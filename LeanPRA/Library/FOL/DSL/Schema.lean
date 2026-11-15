module

public meta import LeanPRA.Library.FOL.DSL.Quotation
public import LeanPRA.Library.FOL.Common.Proof

/-!
# Axiom schemas with syntax parameters

A declaration `axiom name (p : formula of n) := ...` describes a formula template. Arguments to `p`
fill its `n` substitution slots; additional surrounding positions are allowed. Parameters may
produce terms or formulas, and arity zero allows captured free variables.

- `AxiomInfo` stores the template and its named syntax parameters.
- `FormulaActual` stores a term or formula with the named variables used for its slots.
- `instantiateSchema` substitutes actual formulas into a template without capturing variables.
- `compileAxiom` emits numerical instance and membership functions and checked introduction lemmas.

For direct membership checking, each parameter must occur applied to exactly the surrounding
binders, in outermost-first order. A formula occurrence exposes its code directly; a term occurrence
on an equality side exposes its term code. The generated test recovers the parameters and compares
the reconstructed instance with the candidate. Schema instances may be universally closed over
additional parameters. For example, `TheoryName.schema.formula` constructs an instance,
`TheoryName.schema.isInstance` checks its exact shape, and `TheoryName.schema.isAxiom` also accepts
its universal closures. The compiler proves membership for every formula argument, using the common
syntax equations. -/

public meta section

namespace LeanPRA.Library.FOL.DSL

open Lean hiding Term

open Lean.Elab.Command

open LeanPRA.Core

open LeanPRA.Library.Tactic.Construction

structure AxiomInfo where
  name : Name
  parameters : Array SyntaxParameter := #[]
  template : FormulaView
  deriving Inhabited

structure FormulaActual where
  body : FormulaView
  binders : List Name
  termBody : Option TermView := none
  deriving BEq, Hashable, Repr, Inhabited

def FormulaActual.encode (actual : FormulaActual) (L : Term) (bound free : List Name) :
    CommandElabM Term :=
  match actual.termBody with
  | some t => t.encode L (actual.binders.reverse ++ bound) free
  | none => actual.body.encode L (actual.binders.reverse ++ bound) free

private partial def instantiateTerm (actuals : Array FormulaActual) : TermView → TermView
  | .parameter i args =>
    let actual := actuals[i]!
    let values := args.map (instantiateTerm actuals)
    (actual.termBody.getD (.constant 0)).substitute (actual.binders.zip values)
  | .app i args => .app i (args.map (instantiateTerm actuals))
  | t => t

def instantiateSchema (actuals : Array FormulaActual) : FormulaView → FormulaView
  | .parameter i args =>
    let actual := actuals[i]!
    actual.body.substitute (actual.binders.zip (args.map (instantiateTerm actuals)))
  | .equal t u => .equal (instantiateTerm actuals t) (instantiateTerm actuals u)
  | .relation i args => .relation i (args.map (instantiateTerm actuals))
  | .imp a b => .imp (instantiateSchema actuals a) (instantiateSchema actuals b)
  | .all x a => .all x (instantiateSchema actuals a)
  | a => a

private def canonicalArguments (bound : List Name) (args : List TermView) : Bool :=
  args == bound.reverse.map TermView.var

private def recoveryPath (parameter : Nat) (bound : List Name) : FormulaView → Option (List Nat)
  | .parameter i args =>
    if i == parameter && canonicalArguments bound args then some [] else none
  | .equal (.parameter i args) (.parameter j other) =>
    if i == parameter && canonicalArguments bound args then some [3]
    else if j == parameter && canonicalArguments bound other then some [4] else none
  | .equal (.parameter i args) _ =>
    if i == parameter && canonicalArguments bound args then some [3] else none
  | .equal _ (.parameter i args) =>
    if i == parameter && canonicalArguments bound args then some [4] else none
  | .imp a b =>
    (recoveryPath parameter bound a).map (0 :: ·) <|>
      (recoveryPath parameter bound b).map (1 :: ·)
  | .all x a => (recoveryPath parameter (x :: bound) a).map (2 :: ·)
  | _ => none

private def recoverFormula (L candidate : Term) (path : List Nat) : Term :=
  path.foldl (fun A step =>
    let args := applyDefinition `FOL.Formula.arg [L, A]
    if step == 0 || step == 3 then applyDefinition `unpairLeft [args]
    else if step == 1 || step == 4 then applyDefinition `unpairRight [args] else args) candidate

private partial def encodeTemplateTerm (L : Term) (actuals : Array Term) (bound : List Name) :
    TermView → CommandElabM Term
  | .parameter i args => do
    if canonicalArguments bound args then return actuals[i]!
    let terms ← args.mapM (encodeTemplateTerm L actuals bound)
    return applyDefinition `FOL.Term.subst [L, actuals[i]!]
      [SubstitutionView.encode L ⟨terms.reverse, bound.length⟩]
  | .app i args => do
    return applyDefinition `FOL.Term.app
      [L, numeral i, tupleCode (← args.mapM (encodeTemplateTerm L actuals bound))]
  | t => t.encode L bound []

private def encodeTemplate (L : Term) (actuals : Array Term) (bound : List Name) :
    FormulaView → CommandElabM Term
  | .parameter i args => do
    let actual := actuals[i]!
    if canonicalArguments bound args then return actual
    let terms ← args.mapM (encodeTemplateTerm L actuals bound)
    return applyDefinition `FOL.Formula.subst [L, actual]
      [SubstitutionView.encode L ⟨terms.reverse, bound.length⟩]
  | .imp a b => do
    return applyDefinition `FOL.Formula.imp
      [← encodeTemplate L actuals bound a, ← encodeTemplate L actuals bound b]
  | .all x a => do
    return applyDefinition `FOL.Formula.all
      [← encodeTemplate L actuals (x :: bound) a]
  | .equal t u => do
    return applyDefinition `FOL.Formula.equal
      [L, ← encodeTemplateTerm L actuals bound t, ← encodeTemplateTerm L actuals bound u]
  | .relation i args => do
    return applyDefinition `FOL.Formula.rel
      [L, numeral i, tupleCode (← args.mapM (encodeTemplateTerm L actuals bound))]
  | a => a.encode L bound []

private def projectFormula (L A : Term) (step : Nat) : Term :=
  let args := applyDefinition `FOL.Formula.arg [L, A]
  if step == 0 || step == 3 then applyDefinition `unpairLeft [args]
  else if step == 1 || step == 4 then applyDefinition `unpairRight [args] else args

private def proveRecovery (L : Term) (actuals : Array Term) (template : FormulaView)
    (path : List Nat) (input : Term) : CommandElabM Proof := do
  let mut formula := template
  let mut bound := []
  let mut projection := input
  let mut code ← encodeTemplate L actuals bound formula
  let mut proof := Proof.forallElim .eqRefl input
  for step in path do
    if step == 3 || step == 4 then
      let .equal t u := formula | throwError "expected an equality in a term recovery path"
      let ct ← encodeTemplateTerm L actuals bound t
      let cu ← encodeTemplateTerm L actuals bound u
      let pair := applyDefinition `pair [ct, cu]
      let field := if step == 3 then `unpairLeft else `unpairRight
      let result := if step == 3 then ct else cu
      let arg := applyDefinition `FOL.Formula.arg [L, code]
      let equation := mkEqTrans (projectFormula L code step) (applyDefinition field [pair]) result
        (mkEqCongr (applyDefinition field) arg pair
          (applyTheorem `FOL.Formula.arg_equal [L, ct, cu]))
        (applyTheorem (if step == 3 then `unpairLeft_pair else `unpairRight_pair) [ct, cu])
      let selector := Term.lam `F (projectFormula L.shift (.bvar 0) step)
      return mkEqTrans (projectFormula L projection step) (projectFormula L code step) result
        (mkEqCongr selector projection code proof) equation
    let (child, names, equation) ← match formula, step with
      | .imp a b, 0 | .imp a b, 1 => do
        let ca ← encodeTemplate L actuals bound a
        let cb ← encodeTemplate L actuals bound b
        let pair := applyDefinition `pair [ca, cb]
        let field := if step == 0 then `unpairLeft else `unpairRight
        let result := if step == 0 then ca else cb
        let arg := applyDefinition `FOL.Formula.arg [L, code]
        let equation := mkEqTrans (projectFormula L code step)
          (applyDefinition field [pair]) result
          (mkEqCongr (applyDefinition field) arg pair
            (applyTheorem `FOL.Formula.arg_imp [L, ca, cb]))
          (applyTheorem (if step == 0 then `unpairLeft_pair else `unpairRight_pair) [ca, cb])
        pure (if step == 0 then a else b, bound, equation)
      | .all x a, 2 => do
        let ca ← encodeTemplate L actuals (x :: bound) a
        pure (a, x :: bound, applyTheorem `FOL.Formula.arg_all [L, ca])
      | _, _ => throwError "invalid schema recovery path"
    let next ← encodeTemplate L actuals names child
    let selector := Term.lam `F (projectFormula L.shift (.bvar 0) step)
    proof := mkEqTrans (projectFormula L projection step) (projectFormula L code step) next
      (mkEqCongr selector projection code proof) equation
    projection := projectFormula L projection step
    formula := child
    bound := names
    code := next
  return proof

private def quantifyProof (names : List Name) (type : Predicate) (proof : Proof) :
    Predicate × Proof :=
  names.foldr (fun (name : Name) (type, proof) =>
    let motive := Predicate.lam name type
    (.all motive, .forallIntro name motive proof)) (type, proof)

/-- Compile one named axiom or schema into checked PRA definitions and introduction lemmas. -/
def compileAxiom (theory : Name) (L : Term) (info : AxiomInfo) (source : Syntax) :
    CommandElabM Unit := do
  let name := theory ++ info.name
  let formulaName := name ++ `formula
  let testName := name ++ `isAxiom
  let n := info.parameters.size
  let actuals := (List.range n).map (fun i => Term.bvar (n - i - 1))
  let body ← encodeTemplate L actuals.toArray [] info.template
  let body := info.parameters.toList.foldr (fun p body => Term.lam p.name body) body
  publishChecked (.function ⟨formulaName, [], n, body⟩) source
  if n == 0 then
    publishChecked (.function ⟨testName, [], 1,
      .lam `A (applyDefinition `eqb [.bvar 0, applyDefinition formulaName])⟩) source
    let formula := applyDefinition formulaName
    publishChecked (.theoremE ⟨name ++ `isAxiom_of_instance, [],
      .equal (applyDefinition testName [formula]) (numeral 1),
      applyTheorem `eqb_self [formula]⟩) source
    return
  let mut recovered : Array Term := #[]
  for i in [:n] do
    let parameterName := info.parameters[i]!.name.eraseMacroScopes
    let some path := recoveryPath i [] info.template |
      throwError "syntax parameter `{parameterName}` needs a recoverable occurrence applied to \
        its enclosing binders in outermost-first order; a term must be an equality side"
    recovered := recovered.push (recoverFormula L (.bvar 0) path)
  publishChecked (.function ⟨name ++ `isInstance, [], 1,
    .lam `A (applyDefinition `eqb [.bvar 0, applyDefinition formulaName recovered.toList])⟩) source
  let candidate := Term.bvar 1
  let history := Term.bvar 0
  let isAll := applyDefinition `band [applyDefinition `isPos [candidate],
    applyDefinition `eqb [applyDefinition `FOL.Formula.head [L, candidate], numeral 2]]
  let step := Term.lam `A (.lam `history (applyDefinition `bor
    [applyDefinition (name ++ `isInstance) [candidate], applyDefinition `ite [isAll,
      applyDefinition `Sequence.rget [history, applyDefinition `FOL.Formula.arg [L, candidate]],
      numeral 0]]))
  publishChecked (.function ⟨testName, [], 1, applyDefinition `covrec [] [step]⟩) source
  let A := Term.bvar 0
  let instanceTest := applyDefinition (name ++ `isInstance) [A]
  let history := applyDefinition `Sequence.generate [A] [step]
  let expanded := Core.betaReduceTerm 2048 (.app (.app step A) history)
  let disjuncts := (getAppFnArgs expanded).2
  let premise := Predicate.equal instanceTest (numeral 1)
  let conclusion := Predicate.equal (applyDefinition testName [A]) (numeral 1)
  let motive := Predicate.lam `A (.imp premise conclusion)
  let proof := Proof.forallIntro `A motive (.impIntro `h premise
    (applyTheorem `bor_eq_one_of_left_eq_one disjuncts [] [.hyp 0]))
  publishChecked (.theoremE ⟨name ++ `isAxiom_of_isInstance, [], .all motive, proof⟩) source
  let parameters := actuals.toArray
  let instanceCode := applyDefinition formulaName actuals
  let mut recoveredArgs := #[]
  let mut recoveryProofs := #[]
  for i in [:n] do
    let some path := recoveryPath i [] info.template | throwError "missing schema recovery path"
    recoveredArgs := recoveredArgs.push (recoverFormula L instanceCode path)
    recoveryProofs := recoveryProofs.push
      (← proveRecovery L parameters info.template path instanceCode)
  let reconstructed := applyDefinition formulaName recoveredArgs.toList
  let mut current := reconstructed
  let mut equality := Proof.forallElim .eqRefl reconstructed
  for i in [:n] do
    let values := recoveredArgs.mapIdx fun j value => if j < i then parameters[j]! else value
    let nextValues := values.set! i parameters[i]!
    let selector := Term.lam `p (applyDefinition formulaName
      ((values.map Term.shift).set! i (.bvar 0)).toList)
    let next := applyDefinition formulaName nextValues.toList
    equality := mkEqTrans reconstructed current next equality
      (mkEqCongr selector recoveredArgs[i]! parameters[i]! recoveryProofs[i]!)
    current := next
  let checkedInstance := Proof.impElim
    (← projectTheorem true `eqb_eq_one [instanceCode, reconstructed])
    (mkEqSymm reconstructed instanceCode equality)
  let instanceType := Predicate.equal
    (applyDefinition (name ++ `isInstance) [instanceCode]) (numeral 1)
  let names := info.parameters.toList.map (·.name)
  let (instanceType, checkedInstance) := quantifyProof names instanceType checkedInstance
  publishChecked (.theoremE ⟨name ++ `isInstance_of_instance, [],
    instanceType, checkedInstance⟩) source
  let checkedAxiom := applyTheorem (name ++ `isAxiom_of_isInstance) [instanceCode] []
    [applyTheorem (name ++ `isInstance_of_instance) actuals]
  let (axiomType, checkedAxiom) := quantifyProof names
    (.equal (applyDefinition testName [instanceCode]) (numeral 1)) checkedAxiom
  publishChecked (.theoremE ⟨name ++ `isAxiom_of_instance, [], axiomType, checkedAxiom⟩) source
  let allA := applyDefinition `FOL.Formula.all [A]
  let history := applyDefinition `Sequence.generate [allA] [step]
  let expanded := Core.betaReduceTerm 2048 (.app (.app step allA) history)
  let disjuncts := (getAppFnArgs expanded).2
  let tail := disjuncts[1]!
  let conditional := (getAppFnArgs tail).2
  let guard := conditional[0]!
  let value := conditional[1]!
  let head := applyDefinition `FOL.Formula.head [L, allA]
  let positive := Proof.impElim (← projectTheorem true `isPos_eq_one [allA])
    (applyTheorem `FOL.Formula.all_ne_zero [A])
  let quantified := Proof.impElim (← projectTheorem true `eqb_eq_one [head, numeral 2])
    (applyTheorem `FOL.Formula.head_all [L, A])
  let guardProof := applyTheorem `band_eq_one_of_eq_one (getAppFnArgs guard).2 []
    [positive, quantified]
  let choose := Term.lam `condition
    (applyDefinition `ite [.bvar 0, value.shift, numeral 0])
  let selected := mkEqCongr choose guard (numeral 1) guardProof
  let lookup := applyDefinition `Sequence.rget [history, A]
  let argument := applyDefinition `FOL.Formula.arg [L, allA]
  let lookupProof := mkEqCongr
    (.lam `body (applyDefinition `Sequence.rget [history.shift, .bvar 0])) argument A
    (applyTheorem `FOL.Formula.arg_all [L, A])
  let checked := applyDefinition testName [A]
  let earlier := applyTheorem `Sequence.rget_generate [A, allA] [step]
    [applyTheorem `FOL.Formula.body_lt_all [A]]
  let tailProof := mkEqTrans tail value checked selected
    (mkEqTrans value lookup checked lookupProof earlier)
  let membership := mkEqTrans tail checked (numeral 1) tailProof (.hyp 0)
  let proof := applyTheorem `bor_eq_one_of_right_eq_one disjuncts [] [membership]
  let premise := Predicate.equal checked (numeral 1)
  let motive := Predicate.lam `A
    (.imp premise (.equal (applyDefinition testName [allA]) (numeral 1)))
  publishChecked (.theoremE ⟨name ++ `isAxiom_of_all, [], .all motive,
    .forallIntro `A motive (.impIntro `h premise proof)⟩) source

end LeanPRA.Library.FOL.DSL
