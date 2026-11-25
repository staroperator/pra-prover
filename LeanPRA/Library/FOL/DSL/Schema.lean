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

To recover an argument, the compiler follows the enclosing constructors to an occurrence applied
to exactly the surrounding binders in outermost-first order. A term parameter may occur as an
equality side or inside a function or relation application. The generated test recovers the
arguments and compares the reconstructed formula with the candidate.
`TheoryName.schema.isAxiom` also accepts universal closures of instances. The compiler uses the
constructor equations to prove membership from the arguments.
-/

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

private def AxiomInfo.sentenceName? (info : AxiomInfo) : Option Name :=
  match info.parameters.isEmpty, info.template with
  | true, .code _ (.definition name []) [] => some name
  | _, _ => none

/-- The PRA declaration used when constructing an axiom instance. A named sentence already
has a declaration of its own. -/
def AxiomInfo.formulaName (info : AxiomInfo) (theory : Name) : Name :=
  info.sentenceName?.getD (theory ++ info.name ++ `formula)

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
  | .indexedApp i k args => .indexedApp i k (args.map (instantiateTerm actuals))
  | t => t

def instantiateSchema (actuals : Array FormulaActual) : FormulaView → FormulaView
  | .parameter i args =>
    let actual := actuals[i]!
    actual.body.substitute (actual.binders.zip (args.map (instantiateTerm actuals)))
  | .equal t u => .equal (instantiateTerm actuals t) (instantiateTerm actuals u)
  | .relation i args => .relation i (args.map (instantiateTerm actuals))
  | .indexedRelation i k args => .indexedRelation i k (args.map (instantiateTerm actuals))
  | .imp a b => .imp (instantiateSchema actuals a) (instantiateSchema actuals b)
  | .all x a => .all x (instantiateSchema actuals a)
  | a => a

private def canonicalArguments (bound : List Name) (args : List TermView) : Bool :=
  args == bound.reverse.map TermView.var

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
  | .indexedApp i k args => do
    return applyDefinition `FOL.Term.app
      [L, applyDefinition `FOL.Language.functionFamilyMember [L, numeral i, k],
       tupleCode (← args.mapM (encodeTemplateTerm L actuals bound))]
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
  | .indexedRelation i k args => do
    return applyDefinition `FOL.Formula.rel
      [L, applyDefinition `FOL.Language.relationFamilyMember [L, numeral i, k],
       tupleCode (← args.mapM (encodeTemplateTerm L actuals bound))]
  | a => a.encode L bound []

private structure RecoveryStep where
  project : Term
  value : Term
  /-- Applying the projection to the preceding value gives this step's value. -/
  equation : Proof

private def applyProjection (project value : Term) : Term :=
  match project with
  | .lam _ body => body.subst0 value
  | _ => .app project value

private def pairStep (lhs rhs : Term) (takeRight : Bool) : RecoveryStep :=
  if takeRight then
    ⟨applyDefinition `unpairRight, rhs, applyTheorem `unpairRight_pair [lhs, rhs]⟩
  else ⟨applyDefinition `unpairLeft, lhs, applyTheorem `unpairLeft_pair [lhs, rhs]⟩

private def tupleSteps (index : Nat) : List Term → List RecoveryStep
  | lhs :: rest@(_ :: _) =>
    let rhs := tupleCode rest
    if index == 0 then [pairStep lhs rhs false]
    else pairStep lhs rhs true :: tupleSteps (index - 1) rest
  | _ => []

private structure RecoveryContext where
  language : LanguageInfo
  actuals : Array Term
  parameter : Nat
  bound : List Name := []

private def RecoveryContext.term (ctx : RecoveryContext) (t : TermView) : CommandElabM Term :=
  encodeTemplateTerm (languageTerm ctx.language) ctx.actuals ctx.bound t

private def RecoveryContext.formula (ctx : RecoveryContext) (a : FormulaView) :
    CommandElabM Term :=
  encodeTemplate (languageTerm ctx.language) ctx.actuals ctx.bound a

private def RecoveryContext.isCanonical (ctx : RecoveryContext) (i : Nat) (args : List TermView) :
    Bool :=
  i == ctx.parameter && canonicalArguments ctx.bound args

private inductive FamilyKind where
  | constant
  | function
  | relation

private partial def sequenceLength (xs : Term) : CommandElabM (Nat × Proof) := do
  match getAppFnArgs xs with
  | (.definition `Sequence.nil [], []) => return (0, applyTheorem `Sequence.length_nil)
  | (.definition `Sequence.cons [], [x, tail]) =>
    let (n, proof) ← sequenceLength tail
    let length := applyDefinition `Sequence.length [xs]
    let tailLength := applyDefinition `Sequence.length [tail]
    return (n + 1, mkEqTrans length (.app .succ tailLength) (numeral (n + 1))
      (applyTheorem `Sequence.length_cons [x, tail])
      (mkEqCongr .succ tailLength (numeral n) proof))
  | _ => throwError "expected the declared language's symbol sequence"

private def proveSymbolBound (language : LanguageInfo) (index : Nat) (countName lemma : Name)
    (field : Nat) (sequenceName : Option Name := none) : CommandElabM Proof := do
  -- The signature and sequence equations give the count before computing the signature code.
  let core := LeanPRA.Surface.CoreEnvironment.getState (← getEnv)
  let some (.function decl) := core.lookup (language.name ++ `language) |
    throwError "expected a declared language"
  let (.definition `FOL.Language.make [], fields) := getAppFnArgs decl.body |
    throwError "expected the declared language's signature"
  let L := languageTerm language
  let count := applyDefinition countName [L]
  let entry := fields[field]!
  let equation := applyTheorem lemma fields
  let (n, countEq) ← if let some sequenceName := sequenceName then do
    let (n, entryLength) ← sequenceLength entry
    let length := applyDefinition `Sequence.length
    let projection := applyDefinition sequenceName [L]
    pure (n, mkEqTrans count (.app length entry) (numeral n)
      (mkEqCongr length projection entry equation) entryLength)
  else
    pure ((numeralValue? entry).getD 0, equation)
  let motive := Predicate.lam `n (.app (.app (.definition `LT [] []) (numeral index)) (.bvar 0))
  let transport := Proof.forallElim (Proof.forallElim (.eqSubst motive) (numeral n)) count
  return .impElim (.impElim transport (mkEqSymm count (numeral n) countEq))
    (.forallElim .eqRefl .zero)

private def familyBound (L : LanguageInfo) (kind : FamilyKind) (i : Nat) : CommandElabM Proof :=
  match kind with
  | .constant => proveSymbolBound L i `FOL.Language.constantFamilyCount
      `FOL.Language.constantFamilyCount_make 3
  | .function => proveSymbolBound L i `FOL.Language.functionFamilyCount
      `FOL.Language.functionFamilies_make 4 (some `FOL.Language.functionFamilies)
  | .relation => proveSymbolBound L i `FOL.Language.relationFamilyCount
      `FOL.Language.relationFamilies_make 5 (some `FOL.Language.relationFamilies)

mutual

private partial def RecoveryContext.inTerm (ctx : RecoveryContext) (t : TermView) :
    CommandElabM (Option (List RecoveryStep)) := do
  let L := languageTerm ctx.language
  match t with
  | .parameter i args =>
    return if ctx.isCanonical i args then some [] else none
  | .app i args =>
    ctx.inSymbolArguments false args (numeral i) do
      let bound ← proveSymbolBound ctx.language i `FOL.Language.functionCount
        `FOL.Language.functions_make 1 (some `FOL.Language.functions)
      return applyTheorem `FOL.Language.isFunction_of_lt [L, numeral i] [] [bound]
  | .indexedApp i k args =>
    let symbol := applyDefinition `FOL.Language.functionFamilyMember [L, numeral i, k]
    ctx.inSymbolArguments false args symbol do
      let bound ← familyBound ctx.language .function i
      return applyTheorem `FOL.Language.isFunction_familyMember [L, numeral i, k] [] [bound]
  | _ => return none

private partial def RecoveryContext.inArguments (ctx : RecoveryContext) (args : List TermView) :
    CommandElabM (Option (Nat × List RecoveryStep)) := do
  for (arg, i) in args.zipIdx do
    if let some steps ← ctx.inTerm arg then return some (i, steps)
  return none

private partial def RecoveryContext.inSymbolArguments (ctx : RecoveryContext) (isRelation : Bool)
    (args : List TermView) (symbol : Term) (belongs : CommandElabM Proof) :
    CommandElabM (Option (List RecoveryStep)) := do
  let some (i, path) ← ctx.inArguments args | return none
  let L := languageTerm ctx.language
  let values ← args.mapM ctx.term
  let tuple := tupleCode values
  let (projection, equation) := if isRelation then
    (`FOL.Formula.arg, `FOL.Formula.arg_rel) else (`FOL.Term.arg, `FOL.Term.arg_app)
  let step : RecoveryStep := ⟨applyDefinition projection [L], tuple,
    applyTheorem equation [L, symbol, tuple] [] [← belongs]⟩
  return some (step :: (tupleSteps i values ++ path))

end

private partial def RecoveryContext.inFormula (ctx : RecoveryContext) (a : FormulaView) :
    CommandElabM (Option (List RecoveryStep)) := do
  let L := languageTerm ctx.language
  let arg := applyDefinition `FOL.Formula.arg [L]
  match a with
  | .parameter i args => return if ctx.isCanonical i args then some [] else none
  | .equal t u =>
    let some (i, path) ← ctx.inArguments [t, u] | return none
    let lhs ← ctx.term t
    let rhs ← ctx.term u
    let step : RecoveryStep := ⟨arg, tupleCode [lhs, rhs],
      applyTheorem `FOL.Formula.arg_equal [L, lhs, rhs]⟩
    return some (step :: pairStep lhs rhs (i == 1) :: path)
  | .imp a b =>
    let antecedent ← ctx.inFormula a
    let path ← if antecedent.isSome then pure antecedent else ctx.inFormula b
    let some path := path | return none
    let lhs ← ctx.formula a
    let rhs ← ctx.formula b
    let step : RecoveryStep := ⟨arg, tupleCode [lhs, rhs],
      applyTheorem `FOL.Formula.arg_imp [L, lhs, rhs]⟩
    return some (step :: pairStep lhs rhs antecedent.isNone :: path)
  | .all x a =>
    let inner := { ctx with bound := x :: ctx.bound }
    let some path ← inner.inFormula a | return none
    let value ← inner.formula a
    let step : RecoveryStep := ⟨arg, value, applyTheorem `FOL.Formula.arg_all [L, value]⟩
    return some (step :: path)
  | .relation i args =>
    ctx.inSymbolArguments true args (numeral i) do
      let bound ← proveSymbolBound ctx.language i `FOL.Language.relationCount
        `FOL.Language.relations_make 2 (some `FOL.Language.relations)
      return applyTheorem `FOL.Language.isRelation_of_lt [L, numeral i] [] [bound]
  | .indexedRelation i k args =>
    let symbol := applyDefinition `FOL.Language.relationFamilyMember [L, numeral i, k]
    ctx.inSymbolArguments true args symbol do
      let bound ← familyBound ctx.language .relation i
      return applyTheorem `FOL.Language.isRelation_familyMember [L, numeral i, k] [] [bound]
  | _ => return none

private def recover (input : Term) (path : List RecoveryStep) : Term :=
  path.foldl (fun value step => applyProjection step.project value) input

private def proveRecovery (input : Term) (path : List RecoveryStep) : Proof := Id.run do
  let mut projection := input
  let mut value := input
  let mut proof := Proof.forallElim .eqRefl input
  for step in path do
    let lhs := applyProjection step.project projection
    let rhs := applyProjection step.project value
    proof := mkEqTrans lhs rhs step.value (mkEqCongr step.project projection value proof)
      step.equation
    projection := lhs
    value := step.value
  return proof

private def quantifyProof (names : List Name) (type : Predicate) (proof : Proof) :
    Predicate × Proof :=
  names.foldr (fun (name : Name) (type, proof) =>
    let motive := Predicate.lam name type
    (.all motive, .forallIntro name motive proof)) (type, proof)

private def reconstruct (build : List Term → Term) (actuals recovered : Array Term)
    (proofs : Array Proof) : Proof := Id.run do
  let start := build recovered.toList
  let mut current := start
  let mut values := recovered
  let mut equality := Proof.forallElim .eqRefl start
  for i in [:actuals.size] do
    let selector := Term.lam `p (build ((values.map Term.shift).set! i (.bvar 0)).toList)
    values := values.set! i actuals[i]!
    let next := build values.toList
    equality := mkEqTrans start current next equality
      (mkEqCongr selector recovered[i]! actuals[i]! proofs[i]!)
    current := next
  return equality

/-- Compile one named axiom or schema into checked PRA definitions and introduction lemmas. -/
def compileAxiom (theory : Name) (language : LanguageInfo) (info : AxiomInfo) (source : Syntax) :
    CommandElabM Unit := do
  let L := languageTerm language
  let name := theory ++ info.name
  let formulaName := info.formulaName theory
  let testName := name ++ `isAxiom
  let n := info.parameters.size
  let actuals := (List.range n).map (fun i => Term.bvar (n - i - 1))
  let parameters := actuals.toArray
  let mut paths : Array (List RecoveryStep) := #[]
  for i in [:n] do
    let parameter := info.parameters[i]!
    let ctx : RecoveryContext := { language, actuals := parameters, parameter := i }
    let some path ← ctx.inFormula info.template |
      throwError "syntax parameter `{parameter.name}` needs a recoverable occurrence applied \
        to its enclosing binders in outermost-first order"
    paths := paths.push path
  if info.sentenceName?.isNone then
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
  let recovered := paths.toList.map (recover (.bvar 0))
  publishChecked (.function ⟨name ++ `isInstance, [], 1,
    .lam `A (applyDefinition `eqb [.bvar 0, applyDefinition formulaName recovered])⟩) source
  let instanceCode := applyDefinition formulaName actuals
  let recoveredArgs := paths.map (recover instanceCode)
  let recoveryProofs := paths.map (proveRecovery instanceCode)
  let reconstructed := applyDefinition formulaName recoveredArgs.toList
  let equalCode := reconstruct (applyDefinition formulaName ·) parameters recoveredArgs
    recoveryProofs
  let checkedCode := Proof.impElim
    (← projectTheorem true `eqb_eq_one [instanceCode, reconstructed])
    (mkEqSymm reconstructed instanceCode equalCode)
  let instanceType := Predicate.equal
    (applyDefinition (name ++ `isInstance) [instanceCode]) (numeral 1)
  let names := info.parameters.toList.map (·.name)
  let (instanceType, checkedInstance) := quantifyProof names instanceType checkedCode
  publishChecked (.theoremE ⟨name ++ `isInstance_of_instance, [],
    instanceType, checkedInstance⟩) source
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
