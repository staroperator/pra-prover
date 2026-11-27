module

public meta import PRAProver.Library.FOL.DSL.Quotation
public import PRAProver.Library.FOL.Common.Proof

/-!
# Axiom schemas with syntax and numerical parameters

A declaration `axiom name (p : formula of n) := ...` describes a formula template. Arguments to `p`
fill its `n` substitution slots; additional surrounding positions are allowed. Parameters may
produce terms or formulas, and arity zero allows captured free variables. A `Nat` parameter
supplies a family index or appears in a computation of an index.

- `AxiomInfo` stores the template, its parameters and its optional numerical guard.
- `Actual` is an argument of a schema: a number, or a term or formula with named slots.
- `instantiateSchema` substitutes arguments into a template without capturing variables.
- `compileAxiom` emits numerical instance and membership functions and checked introduction lemmas.

To recover a term or formula argument, the compiler follows the enclosing constructors to an
occurrence applied to exactly the surrounding binders in outermost-first order. Numerical
parameters can occur directly in family indices or inside constructors with registered projections.
The test recovers the arguments, compares
the reconstructed formula with the candidate, and checks that any guard returns exactly one.
`TheoryName.schema.isAxiom` also accepts universal closures of instances. The compiler uses the
constructor equations to prove membership from the arguments and any guard premise.
-/

public meta section

namespace PRAProver.Library.FOL.DSL

open Lean hiding Term

open Lean.Elab.Command

open PRAProver.Core

open PRAProver.Library.Tactic.Construction

structure AxiomInfo where
  name : Name
  parameters : Array SyntaxParameter := #[]
  template : FormulaView
  /-- A numerical function of all arguments in declaration order, accepting when it returns `1`. -/
  guard? : Option Term := none
  deriving Inhabited

private def AxiomInfo.sentenceName? (info : AxiomInfo) : Option Name :=
  match info.parameters.isEmpty, info.template with
  | true, .code _ (.definition name []) [] => some name
  | _, _ => none

/-- The PRA declaration used when constructing an axiom instance. A named sentence already
has a declaration of its own. -/
def AxiomInfo.formulaName (info : AxiomInfo) (theory : Name) : Name :=
  info.sentenceName?.getD (theory ++ info.name ++ `formula)

/-- An argument supplied for a schema parameter. The binders of a term or formula name its
explicit slots, outermost first. -/
inductive Actual where
  | number (value : Term)
  | term (body : TermView) (binders : List Name)
  | formula (body : FormulaView) (binders : List Name)
  deriving BEq, Hashable, Repr, Inhabited

def Actual.binders : Actual → List Name
  | .number _ => []
  | .term _ binders | .formula _ binders => binders

def Actual.encode (actual : Actual) (L : Term) (bound free : List Name) : CommandElabM Term :=
  match actual with
  | .number n => pure n
  | .term t binders => t.encode L (binders.reverse ++ bound) free
  | .formula a binders => a.encode L (binders.reverse ++ bound) free

/-- Whether an actual fits a parameter of the given kind. -/
def Actual.fits (actual : Actual) (kind : SyntaxKind) : Bool :=
  match actual, kind with
  | .number _, .nat => true
  | .term _ binders, .term n => binders.length == n
  | .formula _ binders, .formula n => binders.length == n
  | _, _ => false

private partial def instantiateTerm (actuals : Array Actual) (numbers : List Term) :
    TermView → TermView
  | .parameter i args =>
    let values := args.map (instantiateTerm actuals numbers)
    match actuals[i]! with
    | .term t binders => t.substitute (binders.zip values)
    | _ => .constant 0
  | .app i args => .app i (args.map (instantiateTerm actuals numbers))
  | .indexedConst i k => .indexedConst i (k.instantiate numbers)
  | .indexedApp i k args =>
    .indexedApp i (k.instantiate numbers) (args.map (instantiateTerm actuals numbers))
  | t => t

private def instantiateFormula (actuals : Array Actual) (numbers : List Term) :
    FormulaView → FormulaView
  | .parameter i args =>
    match actuals[i]! with
    | .formula a binders => a.substitute (binders.zip (args.map (instantiateTerm actuals numbers)))
    | _ => .falsum
  | .equal t u => .equal (instantiateTerm actuals numbers t) (instantiateTerm actuals numbers u)
  | .relation i args => .relation i (args.map (instantiateTerm actuals numbers))
  | .indexedRelation i k args =>
    .indexedRelation i (k.instantiate numbers) (args.map (instantiateTerm actuals numbers))
  | .imp a b => .imp (instantiateFormula actuals numbers a) (instantiateFormula actuals numbers b)
  | .all x a => .all x (instantiateFormula actuals numbers a)
  | a => a

def instantiateSchema (actuals : Array Actual) (template : FormulaView) : FormulaView :=
  instantiateFormula actuals (actuals.toList.map fun
    | .number n => n
    | _ => .zero) template

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
      [L, applyDefinition `FOL.Language.functionFamilyMember [L, numeral i,
        k.instantiate actuals.toList],
       tupleCode (← args.mapM (encodeTemplateTerm L actuals bound))]
  | .indexedConst i k =>
    return applyDefinition `FOL.Term.const
      [L, applyDefinition `FOL.Language.constantFamilyMember [L, numeral i,
        k.instantiate actuals.toList]]
  | t => t.encode L bound []

/-- Encode a template whose parameters take the codes `actuals`. -/
def encodeTemplate (L : Term) (actuals : Array Term) (bound : List Name) :
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
      [L, applyDefinition `FOL.Language.relationFamilyMember [L, numeral i,
        k.instantiate actuals.toList],
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

private structure IndexProjection where
  theoremName : Name
  builder : Name
  arity : Nat
  argument : Nat
  project : Term
  deriving Inhabited

private initialize indexProjections :
    SimplePersistentEnvExtension IndexProjection (Array IndexProjection) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
    addEntryFn := Array.push
  }

private partial def projectionBody (constructorCall : Term) (term : Term) : Option Term := do
  if term == constructorCall then return .bvar 0
  let .app (.definition name []) arg := term | none
  return .app (.definition name []) (← projectionBody constructorCall arg)

/-- Register a checked equation such as `∀ a b, project (build a b) = a`.
The projection may be a composition of named unary functions. Axiom membership uses it to read
the selected argument and checks the entire reconstructed formula. -/
def registerAxiomIndexProjection (builder theoremName : Name) : CommandElabM Unit := do
  let env := PRAProver.Surface.CoreEnvironment.getState (← getEnv)
  let some (.theoremE theoremDecl) := env.lookup theoremName |
    throwError "expected a checked PRA theorem `{theoremName}`"
  unless theoremDecl.parameters.isEmpty do
    throwError "an index projection theorem must use universal quantifiers for its arguments"
  let mut type := Core.betaReducePredicate (← Surface.getMaxDepth) theoremDecl.type
  let mut arity := 0
  while let .all (.lam _ body) := type do
    arity := arity + 1
    type := body
  let .equal lhs (.bvar index) := type |
    throwError "an index projection theorem must equate a projection with a bound variable"
  unless index < arity do throwError "the result must be a builder argument"
  let inputs := (List.range arity).reverse.map Term.bvar
  let constructorCall := applyDefinition builder inputs
  let some body := projectionBody constructorCall lhs |
    throwError "expected a projection of `{builder}` applied to all binders in order"
  let rule : IndexProjection := ⟨theoremName, builder, arity, arity - 1 - index,
    .lam `code body⟩
  modifyEnv (indexProjections.addEntry · rule)

private partial def recoverIndex (rules : Array IndexProjection) (actuals : Array Term)
    (parameter : Nat) (index : Term) : Option (List RecoveryStep) := do
  if index == .parameter parameter then return []
  let (.definition name [], args) := getAppFnArgs index | none
  for rule in rules do
    if rule.builder == name && rule.arity == args.length then
      let arg := args[rule.argument]!
      if let some rest := recoverIndex rules actuals parameter arg then
        let values := args.map (·.instantiate actuals.toList)
        let step : RecoveryStep := ⟨rule.project, values[rule.argument]!,
          applyTheorem rule.theoremName values⟩
        return step :: rest
  none

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

private def tupleComponents (value : Term) : Nat → List Term
  | n + 2 =>
    match getAppFnArgs value with
    | (.definition `pair [], [lhs, rhs]) => lhs :: tupleComponents rhs (n + 1)
    | _ => []
  | 1 => [value]
  | 0 => []

private structure RecoveryContext where
  language : LanguageInfo
  actuals : Array Term
  parameter : Nat
  bound : List Name := []
  indexProjections : Array IndexProjection := #[]

private def RecoveryContext.term (ctx : RecoveryContext) (t : TermView) : CommandElabM Term :=
  encodeTemplateTerm (languageTerm ctx.language) ctx.actuals ctx.bound t

private def RecoveryContext.formula (ctx : RecoveryContext) (a : FormulaView) :
    CommandElabM Term :=
  encodeTemplate (languageTerm ctx.language) ctx.actuals ctx.bound a

private def RecoveryContext.isCanonical (ctx : RecoveryContext) (i : Nat) (args : List TermView) :
    Bool :=
  i == ctx.parameter && canonicalArguments ctx.bound args

private def familyMemberStep (prefixCount familyCount symbol family member : Term) (bound : Proof) :
    RecoveryStep := Id.run do
  let quotient := Term.lam `j (applyDefinition `div
    [applyDefinition `sub [.bvar 0, prefixCount], familyCount])
  let payload := applyDefinition `add [applyDefinition `mul [familyCount, member], family]
  let subtract := applyDefinition `sub [symbol, prefixCount]
  let division := applyDefinition `div [payload, familyCount]
  let positive := applyTheorem `lt_of_le_of_lt [.zero, family, familyCount] []
    [applyTheorem `zero_le [family], bound]
  let nonzero := applyTheorem `ne_zero_of_pos [familyCount] [] [positive]
  let subtractPrefix := applyTheorem `add_sub_self_left [prefixCount, payload]
  let proof := mkEqTrans (applyProjection quotient symbol) division member
    (mkEqCongr (.lam `n (applyDefinition `div [.bvar 0, familyCount]))
      subtract payload subtractPrefix)
    (applyTheorem `div_mul_add_of_lt [familyCount, member, family] [] [nonzero, bound])
  return ⟨quotient, member, proof⟩

private inductive FamilyKind where
  | constant
  | function
  | relation

private def RecoveryContext.member (ctx : RecoveryContext) (kind : FamilyKind) (i : Nat)
    (packed : Term) (args : List TermView := []) :
    CommandElabM (Option (List RecoveryStep)) := do
  let language := ctx.language
  let L := languageTerm language
  let families := match kind with
    | .constant => language.constantFamilies
    | .function => language.functionFamilies
    | .relation => language.relationFamilies
  let components := tupleComponents packed families[i]!.indexArity
  let recoverComponent (component : Term) :=
    recoverIndex ctx.indexProjections ctx.actuals ctx.parameter component
  let some (position, recovery) := components.zipIdx.findSome? (fun (component, position) =>
    (recoverComponent component).map fun path => (position, path)) | return none
  let family := numeral i
  let values := components.map (·.instantiate ctx.actuals.toList)
  let member := tupleCode values
  let (symbol, prefixCount, familyCount) := match kind with
    | .constant =>
      (`FOL.Language.constantFamilyMember, `FOL.Language.constants,
        `FOL.Language.constantFamilyCount)
    | .function =>
      (`FOL.Language.functionFamilyMember, `FOL.Language.functionCount,
        `FOL.Language.functionFamilyCount)
    | .relation =>
      (`FOL.Language.relationFamilyMember, `FOL.Language.relationCount,
        `FOL.Language.relationFamilyCount)
  let j := applyDefinition symbol [L, family, member]
  let prefixCount := applyDefinition prefixCount [L]
  let familyCount := applyDefinition familyCount [L]
  let arguments := tupleCode (← args.mapM ctx.term)
  let some info := families[i]? | throwError "invalid family number"
  let bound := applyTheorem (language.symbolTheorem "" info.name "_lt")
  let step := match kind with
    | .constant =>
      ⟨applyDefinition `FOL.Term.constantIndex [L], j,
        applyTheorem `FOL.Term.constantIndex_const_of_le [L, j] []
          [applyTheorem `le_add_right [prefixCount,
            applyDefinition `add [applyDefinition `mul [familyCount, member], family]]]⟩
    | .function =>
      let head := applyDefinition `FOL.Term.head
        [L, applyDefinition `FOL.Term.app [L, j, arguments]]
      let isFunction := applyTheorem `FOL.Language.isFunction_familyMember [L, family, member] []
        [bound]
      let pred := applyDefinition `pred
      let next := Term.app .succ j
      ⟨.lam `t (applyDefinition `pred [applyDefinition `FOL.Term.head [L, .bvar 0]]), j,
        mkEqTrans (.app pred head) (.app pred next) j
          (mkEqCongr pred head next (applyTheorem `FOL.Term.head_app [L, j, arguments] []
            [isFunction]))
          (applyTheorem `pred_succ [j])⟩
    | .relation =>
      let isRelation := applyTheorem `FOL.Language.isRelation_familyMember [L, family, member] []
        [bound]
      ⟨applyDefinition `FOL.Formula.relationIndex [L], j,
        applyTheorem `FOL.Formula.relationIndex_rel [L, j, arguments] [] [isRelation]⟩
  return some (step :: familyMemberStep prefixCount familyCount j family member bound ::
    (tupleSteps position values ++ recovery))

mutual

private partial def RecoveryContext.inTerm (ctx : RecoveryContext) (t : TermView) :
    CommandElabM (Option (List RecoveryStep)) := do
  let L := languageTerm ctx.language
  match t with
  | .parameter i args =>
    return if ctx.isCanonical i args then some [] else none
  | .indexedConst i k => ctx.member .constant i k
  | .app i args =>
    ctx.inSymbolArguments false args (numeral i) do
      let some (name, _) := ctx.language.functions[i]? | throwError "invalid function number"
      return applyTheorem (ctx.language.symbolTheorem "isFunction_" name)
  | .indexedApp i k args =>
    if let some steps ← ctx.member .function i k args then return some steps
    let member := k.instantiate ctx.actuals.toList
    let symbol := applyDefinition `FOL.Language.functionFamilyMember [L, numeral i, member]
    ctx.inSymbolArguments false args symbol do
      let some family := ctx.language.functionFamilies[i]? | throwError "invalid family number"
      return .forallElim
        (applyTheorem (ctx.language.symbolTheorem "isFunction_" family.name)) member
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
      let some (name, _) := ctx.language.relations[i]? | throwError "invalid relation number"
      return applyTheorem (ctx.language.symbolTheorem "isRelation_" name)
  | .indexedRelation i k args =>
    if let some steps ← ctx.member .relation i k args then return some steps
    let member := k.instantiate ctx.actuals.toList
    let symbol := applyDefinition `FOL.Language.relationFamilyMember [L, numeral i, member]
    ctx.inSymbolArguments true args symbol do
      let some family := ctx.language.relationFamilies[i]? | throwError "invalid family number"
      return .forallElim
        (applyTheorem (ctx.language.symbolTheorem "isRelation_" family.name)) member
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

/-- Apply the restriction function of a schema to the codes of its parameters. -/
def applyGuard (guard : Term) (actuals : List Term) : Term :=
  actuals.foldl applyProjection guard

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
  let projections := indexProjections.getState (← getEnv)
  for i in [:n] do
    let parameter := info.parameters[i]!
    let ctx : RecoveryContext := { language, actuals := parameters, parameter := i }
    let direct ← ctx.inFormula info.template
    let path ← if direct.isNone && parameter.isNumeric && !projections.isEmpty then
        ({ ctx with indexProjections := projections }).inFormula info.template
      else pure direct
    let some path := path |
      if parameter.isNumeric then
        throwError "cannot recover numerical parameter `{parameter.name}` from a family index"
      else throwError "syntax parameter `{parameter.name}` needs a recoverable occurrence applied \
        to its enclosing binders in outermost-first order"
    paths := paths.push path
  if info.sentenceName?.isNone then
    let body ← encodeTemplate L actuals.toArray [] info.template
    let body := info.parameters.toList.foldr (fun p body => Term.lam p.name body) body
    publishChecked (.function ⟨formulaName, [], n, body⟩) source
  if n == 0 && info.guard?.isNone then
    publishChecked (.function ⟨testName, [], 1,
      .lam `A (applyDefinition `eqb [.bvar 0, applyDefinition formulaName])⟩) source
    let formula := applyDefinition formulaName
    publishChecked (.theoremE ⟨name ++ `isAxiom_of_instance, [],
      .equal (applyDefinition testName [formula]) (numeral 1),
      applyTheorem `eqb_self [formula]⟩) source
    return
  let recovered := paths.toList.map (recover (.bvar 0))
  let shapeTest := applyDefinition `eqb [.bvar 0, applyDefinition formulaName recovered]
  let test := match info.guard? with
    | none => shapeTest
    | some guard => applyDefinition `band
      [shapeTest, applyDefinition `eqb [applyGuard guard recovered, numeral 1]]
  publishChecked (.function ⟨name ++ `isInstance, [], 1,
    .lam `A test⟩) source
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
  let mut instanceProof := checkedCode
  let mut guardPremise := none
  if let some guard := info.guard? then
    let value := applyGuard guard actuals
    let recoveredValue := applyGuard guard recoveredArgs.toList
    let equalGuard := reconstruct (applyGuard guard) parameters recoveredArgs recoveryProofs
    let accepts := mkEqTrans recoveredValue value (numeral 1) equalGuard (.hyp 0)
    let guardCharacterization ← projectTheorem true `eqb_eq_one [recoveredValue, numeral 1]
    let checkedGuard := Proof.impElim guardCharacterization accepts
    let tests := [applyDefinition `eqb [instanceCode, reconstructed],
      applyDefinition `eqb [recoveredValue, numeral 1]]
    instanceProof := applyTheorem `band_eq_one_of_eq_one tests [] [checkedCode, checkedGuard]
    guardPremise := some (Predicate.equal value (numeral 1))
  let withGuard (type : Predicate) (proof : Proof) := match guardPremise with
    | none => (type, proof)
    | some premise => (.imp premise type, .impIntro `guard premise proof)
  let names := info.parameters.toList.map (·.name)
  let (instanceType, checkedInstance) := withGuard instanceType instanceProof
  let (instanceType, checkedInstance) := quantifyProof names instanceType checkedInstance
  publishChecked (.theoremE ⟨name ++ `isInstance_of_instance, [],
    instanceType, checkedInstance⟩) source
  if n == 0 then
    publishChecked (.function ⟨testName, [], 1, applyDefinition (name ++ `isInstance)⟩) source
    let axiomType := Predicate.equal (applyDefinition testName [instanceCode]) (numeral 1)
    let (axiomType, proof) := withGuard axiomType
      (applyTheorem (name ++ `isInstance_of_instance) [] [] [.hyp 0])
    publishChecked (.theoremE ⟨name ++ `isAxiom_of_instance, [], axiomType, proof⟩) source
    return
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
  let depth ← Surface.getMaxDepth
  let expanded := Core.betaReduceTerm depth (.app (.app step A) history)
  let disjuncts := (getAppFnArgs expanded).2
  let premise := Predicate.equal instanceTest (numeral 1)
  let conclusion := Predicate.equal (applyDefinition testName [A]) (numeral 1)
  let motive := Predicate.lam `A (.imp premise conclusion)
  let proof := Proof.forallIntro `A motive (.impIntro `h premise
    (applyTheorem `bor_eq_one_of_left_eq_one disjuncts [] [.hyp 0]))
  publishChecked (.theoremE ⟨name ++ `isAxiom_of_isInstance, [], .all motive, proof⟩) source
  let checkedAxiom := applyTheorem (name ++ `isAxiom_of_isInstance) [instanceCode] []
    [applyTheorem (name ++ `isInstance_of_instance) actuals []
      (if guardPremise.isSome then [.hyp 0] else [])]
  let (axiomType, checkedAxiom) := withGuard
    (.equal (applyDefinition testName [instanceCode]) (numeral 1)) checkedAxiom
  let (axiomType, checkedAxiom) := quantifyProof names axiomType checkedAxiom
  publishChecked (.theoremE ⟨name ++ `isAxiom_of_instance, [], axiomType, checkedAxiom⟩) source
  let allA := applyDefinition `FOL.Formula.all [A]
  let history := applyDefinition `Sequence.generate [allA] [step]
  let expanded := Core.betaReduceTerm depth (.app (.app step allA) history)
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

end PRAProver.Library.FOL.DSL
