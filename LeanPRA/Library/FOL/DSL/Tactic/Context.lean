module

public import LeanPRA.Library.FOL.Common.Theory
public meta import LeanPRA.Library.FOL.DSL.Proof.Contextual
public meta import LeanPRA.Library.FOL.DSL.Decoding

/-!
# Shared context for FOL tactics

These operations connect object formulas and Hilbert derivations to ordinary PRA tactic goals.
Local assumptions form the list of a goal `Sequent L T Γ A`; each is named by
the name marker around its formula code. Object variables are local PRA names for variable codes.

- `ProofGoal` records the current theory and decoded formula.
- `closedFirst` runs a tactic with definitions closed and, when that fails, keeps a run with
  every definition opened only if it closes the goal.
- `currentGoalAs` and `exposeStep` open the definition at the head of a formula for a tactic
  that needs its connective; `convertStep` restates a step whose formula agrees with another
  once definitions are opened; `openNamed` opens definitions by name.
- `assumptionStep` proves an assumption of the list; `replaceAssumption` replaces an assumption
  by a formula derived from the list, keeping its name and position.
- `rule` resolves assumptions and PRA proofs, including the theorems that stand for axioms,
  applying an application form to its arguments; `proofRule` does this for a proof given as a
  Core proof term. `dischargeAntecedents` proves the PRA antecedents of a proof, such as the
  restriction of an axiom schema, from the goal's PRA hypotheses or by calculation.
- `normalizeProvable` calculates the formula code of a proof before it is read.
- `refineDerivation` creates subgoals and checks how their proofs are combined.
- `applySequentRule` reduces the goal by one application of a `Sequent` rule.
- `introduceVariable` manages object binders and their local aliases.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL.TacticSupport

open Lean Elab Command LeanPRA.Core
open LeanPRA.Surface LeanPRA.Surface.Tactic
open LeanPRA.Library.Tactic (markName markedName? unmarked)
open LeanPRA.Library.Tactic.Construction

/-- The selected theory, numerical formula code, and decoded view of a PRA provability goal. -/
structure ProofGoal where
  theory : TheoryInfo
  code : Core.Term
  formula : FormulaView
  free : List Name
  context : LocalContext := {}

/-- Run a tactic with definitions closed; a definition is opened only where the tactic needs its
body, or where the proof opens it by name with `prw`. When the tactic fails, it runs again with
every definition opened, and that run is kept only when it closes the goal without leaving new
goals, so an opened formula is never shown. Otherwise the error of the first run is reported. -/
def closedFirst (tactic : Tactic) : Tactic := fun stx => do
  if ← opensDefinitions then return ← tactic stx
  let restore ← saveState
  let rest := (← get).drop 1
  try tactic stx
  catch error =>
    if error.isInterrupt then throw error
    if let .internal _ _ := error then throw error
    restore
    let closed ← try
        withOpenDefinitions (tactic stx)
        pure ((← get) == rest)
      catch second =>
        if second.isInterrupt then throw second
        pure false
    unless closed do
      restore
      throw error

/-- Elaborate a PRA numerical expression in the current tactic context. -/
def coreTerm (stx : TSyntax `praExpr) : TacticM Core.Term := do
  let value ← elaborateTerm stx
  return (← getGoal).projection.encodeTerm value

/-- Elaborate a PRA proof expression in the goal's context and return it with its statement. -/
def coreProof (stx : TSyntax `praExpr) : TacticM (Core.Proof × Core.Predicate) := do
  let (proof, type) ← elaborateProof stx
  let goal ← getGoal
  let proof ← match goal.projection.encodeProof proof with
    | .ok proof => pure proof
    | .error message => throwErrorAt stx "{message}"
  return (proof, goal.projection.encodePredicate type)

/-- Read a provability statement of a declared theory, including its optional assumption list. -/
private def provability (type : Core.Predicate) :
    CommandElabM (TheoryInfo × Core.Term × Option Core.Term) := do
  let depth ← Surface.getMaxDepth
  let some (L, theory, code, context) := provabilityParts? depth type |
    throwError "expected an FOL provability goal"
  let some T := (theories.getState (← getEnv)).find? fun T =>
      theory == applyDefinition (T.name ++ `isAxiom) && L == languageTerm T.language |
    throwError "the FOL theory must be a declared theory"
  return (T, code, context)

/-- Read the current provability goal, its local assumptions, and its visible object variables.
An assumption is named by its name marker. -/
def currentGoal : TacticM ProofGoal := do
  let goal ← getGoal
  let (T, code, context) ← provability (goal.projection.encodePredicate goal.target)
  let context := context.getD emptyList
  let entries : List (Name × Core.Term) := (listEntries context).1.zipIdx.map fun (entry, i) =>
    match markedName? entry with
    | some (name, value) => (name, value)
    | none => (Name.num `_folAssumption i, entry)
  let (normalized, entries) ← (do
    let code ← calculate code
    let entries ← entries.mapM fun ((name, value) : Name × Core.Term) =>
      return (name, (← calculate value).value)
    return (code.value, entries)).run' {}
  let closed ← closedDefinitions
  let count := goal.names.termAliases.foldl (fun count (_, value) =>
    match value with
    | .letE `_folBoundVariable value (.bvar 0) => max count (freePositions closed value)
    | _ => count) (entries.foldl (fun count (_, value) => max count (freePositions closed value))
      (freePositions closed normalized))
  let free := (List.range count).map positionName
  let formula ← readFormula T.language [] free normalized
  let assumptions ← entries.mapM fun (name, value) =>
    return (name, ← readFormula T.language [] free value)
  return ⟨T, code, formula, free, ⟨context, assumptions⟩⟩

/-- Elaborate a formula argument using the goal language and object variables. -/
def formulaArgument (g : ProofGoal) (stx : TSyntax `folFormula)
    (binders : List Name := []) : TacticM FormulaView := do
  let origin := activeSyntaxContext.getState (← getEnv)
  let expr ← formulaExpression g.theory.language binders stx #[] (g.free.length - origin)
  let code ← coreTerm expr
  readFormula g.theory.language binders g.free code

/-- Elaborate a term argument using the goal language and object variables. -/
def termArgument (g : ProofGoal) (stx : TSyntax `folTerm) : TacticM TermView := do
  let origin := activeSyntaxContext.getState (← getEnv)
  let expr ← termExpression g.theory.language [] stx #[] (g.free.length - origin)
  readTerm g.theory.language [] g.free (← coreTerm expr)

/-- Read the leading implication premises as named object assumptions. -/
def assumptions : FormulaView → List (Name × FormulaView) × FormulaView
  | .imp a b =>
    let (rest, goal) := assumptions b
    ((Name.num `_folAssumption rest.length, a) :: rest, goal)
  | a => ([], a)

/-- Calculate the conclusion in a proof of `FOL.Provable` or `FOL.Sequent`, and return the
transported proof together with its statement. The calculation carries out substitutions. A
definition with a substitution theorem stays closed unless every definition is opened in the
current scope. A list of local assumptions in the statement stays as it is. -/
def normalizeProvable (proof : Core.Proof) (type : Core.Predicate) :
    CommandElabM (Core.Proof × Core.Predicate) := do
  let depth ← Surface.getMaxDepth
  let some (L, theory, conclusion, context) := provabilityParts? depth type |
    throwError "expected a proof of FOL.Provable or FOL.Sequent"
  let context := context.getD emptyList
  let normalized ← (calculate conclusion).run' {}
  let proof ← transportUnder L theory context conclusion normalized.value proof
  return (proof, provableUnder L theory context normalized.value)

/-- Turn a PRA proof of the provability statement `type` into a derivation step for the goal.
The formula is read in the goal's object variables. A proof with local assumptions must have
the goal's list of assumptions. A proof in a parent theory is carried to the goal's theory. -/
def proofRule (g : ProofGoal) (proof : Core.Proof) (type : Core.Predicate) :
    CommandElabM (DeriveM Nat) := do
  let (T, code, sourceContext) ← provability type
  unless T.language.name == g.theory.language.name do
    throwError "the proof belongs to another FOL language"
  let formula ← readFormula T.language [] g.free code
  let mut proof := proof
  let L := languageTerm T.language
  let originalTheory := applyDefinition (T.name ++ `isAxiom)
  let canonical ← formula.encode L [] g.free
  let mut proofCode := canonical
  if let some source := sourceContext then
    unless source == g.context.code do
      throwError "the supplied proof has local assumptions other than those of the goal"
    proof ← transportUnder L originalTheory source code canonical proof
    proofCode := foldImplications source canonical
  else
    proof ← transportProvable L originalTheory code canonical proof
  let mut extension := g.theory
  let mut path : List TheoryInfo := []
  while extension.name != T.name do
    let some parent := extension.parent |
      throwError "the proof belongs to a theory outside the goal's extension chain"
    path := extension :: path
    extension ← findTheory parent
  for child in path do
    let some parent := child.parent | throwError "missing parent theory"
    let inclusion := applyTheorem `FOL.subtheory_of_axiom_inclusion []
      [languageTerm T.language, applyDefinition (parent ++ `isAxiom),
       applyDefinition (child.name ++ `isAxiom)]
      [applyTheorem (child.name ++ `isAxiom_of_parent)]
    proof := .impElim (.forallElim inclusion proofCode) proof
  return addNode formula (if sourceContext.isSome then .localProof proof else .proven proof)

private def goalHypotheses : TacticM (List Predicate) := do
  let goal ← getGoal
  return (goal.projection.encodeContext goal.context).proofs

private def shownPredicate (predicate : Predicate) : CommandElabM Format := do
  let depth ← Surface.getMaxDepth
  Surface.formatSyntax `praExpr
    (← Surface.delabPredicate {} (Core.betaReducePredicate depth predicate))

/-- Prove `value = 1` from candidate equations, splitting boolean conjunctions and
disjunctions and reading `eqb a b` from an equation `a = b`. -/
private partial def dischargeTest (candidate? : Predicate → Option Proof) (value : Core.Term) :
    CommandElabM (Option Proof) := do
  let one := numeral 1
  if numeralValue? value == some 1 then return some (.forallElim .eqRefl one)
  if let some p := candidate? (.equal value one) then return some p
  match getAppFnArgs value with
  | (.definition `eqb [], [a, b]) =>
    if let some p := candidate? (.equal a b) then
      return some (.impElim (← projectTheorem true `eqb_eq_one [a, b]) p)
    return none
  | (.definition `band [], [a, b]) =>
    let some pa ← dischargeTest candidate? a | return none
    let some pb ← dischargeTest candidate? b | return none
    return some (applyTheorem `band_eq_one_of_eq_one [a, b] [] [pa, pb])
  | (.definition `bor [], [a, b]) =>
    if let some pa ← dischargeTest candidate? a then
      return some (applyTheorem `bor_eq_one_of_left_eq_one [a, b] [] [pa])
    if let some pb ← dischargeTest candidate? b then
      return some (applyTheorem `bor_eq_one_of_right_eq_one [a, b] [] [pb])
    return none
  | _ => return none

/-- Prove the PRA antecedent `premise` of the proof reference `ref` from a supplied proof, the
goal's PRA hypotheses, or by calculation. A candidate is accepted when it states the premise.
For an equation `test = 1`, a conjunction `band a b` needs both parts, a disjunction `bor a b`
needs one part, and a test `eqb a b` is proved from a candidate `a = b`. The test is also
calculated: a value `1` closes the goal, and a simplified test is compared with the candidates
again. Comparisons are syntactic, up to beta reduction. Definitional unfolding is avoided
because a test on an opaque formula code has no bound on its unfolding. -/
def dischargeAntecedent (ref : Syntax) (shown : MessageData) (premise : Predicate)
    (supplied : Option (Proof × Predicate) := none) : TacticM Proof := do
  let depth ← Surface.getMaxDepth
  let premise := Core.betaReducePredicate depth premise
  let candidates := supplied.toList ++ (← goalHypotheses).zipIdx.map fun (h, i) =>
    (Proof.hyp i, h)
  let candidates := candidates.map fun (p, h) => (p, Core.betaReducePredicate depth h)
  let candidate? (type : Predicate) : Option Proof :=
    (candidates.find? fun (_, h) => h == type).map (·.1)
  if let some p := candidate? premise then return p
  let one := numeral 1
  let failure {α : Type} : TacticM α := do
    if let some (_, given) := supplied then
      throwErrorAt ref "the supplied proof shows {← shownPredicate given}, but `{shown}` \
        requires a PRA proof of {← shownPredicate premise}"
    throwErrorAt ref "`{shown}` requires a PRA proof of {← shownPredicate premise}"
  let .equal test rhs := premise | failure
  unless rhs == one do failure
  let discharge := dischargeTest candidate?
  if let some p ← discharge test then return p
  let calculated ← try some <$> (calculate test).run' {} catch error =>
    if error.isInterrupt then throw error else pure none
  if let some ⟨value, equation⟩ := calculated then
    if value != test then
      if let some p ← discharge value then return mkEqTrans test value one equation p
  try calculateClosedEquality test one
  catch error =>
    if error.isInterrupt then throw error
    failure

/-- Discharge the leading PRA antecedents of a proof, such as the restriction of an axiom
schema, until its statement is a provability statement. -/
def dischargeAntecedents (ref : Syntax) (shown : MessageData) (proof : Proof)
    (type : Predicate) : TacticM (Proof × Predicate) := do
  let depth ← Surface.getMaxDepth
  let mut proof := proof
  let mut type := type
  repeat
    let .imp premise rest := Core.betaReducePredicate depth type | break
    if (provabilityParts? depth premise).isSome then break
    proof := .impElim proof (← dischargeAntecedent ref shown premise)
    type := rest
  return (proof, type)

/-- Discharge the leading PRA antecedent of a proof with a supplied PRA proof, which may also
state a test that the antecedent calculates to. -/
def supplyAntecedent (ref : Syntax) (shown : MessageData) (proof : Proof) (type : Predicate)
    (supplied : Proof × Predicate) : TacticM (Proof × Predicate) := do
  let depth ← Surface.getMaxDepth
  let .imp premise rest := Core.betaReducePredicate depth type |
    throwErrorAt ref "`{shown}` has no PRA antecedent for the supplied proof"
  return (.impElim proof (← dischargeAntecedent ref shown premise (some supplied)), rest)

/-- Resolve a PRA proof expression into a derivation step. Each proof in `antecedents`
discharges the next PRA antecedent, where a proof of `a = b` is accepted for a test `eqb a b`.
When that comparison fails, or when `unify` is set because a hole among the other arguments
must be resolved against them, the proofs are applied as ordinary PRA arguments instead, so that
the checker compares the statements up to unfolding. The goal's PRA hypotheses or calculation
discharge the PRA antecedents that remain. -/
def expressionRule (g : ProofGoal) (ref : Syntax) (shown : MessageData)
    (stx : TSyntax `praExpr) (antecedents : Array (TSyntax `folArg) := #[])
    (unify : Bool := false) : TacticM (DeriveM Nat) := do
  let applied : TacticM (Proof × Predicate) := do
    let mut applied := stx
    for antecedent in antecedents do
      applied ← `(praExpr| $applied ($(← argumentAsPra antecedent)))
    coreProof applied
  let discharged : TacticM (Proof × Predicate) := do
    let mut (proof, type) ← coreProof stx
    for antecedent in antecedents do
      let supplied ← coreProof (← argumentAsPra antecedent)
      (proof, type) ← supplyAntecedent antecedent shown proof type supplied
    pure (proof, type)
  let mut (proof, type) ← if unify || antecedents.isEmpty then applied else
    try discharged catch error =>
      if error.isInterrupt then throw error
      try applied catch second =>
        if second.isInterrupt then throw second
        throw error
  (proof, type) ← dischargeAntecedents ref shown proof type
  (proof, type) ← normalizeProvable proof type
  proofRule g proof type

/-- The proof of a theorem or local proof applied to arguments, with or without parentheses. -/
private def appliedRule (g : ProofGoal) (ref : TSyntax `folRef) (head : Ident)
    (args : Array (TSyntax `folArg)) : TacticM (DeriveM Nat) := do
  let origin := activeSyntaxContext.getState (← getEnv)
  let (expr, antecedents) ← applicationHead g.theory.language [] head args #[]
    (g.free.length - origin)
  expressionRule g ref m!"{head.getId.eraseMacroScopes}" expr antecedents
    (unify := args.any isHoleArgument)

/-- Resolve an object assumption or a PRA proof into a derivation step. An application form
`h a₁ … aₘ`, with or without parentheses, applies a theorem, including the theorem that stands
for an axiom, or a local proof to its arguments. Names resolve as PRA names do, through the
current namespace and the open scopes. -/
def rule (g : ProofGoal) (ref : TSyntax `folRef) : TacticM (DeriveM Nat) := withRef ref do
  match ref with
  | `(folRef| ${$proof:praExpr}) => expressionRule g ref m!"{proof}" proof
  | `(folRef| ($head:ident $args:folArg*)) => appliedRule g ref head args
  | `(folRef| $head:ident $args:folArg*) => appliedRule g ref head args
  | `(folRef| $id:ident) =>
    let stx ← `(praExpr| $id:ident)
    let name := id.getId.eraseMacroScopes
    if let some index := g.context.entries.findIdx? (fun (n, _) => n == name) then
      let L := languageTerm g.theory.language
      let theory := applyDefinition (g.theory.name ++ `isAxiom)
      let formula := g.context.entries[index]!.2
      if let some (entry, proof) := assumptionProof L theory g.context.code index then
        let proof ← transportUnder L theory g.context.code entry
          (← formula.encode L [] g.free) proof
        return addNode formula (.localProof proof)
    expressionRule g ref m!"{name}" stx
  | _ => throwUnsupportedSyntax

/-- Construct the underlying PRA goal predicate under the goal's local assumptions. -/
private def goalPredicate (g : ProofGoal) (code : Core.Term) : CommandElabM Predicate := do
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  return provableUnder L T g.context.code code

private def proofInContext (g : ProofGoal) (graph : Derivation) (root : Nat)
    (formula : FormulaView) : CommandElabM Core.Proof := do
  if g.context.code == emptyList then derivationProof g.theory graph root formula g.free
  else contextualProof g.theory graph root formula g.context g.free

private def transportGoal (g : ProofGoal) (encoded : Core.Term) (p : Core.Proof) :
    CommandElabM Core.Proof := do
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  transportUnder L T g.context.code encoded g.code p

/-- A proof that the formula at `root` of a derivation follows from the goal's assumptions,
together with that formula. -/
def derivedProof (g : ProofGoal) (graph : Derivation) (root : Nat) :
    TacticM (FormulaView × Core.Proof) := do
  let formula := graph.nodes[root]!.formula
  let proof ← proofInContext g graph root formula
  return (formula, proof)

/-- Reduce the goal by one rule. The new goals state the formula codes `premises` under the
goal's assumptions. `rule` receives their proofs and returns a proof of the code `conclusion`
under the same assumptions; the result is transported to the goal's own code. A proof that
`rule` takes from outside must be valid beneath one more hypothesis for each premise. -/
def applySequentRule (g : ProofGoal) (premises : List Core.Term) (conclusion : Core.Term)
    (rule : List Core.Proof → CommandElabM Core.Proof) : TacticM Unit := do
  let count := premises.length
  let inputs := (List.range count).map fun i => Core.Proof.hyp (count - i - 1)
  let mut proof ← transportGoal g conclusion (← rule inputs)
  let mut statements := []
  for code in premises.reverse do
    let premise ← goalPredicate g code
    proof := .impIntro `_folPremise premise proof
    statements := premise :: statements
  let view := (← getGoal).projection
  Tactic.applyProof (view.decodeProof proof) (statements.map view.decodePredicate)

/-- Whether the formula is a definition that stays closed when read. -/
def isClosedDefinition : FormulaView → CommandElabM Bool
  | .code _ value _ => return (← headFormulaDefinition? value).isSome
  | _ => return false

/-- Replace a goal whose conclusion is a closed definition by the goal for its body, and return
whether a definition was opened. -/
def openGoal : TacticM Bool := do
  let g ← currentGoal
  unless ← isClosedDefinition g.formula do return false
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  let encoded ← g.formula.encode L [] g.free
  let some opened ← openHead encoded | return false
  applySequentRule g [opened.value] encoded fun proofs =>
    return transportAlong L T g.context.code opened.value encoded
      (mkEqSymm encoded opened.value opened.proof) proofs[0]!
  return true

/-- Return the current goal after opening definitions at the head of its conclusion until the
conclusion satisfies `wanted` or can no longer be opened. -/
def currentGoalAs (wanted : FormulaView → Bool) : TacticM ProofGoal := do
  for _ in [:32] do
    let g ← currentGoal
    if wanted g.formula then return g
    unless ← openGoal do return g
  currentGoal

/-- Open the definition at the head of the formula code `t`, or at the head of the conclusion
behind its leading premises. -/
partial def openConclusion (t : Core.Term) : CommandElabM (Option Calculation) := do
  if let some opened ← openHead t then return some opened
  let (.definition `FOL.Formula.imp [], [a, b]) := getAppFnArgs t | return none
  let some opened ← openConclusion b | return none
  let hole := Core.Term.lam `B (applyDefinition `FOL.Formula.imp [a.shift, .bvar 0])
  return some ⟨applyDefinition `FOL.Formula.imp [a, opened.value],
    mkEqCongr hole b opened.value opened.proof⟩

/-- Return the derivation step `initial` after opening definitions at the head of its formula
or of its conclusion until the formula satisfies `wanted` or can no longer be opened. -/
def exposeStep (g : ProofGoal) (initial : DeriveM Nat) (wanted : FormulaView → Bool) :
    TacticM (DeriveM Nat) := do
  let (root, graph) ← initial.run {}
  let mut formula := graph.nodes[root]!.formula
  if wanted formula then return initial
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  let mut proof := (← derivedProof g graph root).2
  let mut code ← formula.encode L [] g.free
  for _ in [:32] do
    if wanted formula then break
    let some opened ← openConclusion code | break
    proof := transportAlong L T g.context.code code opened.value opened.proof proof
    code := opened.value
    formula ← readFormula g.theory.language [] g.free code
  -- A derivation step proves the code that its formula is written as.
  let result := formula
  let stated ← transportUnder L T g.context.code code (← result.encode L [] g.free) proof
  return addNode result
    (if g.context.code == emptyList then .proven stated else .localProof stated)

/-- Restate the derivation step `initial` as a proof of `target` when the formula it proves
agrees with `target` once some definitions are opened. -/
def convertStep (g : ProofGoal) (initial : DeriveM Nat) (target : FormulaView) :
    TacticM (Option (DeriveM Nat)) := do
  let (root, graph) ← initial.run {}
  let formula := graph.nodes[root]!.formula
  if formula.equiv target then return some initial
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  let source ← formula.encode L [] g.free
  let stated ← target.encode L [] g.free
  let some equality ← calculateOpeningEquality source stated | return none
  let proof := transportAlong L T g.context.code source stated equality
    (← derivedProof g graph root).2
  return some (addNode target
    (if g.context.code == emptyList then .proven proof else .localProof proof))

/-- Open the definitions `names` wherever they occur in the conclusion of the goal, or in the
assumption `location` when one is given. -/
def openNamed (names : List Name) (location : Option Ident) : TacticM Unit := do
  let g ← currentGoal
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  let changed (code : Core.Term) : TacticM Calculation := do
    let result ← openDefinitions names code
    if result.value == (← openDefinitions [] code).value then
      throwError "the formula does not use the definitions to open"
    return result
  let some h := location |
    let encoded ← g.formula.encode L [] g.free
    let opened ← changed encoded
    applySequentRule g [opened.value] encoded fun proofs =>
      return transportAlong L T g.context.code opened.value encoded
        (mkEqSymm encoded opened.value opened.proof) proofs[0]!
  let name := h.getId.eraseMacroScopes
  let (entries, tail) := listEntries g.context.code
  let some index := g.context.entries.findIdx? (·.1 == name) |
    throwErrorAt h "unknown object assumption `{name}`"
  let code := unmarked entries[index]!
  let opened ← changed code
  let list (entry : Core.Term) := (entries.set index entry).foldr consList tail
  let source := list (markName name opened.value)
  let hole := Core.Term.lam `A ((entries.zipIdx.map fun (entry, i) =>
    if i == index then Core.Term.bvar 0 else entry.shift).foldr consList tail.shift)
  let equality := mkEqCongr hole opened.value code
    (mkEqSymm code opened.value opened.proof)
  let premise := provableUnder L T source g.code
  let proof := Core.Proof.impIntro `_folPremise premise
    (transportList L T source g.context.code g.code equality (.hyp 0))
  let view := (← getGoal).projection
  Tactic.applyProof (view.decodeProof proof) [view.decodePredicate premise]

/-- The derivation step that proves the assumption at position `index` of the goal's list. -/
def assumptionStep (g : ProofGoal) (index : Nat) : TacticM (DeriveM Nat) := do
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  let some (_, formula) := g.context.entries[index]? | throwError "unknown object assumption"
  let some (entry, proof) := assumptionProof L T g.context.code index |
    throwError "unknown object assumption"
  let proof ← transportUnder L T g.context.code entry (← formula.encode L [] g.free) proof
  return addNode formula (.localProof proof)

/-- Replace the assumption at position `index` of the goal's list by `replacement`, keeping its
name and position. `step` derives `replacement` from the goal's assumptions.

The new goal `Γ' ⊢ A` differs from the goal `Γ ⊢ A` only at that position. Moving the entries up
to that position into the conclusion with `Sequent.imp_intro`, and adding them back with
`Sequent.weaken`, turns a proof of `Γ' ⊢ A` into a proof of `Γ ⊢ B' → Cₖ₋₁ → … → C₀ → A`, where
`B'` is the replacement and `Cₖ₋₁, …, C₀` are the newer assumptions. Modus ponens with `step`
and with those assumptions then proves `A` from `Γ`. -/
def replaceAssumption (g : ProofGoal) (index : Nat) (replacement : FormulaView)
    (step : DeriveM Nat) : TacticM Unit := do
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  let (entries, tail) := listEntries g.context.code
  let some (name, _) := g.context.entries[index]? | throwError "unknown object assumption"
  let marked := markName name (← replacement.encode L [] g.free)
  let replaced := entries.set index marked
  let list (items : List Core.Term) (k : Nat) := (items.drop k).foldr consList tail
  let premise := provableUnder L T (list replaced 0) g.code
  -- A proof of `Γ ⊢ B' → Cₖ₋₁ → … → C₀ → A` from the new goal, the hypothesis `.hyp 0`.
  let mut conclusion := g.code
  let mut proof : Core.Proof := .hyp 0
  for k in [:index + 1] do
    proof := applyTheorem `FOL.Sequent.imp_intro [list replaced (k + 1), replaced[k]!, conclusion]
      [L, T] [proof]
    conclusion := applyDefinition `FOL.Formula.imp [replaced[k]!, conclusion]
  for k in (List.range (index + 1)).reverse do
    proof := applyTheorem `FOL.Sequent.weaken [list entries (k + 1), entries[k]!, conclusion]
      [L, T] [proof]
  let chain := (g.context.entries.take index).foldl (fun body (_, a) => .imp a body) g.formula
  let chain := FormulaView.imp replacement chain
  proof ← transportUnder L T g.context.code conclusion (← chain.encode L [] g.free) proof
  let newer ← (List.range index).mapM (assumptionStep g)
  let ((replacementProof, newerProofs), graph) ← (do
    let p ← step
    let qs ← newer.mapM id
    return (p, qs)).run {}
  -- The derivation sits beneath the hypothesis for the new goal.
  let graph := { graph with nodes := graph.nodes.map fun node =>
    match node.reason with
    | .proven p => { node with reason := .proven (shiftHypotheses 1 p) }
    | .localProof p => { node with reason := .localProof (shiftHypotheses 1 p) }
    | _ => node }
  let (root, graph) ← (do
    let mut q ← mp (← addNode chain (.localProof proof)) replacementProof
    for p in newerProofs.reverse do q ← mp q p
    return q).run graph
  let result ← proofInContext g graph root g.formula
  let result ← transportGoal g (← g.formula.encode L [] g.free) result
  let view := (← getGoal).projection
  Tactic.applyProof (view.decodeProof (.impIntro `_folPremise premise result))
    [view.decodePredicate premise]

/-- Close the PRA goal with the checked proof generated from a completed derivation. -/
def finish (g : ProofGoal) (action : DeriveM Nat) : TacticM Unit := do
  let (root, graph) ← action.run {}
  let proof ← proofInContext g graph root g.formula
  let L := languageTerm g.theory.language
  let encoded ← g.formula.encode L [] g.free
  let proof ← transportGoal g encoded proof
  Tactic.close ((← getGoal).projection.decodeProof proof)

/-- Discharge object assumptions in their original implication order. -/
def discharge (hypotheses : List (Name × FormulaView)) (root : Nat) : DeriveM Nat :=
  hypotheses.reverse.foldlM (fun p (h, a) => deduct h a p) root

/-- Open an object universal quantifier. The local assumptions are shifted past the new
variable, and the visible object variables are renumbered. -/
def introduceVariable (name : Ident) : TacticM Unit := do
  let g ← currentGoal
  let .all x body := g.formula | throwError "pintro requires an object universal quantifier"
  let L := languageTerm g.theory.language
  let theory := applyDefinition (g.theory.name ++ `isAxiom)
  let code ← body.encode L [] (x :: g.free)
  let goal ← getGoal
  let result := applyDefinition `FOL.Formula.all [code]
  let (premise, proof) ← if g.context.code == emptyList then
      pure (provable L theory code,
        applyTheorem `FOL.Provable.gen [code] [L, theory] [.hyp 0])
    else do
      unless (listEntries g.context.code).2 == emptyList do
        throwError "pintro cannot shift local assumptions that are not written out"
      let shifted ← g.context.entries.foldrM (fun (h, a) rest => do
        return consList (markName h (← a.encode L [] (x :: g.free))) rest) emptyList
      let mapped := shiftedList L g.context.code
      let equality ← shiftedListEquality L g.context.code shifted
      let p := transportList L theory shifted mapped code (mkEqSymm mapped shifted equality)
        (.hyp 0)
      pure (provableUnder L theory shifted code,
        applyTheorem `FOL.Sequent.all_intro [g.context.code, code] [L, theory] [p])
  let proof ← transportGoal g result proof
  let proof := Core.Proof.impIntro `h premise proof
  let view := goal.projection
  Tactic.applyProof (view.decodeProof proof) [view.decodePredicate premise]
  -- Renumber the visible variables beneath the new position; the new variable is defined last.
  let position (i : Nat) := view.decodeTerm
    (.letE `_folBoundVariable (applyDefinition `FOL.Term.var [L, numeral i]) (.bvar 0))
  for (alias, value) in goal.names.termAliases.reverse do
    let .letE `_folBoundVariable value (.bvar 0) := value | continue
    let (head, args) := getAppFnArgs value
    if head == .definition `FOL.Term.var [] then
      if let [l, index] := args then
        if l == L then
          if let some i := numeralValue? index then Tactic.redefine alias (position (i + 1))
  Tactic.define name.getId.eraseMacroScopes (position 0) name

/-- Move an implication antecedent into the list of local assumptions under the given name. -/
def introduceAssumption (name : Ident) : TacticM Unit := do
  let g ← currentGoal
  let .imp a b := g.formula | throwError "pintro expects an implication"
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  let A := markName name.getId.eraseMacroScopes (← a.encode L [] g.free)
  let B ← b.encode L [] g.free
  let premise := provableUnder L T (consList A g.context.code) B
  let p := ofSequent L T g.context.code (applyDefinition `FOL.Formula.imp [A, B])
    (applyTheorem `FOL.Sequent.imp_intro [g.context.code, A, B] [L, T] [.hyp 0])
  let p ← transportGoal g (applyDefinition `FOL.Formula.imp [A, B]) p
  let p := Core.Proof.impIntro `h premise p
  let view := (← getGoal).projection
  Tactic.applyProof (view.decodeProof p) [view.decodePredicate premise]

/-- Create PRA subgoals and connect their proofs through a checked derivation. -/
def refineDerivation (g : ProofGoal)
    (initial : DeriveM (List FormulaView × (List Nat → DeriveM Nat))) : TacticM Unit := do
  let ((children, assemble), graph) ← initial.run {}
  let count := children.length
  let graph := { graph with nodes := graph.nodes.map fun node =>
    match node.reason with
    | .proven p => { node with reason := .proven (shiftHypotheses count p) }
    | .localProof p => { node with reason := .localProof (shiftHypotheses count p) }
    | _ => node }
  let action : DeriveM Nat := do
    let inputs ← children.zipIdx.mapM fun (a, i) =>
      let p := Core.Proof.hyp (count - i - 1)
      addNode a (if g.context.code == emptyList then .proven p else .localProof p)
    assemble inputs
  let (root, graph) ← action.run graph
  let L := languageTerm g.theory.language
  let premises ← children.mapM fun a => do goalPredicate g (← a.encode L [] g.free)
  let mut proof ← proofInContext g graph root g.formula
  let encoded ← g.formula.encode L [] g.free
  proof ← transportGoal g encoded proof
  for premise in premises.reverse do
    proof := .impIntro `_folPremise premise proof
  let view := (← getGoal).projection
  Tactic.applyProof (view.decodeProof proof) (premises.map view.decodePredicate)

end LeanPRA.Library.FOL.DSL.TacticSupport
