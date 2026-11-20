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
- `closedFirst` runs a tactic with definitions closed and, when that fails, runs it again with
  every definition opened.
- `currentGoalAs` and `exposeStep` open the definition at the head of a formula for a tactic
  that needs its connective; `convertStep` restates a step whose formula agrees with another
  once definitions are opened; `openNamed` opens definitions by name.
- `rule` resolves assumptions, axioms, and existing PRA proofs; `proofRule` does this for a
  proof given as a Core proof term.
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

private def findAxiomIndex? (T : TheoryInfo) (name : Name) : CommandElabM (Option Nat) := do
  if let some i := T.axioms.toList.findIdx? (fun info => info.name == name) then return some i
  let declaration ← resolveDeclaration? (CoreEnvironment.getState (← getEnv)) (name ++ `isAxiom)
  return T.axioms.toList.findIdx? fun info =>
    declaration.any (·.name == T.name ++ info.name ++ `isAxiom)

/-- Resolve a declared axiom name within the selected theory and the current namespace scope. -/
def axiomIndex (T : TheoryInfo) (name : Name) : CommandElabM Nat := do
  let some i ← findAxiomIndex? T name |
    throwError "unknown axiom schema `{name}` for `{T.name}`"
  return i

/-- Add an instantiated axiom and report the free variables used to close it. -/
def addAxiomInstance (T : TheoryInfo) (index : Nat) (actuals : Array FormulaActual) :
    DeriveM (Nat × List Name) := do
  let info := T.axioms[index]!
  unless actuals.size == info.parameters.size do
    throwError "axiom `{info.name}` expects {info.parameters.size} syntax parameters"
  for (actual, parameter) in actuals.zip info.parameters do
    unless actual.binders.length == parameter.arity &&
        actual.termBody.isNone == parameter.isFormula do
      throwError "syntax parameter kind or arity mismatch"
  let formula := instantiateSchema actuals info.template
  let parameters := formula.variables.eraseDups
  let closed := parameters.foldr FormulaView.all formula
  let root ← addNode closed (.theory index actuals parameters)
  return (root, parameters)

/-- The selected theory, numerical formula code, and decoded view of a PRA provability goal. -/
structure ProofGoal where
  theory : TheoryInfo
  code : Core.Term
  formula : FormulaView
  free : List Name
  context : LocalContext := {}

/-- Run a tactic with definitions closed. When that fails, run it again with every definition
opened, so that the tactic sees each formula written out in full. The error of the first run is
reported when both fail. -/
def closedFirst (tactic : Tactic) : Tactic := fun stx => do
  if ← opensDefinitions then return ← tactic stx
  let restore ← saveState
  try tactic stx
  catch error =>
    if error.isInterrupt then throw error
    if let .internal _ _ := error then throw error
    restore
    try withOpenDefinitions (tactic stx)
    catch second =>
      if second.isInterrupt then throw second
      restore
      throw error

/-- Elaborate a PRA numerical expression in the current tactic context. -/
def coreTerm (stx : TSyntax `praExpr) : TacticM Core.Term := do
  let value ← elaborateTerm stx
  return (← getGoal).projection.encodeTerm value

/-- Read a provability statement of a declared theory, including its optional assumption list. -/
private def provability (type : Core.Predicate) :
    CommandElabM (TheoryInfo × Core.Term × Option Core.Term) := do
  let some (L, theory, code, context) := provabilityParts? type |
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

/-- Elaborate a named syntax actual, including captures and omitted final arguments. -/
def syntaxArgument (g : ProofGoal) (parameter : SyntaxParameter) (binders : List Name)
    (body : TSyntax `folFormula) : TacticM FormulaActual := do
  let parsed ← if parameter.isFormula then pure body.raw else pure (← formulaAsTerm body).raw
  let (parsed, scope) ← if binders.isEmpty then completeApplication parsed parameter []
    else do
      unless binders.length == parameter.arity do
        throwErrorAt body
          "parameter `{parameter.name}` expects {parameter.arity} explicit arguments"
      pure (parsed, binders.reverse)
  if parameter.isFormula then
    let formula ← formulaArgument g ⟨parsed⟩ scope
    return { body := formula, binders := scope.reverse }
  let origin := activeSyntaxContext.getState (← getEnv)
  let expr ← termExpression g.theory.language scope parsed #[] (g.free.length - origin)
  let term ← readTerm g.theory.language scope g.free (← coreTerm expr)
  return { body := .falsum, binders := scope.reverse, termBody := some term }

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
  let some (L, theory, conclusion, context) := provabilityParts? type |
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

/-- Resolve an object assumption, declared axiom, or PRA proof into a derivation step. -/
def rule (g : ProofGoal) (stx : TSyntax `praExpr) : TacticM (DeriveM Nat) := do
  let mut stx := stx
  while let `(praExpr| ($inner:praExpr)) := stx do stx := inner
  if let `(praExpr| $id:ident) := stx then
    let name := id.getId.eraseMacroScopes
    if let some index := g.context.entries.findIdx? (fun (n, _) => n == name) then
      let L := languageTerm g.theory.language
      let theory := applyDefinition (g.theory.name ++ `isAxiom)
      let formula := g.context.entries[index]!.2
      if let some (entry, proof) := assumptionProof L theory g.context.code index then
        let proof ← transportUnder L theory g.context.code entry
          (← formula.encode L [] g.free) proof
        return addNode formula (.localProof proof)
    unless (← getGoal).names.used.contains name ||
        g.context.entries.any (fun (n, _) => n == name) do
      if let some i ← findAxiomIndex? g.theory name then
        return do return (← addAxiomInstance g.theory i #[]).1
      let environment := (← getGoal).environment
      if (← resolveDeclaration? environment name).isNone &&
          (environment.lookup (g.theory.name ++ name)).isSome then
        stx ← expressionCall (g.theory.name ++ name) []
  let (proof, type) ← elaborateProof stx
  let goal ← getGoal
  let proof ← match goal.projection.encodeProof proof with
    | .ok proof => pure proof
    | .error message => throwError "{message}"
  proofRule g proof (goal.projection.encodePredicate type)

/-- Construct the underlying PRA goal predicate under the goal's local assumptions. -/
private def goalPredicate (g : ProofGoal) (code : Core.Term) : CommandElabM Predicate := do
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  return provableUnder L T g.context.code code

private def goalProof (g : ProofGoal) (graph : Derivation) (root : Nat) :
    CommandElabM Core.Proof := do
  if g.context.code == emptyList then derivationProof g.theory graph root g.formula g.free
  else contextualProof g.theory graph root g.formula g.context g.free

private def transportGoal (g : ProofGoal) (encoded : Core.Term) (p : Core.Proof) :
    CommandElabM Core.Proof := do
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  transportUnder L T g.context.code encoded g.code p

/-- A proof that the formula at `root` of a derivation follows from the goal's assumptions,
together with that formula. -/
def derivedProof (g : ProofGoal) (graph : Derivation) (root : Nat) :
    CommandElabM (FormulaView × Core.Proof) := do
  let formula := graph.nodes[root]!.formula
  let proof ← if g.context.code == emptyList then
      derivationProof g.theory graph root formula g.free
    else contextualProof g.theory graph root formula g.context g.free
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
  | .code _ value _ => return (← definitionApplication? value).isSome
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

/-- Return the derivation step `initial` after opening definitions at the head of its formula
until the formula satisfies `wanted` or can no longer be opened. -/
def exposeStep (g : ProofGoal) (initial : DeriveM Nat) (wanted : FormulaView → Bool) :
    TacticM (DeriveM Nat) := do
  let (root, graph) ← initial.run {}
  let mut formula := graph.nodes[root]!.formula
  if wanted formula || !(← isClosedDefinition formula) then return initial
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  let mut proof := (← derivedProof g graph root).2
  let mut code ← formula.encode L [] g.free
  for _ in [:32] do
    if wanted formula then break
    let some opened ← openHead code | break
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

/-- Close the PRA goal with the checked proof generated from a completed derivation. -/
def finish (g : ProofGoal) (action : DeriveM Nat) : TacticM Unit := do
  let (root, graph) ← action.run {}
  let proof ← goalProof g graph root
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
  let mut proof ← goalProof g graph root
  let encoded ← g.formula.encode L [] g.free
  proof ← transportGoal g encoded proof
  let mut premises := []
  for a in children.reverse do
    let premise ← goalPredicate g (← a.encode L [] g.free)
    proof := .impIntro `_folPremise premise proof
    premises := premise :: premises
  let view := (← getGoal).projection
  Tactic.applyProof (view.decodeProof proof) (premises.map view.decodePredicate)

end LeanPRA.Library.FOL.DSL.TacticSupport
