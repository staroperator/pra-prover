module

public meta import PRAProver.Library.FOL.DSL.Tactic.Context

/-!
# Applying induction schemas in declared FOL theories

`evalInductionTactic` applies the theorem of a declared induction schema with `zero`/`succ`
branches or a single `step` branch. The schema supplies the terms and the induction hypothesis.
Each branch is an ordinary PRA tactic proof of the required object derivation. When the schema
has an `assuming` restriction, `(assuming := h)` supplies a PRA proof of it for the motive;
without it, the restriction is discharged like any PRA antecedent of a theorem, from the local
PRA hypotheses or by calculation.
-/

public meta section

namespace PRAProver.Library.FOL.DSL

open Lean Elab Command PRAProver.Core
open PRAProver.Surface PRAProver.Surface.Tactic
open PRAProver.Library.Tactic.Construction
open TacticSupport

private structure InductionPattern where
  base : Option TermView
  binder : Name
  hypothesis : FormulaView
  next : TermView

private def inductionPattern (info : AxiomInfo) : Option InductionPattern := do
  unless info.parameters.size == 1 && info.parameters[0]!.arity == 1 &&
      info.parameters[0]!.isFormula && !info.parameters[0]!.isNumeric do none
  match info.template with
  | .imp (.parameter 0 [base])
      (.imp (.all x (.imp (.parameter 0 [.var z]) (.parameter 0 [next])))
        (.all y (.parameter 0 [.var w]))) =>
    if x == z && y == w && base.variables.isEmpty && next.variables.all (· == x) then
      some ⟨some base, x, .parameter 0 [.var x], next⟩ else none
  | .imp (.all x (.imp hypothesis (.parameter 0 [.var z])))
      (.all y (.parameter 0 [.var w])) =>
    if x == z && y == w then some ⟨none, x, hypothesis, .var x⟩ else none
  | _ => none

/-- The theorems of induction shape among the axioms of the theory and its parents. -/
private def inductionTheorems (T : TheoryInfo) :
    CommandElabM (List (Name × InductionPattern)) := do
  let mut choices := []
  let mut theory := some T
  while let some current := theory do
    for info in current.axioms.toList.drop current.inherited do
      if let some pattern := inductionPattern info then
        choices := choices ++ [(current.name ++ info.name, pattern)]
    theory ← current.parent.mapM fun parent => (findTheory parent : CommandElabM TheoryInfo)
  return choices

private def selectInduction (T : TheoryInfo) (selected : Option Ident) :
    TacticM (Name × InductionPattern) := do
  let choices ← inductionTheorems T
  if let some selected := selected then
    let name := selected.getId.eraseMacroScopes
    let some declaration ← resolveDeclaration? (← getGoal).environment name |
      throwErrorAt selected "unknown induction theorem `{name}`"
    let some choice := choices.find? (·.1 == declaration.name) |
      throwErrorAt selected "the selected theorem has no supported induction shape"
    return choice
  match choices with
  | [choice] => return choice
  | [] => throwError "this theory has no induction theorem of a supported shape"
  | _ => throwError "multiple induction theorems are available; select one with `using`"

private def runBranch (goal : GoalId) (steps : TSyntax ``praTacticSeq) : TacticM Unit := do
  set [goal]
  evalTacticSeq steps
  unless (← get).isEmpty do throwErrorAt steps "unfinished FOL induction branch"

private def inductionTactic (g : ProofGoal) (x : Ident) (selected binder : Option Ident)
    (explicitMotive : Option (TSyntax `folFormula)) (guard : Option (TSyntax `praExpr))
    (k ih : Ident) (base : Option (TSyntax ``praTacticSeq)) (step : TSyntax ``praTacticSeq) :
    TacticM Unit := do
  let (theoremName, pattern) ← selectInduction g.theory selected
  unless pattern.base.isSome == base.isSome do throwError "induction branch shape mismatch"
  let variableCode ← coreTerm (← `(praExpr| $x:ident))
  let .var y ← readTerm g.theory.language [] g.free variableCode |
    throwErrorAt x "induction requires an introduced FOL variable"
  if let some binder := binder then
    let some explicitMotive := explicitMotive | throwError "missing induction motive"
    let specified ← formulaArgument g explicitMotive [binder.getId.eraseMacroScopes]
    let expected := g.formula.replace y (.var binder.getId.eraseMacroScopes)
    unless specified.equiv expected do
      throwError "the induction motive does not match the goal"
  let fresh ← liftCoreM (mkFreshUserName k.getId.eraseMacroScopes)
  let motive := g.formula.replace y (.var fresh)
  let actuals : Array Actual := #[.formula motive [fresh]]
  let hypothesis := (instantiateSchema actuals pattern.hypothesis).replace
    pattern.binder (.var fresh)
  let next := pattern.next.replace pattern.binder (.var fresh)
  let stepGoal := FormulaView.all fresh (.imp hypothesis (motive.replace fresh next))
  let baseGoal := pattern.base.map (fun t => g.formula.replace y t)
  let L := languageTerm g.theory.language
  let motiveCode ← (Actual.formula motive [fresh]).encode L [] g.free
  let some (.theoremE declaration) := (← getGoal).environment.lookup theoremName |
    throwError "unknown induction theorem `{theoremName}`"
  let proof := Core.Proof.theoremE theoremName [motiveCode] []
  let type := declaration.type.instantiate [motiveCode] []
  let (proof, type) ← match guard with
    | some guard => supplyAntecedent x m!"{theoremName}" proof type (← coreProof guard)
    | none => dischargeAntecedents x m!"{theoremName}" proof type
  let (proof, type) ← normalizeProvable proof type
  let initial ← proofRule g proof type
  let rest := (← get).drop 1
  refineDerivation g do
    let p ← initial
    return (baseGoal.toList ++ [stepGoal], fun inputs => do
      let mut proof := p
      for premise in inputs do proof ← mp proof premise
      instantiate proof (.var y))
  let goals := (← get).take (if base.isSome then 2 else 1)
  if let some base := base then runBranch goals[0]! base
  set [goals.getLast!]
  introduceVariable k
  introduceAssumption ih
  evalTacticSeq step
  unless (← get).isEmpty do throwErrorAt step "unfinished FOL induction branch"
  set rest

/-- Apply ordinary or strong induction through the theory's declared schema. -/
@[pra_tactic pinductionTac, pra_tactic pstrongInductionTac]
def evalInductionTactic : Tactic := closedFirst fun stx => do
  match stx with
  | `(praTactic| pinduction $x:ident $[using $selected:ident]?
      $[(motive := fun $binder:ident => $motive:folFormula)]?
      $[(assuming := $guard:praExpr)]? with
      | zero => $base:praTacticSeq
      | succ $k:ident $ih:ident => $step:praTacticSeq) =>
    inductionTactic (← currentGoal) x selected binder motive guard k ih (some base) step
  | `(praTactic| pinduction $x:ident $[using $selected:ident]?
      $[(motive := fun $binder:ident => $motive:folFormula)]?
      $[(assuming := $guard:praExpr)]? with
      | step $k:ident $ih:ident => $step:praTacticSeq) =>
    inductionTactic (← currentGoal) x selected binder motive guard k ih none step
  | _ => throwUnsupportedSyntax

end PRAProver.Library.FOL.DSL
