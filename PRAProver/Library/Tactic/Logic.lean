module

public meta import PRAProver.Library.Tactic.Combinators
public import PRAProver.Library.Logic

/-!
# Elementary logical PRA tactics

- `exact` closes a goal with a proof; `refine` exposes `?_` proof holes as new goals and infers `_`
  arguments from constraints, including constraints supplied by later proofs of those goals.
- `intro` introduces numerical variables and implication hypotheses.
- `rintro` introduces names and destructures nested tuple and disjunction patterns, as in
  `rintro n (hp, hq)` or `rintro (hp | hq)`. Later patterns are introduced in every branch.
- `rcases h with pat` destructures a proof with the same patterns as `rintro`, including
  `((hp, hq) | hr)` and `(n, (hp | hq))`. A local source hypothesis is removed from each branch.
  Tuples also accept angle brackets, as in `⟨hp, hq⟩`.
- `constructor`, `left`, `right`, and `exists` build logical introductions.
- `assumption`, `rfl`, and `exfalso` use hypotheses, equality reflexivity, and falsity elimination.
- `by_contra h` applies `dne` to the goal `P`, introducing `h : ¬ P` with goal `False`.
  Bare `by_contra` chooses a fresh hypothesis name.
- `apply` supplies proof and numerical holes until a theorem matches the goal.

The implementations construct PRA proof expressions and use the shared refinement interface.
-/

public meta section

namespace PRAProver.Library.Tactic

open Lean Elab PRAProver.Surface PRAProver.Surface.Tactic

syntax (name := exactTac) "exact" praExpr : praTactic
syntax (name := refineTac) "refine" praExpr : praTactic
syntax (name := introTac) "intro" (ppSpace colGt praFunBinder)* : praTactic

/-- Patterns shared by `rintro` and `rcases`: names, ignored binders, tuples, and disjunctions. -/
declare_syntax_cat praCasesPattern

syntax:max ident : praCasesPattern
syntax:max "_" : praCasesPattern
syntax:max "(" praCasesPattern ")" : praCasesPattern
syntax:max "(" praCasesPattern ", " praCasesPattern,+ ")" : praCasesPattern
syntax:max "⟨" praCasesPattern ", " praCasesPattern,+ "⟩" : praCasesPattern
syntax:30 praCasesPattern:31 atomic(" | " praCasesPattern:30) : praCasesPattern
syntax (name := rintroTac) "rintro" (ppSpace colGt praCasesPattern:arg)+ : praTactic
syntax (name := rcasesTac) "rcases" praExpr " with " praCasesPattern : praTactic
syntax (name := constructorTac) "constructor" : praTactic
syntax (name := leftTac) "left" : praTactic
syntax (name := rightTac) "right" : praTactic
syntax (name := existsTac) "exists" praExpr,+ : praTactic
syntax (name := assumptionTac) "assumption" : praTactic
syntax (name := rflTac) "rfl" : praTactic
syntax (name := exfalsoTac) "exfalso" : praTactic
syntax (name := byContraTac) "by_contra" (ppSpace colGt ident)? : praTactic
syntax (name := applyTac) "apply" praExpr : praTactic

macro "rfl" : praExpr => `(praExpr| $(mkIdent `rfl):ident)

/-- Expose the outer connective while preserving the expressions inside it. -/
def headPredicate (goal : Goal) (p : Metavariable.Predicate) : TacticM Metavariable.Predicate :=
  match Metavariable.Bridge.whnfPredicate goal.projection goal.maxDepth goal.environment p with
  | .ok p => pure p
  | .error error => throwError "{error.message}"

private def exactProof (p : TSyntax `praExpr) : TacticM Unit := do
  let count := (← get).length
  Tactic.refine p
  unless (← get).length == count - 1 do throwError "exact left unsolved PRA proof holes"

private partial def hasExplicitHead : Syntax → Bool
  | `(praExpr| @$_id:ident) | `(praExpr| @($_p:praExpr)) => true
  | `(praExpr| ($p:praExpr)) | `(praExpr| $p:praExpr $_a:praExpr) => hasExplicitHead p
  | _ => false

private abbrev PatternSplit := Ident × TSyntax `praCasesPattern × TSyntax `praCasesPattern

private partial def patternNames (stx : Syntax) : List Name :=
  if stx.isIdent then [stx.getId.eraseMacroScopes]
  else stx.getArgs.toList.flatMap patternNames

-- Tuple binders use the existing elaborator. Disjunctions get fresh names for later case splits.
private partial def patternBinder (pat : TSyntax `praCasesPattern) :
    StateT (List Name) TacticM (TSyntax `praFunBinder × List PatternSplit) := do
  match pat with
  | `(praCasesPattern| $id:ident) =>
    let binder ← `(praFunBinder| $id:ident)
    return (⟨binder.raw.setInfo id.raw.getHeadInfo⟩, [])
  | `(praCasesPattern| _) =>
    let binder ← `(praFunBinder| _)
    return (⟨binder.raw.setInfo pat.raw.getHeadInfo⟩, [])
  | `(praCasesPattern| ($p:praCasesPattern)) => patternBinder p
  | `(praCasesPattern| ⟨$p:praCasesPattern, $ps:praCasesPattern,*⟩) =>
    patternBinder (← `(praCasesPattern| ($p:praCasesPattern, $ps:praCasesPattern,*)))
  | `(praCasesPattern| ($p:praCasesPattern, $ps:praCasesPattern,*)) =>
    let (firstBinder, splits) ← patternBinder p
    let mut binders := #[]
    let mut splits := splits
    for p in ps.getElems do
      let (binder, next) ← patternBinder p
      binders := binders.push binder
      splits := splits ++ next
    let binder ← `(praFunBinder| ($firstBinder:praFunBinder, $binders:praFunBinder,*))
    return (⟨binder.raw.setInfo pat.raw.getHeadInfo⟩, splits)
  | `(praCasesPattern| $a:praCasesPattern | $b:praCasesPattern) =>
    let mut name := `rintroHyp
    while (← get).contains name do name := name.appendAfter "'"
    modify (name :: ·)
    let id := mkIdent name
    return (← `(praFunBinder| $id:ident), [(id, a, b)])
  | _ => throwUnsupportedSyntax

-- Tuple elaboration introduces unnamed intermediate proofs. Only named components remain.
private def clearPatternTemporaries (outerCount : Nat) : TacticM Unit := do
  let names := (← getGoal).names.proofs
  for i in (List.range (names.length - outerCount)).reverse do
    if names[i]!.isAnonymous then Tactic.clearHypothesis i

private def clearNamedHypothesis (name : Name) : TacticM Unit := do
  let names := (← getGoal).names.proofs
  let some index := names.idxOf? name | throwError "unknown PRA hypothesis {name}"
  Tactic.clearHypothesis index

private partial def patternSplits (used : List Name) (splits : List PatternSplit)
    (consumeSources : Bool) : TacticM Unit := do
  for (id, a, b) in splits do
    onAllGoals do
      let ((leftBinder, leftSplits), (rightBinder, rightSplits)) ← (do
        let leftResult ← patternBinder a
        let rightResult ← patternBinder b
        pure (leftResult, rightResult)).run' (used ++ (← getGoal).names.used)
      let outerCount := (← getGoal).context.proofs.length
      Tactic.refine (← `(praExpr| or_elim $id:ident
        (fun $leftBinder:praFunBinder => ?_) (fun $rightBinder:praFunBinder => ?_)))
      if consumeSources then onAllGoals do
        clearPatternTemporaries outerCount
        clearNamedHypothesis id.getId
      let [leftGoal, rightGoal] ← get | throwError "pattern split expected two disjunction branches"
      set [leftGoal]
      patternSplits used leftSplits consumeSources
      let leftGoals ← get
      set [rightGoal]
      patternSplits used rightSplits consumeSources
      modify (leftGoals ++ ·)

/-- Elaborate elementary logical tactics into checked PRA proof refinements. -/
@[pra_tactic exactTac, pra_tactic refineTac, pra_tactic introTac, pra_tactic rintroTac,
  pra_tactic rcasesTac, pra_tactic constructorTac, pra_tactic leftTac, pra_tactic rightTac,
  pra_tactic existsTac, pra_tactic assumptionTac, pra_tactic rflTac, pra_tactic exfalsoTac,
  pra_tactic byContraTac, pra_tactic applyTac]
def evalLogical : Tactic := fun stx => do
  match stx with
  | `(praTactic| exact $p:praExpr) => exactProof p
  | `(praTactic| refine $p:praExpr) => Tactic.refine p
  | `(praTactic| intro $xs:praFunBinder*) =>
    let xs ← if xs.isEmpty then do
      let goal ← getGoal
      let mut name := `h
      while goal.names.proofs.contains name || goal.names.locals.contains name do
        name := name.appendAfter "'"
      pure #[← `(praFunBinder| $(mkIdent name):ident)]
    else pure xs
    Tactic.refine (← `(praExpr| fun $xs:praFunBinder* => ?_))
  | `(praTactic| rintro $ps:praCasesPattern*) =>
    let goal ← mainGoal
    let rest := (← get).drop 1
    set [goal]
    let used := patternNames stx
    for pat in ps do
      onAllGoals do
        let (binder, splits) ← (patternBinder pat).run' (used ++ (← getGoal).names.used)
        Tactic.refine (← `(praExpr| fun $binder:praFunBinder => ?_))
        patternSplits used splits false
    modify (· ++ rest)
  | `(praTactic| rcases $p:praExpr with $pat:praCasesPattern) =>
    let main ← mainGoal
    let rest := (← get).drop 1
    set [main]
    let (proof, type) ← Tactic.elaborateProof p
    let goal ← getGoal
    let used := patternNames stx
    let (binder, splits) ← (patternBinder pat).run' (used ++ goal.names.used)
    Tactic.assertPremise type proof
    if let .hyp index := proof then Tactic.clearHypothesis index
    let outerCount := (← getGoal).context.proofs.length
    Tactic.refine (← `(praExpr| fun $binder:praFunBinder => ?_))
    clearPatternTemporaries outerCount
    patternSplits used splits true
    modify (· ++ rest)
  | `(praTactic| constructor) =>
    let goal ← getGoal
    match ← headPredicate goal goal.target with
    | .true => Tactic.refine (← `(praExpr| ()))
    | .and .. => Tactic.refine (← `(praExpr| (?_, ?_)))
    | _ => throwError "constructor expects True or a conjunction; use exists for a witness"
  | `(praTactic| left) => Tactic.refine (← `(praExpr| or_left ?_))
  | `(praTactic| right) => Tactic.refine (← `(praExpr| or_right ?_))
  | `(praTactic| exists $xs:praExpr,*) =>
    for x in xs.getElems do Tactic.refine (← `(praExpr| ($x, ?_)))
  | `(praTactic| assumption) =>
    for i in [:(← getGoal).context.proofs.length] do
      if ← attempt (Tactic.close (.hyp i)) then return
    throwError "no PRA hypothesis matches the goal"
  | `(praTactic| rfl) =>
    let goal ← getGoal
    let .equal lhs _ ← headPredicate goal goal.target | throwError "rfl expects an equality goal"
    Tactic.close (.forallElim .eqRefl lhs)
  | `(praTactic| exfalso) => Tactic.refine (← `(praExpr| false_elim ?_))
  | `(praTactic| by_contra $[$name:ident]?) =>
    let goal ← getGoal
    let name := name.getD (mkIdent (goal.names.freshName "h" `h))
    let binder ← `(praFunBinder| $name:ident)
    let binder : TSyntax `praFunBinder := ⟨binder.raw.setInfo name.raw.getHeadInfo⟩
    Tactic.applyProof (.theoremE `dne [] [goal.target])
      [.imp (.imp goal.target .false) .false]
    Tactic.refine (← `(praExpr| fun $binder:praFunBinder => ?_))
  | `(praTactic| apply $p:praExpr) =>
    let goal ← getGoal
    let restore ← saveState
    let mut type ← infer p
    let explicit := hasExplicitHead p
    let mut arguments : List Bool := []
    for _ in [:goal.maxDepth] do
      match ← headPredicate goal type with
      | .all motive =>
        let implicit := match motive with
          | .lam info _ => info.isImplicit && !explicit
          | _ => false
        unless implicit do arguments := arguments ++ [false]
        type := Metavariable.Bridge.betaReducePredicate goal.projection goal.maxDepth
          (.app motive.shift (.bvar 0))
      | .imp _ result =>
        arguments := arguments ++ [true]
        type := result
      | _ => break
    restore
    let mut candidate := p
    if ← attempt (Tactic.refine candidate) then return
    for proofArgument in arguments do
      candidate ← if proofArgument then `(praExpr| $candidate ?_) else `(praExpr| $candidate _)
      if ← attempt (Tactic.refine candidate) then return
    throwError "apply could not match the PRA goal"
  | _ => throwUnsupportedSyntax

end PRAProver.Library.Tactic
