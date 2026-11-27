module

public meta import PRAProver.Library.FOL.DSL.Display
public meta import PRAProver.Library.FOL.DSL.Proof.Logic

/-!
# Basic FOL tactics

`evalBasicTactic` implements introduction, exact proofs, application, cases, and propositional
reasoning through the shared PRA tactic interface. Object assumptions form an explicit local
context, and implication introduction uses the checked deduction rule. A tactic that needs the
connective of a formula opens the definition at its head; `passumption`, `pexact`, and `papply`
accept a formula that agrees with the goal once definitions are opened. A proof reference names
an assumption, an axiom, or a PRA proof, or applies one to arguments in the application form.

`pcases h with pat` uses names, ignored components, tuple patterns, and alternatives to name
the resulting variables and assumptions. A local source hypothesis is removed from each branch,
along with temporary assumptions used while processing nested patterns. Nested alternatives
produce separate goals.
-/

public meta section

namespace PRAProver.Library.FOL.DSL

open Lean Elab Command PRAProver.Core
open PRAProver.Surface PRAProver.Surface.Tactic
open PRAProver.Library.Tactic.Construction
open PRAProver.Library.Tactic
open TacticSupport

private def dischargeResult (goal : FormulaView) (p : Nat) : DeriveM Nat := do
  let (hs, _) := assumptions goal
  let mut target := goal
  let mut introduced := []
  for h in hs do
    if target.equiv (← conclusion p) then return ← discharge introduced p
    introduced := introduced ++ [h]
    let .imp _ b := target | throwError "invalid implication context"
    target := b
  unless target.equiv (← conclusion p) do throwError "pexact conclusion differs from the goal"
  discharge introduced p

/-- Instantiate the leading universal quantifiers of a derived formula with `args`. The terms
are collected in one substitution by `Sequent.subst_consSubst_of_all` and
`subst_consSubst_of_subst_all`, and the resulting formula is calculated once. A formula whose
quantifiers stand behind implications is instantiated step by step inside the derivation. -/
private def instantiated (g : ProofGoal) (initial : DeriveM Nat)
    (args : Array (TSyntax `folTerm)) : TacticM (DeriveM Nat) := do
  let terms ← args.toList.mapM (termArgument g)
  let isQuantified : FormulaView → Bool := fun | .all _ _ => true | _ => false
  let initial ← if terms.isEmpty then pure initial else exposeStep g initial isQuantified
  -- Each step opens the definitions in front of the next quantifier before instantiating it.
  let mut stepwise := initial
  for t in terms do
    let exposed ← exposeStep g stepwise isQuantified
    stepwise := do instantiate (← exposed) t
  if terms.isEmpty then return stepwise
  let (root, graph) ← initial.run {}
  let mut body := graph.nodes[root]!.formula
  for t in terms do
    let .all x a := body | return stepwise
    body := a.replace x t
  let L := languageTerm g.theory.language
  let theory := applyDefinition (g.theory.name ++ `isAxiom)
  let Γ := g.context.code
  let (formula, derived) ← derivedProof g graph root
  let mut code ← formula.encode L [] g.free
  let mut values : List Core.Term := []
  let mut proof := asSequent L theory Γ code derived
  for t in terms do
    let (.definition `FOL.Formula.all [], [A]) := getAppFnArgs code | return stepwise
    let value ← t.encode L [] g.free
    proof := if values.isEmpty then
        applyTheorem `FOL.Sequent.subst_consSubst_of_all [Γ, A, value] [L, theory] [proof]
      else applyTheorem `FOL.Sequent.subst_consSubst_of_subst_all [Γ, A, value]
        [L, theory, SubstitutionView.encode L ⟨values, 0⟩] [proof]
    values := value :: values
    code := A
  let substituted := applyDefinition `FOL.Formula.subst [L, code]
    [SubstitutionView.encode L ⟨values, 0⟩]
  let result ← transportUnder L theory Γ substituted (← body.encode L [] g.free)
    (ofSequent L theory Γ substituted proof)
  return addNode body (if Γ == emptyList then .proven result else .localProof result)

/-- Close the goal with the derivation step `step`. The step may prove the goal behind some of
its leading premises, or state it with some definitions opened or closed. -/
private def exactStep (g : ProofGoal) (step : DeriveM Nat) : TacticM Unit := do
  try finish g do dischargeResult g.formula (← step)
  catch error =>
    if error.isInterrupt then throw error
    let some converted ← convertStep g step g.formula | throw error
    finish g converted

private def instantiatedRule (g : ProofGoal) (ref : TSyntax `folRef)
    (args : Array (TSyntax `folTerm)) : TacticM (DeriveM Nat) := do
  instantiated g (← rule g ref) args

private def isExistence : FormulaView → Bool
  | .imp (.all _ (.imp _ .falsum)) .falsum => true
  | _ => false

private def isConjunction : FormulaView → Bool
  | .imp (.imp _ (.imp _ .falsum)) .falsum => true
  | _ => false

private def isDisjunction : FormulaView → Bool
  | .imp (.imp _ .falsum) _ => true
  | _ => false

private def introduce (name : Ident) : TacticM Unit := do
  let g ← currentGoalAs fun | .all _ _ | .imp _ _ => true | _ => false
  if let .all _ _ := g.formula then introduceVariable name
  else introduceAssumption name

/-- The formulas `Pₖ → ⋯ → Pₙ → C` that remain of `P₁ → ⋯ → Pₙ → C` after its leading
premises, each with the premises before it. -/
private def conclusions : FormulaView → List (List FormulaView × FormulaView)
  | .imp a b => ([], .imp a b) :: (conclusions b).map fun (premises, c) => (a :: premises, c)
  | a => [([], a)]

/-- When no conclusion of the step `initial` is the goal as written, restate the step, or a
component of a conjunction it proves, with a conclusion that agrees with the goal once
definitions are opened. -/
private partial def matchConclusion (g : ProofGoal) (initial : DeriveM Nat) :
    TacticM (DeriveM Nat) := do
  let (root, graph) ← initial.run {}
  let formula := graph.nodes[root]!.formula
  if (conclusions formula).any (·.2.equiv g.formula) then return initial
  if let some step ← restate initial formula then return step
  -- A closed definition at the head of the step is opened, and the match is tried again.
  let opened ← exposeStep g initial fun | .code .. => false | _ => true
  let (root', graph') ← opened.run {}
  if graph'.nodes[root']!.formula.equiv formula then return initial
  matchConclusion g opened
where
  restate (step : DeriveM Nat) (formula : FormulaView) : TacticM (Option (DeriveM Nat)) := do
    -- The conclusion behind every premise is tried first.
    for (premises, _) in (conclusions formula).reverse do
      let restated := premises.foldr FormulaView.imp g.formula
      if let some converted ← convertStep g step restated then return some converted
    if let .imp (.imp a (.imp b .falsum)) .falsum := formula then
      if let some converted ← restate (do conjunctionLeft (← step)) a then return some converted
      if let some converted ← restate (do conjunctionRight (← step)) b then return some converted
    return none

private def applyRule (g : ProofGoal) (initial : DeriveM Nat) : TacticM Unit := do
  let target := g.formula
  let initial ← matchConclusion g initial
  refineDerivation g do
    let mut p ← initial
    let rec directPremises (a : FormulaView) : Option (List FormulaView) :=
      if a.equiv target then some [] else match a with
      | .imp a b => (directPremises b).map (a :: ·)
      | _ => none
    if let some premises := directPremises (← conclusion p) then
      return (premises, fun inputs => do
        let mut q := p
        for r in inputs do q ← mp q r
        return q)
    let rec reaches (a : FormulaView) : Bool :=
      if a.equiv target then true else match a with
      | .imp (.imp b (.imp c .falsum)) .falsum =>
        reaches b || reaches c || target == .falsum
      | .imp _ b => reaches b
      | _ => false
    let mut premises := []
    while !(← conclusion p).equiv target do
      if let .imp (.imp a (.imp b .falsum)) .falsum ← conclusion p then
        if reaches a then
          p ← conjunctionLeft p
          continue
        if reaches b then
          p ← conjunctionRight p
          continue
      let .imp a _ ← conclusion p | throwError "papply conclusion differs from the goal"
      let h ← liftCoreM (mkFreshUserName `_folApply)
      let hp ← addNode a (.hypothesis h)
      premises := premises ++ [(h, a)]
      p ← mp p hp
    p ← discharge premises p
    return (premises.map (·.2), fun inputs => do
      let mut q := p
      for r in inputs do q ← mp q r
      return q)

/-- Instantiate the object quantifiers of a derivation step with `args` and reduce the goal to
the premises of the result. -/
def applyInstantiated (g : ProofGoal) (initial : DeriveM Nat)
    (args : Array (TSyntax `folTerm)) : TacticM Unit := do
  applyRule g (← instantiated g initial args)

private def splitGoal (g : ProofGoal) (kind : Nat) : TacticM Unit := do
  refineDerivation g do
    match kind, g.formula with
    | 0, .imp (.imp a (.imp b .falsum)) .falsum =>
      return ([a, b], fun ps => conjunctionIntro ps[0]! ps[1]!)
    | 1, .imp (.imp a .falsum) b =>
      return ([a], fun ps => disjunctionLeft b ps[0]!)
    | 2, .imp (.imp a .falsum) b =>
      return ([b], fun ps => disjunctionRight a ps[0]!)
    | _, _ => throwError "the goal has the wrong connective"

private def casesRule (g : ProofGoal) (initial : DeriveM Nat) : TacticM Unit := do
  let target := g.formula
  let initial ← exposeStep g initial fun a => isExistence a || isConjunction a || isDisjunction a
  let (root, graph) ← initial.run {}
  -- Eliminate an existential statement by a single rule; the branch goal is `∀ x, A → B`.
  if let .imp (.all x (.imp body .falsum)) .falsum := graph.nodes[root]!.formula then
    let L := languageTerm g.theory.language
    let theory := applyDefinition (g.theory.name ++ `isAxiom)
    let Γ := g.context.code
    let (existential, proof) ← derivedProof g graph root
    let A ← body.encode L [] (x :: g.free)
    let B ← target.encode L [] g.free
    let branch ← (FormulaView.all x (.imp body target)).encode L [] g.free
    let imp (a b : Core.Term) := applyDefinition `FOL.Formula.imp [a, b]
    applySequentRule g [branch] B fun proofs => do
      let statement := applyDefinition `FOL.Formula.ex [A]
      let quantified := applyDefinition `FOL.Formula.all
        [imp A (applyDefinition `FOL.Formula.shift [L, B])]
      let p ← transportUnder L theory Γ (← existential.encode L [] g.free) statement
        (shiftHypotheses 1 proof)
      let q ← transportUnder L theory Γ branch quantified proofs[0]!
      return ofSequent L theory Γ B
        (applyTheorem `FOL.Sequent.ex_elim_of_all_imp [Γ, A, B] [L, theory]
          [asSequent L theory Γ statement p, asSequent L theory Γ quantified q])
    return
  refineDerivation g do
    let p ← initial
    let a ← conclusion p
    match a with
    | .imp (.imp b (.imp c .falsum)) .falsum =>
      return ([.imp b (.imp c target)], fun ps => do
        mp (← mp ps[0]! (← conjunctionLeft p)) (← conjunctionRight p))
    | .imp (.imp b .falsum) c =>
      return ([.imp b target, .imp c target], fun ps => disjunctionElim p ps[0]! ps[1]!)
    | _ => throwError "pcases expects a conjunction or disjunction"

private partial def caseNames (stx : Syntax) : List Name :=
  if stx.isIdent then [stx.getId.eraseMacroScopes]
  else stx.getArgs.toList.flatMap caseNames

private def freshCaseName (reserved : List Name) : TacticM Ident := do
  let g ← currentGoal
  let used := reserved ++ (← getGoal).names.used ++ g.context.entries.map (·.1)
  let mut name := `_pcases
  while used.contains name do name := name.appendAfter "'"
  return mkIdent name

-- Reinsert the removed assumption in a continuation proof, preserving the surrounding order.
private def weakenCaseContext (L T : Core.Term) (tail : Core.Term) :
    List Core.Term → Nat → Core.Term → Core.Proof → Core.Proof
  | [], _, _, proof => proof
  | source :: rest, 0, target, proof =>
    applyTheorem `FOL.Sequent.weaken [rest.foldr consList tail, source, target] [L, T] [proof]
  | head :: rest, index + 1, target, proof =>
    let reduced := (rest.eraseIdx index).foldr consList tail
    let implication := applyDefinition `FOL.Formula.imp [head, target]
    let proof := applyTheorem `FOL.Sequent.imp_intro [reduced, head, target] [L, T] [proof]
    let proof := weakenCaseContext L T tail rest index implication proof
    applyTheorem `FOL.Sequent.cons_of_imp [rest.foldr consList tail, head, target] [L, T] [proof]

private def dropCaseSource (index : Nat) : TacticM Unit := do
  let g ← currentGoal
  let (entries, tail) := listEntries g.context.code
  unless index < entries.length do throwError "missing case source"
  let context := (entries.eraseIdx index).foldr consList tail
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  let premise := provableUnder L T context g.code
  let proof := ofSequent L T g.context.code g.code
    (weakenCaseContext L T tail entries index g.code (asSequent L T context g.code (.hyp 0)))
  let view := (← getGoal).projection
  Tactic.applyProof (view.decodeProof (.impIntro `_folPremise premise proof))
    [view.decodePredicate premise]

private def caseSource (g : ProofGoal) (ref : TSyntax `folRef) :
    TacticM (TacticM Unit) := do
  match ref with
  | `(folRef| $name:ident) =>
    let name := name.getId.eraseMacroScopes
    if let some index := (g.context.entries.map (·.1)).idxOf? name then
      return dropCaseSource index
    if let some index := (← getGoal).names.proofs.idxOf? name then
      return Tactic.clearHypothesis index
    return pure ()
  | _ => return pure ()

mutual

private partial def introduceCase (reserved : List Name) (pat : TSyntax `praCasesPattern) :
    TacticM Unit := withRef pat do
  match pat with
  | `(praCasesPattern| $name:ident) => introduce name
  | `(praCasesPattern| _) =>
    let g ← currentGoalAs fun | .all _ _ | .imp _ _ => true | _ => false
    if let .all _ _ := g.formula then introduceVariable (← freshCaseName reserved)
    else
      let .imp a b := g.formula | throwError "case pattern expects a binder or premise"
      let name ← freshCaseName reserved
      refineDerivation g do
        return ([b], fun ps => deduct name.getId a ps[0]!)
  | `(praCasesPattern| ($p:praCasesPattern)) => introduceCase reserved p
  | _ =>
    let g ← currentGoalAs fun | .all _ _ | .imp _ _ => true | _ => false
    if let .all _ _ := g.formula then
      throwError "an existential witness pattern must be a name or _"
    let name ← freshCaseName reserved
    introduceAssumption name
    let g ← currentGoal
    casesPattern reserved g (← rule g (← `(folRef| $name:ident))) pat (dropCaseSource 0)

private partial def casesPattern (reserved : List Name) (g : ProofGoal)
    (initial : DeriveM Nat) (pat : TSyntax `praCasesPattern)
    (dropSource : TacticM Unit := pure ()) : TacticM Unit := withRef pat do
  match pat with
  | `(praCasesPattern| $name:ident) =>
    refineDerivation g do
      let p ← initial
      let a ← conclusion p
      return ([.imp a g.formula], fun ps => mp ps[0]! p)
    dropSource
    introduceAssumption name
  | `(praCasesPattern| _) => dropSource
  | `(praCasesPattern| ($p:praCasesPattern)) => casesPattern reserved g initial p dropSource
  | `(praCasesPattern| ⟨$p:praCasesPattern, $ps:praCasesPattern,*⟩) =>
    casesPattern reserved g initial
      (← `(praCasesPattern| ($p:praCasesPattern, $ps:praCasesPattern,*))) dropSource
  | `(praCasesPattern| ($p:praCasesPattern, $ps:praCasesPattern,*)) =>
    let initial ← exposeStep g initial fun a => isExistence a || isConjunction a
    let (root, graph) ← initial.run {}
    let source := graph.nodes[root]!.formula
    unless isExistence source || isConjunction source do
      throwError "a tuple case pattern requires an existential or conjunction"
    let rest := ps.getElems
    let head := rest[0]!
    let others := rest.extract 1 rest.size
    let tail ← if rest.size == 1 then pure head else
      `(praCasesPattern| ($head:praCasesPattern, $others:praCasesPattern,*))
    casesRule g initial
    dropSource
    introduceCase reserved p
    onAllGoals (introduceCase reserved tail)
  | `(praCasesPattern| $a:praCasesPattern | $b:praCasesPattern) =>
    let initial ← exposeStep g initial isDisjunction
    let (root, graph) ← initial.run {}
    unless isDisjunction graph.nodes[root]!.formula do
      throwError "an alternative case pattern requires a disjunction"
    casesRule g initial
    onAllGoals dropSource
    let [leftGoal, rightGoal] ← get | throwError "expected two case branches"
    set [leftGoal]
    introduceCase reserved a
    let leftGoals ← get
    set [rightGoal]
    introduceCase reserved b
    modify (leftGoals ++ ·)
  | _ => throwUnsupportedSyntax

end

/-- Elaborate the basic logical tactics through checked PRA proof data. -/
@[pra_tactic pintroTac, pra_tactic pexactTac, pra_tactic papplyTac,
  pra_tactic passumptionTac, pra_tactic pconstructorTac, pra_tactic pleftTac,
  pra_tactic prightTac, pra_tactic pexistsTac, pra_tactic pcasesTac, pra_tactic phaveTac,
  pra_tactic pcontradictionTac, pra_tactic pexfalsoTac]
def evalBasicTactic : Tactic := closedFirst fun stx => do
  match stx with
  | `(praTactic| pintro $xs:ident*) => for x in xs do introduce x
  | `(praTactic| passumption) =>
    let g ← currentGoal
    if let some p ← contextProjection (languageTerm g.theory.language)
        (applyDefinition (g.theory.name ++ `isAxiom)) g.context g.formula g.free then
      finish g (addNode g.formula (.localProof p))
      return
    let (hs, _) := assumptions g.formula
    -- The goal behind each leading premise, with the premises introduced before it.
    let mut target := g.formula
    let mut introduced := []
    let mut stages := []
    for (h, a) in hs do
      introduced := introduced ++ [(h, a)]
      let .imp _ b := target | throwError "invalid implication context"
      target := b
      stages := stages ++ [(introduced, target)]
    for (premises, behind) in stages do
      for (k, c) in premises do
        if c.equiv behind then
          finish g do discharge premises (← addNode c (.hypothesis k))
          return
    -- An assumption may state the goal with some definitions opened or closed. Leading
    -- premises are introduced one by one so that they can be matched the same way.
    let mut current := g
    for i in [:hs.length + 1] do
      for (name, _) in current.context.entries do
        let step ← rule current (← `(folRef| $(mkIdent name):ident))
        if let some converted ← convertStep current step current.formula then
          finish current converted
          return
      let .imp _ _ := current.formula | break
      introduceAssumption (mkIdent (Name.num `_passumption i))
      current ← currentGoal
    throwError "no object assumption matches the goal"
  | `(praTactic| pconstructor) => splitGoal (← currentGoalAs isConjunction) 0
  | `(praTactic| pleft) => splitGoal (← currentGoalAs isDisjunction) 1
  | `(praTactic| pright) => splitGoal (← currentGoalAs isDisjunction) 2
  | `(praTactic| papply $ref:folRef $[[$args:folTerm,*]]?) =>
    let g ← currentGoal
    applyRule g (← instantiatedRule g ref (args.map (·.getElems) |>.getD #[]))
  | `(praTactic| pcases $ref:folRef $[[$args:folTerm,*]]? with $pat:praCasesPattern) =>
    let g ← currentGoal
    let initial ← instantiatedRule g ref (args.map (·.getElems) |>.getD #[])
    let main ← mainGoal
    let rest := (← get).drop 1
    set [main]
    casesPattern (caseNames pat) g initial pat (← caseSource g ref)
    modify (· ++ rest)
  | `(praTactic| pexists $term:folTerm) =>
    let g ← currentGoalAs isExistence
    let .imp (.all x (.imp body .falsum)) .falsum := g.formula |
      throwError "pexists expects an existential goal"
    let t ← termArgument g term
    let L := languageTerm g.theory.language
    let theory := applyDefinition (g.theory.name ++ `isAxiom)
    let A ← body.encode L [] (x :: g.free)
    let witness ← t.encode L [] g.free
    let explicit ← (body.replace x t).encode L [] g.free
    applySequentRule g [explicit] (applyDefinition `FOL.Formula.ex [A]) fun proofs => do
      let instantiated := applyDefinition `FOL.Formula.instantiate [L, A, witness]
      let p ← transportUnder L theory g.context.code explicit instantiated proofs[0]!
      return ofSequent L theory g.context.code (applyDefinition `FOL.Formula.ex [A])
        (applyTheorem `FOL.Sequent.ex_intro [g.context.code, A, witness] [L, theory]
          [asSequent L theory g.context.code instantiated p])
  | `(praTactic| phave $name:ident : $formula:folFormula) =>
    let g ← currentGoal
    let a ← formulaArgument g formula
    refineDerivation g do
      return ([a, .imp a g.formula], fun ps => mp ps[1]! ps[0]!)
    let firstGoal :: secondGoal :: rest ← get | throwError "missing phave goals"
    set [secondGoal]
    introduceAssumption name
    let next ← get
    set (firstGoal :: next ++ rest)
  | `(praTactic| pexfalso) =>
    let g ← currentGoal
    refineDerivation g do
      return ([.falsum], fun ps => falseElim g.formula ps[0]!)
  | `(praTactic| pcontradiction) =>
    let g ← currentGoal
    let target := g.formula
    if target == .falsum then
      let localFacts ← g.context.entries.mapM fun (_, a) => do
        let some proof ← contextProjection (languageTerm g.theory.language)
            (applyDefinition (g.theory.name ++ `isAxiom)) g.context a g.free |
          throwError "missing local assumption projection"
        pure (a, proof)
      finish g do
        let mut facts : List Nat := []
        for (a, proof) in localFacts do facts := facts ++ [← addNode a (.localProof proof)]
        for _ in [:facts.length + 1] do
          for p in facts do
            if let .imp a _ ← conclusion p then
              for q in facts do
                if a.equiv (← conclusion q) then
                  let r ← mp p q
                  if (← conclusion r) == .falsum then return r
                  unless facts.contains r do facts := facts ++ [r]
        throwError "no contradiction follows by modus ponens"
    else
      refineDerivation g do
        return ([target.neg.neg], fun ps => doubleNegation target ps[0]!)
  | `(praTactic| pexact $ref:folRef $[[$args:folTerm,*]]?) =>
    let g ← currentGoal
    exactStep g (← instantiatedRule g ref (args.map (·.getElems) |>.getD #[]))
  | _ => throwUnsupportedSyntax

end PRAProver.Library.FOL.DSL
