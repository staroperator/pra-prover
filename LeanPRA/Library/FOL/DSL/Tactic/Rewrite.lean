module

public meta import LeanPRA.Library.FOL.DSL.Tactic.Context
public meta import LeanPRA.Library.FOL.DSL.Proof.Logic

/-!
# Equality tactics for FOL proofs

`evalRewriteTactic` implements `prefl`, `prw`, `ptrans`, `psymm`, and `pcongr`.
`prefl` closes an equation whose sides are the same term. On an equality goal, rewriting
constructs equality derivations from the rules and closes the resulting PRA provability goal.
On any other goal, an equation rewrites the terms of the goal wherever they occur, through the
congruence rules, and an equivalence `A ↔ B` rewrites the formula `A` wherever it occurs under
implications, the derived connectives, and quantifiers; the rewritten goal remains. A rule of
`prw` that names a definition opens that definition in the goal, and leaves the resulting goal.
With `at h`, the rules rewrite or open the assumption `h` in the same way, and `h` keeps its
name and position.
Each list entry records the goals before and after its step for the editor. Equality rules
accumulate from left to right, and the closing bracket finishes the resulting equation.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL

open Lean Elab Command LeanPRA.Core
open LeanPRA.Surface LeanPRA.Surface.Tactic
open LeanPRA.Library.Tactic.Construction
open TacticSupport

private partial def matchTerm (binders : List Name) (pattern target : TermView)
    (env : List (Name × TermView)) : Option (List (Name × TermView)) := do
  match pattern, target with
  | .var x, t =>
    if binders.contains x then
      match env.lookup x with
      | some s => if s == t then some env else none
      | none => some ((x, t) :: env)
    else if pattern == target then some env else none
  | .constant i, .constant j => if i == j then some env else none
  | .indexedConst i k, .indexedConst j l => if i == j && k == l then some env else none
  | .app i xs, .app j ys =>
    if i != j || xs.length != ys.length then none else
      (xs.zip ys).foldlM (fun e (a, b) => matchTerm binders a b e) env
  | .indexedApp i k xs, .indexedApp j l ys =>
    if i != j || k != l || xs.length != ys.length then none else
      (xs.zip ys).foldlM (fun e (a, b) => matchTerm binders a b e) env
  | .code L a xs, .code M b ys =>
    if L != M || a != b || xs.length != ys.length then none else
      (xs.zip ys).foldlM (fun e (a, b) => matchTerm binders a b e) env
  | _, _ => none

private def unbind : FormulaView → List Name × FormulaView
  | .all x a => let (xs, b) := unbind a; (x :: xs, b)
  | a => ([], a)

private def rewriteRoot (rules : List Nat) (t : TermView) : DeriveM (Option Nat) := do
  for rule in rules do
    let (xs, a) := unbind (← conclusion rule)
    if let .equal lhs rhs := a then
      if let some env := matchTerm xs lhs t [] then
        if xs.all (fun x => (env.lookup x).isSome) then
          let result := xs.foldl (fun r x => r.replace x (env.lookup x).get!) rhs
          if t != result then
            let mut proof := rule
            for x in xs do proof ← instantiate proof (env.lookup x).get!
            return some proof
  return none

private partial def rewriteTerm (rules : List Nat) (t : TermView) (fuel? : Option Nat := none) :
    DeriveM Nat := do
  let fuel ← match fuel? with | some fuel => pure fuel | none => maxSteps
  if fuel == 0 then throwError "first-order rewriting exceeded its step limit"
  let initial ← match t with
    | .app i args => eqCongr i (← args.mapM (fun a => rewriteTerm rules a (some (fuel - 1))))
    | .indexedApp i k args =>
      eqCongr i (← args.mapM (fun a => rewriteTerm rules a (some (fuel - 1)))) (some k)
    | _ => eqRefl t
  let .equal _ u ← conclusion initial | throwError "invalid rewrite result"
  if let some step ← rewriteRoot rules u then
    let .equal _ v ← conclusion step | throwError "invalid rewrite result"
    return ← eqTrans initial (← eqTrans step (← rewriteTerm rules v (some (fuel - 1))))
  return initial

private def rewriteSides (goal : FormulaView) (rules : List Nat) : DeriveM (Nat × Nat) := do
  let .equal a b := goal | throwError "prw currently closes equality goals"
  let universals ← rules.filterM fun p => do
    return match ← conclusion p with | .all _ _ => true | _ => false
  let mut normalized := []
  for rule in rules do
    if let .equal lhs rhs ← conclusion rule then
      let earlier := universals ++ normalized
      let p ← rewriteTerm earlier lhs
      let q ← rewriteTerm earlier rhs
      normalized := normalized ++ [← eqTrans (← eqSymm p) (← eqTrans rule q)]
  let rules := normalized ++ rules
  let p ← rewriteTerm rules a
  let q ← rewriteTerm rules b
  return (p, q)

/-! ## Rewriting inside formulas

A term `s` is rewritten to `u` by abstracting its occurrences as a fresh variable and using
`formulaTransport` along `u = s`, which proves the goal from its rewritten form. An
equivalence `A ↔ B` is carried through implications and quantifiers by deduction. -/

private partial def replaceTerm (target replacement : TermView) : TermView → TermView
  | t => if t == target then replacement else match t with
    | .app i args => .app i (args.map (replaceTerm target replacement))
    | .indexedApp i k args => .indexedApp i k (args.map (replaceTerm target replacement))
    | .code L value args => .code L value (args.map (replaceTerm target replacement))
    | t => t

/-- Replace the term `target`, including in the explicit arguments of closed definitions. Binder
names are fresh, so a binder named like a variable of the term binds that very variable. -/
private partial def replaceTermInFormula (target replacement : TermView) :
    FormulaView → FormulaView
  | .equal a b => .equal (replaceTerm target replacement a) (replaceTerm target replacement b)
  | .relation i args => .relation i (args.map (replaceTerm target replacement))
  | .indexedRelation i k args => .indexedRelation i k (args.map (replaceTerm target replacement))
  | .imp a b =>
    .imp (replaceTermInFormula target replacement a) (replaceTermInFormula target replacement b)
  | .all x a => .all x (replaceTermInFormula target replacement a)
  | .code L value args => .code L value (args.map (replaceTerm target replacement))
  | a => a

/-- Replace every subformula equivalent to `target`. -/
private partial def replaceFormula (target replacement : FormulaView) : FormulaView → FormulaView
  | a => if a.equiv target then replacement else match a with
    | .imp b c => .imp (replaceFormula target replacement b) (replaceFormula target replacement c)
    | .all x b => .all x (replaceFormula target replacement b)
    | a => a

/-- A term of the formula that a rule rewrites, with the rewritten term and the proof of the
equation. The explicit arguments of closed definitions are searched as well. -/
private partial def findTermRewrite (rules : List Nat) :
    FormulaView → DeriveM (Option (TermView × TermView × Nat))
  | .equal a b => do
    if let some found ← findInTerm a then return some found
    findInTerm b
  | .relation _ args | .indexedRelation _ _ args => do
    for arg in args do
      if let some found ← findInTerm arg then return some found
    return none
  | .imp a b => do
    if let some found ← findTermRewrite rules a then return some found
    findTermRewrite rules b
  | .all _ a => findTermRewrite rules a
  | .code _ _ args => do
    -- The explicit arguments of a closed definition are open to rewriting.
    for arg in args do
      if let some found ← findInTerm arg then return some found
    return none
  | _ => return none
where
  findInTerm (t : TermView) : DeriveM (Option (TermView × TermView × Nat)) := do
    if let some step ← rewriteRoot rules t then
      let .equal _ u ← conclusion step | throwError "invalid rewrite result"
      return some (t, u, step)
    match t with
    | .app _ args | .indexedApp _ _ args | .code _ _ args =>
      for arg in args do
        if let some found ← findInTerm arg then return some found
      return none
    | _ => return none

private partial def matchFormula (binders : List Name) (pattern target : FormulaView)
    (env : List (Name × TermView)) : Option (List (Name × TermView)) :=
  match pattern, target with
  | .falsum, .falsum => some env
  | .equal a b, .equal c d => do matchTerm binders b d (← matchTerm binders a c env)
  | .relation i xs, .relation j ys =>
    if i != j || xs.length != ys.length then none else
      (xs.zip ys).foldlM (fun e (a, b) => matchTerm binders a b e) env
  | .indexedRelation i k xs, .indexedRelation j l ys =>
    if i != j || k != l || xs.length != ys.length then none else
      (xs.zip ys).foldlM (fun e (a, b) => matchTerm binders a b e) env
  | .code L a xs, .code M b ys =>
    if L != M || a != b || xs.length != ys.length then none else
      (xs.zip ys).foldlM (fun e (a, b) => matchTerm binders a b e) env
  | .imp a b, .imp c d => do matchFormula binders b d (← matchFormula binders a c env)
  | .all x a, .all y b => matchFormula binders a (b.replace y (.var x)) env
  | _, _ => none

/-- An equivalence rule instantiated so that its left side is `a`. -/
private def equivalenceAt (rules : List Nat) (a : FormulaView) : DeriveM (Option Nat) := do
  for rule in rules do
    let (xs, c) := unbind (← conclusion rule)
    if let .imp (.imp (.imp lhs rhs) (.imp (.imp rhs' lhs') .falsum)) .falsum := c then
      unless rhs.equiv rhs' && lhs.equiv lhs' do continue
      if let some env := matchFormula xs lhs a [] then
        if xs.all (fun x => (env.lookup x).isSome) then
          let mut proof := rule
          for x in xs do proof ← instantiate proof (env.lookup x).get!
          return some proof
  return none

/-- A subformula that an equivalence rule rewrites, with the rewritten formula and the proof
of the equivalence. -/
private partial def findFormulaRewrite (rules : List Nat) (a : FormulaView) :
    DeriveM (Option (FormulaView × FormulaView × Nat)) := do
  if let some step ← equivalenceAt rules a then
    let .imp (.imp (.imp _ b) _) _ ← conclusion step | throwError "invalid rewrite result"
    return some (a, b, step)
  match a with
  | .imp b c =>
    if let some found ← findFormulaRewrite rules b then return some found
    findFormulaRewrite rules c
  | .all _ b => findFormulaRewrite rules b
  | _ => return none

/-- From a proof of `a` with the subformula `source` replaced by `target` (when `forward` is
false), or from a proof of `a` (when `forward` is true), prove the other formula, using the
equivalence `source ↔ target` at each occurrence. -/
private partial def equivalenceTransport (source target : FormulaView) (equivalence : Nat)
    (forward : Bool) (a : FormulaView) (q : Nat) : DeriveM Nat := do
  if a.equiv source then
    return ← mp (← if forward then conjunctionLeft equivalence else conjunctionRight equivalence) q
  let replaced := replaceFormula source target
  match a with
  | .imp b c =>
    let premise := if forward then replaced b else b
    let h ← liftCoreM (mkFreshUserName `h)
    let hb ← addNode premise (.hypothesis h)
    let inner ← equivalenceTransport source target equivalence (!forward) b hb
    let result ← equivalenceTransport source target equivalence forward c (← mp q inner)
    deduct h premise result
  | .all y b =>
    generalize y (← equivalenceTransport source target equivalence forward b
      (← instantiate q (.var y)))
  | _ => return q

/-- How a rewrite was found: a term `s` rewritten to `u` by the equation `step`, with the
formula abstracted at the hole `x`, or a subformula rewritten with the proof back to the
original formula. -/
private inductive Found where
  | term (x : Name) (s u : TermView) (step : Nat) (abstracted : FormulaView)
  | formula (back : Nat)

/-- The instance of `Equality.substitution_congruence` stating that `s = u` makes the formula
`abstracted`, with `x` as the substituted position, equivalent at `s` and at `u`. It carries a
term rewrite through every position of a formula, including the arguments of closed
definitions. -/
private def congruenceInstance (g : ProofGoal) (x : Name) (s u : TermView)
    (abstracted : FormulaView) : TacticM (DeriveM Nat) := do
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  let arguments := [L, T, ← s.encode L [] g.free, ← u.encode L [] g.free,
    ← abstracted.encode L [x] g.free]
  let congruence := `FOL.Equality.substitution_congruence
  let some (.theoremE declaration) := (← getGoal).environment.lookup congruence |
    throwError "unknown theorem {congruence}"
  proofRule g (.theoremE congruence arguments []) (declaration.type.instantiate arguments [])

/-- Rewrite the conclusion of a goal with one rule: every occurrence of the first term that
the rule matches, when the rule is an equation, or every subformula that the rule matches,
when it is an equivalence. The conclusion is the goal after its leading hypotheses; when the
rule matches nothing there, the whole goal is tried, since a negation `¬ A` is the implication
`A → ⊥` and would otherwise leave only `⊥` to rewrite. Returns whether the rule applied. -/
private def rewriteFormulaGoal (g : ProofGoal) (rule : DeriveM Nat) : TacticM Bool := do
  let (hypotheses, target) := assumptions g.formula
  let (found, graph) ← (do
    if let some result ← rewriteIn target then return some result
    if hypotheses.isEmpty then return none
    rewriteIn g.formula).run {}
  let some (rewritten, how, whole) := found | return false
  let hypotheses := if whole then [] else hypotheses
  -- A term rewrite states the rewritten formula as the congruence theorem does, which can
  -- number the arguments of a closed definition differently from a direct replacement.
  let (back, rewritten, graph) ← match how with
    | .formula back => pure (back, rewritten, graph)
    | .term x s u step abstracted => do
      let transport ← congruenceInstance g x s u abstracted
      let (back, graph) ← (do conjunctionRight (← mp (← transport) step)).run graph
      let .imp rewritten _ := graph.nodes[back]!.formula |
        throwError "invalid rewrite result"
      pure (back, rewritten, graph)
  refineDerivation g do
    set graph
    let next := hypotheses.foldr (fun (_, h) body => .imp h body) rewritten
    return ([next], fun ps => do
      let mut middle := ps[0]!
      for (name, h) in hypotheses do
        middle ← mp middle (← addNode h (.hypothesis name))
      discharge hypotheses (← mp back middle))
  return true
where
  /-- The rewritten formula and how it was found, with whether the whole goal was rewritten. -/
  rewriteIn (target : FormulaView) : DeriveM (Option (FormulaView × Found × Bool)) := do
    let rules := [← rule]
    let whole := target == g.formula
    if let some (s, u, step) ← findTermRewrite rules target then
      let x ← liftCoreM (mkFreshUserName `_folHole)
      let abstracted := replaceTermInFormula s (.var x) target
      return some (abstracted.replace x u, .term x s u step abstracted, whole)
    if let some (a, b, step) ← findFormulaRewrite rules target then
      let rewritten := replaceFormula a b target
      let h ← liftCoreM (mkFreshUserName `h)
      let hr ← addNode rewritten (.hypothesis h)
      let back ← deduct h rewritten (← equivalenceTransport a b step false target hr)
      return some (rewritten, .formula back, whole)
    return none

/-- Rewrite the assumption at position `index` of the goal's list with one rule, as
`rewriteFormulaGoal` rewrites a goal: every occurrence of the first term that an equation
matches, or every subformula that an equivalence matches. The assumption keeps its name and
position. Returns whether the rule applied. -/
private def rewriteAssumption (g : ProofGoal) (index : Nat) (rule : DeriveM Nat) :
    TacticM Bool := do
  let some (_, a) := g.context.entries[index]? | throwError "unknown object assumption"
  let hypothesis ← assumptionStep g index
  let (found, graph) ← (do
    let rules := [← rule]
    if let some (s, u, step) ← findTermRewrite rules a then
      let x ← liftCoreM (mkFreshUserName `_folHole)
      return some (Sum.inl (x, s, u, step, replaceTermInFormula s (.var x) a))
    if let some (source, target, step) ← findFormulaRewrite rules a then
      return some (.inr (← equivalenceTransport source target step true a (← hypothesis)))
    return none).run {}
  let some found := found | return false
  let step : DeriveM Nat ← match found with
    | .inr p => pure (do set graph; pure p)
    | .inl (x, s, u, step, abstracted) => do
      -- The congruence theorem states the rewritten assumption, as for a goal.
      let transport ← congruenceInstance g x s u abstracted
      let (forward, graph) ← (do conjunctionLeft (← mp (← transport) step)).run graph
      let .imp source _ := graph.nodes[forward]!.formula | throwError "invalid rewrite result"
      let some hypothesis ← convertStep g hypothesis source | throwError "invalid rewrite result"
      pure (do set graph; mp forward (← hypothesis))
  let (root, graph) ← step.run {}
  replaceAssumption g index graph.nodes[root]!.formula step
  return true

/-- The rule read in the other direction: an equation by symmetry, an equivalence by
exchanging its two implications, beneath any leading universal quantifiers. -/
private partial def reversed (p : Nat) : DeriveM Nat := do
  match ← conclusion p with
  | .all x _ => generalize x (← reversed (← instantiate p (.var x)))
  | .equal _ _ => eqSymm p
  | .imp (.imp (.imp _ _) (.imp (.imp _ _) .falsum)) .falsum =>
    conjunctionIntro (← conjunctionRight p) (← conjunctionLeft p)
  | _ => throwError "a reversed rule must be an equation or an equivalence"

/-- Resolve a rewrite rule, reversing it after `←`. -/
private def rewriteRule (g : ProofGoal) (r : TSyntax ``folRewriteRule) :
    TacticM (DeriveM Nat) := do
  let step ← rule g ⟨r.raw[1]⟩
  if r.raw[0].getNumArgs == 0 then return step
  return do reversed (← step)

private def rewriteEquations (equations : Array (TSyntax ``folRewriteRule)) : TacticM Unit := do
  let g ← currentGoal
  let isEquation (a : FormulaView) := match (unbind a).2 with
    | .equal _ _ => true
    | _ => false
  unless (match (assumptions g.formula).2 with | .equal _ _ => true | _ => false) do
    -- Each rule rewrites the goal once, in the order written.
    let rules ← equations.toList.mapM fun r => do exposeStep g (← rewriteRule g r) isEquation
    for (r, step) in equations.toList.zip rules do
      unless ← rewriteFormulaGoal (← currentGoal) step do
        throwErrorAt r "the rule does not apply to the goal"
    return
  let g ← currentGoalAs fun a => match (assumptions a).2 with
    | .equal _ _ => true
    | _ => false
  let (hypotheses, target) := assumptions g.formula
  let rules ← equations.toList.mapM fun r => do exposeStep g (← rewriteRule g r) isEquation
  refineDerivation g do
    let (p, q) ← rewriteSides target (← rules.mapM id)
    let .equal _ a ← conclusion p | throwError "invalid rewrite result"
    let .equal _ b ← conclusion q | throwError "invalid rewrite result"
    let next := hypotheses.foldr (fun (_, h) body => .imp h body) (.equal a b)
    return ([next], fun ps => do
      let mut middle := ps[0]!
      for (name, h) in hypotheses do
        middle ← mp middle (← addNode h (.hypothesis name))
      discharge hypotheses (← eqTrans p (← eqTrans middle (← eqSymm q))))
  -- When the sides still differ, each rule is also carried into the arguments of closed
  -- definitions, as often as it applies.
  let g ← currentGoal
  if let .equal a b := (assumptions g.formula).2 then
    if a != b then
      for step in rules do
        for _ in [:← maxSteps] do
          let before ← currentGoal
          unless ← rewriteFormulaGoal before step do break
          if (← currentGoal).formula.equiv before.formula then break

private def closeEquation : TacticM Unit := do
  let g ← currentGoal
  let (hypotheses, target) := assumptions g.formula
  let .equal a b := target | throwError "prw currently closes equality goals"
  unless a == b do
    -- The two sides may agree once definitions are opened where they differ.
    let some step ← convertStep g (eqRefl a) target |
      throwError "prw did not close the equation"
    finish g do discharge hypotheses (← step)
    return
  finish g do discharge hypotheses (← eqRefl a)

/-- Elaborate the equality tactics through checked PRA proof data. -/
@[pra_tactic preflTac, pra_tactic prwTac, pra_tactic ptransTac, pra_tactic psymmTac,
  pra_tactic pcongrTac]
def evalRewriteTactic : Tactic := closedFirst fun stx => do
  match stx with
  | `(praTactic| prefl) =>
    let g ← currentGoalAs fun a => match (assumptions a).2 with
      | .equal _ _ => true
      | _ => false
    let (hypotheses, target) := assumptions g.formula
    let .equal a b := target | throwError "prefl expects an equation"
    unless a == b do throwError "prefl expects both sides to be the same term"
    finish g do discharge hypotheses (← eqRefl a)
  | `(praTactic| ptrans $term:folTerm) =>
    let g ← currentGoalAs fun | .equal _ _ => true | _ => false
    let .equal a b := g.formula | throwError "ptrans expects an equation"
    let t ← termArgument g term
    refineDerivation g do
      return ([.equal a t, .equal t b], fun ps => eqTrans ps[0]! ps[1]!)
  | `(praTactic| psymm) =>
    let g ← currentGoalAs fun | .equal _ _ => true | _ => false
    let .equal a b := g.formula | throwError "psymm expects an equation"
    refineDerivation g do
      return ([.equal b a], fun ps => eqSymm ps[0]!)
  | `(praTactic| pcongr) =>
    let g ← currentGoalAs fun | .equal _ _ => true | _ => false
    let (i, member, xs, ys) ← match g.formula with
      | .equal (.app i xs) (.app j ys) =>
        unless i == j do throwError "function symbols differ"
        pure (i, none, xs, ys)
      | .equal (.indexedApp i k xs) (.indexedApp j l ys) =>
        unless i == j && k == l do throwError "function symbols differ"
        pure (i, some k, xs, ys)
      | _ => throwError "pcongr expects applications of the same function"
    unless xs.length == ys.length do throwError "function arities differ"
    refineDerivation g do
      return ((xs.zip ys).map (fun (a, b) => .equal a b), fun ps => eqCongr i ps member)
  | `(praTactic| prw $[[$rules:folRewriteRule,*]]? $[at $location:ident]?) =>
    let some rules := rules | do
      if let some h := location then
        throwErrorAt h "prw at an assumption needs a definition to open"
      closeEquation
    let elems := rules.getElems
    withTacticInfo (mkNullNode #[stx[0], stx[1][0]]) (pure ())
    let mut opened := false
    let mut equations := #[]
    for i in [:elems.size] do
      let r := elems[i]!
      let sep := rules.elemsAndSeps.getD (2 * i + 1) .missing
      let isDefinition ← withTacticInfo (mkNullNode #[r.raw, sep]) <| withRef r do
        let g ← currentGoal
        if let `(folRewriteRule| $id:ident) := r then
          let name := id.getId.eraseMacroScopes
          unless g.context.entries.any (·.1 == name) ||
              (← getGoal).names.used.contains name do
            if let some d ← findDefinition name then
              openNamed [d.name] location
              return true
        if let some h := location then
          let name := h.getId.eraseMacroScopes
          let some index := g.context.entries.findIdx? (·.1 == name) |
            throwErrorAt h "unknown object assumption `{name}`"
          let step ← exposeStep g (← rewriteRule g r) fun a => match (unbind a).2 with
            | .equal _ _ => true
            | _ => false
          unless ← rewriteAssumption g index step do
            throwErrorAt r "the rule does not apply to the assumption"
          return false
        rewriteEquations (equations.push r)
        return false
      if isDefinition then opened := true else equations := equations.push r
    withTacticInfo stx[1][2] <| withRef stx[1][2] do
      if location.isNone && (!opened || !equations.isEmpty) then
        let g ← currentGoal
        if let .equal _ _ := (assumptions g.formula).2 then closeEquation
  | _ => throwUnsupportedSyntax

end LeanPRA.Library.FOL.DSL
