module

public meta import LeanPRA.Library.FOL.DSL.Tactic.Context

/-!
# Equality tactics for FOL proofs

`evalRewriteTactic` implements `prefl`, `prw`, `ptrans`, `psymm`, and `pcongr`.
`prefl` closes an equation whose sides are the same term. Rewriting constructs
equality derivations from named rules and closes the resulting PRA provability goal. A rule of
`prw` that names a definition opens that definition in the goal, or in the assumption named
after `at`, and leaves the resulting goal.
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

private partial def rewriteTerm (rules : List Nat) (t : TermView) (fuel : Nat := 100) :
    DeriveM Nat := do
  if fuel == 0 then throwError "first-order rewriting exceeded its step limit"
  let initial ← match t with
    | .app i args => eqCongr i (← args.mapM (fun a => rewriteTerm rules a (fuel - 1)))
    | .indexedApp i k args =>
      eqCongr i (← args.mapM (fun a => rewriteTerm rules a (fuel - 1))) (some k)
    | _ => eqRefl t
  let .equal _ u ← conclusion initial | throwError "invalid rewrite result"
  if let some step ← rewriteRoot rules u then
    let .equal _ v ← conclusion step | throwError "invalid rewrite result"
    return ← eqTrans initial (← eqTrans step (← rewriteTerm rules v (fuel - 1)))
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

private def rewriteEquations (equations : Array (TSyntax `praExpr)) : TacticM Unit := do
  let g ← currentGoalAs fun a => match (assumptions a).2 with
    | .equal _ _ => true
    | _ => false
  let (hypotheses, target) := assumptions g.formula
  let isEquation (a : FormulaView) := match (unbind a).2 with
    | .equal _ _ => true
    | _ => false
  let rules ← equations.toList.mapM fun r => do exposeStep g (← rule g r) isEquation
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

private def closeEquation : TacticM Unit := do
  let g ← currentGoal
  let (hypotheses, target) := assumptions g.formula
  let .equal a b := target | throwError "prw currently closes equality goals"
  unless a == b do throwError "prw did not close the equation"
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
  | `(praTactic| prw $[[$rules:praExpr,*]]? $[at $location:ident]?) =>
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
        if let `(praExpr| $id:ident) := r then
          let name := id.getId.eraseMacroScopes
          unless g.context.entries.any (·.1 == name) ||
              (← getGoal).names.used.contains name do
            if let some d ← findDefinition name then
              unless d.isFormula do
                throwErrorAt id "the term definition `{name}` is always written out in a formula"
              openNamed [d.name] location
              return true
        if let some h := location then
          throwErrorAt h "prw changes an assumption only by opening definitions"
        rewriteEquations (equations.push r)
        return false
      if isDefinition then opened := true else equations := equations.push r
    withTacticInfo stx[1][2] <| withRef stx[1][2] do
      if let some h := location then
        unless opened do throwErrorAt h "prw at an assumption needs a definition to open"
      else if !opened || !equations.isEmpty then
        closeEquation
  | _ => throwUnsupportedSyntax

end LeanPRA.Library.FOL.DSL
