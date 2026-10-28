module

public meta import LeanPRA.Library.Tactic.Logic

/-!
# Equality rewriting in PRA proofs

`rw [h₁, ← h₂]` rewrites the goal using numerical equalities, then tries beta-only reflexivity.
Universally quantified rules are instantiated from the first matching numerical subterm.
Matching contracts lambda applications and ignores binder names. Both representations of builtin
successor use the same matching form. Definitions, lets, recursor equations, and eta expansion keep
their explicit form. Each rule replaces all occurrences of that instance, including occurrences
beneath binders.
An instance must be expressible in the current goal context; introduce a bound variable before
using a rule whose instance depends on it. `rw [h] at hp` adds a rewritten version of `hp`
under the same name.

- `rewrite` constructs a unary predicate describing the replaced occurrences and refines the
  goal with equality substitution.
- `evalRewrite` implements the syntax, rule ordering, and final reflexivity attempt.

Matching and motive construction operate on PRA expressions. The resulting proof uses checked
equality substitution and the PRA library's symmetry theorem.
-/

public meta section
namespace LeanPRA.Library.Tactic
open Lean Elab LeanPRA.Surface LeanPRA.Surface.Tactic
open Metavariable hiding Term

declare_syntax_cat praRewriteRule
syntax praExpr : praRewriteRule
syntax "← " praExpr : praRewriteRule
syntax (name := rwTac) "rw" " [" praRewriteRule,+ "]" (" at " ident)? : praTactic

-- Numerals and builtin proof types use primitive successor; written `S` uses its declaration.
private def matchingTerm : Metavariable.Term → Metavariable.Term
  | .succ => .definition `S []
  | .lam _ body => .lam .anonymous (matchingTerm body)
  | .app f a => .app (matchingTerm f) (matchingTerm a)
  | .letE _ a b => .letE .anonymous (matchingTerm a) (matchingTerm b)
  | .primrec b s n => .primrec (matchingTerm b) (matchingTerm s) (matchingTerm n)
  | .definition n fs => .definition n (fs.map matchingTerm)
  | t => t

private def betaEqual (goal : Goal) (a b : Metavariable.Term) : Bool :=
  matchingTerm (Bridge.betaReduceTerm goal.projection goal.maxDepth a) ==
    matchingTerm (Bridge.betaReduceTerm goal.projection goal.maxDepth b)

private def lowerTerm (count : Nat) (t : Metavariable.Term) : Option Metavariable.Term := do
  let marker := (termMetas t).foldl max 0 + 1
  let result := t.transform (fun depth i =>
    if i < depth then .bvar i
    else if i < depth + count then .mvar marker else .bvar (i - count))
    (fun _ i => .parameter i)
  if (termMetas result).contains marker then none else some result

private def termCandidates (depth : Nat) (t : Metavariable.Term) : List Metavariable.Term :=
  (lowerTerm depth t).toList ++ match t with
  | .lam _ body => termCandidates (depth + 1) body
  | .app f a => termCandidates depth f ++ termCandidates depth a
  | .letE _ a b => termCandidates depth a ++ termCandidates (depth + 1) b
  | .primrec b s n => termCandidates depth b ++ termCandidates depth s ++ termCandidates depth n
  | .definition _ fs => fs.flatMap (termCandidates depth)
  | _ => []

private def predicateCandidates (depth : Nat) : Predicate → List Metavariable.Term
  | .equal a b => termCandidates depth a ++ termCandidates depth b
  | .imp a b | .and a b | .or a b | .letPredicate _ a b =>
    predicateCandidates depth a ++ predicateCandidates depth b
  | .all p | .ex p => predicateCandidates depth p
  | .lam _ p => predicateCandidates (depth + 1) p
  | .app p a | .letTerm _ a p => predicateCandidates depth p ++ termCandidates depth a
  | .definition _ fs ps =>
    fs.flatMap (termCandidates depth) ++ ps.flatMap (predicateCandidates depth)
  | _ => []

private def abstractTerm (source : Metavariable.Term) (depth : Nat)
    (t : Metavariable.Term) : Metavariable.Term :=
  if matchingTerm t == matchingTerm (source.shift depth) then .bvar depth else match t with
  | .bvar i => .bvar (if i < depth then i else i + 1)
  | .lam n b => .lam n (abstractTerm source (depth + 1) b)
  | .app f a => .app (abstractTerm source depth f) (abstractTerm source depth a)
  | .letE n a b => .letE n (abstractTerm source depth a) (abstractTerm source (depth + 1) b)
  | .primrec b s n => .primrec (abstractTerm source depth b) (abstractTerm source depth s)
      (abstractTerm source depth n)
  | .definition n fs => .definition n (fs.map (abstractTerm source depth))
  | other => other

private def abstractPredicate (source : Metavariable.Term) (depth : Nat) : Predicate → Predicate
  | .equal a b => .equal (abstractTerm source depth a) (abstractTerm source depth b)
  | .imp a b => .imp (abstractPredicate source depth a) (abstractPredicate source depth b)
  | .and a b => .and (abstractPredicate source depth a) (abstractPredicate source depth b)
  | .or a b => .or (abstractPredicate source depth a) (abstractPredicate source depth b)
  | .all p => .all (abstractPredicate source depth p)
  | .ex p => .ex (abstractPredicate source depth p)
  | .lam n p => .lam n (abstractPredicate source (depth + 1) p)
  | .app p a => .app (abstractPredicate source depth p) (abstractTerm source depth a)
  | .letTerm n a p => .letTerm n (abstractTerm source depth a) (abstractPredicate source depth p)
  | .letPredicate n a b =>
    .letPredicate n (abstractPredicate source depth a) (abstractPredicate source depth b)
  | .definition n fs ps => .definition n (fs.map (abstractTerm source depth))
      (ps.map (abstractPredicate source depth))
  | other => other

/-- Rewrite the goal or one hypothesis with an equality in the requested direction. -/
def rewrite (rule : TSyntax `praExpr) (reverse : Bool) (location : Option (TSyntax `ident)) :
    TacticM Unit := do
  let goal ← getGoal
  let target ← match location with
    | none => pure goal.target
    | some h => infer (← `(praExpr| $h:ident))
  let target := Bridge.betaReducePredicate goal.projection goal.maxDepth target
  let restoreInspection ← saveState
  let mut equation ← `(praExpr| @($rule))
  let mut type ← infer equation
  let mut count := 0
  repeat
    let .all motive := Bridge.betaReducePredicate goal.projection goal.maxDepth type | break
    count := count + 1
    if count > goal.maxDepth then throwError "rw rule binder limit exhausted"
    type := Bridge.betaReducePredicate goal.projection goal.maxDepth
      (.app motive.shift (.bvar 0))
    equation ← `(praExpr| $equation _)
  let .equal .. := Bridge.betaReducePredicate goal.projection goal.maxDepth type
    | throwError "rw expects a numerical equality"
  restoreInspection
  for candidate in (predicateCandidates 0 target).eraseDups do
    let .ok 0 := Bridge.termType goal.projection goal.maxDepth goal.environment goal.context
        candidate
      | continue
    let restore ← saveState
    try
      let candidateSyntax ← delabTerm goal.names (goal.projection.encodeTerm candidate)
      let expected ← if reverse then `(praExpr| _ = $candidateSyntax)
        else `(praExpr| $candidateSyntax = _)
      let instanceType := Bridge.betaReducePredicate goal.projection goal.maxDepth
        (← infer equation (some expected))
      let .equal a b := instanceType
        | throwError "rw expects a numerical equality"
      let (source, destination) := if reverse then (b, a) else (a, b)
      unless source.isComplete && destination.isComplete do
        throwError "rw could not infer the rule's arguments"
      unless betaEqual goal source candidate do
        throwError "rw occurrence does not match by beta reduction"
      let annotation ← predicateSyntax goal instanceType
      let annotated ← `(praExpr| ($equation : $annotation))
      let body := abstractPredicate candidate 0 target
      if body == target.shift then throwError "rw found no occurrence"
      let name := goal.names.freshName "rw"
      let motive ← predicateSyntax goal (.lam name body)
      let symmetry := mkIdent `_root_.eq_symm
      let equality ← if reverse then `(praExpr| $symmetry:ident $annotated) else pure annotated
      match location with
      | none =>
        Tactic.refine (← `(praExpr| eq_subst $motive ($symmetry:ident $equality) ?_))
      | some h =>
        Tactic.refine (← `(praExpr| let $h:ident := eq_subst $motive $equality $h:ident; ?_))
      return
    catch ex =>
      if ex.isInterrupt then throw ex
      restore
  throwError "rw found no matching occurrence; supply explicit rule arguments if needed"

/-- Apply equality rewrites in order and close the result when its sides agree by beta reduction. -/
@[pra_tactic rwTac]
def evalRewrite : Tactic := fun stx => do
  let `(praTactic| rw [$rules:praRewriteRule,*] $[at $location:ident]?) := stx
    | throwUnsupportedSyntax
  withTacticInfo (mkNullNode #[stx[0], stx[1]]) (pure ())
  let elems := rules.getElems
  for i in [:elems.size] do
    let rule := elems[i]!
    let sep := rules.elemsAndSeps.getD (2 * i + 1) .missing
    -- Include the comma and its trailing whitespace in the preceding rule's goal snapshot.
    withTacticInfo (mkNullNode #[rule.raw, sep]) <| withRef rule do
      match rule with
      | `(praRewriteRule| ← $p:praExpr) => rewrite p true location
      | `(praRewriteRule| $p:praExpr) => rewrite p false location
      | _ => throwUnsupportedSyntax
  withTacticInfo stx[3] <| withRef stx[3] do
    if location.isNone then
      let goal ← getGoal
      if let .equal a b := Bridge.betaReducePredicate goal.projection goal.maxDepth goal.target then
        if betaEqual goal a b then discard <| attempt (Tactic.close (.eqRefl a))

end LeanPRA.Library.Tactic
