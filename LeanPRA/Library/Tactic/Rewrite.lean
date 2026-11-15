module

public meta import LeanPRA.Library.Tactic.Logic

/-!
# Equality rewriting in PRA proofs

`rw [h₁, ← h₂]` rewrites the goal using numerical equalities, then tries beta-only reflexivity.
Universally quantified rules are instantiated from the first matching numerical subterm.
Equality-rule matching contracts lambda applications and ignores binder names. Definitions, lets,
recursor equations, and eta expansion keep their explicit form during matching. Each rule replaces
all occurrences of that instance, including occurrences beneath binders.
An instance must be expressible in the current goal context; introduce a bound variable before
using a rule whose instance depends on it. `rw [h] at hp` replaces `hp` with its rewritten
version, preserving its name and position in the context.

A definition name in `rw [f]` unfolds the first matching application and its other occurrences.
Function and predicate parameters come from that application. Lambda applications and exposed head
lets are reduced; other definitions and primitive recursion expressions stay available for later
rules. Local names take precedence over global definitions. Definition unfolding proceeds forward;
use an equality lemma for reverse rewriting.

- `rewrite` constructs a unary predicate describing the replaced occurrences and refines the
  goal with equality substitution.
- `evalRewrite` implements the syntax, rule ordering, and final reflexivity attempt.

Matching and motive construction operate on PRA expressions. The resulting proof uses checked
equality substitution and the PRA library's symmetry theorem. Definition unfolding changes the
proof's expected type through the core checker's definitional equality.
-/

public meta section

namespace LeanPRA.Library.Tactic

open Lean Elab LeanPRA.Surface LeanPRA.Surface.Tactic

open Metavariable hiding Term

declare_syntax_cat praRewriteRule

syntax praExpr : praRewriteRule
syntax "← " praExpr : praRewriteRule
syntax (name := rwTac) "rw" " [" praRewriteRule,+ "]" (" at " ident)? : praTactic

private def matchingTerm : Metavariable.Term → Metavariable.Term
  | .lam _ body => .lam .anonymous (matchingTerm body)
  | .app f a => .app (matchingTerm f) (matchingTerm a)
  | .letE _ a b => .letE .anonymous (matchingTerm a) (matchingTerm b)
  | .primrec b s => .primrec (matchingTerm b) (matchingTerm s)
  | .definition n fs => .definition n (fs.map matchingTerm)
  | t => t

private def betaEqual (goal : Goal) (a b : Metavariable.Term) : Bool :=
  matchingTerm (Bridge.betaReduceTerm goal.projection goal.maxDepth a) ==
    matchingTerm (Bridge.betaReduceTerm goal.projection goal.maxDepth b)

-- Two applications with distinct rigid heads cannot become equal by beta reduction alone.
-- Terms headed by lambdas, lets, recursors, or metavariables return `none` and stay as candidates.
private def fixedHead : Metavariable.Term → Option Metavariable.Term
  | .app f _ => fixedHead f
  | .definition n _ => some (.definition n [])
  | .parameter i => some (.parameter i)
  | .zero => some .zero
  | .succ => some .succ
  | _ => none

private def compatibleHeads (pattern candidate : Metavariable.Term) : Bool :=
  match fixedHead (matchingTerm pattern), fixedHead (matchingTerm candidate) with
  | some a, some b => a == b
  | _, _ => true

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
  | .primrec b s => termCandidates depth b ++ termCandidates depth s
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
  | .primrec b s => .primrec (abstractTerm source depth b) (abstractTerm source depth s)
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
  let .equal patternLeft patternRight :=
      Bridge.betaReducePredicate goal.projection goal.maxDepth type
    | throwError "rw expects a numerical equality"
  let pattern := if reverse then patternRight else patternLeft
  restoreInspection
  for candidate in (predicateCandidates 0 target).eraseDups do
    unless compatibleHeads pattern candidate do continue
    -- A rule without quantified binders or metavariables must already beta-match the candidate.
    if count == 0 && pattern.isComplete && candidate.isComplete then
      unless betaEqual goal pattern candidate do continue
    let .ok 0 := Bridge.termType goal.projection goal.maxDepth goal.environment goal.context
        candidate
      | continue
    let restore ← saveState
    try
      let other ← Tactic.unknownTerm
      let (proof, instanceType) ← Tactic.elaborateProofAs equation
        (if reverse then .equal other candidate else .equal candidate other)
      let instanceType := Bridge.betaReducePredicate goal.projection goal.maxDepth instanceType
      let .equal a b := instanceType
        | throwError "rw expects a numerical equality"
      let (source, destination) := if reverse then (b, a) else (a, b)
      unless source.isComplete && destination.isComplete do
        throwError "rw could not infer the rule's arguments"
      unless betaEqual goal source candidate do
        throwError "rw occurrence does not match by beta reduction"
      let body := abstractPredicate candidate 0 target
      if body == target.shift then throwError "rw found no occurrence"
      let motive : Predicate := .lam (goal.names.freshName "rw") body
      let symmetry (x y : Metavariable.Term) (p : Metavariable.Proof) : Metavariable.Proof :=
        .impElim (.forallElim (.forallElim (.theoremE `eq_symm [] []) x) y) p
      -- `transport x y p` carries the motive from `x` to `y` along `p : x = y`.
      let transport (x y : Metavariable.Term) (p : Metavariable.Proof) : Metavariable.Proof :=
        .impElim (.forallElim (.forallElim (.eqSubst motive) x) y) p
      let equality := if reverse then symmetry a b proof else proof
      let result := Bridge.betaReducePredicate goal.projection goal.maxDepth
        (.app motive destination)
      match location with
      | none =>
        Tactic.applyProof (transport destination source (symmetry source destination equality))
          [result]
      | some h =>
        let (hypothesis, _) ← Tactic.elaborateProof (← `(praExpr| $h:ident))
        let .hyp index := hypothesis | throwErrorAt h "expected a local proof hypothesis"
        Tactic.replaceHypothesis index result
          (.impElim (transport source destination equality) hypothesis) h
      return
    catch ex =>
      if ex.isInterrupt then throw ex
      restore
  throwError "rw found no matching occurrence; supply explicit rule arguments if needed"

private def matchingPredicate : Predicate → Predicate
  | .equal a b => .equal (matchingTerm a) (matchingTerm b)
  | .imp a b => .imp (matchingPredicate a) (matchingPredicate b)
  | .and a b => .and (matchingPredicate a) (matchingPredicate b)
  | .or a b => .or (matchingPredicate a) (matchingPredicate b)
  | .all p => .all (matchingPredicate p)
  | .ex p => .ex (matchingPredicate p)
  | .lam _ p => .lam .anonymous (matchingPredicate p)
  | .app p a => .app (matchingPredicate p) (matchingTerm a)
  | .letTerm _ a p => .letTerm .anonymous (matchingTerm a) (matchingPredicate p)
  | .letPredicate _ p q => .letPredicate .anonymous (matchingPredicate p) (matchingPredicate q)
  | .definition n fs ps => .definition n (fs.map matchingTerm) (ps.map matchingPredicate)
  | p => p

private def predicateHead : Predicate → Option Name
  | .definition n _ _ => some n
  | .app p _ => predicateHead p
  | _ => none

-- Contract the lambda applications and head lets exposed by unfolding, leaving other definitions
-- and primitive recursion expressions available for subsequent rewrite rules.
private def reduceUnfoldedTerm (goal : Goal) : Nat → Metavariable.Term → Metavariable.Term
  | 0, t => t
  | fuel + 1, t =>
    let t := Bridge.betaReduceTerm goal.projection goal.maxDepth t
    match t with
    | .letE _ value body => reduceUnfoldedTerm goal fuel (body.subst0 value)
    | _ => t

private def reduceUnfoldedPredicate (goal : Goal) : Nat → Predicate → Predicate
  | 0, p => p
  | fuel + 1, p =>
    let p := Bridge.betaReducePredicate goal.projection goal.maxDepth p
    match p with
    | .letTerm _ _ body | .letPredicate _ _ body => reduceUnfoldedPredicate goal fuel body
    | _ => p

private inductive UnfoldOccurrence where
  | term (depth : Nat) (value : Metavariable.Term)
  | predicate (depth : Nat) (value : Predicate)

private abbrev UnfoldM := StateT (Option UnfoldOccurrence) TacticM

private def selectUnfoldTerm (depth : Nat) (t : Metavariable.Term) : UnfoldM Bool := do
  match (← get : Option UnfoldOccurrence) with
  | none => set (some (UnfoldOccurrence.term depth t)); return true
  | some (.term savedDepth source) =>
    return matchingTerm (source.shift (depth - savedDepth)) ==
      matchingTerm (t.shift (savedDepth - depth))
  | _ => return false

private def selectUnfoldPredicate (depth : Nat) (p : Predicate) : UnfoldM Bool := do
  match (← get : Option UnfoldOccurrence) with
  | none => set (some (UnfoldOccurrence.predicate depth p)); return true
  | some (.predicate savedDepth source) =>
    return matchingPredicate (source.shift (depth - savedDepth)) ==
      matchingPredicate (p.shift (savedDepth - depth))
  | _ => return false

private partial def unfoldTermOccurrences (goal : Goal) (name : Name) (depth : Nat)
    (t : Metavariable.Term) : UnfoldM Metavariable.Term := do
  if fixedHead t == some (.definition name []) then
    if ← selectUnfoldTerm depth t then
      let .ok body := Bridge.exposeTerm goal.projection goal.maxDepth goal.environment t
        | throwError "rw could not unfold definition `{name}`"
      return reduceUnfoldedTerm goal goal.maxDepth body
  let visit := unfoldTermOccurrences goal name depth
  match t with
  | .lam n body => return .lam n (← unfoldTermOccurrences goal name (depth + 1) body)
  | .app f a => return .app (← visit f) (← visit a)
  | .letE n a b =>
    return .letE n (← visit a) (← unfoldTermOccurrences goal name (depth + 1) b)
  | .primrec b s => return .primrec (← visit b) (← visit s)
  | .definition n fs => return .definition n (← fs.mapM visit)
  | t => return t

private partial def unfoldPredicateOccurrences (goal : Goal) (name : Name) (depth : Nat)
    (p : Predicate) : UnfoldM Predicate := do
  if predicateHead p == some name then
    if ← selectUnfoldPredicate depth p then
      let .ok body := Bridge.exposePredicate goal.projection goal.maxDepth goal.environment p
        | throwError "rw could not unfold definition `{name}`"
      return reduceUnfoldedPredicate goal goal.maxDepth body
  let term := unfoldTermOccurrences goal name depth
  let visit := unfoldPredicateOccurrences goal name depth
  match p with
  | .equal a b => return .equal (← term a) (← term b)
  | .imp a b => return .imp (← visit a) (← visit b)
  | .and a b => return .and (← visit a) (← visit b)
  | .or a b => return .or (← visit a) (← visit b)
  | .all p => return .all (← visit p)
  | .ex p => return .ex (← visit p)
  | .lam n p => return .lam n (← unfoldPredicateOccurrences goal name (depth + 1) p)
  | .app p a => return .app (← visit p) (← term a)
  | .letTerm n a p => return .letTerm n (← term a) (← visit p)
  | .letPredicate n p q => return .letPredicate n (← visit p) (← visit q)
  | .definition n fs ps => return .definition n (← fs.mapM term) (← ps.mapM visit)
  | p => return p

private def unfoldDefinition (decl : Core.Declaration) (location : Option (TSyntax `ident)) :
    TacticM Unit := do
  let goal ← getGoal
  let target ← match location with
    | none => pure goal.target
    | some h => infer (← `(praExpr| $h:ident))
  let target := Bridge.betaReducePredicate goal.projection goal.maxDepth target
  let (unfolded, occurrence) ← (unfoldPredicateOccurrences goal decl.name 0 target).run none
  if occurrence.isNone then
    throwError "rw found no matching occurrence of definition `{decl.name}`"
  match location with
  | none => Tactic.change unfolded
  | some h =>
    let (proof, _) ← Tactic.elaborateProof (← `(praExpr| $h:ident))
    let .hyp index := proof | throwErrorAt h "expected a local proof hypothesis"
    Tactic.replaceHypothesis index unfolded proof h

private def rewriteRule (rule : TSyntax `praExpr) (reverse : Bool)
    (location : Option (TSyntax `ident)) : TacticM Unit := do
  let id? := match rule with
    | `(praExpr| $id:ident) | `(praExpr| @$id:ident) => some id
    | _ => none
  if let some id := id? then
    let goal ← getGoal
    unless goal.names.used.contains id.getId do
      if let some decl ← resolveDeclaration? goal.environment id.getId then
        match decl with
        | .function _ | .predicate _ =>
          if reverse then
            throwError "rw cannot unfold a definition backwards; use an equality lemma to fold it"
          addDeclarationInfo id decl
          unfoldDefinition decl location
          return
        | .theoremE _ => pure ()
  rewrite rule reverse location

/-- Apply equality rewrites and definition unfoldings in order, then try beta-only reflexivity. -/
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
      | `(praRewriteRule| ← $p:praExpr) => rewriteRule p true location
      | `(praRewriteRule| $p:praExpr) => rewriteRule p false location
      | _ => throwUnsupportedSyntax
  withTacticInfo stx[3] <| withRef stx[3] do
    if location.isNone then
      let goal ← getGoal
      if let .equal a b := Bridge.betaReducePredicate goal.projection goal.maxDepth goal.target then
        if betaEqual goal a b then discard <| attempt (Tactic.close (.forallElim .eqRefl a))

end LeanPRA.Library.Tactic
