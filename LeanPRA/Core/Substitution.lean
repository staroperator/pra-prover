module

public import LeanPRA.Core.Syntax

/-!
# Variable renaming and substitution

Capture-avoiding variable renaming, substitution, and parameter instantiation:

- `Term.rename` and `Predicate.rename` map free variable indices.
- `Term.subst` and `Predicate.subst` replace free variables with terms.
- `Term.instantiate` and `Predicate.instantiate` replace declaration parameters with arguments.

When crossing a binder, replacement terms are shifted so their free variables still refer to the
same outer binders.
-/

@[expose] public section

namespace LeanPRA.Core

/-- Map from local variable indices to replacement indices. -/
abbrev Renaming := Nat → Nat

/-- Map from local variable indices to replacement terms. -/
abbrev Subst := Nat → Term

/-- Lift `rename` across `count` binders. -/
def Renaming.lift (count : Nat) (rename : Renaming) (index : Nat) : Nat :=
  if index < count then index else count + rename (index - count)

/-- Rename free variables in a term. -/
def Term.rename (rename : Renaming) : Term → Term
  | .bvar i => .bvar (rename i)
  | .parameter i => .parameter i
  | .zero => .zero
  | .succ => .succ
  | .lam hint t =>
    .lam hint (t.rename (Renaming.lift
      1 rename))
  | .app f a => .app (f.rename rename) (a.rename rename)
  | .letE hint a t =>
    .letE hint (a.rename rename)
      (t.rename (Renaming.lift 1 rename))
  | .primrec b s => .primrec (b.rename rename) (s.rename rename)
  | .definition name fs => .definition name (fs.map (Term.rename rename))

/-- Add `count` to variable indices at or above `cutoff`. -/
def Term.shift (term : Term) (count : Nat := 1) (cutoff : Nat := 0) : Term :=
  term.rename fun i => if i < cutoff then i else i + count

/-- Lift `subst` across `count` binders, shifting free variables in replacement terms. -/
def Subst.lift (count : Nat) (subst : Subst) (index : Nat) : Term :=
  if index < count then .bvar index else (subst (index - count)).shift count

/-- Substitute terms for free variables in a term. -/
def Term.subst (subst : Subst) : Term → Term
  | .bvar i => subst i
  | .parameter i => .parameter i
  | .zero => .zero
  | .succ => .succ
  | .lam hint t =>
    .lam hint (t.subst (Subst.lift 1
      subst))
  | .app f a => .app (f.subst subst) (a.subst subst)
  | .letE hint a t =>
    .letE hint (a.subst subst)
      (t.subst (Subst.lift 1 subst))
  | .primrec b s => .primrec (b.subst subst) (s.subst subst)
  | .definition name fs => .definition name (fs.map (Term.subst subst))

/-- Substitute `argument` for variable `0` and decrement remaining free variable indices. -/
def Term.subst0 (body argument : Term) : Term :=
  body.subst fun | 0 => argument | i + 1 => .bvar i

/-- Instantiate function parameters with `actuals`, shifting each argument by the binder `depth`.
Out-of-range parameter indices are left unchanged. -/
def Term.instantiate (actuals : List Term) (depth : Nat := 0) : Term → Term
  | .bvar i => .bvar i
  | .parameter i => (actuals[i]?.getD (.parameter i)).shift depth
  | .zero => .zero
  | .succ => .succ
  | .lam hint t =>
    .lam hint (t.instantiate actuals
      (depth + 1))
  | .app f a => .app (f.instantiate actuals depth) (a.instantiate actuals depth)
  | .letE hint a t =>
    .letE hint (a.instantiate actuals depth) (t.instantiate actuals (depth +
        1))
  | .primrec b s => .primrec (b.instantiate actuals depth) (s.instantiate actuals depth)
  | .definition name fs =>
    .definition name (fs.map (Term.instantiate actuals depth))

/-- Rename free variables in a predicate. Only `Predicate.lam` binds a local variable. -/
def Predicate.rename (rename : Renaming) : Predicate → Predicate
  | .false => .false
  | .true => .true
  | .equal a b => .equal (a.rename rename) (b.rename rename)
  | .imp a b => .imp (a.rename rename) (b.rename rename)
  | .and a b => .and (a.rename rename) (b.rename rename)
  | .or a b => .or (a.rename rename) (b.rename rename)
  | .all p => .all (p.rename rename)
  | .ex p => .ex (p.rename rename)
  | .parameter i => .parameter i
  | .lam hint p =>
    .lam hint (p.rename (Renaming.lift
      1 rename))
  | .app p a => .app (p.rename rename) (a.rename rename)
  | .letTerm hint a p =>
    .letTerm hint (a.rename
      rename) (p.rename rename)
  | .letPredicate hint p q =>
    .letPredicate hint
      (p.rename rename) (q.rename rename)
  | .definition name fs ps =>
    .definition name (fs.map (Term.rename rename)) (ps.map (Predicate.rename rename))

/-- Add `count` to variable indices at or above `cutoff` in a predicate. -/
def Predicate.shift (predicate : Predicate) (count : Nat := 1) (cutoff : Nat := 0) : Predicate :=
  predicate.rename fun i => if i < cutoff then i else i + count

/-- Substitute terms for free variables in a predicate. -/
def Predicate.subst (subst : Subst) : Predicate → Predicate
  | .false => .false
  | .true => .true
  | .equal a b => .equal (a.subst subst) (b.subst subst)
  | .imp a b => .imp (a.subst subst) (b.subst subst)
  | .and a b => .and (a.subst subst) (b.subst subst)
  | .or a b => .or (a.subst subst) (b.subst subst)
  | .all p => .all (p.subst subst)
  | .ex p => .ex (p.subst subst)
  | .parameter i => .parameter i
  | .lam hint p =>
    .lam hint (p.subst (Subst.lift 1
      subst))
  | .app p a => .app (p.subst subst) (a.subst subst)
  | .letTerm hint a p =>
    .letTerm hint (a.subst subst)
      (p.subst subst)
  | .letPredicate hint p q =>
    .letPredicate hint
      (p.subst subst) (q.subst subst)
  | .definition name fs ps =>
    .definition name (fs.map (Term.subst subst)) (ps.map (Predicate.subst subst))

/-- Substitute `argument` for variable `0` in a predicate and decrement remaining indices. -/
def Predicate.subst0 (body : Predicate) (argument : Term) : Predicate :=
  body.subst fun | 0 => argument | i + 1 => .bvar i

/-- Instantiate function and predicate parameters in a predicate, shifting arguments by the binder
`depth`. -/
def Predicate.instantiate (functions : List Term) (predicates : List Predicate)
    (depth : Nat := 0) : Predicate → Predicate
  | .false => .false
  | .true => .true
  | .equal a b => .equal (a.instantiate functions depth)
      (b.instantiate functions depth)
  | .imp a b => .imp (a.instantiate functions predicates depth)
      (b.instantiate functions predicates depth)
  | .and a b => .and (a.instantiate functions predicates depth)
      (b.instantiate functions predicates depth)
  | .or a b => .or (a.instantiate functions predicates depth)
      (b.instantiate functions predicates depth)
  | .all p => .all (p.instantiate functions predicates depth)
  | .ex p => .ex (p.instantiate functions predicates depth)
  | .parameter i => (predicates[i]?.getD (.parameter i)).shift depth
  | .lam hint p =>
    .lam hint (p.instantiate functions
      predicates (depth + 1))
  | .app p a => .app (p.instantiate functions predicates depth)
      (a.instantiate functions depth)
  | .letTerm hint a p =>
    .letTerm hint (a.instantiate
      functions depth)
      (p.instantiate functions predicates depth)
  | .letPredicate hint p q =>
    .letPredicate hint
      (p.instantiate functions predicates depth)
      (q.instantiate functions predicates depth)
  | .definition name fs ps =>
    .definition name (fs.map (Term.instantiate functions depth))
      (ps.map (Predicate.instantiate functions predicates depth))

/-- Push a local variable of `arity` and shift variable indices in `proofs`. -/
def Context.pushLocal (context : Context) (arity : Arity) : Context :=
  { context with locals := arity :: context.locals, proofs := context.proofs.map Predicate.shift }

/-- Push a local variable of `arity` for checking a term or predicate beneath a binder.
Term and predicate typing reads only the variables and parameters, so the proof hypotheses
are dropped. -/
def Context.pushExpressionLocal (context : Context) (arity : Arity) : Context :=
  { context with locals := arity :: context.locals, proofs := [] }

/-- Push a proof hypothesis. -/
def Context.pushProof (context : Context) (predicate : Predicate) : Context :=
  { context with proofs := predicate :: context.proofs }

end LeanPRA.Core
