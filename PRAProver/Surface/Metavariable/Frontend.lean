module

public meta import PRAProver.Surface.Metavariable.Solver

/-!
# Metavariable sessions at the frontend boundary

Frontend interface for metavariable solving, proof substitution, and converting completed
expressions to Core syntax:

- `hasImplicitBinders` checks whether a predicate type contains an implicit binder.
- `freshProof`, `assignProof`, and `resolveProof` allocate, assign, and resolve proof unknowns.
- `unassigned?` finds the first unassigned metavariable for error reporting.
- `completeTerm`, `completePredicate`, and `completeProof` verify that no metavariables remain and
  convert expressions to `Core` syntax.
-/

public meta section
namespace PRAProver.Surface.Metavariable.Frontend
open Core hiding Term Predicate Proof Context


export Metavariable (State M Failure UnknownId Origin empty isEmpty hasUnassigned
  context displaySlots
  freshLocal allocated assigned settle finish solve rootProblemId contributingProblems)

/-- Check whether `p` contains an implicit binder after weak-head reduction; return `true` if
reduction hits the depth limit so printing prefixes `@`. -/
def hasImplicitBinders : Nat → Environment → Core.Predicate → Bool
  | 0, _, _ => true
  | depth + 1, env, p =>
    match Core.whnfPredicate (depth + 1) env p with
    | .error _ => true
    | .ok p => match p with
      | .lam info body => info.isImplicit || hasImplicitBinders depth env body
      | .all p | .ex p => hasImplicitBinders depth env p
      | .imp p q | .and p q | .or p q =>
        hasImplicitBinders depth env p || hasImplicitBinders depth env q
      | _ => false

export Metavariable (freshTerm freshPredicate resolveTerm resolvePredicate
  termDependencies predicateDependencies Constraint submit constrain)

export Metavariable (freshProof assignProof captureProof resolveProof proofMetas)

export Metavariable (conflicts rootProblem)

/-- First unassigned numerical or predicate metavariable, with its diagnostic subject, source
binder name, and display number. -/
def unassigned? (state : State) : Option (Subject × Lean.Name × Nat) := do
  for (u, i) in state.terms.toList.zipIdx do
    if u.value.isNone then return (.term (.mvar i), u.name, u.id)
  for (u, i) in state.predicates.toList.zipIdx do
    if u.value.isNone then
      return (.predicate (.mvar i), u.name, u.id)
  none

/-- Whether `t` contains no metavariables. -/
def termComplete (_s : State) (t : Term) : Bool := t.isComplete

/-- Whether `p` contains no numerical or predicate metavariables. -/
def predicateComplete (_s : State) (p : Predicate) : Bool := p.isComplete

/-- Whether a proof and its embedded arguments contain no metavariables. -/
def proofComplete (_s : State) (p : Proof) : Bool := p.isComplete

/-- Convert `value` to a `Core.Term`, failing if any metavariable remains. -/
def completeTerm (value : Term) : Except Failure Core.Term := do
  unless (termMetas value).isEmpty do throw (.incomplete "unresolved numerical argument")
  return (⟨0, 0⟩ : Projection).encodeTerm value

/-- Convert `value` to a `Core.Predicate`, failing if any metavariable remains. -/
def completePredicate (value : Predicate) : Except Failure Core.Predicate := do
  let (terms, predicates) := predicateMetas value
  unless terms.isEmpty && predicates.isEmpty do throw (.incomplete "unresolved predicate argument")
  return (⟨0, 0⟩ : Projection).encodePredicate value

/-- Convert `value` to a `Core.Proof`, failing if any metavariable remains. -/
def completeProof (value : Proof) : Except Failure Core.Proof := do
  unless proofComplete (empty 0 0) value do throw (.incomplete "unresolved proof argument")
  ((⟨0, 0⟩ : Projection).encodeProof value).mapError Failure.incomplete

end PRAProver.Surface.Metavariable.Frontend
