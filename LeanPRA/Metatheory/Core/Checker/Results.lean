module

public import LeanPRA.Core.Checker
public import LeanPRA.Metatheory.Core.Judgement.Defs
public import LeanPRA.Metatheory.Core.Judgement.Syntax

/-!
# Successful checker results

- `CheckResult.withSite_eq_ok` and `CheckResult.inDeclaration_eq_ok` remove diagnostic wrappers.
- `CheckResult.bind_eq_ok` exposes successful intermediate results.
- `checkArity_sound` and `checkSort_sound` justify primitive type checks.
-/

namespace LeanPRA.Core

/-- Adding an expression diagnostic preserves exactly the successful results. -/
@[simp] public theorem CheckResult.withSite_eq_ok {r : CheckResult α} {c s a} :
    r.withSite c s = .ok a ↔ r = .ok a := by
  cases r <;> simp [CheckResult.withSite, Except.mapError]

/-- Adding a declaration diagnostic preserves exactly the successful results. -/
@[simp] public theorem CheckResult.inDeclaration_eq_ok {r : CheckResult α} {n a} :
    r.inDeclaration n = .ok a ↔ r = .ok a := by
  cases r <;> simp [CheckResult.inDeclaration, Except.mapError]

/-- A successful sequential check has successful intermediate and final results. -/
@[simp] public theorem CheckResult.bind_eq_ok {r : CheckResult α}
    {f : α → CheckResult β} {b} :
    (r >>= f) = .ok b ↔ ∃ a, r = .ok a ∧ f a = .ok b := by
  cases r <;> simp [bind, Except.bind]

/-- A successful loop without early exit checks every list entry. -/
@[simp] public theorem CheckResult.forIn_yield_eq_ok (xs : List α)
    (f : α → CheckResult Unit) :
    (forIn xs () (fun a _ => do f a; pure (ForInStep.yield ()))) = .ok () ↔
      ∀ a ∈ xs, f a = .ok () := by
  induction xs with
  | nil => simp [pure, Except.pure]
  | cons a xs ih =>
      cases h : f a with
      | error e => simp [List.forIn_cons, h, bind, Except.bind]
      | ok v =>
          cases v
          simpa [List.forIn_cons, h, bind, Except.bind, pure, Except.pure] using ih

/-- A successful loop that discards results has a successful result at every entry. -/
@[simp] public theorem CheckResult.forIn_discard_eq_ok (xs : List α)
    (f : α → CheckResult β) :
    (forIn xs () (fun a _ => do let _ ← f a; pure (ForInStep.yield ()))) = .ok () ↔
      ∀ a ∈ xs, ∃ b, f a = .ok b := by
  induction xs with
  | nil => simp [pure, Except.pure]
  | cons a xs ih =>
      cases h : f a with
      | error e => simp [List.forIn_cons, h, bind, Except.bind]
      | ok v =>
          simpa [List.forIn_cons, h, bind, Except.bind, pure, Except.pure] using ih

open Theory

/-- Successful numerical arity checking establishes equality of arities. -/
public theorem checkArity_sound {k j} (h : checkArity k j = .ok ()) : k = j := by
  unfold checkArity at h
  split at h <;> simp_all [fail]

/-- Successful argument-count checking establishes exact list length agreement. -/
public theorem checkArgumentCount_sound {n kind k j}
    (h : checkArgumentCount n kind k j = .ok ()) : k = j := by
  unfold checkArgumentCount at h
  split at h <;> simp_all [fail]

/-- Successful sort checking permits only reflexivity or QF inclusion at fixed arity. -/
public theorem checkSort_sound {s t} (h : checkSort s t = .ok ()) (k : Arity) :
    PredicateSubtyping ⟨k, t⟩ ⟨k, s⟩ := by
  cases s <;> cases t <;> simp_all [checkSort, fail]
  all_goals constructor

/-- Successful equality inspection exposes precisely the two numerical sides. -/
public theorem equalitySides_sound {P a b} (run : equalitySides P = .ok (a, b)) :
    P = .equal a b := by
  cases P <;> simp_all [equalitySides, fail, pure, Except.pure]

end LeanPRA.Core
