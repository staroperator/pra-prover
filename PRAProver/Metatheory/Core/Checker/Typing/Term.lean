module

public import PRAProver.Metatheory.Core.Checker.Results
public import PRAProver.Metatheory.Core.Judgement.Inversion

/-!
# Soundness of numerical term synthesis and checking

- `inferTerm_sound` derives the inferred numerical arity.
- `checkTerm_sound` derives typing at the expected arity.
- `checkFunctionArguments_sound` checks a complete list of function actuals.

These procedures depend only on the parameter context, local term context, and declared function
signatures.
-/

namespace PRAProver.Core

open Theory

private theorem arguments_of_checks {n E c ks fs}
    (sound : ∀ {t k}, inferTerm n E c t = .ok k → TermTyping E c.parameters c.locals t k)
    (lengths : ks.length = fs.length)
    (checks : ∀ pair ∈ ks.zip fs,
      (do checkArity pair.1 (← inferTerm n E c pair.2)).withSite c (.term pair.2) = .ok ()) :
    FunctionArguments E c.parameters c.locals fs ks := by
  induction ks generalizing fs with
  | nil => cases fs <;> simp_all; exact .nil
  | cons k ks ih =>
      cases fs with
      | nil => simp at lengths
      | cons t fs =>
          have head := checks (k, t) (by simp)
          simp only [CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok] at head
          obtain ⟨j, hj, hc⟩ := head
          have := checkArity_sound hc
          subst j
          refine .cons (sound hj) (ih (by simpa using lengths) ?_)
          intro pair hp
          exact checks pair (by simp [hp])

private theorem infer_correct {n E c t k} (run : inferTerm n E c t = .ok k) :
    TermTyping E c.parameters c.locals t k := by
  induction n generalizing c t k with
  | zero => simp [inferTerm, exhausted, fail] at run
  | succ n ih =>
      cases t <;> simp only [inferTerm, CheckResult.withSite_eq_ok] at run
      case bvar i =>
        split at run
        next j lookup =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst k
          exact .bvar lookup
        next => simp [fail] at run
      case parameter i =>
        split at run
        next j lookup =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst k
          exact .parameter lookup
        next => simp [fail] at run
      case zero =>
        simp only [pure, Except.pure, Except.ok.injEq] at run
        subst k
        exact .zero
      case succ =>
        simp only [pure, Except.pure, Except.ok.injEq] at run
        subst k
        exact .succ
      case lam body =>
        simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
        obtain ⟨j, hj, rfl⟩ := run
        exact .lam (ih hj)
      case app f a =>
        simp only [CheckResult.bind_eq_ok] at run
        obtain ⟨j, hj, run⟩ := run
        cases j with
        | zero => simp [fail] at run
        | succ j =>
            simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
            obtain ⟨m, hm, ⟨⟩, hc, rfl⟩ := run
            have := checkArity_sound hc
            subst m
            exact .app (ih hj) (ih hm)
      case letE value body =>
        simp only [CheckResult.bind_eq_ok] at run
        obtain ⟨j, hj, hb⟩ := run
        exact .letE (ih hj) (ih hb)
      case primrec b s =>
        simp only [CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok, pure,
          Except.pure, Except.ok.injEq] at run
        obtain ⟨⟨⟩, ⟨j, hj, hbc⟩, ⟨⟩, ⟨l, hl, hsc⟩, rfl⟩ := run
        have := checkArity_sound hbc
        have := checkArity_sound hsc
        subst j; subst l
        exact .primrec (ih hj) (ih hl)
      case definition name fs =>
        split at run
        next d lookup =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨⟨⟩, count, ⟨⟩, checks, rfl⟩ := run
          apply TermTyping.definition lookup
          apply arguments_of_checks ih (checkArgumentCount_sound count)
          exact (CheckResult.forIn_yield_eq_ok _ _).mp checks
        next =>
          simp [referenceError, fail] at run
          split at run <;> contradiction

/-- A successful internal inference is a declarative numerical typing derivation. -/
public theorem inferTerm_sound {n E c t k} (run : inferTerm n E c t = .ok k) :
    TermTyping E c.parameters c.locals t k := infer_correct run

/-- A successful internal term check establishes typing at its expected arity. -/
public theorem checkTerm_sound {n E c t k} (run : checkTerm n E c t k = .ok ()) :
    TermTyping E c.parameters c.locals t k := by
  simp only [checkTerm, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok] at run
  obtain ⟨j, hj, hc⟩ := run
  have := checkArity_sound hc
  subst j
  exact infer_correct hj

/-- Successful function-argument checking supplies every actual at its declared arity. -/
public theorem checkFunctionArguments_sound {n E c name ks fs}
    (run : checkFunctionArguments n E c name ks fs = .ok ()) :
    FunctionArguments E c.parameters c.locals fs ks := by
  simp only [checkFunctionArguments, CheckResult.bind_eq_ok] at run
  obtain ⟨⟨⟩, count, ⟨⟩, checks, _⟩ := run
  exact arguments_of_checks infer_correct (checkArgumentCount_sound count)
    ((CheckResult.forIn_yield_eq_ok _ _).mp checks)

end PRAProver.Core
