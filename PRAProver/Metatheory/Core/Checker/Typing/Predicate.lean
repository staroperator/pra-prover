module

public import PRAProver.Metatheory.Core.Checker.Typing.Term
public import PRAProver.Metatheory.Core.Judgement.Formation

/-!
# Soundness of predicate synthesis and checking

- `inferPredicate_sound` justifies the complete inferred predicate signature.
- `checkPredicate_sound` permits the declared QF inclusion.
- `inferFormula_sound`, `checkFormula_sound`, and `checkMotive_sound` specialize arities.
- `checkContext_sound` forms every local proof assumption after context checking succeeds.
- `checkPredicateArguments_sound` establishes complete predicate actual lists.

Predicate references use stored signatures after checking their actuals, depending only on the
parameter context, local term context, and declared signatures.
-/

namespace PRAProver.Core

open Theory

private theorem check_of_infer {n E c}
    (sound : ∀ {P σ}, inferPredicate n E c P = .ok σ → PredicateTyping E c.parameters c.locals P σ)
    {P σ} (run : checkPredicate n E c P σ = .ok ()) :
    PredicateTyping E c.parameters c.locals P σ := by
  simp only [checkPredicate, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok] at run
  obtain ⟨⟨k, s⟩, hP, ⟨⟩, ha, hs⟩ := run
  obtain ⟨j, t⟩ := σ
  have := checkArity_sound ha
  dsimp at this
  subst j
  exact .subsumption (sound hP) (checkSort_sound hs k)

private theorem arguments_of_checks {n E c ks ps}
    (sound : ∀ {P σ}, inferPredicate n E c P = .ok σ → PredicateTyping E c.parameters c.locals P σ)
    (lengths : ks.length = ps.length)
    (checks : ∀ pair ∈ ks.zip ps, checkPredicate n E c pair.2 pair.1 = .ok ()) :
    PredicateArguments E c.parameters c.locals ps ks := by
  induction ks generalizing ps with
  | nil => cases ps <;> simp_all; exact .nil
  | cons σ ks ih =>
      cases ps with
      | nil => simp at lengths
      | cons P ps =>
          refine .cons (check_of_infer sound (checks (σ, P) (by simp)))
            (ih (by simpa using lengths) ?_)
          intro pair hp
          exact checks pair (by simp [hp])

private theorem infer_correct {n E c P σ} (run : inferPredicate n E c P = .ok σ) :
    PredicateTyping E c.parameters c.locals P σ := by
  induction n generalizing c P σ with
  | zero => simp [inferPredicate, exhausted, fail] at run
  | succ n ih =>
      cases P <;> simp only [inferPredicate, CheckResult.withSite_eq_ok] at run
      case false =>
        simp only [pure, Except.pure, Except.ok.injEq] at run
        subst σ
        exact .false
      case true =>
        simp only [pure, Except.pure, Except.ok.injEq] at run
        subst σ
        exact .true
      case letTerm a P =>
        simp only [CheckResult.bind_eq_ok] at run
        obtain ⟨j, hv, hb⟩ := run
        exact .letTerm (inferTerm_sound hv) (ih hb)
      case letPredicate Q P =>
        simp only [CheckResult.bind_eq_ok] at run
        obtain ⟨τ, hv, hb⟩ := run
        exact .letPredicate (ih hv) (ih hb)
      case equal a b =>
        simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
        obtain ⟨⟨⟩, ha, ⟨⟩, hb, rfl⟩ := run
        exact .equal (checkTerm_sound ha) (checkTerm_sound hb)
      case imp A B =>
        simp only [CheckResult.bind_eq_ok, CheckResult.withSite_eq_ok, pure,
          Except.pure, Except.ok.injEq] at run
        obtain ⟨⟨k, s⟩, ha, ⟨j, t⟩, hb, ⟨⟩, hka, ⟨⟩, hkb, rfl⟩ := run
        have := checkArity_sound hka
        dsimp at this
        have := checkArity_sound hkb
        dsimp at this
        subst k; subst j
        exact .imp (.subsumption (ih ha) (.join_left 0 s t))
          (.subsumption (ih hb) (.join_right 0 s t))
      case and A B =>
        simp only [CheckResult.bind_eq_ok, CheckResult.withSite_eq_ok, pure,
          Except.pure, Except.ok.injEq] at run
        obtain ⟨⟨k, s⟩, ha, ⟨j, t⟩, hb, ⟨⟩, hka, ⟨⟩, hkb, rfl⟩ := run
        have := checkArity_sound hka
        dsimp at this
        have := checkArity_sound hkb
        dsimp at this
        subst k; subst j
        exact .and (.subsumption (ih ha) (.join_left 0 s t))
          (.subsumption (ih hb) (.join_right 0 s t))
      case or A B =>
        simp only [CheckResult.bind_eq_ok, CheckResult.withSite_eq_ok, pure,
          Except.pure, Except.ok.injEq] at run
        obtain ⟨⟨k, s⟩, ha, ⟨j, t⟩, hb, ⟨⟩, hka, ⟨⟩, hkb, rfl⟩ := run
        have := checkArity_sound hka
        dsimp at this
        have := checkArity_sound hkb
        dsimp at this
        subst k; subst j
        exact .or (.subsumption (ih ha) (.join_left 0 s t))
          (.subsumption (ih hb) (.join_right 0 s t))
      case all P =>
        simp only [CheckResult.bind_eq_ok, CheckResult.withSite_eq_ok, pure,
          Except.pure, Except.ok.injEq] at run
        obtain ⟨⟨k, s⟩, hP, ⟨⟩, hk, rfl⟩ := run
        have := checkArity_sound hk
        dsimp at this
        subst k
        exact .all (ih hP).toProp
      case ex P =>
        simp only [CheckResult.bind_eq_ok, CheckResult.withSite_eq_ok, pure,
          Except.pure, Except.ok.injEq] at run
        obtain ⟨⟨k, s⟩, hP, ⟨⟩, hk, rfl⟩ := run
        have := checkArity_sound hk
        dsimp at this
        subst k
        exact .ex (ih hP).toProp
      case parameter i =>
        split at run
        next τ lookup =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst σ
          exact .parameter lookup
        next => simp [fail] at run
      case lam body =>
        simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
        obtain ⟨⟨k, s⟩, hb, rfl⟩ := run
        exact .lam (ih hb)
      case app f a =>
        simp only [CheckResult.bind_eq_ok] at run
        obtain ⟨⟨k, s⟩, hf, run⟩ := run
        cases k with
        | zero => simp [fail] at run
        | succ k =>
            simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
            obtain ⟨⟨⟩, ha, rfl⟩ := run
            exact .app (ih hf) (checkTerm_sound ha)
      case definition name fs ps =>
        split at run
        next d lookup =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨⟨⟩, functions, ⟨⟩, count, ⟨⟩, predicates, rfl⟩ := run
          apply PredicateTyping.definition lookup (checkFunctionArguments_sound functions)
            (arguments_of_checks ih (checkArgumentCount_sound count) ?_)
          exact (CheckResult.forIn_yield_eq_ok _ _).mp predicates
        next =>
          simp [referenceError, fail] at run
          split at run <;> contradiction

/-- Successful inference produces a declarative typing at the complete inferred signature. -/
public theorem inferPredicate_sound {n E c P σ} (run : inferPredicate n E c P = .ok σ) :
    PredicateTyping E c.parameters c.locals P σ := infer_correct run

/-- Successful predicate checking establishes typing at the supplied complete signature. -/
public theorem checkPredicate_sound {n E c P σ} (run : checkPredicate n E c P σ = .ok ()) :
    PredicateTyping E c.parameters c.locals P σ := check_of_infer infer_correct run

/-- Successful formula inference establishes an arity-zero predicate at the inferred sort. -/
public theorem inferFormula_sound {n E c P s} (run : inferFormula n E c P = .ok s) :
    PredicateTyping E c.parameters c.locals P ⟨0, s⟩ := by
  simp only [inferFormula, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok, pure,
    Except.pure, Except.ok.injEq] at run
  obtain ⟨⟨k, t⟩, hP, ⟨⟩, hk, rfl⟩ := run
  have := checkArity_sound hk
  dsimp at this
  subst k
  exact infer_correct hP

/-- Formula checking is predicate checking at arity zero. -/
public theorem checkFormula_sound {n E c P s} (run : checkFormula n E c P s = .ok ()) :
    PredicateTyping E c.parameters c.locals P ⟨0, s⟩ := checkPredicate_sound run

/-- Motive checking requires precisely one numerical argument at the supplied sort. -/
public theorem checkMotive_sound {n E c P s} (run : checkMotive n E c P s = .ok ()) :
    PredicateTyping E c.parameters c.locals P ⟨1, s⟩ := checkPredicate_sound run

/-- Successful predicate-argument checking supplies every actual at its declared signature. -/
public theorem checkPredicateArguments_sound {n E c name ks ps}
    (run : checkPredicateArguments n E c name ks ps = .ok ()) :
    PredicateArguments E c.parameters c.locals ps ks := by
  simp only [checkPredicateArguments, CheckResult.bind_eq_ok] at run
  obtain ⟨⟨⟩, count, ⟨⟩, checks, _⟩ := run
  exact arguments_of_checks infer_correct (checkArgumentCount_sound count)
    ((CheckResult.forIn_yield_eq_ok _ _).mp checks)

end PRAProver.Core

namespace PRAProver.Core

open Theory

private theorem context_correct {n E c} (run : checkContext n E c = .ok ()) :
    ContextWF E c.parameters c.locals c.proofs := by
  simp only [checkContext, CheckResult.bind_eq_ok] at run
  obtain ⟨⟨⟩, loop, _⟩ := run
  have checks := (CheckResult.forIn_discard_eq_ok _ _).mp loop
  have types : ∀ P ∈ c.proofs, PredicateTyping E c.parameters c.locals P ⟨0, .prop⟩ := by
    intro P hp
    obtain ⟨s, hs⟩ := checks P hp
    exact (inferFormula_sound hs).toProp
  suffices ∀ H, (∀ P ∈ H, PredicateTyping E c.parameters c.locals P ⟨0, .prop⟩) →
      ContextWF E c.parameters c.locals H from this _ types
  intro H
  induction H with
  | nil => intro _; exact .nil
  | cons P H ih =>
      intro types
      exact .cons (types P (by simp)) (ih (by intro Q hQ; exact types Q (by simp [hQ])))

/-- Successful context checking forms every local proof assumption. -/
public theorem checkContext_sound {n E c} (run : checkContext n E c = .ok ()) :
    ContextWF E c.parameters c.locals c.proofs := context_correct run

end PRAProver.Core
