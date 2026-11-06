module

public import LeanPRA.Metatheory.Core.Properties.Normalization.WeakHead

/-!
# Normal-form shape of successful reduction

- `reduceTerm_normal` and `reduceTermNeutral_normal` characterize numerical outputs.
- `reducePredicate_normal` and `reducePredicateNeutral_normal` characterize predicates.
- `reduceFormula_normal` specializes the result to formulas.

These theorems apply to successful reductions. A returned recursor has a blocked normal argument,
and typing preservation is proved in `Soundness`.
-/

namespace LeanPRA.Core

open Theory

private theorem neutral_succ {n E t u} (head : TermWhnf t)
    (run : reduceTermNeutral n E t = .ok u) : u = .succ ↔ t = .succ := by
  cases n with
  | zero => simp [reduceTermNeutral, exhausted, fail] at run
  | succ n =>
      simp only [reduceTermNeutral, CheckResult.bind_eq_ok] at run
      obtain ⟨w, hw, run⟩ := run
      have := whnfTerm_fixed head hw
      subst w
      cases t <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
        Except.ok.injEq, fail] at run <;> try contradiction
      case app f a =>
        obtain ⟨g, hg, b, hb, rfl⟩ := run
        simp
      all_goals subst u; simp

private theorem blocked_preserved {n E t u} (head : TermWhnf t) (blocked : TermBlocked t)
    (run : reduceTerm n E 0 t = .ok u) : TermBlocked u := by
  cases n with
  | zero => simp [reduceTerm, exhausted, fail] at run
  | succ n =>
      simp only [reduceTerm, CheckResult.bind_eq_ok] at run
      obtain ⟨w, hw, run⟩ := run
      have := whnfTerm_fixed head hw
      subst w
      cases t <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
        Except.ok.injEq, fail] at run <;> try contradiction
      case zero => exact False.elim (blocked.1 rfl)
      case app f a =>
        obtain ⟨g, hg, b, hb, rfl⟩ := run
        cases head with
        | app hf notLam =>
            constructor
            · intro h; cases h
            · intro p h
              have eqg := (Term.app.inj h).1
              have eqf := (neutral_succ hf hg).mp eqg
              exact blocked.2 a (by rw [eqf])
      case primrec b s a =>
        obtain ⟨c, hc, v, hv, m, hm, rfl⟩ := run
        constructor
        · intro h; cases h
        · intro p h; cases h
      all_goals
        subst u
        constructor
        · intro h; cases h
        · intro p h; cases h

private theorem term_normal (n : Nat) :
    (∀ {E k t u}, reduceTerm n E k t = .ok u → TermNormal k u) ∧
    (∀ {E t u}, reduceTermNeutral n E t = .ok u → TermNeutral u) := by
  induction n with
  | zero =>
      constructor <;> intros <;> simp_all [reduceTerm, reduceTermNeutral, exhausted, fail]
  | succ n ih =>
      constructor
      · intro E k t u run
        cases k with
        | succ k =>
            simp only [reduceTerm, CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq] at run
            obtain ⟨body, hb, rfl⟩ := run
            exact .lam (ih.1 hb)
        | zero =>
            simp only [reduceTerm, CheckResult.bind_eq_ok] at run
            obtain ⟨w, hw, run⟩ := run
            have head := whnfTerm_normal hw
            cases w <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq, fail] at run <;> try contradiction
            case bvar i => subst u; exact .bvar
            case parameter i => subst u; exact .parameter
            case zero => subst u; exact .zero
            case app f a =>
              obtain ⟨g, hg, b, hb, rfl⟩ := run
              exact .app (ih.2 hg) (ih.1 hb)
            case primrec b s a =>
              obtain ⟨c, hc, v, hv, m, hm, rfl⟩ := run
              cases head with
              | primrec argument blocked =>
                  exact .primrec (ih.1 hc) (ih.1 hv) (ih.1 hm)
                    (blocked_preserved argument blocked hm)
      · intro E t u run
        simp only [reduceTermNeutral, CheckResult.bind_eq_ok] at run
        obtain ⟨w, hw, run⟩ := run
        cases w <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
          Except.ok.injEq, fail] at run <;> try contradiction
        case bvar i => subst u; exact .bvar
        case parameter i => subst u; exact .parameter
        case succ => subst u; exact .succ
        case app f a =>
          obtain ⟨g, hg, b, hb, rfl⟩ := run
          exact .app (ih.2 hg) (ih.1 hb)

private theorem predicate_normal (n : Nat) :
    (∀ {E k P Q}, reducePredicate n E k P = .ok Q → PredicateNormal k Q) ∧
    (∀ {E P Q}, reducePredicateNeutral n E P = .ok Q → PredicateNeutral Q) := by
  induction n with
  | zero =>
      constructor <;> intros <;>
        simp_all [reducePredicate, reducePredicateNeutral, exhausted, fail]
  | succ n ih =>
      constructor
      · intro E k P Q run
        cases k with
        | succ k =>
            simp only [reducePredicate, CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq] at run
            obtain ⟨body, hb, rfl⟩ := run
            exact .lam (ih.1 hb)
        | zero =>
            simp only [reducePredicate, CheckResult.bind_eq_ok] at run
            obtain ⟨R, hR, run⟩ := run
            cases R <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq, fail] at run <;> try contradiction
            case false => subst Q; exact .false
            case true => subst Q; exact .true
            case parameter i => subst Q; exact .parameter
            case equal a b =>
              obtain ⟨c, hc, d, hd, rfl⟩ := run
              exact .equal ((term_normal n).1 hc) ((term_normal n).1 hd)
            case imp A B =>
              obtain ⟨C, hC, D, hD, rfl⟩ := run
              exact .imp (ih.1 hC) (ih.1 hD)
            case and A B =>
              obtain ⟨C, hC, D, hD, rfl⟩ := run
              exact .and (ih.1 hC) (ih.1 hD)
            case or A B =>
              obtain ⟨C, hC, D, hD, rfl⟩ := run
              exact .or (ih.1 hC) (ih.1 hD)
            case all A =>
              obtain ⟨B, hB, rfl⟩ := run
              exact .all (ih.1 hB)
            case ex A =>
              obtain ⟨B, hB, rfl⟩ := run
              exact .ex (ih.1 hB)
            case app f a =>
              obtain ⟨g, hg, b, hb, rfl⟩ := run
              exact .app (ih.2 hg) ((term_normal n).1 hb)
      · intro E P Q run
        simp only [reducePredicateNeutral, CheckResult.bind_eq_ok] at run
        obtain ⟨R, hR, run⟩ := run
        cases R <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
          Except.ok.injEq, fail] at run <;> try contradiction
        case parameter i => subst Q; exact .parameter
        case app f a =>
          obtain ⟨g, hg, b, hb, rfl⟩ := run
          exact .app (ih.2 hg) ((term_normal n).1 hb)

/-- Neutral normalization preserves whether an already weak-head input is bare successor. -/
public theorem reduceTermNeutral_succ_iff {n E t u} (head : TermWhnf t)
    (run : reduceTermNeutral n E t = .ok u) : u = .succ ↔ t = .succ :=
  neutral_succ head run

/-- Successful full term reduction returns beta-normal, eta-long syntax at the requested arity. -/
public theorem reduceTerm_normal {n E k t u} (run : reduceTerm n E k t = .ok u) :
    TermNormal k u := (term_normal n).1 run

/-- Successful neutral term reduction returns a neutral chain with normal arguments. -/
public theorem reduceTermNeutral_normal {n E t u} (run : reduceTermNeutral n E t = .ok u) :
    TermNeutral u := (term_normal n).2 run

/-- Successful predicate reduction returns normal syntax at the requested arity. -/
public theorem reducePredicate_normal {n E k P Q} (run : reducePredicate n E k P = .ok Q) :
    PredicateNormal k Q := (predicate_normal n).1 run

/-- Successful neutral predicate reduction returns a neutral chain with normal numbers. -/
public theorem reducePredicateNeutral_normal {n E P Q}
    (run : reducePredicateNeutral n E P = .ok Q) : PredicateNeutral Q :=
  (predicate_normal n).2 run

/-- Successful formula reduction returns arity-zero normal predicate syntax. -/
public theorem reduceFormula_normal {n E P Q} (run : reduceFormula n E P = .ok Q) :
    PredicateNormal 0 Q := reducePredicate_normal run

end LeanPRA.Core
