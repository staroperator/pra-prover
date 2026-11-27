module

public import PRAProver.Metatheory.Core.Checker.Results

/-!
# Stability of successful reduction under increasing depth

The `*_mono` theorems preserve the exact successful result when the recursive-depth
budget increases. They cover weak-head, full, neutral, and formula reduction.
-/

namespace PRAProver.Core

private theorem whnf_term_step {n E t u} (run : whnfTerm n E t = .ok u) :
    whnfTerm (n + 1) E t = .ok u := by
  induction n generalizing t u with
  | zero => simp [whnfTerm, exhausted, fail] at run
  | succ n ih =>
      cases t <;> rw [whnfTerm.eq_def] at run ⊢ <;>
        simp only [Nat.add_one] at run ⊢
      case definition name fs =>
        split at run
        next d lookup => exact ih run
        next =>
          simp [referenceError, fail] at run
          split at run <;> contradiction
      case letE a body => exact ih run
      case app f a =>
        simp only [CheckResult.bind_eq_ok] at run ⊢
        obtain ⟨g, hg, run⟩ := run
        refine ⟨g, ih hg, ?_⟩
        cases g <;> try first | exact ih run | exact run
        case primrec b s =>
          simp only [CheckResult.bind_eq_ok] at run ⊢
          obtain ⟨m, hm, run⟩ := run
          refine ⟨m, ih hm, ?_⟩
          cases m with
          | zero => exact ih run
          | app f p => cases f <;> first | exact ih run | exact run
          | _ => exact run
      all_goals exact run

private theorem term_step (n : Nat) :
    (∀ {E k t u}, reduceTerm n E k t = .ok u → reduceTerm (n + 1) E k t = .ok u) ∧
    (∀ {E t u}, reduceTermNeutral n E t = .ok u →
      reduceTermNeutral (n + 1) E t = .ok u) := by
  induction n with
  | zero =>
      constructor <;> intros <;> simp_all [reduceTerm, reduceTermNeutral, exhausted, fail]
  | succ n ih =>
      constructor
      · intro E k t u run
        cases k with
        | succ k =>
            rw [reduceTerm.eq_def] at run ⊢
            simp only [CheckResult.bind_eq_ok] at run ⊢
            obtain ⟨body, hb, hu⟩ := run
            exact ⟨body, ih.1 hb, hu⟩
        | zero =>
            rw [reduceTerm.eq_def] at run ⊢
            simp only [CheckResult.bind_eq_ok] at run ⊢
            obtain ⟨m, hm, run⟩ := run
            refine ⟨m, whnf_term_step hm, ?_⟩
            cases m <;> simp only [fail] at run ⊢ <;>
              try contradiction
            case app f a =>
              cases f <;> simp only [CheckResult.bind_eq_ok] at run ⊢
              case primrec b s =>
                obtain ⟨c, hc, v, hv, m, hm, hu⟩ := run
                exact ⟨c, ih.1 hc, v, ih.1 hv, m, ih.1 hm, hu⟩
              all_goals
                obtain ⟨g, hg, b, hb, hu⟩ := run
                exact ⟨g, ih.2 hg, b, ih.1 hb, hu⟩
            all_goals exact run
      · intro E t u run
        rw [reduceTermNeutral.eq_def] at run ⊢
        simp only [CheckResult.bind_eq_ok] at run ⊢
        obtain ⟨m, hm, run⟩ := run
        refine ⟨m, whnf_term_step hm, ?_⟩
        cases m <;> simp only [CheckResult.bind_eq_ok, fail] at run ⊢ <;>
          try contradiction
        case app f a =>
          obtain ⟨g, hg, b, hb, hu⟩ := run
          exact ⟨g, ih.2 hg, b, ih.1 hb, hu⟩
        all_goals exact run

private theorem whnf_predicate_step {n E P Q} (run : whnfPredicate n E P = .ok Q) :
    whnfPredicate (n + 1) E P = .ok Q := by
  induction n generalizing P Q with
  | zero => simp [whnfPredicate, exhausted, fail] at run
  | succ n ih =>
      cases P <;> rw [whnfPredicate.eq_def] at run ⊢ <;>
        simp only [Nat.add_one] at run ⊢
      case definition name fs ps =>
        split at run
        next d lookup => exact ih run
        next =>
          simp [referenceError, fail] at run
          split at run <;> contradiction
      case app f a =>
        simp only [CheckResult.bind_eq_ok] at run ⊢
        obtain ⟨g, hg, run⟩ := run
        refine ⟨g, ih hg, ?_⟩
        cases g <;> first | exact ih run | exact run
      case letTerm => exact ih run
      case letPredicate => exact ih run
      all_goals exact run

private theorem predicate_step (n : Nat) :
    (∀ {E k P Q}, reducePredicate n E k P = .ok Q →
      reducePredicate (n + 1) E k P = .ok Q) ∧
    (∀ {E P Q}, reducePredicateNeutral n E P = .ok Q →
      reducePredicateNeutral (n + 1) E P = .ok Q) := by
  induction n with
  | zero =>
      constructor <;> intros <;>
        simp_all [reducePredicate, reducePredicateNeutral, exhausted, fail]
  | succ n ih =>
      constructor
      · intro E k P Q run
        cases k with
        | succ k =>
            rw [reducePredicate.eq_def] at run ⊢
            simp only [CheckResult.bind_eq_ok] at run ⊢
            obtain ⟨body, hb, hQ⟩ := run
            exact ⟨body, ih.1 hb, hQ⟩
        | zero =>
            rw [reducePredicate.eq_def] at run ⊢
            simp only [CheckResult.bind_eq_ok] at run ⊢
            obtain ⟨R, hR, run⟩ := run
            refine ⟨R, whnf_predicate_step hR, ?_⟩
            cases R <;> simp only [CheckResult.bind_eq_ok, fail] at run ⊢ <;>
              try contradiction
            case equal a b =>
              obtain ⟨c, hc, d, hd, hQ⟩ := run
              exact ⟨c, (term_step n).1 hc, d, (term_step n).1 hd, hQ⟩
            case imp A B =>
              obtain ⟨C, hC, D, hD, hQ⟩ := run
              exact ⟨C, ih.1 hC, D, ih.1 hD, hQ⟩
            case and A B =>
              obtain ⟨C, hC, D, hD, hQ⟩ := run
              exact ⟨C, ih.1 hC, D, ih.1 hD, hQ⟩
            case or A B =>
              obtain ⟨C, hC, D, hD, hQ⟩ := run
              exact ⟨C, ih.1 hC, D, ih.1 hD, hQ⟩
            case all A =>
              obtain ⟨B, hB, hQ⟩ := run
              exact ⟨B, ih.1 hB, hQ⟩
            case ex A =>
              obtain ⟨B, hB, hQ⟩ := run
              exact ⟨B, ih.1 hB, hQ⟩
            case app f a =>
              obtain ⟨g, hg, b, hb, hQ⟩ := run
              exact ⟨g, ih.2 hg, b, (term_step n).1 hb, hQ⟩
            all_goals exact run
      · intro E P Q run
        rw [reducePredicateNeutral.eq_def] at run ⊢
        simp only [CheckResult.bind_eq_ok] at run ⊢
        obtain ⟨R, hR, run⟩ := run
        refine ⟨R, whnf_predicate_step hR, ?_⟩
        cases R <;> simp only [CheckResult.bind_eq_ok, fail] at run ⊢ <;>
          try contradiction
        case app f a =>
          obtain ⟨g, hg, b, hb, hQ⟩ := run
          exact ⟨g, ih.2 hg, b, (term_step n).1 hb, hQ⟩
        all_goals exact run

/-- Increasing the depth budget preserves a successful weak-head term result exactly. -/
public theorem whnfTerm_mono {n m E t u} (le : n ≤ m) (run : whnfTerm n E t = .ok u) :
    whnfTerm m E t = .ok u := by
  induction le with
  | refl => exact run
  | step le ih => exact whnf_term_step ih

/-- Increasing the depth budget preserves a successful full term result exactly. -/
public theorem reduceTerm_mono {n m E k t u} (le : n ≤ m) (run : reduceTerm n E k t = .ok u) :
    reduceTerm m E k t = .ok u := by
  induction le with
  | refl => exact run
  | @step m le ih => exact (term_step m).1 ih

/-- Increasing the depth budget preserves a successful neutral term result exactly. -/
public theorem reduceTermNeutral_mono {n m E t u} (le : n ≤ m)
    (run : reduceTermNeutral n E t = .ok u) : reduceTermNeutral m E t = .ok u := by
  induction le with
  | refl => exact run
  | @step m le ih => exact (term_step m).2 ih

/-- Increasing the depth budget preserves a successful weak-head predicate result exactly. -/
public theorem whnfPredicate_mono {n m E P Q} (le : n ≤ m)
    (run : whnfPredicate n E P = .ok Q) : whnfPredicate m E P = .ok Q := by
  induction le with
  | refl => exact run
  | step le ih => exact whnf_predicate_step ih

/-- Increasing the depth budget preserves a successful full predicate result exactly. -/
public theorem reducePredicate_mono {n m E k P Q} (le : n ≤ m)
    (run : reducePredicate n E k P = .ok Q) : reducePredicate m E k P = .ok Q := by
  induction le with
  | refl => exact run
  | @step m le ih => exact (predicate_step m).1 ih

/-- Increasing the depth budget preserves a successful neutral predicate result exactly. -/
public theorem reducePredicateNeutral_mono {n m E P Q} (le : n ≤ m)
    (run : reducePredicateNeutral n E P = .ok Q) : reducePredicateNeutral m E P = .ok Q := by
  induction le with
  | refl => exact run
  | @step m le ih => exact (predicate_step m).2 ih

/-- Increasing the depth budget preserves a successful formula result exactly. -/
public theorem reduceFormula_mono {n m E P Q} (le : n ≤ m)
    (run : reduceFormula n E P = .ok Q) : reduceFormula m E P = .ok Q :=
  reducePredicate_mono le run

/-- Two successful `whnfTerm` runs at different depths return the same syntax. -/
public theorem whnfTerm_unique {n m E t u v}
    (left : whnfTerm n E t = .ok u)
    (right : whnfTerm m E t = .ok v) : u = v := by
  have eq := (whnfTerm_mono (Nat.le_max_left n m) left).symm.trans
    (whnfTerm_mono (Nat.le_max_right n m) right)
  exact Except.ok.inj eq

/-- Two successful `reduceTerm` runs at different depths return the same syntax. -/
public theorem reduceTerm_unique {n m E k t u v}
    (left : reduceTerm n E k t = .ok u)
    (right : reduceTerm m E k t = .ok v) : u = v := by
  have eq := (reduceTerm_mono (Nat.le_max_left n m) left).symm.trans
    (reduceTerm_mono (Nat.le_max_right n m) right)
  exact Except.ok.inj eq

/-- Two successful `reduceTermNeutral` runs at different depths return the same syntax. -/
public theorem reduceTermNeutral_unique {n m E t u v}
    (left : reduceTermNeutral n E t = .ok u)
    (right : reduceTermNeutral m E t = .ok v) : u = v := by
  have eq := (reduceTermNeutral_mono (Nat.le_max_left n m) left).symm.trans
    (reduceTermNeutral_mono (Nat.le_max_right n m) right)
  exact Except.ok.inj eq

/-- Two successful `whnfPredicate` runs at different depths return the same syntax. -/
public theorem whnfPredicate_unique {n m E P Q R}
    (left : whnfPredicate n E P = .ok Q)
    (right : whnfPredicate m E P = .ok R) : Q = R := by
  have eq := (whnfPredicate_mono (Nat.le_max_left n m) left).symm.trans
    (whnfPredicate_mono (Nat.le_max_right n m) right)
  exact Except.ok.inj eq

/-- Two successful `reducePredicate` runs at different depths return the same syntax. -/
public theorem reducePredicate_unique {n m E k P Q R}
    (left : reducePredicate n E k P = .ok Q)
    (right : reducePredicate m E k P = .ok R) : Q = R := by
  have eq := (reducePredicate_mono (Nat.le_max_left n m) left).symm.trans
    (reducePredicate_mono (Nat.le_max_right n m) right)
  exact Except.ok.inj eq

/-- Two successful `reducePredicateNeutral` runs at different depths return the same syntax. -/
public theorem reducePredicateNeutral_unique {n m E P Q R}
    (left : reducePredicateNeutral n E P = .ok Q)
    (right : reducePredicateNeutral m E P = .ok R) : Q = R := by
  have eq := (reducePredicateNeutral_mono (Nat.le_max_left n m) left).symm.trans
    (reducePredicateNeutral_mono (Nat.le_max_right n m) right)
  exact Except.ok.inj eq

/-- Two successful `reduceFormula` runs at different depths return the same syntax. -/
public theorem reduceFormula_unique {n m E P Q R}
    (left : reduceFormula n E P = .ok Q)
    (right : reduceFormula m E P = .ok R) : Q = R := by
  have eq := (reduceFormula_mono (Nat.le_max_left n m) left).symm.trans
    (reduceFormula_mono (Nat.le_max_right n m) right)
  exact Except.ok.inj eq

end PRAProver.Core
