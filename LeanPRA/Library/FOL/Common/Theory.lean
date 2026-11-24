module

public import LeanPRA.Library.FOL.Common.Proof

/-!
# Inclusion, consistency, and incompleteness of theories

Theories are numerical axiom-membership functions over a fixed language.

- `Subtheory L T U` means that every theorem of `T` is a theorem of `U`.
- `isProof_mono` preserves the same proof tree under inclusion of axiom sets.
- `Consistent L T` means that falsity has no proof in `T`.
- `Independent L T A` says that formula `A` and its negation both have no proof in `T`.
- `Incomplete L T` means that some sentence is independent of `T`.

A sentence is a formula with bound zero. Theory axioms themselves may have open formulas, under the
convention of the common Hilbert system.
-/

@[expose] public section

pra

namespace FOL

/-- `Subtheory L T U` states inclusion of provable formulas in language code `L`. -/
def Subtheory (L : Nat) (T U : Nat → Nat) : Prop :=
  ∀ A, Provable L T A → Provable L U A

theorem Subtheory.refl (L : Nat) (T : Nat → Nat) : Subtheory L T T :=
  fun A h => h

theorem Subtheory.trans (L : Nat) (T U V : Nat → Nat) :
    Subtheory L T U → Subtheory L U V → Subtheory L T V :=
  fun htu huv A h => huv A (htu A h)

/-- Inclusion of axiom sets preserves acceptance of each numerical proof tree. -/
theorem isProof_mono (L : Nat) (T U : Nat → Nat) :
    (∀ A, T A = 1 → U A = 1) → ∀ p, isProof L T p = 1 → isProof L U p = 1 := by
  intro inclusion
  apply strong_induction_of_bool
    (fun p => isProof L T p = 1 → isProof L U p = 1)
    (fun p => bimp (isProof L T p) (isProof L U p))
  · intro p
    constructor
    · intro h ht
      have implication := and_left (bimp_eq_one _ _)
        (and_right (bool_eq_one _ (bimp_bool _ _)) h)
      exact and_right (bool_eq_one _ (isProof_bool L U p))
        (implication (and_left (bool_eq_one _ (isProof_bool L T p)) ht))
    · intro h
      apply and_left (bool_eq_one _ (bimp_bool _ _))
      apply and_right (bimp_eq_one _ _)
      intro ht
      exact and_left (bool_eq_one _ (isProof_bool L U p))
        (h (and_right (bool_eq_one _ (isProof_bool L T p)) ht))
  · intro p earlier hp
    by_cases hz : p = 0
    · rw [hz, isProof_zero L T] at hp
      exact false_elim (zero_ne_succ 0 hp)
    have children_lt : Proof.premises p < p := by
      have he := succ_pred p hz
      have bound : Proof.premises p ≤ pred p :=
        le_trans _ _ _ (unpairRight_le (unpairRight (pred p)))
          (unpairRight_le (pred p))
      have h := lt_of_le_of_lt _ _ _ bound (lt_succ_self (pred p))
      rw [he] at h
      exact h
    have left_lt : unpairLeft (Proof.premises p) < p :=
      lt_of_le_of_lt _ _ _ (unpairLeft_le (Proof.premises p)) children_lt
    have right_lt : unpairRight (Proof.premises p) < p :=
      lt_of_le_of_lt _ _ _ (unpairRight_le (Proof.premises p)) children_lt
    have reconstruct :
        S (pair (Proof.rule p) (pair (Proof.conclusion p) (Proof.premises p))) = p := by
      rw [Proof.rule, Proof.conclusion, Proof.premises, pair_unpair, pair_unpair]
      exact succ_pred p hz
    have ht := isProof_node_eq L T (Proof.rule p) (Proof.conclusion p) (Proof.premises p)
    have hu := isProof_node_eq L U (Proof.rule p) (Proof.conclusion p) (Proof.premises p)
    rw [reconstruct] at ht
    rw [reconstruct] at hu
    rw [hu]
    rw [ht] at hp
    by_cases h0 : Proof.rule p = 0
    · rw [h0] at hp
      rw [h0]
      rw [eqb_self 0, ite_succ] at hp
      rw [eqb_self 0, ite_succ]
      exact hp
    rw [and_right (eqb_eq_zero (Proof.rule p) 0) h0] at hp
    rw [and_right (eqb_eq_zero (Proof.rule p) 0) h0]
    by_cases h1 : Proof.rule p = 1
    · rw [h1] at hp
      rw [h1]
      by_cases hc : Proof.premises p = 0
      · rw [hc] at hp
        rw [hc]
        apply and_right (eqb_eq_one _ _)
        exact inclusion _ (and_left (eqb_eq_one _ _) hp)
      · rw [and_right (eqb_eq_zero (Proof.premises p) 0) hc] at hp
        exact false_elim (zero_ne_succ 0 hp)
    rw [and_right (eqb_eq_zero (Proof.rule p) 1) h1] at hp
    rw [and_right (eqb_eq_zero (Proof.rule p) 1) h1]
    by_cases h2 : Proof.rule p = 2
    · rw [h2] at hp
      rw [h2]
      let a := unpairLeft (Proof.premises p)
      let b := unpairRight (Proof.premises p)
      rw [ite_zero, ite_zero, eqb_self 2, ite_succ] at hp
      rw [ite_zero, ite_zero, eqb_self 2, ite_succ]
      have parts := and_left (band_eq_one _ _) hp
      have both := and_left (band_eq_one _ _)
        (and_right (bool_eq_one _ (band_bool _ _)) (and_left parts))
      have ha := earlier a left_lt
        (and_right (bool_eq_one _ (isProof_bool L T a)) (and_left both))
      have hb := earlier b right_lt
        (and_right (bool_eq_one _ (isProof_bool L T b)) (and_right both))
      rw [ha, hb]
      exact and_right (band_eq_one _ _) (succ_ne_zero 0, and_right parts)
    rw [and_right (eqb_eq_zero (Proof.rule p) 2) h2] at hp
    rw [and_right (eqb_eq_zero (Proof.rule p) 2) h2]
    by_cases h3 : Proof.rule p = 3
    · rw [h3] at hp
      rw [h3]
      let a := Proof.premises p
      let guard := eqb (Proof.conclusion p) (Formula.all (Proof.conclusion a))
      have hp : band (isProof L T a) guard = 1 := hp
      change band (isProof L U a) guard = 1
      have parts := and_left (band_eq_one _ _) hp
      have ha := earlier a children_lt
        (and_right (bool_eq_one _ (isProof_bool L T a)) (and_left parts))
      rw [ha]
      exact and_right (band_eq_one _ _) (succ_ne_zero 0, and_right parts)
    rw [and_right (eqb_eq_zero (Proof.rule p) 3) h3] at hp
    exact false_elim (zero_ne_succ 0 hp)

theorem subtheory_of_axiom_inclusion (L : Nat) (T U : Nat → Nat) :
    (∀ A, T A = 1 → U A = 1) → Subtheory L T U := by
  intro inclusion A h
  rcases h with (p, hp, ha)
  exact (p, isProof_mono L T U inclusion p hp, ha)

/-- `Consistent L T` states that no numerical proof in `T` concludes falsity. -/
def Consistent (L : Nat) (T : Nat → Nat) : Prop := ¬ Provable L T Formula.falsum

/-- `Independent L T A` states that neither formula `A` nor its negation has a proof in `T`.
The formula may have free variable positions. -/
def Independent (L : Nat) (T : Nat → Nat) : Nat → Prop := fun A =>
  ¬ Provable L T A ∧ ¬ Provable L T (Formula.neg A)

/-- `Incomplete L T` states that `T` has an independent sentence. -/
def Incomplete (L : Nat) (T : Nat → Nat) : Prop :=
  ∃ A, Formula.Closed L A ∧ Independent L T A

theorem Consistent.not_both (L : Nat) (T : Nat → Nat) :
    Consistent L T → ∀ A, Provable L T A → ¬ Provable L T (Formula.neg A) :=
  fun consistent A positive negative =>
    consistent (Provable.mp L T A Formula.falsum negative positive)

theorem Consistent.of_subtheory (L : Nat) (T U : Nat → Nat) :
    Subtheory L T U → Consistent L U → Consistent L T :=
  fun htu hu ht => hu (htu Formula.falsum ht)

theorem Independent.of_subtheory (L : Nat) (T U : Nat → Nat) :
    Subtheory L T U → ∀ A, Independent L U A → Independent L T A := by
  intro htu A h
  rcases h with (positive, negative)
  exact ((fun ht => positive (htu A ht)),
    (fun ht => negative (htu (Formula.neg A) ht)))

theorem Incomplete.of_subtheory (L : Nat) (T U : Nat → Nat) :
    Subtheory L T U → Incomplete L U → Incomplete L T := by
  intro htu h
  rcases h with (A, closed, ha)
  exact (A, closed, Independent.of_subtheory L T U htu A ha)

end FOL

end
