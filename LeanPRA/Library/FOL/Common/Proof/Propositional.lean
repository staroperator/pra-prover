module

public import LeanPRA.Library.FOL.Common.Proof
public meta import LeanPRA.Library.Tactic.Witnessing

/-!
# Derived propositional rules

These PRA proofs derive the propositional rules from the Hilbert axioms for arbitrary numerical
language, theory, and formula parameters. Implication composition and reasoning under a shared
assumption provide the intermediate steps.

- `FOL.Provable.imp_refl` proves reflexivity of implication.
- The conjunction and disjunction rules give introduction and elimination implications.
- The implication and contraposition rules support reasoning under assumptions.

Numerical witnesses for the rules used in proof-code constructions are extracted at the end.
-/

@[expose] public section

pra

namespace FOL.Provable

open Formula

/-- A proved conclusion remains provable with an additional premise. -/
theorem imp_of_provable (L : Nat) (T : Nat → Nat) {A B : Nat} :
    Provable L T B → Provable L T (imp A B) :=
  fun h => mp L T B (imp A B) (implication L T B A) h

/-- Apply modus ponens while keeping a shared assumption. -/
theorem mp_under (L : Nat) (T : Nat → Nat) {E A B : Nat} :
    Provable L T (imp E (imp A B)) → Provable L T (imp E A) →
      Provable L T (imp E B) :=
  fun h k => mp L T _ _ (mp L T _ _ (implicationDistribution L T E A B) h) k

theorem imp_refl (L : Nat) (T : Nat → Nat) (A : Nat) :
    Provable L T (imp A A) :=
  mp_under L T (implication L T A (imp A A)) (implication L T A A)

/-- A proved implication can be applied beneath another premise. -/
theorem imp_mono_right_of_provable (L : Nat) (T : Nat → Nat) {E A B : Nat} :
    Provable L T (imp A B) → Provable L T (imp (imp E A) (imp E B)) :=
  fun h => mp L T _ _ (implicationDistribution L T E A B) (imp_of_provable L T h)

theorem imp_trans_of_provable (L : Nat) (T : Nat → Nat) {A B C : Nat} :
    Provable L T (imp A B) → Provable L T (imp B C) → Provable L T (imp A C) :=
  fun h k => mp L T _ _ (imp_mono_right_of_provable L T k) h

/-- Exchange the two leading premises of a proved implication. -/
theorem imp_swap (L : Nat) (T : Nat → Nat) {A B C : Nat} :
    Provable L T (imp A (imp B C)) → Provable L T (imp B (imp A C)) :=
  fun h => imp_trans_of_provable L T (implication L T B A)
    (mp L T _ _ (implicationDistribution L T A B C) h)

theorem imp_mono_right (L : Nat) (T : Nat → Nat) (E A B : Nat) :
    Provable L T (imp (imp A B) (imp (imp E A) (imp E B))) :=
  imp_trans_of_provable L T (implication L T (imp A B) E) (implicationDistribution L T E A B)

theorem imp_trans (L : Nat) (T : Nat → Nat) (A B C : Nat) :
    Provable L T (imp (imp A B) (imp (imp B C) (imp A C))) :=
  imp_swap L T (imp_mono_right L T A B C)

theorem imp_mp (L : Nat) (T : Nat → Nat) (A B : Nat) :
    Provable L T (imp A (imp (imp A B) B)) :=
  imp_swap L T (imp_refl L T (imp A B))

theorem imp_imp_right (L : Nat) (T : Nat → Nat) (C G X : Nat) :
    Provable L T (imp (imp C G) (imp C (imp X G))) :=
  imp_mono_right_of_provable L T (implication L T G X)

theorem imp_distrib (L : Nat) (T : Nat → Nat) (U V W X : Nat) :
    Provable L T (imp (imp U (imp V W))
      (imp (imp X U) (imp (imp X V) (imp X W)))) :=
  imp_trans_of_provable L T (imp_mono_right L T X U (imp V W))
    (imp_mono_right_of_provable L T (implicationDistribution L T X V W))

theorem imp_trans_under (L : Nat) (T : Nat → Nat) (P X Q R : Nat) :
    Provable L T (imp (imp P (imp X Q)) (imp (imp Q R) (imp P (imp X R)))) :=
  imp_swap L T (imp_trans_of_provable L T (imp_mono_right L T X Q R)
    (imp_mono_right L T P (imp X Q) (imp X R)))

/-- Compose two implications under a shared assumption. -/
theorem imp_trans_under_of_provable (L : Nat) (T : Nat → Nat) {E A B C : Nat} :
    Provable L T (imp E (imp A B)) → Provable L T (imp E (imp B C)) →
      Provable L T (imp E (imp A C)) :=
  fun h k => mp_under L T
    (mp_under L T (imp_of_provable L T (imp_trans L T A B C)) h) k

theorem falsum_imp (L : Nat) (T : Nat → Nat) (A : Nat) :
    Provable L T (imp falsum A) :=
  mp L T _ _ (contraposition L T A falsum) (imp_of_provable L T (imp_refl L T falsum))

theorem neg_neg_elim (L : Nat) (T : Nat → Nat) (A : Nat) :
    Provable L T (imp (neg (neg A)) A) :=
  mp L T _ _ (contraposition L T A (neg (neg A)))
    (imp_mp L T (neg A) falsum)

theorem imp_contrapos (L : Nat) (T : Nat → Nat) (A B : Nat) :
    Provable L T (imp (imp A B) (imp (neg B) (neg A))) :=
  imp_swap L T (imp_mono_right L T A B falsum)

theorem imp_neg_swap (L : Nat) (T : Nat → Nat) (A B : Nat) :
    Provable L T (imp (imp A (neg B)) (imp B (neg A))) := by
  have flip := mp L T _ _
    (imp_swap L T (imp_mono_right L T B (imp A B) (neg A)))
    (implication L T B A)
  exact imp_trans_of_provable L T (implicationDistribution L T A B falsum) flip

theorem conj_intro (L : Nat) (T : Nat → Nat) (A B : Nat) :
    Provable L T (imp A (imp B (conj A B))) := by
  -- Given B, a proof of ¬B from A → ¬B contradicts that implication.
  have contradiction := imp_trans_of_provable L T (imp_mp L T B falsum)
    (imp_mono_right L T (imp A (neg B)) (neg B) falsum)
  exact imp_trans_of_provable L T (imp_mp L T A (neg B)) (imp_swap L T contradiction)

theorem conj_left (L : Nat) (T : Nat → Nat) (A B : Nat) :
    Provable L T (imp (conj A B) A) := by
  have deny := imp_trans_of_provable L T (imp_mono_right_of_provable L T (falsum_imp L T (neg B)))
    (imp_mp L T (imp A (neg B)) falsum)
  exact mp L T _ _ (contraposition L T A (conj A B)) deny

theorem conj_right (L : Nat) (T : Nat → Nat) (A B : Nat) :
    Provable L T (imp (conj A B) B) := by
  have deny := imp_trans_of_provable L T (implication L T (neg B) A)
    (imp_mp L T (imp A (neg B)) falsum)
  exact mp L T _ _ (contraposition L T B (conj A B)) deny

/-- Assemble two conclusions under a shared assumption. -/
theorem conj_intro_under (L : Nat) (T : Nat → Nat) {E A B : Nat} :
    Provable L T (imp E A) → Provable L T (imp E B) →
      Provable L T (imp E (conj A B)) :=
  fun h k => mp_under L T (imp_trans_of_provable L T h (conj_intro L T A B)) k

theorem imp_curry (L : Nat) (T : Nat → Nat) (G A B : Nat) :
    Provable L T (imp (imp (conj G A) B) (imp G (imp A B))) :=
  mp L T _ _ (imp_trans_under L T G A (conj G A) B) (conj_intro L T G A)

theorem imp_uncurry (L : Nat) (T : Nat → Nat) (G A B : Nat) :
    Provable L T (imp (imp G (imp A B)) (imp (conj G A) B)) := by
  have hleft := mp_under L T (imp_distrib L T G A B (conj G A))
    (imp_of_provable L T (conj_left L T G A))
  exact mp_under L T hleft (imp_of_provable L T (conj_right L T G A))

theorem disj_intro_left (L : Nat) (T : Nat → Nat) (A B : Nat) :
    Provable L T (imp A (disj A B)) :=
  imp_trans_of_provable L T (imp_mp L T A falsum)
    (imp_mono_right_of_provable L T (falsum_imp L T B))

theorem disj_intro_right (L : Nat) (T : Nat → Nat) (A B : Nat) :
    Provable L T (imp B (disj A B)) :=
  implication L T B (neg A)

/-- Reason by cases while keeping a shared assumption. -/
theorem disj_elim_under (L : Nat) (T : Nat → Nat) {E A B C : Nat} :
    Provable L T (imp E (disj A B)) →
      Provable L T (imp E (imp A C)) → Provable L T (imp E (imp B C)) →
        Provable L T (imp E C) := by
  intro hcases hleft hright
  -- If C were false, both branches would be false; the disjunction then gives B.
  have denyA := imp_trans_of_provable L T hleft (imp_contrapos L T A C)
  have denyB := imp_trans_of_provable L T hright (imp_contrapos L T B C)
  have obtainB := imp_trans_under_of_provable L T denyA hcases
  have contradiction := mp_under L T
    (imp_trans_of_provable L T denyB (implicationDistribution L T (neg C) B falsum)) obtainB
  exact imp_trans_of_provable L T contradiction (neg_neg_elim L T C)

theorem disj_elim (L : Nat) (T : Nat → Nat) (A B C : Nat) :
    Provable L T (imp (disj A B) (imp (imp A C) (imp (imp B C) C))) := by
  -- Collect the three premises in one conjunction, then curry the result.
  let branches := conj (imp A C) (imp B C)
  have hleft := imp_trans_of_provable L T (conj_right L T (disj A B) branches)
    (conj_left L T (imp A C) (imp B C))
  have hright := imp_trans_of_provable L T (conj_right L T (disj A B) branches)
    (conj_right L T (imp A C) (imp B C))
  have conclusion := disj_elim_under L T (conj_left L T (disj A B) branches) hleft hright
  have curried := mp L T _ _ (imp_curry L T (disj A B) branches C) conclusion
  exact imp_trans_of_provable L T curried (imp_curry L T (imp A C) (imp B C) C)

extract_witness imp_refl imp_trans imp_imp_right imp_distrib imp_trans_under
  imp_trans_under_of_provable falsum_imp neg_neg_elim imp_contrapos imp_neg_swap conj_intro
  conj_left conj_right conj_intro_under imp_curry disj_intro_left disj_elim_under disj_elim

end FOL.Provable

end
