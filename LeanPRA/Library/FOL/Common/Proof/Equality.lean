module

public import LeanPRA.Library.FOL.Common.Proof.Propositional

/-!
# Derived equality rules

These PRA proofs transport equality and equivalence through formula constructors for arbitrary
numerical language and theory parameters. The proofs first establish each direction under a
shared assumption, then assemble the resulting equivalence.

- `FOL.Provable.equal_congr_under` transports equality formulas along equal terms.
- `FOL.Provable.imp_congr_under` transports implications along equivalent formulas.
- `FOL.Provable.all_congr_under` transports universal formulas along pointwise equivalences.

Numerical witnesses and their checked specifications are extracted after the proofs.
-/

@[expose] public section

pra

namespace FOL.Provable

open Formula

/-- Open a shifted universal formula at the new variable. -/
theorem shift_all_imp (L : Nat) (T : Nat → Nat) (A : Nat) :
    Provable L T (imp (shift L (all A)) A) := by
  have hinst := instantiate L T (subst (FOL.liftSubst (FOL.shiftSubst L 1) L 1) L A)
    (Term.var L 0)
  rw [instantiate_lifted, ← shift_all] at hinst
  exact hinst

/-- Universal quantification preserves a proved implication. -/
theorem all_mono (L : Nat) (T : Nat → Nat) {A B : Nat} :
    Provable L T (imp A B) → Provable L T (imp (all A) (all B)) := by
  intro h
  have body := imp_trans_of_provable L T (shift_all_imp L T A) h
  exact mp L T _ _ (quantifierImplication L T (all A) B) (gen L T _ body)

/-- Universal quantification distributes over implication. -/
theorem all_imp (L : Nat) (T : Nat → Nat) (A B : Nat) :
    Provable L T (imp (all (imp A B)) (imp (all A) (all B))) := by
  have body := mp_under L T
    (imp_trans_of_provable L T (shift_all_imp L T (imp A B))
      (imp_mono_right L T (shift L (all A)) A B))
    (imp_of_provable L T (shift_all_imp L T A))
  have quantified := mp L T _ _
    (quantifierImplication L T (all (imp A B)) (imp (shift L (all A)) B))
    (gen L T _ body)
  exact imp_trans_of_provable L T quantified (quantifierImplication L T (all A) B)

theorem equal_refl_under (L : Nat) (T : Nat → Nat) (E t : Nat) :
    Provable L T (imp E (equal L t t)) :=
  imp_of_provable L T (reflexivity L T t)

theorem iff_refl_under (L : Nat) (T : Nat → Nat) (E A : Nat) :
    Provable L T (imp E (conj (imp A A) (imp A A))) :=
  conj_intro_under L T (imp_of_provable L T (imp_refl L T A)) (imp_of_provable L T (imp_refl L T A))

theorem imp_mp_trans_under (L : Nat) (T : Nat → Nat) (E A B C : Nat) :
    Provable L T (imp (imp (imp E B) (imp E C))
      (imp (imp E A) (imp (imp E (imp A B)) (imp E C)))) :=
  imp_swap L T (imp_trans_of_provable L T (imp_swap L T (implicationDistribution L T E A B))
    (imp_trans L T (imp E (imp A B)) (imp E B) (imp E C)))

theorem equal_symm_under (L : Nat) (T : Nat → Nat) (E a b : Nat) :
    Provable L T (imp (imp E (equal L a b)) (imp E (equal L b a))) :=
  imp_mono_right_of_provable L T (symmetry L T a b)

theorem iff_intro_under (L : Nat) (T : Nat → Nat) (E A B : Nat) :
    Provable L T (imp (imp E (imp A B))
      (imp (imp E (imp B A)) (imp E (conj (imp A B) (imp B A))))) :=
  mp L T _ _ (imp_distrib L T (imp A B) (imp B A) (conj (imp A B) (imp B A)) E)
    (conj_intro L T (imp A B) (imp B A))

/-- Transport one direction of an equality using two equalities under a shared assumption. -/
theorem equal_imp_of_equal_under (L : Nat) (T : Nat → Nat) {E a b c d : Nat} :
    Provable L T (imp E (equal L a c)) → Provable L T (imp E (equal L b d)) →
      Provable L T (imp E (imp (equal L a b) (equal L c d))) := by
  intro hac hbd
  have hca := imp_trans_of_provable L T hac (symmetry L T a c)
  have toCB := imp_trans_of_provable L T hca (transitivity L T c a b)
  have toCD := imp_trans_of_provable L T hbd (imp_swap L T (transitivity L T c b d))
  exact imp_trans_under_of_provable L T toCB toCD

/-- Equal terms give equivalent equality formulas under a shared assumption. -/
theorem equal_congr_under (L : Nat) (T : Nat → Nat) (E a b c d : Nat) :
    Provable L T (imp (imp E (equal L a c)) (imp (imp E (equal L b d))
      (imp E (conj (imp (equal L a b) (equal L c d))
        (imp (equal L c d) (equal L a b)))))) := by
  let premises := conj (imp E (equal L a c)) (imp E (equal L b d))
  have hE := conj_right L T premises E
  have hac := mp_under L T
    (imp_trans_of_provable L T (conj_left L T premises E)
      (conj_left L T (imp E (equal L a c)) (imp E (equal L b d)))) hE
  have hbd := mp_under L T
    (imp_trans_of_provable L T (conj_left L T premises E)
      (conj_right L T (imp E (equal L a c)) (imp E (equal L b d)))) hE
  have forward := equal_imp_of_equal_under L T hac hbd
  have backward := equal_imp_of_equal_under L T
    (imp_trans_of_provable L T hac (symmetry L T a c))
    (imp_trans_of_provable L T hbd (symmetry L T b d))
  have equivalent := conj_intro_under L T forward backward
  -- Discharge E, then separate the two equality premises.
  have conditional := mp L T _ _ (imp_curry L T premises E _) equivalent
  exact mp L T _ _ (imp_curry L T (imp E (equal L a c)) (imp E (equal L b d)) _) conditional

/-- Transport an implication backwards in its premise and forwards in its conclusion. -/
theorem imp_mono_under (L : Nat) (T : Nat → Nat) {E A B C D : Nat} :
    Provable L T (imp E (imp C A)) → Provable L T (imp E (imp B D)) →
      Provable L T (imp E (imp (imp A B) (imp C D))) := by
  intro hca hbd
  have toB := imp_trans_of_provable L T hca (imp_trans L T C A B)
  have toD := imp_trans_of_provable L T hbd (imp_mono_right L T C B D)
  exact imp_trans_under_of_provable L T toB toD

/-- Equivalence of both operands gives equivalence of implications. -/
theorem imp_congr_under (L : Nat) (T : Nat → Nat) (E A B C D : Nat) :
    Provable L T (imp (imp E (conj (imp A C) (imp C A)))
      (imp (imp E (conj (imp B D) (imp D B)))
        (imp E (conj (imp (imp A B) (imp C D)) (imp (imp C D) (imp A B)))))) := by
  let premises := conj (imp E (conj (imp A C) (imp C A))) (imp E (conj (imp B D) (imp D B)))
  have hE := conj_right L T premises E
  have hac := mp_under L T
    (imp_trans_of_provable L T (conj_left L T premises E)
      (conj_left L T (imp E (conj (imp A C) (imp C A)))
        (imp E (conj (imp B D) (imp D B))))) hE
  have hbd := mp_under L T
    (imp_trans_of_provable L T (conj_left L T premises E)
      (conj_right L T (imp E (conj (imp A C) (imp C A)))
        (imp E (conj (imp B D) (imp D B))))) hE
  have forward := imp_mono_under L T
    (imp_trans_of_provable L T hac (conj_right L T (imp A C) (imp C A)))
    (imp_trans_of_provable L T hbd (conj_left L T (imp B D) (imp D B)))
  have backward := imp_mono_under L T
    (imp_trans_of_provable L T hac (conj_left L T (imp A C) (imp C A)))
    (imp_trans_of_provable L T hbd (conj_right L T (imp B D) (imp D B)))
  have equivalent := conj_intro_under L T forward backward
  have conditional := mp L T _ _ (imp_curry L T premises E _) equivalent
  exact mp L T _ _ (imp_curry L T (imp E (conj (imp A C) (imp C A)))
    (imp E (conj (imp B D) (imp D B))) _) conditional

/-- Pointwise equivalence gives equivalence of universal formulas. The assumption is shifted
under the quantifier so that the quantified variable is fresh for it. -/
theorem all_congr_under (L : Nat) (T : Nat → Nat) (E A B : Nat) :
    Provable L T (imp
      (all (imp (subst (FOL.shiftSubst L 1) L E) (conj (imp A B) (imp B A))))
      (imp E (conj (imp (all A) (all B)) (imp (all B) (all A))))) := by
  rw [← shift_eq_subst L E]
  have forward := imp_trans_of_provable L T
    (all_mono L T (conj_left L T (imp A B) (imp B A))) (all_imp L T A B)
  have backward := imp_trans_of_provable L T
    (all_mono L T (conj_right L T (imp A B) (imp B A))) (all_imp L T B A)
  have equivalent := conj_intro_under L T forward backward
  exact imp_trans_of_provable L T (quantifierImplication L T E (conj (imp A B) (imp B A)))
    (imp_mono_right_of_provable L T equivalent)

extract_witness equal_refl_under iff_refl_under imp_mp_trans_under equal_symm_under
  iff_intro_under equal_congr_under imp_congr_under all_congr_under

end FOL.Provable

end
