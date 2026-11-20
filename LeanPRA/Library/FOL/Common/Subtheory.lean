module

public import LeanPRA.Library.FOL.Common.Theory

/-!
# Subtheories from proofs of axioms

If every axiom of a theory `T` has a proof in a theory `U`, then every theorem of `T` is a theorem
of `U`. The proof replaces each hypothesis leaf of a `T`-proof by the corresponding `U`-proof.
The replacement proofs are supplied by an explicit numerical function, so the translation of a
proof tree is a numerical function too.

- `isProof_cases` describes the four forms of an accepted proof tree.
- `Proof.replace proof p` replaces every hypothesis leaf with conclusion `A` in the proof tree `p`
  by the tree `proof A`, and keeps the other nodes.
- `isProofOf_replace` shows that the replaced tree is a `U`-proof of the same conclusion.
- `subtheory_of_isProofOf` concludes `Subtheory L T U`.
-/

@[expose] public section

pra

namespace FOL

/-- An accepted proof tree is a logical axiom, a theory axiom, an application of modus ponens to
two accepted trees, or a generalization of an accepted tree. -/
theorem isProof_cases (L : Nat) (T : Nat → Nat) : ∀ p, isProof L T p = 1 →
    (∃ A, p = Proof.axiom A ∧ isLogicalAxiom L A = 1) ∨
    (∃ A, p = Proof.hypothesis A ∧ T A = 1) ∨
    (∃ A q r, p = Proof.mp A q r ∧ isProof L T q = 1 ∧ isProof L T r = 1 ∧
      Proof.conclusion q = Formula.imp (Proof.conclusion r) A) ∨
    (∃ q, p = Proof.gen (Proof.conclusion q) q ∧ isProof L T q = 1) := by
  intro p hp
  have hz : ¬ p = 0 := by
    intro h0
    rw [h0, isProof_zero L T] at hp
    exact zero_ne_succ 0 hp
  have reconstruct :
      S (pair (Proof.rule p) (pair (Proof.conclusion p) (Proof.premises p))) = p := by
    rw [Proof.rule, Proof.conclusion, Proof.premises, pair_unpair, pair_unpair]
    exact succ_pred p hz
  have node := isProof_node_eq L T (Proof.rule p) (Proof.conclusion p) (Proof.premises p)
  rw [reconstruct] at node
  rw [node] at hp
  by_cases h0 : Proof.rule p = 0
  · rw [h0] at hp
    have hp : ite (eqb (Proof.premises p) 0) (isLogicalAxiom L (Proof.conclusion p)) 0 = 1 := hp
    by_cases hc : Proof.premises p = 0
    · rw [hc] at hp
      have hax : isLogicalAxiom L (Proof.conclusion p) = 1 := hp
      left
      exists Proof.conclusion p
      constructor
      · have form : S (pair (Proof.rule p) (pair (Proof.conclusion p) (Proof.premises p))) =
            Proof.axiom (Proof.conclusion p) := by
          rw [h0, hc]
          rfl
        exact eq_trans (eq_symm reconstruct) form
      · exact hax
    · rw [and_right (eqb_eq_zero (Proof.premises p) 0) hc] at hp
      exact false_elim (zero_ne_succ 0 hp)
  rw [and_right (eqb_eq_zero (Proof.rule p) 0) h0] at hp
  by_cases h1 : Proof.rule p = 1
  · rw [h1] at hp
    have hp : ite (eqb (Proof.premises p) 0) (eqb (T (Proof.conclusion p)) 1) 0 = 1 := hp
    by_cases hc : Proof.premises p = 0
    · rw [hc] at hp
      have ht : eqb (T (Proof.conclusion p)) 1 = 1 := hp
      right
      left
      exists Proof.conclusion p
      constructor
      · have form : S (pair (Proof.rule p) (pair (Proof.conclusion p) (Proof.premises p))) =
            Proof.hypothesis (Proof.conclusion p) := by
          rw [h1, hc]
          rfl
        exact eq_trans (eq_symm reconstruct) form
      · exact and_left (eqb_eq_one _ _) ht
    · rw [and_right (eqb_eq_zero (Proof.premises p) 0) hc] at hp
      exact false_elim (zero_ne_succ 0 hp)
  rw [and_right (eqb_eq_zero (Proof.rule p) 1) h1] at hp
  by_cases h2 : Proof.rule p = 2
  · rw [h2] at hp
    let q := unpairLeft (Proof.premises p)
    let r := unpairRight (Proof.premises p)
    have hp : band (band (isProof L T q) (isProof L T r))
        (eqb (Proof.conclusion q) (Formula.imp (Proof.conclusion r) (Proof.conclusion p))) = 1 :=
      hp
    have parts := and_left (band_eq_one _ _) hp
    have both := and_left (band_eq_one _ _)
      (and_right (bool_eq_one _ (band_bool _ _)) (and_left parts))
    right
    right
    left
    exists Proof.conclusion p
    exists q
    exists r
    have form : S (pair (Proof.rule p) (pair (Proof.conclusion p) (Proof.premises p))) =
        Proof.mp (Proof.conclusion p) q r := by
      rw [h2, Proof.mp, pair_unpair]
    exact (eq_trans (eq_symm reconstruct) form,
      and_right (bool_eq_one _ (isProof_bool L T q)) (and_left both),
      and_right (bool_eq_one _ (isProof_bool L T r)) (and_right both),
      and_left (eqb_ne_zero _ _) (and_right parts))
  rw [and_right (eqb_eq_zero (Proof.rule p) 2) h2] at hp
  by_cases h3 : Proof.rule p = 3
  · rw [h3] at hp
    let q := Proof.premises p
    have hp : band (isProof L T q)
        (eqb (Proof.conclusion p) (Formula.all (Proof.conclusion q))) = 1 := hp
    have parts := and_left (band_eq_one _ _) hp
    have he := and_left (eqb_ne_zero _ _) (and_right parts)
    right
    right
    right
    exists q
    have form : S (pair (Proof.rule p) (pair (Proof.conclusion p) (Proof.premises p))) =
        Proof.gen (Proof.conclusion q) q := by
      rw [h3, he]
      rfl
    exact (eq_trans (eq_symm reconstruct) form,
      and_right (bool_eq_one _ (isProof_bool L T q)) (and_left parts))
  rw [and_right (eqb_eq_zero (Proof.rule p) 3) h3] at hp
  exact false_elim (zero_ne_succ 0 hp)

namespace Proof

/-- `replace proof p` replaces every hypothesis leaf with conclusion `A` in the proof tree `p` by
the tree `proof A`, and rebuilds the logical axioms, modus ponens, and generalization nodes with
their conclusions unchanged. -/
def replace (proof : Nat → Nat) : Nat → Nat :=
  rec «axiom» proof (fun A p q x y => mp A x y) (fun A p x => gen (conclusion p) x)

theorem replace_axiom (proof : Nat → Nat) : ∀ A, replace proof («axiom» A) = «axiom» A :=
  rec_axiom «axiom» proof (fun A p q x y => mp A x y) (fun A p x => gen (conclusion p) x)

theorem replace_hypothesis (proof : Nat → Nat) : ∀ A, replace proof (hypothesis A) = proof A :=
  rec_hypothesis «axiom» proof (fun A p q x y => mp A x y) (fun A p x => gen (conclusion p) x)

theorem replace_mp (proof : Nat → Nat) : ∀ A p q,
    replace proof (mp A p q) = mp A (replace proof p) (replace proof q) :=
  rec_mp «axiom» proof (fun A p q x y => mp A x y) (fun A p x => gen (conclusion p) x)

theorem replace_gen (proof : Nat → Nat) : ∀ A p,
    replace proof (gen A p) = gen (conclusion p) (replace proof p) :=
  rec_gen «axiom» proof (fun A p q x y => mp A x y) (fun A p x => gen (conclusion p) x)

end Proof

/-- If `proof A` is a `U`-proof of every axiom `A` of `T`, then replacing the hypothesis leaves of
a `T`-proof gives a `U`-proof of the same conclusion. -/
theorem isProofOf_replace (L : Nat) (T U proof : Nat → Nat) :
    (∀ A, T A = 1 → IsProofOf L U A (proof A)) →
    ∀ p, isProof L T p = 1 → IsProofOf L U (Proof.conclusion p) (Proof.replace proof p) := by
  intro supplied
  have invariant : ∀ p,
      ite (isProof L T p)
        (pair (isProof L U (Proof.replace proof p)) (Proof.conclusion (Proof.replace proof p)))
        (pair 1 (Proof.conclusion p)) = pair 1 (Proof.conclusion p) := by
    apply strong_induction_eq
      (fun p => ite (isProof L T p)
        (pair (isProof L U (Proof.replace proof p)) (Proof.conclusion (Proof.replace proof p)))
        (pair 1 (Proof.conclusion p)))
      (fun p => pair 1 (Proof.conclusion p))
    intro p ih
    have earlier : ∀ q, q < p → isProof L T q = 1 →
        IsProofOf L U (Proof.conclusion q) (Proof.replace proof q) := by
      intro q hq valid
      have h : ite (isProof L T q)
          (pair (isProof L U (Proof.replace proof q)) (Proof.conclusion (Proof.replace proof q)))
          (pair 1 (Proof.conclusion q)) = pair 1 (Proof.conclusion q) := ih q hq
      rw [valid] at h
      exact pair_injective _ _ _ _ h
    change ite (isProof L T p)
        (pair (isProof L U (Proof.replace proof p)) (Proof.conclusion (Proof.replace proof p)))
        (pair 1 (Proof.conclusion p)) = pair 1 (Proof.conclusion p)
    by_cases hv : isProof L T p = 0
    · rw [hv]
      rfl
    have valid := and_right (bool_eq_one _ (isProof_bool L T p)) hv
    have result : IsProofOf L U (Proof.conclusion p) (Proof.replace proof p) := by
      rcases isProof_cases L T p valid with ha | hh | hm | hg
      · rcases ha with (A, hpe, hax)
        rw [hpe, Proof.replace_axiom proof A, Proof.conclusion_axiom A]
        exact (isProof_axiom L U A hax, Proof.conclusion_axiom A)
      · rcases hh with (A, hpe, ht)
        rw [hpe, Proof.replace_hypothesis proof A, Proof.conclusion_hypothesis A]
        exact supplied A ht
      · rcases hm with (A, q, r, hpe, hq, hr, hc)
        have hql : q < p := by
          rw [hpe]
          exact Proof.left_lt_mp A q r
        have hrl : r < p := by
          rw [hpe]
          exact Proof.right_lt_mp A q r
        have pq := earlier q hql hq
        have pr := earlier r hrl hr
        rw [hc] at pq
        rw [hpe, Proof.replace_mp proof A q r, Proof.conclusion_mp A q r]
        exact IsProofOf.mp L U (Proof.conclusion r) A (Proof.replace proof q)
          (Proof.replace proof r) pq pr
      · rcases hg with (q, hpe, hq)
        have hql : q < p := by
          rw [hpe]
          exact Proof.premise_lt_gen (Proof.conclusion q) q
        have pq := earlier q hql hq
        rw [hpe, Proof.replace_gen proof (Proof.conclusion q) q,
          Proof.conclusion_gen (Proof.conclusion q) q]
        exact IsProofOf.gen L U (Proof.conclusion q) (Proof.replace proof q) pq
    rw [ite_of_ne_zero _ _ _ hv, and_left result, and_right result]
  intro p valid
  have h := invariant p
  rw [valid] at h
  exact pair_injective _ _ _ _ h

/-- A theory whose axioms all have explicit proofs in `U` is a subtheory of `U`. -/
theorem subtheory_of_isProofOf (L : Nat) (T U proof : Nat → Nat) :
    (∀ A, T A = 1 → IsProofOf L U A (proof A)) → Subtheory L T U := by
  intro supplied A provable
  rcases provable with (p, valid, conclusion)
  have h := isProofOf_replace L T U proof supplied p valid
  rw [conclusion] at h
  exact (Proof.replace proof p, h)

end FOL

end
