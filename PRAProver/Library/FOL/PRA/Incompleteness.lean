module

public import PRAProver.Library.FOL.PRA.Provability.D1
public import PRAProver.Library.FOL.PRA.Provability.D2
public import PRAProver.Library.FOL.PRA.Provability.D3

/-!
# Gödel's second incompleteness in first-order PRA

- `FOL.PRA.diagonal` and `FOL.PRA.diagonal_lemma`: diagonal lemma.
- `FOL.PRA.goedel`: Gödel's sentence.
- `FOL.PRA.con_unprovable`: Gödel's second incompleteness for PRA.
-/

pra

namespace FOL.PRA

fol_def diagonalStep over PRA (p : formula of 1) : Nat → formula :=
  fun e => p(eval[e](${num e}))

derive_primrec diagonalStep

/-- The fixed point of the one-variable formula `p`. -/
fol_def diagonal over PRA : formula of 1 → formula := fun p =>
  ${diagonalStep p (diagonalStep.code p)}

/-- PRA proves that the fixed point is equivalent to `p` applied to its code. -/
fol_theorem diagonal_lemma (p : formula of 1) : PRA ⊢
    (diagonal p) ↔ p(${num (diagonal p)}) := by
  let e := diagonalStep.code p
  have h := eval_num_of_evaluates e e (diagonal p) (diagonalStep.trace p e)
    (diagonalStep.computedBy p e)
  prw [← h]
  pconstructor
  · passumption
  · passumption

/-- Gödel's sentence of PRA. -/
fol_def goedel over PRA : formula :=
  (diagonal (fun x => ¬ (pr language isAxiom.code x)))

theorem goedel_iff : PRA ⊢ goedel ↔ ¬ (pr language isAxiom.code ${num goedel}) := by
  pexact diagonal_lemma (fun x => ¬ (pr language isAxiom.code x))

theorem goedel_imp : PRA ⊢ goedel → ¬ (pr language isAxiom.code ${num goedel}) := by
  prw [← goedel_iff]
  passumption

theorem goedel_unprovable : Consistent language isAxiom → ¬ (PRA ⊢ goedel) := by
  intro h₁ h₂
  apply h₁
  papply goedel_imp
  · pexact h₂
  · exact pr_of_provable _ _ _ _ isAxiom.computedBy _ h₂

theorem goedel_iff_con : PRA ⊢ goedel ↔ con language isAxiom.code := by
  pconstructor
  · pintro h₁ h₂
    prw [goedel_iff] at h₁
    papply h₁
    papply (pr_mp_num language isAxiom.code Formula.falsum goedel)
    · pexact pr_of_provable _ _ _ _ isAxiom.computedBy _
        (Provable.falsum_imp language isAxiom goedel)
    · pexact h₂
  · prw [goedel_iff]
    pintro h₁ h₂
    papply h₁
    papply pr_mp_num language isAxiom.code
      (pr language isAxiom.code (num goedel)) Formula.falsum
    · papply (pr_mp_num language isAxiom.code goedel
        (fol_formula[PRA | ¬ (pr language isAxiom.code ${num goedel})]))
      · pexact pr_of_provable _ _ _ _ isAxiom.computedBy _ goedel_imp
      · pexact h₂
    · papply pr_pr_num language isAxiom.code goedel
      pexact h₂

/-- **Gödel's second incompleteness theorem** for PRA: assuming PRA is consistent, it can not prove
its own consistency `con_PRA`. -/
theorem con_unprovable : Consistent language isAxiom → ¬ (PRA ⊢ con language isAxiom.code) := by
  intro h₁ h₂
  apply goedel_unprovable h₁
  prw [goedel_iff_con]
  exact h₂

end FOL.PRA

end
