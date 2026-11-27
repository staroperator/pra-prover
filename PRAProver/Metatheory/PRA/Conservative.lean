module

public import PRAProver.Metatheory.PRA.Witness

/-!
# Conservativity of first-order PRA over quantifier-free PRA

`proof_iff_qfProof` shows that first-order PRA is conservative over quantifier-free PRA: for any
quantifier-free formula `A`, `Proof A.toFormula` holds if and only if `QFProof A` holds.

The forward direction introduces a vacuous existential quantifier and extracts a witness via
`exists_primrec_witness`; the reverse direction embeds the quantifier-free derivation via
`QFProof.toProof`.
-/

namespace PRA

private theorem fo_to_qf {A : QFFormula n} (h : Proof A.toFormula) : QFProof A := by
  have h₀ : Proof (A.shift.toFormula.inst 0) := by
    rw [Formula.inst, ← QFFormula.toFormula_subst]
    change Proof ((A.shift.inst 0).toFormula)
    rw [QFFormula.inst_shift]
    exact h
  have he : Proof (.ex A.shift.toFormula) := .mp (.exists_intro (t := 0)) h₀
  obtain ⟨f, hf⟩ := exists_primrec_witness he
  simpa only [QFFormula.inst_shift] using hf

/-- First-order PRA proves an embedded quantifier-free formula if and only if quantifier-free
PRA proves it. -/
public theorem proof_iff_qfProof {A : QFFormula n} : Proof A.toFormula ↔ QFProof A :=
  ⟨fo_to_qf, QFProof.toProof⟩

end PRA
