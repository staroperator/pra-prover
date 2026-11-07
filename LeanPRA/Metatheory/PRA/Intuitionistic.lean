module

public import LeanPRA.Metatheory.PRA.Basic

/-!
# Classical and intuitionistic quantifier-free PRA

`qfProofI_iff_qfProof` shows that intuitionistic and classical quantifier-free PRA prove the same
formulas. The proof derives `(s ≡ t) ⊔ ∼ (s ≡ t)` in `QFProofI` by quantifier-free induction on
terms, extends excluded middle to all quantifier-free formulas via `QFProofI.formula_decidable`,
and derives the classical contraposition axiom `imp_contra`.
-/

namespace PRA

open QFFormula
open Term (pred sub)

variable {n : Nat}

namespace Intuitionistic

open QFProofI

variable {φ ψ χ θ : QFFormula n}

private def decEq (s t : Term n) : QFFormula n := (s ≡ t) ⊔ ∼ (s ≡ t)

private theorem decEq_congr_under {s s' t t' : Term n}
    (h₁ : QFProofI (φ ⇒ s ≡ s')) (h₂ : QFProofI (φ ⇒ t ≡ t')) :
    QFProofI (φ ⇒ decEq s t ⇒ decEq s' t') := by
  have hf := eq_congr_under h₁ h₂
  have hb := eq_congr_under (imp_trans_rule h₁ eq_symm) (imp_trans_rule h₂ eq_symm)
  exact mp_under (imp_trans_rule (imp_trans_under hf (weaken or_left)) or_elim)
    (imp_trans_under (imp_trans_rule hb imp_trans) (weaken or_right))

private theorem decEq_congr {s s' t t' : Term n}
    (h₁ : QFProofI (s ≡ s')) (h₂ : QFProofI (t ≡ t')) :
    QFProofI (decEq s t ⇒ decEq s' t') :=
  mp (decEq_congr_under (φ := ⊤) (weaken h₁) (weaken h₂)) imp_refl

private theorem decEq_zero (t : Term n) : QFProofI (decEq t 0) := by
  apply cases_rule (zero_or_succ t) or_left
  apply imp_trans_rule _ or_right
  exact imp_trans_under (imp_trans_rule eq_symm eq_trans) (weaken (succ_ne_zero (t := pred t)))

private theorem decEq_zero_left (t : Term n) : QFProofI (decEq 0 t) := by
  apply cases_rule (decEq_zero t)
  · exact imp_trans_rule eq_symm or_left
  · exact imp_trans_rule (contrapose eq_symm) or_right

private theorem decEq_succ (s t : Term n) :
    QFProofI (decEq s t ⇒ decEq s.succ t.succ) :=
  mp (mp or_elim (imp_trans_rule (unary_congr_under imp_refl) or_left))
    (imp_trans_rule (contrapose succ_inj) or_right)

private theorem decEq_of_zero_left (s t : Term n) :
    QFProofI (s ≡ 0 ⇒ decEq s t) :=
  mp_under (decEq_congr_under (imp_trans_rule imp_refl eq_symm) (weaken eq_refl))
    (weaken (decEq_zero_left t))

private theorem decEq_of_zero_right (s t : Term n) :
    QFProofI (t ≡ 0 ⇒ decEq s t) :=
  mp_under (decEq_congr_under (weaken eq_refl) (imp_trans_rule imp_refl eq_symm))
    (weaken (decEq_zero s))

private theorem decEq_pred (s t : Term n) :
    QFProofI (decEq (pred s) (pred t) ⇒ decEq s t) := by
  apply cases_rule (zero_or_succ s)
  · exact imp_trans_rule (decEq_of_zero_left s t) imp_imp_self
  · apply cases_under (zero_or_succ t)
    · exact weaken (imp_trans_rule (decEq_of_zero_right s t) imp_imp_self)
    · apply and_curry
      exact imp_trans_under (weaken (decEq_succ (pred s) (pred t)))
        (decEq_congr_under (imp_trans_rule and_left eq_symm) (imp_trans_rule and_right eq_symm))

-- Subtract the induction variable from both sides, then recover the original decision.
private theorem decEq_sub (s t u : Term n) :
    QFProofI (decEq (sub s u) (sub t u) ⇒ decEq s t) := by
  have h : QFProofI (decEq (sub (.var 1 : Term 3) (.var 0))
      (sub (.var 2) (.var 0)) ⇒ decEq (.var 1) (.var 2)) := by
    apply induction <;>
      simp only [QFFormula.inst, QFFormula.replace, QFFormula.subst, decEq, QFFormula.neg,
        sub, Term.subst_app₂, Term.subst, Fin.cases_zero]
    · exact decEq_congr (sub_zero _) (sub_zero _)
    · have hstep : QFProofI (decEq (sub (.var 1 : Term 3) (.var 0 : Term 3).succ)
          (sub (.var 2) (.var 0 : Term 3).succ) ⇒
          decEq (sub (.var 1) (.var 0)) (sub (.var 2) (.var 0))) :=
        imp_trans_rule (decEq_congr (sub_succ _ _) (sub_succ _ _)) (decEq_pred _ _)
      exact mp imp_trans hstep
  simpa only [QFFormula.subst, decEq, QFFormula.neg, sub, Term.subst_app₂, Term.subst,
    Fin.cases_two, Fin.cases_one, Fin.cases_zero] using
    (QFProofI.subst (v := (Fin.cases u (Fin.cases s (Fin.cases t Fin.elim0)))) h)

private theorem equality_decidable (s t : Term n) : QFProofI (decEq s t) :=
  mp (decEq_sub s t s)
    (mp (decEq_congr (eq_symm_rule (sub_self s)) eq_refl) (decEq_zero_left (sub t s)))

private theorem to_intuitionistic
    (heq : ∀ {n} (s t : Term n), QFProofI ((s ≡ t) ⊔ ∼ (s ≡ t)))
    (h : QFProof φ) : QFProofI φ := by
  induction h with
  | imp_imp_self => exact .imp_imp_self
  | imp_distrib => exact .imp_distrib
  | imp_contra => exact contra (formula_decidable heq _)
  | and_intro => exact .and_intro
  | and_left => exact .and_left
  | and_right => exact .and_right
  | or_left => exact .or_left
  | or_right => exact .or_right
  | or_elim => exact .or_elim
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | eq_refl => exact .eq_refl
  | eq_symm => exact .eq_symm
  | eq_trans => exact .eq_trans
  | eq_congr_ith => exact .eq_congr_ith
  | succ_ne_zero => exact .succ_ne_zero
  | succ_inj => exact .succ_inj
  | app_proj => exact .app_proj
  | app_comp => exact .app_comp
  | app_prec_zero => exact .app_prec_zero
  | app_prec_succ => exact .app_prec_succ
  | induction _ _ ih₁ ih₂ => exact .induction ih₁ ih₂
  | subst _ ih => exact .subst ih

end Intuitionistic

/-- Classical and intuitionistic quantifier-free PRA prove the same formulas. -/
public theorem qfProofI_iff_qfProof {φ : QFFormula n} : QFProofI φ ↔ QFProof φ :=
  ⟨QFProofI.toQFProof,
    Intuitionistic.to_intuitionistic Intuitionistic.equality_decidable⟩

end PRA
