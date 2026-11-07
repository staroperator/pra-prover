module

public import LeanPRA.Metatheory.PRA.Substitution

/-!
# Basic proof rules and arithmetic in PRA

Derived logical rules, equality congruence, predecessor and subtraction, conditionals, boolean
tests for quantifier-free formulas, and embeddings between the PRA proof systems:

- `QFProofI.imp_trans_rule` and `QFProof.imp_trans_rule`, together with the surrounding
  propositional lemmas, combine derivations under shared assumptions.
- `QFProofI.app_congr_under`, `QFProof.app_congr_under`, and `QFProof.formula_congr_under` prove
  congruence of function applications and quantifier-free formulas under provably equal arguments.
- `QFProofI.app_reindex` evaluates a reindexed primitive recursive expression on an argument tuple.
- `QFProofI.formula_decidable` lifts decidability of atomic equations to all quantifier-free
  formulas.
- `Primrec.pred`, `Primrec.sub`, `Term.pred`, and `Term.sub` define predecessor and truncated
  subtraction, with their defining equations proved in both quantifier-free calculi.
- `Primrec.cond` and `Term.cond` branch on whether a numerical test is zero.
- `QFFormula.test` and `QFProof.test_correct` represent any quantifier-free formula `A` as the
  equation `test A ≡ 0`, and `Term.choose` selects between two terms according to `A`.
- `Term.toPrimrec` and `QFProof.toPrimrec_eq` compile a term to a single primitive recursive
  symbol, and `qf_witness_iff_primrec` converts a term witness into a primitive recursive symbol.
- `Term.recApp`, `QFProof.recApp_zero`, and `QFProof.recApp_succ` provide primitive recursion with
  term bodies.
- `Proof.subst` and `Proof.forall_body` substitute terms into first-order derivations and
  instantiate universal theorems.
- `QFProofI.toQFProof` and `QFProof.toProof` embed intuitionistic into classical quantifier-free
  derivations and classical quantifier-free into first-order derivations.
-/

namespace Primrec

/-- Predecessor, with value zero at zero. -/
@[expose] public def pred : Primrec 1 := prec zero proj₀

/-- Truncated subtraction: the first argument is the minuend and the second is subtracted. -/
@[expose] public def sub : Primrec 2 := swap (prec proj₀ (comp₁ pred proj₁))

end Primrec

namespace PRA.Term

/-- Apply the predecessor symbol to a term. -/
public abbrev pred (t : Term n) : Term n := Term.app₁ Primrec.pred t

/-- Apply truncated subtraction to two terms, in minuend-subtrahend order. -/
public abbrev sub (s t : Term n) : Term n := Term.app₂ Primrec.sub s t

end PRA.Term

namespace PRA.QFProofI

open QFFormula
open Term (pred sub)

variable {n : Nat} {φ ψ χ θ : QFFormula n}

public theorem imp_refl : QFProofI (φ ⇒ φ) :=
  mp (mp imp_distrib (imp_imp_self (φ := φ) (ψ := φ ⇒ φ))) imp_imp_self

public theorem weaken (h : QFProofI ψ) : QFProofI (φ ⇒ ψ) :=
  mp imp_imp_self h

public theorem mp_under (h₁ : QFProofI (φ ⇒ ψ ⇒ χ)) (h₂ : QFProofI (φ ⇒ ψ)) :
    QFProofI (φ ⇒ χ) :=
  mp (mp imp_distrib h₁) h₂

public theorem imp_trans_rule (h₁ : QFProofI (φ ⇒ ψ)) (h₂ : QFProofI (ψ ⇒ χ)) :
    QFProofI (φ ⇒ χ) :=
  mp_under (weaken h₂) h₁

public theorem imp_swap_rule (h : QFProofI (φ ⇒ ψ ⇒ χ)) : QFProofI (ψ ⇒ φ ⇒ χ) :=
  mp_under (weaken (mp imp_distrib h)) imp_imp_self

public theorem imp_trans : QFProofI ((φ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ φ ⇒ χ) :=
  imp_swap_rule (imp_trans_rule imp_imp_self imp_distrib)

public theorem imp_trans_under (h₁ : QFProofI (θ ⇒ φ ⇒ ψ))
    (h₂ : QFProofI (θ ⇒ ψ ⇒ χ)) : QFProofI (θ ⇒ φ ⇒ χ) :=
  mp_under (imp_trans_rule h₁ imp_trans) h₂

public theorem imp_apply : QFProofI (φ ⇒ (φ ⇒ ψ) ⇒ ψ) :=
  imp_swap_rule imp_refl

public theorem cases_rule (h : QFProofI (φ ⊔ ψ)) (h₁ : QFProofI (φ ⇒ χ))
    (h₂ : QFProofI (ψ ⇒ χ)) : QFProofI χ :=
  mp (mp (mp or_elim h₁) h₂) h

public theorem cases_under (h : QFProofI (φ ⊔ ψ)) (h₁ : QFProofI (θ ⇒ φ ⇒ χ))
    (h₂ : QFProofI (θ ⇒ ψ ⇒ χ)) : QFProofI (θ ⇒ χ) :=
  mp_under (mp_under (imp_trans_rule h₁ or_elim) h₂) (weaken h)

public theorem contrapose (h : QFProofI (φ ⇒ ψ)) : QFProofI (∼ ψ ⇒ ∼ φ) :=
  mp imp_trans h

public theorem eq_symm_rule {s t : Term n} (h : QFProofI (s ≡ t)) :
    QFProofI (t ≡ s) := mp eq_symm h

public theorem eq_trans_rule {s t u : Term n} (h₁ : QFProofI (s ≡ t))
    (h₂ : QFProofI (t ≡ u)) : QFProofI (s ≡ u) := mp (mp eq_trans h₁) h₂

public theorem eq_trans_under {s t u : Term n} (h₁ : QFProofI (φ ⇒ s ≡ t))
    (h₂ : QFProofI (φ ⇒ t ≡ u)) : QFProofI (φ ⇒ s ≡ u) :=
  mp_under (imp_trans_rule h₁ eq_trans) h₂

private theorem app_congr_list {m : Nat} [BEq (Fin m)] [LawfulBEq (Fin m)]
    {f : Primrec m} {v w : Fin m → Term n}
    (h : ∀ i, QFProofI (φ ⇒ v i ≡ w i)) (is : List (Fin m)) :
    QFProofI (φ ⇒ Term.app f v ≡ Term.app f (fun i => if i ∈ is then w i else v i)) := by
  induction is with
  | nil => simpa using (weaken (φ := φ) (eq_refl (t := Term.app f v)))
  | cons i is ih =>
    let u : Fin m → Term n := fun j => if j ∈ is then w j else v j
    have hi : QFProofI (φ ⇒ u i ≡ w i) := by
      cases (inferInstance : Decidable (i ∈ is)) with
      | isTrue hm => simpa [u, hm] using (weaken (φ := φ) (eq_refl (t := w i)))
      | isFalse hm => simpa [u, hm] using h i
    have hu : (fun j => if j = i then w i else u j) =
        (fun j => if j ∈ i :: is then w j else v j) := by
      funext j
      cases (inferInstance : Decidable (j = i)) with
      | isTrue hj => subst j; simp
      | isFalse hj => simp [u, hj]
    simpa only [hu] using eq_trans_under ih (imp_trans_rule hi (eq_congr_ith (f := f)))

/-- Pointwise equality of arguments gives equality of applications under a shared antecedent. -/
public theorem app_congr_under {m : Nat} {f : Primrec m} {v w : Fin m → Term n}
    (h : ∀ i, QFProofI (φ ⇒ v i ≡ w i)) :
    QFProofI (φ ⇒ Term.app f v ≡ Term.app f w) := by
  letI : BEq (Fin m) := instBEqOfDecidableEq
  letI : LawfulBEq (Fin m) :=
    { rfl := decide_eq_true rfl, eq_of_beq := of_decide_eq_true }
  simpa only [List.mem_finRange, ite_true] using app_congr_list h (List.finRange m)

/-- Provably equal arguments give provably equal function applications. -/
public theorem app_congr {m : Nat} {f : Primrec m} {v w : Fin m → Term n}
    (h : ∀ i, QFProofI (v i ≡ w i)) : QFProofI (Term.app f v ≡ Term.app f w) :=
  mp (app_congr_under (φ := ⊤) (fun i => weaken (h i))) imp_refl

/-- Applying a reindexed symbol agrees with selecting its arguments through the index map. -/
public theorem app_reindex {k m : Nat} (f : Primrec k) (ρ : Fin k → Fin m)
    (v : Fin m → Term n) :
    QFProofI (Term.app (Primrec.reindex f ρ) v ≡ Term.app f (fun i => v (ρ i))) := by
  exact eq_trans_rule app_comp (app_congr (fun _ => app_proj))

public theorem unary_congr_under {f : Primrec 1} {s t : Term n}
    (h : QFProofI (φ ⇒ s ≡ t)) : QFProofI (φ ⇒ Term.app₁ f s ≡ Term.app₁ f t) := by
  apply app_congr_under
  intro i
  simpa only [Term.app₁, Fin.cases_fin_one] using h

public theorem unary_congr {f : Primrec 1} {s t : Term n}
    (h : QFProofI (s ≡ t)) : QFProofI (Term.app₁ f s ≡ Term.app₁ f t) :=
  mp (unary_congr_under (φ := ⊤) (weaken h)) imp_refl

public theorem eq_congr_under {s s' t t' : Term n} (h₁ : QFProofI (φ ⇒ s ≡ s'))
    (h₂ : QFProofI (φ ⇒ t ≡ t')) : QFProofI (φ ⇒ (s ≡ t) ⇒ s' ≡ t') :=
  imp_trans_under (imp_trans_rule (imp_trans_rule h₁ eq_symm) eq_trans)
    (imp_trans_rule h₂ (imp_swap_rule eq_trans))

public theorem pred_succ (t : Term n) : QFProofI (pred t.succ ≡ t) := by
  have h := app_prec_succ (f := Primrec.zero) (g := Primrec.proj₀)
    (v := Fin.elim0) (t := t)
  simpa only [pred, Term.app₁, Primrec.pred, Fin.cases_zero] using
    eq_trans_rule h (app_proj (i := 0))

private theorem comp_one {k} (f : Primrec 1) (g : Primrec k)
    (v : Fin k → Term n) :
    QFProofI (Term.app (Primrec.comp₁ f g) v ≡ Term.app₁ f (Term.app g v)) := by
  apply eq_trans_rule app_comp
  apply app_congr
  intro i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  exact eq_refl

private abbrev subRec : Primrec 2 :=
  Primrec.prec Primrec.proj₀ (Primrec.comp₁ Primrec.pred Primrec.proj₁)

private theorem sub_eq (s t : Term n) :
    QFProofI (sub s t ≡ Term.app subRec (Fin.cases t (Fin.cases s Fin.elim0))) := by
  apply eq_trans_rule app_comp
  apply app_congr
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
  · exact app_proj
  · exact app_proj

public theorem sub_zero (s : Term n) : QFProofI (sub s 0 ≡ s) :=
  eq_trans_rule (sub_eq s 0) (eq_trans_rule app_prec_zero app_proj)

public theorem sub_succ (s t : Term n) : QFProofI (sub s t.succ ≡ pred (sub s t)) := by
  apply eq_trans_rule (sub_eq s t.succ)
  apply eq_trans_rule app_prec_succ
  apply eq_trans_rule (comp_one _ _ _)
  apply unary_congr
  exact eq_trans_rule app_proj (eq_symm_rule (sub_eq s t))

/-- Every term is zero or the successor of its predecessor, as a formula of QF-IPRA. -/
public theorem zero_or_succ (t : Term n) : QFProofI ((t ≡ 0) ⊔ (t ≡ (pred t).succ)) := by
  have h : QFProofI (((.var 0 : Term 1) ≡ 0) ⊔
      ((.var 0 : Term 1) ≡ (pred (.var 0)).succ)) := by
    apply induction <;>
      simp only [QFFormula.inst, QFFormula.replace, QFFormula.subst, pred,
        Term.subst_app₁, Term.subst_succ, Term.subst_zero, Term.subst,
        Fin.cases_zero]
    · exact mp or_left eq_refl
    · apply weaken
      exact mp or_right (eq_symm_rule (unary_congr (f := Primrec.succ) (pred_succ _)))
  simpa only [QFFormula.subst, pred, Term.subst_app₁, Term.subst_succ,
    Term.subst_zero, Term.subst, Fin.cases_zero] using
    (QFProofI.subst (v := (Fin.cases t Fin.elim0)) h)

public theorem sub_succ_succ (s t : Term n) :
    QFProofI (sub s.succ t.succ ≡ sub s t) := by
  have h : QFProofI (sub (.var 1 : Term 2).succ (.var 0 : Term 2).succ ≡
      sub (.var 1) (.var 0)) := by
    apply induction <;>
      simp only [QFFormula.inst, QFFormula.replace, QFFormula.subst, sub,
        Term.subst_app₂, Term.subst_succ, Term.subst, Fin.cases_zero]
    · exact eq_trans_rule (sub_succ _ 0)
        (eq_trans_rule (unary_congr (sub_zero _))
          (eq_trans_rule (pred_succ _) (eq_symm_rule (sub_zero _))))
    · apply eq_trans_under (weaken (sub_succ _ _))
      apply eq_trans_under (unary_congr_under imp_refl)
      exact weaken (eq_symm_rule (sub_succ _ _))
  simpa only [QFFormula.subst, sub, Term.subst_app₂, Term.subst_succ, Term.subst,
    Fin.cases_one, Fin.cases_zero] using
    (QFProofI.subst (v := (Fin.cases t (Fin.cases s Fin.elim0))) h)

private theorem sub_succ_self (t : Term n) : QFProofI (sub t.succ t ≡ (0 : Term n).succ) := by
  have h : QFProofI (sub (.var 0 : Term 1).succ (.var 0) ≡ (0 : Term 1).succ) := by
    apply induction <;>
      simp only [QFFormula.inst, QFFormula.replace, QFFormula.subst, sub,
        Term.subst_app₂, Term.subst_succ, Term.subst_zero, Term.subst,
        Fin.cases_zero]
    · exact sub_zero _
    · exact eq_trans_under (weaken (sub_succ_succ _ _)) imp_refl
  simpa only [QFFormula.subst, sub, Term.subst_app₂, Term.subst_succ, Term.subst_zero,
    Term.subst, Fin.cases_zero] using (QFProofI.subst (v := (Fin.cases t Fin.elim0)) h)

public theorem sub_self (t : Term n) : QFProofI (sub t t ≡ 0) :=
  eq_trans_rule (eq_symm_rule (sub_succ_succ t t))
    (eq_trans_rule (sub_succ _ _)
      (eq_trans_rule (unary_congr (sub_succ_self t)) (pred_succ 0)))

public theorem and_curry (h : QFProofI (φ ⊓ ψ ⇒ χ)) : QFProofI (φ ⇒ ψ ⇒ χ) :=
  imp_trans_under and_intro (weaken h)

/-- Every intuitionistic QF derivation is a classical QF derivation. -/
public theorem toQFProof (h : QFProofI φ) : QFProof φ := by
  induction h with
  | imp_imp_self => exact .imp_imp_self
  | imp_distrib => exact .imp_distrib
  | @false_elim n φ =>
    have hi : QFProof ((⊥ : QFFormula n) ⇒ ⊥) :=
      .mp (.mp .imp_distrib (.imp_imp_self (φ := ⊥) (ψ := ⊥ ⇒ ⊥))) .imp_imp_self
    exact .mp .imp_contra (.mp .imp_imp_self hi)
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

public theorem decidable_imp (hφ : QFProofI (φ ⊔ ∼ φ))
    (hψ : QFProofI (ψ ⊔ ∼ ψ)) : QFProofI ((φ ⇒ ψ) ⊔ ∼ (φ ⇒ ψ)) := by
  have h : QFProofI (φ ⇒ ∼ ψ ⇒ ∼ (φ ⇒ ψ)) := imp_trans_rule imp_apply imp_trans
  exact cases_rule hφ
    (cases_under hψ (weaken (imp_trans_rule imp_imp_self or_left))
      (imp_trans_under h (weaken or_right)))
    (imp_trans_rule (mp (imp_swap_rule imp_trans) false_elim) or_left)

public theorem decidable_and (hφ : QFProofI (φ ⊔ ∼ φ))
    (hψ : QFProofI (ψ ⊔ ∼ ψ)) : QFProofI ((φ ⊓ ψ) ⊔ ∼ (φ ⊓ ψ)) :=
  cases_rule hφ
    (cases_under hψ (imp_trans_under and_intro (weaken or_left))
      (weaken (imp_trans_rule (contrapose and_right) or_right)))
    (imp_trans_rule (contrapose and_left) or_right)

public theorem decidable_or (hφ : QFProofI (φ ⊔ ∼ φ))
    (hψ : QFProofI (ψ ⊔ ∼ ψ)) : QFProofI ((φ ⊔ ψ) ⊔ ∼ (φ ⊔ ψ)) :=
  cases_rule hφ (imp_trans_rule or_left or_left)
    (cases_under hψ (weaken (imp_trans_rule or_right or_left))
      (imp_trans_under or_elim (weaken or_right)))

/-- Decidable atomic equalities give decidability of every quantifier-free formula. -/
public theorem formula_decidable
    (heq : ∀ {n} (s t : Term n), QFProofI ((s ≡ t) ⊔ ∼ (s ≡ t)))
    (φ : QFFormula n) : QFProofI (φ ⊔ ∼ φ) := by
  induction φ with
  | false => exact mp or_right imp_refl
  | eq s t => exact heq s t
  | imp φ ψ ihφ ihψ => exact decidable_imp ihφ ihψ
  | and φ ψ ihφ ihψ => exact decidable_and ihφ ihψ
  | or φ ψ ihφ ihψ => exact decidable_or ihφ ihψ

public theorem double_neg_elim (h : QFProofI (φ ⊔ ∼ φ)) :
    QFProofI (∼ ∼ φ ⇒ φ) :=
  cases_under h (weaken imp_refl) (imp_trans_under imp_refl (weaken false_elim))

public theorem contra (h : QFProofI (φ ⊔ ∼ φ)) :
    QFProofI ((∼ φ ⇒ ∼ ψ) ⇒ ψ ⇒ φ) :=
  imp_trans_under (imp_swap_rule (imp_trans_rule imp_apply (imp_swap_rule imp_trans)))
    (weaken (double_neg_elim h))

end PRA.QFProofI

namespace PRA.Proof

open Formula

variable {n : Nat} {φ : Formula n}

/-- Uniform substitution preserves PRA derivability, including the induction restriction. -/
public theorem subst (h : Proof φ) (v : Fin n → Term m) : Proof (φ.subst v) := by
  induction h generalizing m with
  | imp_imp_self => exact imp_imp_self
  | imp_distrib => exact imp_distrib
  | imp_contra => exact imp_contra
  | and_intro => exact and_intro
  | and_left => exact and_left
  | and_right => exact and_right
  | or_left => exact or_left
  | or_right => exact or_right
  | or_elim => exact or_elim
  | mp h₁ h₂ ih₁ ih₂ => exact mp (ih₁ v) (ih₂ v)
  | @forall_elim n φ t =>
    simpa only [Formula.subst, Formula.subst_inst] using
      (forall_elim (φ := φ.subst (Fin.cases (.var 0) fun i => (v i).shift))
        (t := t.subst v))
  | @forall_imp n φ ψ =>
    simpa only [Formula.subst, Formula.subst_shift, Fin.cases_succ, Formula.shift_subst]
      using (forall_imp (φ := φ.subst v)
        (ψ := ψ.subst (Fin.cases (.var 0) fun i => (v i).shift)))
  | @exists_intro n φ t =>
    simpa only [Formula.subst, Formula.subst_inst] using
      (exists_intro (φ := φ.subst (Fin.cases (.var 0) fun i => (v i).shift))
        (t := t.subst v))
  | @exists_elim n φ ψ =>
    simpa only [Formula.subst, Formula.subst_shift, Fin.cases_succ, Formula.shift_subst]
      using (exists_elim (φ := φ.subst (Fin.cases (.var 0) fun i => (v i).shift))
        (ψ := ψ.subst v))
  | gen h ih => exact gen (ih (Fin.cases (.var 0) fun i => (v i).shift))
  | eq_refl => exact eq_refl
  | eq_symm => exact eq_symm
  | eq_trans => exact eq_trans
  | @eq_congr_ith n k f u i t =>
    simpa only [Formula.subst, Term.subst, apply_ite (fun t : Term n => t.subst v)] using
      (eq_congr_ith (f := f) (v := fun i => (u i).subst v) (i := i) (t := t.subst v))
  | @succ_ne_zero n t =>
    simpa only [Formula.subst, Formula.neg, Term.subst_succ, Term.subst_zero] using
      (succ_ne_zero (t := t.subst v))
  | @succ_inj n s t =>
    simpa only [Formula.subst, Term.subst_succ] using
      (succ_inj (t₁ := s.subst v) (t₂ := t.subst v))
  | app_proj => exact app_proj
  | app_comp => exact app_comp
  | @app_prec_zero n k f g u =>
    simpa only [Formula.subst, Term.subst, Fin.map_cases (fun t => Term.subst t v),
      Term.subst_zero] using
      (app_prec_zero (f := f) (g := g) (v := fun i => (u i).subst v))
  | @app_prec_succ n k f g t u =>
    simpa only [Formula.subst, Term.subst, Fin.map_cases (fun t => Term.subst t v),
      Term.subst_succ] using
      (app_prec_succ (f := f) (g := g) (v := fun i => (u i).subst v) (t := t.subst v))
  | @induction n φ hφ =>
    have hφ' := (Formula.quantifierFree_subst φ
      (Fin.cases (.var 0) fun i => (v i).shift)).mpr hφ
    simpa only [Formula.subst, Formula.subst_inst, Term.subst_zero, Formula.subst_replace,
      Formula.replace_subst, Term.subst_succ, Term.subst, Fin.cases_zero, Fin.cases_succ]
      using (Proof.induction hφ')

/-- A universally quantified theorem yields its body with the quantified variable free.
The remaining variables keep their order. -/
public theorem forall_body {A : Formula (n + 1)} (h : Proof (.all A)) : Proof A := by
  have shifted := Proof.subst h (Term.var ∘ Fin.succ)
  have specialized := Proof.mp (Proof.forall_elim (t := .var 0)) shifted
  simpa only [Formula.subst, Function.comp_apply, Term.shift, Term.subst,
    Formula.inst_shift_all] using specialized

end PRA.Proof

namespace PRA.QFProof

open QFFormula
open Term (pred sub)

variable {n : Nat} {φ ψ χ θ : QFFormula n}

public theorem imp_refl : QFProof (φ ⇒ φ) :=
  mp (mp imp_distrib (imp_imp_self (φ := φ) (ψ := φ ⇒ φ))) imp_imp_self

public theorem weaken (h : QFProof ψ) : QFProof (φ ⇒ ψ) :=
  mp imp_imp_self h

public theorem mp_under (h₁ : QFProof (φ ⇒ ψ ⇒ χ)) (h₂ : QFProof (φ ⇒ ψ)) :
    QFProof (φ ⇒ χ) :=
  mp (mp imp_distrib h₁) h₂

public theorem imp_trans_rule (h₁ : QFProof (φ ⇒ ψ)) (h₂ : QFProof (ψ ⇒ χ)) :
    QFProof (φ ⇒ χ) :=
  mp_under (weaken h₂) h₁

public theorem imp_swap_rule (h : QFProof (φ ⇒ ψ ⇒ χ)) : QFProof (ψ ⇒ φ ⇒ χ) :=
  mp_under (weaken (mp imp_distrib h)) imp_imp_self

public theorem imp_trans : QFProof ((φ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ φ ⇒ χ) :=
  imp_swap_rule (imp_trans_rule imp_imp_self imp_distrib)

public theorem imp_apply : QFProof (φ ⇒ (φ ⇒ ψ) ⇒ ψ) :=
  imp_swap_rule imp_refl

public theorem not_not_intro : QFProof (φ ⇒ ∼ ∼ φ) :=
  imp_apply

public theorem not_not_elim : QFProof (∼ ∼ φ ⇒ φ) :=
  mp imp_contra not_not_intro

public theorem contraposition : QFProof ((φ ⇒ ψ) ⇒ ∼ ψ ⇒ ∼ φ) :=
  imp_trans

public theorem contrapose (h : QFProof (φ ⇒ ψ)) : QFProof (∼ ψ ⇒ ∼ φ) :=
  mp contraposition h

public theorem and_intro_under (h₁ : QFProof (φ ⇒ ψ)) (h₂ : QFProof (φ ⇒ χ)) :
    QFProof (φ ⇒ ψ ⊓ χ) :=
  mp_under (imp_trans_rule h₁ and_intro) h₂

public theorem and_curry (h : QFProof (φ ⊓ ψ ⇒ χ)) : QFProof (φ ⇒ ψ ⇒ χ) :=
  imp_trans_rule and_intro (mp (imp_swap_rule imp_trans) h)

public theorem or_elim_imp (hφ : QFProof (φ ⇒ χ)) (hψ : QFProof (ψ ⇒ χ)) :
    QFProof (φ ⊔ ψ ⇒ χ) :=
  mp (mp or_elim hφ) hψ

public theorem false_elim {A : QFFormula n} : QFProof (⊥ ⇒ A) :=
  mp imp_contra (weaken (imp_refl (φ := ⊥)))

public theorem imp_trans_under (h₁ : QFProof (θ ⇒ φ ⇒ ψ))
    (h₂ : QFProof (θ ⇒ ψ ⇒ χ)) : QFProof (θ ⇒ φ ⇒ χ) :=
  mp_under (imp_trans_rule h₁ imp_trans) h₂

public theorem cases_rule (h : QFProof (φ ⊔ ψ)) (h₁ : QFProof (φ ⇒ χ))
    (h₂ : QFProof (ψ ⇒ χ)) : QFProof χ :=
  mp (mp (mp or_elim h₁) h₂) h

public theorem cases_under (h : QFProof (φ ⊔ ψ)) (h₁ : QFProof (θ ⇒ φ ⇒ χ))
    (h₂ : QFProof (θ ⇒ ψ ⇒ χ)) : QFProof (θ ⇒ χ) :=
  mp_under (mp_under (imp_trans_rule h₁ or_elim) h₂) (weaken h)

public theorem excluded_middle (A : QFFormula n) : QFProof (A ⊔ ∼ A) :=
  mp (mp imp_contra imp_apply) (mp_under (contrapose or_right) (contrapose or_left))

public theorem eq_symm_rule {s t : Term n} (h : QFProof (s ≡ t)) :
    QFProof (t ≡ s) := mp eq_symm h

public theorem eq_trans_rule {s t u : Term n} (h₁ : QFProof (s ≡ t))
    (h₂ : QFProof (t ≡ u)) : QFProof (s ≡ u) := mp (mp eq_trans h₁) h₂

public theorem eq_trans_under {s t u : Term n} (h₁ : QFProof (φ ⇒ s ≡ t))
    (h₂ : QFProof (φ ⇒ t ≡ u)) : QFProof (φ ⇒ s ≡ u) :=
  mp_under (imp_trans_rule h₁ eq_trans) h₂

private theorem app_congr_list {m : Nat} [BEq (Fin m)] [LawfulBEq (Fin m)]
    {f : Primrec m} {v w : Fin m → Term n}
    (h : ∀ i, QFProof (φ ⇒ v i ≡ w i)) (is : List (Fin m)) :
    QFProof (φ ⇒ Term.app f v ≡ Term.app f (fun i => if i ∈ is then w i else v i)) := by
  induction is with
  | nil => simpa using (weaken (φ := φ) (eq_refl (t := Term.app f v)))
  | cons i is ih =>
    let u : Fin m → Term n := fun j => if j ∈ is then w j else v j
    have hi : QFProof (φ ⇒ u i ≡ w i) := by
      cases (inferInstance : Decidable (i ∈ is)) with
      | isTrue hm => simpa [u, hm] using (weaken (φ := φ) (eq_refl (t := w i)))
      | isFalse hm => simpa [u, hm] using h i
    have hu : (fun j => if j = i then w i else u j) =
        (fun j => if j ∈ i :: is then w j else v j) := by
      funext j
      cases (inferInstance : Decidable (j = i)) with
      | isTrue hj => subst j; simp
      | isFalse hj => simp [u, hj]
    simpa only [hu] using eq_trans_under ih (imp_trans_rule hi (eq_congr_ith (f := f)))

/-- Pointwise equality of arguments gives equality of applications under a shared antecedent. -/
public theorem app_congr_under {m : Nat} {f : Primrec m} {v w : Fin m → Term n}
    (h : ∀ i, QFProof (φ ⇒ v i ≡ w i)) :
    QFProof (φ ⇒ Term.app f v ≡ Term.app f w) := by
  letI : BEq (Fin m) := instBEqOfDecidableEq
  letI : LawfulBEq (Fin m) :=
    { rfl := decide_eq_true rfl, eq_of_beq := of_decide_eq_true }
  simpa only [List.mem_finRange, ite_true] using app_congr_list h (List.finRange m)

/-- Provably equal arguments give provably equal function applications. -/
public theorem app_congr {m : Nat} {f : Primrec m} {v w : Fin m → Term n}
    (h : ∀ i, QFProof (v i ≡ w i)) : QFProof (Term.app f v ≡ Term.app f w) :=
  mp (app_congr_under (φ := ⊤) (fun i => weaken (h i))) imp_refl

public theorem unary_congr_under {f : Primrec 1} {s t : Term n}
    (h : QFProof (φ ⇒ s ≡ t)) : QFProof (φ ⇒ Term.app₁ f s ≡ Term.app₁ f t) := by
  apply app_congr_under
  intro i
  simpa only [Term.app₁, Fin.cases_fin_one] using h

public theorem unary_congr {f : Primrec 1} {s t : Term n}
    (h : QFProof (s ≡ t)) : QFProof (Term.app₁ f s ≡ Term.app₁ f t) :=
  mp (unary_congr_under (φ := ⊤) (weaken h)) imp_refl

public theorem eq_congr_under {s s' t t' : Term n} (h₁ : QFProof (φ ⇒ s ≡ s'))
    (h₂ : QFProof (φ ⇒ t ≡ t')) : QFProof (φ ⇒ (s ≡ t) ⇒ s' ≡ t') :=
  imp_trans_under (imp_trans_rule (imp_trans_rule h₁ eq_symm) eq_trans)
    (imp_trans_rule h₂ (imp_swap_rule eq_trans))

public theorem pred_succ (t : Term n) : QFProof (pred t.succ ≡ t) :=
  (QFProofI.pred_succ t).toQFProof

public theorem sub_zero (s : Term n) : QFProof (sub s 0 ≡ s) :=
  (QFProofI.sub_zero s).toQFProof

public theorem sub_succ (s t : Term n) : QFProof (sub s t.succ ≡ pred (sub s t)) :=
  (QFProofI.sub_succ s t).toQFProof

public theorem zero_or_succ (t : Term n) : QFProof ((t ≡ 0) ⊔ (t ≡ (pred t).succ)) :=
  (QFProofI.zero_or_succ t).toQFProof

public theorem sub_succ_succ (s t : Term n) :
    QFProof (sub s.succ t.succ ≡ sub s t) :=
  (QFProofI.sub_succ_succ s t).toQFProof

public theorem sub_self (t : Term n) : QFProof (sub t t ≡ 0) :=
  (QFProofI.sub_self t).toQFProof

public theorem imp_mono_under {ρ : QFFormula n} (h₁ : QFProof (ρ ⇒ χ ⇒ φ))
    (h₂ : QFProof (ρ ⇒ ψ ⇒ θ)) : QFProof (ρ ⇒ (φ ⇒ ψ) ⇒ χ ⇒ θ) :=
  imp_trans_under (imp_trans_rule h₁ imp_trans) (imp_trans_rule h₂ (imp_swap_rule imp_trans))

public theorem and_mono_under {ρ : QFFormula n} (h₁ : QFProof (ρ ⇒ φ ⇒ χ))
    (h₂ : QFProof (ρ ⇒ ψ ⇒ θ)) : QFProof (ρ ⇒ φ ⊓ ψ ⇒ χ ⊓ θ) :=
  and_curry (and_intro_under
    (mp_under (imp_trans_rule and_left h₁) (imp_trans_rule and_right and_left))
    (mp_under (imp_trans_rule and_left h₂) (imp_trans_rule and_right and_right)))

public theorem or_elim_under (h₁ : QFProof (θ ⇒ φ ⇒ χ)) (h₂ : QFProof (θ ⇒ ψ ⇒ χ)) :
    QFProof (θ ⇒ φ ⊔ ψ ⇒ χ) := mp_under (imp_trans_rule h₁ or_elim) h₂

public theorem or_mono_under {ρ : QFFormula n} (h₁ : QFProof (ρ ⇒ φ ⇒ χ))
    (h₂ : QFProof (ρ ⇒ ψ ⇒ θ)) : QFProof (ρ ⇒ φ ⊔ ψ ⇒ χ ⊔ θ) :=
  or_elim_under (imp_trans_under h₁ (weaken or_left)) (imp_trans_under h₂ (weaken or_right))

public theorem term_congr_under (t : Term m) {v w : Fin m → Term n}
    (h : ∀ i, QFProof (φ ⇒ v i ≡ w i)) : QFProof (φ ⇒ t.subst v ≡ t.subst w) := by
  induction t with
  | var i => exact h i
  | app f u ih => exact app_congr_under (fun i => ih i h)

/-- Equal parameter substitutions give provably equivalent instances, in either direction.
This direction transports a proof from the first instance to the second. -/
public theorem formula_congr_under (A : QFFormula m) {v w : Fin m → Term n}
    (h : ∀ i, QFProof (φ ⇒ v i ≡ w i)) : QFProof (φ ⇒ A.subst v ⇒ A.subst w) := by
  induction A generalizing v w with
  | false => exact weaken imp_refl
  | eq s t => exact eq_congr_under (term_congr_under s h) (term_congr_under t h)
  | imp A B ihA ihB => exact imp_mono_under (ihA (fun i => imp_trans_rule (h i) eq_symm)) (ihB h)
  | and A B ihA ihB => exact and_mono_under (ihA h) (ihB h)
  | or A B ihA ihB => exact or_mono_under (ihA h) (ihB h)

public theorem imp_mono (h₁ : QFProof (χ ⇒ φ)) (h₂ : QFProof (ψ ⇒ θ)) :
    QFProof ((φ ⇒ ψ) ⇒ χ ⇒ θ) := imp_trans_rule (mp imp_trans h₁) (mp (imp_swap_rule imp_trans) h₂)

public theorem instance_congr_under (P : QFFormula (k + 1)) (v : Fin k → Term n)
    {s t : Term n} (h : QFProof (φ ⇒ s ≡ t)) :
    QFProof (φ ⇒ P.subst (Fin.cases s v) ⇒ P.subst (Fin.cases t v)) :=
  formula_congr_under P (fun i => Fin.cases h (fun _ => weaken eq_refl) i)

public theorem or_mp {A B C D : QFFormula n} :
    QFProof (((A ⇒ B) ⊔ C) ⇒ (A ⊔ D) ⇒ B ⊔ (D ⊔ C)) := by
  apply or_elim_imp
  · exact or_elim_under (imp_trans_under imp_refl (weaken or_left))
      (weaken (imp_trans_rule or_left or_right))
  · exact imp_trans_rule (imp_trans_rule or_right or_right) imp_imp_self

public theorem or_map (h₁ : QFProof (φ ⇒ χ)) (h₂ : QFProof (ψ ⇒ θ)) :
    QFProof (φ ⊔ ψ ⇒ χ ⊔ θ) := or_elim_imp (imp_trans_rule h₁ or_left) (imp_trans_rule h₂ or_right)

public theorem or_and {A B C D : QFFormula n} :
    QFProof ((A ⊔ C) ⇒ (B ⊔ D) ⇒ (A ⊓ B) ⊔ (C ⊔ D)) := by
  apply or_elim_imp
  · exact or_elim_under (imp_trans_under and_intro (weaken or_left))
      (weaken (imp_trans_rule or_right or_right))
  · exact imp_trans_rule (imp_trans_rule or_left or_right) imp_imp_self

public theorem imp_or {A B C : QFFormula n} :
    QFProof ((A ⇒ B ⊔ C) ⇒ (A ⇒ B) ⊔ C) := by
  apply cases_rule (excluded_middle C)
  · exact imp_trans_rule or_right imp_imp_self
  · have h : QFProof (∼ C ⇒ B ⊔ C ⇒ B) :=
      or_elim_under (weaken imp_refl) (imp_trans_under imp_refl (weaken false_elim))
    exact imp_trans_under (imp_mono_under (weaken imp_refl) h) (weaken or_left)

end PRA.QFProof

namespace PRA.Term

/-- Compile a term to a primitive-recursive symbol with the same free variables. -/
@[expose] public def toPrimrec : Term n → Primrec n
  | .var i => .proj i
  | .app f v => .comp f (fun i => toPrimrec (v i))

end PRA.Term

namespace PRA.QFProof

open QFFormula

/-- Applying the compiled symbol proves the corresponding term instance. -/
public theorem toPrimrec_eq (t : Term n) (v : Fin n → Term m) :
    QFProof (.app (Term.toPrimrec t) v ≡ t.subst v) := by
  induction t with
  | var i => exact app_proj
  | app f ts ih => exact eq_trans_rule app_comp (app_congr (fun i => ih i v))

private theorem compile_witness {P : QFFormula (n + 1)} {t : Term n}
    (h : QFProof (P.inst t)) : QFProof (P.inst (.app (Term.toPrimrec t) Term.var)) := by
  have heq : QFProof (t ≡ .app (Term.toPrimrec t) Term.var) := by
    exact eq_symm_rule (by simpa only [Term.subst_id] using toPrimrec_eq t Term.var)
  have ht := instance_congr_under P Term.var (φ := ⊤) (weaken heq)
  exact mp (mp ht imp_refl) h

end PRA.QFProof

namespace PRA

/-- A quantifier-free formula has a provable term instance exactly when it has a provable
instance given by a primitive-recursive expression in its free variables. Variable zero of
`P` is replaced by the witness; the remaining variables are the numerical parameters. -/
public theorem qf_witness_iff_primrec {P : QFFormula (n + 1)} :
    (∃ t : Term n, QFProof (P.inst t)) ↔
      ∃ f : Primrec n, QFProof (P.inst (.app f Term.var)) := by
  constructor
  · rintro ⟨t, h⟩
    exact ⟨Term.toPrimrec t, QFProof.compile_witness h⟩
  · rintro ⟨f, h⟩
    exact ⟨.app f Term.var, h⟩

/-- Embed a classical QF derivation into first-order PRA, preserving its formula. -/
public theorem QFProof.toProof {A : QFFormula n} (h : QFProof A) : Proof A.toFormula := by
  induction h with
  | imp_imp_self => exact .imp_imp_self
  | imp_distrib => exact .imp_distrib
  | imp_contra => exact .imp_contra
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
  | @induction n A _ _ ih₀ ihs =>
    have base : Proof (A.toFormula.inst 0) := by
      simpa only [QFFormula.inst, QFFormula.toFormula_subst, Formula.inst] using ih₀
    have step : Proof (.imp A.toFormula (A.toFormula.replace (.succ (.var 0)))) := by
      simpa only [QFFormula.toFormula, QFFormula.replace, QFFormula.toFormula_subst,
        Formula.replace] using ihs
    have all : Proof (.all A.toFormula) :=
      .mp (.mp (.induction (QFFormula.toFormula_qf A)) base) (.gen step)
    exact Proof.forall_body all
  | @subst n m A v _ ih =>
    rw [QFFormula.toFormula_subst]
    exact Proof.subst ih v

end PRA

namespace Primrec

/-- A conditional symbol with arguments for the test value, the zero branch, and the positive
branch. Its value is the second argument when the first is zero, and the third otherwise. -/
@[expose] public def cond : Primrec 3 := prec (proj 0) (proj 3)

end Primrec

namespace PRA.Term

/-- `cond c a b` chooses `a` when `c` is zero and `b` when `c` is positive. -/
@[expose] public def cond (c a b : Term n) : Term n :=
  .app Primrec.cond (Fin.cases c (Fin.cases a (Fin.cases b Fin.elim0)))

/-- Apply primitive recursion with term bodies `b` and `s` to `x` and parameters `v`.
The step body has variable zero for the predecessor, variable one for the previous result,
and the remaining variables for the parameters. -/
@[expose] public def recApp (b : Term k) (s : Term (k + 2)) (x : Term n)
    (v : Fin k → Term n) : Term n :=
  .app (.prec (Term.toPrimrec b) (Term.toPrimrec s)) (Fin.cases x v)

public theorem cond_subst (c a b : Term n) (v : Fin n → Term m) :
    (cond c a b).subst v = cond (c.subst v) (a.subst v) (b.subst v) := by
  simp only [cond, Term.subst, Fin.map_cases (fun t => Term.subst t v),
    Fin.map_elim0 (fun t => Term.subst t v)]

public theorem recApp_subst (b : Term k) (s : Term (k + 2)) (x : Term n)
    (v : Fin k → Term n) (w : Fin n → Term m) :
    (recApp b s x v).subst w = recApp b s (x.subst w) (fun i => (v i).subst w) := by
  simp only [recApp, Term.subst, Fin.map_cases (fun t => Term.subst t w)]

end PRA.Term

namespace PRA.QFFormula

open Term (cond sub)

/-- Compile a QF formula into a numerical term whose equality to zero expresses the formula.
The term has the same free variables. `QFProof.test_correct` proves both implications. -/
@[expose] public def test : QFFormula n → Term n
  | .false => (0 : Term n).succ
  | .eq s t => cond (sub s t) (sub t s) (0 : Term n).succ
  | .imp A B => cond (test A) (test B) 0
  | .and A B => cond (test A) (test B) (0 : Term n).succ
  | .or A B => cond (test A) 0 (test B)

public theorem test_subst (A : QFFormula n) (v : Fin n → Term m) :
    (test A).subst v = test (A.subst v) := by
  induction A with
  | false => simp only [test, Term.subst_succ, Term.subst_zero, QFFormula.subst]
  | eq s t =>
    simp only [test, Term.cond_subst, sub, Term.subst_app₂, Term.subst_succ, Term.subst_zero,
      QFFormula.subst]
  | imp A B ihA ihB | and A B ihA ihB | or A B ihA ihB =>
    simp only [test, Term.cond_subst, ihA, ihB, Term.subst_succ, Term.subst_zero, QFFormula.subst]

end PRA.QFFormula

namespace PRA.Term

open QFFormula (test)

/-- Choose `s` when the QF formula `A` holds and `t` when its negation holds.
The branches are justified by `QFProof.choose_left` and `QFProof.choose_right`. -/
@[expose] public def choose (A : QFFormula n) (s t : Term n) : Term n := cond (test A) s t

public theorem choose_subst (A : QFFormula n) (s t : Term n) (v : Fin n → Term m) :
    (choose A s t).subst v = choose (A.subst v) (s.subst v) (t.subst v) := by
  simp only [choose, cond_subst, QFFormula.test_subst]

end PRA.Term

namespace PRA.QFProof

open QFFormula
open Term (pred sub cond choose recApp)

variable {n : Nat} {φ ψ χ θ : QFFormula n}

private theorem decEq_zero (t : Term n) : QFProof ((t ≡ 0) ⊔ ∼ (t ≡ 0)) :=
  excluded_middle (t ≡ 0)

private def subAntisymm (s t : Term n) : QFFormula n :=
  ((sub s t ≡ 0) ⊓ (sub t s ≡ 0)) ⇒ s ≡ t

private theorem subAntisymm_congr_under {s s' t t' : Term n}
    (hs : QFProof (φ ⇒ s ≡ s')) (ht : QFProof (φ ⇒ t ≡ t')) :
    QFProof (φ ⇒ subAntisymm s t ⇒ subAntisymm s' t') := by
  have h := formula_congr_under (subAntisymm (.var 0 : Term 2) (.var 1))
    (v := Fin.cases s (Fin.cases t Fin.elim0))
    (w := Fin.cases s' (Fin.cases t' Fin.elim0))
    (fun i => Fin.cases hs (Fin.cases ht (fun j => Fin.elim0 j)) i)
  simpa only [subAntisymm, QFFormula.subst, sub, Term.subst_app₂, Term.subst_zero,
    Term.subst, Fin.cases_zero, Fin.cases_one] using h

private theorem subAntisymm_congr {s s' t t' : Term n}
    (hs : QFProof (s ≡ s')) (ht : QFProof (t ≡ t')) :
    QFProof (subAntisymm s t ⇒ subAntisymm s' t') :=
  mp (subAntisymm_congr_under (φ := ⊤) (weaken hs) (weaken ht)) imp_refl

private theorem subAntisymm_zero_left (t : Term n) : QFProof (subAntisymm 0 t) :=
  imp_trans_rule and_right (imp_trans_rule (mp eq_trans (eq_symm_rule (sub_zero t))) eq_symm)

private theorem subAntisymm_zero_right (s : Term n) : QFProof (subAntisymm s 0) :=
  imp_trans_rule and_left (mp eq_trans (eq_symm_rule (sub_zero s)))

private theorem subAntisymm_succ (s t : Term n) :
    QFProof (subAntisymm s t ⇒ subAntisymm s.succ t.succ) := by
  have h₁ : QFProof ((sub s.succ t.succ ≡ 0) ⇒ sub s t ≡ 0) :=
    mp eq_trans (eq_symm_rule (sub_succ_succ s t))
  have h₂ : QFProof ((sub t.succ s.succ ≡ 0) ⇒ sub t s ≡ 0) :=
    mp eq_trans (eq_symm_rule (sub_succ_succ t s))
  have h₃ := and_intro_under (imp_trans_rule and_left h₁) (imp_trans_rule and_right h₂)
  exact imp_trans_under (weaken h₃) (imp_trans_under imp_refl
    (weaken (unary_congr_under (f := Primrec.succ) imp_refl)))

private theorem subAntisymm_pred (s t : Term n) :
    QFProof (subAntisymm (pred s) (pred t) ⇒ subAntisymm s t) := by
  apply cases_rule (zero_or_succ s)
  · apply imp_swap_rule
    apply weaken
    exact mp_under (subAntisymm_congr_under (imp_trans_rule imp_refl eq_symm) (weaken eq_refl))
      (weaken (subAntisymm_zero_left t))
  · apply cases_under (zero_or_succ t)
    · apply weaken
      apply imp_swap_rule
      apply weaken
      exact mp_under (subAntisymm_congr_under (weaken eq_refl) (imp_trans_rule imp_refl eq_symm))
        (weaken (subAntisymm_zero_right s))
    · apply and_curry
      exact imp_trans_under (weaken (subAntisymm_succ (pred s) (pred t)))
        (subAntisymm_congr_under (imp_trans_rule and_left eq_symm)
          (imp_trans_rule and_right eq_symm))

private theorem subAntisymm_sub (s t u : Term n) :
    QFProof (subAntisymm (sub s u) (sub t u) ⇒ subAntisymm s t) := by
  have h : QFProof (subAntisymm (sub (.var 1 : Term 3) (.var 0))
      (sub (.var 2) (.var 0)) ⇒ subAntisymm (.var 1) (.var 2)) := by
    apply induction <;>
      simp only [QFFormula.inst, QFFormula.replace, QFFormula.subst, subAntisymm,
        sub, Term.subst_app₂, Term.subst_zero, Term.subst, Fin.cases_zero]
    · exact subAntisymm_congr (sub_zero _) (sub_zero _)
    · have hstep : QFProof (subAntisymm (sub (.var 1 : Term 3) (.var 0 : Term 3).succ)
          (sub (.var 2) (.var 0 : Term 3).succ) ⇒
          subAntisymm (sub (.var 1) (.var 0)) (sub (.var 2) (.var 0))) :=
        imp_trans_rule (subAntisymm_congr (sub_succ _ _) (sub_succ _ _)) (subAntisymm_pred _ _)
      exact mp imp_trans hstep
  simpa only [QFFormula.subst, subAntisymm, sub, Term.subst_app₂, Term.subst_zero,
    Term.subst, Fin.cases_two, Fin.cases_one, Fin.cases_zero] using
    (QFProof.subst (v := Fin.cases u (Fin.cases s (Fin.cases t Fin.elim0))) h)

/-- If both mutual truncated differences vanish, the two terms are provably equal. -/
public theorem sub_antisymm (s t : Term n) :
    QFProof (((sub s t ≡ 0) ⊓ (sub t s ≡ 0)) ⇒ s ≡ t) :=
  mp (subAntisymm_sub s t s)
    (mp (subAntisymm_congr (eq_symm_rule (sub_self s)) eq_refl)
      (subAntisymm_zero_left (sub t s)))

public theorem cond_zero (a b : Term n) : QFProof (cond 0 a b ≡ a) :=
  eq_trans_rule app_prec_zero app_proj

public theorem cond_succ (c a b : Term n) : QFProof (cond c.succ a b ≡ b) :=
  eq_trans_rule app_prec_succ app_proj

public theorem cond_congr_under {c c' a a' b b' : Term n}
    (hc : QFProof (φ ⇒ c ≡ c')) (ha : QFProof (φ ⇒ a ≡ a'))
    (hb : QFProof (φ ⇒ b ≡ b')) : QFProof (φ ⇒ cond c a b ≡ cond c' a' b') :=
  app_congr_under (fun i => Fin.cases hc (Fin.cases ha
    (Fin.cases hb (fun j => Fin.elim0 j))) i)

public theorem cond_of_zero (c a b : Term n) :
    QFProof ((c ≡ 0) ⇒ cond c a b ≡ a) :=
  eq_trans_under (cond_congr_under imp_refl (weaken eq_refl) (weaken eq_refl))
    (weaken (cond_zero a b))

public theorem cond_of_ne_zero (c a b : Term n) :
    QFProof (∼ (c ≡ 0) ⇒ cond c a b ≡ b) := by
  apply cases_under (zero_or_succ c)
  · exact imp_trans_under imp_refl (weaken false_elim)
  · apply weaken
    exact eq_trans_under (cond_congr_under imp_refl (weaken eq_refl) (weaken eq_refl))
      (weaken (cond_succ (pred c) a b))

private abbrev Bi (A B : QFFormula n) := QFProof (A ⇒ B) ∧ QFProof (B ⇒ A)

private theorem bi_trans {A B C : QFFormula n} (h : Bi A B) (h' : Bi B C) : Bi A C :=
  ⟨imp_trans_rule h.1 h'.1, imp_trans_rule h'.2 h.2⟩

private theorem bi_imp {A B C D : QFFormula n} (h : Bi A B) (h' : Bi C D) :
    Bi (A ⇒ C) (B ⇒ D) := ⟨imp_mono h.2 h'.1, imp_mono h.1 h'.2⟩

private theorem bi_and {A B C D : QFFormula n} (h : Bi A B) (h' : Bi C D) :
    Bi (A ⊓ C) (B ⊓ D) :=
  ⟨and_intro_under (imp_trans_rule and_left h.1) (imp_trans_rule and_right h'.1),
    and_intro_under (imp_trans_rule and_left h.2) (imp_trans_rule and_right h'.2)⟩

private theorem bi_or {A B C D : QFFormula n} (h : Bi A B) (h' : Bi C D) :
    Bi (A ⊔ C) (B ⊔ D) :=
  ⟨or_elim_imp (imp_trans_rule h.1 or_left) (imp_trans_rule h'.1 or_right),
    or_elim_imp (imp_trans_rule h.2 or_left) (imp_trans_rule h'.2 or_right)⟩

private theorem eq_zero_congr {s t : Term n} (h : QFProof (s ≡ t)) :
    Bi (s ≡ 0) (t ≡ 0) :=
  ⟨mp eq_trans (eq_symm_rule h), mp eq_trans h⟩

private theorem cond_eq_zero (c a b : Term n) :
    QFProof ((c ≡ 0) ⇒ (cond c a b ≡ 0) ⇒ a ≡ 0) :=
  eq_congr_under (cond_of_zero c a b) (weaken eq_refl)

private theorem cond_eq_zero_rev (c a b : Term n) :
    QFProof ((c ≡ 0) ⇒ (a ≡ 0) ⇒ cond c a b ≡ 0) :=
  eq_congr_under (imp_trans_rule (cond_of_zero c a b) eq_symm) (weaken eq_refl)

private theorem cond_ne_zero (c a b : Term n) :
    QFProof (∼ (c ≡ 0) ⇒ (cond c a b ≡ 0) ⇒ b ≡ 0) :=
  eq_congr_under (cond_of_ne_zero c a b) (weaken eq_refl)

private theorem cond_ne_zero_rev (c a b : Term n) :
    QFProof (∼ (c ≡ 0) ⇒ (b ≡ 0) ⇒ cond c a b ≡ 0) :=
  eq_congr_under (imp_trans_rule (cond_of_ne_zero c a b) eq_symm) (weaken eq_refl)

private theorem cond_and (c a : Term n) :
    Bi (cond c a (0 : Term n).succ ≡ 0) ((c ≡ 0) ⊓ (a ≡ 0)) := by
  constructor
  · apply cases_rule (decEq_zero c)
    · apply and_curry
      exact and_intro_under and_left
        (mp_under (imp_trans_rule and_left (cond_eq_zero c a _)) and_right)
    · apply imp_trans_under (cond_ne_zero c a _)
      exact weaken (imp_trans_rule succ_ne_zero false_elim)
  · exact mp_under (imp_trans_rule and_left (cond_eq_zero_rev c a _)) and_right

private theorem cond_or (c a : Term n) :
    Bi (cond c 0 a ≡ 0) ((c ≡ 0) ⊔ (a ≡ 0)) := by
  constructor
  · apply cases_rule (decEq_zero c)
    · exact imp_trans_rule or_left imp_imp_self
    · exact imp_trans_under (cond_ne_zero c 0 a) (weaken or_right)
  · apply or_elim_imp
    · exact mp_under (cond_eq_zero_rev c 0 a) (weaken eq_refl)
    · apply cases_under (decEq_zero c)
      · exact weaken (mp_under (cond_eq_zero_rev c 0 a) (weaken eq_refl))
      · exact imp_swap_rule (cond_ne_zero_rev c 0 a)

private theorem cond_imp (c a : Term n) :
    Bi (cond c a 0 ≡ 0) ((c ≡ 0) ⇒ a ≡ 0) := by
  constructor
  · exact imp_swap_rule (cond_eq_zero c a 0)
  · apply cases_under (decEq_zero c)
    · exact imp_swap_rule (imp_trans_under imp_apply (cond_eq_zero_rev c a 0))
    · exact weaken (mp_under (cond_ne_zero_rev c a 0) (weaken eq_refl))

/-- A QF formula and the equality of its compiled test to zero imply one another in QF-PRA. -/
public theorem test_correct (A : QFFormula n) :
    QFProof ((test A ≡ 0) ⇒ A) ∧ QFProof (A ⇒ test A ≡ 0) := by
  induction A with
  | false => exact ⟨succ_ne_zero, false_elim⟩
  | eq s t =>
    apply bi_trans (cond_and _ _)
    constructor
    · exact sub_antisymm s t
    · apply and_intro_under
      · apply eq_trans_under ?_ (weaken (sub_self t))
        exact app_congr_under (fun i => Fin.cases imp_refl
          (Fin.cases (weaken eq_refl) (fun j => Fin.elim0 j)) i)
      · apply eq_trans_under ?_ (weaken (sub_self s))
        exact app_congr_under (fun i => Fin.cases (imp_trans_rule imp_refl eq_symm)
          (Fin.cases (weaken eq_refl) (fun j => Fin.elim0 j)) i)
  | imp A B ihA ihB => exact bi_trans (cond_imp _ _) (bi_imp ihA ihB)
  | and A B ihA ihB => exact bi_trans (cond_and _ _) (bi_and ihA ihB)
  | or A B ihA ihB => exact bi_trans (cond_or _ _) (bi_or ihA ihB)

/-- `choose A s t` equals `s` when the quantifier-free formula `A` holds. -/
public theorem choose_left (A : QFFormula n) (s t : Term n) :
    QFProof (A ⇒ choose A s t ≡ s) := imp_trans_rule (test_correct A).2 (cond_of_zero _ _ _)

/-- `choose A s t` equals `t` when the negation of `A` holds. -/
public theorem choose_right (A : QFFormula n) (s t : Term n) :
    QFProof (∼ A ⇒ choose A s t ≡ t) :=
  imp_trans_rule (contrapose (test_correct A).1) (cond_of_ne_zero _ _ _)

/-- Zero equation for `recApp`: recursion at zero evaluates the base term at the parameters. -/
public theorem recApp_zero (b : Term k) (s : Term (k + 2)) (v : Fin k → Term n) :
    QFProof (recApp b s 0 v ≡ b.subst v) := eq_trans_rule app_prec_zero (QFProof.toPrimrec_eq b v)

/-- Successor equation for `recApp`: recursion at `x.succ` evaluates the step term at `x`, the
previous result `recApp b s x v`, and the parameters. -/
public theorem recApp_succ (b : Term k) (s : Term (k + 2)) (x : Term n)
    (v : Fin k → Term n) :
    QFProof (recApp b s x.succ v ≡ s.subst (Fin.cases x (Fin.cases (recApp b s x v) v))) :=
  eq_trans_rule app_prec_succ (QFProof.toPrimrec_eq s _)

end PRA.QFProof
