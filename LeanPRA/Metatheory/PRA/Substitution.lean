module

public import LeanPRA.Metatheory.PRA.Defs

/-!
# Substitution identities for PRA syntax

Identities for simultaneous substitution, shifting, and variable instantiation on PRA terms and
formulas:

- `Term.subst_id` and `Term.subst_comp` give identity and composition laws for term substitution.
- `Term.subst_zero`, `Term.subst_succ`, `Term.subst_app₁`, and `Term.subst_app₂` commute
  substitution with constants, successor, and function applications.
- `QFFormula.subst_id`, `QFFormula.subst_comp`, `QFFormula.inst_subst`, and
  `QFFormula.replace_subst` give the corresponding laws for quantifier-free formulas.
- `QFFormula.toFormula_subst` commutes the embedding into `Formula` with substitution.
- `Formula.subst_id`, `Formula.subst_comp`, `Formula.subst_inst`, and `Formula.replace_subst`
  give substitution laws for quantified formulas.
- `Formula.quantifierFree_subst` shows that substitution preserves `Formula.QuantifierFree`, and
  `Formula.quantifierFree_image` lifts a quantifier-free `Formula` back to `QFFormula`.
-/

namespace Fin

public theorem map_cases (f : α → β) (a : α) (v : Fin n → α) :
    (fun i => f (Fin.cases a v i)) = Fin.cases (f a) (fun i => f (v i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

public theorem map_elim0 (f : α → β) : (fun i => f (Fin.elim0 i)) = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

public theorem cases_one (a : α) (v : Fin (n + 1) → α) : Fin.cases a v 1 = v 0 := rfl

public theorem cases_two (a : α) (v : Fin (n + 2) → α) : Fin.cases a v 2 = v 1 := rfl

public theorem cases_fin_one (a : α) (v : Fin 0 → α) (i : Fin 1) :
    Fin.cases a v i = a :=
  Fin.cases rfl (fun j => Fin.elim0 j) i

end Fin

namespace PRA.Term

/-- Substitution by the variables leaves a term unchanged. -/
@[simp] public theorem subst_id (t : Term n) : t.subst Term.var = t := by
  induction t with
  | var i => rfl
  | app f v ih =>
    change Term.app f (fun i => (v i).subst Term.var) = Term.app f v
    exact congrArg (Term.app f) (funext ih)

/-- Successive term substitutions compose pointwise. -/
public theorem subst_comp (t : Term n) (v : Fin n → Term m) (w : Fin m → Term k) :
    (t.subst v).subst w = t.subst (fun i => (v i).subst w) := by
  induction t with
  | var i => rfl
  | app f u ih =>
    change Term.app f (fun i => ((u i).subst v).subst w) =
      Term.app f (fun i => (u i).subst (fun j => (v j).subst w))
    exact congrArg (Term.app f) (funext (fun i => ih i v))

@[simp] public theorem subst_nat (c : Nat) (v : Fin n → Term m) :
    (OfNat.ofNat c : Term n).subst v = OfNat.ofNat c := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext i
  exact Fin.elim0 i

@[simp] public theorem subst_zero (v : Fin n → Term m) : (0 : Term n).subst v = 0 :=
  subst_nat 0 v

public theorem subst_app₁ {m} (f : Primrec 1) (t : Term n) (v : Fin n → Term m) :
    (Term.app₁ f t).subst v = Term.app₁ f (t.subst v) := by
  simp only [Term.app₁, Term.subst, Fin.map_cases (fun t => Term.subst t v),
    Fin.map_elim0 (fun t => Term.subst t v)]

public theorem subst_app₂ {m} (f : Primrec 2) (s t : Term n)
    (v : Fin n → Term m) :
    (Term.app₂ f s t).subst v = Term.app₂ f (s.subst v) (t.subst v) := by
  simp only [Term.app₂, Term.subst, Fin.map_cases (fun t => Term.subst t v),
    Fin.map_elim0 (fun t => Term.subst t v)]

@[simp] public theorem subst_succ (t : Term n) (v : Fin n → Term m) :
    t.succ.subst v = (t.subst v).succ :=
  subst_app₁ Primrec.succ t v

end PRA.Term

namespace PRA.QFFormula

/-- Substitution by the variables leaves a quantifier-free formula unchanged. -/
public theorem subst_id (A : QFFormula n) : A.subst Term.var = A := by
  induction A with
  | false => rfl
  | eq s t => simp only [QFFormula.subst, Term.subst_id]
  | imp _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ =>
    simp only [QFFormula.subst, ih₁, ih₂]

/-- Successive substitutions on a quantifier-free formula compose pointwise. -/
public theorem subst_comp (A : QFFormula k) (v : Fin k → Term n)
    (w : Fin n → Term m) :
    (A.subst v).subst w = A.subst (fun i => (v i).subst w) := by
  induction A with
  | false => rfl
  | eq s t => simp only [QFFormula.subst, Term.subst_comp]
  | imp _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ =>
    simp only [QFFormula.subst, ih₁, ih₂]

end PRA.QFFormula

namespace PRA.Term

@[simp] public theorem subst_shift (t : Term n) (v : Fin (n + 1) → Term m) :
    t.shift.subst v = t.subst (fun i => v i.succ) := by
  simp only [shift, subst_comp, Function.comp_apply, subst]

@[simp] public theorem inst_shift (t u : Term n) : t.shift.inst u = t := by
  simp only [inst, subst_shift, Fin.cases_succ, subst_id]

end PRA.Term

namespace PRA.Formula

/-- Substitution by the variables leaves a formula unchanged, including under binders. -/
@[simp] public theorem subst_id (φ : Formula n) : φ.subst Term.var = φ := by
  induction φ with
  | false => rfl
  | eq s t => simp [subst]
  | imp φ ψ ihφ ihψ | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp [subst, ihφ, ihψ]
  | @all n φ ih | @ex n φ ih =>
    simp only [subst]
    congr 1
    have hv : (Fin.cases (Term.var 0) fun i =>
        (Term.var i).shift) = @Term.var (n + 1) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hv, ih]

/-- Successive formula substitutions compose, with bound variables protected at each binder. -/
public theorem subst_comp (φ : Formula n) (v : Fin n → Term m) (w : Fin m → Term k) :
    (φ.subst v).subst w = φ.subst (fun i => (v i).subst w) := by
  induction φ generalizing m k with
  | false => rfl
  | eq s t => simp [subst, Term.subst_comp]
  | imp φ ψ ihφ ihψ | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp [subst, ihφ, ihψ]
  | all φ ih | ex φ ih =>
    simp only [subst, ih]
    congr 2
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp only [Fin.cases_succ, Term.shift, Term.subst_comp]
    congr 1

public theorem subst_congr (φ : Formula n) {v w : Fin n → Term m} (h : ∀ i, v i = w i) :
    φ.subst v = φ.subst w :=
  congrArg (subst φ) (funext h)

@[simp] public theorem subst_shift (φ : Formula n) (v : Fin (n + 1) → Term m) :
    φ.shift.subst v = φ.subst (fun i => v i.succ) := by
  simp only [shift, subst_comp, Function.comp_apply, Term.subst]

public theorem shift_subst (φ : Formula n) (v : Fin n → Term m) :
    (φ.subst v).shift = φ.subst (fun i => (v i).shift) :=
  subst_comp φ v (Term.var ∘ Fin.succ)

@[simp] public theorem inst_shift (φ : Formula n) (t : Term n) : φ.shift.inst t = φ := by
  simp only [inst, subst_shift, Fin.cases_succ, subst_id]

public theorem inst_subst (φ : Formula (n + 1)) (v : Fin n → Term m) (t : Term m) :
    (φ.subst (Fin.cases (.var 0) fun i => (v i).shift)).inst t =
      φ.subst (Fin.cases t v) := by
  rw [inst, subst_comp]
  apply subst_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  exact Term.inst_shift (v j) t

public theorem subst_inst (φ : Formula (n + 1)) (t : Term n) (v : Fin n → Term m) :
    (φ.inst t).subst v =
      (φ.subst (Fin.cases (.var 0) fun i => (v i).shift)).inst (t.subst v) := by
  rw [inst_subst, inst, subst_comp]
  apply subst_congr
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] public theorem replace_var (φ : Formula (n + 1)) : φ.replace (.var 0) = φ := by
  unfold replace
  apply Eq.trans (subst_congr φ ?_) (subst_id φ)
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

public theorem subst_replace (φ : Formula (n + 1)) (t : Term (n + 1))
    (v : Fin (n + 1) → Term m) :
    (φ.replace t).subst v =
      φ.subst (Fin.cases (t.subst v) fun i => v i.succ) := by
  rw [replace, subst_comp]
  apply subst_congr
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

public theorem replace_subst (φ : Formula (n + 1)) (v : Fin n → Term m) (t : Term (m + 1)) :
    (φ.subst (Fin.cases (.var 0) fun i => (v i).shift)).replace t =
      φ.subst (Fin.cases t fun i => (v i).shift) := by
  rw [replace, subst_comp]
  apply subst_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Fin.cases_succ, Term.subst_shift]
  rfl

/-- Substitution preserves the quantifier-free property of a formula. -/
@[simp] public theorem quantifierFree_subst (φ : Formula n) (v : Fin n → Term m) :
    (φ.subst v).QuantifierFree ↔ φ.QuantifierFree := by
  induction φ generalizing m with
  | false | eq | all | ex => rfl
  | imp φ ψ ihφ ihψ | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [subst, QuantifierFree, ihφ, ihψ]

/-- Instantiating the shifted body of a universal formula at the new variable restores its body. -/
@[simp] public theorem inst_shift_all (φ : Formula (n + 1)) :
    (φ.subst (Fin.cases (.var 0) fun i => .var (Fin.succ (Fin.succ i)))).inst (.var 0) =
      φ := by
  simp only [inst, subst_comp]
  apply Eq.trans (congrArg (subst φ) ?_) (subst_id φ)
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

end PRA.Formula

namespace PRA.QFFormula

public theorem subst_replace (A : QFFormula (k + 1)) (t : Term (k + 1))
    (v : Fin (k + 1) → Term n) :
    (A.replace t).subst v = A.subst (Fin.cases (t.subst v) (fun i => v i.succ)) := by
  simp only [QFFormula.replace, QFFormula.subst_comp, Fin.map_cases (fun t => Term.subst t v),
    Term.subst, Function.comp_apply]

public theorem subst_shift (A : QFFormula n) (v : Fin (n + 1) → Term m) :
    A.shift.subst v = A.subst (fun i => v i.succ) := by
  simp only [QFFormula.shift, QFFormula.subst_comp, Term.subst, Function.comp_apply]

public theorem subst_inst (A : QFFormula (k + 1)) (t : Term k)
    (v : Fin k → Term n) : (A.inst t).subst v = A.subst (Fin.cases (t.subst v) v) := by
  simp only [QFFormula.inst, QFFormula.subst_comp,
    Fin.map_cases (fun t => Term.subst t v), Term.subst]

public theorem subst_cons (A : QFFormula (k + 1)) (t : Term n)
    (v : Fin k → Term n) (w : Fin n → Term m) :
    (A.subst (Fin.cases t v)).subst w =
      A.subst (Fin.cases (t.subst w) (fun i => (v i).subst w)) := by
  rw [QFFormula.subst_comp]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Embedding a quantifier-free formula into the quantified syntax commutes with substitution. -/
public theorem toFormula_subst (A : QFFormula n) (v : Fin n → Term m) :
    (A.subst v).toFormula = A.toFormula.subst v := by
  induction A with
  | false | eq => rfl
  | imp _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ =>
    simp only [subst, toFormula, Formula.subst, ih₁, ih₂]

/-- Every embedded quantifier-free formula satisfies `Formula.QuantifierFree`. -/
public theorem toFormula_qf (A : QFFormula n) : A.toFormula.QuantifierFree := by
  induction A with
  | false | eq => trivial
  | imp _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

/-- Instantiating a shifted quantifier-free formula at any term restores the original formula. -/
public theorem inst_shift (A : QFFormula n) (t : Term n) : A.shift.inst t = A := by
  simp only [QFFormula.shift, QFFormula.inst, QFFormula.subst_comp,
    Function.comp_apply, Term.subst, Fin.cases_succ, QFFormula.subst_id]

/-- Instantiating variable zero after a lifted substitution substitutes at variable zero and
applies the remaining substitution. -/
public theorem inst_subst (A : QFFormula (k + 1)) (v : Fin k → Term n) (t : Term n) :
    (A.subst (Fin.cases (.var 0) (fun i => (v i).shift))).inst t =
      A.subst (Fin.cases t v) := by
  rw [QFFormula.inst, QFFormula.subst_comp]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Term.inst_shift (v j) t

/-- Replacing variable zero after a lifted substitution replaces variable zero in the lifted
substitution. -/
public theorem replace_subst (A : QFFormula (k + 1)) (v : Fin k → Term n)
    (t : Term (n + 1)) :
    (A.subst (Fin.cases (.var 0) (fun i => (v i).shift))).replace t =
      A.subst (Fin.cases t (fun i => (v i).shift)) := by
  rw [QFFormula.replace, QFFormula.subst_comp]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Fin.cases_succ, Term.subst_shift]
  rfl

end PRA.QFFormula

namespace PRA.Formula

/-- Every formula satisfying `Formula.QuantifierFree` is the image of a `QFFormula`. -/
public theorem quantifierFree_image {A : Formula k} (h : A.QuantifierFree) :
    ∃ B : QFFormula k, B.toFormula = A := by
  induction A with
  | false => exact ⟨.false, rfl⟩
  | eq s t => exact ⟨.eq s t, rfl⟩
  | imp A B ihA ihB =>
    obtain ⟨A', rfl⟩ := ihA h.1
    obtain ⟨B', rfl⟩ := ihB h.2
    exact ⟨.imp A' B', rfl⟩
  | and A B ihA ihB =>
    obtain ⟨A', rfl⟩ := ihA h.1
    obtain ⟨B', rfl⟩ := ihB h.2
    exact ⟨.and A' B', rfl⟩
  | or A B ihA ihB =>
    obtain ⟨A', rfl⟩ := ihA h.1
    obtain ⟨B', rfl⟩ := ihB h.2
    exact ⟨.or A' B', rfl⟩
  | all | ex => contradiction

end PRA.Formula
