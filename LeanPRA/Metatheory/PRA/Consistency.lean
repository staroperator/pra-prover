module

public import LeanPRA.Metatheory.PRA.Substitution

/-!
# Consistency of first-order PRA

`consistent` states that first-order PRA cannot derive falsity (`¬ Proof ⊥`). The proof evaluates
primitive recursive expressions, terms, and formulas in Lean's `Nat` and `Prop`, and shows by
induction on derivations that every theorem of `Proof` holds under all variable assignments.
-/

namespace PRA

private def evalPrimrec : {n : Nat} → Primrec n → (Fin n → Nat) → Nat
  | _, .zero, _ => 0
  | _, .proj i, v => v i
  | _, .succ, v => v 0 + 1
  | _, .comp f g, v => evalPrimrec f (fun i => evalPrimrec (g i) v)
  | _, .prec f g, v =>
      Nat.rec (evalPrimrec f (fun i => v i.succ))
        (fun i a => evalPrimrec g (Fin.cases i (Fin.cases a (fun j => v j.succ)))) (v 0)

private def evalTerm : {n : Nat} → Term n → (Fin n → Nat) → Nat
  | _, .var i, v => v i
  | _, .app f ts, v => evalPrimrec f (fun i => evalTerm (ts i) v)

private def evalFormula : {n : Nat} → Formula n → (Fin n → Nat) → Prop
  | _, .false, _ => False
  | _, .eq s t, v => evalTerm s v = evalTerm t v
  | _, .imp A B, v => evalFormula A v → evalFormula B v
  | _, .and A B, v => evalFormula A v ∧ evalFormula B v
  | _, .or A B, v => evalFormula A v ∨ evalFormula B v
  | _, .all A, v => ∀ a, evalFormula A (Fin.cases a v)
  | _, .ex A, v => ∃ a, evalFormula A (Fin.cases a v)

private theorem evalTerm_subst (t : Term n) (s : Fin n → Term m) (v : Fin m → Nat) :
    evalTerm (t.subst s) v = evalTerm t (fun i => evalTerm (s i) v) := by
  induction t with
  | var i => rfl
  | app f ts ih => simp only [Term.subst, evalTerm, ih]

private theorem evalTerm_shift (t : Term n) (a : Nat) (v : Fin n → Nat) :
    evalTerm t.shift (Fin.cases a v) = evalTerm t v := by
  simp only [Term.shift, evalTerm_subst, Function.comp_apply, evalTerm, Fin.cases_succ]

private theorem evalTerm_cases (t : Term n) (ts : Fin k → Term n) (v : Fin n → Nat) :
    (fun i => evalTerm (Fin.cases t ts i) v) =
      Fin.cases (evalTerm t v) (fun i => evalTerm (ts i) v) :=
  Fin.map_cases (fun t => evalTerm t v) t ts

private theorem evalFormula_subst (A : Formula n) (s : Fin n → Term m) (v : Fin m → Nat) :
    evalFormula (A.subst s) v = evalFormula A (fun i => evalTerm (s i) v) := by
  induction A generalizing m with
  | false => rfl
  | eq t u => simp only [Formula.subst, evalFormula, evalTerm_subst]
  | imp A B ihA ihB | and A B ihA ihB | or A B ihA ihB =>
      simp only [Formula.subst, evalFormula, ihA, ihB]
  | all A ih | ex A ih =>
      simp only [Formula.subst, evalFormula, ih, evalTerm_cases, evalTerm, Fin.cases_zero,
        evalTerm_shift]

private theorem evalFormula_shift (A : Formula n) (a : Nat) (v : Fin n → Nat) :
    evalFormula A.shift (Fin.cases a v) = evalFormula A v := by
  simp only [Formula.shift, evalFormula_subst, Function.comp_apply, evalTerm, Fin.cases_succ]

private theorem evalFormula_inst (A : Formula (n + 1)) (t : Term n) (v : Fin n → Nat) :
    evalFormula (A.inst t) v = evalFormula A (Fin.cases (evalTerm t v) v) := by
  simp only [Formula.inst, evalFormula_subst, evalTerm_cases, evalTerm]

private theorem evalTerm_zero (v : Fin n → Nat) : evalTerm (0 : Term n) v = 0 := rfl

private theorem evalTerm_succ (t : Term n) (v : Fin n → Nat) :
    evalTerm t.succ v = evalTerm t v + 1 := rfl

private theorem evalFormula_replace (A : Formula (n + 1)) (t : Term (n + 1))
    (a : Nat) (v : Fin n → Nat) :
    evalFormula (A.replace t) (Fin.cases a v) =
      evalFormula A (Fin.cases (evalTerm t (Fin.cases a v)) v) := by
  simp only [Formula.replace, evalFormula_subst, evalTerm_cases, Function.comp_apply,
    evalTerm, Fin.cases_succ]

private theorem proof_sound {A : Formula n} (h : Proof A) (v : Fin n → Nat) : evalFormula A v := by
  classical
  induction h with
  | imp_imp_self => exact fun a _ => a
  | imp_distrib => exact fun f g a => f a (g a)
  | imp_contra =>
      intro h b
      exact Classical.byContradiction (fun na => h na b)
  | and_intro => exact And.intro
  | and_left => exact And.left
  | and_right => exact And.right
  | or_left => exact Or.inl
  | or_right => exact Or.inr
  | or_elim => exact fun f g h => h.elim f g
  | mp _ _ ihf iha => exact ihf v (iha v)
  | forall_elim =>
      intro h
      rw [evalFormula_inst]
      exact h _
  | forall_imp =>
      intro h a x
      exact h x ((evalFormula_shift _ _ _).symm ▸ a)
  | exists_intro =>
      intro h
      rw [evalFormula_inst] at h
      exact ⟨_, h⟩
  | exists_elim =>
      intro h ⟨x, hx⟩
      exact evalFormula_shift _ _ _ ▸ h x hx
  | gen _ ih => exact fun a => ih (Fin.cases a v)
  | eq_refl => rfl
  | eq_symm => exact Eq.symm
  | eq_trans => exact Eq.trans
  | eq_congr_ith =>
      intro h
      simp only [evalFormula, evalTerm]
      congr 1
      funext j
      split <;> rename_i hj
      · subst j
        exact h
      · rfl
  | succ_ne_zero => exact Nat.succ_ne_zero _
  | succ_inj => exact Nat.succ.inj
  | app_proj => rfl
  | app_comp => rfl
  | app_prec_zero =>
      simp only [evalFormula, evalTerm, evalPrimrec, evalTerm_zero, Fin.cases_zero,
        Fin.cases_succ]
      rfl
  | app_prec_succ =>
      simp only [evalFormula, evalTerm, evalTerm_cases, evalPrimrec, evalTerm_succ, Fin.cases_zero,
        Fin.cases_succ]
  | induction qf =>
      intro base step a
      rw [evalFormula_inst, evalTerm_zero] at base
      induction a with
      | zero => exact base
      | succ a ih =>
          have next := step a ih
          rw [evalFormula_replace, evalTerm_succ] at next
          exact next

/-- First-order PRA cannot derive falsity. -/
public theorem consistent {n : Nat} : ¬ Proof (.false : Formula n) :=
  fun h => proof_sound h (fun _ => 0)

end PRA
