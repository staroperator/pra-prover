module

public import LeanPRA.Library.FOL.Common.Substitution

/-!
# Free-variable bounds of substituted syntax

`Term.bound` and `Formula.bound` count the surrounding variable positions that a code uses. This
module bounds the result of a substitution by bounds on its replacement terms. A formula whose
free variables are all replaced by closed terms is therefore a sentence.

- `Tuple.max_le_of_get_le` bounds the largest component of a tuple of positive length.
- `Term.bound_subst_le` bounds a substituted term when every replacement term is bounded.
- `Formula.bound_substWithDepth_le` bounds a formula substitution in which the replacement at
  binder depth `d` may use `d` additional positions, one for each enclosing quantifier.
- `Formula.bound_subst_le` specializes this to `Formula.subst`.
- `closeAbove L k` keeps the variables below position `k` and replaces every other variable by
  the constant with index `0`. `Formula.bound_subst_closeAbove` shows that the result uses at most
  `k` positions.
- `Formula.subst_eq_self_of_closeAbove` shows that a formula fixed by `closeAbove L k` is also
  fixed by every substitution that keeps the variables below `k`.
-/

@[expose] public section

pra

namespace Tuple

/-- A bound on every component of a tuple of positive length bounds its largest component. -/
theorem max_le_of_get_le : ∀ n xs m, 0 < n → (∀ i, i < n → get n xs i ≤ m) → max n xs ≤ m := by
  intro n xs m hn h
  have prefixes : ∀ k, k < n →
      primrec (get n xs 0) (fun i r => _root_.max r (get n xs (S i))) k ≤ m := by
    intro k
    induction k with k ih
    · intro hk
      exact h 0 hk
    · intro hk
      change _root_.max (primrec (get n xs 0) (fun i r => _root_.max r (get n xs (S i))) k)
        (get n xs (S k)) ≤ m
      have hlt : k < n := lt_of_lt_of_le k (S k) n (lt_succ_self k) (le_of_lt (S k) n hk)
      exact max_le _ _ _ (ih hlt) (h (S k) hk)
  have hz : ¬ n = 0 := by
    intro h0
    rw [h0] at hn
    exact not_lt_self 0 hn
  have hp : pred n < n := by
    have h1 := lt_succ_self (pred n)
    rw [succ_pred n hz] at h1
    exact h1
  exact prefixes (pred n) hp

end Tuple

namespace FOL

namespace Term

/-- If every replacement term uses at most `n` positions, so does the substituted term. -/
theorem bound_subst_le (f : Nat → Nat) : ∀ L n, (∀ i, bound L (f i) ≤ n) →
    ∀ t, bound L (subst f L t) ≤ n := by
  intro L n hf
  apply induction_of_bool (fun t => bound L (subst f L t) ≤ n)
    (fun t => leb (bound L (subst f L t)) n) L
  · intro t
    constructor
    · intro h
      exact and_left (leb_eq_one _ _) (and_right (bool_eq_one _ (leb_bool _ _)) h)
    · intro h
      exact and_left (bool_eq_one _ (leb_bool _ _)) (and_right (leb_eq_one _ _) h)
  · intro j hj
    rw [subst_const f L j hj, bound_const L j hj]
    exact zero_le n
  · intro i
    rw [subst_var f L i]
    exact hf i
  · intro j args hj ih
    rw [subst_app f L j args hj, bound_app L j _ hj]
    have hpos := Language.functionSymbolArity_pos L j
    apply Tuple.max_le_of_get_le _ _ n hpos
    intro i hi
    rw [Tuple.get_map (bound L) _ _ i hi, Tuple.get_map (subst f L) _ _ i hi]
    exact ih i hi

end Term

namespace Formula

/-- If the replacement terms at binder depth `d` use at most `n + d` positions, then substituting
from depth `d` produces a formula using at most `n + d` positions. -/
theorem bound_substWithDepth_le (f : Nat → Nat → Nat) : ∀ L n,
    (∀ d i, Term.bound L (f d i) ≤ n + d) →
    ∀ A d, bound L (substWithDepth f L A d) ≤ n + d := by
  intro L n hf
  apply inductionWithDepth_of_bool (fun A d => bound L (substWithDepth f L A d) ≤ n + d)
    (fun A d => leb (bound L (substWithDepth f L A d)) (n + d)) L
  · intro A d
    constructor
    · intro h
      exact and_left (leb_eq_one _ _) (and_right (bool_eq_one _ (leb_bool _ _)) h)
    · intro h
      exact and_left (bool_eq_one _ (leb_bool _ _)) (and_right (leb_eq_one _ _) h)
  · intro d
    rw [substWithDepth_falsum f L d, bound_falsum L]
    exact zero_le (n + d)
  · intro t u d
    rw [substWithDepth_equal f L t u d, bound_equal L]
    exact max_le _ _ _ (Term.bound_subst_le (f d) L (n + d) (hf d) t)
      (Term.bound_subst_le (f d) L (n + d) (hf d) u)
  · intro j xs d hj
    rw [substWithDepth_rel f L j xs d hj, bound_rel L j _ hj]
    have hpos := Language.relationSymbolArity_pos L j
    apply Tuple.max_le_of_get_le _ _ (n + d) hpos
    intro i hi
    rw [Tuple.get_map (Term.bound L) _ _ i hi, Tuple.get_map (Term.subst (f d) L) _ _ i hi]
    exact Term.bound_subst_le (f d) L (n + d) (hf d) _
  · intro A B d hA hB
    rw [substWithDepth_imp f L A B d, bound_imp L]
    exact max_le _ _ _ (hA d (le_refl d)) (hB d (le_refl d))
  · intro A d hA
    rw [substWithDepth_all f L A d, bound_all L]
    have h := hA (S d) (le_refl (S d))
    rw [add_succ] at h
    change pred (bound L (substWithDepth f L A (S d))) - (n + d) = 0
    rw [← pred_sub, ← sub_succ]
    exact h

/-- If every lifted replacement term `liftSubst f L d i` uses at most `n + d` positions, then
`Formula.subst f L A` uses at most `n` positions. -/
theorem bound_subst_le (f : Nat → Nat) : ∀ L n,
    (∀ d i, Term.bound L (FOL.liftSubst f L d i) ≤ n + d) → ∀ A, bound L (subst f L A) ≤ n := by
  intro L n hf A
  have h := bound_substWithDepth_le (FOL.liftSubst f L) L n hf A 0
  rw [add_zero] at h
  rw [subst]
  exact h

end Formula

/-- `closeAbove L k` keeps each variable below position `k` and replaces every other variable by
the constant with index `0` in language `L`. -/
def closeAbove : Nat → Nat → Nat → Nat := fun L k i =>
  ite (ltb i k) (Term.var L i) (Term.const L 0)

theorem closeAbove_of_lt : ∀ L k i, i < k → closeAbove L k i = Term.var L i := by
  intro L k i h
  rw [closeAbove, and_right (ltb_eq_one i k) h, ite_succ]

theorem closeAbove_of_ge : ∀ L k i, k ≤ i → closeAbove L k i = Term.const L 0 := by
  intro L k i h
  rw [closeAbove, ltb_eq_zero_of_ge i k h, ite_zero]

/-- Beneath `d` binders, a replacement term of `closeAbove L k` uses at most `k + d` positions. -/
theorem bound_liftSubst_closeAbove : ∀ L k, 0 < Language.constants L →
    ∀ d i, Term.bound L (liftSubst (closeAbove L k) L d i) ≤ k + d := by
  intro L k hc d i
  by_cases hi : i < d
  · rw [liftSubst_of_lt (closeAbove L k) L d i hi, Term.bound_var L i]
    exact le_trans (S i) d (k + d) hi (le_add_left k d)
  · have hd := le_of_not_lt d i hi
    rw [liftSubst_of_le (closeAbove L k) L d i hd]
    by_cases hk : i - d < k
    · rw [closeAbove_of_lt L k (i - d) hk, Term.shift_var L d (i - d),
        sub_add_cancel_of_le i d hd, Term.bound_var L i]
      have h := and_left (sub_lt_iff i d k hd) hk
      rw [add_comm d k] at h
      exact h
    · rw [closeAbove_of_ge L k (i - d) (le_of_not_lt k (i - d) hk), Term.shift,
        Term.subst_const (fun n => Term.var L (n + d)) L 0 (Language.isConstant_of_lt L 0 hc),
        Term.bound_const L 0 (Language.isConstant_of_lt L 0 hc)]
      exact zero_le (k + d)

namespace Formula

/-- Replacing every variable at position `k` or above by a constant leaves at most `k` free
positions. -/
theorem bound_subst_closeAbove : ∀ L k, 0 < Language.constants L → ∀ A,
    bound L (subst (closeAbove L k) L A) ≤ k :=
  fun L k hc A => bound_subst_le (closeAbove L k) L k (bound_liftSubst_closeAbove L k hc) A

/-- A formula fixed by `closeAbove L k` is fixed by every substitution that keeps the variables
below `k`. -/
theorem subst_eq_self_of_closeAbove (g : Nat → Nat) : ∀ L k A, 0 < Language.constants L →
    (∀ i, i < k → g i = Term.var L i) → subst (closeAbove L k) L A = A → subst g L A = A := by
  intro L k A hc hg hA
  have pointwise : ∀ i, Term.subst g L (closeAbove L k i) = closeAbove L k i := by
    intro i
    by_cases hi : i < k
    · rw [closeAbove_of_lt L k i hi, Term.subst_var g L i]
      exact hg i hi
    · rw [closeAbove_of_ge L k i (le_of_not_lt k i hi),
        Term.subst_const g L 0 (Language.isConstant_of_lt L 0 hc)]
  rw [← hA, subst_comp g (closeAbove L k) L A]
  exact subst_congr (fun i => Term.subst g L (closeAbove L k i)) (closeAbove L k) L pointwise A

end Formula

end FOL

end
