module

public import LeanPRA.Library.Nat.Bounded

/-!
# Division and remainder in PRA

Euclidean division and remainder on `Nat`:

- `div` (`/`) finds the quotient `x / d` as the first `q ≤ x` with `x < d * S q` when `¬ d = 0`,
  and returns `0` when `d = 0`.
- `mod` (`%`) computes the remainder `x - d * (x / d)`, with `x % 0 = x`.

For a nonzero divisor `d`, `d * (x / d) + x % d = x` and `x % d < d`, and these conditions uniquely
determine both `x / d` and `x % d`.
-/

@[expose] public section

pra

/-- The quotient `x / d` (with `x / 0 = 0`). -/
def div : Nat → Nat → Nat :=
  fun x d => ite d (findBelow (fun q => ltb x (d * S q)) (S x)) 0

infixl:70 " / " => div

/-- The remainder `x % d = x - d * (x / d)` (with `x % 0 = x`). -/
def mod : Nat → Nat → Nat := fun x d => x - d * div x d

infixl:70 " % " => mod

theorem div_zero : ∀ x, div x 0 = 0 := fun x => rfl

theorem div_of_ne_zero : ∀ x d, ¬ d = 0 →
    div x d = findBelow (fun q => ltb x (d * S q)) (S x) := by
  intro x d hd
  exact ite_of_ne_zero d _ 0 hd

theorem mod_zero : ∀ x, mod x 0 = x := by
  intro x
  change x - 0 * div x 0 = x
  rw [zero_mul, sub_zero]

theorem zero_mod : ∀ x, 0 % x = 0 := by
  intro x
  exact zero_sub (x * (0 / x))

/-- For `¬ d = 0`, `x` lies between `d * (x / d)` and `d * S (x / d)`. -/
theorem div_bounds : ∀ x d, ¬ d = 0 →
    d * div x d ≤ x ∧ x < d * S (div x d) := by
  intro x d hd
  have witness : ¬ ltb x (d * S x) = 0 := by
    apply and_left (bool_eq_one _ (ltb_bool _ _))
    apply and_right (ltb_eq_one _ _)
    exact lt_of_lt_of_le x (S x) (d * S x) (lt_succ_self x)
      (le_mul_of_pos (S x) d hd)
  have hq : div x d < S x := by
    rw [div_of_ne_zero x d hd]
    exact lt_of_le_of_lt _ x (S x)
      (findBelow_le_of_witness (fun q => ltb x (d * S q)) x (S x) witness)
      (lt_succ_self x)
  constructor
  · rcases zero_or_succ_pred (div x d) with hz | hs
    · rw [hz, mul_zero]; exact zero_le x
    · have hp : pred (div x d) < findBelow (fun q => ltb x (d * S q)) (S x) := by
        rw [← div_of_ne_zero x d hd, hs]
        exact lt_succ_self (pred (div x d))
      have hf := findBelow_min (fun q => ltb x (d * S q))
        (pred (div x d)) (S x) hp
      rw [← hs] at hf
      exact le_of_not_lt _ x (and_left (ltb_eq_zero _ _) hf)
  · apply and_left (ltb_eq_one _ _)
    apply and_right (bool_eq_one _ (ltb_bool _ _))
    rw [div_of_ne_zero x d hd] at hq
    rw [div_of_ne_zero x d hd]
    exact findBelow_spec (fun q => ltb x (d * S q)) (S x) hq

theorem div_mul_le_self : ∀ x d, x / d * d ≤ x := by
  intro x d
  by_cases hd : d = 0
  · rw [hd, mul_zero]; exact zero_le x
  · rw [mul_comm]
    exact and_left (div_bounds x d hd)

theorem div_le_self : ∀ x d, x / d ≤ x := by
  intro x d
  by_cases hd : d = 0
  · rw [hd, div_zero]; exact zero_le x
  · exact le_trans (x / d) (d * (x / d)) x
      (le_mul_of_pos (x / d) d hd) (and_left (div_bounds x d hd))

theorem mod_le : ∀ x d, x % d ≤ x :=
  fun x d => sub_le x (d * (x / d))

/-- Quotient and remainder reconstruct the dividend, including for a zero divisor. -/
theorem div_mod : ∀ x d, d * div x d + mod x d = x := by
  intro x d
  change d * div x d + (x - d * div x d) = x
  rw [add_comm]
  by_cases hd : d = 0
  · rw [hd, zero_mul, sub_zero, add_zero]
  · exact sub_add_cancel_of_le x (d * div x d) (and_left (div_bounds x d hd))

theorem mod_add_div : ∀ x d, x % d + d * (x / d) = x := by
  intro x d
  rw [add_comm]
  exact div_mod x d

/-- For a positive divisor, the remainder is strictly smaller than it. -/
theorem mod_lt : ∀ x d, ¬ d = 0 → mod x d < d := by
  intro x d hd
  apply lt_of_add_lt_add_left (mod x d) d (d * div x d)
  rw [div_mod, ← mul_succ]
  exact and_right (div_bounds x d hd)

/-- For `¬ d = 0`, `x / d` and `x % d` are the unique `q` and `r < d` with `d * q + r = x`. -/
theorem div_mod_unique : ∀ x d q r, ¬ d = 0 → d * q + r = x → r < d →
    div x d = q ∧ mod x d = r := by
  intro x d q r hd he hr
  have hq : div x d = q := by
    apply le_antisymm (div x d) q
    · apply le_of_not_lt (div x d) q
      intro h
      have hlo := mul_le_mul_left (S q) (div x d) d h
      have hhi : x < d * S q := by
        rw [← he, mul_succ]
        exact add_lt_add_left r d (d * q) hr
      exact not_le_of_lt x (d * S q) hhi
        (le_trans _ _ x hlo (and_left (div_bounds x d hd)))
    · apply le_of_not_lt q (div x d)
      intro h
      have hlo := mul_le_mul_left (S (div x d)) q d h
      have hx : d * q ≤ x := by
        rw [← he]; exact le_add_right (d * q) r
      exact not_le_of_lt x (d * S (div x d)) (and_right (div_bounds x d hd))
        (le_trans _ _ x hlo hx)
  constructor
  · exact hq
  · apply add_left_cancel (d * q) (mod x d) r
    have hm := div_mod x d
    rw [hq] at hm
    exact eq_trans hm (eq_symm he)

theorem div_lt : ∀ x d, x < d → div x d = 0 := by
  intro x d h
  have hd : ¬ d = 0 := by
    intro he; rw [he] at h; exact not_lt_zero x h
  refine and_left (div_mod_unique x d 0 x hd ?_ h)
  rw [mul_zero, zero_add]

theorem zero_div : ∀ x, 0 / x = 0 := by
  intro x
  by_cases hx : x = 0
  · rw [hx, div_zero]
  · exact div_lt 0 x (pos_of_ne_zero x hx)

theorem div_eq_zero_iff_lt : ∀ x d, ¬ d = 0 → (x / d = 0 ↔ x < d) := by
  intro x d hd
  constructor
  · intro h
    have bound := and_right (div_bounds x d hd)
    rw [h, mul_one] at bound
    exact bound
  · exact div_lt x d

theorem div_pos_iff : ∀ x d, ¬ d = 0 → (0 < x / d ↔ d ≤ x) := by
  intro x d hd
  constructor
  · intro h
    apply le_of_not_lt d x
    intro hlt
    exact ne_zero_of_pos (x / d) h (div_lt x d hlt)
  · intro h
    apply pos_of_ne_zero (x / d)
    intro hz
    exact not_le_of_lt x d (and_left (div_eq_zero_iff_lt x d hd) hz) h

theorem mod_of_lt : ∀ x d, x < d → mod x d = x := by
  intro x d h
  change x - d * div x d = x
  rw [div_lt x d h, mul_zero, sub_zero]

theorem mod_eq_self_iff_lt : ∀ x d, ¬ d = 0 → (x % d = x ↔ x < d) := by
  intro x d hd
  constructor
  · intro h
    have bound := mod_lt x d hd
    rw [h] at bound
    exact bound
  · exact mod_of_lt x d

theorem mod_mod : ∀ x d, x % d % d = x % d := by
  intro x d
  by_cases hd : d = 0
  · rw [hd, mod_zero]
  · exact mod_of_lt (x % d) d (mod_lt x d hd)

theorem div_one : ∀ x, div x 1 = x := by
  intro x
  refine and_left (div_mod_unique x 1 x 0 (succ_ne_zero 0) ?_ (lt_succ_self 0))
  rw [one_mul, add_zero]

theorem mod_one : ∀ x, mod x 1 = 0 := by
  intro x
  change x - 1 * div x 1 = 0
  rw [div_one, one_mul, sub_self]

theorem div_self : ∀ x, ¬ x = 0 → x / x = 1 := by
  intro x hx
  refine and_left (div_mod_unique x x 1 0 hx ?_ (pos_of_ne_zero x hx))
  rw [mul_one, add_zero]

theorem mod_self : ∀ x, x % x = 0 := by
  intro x
  by_cases hx : x = 0
  · rw [hx, mod_zero]
  · change x - x * (x / x) = 0
    rw [div_self x hx, mul_one, sub_self]

theorem div_mul : ∀ d q, ¬ d = 0 → div (d * q) d = q := by
  intro d q hd
  exact and_left (div_mod_unique (d * q) d q 0 hd rfl (pos_of_ne_zero d hd))

theorem mod_mul : ∀ d q, mod (d * q) d = 0 := by
  intro d q
  by_cases hd : d = 0
  · rw [hd, zero_mul, mod_zero]
  · exact and_right (div_mod_unique (d * q) d q 0 hd rfl (pos_of_ne_zero d hd))

theorem div_add_mul : ∀ x d k, ¬ d = 0 → div (x + d * k) d = div x d + k := by
  intro x d k hd
  refine and_left (div_mod_unique (x + d * k) d (div x d + k) (mod x d) hd ?_
    (mod_lt x d hd))
  rw [mul_add_left_distrib, add_right_comm, div_mod]

theorem mod_add_mul : ∀ x d k, mod (x + d * k) d = mod x d := by
  intro x d k
  by_cases hd : d = 0
  · rw [hd, zero_mul, add_zero]
  · refine and_right (div_mod_unique (x + d * k) d (div x d + k) (mod x d) hd ?_
      (mod_lt x d hd))
    rw [mul_add_left_distrib, add_right_comm, div_mod]

theorem div_mod_succ_of_lt : ∀ x d, S (mod x d) < d →
    div (S x) d = div x d ∧ mod (S x) d = S (mod x d) := by
  intro x d h
  have hd : ¬ d = 0 := by
    intro he; rw [he] at h; exact not_lt_zero _ h
  apply div_mod_unique (S x) d (div x d) (S (mod x d)) hd
  · rw [add_succ, div_mod]
  · exact h

theorem div_mod_succ_of_eq : ∀ x d, S (mod x d) = d →
    div (S x) d = S (div x d) ∧ mod (S x) d = 0 := by
  intro x d h
  have hd : ¬ d = 0 := by
    intro he
    exact succ_ne_zero (mod x d) (eq_trans h he)
  apply div_mod_unique (S x) d (S (div x d)) 0 hd
  · have he := eq_congr S (div_mod x d)
    rw [← add_succ, h] at he
    rw [add_zero, mul_succ]
    exact he
  · exact pos_of_ne_zero d hd

end
