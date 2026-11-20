module

public import LeanPRA.Library.Nat.Bounded

/-!
# Division and remainder in PRA

Euclidean division and remainder on `Nat`:

- `div` (`/`) finds the quotient `x / d` as the first `q ≤ x` with `x < d * S q` when `¬ d = 0`,
  and returns `0` when `d = 0`.
- `mod` (`%`) computes the remainder `x - d * (x / d)`, with `x % 0 = x`.
- `mod_add_eq` and `mod_mul_eq` reduce sums and products to their remainders.
- `factorial_mod`, `product_mod_one`, and `product_mod_zero` give remainders of finite products.

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
  rw [mod, zero_mul, sub_zero]

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
  rw [mod, add_comm]
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

theorem div_mul_add_of_lt : ∀ d q r, ¬ d = 0 → r < d → (d * q + r) / d = q := by
  intro d q r hd hr
  exact and_left (div_mod_unique (d * q + r) d q r hd rfl hr)

theorem mod_mul_add_of_lt : ∀ d q r, ¬ d = 0 → r < d → (d * q + r) % d = r := by
  intro d q r hd hr
  exact and_right (div_mod_unique (d * q + r) d q r hd rfl hr)

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
  rw [mod, div_lt x d h, mul_zero, sub_zero]

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
  rw [mod, div_one, one_mul, sub_self]

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

/-! ## Remainder identities and finite products -/

theorem mod_add_eq (a b d : Nat) : (a + b) % d = (a % d + b % d) % d := by
  have h : (a % d + b % d) + d * (a / d + b / d) = a + b := by
    rw [mul_add_left_distrib, add_add_add_comm,
      add_comm (a % d) (d * (a / d)), add_comm (b % d) (d * (b / d)), div_mod, div_mod]
  rw [← h, mod_add_mul]

theorem mod_mul_left (a b d : Nat) : (a * b) % d = ((a % d) * b) % d := by
  have h : (a % d) * b + d * ((a / d) * b) = a * b := by
    rw [← mul_assoc, ← mul_add_right_distrib, add_comm, div_mod]
  rw [← h, mod_add_mul]

theorem mod_mul_eq (a b d : Nat) : (a * b) % d = ((a % d) * (b % d)) % d := by
  rw [mod_mul_left a b d, mul_comm (a % d) b, mod_mul_left b (a % d) d,
    mul_comm (b % d) (a % d)]

theorem mod_eq_of_add_mul_eq (a b m u v : Nat) : a + m * u = b + m * v → a % m = b % m := by
  intro h
  have hm := eq_congr (fun x => x % m) h
  rw [mod_add_mul, mod_add_mul] at hm
  exact hm

theorem inverse_of_negative (a u v k : Nat) :
    a * u + 1 = S k * v → (a * (k * u)) % S k = 1 % S k := by
  intro h
  apply mod_eq_of_add_mul_eq (a * (k * u)) 1 (S k) v (a * u)
  rw [← h, mul_left_comm a k u, ← add_assoc, ← succ_mul, add_comm]

theorem adjusted_remainder (b d u m r : Nat) :
    ¬ m = 0 → r < m → (d * u) % m = 1 % m → (b + d * (u * (r + m - b % m))) % m = r := by
  intro hm hr hu
  let z := r + m - b % m
  have hz : b % m + z = r + m := by
    have hb : b % m ≤ r + m :=
      le_trans (b % m) m (r + m) (le_of_lt (b % m) m (mod_lt b m hm))
        (le_add_left r m)
    rw [add_comm]
    exact sub_add_cancel_of_le (r + m) (b % m) hb
  have hp : (d * (u * z)) % m = z % m := by
    rw [← mul_assoc d u z, mod_mul_eq (d * u) z m, hu,
      ← mod_mul_eq 1 z m, one_mul]
  have hs := mod_add_eq (b % m) z m
  rw [mod_mod] at hs
  change (b + d * (u * z)) % m = r
  rw [mod_add_eq b (d * (u * z)) m, hp, ← hs, hz]
  have ht := mod_add_mul r m 1
  rw [mul_one] at ht
  rw [ht, mod_of_lt r m hr]

theorem factorial_mod : ∀ j n, ¬ j = 0 → j ≤ n → factorial n % j = 0 := by
  intro j n hj
  induction n with n ih
  · intro h
    exact false_elim (hj (le_zero j h))
  · intro h
    rcases lt_or_eq_of_le j (S n) h with hl | he
    · have hjn : j ≤ n := and_left (lt_succ j n) hl
      rw [factorial_succ n, mod_mul_eq (factorial n) (S n) j, ih hjn, zero_mul, zero_mod]
    · rw [he, factorial_succ n, mul_comm, mod_mul]

theorem product_mod_one (f : Nat → Nat) (n m : Nat) :
    (∀ i, i < n → f i % m = 1 % m) → product f n % m = 1 % m := by
  intro h
  have prefixes : ∀ k, k ≤ n → product f k % m = 1 % m := by
    intro k
    induction k with k ih
    · intro hk
      rfl
    · intro hk
      have hkn : k ≤ n := le_trans k (S k) n (le_succ_self k) hk
      rw [product_succ f, mod_mul_eq (product f k) (f k) m, ih hkn, h k hk]
      rw [← mod_mul_eq 1 1 m, one_mul]
  exact prefixes n (le_refl n)

theorem product_mod_zero (f : Nat → Nat) (n i m : Nat) :
    i < n → f i % m = 0 → product f n % m = 0 := by
  intro hi hf
  have prefixes : ∀ k, i < k → product f k % m = 0 := by
    intro k
    induction k with k ih
    · intro hk
      exact false_elim (not_lt_zero i hk)
    · intro hk
      rcases lt_or_eq_of_le i k (and_left (lt_succ i k) hk) with hil | hie
      · rw [product_succ f, mod_mul_eq (product f k) (f k) m, ih hil, zero_mul, zero_mod]
      · rw [← hie, product_succ f, mod_mul_eq (product f i) (f i) m, hf, mul_zero, zero_mod]
  exact prefixes n hi

/-!
## Remainders after a fixed prefix

After an initial segment of length `p`, divide the indices into blocks of positive length `d`.
The index `p + (d * q + r)` has the same position in its block as `p + r` when `r < d`.
A lookup that depends only on this position gives the same value in every block.
-/

theorem ite_ltb_mod_mul_add_of_lt : ∀ p d r q, r < d →
    let j := p + (d * q + r);
    ite (ltb j p) j (p + ((j - p) % d)) = p + r := by
  intro p d r q hr
  have hd := ne_zero_of_pos d (lt_of_le_of_lt 0 r d (zero_le r) hr)
  rw [ltb_eq_zero_of_ge _ _ (le_add_right p (d * q + r)), ite_zero, add_sub_self_left,
    mod_mul_add_of_lt d q r hd hr]
  rfl

theorem ite_ltb_mod_eq_self_of_lt_add : ∀ p d r q, r < p + d →
    let j := ite (ltb r p) r (p + (d * q + (r - p)));
    ite (ltb j p) j (p + ((j - p) % d)) = r := by
  intro p d r q h
  by_cases hr : r < p
  · rw [and_right (ltb_eq_one r p) hr, ite_succ,
      and_right (ltb_eq_one r p) hr, ite_succ]
    rfl
  · have hle := le_of_not_lt p r hr
    have hd := and_right (sub_lt_iff r p d hle) h
    rw [ltb_eq_zero_of_ge r p hle, ite_zero]
    exact eq_trans (ite_ltb_mod_mul_add_of_lt p d (r - p) q hd)
      (eq_trans (add_comm p (r - p)) (sub_add_cancel_of_le r p hle))

theorem ite_ltb_apply_mod_mod (initial periodic : Nat → Nat) : ∀ p d j,
    let r := ite (ltb j p) j (p + ((j - p) % d));
    ite (ltb r p) (initial r) (periodic ((r - p) % d)) =
      ite (ltb j p) (initial j) (periodic ((j - p) % d)) := by
  intro p d j
  by_cases h : j < p
  · rw [and_right (ltb_eq_one j p) h, ite_succ, and_right (ltb_eq_one j p) h, ite_succ]
    rfl
  · rw [ltb_eq_zero_of_ge _ _ (le_of_not_lt _ _ h), ite_zero,
      ltb_eq_zero_of_ge _ _ (le_add_right p _), ite_zero, add_sub_self_left, mod_mod]
    rfl

end
