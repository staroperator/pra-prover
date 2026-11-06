module

public import LeanPRA.Library.Tactic

/-!
# Basic numerical operations in PRA

Primitive recursive arithmetic and order on `Nat`:

- `add`, `sub`, `mul`, and `pow` define addition (`+`), truncated subtraction (`-`),
  multiplication (`*`), and exponentiation, each recursing on its second argument.
- `pred` defines predecessor (`pred 0 = 0`).
- `LE` (`≤`) and `LT` (`<`) define order as the quantifier-free formulas `x - y = 0` and `S x ≤ y`.
- `iter` iterates a unary function `f : Nat → Nat`.
-/

@[expose] public section

pra

/-- Addition. -/
def add : Nat → Nat → Nat :=
  fun x y => primrec x (fun _ z => S z) y

infixl:65 " + " => add

theorem add_zero : ∀ x, x + 0 = x :=
  fun x => rfl

theorem add_succ : ∀ x y, x + S y = S (x + y) :=
  fun x y => rfl

theorem add_one : ∀ x, x + 1 = S x := fun x => rfl

theorem zero_add : ∀ x, 0 + x = x :=
  fun x => induction rfl (fun x ih => by rw [add_succ, ih]) x

theorem succ_add : ∀ x y, S x + y = S (x + y) :=
  fun x y => induction rfl (fun y ih => by rw [add_succ, ih, add_succ]) y

theorem one_add : ∀ x, 1 + x = S x := by
  intro x
  rw [succ_add, zero_add]

theorem add_comm : ∀ x y, x + y = y + x :=
  fun x y => induction (zero_add y) (fun x ih => by rw [succ_add, ih, add_succ]) x

theorem add_assoc : ∀ x y z, x + y + z = x + (y + z) :=
  fun x y z => induction rfl (fun z ih => by rw [add_succ, ih, add_succ, add_succ]) z

theorem add_left_comm : ∀ x y z, x + (y + z) = y + (x + z) := by
  intro x y z
  rw [← add_assoc, ← add_assoc, add_comm x y]

theorem add_right_comm : ∀ x y z, x + y + z = x + z + y := by
  intro x y z
  rw [add_assoc, add_assoc, add_comm y z]

theorem add_add_add_comm : ∀ a b c d, a + b + (c + d) = a + c + (b + d) := by
  intro a b c d
  rw [← add_assoc (a + b) c d, add_right_comm a b c, add_assoc (a + c) b d]

/-- Predecessor (with `pred 0 = 0`). -/
def pred : Nat → Nat := fun n => primrec 0 (fun k _ => k) n

theorem pred_zero : pred 0 = 0 := rfl

theorem pred_succ : ∀ n, pred (S n) = n := fun n => rfl

theorem zero_ne_succ : ∀ n, ¬ 0 = S n :=
  fun n h => succ_ne_zero n (eq_symm h)

theorem zero_or_succ_pred : ∀ n, n = 0 ∨ n = S (pred n) := by
  intro n
  induction n with k ih
  · left; rfl
  · right; rfl

theorem succ_pred : ∀ n, ¬ n = 0 → S (pred n) = n := by
  intro n hn
  rcases zero_or_succ_pred n with hz | hs
  · exact false_elim (hn hz)
  · exact eq_symm hs

/-- Split a proof of `P n` into `P 0` and `∀ n, P (S n)` for any predicate `P : Nat → Prop`. -/
theorem nat_cases (P : Nat → Prop) : P 0 → (∀ n, P (S n)) → ∀ n, P n := by
  intro base step n
  rcases zero_or_succ_pred n with hz | hs
  · exact eq_subst P (eq_symm hz) base
  · exact eq_subst P (eq_symm hs) (step (pred n))

/-- Truncated subtraction (`x - y = 0` when `x ≤ y`), recursing on the second argument. -/
def sub : Nat → Nat → Nat := fun x y => primrec x (fun _ z => pred z) y

infixl:65 " - " => sub

theorem sub_zero : ∀ x, x - 0 = x := fun x => rfl

theorem sub_succ : ∀ x y, x - S y = pred (x - y) := fun x y => rfl

theorem zero_sub : ∀ x, 0 - x = 0 := by
  intro x
  induction x with k ih
  · rfl
  · rw [sub_succ, ih]; rfl

theorem pred_sub : ∀ x y, pred (x - y) = pred x - y := by
  intro x y
  induction y with k ih
  · rfl
  · rw [sub_succ, ih, sub_succ]

theorem succ_sub_succ : ∀ x y, S x - S y = x - y := by
  intro x y
  rw [sub_succ, pred_sub, pred_succ]

theorem sub_self : ∀ x, x - x = 0 := by
  intro x
  induction x with k ih
  · rfl
  · rw [succ_sub_succ, ih]

theorem sub_add : ∀ x y z, x - (y + z) = x - y - z := by
  intro x y z
  induction z with k ih
  · rfl
  · rw [add_succ, sub_succ, ih, sub_succ]

theorem add_sub_self_right : ∀ x y, x + y - y = x := by
  intro x y
  induction y with k ih
  · rfl
  · rw [add_succ, succ_sub_succ, ih]

theorem add_sub_self_left : ∀ x y, x + y - x = y := by
  intro x y
  rw [add_comm x y, add_sub_self_right]

theorem succ_sub_self : ∀ x, S x - x = 1 := by
  intro x
  rw [← one_add x, add_sub_self_right]

theorem sub_add_of_ne_zero : ∀ x y, ¬ x - y = 0 → x - y + y = x := by
  intro x y
  induction y with k ih
  · intro h; rfl
  · intro h
    have hp : ¬ x - k = 0 := by
      intro hz
      apply h
      rw [sub_succ, hz]; rfl
    rw [sub_succ, add_succ, ← succ_add, succ_pred (x - k) hp]
    exact ih hp

theorem add_right_cancel : ∀ x y z, x + z = y + z → x = y := by
  intro x y z h
  have hs := eq_congr (fun n => n - z) h
  rw [add_sub_self_right, add_sub_self_right] at hs
  exact hs

theorem add_left_cancel : ∀ x y z, x + y = x + z → y = z := by
  intro x y z h
  rw [add_comm x y, add_comm x z] at h
  exact add_right_cancel y z x h

/-- Non-strict order (`x ≤ y`), defined as the quantifier-free formula `x - y = 0`. -/
def LE : Nat → Nat → QFProp := fun x y => x - y = 0

infix:50 " ≤ " => LE

theorem le_refl : ∀ x, x ≤ x := sub_self

theorem zero_le : ∀ x, 0 ≤ x := zero_sub

theorem le_zero : ∀ x, x ≤ 0 → x = 0 := fun x h => h

theorem succ_le_succ : ∀ x y, S x ≤ S y ↔ x ≤ y := by
  intro x y
  rw [LE, LE, succ_sub_succ]
  exact iff_refl

theorem le_antisymm : ∀ x y, x ≤ y → y ≤ x → x = y := by
  intro x y
  induction y with k ih
  · intro h _; exact h
  · intro hxy hyx
    by_cases h : x - k = 0
    · have hy : k - x = 0 :=
        eq_trans (eq_symm (pred_sub (S k) x)) (eq_congr pred hyx)
      have he := ih h hy
      have hbad : S k - x = 0 := hyx
      rw [he, succ_sub_self] at hbad
      exact false_elim (succ_ne_zero 0 hbad)
    · have hp : pred (x - k) = 0 := hxy
      have hs := succ_pred (x - k) h
      rw [hp] at hs
      have he := sub_add_of_ne_zero x k h
      rw [← hs, one_add] at he
      exact eq_symm he

theorem sub_add_cancel_of_le : ∀ x y, y ≤ x → x - y + y = x := by
  intro x y h
  by_cases hz : x - y = 0
  · have he := le_antisymm x y hz h
    rw [he, sub_self, zero_add]
  · exact sub_add_of_ne_zero x y hz

theorem le_add_right : ∀ x y, x ≤ x + y := by
  intro x y
  change x - (x + y) = 0
  rw [sub_add, sub_self, zero_sub]

theorem le_add_left : ∀ x y, y ≤ x + y := by
  intro x y
  rw [add_comm]
  exact le_add_right y x

theorem le_of_add_eq : ∀ x y z, x + z = y → x ≤ y := by
  intro x y z h
  rw [← h]
  exact le_add_right x z

/-- `x ≤ y` is equivalent to `∃ z, x + z = y`. Note `x ≤ y` itself is defined without quantifier. -/
theorem le_iff_exists_add : ∀ x y, x ≤ y ↔ ∃ z, x + z = y := by
  intro x y
  constructor
  · intro h
    exists y - x
    rw [add_comm]
    exact sub_add_cancel_of_le y x h
  · rintro (z, h)
    exact le_of_add_eq x y z h

theorem le_trans : ∀ x y z, x ≤ y → y ≤ z → x ≤ z := by
  intro x y z hxy hyz
  rcases and_left (le_iff_exists_add x y) hxy with (a, ha)
  rcases and_left (le_iff_exists_add y z) hyz with (b, hb)
  apply le_of_add_eq x z (a + b)
  rw [← add_assoc, ha]
  exact hb

theorem le_total : ∀ x y, x ≤ y ∨ y ≤ x := by
  intro x y
  by_cases h : x - y = 0
  · left; exact h
  · right
    apply le_of_add_eq y x (x - y)
    rw [add_comm]
    exact sub_add_of_ne_zero x y h

theorem le_succ_self : ∀ x, x ≤ S x := fun x => le_add_right x 1

theorem le_succ_of_le : ∀ x y, x ≤ y → x ≤ S y :=
  fun x y h => le_trans x y (S y) h (le_succ_self y)

theorem add_le_add_left : ∀ x y z, x ≤ y → z + x ≤ z + y := by
  intro x y z h
  rcases and_left (le_iff_exists_add x y) h with (d, hd)
  apply le_of_add_eq (z + x) (z + y) d
  rw [add_assoc, hd]

theorem add_le_add_right : ∀ x y z, x ≤ y → x + z ≤ y + z := by
  intro x y z h
  rw [add_comm x z, add_comm y z]
  exact add_le_add_left x y z h

theorem le_of_add_le_add_left : ∀ x y z, z + x ≤ z + y → x ≤ y := by
  intro x y z h
  rcases and_left (le_iff_exists_add (z + x) (z + y)) h with (d, hd)
  apply le_of_add_eq x y d
  apply add_left_cancel z (x + d) y
  rw [← add_assoc]; exact hd

theorem le_of_add_le_add_right : ∀ x y z, x + z ≤ y + z → x ≤ y := by
  intro x y z h
  rw [add_comm x z, add_comm y z] at h
  exact le_of_add_le_add_left x y z h

/-- If `f n ≤ f (S n)` for every `n`, then `f` preserves `≤`. -/
theorem monotone_of_succ (f : Nat → Nat) :
    (∀ n, f n ≤ f (S n)) → ∀ x y, x ≤ y → f x ≤ f y := by
  intro step x y h
  rcases and_left (le_iff_exists_add x y) h with (d, hd)
  have growth : ∀ k, f x ≤ f (x + k) := by
    intro k
    induction k with j ih
    · exact le_refl (f x)
    · exact le_trans (f x) (f (x + j)) (f (S (x + j))) ih (step (x + j))
  rw [← hd]; exact growth d

/-- Strict order (`x < y`), defined as the quantifier-free formula `S x ≤ y`. -/
def LT : Nat → Nat → QFProp := fun x y => LE (S x) y

infix:50 " < " => LT

theorem lt_succ : ∀ x y, x < S y ↔ x ≤ y := succ_le_succ

theorem lt_succ_self : ∀ x, x < S x :=
  fun x => and_right (lt_succ x x) (le_refl x)

theorem not_lt_zero : ∀ x, ¬ x < 0 := succ_ne_zero

theorem not_lt_self : ∀ x, ¬ x < x := by
  intro x h
  have he : S x - x = 0 := h
  rw [succ_sub_self] at he
  exact succ_ne_zero 0 he

theorem le_of_lt : ∀ x y, x < y → x ≤ y :=
  fun x y h => le_trans x (S x) y (le_succ_self x) h

theorem lt_or_eq_of_le : ∀ x y, x ≤ y → x < y ∨ x = y := by
  intro x y h
  by_cases hz : y - x = 0
  · right; exact le_antisymm x y h hz
  · left
    apply le_of_add_eq (S x) y (pred (y - x))
    rw [succ_add, ← add_succ, succ_pred (y - x) hz, add_comm]
    exact sub_add_of_ne_zero y x hz

theorem lt_succ_iff : ∀ x y, x < S y ↔ x < y ∨ x = y := by
  intro x y
  constructor
  · intro h
    exact lt_or_eq_of_le x y (and_left (lt_succ x y) h)
  · rintro (h | h)
    · exact and_right (lt_succ x y) (le_of_lt x y h)
    · rw [h]; exact lt_succ_self y

theorem lt_of_lt_of_le : ∀ x y z, x < y → y ≤ z → x < z :=
  fun x y z hxy hyz => le_trans (S x) y z hxy hyz

theorem lt_of_le_of_lt : ∀ x y z, x ≤ y → y < z → x < z :=
  fun x y z hxy hyz => le_trans (S x) (S y) z (and_right (succ_le_succ x y) hxy) hyz

theorem not_le_of_lt : ∀ x y, x < y → ¬ y ≤ x :=
  fun x y h h' => not_lt_self x (lt_of_lt_of_le x y x h h')

theorem le_of_not_lt : ∀ x y, ¬ y < x → x ≤ y := by
  intro x y h
  rcases le_total x y with hxy | hyx
  · exact hxy
  · rcases lt_or_eq_of_le y x hyx with hlt | he
    · exact false_elim (h hlt)
    · rw [← he]; exact le_refl y

theorem lt_of_not_le : ∀ x y, ¬ y ≤ x → x < y := by
  intro x y h
  by_contra hn
  exact h (le_of_not_lt y x hn)

theorem pos_of_ne_zero : ∀ x, ¬ x = 0 → 0 < x := by
  intro x h
  apply lt_of_not_le 0 x
  exact h

theorem ne_zero_of_pos : ∀ x, 0 < x → ¬ x = 0 := by
  intro x h he
  rw [he] at h
  exact not_lt_zero 0 h

theorem add_lt_add_left : ∀ x y z, x < y → z + x < z + y := by
  intro x y z h
  change S (z + x) ≤ z + y
  rw [← add_succ]
  exact add_le_add_left (S x) y z h

theorem add_lt_add_right : ∀ x y z, x < y → x + z < y + z := by
  intro x y z h
  rw [add_comm x z, add_comm y z]
  exact add_lt_add_left x y z h

theorem lt_of_add_lt_add_left : ∀ x y z, z + x < z + y → x < y := by
  intro x y z h
  apply le_of_add_le_add_left (S x) y z
  rw [add_succ]; exact h

theorem sub_le : ∀ x y, x - y ≤ x := by
  intro x y
  induction y with k ih
  · exact le_refl x
  · have hp : pred (x - k) ≤ x - k := by
      rcases zero_or_succ_pred (x - k) with hz | hs
      · rw [hz]; exact le_refl 0
      · rw [hs]; exact le_succ_self (pred (x - k))
    exact le_trans (pred (x - k)) (x - k) x hp ih

theorem sub_le_sub_left : ∀ x y z, x ≤ y → z - y ≤ z - x := by
  intro x y z h
  rcases and_left (le_iff_exists_add x y) h with (d, hd)
  rw [← hd, sub_add]
  exact sub_le (z - x) d

theorem sub_le_sub_right : ∀ x y z, x ≤ y → x - z ≤ y - z := by
  intro x y z h
  by_cases hz : x ≤ z
  · have he : x - z = 0 := hz
    rw [he]; exact zero_le (y - z)
  · have hzx := le_of_lt z x (lt_of_not_le z x hz)
    have hzy := le_trans z x y hzx h
    apply le_of_add_le_add_right (x - z) (y - z) z
    rw [sub_add_cancel_of_le x z hzx, sub_add_cancel_of_le y z hzy]
    exact h

theorem succ_sub_of_le : ∀ x y, y ≤ x → S x - y = S (x - y) := by
  intro x y h
  apply add_right_cancel (S x - y) (S (x - y)) y
  rw [sub_add_cancel_of_le (S x) y (le_succ_of_le y x h), succ_add,
    sub_add_cancel_of_le x y h]

theorem sub_lt_of_pos : ∀ x y, 0 < x → 0 < y → x - y < x := by
  intro x y hx hy
  have hp : pred x < x := by
    rw [← succ_pred x (ne_zero_of_pos x hx)]
    exact lt_succ_self (pred x)
  exact lt_of_le_of_lt (x - y) (pred x) x (sub_le_sub_left 1 y x hy) hp

theorem sub_le_iff : ∀ x y z, x - y ≤ z ↔ x ≤ y + z := by
  intro x y z
  rw [LE, LE, sub_add]
  exact iff_refl

theorem sub_lt_iff : ∀ x y z, y ≤ x → (x - y < z ↔ x < y + z) := by
  intro x y z h
  change S (x - y) ≤ z ↔ S x ≤ y + z
  rw [← succ_sub_of_le x y h]
  exact sub_le_iff (S x) y z

theorem sub_sub_cancel : ∀ x y, y ≤ x → x - (x - y) = y := by
  intro x y h
  have he := sub_add_cancel_of_le x y h
  have hh := eq_congr (fun k => k - (x - y)) he
  rw [add_comm (x - y) y, add_sub_self_right] at hh
  exact eq_symm hh

theorem sub_succ_lt_self : ∀ n i, i < n → n - S i < n := by
  intro n i hi
  exact sub_lt_of_pos n (S i)
    (lt_of_le_of_lt 0 i n (zero_le i) hi) (pos_of_ne_zero (S i) (succ_ne_zero i))

theorem sub_succ_sub_succ_cancel : ∀ n i, i < n → n - S (n - S i) = i := by
  intro n i hi
  rw [sub_succ, sub_sub_cancel n (S i) hi, pred_succ]

theorem succ_sub_succ_eq_sub : ∀ n i, i < n → S (n - S i) = n - i := by
  intro n i hi
  rw [sub_succ]
  exact succ_pred (n - i) (not_le_of_lt i n hi)

/-- Multiplication. -/
def mul : Nat → Nat → Nat :=
  fun x y => primrec 0 (fun _ z => add z x) y

infixl:70 " * " => mul

theorem mul_zero : ∀ x, x * 0 = 0 :=
  fun x => rfl

theorem mul_succ : ∀ x y, x * S y = x * y + x :=
  fun x y => rfl

theorem mul_one : ∀ x, x * 1 = x :=
  fun x => zero_add x

theorem zero_mul : ∀ x, 0 * x = 0 :=
  fun x => induction rfl (fun x ih => by rw [mul_succ, ih, add_zero]) x

theorem succ_mul : ∀ x y, S x * y = x * y + y :=
  fun x y => induction rfl (fun y ih => by
    rw [mul_succ, add_succ, ih, add_right_comm, mul_succ, add_succ]) y

theorem one_mul : ∀ x, 1 * x = x := by
  intro x
  rw [succ_mul, zero_mul, zero_add]

theorem mul_comm : ∀ x y, x * y = y * x :=
  fun x y => induction (zero_mul y) (fun x ih => by rw [succ_mul, ih, mul_succ]) x

theorem mul_add_right_distrib : ∀ x y z, (x + y) * z = x * z + y * z :=
  fun x y z => induction rfl (fun z ih => by
    rw [mul_succ, ih, add_add_add_comm, mul_succ, mul_succ]) z

theorem mul_add_left_distrib : ∀ x y z, x * (y + z) = x * y + x * z := by
  intro x y z
  rw [mul_comm, mul_add_right_distrib, mul_comm y x, mul_comm z x]

theorem mul_assoc : ∀ x y z, x * y * z = x * (y * z) :=
  fun x y z => induction rfl (fun z ih => by
    rw [mul_succ, ih, ← mul_add_left_distrib, mul_succ]) z

theorem mul_left_comm : ∀ x y z, x * (y * z) = y * (x * z) := by
  intro x y z
  rw [← mul_assoc, ← mul_assoc, mul_comm x y]

theorem mul_right_comm : ∀ x y z, x * y * z = x * z * y := by
  intro x y z
  rw [mul_assoc, mul_assoc, mul_comm y z]

theorem mul_mul_mul_comm : ∀ a b c d, a * b * (c * d) = a * c * (b * d) := by
  intro a b c d
  rw [← mul_assoc (a * b) c d, mul_right_comm a b c, mul_assoc (a * c) b d]

theorem mul_le_mul_left : ∀ x y z, x ≤ y → z * x ≤ z * y := by
  intro x y z h
  rcases and_left (le_iff_exists_add x y) h with (d, hd)
  apply le_of_add_eq (z * x) (z * y) (z * d)
  rw [← mul_add_left_distrib, hd]

theorem mul_le_mul_right : ∀ x y z, x ≤ y → x * z ≤ y * z := by
  intro x y z h
  rw [mul_comm x z, mul_comm y z]
  exact mul_le_mul_left x y z h

theorem le_mul_of_pos : ∀ x d, ¬ d = 0 → x ≤ d * x := by
  intro x d h
  have hm := mul_le_mul_right 1 d x (pos_of_ne_zero d h)
  rw [one_mul] at hm
  exact hm

theorem mul_lt_mul_left : ∀ x y z, x < y → ¬ z = 0 → z * x < z * y := by
  intro x y z h hz
  have hs : z * x < z * S x := by
    rw [mul_succ]
    have ha := add_lt_add_left 0 z (z * x) (pos_of_ne_zero z hz)
    rw [add_zero] at ha
    exact ha
  exact lt_of_lt_of_le (z * x) (z * S x) (z * y) hs (mul_le_mul_left (S x) y z h)

/-- Exponentiation `pow x n` (`x ^ n`), recursing on the exponent `n`. -/
def pow : Nat → Nat → Nat := fun x n => primrec 1 (fun _ r => r * x) n

theorem pow_zero : ∀ x, pow x 0 = 1 := fun x => rfl

theorem pow_succ : ∀ x n, pow x (S n) = pow x n * x := fun x n => rfl

theorem pow_one : ∀ x, pow x 1 = x := one_mul

theorem pow_add : ∀ x m n, pow x (m + n) = pow x m * pow x n := by
  intro x m n
  induction n with k ih
  · exact eq_symm (mul_one (pow x m))
  · rw [add_succ, pow_succ, ih, mul_assoc, pow_succ]

/-- `iter f n` applies `f` repeatedly for `n` times. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat :=
  fun n x => primrec x (fun _ y => f y) n

theorem iter_zero (f : Nat → Nat) : ∀ x, iter f 0 x = x :=
  fun x => rfl

theorem iter_succ (f : Nat → Nat) : ∀ n x, iter f (S n) x = f (iter f n x) :=
  fun n x => rfl

theorem iter_succ_apply (f : Nat → Nat) :
    ∀ n x, iter f n (f x) = f (iter f n x) := by
  intro n x
  induction n with k ih
  · rfl
  · rw [iter_succ f, ih, iter_succ f]

theorem iter_add (f : Nat → Nat) :
    ∀ m n x, iter f (m + n) x = iter f n (iter f m x) := by
  intro m n x
  induction n with k ih
  · rfl
  · rw [add_succ, iter_succ f, ih, iter_succ f]

theorem iter_invariant (P : Nat → QFProp) (f : Nat → Nat) :
    (∀ x, P x → P (f x)) → ∀ x, P x → ∀ n, P (iter f n x) := by
  intro step x initial n
  induction n with k ih
  · exact initial
  · exact step (iter f k x) ih

theorem iter_congr (f g : Nat → Nat) :
    (∀ x, f x = g x) → ∀ n x, iter f n x = iter g n x := by
  intro h n x
  induction n with k ih
  · rfl
  · rw [iter_succ f, iter_succ g, ih, h]

end
