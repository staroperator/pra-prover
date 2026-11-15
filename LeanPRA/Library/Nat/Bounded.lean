module

public import LeanPRA.Library.Nat.Boolean

/-!
# Bounded numerical reasoning in PRA

Bounded checks, bounded search, and derived induction principles on `Nat`. A bound `n` covers the
indices `0` through `n - 1`, and a numerical test `f : Nat → Nat` counts as true at `i` when
`¬ f i = 0`:

- `allBelow f n` returns `1` when `¬ f i = 0` for all `i < n`, and `0` otherwise.
- `anyBelow f n` returns `1` when `¬ f i = 0` for some `i < n`, and `0` otherwise.
- `findBelow f n` returns the least `i < n` with `¬ f i = 0`, or `n` when `f i = 0` for all `i < n`.
- `agreeBelow f g n` states as a quantifier-free formula that `f i = g i` for all `i < n`.
- `factorial n` is the product of the numbers from one through `n`.
- `product f n` multiplies the first `n` values of `f`.
- `maximum f n` bounds the first `n` values of `f`.
- `strong_induction_eq` proves numerical equations from their instances at smaller indices.

Ordinary quantifier-free induction on `allBelow` yields strong induction, and inducting on `n - k`
yields downward induction from `n` to `0`.
-/

@[expose] public section

pra

/-- Check a boolean predicate at every index strictly below the bound. -/
def allBelow (f : Nat → Nat) : Nat → Nat :=
  fun n => primrec 1 (fun k r => band r (f k)) n

theorem allBelow_zero (f : Nat → Nat) : allBelow f 0 = 1 := rfl

theorem allBelow_succ (f : Nat → Nat) :
    ∀ n, allBelow f (S n) = band (allBelow f n) (f n) := fun n => rfl

theorem allBelow_bool (f : Nat → Nat) : ∀ n, IsBool (allBelow f n) := by
  intro n
  induction n with k ih
  · right; rfl
  · exact band_bool (allBelow f k) (f k)

theorem allBelow_succ_iff (f : Nat → Nat) :
    ∀ n, allBelow f (S n) = 1 ↔ allBelow f n = 1 ∧ ¬ f n = 0 := by
  intro n
  constructor
  · intro h
    rcases and_left (band_eq_one (allBelow f n) (f n)) h with (hp, hn)
    exact (and_right (bool_eq_one (allBelow f n) (allBelow_bool f n)) hp, hn)
  · rintro (hp, hn)
    exact and_right (band_eq_one (allBelow f n) (f n))
      (and_left (bool_eq_one (allBelow f n) (allBelow_bool f n)) hp, hn)

theorem allBelow_elim (f : Nat → Nat) :
    ∀ i n, allBelow f n = 1 → i < n → ¬ f i = 0 := by
  intro i n
  induction n with k ih
  · intro _ h; exact false_elim (not_lt_zero i h)
  · intro h hi
    rcases and_left (allBelow_succ_iff f k) h with (hp, hk)
    rcases and_left (lt_succ_iff i k) hi with hlt | he
    · exact ih hp hlt
    · rw [he]; exact hk

theorem allBelow_intro (f : Nat → Nat) :
    ∀ n, (∀ i, i < n → ¬ f i = 0) → allBelow f n = 1 := by
  intro n h
  have checkedPrefix : ∀ k, k ≤ n → allBelow f k = 1 := by
    intro k
    induction k with j ih
    · intro _; rfl
    · intro hj
      apply and_right (allBelow_succ_iff f j)
      constructor
      · exact ih (le_trans j (S j) n (le_succ_self j) hj)
      · exact h j hj
  exact checkedPrefix n (le_refl n)

theorem allBelow_eq_one (f : Nat → Nat) :
    ∀ n, allBelow f n = 1 ↔ ∀ i, i < n → ¬ f i = 0 :=
  fun n => (fun h i hi => allBelow_elim f i n h hi, allBelow_intro f n)

theorem allBelow_prefix (f : Nat → Nat) :
    ∀ m n, m ≤ n → allBelow f n = 1 → allBelow f m = 1 := by
  intro m n hmn h
  apply allBelow_intro f m
  intro i hi
  exact allBelow_elim f i n h (lt_of_lt_of_le i m n hi hmn)

/-- Strong induction for a numerical test `f`: if `allBelow f n = 1` implies `¬ f n = 0` for all
`n`, then `¬ f n = 0` for all `n`. -/
theorem strong_induction (f : Nat → Nat) :
    (∀ n, allBelow f n = 1 → ¬ f n = 0) → ∀ n, ¬ f n = 0 := by
  intro step n
  have checkedPrefix : ∀ k, allBelow f k = 1 := by
    intro k
    induction k with j ih
    · rfl
    · exact and_right (allBelow_succ_iff f j) (ih, step j ih)
  exact step n (checkedPrefix n)

/-- Strong induction for a predicate `P : Nat → Prop` represented by a numerical test `f` with
`∀ n, ¬ f n = 0 ↔ P n`. -/
theorem strong_induction_of_bool (P : Nat → Prop) (f : Nat → Nat) :
    (∀ n, ¬ f n = 0 ↔ P n) →
    (∀ n, (∀ i, i < n → P i) → P n) → ∀ n, P n := by
  intro spec step n
  apply and_left (spec n)
  apply strong_induction f
  intro k hk
  apply and_right (spec k)
  apply step k
  intro i hi
  exact and_left (spec i) (allBelow_elim f i k hk hi)

/-- Prove pointwise equality of numerical functions by assuming equality at every smaller index. -/
theorem strong_induction_eq (f g : Nat → Nat) :
    (∀ n, (∀ i, i < n → f i = g i) → f n = g n) → ∀ n, f n = g n := by
  apply strong_induction_of_bool (fun n => f n = g n) (fun n => eqb (f n) (g n))
  intro n
  constructor
  · intro h
    by_contra hn
    exact h (and_right (eqb_eq_zero (f n) (g n)) hn)
  · intro h hn
    exact and_left (eqb_eq_zero (f n) (g n)) hn h

/-- Test whether at least one index strictly below the bound satisfies the predicate. -/
def anyBelow (f : Nat → Nat) : Nat → Nat :=
  fun n => bnot (allBelow (fun i => bnot (f i)) n)

theorem anyBelow_bool (f : Nat → Nat) : ∀ n, IsBool (anyBelow f n) :=
  fun n => bnot_bool (allBelow (fun i => bnot (f i)) n)

theorem anyBelow_zero (f : Nat → Nat) : anyBelow f 0 = 0 := rfl

/-- Search in increasing order for the least `i < n` with `¬ f i = 0`, returning `n` when none
exists. -/
def findBelow (f : Nat → Nat) : Nat → Nat :=
  fun n => primrec 0 (fun k r => ite (eqb r k) (ite (f k) k (S k)) r) n

theorem findBelow_zero (f : Nat → Nat) : findBelow f 0 = 0 := rfl

theorem findBelow_succ (f : Nat → Nat) : ∀ n,
    findBelow f (S n) =
      ite (eqb (findBelow f n) n) (ite (f n) n (S n)) (findBelow f n) :=
  fun n => rfl

theorem findBelow_succ_of_ne (f : Nat → Nat) :
    ∀ n, ¬ findBelow f n = n → findBelow f (S n) = findBelow f n := by
  intro n h
  rw [findBelow_succ f, and_right (eqb_eq_zero (findBelow f n) n) h, ite_zero]

theorem findBelow_succ_of_eq (f : Nat → Nat) :
    ∀ n, findBelow f n = n → findBelow f (S n) = ite (f n) n (S n) := by
  intro n h
  rw [findBelow_succ f, and_right (eqb_eq_one (findBelow f n) n) h, ite_succ]

theorem findBelow_le (f : Nat → Nat) : ∀ n, findBelow f n ≤ n := by
  intro n
  induction n with k ih
  · exact le_refl 0
  · by_cases h : findBelow f k = k
    · rw [findBelow_succ_of_eq f k h]
      by_cases hf : f k = 0
      · rw [hf, ite_zero]; exact le_refl (S k)
      · rw [ite_of_ne_zero (f k) k (S k) hf]; exact le_succ_self k
    · rw [findBelow_succ_of_ne f k h]
      exact le_succ_of_le (findBelow f k) k ih

/-- When `findBelow f n < n`, the returned index satisfies `¬ f (findBelow f n) = 0`. -/
theorem findBelow_spec (f : Nat → Nat) :
    ∀ n, findBelow f n < n → ¬ f (findBelow f n) = 0 := by
  intro n
  induction n with k ih
  · intro h; exact false_elim (not_lt_zero (findBelow f 0) h)
  · intro hn
    by_cases h : findBelow f k = k
    · have he := findBelow_succ_of_eq f k h
      by_cases hf : f k = 0
      · rw [hf, ite_zero] at he
        rw [he] at hn
        exact false_elim (not_lt_self (S k) hn)
      · rw [ite_of_ne_zero (f k) k (S k) hf] at he
        rw [he]; exact hf
    · have he := findBelow_succ_of_ne f k h
      rw [he]
      apply ih
      rcases lt_or_eq_of_le (findBelow f k) k (findBelow_le f k) with hlt | heq
      · exact hlt
      · exact false_elim (h heq)

/-- Every index `i < findBelow f n` satisfies `f i = 0`. -/
theorem findBelow_min (f : Nat → Nat) :
    ∀ i n, i < findBelow f n → f i = 0 := by
  intro i n
  induction n with k ih
  · intro h; exact false_elim (not_lt_zero i h)
  · intro hi
    by_cases h : findBelow f k = k
    · have he := findBelow_succ_of_eq f k h
      by_cases hf : f k = 0
      · rw [hf, ite_zero] at he
        rw [he] at hi
        rcases and_left (lt_succ_iff i k) hi with hlt | heq
        · apply ih
          rw [h]; exact hlt
        · rw [heq]; exact hf
      · rw [ite_of_ne_zero (f k) k (S k) hf] at he
        rw [he] at hi
        apply ih
        rw [h]; exact hi
    · rw [findBelow_succ_of_ne f k h] at hi
      exact ih hi

theorem findBelow_le_of_witness (f : Nat → Nat) :
    ∀ i n, ¬ f i = 0 → findBelow f n ≤ i := by
  intro i n h
  apply le_of_not_lt (findBelow f n) i
  intro hi
  exact h (findBelow_min f i n hi)

theorem findBelow_lt_iff (f : Nat → Nat) :
    ∀ n, findBelow f n < n ↔ ∃ i, i < n ∧ ¬ f i = 0 := by
  intro n
  constructor
  · intro h
    exact (findBelow f n, h, findBelow_spec f n h)
  · rintro (i, hi, hf)
    exact lt_of_le_of_lt (findBelow f n) i n (findBelow_le_of_witness f i n hf) hi

/-- `findBelow f n = n` holds iff `f i = 0` for all `i < n`. -/
theorem findBelow_eq_bound (f : Nat → Nat) :
    ∀ n, findBelow f n = n ↔ ∀ i, i < n → f i = 0 := by
  intro n
  constructor
  · intro h i hi
    apply findBelow_min f i n
    rw [h]; exact hi
  · intro h
    rcases lt_or_eq_of_le (findBelow f n) n (findBelow_le f n) with hlt | heq
    · exact false_elim (findBelow_spec f n hlt (h (findBelow f n) hlt))
    · exact heq

theorem anyBelow_eq_zero (f : Nat → Nat) :
    ∀ n, anyBelow f n = 0 ↔ ∀ i, i < n → f i = 0 := by
  intro n
  constructor
  · intro h i hi
    have hall : allBelow (fun j => bnot (f j)) n = 1 :=
      and_right (bool_eq_one _ (allBelow_bool (fun j => bnot (f j)) n))
        (and_left (bnot_eq_zero _) h)
    have hn := allBelow_elim (fun j => bnot (f j)) i n hall hi
    exact and_left (bnot_eq_one (f i))
      (and_right (bool_eq_one (bnot (f i)) (bnot_bool (f i))) hn)
  · intro h
    apply and_right (bnot_eq_zero _)
    apply and_left (bool_eq_one _ (allBelow_bool (fun j => bnot (f j)) n))
    apply allBelow_intro (fun j => bnot (f j)) n
    intro i hi
    rw [h i hi]
    exact succ_ne_zero 0

theorem anyBelow_eq_one (f : Nat → Nat) :
    ∀ n, anyBelow f n = 1 ↔ ∃ i, i < n ∧ ¬ f i = 0 := by
  intro n
  constructor
  · intro h
    by_contra hn
    apply and_left (bool_eq_one _ (anyBelow_bool f n)) h
    apply and_right (anyBelow_eq_zero f n)
    intro i hi
    by_contra hf
    exact hn (i, hi, hf)
  · rintro (i, hi, hf)
    apply and_right (bool_eq_one _ (anyBelow_bool f n))
    intro h
    exact hf (and_left (anyBelow_eq_zero f n) h i hi)

theorem allBelow_eq_zero (f : Nat → Nat) :
    ∀ n, allBelow f n = 0 ↔ ∃ i, i < n ∧ f i = 0 := by
  intro n
  constructor
  · intro h
    by_contra hn
    apply and_left (bool_eq_zero _ (allBelow_bool f n)) h
    apply allBelow_intro f n
    intro i hi hf
    exact hn (i, hi, hf)
  · rintro (i, hi, hf)
    apply and_right (bool_eq_zero _ (allBelow_bool f n))
    intro h
    exact allBelow_elim f i n h hi hf

theorem findBelow_bnot_spec_of_allBelow_eq_zero (f : Nat → Nat) :
    ∀ n, allBelow f n = 0 → findBelow (fun i => bnot (f i)) n < n ∧
      f (findBelow (fun i => bnot (f i)) n) = 0 := by
  intro n h
  rcases and_left (allBelow_eq_zero f n) h with (i, hi, hf)
  have hn : ¬ bnot (f i) = 0 := by
    rw [hf]; exact succ_ne_zero 0
  have hlt := and_right (findBelow_lt_iff (fun j => bnot (f j)) n) (i, hi, hn)
  constructor
  · exact hlt
  · apply and_left (bnot_eq_one _)
    apply and_right (bool_eq_one _ (bnot_bool _))
    exact findBelow_spec (fun j => bnot (f j)) n hlt

theorem findBelow_eq (f : Nat → Nat) : ∀ i n, i < n → ¬ f i = 0 →
    (∀ j, j < i → f j = 0) → findBelow f n = i := by
  intro i n hi hf earlier
  apply le_antisymm (findBelow f n) i
  · exact findBelow_le_of_witness f i n hf
  · apply le_of_not_lt i (findBelow f n)
    intro h
    exact findBelow_spec f n
      (lt_of_lt_of_le _ i n h (le_of_lt i n hi)) (earlier (findBelow f n) h)

theorem allBelow_congr (f g : Nat → Nat) : ∀ n,
    (∀ i, i < n → f i = g i) → allBelow f n = allBelow g n := by
  intro n h
  have checked : ∀ k, k ≤ n → allBelow f k = allBelow g k := by
    intro k
    induction k with j ih
    · intro _; rfl
    · intro hj
      rw [allBelow_succ f, allBelow_succ g,
        ih (le_trans j (S j) n (le_succ_self j) hj), h j hj]
  exact checked n (le_refl n)

theorem eqb_ne_zero : ∀ x y, ¬ eqb x y = 0 ↔ x = y := by
  intro x y
  constructor
  · intro h
    exact and_left (eqb_eq_one x y) (and_right (bool_eq_one _ (eqb_bool x y)) h)
  · intro h
    exact and_left (bool_eq_one _ (eqb_bool x y)) (and_right (eqb_eq_one x y) h)

theorem ltb_ne_zero : ∀ x y, ¬ ltb x y = 0 ↔ x < y := by
  intro x y
  constructor
  · intro h
    exact and_left (ltb_eq_one x y) (and_right (bool_eq_one _ (ltb_bool x y)) h)
  · intro h
    exact and_left (bool_eq_one _ (ltb_bool x y)) (and_right (ltb_eq_one x y) h)

/-- Quantifier-free formula stating that `f i = g i` for every `i < n`. -/
def agreeBelow (f g : Nat → Nat) : Nat → QFProp :=
  fun n => allBelow (fun i => eqb (f i) (g i)) n = 1

theorem agreeBelow_iff (f g : Nat → Nat) :
    ∀ n, agreeBelow f g n ↔ ∀ i, i < n → f i = g i := by
  intro n
  constructor
  · intro h i hi
    exact and_left (eqb_ne_zero (f i) (g i))
      (allBelow_elim (fun j => eqb (f j) (g j)) i n h hi)
  · intro h
    apply allBelow_intro (fun i => eqb (f i) (g i)) n
    intro i hi
    exact and_right (eqb_ne_zero (f i) (g i)) (h i hi)

theorem findBelow_congr (f g : Nat → Nat) : ∀ n,
    (∀ i, i < n → f i = g i) → findBelow f n = findBelow g n := by
  intro n h
  rcases lt_or_eq_of_le (findBelow f n) n (findBelow_le f n) with hlt | he
  · apply eq_symm
    apply findBelow_eq g (findBelow f n) n hlt
    · rw [← h (findBelow f n) hlt]; exact findBelow_spec f n hlt
    · intro i hi
      rw [← h i (lt_of_lt_of_le i (findBelow f n) n hi (findBelow_le f n))]
      exact findBelow_min f i n hi
  · rw [he]
    apply eq_symm
    apply and_right (findBelow_eq_bound g n)
    intro i hi
    rw [← h i hi]
    exact and_left (findBelow_eq_bound f n) he i hi

theorem anyBelow_congr (f g : Nat → Nat) : ∀ n,
    (∀ i, i < n → f i = g i) → anyBelow f n = anyBelow g n := by
  intro n h
  have he := allBelow_congr (fun i => bnot (f i)) (fun i => bnot (g i)) n
    (fun i hi => eq_congr bnot (h i hi))
  exact eq_congr bnot he

theorem allBelow_add_iff (f : Nat → Nat) : ∀ m n,
    allBelow f (m + n) = 1 ↔
      allBelow f m = 1 ∧ allBelow (fun i => f (m + i)) n = 1 := by
  intro m n
  constructor
  · intro h
    constructor
    · exact allBelow_prefix f m (m + n) (le_add_right m n) h
    · apply allBelow_intro (fun i => f (m + i)) n
      intro i hi
      exact allBelow_elim f (m + i) (m + n) h (add_lt_add_left i n m hi)
  · rintro (hm, hn)
    apply allBelow_intro f (m + n)
    intro i hi
    by_cases him : i < m
    · exact allBelow_elim f i m hm him
    · have hmi := le_of_not_lt m i him
      have he : m + (i - m) = i := by
        rw [add_comm]; exact sub_add_cancel_of_le i m hmi
      have hx := allBelow_elim (fun j => f (m + j)) (i - m) n hn
        (and_right (sub_lt_iff i m n hmi) hi)
      rw [he] at hx; exact hx

theorem findBelow_extend (f : Nat → Nat) : ∀ m n,
    findBelow f m < m → m ≤ n → findBelow f n = findBelow f m := by
  intro m n hm hmn
  apply findBelow_eq f (findBelow f m) n
    (lt_of_lt_of_le _ m n hm hmn) (findBelow_spec f m hm)
  intro i hi
  exact findBelow_min f i m hi

/-- Downward induction from `P n` to `P 0` for a quantifier-free predicate `P`. -/
theorem induction_down (P : Nat → QFProp) : ∀ n,
    P n → (∀ i, i < n → P (S i) → P i) → P 0 := by
  intro n last step
  have backward : ∀ k, k ≤ n → P (n - k) := by
    intro k
    induction k with j ih
    · intro _; exact last
    · intro hj
      apply step (n - S j) (sub_succ_lt_self n j hj)
      have he := succ_sub_succ_eq_sub n j hj
      exact eq_subst P (eq_symm he) (ih (le_of_lt j n hj))
  have h := backward n (le_refl n)
  have he := sub_self n
  exact eq_subst P he h

/-! ## Finite products and maxima -/

/-- `factorial n` is the product of the numbers from one through `n`; its value at zero is one. -/
def factorial : Nat → Nat := primrec 1 (fun i n => n * S i)

theorem factorial_zero : factorial 0 = 1 := rfl

theorem factorial_succ (n : Nat) : factorial (S n) = factorial n * S n := rfl

theorem factorial_ne_zero : ∀ n, ¬ factorial n = 0 := by
  intro n
  induction n with n ih
  · exact succ_ne_zero 0
  · intro hz
    have hle : factorial n ≤ S n * factorial n :=
      le_mul_of_pos (factorial n) (S n) (succ_ne_zero n)
    rw [mul_comm, ← factorial_succ n, hz] at hle
    exact ih (le_zero (factorial n) hle)

/-- `product f n` multiplies `f i` for `i < n`, starting with one. -/
def product (f : Nat → Nat) : Nat → Nat := primrec 1 (fun i p => p * f i)

theorem product_zero (f : Nat → Nat) : product f 0 = 1 := rfl

theorem product_succ (f : Nat → Nat) : ∀ n, product f (S n) = product f n * f n :=
  fun n => rfl

theorem product_mul (f g : Nat → Nat) :
    ∀ n, product (fun i => f i * g i) n = product f n * product g n := by
  intro n
  induction n with n ih
  · rfl
  · rw [product_succ (fun i => f i * g i), product_succ f, product_succ g, ih,
      mul_mul_mul_comm]

/-- `maximum f n` is the largest of the first `n` values of `f`, with zero for the empty prefix. -/
def maximum (f : Nat → Nat) : Nat → Nat := primrec 0 (fun i m => max m (f i))

theorem maximum_succ (f : Nat → Nat) : ∀ n,
    maximum f (S n) = max (maximum f n) (f n) := fun n => rfl

theorem le_maximum (f : Nat → Nat) (i n : Nat) : i < n → f i ≤ maximum f n := by
  intro hi
  have prefixes : ∀ k, i < k → f i ≤ maximum f k := by
    intro k
    induction k with k ih
    · intro hk
      exact false_elim (not_lt_zero i hk)
    · intro hk
      rcases lt_or_eq_of_le i k (and_left (lt_succ i k) hk) with hil | hie
      · exact le_trans (f i) (maximum f k) (max (maximum f k) (f k))
          (ih hil) (le_max_left (maximum f k) (f k))
      · rw [hie]
        exact le_max_right (maximum f k) (f k)
  exact prefixes n hi

end
