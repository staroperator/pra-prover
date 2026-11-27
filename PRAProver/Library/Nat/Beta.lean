module

public import PRAProver.Library.Nat.DivMod

/-!
# Gödel's beta function

`beta b c i` is the remainder of `b` modulo `1 + (i + 1) * c`. The modulus is always positive.

- `beta_lt` gives the remainder bound.
- `beta_eq_iff` characterizes a value by a quotient and a remainder bound.
- `beta_eq_iff_exists` expresses its graph using arithmetic equations.
- `beta_add_mul` preserves a value when a multiple of its modulus is added.
- `beta_exists` gives parameters representing any finite sequence of numerical values.
-/

@[expose] public section

pra

/-! ## Definition and elementary properties -/

/-- `beta b c i` is the remainder of `b` modulo `1 + (i + 1) * c`. -/
def beta : Nat → Nat → Nat → Nat := fun b c i => b % S (S i * c)

theorem beta_lt : ∀ b c i, beta b c i < S (S i * c) :=
  fun b c i => mod_lt b (S (S i * c)) (succ_ne_zero (S i * c))

theorem beta_le : ∀ b c i, beta b c i ≤ b :=
  fun b c i => mod_le b (S (S i * c))

theorem beta_zero_left : ∀ c i, beta 0 c i = 0 :=
  fun c i => zero_mod (S (S i * c))

theorem beta_zero_right : ∀ b i, beta b 0 i = 0 := by
  intro b i
  rw [beta, mul_zero, mod_one]

theorem beta_of_lt : ∀ b c i, b < S (S i * c) → beta b c i = b :=
  fun b c i h => mod_of_lt b (S (S i * c)) h

theorem beta_add_mul : ∀ b c i k,
    beta (b + S (S i * c) * k) c i = beta b c i :=
  fun b c i k => mod_add_mul b (S (S i * c)) k

/-! ## Arithmetic characterizations -/

/-- A beta value is exactly the remainder in a quotient decomposition at that position. -/
theorem beta_eq_iff : ∀ b c i r,
    beta b c i = r ↔ r < S (S i * c) ∧ ∃ q, S (S i * c) * q + r = b := by
  intro b c i r
  constructor
  · intro h
    constructor
    · have bound := beta_lt b c i
      rw [h] at bound
      exact bound
    · exists b / S (S i * c)
      have he := div_mod b (S (S i * c))
      have h : b % S (S i * c) = r := h
      rw [h] at he
      exact he
  · rintro (hr, q, hq)
    exact and_right (div_mod_unique b (S (S i * c)) q r
      (succ_ne_zero (S i * c)) hq hr)

/-- The graph of beta is expressed using only addition, multiplication, successor, and equality. -/
theorem beta_eq_iff_exists : ∀ b c i r,
    beta b c i = r ↔ ∃ q z, S (S i * c) * q + r = b ∧ r + S z = S (S i * c) := by
  intro b c i r
  constructor
  · intro h
    rcases and_left (beta_eq_iff b c i r) h with (hr, q, hq)
    rcases and_left (le_iff_exists_add (S r) (S (S i * c))) hr with (z, hz)
    exists q, z
    constructor
    · exact hq
    · rw [add_succ, ← succ_add]
      exact hz
  · rintro (q, z, hq, hz)
    apply and_right (beta_eq_iff b c i r)
    constructor
    · apply le_of_add_eq (S r) (S (S i * c)) z
      rw [succ_add, ← add_succ]
      exact hz
    · exact (q, hq)

/-! ## Representing finite sequences -/

/-- Every finite sequence of values has beta parameters `b` and `c`.
The equation holds at each index strictly below `n`; when `n = 0`, there are no constraints. -/
theorem beta_exists (f : Nat → Nat) (n : Nat) :
    ∃ b c, ∀ i, i < n → beta b c i = f i := by
  -- An explicit Bézout identity supplies inverses between the chosen moduli.
  have bezout : ∀ a d q,
      S (a * (d * q)) * ((a + d) * (a + d) * q) + 1 =
        S ((a + d) * (d * q)) * (a * (a + d) * q + 1) := by
    intro a d q
    let b := a + d
    let c := d * q
    have square : b * b * q = b * c + a * b * q := by
      change (a + d) * b * q = b * (d * q) + a * b * q
      rw [mul_add_right_distrib a d b, mul_add_right_distrib (a * b) (d * b) q,
        mul_comm d b, mul_assoc b d q, add_comm]
    have product : (a * c) * (b * b * q) = (b * c) * (a * b * q) := by
      rw [← mul_assoc (a * c) (b * b) q, ← mul_assoc (b * c) (a * b) q,
        mul_mul_mul_comm a c b b, mul_mul_mul_comm b c a b, mul_comm a b]
    change S (a * c) * (b * b * q) + 1 = S (b * c) * (a * b * q + 1)
    rw [succ_mul (a * c) (b * b * q), product, square,
      succ_mul (b * c) (a * b * q + 1),
      mul_add_left_distrib (b * c) (a * b * q) 1, mul_one (b * c)]
    change (b * c) * (a * b * q) + (b * c + a * b * q) + 1 =
      ((b * c) * (a * b * q) + b * c) + (a * b * q + 1)
    rw [add_assoc ((b * c) * (a * b * q)) (b * c + a * b * q) 1,
      add_assoc (b * c) (a * b * q) 1,
      add_assoc ((b * c) * (a * b * q)) (b * c) (a * b * q + 1)]
  let modulus : Nat → Nat → Nat := fun c i => S (S i * c)
  let inverse : Nat → Nat → Nat → Nat := fun c i k =>
    (S k * c) * (S k * S k * (c / (k - i)))
  have inverse_spec : ∀ c i k, i < k → c % (k - i) = 0 →
      (modulus c i * inverse c i k) % modulus c k = 1 % modulus c k := by
    intro c i k hik hdiv
    have hc : (k - i) * (c / (k - i)) = c := by
      have h := div_mod c (k - i)
      rw [hdiv, add_zero] at h
      exact h
    have hk : S i + (k - i) = S k := by
      rw [succ_add, add_comm i (k - i), sub_add_cancel_of_le k i (le_of_lt i k hik)]
    have h := bezout (S i) (k - i) (c / (k - i))
    rw [hc, hk] at h
    exact inverse_of_negative (S (S i * c)) (S k * S k * (c / (k - i)))
      (S i * S k * (c / (k - i)) + 1) (S k * c) h
  -- The parameter exceeds the entries and is divisible by every positive number up to n.
  let parameter : Nat → Nat := fun n => factorial n * S (maximum f n)
  have parameter_mod : ∀ n d, ¬ d = 0 → d ≤ n → parameter n % d = 0 := by
    intro n d hd hdn
    change (factorial n * S (maximum f n)) % d = 0
    rw [mod_mul_eq (factorial n) (S (maximum f n)) d,
      factorial_mod d n hd hdn, zero_mul, zero_mod]
  have parameter_bound : ∀ n i, i < n → f i < modulus (parameter n) i := by
    intro n i hi
    have hmax : S (maximum f n) ≤ parameter n :=
      le_mul_of_pos (S (maximum f n)) (factorial n) (factorial_ne_zero n)
    have hm : parameter n ≤ S i * parameter n :=
      le_mul_of_pos (parameter n) (S i) (succ_ne_zero i)
    apply and_right (lt_succ (f i) (S i * parameter n))
    exact le_trans (f i) (maximum f n) (S i * parameter n)
      (le_maximum f i n hi) (le_trans (maximum f n) (S (maximum f n))
        (S i * parameter n) (le_succ_self (maximum f n))
        (le_trans (S (maximum f n)) (parameter n) (S i * parameter n) hmax hm))
  let modulusProduct : Nat → Nat → Nat := fun c k => product (modulus c) k
  let inverseProduct : Nat → Nat → Nat := fun c k => product (fun i => inverse c i k) k
  have modulusProduct_mod : ∀ c i k, i < k → modulusProduct c k % modulus c i = 0 := by
    intro c i k hi
    exact product_mod_zero (modulus c) k i (modulus c i) hi
      (mod_self (modulus c i))
  have inverseProduct_spec : ∀ n k, k ≤ n →
      (modulusProduct (parameter n) k * inverseProduct (parameter n) k) %
        modulus (parameter n) k = 1 % modulus (parameter n) k := by
    intro n k hk
    change (product (modulus (parameter n)) k *
      product (fun i => inverse (parameter n) i k) k) % modulus (parameter n) k =
        1 % modulus (parameter n) k
    rw [← product_mul (modulus (parameter n))
        (fun i => inverse (parameter n) i k)]
    apply product_mod_one
      (fun i => modulus (parameter n) i * inverse (parameter n) i k)
      k (modulus (parameter n) k)
    intro i hi
    apply inverse_spec (parameter n) i k hi
    exact parameter_mod n (k - i) (not_le_of_lt i k hi)
      (le_trans (k - i) k n (sub_le k i) hk)
  -- Each adjustment sets the next remainder and preserves the earlier ones.
  let adjust : Nat → Nat → Nat → Nat := fun c k b =>
    b + modulusProduct c k * (inverseProduct c k * (f k + modulus c k - b % modulus c k))
  let dividend : Nat → Nat → Nat := fun c => primrec 0 (adjust c)
  have dividend_succ : ∀ c k,
      dividend c (S k) = adjust c k (dividend c k) := fun c k => rfl
  have adjust_before : ∀ c k b i, i < k → beta (adjust c k b) c i = beta b c i := by
    intro c k b i hi
    change (b + modulusProduct c k *
      (inverseProduct c k * (f k + modulus c k - b % modulus c k))) % modulus c i =
        b % modulus c i
    rw [mod_add_eq b (modulusProduct c k *
        (inverseProduct c k * (f k + modulus c k - b % modulus c k))) (modulus c i),
      mod_mul_eq (modulusProduct c k)
        (inverseProduct c k * (f k + modulus c k - b % modulus c k)) (modulus c i),
      modulusProduct_mod c i k hi, zero_mul, zero_mod, add_zero, mod_mod]
  have adjust_last : ∀ n k b, k < n → beta (adjust (parameter n) k b) (parameter n) k = f k := by
    intro n k b hk
    exact adjusted_remainder b (modulusProduct (parameter n) k)
      (inverseProduct (parameter n) k) (modulus (parameter n) k) (f k)
      (succ_ne_zero (S k * parameter n)) (parameter_bound n k hk)
      (inverseProduct_spec n k (le_of_lt k n hk))
  have dividend_spec : ∀ n i, i < n → beta (dividend (parameter n) n) (parameter n) i = f i := by
    intro n i hi
    have prefixes : ∀ k, k ≤ n → i < k →
        beta (dividend (parameter n) k) (parameter n) i = f i := by
      intro k
      induction k with k ih
      · intro hkn hik
        exact false_elim (not_lt_zero i hik)
      · intro hkn hik
        rw [dividend_succ (parameter n)]
        rcases lt_or_eq_of_le i k (and_left (lt_succ i k) hik) with hil | hie
        · rw [adjust_before (parameter n) k (dividend (parameter n) k) i hil]
          exact ih (le_trans k (S k) n (le_succ_self k) hkn) hil
        · rw [hie]
          exact adjust_last n k (dividend (parameter n) k) hkn
    exact prefixes n (le_refl n) hi
  exists dividend (parameter n) n, parameter n
  exact dividend_spec n

end
