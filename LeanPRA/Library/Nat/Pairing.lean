module

public import LeanPRA.Library.Nat.Bounded

/-!
# Numerical pairing in PRA

Cantor diagonal pairing between `Nat × Nat` and `Nat`:

- `triangular n` is the sum `1 + 2 + … + n`, and `diagonal z` is the unique `n` with
  `triangular n ≤ z < triangular (S n)`.
- `pair x y` encodes `(x, y)` as `triangular (x + y) + x`.
- `unpairLeft z` and `unpairRight z` recover the first and second components of `z`.

The pairing enumerates every natural number once (`pair (unpairLeft z) (unpairRight z) = z`), and
each component is bounded by the code (`x ≤ pair x y` and `y ≤ pair x y`).
-/

@[expose] public section

pra

/-- The triangular number `1 + 2 + … + n`, with `triangular 0 = 0`. -/
def triangular : Nat → Nat := fun n => primrec 0 (fun k r => r + S k) n

theorem triangular_zero : triangular 0 = 0 := rfl

theorem triangular_succ : ∀ n, triangular (S n) = triangular n + S n := fun n => rfl

theorem le_triangular : ∀ n, n ≤ triangular n := by
  intro n
  induction n with k ih
  · exact le_refl 0
  · exact le_add_left (triangular k) (S k)

theorem triangular_step : ∀ n, triangular n < triangular (S n) := by
  intro n
  rw [triangular_succ]
  have h := add_lt_add_left 0 (S n) (triangular n)
    (pos_of_ne_zero (S n) (succ_ne_zero n))
  rw [add_zero] at h
  exact h

theorem triangular_mono : ∀ x y, x ≤ y → triangular x ≤ triangular y :=
  monotone_of_succ triangular (fun n => le_of_lt _ _ (triangular_step n))

theorem triangular_strict : ∀ x y, x < y → triangular x < triangular y := by
  intro x y h
  exact lt_of_lt_of_le _ _ _ (triangular_step x) (triangular_mono (S x) y h)

/-- The diagonal index of a code `z`: the first `n ≤ z` with `z < triangular (S n)`. -/
def diagonal : Nat → Nat :=
  fun z => findBelow (fun n => ltb z (triangular (S n))) (S z)

theorem diagonal_lt : ∀ z, diagonal z < S z := by
  intro z
  have h : ¬ ltb z (triangular (S z)) = 0 :=
    and_right (ltb_ne_zero _ _)
      (lt_of_lt_of_le z (S z) _ (lt_succ_self z) (le_triangular (S z)))
  exact lt_of_le_of_lt _ z (S z)
    (findBelow_le_of_witness (fun n => ltb z (triangular (S n))) z (S z) h)
    (lt_succ_self z)

theorem diagonal_bounds : ∀ z,
    triangular (diagonal z) ≤ z ∧ z < triangular (S (diagonal z)) := by
  intro z
  constructor
  · rcases zero_or_succ_pred (diagonal z) with hz | hs
    · rw [hz, triangular_zero]; exact zero_le z
    · have hp : pred (diagonal z) < diagonal z := by
        rw [hs]; exact lt_succ_self (pred (diagonal z))
      have hf := findBelow_min (fun n => ltb z (triangular (S n)))
        (pred (diagonal z)) (S z) hp
      rw [← hs] at hf
      exact le_of_not_lt _ z (and_left (ltb_eq_zero _ _) hf)
  · exact and_left (ltb_ne_zero _ _)
      (findBelow_spec (fun n => ltb z (triangular (S n))) (S z) (diagonal_lt z))

theorem diagonal_unique : ∀ z n,
    triangular n ≤ z → z < triangular (S n) → diagonal z = n := by
  intro z n hlo hhi
  apply findBelow_eq (fun k => ltb z (triangular (S k))) n (S z)
  · exact and_right (lt_succ n z) (le_trans n (triangular n) z (le_triangular n) hlo)
  · exact and_right (ltb_ne_zero _ _) hhi
  · intro k hk
    apply and_right (ltb_eq_zero _ _)
    intro h
    exact not_le_of_lt z (triangular (S k)) h
      (le_trans _ _ z (triangular_mono (S k) n hk) hlo)

/-- Encode `(x, y)` as the natural number `triangular (x + y) + x`. -/
def pair : Nat → Nat → Nat := fun x y => triangular (x + y) + x

/-- Recover the first component `z - triangular (diagonal z)` of a code `z`. -/
def unpairLeft : Nat → Nat := fun z => z - triangular (diagonal z)

/-- Recover the second component `diagonal z - unpairLeft z` of a code `z`. -/
def unpairRight : Nat → Nat := fun z => diagonal z - unpairLeft z

theorem diagonal_pair : ∀ x y, diagonal (pair x y) = x + y := by
  intro x y
  apply diagonal_unique (pair x y) (x + y)
  · exact le_add_right (triangular (x + y)) x
  · change triangular (x + y) + x < triangular (S (x + y))
    rw [triangular_succ]
    exact add_lt_add_left x (S (x + y)) (triangular (x + y))
      (and_right (lt_succ x (x + y)) (le_add_right x y))

theorem unpairLeft_pair : ∀ x y, unpairLeft (pair x y) = x := by
  intro x y
  rw [unpairLeft, diagonal_pair, pair, add_comm, add_sub_self_right]

theorem unpairRight_pair : ∀ x y, unpairRight (pair x y) = y := by
  intro x y
  rw [unpairRight, diagonal_pair, unpairLeft_pair, add_comm, add_sub_self_right]

theorem unpairLeft_le_diagonal : ∀ z, unpairLeft z ≤ diagonal z := by
  intro z
  apply and_left (lt_succ (unpairLeft z) (diagonal z))
  apply lt_of_add_lt_add_left (unpairLeft z) (S (diagonal z)) (triangular (diagonal z))
  have he : triangular (diagonal z) + unpairLeft z = z := by
    rw [add_comm]
    exact sub_add_cancel_of_le z _ (and_left (diagonal_bounds z))
  rw [he, ← triangular_succ]
  exact and_right (diagonal_bounds z)

/-- Re-encoding `unpairLeft z` and `unpairRight z` recovers `z`. -/
theorem pair_unpair : ∀ z, pair (unpairLeft z) (unpairRight z) = z := by
  intro z
  have hs : unpairLeft z + unpairRight z = diagonal z := by
    rw [add_comm]
    exact sub_add_cancel_of_le (diagonal z) (unpairLeft z) (unpairLeft_le_diagonal z)
  rw [pair, hs, add_comm]
  exact sub_add_cancel_of_le z _ (and_left (diagonal_bounds z))

theorem pair_injective : ∀ a b c d, pair a b = pair c d → a = c ∧ b = d := by
  intro a b c d h
  constructor
  · have he := eq_congr unpairLeft h
    rw [unpairLeft_pair, unpairLeft_pair] at he; exact he
  · have he := eq_congr unpairRight h
    rw [unpairRight_pair, unpairRight_pair] at he; exact he

theorem left_le_pair : ∀ x y, x ≤ pair x y :=
  fun x y => le_add_left (triangular (x + y)) x

theorem right_le_pair : ∀ x y, y ≤ pair x y := by
  intro x y
  exact le_trans y (x + y) (pair x y) (le_add_left x y)
    (le_trans (x + y) (triangular (x + y)) (pair x y)
      (le_triangular (x + y)) (le_add_right _ x))

theorem unpairLeft_le : ∀ z, unpairLeft z ≤ z :=
  fun z => sub_le z (triangular (diagonal z))

theorem unpairRight_le : ∀ z, unpairRight z ≤ z := by
  intro z
  have h := right_le_pair (unpairLeft z) (unpairRight z)
  rw [pair_unpair] at h; exact h

theorem pair_lt_of_sum_lt : ∀ a b c d, a + b < c + d → pair a b < pair c d := by
  intro a b c d h
  have htop := and_right (diagonal_bounds (pair a b))
  rw [diagonal_pair] at htop
  exact lt_of_lt_of_le (pair a b) (triangular (S (a + b))) (pair c d) htop
    (le_trans _ (triangular (c + d)) _ (triangular_mono (S (a + b)) (c + d) h)
      (le_add_right (triangular (c + d)) c))

theorem pair_lt_left : ∀ a b c d, a < c → b ≤ d → pair a b < pair c d := by
  intro a b c d ha hb
  apply pair_lt_of_sum_lt a b c d
  exact lt_of_lt_of_le (a + b) (c + b) (c + d)
    (add_lt_add_right a c b ha) (add_le_add_left b d c hb)

theorem pair_lt_right : ∀ a b c d, a ≤ c → b < d → pair a b < pair c d := by
  intro a b c d ha hb
  apply pair_lt_of_sum_lt a b c d
  exact lt_of_le_of_lt (a + b) (c + b) (c + d)
    (add_le_add_right a c b ha) (add_lt_add_left b d c hb)

theorem pair_mono : ∀ a b c d, a ≤ c → b ≤ d → pair a b ≤ pair c d := by
  intro a b c d ha hb
  rcases lt_or_eq_of_le a c ha with hlt | he
  · exact le_of_lt _ _ (pair_lt_left a b c d hlt hb)
  · rw [he]
    rcases lt_or_eq_of_le b d hb with hlt | he'
    · exact le_of_lt _ _ (pair_lt_right c b c d (le_refl c) hlt)
    · rw [he']; exact le_refl _

theorem triangular_double : ∀ n, triangular n + triangular n = n * S n := by
  intro n
  induction n with k ih
  · rfl
  · have h : S k * S (S k) = k * S k + (S k + S k) := by
      rw [mul_succ, succ_mul, add_assoc]
    change triangular k + S k + (triangular k + S k) = S k * S (S k)
    rw [add_add_add_comm, ih, h]

theorem pair_double : ∀ x y, pair x y + pair x y = (x + y) * S (x + y) + (x + x) := by
  intro x y
  rw [pair, add_add_add_comm, triangular_double]

end
