module

public import LeanPRA.Library.Nat.Pairing

/-!
# Numerical tuples of fixed positive length

Tuples are encoded in `Nat`, with their positive length supplied separately:

- `(a)` is encoded as `a`.
- `(a, b)` is encoded as `pair a b`.
- `(a, b, c)` is encoded as `pair a (pair b c)`.

Unpairing recovers successive components; the final component is the remaining code itself.
Indices start at zero. For each fixed positive length, every code describes a unique tuple.

- `Tuple.get` reads a component at an index below the supplied length.
  `Tuple.get_le` bounds every component by the tuple code.
- `Tuple.ext` proves equality from equality of all components.
- `Tuple.map` applies a function to every component.
  `Tuple.map_congr_of_get_eq` compares functions only on those components.
- `Tuple.max` takes the maximum component.
-/

@[expose] public section

pra

namespace Tuple

/--
`Tuple.get n xs i` reads component `i` of a tuple code `xs` of positive length `n`, for `i < n`.
-/
def get : Nat → Nat → Nat → Nat := fun n xs i =>
  ite (eqb (S i) n) (iter unpairRight i xs) (unpairLeft (iter unpairRight i xs))

theorem get_one : ∀ x, get 1 x 0 = x := fun x => rfl

theorem get_last : ∀ n xs, get (S n) xs n = iter unpairRight n xs := by
  intro n xs
  rw [get, eqb_self, ite_succ]

theorem get_of_lt_last : ∀ n xs i, i < n →
    get (S n) xs i = unpairLeft (iter unpairRight i xs) := by
  intro n xs i hi
  have h : ¬ S i = S n := by
    intro he
    have he' := succ_inj he
    rw [he'] at hi
    exact not_lt_self n hi
  rw [get, and_right (eqb_eq_zero (S i) (S n)) h, ite_zero]

theorem get_zero : ∀ n xs, get (S (S n)) xs 0 = unpairLeft xs :=
  fun n xs => get_of_lt_last (S n) xs 0 (pos_of_ne_zero (S n) (succ_ne_zero n))

theorem get_succ : ∀ n xs i, get (S n) xs (S i) = get n (unpairRight xs) i := by
  intro n xs i
  have he : eqb (S (S i)) (S n) = eqb (S i) n := by
    change band (isZero (S (S i) - S n)) (isZero (S n - S (S i))) =
      band (isZero (S i - n)) (isZero (n - S i))
    rw [succ_sub_succ, succ_sub_succ]
  have ht : iter unpairRight (S i) xs = iter unpairRight i (unpairRight xs) := by
    rw [iter_succ unpairRight, iter_succ_apply unpairRight]
  change ite (eqb (S (S i)) (S n)) (iter unpairRight (S i) xs)
      (unpairLeft (iter unpairRight (S i) xs)) =
    ite (eqb (S i) n) (iter unpairRight i (unpairRight xs))
      (unpairLeft (iter unpairRight i (unpairRight xs)))
  rw [he, ht]

theorem get_pair_zero : ∀ n x xs, get (S (S n)) (pair x xs) 0 = x := by
  intro n x xs
  rw [get_zero, unpairLeft_pair]

theorem get_pair_succ : ∀ n x xs i, get (S n) (pair x xs) (S i) = get n xs i := by
  intro n x xs i
  rw [get_succ, unpairRight_pair]

theorem get_two_one : ∀ x y, get 2 (pair x y) 1 = y := by
  intro x y
  rw [get_pair_succ, get_one]

theorem pair_get_two : ∀ xs, pair (get 2 xs 0) (get 2 xs 1) = xs := by
  intro xs
  rw [get_zero, get_last, iter_succ unpairRight, iter_zero unpairRight]
  exact pair_unpair xs

theorem get_le : ∀ n xs i, get n xs i ≤ xs := by
  intro n xs i
  have hi := iter_invariant (fun y => y ≤ xs) unpairRight
    (fun y hy => le_trans _ _ _ (unpairRight_le y) hy) xs (le_refl xs) i
  rw [get]
  by_cases h : eqb (S i) n = 0
  · rw [h, ite_zero]
    exact le_trans _ _ _ (unpairLeft_le (iter unpairRight i xs)) hi
  · rw [ite_of_ne_zero _ _ _ h]
    exact hi

/-- Two tuples of the same positive length are equal when all their components agree. -/
theorem ext : ∀ n xs ys,
    (∀ i, i < S n → get (S n) xs i = get (S n) ys i) → xs = ys := by
  intro n xs ys entries
  apply induction_down (fun i => iter unpairRight i xs = iter unpairRight i ys) n
  · have h := entries n (lt_succ_self n)
    rw [get_last, get_last] at h
    exact h
  · intro i hi ih
    have h := entries i (lt_of_lt_of_le i n (S n) hi (le_succ_self n))
    rw [get_of_lt_last n xs i hi, get_of_lt_last n ys i hi] at h
    have ht : unpairRight (iter unpairRight i xs) = unpairRight (iter unpairRight i ys) := ih
    have hx := pair_unpair (iter unpairRight i xs)
    rw [h, ht] at hx
    exact eq_trans (eq_symm hx) (pair_unpair (iter unpairRight i ys))

/--
`Tuple.map f n xs` applies `f` to all `n` components of tuple code `xs`, rebuilding the tuple
from right to left. For `n = 0`, the result is `0`.
-/
def map (f : Nat → Nat) : Nat → Nat → Nat := fun n xs =>
  primrec 0 (fun i r => ite i (pair (f (get n xs (n - S i))) r)
    (f (get n xs (pred n)))) n

theorem map_zero (f : Nat → Nat) : ∀ xs, map f 0 xs = 0 := fun xs => rfl

theorem map_one (f : Nat → Nat) : ∀ x, map f 1 x = f x := by
  intro x
  rfl

theorem map_two (f : Nat → Nat) : ∀ x y, map f 2 (pair x y) = pair (f x) (f y) := by
  intro x y
  change pair (f (unpairLeft (pair x y))) (f (unpairRight (pair x y))) = pair (f x) (f y)
  rw [unpairLeft_pair, unpairRight_pair]

theorem map_three (f : Nat → Nat) : ∀ x y z,
    map f 3 (pair x (pair y z)) = pair (f x) (pair (f y) (f z)) := by
  intro x y z
  change pair (f (get 3 (pair x (pair y z)) 0))
    (pair (f (get 3 (pair x (pair y z)) 1)) (f (get 3 (pair x (pair y z)) 2))) =
    pair (f x) (pair (f y) (f z))
  rw [get_pair_zero, get_pair_succ, get_pair_zero, get_pair_succ, get_two_one]

theorem map_congr_of_get_eq (f g : Nat → Nat) : ∀ n xs,
    (∀ i, i < n → f (get n xs i) = g (get n xs i)) → map f n xs = map g n xs := by
  intro n xs h
  let stepF : Nat → Nat → Nat := fun i r =>
    ite i (pair (f (get n xs (n - S i))) r) (f (get n xs (pred n)))
  let stepG : Nat → Nat → Nat := fun i r =>
    ite i (pair (g (get n xs (n - S i))) r) (g (get n xs (pred n)))
  by_cases hn : n = 0
  · rw [hn, map_zero f, map_zero g]
  have hp := lt_succ_self (pred n)
  rw [succ_pred n hn] at hp
  have stepEq : ∀ i r, stepF i r = stepG i r := by
    intro i r
    change ite i (pair (f (get n xs (n - S i))) r) (f (get n xs (pred n))) =
      ite i (pair (g (get n xs (n - S i))) r) (g (get n xs (pred n)))
    rw [h (n - S i) (sub_lt_of_pos n (S i) (pos_of_ne_zero n hn)
      (pos_of_ne_zero (S i) (succ_ne_zero i))), h (pred n) hp]
  have build : ∀ k, primrec 0 stepF k = primrec 0 stepG k := by
    intro k
    induction k with j ih
    · rfl
    · exact eq_trans (stepEq j (primrec 0 stepF j)) (eq_congr (stepG j) ih)
  exact build n

theorem map_congr (f g : Nat → Nat) :
    (∀ x, f x = g x) → ∀ n xs, map f n xs = map g n xs :=
  fun h n xs => map_congr_of_get_eq f g n xs (fun i _ => h (get n xs i))

/-- `Tuple.max n xs` returns the maximum of the `n` components of positive-length tuple code `xs`. -/
def max : Nat → Nat → Nat := fun n xs =>
  primrec (get n xs 0) (fun i r => _root_.max r (get n xs (S i))) (pred n)

theorem max_one : ∀ x, max 1 x = x := fun x => rfl

theorem max_two : ∀ x y, max 2 (pair x y) = _root_.max x y := by
  intro x y
  change _root_.max (unpairLeft (pair x y)) (unpairRight (pair x y)) = _root_.max x y
  rw [unpairLeft_pair, unpairRight_pair]

theorem max_three : ∀ x y z,
    max 3 (pair x (pair y z)) = _root_.max (_root_.max x y) z := by
  intro x y z
  change _root_.max (_root_.max (get 3 (pair x (pair y z)) 0) (get 3 (pair x (pair y z)) 1))
    (get 3 (pair x (pair y z)) 2) = _root_.max (_root_.max x y) z
  rw [get_pair_zero, get_pair_succ, get_pair_zero, get_pair_succ, get_two_one]

end Tuple

end
