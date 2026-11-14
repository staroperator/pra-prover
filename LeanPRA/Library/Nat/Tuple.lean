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
  `Tuple.map_pair_succ` computes a mapped tuple from its head and tail.
  `Tuple.get_map` reads a mapped component, and `Tuple.map_map` composes two maps.
  `Tuple.map_id` preserves a tuple under the identity function.
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

theorem map_pair_succ (f : Nat → Nat) : ∀ n x xs,
    map f (S (S n)) (pair x xs) = pair (f x) (map f (S n) xs) := by
  intro n x xs
  let large := fun i r => ite i
    (pair (f (get (S (S n)) (pair x xs) (S (S n) - S i))) r)
    (f (get (S (S n)) (pair x xs) (pred (S (S n)))))
  let small := fun i r => ite i
    (pair (f (get (S n) xs (S n - S i))) r) (f (get (S n) xs (pred (S n))))
  have entry : ∀ i, i ≤ n →
      get (S (S n)) (pair x xs) (S (S n) - S i) = get (S n) xs (S n - S i) := by
    intro i hi
    rw [succ_sub_succ, succ_sub_of_le n i hi, get_pair_succ, succ_sub_succ]
  have step : ∀ i r, i ≤ n → large i r = small i r := by
    intro i r hi
    change ite i (pair (f (get (S (S n)) (pair x xs) (S (S n) - S i))) r)
        (f (get (S (S n)) (pair x xs) (pred (S (S n))))) =
      ite i (pair (f (get (S n) xs (S n - S i))) r)
        (f (get (S n) xs (pred (S n))))
    rw [entry i hi, pred_succ, get_pair_succ, pred_succ]
  have builtPrefix : ∀ k, k ≤ S n → primrec 0 large k = primrec 0 small k := by
    intro k
    induction k with j ih
    · intro hk
      rfl
    · intro hk
      have hj := and_left (succ_le_succ j n) hk
      change large j (primrec 0 large j) = small j (primrec 0 small j)
      rw [step j (primrec 0 large j) hj,
        ih (le_trans j n (S n) hj (le_succ_self n))]
  change large (S n) (primrec 0 large (S n)) = pair (f x) (map f (S n) xs)
  rw [builtPrefix (S n) (le_refl (S n))]
  change pair (f (get (S (S n)) (pair x xs) (S (S n) - S (S n))))
      (map f (S n) xs) = pair (f x) (map f (S n) xs)
  rw [sub_self, get_pair_zero]

/-- Reading a mapped tuple applies the function to the original component. -/
theorem get_map (f : Nat → Nat) : ∀ n xs i, i < n →
    get n (map f n xs) i = f (get n xs i) := by
  have total : ∀ k, ite (ltb (unpairRight (unpairRight k)) (unpairLeft k))
        (get (unpairLeft k) (map f (unpairLeft k) (unpairLeft (unpairRight k)))
          (unpairRight (unpairRight k))) 0 =
      ite (ltb (unpairRight (unpairRight k)) (unpairLeft k))
        (f (get (unpairLeft k) (unpairLeft (unpairRight k)) (unpairRight (unpairRight k)))) 0 := by
    apply strong_induction_eq
      (fun k => ite (ltb (unpairRight (unpairRight k)) (unpairLeft k))
        (get (unpairLeft k) (map f (unpairLeft k) (unpairLeft (unpairRight k)))
          (unpairRight (unpairRight k))) 0)
      (fun k => ite (ltb (unpairRight (unpairRight k)) (unpairLeft k))
        (f (get (unpairLeft k) (unpairLeft (unpairRight k)) (unpairRight (unpairRight k)))) 0)
    intro k ih
    let n := unpairLeft k
    let xs := unpairLeft (unpairRight k)
    let i := unpairRight (unpairRight k)
    have hk : pair n (pair xs i) = k := by
      rw [pair_unpair, pair_unpair]
    change ite (ltb i n) (get n (map f n xs) i) 0 =
      ite (ltb i n) (f (get n xs i)) 0
    by_cases hi : i < n
    · rw [and_right (ltb_eq_one i n) hi, ite_succ, ite_succ]
      rcases zero_or_succ_pred n with hn | hn
      · rw [hn] at hi
        exact false_elim (not_lt_zero i hi)
      · rcases zero_or_succ_pred (pred n) with hm | hm
        · have hz : i = 0 := by
            rw [hn, hm] at hi
            exact le_zero i (and_left (lt_succ i 0) hi)
          rw [hn, hm, hz, map_one f, get_one, get_one]
        · have shape : xs = pair (unpairLeft xs) (unpairRight xs) := eq_symm (pair_unpair xs)
          rcases zero_or_succ_pred i with hz | hz
          · rw [hn, hm, shape, hz, map_pair_succ f, get_pair_zero, get_pair_zero]
          · have smaller : pair (pred n) (pair (unpairRight xs) (pred i)) < k := by
              have hnlt : pred n < n := by
                rw [hn, pred_succ]
                exact lt_succ_self (pred n)
              have hile : pred i ≤ i := by
                rw [hz, pred_succ]
                exact le_succ_self (pred i)
              have h := pair_lt_left (pred n) (pair (unpairRight xs) (pred i)) n
                (pair xs i) hnlt
                (pair_mono _ _ _ _ (unpairRight_le xs) hile)
              rw [hk] at h
              exact h
            have hit : pred i < pred n := by
              rw [hn, hz] at hi
              exact and_left (succ_le_succ (S (pred i)) (pred n)) hi
            have ht := ih (pair (pred n) (pair (unpairRight xs) (pred i))) smaller
            rw [unpairLeft_pair, unpairRight_pair,
              unpairLeft_pair, unpairRight_pair] at ht
            rw [and_right (ltb_eq_one (pred i) (pred n)) hit, ite_succ, ite_succ] at ht
            rw [hn, hm, shape, hz, map_pair_succ f, get_pair_succ, get_pair_succ]
            rw [hm] at ht
            exact ht
    · rw [ltb_eq_zero_of_ge i n (le_of_not_lt n i hi), ite_zero, ite_zero]
  intro n xs i hi
  have h := total (pair n (pair xs i))
  rw [unpairLeft_pair, unpairRight_pair,
    unpairLeft_pair, unpairRight_pair] at h
  rw [and_right (ltb_eq_one i n) hi, ite_succ, ite_succ] at h
  exact h

/-- Mapping a function over a mapped tuple is pointwise function composition. -/
theorem map_map (f g : Nat → Nat) : ∀ n xs,
    map f n (map g n xs) = map (fun x => f (g x)) n xs := by
  have total : ∀ k,
      map f (unpairLeft k) (map g (unpairLeft k) (unpairRight k)) =
        map (fun x => f (g x)) (unpairLeft k) (unpairRight k) := by
    apply strong_induction_eq
      (fun k => map f (unpairLeft k) (map g (unpairLeft k) (unpairRight k)))
      (fun k => map (fun x => f (g x)) (unpairLeft k) (unpairRight k))
    intro k ih
    let n := unpairLeft k
    let xs := unpairRight k
    have hk : pair n xs = k := pair_unpair k
    rcases zero_or_succ_pred n with hn | hn
    · rw [hn, map_zero f, map_zero (fun x => f (g x))]
    · rcases zero_or_succ_pred (pred n) with hm | hm
      · rw [hn, hm, map_one g, map_one f, map_one (fun x => f (g x))]
      · have shape : xs = pair (unpairLeft xs) (unpairRight xs) := eq_symm (pair_unpair xs)
        have smaller : pair (S (pred (pred n))) (unpairRight xs) < k := by
          have hl : pair (S (pred (pred n))) (unpairRight xs) < pair n xs := by
            apply pair_lt_left
            · rw [hn, hm]
              exact lt_succ_self (S (pred (pred n)))
            · exact unpairRight_le xs
          rw [hk] at hl
          exact hl
        have ht := ih (pair (S (pred (pred n))) (unpairRight xs)) smaller
        rw [unpairLeft_pair, unpairRight_pair] at ht
        change map f n (map g n xs) = map (fun x => f (g x)) n xs
        rw [hn, hm, shape, map_pair_succ g, map_pair_succ f,
          map_pair_succ (fun x => f (g x)), ht]
  intro n xs
  have h := total (pair n xs)
  rw [unpairLeft_pair, unpairRight_pair] at h
  exact h

/-- Mapping the identity over a positive-length tuple preserves its code. -/
theorem map_id : ∀ n xs, map (fun x => x) (S n) xs = xs := by
  have total : ∀ k, map (fun x => x) (S (unpairLeft k)) (unpairRight k) = unpairRight k := by
    apply strong_induction_eq
      (fun k => map (fun x => x) (S (unpairLeft k)) (unpairRight k)) unpairRight
    intro k ih
    let n := unpairLeft k
    let xs := unpairRight k
    have hk : pair n xs = k := pair_unpair k
    rcases zero_or_succ_pred n with hn | hn
    · rw [hn, map_one (fun x => x)]
    · have smaller : pair (pred n) (unpairRight xs) < k := by
        have hlt : pred n < n := by
          rw [hn, pred_succ]
          exact lt_succ_self (pred n)
        have h := pair_lt_left (pred n) (unpairRight xs) n xs hlt (unpairRight_le xs)
        rw [hk] at h
        exact h
      have ht := ih (pair (pred n) (unpairRight xs)) smaller
      rw [unpairLeft_pair, unpairRight_pair] at ht
      have shape : xs = pair (unpairLeft xs) (unpairRight xs) := eq_symm (pair_unpair xs)
      change map (fun x => x) (S n) xs = xs
      rw [hn, shape, map_pair_succ (fun x => x), ht]
  intro n xs
  have h := total (pair n xs)
  rw [unpairLeft_pair, unpairRight_pair] at h
  exact h

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

/-- A function that is larger on every component gives a larger tuple code. -/
theorem map_mono (f g : Nat → Nat) : ∀ n xs,
    (∀ i, i < n → f (get n xs i) ≤ g (get n xs i)) → map f n xs ≤ map g n xs := by
  intro n xs h
  let stepF : Nat → Nat → Nat := fun i r =>
    ite i (pair (f (get n xs (n - S i))) r) (f (get n xs (pred n)))
  let stepG : Nat → Nat → Nat := fun i r =>
    ite i (pair (g (get n xs (n - S i))) r) (g (get n xs (pred n)))
  by_cases hn : n = 0
  · rw [hn, map_zero f, map_zero g]
    exact le_refl 0
  have hp := lt_succ_self (pred n)
  rw [succ_pred n hn] at hp
  have build : ∀ k, primrec 0 stepF k ≤ primrec 0 stepG k := by
    intro k
    induction k with j ih
    · exact le_refl 0
    · by_cases hj : j = 0
      · change ite j (pair (f (get n xs (n - S j))) (primrec 0 stepF j)) (f (get n xs (pred n))) ≤
          ite j (pair (g (get n xs (n - S j))) (primrec 0 stepG j)) (g (get n xs (pred n)))
        rw [hj, ite_zero, ite_zero]
        exact h (pred n) hp
      · change ite j (pair (f (get n xs (n - S j))) (primrec 0 stepF j)) (f (get n xs (pred n))) ≤
          ite j (pair (g (get n xs (n - S j))) (primrec 0 stepG j)) (g (get n xs (pred n)))
        rw [ite_of_ne_zero j _ _ hj, ite_of_ne_zero j _ _ hj]
        exact pair_mono _ _ _ _
          (h (n - S j) (sub_lt_of_pos n (S j) (pos_of_ne_zero n hn)
            (pos_of_ne_zero (S j) (succ_ne_zero j)))) ih
  exact build n

/-- If on every component either `t ≤ f x` or `f x = g x`, then either `t` is at most the
mapped tuple code or the two mapped tuple codes are equal. -/
theorem map_dichotomy (f g : Nat → Nat) (t : Nat) : ∀ n xs,
    (∀ i, i < n → t ≤ f (get n xs i) ∨ f (get n xs i) = g (get n xs i)) →
      t ≤ map f n xs ∨ map f n xs = map g n xs := by
  intro n xs h
  let stepF : Nat → Nat → Nat := fun i r =>
    ite i (pair (f (get n xs (n - S i))) r) (f (get n xs (pred n)))
  let stepG : Nat → Nat → Nat := fun i r =>
    ite i (pair (g (get n xs (n - S i))) r) (g (get n xs (pred n)))
  by_cases hn : n = 0
  · right
    rw [hn, map_zero f, map_zero g]
  have hp := lt_succ_self (pred n)
  rw [succ_pred n hn] at hp
  have build : ∀ k,
      t ≤ primrec 0 stepF k ∨ primrec 0 stepF k = primrec 0 stepG k := by
    intro k
    induction k with j ih
    · right
      rfl
    · by_cases hj : j = 0
      · change
          t ≤ ite j (pair (f (get n xs (n - S j))) (primrec 0 stepF j)) (f (get n xs (pred n))) ∨
          ite j (pair (f (get n xs (n - S j))) (primrec 0 stepF j)) (f (get n xs (pred n))) =
          ite j (pair (g (get n xs (n - S j))) (primrec 0 stepG j)) (g (get n xs (pred n)))
        rw [hj, ite_zero, ite_zero]
        exact h (pred n) hp
      · change
          t ≤ ite j (pair (f (get n xs (n - S j))) (primrec 0 stepF j)) (f (get n xs (pred n))) ∨
          ite j (pair (f (get n xs (n - S j))) (primrec 0 stepF j)) (f (get n xs (pred n))) =
          ite j (pair (g (get n xs (n - S j))) (primrec 0 stepG j)) (g (get n xs (pred n)))
        rw [ite_of_ne_zero j _ _ hj, ite_of_ne_zero j _ _ hj]
        rcases h (n - S j) (sub_lt_of_pos n (S j) (pos_of_ne_zero n hn)
          (pos_of_ne_zero (S j) (succ_ne_zero j))) with hc | hc
        · left
          exact le_trans t _ _ hc (left_le_pair _ _)
        · rcases ih with hr | hr
          · left
            exact le_trans t _ _ hr (right_le_pair _ _)
          · right
            rw [hc, hr]
  exact build n

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
