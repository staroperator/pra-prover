module

public import PRAProver.Library.Nat.Pairing

/-!
# Finite sequences encoded by numbers

Sequences are encoded in `Nat`, with zero marking the end:

- `[]` is encoded as `0`.
- `[a]` is encoded as `S (pair a 0)`.
- `[a, b]` is encoded as `S (pair a (S (pair b 0)))`.

Unpairing the predecessor of a positive code recovers its head and tail. Each tail is smaller,
so repeated tails reach zero and determine the length. Indices start at zero.

- `Sequence.nil`, `Sequence.cons`, `Sequence.head`, and `Sequence.tail` construct and destruct
  sequences.
- `Sequence.drop` iterates `tail`; `Sequence.length` finds the first `n` with `drop xs n = nil`.
- `Sequence.get xs i` reads entry `i` from the front (returning `0` when `length xs ≤ i`), and
  `Sequence.rget xs i` reads entry `length xs - S i` from the end (returning `head xs` when
  `length xs ≤ i`, and `0` on `nil`).
- `Sequence.revTabulate` and `Sequence.tabulate` build a length-`n` sequence from `f : Nat → Nat`.
- `Sequence.append`, `Sequence.map`, `Sequence.reverse`, `Sequence.take`, `Sequence.update`,
  `Sequence.fold`, and `Sequence.collect` provide standard sequence operations and bounded-witness
  collection.
- `Sequence.generate step n` builds the length-`n` sequence of earlier step values, newest first,
  so `Sequence.rget (Sequence.generate step n) i = step i (Sequence.generate step i)` for `i < n`.
- `covrec step n` evaluates `step n (Sequence.generate step n)` for course-of-values recursion.
-/

@[expose] public section

pra

namespace Sequence

/-- The empty sequence (`0`). -/
def nil : Nat := 0

/-- Prepend `x` to `xs`, encoded as `S (pair x xs)`. -/
def cons : Nat → Nat → Nat := fun x xs => S (pair x xs)

/-- The first entry of `xs`, or `0` when `xs = nil`. -/
def head : Nat → Nat := fun xs => ite xs (unpairLeft (pred xs)) 0

/-- The remaining sequence after removing the first entry of `xs` (with `tail nil = nil`). -/
def tail : Nat → Nat := fun xs => ite xs (unpairRight (pred xs)) 0

theorem head_nil : head nil = 0 := rfl

theorem tail_nil : tail nil = nil := rfl

theorem head_cons : ∀ x xs, head (cons x xs) = x := unpairLeft_pair

theorem tail_cons : ∀ x xs, tail (cons x xs) = xs := unpairRight_pair

theorem cons_ne_nil : ∀ x xs, ¬ cons x xs = nil := fun x xs => succ_ne_zero (pair x xs)

theorem cons_head_tail : ∀ xs, ¬ xs = nil → cons (head xs) (tail xs) = xs := by
  intro xs h
  have hs := succ_pred xs h
  rw [← hs]
  change S (pair (unpairLeft (pred xs)) (unpairRight (pred xs))) = S (pred xs)
  rw [pair_unpair]

theorem tail_le_pred : ∀ xs, tail xs ≤ pred xs := by
  intro xs
  rcases zero_or_succ_pred xs with hz | hs
  · rw [hz]; exact le_refl 0
  · rw [hs]; exact unpairRight_le (pred xs)

theorem tail_lt : ∀ xs, ¬ xs = nil → tail xs < xs := by
  intro xs h
  have hs := succ_pred xs h
  exact lt_of_le_of_lt (tail xs) (pred xs) xs (tail_le_pred xs)
    (eq_subst (fun z => pred xs < z) hs (lt_succ_self (pred xs)))

theorem tail_le : ∀ xs, tail xs ≤ xs := by
  intro xs
  by_cases h : xs = nil
  · rw [h]; exact le_refl 0
  · exact le_of_lt _ _ (tail_lt xs h)

/-- Remove the first `n` entries of `xs` by iterating `tail`. -/
def drop : Nat → Nat → Nat := fun xs n => iter tail n xs

/-- Read entry `i` from the front of `xs`, returning `0` when `length xs ≤ i`. -/
def get : Nat → Nat → Nat := fun xs i => head (drop xs i)

theorem drop_zero : ∀ xs, drop xs 0 = xs := fun xs => rfl

theorem drop_succ : ∀ xs n, drop xs (S n) = tail (drop xs n) := fun xs n => rfl

theorem drop_nil : ∀ n, drop nil n = nil := by
  intro n
  induction n with k ih
  · rfl
  · rw [drop_succ, ih, tail_nil]

theorem drop_cons : ∀ x xs n, drop (cons x xs) (S n) = drop xs n := by
  intro x xs n
  change tail (iter tail n (cons x xs)) = iter tail n xs
  rw [← iter_succ_apply tail, tail_cons]

theorem drop_add : ∀ xs m n, drop xs (m + n) = drop (drop xs m) n :=
  fun xs m n => iter_add tail m n xs

theorem get_zero : ∀ xs, get xs 0 = head xs := fun xs => rfl

theorem get_nil : ∀ n, get nil n = 0 := by
  intro n
  rw [get, drop_nil, head_nil]

theorem get_cons_zero : ∀ x xs, get (cons x xs) 0 = x := head_cons

theorem get_cons_succ : ∀ x xs n, get (cons x xs) (S n) = get xs n := by
  intro x xs n
  rw [get, get, drop_cons]

theorem get_drop : ∀ xs n i, get (drop xs n) i = get xs (n + i) := by
  intro xs n i
  rw [get, get, drop_add]

theorem drop_le_sub : ∀ xs n, drop xs n ≤ xs - n := by
  intro xs n
  induction n with k ih
  · exact le_refl xs
  · exact le_trans _ _ _ (tail_le_pred (drop xs k))
      (sub_le_sub_right (drop xs k) (xs - k) 1 ih)

theorem drop_self : ∀ xs, drop xs xs = nil := by
  intro xs
  have h := drop_le_sub xs xs
  rw [sub_self] at h
  exact h

/-- The length of `xs`: the least `n ≤ xs` with `drop xs n = nil`. -/
def length : Nat → Nat :=
  fun xs => findBelow (fun n => eqb (drop xs n) nil) (S xs)

theorem length_le_code : ∀ xs, length xs ≤ xs := by
  intro xs
  exact findBelow_le_of_witness (fun n => eqb (drop xs n) nil) xs (S xs)
    (and_right (eqb_ne_zero _ _) (drop_self xs))

theorem drop_length : ∀ xs, drop xs (length xs) = nil := by
  intro xs
  apply and_left (eqb_ne_zero _ _)
  exact findBelow_spec (fun n => eqb (drop xs n) nil) (S xs)
    (and_right (lt_succ (length xs) xs) (length_le_code xs))

theorem drop_ne_nil : ∀ xs n, n < length xs → ¬ drop xs n = nil := by
  intro xs n h
  exact and_left (eqb_eq_zero _ _)
    (findBelow_min (fun i => eqb (drop xs i) nil) n (S xs) h)

theorem length_le_of_drop : ∀ xs n, drop xs n = nil → length xs ≤ n := by
  intro xs n h
  exact findBelow_le_of_witness (fun i => eqb (drop xs i) nil) n (S xs)
    (and_right (eqb_ne_zero _ _) h)

theorem drop_eq_nil : ∀ xs n, drop xs n = nil ↔ length xs ≤ n := by
  intro xs n
  constructor
  · exact length_le_of_drop xs n
  · intro h
    rcases and_left (le_iff_exists_add (length xs) n) h with (d, hd)
    rw [← hd, drop_add, drop_length, drop_nil]

theorem length_eq : ∀ xs n, drop xs n = nil →
    (∀ i, i < n → ¬ drop xs i = nil) → length xs = n := by
  intro xs n hn earlier
  apply le_antisymm (length xs) n
  · exact length_le_of_drop xs n hn
  · apply le_of_not_lt n (length xs)
    intro h
    exact earlier (length xs) h (drop_length xs)

theorem length_nil : length nil = 0 := rfl

theorem length_cons : ∀ x xs, length (cons x xs) = S (length xs) := by
  intro x xs
  apply length_eq (cons x xs) (S (length xs))
  · rw [drop_cons, drop_length]
  · intro i hi
    rcases zero_or_succ_pred i with hz | hs
    · rw [hz, drop_zero]; exact cons_ne_nil x xs
    · rw [hs, drop_cons]
      apply drop_ne_nil xs (pred i)
      rw [hs] at hi
      exact and_left (succ_le_succ (S (pred i)) (length xs)) hi

theorem length_eq_zero : ∀ xs, length xs = 0 ↔ xs = nil := by
  intro xs
  constructor
  · intro h
    have hd := drop_length xs
    rw [h, drop_zero] at hd; exact hd
  · intro h; rw [h, length_nil]

theorem get_of_length_le : ∀ xs i, length xs ≤ i → get xs i = 0 := by
  intro xs i h
  change head (drop xs i) = 0
  rw [and_right (drop_eq_nil xs i) h, head_nil]

theorem length_drop : ∀ xs n, length (drop xs n) = length xs - n := by
  intro xs n
  apply le_antisymm _ _
  · apply length_le_of_drop (drop xs n) (length xs - n)
    rw [← drop_add]
    apply and_right (drop_eq_nil xs _)
    exact and_left (sub_le_iff (length xs) n (length xs - n)) (le_refl _)
  · apply and_right (sub_le_iff (length xs) n (length (drop xs n)))
    apply length_le_of_drop xs (n + length (drop xs n))
    rw [drop_add, drop_length]

/-- Read entry `i` from the end of `xs` as `get xs (length xs - S i)`. Indices `i` with
`length xs ≤ i` return `head xs`, and `rget nil i = 0`. -/
def rget : Nat → Nat → Nat := fun xs i => get xs (length xs - S i)

theorem rget_eq_get : ∀ xs i, rget xs i = get xs (length xs - S i) := fun xs i => rfl

theorem rget_nil : ∀ i, rget nil i = 0 := by
  intro i
  rw [rget_eq_get, get_nil]

theorem rget_of_length_le : ∀ xs i, length xs ≤ i → rget xs i = head xs := by
  intro xs i hi
  have hz : length xs - S i = 0 := le_succ_of_le (length xs) i hi
  rw [rget_eq_get, hz, get_zero]

theorem rget_cons : ∀ x xs i, i < length xs → rget (cons x xs) i = rget xs i := by
  intro x xs i hi
  rw [rget_eq_get, length_cons, succ_sub_of_le (length xs) (S i) hi,
    get_cons_succ, rget_eq_get]

theorem rget_cons_length : ∀ x xs, rget (cons x xs) (length xs) = x := by
  intro x xs
  rw [rget_eq_get, length_cons, sub_self, get_cons_zero]

/-- Two sequences with the same length and the same entries below that length are equal. -/
theorem ext : ∀ xs ys, length xs = length ys →
    (∀ i, i < length xs → get xs i = get ys i) → xs = ys := by
  intro xs ys hl entries
  apply induction_down (fun i => drop xs i = drop ys i) (length xs)
  · rw [drop_length, hl, drop_length]
  · intro i hi ih
    have hx := cons_head_tail (drop xs i) (drop_ne_nil xs i hi)
    have hi' : i < length ys := by
      rw [← hl]; exact hi
    have hy := cons_head_tail (drop ys i) (drop_ne_nil ys i hi')
    have hh : head (drop xs i) = head (drop ys i) := entries i hi
    have ht : tail (drop xs i) = tail (drop ys i) := ih
    rw [hh, ht] at hx
    exact eq_trans (eq_symm hx) hy

theorem ext_of_agree : ∀ xs ys, length xs = length ys →
    agreeBelow (get xs) (get ys) (length xs) → xs = ys := by
  intro xs ys hl h
  exact ext xs ys hl (and_left (agreeBelow_iff (get xs) (get ys) (length xs)) h)

/-- Build the length-`n` sequence `[f (n - 1), …, f 0]` by prepending `f 0` through `f (n - 1)`. -/
def revTabulate (f : Nat → Nat) : Nat → Nat :=
  fun n => primrec nil (fun k xs => cons (f k) xs) n

theorem revTabulate_zero (f : Nat → Nat) : revTabulate f 0 = nil := rfl

theorem revTabulate_succ (f : Nat → Nat) :
    ∀ n, revTabulate f (S n) = cons (f n) (revTabulate f n) := fun n => rfl

theorem length_revTabulate (f : Nat → Nat) : ∀ n, length (revTabulate f n) = n := by
  intro n
  induction n with k ih
  · rfl
  · rw [revTabulate_succ f, length_cons, ih]

theorem get_revTabulate_reverse (f : Nat → Nat) :
    ∀ i n, i < n → get (revTabulate f n) (n - S i) = f i := by
  intro i n
  induction n with k ih
  · intro h; exact false_elim (not_lt_zero i h)
  · intro hi
    rcases and_left (lt_succ_iff i k) hi with hk | he
    · rw [revTabulate_succ f, succ_sub_of_le k (S i) hk, get_cons_succ]
      exact ih hk
    · rw [he, sub_self, revTabulate_succ f, get_cons_zero]

theorem get_revTabulate (f : Nat → Nat) :
    ∀ n i, i < n → get (revTabulate f n) i = f (n - S i) := by
  intro n i hi
  have h := get_revTabulate_reverse f (n - S i) n (sub_succ_lt_self n i hi)
  rw [sub_succ_sub_succ_cancel n i hi] at h
  exact h

/-- Build the length-`n` sequence `[f 0, …, f (n - 1)]`, so `get (tabulate f n) i = f i` for
`i < n`. -/
def tabulate (f : Nat → Nat) : Nat → Nat :=
  fun n => revTabulate (fun i => f (n - S i)) n

theorem length_tabulate (f : Nat → Nat) : ∀ n, length (tabulate f n) = n :=
  fun n => length_revTabulate (fun i => f (n - S i)) n

theorem get_tabulate (f : Nat → Nat) : ∀ n i, i < n → get (tabulate f n) i = f i := by
  intro n i hi
  have h := get_revTabulate (fun j => f (n - S j)) n i hi
  rw [sub_succ_sub_succ_cancel n i hi] at h
  exact h

theorem tabulate_get : ∀ xs, tabulate (get xs) (length xs) = xs := by
  intro xs
  apply ext (tabulate (get xs) (length xs)) xs (length_tabulate (get xs) (length xs))
  intro i hi
  rw [length_tabulate (get xs)] at hi
  exact get_tabulate (get xs) (length xs) i hi

/-- Concatenate two sequences. -/
def append : Nat → Nat → Nat := fun xs ys =>
  tabulate (fun i => ite (ltb i (length xs)) (get xs i) (get ys (i - length xs)))
    (length xs + length ys)

theorem length_append : ∀ xs ys, length (append xs ys) = length xs + length ys :=
  fun xs ys => length_tabulate
    (fun i => ite (ltb i (length xs)) (get xs i) (get ys (i - length xs)))
    (length xs + length ys)

theorem get_append_left : ∀ xs ys i, i < length xs → get (append xs ys) i = get xs i := by
  intro xs ys i hi
  change get (tabulate
    (fun j => ite (ltb j (length xs)) (get xs j) (get ys (j - length xs)))
    (length xs + length ys)) i = get xs i
  rw [get_tabulate _ _ i
    (lt_of_lt_of_le i (length xs) _ hi (le_add_right (length xs) (length ys)))]
  exact ite_of_ne_zero _ _ _ (and_right (ltb_ne_zero _ _) hi)

theorem get_append_right : ∀ xs ys i, i < length ys →
    get (append xs ys) (length xs + i) = get ys i := by
  intro xs ys i hi
  change get (tabulate
    (fun j => ite (ltb j (length xs)) (get xs j) (get ys (j - length xs)))
    (length xs + length ys)) (length xs + i) = get ys i
  rw [get_tabulate _ _ _ (add_lt_add_left i (length ys) (length xs) hi)]
  have hz : ltb (length xs + i) (length xs) = 0 := by
    apply and_right (ltb_eq_zero _ _)
    intro h
    exact not_le_of_lt _ _ h (le_add_right (length xs) i)
  rw [hz, ite_zero, add_comm (length xs) i, add_sub_self_right]

theorem get_append_of_le : ∀ xs ys i, length xs ≤ i → i < length xs + length ys →
    get (append xs ys) i = get ys (i - length xs) := by
  intro xs ys i hlo hhi
  have he : length xs + (i - length xs) = i := by
    rw [add_comm]; exact sub_add_cancel_of_le i (length xs) hlo
  have hi : i - length xs < length ys :=
    and_right (sub_lt_iff i (length xs) (length ys) hlo) hhi
  have h := get_append_right xs ys (i - length xs) hi
  rw [he] at h; exact h

/-- Apply a numerical function to every entry. -/
def map (f : Nat → Nat) : Nat → Nat :=
  fun xs => tabulate (fun i => f (get xs i)) (length xs)

theorem length_map (f : Nat → Nat) : ∀ xs, length (map f xs) = length xs :=
  fun xs => length_tabulate (fun i => f (get xs i)) (length xs)

theorem get_map (f : Nat → Nat) :
    ∀ xs i, i < length xs → get (map f xs) i = f (get xs i) :=
  fun xs i hi => get_tabulate (fun j => f (get xs j)) (length xs) i hi

theorem map_nil (f : Nat → Nat) : map f nil = nil := rfl

theorem get_cons_map (f : Nat → Nat) : ∀ x xs i, i < S (length xs) →
    f (get (cons x xs) i) = get (cons (f x) (map f xs)) i := by
  intro x xs i
  induction i with j ih
  · intro _
    rw [get_cons_zero, get_cons_zero]
  · intro h
    rw [get_cons_succ, get_cons_succ,
      get_map f xs j (and_left (succ_le_succ (S j) (length xs)) h)]

theorem map_cons (f : Nat → Nat) : ∀ x xs, map f (cons x xs) = cons (f x) (map f xs) := by
  intro x xs
  apply ext (map f (cons x xs)) (cons (f x) (map f xs))
  · rw [length_map f, length_cons, length_cons, length_map f]
  · intro i hi
    rw [length_map f, length_cons] at hi
    have bound : i < length (cons x xs) := by
      rw [length_cons]
      exact hi
    rw [get_map f (cons x xs) i bound]
    exact get_cons_map f x xs i hi

/-- Reverse the order of the entries. -/
def reverse : Nat → Nat :=
  fun xs => tabulate (fun i => get xs (length xs - S i)) (length xs)

theorem length_reverse : ∀ xs, length (reverse xs) = length xs :=
  fun xs => length_tabulate (fun i => get xs (length xs - S i)) (length xs)

theorem get_reverse : ∀ xs i, i < length xs →
    get (reverse xs) i = get xs (length xs - S i) :=
  fun xs i hi => get_tabulate (fun j => get xs (length xs - S j)) (length xs) i hi

theorem reverse_reverse : ∀ xs, reverse (reverse xs) = xs := by
  intro xs
  apply ext (reverse (reverse xs)) xs
  · rw [length_reverse, length_reverse]
  · intro i hi
    rw [length_reverse, length_reverse] at hi
    rw [get_reverse (reverse xs) i
      (eq_subst (fun n => i < n) (eq_symm (length_reverse xs)) hi), length_reverse,
      get_reverse xs (length xs - S i) (sub_succ_lt_self (length xs) i hi),
      sub_succ_sub_succ_cancel (length xs) i hi]

/-- Keep the first `n` entries of `xs`, or all of `xs` when `length xs ≤ n`. -/
def take : Nat → Nat → Nat := fun xs n =>
  tabulate (get xs) (ite (leb n (length xs)) n (length xs))

theorem take_of_le : ∀ xs n, n ≤ length xs → take xs n = tabulate (get xs) n := by
  intro xs n h
  change tabulate (get xs) (ite (leb n (length xs)) n (length xs)) = tabulate (get xs) n
  rw [and_right (leb_eq_one n (length xs)) h, ite_succ]

theorem take_of_length_le : ∀ xs n, length xs ≤ n → take xs n = xs := by
  intro xs n h
  by_cases hn : n ≤ length xs
  · have he := le_antisymm n (length xs) hn h
    rw [he, take_of_le xs (length xs) (le_refl _), tabulate_get]
  · change tabulate (get xs) (ite (leb n (length xs)) n (length xs)) = xs
    rw [and_right (leb_eq_zero _ _) hn, ite_zero, tabulate_get]

theorem length_take : ∀ xs n, n ≤ length xs → length (take xs n) = n := by
  intro xs n h
  rw [take_of_le xs n h, length_tabulate (get xs)]

theorem get_take : ∀ xs n i, i < n → i < length xs → get (take xs n) i = get xs i := by
  intro xs n i hin hi
  by_cases hn : n ≤ length xs
  · rw [take_of_le xs n hn, get_tabulate (get xs) n i hin]
  · rw [take_of_length_le xs n (le_of_lt _ _ (lt_of_not_le _ _ hn))]

/-- Replace entry `i` of `xs` with `x`, leaving `xs` unchanged when `length xs ≤ i`. -/
def update : Nat → Nat → Nat → Nat := fun xs i x =>
  tabulate (fun j => ite (eqb j i) x (get xs j)) (length xs)

theorem length_update : ∀ xs i x, length (update xs i x) = length xs :=
  fun xs i x => length_tabulate (fun j => ite (eqb j i) x (get xs j)) (length xs)

theorem get_update_same : ∀ xs i x, i < length xs → get (update xs i x) i = x := by
  intro xs i x hi
  change get (tabulate (fun j => ite (eqb j i) x (get xs j)) (length xs)) i = x
  rw [get_tabulate _ _ i hi, and_right (eqb_eq_one i i) rfl, ite_succ]

theorem get_update_other : ∀ xs i j x, ¬ j = i → get (update xs i x) j = get xs j := by
  intro xs i j x hji
  by_cases hj : j < length xs
  · change get (tabulate (fun k => ite (eqb k i) x (get xs k)) (length xs)) j = get xs j
    rw [get_tabulate _ _ j hj, and_right (eqb_eq_zero j i) hji, ite_zero]
  · have hlo := le_of_not_lt (length xs) j hj
    have hu : length (update xs i x) ≤ j := by
      rw [length_update]; exact hlo
    rw [get_of_length_le (update xs i x) j hu, get_of_length_le xs j hlo]

theorem update_of_length_le : ∀ xs i x, length xs ≤ i → update xs i x = xs := by
  intro xs i x hi
  apply ext (update xs i x) xs (length_update xs i x)
  intro j hj
  rw [length_update] at hj
  apply get_update_other xs i j x
  intro he
  rw [he] at hj
  exact not_le_of_lt i (length xs) hj hi

/-- Fold every entry of `xs` from left to right, starting from `initial`.
The function receives the accumulated value first and the current entry second. -/
def fold (f : Nat → Nat → Nat) : Nat → Nat → Nat :=
  fun xs initial => primrec initial (fun i r => f r (get xs i)) (length xs)

theorem fold_nil (f : Nat → Nat → Nat) : ∀ a, fold f nil a = a := fun a => rfl

theorem fold_cons (f : Nat → Nat → Nat) : ∀ x xs a,
    fold f (cons x xs) a = fold f xs (f a x) := by
  intro x xs a
  have initialSegments : ∀ n,
      primrec a (fun i r => f r (get (cons x xs) i)) (S n) =
        primrec (f a x) (fun i r => f r (get xs i)) n := by
    intro n
    induction n with k ih
    · change f a (get (cons x xs) 0) = f a x
      rw [get_cons_zero]
    · change f (primrec a (fun i r => f r (get (cons x xs) i)) (S k))
          (get (cons x xs) (S k)) =
        f (primrec (f a x) (fun i r => f r (get xs i)) k) (get xs k)
      rw [ih, get_cons_succ]
  rw [fold, length_cons, fold]
  exact initialSegments (length xs)

theorem fold_map (f : Nat → Nat → Nat) (g : Nat → Nat) : ∀ xs a,
    fold f (map g xs) a = fold (fun r x => f r (g x)) xs a := by
  intro xs a
  have initialSegments : ∀ n, n ≤ length xs →
      primrec a (fun i r => f r (get (map g xs) i)) n =
        primrec a (fun i r => f r (g (get xs i))) n := by
    intro n
    induction n with k ih
    · intro _
      rfl
    · intro hk
      change f (primrec a (fun i r => f r (get (map g xs) i)) k)
          (get (map g xs) k) =
        f (primrec a (fun i r => f r (g (get xs i))) k) (g (get xs k))
      rw [get_map g xs k hk, ih (le_of_lt k (length xs) hk)]
  rw [fold, length_map g, fold]
  exact initialSegments (length xs) (le_refl (length xs))

/-- A quantifier-free property preserved at each entry holds after folding the whole sequence. -/
theorem fold_invariant (P : Nat → QFProp) (f : Nat → Nat → Nat) : ∀ xs a,
    P a → (∀ i r, i < length xs → P r → P (f r (get xs i))) → P (fold f xs a) := by
  intro xs a initial step
  have initialSegments : ∀ n, n ≤ length xs → P (primrec a (fun i r => f r (get xs i)) n) := by
    intro n
    induction n with k ih
    · intro _
      exact initial
    · intro hk
      exact step k (primrec a (fun i r => f r (get xs i)) k) hk
        (ih (le_of_lt k (length xs) hk))
  exact initialSegments (length xs) (le_refl (length xs))

theorem tabulate_congr (f g : Nat → Nat) : ∀ n,
    agreeBelow f g n → tabulate f n = tabulate g n := by
  intro n h
  apply ext (tabulate f n) (tabulate g n)
  · rw [length_tabulate f, length_tabulate g]
  · intro i hi
    rw [length_tabulate f] at hi
    rw [get_tabulate f n i hi, get_tabulate g n i hi]
    exact and_left (agreeBelow_iff f g n) h i hi

theorem append_nil : ∀ xs, append xs nil = xs := by
  intro xs
  apply ext (append xs nil) xs
  · rw [length_append, length_nil, add_zero]
  · intro i hi
    rw [length_append, length_nil, add_zero] at hi
    exact get_append_left xs nil i hi

theorem nil_append : ∀ xs, append nil xs = xs := by
  intro xs
  apply ext (append nil xs) xs
  · rw [length_append, length_nil, zero_add]
  · intro i hi
    rw [length_append, length_nil, zero_add] at hi
    have h := get_append_right nil xs i hi
    rw [length_nil, zero_add] at h; exact h

theorem take_tabulate (f : Nat → Nat) : ∀ n m, m ≤ n →
    take (tabulate f n) m = tabulate f m := by
  intro n m hmn
  have hm : m ≤ length (tabulate f n) := by
    rw [length_tabulate f]; exact hmn
  rw [take_of_le (tabulate f n) m hm]
  apply tabulate_congr (get (tabulate f n)) f m
  apply and_right (agreeBelow_iff (get (tabulate f n)) f m)
  intro i hi
  exact get_tabulate f n i (lt_of_lt_of_le i m n hi hmn)

theorem take_take : ∀ xs m n, m ≤ n → n ≤ length xs → take (take xs n) m = take xs m := by
  intro xs m n hmn hn
  have hm := le_trans m n (length xs) hmn hn
  rw [take_of_le xs n hn]
  exact eq_trans (take_tabulate (get xs) n m hmn) (eq_symm (take_of_le xs m hm))

theorem take_append : ∀ xs ys, take (append xs ys) (length xs) = xs := by
  intro xs ys
  have hl : length xs ≤ length (append xs ys) := by
    rw [length_append]; exact le_add_right (length xs) (length ys)
  apply ext (take (append xs ys) (length xs)) xs
  · exact length_take (append xs ys) (length xs) hl
  · intro i hi
    rw [length_take (append xs ys) (length xs) hl] at hi
    rw [get_take (append xs ys) (length xs) i hi
      (lt_of_lt_of_le i (length xs) _ hi hl), get_append_left xs ys i hi]

theorem fold_congr (f : Nat → Nat → Nat) : ∀ xs ys a,
    length xs = length ys → agreeBelow (get xs) (get ys) (length xs) →
      fold f xs a = fold f ys a := by
  intro xs ys a hlen hget
  have same := ext xs ys hlen (and_left (agreeBelow_iff (get xs) (get ys) (length xs)) hget)
  rw [same]

/-- Tabulate `findBelow (relation i) (bound i)` for `i = 0` through `n - 1`. -/
def collect (relation : Nat → Nat → Nat) (bound : Nat → Nat) : Nat → Nat :=
  fun n => tabulate (fun i => findBelow (relation i) (bound i)) n

theorem length_collect (relation : Nat → Nat → Nat) (bound : Nat → Nat) :
    ∀ n, length (collect relation bound n) = n :=
  fun n => length_tabulate (fun i => findBelow (relation i) (bound i)) n

theorem get_collect (relation : Nat → Nat → Nat) (bound : Nat → Nat) : ∀ n i,
    i < n → anyBelow (relation i) (bound i) = 1 →
    get (collect relation bound n) i < bound i ∧
      ¬ relation i (get (collect relation bound n) i) = 0 := by
  intro n i hi h
  have he : get (collect relation bound n) i = findBelow (relation i) (bound i) :=
    get_tabulate (fun j => findBelow (relation j) (bound j)) n i hi
  rw [he]
  have hs := and_right (findBelow_lt_iff (relation i) (bound i))
    (and_left (anyBelow_eq_one (relation i) (bound i)) h)
  exact (hs, findBelow_spec (relation i) (bound i) hs)

/-- Build a sequence of `n` entries, newest first, where step `k` receives `k` and the sequence of
the `k` earlier entries. -/
def generate (step : Nat → Nat → Nat) : Nat → Nat :=
  fun n => primrec nil (fun k xs => cons (step k xs) xs) n

theorem generate_zero (step : Nat → Nat → Nat) : generate step 0 = nil := rfl

theorem generate_succ (step : Nat → Nat → Nat) : ∀ n,
    generate step (S n) = cons (step n (generate step n)) (generate step n) := fun n => rfl

theorem length_generate (step : Nat → Nat → Nat) : ∀ n, length (generate step n) = n := by
  intro n
  induction n with k ih
  · rfl
  · rw [generate_succ step, length_cons, ih]

/-- For `i < n`, `rget (generate step n) i` recovers the value `step i (generate step i)` computed
at stage `i`. -/
theorem rget_generate (step : Nat → Nat → Nat) :
    ∀ i n, i < n → rget (generate step n) i = step i (generate step i) := by
  intro i n
  induction n with k ih
  · intro h; exact false_elim (not_lt_zero i h)
  · intro hi
    rw [generate_succ step]
    rcases and_left (lt_succ_iff i k) hi with hk | he
    · have hi' : i < length (generate step k) := by
        rw [length_generate step]; exact hk
      rw [rget_cons _ _ i hi']; exact ih hk
    · have hlast := rget_cons_length (step k (generate step k)) (generate step k)
      rw [length_generate step] at hlast
      rw [he]; exact hlast

theorem drop_generate (step : Nat → Nat → Nat) :
    ∀ k n, k ≤ n → drop (generate step n) (n - k) = generate step k := by
  intro k n
  induction n with j ih
  · intro hk
    have he : k = 0 := hk
    rw [he]; rfl
  · intro hk
    rcases lt_or_eq_of_le k (S j) hk with hlt | he
    · have hkj : k ≤ j := and_left (lt_succ k j) hlt
      rw [succ_sub_of_le j k hkj, generate_succ step, drop_cons]
      exact ih hkj
    · rw [he, sub_self, drop_zero]

end Sequence

/-- Course-of-values recursion: evaluate `step n` on the sequence `Sequence.generate step n` of all
earlier results, stored newest first. Inside `step n xs`, `Sequence.rget xs i` reads the result at
an earlier index `i < n`. -/
def covrec (step : Nat → Nat → Nat) : Nat → Nat :=
  fun n => step n (Sequence.generate step n)

/-- Prove `¬ check n (covrec step n) = 0` for all `n` by showing that `step n xs` satisfies
`check n` whenever `xs` has length `n` and every earlier entry `Sequence.rget xs i` (`i < n`)
satisfies `check i`. -/
theorem covrec_correct (check : Nat → Nat → Nat) (step : Nat → Nat → Nat) :
    (∀ n xs, Sequence.length xs = n →
      allBelow (fun i => check i (Sequence.rget xs i)) n = 1 → ¬ check n (step n xs) = 0) →
    ∀ n, ¬ check n (covrec step n) = 0 := by
  intro advance n
  apply strong_induction (fun i => check i (covrec step i))
  intro k earlier
  apply advance k (Sequence.generate step k) (Sequence.length_generate step k)
  have he := allBelow_congr (fun i => check i (Sequence.rget (Sequence.generate step k) i))
    (fun i => check i (covrec step i)) k
    (fun i hi => eq_congr (fun v => check i v) (Sequence.rget_generate step i k hi))
  rw [he]; exact earlier

/-- Prove `P n (covrec step n)` for a relation `P : Nat → Nat → Prop` represented by a numerical
test `check` with `∀ i v, ¬ check i v = 0 ↔ P i v`. -/
theorem covrec_induction (P : Nat → Nat → Prop) (check : Nat → Nat → Nat)
    (step : Nat → Nat → Nat) :
    (∀ i v, ¬ check i v = 0 ↔ P i v) →
    (∀ n xs, Sequence.length xs = n →
      (∀ i, i < n → P i (Sequence.rget xs i)) → P n (step n xs)) →
    ∀ n, P n (covrec step n) := by
  intro spec advance n
  apply and_left (spec n (covrec step n))
  apply covrec_correct check step
  intro k xs hl earlier
  apply and_right (spec k (step k xs))
  apply advance k xs hl
  intro i hi
  exact and_left (spec i (Sequence.rget xs i))
    (allBelow_elim (fun j => check j (Sequence.rget xs j)) i k earlier hi)

end
