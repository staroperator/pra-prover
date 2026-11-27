module

public import PRAProver.Library.Nat.DivMod
public import PRAProver.Library.Nat.Sequence

/-!
# Primitive-recursive function codes

Primitive recursive functions are encoded as natural numbers. For convenience, we encode unary
functions and `n`-ary functions are represented as unary functions over all arguments paired, the
same as [Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Primrec/Basic.html#Nat.Primrec)
([paper](https://arxiv.org/pdf/1810.08380)).

For the encoding, `0` to `3` encodes the four basic operations: zero, successor, left and right, and
`4 + (3 * pair f g + k)` encodes the remained three binary operations: `k = 0` for pairing, `k = 1`
for composition and `k = 2` for primitive recursion. This gives a one-to-one correspondence.
-/

@[expose] public section

pra

namespace Primrec.Code

/-! ## Constructors and decoding

- `zero`, `succ`, `left`, and `right` encode the basic unary operations.
- `pair`, `comp`, and `rec` combine two child codes.
- `binary` is the shared encoding of the three two-argument constructors.
- `tag` and `args` recover the operation number and paired child codes. `tag_pair`,
  `args_pair`, `left_lt_pair`, and `pair_injective`, with their `comp` and `rec` versions,
  state the properties of each constructor.
-/

/-- The program returning zero on every input. -/
def zero : Nat := 0

/-- The successor program. -/
def succ : Nat := 1

/-- The program returning the first component of a numerical pair. -/
def left : Nat := 2

/-- The program returning the second component of a numerical pair. -/
def right : Nat := 3

/-- `binary k f g` encodes operation `k < 3` with child programs `f` and `g`. -/
def binary : Nat → Nat → Nat → Nat := fun k f g => 4 + (3 * _root_.pair f g + k)

/-- `pair f g` evaluates `f` and `g` at the input and pairs their outputs. -/
def pair : Nat → Nat → Nat := binary 0

/-- `comp f g` evaluates `g` at the input, then evaluates `f` at its output. -/
def comp : Nat → Nat → Nat := binary 1

/-- `rec f g` iterates `g (pair x (pair i previous))` from `f x` for `n` steps on input
`pair x n`. -/
def rec : Nat → Nat → Nat := binary 2

/-- `const n` encodes the constant function with value `n`. -/
def const : Nat → Nat := fun n => primrec zero (fun _ e => comp succ e) n

/-- The identity program, obtained by pairing the two projections. -/
def id : Nat := pair left right

/-- `tag e` returns the operation number: zero through three for basic programs, four through six
for binary ones. -/
def tag : Nat → Nat := fun e => ite (ltb e 4) e (4 + (e - 4) % 3)

/-- `args e` returns the paired child codes of a binary program, and zero for a basic program. -/
def args : Nat → Nat := fun e => (e - 4) / 3

theorem tag_binary : ∀ k f g, k < 3 → tag (binary k f g) = 4 + k := by
  intro k f g hk
  have h : ltb (binary k f g) 4 = 0 :=
    and_right (ltb_eq_zero _ _) (fun h => not_le_of_lt _ _ h (le_add_right 4 _))
  rw [tag, h, binary, add_sub_self_left, mod_mul_add_of_lt 3 _ k (succ_ne_zero 2) hk]
  rfl

theorem args_binary : ∀ k f g, k < 3 → args (binary k f g) = _root_.pair f g := by
  intro k f g hk
  rw [args, binary, add_sub_self_left, div_mul_add_of_lt 3 _ k (succ_ne_zero 2) hk]

theorem left_lt_binary : ∀ k f g, f < binary k f g := by
  intro k f g
  have h := le_trans f (3 * _root_.pair f g) (3 * _root_.pair f g + k)
    (le_trans f (_root_.pair f g) _ (left_le_pair f g)
      (le_mul_of_pos (_root_.pair f g) 3 (succ_ne_zero 2))) (le_add_right _ k)
  have step := add_lt_add_right 0 4 (3 * _root_.pair f g + k) rfl
  rw [zero_add] at step
  exact lt_of_le_of_lt _ _ _ h step

theorem right_lt_binary : ∀ k f g, g < binary k f g := by
  intro k f g
  have h := le_trans g (3 * _root_.pair f g) (3 * _root_.pair f g + k)
    (le_trans g (_root_.pair f g) _ (right_le_pair f g)
      (le_mul_of_pos (_root_.pair f g) 3 (succ_ne_zero 2))) (le_add_right _ k)
  have step := add_lt_add_right 0 4 (3 * _root_.pair f g + k) rfl
  rw [zero_add] at step
  exact lt_of_le_of_lt _ _ _ h step

theorem binary_injective : ∀ k l f g a b, k < 3 → l < 3 →
    binary k f g = binary l a b → k = l ∧ f = a ∧ g = b := by
  intro k l f g a b hk hl he
  have ht := eq_congr tag he
  rw [tag_binary k f g hk, tag_binary l a b hl] at ht
  have ha := eq_congr args he
  rw [args_binary k f g hk, args_binary l a b hl] at ha
  exact (add_left_cancel 4 k l ht, _root_.pair_injective f g a b ha)

theorem tag_pair : ∀ f g, tag (pair f g) = 4 := fun f g => tag_binary 0 f g rfl

theorem tag_comp : ∀ f g, tag (comp f g) = 5 := fun f g => tag_binary 1 f g rfl

theorem tag_rec : ∀ f g, tag (rec f g) = 6 := fun f g => tag_binary 2 f g rfl

theorem args_pair : ∀ f g, args (pair f g) = _root_.pair f g := fun f g => args_binary 0 f g rfl

theorem args_comp : ∀ f g, args (comp f g) = _root_.pair f g := fun f g => args_binary 1 f g rfl

theorem args_rec : ∀ f g, args (rec f g) = _root_.pair f g := fun f g => args_binary 2 f g rfl

theorem left_pair : ∀ f g, unpairLeft (args (pair f g)) = f := by
  intro f g
  rw [args_pair f g, unpairLeft_pair]

theorem right_pair : ∀ f g, unpairRight (args (pair f g)) = g := by
  intro f g
  rw [args_pair f g, unpairRight_pair]

theorem left_comp : ∀ f g, unpairLeft (args (comp f g)) = f := by
  intro f g
  rw [args_comp f g, unpairLeft_pair]

theorem right_comp : ∀ f g, unpairRight (args (comp f g)) = g := by
  intro f g
  rw [args_comp f g, unpairRight_pair]

theorem left_rec : ∀ f g, unpairLeft (args (rec f g)) = f := by
  intro f g
  rw [args_rec f g, unpairLeft_pair]

theorem right_rec : ∀ f g, unpairRight (args (rec f g)) = g := by
  intro f g
  rw [args_rec f g, unpairRight_pair]

theorem left_lt_pair : ∀ f g, f < pair f g := left_lt_binary 0

theorem right_lt_pair : ∀ f g, g < pair f g := right_lt_binary 0

theorem left_lt_comp : ∀ f g, f < comp f g := left_lt_binary 1

theorem right_lt_comp : ∀ f g, g < comp f g := right_lt_binary 1

theorem left_lt_rec : ∀ f g, f < rec f g := left_lt_binary 2

theorem right_lt_rec : ∀ f g, g < rec f g := right_lt_binary 2

theorem pair_injective : ∀ f g a b, pair f g = pair a b → f = a ∧ g = b :=
  fun f g a b h => and_right (binary_injective 0 0 f g a b rfl rfl h)

theorem comp_injective : ∀ f g a b, comp f g = comp a b → f = a ∧ g = b :=
  fun f g a b h => and_right (binary_injective 1 1 f g a b rfl rfl h)

theorem rec_injective : ∀ f g a b, rec f g = rec a b → f = a ∧ g = b :=
  fun f g a b h => and_right (binary_injective 2 2 f g a b rfl rfl h)

/-! ## Constructor cases and induction

- `cases` expresses every code as one of the seven constructors.
- `induction_of_bool` proves decidable properties by constructor induction. Each binary case
  gets the induction hypotheses for both children.
-/

/-- Every numerical code has one of the seven expression constructors. -/
theorem cases : ∀ e,
    e = zero ∨ e = succ ∨ e = left ∨ e = right ∨
      ∃ f g, e = pair f g ∨ e = comp f g ∨ e = rec f g := by
  intro e
  by_cases h : e < 4
  · rcases and_left (lt_succ_iff e 3) h with h | h
    · rcases and_left (lt_succ_iff e 2) h with h | h
      · rcases and_left (lt_succ_iff e 1) h with h | h
        · left
          exact and_left (lt_succ e 0) h
        · right; left; exact h
      · right; right; left; exact h
    · right; right; right; left; exact h
  · have bound := le_of_not_lt 4 e h
    let a := args e
    let k := (e - 4) % 3
    let f := _root_.unpairLeft a
    let g := _root_.unpairRight a
    have he : binary k f g = e := by
      rw [binary, pair_unpair, args, div_mod, add_comm]
      exact sub_add_cancel_of_le e 4 bound
    have hk : k < 3 := mod_lt (e - 4) 3 (succ_ne_zero 2)
    right; right; right; right
    exists f
    exists g
    rcases and_left (lt_succ_iff k 2) hk with hk | hk
    · rcases and_left (lt_succ_iff k 1) hk with hk | hk
      · have hz : k = 0 := and_left (lt_succ k 0) hk
        rw [hz] at he
        left; exact eq_symm he
      · rw [hk] at he
        right; left; exact eq_symm he
    · rw [hk] at he
      right; right; exact eq_symm he

/-- Induction over the seven program constructors. The numerical test decides the induction
predicate in the typed PRA language. Each binary case receives the hypotheses for its children. -/
theorem induction_of_bool (P : Nat → Prop) (test : Nat → Nat) :
    (∀ e, ¬ test e = 0 ↔ P e) →
    P zero → P succ → P left → P right →
    (∀ f g, P f → P g → P (pair f g)) →
    (∀ f g, P f → P g → P (comp f g)) →
    (∀ f g, P f → P g → P (rec f g)) → ∀ e, P e := by
  intro decides hz hs hl hr hp hc hrec
  apply strong_induction_of_bool P test decides
  intro e earlier
  rcases cases e with h | h | h | h | rest
  · rw [h]
    exact hz
  · rw [h]
    exact hs
  · rw [h]
    exact hl
  · rw [h]
    exact hr
  · rcases rest with (f, g, branch)
    rcases branch with h | h | h
    · rw [h] at earlier
      rw [h]
      exact hp f g (earlier f (left_lt_pair f g)) (earlier g (right_lt_pair f g))
    · rw [h] at earlier
      rw [h]
      exact hc f g (earlier f (left_lt_comp f g)) (earlier g (right_lt_comp f g))
    · rw [h] at earlier
      rw [h]
      exact hrec f g (earlier f (left_lt_rec f g)) (earlier g (right_lt_rec f g))

/-! ## Recursion over program codes

- `fold` combines the child codes and their results at each binary constructor.
- `fold_induction` proves a decidable property of the result for every code.
-/

/-- Fold a program code using the results `z`, `s`, `l`, and `r` at the four basic
constructors. Each binary branch receives its left code, right code, left result, and right
result in that order. -/
def fold (z s l r : Nat)
    (onPair onComp onRec : Nat → Nat → Nat → Nat → Nat) : Nat → Nat :=
  covrec (fun e history =>
    let k := tag e;
    let children := args e;
    let f := unpairLeft children;
    let g := unpairRight children;
    let a := Sequence.rget history f;
    let b := Sequence.rget history g;
    ite (eqb k 0) z (ite (eqb k 1) s (ite (eqb k 2) l (ite (eqb k 3) r
      (ite (eqb k 4) (onPair f g a b) (ite (eqb k 5) (onComp f g a b) (onRec f g a b)))))))

theorem fold_zero (z s l r : Nat) (onPair onComp onRec : Nat → Nat → Nat → Nat → Nat) :
    fold z s l r onPair onComp onRec zero = z := rfl

theorem fold_succ (z s l r : Nat) (onPair onComp onRec : Nat → Nat → Nat → Nat → Nat) :
    fold z s l r onPair onComp onRec succ = s := rfl

theorem fold_left (z s l r : Nat) (onPair onComp onRec : Nat → Nat → Nat → Nat → Nat) :
    fold z s l r onPair onComp onRec left = l := rfl

theorem fold_right (z s l r : Nat) (onPair onComp onRec : Nat → Nat → Nat → Nat → Nat) :
    fold z s l r onPair onComp onRec right = r := rfl

theorem fold_pair (z s l r : Nat) (onPair onComp onRec : Nat → Nat → Nat → Nat → Nat) :
    ∀ f g, fold z s l r onPair onComp onRec (pair f g) =
      onPair f g (fold z s l r onPair onComp onRec f) (fold z s l r onPair onComp onRec g) := by
  intro f g
  rw [fold, covrec, tag_pair f g, args_pair f g, unpairLeft_pair, unpairRight_pair]
  rw [Sequence.rget_generate _ f (pair f g) (left_lt_pair f g),
    Sequence.rget_generate _ g (pair f g) (right_lt_pair f g)]
  rfl

theorem fold_comp (z s l r : Nat) (onPair onComp onRec : Nat → Nat → Nat → Nat → Nat) :
    ∀ f g, fold z s l r onPair onComp onRec (comp f g) =
      onComp f g (fold z s l r onPair onComp onRec f) (fold z s l r onPair onComp onRec g) := by
  intro f g
  rw [fold, covrec, tag_comp f g, args_comp f g, unpairLeft_pair, unpairRight_pair]
  rw [Sequence.rget_generate _ f (comp f g) (left_lt_comp f g),
    Sequence.rget_generate _ g (comp f g) (right_lt_comp f g)]
  rfl

theorem fold_rec (z s l r : Nat) (onPair onComp onRec : Nat → Nat → Nat → Nat → Nat) :
    ∀ f g, fold z s l r onPair onComp onRec (rec f g) =
      onRec f g (fold z s l r onPair onComp onRec f) (fold z s l r onPair onComp onRec g) := by
  intro f g
  rw [fold, covrec, tag_rec f g, args_rec f g, unpairLeft_pair, unpairRight_pair]
  rw [Sequence.rget_generate _ f (rec f g) (left_lt_rec f g),
    Sequence.rget_generate _ g (rec f g) (right_lt_rec f g)]
  rfl

/-- A property decided by `check e a` holds for each result of the fold if the four basic
results satisfy it and the three binary branches preserve it. -/
theorem fold_induction (P : Nat → Nat → Prop) (check : Nat → Nat → Nat)
    (z s l r : Nat) (onPair onComp onRec : Nat → Nat → Nat → Nat → Nat) :
    (∀ e a, ¬ check e a = 0 ↔ P e a) →
    P zero z → P succ s → P left l → P right r →
    (∀ f g a b, P f a → P g b → P (pair f g) (onPair f g a b)) →
    (∀ f g a b, P f a → P g b → P (comp f g) (onComp f g a b)) →
    (∀ f g a b, P f a → P g b → P (rec f g) (onRec f g a b)) →
    ∀ e, P e (fold z s l r onPair onComp onRec e) := by
  intro decides hz hs hl hr hp hc hrec
  let run := fold z s l r onPair onComp onRec
  apply induction_of_bool (fun e => P e (run e)) (fun e => check e (run e))
  · exact fun e => decides e (run e)
  · exact hz
  · exact hs
  · exact hl
  · exact hr
  · intro f g hf hg
    change P (pair f g) (fold z s l r onPair onComp onRec (pair f g))
    rw [fold_pair z s l r onPair onComp onRec f g]
    exact hp f g (run f) (run g) hf hg
  · intro f g hf hg
    change P (comp f g) (fold z s l r onPair onComp onRec (comp f g))
    rw [fold_comp z s l r onPair onComp onRec f g]
    exact hc f g (run f) (run g) hf hg
  · intro f g hf hg
    change P (rec f g) (fold z s l r onPair onComp onRec (rec f g))
    rw [fold_rec z s l r onPair onComp onRec f g]
    exact hrec f g (run f) (run g) hf hg

end Primrec.Code

end
