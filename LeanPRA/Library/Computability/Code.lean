module

public import LeanPRA.Library.Nat.Pairing
public import LeanPRA.Library.Nat.DivMod

/-!
# Primitive-recursive expression codes

Every natural number encodes one expression built from four basic operations and three binary
operations. The basic codes are zero through three. Binary codes are
`4 + (3 * pair f g + k)`, where `k` is zero for pairing, one for composition, and two for recursion.

- `Primrec.Code.zero`, `Primrec.Code.succ`, `Primrec.Code.left`, and `Primrec.Code.right` encode the
  basic unary functions.
- `Primrec.Code.pair f g`, `Primrec.Code.comp f g`, and `Primrec.Code.rec f g` combine two
  expression codes.
- `Primrec.Code.const n` and `Primrec.Code.id` build constant and identity programs.
- `Primrec.Code.tag e` and `Primrec.Code.args e` recover the operation and the paired children.
- `Primrec.Code.cases` decomposes every number into a constructor; both children have smaller codes.

Pairing and quotient/remainder give each constructor unique arguments. Distinct expression trees
can compute the same function.
-/

@[expose] public section

pra

namespace Primrec.Code

/-- The program returning zero on every input. -/
def zero : Nat := 0

/-- The successor program. -/
def succ : Nat := 1

/-- The program returning the first component of a numerical pair. -/
def «left» : Nat := 2

/-- The program returning the second component of a numerical pair. -/
def «right» : Nat := 3

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
def id : Nat := pair «left» «right»

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

theorem left_rec : ∀ f g, unpairLeft (args (rec f g)) = f := by
  intro f g
  have children : args (rec f g) = _root_.pair f g := args_binary 2 f g rfl
  rw [children, unpairLeft_pair]

theorem right_rec : ∀ f g, unpairRight (args (rec f g)) = g := by
  intro f g
  have children : args (rec f g) = _root_.pair f g := args_binary 2 f g rfl
  rw [children, unpairRight_pair]

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
  exact (add_left_cancel 4 k l ht, pair_injective f g a b ha)

/-- Every numerical code has one of the seven expression constructors. -/
theorem cases : ∀ e,
    e = zero ∨ e = succ ∨ e = «left» ∨ e = «right» ∨
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

end Primrec.Code

end
