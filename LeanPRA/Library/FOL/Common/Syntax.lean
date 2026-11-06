module

public import LeanPRA.Library.FOL.Common.Language
public import LeanPRA.Library.Nat.DivMod
public import LeanPRA.Library.Nat.Tuple

/-!
# Numerical first-order syntax

Terms and formulas are encoded in `Nat`. For a fixed language `L`, every number has an
interpretation as each kind of syntax. Symbol indices start at zero within each symbol group.

For terms, let `c = Language.constants L` and `k = S (Language.functionCount L)`,
one more than the number of positive-arity function symbols:

- `Term.const L j` is encoded as `j`, for `j < c`.
- `Term.var L i` is encoded as `c + k * i`.
- `Term.app L j args` is encoded as `c + (k * args + S j)`.

For formulas, let `m = S (Language.relationCount L)`:

- `Formula.falsum` is encoded as `0`.
- `Formula.equal L t u` is encoded as `S (3 * (m * pair t u))`.
- `Formula.rel L j args` is encoded as `S (3 * (m * args + S j))`.
- `Formula.imp A B` is encoded as `S (3 * pair A B + 1)`.
- `Formula.all A` is encoded as `S (3 * A + 2)`.

Here `t`, `u` are term codes, and `A`, `B` are formula codes. In function and relation
applications, `j` is below the corresponding symbol count and `args` encodes a tuple of term
codes of that symbol's arity: one argument `t` is encoded as `t`, and two as `pair t u`.
`Term.head` and `Term.arg` recover a nonconstant term's constructor and arguments.

For positive formulas, the predecessor's remainder modulo `3` distinguishes equality or relation
application from implication and universal quantification. In the first case, division by `3`
and then remainder modulo `m` distinguishes equality (`0`) from relation symbol `j` (`S j`).
`Formula.head`, `Formula.arg`, and `Formula.relationIndex` recover the constructor and its
arguments.

Variables use de Bruijn indices: `0` refers to the nearest binder, with larger indices counting
outward. Beneath `d` binders, an index `i ≥ d` refers to surrounding position `i - d`.
Formulas have no fixed scope. The main operations are:

- `Term.rec` processes variables, constants, and function applications by numerical recursion,
  passing an exact-arity tuple of child results to the application handler.
- `Formula.recWithDepth` processes the five formula cases while tracking binder depth.
  Its paired recursion rank decreases when entering a quantified body, even though depth increases.
- `Formula.rec` processes the same cases with handlers that ignore binder depth.
- `Term.subst` and `Formula.subst` replace variables, tracking depth beneath quantifiers.
- `Formula.instantiateAt` and `Formula.instantiate` substitute a term into a surrounding
  variable position or quantifier body, lifting it beneath inner binders and lowering later indices.
- `Term.bound` and `Formula.bound` give the number of surrounding variable positions
  needed by the syntax; `Formula.isClosed` tests whether the formula bound is `0`.
-/

@[expose] public section

pra

namespace FOL

/-! ## Syntax -/

namespace Term

/--
`Term.const L j` encodes constant symbol `j` in language code `L`,
for `j < Language.constants L`.
-/
def const : Nat → Nat → Nat := fun _ j => j

/--
`Term.var L i` encodes variable index `i` in language code `L`. Indices start at zero;
under `d` surrounding binders, `i < d` refers to one of those binders and `i - d` otherwise
identifies a position in the surrounding context. Indices count outward from the nearest binder.
-/
def var : Nat → Nat → Nat := fun L i => Language.constants L + S (Language.functionCount L) * i

/--
`Term.app L j args` encodes an application of function symbol `j` in language code `L`,
for `j < Language.functionCount L`. `args` is a tuple code of `Language.functionArity L j`
term codes.
-/
def app : Nat → Nat → Nat → Nat :=
  fun L j args => Language.constants L + (S (Language.functionCount L) * args + S j)

/--
`Term.head L t` reads the head code of a nonconstant term code `t` in language code `L`:
`0` for a variable and `S j` for function symbol `j`. Use with `Language.constants L ≤ t`.
-/
def head : Nat → Nat → Nat := fun L t => (t - Language.constants L) % S (Language.functionCount L)

/--
`Term.arg L t` reads the variable index or argument tuple from a nonconstant term code `t`
in language code `L`. Use with `Language.constants L ≤ t`.
-/
def arg : Nat → Nat → Nat := fun L t => (t - Language.constants L) / S (Language.functionCount L)

theorem constants_le_var : ∀ L i, Language.constants L ≤ var L i := by
  intro L i
  exact le_add_right (Language.constants L) (S (Language.functionCount L) * i)

theorem constants_le_app : ∀ L j args, Language.constants L ≤ app L j args := by
  intro L j args
  exact le_add_right (Language.constants L) (S (Language.functionCount L) * args + S j)

theorem head_var : ∀ L i, head L (var L i) = 0 := by
  intro L i
  rw [head, var, add_sub_self_left]
  exact mod_mul (S (Language.functionCount L)) i

theorem arg_var : ∀ L i, arg L (var L i) = i := by
  intro L i
  rw [arg, var, add_sub_self_left]
  exact div_mul (S (Language.functionCount L)) i (succ_ne_zero (Language.functionCount L))

theorem head_app : ∀ L j args, j < Language.functionCount L → head L (app L j args) = S j := by
  intro L j args hj
  rw [head, app, add_sub_self_left]
  exact mod_mul_add_of_lt (S (Language.functionCount L)) args (S j)
    (succ_ne_zero (Language.functionCount L))
    (and_right (succ_le_succ (S j) (Language.functionCount L)) hj)

theorem arg_app : ∀ L j args, j < Language.functionCount L → arg L (app L j args) = args := by
  intro L j args hj
  rw [arg, app, add_sub_self_left]
  exact div_mul_add_of_lt (S (Language.functionCount L)) args (S j)
    (succ_ne_zero (Language.functionCount L))
    (and_right (succ_le_succ (S j) (Language.functionCount L)) hj)

theorem args_lt_app : ∀ L j args, args < app L j args := by
  intro L j args
  have h₁ := le_mul_of_pos args (S (Language.functionCount L))
    (succ_ne_zero (Language.functionCount L))
  have h₂ := le_add_right (S (Language.functionCount L) * args) j
  have h₃ : args < S (Language.functionCount L) * args + S j :=
    and_right (lt_succ args (S (Language.functionCount L) * args + j)) (le_trans _ _ _ h₁ h₂)
  exact lt_of_lt_of_le _ _ _ h₃
    (le_add_left (Language.constants L) (S (Language.functionCount L) * args + S j))

end Term

namespace Formula

/-- `Formula.falsum` is the formula code for falsity (`0`). -/
def falsum : Nat := 0

/--
`Formula.equal L t u` encodes the equality formula between term codes `t` and `u`
in language code `L`.
-/
def equal : Nat → Nat → Nat → Nat :=
  fun L t u => S (3 * (S (Language.relationCount L) * pair t u))

/--
`Formula.rel L j args` encodes a relation formula in language code `L`,
for `j < Language.relationCount L`. `args` is a tuple code of `Language.relationArity L j`
term codes.
-/
def rel : Nat → Nat → Nat → Nat :=
  fun L j args => S (3 * (S (Language.relationCount L) * args + S j))

/-- `Formula.imp A B` encodes implication from formula code `A` to formula code `B`. -/
def imp : Nat → Nat → Nat := fun A B => S (3 * pair A B + 1)

/--
`Formula.all A` encodes universal quantification with formula code `A` as its body.
The new binder binds index `0` at the root of `A`, index `1` beneath one inner quantifier,
and so on.
-/
def all : Nat → Nat := fun A => S (3 * A + 2)

/-- `Formula.neg A` encodes negation of formula code `A` as `A → ⊥`. -/
def neg : Nat → Nat := fun A => imp A falsum

/-- `Formula.conj A B` encodes conjunction of formula codes `A` and `B` as `¬ (A → ¬ B)`. -/
def conj : Nat → Nat → Nat := fun A B => neg (imp A (neg B))

/-- `Formula.disj A B` encodes disjunction of formula codes `A` and `B` as `¬ A → B`. -/
def disj : Nat → Nat → Nat := fun A B => imp (neg A) B

/--
`Formula.ex A` encodes existential quantification with formula code `A` as its body,
as `¬ ∀ ¬ A`. Variable indices follow the convention of `Formula.all`.
-/
def ex : Nat → Nat := fun A => neg (all (neg A))

/--
`Formula.head L A` reads the head code of positive formula code `A` in language code `L`:
`0` for equality, `1` for implication, `2` for universal quantification, and `3` for a relation.
Falsity is recognized by `A = 0`.
-/
def head : Nat → Nat → Nat := fun L A =>
  ite (pred A % 3) (pred A % 3)
    (ite ((pred A / 3) % S (Language.relationCount L)) 3 0)

/--
`Formula.arg L A` reads the arguments of positive formula code `A` in language code `L`:
a pair of term codes for equality, a tuple code of term codes for a relation, a pair of formula
codes for implication, or the body formula code for universal quantification.
-/
def arg : Nat → Nat → Nat := fun L A =>
  ite (pred A % 3) (pred A / 3) ((pred A / 3) / S (Language.relationCount L))

/--
`Formula.relationIndex L A` reads the relation symbol index from relation formula code `A`
in language code `L`. Use with `Formula.head L A = 3` and `0 < A`.
-/
def relationIndex : Nat → Nat → Nat := fun L A =>
  pred ((pred A / 3) % S (Language.relationCount L))

theorem equal_ne_zero : ∀ L t u, ¬ equal L t u = 0 :=
  fun L t u => succ_ne_zero (3 * (S (Language.relationCount L) * pair t u))

theorem rel_ne_zero : ∀ L j args, ¬ rel L j args = 0 :=
  fun L j args => succ_ne_zero (3 * (S (Language.relationCount L) * args + S j))

theorem imp_ne_zero : ∀ A B, ¬ imp A B = 0 := fun A B => succ_ne_zero (3 * pair A B + 1)

theorem all_ne_zero : ∀ A, ¬ all A = 0 := fun A => succ_ne_zero (3 * A + 2)

theorem head_equal : ∀ L t u, head L (equal L t u) = 0 := by
  intro L t u
  rw [head, equal, pred_succ, mod_mul, div_mul 3 _ (succ_ne_zero 2), mod_mul]
  rfl

theorem arg_equal : ∀ L t u, arg L (equal L t u) = pair t u := by
  intro L t u
  rw [arg, equal, pred_succ, mod_mul, div_mul 3 _ (succ_ne_zero 2),
    div_mul _ _ (succ_ne_zero (Language.relationCount L))]
  rfl

theorem head_rel : ∀ L j args, j < Language.relationCount L → head L (rel L j args) = 3 := by
  intro L j args hj
  rw [head, rel, pred_succ, mod_mul, div_mul 3 _ (succ_ne_zero 2),
    mod_mul_add_of_lt _ args (S j) (succ_ne_zero (Language.relationCount L))
      (and_right (succ_le_succ (S j) (Language.relationCount L)) hj)]
  rfl

theorem arg_rel : ∀ L j args, j < Language.relationCount L → arg L (rel L j args) = args := by
  intro L j args hj
  rw [arg, rel, pred_succ, mod_mul, div_mul 3 _ (succ_ne_zero 2),
    div_mul_add_of_lt _ args (S j) (succ_ne_zero (Language.relationCount L))
      (and_right (succ_le_succ (S j) (Language.relationCount L)) hj)]
  rfl

theorem relationIndex_rel : ∀ L j args, j < Language.relationCount L →
    relationIndex L (rel L j args) = j := by
  intro L j args hj
  rw [relationIndex, rel, pred_succ, div_mul 3 _ (succ_ne_zero 2),
    mod_mul_add_of_lt _ args (S j) (succ_ne_zero (Language.relationCount L))
      (and_right (succ_le_succ (S j) (Language.relationCount L)) hj)]
  rfl

theorem head_imp : ∀ L A B, head L (imp A B) = 1 := by
  intro L A B
  rw [head, imp, pred_succ, mod_mul_add_of_lt 3 _ 1 (succ_ne_zero 2) rfl]
  rfl

theorem arg_imp : ∀ L A B, arg L (imp A B) = pair A B := by
  intro L A B
  rw [arg, imp, pred_succ, mod_mul_add_of_lt 3 _ 1 (succ_ne_zero 2) rfl,
    div_mul_add_of_lt 3 _ 1 (succ_ne_zero 2) rfl]
  rfl

theorem head_all : ∀ L A, head L (all A) = 2 := by
  intro L A
  rw [head, all, pred_succ, mod_mul_add_of_lt 3 _ 2 (succ_ne_zero 2) rfl]
  rfl

theorem arg_all : ∀ L A, arg L (all A) = A := by
  intro L A
  rw [arg, all, pred_succ, mod_mul_add_of_lt 3 _ 2 (succ_ne_zero 2) rfl,
    div_mul_add_of_lt 3 _ 2 (succ_ne_zero 2) rfl]
  rfl

theorem left_lt_imp : ∀ A B, A < imp A B := by
  intro A B
  apply and_right (lt_succ A (3 * pair A B + 1))
  exact le_trans _ _ _ (left_le_pair A B)
    (le_trans _ _ _ (le_mul_of_pos (pair A B) 3 (succ_ne_zero 2))
      (le_add_right (3 * pair A B) 1))

theorem right_lt_imp : ∀ A B, B < imp A B := by
  intro A B
  apply and_right (lt_succ B (3 * pair A B + 1))
  exact le_trans _ _ _ (right_le_pair A B)
    (le_trans _ _ _ (le_mul_of_pos (pair A B) 3 (succ_ne_zero 2))
      (le_add_right (3 * pair A B) 1))

theorem body_lt_all : ∀ A, A < all A := by
  intro A
  apply and_right (lt_succ A (3 * A + 2))
  exact le_trans _ _ _ (le_mul_of_pos A 3 (succ_ne_zero 2)) (le_add_right (3 * A) 2)

theorem imp_arg_of_head_eq_one : ∀ L A, ¬ A = 0 → head L A = 1 →
    imp (unpairLeft (arg L A)) (unpairRight (arg L A)) = A := by
  intro L A ha hh
  have hm : pred A % 3 = 1 := by
    by_cases hz : pred A % 3 = 0
    · rw [head, hz] at hh
      by_cases hr : (pred A / 3) % S (Language.relationCount L) = 0
      · rw [hr] at hh
        exact false_elim (zero_ne_succ 0 hh)
      · rw [ite_of_ne_zero _ _ _ hr] at hh
        exact false_elim (succ_ne_zero 1 (eq_congr pred hh))
    · rw [head, ite_of_ne_zero _ _ _ hz] at hh
      exact hh
  rw [imp, pair_unpair, arg, hm]
  exact eq_trans (eq_congr S (eq_trans
    (eq_congr (fun r => 3 * (pred A / 3) + r) (eq_symm hm)) (div_mod (pred A) 3)))
    (succ_pred A ha)

theorem all_arg_of_head_eq_two : ∀ L A, ¬ A = 0 → head L A = 2 → all (arg L A) = A := by
  intro L A ha hh
  have hm : pred A % 3 = 2 := by
    by_cases hz : pred A % 3 = 0
    · rw [head, hz] at hh
      by_cases hr : (pred A / 3) % S (Language.relationCount L) = 0
      · rw [hr] at hh
        exact false_elim (zero_ne_succ 1 hh)
      · rw [ite_of_ne_zero _ _ _ hr] at hh
        exact false_elim (succ_ne_zero 0 (eq_congr pred (eq_congr pred hh)))
    · rw [head, ite_of_ne_zero _ _ _ hz] at hh
      exact hh
  rw [all, arg, hm]
  exact eq_trans (eq_congr S (eq_trans
    (eq_congr (fun r => 3 * (pred A / 3) + r) (eq_symm hm)) (div_mod (pred A) 3)))
    (succ_pred A ha)

/--
`Formula.allN n A` adds `n` universal quantifiers around formula code `A`.
When `Formula.bound L A ≤ n`, the result has bound `0`.
-/
def allN : Nat → Nat → Nat := fun n A => iter all n A

theorem allN_zero : ∀ A, allN 0 A = A := fun A => rfl

theorem allN_succ : ∀ n A, allN (S n) A = all (allN n A) := fun n A => rfl

/--
`Formula.equalPremises L n xs ys A` encodes `x₀ = y₀ → ⋯ → xₙ₋₁ = yₙ₋₁ → A`
in language code `L`. `xs` and `ys` are tuple codes of `n` terms, and `A` is a formula code.
For `n = 0`, the result is `A` and both tuple arguments are ignored.
-/
def equalPremises : Nat → Nat → Nat → Nat → Nat → Nat := fun L n xs ys A =>
  primrec A (fun i B => imp
    (equal L (Tuple.get n xs (n - S i)) (Tuple.get n ys (n - S i))) B) n

theorem equalPremises_succ_ne_zero : ∀ L n xs ys A,
    ¬ equalPremises L (S n) xs ys A = 0 :=
  fun L n xs ys A => imp_ne_zero _ _

theorem head_equalPremises_succ : ∀ L n xs ys A,
    head L (equalPremises L (S n) xs ys A) = 1 :=
  fun L n xs ys A => head_imp L _ _

theorem equalPremises_consequent : ∀ L n xs ys A,
    iter (fun B => unpairRight (arg L B)) n (equalPremises L n xs ys A) = A := by
  intro L n xs ys A
  let step := fun i B => imp
    (equal L (Tuple.get n xs (n - S i)) (Tuple.get n ys (n - S i))) B
  have peel : ∀ i B, unpairRight (arg L (step i B)) = B := by
    intro i B
    exact eq_trans (eq_congr unpairRight (arg_imp L _ B)) (unpairRight_pair _ B)
  have h : ∀ k, iter (fun B => unpairRight (arg L B)) k (primrec A step k) = A := by
    intro k
    induction k with j ih
    · rfl
    · exact eq_trans
        (eq_symm (iter_succ_apply (fun B => unpairRight (arg L B)) j
          (step j (primrec A step j))))
        (eq_trans (eq_congr (iter (fun B => unpairRight (arg L B)) j)
          (peel j (primrec A step j))) ih)
  exact h n

theorem equalPremises_one : ∀ L x y A,
    equalPremises L 1 x y A = imp (equal L x y) A := fun L x y A => rfl

theorem equalPremises_two : ∀ L x y u v A,
    equalPremises L 2 (pair x y) (pair u v) A =
      imp (equal L x u) (imp (equal L y v) A) := by
  intro L x y u v A
  change imp (equal L (unpairLeft (pair x y)) (unpairLeft (pair u v)))
    (imp (equal L (unpairRight (pair x y)) (unpairRight (pair u v))) A) = _
  rw [unpairLeft_pair, unpairLeft_pair, unpairRight_pair, unpairRight_pair]

end Formula

/-! ## Recursion -/

namespace Term

/--
`Term.rec var const app L t` processes term code `t` in language code `L` to a numerical value:

- `var i` handles variable index `i`.
- `const j` handles constant symbol index `j`.
- `app j xs` handles function symbol index `j`, with `xs` a tuple of child results of length
  `Language.functionArity L j`.
-/
def rec (var const : Nat → Nat) (app : Nat → Nat → Nat) : Nat → Nat → Nat :=
  fun L => covrec (fun t history => ite (ltb t (Language.constants L)) (const t)
    (ite (head L t)
      (app (pred (head L t)) (Tuple.map (fun a => Sequence.rget history a)
        (Language.functionArity L (pred (head L t))) (arg L t)))
      (var (arg L t))))

theorem rec_const (var const : Nat → Nat) (app : Nat → Nat → Nat) :
    ∀ L j, j < Language.constants L → rec var const app L (Term.const L j) = const j := by
  intro L j hj
  change rec var const app L j = const j
  rw [rec, covrec, and_right (ltb_eq_one j (Language.constants L)) hj]
  rfl

theorem rec_var (var const : Nat → Nat) (app : Nat → Nat → Nat) :
    ∀ L i, rec var const app L (Term.var L i) = var i := by
  intro L i
  rw [rec, covrec,
    ltb_eq_zero_of_ge (Term.var L i) (Language.constants L) (constants_le_var L i),
    head_var, arg_var]
  rfl

theorem rec_app (var const : Nat → Nat) (app : Nat → Nat → Nat) :
    ∀ L j args, j < Language.functionCount L →
    rec var const app L (Term.app L j args) =
      app j (Tuple.map (rec var const app L) (Language.functionArity L j) args) := by
  intro L j args hj
  rw [rec, covrec,
    ltb_eq_zero_of_ge (Term.app L j args) (Language.constants L) (constants_le_app L j args),
    head_app L j args hj, arg_app L j args hj]
  change app j (Tuple.map _ (Language.functionArity L j) args) = _
  apply eq_congr (app j)
  apply Tuple.map_congr_of_get_eq _ _
  intro i hi
  rw [Sequence.rget_generate _ (Tuple.get (Language.functionArity L j) args i)
    (Term.app L j args) (lt_of_le_of_lt _ args _
      (Tuple.get_le (Language.functionArity L j) args i) (args_lt_app L j args))]
  rfl

theorem rec_app_one (var const : Nat → Nat) (app : Nat → Nat → Nat) :
    ∀ L j x, j < Language.functionCount L → Language.functionArity L j = 1 →
    rec var const app L (Term.app L j x) = app j (rec var const app L x) := by
  intro L j x hj ha
  rw [rec_app var const app L j x hj, ha, Tuple.map_one _]

theorem rec_app_two (var const : Nat → Nat) (app : Nat → Nat → Nat) :
    ∀ L j x y, j < Language.functionCount L → Language.functionArity L j = 2 →
    rec var const app L (Term.app L j (pair x y)) =
      app j (pair (rec var const app L x) (rec var const app L y)) := by
  intro L j x y hj ha
  rw [rec_app var const app L j (pair x y) hj, ha, Tuple.map_two _]

end Term

namespace Formula

/-- Binder traversal increases depth by one while strictly decreasing the paired recursion rank. -/
theorem binder_rank_lt : ∀ A d, pair A (S d) < pair (all A) d := by
  intro A d
  apply pair_lt_of_sum_lt A (S d) (all A) d
  have h : S A < all A := by
    apply and_right (lt_succ (S A) (3 * A + 2))
    exact le_trans _ _ _
      (and_right (succ_le_succ A (3 * A)) (le_mul_of_pos A 3 (succ_ne_zero 2)))
      (le_succ_self (S (3 * A)))
  have hd := add_lt_add_right (S A) (all A) d h
  rw [succ_add] at hd
  exact hd

/--
`Formula.recWithDepth equal rel imp all L falsum A d` processes formula code `A` to a numerical
value in language code `L`, starting at binder depth `d`:

- `falsum` is the value for falsity.
- `equal k t s` handles equality of term codes `t`, `s` at the current binder depth `k`.
- `rel k j xs` handles relation symbol index `j` at depth `k`, with a tuple `xs` of term codes
  of length `Language.relationArity L j`.
- `imp x y` combines the results for the antecedent and consequent of an implication.
- `all x` handles a quantified body, whose result `x` is computed one binder deeper.

The equality and relation handlers receive term codes; they can use `Term.rec` to process them.
-/
def recWithDepth (equal rel : Nat → Nat → Nat → Nat) (imp : Nat → Nat → Nat) (all : Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat :=
  fun L falsum A d => covrec (fun n history =>
    let A := unpairLeft n;
    let d := unpairRight n;
    ite A
      (ite (head L A)
        (ite (eqb (head L A) 1)
          (imp (Sequence.rget history (pair (unpairLeft (arg L A)) d))
            (Sequence.rget history (pair (unpairRight (arg L A)) d)))
          (ite (eqb (head L A) 2)
            (all (Sequence.rget history (pair (arg L A) (S d))))
            (rel d (relationIndex L A) (arg L A))))
        (equal d (unpairLeft (arg L A)) (unpairRight (arg L A)))) falsum) (pair A d)

theorem recWithDepth_falsum (equal rel : Nat → Nat → Nat → Nat) (imp : Nat → Nat → Nat)
    (all : Nat → Nat) : ∀ L falsum d,
    recWithDepth equal rel imp all L falsum Formula.falsum d = falsum := by
  intro L falsum d
  rw [recWithDepth, covrec, unpairLeft_pair, unpairRight_pair]
  rfl

theorem recWithDepth_equal (equal rel : Nat → Nat → Nat → Nat) (imp : Nat → Nat → Nat)
    (all : Nat → Nat) : ∀ L falsum t s d,
    recWithDepth equal rel imp all L falsum (Formula.equal L t s) d = equal d t s := by
  intro L falsum t s d
  rw [recWithDepth, covrec, unpairLeft_pair, unpairRight_pair]
  change ite (Formula.equal L t s) _ falsum = _
  rw [ite_of_ne_zero _ _ _ (equal_ne_zero L t s), head_equal,
    arg_equal, unpairLeft_pair, unpairRight_pair]
  rfl

theorem recWithDepth_rel (equal rel : Nat → Nat → Nat → Nat) (imp : Nat → Nat → Nat)
    (all : Nat → Nat) : ∀ L falsum j xs d, j < Language.relationCount L →
    recWithDepth equal rel imp all L falsum (Formula.rel L j xs) d = rel d j xs := by
  intro L falsum j xs d hj
  rw [recWithDepth, covrec, unpairLeft_pair, unpairRight_pair]
  change ite (Formula.rel L j xs) _ falsum = _
  rw [ite_of_ne_zero _ _ _ (rel_ne_zero L j xs), head_rel L j xs hj,
    relationIndex_rel L j xs hj, arg_rel L j xs hj]
  rfl

theorem recWithDepth_imp (equal rel : Nat → Nat → Nat → Nat) (imp : Nat → Nat → Nat)
    (all : Nat → Nat) : ∀ L falsum A B d,
    recWithDepth equal rel imp all L falsum (Formula.imp A B) d =
      imp (recWithDepth equal rel imp all L falsum A d)
        (recWithDepth equal rel imp all L falsum B d) := by
  intro L falsum A B d
  rw [recWithDepth, covrec, unpairLeft_pair, unpairRight_pair]
  change ite (Formula.imp A B) _ falsum = _
  rw [ite_of_ne_zero _ _ _ (imp_ne_zero A B), head_imp, arg_imp,
    unpairLeft_pair, unpairRight_pair]
  change imp (Sequence.rget _ (pair A d)) (Sequence.rget _ (pair B d)) = _
  rw [Sequence.rget_generate _ (pair A d) (pair (Formula.imp A B) d)
      (pair_lt_left A d (Formula.imp A B) d (left_lt_imp A B) (le_refl d)),
    Sequence.rget_generate _ (pair B d) (pair (Formula.imp A B) d)
      (pair_lt_left B d (Formula.imp A B) d (right_lt_imp A B) (le_refl d))]
  rfl

theorem recWithDepth_all (equal rel : Nat → Nat → Nat → Nat) (imp : Nat → Nat → Nat)
    (all : Nat → Nat) : ∀ L falsum A d,
    recWithDepth equal rel imp all L falsum (Formula.all A) d =
      all (recWithDepth equal rel imp all L falsum A (S d)) := by
  intro L falsum A d
  rw [recWithDepth, covrec, unpairLeft_pair, unpairRight_pair]
  change ite (Formula.all A) _ falsum = _
  rw [ite_of_ne_zero _ _ _ (all_ne_zero A), head_all, arg_all]
  change all (Sequence.rget _ (pair A (S d))) = _
  rw [Sequence.rget_generate _ (pair A (S d)) (pair (Formula.all A) d) (binder_rank_lt A d)]
  rfl

/-- Ignoring depth in the atomic handlers makes the result independent of the starting depth. -/
theorem recWithDepth_eq_zero_depth (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) :
    ∀ L falsum A d,
    recWithDepth (fun _ t s => equal t s) (fun _ j xs => rel j xs) imp all L falsum A d =
      recWithDepth (fun _ t s => equal t s) (fun _ j xs => rel j xs) imp all L falsum A 0 := by
  intro L falsum A d
  let R := recWithDepth (fun _ t s => equal t s) (fun _ j xs => rel j xs) imp all L falsum
  have atomic : ∀ B k, ¬ B = 0 → ¬ head L B = 1 → ¬ head L B = 2 →
      R B k = ite (head L B) (rel (relationIndex L B) (arg L B))
        (equal (unpairLeft (arg L B)) (unpairRight (arg L B))) := by
    intro B k hz h1 h2
    change recWithDepth (fun _ t s => equal t s) (fun _ j xs => rel j xs)
      imp all L falsum B k = _
    rw [recWithDepth, covrec, unpairLeft_pair, unpairRight_pair,
      ite_of_ne_zero B _ _ hz,
      and_right (eqb_eq_zero (head L B) 1) h1,
      and_right (eqb_eq_zero (head L B) 2) h2]
    rfl
  have invariant : ∀ n, R (unpairLeft n) (unpairRight n) = R (unpairLeft n) 0 := by
    apply strong_induction_of_bool
      (fun n => R (unpairLeft n) (unpairRight n) = R (unpairLeft n) 0)
      (fun n => eqb (R (unpairLeft n) (unpairRight n)) (R (unpairLeft n) 0))
    · intro n
      constructor
      · intro h
        by_contra he
        exact h (and_right (eqb_eq_zero _ _) he)
      · intro he h
        exact and_left (eqb_eq_zero _ _) h he
    · intro n earlier
      let B := unpairLeft n
      let k := unpairRight n
      have ih : ∀ C e, pair C e < pair B k → R C e = R C 0 := by
        intro C e hc
        have hn : pair B k = n := pair_unpair n
        rw [hn] at hc
        have result := earlier (pair C e) hc
        rw [unpairLeft_pair, unpairRight_pair] at result
        exact result
      change recWithDepth (fun _ t s => equal t s) (fun _ j xs => rel j xs)
        imp all L falsum B k = recWithDepth (fun _ t s => equal t s)
          (fun _ j xs => rel j xs) imp all L falsum B 0
      by_cases hz : B = 0
      · rw [hz]
        exact eq_trans
          (recWithDepth_falsum (fun _ t s => equal t s) (fun _ j xs => rel j xs)
            imp all L falsum k)
          (eq_symm (recWithDepth_falsum (fun _ t s => equal t s)
            (fun _ j xs => rel j xs) imp all L falsum 0))
      by_cases h1 : head L B = 1
      · let C := unpairLeft (arg L B)
        let D := unpairRight (arg L B)
        have he : Formula.imp C D = B := imp_arg_of_head_eq_one L B hz h1
        have hc : C < B := by
          have h := left_lt_imp C D
          rw [he] at h
          exact h
        have hd : D < B := by
          have h := right_lt_imp C D
          rw [he] at h
          exact h
        have ec := ih C k (pair_lt_left C k B k hc (le_refl k))
        have ed := ih D k (pair_lt_left D k B k hd (le_refl k))
        have ek := recWithDepth_imp (fun _ t s => equal t s) (fun _ j xs => rel j xs)
          imp all L falsum C D k
        have ez := recWithDepth_imp (fun _ t s => equal t s) (fun _ j xs => rel j xs)
          imp all L falsum C D 0
        rw [he] at ek
        rw [he] at ez
        exact eq_trans ek (eq_trans (eq_congr₂ imp ec ed) (eq_symm ez))
      by_cases h2 : head L B = 2
      · let C := arg L B
        have he : Formula.all C = B := all_arg_of_head_eq_two L B hz h2
        have hc : pair C (S k) < pair B k := by
          have h := binder_rank_lt C k
          rw [he] at h
          exact h
        have hzero : pair C 1 < pair B k :=
          lt_of_le_of_lt _ _ _
            (pair_mono C 1 C (S k) (le_refl C)
              (and_right (succ_le_succ 0 k) (zero_le k))) hc
        have ec := eq_trans (ih C (S k) hc) (eq_symm (ih C 1 hzero))
        have ek := recWithDepth_all (fun _ t s => equal t s) (fun _ j xs => rel j xs)
          imp all L falsum C k
        have ez := recWithDepth_all (fun _ t s => equal t s) (fun _ j xs => rel j xs)
          imp all L falsum C 0
        rw [he] at ek
        rw [he] at ez
        exact eq_trans ek (eq_trans (eq_congr all ec) (eq_symm ez))
      exact eq_trans (atomic B k hz h1 h2) (eq_symm (atomic B 0 hz h1 h2))
  have result := invariant (pair A d)
  rw [unpairLeft_pair, unpairRight_pair] at result
  exact result

/--
`Formula.rec equal rel imp all L falsum A` processes formula code `A` in language code `L`.
It uses `recWithDepth` with handlers that ignore binder depth:

- `falsum` is the value for falsity.
- `equal t s` handles equality of term codes `t`, `s`.
- `rel j xs` handles relation symbol index `j` and its tuple `xs` of term codes.
- `imp x y` combines the results for the antecedent and consequent.
- `all x` handles the result for a quantified body.
-/
def rec (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) :
    Nat → Nat → Nat → Nat := fun L falsum A =>
  recWithDepth (fun _ t s => equal t s) (fun _ j xs => rel j xs) imp all L falsum A 0

theorem rec_falsum (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) :
    ∀ L falsum, rec equal rel imp all L falsum Formula.falsum = falsum :=
  fun L falsum => recWithDepth_falsum
    (fun _ t s => equal t s) (fun _ j xs => rel j xs) imp all L falsum 0

theorem rec_equal (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) :
    ∀ L falsum t s, rec equal rel imp all L falsum (Formula.equal L t s) = equal t s :=
  fun L falsum t s => recWithDepth_equal
    (fun _ t s => equal t s) (fun _ j xs => rel j xs) imp all L falsum t s 0

theorem rec_rel (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) :
    ∀ L falsum j xs, j < Language.relationCount L →
    rec equal rel imp all L falsum (Formula.rel L j xs) = rel j xs :=
  fun L falsum j xs hj => recWithDepth_rel
    (fun _ t s => equal t s) (fun _ j xs => rel j xs) imp all L falsum j xs 0 hj

theorem rec_imp (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) : ∀ L falsum A B,
    rec equal rel imp all L falsum (Formula.imp A B) =
      imp (rec equal rel imp all L falsum A) (rec equal rel imp all L falsum B) :=
  fun L falsum A B => recWithDepth_imp
    (fun _ t s => equal t s) (fun _ j xs => rel j xs) imp all L falsum A B 0

theorem rec_all (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) : ∀ L falsum A,
    rec equal rel imp all L falsum (Formula.all A) =
      all (rec equal rel imp all L falsum A) := by
  intro L falsum A
  exact eq_trans (recWithDepth_all
    (fun _ t s => equal t s) (fun _ j xs => rel j xs) imp all L falsum A 0)
    (eq_congr all (recWithDepth_eq_zero_depth equal rel imp all L falsum A 1))

end Formula

/-! ## Substitution -/

namespace Term

/--
`Term.subst f L t` simultaneously substitutes terms for variables in term code `t` in language
code `L`. `f i` supplies the term code for variable index `i`, inserted unchanged.
Constants and function symbols are preserved.
-/
def subst (f : Nat → Nat) : Nat → Nat → Nat :=
  fun L => rec f (const L) (app L) L

theorem subst_const (f : Nat → Nat) : ∀ L j, j < Language.constants L →
    subst f L (const L j) = const L j := fun L j h => rec_const f (const L) (app L) L j h

theorem subst_var (f : Nat → Nat) : ∀ L i, subst f L (var L i) = f i :=
  fun L i => rec_var f (const L) (app L) L i

theorem subst_app (f : Nat → Nat) : ∀ L j args, j < Language.functionCount L →
    subst f L (app L j args) =
      app L j (Tuple.map (subst f L) (Language.functionArity L j) args) :=
  fun L j args hj => rec_app f (const L) (app L) L j args hj

theorem subst_app_one (f : Nat → Nat) : ∀ L j t,
    j < Language.functionCount L → Language.functionArity L j = 1 →
    subst f L (app L j t) = app L j (subst f L t) :=
  fun L j t hj ha => rec_app_one f (const L) (app L) L j t hj ha

theorem subst_app_two (f : Nat → Nat) : ∀ L j t u,
    j < Language.functionCount L → Language.functionArity L j = 2 →
    subst f L (app L j (pair t u)) = app L j (pair (subst f L t) (subst f L u)) :=
  fun L j t u hj ha => rec_app_two f (const L) (app L) L j t u hj ha

/--
`Term.shift L d t` returns the term code obtained by raising every variable index in term
code `t` by `d`, in language code `L`.
-/
def shift : Nat → Nat → Nat → Nat := fun L d => subst (fun n => var L (n + d)) L

/--
`Term.instantiateAt L k t d n` gives the replacement term code for variable index `n` at binder
depth `d`, when surrounding position `k` is replaced by term code `t` in language code `L`.
Indices below `d` are preserved; position `k` receives `t` shifted by `d`; later positions
move down by one. This removes position `k` from the surrounding variable context.
-/
def instantiateAt : Nat → Nat → Nat → Nat → Nat → Nat := fun L k t d n =>
  ite (ltb n d) (var L n)
    (ite (eqb (n - d) k) (shift L d t)
      (var L (ite (ltb k (n - d)) (pred n) n)))

/--
`Term.bound L t` is one more than the largest variable index in term code `t` in language
code `L`, or `0` when the term contains no variables.
-/
def bound : Nat → Nat → Nat := fun L =>
  rec S (fun _ => 0) (fun j xs => Tuple.max (Language.functionArity L j) xs) L

theorem bound_const : ∀ L j, j < Language.constants L → bound L (const L j) = 0 :=
  fun L j hj => rec_const S (fun _ => 0)
    (fun j xs => Tuple.max (Language.functionArity L j) xs) L j hj

theorem bound_var : ∀ L n, bound L (var L n) = S n :=
  fun L n => rec_var S (fun _ => 0)
    (fun j xs => Tuple.max (Language.functionArity L j) xs) L n

theorem bound_app : ∀ L j args, j < Language.functionCount L →
    bound L (app L j args) = Tuple.max (Language.functionArity L j)
      (Tuple.map (bound L) (Language.functionArity L j) args) :=
  fun L j args hj => rec_app S (fun _ => 0)
    (fun j xs => Tuple.max (Language.functionArity L j) xs) L j args hj

theorem bound_app_one : ∀ L j t,
    j < Language.functionCount L → Language.functionArity L j = 1 →
    bound L (app L j t) = bound L t := by
  intro L j t hj ha
  rw [bound_app L j t hj, ha, Tuple.map_one _, Tuple.max_one]

theorem bound_app_two : ∀ L j t u,
    j < Language.functionCount L → Language.functionArity L j = 2 →
    bound L (app L j (pair t u)) = max (bound L t) (bound L u) := by
  intro L j t u hj ha
  rw [bound_app L j (pair t u) hj, ha, Tuple.map_two _, Tuple.max_two]

end Term

namespace Formula

/--
`Formula.subst f L A d` replaces variables in formula code `A` in language code `L`, starting
at binder depth `d`. `f k i` supplies a term code for variable index `i` at the current depth
`k`. Each quantifier increases `k` by one; `f` determines how bound variables are treated.
-/
def subst (f : Nat → Nat → Nat) : Nat → Nat → Nat → Nat := fun L =>
  recWithDepth (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs)) imp all L falsum

theorem subst_falsum (f : Nat → Nat → Nat) : ∀ L d, subst f L falsum d = falsum :=
  fun L d => recWithDepth_falsum
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs)) imp all L falsum d

theorem subst_equal (f : Nat → Nat → Nat) : ∀ L t s d,
    subst f L (equal L t s) d = equal L (Term.subst (f d) L t) (Term.subst (f d) L s) :=
  fun L t s d => recWithDepth_equal
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs)) imp all L falsum t s d

theorem subst_rel (f : Nat → Nat → Nat) : ∀ L j xs d, j < Language.relationCount L →
    subst f L (rel L j xs) d =
      rel L j (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs) :=
  fun L j xs d hj => recWithDepth_rel
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs)) imp all L falsum j xs d hj

theorem subst_imp (f : Nat → Nat → Nat) : ∀ L A B d,
    subst f L (imp A B) d = imp (subst f L A d) (subst f L B d) :=
  fun L A B d => recWithDepth_imp
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs)) imp all L falsum A B d

theorem subst_all (f : Nat → Nat → Nat) : ∀ L A d, subst f L (all A) d = all (subst f L A (S d)) :=
  fun L A d => recWithDepth_all
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs)) imp all L falsum A d

/--
`Formula.instantiateAt L k A t` substitutes term code `t` for surrounding position `k` in
formula code `A`, in language code `L`. Indices referring to inner binders and earlier
surrounding positions are preserved; `t` is shifted beneath binders, and later positions
move down by one.
-/
def instantiateAt : Nat → Nat → Nat → Nat → Nat :=
  fun L k A t => subst (Term.instantiateAt L k t) L A 0

/--
`Formula.instantiate L A t` instantiates the body formula code `A` with term code `t` in language
code `L`. It replaces surrounding position `0`, lifts `t` beneath inner binders, and lowers later
positions by one. Thus `A` is the body passed to `Formula.all` for universal instantiation.
-/
def instantiate : Nat → Nat → Nat → Nat := fun L A t => instantiateAt L 0 A t

/--
`Formula.shift L A` returns the formula code obtained by raising each surrounding variable
position in formula code `A` by one, in language code `L`. Indices referring to binders
inside `A` are preserved.
-/
def shift : Nat → Nat → Nat := fun L A =>
  subst (fun d n => Term.var L (ite (ltb n d) n (S n))) L A 0

/--
`Formula.successorInstance L successor A` replaces surrounding position `0` in formula code `A`
by its successor, preserving other positions. `L` is a language code, and `successor`
is a function symbol index below `Language.functionCount L` with arity `1`.
-/
def successorInstance : Nat → Nat → Nat → Nat := fun L successor A =>
  subst (fun d n => ite (eqb n d) (Term.app L successor (Term.var L n)) (Term.var L n)) L A 0

/--
`Formula.bound L A` gives the number of surrounding variable positions needed by formula
code `A` in language code `L`. Equality and relations take the maximum of their term bounds;
implication takes the maximum of its two formula bounds. A quantifier decreases its body's
bound by one, down to `0`. Falsity has bound `0`.
-/
def bound : Nat → Nat → Nat := fun L =>
  rec (fun t s => max (Term.bound L t) (Term.bound L s))
    (fun j xs => Tuple.max (Language.relationArity L j)
      (Tuple.map (Term.bound L) (Language.relationArity L j) xs)) max pred L 0

/--
`Formula.isClosed L A` returns `1` when `Formula.bound L A = 0` in language code `L`,
and `0` otherwise.
-/
def isClosed : Nat → Nat → Nat := fun L A => eqb (bound L A) 0

theorem bound_falsum : ∀ L, bound L falsum = 0 :=
  fun L => rec_falsum
    (fun t s => max (Term.bound L t) (Term.bound L s))
    (fun j xs => Tuple.max (Language.relationArity L j)
      (Tuple.map (Term.bound L) (Language.relationArity L j) xs)) max pred L 0

theorem bound_equal : ∀ L t s,
    bound L (equal L t s) = max (Term.bound L t) (Term.bound L s) :=
  fun L t s => rec_equal
    (fun t s => max (Term.bound L t) (Term.bound L s))
    (fun j xs => Tuple.max (Language.relationArity L j)
      (Tuple.map (Term.bound L) (Language.relationArity L j) xs)) max pred L 0 t s

theorem bound_rel : ∀ L j xs, j < Language.relationCount L →
    bound L (rel L j xs) = Tuple.max (Language.relationArity L j)
      (Tuple.map (Term.bound L) (Language.relationArity L j) xs) :=
  fun L j xs hj => rec_rel
    (fun t s => max (Term.bound L t) (Term.bound L s))
    (fun j xs => Tuple.max (Language.relationArity L j)
      (Tuple.map (Term.bound L) (Language.relationArity L j) xs)) max pred L 0 j xs hj

theorem bound_imp : ∀ L A B, bound L (imp A B) = max (bound L A) (bound L B) :=
  fun L A B => rec_imp
    (fun t s => max (Term.bound L t) (Term.bound L s))
    (fun j xs => Tuple.max (Language.relationArity L j)
      (Tuple.map (Term.bound L) (Language.relationArity L j) xs)) max pred L 0 A B

theorem bound_all : ∀ L A, bound L (all A) = pred (bound L A) :=
  fun L A => rec_all
    (fun t s => max (Term.bound L t) (Term.bound L s))
    (fun j xs => Tuple.max (Language.relationArity L j)
      (Tuple.map (Term.bound L) (Language.relationArity L j) xs)) max pred L 0 A

end Formula

end FOL

end
