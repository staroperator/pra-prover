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
Formulas have no fixed scope. The main operations and proof principles are:

- `Term.cases` and `Formula.cases` recover the constructor represented by any code.
- `Term.induction_of_bool` and `Formula.induction_of_bool` prove predicates represented by
  numerical tests, using hypotheses for the immediate children.
- `Formula.inductionWithDepth_of_bool` also tracks binder depth, allowing smaller child depths.
- `Term.induction_eq` and `Formula.induction_eq` specialize these principles to equations;
  the formula version tracks binder depth.
- `Term.rec` processes variables, constants, and function applications by numerical recursion,
  passing an exact-arity tuple of child results to the application handler.
- `Formula.recWithDepth` makes the binder depth available to every formula handler.
  Its paired recursion rank decreases when entering a quantified body, even though depth increases.
- `Formula.rec` processes the same cases with handlers that ignore binder depth.
- `Term.subst` and `Formula.substWithDepth` replace variables, tracking depth beneath quantifiers.
- `Formula.instantiateAt` and `Formula.instantiate` substitute a term into a surrounding
  variable position or quantifier body, lifting it beneath inner binders and lowering later indices.
- `Term.bound` and `Formula.bound` give the number of surrounding variable positions
  needed by the syntax.
- `Formula.Closed` states that a formula has no free variable positions;
  `Formula.isClosed` is its numerical test.
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

theorem var_mono : ∀ L i d, var L i ≤ var L (i + d) := by
  intro L i d
  change Language.constants L + S (Language.functionCount L) * i ≤
    Language.constants L + S (Language.functionCount L) * (i + d)
  exact add_le_add_left _ _ (Language.constants L)
    (mul_le_mul_left i (i + d) (S (Language.functionCount L)) (le_add_right i d))

theorem app_mono : ∀ L j xs ys, xs ≤ ys → app L j xs ≤ app L j ys := by
  intro L j xs ys h
  change Language.constants L + (S (Language.functionCount L) * xs + S j) ≤
    Language.constants L + (S (Language.functionCount L) * ys + S j)
  exact add_le_add_left _ _ (Language.constants L)
    (add_le_add_right _ _ (S j) (mul_le_mul_left xs ys (S (Language.functionCount L)) h))

theorem head_lt : ∀ L t, head L t < S (Language.functionCount L) :=
  fun L t => mod_lt (t - Language.constants L) (S (Language.functionCount L))
    (succ_ne_zero (Language.functionCount L))

theorem var_arg_of_head_eq_zero : ∀ L t, Language.constants L ≤ t → head L t = 0 →
    var L (arg L t) = t := by
  intro L t hc hh
  have h : S (Language.functionCount L) * arg L t + head L t = t - Language.constants L :=
    div_mod (t - Language.constants L) (S (Language.functionCount L))
  rw [hh, add_zero] at h
  rw [var, h, add_comm]
  exact sub_add_cancel_of_le t (Language.constants L) hc

theorem app_arg_of_head_ne_zero : ∀ L t,
    Language.constants L ≤ t → ¬ head L t = 0 →
    pred (head L t) < Language.functionCount L ∧
      app L (pred (head L t)) (arg L t) = t := by
  intro L t hc hh
  constructor
  · have h := and_left (lt_succ (head L t) (Language.functionCount L)) (head_lt L t)
    rw [← succ_pred (head L t) hh] at h
    exact h
  · have h : S (Language.functionCount L) * arg L t + head L t = t - Language.constants L :=
      div_mod (t - Language.constants L) (S (Language.functionCount L))
    rw [app, succ_pred (head L t) hh, h, add_comm]
    exact sub_add_cancel_of_le t (Language.constants L) hc

/-- Every number denotes a constant, variable, or application with a valid symbol index. -/
theorem cases (P : Nat → Prop) : ∀ L,
    (∀ j, j < Language.constants L → P (const L j)) →
    (∀ i, P (var L i)) →
    (∀ j args, j < Language.functionCount L → P (app L j args)) → ∀ t, P t := by
  intro L hc hv ha t
  by_cases ht : t < Language.constants L
  · exact hc t ht
  · have hle := le_of_not_lt (Language.constants L) t ht
    by_cases hh : head L t = 0
    · rw [← var_arg_of_head_eq_zero L t hle hh]
      exact hv (arg L t)
    · have h := app_arg_of_head_ne_zero L t hle hh
      rw [← and_right h]
      exact ha (pred (head L t)) (arg L t) (and_left h)

/-- Structural induction on term codes for a predicate represented by the numerical test `f`.
The application case assumes the predicate for each component of its argument tuple. -/
theorem induction_of_bool (P : Nat → Prop) (f : Nat → Nat) : ∀ L,
    (∀ t, ¬ f t = 0 ↔ P t) →
    (∀ j, j < Language.constants L → P (const L j)) →
    (∀ i, P (var L i)) →
    (∀ j args, j < Language.functionCount L →
      (∀ i, i < Language.functionArity L j → P (Tuple.get (Language.functionArity L j) args i)) →
      P (app L j args)) → ∀ t, P t := by
  intro L spec hc hv ha
  apply strong_induction_of_bool P f spec
  apply cases (fun t => (∀ u, u < t → P u) → P t) L
  · intro j hj ih
    exact hc j hj
  · intro i ih
    exact hv i
  · intro j args hj ih
    apply ha j args hj
    intro i hi
    exact ih (Tuple.get (Language.functionArity L j) args i)
      (lt_of_le_of_lt _ args _ (Tuple.get_le (Language.functionArity L j) args i)
        (args_lt_app L j args))

/-- Prove equations on term codes from their constant, variable, and application cases. -/
theorem induction_eq (f g : Nat → Nat) : ∀ L,
    (∀ j, j < Language.constants L → f (const L j) = g (const L j)) →
    (∀ i, f (var L i) = g (var L i)) →
    (∀ j args, j < Language.functionCount L →
      (∀ i, i < Language.functionArity L j →
        f (Tuple.get (Language.functionArity L j) args i) =
          g (Tuple.get (Language.functionArity L j) args i)) →
      f (app L j args) = g (app L j args)) → ∀ t, f t = g t := by
  intro L
  apply induction_of_bool (fun t => f t = g t) (fun t => eqb (f t) (g t)) L
  intro t
  constructor
  · intro h
    by_contra hn
    exact h (and_right (eqb_eq_zero (f t) (g t)) hn)
  · intro h hn
    exact and_left (eqb_eq_zero (f t) (g t)) hn h

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

theorem le_equal_left : ∀ L t u, t ≤ equal L t u := by
  intro L t u
  change t ≤ S (3 * (S (Language.relationCount L) * pair t u))
  exact le_trans _ _ _ (left_le_pair t u)
    (le_trans _ _ _
      (le_mul_of_pos (pair t u) (S (Language.relationCount L))
        (succ_ne_zero (Language.relationCount L)))
      (le_trans _ _ _
        (le_mul_of_pos (S (Language.relationCount L) * pair t u) 3 (succ_ne_zero 2))
        (le_succ_self (3 * (S (Language.relationCount L) * pair t u)))))

theorem le_equal_right : ∀ L t u, u ≤ equal L t u := by
  intro L t u
  change u ≤ S (3 * (S (Language.relationCount L) * pair t u))
  exact le_trans _ _ _ (right_le_pair t u)
    (le_trans _ _ _
      (le_mul_of_pos (pair t u) (S (Language.relationCount L))
        (succ_ne_zero (Language.relationCount L)))
      (le_trans _ _ _
        (le_mul_of_pos (S (Language.relationCount L) * pair t u) 3 (succ_ne_zero 2))
        (le_succ_self (3 * (S (Language.relationCount L) * pair t u)))))

theorem args_le_rel : ∀ L j xs, xs ≤ rel L j xs := by
  intro L j xs
  change xs ≤ S (3 * (S (Language.relationCount L) * xs + S j))
  exact le_trans _ _ _
    (le_mul_of_pos xs (S (Language.relationCount L)) (succ_ne_zero (Language.relationCount L)))
    (le_trans _ _ _ (le_add_right (S (Language.relationCount L) * xs) (S j))
      (le_trans _ _ _
        (le_mul_of_pos (S (Language.relationCount L) * xs + S j) 3 (succ_ne_zero 2))
        (le_succ_self (3 * (S (Language.relationCount L) * xs + S j)))))

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

/-- Every number denotes falsity, an atomic formula, an implication, or a quantifier. -/
theorem cases (P : Nat → Prop) : ∀ L, P falsum →
    (∀ t u, P (equal L t u)) →
    (∀ j xs, j < Language.relationCount L → P (rel L j xs)) →
    (∀ A B, P (imp A B)) → (∀ A, P (all A)) → ∀ A, P A := by
  intro L hf he hr hi ha A
  by_cases hz : A = 0
  · rw [hz]
    exact hf
  · let r := pred A % 3
    have tags : r = 0 ∨ r = 1 ∨ r = 2 := by
      have bound : r < 3 := mod_lt (pred A) 3 (succ_ne_zero 2)
      rcases zero_or_succ_pred r with h0 | h0
      · left
        exact h0
      · rcases zero_or_succ_pred (pred r) with h1 | h1
        · right
          left
          rw [h0, h1]
        · rcases zero_or_succ_pred (pred (pred r)) with h2 | h2
          · right
            right
            rw [h0, h1, h2]
          · rw [h0, h1, h2] at bound
            exact false_elim (succ_ne_zero (pred (pred (pred r))) bound)
    rcases tags with h0 | hrest
    · let q := pred A / 3
      let m := S (Language.relationCount L)
      have outer : 3 * q = pred A := by
        have h := div_mod (pred A) 3
        rw [h0, add_zero] at h
        exact h
      by_cases hq : q % m = 0
      · have inner : m * (q / m) = q := by
          have h := div_mod q m
          rw [hq, add_zero] at h
          exact h
        have form : equal L (unpairLeft (q / m)) (unpairRight (q / m)) = A := by
          rw [equal, pair_unpair, inner, outer, succ_pred A hz]
        rw [← form]
        exact he (unpairLeft (q / m)) (unpairRight (q / m))
      · have symbol : pred (q % m) < Language.relationCount L := by
          have h := and_left (lt_succ (q % m) (Language.relationCount L))
            (mod_lt q m (succ_ne_zero (Language.relationCount L)))
          rw [← succ_pred (q % m) hq] at h
          exact h
        have form : rel L (pred (q % m)) (q / m) = A := by
          rw [rel, succ_pred (q % m) hq, div_mod, outer, succ_pred A hz]
        rw [← form]
        exact hr (pred (q % m)) (q / m) symbol
    · rcases hrest with h1 | h2
      · have hh : head L A = 1 := by
          rw [head, h1]
          rfl
        rw [← imp_arg_of_head_eq_one L A hz hh]
        exact hi (unpairLeft (arg L A)) (unpairRight (arg L A))
      · have hh : head L A = 2 := by
          rw [head, h2]
          rfl
        rw [← all_arg_of_head_eq_two L A hz hh]
        exact ha (arg L A)

/-- Structural induction with a binder depth for a predicate represented by the numerical test
`f`. At depth `d`, implication cases may use either child at depths at most `d`; the quantified
case may use its body at depths at most `S d`. Atomic cases receive their term codes directly.
This allows comparisons between a traversal at its current depth and at a smaller depth. -/
theorem inductionWithDepth_of_bool (P : Nat → Nat → Prop) (f : Nat → Nat → Nat) : ∀ L,
    (∀ A d, ¬ f A d = 0 ↔ P A d) →
    (∀ d, P falsum d) →
    (∀ t u d, P (equal L t u) d) →
    (∀ j xs d, j < Language.relationCount L → P (rel L j xs) d) →
    (∀ A B d, (∀ e, e ≤ d → P A e) → (∀ e, e ≤ d → P B e) → P (imp A B) d) →
    (∀ A d, (∀ e, e ≤ S d → P A e) → P (all A) d) → ∀ A d, P A d := by
  intro L spec hf he hr hi ha
  have step : ∀ A d, (∀ B e, pair B e < pair A d → P B e) → P A d := by
    apply cases (fun A => ∀ d, (∀ B e, pair B e < pair A d → P B e) → P A d) L
    · intro d ih
      exact hf d
    · intro t u d ih
      exact he t u d
    · intro j xs hj d ih
      exact hr j xs d hj
    · intro A B d ih
      exact hi A B d
        (fun e h => ih A e (pair_lt_left A e (imp A B) d (left_lt_imp A B) h))
        (fun e h => ih B e (pair_lt_left B e (imp A B) d (right_lt_imp A B) h))
    · intro A d ih
      apply ha A d
      intro e h
      exact ih A e (lt_of_le_of_lt _ _ _
        (pair_mono A e A (S d) (le_refl A) h) (binder_rank_lt A d))
  have total : ∀ k, P (unpairLeft k) (unpairRight k) := by
    apply strong_induction_of_bool
      (fun k => P (unpairLeft k) (unpairRight k))
      (fun k => f (unpairLeft k) (unpairRight k))
    · intro k
      exact spec (unpairLeft k) (unpairRight k)
    · intro k ih
      apply step (unpairLeft k) (unpairRight k)
      intro B e h
      rw [pair_unpair] at h
      have hp := ih (pair B e) h
      rw [unpairLeft_pair, unpairRight_pair] at hp
      exact hp
  intro A d
  have h := total (pair A d)
  rw [unpairLeft_pair, unpairRight_pair] at h
  exact h

/-- Structural induction on formula codes for a predicate represented by the numerical test `f`.
Implication has one hypothesis for each child, and quantification has one for its body.
Equality and relation cases receive term codes; use term induction when reasoning about them. -/
theorem induction_of_bool (P : Nat → Prop) (f : Nat → Nat) : ∀ L,
    (∀ A, ¬ f A = 0 ↔ P A) → P falsum →
    (∀ t u, P (equal L t u)) →
    (∀ j xs, j < Language.relationCount L → P (rel L j xs)) →
    (∀ A B, P A → P B → P (imp A B)) →
    (∀ A, P A → P (all A)) → ∀ A, P A := by
  intro L spec hf he hr hi ha A
  have h := inductionWithDepth_of_bool (fun A d => P A) (fun A d => f A) L
    (fun A d => spec A) (fun d => hf) (fun t u d => he t u)
    (fun j xs d hj => hr j xs hj)
    (fun A B d hA hB => hi A B (hA d (le_refl d)) (hB d (le_refl d)))
    (fun A d hA => ha A (hA (S d) (le_refl (S d)))) A 0
  exact h

/-- Prove equations on formula codes and binder depths from their constructor cases.
The quantified-body hypothesis is at depth `S d`; implication hypotheses are at depth `d`. -/
theorem induction_eq (f g : Nat → Nat → Nat) : ∀ L,
    (∀ d, f falsum d = g falsum d) →
    (∀ t u d, f (equal L t u) d = g (equal L t u) d) →
    (∀ j xs d, j < Language.relationCount L → f (rel L j xs) d = g (rel L j xs) d) →
    (∀ A B d, f A d = g A d → f B d = g B d → f (imp A B) d = g (imp A B) d) →
    (∀ A d, f A (S d) = g A (S d) → f (all A) d = g (all A) d) →
    ∀ A d, f A d = g A d := by
  intro L hf he hr hi ha
  apply inductionWithDepth_of_bool (fun A d => f A d = g A d)
    (fun A d => eqb (f A d) (g A d)) L
  · intro A d
    constructor
    · intro h
      by_contra hn
      exact h (and_right (eqb_eq_zero (f A d) (g A d)) hn)
    · intro h hn
      exact and_left (eqb_eq_zero (f A d) (g A d)) hn h
  · exact hf
  · exact he
  · exact hr
  · intro A B d hA hB
    exact hi A B d (hA d (le_refl d)) (hB d (le_refl d))
  · intro A d hA
    exact ha A d (hA (S d) (le_refl (S d)))

/--
`Formula.recWithDepth falsum equal rel imp all L A d` processes formula code `A` in language
code `L`, starting at binder depth `d`. Every handler receives the current depth `k`:

- `falsum k` is the value for falsity.
- `equal k t s` handles equality of term codes `t` and `s`.
- `rel k j xs` handles relation symbol index `j`, with a tuple `xs` of term codes of length
  `Language.relationArity L j`.
- `imp k x y` combines the recursive results for the antecedent and consequent at depth `k`.
- `all k x` handles a quantified body whose recursive result `x` is computed at depth `S k`.

The equality and relation handlers receive term codes; they can use `Term.rec` to process them.
-/
def recWithDepth (falsum : Nat → Nat) (equal rel imp : Nat → Nat → Nat → Nat)
    (all : Nat → Nat → Nat) :
    Nat → Nat → Nat → Nat :=
  fun L A d => covrec (fun n history =>
    let A := unpairLeft n;
    let d := unpairRight n;
    ite A
      (ite (head L A)
        (ite (eqb (head L A) 1)
          (imp d (Sequence.rget history (pair (unpairLeft (arg L A)) d))
            (Sequence.rget history (pair (unpairRight (arg L A)) d)))
          (ite (eqb (head L A) 2)
            (all d (Sequence.rget history (pair (arg L A) (S d))))
            (rel d (relationIndex L A) (arg L A))))
        (equal d (unpairLeft (arg L A)) (unpairRight (arg L A)))) (falsum d)) (pair A d)

theorem recWithDepth_falsum (falsum : Nat → Nat) (equal rel imp : Nat → Nat → Nat → Nat)
    (all : Nat → Nat → Nat) : ∀ L d,
    recWithDepth falsum equal rel imp all L Formula.falsum d = falsum d := by
  intro L d
  rw [recWithDepth, covrec, unpairLeft_pair, unpairRight_pair]
  rfl

theorem recWithDepth_equal (falsum : Nat → Nat) (equal rel imp : Nat → Nat → Nat → Nat)
    (all : Nat → Nat → Nat) : ∀ L t s d,
    recWithDepth falsum equal rel imp all L (Formula.equal L t s) d = equal d t s := by
  intro L t s d
  rw [recWithDepth, covrec, unpairLeft_pair, unpairRight_pair]
  change ite (Formula.equal L t s) _ (falsum d) = _
  rw [ite_of_ne_zero _ _ _ (equal_ne_zero L t s), head_equal,
    arg_equal, unpairLeft_pair, unpairRight_pair]
  rfl

theorem recWithDepth_rel (falsum : Nat → Nat) (equal rel imp : Nat → Nat → Nat → Nat)
    (all : Nat → Nat → Nat) : ∀ L j xs d, j < Language.relationCount L →
    recWithDepth falsum equal rel imp all L (Formula.rel L j xs) d = rel d j xs := by
  intro L j xs d hj
  rw [recWithDepth, covrec, unpairLeft_pair, unpairRight_pair]
  change ite (Formula.rel L j xs) _ (falsum d) = _
  rw [ite_of_ne_zero _ _ _ (rel_ne_zero L j xs), head_rel L j xs hj,
    relationIndex_rel L j xs hj, arg_rel L j xs hj]
  rfl

theorem recWithDepth_imp (falsum : Nat → Nat) (equal rel imp : Nat → Nat → Nat → Nat)
    (all : Nat → Nat → Nat) : ∀ L A B d,
    recWithDepth falsum equal rel imp all L (Formula.imp A B) d =
      imp d (recWithDepth falsum equal rel imp all L A d)
        (recWithDepth falsum equal rel imp all L B d) := by
  intro L A B d
  rw [recWithDepth, covrec, unpairLeft_pair, unpairRight_pair]
  change ite (Formula.imp A B) _ (falsum d) = _
  rw [ite_of_ne_zero _ _ _ (imp_ne_zero A B), head_imp, arg_imp,
    unpairLeft_pair, unpairRight_pair]
  change imp d (Sequence.rget _ (pair A d)) (Sequence.rget _ (pair B d)) = _
  rw [Sequence.rget_generate _ (pair A d) (pair (Formula.imp A B) d)
      (pair_lt_left A d (Formula.imp A B) d (left_lt_imp A B) (le_refl d)),
    Sequence.rget_generate _ (pair B d) (pair (Formula.imp A B) d)
      (pair_lt_left B d (Formula.imp A B) d (right_lt_imp A B) (le_refl d))]
  rfl

theorem recWithDepth_all (falsum : Nat → Nat) (equal rel imp : Nat → Nat → Nat → Nat)
    (all : Nat → Nat → Nat) : ∀ L A d,
    recWithDepth falsum equal rel imp all L (Formula.all A) d =
      all d (recWithDepth falsum equal rel imp all L A (S d)) := by
  intro L A d
  rw [recWithDepth, covrec, unpairLeft_pair, unpairRight_pair]
  change ite (Formula.all A) _ (falsum d) = _
  rw [ite_of_ne_zero _ _ _ (all_ne_zero A), head_all, arg_all]
  change all d (Sequence.rget _ (pair A (S d))) = _
  rw [Sequence.rget_generate _ (pair A (S d)) (pair (Formula.all A) d) (binder_rank_lt A d)]
  rfl

/-- Ignoring depth in every handler makes the result independent of the starting depth. -/
theorem recWithDepth_eq_zero_depth (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) :
    ∀ L falsum A d,
    recWithDepth (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
      (fun _ x y => imp x y) (fun _ x => all x) L A d =
    recWithDepth (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
      (fun _ x y => imp x y) (fun _ x => all x) L A 0 := by
  intro L falsum
  let R := recWithDepth (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
    (fun _ x y => imp x y) (fun _ x => all x) L
  apply inductionWithDepth_of_bool (fun A d => R A d = R A 0)
    (fun A d => eqb (R A d) (R A 0)) L
  · intro A d
    constructor
    · intro h
      by_contra hn
      exact h (and_right (eqb_eq_zero _ _) hn)
    · intro h hn
      exact and_left (eqb_eq_zero _ _) hn h
  · intro d
    exact eq_trans
      (recWithDepth_falsum (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
        (fun _ x y => imp x y) (fun _ x => all x) L d)
      (eq_symm (recWithDepth_falsum (fun _ => falsum) (fun _ t s => equal t s)
        (fun _ j xs => rel j xs) (fun _ x y => imp x y) (fun _ x => all x) L 0))
  · intro t s d
    exact eq_trans
      (recWithDepth_equal (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
        (fun _ x y => imp x y) (fun _ x => all x) L t s d)
      (eq_symm (recWithDepth_equal (fun _ => falsum) (fun _ t s => equal t s)
        (fun _ j xs => rel j xs) (fun _ x y => imp x y) (fun _ x => all x) L t s 0))
  · intro j xs d hj
    exact eq_trans
      (recWithDepth_rel (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
        (fun _ x y => imp x y) (fun _ x => all x) L j xs d hj)
      (eq_symm (recWithDepth_rel (fun _ => falsum) (fun _ t s => equal t s)
        (fun _ j xs => rel j xs) (fun _ x y => imp x y) (fun _ x => all x) L j xs 0 hj))
  · intro A B d hA hB
    exact eq_trans
      (recWithDepth_imp (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
        (fun _ x y => imp x y) (fun _ x => all x) L A B d)
      (eq_trans (eq_congr₂ imp (hA d (le_refl d)) (hB d (le_refl d)))
        (eq_symm (recWithDepth_imp (fun _ => falsum) (fun _ t s => equal t s)
          (fun _ j xs => rel j xs) (fun _ x y => imp x y) (fun _ x => all x) L A B 0)))
  · intro A d hA
    have body := eq_trans (hA (S d) (le_refl (S d)))
      (eq_symm (hA 1 (and_right (succ_le_succ 0 d) (zero_le d))))
    exact eq_trans
      (recWithDepth_all (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
        (fun _ x y => imp x y) (fun _ x => all x) L A d)
      (eq_trans (eq_congr all body)
        (eq_symm (recWithDepth_all (fun _ => falsum) (fun _ t s => equal t s)
          (fun _ j xs => rel j xs) (fun _ x y => imp x y) (fun _ x => all x) L A 0)))

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
  recWithDepth (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
    (fun _ x y => imp x y) (fun _ x => all x) L A 0

theorem rec_falsum (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) :
    ∀ L falsum, rec equal rel imp all L falsum Formula.falsum = falsum :=
  fun L falsum => recWithDepth_falsum
    (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
    (fun _ x y => imp x y) (fun _ x => all x) L 0

theorem rec_equal (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) :
    ∀ L falsum t s, rec equal rel imp all L falsum (Formula.equal L t s) = equal t s :=
  fun L falsum t s => recWithDepth_equal
    (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
    (fun _ x y => imp x y) (fun _ x => all x) L t s 0

theorem rec_rel (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) :
    ∀ L falsum j xs, j < Language.relationCount L →
    rec equal rel imp all L falsum (Formula.rel L j xs) = rel j xs :=
  fun L falsum j xs hj => recWithDepth_rel
    (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
    (fun _ x y => imp x y) (fun _ x => all x) L j xs 0 hj

theorem rec_imp (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) : ∀ L falsum A B,
    rec equal rel imp all L falsum (Formula.imp A B) =
      imp (rec equal rel imp all L falsum A) (rec equal rel imp all L falsum B) :=
  fun L falsum A B => recWithDepth_imp
    (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
    (fun _ x y => imp x y) (fun _ x => all x) L A B 0

theorem rec_all (equal rel imp : Nat → Nat → Nat) (all : Nat → Nat) : ∀ L falsum A,
    rec equal rel imp all L falsum (Formula.all A) =
      all (rec equal rel imp all L falsum A) := by
  intro L falsum A
  exact eq_trans (recWithDepth_all
    (fun _ => falsum) (fun _ t s => equal t s) (fun _ j xs => rel j xs)
    (fun _ x y => imp x y) (fun _ x => all x) L A 0)
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
`Formula.substWithDepth f L A d` replaces variables in formula code `A` in language code `L`,
starting at binder depth `d`. `f k i` supplies a term code for variable index `i` at the
current depth `k`. Each quantifier increases `k` by one. The replacement function `f`
determines how bound variables are treated.
-/
def substWithDepth (f : Nat → Nat → Nat) : Nat → Nat → Nat → Nat := fun L =>
  recWithDepth (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L

theorem substWithDepth_falsum (f : Nat → Nat → Nat) : ∀ L d, substWithDepth f L falsum d = falsum :=
  fun L d => recWithDepth_falsum (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L d

theorem substWithDepth_equal (f : Nat → Nat → Nat) : ∀ L t s d,
    substWithDepth f L (equal L t s) d = equal L (Term.subst (f d) L t) (Term.subst (f d) L s) :=
  fun L t s d => recWithDepth_equal (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L t s d

theorem substWithDepth_rel (f : Nat → Nat → Nat) : ∀ L j xs d, j < Language.relationCount L →
    substWithDepth f L (rel L j xs) d =
      rel L j (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs) :=
  fun L j xs d hj => recWithDepth_rel (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L j xs d hj

theorem substWithDepth_imp (f : Nat → Nat → Nat) : ∀ L A B d,
    substWithDepth f L (imp A B) d = imp (substWithDepth f L A d) (substWithDepth f L B d) :=
  fun L A B d => recWithDepth_imp (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L A B d

theorem substWithDepth_all (f : Nat → Nat → Nat) : ∀ L A d,
    substWithDepth f L (all A) d = all (substWithDepth f L A (S d)) :=
  fun L A d => recWithDepth_all (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L A d

/--
`Formula.instantiateAt L k A t` substitutes term code `t` for surrounding position `k` in
formula code `A`, in language code `L`. Indices referring to inner binders and earlier
surrounding positions are preserved; `t` is shifted beneath binders, and later positions
move down by one.
-/
def instantiateAt : Nat → Nat → Nat → Nat → Nat :=
  fun L k A t => substWithDepth (Term.instantiateAt L k t) L A 0

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
  substWithDepth (fun d n => Term.var L (ite (ltb n d) n (S n))) L A 0

/--
`Formula.successorInstance L successor A` replaces surrounding position `0` in formula code `A`
by its successor, preserving other positions. `L` is a language code, and `successor`
is a function symbol index below `Language.functionCount L` with arity `1`.
-/
def successorInstance : Nat → Nat → Nat → Nat := fun L successor A =>
  substWithDepth
    (fun d n => ite (eqb n d) (Term.app L successor (Term.var L n)) (Term.var L n)) L A 0

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

/-- `Formula.Closed L A` states that formula code `A` has no free variable positions in
language code `L`. Such a formula is a sentence. -/
def Closed : Nat → Nat → QFProp := fun L A => bound L A = 0

/-- `Formula.isClosed L A` returns `1` when `Formula.Closed L A` holds, and `0` otherwise. -/
def isClosed : Nat → Nat → Nat := fun L A => eqb (bound L A) 0

theorem isClosed_eq_one : ∀ L A, isClosed L A = 1 ↔ Closed L A :=
  fun L A => eqb_eq_one (bound L A) 0

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
