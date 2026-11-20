module

public import LeanPRA.Library.FOL.Common.Language
public import LeanPRA.Library.Nat.Tuple

/-!
# First-order syntax

Terms and formulas are encoded in `Nat`. For a fixed language `L`, every number has an
interpretation as each kind of syntax. Symbol indices start at zero within each symbol group.

Variables use de Bruijn indices: `0` refers to the nearest binder, with larger indices counting
outward. Beneath `d` binders, an index `i ≥ d` refers to surrounding position `i - d`.
Formulas have no fixed scope.
-/

@[expose] public section

pra

namespace FOL

open Language

/-! ## Constructors

For terms, let `c = Language.constants L`, `p = Language.functionCount L`, and
`s = S (p + Language.functionFamilyCount L)`. The stride `k` is `s` when there are no constant
families and `s + 1` otherwise.

- `Term.const L j` is encoded as `j` for an ordinary constant `j < c`. For member `i` of constant
  family `b`, let `q = Language.constantFamilyCount L * i + b`. Its symbol index is `c + q`,
  and its term code is `c + (k * q + s)`.
- `Term.var L i` is encoded as `c + k * i`.
- `Term.app L j args` is encoded as `c + (k * args + S j)` for an ordinary function `j < p`.
  For `j = Language.functionFamilyMember L b i`, its code is `c + (k * pair i args + S (p + b))`.

For formulas, let `q = Language.relationCount L` and `m = S (q + Language.relationFamilyCount L)`.

- `Formula.falsum` is encoded as `0`.
- `Formula.equal L t u` is encoded as `S (3 * (m * pair t u))`.
- `Formula.rel L j args` is encoded as `S (3 * (m * args + S j))` for an ordinary relation `j < q`.
  For `j = Language.relationFamilyMember L b i`, its code is
  `S (3 * (m * pair i args + S (q + b)))`.
- `Formula.imp A B` is encoded as `S (3 * pair A B + 1)`.
- `Formula.all A` is encoded as `S (3 * A + 2)`.

Here `t`, `u` are term codes, and `A`, `B` are formula codes. The tuple `args` contains one term
code per argument. One argument has its own code, and a longer
tuple pairs its first argument with the remaining tuple. When the language has no indexed families,
these equations give the original finite-language codes.
-/

namespace Term

/--
`Term.const L j` encodes constant symbol `j` in language code `L`,
for `Language.IsConstant L j`.
-/
def const : Nat → Nat → Nat := fun L j =>
  let c := constants L;
  let s := S (functionCount L + functionFamilyCount L);
  ite (ltb j c) j (c + (S s * (j - c) + s))

theorem const_of_lt : ∀ L j, j < constants L → const L j = j := by
  intro L j hj
  rw [const, and_right (ltb_eq_one j (constants L)) hj, ite_succ]

/--
`Term.var L i` encodes variable index `i` in language code `L`. Indices start at zero;
under `d` surrounding binders, `i < d` refers to one of those binders and `i - d` otherwise
identifies a position in the surrounding context. Indices count outward from the nearest binder.
-/
def var : Nat → Nat → Nat := fun L i =>
  constants L + S (functionCount L + functionFamilyCount L + isPos (constantFamilyCount L)) * i

/--
`Term.app L j args` encodes an application of function symbol `j` in language code `L`,
for `Language.IsFunction L j`. The tuple `args` contains `Language.functionSymbolArity L j`
term codes.
-/
def app : Nat → Nat → Nat → Nat := fun L j args =>
  let p := functionCount L;
  let f := functionFamilyCount L;
  let b := ite (ltb j p) j (p + ((j - p) % f));
  let k := (j - p) / f;
  let xs := ite (ltb b p) args (pair k args);
  constants L + (S (p + f + isPos (constantFamilyCount L)) * xs + S b)

end Term

namespace Formula

/-- `Formula.falsum` is the formula code for falsity (`0`). -/
def falsum : Nat := 0

/--
`Formula.equal L t u` encodes the equality formula between term codes `t` and `u`
in language code `L`.
-/
def equal : Nat → Nat → Nat → Nat :=
  fun L t u => S (3 * (S (relationCount L + relationFamilyCount L) * pair t u))

/--
`Formula.rel L j args` encodes the atomic formula for relation symbol `j` in language code `L`,
for `Language.IsRelation L j`. The tuple `args` contains `Language.relationSymbolArity L j`
term codes.
-/
def rel : Nat → Nat → Nat → Nat := fun L j args =>
  let p := relationCount L;
  let f := relationFamilyCount L;
  let b := ite (ltb j p) j (p + ((j - p) % f));
  let k := (j - p) / f;
  let xs := ite (ltb b p) args (pair k args);
  S (3 * (S (p + f) * xs + S b))

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

end Formula

/-! ## Destructing terms

`Term.head` and `Term.arg` recover a nonconstant term's constructor and arguments.

- `Term.cases` recovers the constructor represented by any term code.
- `Term.induction_of_bool` proves predicates represented by numerical tests, using hypotheses for
  the immediate children.
- `Term.induction_eq` specializes this principle to equations.
-/

namespace Term

/--
`Term.head L t` reads the head of a nonconstant term code `t` in language code `L`.
It returns zero for a variable or `S j` for an application of function symbol `j`.
-/
def head : Nat → Nat → Nat := fun L t =>
  let m := S (functionCount L + functionFamilyCount L + isPos (constantFamilyCount L));
  let u := t - constants L;
  let b := pred (u % m);
  let xs := u / m;
  let k := unpairLeft xs;
  let j := ite (ltb b (functionCount L)) b (functionFamilyMember L (b - functionCount L) k);
  ite (u % m) (S j) 0

/--
`Term.arg L t` reads the variable index or argument tuple from a nonconstant term code `t`
in language code `L`.
-/
def arg : Nat → Nat → Nat := fun L t =>
  let m := S (functionCount L + functionFamilyCount L + isPos (constantFamilyCount L));
  let u := t - constants L;
  let b := pred (u % m);
  let xs := u / m;
  let args := ite (ltb b (functionCount L)) xs (unpairRight xs);
  ite (u % m) args xs

theorem constants_le_var : ∀ L i, constants L ≤ var L i :=
  fun L i => le_add_right (constants L) _

theorem constants_le_app : ∀ L j args, constants L ≤ app L j args :=
  fun L j args => le_add_right (constants L) _

theorem head_var : ∀ L i, head L (var L i) = 0 := by
  intro L i
  rw [head, var, add_sub_self_left, mod_mul, ite_zero]

theorem arg_var : ∀ L i, arg L (var L i) = i := by
  intro L i
  rw [arg, var, add_sub_self_left, mod_mul, ite_zero, div_mul _ _ (succ_ne_zero _)]

theorem head_app : ∀ L j args, IsFunction L j → head L (app L j args) = S j := by
  intro L j args hj
  let p := functionCount L
  let f := functionFamilyCount L
  have hb := and_right (succ_le_succ _ _) (lt_of_lt_of_le _ _ _ hj
    (le_add_right (p + f) (isPos (constantFamilyCount L))))
  rw [head, app, add_sub_self_left, mod_mul_add_of_lt _ _ _ (succ_ne_zero _) hb,
    div_mul_add_of_lt _ _ _ (succ_ne_zero _) hb, ite_succ, pred_succ]
  by_cases ho : j < p
  · rw [and_right (ltb_eq_one j p) ho, ite_succ, and_right (ltb_eq_one j p) ho, ite_succ]
  · have hle := le_of_not_lt p j ho
    rw [ltb_eq_zero_of_ge j p hle, ite_zero, ltb_eq_zero_of_ge _ _ (le_add_right p _),
      ite_zero, ite_zero, add_sub_self_left]
    rw [unpairLeft_pair]
    change S (p + (f * ((j - p) / f) + (j - p) % f)) = S j
    rw [div_mod, add_comm, sub_add_cancel_of_le j p hle]

theorem arg_app : ∀ L j args, IsFunction L j →
    arg L (app L j args) = args := by
  intro L j args hj
  let p := functionCount L
  let f := functionFamilyCount L
  have hb := and_right (succ_le_succ _ _) (lt_of_lt_of_le _ _ _ hj
    (le_add_right (p + f) (isPos (constantFamilyCount L))))
  rw [arg, app, add_sub_self_left, mod_mul_add_of_lt _ _ _ (succ_ne_zero _) hb,
    div_mul_add_of_lt _ _ _ (succ_ne_zero _) hb, ite_succ, pred_succ]
  let b := ite (ltb j p) j (p + ((j - p) % f))
  by_cases ho : b < p
  · rw [and_right (ltb_eq_one b p) ho, ite_succ, ite_succ]
  · rw [ltb_eq_zero_of_ge b p (le_of_not_lt p b ho), ite_zero, ite_zero, unpairRight_pair]

theorem args_lt_app : ∀ L j args, args < app L j args := by
  intro L j args
  let p := functionCount L
  let f := functionFamilyCount L
  let b := ite (ltb j p) j (p + ((j - p) % f))
  let m := S (p + f + isPos (constantFamilyCount L))
  let k := (j - p) / f
  let xs := ite (ltb b p) args (pair k args)
  have hp := le_ite (ltb b p) args args (pair k args) (le_refl args) (right_le_pair k args)
  have hm := le_mul_of_pos xs m (succ_ne_zero _)
  have h := le_trans _ _ _ (le_trans _ _ _ hp hm) (le_add_right (m * xs) b)
  exact lt_of_lt_of_le _ _ _ (and_right (lt_succ _ _) h) (le_add_left (constants L) _)

theorem var_mono : ∀ L i d, var L i ≤ var L (i + d) := by
  intro L i d
  exact add_le_add_left _ _ (constants L)
    (mul_le_mul_left i (i + d) _ (le_add_right i d))

theorem app_mono : ∀ L j xs ys, xs ≤ ys → app L j xs ≤ app L j ys := by
  intro L j xs ys h
  apply add_le_add_left
  apply add_le_add_right
  apply mul_le_mul_left
  apply ite_mono
  · exact h
  exact pair_mono _ _ _ _ (le_refl _) h

/-- Every number denotes a constant, variable, or application with a valid symbol index. -/
theorem cases (P : Nat → Prop) : ∀ L,
    (∀ j, IsConstant L j → P (const L j)) →
    (∀ i, P (var L i)) →
    (∀ j args, IsFunction L j → P (app L j args)) → ∀ t, P t := by
  intro L hc hv ha t
  by_cases ht : t < constants L
  · rw [← const_of_lt L t ht]
    exact hc t (isConstant_of_lt L t ht)
  · have hle := le_of_not_lt (constants L) t ht
    let p := functionCount L
    let f := functionFamilyCount L
    let m := S (p + f + isPos (constantFamilyCount L))
    let u := t - constants L
    have hdiv := div_mod u m
    by_cases hh : u % m = 0
    · have form : var L (u / m) = t := by
        rw [hh, add_zero] at hdiv
        rw [var, hdiv, add_comm, sub_add_cancel_of_le t (constants L) hle]
      rw [← form]
      exact hv (u / m)
    · by_cases h : u % m < S (p + f)
      · let b := pred (u % m)
        let v := u / m
        let k := unpairLeft v
        let j := ite (ltb b p) b (functionFamilyMember L (b - p) k)
        have hb : b < p + f := by
          rw [← succ_pred (u % m) hh] at h
          exact and_left (succ_le_succ _ _) h
        have hentry : ite (ltb j p) j (p + ((j - p) % f)) = b :=
          ite_ltb_mod_eq_self_of_lt_add p f b k hb
        let xs := ite (ltb b p) v (unpairRight v)
        have form : app L j xs = t := by
          rw [app, hentry]
          have hx : ite (ltb b p) xs (pair ((j - p) / f) xs) = v := by
            by_cases ho : b < p
            · rw [and_right (ltb_eq_one b p) ho, ite_succ, ite_succ]
            · have hle := le_of_not_lt p b ho
              have hf : b - p < f := and_right (sub_lt_iff b p f hle) hb
              have hnz := ne_zero_of_pos f (lt_of_le_of_lt 0 _ f (zero_le _) hf)
              rw [ltb_eq_zero_of_ge b p hle, ite_zero, ite_zero, functionFamilyMember,
                add_sub_self_left, div_mul_add_of_lt f _ (b - p) hnz hf]
              exact pair_unpair v
          rw [hx, succ_pred (u % m) hh, hdiv, add_comm, sub_add_cancel_of_le t (constants L) hle]
        rw [← form]
        apply ha
        rw [IsFunction, hentry]
        exact hb
      · have hm := mod_lt u m (succ_ne_zero _)
        have hC : ¬ constantFamilyCount L = 0 := by
          intro hz
          have he : m = S (p + f) := by
            change S (p + f + isPos (constantFamilyCount L)) = S (p + f)
            rw [hz, isPos_zero, add_zero]
          exact h (eq_subst (fun n => u % m < n) he hm)
        have hp := and_right (isPos_eq_one _) hC
        have hm' : m = S (S (p + f)) := by
          change S (p + f + isPos (constantFamilyCount L)) = S (S (p + f))
          rw [hp, add_succ, add_zero]
        have hr : u % m = S (p + f) := by
          have he := eq_subst (fun n => u % m < n) hm' hm
          exact le_antisymm _ _ (and_left (lt_succ _ _) he) (le_of_not_lt _ _ h)
        let j := constants L + u / m
        have form : const L j = t := by
          rw [const, ltb_eq_zero_of_ge _ _ (le_add_right (constants L) (u / m)), ite_zero,
            add_sub_self_left]
          have hd := hdiv
          rw [hr] at hd
          rw [← hm', hd, add_comm, sub_add_cancel_of_le t (constants L) hle]
        rw [← form]
        apply hc j
        right
        exact hC

/-- Structural induction on term codes for a predicate represented by the numerical test `f`.
The application case assumes the predicate for each component of its argument tuple. -/
theorem induction_of_bool (P : Nat → Prop) (f : Nat → Nat) : ∀ L,
    (∀ t, ¬ f t = 0 ↔ P t) →
    (∀ j, IsConstant L j → P (const L j)) →
    (∀ i, P (var L i)) →
    (∀ j args, IsFunction L j →
      (∀ i, i < functionSymbolArity L j → P (Tuple.get (functionSymbolArity L j) args i)) →
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
    have h := args_lt_app L j args
    exact ih (Tuple.get (functionSymbolArity L j) args i)
      (lt_of_le_of_lt _ args _ (Tuple.get_le (functionSymbolArity L j) args i) h)

/-- Prove equations on term codes from their constant, variable, and application cases. -/
theorem induction_eq (f g : Nat → Nat) : ∀ L,
    (∀ j, IsConstant L j → f (const L j) = g (const L j)) →
    (∀ i, f (var L i) = g (var L i)) →
    (∀ j args, IsFunction L j →
      (∀ i, i < Language.functionSymbolArity L j →
        f (Tuple.get (Language.functionSymbolArity L j) args i) =
          g (Tuple.get (Language.functionSymbolArity L j) args i)) →
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

/-! ## Destructing formulas

For positive formulas, the predecessor's remainder modulo `3` distinguishes an atom from an
implication or a universal quantifier. Let
`m = S (Language.relationCount L + Language.relationFamilyCount L)`.
For an atom, dividing the predecessor by `3` and taking the remainder modulo `m` gives zero for
equality or the successor of the relation entry. For a relation family, unpairing the quotient
recovers the member number and the argument tuple. `Formula.head`, `Formula.arg`, and
`Formula.relationIndex` recover the constructor, arguments, and relation symbol.

- `Formula.cases` recovers the constructor represented by any formula code.
-/

namespace Formula

/--
`Formula.head L A` reads the head code of positive formula code `A` in language code `L`:
`0` for equality, `1` for implication, `2` for universal quantification, and `3` for a relation.
Falsity is recognized by `A = 0`.
-/
def head : Nat → Nat → Nat := fun L A =>
  ite (pred A % 3) (pred A % 3)
    (ite ((pred A / 3) % S (relationCount L + relationFamilyCount L)) 3 0)

/--
`Formula.arg L A` reads the arguments of positive formula code `A` in language code `L`:
a pair of term codes for equality, a tuple code of term codes for a relation, a pair of formula
codes for implication, or the body formula code for universal quantification.
-/
def arg : Nat → Nat → Nat := fun L A =>
  let u := pred A / 3;
  let m := S (relationCount L + relationFamilyCount L);
  let b := pred (u % m);
  let xs := u / m;
  ite (pred A % 3) u
    (ite (u % m) (ite (ltb b (relationCount L)) xs (unpairRight xs)) xs)

/--
`Formula.relationIndex L A` reads the relation symbol index from relation formula code `A`
in language code `L`. Use with `Formula.head L A = 3` and `0 < A`.
-/
def relationIndex : Nat → Nat → Nat := fun L A =>
  let u := pred A / 3;
  let m := S (relationCount L + relationFamilyCount L);
  let b := pred (u % m);
  ite (ltb b (relationCount L)) b
    (relationFamilyMember L (b - relationCount L) (unpairLeft (u / m)))

theorem equal_ne_zero : ∀ L t u, ¬ equal L t u = 0 :=
  fun L t u => succ_ne_zero _

theorem rel_ne_zero : ∀ L j args, ¬ rel L j args = 0 :=
  fun L j args => succ_ne_zero _

theorem imp_ne_zero : ∀ A B, ¬ imp A B = 0 := fun A B => succ_ne_zero (3 * pair A B + 1)

theorem all_ne_zero : ∀ A, ¬ all A = 0 := fun A => succ_ne_zero (3 * A + 2)

theorem head_equal : ∀ L t u, head L (equal L t u) = 0 := by
  intro L t u
  rw [head, equal, pred_succ, mod_mul, div_mul 3 _ (succ_ne_zero 2),
    mod_mul, ite_zero, ite_zero]

theorem arg_equal : ∀ L t u, arg L (equal L t u) = pair t u := by
  intro L t u
  rw [arg, equal, pred_succ, mod_mul,
    div_mul 3 _ (succ_ne_zero 2), mod_mul, div_mul _ _ (succ_ne_zero _),
    ite_zero, ite_zero]

theorem head_rel : ∀ L j args, IsRelation L j → head L (rel L j args) = 3 := by
  intro L j args h
  rw [head, rel, pred_succ, mod_mul, ite_zero, div_mul 3 _ (succ_ne_zero 2),
    mod_mul_add_of_lt _ _ _ (succ_ne_zero _) (and_right (succ_le_succ _ _) h), ite_succ]

theorem arg_rel : ∀ L j args, IsRelation L j → arg L (rel L j args) = args := by
  intro L j args h
  let p := relationCount L
  let f := relationFamilyCount L
  have hb := and_right (succ_le_succ _ _) h
  rw [arg, rel, pred_succ, mod_mul, ite_zero, div_mul 3 _ (succ_ne_zero 2),
    mod_mul_add_of_lt _ _ _ (succ_ne_zero _) hb, ite_succ, pred_succ,
    div_mul_add_of_lt _ _ _ (succ_ne_zero _) hb]
  let b := ite (ltb j p) j (p + ((j - p) % f))
  by_cases ho : b < p
  · rw [and_right (ltb_eq_one b p) ho, ite_succ, ite_succ]
  · rw [ltb_eq_zero_of_ge b p (le_of_not_lt p b ho), ite_zero, ite_zero, unpairRight_pair]

theorem relationIndex_rel : ∀ L j args, IsRelation L j →
    relationIndex L (rel L j args) = j := by
  intro L j args h
  let p := relationCount L
  let f := relationFamilyCount L
  have hb := and_right (succ_le_succ _ _) h
  rw [relationIndex, rel, pred_succ, div_mul 3 _ (succ_ne_zero 2),
    mod_mul_add_of_lt _ _ _ (succ_ne_zero _) hb, pred_succ,
    div_mul_add_of_lt _ _ _ (succ_ne_zero _) hb]
  by_cases ho : j < p
  · rw [and_right (ltb_eq_one j p) ho, ite_succ, and_right (ltb_eq_one j p) ho, ite_succ]
  · have hle := le_of_not_lt p j ho
    rw [ltb_eq_zero_of_ge j p hle, ite_zero, ltb_eq_zero_of_ge _ _ (le_add_right p _),
      ite_zero, ite_zero, add_sub_self_left]
    rw [unpairLeft_pair]
    change p + (f * ((j - p) / f) + (j - p) % f) = j
    rw [div_mod, add_comm, sub_add_cancel_of_le j p hle]

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
  let m := S (relationCount L + relationFamilyCount L)
  change t ≤ S (3 * (m * pair t u))
  exact le_trans _ _ _ (left_le_pair t u)
    (le_trans _ _ _
      (le_mul_of_pos (pair t u) m (succ_ne_zero _))
      (le_trans _ _ _
        (le_mul_of_pos (m * pair t u) 3 (succ_ne_zero 2))
        (le_succ_self (3 * (m * pair t u)))))

theorem le_equal_right : ∀ L t u, u ≤ equal L t u := by
  intro L t u
  let m := S (relationCount L + relationFamilyCount L)
  change u ≤ S (3 * (m * pair t u))
  exact le_trans _ _ _ (right_le_pair t u)
    (le_trans _ _ _
      (le_mul_of_pos (pair t u) m (succ_ne_zero _))
      (le_trans _ _ _
        (le_mul_of_pos (m * pair t u) 3 (succ_ne_zero 2))
        (le_succ_self (3 * (m * pair t u)))))

theorem args_le_rel : ∀ L j xs, xs ≤ rel L j xs := by
  intro L j xs
  let p := relationCount L
  let f := relationFamilyCount L
  let b := ite (ltb j p) j (p + ((j - p) % f))
  let m := S (p + f)
  let k := (j - p) / f
  let args := ite (ltb b p) xs (pair k xs)
  have hp := le_ite (ltb b p) xs xs (pair k xs) (le_refl xs) (right_le_pair k xs)
  have hm := le_mul_of_pos args m (succ_ne_zero _)
  have ha := le_add_right (m * args) (S b)
  have ht := le_mul_of_pos
    (m * args + S b) 3 (succ_ne_zero 2)
  exact le_trans _ _ _ hp (le_trans _ _ _ hm
    (le_trans _ _ _ ha (le_trans _ _ _ ht (le_succ_self _))))

/-- Every number denotes falsity, an atomic formula, an implication, or a quantifier. -/
theorem cases (P : Nat → Prop) : ∀ L, P falsum →
    (∀ t u, P (equal L t u)) →
    (∀ j xs, IsRelation L j → P (rel L j xs)) →
    (∀ A B, P (imp A B)) → (∀ A, P (all A)) → ∀ A, P A := by
  intro L hf he hr hi ha A
  by_cases hz : A = 0
  · rw [hz]
    exact hf
  · let r := pred A % 3
    have residues : r = 0 ∨ r = 1 ∨ r = 2 := by
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
    rcases residues with h0 | hrest
    · let q := pred A / 3
      let p := relationCount L
      let f := relationFamilyCount L
      let m := S (p + f)
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
      · let b := pred (q % m)
        let v := q / m
        let j := ite (ltb b p) b
          (relationFamilyMember L (b - p) (unpairLeft v))
        have hb : b < p + f := by
          have h := mod_lt q m (succ_ne_zero _)
          rw [← succ_pred (q % m) hq] at h
          exact and_left (succ_le_succ _ _) h
        have hentry : ite (ltb j p) j (p + ((j - p) % f)) = b :=
          ite_ltb_mod_eq_self_of_lt_add p f b (unpairLeft v) hb
        let xs := ite (ltb b p) v (unpairRight v)
        have form : rel L j xs = A := by
          rw [rel, hentry]
          have hx : ite (ltb b p) xs
              (pair ((j - p) / f) xs) = v := by
            by_cases ho : b < p
            · rw [and_right (ltb_eq_one b p) ho, ite_succ, ite_succ]
            · have hle := le_of_not_lt p b ho
              have hf : b - p < f := and_right (sub_lt_iff b p f hle) hb
              have hnz := ne_zero_of_pos f (lt_of_le_of_lt 0 _ f (zero_le _) hf)
              rw [ltb_eq_zero_of_ge b p hle, ite_zero, ite_zero, relationFamilyMember,
                add_sub_self_left, div_mul_add_of_lt f _ (b - p) hnz hf]
              exact pair_unpair v
          rw [hx, succ_pred (q % m) hq, div_mod, outer, succ_pred A hz]
        rw [← form]
        apply hr
        rw [IsRelation, hentry]
        exact hb
    · let q := pred A / 3
      have h := div_mod (pred A) 3
      rcases hrest with h1 | h2
      · rw [h1] at h
        have form : imp (unpairLeft q) (unpairRight q) = A := by
          rw [imp, pair_unpair, h, succ_pred A hz]
        rw [← form]
        exact hi (unpairLeft q) (unpairRight q)
      · rw [h2] at h
        have form : all q = A := by
          rw [all, h, succ_pred A hz]
        rw [← form]
        exact ha q

theorem imp_arg_of_head_eq_one : ∀ L A, ¬ A = 0 → head L A = 1 →
    imp (unpairLeft (arg L A)) (unpairRight (arg L A)) = A := by
  intro L
  apply cases (fun A => ¬ A = 0 → head L A = 1 →
    imp (unpairLeft (arg L A)) (unpairRight (arg L A)) = A) L
  · intro hz hh
    exact false_elim (hz rfl)
  · intro t u hz hh
    rw [head_equal] at hh
    exact false_elim (zero_ne_succ 0 hh)
  · intro j xs hj hz hh
    rw [head_rel L j xs hj] at hh
    exact false_elim (succ_ne_zero 1 (eq_congr pred hh))
  · intro A B hz hh
    rw [arg_imp, unpairLeft_pair, unpairRight_pair]
  · intro A hz hh
    rw [head_all] at hh
    exact false_elim (succ_ne_zero 0 (eq_congr pred hh))

theorem all_arg_of_head_eq_two : ∀ L A, ¬ A = 0 → head L A = 2 → all (arg L A) = A := by
  intro L
  apply cases (fun A => ¬ A = 0 → head L A = 2 → all (arg L A) = A) L
  · intro hz hh
    exact false_elim (hz rfl)
  · intro t u hz hh
    rw [head_equal] at hh
    exact false_elim (zero_ne_succ 1 hh)
  · intro j xs hj hz hh
    rw [head_rel L j xs hj] at hh
    exact false_elim (succ_ne_zero 0 (eq_congr pred (eq_congr pred hh)))
  · intro A B hz hh
    rw [head_imp] at hh
    exact false_elim (zero_ne_succ 0 (eq_congr pred hh))
  · intro A hz hh
    rw [arg_all]

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

/-! ## Recursion

- `Term.rec` processes variables, constants, and function applications by numerical recursion,
  passing an exact-arity tuple of child results to the application handler.
- `Formula.induction_of_bool` proves predicates represented by numerical tests, using hypotheses for
  the immediate children.
- `Formula.inductionWithDepth_of_bool` also tracks binder depth, allowing smaller child depths.
- `Formula.induction_eq` specializes induction to equations and tracks binder depth.
- `Formula.recWithDepth` makes the binder depth available to every formula handler.
  Its paired recursion rank decreases when entering a quantified body, even though depth increases.
- `Formula.rec` processes the same cases with handlers that ignore binder depth.
-/

namespace Term

/--
`Term.rec var const app L t` processes term code `t` in language code `L` to a numerical value:

- `var i` handles variable index `i`.
- `const j` handles constant symbol index `j`.
- `app j xs` handles function symbol index `j`, with `xs` a tuple of child results of length
  `Language.functionSymbolArity L j`.
-/
def rec (var const : Nat → Nat) (app : Nat → Nat → Nat) : Nat → Nat → Nat :=
  fun L => covrec (fun t history =>
    let c := Language.constants L;
    let s := S (functionCount L + functionFamilyCount L);
    let m := S (functionCount L + functionFamilyCount L + isPos (constantFamilyCount L));
    ite (ltb t c) (const t)
      (ite (eqb ((t - c) % m) s) (const (c + (t - c) / m))
        (ite (head L t)
          (app (pred (head L t)) (Tuple.map (fun a => Sequence.rget history a)
            (Language.functionSymbolArity L (pred (head L t))) (arg L t)))
          (var (arg L t)))))

theorem rec_const (var const : Nat → Nat) (app : Nat → Nat → Nat) :
    ∀ L j, IsConstant L j → rec var const app L (Term.const L j) = const j := by
  intro L j hj
  by_cases ho : j < constants L
  · rw [const_of_lt L j ho, rec, covrec, and_right (ltb_eq_one j (constants L)) ho, ite_succ]
  · have hC : ¬ constantFamilyCount L = 0 := by
      rcases hj with h | h
      · exact false_elim (ho h)
      · exact h
    let c := constants L
    let s := S (functionCount L + functionFamilyCount L)
    have hle := le_of_not_lt c j ho
    have hc := le_add_right c (S s * (j - c) + s)
    have hm : S (functionCount L + functionFamilyCount L + isPos (constantFamilyCount L)) =
        S s := by
      rw [and_right (isPos_eq_one _) hC, add_succ, add_zero]
    rw [Term.const, ltb_eq_zero_of_ge j c hle, ite_zero, rec, covrec,
      ltb_eq_zero_of_ge _ _ hc, ite_zero, add_sub_self_left, hm,
      mod_mul_add_of_lt _ _ s (succ_ne_zero _) (lt_succ_self s),
      eqb_self, ite_succ, div_mul_add_of_lt _ _ s (succ_ne_zero _) (lt_succ_self s),
      add_comm, sub_add_cancel_of_le j c hle]

theorem rec_var (var const : Nat → Nat) (app : Nat → Nat → Nat) :
    ∀ L i, rec var const app L (Term.var L i) = var i := by
  intro L i
  rw [rec, covrec,
    ltb_eq_zero_of_ge (Term.var L i) (Language.constants L) (constants_le_var L i),
    head_var, arg_var, Term.var, add_sub_self_left, mod_mul,
    and_right (eqb_eq_zero 0 _) (zero_ne_succ _)]
  rfl

theorem rec_app (var const : Nat → Nat) (app : Nat → Nat → Nat) :
    ∀ L j args, IsFunction L j →
    rec var const app L (Term.app L j args) =
      app j (Tuple.map (rec var const app L) (Language.functionSymbolArity L j) args) := by
  intro L j args hj
  let p := functionCount L
  let f := functionFamilyCount L
  let b := ite (ltb j p) j (p + ((j - p) % f))
  let m := S (p + f + isPos (constantFamilyCount L))
  have hb : S b < m := and_right (succ_le_succ _ _) (lt_of_lt_of_le _ _ _ hj
    (le_add_right (p + f) (isPos (constantFamilyCount L))))
  have hr : (Term.app L j args - constants L) % m = S b := by
    rw [Term.app, add_sub_self_left, mod_mul_add_of_lt _ _ _ (succ_ne_zero _) hb]
  have hne : ¬ S b = S (p + f) := by
    intro h
    have he : b = p + f := succ_inj h
    exact not_lt_self _ (eq_subst (fun n => n < p + f) he hj)
  rw [rec, covrec,
    ltb_eq_zero_of_ge (Term.app L j args) (Language.constants L) (constants_le_app L j args),
    hr, and_right (eqb_eq_zero _ _) hne, ite_zero, head_app L j args hj, arg_app L j args hj,
    ite_zero, ite_succ, pred_succ]
  apply eq_congr (app j)
  apply Tuple.map_congr_of_get_eq _ _
  intro i hi
  have h := lt_of_le_of_lt _ args _ (Tuple.get_le (functionSymbolArity L j) args i)
    (args_lt_app L j args)
  rw [Sequence.rget_generate _ (Tuple.get (functionSymbolArity L j) args i) (Term.app L j args) h]
  rfl

theorem rec_app_one (var const : Nat → Nat) (app : Nat → Nat → Nat) :
    ∀ L j x, IsFunction L j → Language.functionSymbolArity L j = 1 →
    rec var const app L (Term.app L j x) = app j (rec var const app L x) := by
  intro L j x hj ha
  rw [rec_app var const app L j x hj, ha, Tuple.map_one _]

theorem rec_app_two (var const : Nat → Nat) (app : Nat → Nat → Nat) :
    ∀ L j x y, IsFunction L j → Language.functionSymbolArity L j = 2 →
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

/-- Structural induction with a binder depth for a predicate represented by the numerical test
`f`. At depth `d`, implication cases may use either child at depths at most `d`; the quantified
case may use its body at depths at most `S d`. Atomic cases receive their term codes directly.
This allows comparisons between a traversal at its current depth and at a smaller depth. -/
theorem inductionWithDepth_of_bool (P : Nat → Nat → Prop) (f : Nat → Nat → Nat) : ∀ L,
    (∀ A d, ¬ f A d = 0 ↔ P A d) →
    (∀ d, P falsum d) →
    (∀ t u d, P (equal L t u) d) →
    (∀ j xs d, IsRelation L j → P (rel L j xs) d) →
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
    (∀ j xs, IsRelation L j → P (rel L j xs)) →
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
    (∀ j xs d, IsRelation L j → f (rel L j xs) d = g (rel L j xs) d) →
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
  `Language.relationSymbolArity L j`.
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
    (all : Nat → Nat → Nat) : ∀ L j xs d, IsRelation L j →
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
    ∀ L falsum j xs, IsRelation L j →
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

/-! ## Substitution

- `Term.subst` and `Formula.substWithDepth` replace variables, tracking depth beneath quantifiers.
- `Formula.instantiateAt` and `Formula.instantiate` substitute a term into a surrounding
  variable position or quantifier body, lifting it beneath inner binders and lowering later indices.
- `Term.bound` and `Formula.bound` give the number of surrounding variable positions
  needed by the syntax.
- `Formula.Closed` states that a formula has no free variable positions;
  `Formula.isClosed` is its numerical test.
-/

namespace Term

/--
`Term.subst f L t` simultaneously substitutes terms for variables in term code `t` in language
code `L`. `f i` supplies the term code for variable index `i`, inserted unchanged.
Constants and function symbols are preserved.
-/
def subst (f : Nat → Nat) : Nat → Nat → Nat :=
  fun L => rec f (const L) (app L) L

theorem subst_const (f : Nat → Nat) : ∀ L j, IsConstant L j →
    subst f L (const L j) = const L j := fun L j h => rec_const f (const L) (app L) L j h

theorem subst_var (f : Nat → Nat) : ∀ L i, subst f L (var L i) = f i :=
  fun L i => rec_var f (const L) (app L) L i

theorem subst_app (f : Nat → Nat) : ∀ L j args, IsFunction L j →
    subst f L (app L j args) =
      app L j (Tuple.map (subst f L) (Language.functionSymbolArity L j) args) :=
  fun L j args hj => rec_app f (const L) (app L) L j args hj

theorem subst_app_one (f : Nat → Nat) : ∀ L j t,
    IsFunction L j → Language.functionSymbolArity L j = 1 →
    subst f L (app L j t) = app L j (subst f L t) :=
  fun L j t hj ha => rec_app_one f (const L) (app L) L j t hj ha

theorem subst_app_two (f : Nat → Nat) : ∀ L j t u,
    IsFunction L j → Language.functionSymbolArity L j = 2 →
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
  rec S (fun _ => 0) (fun j xs => Tuple.max (Language.functionSymbolArity L j) xs) L

theorem bound_const : ∀ L j, IsConstant L j → bound L (const L j) = 0 :=
  fun L j hj => rec_const S (fun _ => 0)
    (fun j xs => Tuple.max (Language.functionSymbolArity L j) xs) L j hj

theorem bound_var : ∀ L n, bound L (var L n) = S n :=
  fun L n => rec_var S (fun _ => 0)
    (fun j xs => Tuple.max (Language.functionSymbolArity L j) xs) L n

theorem bound_app : ∀ L j args, IsFunction L j →
    bound L (app L j args) = Tuple.max (Language.functionSymbolArity L j)
      (Tuple.map (bound L) (Language.functionSymbolArity L j) args) :=
  fun L j args hj => rec_app S (fun _ => 0)
    (fun j xs => Tuple.max (Language.functionSymbolArity L j) xs) L j args hj

theorem bound_app_one : ∀ L j t,
    IsFunction L j → Language.functionSymbolArity L j = 1 →
    bound L (app L j t) = bound L t := by
  intro L j t hj ha
  rw [bound_app L j t hj, ha, Tuple.map_one _, Tuple.max_one]

theorem bound_app_two : ∀ L j t u,
    IsFunction L j → Language.functionSymbolArity L j = 2 →
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
      (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L

theorem substWithDepth_falsum (f : Nat → Nat → Nat) : ∀ L d,
    substWithDepth f L falsum d = falsum :=
  fun L d => recWithDepth_falsum (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L d

theorem substWithDepth_equal (f : Nat → Nat → Nat) : ∀ L t s d,
    substWithDepth f L (equal L t s) d = equal L (Term.subst (f d) L t) (Term.subst (f d) L s) :=
  fun L t s d => recWithDepth_equal (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L t s d

theorem substWithDepth_rel (f : Nat → Nat → Nat) : ∀ L j xs d, IsRelation L j →
    substWithDepth f L (rel L j xs) d =
      rel L j (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs) :=
  fun L j xs d hj => recWithDepth_rel (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L j xs d hj

theorem substWithDepth_imp (f : Nat → Nat → Nat) : ∀ L A B d,
    substWithDepth f L (imp A B) d = imp (substWithDepth f L A d) (substWithDepth f L B d) :=
  fun L A B d => recWithDepth_imp (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L A B d

theorem substWithDepth_all (f : Nat → Nat → Nat) : ∀ L A d,
    substWithDepth f L (all A) d = all (substWithDepth f L A (S d)) :=
  fun L A d => recWithDepth_all (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs))
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
    (fun j xs => Tuple.max (Language.relationSymbolArity L j)
      (Tuple.map (Term.bound L) (Language.relationSymbolArity L j) xs)) max pred L 0

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
    (fun j xs => Tuple.max (Language.relationSymbolArity L j)
      (Tuple.map (Term.bound L) (Language.relationSymbolArity L j) xs)) max pred L 0

theorem bound_equal : ∀ L t s,
    bound L (equal L t s) = max (Term.bound L t) (Term.bound L s) :=
  fun L t s => rec_equal
    (fun t s => max (Term.bound L t) (Term.bound L s))
    (fun j xs => Tuple.max (Language.relationSymbolArity L j)
      (Tuple.map (Term.bound L) (Language.relationSymbolArity L j) xs)) max pred L 0 t s

theorem bound_rel : ∀ L j xs, IsRelation L j →
    bound L (rel L j xs) = Tuple.max (Language.relationSymbolArity L j)
      (Tuple.map (Term.bound L) (Language.relationSymbolArity L j) xs) :=
  fun L j xs hj => rec_rel
    (fun t s => max (Term.bound L t) (Term.bound L s))
    (fun j xs => Tuple.max (Language.relationSymbolArity L j)
      (Tuple.map (Term.bound L) (Language.relationSymbolArity L j) xs)) max pred L 0 j xs hj

theorem bound_imp : ∀ L A B, bound L (imp A B) = max (bound L A) (bound L B) :=
  fun L A B => rec_imp
    (fun t s => max (Term.bound L t) (Term.bound L s))
    (fun j xs => Tuple.max (Language.relationSymbolArity L j)
      (Tuple.map (Term.bound L) (Language.relationSymbolArity L j) xs)) max pred L 0 A B

theorem bound_all : ∀ L A, bound L (all A) = pred (bound L A) :=
  fun L A => rec_all
    (fun t s => max (Term.bound L t) (Term.bound L s))
    (fun j xs => Tuple.max (Language.relationSymbolArity L j)
      (Tuple.map (Term.bound L) (Language.relationSymbolArity L j) xs)) max pred L 0 A

end Formula

end FOL

end
