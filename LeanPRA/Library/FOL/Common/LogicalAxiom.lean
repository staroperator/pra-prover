module

public import LeanPRA.Library.FOL.Common.Syntax

/-!
# Logical axioms of the shared Hilbert calculus

The axiom basis has three propositional schemas, two quantifier schemas, and five equality
schemas. In the formulas below, `A`, `B`, and `C` range over formulas of language `L`, and `s`, `t`,
and `u` range over its terms. Implications associate to the right, and `¬ A` means `A → ⊥`.

Propositional axioms:

1. `A → (B → A)`.
2. `(A → (B → C)) → ((A → B) → (A → C))`.
3. `(¬ A → ¬ B) → (B → A)`.

Quantifier axioms:

4. `(∀ A) → A[t]`.
5. `∀ (↑A → B) → (A → ∀ B)`.

Here `∀ A` means `Formula.all A`, `A[t]` means `Formula.instantiate L A t`, and `↑A` means
`Formula.shift L A`. Instantiation replaces the outermost quantifier position, adjusting indices
beneath nested binders. Shifting raises surrounding indices by one and preserves indices belonging
to binders inside `A`, so `↑A` does not depend on the position bound by the outer quantifier.
Schema 5 is the de Bruijn form of axiom (10) in §1H of
[Moschovakis's Logic Notes](https://www.math.ucla.edu/~ynm/lnlfiles/lnl.pdf), July 16, 2012, p. 34.

Equality axioms:

6. `t = t`.
7. `s = t → t = s`.
8. `s = t → (t = u → s = u)`.
9. `s₁ = t₁ → ⋯ → sₙ = tₙ → f(s₁, …, sₙ) = f(t₁, …, tₙ)`.
10. `s₁ = t₁ → ⋯ → sₙ = tₙ → (R(s₁, …, sₙ) → R(t₁, …, tₙ))`.

In schemas 9 and 10, `f` and `R` belong to `L` and have arity `n`. `Formula.equalPremises` builds
the chained equality premises.

- `isLogicalAxiom` tests whether a formula code matches one of the ten schemas, and
  `isLogicalAxiom_iff` characterizes acceptance as a disjunction of schema instances.
-/

@[expose] public section

pra

namespace FOL

namespace LogicalAxiom

/-- `isImplication L F` tests whether formula code `F` in language code `L` has the form
`A → (B → A)`. -/
def isImplication : Nat → Nat → Nat := fun L F =>
  let A := unpairLeft (Formula.arg L F);
  let B := unpairLeft (Formula.arg L (unpairRight (Formula.arg L F)));
  eqb F (Formula.imp A (Formula.imp B A))

theorem isImplication_bool : ∀ L F, IsBool (isImplication L F) :=
  fun L F => eqb_bool F _

theorem isImplication_iff : ∀ L F,
    isImplication L F = 1 ↔ ∃ A B, F = Formula.imp A (Formula.imp B A) := by
  intro L F
  constructor
  · intro h
    exact (unpairLeft (Formula.arg L F),
      unpairLeft (Formula.arg L (unpairRight (Formula.arg L F))),
      and_left (eqb_eq_one F _) h)
  · rintro (A, B, h)
    rw [h, isImplication]
    apply and_right (eqb_eq_one _ _)
    repeat first
      | rw [Formula.arg_imp]
      | rw [unpairLeft_pair]
      | rw [unpairRight_pair]

/-- `isImplicationDistribution L F` tests whether formula code `F` in language code `L` has the
form `(A → (B → C)) → ((A → B) → (A → C))`. -/
def isImplicationDistribution : Nat → Nat → Nat := fun L F =>
  let premise := unpairLeft (Formula.arg L F);
  let A := unpairLeft (Formula.arg L premise);
  let consequent := unpairRight (Formula.arg L premise);
  let B := unpairLeft (Formula.arg L consequent);
  let C := unpairRight (Formula.arg L consequent);
  eqb F (Formula.imp (Formula.imp A (Formula.imp B C))
    (Formula.imp (Formula.imp A B) (Formula.imp A C)))

theorem isImplicationDistribution_bool : ∀ L F, IsBool (isImplicationDistribution L F) :=
  fun L F => eqb_bool F _

theorem isImplicationDistribution_iff : ∀ L F,
    isImplicationDistribution L F = 1 ↔
      ∃ A B C, F = Formula.imp (Formula.imp A (Formula.imp B C))
        (Formula.imp (Formula.imp A B) (Formula.imp A C)) := by
  intro L F
  constructor
  · intro h
    exact (unpairLeft (Formula.arg L (unpairLeft (Formula.arg L F))),
      unpairLeft (Formula.arg L (unpairRight (Formula.arg L (unpairLeft (Formula.arg L F))))),
      unpairRight (Formula.arg L (unpairRight (Formula.arg L (unpairLeft (Formula.arg L F))))),
      and_left (eqb_eq_one F _) h)
  · rintro (A, B, C, h)
    rw [h, isImplicationDistribution]
    apply and_right (eqb_eq_one _ _)
    repeat first
      | rw [Formula.arg_imp]
      | rw [unpairLeft_pair]
      | rw [unpairRight_pair]

/-- `isContraposition L F` tests whether formula code `F` in language code `L` has the form
`(¬ A → ¬ B) → (B → A)`. -/
def isContraposition : Nat → Nat → Nat := fun L F =>
  let consequent := unpairRight (Formula.arg L F);
  let A := unpairRight (Formula.arg L consequent);
  let B := unpairLeft (Formula.arg L consequent);
  eqb F (Formula.imp (Formula.imp (Formula.neg A) (Formula.neg B)) (Formula.imp B A))

theorem isContraposition_bool : ∀ L F, IsBool (isContraposition L F) :=
  fun L F => eqb_bool F _

theorem isContraposition_iff : ∀ L F,
    isContraposition L F = 1 ↔
      ∃ A B, F = Formula.imp (Formula.imp (Formula.neg A) (Formula.neg B))
        (Formula.imp B A) := by
  intro L F
  constructor
  · intro h
    exact (unpairRight (Formula.arg L (unpairRight (Formula.arg L F))),
      unpairLeft (Formula.arg L (unpairRight (Formula.arg L F))),
      and_left (eqb_eq_one F _) h)
  · rintro (A, B, h)
    rw [h, isContraposition]
    apply and_right (eqb_eq_one _ _)
    repeat first
      | rw [Formula.arg_imp]
      | rw [unpairLeft_pair]
      | rw [unpairRight_pair]

/-- `isQuantifierImplication L F` tests whether formula code `F` in language code `L` has the form
`∀ (↑A → B) → (A → ∀ B)`. -/
def isQuantifierImplication : Nat → Nat → Nat := fun L F =>
  let consequent := unpairRight (Formula.arg L F);
  let A := unpairLeft (Formula.arg L consequent);
  let B := Formula.arg L (unpairRight (Formula.arg L consequent));
  eqb F (Formula.imp (Formula.all (Formula.imp (Formula.shift L A) B))
    (Formula.imp A (Formula.all B)))

theorem isQuantifierImplication_bool : ∀ L F, IsBool (isQuantifierImplication L F) :=
  fun L F => eqb_bool F _

theorem isQuantifierImplication_iff : ∀ L F,
    isQuantifierImplication L F = 1 ↔
      ∃ A B, F = Formula.imp (Formula.all (Formula.imp (Formula.shift L A) B))
        (Formula.imp A (Formula.all B)) := by
  intro L F
  constructor
  · intro h
    exact (unpairLeft (Formula.arg L (unpairRight (Formula.arg L F))),
      Formula.arg L (unpairRight (Formula.arg L (unpairRight (Formula.arg L F)))),
      and_left (eqb_eq_one F _) h)
  · rintro (A, B, h)
    rw [h, isQuantifierImplication]
    apply and_right (eqb_eq_one _ _)
    repeat first
      | rw [Formula.arg_imp]
      | rw [Formula.arg_all]
      | rw [unpairLeft_pair]
      | rw [unpairRight_pair]

/-- `isReflexivity L F` tests whether formula code `F` in language code `L` has the form `t = t`. -/
def isReflexivity : Nat → Nat → Nat := fun L F =>
  let t := unpairLeft (Formula.arg L F);
  eqb F (Formula.equal L t t)

theorem isReflexivity_bool : ∀ L F, IsBool (isReflexivity L F) :=
  fun L F => eqb_bool F _

theorem isReflexivity_iff : ∀ L F,
    isReflexivity L F = 1 ↔ ∃ t, F = Formula.equal L t t := by
  intro L F
  constructor
  · intro h
    exact (unpairLeft (Formula.arg L F), and_left (eqb_eq_one F _) h)
  · rintro (t, h)
    rw [h, isReflexivity]
    apply and_right (eqb_eq_one _ _)
    repeat first
      | rw [Formula.arg_imp]
      | rw [Formula.arg_equal]
      | rw [unpairLeft_pair]
      | rw [unpairRight_pair]

/-- `isSymmetry L F` tests whether formula code `F` in language code `L` has the form
`s = t → t = s`. -/
def isSymmetry : Nat → Nat → Nat := fun L F =>
  let premise := unpairLeft (Formula.arg L F);
  let s := unpairLeft (Formula.arg L premise);
  let t := unpairRight (Formula.arg L premise);
  eqb F (Formula.imp (Formula.equal L s t) (Formula.equal L t s))

theorem isSymmetry_bool : ∀ L F, IsBool (isSymmetry L F) :=
  fun L F => eqb_bool F _

theorem isSymmetry_iff : ∀ L F,
    isSymmetry L F = 1 ↔ ∃ s t, F = Formula.imp (Formula.equal L s t) (Formula.equal L t s) := by
  intro L F
  constructor
  · intro h
    exact (unpairLeft (Formula.arg L (unpairLeft (Formula.arg L F))),
      unpairRight (Formula.arg L (unpairLeft (Formula.arg L F))),
      and_left (eqb_eq_one F _) h)
  · rintro (s, t, h)
    rw [h, isSymmetry]
    apply and_right (eqb_eq_one _ _)
    repeat first
      | rw [Formula.arg_imp]
      | rw [Formula.arg_equal]
      | rw [unpairLeft_pair]
      | rw [unpairRight_pair]

/-- `isTransitivity L F` tests whether formula code `F` in language code `L` has the form
`s = t → (t = u → s = u)`. -/
def isTransitivity : Nat → Nat → Nat := fun L F =>
  let premise := unpairLeft (Formula.arg L F);
  let s := unpairLeft (Formula.arg L premise);
  let t := unpairRight (Formula.arg L premise);
  let u := unpairRight (Formula.arg L (unpairRight
    (Formula.arg L (unpairRight (Formula.arg L F)))));
  eqb F (Formula.imp (Formula.equal L s t)
    (Formula.imp (Formula.equal L t u) (Formula.equal L s u)))

theorem isTransitivity_bool : ∀ L F, IsBool (isTransitivity L F) :=
  fun L F => eqb_bool F _

theorem isTransitivity_iff : ∀ L F,
    isTransitivity L F = 1 ↔
      ∃ s t u, F = Formula.imp (Formula.equal L s t)
        (Formula.imp (Formula.equal L t u) (Formula.equal L s u)) := by
  intro L F
  constructor
  · intro h
    exact (unpairLeft (Formula.arg L (unpairLeft (Formula.arg L F))),
      unpairRight (Formula.arg L (unpairLeft (Formula.arg L F))),
      unpairRight (Formula.arg L (unpairRight (Formula.arg L (unpairRight (Formula.arg L F))))),
      and_left (eqb_eq_one F _) h)
  · rintro (s, t, u, h)
    rw [h, isTransitivity]
    apply and_right (eqb_eq_one _ _)
    repeat first
      | rw [Formula.arg_imp]
      | rw [Formula.arg_equal]
      | rw [unpairLeft_pair]
      | rw [unpairRight_pair]

/--
`isInstantiation L F` tests whether formula code `F` in language code `L` has the form
`(∀ A) → A[t]`, searching for the replacement term code `t` up to `F`.
An occurrence of `t` in `A[t]` bounds `t` by `F`; when the quantifier position is unused,
term code `0` gives the same instance.
-/
def isInstantiation : Nat → Nat → Nat := fun L F =>
  let antecedent := unpairLeft (Formula.arg L F);
  let A := Formula.arg L antecedent;
  band (eqb (Formula.head L F) 1)
    (band (eqb (Formula.head L antecedent) 2)
      (anyBelow (fun t => eqb F
        (Formula.imp (Formula.all A) (Formula.instantiate L A t))) (S F)))

theorem isInstantiation_bool : ∀ L F, IsBool (isInstantiation L F) :=
  fun L F => band_bool _ _

theorem isInstantiation_iff : ∀ L F,
    isInstantiation L F = 1 ↔ ∃ A t, t ≤ F ∧
      F = Formula.imp (Formula.all A) (Formula.instantiate L A t) := by
  intro L F
  constructor
  · intro h
    have h₁ := and_right (and_left (band_eq_one _ _) h)
    have h₂ := and_right (and_left (band_eq_one _ _)
      (and_right (bool_eq_one _ (band_bool _ _)) h₁))
    have hs := and_right (bool_eq_one _ (anyBelow_bool
      (fun t => eqb F (Formula.imp
        (Formula.all (Formula.arg L (unpairLeft (Formula.arg L F))))
        (Formula.instantiate L (Formula.arg L (unpairLeft (Formula.arg L F))) t))) (S F))) h₂
    rcases and_left (anyBelow_eq_one _ (S F)) hs with (t, ht, he)
    exact (Formula.arg L (unpairLeft (Formula.arg L F)), t,
      and_left (lt_succ t F) ht,
      and_left (eqb_eq_one F _) (and_right (bool_eq_one _ (eqb_bool F _)) he))
  · rintro (A, t, ht, he)
    rw [he, isInstantiation, Formula.head_imp, Formula.arg_imp, unpairLeft_pair,
      Formula.head_all, Formula.arg_all, eqb_self]
    apply band_eq_one_of_eq_one _ _ rfl
    apply band_eq_one_of_eq_one _ _ rfl
    rw [← he]
    apply and_right (anyBelow_eq_one _ (S F))
    exists t
    constructor
    · exact and_right (lt_succ t F) ht
    apply and_left (bool_eq_one _ (eqb_bool F _))
    apply and_right (eqb_eq_one F _)
    exact he

/-- `isFunctionCongruence L F` tests whether formula code `F` in language code `L` has the form
`s₁ = t₁ → ⋯ → sₙ = tₙ → f(s₁, …, sₙ) = f(t₁, …, tₙ)` for a function symbol `f` of `L`. -/
def isFunctionCongruence : Nat → Nat → Nat := fun L F =>
  anyBelow (fun j =>
    let conclusion := iter (fun B => unpairRight (Formula.arg L B)) (Language.functionArity L j) F;
    let xs := Term.arg L (unpairLeft (Formula.arg L conclusion));
    let ys := Term.arg L (unpairRight (Formula.arg L conclusion));
    eqb F (Formula.equalPremises L (Language.functionArity L j) xs ys
      (Formula.equal L (Term.app L j xs) (Term.app L j ys)))) (Language.functionCount L)

theorem isFunctionCongruence_bool : ∀ L F, IsBool (isFunctionCongruence L F) :=
  fun L F => anyBelow_bool _ (Language.functionCount L)

theorem isFunctionCongruence_iff : ∀ L F,
    isFunctionCongruence L F = 1 ↔ ∃ j xs ys, j < Language.functionCount L ∧
      F = Formula.equalPremises L (Language.functionArity L j) xs ys
        (Formula.equal L (Term.app L j xs) (Term.app L j ys)) := by
  intro L F
  constructor
  · intro h
    rcases and_left (anyBelow_eq_one _ (Language.functionCount L)) h with (j, hj, he)
    exact (j,
      Term.arg L (unpairLeft (Formula.arg L
        (iter (fun B => unpairRight (Formula.arg L B)) (Language.functionArity L j) F))),
      Term.arg L (unpairRight (Formula.arg L
        (iter (fun B => unpairRight (Formula.arg L B)) (Language.functionArity L j) F))),
      hj, and_left (eqb_eq_one F _) (and_right (bool_eq_one _ (eqb_bool F _)) he))
  · rintro (j, xs, ys, hj, he)
    rw [isFunctionCongruence]
    apply and_right (anyBelow_eq_one _ (Language.functionCount L))
    exists j
    constructor
    · exact hj
    apply and_left (bool_eq_one _ (eqb_bool F _))
    apply and_right (eqb_eq_one F _)
    rw [he, Formula.equalPremises_consequent,
      Formula.arg_equal, unpairLeft_pair, unpairRight_pair,
      Term.arg_app L j xs hj, Term.arg_app L j ys hj]

/-- `isRelationCongruence L F` tests whether formula code `F` in language code `L` has the form
`s₁ = t₁ → ⋯ → sₙ = tₙ → (R(s₁, …, sₙ) → R(t₁, …, tₙ))` for a relation symbol `R` of `L`. -/
def isRelationCongruence : Nat → Nat → Nat := fun L F =>
  anyBelow (fun j =>
    let conclusion := iter (fun B => unpairRight (Formula.arg L B)) (Language.relationArity L j) F;
    let xs := Formula.arg L (unpairLeft (Formula.arg L conclusion));
    let ys := Formula.arg L (unpairRight (Formula.arg L conclusion));
    eqb F (Formula.equalPremises L (Language.relationArity L j) xs ys
      (Formula.imp (Formula.rel L j xs) (Formula.rel L j ys)))) (Language.relationCount L)

theorem isRelationCongruence_bool : ∀ L F, IsBool (isRelationCongruence L F) :=
  fun L F => anyBelow_bool _ (Language.relationCount L)

theorem isRelationCongruence_iff : ∀ L F,
    isRelationCongruence L F = 1 ↔ ∃ j xs ys, j < Language.relationCount L ∧
      F = Formula.equalPremises L (Language.relationArity L j) xs ys
        (Formula.imp (Formula.rel L j xs) (Formula.rel L j ys)) := by
  intro L F
  constructor
  · intro h
    rcases and_left (anyBelow_eq_one _ (Language.relationCount L)) h with (j, hj, he)
    exact (j,
      Formula.arg L (unpairLeft (Formula.arg L
        (iter (fun B => unpairRight (Formula.arg L B)) (Language.relationArity L j) F))),
      Formula.arg L (unpairRight (Formula.arg L
        (iter (fun B => unpairRight (Formula.arg L B)) (Language.relationArity L j) F))),
      hj, and_left (eqb_eq_one F _) (and_right (bool_eq_one _ (eqb_bool F _)) he))
  · rintro (j, xs, ys, hj, he)
    rw [isRelationCongruence]
    apply and_right (anyBelow_eq_one _ (Language.relationCount L))
    exists j
    constructor
    · exact hj
    apply and_left (bool_eq_one _ (eqb_bool F _))
    apply and_right (eqb_eq_one F _)
    rw [he, Formula.equalPremises_consequent,
      Formula.arg_imp, unpairLeft_pair, unpairRight_pair,
      Formula.arg_rel L j xs hj, Formula.arg_rel L j ys hj]

end LogicalAxiom

/--
`isLogicalAxiom L F` returns `1` when formula code `F` in language code `L` is an instance of
one of the ten logical axiom schemas, and `0` otherwise.
-/
def isLogicalAxiom : Nat → Nat → Nat := fun L F =>
  bor (LogicalAxiom.isImplication L F)
    (bor (LogicalAxiom.isImplicationDistribution L F)
    (bor (LogicalAxiom.isContraposition L F)
    (bor (LogicalAxiom.isInstantiation L F)
    (bor (LogicalAxiom.isQuantifierImplication L F)
    (bor (LogicalAxiom.isReflexivity L F)
    (bor (LogicalAxiom.isSymmetry L F)
    (bor (LogicalAxiom.isTransitivity L F)
    (bor (LogicalAxiom.isFunctionCongruence L F)
      (LogicalAxiom.isRelationCongruence L F)))))))))

theorem isLogicalAxiom_bool : ∀ L F, IsBool (isLogicalAxiom L F) :=
  fun L F => bor_bool _ _

/-- Acceptance is equivalent to a schema instance, with the instantiation search bound explicit. -/
theorem isLogicalAxiom_iff : ∀ L F, isLogicalAxiom L F = 1 ↔
    (∃ A B, F = Formula.imp A (Formula.imp B A)) ∨
    (∃ A B C, F = Formula.imp (Formula.imp A (Formula.imp B C))
      (Formula.imp (Formula.imp A B) (Formula.imp A C))) ∨
    (∃ A B, F = Formula.imp (Formula.imp (Formula.neg A) (Formula.neg B)) (Formula.imp B A)) ∨
    (∃ A t, t ≤ F ∧
      F = Formula.imp (Formula.all A) (Formula.instantiate L A t)) ∨
    (∃ A B, F = Formula.imp (Formula.all (Formula.imp (Formula.shift L A) B))
      (Formula.imp A (Formula.all B))) ∨
    (∃ t, F = Formula.equal L t t) ∨
    (∃ s t, F = Formula.imp (Formula.equal L s t) (Formula.equal L t s)) ∨
    (∃ s t u, F = Formula.imp (Formula.equal L s t)
      (Formula.imp (Formula.equal L t u) (Formula.equal L s u))) ∨
    (∃ j xs ys, j < Language.functionCount L ∧
      F = Formula.equalPremises L (Language.functionArity L j) xs ys
        (Formula.equal L (Term.app L j xs) (Term.app L j ys))) ∨
    (∃ j xs ys, j < Language.relationCount L ∧
      F = Formula.equalPremises L (Language.relationArity L j) xs ys
        (Formula.imp (Formula.rel L j xs) (Formula.rel L j ys))) := by
  intro L F
  apply iff_trans (bor_eq_one_of_bool _ _ (LogicalAxiom.isImplication_bool L F)
    (bor_bool _ _))
  apply or_congr (LogicalAxiom.isImplication_iff L F)
  apply iff_trans (bor_eq_one_of_bool _ _ (LogicalAxiom.isImplicationDistribution_bool L F)
    (bor_bool _ _))
  apply or_congr (LogicalAxiom.isImplicationDistribution_iff L F)
  apply iff_trans (bor_eq_one_of_bool _ _ (LogicalAxiom.isContraposition_bool L F)
    (bor_bool _ _))
  apply or_congr (LogicalAxiom.isContraposition_iff L F)
  apply iff_trans (bor_eq_one_of_bool _ _ (LogicalAxiom.isInstantiation_bool L F)
    (bor_bool _ _))
  apply or_congr (LogicalAxiom.isInstantiation_iff L F)
  apply iff_trans (bor_eq_one_of_bool _ _ (LogicalAxiom.isQuantifierImplication_bool L F)
    (bor_bool _ _))
  apply or_congr (LogicalAxiom.isQuantifierImplication_iff L F)
  apply iff_trans (bor_eq_one_of_bool _ _ (LogicalAxiom.isReflexivity_bool L F)
    (bor_bool _ _))
  apply or_congr (LogicalAxiom.isReflexivity_iff L F)
  apply iff_trans (bor_eq_one_of_bool _ _ (LogicalAxiom.isSymmetry_bool L F)
    (bor_bool _ _))
  apply or_congr (LogicalAxiom.isSymmetry_iff L F)
  apply iff_trans (bor_eq_one_of_bool _ _ (LogicalAxiom.isTransitivity_bool L F)
    (bor_bool _ _))
  apply or_congr (LogicalAxiom.isTransitivity_iff L F)
  apply iff_trans (bor_eq_one_of_bool _ _ (LogicalAxiom.isFunctionCongruence_bool L F)
    (LogicalAxiom.isRelationCongruence_bool L F))
  apply or_congr (LogicalAxiom.isFunctionCongruence_iff L F)
  exact LogicalAxiom.isRelationCongruence_iff L F

theorem isLogicalAxiom_falsum : ∀ L, isLogicalAxiom L Formula.falsum = 0 := by
  intro L
  apply and_right (bool_eq_zero _ (isLogicalAxiom_bool L Formula.falsum))
  intro h
  rcases and_left (isLogicalAxiom_iff L Formula.falsum) h with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · rcases h0 with (A, B, he)
    exact Formula.imp_ne_zero _ _ (eq_symm he)
  · rcases h1 with (A, B, C, he)
    exact Formula.imp_ne_zero _ _ (eq_symm he)
  · rcases h2 with (A, B, he)
    exact Formula.imp_ne_zero _ _ (eq_symm he)
  · rcases h3 with (A, t, ht, he)
    exact Formula.imp_ne_zero _ _ (eq_symm he)
  · rcases h4 with (A, B, he)
    exact Formula.imp_ne_zero _ _ (eq_symm he)
  · rcases h5 with (t, he)
    exact Formula.equal_ne_zero L _ _ (eq_symm he)
  · rcases h6 with (s, t, he)
    exact Formula.imp_ne_zero _ _ (eq_symm he)
  · rcases h7 with (s, t, u, he)
    exact Formula.imp_ne_zero _ _ (eq_symm he)
  · rcases h8 with (j, xs, ys, hj, he)
    exact Formula.equalPremises_succ_ne_zero L _ _ _ _ (eq_symm he)
  · rcases h9 with (j, xs, ys, hj, he)
    exact Formula.equalPremises_succ_ne_zero L _ _ _ _ (eq_symm he)

theorem isLogicalAxiom_all : ∀ L body, isLogicalAxiom L (Formula.all body) = 0 := by
  intro L body
  apply and_right (bool_eq_zero _ (isLogicalAxiom_bool L (Formula.all body)))
  intro h
  rcases and_left (isLogicalAxiom_iff L (Formula.all body)) h with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · rcases h0 with (A, B, he)
    have hh := eq_congr (Formula.head L) he
    rw [Formula.head_all, Formula.head_imp] at hh
    exact succ_ne_zero 0 (succ_inj hh)
  · rcases h1 with (A, B, C, he)
    have hh := eq_congr (Formula.head L) he
    rw [Formula.head_all, Formula.head_imp] at hh
    exact succ_ne_zero 0 (succ_inj hh)
  · rcases h2 with (A, B, he)
    have hh := eq_congr (Formula.head L) he
    rw [Formula.head_all, Formula.head_imp] at hh
    exact succ_ne_zero 0 (succ_inj hh)
  · rcases h3 with (A, t, ht, he)
    have hh := eq_congr (Formula.head L) he
    rw [Formula.head_all, Formula.head_imp] at hh
    exact succ_ne_zero 0 (succ_inj hh)
  · rcases h4 with (A, B, he)
    have hh := eq_congr (Formula.head L) he
    rw [Formula.head_all, Formula.head_imp] at hh
    exact succ_ne_zero 0 (succ_inj hh)
  · rcases h5 with (t, he)
    have hh := eq_congr (Formula.head L) he
    rw [Formula.head_all, Formula.head_equal] at hh
    exact succ_ne_zero 1 hh
  · rcases h6 with (s, t, he)
    have hh := eq_congr (Formula.head L) he
    rw [Formula.head_all, Formula.head_imp] at hh
    exact succ_ne_zero 0 (succ_inj hh)
  · rcases h7 with (s, t, u, he)
    have hh := eq_congr (Formula.head L) he
    rw [Formula.head_all, Formula.head_imp] at hh
    exact succ_ne_zero 0 (succ_inj hh)
  · rcases h8 with (j, xs, ys, hj, he)
    have hh := eq_congr (Formula.head L) he
    rw [Formula.head_all, Language.functionArity, Formula.head_equalPremises_succ] at hh
    exact succ_ne_zero 0 (succ_inj hh)
  · rcases h9 with (j, xs, ys, hj, he)
    have hh := eq_congr (Formula.head L) he
    rw [Formula.head_all, Language.relationArity, Formula.head_equalPremises_succ] at hh
    exact succ_ne_zero 0 (succ_inj hh)

theorem isLogicalAxiom_of_implication : ∀ L A B,
    isLogicalAxiom L (Formula.imp A (Formula.imp B A)) = 1 := by
  intro L A B
  apply and_right (isLogicalAxiom_iff L _)
  left
  exact (A, B, rfl)

theorem isLogicalAxiom_of_implicationDistribution : ∀ L A B C,
    isLogicalAxiom L (Formula.imp (Formula.imp A (Formula.imp B C))
      (Formula.imp (Formula.imp A B) (Formula.imp A C))) = 1 := by
  intro L A B C
  apply and_right (isLogicalAxiom_iff L _)
  right
  left
  exact (A, B, C, rfl)

theorem isLogicalAxiom_of_contraposition : ∀ L A B,
    isLogicalAxiom L
      (Formula.imp (Formula.imp (Formula.neg A) (Formula.neg B)) (Formula.imp B A)) = 1 := by
  intro L A B
  apply and_right (isLogicalAxiom_iff L _)
  right
  right
  left
  exact (A, B, rfl)

theorem isLogicalAxiom_of_instantiation : ∀ L A t,
    t ≤ Formula.imp (Formula.all A) (Formula.instantiate L A t) →
    isLogicalAxiom L (Formula.imp (Formula.all A) (Formula.instantiate L A t)) = 1 := by
  intro L A t h
  apply and_right (isLogicalAxiom_iff L _)
  right
  right
  right
  left
  exact (A, t, h, rfl)

theorem isLogicalAxiom_of_quantifierImplication : ∀ L A B,
    isLogicalAxiom L (Formula.imp (Formula.all (Formula.imp (Formula.shift L A) B))
      (Formula.imp A (Formula.all B))) = 1 := by
  intro L A B
  apply and_right (isLogicalAxiom_iff L _)
  right
  right
  right
  right
  left
  exact (A, B, rfl)

theorem isLogicalAxiom_of_reflexivity : ∀ L t,
    isLogicalAxiom L (Formula.equal L t t) = 1 := by
  intro L t
  apply and_right (isLogicalAxiom_iff L _)
  right
  right
  right
  right
  right
  left
  exact (t, rfl)

theorem isLogicalAxiom_of_symmetry : ∀ L s t,
    isLogicalAxiom L (Formula.imp (Formula.equal L s t) (Formula.equal L t s)) = 1 := by
  intro L s t
  apply and_right (isLogicalAxiom_iff L _)
  right
  right
  right
  right
  right
  right
  left
  exact (s, t, rfl)

theorem isLogicalAxiom_of_transitivity : ∀ L s t u,
    isLogicalAxiom L (Formula.imp (Formula.equal L s t)
      (Formula.imp (Formula.equal L t u) (Formula.equal L s u))) = 1 := by
  intro L s t u
  apply and_right (isLogicalAxiom_iff L _)
  right
  right
  right
  right
  right
  right
  right
  left
  exact (s, t, u, rfl)

theorem isLogicalAxiom_of_functionCongruence : ∀ L j xs ys,
    j < Language.functionCount L →
    isLogicalAxiom L (Formula.equalPremises L (Language.functionArity L j) xs ys
      (Formula.equal L (Term.app L j xs) (Term.app L j ys))) = 1 := by
  intro L j xs ys h
  apply and_right (isLogicalAxiom_iff L _)
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact (j, xs, ys, h, rfl)

theorem isLogicalAxiom_of_relationCongruence : ∀ L j xs ys,
    j < Language.relationCount L →
    isLogicalAxiom L (Formula.equalPremises L (Language.relationArity L j) xs ys
      (Formula.imp (Formula.rel L j xs) (Formula.rel L j ys))) = 1 := by
  intro L j xs ys h
  apply and_right (isLogicalAxiom_iff L _)
  right
  right
  right
  right
  right
  right
  right
  right
  right
  exact (j, xs, ys, h, rfl)

end FOL

end
