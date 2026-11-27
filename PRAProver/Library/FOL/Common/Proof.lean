module

public import PRAProver.Library.FOL.Common.LogicalAxiom
meta import PRAProver.Library.Tactic.Witness.Extract

/-!
# Numerical Hilbert proofs and provability

This module encodes first-order proofs as natural numbers, checks their inference rules, and
proves that the proof constructors produce accepted proofs. It also derives proofs of the
logical axioms and proves universal instantiation for arbitrary formula and term codes.

For a first-order language `L` and a theory `T` of formulas, the Hilbert proof system has four
rules:

- Logical axiom: `T ⊢ A` if `A` is an instance of a schema in `LogicalAxiom.lean`.
- Hypothesis: `T ⊢ A` if `A ∈ T`.
- Modus ponens (MP): `T ⊢ A` if `T ⊢ B → A` and `T ⊢ B`.
- Generalization (GEN): `T ⊢ ∀ A` if `T ⊢ A`, binding surrounding position `0`.

Proofs are finite trees whose leaves are logical axioms or theory hypotheses. Theory axioms and
proof conclusions may contain surrounding variable positions, with theory axioms understood
universally, so GEN applies at any node.
-/

@[expose] public section

pra

namespace FOL

/-! ## Proof trees and recursion

Proof trees are encoded in `Nat`. Each node stores a rule tag, its conclusion formula, and
its premise subtrees, using `S (pair rule (pair conclusion premises))`:

- `Proof.axiom A` is encoded as `S (pair 0 (pair A 0))`.
- `Proof.hypothesis A` is encoded as `S (pair 1 (pair A 0))`.
- `Proof.mp A p q` is encoded as `S (pair 2 (pair A (pair p q)))`.
- `Proof.gen A p` is encoded as `S (pair 3 (pair (Formula.all A) p))`.

Here `A` is a formula code, and `p`, `q` are complete subtree codes. In `Proof.mp`, `p` proves
`B → A` and `q` proves `B`; in `Proof.gen`, `p` proves `A`.

Taking the predecessor and unpairing recovers the node fields through `Proof.rule`,
`Proof.conclusion`, and `Proof.premises`. Code `0`, rule tags above `3`, and leaves with nonzero
premise data are invalid. Every subtree code is smaller than its parent, so the tree can be
traversed by numerical course-of-values recursion.

- `Proof.mp'` reads the consequent from the first proof and applies modus ponens.
- `Proof.rec` combines the results from premise subtrees according to the rule at each node.
-/

namespace Proof

/-- `Proof.axiom A` encodes a logical axiom leaf with conclusion formula code `A`. -/
def «axiom» : Nat → Nat := fun A => S (pair 0 (pair A 0))

/-- `Proof.hypothesis A` encodes a hypothesis leaf with conclusion formula code `A`. -/
def hypothesis : Nat → Nat := fun A => S (pair 1 (pair A 0))

/--
`Proof.mp A p q` encodes modus ponens with conclusion formula code `A`, implication subtree
code `p`, and antecedent subtree code `q`.
-/
def mp : Nat → Nat → Nat → Nat := fun A p q => S (pair 2 (pair A (pair p q)))

/--
`Proof.gen A p` encodes generalization from subtree code `p`, whose conclusion should be formula
code `A`, to `Formula.all A`.
-/
def gen : Nat → Nat → Nat := fun A p => S (pair 3 (pair (Formula.all A) p))

/--
`Proof.rule prf` reads the rule tag of a nonzero tree code: `0` for a logical axiom, `1` for a
hypothesis, `2` for modus ponens, and `3` for generalization. Other tags are invalid.
-/
def rule : Nat → Nat := fun prf => unpairLeft (pred prf)

/-- `Proof.conclusion prf` reads the conclusion formula code at the root of tree code `prf`. -/
def conclusion : Nat → Nat := fun prf => unpairLeft (unpairRight (pred prf))

/--
`Proof.premises prf` reads the subtree data: `0` for a leaf, a pair of subtree codes for modus
ponens, or one subtree code for generalization. Code `0` is invalid.
-/
def premises : Nat → Nat := fun prf => unpairRight (unpairRight (pred prf))

/-- Apply a proof of an implication to a proof of its antecedent. The implication
conclusion supplies the consequent code; `IsProofOf.mp'` states the required premises. -/
def mp' : Nat → Nat → Nat → Nat := fun L p q =>
  mp (unpairRight (Formula.arg L (conclusion p))) p q

theorem rule_axiom : ∀ A, rule (Proof.axiom A) = 0 := by
  intro A
  rw [rule, Proof.axiom, pred_succ, unpairLeft_pair]

theorem conclusion_axiom : ∀ A, conclusion (Proof.axiom A) = A := by
  intro A
  rw [conclusion, Proof.axiom, pred_succ, unpairRight_pair, unpairLeft_pair]

theorem premises_axiom : ∀ A, premises (Proof.axiom A) = 0 := by
  intro A
  rw [premises, Proof.axiom, pred_succ, unpairRight_pair, unpairRight_pair]

theorem rule_hypothesis : ∀ A, rule (hypothesis A) = 1 := by
  intro A
  rw [rule, hypothesis, pred_succ, unpairLeft_pair]

theorem conclusion_hypothesis : ∀ A, conclusion (hypothesis A) = A := by
  intro A
  rw [conclusion, hypothesis, pred_succ, unpairRight_pair, unpairLeft_pair]

theorem premises_hypothesis : ∀ A, premises (hypothesis A) = 0 := by
  intro A
  rw [premises, hypothesis, pred_succ, unpairRight_pair, unpairRight_pair]

theorem rule_mp : ∀ A p q, rule (mp A p q) = 2 := by
  intro A p q
  rw [rule, mp, pred_succ, unpairLeft_pair]

theorem conclusion_mp : ∀ A p q, conclusion (mp A p q) = A := by
  intro A p q
  rw [conclusion, mp, pred_succ, unpairRight_pair, unpairLeft_pair]

theorem premises_mp : ∀ A p q, premises (mp A p q) = pair p q := by
  intro A p q
  rw [premises, mp, pred_succ, unpairRight_pair, unpairRight_pair]

theorem rule_gen : ∀ A p, rule (gen A p) = 3 := by
  intro A p
  rw [rule, gen, pred_succ, unpairLeft_pair]

theorem conclusion_gen : ∀ A p, conclusion (gen A p) = Formula.all A := by
  intro A p
  rw [conclusion, gen, pred_succ, unpairRight_pair, unpairLeft_pair]

theorem premises_gen : ∀ A p, premises (gen A p) = p := by
  intro A p
  rw [premises, gen, pred_succ, unpairRight_pair, unpairRight_pair]

theorem left_lt_mp : ∀ A p q, p < mp A p q := by
  intro A p q
  apply and_right (lt_succ p (pair 2 (pair A (pair p q))))
  exact le_trans _ _ _ (left_le_pair p q)
    (le_trans _ _ _ (right_le_pair A (pair p q)) (right_le_pair 2 (pair A (pair p q))))

theorem right_lt_mp : ∀ A p q, q < mp A p q := by
  intro A p q
  apply and_right (lt_succ q (pair 2 (pair A (pair p q))))
  exact le_trans _ _ _ (right_le_pair p q)
    (le_trans _ _ _ (right_le_pair A (pair p q)) (right_le_pair 2 (pair A (pair p q))))

theorem premise_lt_gen : ∀ A p, p < gen A p := by
  intro A p
  apply and_right (lt_succ p (pair 3 (pair (Formula.all A) p)))
  exact le_trans _ _ _ (right_le_pair (Formula.all A) p)
    (right_le_pair 3 (pair (Formula.all A) p))

/--
`Proof.rec onAxiom hypothesis mp gen prf` traverses numerical tree code `prf`:

- `onAxiom A` and `hypothesis A` process leaves with conclusion formula code `A`.
- `mp A p q x y` receives the conclusion formula code `A`, subtree codes `p` and `q`, and their
  recursive results `x` and `y`.
- `gen A p x` receives the quantified conclusion formula code `A`, subtree code `p`, and its
  recursive result `x`.

Invalid root encodings return `0`.
-/
def rec (onAxiom hypothesis : Nat → Nat) (mp : Nat → Nat → Nat → Nat → Nat → Nat)
    (gen : Nat → Nat → Nat → Nat) : Nat → Nat := covrec (fun prf history =>
  let k := rule prf;
  let A := conclusion prf;
  let children := premises prf;
  ite prf
    (ite (eqb k 0) (ite (eqb children 0) (onAxiom A) 0)
    (ite (eqb k 1) (ite (eqb children 0) (hypothesis A) 0)
    (ite (eqb k 2) (mp A (unpairLeft children) (unpairRight children)
      (Sequence.rget history (unpairLeft children))
      (Sequence.rget history (unpairRight children)))
    (ite (eqb k 3) (gen A children (Sequence.rget history children)) 0)))) 0)

theorem rec_zero (onAxiom hypothesis : Nat → Nat) (mp : Nat → Nat → Nat → Nat → Nat → Nat)
    (gen : Nat → Nat → Nat → Nat) : rec onAxiom hypothesis mp gen 0 = 0 := rfl

theorem rec_axiom (onAxiom hypothesis : Nat → Nat) (mp : Nat → Nat → Nat → Nat → Nat → Nat)
    (gen : Nat → Nat → Nat → Nat) :
    ∀ A, rec onAxiom hypothesis mp gen (Proof.axiom A) = onAxiom A := by
  intro A
  rw [rec, covrec, rule_axiom, conclusion_axiom, premises_axiom]
  rw [ite_of_ne_zero _ _ _ (succ_ne_zero (pred (Proof.axiom A)))]
  rfl

theorem rec_hypothesis (onAxiom hypothesis : Nat → Nat) (mp : Nat → Nat → Nat → Nat → Nat → Nat)
    (gen : Nat → Nat → Nat → Nat) :
    ∀ A, rec onAxiom hypothesis mp gen (Proof.hypothesis A) = hypothesis A := by
  intro A
  rw [rec, covrec, rule_hypothesis, conclusion_hypothesis, premises_hypothesis]
  rw [ite_of_ne_zero _ _ _ (succ_ne_zero (pred (Proof.hypothesis A)))]
  rfl

theorem rec_mp (onAxiom hypothesis : Nat → Nat) (mp : Nat → Nat → Nat → Nat → Nat → Nat)
    (gen : Nat → Nat → Nat → Nat) :
    ∀ A p q, rec onAxiom hypothesis mp gen (Proof.mp A p q) =
      mp A p q (rec onAxiom hypothesis mp gen p) (rec onAxiom hypothesis mp gen q) := by
  intro A p q
  rw [rec, covrec, rule_mp, conclusion_mp, premises_mp]
  rw [ite_of_ne_zero _ _ _ (succ_ne_zero (pred (Proof.mp A p q)))]
  rw [unpairLeft_pair, unpairRight_pair]
  change mp A p q _ _ = _
  rw [Sequence.rget_generate _ p (Proof.mp A p q) (left_lt_mp A p q),
    Sequence.rget_generate _ q (Proof.mp A p q) (right_lt_mp A p q)]
  rfl

theorem rec_gen (onAxiom hypothesis : Nat → Nat) (mp : Nat → Nat → Nat → Nat → Nat → Nat)
    (gen : Nat → Nat → Nat → Nat) :
    ∀ A p, rec onAxiom hypothesis mp gen (Proof.gen A p) =
      gen (Formula.all A) p (rec onAxiom hypothesis mp gen p) := by
  intro A p
  rw [rec, covrec, rule_gen, conclusion_gen, premises_gen]
  rw [ite_of_ne_zero _ _ _ (succ_ne_zero (pred (Proof.gen A p)))]
  change gen (Formula.all A) p _ = _
  rw [Sequence.rget_generate _ p (Proof.gen A p) (premise_lt_gen A p)]
  rfl

end Proof

/-! ## Proofs and provability in a theory

The theory is represented by a numerical membership test. `T A = 1` means that formula code `A`
is an axiom of `T`.

- `isProof L T prf` checks the rules and membership in `T` in one traversal.
- `IsProofOf L T A prf` states that `prf` is an accepted proof with conclusion `A`.
- `Provable L T A` states that some proof code satisfies `IsProofOf L T A`.
-/

/--
`isProof L T prf` checks tree code `prf` in language code `L` over theory `T`. A hypothesis leaf
requires `T A = 1`; an axiom leaf uses `isLogicalAxiom L A`. Other nodes check their inference rule
and premises. Theory axioms and the conclusion `Proof.conclusion prf` may contain surrounding
variable positions, with theory axioms understood universally.
-/
def isProof (L : Nat) (T : Nat → Nat) : Nat → Nat :=
  Proof.rec (isLogicalAxiom L) (fun A => eqb (T A) 1)
    (fun A p q x y => band (band x y)
      (eqb (Proof.conclusion p) (Formula.imp (Proof.conclusion q) A)))
    (fun A p x => band x (eqb A (Formula.all (Proof.conclusion p))))

theorem isProof_zero (L : Nat) (T : Nat → Nat) : isProof L T 0 = 0 := rfl

theorem isProof_axiom_eq (L : Nat) (T : Nat → Nat) : ∀ A,
    isProof L T (Proof.axiom A) = isLogicalAxiom L A := by
  intro A
  rw [isProof, Proof.rec_axiom _ _ _ _]

theorem isProof_hypothesis_eq (L : Nat) (T : Nat → Nat) : ∀ A,
    isProof L T (Proof.hypothesis A) = eqb (T A) 1 := by
  intro A
  rw [isProof, Proof.rec_hypothesis _ _ _ _]

theorem isProof_mp_eq (L : Nat) (T : Nat → Nat) : ∀ A p q,
    isProof L T (Proof.mp A p q) = band (band (isProof L T p) (isProof L T q))
      (eqb (Proof.conclusion p) (Formula.imp (Proof.conclusion q) A)) := by
  intro A p q
  rw [isProof, Proof.rec_mp _ _ _ _]
  rfl

theorem isProof_gen_eq (L : Nat) (T : Nat → Nat) : ∀ A p,
    isProof L T (Proof.gen A p) = band (isProof L T p)
      (eqb (Formula.all A) (Formula.all (Proof.conclusion p))) := by
  intro A p
  rw [isProof, Proof.rec_gen _ _ _ _]
  rfl

theorem isProof_node_eq (L : Nat) (T : Nat → Nat) : ∀ k A children,
    isProof L T (S (pair k (pair A children))) =
      ite (eqb k 0) (ite (eqb children 0) (isLogicalAxiom L A) 0)
        (ite (eqb k 1) (ite (eqb children 0) (eqb (T A) 1) 0)
          (ite (eqb k 2)
            (band (band (isProof L T (unpairLeft children))
              (isProof L T (unpairRight children)))
              (eqb (Proof.conclusion (unpairLeft children))
                (Formula.imp (Proof.conclusion (unpairRight children)) A)))
            (ite (eqb k 3) (band (isProof L T children)
              (eqb A (Formula.all (Proof.conclusion children)))) 0))) := by
  intro k A children
  have hc : children < S (pair k (pair A children)) :=
    lt_of_le_of_lt _ _ _
      (le_trans _ _ _ (right_le_pair A children) (right_le_pair k (pair A children)))
      (lt_succ_self (pair k (pair A children)))
  have hl := lt_of_le_of_lt _ _ _ (unpairLeft_le children) hc
  have hr := lt_of_le_of_lt _ _ _ (unpairRight_le children) hc
  rw [isProof, Proof.rec, covrec, Proof.rule, Proof.conclusion, Proof.premises,
    pred_succ, unpairLeft_pair, unpairRight_pair, unpairLeft_pair, unpairRight_pair,
    ite_succ]
  rw [Sequence.rget_generate _ _ _ hl, Sequence.rget_generate _ _ _ hr,
    Sequence.rget_generate _ _ _ hc]
  rfl

theorem isProof_bool (L : Nat) (T : Nat → Nat) : ∀ prf, IsBool (isProof L T prf) := by
  intro prf
  unfold isProof Proof.rec covrec
  have hz : IsBool 0 := by left; rfl
  exact ite_bool _ _ _ (ite_bool _ _ _
    (ite_bool _ _ _ (isLogicalAxiom_bool L _) hz)
    (ite_bool _ _ _ (ite_bool _ _ _ (eqb_bool _ _) hz)
      (ite_bool _ _ _ (band_bool _ _) (ite_bool _ _ _ (band_bool _ _) hz)))) hz

/-- `IsProofOf L T A p` states that proof code `p` is accepted in language `L` over theory `T`
and has conclusion formula code `A`. Its two numerical equations form a quantifier-free predicate,
suitable for induction on proof-code builders. -/
def IsProofOf (L : Nat) (T : Nat → Nat) : Nat → Nat → QFProp :=
  fun A p => isProof L T p = 1 ∧ Proof.conclusion p = A

/--
`Provable L T A` states that formula code `A` has a checked proof in language code `L` over
theory `T`.
-/
def Provable (L : Nat) (T : Nat → Nat) : Nat → Prop := fun A =>
  ∃ prf, IsProofOf L T A prf

theorem IsProofOf.provable (L : Nat) (T : Nat → Nat) : ∀ A p,
    IsProofOf L T A p → Provable L T A := fun A p h => (p, h)

/-! ## Construction of checked proofs

The proof-construction lemmas justify the four inference rules for checked proof trees.
-/

theorem isProof_axiom (L : Nat) (T : Nat → Nat) : ∀ A,
    isLogicalAxiom L A = 1 → isProof L T (Proof.axiom A) = 1 := by
  intro A h
  rw [isProof_axiom_eq L T, h]

theorem isProof_hypothesis (L : Nat) (T : Nat → Nat) : ∀ A,
    T A = 1 → isProof L T (Proof.hypothesis A) = 1 := by
  intro A ht
  rw [isProof_hypothesis_eq L T, ht]
  rfl

theorem isProof_mp (L : Nat) (T : Nat → Nat) : ∀ A p q,
    isProof L T p = 1 → isProof L T q = 1 →
    Proof.conclusion p = Formula.imp (Proof.conclusion q) A →
    isProof L T (Proof.mp A p q) = 1 := by
  intro A p q hp hq he
  rw [isProof_mp_eq L T, hp, hq, he, eqb_self]
  rfl

theorem isProof_gen (L : Nat) (T : Nat → Nat) : ∀ A p,
    isProof L T p = 1 → Proof.conclusion p = A → isProof L T (Proof.gen A p) = 1 := by
  intro A p hp he
  rw [isProof_gen_eq L T, hp, he, eqb_self]
  rfl

theorem IsProofOf.mp (L : Nat) (T : Nat → Nat) : ∀ A B p q,
    IsProofOf L T (Formula.imp A B) p → IsProofOf L T A q →
      IsProofOf L T B (Proof.mp B p q) := by
  intro A B p q hp hq
  constructor
  · apply isProof_mp L T B p q (and_left hp) (and_left hq)
    rw [and_right hp, and_right hq]
  · exact Proof.conclusion_mp B p q

theorem IsProofOf.gen (L : Nat) (T : Nat → Nat) : ∀ A p,
    IsProofOf L T A p → IsProofOf L T (Formula.all A) (Proof.gen A p) := by
  intro A p hp
  exact (isProof_gen L T A p (and_left hp) (and_right hp), Proof.conclusion_gen A p)

theorem IsProofOf.mp' (L : Nat) (T : Nat → Nat) : ∀ A B p q,
    IsProofOf L T (Formula.imp A B) p → IsProofOf L T A q →
      IsProofOf L T B (Proof.mp' L p q) := by
  intro A B p q hp hq
  rw [Proof.mp', and_right hp, Formula.arg_imp, unpairRight_pair]
  exact IsProofOf.mp L T A B p q hp hq

/-! ## Provability rules and logical axioms

The provability lemmas justify the inference rules and logical axiom instances, with congruence
restricted to symbols in the language.
-/

theorem Provable.axiom (L : Nat) (T : Nat → Nat) : ∀ A,
    isLogicalAxiom L A = 1 → Provable L T A :=
  fun A h => (Proof.axiom A, isProof_axiom L T A h, Proof.conclusion_axiom A)

theorem Provable.hypothesis (L : Nat) (T : Nat → Nat) : ∀ A,
    T A = 1 → Provable L T A :=
  fun A h => (Proof.hypothesis A, isProof_hypothesis L T A h, Proof.conclusion_hypothesis A)

theorem Provable.mp (L : Nat) (T : Nat → Nat) : ∀ A B,
    Provable L T (Formula.imp A B) → Provable L T A → Provable L T B := by
  rintro A B (p, hp, ep) (q, hq, eq)
  exists Proof.mp B p q
  constructor
  · apply isProof_mp L T B p q hp hq
    rw [eq]
    exact ep
  · exact Proof.conclusion_mp B p q

theorem Provable.gen (L : Nat) (T : Nat → Nat) : ∀ A,
    Provable L T A → Provable L T (Formula.all A) := by
  rintro A (p, hp, ep)
  exact (Proof.gen A p, isProof_gen L T A p hp ep, Proof.conclusion_gen A p)

namespace Provable

theorem implication (L : Nat) (T : Nat → Nat) (A B : Nat) :
    Provable L T (Formula.imp A (Formula.imp B A)) :=
  FOL.Provable.axiom L T _ (isLogicalAxiom_of_implication L A B)

theorem implicationDistribution (L : Nat) (T : Nat → Nat) (A B C : Nat) :
    Provable L T (Formula.imp (Formula.imp A (Formula.imp B C))
      (Formula.imp (Formula.imp A B) (Formula.imp A C))) :=
  FOL.Provable.axiom L T _ (isLogicalAxiom_of_implicationDistribution L A B C)

theorem contraposition (L : Nat) (T : Nat → Nat) (A B : Nat) :
    Provable L T
      (Formula.imp (Formula.imp (Formula.neg A) (Formula.neg B)) (Formula.imp B A)) :=
  FOL.Provable.axiom L T _ (isLogicalAxiom_of_contraposition L A B)

theorem quantifierImplication (L : Nat) (T : Nat → Nat) (A B : Nat) :
    Provable L T (Formula.imp (Formula.all (Formula.imp (Formula.shift L A) B))
      (Formula.imp A (Formula.all B))) :=
  FOL.Provable.axiom L T _ (isLogicalAxiom_of_quantifierImplication L A B)

theorem reflexivity (L : Nat) (T : Nat → Nat) (t : Nat) :
    Provable L T (Formula.equal L t t) :=
  FOL.Provable.axiom L T _ (isLogicalAxiom_of_reflexivity L t)

theorem symmetry (L : Nat) (T : Nat → Nat) (s t : Nat) :
    Provable L T (Formula.imp (Formula.equal L s t) (Formula.equal L t s)) :=
  FOL.Provable.axiom L T _ (isLogicalAxiom_of_symmetry L s t)

theorem transitivity (L : Nat) (T : Nat → Nat) (s t u : Nat) :
    Provable L T (Formula.imp (Formula.equal L s t)
      (Formula.imp (Formula.equal L t u) (Formula.equal L s u))) :=
  FOL.Provable.axiom L T _ (isLogicalAxiom_of_transitivity L s t u)

theorem functionCongruence (L : Nat) (T : Nat → Nat) (j xs ys : Nat) :
    Language.IsFunction L j →
      Provable L T (Formula.equalPremises L (Language.functionSymbolArity L j) xs ys
        (Formula.equal L (Term.app L j xs) (Term.app L j ys))) :=
  fun h => FOL.Provable.axiom L T _ (isLogicalAxiom_of_functionCongruence L j xs ys h)

theorem relationCongruence (L : Nat) (T : Nat → Nat) (j xs ys : Nat) :
    Language.IsRelation L j →
      Provable L T (Formula.equalPremises L (Language.relationSymbolArity L j) xs ys
        (Formula.imp (Formula.rel L j xs) (Formula.rel L j ys))) :=
  fun h => FOL.Provable.axiom L T _ (isLogicalAxiom_of_relationCongruence L j xs ys h)

end Provable

/-! ## Universal instantiation

Universal instantiation holds for every formula and term code because the bounded axiom search
can use either the substituted term or the term with code `0`.
-/

namespace Term

/-- Instantiating position `0` by `t` in a term at binder depth `d` either gives a code at least
`t`, or gives the same code as instantiating by `0`. -/
theorem instantiateAt_dichotomy : ∀ L t d s,
    t ≤ subst (instantiateAt L 0 t d) L s ∨
      subst (instantiateAt L 0 t d) L s = subst (instantiateAt L 0 0 d) L s := by
  intro L t d
  apply induction_of_bool
    (fun s => t ≤ subst (instantiateAt L 0 t d) L s ∨
      subst (instantiateAt L 0 t d) L s = subst (instantiateAt L 0 0 d) L s)
    (fun s => bor (leb t (subst (instantiateAt L 0 t d) L s))
      (eqb (subst (instantiateAt L 0 t d) L s) (subst (instantiateAt L 0 0 d) L s))) L
  · intro s
    exact le_or_eq_bool t (subst (instantiateAt L 0 t d) L s) (subst (instantiateAt L 0 0 d) L s)
  · intro j hj
    right
    rw [subst_const (instantiateAt L 0 t d) L j hj, subst_const (instantiateAt L 0 0 d) L j hj]
  · intro i
    rw [subst_var (instantiateAt L 0 t d), subst_var (instantiateAt L 0 0 d)]
    change
      t ≤ ite (ltb i d) (var L i)
        (ite (eqb (i - d) 0) (shift L d t) (var L (ite (ltb 0 (i - d)) (pred i) i))) ∨
      ite (ltb i d) (var L i)
        (ite (eqb (i - d) 0) (shift L d t) (var L (ite (ltb 0 (i - d)) (pred i) i))) =
      ite (ltb i d) (var L i)
        (ite (eqb (i - d) 0) (shift L d 0) (var L (ite (ltb 0 (i - d)) (pred i) i)))
    by_cases h₁ : ltb i d = 0
    · rw [h₁, ite_zero, ite_zero]
      by_cases h₂ : eqb (i - d) 0 = 0
      · right
        rw [h₂, ite_zero, ite_zero]
      · left
        rw [ite_of_ne_zero (eqb (i - d) 0) _ _ h₂]
        exact le_shift L d t
    · right
      rw [ite_of_ne_zero (ltb i d) _ _ h₁, ite_of_ne_zero (ltb i d) _ _ h₁]
  · intro j args hj ih
    rw [subst_app (instantiateAt L 0 t d) L j args hj,
      subst_app (instantiateAt L 0 0 d) L j args hj]
    rcases Tuple.map_dichotomy (subst (instantiateAt L 0 t d) L)
        (subst (instantiateAt L 0 0 d) L) t (Language.functionSymbolArity L j) args
        (fun i hi => ih i hi) with hm | hm
    · left
      have h := args_lt_app L j
        (Tuple.map (subst (instantiateAt L 0 t d) L) (Language.functionSymbolArity L j) args)
      exact le_trans t _ _ hm (le_of_lt _ _ h)
    · right
      rw [hm]

end Term

namespace Formula

/-- Instantiating position `0` by `t` in a formula at binder depth `d` either gives a code at
least `t`, or gives the same code as instantiating by `0`. -/
theorem instantiate_dichotomy : ∀ L t A d,
    (t ≤ substWithDepth (Term.instantiateAt L 0 t) L A d ∨
      substWithDepth (Term.instantiateAt L 0 t) L A d =
        substWithDepth (Term.instantiateAt L 0 0) L A d) := by
  intro L t
  apply inductionWithDepth_of_bool
    (fun A d => t ≤ substWithDepth (Term.instantiateAt L 0 t) L A d ∨
      substWithDepth (Term.instantiateAt L 0 t) L A d =
        substWithDepth (Term.instantiateAt L 0 0) L A d)
    (fun A d => bor (leb t (substWithDepth (Term.instantiateAt L 0 t) L A d))
      (eqb (substWithDepth (Term.instantiateAt L 0 t) L A d)
        (substWithDepth (Term.instantiateAt L 0 0) L A d))) L
  · intro A d
    exact le_or_eq_bool t (substWithDepth (Term.instantiateAt L 0 t) L A d)
      (substWithDepth (Term.instantiateAt L 0 0) L A d)
  · intro d
    right
    rw [substWithDepth_falsum (Term.instantiateAt L 0 t) L d,
      substWithDepth_falsum (Term.instantiateAt L 0 0) L d]
  · intro a b d
    rw [substWithDepth_equal (Term.instantiateAt L 0 t) L a b d,
      substWithDepth_equal (Term.instantiateAt L 0 0) L a b d]
    rcases Term.instantiateAt_dichotomy L t d a with ha | ha
    · left
      exact le_trans t _ _ ha (le_equal_left L _ _)
    · rcases Term.instantiateAt_dichotomy L t d b with hb | hb
      · left
        exact le_trans t _ _ hb (le_equal_right L _ _)
      · right
        rw [ha, hb]
  · intro j xs d hj
    rw [substWithDepth_rel (Term.instantiateAt L 0 t) L j xs d hj,
      substWithDepth_rel (Term.instantiateAt L 0 0) L j xs d hj]
    rcases Tuple.map_dichotomy (Term.subst (Term.instantiateAt L 0 t d) L)
        (Term.subst (Term.instantiateAt L 0 0 d) L) t
        (Language.relationSymbolArity L j) xs
        (fun i hi => Term.instantiateAt_dichotomy L t d
          (Tuple.get (Language.relationSymbolArity L j) xs i)) with hm | hm
    · left
      exact le_trans t _ _ hm (args_le_rel L j _)
    · right
      rw [hm]
  · intro A B d hA hB
    rw [substWithDepth_imp (Term.instantiateAt L 0 t) L A B d,
      substWithDepth_imp (Term.instantiateAt L 0 0) L A B d]
    rcases hA d (le_refl d) with ha | ha
    · left
      exact le_trans t _ _ ha (le_of_lt _ _ (left_lt_imp _ _))
    · rcases hB d (le_refl d) with hb | hb
      · left
        exact le_trans t _ _ hb (le_of_lt _ _ (right_lt_imp _ _))
      · right
        rw [ha, hb]
  · intro A d ih
    rw [substWithDepth_all (Term.instantiateAt L 0 t) L A d,
      substWithDepth_all (Term.instantiateAt L 0 0) L A d]
    rcases ih (S d) (le_refl (S d)) with ha | ha
    · left
      exact le_trans t _ _ ha (le_of_lt _ _ (body_lt_all _))
    · right
      rw [ha]

/-- Either `t` is at most the instance `A[t]`, or `A[t]` is the instance `A[0]`. -/
theorem instantiate_bound : ∀ L A t,
    t ≤ instantiate L A t ∨ instantiate L A t = instantiate L A 0 :=
  fun L A t => instantiate_dichotomy L t A 0

end Formula

/-- Every instance `(∀ A) → A[t]` passes the test for the instantiation axiom: the search for
the term succeeds with `t` or with `0`. -/
theorem isLogicalAxiom_of_instantiate : ∀ L A t,
    isLogicalAxiom L (Formula.imp (Formula.all A) (Formula.instantiate L A t)) = 1 := by
  intro L A t
  rcases Formula.instantiate_bound L A t with h | h
  · exact isLogicalAxiom_of_instantiation L A t
      (le_trans t (Formula.instantiate L A t) _ h
        (le_of_lt _ _ (Formula.right_lt_imp (Formula.all A) (Formula.instantiate L A t))))
  · rw [h]
    exact isLogicalAxiom_of_instantiation L A 0 (zero_le _)

namespace Provable

/-- Universal instantiation for every formula code and every term code. -/
theorem instantiate (L : Nat) (T : Nat → Nat) (A t : Nat) :
    Provable L T (Formula.imp (Formula.all A) (Formula.instantiate L A t)) :=
  FOL.Provable.axiom L T _ (isLogicalAxiom_of_instantiate L A t)

end Provable

end FOL

extract_witness FOL.Provable.contraposition FOL.Provable.functionCongruence FOL.Provable.implication
  FOL.Provable.implicationDistribution FOL.Provable.instantiate FOL.Provable.quantifierImplication
  FOL.Provable.reflexivity FOL.Provable.symmetry FOL.Provable.transitivity

end
