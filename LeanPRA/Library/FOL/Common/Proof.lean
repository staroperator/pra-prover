module

public import LeanPRA.Library.FOL.Common.LogicalAxiom

/-!
# Numerical Hilbert proof trees

For a first-order language `L` and a theory `T` of formulas, the Hilbert proof system has
four rules:

- Logical axiom: `T ⊢ A` if `A` is an instance of a schema in `LogicalAxiom.lean`.
- Hypothesis: `T ⊢ A` if `A ∈ T`.
- Modus ponens (MP): `T ⊢ A` if `T ⊢ B → A` and `T ⊢ B`.
- Generalization (GEN): `T ⊢ ∀ A` if `T ⊢ A`, binding surrounding position `0`.

Proofs are finite trees whose leaves are logical axioms or theory hypotheses. Theory axioms and
proof conclusions may contain surrounding variable positions, with theory axioms understood
universally, so GEN applies at any node.

Proof trees are encoded in `Nat`. Each node stores a rule tag, its conclusion formula, and
its premise subtrees, using `S (pair rule (pair conclusion premises))`:

- `Proof.axiom A` is encoded as `S (pair 0 (pair A 0))`.
- `Proof.hypothesis A` is encoded as `S (pair 1 (pair A 0))`.
- `Proof.mp A p q` is encoded as `S (pair 2 (pair A (pair p q)))`.
- `Proof.gen A p` is encoded as `S (pair 3 (pair (Formula.all A) p))`.

Here `A` is a formula code, and `p`, `q` are complete subtree codes. In `Proof.mp`, `p` proves
`B → A` and `q` proves `B`; in `Proof.gen`, `p` proves `A`. The theory is represented by a
numerical membership test: `T A = 1` means that formula code `A` is an axiom of `T`.

Taking the predecessor and unpairing recovers the node fields through `Proof.rule`,
`Proof.conclusion`, and `Proof.premises`. Code `0`, rule tags above `3`, and leaves with nonzero
premise data are invalid. Every subtree code is smaller than its parent, so the tree can be
traversed by numerical course-of-values recursion. The main operations are:

- `Proof.rec` combines the results from premise subtrees according to the rule at each node.
- `isProof L T prf` checks the rules and membership in `T` in one traversal.
- `Provable L T A` states that a checked proof of `A` exists.
-/

@[expose] public section

pra

namespace FOL

/-! ## Proof trees and recursion -/

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

/-! ## Proofs and provability in a theory -/

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

theorem isProof_bool (L : Nat) (T : Nat → Nat) : ∀ prf, IsBool (isProof L T prf) := by
  intro prf
  by_cases hz : prf = 0
  · rw [hz, isProof_zero L T]
    left; rfl
  rw [isProof, Proof.rec, covrec, ite_of_ne_zero prf _ _ hz]
  by_cases h₀ : Proof.rule prf = 0
  · rw [h₀]
    by_cases hc : Proof.premises prf = 0
    · rw [hc]
      exact isLogicalAxiom_bool L (Proof.conclusion prf)
    · rw [and_right (eqb_eq_zero (Proof.premises prf) 0) hc]
      left; rfl
  rw [and_right (eqb_eq_zero (Proof.rule prf) 0) h₀]
  by_cases h₁ : Proof.rule prf = 1
  · rw [h₁]
    by_cases hc : Proof.premises prf = 0
    · rw [hc]
      exact eqb_bool _ _
    · rw [and_right (eqb_eq_zero (Proof.premises prf) 0) hc]
      left; rfl
  rw [and_right (eqb_eq_zero (Proof.rule prf) 1) h₁]
  by_cases h₂ : Proof.rule prf = 2
  · rw [h₂]
    exact band_bool _ _
  rw [and_right (eqb_eq_zero (Proof.rule prf) 2) h₂]
  by_cases h₃ : Proof.rule prf = 3
  · rw [h₃]
    exact band_bool _ _
  rw [and_right (eqb_eq_zero (Proof.rule prf) 3) h₃]
  left; rfl

/--
`Provable L T A` states that formula code `A` has a checked proof in language code `L` over
theory `T`.
-/
def Provable (L : Nat) (T : Nat → Nat) : Nat → Prop := fun A =>
  ∃ prf, isProof L T prf = 1 ∧ Proof.conclusion prf = A

/-! ## Construction of checked proofs -/

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

end FOL

end
