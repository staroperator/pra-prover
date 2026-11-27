module

public import PRAProver.Library.Computability.Primrec
public import PRAProver.Library.FOL.Arithmetic.Representation.Composition
public import PRAProver.Library.FOL.Arithmetic.Representation.Recursion

/-!
# Graph formulas for primitive-recursive programs

`Arithmetic.rep e` constructs an arithmetic formula from the program code `e`. Its free positions
are output at zero and input at one. Inputs with several components use Cantor pairing, as in
`Primrec.Computation`. The recursion formula selects the least code of a computation sequence.

- `Arithmetic.rep_zero`, `Arithmetic.rep_succ`, `Arithmetic.rep_left`, `Arithmetic.rep_right`,
  `Arithmetic.rep_pair`, `Arithmetic.rep_comp`, and `Arithmetic.rep_rec` give the formula for each
  primitive-recursive operation.
- `Q.rep_num_iff` proves the graph's output equivalence at every numeral input from a computation
  of the program. `Q.represents` applies this to a function computed by that program.
- `PA.rep_total` and `PA.rep_unique` give totality and uniqueness of the same graph for
  every numerical program code.

Supporting Q and PA closure lemmas are grouped with their operations in the other
representation modules.
-/

namespace FOL

set_option pra.maxDepth 8192

/-! ## Graph formulas and proof checks -/

pra

namespace Arithmetic

/-- `rep e` constructs the graph formula of the unary primitive-recursive program encoded by `e` by
course-of-values recursion on the expression code `e`. -/
fol_def rep over Arithmetic (e : Nat) : formula of 2 :=
  ${covrec (fun e history =>
      let k := Primrec.Code.tag e;
      let args := Primrec.Code.args e;
      let p := Sequence.rget history (unpairLeft args);
      let q := Sequence.rget history (unpairRight args);
      let y := Term.var language 0;
      let x := Term.var language 1;
      ite (eqb k 0) (constGraph 0 y x)
        (ite (eqb k 1) (succGraph y x)
          (ite (eqb k 2) (leftGraph y x)
            (ite (eqb k 3) (rightGraph y x)
              (ite (eqb k 4) (pairCompGraph (FOL.Formula.subst (FOL.liftSubst (FOL.shiftSubst
                  language 2) language 2) language p)
                  (FOL.Formula.subst (FOL.liftSubst (FOL.shiftSubst language 2)
                  language 2) language q) y x)
                (ite (eqb k 5) (compGraph (FOL.Formula.subst (FOL.liftSubst (FOL.shiftSubst
                    language 2) language 2) language p)
                    (FOL.Formula.subst (FOL.liftSubst (FOL.shiftSubst language 2)
                    language 2) language q) y x)
                  (leastRecursionGraph
                    (Formula.subst (liftSubst (shiftSubst language 2) language 2) language p)
                    (Formula.subst (liftSubst (shiftSubst language 2) language 2) language q)
                    y x))))))) e}

theorem rep_zero : rep Primrec.Code.zero =
    constGraph 0 (Term.var language 0) (Term.var language 1) := rfl

theorem rep_succ : rep Primrec.Code.succ =
    succGraph (Term.var language 0) (Term.var language 1) := rfl

theorem rep_left : rep Primrec.Code.left =
    leftGraph (Term.var language 0) (Term.var language 1) := rfl

theorem rep_right : rep Primrec.Code.right =
    rightGraph (Term.var language 0) (Term.var language 1) := rfl

theorem rep_pair :
    ∀ f g, rep (Primrec.Code.pair f g) = pairCompGraph (FOL.Formula.subst (FOL.liftSubst
    (FOL.shiftSubst language 2) language 2) language (rep f))
    (FOL.Formula.subst (FOL.liftSubst (FOL.shiftSubst language 2) language
    2) language (rep g)) (Term.var language 0) (Term.var language 1) := by
  intro f g
  rw [rep, covrec, Primrec.Code.tag_pair f g,
        Primrec.Code.args_pair f g, unpairLeft_pair, unpairRight_pair]
  rw [Sequence.rget_generate _ f _ (Primrec.Code.left_lt_pair f g),
    Sequence.rget_generate _ g _ (Primrec.Code.right_lt_pair f g)]
  rfl

theorem rep_comp :
    ∀ f g, rep (Primrec.Code.comp f g) = compGraph (FOL.Formula.subst (FOL.liftSubst
    (FOL.shiftSubst language 2) language 2) language (rep f))
    (FOL.Formula.subst (FOL.liftSubst (FOL.shiftSubst language 2) language
    2) language (rep g)) (Term.var language 0) (Term.var language 1) := by
  intro f g
  rw [rep, covrec, Primrec.Code.tag_comp f g,
        Primrec.Code.args_comp f g, unpairLeft_pair, unpairRight_pair]
  rw [Sequence.rget_generate _ f _ (Primrec.Code.left_lt_comp f g),
    Sequence.rget_generate _ g _ (Primrec.Code.right_lt_comp f g)]
  rfl

theorem rep_rec :
    ∀ f g, rep (Primrec.Code.rec f g) = leastRecursionGraph
    (Formula.subst (liftSubst (shiftSubst language 2) language 2) language (rep f))
    (Formula.subst (liftSubst (shiftSubst language 2) language 2) language (rep g))
    (Term.var language 0) (Term.var language 1) := by
  intro f g
  rw [rep, covrec, Primrec.Code.tag_rec f g,
        Primrec.Code.args_rec f g, unpairLeft_pair, unpairRight_pair]
  rw [Sequence.rget_generate _ f _ (Primrec.Code.left_lt_rec f g),
    Sequence.rget_generate _ g _ (Primrec.Code.right_lt_rec f g)]
  rfl

/-- `(isTotal p)` states that every input has an output related to it by `p`. -/
fol_def isTotal over Arithmetic (p : formula of 2) : formula := ∀ x, ∃ y, p(x, y)

/-- `(isUnique p)` states that any two outputs related by `p` to the same input are equal. -/
fol_def isUnique over Arithmetic (p : formula of 2) : formula :=
  ∀ x y z, p(x, y) → p(x, z) → y = z

/-- `proofCheck axioms A p` returns `1` when `p` is a valid proof of `A` from `axioms`, and `0`
otherwise. -/
def proofCheck (axioms : Nat → Nat) (A p : Nat) : Nat :=
  band (eqb (isProof language axioms p) 1) (eqb (Proof.conclusion p) A)

theorem proofCheck_iff (axioms : Nat → Nat) :
    ∀ A p, ¬ proofCheck axioms A p = 0 ↔ IsProofOf language axioms A p := by
  intro A p
  let a := eqb (isProof language axioms p) 1
  let b := eqb (Proof.conclusion p) A
  constructor
  · intro h
    have hb : band a b = 1 := and_right (bool_eq_one (band a b) (band_bool a b)) h
    rcases and_left (band_eq_one a b) hb with (ha, hb)
    exact (and_left (eqb_ne_zero _ _) ha, and_left (eqb_ne_zero _ _) hb)
  · rintro (ha, hb)
    apply and_left (bool_eq_one (band a b) (band_bool a b))
    apply and_right (band_eq_one a b)
    exact (and_right (eqb_ne_zero _ _) ha, and_right (eqb_ne_zero _ _) hb)

end Arithmetic

/-! ## Numeralwise representation in Q -/

namespace Q

open Arithmetic

theorem representsAt_rep_zero (x y t : Nat) :
    Primrec.Computation.Evaluates Primrec.Code.zero x y t →
    (Q ⊢ ${representsAt (rep Primrec.Code.zero) x y}) := by
  intro h
  have hy := Primrec.Computation.output_zero_of_evaluates x y t h
  rw [hy, rep_zero, representsAt]
  pexact constGraph_num_iff 0 x

theorem representsAt_rep_succ (x y t : Nat) :
    Primrec.Computation.Evaluates Primrec.Code.succ x y t →
    (Q ⊢ ${representsAt (rep Primrec.Code.succ) x y}) := by
  intro h
  have hy := Primrec.Computation.output_succ_of_evaluates x y t h
  rw [hy, rep_succ, representsAt]
  pexact succGraph_num_iff x

theorem representsAt_rep_left (x y t : Nat) :
    Primrec.Computation.Evaluates Primrec.Code.left x y t →
    (Q ⊢ ${representsAt (rep Primrec.Code.left) x y}) := by
  intro h
  have hy := Primrec.Computation.output_left_of_evaluates x y t h
  rw [hy, rep_left, representsAt]
  pexact leftGraph_num_iff x

theorem representsAt_rep_right (x y t : Nat) :
    Primrec.Computation.Evaluates Primrec.Code.right x y t →
    (Q ⊢ ${representsAt (rep Primrec.Code.right) x y}) := by
  intro h
  have hy := Primrec.Computation.output_right_of_evaluates x y t h
  rw [hy, rep_right, representsAt]
  pexact rightGraph_num_iff x

extract_witness representsAt_rep_zero representsAt_rep_succ representsAt_rep_left
  representsAt_rep_right

/-- `computationCheck sentence t proof` checks that `proof` proves `sentence t` in Q whenever `t` is
a valid computation tree. -/
def computationCheck (sentence : Nat → Nat) : Nat → Nat → Nat := fun t proof =>
  ite (eqb (Primrec.Computation.isValid t) 1) (proofCheck isAxiom (sentence t) proof) 1

theorem computationCheck_iff (sentence : Nat → Nat) :
    ∀ t proof, ¬ computationCheck sentence t proof = 0 ↔
    (Primrec.Computation.isValid t = 1 → IsProofOf language isAxiom (sentence t) proof) := by
  intro t proof
  by_cases ht : Primrec.Computation.isValid t = 1
  · have htq := and_right (eqb_eq_one (Primrec.Computation.isValid t) 1) ht
    rw [computationCheck, htq]
    constructor
    · intro h hv
      exact and_left (proofCheck_iff isAxiom _ proof) h
    · intro h
      exact and_right (proofCheck_iff isAxiom _ proof) (h ht)
  · have htq := and_right (eqb_eq_zero (Primrec.Computation.isValid t) 1) ht
    rw [computationCheck, htq]
    constructor
    · intro h hv
      exact false_elim (ht hv)
    · intro h
      exact _root_.succ_ne_zero 0

theorem representsAt_rep_pair_of_isProofOf (f g x u v y a b : Nat) :
    y = pair u v → IsProofOf language isAxiom (representsAt (rep f) x u) a → IsProofOf language
    isAxiom (representsAt (rep g) x v) b →
    (Q ⊢ ${representsAt (rep (Primrec.Code.pair f g)) x y}) := by
  intro hy ha hb
  have leftResult : Q ⊢ ${representsAt (rep f) x u} := (a, ha)
  have rightResult : Q ⊢ ${representsAt (rep g) x v} := (b, hb)
  rw [representsAt] at leftResult
  rw [representsAt] at rightResult
  rw [hy, rep_pair, representsAt]
  papply pairCompGraph_num_iff (rep f) (rep g) x u v
  · pexact leftResult
  · pexact rightResult

theorem representsAt_rep_comp_of_isProofOf (f g x u y a b : Nat) :
    IsProofOf language isAxiom (representsAt (rep g) x u) a → IsProofOf language isAxiom
    (representsAt (rep f) u y) b → (Q ⊢ ${representsAt (rep (Primrec.Code.comp f g)) x y}) :=
    by
  intro ha hb
  have inner : Q ⊢ ${representsAt (rep g) x u} := (a, ha)
  have outer : Q ⊢ ${representsAt (rep f) u y} := (b, hb)
  rw [representsAt] at inner
  rw [representsAt] at outer
  rw [rep_comp, representsAt]
  papply compGraph_num_iff (rep f) (rep g) x u y
  · pexact inner
  · pexact outer

theorem stepRepresentsAt_of_isProofOf (q x i u v proof : Nat) :
    IsProofOf language isAxiom (representsAt q (pair x (pair i u)) v) proof →
    (Q ⊢ ${stepRepresentsAt (recStepFormula q) x i u v}) := by
  intro h
  have step : Q ⊢ ${representsAt q (pair x (pair i u)) v} := (proof, h)
  rw [representsAt] at step
  rw [stepRepresentsAt, recStepFormula]
  papply recStepGraph_num_iff ${q} x i u v
  pexact step

extract_witness representsAt_rep_pair_of_isProofOf representsAt_rep_comp_of_isProofOf
  stepRepresentsAt_of_isProofOf

theorem representsAt_rep_rec_of_isProofOf (f g x n y t history : Nat) :
    Primrec.Computation.Evaluates (Primrec.Code.rec f g) (pair x n) y t → (∀ u, u < t →
    Primrec.Computation.isValid u = 1 → IsProofOf language isAxiom (representsAt (rep
    (Primrec.Computation.program u)) (Primrec.Computation.input u) (Primrec.Computation.output u))
    (Sequence.rget history u)) →
    (Q ⊢ ${representsAt (rep (Primrec.Code.rec f g)) (pair x n) y}) := by
  intro ht earlier
  let values := Primrec.Computation.recValue t n
  let base := Primrec.Computation.recBaseTrace t n
  let proofs := fun i => stepRepresentsAt_of_isProofOf.witness (rep g) x i (values i) (values (S i))
    (Sequence.rget history (Primrec.Computation.recStepTrace t n i))
  have baseEvaluation := Primrec.Computation.recBaseTrace_evaluates f g x n y t ht
  rcases baseEvaluation with (hb, lessBase)
  rcases hb with (validBase, programBase, inputBase, outputBase)
  have baseChecked := earlier base lessBase validBase
  rw [programBase, inputBase, outputBase] at baseChecked
  have stepChecked : ∀ i, i < n → IsProofOf language isAxiom
      (stepRepresentsAt (recStepFormula (rep g)) x i (values i) (values (S i))) (proofs i) := by
    intro i hi
    let step := Primrec.Computation.recStepTrace t n i
    have stepEvaluation := Primrec.Computation.recStepTrace_evaluates f g x n y t i ht hi
    rcases stepEvaluation with (hs, lessStep)
    rcases hs with (validStep, programStep, inputStep, outputStep)
    have checked := earlier step lessStep validStep
    rw [programStep, inputStep, outputStep] at checked
    exact stepRepresentsAt_of_isProofOf.witness_correct (rep g) x i (values i) (values (S i))
      (Sequence.rget history step) checked
  have represented := leastRecursionGraph_num_iff_of_isProofOf values proofs (rep f) (rep g)
    x n (Sequence.rget history base) baseChecked stepChecked
  have last : values n = y := Primrec.Computation.recValue_last n y t
    (and_right (and_right (and_right ht)))
  rw [last] at represented
  rw [rep_rec, representsAt]
  pexact represented

extract_witness representsAt_rep_rec_of_isProofOf

/-- `representationProofStep t history` constructs the Q proof of numeral-instance representation
for computation tree `t` from the proof history `history` of smaller subtrees. -/
def representationProofStep : Nat → Nat → Nat := fun t history =>
  let e := Primrec.Computation.program t;
  let x := Primrec.Computation.input t;
  let y := Primrec.Computation.output t;
  let k := Primrec.Code.tag e;
  let args := Primrec.Code.args e;
  let f := unpairLeft args;
  let g := unpairRight args;
  let leftTree := Primrec.Computation.childLeft t;
  let rightTree := Primrec.Computation.childRight t;
  let a := Sequence.rget history leftTree;
  let b := Sequence.rget history rightTree;
  ite (eqb k 0) (representsAt_rep_zero.witness x y t)
    (ite (eqb k 1) (representsAt_rep_succ.witness x y t)
      (ite (eqb k 2) (representsAt_rep_left.witness x y t)
        (ite (eqb k 3) (representsAt_rep_right.witness x y t)
          (ite (eqb k 4)
            (representsAt_rep_pair_of_isProofOf.witness f g x (Primrec.Computation.output leftTree)
              (Primrec.Computation.output rightTree) y a b)
            (ite (eqb k 5)
              (representsAt_rep_comp_of_isProofOf.witness f g x (Primrec.Computation.output
                  leftTree) y a b)
              (representsAt_rep_rec_of_isProofOf.witness f g (unpairLeft x) (unpairRight x) y t
                  history))))))

/-- `representationProof t` constructs the Q proof of numeral-instance representation for a checked
computation tree `t`. -/
def representationProof : Nat → Nat := covrec representationProofStep

theorem representationProofStep_isProofOf :
    ∀ t xs, Sequence.length xs = t → (∀ u, u < t → Primrec.Computation.isValid u = 1 → IsProofOf
    language isAxiom (representsAt (rep (Primrec.Computation.program u))
    (Primrec.Computation.input u) (Primrec.Computation.output u)) (Sequence.rget xs u)) →
    Primrec.Computation.isValid t = 1 → IsProofOf language isAxiom (representsAt (rep
    (Primrec.Computation.program t)) (Primrec.Computation.input t) (Primrec.Computation.output t))
    (representationProofStep t xs) := by
  intro t xs hlen ih hv
  have evaluation : Primrec.Computation.Evaluates (Primrec.Computation.program t)
      (Primrec.Computation.input t) (Primrec.Computation.output t) t := (hv, rfl, rfl, rfl)
  have nonzero := Primrec.Computation.ne_zero_of_isValid t hv
  have leftLess := Primrec.Computation.childLeft_lt t nonzero
  have rightLess := Primrec.Computation.childRight_lt t nonzero
  rcases Primrec.Code.cases (Primrec.Computation.program t) with
    h0 | h1 | h2 | h3 | rest
  · rw [h0] at evaluation
    rw [representationProofStep, h0]
    exact representsAt_rep_zero.witness_correct (Primrec.Computation.input t)
        (Primrec.Computation.output t)
      t evaluation
  · rw [h1] at evaluation
    rw [representationProofStep, h1]
    exact representsAt_rep_succ.witness_correct (Primrec.Computation.input t)
        (Primrec.Computation.output t)
      t evaluation
  · rw [h2] at evaluation
    rw [representationProofStep, h2]
    exact representsAt_rep_left.witness_correct (Primrec.Computation.input t)
        (Primrec.Computation.output t)
      t evaluation
  · rw [h3] at evaluation
    rw [representationProofStep, h3]
    exact representsAt_rep_right.witness_correct (Primrec.Computation.input t)
        (Primrec.Computation.output t)
      t evaluation
  · rcases rest with (f, g, cases)
    rcases cases with hp | hc | hr
    · rw [hp] at evaluation
      have branches := Primrec.Computation.evaluates_pair_elim f g
        (Primrec.Computation.input t) (Primrec.Computation.output t) t evaluation
      rcases branches with (leftEvaluation, rightEvaluation, outputPair)
      rcases leftEvaluation with (leftValid, leftProgram, leftInput, leftOutput)
      rcases rightEvaluation with (rightValid, rightProgram, rightInput, rightOutput)
      have leftProof := ih (Primrec.Computation.childLeft t) leftLess leftValid
      have rightProof := ih (Primrec.Computation.childRight t) rightLess rightValid
      rw [leftProgram, leftInput] at leftProof
      rw [rightProgram, rightInput] at rightProof
      rw [representationProofStep, hp, Primrec.Code.tag_pair f g,
        Primrec.Code.args_pair f g, unpairLeft_pair, unpairRight_pair]
      exact representsAt_rep_pair_of_isProofOf.witness_correct f g (Primrec.Computation.input t)
        (Primrec.Computation.output (Primrec.Computation.childLeft t))
        (Primrec.Computation.output (Primrec.Computation.childRight t))
        (Primrec.Computation.output t) (Sequence.rget xs (Primrec.Computation.childLeft t))
        (Sequence.rget xs (Primrec.Computation.childRight t)) outputPair leftProof rightProof
    · rw [hc] at evaluation
      have branches := Primrec.Computation.evaluates_comp_elim f g
        (Primrec.Computation.input t) (Primrec.Computation.output t) t evaluation
      rcases branches with (leftEvaluation, rightEvaluation)
      rcases leftEvaluation with (leftValid, leftProgram, leftInput, leftOutput)
      rcases rightEvaluation with (rightValid, rightProgram, rightInput, rightOutput)
      have leftProof := ih (Primrec.Computation.childLeft t) leftLess leftValid
      have rightProof := ih (Primrec.Computation.childRight t) rightLess rightValid
      rw [leftProgram, leftInput] at leftProof
      rw [rightProgram, rightInput, rightOutput] at rightProof
      rw [representationProofStep, hc, Primrec.Code.tag_comp f g,
        Primrec.Code.args_comp f g, unpairLeft_pair, unpairRight_pair]
      exact representsAt_rep_comp_of_isProofOf.witness_correct f g (Primrec.Computation.input t)
        (Primrec.Computation.output (Primrec.Computation.childLeft t))
        (Primrec.Computation.output t) (Sequence.rget xs (Primrec.Computation.childLeft t))
        (Sequence.rget xs (Primrec.Computation.childRight t)) leftProof rightProof
    · rw [hr] at evaluation
      have recursion : Primrec.Computation.Evaluates (Primrec.Code.rec f g)
          (pair (unpairLeft (Primrec.Computation.input t))
            (unpairRight (Primrec.Computation.input t))) (Primrec.Computation.output t) t := by
        rw [pair_unpair]
        exact evaluation
      have checked := representsAt_rep_rec_of_isProofOf.witness_correct f g
        (unpairLeft (Primrec.Computation.input t))
        (unpairRight (Primrec.Computation.input t)) (Primrec.Computation.output t) t xs
        recursion ih
      rw [pair_unpair] at checked
      rw [representationProofStep, hr, Primrec.Code.tag_rec f g,
        Primrec.Code.args_rec f g, unpairLeft_pair, unpairRight_pair]
      exact checked

theorem representationProof_isProofOf :
    ∀ t, Primrec.Computation.isValid t = 1 → IsProofOf language isAxiom (representsAt (rep
    (Primrec.Computation.program t)) (Primrec.Computation.input t) (Primrec.Computation.output t))
    (representationProof t) := by
  intro t
  exact covrec_induction
    (fun t proof => Primrec.Computation.isValid t = 1 → IsProofOf language isAxiom
        (representsAt (rep (Primrec.Computation.program t))
          (Primrec.Computation.input t) (Primrec.Computation.output t)) proof)
    (computationCheck (fun t => representsAt (rep (Primrec.Computation.program t))
      (Primrec.Computation.input t) (Primrec.Computation.output t))) representationProofStep
    (computationCheck_iff (fun t => representsAt (rep (Primrec.Computation.program t))
      (Primrec.Computation.input t) (Primrec.Computation.output t)))
    representationProofStep_isProofOf t

/-- At each numeral input, Q identifies every output of the program's graph with the
numeral produced by a checked computation of that program. -/
theorem rep_num_iff (e n m : Nat) :
    Primrec.Evaluates e n m →
    (Q ⊢ ∀ y, ${rep e}[${num n}, y] ↔ y = ${num m}) := by
  rintro (t, valid, program, input, output)
  have checked := representationProof_isProofOf t valid
  rw [program, input, output] at checked
  have represented : Q ⊢ ${representsAt (rep e) n m} := (representationProof t, checked)
  rw [representsAt] at represented
  pexact represented

/-- The formula constructed from a code represents every function computed by that code. -/
theorem represents (f : Nat → Nat) (e : Nat) :
    Primrec.Encodes f e → Represents f (rep e) := by
  intro computes n
  exact rep_num_iff e n (f n) (computes n)

end Q

/-! ## Totality and uniqueness in PA -/

namespace PA

open Arithmetic

theorem isTotal_rep_zero : PA ⊢ ${isTotal (rep Primrec.Code.zero)} := by
  rw [rep_zero, isTotal]
  pexact constGraph_total 0

theorem isUnique_rep_zero : PA ⊢ ${isUnique (rep Primrec.Code.zero)} := by
  rw [rep_zero, isUnique]
  pexact constGraph_unique 0

theorem isTotal_rep_succ : PA ⊢ ${isTotal (rep Primrec.Code.succ)} := by
  rw [rep_succ, isTotal]
  pexact succGraph_total

theorem isUnique_rep_succ : PA ⊢ ${isUnique (rep Primrec.Code.succ)} := by
  rw [rep_succ, isUnique]
  pexact succGraph_unique

theorem isTotal_rep_left : PA ⊢ ${isTotal (rep Primrec.Code.left)} := by
  rw [rep_left, isTotal]
  pexact leftGraph_total

theorem isUnique_rep_left : PA ⊢ ${isUnique (rep Primrec.Code.left)} := by
  rw [rep_left, isUnique]
  pexact leftGraph_unique

theorem isTotal_rep_right : PA ⊢ ${isTotal (rep Primrec.Code.right)} := by
  rw [rep_right, isTotal]
  pexact rightGraph_total

theorem isUnique_rep_right : PA ⊢ ${isUnique (rep Primrec.Code.right)} := by
  rw [rep_right, isUnique]
  pexact rightGraph_unique

theorem isTotal_rep_pair_of_isProofOf (f g a b : Nat) :
    IsProofOf language isAxiom (isTotal (rep f)) a → IsProofOf language isAxiom
    (isTotal (rep g)) b → (PA ⊢ ${isTotal (rep (Primrec.Code.pair f g))}) := by
  intro ha hb
  have hf : PA ⊢ ${isTotal (rep f)} := (a, ha)
  have hg : PA ⊢ ${isTotal (rep g)} := (b, hb)
  rw [isTotal] at hf
  rw [isTotal] at hg
  rw [rep_pair, isTotal]
  papply pairCompGraph_total (fun x y => ${rep f}[x, y]) (fun x y => ${rep g}[x, y])
  · pexact hf
  · pexact hg

theorem isUnique_rep_pair_of_isProofOf (f g a b : Nat) :
    IsProofOf language isAxiom (isUnique (rep f)) a → IsProofOf language isAxiom
    (isUnique (rep g)) b → (PA ⊢ ${isUnique (rep (Primrec.Code.pair f g))}) := by
  intro ha hb
  have hf : PA ⊢ ${isUnique (rep f)} := (a, ha)
  have hg : PA ⊢ ${isUnique (rep g)} := (b, hb)
  rw [isUnique] at hf
  rw [isUnique] at hg
  rw [rep_pair, isUnique]
  papply pairCompGraph_unique (fun x y => ${rep f}[x, y]) (fun x y => ${rep g}[x, y])
  · pexact hf
  · pexact hg

theorem isTotal_rep_comp_of_isProofOf (f g a b : Nat) :
    IsProofOf language isAxiom (isTotal (rep f)) a → IsProofOf language isAxiom
    (isTotal (rep g)) b → (PA ⊢ ${isTotal (rep (Primrec.Code.comp f g))}) := by
  intro ha hb
  have hf : PA ⊢ ${isTotal (rep f)} := (a, ha)
  have hg : PA ⊢ ${isTotal (rep g)} := (b, hb)
  rw [isTotal] at hf
  rw [isTotal] at hg
  rw [rep_comp, isTotal]
  papply compGraph_total (fun x y => ${rep f}[x, y]) (fun x y => ${rep g}[x, y])
  · pexact hf
  · pexact hg

theorem isUnique_rep_comp_of_isProofOf (f g a b : Nat) :
    IsProofOf language isAxiom (isUnique (rep f)) a → IsProofOf language isAxiom
    (isUnique (rep g)) b → (PA ⊢ ${isUnique (rep (Primrec.Code.comp f g))}) := by
  intro ha hb
  have hf : PA ⊢ ${isUnique (rep f)} := (a, ha)
  have hg : PA ⊢ ${isUnique (rep g)} := (b, hb)
  rw [isUnique] at hf
  rw [isUnique] at hg
  rw [rep_comp, isUnique]
  papply compGraph_unique (fun x y => ${rep f}[x, y]) (fun x y => ${rep g}[x, y])
  · pexact hf
  · pexact hg

theorem isTotal_leastRecursionGraph (p q : Nat) :
    (PA ⊢ ${isTotal p}) → (PA ⊢ ${isTotal q}) → (PA ⊢ ${isTotal (leastRecursionGraph
    (Formula.subst (liftSubst (shiftSubst language 2) language 2) language p) (Formula.subst
    (liftSubst (shiftSubst language 2) language 2) language q) (Term.var language 0) (Term.var
    language 1))}) := by
  intro hp hq
  rw [isTotal]
  papply leastRecursionGraph_total ${p} ${q}
  · pexact hp
  · pexact hq

theorem isUnique_leastRecursionGraph (p q : Nat) :
    (PA ⊢ ${isUnique p}) → (PA ⊢ ${isUnique q}) → (PA ⊢ ${isUnique (leastRecursionGraph
    (Formula.subst (liftSubst (shiftSubst language 2) language 2) language p) (Formula.subst
    (liftSubst (shiftSubst language 2) language 2) language q) (Term.var language 0) (Term.var
    language 1))}) := by
  intro hp hq
  rw [isUnique]
  papply leastRecursionGraph_unique ${p} ${q}
  · pexact hp
  · pexact hq

theorem isTotal_rep_rec_of_isProofOf (f g a b : Nat) :
    IsProofOf language isAxiom (isTotal (rep f)) a → IsProofOf language isAxiom
    (isTotal (rep g)) b → (PA ⊢ ${isTotal (rep (Primrec.Code.rec f g))}) := by
  intro ha hb
  rw [rep_rec]
  exact isTotal_leastRecursionGraph (rep f) (rep g) (a, ha) (b, hb)

theorem isUnique_rep_rec_of_isProofOf (f g a b : Nat) :
    IsProofOf language isAxiom (isUnique (rep f)) a → IsProofOf language isAxiom
    (isUnique (rep g)) b → (PA ⊢ ${isUnique (rep (Primrec.Code.rec f g))}) := by
  intro ha hb
  rw [rep_rec]
  exact isUnique_leastRecursionGraph (rep f) (rep g) (a, ha) (b, hb)

extract_witness isTotal_rep_zero isUnique_rep_zero isTotal_rep_succ isUnique_rep_succ
  isTotal_rep_left isUnique_rep_left isTotal_rep_right isUnique_rep_right
  isTotal_rep_pair_of_isProofOf isUnique_rep_pair_of_isProofOf isTotal_rep_comp_of_isProofOf
  isUnique_rep_comp_of_isProofOf isTotal_rep_rec_of_isProofOf isUnique_rep_rec_of_isProofOf

/-- `totalProofStep e history` constructs the PA totality proof for program `e` from the totality
proofs `history` of its child programs. -/
def totalProofStep : Nat → Nat → Nat := fun e history =>
  let k := Primrec.Code.tag e;
  let args := Primrec.Code.args e;
  let f := unpairLeft args;
  let g := unpairRight args;
  let a := Sequence.rget history f;
  let b := Sequence.rget history g;
  ite (eqb k 0) isTotal_rep_zero.witness
    (ite (eqb k 1) isTotal_rep_succ.witness
      (ite (eqb k 2) isTotal_rep_left.witness
        (ite (eqb k 3) isTotal_rep_right.witness
          (ite (eqb k 4) (isTotal_rep_pair_of_isProofOf.witness f g a b)
            (ite (eqb k 5) (isTotal_rep_comp_of_isProofOf.witness f g a b)
              (isTotal_rep_rec_of_isProofOf.witness f g a b))))))

/-- `totalProof e` constructs a PA proof of totality for the primitive-recursive program `e`. -/
def totalProof : Nat → Nat := covrec totalProofStep

/-- `uniqueProofStep e history` constructs the PA uniqueness proof for program `e` from the
uniqueness proofs `history` of its child programs. -/
def uniqueProofStep : Nat → Nat → Nat := fun e history =>
  let k := Primrec.Code.tag e;
  let args := Primrec.Code.args e;
  let f := unpairLeft args;
  let g := unpairRight args;
  let a := Sequence.rget history f;
  let b := Sequence.rget history g;
  ite (eqb k 0) isUnique_rep_zero.witness
    (ite (eqb k 1) isUnique_rep_succ.witness
      (ite (eqb k 2) isUnique_rep_left.witness
        (ite (eqb k 3) isUnique_rep_right.witness
          (ite (eqb k 4) (isUnique_rep_pair_of_isProofOf.witness f g a b)
            (ite (eqb k 5) (isUnique_rep_comp_of_isProofOf.witness f g a b)
              (isUnique_rep_rec_of_isProofOf.witness f g a b))))))

/-- `uniqueProof e` constructs a PA proof of uniqueness for the primitive-recursive program `e`. -/
def uniqueProof : Nat → Nat := covrec uniqueProofStep

theorem totalProofStep_isProofOf :
    ∀ n xs, Sequence.length xs = n →
    (∀ i, i < n → IsProofOf language isAxiom (isTotal (rep i)) (Sequence.rget xs i)) →
    IsProofOf language isAxiom (isTotal (rep n)) (totalProofStep n xs) := by
  intro n xs hlen ih
  rcases Primrec.Code.cases n with h0 | h1 | h2 | h3 | rest
  · rw [h0]
    change IsProofOf language isAxiom (isTotal (rep Primrec.Code.zero))
      isTotal_rep_zero.witness
    exact isTotal_rep_zero.witness_correct
  · rw [h1]
    change IsProofOf language isAxiom (isTotal (rep Primrec.Code.succ))
      isTotal_rep_succ.witness
    exact isTotal_rep_succ.witness_correct
  · rw [h2]
    change IsProofOf language isAxiom (isTotal (rep Primrec.Code.left))
      isTotal_rep_left.witness
    exact isTotal_rep_left.witness_correct
  · rw [h3]
    change IsProofOf language isAxiom (isTotal (rep Primrec.Code.right))
      isTotal_rep_right.witness
    exact isTotal_rep_right.witness_correct
  · rcases rest with (f, g, cases)
    rcases cases with he | he | he
    · have hfi : f < n := by
        rw [he]
        exact Primrec.Code.left_lt_pair f g
      have hgi : g < n := by
        rw [he]
        exact Primrec.Code.right_lt_pair f g
      have hfp := ih f hfi
      have hgp := ih g hgi
      rw [he, totalProofStep, Primrec.Code.tag_pair f g,
        Primrec.Code.args_pair f g, unpairLeft_pair, unpairRight_pair]
      exact isTotal_rep_pair_of_isProofOf.witness_correct f g (Sequence.rget xs f) (Sequence.rget xs
          g)
        hfp hgp
    · have hfi : f < n := by
        rw [he]
        exact Primrec.Code.left_lt_comp f g
      have hgi : g < n := by
        rw [he]
        exact Primrec.Code.right_lt_comp f g
      have hfp := ih f hfi
      have hgp := ih g hgi
      rw [he, totalProofStep, Primrec.Code.tag_comp f g,
        Primrec.Code.args_comp f g, unpairLeft_pair, unpairRight_pair]
      exact isTotal_rep_comp_of_isProofOf.witness_correct f g (Sequence.rget xs f) (Sequence.rget xs
          g)
        hfp hgp
    · have hfi : f < n := by
        rw [he]
        exact Primrec.Code.left_lt_rec f g
      have hgi : g < n := by
        rw [he]
        exact Primrec.Code.right_lt_rec f g
      have hfp := ih f hfi
      have hgp := ih g hgi
      rw [he, totalProofStep, Primrec.Code.tag_rec f g,
        Primrec.Code.args_rec f g, unpairLeft_pair, unpairRight_pair]
      exact isTotal_rep_rec_of_isProofOf.witness_correct f g (Sequence.rget xs f) (Sequence.rget xs
          g)
        hfp hgp

/-- The constructed proof has the required conclusion for every primitive-recursive program. -/
theorem totalProof_isProofOf :
    ∀ e, IsProofOf language isAxiom (isTotal (rep e)) (totalProof e) := by
  intro e
  exact covrec_induction
    (fun n p => IsProofOf language isAxiom (isTotal (rep n)) p)
    (fun n p => proofCheck isAxiom (isTotal (rep n)) p) totalProofStep
    (fun n p => proofCheck_iff isAxiom (isTotal (rep n)) p) totalProofStep_isProofOf e

theorem uniqueProofStep_isProofOf :
    ∀ n xs, Sequence.length xs = n →
    (∀ i, i < n → IsProofOf language isAxiom (isUnique (rep i)) (Sequence.rget xs i)) →
    IsProofOf language isAxiom (isUnique (rep n)) (uniqueProofStep n xs) := by
  intro n xs hlen ih
  rcases Primrec.Code.cases n with h0 | h1 | h2 | h3 | rest
  · rw [h0]
    change IsProofOf language isAxiom (isUnique (rep Primrec.Code.zero))
      isUnique_rep_zero.witness
    exact isUnique_rep_zero.witness_correct
  · rw [h1]
    change IsProofOf language isAxiom (isUnique (rep Primrec.Code.succ))
      isUnique_rep_succ.witness
    exact isUnique_rep_succ.witness_correct
  · rw [h2]
    change IsProofOf language isAxiom (isUnique (rep Primrec.Code.left))
      isUnique_rep_left.witness
    exact isUnique_rep_left.witness_correct
  · rw [h3]
    change IsProofOf language isAxiom (isUnique (rep Primrec.Code.right))
      isUnique_rep_right.witness
    exact isUnique_rep_right.witness_correct
  · rcases rest with (f, g, cases)
    rcases cases with he | he | he
    · have hfi : f < n := by
        rw [he]
        exact Primrec.Code.left_lt_pair f g
      have hgi : g < n := by
        rw [he]
        exact Primrec.Code.right_lt_pair f g
      have hfp := ih f hfi
      have hgp := ih g hgi
      rw [he, uniqueProofStep, Primrec.Code.tag_pair f g,
        Primrec.Code.args_pair f g, unpairLeft_pair, unpairRight_pair]
      exact isUnique_rep_pair_of_isProofOf.witness_correct f g (Sequence.rget xs f)
        (Sequence.rget xs g) hfp hgp
    · have hfi : f < n := by
        rw [he]
        exact Primrec.Code.left_lt_comp f g
      have hgi : g < n := by
        rw [he]
        exact Primrec.Code.right_lt_comp f g
      have hfp := ih f hfi
      have hgp := ih g hgi
      rw [he, uniqueProofStep, Primrec.Code.tag_comp f g,
        Primrec.Code.args_comp f g, unpairLeft_pair, unpairRight_pair]
      exact isUnique_rep_comp_of_isProofOf.witness_correct f g (Sequence.rget xs f)
        (Sequence.rget xs g) hfp hgp
    · have hfi : f < n := by
        rw [he]
        exact Primrec.Code.left_lt_rec f g
      have hgi : g < n := by
        rw [he]
        exact Primrec.Code.right_lt_rec f g
      have hfp := ih f hfi
      have hgp := ih g hgi
      rw [he, uniqueProofStep, Primrec.Code.tag_rec f g,
        Primrec.Code.args_rec f g, unpairLeft_pair, unpairRight_pair]
      exact isUnique_rep_rec_of_isProofOf.witness_correct f g (Sequence.rget xs f) (Sequence.rget xs
          g)
        hfp hgp

/-- The constructed proof has the required conclusion for every primitive-recursive program. -/
theorem uniqueProof_isProofOf :
    ∀ e, IsProofOf language isAxiom (isUnique (rep e)) (uniqueProof e) := by
  intro e
  exact covrec_induction
    (fun n p => IsProofOf language isAxiom (isUnique (rep n)) p)
    (fun n p => proofCheck isAxiom (isUnique (rep n)) p) uniqueProofStep
    (fun n p => proofCheck_iff isAxiom (isUnique (rep n)) p) uniqueProofStep_isProofOf e

/-- PA proves totality of the graph constructed from any primitive-recursive program code. -/
theorem rep_total (e : Nat) : (PA ⊢ ∀ x, ∃ y, ${rep e}[x, y]) := by
  have represented : PA ⊢ ${isTotal (rep e)} := (totalProof e, totalProof_isProofOf e)
  rw [isTotal] at represented
  pexact represented

/-- PA proves uniqueness for the same graph constructed from the program code. -/
theorem rep_unique (e : Nat) : (PA ⊢ ∀ x y z, ${rep e}[x, y] → ${rep e}[x, z] → y = z) := by
  have represented : PA ⊢ ${isUnique (rep e)} := (uniqueProof e, uniqueProof_isProofOf e)
  rw [isUnique] at represented
  pexact represented

end PA

end

end FOL
