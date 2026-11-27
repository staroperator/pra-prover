module

public import LeanPRA.Library.FOL.PRA.Derive.Command
public import LeanPRA.Library.FOL.PRA.Provability.Defs
meta import LeanPRA.Library.FOL.DSL.Tactic

/-!
# Necessitation in first-order PRA

- `FOL.PRA.eval_num_of_evaluates`: evaluation of primitive recursive programs on numerals in PRA.
- `FOL.PRA.pr_of_provable`: the first Hilbert–Bernays–Löb provability condition.
-/

pra

namespace FOL.PRA

open FOL

/-! ## Evaluating programs on `num` terms -/

open Primrec.Computation

def EvaluationProofOf (e x y p : Nat) : QFProp :=
  IsProofOf language isAxiom
    (Formula.equal language fol_term[PRA | eval[e](${num x})] (num y)) p

theorem eval_zero_num (x : Nat) :
    (PRA ⊢ eval[Primrec.Code.zero](${num x}) = ${num 0}) := by
  rw [num_zero]
  exact FOL.PRA.eval_zero' (num x)

theorem eval_succ_num (x : Nat) :
    (PRA ⊢ eval[Primrec.Code.succ](${num x}) = ${num (S x)}) := by
  rw [num_succ]
  exact FOL.PRA.eval_succ' (num x)

extract_witness pair_num

theorem eval_pair_num (e a b : Nat) :
    (PRA ⊢ eval[e](pair(${num a}, ${num b})) = eval[e](${num (pair a b)})) :=
  Evaluation.congr_eval e _ _ (pair_num a b)

extract_witness eval_pair_num

theorem eval_left_num (x : Nat) :
    (PRA ⊢ eval[Primrec.Code.left](${num x}) = ${num (unpairLeft x)}) := by
  let a := unpairLeft x
  let b := unpairRight x
  have h := eval_pair_num Primrec.Code.left a b
  rw [pair_unpair] at h
  exact Evaluation.trans _ _ _
    (Evaluation.symm _ _ h) (FOL.PRA.eval_left' (num a) (num b))

theorem eval_right_num (x : Nat) :
    (PRA ⊢ eval[Primrec.Code.right](${num x}) = ${num (unpairRight x)}) := by
  let a := unpairLeft x
  let b := unpairRight x
  have h := eval_pair_num Primrec.Code.right a b
  rw [pair_unpair] at h
  exact Evaluation.trans _ _ _
    (Evaluation.symm _ _ h) (FOL.PRA.eval_right' (num a) (num b))

theorem eval_pair_code_num (f g x u v a b : Nat) :
    EvaluationProofOf f x u a → EvaluationProofOf g x v b →
    (PRA ⊢ eval[Primrec.Code.pair f g](${num x}) = ${num (pair u v)}) := by
  intro ha hb
  let l := fol_term[PRA | eval[f](${num x})]
  let r := fol_term[PRA | eval[g](${num x})]
  have h₁ : (PRA ⊢ ${l} = ${num u}) := (a, ha)
  have h₂ : (PRA ⊢ ${r} = ${num v}) := (b, hb)
  have h := Evaluation.congr_pair l r (num u) (num v) h₁ h₂
  exact Evaluation.trans _ _ _ (FOL.PRA.eval_pair' f g (num x))
    (Evaluation.trans _ _ _ h (pair_num u v))

theorem eval_comp_num (f g x u y a b : Nat) :
    EvaluationProofOf g x u a → EvaluationProofOf f u y b →
    (PRA ⊢ eval[Primrec.Code.comp f g](${num x}) = ${num y}) := by
  intro ha hb
  let r := fol_term[PRA | eval[g](${num x})]
  have h₁ : (PRA ⊢ ${r} = ${num u}) := (a, ha)
  have h₂ : (PRA ⊢ eval[f](${num u}) = ${num y}) := (b, hb)
  exact Evaluation.trans _ _ _ (FOL.PRA.eval_comp' f g (num x))
    (Evaluation.trans _ _ _ (Evaluation.congr_eval f r (num u) h₁) h₂)

theorem eval_rec_zero_num (f g x y a : Nat) :
    EvaluationProofOf f x y a →
    (PRA ⊢ eval[Primrec.Code.rec f g](${num (pair x 0)}) = ${num y}) := by
  intro ha
  have h := Evaluation.symm _ _ (eval_pair_num (Primrec.Code.rec f g) x 0)
  rw [num_zero] at h
  have base : (PRA ⊢ eval[f](${num x}) = ${num y}) := (a, ha)
  exact Evaluation.trans _ _ _ h (Evaluation.trans _ _ _ (FOL.PRA.eval_rec_zero' f g (num x)) base)

theorem eval_rec_succ_num (f g x n u y a b : Nat) :
    EvaluationProofOf (Primrec.Code.rec f g) (pair x n) u a →
    EvaluationProofOf g (pair x (pair n u)) y b →
    (PRA ⊢ eval[Primrec.Code.rec f g](${num (pair x (S n))}) = ${num y}) := by
  intro ha hb
  let e := Primrec.Code.rec f g
  let xn := num x
  let nn := num n
  let prev := fol_term[PRA | eval[e](pair(${xn}, ${nn}))]
  have hi := Evaluation.symm _ _ (eval_pair_num e x (S n))
  rw [num_succ n] at hi
  have hp : (PRA ⊢ eval[e](${num (pair x n)}) = ${num u}) := (a, ha)
  have hv : (PRA ⊢ ${prev} = ${num u}) := Evaluation.trans _ _ _ (eval_pair_num e x n) hp
  have hright : (PRA ⊢ pair(${nn}, ${prev}) = ${num (pair n u)}) :=
    Evaluation.trans _ _ _ (Evaluation.congr_pair nn prev nn (num u) (Evaluation.refl nn) hv)
      (pair_num n u)
  have harg : (PRA ⊢ pair(${xn}, pair(${nn}, ${prev})) = ${num (pair x (pair n u))}) :=
    Evaluation.trans _ _ _ (Evaluation.congr_pair xn _ xn _ (Evaluation.refl xn) hright)
      (pair_num x (pair n u))
  have hs : (PRA ⊢ eval[g](${num (pair x (pair n u))}) = ${num y}) :=
    (b, hb)
  exact Evaluation.trans _ _ _ hi (Evaluation.trans _ _ _ (FOL.PRA.eval_rec_succ' f g xn nn)
    (Evaluation.trans _ _ _ (Evaluation.congr_eval g _ _ harg) hs))

extract_witness eval_zero_num eval_succ_num eval_left_num eval_right_num
  eval_pair_code_num eval_comp_num eval_rec_zero_num eval_rec_succ_num

/-- The proof at each child index is stored in the course-of-values recursion history. -/
def evaluationProofStep : Nat → Nat → Nat := fun t history =>
  let e := program t;
  let x := input t;
  let y := output t;
  let k := Primrec.Code.tag e;
  let args := Primrec.Code.args e;
  let f := unpairLeft args;
  let g := unpairRight args;
  let u := output (childLeft t);
  let v := output (childRight t);
  let a := Sequence.rget history (childLeft t);
  let b := Sequence.rget history (childRight t);
  ite (eqb k 0) (eval_zero_num.witness x)
    (ite (eqb k 1) (eval_succ_num.witness x)
      (ite (eqb k 2) (eval_left_num.witness x)
        (ite (eqb k 3) (eval_right_num.witness x)
          (ite (eqb k 4) (eval_pair_code_num.witness f g x u v a b)
            (ite (eqb k 5) (eval_comp_num.witness f g x u y a b)
              (let m := unpairLeft x;
               let n := unpairRight x;
               ite n (eval_rec_succ_num.witness f g m (pred n) u y a b)
                 (eval_rec_zero_num.witness f g m y a)))))))

def TreeProofOf (t p : Nat) : QFProp :=
  isValid t = 1 → EvaluationProofOf (program t) (input t) (output t) p

def isTreeProofOf (t p : Nat) : Nat :=
  bimp (eqb (isValid t) 1) (band (eqb (FOL.isProof language isAxiom p) 1)
    (eqb (FOL.Proof.conclusion p)
      (Formula.equal language fol_term[PRA | eval[program t](${num (input t)})]
        (num (output t)))))

theorem isTreeProofOf_iff : ∀ t p,
    ¬ isTreeProofOf t p = 0 ↔ TreeProofOf t p := by
  intro t p
  let v := eqb (isValid t) 1
  let a := eqb (FOL.isProof language isAxiom p) 1
  let b := eqb (FOL.Proof.conclusion p)
    (Formula.equal language fol_term[PRA | eval[program t](${num (input t)})] (num (output t)))
  let c := bimp v (band a b)
  have checked : ¬ band a b = 0 ↔ EvaluationProofOf (program t) (input t) (output t) p := by
    apply iff_trans (and_symm (bool_eq_one (band a b) (band_bool a b)))
    apply iff_trans (band_eq_one a b)
    exact and_congr (eqb_ne_zero _ _) (eqb_ne_zero _ _)
  have valid := eqb_ne_zero (isValid t) 1
  apply iff_trans (and_symm (bool_eq_one c (bimp_bool v (band a b))))
  apply iff_trans (bimp_eq_one v (band a b))
  exact (fun test ht => and_left checked (test (and_right valid ht)),
    fun proof hv => and_right checked (proof (and_left valid hv)))

theorem evaluationProofOf_of_evaluates (e x y t p : Nat) :
    Evaluates e x y t → TreeProofOf t p → EvaluationProofOf e x y p := by
  rintro (hv, he, hx, hy) h
  have checked := h hv
  rw [he, hx, hy] at checked
  exact checked

theorem evaluationProofStep_correct : ∀ t history,
    (∀ u, u < t → TreeProofOf u (Sequence.rget history u)) →
    TreeProofOf t (evaluationProofStep t history) := by
  intro t history earlier ht
  let e := program t
  let x := input t
  let y := output t
  let l := childLeft t
  let r := childRight t
  let a := Sequence.rget history l
  let b := Sequence.rget history r
  let u := output l
  let v := output r
  have h : Evaluates e x y t := (ht, rfl, rfl, rfl)
  have nonzero := ne_zero_of_isValid t ht
  have hl : TreeProofOf l a := earlier l (childLeft_lt t nonzero)
  have hr : TreeProofOf r b := earlier r (childRight_lt t nonzero)
  change EvaluationProofOf e x y (evaluationProofStep t history)
  rcases Primrec.Code.cases e with h0 | h1 | h2 | h3 | rest
  · rw [h0] at h
    have hy := output_zero_of_evaluates x y t h
    rw [hy, evaluationProofStep, h0]
    exact eval_zero_num.witness_correct x
  · rw [h1] at h
    have hy := output_succ_of_evaluates x y t h
    rw [hy, evaluationProofStep, h1]
    exact eval_succ_num.witness_correct x
  · rw [h2] at h
    have hy := output_left_of_evaluates x y t h
    rw [hy, evaluationProofStep, h2]
    exact eval_left_num.witness_correct x
  · rw [h3] at h
    have hy := output_right_of_evaluates x y t h
    rw [hy, evaluationProofStep, h3]
    exact eval_right_num.witness_correct x
  · rcases rest with (f, g, cases)
    rcases cases with hpair | hcomp | hrec
    · rw [hpair] at h
      rcases evaluates_pair_elim f g x y t h with (h₁, h₂, hy)
      have p := evaluationProofOf_of_evaluates f x u l a h₁ hl
      have q := evaluationProofOf_of_evaluates g x v r b h₂ hr
      rw [hy, evaluationProofStep, hpair, Primrec.Code.tag_pair f g,
        Primrec.Code.args_pair f g,
        unpairLeft_pair, unpairRight_pair]
      exact eval_pair_code_num.witness_correct f g x u v a b p q
    · rw [hcomp] at h
      rcases evaluates_comp_elim f g x y t h with (h₁, h₂)
      have p := evaluationProofOf_of_evaluates g x u l a h₁ hl
      have q := evaluationProofOf_of_evaluates f u y r b h₂ hr
      rw [evaluationProofStep, hcomp, Primrec.Code.tag_comp f g,
        Primrec.Code.args_comp f g, unpairLeft_pair, unpairRight_pair]
      exact eval_comp_num.witness_correct f g x u y a b p q
    · rw [hrec] at h
      rw [evaluationProofStep, hrec, Primrec.Code.tag_rec f g,
        Primrec.Code.args_rec f g, unpairLeft_pair, unpairRight_pair]
      let m := unpairLeft x
      rcases zero_or_succ_pred (unpairRight x) with hn | hn
      · have hx : pair m 0 = x := by rw [← hn, pair_unpair]
        have h₁ : Evaluates f m y l := by
          apply evaluates_rec_zero_elim f g m y t
          rw [hx]
          exact h
        have p := evaluationProofOf_of_evaluates f m y l a h₁ hl
        have checked := eval_rec_zero_num.witness_correct f g m y a p
        rw [hx] at checked
        rw [hn]
        exact checked
      · let n := pred (unpairRight x)
        have hx : pair m (S n) = x := by rw [← hn, pair_unpair]
        have step : Evaluates (Primrec.Code.rec f g) (pair m (S n)) y t := by
          rw [hx]
          exact h
        rcases evaluates_rec_succ_elim f g m n y t step with (h₁, h₂)
        have p := evaluationProofOf_of_evaluates (Primrec.Code.rec f g) (pair m n) u l a h₁ hl
        have q := evaluationProofOf_of_evaluates g (pair m (pair n u)) y r b h₂ hr
        have checked := eval_rec_succ_num.witness_correct f g m n u y a b p q
        rw [hx] at checked
        rw [hn]
        exact checked

/-- For a primitive recursive program `e`, if `e` evaluates `x` to `y`, then PRA proves
`eval[e](num x) = num y`. -/
theorem eval_num_of_evaluates : ∀ e x y t, Primrec.Computation.Evaluates e x y t →
    (PRA ⊢ eval[e](${num x}) = ${num y}) := by
  intro e x y t h
  let proof := covrec evaluationProofStep
  have valid : ∀ u, TreeProofOf u (proof u) :=
    covrec_induction (fun u p => TreeProofOf u p)
      (fun u p => isTreeProofOf u p) evaluationProofStep isTreeProofOf_iff
      (fun u history _ earlier => evaluationProofStep_correct u history earlier)
  exact (proof t, evaluationProofOf_of_evaluates e x y t (proof t) h (valid t))

/-- **The first Hilbert–Bernays–Löb provability condition:** if `T ⊢ A`, then `PRA ⊢ pr_T(⌜A⌝)`.
Here `T` is a first-order theory in language `L` whose axioms are encoded by the program code `e`
with computation trace witness `tr`. -/
theorem pr_of_provable (L : Nat) (T : Nat → Nat) (e : Nat) (tr : Nat → Nat) :
    Primrec.ComputedBy T e tr → ∀ a, FOL.Provable L T a →
      (PRA ⊢ (pr L e ${num a})) := by
  intro computes a h
  rcases h with (p, hp, ha)
  have verifier := FOL.isProof.computedBy L e T tr computes p
  have verified := eval_num_of_evaluates
    (FOL.isProof.code L e) p (FOL.isProof L T p)
    (FOL.isProof.trace L e T tr p) verifier
  have conclusion := eval_num_of_evaluates
    FOL.Proof.conclusion.code p (FOL.Proof.conclusion p)
    (FOL.Proof.conclusion.trace p) (FOL.Proof.conclusion.computedBy p)
  rw [hp, num_succ 0, num_zero] at verified
  rw [ha] at conclusion
  pexists ${num p}
  pconstructor
  · pexact verified
  · pexact conclusion

end FOL.PRA

end
