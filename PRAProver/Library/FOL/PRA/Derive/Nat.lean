module

public import PRAProver.Library.FOL.PRA.Derive.Command

/-!
# Natural number theorems in first-order PRA

The deriver translates arithmetic, pairing, and sequence theorems into first-order PRA.
The pairing lemmas relate the derived arithmetic programs to the primitive tuple operations.
-/

pra

namespace FOL.PRA

derive_fol_pra sub_succ as sub_succ

derive_fol_pra succ_sub_succ as succ_sub_succ

derive_fol_pra _root_.unpairLeft_pair as eval_unpairLeft_pair

derive_fol_pra _root_.unpairRight_pair as eval_unpairRight_pair

derive_fol_pra _root_.pair_unpair as eval_pair_unpair

derive_fol_pra _root_.left_le_pair as left_le_pair

derive_fol_pra _root_.right_le_pair as right_le_pair

derive_fol_pra _root_.unpairLeft_le as unpairLeft_le

derive_fol_pra _root_.unpairRight_le as unpairRight_le

derive_fol_pra _root_.pair_lt_of_sum_lt as pair_lt_of_sum_lt

derive_fol_pra _root_.eq_pair_of_equations as eq_pair_of_equations

/-- The identity instruction returns its input. -/
fol_theorem eval_id : PRA ⊢ ∀ x, eval[Primrec.Code.id](x) = x := by
  have code : Primrec.Code.id = Primrec.Code.pair Primrec.Code.left Primrec.Code.right := rfl
  rw [code]
  pintro x
  ptrans pair(eval[Primrec.Code.left](x), eval[Primrec.Code.right](x))
  · pexact (PRA.eval_pair Primrec.Code.left Primrec.Code.right)[x]
  · pexact PRA.pair_eval_left_right[x]

/-- The arithmetic pairing program computes the primitive pair of its arguments. -/
fol_theorem pair_value : PRA ⊢ ∀ x y, eval[pair.code](pair(x, y)) = pair(x, y) := by
  have law : PRA ⊢ ∀ x y, eval[Primrec.Code.id](pair(x, y)) = eval[pair.code](pair(x, y)) := by
    papply (FOL.PRA.eq_pair_of_equations Primrec.Code.id)[]
    · prw [FOL.PRA.eval_id, PRA.pair_zero_zero]
    · pintro n
      prw [FOL.PRA.eval_id, PRA.pair_zero_succ]
    · pintro x y
      prw [FOL.PRA.eval_id, PRA.pair_succ]
  pintro x y
  psymm
  ptrans eval[Primrec.Code.id](pair(x, y))
  · psymm
    pexact FOL.PRA.eval_id[pair(x, y)]
  · pexact law[x, y]

/-- Pairing the outputs of the two arithmetic projections recovers their input. -/
fol_theorem pair_eval_unpair : PRA ⊢ ∀ x,
    pair(eval[unpairLeft.code](x), eval[unpairRight.code](x)) = x := by
  pintro x
  ptrans eval[pair.code](pair(eval[unpairLeft.code](x), eval[unpairRight.code](x)))
  · psymm
    pexact FOL.PRA.pair_value[eval[unpairLeft.code](x), eval[unpairRight.code](x)]
  · pexact FOL.PRA.eval_pair_unpair[x]

/-- The arithmetic left projection agrees with the left instruction on every input. -/
fol_theorem unpairLeft_value : PRA ⊢ ∀ x,
    eval[unpairLeft.code](x) = eval[Primrec.Code.left](x) := by
  pintro x
  psymm
  ptrans eval[Primrec.Code.left](pair(eval[unpairLeft.code](x), eval[unpairRight.code](x)))
  · pcongr
    psymm
    pexact FOL.PRA.pair_eval_unpair[x]
  · pexact PRA.eval_left[eval[unpairLeft.code](x), eval[unpairRight.code](x)]

/-- The arithmetic right projection agrees with the right instruction on every input. -/
fol_theorem unpairRight_value : PRA ⊢ ∀ x,
    eval[unpairRight.code](x) = eval[Primrec.Code.right](x) := by
  pintro x
  psymm
  ptrans eval[Primrec.Code.right](pair(eval[unpairLeft.code](x), eval[unpairRight.code](x)))
  · pcongr
    psymm
    pexact FOL.PRA.pair_eval_unpair[x]
  · pexact PRA.eval_right[eval[unpairLeft.code](x), eval[unpairRight.code](x)]

namespace Sequence

derive_fol_pra Sequence.get_cons_zero as get_cons_zero

derive_fol_pra Sequence.get_cons_succ as get_cons_succ

derive_fol_pra Sequence.length_cons as length_cons

derive_fol_pra Sequence.rget_cons_length as rget_cons_length

derive_fol_pra Sequence.rget_cons as rget_cons

end Sequence

derive_fol_pra band_eq_one_of_eq_one as band_eq_one_of_eq_one_inner

end FOL.PRA

end
