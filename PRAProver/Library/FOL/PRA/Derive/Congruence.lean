module

public import PRAProver.Library.FOL.PRA.Defs
meta import PRAProver.Library.FOL.DSL.Tactic

/-!
# Congruence of primitive recursive programs in first-order PRA

- `FOL.PRA.Evaluation.rec_congr` compares two recursions at the same counter. Their
  fixed inputs may differ.
- `FOL.PRA.Evaluation.comp_congr` and `FOL.PRA.Evaluation.pair_congr` give the
  pointwise equations for composition and pairing.
- `FOL.PRA.Evaluation.rec_congr_programs` gives the pointwise equation for recursion
  when the base and step programs agree at all inputs.
-/

pra

namespace FOL.PRA.Evaluation

/-- Compare two recursion programs at the same counter by induction on the equality
of their results. The base and step equations compare the two fixed parameters. -/
fol_theorem rec_congr (f g f' g' : Nat) : PRA ⊢ ∀ x y n,
    eval[f](x) = eval[f'](y) →
    (∀ i r, eval[g](pair(x, pair(i, r))) = eval[g'](pair(y, pair(i, r)))) →
    eval[Primrec.Code.rec f g](pair(x, n)) =
      eval[Primrec.Code.rec f' g'](pair(y, n)) := by
  pintro x y n base steps
  phave values : ∀ k, eval[Primrec.Code.rec f g](pair(x, k)) =
    eval[Primrec.Code.rec f' g'](pair(y, k))
  · pintro k
    pinduction k with
    | zero =>
      ptrans eval[f](x)
      · pexact (PRA.eval_rec_zero f g)[x]
      · ptrans eval[f'](y)
        · pexact base
        · psymm
          pexact (PRA.eval_rec_zero f' g')[y]
    | succ i ih =>
      ptrans eval[g](pair(x, pair(i, eval[Primrec.Code.rec f g](pair(x, i)))))
      · pexact (PRA.eval_rec_succ f g)[x, i]
      · ptrans eval[g'](pair(y, pair(i, eval[Primrec.Code.rec f g](pair(x, i)))))
        · pexact steps[i, eval[Primrec.Code.rec f g](pair(x, i))]
        · ptrans eval[g'](pair(y, pair(i, eval[Primrec.Code.rec f' g'](pair(y, i)))))
          · prw [ih]
          · psymm
            pexact (PRA.eval_rec_succ f' g')[y, i]
  pexact values[n]

/-- Substituting pointwise equal programs in a composition preserves its value. -/
fol_theorem comp_congr (f g f' g' : Nat) : PRA ⊢
    (∀ x, eval[f](x) = eval[f'](x)) → (∀ x, eval[g](x) = eval[g'](x)) →
      ∀ x, eval[Primrec.Code.comp f g](x) = eval[Primrec.Code.comp f' g'](x) := by
  pintro outer inner x
  ptrans eval[f](eval[g](x))
  · pexact (PRA.eval_comp f g)[x]
  · ptrans eval[f'](eval[g](x))
    · pexact outer[eval[g](x)]
    · phave h : eval[g](x) = eval[g'](x)
      · pexact inner[x]
      ptrans eval[f'](eval[g'](x))
      · prw [h]
      · psymm
        pexact (PRA.eval_comp f' g')[x]

/-- Substituting pointwise equal programs in a pair preserves its value. -/
fol_theorem pair_congr (f g f' g' : Nat) : PRA ⊢
    (∀ x, eval[f](x) = eval[f'](x)) → (∀ x, eval[g](x) = eval[g'](x)) →
      ∀ x, eval[Primrec.Code.pair f g](x) = eval[Primrec.Code.pair f' g'](x) := by
  pintro lhs rhs x
  ptrans pair(eval[f](x), eval[g](x))
  · pexact (PRA.eval_pair f g)[x]
  · phave hf : eval[f](x) = eval[f'](x)
    · pexact lhs[x]
    phave hg : eval[g](x) = eval[g'](x)
    · pexact rhs[x]
    ptrans pair(eval[f'](x), eval[g'](x))
    · prw [hf, hg]
    · psymm
      pexact (PRA.eval_pair f' g')[x]

/-- Substituting pointwise equal programs in a primitive recursion preserves its value. -/
fol_theorem rec_congr_programs (f g f' g' : Nat) : PRA ⊢
    (∀ x, eval[f](x) = eval[f'](x)) → (∀ x, eval[g](x) = eval[g'](x)) →
      ∀ x, eval[Primrec.Code.rec f g](x) = eval[Primrec.Code.rec f' g'](x) := by
  pintro base step x
  phave packed : pair(eval[Primrec.Code.left](x), eval[Primrec.Code.right](x)) = x
  · pexact PRA.pair_eval_left_right[x]
  ptrans eval[Primrec.Code.rec f g](pair(eval[Primrec.Code.left](x), eval[Primrec.Code.right](x)))
  · prw [packed]
  · ptrans eval[Primrec.Code.rec f' g'](
      pair(eval[Primrec.Code.left](x), eval[Primrec.Code.right](x)))
    · papply (rec_congr f g f' g')[eval[Primrec.Code.left](x), eval[Primrec.Code.left](x),
        eval[Primrec.Code.right](x)]
      · pexact base[eval[Primrec.Code.left](x)]
      · pintro i r
        pexact step[pair(eval[Primrec.Code.left](x), pair(i, r))]
    · prw [packed]

end FOL.PRA.Evaluation

end
