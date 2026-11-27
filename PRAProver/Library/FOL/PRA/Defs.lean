module

public import PRAProver.Library.FOL.Common.Computability
public import PRAProver.Library.FOL.DSL.Tactic

/-!
# The first-order theory of PRA

- `FOL.PRA.language` has zero, successor, Cantor pairing, and one unary function `eval[e]` for
  each program code `e`.
- `FOL.PRA.isAxiom` checks the successor and pairing laws, the program equations, and induction
  with quantifier-free bodies.
- Each axiom `ax` is also the theorem `FOL.PRA.ax`, as for every declared theory. For a
  quantified axiom `ax`, the theorem `ax'` states its instance at arbitrary term codes, for use
  from Lean proofs that combine provability facts.
-/

open PRAProver.Library.FOL.DSL in
run_cmd do
  registerAxiomIndexProjection `Primrec.Code.rec `Primrec.Code.left_rec
  registerAxiomIndexProjection `Primrec.Code.rec `Primrec.Code.right_rec

pra

namespace FOL

fol_language PRA where
  constant zero
  function succ of 1
  function pair of 2
  eval (e : Nat) : function of 1

fol_theory PRA over PRA where
  axiom succ_ne_zero := ∀ x, succ(x) ≠ zero
  axiom succ_injective := ∀ x y, succ(x) = succ(y) → x = y
  axiom pair_zero_zero := pair(zero, zero) = zero
  axiom pair_zero_succ := ∀ y, pair(zero, succ(y)) = succ(pair(y, zero))
  axiom pair_succ := ∀ x y, pair(succ(x), y) = succ(pair(x, succ(y)))
  axiom pair_eval_left_right :=
    ∀ x, pair(eval[Primrec.Code.left](x), eval[Primrec.Code.right](x)) = x
  axiom eval_zero := ∀ x, eval[Primrec.Code.zero](x) = zero
  axiom eval_succ := ∀ x, eval[Primrec.Code.succ](x) = succ(x)
  axiom eval_left := ∀ x y, eval[Primrec.Code.left](pair(x, y)) = x
  axiom eval_right := ∀ x y, eval[Primrec.Code.right](pair(x, y)) = y
  axiom eval_pair (f g : Nat) :=
    ∀ x, eval[Primrec.Code.pair f g](x) = pair(eval[f](x), eval[g](x))
  axiom eval_comp (f g : Nat) :=
    ∀ x, eval[Primrec.Code.comp f g](x) = eval[f](eval[g](x))
  axiom eval_rec_zero (f g : Nat) :=
    ∀ x, eval[Primrec.Code.rec f g](pair(x, zero)) = eval[f](x)
  axiom eval_rec_succ (f g : Nat) :=
    ∀ x n, eval[Primrec.Code.rec f g](pair(x, succ(n))) =
      eval[g](pair(x, pair(n, eval[Primrec.Code.rec f g](pair(x, n)))))
  axiom induction (P : formula of 1) assuming Formula.isQuantifierFree PRA.language P = 1 :=
    P(zero) → (∀ x, P(x) → P(succ(x))) → ∀ x, P(x)

namespace PRA

derive_primrec language succ_ne_zero.formula succ_ne_zero.isAxiom succ_injective.formula

derive_primrec succ_injective.isAxiom pair_zero_zero.formula pair_zero_zero.isAxiom

derive_primrec pair_zero_succ.formula pair_zero_succ.isAxiom pair_succ.formula pair_succ.isAxiom

derive_primrec pair_eval_left_right.formula pair_eval_left_right.isAxiom eval_zero.formula

derive_primrec eval_zero.isAxiom eval_succ.formula eval_succ.isAxiom eval_left.formula

derive_primrec eval_left.isAxiom eval_right.formula eval_right.isAxiom eval_pair.formula

derive_primrec eval_pair.isInstance eval_pair.isAxiom eval_comp.formula eval_comp.isInstance

derive_primrec eval_comp.isAxiom eval_rec_zero.formula eval_rec_zero.isInstance

derive_primrec eval_rec_zero.isAxiom eval_rec_succ.formula eval_rec_succ.isInstance

derive_primrec eval_rec_succ.isAxiom induction.formula induction.isInstance induction.isAxiom

derive_primrec isAxiom

fol_theorem pair_zero_succ' (y : Nat) : PRA ⊢
    pair(zero, succ(${y})) = succ(pair(${y}, zero)) := by
  pexact PRA.pair_zero_succ[${y}]

fol_theorem pair_succ' (x y : Nat) : PRA ⊢
    pair(succ(${x}), ${y}) = succ(pair(${x}, succ(${y}))) := by
  pexact PRA.pair_succ[${x}, ${y}]

fol_theorem pair_eval_left_right' (t : Nat) : PRA ⊢
    pair(eval[Primrec.Code.left](${t}), eval[Primrec.Code.right](${t})) = ${t} := by
  pexact PRA.pair_eval_left_right[${t}]

fol_theorem eval_zero' (x : Nat) : PRA ⊢ eval[Primrec.Code.zero](${x}) = zero := by
  pexact PRA.eval_zero[${x}]

fol_theorem eval_succ' (x : Nat) : PRA ⊢ eval[Primrec.Code.succ](${x}) = succ(${x}) := by
  pexact PRA.eval_succ[${x}]

fol_theorem eval_left' (x y : Nat) : PRA ⊢
    eval[Primrec.Code.left](pair(${x}, ${y})) = ${x} := by
  pexact PRA.eval_left[${x}, ${y}]

fol_theorem eval_right' (x y : Nat) : PRA ⊢
    eval[Primrec.Code.right](pair(${x}, ${y})) = ${y} := by
  pexact PRA.eval_right[${x}, ${y}]

fol_theorem eval_pair' (f g x : Nat) : PRA ⊢
    eval[Primrec.Code.pair f g](${x}) = pair(eval[f](${x}), eval[g](${x})) := by
  pexact (PRA.eval_pair f g)[${x}]

fol_theorem eval_comp' (f g x : Nat) : PRA ⊢
    eval[Primrec.Code.comp f g](${x}) = eval[f](eval[g](${x})) := by
  pexact (PRA.eval_comp f g)[${x}]

fol_theorem eval_rec_zero' (f g x : Nat) : PRA ⊢
    eval[Primrec.Code.rec f g](pair(${x}, zero)) = eval[f](${x}) := by
  pexact (PRA.eval_rec_zero f g)[${x}]

fol_theorem eval_rec_succ' (f g x n : Nat) : PRA ⊢
    eval[Primrec.Code.rec f g](pair(${x}, succ(${n}))) =
      eval[g](pair(${x}, pair(${n}, eval[Primrec.Code.rec f g](pair(${x}, ${n}))))) := by
  pexact (PRA.eval_rec_succ f g)[${x}, ${n}]

end PRA

end FOL

end
