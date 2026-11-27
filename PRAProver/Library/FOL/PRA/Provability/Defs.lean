module

public import PRAProver.Library.FOL.PRA.Numeral

/-!
# Provability in a primitive recursive theory

`pr L T a` says that the formula with code `a` has a proof.
Here `L` is the language code and `T` is the theory's program code. The program tests
whether a formula is an axiom. For first-order PRA the codes are `FOL.PRA.language`
and `FOL.PRA.isAxiom.code`.
-/

pra

namespace FOL.PRA

/-- `proofOf L T a p` says that `p` encodes a proof with conclusion `a` in the language `L`
from the axioms recognized by program `T`. -/
fol_def proofOf over PRA (L T : Nat) : term → term → formula := fun a p =>
  eval[FOL.isProof.code L T](p) = succ(zero) ∧ eval[FOL.Proof.conclusion.code](p) = a

/-- Formula `pr_T(a)` asserts that there exists a proof of the formula encoded by `a` from theory
`T` (encoded as program code of its axioms) of language `L`.

Use `num A` for `a` to assert provability of the formula with code `A`. -/
fol_def pr over PRA (L T : Nat) : term → formula := fun a => ∃ p, (proofOf L T a p)

fol_theorem pr_of_proofOf (L T : Nat) : PRA ⊢ ∀ a p,
    (proofOf L T a p) → (pr L T a) := by
  pintro a p checked
  pexists p
  pexact checked

/-- Sentence `con_T` asserts the consistency of the theory `T` in PRA. -/
fol_def con over PRA (L T : Nat) : formula :=
  ¬ (pr L T ${num Formula.falsum})

end FOL.PRA

end
