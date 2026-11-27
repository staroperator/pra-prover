module

public import LeanPRA.Library.FOL.PRA.Provability.Computability
public import LeanPRA.Library.FOL.PRA.Derive.FOL
meta import LeanPRA.Library.FOL.DSL.Tactic

/-!
# Modus ponens for provability in first-order PRA

- `FOL.PRA.proofOf_mp`: modus ponens on proof codes in PRA.
- `FOL.PRA.pr_mp` and `FOL.PRA.pr_mp_num`: the third Hilbert–Bernays–Löb provability condition.
-/

pra

namespace FOL.PRA

derive_fol_pra (public := true) FOL.IsProofOf.mp as proofOf_mp

theorem pr_mp (L T : Nat) : PRA ⊢ ∀ a b,
    (pr L T (eval[Formula.imp.code](pair(a, b)))) →
    (pr L T a) → (pr L T b) := by
  pintro a b hab ha
  pcases hab with ⟨p, hp, ep⟩
  pcases ha with ⟨q, hq, eq⟩
  papply (pr_of_proofOf L T)[b, eval[Proof.mp.code](pair(b, pair(p, q)))]
  papply (proofOf_mp L T)[a, b, p, q]
  · pconstructor
    · pexact hp
    · pexact ep
  · pconstructor
    · pexact hq
    · pexact eq

/-- **The third Hilbert–Bernays–Löb provability condition:** given a first-order theory `T` and
formulas `A, B` of language `L`, `PRA ⊢ pr_T(⌜A → B⌝) → pr_T(⌜A⌝) → pr_T(⌜B⌝)`. Here `T` is
represented as a program code of its axioms. -/
theorem pr_mp_num (L T : Nat) : ∀ a b,
    (PRA ⊢ (pr L T ${num (Formula.imp a b)}) →
      (pr L T ${num a}) → (pr L T ${num b})) := by
  intro a b
  have computation := Formula.imp.computedBy (pair a b)
  rw [unpairLeft_pair, unpairRight_pair] at computation
  have result := eval_num_of_evaluates Formula.imp.code (pair a b) (Formula.imp a b)
    (Formula.imp.trace (pair a b)) computation
  have computes : (PRA ⊢ eval[Formula.imp.code](pair(${num a}, ${num b})) =
      ${num (Formula.imp a b)}) :=
    Evaluation.trans _ _ _ (Evaluation.congr_eval _ _ _ (pair_num a b)) result
  pintro hab ha
  papply (pr_mp L T)[${num a}, ${num b}]
  · pcases hab with ⟨p, verified, conclusion⟩
    pexists p
    pconstructor
    · pexact verified
    · prw [conclusion, computes]
  · pexact ha

end FOL.PRA

end
