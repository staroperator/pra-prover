module

public import LeanPRA.Library.FOL.PRA.Defs

/-!
# Numerals in first-order PRA

- `num n` applies successor `n` times to zero.
- `num_zero` and `num_succ` give its defining equations.
- `subst_num` shows that substitution leaves numerals unchanged.
-/

pra

namespace FOL.PRA

/-- The numeral for `n` consists of `n` successors of zero. -/
fol_def num over PRA : Nat → term := fun n =>
  ${primrec (Term.const language 0) (fun _ t => Term.app language 0 t) n}

theorem num_zero : num 0 = fol_term[PRA | zero] := rfl

theorem num_succ : ∀ n, num (S n) = fol_term[PRA | succ(${num n})] :=
  fun n => rfl

/-- A substitution leaves a numeral unchanged because it has no free variables. -/
theorem subst_num (f : Nat → Nat) : ∀ n,
    Term.subst f language (num n) = num n := by
  intro n
  induction n with k ih
  · rw [num_zero]
    exact Term.subst_const f language 0 isConstant_zero
  · rw [num_succ, Term.subst_app_one f language 0 (num k) isFunction_succ succ_arity, ih]

end FOL.PRA

end

open LeanPRA.Library.FOL.DSL in
run_cmd registerClosedTerm `FOL.PRA.num `FOL.PRA.subst_num
