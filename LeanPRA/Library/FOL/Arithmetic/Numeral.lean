module

public import LeanPRA.Library.FOL.Arithmetic.Defs

/-!
# Arithmetic numerals

`FOL.Arithmetic.num n` encodes the closed arithmetic term with `n` applications of `succ` to
`zero`. These definitions and theorems connect natural numbers in PRA to the term codes used in
first-order arithmetic formulas:

- `FOL.Arithmetic.num` builds the term code for `n` by primitive recursion.
- `FOL.Arithmetic.bound_num` proves that `num n` has free-variable bound `0`.
- `FOL.Arithmetic.subst_num` proves that simultaneous term substitution leaves `num n` unchanged.

Registering `subst_num`, `num_zero`, and `num_succ` with the FOL frontend lets `num n` stay
symbolic under substitutions while reducing on concrete numerals.
-/

@[expose] public section

namespace FOL

pra

namespace Arithmetic

/-- `num n` is the arithmetic term code for the natural number `n`, formed by applying `succ`
`n` times to `zero`. -/
fol_def num over Arithmetic (n : Nat) : term :=
  ${primrec (FOL.Term.const language 0) (fun _ t => FOL.Term.app language 0 t) n}

theorem num_zero : num 0 = FOL.Term.const language 0 := rfl

theorem num_succ : ∀ n, num («S» n) = FOL.Term.app language 0 (num n) := fun n => rfl

theorem bound_num : ∀ n, FOL.Term.bound language (num n) = 0 := by
  have hc : FOL.Language.IsConstant language 0 := by
    apply FOL.Language.isConstant_of_lt
    rw [constants_language]
    exact lt_succ_self 0
  have hs : 0 < FOL.Language.functionCount language := by
    rw [functionCount_language]
    exact pos_of_ne_zero 3 (succ_ne_zero 2)
  have h := FOL.Language.isFunction_of_lt language 0 hs
  have ha : FOL.Language.functionSymbolArity language 0 = 1 := by
    rw [FOL.Language.functionSymbolArity_of_lt language 0 hs, succ_arity]
  intro n
  induction n with k ih
  · rw [num_zero]
    exact FOL.Term.bound_const language 0 hc
  · rw [num_succ, FOL.Term.bound_app_one language 0 (num k) h ha]
    exact ih

theorem subst_num (f : Nat → Nat) : ∀ n, FOL.Term.subst f language (num n) = num n := by
  have hc : FOL.Language.IsConstant language 0 := by
    apply FOL.Language.isConstant_of_lt
    rw [constants_language]
    exact lt_succ_self 0
  have hs : 0 < FOL.Language.functionCount language := by
    rw [functionCount_language]
    exact pos_of_ne_zero 3 (succ_ne_zero 2)
  have h := FOL.Language.isFunction_of_lt language 0 hs
  have ha : FOL.Language.functionSymbolArity language 0 = 1 := by
    rw [FOL.Language.functionSymbolArity_of_lt language 0 hs, succ_arity]
  intro n
  induction n with k ih
  · rw [num_zero]
    exact FOL.Term.subst_const f language 0 hc
  · rw [num_succ, FOL.Term.subst_app_one f language 0 (num k) h ha, ih]

end Arithmetic

end

open LeanPRA.Library.FOL.DSL in
run_cmd do
  registerClosedTerm `FOL.Arithmetic.num `FOL.Arithmetic.subst_num
  registerCalculation `FOL.Arithmetic.num_zero
  registerCalculation `FOL.Arithmetic.num_succ

end FOL
