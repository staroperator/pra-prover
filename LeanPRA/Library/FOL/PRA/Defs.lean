module

public import LeanPRA.Library.Computability.Code
public import LeanPRA.Library.FOL.DSL.Tactic

/-!
# The first-order theory of PRA

- `FOL.PRA.language` has zero, successor, Cantor pairing, and one unary function `eval[e]` for
  each program code `e`.
- `FOL.PRA.isAxiom` checks the successor and pairing laws, the program equations, and induction
  with quantifier-free bodies.
- The `eval_*` theorems instantiate the program equations at arbitrary term codes.
-/

open LeanPRA.Library.FOL.DSL in
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

namespace Axiom

theorem constants_language : Language.constants language = 1 := by
  rw [language, Language.constants_make]

theorem isConstant_zero : Language.IsConstant language 0 := by
  apply Language.isConstant_of_lt
  rw [constants_language]
  exact lt_succ_self 0

theorem functionCount_language : Language.functionCount language = 2 := by
  rw [language, Language.functionCount_make, Sequence.length_cons,
    Sequence.length_cons, Sequence.length_nil]

theorem isFunction_succ : Language.IsFunction language 0 := by
  apply Language.isFunction_of_lt
  rw [functionCount_language]
  rfl

theorem isFunction_pair : Language.IsFunction language 1 := by
  apply Language.isFunction_of_lt
  rw [functionCount_language]
  rfl

theorem evalFamily_lt : 0 < Language.functionFamilyCount language := by
  have count : ∀ L, Language.functionFamilyCount L =
      Sequence.length (Language.functionFamilies L) := fun L => rfl
  rw [count, language, Language.functionFamilies_make, Sequence.length_cons, Sequence.length_nil]
  exact lt_succ_self 0

theorem isFunction_program : ∀ e,
    Language.IsFunction language (Language.functionFamilyMember language 0 e) :=
  fun e => Language.isFunction_familyMember language 0 e evalFamily_lt

theorem succ_arity : Language.functionSymbolArity language 0 = 1 := by
  have h : 0 < Language.functionCount language := by
    rw [functionCount_language]
    rfl
  rw [Language.functionSymbolArity_of_lt language 0 h, language, Language.functionArity_make,
    Sequence.get_cons_zero]

theorem pair_arity : Language.functionSymbolArity language 1 = 2 := by
  have h : 1 < Language.functionCount language := by
    rw [functionCount_language]
    rfl
  rw [Language.functionSymbolArity_of_lt language 1 h, language, Language.functionArity_make,
    Sequence.get_cons_succ, Sequence.get_cons_zero]

theorem eval_arity : ∀ e,
    Language.functionSymbolArity language (Language.functionFamilyMember language 0 e) = 1 := by
  intro e
  rw [Language.functionSymbolArity_familyMember language 0 e evalFamily_lt]
  have arity : ∀ L, Language.functionFamilyArity L 0 =
      S (Sequence.get (Language.functionFamilies L) 0) := fun L => rfl
  rw [arity, language, Language.functionFamilies_make, Sequence.get_cons_zero]

end Axiom

fol_theorem succ_ne_zero (x : Nat) : PRA ⊢ succ(${x}) ≠ zero := by
  pexact PRA.succ_ne_zero[${x}]

fol_theorem succ_injective (x y : Nat) : PRA ⊢ succ(${x}) = succ(${y}) → ${x} = ${y} := by
  pexact PRA.succ_injective[${x}, ${y}]

fol_theorem pair_zero_zero : PRA ⊢ pair(zero, zero) = zero := by
  pexact PRA.pair_zero_zero

fol_theorem pair_zero_succ (y : Nat) : PRA ⊢ pair(zero, succ(${y})) = succ(pair(${y}, zero)) := by
  pexact PRA.pair_zero_succ[${y}]

fol_theorem pair_succ (x y : Nat) : PRA ⊢
    pair(succ(${x}), ${y}) = succ(pair(${x}, succ(${y}))) := by
  pexact PRA.pair_succ[${x}, ${y}]

fol_theorem pair_eval_left_right (t : Nat) : PRA ⊢
    pair(eval[Primrec.Code.left](${t}), eval[Primrec.Code.right](${t})) = ${t} := by
  pexact PRA.pair_eval_left_right[${t}]

fol_theorem eval_zero (x : Nat) : PRA ⊢ eval[Primrec.Code.zero](${x}) = zero := by
  pexact PRA.eval_zero[${x}]

fol_theorem eval_succ (x : Nat) : PRA ⊢ eval[Primrec.Code.succ](${x}) = succ(${x}) := by
  pexact PRA.eval_succ[${x}]

fol_theorem eval_left (x y : Nat) : PRA ⊢ eval[Primrec.Code.left](pair(${x}, ${y})) = ${x} := by
  pexact PRA.eval_left[${x}, ${y}]

fol_theorem eval_right (x y : Nat) : PRA ⊢ eval[Primrec.Code.right](pair(${x}, ${y})) = ${y} := by
  pexact PRA.eval_right[${x}, ${y}]

fol_theorem eval_pair (f g x : Nat) : PRA ⊢
    eval[Primrec.Code.pair f g](${x}) = pair(eval[f](${x}), eval[g](${x})) := by
  pexact PRA.eval_pair (f := f) (g := g)[${x}]

fol_theorem eval_comp (f g x : Nat) : PRA ⊢
    eval[Primrec.Code.comp f g](${x}) = eval[f](eval[g](${x})) := by
  pexact PRA.eval_comp (f := f) (g := g)[${x}]

fol_theorem eval_rec_zero (f g x : Nat) : PRA ⊢
    eval[Primrec.Code.rec f g](pair(${x}, zero)) = eval[f](${x}) := by
  pexact PRA.eval_rec_zero (f := f) (g := g)[${x}]

fol_theorem eval_rec_succ (f g x n : Nat) : PRA ⊢
    eval[Primrec.Code.rec f g](pair(${x}, succ(${n}))) =
      eval[g](pair(${x}, pair(${n}, eval[Primrec.Code.rec f g](pair(${x}, ${n}))))) := by
  pexact PRA.eval_rec_succ (f := f) (g := g)[${x}, ${n}]

/-- A quantifier-free formula gives a first-order proof of its induction instance. -/
theorem «induction» (P : Nat) : Formula.isQuantifierFree language P = 1 →
    (PRA ⊢ ${induction.formula P}) := by
  intro h
  pexact PRA.induction (P := fun x => ${P}[x])[]

end PRA

end FOL

end
