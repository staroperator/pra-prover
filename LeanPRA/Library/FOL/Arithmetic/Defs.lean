module

public meta import LeanPRA.Library.FOL.DSL.Tactic.Basic
public meta import LeanPRA.Library.FOL.DSL.Tactic.Rewrite
public meta import LeanPRA.Library.FOL.DSL.Tactic.Induction

/-!
# Robinson arithmetic and Peano arithmetic

This module declares the first-order language of arithmetic together with Robinson arithmetic (`Q`)
and Peano arithmetic (`PA`), and sets up surface notation and display handlers for arithmetic
terms and order formulas.

- `FOL.Arithmetic.language` has the constant `zero` and the functions `succ`, `add`, and `mul`.
- Arithmetic terms use numerals, `S`, `+`, and `*`; `FOL.Arithmetic.le` and `FOL.Arithmetic.lt`
  define `≤` and `<`.
- `FOL.Q.isAxiom` checks the seven axioms of Robinson arithmetic.
- `FOL.PA.isAxiom` extends `Q` with the full first-order induction schema `FOL.PA.induction`.
- `FOL.Q.subtheory_PA` transfers `Q` derivations to `PA`, and `FOL.Q.consistent_of_PA` transfers
  consistency from `PA` to `Q`.

The shared Hilbert checker supplies classical first-order logic with equality. Induction permits
additional surrounding parameters in its formula argument.
-/

namespace FOL

public meta section

open Lean Elab Command LeanPRA.Surface

open LeanPRA.Library.FOL.DSL

syntax:max num : folTerm
syntax:75 (priority := high) &"S " folTerm:75 : folTerm
syntax:65 folTerm:65 " + " folTerm:66 : folTerm
syntax:70 folTerm:70 " * " folTerm:71 : folTerm
syntax:50 folTerm " ≤ " folTerm : folFormula
syntax:50 folTerm " < " folTerm : folFormula

macro_rules
  | `(folTerm| $n:num) => do
    let mut term ← `(folTerm| zero())
    for _ in [:n.getNat] do term ← `(folTerm| succ($term))
    return term
  | `(folTerm| S $t:folTerm) => `(folTerm| succ($t))
  | `(folTerm| $a:folTerm + $b:folTerm) => `(folTerm| add($a, $b))
  | `(folTerm| $a:folTerm * $b:folTerm) => `(folTerm| mul($a, $b))
  | `(folFormula| $a:folTerm ≤ $b:folTerm) => `(folFormula| _root_.FOL.Arithmetic.le($a, $b))
  | `(folFormula| $a:folTerm < $b:folTerm) => `(folFormula| _root_.FOL.Arithmetic.lt($a, $b))

/-- Display numerals and arithmetic operations (`S`, `+`, and `*`) for symbols with the
corresponding names and arities. -/
@[fol_term_display zero, fol_term_display succ, fol_term_display add, fol_term_display mul]
def displayArithmeticTerm : TermDisplay := fun L term t => do
  let numeralValue? : TermView → Option Nat := fun t => Id.run do
    let mut t := t
    let mut n := 0
    repeat
      match t with
      | .app i [a] =>
        if L.functions[i]? == some (`succ, 1) then
          n := n + 1
          t := a
        else return none
      | .constant i => return if L.constants[i]? == some `zero then some n else none
      | _ => return none
    return none
  if let some n := numeralValue? t then
    return some (1024, ← `(folTerm| $(Syntax.mkNumLit (toString n)):num))
  let .app i args := t | return none
  match L.functions[i]?, args with
  | some (`succ, 1), [a] =>
    return some (75, ← `(folTerm| S $(← term a 75):folTerm))
  | some (`add, 2), [a, b] =>
    return some (65, ← `(folTerm| $(← term a 65):folTerm + $(← term b 66):folTerm))
  | some (`mul, 2), [a, b] =>
    return some (70, ← `(folTerm| $(← term a 70):folTerm * $(← term b 71):folTerm))
  | _, _ => return none

end

pra

fol_language Arithmetic where
  constant zero
  function succ of 1
  function add of 2
  function mul of 2

namespace Arithmetic

/-- `le x y` is the less-equal formula `x ≤ y`, defined as `∃ z, z + x = y`. -/
fol_def le over Arithmetic (x y : term) : formula := ∃ z, z + x = y

/-- `lt x y` is the less-than formula `x < y`, defined as `le(S x, y)`. -/
fol_def lt over Arithmetic (x y : term) : formula := le(S x, y)

theorem constants_language : FOL.Language.constants language = 1 := by
  rw [language, FOL.Language.constants_make]

theorem functionCount_language : FOL.Language.functionCount language = 3 := by
  rw [language, FOL.Language.functionCount_make,
    Sequence.length_cons, Sequence.length_cons, Sequence.length_cons, Sequence.length_nil]

theorem succ_arity : FOL.Language.functionArity language 0 = 1 := by
  rw [language, FOL.Language.functionArity_make, Sequence.get_cons_zero]

theorem add_arity : FOL.Language.functionArity language 1 = 2 := by
  rw [language, FOL.Language.functionArity_make,
    Sequence.get_cons_succ, Sequence.get_cons_zero]

theorem mul_arity : FOL.Language.functionArity language 2 = 2 := by
  rw [language, FOL.Language.functionArity_make,
    Sequence.get_cons_succ, Sequence.get_cons_succ, Sequence.get_cons_zero]

end Arithmetic

fol_theory Q over Arithmetic where
  axiom succ_ne_zero := ∀ x, S x ≠ 0
  axiom succ_injective := ∀ x y, S x = S y → x = y
  axiom zero_or_succ := ∀ x, x = 0 ∨ (∃ y, x = S y)
  axiom add_zero := ∀ x, x + 0 = x
  axiom add_succ := ∀ x y, x + S y = S (x + y)
  axiom mul_zero := ∀ x, x * 0 = 0
  axiom mul_succ := ∀ x y, x * S y = x * y + x

fol_theory PA over Arithmetic extends Q where
  axiom induction (p : formula of 1) :=
    p 0 → (∀ x, p x → p (S x)) → ∀ x, p x

end

@[expose] public section

pra

namespace Q

open Arithmetic

theorem isAxiom_implies_PA : ∀ A, Q.isAxiom A = 1 → PA.isAxiom A = 1 :=
  PA.isAxiom_of_parent

/-- Every theorem of `Q` is a theorem of `PA`. -/
theorem subtheory_PA : FOL.Subtheory language Q.isAxiom PA.isAxiom :=
  FOL.subtheory_of_axiom_inclusion language Q.isAxiom PA.isAxiom isAxiom_implies_PA

/-- If `PA` is consistent, then `Q` is consistent. -/
theorem consistent_of_PA :
    FOL.Consistent language PA.isAxiom → FOL.Consistent language Q.isAxiom :=
  FOL.Consistent.of_subtheory language Q.isAxiom PA.isAxiom subtheory_PA

end Q

end

end

end FOL
