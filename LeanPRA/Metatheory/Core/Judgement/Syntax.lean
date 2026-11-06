module

public import LeanPRA.Core.Syntax

/-!
# Boolean comparison of core syntax

The `LawfulBEq` instances for `FormulaSort`, `PredicateSignature`, `BinderInfo`, `Term`, and
`Predicate` connect Boolean comparison to host Lean equality of core syntax.
-/

public section

namespace LeanPRA.Core

deriving instance ReflBEq, LawfulBEq for FormulaSort, PredicateSignature, BinderInfo

private theorem term_beq (t : Term) : ∀ u, Term.beq t u = true ↔ t = u := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ us, Term.beqList ts us = true ↔ ts = us) <;>
    (first | (intro u; cases u) | (rename_i u; cases u)) <;>
    simp_all [Term.beq, Term.beqList, and_assoc]

instance : ReflBEq Term := ⟨fun {t} => (term_beq t t).mpr rfl⟩
instance : LawfulBEq Term := ⟨fun {t u} h => (term_beq t u).mp h⟩

private theorem predicate_beq (P : Predicate) : ∀ Q, Predicate.beq P Q = true ↔ P = Q := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ qs, Predicate.beqList ps qs = true ↔ ps = qs) <;>
    (first | (intro Q; cases Q) | (rename_i Q; cases Q)) <;>
    simp_all [Predicate.beq, Predicate.beqList, and_assoc]

instance : ReflBEq Predicate := ⟨fun {P} => (predicate_beq P P).mpr rfl⟩
instance : LawfulBEq Predicate := ⟨fun {P Q} h => (predicate_beq P Q).mp h⟩

end LeanPRA.Core
