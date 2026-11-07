module

public import LeanPRA.Metatheory.PRA.Consistency
public import LeanPRA.Metatheory.Translation.Correctness
import Std.Data.ExtHashMap.Lemmas

/-!
# Consistency of the PRA language

Consistency of the declarative PRA language, derived from `declarationTranslation_correct` and
`PRA.consistent`:

- `declaration_consistent` shows that no theorem declaration well-formed in a well-formed
  environment has `.false` as its statement, even when the theorem takes function or predicate
  parameters.
- `environment_consistent` shows that no theorem entry in a well-formed environment has `.false`
  as its statement.
-/

namespace LeanPRA.Translation

open Core Core.Theory

private theorem false_translation {E Ξ ρ π n A}
    (translation : PredicateTranslation E Ξ ρ π n .false ⟨0, .prop⟩ A) : A = .false := by
  cases translation
  rfl

/-- No theorem declaration well-formed in a well-formed environment has `.false` as its
statement. -/
public theorem declaration_consistent {E : Environment} {d : TheoremDefinition}
    (valid : EnvironmentWF E) (formed : DeclarationWF E (.theoremE d)) :
    d.type ≠ .false := by
  intro falseType
  obtain ⟨target, translation⟩ := declarationTranslation_correct valid formed
  cases translation with
  | theoremE statement proof =>
      let ρ : FunctionAssignment d.functions := fun _ _ _ => Primrec.comp₀ .zero
      let π : PredicateAssignment d.predicates := fun _ _ _ => ⟨.false, fun _ => True.intro⟩
      have translated := statement ρ π
      rw [falseType] at translated
      have h := proof ρ π
      rw [false_translation translated] at h
      exact PRA.consistent h

/-- No theorem entry in a well-formed environment has `.false` as its statement. -/
public theorem environment_consistent {E : Environment} (valid : EnvironmentWF E)
    {name : Lean.Name} {d : TheoremDefinition} (lookup : E[name]? = some (.theoremE d)) :
    d.type ≠ .false := by
  induction valid with
  | empty => simp at lookup
  | @insert E e previous fresh formed ih =>
      by_cases sameName : e.name = name
      · have same : e = .theoremE d := by
          simpa only [Std.ExtHashMap.getElem?_insert, sameName, beq_self_eq_true, ↓reduceIte,
            Option.some.injEq] using lookup
        subst e
        exact declaration_consistent previous formed
      · apply ih
        simpa [Std.ExtHashMap.getElem?_insert, sameName] using lookup

end LeanPRA.Translation
