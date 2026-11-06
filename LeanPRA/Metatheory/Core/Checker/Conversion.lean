module

public import LeanPRA.Metatheory.Core.Checker.DefEq

/-!
# Soundness and completeness of conversion checking

- `equalTerms_sound` and `equalTerms_complete` relate numerical comparison to typed conversion.
- `equalPredicates_sound` and `equalPredicates_complete` cover full predicate signatures.
- `equalFormulas_sound` and `equalFormulas_complete` specialize conversion to arity-zero formulas.

Soundness assumes independently typed endpoints in a valid environment. Completeness supplies a
depth at which every larger comparison succeeds for definitionally equal inputs.
-/

namespace LeanPRA.Core

open Theory

private theorem terms_equal {n E Ξ Γ t u k} (valid : EnvironmentWF E)
    (left : TermTyping E Ξ Γ t k) (right : TermTyping E Ξ Γ u k)
    (run : equalTerms n E k t u = .ok ()) : TermEq E Ξ Γ t u k := by
  simp only [equalTerms, CheckResult.bind_eq_ok] at run
  obtain ⟨equal, hequal, run⟩ := run
  cases equal with
  | false => simp [fail] at run
  | true => exact defEqTerm_sound valid left right hequal

private theorem predicates_equal {n E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (left : PredicateTyping E Ξ Γ P σ) (right : PredicateTyping E Ξ Γ Q σ)
    (run : equalPredicates n E σ.arity P Q = .ok ()) : PredicateEq E Ξ Γ P Q σ := by
  simp only [equalPredicates, CheckResult.bind_eq_ok] at run
  obtain ⟨equal, hequal, run⟩ := run
  cases equal with
  | false => simp [fail] at run
  | true => exact defEqPredicate_sound valid left right hequal

/-- Successful term comparison is sound for two terms at the supplied arity. -/
public theorem equalTerms_sound {n E Ξ Γ t u k} (valid : EnvironmentWF E)
    (left : TermTyping E Ξ Γ t k) (right : TermTyping E Ξ Γ u k)
    (run : equalTerms n E k t u = .ok ()) : TermEq E Ξ Γ t u k := terms_equal valid left right run

/-- Successful predicate comparison is sound at any full signature shared by its inputs. -/
public theorem equalPredicates_sound {n E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (left : PredicateTyping E Ξ Γ P σ) (right : PredicateTyping E Ξ Γ Q σ)
    (run : equalPredicates n E σ.arity P Q = .ok ()) : PredicateEq E Ξ Γ P Q σ :=
  predicates_equal valid left right run

/-- Successful formula comparison is sound at either formula sort shared by its inputs. -/
public theorem equalFormulas_sound {n E Ξ Γ P Q s} (valid : EnvironmentWF E)
    (left : PredicateTyping E Ξ Γ P ⟨0, s⟩) (right : PredicateTyping E Ξ Γ Q ⟨0, s⟩)
    (run : equalFormulas n E P Q = .ok ()) : PredicateEq E Ξ Γ P Q ⟨0, s⟩ :=
  predicates_equal valid left right run

end LeanPRA.Core

namespace LeanPRA.Core

open Theory

/-- Numerical conversion succeeds at every depth beyond a finite bound. -/
public theorem equalTerms_complete {E Ξ Γ t u k} (valid : EnvironmentWF E)
    (eq : TermEq E Ξ Γ t u k) : ∃ n, ∀ m ≥ n, equalTerms m E k t u = .ok () := by
  obtain ⟨n, h⟩ := defEqTerm_complete valid eq
  exact ⟨n, fun m hm => by simp [equalTerms, h m hm, pure, Except.pure]⟩

/-- Predicate conversion succeeds at the full signature's arity, including QF inclusion. -/
public theorem equalPredicates_complete {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ P Q σ) :
    ∃ n, ∀ m ≥ n, equalPredicates m E σ.arity P Q = .ok () := by
  obtain ⟨n, h⟩ := defEqPredicate_complete valid eq
  exact ⟨n, fun m hm => by simp [equalPredicates, h m hm, pure, Except.pure]⟩

/-- Formula conversion succeeds at every sufficiently large depth. -/
public theorem equalFormulas_complete {E Ξ Γ P Q s} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ P Q ⟨0, s⟩) :
    ∃ n, ∀ m ≥ n, equalFormulas m E P Q = .ok () := equalPredicates_complete valid eq

end LeanPRA.Core
