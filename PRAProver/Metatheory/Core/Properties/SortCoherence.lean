module

public import PRAProver.Metatheory.Core.Checker.Conversion

/-!
# Coherence of predicate equality under sort inclusion

`PredicateEq.qf_iff_prop` identifies equality at QFProp and Prop when both endpoints are already
quantifier-free at the same arity. Its downward direction uses the common normalization algorithm
and its soundness at the independently established QF signature.
-/

namespace PRAProver.Core.Theory

/-- Two independently QF predicates are convertible at QFProp if and only if they are convertible
at Prop. -/
public theorem PredicateEq.qf_iff_prop {E Ξ Γ P Q k} (valid : EnvironmentWF E)
    (left : PredicateTyping E Ξ Γ P ⟨k, .qf⟩)
    (right : PredicateTyping E Ξ Γ Q ⟨k, .qf⟩) :
    PredicateEq E Ξ Γ P Q ⟨k, .qf⟩ ↔ PredicateEq E Ξ Γ P Q ⟨k, .prop⟩ := by
  constructor
  · intro eq; exact .subsumption eq .lift
  · intro eq
    obtain ⟨n, hn⟩ := equalPredicates_complete valid eq
    exact equalPredicates_sound valid left right (hn n (by omega))

end PRAProver.Core.Theory
