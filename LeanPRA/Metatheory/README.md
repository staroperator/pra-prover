# Metatheory of Lean-PRA

This directory contains the formal metatheory of the PRA language in Lean.

## Core Language Metatheory

[`LeanPRA/Metatheory/Core`](Core) defines the declarative typing and conversion rules of the core
language, proves the soundness and completeness of the executable core checker against those rules,
and establishes normalization and structural properties of the calculus.

### Judgements

[`Core/Judgement/Defs.lean`](Core/Judgement/Defs.lean) defines the declarative judgements.

- Typing judgements `TermTyping`, `PredicateTyping`, and `ProofTyping`.
- Definitional equality judgements `TermEq` and `PredicateEq`.
- Context well-formedness `ContextWF`, `DeclarationWF`, and `EnvironmentWF`.

### Main Results

#### 1. Checker Soundness and Completeness

In [`Core/Checker/Correctness.lean`](Core/Checker/Correctness.lean), the core checkers are proved
sound and complete with respect to the declarative judgements:

```lean
theorem checkDeclaration_sound {n E d F} (valid : EnvironmentWF E)
    (run : checkDeclaration n E d = .ok F) :
    E[d.name]? = none ∧ DeclarationWF E d ∧ F = E.insert d.name d ∧
      EnvironmentWF F ∧ EnvironmentExtends E F

theorem checkDeclaration_complete {E d} (valid : EnvironmentWF E)
    (fresh : E[d.name]? = none) (formed : DeclarationWF E d) :
    ∃ n, ∀ m ≥ n, checkDeclaration m E d = .ok (E.insert d.name d)
```

#### 2. Normalization and Canonicity

In [`Core/Properties/Normalization/CanonicalForms.lean`](Core/Properties/Normalization/CanonicalForms.lean)
and [`Core/Properties/Normalization/Canonicity.lean`](Core/Properties/Normalization/Canonicity.lean),
well-typed terms and predicates have unique beta-normal, eta-long representatives, and closed
numerical terms reduce to unique numerals:

```lean
theorem TermEq.unique_normal_form {E Ξ Γ t k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) :
    ∃ u, TermNormal k u ∧ TermEq E Ξ Γ t u k ∧
      ∀ v, TermNormal k v → TermEq E Ξ Γ t v k → v = u

theorem PredicateEq.unique_normal_form {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) :
    ∃ Q, PredicateNormal σ.arity Q ∧ PredicateEq E Ξ Γ P Q σ ∧
      ∀ R, PredicateNormal σ.arity R → PredicateEq E Ξ Γ P R σ → R = Q

theorem TermTyping.closed_canonicity_unique {E t} (valid : EnvironmentWF E)
    (typed : TermTyping E {} [] t 0) :
    ∃ n, TermEq E {} [] t (Term.numeral n) 0 ∧
      ∀ m, TermEq E {} [] t (Term.numeral m) 0 → m = n
```

#### 3. Type Uniqueness and Sort Coherence

In [`Core/Properties/UniqueTyping.lean`](Core/Properties/UniqueTyping.lean) and
[`Core/Properties/SortCoherence.lean`](Core/Properties/SortCoherence.lean), terms have unique
arities, predicates have unique principal signatures under `QFProp`-to-`Prop` subtyping, proofs
have unique conclusions up to conversion, and predicate conversion is coherent across sort
inclusion:

```lean
theorem TermTyping.unique {E Ξ Γ t k j}
    (left : TermTyping E Ξ Γ t k) (right : TermTyping E Ξ Γ t j) : k = j

theorem PredicateTyping.principal {E Ξ Γ P σ} (typed : PredicateTyping E Ξ Γ P σ) :
    ∃ τ, PredicateTyping E Ξ Γ P τ ∧ ∀ υ, PredicateTyping E Ξ Γ P υ → PredicateSubtyping τ υ

theorem ProofTyping.unique {E Ξ Γ Δ p A B} (valid : EnvironmentWF E)
    (ctx : ContextWF E Ξ Γ Δ) (left : ProofTyping E Ξ Γ Δ p A)
    (right : ProofTyping E Ξ Γ Δ p B) : PredicateEq E Ξ Γ A B ⟨0, .prop⟩

theorem PredicateEq.qf_iff_prop {E Ξ Γ P Q k} (valid : EnvironmentWF E)
    (left : PredicateTyping E Ξ Γ P ⟨k, .qf⟩)
    (right : PredicateTyping E Ξ Γ Q ⟨k, .qf⟩) :
    PredicateEq E Ξ Γ P Q ⟨k, .qf⟩ ↔ PredicateEq E Ξ Γ P Q ⟨k, .prop⟩
```

#### 4. Decidability of Conversion

In [`Core/Properties/Decidability.lean`](Core/Properties/Decidability.lean), definitional equality
on well-typed terms and predicates in a well-formed environment is decidable:

```lean
def decideTermEq {E Ξ Γ t u k} (valid : EnvironmentWF E)
    (left : TermTyping E Ξ Γ t k) (right : TermTyping E Ξ Γ u k) :
    Decidable (TermEq E Ξ Γ t u k)

def decidePredicateEq {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (left : PredicateTyping E Ξ Γ P σ) (right : PredicateTyping E Ξ Γ Q σ) :
    Decidable (PredicateEq E Ξ Γ P Q σ)
```
