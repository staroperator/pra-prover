# Metatheory of PRAProver

This directory contains the formal metatheory of the PRA language in Lean.

## Core Language Metatheory

[`PRAProver/Metatheory/Core`](Core) defines the declarative typing and conversion rules of the core
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

## First-Order and Quantifier-Free PRA

[`PRAProver/Metatheory/PRA`](PRA) defines the first-order theory of PRA and two quantifier-free
calculi, and establishes witness extraction, conservativity, and consistency.

### Syntax and Calculi

[`PRA/Defs.lean`](PRA/Defs.lean) defines the syntax and proof systems.

- Primitive recursive expressions `Primrec n` and PRA terms `PRA.Term n`.
- Quantifier-free formulas `PRA.QFFormula n` and quantified formulas `PRA.Formula n`.
- Derivability judgements `PRA.Proof` (classical first-order PRA with quantifier-free induction),
  `PRA.QFProof` (classical quantifier-free PRA), and `PRA.QFProofI` (intuitionistic quantifier-free
  PRA).

### Main Results

#### 1. Classical and Intuitionistic Equivalence

In [`PRA/Intuitionistic.lean`](PRA/Intuitionistic.lean), classical and intuitionistic
quantifier-free PRA prove the same formulas:

```lean
theorem qfProofI_iff_qfProof {φ : QFFormula n} : QFProofI φ ↔ QFProof φ
```

#### 2. Witness Extraction and Conservativity

In [`PRA/Witness.lean`](PRA/Witness.lean) and [`PRA/Conservative.lean`](PRA/Conservative.lean),
existential theorems of first-order PRA with quantifier-free matrices have primitive-recursive
witnesses provable in quantifier-free PRA, and first-order PRA is conservative over quantifier-free
PRA:

```lean
theorem exists_primrec_witness {P : QFFormula (n + 1)} (h : Proof (.ex P.toFormula)) :
    ∃ f : Primrec n, QFProof (P.inst (.app f Term.var))

theorem forall_exists_primrec_witness {P : QFFormula 2} (h : Proof (.all (.ex P.toFormula))) :
    ∃ f : Primrec 1, QFProof (P.inst (.app f Term.var))

theorem proof_iff_qfProof {A : QFFormula n} : Proof A.toFormula ↔ QFProof A
```

#### 3. Consistency

In [`PRA/Consistency.lean`](PRA/Consistency.lean), first-order PRA is proved consistent in the host
theory Lean by interpreting expressions and formulas over `Nat`:

```lean
theorem consistent {n : Nat} : ¬ Proof (.false : Formula n)
```

## Translation to First-Order PRA

[`PRAProver/Metatheory/Translation`](Translation) translates the typed PRA language into the
first-order theory of PRA, proves that the translation preserves typing, definitional equality, and
provability, and derives the consistency of the typed PRA language.

### Translation Judgements

[`Translation/Defs.lean`](Translation/Defs.lean) defines the relational translation.

- Contextual translations `TermTranslation` and `PredicateTranslation`.
- Argument list translations `FunctionArgumentsTranslation` and `PredicateArgumentsTranslation`.
- Closed declaration schema translation `DeclarationTranslation`.

### Main Results

#### 1. Translation Correctness

In [`Translation/Correctness.lean`](Translation/Correctness.lean), well-typed terms and predicates
are characterized by the existence of translations, and well-formed declarations translate to
primitive-recursive schemas and provable first-order PRA formulas:

```lean
theorem termTyping_iff_translation {E Ξ t k} (valid : EnvironmentWF E) :
    TermTyping E Ξ [] t k ↔ ∃ f : FunctionAssignment Ξ.functions → Primrec k,
      ∀ ρ, TermTranslation E Ξ ρ 0 t k (f ρ)

theorem predicateTyping_iff_translation {E Ξ P σ} (valid : EnvironmentWF E) :
    PredicateTyping E Ξ [] P σ ↔
      ∃ A : FunctionAssignment Ξ.functions → PredicateAssignment Ξ.predicates → PRA.Formula σ.arity,
        ∀ ρ π, PredicateTranslation E Ξ ρ π 0 P σ (A ρ π) ∧
          (σ.sort = .qf → (A ρ π).QuantifierFree)

theorem declarationTranslation_correct {E d} (valid : EnvironmentWF E)
    (formed : DeclarationWF E d) : ∃ translated, DeclarationTranslation E d translated
```

#### 2. Consistency of the PRA Language

In [`Translation/Consistency.lean`](Translation/Consistency.lean), the translation and the
consistency of first-order PRA establish that no theorem of `False` can be admitted against or
stored in a well-formed environment:

```lean
theorem declaration_consistent {E} {d : TheoremDefinition} (valid : EnvironmentWF E)
    (formed : DeclarationWF E (.theoremE d)) : d.type ≠ .false

theorem environment_consistent {E name} {d : TheoremDefinition} (valid : EnvironmentWF E)
    (lookup : E[name]? = some (.theoremE d)) : d.type ≠ .false
```
