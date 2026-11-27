module

public import PRAProver.Metatheory.Core.Judgement.Syntax
public import PRAProver.Metatheory.Core.Judgement.Regularity

/-!
# Formation premises at a specified signature

- `PredicateSubtyping.withArity` preserves a sort inclusion at another numerical arity.
- `PredicateTyping.toProp` includes any predicate into Prop at its existing arity.
- `PredicateSubtyping.join_left` and `join_right` include operands into their common sort.
- `PredicateTyping.app_function` and `PredicateTyping.lam_body` recover exact signatures.
- `ContextWF.pushProof` and `pushLocal` preserve formed assumptions under both binder kinds.
-/

namespace PRAProver.Core.Theory

/-- A predicate inclusion can be reused at any fixed numerical arity. -/
public theorem PredicateSubtyping.withArity {σ τ} (h : PredicateSubtyping σ τ) (k : Arity) :
    PredicateSubtyping ⟨k, σ.sort⟩ ⟨k, τ.sort⟩ := by cases h <;> constructor

/-- Either operand's sort includes into the join of two predicate sorts. -/
public theorem PredicateSubtyping.join_left (k : Arity) (s t : FormulaSort) :
    PredicateSubtyping ⟨k, s⟩ ⟨k, FormulaSort.join s t⟩ := by
  cases s <;> cases t <;> simp [FormulaSort.join] <;> constructor

/-- The second operand also includes into the common result sort. -/
public theorem PredicateSubtyping.join_right (k : Arity) (s t : FormulaSort) :
    PredicateSubtyping ⟨k, t⟩ ⟨k, FormulaSort.join s t⟩ := by
  cases s <;> cases t <;> simp [FormulaSort.join] <;> constructor

/-- Two sorts below a common upper bound have their join below the same bound. -/
public theorem PredicateSubtyping.join {k s t u}
    (left : PredicateSubtyping ⟨k, s⟩ ⟨k, u⟩)
    (right : PredicateSubtyping ⟨k, t⟩ ⟨k, u⟩) :
    PredicateSubtyping ⟨k, FormulaSort.join s t⟩ ⟨k, u⟩ := by
  cases s <;> cases t <;> cases u <;> cases left <;> cases right <;>
    simp [FormulaSort.join] <;> constructor

/-- Every predicate can be regarded as Prop without changing its arity. -/
public theorem PredicateTyping.toProp {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ) :
    PredicateTyping E Ξ Γ P ⟨σ.arity, .prop⟩ := by
  obtain ⟨k, s⟩ := σ
  cases s
  · exact .subsumption h .lift
  · exact h

/-- Application exposes a function at the result's exact sort. -/
public theorem PredicateTyping.app_function {E Ξ Γ P a k s}
    (h : PredicateTyping E Ξ Γ (.app P a) ⟨k, s⟩) :
    PredicateTyping E Ξ Γ P ⟨k + 1, s⟩ ∧ TermTyping E Ξ Γ a 0 := by
  obtain ⟨j, r, function, argument, sub⟩ := h.inv_app
  have arities := sub.arity_eq
  simp only at arities
  subst j
  exact ⟨.subsumption function (sub.withArity (k + 1)), argument⟩

/-- A lambda body has the lambda's exact result sort. -/
public theorem PredicateTyping.lam_body {E Ξ Γ P k s}
    (h : PredicateTyping E Ξ Γ (.lam binderName P) ⟨k + 1, s⟩) :
    PredicateTyping E Ξ (0 :: Γ) P ⟨k, s⟩ := by
  obtain ⟨j, r, body, sub⟩ := h.inv_lam
  have arities := Nat.succ.inj sub.arity_eq
  subst j
  exact .subsumption body (sub.withArity k)

/-- Adding a formed formula preserves the validity of proof assumptions. -/
public theorem ContextWF.pushProof {E} {c : Context} {A}
    (h : ContextWF E c.parameters c.locals c.proofs)
    (type : PredicateTyping E c.parameters c.locals A ⟨0, .prop⟩) :
    ContextWF E (c.pushProof A).parameters (c.pushProof A).locals (c.pushProof A).proofs :=
  .cons type h

/-- Introducing a local shifts all proof assumptions and preserves their validity. -/
public theorem ContextWF.pushLocal {E} {c : Context} (valid : EnvironmentWF E)
    (h : ContextWF E c.parameters c.locals c.proofs) (k : Arity) :
    ContextWF E (c.pushLocal k).parameters (c.pushLocal k).locals (c.pushLocal k).proofs :=
  h.shift valid k

end PRAProver.Core.Theory
