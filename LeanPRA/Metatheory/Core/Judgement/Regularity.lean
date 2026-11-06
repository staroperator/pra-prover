module

public import LeanPRA.Metatheory.Core.Judgement.Instantiation

/-!
# Formation of assumptions and proof conclusions

- `ContextWF.lookup` forms the formula at a valid proof-hypothesis index.
- `ContextWF.shift` preserves all hypotheses when introducing a local variable.
- `ProofTyping.regularity` forms the conclusion of every declarative proof derivation.

Proof regularity assumes a valid global environment and valid local proof assumptions. Theorem
references use valid global lookup and simultaneous parameter instantiation. Equality regularity
is in `Conversion`.
-/

namespace LeanPRA.Core.Theory

private theorem context_lookup {E Ξ Γ H} (h : ContextWF E Ξ Γ H) {i : Nat} {A}
    (lookup : H[i]? = some A) : PredicateTyping E Ξ Γ A ⟨0, .prop⟩ := by
  induction h generalizing i with
  | nil => simp at lookup
  | cons head tail ih =>
      cases i with
      | zero => have heq := Option.some.inj lookup; subst heq; exact head
      | succ i => exact ih lookup

private theorem proof_regularity {E Ξ Γ H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H p A) (context : ContextWF E Ξ Γ H) :
    PredicateTyping E Ξ Γ A ⟨0, .prop⟩ := by
  induction h with
  | hyp lookup => exact context_lookup context lookup
  | trueIntro => exact .subsumption .true .lift
  | theoremE lookup functions predicates =>
      obtain ⟨_, wf⟩ := EnvironmentWF.lookup valid lookup
      cases wf with
      | theoremE type body =>
          simpa only [List.nil_append, List.length_nil] using
            PredicateTyping.instantiate valid type ⟨functions, predicates⟩
  | impIntro antecedent body ih => exact .imp antecedent (ih (.cons antecedent context))
  | impElim f a ihf iha =>
      obtain ⟨s, ha, hb, sub⟩ := PredicateTyping.inv_imp (ihf context)
      exact .subsumption hb sub
  | andIntro a b iha ihb => exact .and (iha context) (ihb context)
  | andLeft pair ih =>
      obtain ⟨s, ha, hb, sub⟩ := PredicateTyping.inv_and (ih context)
      exact .subsumption ha sub
  | andRight pair ih =>
      obtain ⟨s, ha, hb, sub⟩ := PredicateTyping.inv_and (ih context)
      exact .subsumption hb sub
  | orLeft other proof ih => exact .or (ih context) other
  | orRight other proof ih => exact .or other (ih context)
  | orElim target scrutinee left right ihp ihl ihr => exact target
  | falseElim target proof ih => exact target
  | forallIntro motive body ih => exact .all motive
  | forallElim proof argument ih =>
      exact .app (PredicateTyping.inv_all (ih context)).2 argument
  | existsIntro motive witness proof ih => exact .ex motive
  | existsElim target scrutinee body ihp ihb => exact target
  | letE type value body ihv ihb => exact ihb (.cons type context)
  | letTerm value body ih => exact ih context
  | letPredicate value body ih => exact ih context
  | ascribe type proof ih => exact type
  | eqRefl term => exact .subsumption (.equal term term) .lift
  | eqSubst motive equality proof ihe ihp =>
      exact .app motive (PredicateTyping.inv_equal (ihe context)).2.1
  | succNeZero term =>
      exact .imp (.subsumption (.equal (.app .succ term) .zero) .lift) (.subsumption .false .lift)
  | succInj proof ih =>
      obtain ⟨left, right, sub⟩ := PredicateTyping.inv_equal (ih context)
      exact .subsumption (.equal (TermTyping.inv_app left).2 (TermTyping.inv_app right).2) .lift
  | lem formula => exact .or formula (.imp formula (.subsumption .false .lift))
  | induction motive base step argument ihb ihs => exact .subsumption (.app motive argument) .lift
  | conversion proof type ih => exact (PredicateEq.regularity valid type).2

/-- A valid hypothesis is an arity-zero predicate of sort Prop. -/
public theorem ContextWF.lookup {E Ξ Γ H} (h : ContextWF E Ξ Γ H) {i : Nat} {A}
    (lookup : H[i]? = some A) : PredicateTyping E Ξ Γ A ⟨0, .prop⟩ := context_lookup h lookup

/-- Introducing a term local shifts all hypotheses without changing their validity. -/
public theorem ContextWF.shift {E Ξ Γ H} (valid : EnvironmentWF E)
    (h : ContextWF E Ξ Γ H) (j : Arity) :
    ContextWF E Ξ (j :: Γ) (H.map Predicate.shift) := by
  simpa only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte] using
    ContextWF.rename valid h (fun i => i + 1) (by intro i k hi; exact hi)

/-- Every declarative proof has a well-formed formula as conclusion. -/
public theorem ProofTyping.regularity {E Ξ Γ H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H p A) (context : ContextWF E Ξ Γ H) :
    PredicateTyping E Ξ Γ A ⟨0, .prop⟩ := proof_regularity valid h context

end LeanPRA.Core.Theory
