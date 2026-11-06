module

public import LeanPRA.Metatheory.Core.Judgement.Regularity

/-!
# Inversion of explicit proof derivations

- `ProofPremises` lists the last primitive rule's premises for each proof constructor.
- `ProofTyping.inversion` recovers those premises and conversion to the given conclusion.
- `ProofTyping.inv_hyp` and `ProofTyping.inv_theorem` specialize the lookup cases.

The recovered conclusion is definitionally equal to the original conclusion at Prop because proof
typing admits conversion.
-/

namespace LeanPRA.Core.Theory

/-- Premises of the last primitive rule, before possible conversion of its conclusion. -/
@[expose] public def ProofPremises (E : Environment) (Ξ : ParameterContext) (Γ : LocalContext)
    (H : ProofContext) : Proof → Predicate → Prop
  | .hyp i, A => H[i]? = some A
  | .trueIntro, A => A = .true
  | .theoremE name fs ps, A =>
      ∃ d, E[name]? = some (.theoremE d) ∧ FunctionArguments E Ξ Γ fs d.functions ∧
        PredicateArguments E Ξ Γ ps d.predicates ∧ A = d.type.instantiate fs ps
  | .impIntro _ A p, C => ∃ B, C = .imp A B ∧ PredicateTyping E Ξ Γ A ⟨0, .prop⟩ ∧
      ProofTyping E Ξ Γ (A :: H) p B
  | .impElim p q, B => ∃ A, ProofTyping E Ξ Γ H p (.imp A B) ∧ ProofTyping E Ξ Γ H q A
  | .andIntro p q, C => ∃ A B, C = .and A B ∧ ProofTyping E Ξ Γ H p A ∧ ProofTyping E Ξ Γ H q B
  | .andLeft p, A => ∃ B, ProofTyping E Ξ Γ H p (.and A B)
  | .andRight p, B => ∃ A, ProofTyping E Ξ Γ H p (.and A B)
  | .orLeft B p, C => ∃ A, C = .or A B ∧ PredicateTyping E Ξ Γ B ⟨0, .prop⟩ ∧
      ProofTyping E Ξ Γ H p A
  | .orRight A p, C => ∃ B, C = .or A B ∧ PredicateTyping E Ξ Γ A ⟨0, .prop⟩ ∧
      ProofTyping E Ξ Γ H p B
  | .orElim _ _ C p q r, D => D = C ∧ PredicateTyping E Ξ Γ C ⟨0, .prop⟩ ∧
      ∃ A B, ProofTyping E Ξ Γ H p (.or A B) ∧ ProofTyping E Ξ Γ (A :: H) q C ∧
        ProofTyping E Ξ Γ (B :: H) r C
  | .falseElim A p, B => B = A ∧ PredicateTyping E Ξ Γ A ⟨0, .prop⟩ ∧
      ProofTyping E Ξ Γ H p .false
  | .forallIntro _ P p, A => A = .all P ∧ PredicateTyping E Ξ Γ P ⟨1, .prop⟩ ∧
      ProofTyping E Ξ (0 :: Γ) (H.map Predicate.shift) p (.app P.shift (.bvar 0))
  | .forallElim p a, A => ∃ P, A = .app P a ∧ ProofTyping E Ξ Γ H p (.all P) ∧
      TermTyping E Ξ Γ a 0
  | .existsIntro P a p, A => A = .ex P ∧ PredicateTyping E Ξ Γ P ⟨1, .prop⟩ ∧
      TermTyping E Ξ Γ a 0 ∧ ProofTyping E Ξ Γ H p (.app P a)
  | .existsElim _ _ C p q, D => D = C ∧ PredicateTyping E Ξ Γ C ⟨0, .prop⟩ ∧
      ∃ P, ProofTyping E Ξ Γ H p (.ex P) ∧
        ProofTyping E Ξ (0 :: Γ) (.app P.shift (.bvar 0) :: H.map Predicate.shift) q C.shift
  | .letE _ A p q, C => PredicateTyping E Ξ Γ A ⟨0, .prop⟩ ∧ ProofTyping E Ξ Γ H p A ∧
      ProofTyping E Ξ Γ (A :: H) q C
  | .letTerm _ a p, A => (∃ j, TermTyping E Ξ Γ a j) ∧ ProofTyping E Ξ Γ H p A
  | .letPredicate _ P p, A => (∃ σ, PredicateTyping E Ξ Γ P σ) ∧ ProofTyping E Ξ Γ H p A
  | .ascribe A p, B => B = A ∧ PredicateTyping E Ξ Γ A ⟨0, .prop⟩ ∧ ProofTyping E Ξ Γ H p A
  | .eqRefl t, A => A = .equal t t ∧ TermTyping E Ξ Γ t 0
  | .eqSubst P e p, A => PredicateTyping E Ξ Γ P ⟨1, .prop⟩ ∧
      ∃ a b, A = .app P b ∧ ProofTyping E Ξ Γ H e (.equal a b) ∧ ProofTyping E Ξ Γ H p (.app P a)
  | .succNeZero t, A => A = .imp (.equal (.app .succ t) .zero) .false ∧ TermTyping E Ξ Γ t 0
  | .succInj p, A => ∃ a b, A = .equal a b ∧
      ProofTyping E Ξ Γ H p (.equal (.app .succ a) (.app .succ b))
  | .lem A, B => B = .or A (.imp A .false) ∧ PredicateTyping E Ξ Γ A ⟨0, .prop⟩
  | .induction _ _ P b s n, A => A = .app P n ∧ PredicateTyping E Ξ Γ P ⟨1, .qf⟩ ∧
      ProofTyping E Ξ Γ H b (.app P .zero) ∧
      ProofTyping E Ξ (0 :: Γ) (.app P.shift (.bvar 0) :: H.map Predicate.shift)
        s (.app P.shift (.app .succ (.bvar 0))) ∧ TermTyping E Ξ Γ n 0

private theorem strip_conversion {E Ξ Γ H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H p A) (formed : PredicateTyping E Ξ Γ A ⟨0, .prop⟩) :
    ∃ B, ProofPremises E Ξ Γ H p B ∧ PredicateEq E Ξ Γ B A ⟨0, .prop⟩ := by
  induction h with
  | hyp lookup => refine ⟨_, ?_, .refl formed⟩; exact lookup
  | trueIntro => refine ⟨_, ?_, .refl formed⟩; rfl
  | theoremE lookup functions predicates =>
      refine ⟨_, ?_, .refl formed⟩
      exact ⟨_, lookup, functions, predicates, rfl⟩
  | impIntro antecedent body ih =>
      refine ⟨_, ?_, .refl formed⟩
      exact ⟨_, rfl, antecedent, body⟩
  | impElim f a ihf iha => refine ⟨_, ?_, .refl formed⟩; exact ⟨_, f, a⟩
  | andIntro p q ihp ihq => refine ⟨_, ?_, .refl formed⟩; exact ⟨_, _, rfl, p, q⟩
  | andLeft p ih => refine ⟨_, ?_, .refl formed⟩; exact ⟨_, p⟩
  | andRight p ih => refine ⟨_, ?_, .refl formed⟩; exact ⟨_, p⟩
  | orLeft other p ih => refine ⟨_, ?_, .refl formed⟩; exact ⟨_, rfl, other, p⟩
  | orRight other p ih => refine ⟨_, ?_, .refl formed⟩; exact ⟨_, rfl, other, p⟩
  | orElim target p q r ihp ihq ihr =>
      refine ⟨_, ?_, .refl formed⟩; exact ⟨rfl, target, _, _, p, q, r⟩
  | falseElim target p ih => refine ⟨_, ?_, .refl formed⟩; exact ⟨rfl, target, p⟩
  | forallIntro motive body ih => refine ⟨_, ?_, .refl formed⟩; exact ⟨rfl, motive, body⟩
  | forallElim p argument ih => refine ⟨_, ?_, .refl formed⟩; exact ⟨_, rfl, p, argument⟩
  | existsIntro motive witness p ih =>
      refine ⟨_, ?_, .refl formed⟩; exact ⟨rfl, motive, witness, p⟩
  | existsElim target p q ihp ihq =>
      refine ⟨_, ?_, .refl formed⟩; exact ⟨rfl, target, _, p, q⟩
  | letE type p q ihp ihq => refine ⟨_, ?_, .refl formed⟩; exact ⟨type, p, q⟩
  | letTerm value body ih => refine ⟨_, ?_, .refl formed⟩; exact ⟨⟨_, value⟩, body⟩
  | letPredicate value body ih => refine ⟨_, ?_, .refl formed⟩; exact ⟨⟨_, value⟩, body⟩
  | ascribe type p ih => refine ⟨_, ?_, .refl formed⟩; exact ⟨rfl, type, p⟩
  | eqRefl term => refine ⟨_, ?_, .refl formed⟩; exact ⟨rfl, term⟩
  | eqSubst motive e p ihe ihp =>
      refine ⟨_, ?_, .refl formed⟩; exact ⟨motive, _, _, rfl, e, p⟩
  | succNeZero term => refine ⟨_, ?_, .refl formed⟩; exact ⟨rfl, term⟩
  | succInj p ih => refine ⟨_, ?_, .refl formed⟩; exact ⟨_, _, rfl, p⟩
  | lem formula => refine ⟨_, ?_, .refl formed⟩; exact ⟨rfl, formula⟩
  | induction motive base step argument ihb ihs =>
      refine ⟨_, ?_, .refl formed⟩; exact ⟨rfl, motive, base, step, argument⟩
  | conversion p type ih =>
      obtain ⟨B, premises, eq⟩ := ih (PredicateEq.regularity valid type).1
      exact ⟨B, premises, .trans eq type⟩

/-- Recover the last primitive rule and a typed equality from its conclusion to the stated type. -/
public theorem ProofTyping.inversion {E Ξ Γ H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H p A) (context : ContextWF E Ξ Γ H) :
    ∃ B, ProofPremises E Ξ Γ H p B ∧ PredicateEq E Ξ Γ B A ⟨0, .prop⟩ :=
  strip_conversion valid h (ProofTyping.regularity valid h context)

/-- A proof-hypothesis use has the looked-up formula up to typed conversion. -/
public theorem ProofTyping.inv_hyp {E Ξ Γ H i A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H (.hyp i) A) (context : ContextWF E Ξ Γ H) :
    ∃ B, H[i]? = some B ∧ PredicateEq E Ξ Γ B A ⟨0, .prop⟩ := ProofTyping.inversion valid h context

/-- A theorem reference has its instantiated statement up to typed conversion. -/
public theorem ProofTyping.inv_theorem {E Ξ Γ H name fs ps A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H (.theoremE name fs ps) A) (context : ContextWF E Ξ Γ H) :
    ∃ d, E[name]? = some (.theoremE d) ∧ FunctionArguments E Ξ Γ fs d.functions ∧
      PredicateArguments E Ξ Γ ps d.predicates ∧
      PredicateEq E Ξ Γ (d.type.instantiate fs ps) A ⟨0, .prop⟩ := by
  obtain ⟨B, premises, eq⟩ := ProofTyping.inversion valid h context
  obtain ⟨d, lookup, functions, predicates, rfl⟩ := premises
  exact ⟨d, lookup, functions, predicates, eq⟩

end LeanPRA.Core.Theory
