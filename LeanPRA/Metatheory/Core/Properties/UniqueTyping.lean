module

public import LeanPRA.Metatheory.Core.Checker.Typing.ProofCompleteness

/-!
# Unique types and principal predicate signatures

- `TermTyping.unique` states that a term has a unique numerical arity.
- `PredicateTyping.principal` supplies a least admissible full signature.
- `PredicateTyping.arity_unique` and `PrincipalPredicateSignature.unique` give uniqueness.
- `ProofTyping.unique` identifies the conclusions of the same proof up to conversion.
- `inferPredicate_unique` makes successful predicate inference independent of depth.
- `inferPredicate_principal` and `inferPredicate_principal_complete` relate inference to
  principal signatures.

Term and predicate formation results hold over arbitrary environments; proof uniqueness requires
valid declarations and well-formed local proof assumptions.
-/

namespace LeanPRA.Core.Theory

private def context (Ξ : ParameterContext) (Γ : LocalContext) (Δ : ProofContext := []) : Context :=
  { functions := Ξ.functions, predicates := Ξ.predicates, locals := Γ, proofs := Δ }

private theorem inferred_signature {E Ξ Γ P σ τ}
    (left : PredicateTyping E Ξ Γ P σ) (right : PredicateTyping E Ξ Γ P τ) :
    ∃ υ, PredicateTyping E Ξ Γ P υ ∧ PredicateSubtyping υ σ ∧ PredicateSubtyping υ τ := by
  obtain ⟨υ, hs, n, hn⟩ := inferPredicate_complete left
  obtain ⟨ν, ht, m, hm⟩ := inferPredicate_complete right
  have run := hn (max n m) (by omega) (context Ξ Γ) rfl rfl
  have same := hm (max n m) (by omega) (context Ξ Γ) rfl rfl
  have eq : υ = ν := Except.ok.inj (run.symm.trans same)
  subst ν
  exact ⟨υ, inferPredicate_sound run, hs, ht⟩

/-- Two derivations of the same term in the same contexts have equal arities. -/
public theorem TermTyping.unique {E Ξ Γ t k j} (left : TermTyping E Ξ Γ t k)
    (right : TermTyping E Ξ Γ t j) : k = j := by
  obtain ⟨n, hn⟩ := inferTerm_complete left
  obtain ⟨m, hm⟩ := inferTerm_complete right
  exact Except.ok.inj ((hn (max n m) (by omega) (context Ξ Γ) rfl rfl).symm.trans
    (hm (max n m) (by omega) (context Ξ Γ) rfl rfl))

/-- A principal signature is itself derivable and is included in every derivable signature. -/
@[expose] public def PrincipalPredicateSignature (E : Environment) (Ξ : ParameterContext)
    (Γ : LocalContext) (P : Predicate) (σ : PredicateSignature) : Prop :=
  PredicateTyping E Ξ Γ P σ ∧ ∀ τ, PredicateTyping E Ξ Γ P τ → PredicateSubtyping σ τ

/-- Every formed predicate has a least admissible signature. -/
public theorem PredicateTyping.principal {E Ξ Γ P σ} (typed : PredicateTyping E Ξ Γ P σ) :
    ∃ τ, PrincipalPredicateSignature E Ξ Γ P τ := by
  obtain ⟨τ, below, n, hn⟩ := inferPredicate_complete typed
  have formed := inferPredicate_sound (hn n (by omega) (context Ξ Γ) rfl rfl)
  refine ⟨τ, formed, ?_⟩
  intro υ hu
  obtain ⟨ν, sub, m, hm⟩ := inferPredicate_complete hu
  have eq : τ = ν := Except.ok.inj
    ((hn (max n m) (by omega) (context Ξ Γ) rfl rfl).symm.trans
      (hm (max n m) (by omega) (context Ξ Γ) rfl rfl))
  exact eq ▸ sub

/-- Subsumption changes only sort, so predicate arity is unique. -/
public theorem PredicateTyping.arity_unique {E Ξ Γ P σ τ}
    (left : PredicateTyping E Ξ Γ P σ) (right : PredicateTyping E Ξ Γ P τ) :
    σ.arity = τ.arity := by
  obtain ⟨υ, _, hs, ht⟩ := inferred_signature left right
  exact hs.arity_eq.symm.trans ht.arity_eq

/-- A predicate's least full signature is unique. -/
public theorem PrincipalPredicateSignature.unique {E Ξ Γ P σ τ}
    (left : PrincipalPredicateSignature E Ξ Γ P σ)
    (right : PrincipalPredicateSignature E Ξ Γ P τ) : σ = τ := by
  have a := left.2 τ right.1
  have b := right.2 σ left.1
  cases a <;> cases b <;> rfl

/-- Every admissible signature is exactly a supertype of the principal signature. -/
public theorem PrincipalPredicateSignature.typing_iff {E Ξ Γ P σ}
    (principal : PrincipalPredicateSignature E Ξ Γ P σ) (τ : PredicateSignature) :
    PredicateTyping E Ξ Γ P τ ↔ PredicateSubtyping σ τ :=
  ⟨principal.2 τ, fun sub => .subsumption principal.1 sub⟩

/-- The same explicit proof has definitionally equal conclusion formulas in a valid context. -/
public theorem ProofTyping.unique {E Ξ Γ Δ p A B} (valid : EnvironmentWF E)
    (ctx : ContextWF E Ξ Γ Δ) (left : ProofTyping E Ξ Γ Δ p A)
    (right : ProofTyping E Ξ Γ Δ p B) : PredicateEq E Ξ Γ A B ⟨0, .prop⟩ := by
  obtain ⟨C, eqA, n, hn⟩ := inferProof_complete (c := context Ξ Γ Δ) valid ctx left
  obtain ⟨D, eqB, m, hm⟩ := inferProof_complete (c := context Ξ Γ Δ) valid ctx right
  have eq : C = D := Except.ok.inj
    ((hn (max n m) (by omega)).symm.trans (hm (max n m) (by omega)))
  subst D
  exact .trans eqA.symm eqB

end LeanPRA.Core.Theory

namespace LeanPRA.Core

private theorem unique {n m E c P σ τ} (left : inferPredicate n E c P = .ok σ)
    (right : inferPredicate m E c P = .ok τ) : σ = τ := by
  induction n generalizing m c P σ τ with
  | zero => simp [inferPredicate, exhausted, fail] at left
  | succ n ih =>
      cases m with
      | zero => simp [inferPredicate, exhausted, fail] at right
      | succ m =>
          cases P <;> rw [inferPredicate.eq_def] at left right <;>
            simp only [CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok,
              pure, Except.pure, Except.ok.injEq] at left right
          case false => exact left.symm.trans right
          case true => exact left.symm.trans right
          case letTerm =>
              obtain ⟨_, _, hb⟩ := left
              obtain ⟨_, _, hc⟩ := right
              exact ih hb hc
          case letPredicate =>
              obtain ⟨_, _, hb⟩ := left
              obtain ⟨_, _, hc⟩ := right
              exact ih hb hc
          case equal a b =>
              obtain ⟨_, _, _, _, rfl⟩ := left
              obtain ⟨_, _, _, _, rfl⟩ := right
              rfl
          case imp A B =>
              obtain ⟨s, hs, t, ht, _, _, _, _, rfl⟩ := left
              obtain ⟨u, hu, v, hv, _, _, _, _, rfl⟩ := right
              rw [ih hs hu, ih ht hv]
          case and A B =>
              obtain ⟨s, hs, t, ht, _, _, _, _, rfl⟩ := left
              obtain ⟨u, hu, v, hv, _, _, _, _, rfl⟩ := right
              rw [ih hs hu, ih ht hv]
          case or A B =>
              obtain ⟨s, hs, t, ht, _, _, _, _, rfl⟩ := left
              obtain ⟨u, hu, v, hv, _, _, _, _, rfl⟩ := right
              rw [ih hs hu, ih ht hv]
          case all P =>
              obtain ⟨_, _, _, _, rfl⟩ := left
              obtain ⟨_, _, _, _, rfl⟩ := right
              rfl
          case ex P =>
              obtain ⟨_, _, _, _, rfl⟩ := left
              obtain ⟨_, _, _, _, rfl⟩ := right
              rfl
          case parameter i =>
              split at left <;> simp_all [fail]
          case lam P =>
              obtain ⟨s, hs, rfl⟩ := left
              obtain ⟨t, ht, rfl⟩ := right
              rw [ih hs ht]
          case app P a =>
              obtain ⟨s, hs, left⟩ := left
              obtain ⟨t, ht, right⟩ := right
              have eq := ih hs ht
              subst t
              split at left
              next => simp [fail] at left
              next k hk =>
                  rw [hk] at right
                  simp only [CheckResult.bind_eq_ok, Except.ok.injEq] at left right
                  obtain ⟨_, _, rfl⟩ := left
                  obtain ⟨_, _, rfl⟩ := right
                  rfl
          case definition name fs ps =>
              split at left
              next d lookup =>
                  rw [lookup] at right
                  simp only [CheckResult.bind_eq_ok, Except.ok.injEq] at left right
                  obtain ⟨_, _, _, _, _, _, rfl⟩ := left
                  obtain ⟨_, _, _, _, _, _, rfl⟩ := right
                  rfl
              next =>
                  simp [referenceError, fail] at left
                  split at left <;> contradiction

/-- Successful predicate inference is independent of recursive depth. -/
public theorem inferPredicate_unique {n m E c P σ τ}
    (left : inferPredicate n E c P = .ok σ) (right : inferPredicate m E c P = .ok τ) :
    σ = τ := unique left right

end LeanPRA.Core

namespace LeanPRA.Core

open Theory

/-- Every successful predicate inference returns the least admissible full signature. -/
public theorem inferPredicate_principal {n E c P σ}
    (run : inferPredicate n E c P = .ok σ) :
    PrincipalPredicateSignature E c.parameters c.locals P σ := by
  refine ⟨inferPredicate_sound run, ?_⟩
  intro τ formed
  obtain ⟨υ, below, m, hm⟩ := inferPredicate_complete formed
  have eq := inferPredicate_unique run (hm m (by omega) c rfl rfl)
  exact eq ▸ below

/-- Inference eventually computes a given principal signature exactly. -/
public theorem inferPredicate_principal_complete {E Ξ Γ P σ}
    (principal : PrincipalPredicateSignature E Ξ Γ P σ) :
    ∃ n, ∀ m ≥ n, ∀ c : Context, c.parameters = Ξ → c.locals = Γ →
      inferPredicate m E c P = .ok σ := by
  obtain ⟨τ, below, n, hn⟩ := inferPredicate_complete principal.1
  let c : Context := { functions := Ξ.functions, predicates := Ξ.predicates, locals := Γ }
  have other := inferPredicate_principal (hn n (by omega) c rfl rfl)
  have same := principal.unique other
  exact ⟨n, same ▸ hn⟩

end LeanPRA.Core
