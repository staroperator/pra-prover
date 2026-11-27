module

public import PRAProver.Metatheory.Core.Checker.Conversion
import PRAProver.Metatheory.Core.Properties.Normalization.Soundness

/-!
# Deciding conversion on typed inputs

- `decideTermEq` decides typed numerical conversion in a valid environment.
- `decidePredicateEq` decides predicate conversion at a shared full signature.

The procedures search increasing recursive depths until both normalizations succeed, then compare
syntax. Their termination proofs use normalization of the supplied typing derivations; exhaustion
at an intermediate depth triggers the next depth step.
-/

namespace PRAProver.Core

open Theory

private def SearchStep (test : Nat → Option α) (i j : Nat) : Prop :=
  i = j + 1 ∧ test j = none

private theorem search_accessible (test : Nat → Option α) (d : Nat) :
    ∀ n, (test (n + d)).isSome = true → Acc (SearchStep test) n := by
  induction d with
  | zero =>
      intro n success
      apply Acc.intro
      intro i step
      simp only [SearchStep] at step
      simp [step.2] at success
  | succ d ih =>
      intro n success
      apply Acc.intro
      intro i step
      obtain ⟨rfl, _⟩ := step
      apply ih (n + 1)
      simpa only [Nat.add_assoc, Nat.add_comm d 1] using success

private theorem search_wellFounded (test : Nat → Option α)
    (terminates : ∃ n, ∀ m ≥ n, (test m).isSome = true) : WellFounded (SearchStep test) := by
  constructor
  intro n
  obtain ⟨m, hm⟩ := terminates
  exact search_accessible test m n (hm (n + m) (by omega))

private def search (test : Nat → Option α)
    (terminates : ∃ n, ∀ m ≥ n, (test m).isSome = true) (n : Nat) :
    {value : α // ∃ depth, test depth = some value} :=
  match run : test n with
  | some value => ⟨value, n, run⟩
  | none => search test terminates (n + 1)
termination_by (search_wellFounded test terminates).wrap n
decreasing_by exact ⟨rfl, run⟩

private def findResult (test : Nat → Option α)
    (terminates : ∃ n, ∀ m ≥ n, (test m).isSome = true) :
    {value : α // ∃ depth, test depth = some value} := search test terminates 0

private def termResult (n : Nat) (E : Environment) (k : Arity) (t : Term) : Option Term :=
  (reduceTerm n E k t).toOption

private theorem term_result {n E k t u} :
    termResult n E k t = some u ↔ reduceTerm n E k t = .ok u := by
  unfold termResult
  cases reduceTerm n E k t <;> simp [Except.toOption]

private def predicateResult (n : Nat) (E : Environment) (k : Arity) (P : Predicate) :
    Option Predicate := (reducePredicate n E k P).toOption

private theorem predicate_result {n E k P Q} :
    predicateResult n E k P = some Q ↔ reducePredicate n E k P = .ok Q := by
  unfold predicateResult
  cases reducePredicate n E k P <;> simp [Except.toOption]

/-- A terminating conversion decision for two independently typed terms at the same arity. -/
public def decideTermEq {E Ξ Γ t u k} (valid : EnvironmentWF E)
    (left : TermTyping E Ξ Γ t k) (right : TermTyping E Ξ Γ u k) :
    Decidable (TermEq E Ξ Γ t u k) := by
  have total {v} (typed : TermTyping E Ξ Γ v k) :
      ∃ n, ∀ m ≥ n, (termResult m E k v).isSome = true := by
    obtain ⟨n, w, hw⟩ := reduceTerm_terminates valid typed
    exact ⟨n, fun m hm => by simp [termResult, hw m hm, Except.toOption]⟩
  let a := findResult (fun n => termResult n E k t) (total left)
  let b := findResult (fun n => termResult n E k u) (total right)
  if same : a.val == b.val then
    apply isTrue
    obtain ⟨n, hn⟩ := a.property
    obtain ⟨m, hm⟩ := b.property
    have eq := eq_of_beq same
    exact .trans (reduceTerm_sound valid left (term_result.mp hn))
      (eq ▸ (reduceTerm_sound valid right (term_result.mp hm)).symm)
  else
    apply isFalse
    intro eq
    obtain ⟨n, hn⟩ := a.property
    obtain ⟨m, hm⟩ := b.property
    have same' := reduceTerm_congr valid eq (term_result.mp hn) (term_result.mp hm)
    exact same (by simp [same'])

/-- A terminating conversion decision for two predicates typed at the same full signature. -/
public def decidePredicateEq {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (left : PredicateTyping E Ξ Γ P σ) (right : PredicateTyping E Ξ Γ Q σ) :
    Decidable (PredicateEq E Ξ Γ P Q σ) := by
  have total {R} (typed : PredicateTyping E Ξ Γ R σ) :
      ∃ n, ∀ m ≥ n, (predicateResult m E σ.arity R).isSome = true := by
    obtain ⟨n, S, hS⟩ := reducePredicate_terminates valid typed
    exact ⟨n, fun m hm => by simp [predicateResult, hS m hm, Except.toOption]⟩
  let a := findResult (fun n => predicateResult n E σ.arity P) (total left)
  let b := findResult (fun n => predicateResult n E σ.arity Q) (total right)
  if same : a.val == b.val then
    apply isTrue
    obtain ⟨n, hn⟩ := a.property
    obtain ⟨m, hm⟩ := b.property
    have eq := eq_of_beq same
    exact .trans (reducePredicate_sound valid left (predicate_result.mp hn))
      (eq ▸ (reducePredicate_sound valid right (predicate_result.mp hm)).symm)
  else
    apply isFalse
    intro eq
    obtain ⟨n, hn⟩ := a.property
    obtain ⟨m, hm⟩ := b.property
    have same' := reducePredicate_congr valid eq (predicate_result.mp hn) (predicate_result.mp hm)
    exact same (by simp [same'])

end PRAProver.Core
