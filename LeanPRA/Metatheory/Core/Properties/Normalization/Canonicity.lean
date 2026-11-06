module

public import LeanPRA.Metatheory.Core.Properties.Normalization.CanonicalForms
import LeanPRA.Metatheory.Core.Properties.Normalization.Soundness

/-!
# Closed numerical canonicity

- `Term.numeral` writes a natural number as zero and repeated successor syntax.
- `TermNormal.closed_numeral` classifies parameter-free closed numerical normal forms.
- `TermTyping.closed_canonicity` gives a numeral definitionally equal to any closed number.
- `TermEq.numerals_iff` separates numerals; `TermTyping.closed_canonicity_unique` gives uniqueness.
- `reduceTerm_closed_numeral` computes the numeral at every sufficiently large depth.

The environment may contain any incrementally valid definitions and theorems, while function and
predicate parameters and local term variables are empty.
-/

namespace LeanPRA.Core

/-- Closed numerical syntax consisting of zero and repeated successor applications. -/
@[expose] public def Term.numeral : Nat → Term
  | 0 => .zero
  | n + 1 => .app .succ (Term.numeral n)

end LeanPRA.Core

namespace LeanPRA.Core.Theory

private theorem numeral_normal (n : Nat) : TermNormal 0 (Term.numeral n) := by
  induction n with
  | zero => exact .zero
  | succ n ih => exact .app .succ ih

private theorem numeral_typed (E Ξ Γ) (n : Nat) : TermTyping E Ξ Γ (Term.numeral n) 0 := by
  induction n with
  | zero => exact .zero
  | succ n ih => exact .app .succ ih

private theorem numeral_injective {n m} (h : Term.numeral n = Term.numeral m) : n = m := by
  induction n generalizing m with
  | zero => cases m <;> simp_all [Term.numeral]
  | succ n ih =>
      cases m with
      | zero => simp [Term.numeral] at h
      | succ m => exact congrArg Nat.succ (ih (Term.app.inj h).2)

private theorem closed_normal {k t} (h : TermNormal k t) :
    ∀ {E}, TermTyping E {} [] t k → k = 0 → ∃ n, t = Term.numeral n := by
  induction h using TermNormal.rec
    (motive_2 := fun t _ => ∀ {E k}, TermTyping E {} [] t k →
      (k = 1 ∧ t = .succ) ∨ (k = 0 ∧ ∃ n, t = Term.numeral (n + 1)))
  case zero => intro E _ _; exact ⟨0, rfl⟩
  case bvar => intro E typed _; simpa using typed.inv_bvar
  case parameter => intro E typed _; simpa using typed.inv_parameter
  case app f a fn arg ihf iha =>
      intro E typed _
      rcases ihf typed.inv_app.1 with ⟨_, rfl⟩ | ⟨bad, _⟩
      · obtain ⟨n, rfl⟩ := iha typed.inv_app.2 rfl
        exact ⟨n + 1, rfl⟩
      · contradiction
  case primrec b s a base step arg blocked ihb ihs iha =>
      intro E typed _
      obtain ⟨n, eq⟩ := iha typed.inv_primrec.2.2.2 rfl
      cases n with
      | zero => exact False.elim (blocked.1 eq)
      | succ n => exact False.elim (blocked.2 _ eq)
  case lam => intro E typed eq; simp_all
  case bvar => intro E k typed; simpa using typed.inv_bvar
  case parameter => intro E k typed; simpa using typed.inv_parameter
  case succ => exact Or.inl ⟨TermTyping.inv_succ ‹_›, rfl⟩
  case app f a fn arg ihf iha =>
      intro E k typed
      rcases ihf typed.inv_app.1 with ⟨arity, rfl⟩ | ⟨bad, _⟩
      · obtain ⟨n, rfl⟩ := iha typed.inv_app.2 rfl
        exact Or.inr ⟨by simpa using Nat.add_right_cancel arity, n, rfl⟩
      · exact False.elim (Nat.succ_ne_zero _ bad)

/-- A closed parameter-free normal term of arity zero is numeral syntax. -/
public theorem TermNormal.closed_numeral {E t} (normal : TermNormal 0 t)
    (typed : TermTyping E {} [] t 0) : ∃ n, t = Term.numeral n := closed_normal normal typed rfl

/-- Every closed numerical term in a valid environment is convertible to a numeral. -/
public theorem TermTyping.closed_canonicity {E t} (valid : EnvironmentWF E)
    (typed : TermTyping E {} [] t 0) : ∃ n, TermEq E {} [] t (Term.numeral n) 0 := by
  obtain ⟨u, normal, formed, eq⟩ := TermEq.normal_form valid typed
  obtain ⟨n, rfl⟩ := normal.closed_numeral formed
  exact ⟨n, eq⟩

/-- Distinct numeral syntax remains distinct under computational conversion, in any contexts. -/
public theorem TermEq.numerals_iff {E Ξ Γ n m} (valid : EnvironmentWF E) :
    TermEq E Ξ Γ (Term.numeral n) (Term.numeral m) 0 ↔ n = m := by
  rw [TermNormal.eq_iff valid (numeral_normal n) (numeral_normal m)
    (numeral_typed E Ξ Γ n) (numeral_typed E Ξ Γ m)]
  exact ⟨numeral_injective, fun eq => congrArg Term.numeral eq⟩

/-- A closed numerical term has exactly one numeral representative modulo conversion. -/
public theorem TermTyping.closed_canonicity_unique {E t} (valid : EnvironmentWF E)
    (typed : TermTyping E {} [] t 0) : ∃ n, TermEq E {} [] t (Term.numeral n) 0 ∧
      ∀ m, TermEq E {} [] t (Term.numeral m) 0 → m = n := by
  obtain ⟨n, hn⟩ := typed.closed_canonicity valid
  exact ⟨n, hn, fun m hm => (TermEq.numerals_iff valid).mp (.trans hm.symm hn)⟩

end LeanPRA.Core.Theory

namespace LeanPRA.Core

open Theory

/-- A closed number reduces to numeral syntax at every sufficiently large recursive depth. -/
public theorem reduceTerm_closed_numeral {E t} (valid : EnvironmentWF E)
    (typed : TermTyping E {} [] t 0) :
    ∃ value n, ∀ m ≥ n, reduceTerm m E 0 t = .ok (Term.numeral value) := by
  obtain ⟨n, u, hu⟩ := reduceTerm_terminates valid typed
  have eq := reduceTerm_sound valid typed (hu n (by omega))
  obtain ⟨value, rfl⟩ := (reduceTerm_normal (hu n (by omega))).closed_numeral eq.regularity.2
  exact ⟨value, n, hu⟩

end LeanPRA.Core
