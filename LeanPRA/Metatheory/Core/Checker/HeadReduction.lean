module

public import LeanPRA.Metatheory.Core.Properties.Normalization.Soundness

/-!
# Reduction used by structural conversion

Successful reduction preserves typed equality at the input arity or predicate signature.

- `exposeTerm_sound` and `exposePredicate_sound` justify beta, let, and zero-recursion batches.
- `unfoldTermHead_sound` and `unfoldPredicateHead_sound` justify unfolding a named head.
- `exposeRecursor_sound` justifies exposing the next recursor comparison.
-/

namespace LeanPRA.Core

open Theory

public theorem exposeTerm_sound {n changed E Ξ Γ t u k}
    (typed : TermTyping E Ξ Γ t k) (run : exposeTerm n changed t = .ok u) :
    TermEq E Ξ Γ t (u.getD t) k := by
  induction n generalizing changed Γ t u k with
  | zero => simp [exposeTerm, exhausted, fail] at run
  | succ n ih =>
    cases t with
    | letE name value body =>
      obtain ⟨j, hv, hb⟩ := typed.inv_let
      have eq := ih (hb.subst0 hv) run
      cases u with
      | none => exact .refl typed
      | some u => exact (TermEq.zeta hv hb).trans eq
    | primrec b s a =>
      cases a with
      | zero =>
        obtain ⟨rfl, hb, hs, _⟩ := typed.inv_primrec
        have eq := ih hb run
        cases u with
        | none => exact .refl typed
        | some u => exact (TermEq.primrecZero hb hs).trans eq
      | _ =>
        simp only [exposeTerm, pure, Except.pure, Except.ok.injEq] at run
        split at run <;> subst u <;> exact .refl typed
    | app f a =>
      obtain ⟨hf, ha⟩ := typed.inv_app
      simp only [exposeTerm, CheckResult.bind_eq_ok] at run
      obtain ⟨g, hg, run⟩ := run
      have eqf := ih hf hg
      cases h : g.getD f with
      | lam name body =>
        rw [h] at eqf
        obtain ⟨j, hj, hb⟩ := eqf.regularity.2.inv_lam
        have : k = j := Nat.succ.inj hj
        subst j
        simp only [h] at run
        have eq := ih (hb.subst0 ha) run
        cases u with
        | none => exact .refl typed
        | some u => exact (TermEq.app eqf (.refl ha)).trans ((TermEq.beta hb ha).trans eq)
      | _ =>
        simp only [h] at run
        cases g with
        | none =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          split at run <;> subst u <;> exact .refl typed
        | some g =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst u
          exact .app eqf (.refl ha)
    | _ =>
      simp only [exposeTerm, pure, Except.pure, Except.ok.injEq] at run
      split at run <;> subst u <;> exact .refl typed

private theorem map_some {result : CheckResult (Option α)} {f : α → β} {y : β}
    (run : result.map (Option.map f) = .ok (some y)) :
    ∃ x, result = .ok (some x) ∧ f x = y := by
  cases result with
  | error e => simp [Except.map] at run
  | ok value =>
    cases value with
    | none => simp [Except.map] at run
    | some x => exact ⟨x, rfl, by simpa [Except.map] using run⟩

public theorem unfoldTermHead_sound {E Ξ Γ t u k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) (run : unfoldTermHead E t = .ok u) :
    TermEq E Ξ Γ t (u.getD t) k := by
  cases u with
  | none => exact .refl typed
  | some u =>
    induction t using Term.rec (motive_2 := fun _ => True) generalizing Γ u k with
    | definition name fs ih =>
      obtain ⟨d, lookup, args, rfl⟩ := typed.inv_definition
      simp only [unfoldTermHead, Environment.lookup, lookup, pure, Except.pure,
        Except.ok.injEq, Option.some.injEq] at run
      subst u
      have body : TermTyping E { functions := d.functions } [] d.body d.arity := by
        cases (valid.lookup lookup).2 with | function body => exact body
      have instantiated := body.instantiate args
      simp only [List.nil_append, List.length_nil] at instantiated
      exact .delta lookup args instantiated
    | app f a ihf iha =>
      obtain ⟨g, h, rfl⟩ := map_some run
      exact .app (ihf typed.inv_app.1 g h) (.refl typed.inv_app.2)
    | nil | cons => trivial
    | _ => simp [unfoldTermHead, pure, Except.pure] at run

public theorem exposePredicate_sound {n changed E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) (run : exposePredicate n changed P = .ok Q) :
    PredicateEq E Ξ Γ P (Q.getD P) σ := by
  induction n generalizing changed Γ P Q σ with
  | zero => simp [exposePredicate, exhausted, fail] at run
  | succ n ih =>
    cases P with
    | letTerm name value body =>
      obtain ⟨⟨j, hv⟩, hb⟩ := typed.inv_letTerm
      have eq := ih hb run
      cases Q with
      | none => exact .refl typed
      | some Q => exact (PredicateEq.zetaTerm hv hb).trans eq
    | letPredicate name value body =>
      obtain ⟨⟨τ, hv⟩, hb⟩ := typed.inv_letPredicate
      have eq := ih hb run
      cases Q with
      | none => exact .refl typed
      | some Q => exact (PredicateEq.zetaPredicate hv hb).trans eq
    | app f a =>
      obtain ⟨hf, ha⟩ := typed.app_function
      simp only [exposePredicate, CheckResult.bind_eq_ok] at run
      obtain ⟨g, hg, run⟩ := run
      have eqf := ih hf hg
      cases h : g.getD f with
      | lam name body =>
        rw [h] at eqf
        have hb := (eqf.regularity valid).2.lam_body
        simp only [h] at run
        have eq := ih (hb.subst0 valid ha) run
        cases Q with
        | none => exact .refl typed
        | some Q => exact (PredicateEq.app eqf (.refl ha)).trans ((PredicateEq.beta hb ha).trans eq)
      | _ =>
        simp only [h] at run
        cases g with
        | none =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          split at run <;> subst Q <;> exact .refl typed
        | some g =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst Q
          exact .app eqf (.refl ha)
    | _ =>
      simp only [exposePredicate, pure, Except.pure, Except.ok.injEq] at run
      split at run <;> subst Q <;> exact .refl typed

public theorem unfoldPredicateHead_sound {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) (run : unfoldPredicateHead E P = .ok Q) :
    PredicateEq E Ξ Γ P (Q.getD P) σ := by
  cases Q with
  | none => exact .refl typed
  | some Q =>
    induction P using Predicate.rec (motive_2 := fun _ => True) generalizing Γ Q σ with
    | definition name fs ps ih =>
      obtain ⟨d, lookup, fs, ps, sub⟩ := typed.inv_definition
      simp only [unfoldPredicateHead, Environment.lookup, lookup, pure, Except.pure,
        Except.ok.injEq, Option.some.injEq] at run
      subst Q
      exact .delta lookup fs ps ((valid.predicate_instance lookup fs ps).subsumption sub) sub
    | app f a ih =>
      obtain ⟨g, h, rfl⟩ := map_some run
      exact .app (ih typed.app_function.1 g h) (.refl typed.app_function.2)
    | nil | cons => trivial
    | _ => simp [unfoldPredicateHead, pure, Except.pure] at run

public theorem exposeRecursor_sound {n E Ξ Γ t u k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) (run : exposeRecursor n E t = .ok u) :
    TermEq E Ξ Γ t (u.getD t) k := by
  cases u with
  | none => exact .refl typed
  | some u =>
    cases t with
    | primrec b s a =>
      obtain ⟨rfl, hb, hs, ha⟩ := typed.inv_primrec
      simp only [exposeRecursor, CheckResult.bind_eq_ok] at run
      obtain ⟨m, hm, run⟩ := run
      have eq := whnfTerm_sound valid ha hm
      have congr := TermEq.primrec (.refl hb) (.refl hs) eq
      cases m with
      | zero => exact congr.trans ((TermEq.primrecZero hb hs).trans (exposeTerm_sound hb run))
      | app f p =>
        cases f with
        | succ =>
          have hp := eq.regularity.2.inv_app.2
          exact congr.trans ((TermEq.primrecSucc hb hs hp).trans
            (exposeTerm_sound (.app (.app hs hp) (.primrec hb hs hp)) run))
        | _ =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          split at run
          next => contradiction
          next => cases run; exact congr
      | _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at run
        split at run
        next => contradiction
        next => cases run; exact congr
    | _ => simp [exposeRecursor, pure, Except.pure] at run

end LeanPRA.Core
