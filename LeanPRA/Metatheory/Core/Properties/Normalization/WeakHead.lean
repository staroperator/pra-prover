module

public import LeanPRA.Metatheory.Core.Properties.Normalization.Depth
public import LeanPRA.Metatheory.Core.Properties.Normalization.Defs

/-!
# Weak-head output shape and stability

- `whnfTerm_normal` and `whnfPredicate_normal` characterize successful outputs.
- `whnfTerm_fixed` and `whnfPredicate_fixed` show that weak-head forms are preserved.
- `whnfTerm_complete` and `whnfPredicate_complete` supply a depth for weak-head forms.
-/

namespace LeanPRA.Core

open Theory

private theorem term_shape {n E t u} (run : whnfTerm n E t = .ok u) : TermWhnf u := by
  induction n generalizing t u with
  | zero => simp [whnfTerm, exhausted, fail] at run
  | succ n ih =>
      cases t <;> simp only [whnfTerm] at run
      case definition name fs =>
        split at run
        next => exact ih run
        next => simp [referenceError, fail] at run; split at run <;> contradiction
      case letE a body => exact ih run
      case app f a =>
        simp only [CheckResult.bind_eq_ok] at run
        obtain ⟨g, hg, run⟩ := run
        have ng := ih hg
        cases g with
        | lam body => exact ih run
        | primrec b s =>
            simp only [CheckResult.bind_eq_ok] at run
            obtain ⟨m, hm, run⟩ := run
            have nm := ih hm
            cases m with
            | zero => exact ih run
            | app f p =>
                cases f with
                | succ => exact ih run
                | _ =>
                    simp only [pure, Except.pure, Except.ok.injEq] at run
                    subst u
                    exact .primrec nm (by
                      constructor
                      · intro h; cases h
                      · intro p h; cases h)
            | _ =>
                simp only [pure, Except.pure, Except.ok.injEq] at run
                subst u
                exact .primrec nm (by
                  constructor
                  · intro h; cases h
                  · intro p h; cases h)
        | _ =>
            simp only [pure, Except.pure, Except.ok.injEq] at run
            subst u
            exact .app ng (by intro body name h; cases h) (by intro b s h; cases h)
      all_goals
        simp only [pure, Except.pure, Except.ok.injEq] at run
        subst u
        constructor

private theorem term_fixed {n E t u} (normal : TermWhnf t)
    (run : whnfTerm n E t = .ok u) : u = t := by
  induction normal generalizing n u with
  | app function notLam notRec ih =>
      cases n with
      | zero => simp [whnfTerm, exhausted, fail] at run
      | succ n =>
          simp only [whnfTerm, CheckResult.bind_eq_ok] at run
          obtain ⟨g, hg, run⟩ := run
          have := ih hg
          subst g
          split at run
          next => exact False.elim (notLam _ _ rfl)
          next => exact False.elim (notRec _ _ rfl)
          next => simpa only [pure, Except.pure, Except.ok.injEq] using run.symm
  | @primrec a b s argument blocked ih =>
      cases n with
      | zero => simp [whnfTerm, exhausted, fail] at run
      | succ n =>
          rw [whnfTerm.eq_def] at run
          cases n with
          | zero => simp [whnfTerm, exhausted, fail] at run
          | succ n =>
              simp only [Nat.add_one] at run
              rw [show whnfTerm (n + 1) E (.primrec b s) = .ok (.primrec b s) from rfl] at run
              simp only [CheckResult.bind_eq_ok, Except.ok.injEq] at run
              obtain ⟨_, rfl, run⟩ := run
              simp only [CheckResult.bind_eq_ok] at run
              obtain ⟨a', ha, run⟩ := run
              have := ih ha
              subst a'
              split at run
              next => exact False.elim (blocked.1 rfl)
              next => exact False.elim (blocked.2 _ rfl)
              next => simpa only [pure, Except.pure, Except.ok.injEq] using run.symm
  | _ => cases n <;> simp_all [whnfTerm, exhausted, fail, pure, Except.pure]

private theorem term_exists {E t} (normal : TermWhnf t) : ∃ n, whnfTerm n E t = .ok t := by
  induction normal with
  | app function notLam notRec ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [whnfTerm.eq_def]
      simp only [hn, bind, Except.bind]
      first
      | rfl
      | split
        next => exact False.elim (notLam _ _ rfl)
        next => exact False.elim (notRec _ _ rfl)
        next => rfl
  | @primrec a b s argument blocked ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 2, ?_⟩
      rw [whnfTerm.eq_def]
      simp only [Nat.add_succ, Nat.add_zero]
      rw [show whnfTerm (n + 1) E (.primrec b s) = .ok (.primrec b s) from rfl]
      simp only [bind, Except.bind]
      rw [whnfTerm_mono (m := n + 1) (Nat.le_succ n) hn]
      simp only
      split
      next => exact False.elim (blocked.1 rfl)
      next => exact False.elim (blocked.2 _ rfl)
      next => rfl
  | _ => exact ⟨1, by simp [whnfTerm, pure, Except.pure]⟩

private theorem predicate_shape {n E P Q} (run : whnfPredicate n E P = .ok Q) :
    PredicateWhnf Q := by
  induction n generalizing P Q with
  | zero => simp [whnfPredicate, exhausted, fail] at run
  | succ n ih =>
      cases P <;> simp only [whnfPredicate] at run
      case definition name fs ps =>
        split at run
        next => exact ih run
        next => simp [referenceError, fail] at run; split at run <;> contradiction
      case app f a =>
        simp only [CheckResult.bind_eq_ok] at run
        obtain ⟨g, hg, run⟩ := run
        have ng := ih hg
        cases g with
        | lam body => exact ih run
        | _ =>
            simp only [pure, Except.pure, Except.ok.injEq] at run
            subst Q
            exact .app ng (by intro body name h; cases h)
      case letTerm => exact ih run
      case letPredicate => exact ih run
      all_goals
        simp only [pure, Except.pure, Except.ok.injEq] at run
        subst Q
        constructor

private theorem predicate_fixed {n E P Q} (normal : PredicateWhnf P)
    (run : whnfPredicate n E P = .ok Q) : Q = P := by
  induction normal generalizing n Q with
  | app function notLam ih =>
      cases n with
      | zero => simp [whnfPredicate, exhausted, fail] at run
      | succ n =>
          simp only [whnfPredicate, CheckResult.bind_eq_ok] at run
          obtain ⟨R, hR, run⟩ := run
          have := ih hR
          subst R
          split at run
          next => exact False.elim (notLam _ _ rfl)
          next => simpa only [pure, Except.pure, Except.ok.injEq] using run.symm
  | _ => cases n <;> simp_all [whnfPredicate, exhausted, fail, pure, Except.pure]

private theorem predicate_exists {E P} (normal : PredicateWhnf P) :
    ∃ n, whnfPredicate n E P = .ok P := by
  induction normal with
  | app function notLam ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [whnfPredicate.eq_def]
      simp only [hn, bind, Except.bind]
      first
      | rfl
      | split
        next => exact False.elim (notLam _ _ rfl)
        next => rfl
  | _ => exact ⟨1, by simp [whnfPredicate, pure, Except.pure]⟩

/-- Successful weak-head term reduction returns weak-head syntax. -/
public theorem whnfTerm_normal {n E t u} (run : whnfTerm n E t = .ok u) : TermWhnf u :=
  term_shape run

/-- A successful reduction of an already weak-head term returns the same term. -/
public theorem whnfTerm_fixed {n E t u} (normal : TermWhnf t)
    (run : whnfTerm n E t = .ok u) : u = t := term_fixed normal run

/-- Every already weak-head term has a successful depth bound in every environment. -/
public theorem whnfTerm_complete {E t} (normal : TermWhnf t) :
    ∃ n, whnfTerm n E t = .ok t := term_exists normal

/-- Successful weak-head predicate reduction returns weak-head syntax. -/
public theorem whnfPredicate_normal {n E P Q} (run : whnfPredicate n E P = .ok Q) :
    PredicateWhnf Q := predicate_shape run

/-- A successful reduction of an already weak-head predicate returns the same predicate. -/
public theorem whnfPredicate_fixed {n E P Q} (normal : PredicateWhnf P)
    (run : whnfPredicate n E P = .ok Q) : Q = P := predicate_fixed normal run

/-- Every already weak-head predicate has a successful depth bound in every environment. -/
public theorem whnfPredicate_complete {E P} (normal : PredicateWhnf P) :
    ∃ n, whnfPredicate n E P = .ok P := predicate_exists normal

end LeanPRA.Core
