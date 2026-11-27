module

public import PRAProver.Metatheory.Core.Properties.Normalization.Shape
public import PRAProver.Metatheory.Core.Judgement.Instantiation

/-!
# Renaming successful reductions

The `*_rename` theorems commute successful reduction with renaming local variables at the same
depth, using environment validity so that global bodies are locally closed.
-/

namespace PRAProver.Core

open Theory

private theorem whnf_term {n E t u} (valid : EnvironmentWF E)
    (run : whnfTerm n E t = .ok u) (r : Renaming) :
    whnfTerm n E (t.rename r) = .ok (u.rename r) := by
  induction n generalizing t u r with
  | zero => simp [whnfTerm, exhausted, fail] at run
  | succ n ih =>
      cases t <;> simp only [whnfTerm] at run <;> simp only [Term.rename, whnfTerm]
      case definition name fs =>
        split at run
        next d lookup =>
          have body : TermTyping E { functions := d.functions } [] d.body d.arity := by
            cases (valid.lookup lookup).2 with | function body => exact body
          simpa only [body.instantiate_rename] using ih run r
        next => simp [referenceError, fail] at run; split at run <;> contradiction
      case letE a body => simpa only [Term.rename_subst0] using ih run r
      case app f a =>
        simp only [CheckResult.bind_eq_ok] at run ⊢
        obtain ⟨g, hg, run⟩ := run
        refine ⟨g.rename r, ih hg r, ?_⟩
        cases g with
        | lam body => simpa only [Term.rename, Term.rename_subst0] using ih run r
        | primrec b s =>
            simp only [Term.rename, CheckResult.bind_eq_ok] at run ⊢
            obtain ⟨m, hm, run⟩ := run
            refine ⟨m.rename r, ih hm r, ?_⟩
            cases m with
            | zero => simpa only [Term.rename] using ih run r
            | app f p =>
                cases f with
                | succ => simpa only [Term.rename] using ih run r
                | _ =>
                    simp only [pure, Except.pure, Except.ok.injEq] at run
                    subst u
                    simp only [Term.rename, pure, Except.pure]
            | _ =>
                simp only [pure, Except.pure, Except.ok.injEq] at run
                subst u
                simp only [Term.rename, pure, Except.pure]
        | _ =>
            simp only [pure, Except.pure, Except.ok.injEq] at run
            subst u
            simp only [Term.rename, pure, Except.pure]
      all_goals
        simp only [pure, Except.pure, Except.ok.injEq] at run
        subst u
        simp only [Term.rename, pure, Except.pure]

private theorem term_rename (n : Nat) (E : Environment) (valid : EnvironmentWF E) :
    (∀ {k t u}, reduceTerm n E k t = .ok u → ∀ r,
      reduceTerm n E k (t.rename r) = .ok (u.rename r)) ∧
    (∀ {t u}, reduceTermNeutral n E t = .ok u → ∀ r,
      reduceTermNeutral n E (t.rename r) = .ok (u.rename r)) := by
  induction n with
  | zero =>
      constructor <;> intros <;> simp_all [reduceTerm, reduceTermNeutral, exhausted, fail]
  | succ n ih =>
      constructor
      · intro k t u run r
        cases k with
        | succ k =>
            simp only [reduceTerm, CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq] at run ⊢
            obtain ⟨body, hb, rfl⟩ := run
            refine ⟨body.rename (Renaming.lift 1 r), ?_, by simp only [Term.rename]⟩
            simpa only [Term.rename, Term.rename_shift,
              Renaming.lift, Nat.zero_lt_one, ↓reduceIte] using ih.1 hb (Renaming.lift 1 r)
        | zero =>
            simp only [reduceTerm, CheckResult.bind_eq_ok] at run ⊢
            obtain ⟨w, hw, run⟩ := run
            refine ⟨w.rename r, whnf_term valid hw r, ?_⟩
            cases w <;> simp only [pure, Except.pure,
              Except.ok.injEq, fail] at run <;> try contradiction
            case app f a =>
              cases f <;> simp only [CheckResult.bind_eq_ok,
                Except.ok.injEq] at run
              case primrec base step =>
                obtain ⟨b, hb, s, hs, a', ha, rfl⟩ := run
                simp only [Term.rename, CheckResult.bind_eq_ok]
                exact ⟨b.rename r, ih.1 hb r, s.rename r, ih.1 hs r,
                  a'.rename r, ih.1 ha r, rfl⟩
              all_goals
                obtain ⟨g, hg, b, hb, rfl⟩ := run
                simp only [Term.rename, CheckResult.bind_eq_ok]
                exact ⟨g.rename r, by simpa only [Term.rename] using ih.2 hg r,
                  b.rename r, ih.1 hb r, rfl⟩
            all_goals subst u; simp only [Term.rename, pure, Except.pure]
      · intro t u run r
        simp only [reduceTermNeutral, CheckResult.bind_eq_ok] at run ⊢
        obtain ⟨w, hw, run⟩ := run
        refine ⟨w.rename r, whnf_term valid hw r, ?_⟩
        cases w <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
          Except.ok.injEq, fail] at run <;> try contradiction
        case app f a =>
          obtain ⟨g, hg, b, hb, rfl⟩ := run
          simp only [Term.rename, CheckResult.bind_eq_ok]
          exact ⟨g.rename r, ih.2 hg r, b.rename r, ih.1 hb r, rfl⟩
        all_goals subst u; simp only [Term.rename, pure, Except.pure]

private theorem whnf_predicate {n E P Q} (valid : EnvironmentWF E)
    (run : whnfPredicate n E P = .ok Q) (r : Renaming) :
    whnfPredicate n E (P.rename r) = .ok (Q.rename r) := by
  induction n generalizing P Q r with
  | zero => simp [whnfPredicate, exhausted, fail] at run
  | succ n ih =>
      cases P <;> simp only [whnfPredicate] at run <;>
        simp only [Predicate.rename, whnfPredicate]
      case definition name fs ps =>
        split at run
        next d lookup =>
          have body := (valid.lookup lookup).2
          cases body with
          | predicate body => simpa only [body.instantiate_rename] using ih run r
        next => simp [referenceError, fail] at run; split at run <;> contradiction
      case app P a =>
        simp only [CheckResult.bind_eq_ok] at run ⊢
        obtain ⟨R, hR, run⟩ := run
        refine ⟨R.rename r, ih hR r, ?_⟩
        cases R with
        | lam body => simpa only [Predicate.rename, Predicate.rename_subst0] using ih run r
        | _ =>
            simp only [pure, Except.pure, Except.ok.injEq] at run
            subst Q
            simp only [Predicate.rename, pure, Except.pure]
      case letTerm => exact ih run r
      case letPredicate => exact ih run r
      all_goals
        simp only [pure, Except.pure, Except.ok.injEq] at run
        subst Q
        simp only [Predicate.rename, pure, Except.pure]

private theorem predicate_rename (n : Nat) (E : Environment) (valid : EnvironmentWF E) :
    (∀ {k P Q}, reducePredicate n E k P = .ok Q → ∀ r,
      reducePredicate n E k (P.rename r) = .ok (Q.rename r)) ∧
    (∀ {P Q}, reducePredicateNeutral n E P = .ok Q → ∀ r,
      reducePredicateNeutral n E (P.rename r) = .ok (Q.rename r)) := by
  induction n with
  | zero =>
      constructor <;> intros <;>
        simp_all [reducePredicate, reducePredicateNeutral, exhausted, fail]
  | succ n ih =>
      constructor
      · intro k P Q run r
        cases k with
        | succ k =>
            simp only [reducePredicate, CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq] at run ⊢
            obtain ⟨body, hb, rfl⟩ := run
            refine ⟨body.rename (Renaming.lift 1 r), ?_, by simp only [Predicate.rename]⟩
            simpa only [Predicate.rename, Predicate.rename_shift, Term.rename,
              Renaming.lift, Nat.zero_lt_one, ↓reduceIte] using ih.1 hb (Renaming.lift 1 r)
        | zero =>
            simp only [reducePredicate, CheckResult.bind_eq_ok] at run ⊢
            obtain ⟨R, hR, run⟩ := run
            refine ⟨R.rename r, whnf_predicate valid hR r, ?_⟩
            cases R <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq, fail] at run <;> try contradiction
            case equal a b =>
              obtain ⟨c, hc, d, hd, rfl⟩ := run
              simp only [Predicate.rename, CheckResult.bind_eq_ok]
              exact ⟨c.rename r, (term_rename n E valid).1 hc r,
                d.rename r, (term_rename n E valid).1 hd r, rfl⟩
            case imp A B =>
              obtain ⟨C, hC, D, hD, rfl⟩ := run
              simp only [Predicate.rename, CheckResult.bind_eq_ok]
              exact ⟨C.rename r, ih.1 hC r, D.rename r, ih.1 hD r, rfl⟩
            case and A B =>
              obtain ⟨C, hC, D, hD, rfl⟩ := run
              simp only [Predicate.rename, CheckResult.bind_eq_ok]
              exact ⟨C.rename r, ih.1 hC r, D.rename r, ih.1 hD r, rfl⟩
            case or A B =>
              obtain ⟨C, hC, D, hD, rfl⟩ := run
              simp only [Predicate.rename, CheckResult.bind_eq_ok]
              exact ⟨C.rename r, ih.1 hC r, D.rename r, ih.1 hD r, rfl⟩
            case all P =>
              obtain ⟨R, hR, rfl⟩ := run
              simp only [Predicate.rename, CheckResult.bind_eq_ok]
              exact ⟨R.rename r, ih.1 hR r, rfl⟩
            case ex P =>
              obtain ⟨R, hR, rfl⟩ := run
              simp only [Predicate.rename, CheckResult.bind_eq_ok]
              exact ⟨R.rename r, ih.1 hR r, rfl⟩
            case app P a =>
              obtain ⟨R, hR, b, hb, rfl⟩ := run
              simp only [Predicate.rename, CheckResult.bind_eq_ok]
              exact ⟨R.rename r, ih.2 hR r, b.rename r, (term_rename n E valid).1 hb r, rfl⟩
            all_goals subst Q; simp only [Predicate.rename, pure, Except.pure]
      · intro P Q run r
        simp only [reducePredicateNeutral, CheckResult.bind_eq_ok] at run ⊢
        obtain ⟨R, hR, run⟩ := run
        refine ⟨R.rename r, whnf_predicate valid hR r, ?_⟩
        cases R <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
          Except.ok.injEq, fail] at run <;> try contradiction
        case app P a =>
          obtain ⟨R, hR, b, hb, rfl⟩ := run
          simp only [Predicate.rename, CheckResult.bind_eq_ok]
          exact ⟨R.rename r, ih.2 hR r, b.rename r, (term_rename n E valid).1 hb r, rfl⟩
        all_goals subst Q; simp only [Predicate.rename, pure, Except.pure]

/-- Weak-head predicate reduction commutes with local renaming at the same depth. -/
public theorem whnfPredicate_rename {n E P Q} (valid : EnvironmentWF E)
    (run : whnfPredicate n E P = .ok Q) (r : Renaming) :
    whnfPredicate n E (P.rename r) = .ok (Q.rename r) := whnf_predicate valid run r

/-- Full predicate reduction commutes with local renaming, including numerical eta expansion. -/
public theorem reducePredicate_rename {n E k P Q} (valid : EnvironmentWF E)
    (run : reducePredicate n E k P = .ok Q) (r : Renaming) :
    reducePredicate n E k (P.rename r) = .ok (Q.rename r) := (predicate_rename n E valid).1 run r

/-- Neutral predicate reduction commutes with local renaming. -/
public theorem reducePredicateNeutral_rename {n E P Q} (valid : EnvironmentWF E)
    (run : reducePredicateNeutral n E P = .ok Q) (r : Renaming) :
    reducePredicateNeutral n E (P.rename r) = .ok (Q.rename r) :=
  (predicate_rename n E valid).2 run r

/-- Weak-head term reduction commutes with every local renaming at the same depth. -/
public theorem whnfTerm_rename {n E t u} (valid : EnvironmentWF E)
    (run : whnfTerm n E t = .ok u) (r : Renaming) :
    whnfTerm n E (t.rename r) = .ok (u.rename r) := whnf_term valid run r

/-- Full term reduction commutes with renaming, including numerical eta expansion. -/
public theorem reduceTerm_rename {n E k t u} (valid : EnvironmentWF E)
    (run : reduceTerm n E k t = .ok u) (r : Renaming) :
    reduceTerm n E k (t.rename r) = .ok (u.rename r) := (term_rename n E valid).1 run r

/-- Neutral term reduction commutes with every local renaming. -/
public theorem reduceTermNeutral_rename {n E t u} (valid : EnvironmentWF E)
    (run : reduceTermNeutral n E t = .ok u) (r : Renaming) :
    reduceTermNeutral n E (t.rename r) = .ok (u.rename r) := (term_rename n E valid).2 run r

end PRAProver.Core
