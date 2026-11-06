module

public import LeanPRA.Metatheory.Core.Checker.Results
public import LeanPRA.Metatheory.Core.Judgement.Formation

/-!
# Soundness of numerical and predicate reduction

- `whnfTerm_sound` and `whnfPredicate_sound` justify successful weak-head reduction.
- `reduceTerm_sound` and `reducePredicate_sound` justify full normalization with eta expansion.
- `reduceTermNeutral_sound` and `reducePredicateNeutral_sound` cover neutral application chains.
- `reduceFormula_sound` specializes predicate normalization to formulas.

All results assume a valid global environment and a declaratively typed input. Successful
reduction gives typed definitional equality at the input arity or full predicate signature.
-/

namespace LeanPRA.Core

open Theory

private theorem term_whnf_correct {n E Ξ Γ t u k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) (run : whnfTerm n E t = .ok u) :
    TermEq E Ξ Γ t u k := by
  induction n generalizing Ξ Γ t u k with
  | zero => simp [whnfTerm, exhausted, fail] at run
  | succ n ih =>
      cases t with
      | definition name fs =>
          obtain ⟨d, lookup, actuals, rfl⟩ := typed.inv_definition
          simp only [whnfTerm, Environment.lookup, lookup] at run
          have body : TermTyping E { functions := d.functions } [] d.body d.arity := by
            have wf := (valid.lookup lookup).2
            cases wf with | function body => exact body
          have instantiated := body.instantiate actuals
          simp only [List.nil_append, List.length_nil] at instantiated
          exact .trans (.delta lookup actuals instantiated) (ih instantiated run)
      | letE value body =>
          obtain ⟨j, hv, hb⟩ := typed.inv_let
          simp only [whnfTerm] at run
          exact .trans (.zeta hv hb) (ih (hb.subst0 hv) run)
      | app f a =>
          obtain ⟨hf, ha⟩ := typed.inv_app
          simp only [whnfTerm, CheckResult.bind_eq_ok] at run
          obtain ⟨g, hg, run⟩ := run
          have eqf := ih hf hg
          have tg := eqf.regularity.2
          have congr := TermEq.app eqf (.refl ha)
          cases g with
          | lam body =>
              obtain ⟨j, hj, hb⟩ := tg.inv_lam
              have : k = j := Nat.succ.inj hj
              subst j
              exact .trans congr (.trans (.beta hb ha) (ih (hb.subst0 ha) run))
          | _ =>
              simp only [pure, Except.pure, Except.ok.injEq] at run
              subst u
              exact congr
      | primrec b s a =>
          obtain ⟨rfl, hb, hs, ha⟩ := typed.inv_primrec
          simp only [whnfTerm, CheckResult.bind_eq_ok] at run
          obtain ⟨m, hm, run⟩ := run
          have eqa := ih ha hm
          have tm := eqa.regularity.2
          have congr := TermEq.primrec (.refl hb) (.refl hs) eqa
          cases m with
          | zero => exact .trans congr (.trans (.primrecZero hb hs) (ih hb run))
          | app f p =>
              cases f with
              | succ =>
                  have hp := tm.inv_app.2
                  exact .trans congr (.trans (.primrecSucc hb hs hp)
                    (ih (.app (.app hs hp) (.primrec hb hs hp)) run))
              | _ =>
                  simp only [pure, Except.pure, Except.ok.injEq] at run
                  subst u
                  exact congr
          | _ =>
              simp only [pure, Except.pure, Except.ok.injEq] at run
              subst u
              exact congr
      | _ =>
          simp only [whnfTerm, pure, Except.pure, Except.ok.injEq] at run
          subst u
          exact .refl typed

private theorem term_reduce_correct (n : Nat) (E : Environment) (valid : EnvironmentWF E) :
    (∀ {Ξ Γ t u k}, TermTyping E Ξ Γ t k → reduceTerm n E k t = .ok u →
      TermEq E Ξ Γ t u k) ∧
    (∀ {Ξ Γ t u k}, TermTyping E Ξ Γ t k → reduceTermNeutral n E t = .ok u →
      TermEq E Ξ Γ t u k) := by
  induction n with
  | zero =>
      constructor <;> intro Ξ Γ t u k typed run <;>
        simp [reduceTerm, reduceTermNeutral, exhausted, fail] at run
  | succ n ih =>
      constructor
      · intro Ξ Γ t u k typed run
        cases k with
        | succ k =>
            simp only [reduceTerm, CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq] at run
            obtain ⟨body, hb, rfl⟩ := run
            exact .trans (.symm (.eta (binderName := .anonymous) typed))
              (.lam (ih.1 (.app (typed.shift 0) (.bvar rfl)) hb))
        | zero =>
            simp only [reduceTerm, CheckResult.bind_eq_ok] at run
            obtain ⟨m, hm, run⟩ := run
            have eqm := term_whnf_correct valid typed hm
            have tm := eqm.regularity.2
            cases m <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq, fail] at run <;> try contradiction
            case bvar i => subst u; exact eqm
            case parameter i => subst u; exact eqm
            case zero => subst u; exact eqm
            case app f a =>
              obtain ⟨g, hg, b, hb, rfl⟩ := run
              exact .trans eqm (.app (ih.2 tm.inv_app.1 hg) (ih.1 tm.inv_app.2 hb))
            case primrec b s a =>
              obtain ⟨c, hc, v, hv, m, hm, rfl⟩ := run
              obtain ⟨_, hb, hs, ha⟩ := tm.inv_primrec
              exact .trans eqm (.primrec (ih.1 hb hc) (ih.1 hs hv) (ih.1 ha hm))
      · intro Ξ Γ t u k typed run
        simp only [reduceTermNeutral, CheckResult.bind_eq_ok] at run
        obtain ⟨m, hm, run⟩ := run
        have eqm := term_whnf_correct valid typed hm
        have tm := eqm.regularity.2
        cases m <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
          Except.ok.injEq, fail] at run <;> try contradiction
        case bvar i => subst u; exact eqm
        case parameter i => subst u; exact eqm
        case succ => subst u; exact eqm
        case app f a =>
          obtain ⟨g, hg, b, hb, rfl⟩ := run
          exact .trans eqm (.app (ih.2 tm.inv_app.1 hg) (ih.1 tm.inv_app.2 hb))

/-- Successful weak-head reduction gives typed equality at the input numerical arity. -/
public theorem whnfTerm_sound {n E Ξ Γ t u k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) (run : whnfTerm n E t = .ok u) :
    TermEq E Ξ Γ t u k := term_whnf_correct valid typed run

/-- Successful full normalization gives typed equality, including at function arities. -/
public theorem reduceTerm_sound {n E Ξ Γ t u k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) (run : reduceTerm n E k t = .ok u) :
    TermEq E Ξ Γ t u k := (term_reduce_correct n E valid).1 typed run

/-- Successful neutral normalization gives typed equality at the unchanged input arity. -/
public theorem reduceTermNeutral_sound {n E Ξ Γ t u k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) (run : reduceTermNeutral n E t = .ok u) :
    TermEq E Ξ Γ t u k := (term_reduce_correct n E valid).2 typed run

end LeanPRA.Core

namespace LeanPRA.Core

open Theory

private theorem predicate_whnf_correct {n E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) (run : whnfPredicate n E P = .ok Q) :
    PredicateEq E Ξ Γ P Q σ := by
  induction n generalizing Ξ Γ P Q σ with
  | zero => simp [whnfPredicate, exhausted, fail] at run
  | succ n ih =>
      cases P with
      | definition name fs ps =>
          obtain ⟨d, lookup, functions, predicates, sub⟩ := typed.inv_definition
          have body := (valid.predicate_instance lookup functions predicates).subsumption sub
          simp only [whnfPredicate, Environment.lookup, lookup] at run
          exact .trans (.delta lookup functions predicates body sub) (ih body run)
      | letTerm a P =>
          obtain ⟨⟨j, value⟩, body⟩ := typed.inv_letTerm
          exact .trans (.zetaTerm value body) (ih body run)
      | letPredicate R P =>
          obtain ⟨⟨τ, value⟩, body⟩ := typed.inv_letPredicate
          exact .trans (.zetaPredicate value body) (ih body run)
      | app f a =>
          obtain ⟨k, s, hf, ha, sub⟩ := typed.inv_app
          simp only [whnfPredicate, CheckResult.bind_eq_ok] at run
          obtain ⟨g, hg, run⟩ := run
          have eqf := ih hf hg
          have tg := (eqf.regularity valid).2
          have congr := PredicateEq.app eqf (.refl ha)
          refine PredicateEq.subsumption (τ := σ) ?_ sub
          cases g with
          | lam body =>
              have hb := tg.lam_body
              exact .trans congr (.trans (.beta hb ha) (ih (hb.subst0 valid ha) run))
          | _ =>
              simp only [pure, Except.pure, Except.ok.injEq] at run
              subst Q
              exact congr
      | _ =>
          simp only [whnfPredicate, pure, Except.pure, Except.ok.injEq] at run
          subst Q
          exact .refl typed

private theorem predicate_reduce_correct (n : Nat) (E : Environment) (valid : EnvironmentWF E) :
    (∀ {Ξ Γ P Q k s}, PredicateTyping E Ξ Γ P ⟨k, s⟩ →
      reducePredicate n E k P = .ok Q → PredicateEq E Ξ Γ P Q ⟨k, s⟩) ∧
    (∀ {Ξ Γ P Q σ}, PredicateTyping E Ξ Γ P σ →
      reducePredicateNeutral n E P = .ok Q → PredicateEq E Ξ Γ P Q σ) := by
  induction n with
  | zero =>
      constructor <;> intros <;>
        simp_all [reducePredicate, reducePredicateNeutral, exhausted, fail]
  | succ n ih =>
      constructor
      · intro Ξ Γ P Q k s typed run
        cases k with
        | succ k =>
            simp only [reducePredicate, CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq] at run
            obtain ⟨body, hb, rfl⟩ := run
            exact .trans (.symm (.eta (binderName := .anonymous) typed))
              (.lam (ih.1 (.app (typed.shift valid 0) (.bvar rfl)) hb))
        | zero =>
            simp only [reducePredicate, CheckResult.bind_eq_ok] at run
            obtain ⟨R, hR, run⟩ := run
            have eqR := predicate_whnf_correct valid typed hR
            have tR := (eqR.regularity valid).2
            cases R <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq, fail] at run <;> try contradiction
            case false => subst Q; exact eqR
            case true => subst Q; exact eqR
            case parameter i => subst Q; exact eqR
            case equal a b =>
              obtain ⟨c, hc, d, hd, rfl⟩ := run
              obtain ⟨ta, tb, sub⟩ := tR.inv_equal
              exact .trans eqR (.subsumption
                (.equal (reduceTerm_sound valid ta hc) (reduceTerm_sound valid tb hd)) sub)
            case imp A B =>
              obtain ⟨C, hC, D, hD, rfl⟩ := run
              obtain ⟨r, ta, tb, sub⟩ := tR.inv_imp
              exact .trans eqR (.imp (ih.1 (.subsumption ta sub) hC)
                (ih.1 (.subsumption tb sub) hD))
            case and A B =>
              obtain ⟨C, hC, D, hD, rfl⟩ := run
              obtain ⟨r, ta, tb, sub⟩ := tR.inv_and
              exact .trans eqR (.and (ih.1 (.subsumption ta sub) hC)
                (ih.1 (.subsumption tb sub) hD))
            case or A B =>
              obtain ⟨C, hC, D, hD, rfl⟩ := run
              obtain ⟨r, ta, tb, sub⟩ := tR.inv_or
              exact .trans eqR (.or (ih.1 (.subsumption ta sub) hC)
                (ih.1 (.subsumption tb sub) hD))
            case all A =>
              obtain ⟨B, hB, rfl⟩ := run
              obtain ⟨hs, ta⟩ := tR.inv_all
              have : s = .prop := congrArg PredicateSignature.sort hs
              subst s
              exact .trans eqR (.all (ih.1 ta hB))
            case ex A =>
              obtain ⟨B, hB, rfl⟩ := run
              obtain ⟨hs, ta⟩ := tR.inv_ex
              have : s = .prop := congrArg PredicateSignature.sort hs
              subst s
              exact .trans eqR (.ex (ih.1 ta hB))
            case app f a =>
              obtain ⟨g, hg, b, hb, rfl⟩ := run
              obtain ⟨tf, ta⟩ := tR.app_function
              exact .trans eqR (.app (ih.2 tf hg) (reduceTerm_sound valid ta hb))
      · intro Ξ Γ P Q σ typed run
        simp only [reducePredicateNeutral, CheckResult.bind_eq_ok] at run
        obtain ⟨R, hR, run⟩ := run
        have eqR := predicate_whnf_correct valid typed hR
        have tR := (eqR.regularity valid).2
        cases R <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
          Except.ok.injEq, fail] at run <;> try contradiction
        case parameter i => subst Q; exact eqR
        case app f a =>
          obtain ⟨g, hg, b, hb, rfl⟩ := run
          obtain ⟨k, s, tf, ta, sub⟩ := tR.inv_app
          exact .trans eqR (.subsumption
            (.app (ih.2 tf hg) (reduceTerm_sound valid ta hb)) sub)

/-- Successful weak-head predicate reduction gives equality at the input's full signature. -/
public theorem whnfPredicate_sound {n E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) (run : whnfPredicate n E P = .ok Q) :
    PredicateEq E Ξ Γ P Q σ := predicate_whnf_correct valid typed run

/-- Successful full predicate reduction preserves the exact input signature. -/
public theorem reducePredicate_sound {n E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) (run : reducePredicate n E σ.arity P = .ok Q) :
    PredicateEq E Ξ Γ P Q σ := (predicate_reduce_correct n E valid).1 typed run

/-- Neutral predicate normalization preserves typed equality at the exact input signature. -/
public theorem reducePredicateNeutral_sound {n E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) (run : reducePredicateNeutral n E P = .ok Q) :
    PredicateEq E Ξ Γ P Q σ := (predicate_reduce_correct n E valid).2 typed run

/-- Formula normalization is sound at either of the two formula sorts. -/
public theorem reduceFormula_sound {n E Ξ Γ P Q s} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P ⟨0, s⟩) (run : reduceFormula n E P = .ok Q) :
    PredicateEq E Ξ Γ P Q ⟨0, s⟩ := reducePredicate_sound valid typed run

end LeanPRA.Core
