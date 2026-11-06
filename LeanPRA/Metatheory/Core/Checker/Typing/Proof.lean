module

public import LeanPRA.Metatheory.Core.Checker.Conversion
public import LeanPRA.Metatheory.Core.Checker.Typing.Predicate
import LeanPRA.Metatheory.Core.Properties.Normalization.Soundness

/-!
# Soundness of proof-type synthesis and checking

- `inferProof_sound` reconstructs a declarative derivation for accepted proof data.
- `checkProof_sound` derives the supplied, well-formed expected formula.

The environment and proof assumptions must be valid. Proof checking also assumes a well-formed
expected formula. All primitive proof constructors, conversion, and the QF restriction on
induction are covered.
-/

namespace LeanPRA.Core

open Theory

private theorem proof_correct (n : Nat) (E : Environment) (valid : EnvironmentWF E) :
    (∀ {c : Context} {p A}, ContextWF E c.parameters c.locals c.proofs →
      inferProof n E c p = .ok A → ProofTyping E c.parameters c.locals c.proofs p A) ∧
    (∀ {c : Context} {p A}, ContextWF E c.parameters c.locals c.proofs →
      PredicateTyping E c.parameters c.locals A ⟨0, .prop⟩ →
      checkProof n E c p A = .ok () → ProofTyping E c.parameters c.locals c.proofs p A) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩ <;> intros <;>
        simp_all [inferProof, checkProof, exhausted, fail]
  | succ n ih =>
      refine ⟨?_, ?_⟩
      · intro c p A ctx run
        cases p <;> simp only [inferProof, CheckResult.withSite_eq_ok] at run
        case trueIntro =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst A
          exact .trueIntro
        case hyp i =>
          split at run
          next B lookup =>
            simp only [pure, Except.pure, Except.ok.injEq] at run
            subst A
            exact .hyp lookup
          next => simp [fail] at run
        case theoremE name fs ps =>
          split at run
          next d lookup =>
            simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
            obtain ⟨⟨⟩, hf, ⟨⟩, hp, rfl⟩ := run
            exact .theoremE lookup (checkFunctionArguments_sound hf)
              (checkPredicateArguments_sound hp)
          next =>
            simp [referenceError, fail] at run
            split at run <;> contradiction
        case impIntro B p =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨s, hB, C, hp, rfl⟩ := run
          have tB := (inferFormula_sound hB).toProp
          exact .impIntro tB (ih.1 (ctx.pushProof tB) hp)
        case impElim p q =>
          simp only [CheckResult.bind_eq_ok] at run
          obtain ⟨C, hp, B, hw, run⟩ := run
          have tp := ih.1 ctx hp
          have tp := ProofTyping.conversion tp
            (whnfPredicate_sound valid (tp.regularity valid ctx) hw)
          cases B <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
            Except.ok.injEq, fail] at run <;> try contradiction
          case imp B C =>
            obtain ⟨⟨⟩, hq, rfl⟩ := run
            obtain ⟨s, tB, tC, sub⟩ := (tp.regularity valid ctx).inv_imp
            exact .impElim tp (ih.2 ctx (.subsumption tB sub) hq)
        case andIntro p q =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨B, hp, C, hq, rfl⟩ := run
          exact .andIntro (ih.1 ctx hp) (ih.1 ctx hq)
        case andLeft p =>
          simp only [CheckResult.bind_eq_ok] at run
          obtain ⟨C, hp, B, hw, run⟩ := run
          have tp := ih.1 ctx hp
          have tp := ProofTyping.conversion tp
            (whnfPredicate_sound valid (tp.regularity valid ctx) hw)
          cases B <;> simp only [pure, Except.pure, Except.ok.injEq, fail] at run <;>
            try contradiction
          case and B C => subst A; exact .andLeft tp
        case andRight p =>
          simp only [CheckResult.bind_eq_ok] at run
          obtain ⟨C, hp, B, hw, run⟩ := run
          have tp := ih.1 ctx hp
          have tp := ProofTyping.conversion tp
            (whnfPredicate_sound valid (tp.regularity valid ctx) hw)
          cases B <;> simp only [pure, Except.pure, Except.ok.injEq, fail] at run <;>
            try contradiction
          case and B C => subst A; exact .andRight tp
        case orLeft B p =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨s, hB, C, hp, rfl⟩ := run
          exact .orLeft (inferFormula_sound hB).toProp (ih.1 ctx hp)
        case orRight B p =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨s, hB, C, hp, rfl⟩ := run
          exact .orRight (inferFormula_sound hB).toProp (ih.1 ctx hp)
        case orElim target p q r =>
          simp only [CheckResult.bind_eq_ok] at run
          obtain ⟨s, ht, C, hp, B, hw, run⟩ := run
          have tt := (inferFormula_sound ht).toProp
          have tp := ih.1 ctx hp
          have tp := ProofTyping.conversion tp
            (whnfPredicate_sound valid (tp.regularity valid ctx) hw)
          cases B <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
            Except.ok.injEq, fail] at run <;> try contradiction
          case or B C =>
            obtain ⟨⟨⟩, hq, ⟨⟩, hr, rfl⟩ := run
            obtain ⟨s, tB, tC, sub⟩ := (tp.regularity valid ctx).inv_or
            exact .orElim tt tp (ih.2 (ctx.pushProof (.subsumption tB sub)) tt hq)
              (ih.2 (ctx.pushProof (.subsumption tC sub)) tt hr)
        case falseElim target p =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨s, ht, ⟨⟩, hp, rfl⟩ := run
          exact .falseElim (inferFormula_sound ht).toProp
            (ih.2 ctx (.subsumption .false .lift) hp)
        case forallIntro motive p =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨⟨⟩, ht, ⟨⟩, hp, rfl⟩ := run
          have tm := checkMotive_sound ht
          exact .forallIntro tm (ih.2 (ctx.pushLocal valid 0)
            (.app (tm.shift valid 0) (.bvar rfl)) hp)
        case forallElim p a =>
          simp only [CheckResult.bind_eq_ok] at run
          obtain ⟨⟨⟩, ha, C, hp, B, hw, run⟩ := run
          have tp := ih.1 ctx hp
          have tp := ProofTyping.conversion tp
            (whnfPredicate_sound valid (tp.regularity valid ctx) hw)
          cases B <;> simp only [pure, Except.pure, Except.ok.injEq, fail] at run <;>
            try contradiction
          case all motive =>
            subst A
            exact .forallElim tp (checkTerm_sound ha)
        case existsIntro motive witness p =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨⟨⟩, ht, ⟨⟩, hw, ⟨⟩, hp, rfl⟩ := run
          have tm := checkMotive_sound ht
          have tw := checkTerm_sound hw
          exact .existsIntro tm tw (ih.2 ctx (.app tm tw) hp)
        case existsElim target p q =>
          simp only [CheckResult.bind_eq_ok] at run
          obtain ⟨s, ht, C, hp, B, hw, run⟩ := run
          have tt := (inferFormula_sound ht).toProp
          have tp := ih.1 ctx hp
          have tp := ProofTyping.conversion tp
            (whnfPredicate_sound valid (tp.regularity valid ctx) hw)
          cases B <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
            Except.ok.injEq, fail] at run <;> try contradiction
          case ex motive =>
            obtain ⟨⟨⟩, hq, rfl⟩ := run
            have tm := (tp.regularity valid ctx).inv_ex.2
            exact .existsElim tt tp
              (ih.2 ((ctx.pushLocal valid 0).pushProof
                (.app (tm.shift valid 0) (.bvar rfl))) (tt.shift valid 0) hq)
        case letE type value body =>
          simp only [CheckResult.bind_eq_ok] at run
          obtain ⟨s, ht, ⟨⟩, hv, hb⟩ := run
          have tt := (inferFormula_sound ht).toProp
          exact .letE tt (ih.2 ctx tt hv) (ih.1 (ctx.pushProof tt) hb)
        case letTerm value body =>
          simp only [CheckResult.bind_eq_ok] at run
          obtain ⟨j, hv, hb⟩ := run
          exact .letTerm (inferTerm_sound hv) (ih.1 ctx hb)
        case letPredicate value body =>
          simp only [CheckResult.bind_eq_ok] at run
          obtain ⟨σ, hv, hb⟩ := run
          exact .letPredicate (inferPredicate_sound hv) (ih.1 ctx hb)
        case ascribe type p =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨s, ht, ⟨⟩, hp, rfl⟩ := run
          have tt := (inferFormula_sound ht).toProp
          exact .ascribe tt (ih.2 ctx tt hp)
        case eqRefl t =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨⟨⟩, ht, rfl⟩ := run
          exact .eqRefl (checkTerm_sound ht)
        case eqSubst motive equality p =>
          simp only [CheckResult.bind_eq_ok] at run
          obtain ⟨⟨⟩, ht, C, he, B, hw, ⟨a, b⟩, hs, ⟨⟩, hp, run⟩ := run
          have te := ih.1 ctx he
          have te := ProofTyping.conversion te
            (whnfPredicate_sound valid (te.regularity valid ctx) hw)
          have hb := equalitySides_sound hs
          subst B
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst A
          have tm := checkMotive_sound ht
          have ta := (te.regularity valid ctx).inv_equal.1
          exact .eqSubst tm te (ih.2 ctx (.app tm ta) hp)
        case succNeZero t =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨⟨⟩, ht, rfl⟩ := run
          exact .succNeZero (checkTerm_sound ht)
        case succInj p =>
          simp only [CheckResult.bind_eq_ok] at run
          obtain ⟨C, hp, B, hw, ⟨a, b⟩, hs, a', ha, b', hb, run⟩ := run
          have tp := ih.1 ctx hp
          have tp := ProofTyping.conversion tp
            (whnfPredicate_sound valid (tp.regularity valid ctx) hw)
          have heq := equalitySides_sound hs
          subst B
          obtain ⟨ta, tb, _⟩ := (tp.regularity valid ctx).inv_equal
          have ea := whnfTerm_sound valid ta ha
          have eb := whnfTerm_sound valid tb hb
          split at run
          next left right =>
            simp only [pure, Except.pure, Except.ok.injEq] at run
            subst A
            exact .succInj (.conversion tp (.subsumption (.equal ea eb) .lift))
          next => simp [fail] at run
        case lem P =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨s, hP, rfl⟩ := run
          exact .lem (inferFormula_sound hP).toProp
        case induction motive base step argument =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨⟨⟩, ht, ⟨⟩, ha, ⟨⟩, hb, ⟨⟩, hs, rfl⟩ := run
          have tm := checkMotive_sound ht
          exact .induction tm (ih.2 ctx (PredicateTyping.app tm .zero).toProp hb)
            (ih.2 ((ctx.pushLocal valid 0).pushProof
              (PredicateTyping.app (tm.shift valid 0) (.bvar rfl)).toProp)
              (PredicateTyping.app (tm.shift valid 0) (.app .succ (.bvar rfl))).toProp hs)
            (checkTerm_sound ha)
      · intro c p A ctx type run
        simp only [checkProof, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok] at run
        obtain ⟨B, hp, equal, hequal, run⟩ := run
        have tp := ih.1 ctx hp
        cases equal with
        | false => simp [fail] at run
        | true =>
          exact .conversion tp (defEqPredicate_sound valid (tp.regularity valid ctx) type hequal)

/-- Successful proof inference establishes the inferred declarative conclusion. -/
public theorem inferProof_sound {n E} {c : Context} {p A} (valid : EnvironmentWF E)
    (ctx : ContextWF E c.parameters c.locals c.proofs) (run : inferProof n E c p = .ok A) :
    ProofTyping E c.parameters c.locals c.proofs p A := (proof_correct n E valid).1 ctx run

/-- Successful proof checking derives a previously formed expected formula. -/
public theorem checkProof_sound {n E} {c : Context} {p A} (valid : EnvironmentWF E)
    (ctx : ContextWF E c.parameters c.locals c.proofs)
    (type : PredicateTyping E c.parameters c.locals A ⟨0, .prop⟩)
    (run : checkProof n E c p A = .ok ()) : ProofTyping E c.parameters c.locals c.proofs p A :=
  (proof_correct n E valid).2 ctx type run

end LeanPRA.Core
