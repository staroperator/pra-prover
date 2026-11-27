module

public import PRAProver.Metatheory.Core.Checker.Conversion
public import PRAProver.Metatheory.Core.Checker.Typing.Predicate
import PRAProver.Metatheory.Core.Properties.Normalization.Soundness

/-!
# Soundness of proof-type synthesis and checking

- `inferProof_sound` reconstructs a declarative derivation for accepted proof data.
- `checkProof_sound` derives the supplied, well-formed expected formula.

The environment and proof assumptions must be valid. Proof checking also assumes a well-formed
expected formula. All primitive proof constructors, conversion, and the QF restriction on
induction are covered.
-/

namespace PRAProver.Core

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
        case andLeft a b =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨sa, ha, sb, hb, rfl⟩ := run
          exact .andLeft (inferFormula_sound ha).toProp (inferFormula_sound hb).toProp
        case andRight a b =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨sa, ha, sb, hb, rfl⟩ := run
          exact .andRight (inferFormula_sound ha).toProp (inferFormula_sound hb).toProp
        case orLeft a b =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨sa, ha, sb, hb, rfl⟩ := run
          exact .orLeft (inferFormula_sound ha).toProp (inferFormula_sound hb).toProp
        case orRight a b =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨sa, ha, sb, hb, rfl⟩ := run
          exact .orRight (inferFormula_sound ha).toProp (inferFormula_sound hb).toProp
        case orElim a b c =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨sa, ha, sb, hb, sc, hc, rfl⟩ := run
          exact .orElim (inferFormula_sound ha).toProp (inferFormula_sound hb).toProp
            (inferFormula_sound hc).toProp
        case falseElim a =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨sa, ha, rfl⟩ := run
          exact .falseElim (inferFormula_sound ha).toProp
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
        case existsElim a b =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨⟨⟩, ha, sb, hb, rfl⟩ := run
          exact .existsElim (checkMotive_sound ha) (inferFormula_sound hb).toProp
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
        case eqRefl =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst A
          exact .eqRefl
        case eqSubst a =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨⟨⟩, ha, rfl⟩ := run
          exact .eqSubst (checkMotive_sound ha)
        case succNeZero =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst A
          exact .succNeZero
        case succInj =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst A
          exact .succInj
        case lem P =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨s, hP, rfl⟩ := run
          exact .lem (inferFormula_sound hP).toProp
        case induction a =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨⟨⟩, ha, rfl⟩ := run
          exact .induction (checkMotive_sound ha)
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

end PRAProver.Core
