module

public import LeanPRA.Metatheory.Core.Checker.Typing.FormationCompleteness
public import LeanPRA.Metatheory.Core.Checker.Typing.Proof
public import LeanPRA.Metatheory.Core.Judgement.ProofInversion
import LeanPRA.Metatheory.Core.Properties.Constructors
import LeanPRA.Metatheory.Core.Properties.Normalization.Soundness

/-!
# Sufficient depth for explicit proof data

- `inferProof_complete` returns a conclusion equal to any derivable conclusion.
- `checkProof_complete` accepts every explicit declaratively derivable proof.

All results supply a bound valid at every larger depth and assume formed local assumptions and
a valid global map. All proof constructors are covered. Inference conclusions are compared by
definitional equality, since proof typing includes conversion.
-/

namespace LeanPRA.Core

open Theory

private abbrev InferComplete (E : Environment) (p : Proof) : Prop :=
  ∀ (c : Context) A, ContextWF E c.parameters c.locals c.proofs →
    ProofTyping E c.parameters c.locals c.proofs p A →
    ∃ B, PredicateEq E c.parameters c.locals B A ⟨0, .prop⟩ ∧
      ∃ n, ∀ m ≥ n, inferProof m E c p = .ok B

private theorem complete_check {E p} (valid : EnvironmentWF E) (ih : InferComplete E p)
    {c : Context} {A} (ctx : ContextWF E c.parameters c.locals c.proofs)
    (typed : ProofTyping E c.parameters c.locals c.proofs p A) :
    ∃ n, ∀ m ≥ n, checkProof m E c p A = .ok () := by
  obtain ⟨B, eq, i, hi⟩ := ih c A ctx typed
  obtain ⟨j, hj⟩ := defEqPredicate_complete valid eq
  refine ⟨max i j + 1, ?_⟩
  intro m le
  cases m with
  | zero => omega
  | succ m =>
      simp only [checkProof, CheckResult.withSite_eq_ok]
      rw [hi m (by omega)]
      simp [hj m (by omega), pure, Except.pure]

private theorem complete_head {E p} (valid : EnvironmentWF E) (ih : InferComplete E p)
    {c : Context} {A} (ctx : ContextWF E c.parameters c.locals c.proofs)
    (typed : ProofTyping E c.parameters c.locals c.proofs p A) :
    ∃ B, PredicateWhnf B ∧ PredicateEq E c.parameters c.locals B A ⟨0, .prop⟩ ∧
      ∃ n, ∀ m ≥ n, ∃ C,
        inferProof m E c p = .ok C ∧ whnfPredicate m E C = .ok B := by
  obtain ⟨B, eq, i, hi⟩ := ih c A ctx typed
  obtain ⟨j, C, hj⟩ := whnfPredicate_terminates valid (eq.regularity valid).1
  have run := hj j (by omega)
  refine ⟨C, whnfPredicate_normal run,
    .trans (whnfPredicate_sound valid (eq.regularity valid).1 run).symm eq,
    max i j, ?_⟩
  intro m le
  exact ⟨B, hi m (by omega), hj m (by omega)⟩

private theorem head_imp {E Ξ Γ H A B} (valid : EnvironmentWF E)
    (head : PredicateWhnf H) (eq : PredicateEq E Ξ Γ H (.imp A B) ⟨0, .prop⟩) :
    ∃ C D, H = .imp C D ∧ PredicateEq E Ξ Γ A C ⟨0, .prop⟩ ∧
      PredicateEq E Ξ Γ B D ⟨0, .prop⟩ := by
  have shape := eq.head_eq valid head PredicateWhnf.imp
  cases H <;> simp only [Predicate.formulaHead, Option.some.injEq, reduceCtorEq] at shape <;>
    try contradiction
  obtain ⟨left, right⟩ := eq.imp_injective valid
  exact ⟨_, _, rfl, left.symm, right.symm⟩

private theorem head_all {E Ξ Γ H P} (valid : EnvironmentWF E)
    (head : PredicateWhnf H) (eq : PredicateEq E Ξ Γ H (.all P) ⟨0, .prop⟩) :
    ∃ Q, H = .all Q ∧ PredicateEq E Ξ Γ P Q ⟨1, .prop⟩ := by
  have shape := eq.head_eq valid head PredicateWhnf.all
  cases H <;> simp only [Predicate.formulaHead, Option.some.injEq, reduceCtorEq] at shape <;>
    try contradiction
  exact ⟨_, rfl, (eq.all_injective valid).symm⟩

private theorem proof_complete (E : Environment) (valid : EnvironmentWF E) (p : Proof) :
    InferComplete E p := by
  induction p with
  | hyp i =>
      intro c A ctx typed
      obtain ⟨B, lookup, eq⟩ := typed.inv_hyp valid ctx
      refine ⟨B, eq, 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m => simp [inferProof, lookup, pure, Except.pure]
  | trueIntro =>
      intro c A ctx typed
      obtain ⟨B, prem, eq⟩ := typed.inversion valid ctx
      cases prem
      refine ⟨.true, eq, 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m => simp [inferProof, pure, Except.pure]
  | theoremE name fs ps =>
      intro c A ctx typed
      obtain ⟨d, lookup, functions, predicates, eq⟩ := typed.inv_theorem valid ctx
      obtain ⟨i, hi⟩ := checkFunctionArguments_complete functions name
      obtain ⟨j, hj⟩ := checkPredicateArguments_complete predicates name
      refine ⟨_, eq, max i j + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, Environment.lookup, lookup, CheckResult.withSite_eq_ok]
          rw [hi m (by omega), hj m (by omega)]
          rfl
  | impIntro _ antecedent body ih =>
      intro c A ctx typed
      obtain ⟨B, ⟨C, rfl, formed, body⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨s, below, i, hi⟩ := inferFormula_complete formed
      obtain ⟨D, eD, j, hj⟩ := ih (c.pushProof antecedent) C (ctx.pushProof formed) body
      refine ⟨.imp antecedent D, .trans (.imp (.refl formed) eD) eq, max i j + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl, hj m (by omega)]
          rfl
  | impElim function argument ihf iha =>
      intro c A ctx typed
      obtain ⟨B, ⟨C, function, argument⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨H, head, eH, i, hi⟩ := complete_head valid ihf ctx function
      obtain ⟨C', B', rfl, eC, eB⟩ := head_imp valid head eH
      obtain ⟨j, hj⟩ := complete_check valid iha ctx (.conversion argument eC)
      refine ⟨B', .trans eB.symm eq, max i j + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          obtain ⟨_, hp, hw⟩ := hi m (by omega)
          simp only [inferProof, CheckResult.withSite_eq_ok, hp, hw,
            pure, Except.pure, bind, Except.bind]
          rw [hj m (by omega)]
  | andIntro left right ihl ihr =>
      intro c A ctx typed
      obtain ⟨B, ⟨C, D, rfl, left, right⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨C', eC, i, hi⟩ := ihl c C ctx left
      obtain ⟨D', eD, j, hj⟩ := ihr c D ctx right
      refine ⟨.and C' D', .trans (.and eC eD) eq, max i j + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega), hj m (by omega)]
          rfl
  | andLeft a b =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, ha, hb⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨sa, belowa, na, runa⟩ := inferFormula_complete ha
      obtain ⟨sb, belowb, nb, runb⟩ := inferFormula_complete hb
      refine ⟨_, eq, max na (nb) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [runa m (by omega) c rfl rfl, runb m (by omega) c rfl rfl]
          rfl
  | andRight a b =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, ha, hb⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨sa, belowa, na, runa⟩ := inferFormula_complete ha
      obtain ⟨sb, belowb, nb, runb⟩ := inferFormula_complete hb
      refine ⟨_, eq, max na (nb) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [runa m (by omega) c rfl rfl, runb m (by omega) c rfl rfl]
          rfl
  | orLeft a b =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, ha, hb⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨sa, belowa, na, runa⟩ := inferFormula_complete ha
      obtain ⟨sb, belowb, nb, runb⟩ := inferFormula_complete hb
      refine ⟨_, eq, max na (nb) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [runa m (by omega) c rfl rfl, runb m (by omega) c rfl rfl]
          rfl
  | orRight a b =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, ha, hb⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨sa, belowa, na, runa⟩ := inferFormula_complete ha
      obtain ⟨sb, belowb, nb, runb⟩ := inferFormula_complete hb
      refine ⟨_, eq, max na (nb) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [runa m (by omega) c rfl rfl, runb m (by omega) c rfl rfl]
          rfl
  | orElim a b c =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, ha, hb, hc⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨sa, belowa, na, runa⟩ := inferFormula_complete ha
      obtain ⟨sb, belowb, nb, runb⟩ := inferFormula_complete hb
      obtain ⟨sc, belowc, nc, runc⟩ := inferFormula_complete hc
      refine ⟨_, eq, max na (max nb (nc)) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [runa m (by omega) c rfl rfl, runb m (by omega) c rfl rfl, runc m (by omega) c rfl rfl]
          rfl
  | falseElim a =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, ha⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨sa, belowa, na, runa⟩ := inferFormula_complete ha
      refine ⟨_, eq, na + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [runa m (by omega) c rfl rfl]
          rfl
  | forallIntro _ motive body ih =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, formed, body⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨i, hi⟩ := checkMotive_complete formed
      obtain ⟨j, hj⟩ := complete_check valid ih (ctx.pushLocal valid 0) body
      refine ⟨.all motive, eq, max i j + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl, hj m (by omega)]
          rfl
  | forallElim proof argument ih =>
      intro c A ctx typed
      obtain ⟨B, ⟨P, rfl, proof, argument⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨H, head, eH, j, hj⟩ := complete_head valid ih ctx proof
      obtain ⟨Q, rfl, eP⟩ := head_all valid head eH
      obtain ⟨i, hi⟩ := checkTerm_complete argument
      refine ⟨.app Q _, .trans (.app eP.symm (.refl argument)) eq, max i j + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          obtain ⟨_, hp, hw⟩ := hj m (by omega)
          simp only [inferProof, CheckResult.withSite_eq_ok, hp, hw,
            pure, Except.pure, bind, Except.bind]
          rw [hi m (by omega) c rfl rfl]
  | existsIntro motive witness proof ih =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, formed, witness, proof⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨i, hi⟩ := checkMotive_complete formed
      obtain ⟨j, hj⟩ := checkTerm_complete witness
      obtain ⟨l, hl⟩ := complete_check valid ih ctx proof
      refine ⟨.ex motive, eq, max i (max j l) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl, hj m (by omega) c rfl rfl, hl m (by omega)]
          rfl
  | existsElim a b =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, ha, hb⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨na, runa⟩ := checkMotive_complete ha
      obtain ⟨sb, belowb, nb, runb⟩ := inferFormula_complete hb
      refine ⟨_, eq, max na (nb) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [runa m (by omega) c rfl rfl, runb m (by omega) c rfl rfl]
          rfl
  | letE _ type value body ihv ihb =>
      intro c A ctx typed
      obtain ⟨B, ⟨formed, value, body⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨s, below, i, hi⟩ := inferFormula_complete formed
      obtain ⟨j, hj⟩ := complete_check valid ihv ctx value
      obtain ⟨C, eC, l, hl⟩ := ihb (c.pushProof type) B (ctx.pushProof formed) body
      refine ⟨C, .trans eC eq, max i (max j l) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl, hj m (by omega), hl m (by omega)]
          rfl
  | letTerm _ value body ih =>
      intro c A ctx typed
      obtain ⟨B, ⟨⟨arity, value⟩, body⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨i, hi⟩ := inferTerm_complete value
      obtain ⟨C, eC, j, hj⟩ := ih c B ctx body
      refine ⟨C, .trans eC eq, max i j + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl, hj m (by omega)]
          rfl
  | letPredicate _ value body ih =>
      intro c A ctx typed
      obtain ⟨B, ⟨⟨signature, value⟩, body⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨τ, below, i, hi⟩ := inferPredicate_complete value
      obtain ⟨C, eC, j, hj⟩ := ih c B ctx body
      refine ⟨C, .trans eC eq, max i j + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl, hj m (by omega)]
          rfl
  | ascribe type proof ih =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, formed, proof⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨s, below, i, hi⟩ := inferFormula_complete formed
      obtain ⟨j, hj⟩ := complete_check valid ih ctx proof
      refine ⟨B, eq, max i j + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl, hj m (by omega)]
          rfl
  | eqRefl =>
      intro c A ctx typed
      obtain ⟨B, prem, eq⟩ := typed.inversion valid ctx
      cases prem
      refine ⟨_, eq, 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rfl
  | eqSubst a =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, ha⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨na, runa⟩ := checkMotive_complete ha
      refine ⟨_, eq, na + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [runa m (by omega) c rfl rfl]
          rfl
  | succNeZero =>
      intro c A ctx typed
      obtain ⟨B, prem, eq⟩ := typed.inversion valid ctx
      cases prem
      refine ⟨_, eq, 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rfl
  | succInj =>
      intro c A ctx typed
      obtain ⟨B, prem, eq⟩ := typed.inversion valid ctx
      cases prem
      refine ⟨_, eq, 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rfl
  | lem formula =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, formed⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨s, below, i, hi⟩ := inferFormula_complete formed
      refine ⟨_, eq, i + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl]
          rfl
  | induction a =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, ha⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨na, runa⟩ := checkMotive_complete ha
      refine ⟨_, eq, na + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [runa m (by omega) c rfl rfl]
          rfl

/-- Proof inference eventually returns a fixed conclusion definitionally equal to any
specified derivable conclusion, accounting for conversion in proof typing. -/
public theorem inferProof_complete {E} {c : Context} {p A} (valid : EnvironmentWF E)
    (ctx : ContextWF E c.parameters c.locals c.proofs)
    (typed : ProofTyping E c.parameters c.locals c.proofs p A) :
    ∃ B, PredicateEq E c.parameters c.locals B A ⟨0, .prop⟩ ∧
      ∃ n, ∀ m ≥ n, inferProof m E c p = .ok B := proof_complete E valid p c A ctx typed

/-- Every explicit derivable proof passes checking at every sufficiently large depth. -/
public theorem checkProof_complete {E} {c : Context} {p A} (valid : EnvironmentWF E)
    (ctx : ContextWF E c.parameters c.locals c.proofs)
    (typed : ProofTyping E c.parameters c.locals c.proofs p A) :
    ∃ n, ∀ m ≥ n, checkProof m E c p A = .ok () :=
  complete_check valid (proof_complete E valid p) ctx typed

end LeanPRA.Core
