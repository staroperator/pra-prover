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

private theorem normal_succ_run {E a A n} (run : reduceTerm n E 0 a = .ok A) :
    ∃ m, reduceTerm m E 0 (.app .succ a) = .ok (.app .succ A) := by
  have head : whnfTerm 2 E (.app .succ a) = .ok (.app .succ a) := by
    simp [whnfTerm, pure, Except.pure]
  have succRun : reduceTermNeutral 2 E .succ = .ok .succ := by
    simp [reduceTermNeutral, whnfTerm, pure, Except.pure]
  refine ⟨max n 2 + 1, ?_⟩
  rw [reduceTerm.eq_def]
  simp only
  rw [whnfTerm_mono (m := max n 2) (by omega) head]
  simp only [pure, Except.pure, bind, Except.bind]
  rw [reduceTermNeutral_mono (m := max n 2) (by omega) succRun,
    reduceTerm_mono (m := max n 2) (by omega) run]

private theorem head_imp {E Ξ Γ H A B} (valid : EnvironmentWF E)
    (head : PredicateWhnf H) (eq : PredicateEq E Ξ Γ H (.imp A B) ⟨0, .prop⟩) :
    ∃ C D, H = .imp C D ∧ PredicateEq E Ξ Γ A C ⟨0, .prop⟩ ∧
      PredicateEq E Ξ Γ B D ⟨0, .prop⟩ := by
  have shape := eq.head_eq valid head PredicateWhnf.imp
  cases H <;> simp only [Predicate.formulaHead, Option.some.injEq, reduceCtorEq] at shape <;>
    try contradiction
  obtain ⟨left, right⟩ := eq.imp_injective valid
  exact ⟨_, _, rfl, left.symm, right.symm⟩

private theorem head_and {E Ξ Γ H A B} (valid : EnvironmentWF E)
    (head : PredicateWhnf H) (eq : PredicateEq E Ξ Γ H (.and A B) ⟨0, .prop⟩) :
    ∃ C D, H = .and C D ∧ PredicateEq E Ξ Γ A C ⟨0, .prop⟩ ∧
      PredicateEq E Ξ Γ B D ⟨0, .prop⟩ := by
  have shape := eq.head_eq valid head PredicateWhnf.and
  cases H <;> simp only [Predicate.formulaHead, Option.some.injEq, reduceCtorEq] at shape <;>
    try contradiction
  obtain ⟨left, right⟩ := eq.and_injective valid
  exact ⟨_, _, rfl, left.symm, right.symm⟩

private theorem head_or {E Ξ Γ H A B} (valid : EnvironmentWF E)
    (head : PredicateWhnf H) (eq : PredicateEq E Ξ Γ H (.or A B) ⟨0, .prop⟩) :
    ∃ C D, H = .or C D ∧ PredicateEq E Ξ Γ A C ⟨0, .prop⟩ ∧
      PredicateEq E Ξ Γ B D ⟨0, .prop⟩ := by
  have shape := eq.head_eq valid head PredicateWhnf.or
  cases H <;> simp only [Predicate.formulaHead, Option.some.injEq, reduceCtorEq] at shape <;>
    try contradiction
  obtain ⟨left, right⟩ := eq.or_injective valid
  exact ⟨_, _, rfl, left.symm, right.symm⟩

private theorem head_equal {E Ξ Γ H A B} (valid : EnvironmentWF E)
    (head : PredicateWhnf H) (eq : PredicateEq E Ξ Γ H (.equal A B) ⟨0, .prop⟩) :
    ∃ c d, H = .equal c d ∧ TermEq E Ξ Γ A c 0 ∧ TermEq E Ξ Γ B d 0 := by
  have shape := eq.head_eq valid head PredicateWhnf.equal
  cases H <;> simp only [Predicate.formulaHead, Option.some.injEq, reduceCtorEq] at shape <;>
    try contradiction
  obtain ⟨left, right⟩ := eq.equal_injective valid
  exact ⟨_, _, rfl, left.symm, right.symm⟩

private theorem head_all {E Ξ Γ H P} (valid : EnvironmentWF E)
    (head : PredicateWhnf H) (eq : PredicateEq E Ξ Γ H (.all P) ⟨0, .prop⟩) :
    ∃ Q, H = .all Q ∧ PredicateEq E Ξ Γ P Q ⟨1, .prop⟩ := by
  have shape := eq.head_eq valid head PredicateWhnf.all
  cases H <;> simp only [Predicate.formulaHead, Option.some.injEq, reduceCtorEq] at shape <;>
    try contradiction
  exact ⟨_, rfl, (eq.all_injective valid).symm⟩

private theorem head_ex {E Ξ Γ H P} (valid : EnvironmentWF E)
    (head : PredicateWhnf H) (eq : PredicateEq E Ξ Γ H (.ex P) ⟨0, .prop⟩) :
    ∃ Q, H = .ex Q ∧ PredicateEq E Ξ Γ P Q ⟨1, .prop⟩ := by
  have shape := eq.head_eq valid head PredicateWhnf.ex
  cases H <;> simp only [Predicate.formulaHead, Option.some.injEq, reduceCtorEq] at shape <;>
    try contradiction
  exact ⟨_, rfl, (eq.ex_injective valid).symm⟩

private theorem normal_successor_head {E n t b} (head : TermWhnf t)
    (run : reduceTerm n E 0 t = .ok (.app .succ b)) : ∃ a, t = .app .succ a := by
  cases n with
  | zero => simp [reduceTerm, exhausted, fail] at run
  | succ n =>
      simp only [reduceTerm, CheckResult.bind_eq_ok] at run
      obtain ⟨u, hu, run⟩ := run
      have same := whnfTerm_fixed head hu
      subst u
      cases t <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
        Except.ok.injEq, fail, reduceCtorEq] at run <;> try contradiction
      case app f a =>
        obtain ⟨g, hg, c, hc, eq⟩ := run
        have same := (Term.app.inj eq).1
        subst g
        cases head with
        | app hf _ =>
            have same := (reduceTermNeutral_succ_iff hf hg).mp rfl
            exact ⟨a, by rw [same]⟩
      case primrec base step arg =>
        obtain ⟨_, _, _, _, _, _, bad⟩ := run
        cases bad

private theorem weak_successor {E Ξ Γ t a} (valid : EnvironmentWF E)
    (eq : TermEq E Ξ Γ t (.app .succ a) 0) :
    ∃ b, TermEq E Ξ Γ a b 0 ∧ ∃ n, ∀ m ≥ n,
      whnfTerm m E t = .ok (.app .succ b) := by
  obtain ⟨i, u, hi⟩ := whnfTerm_terminates valid eq.regularity.1
  have run := hi i (by omega)
  have converted := (whnfTerm_sound valid eq.regularity.1 run).symm.trans eq
  obtain ⟨j, A, hj⟩ := reduceTerm_terminates valid eq.regularity.2.inv_app.2
  obtain ⟨k, hk⟩ := normal_succ_run (hj j (by omega))
  obtain ⟨l, N, hl⟩ := reduceTerm_of_eq valid converted
  have same := reduceTerm_unique (hl l (by omega)).2 hk
  subst N
  obtain ⟨b, rfl⟩ := normal_successor_head (whnfTerm_normal run) (hl l (by omega)).1
  exact ⟨b, (converted.succ_injective valid).symm, i, hi⟩

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
  | andLeft pair ih =>
      intro c A ctx typed
      obtain ⟨B, ⟨C, pair⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨H, head, eH, i, hi⟩ := complete_head valid ih ctx pair
      obtain ⟨B', C', rfl, eB, eC⟩ := head_and valid head eH
      refine ⟨B', .trans eB.symm eq, i + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          obtain ⟨_, hp, hw⟩ := hi m (by omega)
          simp only [inferProof, CheckResult.withSite_eq_ok, hp, hw,
            pure, Except.pure, bind, Except.bind]
  | andRight pair ih =>
      intro c A ctx typed
      obtain ⟨B, ⟨C, pair⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨H, head, eH, i, hi⟩ := complete_head valid ih ctx pair
      obtain ⟨C', B', rfl, eC, eB⟩ := head_and valid head eH
      refine ⟨B', .trans eB.symm eq, i + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          obtain ⟨_, hp, hw⟩ := hi m (by omega)
          simp only [inferProof, CheckResult.withSite_eq_ok, hp, hw,
            pure, Except.pure, bind, Except.bind]
  | orLeft other proof ih =>
      intro c A ctx typed
      obtain ⟨B, ⟨C, rfl, formed, proof⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨s, below, i, hi⟩ := inferFormula_complete formed
      obtain ⟨D, eD, j, hj⟩ := ih c C ctx proof
      refine ⟨.or D other, .trans (.or eD (.refl formed)) eq, max i j + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl, hj m (by omega)]
          rfl
  | orRight other proof ih =>
      intro c A ctx typed
      obtain ⟨B, ⟨C, rfl, formed, proof⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨s, below, i, hi⟩ := inferFormula_complete formed
      obtain ⟨D, eD, j, hj⟩ := ih c C ctx proof
      refine ⟨.or other D, .trans (.or (.refl formed) eD) eq, max i j + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl, hj m (by omega)]
          rfl
  | orElim _ _ target scrutinee left right ihs ihl ihr =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, formed, C, D, scrutinee, left, right⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨s, below, i, hi⟩ := inferFormula_complete formed
      obtain ⟨H, head, eH, j, hj⟩ := complete_head valid ihs ctx scrutinee
      obtain ⟨C', D', rfl, eC, eD⟩ := head_or valid head eH
      have left' := left.context_conversion valid (.cons eC (.refl ctx))
      have right' := right.context_conversion valid (.cons eD (.refl ctx))
      obtain ⟨l, hl⟩ := complete_check valid ihl
        (ctx.pushProof (eC.regularity valid).2) left'
      obtain ⟨r, hr⟩ := complete_check valid ihr
        (ctx.pushProof (eD.regularity valid).2) right'
      refine ⟨B, eq, max i (max j (max l r)) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          obtain ⟨_, hp, hw⟩ := hj m (by omega)
          simp only [inferProof, CheckResult.withSite_eq_ok, hp, hw,
            pure, Except.pure, bind, Except.bind]
          rw [hi m (by omega) c rfl rfl]
          rw [hl m (by omega), hr m (by omega)]
  | falseElim target proof ih =>
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
  | existsElim _ _ target scrutinee body ihs ihb =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, formed, P, scrutinee, body⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨s, below, i, hi⟩ := inferFormula_complete formed
      obtain ⟨H, head, eH, j, hj⟩ := complete_head valid ihs ctx scrutinee
      obtain ⟨Q, rfl, eP⟩ := head_ex valid head eH
      have contexts : ProofContextEq E c.parameters (0 :: c.locals)
          (.app P.shift (.bvar 0) :: c.proofs.map Predicate.shift)
          (.app Q.shift (.bvar 0) :: c.proofs.map Predicate.shift) :=
        .cons (.app (eP.shift valid 0) (.refl (.bvar rfl)))
          (.refl (ctx.pushLocal valid 0))
      have body' := body.context_conversion valid contexts
      obtain ⟨l, hl⟩ := complete_check valid ihb
        (c := (c.pushLocal 0).pushProof (.app Q.shift (.bvar 0)))
        (contexts.regularity valid).2 body'
      refine ⟨B, eq, max i (max j l) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          obtain ⟨_, hp, hw⟩ := hj m (by omega)
          simp only [inferProof, CheckResult.withSite_eq_ok, hp, hw,
            pure, Except.pure, bind, Except.bind]
          rw [hi m (by omega) c rfl rfl]
          rw [hl m (by omega)]
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
  | eqRefl term =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, formed⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨i, hi⟩ := checkTerm_complete formed
      refine ⟨.equal term term, eq, i + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl]
          rfl
  | eqSubst motive equality proof ihe ihp =>
      intro c A ctx typed
      obtain ⟨B, ⟨formed, a, b, rfl, equality, proof⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨H, head, eH, j, hj⟩ := complete_head valid ihe ctx equality
      obtain ⟨a', b', rfl, ea, eb⟩ := head_equal valid head eH
      obtain ⟨i, hi⟩ := checkMotive_complete formed
      obtain ⟨l, hl⟩ := complete_check valid ihp ctx
        (.conversion proof (.app (.refl formed) ea))
      refine ⟨.app motive b', .trans (.app (.refl formed) eb.symm) eq,
        max i (max j l) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          obtain ⟨_, hp, hw⟩ := hj m (by omega)
          simp only [inferProof, CheckResult.withSite_eq_ok, hp, hw,
            pure, Except.pure, bind, Except.bind]
          rw [hi m (by omega) c rfl rfl]
          simp only [equalitySides, pure, Except.pure]
          rw [hl m (by omega)]
  | succNeZero term =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, formed⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨i, hi⟩ := checkTerm_complete formed
      refine ⟨_, eq, i + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl]
          rfl
  | succInj proof ih =>
      intro c A ctx typed
      obtain ⟨B, ⟨a, b, rfl, proof⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨H, head, eH, i, hi⟩ := complete_head valid ih ctx proof
      obtain ⟨a', b', rfl, ea, eb⟩ := head_equal valid head eH
      obtain ⟨a'', ea', j, hj⟩ := weak_successor valid ea.symm
      obtain ⟨b'', eb', k, hk⟩ := weak_successor valid eb.symm
      refine ⟨.equal a'' b'', .trans (.subsumption (.equal ea'.symm eb'.symm) .lift) eq,
        max i (max j k) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          obtain ⟨_, hp, hw⟩ := hi m (by omega)
          simp only [inferProof, CheckResult.withSite_eq_ok, hp, hw,
            pure, Except.pure, bind, Except.bind]
          simp only [equalitySides, pure, Except.pure]
          rw [hj m (by omega), hk m (by omega)]
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
  | induction _ _ motive base step argument ihb ihs =>
      intro c A ctx typed
      obtain ⟨B, ⟨rfl, formed, base, step, argument⟩, eq⟩ := typed.inversion valid ctx
      obtain ⟨i, hi⟩ := checkMotive_complete formed
      obtain ⟨j, hj⟩ := checkTerm_complete argument
      obtain ⟨l, hl⟩ := complete_check valid ihb ctx base
      have motiveProp := formed.toProp
      have assumption : PredicateTyping E c.parameters (0 :: c.locals)
          (.app motive.shift (.bvar 0)) ⟨0, .prop⟩ :=
        .app (motiveProp.shift valid 0) (.bvar rfl)
      obtain ⟨r, hr⟩ := complete_check valid ihs
        ((ctx.pushLocal valid 0).pushProof assumption) step
      refine ⟨_, eq, max i (max j (max l r)) + 1, ?_⟩
      intro m le
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferProof, CheckResult.withSite_eq_ok]
          rw [hi m (by omega) c rfl rfl, hj m (by omega) c rfl rfl,
            hl m (by omega), hr m (by omega)]
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
