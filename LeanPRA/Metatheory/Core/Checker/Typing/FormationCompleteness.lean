module

public import LeanPRA.Metatheory.Core.Checker.Typing.Predicate

/-!
# Sufficient depth for term and predicate synthesis and checking

- `inferTerm_complete` supplies a stable successful depth for each term derivation.
- `checkTerm_complete` supplies a stable depth for checking its arity.
- `inferPredicate_complete` infers a signature below any derivable signature.
- `checkPredicate_complete` supplies a stable depth for checking the full signature.
- `inferFormula_complete`, `checkFormula_complete`, and `checkMotive_complete`
  specialize it.
- `checkContext_complete` validates every formed list of local proof assumptions.
- `checkFunctionArguments_complete` and `checkPredicateArguments_complete` cover actuals.

Inference returns a principal signature included in every signature allowed by subsumption.
-/

namespace LeanPRA.Core

open Theory

private theorem arity_refl (k : Arity) : checkArity k k = .ok () := by
  simp [checkArity, pure, Except.pure]

private theorem count_refl (name kind k) : checkArgumentCount name kind k k = .ok () := by
  simp [checkArgumentCount, pure, Except.pure]

private theorem sort_sub {σ τ} (sub : PredicateSubtyping σ τ) :
    checkSort τ.sort σ.sort = .ok () := by
  cases sub with
  | refl => cases σ.sort <;> simp [checkSort, pure, Except.pure]
  | lift => simp [checkSort, pure, Except.pure]

private theorem arguments_complete {n E c fs ks}
    (lengths : fs.length = ks.length)
    (checks : ∀ pair ∈ ks.zip fs, inferTerm n E c pair.2 = .ok pair.1)
    (name : Lean.Name) : checkFunctionArguments n E c name ks fs = .ok () := by
  unfold checkFunctionArguments
  apply CheckResult.bind_eq_ok.mpr
  refine ⟨(), ?_, ?_⟩
  · rw [lengths]; exact count_refl _ _ _
  · apply CheckResult.bind_eq_ok.mpr
    refine ⟨(), ?_, rfl⟩
    apply (CheckResult.forIn_yield_eq_ok _ _).mpr
    intro pair hp
    simp only [CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
    exact ⟨pair.1, checks pair hp, arity_refl _⟩

private theorem term_complete {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k) :
    ∃ n, ∀ m ≥ n, ∀ c : Context, c.parameters = Ξ → c.locals = Γ →
      inferTerm m E c t = .ok k := by
  induction h using TermTyping.rec
    (motive_2 := fun Γ fs ks _ => ∃ n, ∀ m ≥ n, ∀ c : Context,
      c.parameters = Ξ → c.locals = Γ →
      ∀ pair ∈ ks.zip fs, inferTerm m E c pair.2 = .ok pair.1) with
  | bvar lookup =>
      refine ⟨1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m => simp [inferTerm, hl, lookup, pure, Except.pure]
  | parameter lookup =>
      refine ⟨1, ?_⟩
      intro m hm c hc hl
      have hf := congrArg ParameterContext.functions hc
      cases m with
      | zero => omega
      | succ m => simp [inferTerm, Context.parameters] at hf ⊢; simp [hf, lookup, pure, Except.pure]
  | zero =>
      refine ⟨1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m => simp [inferTerm, pure, Except.pure]
  | succ =>
      refine ⟨1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m => simp [inferTerm, pure, Except.pure]
  | lam body ih =>
      obtain ⟨n, ih⟩ := ih
      refine ⟨n + 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferTerm, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          exact ⟨_, ih m (by omega) (c.pushExpressionLocal 0) hc
            (by simp [Context.pushExpressionLocal, hl]), rfl⟩
  | app f a ihf iha =>
      obtain ⟨n, ihf⟩ := ihf
      obtain ⟨j, iha⟩ := iha
      refine ⟨max n j + 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m =>
          rw [inferTerm.eq_def]
          simp only [CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          refine ⟨_, ihf m (by omega) c hc hl, ?_⟩
          simp only [CheckResult.bind_eq_ok]
          exact ⟨_, iha m (by omega) c hc hl, (), arity_refl _, rfl⟩
  | letE value body ihv ihb =>
      obtain ⟨n, ihv⟩ := ihv
      obtain ⟨j, ihb⟩ := ihb
      refine ⟨max n j + 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferTerm, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          refine ⟨_, ihv m (by omega) c hc hl, ?_⟩
          exact ihb m (by omega) (c.pushExpressionLocal _) hc
            (by simp [Context.pushExpressionLocal, hl])
  | primrec b s ihb ihs =>
      obtain ⟨n, ihb⟩ := ihb
      obtain ⟨j, ihs⟩ := ihs
      refine ⟨max n j + 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferTerm, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          exact ⟨(), ⟨_, ihb m (by omega) c hc hl, arity_refl _⟩,
            (), ⟨_, ihs m (by omega) c hc hl, arity_refl _⟩, rfl⟩
  | definition lookup args ih =>
      obtain ⟨n, ih⟩ := ih
      refine ⟨n + 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferTerm, Environment.lookup, lookup, CheckResult.withSite_eq_ok,
            CheckResult.bind_eq_ok]
          refine ⟨(), ?_, (), ?_, rfl⟩
          · rw [← args.length_eq]; exact count_refl _ _ _
          · apply (CheckResult.forIn_yield_eq_ok _ _).mpr
            intro pair hp
            simp only [CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
            exact ⟨pair.1, ih m (by omega) c hc hl pair hp, arity_refl _⟩
  | nil => exact ⟨0, by intros; simp_all⟩
  | cons head tail ihh iht =>
      obtain ⟨n, ihh⟩ := ihh
      obtain ⟨j, iht⟩ := iht
      refine ⟨max n j, ?_⟩
      intro m hm c hc hl pair hp
      simp only [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ihh m (by omega) c hc hl
      · exact iht m (by omega) c hc hl pair hp

private theorem function_arguments_depth {E Ξ Γ fs ks}
    (h : FunctionArguments E Ξ Γ fs ks) :
    ∃ n, ∀ m ≥ n, ∀ c : Context, c.parameters = Ξ → c.locals = Γ →
      ∀ pair ∈ ks.zip fs, inferTerm m E c pair.2 = .ok pair.1 := by
  induction h using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True) with
  | nil => exact ⟨0, by intros; simp_all⟩
  | cons head tail ihh iht =>
      obtain ⟨n, hn⟩ := term_complete head
      obtain ⟨j, hj⟩ := iht
      refine ⟨max n j, ?_⟩
      intro m hm c hc hl pair hp
      simp only [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hn m (by omega) c hc hl
      · exact hj m (by omega) c hc hl pair hp
  | _ => trivial

private theorem predicate_check {n E c P σ τ} (sub : PredicateSubtyping σ τ)
    (run : inferPredicate n E c P = .ok σ) : checkPredicate n E c P τ = .ok () := by
  simp only [checkPredicate, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
  refine ⟨σ, run, (), ?_, sort_sub sub⟩
  rw [sub.arity_eq]
  exact arity_refl _

private theorem predicate_complete {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ) :
    ∃ τ, PredicateSubtyping τ σ ∧ ∃ n, ∀ m ≥ n, ∀ c : Context,
      c.parameters = Ξ → c.locals = Γ → inferPredicate m E c P = .ok τ := by
  induction h using PredicateTyping.rec
    (motive_2 := fun Γ ps signatures _ => ∃ n, ∀ m ≥ n, ∀ c : Context,
      c.parameters = Ξ → c.locals = Γ →
      ∀ pair ∈ signatures.zip ps, checkPredicate m E c pair.2 pair.1 = .ok ()) with
  | false =>
      refine ⟨_, .refl, 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m => simp [inferPredicate, pure, Except.pure]
  | true =>
      refine ⟨_, .refl, 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m => simp [inferPredicate, pure, Except.pure]
  | equal a b =>
      obtain ⟨n, hn⟩ := term_complete a
      obtain ⟨j, hj⟩ := term_complete b
      refine ⟨_, .refl, max n j + 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferPredicate, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok,
            checkTerm]
          exact ⟨(), ⟨_, hn m (by omega) c hc hl, arity_refl _⟩,
            (), ⟨_, hj m (by omega) c hc hl, arity_refl _⟩, rfl⟩
  | imp A B ihA ihB =>
      obtain ⟨⟨k, s⟩, subA, n, hn⟩ := ihA
      obtain ⟨⟨j, t⟩, subB, l, hl⟩ := ihB
      have ha : k = 0 := subA.arity_eq
      have hb : j = 0 := subB.arity_eq
      subst k; subst j
      refine ⟨_, .join subA subB, max n l + 1, ?_⟩
      intro m hm c hc hlocals
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferPredicate, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          exact ⟨_, hn m (by omega) c hc hlocals, _, hl m (by omega) c hc hlocals,
            (), arity_refl _, (), arity_refl _, rfl⟩
  | and A B ihA ihB =>
      obtain ⟨⟨k, s⟩, subA, n, hn⟩ := ihA
      obtain ⟨⟨j, t⟩, subB, l, hl⟩ := ihB
      have ha : k = 0 := subA.arity_eq
      have hb : j = 0 := subB.arity_eq
      subst k; subst j
      refine ⟨_, .join subA subB, max n l + 1, ?_⟩
      intro m hm c hc hlocals
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferPredicate, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          exact ⟨_, hn m (by omega) c hc hlocals, _, hl m (by omega) c hc hlocals,
            (), arity_refl _, (), arity_refl _, rfl⟩
  | or A B ihA ihB =>
      obtain ⟨⟨k, s⟩, subA, n, hn⟩ := ihA
      obtain ⟨⟨j, t⟩, subB, l, hl⟩ := ihB
      have ha : k = 0 := subA.arity_eq
      have hb : j = 0 := subB.arity_eq
      subst k; subst j
      refine ⟨_, .join subA subB, max n l + 1, ?_⟩
      intro m hm c hc hlocals
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferPredicate, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          exact ⟨_, hn m (by omega) c hc hlocals, _, hl m (by omega) c hc hlocals,
            (), arity_refl _, (), arity_refl _, rfl⟩
  | all P ih =>
      obtain ⟨⟨k, s⟩, sub, n, hn⟩ := ih
      have ha : k = 1 := sub.arity_eq
      subst k
      refine ⟨_, .refl, n + 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferPredicate, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          exact ⟨_, hn m (by omega) c hc hl, (), arity_refl _, rfl⟩
  | ex P ih =>
      obtain ⟨⟨k, s⟩, sub, n, hn⟩ := ih
      have ha : k = 1 := sub.arity_eq
      subst k
      refine ⟨_, .refl, n + 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferPredicate, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          exact ⟨_, hn m (by omega) c hc hl, (), arity_refl _, rfl⟩
  | parameter lookup =>
      refine ⟨_, .refl, 1, ?_⟩
      intro m hm c hc hl
      have hp := congrArg ParameterContext.predicates hc
      cases m with
      | zero => omega
      | succ m =>
          simp only [Context.parameters] at hp
          simp [inferPredicate, hp, lookup, pure, Except.pure]
  | @lam Γ P k s hint body ih =>
      obtain ⟨⟨j, t⟩, sub, n, hn⟩ := ih
      have ha : j = k := sub.arity_eq
      subst j
      refine ⟨_, sub.withArity (k + 1), n + 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferPredicate, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          exact ⟨_, hn m (by omega) (c.pushExpressionLocal 0) hc
            (by simp [Context.pushExpressionLocal, hl]), rfl⟩
  | @app Γ P k s a function argument ih =>
      obtain ⟨⟨j, t⟩, sub, n, hn⟩ := ih
      have ha : j = k + 1 := sub.arity_eq
      subst j
      obtain ⟨l, hl⟩ := term_complete argument
      refine ⟨_, sub.withArity k, max n l + 1, ?_⟩
      intro m hm c hc hlocals
      cases m with
      | zero => omega
      | succ m =>
          rw [inferPredicate.eq_def]
          simp only [CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          refine ⟨_, hn m (by omega) c hc hlocals, ?_⟩
          simp only [CheckResult.bind_eq_ok, checkTerm, CheckResult.withSite_eq_ok]
          exact ⟨(), ⟨_, hl m (by omega) c hc hlocals, arity_refl _⟩, rfl⟩
  | letTerm value body ih =>
      obtain ⟨τ, sub, n, hn⟩ := ih
      obtain ⟨j, hj⟩ := term_complete value
      refine ⟨τ, sub, max n j + 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferPredicate, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          exact ⟨_, hj m (by omega) c hc hl, hn m (by omega) c hc hl⟩
  | letPredicate value body ihv ihb =>
      obtain ⟨τ, sub, n, hn⟩ := ihb
      obtain ⟨υ, below, j, hj⟩ := ihv
      refine ⟨τ, sub, max n j + 1, ?_⟩
      intro m hm c hc hl
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferPredicate, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
          exact ⟨υ, hj m (by omega) c hc hl, hn m (by omega) c hc hl⟩
  | definition lookup functions predicates ihp =>
      obtain ⟨j, hj⟩ := function_arguments_depth functions
      obtain ⟨l, hl⟩ := ihp
      refine ⟨_, .refl, max j l + 1, ?_⟩
      intro m hm c hc hlocals
      cases m with
      | zero => omega
      | succ m =>
          simp only [inferPredicate, CheckResult.withSite_eq_ok, Environment.lookup,
            lookup, CheckResult.bind_eq_ok]
          refine ⟨(), arguments_complete functions.length_eq
            (hj m (by omega) c hc hlocals) _, (), ?_, (), ?_, rfl⟩
          · rw [← predicates.length_eq]; exact count_refl _ _ _
          · apply (CheckResult.forIn_yield_eq_ok _ _).mpr
            exact hl m (by omega) c hc hlocals
  | subsumption typing sub ih =>
      obtain ⟨τ, below, n, hn⟩ := ih
      exact ⟨τ, below.trans sub, n, hn⟩
  | nil => exact ⟨0, by intros; simp_all⟩
  | cons head tail ihh iht =>
      obtain ⟨τ, sub, n, hn⟩ := ihh
      obtain ⟨j, hj⟩ := iht
      refine ⟨max n j, ?_⟩
      intro m hm c hc hl pair hp
      simp only [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact predicate_check sub (hn m (by omega) c hc hl)
      · exact hj m (by omega) c hc hl pair hp

/-- A term derivation has a depth beyond which inference always returns its exact arity. -/
public theorem inferTerm_complete {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k) :
    ∃ n, ∀ m ≥ n, ∀ c : Context, c.parameters = Ξ → c.locals = Γ →
      inferTerm m E c t = .ok k := term_complete h

/-- A term derivation has a depth beyond which checking always succeeds at its arity. -/
public theorem checkTerm_complete {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k) :
    ∃ n, ∀ m ≥ n, ∀ c : Context, c.parameters = Ξ → c.locals = Γ →
      checkTerm m E c t k = .ok () := by
  obtain ⟨n, hn⟩ := term_complete h
  refine ⟨n, ?_⟩
  intro m hm c hc hl
  simp only [checkTerm, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
  exact ⟨k, hn m hm c hc hl, arity_refl k⟩

/-- Predicate inference eventually succeeds at a signature below any displayed derivable one. -/
public theorem inferPredicate_complete {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ) :
    ∃ τ, PredicateSubtyping τ σ ∧ ∃ n, ∀ m ≥ n, ∀ c : Context,
      c.parameters = Ξ → c.locals = Γ → inferPredicate m E c P = .ok τ := predicate_complete h

/-- Predicate checking eventually succeeds at the full signature of a typing derivation. -/
public theorem checkPredicate_complete {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ) :
    ∃ n, ∀ m ≥ n, ∀ c : Context, c.parameters = Ξ → c.locals = Γ →
      checkPredicate m E c P σ = .ok () := by
  obtain ⟨τ, sub, n, hn⟩ := predicate_complete h
  refine ⟨n, ?_⟩
  intro m hm c hc hl
  exact predicate_check sub (hn m hm c hc hl)

/-- Formula inference eventually returns a sort included in every derivable formula sort. -/
public theorem inferFormula_complete {E Ξ Γ P s} (h : PredicateTyping E Ξ Γ P ⟨0, s⟩) :
    ∃ t, PredicateSubtyping ⟨0, t⟩ ⟨0, s⟩ ∧ ∃ n, ∀ m ≥ n, ∀ c : Context,
      c.parameters = Ξ → c.locals = Γ → inferFormula m E c P = .ok t := by
  obtain ⟨τ, sub, n, hn⟩ := predicate_complete h
  have arity := sub.arity_eq
  obtain ⟨k, t⟩ := τ
  simp only at arity
  subst k
  refine ⟨t, sub, n, ?_⟩
  intro m le c hc hl
  simp only [inferFormula, CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
  exact ⟨⟨0, t⟩, hn m le c hc hl, (), arity_refl 0, rfl⟩

/-- Checking a derivable formula eventually succeeds at its stated sort. -/
public theorem checkFormula_complete {E Ξ Γ P s} (h : PredicateTyping E Ξ Γ P ⟨0, s⟩) :
    ∃ n, ∀ m ≥ n, ∀ c : Context, c.parameters = Ξ → c.locals = Γ →
      checkFormula m E c P s = .ok () := checkPredicate_complete h

/-- Checking a unary motive eventually succeeds at its stated sort. -/
public theorem checkMotive_complete {E Ξ Γ P s} (h : PredicateTyping E Ξ Γ P ⟨1, s⟩) :
    ∃ n, ∀ m ≥ n, ∀ c : Context, c.parameters = Ξ → c.locals = Γ →
      checkMotive m E c P s = .ok () := checkPredicate_complete h

/-- Every formed proof context passes context validation at all sufficiently large depths. -/
public theorem checkContext_complete {E} {c : Context}
    (h : ContextWF E c.parameters c.locals c.proofs) :
    ∃ n, ∀ m ≥ n, checkContext m E c = .ok () := by
  have all : ∀ H, ContextWF E c.parameters c.locals H →
      ∃ n, ∀ m ≥ n, ∀ P ∈ H, ∃ s, inferFormula m E c P = .ok s := by
    intro H h
    induction h with
    | nil => exact ⟨0, by intros; contradiction⟩
    | cons head tail ih =>
        obtain ⟨s, sub, n, hn⟩ := inferFormula_complete head
        obtain ⟨j, hj⟩ := ih
        refine ⟨max n j, ?_⟩
        intro m le P hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨s, hn m (by omega) c rfl rfl⟩
        · exact hj m (by omega) P hp
  obtain ⟨n, hn⟩ := all _ h
  refine ⟨n, ?_⟩
  intro m le
  simp only [checkContext, CheckResult.bind_eq_ok]
  refine ⟨(), ?_, rfl⟩
  exact (CheckResult.forIn_discard_eq_ok _ _).mpr (hn m le)

/-- All function actuals of a formed declaration application eventually pass checking. -/
public theorem checkFunctionArguments_complete {E} {c : Context} {fs ks}
    (h : FunctionArguments E c.parameters c.locals fs ks) (name : Lean.Name) :
    ∃ n, ∀ m ≥ n, checkFunctionArguments m E c name ks fs = .ok () := by
  obtain ⟨n, hn⟩ := function_arguments_depth h
  refine ⟨n, ?_⟩
  intro m le
  simp only [checkFunctionArguments, CheckResult.bind_eq_ok]
  refine ⟨(), ?_, (), ?_, rfl⟩
  · rw [← h.length_eq]; exact count_refl _ _ _
  · apply (CheckResult.forIn_yield_eq_ok _ _).mpr
    intro pair hp
    simp only [CheckResult.withSite_eq_ok, CheckResult.bind_eq_ok]
    exact ⟨pair.1, hn m le c rfl rfl pair hp, arity_refl _⟩

/-- All predicate actuals eventually pass checking at their declared full signatures. -/
public theorem checkPredicateArguments_complete {E} {c : Context} {ps signatures}
    (h : PredicateArguments E c.parameters c.locals ps signatures) (name : Lean.Name) :
    ∃ n, ∀ m ≥ n, checkPredicateArguments m E c name signatures ps = .ok () := by
  have each : ∃ n, ∀ m ≥ n, ∀ pair ∈ signatures.zip ps,
      checkPredicate m E c pair.2 pair.1 = .ok () := by
    generalize hc : c.locals = Γ at h
    induction h using PredicateArguments.rec (motive_1 := fun _ _ _ _ => True) with
    | nil => exact ⟨0, by intros; contradiction⟩
    | cons head tail ihh iht =>
        obtain ⟨n, hn⟩ := checkPredicate_complete head
        obtain ⟨j, hj⟩ := iht hc
        refine ⟨max n j, ?_⟩
        intro m le pair hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hn m (by omega) c rfl hc
        · exact hj m (by omega) pair hp
    | _ => trivial
  obtain ⟨n, hn⟩ := each
  refine ⟨n, ?_⟩
  intro m le
  simp only [checkPredicateArguments, CheckResult.bind_eq_ok]
  refine ⟨(), ?_, (), (CheckResult.forIn_yield_eq_ok _ _).mpr (hn m le), rfl⟩
  rw [← h.length_eq]
  exact count_refl _ _ _

end LeanPRA.Core
