module

public import LeanPRA.Metatheory.Core.Properties.Normalization.Existence
import LeanPRA.Metatheory.Core.Checker.HeadReduction
import LeanPRA.Metatheory.Core.Checker.HeadTrace
import LeanPRA.Metatheory.Core.Properties.Normalization.CanonicalForms

/-!
# Correctness of structural definitional equality

- `defEqTerm_sound` and `defEqPredicate_sound` derive typed conversion from successful comparison.
- `defEqTerm_complete` and `defEqPredicate_complete` give a sufficient comparison depth for equal
  inputs, using the existing syntactic normalization theorem.

Soundness follows the comparison calls and justifies each reduction batch by typed equality.
Completeness uses finite head-reduction traces for batches and induction on the common normal
form's size for recursive structural comparisons. Both results assume a valid environment;
soundness also assumes independently typed endpoints in a common context.
-/

namespace LeanPRA.Core

open Theory TermComparison

private theorem and_ok (a b : CheckResult Bool) :
    (do if ← a then b else .ok false) = .ok true ↔ a = .ok true ∧ b = .ok true := by
  cases a with
  | error e => simp
  | ok v => cases v <;> simp

private theorem unfold_by_weight_sound {order : Ordering}
    {openHead : α → CheckResult (Option β)} {a b : α} {x y : Option β}
    (run : unfoldByWeight order openHead a b = .ok (x, y)) :
    (x = none ∨ openHead a = .ok x) ∧ (y = none ∨ openHead b = .ok y) := by
  cases order <;> cases ha : openHead a <;> cases hb : openHead b <;>
    simp_all [unfoldByWeight, bind, Except.bind, pure, Except.pure] <;> grind

private theorem unfold_by_weight_progress {order : Ordering}
    {openHead : α → CheckResult (Option β)} {a b : α} {x y : Option β}
    (ha : openHead a = .ok x) (hb : openHead b = .ok y)
    (hleft : order = .gt → x ≠ none) (hright : order = .lt → y ≠ none) :
    ∃ u v, unfoldByWeight order openHead a b = .ok (u, v) ∧
      (u = none ∨ openHead a = .ok u) ∧ (v = none ∨ openHead b = .ok v) ∧
      ((u ≠ none ∨ v ≠ none) ↔ (x ≠ none ∨ y ≠ none)) := by
  cases order with
  | lt => exact ⟨none, y, by rw [unfoldByWeight, hb]; rfl, .inl rfl, .inr hb,
      by simp [hright rfl]⟩
  | eq => exact ⟨x, y, by simp [unfoldByWeight, ha, hb, bind, Except.bind]; rfl,
      .inr ha, .inr hb, Iff.rfl⟩
  | gt => exact ⟨x, none, by rw [unfoldByWeight, ha]; rfl, .inr ha, .inl rfl,
      by simp [hleft rfl]⟩

private theorem term_unfold_none {E : Environment} (a : Term)
    (h : unfoldTermHead E a = .ok none) : termHeadName a = none := by
  cases a with
  | app f a =>
    cases h' : unfoldTermHead E f with
    | error e => simp [unfoldTermHead, h', Except.map] at h
    | ok x =>
      cases x with
      | none => exact term_unfold_none f h'
      | some x => simp [unfoldTermHead, h', Except.map] at h
  | definition n args =>
    cases hd : E[n]? with
    | none => simp [unfoldTermHead, hd, referenceError, Environment.lookup, fail] at h
    | some d => cases d <;>
        simp [unfoldTermHead, hd, Reduced.beforeChange, referenceError, Environment.lookup,
          fail, pure, Except.pure] at h
  | _ => rfl

private theorem predicate_unfold_none {E : Environment} (a : Predicate)
    (h : unfoldPredicateHead E a = .ok none) : predicateHeadName a = none := by
  cases a with
  | app f a =>
    cases h' : unfoldPredicateHead E f with
    | error e => simp [unfoldPredicateHead, h', Except.map] at h
    | ok x =>
      cases x with
      | none => exact predicate_unfold_none f h'
      | some x => simp [unfoldPredicateHead, h', Except.map] at h
  | definition n fs ps =>
    cases hd : E[n]? with
    | none => simp [unfoldPredicateHead, hd, referenceError, Environment.lookup, fail] at h
    | some d => cases d <;>
        simp [unfoldPredicateHead, hd, referenceError, Environment.lookup, fail, pure, Except.pure] at h
  | _ => rfl

private theorem function_arguments_sound {E Ξ Γ} {compare : Arity → Term → Term → CheckResult Bool}
    (sound : ∀ {Γ a b k}, TermTyping E Ξ Γ a k → TermTyping E Ξ Γ b k →
      compare k a b = .ok true → TermEq E Ξ Γ a b k)
    {as bs ks} (left : FunctionArguments E Ξ Γ as ks)
    (right : FunctionArguments E Ξ Γ bs ks)
    (run : compareArguments compare ks as bs = .ok true) :
    FunctionArgumentEq E Ξ Γ as bs ks := by
  induction ks generalizing as bs with
  | nil => cases left; cases right; exact .nil
  | cons k ks ih =>
    cases left with
    | cons a as =>
      cases right with
      | cons b bs =>
        have h := (and_ok _ _).mp run
        exact .cons (sound a b h.1) (ih as bs h.2)

private def termTrial (term applications : Arity → Term → Term → CheckResult Bool)
    (E : Environment) (k : Arity) (a b : Term) : CheckResult Bool := do
  match a, b with
  | .app f a, .app g b =>
    if ← applications (k + 1) f g then term 0 a b else pure false
  | .primrec a s, .primrec b t =>
    if ← term 0 a b then term 2 s t else pure false
  | .definition f as, .definition g bs =>
    if f != g then return false
    match E.lookup f with
    | some (.function d) => compareArguments term d.functions as bs
    | _ => referenceError E f .function
  | _, _ => pure false

private theorem term_trial_sound {E Ξ}
    {term applications : Arity → Term → Term → CheckResult Bool}
    (termSound : ∀ {Γ a b k}, TermTyping E Ξ Γ a k → TermTyping E Ξ Γ b k →
      term k a b = .ok true → TermEq E Ξ Γ a b k)
    (applicationsSound : ∀ {Γ a b k}, TermTyping E Ξ Γ a k → TermTyping E Ξ Γ b k →
      applications k a b = .ok true → TermEq E Ξ Γ a b k)
    {Γ a b k} (left : TermTyping E Ξ Γ a k) (right : TermTyping E Ξ Γ b k)
    (run : termTrial term applications E k a b = .ok true) : TermEq E Ξ Γ a b k := by
  cases a <;> cases b <;>
    simp only [termTrial, and_ok, pure, Except.pure, Except.ok.injEq] at run <;>
    try contradiction
  case app.app f a g b =>
    exact .app (applicationsSound left.inv_app.1 right.inv_app.1 run.1)
      (termSound left.inv_app.2 right.inv_app.2 run.2)
  case primrec.primrec a s b t =>
    obtain ⟨rfl, ha, hs⟩ := left.inv_primrec
    obtain ⟨_, hb, ht⟩ := right.inv_primrec
    exact .primrec (termSound ha hb run.1) (termSound hs ht run.2)
  case definition.definition f as g bs =>
    by_cases h : f = g
    · subst g
      obtain ⟨d, lookup, ha, rfl⟩ := left.inv_definition
      obtain ⟨e, lookup', hb, _⟩ := right.inv_definition
      have : d = e := by simpa [lookup] using lookup'
      subst e
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        Environment.lookup, lookup] at run
      exact .definition lookup (function_arguments_sound termSound ha hb run)
    · simp [h] at run

private def termFallback (n : Nat) (E : Environment) (k : Arity) (a b : Term)
    (trial : CheckResult Bool) : CheckResult Bool := do
  if let .ok true := trial then return true
  match k with
  | j + 1 => defEqTerm n E j (.app a.shift (.bvar 0)) (.app b.shift (.bvar 0))
  | 0 =>
    let x ← exposeTerm (n + 1) false a
    let y ← exposeTerm (n + 1) false b
    if x.isSome || y.isSome then
      return ← defEqTerm n E 0 (x.getD a) (y.getD b)
    let (x, y) ← unfoldByWeight (termUnfoldingOrder E a b) (unfoldTermHead E ·) a b
    if x.isSome || y.isSome then
      return ← defEqTerm n E 0 (x.getD a) (y.getD b)
    match a, b with
    | .app (.primrec ..) _, .app (.primrec ..) _ =>
      let x ← exposeRecursor (n + 1) E a
      let y ← exposeRecursor (n + 1) E b
      if x.isSome || y.isSome then defEqTerm n E 0 (x.getD a) (y.getD b) else trial
    | .app (.primrec ..) _, _ =>
      let v ← whnfTerm (n + 1) E a
      if v == a then return ← trial
      defEqTerm n E 0 v b
    | _, .app (.primrec ..) _ =>
      let v ← whnfTerm (n + 1) E b
      if v == b then return ← trial
      defEqTerm n E 0 a v
    | _, _ => trial

private theorem term_fallback_sound {n E Ξ Γ a b k trial} (valid : EnvironmentWF E)
    (sound : ∀ {Γ a b k}, TermTyping E Ξ Γ a k → TermTyping E Ξ Γ b k →
      defEqTerm n E k a b = .ok true → TermEq E Ξ Γ a b k)
    (left : TermTyping E Ξ Γ a k) (right : TermTyping E Ξ Γ b k)
    (trialSound : trial = .ok true → TermEq E Ξ Γ a b k)
    (run : termFallback n E k a b trial = .ok true) : TermEq E Ξ Γ a b k := by
  simp only [termFallback] at run
  split at run
  next => exact trialSound rfl
  next =>
    cases k with
    | succ k =>
      exact .trans (.symm (.eta (binderName := .anonymous) left))
        (.trans (.lam (sound (.app (left.shift 0) (.bvar rfl))
          (.app (right.shift 0) (.bvar rfl)) run))
          (.eta (binderName := .anonymous) right))
    | zero =>
      simp only [CheckResult.bind_eq_ok] at run
      obtain ⟨x, hx, y, hy, run⟩ := run
      split at run
      next =>
        have ex := exposeTerm_sound left hx
        have ey := exposeTerm_sound right hy
        exact ex.trans ((sound ex.regularity.2 ey.regularity.2 run).trans ey.symm)
      next =>
        simp only [CheckResult.bind_eq_ok] at run
        obtain ⟨⟨x, y⟩, hu, run⟩ := run
        split at run
        next =>
          obtain ⟨hx, hy⟩ := unfold_by_weight_sound hu
          have ex : TermEq E Ξ Γ a (x.getD a) 0 := by
            rcases hx with rfl | hx
            · exact .refl left
            · exact unfoldTermHead_sound valid left hx
          have ey : TermEq E Ξ Γ b (y.getD b) 0 := by
            rcases hy with rfl | hy
            · exact .refl right
            · exact unfoldTermHead_sound valid right hy
          exact ex.trans ((sound ex.regularity.2 ey.regularity.2 run).trans ey.symm)
        next =>
          split at run
          next =>
            simp only [CheckResult.bind_eq_ok] at run
            obtain ⟨x, hx, y, hy, run⟩ := run
            cases x <;> cases y
            all_goals first
              | exact trialSound run
              | have ex := exposeRecursor_sound valid left hx
                have ey := exposeRecursor_sound valid right hy
                exact ex.trans ((sound ex.regularity.2 ey.regularity.2 run).trans ey.symm)
          next =>
            simp only [CheckResult.bind_eq_ok] at run
            obtain ⟨v, hv, run⟩ := run
            split at run
            next => exact trialSound run
            next =>
              have eq := whnfTerm_sound valid left hv
              exact eq.trans (sound eq.regularity.2 right run)
          next =>
            simp only [CheckResult.bind_eq_ok] at run
            obtain ⟨v, hv, run⟩ := run
            split at run
            next => exact trialSound run
            next =>
              have eq := whnfTerm_sound valid right hv
              exact (sound left eq.regularity.2 run).trans eq.symm
          next => exact trialSound run

private theorem term_sound (n : Nat) {E Ξ} (valid : EnvironmentWF E) :
    (∀ {Γ a b k}, TermTyping E Ξ Γ a k → TermTyping E Ξ Γ b k →
      defEqTerm n E k a b = .ok true → TermEq E Ξ Γ a b k) ∧
    (∀ {Γ a b k}, TermTyping E Ξ Γ a k → TermTyping E Ξ Γ b k →
      compareTermApplications n E k a b = .ok true → TermEq E Ξ Γ a b k) := by
  induction n with
  | zero =>
    constructor <;> intros <;> simp_all [defEqTerm, compareTermApplications, compareTerm, compareHead, exhausted, fail]
  | succ n ih =>
    constructor
    · intro Γ a b k left right run
      simp only [defEqTerm, compareTerm] at run
      split at run
      next h => have : a = b := eq_of_beq h; subst b; exact .refl left
      next =>
        split at run
        next =>
          have eq := eq_of_beq (Except.ok.inj run)
          cases eq; exact .refl left
        next =>
          have eq := eq_of_beq (Except.ok.inj run)
          cases eq; exact .refl left
        next hint a hint' b =>
          obtain ⟨j, rfl, ha⟩ := left.inv_lam
          obtain ⟨l, eq, hb⟩ := right.inv_lam
          have : j = l := Nat.succ.inj eq
          subst l
          exact .lam (ih.1 ha hb run)
        next a s b t =>
          obtain ⟨arity, ha, hs⟩ := left.inv_app.1.inv_primrec
          obtain ⟨_, hb, ht⟩ := right.inv_app.1.inv_primrec
          have hk : k = 0 := Nat.add_right_cancel arity
          subst k
          exact (TermEq.primrecZero ha hs).trans ((ih.1 ha hb run).trans
            (TermEq.primrecZero hb ht).symm)
        next =>
          exact term_fallback_sound valid ih.1 left right
            (term_trial_sound ih.1 ih.2 left right) run
    · intro Γ a b k left right run
      simp only [compareTermApplications, compareHead] at run
      split at run
      next h => have : a = b := eq_of_beq h; subst b; exact .refl left
      next =>
        split at run
        next =>
          have eq := eq_of_beq (Except.ok.inj run)
          cases eq; exact .refl left
        next =>
          have eq := eq_of_beq (Except.ok.inj run)
          cases eq; exact .refl left
        next => exact term_trial_sound ih.1 ih.2 left right run

/-- Successful numerical comparison gives typed equality at the supplied arity. -/
public theorem defEqTerm_sound {n E Ξ Γ a b k} (valid : EnvironmentWF E)
    (left : TermTyping E Ξ Γ a k) (right : TermTyping E Ξ Γ b k)
    (run : defEqTerm n E k a b = .ok true) : TermEq E Ξ Γ a b k :=
  (term_sound n valid).1 left right run

private theorem predicate_arguments_sound {E Ξ Γ}
    {compare : Arity → Predicate → Predicate → CheckResult Bool}
    (sound : ∀ {Γ a b σ}, PredicateTyping E Ξ Γ a σ → PredicateTyping E Ξ Γ b σ →
      compare σ.arity a b = .ok true → PredicateEq E Ξ Γ a b σ)
    {as bs ks} (left : PredicateArguments E Ξ Γ as ks)
    (right : PredicateArguments E Ξ Γ bs ks)
    (run : compareArguments (fun s => compare s.arity) ks as bs = .ok true) :
    PredicateArgumentEq E Ξ Γ as bs ks := by
  induction ks generalizing as bs with
  | nil => cases left; cases right; exact .nil
  | cons k ks ih =>
    cases left with
    | cons a as =>
      cases right with
      | cons b bs =>
        have h := (and_ok _ _).mp run
        exact .cons (sound a b h.1) (ih as bs h.2)

private def predicateTrial (term : Arity → Term → Term → CheckResult Bool)
    (predicate applications : Arity → Predicate → Predicate → CheckResult Bool)
    (E : Environment) (k : Arity) (a b : Predicate) : CheckResult Bool := do
  match a, b with
  | .app f a, .app g b =>
    if ← applications (k + 1) f g then term 0 a b else pure false
  | .definition f fs ps, .definition g gs qs =>
    if f != g then return false
    match E.lookup f with
    | some (.predicate d) =>
      if ← compareArguments term d.functions fs gs then
        compareArguments (fun s => predicate s.arity) d.predicates ps qs
      else pure false
    | _ => referenceError E f .predicate
  | _, _ => pure false

private theorem predicate_trial_sound {E Ξ}
    {term : Arity → Term → Term → CheckResult Bool}
    {predicate applications : Arity → Predicate → Predicate → CheckResult Bool}
    (termSound : ∀ {Γ a b k}, TermTyping E Ξ Γ a k → TermTyping E Ξ Γ b k →
      term k a b = .ok true → TermEq E Ξ Γ a b k)
    (predicateSound : ∀ {Γ a b σ}, PredicateTyping E Ξ Γ a σ → PredicateTyping E Ξ Γ b σ →
      predicate σ.arity a b = .ok true → PredicateEq E Ξ Γ a b σ)
    (applicationsSound : ∀ {Γ a b σ}, PredicateTyping E Ξ Γ a σ → PredicateTyping E Ξ Γ b σ →
      applications σ.arity a b = .ok true → PredicateEq E Ξ Γ a b σ)
    {Γ a b k s} (left : PredicateTyping E Ξ Γ a ⟨k, s⟩)
    (right : PredicateTyping E Ξ Γ b ⟨k, s⟩)
    (run : predicateTrial term predicate applications E k a b = .ok true) :
    PredicateEq E Ξ Γ a b ⟨k, s⟩ := by
  cases a <;> cases b <;>
    simp only [predicateTrial, and_ok, pure, Except.pure, Except.ok.injEq] at run <;>
    try contradiction
  case app.app f a g b =>
    exact .app (applicationsSound left.app_function.1 right.app_function.1 run.1)
      (termSound left.app_function.2 right.app_function.2 run.2)
  case definition.definition f fs ps g gs qs =>
    by_cases h : f = g
    · subst g
      obtain ⟨d, lookup, hfs, hps, _⟩ := left.inv_definition
      obtain ⟨e, lookup', hgs, hqs, _⟩ := right.inv_definition
      have : d = e := by simpa [lookup] using lookup'
      subst e
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        Environment.lookup, lookup, and_ok] at run
      exact .definition lookup (function_arguments_sound termSound hfs hgs run.1)
        (predicate_arguments_sound predicateSound hps hqs run.2) left right
    · simp [h] at run

private def predicateFallback (n : Nat) (E : Environment) (k : Arity) (a b : Predicate)
    (trial : CheckResult Bool) : CheckResult Bool := do
  if let .ok true := trial then return true
  match k with
  | j + 1 => defEqPredicate n E j (.app a.shift (.bvar 0)) (.app b.shift (.bvar 0))
  | 0 =>
    let x ← exposePredicate (n + 1) false a
    let y ← exposePredicate (n + 1) false b
    if x.isSome || y.isSome then
      return ← defEqPredicate n E 0 (x.getD a) (y.getD b)
    let (x, y) ← unfoldByWeight (predicateUnfoldingOrder E a b) (unfoldPredicateHead E) a b
    match x, y with
    | none, none => trial
    | _, _ => defEqPredicate n E 0 (x.getD a) (y.getD b)

private theorem predicate_fallback_sound {n E Ξ Γ a b k s trial} (valid : EnvironmentWF E)
    (sound : ∀ {Γ a b σ}, PredicateTyping E Ξ Γ a σ → PredicateTyping E Ξ Γ b σ →
      defEqPredicate n E σ.arity a b = .ok true → PredicateEq E Ξ Γ a b σ)
    (left : PredicateTyping E Ξ Γ a ⟨k, s⟩) (right : PredicateTyping E Ξ Γ b ⟨k, s⟩)
    (trialSound : trial = .ok true → PredicateEq E Ξ Γ a b ⟨k, s⟩)
    (run : predicateFallback n E k a b trial = .ok true) :
    PredicateEq E Ξ Γ a b ⟨k, s⟩ := by
  simp only [predicateFallback] at run
  split at run
  next => exact trialSound rfl
  next =>
    cases k with
    | succ k =>
      exact .trans (.symm (.eta (binderName := .anonymous) left))
        (.trans (.lam (sound (.app (left.shift valid 0) (.bvar rfl))
          (.app (right.shift valid 0) (.bvar rfl)) run))
          (.eta (binderName := .anonymous) right))
    | zero =>
      simp only [CheckResult.bind_eq_ok] at run
      obtain ⟨x, hx, y, hy, run⟩ := run
      split at run
      next =>
        have ex := exposePredicate_sound valid left hx
        have ey := exposePredicate_sound valid right hy
        exact ex.trans ((sound (ex.regularity valid).2 (ey.regularity valid).2 run).trans ey.symm)
      next =>
        simp only [CheckResult.bind_eq_ok] at run
        obtain ⟨⟨x, y⟩, hu, run⟩ := run
        obtain ⟨hx, hy⟩ := unfold_by_weight_sound hu
        have ex : PredicateEq E Ξ Γ a (x.getD a) ⟨0, s⟩ := by
          rcases hx with rfl | hx
          · exact .refl left
          · exact unfoldPredicateHead_sound valid left hx
        have ey : PredicateEq E Ξ Γ b (y.getD b) ⟨0, s⟩ := by
          rcases hy with rfl | hy
          · exact .refl right
          · exact unfoldPredicateHead_sound valid right hy
        cases x <;> cases y
        all_goals first
          | exact trialSound run
          | exact ex.trans
              ((sound (ex.regularity valid).2 (ey.regularity valid).2 run).trans ey.symm)

private theorem predicate_sound (n : Nat) {E Ξ} (valid : EnvironmentWF E) :
    (∀ {Γ a b σ}, PredicateTyping E Ξ Γ a σ → PredicateTyping E Ξ Γ b σ →
      defEqPredicate n E σ.arity a b = .ok true → PredicateEq E Ξ Γ a b σ) ∧
    (∀ {Γ a b σ}, PredicateTyping E Ξ Γ a σ → PredicateTyping E Ξ Γ b σ →
      comparePredicateApplications n E σ.arity a b = .ok true → PredicateEq E Ξ Γ a b σ) := by
  induction n with
  | zero =>
    constructor <;> intros <;>
      simp_all [defEqPredicate, comparePredicateApplications, exhausted, fail]
  | succ n ih =>
    have trial := @predicate_trial_sound E Ξ _ _ _
      (fun {_ _ _ _} => defEqTerm_sound (n := n) valid) ih.1 ih.2
    constructor
    · intro Γ a b σ left right run
      obtain ⟨k, s⟩ := σ
      simp only [defEqPredicate] at run
      split at run
      next h => have : a = b := eq_of_beq h; subst b; exact .refl left
      next =>
        split at run
        next =>
          have eq := eq_of_beq (Except.ok.inj run)
          cases eq; exact .refl left
        next =>
          cases k with
          | zero => cases (show false = true from Except.ok.inj run)
          | succ k => exact .lam (ih.1 left.lam_body right.lam_body run)
        next =>
          have run := (and_ok _ _).mp run
          obtain ⟨ha, hb, sub⟩ := left.inv_equal
          obtain ⟨hc, hd, _⟩ := right.inv_equal
          exact .subsumption (.equal (defEqTerm_sound valid ha hc run.1)
            (defEqTerm_sound valid hb hd run.2)) sub
        next =>
          have run := (and_ok _ _).mp run
          obtain ⟨r, ha, hb, sub⟩ := left.inv_imp
          obtain ⟨t, hc, hd, sub'⟩ := right.inv_imp
          have hk : 0 = k := sub.arity_eq
          subst k
          exact .imp (ih.1 (.subsumption ha sub) (.subsumption hc sub') run.1)
            (ih.1 (.subsumption hb sub) (.subsumption hd sub') run.2)
        next =>
          have run := (and_ok _ _).mp run
          obtain ⟨r, ha, hb, sub⟩ := left.inv_and
          obtain ⟨t, hc, hd, sub'⟩ := right.inv_and
          have hk : 0 = k := sub.arity_eq
          subst k
          exact .and (ih.1 (.subsumption ha sub) (.subsumption hc sub') run.1)
            (ih.1 (.subsumption hb sub) (.subsumption hd sub') run.2)
        next =>
          have run := (and_ok _ _).mp run
          obtain ⟨r, ha, hb, sub⟩ := left.inv_or
          obtain ⟨t, hc, hd, sub'⟩ := right.inv_or
          have hk : 0 = k := sub.arity_eq
          subst k
          exact .or (ih.1 (.subsumption ha sub) (.subsumption hc sub') run.1)
            (ih.1 (.subsumption hb sub) (.subsumption hd sub') run.2)
        next =>
          obtain ⟨sig, ha⟩ := left.inv_all
          cases sig
          exact .all (ih.1 ha right.inv_all.2 run)
        next =>
          obtain ⟨sig, ha⟩ := left.inv_ex
          cases sig
          exact .ex (ih.1 ha right.inv_ex.2 run)
        next => exact predicate_fallback_sound valid ih.1 left right (trial left right) run
    · intro Γ a b σ left right run
      obtain ⟨k, s⟩ := σ
      simp only [comparePredicateApplications] at run
      split at run
      next h => have : a = b := eq_of_beq h; subst b; exact .refl left
      next =>
        split at run
        next =>
          have eq := eq_of_beq (Except.ok.inj run)
          cases eq; exact .refl left
        next => exact trial left right run
        next => exact trial left right run
        next => cases (show false = true from Except.ok.inj run)

/-- Successful predicate comparison gives equality at the endpoints' full common signature. -/
public theorem defEqPredicate_sound {n E Ξ Γ a b σ} (valid : EnvironmentWF E)
    (left : PredicateTyping E Ξ Γ a σ) (right : PredicateTyping E Ξ Γ b σ)
    (run : defEqPredicate n E σ.arity a b = .ok true) : PredicateEq E Ξ Γ a b σ :=
  (predicate_sound n valid).1 left right run

private theorem eventually_succ {p : Nat → Prop} (h : Eventually p) :
    Eventually (fun n => p (n + 1)) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun m hm => hn (m + 1) (by omega)⟩

private theorem HeadBatch.progress {step : α → CheckResult (Option α)} {a b x y}
    (left : HeadBatch step false a x) (right : HeadBatch step false b y)
    (moves : x ≠ Option.none ∨ y ≠ Option.none) :
    ∃ i j, HeadSteps step i a (x.getD a) ∧ HeadSteps step j b (y.getD b) ∧ 0 < i + j := by
  cases left with
  | none =>
    cases right with
    | none => simp at moves
    | some steps pos => exact ⟨0, _, .refl, steps, by have := pos rfl; omega⟩
  | some steps pos =>
    obtain ⟨j, rest⟩ := right.steps
    exact ⟨_, j, steps, rest, by have := pos rfl; omega⟩

private theorem HeadSteps.positive_of_ne {step : α → CheckResult (Option α)} {n a b}
    (steps : HeadSteps step n a b) (ne : a ≠ b) : 0 < n := by
  cases n with
  | zero => cases steps; contradiction
  | succ => omega

private theorem term_batches_complete {n m E Ξ Γ a b x y}
    (left : TermTyping E Ξ Γ a 0) (right : TermTyping E Ξ Γ b 0)
    (hx : exposeTerm n false a = .ok x) (hy : exposeTerm m false b = .ok y)
    (moves : x ≠ none ∨ y ≠ none)
    (next : ∀ {i j u v}, HeadSteps (termStep E) i a u → HeadSteps (termStep E) j b v →
      0 < i + j → TermTyping E Ξ Γ u 0 → TermTyping E Ξ Γ v 0 →
      Eventually (fun n => defEqTerm n E 0 u v = .ok true)) :
    Eventually (fun n => defEqTerm n E 0 (x.getD a) (y.getD b) = .ok true) := by
  obtain ⟨i, j, si, sj, pos⟩ := HeadBatch.progress
    (exposeTerm_batch hx) (exposeTerm_batch hy) moves
  exact next si sj pos (exposeTerm_sound left hx).regularity.2
    (exposeTerm_sound right hy).regularity.2

private theorem term_unfoldings_complete {E Ξ Γ a b x y} (valid : EnvironmentWF E)
    (left : TermTyping E Ξ Γ a 0) (right : TermTyping E Ξ Γ b 0)
    (hx : x = none ∨ unfoldTermHead E a = .ok x)
    (hy : y = none ∨ unfoldTermHead E b = .ok y)
    (moves : x ≠ none ∨ y ≠ none)
    (next : ∀ {i j u v}, HeadSteps (termStep E) i a u → HeadSteps (termStep E) j b v →
      0 < i + j → TermTyping E Ξ Γ u 0 → TermTyping E Ξ Γ v 0 →
      Eventually (fun n => defEqTerm n E 0 u v = .ok true)) :
    Eventually (fun n => defEqTerm n E 0 (x.getD a) (y.getD b) = .ok true) := by
  have batch {t out} (run : out = none ∨ unfoldTermHead E t = .ok out) :
      HeadBatch (termStep E) false t out := by
    cases out with
    | none => exact .none
    | some out =>
      exact .some (.next (unfoldTermHead_step (run.resolve_left (by simp))) .refl) (by omega)
  obtain ⟨i, j, si, sj, pos⟩ := HeadBatch.progress (batch hx) (batch hy) moves
  apply next si sj pos
  · rcases hx with rfl | hx
    · exact left
    · exact (unfoldTermHead_sound valid left hx).regularity.2
  · rcases hy with rfl | hy
    · exact right
    · exact (unfoldTermHead_sound valid right hy).regularity.2

private def termCompute (n : Nat) (E : Environment) (a b : Term)
    (trial : CheckResult Bool) : CheckResult Bool := do
  match a, b with
  | .app (.primrec ..) _, .app (.primrec ..) _ =>
    let x ← exposeRecursor (n + 1) E a
    let y ← exposeRecursor (n + 1) E b
    if x.isSome || y.isSome then defEqTerm n E 0 (x.getD a) (y.getD b) else trial
  | .app (.primrec ..) _, _ =>
    let v ← whnfTerm (n + 1) E a
    if v == a then return ← trial
    defEqTerm n E 0 v b
  | _, .app (.primrec ..) _ =>
    let v ← whnfTerm (n + 1) E b
    if v == b then return ← trial
    defEqTerm n E 0 a v
  | _, _ => trial

private theorem term_compute_complete {E Ξ Γ a b} (valid : EnvironmentWF E)
    (left : TermTyping E Ξ Γ a 0) (right : TermTyping E Ξ Γ b 0)
    (readyA : (∀ c s t, a ≠ .app (.primrec c s) t) → termStep E a = .ok none)
    (readyB : (∀ c s t, b ≠ .app (.primrec c s) t) → termStep E b = .ok none)
    (moving : ¬(termStep E a = .ok none ∧ termStep E b = .ok none))
    (next : ∀ {i j u v}, HeadSteps (termStep E) i a u → HeadSteps (termStep E) j b v →
      0 < i + j → TermTyping E Ξ Γ u 0 → TermTyping E Ξ Γ v 0 →
      Eventually (fun n => defEqTerm n E 0 u v = .ok true))
    (trial : Nat → CheckResult Bool) :
    Eventually (fun n => termCompute n E a b (trial n) = .ok true) := by
  by_cases ra : ∃ c s t, a = .app (.primrec c s) t
  · obtain ⟨c, s, t, rfl⟩ := ra
    by_cases rb : ∃ d r u, b = .app (.primrec d r) u
    · obtain ⟨d, r, u, rfl⟩ := rb
      obtain ⟨i, A, hA⟩ := whnfTerm_terminates valid left
      obtain ⟨j, B, hB⟩ := whnfTerm_terminates valid right
      obtain ⟨x, ix, hx⟩ := exposeRecursor_terminates (hA i (by omega))
      obtain ⟨y, iy, hy⟩ := exposeRecursor_terminates (hB j (by omega))
      have moves : x ≠ none ∨ y ≠ none := by
        apply Classical.byContradiction
        intro h
        have hx0 : x = none := Classical.byContradiction (fun hn => h (.inl hn))
        have hy0 : y = none := Classical.byContradiction (fun hn => h (.inr hn))
        subst x; subst y
        exact moving ⟨exposeRecursor_none (hx ix (by omega)),
          exposeRecursor_none (hy iy (by omega))⟩
      obtain ⟨i, j, si, sj, pos⟩ := HeadBatch.progress
        (exposeRecursor_batch (hx ix (by omega)))
        (exposeRecursor_batch (hy iy (by omega))) moves
      have tail := next si sj pos
        (exposeRecursor_sound valid left (hx ix (by omega))).regularity.2
        (exposeRecursor_sound valid right (hy iy (by omega))).regularity.2
      refine eventually_mono ?_ (eventually_and (eventually_succ ⟨ix, hx⟩)
        (eventually_and (eventually_succ ⟨iy, hy⟩) tail))
      intro n h
      simp only [termCompute, h.1, h.2.1, bind, Except.bind]
      cases x <;> cases y <;> first | exact h.2.2 | simp at moves
    · have notRec : ∀ d r u, b ≠ .app (.primrec d r) u := fun d r u h => rb ⟨d, r, u, h⟩
      obtain ⟨i, v, hv⟩ := whnfTerm_terminates valid left
      have ne : v ≠ .app (.primrec c s) t := by
        intro eq
        apply moving
        exact ⟨eq ▸ term_stationary (whnfTerm_normal (hv i (by omega))), readyB notRec⟩
      obtain ⟨j, steps⟩ := (whnfTerm_trace (hv i (by omega))).steps
      have tail := next steps (.refl (a := b))
        (by have := steps.positive_of_ne (Ne.symm ne); omega)
        (whnfTerm_sound valid left (hv i (by omega))).regularity.2 right
      refine eventually_mono ?_ (eventually_and (eventually_succ ⟨i, hv⟩) tail)
      intro n h
      cases b <;> try {rename_i f a; cases f}
      all_goals simp only [termCompute, h.1, bind, Except.bind]
      all_goals first
        | exact False.elim (notRec _ _ _ rfl)
        | simpa only [beq_eq_false_iff_ne.mpr ne, Bool.false_eq_true, ↓reduceIte] using h.2
  · have notRecA : ∀ c s t, a ≠ .app (.primrec c s) t := fun c s t h => ra ⟨c, s, t, h⟩
    by_cases rb : ∃ d r u, b = .app (.primrec d r) u
    · obtain ⟨d, r, u, rfl⟩ := rb
      obtain ⟨i, v, hv⟩ := whnfTerm_terminates valid right
      have ne : v ≠ .app (.primrec d r) u := by
        intro eq
        apply moving
        exact ⟨readyA notRecA, eq ▸ term_stationary (whnfTerm_normal (hv i (by omega)))⟩
      obtain ⟨j, steps⟩ := (whnfTerm_trace (hv i (by omega))).steps
      have tail := next (.refl (a := a)) steps
        (by have := steps.positive_of_ne (Ne.symm ne); omega) left
        (whnfTerm_sound valid right (hv i (by omega))).regularity.2
      refine eventually_mono ?_ (eventually_and (eventually_succ ⟨i, hv⟩) tail)
      intro n h
      cases a <;> try {rename_i f a; cases f}
      all_goals simp only [termCompute, h.1, bind, Except.bind]
      all_goals first
        | exact False.elim (notRecA _ _ _ rfl)
        | simpa only [beq_eq_false_iff_ne.mpr ne, Bool.false_eq_true, ↓reduceIte] using h.2
    · exact False.elim (moving ⟨readyA notRecA, readyB (fun d r u h => rb ⟨d, r, u, h⟩)⟩)

private theorem term_fallback_complete {E Ξ Γ a b} (valid : EnvironmentWF E)
    (left : TermTyping E Ξ Γ a 0) (right : TermTyping E Ξ Γ b 0)
    (moving : ¬(termStep E a = .ok none ∧ termStep E b = .ok none))
    (next : ∀ {i j u v}, HeadSteps (termStep E) i a u → HeadSteps (termStep E) j b v →
      0 < i + j → TermTyping E Ξ Γ u 0 → TermTyping E Ξ Γ v 0 →
      Eventually (fun n => defEqTerm n E 0 u v = .ok true))
    (trial : Nat → CheckResult Bool) :
    Eventually (fun n => termFallback n E 0 a b (trial n) = .ok true) := by
  obtain ⟨i, A, hA⟩ := whnfTerm_terminates valid left
  obtain ⟨j, B, hB⟩ := whnfTerm_terminates valid right
  obtain ⟨x, ix, hx⟩ := exposeTerm_terminates (hA i (by omega)) false
  obtain ⟨y, iy, hy⟩ := exposeTerm_terminates (hB j (by omega)) false
  by_cases moves : x ≠ none ∨ y ≠ none
  · have tail := term_batches_complete left right (hx ix (by omega)) (hy iy (by omega))
      moves next
    refine eventually_mono ?_ (eventually_and (eventually_succ ⟨ix, hx⟩)
      (eventually_and (eventually_succ ⟨iy, hy⟩) tail))
    intro n h
    simp only [termFallback]
    split
    next => rfl
    next =>
      simp only [h.1, h.2.1, bind, Except.bind]
      cases x <;> cases y <;> first | exact h.2.2 | simp at moves
  · have hx0 : x = none := Classical.byContradiction (fun h => moves (.inl h))
    have hy0 : y = none := Classical.byContradiction (fun h => moves (.inr h))
    subst x; subst y
    obtain ⟨x, ux⟩ := unfoldTermHead_terminates left
    obtain ⟨y, uy⟩ := unfoldTermHead_terminates right
    obtain ⟨u, v, scheduled, hu, hv, progress⟩ := unfold_by_weight_progress
      (openHead := fun t => unfoldTermHead E t) (a := a) (b := b) ux uy
      (order := termUnfoldingOrder E a b)
      (by intro ord eq; subst x; simp [termUnfoldingOrder, term_unfold_none a ux, compareHeadWeights]
          at ord)
      (by
        intro ord eq; subst y
        cases ha : termHeadName a <;>
          simp [termUnfoldingOrder, ha, term_unfold_none b uy, compareHeadWeights] at ord)
    by_cases moves : x ≠ none ∨ y ≠ none
    · have moved := progress.mpr moves
      have tail := term_unfoldings_complete valid left right hu hv moved next
      refine eventually_mono ?_ (eventually_and (eventually_succ ⟨ix, hx⟩)
        (eventually_and (eventually_succ ⟨iy, hy⟩) tail))
      intro n h
      simp only [termFallback]
      split
      next => rfl
      next =>
        simp only [h.1, h.2.1, scheduled, bind, Except.bind, Option.isSome_none,
          Bool.or_false, Bool.false_eq_true, ↓reduceIte]
        cases u <;> cases v <;> first | exact h.2.2 | simp at moved
    · have hx0 : x = none := Classical.byContradiction (fun h => moves (.inl h))
      have hy0 : y = none := Classical.byContradiction (fun h => moves (.inr h))
      subst x; subst y
      have noMove : u = none ∧ v = none := by simpa using progress
      obtain ⟨rfl, rfl⟩ := noMove
      have tail := term_compute_complete valid left right
        (term_ready left (hx ix (by omega)) ux) (term_ready right (hy iy (by omega)) uy)
        moving next trial
      refine eventually_mono ?_ (eventually_and (eventually_succ ⟨ix, hx⟩)
        (eventually_and (eventually_succ ⟨iy, hy⟩) tail))
      intro n h
      simp only [termFallback]
      split
      next => rfl
      next =>
        simpa only [termCompute, h.1, h.2.1, scheduled, bind, Except.bind, Option.isSome_none,
          Bool.or_false, Bool.false_eq_true, ↓reduceIte] using h.2.2

private theorem term_trace_complete {E Ξ Γ a b A B} (valid : EnvironmentWF E)
    (left : TermTyping E Ξ Γ a 0) (right : TermTyping E Ξ Γ b 0)
    (ta : HeadTrace (termStep E) a A) (tb : HeadTrace (termStep E) b B)
    (tail : Eventually (fun n => defEqTerm n E 0 A B = .ok true)) :
    Eventually (fun n => defEqTerm n E 0 a b = .ok true) := by
  apply HeadTrace.induction_pair (P := fun a b => TermTyping E Ξ Γ a 0 →
    TermTyping E Ξ Γ b 0 → Eventually (fun n => defEqTerm n E 0 a b = .ok true))
    (a := a) (b := b) (A := A) (B := B) ?_ ta tb left right
  intro a b ta tb next left right
  by_cases stopped : termStep E a = .ok none ∧ termStep E b = .ok none
  · rw [ta.stationary stopped.1, tb.stationary stopped.2]
    exact tail
  · have fallback := term_fallback_complete valid left right stopped next
      (fun n => termTrial (defEqTerm n E) (compareTermApplications n E) E 0 a b)
    by_cases zeros : ∃ c s d r, a = .app (.primrec c s) .zero ∧ b = .app (.primrec d r) .zero
    · obtain ⟨c, s, d, r, rfl, rfl⟩ := zeros
      have rest := next (.next rfl .refl) (.next rfl .refl) (by omega)
        left.inv_app.1.inv_primrec.2.1 right.inv_app.1.inv_primrec.2.1
      refine eventually_next ?_ (rest)
      intro n h
      simp only [defEqTerm, compareTerm]
      split
      next => rfl
      next => exact h
    · refine eventually_next ?_ (fallback)
      intro n h
      simp only [defEqTerm, compareTerm]
      split
      next => rfl
      next =>
        split
        next => exact False.elim (stopped ⟨rfl, rfl⟩)
        next => exact False.elim (stopped ⟨rfl, rfl⟩)
        next => obtain ⟨k, hk, _⟩ := left.inv_lam; exact Nat.noConfusion hk.symm
        next => exact False.elim (zeros ⟨_, _, _, _, rfl, rfl⟩)
        next => exact h

private def termOrigin : Term → Term
  | .app f _ => termOrigin f
  | .lam _ body => (termOrigin body).rename (fun i => i - 1)
  | t => t

private theorem term_origin_shift {t} (head : TermApplications t) :
    (termOrigin t.shift).rename (fun i => i - 1) = termOrigin t := by
  induction head with
  | app f ih => simpa only [Term.shift, Term.rename, termOrigin] using ih
  | _ => simp [termOrigin, Term.shift, Term.rename]

private theorem term_origin_normal (n : Nat) :
    (∀ {E k a N}, TermApplications a → reduceTerm n E k a = .ok N →
      termOrigin N = termOrigin a) ∧
    (∀ {E a N}, TermApplications a → reduceTermNeutral n E a = .ok N →
      termOrigin N = termOrigin a) := by
  induction n with
  | zero => constructor <;> intros <;>
      simp_all [reduceTerm, reduceTermNeutral, exhausted, fail]
  | succ n ih =>
    constructor
    · intro E k a N head run
      cases k with
      | succ k =>
        simp only [reduceTerm, CheckResult.bind_eq_ok, pure, Except.pure,
          Except.ok.injEq] at run
        obtain ⟨body, hb, rfl⟩ := run
        have shifted : TermApplications a.shift := head.rename _
        have eq := ih.1 (.app shifted) hb
        simp only [termOrigin] at eq ⊢
        rw [eq, term_origin_shift head]
      | zero =>
        simp only [reduceTerm, CheckResult.bind_eq_ok] at run
        obtain ⟨w, hw, run⟩ := run
        have eq := whnfTerm_fixed head.whnf hw
        subst w
        cases head with
        | bvar | parameter =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst N; rfl
        | succ => simp [fail] at run
        | app hf =>
          have finish {f a : Term} (hf : TermApplications f)
              (run : (do
                let g ← reduceTermNeutral n E f
                let b ← reduceTerm n E 0 a
                pure (Term.app g b)) = .ok N) : termOrigin N = termOrigin (.app f a) := by
            simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
            obtain ⟨g, hg, b, hb, rfl⟩ := run
            simpa only [termOrigin] using ih.2 hf hg
          cases hf <;> exact finish (by constructor <;> assumption) run
    · intro E a N head run
      simp only [reduceTermNeutral, CheckResult.bind_eq_ok] at run
      obtain ⟨w, hw, run⟩ := run
      have eq := whnfTerm_fixed head.whnf hw
      subst w
      cases head with
      | bvar | parameter | succ =>
        simp only [pure, Except.pure, Except.ok.injEq] at run
        subst N; rfl
      | app hf =>
        simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
        obtain ⟨g, hg, b, hb, rfl⟩ := run
        simpa only [termOrigin] using ih.2 hf hg

private theorem term_lam_normal {E Ξ Γ n k name body N} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ (.lam name body) (k + 1))
    (run : reduceTerm n E (k + 1) (.lam name body) = .ok (.lam .anonymous N)) :
    ∃ m, reduceTerm m E k body = .ok N := by
  obtain ⟨j, hj, ht⟩ := typed.inv_lam
  have eq : j = k := Nat.succ.inj hj.symm
  subst j
  cases n with
  | zero => simp [reduceTerm, exhausted, fail] at run
  | succ n =>
    simp only [reduceTerm, CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq,
      Term.lam.injEq, true_and] at run
    obtain ⟨B, hB, rfl⟩ := run
    obtain ⟨m, C, hC⟩ := reduceTerm_terminates valid ht
    have shifted : TermTyping E Ξ (0 :: 0 :: Γ)
        (body.rename (Renaming.lift 1 (fun i => i + 1))) k :=
      TermTyping.rename ht _ (RenamingTyping.lift (by intro i a h; simpa using h) 0)
    have beta := TermEq.beta (binderName := name) shifted (TermTyping.bvar (i := 0) rfl)
    simp only [Term.shift, Term.rename, Nat.not_lt_zero, ↓reduceIte] at beta hB
    rw [term_cancel] at beta
    have same := reduceTerm_congr valid beta hB (hC m (by omega))
    exact ⟨m, same ▸ hC m (by omega)⟩

private theorem term_applications_refl {E k a} :
    Eventually (fun m => compareTermApplications m E k a a = .ok true) := by
  refine ⟨1, ?_⟩
  intro m hm
  cases m with
  | zero => omega
  | succ m => simp [compareTermApplications, compareHead, answer, pure, Except.pure]

private theorem term_refl {E k a} :
    Eventually (fun m => defEqTerm m E k a a = .ok true) := by
  refine ⟨1, ?_⟩
  intro m hm
  cases m with
  | zero => omega
  | succ m => simp [defEqTerm, compareTerm, answer, pure, Except.pure]

private theorem term_applications_app {n E k f a g b}
    (run : compareTermApplications n E (k + 1) f g = .ok true ∧
      defEqTerm n E 0 a b = .ok true) :
    compareTermApplications (n + 1) E k (.app f a) (.app g b) = .ok true := by
  simp only [compareTermApplications, compareHead]
  split
  next => rfl
  next => simpa only [compareChildren, answer, both, pure, Except.pure, and_ok] using run

private theorem term_app_whnf {f a} (h : TermWhnf (.app f a)) : TermWhnf f := by
  cases h with
  | app hf _ _ => exact hf
  | primrec => exact .recursor

private theorem term_app_complete {n E k f a g b}
    (head : TermWhnf (.app f a))
    (run : compareTermApplications n E (k + 1) f g = .ok true ∧
      defEqTerm n E 0 a b = .ok true) :
    defEqTerm (n + 1) E k (.app f a) (.app g b) = .ok true := by
  have notZero : ∀ c s, f ≠ .primrec c s ∨ a ≠ .zero := by
    intro c s
    cases head with
    | app _ _ notRec => exact .inl (notRec c s)
    | primrec _ blocked => exact .inr blocked.1
  have start : (match (.app f a : Term), (.app g b : Term) with
      | .bvar i, .bvar j | .parameter i, .parameter j => pure (i == j)
      | .lam _ c, .lam _ d =>
        match k with
        | j + 1 => defEqTerm n E j c d
        | 0 => pure false
      | .app (.primrec c _) .zero, .app (.primrec d _) .zero => defEqTerm n E 0 c d
      | _, _ => termFallback n E k (.app f a) (.app g b)
          (termTrial (defEqTerm n E) (compareTermApplications n E) E k (.app f a) (.app g b)))
      = .ok true := by
    cases f <;> cases a
    all_goals first
      | exact False.elim ((notZero _ _).elim (fun h => h rfl) (fun h => h rfl))
      | change termFallback n E k _ _ _ = .ok true
        simp only [termTrial, run.1, run.2, bind, Except.bind, ↓reduceIte, termFallback]
        rfl
  simp only [defEqTerm, compareTerm]
  split
  next => rfl
  next => exact start

private theorem term_rec_complete {n E a s b r}
    (run : defEqTerm n E 0 a b = .ok true ∧ defEqTerm n E 2 s r = .ok true) :
    compareTermApplications (n + 1) E 1 (.primrec a s) (.primrec b r) = .ok true := by
  simp only [compareTermApplications, compareHead]
  split
  next => rfl
  next => simpa only [compareChildren, answer, both, pure, Except.pure, and_ok] using run

private theorem neutral_not_rec {n E t b s}
    (h : reduceTermNeutral n E t = .ok (.primrec b s)) : False := by
  cases reduceTermNeutral_normal h

set_option maxHeartbeats 2000000 in
private theorem term_normal_complete (N : Term) {E} (valid : EnvironmentWF E) :
    (∀ {Ξ Γ k a b n m}, TermTyping E Ξ Γ a k → TermTyping E Ξ Γ b k →
      reduceTerm n E k a = .ok N → reduceTerm m E k b = .ok N →
      Eventually (fun d => defEqTerm d E k a b = .ok true)) ∧
    (∀ {Ξ Γ k a b n m}, TermTyping E Ξ Γ a k → TermTyping E Ξ Γ b k →
      TermWhnf a → TermWhnf b → reduceTermNeutral n E a = .ok N →
      reduceTermNeutral m E b = .ok N →
      Eventually (fun d => compareTermApplications d E k a b = .ok true)) := by
  generalize hN : sizeOf N = q
  induction q using Nat.strongRecOn generalizing N with
  | ind q previous =>
    have ih (T : Term) (lt : sizeOf T < sizeOf N) :=
      previous (sizeOf T) (by omega) T rfl
    constructor
    · intro Ξ Γ k a b n m left right ra rb
      cases n with
      | zero => simp [reduceTerm, exhausted, fail] at ra
      | succ n =>
        cases m with
        | zero => simp [reduceTerm, exhausted, fail] at rb
        | succ m =>
          have ha := ra
          have hb := rb
          cases k with
          | succ k =>
            simp only [reduceTerm, CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq] at ha hb
            obtain ⟨A, ha, rfl⟩ := ha
            obtain ⟨B, hb, eq⟩ := hb
            cases eq
            by_cases lams : ∃ name body name' body',
                a = .lam name body ∧ b = .lam name' body'
            · obtain ⟨name, body, name', body', rfl, rfl⟩ := lams
              obtain ⟨i, hi⟩ := term_lam_normal valid left ra
              obtain ⟨j, hj⟩ := term_lam_normal valid right rb
              obtain ⟨l, hl, tl⟩ := left.inv_lam
              obtain ⟨r, hr, tr⟩ := right.inv_lam
              have el : l = k := Nat.succ.inj hl.symm
              have er : r = k := Nat.succ.inj hr.symm
              subst l; subst r
              have rest := (ih A (by simp +arith)).1 tl tr hi hj
              refine eventually_next ?_ (rest)
              intro d h
              simp only [defEqTerm, compareTerm]
              split
              next => rfl
              next => exact h
            · have rest := (ih A (by simp +arith)).1
                (.app (left.shift 0) (.bvar rfl)) (.app (right.shift 0) (.bvar rfl)) ha hb
              refine eventually_next ?_ (rest)
              intro d h
              simp only [defEqTerm, compareTerm]
              split
              next => rfl
              next =>
                split
                next =>
                  have eq := ((term_origin_normal _).1 .bvar ra).symm.trans
                    ((term_origin_normal _).1 .bvar rb)
                  cases Term.bvar.inj eq
                  simp [answer, pure, Except.pure]
                next =>
                  have eq := ((term_origin_normal _).1 .parameter ra).symm.trans
                    ((term_origin_normal _).1 .parameter rb)
                  cases Term.parameter.inj eq
                  simp [answer, pure, Except.pure]
                next => exact False.elim (lams ⟨_, _, _, _, rfl, rfl⟩)
                next => exact Nat.noConfusion (Nat.add_right_cancel left.inv_app.1.inv_primrec.1)
                next =>
                  change termFallback d E (k + 1) _ _ _ = .ok true
                  simp only [termFallback]
                  split
                  next => rfl
                  next => exact h
          | zero =>
            simp only [reduceTerm, CheckResult.bind_eq_ok] at ha hb
            obtain ⟨x, hx, ha⟩ := ha
            obtain ⟨y, hy, hb⟩ := hb
            apply term_trace_complete valid left right (whnfTerm_trace hx) (whnfTerm_trace hy)
            have tx := (whnfTerm_sound valid left hx).regularity.2
            have ty := (whnfTerm_sound valid right hy).regularity.2
            have wx := whnfTerm_normal hx
            have wy := whnfTerm_normal hy
            cases x
            case' app f a => cases f
            all_goals simp only [CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq, fail] at ha <;> try contradiction
            all_goals
              repeat first | obtain ⟨_, _, ha⟩ := ha
              try subst N
              cases y
              case' app f a => cases f
              all_goals simp only [CheckResult.bind_eq_ok, pure, Except.pure,
                Except.ok.injEq, fail, reduceCtorEq] at hb <;> try contradiction
            all_goals
              repeat first | obtain ⟨_, _, hb⟩ := hb | obtain ⟨rfl, hb⟩ := hb
            all_goals first
              | exact False.elim (neutral_not_rec (by assumption))
              | exact term_refl
              | apply eventually_next (fun _ => term_app_complete wx)
                apply eventually_and
                · refine (ih _ ?_).2 tx.inv_app.1 ty.inv_app.1
                    (term_app_whnf wx) (term_app_whnf wy) (by assumption) (by assumption)
                  simp +arith
                · refine (ih _ ?_).1 tx.inv_app.2 ty.inv_app.2 (by assumption) (by assumption)
                  simp +arith
              | apply eventually_next (fun _ => term_app_complete wx)
                apply eventually_and
                · apply eventually_next (fun _ => term_rec_complete)
                  apply eventually_and
                  · refine (ih _ ?_).1 tx.inv_app.1.inv_primrec.2.1
                      ty.inv_app.1.inv_primrec.2.1 (by assumption) (by assumption)
                    simp +arith
                  · refine (ih _ ?_).1 tx.inv_app.1.inv_primrec.2.2
                      ty.inv_app.1.inv_primrec.2.2 (by assumption) (by assumption)
                    simp +arith
                · refine (ih _ ?_).1 tx.inv_app.2 ty.inv_app.2 (by assumption) (by assumption)
                  simp +arith
    · intro Ξ Γ k a b n m left right wa wb ha hb
      cases n with
      | zero => simp [reduceTermNeutral, exhausted, fail] at ha
      | succ n =>
        cases m with
        | zero => simp [reduceTermNeutral, exhausted, fail] at hb
        | succ m =>
          simp only [reduceTermNeutral, CheckResult.bind_eq_ok] at ha hb
          obtain ⟨x, hx, ha⟩ := ha
          obtain ⟨y, hy, hb⟩ := hb
          have ea := whnfTerm_fixed wa hx
          have eb := whnfTerm_fixed wb hy
          subst x; subst y
          cases a <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
            Except.ok.injEq, fail] at ha <;> try contradiction
          all_goals
            repeat first | obtain ⟨_, _, ha⟩ := ha
            try subst N
            cases b <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq, fail, reduceCtorEq] at hb <;> try contradiction
          all_goals
            repeat first | obtain ⟨_, _, hb⟩ := hb | obtain ⟨rfl, hb⟩ := hb
          all_goals first
            | exact term_applications_refl
            | apply eventually_next (fun _ => term_applications_app)
              apply eventually_and
              · refine (ih _ ?_).2 left.inv_app.1 right.inv_app.1
                  (term_app_whnf wa) (term_app_whnf wb) (by assumption) (by assumption)
                simp +arith
              · refine (ih _ ?_).1 left.inv_app.2 right.inv_app.2 (by assumption) (by assumption)
                simp +arith

/-- Equal terms compare successfully at every sufficiently large depth. -/
public theorem defEqTerm_complete {E Ξ Γ a b k} (valid : EnvironmentWF E)
    (eq : TermEq E Ξ Γ a b k) : ∃ n, ∀ m ≥ n, defEqTerm m E k a b = .ok true := by
  obtain ⟨n, N, h⟩ := reduceTerm_of_eq valid eq
  exact (term_normal_complete N valid).1 eq.regularity.1 eq.regularity.2
    (h n (Nat.le_refl n)).1 (h n (Nat.le_refl n)).2

private theorem predicate_fallback_complete {E Ξ Γ a b} (valid : EnvironmentWF E)
    (left : PredicateTyping E Ξ Γ a ⟨0, .prop⟩) (right : PredicateTyping E Ξ Γ b ⟨0, .prop⟩)
    (moving : ¬(predicateStep E a = .ok none ∧ predicateStep E b = .ok none))
    (next : ∀ {i j u v}, HeadSteps (predicateStep E) i a u →
      HeadSteps (predicateStep E) j b v → 0 < i + j →
      PredicateTyping E Ξ Γ u ⟨0, .prop⟩ → PredicateTyping E Ξ Γ v ⟨0, .prop⟩ →
      Eventually (fun n => defEqPredicate n E 0 u v = .ok true))
    (trial : Nat → CheckResult Bool) :
    Eventually (fun n => predicateFallback n E 0 a b (trial n) = .ok true) := by
  obtain ⟨i, A, hA⟩ := whnfPredicate_terminates valid left
  obtain ⟨j, B, hB⟩ := whnfPredicate_terminates valid right
  obtain ⟨x, ix, hx⟩ := exposePredicate_terminates (hA i (by omega)) false
  obtain ⟨y, iy, hy⟩ := exposePredicate_terminates (hB j (by omega)) false
  by_cases moves : x ≠ none ∨ y ≠ none
  · obtain ⟨i, j, si, sj, pos⟩ := HeadBatch.progress
      (exposePredicate_batch (hx ix (by omega))) (exposePredicate_batch (hy iy (by omega))) moves
    have tail := next si sj pos
      ((exposePredicate_sound valid left (hx ix (by omega))).regularity valid).2
      ((exposePredicate_sound valid right (hy iy (by omega))).regularity valid).2
    refine eventually_mono ?_ (eventually_and (eventually_succ ⟨ix, hx⟩)
      (eventually_and (eventually_succ ⟨iy, hy⟩) tail))
    intro n h
    simp only [predicateFallback]
    split
    next => rfl
    next =>
      simp only [h.1, h.2.1, bind, Except.bind]
      cases x <;> cases y <;> first | exact h.2.2 | simp at moves
  · have hx0 : x = none := Classical.byContradiction (fun h => moves (.inl h))
    have hy0 : y = none := Classical.byContradiction (fun h => moves (.inr h))
    subst x; subst y
    obtain ⟨x, ux⟩ := unfoldPredicateHead_terminates left
    obtain ⟨y, uy⟩ := unfoldPredicateHead_terminates right
    obtain ⟨u, v, scheduled, hu, hv, progress⟩ := unfold_by_weight_progress (x := x) (y := y) ux uy
      (order := predicateUnfoldingOrder E a b)
      (by intro ord eq; subst x
          simp [predicateUnfoldingOrder, predicate_unfold_none a ux, compareHeadWeights] at ord)
      (by
        intro ord eq; subst y
        cases ha : predicateHeadName a <;>
          simp [predicateUnfoldingOrder, ha, predicate_unfold_none b uy, compareHeadWeights] at ord)
    have batch {t out} (run : out = none ∨ unfoldPredicateHead E t = .ok out) :
        HeadBatch (predicateStep E) false t out := by
      cases out with
      | none => exact .none
      | some out =>
        exact .some (.next (unfoldPredicateHead_step (run.resolve_left (by simp))) .refl) (by omega)
    have moves : x ≠ none ∨ y ≠ none := by
      apply Classical.byContradiction
      intro h
      have hx0 : x = none := Classical.byContradiction (fun hn => h (.inl hn))
      have hy0 : y = none := Classical.byContradiction (fun hn => h (.inr hn))
      subst x; subst y
      exact moving ⟨predicate_ready (hx ix (by omega)) ux, predicate_ready (hy iy (by omega)) uy⟩
    have moved := progress.mpr moves
    obtain ⟨i, j, si, sj, pos⟩ := HeadBatch.progress (batch hu) (batch hv) moved
    have tail := next si sj pos
      (by
        rcases hu with rfl | hu
        · exact left
        · exact ((unfoldPredicateHead_sound valid left hu).regularity valid).2)
      (by
        rcases hv with rfl | hv
        · exact right
        · exact ((unfoldPredicateHead_sound valid right hv).regularity valid).2)
    refine eventually_mono ?_ (eventually_and (eventually_succ ⟨ix, hx⟩)
      (eventually_and (eventually_succ ⟨iy, hy⟩) tail))
    intro n h
    simp only [predicateFallback]
    split
    next => rfl
    next =>
      simp only [h.1, h.2.1, scheduled, bind, Except.bind, Option.isSome_none,
        Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      cases u <;> cases v <;> first | exact h.2.2 | simp at moved

private theorem predicate_trace_complete {E Ξ Γ a b A B} (valid : EnvironmentWF E)
    (left : PredicateTyping E Ξ Γ a ⟨0, .prop⟩) (right : PredicateTyping E Ξ Γ b ⟨0, .prop⟩)
    (ta : HeadTrace (predicateStep E) a A) (tb : HeadTrace (predicateStep E) b B)
    (tail : Eventually (fun n => defEqPredicate n E 0 A B = .ok true)) :
    Eventually (fun n => defEqPredicate n E 0 a b = .ok true) := by
  apply HeadTrace.induction_pair (P := fun a b => PredicateTyping E Ξ Γ a ⟨0, .prop⟩ →
    PredicateTyping E Ξ Γ b ⟨0, .prop⟩ → Eventually (fun n => defEqPredicate n E 0 a b = .ok true))
    (a := a) (b := b) (A := A) (B := B) ?_ ta tb left right
  intro a b ta tb next left right
  by_cases stopped : predicateStep E a = .ok none ∧ predicateStep E b = .ok none
  · rw [ta.stationary stopped.1, tb.stationary stopped.2]
    exact tail
  · have fallback := predicate_fallback_complete valid left right stopped next
      (fun n => predicateTrial (defEqTerm n E) (defEqPredicate n E)
        (comparePredicateApplications n E) E 0 a b)
    refine eventually_next ?_ (fallback)
    intro n h
    simp only [defEqPredicate]
    split
    next => rfl
    next => split <;> first | exact False.elim (stopped ⟨rfl, rfl⟩) | exact h

private def predicateOrigin : Predicate → Option Nat
  | .parameter i => some i
  | .app f _ => predicateOrigin f
  | .lam _ body => predicateOrigin body
  | _ => none

private theorem predicate_origin_rename {t} (head : PredicateApplications t) (r : Renaming) :
    predicateOrigin (t.rename r) = predicateOrigin t := by
  induction head with
  | parameter => simp [Predicate.rename, predicateOrigin]
  | app f ih => simpa only [Predicate.rename, predicateOrigin] using ih

private theorem predicate_origin_normal (n : Nat) :
    (∀ {E k a N}, PredicateApplications a → reducePredicate n E k a = .ok N →
      predicateOrigin N = predicateOrigin a) ∧
    (∀ {E a N}, PredicateApplications a → reducePredicateNeutral n E a = .ok N →
      predicateOrigin N = predicateOrigin a) := by
  induction n with
  | zero => constructor <;> intros <;>
      simp_all [reducePredicate, reducePredicateNeutral, exhausted, fail]
  | succ n ih =>
    constructor
    · intro E k a N head run
      cases k with
      | succ k =>
        simp only [reducePredicate, CheckResult.bind_eq_ok, pure, Except.pure,
          Except.ok.injEq] at run
        obtain ⟨body, hb, rfl⟩ := run
        have shifted : PredicateApplications a.shift := head.rename _
        have eq := ih.1 (.app shifted) hb
        simpa only [predicateOrigin, Predicate.shift, predicate_origin_rename head] using eq
      | zero =>
        simp only [reducePredicate, CheckResult.bind_eq_ok] at run
        obtain ⟨w, hw, run⟩ := run
        have eq := whnfPredicate_fixed head.whnf hw
        subst w
        cases head with
        | parameter =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst N; rfl
        | app hf =>
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨g, hg, b, hb, rfl⟩ := run
          simpa only [predicateOrigin] using ih.2 hf hg
    · intro E a N head run
      simp only [reducePredicateNeutral, CheckResult.bind_eq_ok] at run
      obtain ⟨w, hw, run⟩ := run
      have eq := whnfPredicate_fixed head.whnf hw
      subst w
      cases head with
      | parameter =>
        simp only [pure, Except.pure, Except.ok.injEq] at run
        subst N; rfl
      | app hf =>
        simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
        obtain ⟨g, hg, b, hb, rfl⟩ := run
        simpa only [predicateOrigin] using ih.2 hf hg

private theorem predicate_lam_normal {E Ξ Γ n k name body N} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ (.lam name body) ⟨k + 1, .prop⟩)
    (run : reducePredicate n E (k + 1) (.lam name body) = .ok (.lam .anonymous N)) :
    ∃ m, reducePredicate m E k body = .ok N := by
  have ht := typed.lam_body
  cases n with
  | zero => simp [reducePredicate, exhausted, fail] at run
  | succ n =>
    simp only [reducePredicate, CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq,
      Predicate.lam.injEq, true_and] at run
    obtain ⟨B, hB, rfl⟩ := run
    obtain ⟨m, C, hC⟩ := reducePredicate_terminates valid ht
    have shifted : PredicateTyping E Ξ (0 :: 0 :: Γ)
        (body.rename (Renaming.lift 1 (fun i => i + 1))) ⟨k, .prop⟩ :=
      PredicateTyping.rename valid ht _ (RenamingTyping.lift (by intro i a h; simpa using h) 0)
    have beta := PredicateEq.beta (binderName := name) shifted (TermTyping.bvar (i := 0) rfl)
    simp only [Predicate.shift, Predicate.rename, Nat.not_lt_zero, ↓reduceIte] at beta hB
    rw [predicate_cancel] at beta
    have same := reducePredicate_congr valid beta hB (hC m (by omega))
    exact ⟨m, same ▸ hC m (by omega)⟩

private theorem predicate_applications_refl {E k a} :
    Eventually (fun m => comparePredicateApplications m E k a a = .ok true) := by
  refine ⟨1, ?_⟩
  intro m hm
  cases m with
  | zero => omega
  | succ m => simp [comparePredicateApplications, pure, Except.pure]

private theorem predicate_refl {E k a} :
    Eventually (fun m => defEqPredicate m E k a a = .ok true) := by
  refine ⟨1, ?_⟩
  intro m hm
  cases m with
  | zero => omega
  | succ m => simp [defEqPredicate, pure, Except.pure]

private theorem predicate_applications_app {n E k f a g b}
    (run : comparePredicateApplications n E (k + 1) f g = .ok true ∧
      defEqTerm n E 0 a b = .ok true) :
    comparePredicateApplications (n + 1) E k (.app f a) (.app g b) = .ok true := by
  simp only [comparePredicateApplications]
  split
  next => rfl
  next => simpa only [pure, Except.pure, and_ok] using run

private theorem predicate_app_whnf {f a} (h : PredicateWhnf (.app f a)) : PredicateWhnf f := by
  cases h with | app hf _ => exact hf

private theorem predicate_app_complete {n E k f a g b}
    (run : comparePredicateApplications n E (k + 1) f g = .ok true ∧
      defEqTerm n E 0 a b = .ok true) :
    defEqPredicate (n + 1) E k (.app f a) (.app g b) = .ok true := by
  simp only [defEqPredicate]
  split
  next => rfl
  next => simp only [run.1, run.2, bind, Except.bind, ↓reduceIte]; rfl

private def predicateStructure (n : Nat) (E : Environment) (a b : Predicate) :
    CheckResult Bool := do
  match a, b with
  | .false, .false | .true, .true => pure true
  | .parameter i, .parameter j => pure (i == j)
  | .equal a b, .equal c d =>
    if ← defEqTerm n E 0 a c then defEqTerm n E 0 b d else pure false
  | .imp a b, .imp c d | .and a b, .and c d | .or a b, .or c d =>
    if ← defEqPredicate n E 0 a c then defEqPredicate n E 0 b d else pure false
  | .all a, .all b | .ex a, .ex b => defEqPredicate n E 1 a b
  | .app f a, .app g b =>
    if ← comparePredicateApplications n E 1 f g then defEqTerm n E 0 a b else pure false
  | _, _ => pure false

private theorem predicate_structure_complete {n E a b}
    (run : predicateStructure n E a b = .ok true) :
    defEqPredicate (n + 1) E 0 a b = .ok true := by
  cases a <;> cases b <;> simp only [predicateStructure] at run
  all_goals try (cases (show false = true from Except.ok.inj run))
  all_goals first
    | exact predicate_app_complete ((and_ok _ _).mp run)
    | simp only [defEqPredicate]
      split
      · rfl
      · first | exact run | contradiction

set_option maxHeartbeats 1000000 in
private theorem predicate_normal_complete (N : Predicate) {E} (valid : EnvironmentWF E) :
    (∀ {Ξ Γ k a b n m}, PredicateTyping E Ξ Γ a ⟨k, .prop⟩ →
      PredicateTyping E Ξ Γ b ⟨k, .prop⟩ →
      reducePredicate n E k a = .ok N → reducePredicate m E k b = .ok N →
      Eventually (fun d => defEqPredicate d E k a b = .ok true)) ∧
    (∀ {Ξ Γ k a b n m}, PredicateTyping E Ξ Γ a ⟨k, .prop⟩ →
      PredicateTyping E Ξ Γ b ⟨k, .prop⟩ → PredicateWhnf a → PredicateWhnf b →
      reducePredicateNeutral n E a = .ok N → reducePredicateNeutral m E b = .ok N →
      Eventually (fun d => comparePredicateApplications d E k a b = .ok true)) := by
  generalize hN : sizeOf N = q
  induction q using Nat.strongRecOn generalizing N with
  | ind q previous =>
    have ih (T : Predicate) (lt : sizeOf T < sizeOf N) :=
      previous (sizeOf T) (by omega) T rfl
    constructor
    · intro Ξ Γ k a b n m left right ra rb
      cases n with
      | zero => simp [reducePredicate, exhausted, fail] at ra
      | succ n =>
        cases m with
        | zero => simp [reducePredicate, exhausted, fail] at rb
        | succ m =>
          have ha := ra
          have hb := rb
          cases k with
          | succ k =>
            simp only [reducePredicate, CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq] at ha hb
            obtain ⟨A, ha, rfl⟩ := ha
            obtain ⟨B, hb, eq⟩ := hb
            cases eq
            by_cases lams : ∃ name body name' body',
                a = .lam name body ∧ b = .lam name' body'
            · obtain ⟨name, body, name', body', rfl, rfl⟩ := lams
              obtain ⟨i, hi⟩ := predicate_lam_normal valid left ra
              obtain ⟨j, hj⟩ := predicate_lam_normal valid right rb
              have rest := (ih A (by simp +arith)).1 left.lam_body right.lam_body hi hj
              refine eventually_next ?_ (rest)
              intro d h
              simp only [defEqPredicate]
              split
              next => rfl
              next => exact h
            · have rest := (ih A (by simp +arith)).1
                (.app (left.shift valid 0) (.bvar rfl))
                (.app (right.shift valid 0) (.bvar rfl)) ha hb
              refine eventually_next ?_ (rest)
              intro d h
              simp only [defEqPredicate]
              split
              next => rfl
              next =>
                split
                next =>
                  have eq := ((predicate_origin_normal _).1 .parameter ra).symm.trans
                    ((predicate_origin_normal _).1 .parameter rb)
                  cases Option.some.inj eq
                  simp [pure, Except.pure]
                next => exact False.elim (lams ⟨_, _, _, _, rfl, rfl⟩)
                next => exact Nat.noConfusion left.inv_equal.2.2.arity_eq
                next =>
                  obtain ⟨_, _, _, sub⟩ := left.inv_imp
                  exact Nat.noConfusion sub.arity_eq
                next =>
                  obtain ⟨_, _, _, sub⟩ := left.inv_and
                  exact Nat.noConfusion sub.arity_eq
                next =>
                  obtain ⟨_, _, _, sub⟩ := left.inv_or
                  exact Nat.noConfusion sub.arity_eq
                next => exact Nat.noConfusion (congrArg PredicateSignature.arity left.inv_all.1)
                next => exact Nat.noConfusion (congrArg PredicateSignature.arity left.inv_ex.1)
                next =>
                  change predicateFallback d E (k + 1) _ _ _ = .ok true
                  simp only [predicateFallback]
                  split
                  next => rfl
                  next => exact h
          | zero =>
            simp only [reducePredicate, CheckResult.bind_eq_ok] at ha hb
            obtain ⟨x, hx, ha⟩ := ha
            obtain ⟨y, hy, hb⟩ := hb
            apply predicate_trace_complete valid left right
              (whnfPredicate_trace hx) (whnfPredicate_trace hy)
            have tx := ((whnfPredicate_sound valid left hx).regularity valid).2
            have ty := ((whnfPredicate_sound valid right hy).regularity valid).2
            have wx := whnfPredicate_normal hx
            have wy := whnfPredicate_normal hy
            clear previous hN ra rb left right hx hy a b q
            apply eventually_next (fun _ => predicate_structure_complete)
            cases x <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq, fail] at ha <;> try contradiction
            all_goals
              repeat first | obtain ⟨_, _, ha⟩ := ha
              try subst N
              cases y <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
                Except.ok.injEq, fail, reduceCtorEq] at hb <;> try contradiction
            all_goals
              repeat first | obtain ⟨_, _, hb⟩ := hb | obtain ⟨rfl, hb⟩ := hb
            all_goals
              simp only [predicateStructure, pure, Except.pure, and_ok, beq_self_eq_true]
            all_goals
              repeat' apply eventually_and
            all_goals first
              | exact eventually_const trivial
              | exact eventually_const rfl
              | refine (term_normal_complete _ valid).1 tx.inv_equal.1 ty.inv_equal.1
                  (by assumption) (by assumption)
              | refine (term_normal_complete _ valid).1 tx.inv_equal.2.1 ty.inv_equal.2.1
                  (by assumption) (by assumption)
              | obtain ⟨_, ta, tb, _⟩ := tx.inv_imp
                obtain ⟨_, tc, td, _⟩ := ty.inv_imp
                first
                | refine (ih _ ?_).1 ta.toProp tc.toProp (by assumption) (by assumption)
                  simp +arith
                | refine (ih _ ?_).1 tb.toProp td.toProp (by assumption) (by assumption)
                  simp +arith
              | obtain ⟨_, ta, tb, _⟩ := tx.inv_and
                obtain ⟨_, tc, td, _⟩ := ty.inv_and
                first
                | refine (ih _ ?_).1 ta.toProp tc.toProp (by assumption) (by assumption)
                  simp +arith
                | refine (ih _ ?_).1 tb.toProp td.toProp (by assumption) (by assumption)
                  simp +arith
              | obtain ⟨_, ta, tb, _⟩ := tx.inv_or
                obtain ⟨_, tc, td, _⟩ := ty.inv_or
                first
                | refine (ih _ ?_).1 ta.toProp tc.toProp (by assumption) (by assumption)
                  simp +arith
                | refine (ih _ ?_).1 tb.toProp td.toProp (by assumption) (by assumption)
                  simp +arith
              | refine (ih _ ?_).1 tx.inv_all.2 ty.inv_all.2 (by assumption) (by assumption)
                simp +arith
              | refine (ih _ ?_).1 tx.inv_ex.2 ty.inv_ex.2 (by assumption) (by assumption)
                simp +arith
              | refine (ih _ ?_).2 tx.app_function.1 ty.app_function.1
                  (predicate_app_whnf wx) (predicate_app_whnf wy) (by assumption) (by assumption)
                simp +arith
              | refine (term_normal_complete _ valid).1 tx.app_function.2 ty.app_function.2
                  (by assumption) (by assumption)
    · intro Ξ Γ k a b n m left right wa wb ha hb
      cases n with
      | zero => simp [reducePredicateNeutral, exhausted, fail] at ha
      | succ n =>
        cases m with
        | zero => simp [reducePredicateNeutral, exhausted, fail] at hb
        | succ m =>
          simp only [reducePredicateNeutral, CheckResult.bind_eq_ok] at ha hb
          obtain ⟨x, hx, ha⟩ := ha
          obtain ⟨y, hy, hb⟩ := hb
          have ea := whnfPredicate_fixed wa hx
          have eb := whnfPredicate_fixed wb hy
          subst x; subst y
          cases a <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
            Except.ok.injEq, fail] at ha <;> try contradiction
          all_goals
            repeat first | obtain ⟨_, _, ha⟩ := ha
            try subst N
            cases b <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
              Except.ok.injEq, fail, reduceCtorEq] at hb <;> try contradiction
          all_goals
            repeat first | obtain ⟨_, _, hb⟩ := hb | obtain ⟨rfl, hb⟩ := hb
          all_goals first
            | exact predicate_applications_refl
            | apply eventually_next (fun _ => predicate_applications_app)
              apply eventually_and
              · refine (ih _ ?_).2 left.app_function.1 right.app_function.1
                  (predicate_app_whnf wa) (predicate_app_whnf wb) (by assumption) (by assumption)
                simp +arith
              · exact (term_normal_complete _ valid).1 left.app_function.2 right.app_function.2
                  (by assumption) (by assumption)

/-- Equal predicates compare successfully at their common arity beyond a finite depth bound. -/
public theorem defEqPredicate_complete {E Ξ Γ a b σ} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ a b σ) :
    ∃ n, ∀ m ≥ n, defEqPredicate m E σ.arity a b = .ok true := by
  obtain ⟨n, N, h⟩ := reducePredicate_of_eq valid eq
  exact (predicate_normal_complete N valid).1 (eq.regularity valid).1.toProp
    (eq.regularity valid).2.toProp (h n (Nat.le_refl n)).1 (h n (Nat.le_refl n)).2

end LeanPRA.Core
