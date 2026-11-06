module

public import LeanPRA.Metatheory.Core.Properties.Normalization.Existence
import LeanPRA.Metatheory.Core.Judgement.Formation
import LeanPRA.Metatheory.Core.Properties.Normalization.Soundness

/-!
# Fixed points and canonical representatives of typed conversion

- `reduceTerm_fixed` and `reducePredicate_fixed` show that normal syntax is fixed by
  successful normalization.
- `TermEq.normal_form` and `PredicateEq.normal_form` give normal representatives for typed syntax.
- `TermNormal.eq_iff` and `PredicateNormal.eq_iff` identify conversion of normal forms with syntax
  equality.
- `TermEq.unique_normal_form` and `PredicateEq.unique_normal_form` package existence and uniqueness.
- `TermEq.normal_forms_iff` and `PredicateEq.normal_forms_iff` characterize conversion by equality
  of any chosen normal representatives.

Normal forms are beta-normal and eta-long at their displayed arities.
-/

namespace LeanPRA.Core

open Theory

private theorem neutral_whnf {t} (h : TermNeutral t) : TermWhnf t := by
  induction h using TermNeutral.rec (motive_1 := fun _ _ _ => True) <;> try trivial
  case bvar => exact .bvar
  case parameter => exact .parameter
  case succ => exact .succ
  case app f a ih _ => exact .app ih (by intro u n eq; cases f <;> cases eq)

private theorem normal_whnf {k t} (h : TermNormal k t) : TermWhnf t := by
  induction h using TermNormal.rec (motive_2 := fun _ _ => True) with
  | zero => exact .zero
  | bvar => exact .bvar
  | parameter => exact .parameter
  | app f a _ _ => exact .app (neutral_whnf f) (by intro u n eq; cases f <;> cases eq)
  | primrec b s a blocked _ _ ih => exact .primrec ih blocked
  | lam => exact .lam
  | _ => trivial

private theorem term_cancel (t : Term) :
    (t.rename (Renaming.lift 1 (fun i => i + 1))).subst0 (.bvar 0) = t := by
  rw [Term.subst0, Term.subst_rename]
  have h : (fun i => (fun | 0 => Term.bvar 0 | j + 1 => Term.bvar j)
      (Renaming.lift 1 (fun j => j + 1) i)) = Term.bvar := by
    funext i; cases i <;> simp [Renaming.lift, Nat.add_comm]
  change t.subst _ = t
  exact (congrArg (fun s => t.subst s) h).trans (Term.subst_id t)

private theorem term_fixed {E} (valid : EnvironmentWF E) {k t} (normal : TermNormal k t) :
    ∀ {Ξ Γ n u}, TermTyping E Ξ Γ t k → reduceTerm n E k t = .ok u → u = t := by
  induction normal using TermNormal.rec
    (motive_2 := fun t _ => ∀ {Ξ Γ k n u}, TermTyping E Ξ Γ t k →
      reduceTermNeutral n E t = .ok u → u = t)
  case lam k t body ih =>
      intro Ξ Γ n u typed run
      cases n with
      | zero => simp [reduceTerm, exhausted, fail] at run
      | succ n =>
          simp only [reduceTerm, CheckResult.bind_eq_ok, pure, Except.pure,
            Except.ok.injEq] at run
          obtain ⟨v, hv, rfl⟩ := run
          obtain ⟨l, arity, bodytyped⟩ := typed.inv_lam
          have eqk : l = k := Nat.add_right_cancel arity.symm
          subst l
          obtain ⟨j, w, hw⟩ := reduceTerm_terminates valid bodytyped
          have ew := ih bodytyped (hw j (by omega))
          subst w
          have shifted : TermTyping E Ξ (0 :: 0 :: Γ)
              (t.rename (Renaming.lift 1 (fun i => i + 1))) k :=
            TermTyping.rename bodytyped _
              (RenamingTyping.lift (by intro i a h; simpa using h) 0)
          have beta := TermEq.beta (binderName := .anonymous) shifted (TermTyping.bvar (i := 0) rfl)
          simp only [Term.shift, Term.rename, Nat.not_lt_zero, ↓reduceIte] at beta hv
          rw [term_cancel] at beta
          have same := reduceTerm_congr valid beta hv (hw j (by omega))
          exact congrArg (fun t => Term.lam _ t) same
  case app f a fn arg ihf iha =>
      intro Ξ Γ n u typed run
      cases n with
      | zero => simp [reduceTerm, exhausted, fail] at run
      | succ n =>
          simp only [reduceTerm, CheckResult.bind_eq_ok] at run
          obtain ⟨w, hw, run⟩ := run
          have eq := whnfTerm_fixed (normal_whnf (.app fn arg)) hw
          subst w
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨g, hg, b, hb, rfl⟩ := run
          rw [ihf typed.inv_app.1 hg, iha typed.inv_app.2 hb]
  case primrec b s a base step arg blocked ihb ihs iha =>
      intro Ξ Γ n u typed run
      cases n with
      | zero => simp [reduceTerm, exhausted, fail] at run
      | succ n =>
          simp only [reduceTerm, CheckResult.bind_eq_ok] at run
          obtain ⟨w, hw, run⟩ := run
          have eq := whnfTerm_fixed (normal_whnf (.primrec base step arg blocked)) hw
          subst w
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨c, hc, v, hv, m, hm, rfl⟩ := run
          obtain ⟨_, tb, ts, ta⟩ := typed.inv_primrec
          rw [ihb tb hc, ihs ts hv, iha ta hm]
  case app f a fn arg ihf iha =>
      intro Ξ Γ k n u typed run
      cases n with
      | zero => simp [reduceTermNeutral, exhausted, fail] at run
      | succ n =>
          simp only [reduceTermNeutral, CheckResult.bind_eq_ok] at run
          obtain ⟨w, hw, run⟩ := run
          have eq := whnfTerm_fixed (neutral_whnf (.app fn arg)) hw
          subst w
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨g, hg, b, hb, rfl⟩ := run
          rw [ihf typed.inv_app.1 hg, iha typed.inv_app.2 hb]
  all_goals
      intros
      rename_i run
      cases ‹Nat› with
      | zero => simp_all [reduceTerm, reduceTermNeutral, exhausted, fail]
      | succ n =>
          cases n <;> simp_all [reduceTerm, reduceTermNeutral, whnfTerm, exhausted, fail,
            pure, Except.pure]

private theorem predicate_neutral_whnf {P} (h : PredicateNeutral P) : PredicateWhnf P := by
  induction h using PredicateNeutral.rec (motive_1 := fun _ _ _ => True) <;> try trivial
  case parameter => exact .parameter
  case app f a ih => exact .app ih (by intro u n eq; cases f <;> cases eq)

private theorem predicate_normal_whnf {k P} (h : PredicateNormal k P) : PredicateWhnf P := by
  cases h with
  | false => exact .false
  | true => exact .true
  | equal => exact .equal
  | imp => exact .imp
  | and => exact .and
  | or => exact .or
  | all => exact .all
  | ex => exact .ex
  | parameter => exact .parameter
  | lam => exact .lam
  | app f a => exact .app (predicate_neutral_whnf f) (by intro u n eq; cases f <;> cases eq)

private theorem predicate_cancel (P : Predicate) :
    (P.rename (Renaming.lift 1 (fun i => i + 1))).subst0 (.bvar 0) = P := by
  rw [Predicate.subst0, Predicate.subst_rename]
  have h : (fun i => (fun | 0 => Term.bvar 0 | j + 1 => Term.bvar j)
      (Renaming.lift 1 (fun j => j + 1) i)) = Term.bvar := by
    funext i; cases i <;> simp [Renaming.lift, Nat.add_comm]
  exact (congrArg (fun s => P.subst s) h).trans (Predicate.subst_id P)

private theorem predicate_fixed {E} (valid : EnvironmentWF E) {k P}
    (normal : PredicateNormal k P) : ∀ {Ξ Γ n Q},
    PredicateTyping E Ξ Γ P ⟨k, .prop⟩ → reducePredicate n E k P = .ok Q → Q = P := by
  induction normal using PredicateNormal.rec
    (motive_2 := fun P _ => ∀ {Ξ Γ k n Q}, PredicateTyping E Ξ Γ P ⟨k, .prop⟩ →
      reducePredicateNeutral n E P = .ok Q → Q = P)
  case lam k P body ih =>
      intro Ξ Γ n Q typed run
      cases n with
      | zero => simp [reducePredicate, exhausted, fail] at run
      | succ n =>
          simp only [reducePredicate, CheckResult.bind_eq_ok, pure, Except.pure,
            Except.ok.injEq] at run
          obtain ⟨R, hR, rfl⟩ := run
          have bodytyped := typed.lam_body
          obtain ⟨j, S, hS⟩ := reducePredicate_terminates valid bodytyped
          have eqS := ih bodytyped (hS j (by omega))
          subst S
          have shifted : PredicateTyping E Ξ (0 :: 0 :: Γ)
              (P.rename (Renaming.lift 1 (fun i => i + 1))) ⟨k, .prop⟩ :=
            PredicateTyping.rename valid bodytyped _
              (RenamingTyping.lift (by intro i a h; simpa using h) 0)
          have beta := PredicateEq.beta (binderName := .anonymous) shifted (TermTyping.bvar (i :=
              0) rfl)
          simp only [Predicate.shift, Predicate.rename, Nat.not_lt_zero, ↓reduceIte] at beta hR
          rw [predicate_cancel] at beta
          exact congrArg (fun t => Predicate.lam _ t) (reducePredicate_congr valid
              beta hR (hS j (by omega)))
  case equal a b left right =>
      intro Ξ Γ n Q typed run
      cases n with
      | zero => simp [reducePredicate, exhausted, fail] at run
      | succ n =>
          simp only [reducePredicate, CheckResult.bind_eq_ok] at run
          obtain ⟨R, hR, run⟩ := run
          have eq := whnfPredicate_fixed PredicateWhnf.equal hR
          subst R
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨c, hc, d, hd, rfl⟩ := run
          rw [term_fixed valid left typed.inv_equal.1 hc,
            term_fixed valid right typed.inv_equal.2.1 hd]
  case imp A B left right ihA ihB =>
      intro Ξ Γ n Q typed run
      cases n with
      | zero => simp [reducePredicate, exhausted, fail] at run
      | succ n =>
          simp only [reducePredicate, CheckResult.bind_eq_ok] at run
          obtain ⟨R, hR, run⟩ := run
          have eq := whnfPredicate_fixed PredicateWhnf.imp hR
          subst R
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨C, hC, D, hD, rfl⟩ := run
          obtain ⟨s, ha, hb, _⟩ := typed.inv_imp
          rw [ihA ha.toProp hC, ihB hb.toProp hD]
  case and A B left right ihA ihB =>
      intro Ξ Γ n Q typed run
      cases n with
      | zero => simp [reducePredicate, exhausted, fail] at run
      | succ n =>
          simp only [reducePredicate, CheckResult.bind_eq_ok] at run
          obtain ⟨R, hR, run⟩ := run
          have eq := whnfPredicate_fixed PredicateWhnf.and hR
          subst R
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨C, hC, D, hD, rfl⟩ := run
          obtain ⟨s, ha, hb, _⟩ := typed.inv_and
          rw [ihA ha.toProp hC, ihB hb.toProp hD]
  case or A B left right ihA ihB =>
      intro Ξ Γ n Q typed run
      cases n with
      | zero => simp [reducePredicate, exhausted, fail] at run
      | succ n =>
          simp only [reducePredicate, CheckResult.bind_eq_ok] at run
          obtain ⟨R, hR, run⟩ := run
          have eq := whnfPredicate_fixed PredicateWhnf.or hR
          subst R
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨C, hC, D, hD, rfl⟩ := run
          obtain ⟨s, ha, hb, _⟩ := typed.inv_or
          rw [ihA ha.toProp hC, ihB hb.toProp hD]
  case all P body ih =>
      intro Ξ Γ n Q typed run
      cases n with
      | zero => simp [reducePredicate, exhausted, fail] at run
      | succ n =>
          simp only [reducePredicate, CheckResult.bind_eq_ok] at run
          obtain ⟨R, hR, run⟩ := run
          have eq := whnfPredicate_fixed PredicateWhnf.all hR
          subst R
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨S, hS, rfl⟩ := run
          rw [ih typed.inv_all.2 hS]
  case ex P body ih =>
      intro Ξ Γ n Q typed run
      cases n with
      | zero => simp [reducePredicate, exhausted, fail] at run
      | succ n =>
          simp only [reducePredicate, CheckResult.bind_eq_ok] at run
          obtain ⟨R, hR, run⟩ := run
          have eq := whnfPredicate_fixed PredicateWhnf.ex hR
          subst R
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨S, hS, rfl⟩ := run
          rw [ih typed.inv_ex.2 hS]
  case app P a fn arg ihP =>
      intro Ξ Γ n Q typed run
      cases n with
      | zero => simp [reducePredicate, exhausted, fail] at run
      | succ n =>
          simp only [reducePredicate, CheckResult.bind_eq_ok] at run
          obtain ⟨R, hR, run⟩ := run
          have eq := whnfPredicate_fixed (predicate_normal_whnf (.app fn arg)) hR
          subst R
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨S, hS, b, hb, rfl⟩ := run
          rw [ihP typed.app_function.1 hS,
            term_fixed valid arg typed.app_function.2 hb]
  case app P a fn arg ihP =>
      intro Ξ Γ k n Q typed run
      cases n with
      | zero => simp [reducePredicateNeutral, exhausted, fail] at run
      | succ n =>
          simp only [reducePredicateNeutral, CheckResult.bind_eq_ok] at run
          obtain ⟨R, hR, run⟩ := run
          have eq := whnfPredicate_fixed (predicate_neutral_whnf (.app fn arg)) hR
          subst R
          simp only [CheckResult.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at run
          obtain ⟨S, hS, b, hb, rfl⟩ := run
          rw [ihP typed.app_function.1 hS,
            term_fixed valid arg typed.app_function.2 hb]
  all_goals
      intros
      rename_i run
      cases ‹Nat› with
      | zero => simp_all [reducePredicate, reducePredicateNeutral, exhausted, fail]
      | succ n =>
          cases n <;> simp_all [reducePredicate, reducePredicateNeutral, whnfPredicate,
            exhausted, fail, pure, Except.pure]

/-- Normalizing well-typed beta-normal, eta-long numerical syntax returns that exact syntax. -/
public theorem reduceTerm_fixed {E Ξ Γ k t n u} (valid : EnvironmentWF E)
    (normal : TermNormal k t) (typed : TermTyping E Ξ Γ t k)
    (run : reduceTerm n E k t = .ok u) : u = t := term_fixed valid normal typed run

/-- Normalizing well-typed beta-normal, eta-long predicate syntax returns that exact syntax. -/
public theorem reducePredicate_fixed {E Ξ Γ σ P n Q} (valid : EnvironmentWF E)
    (normal : PredicateNormal σ.arity P) (typed : PredicateTyping E Ξ Γ P σ)
    (run : reducePredicate n E σ.arity P = .ok Q) : Q = P :=
  predicate_fixed valid normal typed.toProp run

end LeanPRA.Core

namespace LeanPRA.Core.Theory

/-- A typed numerical expression has a definitionally equal, typed normal representative. -/
public theorem TermEq.normal_form {E Ξ Γ t k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) :
    ∃ u, TermNormal k u ∧ TermTyping E Ξ Γ u k ∧ TermEq E Ξ Γ t u k := by
  obtain ⟨n, u, hu⟩ := reduceTerm_terminates valid typed
  have eq := reduceTerm_sound valid typed (hu n (by omega))
  exact ⟨u, reduceTerm_normal (hu n (by omega)), eq.regularity.2, eq⟩

/-- A formed predicate has a normal representative at the same full signature. -/
public theorem PredicateEq.normal_form {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) :
    ∃ Q, PredicateNormal σ.arity Q ∧ PredicateTyping E Ξ Γ Q σ ∧ PredicateEq E Ξ Γ P Q σ := by
  obtain ⟨n, Q, hQ⟩ := reducePredicate_terminates valid typed
  have eq := reducePredicate_sound valid typed (hQ n (by omega))
  exact ⟨Q, reducePredicate_normal (hQ n (by omega)), (eq.regularity valid).2, eq⟩

/-- Two well-typed numerical normal forms are convertible exactly when their syntax agrees. -/
public theorem TermNormal.eq_iff {E Ξ Γ t u k} (valid : EnvironmentWF E)
    (left : TermNormal k t) (right : TermNormal k u)
    (typedLeft : TermTyping E Ξ Γ t k) (typedRight : TermTyping E Ξ Γ u k) :
    TermEq E Ξ Γ t u k ↔ t = u := by
  constructor
  · intro eq
    obtain ⟨n, v, hv⟩ := reduceTerm_of_eq valid eq
    exact (reduceTerm_fixed valid left typedLeft (hv n (by omega)).1).symm.trans
      (reduceTerm_fixed valid right typedRight (hv n (by omega)).2)
  · rintro rfl; exact .refl typedLeft

/-- Predicate conversion at either sort identifies exactly equal typed normal syntax. -/
public theorem PredicateNormal.eq_iff {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (left : PredicateNormal σ.arity P) (right : PredicateNormal σ.arity Q)
    (typedLeft : PredicateTyping E Ξ Γ P σ) (typedRight : PredicateTyping E Ξ Γ Q σ) :
    PredicateEq E Ξ Γ P Q σ ↔ P = Q := by
  constructor
  · intro eq
    obtain ⟨n, R, hR⟩ := reducePredicate_of_eq valid eq
    exact (reducePredicate_fixed valid left typedLeft (hR n (by omega)).1).symm.trans
      (reducePredicate_fixed valid right typedRight (hR n (by omega)).2)
  · rintro rfl; exact .refl typedLeft

/-- Any choices of numerical normal representatives characterize the original conversion. -/
public theorem TermEq.normal_forms_iff {E Ξ Γ t u a b k} (valid : EnvironmentWF E)
    (left : TermEq E Ξ Γ t a k) (right : TermEq E Ξ Γ u b k)
    (normalLeft : TermNormal k a) (normalRight : TermNormal k b) :
    TermEq E Ξ Γ t u k ↔ a = b := by
  constructor
  · intro eq
    exact (normalLeft.eq_iff valid normalRight left.regularity.2 right.regularity.2).mp
      (.trans left.symm (.trans eq right))
  · rintro rfl; exact .trans left right.symm

/-- Any choices of predicate normal representatives characterize conversion at the full sort. -/
public theorem PredicateEq.normal_forms_iff {E Ξ Γ P Q A B σ} (valid : EnvironmentWF E)
    (left : PredicateEq E Ξ Γ P A σ) (right : PredicateEq E Ξ Γ Q B σ)
    (normalLeft : PredicateNormal σ.arity A) (normalRight : PredicateNormal σ.arity B) :
    PredicateEq E Ξ Γ P Q σ ↔ A = B := by
  constructor
  · intro eq
    exact (normalLeft.eq_iff valid normalRight (left.regularity valid).2
      (right.regularity valid).2).mp (.trans left.symm (.trans eq right))
  · rintro rfl; exact .trans left right.symm

/-- A typed term has exactly one beta-normal, eta-long representative modulo conversion. -/
public theorem TermEq.unique_normal_form {E Ξ Γ t k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) :
    ∃ u, TermNormal k u ∧ TermEq E Ξ Γ t u k ∧
      ∀ v, TermNormal k v → TermEq E Ξ Γ t v k → v = u := by
  obtain ⟨u, normal, _, eq⟩ := TermEq.normal_form valid typed
  exact ⟨u, normal, eq, fun v nv ev =>
    (TermEq.normal_forms_iff valid ev eq nv normal).mp (.refl typed)⟩

/-- A formed predicate has exactly one normal representative at its full signature. -/
public theorem PredicateEq.unique_normal_form {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) :
    ∃ Q, PredicateNormal σ.arity Q ∧ PredicateEq E Ξ Γ P Q σ ∧
      ∀ R, PredicateNormal σ.arity R → PredicateEq E Ξ Γ P R σ → R = Q := by
  obtain ⟨Q, normal, _, eq⟩ := PredicateEq.normal_form valid typed
  exact ⟨Q, normal, eq, fun R nr er =>
    (PredicateEq.normal_forms_iff valid er eq nr normal).mp (.refl typed)⟩

end LeanPRA.Core.Theory
