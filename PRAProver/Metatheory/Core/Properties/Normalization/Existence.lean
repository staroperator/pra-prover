module

public import PRAProver.Metatheory.Core.Properties.Normalization.Renaming
public import PRAProver.Metatheory.Core.Judgement.PredicateSubstitution
import Std.Data.ExtHashMap.Lemmas

/-!
# Successful normalization and equality of normal forms

- `reduceTerm_terminates` and `reducePredicate_terminates` supply successful finite depths.
- `whnfTerm_terminates` and `whnfPredicate_terminates` cover weak-head reduction.
- `reduceTermNeutral_terminates` and `reducePredicateNeutral_terminates` cover typed applications
  with neutral heads.
- `reduceFormula_terminates` specializes full normalization to formulas.
- `reduceTerm_of_eq` and `reducePredicate_of_eq` produce common normal forms.
- `reduceTerm_congr` and `reducePredicate_congr` compare any two successful runs.

The private computation relations compare normal forms at arity zero and applications to related
numerical arguments at positive arity, under arbitrary local renamings. Environment validity
supplies an acyclic order for transparent definitions.
-/

namespace PRAProver.Core

open Theory

private def Finish (n : Nat) (E : Environment) : Term → CheckResult Term
  | .zero => pure .zero
  | .bvar i => pure (.bvar i)
  | .parameter i => pure (.parameter i)
  | .app (.primrec b s) a => do
      let b ← reduceTerm n E 0 b
      let s ← reduceTerm n E 2 s
      let a ← reduceTerm n E 0 a
      pure (.app (.primrec b s) a)
  | .app f a => do
      let f ← reduceTermNeutral n E f
      let a ← reduceTerm n E 0 a
      pure (.app f a)
  | t => fail (.expectedForm .number (.term t))

private theorem reduce_zero (n E t) : reduceTerm (n + 1) E 0 t =
    (do let w ← whnfTerm n E t; Finish n E w) := by
  simp only [reduceTerm, Finish]
  congr 1
  funext w
  cases w <;> try rfl
  case app f a => cases f <;> rfl

private theorem finish_mono {n m E w v} (le : n ≤ m) (run : Finish n E w = .ok v) :
    Finish m E w = .ok v := by
  cases w <;> simp only [Finish, fail] at run ⊢ <;>
    try contradiction
  case app f a =>
    cases f <;> simp only [CheckResult.bind_eq_ok] at run ⊢
    case primrec b s =>
      obtain ⟨c, hc, t, ht, m, hm, hv⟩ := run
      exact ⟨c, reduceTerm_mono le hc, t, reduceTerm_mono le ht, m, reduceTerm_mono le hm, hv⟩
    all_goals
      obtain ⟨g, hg, b, hb, hv⟩ := run
      exact ⟨g, reduceTermNeutral_mono le hg, b, reduceTerm_mono le hb, hv⟩
  all_goals exact run

private abbrev HeadEq (E : Environment) (t u : Term) : Prop :=
  ∀ r v, (∃ n, whnfTerm n E (t.rename r) = .ok v) ↔
    (∃ n, whnfTerm n E (u.rename r) = .ok v)

private theorem transfer_zero {E t u v n}
    (heads : ∀ w, (∃ m, whnfTerm m E t = .ok w) → ∃ m, whnfTerm m E u = .ok w)
    (run : reduceTerm n E 0 t = .ok v) : ∃ m, reduceTerm m E 0 u = .ok v := by
  cases n with
  | zero => simp [reduceTerm, exhausted, fail] at run
  | succ n =>
      rw [reduce_zero] at run
      obtain ⟨w, hw, hf⟩ := CheckResult.bind_eq_ok.mp run
      obtain ⟨m, hm⟩ := heads w ⟨n, hw⟩
      refine ⟨max n m + 1, ?_⟩
      rw [reduce_zero]
      exact CheckResult.bind_eq_ok.mpr ⟨w, whnfTerm_mono (by omega) hm,
        finish_mono (by omega) hf⟩

private theorem transfer_app {E t u a v n}
    (heads : ∀ w, (∃ m, whnfTerm m E t = .ok w) → ∃ m, whnfTerm m E u = .ok w)
    (run : whnfTerm n E (.app t a) = .ok v) : ∃ m, whnfTerm m E (.app u a) = .ok v := by
  cases n with
  | zero => simp [whnfTerm, exhausted, fail] at run
  | succ n =>
      simp only [whnfTerm, CheckResult.bind_eq_ok] at run
      obtain ⟨w, hw, run⟩ := run
      obtain ⟨m, hm⟩ := heads w ⟨n, hw⟩
      refine ⟨max n m + 1, ?_⟩
      simp only [whnfTerm, CheckResult.bind_eq_ok]
      refine ⟨w, whnfTerm_mono (by omega) hm, ?_⟩
      cases w <;> try first | exact whnfTerm_mono (by omega) run | exact run
      case primrec base step =>
        simp only [CheckResult.bind_eq_ok] at run ⊢
        obtain ⟨v', hv', run⟩ := run
        refine ⟨v', whnfTerm_mono (by omega) hv', ?_⟩
        cases v' with
        | zero => exact whnfTerm_mono (by omega) run
        | app f p => cases f <;> first | exact whnfTerm_mono (by omega) run | exact run
        | _ => exact run

private theorem head_app {E t u} (eq : HeadEq E t u) (a : Term) :
    HeadEq E (.app t a) (.app u a) := by
  intro r v
  simp only [Term.rename]
  constructor
  · rintro ⟨n, hn⟩
    exact transfer_app (fun w h => (eq r w).mp h) hn
  · rintro ⟨n, hn⟩
    exact transfer_app (fun w h => (eq r w).mpr h) hn

private abbrev NumberRelated (E : Environment) (t u : Term) : Prop :=
  ∃ n m v, reduceTerm n E 0 t = .ok v ∧ reduceTerm m E 0 u = .ok v

private def Related (E : Environment) : Nat → Term → Term → Prop
  | 0, t, u => NumberRelated E t u
  | k + 1, t, u =>
      (∀ r, ∃ n v, whnfTerm n E (t.rename r) = .ok v) ∧
      (∀ r, ∃ n v, whnfTerm n E (u.rename r) = .ok v) ∧
      ∀ r a b, NumberRelated E a b → Related E k (.app (t.rename r) a) (.app (u.rename r) b)
termination_by structural k _ _ => k

private theorem related_symm {E k t u} (h : Related E k t u) : Related E k u t := by
  induction k generalizing t u with
  | zero => obtain ⟨n, m, v, ht, hu⟩ := h; exact ⟨m, n, v, hu, ht⟩
  | succ k ih =>
      refine ⟨h.2.1, h.1, ?_⟩
      intro r a b hab
      obtain ⟨n, m, v, ha, hb⟩ := hab
      exact ih (h.2.2 r b a ⟨m, n, v, hb, ha⟩)

private theorem related_trans {E k t u v} (h : Related E k t u) (g : Related E k u v) :
    Related E k t v := by
  induction k generalizing t u v with
  | zero =>
      obtain ⟨n, m, a, ht, hu⟩ := h
      obtain ⟨l, j, b, hu', hv⟩ := g
      have eq := (reduceTerm_mono (Nat.le_max_left m l) hu).symm.trans
        (reduceTerm_mono (Nat.le_max_right m l) hu')
      have : a = b := Except.ok.inj eq
      subst b
      exact ⟨n, j, a, ht, hv⟩
  | succ k ih =>
      refine ⟨h.1, g.2.1, ?_⟩
      intro r a b hab
      obtain ⟨n, m, w, ha, hb⟩ := hab
      exact ih (h.2.2 r a a ⟨n, n, w, ha, ha⟩) (g.2.2 r a b ⟨n, m, w, ha, hb⟩)

private theorem related_rename {E k t u} (valid : EnvironmentWF E) (h : Related E k t u)
    (r : Renaming) : Related E k (t.rename r) (u.rename r) := by
  cases k with
  | zero =>
      obtain ⟨n, m, v, ht, hu⟩ := h
      exact ⟨n, m, v.rename r, reduceTerm_rename valid ht r, reduceTerm_rename valid hu r⟩
  | succ k =>
      simp only [Related, Term.rename_comp]
      exact ⟨fun s => h.1 (fun i => s (r i)), fun s => h.2.1 (fun i => s (r i)),
        fun s a b hab => h.2.2 (fun i => s (r i)) a b hab⟩

private theorem related_normalize {E k t u} (h : Related E k t u) :
    ∃ n m v, reduceTerm n E k t = .ok v ∧ reduceTerm m E k u = .ok v := by
  induction k generalizing t u with
  | zero => exact h
  | succ k ih =>
      have var : Related E 0 (.bvar 0) (.bvar 0) :=
        ⟨2, 2, .bvar 0, by simp [reduceTerm, whnfTerm, pure, Except.pure],
          by simp [reduceTerm, whnfTerm, pure, Except.pure]⟩
      obtain ⟨n, m, v, ht, hu⟩ := ih (h.2.2 (fun i => i + 1) _ _ var)
      refine ⟨n + 1, m + 1, .lam .anonymous v, ?_, ?_⟩ <;>
        simp only [reduceTerm, CheckResult.bind_eq_ok]
      · exact ⟨v, ht, rfl⟩
      · exact ⟨v, hu, rfl⟩

private theorem related_head_left {E k t u v} (eq : HeadEq E t u) (h : Related E k u v) :
    Related E k t v := by
  induction k generalizing t u v with
  | zero =>
      obtain ⟨n, m, w, hu, hv⟩ := h
      have heads : ∀ w, (∃ m, whnfTerm m E u = .ok w) → ∃ m, whnfTerm m E t = .ok w := by
        intro w hw
        simpa only [Term.rename_id] using (eq id w).mpr (by simpa only [Term.rename_id] using hw)
      obtain ⟨l, ht⟩ := transfer_zero heads hu
      exact ⟨l, m, w, ht, hv⟩
  | succ k ih =>
      refine ⟨?_, h.2.1, ?_⟩
      · intro r
        obtain ⟨n, w, hw⟩ := h.1 r
        obtain ⟨m, hm⟩ := (eq r w).mpr ⟨n, hw⟩
        exact ⟨m, w, hm⟩
      · intro r a b hab
        apply ih (u := .app (u.rename r) a)
        · apply head_app
          intro s w
          simpa only [Term.rename_comp] using eq (fun i => s (r i)) w
        · exact h.2.2 r a b hab

private theorem related_head_right {E k t u v} (eq : HeadEq E t u) (h : Related E k v u) :
    Related E k v t := related_symm (related_head_left eq (related_symm h))

private theorem neutral_zero {n E t u} (applications : TermApplications t) (notSucc : t ≠ .succ)
    (run : reduceTermNeutral n E t = .ok u) : reduceTerm n E 0 t = .ok u := by
  cases n with
  | zero => simp [reduceTermNeutral, exhausted, fail] at run
  | succ n =>
      simp only [reduceTermNeutral, CheckResult.bind_eq_ok] at run
      obtain ⟨w, hw, run⟩ := run
      have := whnfTerm_fixed applications.whnf hw
      subst w
      simp only [reduceTerm, CheckResult.bind_eq_ok]
      refine ⟨t, hw, ?_⟩
      cases applications with
      | bvar => exact run
      | parameter => exact run
      | succ => exact False.elim (notSucc rfl)
      | app h => cases h <;> exact run

private theorem neutral_app_run {E f a F A n m} (applications : TermApplications f)
    (hf : reduceTermNeutral n E f = .ok F) (ha : reduceTerm m E 0 a = .ok A) :
    ∃ l, reduceTermNeutral l E (.app f a) = .ok (.app F A) := by
  obtain ⟨j, hj⟩ := whnfTerm_complete (TermApplications.app applications).whnf
  refine ⟨max j (max n m) + 1, ?_⟩
  simp only [reduceTermNeutral, CheckResult.bind_eq_ok]
  refine ⟨.app f a, whnfTerm_mono (by omega) hj, ?_⟩
  simp only [CheckResult.bind_eq_ok]
  exact ⟨F, reduceTermNeutral_mono (by omega) hf, A, reduceTerm_mono (by omega) ha, rfl⟩

private theorem reflected {E k f g} (valid : EnvironmentWF E) (sf : TermApplications f)
    (sg : TermApplications g) (nf : f ≠ .succ) (ng : g ≠ .succ)
    (runs : ∀ r, ∃ n m v, reduceTermNeutral n E (f.rename r) = .ok v ∧
      reduceTermNeutral m E (g.rename r) = .ok v) : Related E k f g := by
  induction k generalizing f g with
  | zero =>
      obtain ⟨n, m, v, hf, hg⟩ := runs id
      simp only [Term.rename_id] at hf hg
      exact ⟨n, m, v, neutral_zero sf nf hf, neutral_zero sg ng hg⟩
  | succ k ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro r
        obtain ⟨n, hn⟩ := whnfTerm_complete (sf.rename r).whnf
        exact ⟨n, _, hn⟩
      · intro r
        obtain ⟨n, hn⟩ := whnfTerm_complete (sg.rename r).whnf
        exact ⟨n, _, hn⟩
      · intro r a b hab
        apply ih (TermApplications.app (sf.rename r)) (TermApplications.app (sg.rename r))
          (by intro h; cases h) (by intro h; cases h)
        intro s
        obtain ⟨n, m, v, hf, hg⟩ := runs (fun i => s (r i))
        have nums := related_rename (k := 0) valid hab s
        obtain ⟨l, j, w, ha, hb⟩ := nums
        rw [← Term.rename_comp] at hf hg
        obtain ⟨p, hp⟩ := neutral_app_run ((sf.rename r).rename s) hf ha
        obtain ⟨q, hq⟩ := neutral_app_run ((sg.rename r).rename s) hg hb
        refine ⟨p, q, .app v w, ?_, ?_⟩
        · simpa only [Term.rename] using hp
        · simpa only [Term.rename] using hq

private theorem variable_related (E : Environment) (valid : EnvironmentWF E) (i k : Nat) :
    Related E k (.bvar i) (.bvar i) := by
  apply reflected valid .bvar .bvar (by intro h; cases h) (by intro h; cases h)
  intro r
  refine ⟨2, 2, .bvar (r i), ?_, ?_⟩ <;>
    simp [reduceTermNeutral, whnfTerm, Term.rename, pure, Except.pure]

private theorem parameter_related (E : Environment) (valid : EnvironmentWF E) (i k : Nat) :
    Related E k (.parameter i) (.parameter i) := by
  apply reflected valid .parameter .parameter (by intro h; cases h) (by intro h; cases h)
  intro r
  refine ⟨2, 2, .parameter i, ?_, ?_⟩ <;>
    simp [reduceTermNeutral, whnfTerm, Term.rename, pure, Except.pure]

private theorem head_from_run {E t w n} (valid : EnvironmentWF E)
    (run : whnfTerm n E t = .ok w) : HeadEq E t w := by
  intro r v
  have renamed := whnfTerm_rename valid run r
  have normal := whnfTerm_normal renamed
  constructor
  · rintro ⟨m, hm⟩
    have : v = w.rename r := whnfTerm_unique hm renamed
    subst v
    exact whnfTerm_complete normal
  · rintro ⟨m, hm⟩
    have : v = w.rename r := whnfTerm_fixed normal hm
    subst v
    exact ⟨n, renamed⟩

private theorem beta_runs {E t a v} :
    (∃ n, whnfTerm n E (.app (.lam binderName t) a) = .ok v) ↔
      ∃ n, whnfTerm n E (t.subst0 a) = .ok v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [whnfTerm, exhausted, fail] at hn
    | succ n =>
        simp only [whnfTerm, CheckResult.bind_eq_ok] at hn
        obtain ⟨f, hf, hn⟩ := hn
        have := whnfTerm_fixed TermWhnf.lam hf
        subst f
        exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨max n 1 + 1, ?_⟩
    simp only [whnfTerm, CheckResult.bind_eq_ok]
    refine ⟨.lam binderName t, ?_, whnfTerm_mono (Nat.le_max_left _ _) hn⟩
    cases h : max n 1 with
    | zero => have := Nat.le_max_right n 1; omega
    | succ m => simp [whnfTerm, pure, Except.pure]

private theorem head_beta (E : Environment) (t a : Term) :
    HeadEq E (.app (.lam binderName t) a) (t.subst0 a) := by
  intro r v
  simpa only [Term.rename, Term.rename_subst0] using
    (beta_runs (E := E) (t := t.rename (Renaming.lift 1 r)) (a := a.rename r) (v := v))

private theorem head_zeta (E : Environment) (t a : Term) :
    HeadEq E (.letE binderName a t) (t.subst0 a) := by
  intro r v
  simp only [Term.rename, Term.rename_subst0]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [whnfTerm, exhausted, fail] at hn
    | succ n => exact ⟨n, by simpa only [whnfTerm] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa only [whnfTerm] using hn⟩

private theorem head_delta {E name d} (lookup : E[name]? = some (.function d))
    (body : TermTyping E { functions := d.functions } [] d.body d.arity) (fs : List Term) :
    HeadEq E (.definition name fs) (d.body.instantiate fs) := by
  intro r v
  simp only [Term.rename, body.instantiate_rename]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [whnfTerm, exhausted, fail] at hn
    | succ n => exact ⟨n, by simpa only [whnfTerm, Environment.lookup, lookup] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa only [whnfTerm, Environment.lookup, lookup] using hn⟩

private theorem zero_inv {E t n} (run : reduceTerm n E 0 t = .ok .zero) :
    ∃ m, whnfTerm m E t = .ok .zero := by
  cases n with
  | zero => simp [reduceTerm, exhausted, fail] at run
  | succ n =>
      rw [reduce_zero] at run
      obtain ⟨w, hw, hf⟩ := CheckResult.bind_eq_ok.mp run
      cases w <;> simp only [Finish, pure, Except.pure,
        Except.ok.injEq, fail] at hf <;> try contradiction
      case zero => exact ⟨n, hw⟩
      case app f a =>
        cases f <;> simp [CheckResult.bind_eq_ok] at hf

private theorem succ_inv {E t v n} (run : reduceTerm n E 0 t = .ok (.app .succ v)) :
    ∃ m p j, whnfTerm m E t = .ok (.app .succ p) ∧ j < n ∧ reduceTerm j E 0 p = .ok v := by
  cases n with
  | zero => simp [reduceTerm, exhausted, fail] at run
  | succ n =>
      rw [reduce_zero] at run
      obtain ⟨w, hw, hf⟩ := CheckResult.bind_eq_ok.mp run
      have head := whnfTerm_normal hw
      cases w <;> simp only [Finish, pure, Except.pure,
        Except.ok.injEq, fail] at hf <;> try contradiction
      case app f a =>
        cases f <;> simp only [CheckResult.bind_eq_ok,
          Except.ok.injEq] at hf
        case primrec base step =>
          obtain ⟨_, _, _, _, _, _, eq⟩ := hf
          cases eq
        all_goals
          obtain ⟨g, hg, b, hb, eq⟩ := hf
          obtain ⟨ef, ea⟩ := Term.app.inj eq
          subst g; subst b
          cases head with
          | app head notLam notRec =>
              have eqf := (reduceTermNeutral_succ_iff head hg).mp rfl
              cases eqf <;> exact ⟨n, a, n, hw, by omega, hb⟩

private theorem finish_reduce {E w v n} (head : TermWhnf w) (run : Finish n E w = .ok v) :
    ∃ m, reduceTerm m E 0 w = .ok v := by
  obtain ⟨j, hj⟩ := whnfTerm_complete head
  refine ⟨max n j + 1, ?_⟩
  rw [reduce_zero]
  exact CheckResult.bind_eq_ok.mpr ⟨w, whnfTerm_mono (by omega) hj, finish_mono (by omega) run⟩

private theorem blocked_inv {E t v n} (blocked : TermBlocked v)
    (run : reduceTerm n E 0 t = .ok v) :
    ∃ m w j, whnfTerm m E t = .ok w ∧ TermBlocked w ∧ reduceTerm j E 0 w = .ok v := by
  cases n with
  | zero => simp [reduceTerm, exhausted, fail] at run
  | succ n =>
      rw [reduce_zero] at run
      obtain ⟨w, hw, hf⟩ := CheckResult.bind_eq_ok.mp run
      have head := whnfTerm_normal hw
      obtain ⟨j, hj⟩ := finish_reduce head hf
      refine ⟨n, w, j, hw, ?_, hj⟩
      cases w <;> simp only [Finish, pure, Except.pure,
        Except.ok.injEq, fail] at hf <;> try contradiction
      case zero => subst v; exact False.elim (blocked.1 rfl)
      case app f a =>
        cases f <;> simp only [CheckResult.bind_eq_ok,
          Except.ok.injEq] at hf
        case primrec base step =>
          constructor
          · intro h; cases h
          · intro p h; cases h
        all_goals
          obtain ⟨g, hg, b, hb, eq⟩ := hf
          subst v
          cases head with
          | app hf notLam notRec =>
              constructor
              · intro h; cases h
              · intro p h
                have eqf := (Term.app.inj h).1
                cases eqf
                all_goals
                  have : g = .succ := (reduceTermNeutral_succ_iff .succ hg).mpr rfl
                  subst g
                  exact blocked.2 b rfl
      all_goals
        constructor
        · intro h; cases h
        · intro p h; cases h

private theorem whnf_rec (n E b s a) :
    whnfTerm (n + 2) E (.app (.primrec b s) a) = (do
      let a ← whnfTerm (n + 1) E a
      match a with
      | .zero => whnfTerm (n + 1) E b
      | .app .succ p => whnfTerm (n + 1) E (.app (.app s p) (.app (.primrec b s) p))
      | _ => pure (.app (.primrec b s) a)) := rfl

private theorem rec_zero_runs {E b s a n v} (arg : whnfTerm n E a = .ok .zero) :
    (∃ m, whnfTerm m E (.app (.primrec b s) a) = .ok v) ↔ ∃ m, whnfTerm m E b = .ok v := by
  constructor
  · rintro ⟨m, hm⟩
    cases m with
    | zero => simp [whnfTerm, exhausted, fail] at hm
    | succ m =>
        cases m with
        | zero => simp [whnfTerm, exhausted, fail] at hm
        | succ m =>
          rw [whnf_rec] at hm
          simp only [CheckResult.bind_eq_ok] at hm
          obtain ⟨w, hw, hm⟩ := hm
          have : w = .zero := whnfTerm_unique hw arg
          subst w
          exact ⟨m + 1, hm⟩
  · rintro ⟨m, hm⟩
    refine ⟨max n m + 2, ?_⟩
    rw [whnf_rec]
    simp only [CheckResult.bind_eq_ok]
    exact ⟨.zero, whnfTerm_mono (by omega) arg, whnfTerm_mono (by omega) hm⟩

private theorem rec_succ_runs {E b s a p n v} (arg : whnfTerm n E a = .ok (.app .succ p)) :
    (∃ m, whnfTerm m E (.app (.primrec b s) a) = .ok v) ↔
      ∃ m, whnfTerm m E (.app (.app s p) (.app (.primrec b s) p)) = .ok v := by
  constructor
  · rintro ⟨m, hm⟩
    cases m with
    | zero => simp [whnfTerm, exhausted, fail] at hm
    | succ m =>
        cases m with
        | zero => simp [whnfTerm, exhausted, fail] at hm
        | succ m =>
          rw [whnf_rec] at hm
          simp only [CheckResult.bind_eq_ok] at hm
          obtain ⟨w, hw, hm⟩ := hm
          have : w = .app .succ p := whnfTerm_unique hw arg
          subst w
          exact ⟨m + 1, hm⟩
  · rintro ⟨m, hm⟩
    refine ⟨max n m + 2, ?_⟩
    rw [whnf_rec]
    simp only [CheckResult.bind_eq_ok]
    exact ⟨.app .succ p, whnfTerm_mono (by omega) arg, whnfTerm_mono (by omega) hm⟩

private theorem head_rec_zero {E b s a n} (valid : EnvironmentWF E)
    (arg : whnfTerm n E a = .ok .zero) : HeadEq E (.app (.primrec b s) a) b := by
  intro r v
  have renamed := whnfTerm_rename valid arg r
  simp only [Term.rename] at renamed ⊢
  exact rec_zero_runs renamed

private theorem head_rec_succ {E b s a p n} (valid : EnvironmentWF E)
    (arg : whnfTerm n E a = .ok (.app .succ p)) :
    HeadEq E (.app (.primrec b s) a) (.app (.app s p) (.app (.primrec b s) p)) := by
  intro r v
  have renamed := whnfTerm_rename valid arg r
  simp only [Term.rename] at renamed ⊢
  exact rec_succ_runs renamed

private theorem blocked_rec_run {E b s a w B S A n j k l}
    (arg : whnfTerm n E a = .ok w) (blocked : TermBlocked w)
    (base : reduceTerm j E 0 b = .ok B) (step : reduceTerm k E 2 s = .ok S)
    (value : reduceTerm l E 0 w = .ok A) :
    ∃ m, reduceTerm m E 0 (.app (.primrec b s) a) = .ok (.app (.primrec B S) A) := by
  have head : whnfTerm (n + 2) E (.app (.primrec b s) a) = .ok (.app (.primrec b s) w) := by
    rw [whnf_rec]
    simp only [CheckResult.bind_eq_ok]
    refine ⟨w, whnfTerm_mono (Nat.le_succ n) arg, ?_⟩
    split
    next => exact False.elim (blocked.1 rfl)
    next => exact False.elim (blocked.2 _ rfl)
    next => rfl
  refine ⟨max (n + 2) (max j (max k l)) + 1, ?_⟩
  rw [reduce_zero]
  apply CheckResult.bind_eq_ok.mpr
  refine ⟨.app (.primrec b s) w, whnfTerm_mono (by omega) head, ?_⟩
  simp only [Finish, CheckResult.bind_eq_ok]
  exact ⟨B, reduceTerm_mono (by omega) base, S, reduceTerm_mono (by omega) step,
    A, reduceTerm_mono (by omega) value, rfl⟩

private theorem rec_related {E b c s t a d} (valid : EnvironmentWF E)
    (base : Related E 0 b c) (step : Related E 2 s t) (arg : Related E 0 a d) :
    Related E 0 (.app (.primrec b s) a) (.app (.primrec c t) d) := by
  obtain ⟨n, m, v, ha, hd⟩ := arg
  suffices ∀ q n m a d v, n + m = q → reduceTerm n E 0 a = .ok v →
      reduceTerm m E 0 d = .ok v → Related E 0 (.app (.primrec b s) a) (.app (.primrec c t) d) from
    this (n + m) n m a d v rfl ha hd
  intro q
  induction q using Nat.strongRecOn with
  | ind q ih =>
      intro n m a d v sum ha hd
      by_cases zero : v = .zero
      · subst v
        obtain ⟨j, hj⟩ := zero_inv ha
        obtain ⟨k, hk⟩ := zero_inv hd
        exact related_head_left (head_rec_zero valid hj)
          (related_head_right (head_rec_zero valid hk) base)
      · by_cases successor : ∃ w, v = .app .succ w
        · obtain ⟨w, rfl⟩ := successor
          obtain ⟨j, p, l, hj, hl, hp⟩ := succ_inv ha
          obtain ⟨k, r, i, hk, hi, hr⟩ := succ_inv hd
          have recursive := ih (l + i) (by omega) l i p r w rfl hp hr
          have applied := step.2.2 id p r ⟨l, i, w, hp, hr⟩
          simp only [Term.rename_id] at applied
          have result := applied.2.2 id _ _ recursive
          simp only [Term.rename_id] at result
          exact related_head_left (head_rec_succ valid hj)
            (related_head_right (head_rec_succ valid hk) result)
        · have blocked : TermBlocked v := ⟨zero, by intro w hw; exact successor ⟨w, hw⟩⟩
          obtain ⟨j, p, l, hj, bp, hp⟩ := blocked_inv blocked ha
          obtain ⟨k, r, i, hk, br, hr⟩ := blocked_inv blocked hd
          obtain ⟨x, y, B, hb, hc⟩ := base
          obtain ⟨z, o, S, hs, ht⟩ := related_normalize step
          obtain ⟨u, hu⟩ := blocked_rec_run hj bp hb hs hp
          obtain ⟨w, hw⟩ := blocked_rec_run hk br hc ht hr
          exact ⟨u, w, .app (.primrec B S) v, hu, hw⟩

private theorem recursor_related {E b c s t} (valid : EnvironmentWF E)
    (base : Related E 0 b c) (step : Related E 2 s t) :
    Related E 1 (.primrec b s) (.primrec c t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r; exact ⟨1, .primrec (b.rename r) (s.rename r),
      by simp [Term.rename, whnfTerm, pure, Except.pure]⟩
  · intro r; exact ⟨1, .primrec (c.rename r) (t.rename r),
      by simp [Term.rename, whnfTerm, pure, Except.pure]⟩
  · intro r a d arg
    simp only [Term.rename]
    exact rec_related valid (related_rename valid base r) (related_rename valid step r) arg

private theorem successor_related {E} (valid : EnvironmentWF E) : Related E 1 .succ .succ := by
  refine ⟨?_, ?_, ?_⟩
  · intro r; exact ⟨1, .succ, by simp [Term.rename, whnfTerm, pure, Except.pure]⟩
  · intro r; exact ⟨1, .succ, by simp [Term.rename, whnfTerm, pure, Except.pure]⟩
  · intro r a b hab
    simp only [Term.rename]
    apply reflected valid (TermApplications.app .succ) (TermApplications.app .succ)
      (by intro h; cases h) (by intro h; cases h)
    intro q
    obtain ⟨n, m, v, ha, hb⟩ := related_rename (k := 0) valid hab q
    have succRun : reduceTermNeutral 2 E .succ = .ok .succ := by
      simp [reduceTermNeutral, whnfTerm, pure, Except.pure]
    obtain ⟨i, hi⟩ := neutral_app_run .succ succRun ha
    obtain ⟨j, hj⟩ := neutral_app_run .succ succRun hb
    refine ⟨i, j, .app .succ v, ?_, ?_⟩
    · simpa only [Term.rename] using hi
    · simpa only [Term.rename] using hj

private inductive RelatedArguments (E : Environment) : List Term → List Term → List Arity → Prop
  | nil : RelatedArguments E [] [] []
  | cons (head : Related E k t u) (tail : RelatedArguments E ts us ks) :
      RelatedArguments E (t :: ts) (u :: us) (k :: ks)

private theorem arguments_lookup {E fs gs ks} (h : RelatedArguments E fs gs ks)
    {i : Nat} {k : Arity} (lookup : ks[i]? = some k) :
    ∃ a b, fs[i]? = some a ∧ gs[i]? = some b ∧ Related E k a b := by
  induction h generalizing i with
  | nil => simp at lookup
  | cons head tail ih =>
      cases i with
      | zero => have := Option.some.inj lookup; subst k; exact ⟨_, _, rfl, rfl, head⟩
      | succ i => exact ih lookup

private abbrev GlobalRelated (E F : Environment) : Prop :=
  ∀ name d, E[name]? = some (.function d) → ∀ fs gs,
    RelatedArguments F fs gs d.functions →
      Related F d.arity (.definition name fs) (.definition name gs)

private abbrev IndexRelated (E : Environment) (ks : List Arity) (s u : Subst) : Prop :=
  ∀ i k, ks[i]? = some k → Related E k (s i) (u i)

private theorem term_fundamental {E F Ξ Γ t k} (valid : EnvironmentWF F)
    (globals : GlobalRelated E F) (typed : TermTyping E Ξ Γ t k) (s u p q : Subst)
    (locals : IndexRelated F Γ s u) (parameters : IndexRelated F Ξ.functions p q) :
    Related F k (t.replace s p) (t.replace u q) := by
  induction typed using TermTyping.rec
    (motive_2 := fun Γ fs ks _ => ∀ s u p q : Subst,
      IndexRelated F Γ s u → IndexRelated F Ξ.functions p q →
      RelatedArguments F (fs.map (Term.replace s p)) (fs.map (Term.replace u q)) ks)
    generalizing s u p q with
  | bvar lookup => simp only [Term.replace]; exact locals _ _ lookup
  | parameter lookup => simp only [Term.replace]; exact parameters _ _ lookup
  | zero =>
      simp only [Term.replace]
      exact ⟨2, 2, .zero, by simp [reduceTerm, whnfTerm, pure, Except.pure],
        by simp [reduceTerm, whnfTerm, pure, Except.pure]⟩
  | succ => simp only [Term.replace]; exact successor_related valid
  | @lam Γ bodyExpr k hint body ih =>
      simp only [Term.replace]
      refine ⟨?_, ?_, ?_⟩
      · intro r
        refine ⟨1, .lam hint ((bodyExpr.replace (Subst.lift 1 s) (fun i => (p
            i).shift)).rename
          (Renaming.lift 1 r)), ?_⟩
        simp [Term.rename, whnfTerm, pure, Except.pure]
      · intro r
        refine ⟨1, .lam hint ((bodyExpr.replace (Subst.lift 1 u) (fun i => (q
            i).shift)).rename
          (Renaming.lift 1 r)), ?_⟩
        simp [Term.rename, whnfTerm, pure, Except.pure]
      · intro r a b hab
        simp only [Term.rename]
        apply related_head_left (head_beta F _ a)
        apply related_head_right (head_beta F _ b)
        rw [Term.replace_beta_rename, Term.replace_beta_rename]
        apply ih
        · intro i j hi
          cases i with
          | zero => have : j = 0 := (Option.some.inj hi).symm; subst j; exact hab
          | succ i => exact related_rename valid (locals i j hi) r
        · intro i j hi
          exact related_rename valid (parameters i j hi) r
  | app f a ihf iha =>
      simp only [Term.replace]
      have result := (ihf s u p q locals parameters).2.2 id _ _ (iha s u p q locals parameters)
      simpa only [Term.rename_id] using result
  | letE a body iha ihb =>
      simp only [Term.replace]
      apply related_head_left (head_zeta F _ _)
      apply related_head_right (head_zeta F _ _)
      rw [Term.replace_beta, Term.replace_beta]
      apply ihb
      · intro i j hi
        cases i with
        | zero =>
            have hj := Option.some.inj hi
            subst j
            exact iha s u p q locals parameters
        | succ i => exact locals i j hi
      · exact parameters
  | primrec b f ihb ihf =>
      simp only [Term.replace]
      exact recursor_related valid (ihb s u p q locals parameters)
        (ihf s u p q locals parameters)
  | definition lookup args ih =>
      simp only [Term.replace]
      exact globals _ _ lookup _ _ (ih s u p q locals parameters)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i s u p q locals parameters
      simp only [List.map_cons]
      exact .cons (ihh s u p q locals parameters) (iht s u p q locals parameters)

private theorem globals_fundamental {E} (valid : EnvironmentWF E) :
    ∀ F, EnvironmentWF F → EnvironmentExtends E F → GlobalRelated E F := by
  induction valid with
  | empty => intro F vf ext name d lookup; simp at lookup
  | @insert E declaration valid fresh wellformed ih =>
      intro F vf ext name d lookup fs gs args
      have previous : EnvironmentExtends E F := (EnvironmentExtends.insert fresh).trans ext
      by_cases eq : declaration.name = name
      · subst name
        have eqd : declaration = .function d := Option.some.inj (by simpa using lookup)
        subst declaration
        cases wellformed with
        | function body =>
            have computed := term_fundamental vf (ih F vf previous) body
              Term.bvar Term.bvar (fun i => fs[i]?.getD (.parameter i))
              (fun i => gs[i]?.getD (.parameter i)) (by intro i j hi; simp at hi) (by
                intro i k hi
                obtain ⟨a, b, ha, hb, rel⟩ := arguments_lookup args hi
                simpa only [ha, hb, Option.getD_some] using rel)
            rw [body.replace_instantiate fs _ (by intros; rfl),
              body.replace_instantiate gs _ (by intros; rfl)] at computed
            have finalBody := body.weakenEnvironment previous
            have finalLookup := ext d.name (.function d) (by simp [Declaration.name])
            exact related_head_left (head_delta finalLookup finalBody fs)
              (related_head_right (head_delta finalLookup finalBody gs) computed)
      · have old : E[name]? = some (.function d) := by
          simpa [Std.ExtHashMap.getElem?_insert, eq] using lookup
        exact ih F vf previous name d old fs gs args

private theorem typed_related {E Ξ Γ t k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) : Related E k t t := by
  have globals := globals_fundamental valid E valid (.refl E)
  have related := term_fundamental valid globals typed Term.bvar Term.bvar
    Term.parameter Term.parameter (by intro i j hi; exact variable_related E valid i j)
    (by intro i j hi; exact parameter_related E valid i j)
  simpa only [Term.replace_id] using related

private theorem typed_substitutions {E Ξ Γ t k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) (s u : Subst) (locals : IndexRelated E Γ s u) :
    Related E k (t.subst s) (t.subst u) := by
  have globals := globals_fundamental valid E valid (.refl E)
  have related := term_fundamental valid globals typed s u Term.parameter Term.parameter locals
    (by intro i j hi; exact parameter_related E valid i j)
  have replace_subst (t : Term) (s : Subst) : t.replace s Term.parameter = t.subst s := by
    have h := Term.replace_subst t Term.bvar Term.parameter s
    simpa only [Term.replace_id, Term.subst] using h.symm
  simpa only [replace_subst] using related

private theorem index_symm {E Γ s u} (h : IndexRelated E Γ s u) : IndexRelated E Γ u s := by
  intro i j hi
  exact related_symm (h i j hi)

private theorem index_left {E Γ s u} (h : IndexRelated E Γ s u) : IndexRelated E Γ s s := by
  intro i j hi
  exact related_trans (h i j hi) (related_symm (h i j hi))

private theorem index_right {E Γ s u} (h : IndexRelated E Γ s u) : IndexRelated E Γ u u :=
  index_left (index_symm h)

private theorem index_cons {E Γ s u a b k} (h : IndexRelated E Γ s u)
    (ab : Related E k a b) :
    IndexRelated E (k :: Γ) (fun | 0 => a | i + 1 => s i)
      (fun | 0 => b | i + 1 => u i) := by
  intro i j hi
  cases i with
  | zero => have eq := Option.some.inj hi; subst j; exact ab
  | succ i => exact h i j hi

private theorem eta_related {E k f g} (h : Related E (k + 1) f g) :
    Related E (k + 1) (.lam binderName (.app f.shift (.bvar 0))) g := by
  refine ⟨?_, h.2.1, ?_⟩
  · intro r
    exact ⟨1, .lam binderName ((Term.app f.shift (.bvar 0)).rename (Renaming.lift
        1 r)),
      by simp [Term.rename, whnfTerm, pure, Except.pure]⟩
  · intro r a b hab
    simp only [Term.rename]
    apply related_head_left (head_beta E _ a)
    simp only [Term.rename_shift, Renaming.lift, Nat.zero_lt_one, ↓reduceIte]
    have beta : ((f.rename r).shift.app (.bvar 0)).subst0 a =
        .app ((f.rename r).shift.subst0 a) a := by
      simp [Term.subst0, Term.subst]
    rw [beta]
    rw [Term.subst0_shift]
    exact h.2.2 r a b hab

private theorem equality_fundamental {E Ξ Γ t v k} (valid : EnvironmentWF E)
    (eq : TermEq E Ξ Γ t v k) : ∀ s u, IndexRelated E Γ s u →
    Related E k (t.subst s) (v.subst u) := by
  induction eq using TermEq.rec
    (motive_2 := fun Γ ts us ks _ => ∀ s u, IndexRelated E Γ s u →
      RelatedArguments E (ts.map (Term.subst s)) (us.map (Term.subst u)) ks) with
  | refl typing => exact typed_substitutions valid typing
  | symm eq ih =>
      intro s u locals
      exact related_symm (ih u s (index_symm locals))
  | trans left right ihl ihr =>
      intro s u locals
      exact related_trans (ihl s u locals) (ihr u u (index_right locals))
  | beta body argument =>
      intro s u locals
      simp only [Term.subst, Term.subst0_subst]
      apply related_head_left (head_beta E _ _)
      rw [Term.subst_lift_subst0, Term.subst_lift_subst0]
      exact typed_substitutions valid body _ _
        (index_cons locals (typed_substitutions valid argument s u locals))
  | @eta Γ f k hint function =>
      intro s u locals
      have h := eta_related (binderName := hint) (typed_substitutions valid function s u locals)
      simpa [Term.subst, Term.subst_shift, Subst.lift] using h
  | zeta value body =>
      intro s u locals
      simp only [Term.subst, Term.subst0_subst]
      apply related_head_left (head_zeta E _ _)
      rw [Term.subst_lift_subst0, Term.subst_lift_subst0]
      exact typed_substitutions valid body _ _
        (index_cons locals (typed_substitutions valid value s u locals))
  | delta lookup arguments body =>
      intro s u locals
      have stored := (valid.lookup lookup).2
      cases stored with
      | function stored =>
          have computed := typed_substitutions valid body s u locals
          rw [stored.instantiate_subst, stored.instantiate_subst] at computed
          simp only [Term.subst, stored.instantiate_subst]
          exact related_head_left (head_delta lookup stored _) computed
  | primrecZero base step =>
      intro s u locals
      simp only [Term.subst]
      exact related_head_left (head_rec_zero valid
        (by simp [whnfTerm, pure, Except.pure] : whnfTerm 1 E .zero = .ok .zero))
        (typed_substitutions valid base s u locals)
  | @primrecSucc Γ baseExpr stepExpr argExpr base step arg =>
      intro s u locals
      simp only [Term.subst]
      apply related_head_left (head_rec_succ valid
        (by simp [whnfTerm, pure, Except.pure] :
          whnfTerm 2 E (.app .succ (Term.subst s argExpr)) =
            .ok (.app .succ (Term.subst s argExpr))))
      have steps := typed_substitutions valid step s u locals
      have args := typed_substitutions valid arg s u locals
      have recs := rec_related valid (typed_substitutions valid base s u locals) steps args
      have step1 := steps.2.2 id _ _ args
      have step2 := step1.2.2 id _ _ recs
      simpa only [Term.rename_id] using step2
  | @lam Γ t v k hint otherHint body ih =>
      intro s u locals
      simp only [Term.subst]
      refine ⟨?_, ?_, ?_⟩
      · intro r
        exact ⟨1, .lam hint ((t.subst (Subst.lift 1 s)).rename (Renaming.lift 1 r)),
          by simp [Term.rename, whnfTerm, pure, Except.pure]⟩
      · intro r
        exact ⟨1, .lam otherHint ((v.subst (Subst.lift 1 u)).rename (Renaming.lift
            1 r)),
          by simp [Term.rename, whnfTerm, pure, Except.pure]⟩
      · intro r a b hab
        simp only [Term.rename]
        apply related_head_left (head_beta E _ a)
        apply related_head_right (head_beta E _ b)
        rw [Term.subst_beta_rename, Term.subst_beta_rename]
        exact ih _ _ (index_cons (fun i j hi => related_rename valid (locals i j hi) r) hab)
  | app function argument ihf iha =>
      intro s u locals
      simp only [Term.subst]
      simpa only [Term.rename_id] using (ihf s u locals).2.2 id _ _ (iha s u locals)
  | letE value body ihv ihb =>
      intro s u locals
      simp only [Term.subst]
      apply related_head_left (head_zeta E _ _)
      apply related_head_right (head_zeta E _ _)
      rw [Term.subst_lift_subst0, Term.subst_lift_subst0]
      exact ihb _ _ (index_cons locals (ihv s u locals))
  | primrec base step ihb ihs =>
      intro s u locals
      simp only [Term.subst]
      exact recursor_related valid (ihb s u locals) (ihs s u locals)
  | definition lookup arguments ih =>
      intro s u locals
      simp only [Term.subst]
      exact globals_fundamental valid E valid (.refl E) _ _ lookup _ _ (ih s u locals)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i s u locals
      exact .cons (ihh s u locals) (iht s u locals)

private def PFinish (n : Nat) (E : Environment) : Predicate → CheckResult Predicate
  | .false => pure .false
  | .true => pure .true
  | .equal a b => return .equal (← reduceTerm n E 0 a) (← reduceTerm n E 0 b)
  | .imp A B => return .imp (← reducePredicate n E 0 A) (← reducePredicate n E 0 B)
  | .and A B => return .and (← reducePredicate n E 0 A) (← reducePredicate n E 0 B)
  | .or A B => return .or (← reducePredicate n E 0 A) (← reducePredicate n E 0 B)
  | .all P => return .all (← reducePredicate n E 1 P)
  | .ex P => return .ex (← reducePredicate n E 1 P)
  | .parameter i => pure (.parameter i)
  | .app P a => return .app (← reducePredicateNeutral n E P) (← reduceTerm n E 0 a)
  | P => fail (.expectedForm .formula (.predicate P))

private theorem predicate_zero (n E P) : reducePredicate (n + 1) E 0 P =
    (do let Q ← whnfPredicate n E P; PFinish n E Q) := by
  simp only [reducePredicate, PFinish]
  congr 1
  funext Q
  cases Q <;> rfl

private theorem pfinish_mono {n m E P Q} (le : n ≤ m) (run : PFinish n E P = .ok Q) :
    PFinish m E P = .ok Q := by
  cases P <;> simp only [PFinish, CheckResult.bind_eq_ok, fail] at run ⊢ <;> try contradiction
  case equal a b =>
    obtain ⟨c, hc, d, hd, eq⟩ := run
    exact ⟨c, reduceTerm_mono le hc, d, reduceTerm_mono le hd, eq⟩
  case imp A B =>
    obtain ⟨C, hC, D, hD, eq⟩ := run
    exact ⟨C, reducePredicate_mono le hC, D, reducePredicate_mono le hD, eq⟩
  case and A B =>
    obtain ⟨C, hC, D, hD, eq⟩ := run
    exact ⟨C, reducePredicate_mono le hC, D, reducePredicate_mono le hD, eq⟩
  case or A B =>
    obtain ⟨C, hC, D, hD, eq⟩ := run
    exact ⟨C, reducePredicate_mono le hC, D, reducePredicate_mono le hD, eq⟩
  case all P => obtain ⟨R, hR, eq⟩ := run; exact ⟨R, reducePredicate_mono le hR, eq⟩
  case ex P => obtain ⟨R, hR, eq⟩ := run; exact ⟨R, reducePredicate_mono le hR, eq⟩
  case app P a =>
    obtain ⟨R, hR, b, hb, eq⟩ := run
    exact ⟨R, reducePredicateNeutral_mono le hR, b, reduceTerm_mono le hb, eq⟩
  all_goals exact run

private abbrev PHeadEq (E : Environment) (P Q : Predicate) : Prop :=
  ∀ r R, (∃ n, whnfPredicate n E (P.rename r) = .ok R) ↔
    (∃ n, whnfPredicate n E (Q.rename r) = .ok R)

private theorem ptransfer_zero {E P Q R n}
    (heads : ∀ S, (∃ m, whnfPredicate m E P = .ok S) →
      ∃ m, whnfPredicate m E Q = .ok S)
    (run : reducePredicate n E 0 P = .ok R) : ∃ m, reducePredicate m E 0 Q = .ok R := by
  cases n with
  | zero => simp [reducePredicate, exhausted, fail] at run
  | succ n =>
      rw [predicate_zero] at run
      obtain ⟨S, hS, hf⟩ := CheckResult.bind_eq_ok.mp run
      obtain ⟨m, hm⟩ := heads S ⟨n, hS⟩
      refine ⟨max n m + 1, ?_⟩
      rw [predicate_zero]
      exact CheckResult.bind_eq_ok.mpr ⟨S, whnfPredicate_mono (by omega) hm,
        pfinish_mono (by omega) hf⟩

private theorem ptransfer_app {E P Q a R n}
    (heads : ∀ S, (∃ m, whnfPredicate m E P = .ok S) →
      ∃ m, whnfPredicate m E Q = .ok S)
    (run : whnfPredicate n E (.app P a) = .ok R) :
    ∃ m, whnfPredicate m E (.app Q a) = .ok R := by
  cases n with
  | zero => simp [whnfPredicate, exhausted, fail] at run
  | succ n =>
      simp only [whnfPredicate, CheckResult.bind_eq_ok] at run
      obtain ⟨S, hS, run⟩ := run
      obtain ⟨m, hm⟩ := heads S ⟨n, hS⟩
      refine ⟨max n m + 1, ?_⟩
      simp only [whnfPredicate, CheckResult.bind_eq_ok]
      refine ⟨S, whnfPredicate_mono (by omega) hm, ?_⟩
      cases S <;> first | exact whnfPredicate_mono (by omega) run | exact run

private theorem phead_app {E P Q} (eq : PHeadEq E P Q) (a : Term) :
    PHeadEq E (.app P a) (.app Q a) := by
  intro r R
  simp only [Predicate.rename]
  constructor
  · rintro ⟨n, hn⟩; exact ptransfer_app (fun S h => (eq r S).mp h) hn
  · rintro ⟨n, hn⟩; exact ptransfer_app (fun S h => (eq r S).mpr h) hn

private abbrev FormulaRelated (E : Environment) (P Q : Predicate) : Prop :=
  ∃ n m R, reducePredicate n E 0 P = .ok R ∧ reducePredicate m E 0 Q = .ok R

private def PRelated (E : Environment) : Nat → Predicate → Predicate → Prop
  | 0, P, Q => FormulaRelated E P Q
  | k + 1, P, Q =>
      (∀ r, ∃ n R, whnfPredicate n E (P.rename r) = .ok R) ∧
      (∀ r, ∃ n R, whnfPredicate n E (Q.rename r) = .ok R) ∧
      ∀ r a b, NumberRelated E a b → PRelated E k (.app (P.rename r) a) (.app (Q.rename r) b)
termination_by structural k _ _ => k

private theorem prelated_symm {E k P Q} (h : PRelated E k P Q) : PRelated E k Q P := by
  induction k generalizing P Q with
  | zero => obtain ⟨n, m, R, hP, hQ⟩ := h; exact ⟨m, n, R, hQ, hP⟩
  | succ k ih =>
      refine ⟨h.2.1, h.1, ?_⟩
      intro r a b hab
      obtain ⟨n, m, v, ha, hb⟩ := hab
      exact ih (h.2.2 r b a ⟨m, n, v, hb, ha⟩)

private theorem prelated_normalize {E k P Q} (h : PRelated E k P Q) :
    ∃ n m R, reducePredicate n E k P = .ok R ∧ reducePredicate m E k Q = .ok R := by
  induction k generalizing P Q with
  | zero => exact h
  | succ k ih =>
      have var : NumberRelated E (.bvar 0) (.bvar 0) :=
        ⟨2, 2, .bvar 0, by simp [reduceTerm, whnfTerm, pure, Except.pure],
          by simp [reduceTerm, whnfTerm, pure, Except.pure]⟩
      obtain ⟨n, m, R, hP, hQ⟩ := ih (h.2.2 (fun i => i + 1) _ _ var)
      refine ⟨n + 1, m + 1, .lam .anonymous R, ?_, ?_⟩ <;>
        simp only [reducePredicate, CheckResult.bind_eq_ok]
      · exact ⟨R, hP, rfl⟩
      · exact ⟨R, hQ, rfl⟩

private theorem prelated_head_left {E k P Q R} (eq : PHeadEq E P Q)
    (h : PRelated E k Q R) : PRelated E k P R := by
  induction k generalizing P Q R with
  | zero =>
      obtain ⟨n, m, S, hQ, hR⟩ := h
      have heads : ∀ S, (∃ m, whnfPredicate m E Q = .ok S) →
          ∃ m, whnfPredicate m E P = .ok S := by
        intro S hS
        simpa only [Predicate.rename_id] using
          (eq id S).mpr (by simpa only [Predicate.rename_id] using hS)
      obtain ⟨l, hP⟩ := ptransfer_zero heads hQ
      exact ⟨l, m, S, hP, hR⟩
  | succ k ih =>
      refine ⟨?_, h.2.1, ?_⟩
      · intro r
        obtain ⟨n, S, hS⟩ := h.1 r
        obtain ⟨m, hm⟩ := (eq r S).mpr ⟨n, hS⟩
        exact ⟨m, S, hm⟩
      · intro r a b hab
        apply ih (Q := .app (Q.rename r) a)
        · apply phead_app
          intro s S
          simpa only [Predicate.rename_comp] using eq (fun i => s (r i)) S
        · exact h.2.2 r a b hab

private theorem prelated_head_right {E k P Q R} (eq : PHeadEq E P Q)
    (h : PRelated E k R Q) : PRelated E k R P :=
  prelated_symm (prelated_head_left eq (prelated_symm h))

private theorem phead_beta (E : Environment) (P : Predicate) (a : Term) :
    PHeadEq E (.app (.lam binderName P) a) (P.subst0 a) := by
  intro r R
  simp only [Predicate.rename, Predicate.rename_subst0]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [whnfPredicate, exhausted, fail] at hn
    | succ n =>
        simp only [whnfPredicate, CheckResult.bind_eq_ok] at hn
        obtain ⟨Q, hQ, hn⟩ := hn
        have := whnfPredicate_fixed PredicateWhnf.lam hQ
        subst Q
        exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨max n 1 + 1, ?_⟩
    simp only [whnfPredicate, CheckResult.bind_eq_ok]
    refine ⟨.lam binderName (P.rename (Renaming.lift 1 r)), ?_, whnfPredicate_mono
        (by omega) hn⟩
    cases h : max n 1 with
    | zero => have := Nat.le_max_right n 1; omega
    | succ m => simp [whnfPredicate, pure, Except.pure]

private theorem phead_letTerm (E : Environment) (a : Term) (P : Predicate) :
    PHeadEq E (.letTerm binderName a P) P := by
  intro r R
  simp only [Predicate.rename]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [whnfPredicate, exhausted, fail] at hn
    | succ n => exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, hn⟩

private theorem phead_letPredicate (E : Environment) (Q P : Predicate) :
    PHeadEq E (.letPredicate binderName Q P) P := by
  intro r R
  simp only [Predicate.rename]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [whnfPredicate, exhausted, fail] at hn
    | succ n => exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, hn⟩

private theorem phead_delta {E name d} (lookup : E[name]? = some (.predicate d))
    (body : PredicateTyping E { functions := d.functions, predicates := d.predicates }
      [] d.body d.signature) (fs : List Term) (ps : List Predicate) :
    PHeadEq E (.definition name fs ps) (d.body.instantiate fs ps) := by
  intro r R
  simp only [Predicate.rename, body.instantiate_rename]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [whnfPredicate, exhausted, fail] at hn
    | succ n => exact ⟨n, by simpa only [whnfPredicate, Environment.lookup, lookup] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa only [whnfPredicate, Environment.lookup, lookup] using hn⟩

private theorem pneutral_zero {n E P Q} (applications : PredicateApplications P)
    (run : reducePredicateNeutral n E P = .ok Q) : reducePredicate n E 0 P = .ok Q := by
  cases n with
  | zero => simp [reducePredicateNeutral, exhausted, fail] at run
  | succ n =>
      simp only [reducePredicateNeutral, CheckResult.bind_eq_ok] at run
      obtain ⟨R, hR, run⟩ := run
      have := whnfPredicate_fixed applications.whnf hR
      subst R
      simp only [reducePredicate, CheckResult.bind_eq_ok]
      refine ⟨P, hR, ?_⟩
      cases applications <;> exact run

private theorem pneutral_app_run {E P a Q A n m} (applications : PredicateApplications P)
    (hP : reducePredicateNeutral n E P = .ok Q) (ha : reduceTerm m E 0 a = .ok A) :
    ∃ l, reducePredicateNeutral l E (.app P a) = .ok (.app Q A) := by
  obtain ⟨j, hj⟩ := whnfPredicate_complete (PredicateApplications.app applications).whnf
  refine ⟨max j (max n m) + 1, ?_⟩
  simp only [reducePredicateNeutral, CheckResult.bind_eq_ok]
  refine ⟨.app P a, whnfPredicate_mono (by omega) hj, ?_⟩
  simp only [CheckResult.bind_eq_ok]
  exact ⟨Q, reducePredicateNeutral_mono (by omega) hP, A, reduceTerm_mono (by omega) ha, rfl⟩

private theorem preflected {E k P Q} (valid : EnvironmentWF E)
    (sP : PredicateApplications P) (sQ : PredicateApplications Q)
    (runs : ∀ r, ∃ n m R, reducePredicateNeutral n E (P.rename r) = .ok R ∧
      reducePredicateNeutral m E (Q.rename r) = .ok R) : PRelated E k P Q := by
  induction k generalizing P Q with
  | zero =>
      obtain ⟨n, m, R, hP, hQ⟩ := runs id
      simp only [Predicate.rename_id] at hP hQ
      exact ⟨n, m, R, pneutral_zero sP hP, pneutral_zero sQ hQ⟩
  | succ k ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro r
        obtain ⟨n, hn⟩ := whnfPredicate_complete (sP.rename r).whnf
        exact ⟨n, _, hn⟩
      · intro r
        obtain ⟨n, hn⟩ := whnfPredicate_complete (sQ.rename r).whnf
        exact ⟨n, _, hn⟩
      · intro r a b hab
        apply ih (PredicateApplications.app (sP.rename r)) (PredicateApplications.app (sQ.rename r))
        intro s
        obtain ⟨n, m, R, hP, hQ⟩ := runs (fun i => s (r i))
        obtain ⟨l, j, w, ha, hb⟩ := related_rename (k := 0) valid hab s
        rw [← Predicate.rename_comp] at hP hQ
        obtain ⟨p, hp⟩ := pneutral_app_run ((sP.rename r).rename s) hP ha
        obtain ⟨q, hq⟩ := pneutral_app_run ((sQ.rename r).rename s) hQ hb
        refine ⟨p, q, .app R w, ?_, ?_⟩
        · simpa only [Predicate.rename] using hp
        · simpa only [Predicate.rename] using hq

private theorem pfinish_reduce {E P Q n} (head : PredicateWhnf P)
    (run : PFinish n E P = .ok Q) : ∃ m, reducePredicate m E 0 P = .ok Q := by
  obtain ⟨j, hj⟩ := whnfPredicate_complete head
  refine ⟨max n j + 1, ?_⟩
  rw [predicate_zero]
  exact CheckResult.bind_eq_ok.mpr ⟨P, whnfPredicate_mono (by omega) hj,
    pfinish_mono (by omega) run⟩

private theorem equal_related {E a b c d} (left : NumberRelated E a b)
    (right : NumberRelated E c d) : PRelated E 0 (.equal a c) (.equal b d) := by
  obtain ⟨n, m, v, ha, hb⟩ := left
  obtain ⟨j, l, w, hc, hd⟩ := right
  obtain ⟨p, hp⟩ := pfinish_reduce PredicateWhnf.equal (n := max n j)
    (CheckResult.bind_eq_ok.mpr ⟨v, reduceTerm_mono (by omega) ha,
      CheckResult.bind_eq_ok.mpr ⟨w, reduceTerm_mono (by omega) hc, rfl⟩⟩)
  obtain ⟨q, hq⟩ := pfinish_reduce PredicateWhnf.equal (n := max m l)
    (CheckResult.bind_eq_ok.mpr ⟨v, reduceTerm_mono (by omega) hb,
      CheckResult.bind_eq_ok.mpr ⟨w, reduceTerm_mono (by omega) hd, rfl⟩⟩)
  exact ⟨p, q, .equal v w, hp, hq⟩

private theorem imp_related {E A B C D} (left : PRelated E 0 A C)
    (right : PRelated E 0 B D) : PRelated E 0 (.imp A B) (.imp C D) := by
  obtain ⟨n, m, P, hA, hC⟩ := left
  obtain ⟨j, l, Q, hB, hD⟩ := right
  obtain ⟨p, hp⟩ := pfinish_reduce PredicateWhnf.imp (n := max n j)
    (CheckResult.bind_eq_ok.mpr ⟨P, reducePredicate_mono (by omega) hA,
      CheckResult.bind_eq_ok.mpr ⟨Q, reducePredicate_mono (by omega) hB, rfl⟩⟩)
  obtain ⟨q, hq⟩ := pfinish_reduce PredicateWhnf.imp (n := max m l)
    (CheckResult.bind_eq_ok.mpr ⟨P, reducePredicate_mono (by omega) hC,
      CheckResult.bind_eq_ok.mpr ⟨Q, reducePredicate_mono (by omega) hD, rfl⟩⟩)
  exact ⟨p, q, .imp P Q, hp, hq⟩

private theorem and_related {E A B C D} (left : PRelated E 0 A C)
    (right : PRelated E 0 B D) : PRelated E 0 (.and A B) (.and C D) := by
  obtain ⟨n, m, P, hA, hC⟩ := left
  obtain ⟨j, l, Q, hB, hD⟩ := right
  obtain ⟨p, hp⟩ := pfinish_reduce PredicateWhnf.and (n := max n j)
    (CheckResult.bind_eq_ok.mpr ⟨P, reducePredicate_mono (by omega) hA,
      CheckResult.bind_eq_ok.mpr ⟨Q, reducePredicate_mono (by omega) hB, rfl⟩⟩)
  obtain ⟨q, hq⟩ := pfinish_reduce PredicateWhnf.and (n := max m l)
    (CheckResult.bind_eq_ok.mpr ⟨P, reducePredicate_mono (by omega) hC,
      CheckResult.bind_eq_ok.mpr ⟨Q, reducePredicate_mono (by omega) hD, rfl⟩⟩)
  exact ⟨p, q, .and P Q, hp, hq⟩

private theorem or_related {E A B C D} (left : PRelated E 0 A C)
    (right : PRelated E 0 B D) : PRelated E 0 (.or A B) (.or C D) := by
  obtain ⟨n, m, P, hA, hC⟩ := left
  obtain ⟨j, l, Q, hB, hD⟩ := right
  obtain ⟨p, hp⟩ := pfinish_reduce PredicateWhnf.or (n := max n j)
    (CheckResult.bind_eq_ok.mpr ⟨P, reducePredicate_mono (by omega) hA,
      CheckResult.bind_eq_ok.mpr ⟨Q, reducePredicate_mono (by omega) hB, rfl⟩⟩)
  obtain ⟨q, hq⟩ := pfinish_reduce PredicateWhnf.or (n := max m l)
    (CheckResult.bind_eq_ok.mpr ⟨P, reducePredicate_mono (by omega) hC,
      CheckResult.bind_eq_ok.mpr ⟨Q, reducePredicate_mono (by omega) hD, rfl⟩⟩)
  exact ⟨p, q, .or P Q, hp, hq⟩

private theorem all_related {E P Q} (body : PRelated E 1 P Q) :
    PRelated E 0 (.all P) (.all Q) := by
  obtain ⟨n, m, R, hP, hQ⟩ := prelated_normalize body
  obtain ⟨p, hp⟩ := pfinish_reduce PredicateWhnf.all
    (CheckResult.bind_eq_ok.mpr ⟨R, hP, rfl⟩)
  obtain ⟨q, hq⟩ := pfinish_reduce PredicateWhnf.all
    (CheckResult.bind_eq_ok.mpr ⟨R, hQ, rfl⟩)
  exact ⟨p, q, .all R, hp, hq⟩

private theorem ex_related {E P Q} (body : PRelated E 1 P Q) :
    PRelated E 0 (.ex P) (.ex Q) := by
  obtain ⟨n, m, R, hP, hQ⟩ := prelated_normalize body
  obtain ⟨p, hp⟩ := pfinish_reduce PredicateWhnf.ex
    (CheckResult.bind_eq_ok.mpr ⟨R, hP, rfl⟩)
  obtain ⟨q, hq⟩ := pfinish_reduce PredicateWhnf.ex
    (CheckResult.bind_eq_ok.mpr ⟨R, hQ, rfl⟩)
  exact ⟨p, q, .ex R, hp, hq⟩

private theorem prelated_trans {E k P Q R} (h : PRelated E k P Q) (g : PRelated E k Q R) :
    PRelated E k P R := by
  induction k generalizing P Q R with
  | zero =>
      obtain ⟨n, m, A, hP, hQ⟩ := h
      obtain ⟨l, j, B, hQ', hR⟩ := g
      have eq := reducePredicate_unique hQ hQ'
      subst B
      exact ⟨n, j, A, hP, hR⟩
  | succ k ih =>
      refine ⟨h.1, g.2.1, ?_⟩
      intro r a b hab
      obtain ⟨n, m, v, ha, hb⟩ := hab
      exact ih (h.2.2 r a a ⟨n, n, v, ha, ha⟩) (g.2.2 r a b ⟨n, m, v, ha, hb⟩)

private theorem prelated_rename {E k P Q} (valid : EnvironmentWF E) (h : PRelated E k P Q)
    (r : Renaming) : PRelated E k (P.rename r) (Q.rename r) := by
  cases k with
  | zero =>
      obtain ⟨n, m, R, hP, hQ⟩ := h
      exact ⟨n, m, R.rename r, reducePredicate_rename valid hP r, reducePredicate_rename valid hQ r⟩
  | succ k =>
      simp only [PRelated, Predicate.rename_comp]
      exact ⟨fun s => h.1 (fun i => s (r i)), fun s => h.2.1 (fun i => s (r i)),
        fun s a b hab => h.2.2 (fun i => s (r i)) a b hab⟩

private inductive PRelatedArguments (E : Environment) :
    List Predicate → List Predicate → List PredicateSignature → Prop
  | nil : PRelatedArguments E [] [] []
  | cons (head : PRelated E σ.arity P Q) (tail : PRelatedArguments E ps qs signatures) :
      PRelatedArguments E (P :: ps) (Q :: qs) (σ :: signatures)

private abbrev PIndexRelated (E : Environment) (ks : List PredicateSignature)
    (p q : Nat → Predicate) : Prop := ∀ i σ, ks[i]? = some σ → PRelated E σ.arity (p i) (q i)

private abbrev PGlobalRelated (E F : Environment) : Prop :=
  ∀ name d, E[name]? = some (.predicate d) → ∀ fs gs ps qs,
    RelatedArguments F fs gs d.functions → PRelatedArguments F ps qs d.predicates →
    PRelated F d.signature.arity (.definition name fs ps) (.definition name gs qs)

private theorem predicate_parameter_related (E : Environment) (valid : EnvironmentWF E) (i k) :
    PRelated E k (.parameter i) (.parameter i) := by
  apply preflected valid .parameter .parameter
  intro r
  exact ⟨2, 2, .parameter i,
    by simp [Predicate.rename, reducePredicateNeutral, whnfPredicate, pure, Except.pure],
    by simp [Predicate.rename, reducePredicateNeutral, whnfPredicate, pure, Except.pure]⟩

private theorem term_arguments_related {E F Ξ Γ fs ks} (valid : EnvironmentWF F)
    (globals : GlobalRelated E F) (args : FunctionArguments E Ξ Γ fs ks) (s u p q : Subst)
    (locals : IndexRelated F Γ s u) (functions : IndexRelated F Ξ.functions p q) :
    RelatedArguments F (fs.map (Term.replace s p)) (fs.map (Term.replace u q)) ks := by
  induction args using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True) with
  | nil => exact .nil
  | cons head tail ihh iht =>
      exact .cons (term_fundamental valid globals head s u p q locals functions)
        (iht locals)
  | _ => trivial

private theorem predicate_full {E F Ξ Γ P σ} (valid : EnvironmentWF F)
    (globals : GlobalRelated E F) (pglobals : PGlobalRelated E F)
    (typed : PredicateTyping E Ξ Γ P σ) : ∀ s u p q pp qq,
    IndexRelated F Γ s u → IndexRelated F Ξ.functions p q →
    PIndexRelated F Ξ.predicates pp qq →
    PRelated F σ.arity (P.replace s p pp) (P.replace u q qq) := by
  induction typed using PredicateTyping.rec
    (motive_2 := fun Γ ps signatures _ => ∀ s u p q pp qq,
      IndexRelated F Γ s u → IndexRelated F Ξ.functions p q →
      PIndexRelated F Ξ.predicates pp qq → PRelatedArguments F
        (ps.map (Predicate.replace s p pp)) (ps.map (Predicate.replace u q qq)) signatures) with
  | false =>
      intro s u p q pp qq locals functions predicates
      exact ⟨2, 2, .false, by simp [Predicate.replace, reducePredicate, whnfPredicate,
        pure, Except.pure], by simp [Predicate.replace, reducePredicate, whnfPredicate,
        pure, Except.pure]⟩
  | true =>
      intro s u p q pp qq locals functions predicates
      exact ⟨2, 2, .true, by simp [Predicate.replace, reducePredicate, whnfPredicate,
        pure, Except.pure], by simp [Predicate.replace, reducePredicate, whnfPredicate,
        pure, Except.pure]⟩
  | equal a b =>
      intro s u p q pp qq locals functions predicates
      simp only [Predicate.replace]
      exact equal_related (term_fundamental valid globals a s u p q locals functions)
        (term_fundamental valid globals b s u p q locals functions)
  | imp a b iha ihb =>
      intro s u p q pp qq locals functions predicates
      simp only [Predicate.replace]
      exact imp_related (iha s u p q pp qq locals functions predicates)
        (ihb s u p q pp qq locals functions predicates)
  | and a b iha ihb =>
      intro s u p q pp qq locals functions predicates
      simp only [Predicate.replace]
      exact and_related (iha s u p q pp qq locals functions predicates)
        (ihb s u p q pp qq locals functions predicates)
  | or a b iha ihb =>
      intro s u p q pp qq locals functions predicates
      simp only [Predicate.replace]
      exact or_related (iha s u p q pp qq locals functions predicates)
        (ihb s u p q pp qq locals functions predicates)
  | all body ih =>
      intro s u p q pp qq locals functions predicates
      simp only [Predicate.replace]
      exact all_related (ih s u p q pp qq locals functions predicates)
  | ex body ih =>
      intro s u p q pp qq locals functions predicates
      simp only [Predicate.replace]
      exact ex_related (ih s u p q pp qq locals functions predicates)
  | parameter lookup =>
      intro s u p q pp qq locals functions predicates
      simp only [Predicate.replace]
      exact predicates _ _ lookup
  | @lam Γ P k sort hint body ih =>
      intro s u p q pp qq locals functions predicates
      simp only [Predicate.replace]
      refine ⟨?_, ?_, ?_⟩
      · intro r
        exact ⟨1, .lam hint ((P.replace (Subst.lift 1 s) (fun i => (p i).shift)
          (fun i => (pp i).shift)).rename (Renaming.lift 1 r)),
          by simp [Predicate.rename, whnfPredicate, pure, Except.pure]⟩
      · intro r
        exact ⟨1, .lam hint ((P.replace (Subst.lift 1 u) (fun i => (q i).shift)
          (fun i => (qq i).shift)).rename (Renaming.lift 1 r)),
          by simp [Predicate.rename, whnfPredicate, pure, Except.pure]⟩
      · intro r a b hab
        simp only [Predicate.rename]
        apply prelated_head_left (phead_beta F _ a)
        apply prelated_head_right (phead_beta F _ b)
        rw [Predicate.replace_beta_rename, Predicate.replace_beta_rename]
        apply ih
        · exact index_cons (fun i j hi => related_rename valid (locals i j hi) r) hab
        · intro i j hi; exact related_rename valid (functions i j hi) r
        · intro i j hi; exact prelated_rename valid (predicates i j hi) r
  | app function argument ih =>
      intro s u p q pp qq locals functions predicates
      simp only [Predicate.replace]
      simpa only [Predicate.rename_id] using
        (ih s u p q pp qq locals functions predicates).2.2 id _ _
          (term_fundamental valid globals argument s u p q locals functions)
  | letTerm value body ih =>
      intro s u p q pp qq locals functions predicates
      simp only [Predicate.replace]
      apply prelated_head_left (phead_letTerm F _ _)
      apply prelated_head_right (phead_letTerm F _ _)
      exact ih s u p q pp qq locals functions predicates
  | letPredicate value body ihv ihb =>
      intro s u p q pp qq locals functions predicates
      simp only [Predicate.replace]
      apply prelated_head_left (phead_letPredicate F _ _)
      apply prelated_head_right (phead_letPredicate F _ _)
      exact ihb s u p q pp qq locals functions predicates
  | definition lookup args preds ihp =>
      intro s u p q pp qq locals functions predicates
      simp only [Predicate.replace]
      exact pglobals _ _ lookup _ _ _ _
        (term_arguments_related valid globals args s u p q locals functions)
        (ihp s u p q pp qq locals functions predicates)
  | subsumption typing sub ih =>
      intro s u p q pp qq locals functions predicates
      rw [← sub.arity_eq]
      exact ih s u p q pp qq locals functions predicates
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i s u p q pp qq locals functions predicates
      exact .cons (ihh s u p q pp qq locals functions predicates)
        (iht s u p q pp qq locals functions predicates)

private theorem parguments_lookup {E ps qs signatures}
    (h : PRelatedArguments E ps qs signatures) {i : Nat} {σ}
    (hi : signatures[i]? = some σ) :
    ∃ P Q, ps[i]? = some P ∧ qs[i]? = some Q ∧ PRelated E σ.arity P Q := by
  induction h generalizing i with
  | nil => simp at hi
  | cons head tail ih =>
      cases i with
      | zero => have eq := Option.some.inj hi; subst σ; exact ⟨_, _, rfl, rfl, head⟩
      | succ i => exact ih hi

private theorem pglobals_fundamental {E} (valid : EnvironmentWF E) :
    ∀ F, EnvironmentWF F → EnvironmentExtends E F → PGlobalRelated E F := by
  induction valid with
  | empty => intro F vf ext name d lookup; simp at lookup
  | @insert E declaration valid fresh wellformed ih =>
      intro F vf ext name d lookup fs gs ps qs args pargs
      have previous : EnvironmentExtends E F := (EnvironmentExtends.insert fresh).trans ext
      by_cases eq : declaration.name = name
      · subst name
        have eqd : declaration = .predicate d := Option.some.inj (by simpa using lookup)
        subst declaration
        cases wellformed with
        | predicate body =>
            have computed := predicate_full vf (globals_fundamental valid F vf previous)
              (ih F vf previous) body Term.bvar Term.bvar
              (fun i => fs[i]?.getD (.parameter i)) (fun i => gs[i]?.getD (.parameter i))
              (fun i => ps[i]?.getD (.parameter i)) (fun i => qs[i]?.getD (.parameter i))
              (by intro i j hi; simp at hi) (by
                intro i k hi
                obtain ⟨a, b, ha, hb, rel⟩ := arguments_lookup args hi
                simpa only [ha, hb, Option.getD_some] using rel) (by
                intro i σ hi
                obtain ⟨P, Q, hP, hQ, rel⟩ := parguments_lookup pargs hi
                simpa only [hP, hQ, Option.getD_some] using rel)
            rw [body.replace_instantiate fs ps _ _ (by intros; rfl) (by intros; rfl),
              body.replace_instantiate gs qs _ _ (by intros; rfl) (by intros; rfl)] at computed
            have finalBody := body.weakenEnvironment previous
            have finalLookup := ext d.name (.predicate d) (by simp [Declaration.name])
            exact prelated_head_left (phead_delta finalLookup finalBody fs ps)
              (prelated_head_right (phead_delta finalLookup finalBody gs qs) computed)
      · have old : E[name]? = some (.predicate d) := by
          simpa [Std.ExtHashMap.getElem?_insert, eq] using lookup
        exact ih F vf previous name d old fs gs ps qs args pargs

private theorem predicate_fundamental {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) (s u : Subst) (locals : IndexRelated E Γ s u) :
    PRelated E σ.arity (P.subst s) (P.subst u) := by
  have rel := predicate_full valid (globals_fundamental valid E valid (.refl E))
    (pglobals_fundamental valid E valid (.refl E)) typed s u Term.parameter Term.parameter
    Predicate.parameter Predicate.parameter locals
    (by intro i j hi; exact parameter_related E valid i j)
    (by intro i σ hi; exact predicate_parameter_related E valid i σ.arity)
  have as_subst (P : Predicate) (s : Subst) :
      P.replace s Term.parameter Predicate.parameter = P.subst s := by
    have eq := Predicate.replace_subst P Term.bvar Term.parameter s Predicate.parameter
    simpa only [Predicate.replace_id, Term.subst, Predicate.subst] using eq.symm
  simpa only [as_subst] using rel

private theorem predicate_related {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) : PRelated E σ.arity P P := by
  have rel := predicate_fundamental valid typed Term.bvar Term.bvar
    (by intro i j hi; exact variable_related E valid i j)
  simpa only [Predicate.subst_id] using rel

private theorem equality_arguments {E Ξ Γ fs gs ks} (valid : EnvironmentWF E)
    (args : FunctionArgumentEq E Ξ Γ fs gs ks) (s u : Subst)
    (locals : IndexRelated E Γ s u) :
    RelatedArguments E (fs.map (Term.subst s)) (gs.map (Term.subst u)) ks := by
  induction args using FunctionArgumentEq.rec (motive_1 := fun _ _ _ _ _ => True) with
  | nil => exact .nil
  | cons head tail ihh iht =>
      exact .cons (equality_fundamental valid head s u locals) (iht locals)
  | _ => trivial

private theorem peta_related {E k P Q} (h : PRelated E (k + 1) P Q) :
    PRelated E (k + 1) (.lam binderName (.app P.shift (.bvar 0))) Q := by
  refine ⟨?_, h.2.1, ?_⟩
  · intro r
    exact ⟨1, .lam binderName ((Predicate.app P.shift (.bvar 0)).rename
        (Renaming.lift 1 r)),
      by simp [Predicate.rename, whnfPredicate, pure, Except.pure]⟩
  · intro r a b hab
    simp only [Predicate.rename]
    apply prelated_head_left (phead_beta E _ a)
    simp only [Predicate.rename_shift, Term.rename, Renaming.lift,
      Nat.zero_lt_one, ↓reduceIte]
    have beta : ((P.rename r).shift.app (.bvar 0)).subst0 a =
        .app ((P.rename r).shift.subst0 a) a := by
      simp [Predicate.subst0, Predicate.subst, Term.subst]
    rw [beta, Predicate.subst0_shift]
    exact h.2.2 r a b hab

private theorem predicate_equality_fundamental {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ P Q σ) : ∀ s u, IndexRelated E Γ s u →
    PRelated E σ.arity (P.subst s) (Q.subst u) := by
  induction eq using PredicateEq.rec
    (motive_2 := fun Γ ps qs signatures _ => ∀ s u, IndexRelated E Γ s u →
      PRelatedArguments E (ps.map (Predicate.subst s)) (qs.map (Predicate.subst u)) signatures) with
  | refl typing => exact predicate_fundamental valid typing
  | symm eq ih =>
      intro s u locals
      exact prelated_symm (ih u s (index_symm locals))
  | trans left right ihl ihr =>
      intro s u locals
      exact prelated_trans (ihl s u locals) (ihr u u (index_right locals))
  | subsumption eq sub ih =>
      intro s u locals
      rw [← sub.arity_eq]
      exact ih s u locals
  | beta body argument =>
      intro s u locals
      simp only [Predicate.subst, Predicate.subst0_subst]
      apply prelated_head_left (phead_beta E _ _)
      rw [Predicate.subst_lift_subst0, Predicate.subst_lift_subst0]
      exact predicate_fundamental valid body _ _
        (index_cons locals (typed_substitutions valid argument s u locals))
  | @eta Γ P k sort hint function =>
      intro s u locals
      have h := peta_related (binderName := hint) (predicate_fundamental valid function s u locals)
      simpa [Predicate.subst, Predicate.subst_shift, Subst.lift, Term.subst] using h
  | zetaTerm value body =>
      intro s u locals
      simp only [Predicate.subst]
      exact prelated_head_left (phead_letTerm E _ _)
        (predicate_fundamental valid body s u locals)
  | zetaPredicate value body =>
      intro s u locals
      simp only [Predicate.subst]
      exact prelated_head_left (phead_letPredicate E _ _)
        (predicate_fundamental valid body s u locals)
  | delta lookup functions predicates body bound =>
      intro s u locals
      have stored := (valid.lookup lookup).2
      cases stored with
      | predicate stored =>
          have computed := predicate_fundamental valid body s u locals
          rw [stored.instantiate_subst, stored.instantiate_subst] at computed
          simp only [Predicate.subst, stored.instantiate_subst]
          exact prelated_head_left (phead_delta lookup stored _ _) computed
  | equal left right =>
      intro s u locals
      simp only [Predicate.subst]
      exact equal_related (equality_fundamental valid left s u locals)
        (equality_fundamental valid right s u locals)
  | imp a b iha ihb =>
      intro s u locals
      simp only [Predicate.subst]
      exact imp_related (iha s u locals) (ihb s u locals)
  | and a b iha ihb =>
      intro s u locals
      simp only [Predicate.subst]
      exact and_related (iha s u locals) (ihb s u locals)
  | or a b iha ihb =>
      intro s u locals
      simp only [Predicate.subst]
      exact or_related (iha s u locals) (ihb s u locals)
  | all body ih =>
      intro s u locals
      simp only [Predicate.subst]
      exact all_related (ih s u locals)
  | ex body ih =>
      intro s u locals
      simp only [Predicate.subst]
      exact ex_related (ih s u locals)
  | @lam Γ P Q k sort hint otherHint body ih =>
      intro s u locals
      simp only [Predicate.subst]
      refine ⟨?_, ?_, ?_⟩
      · intro r
        exact ⟨1, .lam hint ((P.subst (Subst.lift 1 s)).rename (Renaming.lift 1 r)),
          by simp [Predicate.rename, whnfPredicate, pure, Except.pure]⟩
      · intro r
        exact ⟨1, .lam otherHint ((Q.subst (Subst.lift 1 u)).rename (Renaming.lift
            1 r)),
          by simp [Predicate.rename, whnfPredicate, pure, Except.pure]⟩
      · intro r a b hab
        simp only [Predicate.rename]
        apply prelated_head_left (phead_beta E _ a)
        apply prelated_head_right (phead_beta E _ b)
        rw [Predicate.subst_beta_rename, Predicate.subst_beta_rename]
        exact ih _ _ (index_cons (fun i j hi => related_rename valid (locals i j hi) r) hab)
  | app function argument ih =>
      intro s u locals
      simp only [Predicate.subst]
      simpa only [Predicate.rename_id] using
        (ih s u locals).2.2 id _ _ (equality_fundamental valid argument s u locals)
  | definition lookup functions predicates left right ih =>
      intro s u locals
      obtain ⟨d, hd, args, pargs, below⟩ := left.inv_definition
      have deq := Option.some.inj (hd.symm.trans lookup)
      cases deq
      have arity := below.arity_eq.symm
      simp only [Predicate.subst]
      rw [arity]
      exact pglobals_fundamental valid E valid (.refl E) _ _ lookup _ _ _ _
        (equality_arguments valid functions s u locals) (ih s u locals)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i s u locals
      exact .cons (ihh s u locals) (iht s u locals)

/-- Definitionally equal terms have a common normal form at every sufficiently large depth. -/
public theorem reduceTerm_of_eq {E Ξ Γ t u k} (valid : EnvironmentWF E)
    (eq : TermEq E Ξ Γ t u k) :
    ∃ n v, ∀ m ≥ n, reduceTerm m E k t = .ok v ∧ reduceTerm m E k u = .ok v := by
  have related := equality_fundamental valid eq Term.bvar Term.bvar
    (by intro i j hi; exact variable_related E valid i j)
  simp only [Term.subst_id] at related
  obtain ⟨n, m, v, ht, hu⟩ := related_normalize related
  exact ⟨max n m, v, fun j le =>
    ⟨reduceTerm_mono (by omega) ht, reduceTerm_mono (by omega) hu⟩⟩

/-- Definitionally equal predicates have a common normal form, independently of their sort. -/
public theorem reducePredicate_of_eq {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ P Q σ) :
    ∃ n R, ∀ m ≥ n,
      reducePredicate m E σ.arity P = .ok R ∧ reducePredicate m E σ.arity Q = .ok R := by
  have related := predicate_equality_fundamental valid eq Term.bvar Term.bvar
    (by intro i j hi; exact variable_related E valid i j)
  simp only [Predicate.subst_id] at related
  obtain ⟨n, m, R, hP, hQ⟩ := prelated_normalize related
  exact ⟨max n m, R, fun j le =>
    ⟨reducePredicate_mono (by omega) hP, reducePredicate_mono (by omega) hQ⟩⟩

/-- Successful normalizations of equal terms agree even when their depths differ. -/
public theorem reduceTerm_congr {E Ξ Γ t u k n m a b} (valid : EnvironmentWF E)
    (eq : TermEq E Ξ Γ t u k) (left : reduceTerm n E k t = .ok a)
    (right : reduceTerm m E k u = .ok b) : a = b := by
  obtain ⟨j, v, hv⟩ := reduceTerm_of_eq valid eq
  exact (reduceTerm_unique left (hv j (by omega)).1).trans
    (reduceTerm_unique right (hv j (by omega)).2).symm

/-- Successful normalizations of equal predicates agree at their shared arity. -/
public theorem reducePredicate_congr {E Ξ Γ P Q σ n m A B} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ P Q σ) (left : reducePredicate n E σ.arity P = .ok A)
    (right : reducePredicate m E σ.arity Q = .ok B) : A = B := by
  obtain ⟨j, R, hR⟩ := reducePredicate_of_eq valid eq
  exact (reducePredicate_unique left (hR j (by omega)).1).trans
    (reducePredicate_unique right (hR j (by omega)).2).symm

/-- Every well-typed numerical term successfully normalizes at some finite recursive depth,
and the returned syntax is stable at every larger budget. -/
public theorem reduceTerm_terminates {E Ξ Γ t k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) :
    ∃ n u, ∀ m ≥ n, reduceTerm m E k t = .ok u := by
  have related := typed_related valid typed
  obtain ⟨n, m, u, hn, hm⟩ := related_normalize related
  exact ⟨n, u, fun m le => reduceTerm_mono le hn⟩

/-- Every well-typed predicate successfully normalizes at its arity at all sufficiently
large recursive depths, with a fixed output independent of that depth. -/
public theorem reducePredicate_terminates {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) :
    ∃ n Q, ∀ m ≥ n, reducePredicate m E σ.arity P = .ok Q := by
  obtain ⟨n, m, Q, hn, hm⟩ := prelated_normalize (predicate_related valid typed)
  exact ⟨n, Q, fun m le => reducePredicate_mono le hn⟩

/-- Formula normalization succeeds at every depth beyond a finite bound. -/
public theorem reduceFormula_terminates {E Ξ Γ P s} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P ⟨0, s⟩) :
    ∃ n Q, ∀ m ≥ n, reduceFormula m E P = .ok Q :=
  reducePredicate_terminates valid typed

/-- Weak-head reduction succeeds on every well-typed numerical expression. -/
public theorem whnfTerm_terminates {E Ξ Γ t k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) :
    ∃ n u, ∀ m ≥ n, whnfTerm m E t = .ok u := by
  have related := typed_related valid typed
  have head : ∃ n u, whnfTerm n E t = .ok u := by
    cases k with
    | zero =>
        obtain ⟨n, m, u, hn, hm⟩ := related
        cases n with
        | zero => simp [reduceTerm, exhausted, fail] at hn
        | succ n =>
            rw [reduce_zero] at hn
            obtain ⟨w, hw, rest⟩ := CheckResult.bind_eq_ok.mp hn
            exact ⟨n, w, hw⟩
    | succ k => simpa only [Term.rename_id] using related.1 id
  obtain ⟨n, u, hn⟩ := head
  exact ⟨n, u, fun m le => whnfTerm_mono le hn⟩

/-- Weak-head reduction succeeds on every well-typed predicate expression. -/
public theorem whnfPredicate_terminates {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) :
    ∃ n Q, ∀ m ≥ n, whnfPredicate m E P = .ok Q := by
  have related := predicate_related valid typed
  have head : ∃ n Q, whnfPredicate n E P = .ok Q := by
    cases arity : σ.arity with
    | zero =>
        rw [arity] at related
        obtain ⟨n, m, Q, hn, hm⟩ := related
        cases n with
        | zero => simp [reducePredicate, exhausted, fail] at hn
        | succ n =>
            rw [predicate_zero] at hn
            obtain ⟨R, hR, rest⟩ := CheckResult.bind_eq_ok.mp hn
            exact ⟨n, R, hR⟩
    | succ k =>
        rw [arity] at related
        simpa only [Predicate.rename_id] using related.1 id
  obtain ⟨n, Q, hn⟩ := head
  exact ⟨n, Q, fun m le => whnfPredicate_mono le hn⟩

/-- A well-typed application chain headed by a local, function parameter, or successor has
sufficient depth for neutral reduction. -/
public theorem reduceTermNeutral_terminates {E Ξ Γ t k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ Γ t k) (applications : TermApplications t) :
    ∃ n u, ∀ m ≥ n, reduceTermNeutral m E t = .ok u := by
  suffices ∃ n u, reduceTermNeutral n E t = .ok u by
    obtain ⟨n, u, hn⟩ := this
    exact ⟨n, u, fun m le => reduceTermNeutral_mono le hn⟩
  induction applications generalizing k with
  | @bvar i => exact ⟨2, .bvar i, by simp [reduceTermNeutral, whnfTerm, pure, Except.pure]⟩
  | @parameter i =>
      exact ⟨2, .parameter i, by simp [reduceTermNeutral, whnfTerm, pure, Except.pure]⟩
  | succ => exact ⟨2, .succ, by simp [reduceTermNeutral, whnfTerm, pure, Except.pure]⟩
  | app head ih =>
      obtain ⟨function, argument⟩ := typed.inv_app
      obtain ⟨n, F, hF⟩ := ih function
      obtain ⟨m, A, hA⟩ := reduceTerm_terminates valid argument
      obtain ⟨j, hj⟩ := neutral_app_run head hF (hA m (by omega))
      exact ⟨j, _, hj⟩

/-- A well-typed application of a predicate parameter has sufficient depth for neutral reduction. -/
public theorem reducePredicateNeutral_terminates {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ Γ P σ) (applications : PredicateApplications P) :
    ∃ n Q, ∀ m ≥ n, reducePredicateNeutral m E P = .ok Q := by
  suffices ∃ n Q, reducePredicateNeutral n E P = .ok Q by
    obtain ⟨n, Q, hn⟩ := this
    exact ⟨n, Q, fun m le => reducePredicateNeutral_mono le hn⟩
  induction applications generalizing σ with
  | @parameter i =>
      exact ⟨2, .parameter i, by simp [reducePredicateNeutral, whnfPredicate, pure, Except.pure]⟩
  | app head ih =>
      obtain ⟨k, s, function, argument, bound⟩ := typed.inv_app
      obtain ⟨n, Q, hQ⟩ := ih function
      obtain ⟨m, A, hA⟩ := reduceTerm_terminates valid argument
      obtain ⟨j, hj⟩ := pneutral_app_run head hQ (hA m (by omega))
      exact ⟨j, _, hj⟩

end PRAProver.Core
