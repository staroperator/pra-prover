module

public import PRAProver.Metatheory.Core.Properties.Normalization.WeakHead
import PRAProver.Metatheory.Core.Judgement.Formation

/-!
# Finite computations for conversion completeness

Finite sequences of head reductions connect conversion batches to successful weak-head reduction.
The shared relations and lemmas support the completeness proof for structural conversion.

- `HeadSteps` counts reductions between two expressions.
- `HeadTrace` follows reductions to a stationary head.
- `HeadBatch` records a batch's progress and its optional output.
- `HeadTrace.induction_pair` permits progress along either of two traces.
- `exposeTerm_terminates` and `exposePredicate_terminates` give stable exposure results once
  sufficient depth is available.
-/

namespace PRAProver.Core

open Theory

/-- Take one head-reduction step in a term, returning `none` at a stationary head. -/
@[expose] public def termStep (E : Environment) : Term → CheckResult (Option Term)
  | .definition name fs =>
    match E.lookup name with
    | some (.function d) => pure (some (d.body.instantiate fs))
    | _ => referenceError E name .function
  | .letE _ value body => pure (some (body.subst0 value))
  | .app (.lam _ body) a => pure (some (body.subst0 a))
  | .app (.primrec b _) .zero => pure (some b)
  | .app (.primrec b s) (.app .succ n) => pure (some (.app (.app s n) (.app (.primrec b s) n)))
  | .app (.primrec b s) n => (termStep E n).map (Option.map (fun m => .app (.primrec b s) m))
  | .app f a => (termStep E f).map (Option.map (fun g => .app g a))
  | _ => pure none

/-- Take one head-reduction step in a predicate, returning `none` at a stationary head. -/
@[expose] public def predicateStep (E : Environment) : Predicate → CheckResult (Option Predicate)
  | .definition name fs ps =>
    match E.lookup name with
    | some (.predicate d) => pure (some (d.body.instantiate fs ps))
    | _ => referenceError E name .predicate
  | .letTerm _ _ body | .letPredicate _ _ body => pure (some body)
  | .app (.lam _ body) a => pure (some (body.subst0 a))
  | .app f a => (predicateStep E f).map (Option.map (fun g => .app g a))
  | _ => pure none

/-- A sequence of a specified number of head-reduction steps. -/
public inductive HeadSteps (step : α → CheckResult (Option α)) : Nat → α → α → Prop where
  | refl : HeadSteps step 0 a a
  | next (run : step a = .ok (some b)) (tail : HeadSteps step n b c) :
      HeadSteps step (n + 1) a c

private theorem HeadSteps.trans {step : α → CheckResult (Option α)} {n m a b c}
    (left : HeadSteps step n a b) (right : HeadSteps step m b c) :
    HeadSteps step (n + m) a c := by
  induction left with
  | refl => simpa using right
  | next run tail ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using HeadSteps.next run (ih right)

private theorem HeadSteps.map {step : α → CheckResult (Option α)}
    {other : β → CheckResult (Option β)} {f : α → β}
    (lift : ∀ {a b}, step a = .ok (some b) → other (f a) = .ok (some (f b)))
    {n a b} (steps : HeadSteps step n a b) : HeadSteps other n (f a) (f b) := by
  induction steps with
  | refl => exact .refl
  | next run _ ih => exact .next (lift run) ih

/-- A finite sequence of head reductions ending at a stationary head. -/
public inductive HeadTrace (step : α → CheckResult (Option α)) : α → α → Prop where
  | done (run : step a = .ok none) : HeadTrace step a a
  | next (run : step a = .ok (some b)) (tail : HeadTrace step b c) : HeadTrace step a c

private theorem HeadTrace.terminal {step : α → CheckResult (Option α)} {a b}
    (trace : HeadTrace step a b) : step b = .ok none := by
  induction trace with
  | done run => exact run
  | next _ _ ih => exact ih

private theorem HeadTrace.drop {step : α → CheckResult (Option α)} {n a b c}
    (trace : HeadTrace step a c) (steps : HeadSteps step n a b) : HeadTrace step b c := by
  induction steps with
  | refl => exact trace
  | next run tail ih =>
    cases trace with
    | done stop => simp [stop] at run
    | next run' rest =>
      have eq := run.symm.trans run'
      cases eq
      exact ih rest

public theorem HeadTrace.stationary {step : α → CheckResult (Option α)} {a b}
    (trace : HeadTrace step a b) (stop : step a = .ok none) : a = b := by
  cases trace with
  | done => rfl
  | next run _ => simp [stop] at run

public theorem HeadTrace.steps {step : α → CheckResult (Option α)} {a b}
    (trace : HeadTrace step a b) : ∃ n, HeadSteps step n a b := by
  induction trace with
  | done => exact ⟨0, .refl⟩
  | next run _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .next run h⟩

private theorem HeadTrace.map {step : α → CheckResult (Option α)}
    {other : β → CheckResult (Option β)} {f : α → β}
    (lift : ∀ {a b}, step a = .ok (some b) → other (f a) = .ok (some (f b)))
    {a b c} (trace : HeadTrace step a b) (tail : HeadTrace other (f b) c) :
    HeadTrace other (f a) c := by
  induction trace with
  | done _ => exact tail
  | next run _ ih => exact .next (lift run) (ih tail)

private theorem term_app_step {E f g a} (run : termStep E f = .ok (some g)) :
    termStep E (.app f a) = .ok (some (.app g a)) := by
  cases f with
  | lam | primrec => simp [termStep, pure, Except.pure] at run
  | _ => change (termStep E _).map _ = _; rw [run]; rfl

private theorem term_rec_step {E n m b s} (run : termStep E n = .ok (some m)) :
    termStep E (.app (.primrec b s) n) = .ok (some (.app (.primrec b s) m)) := by
  cases n with
  | zero => simp [termStep, pure, Except.pure] at run
  | app f a =>
    cases f with
    | succ => simp [termStep, Except.map, pure, Except.pure] at run
    | _ => change (termStep E _).map _ = _; rw [run]; rfl
  | _ => change (termStep E _).map _ = _; rw [run]; rfl

private theorem predicate_app_step {E f g a} (run : predicateStep E f = .ok (some g)) :
    predicateStep E (.app f a) = .ok (some (.app g a)) := by
  cases f with
  | lam => simp [predicateStep, pure, Except.pure] at run
  | _ => change (predicateStep E _).map _ = _; rw [run]; rfl

public theorem term_stationary {E t} (head : TermWhnf t) : termStep E t = .ok none := by
  induction head with
  | app hf notLam notRec ih =>
    cases hf with
    | lam => exact False.elim (notLam _ _ rfl)
    | recursor => exact False.elim (notRec _ _ rfl)
    | _ => change (termStep E _).map _ = _; rw [ih]; rfl
  | primrec hn blocked ih =>
    cases hn with
    | zero => exact False.elim (blocked.1 rfl)
    | app hf hnot hrec =>
      cases hf with
      | succ => exact False.elim (blocked.2 _ rfl)
      | _ => change (termStep E _).map _ = _; rw [ih]; rfl
    | _ => change (termStep E _).map _ = _; rw [ih]; rfl
  | _ => rfl

private theorem predicate_stationary {E P} (head : PredicateWhnf P) :
    predicateStep E P = .ok none := by
  induction head with
  | app hf notLam ih =>
    cases hf with
    | lam => exact False.elim (notLam _ _ rfl)
    | _ => change (predicateStep E _).map _ = _; rw [ih]; rfl
  | _ => rfl

public theorem whnfTerm_trace {n E t u} (run : whnfTerm n E t = .ok u) :
    HeadTrace (termStep E) t u := by
  induction n generalizing t u with
  | zero => simp [whnfTerm, exhausted, fail] at run
  | succ n ih =>
    cases t with
    | definition name fs =>
      simp only [whnfTerm] at run
      split at run
      next d lookup => exact .next (by simp [termStep, lookup, pure, Except.pure]) (ih run)
      next => simp [referenceError, fail] at run; split at run <;> contradiction
    | letE name value body => exact .next rfl (ih run)
    | app f a =>
      simp only [whnfTerm, CheckResult.bind_eq_ok] at run
      obtain ⟨g, hg, run⟩ := run
      apply HeadTrace.map (fun h => term_app_step h) (ih hg)
      cases g with
      | lam name body => exact .next rfl (ih run)
      | primrec b s =>
        simp only [CheckResult.bind_eq_ok] at run
        obtain ⟨m, hm, run⟩ := run
        apply HeadTrace.map (fun h => term_rec_step h) (ih hm)
        cases m with
        | zero => exact .next rfl (ih run)
        | app f p =>
          cases f with
          | succ => exact .next rfl (ih run)
          | _ =>
            simp only [pure, Except.pure, Except.ok.injEq] at run
            subst u
            exact .done (term_stationary (.primrec (whnfTerm_normal hm)
              (by constructor <;> intros <;> simp)))
        | _ =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst u
          exact .done (term_stationary (.primrec (whnfTerm_normal hm)
            (by constructor <;> intros <;> simp)))
      | _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at run
        subst u
        exact .done (term_stationary
          (.app (whnfTerm_normal hg) (by intros; simp) (by intros; simp)))
    | _ =>
      simp only [whnfTerm, pure, Except.pure, Except.ok.injEq] at run
      subst u; exact .done rfl

public theorem whnfPredicate_trace {n E P Q} (run : whnfPredicate n E P = .ok Q) :
    HeadTrace (predicateStep E) P Q := by
  induction n generalizing P Q with
  | zero => simp [whnfPredicate, exhausted, fail] at run
  | succ n ih =>
    cases P with
    | definition name fs ps =>
      simp only [whnfPredicate] at run
      split at run
      next d lookup => exact .next (by simp [predicateStep, lookup, pure, Except.pure]) (ih run)
      next => simp [referenceError, fail] at run; split at run <;> contradiction
    | letTerm | letPredicate => exact .next rfl (ih run)
    | app f a =>
      simp only [whnfPredicate, CheckResult.bind_eq_ok] at run
      obtain ⟨g, hg, run⟩ := run
      apply HeadTrace.map (fun h => predicate_app_step h) (ih hg)
      cases g with
      | lam name body => exact .next rfl (ih run)
      | _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at run
        subst Q
        exact .done (predicate_stationary
          (.app (whnfPredicate_normal hg) (by intros; simp)))
    | _ =>
      simp only [whnfPredicate, pure, Except.pure, Except.ok.injEq] at run
      subst Q; exact .done rfl

/-- A property of depth that holds at every depth above some bound. -/
@[expose] public def Eventually (p : Nat → Prop) : Prop := ∃ n, ∀ m ≥ n, p m

public theorem eventually_const {p : Prop} (h : p) : Eventually (fun _ => p) :=
  ⟨0, fun _ _ => h⟩

public theorem eventually_and {p q : Nat → Prop} (hp : Eventually p) (hq : Eventually q) :
    Eventually (fun n => p n ∧ q n) := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  exact ⟨max i j, fun m hm => ⟨hi m (by omega), hj m (by omega)⟩⟩

public theorem eventually_next {p q : Nat → Prop}
    (step : ∀ n, p n → q (n + 1)) (h : Eventually p) : Eventually q := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 1, ?_⟩
  intro m hm
  cases m with
  | zero => omega
  | succ m => exact step m (hn m (by omega))

public theorem eventually_mono {p q : Nat → Prop}
    (step : ∀ n, p n → q n) (h : Eventually p) : Eventually q := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun m hm => step m (hn m hm)⟩

/-- The steps represented by an optional batch result. A result starting with `changed = false`
must include at least one step when it returns `some`. -/
public inductive HeadBatch (step : α → CheckResult (Option α)) :
    Bool → α → Option α → Prop where
  | none : HeadBatch step false a none
  | some (steps : HeadSteps step n a b) (positive : changed = false → 0 < n) :
      HeadBatch step changed a (some b)

public theorem HeadBatch.steps {step : α → CheckResult (Option α)} {changed a result}
    (batch : HeadBatch step changed a result) :
    ∃ n, HeadSteps step n a (result.getD a) := by
  cases batch with
  | none => exact ⟨0, .refl⟩
  | some steps _ => exact ⟨_, steps⟩

private theorem HeadBatch.next {step : α → CheckResult (Option α)} {changed a b result}
    (run : step a = .ok (Option.some b)) (batch : HeadBatch step true b result) :
    HeadBatch step changed a result := by
  cases batch with
  | some steps _ => exact .some (.next run steps) (by omega)

public theorem exposeTerm_batch {n changed E a result}
    (run : exposeTerm n changed a = .ok result) : HeadBatch (termStep E) changed a result := by
  induction n generalizing changed a result with
  | zero => simp [exposeTerm, exhausted, fail] at run
  | succ n ih =>
    cases a with
    | letE name value body => exact (ih run).next rfl
    | app f a =>
      by_cases zero : ∃ b s, f = .primrec b s ∧ a = .zero
      · obtain ⟨b, s, rfl, rfl⟩ := zero
        exact (ih run).next rfl
      rw [exposeTerm_app_eq zero] at run
      simp only [CheckResult.bind_eq_ok] at run
      obtain ⟨g, hg, run⟩ := run
      have batch := ih hg
      obtain ⟨j, steps⟩ := batch.steps
      have mapped := steps.map (fun h => term_app_step (a := a) h)
      cases h : g.getD f with
      | lam name body =>
        simp only [h] at run
        have tail := ih run
        rw [h] at mapped
        cases tail with
        | some tail _ =>
          exact .some (mapped.trans (.next rfl tail)) (by omega)
      | _ =>
        simp only [h] at run
        cases batch with
        | none =>
          cases changed <;> simp only [pure, Except.pure, Bool.false_eq_true,
            ↓reduceIte, Except.ok.injEq] at run <;> subst result
          all_goals first | exact .none | exact .some .refl (by simp)
        | some more pos =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst result
          exact .some (more.map (fun h => term_app_step h)) (fun _ => pos rfl)
    | _ =>
      cases changed <;> simp only [exposeTerm, Bool.false_eq_true, ↓reduceIte,
        pure, Except.pure, Except.ok.injEq] at run <;> subst result
      all_goals first | exact .none | exact .some .refl (by simp)

public theorem exposePredicate_batch {n changed E a result}
    (run : exposePredicate n changed a = .ok result) :
    HeadBatch (predicateStep E) changed a result := by
  induction n generalizing changed a result with
  | zero => simp [exposePredicate, exhausted, fail] at run
  | succ n ih =>
    cases a with
    | letTerm | letPredicate => exact (ih run).next rfl
    | app f a =>
      simp only [exposePredicate, CheckResult.bind_eq_ok] at run
      obtain ⟨g, hg, run⟩ := run
      have batch := ih hg
      obtain ⟨j, steps⟩ := batch.steps
      have mapped := steps.map (fun h => predicate_app_step (a := a) h)
      cases h : g.getD f with
      | lam name body =>
        simp only [h] at run
        have tail := ih run
        rw [h] at mapped
        cases tail with
        | some tail _ => exact .some (mapped.trans (.next rfl tail)) (by omega)
      | _ =>
        simp only [h] at run
        cases batch with
        | none =>
          cases changed <;> simp only [pure, Except.pure, Bool.false_eq_true,
            ↓reduceIte, Except.ok.injEq] at run <;> subst result
          all_goals first | exact .none | exact .some .refl (by simp)
        | some more pos =>
          simp only [pure, Except.pure, Except.ok.injEq] at run
          subst result
          exact .some (more.map (fun h => predicate_app_step h)) (fun _ => pos rfl)
    | _ =>
      cases changed <;> simp only [exposePredicate, Bool.false_eq_true, ↓reduceIte,
        pure, Except.pure, Except.ok.injEq] at run <;> subst result
      all_goals first | exact .none | exact .some .refl (by simp)

public theorem exposeTerm_terminates {n E t w} (run : whnfTerm n E t = .ok w)
    (changed : Bool) : ∃ result, Eventually (fun m => exposeTerm m changed t = .ok result) := by
  induction n generalizing t w changed with
  | zero => simp [whnfTerm, exhausted, fail] at run
  | succ n ih =>
    cases t with
    | letE name value body =>
      obtain ⟨result, h⟩ := ih run true
      exact ⟨result, eventually_next (fun _ h => h) h⟩
    | app f a =>
      by_cases zero : ∃ b s, f = .primrec b s ∧ a = .zero
      · obtain ⟨b, s, rfl, rfl⟩ := zero
        cases n with
        | zero => simp [whnfTerm, exhausted, fail] at run
        | succ n =>
          change whnfTerm (n + 1) E b = .ok w at run
          obtain ⟨result, h⟩ := ih run true
          exact ⟨result, eventually_next (fun _ h => h) h⟩
      simp only [whnfTerm, CheckResult.bind_eq_ok] at run
      obtain ⟨g, hg, run⟩ := run
      obtain ⟨out, j, hout⟩ := ih hg false
      cases h : out.getD f with
      | lam name body =>
        obtain ⟨i, steps⟩ := (exposeTerm_batch (E := E) (hout j (by omega))).steps
        have eq := ((whnfTerm_trace hg).drop steps).stationary (by rw [h]; rfl)
        rw [← eq, h] at run
        obtain ⟨result, resultRun⟩ := ih run true
        refine ⟨result, eventually_next ?_ (eventually_and ⟨j, hout⟩ resultRun)⟩
        intro m hm
        simpa only [exposeTerm_app_eq zero, hm.1, bind, Except.bind, h] using hm.2
      | _ =>
        refine ⟨(match out with
          | some g => some (.app g a)
          | none => if changed then some (.app f a) else none), ?_⟩
        refine eventually_next ?_ (⟨j, hout⟩)
        intro m hm
        simp only [exposeTerm_app_eq zero, hm, bind, Except.bind, h]
        cases out <;> rfl
    | _ => exact ⟨if changed then some _ else none, 1,
        fun m hm => by cases m <;> first | omega | rfl⟩

public theorem exposePredicate_terminates {n E t w} (run : whnfPredicate n E t = .ok w)
    (changed : Bool) :
    ∃ result, Eventually (fun m => exposePredicate m changed t = .ok result) := by
  induction n generalizing t w changed with
  | zero => simp [whnfPredicate, exhausted, fail] at run
  | succ n ih =>
    cases t with
    | letTerm | letPredicate =>
      obtain ⟨result, h⟩ := ih run true
      exact ⟨result, eventually_next (fun _ h => h) h⟩
    | app f a =>
      simp only [whnfPredicate, CheckResult.bind_eq_ok] at run
      obtain ⟨g, hg, run⟩ := run
      obtain ⟨out, j, hout⟩ := ih hg false
      cases h : out.getD f with
      | lam name body =>
        obtain ⟨i, steps⟩ := (exposePredicate_batch (E := E) (hout j (by omega))).steps
        have eq := ((whnfPredicate_trace hg).drop steps).stationary (by rw [h]; rfl)
        rw [← eq, h] at run
        obtain ⟨result, resultRun⟩ := ih run true
        refine ⟨result, eventually_next ?_ (eventually_and ⟨j, hout⟩ resultRun)⟩
        intro m hm
        simpa only [exposePredicate, hm.1, bind, Except.bind, h] using hm.2
      | _ =>
        refine ⟨(match out with
          | some g => some (.app g a)
          | none => if changed then some (.app f a) else none), ?_⟩
        refine eventually_next ?_ (⟨j, hout⟩)
        intro m hm
        simp only [exposePredicate, hm, bind, Except.bind, h]
        cases out <;> rfl
    | _ => exact ⟨if changed then some _ else none, 1,
        fun m hm => by cases m <;> first | omega | rfl⟩

private def HeadBefore (step : α → CheckResult (Option α)) (b a : α) : Prop :=
  ∃ n, HeadSteps step (n + 1) a b

private theorem HeadTrace.accessible {step : α → CheckResult (Option α)} {a b}
    (trace : HeadTrace step a b) : Acc (HeadBefore step) a := by
  induction trace with
  | done stop =>
    constructor
    intro b h
    obtain ⟨n, steps⟩ := h
    cases steps with
    | next run _ => simp [stop] at run
  | next run tail ih =>
    constructor
    intro b h
    obtain ⟨n, steps⟩ := h
    cases steps with
    | next run' rest =>
      have eq := run.symm.trans run'
      cases eq
      cases n with
      | zero => cases rest; exact ih
      | succ n => exact ih.inv ⟨n, rest⟩

/-- Prove a property of two inputs by advancing either of their finite head-reduction traces. -/
public theorem HeadTrace.induction_pair {step : α → CheckResult (Option α)} {A B}
    {P : α → α → Prop}
    (advance : ∀ {a b}, HeadTrace step a A → HeadTrace step b B →
      (∀ {i j x y}, HeadSteps step i a x → HeadSteps step j b y → 0 < i + j → P x y) → P a b)
    {a b} (left : HeadTrace step a A) (right : HeadTrace step b B) : P a b := by
  have aux : ∀ a, Acc (HeadBefore step) a → ∀ b, Acc (HeadBefore step) b →
      HeadTrace step a A → HeadTrace step b B → P a b := by
    intro a ha
    induction ha with
    | intro a accessible iha =>
      intro b hb
      induction hb with
      | intro b accessible' ihb =>
        intro left right
        apply advance left right
        intro i j x y hx hy pos
        cases i with
        | zero =>
          cases hx
          cases j with
          | zero => omega
          | succ j => exact ihb y ⟨j, hy⟩ left (right.drop hy)
        | succ i =>
          exact iha x ⟨i, hx⟩ y (right.drop hy).accessible (left.drop hx) (right.drop hy)
  exact aux a left.accessible b right.accessible left right

public theorem unfoldTermHead_terminates {E Ξ Γ t k} (typed : TermTyping E Ξ Γ t k) :
    ∃ out, unfoldTermHead E t = .ok out := by
  induction t using Term.rec (motive_2 := fun _ => True) generalizing k with
  | definition name fs ih =>
    obtain ⟨d, lookup, _⟩ := typed.inv_definition
    exact ⟨some (d.body.instantiate fs), by
      simp [unfoldTermHead, Environment.lookup, lookup, pure, Except.pure]⟩
  | app f a ihf iha =>
    obtain ⟨out, h⟩ := ihf typed.inv_app.1
    exact ⟨out.map (fun f => .app f a), by simp [unfoldTermHead, h, Except.map]⟩
  | nil | cons => trivial
  | _ => exact ⟨none, rfl⟩

public theorem unfoldPredicateHead_terminates {E Ξ Γ t σ}
    (typed : PredicateTyping E Ξ Γ t σ) : ∃ out, unfoldPredicateHead E t = .ok out := by
  induction t using Predicate.rec (motive_2 := fun _ => True) generalizing σ with
  | definition name fs ps ih =>
    obtain ⟨d, lookup, _⟩ := typed.inv_definition
    exact ⟨some (d.body.instantiate fs ps), by
      simp [unfoldPredicateHead, Environment.lookup, lookup, pure, Except.pure]⟩
  | app f a ih =>
    obtain ⟨out, h⟩ := ih typed.app_function.1
    exact ⟨out.map (fun f => .app f a), by simp [unfoldPredicateHead, h, Except.map]⟩
  | nil | cons => trivial
  | _ => exact ⟨none, rfl⟩

public theorem unfoldTermHead_step {E t out} (run : unfoldTermHead E t = .ok (some out)) :
    termStep E t = .ok (some out) := by
  induction t using Term.rec (motive_2 := fun _ => True) generalizing out with
  | definition => exact run
  | app f a ihf iha =>
    cases h : unfoldTermHead E f with
    | error e => simp [unfoldTermHead, h, Except.map] at run
    | ok result =>
      cases result with
      | none => simp [unfoldTermHead, h, Except.map] at run
      | some g =>
        simp only [unfoldTermHead, h, Except.map, Option.map_some, Except.ok.injEq,
          Option.some.injEq] at run
        subst out
        exact term_app_step (ihf h)
  | nil | cons => trivial
  | _ => simp [unfoldTermHead, pure, Except.pure] at run

public theorem unfoldPredicateHead_step {E t out}
    (run : unfoldPredicateHead E t = .ok (some out)) : predicateStep E t = .ok (some out) := by
  induction t using Predicate.rec (motive_2 := fun _ => True) generalizing out with
  | definition => exact run
  | app f a ih =>
    cases h : unfoldPredicateHead E f with
    | error e => simp [unfoldPredicateHead, h, Except.map] at run
    | ok result =>
      cases result with
      | none => simp [unfoldPredicateHead, h, Except.map] at run
      | some g =>
        simp only [unfoldPredicateHead, h, Except.map, Option.map_some, Except.ok.injEq,
          Option.some.injEq] at run
        subst out
        exact predicate_app_step (ih h)
  | nil | cons => trivial
  | _ => simp [unfoldPredicateHead, pure, Except.pure] at run

public theorem exposeRecursor_terminates {n E b s a w}
    (run : whnfTerm n E (.app (.primrec b s) a) = .ok w) :
    ∃ result, Eventually (fun m => exposeRecursor m E (.app (.primrec b s) a) = .ok result) := by
  cases n with
  | zero => simp [whnfTerm, exhausted, fail] at run
  | succ n =>
    cases n with
    | zero => simp [whnfTerm, exhausted, fail] at run
    | succ n =>
      change (do
        let v ← whnfTerm (n + 1) E a
        match v with
        | .zero => whnfTerm (n + 1) E b
        | .app .succ p => whnfTerm (n + 1) E (.app (.app s p) (.app (.primrec b s) p))
        | _ => pure (.app (.primrec b s) v)) = .ok w at run
      simp only [CheckResult.bind_eq_ok] at run
      obtain ⟨v, hv, run⟩ := run
      have ev : Eventually (fun m => whnfTerm m E a = .ok v) :=
        ⟨n + 1, fun m hm => whnfTerm_mono hm hv⟩
      let output := if v == a then none else some (Term.app (.primrec b s) v)
      cases v with
      | zero =>
        obtain ⟨result, h⟩ := exposeTerm_terminates run true
        exact ⟨result, eventually_mono (fun m h => by
          simpa only [exposeRecursor, h.1, bind, Except.bind] using h.2) (eventually_and ev h)⟩
      | app f p =>
        cases f with
        | succ =>
          obtain ⟨result, h⟩ := exposeTerm_terminates run true
          exact ⟨result, eventually_mono (fun m h => by
            simpa only [exposeRecursor, h.1, bind, Except.bind] using h.2) (eventually_and ev h)⟩
        | _ =>
          refine ⟨output, eventually_mono (fun m h => ?_) ev⟩
          simp only [exposeRecursor, h, bind, Except.bind]
          rfl
      | _ =>
        refine ⟨output, eventually_mono (fun m h => ?_) ev⟩
        simp only [exposeRecursor, h, bind, Except.bind]
        rfl

public theorem exposeRecursor_batch {n E b s a result}
    (run : exposeRecursor n E (.app (.primrec b s) a) = .ok result) :
    HeadBatch (termStep E) false (.app (.primrec b s) a) result := by
  simp only [exposeRecursor, CheckResult.bind_eq_ok] at run
  obtain ⟨v, hv, run⟩ := run
  obtain ⟨j, steps⟩ := (whnfTerm_trace hv).steps
  have mapped := steps.map (fun h => term_rec_step (b := b) (s := s) h)
  cases v with
  | zero =>
    cases exposeTerm_batch (E := E) run with
    | some tail _ => exact .some (mapped.trans (.next rfl tail)) (by omega)
  | app f p =>
    cases f with
    | succ =>
      cases exposeTerm_batch (E := E) run with
      | some tail _ => exact .some (mapped.trans (.next rfl tail)) (by omega)
    | _ =>
      simp only [pure, Except.pure, Except.ok.injEq] at run
      split at run
      next => subst result; exact .none
      next h =>
        subst result
        exact .some mapped (by
          intro _
          cases j with
          | zero => cases steps; simp at h
          | succ => omega)
  | _ =>
    simp only [pure, Except.pure, Except.ok.injEq] at run
    split at run
    next => subst result; exact .none
    next h =>
      subst result
      exact .some mapped (by
        intro _
        cases j with
        | zero => cases steps; simp at h
        | succ => omega)

public theorem exposeRecursor_none {n E b s a}
    (run : exposeRecursor n E (.app (.primrec b s) a) = .ok none) :
    termStep E (.app (.primrec b s) a) = .ok none := by
  simp only [exposeRecursor, CheckResult.bind_eq_ok] at run
  obtain ⟨v, hv, run⟩ := run
  cases v with
  | zero => cases exposeTerm_batch (E := E) run
  | app f p =>
    cases f with
    | succ => cases exposeTerm_batch (E := E) run
    | _ =>
      simp only [pure, Except.pure, Except.ok.injEq, ite_eq_left_iff,
        Option.some_ne_none, imp_false] at run
      have eq := eq_of_beq (Classical.byContradiction run)
      subst a
      exact term_stationary (.primrec (whnfTerm_normal hv)
        (by constructor <;> intros <;> simp))
  | _ =>
    simp only [pure, Except.pure, Except.ok.injEq, ite_eq_left_iff,
      Option.some_ne_none, imp_false] at run
    have eq := eq_of_beq (Classical.byContradiction run)
    subst a
    exact term_stationary (.primrec (whnfTerm_normal hv)
      (by constructor <;> intros <;> simp))

private theorem exposeTerm_app_none {n f a}
    (run : exposeTerm n false (.app f a) = .ok none) :
    ∃ m, exposeTerm m false f = .ok none ∧ ∀ name body, f ≠ .lam name body := by
  cases n with
  | zero => simp [exposeTerm, exhausted, fail] at run
  | succ n =>
    by_cases zero : ∃ b s, f = .primrec b s ∧ a = .zero
    · obtain ⟨b, s, rfl, rfl⟩ := zero
      cases exposeTerm_batch (E := ∅) (n := n) (changed := true) run
    rw [exposeTerm_app_eq zero] at run
    simp only [CheckResult.bind_eq_ok] at run
    obtain ⟨out, hout, run⟩ := run
    cases out with
    | none =>
      refine ⟨n, hout, ?_⟩
      intro name body eq
      subst f
      cases exposeTerm_batch (E := ∅) (changed := true) run
    | some g =>
      cases g <;> simp only [Option.getD_some] at run
      all_goals first
        | cases exposeTerm_batch (E := ∅) (changed := true) run
        | simp [pure, Except.pure] at run

private theorem exposePredicate_app_none {n f a}
    (run : exposePredicate n false (.app f a) = .ok none) :
    ∃ m, exposePredicate m false f = .ok none ∧ ∀ name body, f ≠ .lam name body := by
  cases n with
  | zero => simp [exposePredicate, exhausted, fail] at run
  | succ n =>
    simp only [exposePredicate, CheckResult.bind_eq_ok] at run
    obtain ⟨out, hout, run⟩ := run
    cases out with
    | none =>
      refine ⟨n, hout, ?_⟩
      intro name body eq
      subst f
      cases exposePredicate_batch (E := ∅) (changed := true) run
    | some g =>
      cases g <;> simp only [Option.getD_some] at run
      all_goals first
        | cases exposePredicate_batch (E := ∅) (changed := true) run
        | simp [pure, Except.pure] at run

private theorem unfoldTermHead_app_none {E f a}
    (run : unfoldTermHead E (.app f a) = .ok none) : unfoldTermHead E f = .ok none := by
  cases h : unfoldTermHead E f with
  | error e => simp [unfoldTermHead, h, Except.map] at run
  | ok out => cases out <;> simp_all [unfoldTermHead, Except.map]

private theorem unfoldPredicateHead_app_none {E f a}
    (run : unfoldPredicateHead E (.app f a) = .ok none) :
    unfoldPredicateHead E f = .ok none := by
  cases h : unfoldPredicateHead E f with
  | error e => simp [unfoldPredicateHead, h, Except.map] at run
  | ok out => cases out <;> simp_all [unfoldPredicateHead, Except.map]

public theorem term_ready {n E Ξ Γ t k} (typed : TermTyping E Ξ Γ t k)
    (exposed : exposeTerm n false t = .ok none) (unfolded : unfoldTermHead E t = .ok none)
    (notRec : ∀ b s a, t ≠ .app (.primrec b s) a) : termStep E t = .ok none := by
  induction t using Term.rec (motive_2 := fun _ => True) generalizing n k with
  | definition name fs ih =>
    obtain ⟨d, lookup, _⟩ := typed.inv_definition
    simp [unfoldTermHead, Environment.lookup, lookup, pure, Except.pure] at unfolded
  | letE name value body ihv ihb =>
    cases n with
    | zero => simp [exposeTerm, exhausted, fail] at exposed
    | succ n => cases exposeTerm_batch (E := E) (n := n) (changed := true) exposed
  | app f a ihf iha =>
    obtain ⟨m, hf, notLam⟩ := exposeTerm_app_none exposed
    have stop := ihf typed.inv_app.1 hf (unfoldTermHead_app_none unfolded) (by
      intro b s a eq
      have ht := typed.inv_app.1
      rw [eq] at ht
      have bad : k + 1 + 1 = 0 + 1 := ht.inv_app.1.inv_primrec.1
      exact Nat.noConfusion (Nat.add_right_cancel bad))
    cases f with
    | lam => exact False.elim (notLam _ _ rfl)
    | primrec b s => exact False.elim (notRec b s a rfl)
    | _ => change (termStep E _).map _ = _; rw [stop]; rfl
  | nil | cons => trivial
  | _ => rfl

public theorem predicate_ready {n E t}
    (exposed : exposePredicate n false t = .ok none)
    (unfolded : unfoldPredicateHead E t = .ok none) : predicateStep E t = .ok none := by
  induction t using Predicate.rec (motive_2 := fun _ => True) generalizing n with
  | definition name fs ps ih => exact unfolded
  | letTerm | letPredicate =>
    cases n with
    | zero => simp [exposePredicate, exhausted, fail] at exposed
    | succ n => cases exposePredicate_batch (E := E) (n := n) (changed := true) exposed
  | app f a ih =>
    obtain ⟨m, hf, notLam⟩ := exposePredicate_app_none exposed
    have stop := ih hf (unfoldPredicateHead_app_none unfolded)
    cases f with
    | lam => exact False.elim (notLam _ _ rfl)
    | _ => change (predicateStep E _).map _ = _; rw [stop]; rfl
  | nil | cons => trivial
  | _ => rfl

end PRAProver.Core
