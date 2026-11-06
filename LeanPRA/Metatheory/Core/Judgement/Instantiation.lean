module

public import LeanPRA.Metatheory.Core.Judgement.Inversion
public import LeanPRA.Metatheory.Core.Judgement.Scope
import Lean.Elab.Tactic.Omega

/-!
# Declaration-parameter instantiation

- `Proof.instantiate` transforms every annotation and explicit actual in proof data.
- `TermTyping.instantiate` and `PredicateTyping.instantiate` preserve expression formation.
- `TermEq.instantiate` and `PredicateEq.instantiate` preserve typed definitional equality.
- `ProofTyping.instantiate` transforms a derivation, its assumptions, and its conclusion together.
- `EnvironmentWF.predicate_instance` supplies body typing from an admitted declaration.
- The actual-list and context instantiation theorems preserve their declared full interfaces.

Declaration parameters and local variables have separate index spaces. Instantiation replaces
function and predicate parameters simultaneously. A preserved local prefix shifts caller actuals
under that prefix; local substitution is a different operation.
-/

namespace LeanPRA.Core

/-- Instantiate declaration parameters throughout explicit proof data in a single pass.
`depth` counts the source locals preserved above the caller's context. -/
@[expose] public def Proof.instantiate (fs : List Term) (ps : List Predicate)
    (depth : Nat := 0) : Proof → Proof
  | .hyp i => .hyp i
  | .trueIntro => .trueIntro
  | .theoremE name ts qs =>
      .theoremE name (ts.map (Term.instantiate fs depth))
        (qs.map (Predicate.instantiate fs ps depth))
  | .impIntro binderName A p =>
      .impIntro binderName (A.instantiate fs ps depth) (p.instantiate fs ps depth)
  | .impElim p q => .impElim (p.instantiate fs ps depth) (q.instantiate fs ps depth)
  | .andIntro p q => .andIntro (p.instantiate fs ps depth) (q.instantiate fs ps depth)
  | .andLeft p => .andLeft (p.instantiate fs ps depth)
  | .andRight p => .andRight (p.instantiate fs ps depth)
  | .orLeft A p => .orLeft (A.instantiate fs ps depth) (p.instantiate fs ps depth)
  | .orRight A p => .orRight (A.instantiate fs ps depth) (p.instantiate fs ps depth)
  | .orElim leftName rightName A p q r =>
      .orElim leftName rightName (A.instantiate fs ps depth) (p.instantiate fs ps depth)
        (q.instantiate fs ps depth) (r.instantiate fs ps depth)
  | .falseElim A p => .falseElim (A.instantiate fs ps depth) (p.instantiate fs ps depth)
  | .forallIntro binderName P p =>
      .forallIntro binderName (P.instantiate fs ps depth) (p.instantiate fs ps (depth + 1))
  | .forallElim p a => .forallElim (p.instantiate fs ps depth) (a.instantiate fs depth)
  | .existsIntro P a p =>
      .existsIntro (P.instantiate fs ps depth) (a.instantiate fs depth) (p.instantiate fs ps depth)
  | .existsElim variableName hypothesisName A p q =>
      .existsElim variableName hypothesisName (A.instantiate fs ps depth)
        (p.instantiate fs ps depth) (q.instantiate fs ps (depth + 1))
  | .letE binderName A p q =>
      .letE binderName (A.instantiate fs ps depth) (p.instantiate fs ps depth)
        (q.instantiate fs ps depth)
  | .letTerm binderName a p =>
      .letTerm binderName (a.instantiate fs depth) (p.instantiate fs ps depth)
  | .letPredicate binderName P p =>
      .letPredicate binderName (P.instantiate fs ps depth) (p.instantiate fs ps depth)
  | .ascribe A p => .ascribe (A.instantiate fs ps depth) (p.instantiate fs ps depth)
  | .eqRefl t => .eqRefl (t.instantiate fs depth)
  | .eqSubst P e p => .eqSubst (P.instantiate fs ps depth)
      (e.instantiate fs ps depth) (p.instantiate fs ps depth)
  | .succNeZero t => .succNeZero (t.instantiate fs depth)
  | .succInj p => .succInj (p.instantiate fs ps depth)
  | .lem A => .lem (A.instantiate fs ps depth)
  | .induction variableName hypothesisName P b s a =>
      .induction variableName hypothesisName (P.instantiate fs ps depth)
        (b.instantiate fs ps depth) (s.instantiate fs ps (depth + 1)) (a.instantiate fs depth)

end LeanPRA.Core

namespace LeanPRA.Core.Theory

private theorem lift_comp (r s : Renaming) (n : Nat) :
    (fun i => Renaming.lift n s (Renaming.lift n r i)) =
      Renaming.lift n (fun i => s (r i)) := by
  funext i
  simp only [Renaming.lift]
  split <;> rename_i h
  · simp
  · simp [show ¬n + r (i - n) < n by omega]

private theorem predicate_rename_comp (P : Predicate) (r s : Renaming) :
    (P.rename r).rename s = P.rename (fun i => s (r i)) := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ r s : Renaming,
      (ps.map (Predicate.rename r)).map (Predicate.rename s) =
        ps.map (Predicate.rename (fun i => s (r i)))) generalizing r s <;>
    simp_all [Predicate.rename, Term.rename_comp, lift_comp, List.map_map]

private theorem shift_rename (t : Term) (d e : Nat) (r : Renaming)
    (hr : ∀ i, r (i + d) = i + e) : (t.shift d).rename r = t.shift e := by
  simp only [Term.shift, Nat.not_lt_zero, ↓reduceIte, Term.rename_comp]
  exact congrArg (fun f => t.rename f) (funext hr)

private theorem predicate_shift_rename (P : Predicate) (d e : Nat) (r : Renaming)
    (hr : ∀ i, r (i + d) = i + e) : (P.shift d).rename r = P.shift e := by
  simp only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte, predicate_rename_comp]
  exact congrArg (fun f => P.rename f) (funext hr)

private theorem lift_compatible {d e : Nat} {r : Renaming} (hr : ∀ i, r (i + d) = i + e) :
    ∀ i, Renaming.lift 1 r (i + (d + 1)) = i + (e + 1) := by
  intro i
  have hi : i + (d + 1) - 1 = i + d := by omega
  simp only [Renaming.lift, show ¬i + (d + 1) < 1 by omega, ↓reduceIte, hi, hr]
  omega

private theorem instantiate_rename (t : Term) (fs : List Term) (d e : Nat) (r : Renaming)
    (hr : ∀ i, r (i + d) = i + e) :
    (t.rename r).instantiate fs e = (t.instantiate fs d).rename r := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ d e r, (∀ i, r (i + d) = i + e) →
      (ts.map (Term.rename r)).map (Term.instantiate fs e) =
        (ts.map (Term.instantiate fs d)).map (Term.rename r)) generalizing d e r with
  | parameter i => simp only [Term.rename, Term.instantiate]; exact (shift_rename _ _ _ _ hr).symm
  | lam _ t ih =>
      simp only [Term.rename, Term.instantiate]
      exact congrArg (fun t => Term.lam _ t) (ih _ _ _ (lift_compatible hr))
  | letE _ a t iha iht =>
      simp only [Term.rename, Term.instantiate]
      rw [iha _ _ _ hr, iht _ _ _ (lift_compatible hr)]
  | bvar | zero | succ => simp [Term.rename, Term.instantiate]
  | app f a ihf iha => simp only [Term.rename, Term.instantiate]; rw [ihf _ _ _ hr, iha _ _ _ hr]
  | primrec b s n ihb ihs ihn =>
      simp only [Term.rename, Term.instantiate]
      rw [ihb _ _ _ hr, ihs _ _ _ hr, ihn _ _ _ hr]
  | definition name ts ih => simp only [Term.rename, Term.instantiate]; rw [ih _ _ _ hr]
  | nil => rfl
  | cons t ts iht ihts =>
      rename_i d e r hr
      simp only [List.map_cons]
      rw [iht _ _ _ hr, ihts _ _ _ hr]

private theorem predicate_instantiate_rename (P : Predicate) (fs : List Term)
    (ps : List Predicate) (d e : Nat) (r : Renaming) (hr : ∀ i, r (i + d) = i + e) :
    (P.rename r).instantiate fs ps e = (P.instantiate fs ps d).rename r := by
  induction P using Predicate.rec
    (motive_2 := fun qs => ∀ d e r, (∀ i, r (i + d) = i + e) →
      (qs.map (Predicate.rename r)).map (Predicate.instantiate fs ps e) =
        (qs.map (Predicate.instantiate fs ps d)).map (Predicate.rename r))
    generalizing d e r with
  | false | true => simp [Predicate.rename, Predicate.instantiate]
  | parameter i =>
      simp only [Predicate.rename, Predicate.instantiate]
      exact (predicate_shift_rename _ _ _ _ hr).symm
  | equal a b => simp [Predicate.rename, Predicate.instantiate, instantiate_rename a fs d e r hr,
      instantiate_rename b fs d e r hr]
  | imp A B ihA ihB | and A B ihA ihB | or A B ihA ihB =>
      simp only [Predicate.rename, Predicate.instantiate]; rw [ihA _ _ _ hr, ihB _ _ _ hr]
  | all P ih | ex P ih => simp only [Predicate.rename, Predicate.instantiate]; rw [ih _ _ _ hr]
  | lam _ P ih =>
      simp only [Predicate.rename, Predicate.instantiate]
      exact congrArg (fun t => Predicate.lam _ t) (ih _ _ _ (lift_compatible hr))
  | app P a ih => simp [Predicate.rename, Predicate.instantiate, ih _ _ _ hr,
      instantiate_rename a fs d e r hr]
  | letTerm _ a P ih =>
      simp [Predicate.rename, Predicate.instantiate, instantiate_rename a fs d e r hr, ih _ _ _ hr]
  | letPredicate _ Q P ihQ ihP =>
      simp only [Predicate.rename, Predicate.instantiate]; rw [ihQ _ _ _ hr, ihP _ _ _ hr]
  | definition name ts qs ih =>
      simp only [Predicate.rename, Predicate.instantiate, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro t ht
        exact instantiate_rename t fs d e r hr
      · simpa only [List.map_map] using ih d e r hr
  | nil => rfl
  | cons P qs ihP ihqs =>
      rename_i d e r hr
      simp only [List.map_cons]
      rw [ihP _ _ _ hr, ihqs _ _ _ hr]

private theorem instantiate_shift (t : Term) (fs : List Term) (d n : Nat) :
    (t.shift n).instantiate fs (d + n) = (t.instantiate fs d).shift n := by
  simpa only [Term.shift, Nat.not_lt_zero, ↓reduceIte] using
    instantiate_rename t fs d (d + n) (fun i => i + n) (by intro i; omega)

private theorem predicate_instantiate_shift (P : Predicate) (fs : List Term)
    (ps : List Predicate) (d n : Nat) :
    (P.shift n).instantiate fs ps (d + n) = (P.instantiate fs ps d).shift n := by
  simpa only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte] using
    predicate_instantiate_rename P fs ps d (d + n) (fun i => i + n) (by intro i; omega)

private theorem instantiate_comp (t : Term) (fs gs : List Term) (n d : Nat)
    (scope : TermScope fs.length n t) :
    (t.instantiate fs n).instantiate gs (d + n) =
      t.instantiate (fs.map (Term.instantiate gs d)) n := by
  cases t with
  | bvar i => simp [Term.instantiate]
  | parameter i =>
      simp only [TermScope] at scope
      have hi := List.getElem?_eq_getElem scope
      simp only [Term.instantiate, hi, Option.getD_some, List.getElem?_map, Option.map_some]
      exact instantiate_shift _ _ _ _
  | zero => simp [Term.instantiate]
  | succ => simp [Term.instantiate]
  | lam _ t =>
      simp only [TermScope] at scope
      simp only [Term.instantiate]
      rw [show d + n + 1 = d + (n + 1) by omega, instantiate_comp t fs gs (n + 1) d scope]
  | app f a =>
      simp only [TermScope] at scope
      simp only [Term.instantiate]
      rw [instantiate_comp f fs gs n d scope.1, instantiate_comp a fs gs n d scope.2]
  | letE _ a t =>
      simp only [TermScope] at scope
      simp only [Term.instantiate]
      rw [instantiate_comp a fs gs n d scope.1, show d + n + 1 = d + (n + 1) by omega,
        instantiate_comp t fs gs (n + 1) d scope.2]
  | primrec b s a =>
      simp only [TermScope] at scope
      simp only [Term.instantiate]
      rw [instantiate_comp b fs gs n d scope.1, instantiate_comp s fs gs n d scope.2.1,
        instantiate_comp a fs gs n d scope.2.2]
  | definition name ts =>
      simp only [TermScope] at scope
      simp only [Term.instantiate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      exact instantiate_comp t fs gs n d (scope t ht)
termination_by sizeOf t

private theorem predicate_instantiate_comp (P : Predicate) (fs gs : List Term)
    (ps qs : List Predicate) (n d : Nat) (scope : PredicateScope fs.length ps.length n P) :
    (P.instantiate fs ps n).instantiate gs qs (d + n) =
      P.instantiate (fs.map (Term.instantiate gs d))
        (ps.map (Predicate.instantiate gs qs d)) n := by
  cases P with
  | false => simp [Predicate.instantiate]
  | true => simp [Predicate.instantiate]
  | parameter i =>
      simp only [PredicateScope] at scope
      have hi := List.getElem?_eq_getElem scope
      simp only [Predicate.instantiate, hi, Option.getD_some, List.getElem?_map, Option.map_some]
      exact predicate_instantiate_shift _ _ _ _ _
  | equal a b =>
      simp only [PredicateScope] at scope
      simp [Predicate.instantiate, instantiate_comp a fs gs n d scope.1,
        instantiate_comp b fs gs n d scope.2]
  | imp A B | and A B | or A B =>
      simp only [PredicateScope] at scope
      simp only [Predicate.instantiate]
      rw [predicate_instantiate_comp A fs gs ps qs n d scope.1,
        predicate_instantiate_comp B fs gs ps qs n d scope.2]
  | all P | ex P =>
      simp only [PredicateScope] at scope
      simp only [Predicate.instantiate]
      rw [predicate_instantiate_comp P fs gs ps qs n d scope]
  | lam _ P =>
      simp only [PredicateScope] at scope
      simp only [Predicate.instantiate]
      rw [show d + n + 1 = d + (n + 1) by omega,
        predicate_instantiate_comp P fs gs ps qs (n + 1) d scope]
  | app P a =>
      simp only [PredicateScope] at scope
      simp only [Predicate.instantiate]
      rw [predicate_instantiate_comp P fs gs ps qs n d scope.1,
        instantiate_comp a fs gs n d scope.2]
  | letTerm _ a P =>
      simp only [PredicateScope] at scope
      simp only [Predicate.instantiate]
      rw [instantiate_comp a fs gs n d scope.1,
        predicate_instantiate_comp P fs gs ps qs n d scope.2]
  | letPredicate _ Q P =>
      simp only [PredicateScope] at scope
      simp only [Predicate.instantiate]
      rw [predicate_instantiate_comp Q fs gs ps qs n d scope.1,
        predicate_instantiate_comp P fs gs ps qs n d scope.2]
  | definition name ts rs =>
      simp only [PredicateScope] at scope
      simp only [Predicate.instantiate, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro t ht
        exact instantiate_comp t fs gs n d (scope.1 t ht)
      · apply List.map_congr_left
        intro R hR
        exact predicate_instantiate_comp R fs gs ps qs n d (scope.2 R hR)
termination_by sizeOf P

private theorem shift_add (t : Term) (a b : Nat) : (t.shift a).shift b = t.shift (a + b) := by
  simp only [Term.shift, Nat.not_lt_zero, ↓reduceIte, Term.rename_comp]
  congr 1
  funext i
  omega

private theorem predicate_shift_add (P : Predicate) (a b : Nat) :
    (P.shift a).shift b = P.shift (a + b) := by
  simp only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte, predicate_rename_comp]
  congr 1
  funext i
  omega

private theorem instantiate_subst (t : Term) (fs : List Term) (d e : Nat) (s u : Subst)
    (hs : ∀ i, (s i).instantiate fs d = u i)
    (hu : ∀ a : Term, (a.shift e).subst u = a.shift d) :
    (t.subst s).instantiate fs d = (t.instantiate fs e).subst u := by
  have hslift : ∀ i, (Subst.lift 1 s i).instantiate fs (d + 1) = Subst.lift 1 u i := by
    intro i
    cases i with
    | zero => simp [Subst.lift, Term.instantiate]
    | succ i => simp [Subst.lift, instantiate_shift, hs]
  have hulift : ∀ a : Term, (a.shift (e + 1)).subst (Subst.lift 1 u) = a.shift (d + 1) := by
    intro a
    rw [←shift_add a e 1, Term.subst_shift, hu, shift_add]
  cases t with
  | bvar i => simp only [Term.subst, Term.instantiate]; exact hs i
  | parameter i => simp only [Term.subst, Term.instantiate]; exact (hu _).symm
  | zero => simp [Term.subst, Term.instantiate]
  | succ => simp [Term.subst, Term.instantiate]
  | lam _ t =>
      simp only [Term.subst, Term.instantiate]
      rw [instantiate_subst t fs (d + 1) (e + 1) _ _ hslift hulift]
  | app f a =>
      simp only [Term.subst, Term.instantiate]
      rw [instantiate_subst f fs d e s u hs hu, instantiate_subst a fs d e s u hs hu]
  | letE _ a t =>
      simp only [Term.subst, Term.instantiate]
      rw [instantiate_subst a fs d e s u hs hu,
        instantiate_subst t fs (d + 1) (e + 1) _ _ hslift hulift]
  | primrec b step a =>
      simp only [Term.subst, Term.instantiate]
      rw [instantiate_subst b fs d e s u hs hu, instantiate_subst step fs d e s u hs hu,
        instantiate_subst a fs d e s u hs hu]
  | definition name ts =>
      simp only [Term.subst, Term.instantiate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      exact instantiate_subst t fs d e s u hs hu
termination_by sizeOf t

private theorem predicate_instantiate_subst (P : Predicate) (fs : List Term)
    (ps : List Predicate) (d e : Nat) (s u : Subst)
    (hs : ∀ i, (s i).instantiate fs d = u i)
    (hu : ∀ a : Term, (a.shift e).subst u = a.shift d)
    (hp : ∀ Q : Predicate, (Q.shift e).subst u = Q.shift d) :
    (P.subst s).instantiate fs ps d = (P.instantiate fs ps e).subst u := by
  have hslift : ∀ i, (Subst.lift 1 s i).instantiate fs (d + 1) = Subst.lift 1 u i := by
    intro i
    cases i with
    | zero => simp [Subst.lift, Term.instantiate]
    | succ i => simp [Subst.lift, instantiate_shift, hs]
  have hulift : ∀ a : Term, (a.shift (e + 1)).subst (Subst.lift 1 u) = a.shift (d + 1) := by
    intro a
    rw [←shift_add a e 1, Term.subst_shift, hu, shift_add]
  have hplift : ∀ Q : Predicate, (Q.shift (e + 1)).subst (Subst.lift 1 u) = Q.shift (d + 1) := by
    intro Q
    rw [←predicate_shift_add Q e 1, Predicate.subst_shift, hp, predicate_shift_add]
  cases P with
  | false => simp [Predicate.subst, Predicate.instantiate]
  | true => simp [Predicate.subst, Predicate.instantiate]
  | parameter i => simp only [Predicate.subst, Predicate.instantiate]; exact (hp _).symm
  | equal a b =>
      simp [Predicate.subst, Predicate.instantiate, instantiate_subst a fs d e s u hs hu,
        instantiate_subst b fs d e s u hs hu]
  | imp A B | and A B | or A B =>
      simp only [Predicate.subst, Predicate.instantiate]
      rw [predicate_instantiate_subst A fs ps d e s u hs hu hp,
        predicate_instantiate_subst B fs ps d e s u hs hu hp]
  | all P | ex P =>
      simp only [Predicate.subst, Predicate.instantiate]
      rw [predicate_instantiate_subst P fs ps d e s u hs hu hp]
  | lam _ P =>
      simp only [Predicate.subst, Predicate.instantiate]
      rw [predicate_instantiate_subst P fs ps (d + 1) (e + 1) _ _ hslift hulift hplift]
  | app P a =>
      simp only [Predicate.subst, Predicate.instantiate]
      rw [predicate_instantiate_subst P fs ps d e s u hs hu hp,
        instantiate_subst a fs d e s u hs hu]
  | letTerm _ a P =>
      simp only [Predicate.subst, Predicate.instantiate]
      rw [instantiate_subst a fs d e s u hs hu,
        predicate_instantiate_subst P fs ps d e s u hs hu hp]
  | letPredicate _ Q P =>
      simp only [Predicate.subst, Predicate.instantiate]
      rw [predicate_instantiate_subst Q fs ps d e s u hs hu hp,
        predicate_instantiate_subst P fs ps d e s u hs hu hp]
  | definition name ts qs =>
      simp only [Predicate.subst, Predicate.instantiate, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro t ht
        exact instantiate_subst t fs d e s u hs hu
      · apply List.map_congr_left
        intro Q hQ
        exact predicate_instantiate_subst Q fs ps d e s u hs hu hp
termination_by sizeOf P

private theorem instantiate_subst0 (t a : Term) (fs : List Term) (d : Nat) :
    (t.subst0 a).instantiate fs d = (t.instantiate fs (d + 1)).subst0 (a.instantiate fs d) := by
  apply instantiate_subst
  · intro i
    cases i <;> simp [Term.instantiate]
  · intro b
    rw [←shift_add b d 1]
    exact Term.subst0_shift _ _

private theorem predicate_instantiate_subst0 (P : Predicate) (a : Term) (fs : List Term)
    (ps : List Predicate) (d : Nat) :
    (P.subst0 a).instantiate fs ps d =
      (P.instantiate fs ps (d + 1)).subst0 (a.instantiate fs d) := by
  apply predicate_instantiate_subst
  · intro i
    cases i <;> simp [Term.instantiate]
  · intro b
    rw [←shift_add b d 1]
    exact Term.subst0_shift _ _
  · intro Q
    rw [←predicate_shift_add Q d 1]
    exact Predicate.subst0_shift _ _

private theorem term_shift_prefix {E Ω Γ t k} (h : TermTyping E Ω Γ t k) (L : LocalContext) :
    TermTyping E Ω (L ++ Γ) (t.shift L.length) k := by
  simpa only [Term.shift, Nat.not_lt_zero, ↓reduceIte] using
    TermTyping.rename h (fun i => i + L.length) (by
      intro i j hi
      change (L ++ Γ)[i + L.length]? = some j
      rw [List.getElem?_append_right (by omega)]
      simpa using hi)

private theorem predicate_shift_prefix {E Ω Γ P σ} (valid : EnvironmentWF E)
    (h : PredicateTyping E Ω Γ P σ) (L : LocalContext) :
    PredicateTyping E Ω (L ++ Γ) (P.shift L.length) σ := by
  simpa only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte] using
    PredicateTyping.rename valid h (fun i => i + L.length) (by
      intro i j hi
      change (L ++ Γ)[i + L.length]? = some j
      rw [List.getElem?_append_right (by omega)]
      simpa using hi)

private theorem term_instantiate {E Ξ L t k} (h : TermTyping E Ξ L t k)
    {Ω Γ fs} (actuals : FunctionArguments E Ω Γ fs Ξ.functions) :
    TermTyping E Ω (L ++ Γ) (t.instantiate fs L.length) k := by
  induction h using TermTyping.rec
    (motive_2 := fun L ts ks _ => ∀ {Ω Γ fs}, FunctionArguments E Ω Γ fs Ξ.functions →
      FunctionArguments E Ω (L ++ Γ) (ts.map (Term.instantiate fs L.length)) ks)
    generalizing Ω Γ fs with
  | @bvar L i k lookup =>
      simp only [Term.instantiate]
      exact .bvar
        ((List.getElem?_append_left (List.getElem?_eq_some_iff.mp lookup).choose).trans lookup)
  | @parameter i k L lookup =>
      obtain ⟨a, ha, typing⟩ := FunctionArguments.lookup actuals lookup
      simp only [Term.instantiate, ha, Option.getD_some]
      exact term_shift_prefix typing L
  | zero => simp only [Term.instantiate]; exact .zero
  | succ => simp only [Term.instantiate]; exact .succ
  | lam body ih => simp only [Term.instantiate]; exact .lam (ih actuals)
  | app f a ihf iha => simp only [Term.instantiate]; exact .app (ihf actuals) (iha actuals)
  | letE a t iha iht => simp only [Term.instantiate]; exact .letE (iha actuals) (iht actuals)
  | primrec b s n ihb ihs ihn =>
      simp only [Term.instantiate]; exact .primrec (ihb actuals) (ihs actuals) (ihn actuals)
  | definition lookup args ih => simp only [Term.instantiate]; exact .definition lookup (ih actuals)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i Ω Γ fs actuals
      exact .cons (ihh actuals) (iht actuals)

private theorem functions_instantiate {E Ξ L ts ks} (h : FunctionArguments E Ξ L ts ks)
    {Ω Γ fs} (actuals : FunctionArguments E Ω Γ fs Ξ.functions) :
    FunctionArguments E Ω (L ++ Γ) (ts.map (Term.instantiate fs L.length)) ks := by
  induction h using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True)
    generalizing Ω Γ fs
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (term_instantiate head actuals) (iht actuals)
  all_goals trivial

private theorem predicate_instantiate {E Ξ L P σ} (valid : EnvironmentWF E)
    (h : PredicateTyping E Ξ L P σ) {Ω Γ fs ps}
    (actuals : InstantiationTyping E Ξ Ω Γ fs ps) :
    PredicateTyping E Ω (L ++ Γ) (P.instantiate fs ps L.length) σ := by
  induction h using PredicateTyping.rec
    (motive_2 := fun L qs signatures _ => ∀ {Ω Γ fs ps}, InstantiationTyping E Ξ Ω Γ fs ps →
      PredicateArguments E Ω (L ++ Γ) (qs.map (Predicate.instantiate fs ps L.length)) signatures)
    generalizing Ω Γ fs ps with
  | false => simp only [Predicate.instantiate]; exact .false
  | true => simp only [Predicate.instantiate]; exact .true
  | equal a b =>
      simp only [Predicate.instantiate]
      exact .equal (term_instantiate a actuals.functions) (term_instantiate b actuals.functions)
  | imp A B ihA ihB => simp only [Predicate.instantiate]; exact .imp (ihA actuals) (ihB actuals)
  | and A B ihA ihB => simp only [Predicate.instantiate]; exact .and (ihA actuals) (ihB actuals)
  | or A B ihA ihB => simp only [Predicate.instantiate]; exact .or (ihA actuals) (ihB actuals)
  | all P ih => simp only [Predicate.instantiate]; exact .all (ih actuals)
  | ex P ih => simp only [Predicate.instantiate]; exact .ex (ih actuals)
  | @parameter i σ L lookup =>
      obtain ⟨Q, hQ, typing⟩ := PredicateArguments.lookup actuals.predicates lookup
      simp only [Predicate.instantiate, hQ, Option.getD_some]
      exact predicate_shift_prefix valid typing L
  | lam P ih => simp only [Predicate.instantiate]; exact .lam (ih actuals)
  | app P a ih =>
      simp only [Predicate.instantiate]
      exact .app (ih actuals) (term_instantiate a actuals.functions)
  | letTerm a P ih =>
      simp only [Predicate.instantiate]
      exact .letTerm (term_instantiate a actuals.functions) (ih actuals)
  | letPredicate Q P ihQ ihP =>
      simp only [Predicate.instantiate]; exact .letPredicate (ihQ actuals) (ihP actuals)
  | definition lookup functions predicates ihp =>
      simp only [Predicate.instantiate]
      exact .definition lookup (functions_instantiate functions actuals.functions) (ihp actuals)
  | subsumption h sub ih => exact .subsumption (ih actuals) sub
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i Ω Γ fs ps actuals
      exact .cons (ihh actuals) (iht actuals)

private theorem predicates_instantiate {E Ξ L qs signatures} (valid : EnvironmentWF E)
    (h : PredicateArguments E Ξ L qs signatures) {Ω Γ fs ps}
    (actuals : InstantiationTyping E Ξ Ω Γ fs ps) :
    PredicateArguments E Ω (L ++ Γ) (qs.map (Predicate.instantiate fs ps L.length)) signatures := by
  induction h using PredicateArguments.rec (motive_1 := fun _ _ _ _ => True)
    generalizing Ω Γ fs ps
  case nil => exact .nil
  case cons head tail ihh iht =>
      exact .cons (predicate_instantiate valid head actuals) (iht actuals)
  all_goals trivial

private theorem term_eq_instantiate {E Ξ L t u k} (valid : EnvironmentWF E)
    (h : TermEq E Ξ L t u k) {Ω Γ fs} (actuals : FunctionArguments E Ω Γ fs Ξ.functions) :
    TermEq E Ω (L ++ Γ) (t.instantiate fs L.length) (u.instantiate fs L.length) k := by
  induction h using TermEq.rec
    (motive_2 := fun L ts us ks _ => ∀ {Ω Γ fs}, FunctionArguments E Ω Γ fs Ξ.functions →
      FunctionArgumentEq E Ω (L ++ Γ) (ts.map (Term.instantiate fs L.length))
        (us.map (Term.instantiate fs L.length)) ks) generalizing Ω Γ fs with
  | refl typing => exact .refl (term_instantiate typing actuals)
  | symm h ih => exact .symm (ih actuals)
  | trans h g ihh ihg => exact .trans (ihh actuals) (ihg actuals)
  | beta body argument =>
      simp only [Term.instantiate, instantiate_subst0]
      exact .beta (term_instantiate body actuals) (term_instantiate argument actuals)
  | eta function =>
      simp only [Term.instantiate, instantiate_shift]
      exact .eta (term_instantiate function actuals)
  | zeta value body =>
      simp only [Term.instantiate, instantiate_subst0]
      exact .zeta (term_instantiate value actuals) (term_instantiate body actuals)
  | @delta name L ts d lookup arguments body =>
      have scope := EnvironmentWF.function_scope valid lookup
      rw [←FunctionArguments.length_eq arguments] at scope
      have commute := instantiate_comp d.body ts fs 0 L.length scope
      simp only [Nat.add_zero] at commute
      simp only [Term.instantiate]
      rw [commute]
      have hb := term_instantiate body actuals
      rw [commute] at hb
      exact .delta lookup (functions_instantiate arguments actuals) hb
  | primrecZero base step =>
      simp only [Term.instantiate]
      exact .primrecZero (term_instantiate base actuals) (term_instantiate step actuals)
  | primrecSucc base step argument =>
      simp only [Term.instantiate]
      exact .primrecSucc (term_instantiate base actuals) (term_instantiate step actuals)
        (term_instantiate argument actuals)
  | lam body ih => simp only [Term.instantiate]; exact .lam (ih actuals)
  | app f a ihf iha => simp only [Term.instantiate]; exact .app (ihf actuals) (iha actuals)
  | letE a t iha iht => simp only [Term.instantiate]; exact .letE (iha actuals) (iht actuals)
  | primrec b s n ihb ihs ihn =>
      simp only [Term.instantiate]; exact .primrec (ihb actuals) (ihs actuals) (ihn actuals)
  | definition lookup arguments ih =>
      simp only [Term.instantiate]; exact .definition lookup (ih actuals)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i Ω Γ fs actuals
      exact .cons (ihh actuals) (iht actuals)

private theorem function_eq_instantiate {E Ξ L ts us ks} (valid : EnvironmentWF E)
    (h : FunctionArgumentEq E Ξ L ts us ks) {Ω Γ fs}
    (actuals : FunctionArguments E Ω Γ fs Ξ.functions) :
    FunctionArgumentEq E Ω (L ++ Γ) (ts.map (Term.instantiate fs L.length))
      (us.map (Term.instantiate fs L.length)) ks := by
  induction h using FunctionArgumentEq.rec (motive_1 := fun _ _ _ _ _ => True)
    generalizing Ω Γ fs
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (term_eq_instantiate valid head actuals) (iht actuals)
  all_goals trivial

private theorem predicate_eq_instantiate {E Ξ L P Q σ} (valid : EnvironmentWF E)
    (h : PredicateEq E Ξ L P Q σ) {Ω Γ fs ps} (actuals : InstantiationTyping E Ξ Ω Γ fs ps) :
    PredicateEq E Ω (L ++ Γ) (P.instantiate fs ps L.length) (Q.instantiate fs ps L.length) σ := by
  induction h using PredicateEq.rec
    (motive_2 := fun L qs rs signatures _ => ∀ {Ω Γ fs ps}, InstantiationTyping E Ξ Ω Γ fs ps →
      PredicateArgumentEq E Ω (L ++ Γ) (qs.map (Predicate.instantiate fs ps L.length))
        (rs.map (Predicate.instantiate fs ps L.length)) signatures)
    generalizing Ω Γ fs ps with
  | refl typing => exact .refl (predicate_instantiate valid typing actuals)
  | symm h ih => exact .symm (ih actuals)
  | trans h g ihh ihg => exact .trans (ihh actuals) (ihg actuals)
  | subsumption h sub ih => exact .subsumption (ih actuals) sub
  | beta body argument =>
      simp only [Predicate.instantiate, predicate_instantiate_subst0]
      exact .beta (predicate_instantiate valid body actuals)
        (term_instantiate argument actuals.functions)
  | eta function =>
      simp only [Predicate.instantiate, Term.instantiate, predicate_instantiate_shift]
      exact .eta (predicate_instantiate valid function actuals)
  | zetaTerm a P =>
      simp only [Predicate.instantiate]
      exact .zetaTerm (term_instantiate a actuals.functions) (predicate_instantiate valid P actuals)
  | zetaPredicate Q P =>
      simp only [Predicate.instantiate]
      exact .zetaPredicate (predicate_instantiate valid Q actuals)
        (predicate_instantiate valid P actuals)
  | @delta name L ts qs σ d lookup functions predicates body bound =>
      have scope := EnvironmentWF.predicate_scope valid lookup
      rw [←FunctionArguments.length_eq functions, ←PredicateArguments.length_eq predicates] at scope
      have commute := predicate_instantiate_comp d.body ts fs qs ps 0 L.length scope
      simp only [Nat.add_zero] at commute
      simp only [Predicate.instantiate]
      rw [commute]
      have hb := predicate_instantiate valid body actuals
      rw [commute] at hb
      exact .delta lookup (functions_instantiate functions actuals.functions)
        (predicates_instantiate valid predicates actuals) hb bound
  | equal a b =>
      simp only [Predicate.instantiate]
      exact .equal (term_eq_instantiate valid a actuals.functions)
        (term_eq_instantiate valid b actuals.functions)
  | imp A B ihA ihB => simp only [Predicate.instantiate]; exact .imp (ihA actuals) (ihB actuals)
  | and A B ihA ihB => simp only [Predicate.instantiate]; exact .and (ihA actuals) (ihB actuals)
  | or A B ihA ihB => simp only [Predicate.instantiate]; exact .or (ihA actuals) (ihB actuals)
  | all P ih => simp only [Predicate.instantiate]; exact .all (ih actuals)
  | ex P ih => simp only [Predicate.instantiate]; exact .ex (ih actuals)
  | lam P ih => simp only [Predicate.instantiate]; exact .lam (ih actuals)
  | app P a ih =>
      simp only [Predicate.instantiate]
      exact .app (ih actuals) (term_eq_instantiate valid a actuals.functions)
  | definition lookup functions predicates left right ih =>
      simp only [Predicate.instantiate]
      exact .definition lookup (function_eq_instantiate valid functions actuals.functions)
        (ih actuals)
        (by simpa only [Predicate.instantiate] using predicate_instantiate valid left actuals)
        (by simpa only [Predicate.instantiate] using predicate_instantiate valid right actuals)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i Ω Γ fs ps actuals
      exact .cons (ihh actuals) (iht actuals)

private theorem hypotheses_instantiate_shift (H : ProofContext) (fs : List Term)
    (ps : List Predicate) (d : Nat) :
    (H.map Predicate.shift).map (Predicate.instantiate fs ps (d + 1)) =
      (H.map (Predicate.instantiate fs ps d)).map Predicate.shift := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro P hP
  exact predicate_instantiate_shift P fs ps d 1

private theorem predicate_list_eq_instantiate {E Ξ L qs rs signatures} (valid : EnvironmentWF E)
    (h : PredicateArgumentEq E Ξ L qs rs signatures) {Ω Γ fs ps}
    (actuals : InstantiationTyping E Ξ Ω Γ fs ps) :
    PredicateArgumentEq E Ω (L ++ Γ) (qs.map (Predicate.instantiate fs ps L.length))
      (rs.map (Predicate.instantiate fs ps L.length)) signatures := by
  induction h using PredicateArgumentEq.rec (motive_1 := fun _ _ _ _ _ => True)
    generalizing Ω Γ fs ps
  case nil => exact .nil
  case cons head tail ihh iht =>
      exact .cons (predicate_eq_instantiate valid head actuals) (iht actuals)
  all_goals trivial

private theorem proof_instantiate {E Ξ L H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ L H p A) {Ω Γ fs ps} (actuals : InstantiationTyping E Ξ Ω Γ fs ps) :
    ProofTyping E Ω (L ++ Γ) (H.map (Predicate.instantiate fs ps L.length))
      (p.instantiate fs ps L.length) (A.instantiate fs ps L.length) := by
  induction h generalizing Ω Γ fs ps with
  | hyp lookup =>
      simp only [Proof.instantiate]
      exact .hyp (by simp only [List.getElem?_map, lookup, Option.map_some])
  | trueIntro => simp only [Proof.instantiate, Predicate.instantiate]; exact .trueIntro
  | @theoremE name L ts qs H d lookup functions predicates =>
      have scope := EnvironmentWF.theorem_scope valid lookup
      rw [←FunctionArguments.length_eq functions, ←PredicateArguments.length_eq predicates] at scope
      have commute := predicate_instantiate_comp d.type ts fs qs ps 0 L.length scope
      simp only [Nat.add_zero] at commute
      simp only [Proof.instantiate]
      rw [commute]
      exact .theoremE lookup (functions_instantiate functions actuals.functions)
        (predicates_instantiate valid predicates actuals)
  | impIntro antecedent body ih =>
      simp only [Proof.instantiate, Predicate.instantiate]
      exact .impIntro (predicate_instantiate valid antecedent actuals) (ih actuals)
  | impElim f a ihf iha =>
      simp only [Proof.instantiate]
      apply ProofTyping.impElim
      · simpa only [Predicate.instantiate] using ihf actuals
      · exact iha actuals
  | andIntro a b iha ihb =>
      simp only [Proof.instantiate, Predicate.instantiate]
      exact .andIntro (iha actuals) (ihb actuals)
  | andLeft pair ih =>
      simp only [Proof.instantiate]
      exact .andLeft (by simpa only [Predicate.instantiate] using ih actuals)
  | andRight pair ih =>
      simp only [Proof.instantiate]
      exact .andRight (by simpa only [Predicate.instantiate] using ih actuals)
  | orLeft other proof ih =>
      simp only [Proof.instantiate, Predicate.instantiate]
      exact .orLeft (predicate_instantiate valid other actuals) (ih actuals)
  | orRight other proof ih =>
      simp only [Proof.instantiate, Predicate.instantiate]
      exact .orRight (predicate_instantiate valid other actuals) (ih actuals)
  | orElim target scrutinee left right ihp ihl ihr =>
      simp only [Proof.instantiate]
      exact .orElim (predicate_instantiate valid target actuals)
        (by simpa only [Predicate.instantiate] using ihp actuals) (ihl actuals) (ihr actuals)
  | falseElim target proof ih =>
      simp only [Proof.instantiate]
      exact .falseElim (predicate_instantiate valid target actuals)
        (by simpa only [Predicate.instantiate] using ih actuals)
  | forallIntro motive body ih =>
      simp only [Proof.instantiate, Predicate.instantiate]
      apply ProofTyping.forallIntro (predicate_instantiate valid motive actuals)
      simpa only [List.length_cons, List.cons_append, Predicate.instantiate, Term.instantiate,
        predicate_instantiate_shift, hypotheses_instantiate_shift] using ih actuals
  | forallElim proof argument ih =>
      simp only [Proof.instantiate, Predicate.instantiate]
      exact .forallElim (by simpa only [Predicate.instantiate] using ih actuals)
        (term_instantiate argument actuals.functions)
  | existsIntro motive witness proof ih =>
      simp only [Proof.instantiate, Predicate.instantiate]
      exact .existsIntro (predicate_instantiate valid motive actuals)
        (term_instantiate witness actuals.functions)
        (by simpa only [Predicate.instantiate] using ih actuals)
  | existsElim target scrutinee body ihp ihb =>
      simp only [Proof.instantiate]
      apply ProofTyping.existsElim (predicate_instantiate valid target actuals)
        (by simpa only [Predicate.instantiate] using ihp actuals)
      simpa only [List.length_cons, List.cons_append, List.map_cons,
        Predicate.instantiate, Term.instantiate,
        predicate_instantiate_shift, hypotheses_instantiate_shift] using ihb actuals
  | letE type value body ihv ihb =>
      simp only [Proof.instantiate]
      exact .letE (predicate_instantiate valid type actuals) (ihv actuals) (ihb actuals)
  | letTerm a p ih =>
      simp only [Proof.instantiate]
      exact .letTerm (term_instantiate a actuals.functions) (ih actuals)
  | letPredicate P p ih =>
      simp only [Proof.instantiate]
      exact .letPredicate (predicate_instantiate valid P actuals) (ih actuals)
  | ascribe type proof ih =>
      simp only [Proof.instantiate]
      exact .ascribe (predicate_instantiate valid type actuals) (ih actuals)
  | eqRefl term =>
      simp only [Proof.instantiate, Predicate.instantiate]
      exact .eqRefl (term_instantiate term actuals.functions)
  | eqSubst motive equality proof ihe ihp =>
      simp only [Proof.instantiate, Predicate.instantiate]
      exact .eqSubst (predicate_instantiate valid motive actuals)
        (by simpa only [Predicate.instantiate] using ihe actuals)
        (by simpa only [Predicate.instantiate] using ihp actuals)
  | succNeZero term =>
      simp only [Proof.instantiate, Predicate.instantiate, Term.instantiate]
      exact .succNeZero (term_instantiate term actuals.functions)
  | succInj proof ih =>
      simp only [Proof.instantiate, Predicate.instantiate]
      exact .succInj (by simpa only [Predicate.instantiate, Term.instantiate] using ih actuals)
  | lem formula =>
      simp only [Proof.instantiate, Predicate.instantiate]
      exact .lem (predicate_instantiate valid formula actuals)
  | induction motive base step argument ihb ihs =>
      simp only [Proof.instantiate, Predicate.instantiate]
      apply ProofTyping.induction (predicate_instantiate valid motive actuals)
      · simpa only [Predicate.instantiate, Term.instantiate] using ihb actuals
      · simpa only [List.length_cons, List.cons_append, List.map_cons,
          Predicate.instantiate, Term.instantiate,
          predicate_instantiate_shift, hypotheses_instantiate_shift] using ihs actuals
      · exact term_instantiate argument actuals.functions
  | conversion proof type ih =>
      exact .conversion (ih actuals) (predicate_eq_instantiate valid type actuals)

/-- Instantiating function parameters preserves term typing under any preserved local prefix.
Caller actuals are shifted below that prefix, which is prepended to the caller's locals. -/
public theorem TermTyping.instantiate {E Ξ L t k} (h : TermTyping E Ξ L t k)
    {Ω Γ fs} (actuals : FunctionArguments E Ω Γ fs Ξ.functions) :
    TermTyping E Ω (L ++ Γ) (t.instantiate fs L.length) k := term_instantiate h actuals

/-- Simultaneous function/predicate instantiation preserves the exact predicate signature.
This includes QF results and actuals that capture the caller's numerical locals. -/
public theorem PredicateTyping.instantiate {E Ξ L P σ} (valid : EnvironmentWF E)
    (h : PredicateTyping E Ξ L P σ) {Ω Γ fs ps}
    (actuals : InstantiationTyping E Ξ Ω Γ fs ps) :
    PredicateTyping E Ω (L ++ Γ) (P.instantiate fs ps L.length) σ :=
  predicate_instantiate valid h actuals

/-- A predicate body in a valid environment specializes at its declared signature. -/
public theorem EnvironmentWF.predicate_instance {E : Environment} {Ξ Γ} {name : Lean.Name}
    {fs ps} {d : PredicateDefinition} (valid : EnvironmentWF E)
    (lookup : E[name]? = some (.predicate d))
    (functions : FunctionArguments E Ξ Γ fs d.functions)
    (predicates : PredicateArguments E Ξ Γ ps d.predicates) :
    PredicateTyping E Ξ Γ (d.body.instantiate fs ps) d.signature := by
  obtain ⟨_, formed⟩ := valid.lookup lookup
  cases formed with
  | predicate body =>
      simpa only [List.nil_append, List.length_nil] using
        body.instantiate valid ⟨functions, predicates⟩

/-- Parameter instantiation preserves typed computational conversion under preserved locals. -/
public theorem TermEq.instantiate {E Ξ L t u k} (valid : EnvironmentWF E)
    (h : TermEq E Ξ L t u k) {Ω Γ fs} (actuals : FunctionArguments E Ω Γ fs Ξ.functions) :
    TermEq E Ω (L ++ Γ) (t.instantiate fs L.length) (u.instantiate fs L.length) k :=
  term_eq_instantiate valid h actuals

/-- Parameter instantiation preserves predicate conversion at its exact arity and sort. -/
public theorem PredicateEq.instantiate {E Ξ L P Q σ} (valid : EnvironmentWF E)
    (h : PredicateEq E Ξ L P Q σ) {Ω Γ fs ps} (actuals : InstantiationTyping E Ξ Ω Γ fs ps) :
    PredicateEq E Ω (L ++ Γ) (P.instantiate fs ps L.length) (Q.instantiate fs ps L.length) σ :=
  predicate_eq_instantiate valid h actuals

/-- Simultaneous parameter instantiation preserves explicit proof typing, including every
annotation, hypothesis, and the conclusion. -/
public theorem ProofTyping.instantiate {E Ξ L H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ L H p A) {Ω Γ fs ps} (actuals : InstantiationTyping E Ξ Ω Γ fs ps) :
    ProofTyping E Ω (L ++ Γ) (H.map (Predicate.instantiate fs ps L.length))
      (p.instantiate fs ps L.length) (A.instantiate fs ps L.length) :=
  proof_instantiate valid h actuals

/-- Function actual lists preserve all their interface arities under parameter instantiation. -/
public theorem FunctionArguments.instantiate {E Ξ L ts ks} (h : FunctionArguments E Ξ L ts ks)
    {Ω Γ fs} (actuals : FunctionArguments E Ω Γ fs Ξ.functions) :
    FunctionArguments E Ω (L ++ Γ) (ts.map (Term.instantiate fs L.length)) ks :=
  functions_instantiate h actuals

/-- Predicate actual lists preserve their full interface signatures under instantiation. -/
public theorem PredicateArguments.instantiate {E Ξ L qs signatures} (valid : EnvironmentWF E)
    (h : PredicateArguments E Ξ L qs signatures) {Ω Γ fs ps}
    (actuals : InstantiationTyping E Ξ Ω Γ fs ps) :
    PredicateArguments E Ω (L ++ Γ) (qs.map (Predicate.instantiate fs ps L.length)) signatures :=
  predicates_instantiate valid h actuals

/-- Equality of function actuals is preserved under checked parameter instantiation. -/
public theorem FunctionArgumentEq.instantiate {E Ξ L ts us ks} (valid : EnvironmentWF E)
    (h : FunctionArgumentEq E Ξ L ts us ks) {Ω Γ fs}
    (actuals : FunctionArguments E Ω Γ fs Ξ.functions) :
    FunctionArgumentEq E Ω (L ++ Γ) (ts.map (Term.instantiate fs L.length))
      (us.map (Term.instantiate fs L.length)) ks := function_eq_instantiate valid h actuals

/-- Equality of predicate actuals is preserved at every declared full signature. -/
public theorem PredicateArgumentEq.instantiate {E Ξ L qs rs signatures} (valid : EnvironmentWF E)
    (h : PredicateArgumentEq E Ξ L qs rs signatures) {Ω Γ fs ps}
    (actuals : InstantiationTyping E Ξ Ω Γ fs ps) :
    PredicateArgumentEq E Ω (L ++ Γ) (qs.map (Predicate.instantiate fs ps L.length))
      (rs.map (Predicate.instantiate fs ps L.length)) signatures :=
  predicate_list_eq_instantiate valid h actuals

/-- Formed assumptions remain formed after simultaneous parameter instantiation. -/
public theorem ContextWF.instantiate {E Ξ L H} (valid : EnvironmentWF E)
    (h : ContextWF E Ξ L H) {Ω Γ fs ps} (actuals : InstantiationTyping E Ξ Ω Γ fs ps) :
    ContextWF E Ω (L ++ Γ) (H.map (Predicate.instantiate fs ps L.length)) := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (predicate_instantiate valid head actuals) ih

/-- Definitionally equal assumptions remain equal at Prop after parameter instantiation. -/
public theorem ProofContextEq.instantiate {E Ξ L H K} (valid : EnvironmentWF E)
    (h : ProofContextEq E Ξ L H K) {Ω Γ fs ps} (actuals : InstantiationTyping E Ξ Ω Γ fs ps) :
    ProofContextEq E Ω (L ++ Γ) (H.map (Predicate.instantiate fs ps L.length))
      (K.map (Predicate.instantiate fs ps L.length)) := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (predicate_eq_instantiate valid head actuals) ih

end LeanPRA.Core.Theory
