module

public import PRAProver.Metatheory.Core.Judgement.Defs
import Lean.Elab.Tactic.Omega
import Std.Data.ExtHashMap.Lemmas

/-!
# Renaming and substitution in declarative judgements

- `Proof.subst` and `Proof.rename` transform local numerical occurrences in explicit proof data.
- `TermTyping.rename`, `TermTyping.subst`, and `TermTyping.subst0` preserve numerical arities.
- `PredicateTyping.rename` and `PredicateTyping.subst` preserve full predicate signatures.
- `TermEq.subst` and `PredicateEq.subst` preserve typed conversion; renaming is a special case.
- `ProofTyping.subst` and `ProofTyping.rename` transform proofs, hypotheses, and conclusions.
- `ContextWF.subst` and `ContextWF.rename` preserve the formation of assumptions.
- `FunctionArguments.subst` and `PredicateArguments.subst` preserve declaration actual lists.

The binder lemmas `RenamingTyping.lift` and `SubstitutionTyping.lift` account for newly introduced
variables. Function-valued local substitution is included. Declaration parameters are unchanged
by these local operations; their simultaneous instantiation is a separate operation. Theorems
about transparent bodies require a valid global environment.
-/

namespace PRAProver.Core

/-- Substitute local terms throughout explicit proof data. Proof-hypothesis indices and
declaration parameters are unchanged. Numerical proof binders lift the local substitution. -/
@[expose] public def Proof.subst (s : Subst) : Proof → Proof
  | .hyp i => .hyp i
  | .trueIntro => .trueIntro
  | .theoremE name fs ps =>
      .theoremE name (fs.map (Term.subst s)) (ps.map (Predicate.subst s))
  | .impIntro binderName A p => .impIntro binderName (A.subst s) (p.subst s)
  | .impElim p q => .impElim (p.subst s) (q.subst s)
  | .andIntro p q => .andIntro (p.subst s) (q.subst s)
  | .andLeft a b => .andLeft (a.subst s) (b.subst s)
  | .andRight a b => .andRight (a.subst s) (b.subst s)
  | .orLeft a b => .orLeft (a.subst s) (b.subst s)
  | .orRight a b => .orRight (a.subst s) (b.subst s)
  | .orElim a b c => .orElim (a.subst s) (b.subst s) (c.subst s)
  | .falseElim a => .falseElim (a.subst s)
  | .forallIntro binderName P p => .forallIntro binderName (P.subst s) (p.subst (Subst.lift 1 s))
  | .forallElim p a => .forallElim (p.subst s) (a.subst s)
  | .existsIntro P a p => .existsIntro (P.subst s) (a.subst s) (p.subst s)
  | .existsElim a b => .existsElim (a.subst s) (b.subst s)
  | .letE binderName A p q => .letE binderName (A.subst s) (p.subst s) (q.subst s)
  | .letTerm binderName a p => .letTerm binderName (a.subst s) (p.subst s)
  | .letPredicate binderName P p => .letPredicate binderName (P.subst s) (p.subst s)
  | .ascribe A p => .ascribe (A.subst s) (p.subst s)
  | .eqRefl => .eqRefl
  | .eqSubst a => .eqSubst (a.subst s)
  | .succNeZero => .succNeZero
  | .succInj => .succInj
  | .lem A => .lem (A.subst s)
  | .induction a => .induction (a.subst s)

/-- Rename local term variables in proof data, leaving proof-hypothesis indices unchanged. -/
@[expose] public def Proof.rename (r : Renaming) (p : Proof) : Proof :=
  p.subst fun i => .bvar (r i)

end PRAProver.Core

namespace PRAProver.Core.Theory

private theorem lift_succ_zero (r : Renaming) : Renaming.lift 1 r 0 = 0 := by
  simp [Renaming.lift]

private theorem lift_succ (r : Renaming) (i : Nat) : Renaming.lift 1 r (i + 1) = r i + 1 := by
  simp [Renaming.lift, Nat.add_comm]

private theorem lift_comp (r s : Renaming) (n : Nat) :
    (fun i => Renaming.lift n s (Renaming.lift n r i)) =
      Renaming.lift n (fun i => s (r i)) := by
  funext i
  simp only [Renaming.lift]
  split <;> rename_i h
  · simp
  · simp [show ¬n + r (i - n) < n by omega]

private theorem lift_id (n : Nat) : Renaming.lift n id = id := by
  funext i
  simp only [Renaming.lift, id_eq]
  split <;> omega

private theorem rename_comp (t : Term) (r s : Renaming) :
    (t.rename r).rename s = t.rename (fun i => s (r i)) := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ r s : Renaming,
      (ts.map (Term.rename r)).map (Term.rename s) =
        ts.map (Term.rename (fun i => s (r i)))) generalizing r s <;>
    simp_all [Term.rename, lift_comp]

private theorem rename_id (t : Term) : t.rename id = t := by
  induction t using Term.rec
    (motive_2 := fun ts => ts.map (Term.rename id) = ts) <;>
    simp_all [Term.rename, lift_id]

private theorem rename_shift (t : Term) (r : Renaming) (n : Nat) :
    (t.shift n).rename (Renaming.lift n r) = (t.rename r).shift n := by
  simp only [Term.shift, Nat.not_lt_zero, ↓reduceIte, rename_comp]
  congr 1
  funext i
  simp [Renaming.lift, show ¬n + i < n by omega, Nat.add_comm]

private theorem subst_lift_zero (s : Subst) : Subst.lift 0 s = s := by
  funext i
  simp only [Subst.lift, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, Term.shift, Nat.add_zero]
  rw [show (fun i : Nat => i) = id from rfl]
  exact rename_id _

private theorem subst_lift_rename (r : Renaming) (s : Subst) (n : Nat) :
    (fun i => Subst.lift n s (Renaming.lift n r i)) =
      Subst.lift n (fun i => s (r i)) := by
  funext i
  simp only [Subst.lift, Renaming.lift]
  split <;> rename_i h
  · simp
  · simp [show ¬n + r (i - n) < n by omega]

private theorem rename_subst_lift (s : Subst) (r : Renaming) (n : Nat) :
    (fun i => (Subst.lift n s i).rename (Renaming.lift n r)) =
      Subst.lift n (fun i => (s i).rename r) := by
  funext i
  simp only [Subst.lift]
  split <;> rename_i h
  · simp [Term.rename, Renaming.lift, h]
  · exact rename_shift _ _ _

private theorem subst_rename (t : Term) (r : Renaming) (s : Subst) :
    (t.rename r).subst s = t.subst (fun i => s (r i)) := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ (r : Renaming) (s : Subst),
      (ts.map (Term.rename r)).map (Term.subst s) =
        ts.map (Term.subst (fun i => s (r i)))) generalizing r s <;>
    simp_all [Term.rename, Term.subst, subst_lift_rename]

private theorem rename_subst (t : Term) (s : Subst) (r : Renaming) :
    (t.subst s).rename r = t.subst (fun i => (s i).rename r) := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ (s : Subst) (r : Renaming),
      (ts.map (Term.subst s)).map (Term.rename r) =
        ts.map (Term.subst (fun i => (s i).rename r))) generalizing s r <;>
    simp_all [Term.subst, Term.rename, rename_subst_lift]

private theorem subst_shift (t : Term) (s : Subst) (n : Nat) :
    (t.shift n).subst (Subst.lift n s) = (t.subst s).shift n := by
  simp only [Term.shift, Nat.not_lt_zero, ↓reduceIte, subst_rename, rename_subst]
  congr 1
  funext i
  simp [Subst.lift, Term.shift, show ¬i + n < n by omega]

private theorem subst_lift_comp (s t : Subst) (n : Nat) :
    (fun i => (Subst.lift n s i).subst (Subst.lift n t)) =
      Subst.lift n (fun i => (s i).subst t) := by
  funext i
  simp only [Subst.lift]
  split <;> rename_i h
  · simp [Term.subst, Subst.lift, h]
  · exact subst_shift _ _ _

private theorem subst_comp (t : Term) (s u : Subst) :
    (t.subst s).subst u = t.subst (fun i => (s i).subst u) := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ s u : Subst,
      (ts.map (Term.subst s)).map (Term.subst u) =
        ts.map (Term.subst (fun i => (s i).subst u))) generalizing s u <;>
    simp_all [Term.subst, subst_lift_comp]

private theorem subst_lift_bvar (n : Nat) : Subst.lift n Term.bvar = Term.bvar := by
  funext i
  simp only [Subst.lift, Term.shift, Term.rename]
  split <;> simp_all <;> omega

private theorem subst_id (t : Term) : t.subst Term.bvar = t := by
  induction t using Term.rec
    (motive_2 := fun ts => ts.map (Term.subst Term.bvar) = ts) <;>
    simp_all [Term.subst, subst_lift_bvar]

private theorem subst_lift_add (s : Subst) (m n : Nat) :
    Subst.lift m (Subst.lift n s) = Subst.lift (m + n) s := by
  funext i
  by_cases h : i < m
  · simp [Subst.lift, h, show i < m + n by omega]
  · by_cases h' : i - m < n
    · simp [Subst.lift, h, h', show i < m + n by omega, Term.shift, Term.rename]
      omega
    · simp only [Subst.lift, h, h', show ¬i < m + n by omega, ↓reduceIte,
        Nat.sub_sub, Term.shift, Nat.not_lt_zero, ↓reduceIte, rename_comp]
      congr 1
      funext j
      omega

private theorem predicate_subst_rename (P : Predicate) (r : Renaming) (s : Subst) :
    (P.rename r).subst s = P.subst (fun i => s (r i)) := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ (r : Renaming) (s : Subst),
      (ps.map (Predicate.rename r)).map (Predicate.subst s) =
        ps.map (Predicate.subst (fun i => s (r i)))) generalizing r s <;>
    simp_all [Predicate.rename, Predicate.subst, subst_rename, subst_lift_rename, List.map_map]

private theorem predicate_rename_subst (P : Predicate) (s : Subst) (r : Renaming) :
    (P.subst s).rename r = P.subst (fun i => (s i).rename r) := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ (s : Subst) (r : Renaming),
      (ps.map (Predicate.subst s)).map (Predicate.rename r) =
        ps.map (Predicate.subst (fun i => (s i).rename r))) generalizing s r <;>
    simp_all [Predicate.subst, Predicate.rename, rename_subst, rename_subst_lift, List.map_map]

private theorem predicate_subst_comp (P : Predicate) (s u : Subst) :
    (P.subst s).subst u = P.subst (fun i => (s i).subst u) := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ s u : Subst,
      (ps.map (Predicate.subst s)).map (Predicate.subst u) =
        ps.map (Predicate.subst (fun i => (s i).subst u))) generalizing s u <;>
    simp_all [Predicate.subst, subst_comp, subst_lift_comp, List.map_map]

private theorem rename_as_subst (t : Term) (r : Renaming) :
    t.rename r = t.subst (fun i => .bvar (r i)) := by
  have lift (r : Renaming) : Subst.lift 1 (fun i => .bvar (r i)) =
      fun i => .bvar (Renaming.lift 1 r i) := by
    funext i
    cases i <;> simp [Subst.lift, Renaming.lift, Term.shift, Term.rename, Nat.add_comm]
  induction t using Term.rec
    (motive_2 := fun ts => ∀ r : Renaming,
      ts.map (Term.rename r) = ts.map (Term.subst (fun i => .bvar (r i)))) generalizing r <;>
    simp_all [Term.rename, Term.subst]

private theorem predicate_rename_as_subst (P : Predicate) (r : Renaming) :
    P.rename r = P.subst (fun i => .bvar (r i)) := by
  have lift (r : Renaming) : Subst.lift 1 (fun i => .bvar (r i)) =
      fun i => .bvar (Renaming.lift 1 r i) := by
    funext i
    cases i <;> simp [Subst.lift, Renaming.lift, Term.shift, Term.rename, Nat.add_comm]
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ r : Renaming,
      ps.map (Predicate.rename r) = ps.map (Predicate.subst (fun i => .bvar (r i))))
    generalizing r <;> simp_all [Predicate.rename, Predicate.subst, rename_as_subst]

private theorem renaming_lift {Γ Δ : LocalContext} {r : Renaming}
    (h : RenamingTyping Γ Δ r) (k : Arity) :
    RenamingTyping (k :: Γ) (k :: Δ) (Renaming.lift 1 r) := by
  intro i j hi
  cases i with
  | zero => simpa [lift_succ_zero] using hi
  | succ i => simpa [lift_succ] using h i j hi

private theorem term_rename {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k)
    {Δ : LocalContext} (r : Renaming) (hr : RenamingTyping Γ Δ r) :
    TermTyping E Ξ Δ (t.rename r) k := by
  induction h using TermTyping.rec
    (motive_2 := fun Γ fs ks _ => ∀ {Δ} (r : Renaming), RenamingTyping Γ Δ r →
      FunctionArguments E Ξ Δ (fs.map (Term.rename r)) ks) generalizing Δ r with
  | bvar lookup => simp only [Term.rename]; exact .bvar (hr _ _ lookup)
  | parameter lookup => simp only [Term.rename]; exact .parameter lookup
  | zero => simp only [Term.rename]; exact .zero
  | succ => simp only [Term.rename]; exact .succ
  | lam body ih => simp only [Term.rename]; exact .lam (ih _ (renaming_lift hr 0))
  | app f a ihf iha => simp only [Term.rename]; exact .app (ihf _ hr) (iha _ hr)
  | letE a body iha ihb =>
      simp only [Term.rename]; exact .letE (iha _ hr) (ihb _ (renaming_lift hr _))
  | primrec b s ihb ihs =>
      simp only [Term.rename]; exact .primrec (ihb _ hr) (ihs _ hr)
  | definition lookup args ih => simp only [Term.rename]; exact .definition lookup (ih _ hr)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i Δ r hr
      exact .cons (ihh _ hr) (iht _ hr)

private theorem term_shift {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k) (j : Arity) :
    TermTyping E Ξ (j :: Γ) t.shift k := by
  simpa only [Term.shift, Nat.not_lt_zero, ↓reduceIte] using
    term_rename h (fun i => i + 1) (by intro i a hi; exact hi)

private theorem substitution_lift {E Ξ Γ Δ s}
    (h : SubstitutionTyping E Ξ Γ Δ s) (k : Arity) :
    SubstitutionTyping E Ξ (k :: Γ) (k :: Δ) (Subst.lift 1 s) := by
  intro i j hi
  cases i with
  | zero => simpa [Subst.lift, Term.subst] using (TermTyping.bvar hi :
      TermTyping E Ξ (k :: Δ) (.bvar 0) j)
  | succ i => simpa [Subst.lift] using term_shift (h i j hi) k

private theorem term_subst {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k)
    {Δ : LocalContext} (s : Subst) (hs : SubstitutionTyping E Ξ Γ Δ s) :
    TermTyping E Ξ Δ (t.subst s) k := by
  induction h using TermTyping.rec
    (motive_2 := fun Γ fs ks _ => ∀ {Δ} (s : Subst), SubstitutionTyping E Ξ Γ Δ s →
      FunctionArguments E Ξ Δ (fs.map (Term.subst s)) ks) generalizing Δ s with
  | bvar lookup => simp only [Term.subst]; exact hs _ _ lookup
  | parameter lookup => simp only [Term.subst]; exact .parameter lookup
  | zero => simp only [Term.subst]; exact .zero
  | succ => simp only [Term.subst]; exact .succ
  | lam body ih => simp only [Term.subst]; exact .lam (ih _ (substitution_lift hs 0))
  | app f a ihf iha => simp only [Term.subst]; exact .app (ihf _ hs) (iha _ hs)
  | letE a body iha ihb =>
      simp only [Term.subst]; exact .letE (iha _ hs) (ihb _ (substitution_lift hs _))
  | primrec b s ihb ihs =>
      simp only [Term.subst]; exact .primrec (ihb _ hs) (ihs _ hs)
  | definition lookup args ih => simp only [Term.subst]; exact .definition lookup (ih _ hs)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i Δ s hs
      exact .cons (ihh _ hs) (iht _ hs)

/-- Every local variable in a term lies below the specified binder depth. -/
private def TermScoped : Nat → Term → Prop
  | n, .bvar i => i < n
  | _, .parameter _ | _, .zero | _, .succ => True
  | n, .lam _ t => TermScoped (n + 1) t
  | n, .app f a => TermScoped n f ∧ TermScoped n a
  | n, .letE _ a t => TermScoped n a ∧ TermScoped (n + 1) t
  | n, .primrec b s => TermScoped n b ∧ TermScoped n s
  | n, .definition _ fs => ∀ t ∈ fs, TermScoped n t

private def PredicateScoped : Nat → Predicate → Prop
  | _, .false | _, .true | _, .parameter _ => True
  | n, .equal a b => TermScoped n a ∧ TermScoped n b
  | n, .imp A B | n, .and A B | n, .or A B => PredicateScoped n A ∧ PredicateScoped n B
  | n, .all P | n, .ex P => PredicateScoped n P
  | n, .lam _ P => PredicateScoped (n + 1) P
  | n, .app P a => PredicateScoped n P ∧ TermScoped n a
  | n, .letTerm _ a P => TermScoped n a ∧ PredicateScoped n P
  | n, .letPredicate _ Q P => PredicateScoped n Q ∧ PredicateScoped n P
  | n, .definition _ fs ps =>
      (∀ t ∈ fs, TermScoped n t) ∧ (∀ P ∈ ps, PredicateScoped n P)

private theorem term_scoped {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k) :
    TermScoped Γ.length t := by
  induction h using TermTyping.rec
    (motive_2 := fun Γ fs _ _ => ∀ t ∈ fs, TermScoped Γ.length t) <;>
    try simp only [TermScoped, List.length_cons] at *
  case bvar lookup => exact (List.getElem?_eq_some_iff.mp lookup).choose
  case lam body ih => exact ih
  case app f a ihf iha => exact ⟨ihf, iha⟩
  case letE a body iha ihb => exact ⟨iha, ihb⟩
  case primrec b s ihb ihs => exact ⟨ihb, ihs⟩
  case definition lookup args ih => exact ih
  case nil => contradiction
  case cons ihh iht t ht =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ihh
      · exact iht _ ht

private theorem arguments_scoped {E Ξ Γ fs ks} (h : FunctionArguments E Ξ Γ fs ks) :
    ∀ t ∈ fs, TermScoped Γ.length t := by
  induction h using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => intro t ht; contradiction
  case cons head tail ihh iht =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact term_scoped head
      · exact iht t ht
  all_goals trivial

private theorem predicate_scoped {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ) :
    PredicateScoped Γ.length P := by
  induction h using PredicateTyping.rec
    (motive_2 := fun Γ ps _ _ => ∀ P ∈ ps, PredicateScoped Γ.length P) <;>
    try simp only [PredicateScoped, List.length_cons] at *
  case equal a b => exact ⟨term_scoped a, term_scoped b⟩
  case imp A B ihA ihB => exact ⟨ihA, ihB⟩
  case and A B ihA ihB => exact ⟨ihA, ihB⟩
  case or A B ihA ihB => exact ⟨ihA, ihB⟩
  case all P ih => exact ih
  case ex P ih => exact ih
  case lam P ih => exact ih
  case app P a ih => exact ⟨ih, term_scoped a⟩
  case letTerm a P ih => exact ⟨term_scoped a, ih⟩
  case letPredicate Q P ihQ ihP => exact ⟨ihQ, ihP⟩
  case definition lookup fs ps ihps =>
      exact ⟨arguments_scoped fs, ihps⟩
  case subsumption h sub ih => exact ih
  case nil => contradiction
  case cons ihh iht P hP =>
      rcases List.mem_cons.mp hP with rfl | hP
      · exact ihh
      · exact iht _ hP

private def DeclarationScoped : Declaration → Prop
  | .function d => TermScoped 0 d.body
  | .predicate d => PredicateScoped 0 d.body
  | .theoremE d => PredicateScoped 0 d.type

private theorem declaration_scoped {E d} (h : DeclarationWF E d) : DeclarationScoped d := by
  cases h <;> simp only [DeclarationScoped]
  case function body => exact term_scoped body
  case predicate body => exact predicate_scoped body
  case theoremE type body => exact predicate_scoped type

private theorem environment_scoped {E} (h : EnvironmentWF E) :
    ∀ (name : Lean.Name) d, E[name]? = some d → DeclarationScoped d := by
  induction h with
  | empty => intro name d lookup; simp at lookup
  | @insert E d valid fresh wellformed ih =>
      intro name e lookup
      by_cases heq : d.name = name
      · subst name
        have : d = e := Option.some.inj (by simpa using lookup)
        subst e
        exact declaration_scoped wellformed
      · exact ih _ _ (by simpa [Std.ExtHashMap.getElem?_insert, heq] using lookup)

private theorem instantiate_subst (t : Term) (n : Nat) (h : TermScoped n t)
    (fs : List Term) (s : Subst) :
    (t.instantiate fs n).subst (Subst.lift n s) = t.instantiate (fs.map (Term.subst s)) n := by
  cases t with
  | bvar i =>
      simp only [TermScoped] at h
      simp [Term.instantiate, Term.subst, Subst.lift, h]
  | parameter i =>
      simp only [Term.instantiate, List.getElem?_map]
      cases fs[i]? with
      | none => simp [Term.shift, Term.rename, Term.subst]
      | some a => simpa using subst_shift a s n
  | zero => simp [Term.instantiate, Term.subst]
  | succ => simp [Term.instantiate, Term.subst]
  | lam _ t =>
      simp only [TermScoped] at h
      simp only [Term.instantiate, Term.subst, subst_lift_add, Nat.add_comm 1 n]
      exact congrArg (fun t => Term.lam _ t) (instantiate_subst t (n + 1) h fs s)
  | app f a =>
      simp only [TermScoped] at h
      simp only [Term.instantiate, Term.subst]
      rw [instantiate_subst f n h.1 fs s, instantiate_subst a n h.2 fs s]
  | letE _ a t =>
      simp only [TermScoped] at h
      simp only [Term.instantiate, Term.subst, subst_lift_add, Nat.add_comm 1 n]
      rw [instantiate_subst a n h.1 fs s, instantiate_subst t (n + 1) h.2 fs s]
  | primrec b step =>
      simp only [TermScoped] at h
      simp only [Term.instantiate, Term.subst]
      rw [instantiate_subst b n h.1 fs s, instantiate_subst step n h.2 fs s]
  | definition name ts =>
      simp only [TermScoped] at h
      simp only [Term.instantiate, Term.subst, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      exact instantiate_subst t n (h t ht) fs s
termination_by sizeOf t

private theorem predicate_subst_shift (P : Predicate) (s : Subst) (n : Nat) :
    (P.shift n).subst (Subst.lift n s) = (P.subst s).shift n := by
  simp only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte,
    predicate_subst_rename, predicate_rename_subst]
  congr 1
  funext i
  simp [Subst.lift, Term.shift, show ¬i + n < n by omega]

private theorem predicate_instantiate_subst (P : Predicate) (n : Nat) (h : PredicateScoped n P)
    (fs : List Term) (ps : List Predicate) (s : Subst) :
    (P.instantiate fs ps n).subst (Subst.lift n s) =
      P.instantiate (fs.map (Term.subst s)) (ps.map (Predicate.subst s)) n := by
  cases P with
  | false => simp [Predicate.instantiate, Predicate.subst]
  | true => simp [Predicate.instantiate, Predicate.subst]
  | parameter i =>
      simp only [Predicate.instantiate, List.getElem?_map]
      cases ps[i]? with
      | none => simp [Predicate.shift, Predicate.rename, Predicate.subst]
      | some Q => simpa using predicate_subst_shift Q s n
  | equal a b =>
      simp only [PredicateScoped] at h
      simp [Predicate.instantiate, Predicate.subst, instantiate_subst a n h.1,
        instantiate_subst b n h.2]
  | imp A B | and A B | or A B =>
      simp only [PredicateScoped] at h
      simp only [Predicate.instantiate, Predicate.subst]
      rw [predicate_instantiate_subst A n h.1 fs ps s,
        predicate_instantiate_subst B n h.2 fs ps s]
  | all P | ex P =>
      simp only [PredicateScoped] at h
      simp only [Predicate.instantiate, Predicate.subst]
      rw [predicate_instantiate_subst P n h fs ps s]
  | lam _ P =>
      simp only [PredicateScoped] at h
      simp only [Predicate.instantiate, Predicate.subst, subst_lift_add, Nat.add_comm 1 n]
      exact congrArg (fun t => Predicate.lam _ t) (predicate_instantiate_subst P
          (n + 1) h fs ps s)
  | app P a =>
      simp only [PredicateScoped] at h
      simp only [Predicate.instantiate, Predicate.subst]
      rw [predicate_instantiate_subst P n h.1 fs ps s, instantiate_subst a n h.2 fs s]
  | letTerm _ a P =>
      simp only [PredicateScoped] at h
      simp only [Predicate.instantiate, Predicate.subst]
      rw [instantiate_subst a n h.1 fs s, predicate_instantiate_subst P n h.2 fs ps s]
  | letPredicate _ Q P =>
      simp only [PredicateScoped] at h
      simp only [Predicate.instantiate, Predicate.subst]
      rw [predicate_instantiate_subst Q n h.1 fs ps s,
        predicate_instantiate_subst P n h.2 fs ps s]
  | definition name ts qs =>
      simp only [PredicateScoped] at h
      simp only [Predicate.instantiate, Predicate.subst, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro t ht
        exact instantiate_subst t n (h.1 t ht) fs s
      · apply List.map_congr_left
        intro Q hQ
        exact predicate_instantiate_subst Q n (h.2 Q hQ) fs ps s
termination_by sizeOf P

private theorem arguments_subst {E Ξ Γ fs ks} (h : FunctionArguments E Ξ Γ fs ks)
    {Δ : LocalContext} (s : Subst) (hs : SubstitutionTyping E Ξ Γ Δ s) :
    FunctionArguments E Ξ Δ (fs.map (Term.subst s)) ks := by
  induction h using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True)
    generalizing Δ s
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (term_subst head s hs) (iht _ hs)
  all_goals trivial

private theorem predicate_subst {E Ξ Γ P σ} (_valid : EnvironmentWF E)
    (h : PredicateTyping E Ξ Γ P σ) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) : PredicateTyping E Ξ Δ (P.subst s) σ := by
  induction h using PredicateTyping.rec
    (motive_2 := fun Γ ps signatures _ => ∀ {Δ} (s : Subst),
      SubstitutionTyping E Ξ Γ Δ s →
        PredicateArguments E Ξ Δ (ps.map (Predicate.subst s)) signatures)
    generalizing Δ s with
  | false => simp only [Predicate.subst]; exact .false
  | true => simp only [Predicate.subst]; exact .true
  | equal a b => simp only [Predicate.subst]; exact .equal (term_subst a s hs) (term_subst b s hs)
  | imp A B ihA ihB => simp only [Predicate.subst]; exact .imp (ihA _ hs) (ihB _ hs)
  | and A B ihA ihB => simp only [Predicate.subst]; exact .and (ihA _ hs) (ihB _ hs)
  | or A B ihA ihB => simp only [Predicate.subst]; exact .or (ihA _ hs) (ihB _ hs)
  | all P ih => simp only [Predicate.subst]; exact .all (ih _ hs)
  | ex P ih => simp only [Predicate.subst]; exact .ex (ih _ hs)
  | parameter lookup => simp only [Predicate.subst]; exact .parameter lookup
  | lam P ih => simp only [Predicate.subst]; exact .lam (ih _ (substitution_lift hs 0))
  | app P a ih => simp only [Predicate.subst]; exact .app (ih _ hs) (term_subst a s hs)
  | letTerm a P ih =>
      simp only [Predicate.subst]; exact .letTerm (term_subst a s hs) (ih _ hs)
  | letPredicate Q P ihQ ihP =>
      simp only [Predicate.subst]; exact .letPredicate (ihQ _ hs) (ihP _ hs)
  | definition lookup functions predicates ihps =>
      simp only [Predicate.subst]
      exact .definition lookup (arguments_subst functions s hs) (ihps _ hs)
  | subsumption h sub ih => exact .subsumption (ih _ hs) sub
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i Δ s hs
      exact .cons (ihh _ hs) (iht _ hs)

private theorem predicate_rename {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (h : PredicateTyping E Ξ Γ P σ) {Δ : LocalContext} (r : Renaming)
    (hr : RenamingTyping Γ Δ r) : PredicateTyping E Ξ Δ (P.rename r) σ := by
  rw [predicate_rename_as_subst]
  exact predicate_subst valid h _ (fun i k hi => .bvar (hr i k hi))

private theorem predicates_subst {E Ξ Γ ps signatures} (valid : EnvironmentWF E)
    (h : PredicateArguments E Ξ Γ ps signatures) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) :
    PredicateArguments E Ξ Δ (ps.map (Predicate.subst s)) signatures := by
  induction h using PredicateArguments.rec (motive_1 := fun _ _ _ _ => True)
    generalizing Δ s
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (predicate_subst valid head _ hs) (iht _ hs)
  all_goals trivial

private theorem subst0_shift (t a : Term) : t.shift.subst0 a = t := by
  simp only [Term.shift, Nat.not_lt_zero, ↓reduceIte, Term.subst0, subst_rename]
  exact subst_id t

private theorem subst0_subst (t a : Term) (s : Subst) :
    (t.subst0 a).subst s = (t.subst (Subst.lift 1 s)).subst0 (a.subst s) := by
  simp only [Term.subst0, subst_comp]
  congr 1
  funext i
  cases i with
  | zero => simp [Subst.lift, Term.subst]
  | succ i =>
      simp only [Subst.lift, show ¬i + 1 < 1 by omega, ↓reduceIte,
        Nat.add_sub_cancel, Term.subst]
      simpa only [Term.subst0] using (subst0_shift (s i) (a.subst s)).symm

private theorem predicate_subst0_subst (P : Predicate) (a : Term) (s : Subst) :
    (P.subst0 a).subst s = (P.subst (Subst.lift 1 s)).subst0 (a.subst s) := by
  simp only [Predicate.subst0, predicate_subst_comp]
  congr 1
  funext i
  cases i with
  | zero => simp [Subst.lift, Term.subst]
  | succ i =>
      simp only [Subst.lift, show ¬i + 1 < 1 by omega, ↓reduceIte,
        Nat.add_sub_cancel, Term.subst]
      simpa only [Term.subst0] using (subst0_shift (s i) (a.subst s)).symm

private theorem subst_lift_head (s : Subst) : Subst.lift 1 s 0 = .bvar 0 := by
  simp [Subst.lift]

private theorem term_eq_subst {E Ξ Γ t u k} (valid : EnvironmentWF E)
    (h : TermEq E Ξ Γ t u k) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) : TermEq E Ξ Δ (t.subst s) (u.subst s) k := by
  induction h using TermEq.rec
    (motive_2 := fun Γ fs gs ks _ => ∀ {Δ} (s : Subst), SubstitutionTyping E Ξ Γ Δ s →
      FunctionArgumentEq E Ξ Δ (fs.map (Term.subst s)) (gs.map (Term.subst s)) ks)
    generalizing Δ s with
  | refl typing => exact .refl (term_subst typing s hs)
  | symm h ih => exact .symm (ih _ hs)
  | trans h g ihh ihg => exact .trans (ihh _ hs) (ihg _ hs)
  | beta body arg =>
      simp only [Term.subst, subst0_subst]
      exact .beta (term_subst body _ (substitution_lift hs 0)) (term_subst arg _ hs)
  | eta function =>
      simp only [Term.subst, subst_lift_head, subst_shift]
      exact .eta (term_subst function _ hs)
  | zeta value body =>
      simp only [Term.subst, subst0_subst]
      exact .zeta (term_subst value _ hs) (term_subst body _ (substitution_lift hs _))
  | @delta name Γ fs d lookup args body =>
      have closed : TermScoped 0 d.body := environment_scoped valid name _ lookup
      have commute := instantiate_subst d.body 0 closed fs s
      simp only [subst_lift_zero] at commute
      simp only [Term.subst]
      rw [commute]
      have hb := term_subst body s hs
      rw [commute] at hb
      exact .delta lookup (arguments_subst args s hs) hb
  | primrecZero base step =>
      simp only [Term.subst]
      exact .primrecZero (term_subst base _ hs) (term_subst step _ hs)
  | primrecSucc base step arg =>
      simp only [Term.subst]
      exact .primrecSucc (term_subst base _ hs) (term_subst step _ hs) (term_subst arg _ hs)
  | lam body ih => simp only [Term.subst]; exact .lam (ih _ (substitution_lift hs 0))
  | app f a ihf iha => simp only [Term.subst]; exact .app (ihf _ hs) (iha _ hs)
  | letE a body iha ihb =>
      simp only [Term.subst]; exact .letE (iha _ hs) (ihb _ (substitution_lift hs _))
  | primrec b step ihb ihs =>
      simp only [Term.subst]; exact .primrec (ihb _ hs) (ihs _ hs)
  | definition lookup args ih => simp only [Term.subst]; exact .definition lookup (ih _ hs)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i Δ s hs
      exact .cons (ihh _ hs) (iht _ hs)

private theorem argument_eq_subst {E Ξ Γ fs gs ks} (valid : EnvironmentWF E)
    (h : FunctionArgumentEq E Ξ Γ fs gs ks) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) :
    FunctionArgumentEq E Ξ Δ (fs.map (Term.subst s)) (gs.map (Term.subst s)) ks := by
  induction h using FunctionArgumentEq.rec (motive_1 := fun _ _ _ _ _ => True)
    generalizing Δ s
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (term_eq_subst valid head s hs) (iht _ hs)
  all_goals trivial

private theorem predicate_eq_subst {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (h : PredicateEq E Ξ Γ P Q σ) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) : PredicateEq E Ξ Δ (P.subst s) (Q.subst s) σ := by
  induction h using PredicateEq.rec
    (motive_2 := fun Γ ps qs signatures _ => ∀ {Δ} (s : Subst),
      SubstitutionTyping E Ξ Γ Δ s → PredicateArgumentEq E Ξ Δ
        (ps.map (Predicate.subst s)) (qs.map (Predicate.subst s)) signatures)
    generalizing Δ s with
  | refl typing => exact .refl (predicate_subst valid typing _ hs)
  | symm h ih => exact .symm (ih _ hs)
  | trans h g ihh ihg => exact .trans (ihh _ hs) (ihg _ hs)
  | subsumption h sub ih => exact .subsumption (ih _ hs) sub
  | beta body arg =>
      simp only [Predicate.subst, predicate_subst0_subst]
      exact .beta (predicate_subst valid body _ (substitution_lift hs 0)) (term_subst arg _ hs)
  | eta function =>
      simp only [Predicate.subst, Term.subst, subst_lift_head, predicate_subst_shift]
      exact .eta (predicate_subst valid function _ hs)
  | zetaTerm a P =>
      simp only [Predicate.subst]
      exact .zetaTerm (term_subst a _ hs) (predicate_subst valid P _ hs)
  | zetaPredicate Q P =>
      simp only [Predicate.subst]
      exact .zetaPredicate (predicate_subst valid Q _ hs) (predicate_subst valid P _ hs)
  | @delta name Γ fs ps σ d lookup functions predicates body bound =>
      have closed : PredicateScoped 0 d.body := environment_scoped valid name _ lookup
      have commute := predicate_instantiate_subst d.body 0 closed fs ps s
      simp only [subst_lift_zero] at commute
      simp only [Predicate.subst]
      rw [commute]
      have hb := predicate_subst valid body s hs
      rw [commute] at hb
      exact .delta lookup (arguments_subst functions s hs)
        (predicates_subst valid predicates s hs) hb bound
  | equal a b =>
      simp only [Predicate.subst]
      exact .equal (term_eq_subst valid a _ hs) (term_eq_subst valid b _ hs)
  | imp A B ihA ihB => simp only [Predicate.subst]; exact .imp (ihA _ hs) (ihB _ hs)
  | and A B ihA ihB => simp only [Predicate.subst]; exact .and (ihA _ hs) (ihB _ hs)
  | or A B ihA ihB => simp only [Predicate.subst]; exact .or (ihA _ hs) (ihB _ hs)
  | all P ih => simp only [Predicate.subst]; exact .all (ih _ hs)
  | ex P ih => simp only [Predicate.subst]; exact .ex (ih _ hs)
  | lam P ih => simp only [Predicate.subst]; exact .lam (ih _ (substitution_lift hs 0))
  | app P a ih =>
      simp only [Predicate.subst]; exact .app (ih _ hs) (term_eq_subst valid a _ hs)
  | definition lookup functions predicates left right ih =>
      simp only [Predicate.subst]
      exact .definition lookup (argument_eq_subst valid functions _ hs) (ih _ hs)
        (by simpa only [Predicate.subst] using predicate_subst valid left s hs)
        (by simpa only [Predicate.subst] using predicate_subst valid right s hs)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i Δ s hs
      exact .cons (ihh _ hs) (iht _ hs)

private theorem hypotheses_subst_shift (H : ProofContext) (s : Subst) :
    (H.map Predicate.shift).map (Predicate.subst (Subst.lift 1 s)) =
      (H.map (Predicate.subst s)).map Predicate.shift := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro P hP
  exact predicate_subst_shift P s 1

private theorem proof_subst {E Ξ Γ H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H p A) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) :
    ProofTyping E Ξ Δ (H.map (Predicate.subst s)) (p.subst s) (A.subst s) := by
  induction h generalizing Δ s with
  | hyp lookup =>
      simp only [Proof.subst]
      exact .hyp (by simp only [List.getElem?_map, lookup, Option.map_some])
  | trueIntro => simp only [Proof.subst, Predicate.subst]; exact .trueIntro
  | @theoremE name Γ fs ps H d lookup functions predicates =>
      simp only [Proof.subst]
      have closed : PredicateScoped 0 d.type := environment_scoped valid name _ lookup
      have commute := predicate_instantiate_subst d.type 0 closed fs ps s
      simp only [subst_lift_zero] at commute
      rw [commute]
      exact .theoremE lookup (arguments_subst functions s hs)
        (predicates_subst valid predicates s hs)
  | impIntro antecedent body ih =>
      simp only [Proof.subst, Predicate.subst]
      exact .impIntro (predicate_subst valid antecedent _ hs) (ih _ hs)
  | impElim f a ihf iha =>
      simp only [Proof.subst]
      apply ProofTyping.impElim (A := _)
      · simpa only [Predicate.subst] using ihf s hs
      · exact iha s hs
  | andIntro a b iha ihb =>
      simp only [Proof.subst, Predicate.subst]; exact .andIntro (iha _ hs) (ihb _ hs)
  | andLeft a b =>
      simpa [Proof.subst, Predicate.subst] using
        (ProofTyping.andLeft (predicate_subst valid a s hs) (predicate_subst valid b s hs)
          (E := E) (Ξ := Ξ) (Γ := Δ) (H := _))
  | andRight a b =>
      simpa [Proof.subst, Predicate.subst] using
        (ProofTyping.andRight (predicate_subst valid a s hs) (predicate_subst valid b s hs)
          (E := E) (Ξ := Ξ) (Γ := Δ) (H := _))
  | orLeft a b =>
      simpa [Proof.subst, Predicate.subst] using
        (ProofTyping.orLeft (predicate_subst valid a s hs) (predicate_subst valid b s hs)
          (E := E) (Ξ := Ξ) (Γ := Δ) (H := _))
  | orRight a b =>
      simpa [Proof.subst, Predicate.subst] using
        (ProofTyping.orRight (predicate_subst valid a s hs) (predicate_subst valid b s hs)
          (E := E) (Ξ := Ξ) (Γ := Δ) (H := _))
  | orElim a b c =>
      simpa [Proof.subst, Predicate.subst] using
        (ProofTyping.orElim (predicate_subst valid a s hs)
          (predicate_subst valid b s hs)
          (predicate_subst valid c s hs)
          (E := E) (Ξ := Ξ) (Γ := Δ) (H := _))
  | falseElim a =>
      simpa [Proof.subst, Predicate.subst] using
        (ProofTyping.falseElim (predicate_subst valid a s hs) (E := E) (Ξ := Ξ) (Γ := Δ) (H := _))
  | forallIntro motive body ih =>
      simp only [Proof.subst, Predicate.subst]
      apply ProofTyping.forallIntro (predicate_subst valid motive _ hs)
      simpa only [Predicate.subst, Term.subst, subst_lift_head, predicate_subst_shift,
        hypotheses_subst_shift] using ih (Subst.lift 1 s) (substitution_lift hs 0)
  | forallElim proof argument ih =>
      simp only [Proof.subst, Predicate.subst]
      exact .forallElim (by simpa only [Predicate.subst] using ih s hs) (term_subst argument _ hs)
  | existsIntro motive witness proof ih =>
      simp only [Proof.subst, Predicate.subst]
      exact .existsIntro (predicate_subst valid motive _ hs) (term_subst witness _ hs)
        (by simpa only [Predicate.subst] using ih s hs)
  | existsElim a b =>
      simpa [Proof.subst, Predicate.subst, existentialEliminationType,
        Term.subst, subst_lift_add, predicate_subst_shift, Subst.lift] using
        (ProofTyping.existsElim (predicate_subst valid a s hs) (predicate_subst valid b s hs)
          (E := E) (Ξ := Ξ) (Γ := Δ) (H := _))
  | letE type value body ihv ihb =>
      simp only [Proof.subst]
      exact .letE (predicate_subst valid type _ hs) (ihv _ hs) (ihb _ hs)
  | letTerm a p ih =>
      simp only [Proof.subst]; exact .letTerm (term_subst a _ hs) (ih _ hs)
  | letPredicate P p ih =>
      simp only [Proof.subst]; exact .letPredicate (predicate_subst valid P _ hs) (ih _ hs)
  | ascribe type proof ih =>
      simp only [Proof.subst]; exact .ascribe (predicate_subst valid type _ hs) (ih _ hs)
  | eqRefl =>
      simpa [Proof.subst, Predicate.subst, reflexivityType,
        Term.subst, subst_lift_add, predicate_subst_shift, Subst.lift] using
        (ProofTyping.eqRefl (E := E) (Ξ := Ξ) (Γ := Δ) (H := _))
  | eqSubst a =>
      simpa [Proof.subst, Predicate.subst, substitutionType,
        Term.subst, subst_lift_add, predicate_subst_shift, Subst.lift] using
        (ProofTyping.eqSubst (predicate_subst valid a s hs) (E := E) (Ξ := Ξ) (Γ := Δ) (H := _))
  | succNeZero =>
      simpa [Proof.subst, Predicate.subst, successorNonzeroType,
        Term.subst, subst_lift_add, predicate_subst_shift, Subst.lift] using
        (ProofTyping.succNeZero (E := E) (Ξ := Ξ) (Γ := Δ) (H := _))
  | succInj =>
      simpa [Proof.subst, Predicate.subst, successorInjectivityType,
        Term.subst, subst_lift_add, predicate_subst_shift, Subst.lift] using
        (ProofTyping.succInj (E := E) (Ξ := Ξ) (Γ := Δ) (H := _))
  | lem formula =>
      simp only [Proof.subst, Predicate.subst]; exact .lem (predicate_subst valid formula _ hs)
  | induction a =>
      simpa [Proof.subst, Predicate.subst, inductionType,
        Term.subst, subst_lift_add, predicate_subst_shift, Subst.lift] using
        (ProofTyping.induction (predicate_subst valid a s hs) (E := E) (Ξ := Ξ) (Γ := Δ) (H := _))
  | conversion proof type ih =>
      exact .conversion (ih _ hs) (predicate_eq_subst valid type _ hs)

/-- Renaming preserves the arity of every term, including declaration and recursor actuals. -/
public theorem TermTyping.rename {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k)
    {Δ : LocalContext} (r : Renaming) (hr : RenamingTyping Γ Δ r) :
    TermTyping E Ξ Δ (t.rename r) k := term_rename h r hr

/-- Simultaneous local substitution preserves term typing, also for function-valued locals. -/
public theorem TermTyping.subst {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k)
    {Δ : LocalContext} (s : Subst) (hs : SubstitutionTyping E Ξ Γ Δ s) :
    TermTyping E Ξ Δ (t.subst s) k := term_subst h s hs

/-- Introducing a local variable shifts a term without changing its numerical arity. -/
public theorem TermTyping.shift {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k) (j : Arity) :
    TermTyping E Ξ (j :: Γ) t.shift k := term_shift h j

/-- Removing a let or lambda binder preserves typing at its original arity. -/
public theorem TermTyping.subst0 {E Ξ Γ t k a j}
    (body : TermTyping E Ξ (j :: Γ) t k) (argument : TermTyping E Ξ Γ a j) :
    TermTyping E Ξ Γ (t.subst0 a) k := by
  apply term_subst body
  intro i l hi
  cases i with
  | zero => have hj : j = l := Option.some.inj hi; subst l; exact argument
  | succ i => exact .bvar hi

/-- A valid environment permits substitution through transparent predicates at the same full
signature. In particular, a QF result remains QF. -/
public theorem PredicateTyping.subst {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (h : PredicateTyping E Ξ Γ P σ) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) : PredicateTyping E Ξ Δ (P.subst s) σ :=
  predicate_subst valid h s hs

/-- Renaming preserves predicate arity and sort. -/
public theorem PredicateTyping.rename {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (h : PredicateTyping E Ξ Γ P σ) {Δ : LocalContext} (r : Renaming)
    (hr : RenamingTyping Γ Δ r) : PredicateTyping E Ξ Δ (P.rename r) σ :=
  predicate_rename valid h r hr

/-- Introducing a local variable shifts a predicate while preserving its full signature. -/
public theorem PredicateTyping.shift {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (h : PredicateTyping E Ξ Γ P σ) (j : Arity) :
    PredicateTyping E Ξ (j :: Γ) P.shift σ := by
  simpa only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte] using
    predicate_rename valid h (fun i => i + 1) (by intro i k hi; exact hi)

/-- Numerical substitution into a predicate lambda preserves its result signature. -/
public theorem PredicateTyping.subst0 {E Ξ Γ P σ a} (valid : EnvironmentWF E)
    (body : PredicateTyping E Ξ (0 :: Γ) P σ) (argument : TermTyping E Ξ Γ a 0) :
    PredicateTyping E Ξ Γ (P.subst0 a) σ := by
  apply predicate_subst valid body
  intro i k hi
  cases i with
  | zero => have hk : 0 = k := Option.some.inj hi; subst k; exact argument
  | succ i => exact .bvar hi

/-- Substitution preserves typed computational conversion throughout its full rule set. -/
public theorem TermEq.subst {E Ξ Γ t u k} (valid : EnvironmentWF E)
    (h : TermEq E Ξ Γ t u k) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) : TermEq E Ξ Δ (t.subst s) (u.subst s) k :=
  term_eq_subst valid h s hs

/-- Renaming preserves typed computational conversion. -/
public theorem TermEq.rename {E Ξ Γ t u k} (valid : EnvironmentWF E)
    (h : TermEq E Ξ Γ t u k) {Δ : LocalContext} (r : Renaming)
    (hr : RenamingTyping Γ Δ r) : TermEq E Ξ Δ (t.rename r) (u.rename r) k := by
  rw [rename_as_subst, rename_as_subst]
  exact term_eq_subst valid h _ (fun i k hi => .bvar (hr i k hi))

/-- Substitution preserves predicate conversion at the same full signature. -/
public theorem PredicateEq.subst {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (h : PredicateEq E Ξ Γ P Q σ) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) : PredicateEq E Ξ Δ (P.subst s) (Q.subst s) σ :=
  predicate_eq_subst valid h s hs

/-- Renaming preserves predicate conversion without changing the result sort. -/
public theorem PredicateEq.rename {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (h : PredicateEq E Ξ Γ P Q σ) {Δ : LocalContext} (r : Renaming)
    (hr : RenamingTyping Γ Δ r) : PredicateEq E Ξ Δ (P.rename r) (Q.rename r) σ := by
  rw [predicate_rename_as_subst, predicate_rename_as_subst]
  exact predicate_eq_subst valid h _ (fun i k hi => .bvar (hr i k hi))

/-- Shifting both sides of a predicate equality preserves its full signature. -/
public theorem PredicateEq.shift {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (h : PredicateEq E Ξ Γ P Q σ) (j : Arity) :
    PredicateEq E Ξ (j :: Γ) P.shift Q.shift σ := by
  simpa only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte] using
    PredicateEq.rename valid h (fun i => i + 1) (by intro i k hi; exact hi)

/-- Local substitution preserves the validity of every kept proof hypothesis. -/
public theorem ContextWF.subst {E Ξ Γ H} (valid : EnvironmentWF E)
    (h : ContextWF E Ξ Γ H) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) : ContextWF E Ξ Δ (H.map (Predicate.subst s)) := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (predicate_subst valid head _ hs) ih

/-- Renaming preserves the validity of proof hypotheses. -/
public theorem ContextWF.rename {E Ξ Γ H} (valid : EnvironmentWF E)
    (h : ContextWF E Ξ Γ H) {Δ : LocalContext} (r : Renaming)
    (hr : RenamingTyping Γ Δ r) : ContextWF E Ξ Δ (H.map (Predicate.rename r)) := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (predicate_rename valid head _ hr) ih

/-- Local substitution preserves the typing of explicit proof data, transforming annotations,
the conclusion, and every hypothesis together. Proof-hypothesis indices are kept. -/
public theorem ProofTyping.subst {E Ξ Γ H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H p A) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) :
    ProofTyping E Ξ Δ (H.map (Predicate.subst s)) (p.subst s) (A.subst s) :=
  proof_subst valid h s hs

/-- Renaming preserves proof typing, transforming all local numerical occurrences together. -/
public theorem ProofTyping.rename {E Ξ Γ H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H p A) {Δ : LocalContext} (r : Renaming)
    (hr : RenamingTyping Γ Δ r) :
    ProofTyping E Ξ Δ (H.map (Predicate.rename r)) (p.rename r) (A.rename r) := by
  have hp : Predicate.rename r = Predicate.subst (fun i => .bvar (r i)) :=
    funext fun P => predicate_rename_as_subst P r
  rw [hp, Proof.rename]
  exact proof_subst valid h _ (fun i k hi => .bvar (hr i k hi))

/-- Exact function actual lists are preserved by local substitution. -/
public theorem FunctionArguments.subst {E Ξ Γ fs ks} (h : FunctionArguments E Ξ Γ fs ks)
    {Δ : LocalContext} (s : Subst) (hs : SubstitutionTyping E Ξ Γ Δ s) :
    FunctionArguments E Ξ Δ (fs.map (Term.subst s)) ks := arguments_subst h s hs

/-- Exact predicate actual lists preserve their declared full signatures under substitution. -/
public theorem PredicateArguments.subst {E Ξ Γ ps signatures} (valid : EnvironmentWF E)
    (h : PredicateArguments E Ξ Γ ps signatures) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) :
    PredicateArguments E Ξ Δ (ps.map (Predicate.subst s)) signatures :=
  predicates_subst valid h s hs

/-- A typed local renaming extends under a binder of any permitted arity. -/
public theorem RenamingTyping.lift {Γ Δ : LocalContext} {r : Renaming}
    (h : RenamingTyping Γ Δ r) (k : Arity) :
    RenamingTyping (k :: Γ) (k :: Δ) (Renaming.lift 1 r) := renaming_lift h k

/-- A typed local substitution extends under a binder, shifting its kept actuals. -/
public theorem SubstitutionTyping.lift {E Ξ Γ Δ s}
    (h : SubstitutionTyping E Ξ Γ Δ s) (k : Arity) :
    SubstitutionTyping E Ξ (k :: Γ) (k :: Δ) (Subst.lift 1 s) := substitution_lift h k

private theorem predicate_rename_comp (P : Predicate) (r s : Renaming) :
    (P.rename r).rename s = P.rename (fun i => s (r i)) := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ r s : Renaming,
      (ps.map (Predicate.rename r)).map (Predicate.rename s) =
        ps.map (Predicate.rename (fun i => s (r i)))) generalizing r s <;>
    simp_all [Predicate.rename, rename_comp, lift_comp, List.map_map]

/-- Instantiating a locally closed term commutes with caller-local substitution. -/
public theorem TermTyping.instantiate_subst {E Ξ t k}
    (h : TermTyping E Ξ [] t k) (fs : List Term) (s : Subst) :
    (t.instantiate fs).subst s = t.instantiate (fs.map (Term.subst s)) := by
  simpa only [subst_lift_zero] using
    Theory.instantiate_subst t 0 (term_scoped h) fs s

/-- Instantiating a locally closed term commutes with renaming the caller's actuals. -/
public theorem TermTyping.instantiate_rename {E Ξ t k}
    (h : TermTyping E Ξ [] t k) (fs : List Term) (r : Renaming) :
    (t.instantiate fs).rename r = t.instantiate (fs.map (Term.rename r)) := by
  have asRename : Term.subst (fun i => .bvar (r i)) = Term.rename r :=
    funext fun t => (rename_as_subst t r).symm
  simpa only [asRename] using h.instantiate_subst fs (fun i => .bvar (r i))

/-- Instantiating a locally closed predicate commutes with caller-local substitution. -/
public theorem PredicateTyping.instantiate_subst {E Ξ P σ}
    (h : PredicateTyping E Ξ [] P σ) (fs : List Term) (ps : List Predicate) (s : Subst) :
    (P.instantiate fs ps).subst s =
      P.instantiate (fs.map (Term.subst s)) (ps.map (Predicate.subst s)) := by
  simpa only [subst_lift_zero] using
    predicate_instantiate_subst P 0 (predicate_scoped h) fs ps s

/-- Instantiating a locally closed predicate commutes with renaming caller actuals. -/
public theorem PredicateTyping.instantiate_rename {E Ξ P σ}
    (h : PredicateTyping E Ξ [] P σ) (fs : List Term) (ps : List Predicate) (r : Renaming) :
    (P.instantiate fs ps).rename r =
      P.instantiate (fs.map (Term.rename r)) (ps.map (Predicate.rename r)) := by
  have termRename : Term.subst (fun i => .bvar (r i)) = Term.rename r :=
    funext fun t => (rename_as_subst t r).symm
  have predRename : Predicate.subst (fun i => .bvar (r i)) = Predicate.rename r :=
    funext fun P => (predicate_rename_as_subst P r).symm
  simpa only [termRename, predRename] using
    h.instantiate_subst fs ps (fun i => .bvar (r i))

end PRAProver.Core.Theory

namespace PRAProver.Core

/-- Substitution by the same variable at every index leaves a term unchanged. -/
public theorem Term.subst_id (t : Term) : t.subst Term.bvar = t := Theory.subst_id t

/-- Identity substitution leaves every predicate constructor and argument unchanged. -/
public theorem Predicate.subst_id (P : Predicate) : P.subst Term.bvar = P := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ps.map (Predicate.subst Term.bvar) = ps) <;>
    simp_all [Predicate.subst, Term.subst_id, Theory.subst_lift_bvar,
      show Term.subst Term.bvar = id from funext Term.subst_id]

/-- Removing a fresh binder from a shifted predicate returns the original predicate. -/
public theorem Predicate.subst0_shift (P : Predicate) (a : Term) : P.shift.subst0 a = P := by
  simp only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte, Predicate.subst0,
    Theory.predicate_subst_rename]
  exact Predicate.subst_id P

/-- Renaming a one-variable substitution also renames its actual, lifting under the binder. -/
public theorem Term.rename_subst0 (t a : Term) (r : Renaming) :
    (t.subst0 a).rename r = (t.rename (Renaming.lift 1 r)).subst0 (a.rename r) := by
  simp only [Term.subst0, Theory.rename_subst, Theory.subst_rename]
  congr 1
  funext i
  cases i <;> simp [Renaming.lift, Term.rename, Nat.add_comm]

/-- Renaming after a shift agrees with shifting after the original renaming. -/
public theorem Term.rename_shift (t : Term) (r : Renaming) :
    t.shift.rename (Renaming.lift 1 r) = (t.rename r).shift := by
  simp only [Term.shift, Nat.not_lt_zero, ↓reduceIte, Theory.rename_comp]
  congr 1
  funext i
  simp [Renaming.lift, Nat.add_comm]

/-- Renaming a predicate substitution lifts under its numerical binder. -/
public theorem Predicate.rename_subst0 (P : Predicate) (a : Term) (r : Renaming) :
    (P.subst0 a).rename r = (P.rename (Renaming.lift 1 r)).subst0 (a.rename r) := by
  simp only [Predicate.subst0, Theory.predicate_rename_subst, Theory.predicate_subst_rename]
  congr 1
  funext i
  cases i <;> simp [Renaming.lift, Term.rename, Nat.add_comm]

/-- Predicate shifting commutes with the corresponding lifted renaming. -/
public theorem Predicate.rename_shift (P : Predicate) (r : Renaming) :
    P.shift.rename (Renaming.lift 1 r) = (P.rename r).shift := by
  simp only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte, Theory.predicate_rename_comp]
  congr 1
  funext i
  simp [Renaming.lift, Nat.add_comm]

/-- Identity renaming leaves numerical syntax unchanged. -/
public theorem Term.rename_id (t : Term) : t.rename id = t := Theory.rename_id t

/-- Identity local renaming leaves predicate syntax unchanged. -/
public theorem Predicate.rename_id (P : Predicate) : P.rename id = P := by
  simpa only [Theory.predicate_rename_as_subst, id_eq] using Predicate.subst_id P

/-- Consecutive local renamings compose throughout predicate syntax. -/
public theorem Predicate.rename_comp (P : Predicate) (r s : Renaming) :
    (P.rename r).rename s = P.rename (fun i => s (r i)) := Theory.predicate_rename_comp P r s

/-- Inserting a numerical actual after a lifted substitution keeps the older substitutions. -/
public theorem Predicate.subst_lift_subst0 (P : Predicate) (s : Subst) (a : Term) :
    (P.subst (Subst.lift 1 s)).subst0 a = P.subst (fun | 0 => a | i + 1 => s i) := by
  simp only [Predicate.subst0, Theory.predicate_subst_comp]
  congr 1
  funext i
  cases i with
  | zero => simp [Subst.lift, Term.subst]
  | succ i =>
      change (s i).shift.subst0 a = s i
      exact Theory.subst0_shift _ _

/-- A substituted predicate binder may be renamed before its numerical actual is inserted. -/
public theorem Predicate.subst_beta_rename (P : Predicate) (s : Subst) (a : Term) (r : Renaming) :
    ((P.subst (Subst.lift 1 s)).rename (Renaming.lift 1 r)).subst0 a =
      P.subst (fun | 0 => a | i + 1 => (s i).rename r) := by
  rw [Theory.predicate_rename_subst, Theory.rename_subst_lift]
  exact Predicate.subst_lift_subst0 _ _ _

/-- Two local renamings act by composition on every numerical subexpression. -/
public theorem Term.rename_comp (t : Term) (r s : Renaming) :
    (t.rename r).rename s = t.rename (fun i => s (r i)) := Theory.rename_comp t r s

/-- Renaming after local substitution renames every supplied term. -/
public theorem Term.rename_subst (t : Term) (s : Subst) (r : Renaming) :
    (t.subst s).rename r = t.subst (fun i => (s i).rename r) := Theory.rename_subst t s r

/-- Substitution after local renaming selects the renamed variable's actual. -/
public theorem Term.subst_rename (t : Term) (r : Renaming) (s : Subst) :
    (t.rename r).subst s = t.subst (fun i => s (r i)) := Theory.subst_rename t r s

/-- Shifting an expression commutes with the corresponding lifted substitution. -/
public theorem Term.subst_shift (t : Term) (s : Subst) (n : Nat) :
    (t.shift n).subst (Subst.lift n s) = (t.subst s).shift n := Theory.subst_shift t s n

/-- Removing a fresh binder from a shifted term returns the original term. -/
public theorem Term.subst0_shift (t a : Term) : t.shift.subst0 a = t := Theory.subst0_shift t a

/-- Local substitution composes throughout numerical syntax. -/
public theorem Term.subst_comp (t : Term) (s u : Subst) :
    (t.subst s).subst u = t.subst (fun i => (s i).subst u) := Theory.subst_comp t s u

/-- Renaming after predicate substitution renames each supplied numerical term. -/
public theorem Predicate.rename_subst (P : Predicate) (s : Subst) (r : Renaming) :
    (P.subst s).rename r = P.subst (fun i => (s i).rename r) := Theory.predicate_rename_subst P s r

/-- Predicate substitution after renaming selects the renamed variable's actual. -/
public theorem Predicate.subst_rename (P : Predicate) (r : Renaming) (s : Subst) :
    (P.rename r).subst s = P.subst (fun i => s (r i)) := Theory.predicate_subst_rename P r s

/-- Predicate shifting commutes with the corresponding lifted local substitution. -/
public theorem Predicate.subst_shift (P : Predicate) (s : Subst) (n : Nat) :
    (P.shift n).subst (Subst.lift n s) = (P.subst s).shift n := Theory.predicate_subst_shift P s n

/-- Local substitutions compose throughout predicate syntax. -/
public theorem Predicate.subst_comp (P : Predicate) (s u : Subst) :
    (P.subst s).subst u = P.subst (fun i => (s i).subst u) := Theory.predicate_subst_comp P s u

/-- Substituting after one binder insertion substitutes the body and its numerical actual. -/
public theorem Term.subst0_subst (t a : Term) (s : Subst) :
    (t.subst0 a).subst s = (t.subst (Subst.lift 1 s)).subst0 (a.subst s) :=
  Theory.subst0_subst t a s

/-- Predicate binder insertion commutes with local substitution. -/
public theorem Predicate.subst0_subst (P : Predicate) (a : Term) (s : Subst) :
    (P.subst0 a).subst s = (P.subst (Subst.lift 1 s)).subst0 (a.subst s) :=
  Theory.predicate_subst0_subst P a s

/-- A lifted substitution followed by binder insertion keeps the older substitutions. -/
public theorem Term.subst_lift_subst0 (t : Term) (s : Subst) (a : Term) :
    (t.subst (Subst.lift 1 s)).subst0 a = t.subst (fun | 0 => a | i + 1 => s i) := by
  simp only [Term.subst0, Theory.subst_comp]
  congr 1
  funext i
  cases i with
  | zero => simp [Subst.lift, Term.subst]
  | succ i => exact Theory.subst0_shift _ _

/-- A substituted binder may be renamed before its numerical actual is inserted. -/
public theorem Term.subst_beta_rename (t : Term) (s : Subst) (a : Term) (r : Renaming) :
    ((t.subst (Subst.lift 1 s)).rename (Renaming.lift 1 r)).subst0 a =
      t.subst (fun | 0 => a | i + 1 => (s i).rename r) := by
  rw [Theory.rename_subst, Theory.rename_subst_lift]
  exact Term.subst_lift_subst0 _ _ _

end PRAProver.Core
