module

public import LeanPRA.Metatheory.Translation.Defs
import LeanPRA.Metatheory.Translation.Derivation
import LeanPRA.Metatheory.PRA.Basic
import Std.Data.ExtHashMap.Lemmas

/-!
# Correctness of the translation to first-order PRA

Soundness and completeness of the relational translation between the declarative core judgements
and the first-order theory of PRA:

- `termTyping_iff_translation` shows that a closed term has arity `k` if and only if it translates
  to a `Primrec k` under every function-parameter assignment.
- `predicateTyping_iff_translation` shows that a closed predicate has signature `σ` if and only if
  it translates to a `PRA.Formula σ.arity` under every parameter assignment, with quantifier-free
  signatures yielding quantifier-free formulas.
- `declarationTranslation_correct` shows that every well-formed declaration in a well-formed
  environment has a `DeclarationTranslation`; in particular, every theorem declaration translates
  to a family of formulas provable in `PRA.Proof`.

The translation eliminates function-valued let-bindings and parameterized declaration references by
source-level substitution (`subst0` and `instantiate`), which can increase syntax size. The
induction hypotheses for typing, conversion, and proof translation therefore quantify over
substitutions of local variables and declaration parameters.
-/

namespace LeanPRA.Core

open Theory

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

private theorem subst_lift_bvar (n : Nat) : Subst.lift n Term.bvar = Term.bvar := by
  funext i
  simp only [Subst.lift, Term.shift, Term.rename]
  split <;> simp_all <;> omega

private theorem subst_id (t : Term) : t.subst Term.bvar = t := by
  induction t using Term.rec
    (motive_2 := fun ts => ts.map (Term.subst Term.bvar) = ts) <;>
    simp_all [Term.subst, subst_lift_bvar]

private theorem Term.rename_id (t : Term) : t.rename id = t := LeanPRA.Core.rename_id t

private theorem Term.rename_comp (t : Term) (r s : Renaming) :
    (t.rename r).rename s = t.rename (fun i => s (r i)) := LeanPRA.Core.rename_comp t r s

private theorem Term.rename_subst (t : Term) (s : Subst) (r : Renaming) :
    (t.subst s).rename r = t.subst (fun i => (s i).rename r) := LeanPRA.Core.rename_subst t s r

private theorem Term.subst_rename (t : Term) (r : Renaming) (s : Subst) :
    (t.rename r).subst s = t.subst (fun i => s (r i)) := LeanPRA.Core.subst_rename t r s

private theorem Term.subst_shift (t : Term) (s : Subst) (n : Nat) :
    (t.shift n).subst (Subst.lift n s) = (t.subst s).shift n := LeanPRA.Core.subst_shift t s n

private theorem Term.rename_shift (t : Term) (r : Renaming) :
    t.shift.rename (Renaming.lift 1 r) = (t.rename r).shift := by
  simp only [Term.shift, Nat.not_lt_zero, ↓reduceIte, LeanPRA.Core.rename_comp]
  congr 1
  funext i
  simp [Renaming.lift, Nat.add_comm]

private theorem Term.subst_id (t : Term) : t.subst Term.bvar = t := LeanPRA.Core.subst_id t

private theorem Predicate.rename_id (P : Predicate) : P.rename id = P := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ps.map (Predicate.rename id) = ps) <;>
    simp_all [Predicate.rename, Term.rename_id, lift_id,
      show Term.rename id = id from funext Term.rename_id]

private theorem Predicate.rename_comp (P : Predicate) (r s : Renaming) :
    (P.rename r).rename s = P.rename (fun i => s (r i)) := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ r s,
      (ps.map (Predicate.rename r)).map (Predicate.rename s) =
        ps.map (Predicate.rename (fun i => s (r i)))) generalizing r s <;>
    simp_all [Predicate.rename, Term.rename_comp, lift_comp, List.map_map]

private theorem Term.subst0_shift (t a : Term) : t.shift.subst0 a = t := by
  simp only [Term.shift, Nat.not_lt_zero, ↓reduceIte, Term.subst0, subst_rename]
  exact subst_id t

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

private theorem Theory.TermTyping.subst0 {E Ξ Γ t k a j}
    (body : TermTyping E Ξ (j :: Γ) t k) (argument : TermTyping E Ξ Γ a j) :
    TermTyping E Ξ Γ (t.subst0 a) k := by
  apply term_subst body
  intro i l hi
  cases i with
  | zero => have hj : j = l := Option.some.inj hi; subst l; exact argument
  | succ i => exact .bvar hi

private theorem Theory.TermTyping.inv_bvar {E Ξ Γ i k} (h : TermTyping E Ξ Γ (.bvar i) k) :
    Γ[i]? = some k := by cases h with | bvar lookup => exact lookup

private theorem Theory.TermTyping.inv_parameter {E Ξ Γ i k}
    (h : TermTyping E Ξ Γ (.parameter i) k) :
    Ξ.functions[i]? = some k := by cases h with | parameter lookup => exact lookup

private theorem Theory.TermTyping.inv_zero {E Ξ Γ k} (h : TermTyping E Ξ Γ .zero k) : k = 0 := by
  cases h
  rfl

private theorem Theory.TermTyping.inv_succ {E Ξ Γ k} (h : TermTyping E Ξ Γ .succ k) : k = 1 := by
  cases h
  rfl

private theorem Theory.TermTyping.inv_lam {E Ξ Γ t k} (h : TermTyping E Ξ Γ (.lam binderName t) k) :
    ∃ j, k = j + 1 ∧ TermTyping E Ξ (0 :: Γ) t j := by
  cases h with | lam body => exact ⟨_, rfl, body⟩

private theorem Theory.TermTyping.inv_app {E Ξ Γ f a k} (h : TermTyping E Ξ Γ (.app f a) k) :
    TermTyping E Ξ Γ f (k + 1) ∧ TermTyping E Ξ Γ a 0 := by
  cases h with | app function argument => exact ⟨function, argument⟩

private theorem Theory.TermTyping.inv_let {E Ξ Γ a t k}
    (h : TermTyping E Ξ Γ (.letE binderName a t) k) :
    ∃ j, TermTyping E Ξ Γ a j ∧ TermTyping E Ξ (j :: Γ) t k := by
  cases h with | letE value body => exact ⟨_, value, body⟩

private theorem Theory.TermTyping.inv_primrec {E Ξ Γ b s k}
    (h : TermTyping E Ξ Γ (.primrec b s) k) :
    k = 1 ∧ TermTyping E Ξ Γ b 0 ∧ TermTyping E Ξ Γ s 2 := by
  cases h with | primrec base step => exact ⟨rfl, base, step⟩

private theorem Theory.TermTyping.inv_definition {E Ξ Γ name fs k}
    (h : TermTyping E Ξ Γ (.definition name fs) k) :
    ∃ d, E[name]? = some (.function d) ∧ FunctionArguments E Ξ Γ fs d.functions ∧ k = d.arity := by
  cases h with | definition lookup arguments => exact ⟨_, lookup, arguments, rfl⟩

private def Term.replace (s p : Subst) : Term → Term
  | .bvar i => s i
  | .parameter i => p i
  | .zero => .zero
  | .succ => .succ
  | .lam binderName t => .lam binderName (t.replace (Subst.lift 1 s) (fun i => (p i).shift))
  | .app f a => .app (f.replace s p) (a.replace s p)
  | .letE binderName a t => .letE binderName (a.replace s p)
      (t.replace (Subst.lift 1 s) (fun i => (p i).shift))
  | .primrec b f => .primrec (b.replace s p) (f.replace s p)
  | .definition name fs => .definition name (fs.map (Term.replace s p))

private theorem lift_subst (s u : Subst) :
    (fun i => (Subst.lift 1 s i).subst (Subst.lift 1 u)) =
      Subst.lift 1 (fun i => (s i).subst u) := by
  funext i
  cases i with
  | zero => simp [Subst.lift, Term.subst]
  | succ i => simp [Subst.lift, Term.subst_shift]

private theorem replace_subst (t : Term) (s p u : Subst) :
    (t.replace s p).subst u = t.replace (fun i => (s i).subst u) (fun i => (p i).subst u) := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ s p u : Subst,
      (ts.map (Term.replace s p)).map (Term.subst u) =
        ts.map (Term.replace (fun i => (s i).subst u) (fun i => (p i).subst u)))
    generalizing s p u <;>
    simp_all [Term.replace, Term.subst, Term.subst_shift, lift_subst, List.map_map]

private theorem replace_rename (t : Term) (s p : Subst) (r : Renaming) :
    (t.replace s p).rename r = t.replace (fun i => (s i).rename r) (fun i => (p i).rename r) := by
  have rename_subst : ∀ t : Term, t.rename r = t.subst (fun i => .bvar (r i)) := by
    intro t
    simpa only [Term.subst_id, Term.rename] using Term.rename_subst t Term.bvar r
  simp only [rename_subst, replace_subst]

private theorem replace_beta (t : Term) (s p : Subst) (a : Term) :
    (t.replace (Subst.lift 1 s) (fun i => (p i).shift)).subst0 a =
      t.replace (fun | 0 => a | i + 1 => s i) p := by
  simp only [Term.subst0, replace_subst]
  congr 1
  · funext i
    cases i with
    | zero => simp [Subst.lift, Term.subst]
    | succ i =>
        change (s i).shift.subst0 a = s i
        exact Term.subst0_shift _ _
  · funext i
    exact Term.subst0_shift _ _

private theorem lift_variables : Subst.lift 1 Term.bvar = Term.bvar := by
  funext i
  cases i <;> simp [Subst.lift, Term.shift, Term.rename]

private theorem replace_id (t : Term) : t.replace Term.bvar Term.parameter = t := by
  induction t using Term.rec
    (motive_2 := fun ts => ts.map (Term.replace Term.bvar Term.parameter) = ts) <;>
    simp_all [Term.replace, lift_variables, Term.shift, Term.rename,
      show (fun i => Term.parameter i) = Term.parameter from rfl]

private theorem shift_add (t : Term) (n m : Nat) : (t.shift n).shift m = t.shift (n + m) := by
  simp only [Term.shift, Nat.not_lt_zero, ↓reduceIte, Term.rename_comp]
  congr 1
  funext i
  omega

private theorem replace_instantiate {E Ξ Γ t k} (h : Theory.TermTyping E Ξ Γ t k)
    (fs : List Term) (s p : Subst)
    (locals : ∀ i j, Γ[i]? = some j → s i = .bvar i)
    (parameters : ∀ i j, Ξ.functions[i]? = some j →
      p i = (fs[i]?.getD (.parameter i)).shift Γ.length) :
    t.replace s p = t.instantiate fs Γ.length := by
  induction h using Theory.TermTyping.rec
    (motive_2 := fun Γ ts _ _ => ∀ s p : Subst,
      (∀ i j, Γ[i]? = some j → s i = .bvar i) →
      (∀ i j, Ξ.functions[i]? = some j →
        p i = (fs[i]?.getD (.parameter i)).shift Γ.length) →
      ts.map (Term.replace s p) = ts.map (Term.instantiate fs Γ.length))
    generalizing s p with
  | bvar lookup => simp only [Term.replace, Term.instantiate]; exact locals _ _ lookup
  | parameter lookup => simp only [Term.replace, Term.instantiate]; exact parameters _ _ lookup
  | zero => simp only [Term.replace, Term.instantiate]
  | succ => simp only [Term.replace, Term.instantiate]
  | lam body ih =>
      simp only [Term.replace, Term.instantiate]
      congr 1
      apply ih
      · intro i j hi
        cases i with
        | zero => simp [Subst.lift]
        | succ i => simp [Subst.lift, locals i j hi, Term.shift, Term.rename]
      · intro i j hi
        simp only [parameters i j hi, shift_add, List.length_cons]
  | app f a ihf iha => simp only [Term.replace, Term.instantiate]; rw [ihf _ _ locals parameters,
      iha _ _ locals parameters]
  | letE a body iha ihb =>
      simp only [Term.replace, Term.instantiate]
      rw [iha _ _ locals parameters]
      congr 1
      apply ihb
      · intro i j hi
        cases i with
        | zero => simp [Subst.lift]
        | succ i => simp [Subst.lift, locals i j hi, Term.shift, Term.rename]
      · intro i j hi
        simp only [parameters i j hi, shift_add, List.length_cons]
  | primrec b f ihb ihf =>
      simp only [Term.replace, Term.instantiate]
      rw [ihb _ _ locals parameters, ihf _ _ locals parameters]
  | definition lookup args ih =>
      simp only [Term.replace, Term.instantiate]
      rw [ih _ _ locals parameters]
  | nil => rfl
  | cons head tail ihh iht =>
      rename_i s p locals parameters
      simp only [List.map_cons]
      rw [ihh _ _ locals parameters, iht _ _ locals parameters]

private theorem Theory.TermTyping.replace_instantiate_at {E Ξ Γ t k}
    (h : Theory.TermTyping E Ξ Γ t k) (fs : List Term) (s p : Subst)
    (locals : ∀ i j, Γ[i]? = some j → s i = .bvar i)
    (parameters : ∀ i j, Ξ.functions[i]? = some j →
      p i = (fs[i]?.getD (.parameter i)).shift Γ.length) :
    t.replace s p = t.instantiate fs Γ.length :=
  LeanPRA.Core.replace_instantiate h fs s p locals parameters

private theorem Theory.TermTyping.replace_instantiate {E Ξ t k}
    (h : Theory.TermTyping E Ξ [] t k) (fs : List Term)
    (p : Subst) (parameters : ∀ i j, Ξ.functions[i]? = some j →
      p i = fs[i]?.getD (.parameter i)) : t.replace Term.bvar p = t.instantiate fs := by
  apply LeanPRA.Core.replace_instantiate h fs Term.bvar p (by intros; rfl)
  intro i j hi
  simpa only [List.length_nil, Term.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
    show (fun i : Nat => i) = id from rfl, Term.rename_id] using parameters i j hi

private theorem Term.replace_subst (t : Term) (s p u : Subst) :
    (t.replace s p).subst u = t.replace (fun i => (s i).subst u) (fun i => (p i).subst u) :=
  LeanPRA.Core.replace_subst t s p u

private theorem Term.replace_rename (t : Term) (s p : Subst) (r : Renaming) :
    (t.replace s p).rename r = t.replace (fun i => (s i).rename r) (fun i => (p i).rename r) :=
  LeanPRA.Core.replace_rename t s p r

private theorem Term.replace_beta (t : Term) (s p : Subst) (a : Term) :
    (t.replace (Subst.lift 1 s) (fun i => (p i).shift)).subst0 a =
      t.replace (fun | 0 => a | i + 1 => s i) p := LeanPRA.Core.replace_beta t s p a

private theorem Term.replace_id (t : Term) : t.replace Term.bvar Term.parameter = t :=
  LeanPRA.Core.replace_id t

private def Predicate.replace (s p : Subst) (q : Nat → Predicate) : Predicate → Predicate
  | .false => .false
  | .true => .true
  | .equal a b => .equal (a.replace s p) (b.replace s p)
  | .imp A B => .imp (A.replace s p q) (B.replace s p q)
  | .and A B => .and (A.replace s p q) (B.replace s p q)
  | .or A B => .or (A.replace s p q) (B.replace s p q)
  | .all P => .all (P.replace s p q)
  | .ex P => .ex (P.replace s p q)
  | .parameter i => q i
  | .lam binderName P =>
      .lam binderName (P.replace (Subst.lift 1 s) (fun i => (p i).shift) (fun i => (q i).shift))
  | .app P a => .app (P.replace s p q) (a.replace s p)
  | .letTerm binderName a P => .letTerm binderName (a.replace s p) (P.replace s p q)
  | .letPredicate binderName Q P => .letPredicate binderName (Q.replace s p q) (P.replace s p q)
  | .definition name fs ps => .definition name (fs.map (Term.replace s p))
      (ps.map (Predicate.replace s p q))

private theorem predicate_lift_rename (s : Subst) (r : Renaming) :
    (fun i => (Subst.lift 1 s i).rename (Renaming.lift 1 r)) =
      Subst.lift 1 (fun i => (s i).rename r) := by
  funext i
  cases i <;> simp [Subst.lift, Renaming.lift, Term.rename, Term.rename_shift]

private theorem Predicate.replace_rename (P : Predicate) (s p : Subst) (q : Nat → Predicate)
    (r : Renaming) : (P.replace s p q).rename r = P.replace (fun i => (s i).rename r)
      (fun i => (p i).rename r) (fun i => (q i).rename r) := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ s p q r,
      (ps.map (Predicate.replace s p q)).map (Predicate.rename r) =
        ps.map (Predicate.replace (fun i => (s i).rename r)
          (fun i => (p i).rename r) (fun i => (q i).rename r)))
    generalizing s p q r <;>
    simp_all [Predicate.replace, Predicate.rename, Term.replace_rename, predicate_lift_rename,
      Term.rename_shift, List.map_map]
  congr 1
  funext i
  simp only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte, Predicate.rename_comp]
  congr 1
  funext j
  simp [Renaming.lift, Nat.add_comm]

private theorem predicate_replace_id (P : Predicate) :
    P.replace Term.bvar Term.parameter Predicate.parameter = P := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ps.map
      (Predicate.replace Term.bvar Term.parameter Predicate.parameter) = ps) <;>
    simp_all [Predicate.replace, Term.replace_id, lift_variables, Term.shift,
      Predicate.shift, Term.rename, Predicate.rename,
      show (fun i => Term.parameter i) = Term.parameter from rfl,
      show (fun i => Predicate.parameter i) = Predicate.parameter from rfl]
  rw [show Term.replace Term.bvar Term.parameter = id from funext Term.replace_id]
  exact List.map_id _

private theorem pshift_add (P : Predicate) (n m : Nat) :
    (P.shift n).shift m = P.shift (n + m) := by
  simp only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte, Predicate.rename_comp]
  congr 1
  funext i
  omega

private theorem function_replace_instantiate {E Ξ Γ fs ks}
    (h : Theory.FunctionArguments E Ξ Γ fs ks) (actuals : List Term) (s p : Subst)
    (locals : ∀ i j, Γ[i]? = some j → s i = .bvar i)
    (parameters : ∀ i j, Ξ.functions[i]? = some j →
      p i = (actuals[i]?.getD (.parameter i)).shift Γ.length) :
    fs.map (Term.replace s p) = fs.map (Term.instantiate actuals Γ.length) := by
  induction h using Theory.FunctionArguments.rec (motive_1 := fun _ _ _ _ => True) with
  | nil => rfl
  | cons head tail ihh ih =>
      simp only [List.map_cons]
      rw [head.replace_instantiate_at actuals s p locals parameters, ih locals parameters]
  | _ => trivial

private theorem predicate_replace_instantiate {E Ξ Γ P σ} (h : Theory.PredicateTyping E Ξ Γ P σ)
    (fs : List Term) (ps : List Predicate) (s p : Subst) (q : Nat → Predicate)
    (locals : ∀ i j, Γ[i]? = some j → s i = .bvar i)
    (functions : ∀ i j, Ξ.functions[i]? = some j →
      p i = (fs[i]?.getD (.parameter i)).shift Γ.length)
    (predicates : ∀ i j, Ξ.predicates[i]? = some j →
      q i = (ps[i]?.getD (.parameter i)).shift Γ.length) :
    P.replace s p q = P.instantiate fs ps Γ.length := by
  induction h using Theory.PredicateTyping.rec
    (motive_2 := fun Γ ts _ _ => ∀ s p q,
      (∀ i j, Γ[i]? = some j → s i = .bvar i) →
      (∀ i j, Ξ.functions[i]? = some j →
        p i = (fs[i]?.getD (.parameter i)).shift Γ.length) →
      (∀ i j, Ξ.predicates[i]? = some j →
        q i = (ps[i]?.getD (.parameter i)).shift Γ.length) →
      ts.map (Predicate.replace s p q) = ts.map (Predicate.instantiate fs ps Γ.length))
    generalizing s p q with
  | false => simp only [Predicate.replace, Predicate.instantiate]
  | true => simp only [Predicate.replace, Predicate.instantiate]
  | equal a b =>
      simp only [Predicate.replace, Predicate.instantiate]
      rw [a.replace_instantiate_at fs s p locals functions,
        b.replace_instantiate_at fs s p locals functions]
  | imp a b iha ihb =>
      simp only [Predicate.replace, Predicate.instantiate]
      rw [iha _ _ _ locals functions predicates, ihb _ _ _ locals functions predicates]
  | and a b iha ihb =>
      simp only [Predicate.replace, Predicate.instantiate]
      rw [iha _ _ _ locals functions predicates, ihb _ _ _ locals functions predicates]
  | or a b iha ihb =>
      simp only [Predicate.replace, Predicate.instantiate]
      rw [iha _ _ _ locals functions predicates, ihb _ _ _ locals functions predicates]
  | all body ih =>
      simp only [Predicate.replace, Predicate.instantiate]
      rw [ih _ _ _ locals functions predicates]
  | ex body ih =>
      simp only [Predicate.replace, Predicate.instantiate]
      rw [ih _ _ _ locals functions predicates]
  | parameter lookup =>
      simp only [Predicate.replace, Predicate.instantiate]
      exact predicates _ _ lookup
  | lam body ih =>
      simp only [Predicate.replace, Predicate.instantiate]
      congr 1
      apply ih
      · intro i j hi
        cases i with
        | zero => simp [Subst.lift]
        | succ i => simp [Subst.lift, locals i j hi, Term.shift, Term.rename]
      · intro i j hi
        simp only [functions i j hi, List.length_cons]
        simp [Term.shift, Term.rename_comp, Nat.add_assoc]
      · intro i j hi
        simp only [predicates i j hi, pshift_add, List.length_cons]
  | app function argument ih =>
      simp only [Predicate.replace, Predicate.instantiate]
      rw [ih _ _ _ locals functions predicates,
        argument.replace_instantiate_at fs s p locals functions]
  | letTerm a P ih =>
      simp only [Predicate.replace, Predicate.instantiate]
      rw [a.replace_instantiate_at fs s p locals functions, ih _ _ _ locals functions predicates]
  | letPredicate Q P ihQ ihP =>
      simp only [Predicate.replace, Predicate.instantiate]
      rw [ihQ _ _ _ locals functions predicates, ihP _ _ _ locals functions predicates]
  | definition lookup args preds ihp =>
      simp only [Predicate.replace, Predicate.instantiate]
      rw [function_replace_instantiate args fs s p locals functions,
        ihp _ _ _ locals functions predicates]
  | subsumption typing sub ih => exact ih _ _ _ locals functions predicates
  | nil => rfl
  | cons head tail ihh iht =>
      rename_i s p q locals functions predicates
      simp only [List.map_cons]
      rw [ihh _ _ _ locals functions predicates, iht _ _ _ locals functions predicates]

private theorem Theory.PredicateTyping.replace_instantiate {E Ξ P σ}
    (h : Theory.PredicateTyping E Ξ [] P σ) (fs : List Term) (ps : List Predicate)
    (p : Subst) (q : Nat → Predicate)
    (functions : ∀ i j, Ξ.functions[i]? = some j → p i = fs[i]?.getD (.parameter i))
    (predicates : ∀ i j, Ξ.predicates[i]? = some j → q i = ps[i]?.getD (.parameter i)) :
    P.replace Term.bvar p q = P.instantiate fs ps := by
  apply LeanPRA.Core.predicate_replace_instantiate h fs ps Term.bvar p q (by intros; rfl)
  · intro i j hi
    simpa only [List.length_nil, Term.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
      show (fun i : Nat => i) = id from rfl, Term.rename_id] using functions i j hi
  · intro i j hi
    simpa only [List.length_nil, Predicate.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
      show (fun i : Nat => i) = id from rfl, Predicate.rename_id] using predicates i j hi

private theorem Predicate.replace_id (P : Predicate) :
    P.replace Term.bvar Term.parameter Predicate.parameter = P :=
  LeanPRA.Core.predicate_replace_id P

private theorem Theory.TermTyping.unique {E Ξ Γ t k j} (left : TermTyping E Ξ Γ t k)
    (right : TermTyping E Ξ Γ t j) : k = j := by
  induction left using TermTyping.rec (motive_2 := fun _ _ _ _ => True) generalizing j with
  | bvar lookup => exact Option.some.inj (lookup.symm.trans right.inv_bvar)
  | parameter lookup => exact Option.some.inj (lookup.symm.trans right.inv_parameter)
  | zero => exact right.inv_zero.symm
  | succ => exact right.inv_succ.symm
  | lam body ih =>
      obtain ⟨j, rfl, body⟩ := right.inv_lam
      exact congrArg (· + 1) (ih body)
  | app function argument ihf iha => exact Nat.add_right_cancel (ihf right.inv_app.1)
  | letE value body ihv ihb =>
      obtain ⟨j, hv, hb⟩ := right.inv_let
      cases ihv hv
      exact ihb hb
  | primrec => exact right.inv_primrec.1.symm
  | definition lookup arguments ih =>
      obtain ⟨d, hd, _, rfl⟩ := right.inv_definition
      cases Declaration.function.inj (Option.some.inj (lookup.symm.trans hd))
      rfl
  | nil | cons => trivial

private theorem Theory.EnvironmentExtends.insert {E : Environment} {d : Declaration}
    (fresh : E[d.name]? = none) : EnvironmentExtends E (E.insert d.name d) := by
  intro name e lookup
  by_cases heq : d.name = name
  · subst name
    rw [fresh] at lookup
    contradiction
  · simpa [Std.ExtHashMap.getElem?_insert, heq] using lookup

private theorem Theory.TermTyping.instantiate_rename {E Ξ t k}
    (typed : TermTyping E Ξ [] t k) (fs : List Term) (r : Renaming) :
    (t.instantiate fs).rename r = t.instantiate (fs.map (Term.rename r)) := by
  rw [← typed.replace_instantiate fs _ (by intros; rfl), Term.replace_rename]
  apply typed.replace_instantiate_at
  · intro i j h
    simp at h
  · intro i j hi
    simp only [List.length_nil, Term.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
      show (fun i : Nat => i) = id from rfl, Term.rename_id, List.getElem?_map]
    cases fs[i]? <;> simp [Term.rename]

private theorem Theory.PredicateTyping.instantiate_rename {E Ξ P σ}
    (typed : PredicateTyping E Ξ [] P σ) (fs : List Term) (ps : List Predicate) (r : Renaming) :
    (P.instantiate fs ps).rename r =
      P.instantiate (fs.map (Term.rename r)) (ps.map (Predicate.rename r)) := by
  rw [← typed.replace_instantiate fs ps _ _ (by intros; rfl) (by intros; rfl),
    Predicate.replace_rename]
  apply predicate_replace_instantiate typed
  · intro i j h
    simp at h
  · intro i j hi
    simp only [List.length_nil, Term.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
      show (fun i : Nat => i) = id from rfl, Term.rename_id, List.getElem?_map]
    cases fs[i]? <;> simp [Term.rename]
  · intro i j hi
    simp only [List.length_nil, Predicate.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
      show (fun i : Nat => i) = id from rfl, Predicate.rename_id, List.getElem?_map]
    cases ps[i]? <;> simp [Predicate.rename]

private theorem Term.subst_subst (t : Term) (s u : Subst) :
    (t.subst s).subst u = t.subst (fun i => (s i).subst u) := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ s u,
      (ts.map (Term.subst s)).map (Term.subst u) =
        ts.map (Term.subst (fun i => (s i).subst u))) generalizing s u <;>
    simp_all [Term.subst, lift_subst, List.map_map]

private theorem Term.subst_subst0 (t a : Term) (s : Subst) :
    (t.subst0 a).subst s = (t.subst (Subst.lift 1 s)).subst0 (a.subst s) := by
  simp only [Term.subst0, Term.subst_subst]
  congr 1
  funext i
  cases i with
  | zero => simp [Subst.lift, Term.subst]
  | succ i =>
      simp only [Term.subst]
      simpa only [Term.subst0, Subst.lift, Nat.add_sub_cancel, Nat.not_lt_zero, ↓reduceIte,
        show ¬i + 1 < 1 by omega] using (Term.subst0_shift (s i) (a.subst s)).symm

private theorem Predicate.subst_rename (P : Predicate) (r : Renaming) (s : Subst) :
    (P.rename r).subst s = P.subst (fun i => s (r i)) := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ r s,
      (ps.map (Predicate.rename r)).map (Predicate.subst s) =
        ps.map (Predicate.subst (fun i => s (r i)))) generalizing r s <;>
    simp_all [Predicate.rename, Predicate.subst, Term.subst_rename, subst_lift_rename,
      List.map_map]

private theorem Predicate.rename_subst (P : Predicate) (s : Subst) (r : Renaming) :
    (P.subst s).rename r = P.subst (fun i => (s i).rename r) := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ s r,
      (ps.map (Predicate.subst s)).map (Predicate.rename r) =
        ps.map (Predicate.subst (fun i => (s i).rename r))) generalizing s r <;>
    simp_all [Predicate.rename, Predicate.subst, Term.rename_subst, rename_subst_lift,
      List.map_map]

private theorem Predicate.subst_shift (P : Predicate) (s : Subst) :
    P.shift.subst (Subst.lift 1 s) = (P.subst s).shift := by
  simp only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte, Predicate.subst_rename,
    Predicate.rename_subst]
  congr 1

private theorem Predicate.replace_subst (P : Predicate) (s p : Subst)
    (q : Nat → Predicate) (u : Subst) :
    (P.replace s p q).subst u = P.replace (fun i => (s i).subst u)
      (fun i => (p i).subst u) (fun i => (q i).subst u) := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ s p q u,
      (ps.map (Predicate.replace s p q)).map (Predicate.subst u) =
        ps.map (Predicate.replace (fun i => (s i).subst u)
          (fun i => (p i).subst u) (fun i => (q i).subst u)))
    generalizing s p q u <;>
    simp_all [Predicate.replace, Predicate.subst, Term.replace_subst, lift_subst,
      Term.subst_shift, Predicate.subst_shift, List.map_map]

private theorem Theory.TermTyping.instantiate_subst {E Ξ t k}
    (typed : TermTyping E Ξ [] t k) (fs : List Term) (s : Subst) :
    (t.instantiate fs).subst s = t.instantiate (fs.map (Term.subst s)) := by
  rw [← typed.replace_instantiate fs _ (by intros; rfl), Term.replace_subst]
  apply typed.replace_instantiate_at
  · intro i j h
    simp at h
  · intro i j hi
    simp only [List.length_nil, Term.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
      show (fun i : Nat => i) = id from rfl, Term.rename_id, List.getElem?_map]
    cases fs[i]? <;> simp [Term.subst]

private theorem Theory.PredicateTyping.instantiate_subst {E Ξ P σ}
    (typed : PredicateTyping E Ξ [] P σ) (fs : List Term) (ps : List Predicate) (s : Subst) :
    (P.instantiate fs ps).subst s =
      P.instantiate (fs.map (Term.subst s)) (ps.map (Predicate.subst s)) := by
  rw [← typed.replace_instantiate fs ps _ _ (by intros; rfl) (by intros; rfl),
    Predicate.replace_subst]
  apply predicate_replace_instantiate typed
  · intro i j h
    simp at h
  · intro i j hi
    simp only [List.length_nil, Term.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
      show (fun i : Nat => i) = id from rfl, Term.rename_id, List.getElem?_map]
    cases fs[i]? <;> simp [Term.subst]
  · intro i j hi
    simp only [List.length_nil, Predicate.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
      show (fun i : Nat => i) = id from rfl, Predicate.rename_id, List.getElem?_map]
    cases ps[i]? <;> simp [Predicate.subst]

private theorem lift_replace_rename (s : Subst) (r : Renaming) :
    (fun i => Subst.lift 1 s (Renaming.lift 1 r i)) =
      Subst.lift 1 (fun i => s (r i)) := by
  funext i
  cases i <;> simp [Subst.lift, Renaming.lift, Nat.add_comm]

private theorem Term.rename_replace (t : Term) (r : Renaming) (s p : Subst) :
    (t.rename r).replace s p = t.replace (fun i => s (r i)) p := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ r s p,
      (ts.map (Term.rename r)).map (Term.replace s p) =
        ts.map (Term.replace (fun i => s (r i)) p)) generalizing r s p <;>
    simp_all [Term.rename, Term.replace, lift_replace_rename, List.map_map]

private theorem Term.shift_replace (t : Term) (s p : Subst) :
    t.shift.replace (Subst.lift 1 s) (fun i => (p i).shift) = (t.replace s p).shift := by
  simp only [Term.shift, Nat.not_lt_zero, ↓reduceIte, Term.rename_replace, Term.replace_rename]
  congr 1

private theorem lift_replace (s u p : Subst) :
    (fun i => (Subst.lift 1 u i).replace (Subst.lift 1 s) (fun j => (p j).shift)) =
      Subst.lift 1 (fun i => (u i).replace s p) := by
  funext i
  cases i <;> simp [Subst.lift, Term.replace, Term.shift_replace]

private theorem Term.subst_replace (t : Term) (u s p : Subst) :
    (t.subst u).replace s p = t.replace (fun i => (u i).replace s p) p := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ u s p,
      (ts.map (Term.subst u)).map (Term.replace s p) =
        ts.map (Term.replace (fun i => (u i).replace s p) p)) generalizing u s p <;>
    simp_all [Term.subst, Term.replace, lift_replace, List.map_map]

private theorem Term.subst0_replace (t a : Term) (s p : Subst) :
    (t.subst0 a).replace s p =
      t.replace (fun | 0 => a.replace s p | i + 1 => s i) p := by
  rw [Term.subst0, Term.subst_replace]
  congr 1
  funext i
  cases i <;> simp only [Term.replace]

private theorem Term.replace_replace (t : Term) (s p u v : Subst) :
    (t.replace s p).replace u v = t.replace (fun i => (s i).replace u v)
      (fun i => (p i).replace u v) := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ s p u v,
      (ts.map (Term.replace s p)).map (Term.replace u v) =
        ts.map (Term.replace (fun i => (s i).replace u v)
          (fun i => (p i).replace u v))) generalizing s p u v <;>
    simp_all [Term.replace, lift_replace, Term.shift_replace, List.map_map]

private theorem Predicate.rename_replace (P : Predicate) (r : Renaming)
    (s p : Subst) (q : Nat → Predicate) :
    (P.rename r).replace s p q = P.replace (fun i => s (r i)) p q := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ r s p q,
      (ps.map (Predicate.rename r)).map (Predicate.replace s p q) =
        ps.map (Predicate.replace (fun i => s (r i)) p q)) generalizing r s p q <;>
    simp_all [Predicate.rename, Predicate.replace, Term.rename_replace, lift_replace_rename,
      List.map_map]

private theorem Predicate.shift_replace (P : Predicate) (s p : Subst) (q : Nat → Predicate) :
    P.shift.replace (Subst.lift 1 s) (fun i => (p i).shift) (fun i => (q i).shift) =
      (P.replace s p q).shift := by
  simp only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte, Predicate.rename_replace,
    Predicate.replace_rename]
  congr 1

private theorem Predicate.subst_replace (P : Predicate) (u s p : Subst) (q : Nat → Predicate) :
    (P.subst u).replace s p q = P.replace (fun i => (u i).replace s p) p q := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ u s p q,
      (ps.map (Predicate.subst u)).map (Predicate.replace s p q) =
        ps.map (Predicate.replace (fun i => (u i).replace s p) p q)) generalizing u s p q <;>
    simp_all [Predicate.subst, Predicate.replace, Term.subst_replace, lift_replace, List.map_map]

private theorem Predicate.replace_replace (P : Predicate) (s p u v : Subst)
    (q w : Nat → Predicate) :
    (P.replace s p q).replace u v w = P.replace (fun i => (s i).replace u v)
      (fun i => (p i).replace u v) (fun i => (q i).replace u v w) := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ s p u v q w,
      (ps.map (Predicate.replace s p q)).map (Predicate.replace u v w) =
        ps.map (Predicate.replace (fun i => (s i).replace u v)
          (fun i => (p i).replace u v) (fun i => (q i).replace u v w)))
    generalizing s p u v q w <;>
    simp_all [Predicate.replace, Term.replace_replace, lift_replace, Term.shift_replace,
      Predicate.shift_replace, List.map_map]

private theorem Theory.FunctionArguments.length_eq {E Ξ Γ fs ks}
    (h : FunctionArguments E Ξ Γ fs ks) : fs.length = ks.length := by
  induction h using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => rfl
  case cons head tail _ ih => simp only [List.length_cons, ih]
  all_goals trivial

private theorem Theory.TermTyping.instantiate_replace {E Ξ t k}
    (typed : TermTyping E Ξ [] t k) (fs : List Term) (len : fs.length = Ξ.functions.length)
    (s p : Subst) : (t.instantiate fs).replace s p =
      t.instantiate (fs.map (Term.replace s p)) := by
  rw [← typed.replace_instantiate fs _ (by intros; rfl), Term.replace_replace]
  apply typed.replace_instantiate_at
  · intro i j h
    simp at h
  · intro i j hi
    have bound : i < fs.length := by
      rw [len]
      by_cases bound : i < Ξ.functions.length
      · exact bound
      · rw [List.getElem?_eq_none (show Ξ.functions.length ≤ i by omega)] at hi
        cases hi
    have some := List.getElem?_eq_getElem bound
    simp only [some, Option.getD_some, List.getElem?_map, List.length_nil, Term.shift,
      Nat.not_lt_zero, ↓reduceIte, Nat.add_zero, show (fun i : Nat => i) = id from rfl,
      Term.rename_id, Option.map_some]

private theorem Predicate.subst_id (P : Predicate) : P.subst Term.bvar = P := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ps.map (Predicate.subst Term.bvar) = ps) <;>
    simp_all [Predicate.subst, Term.subst_id, subst_lift_bvar,
      show Term.subst Term.bvar = id from funext Term.subst_id]

private theorem Predicate.subst0_shift (P : Predicate) (a : Term) : P.shift.subst0 a = P := by
  simpa only [Predicate.shift, Predicate.subst0, Predicate.subst_rename, Nat.not_lt_zero,
    ↓reduceIte] using Predicate.subst_id P

private theorem Predicate.replace_beta (P : Predicate) (s p : Subst) (q : Nat → Predicate)
    (a : Term) :
    (P.replace (Subst.lift 1 s) (fun i => (p i).shift) (fun i => (q i).shift)).subst0 a =
      P.replace (fun | 0 => a | i + 1 => s i) p q := by
  simp only [Predicate.subst0, Predicate.replace_subst]
  congr 1
  · funext i
    cases i with
    | zero => simp [Subst.lift, Term.subst]
    | succ i => exact Term.subst0_shift _ _
  · funext i
    exact Term.subst0_shift _ _
  · funext i
    exact Predicate.subst0_shift _ _

private theorem Predicate.subst0_replace (P : Predicate) (a : Term) (s p : Subst)
    (q : Nat → Predicate) : (P.subst0 a).replace s p q =
      P.replace (fun | 0 => a.replace s p | i + 1 => s i) p q := by
  rw [Predicate.subst0, Predicate.subst_replace]
  congr 1
  funext i
  cases i <;> simp only [Term.replace]

private theorem Theory.PredicateArguments.length_eq {E Ξ Γ ps signatures}
    (h : PredicateArguments E Ξ Γ ps signatures) : ps.length = signatures.length := by
  induction h using PredicateArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => rfl
  case cons head tail _ ih => simp only [List.length_cons, ih]
  all_goals trivial

private theorem Theory.PredicateTyping.instantiate_replace {E Ξ P σ}
    (typed : PredicateTyping E Ξ [] P σ) (fs : List Term) (ps : List Predicate)
    (flen : fs.length = Ξ.functions.length) (plen : ps.length = Ξ.predicates.length)
    (s p : Subst) (q : Nat → Predicate) : (P.instantiate fs ps).replace s p q =
      P.instantiate (fs.map (Term.replace s p)) (ps.map (Predicate.replace s p q)) := by
  rw [← typed.replace_instantiate fs ps _ _ (by intros; rfl) (by intros; rfl),
    Predicate.replace_replace]
  apply predicate_replace_instantiate typed
  · intro i j h
    simp at h
  · intro i j hi
    have bound : i < fs.length := by
      rw [flen]
      by_cases bound : i < Ξ.functions.length
      · exact bound
      · rw [List.getElem?_eq_none (show Ξ.functions.length ≤ i by omega)] at hi
        cases hi
    simp only [List.getElem?_eq_getElem bound, Option.getD_some, List.getElem?_map,
      List.length_nil, Term.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
      show (fun i : Nat => i) = id from rfl, Term.rename_id, Option.map_some]
  · intro i σ hi
    have bound : i < ps.length := by
      rw [plen]
      by_cases bound : i < Ξ.predicates.length
      · exact bound
      · rw [List.getElem?_eq_none (show Ξ.predicates.length ≤ i by omega)] at hi
        cases hi
    simp only [List.getElem?_eq_getElem bound, Option.getD_some, List.getElem?_map,
      List.length_nil, Predicate.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
      show (fun i : Nat => i) = id from rfl, Predicate.rename_id, Option.map_some]

end LeanPRA.Core

namespace LeanPRA.Translation

open Core Core.Theory

private theorem term_translation_bvar {E Ξ ρ n t k f i}
    (h : TermTranslation E Ξ ρ n t k f) (ht : t = .bvar i) :
    ∃ j : Fin n, j.val = i ∧ HEq f (.proj (j.natAdd 0) : Primrec (0 + n)) := by
  cases h <;> cases ht
  exact ⟨_, rfl, HEq.rfl⟩

private theorem term_translation_definition {E Ξ ρ n t k f name fs}
    (h : TermTranslation E Ξ ρ n t k f) (ht : t = .definition name fs) :
    ∃ d : FunctionDefinition, E[name]? = some (.function d) ∧
      ∃ g : Primrec (d.arity + n),
        TermTranslation E Ξ ρ n (d.body.instantiate fs) d.arity g ∧ HEq f g := by
  cases h <;> cases ht
  exact ⟨_, by assumption, _, by assumption, HEq.rfl⟩

private theorem predicate_translation_parameter {E Ξ ρ π n P σ A i}
    (h : PredicateTranslation E Ξ ρ π n P σ A) (hP : P = .parameter i) :
    ∃ τ, ∃ lookup : Ξ.predicates[i]? = some τ,
      HEq A ((π i τ lookup).val.subst (fun j => .var (Fin.embedLeft (n := n) j))) := by
  cases h <;> cases hP
  exact ⟨_, by assumption, HEq.rfl⟩

private theorem predicate_translation_definition {E Ξ ρ π n P σ A name fs ps}
    (h : PredicateTranslation E Ξ ρ π n P σ A) (hP : P = .definition name fs ps) :
    ∃ d : PredicateDefinition, E[name]? = some (.predicate d) ∧
      ∃ B : PRA.Formula (d.signature.arity + n),
        PredicateTranslation E Ξ ρ π n (d.body.instantiate fs ps) d.signature B ∧ HEq A B := by
  cases h <;> cases hP
  exact ⟨_, by assumption, _, by assumption, HEq.rfl⟩

private theorem term_translation_unique {E Ξ ρ n t k f}
    (h : TermTranslation E Ξ ρ n t k f) {g} (other : TermTranslation E Ξ ρ n t k g) : f = g := by
  induction h using TermTranslation.rec (motive_2 := fun _ _ _ _ => True) with
  | bvar i =>
      obtain ⟨j, hj, hg⟩ := term_translation_bvar other rfl
      have eq : j = i := Fin.ext hj
      subst j
      exact (eq_of_heq hg).symm
  | zero => cases other; rfl
  | succ => cases other; rfl
  | parameter lookup => cases other; rfl
  | lam body ih =>
      cases other with
      | lam body' => rw [ih body']
  | app function argument ihf iha =>
      cases other with
      | app function' argument' => rw [ihf function', iha argument']
  | letE value body ihv ihb =>
      cases other with
      | letE value' body' => exact ihb body'
  | primrec base step ihb ihs =>
      cases other with
      | primrec base' step' => rw [ihb base', ihs step']
  | definition lookup arguments body iha ihb =>
      obtain ⟨d, hd, g, body', heq⟩ := term_translation_definition other rfl
      cases Declaration.function.inj (Option.some.inj (lookup.symm.trans hd))
      exact (ihb body').trans (eq_of_heq heq).symm
  | nil | cons => trivial

private theorem predicate_translation_unique {E Ξ ρ π n P σ A}
    (h : PredicateTranslation E Ξ ρ π n P σ A) {B}
    (other : PredicateTranslation E Ξ ρ π n P σ B) : A = B := by
  induction h using PredicateTranslation.rec (motive_2 := fun _ _ _ _ => True) with
  | false => cases other; rfl
  | true => cases other; rfl
  | equal left right =>
      cases other with
      | equal left' right' =>
          rw [term_translation_unique left left', term_translation_unique right right']
  | imp left right ihP ihQ =>
      cases other with
      | imp left' right' => rw [ihP left', ihQ right']
  | and left right ihP ihQ =>
      cases other with
      | and left' right' => rw [ihP left', ihQ right']
  | or left right ihP ihQ =>
      cases other with
      | or left' right' => rw [ihP left', ihQ right']
  | all body ih =>
      cases other with
      | all body' => rw [ih body']
  | ex body ih =>
      cases other with
      | ex body' => rw [ih body']
  | parameter lookup sort =>
      obtain ⟨τ, ht, heq⟩ := predicate_translation_parameter other rfl
      cases Option.some.inj (lookup.symm.trans ht)
      exact (eq_of_heq heq).symm
  | lam body ih =>
      cases other with
      | lam body' => rw [ih body']
  | app function argument ih =>
      cases other with
      | app function' argument' => rw [ih function', term_translation_unique argument argument']
  | letTerm value body ih =>
      cases other with
      | letTerm value' body' => exact ih body'
  | letPredicate value body ihv ihb =>
      cases other with
      | letPredicate value' body' => exact ihb body'
  | definition lookup functions predicates body sort ihp ihb =>
      obtain ⟨d, hd, B, body', heq⟩ := predicate_translation_definition other rfl
      cases Declaration.predicate.inj (Option.some.inj (lookup.symm.trans hd))
      exact (ihb body').trans (eq_of_heq heq).symm
  | nil | cons => trivial

private def CodeEq {n} (f g : Primrec n) : Prop :=
  PRA.QFProof (.eq (.app f PRA.Term.var) (.app g PRA.Term.var))

private theorem codeEq_refl (f : Primrec n) : CodeEq f f := .eq_refl

private theorem codeEq_symm {f g : Primrec n} (h : CodeEq f g) : CodeEq g f :=
  PRA.QFProof.eq_symm_rule h

private theorem codeEq_trans {f g h : Primrec n} (left : CodeEq f g) (right : CodeEq g h) :
    CodeEq f h := PRA.QFProof.eq_trans_rule left right

private theorem codeEq_apply {f g : Primrec n} (h : CodeEq f g) (v : Fin n → PRA.Term m) :
    PRA.QFProof (.eq (.app f v) (.app g v)) := by
  simpa only [PRA.QFFormula.subst, PRA.Term.subst] using PRA.QFProof.subst (v := v) h

private theorem codeEq_comp {f g : Primrec n} {v w : Fin n → Primrec m}
    (function : CodeEq f g) (arguments : ∀ i, CodeEq (v i) (w i)) :
    CodeEq (.comp f v) (.comp g w) := by
  apply PRA.QFProof.eq_trans_rule PRA.QFProof.app_comp
  apply PRA.QFProof.eq_trans_rule (codeEq_apply function _)
  apply PRA.QFProof.eq_trans_rule (PRA.QFProof.app_congr (fun i => arguments i))
  exact PRA.QFProof.eq_symm_rule PRA.QFProof.app_comp

private theorem codeEq_prec {b c : Primrec n} {s t : Primrec (n + 2)}
    (base : CodeEq b c) (step : CodeEq s t) : CodeEq (.prec b s) (.prec c t) := by
  let R : PRA.Term (n + 1) := .app (.prec b s) PRA.Term.var
  let S : PRA.Term (n + 1) := .app (.prec c t) PRA.Term.var
  have eq0 : PRA.QFProof ((PRA.QFFormula.eq R S).inst 0) := by
    change PRA.QFProof (.eq (.app (.prec b s) (Fin.cases 0 PRA.Term.var))
      (.app (.prec c t) (Fin.cases 0 PRA.Term.var)))
    exact PRA.QFProof.eq_trans_rule .app_prec_zero
      (PRA.QFProof.eq_trans_rule base (PRA.QFProof.eq_symm_rule .app_prec_zero))
  have vars : Fin.cases (PRA.Term.var 0) (fun i : Fin n => PRA.Term.var i.succ) =
      PRA.Term.var := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have eqs : PRA.QFProof (.imp (.eq R S) ((PRA.QFFormula.eq R S).replace
      (.succ (.var 0)))) := by
    change PRA.QFProof (.imp (.eq R S)
      (.eq (.app (.prec b s) (Fin.cases (.succ (.var 0)) (fun i => .var i.succ)))
        (.app (.prec c t) (Fin.cases (.succ (.var 0)) (fun i => .var i.succ)))))
    apply PRA.QFProof.eq_trans_under (PRA.QFProof.weaken .app_prec_succ)
    apply PRA.QFProof.eq_trans_under (PRA.QFProof.weaken (codeEq_apply step _))
    apply PRA.QFProof.eq_trans_under (PRA.QFProof.app_congr_under ?_)
    · exact PRA.QFProof.weaken (PRA.QFProof.eq_symm_rule .app_prec_succ)
    · intro i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
      · exact PRA.QFProof.weaken .eq_refl
      · simpa only [Fin.cases_succ, Fin.cases_zero, vars] using
          (PRA.QFProof.imp_refl (φ := .eq R S))
      · exact PRA.QFProof.weaken .eq_refl
  exact PRA.QFProof.induction eq0 eqs

private theorem codeEq_fo {f g : Primrec n} (h : CodeEq f g) :
    PRA.Proof (.eq (.app f PRA.Term.var) (.app g PRA.Term.var)) := h.toProof

private theorem recursor_substitution (b : Primrec k) (s : Primrec (k + 2))
    (v : Fin k → Primrec n) :
    PRA.QFProof (.eq
      (.app (.prec (.comp b v) (.comp s
        (Fin.cases (.proj 0) (Fin.cases (.proj 1)
          (fun i => Primrec.reindex (v i) (fun j => j.succ.succ)))))) PRA.Term.var)
      (.app (.prec b s) (Fin.cases (.var 0)
        (fun i => .app (v i) (fun j => .var j.succ))))) := by
  let w : Fin (k + 2) → Primrec (n + 2) :=
    Fin.cases (.proj 0) (Fin.cases (.proj 1)
      (fun i => Primrec.reindex (v i) (fun j => j.succ.succ)))
  let R : PRA.Term (n + 1) := .app (.prec (.comp b v) (.comp s w)) PRA.Term.var
  let S : PRA.Term (n + 1) := .app (.prec b s)
    (Fin.cases (.var 0) (fun i => .app (v i) (fun j => .var j.succ)))
  have vars : Fin.cases (PRA.Term.var 0) (fun i : Fin n => PRA.Term.var i.succ) =
      PRA.Term.var := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have base : PRA.QFProof ((PRA.QFFormula.eq R S).inst 0) := by
    simp only [PRA.QFFormula.inst, PRA.QFFormula.subst, R, S, PRA.Term.subst]
    rw [Fin.map_cases (fun t : PRA.Term (n + 1) =>
      t.subst (Fin.cases (0 : PRA.Term n) PRA.Term.var))]
    change PRA.QFProof (.eq
      (.app (.prec (.comp b v) (.comp s w)) (Fin.cases 0 PRA.Term.var))
      (.app (.prec b s) (Fin.cases 0 (fun i => .app (v i) PRA.Term.var))))
    exact PRA.QFProof.eq_trans_rule .app_prec_zero
      (PRA.QFProof.eq_trans_rule .app_comp (PRA.QFProof.eq_symm_rule .app_prec_zero))
  have step : PRA.QFProof (.imp (.eq R S)
      ((PRA.QFFormula.eq R S).replace (.succ (.var 0)))) := by
    simp only [PRA.QFFormula.replace, PRA.QFFormula.subst, R, S, PRA.Term.subst]
    rw [Fin.map_cases (fun t : PRA.Term (n + 1) =>
      t.subst (Fin.cases (.succ (.var 0)) (PRA.Term.var ∘ Fin.succ)))]
    change PRA.QFProof (.imp (.eq R S) (.eq
      (.app (.prec (.comp b v) (.comp s w))
        (Fin.cases (.succ (.var 0)) (fun i => .var i.succ)))
      (.app (.prec b s) (Fin.cases (.succ (.var 0))
        (fun i => .app (v i) (fun j => .var j.succ))))))
    apply PRA.QFProof.eq_trans_under (PRA.QFProof.weaken .app_prec_succ)
    apply PRA.QFProof.eq_trans_under (PRA.QFProof.weaken .app_comp)
    apply PRA.QFProof.eq_trans_under (PRA.QFProof.app_congr_under ?_)
    · exact PRA.QFProof.weaken (PRA.QFProof.eq_symm_rule .app_prec_succ)
    · intro i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
      · exact PRA.QFProof.weaken .app_proj
      · apply PRA.QFProof.eq_trans_under (PRA.QFProof.weaken .app_proj)
        simpa only [Fin.cases_one, Fin.cases_succ, Fin.cases_zero, vars] using
          (PRA.QFProof.imp_refl (φ := .eq R S))
      · exact PRA.QFProof.weaken
          (PRA.QFProofI.app_reindex (v k) (fun j => j.succ.succ) _).toQFProof
  exact PRA.QFProof.induction base step

private theorem term_subst_cases (a : PRA.Term n) (v : Fin k → PRA.Term n)
    (s : Fin n → PRA.Term m) :
    (fun i => (Fin.cases a v i : PRA.Term n).subst s) =
      Fin.cases (a.subst s) (fun i => (v i).subst s) :=
  Fin.map_cases (fun t : PRA.Term n => t.subst s) a v

private theorem recursion_congr_apply {b : Primrec k} {s : Primrec (k + 2)}
    {c : Primrec l} {t : Primrec (l + 2)} (v : Fin k → PRA.Term n) (w : Fin l → PRA.Term n)
    (base : PRA.QFProof (.eq (.app b v) (.app c w)))
    (step : PRA.QFProof (.eq
      (.app s (Fin.cases (.var 0) (Fin.cases (.var 1) (fun i => (v i).shift.shift))))
      (.app t (Fin.cases (.var 0) (Fin.cases (.var 1) (fun i => (w i).shift.shift))))))
    (a : PRA.Term n) :
    PRA.QFProof (.eq (.app (.prec b s) (Fin.cases a v))
      (.app (.prec c t) (Fin.cases a w))) := by
  let R : PRA.Term (n + 1) := .app (.prec b s) (Fin.cases (.var 0) (fun i => (v i).shift))
  let S : PRA.Term (n + 1) := .app (.prec c t) (Fin.cases (.var 0) (fun i => (w i).shift))
  have zero : PRA.QFProof ((PRA.QFFormula.eq R S).inst 0) := by
    simpa only [R, S, PRA.QFFormula.inst, PRA.QFFormula.subst, PRA.Term.subst,
      term_subst_cases, Fin.cases_zero, Fin.cases_succ, PRA.Term.subst_shift,
      PRA.Term.subst_id] using
      PRA.QFProof.eq_trans_rule (PRA.QFProof.app_prec_zero (f := b) (g := s) (v := v))
        (PRA.QFProof.eq_trans_rule base
          (PRA.QFProof.eq_symm_rule (PRA.QFProof.app_prec_zero (f := c) (g := t))))
  have step' : PRA.QFProof (.eq
      (.app s (Fin.cases (.var 0) (Fin.cases R (fun i => (v i).shift))))
      (.app t (Fin.cases (.var 0) (Fin.cases R (fun i => (w i).shift))))) := by
    have h := PRA.QFProof.subst (v := Fin.cases (PRA.Term.var (n := n + 1) 0)
      (Fin.cases R (PRA.Term.var ∘ Fin.succ))) step
    simpa only [PRA.QFFormula.subst, PRA.Term.subst, term_subst_cases, Fin.cases_zero,
      Fin.cases_succ, Fin.cases_one, PRA.Term.subst_shift, PRA.Term.shift, PRA.Term.subst_comp,
      Function.comp_def, Function.comp_apply] using h
  have succ : PRA.QFProof (.imp (.eq R S)
      ((PRA.QFFormula.eq R S).replace (.succ (.var 0)))) := by
    simp only [R, S, PRA.QFFormula.replace, PRA.QFFormula.subst, PRA.Term.subst,
      term_subst_cases, Fin.cases_zero, Fin.cases_succ, PRA.Term.subst_shift]
    apply PRA.QFProof.eq_trans_under (PRA.QFProof.weaken .app_prec_succ)
    apply PRA.QFProof.eq_trans_under (PRA.QFProof.weaken step')
    apply PRA.QFProof.eq_trans_under (PRA.QFProof.app_congr_under ?_)
    · exact PRA.QFProof.weaken (PRA.QFProof.eq_symm_rule .app_prec_succ)
    · intro i
      refine Fin.cases (PRA.QFProof.weaken .eq_refl) (fun i => ?_) i
      refine Fin.cases ?_ (fun _ => PRA.QFProof.weaken .eq_refl) i
      exact PRA.QFProof.imp_refl
  have result := PRA.QFProof.subst (v := Fin.cases a PRA.Term.var)
    (PRA.QFProof.induction zero succ)
  simpa only [R, S, PRA.QFFormula.subst, PRA.Term.subst, term_subst_cases, Fin.cases_zero,
    Fin.cases_succ, PRA.Term.subst_shift, PRA.Term.subst_id] using result

namespace Target

open PRA PRA.Formula PRA.Proof

variable {n : Nat} {φ ψ χ θ : PRA.Formula n}

private theorem imp_refl : Proof (φ ⇒ φ) :=
  mp (mp imp_distrib (imp_imp_self (φ := φ) (ψ := φ ⇒ φ))) imp_imp_self

private theorem weaken (h : Proof ψ) : Proof (φ ⇒ ψ) :=
  mp imp_imp_self h

private theorem mp_under (h₁ : Proof (φ ⇒ ψ ⇒ χ)) (h₂ : Proof (φ ⇒ ψ)) :
    Proof (φ ⇒ χ) :=
  mp (mp imp_distrib h₁) h₂

private theorem imp_trans_rule (h₁ : Proof (φ ⇒ ψ)) (h₂ : Proof (ψ ⇒ χ)) :
    Proof (φ ⇒ χ) :=
  mp_under (weaken h₂) h₁

private theorem imp_swap_rule (h : Proof (φ ⇒ ψ ⇒ χ)) : Proof (ψ ⇒ φ ⇒ χ) :=
  mp_under (weaken (mp imp_distrib h)) imp_imp_self

private theorem imp_trans : Proof ((φ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ φ ⇒ χ) :=
  imp_swap_rule (imp_trans_rule imp_imp_self imp_distrib)

private theorem imp_apply : Proof (φ ⇒ (φ ⇒ ψ) ⇒ ψ) :=
  imp_swap_rule imp_refl

private theorem not_not_intro : Proof (φ ⇒ ∼ ∼ φ) :=
  imp_apply

private theorem not_not_elim : Proof (∼ ∼ φ ⇒ φ) :=
  mp imp_contra not_not_intro

private theorem contraposition : Proof ((φ ⇒ ψ) ⇒ ∼ ψ ⇒ ∼ φ) :=
  imp_trans

private theorem contrapose (h : Proof (φ ⇒ ψ)) : Proof (∼ ψ ⇒ ∼ φ) :=
  mp contraposition h

private theorem and_intro_under (h₁ : Proof (φ ⇒ ψ)) (h₂ : Proof (φ ⇒ χ)) :
    Proof (φ ⇒ ψ ⊓ χ) :=
  mp_under (imp_trans_rule h₁ and_intro) h₂

private theorem and_curry (h : Proof (φ ⊓ ψ ⇒ χ)) : Proof (φ ⇒ ψ ⇒ χ) :=
  imp_trans_rule and_intro (mp (imp_swap_rule imp_trans) h)

private theorem or_elim_imp (hφ : Proof (φ ⇒ χ)) (hψ : Proof (ψ ⇒ χ)) :
    Proof (φ ⊔ ψ ⇒ χ) :=
  mp (mp or_elim hφ) hψ

private theorem false_elim {A : Formula n} : Proof (⊥ ⇒ A) :=
  mp imp_contra (weaken (imp_refl (φ := ⊥)))

private theorem imp_trans_under (h₁ : Proof (θ ⇒ φ ⇒ ψ))
    (h₂ : Proof (θ ⇒ ψ ⇒ χ)) : Proof (θ ⇒ φ ⇒ χ) :=
  mp_under (imp_trans_rule h₁ imp_trans) h₂

private theorem cases_rule (h : Proof (φ ⊔ ψ)) (h₁ : Proof (φ ⇒ χ))
    (h₂ : Proof (ψ ⇒ χ)) : Proof χ :=
  mp (mp (mp or_elim h₁) h₂) h

private theorem cases_under (h : Proof (φ ⊔ ψ)) (h₁ : Proof (θ ⇒ φ ⇒ χ))
    (h₂ : Proof (θ ⇒ ψ ⇒ χ)) : Proof (θ ⇒ χ) :=
  mp_under (mp_under (imp_trans_rule h₁ or_elim) h₂) (weaken h)

private theorem excluded_middle (A : Formula n) : Proof (A ⊔ ∼ A) :=
  mp (mp imp_contra imp_apply) (mp_under (contrapose or_right) (contrapose or_left))

private theorem eq_symm_rule {s t : Term n} (h : Proof (s ≡ t)) :
    Proof (t ≡ s) := mp eq_symm h

private theorem eq_trans_rule {s t u : Term n} (h₁ : Proof (s ≡ t))
    (h₂ : Proof (t ≡ u)) : Proof (s ≡ u) := mp (mp eq_trans h₁) h₂

private theorem eq_trans_under {s t u : Term n} (h₁ : Proof (φ ⇒ s ≡ t))
    (h₂ : Proof (φ ⇒ t ≡ u)) : Proof (φ ⇒ s ≡ u) :=
  mp_under (imp_trans_rule h₁ eq_trans) h₂

private theorem app_congr_list {m : Nat} [BEq (Fin m)] [LawfulBEq (Fin m)]
    {f : Primrec m} {v w : Fin m → Term n}
    (h : ∀ i, Proof (φ ⇒ v i ≡ w i)) (is : List (Fin m)) :
    Proof (φ ⇒ Term.app f v ≡ Term.app f (fun i => if i ∈ is then w i else v i)) := by
  induction is with
  | nil => simpa using (weaken (φ := φ) (eq_refl (t := Term.app f v)))
  | cons i is ih =>
    let u : Fin m → Term n := fun j => if j ∈ is then w j else v j
    have hi : Proof (φ ⇒ u i ≡ w i) := by
      cases (inferInstance : Decidable (i ∈ is)) with
      | isTrue hm => simpa [u, hm] using (weaken (φ := φ) (eq_refl (t := w i)))
      | isFalse hm => simpa [u, hm] using h i
    have hu : (fun j => if j = i then w i else u j) =
        (fun j => if j ∈ i :: is then w j else v j) := by
      funext j
      cases (inferInstance : Decidable (j = i)) with
      | isTrue hj => subst j; simp
      | isFalse hj => simp [u, hj]
    simpa only [hu] using eq_trans_under ih (imp_trans_rule hi (eq_congr_ith (f := f)))

private theorem app_congr_under {m : Nat} {f : Primrec m} {v w : Fin m → Term n}
    (h : ∀ i, Proof (φ ⇒ v i ≡ w i)) :
    Proof (φ ⇒ Term.app f v ≡ Term.app f w) := by
  letI : BEq (Fin m) := instBEqOfDecidableEq
  letI : LawfulBEq (Fin m) :=
    { rfl := decide_eq_true rfl, eq_of_beq := of_decide_eq_true }
  simpa only [List.mem_finRange, ite_true] using app_congr_list h (List.finRange m)

private theorem app_congr {m : Nat} {f : Primrec m} {v w : Fin m → Term n}
    (h : ∀ i, Proof (v i ≡ w i)) : Proof (Term.app f v ≡ Term.app f w) :=
  mp (app_congr_under (φ := ⊤) (fun i => weaken (h i))) imp_refl

private theorem unary_congr_under {f : Primrec 1} {s t : Term n}
    (h : Proof (φ ⇒ s ≡ t)) : Proof (φ ⇒ Term.app₁ f s ≡ Term.app₁ f t) := by
  apply app_congr_under
  intro i
  simpa only [Term.app₁, Fin.cases_fin_one] using h

private theorem unary_congr {f : Primrec 1} {s t : Term n}
    (h : Proof (s ≡ t)) : Proof (Term.app₁ f s ≡ Term.app₁ f t) :=
  mp (unary_congr_under (φ := ⊤) (weaken h)) imp_refl

private theorem eq_congr_under {s s' t t' : Term n} (h₁ : Proof (φ ⇒ s ≡ s'))
    (h₂ : Proof (φ ⇒ t ≡ t')) : Proof (φ ⇒ (s ≡ t) ⇒ s' ≡ t') :=
  imp_trans_under (imp_trans_rule (imp_trans_rule h₁ eq_symm) eq_trans)
    (imp_trans_rule h₂ (imp_swap_rule eq_trans))

private theorem imp_mono_under {ρ : Formula n} (h₁ : Proof (ρ ⇒ χ ⇒ φ))
    (h₂ : Proof (ρ ⇒ ψ ⇒ θ)) : Proof (ρ ⇒ (φ ⇒ ψ) ⇒ χ ⇒ θ) :=
  imp_trans_under (imp_trans_rule h₁ imp_trans) (imp_trans_rule h₂ (imp_swap_rule imp_trans))

private theorem and_mono_under {ρ : Formula n} (h₁ : Proof (ρ ⇒ φ ⇒ χ))
    (h₂ : Proof (ρ ⇒ ψ ⇒ θ)) : Proof (ρ ⇒ φ ⊓ ψ ⇒ χ ⊓ θ) :=
  and_curry (and_intro_under
    (mp_under (imp_trans_rule and_left h₁) (imp_trans_rule and_right and_left))
    (mp_under (imp_trans_rule and_left h₂) (imp_trans_rule and_right and_right)))

private theorem or_elim_under (h₁ : Proof (θ ⇒ φ ⇒ χ)) (h₂ : Proof (θ ⇒ ψ ⇒ χ)) :
    Proof (θ ⇒ φ ⊔ ψ ⇒ χ) := mp_under (imp_trans_rule h₁ or_elim) h₂

private theorem or_mono_under {ρ : Formula n} (h₁ : Proof (ρ ⇒ φ ⇒ χ))
    (h₂ : Proof (ρ ⇒ ψ ⇒ θ)) : Proof (ρ ⇒ φ ⊔ ψ ⇒ χ ⊔ θ) :=
  or_elim_under (imp_trans_under h₁ (weaken or_left)) (imp_trans_under h₂ (weaken or_right))

private theorem term_congr_under (t : Term m) {v w : Fin m → Term n}
    (h : ∀ i, Proof (φ ⇒ v i ≡ w i)) : Proof (φ ⇒ t.subst v ≡ t.subst w) := by
  induction t with
  | var i => exact h i
  | app f u ih => exact app_congr_under (fun i => ih i h)

private def Entails {n} : List (Formula n) → Formula n → Prop
  | [], A => Proof A
  | B :: H, A => Entails H (.imp B A)

private theorem entails_of_proof {H : List (Formula n)} {A} (h : Proof A) : Entails H A := by
  induction H generalizing A with
  | nil => exact h
  | cons B H ih => exact ih (weaken h)

private theorem entails_mp {H : List (Formula n)} {A B}
    (hf : Entails H (.imp A B)) (ha : Entails H A) : Entails H B := by
  induction H generalizing A B with
  | nil => exact .mp hf ha
  | cons C H ih =>
      exact ih (ih (entails_of_proof .imp_distrib) hf) ha

private theorem entails_head {H : List (Formula n)} {A} : Entails (A :: H) A := by
  change Entails H (.imp A A)
  exact entails_of_proof imp_refl

private theorem entails_cons {H : List (Formula n)} {A B} (h : Entails H A) :
    Entails (B :: H) A := by
  change Entails H (.imp B A)
  exact entails_mp (entails_of_proof .imp_imp_self) h

private theorem entails_hyp {H : List (Formula n)} {A} (h : A ∈ H) : Entails H A := by
  induction H with
  | nil => cases h
  | cons B H ih =>
      rcases List.mem_cons.mp h with eq | mem
      · subst A; exact entails_head
      · exact entails_cons (ih mem)

private theorem entails_subst {H : List (Formula n)} {A} (h : Entails H A)
    (v : Fin n → PRA.Term m) : Entails (H.map (fun P => P.subst v)) (A.subst v) := by
  induction H generalizing A with
  | nil => exact PRA.Proof.subst h v
  | cons B H ih => exact ih h

private theorem entails_gen {H : List (Formula n)} {A : Formula (n + 1)}
    (h : Entails (H.map Formula.shift) A) : Entails H (.all A) := by
  induction H generalizing A with
  | nil => exact .gen h
  | cons B H ih =>
      change Entails H (.imp B (.all A))
      exact entails_mp (entails_of_proof .forall_imp) (ih h)

private theorem entails_all_body {H : List (Formula n)} {A : Formula (n + 1)}
    (h : Entails H (.all A)) : Entails (H.map Formula.shift) A := by
  have shifted := entails_subst h (PRA.Term.var ∘ Fin.succ)
  change Entails (H.map (fun P => P.subst (PRA.Term.var ∘ Fin.succ))) A
  have opened := entails_mp (entails_of_proof (PRA.Proof.forall_elim (t := .var 0))) shifted
  simpa only [Formula.shift, Formula.subst, Function.comp_apply, PRA.Term.shift, PRA.Term.subst,
    Formula.inst_shift_all] using opened

private theorem entails_exists_elim {H : List (Formula n)} {A : Formula (n + 1)} {B}
    (h : Entails H (.ex A)) (body : Entails (A :: H.map Formula.shift) B.shift) :
    Entails H B :=
  entails_mp (entails_mp (entails_of_proof .exists_elim) (entails_gen body)) h

private theorem entails_induction {H : List (Formula n)} {A : Formula (n + 1)}
    (qf : A.QuantifierFree) (base : Entails H (A.inst 0))
    (step : Entails (A :: H.map Formula.shift) (A.replace (.succ (.var 0)))) :
    Entails H (.all A) :=
  entails_mp (entails_mp (entails_of_proof (.induction qf)) base) (entails_gen step)

private theorem entails_map {H K : List (Formula n)}
    (assumptions : ∀ A ∈ H, Entails K A) {B} (h : Entails H B) : Entails K B := by
  induction H generalizing K B with
  | nil => exact entails_of_proof h
  | cons A H ih =>
      exact entails_mp (ih (fun C hc => assumptions C (List.mem_cons_of_mem A hc)) h)
        (assumptions A (List.mem_cons_self))

private theorem forall_mono {A B : Formula (n + 1)} (h : Proof (.imp A B)) :
    Proof (.imp (.all A) (.all B)) := by
  apply entails_gen (H := [.all A])
  exact entails_mp (entails_of_proof h) (entails_all_body entails_head)

private theorem exists_mono {A B : Formula (n + 1)} (h : Proof (.imp A B)) :
    Proof (.imp (.ex A) (.ex B)) := by
  apply entails_exists_elim (H := [.ex A]) entails_head
  have hb := entails_mp (entails_of_proof h)
    (entails_head (H := [(Formula.ex A).shift]))
  have hi : Proof (.imp B (Formula.ex B).shift) := by
    simpa only [Formula.shift, Formula.subst, PRA.Term.shift, PRA.Term.subst,
      Function.comp_apply, Formula.inst_shift_all] using
      (PRA.Proof.exists_intro (φ := B.subst
        (Fin.cases (.var 0) (fun i => .var i.succ.succ))) (t := .var 0))
  exact entails_mp (entails_of_proof hi) hb

private theorem forall_mono_under {C : Formula n} {A B : Formula (n + 1)}
    (h : Proof (.imp C.shift (.imp A B))) : Proof (.imp C (.imp (.all A) (.all B))) := by
  apply entails_gen (H := [.all A, C])
  have hc : Entails ([.all A, C].map Formula.shift) C.shift :=
    entails_cons entails_head
  exact entails_mp (entails_mp (entails_of_proof h) hc)
    (entails_all_body entails_head)

private theorem exists_mono_under {C : Formula n} {A B : Formula (n + 1)}
    (h : Proof (.imp C.shift (.imp A B))) : Proof (.imp C (.imp (.ex A) (.ex B))) := by
  apply entails_exists_elim (H := [.ex A, C]) entails_head
  have hc : Entails (A :: [.ex A, C].map Formula.shift) C.shift :=
    entails_cons (entails_cons entails_head)
  have hb := entails_mp (entails_mp (entails_of_proof h) hc) entails_head
  have hi : Proof (.imp B (Formula.ex B).shift) := by
    simpa only [Formula.shift, Formula.subst, PRA.Term.shift, PRA.Term.subst,
      Function.comp_apply, Formula.inst_shift_all] using
      (PRA.Proof.exists_intro (φ := B.subst
        (Fin.cases (.var 0) (fun i => .var i.succ.succ))) (t := .var 0))
  exact entails_mp (entails_of_proof hi) hb

private theorem formula_congr_under (A : Formula m) {v w : Fin m → PRA.Term n}
    (h : ∀ i, Proof (φ ⇒ v i ≡ w i)) : Proof (φ ⇒ A.subst v ⇒ A.subst w) := by
  induction A generalizing n with
  | false => exact weaken imp_refl
  | eq s t => exact eq_congr_under (term_congr_under s h) (term_congr_under t h)
  | imp A B ihA ihB => exact imp_mono_under (ihA (fun i => imp_trans_rule (h i) eq_symm)) (ihB h)
  | and A B ihA ihB => exact and_mono_under (ihA h) (ihB h)
  | or A B ihA ihB => exact or_mono_under (ihA h) (ihB h)
  | all A ih | ex A ih =>
      first | apply forall_mono_under | apply exists_mono_under
      apply ih
      intro i
      refine Fin.cases (weaken eq_refl) (fun j => ?_) i
      exact PRA.Proof.subst (h j) (PRA.Term.var ∘ Fin.succ)

private theorem formula_congr (A : Formula m) {v w : Fin m → PRA.Term n}
    (h : ∀ i, Proof (.eq (v i) (w i))) : Proof (.imp (A.subst v) (A.subst w)) :=
  .mp (formula_congr_under A (φ := .true) (fun i => weaken (h i))) imp_refl

private theorem instance_congr_under (A : Formula (n + 1)) {s t : PRA.Term n}
    (h : Proof (φ ⇒ s ≡ t)) : Proof (φ ⇒ A.inst s ⇒ A.inst t) :=
  formula_congr_under A (fun i => Fin.cases h (fun _ => weaken eq_refl) i)

end Target

private theorem embedLeft_val (i : Fin k) : (Fin.embedLeft (n := n) i).val = i.val := by
  simp only [Fin.embedLeft, Fin.val_rev, Fin.val_addNat]
  omega

private theorem succAdd_val (i : Fin ((k + 1) + n)) : (Fin.succAdd i).val = i.val := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp [Fin.succAdd]
    · simp [Fin.succAdd, embedLeft_val]
  · simp [Fin.succAdd, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem addCases_embedLeft {α : Sort u} (x : Fin k → α) (v : Fin n → α) (i : Fin k) :
    Fin.addCases x v (Fin.embedLeft i) = x i := by
  have bound : (Fin.embedLeft (n := n) i).val < k := by
    rw [embedLeft_val]
    exact i.isLt
  simp only [Fin.addCases, dite_eq_left bound]
  congr 1
  apply Fin.ext
  exact embedLeft_val i

private theorem addCases_moveToFront {α : Sort u} (a : α) (x : Fin k → α) (v : Fin n → α) :
    (fun i => Fin.addCases (Fin.cases a x) v (Fin.moveToFront i)) =
      Fin.addCases x (Fin.cases a v) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.moveToFront, Fin.addCases_left, addCases_embedLeft, Fin.cases_succ]
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.moveToFront, Fin.addCases_right, Fin.cases_zero, addCases_embedLeft]
    · simp only [Fin.moveToFront, Fin.addCases_right, Fin.cases_succ]

private theorem cases_succAdd {α : Sort u} (a : α) (x : Fin k → α) (v : Fin n → α) :
    (fun i => Fin.cases a (Fin.addCases x v) (Fin.succAdd i)) =
      Fin.addCases (Fin.cases a x) v := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.succAdd, Fin.addCases_left, Fin.cases_zero]
    · simp only [Fin.succAdd, Fin.addCases_left, Fin.cases_succ, addCases_embedLeft]
  · simp only [Fin.succAdd, Fin.addCases_right, Fin.cases_succ]

private theorem local_addCases {α : Sort u} (x : Fin k → α) (v : Fin n → α)
    (i : Fin (0 + n)) :
    (Fin.addCases x v (Fin.addCases (Fin.elim0 : Fin 0 → Fin (k + n)) (Fin.natAdd k) i) : α) =
      (Fin.addCases (Fin.elim0 : Fin 0 → α) v i : α) := by
  refine Fin.addCases (fun i => Fin.elim0 i) (fun i => ?_) i
  simp only [Fin.addCases_right]

private theorem term_lam_apply (f : Primrec (k + (n + 1))) (a : PRA.Term m)
    (x : Fin k → PRA.Term m) (v : Fin n → PRA.Term m) :
    PRA.QFProof (.eq (.app (Primrec.reindex f Fin.moveToFront) (Fin.addCases (Fin.cases a x) v))
      (.app f (Fin.addCases x (Fin.cases a v)))) := by
  simpa only [addCases_moveToFront] using
    (PRA.QFProofI.app_reindex f Fin.moveToFront (Fin.addCases (Fin.cases a x) v)).toQFProof

private theorem term_app_apply (f : Primrec ((k + 1) + n)) (g : Primrec (0 + n))
    (x : Fin k → PRA.Term m) (v : Fin n → PRA.Term m) :
    PRA.QFProof (.eq
      (.app (.comp f (fun i => Fin.cases
        (Primrec.reindex g (Fin.addCases Fin.elim0 (Fin.natAdd k)))
        Primrec.proj (Fin.succAdd i))) (Fin.addCases x v))
      (.app f (Fin.addCases (Fin.cases (.app g (Fin.addCases Fin.elim0 v)) x) v))) := by
  apply PRA.QFProof.eq_trans_rule .app_comp
  apply PRA.QFProof.app_congr
  intro i
  rw [← congrFun (cases_succAdd (.app g (Fin.addCases Fin.elim0 v)) x v) i]
  generalize Fin.succAdd i = j
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [local_addCases, Fin.cases_zero] using
      (PRA.QFProofI.app_reindex g (Fin.addCases Fin.elim0 (Fin.natAdd k))
        (Fin.addCases x v)).toQFProof
  · exact .app_proj

private theorem addCases_shift (v : Fin n → PRA.Term q) (i : Fin (0 + n)) :
    (Fin.addCases Fin.elim0 v i : PRA.Term q).shift =
      (Fin.addCases Fin.elim0 (fun i => (v i).shift) i : PRA.Term (q + 1)) := by
  refine Fin.addCases (fun i => Fin.elim0 i) (fun i => ?_) i
  simp only [Fin.addCases_right]

private theorem recursion_step_apply (g : Primrec (2 + n)) (a b : PRA.Term q)
    (v : Fin n → PRA.Term q) :
    PRA.QFProof (.eq
      (.app (Primrec.reindex g
        (fun i => Fin.cases 0 (fun j => (Fin.succAdd j).succ) (Fin.succAdd i)))
        (Fin.cases a (Fin.cases b (Fin.addCases Fin.elim0 v))))
      (.app g (Fin.addCases (Fin.cases a (Fin.cases b Fin.elim0)) v))) := by
  have tuple : (fun i : Fin (2 + n) =>
      (Fin.cases a (Fin.cases b (Fin.addCases Fin.elim0 v))
        (Fin.cases 0 (fun (j : Fin (1 + n)) => (Fin.succAdd j).succ) (Fin.succAdd i)) :
          PRA.Term q)) = Fin.addCases (Fin.cases a (Fin.cases b Fin.elim0)) v := by
    funext i
    rw [← congrFun (cases_succAdd a (Fin.cases b Fin.elim0) v) i]
    generalize Fin.succAdd i = j
    refine Fin.cases rfl (fun j => ?_) j
    exact congrFun (cases_succAdd b Fin.elim0 v) j
  simpa only [tuple] using (PRA.QFProofI.app_reindex g
    (fun i => Fin.cases 0 (fun j => (Fin.succAdd j).succ) (Fin.succAdd i))
    (Fin.cases a (Fin.cases b (Fin.addCases Fin.elim0 v)))).toQFProof

private theorem recursor_apply (f : Primrec (0 + n)) (g : Primrec (2 + n))
    (x : Fin 1 → PRA.Term q) (v : Fin n → PRA.Term q) :
    PRA.QFProof (.eq
      (.app (Primrec.reindex (.prec f (Primrec.reindex g
        (fun i => Fin.cases 0 (fun j => (Fin.succAdd j).succ) (Fin.succAdd i))))
        (Fin.cases (Fin.embedLeft 0) (Fin.addCases Fin.elim0 (Fin.natAdd 1))))
        (Fin.addCases x v))
      (.app (.prec f (Primrec.reindex g
        (fun i => Fin.cases 0 (fun j => (Fin.succAdd j).succ) (Fin.succAdd i))))
        (Fin.cases (x 0) (Fin.addCases Fin.elim0 v)))) := by
  apply PRA.QFProof.eq_trans_rule (PRA.QFProofI.app_reindex _ _ _).toQFProof
  apply PRA.QFProof.app_congr
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa only [Fin.cases_zero, addCases_embedLeft] using
      (PRA.QFProof.eq_refl (t := x 0))
  · simp only [Fin.cases_succ]
    refine Fin.addCases (fun i => Fin.elim0 i) (fun i => ?_) i
    simp only [Fin.addCases_right]
    exact .eq_refl

private theorem recursion_apply (f : Primrec (0 + n)) (g : Primrec (2 + n))
    (a : Primrec (0 + n)) (v : Fin n → PRA.Term q) :
    PRA.QFProof (.eq
      (.app (.comp (Primrec.reindex (.prec f (Primrec.reindex g
        (fun i => Fin.cases 0 (fun j => (Fin.succAdd j).succ) (Fin.succAdd i))))
        (Fin.cases (Fin.embedLeft 0) (Fin.addCases Fin.elim0 (Fin.natAdd 1))))
        (fun i => Fin.cases
          (Primrec.reindex a (Fin.addCases Fin.elim0 (Fin.natAdd 0)))
          Primrec.proj (Fin.succAdd i))) (Fin.addCases Fin.elim0 v))
      (.app (.prec f (Primrec.reindex g
        (fun i => Fin.cases 0 (fun j => (Fin.succAdd j).succ) (Fin.succAdd i))))
        (Fin.cases (.app a (Fin.addCases Fin.elim0 v)) (Fin.addCases Fin.elim0 v)))) := by
  exact PRA.QFProof.eq_trans_rule (term_app_apply _ _ Fin.elim0 v)
    (recursor_apply f g _ v)

private def unaryFormula (A : PRA.Formula (1 + n)) : PRA.Formula ((0 + n) + 1) :=
  A.subst (fun i => .var (Fin.succAdd i))

private theorem numerical_reindex (f : Primrec (0 + n)) :
    PRA.Proof (.eq
      (.app (Primrec.reindex f (Fin.addCases Fin.elim0 (Fin.natAdd 0))) PRA.Term.var)
      (.app f PRA.Term.var)) := by
  have indices : (fun i : Fin (0 + n) =>
      PRA.Term.var (Fin.addCases Fin.elim0 (Fin.natAdd 0) i)) = PRA.Term.var := by
    funext i
    congr 1
    apply Fin.ext
    refine Fin.addCases (fun j => Fin.elim0 j) (fun j => ?_) i
    simp only [Fin.addCases_right, Fin.val_natAdd, Nat.zero_add]
  simpa only [indices, PRA.QFFormula.toFormula] using
    (PRA.QFProofI.app_reindex f (Fin.addCases Fin.elim0 (Fin.natAdd 0))
      PRA.Term.var).toQFProof.toProof

private theorem translate_application {E Ξ ρ π n P t A f B}
    (predicate : PredicateTranslation E Ξ ρ π n P ⟨1, .prop⟩ A)
    (argument : TermTranslation E Ξ ρ n t 0 f)
    (result : PredicateTranslation E Ξ ρ π n (.app P t) ⟨0, .prop⟩ B) :
    PRA.Proof (B.iff ((unaryFormula A).inst (.app f PRA.Term.var))) := by
  cases result with
  | app predicate' argument' =>
      cases predicate_translation_unique predicate predicate'
      cases term_translation_unique argument argument'
      simp only [unaryFormula, PRA.Formula.inst, PRA.Formula.subst_comp, PRA.Term.subst]
      apply PRA.Proof.mp (PRA.Proof.mp .and_intro ?_) ?_
      · apply Target.formula_congr
        intro i
        refine Fin.cases ?_ (fun _ => PRA.Proof.eq_refl) (Fin.succAdd i)
        exact numerical_reindex f
      · apply Target.formula_congr
        intro i
        refine Fin.cases ?_ (fun _ => PRA.Proof.eq_refl) (Fin.succAdd i)
        exact Target.eq_symm_rule (numerical_reindex f)

private theorem translate_zero {E Ξ ρ n f}
    (translation : TermTranslation E Ξ ρ n .zero 0 f) :
    PRA.Proof (.eq (.app f PRA.Term.var) 0) := by
  cases translation
  change PRA.Proof (.eq (.app (.comp .zero Fin.elim0) PRA.Term.var)
    (.app .zero Fin.elim0))
  have empty : (fun i : Fin 0 => PRA.Term.app (Fin.elim0 i : Primrec (0 + n))
      PRA.Term.var) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  simpa only [Primrec.comp₀, PRA.Term.app₀, empty] using
    (PRA.Proof.app_comp (f := Primrec.zero) (g := Fin.elim0) (v := PRA.Term.var (n := 0 + n)))

private theorem translate_successor {E Ξ ρ n t f g}
    (argument : TermTranslation E Ξ ρ n t 0 f)
    (result : TermTranslation E Ξ ρ n (.app .succ t) 0 g) :
    PRA.Proof (.eq (.app g PRA.Term.var) (.succ (.app f PRA.Term.var))) := by
  cases result with
  | app function argument' =>
      cases function
      cases term_translation_unique argument argument'
      apply Target.eq_trans_rule .app_comp
      apply Target.eq_trans_rule
        (PRA.QFProofI.app_reindex Primrec.succ Fin.embedLeft _).toQFProof.toProof
      apply Target.app_congr
      intro i
      have hi : i = (0 : Fin 1) := by omega
      subst i
      have idx : Fin.succAdd (Fin.embedLeft (n := n) (0 : Fin 1)) = 0 := by
        apply Fin.ext
        simp only [succAdd_val, embedLeft_val, Fin.val_zero]
      simpa only [idx, Fin.cases_zero, PRA.Term.succ, PRA.Term.app₁, Fin.cases_zero] using
        numerical_reindex f

private theorem declaration_origin {E d} {name : Lean.Name} (valid : EnvironmentWF E)
    (lookup : E[name]? = some d) : ∃ F, DeclarationWF F d := by
  induction valid with
  | empty => simp at lookup
  | @insert E e previous fresh formed ih =>
      by_cases same : e.name = name
      · have eq : e = d := by
          simpa only [Std.ExtHashMap.getElem?_insert, same, beq_self_eq_true,
            ↓reduceIte, Option.some.injEq] using lookup
        subst d
        exact ⟨E, formed⟩
      · apply ih
        simpa [Std.ExtHashMap.getElem?_insert, same] using lookup

private theorem rename_subst0 (t a : Term) (r : Renaming) :
    (t.subst0 a).rename r = (t.rename (Renaming.lift 1 r)).subst0 (a.rename r) := by
  simp only [Term.subst0, Term.rename_subst, Term.subst_rename]
  congr 1
  funext i
  cases i with
  | zero => simp [Renaming.lift]
  | succ i => simp [Renaming.lift, Term.rename, Nat.add_comm]

private theorem cases_eta {α : Sort u} (x : Fin (k + 1) → α) :
    Fin.cases (x 0) (fun i => x i.succ) = x := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem cases_lift {α : Sort u} (a : α) (v : Fin m → α) (s : Fin n → Fin m) :
    (fun i => (Fin.cases a v (Fin.cases 0 (fun i => (s i).succ) i) : α)) =
      Fin.cases a (fun i => v (s i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem reindex_arguments (f : Primrec k) (x : Fin k → PRA.Term q)
    (v : Fin n → PRA.Term q) :
    PRA.QFProof (.eq (.app (Primrec.reindex f Fin.embedLeft) (Fin.addCases x v)) (.app f x)) := by
  simpa only [addCases_embedLeft] using
    (PRA.QFProofI.app_reindex f Fin.embedLeft (Fin.addCases x v)).toQFProof

private theorem term_translation_rename {E Ξ ρ n t k f} (valid : EnvironmentWF E)
    (translation : TermTranslation E Ξ ρ n t k f) :
    ∀ {m} (r : Renaming) (s : Fin n → Fin m), (∀ i, r i.val = (s i).val) →
      ∃ g, TermTranslation E Ξ ρ m (t.rename r) k g ∧
        ∀ {q} (x : Fin k → PRA.Term q) (v : Fin m → PRA.Term q),
          PRA.QFProof (.eq (.app g (Fin.addCases x v))
            (.app f (Fin.addCases x (fun i => v (s i))))) := by
  induction translation using TermTranslation.rec
    (motive_2 := fun n fs ks _ => ∀ {m} (r : Renaming) (s : Fin n → Fin m),
      (∀ i, r i.val = (s i).val) →
        FunctionArgumentsTranslation E Ξ ρ m (fs.map (Term.rename r)) ks) with
  | bvar i =>
      intro m r s hs
      simp only [Term.rename]
      simp only [hs]
      refine ⟨_, .bvar (s i), ?_⟩
      intro q x v
      have left : PRA.QFProof (.eq (.app (.proj ((s i).natAdd 0)) (Fin.addCases x v))
          (v (s i))) := by
        simpa only [Fin.addCases_right] using
          (PRA.QFProof.app_proj (i := (s i).natAdd 0) (v := Fin.addCases x v))
      have right : PRA.QFProof (.eq (.app (.proj (i.natAdd 0))
          (Fin.addCases x (fun i => v (s i)))) (v (s i))) := by
        simpa only [Fin.addCases_right] using
          (PRA.QFProof.app_proj (i := i.natAdd 0) (v := Fin.addCases x (fun i => v (s i))))
      exact PRA.QFProof.eq_trans_rule left (PRA.QFProof.eq_symm_rule right)
  | zero =>
      intro m r s hs
      simp only [Term.rename]
      refine ⟨_, .zero, ?_⟩
      intro q x v
      apply PRA.QFProof.eq_trans_rule .app_comp
      apply PRA.QFProof.eq_trans_rule (PRA.QFProof.app_congr (fun i => Fin.elim0 i))
      exact PRA.QFProof.eq_symm_rule .app_comp
  | succ =>
      intro m r s hs
      simp only [Term.rename]
      refine ⟨_, .succ, ?_⟩
      intro q x v
      exact PRA.QFProof.eq_trans_rule (reindex_arguments _ x v)
        (PRA.QFProof.eq_symm_rule (reindex_arguments _ x _))
  | parameter lookup =>
      intro m r s hs
      simp only [Term.rename]
      refine ⟨_, .parameter lookup, ?_⟩
      intro q x v
      exact PRA.QFProof.eq_trans_rule (reindex_arguments _ x v)
        (PRA.QFProof.eq_symm_rule (reindex_arguments _ x _))
  | lam body ih =>
      intro m r s hs
      simp only [Term.rename]
      obtain ⟨g, tg, hg⟩ := ih (Renaming.lift 1 r) (Fin.cases 0 (fun i => (s i).succ)) (by
        intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [Renaming.lift]
        · simp [Renaming.lift, hs, Nat.add_comm])
      refine ⟨_, .lam tg, ?_⟩
      intro q x v
      have hb := hg (fun i => x i.succ) (Fin.cases (x 0) v)
      simp only [cases_lift] at hb
      have eq := PRA.QFProof.eq_trans_rule (term_lam_apply g (x 0) (fun i => x i.succ) v)
        (PRA.QFProof.eq_trans_rule hb
          (PRA.QFProof.eq_symm_rule (term_lam_apply _ (x 0) (fun i => x i.succ) _)))
      simpa only [cases_lift, cases_eta] using eq
  | app function argument ihf iha =>
      intro m r s hs
      simp only [Term.rename]
      obtain ⟨g, tg, hg⟩ := ihf r s hs
      obtain ⟨b, tb, hb⟩ := iha r s hs
      refine ⟨_, .app tg tb, ?_⟩
      intro q x v
      apply PRA.QFProof.eq_trans_rule (term_app_apply g b x v)
      apply PRA.QFProof.eq_trans_rule (hg _ v)
      apply PRA.QFProof.eq_trans_rule (PRA.QFProof.app_congr ?_)
      · exact PRA.QFProof.eq_symm_rule (term_app_apply _ _ x _)
      · intro i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · refine Fin.cases (hb Fin.elim0 v) (fun _ => .eq_refl) i
        · simp only [Fin.addCases_right]
          exact .eq_refl
  | letE value body ihv ihb =>
      intro m r s hs
      simp only [Term.rename]
      obtain ⟨g, tg, hg⟩ := ihv r s hs
      obtain ⟨b, tb, hb⟩ := ihb r s hs
      rw [rename_subst0] at tb
      exact ⟨b, .letE tg tb, hb⟩
  | primrec base step ihb ihs =>
      intro m r s hs
      simp only [Term.rename]
      obtain ⟨b, tb, hb⟩ := ihb r s hs
      obtain ⟨g, tg, hg⟩ := ihs r s hs
      refine ⟨_, .primrec tb tg, ?_⟩
      intro q x v
      apply PRA.QFProof.eq_trans_rule (recursor_apply _ _ _ _)
      apply PRA.QFProof.eq_trans_rule (recursion_congr_apply
        (Fin.addCases Fin.elim0 v) (Fin.addCases Fin.elim0 (fun i => v (s i)))
        (hb Fin.elim0 v) ?_ _)
      · exact PRA.QFProof.eq_symm_rule (recursor_apply _ _ _ _)
      · simp only [addCases_shift]
        apply PRA.QFProof.eq_trans_rule (recursion_step_apply g _ _ _)
        apply PRA.QFProof.eq_trans_rule (hg _ (fun i => (v i).shift.shift))
        exact PRA.QFProof.eq_symm_rule (recursion_step_apply _ _ _ _)
  | definition lookup arguments body iha ihb =>
      intro m r s hs
      simp only [Term.rename]
      obtain ⟨g, tg, hg⟩ := ihb r s hs
      obtain ⟨F, formed⟩ := declaration_origin valid lookup
      cases formed with
      | function typed =>
          rw [typed.instantiate_rename] at tg
          exact ⟨g, .definition lookup (iha r s hs) tg, hg⟩
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i m r s hs
      obtain ⟨g, tg, hg⟩ := ihh r s hs
      exact .cons tg (iht r s hs)

private theorem app_shift (f : Primrec k) (v : Fin k → PRA.Term n) :
    (PRA.Term.app f v).shift = .app f (fun i => (v i).shift) := rfl

private theorem term_translation_subst {E Ξ ρ n t k f} (valid : EnvironmentWF E)
    (translation : TermTranslation E Ξ ρ n t k f) :
    ∀ {m} (r : Subst) (s : Fin n → Primrec (0 + m)),
      (∀ i, TermTranslation E Ξ ρ m (r i.val) 0 (s i)) →
      ∃ g, TermTranslation E Ξ ρ m (t.subst r) k g ∧
        ∀ {q} (x : Fin k → PRA.Term q) (v : Fin m → PRA.Term q),
          PRA.QFProof (.eq (.app g (Fin.addCases x v))
            (.app f (Fin.addCases x (fun i => .app (s i) (Fin.addCases Fin.elim0 v))))) := by
  induction translation using TermTranslation.rec
    (motive_2 := fun n fs ks _ => ∀ {m} (r : Subst) (s : Fin n → Primrec (0 + m)),
      (∀ i, TermTranslation E Ξ ρ m (r i.val) 0 (s i)) →
        FunctionArgumentsTranslation E Ξ ρ m (fs.map (Term.subst r)) ks) with
  | bvar i =>
      intro m r s hs
      simp only [Term.subst]
      refine ⟨s i, hs i, ?_⟩
      intro q x v
      have hx : x = Fin.elim0 := by funext i; exact Fin.elim0 i
      subst x
      exact PRA.QFProof.eq_symm_rule (by
        simpa only [Fin.addCases_right] using
          (PRA.QFProof.app_proj (i := i.natAdd 0)
            (v := Fin.addCases Fin.elim0
              (fun i => PRA.Term.app (s i) (Fin.addCases Fin.elim0 v)))))
  | zero =>
      intro m r s hs
      simp only [Term.subst]
      refine ⟨_, .zero, ?_⟩
      intro q x v
      apply PRA.QFProof.eq_trans_rule .app_comp
      apply PRA.QFProof.eq_trans_rule (PRA.QFProof.app_congr (fun i => Fin.elim0 i))
      exact PRA.QFProof.eq_symm_rule .app_comp
  | succ =>
      intro m r s hs
      simp only [Term.subst]
      refine ⟨_, .succ, ?_⟩
      intro q x v
      exact PRA.QFProof.eq_trans_rule (reindex_arguments _ x v)
        (PRA.QFProof.eq_symm_rule (reindex_arguments _ x _))
  | parameter lookup =>
      intro m r s hs
      simp only [Term.subst]
      refine ⟨_, .parameter lookup, ?_⟩
      intro q x v
      exact PRA.QFProof.eq_trans_rule (reindex_arguments _ x v)
        (PRA.QFProof.eq_symm_rule (reindex_arguments _ x _))
  | @lam n t k f name body ih =>
      intro m r s hs
      simp only [Term.subst]
      have shifted := fun i => term_translation_rename valid (hs i)
        (fun j => j + 1) Fin.succ (fun _ => rfl)
      classical
      let g := fun i => (shifted i).choose
      have tg := fun i => (shifted i).choose_spec.1
      have hg := fun i => @(shifted i).choose_spec.2
      let u : Fin (n + 1) → Primrec (0 + (m + 1)) :=
        Fin.cases (.proj ((0 : Fin (m + 1)).natAdd 0)) g
      have tu : ∀ i, TermTranslation E Ξ ρ (m + 1) (Subst.lift 1 r i.val) 0 (u i) := by
        intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · simpa [Subst.lift, u] using (TermTranslation.bvar (E := E) (Ξ := Ξ) (ρ := ρ)
            (0 : Fin (m + 1)))
        · simpa [Subst.lift, u, Term.shift] using tg i
      obtain ⟨b, tb, hb⟩ := ih (Subst.lift 1 r) u tu
      refine ⟨_, .lam tb, ?_⟩
      intro q x v
      apply PRA.QFProof.eq_trans_rule (by
        simpa only [cases_eta] using term_lam_apply b (x 0) (fun i => x i.succ) v)
      apply PRA.QFProof.eq_trans_rule (hb _ _)
      apply PRA.QFProof.eq_trans_rule (PRA.QFProof.app_congr ?_)
      · exact PRA.QFProof.eq_symm_rule (by
          simpa only [cases_eta] using term_lam_apply f (x 0) (fun i => x i.succ)
            (fun i => PRA.Term.app (s i) (Fin.addCases Fin.elim0 v)))
      · intro i
        refine Fin.addCases (fun _ => by simp only [Fin.addCases_left]; exact .eq_refl)
          (fun i => ?_) i
        simp only [Fin.addCases_right]
        refine Fin.cases ?_ (fun i => ?_) i
        · simpa only [u, Fin.cases_zero, Fin.addCases_right] using
            (PRA.QFProof.app_proj (i := (0 : Fin (m + 1)).natAdd 0)
              (v := Fin.addCases Fin.elim0 (Fin.cases (x 0) v)))
        · simpa only [u, Fin.cases_succ] using hg i Fin.elim0 (Fin.cases (x 0) v)
  | app function argument ihf iha =>
      intro m r s hs
      simp only [Term.subst]
      obtain ⟨g, tg, hg⟩ := ihf r s hs
      obtain ⟨b, tb, hb⟩ := iha r s hs
      refine ⟨_, .app tg tb, ?_⟩
      intro q x v
      apply PRA.QFProof.eq_trans_rule (term_app_apply g b x v)
      apply PRA.QFProof.eq_trans_rule (hg _ v)
      apply PRA.QFProof.eq_trans_rule (PRA.QFProof.app_congr ?_)
      · exact PRA.QFProof.eq_symm_rule (term_app_apply _ _ x _)
      · intro i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · refine Fin.cases (hb Fin.elim0 v) (fun _ => .eq_refl) i
        · simp only [Fin.addCases_right]
          exact .eq_refl
  | letE value body ihv ihb =>
      intro m r s hs
      simp only [Term.subst]
      obtain ⟨g, tg, hg⟩ := ihv r s hs
      obtain ⟨b, tb, hb⟩ := ihb r s hs
      rw [Term.subst_subst0] at tb
      exact ⟨b, .letE tg tb, hb⟩
  | primrec base step ihb ihs =>
      intro m r s hs
      simp only [Term.subst]
      obtain ⟨b, tb, hb⟩ := ihb r s hs
      obtain ⟨g, tg, hg⟩ := ihs r s hs
      refine ⟨_, .primrec tb tg, ?_⟩
      intro q x v
      apply PRA.QFProof.eq_trans_rule (recursor_apply _ _ _ _)
      apply PRA.QFProof.eq_trans_rule (recursion_congr_apply
        (Fin.addCases Fin.elim0 v)
        (Fin.addCases Fin.elim0 (fun i => .app (s i) (Fin.addCases Fin.elim0 v)))
        (hb Fin.elim0 v) ?_ _)
      · exact PRA.QFProof.eq_symm_rule (recursor_apply _ _ _ _)
      · simp only [app_shift, addCases_shift]
        apply PRA.QFProof.eq_trans_rule (recursion_step_apply g _ _ _)
        apply PRA.QFProof.eq_trans_rule (hg _ (fun i => (v i).shift.shift))
        exact PRA.QFProof.eq_symm_rule (recursion_step_apply _ _ _ _)
  | definition lookup arguments body iha ihb =>
      intro m r s hs
      simp only [Term.subst]
      obtain ⟨g, tg, hg⟩ := ihb r s hs
      obtain ⟨F, formed⟩ := declaration_origin valid lookup
      cases formed with
      | function typed =>
          rw [typed.instantiate_subst] at tg
          exact ⟨g, .definition lookup (iha r s hs) tg, hg⟩
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i m r s hs
      obtain ⟨g, tg, hg⟩ := ihh r s hs
      exact .cons tg (iht r s hs)

private theorem translate_termRefl {E Ξ ρ n t k f g}
    (left : TermTranslation E Ξ ρ n t k f) (right : TermTranslation E Ξ ρ n t k g) :
    PRA.Proof (.eq (.app f PRA.Term.var) (.app g PRA.Term.var)) := by
  cases term_translation_unique left right
  exact .eq_refl

private theorem translate_termZeta {E Ξ ρ n name t u k f g}
    (left : TermTranslation E Ξ ρ n (.letE name t u) k f)
    (right : TermTranslation E Ξ ρ n (u.subst0 t) k g) :
    PRA.Proof (.eq (.app f PRA.Term.var) (.app g PRA.Term.var)) := by
  cases left with
  | letE value body => exact translate_termRefl body right

private theorem translate_termDelta {E Ξ ρ n name fs d f g}
    (lookup : E[name]? = some (.function d))
    (left : TermTranslation E Ξ ρ n (.definition name fs) d.arity f)
    (right : TermTranslation E Ξ ρ n (d.body.instantiate fs) d.arity g) :
    PRA.Proof (.eq (.app f PRA.Term.var) (.app g PRA.Term.var)) := by
  obtain ⟨e, he, h, body, heq⟩ := term_translation_definition left rfl
  cases Declaration.function.inj (Option.some.inj (lookup.symm.trans he))
  cases eq_of_heq heq
  exact translate_termRefl body right

private def zeroFunction : Arity → Term
  | 0 => .zero
  | k + 1 => .lam .anonymous (zeroFunction k)

private theorem zeroFunction_typed (k : Arity) : TermTyping E Ξ Γ (zeroFunction k) k := by
  induction k generalizing Γ with
  | zero => exact .zero
  | succ k ih => exact .lam ih

private theorem typing_of_shift {E Ξ Γ t k j}
    (h : TermTyping E Ξ (j :: Γ) t.shift k) : TermTyping E Ξ Γ t k := by
  simpa only [Term.subst0_shift] using h.subst0 (zeroFunction_typed j)

private theorem reflect_lift {E Ξ Γ Δ s}
    (reflect : ∀ i k, TermTyping E Ξ Δ (s i) k → Γ[i]? = some k) (j : Arity) :
    ∀ i k, TermTyping E Ξ (j :: Δ) (Subst.lift 1 s i) k → (j :: Γ)[i]? = some k := by
  intro i k h
  cases i with
  | zero => exact h.inv_bvar
  | succ i =>
      apply reflect i k
      apply typing_of_shift (j := j)
      simpa [Subst.lift] using h

-- Reflection recovers the declared arity of each local from the type of its replacement.
private theorem typing_of_subst (t : Term) {E Ξ Γ Δ s k}
    (reflect : ∀ i j, TermTyping E Ξ Δ (s i) j → Γ[i]? = some j)
    (h : TermTyping E Ξ Δ (t.subst s) k) : TermTyping E Ξ Γ t k := by
  induction t using Term.rec
    (motive_2 := fun ts => ∀ {Γ Δ s ks},
      (∀ i j, TermTyping E Ξ Δ (s i) j → Γ[i]? = some j) →
      FunctionArguments E Ξ Δ (ts.map (Term.subst s)) ks → FunctionArguments E Ξ Γ ts ks)
    generalizing Γ Δ s k with
  | bvar i => simp only [Term.subst] at h; exact .bvar (reflect i k h)
  | parameter i => simp only [Term.subst] at h; exact .parameter h.inv_parameter
  | zero => simp only [Term.subst] at h; have := h.inv_zero; subst k; exact .zero
  | succ => simp only [Term.subst] at h; have := h.inv_succ; subst k; exact .succ
  | lam name t ih =>
      simp only [Term.subst] at h
      obtain ⟨k, rfl, body⟩ := h.inv_lam
      exact .lam (ih (reflect_lift reflect 0) body)
  | app t u iht ihu =>
      simp only [Term.subst] at h
      exact .app (iht reflect h.inv_app.1) (ihu reflect h.inv_app.2)
  | letE name t u iht ihu =>
      simp only [Term.subst] at h
      obtain ⟨j, value, body⟩ := h.inv_let
      exact .letE (iht reflect value) (ihu (reflect_lift reflect j) body)
  | primrec b step ihb ihs =>
      simp only [Term.subst] at h
      obtain ⟨rfl, base, step⟩ := h.inv_primrec
      exact .primrec (ihb reflect base) (ihs reflect step)
  | definition name ts ih =>
      simp only [Term.subst] at h
      obtain ⟨d, lookup, arguments, rfl⟩ := h.inv_definition
      exact .definition lookup (ih reflect arguments)
  | nil => rename_i Γ Δ s ks reflect h; cases h; exact .nil
  | cons t ts iht ihts =>
      rename_i Γ Δ s ks reflect h
      cases h with
      | cons head tail => exact .cons (iht reflect head) (ihts reflect tail)

private theorem typing_of_subst0 {E Ξ Γ t u j k}
    (value : TermTyping E Ξ Γ t j) (body : TermTyping E Ξ Γ (u.subst0 t) k) :
    TermTyping E Ξ (j :: Γ) u k := by
  apply typing_of_subst u (s := fun | 0 => t | i + 1 => .bvar i) _ body
  intro i a h
  cases i with
  | zero => simp only [List.getElem?_cons_zero, value.unique h]
  | succ i => exact h.inv_bvar

private theorem term_translation_typed {E Ξ ρ n t k f}
    (h : TermTranslation E Ξ ρ n t k f) : TermTyping E Ξ (List.replicate n 0) t k := by
  induction h using TermTranslation.rec
    (motive_2 := fun n fs ks _ => FunctionArguments E Ξ (List.replicate n 0) fs ks) with
  | bvar i => exact .bvar (by simp [i.isLt])
  | zero => exact .zero
  | succ => exact .succ
  | parameter lookup => exact .parameter lookup
  | lam body ih => exact .lam (by simpa only [List.replicate_succ] using ih)
  | app function argument ihf iha => exact .app ihf iha
  | letE value body ihv ihb => exact .letE ihv (typing_of_subst0 ihv ihb)
  | primrec base step ihb ihs => exact .primrec ihb ihs
  | definition lookup arguments body iha ihb => exact .definition lookup iha
  | nil => exact .nil
  | cons head tail ihh iht => exact .cons ihh iht

private theorem functions_translation_typed {E Ξ ρ n ts ks}
    (h : FunctionArgumentsTranslation E Ξ ρ n ts ks) :
    FunctionArguments E Ξ (List.replicate n 0) ts ks := by
  induction h using FunctionArgumentsTranslation.rec (motive_1 := fun _ _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail _ ih => exact .cons (term_translation_typed head) ih
  all_goals trivial

private theorem signature_subtyping {σ : PredicateSignature} {s}
    (h : σ.sort = .qf ∨ σ.sort = s) : PredicateSubtyping σ ⟨σ.arity, s⟩ := by
  rcases σ with ⟨k, sort⟩
  cases sort <;> cases s <;> simp_all
  all_goals first | exact .refl | exact .lift

private theorem predicate_translation_typed {E Ξ ρ π n P σ A}
    (h : PredicateTranslation E Ξ ρ π n P σ A) :
    PredicateTyping E Ξ (List.replicate n 0) P σ := by
  induction h using PredicateTranslation.rec
    (motive_2 := fun n ps signatures _ =>
      PredicateArguments E Ξ (List.replicate n 0) ps signatures) with
  | false => exact .subsumption .false (signature_subtyping (.inl rfl))
  | true => exact .subsumption .true (signature_subtyping (.inl rfl))
  | equal left right =>
      exact .subsumption (.equal (term_translation_typed left) (term_translation_typed right))
        (signature_subtyping (.inl rfl))
  | imp _ _ ihP ihQ => exact .imp ihP ihQ
  | and _ _ ihP ihQ => exact .and ihP ihQ
  | or _ _ ihP ihQ => exact .or ihP ihQ
  | all _ ih => exact .all ih
  | ex _ ih => exact .ex ih
  | parameter lookup sort => exact .subsumption (.parameter lookup) (signature_subtyping sort)
  | lam _ ih => exact .lam (by simpa only [List.replicate_succ] using ih)
  | app _ argument ih => exact .app ih (term_translation_typed argument)
  | letTerm value _ ih => exact .letTerm (term_translation_typed value) ih
  | letPredicate _ _ ihv ihb => exact .letPredicate ihv ihb
  | definition lookup functions _ _ sort ihp _ =>
      exact .subsumption (.definition lookup (functions_translation_typed functions) ihp)
        (signature_subtyping sort)
  | nil => exact .nil
  | cons _ _ ihh iht => exact .cons ihh iht

-- Existence under every local renaming lets a captured expression move under fresh binders.
private def TermTranslates (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (n : Nat) (t : Term) (k : Arity) : Prop :=
  ∀ m r, (∀ i, i < n → r i < m) → ∃ f, TermTranslation E Ξ ρ m (t.rename r) k f

private def TranslatesBindings (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (n : Nat) (ks : List Arity) (s : Subst) : Prop :=
  ∀ i k, ks[i]? = some k → TermTranslates E Ξ ρ n (s i) k

private theorem term_translates_here {E Ξ ρ n t k} (h : TermTranslates E Ξ ρ n t k) :
    ∃ f, TermTranslation E Ξ ρ n t k f := by
  simpa only [Term.rename_id] using h n id (fun _ hi => hi)

private theorem term_translates_rename {E Ξ ρ n t k} (h : TermTranslates E Ξ ρ n t k)
    {m} (r : Renaming) (hr : ∀ i, i < n → r i < m) : TermTranslates E Ξ ρ m (t.rename r) k := by
  intro l s hs
  simpa only [Term.rename_comp] using h l (fun i => s (r i)) (fun i hi => hs _ (hr i hi))

private theorem term_translates_shift {E Ξ ρ n t k} (h : TermTranslates E Ξ ρ n t k) :
    TermTranslates E Ξ ρ (n + 1) t.shift k := by
  simpa only [Term.shift, Nat.not_lt_zero, ↓reduceIte] using
    term_translates_rename h (fun i => i + 1) (fun i hi => Nat.succ_lt_succ hi)

private theorem term_translates_bvar {E Ξ ρ n i} (hi : i < n) :
    TermTranslates E Ξ ρ n (.bvar i) 0 := by
  intro m r hr
  have bound := hr i hi
  haveI : NeZero m := ⟨by omega⟩
  have eq : (Fin.ofNat m (r i)).val = r i := Nat.mod_eq_of_lt bound
  refine ⟨.proj ((Fin.ofNat m (r i)).natAdd 0), ?_⟩
  simpa only [Term.rename, eq] using
    (TermTranslation.bvar (E := E) (Ξ := Ξ) (ρ := ρ) (Fin.ofNat m (r i)))

private theorem bindings_rename {E Ξ ρ n ks s}
    (h : TranslatesBindings E Ξ ρ n ks s) {m} (r : Renaming) (hr : ∀ i, i < n → r i < m) :
    TranslatesBindings E Ξ ρ m ks (fun i => (s i).rename r) :=
  fun i k hi => term_translates_rename (h i k hi) r hr

private theorem bindings_shift {E Ξ ρ n ks s} (h : TranslatesBindings E Ξ ρ n ks s) :
    TranslatesBindings E Ξ ρ (n + 1) ks (fun i => (s i).shift) :=
  fun i k hi => term_translates_shift (h i k hi)

private theorem bindings_lift {E Ξ ρ n ks s} (h : TranslatesBindings E Ξ ρ n ks s) :
    TranslatesBindings E Ξ ρ (n + 1) (0 :: ks) (Subst.lift 1 s) := by
  intro i k hi
  cases i with
  | zero =>
      have hk : k = 0 := (Option.some.inj hi).symm
      subst k
      exact term_translates_bvar (Nat.zero_lt_succ n)
  | succ i => simpa [Subst.lift] using term_translates_shift (h i k hi)

private inductive TranslatesArguments (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (n : Nat) : List Term → List Arity → Prop where
  | nil : TranslatesArguments E Ξ ρ n [] []
  | cons (head : TermTranslates E Ξ ρ n t k) (tail : TranslatesArguments E Ξ ρ n ts ks) :
      TranslatesArguments E Ξ ρ n (t :: ts) (k :: ks)

-- Stored bodies use their preceding environment; actuals may use the larger caller environment.
private def FunctionsTranslate (E F : Environment) : Prop :=
  ∀ name d, E[name]? = some (.function d) →
    ∀ Ξ (ρ : FunctionAssignment Ξ.functions) n fs,
      TranslatesArguments F Ξ ρ n fs d.functions →
        TermTranslates F Ξ ρ n (.definition name fs) d.arity

private theorem term_translates {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k)
    {F} (functions : FunctionsTranslate E F) {Ω} {ρ : FunctionAssignment Ω.functions}
    {n s p} (locals : TranslatesBindings F Ω ρ n Γ s)
    (parameters : TranslatesBindings F Ω ρ n Ξ.functions p) :
    TermTranslates F Ω ρ n (t.replace s p) k := by
  induction h using TermTyping.rec
    (motive_2 := fun Γ fs ks _ => ∀ {n s p},
      TranslatesBindings F Ω ρ n Γ s → TranslatesBindings F Ω ρ n Ξ.functions p →
      TranslatesArguments F Ω ρ n (fs.map (Term.replace s p)) ks)
    generalizing n s p with
  | bvar lookup => simpa only [Term.replace] using locals _ _ lookup
  | parameter lookup => simpa only [Term.replace] using parameters _ _ lookup
  | zero =>
      intro m r hr
      simp only [Term.replace, Term.rename]
      exact ⟨_, .zero⟩
  | succ =>
      intro m r hr
      simp only [Term.replace, Term.rename]
      exact ⟨_, .succ⟩
  | lam body ih =>
      intro m r hr
      rw [Term.replace_rename]
      simp only [Term.replace]
      obtain ⟨f, hf⟩ := term_translates_here
        (ih (bindings_lift (bindings_rename locals r hr))
          (bindings_shift (bindings_rename parameters r hr)))
      exact ⟨_, .lam hf⟩
  | app function argument ihf iha =>
      intro m r hr
      obtain ⟨f, hf⟩ := ihf locals parameters m r hr
      obtain ⟨a, ha⟩ := iha locals parameters m r hr
      simp only [Term.replace, Term.rename]
      exact ⟨_, .app hf ha⟩
  | letE value body ihv ihb =>
      intro m r hr
      rw [Term.replace_rename]
      simp only [Term.replace]
      have hl := bindings_rename locals r hr
      have hp := bindings_rename parameters r hr
      have hv := ihv hl hp
      obtain ⟨g, hg⟩ := term_translates_here hv
      refine ⟨_, by
        apply TermTranslation.letE hg
        rw [Term.replace_beta]
        apply (term_translates_here (ihb ?_ hp)).choose_spec
        intro i a hi
        cases i with
        | zero => cases Option.some.inj hi; exact hv
        | succ i => exact hl i a hi⟩
  | primrec base step ihb ihs =>
      intro m r hr
      obtain ⟨b, hb⟩ := ihb locals parameters m r hr
      obtain ⟨s, hs⟩ := ihs locals parameters m r hr
      simp only [Term.replace, Term.rename]
      exact ⟨_, .primrec hb hs⟩
  | definition lookup arguments ih =>
      simpa only [Term.replace] using functions _ _ lookup Ω ρ n _ (ih locals parameters)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i n s p locals parameters
      exact .cons (ihh locals parameters) (iht locals parameters)

private theorem arguments_translation {E Ξ ρ n ts ks}
    (h : TranslatesArguments E Ξ ρ n ts ks) {m} (r : Renaming)
    (hr : ∀ i, i < n → r i < m) :
    FunctionArgumentsTranslation E Ξ ρ m (ts.map (Term.rename r)) ks := by
  induction h with
  | nil => exact .nil
  | cons head tail ih =>
      obtain ⟨f, hf⟩ := head m r hr
      exact .cons hf ih

private theorem arguments_lookup {E Ξ ρ n ts ks}
    (h : TranslatesArguments E Ξ ρ n ts ks) {i : Nat} {k : Arity} (hi : ks[i]? = some k) :
    ∃ t, ts[i]? = some t ∧ TermTranslates E Ξ ρ n t k := by
  induction h generalizing i with
  | nil => simp at hi
  | cons head tail ih =>
      cases i with
      | zero => cases Option.some.inj hi; exact ⟨_, rfl, head⟩
      | succ i => exact ih hi

private theorem arguments_bindings {E Ξ ρ n ts ks}
    (h : TranslatesArguments E Ξ ρ n ts ks) :
    TranslatesBindings E Ξ ρ n ks (fun i => ts[i]?.getD (.parameter i)) := by
  intro i k hi
  obtain ⟨t, ht, htrans⟩ := arguments_lookup h hi
  simpa only [ht, Option.getD_some] using htrans

private theorem reference_translates {E F Ξ ρ n name d fs}
    (lookup : F[name]? = some (.function d))
    (typed : TermTyping E { functions := d.functions } [] d.body d.arity)
    (actuals : TranslatesArguments F Ξ ρ n fs d.functions)
    (body : TermTranslates F Ξ ρ n (d.body.instantiate fs) d.arity) :
    TermTranslates F Ξ ρ n (.definition name fs) d.arity := by
  intro m r hr
  obtain ⟨f, hf⟩ := body m r hr
  rw [typed.instantiate_rename] at hf
  simp only [Term.rename]
  exact ⟨_, .definition lookup (arguments_translation actuals r hr) hf⟩

private theorem functions_translate {E} (valid : EnvironmentWF E) :
    ∀ F, EnvironmentExtends E F → FunctionsTranslate E F := by
  induction valid with
  | empty =>
      intro F ext name d lookup
      simp at lookup
  | @insert E e previous fresh declaration ih =>
      intro F ext name d lookup Ξ ρ n fs actuals
      have older : EnvironmentExtends E F := fun name d lookup =>
        ext name d (EnvironmentExtends.insert fresh name d lookup)
      have hf := ih F older
      by_cases heq : e.name = name
      · have same : e = .function d := by
          simpa only [Std.ExtHashMap.getElem?_insert, heq, beq_self_eq_true, ↓reduceIte,
            Option.some.injEq] using lookup
        subst e
        cases declaration with
        | function typed =>
            have hb := term_translates typed hf
              (s := Term.bvar) (by intro i k hi; simp at hi) (arguments_bindings actuals)
            rw [typed.replace_instantiate fs _ (by intros; rfl)] at hb
            exact reference_translates (ext _ _ lookup) typed actuals hb
      · have old : E[name]? = some (.function d) := by
          simpa [Std.ExtHashMap.getElem?_insert, heq] using lookup
        exact hf name d old Ξ ρ n fs actuals

private theorem locals_translate {E Ξ ρ n} :
    TranslatesBindings E Ξ ρ n (List.replicate n 0) Term.bvar := by
  intro i j hi
  have bound : i < n := by
    by_cases hn : i < n
    · exact hn
    · simp [hn] at hi
  have hj : j = 0 := by simpa [List.getElem?_replicate, bound] using hi.symm
  subst j
  exact term_translates_bvar bound

private theorem parameters_translate {E Ξ ρ n} :
    TranslatesBindings E Ξ ρ n Ξ.functions Term.parameter := by
  intro i j hi m r hr
  simp only [Term.rename]
  exact ⟨_, .parameter hi⟩

private theorem term_translation_exists {E Ξ n t k} (valid : EnvironmentWF E)
    (typed : TermTyping E Ξ (List.replicate n 0) t k) (ρ : FunctionAssignment Ξ.functions) :
    ∃ f, TermTranslation E Ξ ρ n t k f := by
  have functions := functions_translate valid E (fun _ _ h => h)
  have locals := locals_translate (E := E) (Ξ := Ξ) (ρ := ρ) (n := n)
  have parameters := parameters_translate (E := E) (Ξ := Ξ) (ρ := ρ) (n := n)
  have translated := term_translates_here (term_translates typed functions locals parameters)
  simpa only [Term.replace_id] using translated

private theorem sort_toProp (s : FormulaSort) : s = .qf ∨ s = .prop := by
  cases s <;> simp

private theorem translation_toProp {E Ξ ρ π n P σ A}
    (h : PredicateTranslation E Ξ ρ π n P σ A) :
    PredicateTranslation E Ξ ρ π n P ⟨σ.arity, .prop⟩ A := by
  induction h using PredicateTranslation.rec (motive_2 := fun _ _ _ _ => True) with
  | false => exact .false
  | true => exact .true
  | equal left right => exact .equal left right
  | imp _ _ ihP ihQ => exact .imp ihP ihQ
  | and _ _ ihP ihQ => exact .and ihP ihQ
  | or _ _ ihP ihQ => exact .or ihP ihQ
  | all body _ => exact .all body
  | ex body _ => exact .ex body
  | parameter lookup sort =>
      exact .parameter lookup (sort_toProp _)
  | lam _ ih => exact .lam ih
  | app _ argument ih => exact .app ih argument
  | letTerm value _ ih => exact .letTerm value ih
  | letPredicate value _ _ ih => exact .letPredicate value ih
  | definition lookup functions predicates body sort _ _ =>
      exact .definition lookup functions predicates body (sort_toProp _)
  | nil | cons => trivial

private def PredicateTranslates (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates)
    (n : Nat) (P : Predicate) (σ : PredicateSignature) : Prop :=
  ∀ m r, (∀ i, i < n → r i < m) → ∃ A, PredicateTranslation E Ξ ρ π m (P.rename r) σ A

private def TranslatesPredicateBindings (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates)
    (n : Nat) (signatures : List PredicateSignature) (q : Nat → Predicate) : Prop :=
  ∀ i σ, signatures[i]? = some σ → PredicateTranslates E Ξ ρ π n (q i) σ

private theorem predicate_translates_here {E Ξ ρ π n P σ}
    (h : PredicateTranslates E Ξ ρ π n P σ) : ∃ A, PredicateTranslation E Ξ ρ π n P σ A := by
  simpa only [Predicate.rename_id] using h n id (fun _ hi => hi)

private theorem predicate_translates_rename {E Ξ ρ π n P σ}
    (h : PredicateTranslates E Ξ ρ π n P σ) {m}
    (r : Renaming) (hr : ∀ i, i < n → r i < m) :
    PredicateTranslates E Ξ ρ π m (P.rename r) σ := by
  intro l s hs
  simpa only [Predicate.rename_comp] using h l (fun i => s (r i)) (fun i hi => hs _ (hr i hi))

private theorem predicate_translates_shift {E Ξ ρ π n P σ}
    (h : PredicateTranslates E Ξ ρ π n P σ) : PredicateTranslates E Ξ ρ π (n + 1) P.shift σ := by
  simpa only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte] using
    predicate_translates_rename h (fun i => i + 1) (fun i hi => Nat.succ_lt_succ hi)

private theorem predicate_bindings_rename {E Ξ ρ π n signatures q}
    (h : TranslatesPredicateBindings E Ξ ρ π n signatures q)
    {m} (r : Renaming) (hr : ∀ i, i < n → r i < m) :
    TranslatesPredicateBindings E Ξ ρ π m signatures (fun i => (q i).rename r) :=
  fun i σ hi => predicate_translates_rename (h i σ hi) r hr

private theorem predicate_bindings_shift {E Ξ ρ π n signatures q}
    (h : TranslatesPredicateBindings E Ξ ρ π n signatures q) :
    TranslatesPredicateBindings E Ξ ρ π (n + 1) signatures (fun i => (q i).shift) :=
  fun i σ hi => predicate_translates_shift (h i σ hi)

private inductive TranslatesPredicateArguments (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates)
    (n : Nat) : List Predicate → List PredicateSignature → Prop where
  | nil : TranslatesPredicateArguments E Ξ ρ π n [] []
  | cons (head : PredicateTranslates E Ξ ρ π n P σ)
      (tail : TranslatesPredicateArguments E Ξ ρ π n ps signatures) :
      TranslatesPredicateArguments E Ξ ρ π n (P :: ps) (σ :: signatures)

private def PredicatesTranslate (E F : Environment) : Prop :=
  ∀ name d, E[name]? = some (.predicate d) →
    ∀ Ξ (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates) n fs ps,
      TranslatesArguments F Ξ ρ n fs d.functions →
      TranslatesPredicateArguments F Ξ ρ π n ps d.predicates →
        PredicateTranslates F Ξ ρ π n (.definition name fs ps) d.signature

private theorem function_arguments_translate {E Ξ Γ fs ks} (h : FunctionArguments E Ξ Γ fs ks)
    {F} (functions : FunctionsTranslate E F) {Ω} {ρ : FunctionAssignment Ω.functions}
    {n s p} (locals : TranslatesBindings F Ω ρ n Γ s)
    (parameters : TranslatesBindings F Ω ρ n Ξ.functions p) :
    TranslatesArguments F Ω ρ n (fs.map (Term.replace s p)) ks := by
  induction h using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail _ ih =>
    exact .cons (term_translates head functions locals parameters) (ih locals)
  all_goals trivial

private theorem predicate_translates {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ)
    {F} (functions : FunctionsTranslate E F) (predicates : PredicatesTranslate E F)
    {Ω} {ρ : FunctionAssignment Ω.functions} {π : PredicateAssignment Ω.predicates}
    {n s p q} (locals : TranslatesBindings F Ω ρ n Γ s)
    (parameters : TranslatesBindings F Ω ρ n Ξ.functions p)
    (predicateParameters : TranslatesPredicateBindings F Ω ρ π n Ξ.predicates q) :
    PredicateTranslates F Ω ρ π n (P.replace s p q) σ := by
  induction h using PredicateTyping.rec
    (motive_2 := fun Γ ps signatures _ => ∀ {n s p q},
      TranslatesBindings F Ω ρ n Γ s → TranslatesBindings F Ω ρ n Ξ.functions p →
      TranslatesPredicateBindings F Ω ρ π n Ξ.predicates q →
      TranslatesPredicateArguments F Ω ρ π n (ps.map (Predicate.replace s p q)) signatures)
    generalizing n s p q with
  | false =>
      intro m r hr
      simp only [Predicate.replace, Predicate.rename]
      exact ⟨_, .false⟩
  | true =>
      intro m r hr
      simp only [Predicate.replace, Predicate.rename]
      exact ⟨_, .true⟩
  | equal left right =>
      intro m r hr
      obtain ⟨f, hf⟩ := term_translates left functions locals parameters m r hr
      obtain ⟨g, hg⟩ := term_translates right functions locals parameters m r hr
      simp only [Predicate.replace, Predicate.rename]
      exact ⟨_, .equal hf hg⟩
  | imp left right ihP ihQ =>
      intro m r hr
      obtain ⟨A, hA⟩ := ihP locals parameters predicateParameters m r hr
      obtain ⟨B, hB⟩ := ihQ locals parameters predicateParameters m r hr
      simp only [Predicate.replace, Predicate.rename]
      exact ⟨_, .imp hA hB⟩
  | and left right ihP ihQ =>
      intro m r hr
      obtain ⟨A, hA⟩ := ihP locals parameters predicateParameters m r hr
      obtain ⟨B, hB⟩ := ihQ locals parameters predicateParameters m r hr
      simp only [Predicate.replace, Predicate.rename]
      exact ⟨_, .and hA hB⟩
  | or left right ihP ihQ =>
      intro m r hr
      obtain ⟨A, hA⟩ := ihP locals parameters predicateParameters m r hr
      obtain ⟨B, hB⟩ := ihQ locals parameters predicateParameters m r hr
      simp only [Predicate.replace, Predicate.rename]
      exact ⟨_, .or hA hB⟩
  | all body ih =>
      intro m r hr
      obtain ⟨A, hA⟩ := ih locals parameters predicateParameters m r hr
      simp only [Predicate.replace, Predicate.rename]
      exact ⟨_, .all hA⟩
  | ex body ih =>
      intro m r hr
      obtain ⟨A, hA⟩ := ih locals parameters predicateParameters m r hr
      simp only [Predicate.replace, Predicate.rename]
      exact ⟨_, .ex hA⟩
  | parameter lookup => simpa only [Predicate.replace] using predicateParameters _ _ lookup
  | lam body ih =>
      intro m r hr
      rw [Predicate.replace_rename]
      simp only [Predicate.replace]
      obtain ⟨A, hA⟩ := predicate_translates_here
        (ih (bindings_lift (bindings_rename locals r hr))
          (bindings_shift (bindings_rename parameters r hr))
          (predicate_bindings_shift (predicate_bindings_rename predicateParameters r hr)))
      exact ⟨_, .lam hA⟩
  | app function argument ih =>
      intro m r hr
      obtain ⟨A, hA⟩ := ih locals parameters predicateParameters m r hr
      obtain ⟨f, hf⟩ := term_translates argument functions locals parameters m r hr
      simp only [Predicate.replace, Predicate.rename]
      exact ⟨_, .app hA hf⟩
  | letTerm value body ih =>
      intro m r hr
      obtain ⟨f, hf⟩ := term_translates value functions locals parameters m r hr
      obtain ⟨A, hA⟩ := ih locals parameters predicateParameters m r hr
      simp only [Predicate.replace, Predicate.rename]
      exact ⟨_, .letTerm hf hA⟩
  | letPredicate value body ihv ihb =>
      intro m r hr
      obtain ⟨B, hB⟩ := ihv locals parameters predicateParameters m r hr
      obtain ⟨A, hA⟩ := ihb locals parameters predicateParameters m r hr
      simp only [Predicate.replace, Predicate.rename]
      exact ⟨_, .letPredicate hB hA⟩
  | definition lookup fs ps ih =>
      simpa only [Predicate.replace] using predicates _ _ lookup Ω ρ π n _ _
        (function_arguments_translate fs functions locals parameters)
        (ih locals parameters predicateParameters)
  | subsumption typing sub ih =>
      cases sub with
      | refl => exact ih locals parameters predicateParameters
      | lift =>
          intro m r hr
          obtain ⟨A, hA⟩ := ih locals parameters predicateParameters m r hr
          exact ⟨A, translation_toProp hA⟩
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i n s p q locals parameters predicateParameters
      exact .cons (ihh locals parameters predicateParameters)
        (iht locals parameters predicateParameters)

private theorem predicates_arguments_translation {E Ξ ρ π n ps signatures}
    (h : TranslatesPredicateArguments E Ξ ρ π n ps signatures) {m} (r : Renaming)
    (hr : ∀ i, i < n → r i < m) :
    PredicateArgumentsTranslation E Ξ ρ π m (ps.map (Predicate.rename r)) signatures := by
  induction h with
  | nil => exact .nil
  | cons head tail ih =>
      obtain ⟨A, hA⟩ := head m r hr
      exact .cons hA ih

private theorem predicates_arguments_lookup {E Ξ ρ π n ps signatures}
    (h : TranslatesPredicateArguments E Ξ ρ π n ps signatures)
    {i : Nat} {σ : PredicateSignature} (hi : signatures[i]? = some σ) :
    ∃ P, ps[i]? = some P ∧ PredicateTranslates E Ξ ρ π n P σ := by
  induction h generalizing i with
  | nil => simp at hi
  | cons head tail ih =>
      cases i with
      | zero => cases Option.some.inj hi; exact ⟨_, rfl, head⟩
      | succ i => exact ih hi

private theorem predicates_arguments_bindings {E Ξ ρ π n ps signatures}
    (h : TranslatesPredicateArguments E Ξ ρ π n ps signatures) :
    TranslatesPredicateBindings E Ξ ρ π n signatures (fun i => ps[i]?.getD (.parameter i)) := by
  intro i σ hi
  obtain ⟨P, hP, htrans⟩ := predicates_arguments_lookup h hi
  simpa only [hP, Option.getD_some] using htrans

private theorem predicate_reference_translates {E F Ξ ρ π n name d fs ps}
    (lookup : F[name]? = some (.predicate d))
    (typed : PredicateTyping E { functions := d.functions, predicates := d.predicates }
      [] d.body d.signature)
    (functions : TranslatesArguments F Ξ ρ n fs d.functions)
    (predicates : TranslatesPredicateArguments F Ξ ρ π n ps d.predicates)
    (body : PredicateTranslates F Ξ ρ π n (d.body.instantiate fs ps) d.signature) :
    PredicateTranslates F Ξ ρ π n (.definition name fs ps) d.signature := by
  intro m r hr
  obtain ⟨A, hA⟩ := body m r hr
  rw [typed.instantiate_rename] at hA
  simp only [Predicate.rename]
  exact ⟨_, .definition lookup (arguments_translation functions r hr)
    (predicates_arguments_translation predicates r hr) hA (.inr rfl)⟩

private theorem predicates_translate {E} (valid : EnvironmentWF E) :
    ∀ F, EnvironmentExtends E F → PredicatesTranslate E F := by
  induction valid with
  | empty =>
      intro F ext name d lookup
      simp at lookup
  | @insert E e previous fresh declaration ih =>
      intro F ext name d lookup Ξ ρ π n fs ps actuals predicateActuals
      have older : EnvironmentExtends E F := fun name d lookup =>
        ext name d (EnvironmentExtends.insert fresh name d lookup)
      have hf := functions_translate previous F older
      have hp := ih F older
      by_cases heq : e.name = name
      · have same : e = .predicate d := by
          simpa only [Std.ExtHashMap.getElem?_insert, heq, beq_self_eq_true, ↓reduceIte,
            Option.some.injEq] using lookup
        subst e
        cases declaration with
        | predicate typed =>
            have hb := predicate_translates typed hf hp
              (s := Term.bvar) (by intro i k hi; simp at hi) (arguments_bindings actuals)
              (predicates_arguments_bindings predicateActuals)
            rw [typed.replace_instantiate fs ps _ _ (by intros; rfl) (by intros; rfl)] at hb
            exact predicate_reference_translates (ext _ _ lookup) typed actuals predicateActuals hb
      · have old : E[name]? = some (.predicate d) := by
          simpa [Std.ExtHashMap.getElem?_insert, heq] using lookup
        exact hp name d old Ξ ρ π n fs ps actuals predicateActuals

private theorem predicate_translation_exists {E Ξ n P σ} (valid : EnvironmentWF E)
    (typed : PredicateTyping E Ξ (List.replicate n 0) P σ)
    (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates) :
    ∃ A, PredicateTranslation E Ξ ρ π n P σ A := by
  have functions := functions_translate valid E (fun _ _ h => h)
  have predicates := predicates_translate valid E (fun _ _ h => h)
  have locals := locals_translate (E := E) (Ξ := Ξ) (ρ := ρ) (n := n)
  have parameters := parameters_translate (E := E) (Ξ := Ξ) (ρ := ρ) (n := n)
  have predicateParameters :
      TranslatesPredicateBindings E Ξ ρ π n Ξ.predicates Predicate.parameter := by
    intro i σ hi m r hr
    simp only [Predicate.rename]
    exact ⟨_, .parameter hi (.inr rfl)⟩
  have translated := predicate_translates_here
    (predicate_translates typed functions predicates locals parameters predicateParameters)
  simpa only [Predicate.replace_id] using translated

private theorem translation_qf {E Ξ ρ π n P σ A}
    (h : PredicateTranslation E Ξ ρ π n P σ A) : σ.sort = .qf → A.QuantifierFree := by
  induction h using PredicateTranslation.rec (motive_2 := fun _ _ _ _ => True) with
  | false => intro _; trivial
  | true => intro _; exact ⟨True.intro, True.intro⟩
  | equal => intro _; trivial
  | imp _ _ ihP ihQ | and _ _ ihP ihQ | or _ _ ihP ihQ =>
      intro hs
      exact ⟨ihP hs, ihQ hs⟩
  | all | ex => intro hs; cases hs
  | parameter lookup sort =>
      intro hs
      apply (PRA.Formula.quantifierFree_subst _ _).mpr
      exact (π _ _ lookup).property (sort.elim id (fun h => h.trans hs))
  | lam _ ih | app _ _ ih =>
      intro hs
      exact (PRA.Formula.quantifierFree_subst _ _).mpr (ih hs)
  | letTerm _ _ ih => exact ih
  | letPredicate _ _ _ ih => exact ih
  | definition _ _ _ _ sort _ ih =>
      intro hs
      exact ih (sort.elim id (fun h => h.trans hs))
  | nil | cons => trivial

private def ProvableTranslation (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates)
    (n : Nat) (H : List (PRA.Formula (0 + n))) (P : Predicate) : Prop :=
  ∃ A, PredicateTranslation E Ξ ρ π n P ⟨0, .prop⟩ A ∧ Target.Entails H A

private theorem provable_translation_weaken {E Ξ ρ π n H P A}
    (h : ProvableTranslation E Ξ ρ π n H P) : ProvableTranslation E Ξ ρ π n (A :: H) P := by
  obtain ⟨B, translation, proof⟩ := h
  exact ⟨B, translation, Target.entails_cons proof⟩

private theorem provable_translation_at {E Ξ ρ π n H P A}
    (h : ProvableTranslation E Ξ ρ π n H P)
    (translation : PredicateTranslation E Ξ ρ π n P ⟨0, .prop⟩ A) : Target.Entails H A := by
  obtain ⟨B, other, proof⟩ := h
  cases predicate_translation_unique other translation
  exact proof

private theorem entails_iff_forward {H : List (PRA.Formula n)} {A B}
    (h : PRA.Proof (A.iff B)) (ha : Target.Entails H A) : Target.Entails H B :=
  Target.entails_mp (Target.entails_of_proof (.mp .and_left h)) ha

private theorem entails_iff_backward {H : List (PRA.Formula n)} {A B}
    (h : PRA.Proof (A.iff B)) (hb : Target.Entails H B) : Target.Entails H A :=
  Target.entails_mp (Target.entails_of_proof (.mp .and_right h)) hb

private theorem formula_iff_subst (A : PRA.Formula m) {v w : Fin m → PRA.Term n}
    (equal : ∀ i, PRA.Proof (.eq (v i) (w i))) :
    PRA.Proof ((A.subst v).iff (A.subst w)) :=
  .mp (.mp .and_intro (Target.formula_congr A equal))
    (Target.formula_congr A (fun i => Target.eq_symm_rule (equal i)))

private theorem formula_iff_trans {A B C : PRA.Formula n}
    (left : PRA.Proof (A.iff B)) (right : PRA.Proof (B.iff C)) : PRA.Proof (A.iff C) :=
  .mp (.mp .and_intro
    (Target.imp_trans_rule (.mp .and_left left) (.mp .and_left right)))
    (Target.imp_trans_rule (.mp .and_right right) (.mp .and_right left))

private theorem instance_iff {A : PRA.Formula (n + 1)} {s t : PRA.Term n}
    (h : PRA.Proof (.eq s t)) : PRA.Proof ((A.inst s).iff (A.inst t)) :=
  formula_iff_subst A (fun i => Fin.cases h (fun _ => .eq_refl) i)

private theorem replacement_iff {A : PRA.Formula (n + 1)} {s t : PRA.Term (n + 1)}
    (h : PRA.Proof (.eq s t)) : PRA.Proof ((A.replace s).iff (A.replace t)) :=
  formula_iff_subst A (fun i => Fin.cases h (fun _ => .eq_refl) i)

private theorem replace_variable (A : PRA.Formula (n + 1)) : A.replace (.var 0) = A := by
  rw [PRA.Formula.replace]
  have vars : Fin.cases (PRA.Term.var (n := n + 1) 0) (PRA.Term.var ∘ Fin.succ) = PRA.Term.var := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [vars, PRA.Formula.subst_id]

private theorem translate_bvar_zero {E Ξ ρ n f}
    (translation : TermTranslation E Ξ ρ (n + 1) (.bvar 0) 0 f) :
    PRA.Proof (.eq (.app f PRA.Term.var) (.var 0)) := by
  obtain ⟨i, hi, heq⟩ := term_translation_bvar translation rfl
  cases eq_of_heq heq
  have index : i.natAdd 0 = (0 : Fin (0 + (n + 1))) := by
    apply Fin.ext
    simpa only [Fin.val_natAdd, Nat.zero_add, Fin.val_zero] using hi
  simpa only [index] using (PRA.Proof.app_proj (i := i.natAdd 0) (v := PRA.Term.var))

private theorem provable_translation_shift {E Ξ ρ π n H P}
    (shift : ∀ {P A}, PredicateTranslation E Ξ ρ π n P ⟨0, .prop⟩ A →
      ∃ B, PredicateTranslation E Ξ ρ π (n + 1) P.shift ⟨0, .prop⟩ B ∧
        PRA.Proof (B.iff A.shift))
    (proof : ProvableTranslation E Ξ ρ π n H P) :
    ProvableTranslation E Ξ ρ π (n + 1) (H.map PRA.Formula.shift) P.shift := by
  obtain ⟨A, ta, ha⟩ := proof
  obtain ⟨B, tb, hb⟩ := shift ta
  refine ⟨B, tb, entails_iff_backward hb ?_⟩
  exact Target.entails_subst ha (PRA.Term.var ∘ Fin.succ)

private theorem opened_variable {E Ξ ρ π n} {P : Predicate} {A}
    (opening : ∀ {t f}, TermTranslation E Ξ ρ (n + 1) t 0 f →
      ∃ B, PredicateTranslation E Ξ ρ π (n + 1) (.app P.shift t) ⟨0, .prop⟩ B ∧
        PRA.Proof (B.iff ((unaryFormula A).replace (.app f PRA.Term.var)))) :
    ∃ B, PredicateTranslation E Ξ ρ π (n + 1) (.app P.shift (.bvar 0)) ⟨0, .prop⟩ B ∧
      PRA.Proof (B.iff (unaryFormula A)) := by
  have varTranslation := TermTranslation.bvar (E := E) (Ξ := Ξ) (ρ := ρ) (0 : Fin (n + 1))
  obtain ⟨B, tb, hb⟩ := opening varTranslation
  refine ⟨B, tb, ?_⟩
  simpa only [replace_variable] using
    formula_iff_trans hb
      (replacement_iff (A := unaryFormula A) (translate_bvar_zero varTranslation))

private theorem opened_successor {E Ξ ρ π n} {P : Predicate} {A}
    (opening : ∀ {t f}, TermTranslation E Ξ ρ (n + 1) t 0 f →
      ∃ B, PredicateTranslation E Ξ ρ π (n + 1) (.app P.shift t) ⟨0, .prop⟩ B ∧
        PRA.Proof (B.iff ((unaryFormula A).replace (.app f PRA.Term.var)))) :
    ∃ B, PredicateTranslation E Ξ ρ π (n + 1)
      (.app P.shift (.app .succ (.bvar 0))) ⟨0, .prop⟩ B ∧
      PRA.Proof (B.iff ((unaryFormula A).replace (.succ (.var 0)))) := by
  have varTranslation := TermTranslation.bvar (E := E) (Ξ := Ξ) (ρ := ρ) (0 : Fin (n + 1))
  have successor := TermTranslation.app TermTranslation.succ varTranslation
  obtain ⟨B, tb, hb⟩ := opening successor
  have hs := Target.eq_trans_rule (translate_successor varTranslation successor)
    (Target.unary_congr (f := .succ) (translate_bvar_zero varTranslation))
  exact ⟨B, tb, formula_iff_trans hb (replacement_iff hs)⟩

private theorem equality_congr {s t u v : PRA.Term n}
    (left : PRA.Proof (.eq s u)) (right : PRA.Proof (.eq t v)) :
    PRA.Proof (.imp (.eq s t) (.eq u v)) :=
  .mp (Target.eq_congr_under (φ := .true) (Target.weaken left) (Target.weaken right))
    Target.imp_refl

private theorem functions_translation_rename {E Ξ ρ n fs ks} (valid : EnvironmentWF E)
    (translation : FunctionArgumentsTranslation E Ξ ρ n fs ks)
    (r : Renaming) (s : Fin n → Fin m) (hs : ∀ i, r i.val = (s i).val) :
    FunctionArgumentsTranslation E Ξ ρ m (fs.map (Term.rename r)) ks := by
  induction fs generalizing ks with
  | nil => cases translation; exact .nil
  | cons t fs ih =>
      cases translation with
      | cons head tail =>
          obtain ⟨g, tg, hg⟩ := term_translation_rename valid head r s hs
          exact .cons tg (ih tail)

private theorem iff_imp {A B C D : PRA.Formula n}
    (left : PRA.Proof (A.iff B)) (right : PRA.Proof (C.iff D)) :
    PRA.Proof ((PRA.Formula.imp A C).iff (.imp B D)) := by
  apply PRA.Proof.mp (PRA.Proof.mp .and_intro ?_) ?_
  · exact .mp (Target.imp_mono_under (ρ := .true)
      (Target.weaken (.mp .and_right left)) (Target.weaken (.mp .and_left right))) Target.imp_refl
  · exact .mp (Target.imp_mono_under (ρ := .true)
      (Target.weaken (.mp .and_left left)) (Target.weaken (.mp .and_right right))) Target.imp_refl

private theorem iff_and {A B C D : PRA.Formula n}
    (left : PRA.Proof (A.iff B)) (right : PRA.Proof (C.iff D)) :
    PRA.Proof ((PRA.Formula.and A C).iff (.and B D)) := by
  apply PRA.Proof.mp (PRA.Proof.mp .and_intro ?_) ?_
  · exact .mp (Target.and_mono_under (ρ := .true)
      (Target.weaken (.mp .and_left left)) (Target.weaken (.mp .and_left right))) Target.imp_refl
  · exact .mp (Target.and_mono_under (ρ := .true)
      (Target.weaken (.mp .and_right left)) (Target.weaken (.mp .and_right right))) Target.imp_refl

private theorem iff_or {A B C D : PRA.Formula n}
    (left : PRA.Proof (A.iff B)) (right : PRA.Proof (C.iff D)) :
    PRA.Proof ((PRA.Formula.or A C).iff (.or B D)) := by
  apply PRA.Proof.mp (PRA.Proof.mp .and_intro ?_) ?_
  · exact .mp (Target.or_mono_under (ρ := .true)
      (Target.weaken (.mp .and_left left)) (Target.weaken (.mp .and_left right))) Target.imp_refl
  · exact .mp (Target.or_mono_under (ρ := .true)
      (Target.weaken (.mp .and_right left)) (Target.weaken (.mp .and_right right))) Target.imp_refl

private theorem iff_refl (A : PRA.Formula n) : PRA.Proof (A.iff A) :=
  .mp (.mp .and_intro Target.imp_refl) Target.imp_refl

private theorem iff_symm {A B : PRA.Formula n} (h : PRA.Proof (A.iff B)) : PRA.Proof (B.iff A) :=
  .mp (.mp .and_intro (.mp .and_right h)) (.mp .and_left h)

private theorem predicate_app_subst (A : PRA.Formula ((k + 1) + n)) (f : Primrec (0 + n))
    (x : Fin k → PRA.Term q) (v : Fin n → PRA.Term q) :
    PRA.Proof (((A.subst (fun i => Fin.cases
      (.app (Primrec.reindex f (Fin.addCases Fin.elim0 (Fin.natAdd k))) PRA.Term.var)
      PRA.Term.var (Fin.succAdd i))).subst (Fin.addCases x v)).iff
        (A.subst (Fin.addCases (Fin.cases (.app f (Fin.addCases Fin.elim0 v)) x) v))) := by
  rw [PRA.Formula.subst_comp]
  apply formula_iff_subst
  intro i
  rw [← congrFun (cases_succAdd (.app f (Fin.addCases Fin.elim0 v)) x v) i]
  generalize Fin.succAdd i = j
  refine Fin.cases ?_ (fun _ => PRA.Proof.eq_refl) j
  simpa only [Fin.cases_zero, PRA.Term.subst, local_addCases, PRA.QFFormula.toFormula] using
    (PRA.QFProofI.app_reindex f (Fin.addCases Fin.elim0 (Fin.natAdd k))
      (Fin.addCases x v)).toQFProof.toProof

private theorem predicate_translation_rename {E Ξ ρ π n P σ A} (valid : EnvironmentWF E)
    (translation : PredicateTranslation E Ξ ρ π n P σ A) :
    ∀ {m} (r : Renaming) (s : Fin n → Fin m), (∀ i, r i.val = (s i).val) →
      ∃ B, PredicateTranslation E Ξ ρ π m (P.rename r) σ B ∧
        ∀ {q} (x : Fin σ.arity → PRA.Term q) (v : Fin m → PRA.Term q),
          PRA.Proof ((B.subst (Fin.addCases x v)).iff
            (A.subst (Fin.addCases x (fun i => v (s i))))) := by
  induction translation using PredicateTranslation.rec
    (motive_2 := fun n ps signatures _ => ∀ {m} (r : Renaming) (s : Fin n → Fin m),
      (∀ i, r i.val = (s i).val) →
        PredicateArgumentsTranslation E Ξ ρ π m (ps.map (Predicate.rename r)) signatures) with
  | false =>
      intro m r s hs
      simp only [Predicate.rename]
      exact ⟨_, .false, fun _ _ => iff_refl .false⟩
  | true =>
      intro m r s hs
      simp only [Predicate.rename]
      exact ⟨_, .true, fun _ _ => iff_refl .true⟩
  | equal left right =>
      intro m r s hs
      simp only [Predicate.rename]
      obtain ⟨f, tf, hf⟩ := term_translation_rename valid left r s hs
      obtain ⟨g, tg, hg⟩ := term_translation_rename valid right r s hs
      refine ⟨_, .equal tf tg, ?_⟩
      intro q x v
      exact .mp (.mp .and_intro (equality_congr (hf x v).toProof (hg x v).toProof))
        (equality_congr (PRA.QFProof.eq_symm_rule (hf x v)).toProof
          (PRA.QFProof.eq_symm_rule (hg x v)).toProof)
  | imp left right ihl ihr =>
      intro m r s hs
      simp only [Predicate.rename]
      obtain ⟨B, tb, hb⟩ := ihl r s hs
      obtain ⟨C, tc, hc⟩ := ihr r s hs
      exact ⟨_, .imp tb tc, fun x v => iff_imp (hb x v) (hc x v)⟩
  | and left right ihl ihr =>
      intro m r s hs
      simp only [Predicate.rename]
      obtain ⟨B, tb, hb⟩ := ihl r s hs
      obtain ⟨C, tc, hc⟩ := ihr r s hs
      exact ⟨_, .and tb tc, fun x v => iff_and (hb x v) (hc x v)⟩
  | or left right ihl ihr =>
      intro m r s hs
      simp only [Predicate.rename]
      obtain ⟨B, tb, hb⟩ := ihl r s hs
      obtain ⟨C, tc, hc⟩ := ihr r s hs
      exact ⟨_, .or tb tc, fun x v => iff_or (hb x v) (hc x v)⟩
  | all body ih =>
      intro m r s hs
      simp only [Predicate.rename]
      obtain ⟨B, tb, hb⟩ := ih r s hs
      refine ⟨_, .all tb, ?_⟩
      intro q x v
      have empty : x = Fin.elim0 := by funext i; exact Fin.elim0 i
      subst x
      simp only [PRA.Formula.subst, PRA.Formula.subst_comp, PRA.Term.subst, addCases_shift,
        cases_succAdd]
      have h := hb (Fin.cases (.var 0) Fin.elim0) (fun i => (v i).shift)
      exact .mp (.mp .and_intro (Target.forall_mono (.mp .and_left h)))
        (Target.forall_mono (.mp .and_right h))
  | ex body ih =>
      intro m r s hs
      simp only [Predicate.rename]
      obtain ⟨B, tb, hb⟩ := ih r s hs
      refine ⟨_, .ex tb, ?_⟩
      intro q x v
      have empty : x = Fin.elim0 := by funext i; exact Fin.elim0 i
      subst x
      simp only [PRA.Formula.subst, PRA.Formula.subst_comp, PRA.Term.subst, addCases_shift,
        cases_succAdd]
      have h := hb (Fin.cases (.var 0) Fin.elim0) (fun i => (v i).shift)
      exact .mp (.mp .and_intro (Target.exists_mono (.mp .and_left h)))
        (Target.exists_mono (.mp .and_right h))
  | parameter lookup sort =>
      intro m r s hs
      simp only [Predicate.rename]
      refine ⟨_, .parameter lookup sort, ?_⟩
      intro q x v
      simp only [PRA.Formula.subst_comp, PRA.Term.subst, addCases_embedLeft]
      exact iff_refl _
  | lam body ih =>
      intro m r s hs
      simp only [Predicate.rename]
      obtain ⟨B, tb, hb⟩ := ih (Renaming.lift 1 r) (Fin.cases 0 (fun i => (s i).succ)) (by
        intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [Renaming.lift]
        · simp [Renaming.lift, hs, Nat.add_comm])
      refine ⟨_, .lam tb, ?_⟩
      intro q x v
      have h := hb (fun i => x i.succ) (Fin.cases (x 0) v)
      simp only [cases_lift] at h
      have left := addCases_moveToFront (x 0) (fun i => x i.succ) v
      have right := addCases_moveToFront (x 0) (fun i => x i.succ) (fun i => v (s i))
      rw [cases_eta] at left right
      simpa only [PRA.Formula.subst_comp, PRA.Term.subst, left, right] using h
  | app predicate argument ih =>
      intro m r s hs
      simp only [Predicate.rename]
      obtain ⟨B, tb, hb⟩ := ih r s hs
      obtain ⟨g, tg, hg⟩ := term_translation_rename valid argument r s hs
      refine ⟨_, .app tb tg, ?_⟩
      intro q x v
      apply formula_iff_trans (predicate_app_subst B g x v)
      apply formula_iff_trans (hb _ v)
      apply formula_iff_trans (formula_iff_subst _ ?_)
      · exact iff_symm (predicate_app_subst _ _ x _)
      · intro i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · refine Fin.cases (hg Fin.elim0 v).toProof (fun _ => PRA.Proof.eq_refl) i
        · simp only [Fin.addCases_right]
          exact .eq_refl
  | letTerm value body ih =>
      intro m r s hs
      simp only [Predicate.rename]
      obtain ⟨g, tg, hg⟩ := term_translation_rename valid value r s hs
      obtain ⟨B, tb, hb⟩ := ih r s hs
      exact ⟨B, .letTerm tg tb, hb⟩
  | letPredicate value body ihv ihb =>
      intro m r s hs
      simp only [Predicate.rename]
      obtain ⟨B, tb, hb⟩ := ihv r s hs
      obtain ⟨C, tc, hc⟩ := ihb r s hs
      exact ⟨C, .letPredicate tb tc, hc⟩
  | definition lookup functions predicates body sort ihp ihb =>
      intro m r s hs
      simp only [Predicate.rename]
      obtain ⟨B, tb, hb⟩ := ihb r s hs
      obtain ⟨F, formed⟩ := declaration_origin valid lookup
      cases formed with
      | predicate typed =>
          rw [typed.instantiate_rename] at tb
          exact ⟨B, .definition lookup (functions_translation_rename valid functions r s hs)
            (ihp r s hs) tb sort, hb⟩
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i m r s hs
      obtain ⟨B, tb, hb⟩ := ihh r s hs
      exact .cons tb (iht r s hs)

private theorem functions_translation_subst {E Ξ ρ n fs ks} (valid : EnvironmentWF E)
    (translation : FunctionArgumentsTranslation E Ξ ρ n fs ks)
    (r : Subst) (s : Fin n → Primrec (0 + m))
    (hs : ∀ i, TermTranslation E Ξ ρ m (r i.val) 0 (s i)) :
    FunctionArgumentsTranslation E Ξ ρ m (fs.map (Term.subst r)) ks := by
  induction fs generalizing ks with
  | nil => cases translation; exact .nil
  | cons t fs ih =>
      cases translation with
      | cons head tail =>
          obtain ⟨g, tg, hg⟩ := term_translation_subst valid head r s hs
          exact .cons tg (ih tail)

private theorem predicate_translation_subst {E Ξ ρ π n P σ A} (valid : EnvironmentWF E)
    (translation : PredicateTranslation E Ξ ρ π n P σ A) :
    ∀ {m} (r : Subst) (s : Fin n → Primrec (0 + m)),
      (∀ i, TermTranslation E Ξ ρ m (r i.val) 0 (s i)) →
      ∃ B, PredicateTranslation E Ξ ρ π m (P.subst r) σ B ∧
        ∀ {q} (x : Fin σ.arity → PRA.Term q) (v : Fin m → PRA.Term q),
          PRA.Proof ((B.subst (Fin.addCases x v)).iff
            (A.subst (Fin.addCases x (fun i => .app (s i) (Fin.addCases Fin.elim0 v))))) := by
  induction translation using PredicateTranslation.rec
    (motive_2 := fun n ps signatures _ => ∀ {m} (r : Subst) (s : Fin n → Primrec (0 + m)),
      (∀ i, TermTranslation E Ξ ρ m (r i.val) 0 (s i)) →
        PredicateArgumentsTranslation E Ξ ρ π m (ps.map (Predicate.subst r)) signatures) with
  | false =>
      intro m r s hs
      simp only [Predicate.subst]
      exact ⟨_, .false, fun _ _ => iff_refl .false⟩
  | true =>
      intro m r s hs
      simp only [Predicate.subst]
      exact ⟨_, .true, fun _ _ => iff_refl .true⟩
  | equal left right =>
      intro m r s hs
      simp only [Predicate.subst]
      obtain ⟨f, tf, hf⟩ := term_translation_subst valid left r s hs
      obtain ⟨g, tg, hg⟩ := term_translation_subst valid right r s hs
      refine ⟨_, .equal tf tg, ?_⟩
      intro q x v
      exact .mp (.mp .and_intro (equality_congr (hf x v).toProof (hg x v).toProof))
        (equality_congr (PRA.QFProof.eq_symm_rule (hf x v)).toProof
          (PRA.QFProof.eq_symm_rule (hg x v)).toProof)
  | imp left right ihl ihr =>
      intro m r s hs
      simp only [Predicate.subst]
      obtain ⟨B, tb, hb⟩ := ihl r s hs
      obtain ⟨C, tc, hc⟩ := ihr r s hs
      exact ⟨_, .imp tb tc, fun x v => iff_imp (hb x v) (hc x v)⟩
  | and left right ihl ihr =>
      intro m r s hs
      simp only [Predicate.subst]
      obtain ⟨B, tb, hb⟩ := ihl r s hs
      obtain ⟨C, tc, hc⟩ := ihr r s hs
      exact ⟨_, .and tb tc, fun x v => iff_and (hb x v) (hc x v)⟩
  | or left right ihl ihr =>
      intro m r s hs
      simp only [Predicate.subst]
      obtain ⟨B, tb, hb⟩ := ihl r s hs
      obtain ⟨C, tc, hc⟩ := ihr r s hs
      exact ⟨_, .or tb tc, fun x v => iff_or (hb x v) (hc x v)⟩
  | all body ih =>
      intro m r s hs
      simp only [Predicate.subst]
      obtain ⟨B, tb, hb⟩ := ih r s hs
      refine ⟨_, .all tb, ?_⟩
      intro q x v
      have empty : x = Fin.elim0 := by funext i; exact Fin.elim0 i
      subst x
      simp only [PRA.Formula.subst, PRA.Formula.subst_comp, PRA.Term.subst, app_shift,
        addCases_shift, cases_succAdd]
      have h := hb (Fin.cases (.var 0) Fin.elim0) (fun i => (v i).shift)
      exact .mp (.mp .and_intro (Target.forall_mono (.mp .and_left h)))
        (Target.forall_mono (.mp .and_right h))
  | ex body ih =>
      intro m r s hs
      simp only [Predicate.subst]
      obtain ⟨B, tb, hb⟩ := ih r s hs
      refine ⟨_, .ex tb, ?_⟩
      intro q x v
      have empty : x = Fin.elim0 := by funext i; exact Fin.elim0 i
      subst x
      simp only [PRA.Formula.subst, PRA.Formula.subst_comp, PRA.Term.subst, app_shift,
        addCases_shift, cases_succAdd]
      have h := hb (Fin.cases (.var 0) Fin.elim0) (fun i => (v i).shift)
      exact .mp (.mp .and_intro (Target.exists_mono (.mp .and_left h)))
        (Target.exists_mono (.mp .and_right h))
  | parameter lookup sort =>
      intro m r s hs
      simp only [Predicate.subst]
      refine ⟨_, .parameter lookup sort, ?_⟩
      intro q x v
      simp only [PRA.Formula.subst_comp, PRA.Term.subst, addCases_embedLeft]
      exact iff_refl _
  | @lam n P k sort A name body ih =>
      intro m r s hs
      simp only [Predicate.subst]
      have shifted := fun i => term_translation_rename valid (hs i)
        (fun j => j + 1) Fin.succ (fun _ => rfl)
      classical
      let g := fun i => (shifted i).choose
      have tg := fun i => (shifted i).choose_spec.1
      have hg := fun i => @(shifted i).choose_spec.2
      let u : Fin (n + 1) → Primrec (0 + (m + 1)) :=
        Fin.cases (.proj ((0 : Fin (m + 1)).natAdd 0)) g
      have tu : ∀ i, TermTranslation E Ξ ρ (m + 1) (Subst.lift 1 r i.val) 0 (u i) := by
        intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · simpa [Subst.lift, u] using (TermTranslation.bvar (E := E) (Ξ := Ξ) (ρ := ρ)
            (0 : Fin (m + 1)))
        · simpa [Subst.lift, u, Term.shift] using tg i
      obtain ⟨B, tb, hb⟩ := ih (Subst.lift 1 r) u tu
      refine ⟨_, .lam tb, ?_⟩
      intro q x v
      have left := addCases_moveToFront (x 0) (fun i => x i.succ) v
      have right := addCases_moveToFront (x 0) (fun i => x i.succ)
        (fun i => PRA.Term.app (s i) (Fin.addCases Fin.elim0 v))
      rw [cases_eta] at left right
      simp only [PRA.Formula.subst_comp, PRA.Term.subst, left, right]
      apply formula_iff_trans (hb _ _)
      apply formula_iff_subst
      intro i
      refine Fin.addCases (fun _ => by simp only [Fin.addCases_left]; exact .eq_refl)
        (fun i => ?_) i
      simp only [Fin.addCases_right]
      refine Fin.cases ?_ (fun i => ?_) i
      · apply PRA.QFProof.toProof (A := .eq _ _)
        simpa only [u, Fin.cases_zero, Fin.addCases_right] using
            (PRA.QFProof.app_proj (i := (0 : Fin (m + 1)).natAdd 0)
              (v := Fin.addCases Fin.elim0 (Fin.cases (x 0) v)))
      · apply PRA.QFProof.toProof (A := .eq _ _)
        simpa only [u, Fin.cases_succ] using hg i Fin.elim0 (Fin.cases (x 0) v)
  | app predicate argument ih =>
      intro m r s hs
      simp only [Predicate.subst]
      obtain ⟨B, tb, hb⟩ := ih r s hs
      obtain ⟨g, tg, hg⟩ := term_translation_subst valid argument r s hs
      refine ⟨_, .app tb tg, ?_⟩
      intro q x v
      apply formula_iff_trans (predicate_app_subst B g x v)
      apply formula_iff_trans (hb _ v)
      apply formula_iff_trans (formula_iff_subst _ ?_)
      · exact iff_symm (predicate_app_subst _ _ x _)
      · intro i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · refine Fin.cases (hg Fin.elim0 v).toProof (fun _ => PRA.Proof.eq_refl) i
        · simp only [Fin.addCases_right]
          exact .eq_refl
  | letTerm value body ih =>
      intro m r s hs
      simp only [Predicate.subst]
      obtain ⟨g, tg, hg⟩ := term_translation_subst valid value r s hs
      obtain ⟨B, tb, hb⟩ := ih r s hs
      exact ⟨B, .letTerm tg tb, hb⟩
  | letPredicate value body ihv ihb =>
      intro m r s hs
      simp only [Predicate.subst]
      obtain ⟨B, tb, hb⟩ := ihv r s hs
      obtain ⟨C, tc, hc⟩ := ihb r s hs
      exact ⟨C, .letPredicate tb tc, hc⟩
  | definition lookup functions predicates body sort ihp ihb =>
      intro m r s hs
      simp only [Predicate.subst]
      obtain ⟨B, tb, hb⟩ := ihb r s hs
      obtain ⟨F, formed⟩ := declaration_origin valid lookup
      cases formed with
      | predicate typed =>
          rw [typed.instantiate_subst] at tb
          exact ⟨B, .definition lookup (functions_translation_subst valid functions r s hs)
            (ihp r s hs) tb sort, hb⟩
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i m r s hs
      obtain ⟨B, tb, hb⟩ := ihh r s hs
      exact .cons tb (iht r s hs)

private theorem zero_addCases_vars :
    (Fin.addCases (Fin.elim0 : Fin 0 → PRA.Term (0 + n))
      (fun i : Fin n => .var (i.natAdd 0))) = PRA.Term.var := by
  funext i
  refine Fin.addCases (fun i => Fin.elim0 i) (fun i => ?_) i
  simp only [Fin.addCases_right]

private theorem zero_addCases_shift_vars :
    (Fin.addCases (Fin.elim0 : Fin 0 → PRA.Term (0 + (n + 1)))
      (fun i : Fin n => .var (i.succ.natAdd 0))) = PRA.Term.var ∘ Fin.succ := by
  funext i
  refine Fin.addCases (fun i => Fin.elim0 i) (fun i => ?_) i
  simp only [Fin.addCases_right, Function.comp_apply]
  congr 1

private theorem unary_inst (A : PRA.Formula (1 + n)) (t : PRA.Term (0 + n)) :
    (unaryFormula A).inst t =
      A.subst (Fin.addCases (Fin.cases t Fin.elim0) (fun i => .var (i.natAdd 0))) := by
  simp only [unaryFormula, PRA.Formula.inst, PRA.Formula.subst_comp, PRA.Term.subst]
  rw [← zero_addCases_vars (n := n), cases_succAdd]
  simp only [Fin.addCases_right]

private theorem unary_replace (A : PRA.Formula (1 + n)) (t : PRA.Term (0 + (n + 1))) :
    (unaryFormula A).replace t =
      A.subst (Fin.addCases (Fin.cases t Fin.elim0) (fun i => .var (i.succ.natAdd 0))) := by
  simp only [unaryFormula, PRA.Formula.replace, PRA.Formula.subst_comp, PRA.Term.subst]
  rw [← zero_addCases_shift_vars (n := n), cases_succAdd]

private theorem predicate_translation_shift {E Ξ ρ π n P A} (valid : EnvironmentWF E)
    (translation : PredicateTranslation E Ξ ρ π n P ⟨0, .prop⟩ A) :
    ∃ B, PredicateTranslation E Ξ ρ π (n + 1) P.shift ⟨0, .prop⟩ B ∧
      PRA.Proof (B.iff A.shift) := by
  obtain ⟨B, tb, hb⟩ := predicate_translation_rename valid translation
    (fun i => i + 1) Fin.succ (fun _ => rfl)
  refine ⟨B, ?_, ?_⟩
  · simpa only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte] using tb
  · have h := hb Fin.elim0 (fun i => PRA.Term.var (i.natAdd 0))
    simpa only [zero_addCases_vars, zero_addCases_shift_vars, PRA.Formula.subst_id,
      PRA.Formula.shift] using h

private theorem predicate_translation_open {E Ξ ρ π n P A t f} (valid : EnvironmentWF E)
    (translation : PredicateTranslation E Ξ ρ π n P ⟨1, .prop⟩ A)
    (argument : TermTranslation E Ξ ρ (n + 1) t 0 f) :
    ∃ B, PredicateTranslation E Ξ ρ π (n + 1) (.app P.shift t) ⟨0, .prop⟩ B ∧
      PRA.Proof (B.iff ((unaryFormula A).replace (.app f PRA.Term.var))) := by
  obtain ⟨B, tb, hb⟩ := predicate_translation_rename valid translation
    (fun i => i + 1) Fin.succ (fun _ => rfl)
  have shifted : PredicateTranslation E Ξ ρ π (n + 1) P.shift ⟨1, .prop⟩ B := by
    simpa only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte] using tb
  have result := PredicateTranslation.app shifted argument
  refine ⟨_, result, formula_iff_trans (translate_application shifted argument result) ?_⟩
  rw [unary_inst, unary_replace]
  exact hb (Fin.cases (.app f PRA.Term.var) Fin.elim0) (fun i => PRA.Term.var (i.natAdd 0))

private theorem variables_addCases :
    (Fin.addCases (fun i : Fin k => PRA.Term.var (Fin.embedLeft (n := n) i))
      (fun i : Fin n => PRA.Term.var (i.natAdd k))) = PRA.Term.var := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.addCases_left]
    congr 1
    apply Fin.ext
    simp [embedLeft_val]
  · simp only [Fin.addCases_right]

private theorem codeEq_of_apply {f g : Primrec (k + n)}
    (h : ∀ {q} (x : Fin k → PRA.Term q) (v : Fin n → PRA.Term q),
      PRA.QFProof (.eq (.app f (Fin.addCases x v)) (.app g (Fin.addCases x v)))) :
    CodeEq f g := by
  simpa only [CodeEq, variables_addCases] using
    h (fun i => .var (Fin.embedLeft i)) (fun i => .var (i.natAdd k))

private def TermRelated (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (n : Nat) (t u : Term) (k : Arity) : Prop :=
  ∃ f g, TermTranslation E Ξ ρ n t k f ∧ TermTranslation E Ξ ρ n u k g ∧ CodeEq f g

private theorem term_related_refl {E Ξ ρ n t k f}
    (h : TermTranslation E Ξ ρ n t k f) : TermRelated E Ξ ρ n t t k :=
  ⟨f, f, h, h, codeEq_refl f⟩

private theorem term_related_symm {E Ξ ρ n t u k} (h : TermRelated E Ξ ρ n t u k) :
    TermRelated E Ξ ρ n u t k := by
  obtain ⟨f, g, tf, tg, h⟩ := h
  exact ⟨g, f, tg, tf, codeEq_symm h⟩

private theorem term_related_trans {E Ξ ρ n t u v k}
    (h : TermRelated E Ξ ρ n t u k) (h' : TermRelated E Ξ ρ n u v k) :
    TermRelated E Ξ ρ n t v k := by
  obtain ⟨f, g, tf, tg, h⟩ := h
  obtain ⟨g', b, tg', tb, h'⟩ := h'
  cases term_translation_unique tg tg'
  exact ⟨f, b, tf, tb, codeEq_trans h h'⟩

private theorem term_related_rename {E Ξ ρ n t u k} (valid : EnvironmentWF E)
    (h : TermRelated E Ξ ρ n t u k) {m} (r : Renaming) (s : Fin n → Fin m)
    (hs : ∀ i, r i.val = (s i).val) :
    TermRelated E Ξ ρ m (t.rename r) (u.rename r) k := by
  obtain ⟨f, g, tf, tg, h⟩ := h
  obtain ⟨a, ta, ha⟩ := term_translation_rename valid tf r s hs
  obtain ⟨b, tb, hb⟩ := term_translation_rename valid tg r s hs
  refine ⟨a, b, ta, tb, codeEq_of_apply (fun x v => ?_)⟩
  exact PRA.QFProof.eq_trans_rule (ha x v)
    (PRA.QFProof.eq_trans_rule (codeEq_apply h _)
      (PRA.QFProof.eq_symm_rule (hb x v)))

private theorem term_related_shift {E Ξ ρ n t u k} (valid : EnvironmentWF E)
    (h : TermRelated E Ξ ρ n t u k) : TermRelated E Ξ ρ (n + 1) t.shift u.shift k := by
  simpa only [Term.shift, Nat.not_lt_zero, ↓reduceIte] using
    term_related_rename valid h (fun i => i + 1) Fin.succ (fun _ => rfl)

private theorem term_related_lam {E Ξ ρ n t u k} {a b : Lean.Name}
    (h : TermRelated E Ξ ρ (n + 1) t u k) :
    TermRelated E Ξ ρ n (.lam a t) (.lam b u) (k + 1) := by
  obtain ⟨f, g, tf, tg, h⟩ := h
  refine ⟨_, _, .lam tf, .lam tg, ?_⟩
  exact codeEq_comp h (fun _ => codeEq_refl _)

private theorem term_related_app {E Ξ ρ n t u a b k}
    (h : TermRelated E Ξ ρ n t u (k + 1)) (h' : TermRelated E Ξ ρ n a b 0) :
    TermRelated E Ξ ρ n (.app t a) (.app u b) k := by
  obtain ⟨f, g, tf, tg, h⟩ := h
  obtain ⟨c, d, tc, td, h'⟩ := h'
  refine ⟨_, _, .app tf tc, .app tg td, codeEq_of_apply (fun x v => ?_)⟩
  apply PRA.QFProof.eq_trans_rule (term_app_apply f c x v)
  apply PRA.QFProof.eq_trans_rule (codeEq_apply h _)
  apply PRA.QFProof.eq_trans_rule (PRA.QFProof.app_congr ?_)
  · exact PRA.QFProof.eq_symm_rule (term_app_apply g d x v)
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.cases (codeEq_apply h' _) (fun _ => .eq_refl) i
    · simp only [Fin.addCases_right]
      exact .eq_refl

private theorem term_related_primrec {E Ξ ρ n b c s t}
    (hb : TermRelated E Ξ ρ n b c 0) (hs : TermRelated E Ξ ρ n s t 2) :
    TermRelated E Ξ ρ n (.primrec b s) (.primrec c t) 1 := by
  obtain ⟨b, c, tb, tc, hb⟩ := hb
  obtain ⟨s, t, ts, tt, hs⟩ := hs
  refine ⟨_, _, .primrec tb ts, .primrec tc tt, ?_⟩
  exact codeEq_comp (codeEq_prec hb (codeEq_comp hs (fun _ => codeEq_refl _)))
    (fun _ => codeEq_refl _)

private theorem term_related_translates {E Ξ ρ n t u k} (valid : EnvironmentWF E)
    (h : TermRelated E Ξ ρ n t u k) : TermTranslates E Ξ ρ n t k := by
  intro m r hr
  by_cases hm : m = 0
  · subst m
    have hn : n = 0 := by
      by_cases hn : n = 0
      · exact hn
      · have := hr 0 (by omega)
        omega
    subst n
    obtain ⟨f, g, tf, tg, h⟩ := term_related_rename valid h r Fin.elim0
      (fun i => Fin.elim0 i)
    exact ⟨f, tf⟩
  · haveI : NeZero m := ⟨hm⟩
    obtain ⟨f, g, tf, tg, h⟩ := term_related_rename valid h r
      (fun i => Fin.ofNat m (r i.val)) (fun i => (Nat.mod_eq_of_lt (hr i i.isLt)).symm)
    exact ⟨f, tf⟩

private def RelatedBindings (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (n : Nat) (ks : List Arity) (s t : Subst) : Prop :=
  ∀ i k, ks[i]? = some k → TermRelated E Ξ ρ n (s i) (t i) k

private theorem related_bindings_lift {E Ξ ρ n ks s t} (valid : EnvironmentWF E)
    (h : RelatedBindings E Ξ ρ n ks s t) :
    RelatedBindings E Ξ ρ (n + 1) (0 :: ks) (Subst.lift 1 s) (Subst.lift 1 t) := by
  intro i k hi
  cases i with
  | zero =>
      cases Option.some.inj hi
      exact term_related_refl (.bvar 0)
  | succ i => simpa [Subst.lift] using term_related_shift valid (h i k hi)

private theorem related_bindings_shift {E Ξ ρ n ks s t} (valid : EnvironmentWF E)
    (h : RelatedBindings E Ξ ρ n ks s t) :
    RelatedBindings E Ξ ρ (n + 1) ks (fun i => (s i).shift) (fun i => (t i).shift) :=
  fun i k hi => term_related_shift valid (h i k hi)

private inductive RelatedArguments (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (n : Nat) : List Term → List Term → List Arity → Prop
  | nil : RelatedArguments E Ξ ρ n [] [] []
  | cons (head : TermRelated E Ξ ρ n t u k) (tail : RelatedArguments E Ξ ρ n ts us ks) :
      RelatedArguments E Ξ ρ n (t :: ts) (u :: us) (k :: ks)

private def FunctionsRelated (E F : Environment) : Prop :=
  ∀ name d, E[name]? = some (.function d) →
    ∀ Ξ (ρ : FunctionAssignment Ξ.functions) n fs gs,
      RelatedArguments F Ξ ρ n fs gs d.functions →
        TermRelated F Ξ ρ n (.definition name fs) (.definition name gs) d.arity

private theorem term_related_typing {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k)
    {F} (valid : EnvironmentWF F) (functions : FunctionsRelated E F)
    {Ω} {ρ : FunctionAssignment Ω.functions} {n s t' p q}
    (locals : RelatedBindings F Ω ρ n Γ s t')
    (parameters : RelatedBindings F Ω ρ n Ξ.functions p q) :
    TermRelated F Ω ρ n (t.replace s p) (t.replace t' q) k := by
  induction h using TermTyping.rec
    (motive_2 := fun Γ fs ks _ => ∀ {n s t' p q},
      RelatedBindings F Ω ρ n Γ s t' → RelatedBindings F Ω ρ n Ξ.functions p q →
      RelatedArguments F Ω ρ n (fs.map (Term.replace s p)) (fs.map (Term.replace t' q)) ks)
    generalizing n s t' p q with
  | bvar lookup => simpa only [Term.replace] using locals _ _ lookup
  | parameter lookup => simpa only [Term.replace] using parameters _ _ lookup
  | zero =>
      simpa only [Term.replace] using
        term_related_refl (E := F) (Ξ := Ω) (ρ := ρ) (n := n) .zero
  | succ =>
      simpa only [Term.replace] using
        term_related_refl (E := F) (Ξ := Ω) (ρ := ρ) (n := n) .succ
  | lam body ih =>
      simp only [Term.replace]
      exact term_related_lam
        (ih (related_bindings_lift valid locals) (related_bindings_shift valid parameters))
  | app function argument ihf iha =>
      simp only [Term.replace]
      exact term_related_app (ihf locals parameters) (iha locals parameters)
  | letE value body ihv ihb =>
      simp only [Term.replace]
      have hv := ihv locals parameters
      obtain ⟨f, g, tf, tg, hf⟩ := hv
      obtain ⟨a, b, ta, tb, hab⟩ := ihb (s := fun | 0 => _ | i + 1 => s i)
        (t' := fun | 0 => _ | i + 1 => t' i) (by
          intro i k hi
          cases i with
          | zero => cases Option.some.inj hi; exact ⟨f, g, tf, tg, hf⟩
          | succ i => exact locals i k hi) parameters
      refine ⟨a, b, .letE tf ?_, .letE tg ?_, hab⟩
      · simpa only [Term.replace_beta] using ta
      · simpa only [Term.replace_beta] using tb
  | primrec base step ihb ihs =>
      simp only [Term.replace]
      exact term_related_primrec (ihb locals parameters) (ihs locals parameters)
  | definition lookup arguments ih =>
      simpa only [Term.replace] using functions _ _ lookup Ω ρ n _ _ (ih locals parameters)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i n s t' p q locals parameters
      exact .cons (ihh locals parameters) (iht locals parameters)

private theorem related_arguments_translation {E Ξ ρ n fs gs ks}
    (h : RelatedArguments E Ξ ρ n fs gs ks) :
    FunctionArgumentsTranslation E Ξ ρ n fs ks ∧ FunctionArgumentsTranslation E Ξ ρ n gs ks := by
  induction h with
  | nil => exact ⟨.nil, .nil⟩
  | cons head tail ih =>
      obtain ⟨f, g, tf, tg, h⟩ := head
      exact ⟨.cons tf ih.1, .cons tg ih.2⟩

private theorem related_arguments_lookup {E Ξ ρ n fs gs ks}
    (h : RelatedArguments E Ξ ρ n fs gs ks) {i : Nat} {k : Arity} (hi : ks[i]? = some k) :
    ∃ f g, fs[i]? = some f ∧ gs[i]? = some g ∧ TermRelated E Ξ ρ n f g k := by
  induction h generalizing i with
  | nil => simp at hi
  | cons head tail ih =>
      cases i with
      | zero => cases Option.some.inj hi; exact ⟨_, _, rfl, rfl, head⟩
      | succ i => exact ih hi

private theorem related_arguments_bindings {E Ξ ρ n fs gs ks}
    (h : RelatedArguments E Ξ ρ n fs gs ks) :
    RelatedBindings E Ξ ρ n ks (fun i => fs[i]?.getD (.parameter i))
      (fun i => gs[i]?.getD (.parameter i)) := by
  intro i k hi
  obtain ⟨f, g, hf, hg, h⟩ := related_arguments_lookup h hi
  simpa only [hf, hg, Option.getD_some] using h

private theorem functions_related {E} (valid : EnvironmentWF E) :
    ∀ F, EnvironmentWF F → EnvironmentExtends E F → FunctionsRelated E F := by
  induction valid with
  | empty =>
      intro F valid ext name d lookup
      simp at lookup
  | @insert E e previous fresh declaration ih =>
      intro F valid ext name d lookup Ξ ρ n fs gs actuals
      have older : EnvironmentExtends E F := fun name d lookup =>
        ext name d (EnvironmentExtends.insert fresh name d lookup)
      have hf := ih F valid older
      by_cases heq : e.name = name
      · have same : e = .function d := by
          simpa only [Std.ExtHashMap.getElem?_insert, heq, beq_self_eq_true, ↓reduceIte,
            Option.some.injEq] using lookup
        subst e
        cases declaration with
        | function typed =>
            have hb := term_related_typing typed valid hf (s := Term.bvar) (t' := Term.bvar)
              (by intro i k hi; simp at hi) (related_arguments_bindings actuals)
            rw [typed.replace_instantiate fs _ (by intros; rfl),
              typed.replace_instantiate gs _ (by intros; rfl)] at hb
            obtain ⟨f, g, tf, tg, h⟩ := hb
            have ta := related_arguments_translation actuals
            exact ⟨f, g, .definition (ext _ _ lookup) ta.1 tf,
              .definition (ext _ _ lookup) ta.2 tg, h⟩
      · have old : E[name]? = some (.function d) := by
          simpa [Std.ExtHashMap.getElem?_insert, heq] using lookup
        exact hf name d old Ξ ρ n fs gs actuals

private theorem term_related_left {E Ξ ρ n t u k} (h : TermRelated E Ξ ρ n t u k) :
    TermRelated E Ξ ρ n t t k := by
  obtain ⟨f, g, tf, tg, h⟩ := h
  exact term_related_refl tf

private theorem term_related_beta {E Ξ ρ n t a k f g} {name : Lean.Name}
    (valid : EnvironmentWF E) (body : TermTranslation E Ξ ρ (n + 1) t k f)
    (argument : TermTranslation E Ξ ρ n a 0 g) :
    TermRelated E Ξ ρ n (.app (.lam name t) a) (t.subst0 a) k := by
  let s : Fin (n + 1) → Primrec (0 + n) :=
    Fin.cases g (fun i => .proj (i.natAdd 0))
  have hs : ∀ i : Fin (n + 1), TermTranslation E Ξ ρ n
      ((fun | 0 => a | j + 1 => Term.bvar j) i.val) 0 (s i) := by
    intro i
    exact Fin.cases argument (fun i => .bvar i) i
  obtain ⟨b, tb, hb⟩ := term_translation_subst valid body (fun | 0 => a | j + 1 => .bvar j) s hs
  refine ⟨_, b, .app (.lam body) argument, tb, codeEq_of_apply (fun x v => ?_)⟩
  apply PRA.QFProof.eq_trans_rule (term_app_apply _ g x v)
  apply PRA.QFProof.eq_trans_rule (term_lam_apply _ _ x v)
  apply PRA.QFProof.eq_trans_rule (PRA.QFProof.app_congr ?_)
  · exact PRA.QFProof.eq_symm_rule (hb x v)
  · intro i
    refine Fin.addCases (fun _ => by simp only [Fin.addCases_left]; exact .eq_refl)
      (fun i => ?_) i
    simp only [Fin.addCases_right]
    refine Fin.cases (by exact .eq_refl) (fun i => ?_) i
    exact PRA.QFProof.eq_symm_rule (by
      simpa only [s, Fin.cases_succ, Fin.addCases_right] using
        (PRA.QFProof.app_proj (i := i.natAdd 0) (v := Fin.addCases Fin.elim0 v)))

private theorem term_related_eta {E Ξ ρ n t k f} {name : Lean.Name}
    (valid : EnvironmentWF E) (function : TermTranslation E Ξ ρ n t (k + 1) f) :
    TermRelated E Ξ ρ n (.lam name (.app t.shift (.bvar 0))) t (k + 1) := by
  obtain ⟨g, tg, hg⟩ := term_translation_rename valid function
    (fun i => i + 1) Fin.succ (fun _ => rfl)
  have tg' : TermTranslation E Ξ ρ (n + 1) t.shift (k + 1) g := by
    simpa only [Term.shift, Nat.not_lt_zero, ↓reduceIte] using tg
  refine ⟨_, f, .lam (.app tg' (.bvar 0)), function, codeEq_of_apply (fun x v => ?_)⟩
  apply PRA.QFProof.eq_trans_rule (by
    simpa only [cases_eta] using term_lam_apply _ (x 0) (fun i => x i.succ) v)
  apply PRA.QFProof.eq_trans_rule (term_app_apply _ _ _ _)
  apply PRA.QFProof.eq_trans_rule (hg _ _)
  apply PRA.QFProof.app_congr
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.addCases_left]
    refine Fin.cases ?_ (fun _ => .eq_refl) i
    simpa only [Fin.addCases_right, Fin.cases_zero] using (PRA.QFProof.app_proj
      (i := (0 : Fin (n + 1)).natAdd 0)
      (v := Fin.addCases Fin.elim0 (Fin.cases (x 0) v)))
  · simp only [Fin.addCases_right, Fin.cases_succ]
    exact .eq_refl

private theorem term_related_zero {E Ξ ρ n b s f g}
    (base : TermTranslation E Ξ ρ n b 0 f) (step : TermTranslation E Ξ ρ n s 2 g) :
    TermRelated E Ξ ρ n (.app (.primrec b s) .zero) b 0 := by
  refine ⟨_, f, .app (.primrec base step) .zero, base, codeEq_of_apply (fun x v => ?_)⟩
  have hx : x = Fin.elim0 := by funext i; exact Fin.elim0 i
  subst x
  apply PRA.QFProof.eq_trans_rule (recursion_apply _ _ _ _)
  apply PRA.QFProof.eq_trans_rule (PRA.QFProof.app_congr ?_)
  · exact .app_prec_zero
  · intro i
    refine Fin.cases ?_ (fun _ => .eq_refl) i
    simp only [Fin.cases_zero]
    apply PRA.QFProof.eq_trans_rule .app_comp
    exact PRA.QFProof.app_congr (fun i => Fin.elim0 i)

private theorem term_related_successor {E Ξ ρ n b s a f g h}
    (base : TermTranslation E Ξ ρ n b 0 f) (step : TermTranslation E Ξ ρ n s 2 g)
    (argument : TermTranslation E Ξ ρ n a 0 h) :
    TermRelated E Ξ ρ n (.app (.primrec b s) (.app .succ a))
      (.app (.app s a) (.app (.primrec b s) a)) 0 := by
  refine ⟨_, _, .app (.primrec base step) (.app .succ argument),
    .app (.app step argument) (.app (.primrec base step) argument), codeEq_of_apply (fun x v => ?_)⟩
  have hx : x = Fin.elim0 := by funext i; exact Fin.elim0 i
  subst x
  apply PRA.QFProof.eq_trans_rule (recursion_apply _ _ _ _)
  apply PRA.QFProof.eq_trans_rule (PRA.QFProof.app_congr ?_)
  · apply PRA.QFProof.eq_trans_rule
      (PRA.QFProof.app_prec_succ (t := .app h (Fin.addCases Fin.elim0 v))
        (v := Fin.addCases Fin.elim0 v))
    apply PRA.QFProof.eq_trans_rule (recursion_step_apply g _ _ v)
    apply PRA.QFProof.eq_trans_rule (PRA.QFProof.app_congr ?_)
    · apply PRA.QFProof.eq_trans_rule (PRA.QFProof.eq_symm_rule (term_app_apply _ _ _ _))
      exact PRA.QFProof.eq_symm_rule (term_app_apply _ _ _ _)
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.addCases_left]
        refine Fin.cases .eq_refl (fun i => ?_) i
        refine Fin.cases (PRA.QFProof.eq_symm_rule (recursion_apply _ _ _ _))
          (fun i => Fin.elim0 i) i
      · simp only [Fin.addCases_right]
        exact .eq_refl
  · intro i
    refine Fin.cases ?_ (fun _ => .eq_refl) i
    apply PRA.QFProof.eq_trans_rule (term_app_apply _ _ Fin.elim0 v)
    apply PRA.QFProof.eq_trans_rule (reindex_arguments _ _ v)
    exact .eq_refl

private theorem related_bindings_left {E Ξ ρ n ks s t}
    (h : RelatedBindings E Ξ ρ n ks s t) : RelatedBindings E Ξ ρ n ks s s :=
  fun i k hi => term_related_left (h i k hi)

private theorem related_bindings_symm {E Ξ ρ n ks s t}
    (h : RelatedBindings E Ξ ρ n ks s t) : RelatedBindings E Ξ ρ n ks t s :=
  fun i k hi => term_related_symm (h i k hi)

private theorem related_bindings_cons {E Ξ ρ n ks s t a b k}
    (head : TermRelated E Ξ ρ n a b k) (tail : RelatedBindings E Ξ ρ n ks s t) :
    RelatedBindings E Ξ ρ n (k :: ks) (fun | 0 => a | i + 1 => s i)
      (fun | 0 => b | i + 1 => t i) := by
  intro i j hi
  cases i with
  | zero => cases Option.some.inj hi; exact head
  | succ i => exact tail i j hi

private theorem term_related_conversion {E Ξ Γ a b k} (equality : TermEq E Ξ Γ a b k)
    (validE : EnvironmentWF E) {F} (valid : EnvironmentWF F)
    (ext : EnvironmentExtends E F) {Ω} {ρ : FunctionAssignment Ω.functions} {n s t p q}
    (locals : RelatedBindings F Ω ρ n Γ s t)
    (parameters : RelatedBindings F Ω ρ n Ξ.functions p q) :
    TermRelated F Ω ρ n (a.replace s p) (b.replace t q) k := by
  have functions := functions_related validE F valid ext
  induction equality using TermEq.rec
    (motive_2 := fun Γ fs gs ks _ => ∀ {n s t p q},
      RelatedBindings F Ω ρ n Γ s t → RelatedBindings F Ω ρ n Ξ.functions p q →
      RelatedArguments F Ω ρ n (fs.map (Term.replace s p)) (gs.map (Term.replace t q)) ks)
    generalizing n s t p q with
  | refl typed => exact term_related_typing typed valid functions locals parameters
  | symm equal ih =>
      exact term_related_symm (ih (related_bindings_symm locals) (related_bindings_symm parameters))
  | trans left right ihl ihr =>
      exact term_related_trans
        (ihl (related_bindings_left locals) (related_bindings_left parameters))
        (ihr locals parameters)
  | @beta Γ tBody k a name body argument =>
      have ha := term_related_typing argument valid functions locals parameters
      have hb := term_related_typing body valid functions
        (related_bindings_lift valid (related_bindings_left locals))
        (related_bindings_shift valid (related_bindings_left parameters))
      obtain ⟨f, g, tf, tg, heq⟩ := hb
      obtain ⟨c, d, tc, td, hc⟩ := ha
      have first := term_related_beta (name := name) valid tf tc
      rw [Term.replace_beta] at first
      have second := term_related_typing body valid functions
        (related_bindings_cons ⟨c, d, tc, td, hc⟩ locals) parameters
      simpa only [Term.replace, Term.subst0_replace] using
        term_related_trans first second
  | @eta Γ f k name function =>
      obtain ⟨f, g, tf, tg, h⟩ := term_related_typing function valid functions locals parameters
      have first := term_related_eta (name := name) valid tf
      simpa only [Term.replace, Term.shift_replace, Subst.lift, Nat.zero_lt_succ,
        ↓reduceIte] using
        term_related_trans first ⟨f, g, tf, tg, h⟩
  | zeta value body =>
      obtain ⟨f, g, tf, tg, h⟩ := term_related_typing value valid functions locals parameters
      obtain ⟨a, b, ta, tb, h'⟩ := term_related_typing body valid functions
        (related_bindings_cons ⟨f, g, tf, tg, h⟩ locals) parameters
      simp only [Term.replace, Term.subst0_replace]
      refine ⟨a, b, .letE tf ?_, tb, h'⟩
      simpa only [Term.replace_beta] using ta
  | delta lookup arguments body =>
      obtain ⟨a, b, ta, tb, h⟩ := term_related_typing body valid functions locals parameters
      obtain ⟨G, formed⟩ := declaration_origin validE lookup
      cases formed with
      | function typed =>
          rw [typed.instantiate_replace _ arguments.length_eq] at ta
          have args := function_arguments_translate arguments (functions_translate validE F ext)
            (fun i k hi => term_related_translates valid (locals i k hi))
            (fun i k hi => term_related_translates valid (parameters i k hi))
          have actuals := arguments_translation args id (fun _ hi => hi)
          simp only [List.map_map, Function.comp_def, Term.rename_id] at actuals
          exact ⟨a, b, by simpa only [Term.replace] using
            TermTranslation.definition (ext _ _ lookup) actuals ta, tb, h⟩
  | primrecZero base step =>
      obtain ⟨b, c, tb, tc, hb⟩ := term_related_typing base valid functions locals parameters
      obtain ⟨s, t, ts, tt, hs⟩ := term_related_typing step valid functions locals parameters
      simpa only [Term.replace] using
        term_related_trans (term_related_zero tb ts) ⟨b, c, tb, tc, hb⟩
  | primrecSucc base step argument =>
      have hb := term_related_typing base valid functions locals parameters
      have hs := term_related_typing step valid functions locals parameters
      have ha := term_related_typing argument valid functions locals parameters
      obtain ⟨b, c, tb, tc, hbc⟩ := hb
      obtain ⟨s, t, ts, tt, hst⟩ := hs
      obtain ⟨a, d, ta, td, had⟩ := ha
      have first := term_related_successor tb ts ta
      have second := term_related_app
        (term_related_app ⟨s, t, ts, tt, hst⟩ ⟨a, d, ta, td, had⟩)
        (term_related_app (term_related_primrec ⟨b, c, tb, tc, hbc⟩ ⟨s, t, ts, tt, hst⟩)
          ⟨a, d, ta, td, had⟩)
      simpa only [Term.replace] using term_related_trans first second
  | lam body ih =>
      simpa only [Term.replace] using term_related_lam
        (ih (related_bindings_lift valid locals) (related_bindings_shift valid parameters))
  | app function argument ihf iha =>
      simpa only [Term.replace] using
        term_related_app (ihf locals parameters) (iha locals parameters)
  | letE value body ihv ihb =>
      obtain ⟨f, g, tf, tg, h⟩ := ihv locals parameters
      obtain ⟨a, b, ta, tb, h'⟩ := ihb
        (related_bindings_cons ⟨f, g, tf, tg, h⟩ locals) parameters
      simp only [Term.replace]
      refine ⟨a, b, .letE tf ?_, .letE tg ?_, h'⟩
      · simpa only [Term.replace_beta] using ta
      · simpa only [Term.replace_beta] using tb
  | primrec base step ihb ihs =>
      simpa only [Term.replace] using term_related_primrec
        (ihb locals parameters) (ihs locals parameters)
  | definition lookup arguments ih =>
      simpa only [Term.replace] using functions _ _ lookup Ω ρ n _ _ (ih locals parameters)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i n s t p q locals parameters
      exact .cons (ihh locals parameters) (iht locals parameters)

private theorem iff_subst {A B : PRA.Formula n} (h : PRA.Proof (A.iff B))
    (v : Fin n → PRA.Term m) : PRA.Proof ((A.subst v).iff (B.subst v)) := .subst h v

private theorem iff_of_apply {A B : PRA.Formula (k + n)}
    (h : ∀ {q} (x : Fin k → PRA.Term q) (v : Fin n → PRA.Term q),
      PRA.Proof ((A.subst (Fin.addCases x v)).iff (B.subst (Fin.addCases x v)))) :
    PRA.Proof (A.iff B) := by
  simpa only [variables_addCases, PRA.Formula.subst_id] using
    h (fun i => .var (Fin.embedLeft i)) (fun i => .var (i.natAdd k))

private def PredicateRelated (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates)
    (n : Nat) (P Q : Predicate) (σ : PredicateSignature) : Prop :=
  ∃ A B, PredicateTranslation E Ξ ρ π n P σ A ∧ PredicateTranslation E Ξ ρ π n Q σ B ∧
    PRA.Proof (A.iff B)

private theorem predicate_related_refl {E Ξ ρ π n P σ A}
    (h : PredicateTranslation E Ξ ρ π n P σ A) : PredicateRelated E Ξ ρ π n P P σ :=
  ⟨A, A, h, h, iff_refl A⟩

private theorem predicate_related_symm {E Ξ ρ π n P Q σ}
    (h : PredicateRelated E Ξ ρ π n P Q σ) : PredicateRelated E Ξ ρ π n Q P σ := by
  obtain ⟨A, B, ta, tb, h⟩ := h
  exact ⟨B, A, tb, ta, iff_symm h⟩

private theorem predicate_related_left {E Ξ ρ π n P Q σ}
    (h : PredicateRelated E Ξ ρ π n P Q σ) : PredicateRelated E Ξ ρ π n P P σ := by
  obtain ⟨A, B, ta, tb, h⟩ := h
  exact predicate_related_refl ta

private theorem predicate_related_trans {E Ξ ρ π n P Q R σ}
    (h : PredicateRelated E Ξ ρ π n P Q σ) (h' : PredicateRelated E Ξ ρ π n Q R σ) :
    PredicateRelated E Ξ ρ π n P R σ := by
  obtain ⟨A, B, ta, tb, h⟩ := h
  obtain ⟨B', C, tb', tc, h'⟩ := h'
  cases predicate_translation_unique tb tb'
  exact ⟨A, C, ta, tc, formula_iff_trans h h'⟩

private theorem predicate_related_toProp {E Ξ ρ π n P Q σ}
    (h : PredicateRelated E Ξ ρ π n P Q σ) :
    PredicateRelated E Ξ ρ π n P Q ⟨σ.arity, .prop⟩ := by
  obtain ⟨A, B, ta, tb, h⟩ := h
  exact ⟨A, B, translation_toProp ta, translation_toProp tb, h⟩

private theorem predicate_related_rename {E Ξ ρ π n P Q σ} (valid : EnvironmentWF E)
    (h : PredicateRelated E Ξ ρ π n P Q σ) {m} (r : Renaming) (s : Fin n → Fin m)
    (hs : ∀ i, r i.val = (s i).val) :
    PredicateRelated E Ξ ρ π m (P.rename r) (Q.rename r) σ := by
  obtain ⟨A, B, ta, tb, h⟩ := h
  obtain ⟨C, tc, hc⟩ := predicate_translation_rename valid ta r s hs
  obtain ⟨D, td, hd⟩ := predicate_translation_rename valid tb r s hs
  refine ⟨C, D, tc, td, iff_of_apply (fun x v => ?_)⟩
  exact formula_iff_trans (hc x v) (formula_iff_trans (iff_subst h _) (iff_symm (hd x v)))

private theorem predicate_related_shift {E Ξ ρ π n P Q σ} (valid : EnvironmentWF E)
    (h : PredicateRelated E Ξ ρ π n P Q σ) :
    PredicateRelated E Ξ ρ π (n + 1) P.shift Q.shift σ := by
  simpa only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte] using
    predicate_related_rename valid h (fun i => i + 1) Fin.succ (fun _ => rfl)

private theorem predicate_related_equal {E Ξ ρ π n a b c d sort}
    (h : TermRelated E Ξ ρ n a b 0) (h' : TermRelated E Ξ ρ n c d 0) :
    PredicateRelated E Ξ ρ π n (.equal a c) (.equal b d) ⟨0, sort⟩ := by
  obtain ⟨a, b, ta, tb, h⟩ := h
  obtain ⟨c, d, tc, td, h'⟩ := h'
  exact ⟨_, _, .equal ta tc, .equal tb td,
    .mp (.mp .and_intro (equality_congr (codeEq_fo h) (codeEq_fo h')))
      (equality_congr (codeEq_fo (codeEq_symm h)) (codeEq_fo (codeEq_symm h')))⟩

private theorem predicate_related_lam {E Ξ ρ π n P Q k sort} {a b : BinderInfo}
    (h : PredicateRelated E Ξ ρ π (n + 1) P Q ⟨k, sort⟩) :
    PredicateRelated E Ξ ρ π n (.lam a P) (.lam b Q) ⟨k + 1, sort⟩ := by
  obtain ⟨A, B, ta, tb, h⟩ := h
  exact ⟨_, _, .lam ta, .lam tb, iff_subst h _⟩

private theorem predicate_related_app {E Ξ ρ π n P Q a b k sort}
    (h : PredicateRelated E Ξ ρ π n P Q ⟨k + 1, sort⟩)
    (h' : TermRelated E Ξ ρ n a b 0) :
    PredicateRelated E Ξ ρ π n (.app P a) (.app Q b) ⟨k, sort⟩ := by
  obtain ⟨A, B, ta, tb, h⟩ := h
  obtain ⟨f, g, tf, tg, h'⟩ := h'
  refine ⟨_, _, .app ta tf, .app tb tg, iff_of_apply (fun x v => ?_)⟩
  apply formula_iff_trans (predicate_app_subst A f x v)
  apply formula_iff_trans (iff_subst h _)
  apply formula_iff_trans (formula_iff_subst B ?_)
  · exact iff_symm (predicate_app_subst B g x v)
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.cases (codeEq_apply h' _).toProof (fun _ => .eq_refl) i
    · simp only [Fin.addCases_right]
      exact .eq_refl

private theorem predicate_related_all {E Ξ ρ π n P Q}
    (h : PredicateRelated E Ξ ρ π n P Q ⟨1, .prop⟩) :
    PredicateRelated E Ξ ρ π n (.all P) (.all Q) ⟨0, .prop⟩ := by
  obtain ⟨A, B, ta, tb, h⟩ := h
  have hi := iff_subst h (fun i => PRA.Term.var (Fin.succAdd i))
  exact ⟨_, _, .all ta, .all tb,
    .mp (.mp .and_intro (Target.forall_mono (.mp .and_left hi)))
      (Target.forall_mono (.mp .and_right hi))⟩

private theorem predicate_related_ex {E Ξ ρ π n P Q}
    (h : PredicateRelated E Ξ ρ π n P Q ⟨1, .prop⟩) :
    PredicateRelated E Ξ ρ π n (.ex P) (.ex Q) ⟨0, .prop⟩ := by
  obtain ⟨A, B, ta, tb, h⟩ := h
  have hi := iff_subst h (fun i => PRA.Term.var (Fin.succAdd i))
  exact ⟨_, _, .ex ta, .ex tb,
    .mp (.mp .and_intro (Target.exists_mono (.mp .and_left hi)))
      (Target.exists_mono (.mp .and_right hi))⟩

private def RelatedPredicateBindings (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates)
    (n : Nat) (signatures : List PredicateSignature) (p q : Nat → Predicate) : Prop :=
  ∀ i σ, signatures[i]? = some σ → PredicateRelated E Ξ ρ π n (p i) (q i) σ

private theorem related_predicate_bindings_shift {E Ξ ρ π n signatures p q}
    (valid : EnvironmentWF E) (h : RelatedPredicateBindings E Ξ ρ π n signatures p q) :
    RelatedPredicateBindings E Ξ ρ π (n + 1) signatures
      (fun i => (p i).shift) (fun i => (q i).shift) :=
  fun i σ hi => predicate_related_shift valid (h i σ hi)

private inductive RelatedPredicateArguments (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates)
    (n : Nat) : List Predicate → List Predicate → List PredicateSignature → Prop
  | nil : RelatedPredicateArguments E Ξ ρ π n [] [] []
  | cons (head : PredicateRelated E Ξ ρ π n P Q σ)
      (tail : RelatedPredicateArguments E Ξ ρ π n ps qs signatures) :
      RelatedPredicateArguments E Ξ ρ π n (P :: ps) (Q :: qs) (σ :: signatures)

private def PredicatesRelated (E F : Environment) : Prop :=
  ∀ name d, E[name]? = some (.predicate d) →
    ∀ Ξ (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates) n fs gs ps qs,
      RelatedArguments F Ξ ρ n fs gs d.functions →
      RelatedPredicateArguments F Ξ ρ π n ps qs d.predicates →
        PredicateRelated F Ξ ρ π n (.definition name fs ps) (.definition name gs qs) d.signature

private theorem function_arguments_related {E Ξ Γ fs ks} (h : FunctionArguments E Ξ Γ fs ks)
    {F} (valid : EnvironmentWF F) (functions : FunctionsRelated E F)
    {Ω} {ρ : FunctionAssignment Ω.functions} {n s t p q}
    (locals : RelatedBindings F Ω ρ n Γ s t)
    (parameters : RelatedBindings F Ω ρ n Ξ.functions p q) :
    RelatedArguments F Ω ρ n (fs.map (Term.replace s p)) (fs.map (Term.replace t q)) ks := by
  induction h using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail _ ih =>
    exact .cons (term_related_typing head valid functions locals parameters) (ih locals)
  all_goals trivial

private theorem predicate_related_typing {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ)
    {F} (valid : EnvironmentWF F) (functions : FunctionsRelated E F)
    (predicates : PredicatesRelated E F)
    {Ω} {ρ : FunctionAssignment Ω.functions} {π : PredicateAssignment Ω.predicates}
    {n s t p q u v} (locals : RelatedBindings F Ω ρ n Γ s t)
    (parameters : RelatedBindings F Ω ρ n Ξ.functions p q)
    (predicateParameters : RelatedPredicateBindings F Ω ρ π n Ξ.predicates u v) :
    PredicateRelated F Ω ρ π n (P.replace s p u) (P.replace t q v) σ := by
  induction h using PredicateTyping.rec
    (motive_2 := fun Γ ps signatures _ => ∀ {n s t p q u v},
      RelatedBindings F Ω ρ n Γ s t → RelatedBindings F Ω ρ n Ξ.functions p q →
      RelatedPredicateBindings F Ω ρ π n Ξ.predicates u v →
      RelatedPredicateArguments F Ω ρ π n
        (ps.map (Predicate.replace s p u)) (ps.map (Predicate.replace t q v)) signatures)
    generalizing n s t p q u v with
  | false =>
      simp only [Predicate.replace]
      exact predicate_related_refl .false
  | true =>
      simp only [Predicate.replace]
      exact predicate_related_refl .true
  | equal left right =>
      simp only [Predicate.replace]
      exact predicate_related_equal (term_related_typing left valid functions locals parameters)
        (term_related_typing right valid functions locals parameters)
  | imp left right ihl ihr =>
      obtain ⟨A, B, ta, tb, h⟩ := ihl locals parameters predicateParameters
      obtain ⟨C, D, tc, td, h'⟩ := ihr locals parameters predicateParameters
      simp only [Predicate.replace]
      exact ⟨_, _, .imp ta tc, .imp tb td, iff_imp h h'⟩
  | and left right ihl ihr =>
      obtain ⟨A, B, ta, tb, h⟩ := ihl locals parameters predicateParameters
      obtain ⟨C, D, tc, td, h'⟩ := ihr locals parameters predicateParameters
      simp only [Predicate.replace]
      exact ⟨_, _, .and ta tc, .and tb td, iff_and h h'⟩
  | or left right ihl ihr =>
      obtain ⟨A, B, ta, tb, h⟩ := ihl locals parameters predicateParameters
      obtain ⟨C, D, tc, td, h'⟩ := ihr locals parameters predicateParameters
      simp only [Predicate.replace]
      exact ⟨_, _, .or ta tc, .or tb td, iff_or h h'⟩
  | all body ih =>
      simpa only [Predicate.replace] using
        predicate_related_all (ih locals parameters predicateParameters)
  | ex body ih =>
      simpa only [Predicate.replace] using
        predicate_related_ex (ih locals parameters predicateParameters)
  | parameter lookup => simpa only [Predicate.replace] using predicateParameters _ _ lookup
  | lam body ih =>
      simp only [Predicate.replace]
      exact predicate_related_lam (ih (related_bindings_lift valid locals)
        (related_bindings_shift valid parameters)
        (related_predicate_bindings_shift valid predicateParameters))
  | app function argument ih =>
      simp only [Predicate.replace]
      exact predicate_related_app (ih locals parameters predicateParameters)
        (term_related_typing argument valid functions locals parameters)
  | letTerm value body ih =>
      obtain ⟨f, g, tf, tg, h⟩ := term_related_typing value valid functions locals parameters
      obtain ⟨A, B, ta, tb, h'⟩ := ih locals parameters predicateParameters
      simp only [Predicate.replace]
      exact ⟨A, B, .letTerm tf ta, .letTerm tg tb, h'⟩
  | letPredicate value body ihv ihb =>
      obtain ⟨C, D, tc, td, h⟩ := ihv locals parameters predicateParameters
      obtain ⟨A, B, ta, tb, h'⟩ := ihb locals parameters predicateParameters
      simp only [Predicate.replace]
      exact ⟨A, B, .letPredicate tc ta, .letPredicate td tb, h'⟩
  | definition lookup fs ps ih =>
      simpa only [Predicate.replace] using predicates _ _ lookup Ω ρ π n _ _ _ _
        (function_arguments_related fs valid functions locals parameters)
        (ih locals parameters predicateParameters)
  | subsumption typing sub ih =>
      cases sub with
      | refl => exact ih locals parameters predicateParameters
      | lift => exact predicate_related_toProp (ih locals parameters predicateParameters)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i n s t p q u v locals parameters predicateParameters
      exact .cons (ihh locals parameters predicateParameters)
        (iht locals parameters predicateParameters)

private theorem related_predicate_arguments_translation {E Ξ ρ π n fs gs ks}
    (h : RelatedPredicateArguments E Ξ ρ π n fs gs ks) :
    PredicateArgumentsTranslation E Ξ ρ π n fs ks ∧
      PredicateArgumentsTranslation E Ξ ρ π n gs ks := by
  induction h with
  | nil => exact ⟨.nil, .nil⟩
  | cons head tail ih =>
      obtain ⟨f, g, tf, tg, h⟩ := head
      exact ⟨.cons tf ih.1, .cons tg ih.2⟩

private theorem related_predicate_arguments_lookup {E Ξ ρ π n fs gs ks}
    (h : RelatedPredicateArguments E Ξ ρ π n fs gs ks)
    {i : Nat} {k : PredicateSignature} (hi : ks[i]? = some k) :
    ∃ f g, fs[i]? = some f ∧ gs[i]? = some g ∧ PredicateRelated E Ξ ρ π n f g k := by
  induction h generalizing i with
  | nil => simp at hi
  | cons head tail ih =>
      cases i with
      | zero => cases Option.some.inj hi; exact ⟨_, _, rfl, rfl, head⟩
      | succ i => exact ih hi

private theorem related_predicate_arguments_bindings {E Ξ ρ π n fs gs ks}
    (h : RelatedPredicateArguments E Ξ ρ π n fs gs ks) :
    RelatedPredicateBindings E Ξ ρ π n ks (fun i => fs[i]?.getD (.parameter i))
      (fun i => gs[i]?.getD (.parameter i)) := by
  intro i k hi
  obtain ⟨f, g, hf, hg, h⟩ := related_predicate_arguments_lookup h hi
  simpa only [hf, hg, Option.getD_some] using h

private theorem predicates_related {E} (valid : EnvironmentWF E) :
    ∀ F, EnvironmentWF F → EnvironmentExtends E F → PredicatesRelated E F := by
  induction valid with
  | empty =>
      intro F valid ext name d lookup
      simp at lookup
  | @insert E e previous fresh declaration ih =>
      intro F valid ext name d lookup Ξ ρ π n fs gs ps qs actuals predicateActuals
      have older : EnvironmentExtends E F := fun name d lookup =>
        ext name d (EnvironmentExtends.insert fresh name d lookup)
      have hf := functions_related previous F valid older
      have hp := ih F valid older
      by_cases heq : e.name = name
      · have same : e = .predicate d := by
          simpa only [Std.ExtHashMap.getElem?_insert, heq, beq_self_eq_true, ↓reduceIte,
            Option.some.injEq] using lookup
        subst e
        cases declaration with
        | predicate typed =>
            have hb := predicate_related_typing typed valid hf hp
              (s := Term.bvar) (t := Term.bvar) (by intro i k hi; simp at hi)
              (related_arguments_bindings actuals)
              (related_predicate_arguments_bindings predicateActuals)
            rw [typed.replace_instantiate fs ps _ _ (by intros; rfl) (by intros; rfl),
              typed.replace_instantiate gs qs _ _ (by intros; rfl) (by intros; rfl)] at hb
            obtain ⟨A, B, ta, tb, h⟩ := hb
            have tf := related_arguments_translation actuals
            have tp := related_predicate_arguments_translation predicateActuals
            exact ⟨A, B, .definition (ext _ _ lookup) tf.1 tp.1 ta (.inr rfl),
              .definition (ext _ _ lookup) tf.2 tp.2 tb (.inr rfl), h⟩
      · have old : E[name]? = some (.predicate d) := by
          simpa [Std.ExtHashMap.getElem?_insert, heq] using lookup
        exact hp name d old Ξ ρ π n fs gs ps qs actuals predicateActuals

private theorem predicate_related_beta {E Ξ ρ π n P a k sort A f} {name : BinderInfo}
    (valid : EnvironmentWF E) (body : PredicateTranslation E Ξ ρ π (n + 1) P ⟨k, sort⟩ A)
    (argument : TermTranslation E Ξ ρ n a 0 f) :
    PredicateRelated E Ξ ρ π n (.app (.lam name P) a) (P.subst0 a) ⟨k, sort⟩ := by
  let s : Fin (n + 1) → Primrec (0 + n) :=
    Fin.cases f (fun i => .proj (i.natAdd 0))
  have hs : ∀ i : Fin (n + 1), TermTranslation E Ξ ρ n
      ((fun | 0 => a | j + 1 => Term.bvar j) i.val) 0 (s i) := by
    intro i
    exact Fin.cases argument (fun i => .bvar i) i
  obtain ⟨B, tb, hb⟩ := predicate_translation_subst valid body
    (fun | 0 => a | j + 1 => .bvar j) s hs
  refine ⟨_, B, .app (.lam body) argument, tb, iff_of_apply (fun x v => ?_)⟩
  apply formula_iff_trans (predicate_app_subst _ f x v)
  simp only [PRA.Formula.subst_comp, PRA.Term.subst, addCases_moveToFront]
  apply formula_iff_trans (formula_iff_subst A ?_)
  · exact iff_symm (hb x v)
  · intro i
    refine Fin.addCases (fun _ => by simp only [Fin.addCases_left]; exact .eq_refl)
      (fun i => ?_) i
    simp only [Fin.addCases_right]
    refine Fin.cases (by exact .eq_refl) (fun i => ?_) i
    exact Target.eq_symm_rule (by
      simpa only [s, Fin.cases_succ, Fin.addCases_right] using
        (PRA.Proof.app_proj (i := i.natAdd 0) (v := Fin.addCases Fin.elim0 v)))

private theorem predicate_related_eta {E Ξ ρ π n P k sort A} {name : BinderInfo}
    (valid : EnvironmentWF E) (function : PredicateTranslation E Ξ ρ π n P ⟨k + 1, sort⟩ A) :
    PredicateRelated E Ξ ρ π n (.lam name (.app P.shift (.bvar 0))) P ⟨k + 1, sort⟩ := by
  obtain ⟨B, tb, hb⟩ := predicate_translation_rename valid function
    (fun i => i + 1) Fin.succ (fun _ => rfl)
  have tb' : PredicateTranslation E Ξ ρ π (n + 1) P.shift ⟨k + 1, sort⟩ B := by
    simpa only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte] using tb
  refine ⟨_, A, .lam (.app tb' (.bvar 0)), function, iff_of_apply (fun x v => ?_)⟩
  have split := addCases_moveToFront (x 0) (fun i => x i.succ) v
  rw [cases_eta] at split
  simp only [PRA.Formula.subst_comp, PRA.Term.subst_comp, PRA.Term.subst, split]
  -- Normalize application before comparing its supplied variable with the first argument.
  have app := predicate_app_subst B (.proj ((0 : Fin (n + 1)).natAdd 0))
    (fun i => x i.succ) (Fin.cases (x 0) v)
  simp only [PRA.Formula.subst_comp] at app
  apply formula_iff_trans app
  apply formula_iff_trans (hb _ _)
  apply formula_iff_subst
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.addCases_left]
    refine Fin.cases ?_ (fun _ => .eq_refl) i
    simpa only [Fin.addCases_right, Fin.cases_zero] using (PRA.Proof.app_proj
      (i := (0 : Fin (n + 1)).natAdd 0)
      (v := Fin.addCases Fin.elim0 (Fin.cases (x 0) v)))
  · simp only [Fin.addCases_right, Fin.cases_succ]
    exact .eq_refl

private theorem related_predicate_bindings_left {E Ξ ρ π n signatures p q}
    (h : RelatedPredicateBindings E Ξ ρ π n signatures p q) :
    RelatedPredicateBindings E Ξ ρ π n signatures p p :=
  fun i σ hi => predicate_related_left (h i σ hi)

private theorem related_predicate_bindings_symm {E Ξ ρ π n signatures p q}
    (h : RelatedPredicateBindings E Ξ ρ π n signatures p q) :
    RelatedPredicateBindings E Ξ ρ π n signatures q p :=
  fun i σ hi => predicate_related_symm (h i σ hi)

private theorem predicate_related_subtype {E Ξ ρ π n P Q σ τ}
    (h : PredicateRelated E Ξ ρ π n P Q σ) (sub : PredicateSubtyping σ τ) :
    PredicateRelated E Ξ ρ π n P Q τ := by
  cases sub with
  | refl => exact h
  | lift => exact predicate_related_toProp h

private theorem subtype_trans {σ τ υ : PredicateSignature}
    (h : PredicateSubtyping σ τ) (h' : PredicateSubtyping τ υ) : PredicateSubtyping σ υ := by
  cases h <;> cases h' <;> constructor

private theorem predicate_definition_subtype {E Ξ Γ P σ} (typed : PredicateTyping E Ξ Γ P σ) :
    ∀ {name fs ps d}, P = .definition name fs ps → E[name]? = some (.predicate d) →
      PredicateSubtyping d.signature σ := by
  induction typed using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True)
  case definition lookup functions predicates ih =>
    intro name fs ps d eq lookup'
    cases eq
    cases Declaration.predicate.inj (Option.some.inj (lookup.symm.trans lookup'))
    exact .refl
  case subsumption typing sub ih =>
    intro name fs ps d eq lookup
    exact subtype_trans (ih eq lookup) sub
  all_goals first | trivial | (intros; contradiction)

private theorem function_arguments_conversion {E Ξ Γ fs gs ks}
    (h : FunctionArgumentEq E Ξ Γ fs gs ks) (validE : EnvironmentWF E)
    {F} (valid : EnvironmentWF F) (ext : EnvironmentExtends E F)
    {Ω} {ρ : FunctionAssignment Ω.functions} {n s t p q}
    (locals : RelatedBindings F Ω ρ n Γ s t)
    (parameters : RelatedBindings F Ω ρ n Ξ.functions p q) :
    RelatedArguments F Ω ρ n (fs.map (Term.replace s p)) (gs.map (Term.replace t q)) ks := by
  induction h using FunctionArgumentEq.rec (motive_1 := fun _ _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail _ ih =>
    exact .cons (term_related_conversion head validE valid ext locals parameters) (ih locals)
  all_goals trivial

private theorem predicate_arguments_related {E Ξ Γ ps signatures}
    (h : PredicateArguments E Ξ Γ ps signatures)
    {F} (valid : EnvironmentWF F) (functions : FunctionsRelated E F)
    (predicates : PredicatesRelated E F)
    {Ω} {ρ : FunctionAssignment Ω.functions} {π : PredicateAssignment Ω.predicates}
    {n s t p q u v} (locals : RelatedBindings F Ω ρ n Γ s t)
    (parameters : RelatedBindings F Ω ρ n Ξ.functions p q)
    (predicateParameters : RelatedPredicateBindings F Ω ρ π n Ξ.predicates u v) :
    RelatedPredicateArguments F Ω ρ π n
      (ps.map (Predicate.replace s p u)) (ps.map (Predicate.replace t q v)) signatures := by
  induction h using PredicateArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail _ ih =>
    exact .cons (predicate_related_typing head valid functions predicates locals parameters
      predicateParameters) (ih locals)
  all_goals trivial

private theorem predicate_related_conversion {E Ξ Γ P Q σ}
    (equality : PredicateEq E Ξ Γ P Q σ) (validE : EnvironmentWF E)
    {F} (valid : EnvironmentWF F) (ext : EnvironmentExtends E F)
    {Ω} {ρ : FunctionAssignment Ω.functions} {π : PredicateAssignment Ω.predicates}
    {n s t p q u v} (locals : RelatedBindings F Ω ρ n Γ s t)
    (parameters : RelatedBindings F Ω ρ n Ξ.functions p q)
    (predicateParameters : RelatedPredicateBindings F Ω ρ π n Ξ.predicates u v) :
    PredicateRelated F Ω ρ π n (P.replace s p u) (Q.replace t q v) σ := by
  have functions := functions_related validE F valid ext
  have predicates := predicates_related validE F valid ext
  induction equality using PredicateEq.rec
    (motive_2 := fun Γ ps qs signatures _ => ∀ {n s t p q u v},
      RelatedBindings F Ω ρ n Γ s t → RelatedBindings F Ω ρ n Ξ.functions p q →
      RelatedPredicateBindings F Ω ρ π n Ξ.predicates u v →
      RelatedPredicateArguments F Ω ρ π n
        (ps.map (Predicate.replace s p u)) (qs.map (Predicate.replace t q v)) signatures)
    generalizing n s t p q u v with
  | refl typed =>
      exact predicate_related_typing typed valid functions predicates
        locals parameters predicateParameters
  | symm equal ih =>
      exact predicate_related_symm (ih (related_bindings_symm locals)
        (related_bindings_symm parameters) (related_predicate_bindings_symm predicateParameters))
  | trans left right ihl ihr =>
      exact predicate_related_trans (ihl (related_bindings_left locals)
        (related_bindings_left parameters) (related_predicate_bindings_left predicateParameters))
        (ihr locals parameters predicateParameters)
  | subsumption equal sub ih =>
      exact predicate_related_subtype (ih locals parameters predicateParameters) sub
  | @beta Γ P k sort a name body argument =>
      obtain ⟨f, g, tf, tg, h⟩ := term_related_typing argument valid functions locals parameters
      obtain ⟨A, B, ta, tb, h'⟩ := predicate_related_typing body valid functions predicates
        (related_bindings_lift valid (related_bindings_left locals))
        (related_bindings_shift valid (related_bindings_left parameters))
        (related_predicate_bindings_shift valid
          (related_predicate_bindings_left predicateParameters))
      have first := predicate_related_beta (name := name) valid ta tf
      rw [Predicate.replace_beta] at first
      have second := predicate_related_typing body valid functions predicates
        (related_bindings_cons ⟨f, g, tf, tg, h⟩ locals) parameters predicateParameters
      simpa only [Predicate.replace, Predicate.subst0_replace] using
        predicate_related_trans first second
  | @eta Γ P k sort name function =>
      obtain ⟨A, B, ta, tb, h⟩ := predicate_related_typing function valid functions predicates
        locals parameters predicateParameters
      have first := predicate_related_eta (name := name) valid ta
      simpa only [Predicate.replace, Predicate.shift_replace, Term.replace, Subst.lift,
        Nat.zero_lt_succ, ↓reduceIte] using predicate_related_trans first ⟨A, B, ta, tb, h⟩
  | zetaTerm value body =>
      obtain ⟨f, g, tf, tg, h⟩ := term_related_typing value valid functions locals parameters
      obtain ⟨A, B, ta, tb, h'⟩ := predicate_related_typing body valid functions predicates
        locals parameters predicateParameters
      simp only [Predicate.replace]
      exact ⟨A, B, .letTerm tf ta, tb, h'⟩
  | zetaPredicate value body =>
      obtain ⟨C, D, tc, td, h⟩ := predicate_related_typing value valid functions predicates
        locals parameters predicateParameters
      obtain ⟨A, B, ta, tb, h'⟩ := predicate_related_typing body valid functions predicates
        locals parameters predicateParameters
      simp only [Predicate.replace]
      exact ⟨A, B, .letPredicate tc ta, tb, h'⟩
  | delta lookup fs ps body bound =>
      obtain ⟨A, B, ta, tb, h⟩ := predicate_related_typing body valid functions predicates
        locals parameters predicateParameters
      obtain ⟨G, formed⟩ := declaration_origin validE lookup
      cases formed with
      | predicate typed =>
          rw [typed.instantiate_replace _ _ fs.length_eq ps.length_eq] at ta
          have refs := predicate_related_typing (.definition lookup fs ps) valid functions
            predicates locals parameters predicateParameters
          have refs' := predicate_related_subtype refs bound
          obtain ⟨C, D, tc, td, h'⟩ := refs'
          simp only [Predicate.replace] at tc
          cases tc with
          | definition lookup' fs' ps' body' sort =>
              cases Declaration.predicate.inj
                (Option.some.inj ((ext _ _ lookup).symm.trans lookup'))
              have ta' := translation_toProp ta
              have eq := predicate_translation_unique (translation_toProp body') ta'
              cases eq
              exact ⟨_, B, by simpa only [Predicate.replace] using
                PredicateTranslation.definition (ext _ _ lookup) fs' ps' body' sort, tb, h⟩
  | equal left right =>
      simp only [Predicate.replace]
      exact predicate_related_equal
        (term_related_conversion left validE valid ext locals parameters)
        (term_related_conversion right validE valid ext locals parameters)
  | imp left right ihl ihr =>
      obtain ⟨A, B, ta, tb, h⟩ := ihl locals parameters predicateParameters
      obtain ⟨C, D, tc, td, h'⟩ := ihr locals parameters predicateParameters
      simp only [Predicate.replace]
      exact ⟨_, _, .imp ta tc, .imp tb td, iff_imp h h'⟩
  | and left right ihl ihr =>
      obtain ⟨A, B, ta, tb, h⟩ := ihl locals parameters predicateParameters
      obtain ⟨C, D, tc, td, h'⟩ := ihr locals parameters predicateParameters
      simp only [Predicate.replace]
      exact ⟨_, _, .and ta tc, .and tb td, iff_and h h'⟩
  | or left right ihl ihr =>
      obtain ⟨A, B, ta, tb, h⟩ := ihl locals parameters predicateParameters
      obtain ⟨C, D, tc, td, h'⟩ := ihr locals parameters predicateParameters
      simp only [Predicate.replace]
      exact ⟨_, _, .or ta tc, .or tb td, iff_or h h'⟩
  | all body ih =>
      simpa only [Predicate.replace] using
        predicate_related_all (ih locals parameters predicateParameters)
  | ex body ih =>
      simpa only [Predicate.replace] using
        predicate_related_ex (ih locals parameters predicateParameters)
  | lam body ih =>
      simp only [Predicate.replace]
      exact predicate_related_lam (ih (related_bindings_lift valid locals)
        (related_bindings_shift valid parameters)
        (related_predicate_bindings_shift valid predicateParameters))
  | app function argument ih =>
      simp only [Predicate.replace]
      exact predicate_related_app (ih locals parameters predicateParameters)
        (term_related_conversion argument validE valid ext locals parameters)
  | definition lookup fs ps left right ih =>
      simpa only [Predicate.replace] using predicate_related_subtype
        (predicates _ _ lookup Ω ρ π n _ _ _ _
          (function_arguments_conversion fs validE valid ext locals parameters)
          (ih locals parameters predicateParameters))
        (predicate_definition_subtype left rfl lookup)
  | nil => exact .nil
  | cons head tail ihh iht =>
      rename_i n s t p q u v locals parameters predicateParameters
      exact .cons (ihh locals parameters predicateParameters)
        (iht locals parameters predicateParameters)

private theorem term_replaced_translation {E Ξ Γ t k} (typed : TermTyping E Ξ Γ t k)
    (validE : EnvironmentWF E) {F} (valid : EnvironmentWF F) (ext : EnvironmentExtends E F)
    {Ω} {ρ : FunctionAssignment Ω.functions} {n s p}
    (locals : RelatedBindings F Ω ρ n Γ s s)
    (parameters : RelatedBindings F Ω ρ n Ξ.functions p p) :
    ∃ f, TermTranslation F Ω ρ n (t.replace s p) k f := by
  obtain ⟨f, g, tf, tg, h⟩ := term_related_typing typed valid
    (functions_related validE F valid ext) locals parameters
  exact ⟨f, tf⟩

private theorem predicate_replaced_translation {E Ξ Γ P σ} (typed : PredicateTyping E Ξ Γ P σ)
    (validE : EnvironmentWF E) {F} (valid : EnvironmentWF F) (ext : EnvironmentExtends E F)
    {Ω} {ρ : FunctionAssignment Ω.functions} {π : PredicateAssignment Ω.predicates} {n s p q}
    (locals : RelatedBindings F Ω ρ n Γ s s)
    (parameters : RelatedBindings F Ω ρ n Ξ.functions p p)
    (predicateParameters : RelatedPredicateBindings F Ω ρ π n Ξ.predicates q q) :
    ∃ A, PredicateTranslation F Ω ρ π n (P.replace s p q) σ A := by
  obtain ⟨A, B, ta, tb, h⟩ := predicate_related_typing typed valid
    (functions_related validE F valid ext) (predicates_related validE F valid ext)
    locals parameters predicateParameters
  exact ⟨A, ta⟩

private def TheoremsTranslate (E F : Environment) : Prop :=
  ∀ (name : Lean.Name) (d : TheoremDefinition), E[name]? = some (.theoremE d) →
    ∀ Ξ (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates) n fs ps,
      RelatedArguments F Ξ ρ n fs fs d.functions →
      RelatedPredicateArguments F Ξ ρ π n ps ps d.predicates →
        ProvableTranslation F Ξ ρ π n [] (d.type.instantiate fs ps)

private theorem derivation_replaced_translation {E Ξ Γ H P}
    (typed : Derivation E Ξ Γ H P) (validE : EnvironmentWF E)
    {F} (valid : EnvironmentWF F) (ext : EnvironmentExtends E F)
    (theorems : TheoremsTranslate E F)
    {Ω} {ρ : FunctionAssignment Ω.functions} {π : PredicateAssignment Ω.predicates} :
    ∀ n s p q, RelatedBindings F Ω ρ n Γ s s →
      RelatedBindings F Ω ρ n Ξ.functions p p →
      RelatedPredicateBindings F Ω ρ π n Ξ.predicates q q → ∀ Δ,
      (∀ Q ∈ H, ProvableTranslation F Ω ρ π n Δ (Q.replace s p q)) →
      ProvableTranslation F Ω ρ π n Δ (P.replace s p q) := by
  induction typed with
  | hyp lookup =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      exact hypotheses _ (List.mem_of_getElem? lookup)
  | trueIntro =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      exact ⟨_, .true, Target.entails_of_proof Target.imp_refl⟩
  | theoremE lookup functions predicates =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      obtain ⟨G, formed⟩ := declaration_origin validE lookup
      cases formed with
      | theoremE type body =>
          rw [type.instantiate_replace _ _ functions.length_eq predicates.length_eq]
          obtain ⟨A, translation, proof⟩ := theorems _ _ lookup Ω ρ π n _ _
            (function_arguments_related functions valid (functions_related validE F valid ext)
              locals parameters)
            (predicate_arguments_related predicates valid (functions_related validE F valid ext)
              (predicates_related validE F valid ext) locals parameters predicateParameters)
          exact ⟨A, translation, Target.entails_of_proof proof⟩
  | impIntro antecedent body ih =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨A, translation⟩ :=
        predicate_replaced_translation antecedent validE valid ext
          locals parameters predicateParameters
      obtain ⟨B, result, proof⟩ := ih n s p q locals parameters predicateParameters (A :: Δ) (by
        intro Q hQ
        rcases List.mem_cons.mp hQ with eq | mem
        · subst Q; exact ⟨A, translation, Target.entails_head⟩
        · exact provable_translation_weaken (hypotheses Q mem))
      exact ⟨_, .imp translation result, proof⟩
  | impElim function argument ihf iha =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨A, translation, proof⟩ :=
        ihf n s p q locals parameters predicateParameters Δ hypotheses
      cases translation with
      | imp left right =>
          exact ⟨_, right, Target.entails_mp proof
            (provable_translation_at
              (iha n s p q locals parameters predicateParameters Δ hypotheses) left)⟩
  | andIntro left right ihl ihr =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨A, ta, ha⟩ := ihl n s p q locals parameters predicateParameters Δ hypotheses
      obtain ⟨B, tb, hb⟩ := ihr n s p q locals parameters predicateParameters Δ hypotheses
      exact ⟨_, .and ta tb,
        Target.entails_mp (Target.entails_mp (Target.entails_of_proof .and_intro) ha) hb⟩
  | andLeft pair ih =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨A, translation, proof⟩ :=
        ih n s p q locals parameters predicateParameters Δ hypotheses
      cases translation with
      | and left right =>
          exact ⟨_, left, Target.entails_mp (Target.entails_of_proof .and_left) proof⟩
  | andRight pair ih =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨A, translation, proof⟩ :=
        ih n s p q locals parameters predicateParameters Δ hypotheses
      cases translation with
      | and left right =>
          exact ⟨_, right, Target.entails_mp (Target.entails_of_proof .and_right) proof⟩
  | orLeft other proof ih =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨A, ta, ha⟩ := ih n s p q locals parameters predicateParameters Δ hypotheses
      obtain ⟨B, tb⟩ :=
        predicate_replaced_translation other validE valid ext locals parameters predicateParameters
      exact ⟨_, .or ta tb, Target.entails_mp (Target.entails_of_proof .or_left) ha⟩
  | orRight other proof ih =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨A, ta⟩ :=
        predicate_replaced_translation other validE valid ext locals parameters predicateParameters
      obtain ⟨B, tb, hb⟩ := ih n s p q locals parameters predicateParameters Δ hypotheses
      exact ⟨_, .or ta tb, Target.entails_mp (Target.entails_of_proof .or_right) hb⟩
  | orElim target scrutinee left right ihs ihl ihr =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨C, tc⟩ :=
        predicate_replaced_translation target validE valid ext locals parameters predicateParameters
      obtain ⟨A, ta, ha⟩ := ihs n s p q locals parameters predicateParameters Δ hypotheses
      cases ta with
      | @or _ _ _ a _ b ta tb =>
          have left :=
            provable_translation_at (ihl n s p q locals parameters predicateParameters (a :: Δ) (by
              intro Q hQ
              rcases List.mem_cons.mp hQ with eq | mem
              · subst Q; exact ⟨_, ta, Target.entails_head⟩
              · exact provable_translation_weaken (hypotheses Q mem))) tc
          have right :=
            provable_translation_at (ihr n s p q locals parameters predicateParameters (b :: Δ) (by
              intro Q hQ
              rcases List.mem_cons.mp hQ with eq | mem
              · subst Q; exact ⟨_, tb, Target.entails_head⟩
              · exact provable_translation_weaken (hypotheses Q mem))) tc
          exact ⟨_, tc, Target.entails_mp (Target.entails_mp
            (Target.entails_mp (Target.entails_of_proof .or_elim) left) right) ha⟩
  | falseElim target proof ih =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨A, ta⟩ :=
        predicate_replaced_translation target validE valid ext locals parameters predicateParameters
      have hp :=
        provable_translation_at
          (ih n s p q locals parameters predicateParameters Δ hypotheses) .false
      exact ⟨_, ta, Target.entails_mp (Target.entails_of_proof Target.false_elim) hp⟩
  | forallIntro motive body ih =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      have underBinder := ih (n + 1) (Subst.lift 1 s) (fun i => (p i).shift) (fun i => (q i).shift)
        (related_bindings_lift valid locals) (related_bindings_shift valid parameters)
        (related_predicate_bindings_shift valid predicateParameters)
      simp only [Predicate.shift_replace, Term.replace, Subst.lift, Nat.zero_lt_succ,
        ↓reduceIte] at underBinder
      obtain ⟨A, ta⟩ :=
        predicate_replaced_translation motive validE valid ext locals parameters predicateParameters
      obtain ⟨B, tb, hb⟩ := opened_variable (predicate_translation_open valid ta)
      have body := provable_translation_at (underBinder
        (Δ.map PRA.Formula.shift) (by
          intro Q hQ
          obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hQ
          simpa only [Predicate.shift_replace] using
            provable_translation_shift (predicate_translation_shift valid) (hypotheses R hR))) tb
      exact ⟨_, .all ta, Target.entails_gen (entails_iff_forward hb body)⟩
  | forallElim proof argument ih =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨A, ta, ha⟩ := ih n s p q locals parameters predicateParameters Δ hypotheses
      obtain ⟨f, tf⟩ := term_replaced_translation argument validE valid ext locals parameters
      cases ta with
      | all predicate =>
          have result := PredicateTranslation.app predicate tf
          have hb := Target.entails_mp (Target.entails_of_proof
            (PRA.Proof.forall_elim (t := .app f PRA.Term.var))) ha
          exact ⟨_, result, entails_iff_backward
            (translate_application predicate tf result) hb⟩
  | existsIntro motive witness proof ih =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨A, ta⟩ :=
        predicate_replaced_translation motive validE valid ext locals parameters predicateParameters
      obtain ⟨f, tf⟩ := term_replaced_translation witness validE valid ext locals parameters
      have result := PredicateTranslation.app ta tf
      have ha :=
        provable_translation_at
          (ih n s p q locals parameters predicateParameters Δ hypotheses) result
      have hb := entails_iff_forward (translate_application ta tf result) ha
      exact ⟨_, .ex ta, Target.entails_mp (Target.entails_of_proof .exists_intro) hb⟩
  | existsElim target scrutinee body ihs ihb =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      have underBinder := ihb (n + 1) (Subst.lift 1 s) (fun i => (p i).shift) (fun i => (q i).shift)
        (related_bindings_lift valid locals) (related_bindings_shift valid parameters)
        (related_predicate_bindings_shift valid predicateParameters)
      simp only [Predicate.shift_replace] at underBinder
      obtain ⟨C, tc⟩ :=
        predicate_replaced_translation target validE valid ext locals parameters predicateParameters
      obtain ⟨D, td, hd⟩ := predicate_translation_shift valid tc
      obtain ⟨A, ta, ha⟩ := ihs n s p q locals parameters predicateParameters Δ hypotheses
      cases ta with
      | @ex _ _ a ta =>
          obtain ⟨B, tb, hb⟩ := opened_variable (predicate_translation_open valid ta)
          have body := provable_translation_at (underBinder
            (unaryFormula a :: Δ.map PRA.Formula.shift) (by
              intro Q hQ
              rcases List.mem_cons.mp hQ with eq | mem
              · subst Q
                simp only [Predicate.replace, Predicate.shift_replace, Term.replace, Subst.lift,
                  Nat.zero_lt_succ, ↓reduceIte]
                exact ⟨B, tb, entails_iff_backward hb Target.entails_head⟩
              · obtain ⟨R, hR, rfl⟩ := List.mem_map.mp mem
                simpa only [Predicate.shift_replace] using provable_translation_weaken
                  (provable_translation_shift (predicate_translation_shift valid)
                    (hypotheses R hR)))) td
          exact ⟨C, tc, Target.entails_exists_elim ha (entails_iff_forward hd body)⟩
  | letE type value body ihv ihb =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      obtain ⟨A, ta, ha⟩ := ihv n s p q locals parameters predicateParameters Δ hypotheses
      exact ihb n s p q locals parameters predicateParameters Δ (by
        intro Q hQ
        rcases List.mem_cons.mp hQ with eq | mem
        · subst Q; exact ⟨_, ta, ha⟩
        · exact hypotheses Q mem)
  | letTerm value body ih | letPredicate value body ih | ascribe type proof ih => exact ih
  | eqRefl term =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨f, tf⟩ := term_replaced_translation term validE valid ext locals parameters
      exact ⟨_, .equal tf tf, Target.entails_of_proof .eq_refl⟩
  | eqSubst motive equality proof ihe ihp =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨A, ta⟩ :=
        predicate_replaced_translation motive validE valid ext locals parameters predicateParameters
      obtain ⟨B, tb, hb⟩ := ihe n s p q locals parameters predicateParameters Δ hypotheses
      cases tb with
      | @equal _ _ f _ g _ left right =>
          have leftApp := PredicateTranslation.app ta left
          have rightApp := PredicateTranslation.app ta right
          have hl :=
            provable_translation_at
              (ihp n s p q locals parameters predicateParameters Δ hypotheses) leftApp
          have hi := Target.instance_congr_under (unaryFormula A)
            (s := .app f PRA.Term.var) (t := .app g PRA.Term.var) Target.imp_refl
          have hr := Target.entails_mp (Target.entails_mp (Target.entails_of_proof hi) hb)
            (entails_iff_forward (translate_application ta left leftApp) hl)
          exact ⟨_, rightApp, entails_iff_backward (translate_application ta right rightApp) hr⟩
  | succNeZero term =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace, Term.replace] at *
      obtain ⟨f, tf⟩ := term_replaced_translation term validE valid ext locals parameters
      have ts := TermTranslation.app TermTranslation.succ tf
      have tz := TermTranslation.zero (E := F) (Ξ := Ω) (ρ := ρ) (n := n)
      have he := equality_congr (translate_successor tf ts) (translate_zero tz)
      exact ⟨_, .imp (.equal ts tz) .false,
        Target.entails_of_proof (Target.imp_trans_rule he .succ_ne_zero)⟩
  | succInj proof ih =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace, Term.replace] at *
      obtain ⟨A, ta, ha⟩ := ih n s p q locals parameters predicateParameters Δ hypotheses
      cases ta with
      | equal left right =>
          cases left with
          | app leftSucc leftArg =>
              cases right with
              | app rightSucc rightArg =>
                  have left := TermTranslation.app leftSucc leftArg
                  have right := TermTranslation.app rightSucc rightArg
                  have he := equality_congr (translate_successor leftArg left)
                    (translate_successor rightArg right)
                  exact ⟨_, .equal leftArg rightArg, Target.entails_mp
                    (Target.entails_of_proof .succ_inj)
                    (Target.entails_mp (Target.entails_of_proof he) ha)⟩
  | lem formula =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace] at *
      obtain ⟨A, ta⟩ :=
        predicate_replaced_translation formula validE valid ext
          locals parameters predicateParameters
      exact ⟨_, .or ta (.imp ta .false), Target.entails_of_proof (Target.excluded_middle A)⟩
  | induction motive base step argument ihb ihs =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      simp only [Predicate.replace, Term.replace] at *
      have underBinder := ihs (n + 1) (Subst.lift 1 s) (fun i => (p i).shift) (fun i => (q i).shift)
        (related_bindings_lift valid locals) (related_bindings_shift valid parameters)
        (related_predicate_bindings_shift valid predicateParameters)
      simp only [Predicate.shift_replace, Subst.lift, Nat.zero_lt_succ,
        ↓reduceIte] at underBinder
      obtain ⟨A, tqf⟩ :=
        predicate_replaced_translation motive validE valid ext locals parameters predicateParameters
      have ta := translation_toProp tqf
      have qf : (unaryFormula A).QuantifierFree :=
        (PRA.Formula.quantifierFree_subst _ _).mpr (translation_qf tqf rfl)
      have tz := TermTranslation.zero (E := F) (Ξ := Ω) (ρ := ρ) (n := n)
      have baseTranslation := PredicateTranslation.app ta tz
      have base :=
        provable_translation_at
          (ihb n s p q locals parameters predicateParameters Δ hypotheses) baseTranslation
      have base := entails_iff_forward (translate_application ta tz baseTranslation) base
      have base := entails_iff_forward (instance_iff (A := unaryFormula A) (translate_zero tz)) base
      obtain ⟨B, tb, hb⟩ := opened_variable (predicate_translation_open valid ta)
      obtain ⟨S, ts, hs⟩ := opened_successor (predicate_translation_open valid ta)
      have step := provable_translation_at (underBinder
        (unaryFormula A :: Δ.map PRA.Formula.shift) (by
          intro Q hQ
          rcases List.mem_cons.mp hQ with eq | mem
          · subst Q
            simp only [Predicate.replace, Predicate.shift_replace, Term.replace, Subst.lift,
              Nat.zero_lt_succ, ↓reduceIte]
            exact ⟨B, tb, entails_iff_backward hb Target.entails_head⟩
          · obtain ⟨R, hR, rfl⟩ := List.mem_map.mp mem
            simpa only [Predicate.shift_replace] using provable_translation_weaken
              (provable_translation_shift (predicate_translation_shift valid)
                (hypotheses R hR)))) ts
      have all := Target.entails_induction qf base (entails_iff_forward hs step)
      obtain ⟨f, tf⟩ := term_replaced_translation argument validE valid ext locals parameters
      have result := PredicateTranslation.app ta tf
      have applied := Target.entails_mp (Target.entails_of_proof
        (PRA.Proof.forall_elim (t := .app f PRA.Term.var))) all
      exact ⟨_, result, entails_iff_backward (translate_application ta tf result) applied⟩
  | conversion proof type ih =>
      intro n s p q locals parameters predicateParameters Δ hypotheses
      obtain ⟨A, ta, ha⟩ := ih n s p q locals parameters predicateParameters Δ hypotheses
      obtain ⟨B, C, tb, tc, h⟩ := predicate_related_conversion type validE valid ext
        locals parameters predicateParameters
      cases predicate_translation_unique ta tb
      exact ⟨C, tc, entails_iff_forward h ha⟩

private theorem theorems_translate {E} (valid : EnvironmentWF E) :
    ∀ F, EnvironmentWF F → EnvironmentExtends E F → TheoremsTranslate E F := by
  induction valid with
  | empty =>
      intro F valid ext name d lookup
      simp at lookup
  | @insert E e previous fresh declaration ih =>
      intro F valid ext name d lookup Ξ ρ π n fs ps actuals predicateActuals
      have older : EnvironmentExtends E F := fun name d lookup =>
        ext name d (EnvironmentExtends.insert fresh name d lookup)
      have earlier := ih F valid older
      by_cases heq : e.name = name
      · have same : e = .theoremE d := by
          simpa only [Std.ExtHashMap.getElem?_insert, heq, beq_self_eq_true, ↓reduceIte,
            Option.some.injEq] using lookup
        subst e
        cases declaration with
        | theoremE type body =>
            have proof := derivation_replaced_translation (body.toDerivation previous)
              previous valid older earlier
              n Term.bvar _ _ (by intro i k hi; simp at hi)
              (related_arguments_bindings actuals)
              (related_predicate_arguments_bindings predicateActuals) [] (by simp)
            rw [type.replace_instantiate fs ps _ _ (by intros; rfl) (by intros; rfl)] at proof
            exact proof
      · have old : E[name]? = some (.theoremE d) := by
          simpa [Std.ExtHashMap.getElem?_insert, heq] using lookup
        exact earlier name d old Ξ ρ π n fs ps actuals predicateActuals

private theorem proofTranslation_sound {E p P} {Ξ : ParameterContext}
    {A : FunctionAssignment Ξ.functions → PredicateAssignment Ξ.predicates → PRA.Formula 0}
    (valid : EnvironmentWF E)
    (typed : ProofTyping E Ξ [] [] p P)
    (translation : ∀ ρ π, PredicateTranslation E Ξ ρ π 0 P ⟨0, .prop⟩ (A ρ π))
    (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates) :
    PRA.Proof (A ρ π) := by
  have parameters : RelatedBindings E Ξ ρ 0 Ξ.functions Term.parameter Term.parameter := by
    intro i k hi
    exact term_related_refl (.parameter hi)
  have predicates : RelatedPredicateBindings E Ξ ρ π 0 Ξ.predicates
      Predicate.parameter Predicate.parameter := by
    intro i σ hi
    exact predicate_related_refl (.parameter hi (.inr rfl))
  have proof := derivation_replaced_translation (typed.toDerivation valid)
    valid valid (fun _ _ h => h)
    (theorems_translate valid E valid (fun _ _ h => h))
    0 Term.bvar Term.parameter Predicate.parameter (by intro i k hi; simp at hi)
    parameters predicates [] (by simp)
  simp only [Predicate.replace_id] at proof
  exact provable_translation_at proof (translation ρ π)

/-- A closed term has arity `k` if and only if it translates to a `Primrec k` under every
function-parameter assignment. -/
public theorem termTyping_iff_translation {E Ξ t k} (valid : EnvironmentWF E) :
    TermTyping E Ξ [] t k ↔ ∃ f : FunctionAssignment Ξ.functions → Primrec k,
      ∀ ρ, TermTranslation E Ξ ρ 0 t k (f ρ) := by
  constructor
  · intro typed
    classical
    exact ⟨fun ρ => (term_translation_exists (n := 0) valid typed ρ).choose,
      fun ρ => (term_translation_exists (n := 0) valid typed ρ).choose_spec⟩
  · rintro ⟨f, translation⟩
    exact term_translation_typed (translation (fun _ _ _ => Primrec.comp₀ .zero))

/-- A closed predicate has signature `σ` if and only if it translates to a `PRA.Formula σ.arity`
under every parameter assignment, with quantifier-free signatures yielding quantifier-free
formulas. -/
public theorem predicateTyping_iff_translation {E Ξ P σ} (valid : EnvironmentWF E) :
    PredicateTyping E Ξ [] P σ ↔
      ∃ A : FunctionAssignment Ξ.functions → PredicateAssignment Ξ.predicates → PRA.Formula σ.arity,
        ∀ ρ π, PredicateTranslation E Ξ ρ π 0 P σ (A ρ π) ∧
          (σ.sort = .qf → (A ρ π).QuantifierFree) := by
  constructor
  · intro typed
    classical
    exact ⟨fun ρ π => (predicate_translation_exists (n := 0) valid typed ρ π).choose,
      fun ρ π => ⟨(predicate_translation_exists (n := 0) valid typed ρ π).choose_spec,
        translation_qf (predicate_translation_exists (n := 0) valid typed ρ π).choose_spec⟩⟩
  · rintro ⟨A, translation⟩
    exact predicate_translation_typed (translation (fun _ _ _ => Primrec.comp₀ .zero)
      (fun _ _ _ => ⟨.false, fun _ => True.intro⟩)).1

/-- Every well-formed declaration in a well-formed environment has a `DeclarationTranslation`. For
theorem declarations, every translated instance is provable in first-order PRA. -/
public theorem declarationTranslation_correct {E d} (valid : EnvironmentWF E)
    (formed : DeclarationWF E d) : ∃ translated, DeclarationTranslation E d translated := by
  classical
  cases formed with
  | function body =>
      let f := fun ρ => (term_translation_exists (n := 0) valid body ρ).choose
      exact ⟨_, .function (f := f)
        (fun ρ => (term_translation_exists (n := 0) valid body ρ).choose_spec)⟩
  | predicate body =>
      let A := fun ρ π => (predicate_translation_exists (n := 0) valid body ρ π).choose
      exact ⟨_, .predicate (A := A)
        (fun ρ π => (predicate_translation_exists (n := 0) valid body ρ π).choose_spec)⟩
  | theoremE type body =>
      let A := fun ρ π => (predicate_translation_exists (n := 0) valid type ρ π).choose
      have translation := fun ρ π =>
        (predicate_translation_exists (n := 0) valid type ρ π).choose_spec
      exact ⟨_, .theoremE (A := A) translation
        (proofTranslation_sound valid body translation)⟩

end LeanPRA.Translation
