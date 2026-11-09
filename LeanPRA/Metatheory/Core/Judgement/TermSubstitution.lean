module

public import LeanPRA.Metatheory.Core.Judgement.Substitution

/-!
# Simultaneous replacement of numerical bindings

- `Term.replace` replaces local variables and function parameters in one capture-avoiding pass.
- `Term.replace_subst` and `replace_rename` commute the result with local operations.
- `Term.replace_beta` removes the newest local after replacing the kept bindings.
- `Term.replace_id` supplies the unchanged term as the identity instance.
- `TermTyping.replace_instantiate` and `replace_instantiate_at` relate stored bodies to actuals.

Each binding is replaced in a single pass to support the normalization proofs.
-/

namespace LeanPRA.Core

/-- Simultaneously replace local variables and function parameters, shifting both under binders. -/
@[expose] public def Term.replace (s p : Subst) : Term → Term
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

private theorem lift_rename (s : Subst) (r : Renaming) :
    (fun i => (Subst.lift 1 s i).rename (Renaming.lift 1 r)) =
      Subst.lift 1 (fun i => (s i).rename r) := by
  funext i
  cases i <;> simp [Subst.lift, Renaming.lift, Term.rename, Term.rename_shift]

private theorem replace_beta_rename (t : Term) (s p : Subst) (a : Term) (r : Renaming) :
    ((t.replace (Subst.lift 1 s) (fun i => (p i).shift)).rename
      (Renaming.lift 1 r)).subst0 a =
      t.replace (fun | 0 => a | i + 1 => (s i).rename r) (fun i => (p i).rename r) := by
  rw [replace_rename, lift_rename]
  simp only [Term.rename_shift]
  exact replace_beta _ _ _ _

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

/-- Replacement agrees with declaration instantiation in a stored body's local context. -/
public theorem Theory.TermTyping.replace_instantiate_at {E Ξ Γ t k}
    (h : Theory.TermTyping E Ξ Γ t k) (fs : List Term) (s p : Subst)
    (locals : ∀ i j, Γ[i]? = some j → s i = .bvar i)
    (parameters : ∀ i j, Ξ.functions[i]? = some j →
      p i = (fs[i]?.getD (.parameter i)).shift Γ.length) :
    t.replace s p = t.instantiate fs Γ.length :=
  LeanPRA.Core.replace_instantiate h fs s p locals parameters

/-- A replaced binder can be renamed before its fresh numerical actual is inserted. -/
public theorem Term.replace_beta_rename (t : Term) (s p : Subst) (a : Term) (r : Renaming) :
    ((t.replace (Subst.lift 1 s) (fun i => (p i).shift)).rename
      (Renaming.lift 1 r)).subst0 a =
      t.replace (fun | 0 => a | i + 1 => (s i).rename r) (fun i => (p i).rename r) :=
  LeanPRA.Core.replace_beta_rename t s p a r

/-- Replacing a stored function body's parameters agrees with declaration instantiation. -/
public theorem Theory.TermTyping.replace_instantiate {E Ξ t k}
    (h : Theory.TermTyping E Ξ [] t k) (fs : List Term)
    (p : Subst) (parameters : ∀ i j, Ξ.functions[i]? = some j →
      p i = fs[i]?.getD (.parameter i)) : t.replace Term.bvar p = t.instantiate fs := by
  apply LeanPRA.Core.replace_instantiate h fs Term.bvar p (by intros; rfl)
  intro i j hi
  simpa only [List.length_nil, Term.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
    show (fun i : Nat => i) = id from rfl, Term.rename_id] using parameters i j hi

/-- Substitution acts on each supplied local or function actual after replacement. -/
public theorem Term.replace_subst (t : Term) (s p u : Subst) :
    (t.replace s p).subst u = t.replace (fun i => (s i).subst u) (fun i => (p i).subst u) :=
  LeanPRA.Core.replace_subst t s p u

/-- Renaming acts on each actual after simultaneous replacement. -/
public theorem Term.replace_rename (t : Term) (s p : Subst) (r : Renaming) :
    (t.replace s p).rename r = t.replace (fun i => (s i).rename r) (fun i => (p i).rename r) :=
  LeanPRA.Core.replace_rename t s p r

/-- Removing a replaced numerical binder inserts its actual and keeps all older bindings. -/
public theorem Term.replace_beta (t : Term) (s p : Subst) (a : Term) :
    (t.replace (Subst.lift 1 s) (fun i => (p i).shift)).subst0 a =
      t.replace (fun | 0 => a | i + 1 => s i) p := LeanPRA.Core.replace_beta t s p a

/-- Replacing both binding spaces by their own variables leaves the syntax unchanged. -/
public theorem Term.replace_id (t : Term) : t.replace Term.bvar Term.parameter = t :=
  LeanPRA.Core.replace_id t

end LeanPRA.Core
