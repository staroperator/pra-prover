module

public import PRAProver.Metatheory.Core.Judgement.TermSubstitution

/-!
# Simultaneous replacement in predicate expressions

- `Predicate.replace` replaces locals, function parameters, and predicate parameters together.
- `Predicate.replace_subst` and `replace_rename` act on the supplied actuals.
- `Predicate.replace_beta_rename` inserts a fresh numerical argument after replacement.
- `Predicate.replace_id` recovers the original expression.
- `PredicateTyping.replace_instantiate` identifies replacement in a stored declaration body.

These syntax operations support the normalization proof.
-/

namespace PRAProver.Core

/-- Replace all three binding spaces at once in a single pass. -/
@[expose] public def Predicate.replace (s p : Subst) (q : Nat → Predicate) : Predicate → Predicate
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

private theorem lift_subst (s u : Subst) :
    (fun i => (Subst.lift 1 s i).subst (Subst.lift 1 u)) =
      Subst.lift 1 (fun i => (s i).subst u) := by
  funext i
  cases i <;> simp [Subst.lift, Term.subst, Term.subst_shift]

private theorem replace_subst (P : Predicate) (s p u : Subst) (q : Nat → Predicate) :
    (P.replace s p q).subst u = P.replace (fun i => (s i).subst u)
      (fun i => (p i).subst u) (fun i => (q i).subst u) := by
  induction P using Predicate.rec
    (motive_2 := fun ps => ∀ s p u q, (ps.map (Predicate.replace s p q)).map
      (Predicate.subst u) = ps.map (Predicate.replace (fun i => (s i).subst u)
        (fun i => (p i).subst u) (fun i => (q i).subst u)))
    generalizing s p u q <;>
    simp_all [Predicate.replace, Predicate.subst, Term.replace_subst, Term.subst_shift,
      Predicate.subst_shift, lift_subst, List.map_map]

private theorem replace_rename (P : Predicate) (s p : Subst) (q : Nat → Predicate)
    (r : Renaming) : (P.replace s p q).rename r = P.replace (fun i => (s i).rename r)
      (fun i => (p i).rename r) (fun i => (q i).rename r) := by
  have prename : ∀ P : Predicate, P.rename r = P.subst (fun i => .bvar (r i)) := by
    intro P
    simpa only [Predicate.subst_id, Term.rename] using Predicate.rename_subst P Term.bvar r
  have trename : ∀ t : Term, t.rename r = t.subst (fun i => .bvar (r i)) := by
    intro t
    simpa only [Term.subst_id, Term.rename] using Term.rename_subst t Term.bvar r
  simp only [prename, trename, replace_subst]

private theorem replace_beta (P : Predicate) (s p : Subst) (q : Nat → Predicate) (a : Term) :
    (P.replace (Subst.lift 1 s) (fun i => (p i).shift) (fun i => (q i).shift)).subst0 a =
      P.replace (fun | 0 => a | i + 1 => s i) p q := by
  simp only [Predicate.subst0, replace_subst]
  congr 1
  · funext i
    cases i with
    | zero => simp [Subst.lift, Term.subst]
    | succ i => exact Term.subst0_shift _ _
  · funext i; exact Term.subst0_shift _ _
  · funext i; exact Predicate.subst0_shift _ _

private theorem lift_rename (s : Subst) (r : Renaming) :
    (fun i => (Subst.lift 1 s i).rename (Renaming.lift 1 r)) =
      Subst.lift 1 (fun i => (s i).rename r) := by
  funext i
  cases i <;> simp [Subst.lift, Renaming.lift, Term.rename, Term.rename_shift]

private theorem replace_beta_rename (P : Predicate) (s p : Subst) (q : Nat → Predicate)
    (a : Term) (r : Renaming) :
    ((P.replace (Subst.lift 1 s) (fun i => (p i).shift) (fun i => (q i).shift)).rename
      (Renaming.lift 1 r)).subst0 a =
      P.replace (fun | 0 => a | i + 1 => (s i).rename r)
        (fun i => (p i).rename r) (fun i => (q i).rename r) := by
  rw [replace_rename, lift_rename]
  simp only [Term.rename_shift, Predicate.rename_shift]
  exact replace_beta _ _ _ _ _

private theorem lift_variables : Subst.lift 1 Term.bvar = Term.bvar := by
  funext i
  cases i <;> simp [Subst.lift, Term.shift, Term.rename]

private theorem replace_id (P : Predicate) :
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

private theorem replace_instantiate {E Ξ Γ P σ} (h : Theory.PredicateTyping E Ξ Γ P σ)
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

/-- Replacing a stored predicate body's parameters agrees with declaration instantiation. -/
public theorem Theory.PredicateTyping.replace_instantiate {E Ξ P σ}
    (h : Theory.PredicateTyping E Ξ [] P σ) (fs : List Term) (ps : List Predicate)
    (p : Subst) (q : Nat → Predicate)
    (functions : ∀ i j, Ξ.functions[i]? = some j → p i = fs[i]?.getD (.parameter i))
    (predicates : ∀ i j, Ξ.predicates[i]? = some j → q i = ps[i]?.getD (.parameter i)) :
    P.replace Term.bvar p q = P.instantiate fs ps := by
  apply PRAProver.Core.replace_instantiate h fs ps Term.bvar p q (by intros; rfl)
  · intro i j hi
    simpa only [List.length_nil, Term.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
      show (fun i : Nat => i) = id from rfl, Term.rename_id] using functions i j hi
  · intro i j hi
    simpa only [List.length_nil, Predicate.shift, Nat.not_lt_zero, ↓reduceIte, Nat.add_zero,
      show (fun i : Nat => i) = id from rfl, Predicate.rename_id] using predicates i j hi

/-- Local substitution acts once on each supplied actual after simultaneous replacement. -/
public theorem Predicate.replace_subst (P : Predicate) (s p u : Subst) (q : Nat → Predicate) :
    (P.replace s p q).subst u = P.replace (fun i => (s i).subst u)
      (fun i => (p i).subst u) (fun i => (q i).subst u) :=
  PRAProver.Core.replace_subst P s p u q

/-- Local renaming acts once on each supplied actual after replacement. -/
public theorem Predicate.replace_rename (P : Predicate) (s p : Subst) (q : Nat → Predicate)
    (r : Renaming) : (P.replace s p q).rename r = P.replace (fun i => (s i).rename r)
      (fun i => (p i).rename r) (fun i => (q i).rename r) :=
  PRAProver.Core.replace_rename P s p q r

/-- A replaced predicate binder may be renamed before its numerical actual is inserted. -/
public theorem Predicate.replace_beta_rename (P : Predicate) (s p : Subst) (q : Nat → Predicate)
    (a : Term) (r : Renaming) :
    ((P.replace (Subst.lift 1 s) (fun i => (p i).shift) (fun i => (q i).shift)).rename
      (Renaming.lift 1 r)).subst0 a =
      P.replace (fun | 0 => a | i + 1 => (s i).rename r)
        (fun i => (p i).rename r) (fun i => (q i).rename r) :=
  PRAProver.Core.replace_beta_rename P s p q a r

/-- Replacing every binding by its own variable leaves the predicate unchanged. -/
public theorem Predicate.replace_id (P : Predicate) :
    P.replace Term.bvar Term.parameter Predicate.parameter = P := PRAProver.Core.replace_id P

end PRAProver.Core
