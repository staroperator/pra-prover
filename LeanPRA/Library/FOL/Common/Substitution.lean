module

public import LeanPRA.Library.FOL.Common.Syntax

/-!
# Substitution in first-order terms and formulas

- `Term.subst f L t` replaces each variable of index `i` in term `t` by the term `f i`.
  `Term.subst_congr`, `Term.subst_comp`, and `Term.subst_id` give its congruence, composition,
  and identity laws.
- `Formula.substWithDepth f L A d` starts at binder depth `d` and increases it at each quantifier.
  Its constructor equations and composition law allow the replacements to depend on that depth.
  `Formula.subst` uses `FOL.liftSubst` to replace free variables without capturing them.
- `FOL.consSubst` adds a replacement for index zero. `FOL.shiftSubst` raises variable indices
  by a fixed amount.
- `Formula.instantiateAt` substitutes a term for a chosen surrounding variable.
  `Formula.instantiate` specializes this operation to position zero, as needed to open a quantifier.
- `Formula.shift_neg` and `Formula.instantiate_neg` show that shifting and instantiation commute
  with negation.
-/

@[expose] public section

pra

namespace FOL

namespace Term

/--
`Term.subst f L t` simultaneously substitutes terms for variables in term code `t` in language
code `L`. `f i` supplies the term code for variable index `i`, inserted unchanged.
Constants and function symbols are preserved.
-/
def subst (f : Nat → Nat) : Nat → Nat → Nat :=
  fun L => rec f (const L) (app L) L

theorem subst_const (f : Nat → Nat) : ∀ L j, Language.IsConstant L j →
    subst f L (const L j) = const L j := fun L j h => rec_const f (const L) (app L) L j h

theorem subst_var (f : Nat → Nat) : ∀ L i, subst f L (var L i) = f i :=
  fun L i => rec_var f (const L) (app L) L i

theorem subst_app (f : Nat → Nat) : ∀ L j args, Language.IsFunction L j →
    subst f L (app L j args) =
      app L j (Tuple.map (subst f L) (Language.functionSymbolArity L j) args) :=
  fun L j args hj => rec_app f (const L) (app L) L j args hj

theorem subst_app_one (f : Nat → Nat) : ∀ L j t,
    Language.IsFunction L j → Language.functionSymbolArity L j = 1 →
    subst f L (app L j t) = app L j (subst f L t) :=
  fun L j t hj ha => rec_app_one f (const L) (app L) L j t hj ha

theorem subst_app_two (f : Nat → Nat) : ∀ L j t u,
    Language.IsFunction L j → Language.functionSymbolArity L j = 2 →
    subst f L (app L j (pair t u)) = app L j (pair (subst f L t) (subst f L u)) :=
  fun L j t u hj ha => rec_app_two f (const L) (app L) L j t u hj ha

/--
`Term.shift L d t` returns the term code obtained by raising every variable index in term
code `t` by `d`, in language code `L`.
-/
def shift : Nat → Nat → Nat → Nat := fun L d => subst (fun n => var L (n + d)) L

/--
`Term.instantiateAt L k t d n` gives the replacement term code for variable index `n` at binder
depth `d`, when surrounding position `k` is replaced by term code `t` in language code `L`.
Indices below `d` keep their values. Surrounding position `k` receives `t` shifted by `d`, and
later positions move down by one.
-/
def instantiateAt : Nat → Nat → Nat → Nat → Nat → Nat := fun L k t d n =>
  ite (ltb n d) (var L n)
    (ite (eqb (n - d) k) (shift L d t)
      (var L (ite (ltb k (n - d)) (pred n) n)))

/-- Equal replacement values produce equal substituted term codes. -/
theorem subst_congr (f g : Nat → Nat) : ∀ L,
    (∀ i, f i = g i) → ∀ t, subst f L t = subst g L t := by
  intro L h
  apply induction_eq (subst f L) (subst g L) L
  · intro j hj
    rw [subst_const f L j hj, subst_const g L j hj]
  · intro i
    rw [subst_var f, subst_var g]
    exact h i
  · intro j args hj ih
    rw [subst_app f L j args hj, subst_app g L j args hj]
    apply eq_congr (app L j)
    apply Tuple.map_congr_of_get_eq (subst f L) (subst g L)
    intro i hi
    exact ih i hi

/-- Substituting twice composes the replacement functions on variable indices. -/
theorem subst_comp (f g : Nat → Nat) : ∀ L t,
    subst f L (subst g L t) = subst (fun i => subst f L (g i)) L t := by
  intro L
  apply induction_eq (fun t => subst f L (subst g L t))
    (subst (fun i => subst f L (g i)) L) L
  · intro j hj
    exact eq_trans (eq_congr (subst f L) (subst_const g L j hj))
      (eq_trans (subst_const f L j hj)
        (eq_symm (subst_const (fun i => subst f L (g i)) L j hj)))
  · intro i
    exact eq_trans (eq_congr (subst f L) (subst_var g L i))
      (eq_symm (subst_var (fun i => subst f L (g i)) L i))
  · intro j args hj ih
    have entries : Tuple.map (fun t => subst f L (subst g L t))
        (Language.functionSymbolArity L j) args =
        Tuple.map (subst (fun i => subst f L (g i)) L)
          (Language.functionSymbolArity L j) args := by
      apply Tuple.map_congr_of_get_eq
        (fun t => subst f L (subst g L t)) (subst (fun i => subst f L (g i)) L)
      intro i hi
      exact ih i hi
    exact eq_trans (eq_congr (subst f L) (subst_app g L j args hj))
      (eq_trans (subst_app f L j
        (Tuple.map (subst g L) (Language.functionSymbolArity L j) args) hj)
        (eq_trans (eq_congr (app L j)
          (eq_trans (Tuple.map_map (subst f L) (subst g L)
            (Language.functionSymbolArity L j) args) entries))
          (eq_symm (subst_app (fun i => subst f L (g i)) L j args hj))))

/-- Replacing each variable by itself preserves every term code. -/
theorem subst_id : ∀ L t, subst (var L) L t = t := by
  intro L
  apply induction_eq (subst (var L) L) (fun t => t) L
  · intro j hj
    exact subst_const (var L) L j hj
  · intro i
    exact subst_var (var L) L i
  · intro j args hj ih
    rw [subst_app (var L) L j args hj]
    apply eq_congr (app L j)
    have h : Tuple.map (subst (var L) L) (Language.functionSymbolArity L j) args =
        Tuple.map (fun t => t) (Language.functionSymbolArity L j) args := by
      apply Tuple.map_congr_of_get_eq (subst (var L) L) (fun t => t)
      intro i hi
      exact ih i hi
    have hi : Tuple.map (fun t => t) (Language.functionSymbolArity L j) args = args := by
      rw [Language.functionSymbolArity, Tuple.map_id]
    exact eq_trans h hi

theorem shift_var : ∀ L d i, shift L d (var L i) = var L (i + d) :=
  fun L d i => subst_var (fun j => var L (j + d)) L i

/-- A substitution that sends each variable to a code at least as large does not make a term
code smaller. -/
theorem le_subst (h : Nat → Nat) : ∀ L, (∀ n, var L n ≤ h n) → ∀ s, s ≤ subst h L s := by
  intro L hv
  apply induction_of_bool (fun s => s ≤ subst h L s) (fun s => leb s (subst h L s)) L
  · intro s
    constructor
    · intro hs
      exact and_left (leb_eq_one s (subst h L s))
        (and_right (bool_eq_one (leb s (subst h L s)) (leb_bool s (subst h L s))) hs)
    · intro hs
      exact and_left (bool_eq_one (leb s (subst h L s)) (leb_bool s (subst h L s)))
        (and_right (leb_eq_one s (subst h L s)) hs)
  · intro j hj
    rw [subst_const h L j hj]
    exact le_refl (const L j)
  · intro i
    rw [subst_var h]
    exact hv i
  · intro j args hj ih
    rw [subst_app h L j args hj]
    apply app_mono L j args (Tuple.map (subst h L) (Language.functionSymbolArity L j) args)
    have hm := Tuple.map_mono (fun t => t) (subst h L) (Language.functionSymbolArity L j) args
      (fun i hi => ih i hi)
    have he : Tuple.map (fun t => t) (Language.functionSymbolArity L j) args = args := by
      rw [Language.functionSymbolArity, Tuple.map_id]
    exact eq_subst (fun z => z ≤ Tuple.map (subst h L) (Language.functionSymbolArity L j) args)
      he hm

/-- Shifting a term never decreases its code. -/
theorem le_shift : ∀ L d t, t ≤ shift L d t :=
  fun L d t => le_subst (fun n => var L (n + d)) L (fun n => var_mono L n d) t

theorem shift_zero : ∀ L t, shift L 0 t = t := by
  intro L t
  have h := subst_congr (fun i => var L (i + 0)) (var L) L
    (fun i => eq_congr (var L) (add_zero i)) t
  exact eq_trans h (subst_id L t)

theorem shift_shift : ∀ L d e t, shift L d (shift L e t) = shift L (e + d) t := by
  intro L d e t
  let f := fun i => var L (i + d)
  let g := fun i => var L (i + e)
  have h : ∀ i, subst f L (g i) = var L (i + (e + d)) := by
    intro i
    rw [subst_var f, add_assoc]
  exact eq_trans (subst_comp f g L t)
    (subst_congr (fun i => subst f L (g i)) (fun i => var L (i + (e + d))) L h t)

theorem instantiateAt_below (L t d i : Nat) : i < d →
    instantiateAt L 0 t d i = var L i := by
  intro h
  rw [instantiateAt, and_right (ltb_eq_one i d) h, ite_succ]

theorem instantiateAt_above (L t d i : Nat) : d ≤ i →
    instantiateAt L 0 t d (S i) = var L i := by
  intro h
  have hi : d ≤ S i := le_trans d i (S i) h (le_succ_self i)
  have hs : S i - d = S (i - d) := succ_sub_of_le i d h
  rw [instantiateAt, ltb_eq_zero_of_ge (S i) d hi, ite_zero, hs,
    and_right (eqb_eq_zero (S (i - d)) 0) (succ_ne_zero (i - d)), ite_zero,
    and_right (ltb_eq_one 0 (S (i - d)))
      (and_right (lt_succ 0 (i - d)) (zero_le (i - d))), ite_succ, pred_succ]

end Term

/-- `consSubst t f` sends position zero to term code `t` and position `i + 1` to `f i`.
It extends the replacement function `f` with one entry at the front. -/
def consSubst (t : Nat) (f : Nat → Nat) : Nat → Nat := fun i => ite i (f (pred i)) t

theorem consSubst_zero (t : Nat) (f : Nat → Nat) : consSubst t f 0 = t := rfl

theorem consSubst_succ (t : Nat) (f : Nat → Nat) : ∀ i, consSubst t f (S i) = f i := fun i => rfl

theorem consSubst_congr (f g : Nat → Nat) : (∀ i, f i = g i) → ∀ t i,
    consSubst t f i = consSubst t g i := by
  intro h t i
  rcases zero_or_succ_pred i with hi | hi
  · rw [hi, consSubst_zero t f, consSubst_zero t g]
  · rw [hi, consSubst_succ t f, consSubst_succ t g]
    exact h (pred i)

/-- A substitution with one more value in front has the same positions one place later. -/
theorem consSubst_tail (t : Nat) (f : Nat → Nat) : ∀ L d e, (∀ i, f (i + d) = Term.var L (i + e)) →
    ∀ i, consSubst t f (i + S d) = Term.var L (i + e) := by
  intro L d e h i
  rw [add_succ, consSubst_succ t f]
  exact h i

/-- `shiftSubst L k i` is the code of variable `i + k` in language `L`.
The replacement function `shiftSubst L k` raises every variable index by `k`; at `k = 0`, it
replaces each variable by itself. Applying `Term.subst` with this function shifts a term. -/
def shiftSubst (L k : Nat) : Nat → Nat := fun i => Term.var L (i + k)

theorem shiftSubst_zero : ∀ L i, shiftSubst L 0 i = Term.var L i := by
  intro L i
  rw [shiftSubst, add_zero]

/-- The positions from `d` on of `shiftSubst L o` are the positions from `d + o` on. -/
theorem shiftSubst_tail : ∀ L o d i, shiftSubst L o (i + d) = Term.var L (i + (d + o)) := by
  intro L o d i
  rw [shiftSubst, add_assoc]

theorem consSubst_shiftSubst : ∀ L k i,
    consSubst (Term.var L k) (shiftSubst L (S k)) i = shiftSubst L k i := by
  intro L k i
  rcases zero_or_succ_pred i with h | h
  · rw [h, consSubst_zero (Term.var L k) (shiftSubst L (S k)), shiftSubst, zero_add]
  · rw [h, consSubst_succ (Term.var L k) (shiftSubst L (S k)), shiftSubst, shiftSubst,
      add_succ, succ_add]

/-- `liftSubst f L d` extends substitution `f` beneath `d` bound variables in language `L`.
Indices below `d` stay fixed. At index `i + d`, the replacement is `f i` shifted by `d`. -/
def liftSubst (f : Nat → Nat) : Nat → Nat → Nat → Nat := fun L d i =>
  ite (ltb i d) (Term.var L i) (Term.shift L d (f (i - d)))

theorem liftSubst_of_lt (f : Nat → Nat) : ∀ L d i, i < d →
    liftSubst f L d i = Term.var L i := by
  intro L d i h
  rw [liftSubst, and_right (ltb_eq_one i d) h, ite_succ]

theorem liftSubst_of_le (f : Nat → Nat) : ∀ L d i, d ≤ i →
    liftSubst f L d i = Term.shift L d (f (i - d)) := by
  intro L d i h
  rw [liftSubst, ltb_eq_zero_of_ge i d h, ite_zero]

theorem liftSubst_add (f : Nat → Nat) : ∀ L d i,
    liftSubst f L d (i + d) = Term.shift L d (f i) := by
  intro L d i
  rw [liftSubst_of_le f L d (i + d) (le_add_left i d), add_sub_self_right]

theorem liftSubst_id : ∀ L d i, liftSubst (Term.var L) L d i = Term.var L i := by
  intro L d i
  by_cases h : i < d
  · exact liftSubst_of_lt (Term.var L) L d i h
  · have hd : d ≤ i := le_of_not_lt d i h
    rw [liftSubst_of_le (Term.var L) L d i hd, Term.shift_var, sub_add_cancel_of_le i d hd]

theorem liftSubst_zero (f : Nat → Nat) : ∀ L i, liftSubst f L 0 i = f i := by
  intro L i
  rw [liftSubst_of_le f L 0 i (zero_le i), sub_zero, Term.shift_zero]

theorem liftSubst_one (f : Nat → Nat) : ∀ L i,
    liftSubst f L 1 i = consSubst (Term.var L 0) (fun j => Term.shift L 1 (f j)) i := by
  intro L i
  rcases zero_or_succ_pred i with h | h
  · rw [h, liftSubst_of_lt f L 1 0 (lt_succ_self 0),
      consSubst_zero (Term.var L 0) (fun j => Term.shift L 1 (f j))]
  · have hi : 1 ≤ S (pred i) := and_right (succ_le_succ 0 (pred i)) (zero_le (pred i))
    rw [h, liftSubst_of_le f L 1 (S (pred i)) hi, succ_sub_succ, sub_zero,
      consSubst_succ (Term.var L 0) (fun j => Term.shift L 1 (f j))]

theorem liftSubst_liftSubst (f : Nat → Nat) : ∀ L d e i,
    liftSubst (liftSubst f L e) L d i = liftSubst f L (d + e) i := by
  intro L d e i
  by_cases hd : i < d
  · have hde := lt_of_lt_of_le i d (d + e) hd (le_add_right d e)
    rw [liftSubst_of_lt (liftSubst f L e) L d i hd,
      liftSubst_of_lt f L (d + e) i hde]
  · have hid := le_of_not_lt d i hd
    by_cases he : i - d < e
    · have hie := and_left (sub_lt_iff i d e hid) he
      rw [liftSubst_of_le (liftSubst f L e) L d i hid,
        liftSubst_of_lt f L e (i - d) he, Term.shift_var, sub_add_cancel_of_le i d hid,
        liftSubst_of_lt f L (d + e) i hie]
    · have hei := le_of_not_lt e (i - d) he
      have hde : d + e ≤ i := by
        apply le_of_not_lt (d + e) i
        intro h
        exact he (and_right (sub_lt_iff i d e hid) h)
      rw [liftSubst_of_le (liftSubst f L e) L d i hid,
        liftSubst_of_le f L e (i - d) hei,
        liftSubst_of_le f L (d + e) i hde, Term.shift_shift, add_comm e d, sub_add]

/-- Suppose `f` sends each position from `d` on to the position `e - d` places later. Beneath
`k` binders the lifted substitution does the same from `d + k` on. -/
theorem liftSubst_tail (f : Nat → Nat) : ∀ L d e, (∀ i, f (i + d) = Term.var L (i + e)) →
    ∀ k i, liftSubst f L k (i + (d + k)) = Term.var L (i + (e + k)) := by
  intro L d e h k i
  have regroup : i + (d + k) = i + d + k := eq_symm (add_assoc i d k)
  rw [regroup, liftSubst_add f L k (i + d), h i, Term.shift_var L k (i + e), add_assoc i e k]

namespace Term

theorem subst_liftSubst_shift (f : Nat → Nat) : ∀ L d t,
    subst (liftSubst f L d) L (shift L d t) = shift L d (subst f L t) := by
  intro L d t
  let s := fun i => var L (i + d)
  have pointwise : ∀ i, subst (liftSubst f L d) L (s i) = subst s L (f i) := by
    intro i
    exact eq_trans (subst_var (liftSubst f L d) L (i + d)) (liftSubst_add f L d i)
  exact eq_trans (subst_comp (liftSubst f L d) s L t)
    (eq_trans (subst_congr (fun i => subst (liftSubst f L d) L (s i))
      (fun i => subst s L (f i)) L pointwise t) (eq_symm (subst_comp s f L t)))

theorem subst_consSubst (f g : Nat → Nat) : ∀ L t i,
    subst f L (consSubst t g i) = consSubst (subst f L t) (fun j => subst f L (g j)) i := by
  intro L t i
  rcases zero_or_succ_pred i with h | h
  · rw [h, consSubst_zero t g, consSubst_zero (subst f L t) (fun j => subst f L (g j))]
  · rw [h, consSubst_succ t g, consSubst_succ (subst f L t) (fun j => subst f L (g j))]

theorem subst_shiftSubst (f : Nat → Nat) : ∀ L k i,
    subst f L (shiftSubst L k i) = f (i + k) := by
  intro L k i
  exact subst_var f L (i + k)

theorem instantiateAt_eq_liftSubst : ∀ L t d i,
    instantiateAt L 0 t d i = liftSubst (consSubst t (shiftSubst L 0)) L d i := by
  intro L t d i
  by_cases hlt : i < d
  · rw [instantiateAt_below L t d i hlt,
      liftSubst_of_lt (consSubst t (shiftSubst L 0)) L d i hlt]
  · have hle := le_of_not_lt d i hlt
    by_cases he : i = d
    · rw [he, instantiateAt, ltb_eq_zero_of_ge d d (le_refl d), ite_zero, sub_self,
        eqb_self, ite_succ, liftSubst_of_le (consSubst t (shiftSubst L 0)) L d d (le_refl d),
        sub_self, consSubst_zero t (shiftSubst L 0)]
    · have hdi : d < i := by
        rcases lt_or_eq_of_le d i hle with h | h
        · exact h
        · exact false_elim (he (eq_symm h))
      have hi := ne_zero_of_pos i (lt_of_le_of_lt 0 d i (zero_le d) hdi)
      have hd : d ≤ pred i := by
        rw [← succ_pred i hi] at hdi
        exact and_left (lt_succ d (pred i)) hdi
      rw [← succ_pred i hi, instantiateAt_above L t d (pred i) hd,
        liftSubst_of_le (consSubst t (shiftSubst L 0)) L d (S (pred i))
          (le_trans d (pred i) (S (pred i)) hd (le_succ_self (pred i))),
        succ_sub_of_le (pred i) d hd, consSubst_succ t (shiftSubst L 0), shiftSubst_zero,
        shift_var, sub_add_cancel_of_le (pred i) d hd]

theorem subst_consSubst_congr (f g h : Nat → Nat) : ∀ L t u,
    subst f L t = u → (∀ i, subst f L (g i) = h i) → ∀ i,
      subst f L (consSubst t g i) = consSubst u h i := by
  intro L t u ht hh i
  rw [subst_consSubst f g, ht]
  exact consSubst_congr (fun j => subst f L (g j)) h hh u i

theorem subst_shiftSubst_zero (f : Nat → Nat) : ∀ L i,
    subst f L (shiftSubst L 0 i) = f i := by
  intro L i
  rw [subst_shiftSubst f, add_zero]

theorem subst_shiftSubst_succ_consSubst (t : Nat) (f : Nat → Nat) : ∀ L k i,
    subst (consSubst t f) L (shiftSubst L (S k) i) = subst f L (shiftSubst L k i) := by
  intro L k i
  rw [subst_shiftSubst (consSubst t f), add_succ, consSubst_succ t f, subst_shiftSubst f]

theorem subst_shiftSubst_shiftSubst : ∀ L m n i,
    subst (shiftSubst L m) L (shiftSubst L n i) = shiftSubst L (n + m) i := by
  intro L m n i
  rw [subst_shiftSubst (shiftSubst L m), shiftSubst, shiftSubst, add_assoc]

/-- Substituting for position `0` after raising every position by one gives the term back. -/
theorem subst_consSubst_shift (t : Nat) : ∀ L s,
    subst (consSubst t (shiftSubst L 0)) L (shift L 1 s) = s := by
  intro L s
  exact eq_trans (subst_comp (consSubst t (shiftSubst L 0)) (fun n => var L (n + 1)) L s)
    (eq_trans
      (subst_congr (fun i => subst (consSubst t (shiftSubst L 0)) L (var L (i + 1))) (var L) L
        (fun i => eq_trans (subst_var (consSubst t (shiftSubst L 0)) L (i + 1))
          (shiftSubst_zero L i))
        s)
      (subst_id L s))

theorem shift_eq_subst_shiftSubst : ∀ L d t, shift L d t = subst (shiftSubst L d) L t :=
  fun L d t => rfl

/-- Lifting beneath no binder leaves a substitution as it is. -/
theorem subst_liftSubst_zero (f : Nat → Nat) : ∀ L t,
    subst (liftSubst f L 0) L t = subst f L t :=
  fun L t => subst_congr (liftSubst f L 0) f L (liftSubst_zero f L) t

theorem subst_liftSubst_shiftSubst (f : Nat → Nat) : ∀ L d e, (∀ i, f (i + d) = var L (i + e)) →
    ∀ k i, subst (liftSubst f L k) L (shiftSubst L (d + k) i) = shiftSubst L (e + k) i := by
  intro L d e h k i
  exact eq_trans (subst_shiftSubst (liftSubst f L k) L (d + k) i) (liftSubst_tail f L d e h k i)

/-- A term written outside `d` binders and raised past them and `k` more is raised past `e + k`
binders after a substitution that sends the positions from `d` on to those from `e` on. -/
theorem subst_liftSubst_shift_outer (f : Nat → Nat) : ∀ L d e, (∀ i, f (i + d) = var L (i + e)) →
    ∀ k t, subst (liftSubst f L k) L (shift L (d + k) t) = shift L (e + k) t := by
  intro L d e h k t
  rw [shift_eq_subst_shiftSubst L (d + k) t, shift_eq_subst_shiftSubst L (e + k) t]
  exact eq_trans (subst_comp (liftSubst f L k) (shiftSubst L (d + k)) L t)
    (subst_congr (fun i => subst (liftSubst f L k) L (shiftSubst L (d + k) i))
      (shiftSubst L (e + k)) L (subst_liftSubst_shiftSubst f L d e h k) t)

/-- Raising a term past `n` binders may be skipped when `n` is zero. -/
theorem ite_shift : ∀ L n t, ite n (shift L n t) t = shift L n t := by
  intro L n t
  rcases zero_or_succ_pred n with h | h
  · rw [h, ite_zero, shift_zero]
  · rw [h, ite_succ]

/-- `subst_liftSubst_shift_outer` for the form in which a quotation raises a spliced term. -/
theorem subst_liftSubst_outer (f : Nat → Nat) : ∀ L d e, (∀ i, f (i + d) = var L (i + e)) →
    ∀ k t, subst (liftSubst f L k) L (ite (d + k) (shift L (d + k) t) t) =
      ite (e + k) (shift L (e + k) t) t := by
  intro L d e h k t
  rw [ite_shift L (d + k) t, ite_shift L (e + k) t]
  exact subst_liftSubst_shift_outer f L d e h k t

end Term

theorem liftSubst_comp (f g : Nat → Nat) : ∀ L d i,
    Term.subst (liftSubst f L d) L (liftSubst g L d i) =
      liftSubst (fun j => Term.subst f L (g j)) L d i := by
  intro L d i
  by_cases h : i < d
  · rw [liftSubst_of_lt g L d i h, Term.subst_var (liftSubst f L d),
      liftSubst_of_lt f L d i h, liftSubst_of_lt (fun j => Term.subst f L (g j)) L d i h]
  · have hd : d ≤ i := le_of_not_lt d i h
    rw [liftSubst_of_le g L d i hd, Term.subst_liftSubst_shift f,
      liftSubst_of_le (fun j => Term.subst f L (g j)) L d i hd]

namespace Formula

/--
`Formula.substWithDepth f L A d` replaces variables in formula code `A` in language code `L`,
starting at binder depth `d`. `f k i` supplies a term code for variable index `i` at the
current depth `k`. Each quantifier increases `k` by one. The replacement function `f`
determines how bound variables are treated.
-/
def substWithDepth (f : Nat → Nat → Nat) : Nat → Nat → Nat → Nat := fun L =>
  recWithDepth (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L

theorem substWithDepth_falsum (f : Nat → Nat → Nat) : ∀ L d,
    substWithDepth f L falsum d = falsum :=
  fun L d => recWithDepth_falsum (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L d

theorem substWithDepth_equal (f : Nat → Nat → Nat) : ∀ L t s d,
    substWithDepth f L (equal L t s) d = equal L (Term.subst (f d) L t) (Term.subst (f d) L s) :=
  fun L t s d => recWithDepth_equal (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L t s d

theorem substWithDepth_rel (f : Nat → Nat → Nat) : ∀ L j xs d, Language.IsRelation L j →
    substWithDepth f L (rel L j xs) d =
      rel L j (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs) :=
  fun L j xs d hj => recWithDepth_rel (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L j xs d hj

theorem substWithDepth_imp (f : Nat → Nat → Nat) : ∀ L A B d,
    substWithDepth f L (imp A B) d = imp (substWithDepth f L A d) (substWithDepth f L B d) :=
  fun L A B d => recWithDepth_imp (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L A B d

theorem substWithDepth_all (f : Nat → Nat → Nat) : ∀ L A d,
    substWithDepth f L (all A) d = all (substWithDepth f L A (S d)) :=
  fun L A d => recWithDepth_all (fun _ => falsum)
    (fun d t s => equal L (Term.subst (f d) L t) (Term.subst (f d) L s))
    (fun d j xs => rel L j
      (Tuple.map (Term.subst (f d) L) (Language.relationSymbolArity L j) xs))
    (fun _ x y => imp x y) (fun _ x => all x) L A d

/--
`Formula.instantiateAt L k A t` substitutes term code `t` for surrounding position `k` in
formula code `A`, in language code `L`. Indices referring to inner binders and earlier
surrounding positions keep their values. Beneath a binder, `t` is shifted to avoid capture.
Later surrounding positions move down by one.
-/
def instantiateAt : Nat → Nat → Nat → Nat → Nat :=
  fun L k A t => substWithDepth (Term.instantiateAt L k t) L A 0

/--
`Formula.instantiate L A t` instantiates the body formula code `A` with term code `t` in language
code `L`. It replaces surrounding position `0`, lifts `t` beneath inner binders, and lowers later
positions by one. Thus `A` is the body passed to `Formula.all` for universal instantiation.
-/
def instantiate : Nat → Nat → Nat → Nat := fun L A t => instantiateAt L 0 A t

/--
`Formula.shift L A` returns the formula code obtained by raising each surrounding variable
position in formula code `A` by one, in language code `L`. Indices referring to binders
inside `A` are preserved.
-/
def shift : Nat → Nat → Nat := fun L A =>
  substWithDepth (fun d n => Term.var L (ite (ltb n d) n (S n))) L A 0

/--
`Formula.successorInstance L successor A` replaces surrounding position `0` in formula code `A`
by its successor, preserving other positions. `L` is a language code, and `successor`
is a function symbol index below `Language.functionCount L` with arity `1`.
-/
def successorInstance : Nat → Nat → Nat → Nat := fun L successor A =>
  substWithDepth
    (fun d n => ite (eqb n d) (Term.app L successor (Term.var L n)) (Term.var L n)) L A 0

/-- Formula substitution respects pointwise equality at each binder depth and variable index. -/
theorem substWithDepth_congr (f g : Nat → Nat → Nat) : ∀ L,
    (∀ d i, f d i = g d i) → ∀ A d, substWithDepth f L A d = substWithDepth g L A d := by
  intro L h
  apply induction_eq (substWithDepth f L) (substWithDepth g L) L
  · intro d
    exact eq_trans (substWithDepth_falsum f L d) (eq_symm (substWithDepth_falsum g L d))
  · intro t u d
    exact eq_trans (substWithDepth_equal f L t u d)
      (eq_trans (eq_congr₂ (equal L)
        (Term.subst_congr (f d) (g d) L (h d) t)
        (Term.subst_congr (f d) (g d) L (h d) u))
        (eq_symm (substWithDepth_equal g L t u d)))
  · intro j xs d hj
    exact eq_trans (substWithDepth_rel f L j xs d hj)
      (eq_trans (eq_congr (rel L j)
        (Tuple.map_congr (Term.subst (f d) L) (Term.subst (g d) L)
          (Term.subst_congr (f d) (g d) L (h d)) (Language.relationSymbolArity L j) xs))
        (eq_symm (substWithDepth_rel g L j xs d hj)))
  · intro A B d hA hB
    exact eq_trans (substWithDepth_imp f L A B d)
      (eq_trans (eq_congr₂ imp hA hB) (eq_symm (substWithDepth_imp g L A B d)))
  · intro A d hA
    exact eq_trans (substWithDepth_all f L A d)
      (eq_trans (eq_congr all hA) (eq_symm (substWithDepth_all g L A d)))

/-- Nested substitutions compose their replacement terms at the same quantifier depth. -/
theorem substWithDepth_comp (f g : Nat → Nat → Nat) : ∀ L A d,
    substWithDepth f L (substWithDepth g L A d) d =
      substWithDepth (fun e i => Term.subst (f e) L (g e i)) L A d := by
  intro L
  let h := fun e i => Term.subst (f e) L (g e i)
  apply induction_eq (fun A d => substWithDepth f L (substWithDepth g L A d) d)
    (substWithDepth h L) L
  · intro d
    exact eq_trans (eq_congr (fun A => substWithDepth f L A d) (substWithDepth_falsum g L d))
      (eq_trans (substWithDepth_falsum f L d) (eq_symm (substWithDepth_falsum h L d)))
  · intro t u d
    exact eq_trans (eq_congr (fun A => substWithDepth f L A d) (substWithDepth_equal g L t u d))
      (eq_trans (substWithDepth_equal f L (Term.subst (g d) L t) (Term.subst (g d) L u) d)
        (eq_trans (eq_congr₂ (equal L)
          (Term.subst_comp (f d) (g d) L t) (Term.subst_comp (f d) (g d) L u))
          (eq_symm (substWithDepth_equal h L t u d))))
  · intro j xs d hj
    have entries := Tuple.map_congr (fun t => Term.subst (f d) L (Term.subst (g d) L t))
      (Term.subst (h d) L) (Term.subst_comp (f d) (g d) L)
      (Language.relationSymbolArity L j) xs
    exact eq_trans (eq_congr (fun A => substWithDepth f L A d) (substWithDepth_rel g L j xs d hj))
      (eq_trans (substWithDepth_rel f L j
        (Tuple.map (Term.subst (g d) L) (Language.relationSymbolArity L j) xs) d hj)
        (eq_trans (eq_congr (rel L j)
          (eq_trans (Tuple.map_map (Term.subst (f d) L) (Term.subst (g d) L)
            (Language.relationSymbolArity L j) xs) entries))
          (eq_symm (substWithDepth_rel h L j xs d hj))))
  · intro A B d hA hB
    exact eq_trans (eq_congr (fun C => substWithDepth f L C d) (substWithDepth_imp g L A B d))
      (eq_trans (substWithDepth_imp f L (substWithDepth g L A d) (substWithDepth g L B d) d)
        (eq_trans (eq_congr₂ imp hA hB) (eq_symm (substWithDepth_imp h L A B d))))
  · intro A d hA
    exact eq_trans (eq_congr (fun C => substWithDepth f L C d) (substWithDepth_all g L A d))
      (eq_trans (substWithDepth_all f L (substWithDepth g L A (S d)) d)
        (eq_trans (eq_congr all hA) (eq_symm (substWithDepth_all h L A d))))

/-- A substitution that preserves every variable index preserves every formula code. -/
theorem substWithDepth_id : ∀ L A d, substWithDepth (fun _ i => Term.var L i) L A d = A := by
  intro L
  let f := fun _ i => Term.var L i
  apply induction_eq (substWithDepth f L) (fun A _ => A) L
  · intro d
    exact substWithDepth_falsum f L d
  · intro t u d
    exact eq_trans (substWithDepth_equal f L t u d)
      (eq_congr₂ (equal L) (Term.subst_id L t) (Term.subst_id L u))
  · intro j xs d hj
    rw [substWithDepth_rel f L j xs d hj]
    apply eq_congr (rel L j)
    have h := Tuple.map_congr (Term.subst (Term.var L) L) (fun t => t)
      (Term.subst_id L) (Language.relationSymbolArity L j) xs
    exact eq_trans h (Tuple.map_id _ xs)
  · intro A B d hA hB
    rw [substWithDepth_imp f, hA, hB]
  · intro A d hA
    rw [substWithDepth_all f, hA]

/-- `Formula.subst f L A` simultaneously replaces each free variable `i` in formula code `A`
with the term code `f i`. Beneath quantifiers, bound variables stay fixed and replacement terms
are shifted to avoid capture. -/
def subst (f : Nat → Nat) : Nat → Nat → Nat := fun L A =>
  substWithDepth (FOL.liftSubst f L) L A 0

theorem subst_comp (f g : Nat → Nat) : ∀ L A,
    subst f L (subst g L A) = subst (fun i => Term.subst f L (g i)) L A := by
  intro L A
  exact eq_trans (substWithDepth_comp (FOL.liftSubst f L) (FOL.liftSubst g L) L A 0)
    (substWithDepth_congr
      (fun d i => Term.subst (FOL.liftSubst f L d) L (FOL.liftSubst g L d i))
      (FOL.liftSubst (fun i => Term.subst f L (g i)) L) L
      (FOL.liftSubst_comp f g L) A 0)

theorem subst_id : ∀ L A, subst (Term.var L) L A = A := by
  intro L A
  exact eq_trans (substWithDepth_congr (FOL.liftSubst (Term.var L) L) (fun _ i => Term.var L i)
    L (FOL.liftSubst_id L) A 0) (substWithDepth_id L A 0)

/-- Substituting for a newly inserted position leaves the original formula unchanged. -/
theorem instantiate_shift : ∀ L A t, instantiate L (shift L A) t = A := by
  intro L A t
  let f := FOL.Term.instantiateAt L 0 t
  let g := fun d i => FOL.Term.var L (ite (ltb i d) i (S i))
  have pointwise : ∀ d i,
      FOL.Term.subst (f d) L (g d i) = FOL.Term.var L i := by
    intro d i
    rw [FOL.Term.subst_var (f d)]
    by_cases h : i < d
    · rw [and_right (ltb_eq_one i d) h, ite_succ]
      exact FOL.Term.instantiateAt_below L t d i h
    · have hle := le_of_not_lt d i h
      rw [ltb_eq_zero_of_ge i d hle, ite_zero]
      exact FOL.Term.instantiateAt_above L t d i hle
  exact eq_trans (substWithDepth_comp f g L A 0)
    (eq_trans (substWithDepth_congr (fun d i => FOL.Term.subst (f d) L (g d i))
      (fun _ i => FOL.Term.var L i) L pointwise A 0) (substWithDepth_id L A 0))

theorem subst_congr (f g : Nat → Nat) : ∀ L,
    (∀ i, f i = g i) → ∀ A, subst f L A = subst g L A := by
  intro L h A
  apply substWithDepth_congr (FOL.liftSubst f L) (FOL.liftSubst g L) L
  intro d i
  change ite (ltb i d) (FOL.Term.var L i) (FOL.Term.shift L d (f (i - d))) =
    ite (ltb i d) (FOL.Term.var L i) (FOL.Term.shift L d (g (i - d)))
  rw [h]

theorem subst_shiftSubst_zero : ∀ L A, subst (FOL.shiftSubst L 0) L A = A := by
  intro L A
  exact eq_trans (subst_congr (FOL.shiftSubst L 0) (FOL.Term.var L) L
    (FOL.shiftSubst_zero L) A) (subst_id L A)

theorem shift_eq_subst : ∀ L A, shift L A = subst (FOL.shiftSubst L 1) L A := by
  intro L A
  let f := fun d i => FOL.Term.var L (ite (ltb i d) i (S i))
  let g := FOL.liftSubst (FOL.shiftSubst L 1) L
  have h : ∀ d i, f d i = g d i := by
    intro d i
    by_cases hi : i < d
    · rw [and_right (ltb_eq_one i d) hi, ite_succ,
        FOL.liftSubst_of_lt (FOL.shiftSubst L 1) L d i hi]
    · have hd := le_of_not_lt d i hi
      rw [ltb_eq_zero_of_ge i d hd, ite_zero,
        FOL.liftSubst_of_le (FOL.shiftSubst L 1) L d i hd,
        FOL.shiftSubst, FOL.Term.shift_var, add_succ, add_zero, succ_add,
        sub_add_cancel_of_le i d hd]
  exact substWithDepth_congr f g L h A 0

theorem instantiate_eq_subst : ∀ L A t,
    instantiate L A t = subst (FOL.consSubst t (FOL.shiftSubst L 0)) L A := by
  intro L A t
  exact substWithDepth_congr (FOL.Term.instantiateAt L 0 t)
    (FOL.liftSubst (FOL.consSubst t (FOL.shiftSubst L 0)) L) L
    (FOL.Term.instantiateAt_eq_liftSubst L t) A 0

theorem substWithDepth_offset (f : Nat → Nat → Nat) : ∀ L e A d,
    substWithDepth f L A (d + e) = substWithDepth (fun k i => f (k + e) i) L A d := by
  intro L e
  let g := fun k i => f (k + e) i
  exact induction_eq (fun A d => substWithDepth f L A (d + e)) (substWithDepth g L) L
    (fun d => eq_trans (substWithDepth_falsum f L (d + e)) (eq_symm (substWithDepth_falsum g L d)))
    (fun t u d => eq_trans (substWithDepth_equal f L t u (d + e))
      (eq_symm (substWithDepth_equal g L t u d)))
    (fun j xs d hj => eq_trans (substWithDepth_rel f L j xs (d + e) hj)
      (eq_symm (substWithDepth_rel g L j xs d hj)))
    (fun A B d hA hB => eq_trans (substWithDepth_imp f L A B (d + e))
      (eq_trans (eq_congr₂ imp hA hB) (eq_symm (substWithDepth_imp g L A B d))))
    (fun A d hA => eq_trans (substWithDepth_all f L A (d + e))
      (eq_trans (eq_congr all
        (eq_trans (eq_congr (substWithDepth f L A) (eq_symm (succ_add d e))) hA))
        (eq_symm (substWithDepth_all g L A d))))

theorem subst_falsum (f : Nat → Nat) : ∀ L,
    subst f L falsum = falsum := fun L => substWithDepth_falsum (FOL.liftSubst f L) L 0

theorem subst_equal (f : Nat → Nat) : ∀ L t u,
    subst f L (equal L t u) = equal L (Term.subst f L t) (Term.subst f L u) := by
  intro L t u
  rw [subst, substWithDepth_equal (FOL.liftSubst f L)]
  exact eq_congr₂ (equal L)
    (Term.subst_congr (FOL.liftSubst f L 0) f L (FOL.liftSubst_zero f L) t)
    (Term.subst_congr (FOL.liftSubst f L 0) f L (FOL.liftSubst_zero f L) u)

theorem subst_imp (f : Nat → Nat) : ∀ L A B,
    subst f L (imp A B) = imp (subst f L A) (subst f L B) :=
  fun L A B => substWithDepth_imp (FOL.liftSubst f L) L A B 0

theorem subst_all (f : Nat → Nat) : ∀ L A,
    subst f L (all A) = all (subst (FOL.liftSubst f L 1) L A) := by
  intro L A
  let g := FOL.liftSubst f L
  let h := FOL.liftSubst (FOL.liftSubst f L 1) L
  have pointwise : ∀ d i, g (d + 1) i = h d i :=
    fun d i => eq_symm (FOL.liftSubst_liftSubst f L d 1 i)
  rw [subst, substWithDepth_all g, subst]
  exact eq_congr all (eq_trans (substWithDepth_offset g L 1 A 0)
    (substWithDepth_congr (fun d i => g (d + 1) i) h L pointwise A 0))

/-- Shifting a quantified formula shifts its body beneath the quantifier. -/
theorem shift_all : ∀ L A,
    shift L (all A) = all (subst (FOL.liftSubst (FOL.shiftSubst L 1) L 1) L A) := by
  intro L A
  rw [shift_eq_subst L (all A)]
  exact subst_all (FOL.shiftSubst L 1) L A

theorem shift_imp : ∀ L A B, shift L (imp A B) = imp (shift L A) (shift L B) := by
  intro L A B
  rw [shift_eq_subst L (imp A B), shift_eq_subst L A, shift_eq_subst L B]
  exact subst_imp (FOL.shiftSubst L 1) L A B

theorem shift_falsum : ∀ L, shift L falsum = falsum := by
  intro L
  rw [shift_eq_subst L falsum]
  exact subst_falsum (FOL.shiftSubst L 1) L

theorem shift_neg : ∀ L A, shift L (neg A) = neg (shift L A) := by
  intro L A
  rw [neg, neg, shift_imp, shift_falsum]

theorem instantiate_neg : ∀ L A t, instantiate L (neg A) t = neg (instantiate L A t) := by
  intro L A t
  rw [neg, neg, instantiate_eq_subst L (imp A falsum) t, instantiate_eq_subst L A t,
    subst_imp (FOL.consSubst t (FOL.shiftSubst L 0)),
    subst_falsum (FOL.consSubst t (FOL.shiftSubst L 0))]

/-- Instantiating beneath a lifted substitution puts the term in front of the substitution. -/
theorem instantiate_subst_liftSubst (f : Nat → Nat) : ∀ L A t,
    instantiate L (subst (FOL.liftSubst f L 1) L A) t =
      subst (FOL.consSubst t f) L A := by
  intro L A t
  have pointwise : ∀ i,
      FOL.Term.subst (FOL.consSubst t (FOL.shiftSubst L 0)) L (FOL.liftSubst f L 1 i) =
        FOL.consSubst t f i := by
    intro i
    rw [FOL.liftSubst_one f L i]
    rcases zero_or_succ_pred i with h | h
    · rw [h, FOL.consSubst_zero (FOL.Term.var L 0) (fun j => FOL.Term.shift L 1 (f j)),
        FOL.Term.subst_var (FOL.consSubst t (FOL.shiftSubst L 0))]
      rfl
    · rw [h, FOL.consSubst_succ (FOL.Term.var L 0) (fun j => FOL.Term.shift L 1 (f j))]
      exact FOL.Term.subst_consSubst_shift t L (f (pred i))
  rw [instantiate_eq_subst L (subst (FOL.liftSubst f L 1) L A) t,
    subst_comp (FOL.consSubst t (FOL.shiftSubst L 0)) (FOL.liftSubst f L 1) L A]
  exact subst_congr
    (fun i => FOL.Term.subst (FOL.consSubst t (FOL.shiftSubst L 0)) L
      (FOL.liftSubst f L 1 i))
    (FOL.consSubst t f) L pointwise A

/-- Instantiating the shifted body of a quantifier at the new variable gives the body back. -/
theorem instantiate_lifted : ∀ L A,
    instantiate L (subst (FOL.liftSubst (FOL.shiftSubst L 1) L 1) L A)
      (FOL.Term.var L 0) = A := by
  intro L A
  have pointwise : ∀ i,
      FOL.Term.subst (FOL.consSubst (FOL.Term.var L 0) (FOL.shiftSubst L 0)) L
        (FOL.liftSubst (FOL.shiftSubst L 1) L 1 i) = FOL.Term.var L i := by
    intro i
    rw [FOL.liftSubst_one (FOL.shiftSubst L 1) L i]
    rcases zero_or_succ_pred i with h | h
    · rw [h, FOL.consSubst_zero (FOL.Term.var L 0)
        (fun j => FOL.Term.shift L 1 (FOL.shiftSubst L 1 j)),
        FOL.Term.subst_var (FOL.consSubst (FOL.Term.var L 0) (FOL.shiftSubst L 0))]
      exact FOL.consSubst_zero (FOL.Term.var L 0) (FOL.shiftSubst L 0)
    · rw [h, FOL.consSubst_succ (FOL.Term.var L 0)
        (fun j => FOL.Term.shift L 1 (FOL.shiftSubst L 1 j))]
      change FOL.Term.subst (FOL.consSubst (FOL.Term.var L 0) (FOL.shiftSubst L 0)) L
        (FOL.Term.shift L 1 (FOL.Term.var L (pred i + 1))) = FOL.Term.var L (S (pred i))
      rw [FOL.Term.shift_var L 1 (pred i + 1),
        FOL.Term.subst_var (FOL.consSubst (FOL.Term.var L 0) (FOL.shiftSubst L 0))]
      change FOL.shiftSubst L 0 (S (pred i)) = FOL.Term.var L (S (pred i))
      exact FOL.shiftSubst_zero L (S (pred i))
  rw [instantiate_eq_subst L
      (subst (FOL.liftSubst (FOL.shiftSubst L 1) L 1) L A) (FOL.Term.var L 0),
    subst_comp (FOL.consSubst (FOL.Term.var L 0) (FOL.shiftSubst L 0))
      (FOL.liftSubst (FOL.shiftSubst L 1) L 1) L A]
  exact eq_trans
    (subst_congr
      (fun i => FOL.Term.subst (FOL.consSubst (FOL.Term.var L 0) (FOL.shiftSubst L 0)) L
        (FOL.liftSubst (FOL.shiftSubst L 1) L 1 i))
      (FOL.Term.var L) L pointwise A)
    (subst_id L A)

/-- Applying a lifted substitution at depth `k` equals ordinary formula substitution with
the substitution lifted past `k` binders. -/
theorem substWithDepth_liftSubst (f : Nat → Nat) : ∀ L A k,
    substWithDepth (FOL.liftSubst f L) L A k = subst (FOL.liftSubst f L k) L A := by
  intro L A k
  let g := FOL.liftSubst f L
  let h := FOL.liftSubst (FOL.liftSubst f L k) L
  have pointwise : ∀ d i, g (d + k) i = h d i :=
    fun d i => eq_symm (FOL.liftSubst_liftSubst f L d k i)
  have start : substWithDepth g L A k = substWithDepth g L A (0 + k) :=
    eq_congr (substWithDepth g L A) (eq_symm (zero_add k))
  exact eq_trans start (eq_trans (substWithDepth_offset g L k A 0)
    (substWithDepth_congr (fun d i => g (d + k) i) h L pointwise A 0))

/-- Shifting `n` times raises every position by `n`. -/
theorem iter_shift_eq_subst : ∀ L n A,
    iter (shift L) n A = subst (FOL.shiftSubst L n) L A := by
  intro L n A
  induction n with k ih
  · exact eq_symm (subst_shiftSubst_zero L A)
  · rw [iter_succ (shift L), ih, shift_eq_subst L (subst (FOL.shiftSubst L k) L A),
      subst_comp (FOL.shiftSubst L 1) (FOL.shiftSubst L k) L A]
    exact subst_congr (fun i => Term.subst (FOL.shiftSubst L 1) L (FOL.shiftSubst L k i))
      (FOL.shiftSubst L (S k)) L (fun i => Term.subst_shiftSubst_shiftSubst L 1 k i) A

/-- A formula written outside `d` binders and raised past them and `k` more is raised past
`e + k` binders after a substitution that sends the positions from `d` on to those from `e`
on. -/
theorem substWithDepth_liftSubst_outer (f : Nat → Nat) :
    ∀ L d e, (∀ i, f (i + d) = Term.var L (i + e)) →
    ∀ k A, substWithDepth (FOL.liftSubst f L) L (iter (shift L) (d + k) A) k =
      iter (shift L) (e + k) A := by
  intro L d e h k A
  rw [iter_shift_eq_subst L (d + k) A, iter_shift_eq_subst L (e + k) A,
    substWithDepth_liftSubst f L (subst (FOL.shiftSubst L (d + k)) L A) k,
    subst_comp (FOL.liftSubst f L k) (FOL.shiftSubst L (d + k)) L A]
  exact subst_congr
    (fun i => Term.subst (FOL.liftSubst f L k) L (FOL.shiftSubst L (d + k) i))
    (FOL.shiftSubst L (e + k)) L (Term.subst_liftSubst_shiftSubst f L d e h k) A

/-- Successive formula substitutions compose by substituting into the replacement terms,
with the outer substitution lifted past `k` binders. -/
theorem substWithDepth_liftSubst_subst (f g g' : Nat → Nat) : ∀ L k,
    (∀ i, Term.subst (FOL.liftSubst f L k) L (g i) = g' i) →
    ∀ A, substWithDepth (FOL.liftSubst f L) L (subst g L A) k = subst g' L A := by
  intro L k h A
  rw [substWithDepth_liftSubst f L (subst g L A) k, subst_comp (FOL.liftSubst f L k) g L A]
  exact subst_congr (fun i => Term.subst (FOL.liftSubst f L k) L (g i)) g' L h A

end Formula

theorem liftSubst_succ (f : Nat → Nat) : ∀ L n i,
    liftSubst f L (S n) (S i) = Term.shift L 1 (liftSubst f L n i) := by
  intro L n i
  have h := liftSubst_liftSubst f L 1 n (S i)
  rw [one_add] at h
  rw [← h]
  exact liftSubst_add (liftSubst f L n) L 1 i

namespace Term

theorem subst_consSubst_shift_eq (g : Nat → Nat) : ∀ L t u,
    subst (consSubst t g) L (shift L 1 u) = subst g L u := by
  intro L t u
  exact eq_trans (subst_comp (consSubst t g) (shiftSubst L 1) L u)
    (subst_congr (fun i => subst (consSubst t g) L (shiftSubst L 1 i)) g L
      (fun i => eq_trans (subst_shiftSubst (consSubst t g) L 1 i) (consSubst_succ t g i)) u)

theorem subst_liftSubst_shiftSubst_comm (f : Nat → Nat) : ∀ L k i,
    subst (liftSubst f L k) L (shiftSubst L k i) =
      subst (shiftSubst L k) L (liftSubst f L 0 i) := by
  intro L k i
  rw [subst_shiftSubst (liftSubst f L k), liftSubst_add f, liftSubst_zero f]
  rfl

theorem subst_consSubst_liftSubst (f g a b : Nat → Nat) : ∀ L n t u,
    subst f L t = u →
    (∀ i, subst f L (a i) = subst b L (liftSubst g L n i)) → ∀ i,
      subst f L (consSubst t a i) = subst (consSubst u b) L (liftSubst g L (S n) i) := by
  intro L n t u ht h i
  by_cases hz : i = 0
  · rw [hz, consSubst_zero t a, ht,
      liftSubst_of_lt g L (S n) 0 (lt_of_le_of_lt 0 n (S n) (zero_le n) (lt_succ_self n)),
      subst_var (consSubst u b),
      consSubst_zero u b]
  · rw [← succ_pred i hz, consSubst_succ t a, liftSubst_succ g,
      subst_consSubst_shift_eq b]
    exact h (pred i)

theorem subst_subst_of_eq (f g h j : Nat → Nat) : ∀ L,
    (∀ i, subst f L (g i) = subst h L (j i)) → ∀ t,
      subst f L (subst g L t) = subst h L (subst j L t) := by
  intro L same t
  exact eq_trans (subst_comp f g L t)
    (eq_trans (subst_congr (fun i => subst f L (g i)) (fun i => subst h L (j i)) L same t)
      (eq_symm (subst_comp h j L t)))

end Term

namespace Formula

theorem subst_subst_of_eq (f g h j : Nat → Nat) : ∀ L,
    (∀ i, Term.subst f L (g i) = Term.subst h L (j i)) → ∀ A,
      subst f L (subst g L A) = subst h L (subst j L A) := by
  intro L same A
  exact eq_trans (subst_comp f g L A)
    (eq_trans (subst_congr (fun i => Term.subst f L (g i))
      (fun i => Term.subst h L (j i)) L same A) (eq_symm (subst_comp h j L A)))

end Formula

theorem liftSubst_congr (f g : Nat → Nat) : ∀ L n,
    (∀ i, f i = g i) → ∀ i, liftSubst f L n i = liftSubst g L n i := by
  intro L n h i
  by_cases hn : i < n
  · rw [liftSubst_of_lt f L n i hn, liftSubst_of_lt g L n i hn]
  · have hi := le_of_not_lt n i hn
    rw [liftSubst_of_le f L n i hi, liftSubst_of_le g L n i hi, h (i - n)]

theorem liftSubst_shift_comm (f : Nat → Nat) : ∀ L n k i,
    Term.subst (liftSubst f L (n + k)) L (liftSubst (shiftSubst L k) L n i) =
      Term.subst (liftSubst (shiftSubst L k) L n) L (liftSubst f L n i) := by
  intro L n k i
  have raised : ∀ j,
      Term.subst (liftSubst f L (n + k)) L (liftSubst (shiftSubst L k) L n j) =
        Term.subst (liftSubst (liftSubst f L k) L n) L
          (liftSubst (shiftSubst L k) L n j) :=
    fun j => Term.subst_congr (liftSubst f L (n + k)) (liftSubst (liftSubst f L k) L n) L
      (fun z => eq_symm (liftSubst_liftSubst f L n k z))
      (liftSubst (shiftSubst L k) L n j)
  have pointwise : ∀ j, Term.subst (liftSubst f L k) L (shiftSubst L k j) =
      Term.subst (shiftSubst L k) L (f j) := by
    intro j
    rw [Term.subst_shiftSubst (liftSubst f L k), liftSubst_add f]
    rfl
  exact eq_trans (raised i)
    (eq_trans (liftSubst_comp (liftSubst f L k) (shiftSubst L k) L n i)
      (eq_trans (liftSubst_congr
        (fun j => Term.subst (liftSubst f L k) L (shiftSubst L k j))
        (fun j => Term.subst (shiftSubst L k) L (f j)) L n pointwise i)
        (eq_symm (liftSubst_comp (shiftSubst L k) f L n i))))

end FOL

end
