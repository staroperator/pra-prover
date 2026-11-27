module

public import PRAProver.Library.FOL.Common.Proof.Propositional
public meta import PRAProver.Library.Tactic.SigmaInduction

/-!
# Provability under a list of assumptions

`Sequent L T Γ A` states that `A` follows from the assumptions `Γ` in theory `T` over
language `L`. The assumptions form a sequence of formula codes, newest first. Folding
`fun r B => Formula.imp B r` over that sequence builds the nested implication, with the
newest assumption next to `A`. An empty sequence gives `Provable L T A`.

- `Sequent.lift`, `mp`, `head`, and `weaken` handle provability and local assumptions.
- `Sequent.imp_intro` and `cons_of_imp` move a formula between the list and the conclusion;
  `falsum_elim`, `neg_neg_elim`, and the conjunction and disjunction rules handle connectives.
- `Sequent.all_intro` shifts the assumptions past a fresh variable, and `all_elim` instantiates
  a universal quantifier. The `subst_consSubst` lemmas collect successive substitutions.
- `Sequent.ex_intro` and `ex_elim` introduce and eliminate an existential quantifier;
  `ex_elim_of_all_imp` uses a branch stated as a universally quantified implication.
-/

@[expose] public section

pra

namespace FOL

/-- Provability of `A` in language `L` and theory `T` under the assumption list `Γ`.
Folding implication over the list places the newest assumption next to the conclusion. -/
def Sequent (L : Nat) (T : Nat → Nat) : Nat → Nat → Prop :=
  fun Γ A => Provable L T (Sequence.fold (fun r B => Formula.imp B r) Γ A)

namespace Sequent

open Formula

/-- A provable formula is provable under every list of assumptions. -/
theorem lift (L : Nat) (T : Nat → Nat) : ∀ Γ C,
    Provable L T C → Sequent L T Γ C := by
  intro Γ C h
  let chain := fun n => primrec C (fun i r => imp (Sequence.get Γ i) r) n
  have derivation : ∀ n, Provable L T (imp C (chain n)) := by
    intro n
    sigma_induction n with
    | zero => exact Provable.imp_refl L T C
    | succ k ih =>
      exact Provable.mp L T (imp C (chain k))
        (imp C (imp (Sequence.get Γ k) (chain k)))
        (Provable.imp_imp_right L T C (chain k) (Sequence.get Γ k)) ih
  exact Provable.mp L T C (chain (Sequence.length Γ)) (derivation (Sequence.length Γ)) h

/-- Modus ponens under a shared list of assumptions. -/
theorem mp (L : Nat) (T : Nat → Nat) : ∀ Γ A B,
    Sequent L T Γ (imp A B) → Sequent L T Γ A → Sequent L T Γ B := by
  intro Γ A B h k
  let chain := fun C n => primrec C (fun i r => imp (Sequence.get Γ i) r) n
  have distribution : ∀ n,
      Provable L T (imp (chain (imp A B) n) (imp (chain A n) (chain B n))) := by
    intro n
    sigma_induction n with
    | zero => exact Provable.imp_refl L T (imp A B)
    | succ i ih =>
      exact Provable.mp L T
        (imp (chain (imp A B) i) (imp (chain A i) (chain B i)))
        (imp (imp (Sequence.get Γ i) (chain (imp A B) i))
          (imp (imp (Sequence.get Γ i) (chain A i))
            (imp (Sequence.get Γ i) (chain B i))))
        (Provable.imp_distrib L T (chain (imp A B) i) (chain A i) (chain B i)
          (Sequence.get Γ i)) ih
  exact Provable.mp L T (chain A (Sequence.length Γ)) (chain B (Sequence.length Γ))
    (Provable.mp L T (chain (imp A B) (Sequence.length Γ))
      (imp (chain A (Sequence.length Γ)) (chain B (Sequence.length Γ)))
      (distribution (Sequence.length Γ)) h) k

/-- Moving the newest assumption into the conclusion gives the same formula. -/
theorem imp_intro (L : Nat) (T : Nat → Nat) : ∀ Γ A B,
    Sequent L T (Sequence.cons A Γ) B → Sequent L T Γ (imp A B) := by
  intro Γ A B h
  rw [Sequent, Sequence.fold_cons (fun r C => imp C r)] at h
  exact h

theorem cons_of_imp (L : Nat) (T : Nat → Nat) : ∀ Γ A B,
    Sequent L T Γ (imp A B) → Sequent L T (Sequence.cons A Γ) B := by
  intro Γ A B h
  rw [Sequent, Sequence.fold_cons (fun r C => imp C r)]
  exact h

/-- The newest assumption is provable from the list. -/
theorem head (L : Nat) (T : Nat → Nat) : ∀ Γ A,
    Sequent L T (Sequence.cons A Γ) A :=
  fun Γ A => cons_of_imp L T Γ A A (lift L T Γ (imp A A) (Provable.imp_refl L T A))

/-- A conclusion from a list still follows after one more assumption is added. -/
theorem weaken (L : Nat) (T : Nat → Nat) : ∀ Γ A B,
    Sequent L T Γ B → Sequent L T (Sequence.cons A Γ) B :=
  fun Γ A B h => cons_of_imp L T Γ A B
    (mp L T Γ B (imp A B) (lift L T Γ (imp B (imp A B)) (Provable.implication L T B A)) h)

theorem falsum_elim (L : Nat) (T : Nat → Nat) : ∀ Γ A,
    Sequent L T Γ falsum → Sequent L T Γ A :=
  fun Γ A h => mp L T Γ falsum A (lift L T Γ (imp falsum A) (Provable.falsum_imp L T A)) h

theorem neg_neg_elim (L : Nat) (T : Nat → Nat) : ∀ Γ A,
    Sequent L T Γ (neg (neg A)) → Sequent L T Γ A :=
  fun Γ A h => mp L T Γ (neg (neg A)) A
    (lift L T Γ (imp (neg (neg A)) A) (Provable.neg_neg_elim L T A)) h

theorem conj_intro (L : Nat) (T : Nat → Nat) : ∀ Γ A B,
    Sequent L T Γ A → Sequent L T Γ B →
      Sequent L T Γ (conj A B) :=
  fun Γ A B ha hb => mp L T Γ B (conj A B)
    (mp L T Γ A (imp B (conj A B))
      (lift L T Γ (imp A (imp B (conj A B))) (Provable.conj_intro L T A B)) ha) hb

theorem conj_left (L : Nat) (T : Nat → Nat) : ∀ Γ A B,
    Sequent L T Γ (conj A B) → Sequent L T Γ A :=
  fun Γ A B h => mp L T Γ (conj A B) A
    (lift L T Γ (imp (conj A B) A) (Provable.conj_left L T A B)) h

theorem conj_right (L : Nat) (T : Nat → Nat) : ∀ Γ A B,
    Sequent L T Γ (conj A B) → Sequent L T Γ B :=
  fun Γ A B h => mp L T Γ (conj A B) B
    (lift L T Γ (imp (conj A B) B) (Provable.conj_right L T A B)) h

theorem disj_intro_left (L : Nat) (T : Nat → Nat) : ∀ Γ A B,
    Sequent L T Γ A → Sequent L T Γ (disj A B) :=
  fun Γ A B h => mp L T Γ A (disj A B)
    (lift L T Γ (imp A (disj A B)) (Provable.disj_intro_left L T A B)) h

theorem disj_intro_right (L : Nat) (T : Nat → Nat) : ∀ Γ A B,
    Sequent L T Γ B → Sequent L T Γ (disj A B) :=
  fun Γ A B h => mp L T Γ B (disj A B)
    (lift L T Γ (imp B (disj A B)) (Provable.disj_intro_right L T A B)) h

/-- Case analysis: each branch receives its disjunct as the newest assumption. -/
theorem disj_elim (L : Nat) (T : Nat → Nat) : ∀ Γ A B C,
    Sequent L T Γ (disj A B) → Sequent L T (Sequence.cons A Γ) C →
      Sequent L T (Sequence.cons B Γ) C → Sequent L T Γ C :=
  fun Γ A B C h ha hb => mp L T Γ (imp B C) C
    (mp L T Γ (imp A C) (imp (imp B C) C)
      (mp L T Γ (disj A B) (imp (imp A C) (imp (imp B C) C))
        (lift L T Γ (imp (disj A B) (imp (imp A C) (imp (imp B C) C)))
          (Provable.disj_elim L T A B C)) h)
      (imp_intro L T Γ A C ha))
    (imp_intro L T Γ B C hb)

/-- Introduce a universal quantifier. The premise holds under the shifted assumptions, so the
new variable is fresh for them. -/
theorem all_intro (L : Nat) (T : Nat → Nat) : ∀ Γ A,
    Sequent L T (Sequence.map (shift L) Γ) A → Sequent L T Γ (all A) := by
  intro Γ A h
  let chain := fun C n => primrec C (fun i r => imp (Sequence.get Γ i) r) n
  let shifted := fun n => primrec A (fun i r => imp (shift L (Sequence.get Γ i)) r) n
  have quantifiers : ∀ n, Provable L T (imp (all (shifted n)) (chain (all A) n)) := by
    intro n
    sigma_induction n with
    | zero => exact Provable.imp_refl L T (all A)
    | succ k ih =>
      exact Provable.mp L T
        (imp (all (shifted k)) (chain (all A) k))
        (imp (all (imp (shift L (Sequence.get Γ k)) (shifted k)))
          (imp (Sequence.get Γ k) (chain (all A) k)))
        (Provable.mp L T
          (imp (all (imp (shift L (Sequence.get Γ k)) (shifted k)))
            (imp (Sequence.get Γ k) (all (shifted k))))
          (imp (imp (all (shifted k)) (chain (all A) k))
            (imp (all (imp (shift L (Sequence.get Γ k)) (shifted k)))
              (imp (Sequence.get Γ k) (chain (all A) k))))
          (Provable.imp_trans_under L T
            (all (imp (shift L (Sequence.get Γ k)) (shifted k)))
            (Sequence.get Γ k) (all (shifted k)) (chain (all A) k))
          (Provable.quantifierImplication L T (Sequence.get Γ k) (shifted k))) ih
  rw [Sequent, Sequence.fold_map (fun r C => imp C r) (shift L)] at h
  exact Provable.mp L T (all (shifted (Sequence.length Γ))) (chain (all A) (Sequence.length Γ))
    (quantifiers (Sequence.length Γ)) (Provable.gen L T (shifted (Sequence.length Γ)) h)

/-- Instantiate a universal quantifier by any term. -/
theorem all_elim (L : Nat) (T : Nat → Nat) : ∀ Γ A t,
    Sequent L T Γ (all A) → Sequent L T Γ (instantiate L A t) :=
  fun Γ A t h => mp L T Γ (all A) (instantiate L A t)
    (lift L T Γ (imp (all A) (instantiate L A t)) (Provable.instantiate L T A t)) h

/-- Instantiate a universal quantifier, with the instance written as a substitution. -/
theorem subst_consSubst_of_all (L : Nat) (T : Nat → Nat) : ∀ Γ A t,
    Sequent L T Γ (all A) →
      Sequent L T Γ (subst (FOL.consSubst t (FOL.shiftSubst L 0)) L A) := by
  intro Γ A t h
  rw [← instantiate_eq_subst L A t]
  exact all_elim L T Γ A t h

/-- Instantiate the next quantifier beneath a substitution: the term is placed in front of the
substitution. Several quantifiers are instantiated this way before the formula is calculated. -/
theorem subst_consSubst_of_subst_all (L : Nat) (T : Nat → Nat) (f : Nat → Nat) : ∀ Γ A t,
    Sequent L T Γ (subst f L (all A)) →
      Sequent L T Γ (subst (FOL.consSubst t f) L A) := by
  intro Γ A t h
  rw [subst_all f L A] at h
  rw [← instantiate_subst_liftSubst f L A t]
  exact all_elim L T Γ (subst (FOL.liftSubst f L 1) L A) t h

/-- Introduce an existential quantifier from an instance. -/
theorem ex_intro (L : Nat) (T : Nat → Nat) : ∀ Γ A t,
    Sequent L T Γ (instantiate L A t) → Sequent L T Γ (ex A) := by
  intro Γ A t h
  have inst := Provable.instantiate L T (neg A) t
  rw [instantiate_neg] at inst
  have step := Provable.mp L T (imp (all (neg A)) (neg (instantiate L A t)))
    (imp (instantiate L A t) (neg (all (neg A))))
    (Provable.imp_neg_swap L T (all (neg A)) (instantiate L A t)) inst
  rw [ex]
  exact mp L T Γ (instantiate L A t) (neg (all (neg A)))
    (lift L T Γ (imp (instantiate L A t) (neg (all (neg A)))) step) h

/-- Eliminate an existential statement. The branch receives the body as the newest assumption, for
a variable that is fresh for the other assumptions and for the conclusion. -/
theorem ex_elim (L : Nat) (T : Nat → Nat) : ∀ Γ A B,
    Sequent L T Γ (ex A) →
      Sequent L T (Sequence.cons A (Sequence.map (shift L) Γ)) (shift L B) →
        Sequent L T Γ B := by
  intro Γ A B h k
  have k₁ := imp_intro L T (Sequence.map (shift L) Γ) A (shift L B) k
  have k₂ := mp L T (Sequence.map (shift L) Γ) (imp A (shift L B)) (imp (neg (shift L B)) (neg A))
    (lift L T (Sequence.map (shift L) Γ) (imp (imp A (shift L B)) (imp (neg (shift L B)) (neg A)))
      (Provable.imp_contrapos L T A (shift L B))) k₁
  have k₃ := cons_of_imp L T (Sequence.map (shift L) Γ) (neg (shift L B)) (neg A) k₂
  rw [← shift_neg L B, ← Sequence.map_cons (shift L) (neg B) Γ] at k₃
  have k₄ := imp_intro L T Γ (neg B) (all (neg A))
    (all_intro L T (Sequence.cons (neg B) Γ) (neg A) k₃)
  rw [ex] at h
  exact neg_neg_elim L T Γ B (mp L T Γ (neg (all (neg A))) (neg (neg B))
    (mp L T Γ (imp (neg B) (all (neg A))) (imp (neg (all (neg A))) (neg (neg B)))
      (lift L T Γ (imp (imp (neg B) (all (neg A))) (imp (neg (all (neg A))) (neg (neg B))))
        (Provable.imp_contrapos L T (neg B) (all (neg A)))) k₄) h)

/-- Eliminate an existential statement when the branch is stated with a quantifier: from `Γ ⊢ ∃ A`
and `Γ ⊢ ∀ (A → B)`, where `B` does not mention the quantified variable, conclude `Γ ⊢ B`. -/
theorem ex_elim_of_all_imp (L : Nat) (T : Nat → Nat) : ∀ Γ A B,
    Sequent L T Γ (ex A) → Sequent L T Γ (all (imp A (shift L B))) →
      Sequent L T Γ B := by
  intro Γ A B h k
  have branch : Sequent L T
      (Sequence.cons A (Sequence.map (shift L) (Sequence.cons (all (imp A (shift L B))) Γ)))
      (shift L (all (imp A (shift L B)))) := by
    rw [Sequence.map_cons (shift L) (all (imp A (shift L B))) Γ]
    exact weaken L T
      (Sequence.cons (shift L (all (imp A (shift L B)))) (Sequence.map (shift L) Γ)) A
      (shift L (all (imp A (shift L B))))
      (head L T (Sequence.map (shift L) Γ) (shift L (all (imp A (shift L B)))))
  rw [shift_all L (imp A (shift L B))] at branch
  have instantiated := all_elim L T
    (Sequence.cons A (Sequence.map (shift L) (Sequence.cons (all (imp A (shift L B))) Γ)))
    (subst (FOL.liftSubst (FOL.shiftSubst L 1) L 1) L (imp A (shift L B)))
    (FOL.Term.var L 0) branch
  rw [instantiate_lifted L (imp A (shift L B))] at instantiated
  have inner := mp L T
    (Sequence.cons A (Sequence.map (shift L) (Sequence.cons (all (imp A (shift L B))) Γ)))
    A (shift L B) instantiated
    (head L T (Sequence.map (shift L) (Sequence.cons (all (imp A (shift L B))) Γ)) A)
  exact mp L T Γ (all (imp A (shift L B))) B
    (imp_intro L T Γ (all (imp A (shift L B))) B
      (ex_elim L T (Sequence.cons (all (imp A (shift L B))) Γ) A B
        (weaken L T Γ (all (imp A (shift L B))) (ex A) h) inner))
    k

end Sequent

end FOL

extract_witness FOL.Sequent.all_elim FOL.Sequent.subst_consSubst_of_subst_all
  FOL.Sequent.all_intro FOL.Sequent.neg_neg_elim FOL.Sequent.ex_elim_of_all_imp FOL.Sequent.ex_elim
  FOL.Sequent.ex_intro FOL.Sequent.head FOL.Sequent.lift FOL.Sequent.mp FOL.Sequent.weaken

end
