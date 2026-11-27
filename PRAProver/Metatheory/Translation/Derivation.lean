module

public import PRAProver.Metatheory.Core.Judgement.Defs
import PRAProver.Metatheory.Core.Judgement.Formation

/-!
# Logical rules for translation

- `Derivation` expresses the logical introduction and elimination rules on PRA formulas.
- `ProofTyping.toDerivation` expands primitive proof heads into these rules. Ordinary proof and
  numerical applications become implication and universal elimination.

This intermediate judgement lets the translation follow the logical rules independently of the
representation of primitive heads in checked proof data.
-/

namespace PRAProver.Translation

open Core Core.Theory

/-- A derivation using logical introduction and elimination rules, with quantifier-free
induction. -/
public inductive Derivation (E : Environment) (Ξ : ParameterContext) :
    LocalContext → ProofContext → Predicate → Prop where
  | hyp {i : Nat} (lookup : H[i]? = some A) : Derivation E Ξ Γ H A
  | trueIntro : Derivation E Ξ Γ H .true
  | theoremE {name : Lean.Name} {d : TheoremDefinition} (lookup : E[name]? = some (.theoremE d))
      (functions : FunctionArguments E Ξ Γ fs d.functions)
      (predicates : PredicateArguments E Ξ Γ ps d.predicates) :
      Derivation E Ξ Γ H (d.type.instantiate fs ps)
  | impIntro (antecedent : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (body : Derivation E Ξ Γ (A :: H) B) :
      Derivation E Ξ Γ H (.imp A B)
  | impElim (function : Derivation E Ξ Γ H (.imp A B))
      (argument : Derivation E Ξ Γ H A) : Derivation E Ξ Γ H B
  | andIntro (left : Derivation E Ξ Γ H A) (right : Derivation E Ξ Γ H B) :
      Derivation E Ξ Γ H (.and A B)
  | andLeft (pair : Derivation E Ξ Γ H (.and A B)) :
      Derivation E Ξ Γ H A
  | andRight (pair : Derivation E Ξ Γ H (.and A B)) :
      Derivation E Ξ Γ H B
  | orLeft (other : PredicateTyping E Ξ Γ B ⟨0, .prop⟩)
      (proof : Derivation E Ξ Γ H A) : Derivation E Ξ Γ H (.or A B)
  | orRight (other : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (proof : Derivation E Ξ Γ H B) : Derivation E Ξ Γ H (.or A B)
  | orElim (target : PredicateTyping E Ξ Γ C ⟨0, .prop⟩)
      (scrutinee : Derivation E Ξ Γ H (.or A B))
      (left : Derivation E Ξ Γ (A :: H) C) (right : Derivation E Ξ Γ (B :: H) C) :
      Derivation E Ξ Γ H C
  | falseElim (target : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (proof : Derivation E Ξ Γ H .false) : Derivation E Ξ Γ H A
  | forallIntro (motive : PredicateTyping E Ξ Γ P ⟨1, .prop⟩)
      (body : Derivation E Ξ (0 :: Γ) (H.map Predicate.shift) (.app P.shift (.bvar 0))) :
      Derivation E Ξ Γ H (.all P)
  | forallElim (proof : Derivation E Ξ Γ H (.all P)) (argument : TermTyping E Ξ Γ a 0) :
      Derivation E Ξ Γ H (.app P a)
  | existsIntro (motive : PredicateTyping E Ξ Γ P ⟨1, .prop⟩)
      (witness : TermTyping E Ξ Γ a 0) (proof : Derivation E Ξ Γ H (.app P a)) :
      Derivation E Ξ Γ H (.ex P)
  | existsElim (target : PredicateTyping E Ξ Γ C ⟨0, .prop⟩)
      (scrutinee : Derivation E Ξ Γ H (.ex P))
      (body : Derivation E Ξ (0 :: Γ) (.app P.shift (.bvar 0) :: H.map Predicate.shift)
        C.shift) : Derivation E Ξ Γ H C
  | letE (type : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (value : Derivation E Ξ Γ H A) (body : Derivation E Ξ Γ (A :: H) B) :
      Derivation E Ξ Γ H B
  | letTerm (value : TermTyping E Ξ Γ a j) (body : Derivation E Ξ Γ H A) :
      Derivation E Ξ Γ H A
  | letPredicate (value : PredicateTyping E Ξ Γ P σ) (body : Derivation E Ξ Γ H A) :
      Derivation E Ξ Γ H A
  | ascribe (type : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (proof : Derivation E Ξ Γ H A) : Derivation E Ξ Γ H A
  | eqRefl (term : TermTyping E Ξ Γ t 0) : Derivation E Ξ Γ H (.equal t t)
  | eqSubst (motive : PredicateTyping E Ξ Γ P ⟨1, .prop⟩)
      (equality : Derivation E Ξ Γ H (.equal a b))
      (proof : Derivation E Ξ Γ H (.app P a)) :
      Derivation E Ξ Γ H (.app P b)
  | succNeZero (term : TermTyping E Ξ Γ t 0) :
      Derivation E Ξ Γ H (.imp (.equal (.app .succ t) .zero) .false)
  | succInj (proof : Derivation E Ξ Γ H (.equal (.app .succ a) (.app .succ b))) :
      Derivation E Ξ Γ H (.equal a b)
  | lem (formula : PredicateTyping E Ξ Γ A ⟨0, .prop⟩) :
      Derivation E Ξ Γ H (.or A (.imp A .false))
  | induction (motive : PredicateTyping E Ξ Γ P ⟨1, .qf⟩)
      (base : Derivation E Ξ Γ H (.app P .zero))
      (step : Derivation E Ξ (0 :: Γ) (.app P.shift (.bvar 0) :: H.map Predicate.shift)
        (.app P.shift (.app .succ (.bvar 0))))
      (argument : TermTyping E Ξ Γ n 0) :
      Derivation E Ξ Γ H (.app P n)
  | conversion (proof : Derivation E Ξ Γ H A)
      (type : PredicateEq E Ξ Γ A B ⟨0, .prop⟩) : Derivation E Ξ Γ H B

private theorem imp_parts {E Ξ Γ A B}
    (h : PredicateTyping E Ξ Γ (.imp A B) ⟨0, .prop⟩) :
    PredicateTyping E Ξ Γ A ⟨0, .prop⟩ ∧ PredicateTyping E Ξ Γ B ⟨0, .prop⟩ := by
  obtain ⟨_, ha, hb, sub⟩ := h.inv_imp
  exact ⟨.subsumption ha sub, .subsumption hb sub⟩

private theorem open_lambda (B : Predicate) :
    (B.rename (Renaming.lift 1 (fun i => i + 1))).subst0 (.bvar 0) = B := by
  simp only [Predicate.subst0, Predicate.subst_rename]
  apply Eq.trans (b := B.subst Term.bvar) _ (Predicate.subst_id B)
  congr 1
  funext i
  cases i <;> simp [Renaming.lift, Nat.add_comm]

private theorem generalize {E Ξ Γ H B name} (valid : EnvironmentWF E)
    (formed : PredicateTyping E Ξ (0 :: Γ) B ⟨0, .prop⟩)
    (body : Derivation E Ξ (0 :: Γ) (H.map Predicate.shift) B) :
    Derivation E Ξ Γ H (.all (.lam name B)) := by
  apply Derivation.forallIntro (.lam formed)
  have shifted := PredicateTyping.shift valid (.lam (binderName := name) formed) 0
  simp only [Predicate.shift, Predicate.rename, Nat.not_lt_zero, ↓reduceIte] at shifted
  have shifted := shifted.lam_body
  have beta := PredicateEq.beta (binderName := name) shifted (TermTyping.bvar (i := 0) rfl)
  simp only [open_lambda] at beta
  apply Derivation.conversion body
  simpa only [Predicate.shift, Predicate.rename, Nat.not_lt_zero, ↓reduceIte] using beta.symm

private theorem apply_shifted_lambda {E Ξ Γ H B name} (valid : EnvironmentWF E)
    (formed : PredicateTyping E Ξ (0 :: Γ) B ⟨0, .prop⟩)
    (proof : Derivation E Ξ (0 :: Γ) H (Predicate.all (.lam name B)).shift) :
    Derivation E Ξ (0 :: Γ) H B := by
  have shifted := PredicateTyping.shift valid (.lam (binderName := name) formed) 0
  simp only [Predicate.shift, Predicate.rename, Nat.not_lt_zero, ↓reduceIte] at shifted
  have beta := PredicateEq.beta (binderName := name) shifted.lam_body
    (TermTyping.bvar (i := 0) rfl)
  simp only [open_lambda] at beta
  simp only [Predicate.shift, Predicate.rename, Nat.not_lt_zero, ↓reduceIte] at proof
  apply Derivation.conversion (.forallElim proof (.bvar (i := 0) rfl))
  simpa only [Predicate.shift, Predicate.rename, Nat.not_lt_zero, ↓reduceIte] using beta

/-- Expand a checked primitive head to a derivation of its complete declared signature. -/
public theorem _root_.PRAProver.Core.Theory.ProofTyping.toDerivation {E Ξ Γ H proof P}
    (valid : EnvironmentWF E) (typed : ProofTyping E Ξ Γ H proof P) :
    Derivation E Ξ Γ H P := by
  induction typed with
  | hyp h => exact .hyp h
  | trueIntro => exact .trueIntro
  | theoremE h fs ps => exact .theoremE h fs ps
  | impIntro a body ih => exact .impIntro a ih
  | impElim f a ihf iha => exact .impElim ihf iha
  | andIntro a b iha ihb => exact .andIntro iha ihb
  | andLeft a b => exact .impIntro (.and a b) (.andLeft (.hyp (i := 0) rfl))
  | andRight a b => exact .impIntro (.and a b) (.andRight (.hyp (i := 0) rfl))
  | orLeft a b => exact .impIntro a (.orLeft b (.hyp (i := 0) rfl))
  | orRight a b => exact .impIntro b (.orRight a (.hyp (i := 0) rfl))
  | orElim a b c =>
    exact .impIntro (.or a b) (.impIntro (.imp a c) (.impIntro (.imp b c)
      (.orElim c (.hyp (i := 2) rfl)
        (.impElim (.hyp (i := 2) rfl) (.hyp (i := 0) rfl))
        (.impElim (.hyp (i := 1) rfl) (.hyp (i := 0) rfl)))))
  | falseElim a => exact .impIntro (.subsumption .false .lift) (.falseElim a (.hyp (i := 0) rfl))
  | forallIntro motive body ih => exact .forallIntro motive ih
  | forallElim proof arg ih => exact .forallElim ih arg
  | existsIntro motive arg proof ih => exact .existsIntro motive arg ih
  | letE type value body ihv ihb => exact .letE type ihv ihb
  | letTerm value body ih => exact .letTerm value ih
  | letPredicate value body ih => exact .letPredicate value ih
  | ascribe type proof ih => exact .ascribe type ih
  | lem a => exact .lem a
  | conversion proof eq ih => exact .conversion ih eq
  | eqRefl =>
    apply generalize valid (.subsumption (.equal (.bvar rfl) (.bvar rfl)) .lift)
    exact .eqRefl (.bvar rfl)
  | succNeZero =>
    apply generalize valid (.imp
      (.subsumption (.equal (.app .succ (.bvar rfl)) .zero) .lift)
      (.subsumption .false .lift))
    exact .succNeZero (.bvar rfl)
  | succInj =>
    rename_i Γ H
    have type := (ProofTyping.succInj (E := E) (Ξ := Ξ) (Γ := Γ) (H := [])).regularity valid .nil
    have outer := type.inv_all.2.lam_body
    have inner := outer.inv_all.2.lam_body
    apply generalize valid outer
    apply generalize valid inner
    exact .impIntro (imp_parts inner).1 (.succInj (.hyp (i := 0) rfl))
  | eqSubst motive =>
    have type := (ProofTyping.eqSubst (H := []) motive).regularity valid .nil
    have outer := type.inv_all.2.lam_body
    have inner := outer.inv_all.2.lam_body
    apply generalize valid outer
    apply generalize valid inner
    apply Derivation.impIntro (imp_parts inner).1
    apply Derivation.impIntro (imp_parts (imp_parts inner).2).1
    have shifted := PredicateTyping.rename valid motive (Δ := 0 :: 0 :: _)
      (fun i => i + 2) (by intro i k h; exact h)
    exact .eqSubst shifted (.hyp (i := 1) rfl) (.hyp (i := 0) rfl)
  | @existsElim Γ P C H motive target =>
    have type := (ProofTyping.existsElim (H := []) motive target).regularity valid .nil
    have branch := (imp_parts (imp_parts type).2).1
    apply Derivation.impIntro (.ex motive)
    apply Derivation.impIntro branch
    apply Derivation.existsElim target (.hyp (i := 1) rfl)
    have applied := apply_shifted_lambda valid (name := ⟨`x, false⟩)
      (H := .app P.shift (.bvar 0) ::
        List.map Predicate.shift
          (.all (.lam ⟨`x, false⟩ (.imp (.app P.shift (.bvar 0)) C.shift)) :: .ex P :: H))
      branch.inv_all.2.lam_body (.hyp (i := 1) rfl)
    exact .impElim applied (.hyp (i := 0) rfl)
  | @induction Γ P H motive =>
    have type := (ProofTyping.induction (H := []) motive).regularity valid .nil
    have branch := (imp_parts (imp_parts type).2).1
    apply Derivation.impIntro (imp_parts type).1
    apply Derivation.impIntro branch
    apply Derivation.forallIntro motive.toProp
    apply Derivation.induction (PredicateTyping.shift valid motive 0)
      (.hyp (i := 1) (by simp [Predicate.shift, Predicate.rename, Term.rename])) ?_ (.bvar rfl)
    have shifted := PredicateTyping.shift valid branch 0
    simp only [Predicate.shift, Predicate.rename, Nat.not_lt_zero, ↓reduceIte] at shifted
    let step := Predicate.all (.lam ⟨`x, false⟩
      (.imp (.app P.shift (.bvar 0)) (.app P.shift (.app .succ (.bvar 0)))))
    have applied := apply_shifted_lambda valid (name := ⟨`x, false⟩)
      (H := .app P.shift.shift (.bvar 0) ::
        ((step :: .app P .zero :: H).map Predicate.shift).map Predicate.shift)
      shifted.inv_all.2.lam_body (.hyp (i := 1) (by
        simp [step, Predicate.shift, Predicate.rename, Term.rename, Renaming.lift]))
    have eq : (Predicate.rename (Renaming.lift 1 (fun i => i + 1))
        (P.rename (fun i => i + 1))) = P.shift.shift := by
      simp only [Predicate.shift, Predicate.rename_comp, Nat.not_lt_zero, ↓reduceIte]
      congr 1
      funext i
      simp [Renaming.lift, Nat.add_comm]
    simp only [eq, Term.rename, Renaming.lift, Nat.lt_succ_self, ↓reduceIte] at applied
    exact .impElim applied (.hyp (i := 0) rfl)

end PRAProver.Translation
