module

public import PRAProver.Library.FOL.PRA.Numeral
public meta import PRAProver.Library.Tactic.Construction

/-!
# Substitution in quoted first-order PRA formulas

`QuotedSubstitution.instantiate` computes the instance of a formula built by proof translation.
`QuotedSubstitution.shift` raises the free variables of the formula by one.
The traversal uses the common substitution equations with PRA's symbol and arity proofs.
The lemmas below combine equalities for already computed parts into an equality for the whole
term or formula. An evaluation symbol keeps its program index when substitution acts on its
argument.
-/

@[expose] public section

pra

namespace FOL.Term

theorem instantiateAt_eq_of_shift_eq : ∀ L t d u, shift L d t = u →
    instantiateAt L 0 t d d = u := by
  intro L t d u h
  rw [instantiateAt, ltb_eq_zero_of_ge d d (le_refl d), ite_zero, sub_self, eqb_self, ite_succ]
  exact h

theorem subst_app_one_eq (f : Nat → Nat) : ∀ L j t u, Language.IsFunction L j →
    Language.functionSymbolArity L j = 1 → subst f L t = u →
    subst f L (app L j t) = app L j u := by
  intro L j t u hj ha h
  rw [subst_app_one f L j t hj ha, h]

theorem subst_app_two_eq (f : Nat → Nat) : ∀ L j t u v w, Language.IsFunction L j →
    Language.functionSymbolArity L j = 2 → subst f L t = v → subst f L u = w →
    subst f L (app L j (pair t u)) = app L j (pair v w) := by
  intro L j t u v w hj ha ht hu
  rw [subst_app_two f L j t u hj ha, ht, hu]

theorem shift_eq_of_subst_eq : ∀ L d t u, subst (shiftSubst L d) L t = u →
    shift L d t = u := fun L d t u h => eq_trans (shift_eq_subst_shiftSubst L d t) h

end FOL.Term

namespace FOL.Formula

theorem substWithDepth_equal_eq (f : Nat → Nat → Nat) : ∀ L t u d v w,
    Term.subst (f d) L t = v → Term.subst (f d) L u = w →
    substWithDepth f L (equal L t u) d = equal L v w := by
  intro L t u d v w ht hu
  rw [substWithDepth_equal f, ht, hu]

theorem substWithDepth_imp_eq (f : Nat → Nat → Nat) : ∀ L A B d C D,
    substWithDepth f L A d = C → substWithDepth f L B d = D →
    substWithDepth f L (imp A B) d = imp C D := by
  intro L A B d C D hA hB
  rw [substWithDepth_imp f, hA, hB]

theorem substWithDepth_all_eq (f : Nat → Nat → Nat) : ∀ L A d B,
    substWithDepth f L A (S d) = B → substWithDepth f L (all A) d = all B := by
  intro L A d B h
  rw [substWithDepth_all f, h]

theorem subst_eq_of_substWithDepth_eq (f : Nat → Nat) : ∀ L A B,
    substWithDepth (FOL.liftSubst f L) L A 0 = B → subst f L A = B :=
  fun L A B h => h

theorem instantiate_eq_of_substWithDepth_eq : ∀ L A t B,
    substWithDepth (Term.instantiateAt L 0 t) L A 0 = B → instantiate L A t = B :=
  fun L A t B h => h

theorem shift_eq_of_substWithDepth_eq : ∀ L A B,
    substWithDepth (fun d i => Term.var L (ite (ltb i d) i (S i))) L A 0 = B →
    shift L A = B := fun L A B h => h

end FOL.Formula

namespace FOL.PRA.QuotedSubstitution

open FOL

/-- Use the first-order induction axiom with given codes for its base and successor instances. -/
theorem induction_instances : ∀ p base step, Formula.isQuantifierFree language p = 1 →
    Formula.subst (consSubst (Term.const language 0) (shiftSubst language 0)) language p = base →
    Formula.subst (consSubst (Term.app language 0 (Term.var language 0)) (shiftSubst language 1))
      language p = step →
    Provable language isAxiom (Formula.imp base
      (Formula.imp (Formula.all (Formula.imp p step)) (Formula.all p))) := by
  intro p base step qf hb hs
  rw [← hb, ← hs]
  exact FOL.PRA.«induction» p qf

end FOL.PRA.QuotedSubstitution

end

end

public meta section

namespace PRAProver.Library.FOL.PRA.QuotedSubstitution

open Lean hiding Term
open Lean.Elab.Command PRAProver.Core PRAProver.Library.Tactic.Construction

private def language := applyDefinition `FOL.PRA.language

private def varTerm (i : Nat) := applyDefinition `FOL.Term.var [language, numeral i]

private abbrev Result := Term × Proof

/-- Apply `f` to the variables of a quoted term. The caller supplies the checked action on each
variable, which depends on the current quantifier depth. -/
private partial def mapTerm (f : Term) (variableAt : Nat → CommandElabM Result) (t : Term) :
    CommandElabM Result := do
  match getAppFnArgs t with
  | (.definition `FOL.Term.const [], [_, .zero]) =>
    return (t, applyTheorem `FOL.Term.subst_const [language, .zero] [f]
      [applyTheorem `FOL.PRA.isConstant_zero])
  | (.definition `FOL.PRA.num [], [n]) => return (t, applyTheorem `FOL.PRA.subst_num [n] [f])
  | (.definition `FOL.Term.var [], [_, i]) =>
    let some n := numeralValue? i | throwError "expected a quoted variable index"
    let (u, h) ← variableAt n
    return (u, mkEqTrans (applyDefinition `FOL.Term.subst [language, t] [f]) (.app f i) u
      (applyTheorem `FOL.Term.subst_var [language, i] [f]) h)
  | (.definition `FOL.Term.app [], [_, j, arg]) =>
    let app x := applyDefinition `FOL.Term.app [language, j, x]
    if j == numeral 1 then
      let (.definition `pair [], [x, y]) := getAppFnArgs arg | throwError "expected pair arguments"
      let (u, hu) ← mapTerm f variableAt x
      let (v, hv) ← mapTerm f variableAt y
      return (app (applyDefinition `pair [u, v]), applyTheorem
        `FOL.Term.subst_app_two_eq [language, j, x, y, u, v] [f]
        [applyTheorem `FOL.PRA.isFunction_pair,
          applyTheorem `FOL.PRA.pair_arity, hu, hv])
    let (hj, ha) ← if j == numeral 0 then
        pure (applyTheorem `FOL.PRA.isFunction_succ, applyTheorem `FOL.PRA.succ_arity)
      else do
        let (.definition `FOL.Language.functionFamilyMember [], [_, .zero, e]) := getAppFnArgs j
          | throwError "expected a first-order PRA program symbol"
        pure (applyTheorem `FOL.PRA.isFunction_eval [e],
          applyTheorem `FOL.PRA.eval_arity [e])
    let (u, h) ← mapTerm f variableAt arg
    return (app u, applyTheorem `FOL.Term.subst_app_one_eq [language, j, arg, u] [f] [hj, ha, h])
  | _ => throwError "expected a quoted first-order PRA term"

private def instanceTerm (f x : Term) (d : Nat) (t : Term) : CommandElabM Result :=
  mapTerm (.app f (numeral d)) (fun i => do
    if i < d then return (varTerm i, applyTheorem `FOL.Term.instantiateAt_below
      [] [language, x, numeral d, numeral i] [.forallElim .eqRefl .zero])
    if d < i then return (varTerm (i - 1), applyTheorem `FOL.Term.instantiateAt_above
      [] [language, x, numeral d, numeral (i - 1)] [.forallElim .eqRefl .zero])
    let atPosition u h :=
      applyTheorem `FOL.Term.instantiateAt_eq_of_shift_eq [language, x, numeral d, u] [] [h]
    if d == 0 then return (x, atPosition x (applyTheorem `FOL.Term.shift_zero [language, x]))
    let shift := applyDefinition `FOL.shiftSubst [] [language, numeral d]
    let (u, h) ← mapTerm shift (fun j =>
      pure (varTerm (j + d), .forallElim .eqRefl (varTerm (j + d)))) x
    return (u, atPosition u (applyTheorem `FOL.Term.shift_eq_of_subst_eq
      [language, numeral d, x, u] [] [h]))) t

private partial def mapFormula (f : Term) (termAt : Nat → Term → CommandElabM Result)
    (d : Nat) (a : Term) : CommandElabM Result := do
  let depth := numeral d
  match getAppFnArgs a with
  | (.definition `FOL.Formula.falsum [], []) =>
    return (a, applyTheorem `FOL.Formula.substWithDepth_falsum [language, depth] [f])
  | (.definition `FOL.Formula.equal [], [_, l, r]) =>
    let (u, hu) ← termAt d l
    let (v, hv) ← termAt d r
    return (applyDefinition `FOL.Formula.equal [language, u, v],
      applyTheorem `FOL.Formula.substWithDepth_equal_eq [language, l, r, depth, u, v] [f] [hu, hv])
  | (.definition `FOL.Formula.imp [], [p, q]) =>
    let (u, hu) ← mapFormula f termAt d p
    let (v, hv) ← mapFormula f termAt d q
    return (applyDefinition `FOL.Formula.imp [u, v],
      applyTheorem `FOL.Formula.substWithDepth_imp_eq [language, p, q, depth, u, v] [f] [hu, hv])
  | (.definition `FOL.Formula.all [], [p]) =>
    let (u, h) ← mapFormula f termAt (d + 1) p
    return (applyDefinition `FOL.Formula.all [u],
      applyTheorem `FOL.Formula.substWithDepth_all_eq [language, p, depth, u] [f] [h])
  | _ => throwError "expected a quoted first-order PRA formula"

/-- Return the formula obtained by replacing the outer variable in `a` with `argument`, and a
checked PRA equality from `Formula.instantiate language a argument` to that formula. -/
def instantiate (a argument : Term) : CommandElabM (Term × Proof) := do
  let f := applyDefinition `FOL.Term.instantiateAt [language, .zero, argument]
  let (u, h) ← mapFormula f (instanceTerm f argument) 0 a
  return (u, applyTheorem `FOL.Formula.instantiate_eq_of_substWithDepth_eq
    [language, a, argument, u] [] [h])

/-- Replace position zero in a quantifier-free formula. Later positions start at `offset`.
Induction uses offset zero in the base and offset one under the step quantifier. -/
def substituteQF (a x : Term) (offset : Nat) : CommandElabM (Term × Proof) := do
  let k := numeral offset
  let shift := applyDefinition `FOL.shiftSubst [] [language, k]
  let subst := applyDefinition `FOL.consSubst [] [x, shift]
  let f := applyDefinition `FOL.liftSubst [language] [subst]
  let termAt (d : Nat) (t : Term) := do
    unless d == 0 do throwError "expected a quantifier-free induction formula"
    mapTerm (.app f .zero) (fun
      | 0 => pure (x, applyTheorem `FOL.liftSubst_consSubst_shiftSubst_zero [language, x, k])
      | i + 1 => pure (varTerm (i + offset),
          applyTheorem `FOL.liftSubst_consSubst_shiftSubst_succ [language, x, k, numeral i])) t
  let (u, h) ← mapFormula f termAt 0 a
  return (u, applyTheorem `FOL.Formula.subst_eq_of_substWithDepth_eq [language, a, u] [subst] [h])

/-- Raise each free variable of a quoted formula by one and prove the defining shift equation. -/
def shift (a : Term) : CommandElabM (Term × Proof) := do
  let index := Term.bvar 0
  let depth := Term.bvar 1
  let adjusted := applyDefinition `ite
    [applyDefinition `ltb [index, depth], index, .app .succ index]
  let f := Term.lam `d (.lam `i (applyDefinition `FOL.Term.var [language, adjusted]))
  let termAt d := mapTerm (.app f (numeral d)) fun i => do
    let j := if i < d then i else i + 1
    let before := applyDefinition `ite
      [applyDefinition `ltb [numeral i, numeral d], numeral i, numeral (i + 1)]
    let proof := applyTheorem `eq_congr [before, numeral j]
      [applyDefinition `FOL.Term.var [language]] [.forallElim .eqRefl (numeral j)]
    return (varTerm j, proof)
  let (u, h) ← mapFormula f termAt 0 a
  return (u, applyTheorem `FOL.Formula.shift_eq_of_substWithDepth_eq [language, a, u] [] [h])

end PRAProver.Library.FOL.PRA.QuotedSubstitution
