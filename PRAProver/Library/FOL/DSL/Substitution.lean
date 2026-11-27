module

public meta import PRAProver.Library.Tactic.Construction
public import PRAProver.Library.FOL.Common.Substitution

/-!
# Finite substitutions for quoted formulas

A substitution stores a finite list of replacement terms and a variable offset for later indices.
Its equations are checked PRA proofs of pointwise equality.
`FOL.consSubst` supplies the listed terms, and `FOL.shiftSubst` supplies the remaining variables.

- `SubstitutionView.encode` constructs the corresponding numerical substitution function.
- `composeSubstitutions` calculates simultaneous substitution of replacement terms.
- `normalizeSubstitution` simplifies substitutions built from `FOL.consSubst`, `FOL.shiftSubst`,
  and `FOL.liftSubst`.
-/

public meta section

namespace PRAProver.Library.FOL.DSL

open Lean Elab Command PRAProver.Core
open PRAProver.Library.Tactic.Construction

structure SubstitutionView where
  values : List Core.Term := []
  offset : Nat := 0
  deriving BEq, Repr, Inhabited

def SubstitutionView.encode (L : Core.Term) (s : SubstitutionView) : Core.Term :=
  s.values.foldr (fun t rest => applyDefinition `FOL.consSubst [] [t, rest])
    (applyDefinition `FOL.shiftSubst [] [L, numeral s.offset])

structure SubstitutionCalculation where
  substitution : SubstitutionView
  proof : Core.Proof

private def pointwise (f g : Core.Term) (proof : Core.Proof) : Core.Proof :=
  .forallIntro `i (.lam `i (.equal (.app f.shift (.bvar 0)) (.app g.shift (.bvar 0)))) proof

private def reflexive (f : Core.Term) : Core.Proof :=
  pointwise f f (.forallElim .eqRefl (.app f.shift (.bvar 0)))

private def transitive (f g h : Core.Term) (p q : Core.Proof) : Core.Proof :=
  pointwise f h (mkEqTrans (.app f.shift (.bvar 0)) (.app g.shift (.bvar 0))
    (.app h.shift (.bvar 0)) (.forallElim (shiftProof p 1 0) (.bvar 0))
      (.forallElim (shiftProof q 1 0) (.bvar 0)))

private def consCongruence (t u f g : Core.Term) (head tail : Core.Proof) : Core.Proof :=
  let source := applyDefinition `FOL.consSubst [] [t, f]
  let middle := applyDefinition `FOL.consSubst [] [u, f]
  let target := applyDefinition `FOL.consSubst [] [u, g]
  let changeHead := mkEqCongr
    (.lam `t (.app (applyDefinition `FOL.consSubst [] [.bvar 0, f.shift.shift]) (.bvar 1)))
    t.shift u.shift (shiftProof head 1 0)
  let changeTail := Core.Proof.forallElim
    (.impElim (.theoremE `FOL.consSubst_congr [f, g] []) tail) u
  pointwise source target (mkEqTrans (.app source.shift (.bvar 0))
    (.app middle.shift (.bvar 0)) (.app target.shift (.bvar 0)) changeHead
    (.forallElim (shiftProof changeTail 1 0) (.bvar 0)))

private def consSubstitution (L t : Core.Term) (tail : SubstitutionView) :
    SubstitutionCalculation :=
  let source := applyDefinition `FOL.consSubst [] [t, tail.encode L]
  let (head, args) := getAppFnArgs t
  if tail.values.isEmpty && tail.offset > 0 then
    if head == .definition `FOL.Term.var [] && args == [L, numeral (tail.offset - 1)] then
      { substitution := ⟨[], tail.offset - 1⟩
        proof := applyTheorem `FOL.consSubst_shiftSubst [L, numeral (tail.offset - 1)] }
    else { substitution := ⟨t :: tail.values, tail.offset⟩, proof := reflexive source }
  else { substitution := ⟨t :: tail.values, tail.offset⟩, proof := reflexive source }

private def composition (L f g : Core.Term) : Core.Term :=
  .lam `i (applyDefinition `FOL.Term.subst [L.shift, .app g.shift (.bvar 0)] [f.shift])

/-- Compose finite substitutions, returning a proof at every variable index. -/
partial def composeSubstitutions
    (calculate : Core.Term → CommandElabM (Core.Term × Core.Proof))
    (L : Core.Term) (f g : SubstitutionView) : CommandElabM SubstitutionCalculation := do
  let source := composition L (f.encode L) (g.encode L)
  match g.values with
  | t :: rest =>
    let tail : SubstitutionView := ⟨rest, g.offset⟩
    let (u, headProof) ← calculate (applyDefinition `FOL.Term.subst [L, t] [f.encode L])
    let next ← composeSubstitutions calculate L f tail
    let result := consSubstitution L u next.substitution
    let middle := applyDefinition `FOL.consSubst [] [u, next.substitution.encode L]
    let proof := applyTheorem `FOL.Term.subst_consSubst_congr [L, t, u]
      [f.encode L, tail.encode L, next.substitution.encode L] [headProof, next.proof]
    return { result with
      proof := transitive source middle (result.substitution.encode L) proof result.proof }
  | [] =>
    if g.offset == 0 then
      return ⟨f, applyTheorem `FOL.Term.subst_shiftSubst_zero [L] [f.encode L]⟩
    match f.values with
    | t :: rest =>
      let tail : SubstitutionView := ⟨rest, f.offset⟩
      let lowered : SubstitutionView := ⟨[], g.offset - 1⟩
      let result ← composeSubstitutions calculate L tail lowered
      let middle := composition L (tail.encode L) (lowered.encode L)
      let proof := applyTheorem `FOL.Term.subst_shiftSubst_succ_consSubst
        [L, numeral (g.offset - 1)] [t, tail.encode L]
      return { result with
        proof := transitive source middle (result.substitution.encode L) proof result.proof }
    | [] =>
      return ⟨⟨[], g.offset + f.offset⟩,
        applyTheorem `FOL.Term.subst_shiftSubst_shiftSubst
          [L, numeral f.offset, numeral g.offset]⟩

/-- Normalize a finite substitution and prove equality with its original function. -/
partial def normalizeSubstitution
    (calculate : Core.Term → CommandElabM (Core.Term × Core.Proof))
    (L input : Core.Term) : CommandElabM (Option SubstitutionCalculation) := do
  let (head, args) := getAppFnArgs input
  match head, args with
  | .definition `FOL.shiftSubst [language, count], [] =>
    unless language == L do return none
    let (value, proof) ← calculate count
    let some offset := numeralValue? value | return none
    let result : SubstitutionView := ⟨[], offset⟩
    if value == count then return some ⟨result, reflexive input⟩
    let changeOffset := mkEqCongr
      (.lam `offset (.app
        (applyDefinition `FOL.shiftSubst [] [L.shift.shift, .bvar 0]) (.bvar 1)))
      count.shift value.shift (shiftProof proof 1 0)
    return some ⟨result, pointwise input (result.encode L) changeOffset⟩
  | .definition `FOL.consSubst [t, f], [] =>
    let some tail ← normalizeSubstitution calculate L f | return none
    let (u, proof) ← calculate t
    let result := consSubstitution L u tail.substitution
    let middle := applyDefinition `FOL.consSubst [] [u, tail.substitution.encode L]
    return some { result with
      proof := transitive input middle (result.substitution.encode L)
        (consCongruence t u f (tail.substitution.encode L) proof tail.proof) result.proof }
  | .definition `FOL.liftSubst [f], [language, count] =>
    unless language == L do return none
    let some count := numeralValue? count | return none
    let some original ← normalizeSubstitution calculate L f | return none
    if count == 0 then
      let equation := applyTheorem `FOL.liftSubst_zero [L] [f]
      return some { original with
        proof := transitive input f (original.substitution.encode L) equation original.proof }
    if count > 1 then
      let inner := applyDefinition `FOL.liftSubst [L, numeral (count - 1)] [f]
      let expanded := applyDefinition `FOL.liftSubst [L, numeral 1] [inner]
      let some result ← normalizeSubstitution calculate L expanded | return none
      let equation := applyTheorem `FOL.liftSubst_liftSubst
        [L, numeral 1, numeral (count - 1)] [f]
      let reversed := pointwise input expanded
        (mkEqSymm (.app expanded.shift (.bvar 0)) (.app input.shift (.bvar 0))
          (.forallElim (shiftProof equation 1 0) (.bvar 0)))
      return some { result with
        proof := transitive input expanded (result.substitution.encode L) reversed result.proof }
    let raised ← composeSubstitutions calculate L ⟨[], 1⟩ original.substitution
    let variableZero := applyDefinition `FOL.Term.var [L, numeral 0]
    let result := consSubstitution L variableZero raised.substitution
    let sourceTail := composition L (SubstitutionView.encode L ⟨[], 1⟩) f
    let middleTail := composition L (SubstitutionView.encode L ⟨[], 1⟩)
      (original.substitution.encode L)
    let replacement := applyDefinition `FOL.Term.subst [L] [SubstitutionView.encode L ⟨[], 1⟩]
    let changeTail := pointwise sourceTail middleTail
      (mkEqCongr replacement.shift (.app f.shift (.bvar 0))
        (.app (original.substitution.encode L).shift (.bvar 0))
        (.forallElim (shiftProof original.proof 1 0) (.bvar 0)))
    let tailProof := transitive sourceTail middleTail (raised.substitution.encode L)
      changeTail raised.proof
    let sourceCons := applyDefinition `FOL.consSubst [] [variableZero, sourceTail]
    let second := applyDefinition `FOL.consSubst [] [variableZero, raised.substitution.encode L]
    let equation := applyTheorem `FOL.liftSubst_one [L] [f]
    return some { result with
      proof := transitive input sourceCons (result.substitution.encode L)
        equation (transitive sourceCons second (result.substitution.encode L)
          (consCongruence variableZero variableZero sourceTail (raised.substitution.encode L)
            (.forallElim .eqRefl variableZero) tailProof) result.proof) }
  | _, _ => return none

end PRAProver.Library.FOL.DSL
