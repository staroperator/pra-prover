module

public import LeanPRA.Library.FOL.Common.Proof.Congruence
public meta import LeanPRA.Library.FOL.DSL.Tactic.Context
public meta import LeanPRA.Library.FOL.DSL.Proof.Logic

/-!
# Equality substitution in first-order formulas

`psubst h` uses an equation `x = t` to replace the object variable `x` in the goal. It applies
`FOL.Equality.substitution_congruence` for the goal’s language and theory, including quoted
formulas. The assumptions and object-variable context stay available.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL

open Lean Elab Command LeanPRA.Surface LeanPRA.Surface.Tactic
open TacticSupport
open LeanPRA.Library.Tactic.Construction

syntax (name := psubstTac) "psubst " folRef : praTactic

/-- Substitute an equal term using the checked formula-substitution theorem. -/
@[pra_tactic psubstTac]
def evalSubst : Tactic := closedFirst fun stx => do
  let `(praTactic| psubst $ref:folRef) := stx | throwUnsupportedSyntax
  let g ← currentGoal
  let target := g.formula
  let equation ← rule g ref
  let (p, graph) ← equation.run {}
  let .equal (.var x) t := graph.nodes[p]!.formula |
    throwError "psubst expects an equation with a variable on the left"
  let L := languageTerm g.theory.language
  let T := applyDefinition (g.theory.name ++ `isAxiom)
  let arguments := [L, T, ← (TermView.var x).encode L [] g.free, ← t.encode L [] g.free,
    ← target.encode L [x] g.free]
  let congruence := `FOL.Equality.substitution_congruence
  let some (.theoremE declaration) := (← getGoal).environment.lookup congruence |
    throwError "unknown theorem {congruence}"
  let transport ← proofRule g (.theoremE congruence arguments [])
    (declaration.type.instantiate arguments [])
  refineDerivation g do
    let equivalence ← mp (← transport) (← equation)
    let backward ← conjunctionRight equivalence
    return ([target.replace x t], fun proofs => mp backward proofs[0]!)

end LeanPRA.Library.FOL.DSL
