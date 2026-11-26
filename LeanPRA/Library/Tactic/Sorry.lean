module

public meta import LeanPRA.Surface.Tactic

/-!
# PRA proof placeholder

Use `sorry` while writing a PRA proof. It stops elaboration with an error that shows the
current goal's target. The proof stays unfinished until the placeholder is replaced.
-/

public meta section

namespace LeanPRA.Library.Tactic

open Lean LeanPRA.Surface LeanPRA.Surface.Tactic

syntax (name := sorryTac) "sorry" : praTactic

/-- Report the first open goal at the placeholder's source location. -/
@[pra_tactic sorryTac]
def evalSorry : Tactic := fun stx => do
  let goal ← getGoal
  let target := Core.betaReducePredicate goal.maxDepth (goal.projection.encodePredicate goal.target)
  let target ← delabPredicate goal.names target
  throwErrorAt stx "unfinished PRA proof (`sorry`)\n⊢ {← formatSyntax `praExpr target}"

end LeanPRA.Library.Tactic
