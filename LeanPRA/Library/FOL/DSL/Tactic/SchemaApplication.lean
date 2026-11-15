module

public meta import LeanPRA.Library.FOL.DSL.Tactic.Basic

/-!
# Applying theorems with formula parameters

`papply theorem (p := fun r i => A)[t]` supplies a numerical formula code to a PRA theorem
parameter. The last listed variable occupies position zero, following nested binder order. Other
object variables in `A` are captured from the current proof context. The formula code of the
instantiated theorem is then calculated, with a PRA equality proof, to carry out its substitutions.
Ordinary application then instantiates the theorem's object quantifiers and leaves its premises as
goals. -/

public meta section

namespace LeanPRA.Library.FOL.DSL

open Lean Elab Command LeanPRA.Surface LeanPRA.Surface.Tactic
open TacticSupport

syntax (name := papplyFormulaTac) (priority := high)
  "papply " ident folSchemaActual+ ("[" folTerm,* "]")? : praTactic

/-- Instantiate numerical formula parameters before applying an object theorem. -/
@[pra_tactic papplyFormulaTac]
def evalFormulaApplication : Tactic := closedFirst fun stx => do
  let `(praTactic| papply $name:ident $actuals:folSchemaActual* $[[$args:folTerm,*]]?) := stx |
    throwUnsupportedSyntax
  let g ← currentGoal
  let (proof, type) ← formulaInstance g name actuals
  let (proof, type) ← normalizeProvable proof type
  applyInstantiated g (← proofRule g proof type) (args.map (·.getElems) |>.getD #[])

end LeanPRA.Library.FOL.DSL
