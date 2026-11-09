module

public meta import Lean

/-!
# PRA frontend options

- `pra.maxDepth` limits Core checking and reduction.
- `pra.recheckImports` enables checking imported declarations again.
- `editorInfoEnabled` combines server mode and Lean's information state.

Builtin initialization reads the depth option from an empty options map to use its default.
Checking user declarations and auditing imports read the applicable user options.
-/

public meta section

/-- Recursion depth limit for Core checking and reduction. -/
register_option pra.maxDepth : Nat := {
  defValue := 1024
  descr := "recursion-depth limit for PRA core checking and reduction (also during imports)"
}

/-- When true, recheck all imported PRA declarations from scratch instead of trusting `.olean`
exports. -/
register_option pra.recheckImports : Bool := {
  defValue := false
  descr := "recheck the complete imported PRA closure (explicit audit; default trusts build cache)"
}

namespace LeanPRA.Surface

open Lean Elab Command

/-- Whether this elaboration should collect transient PRA editor information. -/
def editorInfoEnabled : CommandElabM Bool := do
  let opts ← getOptions
  return (← getInfoState).enabled && Elab.inServer.get opts

end LeanPRA.Surface
