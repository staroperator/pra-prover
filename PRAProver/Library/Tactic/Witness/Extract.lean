module

public meta import PRAProver.Library.Tactic.Witness.Compiler

/-!
# Ordinary witness extraction

Inside a `pra` block, `extract_witness thm` publishes `thm.witness` and `thm.witness_correct`.
Their arguments come from the statement of `thm`: its declaration parameters, universal numerical
binders, and witnesses of existential premises. The caller can use this pair directly.
-/

public meta section

namespace PRAProver.Library.Tactic.Witness

open Lean Elab Command

/-- Extract one numerical program and correctness theorem for each source theorem. -/
syntax (name := extractWitness) "extract_witness" (ppSpace colGt ident)+ : praDecl

@[command_elab PRAProver.Surface.praEntry]
def elaborateExtractWitness : CommandElab := fun stx => do
  let `(praDecl| extract_witness $names:ident*) := stx[0] | throwUnsupportedSyntax
  for name in names do withRef name do Compiler.compileWitness name.getId name

end PRAProver.Library.Tactic.Witness
