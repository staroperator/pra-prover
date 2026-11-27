module

public meta import PRAProver.Export.Writer

/-!
# PRA export driver

`main` runs the compiled exporter from a Lean process.
-/

public meta unsafe def main (args : List String) : IO Unit := PRAProver.Export.run args
