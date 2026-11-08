module

public meta import LeanPRA.Export.Writer

/-!
# PRA export driver

`main` runs the compiled exporter from a Lean process.
-/

public meta unsafe def main (args : List String) : IO Unit := LeanPRA.Export.run args
