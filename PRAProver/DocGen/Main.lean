import PRAProver.DocGen.Driver

/-!
# PRA documentation entry point

`main` runs the documentation build executable.
The legacy import header makes Lean initialize both runtime and frontend metadata at startup.
-/

unsafe def main (args : List String) : IO Unit := PRAProver.DocGen.run args
