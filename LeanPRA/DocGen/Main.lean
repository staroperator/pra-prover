import LeanPRA.DocGen.Driver

/-!
# PRA documentation entry point

`main` runs the documentation build executable.
The legacy import header makes Lean initialize both runtime and frontend metadata at startup.
-/

unsafe def main (args : List String) : IO Unit := LeanPRA.DocGen.run args
