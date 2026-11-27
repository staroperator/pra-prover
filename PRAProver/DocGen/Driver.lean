module

public meta import PRAProver.DocGen.Writer
public meta import PRAProver.DocGen.Site

/-!
# PRA documentation driver

`run` runs module extraction or assembles the static site for the Lake documentation facets.
-/

/-- Run the documentation build operation selected by Lake. -/
public meta unsafe def PRAProver.DocGen.run (args : List String) : IO Unit := do
  match args with
  | ["module", directory, owner] => PRAProver.DocGen.writeModule directory owner.toName
  | "site" :: dataDir :: directory :: assets :: owners =>
    PRAProver.DocGen.writeSite dataDir directory assets owners
  | _ => throw (IO.userError ("usage: docgen module DIRECTORY MODULE | " ++
      "docgen site DATA DIRECTORY ASSETS MODULE..."))
