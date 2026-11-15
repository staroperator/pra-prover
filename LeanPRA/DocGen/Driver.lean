module

public meta import LeanPRA.DocGen.Writer
public meta import LeanPRA.DocGen.Site

/-!
# PRA documentation driver

`run` runs module extraction or assembles the static site for the Lake documentation facets.
-/

/-- Run the documentation build operation selected by Lake. -/
public meta unsafe def LeanPRA.DocGen.run (args : List String) : IO Unit := do
  match args with
  | ["module", directory, owner] => LeanPRA.DocGen.writeModule directory owner.toName
  | "site" :: dataDir :: directory :: assets :: owners =>
    LeanPRA.DocGen.writeSite dataDir directory assets owners
  | _ => throw (IO.userError ("usage: docgen module DIRECTORY MODULE | " ++
      "docgen site DATA DIRECTORY ASSETS MODULE..."))
