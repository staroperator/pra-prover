module

public meta import LeanPRA.Surface.IDE
public meta import LeanPRA.DocGen.Pretty

/-!
# PRA documentation extraction

`writeModule` reads a module's own checked Core declarations and writes documentation data.
Lean module comments and persistent editor metadata supply the documentation text.
-/

meta section

namespace LeanPRA.DocGen

open Lean Surface

private unsafe def hasDeclarations (owner : Name) : IO Bool := do
  let (data, region) ← readModuleData (← findOLean owner)
  try
    IO.ofExcept (CoreEnvironment.hasModuleDeclarations data owner)
  finally
    region.free

private def writeData (directory : System.FilePath) (owner : Name)
    (docs entries : Array Json) : IO Unit := do
  IO.FS.createDirAll directory
  let path := directory / s!"{owner}.json"
  let temporary := path.addExtension "tmp"
  IO.FS.writeFile temporary (Json.mkObj [
    ("module", toJson owner.toString),
    ("moduleDocs", .arr docs),
    ("declarations", .arr entries)]).compress
  IO.FS.rename temporary path

private def moduleComments (owner : Name) (docs : Array Lean.ModuleDoc)
    (declarations : Array Core.Declaration) (metadata : NameMap DeclarationMetadata) :
    Array Json := Id.run do
  let mut positions : Array (Option Position) := #[]
  let mut next := none
  -- Place declarations without locations with the next located declaration in export order.
  for declaration in declarations.reverse do
    if let some location := (metadata.find? declaration.name).bind (·.location?) then
      if location.module == owner then next := some location.range.pos
    positions := positions.push next
  positions := positions.reverse
  let located := positions.any Option.isSome
  let docs := docs.toList.mergeSort fun a b =>
    !Position.lt b.declarationRange.pos a.declarationRange.pos
  return docs.toArray.map fun doc =>
    let before := if !located then 0 else
      (positions.findIdx? fun pos =>
        pos.any fun pos => !Position.lt pos doc.declarationRange.pos).getD declarations.size
    Json.mkObj [("doc", toJson doc.doc), ("before", toJson before)]

/-- Write all PRA declarations owned by `owner`, preserving their order in the module export.
An empty export skips loading dependencies. For populated modules, stored source positions place
module comments between declarations. Parser and notation extensions are initialized while PRA
imports reuse cached Core admission. -/
public unsafe def writeModule (directory : System.FilePath) (owner : Name) : IO Unit := do
  initSearchPath (← findSysroot)
  unless ← hasDeclarations owner do
    writeData directory owner #[] #[]
    return
  enableInitializersExecution
  let env ← importModules #[{ module := owner }] {} (loadExts := true)
  let mut declarations := #[]
  let mut context : Pretty.Context := {}
  let mut metadata : NameMap DeclarationMetadata := {}
  for i in [:env.header.modules.size] do
    for entry in CoreEnvironment.getModuleEntries env i do
      if entry.owner == owner then declarations := declarations ++ entry.declarations
      for d in entry.declarations do context := context.add d
      for dependency in entry.dependencies do
        for d in dependency.declarations do context := context.add d
    for (name, entry) in declarationMetadata.getModuleEntries env i do
      metadata := metadata.insert name entry
  context := context.withNotations env
  let mut seen : NameSet := {}
  let mut entries := #[]
  for declaration in declarations do
    if seen.contains declaration.name then
      throw (IO.userError s!"duplicate PRA declaration: {declaration.name}")
    seen := seen.insert declaration.name
    let (signature, body) := Pretty.declaration context declaration
    let signatureCode := Pretty.render context signature
    let bodyCode := body.map (Pretty.render context)
    let plain := fun code => String.join (code.toList.map Pretty.CodeSpan.text)
    let kind := match declaration with
      | .function _ => "function"
      | .predicate _ => "predicate"
      | .theoremE _ => "theorem"
    entries := entries.push (Json.mkObj [
      ("name", toJson declaration.name.toString), ("kind", toJson kind),
      ("signature", toJson (plain signatureCode)),
      ("body", toJson (bodyCode.map plain)),
      ("signatureCode", toJson signatureCode),
      ("bodyCode", toJson bodyCode),
      ("doc", toJson ((metadata.find? declaration.name).bind (·.doc?)))])
  writeData directory owner
    (moduleComments owner ((getModuleDoc? env owner).getD #[]) declarations metadata) entries

end LeanPRA.DocGen
