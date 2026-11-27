import Lake

open Lake DSL

/-!
# PRA builds, exports, and documentation

- The module facet `pra` writes a module's specification and object file after its imports are
  built.
- The library facet `pra` collects exports in dependency order and writes `modules.txt`.
- The optional `docs` facet documents PRA declarations in the library's root modules and imports.

The default `PRAProver` build runs its `pra` facet and builds all Library source modules.
-/

package «pra-prover» where
  version := v!"0.1.0"

@[default_target]
lean_lib PRAProver where
  globs := #[.one `PRAProver]
  precompileModules := true
  defaultFacets := #[LeanLib.leanArtsFacet, LeanLib.facetKind ++ `pra]

lean_lib PRAExport where
  roots := #[`PRAProver.Export.Specification, `PRAProver.Export.Writer]
  precompileModules := true

private def exportMarker (pkg : Package) (owner : Lean.Name) : System.FilePath :=
  Lean.modToFilePath pkg.irDir owner "pra-export"

private def removePair (dir : System.FilePath) (owner : Lean.Name) : IO Unit := do
  for ext in ["pra", "prao"] do
    let path := Lean.modToFilePath dir owner ext
    if ← path.pathExists then IO.FS.removeFile path

private def exportAfter (pkg : Package) (owner : Lean.Name) (deps : Job Unit) :
    FetchM (Job System.FilePath) := do
  let some writer ← findModule? `PRAProver.Export.Writer | error "exporter module missing"
  let native ← writer.dynlib.fetch
  let driver := writer.pkg.dir / "PRAProver/Export/Main.lean"
  let source ← inputTextFile driver
  let config ← inputTextFile (writer.pkg.dir / "lakefile.lean")
  let deps := ((deps.mix source).mix config).zipWith (fun _ p => p) native
  let out := pkg.buildDir / "pra"
  let marker := exportMarker pkg owner
  if ← marker.pathExists then
    unless (← IO.FS.readFile marker).isEmpty do
      for ext in ["pra", "prao"] do
        unless ← (Lean.modToFilePath out owner ext).pathExists do
          if ← marker.pathExists then IO.FS.removeFile marker
  deps.mapM fun path => do
    buildFileUnlessUpToDate' marker do
      let plugins := (path.deps ++ path.runtimeOnlyDeps ++ #[path]).map fun lib =>
        s!"--{if lib.plugin then "plugin" else "load-dynlib"}={lib.path}"
      let args := #["module", out.toString, marker.toString, owner.toString]
      proc { cmd := (← getLean).toString
             env := ← getAugmentedEnv
             args := plugins ++ #[s!"--root={writer.pkg.dir}", "--run", driver.toString] ++ args }
    return marker

module_facet pra (mod) : Option System.FilePath := do
  let pkg ← getRootPackage
  let imports ← (← mod.transImports.fetch).await
  let arts ← mod.leanArts.fetch
  -- Modules without the PRA environment extension have no PRA declarations.
  if mod.name != `PRAProver.Surface.Environment &&
      !imports.any (·.name == `PRAProver.Surface.Environment) then
    return ← arts.mapM fun _ => do
      removePair (pkg.buildDir / "pra") mod.name
      let marker := exportMarker pkg mod.name
      if ← marker.pathExists then IO.FS.removeFile marker
      return none
  let dependencies ← (← (← mod.imports.fetch).await).mapM fun imp => fetch <| imp.facet `pra
  let deps := (Job.mixArray dependencies).mix arts
  return (← exportAfter pkg mod.name deps).map (some ·)

private def exportModules (lib : LeanLib) : FetchM (Array Module) := do
  let mut roots ← lib.getModuleArray
  if lib.name == `PRAProver then
    let (_, names) ← StateT.run (s := #[]) do
      (Glob.submodules `PRAProver.Library).forEachModuleIn lib.pkg.dir fun name =>
        modify (·.push name)
    for name in names.qsort (fun a b => a.toString < b.toString) do
      let some mod := lib.pkg.findModule? name | error s!"unknown module {name}"
      roots := roots.push mod
  let mut modules := OrdModuleSet.empty
  for root in roots do
    modules := modules.appendArray (← (← root.transImports.fetch).await)
    modules := modules.insert root
  return modules.toArray

private def pruneExports (dir : System.FilePath) (owners : Array String) : IO Unit := do
  let keep := owners.flatMap fun owner =>
    #[Lean.modToFilePath dir owner.toName "pra", Lean.modToFilePath dir owner.toName "prao"]
  for path in ← dir.walkDir do
    if path.extension == some "pra" || path.extension == some "prao" then
      unless keep.contains path do IO.FS.removeFile path

library_facet pra (lib) : System.FilePath := do
  let pkg ← getRootPackage
  let modules ← exportModules lib
  let jobs ← modules.mapM fun mod => fetch <| mod.facet `pra
  let markers := (Job.collectArray jobs).map (·.filterMap id)
  let some writer ← findModule? `PRAProver.Export.Writer | error "exporter module missing"
  let config ← inputTextFile (writer.pkg.dir / "lakefile.lean")
  let markers := markers.zipWith (fun files _ => files) config
  let out := pkg.buildDir / "pra"
  let marker := out / "modules.txt"
  let names := modules.toList.map (·.name.toString)
  let trace := Hash.ofString (String.intercalate "\n" names)
  markers.mapM fun files => do
    addTrace (BuildTrace.ofHash trace)
    buildFileUnlessUpToDate' marker do
      let mut owners := #[]
      for file in files do
        for owner in (← IO.FS.readFile file).splitOn "\n" do
          unless owner.isEmpty || owners.contains owner do owners := owners.push owner
      pruneExports out owners
      let temporary := marker.addExtension "tmp"
      IO.FS.writeFile temporary (String.intercalate "\n" owners.toList ++ "\n")
      IO.FS.rename temporary marker
    return marker

lean_lib PRADocGen where
  roots := #[`PRAProver.DocGen.Pretty, `PRAProver.DocGen.Writer,
    `PRAProver.DocGen.Site, `PRAProver.DocGen.Driver]

lean_exe praDocGen where
  root := `PRAProver.DocGen.Main
  supportInterpreter := true

private def docgenExecutable : FetchM (Job System.FilePath) := do
  let some exe ← findLeanExe? `praDocGen | error "docgen executable missing"
  exe.exe.fetch

private def docgen (args : Array String) (deps : Job Unit) : FetchM (Job Unit) := do
  let native ← docgenExecutable
  let deps := deps.zipWith (fun _ p => p) native
  deps.mapM fun path => do
    proc { cmd := path.toString
           env := ← getAugmentedEnv
           args }

module_facet docs (mod) : System.FilePath := do
  let pkg ← getRootPackage
  let arts ← mod.leanArts.fetch
  let directory := pkg.buildDir / "doc-data"
  let path := directory / s!"{mod.name}.json"
  let native ← docgenExecutable
  let config ← inputTextFile (pkg.dir / "lakefile.lean")
  let deps := (arts.mix config).zipWith (fun _ path => path) native
  deps.mapM fun executable => do
    buildFileUnlessUpToDate' path do
      proc { cmd := executable.toString
             env := ← getAugmentedEnv
             args := #["module", directory.toString, mod.name.toString] }
    return path

library_facet docs (lib) : System.FilePath := do
  let pkg ← getRootPackage
  let modules := (← (← lib.modules.fetch).await).qsort
    (fun a b => a.name.toString < b.name.toString)
  let names := modules.map (·.name)
  let jobs ← modules.mapM fun mod => fetch <| mod.facet `docs
  let mut deps := (Job.mixArray jobs)
  for file in ["style.css", "search.js"] do
    deps := deps.mix (← inputTextFile (pkg.dir / "PRAProver/DocGen" / file))
  let directory := pkg.buildDir / "doc"
  -- Site assembly checks its cache and removes pages outside the current import graph.
  let job ← docgen (#["site", (pkg.buildDir / "doc-data").toString, directory.toString,
    (pkg.dir / "PRAProver/DocGen").toString] ++ names.map (·.toString)) deps
  return job.map fun _ => directory / "index.html"
