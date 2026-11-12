module

public meta import LeanPRA.Surface.Primitive

/-!
# PRA environments and module imports

Environment extensions for PRA declarations across Lean modules:

- `ModuleBundle` groups the declarations introduced by one Lean module.
- `ModuleExport` stores a module's declarations and the private dependency bundles they use.
- `importModuleExports` loads cached declarations and checks module metadata.
- `checkModuleExports` rechecks all imported declarations over the empty Core environment.
- `CoreEnvironment.getState` reads the Core declaration map.
- `CoreEnvironment.isLocal` checks whether the current module introduced a declaration.
- `publishDeclaration` records an accepted declaration in the environment extension.
- `registerNamespaceParents` registers PRA namespaces in Lean's scope table.

Private Lean imports are forwarded in `dependencies` so their PRA declarations remain available to
downstream modules. Repeated bundles from different import paths must match and are loaded once.
-/

public meta section

namespace LeanPRA.Surface

/-- The declarations introduced by `owner`, in declaration order. -/
structure ModuleBundle where
  owner : Lean.Name
  declarations : Array Core.Declaration

/-- `.olean` payload for one module, including bundles for non-exported Lean imports. -/
structure ModuleExport where
  owner : Lean.Name
  dependencies : Array ModuleBundle := #[]
  declarations : Array Core.Declaration := #[]

/-- Persistent environment state for PRA declarations and module ownership. -/
structure ModuleState where
  environment : Core.Environment := ∅
  modules : Lean.NameMap (Array Lean.Name) := {}
  order : Array Lean.Name := #[]
  localNames : Array Lean.Name := #[]
  checkedDeclarations : Nat := 0
  deriving Inhabited

private def loadBundle (recheck : Bool) (maxDepth : Nat) (state : ModuleState)
    (bundle : ModuleBundle) :
    Except String ModuleState := do
  let names := bundle.declarations.map Core.Declaration.name
  if let some previous := state.modules.find? bundle.owner then
    unless previous == names && bundle.declarations.all
        (fun d => state.environment.lookup d.name == some d) do
      throw s!"PRA import: conflicting exports for module `{bundle.owner}`; rebuild dependencies"
    return state
  let mut environment := state.environment
  for declaration in bundle.declarations do
    if recheck then
      match Core.checkDeclaration maxDepth environment declaration with
      | .ok accepted => environment := accepted
      | .error error =>
        let hint := if error.kind == .exhausted then
          " (import depth exhausted; increase -Dpra.maxDepth on the Lean invocation)" else ""
        throw (s!"PRA import `{bundle.owner}`, declaration `{declaration.name}`: " ++
          s!"{error.message}{hint}")
    else
      if (environment.lookup declaration.name).isSome then
        throw s!"PRA import `{bundle.owner}`: duplicate declaration name `{declaration.name}`"
      environment := environment.insert declaration.name declaration
  return { state with environment
                      modules := state.modules.insert bundle.owner names
                      order := state.order.push bundle.owner
                      checkedDeclarations := state.checkedDeclarations +
                        if recheck then bundle.declarations.size else 0 }

private def loadModuleExports (recheck : Bool) (maxDepth : Nat)
    (modules : Array (Lean.Name × Array ModuleExport)) : Except String ModuleState := do
  let mut state : ModuleState := {}
  for (owner, exports) in modules do
    -- Modules compiled before this extension have no export entry.
    unless exports.size ≤ 1 do
      throw s!"PRA import `{owner}`: expected at most one module export"
    for entry in exports do
      unless entry.owner == owner do
        throw s!"PRA import `{owner}`: wrong owner `{entry.owner}`"
      for dependency in entry.dependencies do
        state ← loadBundle recheck maxDepth state dependency
      state ← loadBundle recheck maxDepth state ⟨owner, entry.declarations⟩
  return state

/-- Load imported declarations without re-running the Core checker, checking owners and
duplicate names. -/
def importModuleExports (modules : Array (Lean.Name × Array ModuleExport)) :
    Except String ModuleState :=
  loadModuleExports false 0 modules

/-- Load and recheck imported declarations and dependencies with `Core.checkDeclaration`. -/
def checkModuleExports (maxDepth : Nat) (modules : Array (Lean.Name × Array ModuleExport)) :
    Except String ModuleState :=
  loadModuleExports true maxDepth modules

/-- Whether `name` is publicly exported by `env`. -/
def isPublicModule (env : Lean.Environment) (name : Lean.Name) : Bool :=
  match env.getModuleIdx? name with
  | some index => !env.header.isModule || env.header.modules[index]!.isExported
  | none => false

private initialize moduleEnvironment :
    Lean.PersistentEnvExtension ModuleExport (Core.Environment × Lean.Name) ModuleState ←
  Lean.registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun imported => do
      let context ← read
      let modules := context.env.header.modules
      unless modules.size == imported.size do
        throw (IO.userError "PRA import: inconsistent Lean module table")
      let entries := modules.zip imported |>.map fun (mod, es) => (mod.module, es)
      -- Command-line `-D` options are still raw strings during `addImportedFn`.
      let depth ← match context.opts.find? `pra.maxDepth with
        | some (.ofString value) =>
          match value.toNat? with
          | some depth => pure depth
          | none => throw (IO.userError "PRA import: pra.maxDepth must be a natural number")
        | _ => pure (pra.maxDepth.get context.opts)
      let recheck ← match context.opts.find? `pra.recheckImports with
        | some (.ofString "true") => pure true
        | some (.ofString "false") => pure false
        | some (.ofString _) =>
          throw (IO.userError "PRA import: pra.recheckImports must be true or false")
        | _ => pure (pra.recheckImports.get context.opts)
      let result :=
        if recheck then checkModuleExports depth entries else importModuleExports entries
      match result with
      | .ok state => pure state
      | .error message => throw (IO.userError message)
    addEntryFn := fun state (accepted, name) =>
      { state with environment := accepted, localNames := state.localNames.push name }
    exportEntriesFnEx := fun env state =>
      let declarations := fun names => names.filterMap state.environment.lookup
      let dependencies := state.order.filterMap fun owner => do
        let names ← state.modules.find? owner
        if names.isEmpty || isPublicModule env owner then none
        else some { owner, declarations := declarations names : ModuleBundle }
      .uniform #[{ owner := env.mainModule, dependencies
                   declarations := declarations state.localNames }]
  }

namespace CoreEnvironment

/-- Get the current `Core.Environment`. -/
def getState (env : Lean.Environment) : Core.Environment :=
  (moduleEnvironment.getState env).environment

/-- Overwrite the `Core.Environment` directly (used by tests). -/
def setState (env : Lean.Environment) (environment : Core.Environment) : Lean.Environment :=
  moduleEnvironment.modifyState env fun state => { state with environment }

/-- Get the exported `ModuleExport` array for a module index. -/
def getModuleEntries (env : Lean.Environment) (index : Lean.ModuleIdx) : Array ModuleExport :=
  moduleEnvironment.getModuleEntries env index

/-- Number of imported declarations rechecked via `pra.recheckImports`. -/
def checkedDeclarations (env : Lean.Environment) : Nat :=
  (moduleEnvironment.getState env).checkedDeclarations

/-- Whether the current module introduced the PRA declaration `name`. -/
def isLocal (env : Lean.Environment) (name : Lean.Name) : Bool :=
  (moduleEnvironment.getState env).localNames.contains name

/-- Whether any local or imported PRA declaration resides under namespace `ns`. -/
def hasNamespace (env : Lean.Environment) (ns : Lean.Name) : Bool :=
  let state := moduleEnvironment.getState env
  let contains := fun name : Lean.Name => ns.isPrefixOf name.getPrefix
  state.localNames.any contains || state.order.any fun owner =>
    ((state.modules.find? owner).getD #[]).any contains

end CoreEnvironment

/-- Register `name` and all of its parent prefixes as Lean namespaces. -/
def registerNamespaceParents (env : Lean.Environment) (name : Lean.Name) : Lean.Environment :=
  match name with
  | .anonymous => env
  | .str parent _ | .num parent _ =>
    (registerNamespaceParents env parent).registerNamespace name

/-- Store the updated `Core.Environment` and record `name` as a local declaration. -/
def publishDeclaration (env : Lean.Environment) (accepted : Core.Environment)
    (name : Lean.Name) : Lean.Environment :=
  moduleEnvironment.addEntry (registerNamespaceParents env name.getPrefix) (accepted, name)

end LeanPRA.Surface
