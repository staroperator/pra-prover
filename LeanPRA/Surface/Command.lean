module

public meta import LeanPRA.Surface.Elab

/-!
# The PRA block command

`elaborateBlock` elaborates `pra … end` entries in order, catching errors per entry so later
declarations still elaborate against the last accepted Core environment. Lean command snapshots
reuse an unchanged prefix after an editor update, including inside namespaces. Each completed entry
reports diagnostics and editor information before the remainder of the block finishes.

Enable `trace.pra.incremental` to inspect which entries are elaborated and reused.
-/

public meta section

namespace LeanPRA.Surface

open Lean Elab Command

private def registerImportedNamespace (id : Ident) : CommandElabM Unit := do
  let name := id.getId
  let mut ns ← getCurrNamespace
  let mut candidates := [name.replacePrefix `_root_ .anonymous]
  if name.getRoot != `_root_ then
    while !ns.isAnonymous do
      candidates := (ns ++ name) :: candidates
      ns := ns.getPrefix
    for opened in ← getOpenDecls do
      if let .simple openedNs _ := opened then candidates := (openedNs ++ name) :: candidates
  for candidate in candidates do
    if CoreEnvironment.hasNamespace (← getEnv) candidate then
      modifyEnv (registerNamespaceParents · candidate)

private structure EntryResult extends Language.Snapshot where
  state? : Option Command.State := none
  deriving Inhabited, TypeName

private instance : Language.ToSnapshotTree EntryResult where
  toSnapshotTreeM s := return ⟨← s.toSnapshot.transform, #[]⟩

private structure EntrySnapshot extends Language.Snapshot where
  result : Language.SnapshotTask EntryResult
  nested : Language.SnapshotTask Language.DynamicSnapshot
  deriving Inhabited, TypeName

private instance : Language.ToSnapshotTree EntrySnapshot where
  toSnapshotTreeM s :=
    return ⟨← s.toSnapshot.transform, #[← s.result.transform, ← s.nested.transform]⟩

private structure EntriesSnapshot extends Language.Snapshot where
  steps : Array (Language.SnapshotTask EntrySnapshot)
  suppressElabErrors : Bool
  deriving Inhabited, TypeName

private instance : Language.ToSnapshotTree EntriesSnapshot where
  toSnapshotTreeM s := return ⟨← s.toSnapshot.transform, ← s.steps.mapM (·.transform)⟩

initialize registerTraceClass `pra.incremental

private def traceEntry (action : String) (entry : TSyntax `praDecl) : CommandElabM Unit := do
  if (← getOptions).getBool `trace.pra.incremental then
    let label := match entry with
      | `(praDecl| def $id:ident $_ps:praParam* : $_type:praExpr := $_body:praExpr)
      | `(praDecl| theorem $id:ident $_ps:praParam* : $_type:praExpr := $_body:praExpr) =>
        id.getId.toString
      | `(praDecl| namespace $id:ident $_body:praDecl* end $[$_closing:ident]?) =>
        "namespace " ++ id.getId.toString
      | `(praDecl| open $_ids:ident*) => "open"
      | `(praDecl| #check $_e:praExpr) => "#check"
      | `(praDecl| #print $_id:ident) => "#print"
      | _ => "entry"
    dbg_trace "PRA {action} {label}"

/-- Give each entry its own context so completed entries can provide editor information early. -/
private def withEntryInfo (entry : Syntax) (action : CommandElabM Unit) : CommandElabM Unit :=
  withInfoTreeContext action fun trees => do
    let ctx ← read
    let s ← get
    let scope ← getScope
    return .context (.commandCtx {
      env := s.env, cmdEnv? := some s.env, fileMap := ctx.fileMap, mctx := {},
      currNamespace := scope.currNamespace, openDecls := scope.openDecls,
      options := scope.opts, ngen := s.ngen
    }) (.node (.ofCommandInfo {
      elaborator := `LeanPRA.Surface.elaborateBlock, stx := entry }) trees)

mutual

/-- Reuse only an unchanged prefix, including source positions and previously admitted entries. -/
private partial def elaborateEntries (entries : Array (TSyntax `praDecl)) : CommandElabM Unit := do
  let some bundle := (← read).snap? | do
    for entry in entries do
      traceEntry "elaborate" entry
      elaborateEntry entry
    return
  let suppressElabErrors := (← read).suppressElabErrors
  let old? := do
    let old ← bundle.old?
    let previous ← old.val.get.toTyped? EntriesSnapshot
    guard (previous.suppressElabErrors == suppressElabErrors)
    return previous
  if bundle.old?.isSome && old?.isNone then
    bundle.old?.forM (·.val.cancelRec)
  let promises ← entries.mapM fun _ => IO.Promise.new (α := EntrySnapshot)
  bundle.new.resolve <| .ofTyped {
    diagnostics := .empty
    suppressElabErrors
    steps := entries.zipWith (fun entry promise => {
      stx? := some entry.raw, task := promise.resultD default, cancelTk? := none
    }) promises : EntriesSnapshot
  }
  let opts ← getOptions
  let mut reuse := true
  for entry in entries, promise in promises, i in *...entries.size do
    let oldStep? := old?.bind (·.steps[i]?)
    let same := reuse && oldStep?.any fun old =>
      old.stx?.any (·.eqWithInfoAndTraceReuse opts entry.raw)
    let oldEntry? := if reuse then oldStep?.map (·.get) else none
    if same then
      if let some previous := oldEntry? then
        if let some state := previous.result.get.state? then
          traceEntry "reuse" entry
          set state
          promise.resolve previous
          continue
    let resultPromise ← IO.Promise.new (α := EntryResult)
    let nestedPromise ← IO.Promise.new (α := Language.DynamicSnapshot)
    let cancelTk ← IO.CancelToken.new
    let nested : Language.SnapshotTask Language.DynamicSnapshot := {
      stx? := some entry.raw, task := nestedPromise.resultD default, cancelTk? := none }
    let result : Language.SnapshotTask EntryResult := {
      stx? := some entry.raw, task := resultPromise.resultD default, cancelTk? := some cancelTk
      reportingRange := if entry.raw[0].isAtom && entry.raw[0].getAtomVal == "namespace" then .skip
        else Language.SnapshotTask.defaultReportingRange entry.raw }
    promise.resolve { diagnostics := .empty, result, nested }
    if let some previous := oldEntry? then
      previous.result.cancelRec
      unless entry.raw[0].getAtomVal == "namespace" do previous.nested.cancelRec
    else if let some old := oldStep? then old.cancelRec
    try
      traceEntry "elaborate" entry
      withReader (fun ctx => { ctx with cancelTk? := some cancelTk, snap? := some {
        new := nestedPromise
        old? := do
          let old ← oldStep?
          let previous ← oldEntry?
          return { stx := (← old.stx?), val := previous.nested }
      } }) (withEntryInfo entry (elaborateEntry entry))
      liftCoreM Core.checkInterrupted
      let s ← get
      let diagnostics ← Language.Snapshot.Diagnostics.ofMessageLog
        { s.messages with reported := {} }
      modify fun s => { s with messages := s.messages.markAllReported }
      let trees := (← getInfoState).trees
      resultPromise.resolve {
        diagnostics, state? := some (← get), infoTree? := trees[trees.size - 1]? }
    finally
      resultPromise.resolve default
      nestedPromise.resolve default
    reuse := false
  -- No deleted or invalidated suffix may keep running after reuse analysis finishes.
  if let some old := old? then
    for step in old.steps[entries.size:] do step.cancelRec

private partial def elaborateEntry (entry : TSyntax `praDecl) : CommandElabM Unit := do
  try
    withRef entry do
      match entry with
      | `(praDecl| #check $e:praExpr) => elaborateCheck e
      | `(praDecl| #print $id:ident) => elaboratePrint id
      | `(praDecl| open $ids:ident*) =>
        for id in ids do registerImportedNamespace id
        withoutCommandIncrementality true <| elabCommand (← `(open $ids:ident*))
      | `(praDecl| namespace $id:ident $body:praDecl* end $[$closing:ident]?) =>
        if let some closing := closing then
          unless closing.getId == id.getId do
            throwErrorAt closing "expected `end {id.getId}`"
        let current ← getCurrNamespace
        let ns := if id.getId.getRoot == `_root_ then
          id.getId.replacePrefix `_root_ .anonymous else current ++ id.getId
        modifyEnv (registerNamespaceParents · ns)
        let opts ← getOptions
        let oldHeaderMatches := (← read).snap?.bind (·.old?) |>.any fun old =>
          old.stx[0].eqWithInfoAndTraceReuse opts entry.raw[0] &&
          old.stx[1].eqWithInfoAndTraceReuse opts entry.raw[1]
        unless oldHeaderMatches do
          (← read).snap?.bind (·.old?) |>.forM (·.val.cancelRec)
        withReader (fun ctx => { ctx with snap? := ctx.snap?.map fun snap =>
          { snap with old? := snap.old?.filter fun _ => oldHeaderMatches } }) do
          withScope (fun scope => { scope with currNamespace := ns }) (elaborateEntries body)
      | _ => elaborateDeclaration entry
  catch ex =>
    -- A namespace rejected before visiting its body cannot use any old nested snapshots.
    (← read).snap?.bind (·.old?) |>.forM (·.val.cancelRec)
    if ex.isInterrupt then throw ex
    match entry with
    | `(praDecl| def $id:ident $_ps:praParam* : $_type:praExpr := $_body:praExpr)
    | `(praDecl| theorem $id:ident $_ps:praParam* : $_type:praExpr := $_body:praExpr) =>
      addUnresolvedInfo id
    | _ => pure ()
    logException ex

end

/-- Elaborate a `pra … end` block, reusing unchanged entries through Lean's command snapshots. -/
@[command_elab praBlock, incremental] def elaborateBlock : CommandElab
  | stx@`(pra $entries:praDecl* end) => do
    let opts ← getOptions
    let sameHeader := (← read).snap?.bind (·.old?) |>.any fun old =>
      old.stx[0].eqWithInfoAndTraceReuse opts stx[0]
    unless sameHeader do
      (← read).snap?.bind (·.old?) |>.forM (·.val.cancelRec)
    withReader (fun ctx => { ctx with snap? := ctx.snap?.map fun snap =>
      { snap with old? := snap.old?.filter fun _ => sameHeader } }) do
      -- The outer command's quotation context changes with its entire text. Use the stable header.
      withInitQuotContext (some (hash ("pra", stx[0].getPos?))) do
        withScope id (elaborateEntries entries)
  | _ => throwUnsupportedSyntax

end LeanPRA.Surface
