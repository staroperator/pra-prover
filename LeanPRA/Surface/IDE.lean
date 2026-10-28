module

public meta import LeanPRA.Surface.Display

/-!
# PRA editor information

Hover, go-to-definition, and infoview integration for PRA syntax:

- `sourceLocation` converts a syntax span to a `DeclarationLocation`.
- `declarationLocations` records source locations for local and imported declarations.
- `addDeclarationInfo` attaches hover signature and go-to-definition info to a declaration
  reference.
- `addExpressionInfo` attaches an inferred hover type and optional binder location to an expression.
- `addProofTypeInfo` attaches hover info for a proof expression's resolved formula.
- `GoalTarget`, `GoalView`, `makeGoalInfo`, and `makeGoalsInfo` build native infoview snapshots.
- `GoalBinding` represents a local variable, parameter, hypothesis, or let-alias in a goal context.
- `addUnresolvedInfo` suppresses fallback navigation on unresolved identifiers.

Editor queries use the well-formed environments and contexts maintained by elaboration.
Incomplete expressions may fail inference; they do not extend the checked context.
-/

public meta section

namespace LeanPRA.Surface

open Lean Elab Command

/-- Expected or inferred type of a goal in the infoview. -/
inductive GoalTarget where
  | term (arity : Nat)
  | predicate (signature : Core.PredicateSignature)
  | proof (type : Core.Predicate)

/-- Whether a saved goal is open, waiting for inference, or part of a conflicting declaration. -/
inductive GoalStatus where
  | openGoal
  | blocked
  | conflicting

/-- Entry in a goal's local context, identified by its Core index or alias value. -/
inductive GoalBinding where
  | local (name : Name) (index : Nat)
  | functionParameter (name : Name) (index : Nat)
  | predicateParameter (name : Name) (index : Nat)
  | proof (name : Name) (index : Nat)
  | termAlias (name : Name) (value : Core.Term)
  | predicateAlias (name : Name) (value : Core.Predicate)

/-- Source name of a `GoalBinding`. -/
def GoalBinding.name : GoalBinding → Name
  | .local n _ | .functionParameter n _ | .predicateParameter n _
  | .proof n _ | .termAlias n _ | .predicateAlias n _ => n

private def GoalBinding.subject : GoalBinding → Core.CheckSubject
  | .local _ i => .term (.bvar i)
  | .functionParameter _ i => .term (.parameter i)
  | .predicateParameter _ i => .predicate (.parameter i)
  | .proof _ i => .proof (.hyp i)
  | .termAlias _ t => .term t
  | .predicateAlias _ p => .predicate p

private def renameBinding (names : Names) (binding : GoalBinding) (name : Name) : Names :=
  match binding with
  | .local _ i => { names with locals := names.locals.set i name }
  | .functionParameter _ i => { names with functions := names.functions.set i name }
  | .predicateParameter _ i => { names with predicates := names.predicates.set i name }
  | .proof _ i => { names with proofs := names.proofs.set i name }
  | _ => names

private def targetSyntax (names : Names) : GoalTarget → CommandElabM (TSyntax `praExpr)
  | .term arity => delabArity arity
  | .predicate signature => delabPredicateType signature
  | .proof type => delabPredicate names type

private def targetExpr (environment : Core.Environment) (context : Core.Context) (names : Names)
    (target : GoalTarget) : CommandElabM Expr := do
  match target with
  | .proof type => makeTypeDisplay environment context names type
  | _ => makeSignatureDisplay (← targetSyntax names target)

private def inferTarget (environment : Core.Environment) (context : Core.Context)
    (subject : Core.CheckSubject) : CommandElabM (Option GoalTarget) := do
  let depth := pra.maxDepth.get (← getOptions)
  return match subject with
    | .term t => (Core.inferTerm depth environment context t).toOption.map .term
    | .predicate p =>
      (Core.inferPredicate depth environment context p).toOption.map .predicate
    | .proof p => (Core.inferProof depth environment context p).toOption.map .proof

/-- The context and target of one PRA goal displayed by the infoview. -/
structure GoalView where
  environment : Core.Environment
  context : Core.Context
  names : Names
  bindings : List GoalBinding
  target : Option GoalTarget
  status : GoalStatus := .openGoal

private def goalContext (view : GoalView) : CommandElabM (LocalContext × Expr) := do
  let { environment, context, names, bindings, target, .. } := view
  let mut lctx : LocalContext := {}
  let mut locals := #[]
  for binding in bindings do
    if binding.name.isAnonymous then continue
    let some type ← inferTarget environment context binding.subject | continue
    let id ← liftCoreM mkFreshFVarId
    lctx := lctx.mkLocalDecl id binding.name (mkConst ``PUnit)
    locals := locals.push (binding, id, type)
  lctx := lctx.sanitizeNames.run' { options := ← getOptions }
  let mut names := { names with termAliases := [], predicateAliases := [] }
  for (binding, id, _) in locals do
    names := renameBinding names binding (lctx.get! id).userName
  for (binding, id, type) in locals do
    lctx := lctx.setType id (← targetExpr environment context names type)
    -- Register each alias after formatting its own type so later entries can use it.
    let name := (lctx.get! id).userName
    match binding with
    | .termAlias _ t => names := { names with termAliases := (name, t) :: names.termAliases }
    | .predicateAlias _ p =>
      names := { names with predicateAliases := (name, p) :: names.predicateAliases }
    | _ => pure ()
  let type ← match target with
    | some target => targetExpr environment context names target
    | none => pure (mkApp (mkConst ``goalType) (mkStrLit "type not yet known"))
  return (lctx, type)

/-- Build one native tactic snapshot containing an ordered list of PRA goals. -/
def makeGoalsInfo (stx : Syntax) (views : List GoalView) : CommandElabM Info := do
  let absent := Info.ofCommandInfo { elaborator := `Delab, stx := .missing }
  unless (← getInfoState).enabled do return absent
  unless (stx.getRange? (canonicalOnly := true)).isSome do return absent
  try
    let contexts ← views.mapM goalContext
    liftTermElabM do
      let mut goals := []
      for (view, (lctx, type)) in views.zip contexts do
        let userName := match view.status with
          | .openGoal => Name.anonymous
          | .blocked => `waitingForInference
          | .conflicting => `declarationHasConflict
        let goal ← Meta.withLCtx lctx #[] <| Meta.mkFreshExprMVar type (userName := userName)
        goals := goals ++ [goal.mvarId!]
      let mctx ← getMCtx
      return .ofTacticInfo {
        elaborator := `Delab
        stx
        mctxBefore := mctx
        mctxAfter := mctx
        goalsBefore := goals
        goalsAfter := goals }
  catch ex =>
    if ex.isInterrupt then throw ex
    return absent

/-- Build a `TacticInfo` goal snapshot for the infoview from `bindings` and `target`. -/
def makeGoalInfo (stx : Syntax) (environment : Core.Environment) (context : Core.Context)
    (names : Names) (bindings : List GoalBinding)
    (target : Option GoalTarget) (status : GoalStatus := .openGoal) : CommandElabM Info :=
  makeGoalsInfo stx [⟨environment, context, names, bindings, target, status⟩]

/-- Persistent environment extension mapping PRA declaration names to their `DeclarationLocation`s.
-/
initialize declarationLocations :
    Lean.SimplePersistentEnvExtension (Name × DeclarationLocation) (NameMap DeclarationLocation) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := fun locations (name, location) => locations.insert name location
    addImportedFn := fun modules => modules.foldl (init := {}) fun locations entries =>
      entries.foldl (fun locations (name, location) => locations.insert name location) locations
    -- Re-export locations from private imports so downstream modules can jump to them.
    exportEntriesFnEx? := some fun env locations _ =>
      .uniform (locations.toArray.filter fun (_, location) => !isPublicModule env location.module)
  }

/-- Convert `stx`'s canonical range in the current file to a `DeclarationLocation`. -/
def sourceLocation (stx : Syntax) : CommandElabM (Option DeclarationLocation) := do
  let some range := stx.getRange? (canonicalOnly := true) | return none
  return some { module := (← getEnv).mainModule
                range := .ofStringPositions (← getFileMap) range.start range.stop }

private def addInfo (stx : Syntax) (text? : Option String)
    (location? : Option DeclarationLocation) :
    CommandElabM Unit := do
  unless (← getInfoState).enabled do return
  unless (stx.getRange? (canonicalOnly := true)).isSome do return
  -- `Delab` prevents Lean from falling back to the command elaborator's definition.
  pushInfoLeaf (.ofDelabTermInfo {
    elaborator := `Delab
    stx
    lctx := {}
    expectedType? := none
    expr := mkSort .zero
    location?
    mkDocString? := text?.map fun text => fun _ => pure s!"```lean\n{text}\n```" })

/-- Record empty `DelabTermInfo` on `stx` so unresolved names do not jump to the elaborator. -/
def addUnresolvedInfo (stx : Syntax) : CommandElabM Unit :=
  addInfo stx none none

/-- Attach hover signature and go-to-definition location for declaration `d` to `stx`. -/
def addDeclarationInfo (stx : Syntax) (d : Core.Declaration) : CommandElabM Unit := do
  unless (← getInfoState).enabled do return
  try
    let text ← (← delabSignature d).toString
    let target := (declarationLocations.getState (← getEnv)).find? d.name
    addInfo stx text target
  catch ex =>
    if ex.isInterrupt then throw ex

/-- Attach hover info and optional binder location for a proof expression's resolved formula `type`.
-/
def addProofTypeInfo (stx : Syntax) (names : Names) (type : Core.Predicate)
    (target : Syntax := .missing) : CommandElabM Unit := do
  unless (← getInfoState).enabled do return
  let depth := pra.maxDepth.get (← getOptions)
  let type ← delabPredicate names (Core.betaReducePredicate depth type)
  let type := (← formatSyntax `praExpr type).pretty
  let id := if stx.isIdent then stx else stx[0]
  let text := if id.isIdent then s!"{id.getId.eraseMacroScopes} : {type}" else type
  addInfo stx text (← sourceLocation target)

/-- Infer the type of `subject` and attach hover and optional binder location info to `stx`. -/
def addExpressionInfo (stx : Syntax) (environment : Core.Environment) (context : Core.Context)
    (names : Names) (subject : Core.CheckSubject) (target : Syntax := .missing) :
    CommandElabM Unit := do
  unless (← getInfoState).enabled do return
  unless (stx.getRange? (canonicalOnly := true)).isSome do return
  try
    let depth := pra.maxDepth.get (← getOptions)
    let type ← match subject with
      | .term t =>
        let .ok arity := Core.inferTerm depth environment context t | return
        delabArity arity
      | .predicate p =>
        let .ok signature := Core.inferPredicate depth environment context p | return
        delabPredicateType signature
      | .proof p =>
        let .ok type := Core.inferProof depth environment context p | return
        delabPredicate names (Core.betaReducePredicate depth type)
    let type := (← formatSyntax `praExpr type).pretty
    let id := if stx.isIdent then stx else stx[0]
    let text := if id.isIdent then s!"{id.getId.eraseMacroScopes} : {type}" else type
    addInfo stx text (← sourceLocation target)
  catch ex =>
    if ex.isInterrupt then throw ex

end LeanPRA.Surface
