module

public meta import PRAProver.Surface.Delab

/-!
# Interactive PRA type displays

Encoding of PRA syntax and subterm types as Lean `Expr`s for the infoview:

- `displayType` encodes a syntax tree, its hover type text, and its child displays.
- `displayValue` attaches the hover type text to a displayed subterm.
- `makeTypeDisplay` builds an interactive display for a formula.
- `deferDisplay` saves display work until a native goal request needs it.
- `captureDisplay` saves the source context for later goal and hover rendering.
- `withDeferredDisplays` scopes the display store to one command and its generated declarations.

Lean's `@[app_delab]` handlers decode these `Expr`s to render goal types and subterm hover popups.
-/

public meta section

namespace PRAProver.Surface

open Lean Elab Command
open Core (Predicate)

/-- Carrier type for a plain-text goal or hover string. -/
@[expose] def goalType (_text : String) : Type := PUnit

/-- Carrier type for a JSON-encoded syntax shape, hover type string, and child displays. -/
@[expose] def displayType (_shape _typeText : String) (_children : List Type) : Type := PUnit

/-- Term wrapper whose type `goalType typeText` is shown when hovering over `_node`. -/
@[expose] def displayValue (_node : Type) (typeText : String) : goalType typeText := PUnit.unit

/-- Carrier for a display saved in the current information tree's environment. -/
@[expose] def deferredDisplay (_key : String) : Type := PUnit

private structure DisplayState where
  nextId : Nat := 0
  entries : PersistentHashMap String (Options → IO Expr) := {}
  deriving Inhabited

private initialize deferredDisplays : EnvExtension (Option (IO.Ref DisplayState)) ←
  registerEnvExtension (pure none) (asyncMode := .local)

/-- Scope display storage to a command, sharing it with nested generated declarations.
The command's information tree saves the store; compiled modules omit it. -/
def withDeferredDisplays (action : CommandElabM α) : CommandElabM α := do
  unless ← editorInfoEnabled do return ← action
  let saved := deferredDisplays.getState (← getEnv)
  if saved.isSome then return ← action
  let store ← IO.mkRef ({} : DisplayState)
  modifyEnv (deferredDisplays.setState · (some store))
  try
    withInfoTreeContext action fun children => do
      let state ← get
      let scope ← getScope
      return .context (.commandCtx {
        env := deferredDisplays.setState state.env (some store)
        fileMap := ← getFileMap
        currNamespace := scope.currNamespace
        openDecls := scope.openDecls
        options := scope.opts
        ngen := state.ngen })
        (.node (.ofCommandInfo { elaborator := `Delab, stx := .missing }) children)
  finally
    modifyEnv (deferredDisplays.setState · saved)

/-- Save immutable source scope for a renderer, with request-specific printing options.
Rendering runs in a fresh command state with information collection disabled. -/
def captureDisplay (action : CommandElabM α) : CommandElabM (Options → IO α) := do
  let env := deferredDisplays.setState (← getEnv) none
  let scope ← getScope
  let context : Command.Context := {
    fileName := (← read).fileName
    fileMap := ← getFileMap
    snap? := none
    cancelTk? := none }
  return fun opts => do
    let state := { Command.mkState env {} opts with
      scopes := [{ scope with opts }]
      infoState.enabled := false }
    match ← ((action.run context).run' state).toBaseIO with
    | .ok value => return value
    | .error error => throw (IO.userError (← error.toMessageData.toString))

/-- Build a display on its first request and reuse it while printing options stay unchanged.
Call this inside `withDeferredDisplays`. -/
def deferDisplay (action : CommandElabM Expr) : CommandElabM Expr := do
  let some store := deferredDisplays.getState (← getEnv)
    | throwError "PRA display storage is unavailable"
  let render ← captureDisplay action
  let cache ← IO.mkRef (none : Option (Options × Expr))
  -- The counter survives tactic backtracking, so saved displays always have distinct keys.
  let index ← store.modifyGet fun state => (state.nextId, { state with nextId := state.nextId + 1 })
  let key := toString index
  let render := fun opts => do
    if let some (previous, value) ← cache.get then
      if previous == opts then return value
    let value ← render opts
    cache.set (some (opts, value))
    return value
  store.modify fun state =>
    { state with entries := state.entries.insert key render }
  return mkApp (mkConst ``deferredDisplay) (mkStrLit key)

open PrettyPrinter.Delaborator SubExpr in
/-- Render a saved PRA display through Lean's ordinary delaborator and subterm annotations. -/
@[app_delab deferredDisplay] def delabDeferredDisplay : Delab := do
  let .lit (.strVal key) := (← getExpr).getArg! 0 | failure
  let some store := deferredDisplays.getState (← getEnv) | failure
  let some render := (← store.get).entries.find? key | failure
  let value ← render (← getOptions)
  withTheReader Lean.SubExpr (fun context => { context with expr := value }) delab

declare_syntax_cat praGoalDisplay
syntax (name := goalText) str : praGoalDisplay

/-- Format `goalText` as a raw atom. -/
@[formatter PRAProver.Surface.goalText] def formatGoalText : PrettyPrinter.Formatter :=
  PrettyPrinter.Formatter.visitAtom Name.anonymous

/-- Parenthesize `goalText` as a single token. -/
@[parenthesizer PRAProver.Surface.goalText]
def parenthesizeGoalText : PrettyPrinter.Parenthesizer :=
  PrettyPrinter.Parenthesizer.visitToken

open PrettyPrinter.Delaborator SubExpr in
/-- Delaborate `goalType text` as `text`. -/
@[app_delab goalType] def delabGoalType : Delab := do
  let e ← getExpr
  let .lit (.strVal text) := e.getArg! 0 | failure
  let stx : Term := ⟨Syntax.node .none ``goalText #[Syntax.atom .none text]⟩
  let pos ← getPos
  addDelabTermInfo pos stx e (explicit := false)
  return annotatePos pos stx

open PrettyPrinter.Delaborator SubExpr in
private partial def displayChild (index : Nat) : Delab :=
  withNaryArg 2 (go index)
where
  go : Nat → Delab
    | 0 => withNaryArg 1 delab
    | i + 1 => withNaryArg 2 (go i)

open PrettyPrinter.Delaborator in
private partial def decodeName : Json → Except String Name
  | .null => pure .anonymous
  | .arr #[parent, .str part] => return .str (← decodeName parent) part
  | .arr #[parent, .num part] => do
    let index ← fromJson? (α := Nat) (.num part)
    return .num (← decodeName parent) index
  | _ => throw "invalid display name"

private def encodeName : Name → Json
  | .anonymous => .null
  | .str parent part => .arr #[encodeName parent, toJson part]
  | .num parent index => .arr #[encodeName parent, toJson index]

open PrettyPrinter.Delaborator in
private partial def decodeShape (shape : Json) : DelabM Syntax := do
  if let .ok index := shape.getObjValAs? Nat "child" then
    return (← displayChild index).raw
  if let .ok atom := shape.getObjValAs? String "atom" then return .atom .none atom
  if let .ok value := shape.getObjVal? "ident" then
    let .ok name := decodeName value | failure
    return mkIdent name
  let .ok value := shape.getObjVal? "kind" | failure
  let .ok kind := decodeName value | failure
  let .ok args := shape.getObjValAs? (Array Json) "args" | failure
  return .node .none kind (← args.mapM decodeShape)

open PrettyPrinter.Delaborator SubExpr in
/-- Decode `displayType` into syntax and attach `displayValue` hover info. -/
@[app_delab displayType] def delabDisplayType : Delab := do
  let e ← getExpr
  let .lit (.strVal shape) := e.getArg! 0 | failure
  let .lit (.strVal typeText) := e.getArg! 1 | failure
  let .ok shape := Json.parse shape | failure
  let stx : Term := ⟨← decodeShape shape⟩
  let pos ← getPos
  addDelabTermInfo pos stx (mkApp2 (mkConst ``displayValue) e (mkStrLit typeText))
    (explicit := false)
  return annotatePos pos stx

open PrettyPrinter.Delaborator SubExpr in
/-- Delaborate `displayValue` by delaborating its wrapped display node. -/
@[app_delab displayValue] def delabDisplayValue : Delab := withNaryArg 0 delab

private def canonical (stx : Syntax) : Syntax :=
  stx.rewriteBottomUp fun
    | .ident _ _ n _ => mkIdent n.eraseMacroScopes
    | other => other.setInfo .none

private partial def encodeShape (stx : Syntax) (children : Array Syntax)
    (root := true) : Json := Id.run do
  if !root then
    if let some index := children.findIdx? (· == stx) then
      return Json.mkObj [("child", toJson index)]
  return match stx with
    | .atom _ text => Json.mkObj [("atom", toJson text)]
    | .ident _ _ name _ => Json.mkObj [("ident", encodeName name.eraseMacroScopes)]
    | .node _ kind args => Json.mkObj [("kind", encodeName kind),
        ("args", toJson (args.map (encodeShape · children false)))]
    | .missing => Json.mkObj [("atom", toJson "")]

private def DelabType.text : DelabType → CommandElabM String
  | .none => return "Type"
  | .term arity => return (← formatSyntax `praExpr (← delabArity arity)).pretty
  | .predicate sig => return (← formatSyntax `praExpr (← delabPredicateType sig)).pretty
  | .declaration d => return ← (← delabSignatureType d).toString

private partial def DelabTree.toExpr (tree : DelabTree) : CommandElabM Expr := do
  -- Parenthesize before replacing child subtrees with placeholders.
  let stx ← liftCoreM (PrettyPrinter.parenthesizeCategory `praExpr tree.stx)
  let displayedChildren ← tree.children.mapM fun child => do
    let stx ← liftCoreM (PrettyPrinter.parenthesizeCategory `praExpr child.stx)
    return { child with stx }
  let children ← displayedChildren.toList.mapM DelabTree.toExpr
  let children ← liftTermElabM (Meta.mkListLit (mkSort (.succ .zero)) children)
  let shape := encodeShape (canonical stx) (displayedChildren.map (canonical ·.stx))
  return mkApp3 (mkConst ``displayType) (mkStrLit shape.compress)
    (mkStrLit (← tree.type.text)) children

/-- Build an interactive display `Expr` for `type` after beta-reduction, using a well-formed
environment and local context. -/
def makeTypeDisplay (environment : Core.Environment) (context : Core.Context) (names : Names)
    (type : Predicate) : CommandElabM Expr := do
  let depth := pra.maxDepth.get (← getOptions)
  let names := { names with
    termAliases := names.termAliases.map fun (n, t) => (n, Core.betaReduceTerm depth t)
    predicateAliases := names.predicateAliases.map fun (n, p) => (n,
        Core.betaReducePredicate depth p) }
  (← delabPredicateTree names (Core.betaReducePredicate depth type)
    (some ⟨environment, context⟩)).toExpr

private partial def signatureTree (stx : TSyntax `praExpr) : DelabTree :=
  let children := match stx with
    | `(praExpr| $a:praExpr → $b:praExpr) => #[signatureTree a, signatureTree b]
    | _ => #[]
  ⟨stx, .none, children⟩

/-- Build an interactive display `Expr` for an arity or predicate signature. -/
def makeSignatureDisplay (stx : TSyntax `praExpr) : CommandElabM Expr :=
  (signatureTree stx).toExpr

end PRAProver.Surface
