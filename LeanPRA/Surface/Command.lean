module

public meta import LeanPRA.Surface.Elab

/-!
# PRA commands

`pra` opens a command scope where entries are parsed and elaborated one command at a time, so
notation declared in a block can be used in later entries of the same block. Lean's command
snapshots handle incremental reuse, diagnostics, and editor information for each entry.

- `elaborateBlock` opens a PRA scope, disables `autoImplicit`, and restricts command parsing to
  PRA entries until the matching `end`.
- `praEntry` parses a command in an active PRA scope using `praDecl`.
- `elaborateEntry` elaborates declarations, notation, inspection commands, and `open`,
  `namespace`, and `end` commands.
-/

public meta section
namespace LeanPRA.Surface
open Lean Elab Command Parser

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

private def inPraFn : ParserFn := fun ctx s =>
  if (praScopes.getState ctx.env).isEmpty then s.mkError "expected a PRA block" else s

private def inPra : Parser := { fn := inPraFn }

@[combinator_formatter inPra] private def formatInPra : PrettyPrinter.Formatter := pure ()
@[combinator_parenthesizer inPra] private def parenthesizeInPra :
    PrettyPrinter.Parenthesizer := pure ()

-- Parse each entry using the environment produced by the previous command.
@[command_parser 2000] def praEntry := leading_parser inPra >> categoryParser `praDecl 0

/-- Open a PRA block. The matching `end` restores the enclosing Lean scope. -/
@[command_elab praBlock] def elaborateBlock : CommandElab := fun _ => do
  unless (praScopes.getState (← getEnv)).isEmpty do throwError "nested PRA blocks are unsupported"
  elabCommand (← `(section))
  modifyScope fun scope => { scope with opts := autoImplicit.set scope.opts false }
  modifyEnv (praScopes.setState · [.anonymous])
  -- Use only PRA entry parsers until this scope closes, including after a parse error.
  modifyEnv fun env => parserExtension.modifyState env fun state =>
    match state.categories.find? `command with
    | none => state
    | some category =>
      let category := { category with tables := { leadingParsers := [(praEntry, 2000)] } }
      { state with categories := state.categories.insert `command category }

/-- Elaborate one PRA entry and publish declarations only after Core checking succeeds. -/
@[command_elab praEntry] def elaborateEntry : CommandElab := fun stx => do
  let entry := stx[0]
  try
    withRef entry do
      match entry with
      | `(praDecl| #check $e:praExpr) => elaborateCheck e
      | `(praDecl| #print $id:ident) => elaboratePrint id
      | `(praDecl| open $ids:ident*) =>
        for id in ids do registerImportedNamespace id
        elabCommand (← `(open $ids:ident*))
      | `(praDecl| namespace $id:ident) =>
        let name := id.getId
        let current ← getCurrNamespace
        let ns := if name.getRoot == `_root_ then name.replacePrefix `_root_ .anonymous
          else current ++ name
        modifyEnv (registerNamespaceParents · ns)
        elabCommand (← `(section))
        modifyScope fun scope => { scope with currNamespace := ns }
        activateScoped ns
        modifyEnv fun env => praScopes.setState env (name :: praScopes.getState env)
      | `(praDecl| end $[$closing:ident]?) =>
        let name :: rest := praScopes.getState (← getEnv) | throwError "no open PRA scope"
        if let some closing := closing then
          unless closing.getId == name do logErrorAt closing m!"expected `end {name}`"
        elabCommand (← `(end))
        modifyEnv (praScopes.setState · rest)
      | _ =>
        if entry.isOfKind ``praNotation || entry.isOfKind ``praMixfix then
          elaborateNotation entry
        else elaborateDeclaration entry
  catch ex =>
    if ex.isInterrupt then throw ex
    match entry with
    | `(praDecl| def $id:ident $_ps:praParam* : $_type:praExpr := $_body:praExpr)
    | `(praDecl| theorem $id:ident $_ps:praParam* : $_type:praExpr := $_body:praExpr) =>
      addUnresolvedInfo id
    | _ => pure ()
    logException ex

end LeanPRA.Surface
