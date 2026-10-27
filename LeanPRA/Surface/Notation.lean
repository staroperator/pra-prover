module

public meta import LeanPRA.Surface.Syntax
public meta import LeanPRA.Surface.NameResolution
public meta import Lean.Elab.Notation

/-!
# Custom PRA notation

Notation commands use Lean's precedence and notation-item syntax with a `praExpr` expansion.
Expansions are expressions without binders; declaration names in the expansion are resolved when
the notation is declared. Commands accept explicit precedences, `(name := ...)`, and
`(priority := ...)`. Notation items are string tokens and expression parameters with optional
precedences. Both `suffix` and `postfix` declare postfix operators.

For example, after defining `add`, `infixl:65 " + " => add` makes `a + b` elaborate as `add a b`.
Registered notations apply in the rest of the current block, in later blocks, and across imports.
Delaboration uses the most recent matching notation whose printed form still parses with that
notation's parser. Notations whose expansion omits a parameter are expanded during elaboration and
left unapplied during delaboration.

`syntax` and `macro` declarations outside PRA blocks can also extend `praExpr`, and can add entries
to `praNotations` to participate in expansion and delaboration.

- `PraNotation` stores a notation parser kind, parameter names, syntax parts, and expansion syntax.
- `praNotations` stores registered notation templates across the file and imported modules.
- `elaborateNotation` elaborates a notation command, registers its parser, and saves its template.
- `expandPraSyntax` expands registered notations and Lean macros before PRA elaboration.
- `unexpandPraSyntax` rewrites delaborated syntax using registered notations when round-trip
  parsing reproduces the notation node.
-/

public meta section
namespace LeanPRA.Surface
open Lean Elab Command

open Lean.Parser.Command in
syntax (name := praNotation) "notation" (":" prec)? (atomic(" (" &"name") " := " ident ")")?
  (atomic(" (" &"priority") " := " prio ")")? notationItem+ " => " praExpr : praDecl
open Lean.Parser.Command in
syntax (name := praMixfix) ("prefix" <|> "infix" <|> "infixl" <|> "infixr" <|>
  "suffix" <|> "postfix") ":" prec (atomic(" (" &"name") " := " ident ")")?
  (atomic(" (" &"priority") " := " prio ")")? str " => " praExpr : praDecl

/-- A registered notation template. `kind` is the `praExpr` parser kind. Each entry of `parts` is
a literal token or an index into `variables`. In `expansion`, parameters appear as `praExpr`
identifiers and resolved declarations appear with `_root_` prefixes. -/
structure PraNotation where
  kind : Name
  variables : Array Name
  parts : Array (String ⊕ Nat)
  expansion : Syntax
  deriving Inhabited

/-- Notation templates from imported modules and the current file, in declaration order. -/
initialize praNotations : SimpleScopedEnvExtension PraNotation (Array PraNotation) ←
  registerSimpleScopedEnvExtension { initial := #[], addEntry := Array.push }

private def notationArguments (rule : PraNotation) (stx : Syntax) : Array Syntax :=
  rule.parts.zipIdx.foldl (fun args (part, position) =>
    match part with
    | .inl _ => args
    | .inr index => args.set! index stx[position])
    (Array.replicate rule.variables.size .missing)

private def variable? (variables : Array Name) (stx : Syntax) : Option Nat :=
  let id := match stx with
    | `(praExpr| $id:ident) => id.raw
    | _ => stx
  if id.isIdent then variables.findIdx? (· == id.getId) else none

private partial def substitute (rule : PraNotation) (args : Array Syntax)
    (stx : Syntax) (ref : Syntax := .missing) (identifierRef : Syntax := .missing) : Syntax :=
  if let some i := variable? rule.variables stx then args[i]!
  else if let `(praExpr| ($_id:ident := $value:praExpr)) := stx then
    stx.setArg 3 (substitute rule args value ref identifierRef)
  else
    let info := if ref.isMissing then stx.getHeadInfo else SourceInfo.fromRef ref
    match stx with
    | .ident .. => stx.setInfo (if identifierRef.isMissing then info
        else SourceInfo.fromRef identifierRef (canonical := true))
    | .node _ kind children =>
      .node info kind (children.map (substitute rule args · ref identifierRef))
    | _ => stx.setInfo info

/-- Expand registered notation and `macro_rules` on raw PRA syntax, preserving argument locations.
Expansion is bounded by Lean's recursion limit. -/
partial def expandPraSyntax (stx : Syntax) : CommandElabM Syntax := withRef stx do
  withIncRecDepth do
    if stx.isOfKind choiceKind then
      let rules := praNotations.getState (← getEnv)
      let env ← getEnv
      let alternatives := stx.getArgs.filter fun alt =>
        rules.any (·.kind == alt.getKind) ||
          !(macroAttribute.getEntries env alt.getKind).isEmpty
      if alternatives.size == 1 then return ← expandPraSyntax alternatives[0]!
      throwErrorAt stx "ambiguous PRA syntax; use distinct notation tokens or priorities"
    if let some rule := (praNotations.getState (← getEnv)).find? (·.kind == stx.getKind) then
      let args := notationArguments rule stx
      let token := rule.parts.zipIdx |>.findSome? fun (part, i) =>
        match part with | .inl _ => some stx[i] | _ => none
      let expanded := substitute rule args rule.expansion stx (token.getD stx)
      return ← expandPraSyntax (expanded.setInfo (SourceInfo.fromRef stx (canonical := true)))
    if let some expanded ← liftMacroM (expandMacro? stx) then
      return ← expandPraSyntax expanded
    match stx with
    | .node info kind args => return .node info kind (← args.mapM expandPraSyntax)
    | _ => return stx

private partial def stripParens (stx : Syntax) : Syntax :=
  match stx with
  | `(praExpr| ($body:praExpr)) => stripParens body
  | _ => stx

private partial def matchExpansion (rule : PraNotation) (locals : List Name)
    (pattern actual : Syntax) (values : Array (Option Syntax)) :
    CommandElabM (Option (Array (Option Syntax))) := do
  let pattern := stripParens pattern
  let actual := stripParens actual
  if let some i := variable? rule.variables pattern then
    if let some previous := values[i]! then
      if previous.rewriteBottomUp (·.setInfo .none) ==
          actual.rewriteBottomUp (·.setInfo .none) then return some values else return none
    return some (values.set! i (some actual))
  if let `(praExpr| ($label:ident := $value:praExpr)) := pattern then
    let `(praExpr| ($actualLabel:ident := $actualValue:praExpr)) := actual | return none
    if label.getId != actualLabel.getId then return none
    return ← matchExpansion rule locals value actualValue values
  if pattern.isIdent && actual.isIdent then
    let name := actual.getId.eraseMacroScopes
    if locals.contains name then return none
    let expected := pattern.getId.replacePrefix `_root_ .anonymous
    if expected == `Nat || expected == `QFProp then
      return if name == expected then some values else none
    let resolved ← resolveDeclaration? (CoreEnvironment.getState (← getEnv)) name
    return if resolved.any (·.name == expected) then some values else none
  if let some nested := (praNotations.getState (← getEnv)).find?
      (·.kind == actual.getKind) then
    let args := notationArguments nested actual
    return ← matchExpansion rule locals pattern (substitute nested args nested.expansion) values
  match pattern, actual with
  | .atom _ p, .atom _ a => return if p == a then some values else none
  | .node _ pk ps, .node _ ak acts =>
    if pk != ak || ps.size != acts.size then return none
    let mut values := values
    for p in ps, a in acts do
      let some next ← matchExpansion rule locals p a values | return none
      values := next
    return some values
  | _, _ => return none

/-- Rewrite `stx` with the most recently declared matching notation in `praNotations`.
`locals` lists local names in scope so local variables are never matched as global declarations. -/
def unexpandPraSyntax (stx : Syntax) (locals : List Name := []) : CommandElabM Syntax := do
  let rules := praNotations.getState (← getEnv)
  for rule in rules.reverse do
    let some values ← matchExpansion rule locals rule.expansion stx
      (Array.replicate rule.variables.size none) | continue
    if values.any Option.isNone then continue
    let args := rule.parts.map fun
      | .inl text => Syntax.atom .none text.trimAscii.toString
      | .inr i => values[i]!.getD .missing
    let result := Syntax.node stx.getHeadInfo rule.kind args
    -- Check that pretty-printing and reparsing still produce this notation kind.
    let printed ← liftCoreM (PrettyPrinter.ppCategory `praExpr result)
    let .ok parsed := Parser.runParserCategory (← getEnv) `praExpr printed.pretty | continue
    let alternatives := if parsed.isOfKind choiceKind then parsed.getArgs else #[parsed]
    let applicable := alternatives.filter fun alt => rules.any (·.kind == alt.getKind)
    if applicable.size == 1 && applicable[0]!.getKind == rule.kind then return result
  return stx

private partial def prepareExpansion (variables : Array Name) (stx : Syntax) :
    CommandElabM Syntax := do
  match stx with
  | `(praExpr| fun $_xs:praFunBinder* => $_body:praExpr)
  | `(praExpr| fun $_xs:praFunBinder* : $_type:praExpr => $_body:praExpr)
  | `(praExpr| let ($_a:praBinder, $_bs:praBinder,*) := $_value:praExpr; $_body:praExpr)
  | `(praExpr| let $_id:ident := $_value:praExpr; $_body:praExpr)
  | `(praExpr| let $_id:ident : $_type:praExpr := $_value:praExpr; $_body:praExpr)
  | `(praExpr| ∀ $_xs:praBinder*, $_body:praExpr)
  | `(praExpr| ∀ $_xs:praBinder* : Nat, $_body:praExpr)
  | `(praExpr| ∀ {$_xs:praBinder*}, $_body:praExpr)
  | `(praExpr| ∀ {$_xs:praBinder* : Nat}, $_body:praExpr)
  | `(praExpr| ∃ $_xs:praBinder*, $_body:praExpr)
  | `(praExpr| ∃ $_xs:praBinder* : Nat, $_body:praExpr) =>
    throwErrorAt stx "PRA notation expansions currently require expressions without binders"
  | _ => pure ()
  if let `(praExpr| ($_label:ident := $value:praExpr)) := stx then
    return stx.setArg 3 (← prepareExpansion variables value)
  if let `(praExpr| @$id:ident) := stx then
    if variables.contains id.getId then
      throwErrorAt stx "write `@({id.getId})` for an explicit notation argument"
  if stx.isIdent then
    if (variable? variables stx).isSome then return stx
    if stx.getId == `Nat || stx.getId == `QFProp then return stx
    let some decl ← resolveDeclaration? (CoreEnvironment.getState (← getEnv)) stx.getId
      | throwErrorAt stx "unknown PRA declaration in notation: `{stx.getId}`"
    return mkIdentFrom stx (`_root_ ++ decl.name)
  match stx with
  | .node info kind args => return .node info kind (← args.mapM (prepareExpansion variables))
  | _ => return stx

/-- Elaborate a PRA `notation` or mixfix command, register its `praExpr` parser and tokens, and
record its template in `praNotations`. -/
def elaborateNotation (stx : Syntax) : CommandElabM Unit := do
  let (prec?, name?, prio?, items, rhs) ← match stx with
    | `(praDecl| notation $[:$prec?]? $[(name := $name?)]? $[(priority := $prio?)]?
        $items:notationItem* => $rhs:praExpr) => pure (prec?, name?, prio?, items, rhs)
    | stx =>
      unless stx.isOfKind ``praMixfix do throwUnsupportedSyntax
      let op := stx[0][0].getAtomVal
      let prec : TSyntax `prec := ⟨stx[2]⟩
      let name? : Option Ident := if stx[3].isNone then none else some ⟨stx[3][3]⟩
      let prio? : Option (TSyntax `prio) :=
        if stx[4].isNone then none else some ⟨stx[4][3]⟩
      let token : StrLit := ⟨stx[5]⟩
      let rhs : TSyntax `praExpr := ⟨stx[7]⟩
      let next : TSyntax `prec := ⟨Syntax.mkNumLit (toString ((← liftMacroM (evalPrec prec)) + 1))⟩
      let left ← `(Parser.Command.notationItem| lhs:$(if op == "infixl" then prec else next))
      let right ← `(Parser.Command.notationItem| rhs:$(if op == "infixr" then prec else next))
      let arg ← `(Parser.Command.notationItem| arg:$prec)
      let token ← `(Parser.Command.notationItem| $token:str)
      if op == "prefix" then
        pure (some prec, name?, prio?, #[token, arg], ← `(praExpr| $rhs arg))
      else if op == "suffix" || op == "postfix" then
        pure (some prec, name?, prio?, #[arg, token], ← `(praExpr| $rhs arg))
      else pure (some prec, name?, prio?, #[left, token, right], ← `(praExpr| $rhs lhs rhs))
  let mut variables : Array Name := #[]
  let mut parts : Array (String ⊕ Nat) := #[]
  let mut syntaxParts : Array (TSyntax `stx) := #[]
  for item in items do
    match item with
    | `(Parser.Command.notationItem| $id:ident $[:$prec?]?) =>
      if variables.contains id.getId then throwErrorAt id "duplicate notation parameter"
      parts := parts.push (.inr variables.size)
      variables := variables.push id.getId
      syntaxParts := syntaxParts.push (← `(stx| praExpr $[:$prec?]?))
    | `(Parser.Command.notationItem| $token:str) =>
      if token.getString.trimAscii.isEmpty then throwErrorAt token "empty notation token"
      parts := parts.push (.inl token.getString)
      syntaxParts := syntaxParts.push (← `(stx| $token:str))
    | _ => throwErrorAt item "expected a string or expression parameter in PRA notation"
  unless parts.any (fun p => p matches .inl _) do
    throwErrorAt stx "PRA notation requires at least one literal token"
  let expansion ← prepareExpansion variables (← expandPraSyntax rhs)
  let kind ← elabSyntax (← `(syntax $[:$prec?]? $[(name := $name?)]?
    $[(priority := $prio?)]? $[$syntaxParts]* : praExpr))
  for part in parts do
    if let .inl token := part then
      let token := token.trimAscii.toString
      unless token.toList.all isIdRest do
        liftCoreM (Parser.addToken token .global)
  praNotations.add { kind, variables, parts, expansion }

end LeanPRA.Surface
