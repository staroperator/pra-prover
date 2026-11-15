module

public meta import LeanPRA.Surface.Notation

/-!
# Delaborating PRA documentation

- `Context` stores declaration signatures, binary notation, and hyperlink identities.
- `Context.withNotations` reads active infix notation and its parser precedences.
- `declaration` reconstructs readable signatures and definition bodies from Core syntax.
- `render` formats text while keeping each global reference's identity.

Fresh binder names prevent capture. Schema arguments follow their declaration's parameter order;
implicit arguments use named application. Theorem rendering reads only parameters and conclusions.
-/

meta section

namespace LeanPRA.DocGen.Pretty

open Lean Core Surface

/-- A binary notation's spelling and the operand precedences recorded by its Lean parser. -/
public structure InfixNotation where
  token : String
  precedence : Nat
  leftPrecedence : Nat
  rightPrecedence : Nat

private def declarationParameters : Core.Declaration → List Parameter
  | .function d => d.parameterSignature
  | .predicate d => d.parameters
  | .theoremE d => d.parameters

/-- Declaration signatures and reference identities needed to print a module's expressions. -/
public structure Context where
  parameters : NameMap (List Parameter) := {}
  indices : NameMap Nat := {}
  names : Array Name := #[]
  infixes : NameMap InfixNotation := {}

/-- Add a declaration's parameter signature and reference identity. -/
public def Context.add (context : Context) (d : Core.Declaration) : Context :=
  if context.indices.contains d.name then context
  else { context with
    parameters := context.parameters.insert d.name (declarationParameters d)
    indices := context.indices.insert d.name context.names.size
    names := context.names.push d.name }

private def operandPrecedences : ParserDescr → List Nat
  | .cat `praExpr prec => [prec]
  | .binary _ a b => operandPrecedences a ++ operandPrecedences b
  | .unary _ body => operandPrecedences body
  | _ => []

/-- Read active binary notation templates from the imported PRA registry. Only direct applications
of a declaration to two distinct operands are used. Parsing a sample checks that the notation still
selects its own parser; precedence and associativity come from that parser's description. -/
public unsafe def Context.withNotations (context : Context) (env : Lean.Environment) : Context :=
  Id.run do
    let rules := Surface.praNotations.getState env
    let mut context := context
    for rule in rules.reverse do
      let #[.inr 0, .inl token, .inr 1] := rule.parts | continue
      let `(praExpr| $head:ident $left:ident $right:ident) := rule.expansion | continue
      unless rule.variables == #[left.getId, right.getId] do continue
      let name := head.getId.replacePrefix `_root_ .anonymous
      if context.infixes.contains name then continue
      unless (context.parameters.find? name).any List.isEmpty do continue
      let .ok parsed := Parser.runParserCategory env `praExpr
        s!"docgenLeft {token.trimAscii} docgenRight" | continue
      let alternatives := if parsed.isOfKind choiceKind then parsed.getArgs else #[parsed]
      let applicable := alternatives.filter fun alt => rules.any (·.kind == alt.getKind)
      unless applicable.size == 1 && applicable[0]!.getKind == rule.kind do continue
      let .ok (.trailingNode _ prec lhs body) :=
        env.evalConstCheck ParserDescr {} ``TrailingParserDescr rule.kind | continue
      let [rhs] := operandPrecedences body | continue
      context := { context with
        infixes := context.infixes.insert name ⟨token.trimAscii.toString, prec, lhs, rhs⟩ }
    return context

/-- A piece of formatted text, with the exact global declaration it references when applicable. -/
public structure CodeSpan where
  text : String
  target : Option String := none
  deriving ToJson, FromJson

private partial def spans (context : Context) (text : Widget.TaggedText (Nat × Nat)) :
    Array CodeSpan :=
  match text with
  | .text s => #[⟨s, none⟩]
  | .append parts => parts.flatMap (spans context)
  | .tag (index, _) content =>
    #[⟨content.stripTags, context.names[index]?.map (·.toString)⟩]

private def boundedIndent (indent : Int) : Format → Format
  | .nest n body =>
    let next := max 0 (min 24 (indent + n))
    .nest (next - indent) (boundedIndent next body)
  | .append a b => .append (boundedIndent indent a) (boundedIndent indent b)
  | .group body behavior => .group (boundedIndent indent body) behavior
  | .tag index body => .tag index (boundedIndent indent body)
  | other => other

/-- Format at 96 columns with at most 24 columns of indentation, preserving reference identities. -/
public def render (context : Context) (text : Format) : Array CodeSpan :=
  spans context (Widget.TaggedText.prettyTagged (boundedIndent 0 text) (w := 96))

private structure Names where
  locals : List Name := []
  functions : List Name := []
  predicates : List Name := []
  used : List Name := []

private def fresh (names : Names) (hint : Name) : Name := Id.run do
  let base := if hint.isAnonymous || hint == `_ then `x else hint.eraseMacroScopes
  let reserved := [`Nat, `Prop, `QFProp, `True, `False, `S, `primrec, `fun, `let]
  if !(names.used ++ reserved).contains base then return base
  let index := ((List.range (names.used.length + reserved.length + 1)).find? fun i =>
    !(names.used ++ reserved).contains (base.appendAfter (toString i))).getD names.used.length
  return base.appendAfter (toString index)

private def localNames (names : Names) (n : Name) : Names :=
  { names with locals := n :: names.locals, used := n :: names.used }

private def indexed (names : List Name) (i : Nat) : Format :=
  (names[i]?.getD (.mkSimple s!"unbound{i}")).toString

private def reference (context : Context) (n : Name) (text : String) : Format :=
  match context.indices.find? n with
  | some index => .tag index text
  | none => text

private def global (context : Context) (names : Names) (n : Name) : Format :=
  reference context n (if names.used.contains n then `_root_ ++ n else n).toString

private def parens (body : Format) : Format :=
  Format.group ("(" ++ Format.nest 2 body ++ ")")

private def atPrec (outer inner : Nat) (body : Format) : Format :=
  if outer > inner then parens body else Format.group body

private def application (head : Format) (arguments : List Format) (prec : Nat) : Format :=
  if arguments.isEmpty then head
  else atPrec prec Parser.leadPrec (head ++ Format.nest 2
    (Format.line ++ Format.joinSep arguments Format.line))

private def typ (arity : Nat) (result : String := "Nat") : Format :=
  Format.group (Format.joinSep (List.replicate arity ("Nat" : Format) ++ [Format.text result])
    (" →" ++ Format.line))

private def sig (s : PredicateSignature) : Format :=
  typ s.arity (if s.sort == .qf then "QFProp" else "Prop")

private def binder (n : Name) (type : Format) (implicit : Bool := false) : Format :=
  (if implicit then "{" else "(") ++ n.toString ++ " : " ++ type ++
    (if implicit then "}" else ")")

private def actuals (context : Context) (name : Name) (fs ps : List Format) : List Format :=
  match context.parameters.find? name with
  | none => fs ++ ps
  | some parameters => Id.run do
    let mut fs := fs
    let mut ps := ps
    let mut result := []
    for parameter in parameters do
      let (hint, value) := match parameter with
        | .function hint _ => (hint, fs.headD "?")
        | .predicate hint _ => (hint, ps.headD "?")
      match parameter with
      | .function _ _ => fs := fs.drop 1
      | .predicate _ _ => ps := ps.drop 1
      let value := if hint.isImplicit then
        parens (hint.name.toString ++ " := " ++ value) else value
      result := result ++ [value]
    return result ++ fs ++ ps

private def numeral? : Core.Term → Option Nat
  | .zero => some 0
  | .app .succ n => (· + 1) <$> numeral? n
  | _ => none

private def termArguments : Core.Term → List Core.Term → Core.Term × List Core.Term
  | .app f a, args => termArguments f (a :: args)
  | f, args => (f, args)

private partial def term (context : Context) (names : Names) (t : Core.Term)
    (prec : Nat := 0) : Format :=
  if let some n := numeral? t then toString n else
  match t with
  | .bvar i => indexed names.locals i
  | .parameter i => indexed names.functions i
  | .zero => "0"
  | .succ => "S"
  | .lam hint body =>
    let n := fresh names hint
    atPrec prec 0 ("fun " ++ n.toString ++ " =>" ++
      Format.nest 2 (Format.line ++ term context (localNames names n) body))
  | .app f a =>
    let (head, args) := termArguments f [a]
    match head, args with
    | .definition n [], [left, right] =>
      if let some rule := context.infixes.find? n then
        atPrec prec rule.precedence (term context names left rule.leftPrecedence ++ " " ++
          reference context n rule.token ++ Format.nest 2
            (Format.line ++ term context names right rule.rightPrecedence))
      else application (term context names head Parser.leadPrec)
        (args.map (term context names · Parser.argPrec)) prec
    | _, _ => application (term context names head Parser.leadPrec)
        (args.map (term context names · Parser.argPrec)) prec
  | .letE hint value body =>
    let n := fresh names hint
    atPrec prec 0 ("let " ++ n.toString ++ " := " ++ term context names value ++ ";" ++
      Format.line ++ term context (localNames names n) body)
  | .primrec b s => application "primrec" ([b, s].map (term context names · Parser.argPrec)) prec
  | .definition n fs => application (global context names n)
      (actuals context n (fs.map (term context names · Parser.argPrec)) []) prec

private def predicateArguments : Predicate → List Core.Term → Predicate × List Core.Term
  | .app p a, args => predicateArguments p (a :: args)
  | p, args => (p, args)

private partial def predicate (context : Context) (names : Names) (p : Predicate)
    (prec : Nat := 0) : Format := Id.run do
  let pred := fun p level => predicate context names p level
  let tm := fun t level => term context names t level
  let binary (left : Predicate) (op : String) (right : Predicate) (level : Nat) :=
    atPrec prec level (pred left (level + 1) ++ " " ++ op ++
      Format.nest 2 (Format.line ++ pred right level))
  match p with
  | .false => return "False"
  | .true => return "True"
  | .equal a b => return atPrec prec 50 (tm a 51 ++ " = " ++ tm b 51)
  | .imp a .false => return atPrec prec 40 ("¬ " ++ pred a 40)
  | .imp a b => return binary a "→" b 25
  | .and a b => return binary a "∧" b 35
  | .or a b => return binary a "∨" b 30
  | .all p | .ex p =>
    let (hint, body) := match p with
      | .lam hint body => (hint, body)
      | other => (Core.BinderInfo.anonymous, Predicate.app other.shift (.bvar 0))
    let n := fresh names hint.name
    let symbol := if matchesAll then "∀ " else "∃ "
    let b := if hint.isImplicit && matchesAll then "{" ++ n.toString ++ " : Nat}"
      else n.toString ++ " : Nat"
    return atPrec prec 0 (symbol ++ b ++ "," ++
      Format.nest 2 (Format.line ++ predicate context (localNames names n) body))
  | .parameter i => return indexed names.predicates i
  | .lam hint body =>
    let n := fresh names hint.name
    return atPrec prec 0 ("fun " ++ n.toString ++ " =>" ++
      Format.nest 2 (Format.line ++ predicate context (localNames names n) body))
  | .app p a =>
    let (head, args) := predicateArguments p [a]
    if let .definition n [] [] := head then
      if let [left, right] := args then
        if let some rule := context.infixes.find? n then
          return atPrec prec rule.precedence (tm left rule.leftPrecedence ++ " " ++
            reference context n rule.token ++ Format.nest 2
              (Format.line ++ tm right rule.rightPrecedence))
    return application (pred head Parser.leadPrec) (args.map (tm · Parser.argPrec)) prec
  | .letTerm hint value body =>
    let n := fresh names hint
    return atPrec prec 0 ("let " ++ n.toString ++ " := " ++ tm value 0 ++ ";" ++
      Format.line ++ predicate context { names with used := n :: names.used } body)
  | .letPredicate hint value body =>
    let n := fresh names hint
    return atPrec prec 0 ("let " ++ n.toString ++ " := " ++ pred value 0 ++ ";" ++
      Format.line ++ predicate context { names with used := n :: names.used } body)
  | .definition n fs ps =>
    return application (global context names n)
      (actuals context n (fs.map (tm · Parser.argPrec)) (ps.map (pred · Parser.argPrec))) prec
where
  matchesAll := match p with | .all _ => true | _ => false

private def parameters (ps : List Parameter) : Names × Format := Id.run do
  let mut names : Names := {}
  let mut result := Format.nil
  for p in ps do
    let (hint, type) := match p with
      | .function b k => (b, typ k)
      | .predicate b s => (b, sig s)
    let n := fresh names hint.name
    match p with
    | .function _ _ => names := { names with functions := names.functions ++ [n] }
    | .predicate _ _ => names := { names with predicates := names.predicates ++ [n] }
    names := { names with used := n :: names.used }
    result := result ++ Format.line ++ binder n type hint.isImplicit
  return (names, result)

/-- Render a definition's signature and body or a theorem's statement.
Fresh binder names prevent capture; tags identify global references. -/
public def declaration (context : Context) (d : Core.Declaration) : Format × Option Format :=
  let (names, ps) := parameters (declarationParameters d)
  let start (keyword : String) := Format.group (keyword ++ " " ++ d.name.toString ++
    Format.nest 2 ps ++ " :")
  match d with
  | .function f =>
    (Format.group (start "def" ++ " " ++ typ f.arity), some (term context names f.body))
  | .predicate p =>
    (Format.group (start "def" ++ " " ++ sig p.signature), some (predicate context names p.body))
  | .theoremE t => (Format.group (start "theorem" ++
      Format.nest 2 (Format.line ++ predicate context names t.type)), none)

end LeanPRA.DocGen.Pretty
