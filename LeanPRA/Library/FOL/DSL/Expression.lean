module

public meta import LeanPRA.Library.FOL.DSL.Theory
public meta import LeanPRA.Library.Tactic.SigmaInduction

/-!
# FOL expressions in PRA declarations

FOL quotations expand to ordinary PRA expressions before elaboration. A splice supplies a
numerical syntax code in the surrounding context; entering a quantifier shifts its free positions.
Syntax parameters describe a result kind and an explicit argument arity. Their captured variables
are transported beneath new binders, and application fills the explicit slots in reverse numerical
order: the last argument occupies position zero. Definitions receive contextual codes as
numerical declaration parameters or ordinary numerical arguments.

The application form `(D a₁ … aₘ)` supplies the PRA parameters of a definition or a theorem.
Each argument is read by the declared kind of its parameter: a term or formula parameter takes
first-order syntax, and any other parameter takes a PRA expression.

- `termExpression` and `formulaExpression` expand notation to PRA syntax constructors.
- `applicationExpression` expands the application form of a theorem or of an ordinary PRA
  declaration; `headSignature` lists the parameters that the form supplies.
- `elaborateTheorem` checks proofs through the ordinary PRA elaborator.
- `expandQuotation` makes provability notation available inside ordinary PRA expressions.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL

open Lean Elab Command LeanPRA.Surface

def expressionCall (name : Name) (args : List (TSyntax `praExpr)) :
    CommandElabM (TSyntax `praExpr) := do
  let mut result ← `(praExpr| $(mkIdent (`_root_ ++ name)):ident)
  for arg in args do result ← `(praExpr| $result ($arg))
  return result

private def numberExpression (n : Nat) : CommandElabM (TSyntax `praExpr) :=
  `(praExpr| $(Syntax.mkNumLit (toString n)):num)

private def languageExpression (L : LanguageInfo) : CommandElabM (TSyntax `praExpr) :=
  expressionCall (L.name ++ `language) []

private def tupleExpression (xs : List (TSyntax `praExpr)) :
    CommandElabM (TSyntax `praExpr) := do
  match xs with
  | [] => numberExpression 0
  | [x] => pure x
  | x :: xs => expressionCall `pair [x, ← tupleExpression xs]

/-- Transport a syntax code beneath new binders while protecting its explicit slots. -/
private def shiftExpression (L : LanguageInfo) (depth : Nat) (value : TSyntax `praExpr)
    (formula : Bool := false) (arity : Nat := 0) : CommandElabM (TSyntax `praExpr) := do
  if depth == 0 then return value
  let language ← languageExpression L
  if !formula && arity == 0 then
    return ← expressionCall `FOL.Term.shift [language, ← numberExpression depth, value]
  let mut substitution ← expressionCall `FOL.shiftSubst [language, ← numberExpression depth]
  if arity > 0 then
    substitution ← expressionCall `FOL.liftSubst
      [substitution, language, ← numberExpression arity]
  expressionCall (if formula then `FOL.Formula.subst else `FOL.Term.subst)
    [substitution, language, value]

/-- Fill explicit slots in source order, with the last argument at index zero. -/
private def applySyntax (L : LanguageInfo) (formula : Bool) (value : TSyntax `praExpr)
    (arguments : List (TSyntax `praExpr)) (depth : Nat) : CommandElabM (TSyntax `praExpr) := do
  if arguments.isEmpty then return ← shiftExpression L depth value formula
  let language ← languageExpression L
  let mut substitution ← expressionCall `FOL.shiftSubst [language, ← numberExpression depth]
  for argument in arguments do
    substitution ← expressionCall `FOL.consSubst [argument, substitution]
  expressionCall (if formula then `FOL.Formula.subst else `FOL.Term.subst)
    [substitution, language, value]

/-- Read an argument written as a formula whose spelling is also a term: a name, a symbol or
definition application, a family member, a parenthesized term, a splice, or an application form.
The syntax tree is converted directly; no source text is parsed again. -/
partial def formulaAsTerm (s : TSyntax `folFormula) : CommandElabM (TSyntax `folTerm) :=
  withRef s do
  let stx := s.raw
  if stx.isOfKind ``formulaTerm || stx.isOfKind ``formulaTermWide then return ⟨stx[0]⟩
  if stx.isOfKind ``formulaSplice then return ⟨← `(folTerm| ${$(⟨stx[2]⟩):praExpr})⟩
  if stx.isOfKind ``formulaApplication then return ⟨stx.setKind ``termApplication⟩
  if stx.isOfKind ``formulaApplied then return ⟨stx.setKind ``termApplied⟩
  if stx.isOfKind ``formulaApplicationSlots then return ⟨stx.setKind ``termApplicationSlots⟩
  match s with
  | `(folFormula| ($a:folFormula)) => return ← `(folTerm| ($(← formulaAsTerm a)))
  | `(folFormula| $n:ident) => `(folTerm| $n:ident)
  | `(folFormula| $n:ident($args:folTerm,*)) => `(folTerm| $n:ident($args,*))
  | `(folFormula| $n:ident[$indices:praExpr,*]($args:folTerm,*)) =>
    `(folTerm| $n:ident[$indices,*]($args,*))
  | _ => throwErrorAt s "expected a term argument"

/-- The numeral at the leaf of a language's numeral notation, such as `0` in arithmetic. -/
private partial def numeralLeaf? (stx : Syntax) : Option (TSyntax `num) :=
  if stx.isOfKind numLitKind then some ⟨stx⟩
  else if stx.getNumArgs == 1 then numeralLeaf? stx[0] else none

/-- The readings of an argument: both when the first-order and the PRA grammar accept its text,
otherwise the one that does. -/
private def argumentReadings (arg : TSyntax `folArg) : Array Syntax :=
  if arg.raw.isOfKind choiceKind then arg.raw.getArgs else #[arg.raw]

/-- The reading of `arg` as a named argument `(x := a)`, when it has one. -/
def namedArgument? (arg : TSyntax `folArg) : Option (TSyntax `folArg) :=
  ((argumentReadings arg).find? (·.isOfKind ``namedArg)).map (⟨·⟩)

/-- Whether `arg` is the hole `_`. -/
def isHoleArgument (arg : TSyntax `folArg) : Bool :=
  (argumentReadings arg).any fun reading =>
    reading.isOfKind ``praArg && reading[0].isOfKind ``LeanPRA.Surface.praHole

/-- Select the reading of an argument by the kind of the parameter it fills: the first-order
reading for a term or formula parameter, the PRA reading otherwise. An argument that only the
other grammar accepts is kept, and the reader of the parameter's kind reports it. -/
private def selectReading (firstOrder : Bool) (arg : TSyntax `folArg) : TSyntax `folArg :=
  let readings := argumentReadings arg
  let wanted := readings.find? fun reading =>
    if firstOrder then reading.isOfKind ``formulaArg || reading.isOfKind ``lambdaArg
    else reading.isOfKind ``praArg
  ⟨(wanted.getD readings[0]!)⟩

mutual

/-- Read an argument of the application form as a PRA expression: its PRA reading when the PRA
grammar accepts it, otherwise a braced splice or a named argument. -/
partial def argumentAsPra (arg : TSyntax `folArg) : CommandElabM (TSyntax `praExpr) :=
  withRef arg do
  if let some reading := (argumentReadings arg).find? (·.isOfKind ``praArg) then
    return ⟨reading[0]⟩
  match (namedArgument? arg).getD (selectReading false arg) with
  | `(folArg| ($x:ident := $value:folArg)) =>
    `(praExpr| ($x:ident := $(← argumentAsPra value)))
  | `(folArg| $a:folFormula) => formulaAsPra a
  | _ => throwErrorAt arg "expected a PRA expression; write it as a braced splice"

partial def formulaAsPra (s : TSyntax `folFormula) : CommandElabM (TSyntax `praExpr) :=
  withRef s do
  let stx := s.raw
  if stx.isOfKind ``formulaSplice then return ⟨stx[2]⟩
  if stx.isOfKind ``formulaApplication then return ← applicationAsPra stx
  if let some n := numeralLeaf? stx then return ← `(praExpr| $n:num)
  if stx.isOfKind ``formulaTerm || stx.isOfKind ``formulaTermWide then
    return ← termAsPra ⟨stx[0]⟩
  match s with
  | `(folFormula| ($a:folFormula)) => return ← `(praExpr| ($(← formulaAsPra a)))
  | `(folFormula| $n:ident) => `(praExpr| $n:ident)
  | _ => throwErrorAt s "expected a PRA expression; write it as a braced splice"

partial def termAsPra (s : TSyntax `folTerm) : CommandElabM (TSyntax `praExpr) :=
  withRef s do
  let stx := s.raw
  if stx.isOfKind ``termSplice then return ⟨stx[2]⟩
  if stx.isOfKind ``termApplication then return ← applicationAsPra stx
  match s with
  | `(folTerm| ($t:folTerm)) => return ← `(praExpr| ($(← termAsPra t)))
  | `(folTerm| $n:ident) => `(praExpr| $n:ident)
  | _ => throwErrorAt s "expected a PRA expression; write it as a braced splice"

private partial def applicationAsPra (stx : Syntax) : CommandElabM (TSyntax `praExpr) := do
  let mut result ← `(praExpr| $(⟨stx[1]⟩):ident)
  for arg in stx[2].getArgs do result ← `(praExpr| $result $(← argumentAsPra ⟨arg⟩))
  return result

end

/-- Abstract the arguments still expected by a partially applied syntax value. -/
partial def completeApplication (body : Syntax) (expected : SyntaxParameter) (bound : List Name) :
    CommandElabM (Syntax × List Name) := do
  if expected.arity == 0 then return (body, bound)
  if let `(folFormula| ($inner:folFormula)) := body then
    return ← completeApplication inner expected bound
  if let `(folTerm| ($inner:folTerm)) := body then
    return ← completeApplication inner expected bound
  -- An application form without parentheses expands to the parenthesized form.
  if let some expanded ← Lean.Elab.liftMacroM (expandMacro? body) then
    return ← completeApplication expanded expected bound
  let names ← (List.range expected.arity).mapM fun _ => do
    let name ← liftCoreM (mkFreshUserName `_folSlot)
    pure (Name.mkSimple name.toString)
  let slots ← names.toArray.mapM fun name => `(folTerm| $(mkIdent name):ident)
  let slotList (existing : Array Syntax) :=
    Syntax.mkSep (existing ++ slots.map (·.raw)) (mkAtom ",")
  if body.isOfKind ``formulaApplicationSlots || body.isOfKind ``termApplicationSlots then
    return (body.setArg 5 (slotList body[5].getSepArgs), names.reverse ++ bound)
  if body.isOfKind ``formulaApplication || body.isOfKind ``termApplication then
    let kind := if expected.isFormula then ``formulaApplicationSlots else ``termApplicationSlots
    return (.node .none kind (body.getArgs ++ #[mkAtom "(", slotList #[], mkAtom ")"]),
      names.reverse ++ bound)
  let result ← if expected.isFormula then do
      let (name, arguments) ← match body with
        | `(folFormula| $name:ident) => pure (name, #[])
        | `(folFormula| $name:ident($args:folTerm,*)) => pure (name, args.getElems)
        | _ => throwErrorAt body "expected a predicate or a partial predicate application"
      let args := arguments ++ slots
      pure (← `(folFormula| $name:ident($args,*))).raw
    else do
      let (name, arguments) ← match body with
        | `(folTerm| $name:ident) => pure (name, #[])
        | `(folTerm| $name:ident($args:folTerm,*)) => pure (name, args.getElems)
        | _ => throwErrorAt body "expected a function or a partial function application"
      let args := arguments ++ slots
      pure (← `(folTerm| $name:ident($args,*))).raw
  return (result, names.reverse ++ bound)

/-- The parameters that the application form supplies for a head: the explicit parameters in
order, each with its first-order kind when it has one, and the implicit parameters that a named
argument may fill. The explicit result binders of a definition are left out, since the slot list
fills them. A head that is not a declaration takes PRA arguments only. -/
structure HeadSignature where
  /-- The resolved declaration, when the head names one. -/
  name : Option Name := none
  explicit : Array (Name × Option SyntaxKind) := #[]
  implicit : Array Name := #[]
  isDefinition : Bool := false

def headSignature (name : Name) : CommandElabM HeadSignature := do
  if let some d ← findDefinition name then
    let explicit := d.binders.filterMap fun binder =>
      if d.positional.contains binder || d.implicit.contains binder then none
      else some (binder, (d.syntaxParameters.find? (·.name == binder)).map (·.kind))
    return { name := d.name, explicit, implicit := d.implicit, isDefinition := true }
  let some (.theoremE declaration) ←
      resolveDeclaration? (CoreEnvironment.getState (← getEnv)) name | return {}
  let kinds := (((theoremParameters.getState (← getEnv)).find?
    (·.1 == declaration.name)).map (·.2)).getD #[]
  let binders := declaration.parameters.toArray.map fun (parameter : Core.Parameter) =>
    match parameter with
    | .function info _ | .predicate info _ => info
  -- The universal quantifiers at the front of the statement take PRA arguments as well.
  let mut quantified : Array (Name × Option SyntaxKind) := #[]
  let mut type := declaration.type
  while let .all (.lam name body) := type do
    quantified := quantified.push ((name : Name), none)
    type := body
  return {
    name := declaration.name
    explicit := (binders.filterMap fun info =>
      if info.isImplicit then none
      else some (info.name, (kinds.find? (·.name == info.name)).map (·.kind))) ++ quantified
    implicit := binders.filterMap fun info => if info.isImplicit then some info.name else none }

mutual

partial def termExpression (L : LanguageInfo) (bound : List Name) (s : Syntax)
    (parameters : Array SyntaxParameter := #[]) (ambient : Nat := 0) :
    CommandElabM (TSyntax `praExpr) := withRef s do
  let environment ← getEnv
  let parameters := if parameters.isEmpty then activeSyntaxParameters.getState environment
    else parameters
  if let some expanded ← Lean.Elab.liftMacroM (expandMacro? s) then
    return ← termExpression L bound expanded parameters ambient
  let language ← languageExpression L
  if s.isOfKind ``termSplice then return ← shiftExpression L bound.length ⟨s[2]⟩ false
  if s.isOfKind ``termApplication || s.isOfKind ``termApplicationSlots then
    let slots := if s.isOfKind ``termApplicationSlots then s[5].getSepArgs.map (⟨·⟩) else #[]
    return ← functionApplication L bound s[1].getId.eraseMacroScopes slots
      (s[2].getArgs.map (⟨·⟩)) parameters ambient
  let stx : TSyntax `folTerm := ⟨s⟩
  match stx with
  | `(folTerm| ($t:folTerm)) => termExpression L bound t parameters ambient
  | `(folTerm| $n:ident[$indices:praExpr,*]) => do
    let i ← withRef n <|
      familyIndex L.constantFamilies n.getId.eraseMacroScopes indices.getElems.size 0
    let symbol ← expressionCall `FOL.Language.constantFamilyMember
      [language, ← numberExpression i, ← tupleExpression indices.getElems.toList]
    expressionCall `FOL.Term.const [language, symbol]
  | `(folTerm| $n:ident[$indices:praExpr,*]($args:folTerm,*)) => do
    let index ← withRef n <|
      familyIndex L.functionFamilies n.getId.eraseMacroScopes indices.getElems.size
        args.getElems.size
    let language ← languageExpression L
    let symbol ← expressionCall `FOL.Language.functionFamilyMember
      [language, ← numberExpression index, ← tupleExpression indices.getElems.toList]
    let values ← args.getElems.toList.mapM
      (fun t => termExpression L bound t.raw parameters ambient)
    expressionCall `FOL.Term.app [language, symbol, ← tupleExpression values]
  | `(folTerm| $n:ident($args:folTerm,*)) =>
    functionApplication L bound n.getId.eraseMacroScopes args.getElems #[] parameters ambient
  | `(folTerm| $n:ident) =>
    if let some i := bound.idxOf? n.getId.eraseMacroScopes then
      return ← expressionCall `FOL.Term.var [language, ← numberExpression i]
    if let some p := parameters.find? (·.name == n.getId.eraseMacroScopes) then
      unless !p.isFormula && p.arity == 0 do throwError "expected a term of arity zero"
      return ← shiftExpression L (bound.length + ambient) (← `(praExpr| $n:ident))
    if let some i := L.constants.toList.idxOf? n.getId.eraseMacroScopes then
      return ← expressionCall `FOL.Term.const [language, ← numberExpression i]
    if let some d ← findDefinition n.getId.eraseMacroScopes then
      return ← definitionApplication L bound d #[] #[] false parameters ambient
    if (activeDataParameters.getState (← getEnv)).contains n.getId.eraseMacroScopes then
      throwErrorAt n "ordinary PRA data requires an explicit braced code injection"
    shiftExpression L bound.length (← `(praExpr| $n:ident))
  | _ => throwError "unsupported FOL term"

private partial def functionApplication (L : LanguageInfo) (bound : List Name) (name : Name)
    (args : Array (TSyntax `folTerm)) (actuals : Array (TSyntax `folArg))
    (parameters : Array SyntaxParameter) (ambient : Nat) :
    CommandElabM (TSyntax `praExpr) := do
  if let some p := parameters.find? (·.name == name) then
    unless actuals.isEmpty do
      throwError "term parameter `{name}` takes its arguments in parentheses"
    unless !p.isFormula && p.arity == args.size do
      throwError "term parameter `{name}` expects {p.arity} arguments"
    let values ← args.toList.mapM (fun t => termExpression L bound t.raw parameters ambient)
    return ← applySyntax L false (← `(praExpr| $(mkIdent name):ident)) values
      (bound.length + ambient)
  if args.isEmpty && actuals.isEmpty then
    if let some i := L.constants.toList.idxOf? name then
      return ← expressionCall `FOL.Term.const [← languageExpression L, ← numberExpression i]
  if let some d ← findDefinition name then
    return ← definitionApplication L bound d args actuals false parameters ambient
  unless actuals.isEmpty do throwError "a language symbol has no PRA parameters"
  let index ← functionIndex L name args.size
  let values ← args.toList.mapM (fun t => termExpression L bound t.raw parameters ambient)
  expressionCall `FOL.Term.app
    [← languageExpression L, ← numberExpression index, ← tupleExpression values]

/-- Read the arguments of the application form against the explicit parameters of `head`. The
values of the explicit parameters are returned in order, with the named arguments for implicit
parameters after them. -/
private partial def applicationArguments (L : LanguageInfo) (bound : List Name) (head : Name)
    (signature : HeadSignature) (actuals : Array (TSyntax `folArg))
    (parameters : Array SyntaxParameter) (ambient : Nat) :
    CommandElabM (Array (TSyntax `praExpr) × Array (Name × TSyntax `praExpr)) := do
  let mut values := #[]
  let mut named := #[]
  for actual in actuals do
    if let some namedActual := namedArgument? actual then
      let `(folArg| ($x:ident := $value:folArg)) := namedActual | throwUnsupportedSyntax
      let name := x.getId.eraseMacroScopes
      if signature.name.isSome then
        unless signature.implicit.contains name do
          throwErrorAt x "`{name}` is not an implicit parameter of `{head}`"
      if named.any (·.1 == name) then throwErrorAt x "duplicate argument for `{name}`"
      named := named.push (name, ← argumentAsPra value)
      continue
    let expected ← if signature.name.isNone then pure none else
      match signature.explicit[values.size]? with
      | some expected => pure (some expected)
      | none => throwErrorAt actual "`{head}` takes {signature.explicit.size} explicit arguments"
    let value ← match expected with
      | some (name, some kind) =>
        if kind == .nat then argumentAsPra actual
        else syntaxActual L bound parameters ⟨name, kind⟩ (selectReading true actual) ambient
      | _ => argumentAsPra actual
    values := values.push value
  if signature.isDefinition && values.size < signature.explicit.size then
    throwError "missing argument `{(signature.explicit[values.size]!).1}` of `{head}`"
  return (values, named)

private partial def definitionApplication (L : LanguageInfo) (bound : List Name)
    (d : DefinitionInfo) (args : Array (TSyntax `folTerm))
    (actuals : Array (TSyntax `folArg)) (formula : Bool)
    (parameters : Array SyntaxParameter) (ambient : Nat := 0) :
    CommandElabM (TSyntax `praExpr) := do
  unless d.language == L.name do throwError "FOL definition `{d.name}` uses another language"
  unless d.isFormula == formula do throwError "FOL definition `{d.name}` has the wrong result kind"
  let arity := d.positional.size + d.resultArity
  unless args.size == arity do
    throwError "FOL definition `{d.name}` expects {arity} term arguments"
  let (values, named) ← applicationArguments L bound d.name (← headSignature d.name) actuals
    parameters ambient
  let positional := d.positional.toList.zip args.toList
  let mut result ← `(praExpr| $(mkIdent (`_root_ ++ d.name)):ident)
  let mut next := 0
  for binder in d.binders do
    if let some term := positional.lookup binder then
      result ← `(praExpr| $result ($(← termExpression L bound term.raw parameters ambient)))
    else if d.implicit.contains binder then
      if let some (_, value) := named.find? (·.1 == binder) then
        result ← `(praExpr| $result ($(mkIdent binder):ident := $value))
    else
      result ← `(praExpr| $result ($(values[next]!)))
      next := next + 1
  if d.resultArity > 0 then
    let slots := args.toList.drop d.positional.size
    -- A closed value whose raw slots are filled with the slot variables themselves, in order,
    -- is the code itself; this is how a partially applied value reaches a parameter.
    let slotName? (t : Syntax) : Option Name :=
      if t.isIdent then some t.getId.eraseMacroScopes
      else if t.getNumArgs == 1 && t[0].isIdent then some t[0].getId.eraseMacroScopes
      else none
    if d.syntaxParameters.isEmpty && slots.zipIdx.all (fun (t, i) =>
        (slotName? t.raw).any fun x => bound.idxOf? x == some (d.resultArity - 1 - i)) then
      return result
    let terms ← slots.mapM fun t => termExpression L bound t.raw parameters ambient
    return ← applySyntax L formula result terms 0
  return result

/-- Elaborate a term or formula argument in the context where it is supplied. -/
private partial def syntaxActual (L : LanguageInfo) (bound : List Name)
    (parameters : Array SyntaxParameter) (expected : SyntaxParameter)
    (actual : TSyntax `folArg) (ambient : Nat := 0) :
    CommandElabM (TSyntax `praExpr) := do
  match actual with
  | `(folArg| (fun $xs:ident* => $body:folFormula)) =>
    unless xs.size == expected.arity do
      throwErrorAt actual "expected {expected.arity} explicit binders"
    let scope := xs.toList.reverse.map (·.getId.eraseMacroScopes) ++ bound
    if expected.isFormula then return ← formulaExpression L scope body parameters ambient
    termExpression L scope (← formulaAsTerm body) parameters ambient
  | `(folArg| $body:folFormula) =>
    if body.raw.isOfKind ``formulaSplice then
      return ← shiftExpression L (bound.length + ambient) ⟨body.raw[2]⟩ expected.isFormula
        expected.arity
    let body ← if expected.isFormula then pure body.raw else pure (← formulaAsTerm body).raw
    let (body, scope) ← completeApplication body expected bound
    if expected.isFormula then formulaExpression L scope body parameters ambient
    else termExpression L scope body parameters ambient
  | _ =>
    if isHoleArgument actual then return ← `(praExpr| _)
    throwErrorAt actual "expected a {if expected.isFormula then "formula" else "term"} argument; \
      a PRA expression holding a code is written as a braced splice"

partial def formulaExpression (L : LanguageInfo) (bound : List Name) (s : Syntax)
    (parameters : Array SyntaxParameter := #[]) (ambient : Nat := 0) :
    CommandElabM (TSyntax `praExpr) := withRef s do
  let environment ← getEnv
  let parameters := if parameters.isEmpty then activeSyntaxParameters.getState environment
    else parameters
  if let some expanded ← Lean.Elab.liftMacroM (expandMacro? s) then
    return ← formulaExpression L bound expanded parameters ambient
  if let `(folFormula| ${$p:praExpr}[$args:folTerm,*]) := s then
    let values ← args.getElems.toList.mapM
      (fun t => termExpression L bound t.raw parameters ambient)
    return ← applySyntax L true p values (bound.length + ambient)
  if s.isOfKind ``formulaSplice then return ← shiftExpression L bound.length ⟨s[2]⟩ true
  if s.isOfKind ``formulaApplication || s.isOfKind ``formulaApplicationSlots then
    let slots := if s.isOfKind ``formulaApplicationSlots then s[5].getSepArgs.map (⟨·⟩)
      else #[]
    return ← relationApplication L bound s[1].getId.eraseMacroScopes slots
      (s[2].getArgs.map (⟨·⟩)) parameters ambient
  let stx : TSyntax `folFormula := ⟨s⟩
  match stx with
  | `(folFormula| ($a:folFormula)) => formulaExpression L bound a parameters ambient
  | `(folFormula| ⊥) => expressionCall `FOL.Formula.falsum []
  | `(folFormula| $a:folTerm = $b:folTerm) =>
    expressionCall `FOL.Formula.equal
      [← languageExpression L, ← termExpression L bound a parameters ambient,
        ← termExpression L bound b parameters ambient]
  | `(folFormula| $a:folTerm ≠ $b:folTerm) => do
    let eq ← expressionCall `FOL.Formula.equal
      [← languageExpression L, ← termExpression L bound a parameters ambient,
        ← termExpression L bound b parameters ambient]
    expressionCall `FOL.Formula.neg [eq]
  | `(folFormula| ¬ $a:folFormula) =>
    expressionCall `FOL.Formula.neg [← formulaExpression L bound a parameters ambient]
  | `(folFormula| $a:folFormula → $b:folFormula) =>
    expressionCall `FOL.Formula.imp
      [← formulaExpression L bound a parameters ambient,
        ← formulaExpression L bound b parameters ambient]
  | `(folFormula| $a:folFormula ∧ $b:folFormula) =>
    expressionCall `FOL.Formula.conj
      [← formulaExpression L bound a parameters ambient,
        ← formulaExpression L bound b parameters ambient]
  | `(folFormula| $a:folFormula ∨ $b:folFormula) =>
    expressionCall `FOL.Formula.disj
      [← formulaExpression L bound a parameters ambient,
        ← formulaExpression L bound b parameters ambient]
  | `(folFormula| $a:folFormula ↔ $b:folFormula) =>
    let a ← formulaExpression L bound a parameters ambient
    let b ← formulaExpression L bound b parameters ambient
    expressionCall `FOL.Formula.conj
      [← expressionCall `FOL.Formula.imp [a, b], ← expressionCall `FOL.Formula.imp [b, a]]
  | `(folFormula| ∀ $xs:ident* , $a:folFormula)
  | `(folFormula| ∃ $xs:ident* , $a:folFormula) =>
    let variables := xs.toList.reverse.map (·.getId.eraseMacroScopes) ++ bound
    let mut body ← formulaExpression L variables a parameters ambient
    let constructorName := if s[0].getAtomVal.trimAscii.toString == "∃" then
      `FOL.Formula.ex else `FOL.Formula.all
    for _ in xs do body ← expressionCall constructorName [body]
    return body
  | `(folFormula| $n:ident[$indices:praExpr,*]($args:folTerm,*)) => do
    let index ← withRef n <|
      familyIndex L.relationFamilies n.getId.eraseMacroScopes indices.getElems.size
        args.getElems.size
    let language ← languageExpression L
    let symbol ← expressionCall `FOL.Language.relationFamilyMember
      [language, ← numberExpression index, ← tupleExpression indices.getElems.toList]
    let values ← args.getElems.toList.mapM
      (fun t => termExpression L bound t.raw parameters ambient)
    expressionCall `FOL.Formula.rel [language, symbol, ← tupleExpression values]
  | `(folFormula| $n:ident($args:folTerm,*)) =>
    relationApplication L bound n.getId.eraseMacroScopes args.getElems #[] parameters ambient
  | `(folFormula| $n:ident) =>
    relationApplication L bound n.getId.eraseMacroScopes #[] #[] parameters ambient
  | _ => throwError "unsupported FOL formula"

private partial def relationApplication (L : LanguageInfo) (bound : List Name) (name : Name)
    (args : Array (TSyntax `folTerm)) (actuals : Array (TSyntax `folArg))
    (parameters : Array SyntaxParameter) (ambient : Nat) :
    CommandElabM (TSyntax `praExpr) := do
  if let some p := parameters.find? (·.name == name) then
    unless actuals.isEmpty do
      throwError "formula parameter `{name}` takes its arguments in parentheses"
    unless p.isFormula && p.arity == args.size do
      throwError "formula parameter `{name}` expects {p.arity} arguments"
    let values ← args.toList.mapM (fun t => termExpression L bound t.raw parameters ambient)
    return ← applySyntax L true (← `(praExpr| $(mkIdent name):ident)) values
      (bound.length + ambient)
  if let some d ← findDefinition name then
    return ← definitionApplication L bound d args actuals true parameters ambient
  unless actuals.isEmpty do throwError "a language symbol has no PRA parameters"
  let some index := L.relations.toList.findIdx? (fun (n, k) => n == name && k == args.size) |
    throwError "unknown relation or formula definition `{name}`"
  expressionCall `FOL.Formula.rel [← languageExpression L, ← numberExpression index,
    ← tupleExpression
      (← args.toList.mapM (fun t => termExpression L bound t.raw parameters ambient))]

/-- Expand the application form `(head a₁ … aₘ)` of a theorem, a local PRA proof, or another
PRA declaration to a PRA application. The arguments are read by the kinds of the parameters of
`head`; a head without a declaration takes PRA arguments. For a theorem, the arguments after
its parameters are returned separately: they are proofs of its PRA antecedents. -/
partial def applicationHead (L : LanguageInfo) (bound : List Name) (head : Ident)
    (actuals : Array (TSyntax `folArg)) (parameters : Array SyntaxParameter := #[])
    (ambient : Nat := 0) :
    CommandElabM (TSyntax `praExpr × Array (TSyntax `folArg)) := withRef head do
  let environment ← getEnv
  let parameters := if parameters.isEmpty then activeSyntaxParameters.getState environment
    else parameters
  let name := head.getId.eraseMacroScopes
  let signature ← headSignature name
  if signature.isDefinition then
    throwError "`{name}` is a first-order definition; its application is a term or a formula"
  let (actuals, antecedents) := if signature.name.isNone then (actuals, #[]) else
    let positional := actuals.filter fun actual => (namedArgument? actual).isNone
    let extra := positional.size - signature.explicit.size
    (actuals.extract 0 (actuals.size - extra), actuals.extract (actuals.size - extra) actuals.size)
  let (values, named) ← applicationArguments L bound name signature actuals parameters ambient
  let mut result ← match signature.name with
    | some resolved => `(praExpr| $(mkIdent (`_root_ ++ resolved)):ident)
    | none => `(praExpr| $head:ident)
  for value in values do result ← `(praExpr| $result ($value))
  for (x, value) in named do result ← `(praExpr| $result ($(mkIdent x):ident := $value))
  return (result, antecedents)

/-- The application form as one PRA expression, applying a theorem to the proofs of its PRA
antecedents as well. -/
partial def applicationExpression (L : LanguageInfo) (bound : List Name) (head : Ident)
    (actuals : Array (TSyntax `folArg)) (parameters : Array SyntaxParameter := #[])
    (ambient : Nat := 0) : CommandElabM (TSyntax `praExpr) := do
  let (result, antecedents) ← applicationHead L bound head actuals parameters ambient
  let mut result := result
  for antecedent in antecedents do result ← `(praExpr| $result ($(← argumentAsPra antecedent)))
  return result

end

@[pra_expander provableQuote, pra_expander openProvableQuote,
  pra_expander termQuote, pra_expander formulaQuote]
def expandQuotation : ExpressionExpander := fun stx => do
  match stx with
  | `(praExpr| fol_term [ $L:ident | $t:folTerm ]) =>
    termExpression (← findLanguage L.getId.eraseMacroScopes) [] t
  | `(praExpr| fol_formula [ $L:ident | $a:folFormula ]) =>
    formulaExpression (← findLanguage L.getId.eraseMacroScopes) [] a
  | _ =>
    let (name, formula, free) ← match stx with
      | `(praExpr| $T:ident ⊢ $a:folFormula) => pure (T.getId.eraseMacroScopes, a, #[])
      | `(praExpr| $T:ident ⊢ free $xs:ident* | $a:folFormula) =>
        pure (T.getId.eraseMacroScopes, a, xs)
      | _ => throwUnsupportedSyntax
    let T ← findTheory name
    let mut body ← formulaExpression T.language [] formula
    for (x, i) in free.toList.zipIdx do
      let value ← expressionCall `FOL.Term.var
        [← languageExpression T.language, ← numberExpression i]
      body ← `(praExpr| let $x:ident := $value; $body)
    expressionCall `FOL.Provable
      [← languageExpression T.language, ← expressionCall (T.name ++ `isAxiom) [], body]

@[command_elab LeanPRA.Surface.praEntry]
def elaborateTheorem : CommandElab := fun stx => do
  let (doc, entry) ← match stx[0] with
    | `(praDecl| $doc:docComment $decl:praDecl) => pure (some doc, decl.raw)
    | entry => pure (none, entry)
  let (name, ps, T, a, free, body) ← match entry with
    | `(praDecl| fol_theorem $name:ident $ps:praParam* :
        $T:ident ⊢ $a:folFormula := $body:praExpr) =>
      pure (name, ps, T, a, #[], body)
    | `(praDecl| fol_theorem $name:ident $ps:praParam* :
        $T:ident ⊢ free $xs:ident* | $a:folFormula := $body:praExpr) =>
      pure (name, ps, T, a, xs, body)
    | _ => throwUnsupportedSyntax
  let (binders, parameters) ← declarationParameters ps
  let theory ← findTheory T.getId.eraseMacroScopes
  let language ← languageExpression theory.language
  let previousData := activeDataParameters.getState (← getEnv)
  let ordinary := (dataParameterNames ps).filter fun n =>
    !(free.any (·.getId.eraseMacroScopes == n))
  modifyEnv (activeDataParameters.setState · ordinary)
  let mut code ← try formulaExpression theory.language [] a parameters
    catch error =>
      modifyEnv (activeDataParameters.setState · previousData)
      throw error
  let mut body := body
  for (x, i) in free.toList.zipIdx do
    let value ← expressionCall `FOL.Term.var [language, ← numberExpression i]
    code ← `(praExpr| let $x:ident := $value; $code)
    body ← `(praExpr| let $x:ident := let _folBoundVariable := $value; _folBoundVariable; $body)
  let type ← expressionCall `FOL.Provable
    [language, ← expressionCall (theory.name ++ `isAxiom) [], code]
  -- The statement takes the source range of the formula, so editor information about its
  -- arguments is placed at the formula instead of spanning the whole declaration.
  let type : TSyntax `praExpr := match a.raw.getPos?, a.raw.getTailPos? with
    | some start, some stop =>
      ⟨type.raw.setInfo (.original "".toRawSubstring start "".toRawSubstring stop)⟩
    | _, _ => type
  let declaration ← `(praDecl| theorem $name:ident $binders:praParam* : $type := $body)
  let declaration ← if let some doc := doc then
      `(praDecl| $doc:docComment $declaration:praDecl)
    else pure declaration
  let previous := activeSyntaxParameters.getState (← getEnv)
  let previousContext := activeSyntaxContext.getState (← getEnv)
  modifyEnv (activeSyntaxContext.setState · free.size)
  modifyEnv (activeSyntaxParameters.setState · parameters)
  try elaborateDeclaration declaration
  finally
    modifyEnv (activeSyntaxParameters.setState · previous)
    modifyEnv (activeSyntaxContext.setState · previousContext)
    modifyEnv (activeDataParameters.setState · previousData)
  let name := (← getCurrNamespace) ++ name.getId.eraseMacroScopes
  modifyEnv (theoremParameters.addEntry · (name, parameters))

end LeanPRA.Library.FOL.DSL
