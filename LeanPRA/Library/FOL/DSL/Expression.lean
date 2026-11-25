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

- `termExpression` and `formulaExpression` expand notation to PRA syntax constructors.
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

/-- Read a formula argument whose spelling is also a term: a name, a symbol or definition
application in parentheses, a family member, a parenthesized term, or a splice. The syntax tree
is converted directly; no source text is parsed again. -/
partial def formulaAsTerm (s : TSyntax `folFormula) : CommandElabM (TSyntax `folTerm) :=
  withRef s do
  let stx := s.raw
  if stx.isOfKind ``formulaTerm then return ⟨stx[0]⟩
  if stx.isOfKind ``formulaSplice then return ⟨← `(folTerm| ${$(⟨stx[2]⟩):praExpr})⟩
  if stx.isOfKind ``formulaDefinedApplication then
    return ⟨stx.setKind ``termDefinedApplication⟩
  match s with
  | `(folFormula| ($a:folFormula)) => return ← `(folTerm| ($(← formulaAsTerm a)))
  | `(folFormula| $n:ident) => `(folTerm| $n:ident)
  | `(folFormula| $n:ident($args:folTerm,*)) => `(folTerm| $n:ident($args,*))
  | `(folFormula| $n:ident[$indices:praExpr,*]($args:folTerm,*)) =>
    `(folTerm| $n:ident[$indices,*]($args,*))
  | _ => throwErrorAt s "expected a term argument"

private partial def termAsNumerical (s : TSyntax `folTerm) : CommandElabM (TSyntax `praExpr) :=
  withRef s do
  if s.raw.isOfKind ``termSplice then return ⟨s.raw[2]⟩
  match s with
  | `(folTerm| ($t:folTerm)) => return ← `(praExpr| ($(← termAsNumerical t)))
  | `(folTerm| $n:ident) => `(praExpr| $n:ident)
  | `(folTerm| $n:ident($t:folTerm)) => `(praExpr| $n:ident ($(← termAsNumerical t)))
  | _ => throwErrorAt s "expected a PRA numerical expression; write it as a braced splice"

/-- Read an actual that parsed as first-order syntax but is used as a PRA numerical expression.
The shared spelling covers names, applications written with spaces, parentheses, and braced
splices. The syntax tree is converted directly; other PRA expressions use a braced splice. -/
partial def formulaAsNumerical (s : TSyntax `folFormula) : CommandElabM (TSyntax `praExpr) :=
  withRef s do
  let stx := s.raw
  if stx.isOfKind ``formulaSplice then return ⟨stx[2]⟩
  if stx.isOfKind ``formulaTerm then return ← termAsNumerical ⟨stx[0]⟩
  match s with
  | `(folFormula| ($a:folFormula)) => return ← `(praExpr| ($(← formulaAsNumerical a)))
  | `(folFormula| $n:ident) => `(praExpr| $n:ident)
  | `(folFormula| $n:ident $args:folTerm*) => do
    let mut result ← `(praExpr| $n:ident)
    for arg in args do result ← `(praExpr| $result $(← termAsNumerical arg))
    return result
  | `(folFormula| $n:ident($t:folTerm)) => `(praExpr| $n:ident ($(← termAsNumerical t)))
  | _ => throwErrorAt s "expected a PRA numerical expression; write it as a braced splice"

/-- Abstract the arguments still expected by a partially applied syntax value. -/
def completeApplication (body : Syntax) (expected : SyntaxParameter) (bound : List Name) :
    CommandElabM (Syntax × List Name) := do
  if expected.arity == 0 then return (body, bound)
  let names ← (List.range expected.arity).mapM fun _ => do
    let name ← liftCoreM (mkFreshUserName `_folSlot)
    pure (Name.mkSimple name.toString)
  let slots ← names.toArray.mapM fun name => `(folTerm| $(mkIdent name):ident)
  if body.isOfKind ``formulaDefinedApplication || body.isOfKind ``termDefinedApplication then
    let arguments := body[3].getSepArgs ++ slots.map (·.raw)
    let applied := body.setArg 3 (Syntax.mkSep arguments (mkAtom ","))
    return (applied, names.reverse ++ bound)
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
  if s.isOfKind ``termDefinedApplication then
    return ← functionApplication L bound s[0].getId.eraseMacroScopes
      (s[3].getSepArgs.map (⟨·⟩)) (s[1].getArgs.map (⟨·⟩)) parameters ambient
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
    (args : Array (TSyntax `folTerm)) (actuals : Array (TSyntax `folPraActual))
    (parameters : Array SyntaxParameter) (ambient : Nat) :
    CommandElabM (TSyntax `praExpr) := do
  if let some p := parameters.find? (·.name == name) then
    unless !p.isFormula && p.arity == args.size && actuals.isEmpty do
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

private partial def definitionApplication (L : LanguageInfo) (bound : List Name)
    (d : DefinitionInfo) (args : Array (TSyntax `folTerm))
    (actuals : Array (TSyntax `folPraActual)) (formula : Bool)
    (parameters : Array SyntaxParameter) (ambient : Nat := 0) :
    CommandElabM (TSyntax `praExpr) := do
  unless d.language == L.name do throwError "FOL definition `{d.name}` uses another language"
  unless d.isFormula == formula do throwError "FOL definition `{d.name}` has the wrong result kind"
  let arity := d.positional.size + d.resultArity
  unless args.size == arity do
    throwError "FOL definition `{d.name}` expects {arity} term arguments"
  let mut supplied : List (Name × Syntax) := []
  for actual in actuals do
    let name ← match actual with
      | `(folPraActual| ($name:ident := fun $_:ident* => $_:folFormula)) =>
        pure name.getId.eraseMacroScopes
      | `(folPraActual| ($name:ident := ${$_:praExpr})) => pure name.getId.eraseMacroScopes
      | `(folPraActual| ($name:ident := $_:praExpr)) => pure name.getId.eraseMacroScopes
      | `(folPraActual| ($name:ident := $_:folFormula)) => pure name.getId.eraseMacroScopes
      | _ => throwUnsupportedSyntax
    unless d.binders.contains name && !d.positional.contains name do
      throwErrorAt actual "unknown named parameter `{name}`"
    if (supplied.lookup name).isSome then throwErrorAt actual "duplicate parameter `{name}`"
    supplied := (name, actual.raw) :: supplied
  let positional := d.positional.toList.zip args.toList
  let values ← d.binders.toList.mapM fun name => do
    if let some term := positional.lookup name then
      return ← termExpression L bound term.raw parameters ambient
    let some actual := supplied.lookup name |
      throwError "missing parameter `{name}` of `{d.name}`"
    if let some expected := d.syntaxParameters.find? (·.name == name) then
      return ← syntaxActual L bound parameters expected actual ambient
    if let `(folPraActual| ($_:ident := $value:praExpr)) := actual then return value
    let `(folPraActual| ($_:ident := $value:folFormula)) := actual |
      throwErrorAt actual "expected an ordinary PRA argument"
    formulaAsNumerical value
  let mut result ← `(praExpr| @$(mkIdent (`_root_ ++ d.name)):ident)
  for value in values do result ← `(praExpr| $result ($value))
  if d.resultArity > 0 then
    let terms ← (args.toList.drop d.positional.size).mapM fun t =>
      termExpression L bound t.raw parameters ambient
    return ← applySyntax L formula result terms 0
  return result

/-- Elaborate a syntax actual in the context where it is supplied. -/
private partial def syntaxActual (L : LanguageInfo) (bound : List Name)
    (parameters : Array SyntaxParameter) (expected : SyntaxParameter) (actual : Syntax)
    (ambient : Nat := 0) :
    CommandElabM (TSyntax `praExpr) := do
  if let `(folPraActual| ($_:ident := ${$value:praExpr})) := actual then
    return ← shiftExpression L (bound.length + ambient) value expected.isFormula expected.arity
  if let `(folPraActual| ($_:ident := fun $xs:ident* => $body:folFormula)) := actual then
    unless xs.size == expected.arity do
      throwErrorAt actual "expected {expected.arity} explicit binders"
    let scope := xs.toList.reverse.map (·.getId.eraseMacroScopes) ++ bound
    if expected.isFormula then return ← formulaExpression L scope body parameters ambient
    let term ← formulaAsTerm body
    return ← termExpression L scope term parameters ambient
  if let `(folPraActual| ($_:ident := $body:folFormula)) := actual then
    let body ← if expected.isFormula then pure body.raw else pure (← formulaAsTerm body).raw
    let (body, scope) ← completeApplication body expected bound
    if expected.isFormula then return ← formulaExpression L scope body parameters ambient
    else return ← termExpression L scope body parameters ambient
  let `(folPraActual| ($_:ident := $value:praExpr)) := actual | throwUnsupportedSyntax
  if let `(praExpr| $id:ident) := value then
    if let some p := parameters.find? (·.name == id.getId.eraseMacroScopes) then
      unless p.isFormula == expected.isFormula && p.arity ≥ expected.arity do
        throwErrorAt actual "syntax parameter kind or arity mismatch"
      if p.arity == expected.arity then
        return ← shiftExpression L (bound.length + ambient) value p.isFormula p.arity
  throwErrorAt value "expected a syntax argument; inject numerical codes with a braced splice"

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
  if s.isOfKind ``formulaDefinedApplication then
    return ← relationApplication L bound s[0].getId.eraseMacroScopes
      (s[3].getSepArgs.map (⟨·⟩)) (s[1].getArgs.map (⟨·⟩)) parameters ambient
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
  | `(folFormula| $n:ident $args:folTerm*) =>
    relationApplication L bound n.getId.eraseMacroScopes args #[] parameters ambient
  | `(folFormula| $n:ident) =>
    relationApplication L bound n.getId.eraseMacroScopes #[] #[] parameters ambient
  | _ => throwError "unsupported FOL formula"

private partial def relationApplication (L : LanguageInfo) (bound : List Name) (name : Name)
    (args : Array (TSyntax `folTerm)) (actuals : Array (TSyntax `folPraActual))
    (parameters : Array SyntaxParameter) (ambient : Nat) :
    CommandElabM (TSyntax `praExpr) := do
  if let some p := parameters.find? (·.name == name) then
    unless p.isFormula && p.arity == args.size && actuals.isEmpty do
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
