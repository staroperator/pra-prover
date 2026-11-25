module

public meta import LeanPRA.Library.FOL.DSL.Syntax
public meta import LeanPRA.Library.FOL.DSL.Substitution

/-!
# Elaboration of first-order quotations

Frontend views track named variables and symbol arities while constructing numerical PRA syntax.
Bound names receive distinct internal names, and numerical output uses de Bruijn indices.

- `TermView` and `FormulaView` represent the source expressions during elaboration.
- `DefinitionInfo` records a definition, its optional static axiom template, and its
  substitution theorem.
- `parseTerm` and `parseFormula` resolve names in the selected language and binder context.
- `TermView.encode` and `FormulaView.encode` produce numerical PRA expressions. A definition
  applied to term arguments is encoded as an application of its numerical definition.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL

open LeanPRA.Library.Tactic.Construction

open Lean hiding Term

open Lean.Elab.Command

open Lean.Elab (throwUnsupportedSyntax)

open LeanPRA.Core
open LeanPRA.Surface

inductive TermView where
  | var (name : Name)
  | constant (index : Nat)
  | indexedConst (family : Nat) (member : Core.Term)
  | app (index : Nat) (args : List TermView)
  | indexedApp (family : Nat) (member : Core.Term) (args : List TermView)
  | parameter (index : Nat) (args : List TermView)
  | code (language value : Core.Term) (arguments : List TermView)
  deriving BEq, Hashable, Repr, Inhabited

inductive FormulaView where
  | falsum
  | equal (lhs rhs : TermView)
  | relation (index : Nat) (args : List TermView)
  | indexedRelation (family : Nat) (member : Core.Term) (args : List TermView)
  | parameter (index : Nat) (args : List TermView)
  | imp (lhs rhs : FormulaView)
  | all (name : Name) (body : FormulaView)
  | code (language value : Core.Term) (arguments : List TermView)
  deriving BEq, Hashable, Repr, Inhabited

/-- A syntax parameter's result kind and number of explicit term arguments.
Surrounding free variables are allowed at every arity. -/
structure SyntaxParameter where
  name : Name
  isFormula : Bool
  arity : Nat := 0
  deriving BEq, Inhabited, Repr

/-- Read the syntax type of a declaration parameter. -/
def syntaxParameterType? (type : Syntax) : Option (Bool × Nat) :=
  if type.isOfKind ``termParameterType || type.isOfKind ``formulaParameterType then
    some (type.isOfKind ``formulaParameterType,
      if type[1].getArgs.isEmpty then 0 else type[1][1].isNatLit?.getD 0)
  else if type.isIdent && [ `term, `formula ].contains type.getId.eraseMacroScopes then
    some (type.getId.eraseMacroScopes == `formula, 0)
  else none

/-- Translate syntax parameter types to numerical PRA parameters, keeping their frontend types. -/
def declarationParameters (ps : Array (TSyntax `praParam)) :
    CommandElabM (Array (TSyntax `praParam) × Array SyntaxParameter) := do
  let mut binders := #[]
  let mut syntaxParameters := #[]
  for p in ps do
    let (ids, type) ← match p with
      | `(praParam| ($ids:ident* : $type:praExpr)) => pure (ids, type)
      | `(praParam| {$ids:ident* : $type:praExpr}) => pure (ids, type)
      | _ => throwUnsupportedSyntax
    if let some (formula, arity) := syntaxParameterType? type then
      for id in ids do
        syntaxParameters := syntaxParameters.push ⟨id.getId.eraseMacroScopes, formula, arity⟩
      binders := binders.push (← `(praParam| ($ids:ident* : Nat)))
    else binders := binders.push p
  return (binders, syntaxParameters)

initialize activeDataParameters : EnvExtension (Array Name) ←
  registerEnvExtension (pure #[])

/-- Ordinary PRA binders need an explicit code injection when used as FOL syntax. -/
def dataParameterNames (ps : Array (TSyntax `praParam)) : Array Name := Id.run do
  let mut names := #[]
  for p in ps do
    let ids := p.raw[1].getArgs
    let type := p.raw[3]
    if (syntaxParameterType? type).isNone then
      names := names ++ ids.map (·.getId.eraseMacroScopes)
  return names

initialize activeSyntaxContext : EnvExtension Nat ← registerEnvExtension (pure 0)

initialize activeSyntaxParameters : EnvExtension (Array SyntaxParameter) ←
  registerEnvExtension (pure #[])

initialize theoremParameters : SimplePersistentEnvExtension
    (Name × Array SyntaxParameter) (Array (Name × Array SyntaxParameter)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

/-- An abbreviation's PRA interface and, when available, its syntax without PRA splices.
The static template uses fresh names for its term parameters. -/
structure DefinitionInfo where
  name : Name
  language : Name
  /-- The declaration parameters followed by the ordinary arguments, in source order. -/
  binders : Array Name
  /-- The binders supplied by the positional term list in a quotation. -/
  positional : Array Name
  isFormula : Bool
  /-- The number of ordinary inputs to the PRA function. -/
  arity : Nat := 0
  /-- Explicit term slots in the returned code, after the declaration's term arguments. -/
  resultArity : Nat := 0
  syntaxParameters : Array SyntaxParameter := #[]
  template : Option (Array Name × Sum TermView FormulaView) := none
  /-- The theorem stating how a substitution acts on the definition, when it was proved. -/
  substitution : Option Name := none
  /-- The positions, among the parameters and arguments, of the terms that a substitution
  changes: the term arguments, and the PRA parameters that the body uses as terms. -/
  termPositions : List Nat := []
  deriving Inhabited

/-- The syntax type of a binder at its position in the numerical definition. -/
def DefinitionInfo.syntaxAt? (d : DefinitionInfo) (i : Nat) : Option SyntaxParameter := do
  let name ← d.binders[i]?
  d.syntaxParameters.find? (·.name == name)

/-- Apply the numerical definition to its parameters and ordinary arguments in source order. -/
def DefinitionInfo.apply (d : DefinitionInfo) (values : List Term) : Term :=
  if d.arity == 0 then .definition d.name values
  else
    let (parameters, arguments) := values.splitAt (d.binders.size - d.arity)
    applyDefinition d.name arguments parameters

/-- Move a syntax parameter along a substitution, protecting its explicit argument slots. -/
def SyntaxParameter.transport (p : SyntaxParameter) (L f value : Term) : Term :=
  let substitution := if p.arity == 0 then f else
    applyDefinition `FOL.liftSubst [L, numeral p.arity] [f]
  applyDefinition (if p.isFormula then `FOL.Formula.subst else `FOL.Term.subst)
    [L, value] [substitution]

initialize definitions : SimplePersistentEnvExtension DefinitionInfo (Array DefinitionInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

/-- Find a FOL definition at a saturated numerical application and return all its inputs. -/
def appliedDefinition? (t : Term) : CommandElabM (Option (DefinitionInfo × List Term)) := do
  let (.definition name parameters, args) := getAppFnArgs t | return none
  let some d := (definitions.getState (← getEnv)).find? (·.name == name) | return none
  unless d.arity == args.length do return none
  return some (d, if args.isEmpty then parameters else parameters ++ args)

def findDefinition (name : Name) : CommandElabM (Option DefinitionInfo) := do
  let some declaration ← LeanPRA.Surface.resolveDeclaration?
      (LeanPRA.Surface.CoreEnvironment.getState (← getEnv)) name.eraseMacroScopes | return none
  return (definitions.getState (← getEnv)).find? (·.name == declaration.name)

def FormulaView.neg (a : FormulaView) : FormulaView := .imp a .falsum

def FormulaView.conj (a b : FormulaView) : FormulaView := (FormulaView.imp a b.neg).neg

def FormulaView.disj (a b : FormulaView) : FormulaView := .imp a.neg b

def FormulaView.ex (n : Name) (a : FormulaView) : FormulaView := (FormulaView.all n a.neg).neg

partial def TermView.replace (target : TermView) (x : Name) (t : TermView) : TermView :=
  match target with
  | .var y => if x == y then t else .var y
  | .constant i => .constant i
  | .indexedConst i k => .indexedConst i k
  | .app i args => .app i (args.map (fun a => replace a x t))
  | .indexedApp i k args => .indexedApp i k (args.map (fun a => replace a x t))
  | .parameter i args => .parameter i (args.map (fun a => replace a x t))
  | .code L value args => .code L value (args.map (fun a => replace a x t))

def FormulaView.replace (x : Name) (t : TermView) : FormulaView → FormulaView
  | .falsum => .falsum
  | .code L value args => .code L value (args.map (·.replace x t))
  | .equal a b => .equal (a.replace x t) (b.replace x t)
  | .relation i args => .relation i (args.map (·.replace x t))
  | .indexedRelation i k args => .indexedRelation i k (args.map (·.replace x t))
  | .parameter i args => .parameter i (args.map (·.replace x t))
  | .imp a b => .imp (replace x t a) (replace x t b)
  | .all y a => if x == y then .all y a else .all y (replace x t a)

/-- Replace free variables simultaneously; inserted terms are left untouched. -/
partial def TermView.substitute (values : List (Name × TermView)) : TermView → TermView
  | .var x => (values.lookup x).getD (.var x)
  | .constant i => .constant i
  | .indexedConst i k => .indexedConst i k
  | .app i args => .app i (args.map (substitute values))
  | .indexedApp i k args => .indexedApp i k (args.map (substitute values))
  | .parameter i args => .parameter i (args.map (substitute values))
  | .code L value args => .code L value (args.map (substitute values))

def FormulaView.substitute (values : List (Name × TermView)) : FormulaView → FormulaView
  | .falsum => .falsum
  | .equal t u => .equal (t.substitute values) (u.substitute values)
  | .relation i args => .relation i (args.map (·.substitute values))
  | .indexedRelation i k args => .indexedRelation i k (args.map (·.substitute values))
  | .parameter i args => .parameter i (args.map (·.substitute values))
  | .code L value args => .code L value (args.map (·.substitute values))
  | .imp a b => .imp (substitute values a) (substitute values b)
  | .all x a => .all x (substitute (values.filter (·.1 != x)) a)

partial def TermView.variables : TermView → List Name
  | .var n => [n]
  | .constant _ | .indexedConst .. => []
  | .app _ args | .indexedApp _ _ args | .parameter _ args | .code _ _ args =>
    args.flatMap variables

def FormulaView.variables : FormulaView → List Name
  | .falsum => []
  | .code _ _ args => args.flatMap TermView.variables
  | .equal a b => a.variables ++ b.variables
  | .relation _ args | .indexedRelation _ _ args | .parameter _ args =>
    args.flatMap TermView.variables
  | .imp a b => a.variables ++ b.variables
  | .all x a => a.variables.filter (· != x)

/-- Rebuild a closed definition from the explicit term arguments in its view. -/
private def definitionCode? (formula : Bool) (L value : Term) (values : List Term) :
    CommandElabM (Option Term) := do
  let some (d, inputs) ← appliedDefinition? value | return none
  if d.syntaxParameters.any (fun p => p.isFormula || p.arity > 0) then return none
  unless L == applyDefinition (d.language ++ `language) && d.isFormula == formula do return none
  let positions := if d.template.isSome then List.range d.positional.size else d.termPositions
  unless (d.template.isSome || d.substitution.isSome) && values.length == positions.length do
    return none
  unless positions.zipIdx.all (fun (position, i) =>
      inputs[position]? == some (applyDefinition `FOL.Term.var [L, numeral i])) do
    return none
  return some (d.apply (positions.zipIdx.foldl (fun inputs (position, i) =>
    inputs.set position values[i]!) inputs))

partial def TermView.encode (L : Term) (bound fvars : List Name) : TermView → CommandElabM Term
  | .parameter _ _ => throwError "a term parameter requires a schema instance"
  | .code _ value args => do
    let scope := bound ++ fvars
    if args == scope.map TermView.var then return value
    let values ← args.mapM (encode L bound fvars)
    if let some applied ← definitionCode? false L value values then return applied
    return applyDefinition `FOL.Term.subst [L, value]
      [SubstitutionView.encode L ⟨values, scope.length⟩]
  | .var n => do
    if let some i := bound.idxOf? n then return applyDefinition `FOL.Term.var [L, numeral i]
    if let some i := fvars.idxOf? n then
      return applyDefinition `FOL.Term.var [L, numeral (bound.length + i)]
    throwError "unbound first-order variable `{n}`"
  | .constant i => pure (applyDefinition `FOL.Term.const [L, numeral i])
  | .indexedConst i k => pure (applyDefinition `FOL.Term.const
      [L, applyDefinition `FOL.Language.constantFamilyMember [L, numeral i, k]])
  | .app i args => do
    return applyDefinition `FOL.Term.app
      [L, numeral i, tupleCode (← args.mapM (encode L bound fvars))]
  | .indexedApp i k args => do
    return applyDefinition `FOL.Term.app
      [L, applyDefinition `FOL.Language.functionFamilyMember [L, numeral i, k],
       tupleCode (← args.mapM (encode L bound fvars))]

def FormulaView.encode (L : Term) (bound fvars : List Name) : FormulaView → CommandElabM Term
  | .code _ value args => do
    let scope := bound ++ fvars
    if args == scope.map TermView.var then return value
    let values ← args.mapM (TermView.encode L bound fvars)
    if let some applied ← definitionCode? true L value values then return applied
    return applyDefinition `FOL.Formula.subst [L, value]
      [SubstitutionView.encode L ⟨values, scope.length⟩]
  | .parameter _ _ => throwError "a formula parameter requires a schema instance"
  | .falsum => pure (applyDefinition `FOL.Formula.falsum)
  | .equal a b => do
    return applyDefinition `FOL.Formula.equal
      [L, ← a.encode L bound fvars, ← b.encode L bound fvars]
  | .relation i args => do
    return applyDefinition `FOL.Formula.rel
      [L, numeral i, tupleCode (← args.mapM (TermView.encode L bound fvars))]
  | .indexedRelation i k args => do
    return applyDefinition `FOL.Formula.rel
      [L, applyDefinition `FOL.Language.relationFamilyMember [L, numeral i, k],
       tupleCode (← args.mapM (TermView.encode L bound fvars))]
  | .imp a b => do
    return applyDefinition `FOL.Formula.imp [← a.encode L bound fvars, ← b.encode L bound fvars]
  | .all x a => do
    return applyDefinition `FOL.Formula.all [← a.encode L (x :: bound) fvars]

def functionIndex (L : LanguageInfo) (n : Name) (arity : Nat) : CommandElabM Nat := do
  match L.functions.toList.findIdx? (fun (m, k) => m == n && k == arity) with
  | some i => pure i
  | none => throwError "unknown function `{n}` of arity {arity} in `{L.name}`"

/-- Theory axioms can use named definitions directly. Static templates for later expansion
keep their full syntax so schemas can recover parameters inside an abbreviation. -/
private structure TemplateContext where
  parameters : List SyntaxParameter := []
  useDefinitions : Bool := false

private partial def containsParameter : TermView → Bool
  | .parameter .. => true
  | .app _ args | .indexedApp _ _ args | .code _ _ args => args.any containsParameter
  | _ => false

private def abbreviation (L : LanguageInfo) (ctx : TemplateContext) (d : DefinitionInfo)
    (values : List TermView) :
    CommandElabM (Sum TermView FormulaView) := do
  unless d.language == L.name do throwError "FOL definition `{d.name}` uses another language"
  let some (arguments, body) := d.template |
    throwError "axiom templates require FOL definitions without PRA parameters or splices"
  unless arguments.size == values.length do
    throwError "FOL definition `{d.name}` expects {arguments.size} term arguments"
  if ctx.useDefinitions && !values.any containsParameter then
    let language := languageTerm L
    let slots := (List.range values.length).map (fun i =>
      applyDefinition `FOL.Term.var [language, numeral i])
    let code := d.apply slots
    return if d.isFormula then .inr (.code language code values)
      else .inl (.code language code values)
  return match body with
    | .inl t => .inl (t.substitute (arguments.toList.zip values))
    | .inr a => .inr (a.substitute (arguments.toList.zip values))

private def templateMember (indices : Array (TSyntax `praExpr)) : CommandElabM Term := do
  let values ← indices.toList.mapM fun (index : TSyntax `praExpr) => do
    let `(praExpr| $value:num) := index |
      throwErrorAt index "a family index in an axiom template must be a natural number literal"
    return numeral value.getNat
  return tupleCode values

private partial def TemplateContext.term (ctx : TemplateContext) (L : LanguageInfo)
    (vars : List (Name × Name))
    (s : TSyntax `folTerm) :
    CommandElabM TermView := withRef s do
  if let some expanded ← Lean.Elab.liftMacroM (expandMacro? s.raw) then
    return ← ctx.term L vars ⟨expanded⟩
  if s.raw.isOfKind ``termSplice || s.raw.isOfKind ``termDefinedApplication then
    throwError "axiom templates do not support PRA splices or parameterized FOL definitions"
  match s with
  | `(folTerm| ($t:folTerm)) => ctx.term L vars t
  | `(folTerm| $n:ident[$indices:praExpr,*]) => do
    let i ← withRef n <|
      familyIndex L.constantFamilies n.getId.eraseMacroScopes indices.getElems.size 0
    return .indexedConst i (← templateMember indices.getElems)
  | `(folTerm| $n:ident[$indices:praExpr,*]($args:folTerm,*)) => do
    let i ← withRef n <|
      familyIndex L.functionFamilies n.getId.eraseMacroScopes indices.getElems.size
        args.getElems.size
    return .indexedApp i (← templateMember indices.getElems)
      (← args.getElems.toList.mapM (fun t => ctx.term L vars t))
  | `(folTerm| $n:ident($args:folTerm,*)) =>
    let values ← args.getElems.toList.mapM (fun t => ctx.term L vars t)
    if let some i := ctx.parameters.findIdx? (·.name == n.getId.eraseMacroScopes) then
      let p := ctx.parameters[i]!
      unless !p.isFormula && p.arity == values.length do
        throwError "term parameter kind or arity mismatch"
      return .parameter i values
    if values.isEmpty then
      if let some i := L.constants.toList.idxOf? n.getId.eraseMacroScopes then return .constant i
    if let some d ← findDefinition n.getId.eraseMacroScopes then
      let .inl t ← abbreviation L ctx d values | throwError "expected a term definition"
      return t
    return .app (← functionIndex L n.getId.eraseMacroScopes values.length) values
  | `(folTerm| $n:ident) =>
    if let some (_, v) := vars.find? (fun (k, _) => k == n.getId.eraseMacroScopes) then
      return .var v
    if let some i := ctx.parameters.findIdx? (·.name == n.getId.eraseMacroScopes) then
      let p := ctx.parameters[i]!
      unless !p.isFormula && p.arity == 0 do throwError "expected a term of arity zero"
      return .parameter i []
    if let some i := L.constants.toList.idxOf? n.getId.eraseMacroScopes then return .constant i
    if let some d ← findDefinition n.getId.eraseMacroScopes then
      let .inl t ← abbreviation L ctx d [] | throwError "expected a term definition"
      return t
    throwError "unknown variable or constant `{n.getId.eraseMacroScopes}`"
  | _ => throwUnsupportedSyntax

private def TemplateContext.formulaApplication (ctx : TemplateContext) (L : LanguageInfo)
    (vars : List (Name × Name))
    (name : Name) (args : List (TSyntax `folTerm)) :
    CommandElabM FormulaView := do
  let values ← args.mapM (fun t => ctx.term L vars t)
  if let some i := ctx.parameters.findIdx? (·.name == name) then
    let arity := ctx.parameters[i]!.arity
    unless ctx.parameters[i]!.isFormula && values.length == arity do
      throwError "formula parameter `{name.eraseMacroScopes}` expects {arity} arguments, \
        got {values.length}"
    return .parameter i values
  if let some d ← findDefinition name then
    let .inr a ← abbreviation L ctx d values | throwError "expected a formula definition"
    return a
  let some i := L.relations.toList.findIdx? (fun (m, k) => m == name && k == values.length)
    | throwError "unknown relation `{name}` of arity {values.length}"
  return .relation i values

private partial def TemplateContext.formula (ctx : TemplateContext) (L : LanguageInfo)
    (vars : List (Name × Name))
    (s : TSyntax `folFormula) :
    CommandElabM FormulaView := withRef s do
  if let some expanded ← Lean.Elab.liftMacroM (expandMacro? s.raw) then
    return ← ctx.formula L vars ⟨expanded⟩
  if s.raw.isOfKind ``formulaSplice || s.raw.isOfKind ``formulaDefinedApplication then
    throwError "axiom templates do not support PRA splices or parameterized FOL definitions"
  match s with
  | `(folFormula| ($a:folFormula)) => ctx.formula L vars a
  | `(folFormula| ⊥) => pure .falsum
  | `(folFormula| $a:folTerm = $b:folTerm) =>
    return .equal (← ctx.term L vars a) (← ctx.term L vars b)
  | `(folFormula| $a:folTerm ≠ $b:folTerm) =>
    return (FormulaView.equal (← ctx.term L vars a)
      (← ctx.term L vars b)).neg
  | `(folFormula| ¬ $a:folFormula) => return (← ctx.formula L vars a).neg
  | `(folFormula| $a:folFormula → $b:folFormula) =>
    return .imp (← ctx.formula L vars a) (← ctx.formula L vars b)
  | `(folFormula| $a:folFormula ∧ $b:folFormula) =>
    return (← ctx.formula L vars a).conj (← ctx.formula L vars b)
  | `(folFormula| $a:folFormula ∨ $b:folFormula) =>
    return (← ctx.formula L vars a).disj (← ctx.formula L vars b)
  | `(folFormula| $a:folFormula ↔ $b:folFormula) =>
    let a ← ctx.formula L vars a
    let b ← ctx.formula L vars b
    return (FormulaView.imp a b).conj (.imp b a)
  | `(folFormula| ∀ $xs:ident* , $a:folFormula)
  | `(folFormula| ∃ $xs:ident* , $a:folFormula) =>
    let mut env := vars
    let mut names := #[]
    for x in xs do
      let fresh ← liftCoreM (mkFreshUserName x.getId.eraseMacroScopes)
      names := names.push fresh
      env := (x.getId.eraseMacroScopes, fresh) :: env
    let body ← ctx.formula L env a
    let existential := s.raw[0].getAtomVal.trimAscii.toString == "∃"
    return names.toList.foldr (fun x b => if existential then .ex x b else .all x b) body
  | `(folFormula| $n:ident[$indices:praExpr,*]($args:folTerm,*)) => do
    let i ← withRef n <|
      familyIndex L.relationFamilies n.getId.eraseMacroScopes indices.getElems.size
        args.getElems.size
    return .indexedRelation i (← templateMember indices.getElems)
      (← args.getElems.toList.mapM (fun t => ctx.term L vars t))
  | `(folFormula| $n:ident($args:folTerm,*)) =>
    ctx.formulaApplication L vars n.getId.eraseMacroScopes args.getElems.toList
  | `(folFormula| $n:ident $args:folTerm*) =>
    ctx.formulaApplication L vars n.getId.eraseMacroScopes args.toList
  | `(folFormula| $n:ident) => ctx.formulaApplication L vars n.getId.eraseMacroScopes []
  | _ => throwUnsupportedSyntax

def parseTerm (L : LanguageInfo) (vars : List (Name × Name)) (s : TSyntax `folTerm)
    (parameters : List SyntaxParameter := []) : CommandElabM TermView :=
  TemplateContext.term { parameters } L vars s

def parseFormula (L : LanguageInfo) (vars : List (Name × Name)) (s : TSyntax `folFormula)
    (parameters : List SyntaxParameter := []) (useDefinitions : Bool := false) :
    CommandElabM FormulaView :=
  TemplateContext.formula { parameters, useDefinitions } L vars s

end LeanPRA.Library.FOL.DSL
