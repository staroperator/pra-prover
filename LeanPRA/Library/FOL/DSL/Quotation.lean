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
  | app (index : Nat) (args : List TermView)
  | parameter (index : Nat) (args : List TermView)
  | code (language value : Core.Term) (arguments : List TermView)
  deriving BEq, Hashable, Repr, Inhabited

inductive FormulaView where
  | falsum
  | equal (lhs rhs : TermView)
  | relation (index : Nat) (args : List TermView)
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
  parameters : Array Name
  arguments : Array Name
  isFormula : Bool
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

/-- The syntax type of an argument in the numerical definition's parameter order. -/
def DefinitionInfo.syntaxAt? (d : DefinitionInfo) (i : Nat) : Option SyntaxParameter := do
  let name ← (d.parameters ++ d.arguments)[i]?
  d.syntaxParameters.find? (·.name == name)

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
  | .app i args => .app i (args.map (fun a => replace a x t))
  | .parameter i args => .parameter i (args.map (fun a => replace a x t))
  | .code L value args => .code L value (args.map (fun a => replace a x t))

def FormulaView.replace (x : Name) (t : TermView) : FormulaView → FormulaView
  | .falsum => .falsum
  | .code L value args => .code L value (args.map (·.replace x t))
  | .equal a b => .equal (a.replace x t) (b.replace x t)
  | .relation i args => .relation i (args.map (·.replace x t))
  | .parameter i args => .parameter i (args.map (·.replace x t))
  | .imp a b => .imp (replace x t a) (replace x t b)
  | .all y a => if x == y then .all y a else .all y (replace x t a)

/-- Replace free variables simultaneously; inserted terms are left untouched. -/
partial def TermView.substitute (values : List (Name × TermView)) : TermView → TermView
  | .var x => (values.lookup x).getD (.var x)
  | .constant i => .constant i
  | .app i args => .app i (args.map (substitute values))
  | .parameter i args => .parameter i (args.map (substitute values))
  | .code L value args => .code L value (args.map (substitute values))

def FormulaView.substitute (values : List (Name × TermView)) : FormulaView → FormulaView
  | .falsum => .falsum
  | .equal t u => .equal (t.substitute values) (u.substitute values)
  | .relation i args => .relation i (args.map (·.substitute values))
  | .parameter i args => .parameter i (args.map (·.substitute values))
  | .code L value args => .code L value (args.map (·.substitute values))
  | .imp a b => .imp (substitute values a) (substitute values b)
  | .all x a => .all x (substitute (values.filter (·.1 != x)) a)

partial def TermView.variables : TermView → List Name
  | .var n => [n]
  | .constant _ => []
  | .app _ args | .parameter _ args | .code _ _ args => args.flatMap variables

def FormulaView.variables : FormulaView → List Name
  | .falsum => []
  | .code _ _ args => args.flatMap TermView.variables
  | .equal a b => a.variables ++ b.variables
  | .relation _ args | .parameter _ args => args.flatMap TermView.variables
  | .imp a b => a.variables ++ b.variables
  | .all x a => a.variables.filter (· != x)

private def replacementFunction (L : Term) (values : List Term) (targetSize : Nat) : Term :=
  let tail := applyDefinition `FOL.Term.var [L.shift,
    applyDefinition `add
      [applyDefinition `sub [.bvar 0, numeral values.length], numeral targetSize]]
  let body := values.zipIdx.foldr (fun (value, i) rest => applyDefinition `ite
    [applyDefinition `eqb [.bvar 0, numeral i], value.shift, rest]) tail
  .lam `i body

partial def TermView.encode (L : Term) (bound fvars : List Name) : TermView → CommandElabM Term
  | .parameter _ _ => throwError "a term parameter requires a schema instance"
  | .code _ value args => do
    let scope := bound ++ fvars
    if args == scope.map TermView.var then return value
    let values ← args.mapM (encode L bound fvars)
    return applyDefinition `FOL.Term.subst [L, value]
      [replacementFunction L values scope.length]
  | .var n => do
    if let some i := bound.idxOf? n then return applyDefinition `FOL.Term.var [L, numeral i]
    if let some i := fvars.idxOf? n then
      return applyDefinition `FOL.Term.var [L, numeral (bound.length + i)]
    throwError "unbound first-order variable `{n}`"
  | .constant i => pure (applyDefinition `FOL.Term.const [L, numeral i])
  | .app i args => do
    return applyDefinition `FOL.Term.app
      [L, numeral i, tupleCode (← args.mapM (encode L bound fvars))]

/-- Rebuild a closed definition from the explicit term arguments in its view. -/
private def definitionCode? (L value : Term) (values : List Term) :
    CommandElabM (Option Term) := do
  let .definition name parameters := value | return none
  let some d := (definitions.getState (← getEnv)).find? (·.name == name) | return none
  if d.syntaxParameters.any (fun p => p.isFormula || p.arity > 0) then return none
  unless d.isFormula && d.substitution.isSome && values.length == d.termPositions.length do
    return none
  unless d.termPositions.zipIdx.all (fun (position, i) =>
      parameters[position]? == some (applyDefinition `FOL.Term.var [L, numeral i])) do
    return none
  return some (.definition name (d.termPositions.zipIdx.foldl (fun parameters (position, i) =>
    parameters.set position values[i]!) parameters))

def FormulaView.encode (L : Term) (bound fvars : List Name) : FormulaView → CommandElabM Term
  | .code _ value args => do
    let scope := bound ++ fvars
    if args == scope.map TermView.var then return value
    let values ← args.mapM (TermView.encode L bound fvars)
    if let some applied ← definitionCode? L value values then return applied
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
  | .imp a b => do
    return applyDefinition `FOL.Formula.imp [← a.encode L bound fvars, ← b.encode L bound fvars]
  | .all x a => do
    return applyDefinition `FOL.Formula.all [← a.encode L (x :: bound) fvars]

def functionIndex (L : LanguageInfo) (n : Name) (arity : Nat) : CommandElabM Nat := do
  match L.functions.toList.findIdx? (fun (m, k) => m == n && k == arity) with
  | some i => pure i
  | none => throwError "unknown function `{n}` of arity {arity} in `{L.name}`"

private def abbreviation (L : LanguageInfo) (d : DefinitionInfo) (values : List TermView) :
    CommandElabM (Sum TermView FormulaView) := do
  unless d.language == L.name do throwError "FOL definition `{d.name}` uses another language"
  let some (arguments, body) := d.template |
    throwError "axiom templates require FOL definitions without PRA parameters or splices"
  unless arguments.size == values.length do
    throwError "FOL definition `{d.name}` expects {arguments.size} term arguments"
  return match body with
    | .inl t => .inl (t.substitute (arguments.toList.zip values))
    | .inr a => .inr (a.substitute (arguments.toList.zip values))

partial def parseTerm (L : LanguageInfo) (vars : List (Name × Name))
    (s : TSyntax `folTerm) (parameters : List SyntaxParameter := []) :
    CommandElabM TermView := withRef s do
  if let some expanded ← Lean.Elab.liftMacroM (expandMacro? s.raw) then
    return ← parseTerm L vars ⟨expanded⟩ parameters
  if s.raw.isOfKind ``termSplice || s.raw.isOfKind ``termDefinedApplication then
    throwError "axiom templates do not support PRA splices or parameterized FOL definitions"
  match s with
  | `(folTerm| ($t:folTerm)) => parseTerm L vars t parameters
  | `(folTerm| $n:ident($args:folTerm,*)) =>
    let values ← args.getElems.toList.mapM (fun t => parseTerm L vars t parameters)
    if let some i := parameters.findIdx? (·.name == n.getId.eraseMacroScopes) then
      let p := parameters[i]!
      unless !p.isFormula && p.arity == values.length do
        throwError "term parameter kind or arity mismatch"
      return .parameter i values
    if values.isEmpty then
      if let some i := L.constants.toList.idxOf? n.getId.eraseMacroScopes then return .constant i
    if let some d ← findDefinition n.getId.eraseMacroScopes then
      let .inl t ← abbreviation L d values | throwError "expected a term definition"
      return t
    return .app (← functionIndex L n.getId.eraseMacroScopes values.length) values
  | `(folTerm| $n:ident) =>
    if let some (_, v) := vars.find? (fun (k, _) => k == n.getId.eraseMacroScopes) then
      return .var v
    if let some i := parameters.findIdx? (·.name == n.getId.eraseMacroScopes) then
      let p := parameters[i]!
      unless !p.isFormula && p.arity == 0 do throwError "expected a term of arity zero"
      return .parameter i []
    if let some i := L.constants.toList.idxOf? n.getId.eraseMacroScopes then return .constant i
    if let some d ← findDefinition n.getId.eraseMacroScopes then
      let .inl t ← abbreviation L d [] | throwError "expected a term definition"
      return t
    throwError "unknown variable or constant `{n.getId.eraseMacroScopes}`"
  | _ => throwUnsupportedSyntax

private def parseFormulaApplication (L : LanguageInfo) (vars : List (Name × Name))
    (parameters : List SyntaxParameter) (name : Name) (args : List (TSyntax `folTerm)) :
    CommandElabM FormulaView := do
  let values ← args.mapM (fun t => parseTerm L vars t parameters)
  if let some i := parameters.findIdx? (·.name == name) then
    let arity := parameters[i]!.arity
    unless parameters[i]!.isFormula && values.length == arity do
      throwError "formula parameter `{name.eraseMacroScopes}` expects {arity} arguments, \
        got {values.length}"
    return .parameter i values
  if let some d ← findDefinition name then
    let .inr a ← abbreviation L d values | throwError "expected a formula definition"
    return a
  let some i := L.relations.toList.findIdx? (fun (m, k) => m == name && k == values.length)
    | throwError "unknown relation `{name}` of arity {values.length}"
  return .relation i values

partial def parseFormula (L : LanguageInfo) (vars : List (Name × Name))
    (s : TSyntax `folFormula) (parameters : List SyntaxParameter := []) :
    CommandElabM FormulaView := withRef s do
  if let some expanded ← Lean.Elab.liftMacroM (expandMacro? s.raw) then
    return ← parseFormula L vars ⟨expanded⟩ parameters
  if s.raw.isOfKind ``formulaSplice || s.raw.isOfKind ``formulaDefinedApplication then
    throwError "axiom templates do not support PRA splices or parameterized FOL definitions"
  match s with
  | `(folFormula| ($a:folFormula)) => parseFormula L vars a parameters
  | `(folFormula| ⊥) => pure .falsum
  | `(folFormula| $a:folTerm = $b:folTerm) =>
    return .equal (← parseTerm L vars a parameters) (← parseTerm L vars b parameters)
  | `(folFormula| $a:folTerm ≠ $b:folTerm) =>
    return (FormulaView.equal (← parseTerm L vars a parameters)
      (← parseTerm L vars b parameters)).neg
  | `(folFormula| ¬ $a:folFormula) => return (← parseFormula L vars a parameters).neg
  | `(folFormula| $a:folFormula → $b:folFormula) =>
    return .imp (← parseFormula L vars a parameters) (← parseFormula L vars b parameters)
  | `(folFormula| $a:folFormula ∧ $b:folFormula) =>
    return (← parseFormula L vars a parameters).conj (← parseFormula L vars b parameters)
  | `(folFormula| $a:folFormula ∨ $b:folFormula) =>
    return (← parseFormula L vars a parameters).disj (← parseFormula L vars b parameters)
  | `(folFormula| $a:folFormula ↔ $b:folFormula) =>
    let a ← parseFormula L vars a parameters
    let b ← parseFormula L vars b parameters
    return (FormulaView.imp a b).conj (.imp b a)
  | `(folFormula| ∀ $xs:ident* , $a:folFormula)
  | `(folFormula| ∃ $xs:ident* , $a:folFormula) =>
    let mut env := vars
    let mut names := #[]
    for x in xs do
      let fresh ← liftCoreM (mkFreshUserName x.getId.eraseMacroScopes)
      names := names.push fresh
      env := (x.getId.eraseMacroScopes, fresh) :: env
    let body ← parseFormula L env a parameters
    let existential := s.raw[0].getAtomVal.trimAscii.toString == "∃"
    return names.toList.foldr (fun x b => if existential then .ex x b else .all x b) body
  | `(folFormula| $n:ident($args:folTerm,*)) =>
    parseFormulaApplication L vars parameters n.getId.eraseMacroScopes args.getElems.toList
  | `(folFormula| $n:ident $args:folTerm*) =>
    parseFormulaApplication L vars parameters n.getId.eraseMacroScopes args.toList
  | `(folFormula| $n:ident) => parseFormulaApplication L vars parameters n.getId.eraseMacroScopes []
  | _ => throwUnsupportedSyntax

end LeanPRA.Library.FOL.DSL
