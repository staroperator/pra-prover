module

public meta import LeanPRA.Library.FOL.DSL.Schema

/-!
# Language and theory declarations

Source declarations produce numerical PRA definitions. Frontend metadata records symbol names,
axiom templates and their syntax parameters for subsequent proof elaboration.
Relation declarations require positive arity; `relation P of 0` is rejected.
A fixed axiom given by a named sentence uses that sentence's PRA code directly. A compound
axiom gets a `.formula` declaration whose body refers to the definitions used in the axiom.
An extension tests the parent's membership function together with its new axioms.
`T.isAxiom_of_parent` is a checked PRA proof of inclusion of the parent axiom set.

- `TheoryInfo` stores the language, named axioms and formula schemas used by the frontend.
- `declareLanguage` elaborates symbol declarations into the numerical language definition.
- `declareTheory` elaborates axioms and formula schemas into a numerical membership test.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL

open LeanPRA.Library.Tactic.Construction

open Lean hiding Term

open Lean.Elab.Command

open Lean.Elab (throwUnsupportedSyntax)

open LeanPRA.Core

structure TheoryInfo where
  name : Name
  language : LanguageInfo
  axioms : Array AxiomInfo := #[]
  parent : Option Name := none
  inherited : Nat := 0
  deriving Inhabited

initialize theories : SimplePersistentEnvExtension TheoryInfo (Array TheoryInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

def findTheory (name : Name) : CommandElabM TheoryInfo := do
  let name := name.eraseMacroScopes
  let resolved ← LeanPRA.Surface.resolveDeclaration?
    (LeanPRA.Surface.CoreEnvironment.getState (← getEnv)) (name ++ `isAxiom)
  match (theories.getState (← getEnv)).find? (fun T =>
      resolved.any (·.name == T.name ++ `isAxiom)) with
  | some T => pure T
  | none => throwError "unknown first-order theory `{name}`"

private def familyIndexArity (indices : Array (TSyntax ``folFamilyIndex)) :
    CommandElabM Nat := do
  let mut seen : List Name := []
  for index in indices do
    let `(folFamilyIndex| ($ns:ident* : Nat)) := index | throwUnsupportedSyntax
    for n in ns do
      let name := n.getId.eraseMacroScopes
      if seen.contains name then throwErrorAt n "duplicate index parameter `{name}`"
      seen := name :: seen
  return seen.length

def declareLanguage (name : Name) (entries : Array Syntax) (source : Syntax) :
    CommandElabM Unit := do
  let mut L : LanguageInfo := { name := (← getCurrNamespace) ++ name }
  let mut used : List Name := []
  for s in entries do
    let (n, k, isRelation, indexArity) ← match s with
      | `(folSymbol| constant $n:ident) => pure (n.getId.eraseMacroScopes, 0, false, 0)
      | `(folSymbol| function $n:ident of $k:num) =>
        pure (n.getId.eraseMacroScopes, k.getNat, false, 0)
      | `(folSymbol| relation $n:ident of $k:num) =>
        pure (n.getId.eraseMacroScopes, k.getNat, true, 0)
      | `(folSymbol| $n:ident $indices:folFamilyIndex* : constant) =>
        pure (n.getId.eraseMacroScopes, 0, false, ← familyIndexArity indices)
      | `(folSymbol| $n:ident $indices:folFamilyIndex* : function of $k:num) =>
        if k.getNat == 0 then throwErrorAt s "function families must have positive arity"
        pure (n.getId.eraseMacroScopes, k.getNat, false, ← familyIndexArity indices)
      | `(folSymbol| $n:ident $indices:folFamilyIndex* : relation of $k:num) =>
        pure (n.getId.eraseMacroScopes, k.getNat, true, ← familyIndexArity indices)
      | _ => throwError "unexpected symbol syntax {repr s}"
    if used.contains n then throwErrorAt s "duplicate symbol `{n}`"
    used := n :: used
    if isRelation then
      if k == 0 then throwErrorAt s "relation symbols must have positive arity"
      if indexArity == 0 then L := { L with relations := L.relations.push (n, k) }
      else L := { L with relationFamilies := L.relationFamilies.push ⟨n, k, indexArity⟩ }
    else if indexArity != 0 && k == 0 then
      L := { L with constantFamilies := L.constantFamilies.push ⟨n, 0, indexArity⟩ }
    else if indexArity != 0 then
      L := { L with functionFamilies := L.functionFamilies.push ⟨n, k, indexArity⟩ }
    else if k == 0 then L := { L with constants := L.constants.push n }
    else L := { L with functions := L.functions.push (n, k) }
  let body := applyDefinition `FOL.Language.make [numeral L.constants.size,
    sequenceCode (L.functions.toList.map (fun (_, k) => numeral (k - 1))),
    sequenceCode (L.relations.toList.map (fun (_, k) => numeral (k - 1))),
    numeral L.constantFamilies.size,
    sequenceCode (L.functionFamilies.toList.map (fun f => numeral (f.arity - 1))),
    sequenceCode (L.relationFamilies.toList.map (fun f => numeral (f.arity - 1)))]
  publishChecked (.function ⟨L.name ++ `language, [], 0, body⟩) source
  modifyEnv (languages.addEntry · L)

def declareTheory (name lang : Name) (parent : Option Name) (entries : Array Syntax)
    (source : Syntax) : CommandElabM Unit := do
  let L ← findLanguage lang
  let mut T : TheoryInfo := { name := (← getCurrNamespace) ++ name, language := L }
  if let some parent := parent then
    let P ← findTheory parent
    unless P.language.name == L.name do throwError "the parent theory uses a different language"
    T := { T with axioms := P.axioms, parent := some P.name, inherited := P.axioms.size }
  for s in entries do
    match s with
    | `(folAxiom| axiom $n:ident $ps:praParam* := $a:folFormula) =>
      let axiomName := n.getId.eraseMacroScopes
      if T.axioms.any (fun entry => entry.name == axiomName) then throwErrorAt n "duplicate axiom"
      let (_, parameters) ← declarationParameters ps
      let mut names : List Name := []
      for parameter in parameters do
        if names.contains parameter.name then throwErrorAt s "duplicate syntax parameter"
        names := parameter.name :: names
      for p in ps do
        let `(praParam| ($_:ident* : $type:praExpr)) := p | throwUnsupportedSyntax
        unless (syntaxParameterType? type).isSome do
          throwErrorAt p "an axiom parameter must have a term or formula type"
      let template ← parseFormula L [] a parameters.toList (useDefinitions := true)
      T := { T with axioms := T.axioms.push ⟨axiomName, parameters, template⟩ }
    | _ => throwUnsupportedSyntax
  for info in T.axioms do compileAxiom T.name L info source
  let body := (T.axioms.toList.drop T.inherited).foldr (fun info rest => applyDefinition `bor
    [applyDefinition (T.name ++ info.name ++ `isAxiom) [.bvar 0], rest]) (numeral 0)
  let body := if let some parent := T.parent then
    applyDefinition `bor [applyDefinition (parent ++ `isAxiom) [.bvar 0], body] else body
  publishChecked (.function ⟨T.name ++ `isAxiom, [], 1, .lam `A body⟩) source
  if let some parent := T.parent then
    let parentTest := applyDefinition (parent ++ `isAxiom) [.bvar 0]
    let premise := Predicate.equal parentTest (numeral 1)
    let conclusion := Predicate.equal (applyDefinition (T.name ++ `isAxiom) [.bvar 0]) (numeral 1)
    let branches := (getAppFnArgs body).2
    let proof := applyTheorem `bor_eq_one_of_left_eq_one branches [] [.hyp 0]
    publishChecked (.theoremE ⟨T.name ++ `isAxiom_of_parent, [],
      .all (.lam `A (.imp premise conclusion)),
      .forallIntro `A (.lam `A (.imp premise conclusion)) (.impIntro `h premise proof)⟩) source
  modifyEnv (theories.addEntry · T)

@[command_elab LeanPRA.Surface.praEntry]
def elaborateFOLDeclarations : CommandElab := fun stx => do
  let entry := stx[0]
  match entry with
  | `(praDecl| fol_language $n:ident where $ss:folSymbolSeq) =>
    declareLanguage n.getId.eraseMacroScopes ss.raw[0].getSepArgs entry
  | `(praDecl| fol_theory $n:ident over $L:ident $[extends $P:ident]?
      where $ss:folAxiomSeq) =>
    declareTheory n.getId.eraseMacroScopes L.getId.eraseMacroScopes
      (P.map (·.getId.eraseMacroScopes)) ss.raw[0].getSepArgs entry
  | _ => throwUnsupportedSyntax

end LeanPRA.Library.FOL.DSL
