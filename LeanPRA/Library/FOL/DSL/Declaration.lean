module

public meta import LeanPRA.Library.Tactic.Construction

/-!
# FOL declaration support

Language metadata records source names and arities for quotation elaboration.
The mathematical language is an ordinary numerical PRA definition.

- `FamilyInfo` stores a family name, object arity, and number of index parameters.
- `LanguageInfo` stores the symbols and families used by the frontend.
- `findLanguage` resolves a language name in the current namespace.
- `languageTerm` refers to its numerical PRA definition.
- `LanguageInfo.symbolTheorem` names the theorems that `fol_language` proves about a symbol.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL

open LeanPRA.Library.Tactic.Construction

open Lean hiding Term

open Lean.Elab.Command

open LeanPRA

open Core

structure FamilyInfo where
  name : Name
  arity : Nat
  indexArity : Nat
  deriving Inhabited

structure LanguageInfo where
  name : Name
  constants : Array Name := #[]
  functions : Array (Name × Nat) := #[]
  relations : Array (Name × Nat) := #[]
  constantFamilies : Array FamilyInfo := #[]
  functionFamilies : Array FamilyInfo := #[]
  relationFamilies : Array FamilyInfo := #[]
  deriving Inhabited

initialize languages : SimplePersistentEnvExtension LanguageInfo (Array LanguageInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

/-- Resolve a family and check the numbers of indices and object arguments. -/
def familyIndex (families : Array FamilyInfo) (name : Name) (indices arity : Nat) :
    CommandElabM Nat := do
  let some i := families.findIdx? (·.name == name) | throwError "unknown symbol family `{name}`"
  let family := families[i]!
  unless indices == family.indexArity do
    throwError "symbol family `{name}` expects {family.indexArity} indices, got {indices}"
  unless arity == family.arity do
    throwError "symbol family `{name}` expects {family.arity} term arguments, got {arity}"
  return i

def languageTerm (L : LanguageInfo) : Term := applyDefinition (L.name ++ `language)

/-- The theorems that `fol_language` proves about a symbol or family live next to the
language, named `isConstant_c`, `isFunction_f`, `isRelation_R`, `f_arity`, and `f_lt`. -/
def LanguageInfo.symbolTheorem (L : LanguageInfo) (label : String) (symbol : Name)
    (tail : String := "") : Name :=
  L.name ++ Name.mkSimple (label ++ symbol.toString ++ tail)

def findLanguage (name : Name) : CommandElabM LanguageInfo := do
  let name := name.eraseMacroScopes
  let resolved ← Surface.resolveDeclaration? (Surface.CoreEnvironment.getState (← getEnv))
    (name ++ `language)
  let entries := languages.getState (← getEnv)
  match entries.find? (fun L => resolved.any (·.name == L.name ++ `language)) with
  | some L => pure L
  | none => throwError "unknown first-order language `{name}`"

end LeanPRA.Library.FOL.DSL
