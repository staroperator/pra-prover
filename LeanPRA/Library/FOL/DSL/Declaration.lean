module

public meta import LeanPRA.Library.Tactic.Construction

/-!
# FOL declaration support

Language metadata records source names and arities for quotation elaboration.
The mathematical language is an ordinary numerical PRA definition.

- `LanguageInfo` stores the source names and arities used by the frontend.
- `findLanguage` resolves a language name in the current namespace.
- `languageTerm` refers to its numerical PRA definition.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL

open LeanPRA.Library.Tactic.Construction

open Lean hiding Term

open Lean.Elab.Command

open LeanPRA

open Core

structure LanguageInfo where
  name : Name
  constants : Array Name := #[]
  functions : Array (Name × Nat) := #[]
  relations : Array (Name × Nat) := #[]
  deriving Inhabited

initialize languages : SimplePersistentEnvExtension LanguageInfo (Array LanguageInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

def languageTerm (L : LanguageInfo) : Term := applyDefinition (L.name ++ `language)

def findLanguage (name : Name) : CommandElabM LanguageInfo := do
  let name := name.eraseMacroScopes
  let resolved ← Surface.resolveDeclaration? (Surface.CoreEnvironment.getState (← getEnv))
    (name ++ `language)
  let entries := languages.getState (← getEnv)
  match entries.find? (fun L => resolved.any (·.name == L.name ++ `language)) with
  | some L => pure L
  | none => throwError "unknown first-order language `{name}`"

end LeanPRA.Library.FOL.DSL
