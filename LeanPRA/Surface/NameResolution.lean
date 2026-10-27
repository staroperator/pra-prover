module

public meta import LeanPRA.Surface.Environment
public meta import LeanPRA.Surface.Builtins

/-!
# PRA names in Lean scopes

Name resolution and unqualification in the current Lean namespace and `open` scope:

- `resolveDeclarationNames` finds matching declarations in enclosing and opened namespaces.
- `resolveDeclaration?` returns the unique match or throws an ambiguity error.
- `relativeName` picks a short unambiguous suffix for printing.
-/

public meta section

namespace LeanPRA.Surface

open Lean Elab Command

private partial def enclosingName? (environment : Core.Environment) (ns name : Name) :
    Option Name :=
  if ns.isAnonymous then none
  else if (environment.lookup (ns ++ name)).isSome then some (ns ++ name)
  else enclosingName? environment ns.getPrefix name

/-- Resolve `name` in `environment`, checking enclosing namespaces before opened namespaces. -/
def resolveDeclarationNames (environment : Core.Environment) (ns : Name)
    (opens : List OpenDecl) (name : Name) : List Name := Id.run do
  if name.getRoot == `_root_ then
    let absolute := name.replacePrefix `_root_ .anonymous
    return if (environment.lookup absolute).isSome then [absolute] else []
  if let some name := enclosingName? environment ns name then return [name]
  let mut result := if (environment.lookup name).isSome then [name] else []
  for opened in opens do
    let candidate := match opened with
      | .simple ns except => if except.contains name then none else some (ns ++ name)
      | .explicit alias target =>
        if alias.isPrefixOf name then some (name.replacePrefix alias target) else none
    if let some candidate := candidate then
      if (environment.lookup candidate).isSome then result := result ++ [candidate]
  return result.eraseDups

/-- Resolve `name` in the current scope, throwing an error if multiple declarations match. -/
def resolveDeclaration? (environment : Core.Environment) (name : Name) :
    CommandElabM (Option Core.Declaration) := do
  match resolveDeclarationNames environment (← getCurrNamespace) (← getOpenDecls) name with
  | [] => return none
  | [name] => return environment.lookup name
  | names => throwError "ambiguous PRA name `{name}`; candidates: {names}"

/-- Shortest suffix of `name` that resolves uniquely without colliding with local names. -/
def relativeName (name : Name) (locals : List Name := []) : CommandElabM Name := do
  let environment := CoreEnvironment.getState (← getEnv)
  let ns ← getCurrNamespace
  let opens ← getOpenDecls
  let fullNames := pp.fullNames.get (← getOptions)
  let mut candidate := Name.anonymous
  for part in name.componentsRev do
    candidate := Name.appendCore part candidate
    if fullNames && candidate != name then continue
    if !locals.contains candidate &&
        resolveDeclarationNames environment ns opens candidate == [name] then
      return candidate
  return `_root_ ++ name

end LeanPRA.Surface
