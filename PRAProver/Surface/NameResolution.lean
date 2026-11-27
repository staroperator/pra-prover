module

public meta import PRAProver.Surface.Environment
public meta import PRAProver.Surface.Primitive

/-!
# PRA names in Lean scopes

Name resolution and unqualification in the current Lean namespace and `open` scope:

- `lookupSignature` looks up the interface of a primitive or a checked declaration.
- `resolveDeclarationNames` finds matching declarations in enclosing and opened namespaces.
- `resolveDeclaration?` and `resolveSignature?` return the unique match or throw an ambiguity error.
- `relativeName` picks a short unambiguous suffix for printing.
-/

public meta section

namespace PRAProver.Surface

open Lean Elab Command

/-- Look up the interface of a primitive or a checked definition. -/
def lookupSignature (environment : Core.Environment) (name : Name) :
    Option DeclarationSignature :=
  (environment.lookup name).map declarationSignature <|>
    (primitiveDeclaration? name).map (·.signature)

private partial def enclosingName? (environment : Core.Environment) (ns name : Name) :
    Option Name :=
  if ns.isAnonymous then none
  else if (lookupSignature environment (ns ++ name)).isSome then some (ns ++ name)
  else enclosingName? environment ns.getPrefix name

/-- Resolve `name` in `environment`. Enclosing namespaces take precedence. A primitive
at the root is the fallback when no declaration matches. -/
def resolveDeclarationNames (environment : Core.Environment) (ns : Name)
    (opens : List OpenDecl) (name : Name) : List Name := Id.run do
  if name.getRoot == `_root_ then
    let absolute := name.replacePrefix `_root_ .anonymous
    return if (lookupSignature environment absolute).isSome then [absolute] else []
  if let some name := enclosingName? environment ns name then return [name]
  let mut result := if (environment.lookup name).isSome then [name] else []
  for opened in opens do
    let candidate := match opened with
      | .simple ns except => if except.contains name then none else some (ns ++ name)
      | .explicit alias target =>
        if alias.isPrefixOf name then some (name.replacePrefix alias target) else none
    if let some candidate := candidate then
      if (lookupSignature environment candidate).isSome then result := result ++ [candidate]
  if result.isEmpty && (primitiveDeclaration? name).isSome then return [name]
  return result.eraseDups

/-- Resolve `name` in the current scope, throwing an error if multiple declarations match. -/
def resolveDeclaration? (environment : Core.Environment) (name : Name) :
    CommandElabM (Option Core.Declaration) := do
  match resolveDeclarationNames environment (← getCurrNamespace) (← getOpenDecls) name with
  | [] => return none
  | [name] => return environment.lookup name
  | names => throwError "ambiguous PRA name `{name}`; candidates: {names}"

/-- Resolve a primitive or definition signature in the current namespace and open scope. -/
def resolveSignature? (environment : Core.Environment) (name : Name) :
    CommandElabM (Option DeclarationSignature) := do
  match resolveDeclarationNames environment (← getCurrNamespace) (← getOpenDecls) name with
  | [] => return none
  | [name] => return lookupSignature environment name
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

end PRAProver.Surface
