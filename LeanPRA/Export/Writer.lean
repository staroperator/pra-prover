module

public meta import LeanPRA.Surface.Environment
public meta import LeanPRA.Export.Specification

/-!
# PRA specifications and object files

`run` reads a module's own elaborated Core declarations from Lean's persistent environment and
writes its specification and object file. Specifications contain definition bodies and theorem
statements; object files also contain theorem proofs. Builtins are exported as ordinary checked
declarations.
-/

open Lean LeanPRA LeanPRA.Core LeanPRA.Surface

meta section

namespace LeanPRA.Export

private inductive S where
  | atom : String → S
  | string : String → S
  | num : Nat → S
  | list : List S → S

private def node (tag : String) (xs : List S := []) : S := .list (.atom tag :: xs)

private def nameParts : Name → List S
  | .anonymous => []
  | .str n s => nameParts n ++ [.string s]
  | .num n i => nameParts n ++ [.num i]

private def name (n : Name) : S := node "name" (nameParts n)

private def binder (b : Core.BinderInfo) : S :=
  node "binder" [name b.name, .num (if b.isImplicit then 1 else 0)]

private def sig (s : PredicateSignature) : S :=
  node "sig" [.num s.arity, .atom (if s.sort == .qf then "qf" else "prop")]

private def params (ps : List Parameter) : S := .list (ps.map fun
  | .function b k => node "funparam" [binder b, .num k]
  | .predicate b s => node "predparam" [binder b, sig s])

private def term : Core.Term → S
  | .bvar i => node "tvar" [.num i]
  | .parameter i => node "tparam" [.num i]
  | .zero => node "zero"
  | .succ => node "succ"
  | .lam n b => node "tlam" [name n, term b]
  | .app f a => node "tapp" [term f, term a]
  | .letE n v b => node "tlet" [name n, term v, term b]
  | .primrec b s n => node "rec" [term b, term s, term n]
  | .definition n fs => node "tdef" [name n, .list (fs.map term)]

private def pred : Predicate → S
  | .false => node "false"
  | .true => node "true"
  | .equal a b => node "eq" [term a, term b]
  | .imp a b => node "imp" [pred a, pred b]
  | .and a b => node "and" [pred a, pred b]
  | .or a b => node "or" [pred a, pred b]
  | .all p => node "all" [pred p]
  | .ex p => node "ex" [pred p]
  | .parameter i => node "pparam" [.num i]
  | .lam b p => node "plam" [binder b, pred p]
  | .app p a => node "papp" [pred p, term a]
  | .letTerm n v b => node "pletTerm" [name n, term v, pred b]
  | .letPredicate n v b => node "pletPred" [name n, pred v, pred b]
  | .definition n fs ps => node "pdef" [name n, .list (fs.map term), .list (ps.map pred)]

private def proof : Proof → S
  | .hyp i => node "hyp" [.num i]
  | .trueIntro => node "trueIntro"
  | .theoremE n fs ps => node "thm" [name n, .list (fs.map term), .list (ps.map pred)]
  | .impIntro n a b => node "impIntro" [name n, pred a, proof b]
  | .impElim f a => node "impElim" [proof f, proof a]
  | .andIntro a b => node "andIntro" [proof a, proof b]
  | .andLeft p => node "andLeft" [proof p]
  | .andRight p => node "andRight" [proof p]
  | .orLeft p h => node "orLeft" [pred p, proof h]
  | .orRight p h => node "orRight" [pred p, proof h]
  | .orElim n m t s a b => node "orElim" [name n, name m, pred t, proof s, proof a, proof b]
  | .falseElim t p => node "falseElim" [pred t, proof p]
  | .forallIntro n m b => node "forallIntro" [name n, pred m, proof b]
  | .forallElim p t => node "forallElim" [proof p, term t]
  | .existsIntro m w p => node "existsIntro" [pred m, term w, proof p]
  | .existsElim n h t s b => node "existsElim" [name n, name h, pred t, proof s, proof b]
  | .letE n t v b => node "hlet" [name n, pred t, proof v, proof b]
  | .letTerm n v b => node "hletTerm" [name n, term v, proof b]
  | .letPredicate n v b => node "hletPred" [name n, pred v, proof b]
  | .ascribe t p => node "ascribe" [pred t, proof p]
  | .eqRefl t => node "refl" [term t]
  | .eqSubst m e p => node "subst" [pred m, proof e, proof p]
  | .succNeZero t => node "succNeZero" [term t]
  | .succInj p => node "succInj" [proof p]
  | .lem p => node "lem" [pred p]
  | .induction n h m b s t => node "ind" [name n, name h, pred m, proof b, proof s, term t]

/-- Encode a declaration, including a theorem's proof, as an object record. -/
private def encodeDeclaration : Core.Declaration → S
  | .function d =>
    node "function" [name d.name, params d.parameterSignature, .num d.arity, term d.body]
  | .predicate d =>
    node "predicate" [name d.name, params d.parameters, sig d.signature, pred d.body]
  | .theoremE d => node "theorem"
      [name d.name, params d.parameters, pred d.type, proof d.body]

private def tags := #["name", "binder", "sig", "qf", "prop", "funparam", "predparam",
  "tvar", "tparam", "zero", "succ", "tlam", "tapp", "tlet", "rec", "tdef", "false", "true",
  "eq", "imp", "and", "or", "all", "ex", "pparam", "plam", "papp", "pletTerm", "pletPred",
  "pdef", "hyp", "trueIntro", "thm", "impIntro", "impElim", "andIntro", "andLeft", "andRight",
  "orLeft", "orRight", "orElim", "falseElim", "forallIntro", "forallElim", "existsIntro",
  "existsElim", "hlet", "hletTerm", "hletPred", "ascribe", "refl", "subst", "succNeZero",
  "succInj", "lem", "ind", "function", "predicate", "theorem"]

private partial def varint (n : Nat) (out : ByteArray) : ByteArray :=
  if n < 128 then out.push n.toUInt8
  else varint (n / 128) (out.push ((n % 128 + 128).toUInt8))

private partial def encodeObject (s : S) (out : ByteArray := {}) : ByteArray :=
  match s with
  | .atom a => out.push ((tags.toList.idxOf a + 16).toUInt8)
  | .string a => (varint a.utf8ByteSize (out.push 1)) ++ a.toUTF8
  | .num n => varint n (out.push 2)
  | .list xs => xs.foldl (fun b x => encodeObject x b) (varint xs.length (out.push 0))

private def writeModule (dir : System.FilePath) (owner : Name)
    (decls : Array Core.Declaration) : IO Unit := do
  let specPath := modToFilePath dir owner "pra"
  let objectPath := modToFilePath dir owner "prao"
  if decls.isEmpty then
    for path in [specPath, objectPath] do
      if ← path.pathExists then IO.FS.removeFile path
  else
    if let some parent := specPath.parent then IO.FS.createDirAll parent
    let specTemporary := specPath.addExtension "tmp"
    let objectTemporary := objectPath.addExtension "tmp"
    do
      let spec ← IO.FS.Handle.mk specTemporary .write
      let object ← IO.FS.Handle.mk objectTemporary .write
      object.write "PRAO".toUTF8
      for d in decls do
        spec.putStrLn ((Specification.declaration d).pretty 100)
        spec.putStrLn ""
        let bytes := encodeObject (encodeDeclaration d)
        object.write (varint bytes.size {})
        object.write bytes
    IO.FS.rename specTemporary specPath
    IO.FS.rename objectTemporary objectPath

private unsafe def moduleDeclarations (owner : Name) : IO (Array Core.Declaration) := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := owner }] {} (loadExts := false)
  let mut declarations := #[]
  for i in [:env.header.modules.size] do
    for entry in CoreEnvironment.getModuleEntries env i do
      if entry.owner == owner then declarations := declarations ++ entry.declarations
  return declarations

/-- Write a module's specification and object file, or the builtin pair, and record whether a pair
was written. Lake schedules imported modules separately, including modules reached through private
imports. -/
public unsafe def run (args : List String) : IO Unit := do
  let (directory, result, owner, declarations) ← match args with
    | ["module", directory, result, name] => do
      let owner := name.toName
      pure (directory, result, owner, ← moduleDeclarations owner)
    | ["builtins", directory, result] =>
      pure (directory, result, `PRA.Builtins, builtinDeclarations.toArray)
    | _ => throw (IO.userError
        "usage: export module DIRECTORY RESULT MODULE | export builtins DIRECTORY RESULT")
  writeModule directory owner declarations
  let result := System.FilePath.mk result
  if let some parent := result.parent then IO.FS.createDirAll parent
  let temporary := result.addExtension "tmp"
  IO.FS.writeFile temporary (if declarations.isEmpty then "" else owner.toString ++ "\n")
  IO.FS.rename temporary result

end LeanPRA.Export
