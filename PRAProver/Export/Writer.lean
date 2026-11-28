module

public meta import PRAProver.Surface.Environment
public meta import PRAProver.Export.Specification

/-!
# PRA specifications and object files

`run` reads a module's own elaborated Core declarations from Lean's persistent environment and
writes its specification and object file. Specifications contain definition bodies and theorem
statements; object files also contain theorem proofs. Primitive constructions appear directly
in the exported expressions.
-/

open Lean PRAProver PRAProver.Core PRAProver.Surface

meta section

namespace PRAProver.Export

private partial def varint (n : Nat) (out : ByteArray) : ByteArray :=
  if n < 128 then out.push n.toUInt8
  else varint (n / 128) (out.push ((n % 128 + 128).toUInt8))

-- The object format assigns consecutive bytes starting at 16 in this order.
private inductive Atom where
  | name | binder | sig | qf | prop | funparam | predparam
  | tvar | tparam | zero | succ | tlam | tapp | tlet | recursor | tdef
  | falseE | trueE | eq | imp | and | or | all | ex | pparam | plam | papp | pletTerm
  | pletPred | pdef | hyp | trueIntro | thm | impIntro | impElim | andIntro | andLeft | andRight
  | orLeft | orRight | orElim | falseElim | forallIntro | forallElim | existsIntro | existsElim
  | hlet | hletTerm | hletPred | ascribe
  | refl | subst | succNeZero | succInj | lem | ind | function | predicate | theoremE

private def Atom.byte (atom : Atom) : UInt8 := (16 + atom.ctorIdx).toUInt8

private abbrev Put := ByteArray → ByteArray

private def listHead (n : Nat) (buf : ByteArray) : ByteArray := varint n (buf.push 0)

private def node (tag : Atom) (n : Nat) (buf : ByteArray) : ByteArray :=
  (listHead (n + 1) buf).push tag.byte

private def num (n : Nat) (buf : ByteArray) : ByteArray := varint n (buf.push 2)

-- Count the components on the way to the root so the list length precedes their bytes.
private def nameParts : Name → Nat → ByteArray → ByteArray
  | .anonymous, count, buf => node .name count buf
  | .str n s, count, buf =>
    (varint s.utf8ByteSize ((nameParts n (count + 1) buf).push 1)) ++ s.toUTF8
  | .num n i, count, buf => num i (nameParts n (count + 1) buf)

private def name (n : Name) (buf : ByteArray) : ByteArray := nameParts n 0 buf

private def binder (b : Core.BinderInfo) (buf : ByteArray) : ByteArray :=
  node .binder 2 buf |> name b.name |> num (if b.isImplicit then 1 else 0)

private def sig (s : PredicateSignature) (buf : ByteArray) : ByteArray :=
  (node .sig 2 buf |> num s.arity).push (if s.sort == .qf then Atom.qf.byte else Atom.prop.byte)

private def list (put : α → Put) (xs : List α) (buf : ByteArray) : ByteArray :=
  xs.foldl (fun acc x => put x acc) (listHead xs.length buf)

private def params (ps : List Parameter) : Put := list (fun
  | .function b k, buf => node .funparam 2 buf |> binder b |> num k
  | .predicate b s, buf => node .predparam 2 buf |> binder b |> sig s) ps

private partial def term : Core.Term → Put
  | .bvar i, buf => node .tvar 1 buf |> num i
  | .parameter i, buf => node .tparam 1 buf |> num i
  | .zero, buf => node .zero 0 buf
  | .succ, buf => node .succ 0 buf
  | .lam n b, buf => node .tlam 2 buf |> name n |> term b
  | .app f a, buf => node .tapp 2 buf |> term f |> term a
  | .letE n v b, buf => node .tlet 3 buf |> name n |> term v |> term b
  | .primrec b s, buf => node .recursor 2 buf |> term b |> term s
  | .definition n fs, buf => node .tdef 2 buf |> name n |> list term fs

private partial def pred : Predicate → Put
  | .false, buf => node .falseE 0 buf
  | .true, buf => node .trueE 0 buf
  | .equal a b, buf => node .eq 2 buf |> term a |> term b
  | .imp a b, buf => node .imp 2 buf |> pred a |> pred b
  | .and a b, buf => node .and 2 buf |> pred a |> pred b
  | .or a b, buf => node .or 2 buf |> pred a |> pred b
  | .all p, buf => node .all 1 buf |> pred p
  | .ex p, buf => node .ex 1 buf |> pred p
  | .parameter i, buf => node .pparam 1 buf |> num i
  | .lam b p, buf => node .plam 2 buf |> binder b |> pred p
  | .app p a, buf => node .papp 2 buf |> pred p |> term a
  | .letTerm n v b, buf => node .pletTerm 3 buf |> name n |> term v |> pred b
  | .letPredicate n v b, buf => node .pletPred 3 buf |> name n |> pred v |> pred b
  | .definition n fs ps, buf => node .pdef 3 buf |> name n |> list term fs |> list pred ps

private partial def proof : Proof → Put
  | .hyp i, buf => node .hyp 1 buf |> num i
  | .trueIntro, buf => node .trueIntro 0 buf
  | .theoremE n fs ps, buf => node .thm 3 buf |> name n |> list term fs |> list pred ps
  | .impIntro n a b, buf => node .impIntro 3 buf |> name n |> pred a |> proof b
  | .impElim f a, buf => node .impElim 2 buf |> proof f |> proof a
  | .andIntro a b, buf => node .andIntro 2 buf |> proof a |> proof b
  | .andLeft a b, buf => node .andLeft 2 buf |> pred a |> pred b
  | .andRight a b, buf => node .andRight 2 buf |> pred a |> pred b
  | .orLeft a b, buf => node .orLeft 2 buf |> pred a |> pred b
  | .orRight a b, buf => node .orRight 2 buf |> pred a |> pred b
  | .orElim a b c, buf => node .orElim 3 buf |> pred a |> pred b |> pred c
  | .falseElim a, buf => node .falseElim 1 buf |> pred a
  | .forallIntro n m b, buf => node .forallIntro 3 buf |> name n |> pred m |> proof b
  | .forallElim p t, buf => node .forallElim 2 buf |> proof p |> term t
  | .existsIntro m w p, buf => node .existsIntro 3 buf |> pred m |> term w |> proof p
  | .existsElim a b, buf => node .existsElim 2 buf |> pred a |> pred b
  | .letE n t v b, buf => node .hlet 4 buf |> name n |> pred t |> proof v |> proof b
  | .letTerm n v b, buf => node .hletTerm 3 buf |> name n |> term v |> proof b
  | .letPredicate n v b, buf => node .hletPred 3 buf |> name n |> pred v |> proof b
  | .ascribe t p, buf => node .ascribe 2 buf |> pred t |> proof p
  | .eqRefl, buf => node .refl 0 buf
  | .eqSubst a, buf => node .subst 1 buf |> pred a
  | .succNeZero, buf => node .succNeZero 0 buf
  | .succInj, buf => node .succInj 0 buf
  | .lem p, buf => node .lem 1 buf |> pred p
  | .induction a, buf => node .ind 1 buf |> pred a

/-- Encode a declaration, including a theorem's proof, as an object record. -/
private def encodeDeclaration : Core.Declaration → Put
  | .function d, buf =>
    node .function 4 buf |> name d.name |> params d.parameterSignature |> num d.arity |> term d.body
  | .predicate d, buf =>
    node .predicate 4 buf |> name d.name |> params d.parameters |> sig d.signature |> pred d.body
  | .theoremE d, buf =>
    node .theoremE 4 buf |> name d.name |> params d.parameters |> pred d.type |> proof d.body

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
        let bytes := encodeDeclaration d {}
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

/-- Write a module's specification and object file, and record whether a pair was written.
Lake schedules imported modules separately, including modules reached through private imports. -/
public unsafe def run (args : List String) : IO Unit := do
  let (directory, result, owner, declarations) ← match args with
    | ["module", directory, result, name] => do
      let owner := name.toName
      pure (directory, result, owner, ← moduleDeclarations owner)
    | _ => throw (IO.userError
        "usage: export module DIRECTORY RESULT MODULE")
  writeModule directory owner declarations
  let result := System.FilePath.mk result
  if let some parent := result.parent then IO.FS.createDirAll parent
  let temporary := result.addExtension "tmp"
  IO.FS.writeFile temporary (if declarations.isEmpty then "" else owner.toString ++ "\n")
  IO.FS.rename temporary result

end PRAProver.Export
