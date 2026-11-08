module

public meta import Lean
public meta import LeanPRA.Core.Syntax

/-!
# Readable PRA specifications

`declaration` prints a definition or theorem statement with named binders and explicit Core
operations. The output preserves names, binder visibility, schema arguments, and syntax trees so
the specification parser can recover the declaration.
-/

meta section

namespace LeanPRA.Export.Specification

open Lean Core

private def reserved := ["def", "theorem", "Nat", "Prop", "QFProp", "fun", "let", "check_term",
  "check_predicate", "True", "False", "Eq", "And", "Or", "Imp", "Forall", "Exists", "succ",
  "primrec", "local", "fnarg", "predarg", "_"]

private def component (s : String) : String :=
  let identifier := s.toList.head?.any (fun c => c.isAlpha || c == '_') &&
    s.toList.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_' || c == '\''))
  if identifier && !reserved.contains s then s else (Json.str s).compress

private def name : Name → String
  | .anonymous => "_"
  | .str .anonymous s => component s
  | .num .anonymous n => s!"#{n}"
  | .str p s => name p ++ "." ++ component s
  | .num p n => name p ++ s!".#{n}"

private structure Names where
  locals : List Name := []
  functions : List Name := []
  predicates : List Name := []

private def indexed (names : List Name) (i : Nat) (fallback : String)
    (shadowed : List Name := []) : Format :=
  match names[i]? with
  | some n =>
    if !n.isAnonymous && names.idxOf n == i && (names.filter (· == n)).length == 1 &&
        !shadowed.contains n then name n
    else s!"{fallback}[{i}]"
  | none => s!"{fallback}[{i}]"

private def parens (body : Format) : Format :=
  Format.group ("(" ++ Format.nest 2 body ++ ")")

private def application (head : Format) (arguments : List Format) : Format :=
  parens (head ++ Format.line ++ Format.joinSep arguments Format.line)

private def actuals (arguments : List Format) : Format :=
  Format.group ("[" ++ Format.nest 2 (Format.joinSep arguments ("," ++ Format.line)) ++ "]")

private def typ (arity : Nat) (result : String := "Nat") : Format :=
  Format.group (Format.joinSep (List.replicate arity ("Nat" : Format) ++ [Format.text result])
    (" ->" ++ Format.line))

private def sig (s : PredicateSignature) : Format :=
  typ s.arity (if s.sort == .qf then "QFProp" else "Prop")

private def binder (n : Name) (type : Format) (implicit : Bool := false) : Format :=
  (if implicit then "{" else "(") ++ name n ++ " : " ++ type ++
    (if implicit then "}" else ")")

private def termArguments : Core.Term → List Core.Term → Core.Term × List Core.Term
  | .app f a, args => termArguments f (a :: args)
  | f, args => (f, args)

private partial def term (names : Names) : Core.Term → Format
  | .bvar i => indexed names.locals i "local"
  | .parameter i => indexed names.functions i "fnarg" (names.locals ++ names.predicates)
  | .zero => "0"
  | .succ => "succ"
  | .lam n body => parens ("fun " ++ binder n "Nat" ++ " =>" ++ Format.line ++
      term { names with locals := n :: names.locals } body)
  | .app f a =>
    let (head, args) := termArguments f [a]
    application (term names head) (args.map (term names))
  | .letE n value body => parens ("let " ++ name n ++ " := " ++ term names value ++ ";" ++
      Format.line ++ term { names with locals := n :: names.locals } body)
  | .primrec b s n => application "primrec" ([b, s, n].map (term names))
  | .definition n fs => "@" ++ name n ++
      (if fs.isEmpty then Format.nil else actuals (fs.map (term names)))

private def predicateArguments : Predicate → List Core.Term → Predicate × List Core.Term
  | .app p a, args => predicateArguments p (a :: args)
  | p, args => (p, args)

private partial def predicate (names : Names) : Predicate → Format
  | .false => "False"
  | .true => "True"
  | .equal a b => application "Eq" ([a, b].map (term names))
  | .imp a b => application "Imp" ([a, b].map (predicate names))
  | .and a b => application "And" ([a, b].map (predicate names))
  | .or a b => application "Or" ([a, b].map (predicate names))
  | .all p => application "Forall" [predicate names p]
  | .ex p => application "Exists" [predicate names p]
  | .parameter i => indexed names.predicates i "predarg" (names.locals ++ names.functions)
  | .lam b body => parens ("fun " ++ binder b.name "Nat" b.isImplicit ++ " =>" ++ Format.line ++
      predicate { names with locals := b.name :: names.locals } body)
  | .app p a =>
    let (head, args) := predicateArguments p [a]
    application (predicate names head) (args.map (term names))
  | .letTerm n value body => parens ("check_term " ++ name n ++ " := " ++ term names value ++
      ";" ++ Format.line ++ predicate names body)
  | .letPredicate n value body => parens ("check_predicate " ++ name n ++ " := " ++
      predicate names value ++ ";" ++ Format.line ++ predicate names body)
  | .definition n fs ps => "@" ++ name n ++
      (if fs.isEmpty && ps.isEmpty then Format.nil else actuals (fs.map (term names))) ++
      (if ps.isEmpty then Format.nil else actuals (ps.map (predicate names)))

private def parameters (ps : List Parameter) : Names × Format := Id.run do
  let mut names : Names := {}
  let mut result := Format.nil
  for p in ps do
    match p with
    | .function b k =>
      names := { names with functions := names.functions ++ [b.name] }
      result := result ++ Format.line ++ binder b.name (typ k) b.isImplicit
    | .predicate b s =>
      names := { names with predicates := names.predicates ++ [b.name] }
      result := result ++ Format.line ++ binder b.name (sig s) b.isImplicit
  return (names, result)

/-- Print a definition or a theorem's parameters and statement, preserving its Core syntax. -/
public def declaration (d : Core.Declaration) : Format :=
  let ps := match d with
    | .function f => f.parameterSignature
    | .predicate p => p.parameters
    | .theoremE t => t.parameters
  let (names, ps) := parameters ps
  let start (keyword : String) := Format.group (keyword ++ " " ++ name d.name ++
    Format.nest 2 ps ++ " :")
  match d with
  | .function f => Format.group (start "def" ++ " " ++ typ f.arity ++ " :=" ++
      Format.nest 2 (Format.line ++ term names f.body) ++ ";")
  | .predicate p => Format.group (start "def" ++ " " ++ sig p.signature ++ " :=" ++
      Format.nest 2 (Format.line ++ predicate names p.body) ++ ";")
  | .theoremE t => Format.group (start "theorem" ++
      Format.nest 2 (Format.line ++ predicate names t.type) ++ ";")

end LeanPRA.Export.Specification
