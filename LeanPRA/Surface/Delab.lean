module

public meta import LeanPRA.Surface.Syntax
public meta import LeanPRA.Surface.NameResolution

/-!
# Reconstructing PRA syntax from checked expressions

Delaboration from Core expressions to `praExpr` and `praDecl` syntax:

- `delabTerm` delaborates a term.
- `delabPredicate` delaborates a predicate or formula.
- `delabProof` delaborates a proof expression.
- `delabDeclaration` delaborates a full declaration.
- `delabSignature` formats a declaration signature for `#check` and hover.

Binder names come from Core hints when available, disambiguated against names in scope.
-/

public meta section

namespace LeanPRA.Surface

open Lean Elab Command
open Core (Predicate Proof)

/-- Binder names and local let-alias values in scope during delaboration, ordered to match
`Core.Context` indices. -/
structure Names where
  locals : List Name := []
  functions : List Name := []
  predicates : List Name := []
  proofs : List Name := []
  termAliases : List (Name × Core.Term) := []
  predicateAliases : List (Name × Predicate) := []
  deriving Inhabited

/-- All local, parameter, hypothesis, and alias names currently in scope. -/
def Names.used (names : Names) : List Name :=
  names.locals ++ names.functions ++ names.predicates ++ names.proofs ++
    names.termAliases.map (·.1) ++ names.predicateAliases.map (·.1)

/-- Push a local variable name `n` and shift free variable indices in stored aliases. -/
def Names.pushLocal (names : Names) (n : Name) : Names :=
  { names with
    locals := n :: names.locals
    termAliases := names.termAliases.map fun (n, t) => (n, t.shift)
    predicateAliases := names.predicateAliases.map fun (n, p) => (n, p.shift) }

/-- Pretty-print `stx` in syntax `category`. -/
def formatSyntax (category : Name) (stx : Syntax) : CommandElabM Format :=
  let stx := stx.rewriteBottomUp fun
    | .ident info raw name _ => .ident info raw name.eraseMacroScopes []
    | other => other
  liftCoreM (PrettyPrinter.ppCategory category stx)

private def fresh (stem : String) (names : List Name) : Name :=
  let index := ((List.range (names.length + 1)).find? fun i =>
    !names.contains (.mkSimple s!"{stem}{i}")).getD names.length
  .mkSimple s!"{stem}{index}"

/-- Pick an unused binder name, starting from `hint` or `stem`. -/
def Names.freshName (names : Names) (stem : String) (hint : Name := .anonymous) : Name :=
  let suggestion := if hint.isAnonymous then fresh stem names.used else hint.eraseMacroScopes
  let used := names.used ++ builtinNames.map (·.1)
  let context := (used.zipIdx).foldl (fun (ctx : LocalContext) (name, i) =>
    ctx.mkLocalDecl ⟨.num `_praDisplay i⟩ name (mkConst ``Nat)) {}
  context.getUnusedName suggestion

private def identExpr (name : Name) : CommandElabM (TSyntax `praExpr) :=
  `(praExpr| $(mkIdent name):ident)

private def globalExpr (names : Names) (name : Name) : CommandElabM (TSyntax `praExpr) := do
  identExpr (← relativeName name names.used)

private def numeral (n : Nat) : CommandElabM (TSyntax `praExpr) :=
  `(praExpr| $(Syntax.mkNumLit (toString n)):num)

private def applyExpr (f a : TSyntax `praExpr) : CommandElabM (TSyntax `praExpr) := do
  -- Parenthesize a lambda argument when another argument follows it.
  if let `(praExpr| $head:praExpr $arg:praExpr) := f then
    match arg with
    | `(praExpr| fun $_xs:praFunBinder* => $_body:praExpr)
    | `(praExpr| fun $_xs:praFunBinder* : $_type:praExpr => $_body:praExpr) =>
      return ← `(praExpr| $head ($arg) $a)
    | _ => pure ()
  `(praExpr| $f $a)

private def applyParameters (names : Names) (name : Name) (fs ps : List (TSyntax `praExpr)) :
    CommandElabM (TSyntax `praExpr) := do
  let environment := CoreEnvironment.getState (← getEnv)
  let parameters ← match environment.lookup name with
    | some (.predicate d) => pure d.parameters
    | some (.theoremE d) => pure d.parameters
    | _ => throwError "cannot find predicate/theorem signature for printing `{name}`"
  let mut fs := fs
  let mut ps := ps
  let mut result ← globalExpr names name
  for parameter in parameters do
    match parameter with
    | .function _ _ =>
      let arg :: rest := fs | throwError "missing function argument when printing `{name}`"
      result ← applyExpr result arg
      fs := rest
    | .predicate _ _ =>
      let arg :: rest := ps | throwError "missing predicate argument when printing `{name}`"
      result ← applyExpr result arg
      ps := rest
  unless fs.isEmpty && ps.isEmpty do
    throwError "extra declaration arguments when printing `{name}`"
  return result

private def call (name : Name) (args : List (TSyntax `praExpr)) :
    CommandElabM (TSyntax `praExpr) := do
  args.foldlM applyExpr (← identExpr name)

private def lambda (name : Name) (body : TSyntax `praExpr) :
    CommandElabM (TSyntax `praExpr) := do
  let binder ← `(praFunBinder| $(mkIdent name):ident)
  if let `(praExpr| fun $binders:praFunBinder* => $inner:praExpr) := body then
    `(praExpr| fun $binder:praFunBinder $binders:praFunBinder* => $inner)
  else `(praExpr| fun $binder:praFunBinder => $body)

/-- Delaborate an arity as `Nat → … → Nat`. -/
def delabArity : Nat → CommandElabM (TSyntax `praExpr)
  | 0 => identExpr `Nat
  | n + 1 => do `(praExpr| Nat → $(← delabArity n))

/-- Delaborate a `PredicateSignature` as `Nat → … → QFProp` or `Nat → … → Prop`. -/
def delabPredicateType (s : Core.PredicateSignature) : CommandElabM (TSyntax `praExpr) := do
  let mut result ← if s.sort == .qf then identExpr `QFProp else `(praExpr| Prop)
  for _ in [:s.arity] do result ← `(praExpr| Nat → $result)
  return result

private def numeralValue? : Core.Term → Option Nat
  | .zero => some 0
  | .app .succ t => (· + 1) <$> numeralValue? t
  | _ => none

/-- Hover type attached to a `DelabTree` node. -/
inductive DelabType where
  | none
  | term (arity : Core.Arity)
  | predicate (signature : Core.PredicateSignature)
  | declaration (value : Core.Declaration)
  deriving Inhabited

/-- Delaborated syntax node paired with its `DelabType` and child subtrees. -/
structure DelabTree where
  stx : Syntax
  type : DelabType := .none
  children : Array DelabTree := #[]
  deriving Inhabited

/-- Flatten child trees when consecutive lambdas are grouped into one `fun`. -/
private def lambdaChildren (binder body : DelabTree) : Array DelabTree :=
  match body.stx with
  | `(praExpr| fun $_binders:praFunBinder* => $_inner:praExpr) => #[binder] ++ body.children
  | _ => #[binder, body]

/-- Well-formed environment and local context used to infer subterm types during delaboration. -/
structure DelabContext where
  environment : Core.Environment
  context : Core.Context

private def DelabContext.pushLocal (c : DelabContext) (arity : Core.Arity) : DelabContext :=
  { c with context := c.context.pushLocal arity }

private def termType (typing : Option DelabContext) (t : Core.Term) :
    CommandElabM DelabType := do
  let some c := typing | return .none
  match Core.inferTerm (pra.maxDepth.get (← getOptions)) c.environment c.context t with
  | .ok arity => return .term arity
  | .error error => throwError "cannot infer a delaboration term: {error.message}"

private def predicateType (typing : Option DelabContext) (p : Predicate) :
    CommandElabM DelabType := do
  let some c := typing | return .none
  match Core.inferPredicate (pra.maxDepth.get (← getOptions)) c.environment c.context p with
  | .ok sig => return .predicate sig
  | .error error => throwError "cannot infer a delaboration predicate: {error.message}"

private def declarationTree (names : Names) (n : Name) : CommandElabM DelabTree := do
  let some d := (CoreEnvironment.getState (← getEnv)).lookup n
    | throwError "cannot find declaration for printing `{n}`"
  return ⟨← globalExpr names n, .declaration d, #[]⟩

/-- Delaborate `term` to a `DelabTree`, inferring subterm types when `typing` is given. -/
partial def delabTermTree (names : Names) (term : Core.Term)
    (typing : Option DelabContext := none) : CommandElabM DelabTree := do
  let type ← termType typing term
  if let some (name, _) := names.termAliases.find? (·.2 == term) then
    return ⟨← identExpr name, type, #[]⟩
  let recur := fun t => delabTermTree names t typing
  let node (stx : TSyntax `praExpr) (children : Array DelabTree := #[]) :=
    pure (⟨stx, type, children⟩ : DelabTree)
  match term with
  | .bvar i => node (← identExpr (names.locals[i]?.getD (.mkSimple s!"unbound{i}")))
  | .parameter i => node (← identExpr (names.functions[i]?.getD (.mkSimple s!"parameter{i}")))
  | .zero => node (← numeral 0)
  | .succ => node (← identExpr `S)
  | .lam hint body =>
    let x := names.freshName "x" hint
    let inner := fun t => delabTermTree (names.pushLocal x) t (typing.map (·.pushLocal 0))
    let binder ← inner (.bvar 0)
    let body ← inner body
    node (← lambda x ⟨body.stx⟩) (lambdaChildren binder body)
  | .app f a =>
    if let .succ := f then
      if !names.termAliases.any (·.2 == Core.Term.succ) then
        if let some n := numeralValue? a then return ← node (← numeral (n + 1))
    let f ← recur f
    let a ← recur a
    node (← applyExpr ⟨f.stx⟩ ⟨a.stx⟩) #[f, a]
  | .letE hint value body =>
    let x := names.freshName "x" hint
    let value ← recur value
    let arity := match value.type with | .term arity => arity | _ => 0
    let inner := fun t => delabTermTree (names.pushLocal x) t (typing.map (·.pushLocal arity))
    let binder ← inner (.bvar 0)
    let body ← inner body
    node (← `(praExpr| let $(mkIdent x):ident := $(⟨value.stx⟩):praExpr;
      $(⟨body.stx⟩):praExpr)) #[value, binder, body]
  | .primrec b s n =>
    let b ← recur b
    let s ← recur s
    let n ← recur n
    node (← call `primrec [⟨b.stx⟩, ⟨s.stx⟩, ⟨n.stx⟩]) #[b, s, n]
  | .definition n fs =>
    let head ← declarationTree names n
    let args ← fs.mapM recur
    let stx ← args.foldlM (fun f a => applyExpr f ⟨a.stx⟩) ⟨head.stx⟩
    node stx (#[head] ++ args.toArray)

/-- Delaborate `predicate` to a `DelabTree`, inferring subterm types when `typing` is given. -/
partial def delabPredicateTree (names : Names) (predicate : Predicate)
    (typing : Option DelabContext := none) : CommandElabM DelabTree := do
  let type ← predicateType typing predicate
  if let some (name, _) := names.predicateAliases.find? (·.2 == predicate) then
    return ⟨← identExpr name, type, #[]⟩
  let pred := fun p => delabPredicateTree names p typing
  let term := fun t => delabTermTree names t typing
  let node (stx : TSyntax `praExpr) (children : Array DelabTree := #[]) :=
    pure (⟨stx, type, children⟩ : DelabTree)
  let bind (hint : Name) (body : Predicate) (kind : Nat) := do
    let x := names.freshName "x" hint
    let innerTyping := typing.map (·.pushLocal 0)
    let binder ← delabTermTree (names.pushLocal x) (.bvar 0) innerTyping
    let body ← delabPredicateTree (names.pushLocal x) body innerTyping
    let b ← `(praBinder| $(mkIdent x):ident)
    let stx ← match kind with
      | 0 => lambda x ⟨body.stx⟩
      | 1 => `(praExpr| ∀ $b:praBinder : Nat, $(⟨body.stx⟩):praExpr)
      | _ => `(praExpr| ∃ $b:praBinder : Nat, $(⟨body.stx⟩):praExpr)
    node stx (if kind == 0 then lambdaChildren binder body else #[binder, body])
  match predicate with
  | .letTerm hint a p =>
    let x := names.freshName "x" hint
    let value ← term a
    let body ← delabPredicateTree
      { names with termAliases := (x, a) :: names.termAliases } p typing
    let binder : DelabTree := ⟨← identExpr x, value.type, #[]⟩
    node (← `(praExpr| let $(mkIdent x):ident := $(⟨value.stx⟩):praExpr;
      $(⟨body.stx⟩):praExpr)) #[value, binder, body]
  | .letPredicate hint q p =>
    let x := names.freshName "P" hint
    let value ← pred q
    let body ← delabPredicateTree
      { names with predicateAliases := (x, q) :: names.predicateAliases } p typing
    let binder : DelabTree := ⟨← identExpr x, value.type, #[]⟩
    node (← `(praExpr| let $(mkIdent x):ident := $(⟨value.stx⟩):praExpr;
      $(⟨body.stx⟩):praExpr)) #[value, binder, body]
  | .false => node (← identExpr `False)
  | .true => node (← identExpr `True)
  | .equal a b =>
    let a ← term a
    let b ← term b
    node (← `(praExpr| $(⟨a.stx⟩):praExpr = $(⟨b.stx⟩):praExpr)) #[a, b]
  | .imp a b =>
    let a ← pred a
    let b ← pred b
    node (← `(praExpr| $(⟨a.stx⟩):praExpr → $(⟨b.stx⟩):praExpr)) #[a, b]
  | .and a b =>
    if let (.imp p q, .imp q' p') := (a, b) then
      if p == p' && q == q' then
        let p ← pred p
        let q ← pred q
        return ← node (← `(praExpr| $(⟨p.stx⟩):praExpr ↔ $(⟨q.stx⟩):praExpr)) #[p, q]
    let a ← pred a
    let b ← pred b
    node (← `(praExpr| $(⟨a.stx⟩):praExpr ∧ $(⟨b.stx⟩):praExpr)) #[a, b]
  | .or a b =>
    let a ← pred a
    let b ← pred b
    node (← `(praExpr| $(⟨a.stx⟩):praExpr ∨ $(⟨b.stx⟩):praExpr)) #[a, b]
  | .all (.lam hint p) => bind hint p 1
  | .ex (.lam hint p) => bind hint p 2
  | .all p => bind .anonymous (.app p.shift (.bvar 0)) 1
  | .ex p => bind .anonymous (.app p.shift (.bvar 0)) 2
  | .parameter i =>
    node (← identExpr (names.predicates[i]?.getD (.mkSimple s!"predicate{i}")))
  | .lam hint body => bind hint body 0
  | .app p n =>
    let p ← pred p
    let n ← term n
    node (← applyExpr ⟨p.stx⟩ ⟨n.stx⟩) #[p, n]
  | .definition n fs ps =>
    let head ← declarationTree names n
    let fs ← fs.mapM term
    let ps ← ps.mapM pred
    node (← applyParameters names n (fs.map fun t => ⟨t.stx⟩) (ps.map fun p => ⟨p.stx⟩))
      (#[head] ++ fs.toArray ++ ps.toArray)

/-- Delaborate `term` to `praExpr` syntax. -/
def delabTerm (names : Names) (term : Core.Term) : CommandElabM (TSyntax `praExpr) :=
  return ⟨(← delabTermTree names term).stx⟩

/-- Delaborate `predicate` to `praExpr` syntax. -/
def delabPredicate (names : Names) (predicate : Predicate) : CommandElabM (TSyntax `praExpr) :=
  return ⟨(← delabPredicateTree names predicate).stx⟩

private def proofType (context : Core.Context) (p : Proof) : CommandElabM Predicate := do
  let env := CoreEnvironment.getState (← getEnv)
  match Core.inferProof (pra.maxDepth.get (← getOptions)) env context p with
  | .ok type => return type
  | .error error => throwError "cannot infer a proof type for printing: {error.message}"

private def formulaHead (context : Core.Context) (p : Proof) : CommandElabM Predicate := do
  let env := CoreEnvironment.getState (← getEnv)
  let type ← proofType context p
  match Core.reduceFormula (pra.maxDepth.get (← getOptions)) env type with
  | .ok type => return type
  | .error error => throwError "cannot normalize a proof formula for printing: {error.message}"

private def typedLambda (name : Name) (type body : TSyntax `praExpr) :
    CommandElabM (TSyntax `praExpr) := do
  let binder ← `(praFunBinder| $(mkIdent name):ident)
  if let `(praExpr| fun $binders:praFunBinder* : $innerType:praExpr => $inner:praExpr) := body then
    if type.raw == innerType.raw then
      return ← `(praExpr| fun $binder:praFunBinder $binders:praFunBinder* : $type => $inner)
  `(praExpr| fun $binder:praFunBinder : $type => $body)

/-- Delaborate `p` to `praExpr` syntax, adding a type ascription when `hasExpected` is false and
the constructor's result formula is not determined by its arguments. The supplied context must
be well formed. -/
partial def delabProof (names : Names) (p : Proof) (context : Core.Context := {})
    (hasExpected : Bool := false) : CommandElabM (TSyntax `praExpr) := do
  let type ← proofType context p
  let finish (result : TSyntax `praExpr) (needsExpected : Bool := false) := do
    if needsExpected && !hasExpected then
      `(praExpr| ($result : $(← delabPredicate names type)))
    else pure result
  match p with
  | .letTerm hint a p =>
    let x := names.freshName "x" hint
    `(praExpr| let $(mkIdent x):ident := $(← delabTerm names a);
      $(← delabProof { names with termAliases := (x, a) :: names.termAliases }
        p context hasExpected))
  | .letPredicate hint q p =>
    let x := names.freshName "P" hint
    `(praExpr| let $(mkIdent x):ident := $(← delabPredicate names q);
      $(← delabProof { names with predicateAliases := (x, q) :: names.predicateAliases }
        p context hasExpected))
  | .hyp i => identExpr (names.proofs[i]?.getD (.mkSimple s!"hypothesis{i}"))
  | .trueIntro => identExpr `trivial
  | .theoremE n fs ps =>
    applyParameters names n (← fs.mapM (delabTerm names)) (← ps.mapM (delabPredicate names))
  | .impIntro hint a p =>
    let h := names.freshName "h" hint
    typedLambda h (← delabPredicate names a)
      (← delabProof { names with proofs := h :: names.proofs } p
        (context.pushProof a) hasExpected)
  | .impElim f a => do
    applyExpr (← delabProof names f context) (← delabProof names a context true)
  | .andIntro a b => do
    `(praExpr| ($(← delabProof names a context hasExpected),
      $(← delabProof names b context hasExpected)))
  | .andLeft p => do call `and_left [← delabProof names p context]
  | .andRight p => do call `and_right [← delabProof names p context]
  | .orLeft _ p => do finish (← call `or_left [← delabProof names p context true]) true
  | .orRight _ p => do finish (← call `or_right [← delabProof names p context true]) true
  | .orElim ln rn _ p l r =>
    let .or a b ← formulaHead context p | throwError "expected a disjunction in core proof"
    let branch hint domain q := do
      let h := names.freshName "h" hint
      typedLambda h (← delabPredicate names domain)
        (← delabProof { names with proofs := h :: names.proofs } q (context.pushProof domain) true)
    finish (← call `or_elim [← delabProof names p context, ← branch ln a l, ← branch rn b r]) true
  | .falseElim _ p => do finish (← call `false_elim [← delabProof names p context true]) true
  | .forallIntro hint _ p =>
    let x := names.freshName "x" hint
    typedLambda x (← identExpr `Nat)
      (← delabProof (names.pushLocal x) p (context.pushLocal 0) hasExpected)
  | .forallElim p n => do applyExpr (← delabProof names p context) (← delabTerm names n)
  | .existsIntro _ n p => do
    finish (← `(praExpr| ($(← delabTerm names n), $(← delabProof names p context true)))) true
  | .existsElim xn hn _ p body =>
    let .ex m ← formulaHead context p | throwError "expected an existential in core proof"
    let x := names.freshName "x" xn
    let h := (names.pushLocal x).freshName "h" hn
    let hypothesis := Predicate.app m.shift (.bvar 0)
    let extendedNames := (names.pushLocal x)
    let body ← delabProof { extendedNames with proofs := h :: names.proofs } body
      ((context.pushLocal 0).pushProof hypothesis) true
    let branch ← typedLambda x (← identExpr `Nat)
      (← typedLambda h (← delabPredicate extendedNames hypothesis) body)
    finish (← call `exists_elim [← delabProof names p context, branch]) true
  | .letE hint type value body =>
    let h := names.freshName "h" hint
    `(praExpr| let $(mkIdent h):ident : $(← delabPredicate names type) :=
      $(← delabProof names value context true);
      $(← delabProof { names with proofs := h :: names.proofs } body
        (context.pushProof type) hasExpected))
  | .ascribe type p =>
    `(praExpr| ($(← delabProof names p context true) : $(← delabPredicate names type)))
  | .eqRefl n => do call `eq_refl [← delabTerm names n]
  | .eqSubst motive e p =>
    call `eq_subst [← delabPredicate names motive, ← delabProof names e context,
      ← delabProof names p context true]
  | .succNeZero n => do call `succ_ne_zero [← delabTerm names n]
  | .succInj p => do call `succ_inj [← delabProof names p context]
  | .lem a => do call `lem [← delabPredicate names a]
  | .induction xn hn motive base step n =>
    let x := names.freshName "x" xn
    let h := (names.pushLocal x).freshName "h" hn
    let hypothesis := Predicate.app motive.shift (.bvar 0)
    let extendedNames := (names.pushLocal x)
    let step ← delabProof { extendedNames with proofs := h :: names.proofs } step
      ((context.pushLocal 0).pushProof hypothesis) true
    let step ← typedLambda x (← identExpr `Nat)
      (← typedLambda h (← delabPredicate extendedNames hypothesis) step)
    let head ← `(praExpr| induction (motive := $(← delabPredicate names motive)))
    [← delabProof names base context true, step, ← delabTerm names n].foldlM applyExpr head

private def parameters (signature : List Core.Parameter) :
    CommandElabM (Names × Array (TSyntax `praParam)) := do
  let mut names : Names := {}
  let mut binders := #[]
  for parameter in signature do
    match parameter with
    | .function hint arity =>
      let n := names.freshName "f" hint
      binders := binders.push (← `(praParam| ($(mkIdent n):ident : $(← delabArity arity))))
      names := { names with functions := names.functions ++ [n] }
    | .predicate hint sig =>
      let n := names.freshName "P" hint
      binders := binders.push (← `(praParam| ($(mkIdent n):ident : $(← delabPredicateType sig))))
      names := { names with predicates := names.predicates ++ [n] }
  return (names, binders)

/-- Delaborate `d` to a `praDecl`. -/
def delabDeclaration (d : Core.Declaration) : CommandElabM (TSyntax `praDecl) := do
  let ns ← getCurrNamespace
  let relative := d.name.replacePrefix ns .anonymous
  let name := if ns.isPrefixOf d.name && ns != d.name && !isBuiltinName relative then
    relative else `_root_ ++ d.name
  match d with
  | .function d =>
    let (names, ps) ← parameters d.parameterSignature
    `(praDecl| def $(mkIdent name):ident $ps:praParam* : $(← delabArity d.arity) :=
      $(← delabTerm names d.body))
  | .predicate d =>
    let (names, ps) ← parameters d.parameters
    `(praDecl| def $(mkIdent name):ident $ps:praParam* : $(← delabPredicateType d.signature) :=
      $(← delabPredicate names d.body))
  | .theoremE d =>
    let (names, ps) ← parameters d.parameters
    `(praDecl| theorem $(mkIdent name):ident $ps:praParam* :
      $(← delabPredicate names d.type) :=
      $(← delabProof names d.body { functions := d.functions, predicates := d.predicates } true))

private def signatureParts (d : Core.Declaration) :
    CommandElabM (Array (TSyntax `praParam) × TSyntax `praExpr) := do
  match d with
  | .function d =>
    let signature := d.parameterSignature
    let (_, ps) ← parameters signature
    return (ps, ← delabArity d.arity)
  | .predicate d =>
    let (_, ps) ← parameters d.parameters
    return (ps, ← delabPredicateType d.signature)
  | .theoremE d =>
    let (names, ps) ← parameters d.parameters
    return (ps, ← delabPredicate names d.type)

/-- Format a declaration's parameter and result types separated by `→`, without its name. -/
def delabSignatureType (d : Core.Declaration) : CommandElabM MessageData := do
  let (ps, type) ← signatureParts d
  let mut text := ""
  for p in ps do
    text := text ++ (← formatSyntax `praParam p).pretty ++ " → "
  return m!"{text}{← formatSyntax `praExpr type}"

/-- Format `d`'s name, parameters, and result type. -/
def delabSignature (d : Core.Declaration) : CommandElabM MessageData := do
  let (ps, type) ← signatureParts d
  let mut text := (← relativeName d.name).toString
  for p in ps do
    text := text ++ " " ++ (← formatSyntax `praParam p).pretty
  return m!"{text} : {← formatSyntax `praExpr type}"

end LeanPRA.Surface
