module

public import LeanPRA.Library.Computability.Computation
public meta import LeanPRA.Library.Tactic.Construction

/-!
# Deriving primitive recursiveness

`derive_primrec f as h` compiles a closed unary numerical PRA definition `f` and publishes a
checked theorem `h : Primrec f`. A unary expression can be written in parentheses in place of `f`.
Compiled dependencies and closed parameter specializations are
shared by name. A dependency of higher arity takes a nested numerical tuple as its input, with the
last component unpaired. Captured variables become numerical arguments of generated helpers.

For each compiled definition, the command emits a numerical program, a numerical computation-tree
builder, and a proof of the builder's correctness.
Every emitted declaration passes through the ordinary PRA checker.
-/

public meta section

namespace LeanPRA.Library.Computability.Tactic

open Lean hiding Term

open Lean.Elab.Command

open Lean.Elab

open LeanPRA Core Surface

open LeanPRA.Library.Tactic.Construction

private def call (name : Name) (args : List Term := []) (parameters : List Term := []) : Term :=
  applyDefinition name args parameters

private def ap (f x : Term) : Term := .app f x

private def pair (x y : Term) : Term := call `pair [x, y]

private def unpairL (x : Term) : Term := call `unpairLeft [x]

private def unpairR (x : Term) : Term := call `unpairRight [x]

private def evalType (e x y t : Term) : Predicate :=
  (((Predicate.definition `Primrec.Computation.Evaluates [] []).app e).app x).app y |>.app t

private def all (p : Predicate) : Predicate := .all (.lam `x p)

private def introAll (p : Predicate) (h : Proof) : Proof := .forallIntro `x (.lam `x p) h

private partial def beta : Term → Term
  | .app f a =>
    let f := beta f
    let a := beta a
    match f with
    | .lam _ b => beta (b.subst0 a)
    | _ => .app f a
  | .letE _ a b => beta (b.subst0 (beta a))
  | .lam n b => .lam n (beta b)
  | .primrec b s => .primrec (beta b) (beta s)
  | .definition n fs => .definition n (fs.map beta)
  | t => t

private partial def closed (depth : Nat := 0) : Term → Bool
  | .bvar i => i < depth
  | .parameter _ => false
  | .lam _ b => closed (depth + 1) b
  | .app f a => closed depth f && closed depth a
  | .letE _ a b => closed depth a && closed (depth + 1) b
  | .primrec b s => closed depth b && closed depth s
  | .definition _ fs => fs.all (closed depth)
  | _ => true

private def lower (count depth : Nat) : Term → Option Term
  | .bvar i => if i < depth then some (.bvar i)
    else if i < depth + count then none else some (.bvar (i - count))
  | .lam n b => return .lam n (← lower count (depth + 1) b)
  | .app f a => return .app (← lower count depth f) (← lower count depth a)
  | .letE n a b => return .letE n (← lower count depth a) (← lower count (depth + 1) b)
  | .primrec b s =>
    return .primrec (← lower count depth b) (← lower count depth s)
  | .definition n fs => return .definition n (← fs.mapM (lower count depth))
  | t => some t

private def projection? (depth : Nat) (t : Term) : Option Term := do
  let (.definition name [], [arg]) := getAppFnArgs t | none
  unless name == `unpairLeft || name == `unpairRight do none
  let (.definition `pair [], [_, _]) := getAppFnArgs arg | none
  lower depth 0 t

private partial def findProjection (depth : Nat) (t : Term) : Option Term :=
  projection? depth t |>.orElse fun _ => match t with
    | .lam _ b => findProjection (depth + 1) b
    | .app f a => (findProjection depth f).orElse fun _ => findProjection depth a
    | .letE _ a b => (findProjection depth a).orElse fun _ => findProjection (depth + 1) b
    | .primrec b s => (findProjection depth b).orElse fun _ => findProjection depth s
    | .definition _ fs => fs.findSome? (findProjection depth)
    | _ => none

private def abstractTerm (source : Term) (depth : Nat) (t : Term) : Term :=
  if t == source.shift depth then .bvar depth else match t with
  | .bvar i => .bvar (if i < depth then i else i + 1)
  | .lam n b => .lam n (abstractTerm source (depth + 1) b)
  | .app f a => .app (abstractTerm source depth f) (abstractTerm source depth a)
  | .letE n a b => .letE n (abstractTerm source depth a) (abstractTerm source (depth + 1) b)
  | .primrec b s => .primrec (abstractTerm source depth b) (abstractTerm source depth s)
  | .definition n fs => .definition n (fs.map (abstractTerm source depth))
  | t => t

/-- Rewrite tuple projections and generated helpers using numerical equality proofs. -/
private partial def simplify (original : Term)
    (unfold : Name → Option (Name × FunctionDefinition) := fun _ => none) :
    Term × Proof := Id.run do
  let t := beta original
  if let some redex := findProjection 0 t then
    let (.definition name [], [arg]) := getAppFnArgs redex | return (t, .forallElim .eqRefl t)
    let (.definition `pair [], [a, b]) := getAppFnArgs arg | return (t, .forallElim .eqRefl t)
    let value := if name == `unpairLeft then a else b
    let lemma := if name == `unpairLeft then `unpairLeft_pair else `unpairRight_pair
    let motive := Term.lam `v (abstractTerm redex 0 t)
    let next := beta (ap motive value)
    let h := mkEqCongr motive redex value (applyTheorem lemma [a, b])
    let (result, rest) := simplify next unfold
    return (result, mkEqTrans t next result h rest)
  if let .app (.primrec b s) n := t then
    let (b', hb) := simplify b unfold
    let (n', hn) := simplify n unfold
    let body := beta (ap (ap (s.shift 2) (.bvar 1)) (.bvar 0))
    let (body', hs) := simplify body unfold
    if b == b' && n == n' && body == body' then return (t, .forallElim .eqRefl t)
    let mut current := t
    let mut proof := Proof.forallElim .eqRefl t
    if b != b' then
      let next := Term.app (.primrec b' s) n
      let h := mkEqCongr (.lam `v (.app (.primrec (.bvar 0) s.shift) n.shift)) b b' hb
      proof := mkEqTrans t current next proof h
      current := next
    if n != n' then
      let next := Term.app (.primrec b' s) n'
      let h := mkEqCongr (.lam `v (.app (.primrec b'.shift s.shift) (.bvar 0))) n n' hn
      proof := mkEqTrans t current next proof h
      current := next
    if body != body' then
      let s' := Term.lam `i (.lam `y body')
      let p := Predicate.equal body body'
      let hs := introAll (.all (.lam `y p)) (introAll p hs)
      let next := Term.app (.primrec b' s') n'
      let h := applyTheorem `primrec_congr [b', n'] [s, s'] [hs]
      proof := mkEqTrans t current next proof h
      current := next
    return (current, proof)
  let (head, args) := getAppFnArgs t
  let mut current := t
  let mut proof := Proof.forallElim .eqRefl t
  let mut args := args.toArray
  for i in [:args.size] do
    let old := args[i]!
    let (value, h) := simplify old unfold
    if old == value then continue
    let motiveArgs := args.mapIdx fun j a => if i == j then Term.bvar 0 else a.shift
    let motive := Term.lam `v (motiveArgs.foldl .app head.shift)
    args := args.set! i value
    let next := args.foldl .app head
    proof := mkEqTrans t current next proof (mkEqCongr motive old value h)
    current := next
  if let (.definition name [], arguments) := getAppFnArgs current then
    if let some (equation, d) := unfold name then
      if arguments.length == d.arity then
        let value := beta (arguments.foldl .app d.body)
        let (result, rest) := simplify value unfold
        return (result, mkEqTrans t current result proof
          (mkEqTrans current value result (applyTheorem equation arguments) rest))
  if let (.definition projection [], [arg]) := getAppFnArgs current then
    if let (.definition `pair [], [a, b]) := getAppFnArgs arg then
      if projection == `unpairLeft || projection == `unpairRight then
        let value := if projection == `unpairLeft then a else b
        let lemma := if projection == `unpairLeft then `unpairLeft_pair else `unpairRight_pair
        return (value, mkEqTrans t current value proof (applyTheorem lemma [a, b]))
  return (current, proof)

private def sameHead (a b : Term) : Bool :=
  match a, b with
  | .primrec .., .primrec .. => true
  | _, _ =>
    match (getAppFnArgs a).1, (getAppFnArgs b).1 with
    | .definition f _, .definition g _ => f == g
    | f, g => f == g

private partial def exposeSource (env : Core.Environment) (target original : Term) : Term × Proof :=
  let (simple, hs) := simplify original
  if sameHead target simple then (simple, hs)
  else
    match getAppFnArgs simple with
    | (.definition name fs, args) =>
      match env.lookup name with
      | some (.function d) =>
        let next := beta (args.foldl .app (d.body.instantiate fs))
        let equation := Proof.ascribe (.equal simple next) (.forallElim .eqRefl simple)
        let (value, h) := exposeSource env target next
        (value, mkEqTrans original simple value hs
          (mkEqTrans simple next value equation h))
      | _ => (simple, hs)
    | _ => (simple, hs)

-- The value and tree builder are closed unary functions. Correctness proves their evaluation
-- for every numerical input.
private structure Compiled where
  code : Term
  value : Term
  trace : Term
  correct : Proof
  deriving Inhabited

private abbrev CompiledFunction := Name × List Term × Compiled

private initialize compiledFunctions :
    SimplePersistentEnvExtension CompiledFunction (Array CompiledFunction) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

private def normalize (c : Compiled) : Compiled := Id.run do
  let x := Term.bvar 0
  let old := beta (ap c.value x)
  let (value, equality) := simplify old
  if value == old then return { c with value := .lam `x old }
  let p := evalType c.code x value (ap c.trace x)
  let h := applyTheorem `Primrec.Computation.evaluates_congr
    [c.code, x, old, value, ap c.trace x] [] [equality, .forallElim c.correct x]
  return { c with value := .lam `x value, correct := introAll p h }

private def constant (n : Term) : Compiled := {
  code := call `Primrec.Code.const [n]
  value := .lam `x n
  trace := call `Primrec.Computation.constTrace [n]
  correct := applyTheorem `Primrec.Computation.evaluates_const [n]
}

private def identity : Compiled := {
  code := call `Primrec.Code.id
  value := .lam `x (.bvar 0)
  trace := call `Primrec.Computation.idTrace
  correct := applyTheorem `Primrec.Computation.evaluates_id
}

private def basic (kind : Name) : Compiled := Id.run do
  let x := Term.bvar 0
  let code := call (`Primrec.Code ++ kind)
  let value := if kind == `succ then ap .succ x else
    if kind == `left then unpairL x else unpairR x
  return {
    code := code
    value := .lam `x value
    trace := .lam `x (call `Primrec.Computation.node [code, x, value, .zero, .zero])
    correct := applyTheorem (`Primrec.Computation ++ Name.mkSimple s!"evaluates_{kind}")
  }

private def combine (kind : Name) (a b : Compiled) : Compiled :=
  let x := Term.bvar 0
  let value := if kind == `comp then ap a.value (ap b.value x)
    else pair (ap a.value x) (ap b.value x)
  let args := [a.value, b.value, a.trace, b.trace]
  normalize {
    code := call (`Primrec.Code ++ kind) [a.code, b.code]
    value := .lam `x value
    trace := call (`Primrec.Computation ++ Name.mkSimple s!"{kind}Trace") [a.code, b.code] args
    correct := applyTheorem (`Primrec.Computation ++ Name.mkSimple s!"evaluates_{kind}Trace")
      [a.code, b.code] args [a.correct, b.correct]
  }

private def recurse (a b : Compiled) : Compiled :=
  let z := Term.bvar 0
  let step := Term.lam `x (.lam `i (.lam `y
    (ap b.value (pair (.bvar 2) (pair (.bvar 1) (.bvar 0))))))
  let ts := Term.lam `x (.lam `i (.lam `y
    (ap b.trace (pair (.bvar 2) (pair (.bvar 1) (.bvar 0))))))
  normalize {
    code := call `Primrec.Code.rec [a.code, b.code]
    value := .lam `z (.app (.primrec (ap a.value (unpairL z))
      (.lam `i (.lam `y (ap b.value
        (pair (unpairL (.bvar 2)) (pair (.bvar 1) (.bvar 0))))))) (unpairR z))
    trace := .lam `z (call `Primrec.Computation.recTrace
      [a.code, b.code, unpairL z, unpairR z] [a.value, step, a.trace, ts])
    correct := applyTheorem `Primrec.Computation.evaluates_rec_unary [a.code, b.code]
      [a.value, b.value, a.trace, b.trace] [a.correct, b.correct]
  }

private structure CompilerState where
  cache : Array (Name × List Term × Compiled) := #[]
  scope : Name := .anonymous
  nextRecursion : Nat := 0
  nextClosure : Nat := 0
  equations : Array (Name × Name × FunctionDefinition) := #[]

private abbrev CompileM := StateRefT CompilerState CommandElabM

private def publish (name : Name) (original : Term) (c : Compiled) (source : Syntax) :
    CompileM Compiled := do
  let codeName := name ++ `primrecCode
  let traceName := name ++ `primrecTrace
  let correctName := name ++ `primrec_evaluates
  publishChecked (.function ⟨codeName, [], 0, c.code⟩) source
  publishChecked (.function ⟨traceName, [], 1, c.trace⟩) source
  let code := call codeName
  let trace := call traceName
  let x := Term.bvar 0
  let mut c := c
  if c.value != original then
    let equations := (← get).equations
    let unfold := fun name =>
      (equations.find? (fun (n, _, _) => n == name)).map (fun (_, eq, d) => (eq, d))
    let old := beta (ap c.value x)
    let (value, equality) := simplify old unfold
    if value != old then
      let type := evalType c.code x value (ap c.trace x)
      let correct := applyTheorem `Primrec.Computation.evaluates_congr
        [c.code, x, old, value, ap c.trace x] [] [equality, .forallElim c.correct x]
      c := { c with value := .lam `x value, correct := introAll type correct }
    -- Source definitions can contain pairing identities too. Prove their simplifications before
    -- transporting the computed output back to the original definition.
    let sourceValue := beta (ap original x)
    let target := beta (ap c.value x)
    let env := CoreEnvironment.getState (← getEnv)
    let (exposed, h₁) := exposeSource env target sourceValue
    let (expected, h₂) := simplify exposed unfold
    let equality := mkEqTrans sourceValue exposed expected h₁ h₂
    let correct := Proof.ascribe (evalType c.code x expected (ap c.trace x))
      (.forallElim c.correct x)
    let correct := applyTheorem `Primrec.Computation.evaluates_congr
      [c.code, x, expected, sourceValue, ap c.trace x] []
      [mkEqSymm sourceValue expected equality, correct]
    c := { c with
      value := original
      correct := introAll (evalType c.code x sourceValue (ap c.trace x)) correct }
  let type := all (evalType code x (ap original x) (ap trace x))
  publishChecked (.theoremE ⟨correctName, [], type, c.correct⟩) source
  return {
    code := code
    trace := trace
    value := original
    correct := applyTheorem correctName
  }

private def projections (n : Nat) : Array Compiled := Id.run do
  let mut rest := identity
  let mut result := #[]
  for i in [:n] do
    if i + 1 == n then result := result.push rest
    else result := result.push (combine `comp (basic `left) rest)
    rest := combine `comp (basic `right) rest
  return result

mutual

private partial def compile (source : Syntax) (vars : Array Compiled) (input : Term) :
    CompileM Compiled := do
  let t := beta input
  if closed 0 t then return constant t
  match t with
  | .bvar i =>
    let some c := vars[i]? | throwError "unbound variable while compiling primitive recursion"
    return c
  | .app (.primrec base step) arg =>
    let b ← compile source vars base
    let n ← compile source vars arg
    let tail := basic `right
    let acc := combine `comp (basic `right) tail
    let index := combine `comp (basic `left) tail
    let lifted := vars.map fun v => combine `comp v (basic `left)
    let stepVars := #[acc, index] ++ lifted
    let s ← compile source stepVars (ap (ap (step.shift 2) (.bvar 1)) (.bvar 0))
    let r := recurse b s
    let state ← get
    modify fun state => { state with nextRecursion := state.nextRecursion + 1 }
    let r ← publish (state.scope ++ .num `recursion state.nextRecursion) r.value r source
    return combine `comp r (combine `pair identity n)
  | _ =>
    let (head, args) := getAppFnArgs t
    if head == .succ then
      let [a] := args | throwError "successor expects one numerical argument"
      return combine `comp (basic `succ) (← compile source vars a)
    if let .definition name fs := head then
      if name == `pair && args.length == 2 then
        return combine `pair (← compile source vars args[0]!) (← compile source vars args[1]!)
      if (name == `unpairLeft || name == `unpairRight) && args.length == 1 then
        return combine `comp (basic (if name == `unpairLeft then `left else `right))
          (← compile source vars args[0]!)
      let env := CoreEnvironment.getState (← getEnv)
      let some (.function d) := env.lookup name
        | throwError "expected numerical definition `{name}`"
      if fs.all (closed 0) && d.arity > 0 && args.length == d.arity then
        let f ← compileDefinition source d fs
        let values ← args.toArray.mapM (compile source vars)
        let mut tuple := values.back!
        for a in values.toList.reverse.drop 1 do tuple := combine `pair a tuple
        return combine `comp f tuple
      -- Numerical arguments keep captured values available to equality rewriting at each call.
      let state ← get
      modify fun state => { state with nextClosure := state.nextClosure + 1 }
      let name := state.scope ++ d.name ++ .num `closure state.nextClosure
      let abstract := fun body => (List.range vars.size).foldl (fun b _ => Term.lam `x b) body
      let declaration : FunctionDefinition := ⟨name, [], vars.size, abstract t⟩
      publishChecked (.function declaration) source
      let equation := name ++ `eq_def
      let arguments := (List.range vars.size).map fun i => Term.bvar (vars.size - 1 - i)
      let mut type := Predicate.equal (call name arguments) t
      let mut proof := Proof.forallElim .eqRefl t
      for _ in [:vars.size] do
        proof := introAll type proof
        type := all type
      publishChecked (.theoremE ⟨equation, [], type, proof⟩) source
      modify fun state =>
        { state with equations := state.equations.push (name, equation, declaration) }
      let body := abstract (args.foldl .app (d.body.instantiate fs))
      let f ← compileDefinition source { declaration with body } []
      let values := vars.reverse
      let mut tuple := values.back!
      for a in values.toList.reverse.drop 1 do tuple := combine `pair a tuple
      return combine `comp f tuple
    throwError "unsupported numerical expression in primitive-recursive compilation: {repr t}"

private partial def compileDefinition (source : Syntax) (d : FunctionDefinition)
    (actuals : List Term) :
    CompileM Compiled := do
  let sameFunction := fun (entry : Name × List Term × Compiled) =>
    entry.1 == d.name && entry.2.1 == actuals
  if let some (_, _, c) := (← get).cache.find? sameFunction then return c
  let ps := projections d.arity
  let original := Term.lam `x (ps.foldl (fun t p => ap t (beta (ap p.value (.bvar 0))))
    (call d.name [] actuals))
  let imported := compiledFunctions.getState (← getEnv)
  if let some (_, _, c) := imported.find? sameFunction then
    return c
  let args := (List.range d.arity).map fun i => Term.bvar (d.arity - 1 - i)
  let c ← compile source ps.reverse (args.foldl .app (d.body.instantiate actuals))
  let modulePrefix := (← getEnv).mainModule ++ `PrimitiveRecursive
  let baseName := if modulePrefix.isPrefixOf d.name then d.name else modulePrefix ++ d.name
  let count := (compiledFunctions.getState (← getEnv)).filter (fun (n, _, _) => n == d.name) |>.size
  let owner := if actuals.isEmpty then baseName else baseName ++ .num `specialization count
  let c ← publish owner original c source
  modifyEnv (compiledFunctions.addEntry · (d.name, actuals, c))
  modify fun s => { s with cache := s.cache.push (d.name, actuals, c) }
  return c

end

syntax (name := derivePrimrec) "derive_primrec " ident " as " ident : praDecl
syntax (name := derivePrimrecExpr) "derive_primrec " "(" praExpr ")" " as " ident : praDecl

@[command_elab LeanPRA.Surface.praEntry]
def elaboratePrimrec : CommandElab := fun stx => do
  let (d, expression, source, result) ← match stx[0] with
    | `(praDecl| derive_primrec $id:ident as $result:ident) =>
      let env := CoreEnvironment.getState (← getEnv)
      let (d, primitive) ← match ← resolveDeclaration? env id.getId with
        | some (.function d) => pure (d, false)
        | _ =>
          let some (.function signature) ← resolveSignature? env id.getId
            | throwErrorAt id "expected a numerical PRA declaration"
          let some primitive := primitiveDeclaration? signature.name
            | throwErrorAt id "expected a numerical PRA declaration"
          let .term body := primitive.construction
            | throwErrorAt id "expected a numerical PRA declaration"
          pure (⟨signature.name, signature.parameters, signature.arity, body⟩, true)
      unless d.parameters.isEmpty && d.arity == 1 do
        throwErrorAt id "expected a closed unary declaration"
      pure (d, primitive, id.raw, result.raw)
    | `(praDecl| derive_primrec ($e:praExpr) as $result:ident) =>
      let name := (← getEnv).mainModule ++ `PrimitiveRecursive ++
        (← getCurrNamespace) ++ result.getId ++ `source
      let id := mkIdent (`_root_ ++ name)
      let declaration ← `(praDecl| def $id:ident : Nat → Nat := $e:praExpr)
      elaborateDeclaration declaration
      let env := CoreEnvironment.getState (← getEnv)
      let some (.function d) := env.lookup name | throwError "expected a unary numerical expression"
      pure (d, true, e.raw, result.raw)
    | _ => throwUnsupportedSyntax
  let theoremName := (← getCurrNamespace) ++ result.getId
  let scope := (← getEnv).mainModule ++ `PrimitiveRecursive ++ theoremName
  let value := if expression then d.body else call d.name
  let action := if expression then do
      let c ← compile source #[identity] (ap d.body (.bvar 0))
      publish scope value c source
    else compileDefinition source d []
  let (c, _) ← action.run { scope }
  let type := Predicate.definition `Primrec [value] []
  let proof := applyTheorem `Primrec.of_evaluates [c.code] [value, c.trace]
    [c.correct]
  publishChecked (.theoremE ⟨theoremName, [], type, proof⟩) result

end LeanPRA.Library.Computability.Tactic
