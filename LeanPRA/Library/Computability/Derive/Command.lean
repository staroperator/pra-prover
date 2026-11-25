module

public import LeanPRA.Library.Computability.Derive.Prelude
public meta import LeanPRA.Library.Tactic.Construction

/-!
# Deriving primitive recursiveness

`derive_primrec f` publishes `f.code`, `f.trace`, `f.computedBy`, `f.encodes`, and
`f.primrec`. Write `derive_primrec f g` to derive several named functions in order. Write
`derive_primrec (expression) as h` for a closed unary expression. This publishes
`h.code`, `h.trace`, `h.computedBy`, `h.encodes`, and `h.primrec` under the prefix `h`.

A functional parameter supplies a code on its ordinary argument tuple. For example, to
specialize a definition at `fun x => add n x`, supply a unary code that adds the fixed value
`n` to its input. Public `.code` takes one number per declaration parameter in source order.
A numerical parameter supplies its value, and a functional parameter supplies its code.
Public `.trace` also takes the source functions and their trace builders. Public `.computedBy`
assumes their computation certificates and certifies the code on the ordinary argument tuple.

For definitions with declaration parameters, the derivers share `.internal.code`,
`.internal.trace`, and `.internal.computedBy`. An internal callback takes the pair of its
capture and its ordinary argument tuple. The internal code for a definition takes the pair of
its environment and its ordinary argument tuple. The environment stores numerical values first
and callback captures second, in declaration order within each group. Tuples are right-nested,
with zero for the empty tuple and the entry itself for a singleton. The public code and trace
specialize the internal ones. Definitions without declaration parameters share the public
declarations directly.

Named calls use the programs and certificates derived for their callees. The compiler uses
the basic program instructions for zero and successor. A primitive recursion includes its base
and step programs directly in its code. It receives a pair of its environment and counter.
The environment of a closure or recursion includes one field for each maximal numerical
expression independent of its local arguments. The fields follow source order, including
literals and repeated expressions. For a partially applied named function with callback parameters,
each callback environment occupies one field, alongside the fixed numerical arguments.
Changing a field value uses the same code.
-/

public meta section

namespace LeanPRA.Library.Computability.Derive.Command

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
    -- Lambda binders range over numbers, so substitution cannot create a beta redex
    -- in the normalized body.
    | .lam _ b => b.subst0 a
    | _ => .app f a
  | .letE _ a b => beta (b.subst0 (beta a))
  | .lam n b => .lam n (beta b)
  | .primrec b s => .primrec (beta b) (beta s)
  | .definition n fs => .definition n (fs.map beta)
  | t => t

/-- Expose the head of a program call. Keep lambda arguments intact so closure conversion
can pass their programs and captured inputs through enclosing calls. -/
partial def programHead : Term → Term
  | .app f a =>
    match programHead f with
    | .lam _ b => programHead (b.subst0 a)
    | g => .app g a
  | .letE _ a b => programHead (b.subst0 a)
  | t => t

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

private def tupleRedex? (depth : Nat) (t : Term) : Option Term := do
  let (.definition name [], args) := getAppFnArgs t | none
  if let [arg] := args then
    unless name == `unpairLeft || name == `unpairRight do none
    let (.definition `pair [], [_, _]) := getAppFnArgs arg | none
    lower depth 0 t
  else if let [a, b] := args then
    guard (name == `pair)
    let (.definition `unpairLeft [], [x]) := getAppFnArgs a | none
    let (.definition `unpairRight [], [y]) := getAppFnArgs b | none
    guard (x == y)
    lower depth 0 t
  else none

private partial def findTupleRedex (depth : Nat) (t : Term) : Option Term :=
  tupleRedex? depth t |>.orElse fun _ => match t with
    | .lam _ b => findTupleRedex (depth + 1) b
    | .app f a => (findTupleRedex depth f).orElse fun _ => findTupleRedex depth a
    | .letE _ a b => (findTupleRedex depth a).orElse fun _ => findTupleRedex (depth + 1) b
    | .primrec b s => (findTupleRedex depth b).orElse fun _ => findTupleRedex depth s
    | .definition _ fs => fs.findSome? (findTupleRedex depth)
    | _ => none

private def reduceTuple (t : Term) : Option (Term × Proof) := do
  let (.definition name [], args) := getAppFnArgs t | none
  if name == `pair then
    let [a, _] := args | none
    let (.definition `unpairLeft [], [x]) := getAppFnArgs a | none
    return (x, applyTheorem `pair_unpair [x])
  else
    let [arg] := args | none
    let (.definition `pair [], [a, b]) := getAppFnArgs arg | none
    if name == `unpairLeft then return (a, applyTheorem `unpairLeft_pair [a, b])
    else return (b, applyTheorem `unpairRight_pair [a, b])

-- The pattern is already shifted for this binder depth. Siblings can use it unchanged.
private def abstractTerm (pattern : Term) (depth : Nat) (t : Term) : Term :=
  if t == pattern then .bvar depth else match t with
  | .bvar i => .bvar (if i < depth then i else i + 1)
  | .lam n b => .lam n (abstractTerm pattern.shift (depth + 1) b)
  | .app f a => .app (abstractTerm pattern depth f) (abstractTerm pattern depth a)
  | .letE n a b =>
    .letE n (abstractTerm pattern depth a) (abstractTerm pattern.shift (depth + 1) b)
  | .primrec b s => .primrec (abstractTerm pattern depth b) (abstractTerm pattern depth s)
  | .definition n fs => .definition n (fs.map (abstractTerm pattern depth))
  | t => t

/-- Rewrite tuple projections using numerical equality proofs. -/
private partial def simplify (original : Term) :
    Term × Proof := Id.run do
  let t := beta original
  if let some redex := findTupleRedex 0 t then
    let some (value, equality) := reduceTuple redex | return (t, .forallElim .eqRefl t)
    let motive := Term.lam `v (abstractTerm redex 0 t)
    let next := beta (ap motive value)
    let h := mkEqCongr motive redex value equality
    let (result, rest) := simplify next
    return (result, mkEqTrans t next result h rest)
  if let .app (.primrec b s) n := t then
    let (b', hb) := simplify b
    let (n', hn) := simplify n
    let body := beta (ap (ap (s.shift 2) (.bvar 1)) (.bvar 0))
    let (body', hs) := simplify body
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
    let (value, h) := simplify old
    if old == value then continue
    let motiveArgs := args.mapIdx fun j a => if i == j then Term.bvar 0 else a.shift
    let motive := Term.lam `v (motiveArgs.foldl .app head.shift)
    args := args.set! i value
    let next := args.foldl .app head
    proof := mkEqTrans t current next proof (mkEqCongr motive old value h)
    current := next
  if (tupleRedex? 0 current).isSome then
    if let some (value, equality) := reduceTuple current then
      return (value, mkEqTrans t current value proof equality)
  return (current, proof)

-- A program's source function and computation trace take the same encoded input.
private structure ComputationCertificate where
  value : Term
  tr : Term
  correct : Proof
  deriving Inhabited

-- Quotation needs just the code and inputs. Deriving a computation theorem also reads the
-- certificate, including the proofs that simplify projections in its source function.
private structure Compiled where
  code : Term
  certificate : Thunk ComputationCertificate
  deriving Inhabited

private def Compiled.value (c : Compiled) := c.certificate.get.value

private def Compiled.tr (c : Compiled) := c.certificate.get.tr

private def Compiled.correct (c : Compiled) := c.certificate.get.correct

private def program (code : Term) (evidence : ComputationCertificate) : Compiled :=
  ⟨code, Thunk.pure evidence⟩

private def withCertificate (code : Term) (build : Unit → ComputationCertificate) : Compiled :=
  ⟨code, ⟨build⟩⟩

private def normalize (c : Compiled) : Compiled := Id.run do
  let x := Term.bvar 0
  let old := beta (ap c.value x)
  let (value, equality) := simplify old
  if value == old then return program c.code { c.certificate.get with value := .lam `x old }
  let p := evalType c.code x value (ap c.tr x)
  let h := applyTheorem `Primrec.Computation.evaluates_congr
    [c.code, x, old, value, ap c.tr x] [] [equality, .forallElim c.correct x]
  return program c.code ⟨.lam `x value, c.tr, introAll p h⟩

private def constant (n : Term) : Compiled :=
  program (call `Primrec.Code.const [n]) ⟨.lam `x n, call `Primrec.Computation.constTrace [n],
    applyTheorem `Primrec.Computation.evaluates_const [n]⟩

private def identity : Compiled :=
  program (call `Primrec.Code.id) ⟨.lam `x (.bvar 0), call `Primrec.Computation.idTrace,
    applyTheorem `Primrec.Computation.evaluates_id⟩

private def basic (kind : Name) : Compiled := Id.run do
  let x := Term.bvar 0
  let code := call (`Primrec.Code ++ kind)
  let value := if kind == `succ then ap .succ x else
    if kind == `left then unpairL x else unpairR x
  return program code ⟨.lam `x value,
    .lam `x (call `Primrec.Computation.node [code, x, value, .zero, .zero]),
    applyTheorem (`Primrec.Computation ++ Name.mkSimple s!"evaluates_{kind}")⟩

private def combine (kind : Name) (a b : Compiled) : Compiled :=
  if kind == `comp && a.code == identity.code then b
  else if kind == `comp && b.code == identity.code then a
  else if kind == `pair && a.code == (basic `left).code && b.code == (basic `right).code then
    identity
  else
    let code := call (`Primrec.Code ++ kind) [a.code, b.code]
    withCertificate code fun _ => Id.run do
      let x := Term.bvar 0
      let value := if kind == `comp then ap a.value (ap b.value x)
        else pair (ap a.value x) (ap b.value x)
      let args := [a.value, b.value, a.tr, b.tr]
      let tr := call (`Primrec.Computation ++ Name.mkSimple s!"{kind}Trace") [a.code, b.code] args
      let h := applyTheorem (`Primrec.Computation ++ Name.mkSimple s!"evaluates_{kind}Trace")
        [a.code, b.code] args [a.correct, b.correct]
      return (normalize (program code ⟨.lam `x value, tr, h⟩)).certificate.get

private def resultAtInput (c : Compiled) : Term :=
  match c.value with
  | .lam _ body => body
  | f => ap f (.bvar 0)

-- A saturated binary call constructs its source application directly. The shared
-- certificate checks the pair input to the named program once.
private def applyBinary (source : Term) (value : Thunk Term) (f a b : Compiled) : Compiled :=
  if a.code == (basic `left).code && b.code == (basic `right).code then f
  else
    let fields := [a.code, b.code]
    let codes := f.code :: fields
    withCertificate (call `Primrec.Code.comp [f.code, call `Primrec.Code.pair fields]) fun _ =>
      let args := [source, a.value, b.value, a.tr, b.tr, f.tr]
      ⟨.lam `x value.get, call `Primrec.Computation.binaryTrace codes args,
        applyTheorem `Primrec.Computation.computedBy_binary [] (args ++ codes)
          [f.correct, a.correct, b.correct]⟩

private def recurse (a b : Compiled) : Compiled :=
  let code := call `Primrec.Code.rec [a.code, b.code]
  withCertificate code fun _ => Id.run do
    let z := Term.bvar 0
    let step := Term.lam `x (.lam `i (.lam `y
      (ap b.value (pair (.bvar 2) (pair (.bvar 1) (.bvar 0))))))
    let ts := Term.lam `x (.lam `i (.lam `y
      (ap b.tr (pair (.bvar 2) (pair (.bvar 1) (.bvar 0))))))
    let value := Term.lam `z (.app (.primrec (ap a.value (unpairL z))
      (.lam `i (.lam `y (ap b.value
        (pair (unpairL (.bvar 2)) (pair (.bvar 1) (.bvar 0))))))) (unpairR z))
    let tr := Term.lam `z (call `Primrec.Computation.recTrace
      [a.code, b.code, unpairL z, unpairR z] [a.value, step, a.tr, ts])
    let h := applyTheorem `Primrec.Computation.evaluates_rec_unary [a.code, b.code]
      [a.value, b.value, a.tr, b.tr] [a.correct, b.correct]
    return (normalize (program code ⟨value, tr, h⟩)).certificate.get

private def computedByType (value code tr : Term) : Predicate :=
  .definition `Primrec.ComputedBy [value, code, tr] []

private def projections (n : Nat) : Array Compiled := Id.run do
  let mut rest := identity
  let mut result := #[]
  for i in [:n] do
    if i + 1 == n then
      result := result.push rest
    else
      result := result.push (combine `comp (basic `left) rest)
      rest := combine `comp (basic `right) rest
  return result

private def packPrograms : List Compiled → Compiled
  | [] => constant .zero
  | [p] => p
  | p :: q :: rest => combine `pair p (packPrograms (q :: rest))

private def packValues : List Term → Term
  | [] => .zero
  | [a] => a
  | a :: b :: rest => pair a (packValues (b :: rest))

/-- A program takes numerical expressions as inputs. The compiler pairs them to pass
several arguments or captured values to a single instruction. -/
inductive ProgramInput where
  | source (term : Term)
  | pair (left right : ProgramInput)
  deriving Inhabited

private def ProgramInput.pack : List ProgramInput → ProgramInput
  | [] => .source .zero
  | [a] => a
  | a :: b :: rest => .pair a (pack (b :: rest))

/-- Interpret each source expression and join its fields with the target's pairing operation. -/
def ProgramInput.foldM [Monad m] (source : Term → m α) (pair : α → α → m α) :
    ProgramInput → m α
  | .source t => source t
  | .pair a b => do pair (← a.foldM source pair) (← b.foldM source pair)

private def unpackValues (n : Nat) (input : Term) : List Term :=
  (projections n).toList.map fun p => beta (ap p.value input)

private def applyArgs (f : Term) (args : List Term) : Term :=
  args.foldl .app f

private def bind (n : Nat) (body : Term) : Term :=
  (List.range n).foldl (fun body _ => Term.lam `x body) body

private def indices (n : Nat) : List Term :=
  (List.range n).reverse.map Term.bvar

private def callbackValue (arity : Nat) (f : Term) : Term :=
  let x := Term.bvar 0
  .lam `x (applyArgs f (unpairL x :: unpackValues arity (unpairR x)))

private def envSlots (params : List Arity) : List Nat :=
  let nums := params.countP (· == 0)
  (params.zipIdx).map fun (arity, i) =>
    let earlier := (params.take i).countP (· == 0)
    if arity == 0 then earlier else nums + i - earlier

private def familyInput (arities : List Arity) (arity : Nat)
    (callbacks : List Term) : List Term × List Term := Id.run do
  let x := Term.bvar 0
  if arities.isEmpty then return (unpackValues arity x, [])
  let env := unpackValues arities.length (unpairL x)
  let (_, actuals) := (arities.zip (envSlots arities)).foldl (fun (next, args) (a, i) =>
    let e := env[i]!
    if a == 0 then (next, args.push e)
    else (next + 1, args.push (ap callbacks[next]! e))) (0, #[])
  return (unpackValues arity (unpairR x), actuals.toList)

private def familyValue (name : Name) (arities : List Arity) (arity : Nat)
    (callbacks : List Term) : Term :=
  if arities.isEmpty && arity == 1 then call name
  else
    let (args, params) := familyInput arities arity callbacks
    .lam `x (call name args params)

-- A callback holds its curried source function and its program on paired inputs.
private structure Callback where
  source : Term
  program : Compiled
  deriving Inhabited

private abbrev Callbacks := Nat → Option Callback

private initialize compiledNames :
    SimplePersistentEnvExtension Name (Std.HashSet Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun names name => names.insert name
    addImportedFn := fun sets => sets.foldl (fun names entries =>
      entries.foldl (fun names name => names.insert name) names)
      {}
  }

private def internalOwner (name : Name) (params : List Arity) : Name :=
  if params.isEmpty then name else name ++ `internal

/-- The code on packed inputs at the given callback code indices. -/
def compiledProgram? (env : Lean.Environment) (name : Name) (codes : List Term := []) :
    Option Term := do
  guard ((compiledNames.getState env).contains name)
  let core := CoreEnvironment.getState env
  let owner := match core.lookup name with
    | some (.function d) => internalOwner name d.functions
    | _ => name
  let some (.function d) := core.lookup (owner ++ `code) | none
  guard (codes.length == d.parameters.length)
  return call d.name [] codes

private def compiledFamily (name : Name) (params : List Arity) (arity : Nat)
    (callbacks : List Callback) : Compiled :=
  let values := callbacks.map (·.source)
  let codes := callbacks.map (·.program.code)
  let owner := internalOwner name params
  withCertificate (call (owner ++ `code) [] codes) fun _ =>
    let args := codes ++ callbacks.flatMap fun cb => [cb.source, cb.program.tr]
    ⟨familyValue name params arity values, call (owner ++ `trace) [] args,
      applyTheorem (owner ++ `computedBy) [] args (callbacks.map (·.program.correct))⟩

-- Pass each maximal numerical expression that is independent of the callback binders.
-- Closed expressions and repeated occurrences also get slots, so replacing a numerical
-- variable with a numeral or another capture leaves the program unchanged.
private partial def captureInputs (env : Core.Environment) (depth arity : Nat) (t : Term) :
    StateM (Array Term) Term := do
  if arity == 0 then
    if let some value := lower depth 0 t then
      let captures ← get
      modify (·.push value)
      return .bvar (depth + captures.size)
  match t with
  | .app f a =>
    let fn ← captureInputs env depth (arity + 1) f
    return .app fn (← captureInputs env depth 0 a)
  | .lam n b => return .lam n (← captureInputs env (depth + 1) (arity - 1) b)
  | .primrec b s =>
    return .primrec (← captureInputs env depth 0 b) (← captureInputs env depth 2 s)
  | .definition n fs =>
    let some (.function d) := env.lookup n | return t
    return .definition n (← (d.functions.zip fs).mapM fun (k, f) =>
      captureInputs env depth k f)
  | _ => return t

private def capture (env : Core.Environment) (arity : Nat) (f : Term) :
    Term × List Term :=
  let f := bind arity (beta (applyArgs (f.shift arity) (indices arity)))
  let (body, values) := (captureInputs env 0 arity f).run #[]
  (body, values.toList)

private def captureSource (count : Nat) (body : Term) : Term :=
  let fields := unpackValues count (.bvar 0)
  .lam `env (body.subst fun i => fields[i]!)

private def certifyValue (c : Compiled) (source : Thunk Term) : Compiled :=
  withCertificate c.code fun _ => Id.run do
    let source := source.get
    let x := Term.bvar 0
    let old := beta (ap c.value x)
    let original := beta (ap source x)
    if old == original then return { c.certificate.get with value := source }
    let (expected, equality) := simplify original
    let tr := ap c.tr x
    let h := Proof.ascribe (evalType c.code x expected tr) (.forallElim c.correct x)
    let correct := applyTheorem `Primrec.Computation.evaluates_congr
      [c.code, x, expected, original, tr] [] [mkEqSymm original expected equality, h]
    return ⟨source, c.tr, introAll (evalType c.code x original tr) correct⟩

private def project (kind : Name) (arg : Compiled) : Compiled :=
  combine `comp (basic kind) arg

private def projected (n : Nat) (input : Compiled) : Array Compiled :=
  (projections n).map (combine `comp · input)

private def contextualCallback (callbacks : Callbacks) (f : Term) :
    Option (Callback × ProgramInput) :=
  let rec stripLambdas (arity : Nat) : Term → Nat × Term
    | .lam _ b => stripLambdas (arity + 1) b
    | b => (arity, b)
  do
    let (arity, body) := stripLambdas 0 f
    let (.parameter i, env :: args) := getAppFnArgs body | none
    guard (args == indices arity)
    return (← callbacks i, .source (← lower arity 0 env))

private def etaPrefix : Term → Term
  | .lam n b => Id.run do
    let b := etaPrefix b
    if let .app f (.bvar 0) := b then
      if let some g := lower 1 0 f then return g
    return .lam n b
  | t => t

-- A partially applied named function keeps its program and captures the inputs that
-- precede the callback arguments. Each functional parameter supplies one environment field.
private def partialNamedCall (env : Core.Environment) (arity : Nat) (f : Term) :
    Option (FunctionDefinition × List Term × List Term) := do
  let applied := programHead (applyArgs (f.shift arity) (indices arity))
  let (.definition name fs, args) := getAppFnArgs applied | none
  let some (.function d) := env.lookup name | none
  guard (d.functions.any (· > 0))
  let fixed := args.length - arity
  guard (args.drop fixed == indices arity)
  return (d, ← fs.mapM (lower arity 0), ← (args.take fixed).mapM (lower arity 0))

-- A nested function argument can have a fixed prefix, as in `f d` inside a lambda over `d`.
-- Give the prefix one environment field. Substituting a partial application for `f` then
-- supplies its code and frame in the same positions as the formal callback.
private inductive ClosureField where
  | number (value : Term)
  | function (arity : Nat) (value : Term)

private partial def parameterBound : Term → Nat
  | .parameter i => i + 1
  | .app f a | .letE _ f a | .primrec f a => max (parameterBound f) (parameterBound a)
  | .lam _ b => parameterBound b
  | .definition _ fs => fs.foldl (fun k f => max k (parameterBound f)) 0
  | _ => 0

private partial def closureFields (env : Core.Environment) (first depth arity : Nat)
    (functionArg : Bool) (t : Term) : StateM (Array ClosureField) Term := do
  if arity == 0 then
    if let some value := lower depth 0 t then
      let i := (← get).size
      modify (·.push (.number value))
      return .bvar (depth + i)
  else if functionArg then
    if let some value := lower depth 0 t then
      let (h, args) := getAppFnArgs value
      if (h matches .definition ..) || ((h matches .parameter _) && !args.isEmpty) ||
          (h matches .lam ..) then
        let i := (← get).size
        modify (·.push (.function arity value))
        return .app (.parameter (first + i)) (.bvar (depth + i))
  match t with
  | .app f a =>
    -- Only a proper prefix can capture a fixed argument. A bare named head would
    -- compile itself again when its closure body is applied to the fresh arguments.
    let captures := (f matches .lam ..) || (f matches .app ..) || (f matches .definition _ (_::_))
    return .app (← closureFields env first depth (arity + 1) captures f)
      (← closureFields env first depth 0 false a)
  | .lam n b => return .lam n (← closureFields env first (depth + 1) (arity - 1) false b)
  | .letE _ a b => closureFields env first depth arity functionArg (b.subst0 a)
  | .primrec b s =>
    return .primrec (← closureFields env first depth 0 false b)
      (← closureFields env first depth 2 true s)
  | .definition n fs =>
    let some (.function d) := env.lookup n | return t
    return .definition n (← (d.functions.zip fs).mapM fun (k, f) =>
      closureFields env first depth k (k > 0) f)
  | _ => return t

mutual

private partial def compile (vars : Array Compiled) (callbacks : Callbacks)
    (input : Term) : CommandElabM Compiled := do
  let t := programHead input
  if (numeralValue? t).isSome then return constant t
  match t with
  | .bvar i =>
    let some c := vars[i]? | throwError "unbound variable while compiling primitive recursion"
    return c
  | .app (.primrec base step) arg =>
    let (r, captures) ← compileRec callbacks base step
    let fields ← captures.mapM fun input =>
      input.foldM (compile vars callbacks) (fun a b => pure (combine `pair a b))
    return combine `comp r (combine `pair (packPrograms fields) (← compile vars callbacks arg))
  | _ =>
    let (head, args) := getAppFnArgs t
    let argumentPrograms ← args.mapM (compile vars callbacks)
    match head with
    | .parameter i =>
      let some cb := callbacks i | throwError "missing program for function parameter {i}"
      let cap :: args := argumentPrograms | throwError "missing callback environment"
      return combine `comp cb.program (combine `pair cap (packPrograms args))
    | .succ =>
      let [a] := argumentPrograms | throwError "successor expects one numerical argument"
      return combine `comp (basic `succ) a
    | .definition name actuals =>
      let (f, captures) ← compileNamed callbacks name actuals
      if let ([], [a, b]) := (actuals, argumentPrograms) then
        return applyBinary (call name) (call name [resultAtInput a, resultAtInput b]) f a b
      -- Here the two input fields are the numerical parameter and the empty argument tuple.
      if let (.definition _ [], [.source capture], []) := (f.code, captures, argumentPrograms) then
        let a ← compile vars callbacks capture
        let source := bind 2 (call name [] [.bvar 1])
        return applyBinary source (call name [] [resultAtInput a]) f a (constant .zero)
      let ordinary := packPrograms argumentPrograms
      if actuals.isEmpty then return combine `comp f ordinary
      let fields ← captures.mapM fun input =>
        input.foldM (compile vars callbacks) (fun a b => pure (combine `pair a b))
      return combine `comp f (combine `pair (packPrograms fields) ordinary)
    | _ => throwError "unsupported expression in primitive-recursive compilation: {repr t}"

private partial def compileCallback (callbacks : Callbacks) (arity : Nat)
    (f : Term) : CommandElabM (Callback × ProgramInput) := do
  let f := etaPrefix (programHead f)
  if let some result := contextualCallback callbacks f then return result
  let env := CoreEnvironment.getState (← getEnv)
  if let .app g a := f then
    let (cb, frame) ← compileCallback callbacks (arity + 1) g
    -- Extend the previous frame by one fixed argument, whether the prefix was named or
    -- supplied as a function parameter. Repeated partial applications use this same layout.
    let fixed := basic `left
    let input := combine `pair (project `left fixed)
      (combine `pair (project `right fixed) (basic `right))
    let env := Term.bvar 0
    let source := Term.lam `env (ap (ap cb.source (unpairL env)) (unpairR env))
    let c := combine `comp cb.program input
    return (⟨source, certifyValue c (callbackValue arity source)⟩, .pair frame (.source a))
  if let .definition n (p :: ps) := f then
    let (family, fields) ← compileNamed callbacks n (p :: ps)
    let input := pair (.bvar arity) (packValues (indices arity))
    let source := bind (arity + 1) ((simplify (ap family.value input)).1)
    let cb := certifyValue family (callbackValue arity source)
    return (⟨source, cb⟩, ProgramInput.pack fields)
  if let some (d, actuals, fixed) := partialNamedCall env arity f then
    let mut fields := #[]
    let mut formals := #[]
    let mut programs := #[]
    for (k, arg) in d.functions.zip actuals do
      let slot := Term.bvar fields.size
      if k == 0 then
        fields := fields.push (.source arg)
        formals := formals.push slot
      else
        let (cb, value) ← compileCallback callbacks k arg
        formals := formals.push (.app (.parameter programs.size) slot)
        fields := fields.push value
        programs := programs.push cb
    let fixedArgs := fixed.zipIdx.map fun (_, i) => Term.bvar (fields.size + i)
    fields := fields ++ (fixed.map ProgramInput.source).toArray
    let template := applyArgs (.definition d.name formals.toList) fixedArgs
    let (cb, frame) ← compileClosure env (programs[·]?) arity template
      (programs.toList.map (·.source))
    -- The template above contains only field variables. Its empty environment is zero.
    let frame ← frame.foldM (fun
      | .bvar i => pure fields[i]!
      | .zero => pure (.source .zero)
      | _ => throwError "a callback template captured an expression outside its fields")
      (fun a b => pure (.pair a b))
    return (cb, frame)
  compileClosure env callbacks arity f []

-- Compile the closure once with its callback parameters abstract. Supplying their source
-- functions here gives the computation certificate at the same program indices.
private partial def compileClosure (env : Core.Environment) (callbacks : Callbacks)
    (arity : Nat) (f : Term) (sources : List Term) : CommandElabM (Callback × ProgramInput) := do
  let expanded := bind arity (programHead (applyArgs (f.shift arity) (indices arity)))
  let first := max (parameterBound expanded) sources.length
  let (body, values) := (closureFields env first 0 arity false expanded).run #[]
  let mut nested := #[]
  let mut frames := #[]
  for field in values do
    match field with
    | .number v =>
      nested := nested.push none
      frames := frames.push (.source v)
    | .function k v =>
      let (cb, frame) ← compileCallback callbacks k v
      nested := nested.push (some cb)
      frames := frames.push frame
  let lookup := fun i => if i < first then callbacks i else nested[i - first]?.join
  let ordinary := projected arity (basic `right)
  let fields := projected values.size (basic `left)
  let c ← compile (ordinary.reverse ++ fields) lookup
    (applyArgs (body.shift arity) (indices arity))
  let source := captureSource values.size body
  let original := (List.range first).map fun i =>
    ((callbacks i).map (·.source)).getD (sources[i]?.getD (.parameter i))
  let actuals := nested.toList.mapIdx fun i cb => (cb.map (·.source)).getD (.parameter (first + i))
  let source := source.instantiate (original ++ actuals)
  return (⟨source, certifyValue c (callbackValue arity source)⟩,
    ProgramInput.pack frames.toList)

private partial def compileNamed (callbacks : Callbacks) (name : Name) (actuals : List Term) :
    CommandElabM (Compiled × List ProgramInput) := do
  let env ← getEnv
  unless (compiledNames.getState env).contains name do
    throwError "missing compiled program for `{name}`; derive it with `derive_primrec {name}`"
  let some (.function d) := (CoreEnvironment.getState env).lookup name
    | throwError "missing numerical definition `{name}`"
  let params := d.functions
  unless actuals.length == params.length do
    throwError "expected {params.length} declaration parameters for `{name}`"
  let mut numeric := #[]
  let mut captured := #[]
  let mut compiled := #[]
  for (arity, actual) in params.zip actuals do
    if arity == 0 then numeric := numeric.push (.source actual)
    else
      let (program, environment) ← compileCallback callbacks arity actual
      compiled := compiled.push program
      captured := captured.push environment
  return (compiledFamily name params d.arity compiled.toList, (numeric ++ captured).toList)

private partial def compileRec (callbacks : Callbacks) (base step : Term) :
    CommandElabM (Compiled × List ProgramInput) := do
  let env := CoreEnvironment.getState (← getEnv)
  let step := bind 2 (programHead (applyArgs (step.shift 2) (indices 2)))
  let first := max (parameterBound base) (parameterBound step)
  let action := do
    let b ← closureFields env first 0 0 false base
    let s ← closureFields env first 0 2 false step
    return (b, s)
  let ((base, step), values) := action.run #[]
  let mut nested := #[]
  let mut frames := #[]
  for field in values do
    match field with
    | .number v =>
      nested := nested.push none
      frames := frames.push (.source v)
    | .function k v =>
      let (cb, frame) ← compileCallback callbacks k v
      nested := nested.push (some cb)
      frames := frames.push frame
  let lookup := fun i => if i < first then callbacks i else nested[i - first]?.join
  let locals := projections values.size
  let b ← compile locals lookup base
  let tail := basic `right
  let stepVars := #[project `right tail, project `left tail] ++
    locals.map (combine `comp · (basic `left))
  let s ← compile stepVars lookup (applyArgs (step.shift 2) (indices 2))
  return (recurse b s, frames.toList)

end

-- For translation, a function formal provides a code and the term for its runtime environment.
-- Add the environment argument before running the same compiler used by the derivation command.
private partial def prepareCallbackTerms (resolve : Nat → Option (Term × Term))
    (depth : Nat) (t : Term) : Term :=
  match t with
  | .parameter i => match resolve i with
    | some (_, env) => ap t (env.shift depth)
    | none => t
  | .app f a => ap (prepareCallbackTerms resolve depth f) (prepareCallbackTerms resolve depth a)
  | .lam n b => .lam n (prepareCallbackTerms resolve (depth + 1) b)
  | .letE n a b => .letE n (prepareCallbackTerms resolve depth a)
      (prepareCallbackTerms resolve (depth + 1) b)
  | .primrec b s => .primrec (prepareCallbackTerms resolve depth b)
      (prepareCallbackTerms resolve depth s)
  | .definition name fs => .definition name (fs.map (prepareCallbackTerms resolve depth))
  | _ => t

private def prepareCallbacks (resolve : Nat → Option (Term × Term)) :
    Callbacks × (Term → Term) :=
  let callbacks i := (resolve i).map fun (code, _) =>
    ⟨.parameter i, program code ⟨.parameter i, .zero, .trueIntro⟩⟩
  (callbacks, prepareCallbackTerms resolve 0)

-- Captures are returned to the caller as source expressions. A captured numerical result
-- may itself call a function formal. Remove the environment inserted at that call so the
-- caller can translate it using its original arity.
private partial def sourceCapture (resolve : Nat → Option (Term × Term)) (depth : Nat) :
    Term → Term
  | .app (.parameter i) a =>
    if (resolve i).any (fun (_, env) => a == env.shift depth) then .parameter i
    else .app (.parameter i) (sourceCapture resolve depth a)
  | .app f a => .app (sourceCapture resolve depth f) (sourceCapture resolve depth a)
  | .lam n b => .lam n (sourceCapture resolve (depth + 1) b)
  | .letE n v b => .letE n (sourceCapture resolve depth v) (sourceCapture resolve (depth + 1) b)
  | .primrec b s => .primrec (sourceCapture resolve depth b) (sourceCapture resolve depth s)
  | .definition n fs => .definition n (fs.map (sourceCapture resolve depth))
  | t => t

/-- Describe the callback body and the numerical values it captures in source order. -/
def captureProgramFunction (arity : Nat) (term : Term) : CommandElabM (Term × List Term) := do
  let env := CoreEnvironment.getState (← getEnv)
  return capture env arity (beta term)

private def restoreInput (resolve : Nat → Option (Term × Term)) (input : ProgramInput) :
    ProgramInput :=
  Id.run (input.foldM (fun t => pure (.source (sourceCapture resolve 0 t)))
    (fun a b => pure (.pair a b)))

/-- Return a callback program and its captured input. -/
def prepareProgramFunction (arity : Nat) (term : Term)
    (resolve : Nat → Option (Term × Term) := fun _ => none) :
    CommandElabM (Term × ProgramInput) := do
  let (callbacks, prepare) := prepareCallbacks resolve
  let (program, captured) ← compileCallback callbacks arity (prepare term)
  return (program.program.code, restoreInput resolve captured)

/-- Return a named program and its packed input. The resolver supplies the code and
environment of each function parameter in the caller. -/
def prepareProgramCall (name : Name) (actuals args : List Term)
    (resolve : Nat → Option (Term × Term) := fun _ => none) :
    CommandElabM (Term × ProgramInput) := do
  let ordinary := ProgramInput.pack (args.map .source)
  if actuals.isEmpty then
    let env ← getEnv
    if let some code := compiledProgram? env name then
      if let some (.function d) := (CoreEnvironment.getState env).lookup name then
        if d.parameters.isEmpty then return (code, ordinary)
  let (callbacks, prepare) := prepareCallbacks resolve
  let (c, captured) ← compileNamed callbacks name (actuals.map prepare)
  return (c.code, if actuals.isEmpty then ordinary else
    .pair (ProgramInput.pack (captured.map (restoreInput resolve))) ordinary)

/-- Return the inline recursion program and the fields of its captured environment. -/
def prepareProgramRecursion (base step : Term)
    (resolve : Nat → Option (Term × Term) := fun _ => none) :
    CommandElabM (Term × List ProgramInput) := do
  let (callbacks, prepare) := prepareCallbacks resolve
  let (r, captured) ← compileRec callbacks (prepare base) (prepare step)
  return (r.code, captured.map (restoreInput resolve))

private def publishComputation (name : Name) (source : Syntax) (c : Compiled)
    (codes params : List FunctionParameter) (premises : List Predicate)
    (alreadyDerived : Bool := false) : CommandElabM Compiled := do
  let codeName := name ++ `code
  let traceName := name ++ `trace
  let correctName := name ++ `computedBy
  let code := call codeName [] ((List.range codes.length).map Term.parameter)
  let args := (List.range params.length).map Term.parameter
  let tr := call traceName [] args
  let type := premises.foldr Predicate.imp (computedByType c.value code tr)
  let signature := params.map fun p => Parameter.function p.binderName p.arity
  if alreadyDerived then
    let core := CoreEnvironment.getState (← getEnv)
    let some (.theoremE previous) := core.lookup correctName
      | throwErrorAt source "missing computation theorem `{correctName}`"
    unless previous.parameters == signature && previous.type == type do
      throwErrorAt source "a different computation theorem already uses `{correctName}`"
  else
    publishChecked (.function ⟨codeName, codes, 0, c.code⟩) source
    publishChecked (.function ⟨traceName, params, 1, c.tr⟩) source
    let proof := premises.foldr (Proof.impIntro `h) c.correct
    publishChecked (.theoremE ⟨correctName, signature, type, proof⟩) source
  let hypotheses := (List.range premises.length).reverse.map Proof.hyp
  return program code ⟨c.value, tr, applyTheorem correctName [] args hypotheses⟩

private def publishEncoding (name : Name) (source : Syntax) (c : Compiled)
    (params : List FunctionParameter) (premises : List Predicate) : CommandElabM Unit := do
  let abstract := fun body => premises.foldr Predicate.imp body
  let discharge := fun proof => premises.foldr (Proof.impIntro `h) proof
  let signature := params.map fun p => Parameter.function p.binderName p.arity
  let encodesName := name ++ `encodes
  let encodesType := Predicate.definition `Primrec.Encodes [c.value, c.code] []
  let encodes := applyTheorem `Primrec.encodes_of_computedBy []
    [c.value, c.tr, c.code] [c.correct]
  publishChecked
    (.theoremE ⟨encodesName, signature, abstract encodesType, discharge encodes⟩) source
  let args := (List.range params.length).map Term.parameter
  let hypotheses := (List.range premises.length).reverse.map Proof.hyp
  let encoding := applyTheorem encodesName [] args hypotheses
  let primrec := applyTheorem `Primrec.of_encodes [] [c.value, c.code] [encoding]
  let primrecType := Predicate.definition `Primrec [c.value] []
  publishChecked (.theoremE
    ⟨name ++ `primrec, signature, abstract primrecType, discharge primrec⟩) source

private def publishSpecialization (source : Syntax) (d : FunctionDefinition) (name : Name) :
    CommandElabM Unit := do
  let codes := d.parameters.map fun p =>
    if p.arity == 0 then p else ⟨0, p.binderName.name.appendAfter "Code"⟩
  let mut params := codes
  let mut premises := #[]
  let mut actuals := #[]
  let mut callbacks := #[]
  let mut numeric := #[]
  let count := d.functions.countP (· > 0)
  for (p, i) in d.parameters.zipIdx do
    let code := Term.parameter i
    if p.arity == 0 then
      actuals := actuals.push code
      numeric := numeric.push code
    else
      let slot := params.length
      params := params ++
        [p, ⟨1, p.binderName.name.appendAfter "Trace"⟩]
      let f := Term.parameter slot
      let tr := Term.parameter (slot + 1)
      let value := if p.arity == 1 then f else
        .lam `x (applyArgs f (unpackValues p.arity (.bvar 0)))
      let program := program code ⟨value, tr, .hyp (count - 1 - callbacks.size)⟩
      let callback := combine `comp program (basic `right)
      let callback := { callback with code := call `Primrec.Code.onRight [code] }
      callbacks := callbacks.push ⟨.lam `env f, callback⟩
      actuals := actuals.push f
      premises := premises.push (computedByType value code tr)
  let internal := compiledFamily name d.functions d.arity callbacks.toList
  let environment := packValues (numeric.toList ++ List.replicate count .zero)
  let specialized := combine `comp internal (combine `pair (constant environment) identity)
  let code := call `Primrec.Code.fixLeft [internal.code, environment]
  let specialized := { specialized with code }
  let value := Term.lam `x (call d.name (unpackValues d.arity (.bvar 0)) actuals.toList)
  let publicProgram ← publishComputation name source (certifyValue specialized value)
    codes params premises.toList
  publishEncoding name source publicProgram params premises.toList

private def compileDefinition (source : Syntax) (d : FunctionDefinition) (owner : Name)
    (sourceTerm? : Option Term := none) : CommandElabM Unit := do
  let arities := d.functions
  let functions := d.parameters.filter (·.arity > 0)
  let codes := functions.map fun p => ⟨0, p.binderName.name.appendAfter "Code"⟩
  let mut params := codes
  let mut callbacks : Array Callback := #[]
  let mut premises := #[]
  for (p, i) in functions.zipIdx do
    let slot := params.length
    params := params ++
      [⟨p.arity + 1, p.binderName⟩, ⟨1, p.binderName.name.appendAfter "Trace"⟩]
    let code := Term.parameter i
    let f := Term.parameter slot
    let tr := Term.parameter (slot + 1)
    let value := callbackValue p.arity f
    let correctness := Proof.hyp (functions.length - 1 - i)
    callbacks := callbacks.push ⟨f, program code ⟨value, tr, correctness⟩⟩
    premises := premises.push (computedByType value code tr)
  let lookup := fun i => if codes.length ≤ i && (i - codes.length) % 2 == 0 then
    callbacks[(i - codes.length) / 2]? else none
  let (argumentPrograms, environmentPrograms) := if arities.isEmpty then
    (projections d.arity, #[])
  else (projected d.arity (basic `right), (projected arities.length (basic `left)).reverse)
  let (_, actuals) := (arities.zip (envSlots arities)).foldl (fun (i, actuals) (a, field) =>
    let env := Term.bvar (d.arity + arities.length - 1 - field)
    if a == 0 then (i, actuals.push env)
    else (i + 1, actuals.push (ap (Term.parameter (codes.length + 2 * i)) env))) (0, #[])
  let callbackTerms := callbacks.toList.map (·.source)
  let original := sourceTerm?.getD (familyValue d.name arities d.arity callbackTerms)
  let (fields, parameters) := familyInput arities d.arity callbackTerms
  let expanded := Term.lam `x (applyArgs (d.body.instantiate parameters) fields)
  let alreadyDerived := (compiledNames.getState (← getEnv)).contains owner
  let c ← if alreadyDerived then
    pure (compiledFamily owner arities d.arity callbacks.toList)
  else
    compile (argumentPrograms.reverse ++ environmentPrograms) lookup
      (applyArgs (if actuals.isEmpty then d.body else d.body.instantiate actuals.toList)
        (indices d.arity))
  let certificate := (certifyValue c expanded).certificate.get
  let internal ← publishComputation (internalOwner owner arities) source
    (program c.code { certificate with value := original }) codes params premises.toList
    alreadyDerived
  unless alreadyDerived do
    if arities.isEmpty then
      publishEncoding owner source internal params premises.toList
    else
      publishSpecialization source d owner
    modifyEnv (compiledNames.addEntry · owner)

syntax (name := derivePrimrec) "derive_primrec " ident : praDecl
syntax (name := derivePrimrecBatch) "derive_primrec " ident ident+ : praDecl
syntax (name := derivePrimrecExpr) "derive_primrec " "(" praExpr ")" " as " ident : praDecl

private def elaborateOne (stx : Syntax) : CommandElabM Unit := do
  match stx with
  | `(praDecl| derive_primrec $id:ident) =>
    let env := CoreEnvironment.getState (← getEnv)
    match ← resolveDeclaration? env id.getId with
    | some (.function d) => compileDefinition id.raw d d.name
    | _ =>
      let some (.function signature) ← resolveSignature? env id.getId
        | throwErrorAt id "expected a numerical PRA declaration"
      let some primitive := primitiveDeclaration? signature.name
        | throwErrorAt id "expected a numerical PRA declaration"
      let .term body := primitive.construction
        | throwErrorAt id "expected a numerical PRA declaration"
      compileDefinition id.raw ⟨signature.name, signature.parameters, signature.arity, body⟩
        signature.name (some body)
  | `(praDecl| derive_primrec ($e:praExpr) as $result:ident) =>
    let body ← elaborateNumericalExpression e 1
    let d : FunctionDefinition := ⟨.anonymous, [], 1, body⟩
    let owner := (← getCurrNamespace) ++ result.getId
    compileDefinition e.raw d owner (some body)
  | _ => throwUnsupportedSyntax

@[command_elab LeanPRA.Surface.praEntry]
def elaboratePrimrec : CommandElab := fun stx => do
  let declaration := stx[0]
  if declaration.isOfKind ``derivePrimrecBatch then
    for id in #[declaration[1]] ++ declaration[2].getArgs do
      let id : TSyntax `ident := ⟨id⟩
      let single ← `(praDecl| derive_primrec $id:ident)
      elaborateOne single
  else
    elaborateOne declaration

end LeanPRA.Library.Computability.Derive.Command
