module

public meta import LeanPRA.Surface.IDE

/-!
# Elaborating PRA syntax into Core expressions

Elaboration from `praExpr` and `praDecl` syntax to Core expressions and declarations:

- `elaborateDeclaration` elaborates a declaration, checks it with `Core.checkDeclaration`,
  and publishes it.
- `elaborateCheck` elaborates an expression, infers its Core type, and logs its signature.
- `elaboratePrint` looks up a declaration and logs its delaborated syntax.

`Scope` maps source binder names to Core variable indices and records syntax spans for error
locations, hover info, go-to-definition, and goal snapshots.
-/

public meta section

namespace LeanPRA.Surface

open Lean Elab Command
open Core (Predicate Proof VariableKind)

/-- A scope has a checked environment and well-formed proof hypotheses. Numerical arities and
parameter signatures are well formed by construction. Formula annotations are checked before
binding; inferred hypotheses come from checked proofs or formed connectives. -/
private structure Scope where
  environment : Core.Environment
  context : Core.Context := {}
  names : Names := {}
  bindings : List GoalBinding := []
  aliases : List (Name × Core.Term) := []
  predicateAliases : List (Name × Predicate) := []
  references : List (Name × Syntax) := []
  parentExpression : Syntax := .missing

private structure Origin where
  site : Core.CheckSite
  ref : Syntax
  names : Names

private abbrev Origins := Array Origin
private abbrev ObjectElabM := ReaderT Scope (StateT Origins CommandElabM)

private def getMaxDepth : ObjectElabM Nat :=
  return pra.maxDepth.get (← getOptions)

private def objectName (stx : Syntax) : Name := stx.getId.eraseMacroScopes

private def binderName (stx : Syntax) : Name :=
  if stx[0].isIdent then objectName stx[0] else .anonymous

private def shiftLocalBinding : GoalBinding → GoalBinding
  | .local n i => .local n (i + 1)
  | .termAlias n t => .termAlias n t.shift
  | .predicateAlias n p => .predicateAlias n p.shift
  | other => other

private def shiftProofBinding : GoalBinding → GoalBinding
  | .proof n i => .proof n (i + 1)
  | other => other

private def Scope.pushLocal (s : Scope) (n : Name) (arity : Nat := 0)
    (ref : Syntax := .missing) : Scope :=
  { s with
    context := s.context.pushLocal arity
    names := { s.names with locals := n :: s.names.locals }
    bindings := .local n 0 :: s.bindings.map shiftLocalBinding
    references := (n, ref) :: s.references
    aliases := (s.aliases.filter (·.1 != n)).map fun (name, value) => (name, value.shift)
    predicateAliases := (s.predicateAliases.filter (·.1 != n)).map
      fun (name, value) => (name, value.shift) }

/-- Extend the scope with an already formed formula. -/
private def Scope.pushProof (s : Scope) (n : Name) (type : Predicate)
    (ref : Syntax := .missing) : Scope :=
  { s with
    context := s.context.pushProof type
    names := { s.names with proofs := n :: s.names.proofs }
    bindings := .proof n 0 :: s.bindings.map shiftProofBinding
    references := (n, ref) :: s.references
    aliases := s.aliases.filter (·.1 != n)
    predicateAliases := s.predicateAliases.filter (·.1 != n) }

/-- Push an unnamed, already formed proof hypothesis and shift existing proof indices. -/
private def Scope.pushAnonymousProof (s : Scope) (type : Predicate) : Scope :=
  { s with
    context := s.context.pushProof type
    names := { s.names with proofs := .anonymous :: s.names.proofs }
    bindings := s.bindings.map shiftProofBinding }

private def Scope.addAlias (s : Scope) (n : Name) (value : Core.Term)
    (ref : Syntax := .missing) : Scope :=
  { s with
    bindings := .termAlias n value :: s.bindings
    references := (n, ref) :: s.references
    aliases := (n, value) :: s.aliases.filter (·.1 != n)
    predicateAliases := s.predicateAliases.filter (·.1 != n) }

private def Scope.addPredicateAlias (s : Scope) (n : Name) (value : Predicate)
    (ref : Syntax := .missing) : Scope :=
  { s with
    bindings := .predicateAlias n value :: s.bindings
    references := (n, ref) :: s.references
    aliases := s.aliases.filter (·.1 != n)
    predicateAliases := (n, value) :: s.predicateAliases.filter (·.1 != n) }

private def binding (n : Name) : ObjectElabM (Option VariableKind) := do
  return ((← read).bindings.find? (·.name == n)).map fun
    | .local .. | .termAlias .. => .local
    | .functionParameter .. => .functionParameter
    | .predicateParameter .. | .predicateAlias .. => .predicateParameter
    | .proof .. => .proof

private def remember (stx : Syntax) (subject : Core.CheckSubject) : ObjectElabM Unit := do
  if stx.isMissing then return
  let s ← read
  modify (·.push ⟨⟨s.context, subject⟩, stx, s.names⟩)
  let id := if stx.isIdent then stx else stx[0]
  let target := if id.isIdent then
    ((s.references.find? (·.1 == objectName id)).map (·.2)).getD .missing else .missing
  addExpressionInfo stx s.environment s.context s.names subject target

private def missingRange (parent : Syntax) : Syntax := Id.run do
  let some start := parent.getTailPos? (canonicalOnly := true) | return .missing
  let stop := start.increaseBy (max 1 parent.getTrailingSize)
  return Syntax.atom (.synthetic start stop true) ""

private def withGoal (stx : Syntax) (expected : Option GoalTarget)
    (infer : Nat → α → Scope → Core.CheckResult GoalTarget) (action : ObjectElabM α) :
    ObjectElabM α := do
  unless (← getInfoState).enabled do return ← action
  let s ← read
  let depth ← getMaxDepth
  let ref := if (stx.getRange? (canonicalOnly := true)).isSome then stx
    else missingRange s.parentExpression
  let info target := makeGoalInfo ref s.environment s.context s.names s.bindings.reverse target
  let action := withReader (fun s => { s with parentExpression := ref }) action
  withInfoContext' action (fun result => do
    let target := match expected with
      | some type => some type
      | none => (infer depth result s).toOption
    return .inl (← info target)) (info expected)

private def rejectHole (stx : Syntax) : ObjectElabM Unit := do
  if stx.isMissing then throwErrorAt stx "incomplete PRA expression"
  if stx.isOfKind `LeanPRA.Surface.recoveredHole then
    throwErrorAt (← read).parentExpression "incomplete PRA expression"
  if stx.isOfKind ``praHole || stx.isOfKind ``praSyntheticHole then
    throwErrorAt stx "incomplete PRA expression"

private def withLocal (ref : Syntax) (n : Name) (arity : Nat) (action : ObjectElabM α) :
    ObjectElabM α :=
  withReader (·.pushLocal n arity ref) do
    remember ref (.term (.bvar 0))
    action

private def withProof (ref : Syntax) (n : Name) (type : Predicate) (action : ObjectElabM α) :
    ObjectElabM α :=
  withReader (·.pushProof n type ref) do
    remember ref (.proof (.hyp 0))
    action

private def withAlias (ref : Syntax) (value : Core.Term) (action : ObjectElabM α) :
    ObjectElabM α :=
  withReader (·.addAlias (objectName ref) value ref) do
    remember ref (.term value)
    action

private def withPredicateAlias (ref : Syntax) (value : Predicate) (action : ObjectElabM α) :
    ObjectElabM α :=
  withReader (·.addPredicateAlias (objectName ref) value ref) do
    remember ref (.predicate value)
    action

private def checked (stx : Syntax) (result : Core.CheckResult α) : ObjectElabM α := do
  match result with
  | .ok value => return value
  | .error error =>
    let origins ← get
    let origin := error.site.bind fun site => origins.findRev? (·.site == site)
    let ref := (origin.map (·.ref)).getD stx
    match error.reason with
    | .proofTypeMismatch expected actual .. =>
      let names := (origin.map (·.names)).getD (← read).names
      let expected ← delabPredicate names expected
      let actual ← delabPredicate names actual
      throwErrorAt ref "proof type mismatch\nexpected: {← formatSyntax `praExpr expected}\n\
        inferred: {← formatSyntax `praExpr actual}"
    | _ => throwErrorAt ref "{error.message}"

private def inferTerm (stx : Syntax) (t : Core.Term) : ObjectElabM Nat := do
  let s ← read
  checked stx (Core.inferTerm (← getMaxDepth) s.environment s.context t)

private def inferPredicate (stx : Syntax) (p : Predicate) :
    ObjectElabM Core.PredicateSignature := do
  let s ← read
  checked stx (Core.inferPredicate (← getMaxDepth) s.environment s.context p)

private def inferProof (stx : Syntax) (p : Proof) : ObjectElabM Predicate := do
  let s ← read
  checked stx (Core.inferProof (← getMaxDepth) s.environment s.context p)

private def reduceFormula (stx : Syntax) (p : Predicate) : ObjectElabM Predicate := do
  let s ← read
  checked stx ((Core.reduceFormula (← getMaxDepth) s.environment p)
    |>.withSite s.context (.predicate p))

-- Reduce to WHNF so the outer connective is visible without normalizing subformulas.
private def exposeFormula (stx : Syntax) (p : Predicate) : ObjectElabM Predicate := do
  let s ← read
  let depth ← getMaxDepth
  let _ ← checked stx (Core.inferFormula depth s.environment s.context p)
  checked stx ((Core.whnfPredicate depth s.environment p)
    |>.withSite s.context (.predicate p))

private partial def unparen (stx : Syntax) : Syntax :=
  match stx with
  | `(praExpr| ($e:praExpr)) => unparen e
  | _ => stx

private partial def spine (stx : Syntax) (args : List Syntax := []) : Syntax × List Syntax :=
  match unparen stx with
  | `(praExpr| $f:praExpr $a:praExpr) => spine f (a.raw :: args)
  | head => (head, args)

private partial def numericalArity? (stx : Syntax) : Option Nat :=
  match unparen stx with
  | `(praExpr| $id:ident) => if objectName id == `Nat then some 0 else none
  | `(praExpr| $a:praExpr → $b:praExpr) => do
    if numericalArity? a != some 0 then none else (· + 1) <$> numericalArity? b
  | _ => none

private partial def predicateSignature? (stx : Syntax) : Option Core.PredicateSignature :=
  match unparen stx with
  | `(praExpr| Prop) => some ⟨0, .prop⟩
  | `(praExpr| $id:ident) =>
    if objectName id == `QFProp then some ⟨0, .qf⟩
    else if objectName id == `Prop then some ⟨0, .prop⟩ else none
  | `(praExpr| $a:praExpr → $b:praExpr) => do
    if numericalArity? a != some 0 then none
    else let s ← predicateSignature? b; some { s with arity := s.arity + 1 }
  | _ => none

private def lookup (stx : Syntax) : ObjectElabM Core.Declaration := do
  let n := objectName stx
  match ← resolveDeclaration? (← read).environment n with
  | some d => addDeclarationInfo stx d; return d
  | none =>
    addUnresolvedInfo stx
    throwErrorAt stx "unknown PRA name `{n}`"

private def lambdaBody (stx : Syntax) : ObjectElabM (Name × Option Syntax × Syntax × Syntax) := do
  let (xs, type, body) ← match unparen stx with
    | `(praExpr| fun $xs:praFunBinder* => $body:praExpr) => pure (xs, none, body)
    | `(praExpr| fun $xs:praFunBinder* : $type:praExpr => $body:praExpr) =>
      pure (xs, some type, body)
    | _ => throwErrorAt stx "expected a branch beginning with `fun`"
  if xs.isEmpty then throwErrorAt stx "expected a binder"
  let body : TSyntax `praExpr :=
    if body.raw.isOfKind `LeanPRA.Surface.recoveredHole &&
        (body.raw.getRange? (canonicalOnly := true)).isNone then
      ⟨Syntax.node (missingRange stx).getHeadInfo `LeanPRA.Surface.recoveredHole #[]⟩
    else body
  let rest := xs.extract 1 xs.size
  let body ← if rest.isEmpty then pure body else
    match type with
    | none => `(praExpr| fun $rest:praFunBinder* => $body)
    | some type => `(praExpr| fun $rest:praFunBinder* : $type => $body)
  return (binderName xs[0]!.raw, type.map (·.raw), body.raw, xs[0]!.raw)

private def requirePlainBinder (ref : Syntax) : ObjectElabM Unit := do
  if ref.isOfKind ``praTupleBinder then
    throwErrorAt ref "a tuple pattern requires a conjunction or existential proof"

private def plainLambdaBody (stx : Syntax) :
    ObjectElabM (Name × Option Syntax × Syntax × Syntax) := do
  let result ← lambdaBody stx
  requirePlainBinder result.2.2.2
  return result

private def tuplePattern (binders : List Syntax) : ObjectElabM Syntax := do
  match binders with
  | [] => throwError "expected a tuple component"
  | [binder] => return binder
  | first :: rest =>
    let first : TSyntax `praFunBinder := ⟨first⟩
    let rest : Array (TSyntax `praFunBinder) := rest.toArray.map (⟨·⟩)
    return (← `(praFunBinder| ($first:praFunBinder, $rest:praFunBinder,*))).raw

private def numericalBinder (type : Option Syntax) : ObjectElabM Unit := do
  if let some type := type then
    unless numericalArity? type == some 0 do
      throwErrorAt type "a numerical lambda binder must have type Nat"

private def requireExpected (stx : Syntax) (expected : Option Predicate) : ObjectElabM Predicate :=
  match expected with
  | some type => pure type
  | none => throwErrorAt stx "an expected formula is needed; add a type ascription"

private partial def abstractNumberTerm (argument : Core.Term) (depth : Nat) :
    Core.Term → Core.Term
  | t =>
    if t == argument.shift depth then .bvar depth else
    match t with
    | .lam hint b => .lam hint (abstractNumberTerm argument (depth
        + 1) b)
    | .app f a => .app (abstractNumberTerm argument depth f) (abstractNumberTerm argument depth a)
    | .letE hint a b => .letE hint (abstractNumberTerm argument
        depth a)
        (abstractNumberTerm argument (depth + 1) b)
    | .primrec b s n => .primrec (abstractNumberTerm argument depth b)
        (abstractNumberTerm argument depth s) (abstractNumberTerm argument depth n)
    | .definition n fs => .definition n (fs.map (abstractNumberTerm argument depth))
    | t => t

private def abstractNumber (argument : Core.Term) (depth : Nat) : Predicate → Predicate
  | .equal a b => .equal (abstractNumberTerm argument depth a) (abstractNumberTerm argument depth b)
  | .imp a b => .imp (abstractNumber argument depth a) (abstractNumber argument depth b)
  | .and a b => .and (abstractNumber argument depth a) (abstractNumber argument depth b)
  | .or a b => .or (abstractNumber argument depth a) (abstractNumber argument depth b)
  | .all p => .all (abstractNumber argument depth p)
  | .ex p => .ex (abstractNumber argument depth p)
  | .lam hint p => .lam hint (abstractNumber argument (depth + 1) p)
  | .app p n => .app (abstractNumber argument depth p) (abstractNumberTerm argument depth n)
  | .letTerm hint a p => .letTerm hint (abstractNumberTerm
      argument depth a) (abstractNumber argument depth p)
  | .letPredicate hint q p =>
      .letPredicate hint (abstractNumber argument depth q) (abstractNumber
          argument depth p)
  | .definition n fs ps => .definition n (fs.map (abstractNumberTerm argument depth))
      (ps.map (abstractNumber argument depth))
  | p => p

private partial def expressionKind (stx : Syntax) : ObjectElabM Core.DeclarationKind := do
  match unparen stx with
  | `(praExpr| $_n:num) => return .function
  | `(praExpr| fun $_xs:praFunBinder* => $_body:praExpr) =>
    let (name, _, body, ref) ← lambdaBody stx
    if ref.isOfKind ``praTupleBinder then return .theoremE
    withReader (·.pushLocal name) (expressionKind body)
  | `(praExpr| fun $_xs:praFunBinder* : $type:praExpr => $_body:praExpr) =>
    if numericalArity? type != some 0 then return .theoremE
    let (name, _, body, ref) ← lambdaBody stx
    if ref.isOfKind ``praTupleBinder then return .theoremE
    withReader (·.pushLocal name) (expressionKind body)
  | `(praExpr| let $id:ident := $value:praExpr; $body:praExpr) =>
    match ← expressionKind value with
    | .function => withReader (·.addAlias (objectName id) .zero) (expressionKind body)
    | .theoremE => withReader (·.pushProof (objectName id) .true) (expressionKind body)
    | .predicate => withReader (·.addPredicateAlias (objectName id) .true) (expressionKind body)
  | `(praExpr| let $id:ident : $type:praExpr := $_value:praExpr; $body:praExpr) =>
    if (numericalArity? type).isSome then
      withReader (·.addAlias (objectName id) .zero) (expressionKind body)
    else if (predicateSignature? type).isSome then
      withReader (·.addPredicateAlias (objectName id) .true) (expressionKind body)
    else withReader (·.pushProof (objectName id) .true) (expressionKind body)
  | `(praExpr| ($_value:praExpr : $type:praExpr)) =>
    if (numericalArity? type).isSome then return .function
    if (predicateSignature? type).isSome then return .predicate
    return .theoremE
  | `(praExpr| $_a:praExpr = $_b:praExpr) | `(praExpr| $_a:praExpr → $_b:praExpr)
  | `(praExpr| $_a:praExpr ∧ $_b:praExpr) | `(praExpr| $_a:praExpr ∨ $_b:praExpr)
  | `(praExpr| $_a:praExpr ↔ $_b:praExpr)
  | `(praExpr| ¬$_a:praExpr) | `(praExpr| ∀ $_xs:praBinder* : Nat, $_body:praExpr)
  | `(praExpr| ∃ $_xs:praBinder* : Nat, $_body:praExpr)
  | `(praExpr| ∀ $_xs:praBinder*, $_body:praExpr)
  | `(praExpr| ∃ $_xs:praBinder*, $_body:praExpr) => return .predicate
  | _ =>
    let (head, args) := spine stx
    if !args.isEmpty then return ← expressionKind head
    if let `(praExpr| $id:ident) := head then
      let n := objectName id
      match ← binding n with
      | some .local | some .functionParameter => return .function
      | some .predicateParameter => return .predicate
      | some .proof => return .theoremE
      | none =>
        match builtinKind? n with
        | some .function => return .function
        | some .predicate => return .predicate
        | _ => pure ()
        if let some d ← resolveDeclaration? (← read).environment n then
          return d.kind
    return .theoremE

mutual

private partial def term (stx : Syntax) (expected : Option Nat := none) :
    ObjectElabM Core.Term :=
  withGoal stx (expected.map .term)
      (fun depth t s => (Core.inferTerm depth s.environment s.context t)
        |>.map .term) do
    rejectHole (unparen stx)
    let t ← termBody (unparen stx) expected
    remember stx (.term t)
    return t

private partial def termBody (stx : Syntax) (expected : Option Nat) : ObjectElabM Core.Term := do
  match stx with
  | `(praExpr| $n:num) =>
    return (List.range n.getNat).foldl (fun t _ => .app .succ t) .zero
  | `(praExpr| fun $_xs:praFunBinder* => $_body:praExpr)
  | `(praExpr| fun $_xs:praFunBinder* : $_type:praExpr => $_body:praExpr) =>
    let (n, type, b, ref) ← plainLambdaBody stx
    numericalBinder type
    let bodyArity := expected.bind fun k => if k == 0 then none else some (k - 1)
    return .lam n (← withLocal ref n 0 (term b bodyArity))
  | `(praExpr| let $id:ident := $value:praExpr; $body:praExpr) =>
    let value ← term value
    let arity ← inferTerm stx value
    return .letE (objectName id) value (← withLocal id (objectName id) arity (term
        body expected))
  | `(praExpr| let $id:ident : $type:praExpr := $value:praExpr; $body:praExpr) =>
    let some arity := numericalArity? type | throwErrorAt type "expected a numerical type"
    let value ← term value arity
    let s ← read
    checked stx (Core.checkTerm (← getMaxDepth) s.environment s.context value arity)
    return .letE (objectName id) value (← withLocal id (objectName id) arity (term
        body expected))
  | `(praExpr| ($value:praExpr : $type:praExpr)) =>
    let some arity := numericalArity? type | throwErrorAt type "expected a numerical type"
    let value ← term value arity
    let s ← read
    checked stx (Core.checkTerm (← getMaxDepth) s.environment s.context value arity)
    return value
  | _ =>
    let (head, args) := spine stx
    let `(praExpr| $id:ident) := head | do
      if args.isEmpty then throwErrorAt head "expected a numerical expression"
      return ← args.foldlM (fun f a => return .app f (← term a (some 0))) (← term head)
    let n := objectName id
    let s ← read
    let (value, rest) ← match ← binding n with
      | some .local =>
        let value := ((s.aliases.find? (·.1 == n)).map (·.2)).getD
          (Core.Term.bvar (s.names.locals.idxOf n))
        pure (value, args)
      | some .functionParameter => pure (Core.Term.parameter (s.names.functions.idxOf n), args)
      | some _ => throwErrorAt id "`{n}` is not a numerical name"
      | none =>
        if n == `S then pure (Core.Term.succ, args)
        else if n == `primrec then
          match args with
          | b :: step :: arg :: rest =>
            pure (Core.Term.primrec (← term b (some 0)) (← term step (some 2))
              (← term arg (some 0)), rest)
          | _ => throwErrorAt stx "`primrec` requires a base, a binary step, and a number"
        else
          let .function d ← lookup id | throwErrorAt id "expected a function definition"
          if args.length < d.functions.length then
            throwErrorAt stx "`{n}` requires {d.functions.length} explicit function parameters"
          let actuals ← ((args.take d.functions.length).zip d.functions).mapM fun (arg, arity) =>
            term arg arity
          pure (Core.Term.definition d.name actuals, args.drop d.functions.length)
    remember head (.term value)
    rest.foldlM (fun f a => return .app f (← term a (some 0))) value

private partial def predicate (stx : Syntax) (expected : Option Core.PredicateSignature := none) :
    ObjectElabM Predicate :=
  withGoal stx (expected.map .predicate)
      (fun depth p s => (Core.inferPredicate depth
        s.environment s.context p).map .predicate) do
    rejectHole (unparen stx)
    let p ← predicateBody (unparen stx) expected
    remember stx (.predicate p)
    return p

/-- Elaborate a formula annotation before using it as an expected type or local hypothesis. -/
private partial def formula (stx : Syntax) : ObjectElabM Predicate := do
  let p ← predicate stx
  let s ← read
  let _ ← checked stx (Core.inferFormula (← getMaxDepth) s.environment s.context p)
  return p

private partial def predicateBody (stx : Syntax)
    (expected : Option Core.PredicateSignature) : ObjectElabM Predicate := do
  let formula : Core.PredicateSignature := ⟨0, (expected.map (·.sort)).getD .prop⟩
  match stx with
  | `(praExpr| ($value:praExpr : $type:praExpr)) =>
    let some sig := predicateSignature? type | throwErrorAt type "expected a predicate type"
    let value ← predicate value sig
    let s ← read
    checked stx (Core.checkPredicate (← getMaxDepth) s.environment s.context value sig)
    return value
  | `(praExpr| $a:praExpr = $b:praExpr) => return .equal (← term a (some 0)) (← term b (some 0))
  | `(praExpr| $a:praExpr → $b:praExpr) =>
    return .imp (← predicate a (some formula)) (← predicate b (some formula))
  | `(praExpr| $a:praExpr ∧ $b:praExpr) =>
    return .and (← predicate a (some formula)) (← predicate b (some formula))
  | `(praExpr| $a:praExpr ∨ $b:praExpr) =>
    return .or (← predicate a (some formula)) (← predicate b (some formula))
  | `(praExpr| $a:praExpr ↔ $b:praExpr) => iffPredicate a b formula
  | `(praExpr| ¬$a:praExpr) => return .imp (← predicate a (some formula)) .false
  | `(praExpr| fun $_xs:praFunBinder* => $_body:praExpr)
  | `(praExpr| fun $_xs:praFunBinder* : $_type:praExpr => $_body:praExpr) =>
    let (n, type, b, ref) ← plainLambdaBody stx
    numericalBinder type
    let bodySignature := expected.map fun sig => { sig with arity := sig.arity - 1 }
    return .lam n (← withLocal ref n 0 (predicate b bodySignature))
  | `(praExpr| let $id:ident := $value:praExpr; $body:praExpr) =>
    predicateLet stx id none value body expected
  | `(praExpr| let $id:ident : $type:praExpr := $value:praExpr; $body:praExpr) =>
    predicateLet stx id (some type.raw) value body expected
  | `(praExpr| ∀ $xs:praBinder* : Nat, $body:praExpr)
  | `(praExpr| ∀ $xs:praBinder*, $body:praExpr) =>
    quantify true xs.toList body
  | `(praExpr| ∃ $xs:praBinder* : Nat, $body:praExpr)
  | `(praExpr| ∃ $xs:praBinder*, $body:praExpr) =>
    quantify false xs.toList body
  | _ =>
    let (head, args) := spine stx
    let `(praExpr| $id:ident) := head | do
      if args.isEmpty then throwErrorAt head "expected a predicate expression"
      return ← args.foldlM (fun p a => return .app p (← term a (some 0))) (← predicate head)
    let n := objectName id
    let s ← read
    let (value, rest) ← match ← binding n with
      | some .predicateParameter =>
        let value := ((s.predicateAliases.find? (·.1 == n)).map (·.2)).getD
          (Predicate.parameter (s.names.predicates.idxOf n))
        pure (value, args)
      | some _ => throwErrorAt id "`{n}` is not a predicate name"
      | none =>
        if n == `True then pure (Predicate.true, args)
        else if n == `False then pure (Predicate.false, args)
        else
          let .predicate d ← lookup id | throwErrorAt id "expected a predicate definition"
          let (fs, ps, rest) ← declarationArguments stx n d.parameters args
          pure (Predicate.definition d.name fs ps, rest)
    remember head (.predicate value)
    rest.foldlM (fun p a => return .app p (← term a (some 0))) value

private partial def iffPredicate (a b : Syntax) (formula : Core.PredicateSignature) :
    ObjectElabM Predicate := do
  let a ← predicate a (some formula)
  let b ← predicate b (some formula)
  return .and (.imp a b) (.imp b a)

private partial def predicateLet (stx id : Syntax) (annotation : Option Syntax)
    (value body : Syntax) (expected : Option Core.PredicateSignature) : ObjectElabM Predicate := do
  let kind ← match annotation with
    | some type =>
      if (numericalArity? type).isSome then pure Core.DeclarationKind.function
      else if (predicateSignature? type).isSome then pure .predicate
      else throwErrorAt type "expected a numerical or predicate type"
    | none => expressionKind value
  match kind with
  | .function =>
    let value ← term value (annotation.bind numericalArity?)
    if let some type := annotation then
      let some arity := numericalArity? type | throwErrorAt type "expected a numerical type"
      let s ← read
      checked stx (Core.checkTerm (← getMaxDepth) s.environment s.context value arity)
    else
      let _ ← inferTerm stx value
      pure ()
    return .letTerm (objectName id) value (← withAlias id value (predicate body
        expected))
  | .predicate =>
    let value ← predicate value (annotation.bind predicateSignature?)
    if let some type := annotation then
      let some sig := predicateSignature? type | throwErrorAt type "expected a predicate type"
      let s ← read
      checked stx (Core.checkPredicate (← getMaxDepth) s.environment s.context value sig)
    else
      let _ ← inferPredicate stx value
      pure ()
    return .letPredicate (objectName id) value (← withPredicateAlias id value
        (predicate body expected))
  | .theoremE => throwErrorAt stx "a predicate let cannot bind a proof"

private partial def declarationArguments (stx : Syntax) (name : Name)
    (parameters : List Core.Parameter) (args : List Syntax) :
    ObjectElabM (List Core.Term × List Predicate × List Syntax) := do
  if args.length < parameters.length then
    throwErrorAt stx "`{name}` requires {parameters.length} explicit parameters"
  let mut fs := []
  let mut ps := []
  for (parameter, arg) in parameters.zip args do
    match parameter with
    | .function _ arity => fs := fs ++ [← term arg arity]
    | .predicate _ signature => ps := ps ++ [← predicate arg signature]
  return (fs, ps, args.drop parameters.length)

private partial def quantify (all : Bool) (xs : List (TSyntax `praBinder))
    (body : Syntax) : ObjectElabM Predicate := do
  match xs with
  | [] => predicate body (some ⟨0, .prop⟩)
  | x :: xs =>
    let p ← withLocal x (binderName x) 0 (quantify all xs body)
    return (if all then Predicate.all else Predicate.ex) (.lam (binderName x) p)

end

private def attemptObject (action : ObjectElabM α) : ObjectElabM (Except Exception α) := do
  try pure (.ok (← action)) catch ex =>
    if ex.isInterrupt then throw ex
    pure (.error ex)

private def independent (left : ObjectElabM α) (right : ObjectElabM β) :
    ObjectElabM (α × β) := do
  unless (← getInfoState).enabled do return (← left, ← right)
  let left ← attemptObject left
  let right ← attemptObject right
  match left, right with
  | .ok a, .ok b => pure (a, b)
  | .error ex, _ | _, .error ex => throw ex

mutual

private partial def proof (stx : Syntax) (expected : Option Predicate := none) :
    ObjectElabM Proof :=
  withGoal stx (expected.map .proof)
      (fun depth p s => (Core.inferProof depth
        s.environment s.context p).map .proof) do
    rejectHole (unparen stx)
    let p ← proofBody (unparen stx) expected
    remember stx (.proof p)
    if let some type := expected then
      let s ← read
      checked stx (Core.checkProof (← getMaxDepth) s.environment s.context p type)
    return p

private partial def proofBody (stx : Syntax) (expected : Option Predicate) : ObjectElabM Proof := do
  match stx with
  | `(praExpr| ()) => return .trueIntro
  | `(praExpr| ($p:praExpr : $type:praExpr)) =>
    let type ← formula type
    return .ascribe type (← proof p type)
  | `(praExpr| fun $_xs:praFunBinder* => $_body:praExpr)
  | `(praExpr| fun $_xs:praFunBinder* : $_type:praExpr => $_body:praExpr) =>
    proofLambda stx expected
  | `(praExpr| ($a:praExpr, $bs:praExpr,*)) =>
    proofTuple stx (a.raw :: bs.getElems.toList.map (·.raw)) expected
  | `(praExpr| let ($a:praBinder, $bs:praBinder,*) := $p:praExpr; $body:praExpr) =>
    let p ← proof p
    destructure stx (a.raw :: bs.getElems.toList.map (·.raw)) p (← inferProof stx p) body expected
  | `(praExpr| let $id:ident := $value:praExpr; $body:praExpr) =>
    proofLet stx id none value body expected
  | `(praExpr| let $id:ident : $type:praExpr := $value:praExpr; $body:praExpr) =>
    proofLet stx id (some type.raw) value body expected
  | _ =>
    let (head, args) := spine stx
    if let `(praExpr| induction (motive := $motive:praExpr)) := head then
      let base :: step :: argument :: rest := args
        | throwErrorAt stx "`induction` requires a base, a step, and a numerical argument"
      let p ← inductionProof stx (some motive.raw) base step argument expected rest
      return ← applyProof stx p rest
    let `(praExpr| $id:ident) := head | do
      if args.isEmpty then throwErrorAt head "expected a proof expression"
      return ← applyProof stx (← proof head) args
    let n := objectName id
    let s ← read
    match ← binding n with
    | some .proof =>
      let p := Proof.hyp (s.names.proofs.idxOf n)
      remember head (.proof p)
      applyProof stx p args
    | some _ => throwErrorAt id "`{n}` is not a proof name"
    | none =>
      if n == `rfl then
        unless args.isEmpty do throwErrorAt stx "`rfl` takes no arguments; use `eq_refl`"
        let type ← requireExpected stx expected
        let .equal left _ ← exposeFormula stx type | throwErrorAt stx "expected numerical equality"
        return .eqRefl left
      if n == `trivial then return ← applyProof stx .trueIntro args
      if let some p ← primitiveProof stx n args expected then return p
      let .theoremE d ← lookup id | throwErrorAt id "expected a theorem"
      let (fs, ps, rest) ← declarationArguments stx n d.parameters args
      applyProof stx (.theoremE d.name fs ps) rest

private partial def proofLambda (stx : Syntax) (expected : Option Predicate) :
    ObjectElabM Proof := do
  let (n, annotation, body, ref) ← lambdaBody stx
  if let some type := expected then
    match ← exposeFormula stx type with
    | .imp a b =>
      let a ← if let some annotation := annotation then do
        let actual ← formula annotation
        let s ← read
        checked annotation ((Core.equalFormulas (← getMaxDepth) s.environment a actual)
          |>.withSite s.context (.predicate a))
        pure actual
      else pure a
      return .impIntro n a (← proofBinderBody ref a body (some b))
    | .all motive =>
      requirePlainBinder ref
      numericalBinder annotation
      return .forallIntro n motive (← withLocal ref n 0
        (proof body (Predicate.app motive.shift (.bvar 0))))
    | _ => throwErrorAt stx "expected an implication or universal formula for a proof lambda"
  let some annotation := annotation
    | throwErrorAt stx "a proof lambda needs typed binders or an expected formula"
  if numericalArity? annotation == some 0 then
    requirePlainBinder ref
    let (p, type) ← withLocal ref n 0 do
      let p ← proof body
      return (p, ← inferProof body p)
    return .forallIntro n (.lam n type) p
  let a ← formula annotation
  return .impIntro n a (← proofBinderBody ref a body none)

private partial def proofTuple (stx : Syntax) (entries : List Syntax)
    (expected : Option Predicate) : ObjectElabM Proof := do
  match entries with
  | [] => return .trueIntro
  | [last] => proof last expected
  | first :: rest =>
    if let some type := expected then
      match ← exposeFormula stx type with
      | .and a b =>
        let (left, right) ← independent (proof first a) (proofTuple stx rest b)
        return .andIntro left right
      | .ex motive =>
        let n ← term first (some 0)
        let s ← read
        checked first (Core.checkTerm (← getMaxDepth) s.environment s.context n 0)
        return .existsIntro motive n (← proofTuple stx rest (Predicate.app motive n))
      | _ => throwErrorAt stx "a proof tuple needs a conjunction or existential formula"
    return .andIntro (← proof first) (← proofTuple stx rest none)

private partial def proofLet (stx id : Syntax) (annotation : Option Syntax)
    (value body : Syntax) (expected : Option Predicate) : ObjectElabM Proof := do
  let kind ← match annotation with
    | some type =>
      if (numericalArity? type).isSome then pure Core.DeclarationKind.function
      else if (predicateSignature? type).isSome then pure .predicate else pure .theoremE
    | none => expressionKind value
  match kind with
  | .predicate =>
    let value ← predicate value (annotation.bind predicateSignature?)
    if let some type := annotation then
      let some sig := predicateSignature? type | throwErrorAt type "expected a predicate type"
      let s ← read
      checked stx (Core.checkPredicate (← getMaxDepth) s.environment s.context value sig)
    else
      let _ ← inferPredicate stx value
      pure ()
    return .letPredicate (objectName id) value (← withPredicateAlias id value (proof
        body expected))
  | .function =>
    let value ← term value (annotation.bind numericalArity?)
    if let some type := annotation then
      let some arity := numericalArity? type | throwErrorAt type "expected a numerical type"
      let s ← read
      checked stx (Core.checkTerm (← getMaxDepth) s.environment s.context value arity)
    else
      let _ ← inferTerm stx value
      pure ()
    return .letTerm (objectName id) value (← withAlias id value (proof body expected))
  | .theoremE =>
    let type ← annotation.mapM formula
    let p ← proof value type
    let type ← match type with | some type => pure type | none => inferProof value p
    return .letE (objectName id) type p (← withProof id (objectName id) type (proof
        body expected))

private partial def proofBinderBody (ref : Syntax) (domain : Predicate) (body : Syntax)
    (expected : Option Predicate) : ObjectElabM Proof := do
  if ref.isOfKind ``praTupleBinder then
    withReader (·.pushAnonymousProof domain) do
      bindPattern ref (.hyp 0) domain expected (fun expected => proof body expected)
  else withProof ref (binderName ref) domain (proof body expected)

/-- Destructure `pattern` over `value : type` using `Proof.letE`, `andLeft`/`andRight`, and
`existsElim`. -/
private partial def bindPattern (pattern : Syntax) (value : Proof) (type : Predicate)
    (expected : Option Predicate) (action : Option Predicate → ObjectElabM Proof) :
    ObjectElabM Proof := do
  let `(praFunBinder| ($first:praFunBinder, $rest:praFunBinder,*)) := pattern | do
    let name := binderName pattern
    let body ← if name.isAnonymous then withReader (·.pushAnonymousProof type) do
      remember pattern (.proof (.hyp 0))
      action expected
    else withProof pattern name type (action expected)
    return .letE name type value body
  let tail ← tuplePattern (rest.getElems.toList.map (·.raw))
  match ← exposeFormula pattern type with
  | .and left right =>
    let destruct (index : Nat) := do
      let start ← read
      bindPattern first (.andLeft (.hyp index)) left expected fun expected => do
        let current ← read
        let index := index + current.context.proofs.length - start.context.proofs.length
        let right := right.shift (current.context.locals.length - start.context.locals.length)
        bindPattern tail (.andRight (.hyp index)) right expected action
    match value with
    | .hyp index => destruct index
    | _ =>
      let body ← withReader (·.pushAnonymousProof type) (destruct 0)
      return .letE .anonymous type value body
  | .ex motive =>
    requirePlainBinder first
    let name := binderName first
    let hypothesis := Predicate.app motive.shift (.bvar 0)
    let extend s := (s.pushLocal name 0 first).pushAnonymousProof hypothesis
    let (body, target) ← withReader extend do
      remember first (.term (.bvar 0))
      let body ← bindPattern tail (.hyp 0) hypothesis (expected.map Predicate.shift) action
      let target ← match expected with
        | some target => pure target
        | none =>
          let type ← reduceFormula pattern (← inferProof pattern body)
          let target := type.subst0 .zero
          unless target.shift == type do
            throwErrorAt pattern "an existential witness escapes the result type"
          pure target
      return (body, target)
    return .existsElim name .anonymous target value body
  | _ => throwErrorAt pattern "tuple destructuring requires a conjunction or existential proof"

private partial def destructure (_stx : Syntax) (binders : List Syntax) (p : Proof)
    (type : Predicate) (body : Syntax) (expected : Option Predicate) : ObjectElabM Proof := do
  let pattern ← tuplePattern binders
  bindPattern pattern p type expected (fun expected => proof body expected)

private partial def proofBranch (stx : Syntax) (domain target : Predicate) :
    ObjectElabM (Name × Proof) := do
  match unparen stx with
  | `(praExpr| fun $_xs:praFunBinder* => $_body:praExpr)
  | `(praExpr| fun $_xs:praFunBinder* : $_type:praExpr => $_body:praExpr) =>
    let (name, annotation, body, ref) ← lambdaBody stx
    let domain ← if let some annotation := annotation then do
      let type ← formula annotation
      let s ← read
      checked annotation ((Core.equalFormulas (← getMaxDepth) s.environment domain type)
        |>.withSite s.context (.predicate domain))
      pure type
    else pure domain
    return (name, ← proofBinderBody ref domain body (some target))
  | _ => withReader (·.pushProof .anonymous domain) do
    let p ← proof stx (Predicate.imp domain target)
    return (.anonymous, .impElim p (.hyp 0))

private partial def applyProof (stx : Syntax) (p : Proof) (args : List Syntax) :
    ObjectElabM Proof := do
  match args with
  | [] => return p
  | a :: rest =>
    match ← exposeFormula stx (← inferProof stx p) with
    | .imp domain _ => applyProof stx (.impElim p (← proof a domain)) rest
    | .all _ => applyProof stx (.forallElim p (← term a (some 0))) rest
    | _ => throwErrorAt a "proof application requires an implication or universal formula"

/-- Reconstruct the expected formula for a proof head before `args` are applied to it. -/
private partial def applicationTarget (args : List Syntax) (expected : Option Predicate) :
    ObjectElabM (Option Predicate) := do
  let some target := expected | return none
  let mut target := target
  for arg in args.reverse do
    match ← expressionKind arg with
    | .function =>
      let argument ← term arg (some 0)
      let s ← read
      checked arg (Core.checkTerm (← getMaxDepth) s.environment s.context argument 0)
      let argument ← checked arg
        ((Core.reduceTerm (← getMaxDepth) s.environment 0 argument)
          |>.withSite s.context (.term argument))
      target := .all (.lam .anonymous (abstractNumber argument.shift 0 target.shift))
    | .theoremE => target := .imp (← inferProof arg (← proof arg)) target
    | .predicate => throwErrorAt arg "proof application requires a numerical term or proof"
  return some target

private partial def primitiveProof (stx : Syntax) (n : Name) (args : List Syntax)
    (expected : Option Predicate) : ObjectElabM (Option Proof) := do
  let finish (p : Proof) (rest : List Syntax) : ObjectElabM (Option Proof) := do
    return some (← applyProof stx p rest)
  match n, args with
  | `eq_refl, a :: rest => return ← finish (.eqRefl (← term a (some 0))) rest
  | `and_left, p :: rest => return ← finish (.andLeft (← proof p)) rest
  | `and_right, p :: rest => return ← finish (.andRight (← proof p)) rest
  | `or_left, p :: rest =>
    let expected ← applicationTarget rest expected
    let .or a b ← exposeFormula stx (← requireExpected stx expected)
      | throwErrorAt stx "expected a disjunction for `or_left`"
    return ← finish (.orLeft b (← proof p a)) rest
  | `or_right, p :: rest =>
    let expected ← applicationTarget rest expected
    let .or a b ← exposeFormula stx (← requireExpected stx expected)
      | throwErrorAt stx "expected a disjunction for `or_right`"
    return ← finish (.orRight a (← proof p b)) rest
  | `false_elim, p :: rest =>
    let expected ← applicationTarget rest expected
    return ← finish (.falseElim (← requireExpected stx expected) (← proof p Predicate.false)) rest
  | `succ_ne_zero, a :: rest => return ← finish (.succNeZero (← term a (some 0))) rest
  | `succ_inj, p :: rest => return ← finish (.succInj (← proof p)) rest
  | `lem, a :: rest => return ← finish (.lem (← predicate a)) rest
  | `eq_subst, m :: e :: p :: rest =>
    let motiveRef := m
    let m ← predicate m (some ⟨1, .prop⟩)
    let s ← read
    checked motiveRef
      (Core.checkPredicate (← getMaxDepth) s.environment s.context m ⟨1, .prop⟩)
    let e ← proof e
    let .equal left _ ← exposeFormula stx (← inferProof stx e)
      | throwErrorAt stx "equality substitution requires an equality proof"
    return ← finish (.eqSubst m e (← proof p (Predicate.app m left))) rest
  | `or_elim, p :: l :: r :: rest =>
    let target ← requireExpected stx (← applicationTarget rest expected)
    let p ← proof p
    let .or a b ← exposeFormula stx (← inferProof stx p)
      | throwErrorAt stx "expected disjunction"
    let (ln, l) ← proofBranch l a target
    let (rn, r) ← proofBranch r b target
    return ← finish (.orElim ln rn target p l r) rest
  | `exists_elim, p :: branch :: rest =>
    let target ← requireExpected stx (← applicationTarget rest expected)
    let p ← proof p
    let .ex m ← exposeFormula stx (← inferProof stx p)
      | throwErrorAt stx "expected existential formula"
    let (x, annotation, body, ref) ← plainLambdaBody branch
    numericalBinder annotation
    let hypothesis := Predicate.app m.shift (.bvar 0)
    let (h, body) ← withLocal ref x 0 (proofBranch body hypothesis target.shift)
    return ← finish (.existsElim x h target p body) rest
  | `induction, base :: step :: argument :: rest =>
    return ← finish (← inductionProof stx none base step argument expected rest) rest
  | _, _ =>
    if isProofPrimitive n then
      throwErrorAt stx "incorrect number of explicit arguments to `{n}`"
    return none

private partial def inductionProof (stx : Syntax) (explicitMotive : Option Syntax)
    (base step argument : Syntax) (expected : Option Predicate)
    (resultArgs : List Syntax) : ObjectElabM Proof := do
  let argument ← term argument (some 0)
  let s ← read
  checked stx (Core.checkTerm (← getMaxDepth) s.environment s.context argument 0)
  let branch ← match unparen step with
    | `(praExpr| fun $_xs:praFunBinder* => $_body:praExpr)
    | `(praExpr| fun $_xs:praFunBinder* : $_type:praExpr => $_body:praExpr) =>
      let (x, annotation, rest, ref) ← plainLambdaBody step
      numericalBinder annotation
      pure (some (x, rest, ref))
    | _ => pure none
  let motive ← match explicitMotive with
    | some motive => predicate motive (some ⟨1, .qf⟩)
    | none => do
      let hintedMotive ← match branch with
        | some (x, rest, ref) =>
          match unparen rest with
          | `(praExpr| fun $_xs:praFunBinder* => $_body:praExpr)
          | `(praExpr| fun $_xs:praFunBinder* : $_type:praExpr => $_body:praExpr) =>
            let (_, annotation, _, _) ← lambdaBody rest
            annotation.mapM fun annotation => withReader (·.pushLocal x 0 ref) do
              pure (Predicate.lam x (← predicate annotation))
          | _ => pure none
        | none =>
          -- If `step` has holes, fall back to generalizing `expected`.
          if (step.find? fun node => node.isMissing || node.isOfKind ``praHole ||
              node.isOfKind ``praSyntheticHole ||
              node.isOfKind `LeanPRA.Surface.recoveredHole).isSome then
            pure none
          else do
            let p ← proof step
            let .all m ← exposeFormula step (← inferProof step p)
              | throwErrorAt step "an induction step must prove a numerical universal formula"
            withReader (·.pushLocal .anonymous) do
              let .imp hypothesis _ ← exposeFormula step (.app m.shift (.bvar 0))
                | throwErrorAt step "an induction step must take an induction hypothesis"
              pure (some (Predicate.lam .anonymous hypothesis))
      match hintedMotive with
        | some motive => pure motive
        | none =>
          let target ← requireExpected stx (← applicationTarget resultArgs expected)
          let depth ← getMaxDepth
          -- Beta-reduce before abstracting `argument`, keeping definitions and `primrec` intact.
          let target := Core.betaReducePredicate depth target
          let argument := Core.betaReduceTerm depth argument
          pure (Predicate.lam .anonymous (abstractNumber argument.shift 0 target.shift))
  checked (explicitMotive.getD stx)
    (Core.checkPredicate (← getMaxDepth) s.environment s.context motive ⟨1, .qf⟩)
  let hypothesis := Predicate.app motive.shift (.bvar 0)
  let successor := Predicate.app motive.shift (.app .succ (.bvar 0))
  let stepType := Predicate.all (.lam .anonymous (.imp hypothesis successor))
  let (base, (hn, step)) ← independent (proof base (Predicate.app motive .zero)) do
    match branch with
    | some (x, rest, ref) => withLocal ref x 0 (proofBranch rest hypothesis successor)
    | none => withReader (fun s => (s.pushLocal .anonymous).pushProof .anonymous hypothesis) do
      let p ← proof step stepType.shift
      let p := Proof.impElim (.forallElim p (.bvar 0)) (.hyp 0)
      let s ← read
      checked stx (Core.checkProof (← getMaxDepth) s.environment s.context p successor)
      pure (.anonymous, p)
  return .induction (branch.map (·.1) |>.getD .anonymous)
    hn motive base step argument

end

private def parameterScope (environment : Core.Environment) (ps : Array Syntax) :
    CommandElabM (Scope × List Core.Parameter) := do
  let mut s : Scope := { environment }
  let mut parameters := []
  let mut expanded := #[]
  for p in ps do
    let `(praParam| ($ids:ident* : $type:praExpr)) := p
      | throwErrorAt p "expected an explicit parameter group"
    for id in ids do
      expanded := expanded.push (← `(praParam| ($id:ident : $type:praExpr)))
  for p in expanded do
    let `(praParam| ($ids:ident* : $type:praExpr)) := p
      | throwErrorAt p "expected an explicit parameter"
    let id := ids[0]!
    let n := objectName id
    if s.bindings.any (·.name == n) then throwErrorAt id "duplicate parameter `{n}`"
    if let some arity := numericalArity? type then
      parameters := parameters ++ [.function n arity]
      s := { s with
        context := { s.context with functions := s.context.functions ++ [arity] }
        names := { s.names with functions := s.names.functions ++ [n] }
        bindings := .functionParameter n s.context.functions.length :: s.bindings
        references := (n, id) :: s.references }
      addExpressionInfo id environment s.context s.names
        (.term (.parameter (s.context.functions.length - 1))) id
    else if let some sig := predicateSignature? type then
      parameters := parameters ++ [.predicate n sig]
      s := { s with
        context := { s.context with predicates := s.context.predicates ++ [sig] }
        names := { s.names with predicates := s.names.predicates ++ [n] }
        bindings := .predicateParameter n s.context.predicates.length :: s.bindings
        references := (n, id) :: s.references }
      addExpressionInfo id environment s.context s.names
        (.predicate (.parameter (s.context.predicates.length - 1))) id
    else throwErrorAt type "expected a first-order numerical or predicate type"
  return (s, parameters)

private def runObject (s : Scope) (action : ObjectElabM α) : CommandElabM α :=
  (action.run s).run' #[]

/-- Elaborate a `def` or `theorem` declaration, check it with `Core.checkDeclaration`,
and publish it. -/
def elaborateDeclaration (stx : Syntax) : CommandElabM Unit := do
  let (isTheorem, id, ps, type, body) ← match stx with
    | `(praDecl| def $id:ident $ps:praParam* : $type:praExpr := $body:praExpr) =>
      pure (false, id, ps.map (·.raw), type, body)
    | `(praDecl| theorem $id:ident $ps:praParam* : $type:praExpr := $body:praExpr) =>
      pure (true, id, ps.map (·.raw), type, body)
    | _ => throwUnsupportedSyntax
  let environment := CoreEnvironment.getState (← getEnv)
  let (s, parameters) ← parameterScope environment ps
  let s := { s with parentExpression := stx }
  let shortName := objectName id
  let ns ← getCurrNamespace
  let name := if shortName.getRoot == `_root_ then
    shortName.replacePrefix `_root_ .anonymous else ns ++ shortName
  if isBuiltinName (shortName.replacePrefix `_root_ .anonymous) then
    throwErrorAt id "reserved PRA name `{name}`"
  let environment ← runObject s do
    let declaration ← if isTheorem then
      let type ← predicate type (some ⟨0, .prop⟩)
      let s ← read
      let _ ← checked stx (Core.inferFormula (← getMaxDepth) environment s.context type)
      pure (Core.Declaration.theoremE ⟨name, parameters, type, ← proof body type⟩)
    else if let some arity := numericalArity? type then
      unless s.context.predicates.isEmpty do
        throwErrorAt id "numerical definitions cannot take predicate parameters"
      pure (Core.Declaration.function
        ⟨name, (s.context.functions.zip s.names.functions).map (fun (k, n) => ⟨k, n⟩),
          arity, ← term body arity⟩)
    else if let some sig := predicateSignature? type then
      pure (Core.Declaration.predicate ⟨name, parameters, sig, ← predicate body sig⟩)
    else throwErrorAt type "expected a first-order numerical or predicate result type"
    checked stx (Core.checkDeclaration (← getMaxDepth) environment declaration)
  -- Reject missing syntax only after elaboration so goal info is still recorded at the cursor.
  if stx.hasMissing then
    throwErrorAt stx "incomplete PRA declaration"
  modifyEnv (publishDeclaration · environment name)
  if let some location ← sourceLocation id then
    modifyEnv (declarationLocations.addEntry · (name, location))
  if let some d := environment.lookup name then addDeclarationInfo id d

/-- Elaborate `#check stx` and log its inferred Core type. -/
def elaborateCheck (stx : Syntax) : CommandElabM Unit := do
  let s : Scope := { environment := CoreEnvironment.getState (← getEnv) }
  if let `(praExpr| $id:ident) := unparen stx then
    let n := objectName id
    if let some d ← resolveDeclaration? s.environment n then
      addDeclarationInfo stx d
      logInfoAt stx (← delabSignature d)
      return
  runObject s do
    let output ← match ← expressionKind stx with
    | .function =>
      let t ← term stx
      let arity ← inferTerm stx t
      pure m!"{← formatSyntax `praExpr (← delabTerm {} t)} : \
        {← formatSyntax `praExpr (← delabArity arity)}"
    | .predicate =>
      let p ← predicate stx
      let sig ← inferPredicate stx p
      pure m!"{← formatSyntax `praExpr (← delabPredicate {} p)} : \
        {← formatSyntax `praExpr (← delabPredicateType sig)}"
    | .theoremE =>
      let p ← proof stx
      let type ← inferProof stx p
      pure m!"{← formatSyntax `praExpr (← delabProof {} p)} : \
        {← formatSyntax `praExpr (← delabPredicate {} type)}"
    logInfoAt stx output

/-- Elaborate `#print id` and log the delaborated declaration. -/
def elaboratePrint (id : Syntax) : CommandElabM Unit := do
  let s : Scope := { environment := CoreEnvironment.getState (← getEnv) }
  let d ← runObject s (lookup id)
  logInfoAt id m!"{← formatSyntax `praDecl (← delabDeclaration d)}"

end LeanPRA.Surface
