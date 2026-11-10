module

public meta import LeanPRA.Surface.Tactic

/-!
# Elaborating PRA syntax with explicit metavariables

Elaboration from `praExpr` and `praDecl` syntax to Core expressions and declarations:

- `elaborateDeclaration` elaborates a declaration, resolves its metavariables, checks it with
  `Core.checkDeclaration`, and publishes it.
- `elaborateCheck` elaborates an expression, infers its Core type, and logs its signature.
- `elaboratePrint` looks up a declaration and logs its delaborated syntax.

`Scope` maps source binder names to local variable indices and records syntax spans for error
locations, hover info, go-to-definition, and goal snapshots. Elaborating a declaration shares one
metavariable and constraint state across suspended proof tasks. Goal snapshots and hover types are
still recorded when constraints conflict or proof holes remain open. Completed declarations are
checked by `Core.checkDeclaration` before publication.
-/

public meta section

namespace LeanPRA.Surface

open Lean Elab Command
open Core (VariableKind)
open Metavariable hiding Term

private structure ProofResult where
  value : Proof
  type : Predicate

private def ProofResult.ready (value : Proof) (type : Predicate) : ProofResult := ⟨value, type⟩

private def ProofResult.map (f : Proof → Proof) (type : Predicate) (p : ProofResult) :
    ProofResult := ⟨f p.value, type⟩

private def ProofResult.map₂ (f : Proof → Proof → Proof) (type : Predicate)
    (p q : ProofResult) : ProofResult := ⟨f p.value q.value, type⟩

private inductive DraftGoalTarget where
  | term (arity : Nat)
  | predicate (signature : Core.PredicateSignature)
  | proof (type : Predicate)

private inductive DraftGoalBinding where
  | local (name : Name) (index : Nat)
  | functionParameter (name : Name) (index : Nat)
  | predicateParameter (name : Name) (index : Nat)
  | proof (name : Name) (index : Nat)
  | termAlias (name : Name) (value : Metavariable.Term)
  | predicateAlias (name : Name) (value : Predicate)

private def DraftGoalBinding.name : DraftGoalBinding → Name
  | .local n _ | .functionParameter n _ | .predicateParameter n _
  | .proof n _ | .termAlias n _ | .predicateAlias n _ => n

private structure DraftSite where
  context : Metavariable.Context
  subject : Metavariable.Subject

private def DraftSite.project (view : Metavariable.Projection) (site : DraftSite) :
    Except String Core.CheckSite := do
  return ⟨view.encodeContext site.context, ← view.encodeSubject site.subject⟩

private def DraftGoalTarget.project (view : Metavariable.Projection) : DraftGoalTarget → GoalTarget
  | .term k => .term k
  | .predicate k => .predicate k
  | .proof p => .proof (view.encodePredicate p)

private def DraftGoalBinding.project (view : Metavariable.Projection) : DraftGoalBinding →
    GoalBinding
  | .local n i => .local n i
  | .functionParameter n i => .functionParameter n i
  | .predicateParameter n i => .predicateParameter n i
  | .proof n i => .proof n i
  | .termAlias n t => .termAlias n (view.encodeTerm t)
  | .predicateAlias n p => .predicateAlias n (view.encodePredicate p)

/-- A scope has a checked environment and well-formed proof hypotheses. Numerical arities and
parameter signatures are well formed by construction. Formula annotations are checked before
binding; inferred hypotheses come from checked proofs or formed connectives. -/
private structure Scope where
  environment : Core.Environment
  context : Metavariable.Context := {}
  names : Names := {}
  bindings : List DraftGoalBinding := []
  aliases : List (Name × Metavariable.Term) := []
  predicateAliases : List (Name × Predicate) := []
  references : List (Name × Syntax) := []
  parentExpression : Syntax := .missing
  localIds : List Nat := []
  reason : String := "proof type"
  inTactic : Bool := false

private structure Origin where
  site : DraftSite
  ref : Syntax
  names : Names
  localIds : List Nat := []
  target : Syntax := .missing
  infoHole : Option MVarId := none

private structure Blocking where
  dependencies : List Metavariable.Frontend.UnknownId
  reason : String

private inductive TaskStatus where
  | ready
  | running
  | waiting (blocker : Blocking)
  | done
  | failed (error : Exception)

private structure ProofTask where
  ref : Syntax
  scope : Scope
  goal : Nat
  status : TaskStatus := .ready
  infoHole : Option MVarId := none

private structure HoleGoal where
  ref : Syntax
  scope : Scope
  type : Predicate

private structure GoalOrigin where
  ref : Syntax
  scope : Scope
  target : Option DraftGoalTarget
  infoHole : MVarId
  children : PersistentArray InfoTree := {}

private structure ObjectState where
  origins : Array Origin := #[]
  proofOrigins : Array (Syntax × Scope × Predicate × MVarId) := #[]
  goals : Array GoalOrigin := #[]
  holes : Array HoleGoal := #[]
  tasks : Array ProofTask := #[]
  constraintScopes : Array (Nat × Scope) := #[]
  argumentSources : Array (Metavariable.Subject × Syntax) := #[]
  unification : Metavariable.Frontend.State := Metavariable.Frontend.empty 0 0
  blocking : Option Blocking := none
  tacticGoals : Array (Nat × Scope) := #[]
  collectingTacticGoals : Bool := false

private abbrev ObjectElabM := ReaderT Scope (StateRefT ObjectState CommandElabM)

/-- Include checked declarations published by tactics while keeping the saved local bindings. -/
private def currentScope : ObjectElabM Scope := do
  let scope ← read
  return { scope with environment := CoreEnvironment.getState (← getEnv) }

private def projection : ObjectElabM Metavariable.Projection :=
  return (← get).unification.projection

private def showTerm (names : Names) (t : Metavariable.Term) := do
  delabTerm names ((← projection).encodeTerm t)

private def showPredicate (names : Names) (p : Predicate) := do
  delabPredicate names ((← projection).encodePredicate p)

private def exportProof (p : Proof) : ObjectElabM Core.Proof := do
  match (← projection).encodeProof p with
  | .ok p => return p
  | .error error => throwError "{error}"

private def showProof (names : Names) (p : Proof) := do
  delabProof names (← exportProof p)

private def expressionInfo (stx : Syntax) (env : Core.Environment) (ctx : Metavariable.Context)
    (names : Names) (subject : Metavariable.Subject) (target : Syntax) : ObjectElabM Unit := do
  let view ← projection
  match view.encodeSubject subject with
  | .ok subject => addExpressionInfo stx env (view.encodeContext ctx) names subject target
  | .error error => throwErrorAt stx "{error}"

private def proofInfo (stx : Syntax) (names : Names) (type : Predicate) (target : Syntax) := do
  addProofTypeInfo stx names ((← projection).encodePredicate type) target

private def goalInfo (stx : Syntax) (env : Core.Environment) (ctx : Metavariable.Context)
    (names : Names) (bindings : List DraftGoalBinding) (target : Option DraftGoalTarget)
    (status : GoalStatus) : ObjectElabM Info := do
  let view ← projection
  makeGoalInfo stx env (view.encodeContext ctx) names (bindings.map (·.project view))
    (target.map (·.project view)) status

private initialize blockedExceptionId : InternalExceptionId ←
  registerInternalExceptionId `LeanPRA.Surface.blocked

private def throwArgumentErrorAt (ref : Syntax) (message : MessageData) : ObjectElabM α :=
  Lean.throwErrorAt ref message

private def runSolver (action : Metavariable.Frontend.M α) : ObjectElabM α := do
  match action.run (← get).unification with
  | .ok (value, state) =>
    modify fun s => { s with unification := state }
    return value
  | .error message => throwError "{message}"

private def resolvedTerm (t : Metavariable.Term) : ObjectElabM Metavariable.Term := do
  let state := (← get).unification
  if state.terms.isEmpty && state.predicates.isEmpty then return t
  let depth := pra.maxDepth.get (← getOptions)
  match Metavariable.Frontend.resolveTerm (← get).unification (← read).localIds depth t with
  | .ok t => return t
  | .error message => throwError "{message}"

private def resolvedPredicate (p : Predicate) : ObjectElabM Predicate := do
  let state := (← get).unification
  if state.terms.isEmpty && state.predicates.isEmpty then return p
  let depth := pra.maxDepth.get (← getOptions)
  match Metavariable.Frontend.resolvePredicate (← get).unification (← read).localIds depth p with
  | .ok p => return p
  | .error message => throwError "{message}"

private def resolvedProof (p : Proof) : ObjectElabM Proof := do
  if Metavariable.Frontend.isEmpty (← get).unification then return p
  let depth := pra.maxDepth.get (← getOptions)
  let scope ← read
  match Metavariable.Frontend.resolveProof (← get).unification
      scope.localIds scope.context.proofs.length depth p with
  | .ok p => return p
  | .error message => throwError "{message}"

private def currentContext : ObjectElabM Metavariable.Context := do
  let s ← read
  let context := Metavariable.Frontend.context (← get).unification s.context
  return { context with proofs := ← context.proofs.mapM resolvedPredicate }

private def displayNames : ObjectElabM Names := do
  let (functions, predicates) := Metavariable.Frontend.displaySlots (← get).unification
  return { (← read).names with unknownFunctions := functions, unknownPredicates := predicates }

private def constrainFormulas (a b : Predicate) (ref : Syntax := .missing) : ObjectElabM Unit := do
  let scope ← currentScope
  let ref := if ref.isMissing then scope.parentExpression else ref
  let id ← runSolver (Metavariable.Frontend.submit (pra.maxDepth.get (← getOptions))
    scope.environment
    (.predicate (← currentContext) scope.localIds 0 a b) ⟨ref, scope.reason⟩)
  modify fun s => { s with constraintScopes := s.constraintScopes.push (id, scope) }

private def blockOn (type : Predicate) (reason : String) : ObjectElabM Unit := do
  let type ← resolvedPredicate type
  let dependencies := Metavariable.Frontend.predicateDependencies (← get).unification type
  unless dependencies.isEmpty do
    modify fun s => { s with blocking := some ⟨dependencies, reason⟩ }
    throw (.internal blockedExceptionId)

private def getMaxDepth : ObjectElabM Nat :=
  return pra.maxDepth.get (← getOptions)

private def objectName (stx : Syntax) : Name := stx.getId.eraseMacroScopes

private def binderName (stx : Syntax) : Name :=
  if stx[0].isIdent then objectName stx[0] else .anonymous

private def shiftLocalBinding : DraftGoalBinding → DraftGoalBinding
  | .local n i => .local n (i + 1)
  | .termAlias n t => .termAlias n t.shift
  | .predicateAlias n p => .predicateAlias n p.shift
  | other => other

private def shiftProofBinding : DraftGoalBinding → DraftGoalBinding
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

/-- Push a well-formed proof hypothesis of formula `type`. -/
private def Scope.pushProof (s : Scope) (n : Name) (type : Predicate)
    (ref : Syntax := .missing) : Scope :=
  { s with
    context := s.context.pushProof type
    names := { s.names with proofs := n :: s.names.proofs }
    bindings := .proof n 0 :: s.bindings.map shiftProofBinding
    references := (n, ref) :: s.references
    aliases := s.aliases.filter (·.1 != n)
    predicateAliases := s.predicateAliases.filter (·.1 != n) }

/-- Push an unnamed, well-formed proof hypothesis and shift existing proof indices. -/
private def Scope.pushAnonymousProof (s : Scope) (type : Predicate) : Scope :=
  { s with
    context := s.context.pushProof type
    names := { s.names with proofs := .anonymous :: s.names.proofs }
    bindings := s.bindings.map shiftProofBinding }

private def Scope.addAlias (s : Scope) (n : Name) (value : Metavariable.Term)
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

private def remember (stx : Syntax) (subject : Metavariable.Subject) : ObjectElabM Unit := do
  if stx.isMissing then return
  let collectInfo ← editorInfoEnabled
  let s ← currentScope
  let id := if stx.isIdent then stx else stx[0]
  let target := if id.isIdent then
    ((s.references.find? (·.1 == objectName id)).map (·.2)).getD .missing else .missing
  -- Share the hypotheses here and resolve them when reporting an error or editor information.
  let context := Metavariable.Frontend.context (← get).unification s.context
  -- Reserve a slot in the info tree to fill once metavariables are resolved.
  let hasUnknowns := !Metavariable.Frontend.isEmpty (← get).unification
  let infoHole ← if hasUnknowns && collectInfo then do
    let hole : MVarId := ⟨← liftTermElabM (mkFreshUserName `praInfo)⟩
    pushInfoTree (.hole hole)
    pure (some hole)
  else pure none
  let names ← displayNames
  modify fun state => { state with origins := state.origins.push {
    site := ⟨context, subject⟩, ref := stx, names, localIds := s.localIds,
    target, infoHole } }
  if collectInfo && infoHole.isNone then
    expressionInfo stx s.environment context (← displayNames) subject target

private def unknownTerm (ref : Syntax) (arity : Nat) (name : Name := .anonymous) :
    ObjectElabM Metavariable.Term := do
  let value ← runSolver (Metavariable.Frontend.freshTerm arity (← read).localIds name)
  modify fun state =>
    { state with argumentSources := state.argumentSources.push (.term value, ref) }
  return value

private def unknownPredicate (ref : Syntax) (sig : Core.PredicateSignature)
    (name : Name := .anonymous) : ObjectElabM Predicate := do
  let value ← runSolver (Metavariable.Frontend.freshPredicate sig (← read).localIds name)
  modify fun state =>
    { state with argumentSources := state.argumentSources.push (.predicate value, ref) }
  return value

private def missingRange (parent : Syntax) : Syntax := Id.run do
  let some start := parent.getTailPos? (canonicalOnly := true) | return .missing
  let stop := start.increaseBy (max 1 parent.getTrailingSize)
  return Syntax.atom (.synthetic start stop true) ""

private def withGoal (stx : Syntax) (expected : Option DraftGoalTarget)
    (infer : Metavariable.Projection → Nat → α → Scope → Core.CheckResult DraftGoalTarget) (action
        : ObjectElabM α) :
    ObjectElabM α := do
  if (← read).inTactic || !(← editorInfoEnabled) then return ← action
  let scope ← read
  let ref := if (stx.getRange? (canonicalOnly := true)).isSome then stx
    else missingRange scope.parentExpression
  let hole : MVarId := ⟨← liftTermElabM (mkFreshUserName `praGoal)⟩
  let id := (← get).goals.size
  modify fun s => { s with goals := s.goals.push ⟨ref, scope, expected, hole, {}⟩ }
  withInfoTreeContext (do
    let result ← withReader (fun s => { s with parentExpression := ref }) action
    if expected.isNone then
      let target :=
        (infer (← projection) (← getMaxDepth) result
          { (← currentScope) with context := ← currentContext }).toOption
      modify fun s => { s with goals := s.goals.modify id (fun g => { g with target }) }
    return result) fun children => do
      modify fun s => { s with goals := s.goals.modify id (fun g => { g with children }) }
      return .hole hole

private def rejectHole (stx : Syntax) : ObjectElabM Unit := do
  if stx.isMissing then throwErrorAt stx "incomplete PRA expression"
  if stx.isOfKind `LeanPRA.Surface.recoveredHole then
    throwErrorAt (← read).parentExpression "incomplete PRA expression"
  if stx.isOfKind ``praHole || stx.isOfKind ``praSyntheticHole then
    throwErrorAt stx "incomplete PRA expression"

private def withLocal (ref : Syntax) (n : Name) (arity : Nat) (action : ObjectElabM α) :
    ObjectElabM α :=
  do
    let id ← runSolver Metavariable.Frontend.freshLocal
    withReader (fun s => { s.pushLocal n arity ref with localIds := id :: s.localIds }) do
      remember ref (.term (.bvar 0))
      action

private def withProof (ref : Syntax) (n : Name) (type : Predicate) (action : ObjectElabM α) :
    ObjectElabM α :=
  withReader (·.pushProof n type ref) do
    remember ref (.proof (.hyp 0))
    action

private def withAnonymousProof (type : Predicate) (action : ObjectElabM α) : ObjectElabM α := do
  withReader (·.pushAnonymousProof type) action

private def withAlias (ref : Syntax) (value : Metavariable.Term) (action : ObjectElabM α) :
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
    let origins := (← get).origins
    let view ← projection
    let state := (← get).unification
    let depth ← getMaxDepth
    let origin := error.site.bind fun site =>
      origins.findRev? fun origin =>
        let proofs := origin.site.context.proofs.mapM
          (Metavariable.Frontend.resolvePredicate state origin.localIds depth)
        match proofs with
        | .error _ => false
        | .ok proofs =>
          let draft := { origin.site with context := { origin.site.context with proofs } }
          (draft.project view).toOption == some site
    let ref := (origin.map (·.ref)).getD stx
    match error.reason with
    | .proofTypeMismatch expected actual .. =>
      let names := (origin.map (·.names)).getD (← read).names
      let depth ← getMaxDepth
      let expected ← delabPredicate names (Core.betaReducePredicate depth expected)
      let actual ← delabPredicate names (Core.betaReducePredicate depth actual)
      throwErrorAt ref "proof type mismatch\nexpected: {← formatSyntax `praExpr expected}\n\
        inferred: {← formatSyntax `praExpr actual}"
    | .termConversion _ left right .. =>
      let names := (origin.map (·.names)).getD (← displayNames)
      let left ← delabTerm names left
      let right ← delabTerm names right
      throwErrorAt ref "terms are not definitionally equal\nleft: {← formatSyntax `praExpr left}\n\
        right: {← formatSyntax `praExpr right}"
    | .predicateConversion _ left right .. =>
      let names := (origin.map (·.names)).getD (← displayNames)
      let left ← delabPredicate names left
      let right ← delabPredicate names right
      throwErrorAt ref "predicates are not definitionally equal\n\
        left: {← formatSyntax `praExpr left}\nright: {← formatSyntax `praExpr right}"
    | _ => throwErrorAt ref "{error.message}"

private def inferTerm (stx : Syntax) (t : Metavariable.Term) : ObjectElabM Nat := do
  let s ← currentScope
  checked stx (Bridge.termType (← projection) (← getMaxDepth) s.environment (← currentContext)
    (← resolvedTerm t))

private def inferPredicate (stx : Syntax) (p : Predicate) :
    ObjectElabM Core.PredicateSignature := do
  let s ← currentScope
  checked stx (Bridge.predicateType (← projection) (← getMaxDepth) s.environment (← currentContext)
    (← resolvedPredicate p))

private def resolvedProofType (_stx : Syntax) (p : ProofResult) : ObjectElabM Predicate :=
  resolvedPredicate p.type

private def closeProof (action : ObjectElabM ProofResult) : ObjectElabM ProofResult := do
  let result ← action
  if Metavariable.Frontend.proofComplete (← get).unification result.value then return result
  let scope ← read
  let value ← runSolver (Metavariable.Frontend.captureProof (← getMaxDepth)
    result.type scope.context scope.localIds result.value)
  return { result with value }

private def readyProof (stx : Syntax) (p : Proof) : ObjectElabM ProofResult := do
  let s ← currentScope
  let result := Bridge.proofType (← projection) (← getMaxDepth) s.environment (← currentContext) p
  let type ← match result with
    | .ok result => checked stx result
    | .error error => throwErrorAt stx "{error}"
  return ProofResult.ready p type

private def existentialResult (stx : Syntax) (outer : Scope) (type : Predicate) :
    ObjectElabM Predicate := do
  let type ← resolvedPredicate type
  let state := (← get).unification
  -- An unresolved metavariable may later use any local in its creation scope.
  let dependencies := (Metavariable.Frontend.predicateDependencies state type).filter fun
    | .term i => state.terms[i]?.any fun u => !u.locals.all outer.localIds.contains
    | .predicate i => state.predicates[i]?.any fun u => !u.locals.all outer.localIds.contains
  unless dependencies.isEmpty do
    modify fun s => { s with blocking := some ⟨dependencies,
      "the existential result is waiting for scoped implicit arguments"⟩ }
    throw (.internal blockedExceptionId)
  -- Substituting zero gives a candidate in the outer scope. Conversion checks that the witness
  -- can be replaced this way, including when computation discards it inside a subformula.
  let target := type.subst0 .zero
  unless target.shift == type do
    let view ← projection
    let equal ← checked stx
      ((Core.defEqPredicate (← getMaxDepth) (CoreEnvironment.getState (← getEnv)) 0
        (view.encodePredicate type)
        (view.encodePredicate target.shift)).withSite (view.encodeContext (← currentContext))
          (.predicate (view.encodePredicate type)))
    unless equal do
      blockOn type "the existential result is waiting for its witness dependency to be resolved"
      throwErrorAt stx "an existential witness escapes the result type"
  withReader (fun _ => outer) do
    let _ ← checked stx (Bridge.formulaSort (← projection) (← getMaxDepth)
      (CoreEnvironment.getState (← getEnv))
      (← currentContext) target)
    pure target

-- Reduce to WHNF so the outer connective is visible without normalizing subformulas.
private def exposeFormula (stx : Syntax) (p : Predicate) : ObjectElabM Predicate := do
  let s ← currentScope
  let depth ← getMaxDepth
  let _ ← checked stx
    (Bridge.formulaSort (← projection) depth s.environment (← currentContext) (← resolvedPredicate
        p))
  checked stx ((Bridge.whnfPredicate (← projection) depth s.environment (← resolvedPredicate p))
    |>.withSite ((← projection).encodeContext s.context)
      (.predicate ((← projection).encodePredicate p)))

private def formulaKind? : Predicate → Option String
  | .false => some "a proof of False"
  | .true => some "a proof of True"
  | .equal .. => some "an equality"
  | .imp .. => some "an implication"
  | .and .. => some "a conjunction"
  | .or .. => some "a disjunction"
  | .all .. => some "a universally quantified formula"
  | .ex .. => some "an existentially quantified formula"
  | _ => none

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

private def lookup (stx : Syntax) : ObjectElabM DeclarationSignature := do
  let n := objectName stx
  match ← resolveSignature? (← currentScope).environment n with
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

private partial def abstractNumberTerm (argument : Metavariable.Term) (depth : Nat) :
    Metavariable.Term → Metavariable.Term
  | t =>
    if t == argument.shift depth then .bvar depth else
    match t with
    | .lam hint b => .lam hint (abstractNumberTerm argument (depth
        + 1) b)
    | .app f a => .app (abstractNumberTerm argument depth f) (abstractNumberTerm argument depth a)
    | .letE hint a b => .letE hint (abstractNumberTerm argument
        depth a)
        (abstractNumberTerm argument (depth + 1) b)
    | .primrec b s => .primrec (abstractNumberTerm argument depth b)
        (abstractNumberTerm argument depth s)
    | .definition n fs => .definition n (fs.map (abstractNumberTerm argument depth))
    | t => t

private def abstractNumber (argument : Metavariable.Term) (depth : Nat) : Predicate → Predicate
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
  | `(praExpr| ∃ $_xs:praBinder*, $_body:praExpr)
  | `(praExpr| ∀ {$_xs:praBinder*}, $_body:praExpr)
  | `(praExpr| ∀ {$_xs:praBinder* : Nat}, $_body:praExpr) => return .predicate
  | _ =>
    let (head, args) := spine stx
    let _explicit := match head with
      | `(praExpr| @$_id:ident) | `(praExpr| @($_p:praExpr)) => true
      | _ => false
    let head ← match head with
      | `(praExpr| @$id:ident) => pure (← `(praExpr| $id:ident)).raw
      | `(praExpr| @($p:praExpr)) => pure p.raw
      | _ => pure head
    if !args.isEmpty then return ← expressionKind head
    if let `(praExpr| $id:ident) := head then
      let n := objectName id
      match ← binding n with
      | some .local | some .functionParameter => return .function
      | some .predicateParameter => return .predicate
      | some .proof => return .theoremE
      | none =>
        if let some d ← resolveSignature? (← currentScope).environment n then
          return d.kind
    return .theoremE

mutual

private partial def term (stx : Syntax) (expected : Option Nat := none) :
    ObjectElabM Metavariable.Term :=
  withGoal stx (expected.map .term)
      (fun view depth t s => (Bridge.termType view depth s.environment s.context t)
        |>.map .term) do
    if (unparen stx).isOfKind ``praHole then
      let some arity := expected | throwErrorAt stx "a numerical hole needs an expected arity"
      return ← unknownTerm stx arity
    rejectHole (unparen stx)
    let t ← termBody (unparen stx) expected
    let t ← resolvedTerm t
    remember stx (.term t)
    return t

private partial def termBody (stx : Syntax) (expected : Option Nat) : ObjectElabM
    Metavariable.Term := do
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
    let s ← currentScope
    checked stx (Bridge.checkTerm (← projection) (← getMaxDepth) s.environment (← currentContext)
        value arity)
    return .letE (objectName id) value (← withLocal id (objectName id) arity (term
        body expected))
  | `(praExpr| ($value:praExpr : $type:praExpr)) =>
    let some arity := numericalArity? type | throwErrorAt type "expected a numerical type"
    let value ← term value arity
    let s ← currentScope
    checked stx (Bridge.checkTerm (← projection) (← getMaxDepth) s.environment (← currentContext)
        value arity)
    return value
  | _ =>
    let (head, args) := spine stx
    let explicit := match head with
      | `(praExpr| @$_id:ident) | `(praExpr| @($_p:praExpr)) => true
      | _ => false
    let head ← match head with
      | `(praExpr| @$id:ident) => pure (← `(praExpr| $id:ident)).raw
      | `(praExpr| @($p:praExpr)) => pure p.raw
      | _ => pure head
    let `(praExpr| $id:ident) := head | do
      if args.isEmpty then throwErrorAt head "expected a numerical expression"
      return ← args.foldlM (fun f a => return .app f (← term a (some 0))) (← term head)
    let n := objectName id
    let s ← currentScope
    let (value, rest) ← match ← binding n with
      | some .local =>
        let value := ((s.aliases.find? (·.1 == n)).map (·.2)).getD
          (Metavariable.Term.bvar (s.names.locals.idxOf n))
        pure (value, args)
      | some .functionParameter => pure (Metavariable.Term.parameter (s.names.functions.idxOf n),
          args)
      | some .proof =>
        let type ← resolvedPredicate s.context.proofs[s.names.proofs.idxOf n]!
        let type ← showPredicate (← displayNames)
          (Bridge.betaReducePredicate (← projection) (← getMaxDepth) type)
        let expected ← match expected with
          | some arity => do
            let type ← delabArity arity
            pure m!"a numerical argument of type {← formatSyntax `praExpr type}"
          | none => pure m!"a numerical expression"
        throwArgumentErrorAt id m!"expected {expected},\nbut {n} is a proof of \
          {← formatSyntax `praExpr type}"
      | some _ => throwArgumentErrorAt id m!"`{n}` is not a numerical name"
      | none =>
        let .function d ← lookup id | throwArgumentErrorAt id "expected a function definition"
        let (actuals, _, rest) ←
          declarationArguments stx d.name d.parameterSignature args explicit
        let value := match primitiveDeclaration? d.name with
          | some { construction := .term t, .. } => (Metavariable.Term.ofCore t).instantiate actuals
          | _ => Metavariable.Term.definition d.name actuals
        pure (value, rest)
    remember head (.term value)
    rest.foldlM (fun f a => return .app f (← term a (some 0))) value

private partial def predicate (stx : Syntax) (expected : Option Core.PredicateSignature := none) :
    ObjectElabM Predicate :=
  withGoal stx (expected.map .predicate)
      (fun view depth p s => (Bridge.predicateType view depth
        s.environment s.context p).map .predicate) do
    if (unparen stx).isOfKind ``praHole then
      let some sig := expected | throwErrorAt stx "a predicate hole needs an expected signature"
      return ← unknownPredicate stx sig
    rejectHole (unparen stx)
    let p ← predicateBody (unparen stx) expected
    let p ← resolvedPredicate p
    remember stx (.predicate p)
    return p

/-- Elaborate `stx` and check that it is a formula (arity `0`). -/
private partial def formula (stx : Syntax) : ObjectElabM Predicate := do
  let p ← predicate stx
  let s ← currentScope
  let _ ← checked stx (Bridge.formulaSort (← projection) (← getMaxDepth) s.environment (←
      currentContext) p)
  return p

private partial def predicateBody (stx : Syntax)
    (expected : Option Core.PredicateSignature) : ObjectElabM Predicate := do
  let formula : Core.PredicateSignature := ⟨0, (expected.map (·.sort)).getD .prop⟩
  match stx with
  | `(praExpr| ($value:praExpr : $type:praExpr)) =>
    let some sig := predicateSignature? type | throwErrorAt type "expected a predicate type"
    let value ← predicate value sig
    let s ← currentScope
    checked stx (Bridge.checkPredicate (← projection) (← getMaxDepth) s.environment (←
        currentContext) value sig)
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
  | `(praExpr| ∀ {$xs:praBinder* : Nat}, $body:praExpr)
  | `(praExpr| ∀ {$xs:praBinder*}, $body:praExpr) =>
    quantify true xs.toList body true
  | `(praExpr| ∃ $xs:praBinder* : Nat, $body:praExpr)
  | `(praExpr| ∃ $xs:praBinder*, $body:praExpr) =>
    quantify false xs.toList body
  | _ =>
    let (head, args) := spine stx
    let explicit := match head with
      | `(praExpr| @$_id:ident) | `(praExpr| @($_p:praExpr)) => true
      | _ => false
    let head ← match head with
      | `(praExpr| @$id:ident) => pure (← `(praExpr| $id:ident)).raw
      | `(praExpr| @($p:praExpr)) => pure p.raw
      | _ => pure head
    let `(praExpr| $id:ident) := head | do
      if args.isEmpty then throwErrorAt head "expected a predicate expression"
      return ← args.foldlM (fun p a => return .app p (← term a (some 0))) (← predicate head)
    let n := objectName id
    let s ← currentScope
    let (value, rest) ← match ← binding n with
      | some .predicateParameter =>
        let value := ((s.predicateAliases.find? (·.1 == n)).map (·.2)).getD
          (Predicate.parameter (s.names.predicates.idxOf n))
        pure (value, args)
      | some _ => throwArgumentErrorAt id m!"`{n}` is not a predicate name"
      | none =>
        let .predicate d ← lookup id | throwArgumentErrorAt id "expected a predicate definition"
        let (fs, ps, rest) ← declarationArguments stx d.name d.parameters args explicit
        let value := match primitiveDeclaration? d.name with
          | some { construction := .predicate p, .. } => (Predicate.ofCore p).instantiate fs ps
          | _ => Predicate.definition d.name fs ps
        pure (value, rest)
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
      let s ← currentScope
      checked stx (Bridge.checkTerm (← projection) (← getMaxDepth) s.environment (←
          currentContext) value arity)
    else
      let _ ← inferTerm stx value
      pure ()
    return .letTerm (objectName id) value (← withAlias id value (predicate body
        expected))
  | .predicate =>
    let value ← predicate value (annotation.bind predicateSignature?)
    if let some type := annotation then
      let some sig := predicateSignature? type | throwErrorAt type "expected a predicate type"
      let s ← currentScope
      checked stx (Bridge.checkPredicate (← projection) (← getMaxDepth) s.environment (←
          currentContext) value sig)
    else
      let _ ← inferPredicate stx value
      pure ()
    return .letPredicate (objectName id) value (← withPredicateAlias id value
        (predicate body expected))
  | .theoremE => throwErrorAt stx "a predicate let cannot bind a proof"

private partial def declarationArguments (stx : Syntax) (name : Name)
    (parameters : List Core.Parameter) (args : List Syntax) (explicit : Bool := false)
    (inferred : List (Name × Predicate) := []) :
    ObjectElabM (List Metavariable.Term × List Predicate × List Syntax) := do
  let flags := if explicit then [] else parameters.map fun
    | .function binder _ | .predicate binder _ => binder.isImplicit
  let mut positional := []
  let mut named : List (Name × Syntax) := []
  for arg in args do
    if let `(praExpr| ($id:ident := $value:praExpr)) := arg then
      let n := objectName id
      if named.any (·.1 == n) then throwErrorAt arg "duplicate named argument `{n}`"
      named := named ++ [(n, value.raw)]
    else positional := positional ++ [arg]
  if named.isEmpty && !flags.any id && positional.length < parameters.length then
    match (← currentScope).environment.lookup name with
    | some (.function _) =>
      throwErrorAt stx "`{name}` requires {parameters.length} explicit function parameters"
    | _ => throwErrorAt stx "`{name}` requires {parameters.length} explicit parameters"
  let mut fs := []
  let mut ps := []
  for parameter in parameters, i in *...parameters.length do
    let n : Name := match parameter with | .function n _ | .predicate n _ => n.name
    let supplied := named.find? (·.1 == n)
    let arg ← if let some (_, value) := supplied then
      named := named.filter (·.1 != n)
      pure (some value)
    else if (flags[i]?).getD false then pure none
    else match positional with
      | a :: rest => positional := rest; pure (some a)
      | [] => throwErrorAt stx "missing explicit argument `{n}` to `{name}`"
    match parameter with
    | .function _ arity =>
      fs := fs ++ [← match arg with
        | some a => do
          let value ← term a arity
          checked a (Bridge.checkTerm (← projection) (← getMaxDepth) (← currentScope).environment
            (← currentContext) value arity)
          pure value
        | none => unknownTerm stx arity n]
    | .predicate _ sig =>
      ps := ps ++ [← match arg with
        | some a => do
          let value ← predicate a sig
          checked a (Bridge.checkPredicate (← projection) (← getMaxDepth)
            (← currentScope).environment
            (← currentContext) value sig)
          pure value
        | none =>
          match inferred.find? (·.1 == n) with
          | some (_, value) => pure value
          | none => unknownPredicate stx sig n]
  for (n, value) in named do
    let value : TSyntax `praExpr := ⟨value⟩
    positional := positional ++ [(← `(praExpr| ($(mkIdent n):ident := $value))).raw]
  return (fs, ps, positional)

private partial def quantify (all : Bool) (xs : List (TSyntax `praBinder))
    (body : Syntax) (implicit : Bool := false) : ObjectElabM Predicate := do
  match xs with
  | [] => predicate body (some ⟨0, .prop⟩)
  | x :: xs =>
    let p ← withLocal x (binderName x) 0 (quantify all xs body implicit)
    let info : Core.BinderInfo := ⟨binderName x, implicit⟩
    return (if all then Predicate.all else Predicate.ex) (.lam info p)

end

private inductive Attempt (α : Type) where
  | ready (value : α)
  | blocked (blocker : Blocking)
  | failed (error : Exception)

-- When a check blocks on an unassigned metavariable, roll back state and info-tree changes so it
-- can be retried; on a source error, keep the partial info tree so cursor goals are preserved.
private def attemptObject (action : ObjectElabM α) : ObjectElabM (Attempt α) := do
  let saved ← get
  let info ← getInfoState
  try return .ready (← action) catch ex =>
    if ex.isInterrupt then throw ex
    let blocker := (← get).blocking
    if let .internal id _ := ex then
      if id == blockedExceptionId then
        -- Return an inner task's error immediately rather than waiting on blocked metavariables.
        for task in (← get).tasks do
          if let .failed error := task.status then return .failed error
        set saved
        modifyInfoState fun _ => info
        if let some blocker := blocker then
          let dependencies := blocker.dependencies.filter
            (Metavariable.Frontend.allocated saved.unification)
          unless dependencies.isEmpty do return .blocked { blocker with dependencies }
        return .failed (.error (← getRef) m!"cannot infer this expression; add a type annotation")
    return .failed ex

private def scheduleProof (ref : Syntax) (type : Predicate)
    (status : TaskStatus := .ready) : ObjectElabM ProofResult := do
  let scope ← read
  let value ← runSolver (Metavariable.Frontend.freshProof type scope.context scope.localIds)
  let .mvar goal _ _ := value | throwError "expected a proof metavariable"
  let failed := match status with | .failed _ => true | _ => false
  let infoHole ← if (← editorInfoEnabled) && !failed then do
    let hole : MVarId := ⟨← liftTermElabM (mkFreshUserName `praTask)⟩
    pushInfoTree (.hole hole)
    pure (some hole)
  else pure none
  modify fun s => { s with tasks := s.tasks.push ⟨ref, scope, goal, status, infoHole⟩ }
  return ⟨value, type⟩

mutual

private partial def proof (stx : Syntax) (expected : Option Predicate := none) :
    ObjectElabM ProofResult := do
  match ← attemptObject (proofNow stx expected) with
  | .ready p => return p
  | .blocked blocker =>
    let type ← match expected with
      | some type => pure type
      | none => unknownPredicate stx ⟨0, .prop⟩
    scheduleProof stx type (.waiting blocker)
  | .failed error =>
    let type ← match expected with
      | some type => pure type
      | none => unknownPredicate stx ⟨0, .prop⟩
    scheduleProof stx type (.failed error)

private partial def proofNow (stx : Syntax) (expected : Option Predicate) :
    ObjectElabM ProofResult :=
  withGoal stx (expected.map .proof) (fun _ _ p _ => .ok (.proof p.type)) do
    let hole := unparen stx
    if hole.isMissing || hole.isOfKind ``praHole || hole.isOfKind ``praSyntheticHole ||
        hole.isOfKind `LeanPRA.Surface.recoveredHole then
      if (← get).collectingTacticGoals && hole.isOfKind ``praHole then
        throwErrorAt stx "cannot infer PRA proof placeholder `_`; use `?_` to create a new goal"
      let type ← match expected with
        | some type => pure type
        | none => unknownPredicate stx ⟨0, .prop⟩
      let scope ← read
      let value ← runSolver (Metavariable.Frontend.freshProof type scope.context scope.localIds)
      if (← get).collectingTacticGoals && hole.isOfKind ``praSyntheticHole then
        let .mvar id _ _ := value | throwError "expected a proof metavariable"
        modify fun s => { s with tacticGoals := s.tacticGoals.push (id, scope) }
      else
        modify fun s => { s with holes := s.holes.push ⟨stx, scope, type⟩ }
      return ⟨value, type⟩
    let p ← proofBody hole expected
    if let some type := expected then constrainFormulas p.type type stx
    if (← editorInfoEnabled) then
      let hole : MVarId := ⟨← liftTermElabM (mkFreshUserName `praProofInfo)⟩
      pushInfoTree (.hole hole)
      let scope ← read
      modify fun s => { s with proofOrigins := s.proofOrigins.push (stx, scope, p.type, hole) }
    return p

private partial def proofBody (stx : Syntax) (expected : Option Predicate) :
    ObjectElabM ProofResult := do
  match stx with
  | `(praExpr| by $seq:praTacticSeq) =>
    proofBy seq (← requireExpected stx expected)
  | `(praExpr| ()) => return ProofResult.ready .trueIntro .true
  | `(praExpr| ($p:praExpr : $type:praExpr)) =>
    let type ← formula type
    return (← proof p type).map (.ascribe type) type
  | `(praExpr| fun $_xs:praFunBinder* => $_body:praExpr)
  | `(praExpr| fun $_xs:praFunBinder* : $_type:praExpr => $_body:praExpr) =>
    proofLambda stx expected
  | `(praExpr| ($a:praExpr, $bs:praExpr,*)) =>
    proofTuple stx (a.raw :: bs.getElems.toList.map (·.raw)) expected
  | `(praExpr| let ($a:praBinder, $bs:praBinder,*) := $p:praExpr; $body:praExpr) =>
    let p ← proof p
    destructure stx (a.raw :: bs.getElems.toList.map (·.raw)) p
      (← resolvedProofType stx p) body expected
  | `(praExpr| let $id:ident := $value:praExpr; $body:praExpr) =>
    proofLet stx id none value body expected
  | `(praExpr| let $id:ident : $type:praExpr := $value:praExpr; $body:praExpr) =>
    proofLet stx id (some type.raw) value body expected
  | _ =>
    let (head, args) := spine stx
    let explicit := match head with
      | `(praExpr| @$_id:ident) | `(praExpr| @($_p:praExpr)) => true
      | _ => false
    let head ← match head with
      | `(praExpr| @$id:ident) => pure (← `(praExpr| $id:ident)).raw
      | `(praExpr| @($p:praExpr)) => pure p.raw
      | _ => pure head
    if let `(praExpr| induction (motive := $motive:praExpr)) := head then
      let id := mkIdentFrom head[0] `induction
      let .theoremE d ← lookup id | throwErrorAt head "expected the induction declaration"
      let named ← `(praExpr| (motive := $motive))
      return ← constantProof stx d (named.raw :: args) expected explicit
    let `(praExpr| $id:ident) := head | do
      if args.isEmpty && !explicit then throwErrorAt head "expected a proof expression"
      return ← applyProof stx (← proof head) args expected explicit
    let n := objectName id
    let s ← read
    match ← binding n with
    | some .proof =>
      let p := Proof.hyp (s.names.proofs.idxOf n)
      remember head (.proof p)
      applyProof stx (← readyProof head p) args expected explicit
    | some _ => throwArgumentErrorAt id m!"`{n}` is not a proof name"
    | none =>
      let .theoremE d ← lookup id | throwArgumentErrorAt id "expected a theorem"
      constantProof stx d args expected explicit

private partial def proofBy (seq : TSyntax ``praTacticSeq) (type : Predicate) :
    ObjectElabM ProofResult := fun scope stateRef => do
  let run {α : Type} (s : Scope) (action : ObjectElabM α) : CommandElabM α := action s stateRef
  let root ← run scope do
    let root ← runSolver (Metavariable.Frontend.freshProof type scope.context scope.localIds)
    let .mvar id _ _ := root | throwError "expected a proof metavariable"
    modify fun s => { s with tacticGoals := s.tacticGoals.push (id, scope) }
    return root
  let .mvar rootId _ _ := root | throwError "expected a proof metavariable"
  let goalScope (id : Nat) : CommandElabM Scope := do
    let some (_, s) := (← stateRef.get).tacticGoals.find? (·.1 == id)
      | throwError "unknown PRA tactic goal"
    return { s with inTactic := true }
  let goalType (id : Nat) : ObjectElabM Predicate := do
    let some entry := (← get).unification.proofs[id]?
      | throwError "unknown PRA proof metavariable"
    if entry.value.isSome then throwError "PRA goal is already assigned"
    resolvedPredicate entry.type
  let checkProgress : ObjectElabM Unit := do
    let mut budget ← getMaxDepth
    repeat
      if budget == 0 then throwError "PRA tactic inference limit exhausted"
      budget := budget - 1
      drainTasks
      let revision := (← get).unification.revision
      runSolver (Metavariable.Frontend.settle (← getMaxDepth) (← currentScope).environment)
      if revision == (← get).unification.revision then break
    for task in (← get).tasks do
      if let .failed error := task.status then throw error
    if let (_, _, error) :: _ := Metavariable.Frontend.conflicts (← get).unification then
      throwError "PRA tactic proof type mismatch: {error}"
  let ctx : Tactic.Context := {
    inspect := fun id => do
      run (← goalScope id) do
        let view ← projection
        let aliases ← (← read).aliases.mapM fun (name, value) => do
          return (name, view.encodeTerm (← resolvedTerm value))
        let predicateAliases ← (← read).predicateAliases.mapM fun (name, value) => do
          return (name, view.encodePredicate (← resolvedPredicate value))
        return {
          target := (← goalType id)
          context := (← currentContext)
          names := { (← displayNames) with termAliases := aliases, predicateAliases }
          environment := (← currentScope).environment
          projection := (← projection)
          maxDepth := (← getMaxDepth) }
    refine := fun id stx => do
      run (← goalScope id) do
        let type ← goalType id
        let start := (← get).tacticGoals.size
        let initial := (← get).unification
        let collecting := (← get).collectingTacticGoals
        modify fun s => { s with collectingTacticGoals := true }
        try
          let p ← proofNow (← expandPraSyntax stx) type
          checkProgress
          runSolver (Metavariable.Frontend.assignProof (← getMaxDepth) id p.value)
          let state ← get
          let goals := (state.tacticGoals.toList.drop start).filterMap fun (id, _) =>
            if (state.unification.proofs[id]?).any (·.value.isNone) then some id else none
          if goals.isEmpty then
            unless (state.unification.terms.toList.drop initial.terms.size).all (·.value.isSome) &&
                (state.unification.predicates.toList.drop initial.predicates.size).all
                  (·.value.isSome) do
              throwErrorAt stx "PRA tactic could not infer its implicit arguments"
          return goals
        finally
          modify fun s => { s with collectingTacticGoals := collecting }
    close := fun id p => do
      run (← goalScope id) do
        let target ← goalType id
        let p ← resolvedProof p
        let proof ← readyProof (← getRef) p
        constrainFormulas proof.type target
        checkProgress
        runSolver (Metavariable.Frontend.assignProof (← getMaxDepth) id p)
    infer := fun id stx expected => do
      run (← goalScope id) do
        let p ← proofNow (← expandPraSyntax stx) none
        if let some expected := expected then
          constrainFormulas p.type (← formula (← expandPraSyntax expected)) stx
        checkProgress
        resolvedPredicate p.type
    term := fun id stx arity => do
      run (← goalScope id) do
        let value ← term (← expandPraSyntax stx) arity
        checkProgress
        resolvedTerm value
    proof := fun id stx => do
      run (← goalScope id) do
        let result ← proofNow (← expandPraSyntax stx) none
        checkProgress
        return (← resolvedProof result.value, ← resolvedPredicate result.type)
    save := do
      let saved ← stateRef.get
      let commandState ← get
      return do stateRef.set saved; set commandState
    snapshot := fun goals ref => do
      unless ← editorInfoEnabled do
        return .ofCommandInfo { elaborator := `Delab, stx := .missing }
      unless (ref.getRange? (canonicalOnly := true)).isSome do
        return .ofCommandInfo { elaborator := `Delab, stx := .missing }
      let views ← goals.mapM fun id => do
        run (← goalScope id) do
          let type ← goalType id
          let view ← projection
          let scope ← currentScope
          return { environment := scope.environment
                   context := view.encodeContext (← currentContext)
                   names := (← displayNames)
                   bindings := scope.bindings.reverse.map (·.project view)
                   target := some (.proof (view.encodePredicate type)) : GoalView }
      makeGoalsInfo ref views
  }
  let (_, goals) ← (Tactic.evalTacticSeq seq).run ctx |>.run [rootId]
  unless goals.isEmpty do
    let first := goals.head!
    run (← goalScope first) do
      let target ← showPredicate (← displayNames) (← goalType first)
      throwErrorAt seq "unsolved PRA goals ({goals.length})\n⊢ {← formatSyntax `praExpr target}"
  return ⟨root, type⟩

private partial def proofLambda (stx : Syntax) (expected : Option Predicate) :
    ObjectElabM ProofResult := do
  let (n, annotation, body, ref) ← lambdaBody stx
  if let some type := expected then
    match ← exposeFormula stx type with
    | .imp a b =>
      let a ← if let some annotation := annotation then do
        let actual ← formula annotation
        constrainFormulas a actual
        pure actual
      else pure a
      return (← proofBinderBody ref a body (some b)).map (.impIntro n a) (.imp a b)
    | .all motive =>
      requirePlainBinder ref
      numericalBinder annotation
      return (← withLocal ref n 0 (closeProof (proof body (Predicate.app motive.shift (.bvar 0)))))
        |>.map (.forallIntro n motive) (.all motive)
    | .parameter _ =>
      if annotation.isSome then return ← proofLambda stx none
      blockOn type "the lambda needs the shape of its expected formula"
      throwErrorAt stx "a proof lambda needs typed binders or an expected formula"
    | _ =>
      blockOn type "the lambda needs the shape of its expected formula"
      throwErrorAt stx "expected an implication or universal formula for a proof lambda"
  let some annotation := annotation
    | throwErrorAt stx "a proof lambda needs typed binders or an expected formula"
  if numericalArity? annotation == some 0 then
    requirePlainBinder ref
    let (p, type) ← withLocal ref n 0 do
      let p ← closeProof (proof body)
      return (p, ← resolvedProofType body p)
    return p.map (.forallIntro n (.lam n type)) (.all (.lam n type))
  let a ← formula annotation
  let p ← proofBinderBody ref a body none
  return p.map (.impIntro n a) (.imp a p.type)

private partial def proofTuple (stx : Syntax) (entries : List Syntax)
    (expected : Option Predicate) : ObjectElabM ProofResult := do
  match entries with
  | [] => return ProofResult.ready .trueIntro .true
  | [last] => proof last expected
  | first :: rest =>
    if let some type := expected then
      match ← exposeFormula stx type with
      | .and a b =>
        let left ← proof first a
        let right ← proofTuple stx rest b
        return ProofResult.map₂ .andIntro (.and a b) left right
      | .ex motive =>
        let n ← term first (some 0)
        let s ← currentScope
        checked first (Bridge.checkTerm (← projection) (← getMaxDepth) s.environment (←
            currentContext) n 0)
        return (← proofTuple stx rest (Predicate.app motive n)).map
          (.existsIntro motive n) (.ex motive)
      | _ =>
        blockOn type "the tuple needs the shape of its expected formula"
        throwErrorAt stx "a proof tuple needs a conjunction or existential formula"
    let left ← proof first
    let right ← proofTuple stx rest none
    return ProofResult.map₂ .andIntro (.and left.type right.type) left right

private partial def proofLet (stx id : Syntax) (annotation : Option Syntax)
    (value body : Syntax) (expected : Option Predicate) : ObjectElabM ProofResult := do
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
      let s ← currentScope
      checked stx (Bridge.checkPredicate (← projection) (← getMaxDepth) s.environment (←
          currentContext) value sig)
    else
      let _ ← inferPredicate stx value
      pure ()
    let p ← withPredicateAlias id value (proof body expected)
    return p.map (.letPredicate (objectName id) value) p.type
  | .function =>
    let value ← term value (annotation.bind numericalArity?)
    if let some type := annotation then
      let some arity := numericalArity? type | throwErrorAt type "expected a numerical type"
      let s ← currentScope
      checked stx (Bridge.checkTerm (← projection) (← getMaxDepth) s.environment (←
          currentContext) value arity)
    else
      let _ ← inferTerm stx value
      pure ()
    let p ← withAlias id value (proof body expected)
    return p.map (.letTerm (objectName id) value) p.type
  | .theoremE =>
    let type ← annotation.mapM formula
    let p ← proof value type
    let type ← match type with | some type => pure type | none => resolvedProofType value p
    let q ← withProof id (objectName id) type (closeProof (proof body expected))
    return ProofResult.map₂ (.letE (objectName id) type) q.type p q

private partial def proofBinderBody (ref : Syntax) (domain : Predicate) (body : Syntax)
    (expected : Option Predicate) : ObjectElabM ProofResult := do
  if ref.isOfKind ``praTupleBinder then
    withAnonymousProof domain <| closeProof do
      bindPattern ref (ProofResult.ready (.hyp 0) domain) domain expected
        (fun expected => proof body expected)
  else withProof ref (binderName ref) domain (closeProof (proof body expected))

/-- Destructure `pattern` over `value : type` using `Proof.letE`, `andLeft`/`andRight`, and
`existsElim`. -/
private partial def bindPattern (pattern : Syntax) (value : ProofResult) (type : Predicate)
    (expected : Option Predicate) (action : Option Predicate → ObjectElabM ProofResult) :
    ObjectElabM ProofResult := do
  let `(praFunBinder| ($first:praFunBinder, $rest:praFunBinder,*)) := pattern | do
    let name := binderName pattern
    let body ← if name == .anonymous then withAnonymousProof type do
      remember pattern (.proof (.hyp 0))
      closeProof (action expected)
    else withProof pattern name type (closeProof (action expected))
    return ProofResult.map₂ (.letE name type) body.type value body
  let tail ← tuplePattern (rest.getElems.toList.map (·.raw))
  match ← exposeFormula pattern type with
  | .and left right =>
    let destruct (index : Nat) := do
      let start ← read
      bindPattern first (ProofResult.ready (.impElim (.andLeft left right) (.hyp index)) left)
        left expected
          fun expected => do
        let current ← read
        let index := index + current.context.proofs.length - start.context.proofs.length
        let shift := current.context.locals.length - start.context.locals.length
        let left := left.shift shift
        let right := right.shift shift
        bindPattern tail (ProofResult.ready (.impElim (.andRight left right) (.hyp index)) right)
          right expected action
    let body ← withAnonymousProof type (closeProof (destruct 0))
    return ProofResult.map₂ (.letE .anonymous type) body.type value body
  | .ex motive =>
    requirePlainBinder first
    let outer ← read
    let name := binderName first
    let hypothesis := Predicate.app motive.shift (.bvar 0)
    let id ← runSolver Metavariable.Frontend.freshLocal
    let extend s := { (s.pushLocal name 0 first).pushAnonymousProof hypothesis with
      localIds := id :: s.localIds }
    let (body, target) ← withReader extend do
      remember first (.term (.bvar 0))
      let body ← closeProof (bindPattern tail (ProofResult.ready (.hyp 0) hypothesis) hypothesis
        (expected.map Predicate.shift) action)
      let target ← match expected with
        | some target => pure target
        | none => do
          drainTasks
          existentialResult pattern outer (← resolvedProofType pattern body)
      return (body, target)
    return ProofResult.map₂ (fun value body =>
      .impElim (.impElim (.existsElim motive target) value)
        (.forallIntro name (.lam ⟨name, false⟩ (.imp hypothesis target.shift))
          (.impIntro .anonymous hypothesis body))) target value body
  | _ =>
    blockOn type "destructuring needs the shape of its proof type"
    throwErrorAt pattern "tuple destructuring requires a conjunction or existential proof"

private partial def destructure (_stx : Syntax) (binders : List Syntax) (p : ProofResult)
    (type : Predicate) (body : Syntax) (expected : Option Predicate) : ObjectElabM ProofResult := do
  let pattern ← tuplePattern binders
  bindPattern pattern p type expected (fun expected => proof body expected)

private partial def applyInferred (stx : Syntax) (head : ProofResult) (type : Predicate)
    (args : List Syntax) (expected : Option Predicate) (explicit : Bool := false) :
    ObjectElabM ProofResult := do
  let mut type := type
  let mut result := head
  let mut positional := []
  let mut named : List (Name × Syntax) := []
  let mut argumentIndex := 0
  for arg in args do
    if let `(praExpr| ($id:ident := $value:praExpr)) := arg then
      let n := objectName id
      if named.any (·.1 == n) then throwErrorAt arg "duplicate named argument `{n}`"
      named := named ++ [(n, value.raw)]
    else positional := positional ++ [arg]
  repeat
    let exposed ← exposeFormula stx (← resolvedPredicate type)
    let implicitBinder := match exposed with
      | .all (.lam info _) => info.isImplicit && !explicit
      | _ => false
    if positional.isEmpty && named.isEmpty && !implicitBinder then break
    match exposed with
    | .imp domain target =>
      let arg :: rest := positional
        | throwErrorAt stx "unknown named argument `{named.head!.1}`"
      positional := rest
      argumentIndex := argumentIndex + 1
      let p ← withReader
        (fun s => { s with reason := s!"argument {argumentIndex} of this application" })
        (scheduleProof arg domain)
      result := ProofResult.map₂ .impElim target result p
      type := target
    | .all motive =>
      let n : Name := match motive with | .lam info _ => info.name | _ => .anonymous
      let supplied := named.find? (·.1 == n)
      let t ← if let some (_, arg) := supplied then
        named := named.filter (·.1 != n)
        term arg (some 0)
      else if implicitBinder then unknownTerm stx 0 n
      else match positional with
        | arg :: rest => positional := rest; term arg (some 0)
        | [] => throwErrorAt stx "unknown named argument `{named.head!.1}`"
      type := .app motive t
      result := result.map (fun p => .forallElim p t) type
    | _ =>
      let before := (← get).unification.revision
      -- Earlier proof arguments often determine the head's type. Check them before guessing
      -- a type from the remaining arguments and the expected result.
      drainTasks
      if (← get).unification.revision != before then continue
      if let some target ← applicationTarget positional expected then
        constrainFormulas type target stx
      drainTasks
      if (← get).unification.revision != before then continue
      blockOn type "application is waiting for its function type"
      let displayedType ← showPredicate (← displayNames)
        (Bridge.betaReducePredicate (← projection) (← getMaxDepth) (← resolvedPredicate type))
      throwArgumentErrorAt stx m!"proof application requires an implication or universal formula\n\
        inferred: {← formatSyntax `praExpr displayedType}"
  if let some target := expected then
    withReader (fun s => { s with reason := "the expected result of this application" })
      (constrainFormulas type target stx)
  let resultType ← resolvedPredicate type
  if Metavariable.Frontend.hasImplicitBinders (← getMaxDepth) (← currentScope).environment ((←
      projection).encodePredicate resultType) then
    return result.map (.ascribe resultType) resultType
  return { result with type := resultType }

-- Run ready proof tasks and wake waiting tasks whose metavariable dependencies have been assigned,
-- elaborating each task in its saved `Scope`.
private partial def drainTasks : ObjectElabM Unit := do
  let mut budget := (← getMaxDepth) * ((← get).tasks.size + 1)
  repeat
    let mut progress := false
    for id in [: (← get).tasks.size] do
      let some task := (← get).tasks[id]? | continue
      let unification := (← get).unification
      let ready := match task.status with
        | .ready => true
        | .waiting blocker => blocker.dependencies.any (Metavariable.Frontend.assigned unification)
        | _ => false
      unless ready do continue
      if budget == 0 then throwErrorAt task.ref "elaboration task work limit exhausted"
      budget := budget - 1
      progress := true
      modify fun s => { s with tasks := s.tasks.modify id (fun t => { t with status := .running }) }
      let some goal := (← get).unification.proofs[task.goal]?
        | throwErrorAt task.ref "unknown proof metavariable"
      let action := withReader (fun _ => task.scope)
        (attemptObject (proofNow task.ref (some goal.type)))
      let result ← match task.infoHole with
        | some hole => withInfoHole hole action
        | none => action
      let status ← match result with
        | .ready p => do
          runSolver (Metavariable.Frontend.assignProof (← getMaxDepth) task.goal p.value)
          pure TaskStatus.done
        | .blocked blocker => pure (.waiting blocker)
        | .failed error => pure (.failed error)
      modify fun s => { s with tasks := s.tasks.modify id (fun t => { t with status }) }
    unless progress do break

private partial def applyProof (stx : Syntax) (p : ProofResult) (args : List Syntax)
    (expected : Option Predicate := none) (explicit : Bool := false) : ObjectElabM ProofResult := do
  applyInferred stx p (← resolvedProofType stx p) args expected explicit

/-- Reconstruct the expected formula for a proof head before `args` are applied to it. -/
private partial def applicationTarget (args : List Syntax) (expected : Option Predicate) :
    ObjectElabM (Option Predicate) := do
  let some target := expected | return none
  let mut target := target
  for arg in args.reverse do
    match ← expressionKind arg with
    | .function =>
      let argument ← term arg (some 0)
      let s ← currentScope
      checked arg (Bridge.checkTerm (← projection) (← getMaxDepth) s.environment (←
          currentContext) argument 0)
      let view ← projection
      let depth ← getMaxDepth
      let argument := Bridge.betaReduceTerm view depth (← resolvedTerm argument)
      target := Bridge.betaReducePredicate view depth (← resolvedPredicate target)
      target := .all (.lam .anonymous (abstractNumber argument.shift 0 target.shift))
    | .theoremE =>
      -- A proof hole receives its domain when the application consumes it. Elaborating it here
      -- as well would create a second goal that the resulting proof never uses.
      let domain ← if (arg.find? (·.isOfKind ``praSyntheticHole)).isSome then
        unknownPredicate arg ⟨0, .prop⟩
      else resolvedProofType arg (← proof arg)
      target := .imp domain target
    | .predicate => throwErrorAt arg "proof application requires a numerical term or proof"
  return some target

private partial def constantProof (stx : Syntax) (d : ProofSignature)
    (args : List Syntax) (expected : Option Predicate) (explicit : Bool) :
    ObjectElabM ProofResult := do
  let hasNamed := args.any fun arg => match arg with
    | `(praExpr| ($_id:ident := $_value:praExpr)) => true
    | _ => false
  let mut inferred := []
  -- The induction notation can infer its motive by generalizing the expected result.
  if d.name == `induction && !explicit && !hasNamed then
    if let _base :: step :: argument :: rest := args then
      inferred := [(`motive, ← inferInductionMotive stx step argument expected rest)]
  let (fs, ps, rest) ← declarationArguments stx d.name d.parameters args explicit inferred
  let value ← match primitiveDeclaration? d.name with
    | some { construction := .proof p, .. } =>
      match Metavariable.primitiveProof p fs ps with
      | some p => pure p
      | none => throwErrorAt stx "invalid primitive proof declaration {d.name}"
    | _ => pure (.theoremE d.name fs ps)
  applyInferred stx (ProofResult.ready value ((Predicate.ofCore d.type).instantiate fs ps))
    ((Predicate.ofCore d.type).instantiate fs ps) rest expected explicit

private partial def inferInductionMotive (stx step argument : Syntax)
    (expected : Option Predicate) (resultArgs : List Syntax) : ObjectElabM Predicate := do
  let argument ← term argument (some 0)
  let s ← currentScope
  checked stx (Bridge.checkTerm (← projection) (← getMaxDepth) s.environment (← currentContext)
      argument 0)
  let branch ← match unparen step with
    | `(praExpr| fun $_xs:praFunBinder* => $_body:praExpr)
    | `(praExpr| fun $_xs:praFunBinder* : $_type:praExpr => $_body:praExpr) =>
      let (x, annotation, rest, ref) ← plainLambdaBody step
      numericalBinder annotation
      pure (some (x, rest, ref))
    | _ => pure none
  let motive ← do
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
          let .all m ← exposeFormula step (← resolvedProofType step p)
            | throwErrorAt step "an induction step must prove a numerical universal formula"
          withLocal .missing .anonymous 0 do
            let .imp hypothesis _ ← exposeFormula step (.app m.shift (.bvar 0))
              | throwErrorAt step "an induction step must take an induction hypothesis"
            pure (some (Predicate.lam .anonymous hypothesis))
    match hintedMotive with
      | some motive => pure motive
      | none =>
        let target ← requireExpected stx (← applicationTarget resultArgs expected)
        let depth ← getMaxDepth
        -- Beta-reduce before abstracting `argument`, keeping definitions and `primrec` intact.
        let target := Bridge.betaReducePredicate (← projection) depth target
        let argument := Bridge.betaReduceTerm (← projection) depth argument
        pure (Predicate.lam .anonymous (abstractNumber argument.shift 0 target.shift))
  checked stx
    (Bridge.checkPredicate (← projection) (← getMaxDepth) s.environment (← currentContext) motive
        ⟨1, .qf⟩)
  return motive

end

private def parameterScope (environment : Core.Environment) (ps : Array Syntax) :
    CommandElabM (Scope × List Core.Parameter) := do
  let mut s : Scope := { environment }
  let mut parameters := []
  let mut expanded := #[]
  for p in ps do
    let (ids, type, hidden) ← match p with
      | `(praParam| ($ids:ident* : $type:praExpr)) => pure (ids, type, false)
      | `(praParam| {$ids:ident* : $type:praExpr}) => pure (ids, type, true)
      | _ => throwErrorAt p "expected a parameter group"
    for id in ids do
      expanded := expanded.push ((← `(praParam| ($id:ident : $type:praExpr))).raw, hidden)
  for (p, hidden) in expanded do
    let `(praParam| ($ids:ident* : $type:praExpr)) := p
      | throwErrorAt p "expected an explicit parameter"
    let id := ids[0]!
    let n := objectName id
    if s.bindings.any (·.name == n) then throwErrorAt id "duplicate parameter `{n}`"
    if let some arity := numericalArity? type then
      parameters := parameters ++ [.function ⟨n, hidden⟩ arity]
      s := { s with
        context := { s.context with functions := s.context.functions ++ [arity] }
        names := { s.names with functions := s.names.functions ++ [n] }
        bindings := .functionParameter n s.context.functions.length :: s.bindings
        references := (n, id) :: s.references }
      addExpressionInfo id environment
        ((⟨0, 0⟩ : Metavariable.Projection).encodeContext s.context) s.names
        (.term (.parameter (s.context.functions.length - 1))) id
    else if let some sig := predicateSignature? type then
      parameters := parameters ++ [.predicate ⟨n, hidden⟩ sig]
      s := { s with
        context := { s.context with predicates := s.context.predicates ++ [sig] }
        names := { s.names with predicates := s.names.predicates ++ [n] }
        bindings := .predicateParameter n s.context.predicates.length :: s.bindings
        references := (n, id) :: s.references }
      addExpressionInfo id environment
        ((⟨0, 0⟩ : Metavariable.Projection).encodeContext s.context) s.names
        (.predicate (.parameter (s.context.predicates.length - 1))) id
    else throwErrorAt type "expected a first-order numerical or predicate type"
  return (s, parameters)

private def completeGoalInfo : ObjectElabM Unit := do
  unless ← editorInfoEnabled do return
  let state ← get
  let failures := Metavariable.Frontend.conflicts state.unification
  let conflict := failures.any (fun (_, p, error) => !p.heuristic && !error.isExhausted &&
    match error with | .unsupported _ => false | _ => true) || state.tasks.any fun task =>
      match task.status with | .failed _ => true | _ => false
  let constraintFailure := !failures.isEmpty
  for goal in state.goals do
    withReader (fun _ => goal.scope) do
      let target ← goal.target.mapM fun
        | .proof p => return DraftGoalTarget.proof (← resolvedPredicate p)
        | other => pure other
      let bindings ← goal.scope.bindings.reverse.mapM fun
        | .termAlias n t => return DraftGoalBinding.termAlias n (← resolvedTerm t)
        | .predicateAlias n p => return DraftGoalBinding.predicateAlias n (← resolvedPredicate p)
        | other => pure other
      let waiting := match target with
        | some (.proof p) =>
          !(Metavariable.Frontend.predicateDependencies state.unification p).isEmpty
        | _ => false
      let status := if conflict then GoalStatus.conflicting
        else if waiting || constraintFailure then .blocked else .openGoal
      withInfoHole goal.infoHole do
        pushInfoTree (.node (← goalInfo goal.ref (CoreEnvironment.getState (← getEnv))
          (← currentContext)
          (← displayNames) bindings target status) goal.children)
  for task in state.tasks do
    if let .done := task.status then continue
    let some goal := state.unification.proofs[task.goal]? | continue
    let some hole := task.infoHole | continue
    if (← getInfoState).assignment.contains hole then continue
    withReader (fun _ => task.scope) do
      withInfoHole hole do
        let status := if conflict then GoalStatus.conflicting else .blocked
        pushInfoLeaf (← goalInfo task.ref (CoreEnvironment.getState (← getEnv)) (← currentContext)
          (← displayNames) task.scope.bindings.reverse
          (some (.proof (← resolvedPredicate goal.type)))
          status)

private def reportConflicts : ObjectElabM Unit := do
  let state ← get
  if let (id, problem, error) :: _ := Metavariable.Frontend.conflicts state.unification then
    let root := (Metavariable.Frontend.rootProblem state.unification id).getD problem
    let rootId := (Metavariable.Frontend.rootProblemId state.unification id).getD id
    let scope := (state.constraintScopes.find? (·.1 == rootId)).map (·.2) |>.getD (← read)
    withReader (fun _ => scope) do
      let ref := root.origin.ref
      if error.isExhausted then throwErrorAt ref "{error}"
      if let .unsupported message := error then
        throwErrorAt ref "cannot infer this application: {message}"
      let fileMap ← getFileMap
      let mut reasons := []
      for cause in Metavariable.Frontend.contributingProblems state.unification id do
        if cause == rootId then continue
        if let some p := state.unification.problems[cause]? then
          let line := p.origin.ref.getPos?.map fun pos => fileMap.toPosition pos |>.line
          let location := line.map (fun n => s!" on line {n}") |>.getD ""
          reasons := (p.origin.description ++ location) :: reasons
      let related := if reasons.isEmpty then "" else
        "\nOther requirements used here: " ++ String.intercalate "; " reasons.eraseDups
      let choice := if problem.heuristic then
        "\nThis inference choice failed; supply explicit arguments to choose another solution."
        else ""
      match root.constraint with
      | .predicate _ _ _ actual expected =>
        let names ← displayNames
        let actual ← resolvedPredicate actual
        let expected ← resolvedPredicate expected
        let actualKind := formulaKind? (← exposeFormula ref actual)
        let expectedKind := formulaKind? (← exposeFormula ref expected)
        let shape := match actualKind, expectedKind with
          | some a, some b => if a != b then
              s!"this application produces {a}, but {b} is expected\n" else ""
          | _, _ => ""
        let actual ← showPredicate names (Bridge.betaReducePredicate (← projection) (←
            getMaxDepth) actual)
        let expected ← showPredicate names (Bridge.betaReducePredicate (← projection) (←
            getMaxDepth) expected)
        let holes := if state.holes.isEmpty || problem.heuristic then "" else
          "\nFilling a proof hole alone cannot repair this conflict."
        throwErrorAt ref "proof type mismatch\n{shape}\
          expected: {← formatSyntax `praExpr expected}\n\
          inferred: {← formatSyntax `praExpr actual}\nwhile checking {root.origin.description}\
          \n{error.message}{related}{holes}{choice}"
      | _ => throwErrorAt ref "{error}{choice}"

private def completeExpressionInfo : ObjectElabM Unit := do
  unless ← editorInfoEnabled do return
  let state ← get
  let environment := (← currentScope).environment
  let depth ← getMaxDepth
  for origin in state.origins do
    let some hole := origin.infoHole | continue
    let resolveTerm := Metavariable.Frontend.resolveTerm state.unification origin.localIds depth
    let resolvePredicate :=
      Metavariable.Frontend.resolvePredicate state.unification origin.localIds depth
    let result : Except Metavariable.Frontend.Failure (Metavariable.Context ×
        Metavariable.Subject) := do
      let context := origin.site.context
      let context := Metavariable.Frontend.context state.unification context
      let context := { context with proofs := ← context.proofs.mapM resolvePredicate }
      let subject : Metavariable.Subject ← match origin.site.subject with
        | .term t => Metavariable.Subject.term <$> resolveTerm t
        | .predicate p => Metavariable.Subject.predicate <$> resolvePredicate p
        | .proof p => Metavariable.Subject.proof <$>
            (Metavariable.Frontend.resolveProof state.unification
              origin.localIds context.proofs.length depth p)
      pure (context, subject)
    match result with
    | .ok (context, subject) =>
      withInfoHole hole do
        expressionInfo origin.ref environment context origin.names subject origin.target
    | .error message => throwErrorAt origin.ref "{message}"
  for (ref, scope, type, hole) in state.proofOrigins do
    withReader (fun _ => scope) do
      let id := if ref.isIdent then ref else ref[0]
      let target := if id.isIdent then
        ((scope.references.find? (·.1 == objectName id)).map (·.2)).getD .missing else .missing
      withInfoHole hole do
        proofInfo ref (← displayNames) (← resolvedPredicate type) target
  -- Substitute info-tree holes before the entry snapshot records the info trees.
  modifyInfoState fun info =>
    { info with trees := info.trees.map (·.substitute info.assignment) }

private def finishPendingChecks : ObjectElabM Unit := do
  let scope ← currentScope
  let depth ← getMaxDepth
  let mut budget := depth
  repeat
    if budget == 0 then throwError "elaboration scheduling work limit exhausted"
    budget := budget - 1
    drainTasks
    let revision := (← get).unification.revision
    runSolver (Metavariable.Frontend.settle depth (← currentScope).environment)
    if (← get).unification.revision == revision then break
  for task in (← get).tasks do
    if let .failed error := task.status then throw error
  reportConflicts
  let state ← get
  if let some hole := state.holes[0]? then
    withReader (fun _ => hole.scope) do
      let type ← resolvedPredicate hole.type
      let type ← showPredicate (← displayNames) (Bridge.betaReducePredicate (← projection) depth
          type)
      throwErrorAt hole.ref "incomplete PRA expression\n\
        expected a proof of: {← formatSyntax `praExpr type}"
  for task in state.tasks do
    if let .waiting blocker := task.status then
      throwErrorAt task.ref "cannot infer this proof: {blocker.reason}\n\
        add an explicit argument or type annotation"
  let state ← get
  if let some (subject, name, id) := Metavariable.Frontend.unassigned? state.unification then
    let ref := (state.argumentSources.findRev? (·.1 == subject)).map (·.2)
      |>.getD scope.parentExpression
    let context ← currentContext
    let (kind, type) ← match subject with
      | .term t =>
        let arity ← checked ref (Bridge.termType (← projection) depth
          (← currentScope).environment context t)
        pure ("numerical", ← delabArity arity)
      | .predicate p =>
        let sig ← checked ref (Bridge.predicateType (← projection) depth
          (← currentScope).environment context
            p)
        pure ("predicate", ← delabPredicateType sig)
      | .proof _ => throwErrorAt ref "unexpected proof argument during inference"
    let binder := if name == .anonymous then "" else s!" for parameter `{name}`"
    let hint := if (unparen ref).isOfKind ``praHole then
      "replace this `_` with an explicit argument"
    else if name == .anonymous then "supply an explicit argument or type annotation"
    else s!"supply `({name} := ...)`, or use `@` to pass implicit arguments explicitly"
    throwErrorAt ref "cannot infer {kind} argument ?{id}{binder} : {← formatSyntax `praExpr type}\n\
      could not determine its value from the surrounding types\n{hint}"
  runSolver (Metavariable.Frontend.finish depth (← currentScope).environment)

private def runObject (s : Scope) (action : ObjectElabM α) : CommandElabM α :=
  (do
    try
      action
    finally
      completeGoalInfo
      completeExpressionInfo).run s |>.run'
        { unification :=
            Metavariable.Frontend.empty s.context.functions.length s.context.predicates.length }

private inductive DraftDeclaration where
  | function (arity : Nat) (body : Metavariable.Term)
  | predicate (signature : Core.PredicateSignature) (body : Predicate)
  | theoremE (type : Predicate) (body : Proof)

/-- Elaborate a `def` or `theorem` declaration, check it with `Core.checkDeclaration`,
and publish it. -/
def elaborateDeclaration (stx : Syntax) : CommandElabM Unit := do
  let stx ← expandPraSyntax stx
  let (doc?, stx) ← match stx with
    | `(praDecl| $doc:docComment $decl:praDecl) =>
      pure (some (← getDocStringText doc), decl.raw)
    | _ => pure (none, stx)
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
      finishPendingChecks
      let type ← resolvedPredicate type
      let _ ← checked stx (Bridge.formulaSort (← projection) (← getMaxDepth) environment (←
          currentContext) type)
      let draft ← proof body type
      finishPendingChecks
      pure (DraftDeclaration.theoremE type (← resolvedProof draft.value))
    else if let some arity := numericalArity? type then
      unless s.context.predicates.isEmpty do
        throwErrorAt id "numerical definitions cannot take predicate parameters"
      pure (DraftDeclaration.function arity (← term body arity))
    else if let some sig := predicateSignature? type then
      pure (DraftDeclaration.predicate sig (← predicate body sig))
    else throwErrorAt type "expected a first-order numerical or predicate result type"
    unless isTheorem do finishPendingChecks
    let complete {α} (result : Except Metavariable.Failure α) : ObjectElabM α :=
      match result with
      | .ok value => pure value
      | .error error => throwErrorAt stx "{error}"
    let declaration ← match declaration with
      | .function arity body =>
        let body ← complete (Metavariable.Frontend.completeTerm (← resolvedTerm body))
        pure (Core.Declaration.function ⟨name, parameters.filterMap (fun
          | .function info k => some ⟨k, info⟩ | _ => none), arity, body⟩)
      | .predicate sig body =>
        let body ← complete (Metavariable.Frontend.completePredicate (← resolvedPredicate body))
        pure (Core.Declaration.predicate ⟨name, parameters, sig, body⟩)
      | .theoremE type body =>
        let type ← complete (Metavariable.Frontend.completePredicate (← resolvedPredicate type))
        let body ← complete (Metavariable.Frontend.completeProof (← resolvedProof body))
        pure (Core.Declaration.theoremE ⟨name, parameters, type, body⟩)
    -- Share repeated syntax before checking and storing the declaration.
    let declaration := ShareCommon.shareCommon' declaration
    checked stx (Core.checkDeclaration (← getMaxDepth)
      (CoreEnvironment.getState (← getEnv)) declaration)
  -- Reject missing syntax only after elaboration so goal info is still recorded at the cursor.
  if stx.hasMissing then
    throwErrorAt stx "incomplete PRA declaration"
  modifyEnv (publishDeclaration · environment name)
  let metadata : DeclarationMetadata := { location? := ← sourceLocation id, doc? }
  modifyEnv (declarationMetadata.addEntry · (name, metadata))
  if let some d := environment.lookup name then addDeclarationInfo id d

/-- Elaborate `#check stx` and log its inferred Core type. -/
def elaborateCheck (stx : Syntax) : CommandElabM Unit := do
  let stx ← expandPraSyntax stx
  let s : Scope := { environment := CoreEnvironment.getState (← getEnv) }
  if let `(praExpr| $id:ident) := unparen stx then
    let n := objectName id
    if let some d ← resolveSignature? s.environment n then
      addDeclarationInfo stx d
      logInfoAt stx (← delabSignature d)
      return
  runObject s do
    let output ← match ← expressionKind stx with
    | .function =>
      let t ← term stx
      let arity ← inferTerm stx t
      pure m!"{← formatSyntax `praExpr (← showTerm {} t)} : \
        {← formatSyntax `praExpr (← delabArity arity)}"
    | .predicate =>
      let p ← predicate stx
      let sig ← inferPredicate stx p
      pure m!"{← formatSyntax `praExpr (← showPredicate {} p)} : \
        {← formatSyntax `praExpr (← delabPredicateType sig)}"
    | .theoremE =>
      let draft ← proof stx
      finishPendingChecks
      let type ← resolvedProofType stx draft
      let p ← resolvedProof draft.value
      pure m!"{← formatSyntax `praExpr (← showProof {} p)} : \
        {← formatSyntax `praExpr (← showPredicate {} type)}"
    finishPendingChecks
    logInfoAt stx output

/-- Elaborate `#print id` and log the delaborated declaration. -/
def elaboratePrint (id : Syntax) : CommandElabM Unit := do
  let s : Scope := { environment := CoreEnvironment.getState (← getEnv) }
  let signature ← runObject s (lookup id)
  if let some d := s.environment.lookup signature.name then
    logInfoAt id m!"{← formatSyntax `praDecl (← delabDeclaration d)}"
  else
    logInfoAt id m!"primitive {← delabSignature signature}"

end LeanPRA.Surface
