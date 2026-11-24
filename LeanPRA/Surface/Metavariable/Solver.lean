module

public meta import LeanPRA.Surface.Metavariable.Resolution

/-!
# Solving typed equality constraints

Unification and constraint propagation for expressions with metavariables:

- `submit` checks both sides of an equality problem, records its source origin, and runs
  constraint propagation.
- `propagate` decomposes and solves ready problems, waking blocked problems when their
  metavariables are assigned.
- `settle` runs `primrec` congruence trials on remaining blocked problems after deterministic
  propagation finishes.

Typing, head unfolding, and closed definitional equality use Core operations through `Bridge`.
-/

public meta section
namespace LeanPRA.Surface.Metavariable
open Core hiding Term Predicate Proof Context

private def checked (result : CheckResult α) : M α :=
  match result with | .ok a => pure a | .error e => throw (.core e)

/-- Lift an `Except Failure` result into the solver monad `M`. -/
def liftResult (result : Except Failure α) : M α :=
  match result with | .ok a => pure a | .error e => throw e

private def dependenciesInScope (state : State) (allowed : List Nat) (fs ps : List Nat) : Bool :=
  fs.all (fun i => (state.terms[i]?.any fun u => u.locals.all allowed.contains)) &&
  ps.all (fun i => (state.predicates[i]?.any fun u => u.locals.all allowed.contains))

private def recordAssignment (unknown : UnknownId) : M Unit := do
  if let some id := (← get).currentProblem then
    modify fun s => { s with assignmentOrigins := s.assignmentOrigins.insert unknown id }

private def assignTerm (depth : Nat) (env : Environment) (ctx : Context) (locals : List Nat)
    (i : Nat) (value : Term) : M Bool := do
  let state ← get
  let some u := state.terms[i]? | return false
  let value ← liftResult (resolveTerm state locals depth value)
  if (termMetas value).contains i then throw (.invalid "cyclic implicit numerical argument")
  unless dependenciesInScope state u.locals (termMetas value) [] do return false
  let .ok captured := renameTerm locals u.locals 0 value | return false
  checked (Bridge.checkTerm (← get).projection depth env (context state ctx) value u.type)
  modify fun s => { s with
    terms := s.terms.modify i (fun u => { u with value := some captured })
    revision := s.revision + 1
    changed := .term i :: s.changed }
  recordAssignment (.term i)
  return true

private def assignPredicate (depth : Nat) (env : Environment) (ctx : Context) (locals : List Nat)
    (i : Nat) (value : Predicate) : M Bool := do
  let state ← get
  let some u := state.predicates[i]? | return false
  let value ← liftResult (resolvePredicate state locals depth value)
  let (fs, ps) := predicateMetas value
  if ps.contains i then throw (.invalid "cyclic implicit predicate argument")
  unless dependenciesInScope state u.locals fs ps do return false
  let .ok captured := renamePredicate locals u.locals 0 value | return false
  match Bridge.checkPredicate (← get).projection depth env (context state ctx) value u.type with
  | .ok _ => pure ()
  | .error e =>
    if !fs.isEmpty || !ps.isEmpty then return false
    throw (.core e)
  modify fun s => { s with
    predicates := (s.predicates.modify i
      (fun u => { u with value := some captured }))
    revision := s.revision + 1
    changed := .predicate i :: s.changed }
  recordAssignment (.predicate i)
  return true

private def termSpineAux (args : List Term) : Term → Term × List Term
  | .app f a => termSpineAux (a :: args) f
  | t => (t, args)

private def termSpine (t : Term) : Term × List Term := termSpineAux [] t

private def predSpineAux (args : List Term) : Predicate → Predicate × List Term
  | .app p a => predSpineAux (a :: args) p
  | p => (p, args)

private def predSpine (p : Predicate) : Predicate × List Term := predSpineAux [] p

private def pattern (allowed locals : List Nat) (args : List Term) : Option (List Nat) := do
  let indices ← args.mapM fun | .bvar i => some i | _ => none
  guard (indices.eraseDups.length == indices.length)
  for i in indices do
    let id ← locals[i]?
    guard (!allowed.contains id)
  return indices

private def formulaHead : Predicate → Option Nat
  | .false => some 0 | .true => some 1 | .equal .. => some 2
  | .imp .. => some 3 | .and .. => some 4 | .or .. => some 5
  | .all .. => some 6 | .ex .. => some 7 | .lam .. => some 8
  | _ => none

private def abstractVars (indices : List Nat) (i : Nat) : Term :=
  match indices.idxOf? i with
  | some j => .bvar (indices.length - 1 - j)
  | none => .bvar (i + indices.length)

private def tryCongruence (action : M Bool) : M Bool := do
  match action.run (← get) with
  | .ok (true, state) => set state; return true
  | .ok (false, _) => return false
  | .error message =>
    if message.isExhausted then throw message
    return false

-- Defer reporting an assignment error until unfolding has a chance to simplify the other side;
-- roll back state changes when the assignment does not succeed.
private def tryAssignment (action : M Bool) : M (Except Failure Bool) := do
  match action.run (← get) with
  | .ok (true, state) => set state; return .ok true
  | .ok (false, _) => return .ok false
  | .error error =>
    if error.isExhausted then throw error
    return .error error

private def rigidTermHead : Term → Bool
  | .bvar _ | .parameter _ | .succ => true
  | _ => false

private def comparePredicateDefinition (env : Environment)
    (compareTerm : Nat → Term → Term → M Bool)
    (comparePredicate : Nat → Predicate → Predicate → M Bool)
    (left right : Predicate) : M Bool := do
  let (head, args) := predSpine left
  let (head', args') := predSpine right
  if let .definition name fs ps := head then
    if let .definition name' gs qs := head' then
      if name == name' && fs.length == gs.length && ps.length == qs.length &&
          args.length == args'.length then
        let some (.predicate declaration) := env.lookup name
          | throw (.invalid "missing checked predicate definition")
        let revision := (← get).revision
        let solved ← tryCongruence do
          for ((a, b), k) in (fs.zip gs).zip (Parameter.functions declaration.parameters) do
            unless ← compareTerm k a b do return false
          for ((a, b), sig) in (ps.zip qs).zip (Parameter.predicates declaration.parameters) do
            unless ← comparePredicate sig.arity a b do return false
          for (a, b) in args.zip args' do
            unless ← compareTerm 0 a b do return false
          return true
        if solved then
          if (← get).revision != revision then
            modify fun s => { s with usedHeuristic := true }
          return true
  return false

-- Compare expressions before unfolding definitions. When both sides apply the same definition,
-- try matching their arguments first and roll back if that fails. Both inputs are already
-- well typed, and constructor decomposition and checked assignments preserve typing on subterms.
mutual
private def solveTerm : Nat → Nat → Environment → Context → List Nat → Nat → Term → Term → M Bool
  | 0, _, _, _, _, _, _, _ => throw (.exhausted "metavariable unification depth")
  | fuel + 1, depth, env, ctx, locals, arity, left, right => do
    let state ← get
    let left ← liftResult (resolveTerm state locals depth left)
    let right ← liftResult (resolveTerm state locals depth right)
    if left == right then return true
    if left.isComplete && right.isComplete then
      checked (Bridge.equalTerms state.projection depth env arity left right)
      return true
    let mut assignmentFailure := none
    if let .mvar i := left then
      match ← tryAssignment (assignTerm depth env ctx locals i right) with
      | .ok true => return true
      | .ok false => pure ()
      | .error error => assignmentFailure := some error
    if let .mvar i := right then
      match ← tryAssignment (assignTerm depth env ctx locals i left) with
      | .ok true => return true
      | .ok false => pure ()
      | .error error => assignmentFailure := some error
    let tryPattern (left right : Term) : M Bool := do
      let (.mvar i, args) := termSpine left | return false
      let some u := (← get).terms[i]? | return false
      let some indices := pattern u.locals locals args | return false
      let body := (← get).projection.substTerm right (abstractVars indices)
      let value := indices.foldr (fun _ b => Term.lam .anonymous b) body
      assignTerm depth env ctx locals i value
    if ← tryCongruence (tryPattern left right) then return true
    if ← tryCongruence (tryPattern right left) then return true
    let (head, args) := termSpine left
    let (head', args') := termSpine right
    if head == head' && rigidTermHead head && args.length == args'.length then
      let mut solved := true
      for (a, b) in args.zip args' do
        let argumentSolved ← solveTerm fuel depth env ctx locals 0 a b
        solved := solved && argumentSolved
      return solved
    if rigidTermHead head && rigidTermHead head' && head != head' then
      throw (.invalid "terms are not definitionally equal")
    if let .definition name fs := head then
      if let .definition name' gs := head' then
        if name == name' && fs.length == gs.length && args.length == args'.length then
          let some (.function declaration) := env.lookup name
            | throw (.invalid "missing checked function definition")
          let revision := (← get).revision
          let solved ← tryCongruence do
            for ((a, b), k) in (fs.zip gs).zip declaration.functions do
              unless ← solveTerm fuel depth env ctx locals k a b do return false
            for (a, b) in args.zip args' do
              unless ← solveTerm fuel depth env ctx locals 0 a b do return false
            return true
          if solved then
            if (← get).revision != revision then
              modify fun s => { s with usedHeuristic := true }
            return true
    if let .primrec base step := head then
      if let .primrec base' step' := head' then
        if args.length == args'.length && (← get).allowHeuristics then
          let revision := (← get).revision
          let solved ← tryCongruence do
            unless ← solveTerm fuel depth env ctx locals 0 base base' do return false
            unless ← solveTerm fuel depth env ctx locals 2 step step' do return false
            for (a, b) in args.zip args' do
              unless ← solveTerm fuel depth env ctx locals 0 a b do return false
            return true
          if solved then
            if (← get).revision != revision then
              modify fun s => { s with usedHeuristic := true }
            return true
    if arity > 0 then
      match left, right with
      | .lam _ a, .lam _ b =>
        let id ← freshLocal
        return ← solveTerm fuel depth env (ctx.pushLocal 0) (id :: locals) (arity - 1) a b
      | .lam _ a, b =>
        let id ← freshLocal
        let b := .app ((← get).projection.shiftTerm b) (.bvar 0)
        return ← solveTerm fuel depth env (ctx.pushLocal 0) (id :: locals) (arity - 1) a b
      | a, .lam _ b =>
        let id ← freshLocal
        let a := .app ((← get).projection.shiftTerm a) (.bvar 0)
        return ← solveTerm fuel depth env (ctx.pushLocal 0) (id :: locals) (arity - 1) a b
      | _, _ => pure ()
    -- Unfold one head step on the left and retry before unfolding the right side.
    let exposed ← checked (Bridge.exposeTerm (← get).projection depth env left)
    if exposed != left then
      return ← solveTerm fuel depth env ctx locals arity exposed right
    let exposed ← checked (Bridge.exposeTerm (← get).projection depth env right)
    if exposed != right then
      return ← solveTerm fuel depth env ctx locals arity left exposed
    if let some error := assignmentFailure then throw error
    match left, right with
    | .primrec base step, .primrec base' step' =>
      let state ← get
      if !(termMetas left ++ termMetas right).isEmpty then
        unless state.allowHeuristics do return false
        let solved ← tryCongruence do
          let baseSolved ← solveTerm fuel depth env ctx locals 0 base base'
          let stepSolved ← solveTerm fuel depth env ctx locals 2 step step'
          return baseSolved && stepSolved
        if solved then modify fun s => { s with usedHeuristic := true }
        return solved
    | _, _ => pure ()
    return false

private def solvePredicate : Nat → Nat → Environment → Context → List Nat → Nat →
    Predicate → Predicate → M Bool
  | 0, _, _, _, _, _, _, _ => throw (.exhausted "metavariable unification depth")
  | fuel + 1, depth, env, ctx, locals, arity, left, right => do
    let state ← get
    let left ← liftResult (resolvePredicate state locals depth left)
    let right ← liftResult (resolvePredicate state locals depth right)
    if left == right then return true
    if left.isComplete && right.isComplete then
      checked (Bridge.equalPredicates state.projection depth env arity left right)
      return true
    let mut assignmentFailure := none
    if let .mvar i := left then
      match ← tryAssignment (assignPredicate depth env ctx locals i right) with
      | .ok true => return true
      | .ok false => pure ()
      | .error error => assignmentFailure := some error
    if let .mvar i := right then
      match ← tryAssignment (assignPredicate depth env ctx locals i left) with
      | .ok true => return true
      | .ok false => pure ()
      | .error error => assignmentFailure := some error
    let tryPattern (left right : Predicate) : M Bool := do
      let (.mvar i, args) := predSpine left | return false
      let some u := (← get).predicates[i]? | return false
      let some indices := pattern u.locals locals args | return false
      let body := (← get).projection.substPredicate right (abstractVars indices)
      let value := indices.foldr (fun _ b => Predicate.lam .anonymous b) body
      assignPredicate depth env ctx locals i value
    if ← tryCongruence (tryPattern left right) then return true
    if ← tryCongruence (tryPattern right left) then return true
    let (head, args) := predSpine left
    let (head', args') := predSpine right
    if let .parameter _ := head then
      if head == head' && args.length == args'.length then
        let mut solved := true
        for (a, b) in args.zip args' do
          let argumentSolved ← solveTerm fuel depth env ctx locals 0 a b
          solved := solved && argumentSolved
        return solved
    if let .parameter _ := head then
      if let .parameter _ := head' then
        if head != head' then throw (.invalid "predicates are not definitionally equal")
    if ← comparePredicateDefinition env (solveTerm fuel depth env ctx locals)
        (solvePredicate fuel depth env ctx locals) left right then return true
    let recur := solvePredicate fuel depth env ctx locals 0
    match left, right with
    | .lam _ a, .lam _ b =>
      let id ← freshLocal
      return ← solvePredicate fuel depth env (ctx.pushLocal 0) (id :: locals) (arity - 1) a b
    | .lam _ a, b =>
      let id ← freshLocal
      let b := .app ((← get).projection.shiftPredicate b) (.bvar 0)
      return ← solvePredicate fuel depth env (ctx.pushLocal 0) (id :: locals) (arity - 1) a b
    | a, .lam _ b =>
      let id ← freshLocal
      let a := .app ((← get).projection.shiftPredicate a) (.bvar 0)
      return ← solvePredicate fuel depth env (ctx.pushLocal 0) (id :: locals) (arity - 1) a b
    | .all a, .all b | .ex a, .ex b =>
      return ← solvePredicate fuel depth env ctx locals 1 a b
    | .imp a b, .imp c d | .and a b, .and c d | .or a b, .or c d =>
      let first ← recur a c
      let second ← recur b d
      return first && second
    | .equal a b, .equal c d =>
      let first ← solveTerm fuel depth env ctx locals 0 a c
      let second ← solveTerm fuel depth env ctx locals 0 b d
      return first && second
    | _, _ => pure ()
    let exposed ← checked (Bridge.exposePredicate (← get).projection depth env left)
    if exposed != left then
      return ← solvePredicate fuel depth env ctx locals arity exposed right
    let exposed ← checked (Bridge.exposePredicate (← get).projection depth env right)
    if exposed != right then
      return ← solvePredicate fuel depth env ctx locals arity left exposed
    if let some error := assignmentFailure then throw error
    if let some a := formulaHead left then
      if let some b := formulaHead right then
        if a != b then throw (.invalid "incompatible formula shapes")
    return false

end

/-- Unassigned numerical metavariables occurring in `t`. -/
def termDependencies (state : State) (t : Term) : List UnknownId :=
  (termMetas t).filterMap fun i =>
    if (state.terms[i]?.any (·.value.isNone))
    then some (UnknownId.term i) else none

/-- Unassigned numerical and predicate metavariables occurring in `p`. -/
def predicateDependencies (state : State) (p : Predicate) : List UnknownId :=
  let (fs, ps) := predicateMetas p
  ((fs.filterMap fun i =>
    if (state.terms[i]?.any (·.value.isNone))
    then some (UnknownId.term i) else none) ++
   (ps.filterMap fun i =>
    if (state.predicates[i]?.any (·.value.isNone))
    then some (UnknownId.predicate i) else none)).eraseDups

/-- Whether `UnknownId` refers to an allocated metavariable in `state`. -/
def allocated (state : State) : UnknownId → Bool
  | .term i => i < state.terms.size
  | .predicate i => i < state.predicates.size

/-- Whether `UnknownId` has been assigned a value in `state`. -/
def assigned (state : State) : UnknownId → Bool
  | .term i => state.terms[i]?.any (·.value.isSome)
  | .predicate i => state.predicates[i]?.any (·.value.isSome)

private def constraintDependencies (depth : Nat) (state : State) : Constraint → Except Failure
    (List UnknownId)
  | .term _ locals _ a b => do
    return (termDependencies state (← resolveTerm state locals depth a) ++
      termDependencies state (← resolveTerm state locals depth b)).eraseDups
  | .predicate _ locals _ a b => do
    return (predicateDependencies state (← resolvePredicate state locals depth a) ++
      predicateDependencies state (← resolvePredicate state locals depth b)).eraseDups

private def constraintUnknowns (state : State) : Constraint → List UnknownId
  | .term _ _ _ a b =>
    ((termMetas a ++ termMetas b).map UnknownId.term).filter (allocated state)
  | .predicate _ _ _ a b =>
    let (af, ap) := predicateMetas a
    let (bf, bp) := predicateMetas b
    ((af ++ bf).map UnknownId.term ++ (ap ++ bp).map UnknownId.predicate).filter (allocated state)

private def enqueue (constraint : Constraint) (origin : Origin) (parent : Option Nat := none) :
    M Nat := do
  let id := (← get).problems.size
  modify fun s => { s with
    problems := s.problems.push { constraint, origin, parent }
    awake := s.awake.push id }
  return id

private def setProgress (id : Nat) (progress : Progress) : M Unit :=
  modify fun s => { s with problems := (s.problems.modify id
    (fun p => { p with progress, heuristic := s.usedHeuristic })) }

-- Split matching logical connectives into child constraints; leave metavariable or matching
-- parameter heads to `solvePredicate` before unfolding definitions.
private def predicateChildren (ctx : Context) (locals : List Nat) :
    Predicate → Predicate → Option (List Constraint)
  | .equal a b, .equal c d => some [.term ctx locals 0 a c, .term ctx locals 0 b d]
  | .imp a b, .imp c d | .and a b, .and c d | .or a b, .or c d =>
    some [.predicate ctx locals 0 a c, .predicate ctx locals 0 b d]
  | .all a, .all b | .ex a, .ex b => some [.predicate ctx locals 1 a b]
  | _, _ => none

private def decompose (depth : Nat) (env : Environment) (c : Constraint) :
    M (Option (List Constraint)) :=
  match depth, c with
  | 0, _ => throw (.exhausted "predicate head exposure depth")
  | fuel + 1, .predicate ctx locals 0 a b => do
    let state ← get
    let a ← liftResult (resolvePredicate state locals depth a)
    let b ← liftResult (resolvePredicate state locals depth b)
    if a == b then return some []
    if let some children := predicateChildren ctx locals a b then return some children
    let (head, _) := predSpine a
    let (head', _) := predSpine b
    match head, head' with
    | .mvar _, _ | _, .mvar _ => return none
    | .definition n .., .definition m .. =>
      if n == m then
        if ← comparePredicateDefinition env (solveTerm depth depth env ctx locals)
            (solvePredicate depth depth env ctx locals) a b then return some []
    | .parameter i, .parameter j => if i == j then return none
    | _, _ => pure ()
    let exposed ← checked (Bridge.exposePredicate state.projection depth env a)
    if exposed != a then
      return ← decompose fuel env (.predicate ctx locals 0 exposed b)
    let exposed' ← checked (Bridge.exposePredicate state.projection depth env b)
    if exposed' != b then
      return ← decompose fuel env (.predicate ctx locals 0 a exposed')
    return none
  | _, _ => pure none

private def wakeChanged : M Unit := do
  let state ← get
  let ids := (state.changed.flatMap fun u => state.waiting[u]?.getD []).eraseDups
  modify fun s => { s with changed := [] }
  for id in ids do
    if let some problem := (← get).problems[id]? then
      if let .blocked _ := problem.progress then
        setProgress id .ready
        modify fun s => { s with awake := s.awake.push id }

/-- Solve ready problems in the queue and wake blocked problems whose metavariables were assigned.
Failed problems are recorded as `.conflict` so independent problems can still run. -/
def propagate (depth : Nat) (env : Environment) : M Unit := do
  let mut budget := depth * ((← get).problems.size + 1)
  wakeChanged
  while (← get).awakeCursor < (← get).awake.size do
    if budget == 0 then throw (.exhausted "metavariable solving work limit")
    budget := budget - 1
    let state ← get
    let id := state.awake[state.awakeCursor]!
    modify fun s => { s with awakeCursor := s.awakeCursor + 1 }
    let some problem := (← get).problems[id]? | continue
    if let .ready := problem.progress then
      let state ← get
      let causes := (problem.causes ++ (constraintUnknowns state problem.constraint).filterMap
        (state.assignmentOrigins[·]?)).filter (· != id) |>.eraseDups
      modify fun s => { s with problems := s.problems.modify id (fun p => { p with causes }) }
      let before ← get
      let action : M Progress := do
        modify fun s => { s with currentProblem := some id }
        if let some children ← decompose depth env problem.constraint then
          return .decomposed (← children.mapM fun c => enqueue c problem.origin (some id))
        let solved ← match problem.constraint with
          | .term ctx locals k a b => solveTerm depth depth env ctx locals k a b
          | .predicate ctx locals k a b => solvePredicate depth depth env ctx locals k a b
        if solved then return .solved
        let deps ← liftResult (constraintDependencies depth (← get) problem.constraint)
        if deps.isEmpty then return .conflict (.unsupported
          "this equation needs an explicit argument or annotation")
        return .blocked deps
      match action.run before with
      | .ok (progress, state) =>
        set { state with currentProblem := none }
        setProgress id progress
        if let .blocked deps := progress then
          for dep in deps do
            modify fun s => { s with waiting := (s.waiting.insert dep
              (id :: s.waiting[dep]?.getD [])) }
      | .error error =>
        set before
        setProgress id (.conflict error)
      wakeChanged
  modify fun s => { s with awake := #[], awakeCursor := 0 }

/-- Check that both sides of `c` are well typed in `ctx` before solving `c`. -/
private def validate (depth : Nat) (env : Environment) (c : Constraint) : M Unit := do
  let state ← get
  match c with
  | .term ctx locals k a b =>
    let a ← liftResult (resolveTerm state locals depth a)
    let b ← liftResult (resolveTerm state locals depth b)
    checked (Bridge.checkTerm state.projection depth env (context state ctx) a k)
    checked (Bridge.checkTerm state.projection depth env (context state ctx) b k)
  | .predicate ctx locals k a b =>
    let a ← liftResult (resolvePredicate state locals depth a)
    let b ← liftResult (resolvePredicate state locals depth b)
    checked (Bridge.checkPredicate state.projection depth env (context state ctx) a ⟨k, .prop⟩)
    checked (Bridge.checkPredicate state.projection depth env (context state ctx) b ⟨k, .prop⟩)

/-- Enqueue `constraint`, check its types, and run `propagate`, returning the new problem ID. -/
def submit (depth : Nat) (env : Environment) (constraint : Constraint)
    (origin : Origin := {}) : M Nat := do
  let id ← enqueue constraint origin
  match (validate depth env constraint).run (← get) with
  | .ok (_, state) => set state
  | .error error => setProgress id (.conflict error)
  propagate depth env
  return id

/-- All problems in `state` that failed with `.conflict`, in submission order. -/
def conflicts (state : State) : List (Nat × Problem × Failure) :=
  state.problems.toList.zipIdx.filterMap fun (p, id) => match p.progress with
    | .conflict error => some (id, p, error)
    | _ => none

/-- Follow `parent` links from `id` to the original submitted problem ID. -/
def rootProblemId (state : State) (id : Nat) : Option Nat := Id.run do
  let mut current := id
  for _ in [:state.problems.size] do
    let some p := state.problems[current]? | return none
    match p.parent with
    | none => return some current
    | some parent => current := parent
  return none

/-- Look up the original submitted `Problem` for `id`. -/
def rootProblem (state : State) (id : Nat) : Option Problem := do
  state.problems[← rootProblemId state id]?

/-- Original problem IDs whose assignments or parent problems contributed to problem `id`. -/
def contributingProblems (state : State) (id : Nat) : List Nat := Id.run do
  let mut pending := [id]
  let mut seen := []
  let mut roots := []
  for _ in [:state.problems.size] do
    let some current := pending.head? | break
    pending := pending.tail
    if seen.contains current then continue
    seen := current :: seen
    let some p := state.problems[current]? | continue
    if let some root := rootProblemId state current then roots := root :: roots
    pending := p.causes ++ p.parent.toList ++ pending
  return roots.reverse.eraseDups

/-- Run `propagate`, and if no conflicts exist, retry blocked problems with `primrec` congruence
enabled. -/
def settle (depth : Nat) (env : Environment) : M Unit := do
  propagate depth env
  if !(conflicts (← get)).isEmpty then return
  modify fun s => { s with allowHeuristics := true }
  for (p, id) in (← get).problems.toList.zipIdx do
    if let .blocked _ := p.progress then
      setProgress id .ready
      modify fun s => { s with awake := s.awake.push id }
  propagate depth env
  modify fun s => { s with allowHeuristics := false }

/-- Run `settle` and throw the first conflict if any problem failed. -/
def solve (depth : Nat) (env : Environment) : M Unit := do
  settle depth env
  if let (_, _, error) :: _ := conflicts (← get) then throw error

/-- Submit `obligation` and throw the first conflict if any problem failed. -/
def constrain (depth : Nat) (env : Environment) (obligation : Constraint) : M Unit := do
  let _ ← submit depth env obligation
  if let (_, _, error) :: _ := conflicts (← get) then throw error

/-- Run `solve` and verify that no unassigned metavariables or blocked problems remain. -/
def finish (depth : Nat) (env : Environment) : M Unit := do
  solve depth env
  let state ← get
  if hasUnassigned state then
    throw (.incomplete "unresolved metavariable; supply an explicit argument")
  for p in state.problems do
    if let .blocked _ := p.progress then
      throw (.unsupported "metavariable constraints remain blocked; supply an explicit argument")

end LeanPRA.Surface.Metavariable
