module

public import PRAProver.Core.Reduction
import Std.Data.HashMap.Basic
import Std.Sync.Mutex

/-!
# Structural definitional equality

- `defEqTerm` compares numerical terms at their common arity.
- `termConversion` records the reductions and congruence steps of a successful term comparison.
- `defEqPredicate` compares predicates at their common arity.
- `compareTermApplications` and `comparePredicateApplications` match application heads and compare
  their arguments. Success establishes equality; an unsuccessful trial can still require unfolding.

Comparison follows the available syntax first, including lambda bodies and recursor components.
Definitions unfold when their arguments fail to establish equality. Beta redexes, lets, and zero
recursors compute together until another definition, recursor, or rigid head becomes available.
Two unresolved recursors expose their next comparable structure; a recursor facing a rigid
numerical head computes to weak-head form. Function extensionality handles remaining comparisons
at positive arity.

Inputs must already be well typed in a common context and a checked environment. Each recursive
comparison consumes depth. Exhaustion means that comparison is unfinished. A tentative comparison
of arguments may exhaust its depth and still allow a definition or recursor to discard them.
-/

namespace PRAProver.Core

/-- Compare two argument lists against their common list of types. Mismatched lengths fail. -/
@[expose]
public def compareArguments (compare : α → β → β → CheckResult Bool) :
    List α → List β → List β → CheckResult Bool
  | [], [], [] => pure true
  | k :: ks, a :: as, b :: bs => do
    if ← compare k a b then compareArguments compare ks as bs else pure false
  | _, _, _ => pure false

private abbrev WeightM := StateM (Std.HashMap Lean.Name Nat)

mutual

private partial def termWeight (env : Environment) (depth : Nat) : Term → WeightM Nat
  | .definition name args => do
    args.foldlM (fun w arg => return max w (← termWeight env depth arg))
      (← definitionWeight env depth name)
  | .app a b | .letE _ a b | .primrec a b =>
    return max (← termWeight env depth a) (← termWeight env depth b)
  | .lam _ b => termWeight env depth b
  | _ => pure 0

private partial def predicateWeight (env : Environment) (depth : Nat) : Predicate → WeightM Nat
  | .definition name fs ps => do
    let w ← fs.foldlM (fun w arg => return max w (← termWeight env depth arg))
      (← definitionWeight env depth name)
    ps.foldlM (fun w arg => return max w (← predicateWeight env depth arg)) w
  | .equal a b => return max (← termWeight env depth a) (← termWeight env depth b)
  | .app p a | .letTerm _ a p =>
    return max (← predicateWeight env depth p) (← termWeight env depth a)
  | .imp a b | .and a b | .or a b | .letPredicate _ a b =>
    return max (← predicateWeight env depth a) (← predicateWeight env depth b)
  | .all p | .ex p | .lam _ p => predicateWeight env depth p
  | _ => pure 0

private partial def definitionWeight (env : Environment) (depth : Nat)
    (name : Lean.Name) : WeightM Nat := do
  if let some w := (← get)[name]? then
    if w < depth then return w
  let depth + 1 := depth | return 0
  let w ← match env.lookup name with
    | some (.function d) => (· + 1) <$> termWeight env depth d.body
    | some (.predicate d) => (· + 1) <$> predicateWeight env depth d.body
    | _ => pure 0
  -- A walk that reaches its depth bound cannot supply a weight for a later walk.
  if w ≤ depth then modify (·.insert name w)
  return w

end

@[expose] public def termHeadName : Term → Option Lean.Name
  | .definition name _ => some name
  | .app f _ => termHeadName f
  | _ => none

@[expose] public def predicateHeadName : Predicate → Option Lean.Name
  | .definition name .. => some name
  | .app f _ => predicateHeadName f
  | _ => none

private def computeWeightOrder (env : Environment) (a b : Lean.Name) : WeightM Ordering := do
  if a == b then return .eq
  -- A chain through every declaration still has one spare step at its last definition.
  let depth := env.size + 1
  let wa ← definitionWeight env depth a
  let wb ← definitionWeight env depth b
  return compare wa wb

private initialize weightCache : Std.Mutex (Option (Environment ×
    Std.HashMap Lean.Name Nat)) ← Std.Mutex.new none

private unsafe def memoWeightOrder (env : Environment) (a b : Lean.Name) : Ordering :=
  if a == b then .eq else unsafeBaseIO do
    weightCache.atomically (m := BaseIO) do
      let cache := match ← get with
        | some (saved, cache) => if ptrEq saved env then cache else {}
        | none => {}
      let (order, cache) := (computeWeightOrder env a b).run cache
      -- Keep the environment itself in the cache so its address cannot be reused.
      set (some (env, cache))
      return order

/-- Choose the unfolding order for two names in the same declaration environment. -/
@[implemented_by memoWeightOrder]
public def namedWeightOrder (env : Environment) (a b : Lean.Name) : Ordering :=
  (computeWeightOrder env a b).run' {}

/-- Compare the weights of two named heads. Each weight is one more than the highest weight
of a definition referenced in its body. Other heads and identical names need no weight lookup. -/
@[expose] public def compareHeadWeights (env : Environment) :
    Option Lean.Name → Option Lean.Name → Ordering
  | some a, some b => namedWeightOrder env a b
  | _, _ => .eq

/-- Run one head unfolding on the heavier side, or on both sides when their weights agree. -/
@[expose] public def unfoldByWeight (order : Ordering) (openHead : α → CheckResult (Option β))
    (a b : α) : CheckResult (Option β × Option β) := do
  match order with
  | .gt => return (← openHead a, none)
  | .lt => return (none, ← openHead b)
  | .eq => return (← openHead a, ← openHead b)

@[expose] public def termUnfoldingOrder (env : Environment) (a b : Term) : Ordering :=
  compareHeadWeights env (termHeadName a) (termHeadName b)

@[expose] public def predicateUnfoldingOrder (env : Environment) (a b : Predicate) : Ordering :=
  compareHeadWeights env (predicateHeadName a) (predicateHeadName b)

/-- Add earlier contractions to a reduction that changed its input. -/
public abbrev Reduced.beforeChange : (record : Bool) → (Unit → HeadReduction) →
    CheckResult (Option (Reduced record)) → CheckResult (Option (Reduced record))
  | false, _, result => result
  | true, first, result => result.map (Option.map fun (t, h) => (t, (first ()).append h))

/-- Compute beta, let, and zero-recursion steps at a term head. -/
@[expose] public def exposeTerm (depth : Nat) (changed : Bool) (expression : Term)
    (record : Bool := false) : CheckResult (Option (Reduced record)) := match depth with
  | 0 => exhausted
  | depth + 1 => do
    let next := fun t => exposeTerm depth true t record
    let before := Reduced.beforeChange record
    match expression with
    | .letE _ value body => before (fun _ => .letTerm) (next (body.subst0 value))
    | .app (.primrec base _) .zero => before (fun _ => .recZero) (next base)
    | .app function argument =>
      let computed ← exposeTerm depth false function record
      let fn := computed.getD (Reduced.done record function)
      before (fun _ => (Reduced.steps record fn).lift .function) <|
        match Reduced.term record fn with
        | .lam _ body => before (fun _ => .beta) (next (body.subst0 argument))
        | _ =>
          match computed with
          | some f => pure (some (Reduced.done record (.app (Reduced.term record f) argument)))
          | none => pure (if changed then some (Reduced.done record expression) else none)
    | _ => pure (if changed then some (Reduced.done record expression) else none)

public abbrev Reduced.applyTo (argument : Term) : (record : Bool) →
    Reduced record → Reduced record
  | false, f => .app f argument
  | true, (f, h) => (.app f argument, h.lift .function)

/-- Unfold one named head while preserving its application spine. -/
@[expose] public def unfoldTermHead (environment : Environment) (t : Term)
    (record : Bool := false) : CheckResult (Option (Reduced record)) := match t with
  | .definition name functions =>
    match environment.lookup name with
    | some (.function d) => Reduced.beforeChange record (fun _ => .unfold)
        (pure (some (Reduced.done record (d.body.instantiate functions))))
    | _ => referenceError environment name .function
  | .app function argument =>
    (unfoldTermHead environment function record).map (·.map (Reduced.applyTo argument record))
  | _ => pure none

/-- Expose a recursion counter and take its defining equation when the counter permits it. -/
@[expose] public def exposeRecursor (depth : Nat) (environment : Environment) (t : Term)
    (record : Bool := false) : CheckResult (Option (Reduced record)) := match t with
  | .app (.primrec base step) argument => do
    let arg ← whnfTerm depth environment argument record
    let value := Reduced.term record arg
    let before := Reduced.beforeChange record
    before (fun _ => (Reduced.steps record arg).lift .counter) <| do
      match value with
      | .zero => before (fun _ => .recZero) (exposeTerm depth true base record)
      | .app .succ i =>
        before (fun _ => .recSucc)
          (exposeTerm depth true (.app (.app step i) (.app (.primrec base step) i)) record)
      | _ => pure (if value == argument then none else
          some (Reduced.done record (.app (.primrec base step) value)))
  | _ => pure none

/-- The successful comparisons used to establish numerical definitional equality.
A reduction records the new endpoints. A pair records comparisons of corresponding children. -/
public inductive TermConversion where
  | same
  | pair (left right : TermConversion)
  | reduce (left right : Term) (leftSteps rightSteps : HeadReduction) (rest : TermConversion)
  | lambda (body : TermConversion)
  | eta (body : TermConversion)
  deriving Inhabited

namespace TermComparison

/-- Recording keeps the successful comparison. Ordinary checking needs only its verdict. -/
public abbrev Answer : Bool → Type
  | false => Bool
  | true => Option TermConversion

@[expose] public def answer : (record : Bool) → Bool → Answer record
  | false, b => b
  | true, b => if b then some .same else none

@[expose] public def onMismatch : (record : Bool) → CheckResult (Answer record) →
    (Unit → CheckResult (Answer record)) → CheckResult (Answer record)
  | false => fun trial next => match trial with
    | .ok true => pure true
    | _ => next ()
  | true => fun trial next => match trial with
    | .ok (some p) => pure (some p)
    | _ => next ()

@[expose] public def mark : (record : Bool) → (TermConversion → TermConversion) →
    CheckResult (Answer record) → CheckResult (Answer record)
  | false, _, x => x
  | true, f, x => x.map (Option.map f)

@[expose] public def both : (record : Bool) → CheckResult (Answer record) →
    (Unit → CheckResult (Answer record)) → CheckResult (Answer record)
  | false, x, y => do if ← x then y () else pure false
  | true, x, y => do
    let some p ← x | return none
    mark true (.pair p) (y ())

@[expose] public def argumentPaths
    (compare : Arity → Term → Term → CheckResult (Option TermConversion)) :
    List Arity → List Term → List Term → CheckResult (Option TermConversion)
  | [], [], [] => pure (some .same)
  | k :: ks, a :: as, b :: bs =>
    both true (compare k a b) fun _ => argumentPaths compare ks as bs
  | _, _, _ => pure none

@[expose] public def arguments : (record : Bool) →
    (Arity → Term → Term → CheckResult (Answer record)) →
    List Arity → List Term → List Term → CheckResult (Answer record)
  | false => compareArguments
  | true => argumentPaths

/-- Compare the children of applications, recursors, and named definitions by congruence. -/
@[expose, specialize] public def compareChildren (record : Bool)
    (term head : Arity → Term → Term → CheckResult (Answer record)) (env : Environment)
    (arity : Arity) (left right : Term) : CheckResult (Answer record) := do
  match left, right with
  | .app f a, .app g b => both record (head (arity + 1) f g) fun _ => term 0 a b
  | .primrec a s, .primrec b t => both record (term 0 a b) fun _ => term 2 s t
  | .definition f as, .definition g bs =>
    if f != g then return answer record false
    match env.lookup f with
    | some (.function d) => arguments record term d.functions as bs
    | _ => referenceError env f .function
  | _, _ => return answer record false

mutual

/-- Compare terms at their common arity, unfolding when congruence is insufficient. -/
@[expose, specialize record] public def compareTerm (record : Bool) :
    Nat → Environment → Arity → Term → Term → CheckResult (Answer record)
  | 0, _, _, _, _ => exhausted
  | n + 1, env, arity, left, right => do
    let depth := n + 1
    let term := compareTerm record n env
    let head := compareHead record n env
    if left == right then return answer record true
    match left, right with
    | .bvar i, .bvar j | .parameter i, .parameter j => return answer record (i == j)
    | .lam _ a, .lam _ b =>
      match arity with
      | k + 1 => return ← mark record .lambda (term k a b)
      | 0 => return answer record false
    | .app (.primrec a _) .zero, .app (.primrec b _) .zero =>
      return ← mark record (.reduce a b .recZero .recZero) (term 0 a b)
    | _, _ => pure ()
    let structural := compareChildren record term head env arity left right
    onMismatch record structural fun _ => do
      match arity with
      | k + 1 => mark record .eta (term k (.app left.shift (.bvar 0)) (.app right.shift (.bvar 0)))
      | 0 =>
        let next := fun (a b : Reduced record) =>
          let x := Reduced.term record a
          let y := Reduced.term record b
          mark record (.reduce x y (Reduced.steps record a) (Reduced.steps record b)) (term 0 x y)
        let l := Reduced.done record left
        let r := Reduced.done record right
        let a ← exposeTerm depth false left record
        let b ← exposeTerm depth false right record
        if a.isSome || b.isSome then return ← next (a.getD l) (b.getD r)
        let (a, b) ← unfoldByWeight (termUnfoldingOrder env left right)
          (fun t => unfoldTermHead env t record) left right
        if a.isSome || b.isSome then return ← next (a.getD l) (b.getD r)
        match left, right with
        | .app (.primrec ..) _, .app (.primrec ..) _ =>
          let a ← exposeRecursor depth env left record
          let b ← exposeRecursor depth env right record
          if a.isSome || b.isSome then next (a.getD l) (b.getD r) else structural
        | .app (.primrec ..) _, _ =>
          let a ← whnfTerm depth env left record
          if Reduced.term record a == left then return ← structural
          next a r
        | _, .app (.primrec ..) _ =>
          let b ← whnfTerm depth env right record
          if Reduced.term record b == right then return ← structural
          next l b
        | _, _ => structural

/-- Compare application heads with their definitions folded. -/
@[expose, specialize record] public def compareHead (record : Bool) :
    Nat → Environment → Arity → Term → Term → CheckResult (Answer record)
  | 0, _, _, _, _ => exhausted
  | n + 1, env, arity, left, right => do
    let term := compareTerm record n env
    let head := compareHead record n env
    if left == right then return answer record true
    match left, right with
    | .bvar i, .bvar j | .parameter i, .parameter j => pure (answer record (i == j))
    | _, _ => compareChildren record term head env arity left right

end

end TermComparison

/-- Compare well-typed numerical terms at their common arity. -/
public abbrev defEqTerm := TermComparison.compareTerm false

/-- Compare folded application heads and their arguments. -/
public abbrev compareTermApplications := TermComparison.compareHead false

/-- Record the successful comparison of two numerical terms. -/
public abbrev termConversion := TermComparison.compareTerm true

/-- Record congruence at an application head. -/
public abbrev termApplicationConversion := TermComparison.compareHead true

/-- Compute beta and let steps at a predicate head. Return a new predicate when a step occurs
or `changed` is true, and `none` otherwise. Each recursive call consumes depth. -/
@[expose]
public def exposePredicate : Nat → Bool → Predicate → CheckResult (Option Predicate)
  | 0, _, _ => exhausted
  | depth + 1, changed, expression => do
    match expression with
    | .letTerm _ _ body | .letPredicate _ _ body => exposePredicate depth true body
    | .app function argument =>
      let computed ← exposePredicate depth false function
      match computed.getD function with
      | .lam _ body => exposePredicate depth true (body.subst0 argument)
      | _ =>
        match computed with
        | some f => pure (some (.app f argument))
        | none => pure (if changed then some expression else none)
    | _ => pure (if changed then some expression else none)

/-- Unfold a named predicate at the head of an application, preserving its numerical arguments.
Return `none` when the head has no named definition. -/
@[expose]
public def unfoldPredicateHead (environment : Environment) :
    Predicate → CheckResult (Option Predicate)
  | .definition name functions predicates =>
    match environment.lookup name with
    | some (.predicate d) => pure (some (d.body.instantiate functions predicates))
    | _ => referenceError environment name .predicate
  | .app function argument =>
    (unfoldPredicateHead environment function).map (·.map (fun f => .app f argument))
  | _ => pure none

mutual

/-- Compare predicates at a common arity in a well-formed context and checked environment.
Both inputs must be well typed at a common predicate signature, including any QF inclusion.
Matching logical constructors compare their components directly. -/
@[expose]
public def defEqPredicate : Nat → Environment → Arity → Predicate → Predicate → CheckResult Bool
  | 0, _, _, _, _ => exhausted
  | depth + 1, environment, arity, left, right => do
    if left == right then return true
    match left, right with
    | .parameter i, .parameter j => return i == j
    | .lam _ a, .lam _ b =>
      match arity with
      | k + 1 => return ← defEqPredicate depth environment k a b
      | 0 => return false
    | .equal a b, .equal c d =>
      if ← defEqTerm depth environment 0 a c then return ← defEqTerm depth environment 0 b d
      else return false
    | .imp a b, .imp c d | .and a b, .and c d | .or a b, .or c d =>
      if ← defEqPredicate depth environment 0 a c then
        return ← defEqPredicate depth environment 0 b d
      else return false
    | .all a, .all b | .ex a, .ex b => return ← defEqPredicate depth environment 1 a b
    | _, _ => pure ()
    let structural : CheckResult Bool := do
      match left, right with
      | .app f a, .app g b =>
        if ← comparePredicateApplications depth environment (arity + 1) f g then
          defEqTerm depth environment 0 a b
        else pure false
      | .definition f fs ps, .definition g gs qs =>
        if f != g then return false
        match environment.lookup f with
        | some (.predicate d) =>
          if ← compareArguments (defEqTerm depth environment) d.functions fs gs then
            compareArguments (fun s => defEqPredicate depth environment s.arity) d.predicates ps qs
          else pure false
        | _ => referenceError environment f .predicate
      | _, _ => pure false
    if let .ok true := structural then return true
    match arity with
    | k + 1 =>
      defEqPredicate depth environment k (.app left.shift (.bvar 0)) (.app right.shift (.bvar 0))
    | 0 =>
      let a ← exposePredicate (depth + 1) false left
      let b ← exposePredicate (depth + 1) false right
      if a.isSome || b.isSome then
        return ← defEqPredicate depth environment 0 (a.getD left) (b.getD right)
      let (a, b) ← unfoldByWeight (predicateUnfoldingOrder environment left right)
        (unfoldPredicateHead environment) left right
      match a, b with
      | none, none => structural
      | _, _ => defEqPredicate depth environment 0 (a.getD left) (b.getD right)

/-- Compare predicate application heads and their numerical arguments, keeping heads folded.
Inputs satisfy the typing assumptions of `defEqPredicate`. Success establishes equality. Failure
or exhaustion can still require unfolding a predicate that discards its arguments. -/
@[expose]
public def comparePredicateApplications : Nat → Environment → Arity → Predicate → Predicate →
    CheckResult Bool
  | 0, _, _, _, _ => exhausted
  | depth + 1, environment, arity, left, right => do
    if left == right then return true
    match left, right with
    | .parameter i, .parameter j => pure (i == j)
    | .app f a, .app g b =>
      if ← comparePredicateApplications depth environment (arity + 1) f g then
        defEqTerm depth environment 0 a b
      else pure false
    | .definition f fs ps, .definition g gs qs =>
      if f != g then return false
      match environment.lookup f with
      | some (.predicate d) =>
        if ← compareArguments (defEqTerm depth environment) d.functions fs gs then
          compareArguments (fun s => defEqPredicate depth environment s.arity) d.predicates ps qs
        else pure false
      | _ => referenceError environment f .predicate
    | _, _ => pure false

end
end PRAProver.Core
