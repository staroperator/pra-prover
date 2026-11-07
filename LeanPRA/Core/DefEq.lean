module

public import LeanPRA.Core.Reduction

/-!
# Structural definitional equality

- `defEqTerm` compares numerical terms at their common arity.
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

namespace LeanPRA.Core

/-- Compare two argument lists against their common list of types. Mismatched lengths fail. -/
@[expose]
public def compareArguments (compare : α → β → β → CheckResult Bool) :
    List α → List β → List β → CheckResult Bool
  | [], [], [] => pure true
  | k :: ks, a :: as, b :: bs => do
    if ← compare k a b then compareArguments compare ks as bs else pure false
  | _, _, _ => pure false

/-- Compute beta, let, and zero-recursion steps at a term head. Return a new term when a step
occurs or `changed` is true, and `none` otherwise. Each recursive call consumes depth. -/
@[expose]
public def exposeTerm : Nat → Bool → Term → CheckResult (Option Term)
  | 0, _, _ => exhausted
  | depth + 1, changed, expression => do
    match expression with
    | .letE _ value body => exposeTerm depth true (body.subst0 value)
    | .primrec base _ .zero => exposeTerm depth true base
    | .app function argument =>
      let computed ← exposeTerm depth false function
      match computed.getD function with
      | .lam _ body => exposeTerm depth true (body.subst0 argument)
      | _ =>
        match computed with
        | some f => pure (some (.app f argument))
        | none => pure (if changed then some expression else none)
    | _ => pure (if changed then some expression else none)

/-- Unfold a named function at the head of an application, preserving its arguments.
Return `none` when the head has no named definition. -/
@[expose]
public def unfoldTermHead (environment : Environment) : Term → CheckResult (Option Term)
  | .definition name functions =>
    match environment.lookup name with
    | some (.function d) => pure (some (d.body.instantiate functions))
    | _ => referenceError environment name .function
  | .app function argument =>
    (unfoldTermHead environment function).map (·.map (fun f => .app f argument))
  | _ => pure none

/-- Reduce a recursor argument to weak-head form and take its zero or successor step if possible.
Return `none` when the input is unchanged. -/
@[expose]
public def exposeRecursor (depth : Nat) (environment : Environment) :
    Term → CheckResult (Option Term)
  | .primrec base step argument => do
    let value ← whnfTerm depth environment argument
    match value with
    | .zero => exposeTerm depth true base
    | .app .succ predecessor =>
      exposeTerm depth true (.app (.app step predecessor) (.primrec base step predecessor))
    | _ => pure (if value == argument then none else some (.primrec base step value))
  | _ => pure none

mutual

/-- Compare terms of the supplied arity in a common well-formed context and checked environment.
Structural comparison requests unfolding and head computation as needed. -/
@[expose]
public def defEqTerm : Nat → Environment → Arity → Term → Term → CheckResult Bool
  | 0, _, _, _, _ => exhausted
  | depth + 1, environment, arity, left, right => do
    if left == right then return true
    match left, right with
    | .bvar i, .bvar j | .parameter i, .parameter j => return i == j
    | .lam _ a, .lam _ b =>
      match arity with
      | k + 1 => return ← defEqTerm depth environment k a b
      | 0 => return false
    | .primrec a _ .zero, .primrec b _ .zero => return ← defEqTerm depth environment 0 a b
    | _, _ => pure ()
    let structural : CheckResult Bool := do
      match left, right with
      | .app f a, .app g b =>
        if ← compareTermApplications depth environment (arity + 1) f g then
          defEqTerm depth environment 0 a b
        else pure false
      | .primrec a s n, .primrec b t m =>
        if ← defEqTerm depth environment 0 a b then
          if ← defEqTerm depth environment 2 s t then defEqTerm depth environment 0 n m
          else pure false
        else pure false
      | .definition f as, .definition g bs =>
        if f != g then return false
        match environment.lookup f with
        | some (.function d) => compareArguments (defEqTerm depth environment) d.functions as bs
        | _ => referenceError environment f .function
      | _, _ => pure false
    if let .ok true := structural then return true
    match arity with
    | k + 1 =>
      defEqTerm depth environment k (.app left.shift (.bvar 0)) (.app right.shift (.bvar 0))
    | 0 =>
      let a ← exposeTerm (depth + 1) false left
      let b ← exposeTerm (depth + 1) false right
      if a.isSome || b.isSome then
        return ← defEqTerm depth environment 0 (a.getD left) (b.getD right)
      let a ← unfoldTermHead environment left
      let b ← unfoldTermHead environment right
      if a.isSome || b.isSome then
        return ← defEqTerm depth environment 0 (a.getD left) (b.getD right)
      match left, right with
      | .primrec .., .primrec .. =>
        let a ← exposeRecursor (depth + 1) environment left
        let b ← exposeRecursor (depth + 1) environment right
        match a, b with
        | none, none => structural
        | _, _ => defEqTerm depth environment 0 (a.getD left) (b.getD right)
      | .primrec .., _ =>
        let value ← whnfTerm (depth + 1) environment left
        if value == left then return ← structural
        defEqTerm depth environment 0 value right
      | _, .primrec .. =>
        let value ← whnfTerm (depth + 1) environment right
        if value == right then return ← structural
        defEqTerm depth environment 0 left value
      | _, _ => structural

/-- Compare application heads and their arguments at a common arity, keeping heads folded.
Inputs satisfy the typing assumptions of `defEqTerm`. Success establishes equality. Failure or
exhaustion can still require unfolding when a head computes or discards its arguments. -/
@[expose]
public def compareTermApplications : Nat → Environment → Arity → Term → Term → CheckResult Bool
  | 0, _, _, _, _ => exhausted
  | depth + 1, environment, arity, left, right => do
    if left == right then return true
    match left, right with
    | .bvar i, .bvar j | .parameter i, .parameter j => pure (i == j)
    | .app f a, .app g b =>
      if ← compareTermApplications depth environment (arity + 1) f g then
        defEqTerm depth environment 0 a b
      else pure false
    | .definition f as, .definition g bs =>
      if f != g then return false
      match environment.lookup f with
      | some (.function d) => compareArguments (defEqTerm depth environment) d.functions as bs
      | _ => referenceError environment f .function
    | _, _ => pure false

end

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
      let a ← unfoldPredicateHead environment left
      let b ← unfoldPredicateHead environment right
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
end LeanPRA.Core
