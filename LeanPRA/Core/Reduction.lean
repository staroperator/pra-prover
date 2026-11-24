module

public import LeanPRA.Core.Utils
public import LeanPRA.Core.Substitution

/-!
# Normalization with a recursion depth limit

Normalization computes beta-long, eta-long normal forms for explicit reduction requests.
Definitional equality uses a separate structural comparison with weak-head computation.

- `reduceTerm` normalizes a term at a given arity.
- `reducePredicate` normalizes a predicate at a given arity.
- `reduceFormula` normalizes a formula (arity `0`).
- `whnfTerm` and `whnfPredicate` reduce to weak head normal form.
- `betaReduceTerm` and `betaReducePredicate` contract beta redexes for display,
  keeping definitions, lets, `primrec`, and binder names intact.

Normalization assumes well-typed inputs. Callers establish their types through
inference or checking before normalization. `maxDepth` bounds recursive call depth: reaching `0`
returns `exhausted` during normalization and leaves the expression unchanged during beta reduction.
-/

@[expose] public section

namespace LeanPRA.Core

/-- Head contractions, including the position of a reduction inside an application. -/
inductive HeadReduction where
  | refl
  | beta
  | letTerm
  | unfold
  | recZero
  | recSucc
  | function (steps : HeadReduction)
  | counter (steps : HeadReduction)
  | trans (first second : HeadReduction)
  deriving Inhabited, Repr

namespace HeadReduction

/-- Join successive contractions, dropping empty paths. -/
def append : HeadReduction → HeadReduction → HeadReduction
  | .refl, q => q
  | p, .refl => p
  | p, q => .trans p q

/-- Lift contractions through one enclosing operation. -/
def lift (atPosition : HeadReduction → HeadReduction) : HeadReduction → HeadReduction
  | .refl => .refl
  | p => atPosition p

end HeadReduction

abbrev Reduced : Bool → Type
  | false => Term
  | true => Term × HeadReduction

namespace Reduced

abbrev term : (record : Bool) → Reduced record → Term
  | false, t => t
  | true, r => r.1

abbrev done : (record : Bool) → Term → Reduced record
  | false, t => t
  | true, t => (t, .refl)

abbrev before : (record : Bool) → (Unit → HeadReduction) →
    CheckResult (Reduced record) → CheckResult (Reduced record)
  | false, _, x => x
  | true, step, x => x.map fun (t, h) => (t, (step ()).append h)

abbrev steps : (record : Bool) → Reduced record → HeadReduction
  | false, _ => .refl
  | true, r => r.2

end Reduced

/-- Reduce to weak head normal form, optionally recording the contractions in order. -/
@[specialize record] def whnfTerm (depth : Nat) (env : Environment) (expression : Term)
    (record : Bool := false) :
    CheckResult (Reduced record) := match depth with
  | 0 => exhausted
  | depth + 1 => do
    let again := fun t => whnfTerm depth env t record
    let before := Reduced.before record
    match expression with
    | .definition name functions =>
      match env.lookup name with
      | some (.function d) => before (fun _ => .unfold) (again (d.body.instantiate functions))
      | _ => referenceError env name .function
    | .letE _ value body => before (fun _ => .letTerm) (again (body.subst0 value))
    | .app f a =>
      let fn ← again f
      before (fun _ => (Reduced.steps record fn).lift .function) <| do
        let function := Reduced.term record fn
        match function with
        | .lam _ body => before (fun _ => .beta) (again (body.subst0 a))
        | .primrec base step =>
          let arg ← again a
          before (fun _ => (Reduced.steps record arg).lift .counter) <| do
            let argument := Reduced.term record arg
            match argument with
            | .zero => before (fun _ => .recZero) (again base)
            | .app .succ i =>
              before (fun _ => .recSucc)
                (again (.app (.app step i) (.app (.primrec base step) i)))
            | _ => pure (Reduced.done record (.app (.primrec base step) argument))
        | _ => pure (Reduced.done record (.app function a))
    | _ => pure (Reduced.done record expression)

mutual

/-- Normalize a checked term at `arity` by eta-expanding and beta-reducing. -/
def reduceTerm : Nat → Environment → Arity → Term → CheckResult Term
  | 0, _, _, _ => exhausted
  | maxDepth + 1, environment, arity, expression => do
    match arity with
    | k + 1 =>
      let body ← reduceTerm maxDepth environment k (.app (expression.shift) (.bvar 0))
      pure (.lam .anonymous body)
    | 0 =>
      let expression ← whnfTerm maxDepth environment expression
      match expression with
      | .zero => pure .zero
      | .bvar i => pure (.bvar i)
      | .parameter i => pure (.parameter i)
      | .app (.primrec base step) argument =>
        let base ← reduceTerm maxDepth environment 0 base
        let step ← reduceTerm maxDepth environment 2 step
        let argument ← reduceTerm maxDepth environment 0 argument
        pure (.app (.primrec base step) argument)
      | .app function argument =>
        let function ← reduceTermNeutral maxDepth environment function
        let argument ← reduceTerm maxDepth environment 0 argument
        pure (.app function argument)
      | _ => fail (.expectedForm .number (.term expression))

/-- Normalize the arguments of a neutral application spine without eta-expanding its head. -/
def reduceTermNeutral : Nat → Environment → Term → CheckResult Term
  | 0, _, _ => exhausted
  | maxDepth + 1, environment, expression => do
    let expression ← whnfTerm maxDepth environment expression
    match expression with
    | .bvar i => pure (.bvar i)
    | .parameter i => pure (.parameter i)
    | .succ => pure .succ
    | .app function argument =>
      let function ← reduceTermNeutral maxDepth environment function
      let argument ← reduceTerm maxDepth environment 0 argument
      pure (.app function argument)
    | _ => fail (.expectedForm .neutralTerm (.term expression))

end

mutual

/-- Reduce a checked predicate to weak head normal form. -/
def whnfPredicate : Nat → Environment → Predicate → CheckResult Predicate
  | 0, _, _ => exhausted
  | maxDepth + 1, environment, expression => do
    match expression with
    | .letTerm _ _ body | .letPredicate _ _ body => whnfPredicate maxDepth environment body
    | .definition name functions predicates =>
      match environment.lookup name with
      | some (.predicate declaration) =>
        whnfPredicate maxDepth environment (declaration.body.instantiate functions predicates)
      | _ => referenceError environment name .predicate
    | .app function argument =>
      let function ← whnfPredicate maxDepth environment function
      match function with
      | .lam _ body => whnfPredicate maxDepth environment (body.subst0 argument)
      | _ => pure (.app function argument)
    | _ => pure expression

/-- Normalize a checked predicate at `arity` by eta-expanding and beta-reducing. -/
def reducePredicate : Nat → Environment → Arity → Predicate → CheckResult Predicate
  | 0, _, _, _ => exhausted
  | maxDepth + 1, environment, arity, expression => do
    match arity with
    | k + 1 =>
      let body ← reducePredicate maxDepth environment k (.app expression.shift (.bvar 0))
      pure (.lam .anonymous body)
    | 0 =>
      let expression ← whnfPredicate maxDepth environment expression
      match expression with
      | .false => pure .false
      | .true => pure .true
      | .equal left right =>
        return .equal (← reduceTerm maxDepth environment 0 left)
          (← reduceTerm maxDepth environment 0 right)
      | .imp left right =>
        return .imp (← reducePredicate maxDepth environment 0 left)
          (← reducePredicate maxDepth environment 0 right)
      | .and left right =>
        return .and (← reducePredicate maxDepth environment 0 left)
          (← reducePredicate maxDepth environment 0 right)
      | .or left right =>
        return .or (← reducePredicate maxDepth environment 0 left)
          (← reducePredicate maxDepth environment 0 right)
      | .all body => return .all (← reducePredicate maxDepth environment 1 body)
      | .ex body => return .ex (← reducePredicate maxDepth environment 1 body)
      | .parameter index => pure (.parameter index)
      | .app function argument =>
        return .app (← reducePredicateNeutral maxDepth environment function)
          (← reduceTerm maxDepth environment 0 argument)
      | _ => fail (.expectedForm .formula (.predicate expression))

/-- Normalize the arguments of a neutral predicate application without eta-expanding its head. -/
def reducePredicateNeutral : Nat → Environment → Predicate → CheckResult Predicate
  | 0, _, _ => exhausted
  | maxDepth + 1, environment, expression => do
    let expression ← whnfPredicate maxDepth environment expression
    match expression with
    | .parameter index => pure (.parameter index)
    | .app function argument =>
      return .app (← reducePredicateNeutral maxDepth environment function)
        (← reduceTerm maxDepth environment 0 argument)
    | _ => fail (.expectedForm .neutralPredicate (.predicate expression))

end

/-- Normalize a checked formula (arity `0`). -/
def reduceFormula (maxDepth : Nat) (environment : Environment) (expression : Predicate) :
    CheckResult Predicate :=
  reducePredicate maxDepth environment 0 expression

/-- Contract beta redexes in a term, keeping definitions, lets, and `primrec` intact. -/
def betaReduceTerm : Nat → Term → Term
  | 0, t => t
  | k + 1, t => match t with
    | .app f a =>
      let f := betaReduceTerm k f
      let a := betaReduceTerm k a
      match f with
      | .lam _ body => betaReduceTerm k (body.subst0 a)
      | _ => .app f a
    | .lam n body => .lam n (betaReduceTerm k body)
    | .letE n a body =>
      .letE n (betaReduceTerm k a) (betaReduceTerm k body)
    | .primrec b s => .primrec (betaReduceTerm k b) (betaReduceTerm k s)
    | .definition n fs => .definition n (fs.map (betaReduceTerm k))
    | _ => t

/-- Contract beta redexes in a predicate, keeping definitions, lets, and `primrec` intact. -/
def betaReducePredicate : Nat → Predicate → Predicate
  | 0, p => p
  | k + 1, p => match p with
    | .app f a =>
      let f := betaReducePredicate k f
      let a := betaReduceTerm k a
      match f with
      | .lam _ body => betaReducePredicate k (body.subst0 a)
      | _ => .app f a
    | .lam n body => .lam n (betaReducePredicate k body)
    | .equal a b => .equal (betaReduceTerm k a) (betaReduceTerm k b)
    | .imp a b => .imp (betaReducePredicate k a) (betaReducePredicate k b)
    | .and a b => .and (betaReducePredicate k a) (betaReducePredicate k b)
    | .or a b => .or (betaReducePredicate k a) (betaReducePredicate k b)
    | .all p => .all (betaReducePredicate k p)
    | .ex p => .ex (betaReducePredicate k p)
    | .letTerm n t p =>
      .letTerm n (betaReduceTerm k t) (betaReducePredicate k p)
    | .letPredicate n q p =>
      .letPredicate n (betaReducePredicate k q) (betaReducePredicate k p)
    | .definition n fs ps =>
      .definition n (fs.map (betaReduceTerm k)) (ps.map (betaReducePredicate k))
    | _ => p

end LeanPRA.Core
