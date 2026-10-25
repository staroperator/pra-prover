module

public import LeanPRA.Core.Utils
public import LeanPRA.Core.Substitution

/-!
# Normalization with a recursion depth limit

Normalization reduces expressions to beta-long, eta-long normal form so the checker can compare
them for definitional equality.

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

mutual

/-- Reduce a checked term to weak head normal form. -/
def whnfTerm : Nat → Environment → Term → CheckResult Term
  | 0, _, _ => exhausted
  | maxDepth + 1, environment, expression => do
    match expression with
    | .definition name functions =>
      match environment.lookup name with
      | some (.function declaration) =>
        whnfTerm maxDepth environment (declaration.body.instantiate functions)
      | _ => referenceError environment name .function
    | .letE _ value body => whnfTerm maxDepth environment (body.subst0 value)
    | .app function argument =>
      let function ← whnfTerm maxDepth environment function
      match function with
      | .lam _ body => whnfTerm maxDepth environment (body.subst0 argument)
      | _ => pure (.app function argument)
    | .primrec base step argument =>
      let argument ← whnfTerm maxDepth environment argument
      match argument with
      | .zero => whnfTerm maxDepth environment base
      | .app .succ predecessor =>
        whnfTerm maxDepth environment
          (.app (.app step predecessor) (.primrec base step predecessor))
      | _ => pure (.primrec base step argument)
    | _ => pure expression

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
      | .app function argument =>
        let function ← reduceTermNeutral maxDepth environment function
        let argument ← reduceTerm maxDepth environment 0 argument
        pure (.app function argument)
      | .primrec base step argument =>
        let base ← reduceTerm maxDepth environment 0 base
        let step ← reduceTerm maxDepth environment 2 step
        let argument ← reduceTerm maxDepth environment 0 argument
        pure (.primrec base step argument)
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
    | .primrec b s n => .primrec (betaReduceTerm k b) (betaReduceTerm k s) (betaReduceTerm k n)
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
