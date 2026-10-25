module

public import LeanPRA.Core.Syntax

/-!
# Core checker results and diagnostics

Result and error types for the core checker:

- `ErrorReason` describes why a check failed, including expected and actual values.
- `CheckError.kind` groups errors into ill-formed input, failed checks, and depth exhaustion.
- `CheckSite` records the innermost failing expression and its `Context`.
- `Environment.lookup` looks up a declaration by name.

The surface frontend maps `CheckSite` to a source location and formats expressions for display.
-/

@[expose] public section

namespace LeanPRA.Core

/-- Error category: ill-formed input (`illformed`), failed typing or conversion (`failed`), or
reaching the recursion depth limit (`exhausted`). -/
inductive ErrorKind where
  | illformed
  | failed
  | exhausted
  deriving Repr, BEq

/-- Kind of declaration: function definition, predicate definition, or theorem. -/
inductive DeclarationKind where
  | function
  | predicate
  | theoremE
  deriving Repr, BEq

/-- Kind of a declaration. -/
def Declaration.kind : Declaration → DeclarationKind
  | .function _ => .function
  | .predicate _ => .predicate
  | .theoremE _ => .theoremE

/-- Which list in `Context` a variable, parameter, or hypothesis index refers to. -/
inductive VariableKind where
  | local
  | functionParameter
  | predicateParameter
  | proof
  deriving Repr, BEq

/-- Whether a declaration argument is a function or a predicate. -/
inductive ArgumentKind where
  | function
  | predicate
  deriving Repr, BEq

/-- A `Term`, `Predicate`, or `Proof` attached to an error or editor info node. -/
inductive CheckSubject where
  | term (expression : Term)
  | predicate (expression : Predicate)
  | proof (expression : Proof)
  deriving Repr, BEq

/-- An expression paired with its local `Context`. -/
structure CheckSite where
  context : Context
  subject : CheckSubject
  deriving Repr, BEq

/-- Syntactic form expected by an application, eliminator, or reduction step. -/
inductive ExpectedForm where
  | number
  | function
  | predicateFunction
  | neutralTerm
  | neutralPredicate
  | formula
  | implication
  | conjunction
  | disjunction
  | universal
  | existential
  | equality
  | successors
  deriving Repr, BEq

/-- Details of a checker failure. Conversion failures store both original and normalized
expressions; mismatches list `expected` before `actual`.
-/
inductive ErrorReason where
  | unboundVariable (kind : VariableKind) (index : Nat)
  | unknownDeclaration (name : Lean.Name) (expected : DeclarationKind)
  | declarationKind (name : Lean.Name) (expected actual : DeclarationKind)
  | duplicateDeclaration (name : Lean.Name)
  | argumentCount (name : Lean.Name) (kind : ArgumentKind) (expected actual : Nat)
  | arityMismatch (expected actual : Arity)
  | sortMismatch (expected actual : FormulaSort)
  | expectedForm (expected : ExpectedForm) (actual : CheckSubject)
  | termConversion (arity : Arity) (left right leftNormal rightNormal : Term)
  | predicateConversion (arity : Arity) (left right leftNormal rightNormal : Predicate)
  | proofTypeMismatch (expected actual expectedNormal actualNormal : Predicate)
  | recursionDepth
  deriving Repr, BEq

/-- Error category of an `ErrorReason`. -/
def ErrorReason.kind : ErrorReason → ErrorKind
  | .unboundVariable .. | .unknownDeclaration .. | .declarationKind ..
  | .duplicateDeclaration .. | .argumentCount .. => .illformed
  | .recursionDepth => .exhausted
  | _ => .failed

/-- A checker error, with the innermost failing `site` and the enclosing `declaration` name. -/
structure CheckError where
  reason : ErrorReason
  site : Option CheckSite := none
  declaration : Option Lean.Name := none
  deriving Repr, BEq

/-- Error category of `error`. -/
def CheckError.kind (error : CheckError) : ErrorKind := error.reason.kind

/-- Plain-text message for `error`. -/
def CheckError.message (error : CheckError) : String :=
  let declarationKindDescription : DeclarationKind → String := fun
    | .function => "function definition"
    | .predicate => "predicate definition"
    | .theoremE => "theorem"

  let variableKindDescription : VariableKind → String := fun
    | .local => "local variable"
    | .functionParameter => "function parameter"
    | .predicateParameter => "predicate parameter"
    | .proof => "proof hypothesis"

  let expectedFormDescription : ExpectedForm → String := fun
    | .number => "a natural number"
    | .function => "a numerical function"
    | .predicateFunction => "a predicate with numerical arguments"
    | .neutralTerm => "a numerical expression that cannot reduce further"
    | .neutralPredicate => "a predicate expression that cannot reduce further"
    | .formula => "a formula of arity 0"
    | .implication => "an implication"
    | .conjunction => "a conjunction"
    | .disjunction => "a disjunction"
    | .universal => "a universally quantified formula"
    | .existential => "an existentially quantified formula"
    | .equality => "a numerical equality"
    | .successors => "an equality between successors"
  match error.reason with
  | .unboundVariable kind index => s!"unbound {variableKindDescription kind} at index {index}"
  | .unknownDeclaration name expected => s!"unknown {declarationKindDescription expected} `{name}`"
  | .declarationKind name expected actual =>
    s!"expected {declarationKindDescription expected} `{name}`, but found a \
      {declarationKindDescription actual}"
  | .duplicateDeclaration name => s!"duplicate declaration name `{name}`"
  | .argumentCount name kind expected actual =>
    let kind := match kind with | .function => "function" | .predicate => "predicate"
    s!"`{name}` expects {expected} {kind} arguments for its parameters, but received {actual}"
  | .arityMismatch expected actual => s!"expected numerical arity {expected}, got {actual}"
  | .sortMismatch expected actual =>
    let sortName : FormulaSort → String := fun | .qf => "QFProp" | .prop => "Prop"
    s!"expected formula sort {sortName expected}, got {sortName actual}"
  | .expectedForm expected _ => s!"expected {expectedFormDescription expected}"
  | .termConversion .. => "terms are not definitionally equal"
  | .predicateConversion .. => "predicates are not definitionally equal"
  | .proofTypeMismatch .. => "inferred proof type is not definitionally equal to the expected type"
  | .recursionDepth => "checker recursion depth limit exhausted"

/-- Result of a core check or reduction. -/
abbrev CheckResult (α : Type) := Except CheckError α

/-- Attach `context` and `subject` if the error does not already have a `site`. -/
def CheckResult.withSite (result : CheckResult α) (context : Context)
    (subject : CheckSubject) : CheckResult α :=
  result.mapError fun error =>
    { error with site := error.site.or (some { context, subject }) }

/-- Attach the enclosing declaration `name` to an error. -/
def CheckResult.inDeclaration (result : CheckResult α) (name : Lean.Name) : CheckResult α :=
  result.mapError fun error => { error with declaration := some name }

/-- Fail with `reason`. -/
def fail (reason : ErrorReason) : CheckResult α := .error { reason }

/-- Fail with `ErrorReason.recursionDepth`. -/
def exhausted : CheckResult α := fail .recursionDepth

/-- Fail because `name` is missing from `environment` or has the wrong `DeclarationKind`. -/
def referenceError (environment : Environment) (name : Lean.Name)
    (expected : DeclarationKind) : CheckResult α :=
  match environment[name]? with
  | none => fail (.unknownDeclaration name expected)
  | some actual => fail (.declarationKind name expected actual.kind)

/-- Look up `name` in `environment`. -/
def Environment.lookup (environment : Environment) (name : Lean.Name) : Option Declaration :=
  environment[name]?

end LeanPRA.Core
