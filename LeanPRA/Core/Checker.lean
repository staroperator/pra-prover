module

public import LeanPRA.Core.DefEq
public import LeanPRA.Core.PrimitiveTypes

/-!
# Checking PRA expressions and declarations

Type checking and inference for PRA expressions and declarations:

- `checkDeclaration` checks a declaration and inserts it into the environment.
- `inferTerm` infers a term's arity.
- `inferPredicate` infers a predicate's arity and sort.
- `inferFormula` checks that a predicate has arity `0` and returns its sort.
- `inferProof` infers the formula proved by a proof expression.
- `checkTerm`, `checkPredicate`, and `checkProof` check expressions against expected types.
- `checkContext` validates a supplied list of proof hypotheses.

All operations are in `LeanPRA.Core`. Callers build `Environment` from `∅` through
`checkDeclaration` and maintain well-formed local contexts as they introduce bindings.
`checkProof` also assumes its expected formula is well formed.
Proof inference uses weak-head reduction to expose the constructor needed by each rule,
so its results preserve expressions inside that constructor. Term, predicate, and proof checking
use structural definitional equality, computing heads where comparison requires it.
Equality assumes well-typed inputs at the supplied arities.
`maxDepth` bounds recursive call depth; `ErrorKind.exhausted` means checking hit the depth limit.
-/

@[expose] public section

namespace LeanPRA.Core

/-!
Expression checking assumes a well-formed environment and context. `checkContext` validates raw
contexts explicitly. Declaration checking starts with an empty proof context and checks every
binder and local definition while traversing the declaration body.
-/

def checkArity (expected actual : Arity) : CheckResult Unit :=
  if expected == actual then pure ()
  else fail (.arityMismatch expected actual)

def checkArgumentCount (name : Lean.Name) (kind : ArgumentKind)
    (expected actual : Nat) : CheckResult Unit :=
  if expected == actual then pure () else fail (.argumentCount name kind expected actual)

/-- Infer the arity of a term. -/
def inferTerm : Nat → Environment → Context → Term → CheckResult Arity
  | 0, _, context, expression => exhausted.withSite context (.term expression)
  | maxDepth + 1, environment, context, expression =>
    (show CheckResult Arity from do
      match expression with
      | .bvar i =>
        match context.locals[i]? with
        | some arity => pure arity
        | none => fail (.unboundVariable .local i)
      | .parameter i =>
        match context.functions[i]? with
        | some arity => pure arity
        | none => fail (.unboundVariable .functionParameter i)
      | .zero => pure 0
      | .succ => pure 1
      | .lam _ body =>
        let arity ← (inferTerm maxDepth environment (context.pushExpressionLocal 0) body)
        pure (arity + 1)
      | .app function argument =>
        let arity ← (inferTerm maxDepth environment context function)
        match arity with
        | 0 => fail (.expectedForm .function (.term function))
        | arity + 1 =>
          checkArity 0 (← (inferTerm maxDepth environment context argument))
          pure arity
      | .letE _ value body =>
        let arity ← (inferTerm maxDepth environment context value)
        (inferTerm maxDepth environment (context.pushExpressionLocal arity) body)
      | .primrec base step =>
        (do checkArity 0 (← inferTerm maxDepth environment context base))
          |>.withSite context (.term base)
        (do checkArity 2 (← inferTerm maxDepth environment context step))
          |>.withSite context (.term step)
        pure 1
      | .definition name functions =>
        match environment.lookup name with
        | some (.function declaration) =>
          checkArgumentCount name .function declaration.functions.length functions.length
          for (expected, actual) in declaration.functions.zip functions do
            (do checkArity expected (← inferTerm maxDepth environment context actual))
            |>.withSite context (.term actual)
          pure declaration.arity
        | _ => referenceError environment name .function
    ).withSite context (.term expression)

/-- Check that `term` has arity `expected`. -/
def checkTerm (maxDepth : Nat) (environment : Environment) (context : Context)
    (term : Term) (expected : Arity) : CheckResult Unit :=
  (do checkArity expected (← inferTerm maxDepth environment context term))
    |>.withSite context (.term term)

def checkFunctionArguments (maxDepth : Nat) (environment : Environment) (context : Context)
    (name : Lean.Name) (signatures : List Arity) (actuals : List Term) : CheckResult Unit := do
  checkArgumentCount name .function signatures.length actuals.length
  for (expected, actual) in signatures.zip actuals do
    (do checkArity expected (← inferTerm maxDepth environment context actual))
      |>.withSite context (.term actual)

def checkSort (expected actual : FormulaSort) : CheckResult Unit :=
  if expected == .qf && actual != .qf then fail (.sortMismatch expected actual)
  else pure ()

/-- Infer the arity and sort of a predicate. -/
def inferPredicate : Nat → Environment → Context → Predicate → CheckResult PredicateSignature
  | 0, _, context, expression => exhausted.withSite context (.predicate expression)
  | maxDepth + 1, environment, context, expression =>
    (show CheckResult PredicateSignature from do
      match expression with
      | .false | .true => pure ⟨0, .qf⟩
      | .letTerm _ value body =>
        let _ ← inferTerm maxDepth environment context value
        inferPredicate maxDepth environment context body
      | .letPredicate _ value body =>
        let _ ← inferPredicate maxDepth environment context value
        inferPredicate maxDepth environment context body
      | .equal left right =>
        checkTerm maxDepth environment context left 0
        checkTerm maxDepth environment context right 0
        pure ⟨0, .qf⟩
      | .imp left right | .and left right | .or left right =>
        let leftType ← inferPredicate maxDepth environment context left
        let rightType ← inferPredicate maxDepth environment context right
        (checkArity 0 leftType.arity).withSite context (.predicate left)
        (checkArity 0 rightType.arity).withSite context (.predicate right)
        pure ⟨0, FormulaSort.join leftType.sort rightType.sort⟩
      | .all body | .ex body =>
        let signature ← (inferPredicate maxDepth environment context body)
        (checkArity 1 signature.arity).withSite context (.predicate body)
        pure ⟨0, .prop⟩
      | .parameter i =>
        match context.predicates[i]? with
        | some signature => pure signature
        | none => fail (.unboundVariable .predicateParameter i)
      | .lam _ body =>
        let signature ←
          (inferPredicate maxDepth environment (context.pushExpressionLocal 0) body)
        pure ⟨signature.arity + 1, signature.sort⟩
      | .app function argument =>
        let signature ← (inferPredicate maxDepth environment context function)
        match signature.arity with
        | 0 => fail (.expectedForm .predicateFunction (.predicate function))
        | k + 1 =>
          checkTerm maxDepth environment context argument 0
          pure ⟨k, signature.sort⟩
      | .definition name functions predicates =>
        match environment.lookup name with
        | some (.predicate declaration) =>
          checkFunctionArguments maxDepth environment context name declaration.functions functions
          checkArgumentCount name .predicate declaration.predicates.length predicates.length
          for (expected, actual) in declaration.predicates.zip predicates do
            (do
              let signature ← inferPredicate maxDepth environment context actual
              checkArity expected.arity signature.arity
              checkSort expected.sort signature.sort
            ).withSite context (.predicate actual)
          pure declaration.signature
        | _ => referenceError environment name .predicate
    ).withSite context (.predicate expression)

/-- Check `predicate` against `expected`, allowing `qf` where `prop` is expected. -/
def checkPredicate (maxDepth : Nat) (environment : Environment) (context : Context)
    (predicate : Predicate) (expected : PredicateSignature) : CheckResult Unit :=
  (do
    let actual ← inferPredicate maxDepth environment context predicate
    checkArity expected.arity actual.arity
    checkSort expected.sort actual.sort
  ).withSite context (.predicate predicate)

/-- Check that `predicate` has arity `0` and return its sort. -/
def inferFormula (maxDepth : Nat) (environment : Environment) (context : Context)
    (predicate : Predicate) : CheckResult FormulaSort :=
  (do
    let signature ← inferPredicate maxDepth environment context predicate
    checkArity 0 signature.arity
    pure signature.sort
  ).withSite context (.predicate predicate)

/-- Check that `formula` has arity `0` and sort `expected`. -/
def checkFormula (maxDepth : Nat) (environment : Environment) (context : Context)
    (formula : Predicate) (expected : FormulaSort) : CheckResult Unit :=
  checkPredicate maxDepth environment context formula ⟨0, expected⟩

/-- Check that `motive` is a unary predicate of sort `sort`. -/
def checkMotive (maxDepth : Nat) (environment : Environment) (context : Context)
    (motive : Predicate) (sort : FormulaSort := .prop) : CheckResult Unit :=
  checkPredicate maxDepth environment context motive ⟨1, sort⟩

def checkPredicateArguments (maxDepth : Nat) (environment : Environment) (context : Context)
    (name : Lean.Name) (signatures : List PredicateSignature)
    (actuals : List Predicate) : CheckResult Unit := do
  checkArgumentCount name .predicate signatures.length actuals.length
  for (expected, actual) in signatures.zip actuals do
    checkPredicate maxDepth environment context actual expected

/-- Compare well-typed terms at their common numerical arity. -/
def equalTerms (maxDepth : Nat) (environment : Environment) (arity : Arity)
    (left right : Term) : CheckResult Unit := do
  if ← defEqTerm maxDepth environment arity left right then pure ()
  else fail (.termConversion arity left right)

/-- Compare well-typed predicates at their common arity. -/
def equalPredicates (maxDepth : Nat) (environment : Environment) (arity : Arity)
    (left right : Predicate) : CheckResult Unit := do
  if ← defEqPredicate maxDepth environment arity left right then pure ()
  else fail (.predicateConversion arity left right)

/-- Compare well-formed formulas by definitional equality. -/
def equalFormulas (maxDepth : Nat) (environment : Environment)
    (left right : Predicate) : CheckResult Unit :=
  equalPredicates maxDepth environment 0 left right

def equalitySides (formula : Predicate) : CheckResult (Term × Term) :=
  match formula with
  | .equal left right => pure (left, right)
  | _ => fail (.expectedForm .equality (.predicate formula))

mutual

/-- Infer the formula proved by a proof expression. -/
def inferProof : Nat → Environment → Context → Proof → CheckResult Predicate
  | 0, _, context, expression => exhausted.withSite context (.proof expression)
  | maxDepth + 1, environment, context, expression =>
    (show CheckResult Predicate from do
      match expression with
      | .trueIntro => pure .true
      | .hyp i =>
        match context.proofs[i]? with
        | some formula => pure formula
        | none => fail (.unboundVariable .proof i)
      | .theoremE name functions predicates =>
        match environment.lookup name with
        | some (.theoremE declaration) =>
          checkFunctionArguments maxDepth environment context name declaration.functions functions
          checkPredicateArguments maxDepth environment context name
            declaration.predicates predicates
          pure (declaration.type.instantiate functions predicates)
        | _ => referenceError environment name .theoremE
      | .impIntro _ antecedent body =>
        let _ ← (inferFormula maxDepth environment context antecedent)
        let consequent ← (inferProof maxDepth environment (context.pushProof antecedent) body)
        pure (.imp antecedent consequent)
      | .impElim function argument =>
        let type ← whnfPredicate maxDepth environment
          (← inferProof maxDepth environment context function)
        match type with
        | .imp antecedent consequent =>
          (checkProof maxDepth environment context argument antecedent)
          pure consequent
        | actual => fail (.expectedForm .implication (.predicate actual))
      | .andIntro left right =>
        return .and (← (inferProof maxDepth environment context left))
          (← (inferProof maxDepth environment context right))
      | .andLeft left right | .andRight left right
      | .orLeft left right | .orRight left right =>
        let _ ← inferFormula maxDepth environment context left
        let _ ← inferFormula maxDepth environment context right
        match expression with
        | .andLeft .. => pure (.imp (.and left right) left)
        | .andRight .. => pure (.imp (.and left right) right)
        | .orLeft .. => pure (.imp left (.or left right))
        | _ => pure (.imp right (.or left right))
      | .orElim left right target =>
        let _ ← inferFormula maxDepth environment context left
        let _ ← inferFormula maxDepth environment context right
        let _ ← inferFormula maxDepth environment context target
        pure (.imp (.or left right) (.imp (.imp left target) (.imp (.imp right target) target)))
      | .falseElim target =>
        let _ ← inferFormula maxDepth environment context target
        pure (.imp .false target)
      | .forallIntro _ motive body =>
        checkMotive maxDepth environment context motive
        let extended := context.pushLocal 0
        (checkProof maxDepth environment extended body (.app motive.shift (.bvar 0)))
        pure (.all motive)
      | .forallElim proof argument =>
        checkTerm maxDepth environment context argument 0
        match ← whnfPredicate maxDepth environment
          (← inferProof maxDepth environment context proof) with
        | .all body => pure (.app body argument)
        | actual => fail (.expectedForm .universal (.predicate actual))
      | .existsIntro motive witness proof =>
        checkMotive maxDepth environment context motive
        checkTerm maxDepth environment context witness 0
        (checkProof maxDepth environment context proof (.app motive witness))
        pure (.ex motive)
      | .existsElim motive target =>
        checkMotive maxDepth environment context motive
        let _ ← inferFormula maxDepth environment context target
        pure (existentialEliminationType motive target)
      | .letE _ type value body =>
        let _ ← inferFormula maxDepth environment context type
        (checkProof maxDepth environment context value type)
        (inferProof maxDepth environment (context.pushProof type) body)
      | .letTerm _ value body =>
        let _ ← inferTerm maxDepth environment context value
        inferProof maxDepth environment context body
      | .letPredicate _ value body =>
        let _ ← inferPredicate maxDepth environment context value
        inferProof maxDepth environment context body
      | .ascribe type proof =>
        let _ ← inferFormula maxDepth environment context type
        checkProof maxDepth environment context proof type
        pure type
      | .eqRefl => pure reflexivityType
      | .eqSubst motive =>
        checkMotive maxDepth environment context motive
        pure (substitutionType motive)
      | .succNeZero => pure successorNonzeroType
      | .succInj => pure successorInjectivityType
      | .lem formula =>
        let _ ← inferFormula maxDepth environment context formula
        pure (.or formula (.imp formula .false))
      | .induction motive =>
        checkMotive maxDepth environment context motive .qf
        pure (inductionType motive)
    ).withSite context (.proof expression)

/-- Check that `proof` proves a formula definitionally equal to the well-formed `expected`. -/
def checkProof : Nat → Environment → Context → Proof → Predicate → CheckResult Unit
  | 0, _, context, proof, _ => exhausted.withSite context (.proof proof)
  | maxDepth + 1, environment, context, proof, expected =>
    (show CheckResult Unit from do
      let actual ← inferProof maxDepth environment context proof
      if ← defEqPredicate maxDepth environment 0 actual expected then pure ()
      else fail (.proofTypeMismatch expected actual)
    ).withSite context (.proof proof)

end

/-- Check that every proof hypothesis in `context` is a well-typed formula. -/
def checkContext (maxDepth : Nat) (environment : Environment)
    (context : Context) : CheckResult Unit := do
  for formula in context.proofs do
    let _ ← (inferFormula maxDepth environment context formula)

/-- Check `declaration` in `environment`, rejecting duplicate declaration names. -/
def checkDeclarationBody (maxDepth : Nat) (environment : Environment)
    (declaration : Declaration) : CheckResult Unit := do
  if (environment.lookup declaration.name).isSome then
    fail (.duplicateDeclaration declaration.name)
  else
    match declaration with
    | .function definition =>
      let context : Context := { functions := definition.functions }
      checkTerm maxDepth environment context definition.body definition.arity
    | .predicate definition =>
      let context : Context := {
        functions := definition.functions
        predicates := definition.predicates }
      checkPredicate maxDepth environment context definition.body definition.signature
    | .theoremE definition =>
      let context : Context := {
        functions := definition.functions
        predicates := definition.predicates }
      let _ ← inferFormula maxDepth environment context definition.type
      checkProof maxDepth environment context definition.body definition.type

/-- Check `declaration` and insert it into `environment`. -/
def checkDeclaration (maxDepth : Nat) (environment : Environment)
    (declaration : Declaration) : CheckResult Environment := do
  (checkDeclarationBody maxDepth environment declaration).inDeclaration declaration.name
  pure (environment.insert declaration.name declaration)

end LeanPRA.Core
