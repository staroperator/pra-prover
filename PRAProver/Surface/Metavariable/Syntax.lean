module

public meta import PRAProver.Core.Syntax

/-!
# Expressions with explicit metavariables

Expressions used during Surface elaboration before all implicit arguments are known:

- `Term` and `Predicate` represent numerical and predicate expressions with explicit unknowns.
- `Proof` represents proofs with unknown subproofs, terms, and predicates.
- `Context` stores the types of local variables, parameters, and proof hypotheses.
- `Subject` wraps a term, predicate, or proof for source diagnostics.

Each `Term` and `Predicate` has separate constructors for declaration parameters (`parameter`) and
metavariables (`mvar`). Each expression category uses separate `0`-based indices in the
elaboration state. Core typing and reduction functions run on these expressions through `Projection`
in `PRAProver.Surface.Metavariable.Bridge`.
-/

public meta section
namespace PRAProver.Surface.Metavariable
open Core hiding Term Predicate

/-- Numerical terms and first-order functions on `Nat`, with `mvar` for unknown numerical or
function arguments. -/
inductive Term where
  | bvar (index : Nat)
  | parameter (index : Nat)
  | mvar (id : Nat)
  | zero
  | succ
  | lam (binderName : Lean.Name) (body : Term)
  | app (function argument : Term)
  | letE (binderName : Lean.Name) (value body : Term)
  | primrec (base step : Term)
  | definition (name : Lean.Name) (functions : List Term)
  deriving Repr, Inhabited, BEq

/-- Formulas and predicates on `Nat`, with `mvar` for unknown predicate or formula arguments.
A formula is a predicate of arity `0`. `lam` binds one `Nat` variable. The quantifiers `all` and
`ex` take a unary predicate. Negation is `imp A false`. -/
inductive Predicate where
  | false
  | true
  | equal (left right : Term)
  | imp (antecedent consequent : Predicate)
  | and (left right : Predicate)
  | or (left right : Predicate)
  | all (predicate : Predicate)
  | ex (predicate : Predicate)
  | parameter (index : Nat)
  | mvar (id : Nat)
  | lam (binderName : BinderInfo) (body : Predicate)
  | app (predicate : Predicate) (argument : Term)
  | letTerm (binderName : Lean.Name) (value : Term) (body : Predicate)
  | letPredicate (binderName : Lean.Name) (value body : Predicate)
  | definition (name : Lean.Name) (functions : List Term) (predicates : List Predicate)
  deriving Repr, Inhabited, BEq

/-- Proof expressions with explicit metavariables. Each metavariable occurrence supplies its
captured numerical variables and hypotheses as arguments, ordered from innermost to outermost.
Embedded terms and predicates may also contain metavariables. -/
inductive Proof where
  | mvar (id : Nat) (termArgs : List Term) (proofArgs : List Proof)
  | hyp (index : Nat)
  | trueIntro
  | theoremE (name : Lean.Name) (functions : List Term) (predicates : List Predicate)
  | impIntro (binderName : Lean.Name) (antecedent : Predicate) (body : Proof)
  | impElim (function argument : Proof)
  | andIntro (left right : Proof)
  | andLeft (left right : Predicate)
  | andRight (left right : Predicate)
  | orLeft (left right : Predicate)
  | orRight (left right : Predicate)
  | orElim (left right target : Predicate)
  | falseElim (target : Predicate)
  | forallIntro (binderName : Lean.Name) (motive : Predicate) (body : Proof)
  | forallElim (proof : Proof) (argument : Term)
  | existsIntro (motive : Predicate) (witness : Term) (proof : Proof)
  | existsElim (motive target : Predicate)
  | letE (binderName : Lean.Name) (type : Predicate) (value body : Proof)
  | letTerm (binderName : Lean.Name) (value : Term) (body : Proof)
  | letPredicate (binderName : Lean.Name) (value : Predicate) (body : Proof)
  | ascribe (type : Predicate) (proof : Proof)
  | eqRefl
  | eqSubst (motive : Predicate)
  | succNeZero
  | succInj
  | lem (formula : Predicate)
  | induction (motive : Predicate)
  deriving Repr, BEq, Inhabited

/-- Typing context for local variables, declaration parameters, and proof hypotheses during
elaboration. -/
structure Context where
  locals : List Arity := []
  functions : List Arity := []
  predicates : List PredicateSignature := []
  proofs : List Predicate := []
  deriving Repr, BEq, Inhabited

/-- A term, predicate, or proof saved for hover and error reporting. -/
inductive Subject where
  | term (value : Term)
  | predicate (value : Predicate)
  | proof (value : Proof)
  deriving BEq

end PRAProver.Surface.Metavariable
