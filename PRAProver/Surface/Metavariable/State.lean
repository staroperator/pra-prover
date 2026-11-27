module

public meta import PRAProver.Surface.Metavariable.Bridge
public meta import Lean.Message
public meta import Std.Data.HashMap.Basic

/-!
# Metavariable declarations and constraint state

State for metavariable allocation, assignments, and equality constraints during elaboration:

- `Entry` stores a metavariable's type, the local variable IDs in scope where it was created, and
  its assigned value if solved.
- `ProofEntry` stores a proof metavariable's formula, context, scope, and assignment.
- `Constraint` represents a term or predicate equality problem in its original local context.
- `State` stores allocated metavariables, equality problems, and the wakeup queue for blocked
  problems.
-/

public meta section
namespace PRAProver.Surface.Metavariable
open Core hiding Term Predicate Proof Context

/-- Identifier of a numerical or predicate metavariable in `State`. -/
inductive UnknownId where
  | term (index : Nat)
  | predicate (index : Nat)
  deriving BEq, Hashable, Repr

/-- Error returned by metavariable solving, substitution, or completion: a Core check failure,
an invalid assignment or equation, resource exhaustion, an unsupported equation, or an unresolved
metavariable. -/
inductive Failure where
  | core (error : CheckError)
  | invalid (message : String)
  | exhausted (operation : String)
  | unsupported (message : String)
  | incomplete (message : String)
  deriving Repr

/-- Format a `Failure` as a diagnostic message. -/
def Failure.message : Failure → String
  | .core error => error.message
  | .invalid message | .unsupported message | .incomplete message => message
  | .exhausted operation => operation ++ " exhausted"

instance : Lean.ToMessageData Failure := ⟨fun e => Lean.toMessageData e.message⟩

/-- Whether `Failure` hit a recursion or work limit. -/
def Failure.isExhausted : Failure → Bool
  | .exhausted _ => true
  | .core e => e.kind == .exhausted
  | _ => false

/-- Source syntax and description of an equality problem, kept when the problem is decomposed. -/
structure Origin where
  ref : Lean.Syntax := .missing
  description : String := "type compatibility"

/-- A metavariable entry: its type, the local variable IDs in scope at creation, its source binder
name, its assigned value (expressed in `locals`), and its display number. -/
structure Entry (α β : Type) where
  type : α
  locals : List Nat
  name : Lean.Name
  value : Option β := none
  id : Nat := 0

/-- A typed equality problem between two terms or two predicates in a local context. -/
inductive Constraint where
  | term (context : Context) (locals : List Nat) (arity : Nat) (left right : Term)
  | predicate (context : Context) (locals : List Nat) (arity : Nat) (left right : Predicate)

/-- Status of an equality problem: ready to run, waiting on unassigned metavariables, solved,
split into child problems, or failed. -/
inductive Progress where
  | ready
  | blocked (dependencies : List UnknownId)
  | solved
  | decomposed (children : List Nat)
  | conflict (failure : Failure)

/-- An equality problem in `State.problems`, with its origin, optional parent problem, contributing
problem IDs, and current status. -/
structure Problem where
  constraint : Constraint
  origin : Origin
  parent : Option Nat := none
  causes : List Nat := []
  progress : Progress := .ready
  heuristic : Bool := false

/-- A proof metavariable's formula, typing context, numerical local identities, and assignment.
Assignments use the indices of the recorded context. -/
structure ProofEntry where
  type : Predicate
  context : Context
  locals : List Nat
  value : Option Proof := none

/-- Metavariable and constraint state for elaborating one declaration or command.
`baseFunctions` and `basePredicates` count the declaration's own parameters. -/
structure State where
  baseFunctions : Nat := 0
  basePredicates : Nat := 0
  proofs : Array ProofEntry := #[]
  terms : Array (Entry Nat Term) := #[]
  predicates : Array (Entry PredicateSignature Predicate) := #[]
  problems : Array Problem := #[]
  awake : Array Nat := #[]
  awakeCursor : Nat := 0
  waiting : Std.HashMap UnknownId (List Nat) := {}
  changed : List UnknownId := []
  assignmentOrigins : Std.HashMap UnknownId Nat := {}
  currentProblem : Option Nat := none
  allowHeuristics : Bool := false
  usedHeuristic : Bool := false
  nextLocal : Nat := 1
  revision : Nat := 0

/-- Initial state for a declaration with `functions` function parameters and `predicates` predicate
parameters. -/
def empty (functions predicates : Nat) : State :=
  { baseFunctions := functions, basePredicates := predicates }

/-- Whether any numerical or predicate metavariable is still unassigned. -/
def hasUnassigned (state : State) : Bool :=
  state.terms.any (·.value.isNone) || state.predicates.any (·.value.isNone)

/-- Whether no metavariables have been allocated. -/
def isEmpty (state : State) : Bool :=
  state.terms.isEmpty && state.predicates.isEmpty && state.proofs.isEmpty

/-- Core parameter indices and display numbers (`?0`, `?1`, …) for all metavariables in `state`. -/
def displaySlots (state : State) : List (Nat × Nat) × List (Nat × Nat) :=
  ((state.terms.toList.zipIdx.map fun (u, i) => (state.baseFunctions + i, u.id)),
   (state.predicates.toList.zipIdx.map fun (u, i) => (state.basePredicates + i, u.id)))

/-- Solver monad with mutable `State` and `Failure` errors. -/
abbrev M := StateT State (Except Failure)

/-- Append the types of all allocated metavariables to `ctx`'s parameter lists. -/
def context (state : State) (ctx : Context) : Context :=
  { ctx with functions := ctx.functions.take state.baseFunctions ++ state.terms.toList.map (·.type)
             predicates := ctx.predicates.take state.basePredicates ++
               state.predicates.toList.map (·.type) }

/-- Allocate a fresh identity for a numerical local or proof hypothesis. -/
def freshLocal : M Nat := do
  let state ← get
  set { state with nextLocal := state.nextLocal + 1 }
  return state.nextLocal

/-- Allocate a fresh numerical metavariable of `arity` in the local scope `locals`. -/
def freshTerm (arity : Nat) (locals : List Nat) (name : Lean.Name := .anonymous) : M Term := do
  let state ← get
  let index := state.terms.size
  let id := state.terms.size + state.predicates.size
  set { state with terms := state.terms.push ⟨arity, locals, name, none, id⟩ }
  return .mvar index

/-- Allocate a fresh predicate metavariable of signature `sig` in the local scope `locals`. -/
def freshPredicate (sig : PredicateSignature) (locals : List Nat)
    (name : Lean.Name := .anonymous) : M Predicate := do
  let state ← get
  let index := state.predicates.size
  let id := state.terms.size + state.predicates.size
  set { state with predicates := state.predicates.push ⟨sig, locals, name, none, id⟩ }
  return .mvar index

/-- Allocate a proof metavariable at `type` in the supplied context. `locals` gives the numerical
local identities used by term and predicate inference. The caller checks formula formation;
the completed declaration is checked independently by Core. -/
def freshProof (type : Predicate) (context : Context) (locals : List Nat) : M Proof := do
  unless context.locals.length == locals.length do
    throw (.invalid "proof metavariable context does not match its numerical locals")
  unless locals.all (· != 0) && locals.eraseDups.length == locals.length do
    throw (.invalid "proof metavariable numerical locals need distinct nonzero identities")
  let state ← get
  let id := state.proofs.size
  set { state with proofs := state.proofs.push ⟨type, context, locals, none⟩ }
  return .mvar id ((List.range context.locals.length).map Term.bvar)
    ((List.range context.proofs.length).map Proof.hyp)

/-- `Projection` for encoding `state`'s metavariables as Core parameters after the declaration's
own parameters. -/
def State.projection (state : State) : Projection :=
  ⟨state.baseFunctions, state.basePredicates⟩

end PRAProver.Surface.Metavariable
