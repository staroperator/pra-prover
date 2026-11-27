module

public meta import LeanPRA.Surface.IDE

/-!
# PRA tactic interface

Tactics are Lean programs that fill contextual PRA proof metavariables.

- `Goal` describes a goal in its saved local context.
- `Context` connects tactics to the PRA elaborator, including transactional state restoration.
- `TacticM` carries an ordered list of goals; `refine` replaces the first goal with explicit holes.
- `applyProof`, `assert`, `replaceHypothesis`, `assertPremise`, `change`, `define`, `redefine`,
  `rename`, `clearHypothesis`, and `prove` act on goals using proof data built by a tactic.
  They use four basic operations of `Context`: read a goal's target, check a proof, open a goal,
  and assign a goal.
- `withTacticInfo` records goals before and after a tactic step at its source range.
- `evalTactic` dispatches syntax to programs registered with `@[pra_tactic syntaxKind]`.

Tactic programs and their syntax belong in `LeanPRA.Library.Tactic` modules. Every finished proof
passes through the ordinary PRA declaration checker.

Register syntax and its Lean implementation outside a `pra` block:

```
open Lean LeanPRA.Surface LeanPRA.Surface.Tactic

syntax (name := trivialTac) "trivial" : praTactic

@[pra_tactic trivialTac]
meta def evalTrivial : Tactic := fun _ => Tactic.close .trueIntro
```

`Tactic.refine` elaborates quoted `praExpr` syntax. Use `?_` for new proof goals and `_` for
arguments to infer. `Tactic.close` checks explicit proof data. Use `public meta section` to export
a tactic from a Lean module.

A tactic that has computed its step as data passes the data on directly.
`Tactic.applyProof rule [P₁, …, Pₙ]` takes a proof of `P₁ → ⋯ → Pₙ → target` and makes
`P₁, …, Pₙ` the new goals. `Tactic.define x value` continues with the same target under the
local definition `x := value`, `Tactic.assert h type proof` continues under the proven hypothesis
`h : type`, `Tactic.assertPremise type proof` turns the target `T` into `type → T`, and
`Tactic.change type` replaces the target by a definitionally equal one.
`Tactic.prove type tactic` proves a separate statement in the first goal's context and returns
its proof.

For example, `refine (_, ?_)` builds an existential proof whose witness can be inferred while
solving the new proof goal. A proof-position `_` reports an inference error suggesting `?_`.
-/

public meta section
namespace LeanPRA.Surface
open Lean Elab Command

declare_syntax_cat praTactic (behavior := both)
syntax praTacticSeq := sepBy1IndentSemicolon(praTactic)
syntax (name := praBy) "by" ppIndent(colGt praTacticSeq) : praExpr

namespace Tactic

/-- Index of a contextual proof metavariable in the current elaboration session. -/
abbrev GoalId := Nat

/-- The target and names of a goal, using its creation context's variable indices. -/
structure Goal where
  target : Metavariable.Predicate
  context : Metavariable.Context
  names : Names
  environment : Core.Environment
  projection : Metavariable.Projection
  maxDepth : Nat

/-- A change to the bindings of a new goal.
`ref` is the identifier in the source that introduces the name, when there is one; editor
information is attached to it. A `redefinition` gives a defined name a new value, and the goal
display lists the name once. A `replacement` changes a hypothesis at its existing index.
A `removal` drops a hypothesis and shifts the following proof indices. A `renaming` changes
local names while preserving their values and context indices. -/
inductive Binding where
  /-- An abstract local of the given arity. Supply its value in the hole's context arguments
  when using the new goal's proof in the original scope. -/
  | variable (name : Name) (arity : Nat) (ref : Syntax := .missing)
  | definition (name : Name) (value : Metavariable.Term) (ref : Syntax := .missing)
  | hypothesis (name : Name) (type : Metavariable.Predicate) (ref : Syntax := .missing)
  | redefinition (name : Name) (value : Metavariable.Term)
  | renaming (oldName newName : Name)
  | replacement (index : Nat) (type : Metavariable.Predicate) (ref : Syntax := .missing)
  | removal (index : Nat)

/-- Operations supplied by the elaborator.

- `inspect` returns a goal with its context and names.
- `refine` elaborates syntax against a goal and returns its explicit proof holes in source order.
- `target` returns the statement of a goal.
- `check` checks an explicit proof, without open proof metavariables, against a statement in a
  goal's context, and returns the proof with its inferred arguments filled in.
- `openGoal` creates a goal for a statement in the context of the given goal, applying the
  bindings in order. It returns the new goal and its proof metavariable in the resulting context.
- `assign` fills a goal with a proof, which may contain goals created by `openGoal`.
- `prove` opens a goal for a statement in the given goal's context, passes it to the supplied
  action, reports the goals that the action returns as unsolved, and returns the finished proof.
- `unknownTerm` creates a numerical unknown.
- `infer` can constrain an inferred type while returning its original form with arguments
  resolved. `term` and `proof` elaborate syntax in a goal's context; `proof` can constrain the
  type to an expected statement, which may contain unknowns.
- `save` captures assignments, constraints, goals, diagnostics, and editor information.
- `snapshot` builds a native infoview snapshot for the supplied goal list. -/
structure Context where
  inspect : GoalId → CommandElabM Goal
  refine : GoalId → Syntax → CommandElabM (List GoalId)
  target : GoalId → CommandElabM Metavariable.Predicate
  check : GoalId → Metavariable.Proof → Metavariable.Predicate → CommandElabM Metavariable.Proof
  openGoal : GoalId → Metavariable.Predicate → List Binding →
    CommandElabM (GoalId × Metavariable.Proof)
  assign : GoalId → Metavariable.Proof → CommandElabM Unit
  prove : GoalId → Metavariable.Predicate → Syntax → (GoalId → CommandElabM (List GoalId)) →
    CommandElabM Metavariable.Proof
  unknownTerm : GoalId → CommandElabM Metavariable.Term
  infer : GoalId → Syntax → Option Syntax → CommandElabM Metavariable.Predicate
  term : GoalId → Syntax → Nat → CommandElabM Metavariable.Term
  proof : GoalId → Syntax → Option Metavariable.Predicate →
    CommandElabM (Metavariable.Proof × Metavariable.Predicate)
  save : CommandElabM (CommandElabM Unit)
  snapshot : List GoalId → Syntax → CommandElabM Info

/-- A tactic program, with an ordered list of open proof metavariables. -/
abbrev TacticM := ReaderT Context (StateRefT (List GoalId) CommandElabM)

/-- Elaborator for one registered tactic syntax node. -/
abbrev Tactic := Syntax → TacticM Unit

unsafe initialize tacticElabAttribute : KeyedDeclsAttribute Tactic ←
  mkElabAttribute Tactic `builtin_pra_tactic `pra_tactic `LeanPRA.Surface
    `LeanPRA.Surface.Tactic.Tactic "PRA tactic"

/-- Return the first open goal, or report that the proof is already complete. -/
def mainGoal : TacticM GoalId := do
  let goal :: _ ← get | throwError "no PRA goals to solve"
  return goal

/-- Read the target and context of the first goal. -/
def getGoal : TacticM Goal := do
  (← read).inspect (← mainGoal)

/-- Elaborate a proof against the first goal. Explicit `?_` and named proof holes become the new
leading goals. Numerical and predicate `_` arguments are inferred from elaboration constraints. -/
def refine (proof : TSyntax `praExpr) : TacticM Unit := do
  let goal ← mainGoal
  let goals ← (← read).refine goal proof
  modify fun rest => goals ++ rest.drop 1

/-- Check an explicit PRA proof and assign it to the first goal. The proof must have no open
proof metavariables; its numerical and predicate arguments may use the goal's inference state. -/
def close (proof : Metavariable.Proof) : TacticM Unit := do
  let context ← read
  let goal ← mainGoal
  context.assign goal (← context.check goal proof (← context.target goal))
  modify (·.drop 1)

/-- Reduce the first goal to `premises`. `rule` must be an explicit proof, without open proof
metavariables, of the implication from `premises`, in order, to the goal's target. The rule is
checked, each premise becomes a new leading goal in the first goal's context, and the first goal
is assigned `rule` applied to the new goals. -/
def applyProof (rule : Metavariable.Proof) (premises : List Metavariable.Predicate) :
    TacticM Unit := do
  let context ← read
  let goal ← mainGoal
  let mut proof ← context.check goal rule (premises.foldr .imp (← context.target goal))
  let mut goals := #[]
  for premise in premises do
    let (new, hole) ← context.openGoal goal premise []
    proof := .impElim proof hole
    goals := goals.push new
  context.assign goal proof
  modify fun rest => goals.toList ++ rest.drop 1

/-- Continue the first goal under the local numerical definition `name := value`. The new goal
has the same target, and its context shows `name` in place of `value`. `ref` is the identifier in
the source that introduces `name`, when there is one; editor information is attached to it. -/
def define (name : Name) (value : Metavariable.Term) (ref : Syntax := .missing) :
    TacticM Unit := do
  let context ← read
  let goal ← mainGoal
  let (new, hole) ← context.openGoal goal (← context.target goal) [.definition name value ref]
  context.assign goal (.letTerm name value hole)
  modify fun rest => new :: rest.drop 1

/-- Give the local numerical definition `name` the new value `value` in the first goal. The goal
display lists `name` once, with the new value. -/
def redefine (name : Name) (value : Metavariable.Term) : TacticM Unit := do
  let context ← read
  let goal ← mainGoal
  let (new, hole) ← context.openGoal goal (← context.target goal) [.redefinition name value]
  context.assign goal (.letTerm name value hole)
  modify fun rest => new :: rest.drop 1

/-- Give existing local bindings a fresh name, preserving their values and context indices. -/
def rename (oldName newName : Name) : TacticM Unit := do
  let context ← read
  let goal ← mainGoal
  let (new, hole) ← context.openGoal goal (← context.target goal) [.renaming oldName newName]
  context.assign goal hole
  modify fun rest => new :: rest.drop 1

/-- Continue the first goal under the hypothesis `name : type`, which `proof` proves. `proof` must
be an explicit proof without open proof metavariables; it is checked against `type`. `ref` is the
identifier in the source that introduces `name`, when there is one. -/
def assert (name : Name) (type : Metavariable.Predicate) (proof : Metavariable.Proof)
    (ref : Syntax := .missing) : TacticM Unit := do
  let context ← read
  let goal ← mainGoal
  let proof ← context.check goal proof type
  let (new, hole) ← context.openGoal goal (← context.target goal) [.hypothesis name type ref]
  context.assign goal (.letE name type proof hole)
  modify fun rest => new :: rest.drop 1

/-- Replace the hypothesis at `index` by `type`, preserving its name and position. `proof` is
checked against `type` in the original context and must have no open proof metavariables.
The continuation can use the replacement and the other hypotheses. -/
def replaceHypothesis (index : Nat) (type : Metavariable.Predicate) (proof : Metavariable.Proof)
    (ref : Syntax := .missing) : TacticM Unit := do
  let context ← read
  let goal ← mainGoal
  let some name := (← getGoal).names.proofs[index]?
    | throwError "unknown PRA hypothesis"
  let proof ← context.check goal proof type
  let (new, hole) ← context.openGoal goal (← context.target goal) [.replacement index type ref]
  -- The new let binds the replacement at zero; the other hypotheses refer to the outer context.
  let hole := hole.subst .bvar (fun i => .hyp (if i == index then 0 else i + 1))
  context.assign goal (.letE name type proof hole)
  modify fun rest => new :: rest.drop 1

/-- Remove the hypothesis at `index` from the first goal's context. The continuation proof is
weakened back into the original context when it fills the goal. -/
def clearHypothesis (index : Nat) : TacticM Unit := do
  let context ← read
  let goal ← mainGoal
  let (new, hole) ← context.openGoal goal (← context.target goal) [.removal index]
  let hole := hole.subst .bvar (fun i => .hyp (if i < index then i else i + 1))
  context.assign goal hole
  modify fun rest => new :: rest.drop 1

/-- Replace the target `T` of the first goal by `type → T`, using `proof` of `type`. `proof` must
be an explicit proof without open proof metavariables; it is checked against `type`. -/
def assertPremise (type : Metavariable.Predicate) (proof : Metavariable.Proof) :
    TacticM Unit := do
  let context ← read
  let goal ← mainGoal
  let proof ← context.check goal proof type
  let (new, hole) ← context.openGoal goal (.imp type (← context.target goal)) []
  context.assign goal (.impElim hole proof)
  modify fun rest => new :: rest.drop 1

/-- Replace the target of the first goal by `type`, which must be definitionally equal to it. -/
def change (type : Metavariable.Predicate) : TacticM Unit := do
  let context ← read
  let goal ← mainGoal
  -- The identity on `type` proves `type → target` exactly when the two statements agree.
  discard <| context.check goal (.impIntro `h type (.hyp 0))
    (.imp type (← context.target goal))
  let (new, hole) ← context.openGoal goal type []
  context.assign goal (.ascribe type hole)
  modify fun rest => new :: rest.drop 1

/-- Prove `type` in the first goal's context by running `tactic` on a new goal, and return the
finished proof. The current goals are unchanged. Goals that `tactic` leaves open are reported as
unsolved at `ref`. -/
def prove (type : Metavariable.Predicate) (ref : Syntax) (tactic : TacticM Unit) :
    TacticM Metavariable.Proof := do
  let context ← read
  context.prove (← mainGoal) type ref fun goal => do
    let (_, goals) ← (tactic.run context).run [goal]
    return goals

/-- Create a numerical unknown in the first goal's context for the elaborator to infer. -/
def unknownTerm : TacticM Metavariable.Term := do
  (← read).unknownTerm (← mainGoal)

/-- Elaborate a proof in the first goal's context and constrain its type to `expected`, which may
contain unknowns. Returns the proof and its type with the inferred arguments filled in. -/
def elaborateProofAs (value : TSyntax `praExpr) (expected : Metavariable.Predicate) :
    TacticM (Metavariable.Proof × Metavariable.Predicate) := do
  (← read).proof (← mainGoal) value (some expected)

/-- Infer a proof expression in the first goal's context. An optional expected type supplies
constraints for its arguments; the result is the inferred type with those arguments resolved. -/
def infer (proof : TSyntax `praExpr) (expected : Option (TSyntax `praExpr) := none) :
    TacticM Metavariable.Predicate := do
  (← read).infer (← mainGoal) proof (expected.map (·.raw))

/-- Elaborate a numerical expression in the current goal's context. -/
def elaborateTerm (value : TSyntax `praExpr) (arity : Nat := 0) : TacticM Metavariable.Term := do
  (← read).term (← mainGoal) value arity

/-- Elaborate a proof together with its type in the current goal's context. -/
def elaborateProof (value : TSyntax `praExpr) :
    TacticM (Metavariable.Proof × Metavariable.Predicate) := do
  (← read).proof (← mainGoal) value none

/-- Save the complete elaboration session and the current goal list for backtracking. -/
def saveState : TacticM (TacticM Unit) := do
  let goals ← get
  let restore ← (← read).save
  return do restore; set goals

/-- Record goals before and after `action` at `stx`, with nested editor information. -/
def withTacticInfo (stx : Syntax) (action : TacticM α) : TacticM α := do
  unless ← editorInfoEnabled do return ← action
  unless (stx.getRange? (canonicalOnly := true)).isSome do return ← action
  let info ← (← read).snapshot (← get) stx
  withInfoTreeContext action fun children => do
    let after ← (← read).snapshot (← get) stx
    let info := match info, after with
      | .ofTacticInfo before, .ofTacticInfo after =>
        .ofTacticInfo { before with mctxAfter := after.mctxAfter, goalsAfter := after.goalsAfter }
      | _, _ => info
    return .node info children

/-- Run a registered Lean tactic program. Macros can expand custom syntax into other tactics. -/
partial def evalTactic (stx : Syntax) : TacticM Unit := withRef stx do
  withIncRecDepth <| withTacticInfo stx (dispatch stx)
where
  dispatch (stx : Syntax) : TacticM Unit := do
    let entries := tacticElabAttribute.getEntries (← getEnv) stx.getKind
    for entry in entries do
      let restore ← saveState
      try
        entry.value stx
        return
      catch ex =>
        if ex.isInterrupt then throw ex
        let unsupported := match ex with
          | .internal id _ => id == unsupportedSyntaxExceptionId
          | _ => false
        let info ← getInfoState
        restore
        unless unsupported do
          -- Keep the failed tactic's intermediate goals; enclosing alternatives can roll them back.
          modifyInfoState fun _ => info
          throw ex
    if let some expanded ← liftMacroM (expandMacro? stx) then
      evalTactic expanded
    else throwErrorAt stx "no PRA tactic elaborator for `{stx.getKind}`"

/-- Evaluate a parsed tactic sequence in source order. -/
def evalTacticSeq (stx : TSyntax ``praTacticSeq) : TacticM Unit := do
  for tactic in stx.raw[0].getSepArgs do evalTactic tactic

end Tactic
end LeanPRA.Surface
