module

public meta import LeanPRA.Surface.IDE

/-!
# PRA tactic interface

Tactics are Lean programs that fill contextual PRA proof metavariables.

- `Goal` describes a goal in its saved local context.
- `Context` connects tactics to the PRA elaborator, including transactional state restoration.
- `TacticM` carries an ordered list of goals; `refine` replaces the first goal with explicit holes.
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

For example, `refine (_, ?_)` builds an existential proof whose witness can be inferred while
solving the new proof goal. A proof-position `_` reports an inference error suggesting `?_`.
-/

public meta section
namespace LeanPRA.Surface
open Lean Elab Command

declare_syntax_cat praTactic
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

/-- Operations supplied by the elaborator. `refine` returns explicit proof holes in source order.
`infer` can constrain an inferred type while returning its original form with arguments resolved.
`save` captures assignments, constraints, goals, diagnostics, and editor information. `snapshot`
builds a native infoview snapshot for the supplied goal list. -/
structure Context where
  inspect : GoalId → CommandElabM Goal
  refine : GoalId → Syntax → CommandElabM (List GoalId)
  close : GoalId → Metavariable.Proof → CommandElabM Unit
  infer : GoalId → Syntax → Option Syntax → CommandElabM Metavariable.Predicate
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
  (← read).close (← mainGoal) proof
  modify (·.drop 1)

/-- Infer a proof expression in the first goal's context. An optional expected type supplies
constraints for its arguments; the result is the inferred type with those arguments resolved. -/
def infer (proof : TSyntax `praExpr) (expected : Option (TSyntax `praExpr) := none) :
    TacticM Metavariable.Predicate := do
  (← read).infer (← mainGoal) proof (expected.map (·.raw))

/-- Save the complete elaboration session and the current goal list for backtracking. -/
def saveState : TacticM (TacticM Unit) := do
  let goals ← get
  let restore ← (← read).save
  return do restore; set goals

/-- Record goals before and after `action` at `stx`, with nested editor information. -/
def withTacticInfo (stx : Syntax) (action : TacticM α) : TacticM α := do
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
