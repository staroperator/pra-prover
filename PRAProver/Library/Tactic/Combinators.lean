module

public meta import PRAProver.Surface.Tactic

/-!
# PRA tactic combinators

- Semicolons and newlines run tactics on the first remaining goal in sequence.
- `a <;> b` applies `b` to each goal produced by `a`.
- `all_goals`, `first`, `try`, and `repeat` control goal selection and backtracking.
- `·` and braces focus a proof on the first goal and require it to be solved.

Failed alternatives restore proof assignments, inference state, diagnostics, and editor snapshots.
-/

public meta section

namespace PRAProver.Library.Tactic

open Lean Elab PRAProver.Surface PRAProver.Surface.Tactic

syntax (name := skipTac) "skip" : praTactic
syntax (name := failTac) "fail" str : praTactic
syntax (name := groupTac) "(" praTacticSeq ")" : praTactic
syntax (name := focusTac) "· " praTacticSeq : praTactic
syntax (name := braceTac) "{" praTacticSeq "}" : praTactic
syntax (name := allGoalsTac) "all_goals" praTacticSeq : praTactic
syntax:1 (name := andThenTac) praTactic:2 " <;> " praTactic:1 : praTactic
syntax (name := firstTac) "first" (" | " praTacticSeq)+ : praTactic
syntax (name := tryTac) "try" praTacticSeq : praTactic
syntax (name := repeatTac) "repeat" praTacticSeq : praTactic

/-- Run an action on each current goal, preserving the order of resulting goals. -/
def onAllGoals (action : TacticM Unit) : TacticM Unit := do
  let goals ← get
  let mut result := []
  for goal in goals do
    set [goal]
    action
    result := result ++ (← get)
  set result

/-- Try an action, restoring the complete session if it fails. Interrupts propagate. -/
def attempt (action : TacticM Unit) : TacticM Bool := do
  let restore ← saveState
  try
    action
    return true
  catch ex =>
    if ex.isInterrupt then throw ex
    restore
    return false

/-- Run the basic goal-selection, sequencing, and backtracking combinators. -/
@[pra_tactic skipTac, pra_tactic failTac, pra_tactic groupTac, pra_tactic focusTac,
  pra_tactic braceTac, pra_tactic allGoalsTac, pra_tactic andThenTac, pra_tactic firstTac,
  pra_tactic tryTac, pra_tactic repeatTac]
def evalCombinator : Tactic := fun stx => do
  match stx with
  | `(praTactic| skip) => pure ()
  | `(praTactic| fail $message:str) => throwError message.getString
  | `(praTactic| ($seq:praTacticSeq)) => evalTacticSeq seq
  | `(praTactic| · $seq:praTacticSeq) | `(praTactic| { $seq:praTacticSeq }) =>
    let goal ← mainGoal
    let rest := (← get).drop 1
    set [goal]
    evalTacticSeq seq
    unless (← get).isEmpty do throwError "focused PRA proof has unsolved goals"
    set rest
  | `(praTactic| all_goals $seq:praTacticSeq) => onAllGoals (evalTacticSeq seq)
  | `(praTactic| $a:praTactic <;> $b:praTactic) =>
    let goal ← mainGoal
    let rest := (← get).drop 1
    set [goal]
    evalTactic a
    onAllGoals (evalTactic b)
    modify (· ++ rest)
  | `(praTactic| first $[| $seqs:praTacticSeq]*) =>
    for seq in seqs do
      if ← attempt (evalTacticSeq seq) then return
    throwError "all PRA tactic alternatives failed"
  | `(praTactic| try $seq:praTacticSeq) => discard <| attempt (evalTacticSeq seq)
  | `(praTactic| repeat $seq:praTacticSeq) =>
    if (← get).isEmpty then return
    let depth := (← getGoal).maxDepth
    for _ in [:depth] do
      if (← get).isEmpty then return
      let before ← get
      unless ← attempt (evalTacticSeq seq) do return
      if before == (← get) then return
    throwError "PRA tactic repetition limit exhausted"
  | _ => throwUnsupportedSyntax

end PRAProver.Library.Tactic
