module

public meta import LeanPRA.Library.Tactic.Logic

/-!
# Induction and local reasoning in PRA

Tactics for induction, case splits, local definitions, and goal conversion in the PRA language:

- `induction n with k ih` refines the goal by induction on `n`, producing the base goal for `0`
  and the step goal with variable `k` and induction hypothesis `ih`.
- `by_cases h : P` splits the goal on `lem P`, naming the assumption `h` in both branches.
- `have h : P := proof` and `have h := proof` bind a local proof `h` for the remaining goal.
- `let x := value` and `let x : T := value` define a local number, function, predicate, or proof.
  `let _ := value` and `let _ : T := value` check the value with an anonymous binder.
- `change P` replaces the goal target with a definitionally equal formula `P`.

`induction` elaborates through the built-in `induction` proof form, which requires the inferred
motive to be quantifier-free (`QFProp`). Leave any hypothesis that depends on `n` in the goal
target before calling `induction` so that the motive includes it.
-/

public meta section

namespace LeanPRA.Library.Tactic

open Lean Elab LeanPRA.Surface LeanPRA.Surface.Tactic

syntax (name := inductionTac) "induction " praExpr " with " ident ident : praTactic
syntax (name := structuredInductionTac) "induction " ident " with"
  ppLine "| " &"zero" "=>" ppIndent(colGt praTacticSeq)
  ppLine "| " &"succ" ident ident " =>" ppIndent(colGt praTacticSeq) : praTactic
syntax (name := byCasesTac) "by_cases " ident " : " praExpr : praTactic
syntax (name := haveTypedTac) "have " ident " : " praExpr " := " praExpr : praTactic
syntax (name := haveTac) "have " ident " := " praExpr : praTactic
syntax (name := letTypedTac) "let " ident " : " praExpr " := " praExpr : praTactic
syntax (name := letTac) "let " ident " := " praExpr : praTactic
syntax (name := letAnonymousTypedTac) "let " "_" " : " praExpr " := " praExpr : praTactic
syntax (name := letAnonymousTac) "let " "_" " := " praExpr : praTactic
syntax (name := changeTac) "change " praExpr : praTactic

/-- Elaborate induction, case splits, local bindings, and conversion into PRA proof refinements. -/
@[pra_tactic inductionTac, pra_tactic byCasesTac, pra_tactic haveTypedTac,
  pra_tactic haveTac, pra_tactic letTypedTac, pra_tactic letTac,
  pra_tactic letAnonymousTypedTac, pra_tactic letAnonymousTac, pra_tactic changeTac]
def evalInduction : Tactic := fun stx => do
  match stx with
  | `(praTactic| induction $n:praExpr with $k:ident $ih:ident) =>
    Tactic.refine (← `(praExpr| _root_.induction ?_ (fun $k:ident $ih:ident => ?_) $n))
  | `(praTactic| by_cases $h:ident : $p:praExpr) =>
    Tactic.refine (← `(praExpr| or_elim (lem $p)
      (fun $h:ident => ?_) (fun $h:ident => ?_)))
  | `(praTactic| have $h:ident : $p:praExpr := $proof:praExpr) =>
    Tactic.refine (← `(praExpr| let $h:ident : $p := $proof; ?_))
  | `(praTactic| have $h:ident := $proof:praExpr) =>
    Tactic.refine (← `(praExpr| let $h:ident := $proof; ?_))
  | `(praTactic| let $id:ident : $type:praExpr := $value:praExpr) =>
    Tactic.refine (← `(praExpr| let $id:ident : $type := $value; ?_))
  | `(praTactic| let $id:ident := $value:praExpr) =>
    Tactic.refine (← `(praExpr| let $id:ident := $value; ?_))
  | `(praTactic| let _ : $type:praExpr := $value:praExpr) =>
    let id := mkIdentFrom stx .anonymous
    Tactic.refine (← `(praExpr| let $id:ident : $type := $value; ?_))
  | `(praTactic| let _ := $value:praExpr) =>
    let id := mkIdentFrom stx .anonymous
    Tactic.refine (← `(praExpr| let $id:ident := $value; ?_))
  | `(praTactic| change $p:praExpr) =>
    Tactic.refine (← `(praExpr| (?_ : $p)))
  | _ => throwUnsupportedSyntax

/-- Elaborate named branches through the existing quantifier-free induction rule. -/
@[pra_tactic structuredInductionTac]
def evalStructuredInduction : Tactic := fun stx => do
  let `(praTactic| induction $n:ident with
    | zero => $base:praTacticSeq
    | succ $k:ident $ih:ident => $step:praTacticSeq) := stx | throwUnsupportedSyntax
  let rest := (← get).drop 1
  Tactic.refine (← `(praExpr| _root_.induction ?_ (fun $k:ident $ih:ident => ?_) $n:ident))
  let goals := (← get).take 2
  for (goal, branch) in goals.zip [base, step] do
    set [goal]
    Tactic.evalTacticSeq branch
    unless (← get).isEmpty do throwErrorAt branch "unfinished PRA induction branch"
  set rest

end LeanPRA.Library.Tactic
