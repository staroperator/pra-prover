module

public meta import LeanPRA.Library.Tactic.Logic

/-!
# Induction and local reasoning in PRA

Tactics for induction, case splits, local hypotheses, and goal conversion in the PRA language:

- `induction n with k ih` refines the goal by induction on `n`, producing the base goal for `0`
  and the step goal with variable `k` and induction hypothesis `ih`.
- `by_cases h : P` splits the goal on `lem P`, naming the assumption `h` in both branches.
- `have h : P := proof` and `have h := proof` bind a local proof `h` for the remaining goal.
- `change P` replaces the goal target with a definitionally equal formula `P`.

`induction` elaborates through the built-in `induction` proof form, which requires the inferred
motive to be quantifier-free (`QFProp`). Leave any hypothesis that depends on `n` in the goal
target before calling `induction` so that the motive includes it.
-/

public meta section

namespace LeanPRA.Library.Tactic

open Lean Elab LeanPRA.Surface LeanPRA.Surface.Tactic

syntax (name := inductionTac) "induction " praExpr " with " ident ident : praTactic
syntax (name := byCasesTac) "by_cases " ident " : " praExpr : praTactic
syntax (name := haveTypedTac) "have " ident " : " praExpr " := " praExpr : praTactic
syntax (name := haveTac) "have " ident " := " praExpr : praTactic
syntax (name := changeTac) "change " praExpr : praTactic

macro "induction" : praExpr => `(praExpr| $(mkIdent `induction):ident)

/-- Elaborate `induction`, `by_cases`, `have`, and `change` into PRA proof refinements. -/
@[pra_tactic inductionTac, pra_tactic byCasesTac, pra_tactic haveTypedTac,
  pra_tactic haveTac, pra_tactic changeTac]
def evalInduction : Tactic := fun stx => do
  match stx with
  | `(praTactic| induction $n:praExpr with $k:ident $ih:ident) =>
    Tactic.refine (← `(praExpr| induction ?_ (fun $k:ident $ih:ident => ?_) $n))
  | `(praTactic| by_cases $h:ident : $p:praExpr) =>
    Tactic.refine (← `(praExpr| or_elim (lem $p)
      (fun $h:ident => ?_) (fun $h:ident => ?_)))
  | `(praTactic| have $h:ident : $p:praExpr := $proof:praExpr) =>
    Tactic.refine (← `(praExpr| let $h:ident : $p := $proof; ?_))
  | `(praTactic| have $h:ident := $proof:praExpr) =>
    Tactic.refine (← `(praExpr| let $h:ident := $proof; ?_))
  | `(praTactic| change $p:praExpr) =>
    Tactic.refine (← `(praExpr| (?_ : $p)))
  | _ => throwUnsupportedSyntax

end LeanPRA.Library.Tactic
