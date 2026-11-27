module

public meta import PRAProver.Core.Syntax

/-!
# Name markers

A name marker attaches a name to a numerical term without changing its meaning. The marked form
of a term `t` is `let h := t; h`. The Core checker unfolds a `let` when it compares two terms, so
a marked term can stand wherever `t` can, and it stays in a goal while a proof is built.

A tactic library uses markers to keep names inside a goal. A later tactic and the goal display
read the names back from the goal itself, so they are also present in goals that another tactic
produced, for example the cases of an induction. A library for an object logic can write each
local assumption of a sequent as a marked formula code; the name of the marker is then the name
of the assumption.

- `markName h t` builds the marked term `let h := t; h`.
- `markedName? t` returns the name and the term when `t` is a marked term.
- `unmarked t` removes the markers at the head of `t`.
-/

public meta section

namespace PRAProver.Library.Tactic

open PRAProver.Core

/-- The term `t` carrying the name `name`, written `let name := t; name`. -/
def markName (name : Lean.Name) (t : Term) : Term := .letE name t (.bvar 0)

/-- The name and the term of a marked term. -/
def markedName? : Term → Option (Lean.Name × Term)
  | .letE name t (.bvar 0) => some (name, t)
  | _ => none

/-- Remove the name markers at the head of a term. -/
def unmarked : Term → Term
  | .letE _ t (.bvar 0) => unmarked t
  | t => t

end PRAProver.Library.Tactic
