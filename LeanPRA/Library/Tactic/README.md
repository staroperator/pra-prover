# PRA tactics

Tactic modules in `LeanPRA/Library/Tactic` provide interactive proof construction and witness
compilation for the PRA language. Tactics are host Lean programs that fill contextual PRA proof
metavariables inside `by ...` expressions. Every finished proof and generated helper declaration is
checked by the PRA core checker before it enters the environment.

Import `LeanPRA.Library.Tactic` for the general proof tactics, and import
`LeanPRA.Library.Tactic.SigmaInduction` or `LeanPRA.Library.Tactic.Witnessing` when a module uses
existential induction or witness compilation.

## Module organization

| Module | Responsibility |
| --- | --- |
| `Combinators` | Sequencing, goal focusing, multi-goal application, and backtracking. |
| `Logic` | Introductions, destructuring patterns, logical connectives, and rule application. |
| `Rewrite` | Numerical equality rewriting and definition unfolding in goals and hypotheses. |
| `Induction` | Quantifier-free induction, excluded-middle case splits, local bindings, and target conversion. |
| `SigmaInduction` | Induction for existential goals with quantifier-free bodies via witness compilation. |
| `Witnessing` | Compilation of constructive existential proofs into primitive-recursive functions and specifications. |
| `Construction` | Shared metaprogramming helpers for building terms, equality proofs, inequalities, and checked declarations. |
| `Marker` | Name markers (`let h := t; h`) that attach local names to numerical terms inside goals. |

## Combinators and goal control

Tactics in a `by` block separated by newlines or `;` run in sequence on the first open goal.
Failed tactic steps restore proof assignments, constraint state, diagnostics, and editor snapshots.

| Tactic | Action |
| --- | --- |
| `· seq` or `{ seq }` | Focus on the first goal and require `seq` to close it completely. |
| `(seq)` | Group a tactic sequence as a single step. |
| `a <;> b` | Run `a` on the first goal, then run `b` on every goal produced by `a`. |
| `all_goals seq` | Run `seq` on each open goal in order. |
| `first \| s₁ \| s₂` | Run the first alternative sequence that succeeds, rolling back failed attempts. |
| `try seq` | Run `seq` and keep the original state if it fails. |
| `repeat seq` | Repeat `seq` until it fails, solves all goals, or leaves the goal list unchanged (bounded by the maximum depth). |
| `skip` | Leave the goals unchanged. |
| `fail "msg"` | Fail immediately with the error message `"msg"`. |

```lean
theorem and_comm : ∀ x y, x = 0 ∧ y = 0 → y = 0 ∧ x = 0 := by
  rintro x y (hx, hy)
  constructor <;> assumption
```

## Logical tactics

Logical tactics build PRA proof terms through the Surface refinement interface. In `refine`,
explicit `?_` and named proof holes become new goals in source order, while `_` in a numerical or
predicate argument position is inferred from elaboration constraints.

| Tactic | Action |
| --- | --- |
| `exact e` | Close the first goal with `e`, requiring all proof holes to be solved. |
| `refine e` | Elaborate `e` against the first goal and replace it with any `?_` holes in `e`. |
| `intro x₁ x₂ ...` | Introduce universal variables and implication premises. Bare `intro` chooses a fresh name `h`. |
| `rintro p₁ p₂ ...` | Introduce and destructure arguments using case patterns. |
| `rcases e with p` | Destructure the proof expression `e` using the pattern `p`. |
| `apply e` | Supply inferred `_` arguments and `?_` proof subgoals until the conclusion of `e` matches the goal. Prefix `@` to supply implicit universal arguments explicitly. |
| `assumption` | Close the goal with the first matching hypothesis in the local context. |
| `rfl` | Close an equality goal `a = b` by reflexivity when `a` and `b` are definitionally equal. |
| `constructor` | Prove `True` with `()`, or split a conjunction `A ∧ B` into two goals `A` and `B`. |
| `left`, `right` | Reduce a disjunction goal `A ∨ B` to `A` or `B`. |
| `exists t₁, t₂, ...` | Provide one or more existential witnesses in order, leaving the instantiated body as the new goal. |
| `exfalso` | Replace the current goal target with `False`. |
| `by_contra h` | Apply double-negation elimination (`dne`) to a goal `P`, introducing `h : ¬ P` with target `False`. Bare `by_contra` chooses a fresh name. |

```lean
theorem succ_pred : ∀ n, ¬ n = 0 → S (pred n) = n := by
  intro n hn
  rcases zero_or_succ_pred n with hz | hs
  · exfalso
    exact hn hz
  · exact eq_symm hs
```

### Patterns in `rintro` and `rcases`

`rintro` and `rcases` share the pattern grammar `praCasesPattern`:

- An identifier `x` binds a numerical variable or proof hypothesis.
- An underscore `_` ignores the bound value.
- A tuple pattern `(p₁, p₂, ...)` destructures conjunctions (`∧`), equivalences (`↔`), or
  existential pairs (`∃ x, P x`).
- A disjunction pattern `p₁ | p₂` splits a disjunction (`∨`) into two goals. In `rintro`, wrap
  top-level disjunction patterns in parentheses, as in `rintro (hp | hq)`.

`rcases h with p` removes the local hypothesis `h` from the resulting branches. Its name can be
reused in the pattern. Ignored components and intermediate tuple proofs are removed as well.

Patterns can nest arbitrarily, such as `rintro n ((hp, hq) | hr)` or `rcases h with (x, hx | hy)`.
When `rintro` has patterns after a disjunction split, those remaining patterns are introduced in
each resulting branch in depth-first, left-to-right order.

## Equality rewriting and unfolding

`rw [r₁, r₂, ...]` applies a sequence of rewrite rules to the goal, then attempts to close a
resulting equality goal by beta-only reflexivity. Append `at h` to rewrite inside the local
hypothesis `h`, replacing `h` in place while keeping its name and context position.

```lean
theorem add_right_comm : ∀ x y z, x + y + z = x + z + y := by
  intro x y z
  rw [add_assoc, add_assoc, add_comm y z]
```

Each rule in the list has one of three forms:

- `e`: rewrite left-to-right with the numerical equality proof `e`. If `e` is universally
  quantified, the tactic inspects numerical subterms of the target and instantiates `e` from the
  first subterm that matches its left-hand side.
- `← e`: rewrite right-to-left with `e`, matching against its right-hand side and replacing
  matches with its left-hand side.
- `f`: when `f` resolves to a global function or predicate definition (with no local binding of the
  same name), unfold the first matching application of `f` and all other occurrences of that same
  application, reducing exposed lambda applications and head `let` bindings.

Equality matching compares subterms up to beta reduction and ignores binder names. Definitions,
`let` bindings, primitive-recursion equations, and eta expansion keep their written form during
matching so that individual steps remain predictable. Once a rule instance `a = b` is chosen, all
occurrences of `a` in the target (including occurrences beneath binders) are replaced by `b` using
equality substitution (`eq_subst`) and symmetry (`eq_symm`). Every inferred argument of the rule
must be well-scoped in the goal's context; introduce quantified variables with `intro` before
rewriting subterms that depend on them.

Definition unfolding only works forward. To fold an expression back into a definition, rewrite with
an equality theorem (for example, `rw [← add_succ]`).

## Induction and local bindings

The induction module provides tactics for quantifier-free induction, classical case splits, local
definitions, and definitional target changes:

| Tactic | Action |
| --- | --- |
| `induction n with k ih` | Refine the goal by induction on `n`, producing a base goal for `0` and a step goal with predecessor `k` and induction hypothesis `ih`. |
| `induction n with \| zero => s₁ \| succ k ih => s₂` | Run `s₁` on the base goal and `s₂` on the step goal, requiring both branches to finish. |
| `by_cases h : P` | Split the goal into two branches using `lem P`, binding `h : P` in the first branch and `h : ¬ P` in the second. |
| `have h : P := e`, `have h := e` | Add a proved local hypothesis `h` to the context for the remainder of the goal. |
| `let x : T := v`, `let x := v` | Define a local number, function, predicate, or proof `x` in the context. Replace `x` with `_` for an anonymous check. |
| `change P` | Replace the goal target with `P`, checking that `P` is definitionally equal to the current target. |

```lean
theorem sub_self : ∀ x, x - x = 0 := by
  intro x
  induction x with k ih
  · rfl
  · rw [succ_sub_succ, ih]
```

Both `induction` forms elaborate to the primitive `induction` proof constructor, which requires the
inferred motive `fun n => Goal(n)` to be quantifier-free (`QFProp`). If a local hypothesis depends
on the induction variable `n`, leave that hypothesis as an implication in the goal target until
after calling `induction` so that it becomes part of the induction motive.

## Existential induction and witness compilation

When a goal has the existential form `∃ w, R n w` for a quantifier-free relation `R`,
`sigma_induction` proves it by compiling constructive branch proofs into primitive-recursive witness
functions:

```lean
sigma_induction n with
| zero =>
  ...
| succ k ih =>
  ...
```

The bulleted form `sigma_induction n with k ih` followed by two `·` blocks is also accepted.

In `sigma_induction`:

- `n` must be a local numerical variable or declaration parameter, and the goal must reduce to an
  existential `∃ w, R n w` with a quantifier-free body.
- In the `zero` branch, `n` is bound to `0` and the goal is `∃ w, R 0 w`.
- In the `succ k ih` branch, `k` is the predecessor, `n` is bound to `S k`, `ih` has the
  existential type `∃ w, R k w`, and the goal is `∃ w, R (S k) w`.
- Both branches are proved with ordinary PRA tactics. Each branch must construct its witness from
  explicit existential introductions, local `let`/`have` bindings, existential eliminations
  (`rcases`), equality transport (`rw` or `eq_subst`), falsity elimination, or previously compiled
  theorems.
- The tactic compiles the base proof and step proof into numerical functions, combines them with
  `primrec`, proves the quantifier-free invariant `R n (witness n)` by primitive PRA induction, and
  closes the original existential goal.

### Sharing witnesses with `extract_witness`

Inside a `pra ... end` block, the command

```lean
extract_witness thm₁ thm₂ ...
```

compiles each named theorem `thm` into two checked PRA declarations:

- `thm.witness`: a function taking the theorem's universal numerical arguments and the witnesses of
  any existential premises.
- `thm.witness_correct`: a theorem proving that `thm.witness` satisfies the existential matrix
  whenever the premises hold. For example, a theorem of type
  `∀ x, (∃ u, Q x u) → ∃ v, R x v` produces `thm.witness : Nat → Nat → Nat` and
  `thm.witness_correct : ∀ x u, Q x u → R x (thm.witness x u)`.

When a `sigma_induction` branch or another compiled proof uses an existential theorem from the
current module, the compiler extracts `thm.witness` and `thm.witness_correct` automatically (or
unfolds the theorem in place when its witness is a single variable or function call and its proof
has at most 128 inference steps). To reuse a compiled witness across module imports without
unfolding the theorem in downstream modules, place `extract_witness thm` at the end of the module
that defines `thm`.

## Metaprogramming support

`Construction` and `Marker` provide building blocks for custom tactic modules:

- `numeral` and `numeralValue?` convert between Lean `Nat` values and PRA successor numerals.
- `applyDefinition`, `getAppFnArgs`, `applyTheorem`, and `projectTheorem` assemble and inspect Core
  applications and theorem instantiations.
- `mkEqSymm`, `mkEqTrans`, and `mkEqCongr` construct equality proofs from `eq_symm`, `eq_trans`,
  and `eq_congr`.
- `mapProof` and `shiftProof` traverse Core proof trees while tracking numerical and hypothesis
  binder depths.
- `proveArithmeticLe` proves numerical inequalities `a ≤ b` built from numerals, addition,
  multiplication, successor, and pairing.
- `sequenceCode` and `tupleCode` build Core terms for `Sequence` lists and nested `pair` tuples.
- `publishChecked` runs the Core declaration checker on a generated declaration (using common
  subterm sharing) and registers it with its source location.
- `markName`, `markedName?`, and `unmarked` wrap and inspect identity `let` bindings
  (`let h := t; h`) so tactics and custom goal printers can preserve user-chosen names inside
  numerical terms.
