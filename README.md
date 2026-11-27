# PRA-Prover: A proof assistant of Primitive Recursive Arithmetic (PRA)

Primitive Recursive Arithmetic (PRA) is a first-order theory of arithmetic that is widely accepted
for *finitism* reasoning. **PRA-Prover** is a proof assistant of PRA, based on a type-theoretic
formalization of PRA, written as a DSL embedded in Lean.

Although PRA-Prover is embedded in Lean, *you don't need to assume the consistency of Lean's axioms* or ZFC + $<\omega$ inaccessible cardinals. Lean is merely for metaprogramming and IDE support,
and all proofs that are checked in PRA-Prover are exported and re-checked by a smaller core checker
written in Rust.

> [!WARNING]
> This repository is largely maintained by LLM. Some features are quite unstable. I will try my best
> to review the specifications and documents.

## Main results

### Proof theory

Gödel's second incompleteness theorem for PRA:

```lean
theorem PRA.con_unprovable : Consistent PRA.language PRA.isAxiom →
    ¬ (PRA ⊢ con PRA.language PRA.isAxiom.code)
```

## Language features

The language of PRA-Prover is a type-theoretic formalization of PRA (we will call it the PRA
language in the rest).

### Syntax

**Types.** To make it faithful to the first-order formalization of PRA, the only base types in PRA
languages are `Nat` (natural numbers), `Prop` (propositions) and `QFProp` (a subtype of `Prop` for
quantifier-free propositions), and all types are first-order (i.e. `Nat → Nat → ⋯ → BaseType`).
There is no inductive types, higher-order function types or dependent types. Inductive concepts like
syntax trees have to be explicitly encoded into `Nat`.

**Definitions and theorems.** A definition's type can be either a *function* (`Nat → Nat → ⋯ → Nat`)
or a *predicate* (`Nat → Nat → ⋯ → QFProp/Prop`). They can be *parameterized* with first-order
parameters:
``` lean
def iter (f : Nat → Nat) : Nat → Nat → Nat
```
Every variable written in the left of `:` is a parameter. Such definitions and theorems should be
understood as schemas, not higher-order functions. Each parameter is a hole to be replaced by a
concrete term, and are required to be instantiated at each use.

**Functions.** The primitive consturctions for functions are:

- Zero `0 : Nat`,
- Successor `S : Nat → Nat`,
- Lambda abstraction `fun x => t` and application `t₁ t₂`,
- Primitive recursion `primrec base step : Nat → Nat` where `base : Nat` and
  `step : Nat → Nat → Nat`.

The motive of `primrec` is limited to `Nat` as primitive recursion.

**Predicates.** The primitive constructions for predicates are:

- First-order logic connectives, `True`, `False`, `∧`, `∨`, `→`,
- Equality `=`,
- First-order quantifiers `∀, ∃`.

Negation is `¬ p` derived as `p → False`, and bi-implication `p ↔ q` is derived as
`(p → q) ∧ (q → p)`. The type of a predicate is automatically *inferred* by its term. For example,
`p ∧ q : QFProp` if both `p : QFProp` and `q : QFProp`. Though, each definition has to choose either
`QFProp` or `Prop` explicitly.

**Proofs.** The primitive constructions for predicates are:

- Lambda abstruction `fun h => t` and application (modus ponens) `t₁ t₂`,
- Introduction and elimination of each logical connective, e.g. `and_intro : p → q → p ∧ q`,
- Equality axioms, `eq_refl : ∀ x, x = x` and `eq_subst P : ∀ x y, x = y → P x → P y` for
  `P : Prop`,
- *Law of excluded middle* `lem p : p ∨ ¬ p` for `p : Prop`,
- induction principle `induction P : motive 0 → (∀ x, motive x → motive (S x)) → ∀ x, motive x` for
  `P : Nat → QFProp`.

The law of excluded middle applies to both quantifier-free and quantified predicates. The induction
principle is limited to **quantifier-free predicates**.

### Demo

PRA-Prover is embedded in Lean. Use `pra` block to declare definitions and theorems in PRA language:

```lean4
pra

def add : Nat → Nat → Nat :=
  fun x y => primrec x (fun _ z => S z) y

theorem zero_add : ∀ x, add 0 x = x :=
  fun x => induction rfl (fun y ih => eq_congr S ih) x

end
```

This language further supports tactics as programs written in Lean. The library provides a large set
of tactics to use; see [`PRAProver/Library/Tactic/README.md`](PRAProver/Library/Tactic/README.md).

```lean4
pra

theorem add_left_comm : ∀ x y z, x + (y + z) = y + (x + z) := by
  intro x y z
  rw [← add_assoc, ← add_assoc, add_comm x y]

end
```

Metaprogramming allows us to create DSL for defining and proving in first-order logic. For example,
you can define a first-order theory of arithmetic, writing a proof in first-order logic, and they
are translated into natural number operations and proofs in PRA. See
[`PRAProver/Library/FOL/DSL/README.md`](PRAProver/Library/FOL/DSL/README.md) for more details.

```lean4
pra

fol_language Arith where
  constant zero
  function succ of 1
  function add of 2

fol_theory Base over Arith where
  axiom add_zero := ∀ x, add(x, zero) = x
  axiom add_succ := ∀ x y, add(x, succ(y)) = succ(add(x, y))

fol_theory AddTheory over Arith extends Base where
  axiom induction (p : formula of 1) :=
    p(zero) → (∀ x, p(x) → p(succ(x))) → ∀ x, p(x)

fol_def double over Arith (x : term) : term := add(x, x)

fol_theorem and_symm (p q : formula) : AddTheory ⊢ p ∧ q → q ∧ p := by
  pintro hpq
  pcases hpq with ⟨hp, hq⟩
  pconstructor
  · passumption
  · passumption

end
```

## Structure

- [`PRAProver/Core`](PRAProver/Core/) contains the core language syntax and its executable checker.
- [`PRAProver/Surface`](PRAProver/Surface/) contains the surface language, including parsing,
  elaboration, printing, and editor support.
- [`PRAProver/Library`](PRAProver/Library/) is the library for the PRA language.
  - [`Nat`](PRAProver/Library/Nat/) gives basic operations and theorems in PRA.
  - [`Tactic`](PRAProver/Library/Tactic/) provides tactics in PRA.
  - [`FOL`](PRAProver/Library/FOL/) formalizes first-order logic in PRA.
- [`PRAProver/Metatheory`](PRAProver/Metatheory/) contains the metatheory of the PRA language and
  first-order PRA; see [`PRAProver/Metatheory/README.md`](PRAProver/Metatheory/README.md) for the
  summary of results.
- [`PRAProver/Export`](PRAProver/Export/) is for exporting the specifications and proof scripts, and
  [`checker`](checker/) is an independent PRA checker written in Rust; see
  [`checker/README.md`](checker/README.md) for how to run it.
