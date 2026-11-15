# Lean-PRA: A language for writing finitistic proofs

This project aims to develop a language for writing proofs in *Primitive Recursive Arithmetic*
(PRA), a first-order theory of arithmetic that allows us to formalize a wide range of syntactic
proofs in logic (e.g. Gödel's incompleteness theorems), while being widely accepted as a *finitistic
proof system*.

The PRA language is a DSL embedded in Lean. Its core is a MLTT-style lambda calculus with only
first-order functions and first-order predicates over natural numbers. It has a surface syntax in
Lean with an elaborator reducing it to the core language, and every definition must be fully checked
by the core. *Note: you don't need to assume Lean's axioms are consistent. The role of Lean here is
for metaprogramming and an executable checker. Furthermore, it is possible to export PRA definitions
and re-check them in an independent checker.*

We further formalize the metatheory of the core language, the correctness of the core checker, and
translation from this core language into first-order PRA. *These metatheory formalizations, however,
assumes Lean's axioms which are much stronger than PRA.*

> [!WARNING]
> This repository is largely maintained by LLM. I will try my best to review the specifications and
> documents.

## Demo

One can use `pra` block to declare definitions and theorems in PRA language.

```lean4
pra

def add : Nat → Nat → Nat :=
  fun x y => primrec x (fun _ z => S z) y

theorem zero_add : ∀ x, add 0 x = x :=
  fun x => induction rfl (fun y ih => eq_congr S ih) x

end
```

Here, `primrec base step n` is a replacement of `Nat.rec` to define recursive functions. Its motive
is restricted to be `Nat` so that it is limited to primitive recursion. `induction base step x`
gives a proof of `P x` from `base : P 0` and `step : ∀ x, P x → P (S x)`, given that
`P : Nat → QFProp` is a quantifier-free predicate. The base case uses `rfl`, which gives a proof of
definitional equality `add 0 0 = 0`. The step case uses lemma
`eq_congr (f : Nat → Nat) : ∀ {x y}, x = y → f x = f y`.

A definition or theorem can take functions and predicates as parameters. However, the PRA language
does not allow any higher-order construction, including quantification over functions or predicates.
Such definitions and theorems should be understood as schemas and are required to be instantiated at
each use.

```lean4
pra

def iter (f : Nat → Nat) : Nat → Nat → Nat :=
  fun n x => primrec x (fun _ y => f y) n

end
```

This language further supports tactics as programs written in Lean. The library provides a large set
of tactics to use; see [`LeanPRA/Library/Tactic/README.md`](LeanPRA/Library/Tactic/README.md).

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
[`LeanPRA/Library/FOL/DSL/README.md`](LeanPRA/Library/FOL/DSL/README.md) for more details.

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

- [`LeanPRA/Core`](LeanPRA/Core/) contains the syntax and executable checker for the core language.
- [`LeanPRA/Surface`](LeanPRA/Surface/) contains the surface language, including parsing,
  elaboration, printing, and editor support.
- [`LeanPRA/Library`](LeanPRA/Library/) is the library for the PRA language.
  - [`Nat`](LeanPRA/Library/Nat/) gives basic operations and theorems in PRA.
  - [`Tactic`](LeanPRA/Library/Tactic/) provides tactics in PRA.
  - [`FOL`](LeanPRA/Library/FOL/) formalizes first-order logic in PRA.
- [`LeanPRA/Metatheory`](LeanPRA/Metatheory/) contains the metatheory of the PRA language and
  first-order PRA; see [`LeanPRA/Metatheory/README.md`](LeanPRA/Metatheory/README.md) for the
  summary of results.
- [`LeanPRA/Export`](LeanPRA/Export/) is for exporting the specifications and proof scripts, and
  [`checker`](checker/) is an independent PRA checker written in Rust; see
  [`checker/README.md`](checker/README.md) for how to run it.
