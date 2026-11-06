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

We further formalize the metatheory of the core language and the correctness of the core checker.
*The metatheory formalization, however, assumes Lean's axioms which are much stronger than PRA.*

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

This language further supports tactics as programs written in Lean.

```lean4
pra

theorem add_left_comm : ∀ x y z, x + (y + z) = y + (x + z) := by
  intro x y z
  rw [← add_assoc, ← add_assoc, add_comm x y]

end
```

## Structure

- [`LeanPRA/Core`](LeanPRA/Core/) contains the syntax and executable checker for the core language.
- [`LeanPRA/Surface`](LeanPRA/Surface/) contains the surface language, including parsing,
  elaboration, printing, and editor support.
- [`LeanPRA/Library`](LeanPRA/Library/) is the library for the PRA language.
- [`LeanPRA/Metatheory`](LeanPRA/Metatheory/) contains the metatheory of the PRA language.
