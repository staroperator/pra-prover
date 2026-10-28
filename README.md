# Lean-PRA: A language for writing finistic proofs

This project aims to develop a language for writing proofs in *Primitive Recursive Arithmetic*
(PRA), a first-order theory of arithmetic that allows us to formalize a wide range of syntactic
proofs in logic (e.g. Gödel's incompleteness theorems), while being widely accepted as a *finistic
proof system*.

The PRA language is a DSL embedded in Lean. Its core is a MLTT-style lambda calculus with only first-order functions and first-order predicates of natural numbers. It has a surface syntax in Lean
with an elaborator reducing it to the core language, and every definition must be checked
independently by the core.

> [!WARNING]
> This repository is largely maintained by LLM. I will try my best to review the specifications and
> documents.

## Demo

One can use `pra` block to declare definitions and theorems in PRA language.

```lean4
pra

def add : Nat → Nat → Nat :=
  fun x y => primrec x (fun _ z => S z) y

theorem add_zero : ∀ x, add x 0 = x :=
  fun x => rfl

theorem zero_add : ∀ x, add 0 x = x :=
  fun x => induction rfl (fun y ih => eq_congr S ih) x

end
```

Here, `primrec base step n` is a replacement of `Nat.rec` to define recursive functions. Its motive
is restricted to be `Nat` so that it is limited to primitive recursion. `rfl` gives a proof of
`add x 0 = x`, which is a definitional equality. `induction base step x` gives a proof of `P x` from
`base : P 0` and `step : ∀ x, P x → P (S x)`, given that `P : Nat → QFProp` is a quantifier-free
predicate. Finally, `eq_congr (f : Nat → Nat) : ∀ {x y}, x = y → f x = f y` is a lemma of congurence.

A definition or theorem can take functions and predicates as parameters. However, the PRA language
does not allow any higher-order construction, including quantification over functions or predicates.
Such definitions and theorems should be understood as schemas and are required to be instantiated at
each use.

```lean4
pra

def iter (f : Nat → Nat) : Nat → Nat → Nat :=
  fun n x => primrec x (fun _ y => f y) n

theorem iter_zero (f : Nat → Nat) : ∀ x, iter f 0 x = x :=
  fun x => rfl

theorem iter_succ (f : Nat → Nat) : ∀ n x, iter f (S n) x = f (iter f n x) :=
  fun n x => rfl

end
```

This language further support tactics as programs written in Lean.

```lean4
pra

theorem add_left_comm : ∀ x y z, x + (y + z) = y + (x + z) := by
  intro x y z
  rw [← add_assoc, ← add_assoc, add_comm x y]

end
```
