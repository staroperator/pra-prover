module

public import LeanPRA.Library.Computability.Computation

/-!
# Primitive-recursive functions

A function is primitive recursive when some program code computes it, witnessed by a valid
computation trees. This module defines that notion on top of the computation trees and proves
closure properties for basic functions and combinations.

- `Primrec.Evaluates e x y` says that there is a valid computation of code `e` that gives output `y`
  on the input `x`.
- `Primrec.Encodes f e` says that code `e` encodes the function `f`, that it evaluates to `f x` for
  every input `x`.
- `Primrec f` asserts that some code encodes `f`.
- `Primrec.ComputedBy f e tr` says that `e` encodes the function `f` for all inputs, and that fact
  is witnessed by a trace builder `tr`. `tr` is the Skolem function of `Primrec.Encodes f e`.
-/

@[expose] public section

pra

namespace Primrec

/-! ## Encoded functions -/

/-- Code `e` evaluates at input `x` to output `y` if it has a checked computation tree. -/
def Evaluates : Nat → Nat → Nat → Prop := fun e x y =>
  ∃ t, Computation.Evaluates e x y t

/-- Code `e` encodes `f` if every input has a checked computation with output `f x`. -/
def Encodes (f : Nat → Nat) (e : Nat) : Prop :=
  ∀ x, Evaluates e x (f x)

end Primrec

/-- A function is primitive recursive if some primitive-recursive program encodes it. -/
def Primrec (f : Nat → Nat) : Prop := ∃ e, Primrec.Encodes f e

/-- `Primrec.ComputedBy f e tr` says that for each input `x`, `tr x` is a checked computation
tree for code `e` with result `f x`. Thus `tr` chooses the tree whose existence is asserted by
`Primrec.Encodes f e`. Quantifier-free induction can use this explicit builder to assemble
computation trees, for example when a recursion calls the function encoded by `e`.
The command `derive_primrec` supplies a builder and its correctness theorem. -/
def Primrec.ComputedBy (f : Nat → Nat) (e : Nat) (tr : Nat → Nat) : Prop :=
  ∀ x, Primrec.Computation.Evaluates e x (f x) (tr x)

namespace Primrec.Computation

theorem computedBy_binary (f : Nat → Nat → Nat) (a b ta tb tf : Nat → Nat)
    (c l r : Nat) :
    ComputedBy (fun p => f (unpairLeft p) (unpairRight p)) c tf →
    ComputedBy a l ta → ComputedBy b r tb →
    ComputedBy (fun x => f (a x) (b x)) (Code.comp c (Code.pair l r))
      (binaryTrace f a b ta tb tf c l r) := by
  intro hf ha hb x
  have value := hf (pair (a x) (b x))
  rw [unpairLeft_pair, unpairRight_pair] at value
  exact evaluates_comp c (Code.pair l r) x (pair (a x) (b x)) (f (a x) (b x)) _ _
    (evaluates_pairTrace a b ta tb l r ha hb x) value

end Primrec.Computation

/-- A checked trace builder gives an encoding certificate. -/
theorem Primrec.encodes_of_computedBy (f tr : Nat → Nat) (e : Nat) :
    Primrec.ComputedBy f e tr → Primrec.Encodes f e :=
  fun h x => (tr x, h x)

/-- An encoding witnesses primitive recursiveness. -/
theorem Primrec.of_encodes (f : Nat → Nat) (e : Nat) :
    Primrec.Encodes f e → Primrec f :=
  fun h => (e, h)

/-- A program with a checked trace builder witnesses primitive recursiveness. -/
theorem Primrec.of_computedBy (f tr : Nat → Nat) :
    ∀ e, Primrec.ComputedBy f e tr → Primrec f :=
  fun e h => Primrec.of_encodes f e (Primrec.encodes_of_computedBy f tr e h)

/-- A primitive-recursive program with an explicit correct computation for every input witnesses
primitive recursiveness. The tree builder is a numerical function in the PRA language. -/
theorem Primrec.of_evaluates (f tr : Nat → Nat) : ∀ e,
    (∀ x, Primrec.Computation.Evaluates e x (f x) (tr x)) → Primrec f := by
  intro e h
  exists e
  intro x
  exact (tr x, h x)

/-! ## Closure properties -/

theorem Primrec.congr (f g : Nat → Nat) :
    (∀ x, f x = g x) → Primrec f → Primrec g := by
  rintro h (e, he)
  exists e
  intro x
  have hx := he x
  rw [h x] at hx
  exact hx

theorem Primrec.const : ∀ n, Primrec (fun _ => n) := by
  intro n
  exact Primrec.of_evaluates (fun _ => n) (Primrec.Computation.constTrace n)
    (Primrec.Code.const n)
    (Primrec.Computation.evaluates_const n)

theorem Primrec.id : Primrec (fun x => x) :=
  Primrec.of_evaluates (fun x => x) Primrec.Computation.idTrace Primrec.Code.id
    Primrec.Computation.evaluates_id

theorem Primrec.succ : Primrec S :=
  Primrec.of_evaluates S (fun x => Primrec.Computation.node Primrec.Code.succ x (S x) 0 0)
    Primrec.Code.succ Primrec.Computation.evaluates_succ

theorem Primrec.comp (f g : Nat → Nat) :
    Primrec f → Primrec g → Primrec (fun x => f (g x)) := by
  rintro (a, ha) (b, hb)
  exists Primrec.Code.comp a b
  intro x
  rcases hb x with (p, hp)
  rcases ha (g x) with (q, hq)
  exists Primrec.Computation.node (Primrec.Code.comp a b) x (f (g x)) p q
  exact Primrec.Computation.evaluates_comp a b x (g x) (f (g x)) p q hp hq

theorem Primrec.pair (f g : Nat → Nat) :
    Primrec f → Primrec g → Primrec (fun x => pair (f x) (g x)) := by
  rintro (a, ha) (b, hb)
  exists Primrec.Code.pair a b
  intro x
  rcases ha x with (p, hp)
  rcases hb x with (q, hq)
  exists Primrec.Computation.node (Primrec.Code.pair a b) x (pair (f x) (g x)) p q
  exact Primrec.Computation.evaluates_pair a b x (f x) (g x) p q hp hq

end
