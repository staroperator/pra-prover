module

public meta import LeanPRA.Library.Computability.Tactic

/-!
# Primitive-recursive functions

Basic numerical functions and operations that preserve primitive recursiveness.

- `Primrec.congr` transfers primitive recursiveness along pointwise equality.
- `Primrec.const`, `Primrec.id`, `Primrec.succ`, `Primrec.unpairLeft`, and `Primrec.unpairRight`
  give the basic functions.
- `Primrec.comp` and `Primrec.pair` close the class under composition and pairing.
- `Primrec.eqb_pair` computes equality on a paired input; `Primrec.eqb` compares the outputs
  of two primitive-recursive functions.
-/

@[expose] public section

pra

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

theorem Primrec.unpairLeft : Primrec unpairLeft :=
  Primrec.of_evaluates unpairLeft
    (fun x => Primrec.Computation.node Primrec.Code.left x (unpairLeft x) 0 0)
    Primrec.Code.left Primrec.Computation.evaluates_left

theorem Primrec.unpairRight : Primrec unpairRight :=
  Primrec.of_evaluates unpairRight
    (fun x => Primrec.Computation.node Primrec.Code.right x (unpairRight x) 0 0)
    Primrec.Code.right Primrec.Computation.evaluates_right

theorem Primrec.comp (f g : Nat → Nat) :
    Primrec f → Primrec g → Primrec (fun x => f (g x)) := by
  rintro (a, ha) (b, hb)
  exists Primrec.Code.comp a b
  intro x
  exact Primrec.computes_comp a b x (g x) (f (g x)) (hb x) (ha (g x))

theorem Primrec.pair (f g : Nat → Nat) :
    Primrec f → Primrec g → Primrec (fun x => pair (f x) (g x)) := by
  rintro (a, ha) (b, hb)
  exists Primrec.Code.pair a b
  intro x
  exact Primrec.computes_pair a b x (f x) (g x) (ha x) (hb x)

derive_primrec (fun x => eqb (unpairLeft x) (unpairRight x)) as Primrec.eqb_pair

theorem Primrec.eqb (f g : Nat → Nat) :
    Primrec f → Primrec g → Primrec (fun x => eqb (f x) (g x)) := by
  intro hf hg
  apply Primrec.congr (fun x => eqb (unpairLeft (pair (f x) (g x)))
    (unpairRight (pair (f x) (g x)))) (fun x => eqb (f x) (g x))
  · intro x
    rw [unpairLeft_pair, unpairRight_pair]
  · exact Primrec.comp (fun x => eqb (unpairLeft x) (unpairRight x))
      (fun x => pair (f x) (g x)) Primrec.eqb_pair (Primrec.pair f g hf hg)

end
