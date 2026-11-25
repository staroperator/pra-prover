module

public import LeanPRA.Library.Computability.Primrec

/-!
# Programs supplied to the primitive recursive deriver

The deriver uses these program codes and correctness proofs when compiling tuple operations
and calling programs with a fixed input.
-/

pra

/-!
## Supplying a fixed input to a program

- `Primrec.Code.fixLeft e a` runs `e` on the pair of `a` and the ordinary input.
- `Primrec.Code.onRight e` runs a unary callback `e` on the second component of its input.
- `Primrec.Computation.computedBy_fixLeft` and `computedBy_onRight` construct the corresponding
  computation trees from the tree builder for `e`.
-/

namespace Primrec.Code

def fixLeft : Nat → Nat → Nat := fun e a => comp e (pair (const a) id)

def onRight : Nat → Nat := fun e => comp e right

end Primrec.Code

namespace Primrec.Computation

def fixLeftTrace (f tr : Nat → Nat) : Nat → Nat → Nat → Nat := fun e a x =>
  let p := _root_.pair a x;
  let inputTrace := node (Code.pair (Code.const a) Code.id) x p (constTrace a x) (idTrace x);
  node (Code.fixLeft e a) x (f p) inputTrace (tr p)

theorem computedBy_fixLeft (f tr : Nat → Nat) (e : Nat) :
    Primrec.ComputedBy f e tr → ∀ a x,
      Evaluates (Code.fixLeft e a) x (f (_root_.pair a x)) (fixLeftTrace f tr e a x) := by
  intro h a x
  exact evaluates_comp e (Code.pair (Code.const a) Code.id) x (_root_.pair a x)
    (f (_root_.pair a x)) _ _
    (evaluates_pair (Code.const a) Code.id x a x _ _ (evaluates_const a x) (evaluates_id x))
    (h (_root_.pair a x))

def onRightTrace (f tr : Nat → Nat) : Nat → Nat → Nat := fun e x =>
  let r := unpairRight x;
  node (Code.onRight e) x (f r) (node Code.right x r 0 0) (tr r)

theorem computedBy_onRight (f tr : Nat → Nat) (e : Nat) :
    Primrec.ComputedBy f e tr →
      Primrec.ComputedBy (fun x => f (unpairRight x)) (Code.onRight e) (onRightTrace f tr e) := by
  intro h x
  exact evaluates_comp e Code.right x (unpairRight x) _ _ _ (evaluates_right x) (h (unpairRight x))

end Primrec.Computation

end
