module

public import LeanPRA.Library.Logic

@[expose] public section

pra

def add : Nat → Nat → Nat :=
  fun x y => primrec x (fun _ z => S z) y

theorem add_zero : ∀ x, add x 0 = x :=
  fun x => rfl

theorem add_succ : ∀ x y, add x (S y) = S (add x y) :=
  fun x y => rfl

theorem zero_add : ∀ x, add 0 x = x :=
  fun x => induction rfl (fun x ih => eq_congr S (add 0 x) x ih) x

theorem succ_add : ∀ x y, add (S x) y = S (add x y) :=
  fun x y => induction rfl (fun y ih => eq_congr S (add (S x) y) (S (add x y)) ih) y

theorem add_comm : ∀ x y, add x y = add y x :=
  fun x y => induction (zero_add y) (fun x ih =>
    eq_trans (add (S x) y) (S (add x y)) (add y (S x)) (succ_add x y)
      (eq_congr S (add x y) (add y x) ih)) x

theorem add_assoc : ∀ x y z, add (add x y) z = add x (add y z) :=
  fun x y z => induction rfl (fun z ih => eq_congr S (add (add x y) z) (add x (add y z)) ih) z

end
