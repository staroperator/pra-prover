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
  fun x => induction rfl (fun x ih => eq_congr S ih) x

theorem succ_add : ∀ x y, add (S x) y = S (add x y) :=
  fun x y => induction rfl (fun y ih => eq_congr S ih) y

theorem add_comm : ∀ x y, add x y = add y x :=
  fun x y => induction (zero_add y) (fun x ih => eq_trans (succ_add x y) (eq_congr S ih)) x

theorem add_assoc : ∀ x y z, add (add x y) z = add x (add y z) :=
  fun x y z => induction rfl (fun z ih => eq_congr S ih) z

theorem add_left_comm : ∀ x y z, add x (add y z) = add y (add x z) :=
  fun x y z => eq_trans (eq_symm (add_assoc x y z))
    (eq_trans (eq_congr (fun a => add a z) (add_comm x y)) (add_assoc y x z))

theorem add_right_comm : ∀ x y z, add (add x y) z = add (add x z) y :=
  fun x y z => eq_trans (add_assoc x y z)
    (eq_trans (eq_congr (fun a => add x a) (add_comm y z)) (eq_symm (add_assoc x z y)))

theorem add_add_add_comm : ∀ a b c d, add (add a b) (add c d) = add (add a c) (add b d) :=
  fun a b c d => eq_trans (eq_symm (add_assoc (add a b) c d))
    (eq_trans (eq_congr (fun x => add x d) (add_right_comm a b c)) (add_assoc (add a c) b d))

def mul : Nat → Nat → Nat :=
  fun x y => primrec 0 (fun _ z => add z x) y

theorem mul_zero : ∀ x, mul x 0 = 0 :=
  fun x => rfl

theorem mul_succ : ∀ x y, mul x (S y) = add (mul x y) x :=
  fun x y => rfl

theorem mul_one : ∀ x, mul x 1 = x :=
  fun x => zero_add x

theorem zero_mul : ∀ x, mul 0 x = 0 :=
  fun x => induction rfl (fun x ih => (eq_congr (fun y => add y 0) ih)) x

theorem succ_mul : ∀ x y, mul (S x) y = add (mul x y) y :=
  fun x y => induction rfl (fun y ih =>
    eq_congr S (eq_trans (eq_congr (fun z => add z x) ih) (add_right_comm (mul x y) y x))) y

theorem one_mul : ∀ x, mul 1 x = x :=
  fun x => eq_trans (succ_mul 0 x)
    (eq_trans (eq_congr (fun y => add y x) (zero_mul x)) (zero_add x))

theorem mul_comm : ∀ x y, mul x y = mul y x :=
  fun x y => induction (zero_mul y)
    (fun x ih => eq_trans (succ_mul x y) (eq_congr (fun z => add z y) ih)) x

theorem mul_add_right_distrib : ∀ x y z, mul (add x y) z = add (mul x z) (mul y z) :=
  fun x y z => induction rfl
    (fun z ih => eq_trans (eq_congr (fun a => add a (add x y)) ih) (add_add_add_comm _ _ _ _)) z

theorem mul_add_left_distrib : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z) :=
  fun x y z => eq_trans (mul_comm _ _)
    (eq_trans (mul_add_right_distrib _ _ _) (eq_congr₂ add (mul_comm _ _) (mul_comm _ _)))

theorem mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z) :=
  fun x y z => induction rfl (fun z ih => eq_trans (eq_congr (fun a => add a (mul x y)) ih)
    (eq_symm (mul_add_left_distrib _ _ _))) z

theorem mul_left_comm : ∀ x y z, mul x (mul y z) = mul y (mul x z) :=
  fun x y z => eq_trans (eq_symm (mul_assoc x y z))
    (eq_trans (eq_congr (fun a => mul a z) (mul_comm x y)) (mul_assoc y x z))

theorem mul_right_comm : ∀ x y z, mul (mul x y) z = mul (mul x z) y :=
  fun x y z => eq_trans (mul_assoc x y z)
    (eq_trans (eq_congr (fun a => mul x a) (mul_comm y z)) (eq_symm (mul_assoc x z y)))

theorem mul_mul_mul_comm : ∀ a b c d, mul (mul a b) (mul c d) = mul (mul a c) (mul b d) :=
  fun a b c d => eq_trans (eq_symm (mul_assoc (mul a b) c d))
    (eq_trans (eq_congr (fun x => mul x d) (mul_right_comm a b c)) (mul_assoc (mul a c) b d))

def iter (f : Nat → Nat) : Nat → Nat → Nat :=
  fun n x => primrec x (fun _ y => f y) n

theorem iter_zero (f : Nat → Nat) : ∀ x, iter f 0 x = x :=
  fun x => rfl

theorem iter_succ (f : Nat → Nat) : ∀ n x, iter f (S n) x = f (iter f n x) :=
  fun n x => rfl

end
