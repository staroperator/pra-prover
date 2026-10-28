module

public import LeanPRA.Library.Tactic

@[expose] public section

pra

def add : Nat → Nat → Nat :=
  fun x y => primrec x (fun _ z => S z) y

infixl:65 " + " => add

theorem add_zero : ∀ x, x + 0 = x :=
  fun x => rfl

theorem add_succ : ∀ x y, x + S y = S (x + y) :=
  fun x y => rfl

theorem zero_add : ∀ x, 0 + x = x :=
  fun x => induction rfl (fun x ih => by rw [add_succ, ih]) x

theorem succ_add : ∀ x y, S x + y = S (x + y) :=
  fun x y => induction rfl (fun y ih => by rw [add_succ, ih, add_succ]) y

theorem add_comm : ∀ x y, x + y = y + x :=
  fun x y => induction (zero_add y) (fun x ih => by rw [succ_add, ih, add_succ]) x

theorem add_assoc : ∀ x y z, x + y + z = x + (y + z) :=
  fun x y z => induction rfl (fun z ih => by rw [add_succ, ih, add_succ, add_succ]) z

theorem add_left_comm : ∀ x y z, x + (y + z) = y + (x + z) := by
  intro x y z
  rw [← add_assoc, ← add_assoc, add_comm x y]

theorem add_right_comm : ∀ x y z, x + y + z = x + z + y := by
  intro x y z
  rw [add_assoc, add_assoc, add_comm y z]

theorem add_add_add_comm : ∀ a b c d, a + b + (c + d) = a + c + (b + d) := by
  intro a b c d
  rw [← add_assoc (a + b) c d, add_right_comm a b c, add_assoc (a + c) b d]

def mul : Nat → Nat → Nat :=
  fun x y => primrec 0 (fun _ z => add z x) y

infixl:70 " * " => mul

theorem mul_zero : ∀ x, x * 0 = 0 :=
  fun x => rfl

theorem mul_succ : ∀ x y, x * S y = x * y + x :=
  fun x y => rfl

theorem mul_one : ∀ x, x * 1 = x :=
  fun x => zero_add x

theorem zero_mul : ∀ x, 0 * x = 0 :=
  fun x => induction rfl (fun x ih => by rw [mul_succ, ih, add_zero]) x

theorem succ_mul : ∀ x y, S x * y = x * y + y :=
  fun x y => induction rfl (fun y ih => by
    rw [mul_succ, add_succ, ih, add_right_comm, mul_succ, add_succ]) y

theorem one_mul : ∀ x, 1 * x = x := by
  intro x
  rw [succ_mul, zero_mul, zero_add]

theorem mul_comm : ∀ x y, x * y = y * x :=
  fun x y => induction (zero_mul y) (fun x ih => by rw [succ_mul, ih, mul_succ]) x

theorem mul_add_right_distrib : ∀ x y z, (x + y) * z = x * z + y * z :=
  fun x y z => induction rfl (fun z ih => by
    rw [mul_succ, ih, add_add_add_comm, mul_succ, mul_succ]) z

theorem mul_add_left_distrib : ∀ x y z, x * (y + z) = x * y + x * z := by
  intro x y z
  rw [mul_comm, mul_add_right_distrib, mul_comm y x, mul_comm z x]

theorem mul_assoc : ∀ x y z, x * y * z = x * (y * z) :=
  fun x y z => induction rfl (fun z ih => by
    rw [mul_succ, ih, ← mul_add_left_distrib, mul_succ]) z

theorem mul_left_comm : ∀ x y z, x * (y * z) = y * (x * z) := by
  intro x y z
  rw [← mul_assoc, ← mul_assoc, mul_comm x y]

theorem mul_right_comm : ∀ x y z, x * y * z = x * z * y := by
  intro x y z
  rw [mul_assoc, mul_assoc, mul_comm y z]

theorem mul_mul_mul_comm : ∀ a b c d, a * b * (c * d) = a * c * (b * d) := by
  intro a b c d
  rw [← mul_assoc (a * b) c d, mul_right_comm a b c, mul_assoc (a * c) b d]

def iter (f : Nat → Nat) : Nat → Nat → Nat :=
  fun n x => primrec x (fun _ y => f y) n

theorem iter_zero (f : Nat → Nat) : ∀ x, iter f 0 x = x :=
  fun x => rfl

theorem iter_succ (f : Nat → Nat) : ∀ n x, iter f (S n) x = f (iter f n x) :=
  fun n x => rfl

end
