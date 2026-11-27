module

public import PRAProver.Library.Nat.Defs

/-!
# Numerical Booleans in PRA

Boolean operations on `Nat` represent false as `0` and true as any positive number, and return
`0` or `1`:

- `IsBool b` states that `b` is `0` or `1`.
- `ite c x y` returns `x` when `c` is positive and `y` when `c = 0`.
- `isZero` and `isPos` test whether a number is zero or positive.
- `bnot`, `band`, `bor`, and `bimp` compute Boolean negation, conjunction, disjunction, and
  implication.
- `leb`, `ltb`, and `eqb` test `≤`, `<`, and `=` on numbers.
- `min` and `max` select the smaller and larger of two numbers.
-/

@[expose] public section

pra

/-- `IsBool b` holds when `b` is `0` or `1`. -/
def IsBool : Nat → QFProp := fun b => b = 0 ∨ b = 1

/-- `ite a b c` evaluates to `b` if `a` is positive and to `c` if `a` is zero. -/
def ite : Nat → Nat → Nat → Nat :=
  fun c x y => primrec y (fun _ _ => x) c

theorem ite_zero : ∀ x y, ite 0 x y = y := fun x y => rfl

theorem ite_succ : ∀ c x y, ite (S c) x y = x := fun c x y => rfl

theorem ite_of_ne_zero : ∀ c x y, ¬ c = 0 → ite c x y = x := by
  intro c x y
  induction c with k ih
  · intro h; exact false_elim (h rfl)
  · intro h; rfl

theorem ite_bool : ∀ c x y, IsBool x → IsBool y → IsBool (ite c x y) := by
  intro c x y hx hy
  induction c with n ih
  · exact hy
  · exact hx

theorem ite_self : ∀ c x, ite c x x = x := by
  intro c x
  induction c with k ih
  · rfl
  · rfl

theorem ite_mono : ∀ c x y u v, x ≤ u → y ≤ v → ite c x y ≤ ite c u v := by
  intro c x y u v hx hy
  by_cases h : c = 0
  · rw [h, ite_zero, ite_zero]
    exact hy
  · rw [ite_of_ne_zero c _ _ h, ite_of_ne_zero c _ _ h]
    exact hx

theorem le_ite : ∀ c x y z, x ≤ y → x ≤ z → x ≤ ite c y z := by
  intro c x y z hy hz
  have h := ite_mono c x x y z hy hz
  rw [ite_self] at h
  exact h

/-- Return `1` when `n = 0` and `0` when `n` is positive. -/
def isZero : Nat → Nat := fun n => ite n 0 1

/-- Return `1` when `n` is positive and `0` when `n = 0`. -/
def isPos : Nat → Nat := fun n => ite n 1 0

theorem isZero_zero : isZero 0 = 1 := rfl

theorem isZero_succ : ∀ n, isZero (S n) = 0 := fun n => rfl

theorem isPos_zero : isPos 0 = 0 := rfl

theorem isPos_succ : ∀ n, isPos (S n) = 1 := fun n => rfl

theorem isZero_bool : ∀ n, IsBool (isZero n) := by
  intro n
  induction n with k ih
  · right; rfl
  · left; rfl

theorem isPos_bool : ∀ n, IsBool (isPos n) := by
  intro n
  induction n with k ih
  · left; rfl
  · right; rfl

theorem isZero_eq_one : ∀ n, isZero n = 1 ↔ n = 0 := by
  intro n
  induction n with k ih
  · constructor <;> intro h <;> rfl
  · constructor
    · intro h; exact false_elim (zero_ne_succ 0 h)
    · intro h; exact false_elim (succ_ne_zero k h)

theorem isPos_eq_zero : ∀ n, isPos n = 0 ↔ n = 0 := by
  intro n
  induction n with k ih
  · constructor <;> intro h <;> rfl
  · constructor
    · intro h; exact false_elim (succ_ne_zero 0 h)
    · intro h; exact false_elim (succ_ne_zero k h)

theorem bool_eq_one : ∀ b, IsBool b → (b = 1 ↔ ¬ b = 0) := by
  intro b hb
  constructor
  · intro h hz
    exact succ_ne_zero 0 (eq_trans (eq_symm h) hz)
  · intro hn
    rcases hb with hz | ho
    · exact false_elim (hn hz)
    · exact ho

theorem bool_eq_zero : ∀ b, IsBool b → (b = 0 ↔ ¬ b = 1) := by
  intro b hb
  constructor
  · intro h ho
    exact zero_ne_succ 0 (eq_trans (eq_symm h) ho)
  · intro hn
    rcases hb with hz | ho
    · exact hz
    · exact false_elim (hn ho)

theorem isPos_eq_one : ∀ n, isPos n = 1 ↔ ¬ n = 0 := by
  intro n
  constructor
  · intro h hz
    rw [hz, isPos_zero] at h
    exact zero_ne_succ 0 h
  · intro hn
    apply and_right (bool_eq_one (isPos n) (isPos_bool n))
    intro hz
    exact hn (and_left (isPos_eq_zero n) hz)

theorem isZero_eq_zero : ∀ n, isZero n = 0 ↔ ¬ n = 0 := by
  intro n
  constructor
  · intro h hz
    rw [hz, isZero_zero] at h
    exact succ_ne_zero 0 h
  · intro hn
    apply and_right (bool_eq_zero (isZero n) (isZero_bool n))
    intro ho
    exact hn (and_left (isZero_eq_one n) ho)

theorem isPos_of_bool : ∀ b, IsBool b → isPos b = b := by
  intro b hb
  rcases hb with hz | ho
  · rw [hz]; rfl
  · rw [ho]; rfl

/-- Boolean negation: `1` when `a = 0` and `0` when `a` is positive. -/
def bnot : Nat → Nat := isZero

/-- Boolean conjunction: `1` when both `a` and `b` are positive, and `0` otherwise. -/
def band : Nat → Nat → Nat := fun a b => ite a (isPos b) 0

/-- Boolean disjunction: `1` when `a` or `b` is positive, and `0` when both are `0`. -/
def bor : Nat → Nat → Nat := fun a b => ite a 1 (isPos b)

/-- Boolean implication: `0` when `a` is positive and `b = 0`, and `1` otherwise. -/
def bimp : Nat → Nat → Nat := fun a b => ite a (isPos b) 1

theorem bnot_bool : ∀ a, IsBool (bnot a) := isZero_bool

theorem bnot_eq_one : ∀ a, bnot a = 1 ↔ a = 0 := isZero_eq_one

theorem bnot_eq_zero : ∀ a, bnot a = 0 ↔ ¬ a = 0 := isZero_eq_zero

theorem band_zero : ∀ b, band 0 b = 0 := fun b => rfl

theorem band_one_left : ∀ x, band 1 x = isPos x := fun x => rfl

theorem band_eq_one_of_eq_one : ∀ x y, x = 1 → y = 1 → band x y = 1 := by
  intro x y hx hy
  rw [hx, hy]; rfl

theorem band_of_ne_zero : ∀ a b, ¬ a = 0 → band a b = isPos b :=
  fun a b h => ite_of_ne_zero a (isPos b) 0 h

theorem band_bool : ∀ a b, IsBool (band a b) := by
  intro a b
  by_cases h : a = 0
  · rw [h, band_zero]; left; rfl
  · rw [band_of_ne_zero a b h]; exact isPos_bool b

theorem band_eq_one : ∀ a b, band a b = 1 ↔ ¬ a = 0 ∧ ¬ b = 0 := by
  intro a b
  constructor
  · intro h
    have ha : ¬ a = 0 := by
      intro hz
      rw [hz, band_zero] at h
      exact zero_ne_succ 0 h
    constructor
    · exact ha
    · rw [band_of_ne_zero a b ha] at h
      exact and_left (isPos_eq_one b) h
  · rintro (ha, hb)
    rw [band_of_ne_zero a b ha]
    exact and_right (isPos_eq_one b) hb

theorem band_eq_zero : ∀ a b, band a b = 0 ↔ a = 0 ∨ b = 0 := by
  intro a b
  constructor
  · intro h
    by_cases ha : a = 0
    · left; exact ha
    · right
      rw [band_of_ne_zero a b ha] at h
      exact and_left (isPos_eq_zero b) h
  · rintro (ha | hb)
    · rw [ha, band_zero]
    · change ite a (isPos b) 0 = 0
      rw [hb, isPos_zero, ite_self]

theorem bor_zero : ∀ b, bor 0 b = isPos b := fun b => rfl

theorem bor_of_ne_zero : ∀ a b, ¬ a = 0 → bor a b = 1 :=
  fun a b h => ite_of_ne_zero a 1 (isPos b) h

theorem bor_bool : ∀ a b, IsBool (bor a b) := by
  intro a b
  by_cases h : a = 0
  · rw [h, bor_zero]; exact isPos_bool b
  · right; exact bor_of_ne_zero a b h

theorem bor_eq_one : ∀ a b, bor a b = 1 ↔ ¬ a = 0 ∨ ¬ b = 0 := by
  intro a b
  constructor
  · intro h
    by_cases ha : a = 0
    · right
      rw [ha, bor_zero] at h
      exact and_left (isPos_eq_one b) h
    · left; exact ha
  · rintro (ha | hb)
    · exact bor_of_ne_zero a b ha
    · by_cases ha : a = 0
      · rw [ha, bor_zero]; exact and_right (isPos_eq_one b) hb
      · exact bor_of_ne_zero a b ha

theorem bor_eq_one_of_bool : ∀ a b, IsBool a → IsBool b →
    (bor a b = 1 ↔ a = 1 ∨ b = 1) := by
  intro a b ha hb
  exact iff_trans (bor_eq_one a b)
    (or_congr (and_right (bool_eq_one a ha), and_left (bool_eq_one a ha))
      (and_right (bool_eq_one b hb), and_left (bool_eq_one b hb)))

theorem bor_eq_one_of_left_eq_one : ∀ a b, a = 1 → bor a b = 1 := by
  intro a b h
  rw [h]
  rfl

theorem bor_eq_one_of_right_eq_one : ∀ a b, b = 1 → bor a b = 1 := by
  intro a b h
  rw [h]
  apply and_right (bor_eq_one a 1)
  right
  exact succ_ne_zero 0

theorem bor_eq_zero : ∀ a b, bor a b = 0 ↔ a = 0 ∧ b = 0 := by
  intro a b
  constructor
  · intro h
    have ha : a = 0 := by
      by_contra hn
      rw [bor_of_ne_zero a b hn] at h
      exact succ_ne_zero 0 h
    constructor
    · exact ha
    · rw [ha, bor_zero] at h
      exact and_left (isPos_eq_zero b) h
  · rintro (ha, hb)
    rw [ha, hb, bor_zero, isPos_zero]

theorem bimp_zero : ∀ b, bimp 0 b = 1 := fun b => rfl

theorem bimp_of_ne_zero : ∀ a b, ¬ a = 0 → bimp a b = isPos b :=
  fun a b h => ite_of_ne_zero a (isPos b) 1 h

theorem bimp_bool : ∀ a b, IsBool (bimp a b) := by
  intro a b
  by_cases h : a = 0
  · right; rw [h, bimp_zero]
  · rw [bimp_of_ne_zero a b h]; exact isPos_bool b

theorem bimp_eq_one : ∀ a b, bimp a b = 1 ↔ (¬ a = 0 → ¬ b = 0) := by
  intro a b
  constructor
  · intro h ha
    rw [bimp_of_ne_zero a b ha] at h
    exact and_left (isPos_eq_one b) h
  · intro h
    by_cases ha : a = 0
    · rw [ha, bimp_zero]
    · rw [bimp_of_ne_zero a b ha]
      exact and_right (isPos_eq_one b) (h ha)

theorem bimp_eq_zero : ∀ a b, bimp a b = 0 ↔ ¬ a = 0 ∧ b = 0 := by
  intro a b
  constructor
  · intro h
    have ha : ¬ a = 0 := by
      intro hz
      rw [hz, bimp_zero] at h
      exact succ_ne_zero 0 h
    constructor
    · exact ha
    · rw [bimp_of_ne_zero a b ha] at h
      exact and_left (isPos_eq_zero b) h
  · rintro (ha, hb)
    rw [bimp_of_ne_zero a b ha, hb, isPos_zero]

/-- Return `1` when `a ≤ b` and `0` otherwise. -/
def leb : Nat → Nat → Nat := fun a b => isZero (a - b)

/-- Return `1` when `a < b` and `0` otherwise. -/
def ltb : Nat → Nat → Nat := fun a b => leb (S a) b

theorem leb_bool : ∀ a b, IsBool (leb a b) := fun a b => isZero_bool (a - b)

theorem ltb_bool : ∀ a b, IsBool (ltb a b) := fun a b => leb_bool (S a) b

theorem leb_eq_one : ∀ a b, leb a b = 1 ↔ a ≤ b :=
  fun a b => isZero_eq_one (a - b)

theorem leb_eq_zero : ∀ a b, leb a b = 0 ↔ ¬ a ≤ b :=
  fun a b => isZero_eq_zero (a - b)

theorem ltb_eq_one : ∀ a b, ltb a b = 1 ↔ a < b := fun a b => leb_eq_one (S a) b

theorem ltb_eq_zero : ∀ a b, ltb a b = 0 ↔ ¬ a < b := fun a b => leb_eq_zero (S a) b

theorem ltb_eq_zero_of_ge : ∀ x y, y ≤ x → ltb x y = 0 := by
  intro x y h
  apply and_right (ltb_eq_zero x y)
  intro hxy
  exact not_le_of_lt x y hxy h

theorem band_eq_one_of_bool : ∀ a b, IsBool a → IsBool b →
    (band a b = 1 ↔ a = 1 ∧ b = 1) := by
  intro a b ha hb
  constructor
  · intro h
    rcases and_left (band_eq_one a b) h with (h₁, h₂)
    exact (and_right (bool_eq_one a ha) h₁, and_right (bool_eq_one b hb) h₂)
  · rintro (h₁, h₂)
    exact and_right (band_eq_one a b)
      (and_left (bool_eq_one a ha) h₁, and_left (bool_eq_one b hb) h₂)

/-- Return `1` when `a = b` and `0` otherwise. -/
def eqb : Nat → Nat → Nat := fun a b => band (leb a b) (leb b a)

theorem eqb_bool : ∀ a b, IsBool (eqb a b) := fun a b => band_bool (leb a b) (leb b a)

theorem eqb_eq_one : ∀ a b, eqb a b = 1 ↔ a = b := by
  intro a b
  constructor
  · intro h
    rcases and_left (band_eq_one_of_bool (leb a b) (leb b a)
      (leb_bool a b) (leb_bool b a)) h with (hab, hba)
    exact le_antisymm a b (and_left (leb_eq_one a b) hab) (and_left (leb_eq_one b a) hba)
  · intro h
    apply and_right (band_eq_one_of_bool (leb a b) (leb b a) (leb_bool a b) (leb_bool b a))
    rw [h]
    constructor <;> exact and_right (leb_eq_one b b) (le_refl b)

theorem eqb_self : ∀ x, eqb x x = 1 :=
  fun x => and_right (eqb_eq_one x x) rfl

/-- The boolean form of "`x ≤ y` or `y = z`", for inductions on a decidable statement. -/
theorem le_or_eq_bool : ∀ x y z, ¬ bor (leb x y) (eqb y z) = 0 ↔ (x ≤ y ∨ y = z) := by
  intro x y z
  constructor
  · intro h
    have h₁ := and_right (bool_eq_one (bor (leb x y) (eqb y z)) (bor_bool (leb x y) (eqb y z))) h
    rcases and_left (bor_eq_one (leb x y) (eqb y z)) h₁ with ha | hb
    · left
      exact and_left (leb_eq_one x y) (and_right (bool_eq_one (leb x y) (leb_bool x y)) ha)
    · right
      exact and_left (eqb_eq_one y z) (and_right (bool_eq_one (eqb y z) (eqb_bool y z)) hb)
  · intro h
    apply and_left (bool_eq_one (bor (leb x y) (eqb y z)) (bor_bool (leb x y) (eqb y z)))
    rcases h with ha | hb
    · exact bor_eq_one_of_left_eq_one (leb x y) (eqb y z) (and_right (leb_eq_one x y) ha)
    · exact bor_eq_one_of_right_eq_one (leb x y) (eqb y z) (and_right (eqb_eq_one y z) hb)

theorem eqb_eq_zero : ∀ a b, eqb a b = 0 ↔ ¬ a = b := by
  intro a b
  constructor
  · intro h he
    exact and_left (bool_eq_zero (eqb a b) (eqb_bool a b)) h
      (and_right (eqb_eq_one a b) he)
  · intro hn
    apply and_right (bool_eq_zero (eqb a b) (eqb_bool a b))
    intro h
    exact hn (and_left (eqb_eq_one a b) h)

/-- The smaller of two numbers. -/
def min : Nat → Nat → Nat := fun x y => ite (leb x y) x y

/-- The larger of two numbers. -/
def max : Nat → Nat → Nat := fun x y => ite (leb x y) y x

theorem min_of_le : ∀ x y, x ≤ y → min x y = x := by
  intro x y h
  rw [min, and_right (leb_eq_one x y) h, ite_succ]

theorem max_of_le : ∀ x y, x ≤ y → max x y = y := by
  intro x y h
  rw [max, and_right (leb_eq_one x y) h, ite_succ]

theorem min_of_ge : ∀ x y, y ≤ x → min x y = y := by
  intro x y h
  by_cases hxy : x ≤ y
  · rw [min_of_le x y hxy]; exact le_antisymm x y hxy h
  · change ite (leb x y) x y = y
    rw [and_right (leb_eq_zero x y) hxy, ite_zero]

theorem max_of_ge : ∀ x y, y ≤ x → max x y = x := by
  intro x y h
  by_cases hxy : x ≤ y
  · rw [max_of_le x y hxy]; exact le_antisymm y x h hxy
  · change ite (leb x y) y x = x
    rw [and_right (leb_eq_zero x y) hxy, ite_zero]

theorem min_le_left : ∀ x y, min x y ≤ x := by
  intro x y
  rcases le_total x y with h | h
  · rw [min_of_le x y h]; exact le_refl x
  · rw [min_of_ge x y h]; exact h

theorem min_le_right : ∀ x y, min x y ≤ y := by
  intro x y
  rcases le_total x y with h | h
  · rw [min_of_le x y h]; exact h
  · rw [min_of_ge x y h]; exact le_refl y

theorem le_min : ∀ x y z, z ≤ x → z ≤ y → z ≤ min x y := by
  intro x y z hx hy
  rcases le_total x y with h | h
  · rw [min_of_le x y h]; exact hx
  · rw [min_of_ge x y h]; exact hy

theorem le_max_left : ∀ x y, x ≤ max x y := by
  intro x y
  rcases le_total x y with h | h
  · rw [max_of_le x y h]; exact h
  · rw [max_of_ge x y h]; exact le_refl x

theorem le_max_right : ∀ x y, y ≤ max x y := by
  intro x y
  rcases le_total x y with h | h
  · rw [max_of_le x y h]; exact le_refl y
  · rw [max_of_ge x y h]; exact h

theorem max_le : ∀ x y z, x ≤ z → y ≤ z → max x y ≤ z := by
  intro x y z hx hy
  rcases le_total x y with h | h
  · rw [max_of_le x y h]; exact hy
  · rw [max_of_ge x y h]; exact hx

end
