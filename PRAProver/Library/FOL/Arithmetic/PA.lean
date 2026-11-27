module

public import PRAProver.Library.FOL.Arithmetic.Q

/-!
# Arithmetic in PA

This module establishes the basic algebraic, order, and induction laws of Peano arithmetic (`PA`)
as checked derivations using its first-order induction schema:

- Addition and multiplication laws (`FOL.PA.add_assoc`, `FOL.PA.add_comm`, `FOL.PA.mul_assoc`,
  `FOL.PA.mul_comm`, `FOL.PA.left_distrib`, and `FOL.PA.right_distrib`) together with additive
  cancellation (`FOL.PA.add_right_cancel` and `FOL.PA.add_left_cancel`).
- Linear order properties of `≤` and `<` (`FOL.PA.le_refl`, `FOL.PA.le_trans`,
  `FOL.PA.le_antisymm`, `FOL.PA.le_total`, `FOL.PA.lt_iff_le_not_ge`, and `FOL.PA.lt_or_ge`) and
  monotonicity of addition and multiplication.
- `FOL.PA.ind` and `FOL.PA.strong_ind` prove ordinary and strong induction for arbitrary formula
  codes `p`, where position `0` is the induction variable and later positions are parameters.
- `FOL.PA.exists_min` proves the least-number principle (`FOL.Arithmetic.leastNumber p`).
-/

namespace FOL

pra

namespace Arithmetic

/-- `belowAll p` states that the formula code `p` holds at all `y` below the variable `x` at
position `0`, defined as `∀ y, y < x → p(y)`. -/
fol_def belowAll over Arithmetic (p : Nat) : formula :=
  ${FOL.Formula.all (FOL.Formula.imp
    (lt (FOL.Term.var language 0) (FOL.Term.var language 1))
    (FOL.Formula.subst
      (FOL.consSubst (FOL.Term.var language 0) (FOL.shiftSubst language 2)) language p))}

/-- `strongInduction p` encodes the strong-induction schema for the unary formula code `p`,
defined as `(∀ x, (∀ y, y < x → p(y)) → p(x)) → ∀ x, p(x)`. -/
fol_def strongInduction over Arithmetic (p : Nat) : formula :=
  ${FOL.Formula.imp
    (FOL.Formula.all (FOL.Formula.imp (belowAll p) p)) (FOL.Formula.all p)}

/-- `leastNumber p` encodes the least-number principle for `p`: if `p` has a witness, it has one
with no smaller witness, defined as `(∃ x, p(x)) → ∃ x, p(x) ∧ ∀ y, y < x → ¬ p(y)`. -/
fol_def leastNumber over Arithmetic (p : Nat) : formula :=
  ${FOL.Formula.imp (FOL.Formula.ex p)
    (FOL.Formula.ex (FOL.Formula.conj p (belowAll (FOL.Formula.neg p))))}

end Arithmetic

namespace PA

open Arithmetic

theorem isAxiom_eq : ∀ A, PA.isAxiom A =
    bor (Q.isAxiom A) (bor (PA.induction.isAxiom A) 0) := fun A => rfl

theorem isAxiom_of_induction : ∀ A, PA.induction.isAxiom A = 1 → PA.isAxiom A = 1 := by
  intro A h
  rw [isAxiom_eq]
  exact bor_eq_one_of_right_eq_one (Q.isAxiom A) (bor (PA.induction.isAxiom A) 0)
    (bor_eq_one_of_left_eq_one (PA.induction.isAxiom A) 0 h)

/-- Every numerical formula code `p` yields a `PA` proof of its first-order induction instance.
Position `0` in `p` is the induction variable, and later positions are surrounding parameters. -/
fol_theorem ind (p : Nat) : PA ⊢ ${PA.induction.formula p} := by
  exact FOL.Provable.hypothesis language PA.isAxiom (PA.induction.formula p)
    (isAxiom_of_induction (PA.induction.formula p) (PA.induction.isAxiom_of_instance p))

fol_theorem zero_add : PA ⊢ ∀ y, 0 + y = y := by
  pintro y
  pinduction y with
  | zero =>
    prw [Q.add_zero]
  | succ k ih =>
    prw [Q.add_succ, ih]

fol_theorem succ_add : PA ⊢ ∀ x y, S x + y = S (x + y) := by
  pintro x y
  pinduction y with
  | zero =>
    prw [Q.add_zero]
  | succ k ih =>
    prw [Q.add_succ, ih]

fol_theorem add_assoc : PA ⊢ ∀ x y z, x + y + z = x + (y + z) := by
  pintro x y z
  pinduction z with
  | zero =>
    prw [Q.add_zero]
  | succ k ih =>
    prw [Q.add_succ, ih]

fol_theorem add_comm : PA ⊢ ∀ x y, x + y = y + x := by
  pintro x y
  pinduction y using PA.induction (motive := fun n => x + n = n + x) with
  | zero =>
    prw [Q.add_zero, zero_add]
  | succ k ih =>
    prw [Q.add_succ, ih, succ_add]

fol_theorem one_add_comm : PA ⊢ free x | 1 + x = x + 1 := by
  pexact add_comm[1, x]

fol_theorem one_add : PA ⊢ ∀ x, 1 + x = S x := by
  pintro x
  phave h : 1 + x = x + 1
  · pexact add_comm[1, x]
  · prw [h, Q.add_succ, Q.add_zero]

fol_theorem add_right_comm : PA ⊢ ∀ x y z, x + y + z = x + z + y := by
  pintro x y z
  phave h : y + z = z + y
  · pexact add_comm[y, z]
  · prw [add_assoc, h]

fol_theorem add_left_comm : PA ⊢ ∀ x y z, x + (y + z) = y + (x + z) := by
  pintro x y z
  ptrans (x + y) + z
  · prw [add_assoc]
  · ptrans (y + x) + z
    · pcongr
      · pexact add_comm[x, y]
      · prefl
    · prw [add_assoc]

fol_theorem add_right_cancel : PA ⊢ ∀ x y z, x + z = y + z → x = y := by
  pintro x y z
  pinduction z with
  | zero =>
    pintro h
    prw [Q.add_zero, h]
  | succ k ih =>
    pintro h
    papply ih
    papply Q.succ_inj[x + k, y + k]
    prw [Q.add_succ, h]

fol_theorem add_left_cancel : PA ⊢ ∀ x y z, z + x = z + y → x = y := by
  pintro x y z h
  papply PA.add_right_cancel[x, y, z]
  phave hx : z + x = x + z
  · pexact add_comm[z, x]
  · phave hy : z + y = y + z
    · pexact add_comm[z, y]
    · prw [hx, hy, h]

fol_theorem zero_mul : PA ⊢ ∀ y, 0 * y = 0 := by
  pintro y
  pinduction y with
  | zero =>
    prw [Q.mul_zero]
  | succ k ih =>
    prw [Q.mul_succ, ih, Q.add_zero]

fol_theorem succ_mul : PA ⊢ ∀ x y, S x * y = x * y + y := by
  pintro x y
  pinduction y with
  | zero =>
    prw [Q.mul_zero, Q.add_zero]
  | succ k ih =>
    phave h : x * k + k + x = x * k + x + k
    · pexact add_right_comm[x * k, k, x]
    · prw [Q.mul_succ, ih, Q.add_succ, h]

fol_theorem mul_comm : PA ⊢ ∀ x y, x * y = y * x := by
  pintro x y
  pinduction y with
  | zero =>
    prw [Q.mul_zero, zero_mul]
  | succ k ih =>
    prw [Q.mul_succ, succ_mul, ih]

fol_theorem one_mul : PA ⊢ ∀ y, 1 * y = y := by
  pintro y
  pinduction y with
  | zero =>
    prw [Q.mul_zero]
  | succ k ih =>
    prw [Q.mul_succ, ih, Q.add_succ, Q.add_zero]

fol_theorem mul_add : PA ⊢ ∀ x y z, x * (y + z) = x * y + x * z := by
  pintro x y z
  pinduction z with
  | zero =>
    prw [Q.add_zero, Q.mul_zero]
  | succ k ih =>
    prw [Q.add_succ, Q.mul_succ, ih, add_assoc]

fol_theorem left_distrib : PA ⊢ ∀ x y z, x * (y + z) = x * y + x * z := by
  pexact mul_add

fol_theorem right_distrib : PA ⊢ ∀ x y z, (x + y) * z = x * z + y * z := by
  pintro x y z
  phave h : (x + y) * z = z * (x + y)
  · pexact mul_comm[x + y, z]
  · phave hx : x * z = z * x
    · pexact mul_comm[x, z]
    · phave hy : y * z = z * y
      · pexact mul_comm[y, z]
      · prw [h, hx, hy, mul_add]

fol_theorem mul_assoc : PA ⊢ ∀ x y z, x * y * z = x * (y * z) := by
  pintro x y z
  pinduction z with
  | zero =>
    prw [Q.mul_zero]
  | succ k ih =>
    prw [Q.mul_succ, ih, mul_add]

fol_theorem mul_right_comm : PA ⊢ ∀ x y z, x * y * z = x * z * y := by
  pintro x y z
  phave h : y * z = z * y
  · pexact mul_comm[y, z]
  · prw [mul_assoc, h]

fol_theorem mul_one : PA ⊢ ∀ x, x * 1 = x := by
  pintro x
  prw [Q.mul_succ, Q.mul_zero, zero_add]

fol_theorem le_refl : PA ⊢ ∀ x, x ≤ x := by
  pintro x
  pexists 0
  prw [zero_add]

fol_theorem le_trans : PA ⊢ ∀ x y z, x ≤ y → y ≤ z → x ≤ z := by
  pintro x y z hxy hyz
  pcases hxy with ⟨a, ha⟩
  pcases hyz with ⟨b, hb⟩
  pexists b + a
  prw [add_assoc, ha, hb]

fol_theorem le_succ_self : PA ⊢ ∀ x, x ≤ S x := by
  pintro x
  pexists 1
  prw [one_add]

fol_theorem lt_succ_self : PA ⊢ ∀ x, x < S x := by
  pintro x
  pexact le_refl[S x]

fol_theorem le_antisymm : PA ⊢ ∀ x y, x ≤ y → y ≤ x → x = y := by
  pintro x y hxy hyx
  pcases hxy with ⟨a, ha⟩
  pcases hyx with ⟨b, hb⟩
  phave hsum : b + a = 0
  · papply PA.add_right_cancel[b + a, 0, x]
    prw [add_assoc, ha, hb, zero_add]
  · phave hz : b = 0 ∧ a = 0
    · papply Q.add_eq_zero_iff[b, a]
      passumption
    · pcases hz with ⟨hb0, ha0⟩
      prw [ha0, zero_add, ha]

fol_theorem lt_iff_le_not_ge : PA ⊢ ∀ x y, x < y ↔ x ≤ y ∧ ¬ y ≤ x := by
  pintro x y
  pconstructor
  · pintro h
    pcases h with ⟨a, ha⟩
    pconstructor
    · pexists S a
      prw [succ_add, Q.add_succ, ha]
    · pintro hyx
      pcases hyx with ⟨b, hb⟩
      papply Q.succ_ne_zero[b + a]
      papply PA.add_right_cancel[S (b + a), 0, x]
      phave hs : (b + a) + S x = x
      · prw [add_assoc, ha, hb]
      · prw [hs, succ_add, Q.add_succ, zero_add]
  · pintro h
    pcases h with ⟨hle, hng⟩
    pcases hle with ⟨a, ha⟩
    pcases Q.zero_or_succ[a] with ha0 | hex
    · pexfalso
      papply hng
      pexists 0
      prw [ha0, zero_add, ha]
    · pcases hex with ⟨b, hb⟩
      pexists b
      prw [hb, ha, succ_add, Q.add_succ]

fol_theorem le_total : PA ⊢ ∀ x y, x ≤ y ∨ y ≤ x := by
  pintro x y
  pinduction x with
  | zero =>
    pleft
    pexact Q.zero_le[y]
  | succ k ih =>
    pcases ih with hky | hyk
    · pcases hky with ⟨a, ha⟩
      pcases Q.zero_or_succ[a] with ha0 | hex
      · pright
        pexists 1
        prw [ha0, ha, zero_add, one_add]
      · pcases hex with ⟨b, hb⟩
        pleft
        pexists b
        prw [hb, ha, succ_add, Q.add_succ]
    · pright
      papply le_trans[y, k, S k]
      · passumption
      · pexact le_succ_self[k]

fol_theorem le_succ_of_le : PA ⊢ ∀ x y, x ≤ y → x ≤ S y := by
  pintro x y h
  papply le_trans[x, y, S y]
  · passumption
  · pexact le_succ_self[y]

fol_theorem lt_succ_of_lt : PA ⊢ ∀ x y, x < y → x < S y := by
  pintro x y
  pexact le_succ_of_le[S x, y]

fol_theorem add_le_add : PA ⊢ ∀ x y z w, x ≤ y → z ≤ w → x + z ≤ y + w := by
  pintro x y z w hxy hzw
  pcases hxy with ⟨a, ha⟩
  pcases hzw with ⟨b, hb⟩
  pexists a + b
  ptrans ((a + b) + x) + z
  · prw [add_assoc]
  · ptrans ((a + x) + b) + z
    · pcongr
      · pexact add_right_comm[a, b, x]
      · prefl
    · ptrans (a + x) + (b + z)
      · prw [add_assoc]
      · pcongr
        · passumption
        · passumption

fol_theorem add_le_add_iff_left : PA ⊢ ∀ x y z, z + x ≤ z + y ↔ x ≤ y := by
  pintro x y z
  pconstructor
  · pintro h
    pcases h with ⟨a, ha⟩
    pexists a
    papply PA.add_left_cancel[a + x, y, z]
    ptrans a + (z + x)
    · pexact add_left_comm[z, a, x]
    · passumption
  · pintro h
    papply add_le_add[z, z, x, y]
    · pexact le_refl[z]
    · passumption

fol_theorem add_le_add_iff_right : PA ⊢ ∀ x y z, x + z ≤ y + z ↔ x ≤ y := by
  pintro x y z
  pconstructor
  · pintro h
    pcases h with ⟨a, ha⟩
    pexists a
    papply PA.add_right_cancel[a + x, y, z]
    prw [add_assoc, ha]
  · pintro h
    papply add_le_add[x, y, z, z]
    · passumption
    · pexact le_refl[z]

fol_theorem le_add_of_le_left : PA ⊢ ∀ x y z, x ≤ y → x ≤ z + y := by
  pintro x y z h
  pcases h with ⟨a, ha⟩
  pexists z + a
  prw [add_assoc, ha]

fol_theorem le_add_of_le_right : PA ⊢ ∀ x y z, x ≤ y → x ≤ y + z := by
  pintro x y z h
  pcases h with ⟨a, ha⟩
  pexists a + z
  phave hc : a + z + x = a + x + z
  · pexact add_right_comm[a, z, x]
  · prw [hc, ha]

fol_theorem le_add_left : PA ⊢ ∀ x y, x ≤ y + x := by
  pintro x y
  pexists y
  prefl

fol_theorem le_add_right : PA ⊢ ∀ x y, x ≤ x + y := by
  pintro x y
  pexists y
  pexact add_comm[y, x]

fol_theorem add_lt_add_of_le_of_lt : PA ⊢ ∀ x y z w, x ≤ y → z < w → x + z < y + w := by
  pintro x y z w hxy hzw
  pcases hxy with ⟨a, ha⟩
  pcases hzw with ⟨b, hb⟩
  pexists a + b
  ptrans (a + b) + (x + S z)
  · prw [Q.add_succ]
  · ptrans ((a + b) + x) + S z
    · prw [add_assoc]
    · ptrans ((a + x) + b) + S z
      · pcongr
        · pexact add_right_comm[a, b, x]
        · prefl
      · ptrans (a + x) + (b + S z)
        · prw [add_assoc]
        · pcongr
          · passumption
          · passumption

fol_theorem add_lt_add_of_lt_of_le : PA ⊢ ∀ x y z w, x < y → z ≤ w → x + z < y + w := by
  pintro x y z w hxy hzw
  pcases hxy with ⟨a, ha⟩
  pcases hzw with ⟨b, hb⟩
  pexists a + b
  ptrans (a + b) + (S x + z)
  · prw [succ_add, Q.add_succ]
  · ptrans ((a + b) + S x) + z
    · prw [add_assoc]
    · ptrans ((a + S x) + b) + z
      · pcongr
        · pexact add_right_comm[a, b, S x]
        · prefl
      · ptrans (a + S x) + (b + z)
        · prw [add_assoc]
        · pcongr
          · passumption
          · passumption

fol_theorem lt_add_of_lt_left : PA ⊢ ∀ x y z, x < y → x < z + y := by
  pintro x y z
  pexact le_add_of_le_left[S x, y, z]

fol_theorem lt_add_of_lt_right : PA ⊢ ∀ x y z, x < y → x < y + z := by
  pintro x y z
  pexact le_add_of_le_right[S x, y, z]

fol_theorem mul_le_mul : PA ⊢ ∀ x y z w, x ≤ y → z ≤ w → x * z ≤ y * w := by
  pintro x y z w hxy hzw
  pcases hxy with ⟨a, ha⟩
  pcases hzw with ⟨b, hb⟩
  pexists a * b + x * b + a * z
  ptrans (a * b + x * b) + (a * z + x * z)
  · prw [add_assoc]
  · ptrans (a + x) * b + (a + x) * z
    · pcongr
      · psymm
        pexact right_distrib[a, x, b]
      · psymm
        pexact right_distrib[a, x, z]
    · ptrans (a + x) * (b + z)
      · psymm
        pexact left_distrib[a + x, b, z]
      · pcongr
        · passumption
        · passumption

fol_theorem mul_le_mul_left : PA ⊢ ∀ x y z, x ≤ y → z * x ≤ z * y := by
  pintro x y z h
  papply mul_le_mul[z, z, x, y]
  · pexact le_refl[z]
  · passumption

fol_theorem mul_le_mul_right : PA ⊢ ∀ x y z, x ≤ y → x * z ≤ y * z := by
  pintro x y z h
  papply mul_le_mul[x, y, z, z]
  · passumption
  · pexact le_refl[z]

fol_theorem le_iff_lt_or_eq : PA ⊢ ∀ x y, x ≤ y ↔ x < y ∨ x = y := by
  pintro x y
  pconstructor
  · pintro h
    pcontradiction
    pintro hn
    papply hn
    pleft
    papply lt_iff_le_not_ge[x, y]
    pconstructor
    · passumption
    · pintro hback
      papply hn
      pright
      papply le_antisymm[x, y]
      · passumption
      · passumption
  · pintro h
    pcases h with hlt | he
    · phave hp : x ≤ y ∧ ¬ y ≤ x
      · papply lt_iff_le_not_ge[x, y]
        passumption
      · pcases hp with ⟨hle, hn⟩
        passumption
    · pexists 0
      prw [zero_add, he]

fol_theorem lt_succ_iff_lt_or_eq : PA ⊢ ∀ x y, x < S y ↔ x < y ∨ x = y := by
  pintro x y
  pconstructor
  · pintro h
    papply le_iff_lt_or_eq[x, y]
    papply Q.lt_succ_iff_le[x, y]
    passumption
  · pintro h
    papply Q.lt_succ_iff_le[x, y]
    papply le_iff_lt_or_eq[x, y]
    passumption

fol_theorem succ_not_le_self : PA ⊢ ∀ x, ¬ S x ≤ x := by
  pintro x h
  phave hp : x ≤ x ∧ ¬ x ≤ x
  · papply lt_iff_le_not_ge[x, x]
    passumption
  · pcases hp with ⟨hy, hn⟩
    pcontradiction

fol_theorem succ_ne_self : PA ⊢ ∀ x, S x ≠ x := by
  pintro x h
  papply succ_not_le_self[x]
  pexists 0
  prw [zero_add, h]

fol_theorem lt_of_lt_of_le : PA ⊢ ∀ x y z, x < y → y ≤ z → x < z := by
  pintro x y z
  pexact le_trans[S x, y, z]

fol_theorem lt_of_le_of_lt : PA ⊢ ∀ x y z, x ≤ y → y < z → x < z := by
  pintro x y z hxy hyz
  papply le_trans[S x, S y, z]
  · papply Q.succ_le_succ_iff[x, y]
    passumption
  · passumption

fol_theorem pos_of_lt : PA ⊢ ∀ x y, x < y → 0 < y := by
  pintro x y h
  papply lt_of_le_of_lt[0, x, y]
  · pexact Q.zero_le[x]
  · passumption

fol_theorem zero_or_pos : PA ⊢ ∀ x, x = 0 ∨ 0 < x := by
  pintro x
  pcases Q.zero_or_succ[x] with h | h
  · pleft
    passumption
  · pcases h with ⟨a, ha⟩
    pright
    pexists a
    prw [Q.add_one, ha]

fol_theorem add_lt_add_iff_left : PA ⊢ ∀ x y z, z + x < z + y ↔ x < y := by
  pintro x y z
  pconstructor
  · pintro h
    pcases h with ⟨a, ha⟩
    pexists a
    papply PA.add_left_cancel[a + S x, y, z]
    ptrans a + (z + S x)
    · pexact add_left_comm[z, a, S x]
    · ptrans a + S (z + x)
      · prw [Q.add_succ]
      · passumption
  · pintro h
    papply add_lt_add_of_le_of_lt[z, z, x, y]
    · pexact le_refl[z]
    · passumption

fol_theorem add_lt_add_iff_right : PA ⊢ ∀ x y z, x + z < y + z ↔ x < y := by
  pintro x y z
  pconstructor
  · pintro h
    pcases h with ⟨a, ha⟩
    pexists a
    papply PA.add_right_cancel[a + S x, y, z]
    ptrans a + (S x + z)
    · prw [add_assoc]
    · ptrans a + S (x + z)
      · prw [succ_add]
      · passumption
  · pintro h
    papply add_lt_add_of_lt_of_le[x, y, z, z]
    · passumption
    · pexact le_refl[z]

fol_theorem lt_add_of_pos_left : PA ⊢ ∀ x z, 0 < z → x < z + x := by
  pintro x z h
  pcases h with ⟨a, ha⟩
  pexists a
  ptrans S a + x
  · prw [Q.add_succ, succ_add]
  · pcongr
    · prw [Q.add_one, ha]
    · prefl

fol_theorem lt_add_of_pos_right : PA ⊢ ∀ x z, 0 < z → x < x + z := by
  pintro x z h
  pcases h with ⟨a, ha⟩
  pexists a
  ptrans S a + x
  · prw [Q.add_succ, succ_add]
  · ptrans z + x
    · pcongr
      · prw [Q.add_one, ha]
      · prefl
    · pexact add_comm[z, x]

fol_theorem le_mul_of_le_left : PA ⊢ ∀ x y z, 0 < z → x ≤ y → x ≤ z * y := by
  pintro x y z hz hxy
  phave hp : 1 * x ≤ z * y
  · papply mul_le_mul[1, z, x, y]
    · passumption
    · passumption
  · pcases hp with ⟨a, ha⟩
    pexists a
    prw [one_mul, ha]

fol_theorem le_mul_of_le_right : PA ⊢ ∀ x y z, 0 < z → x ≤ y → x ≤ y * z := by
  pintro x y z hz hxy
  phave hp : x * 1 ≤ y * z
  · papply mul_le_mul[x, y, 1, z]
    · passumption
    · passumption
  · pcases hp with ⟨a, ha⟩
    pexists a
    prw [mul_one, ha]

fol_theorem le_mul_left : PA ⊢ ∀ x z, 0 < z → x ≤ z * x := by
  pintro x z hz
  papply le_mul_of_le_left[x, x, z]
  · passumption
  · pexact le_refl[x]

fol_theorem le_mul_right : PA ⊢ ∀ x z, 0 < z → x ≤ x * z := by
  pintro x z hz
  papply le_mul_of_le_right[x, x, z]
  · passumption
  · pexact le_refl[x]

fol_theorem mul_lt_mul_left : PA ⊢ ∀ x y z, 0 < z → x < y → z * x < z * y := by
  pintro x y z hz hxy
  papply lt_of_lt_of_le[z * x, z * S x, z * y]
  · pcases hz with ⟨a, ha⟩
    pexists a
    ptrans z + (z * x)
    · ptrans S a + (z * x)
      · prw [Q.add_succ, succ_add]
      · pcongr
        · prw [Q.add_one, ha]
        · prefl
    · ptrans z * x + z
      · pexact add_comm[z, z * x]
      · prw [Q.mul_succ]
  · papply mul_le_mul_left[S x, y, z]
    passumption

fol_theorem mul_lt_mul_right : PA ⊢ ∀ x y z, 0 < z → x < y → x * z < y * z := by
  pintro x y z hz hxy
  phave hp : z * x < z * y
  · papply mul_lt_mul_left[x, y, z]
    · passumption
    · passumption
  · pcases hp with ⟨a, ha⟩
    pexists a
    phave hx : x * z = z * x
    · pexact mul_comm[x, z]
    · phave hy : y * z = z * y
      · pexact mul_comm[y, z]
      · prw [hx, hy, ha]

fol_theorem lt_mul_left : PA ⊢ ∀ x z, 0 < x → 1 < z → x < z * x := by
  pintro x z hx hz
  phave hp : 1 * x < z * x
  · papply mul_lt_mul_right[1, z, x]
    · passumption
    · passumption
  · pcases hp with ⟨a, ha⟩
    pexists a
    prw [one_mul, ha]

fol_theorem lt_mul_right : PA ⊢ ∀ x z, 0 < x → 1 < z → x < x * z := by
  pintro x z hx hz
  phave hp : x * 1 < x * z
  · papply mul_lt_mul_left[1, z, x]
    · passumption
    · passumption
  · pcases hp with ⟨a, ha⟩
    pexists a
    prw [mul_one, ha]

fol_theorem mul_le_mul_iff_left : PA ⊢ ∀ x y z, 0 < z → (z * x ≤ z * y ↔ x ≤ y) := by
  pintro x y z hz
  pconstructor
  · pintro hp
    pcontradiction
    pintro hn
    phave hyx : y < x
    · papply lt_iff_le_not_ge[y, x]
      pconstructor
      · pcases le_total[x, y] with hxy | hyx
        · pexfalso
          pcontradiction
        · passumption
      · passumption
    · phave hlt : z * y < z * x
      · papply mul_lt_mul_left[y, x, z]
        · passumption
        · passumption
      · phave hpair : z * y ≤ z * x ∧ ¬ z * x ≤ z * y
        · papply lt_iff_le_not_ge[z * y, z * x]
          passumption
        · pcases hpair with ⟨hle, hnot⟩
          pcontradiction
  · pexact mul_le_mul_left[x, y, z]

fol_theorem mul_le_mul_iff_right : PA ⊢ ∀ x y z, 0 < z → (x * z ≤ y * z ↔ x ≤ y) := by
  pintro x y z hz
  pconstructor
  · pintro hp
    papply mul_le_mul_iff_left[x, y, z]
    · passumption
    · pcases hp with ⟨a, ha⟩
      pexists a
      phave hx : z * x = x * z
      · pexact mul_comm[z, x]
      · phave hy : z * y = y * z
        · pexact mul_comm[z, y]
        · prw [hx, hy, ha]
  · pexact mul_le_mul_right[x, y, z]

fol_theorem mul_pos_iff : PA ⊢ ∀ x y, 0 < x * y ↔ 0 < x ∧ 0 < y := by
  pintro x y
  pconstructor
  · pintro hp
    pcases zero_or_pos[x] with hx | hx
    · pexfalso
      papply Q.not_lt_zero[0]
      pcases hp with ⟨a, ha⟩
      pexists a
      prw [hx, zero_mul, ha]
    · pcases zero_or_pos[y] with hy | hy
      · pexfalso
        papply Q.not_lt_zero[0]
        pcases hp with ⟨a, ha⟩
        pexists a
        prw [hy, Q.mul_zero, ha]
      · pconstructor
        · passumption
        · passumption
  · pintro hp
    pcases hp with ⟨hx, hy⟩
    phave hle : 1 * 1 ≤ x * y
    · papply mul_le_mul[1, x, 1, y]
      · passumption
      · passumption
    · pcases hle with ⟨a, ha⟩
      pexists a
      prw [one_mul, ha]

fol_theorem mul_eq_zero_iff : PA ⊢ ∀ x y, x * y = 0 ↔ x = 0 ∨ y = 0 := by
  pintro x y
  pconstructor
  · pintro h
    pcases Q.zero_or_succ[x] with hx | hx
    · pleft
      passumption
    · pcases hx with ⟨a, ha⟩
      pcases Q.zero_or_succ[y] with hy | hy
      · pright
        passumption
      · pcases hy with ⟨b, hb⟩
        pexfalso
        papply Q.succ_ne_zero[(S a) * b + a]
        ptrans x * y
        · prw [ha, hb, Q.mul_succ, Q.add_succ]
        · passumption
  · pintro h
    pcases h with hx | hy
    · prw [hx, zero_mul]
    · prw [hy, Q.mul_zero]

fol_theorem mul_eq_one_iff : PA ⊢ ∀ x y, x * y = 1 ↔ x = 1 ∧ y = 1 := by
  pintro x y
  pconstructor
  · pintro h
    phave positive : 0 < x ∧ 0 < y
    · papply mul_pos_iff[x, y]
      pexists 0
      prw [Q.add_succ, Q.add_zero, h]
    · pcases positive with ⟨hx, hy⟩
      pconstructor
      · papply le_antisymm[x, 1]
        · phave bound : x ≤ x * y
          · papply le_mul_right[x, y]
            passumption
          · pcases bound with ⟨a, ha⟩
            pexists a
            prw [ha, h]
        · papply Q.one_le_iff_zero_lt[x]
          passumption
      · papply le_antisymm[y, 1]
        · phave bound : y ≤ x * y
          · papply le_mul_left[y, x]
            passumption
          · pcases bound with ⟨a, ha⟩
            pexists a
            prw [ha, h]
        · papply Q.one_le_iff_zero_lt[y]
          passumption
  · pintro h
    pcases h with ⟨hx, hy⟩
    prw [hx, hy, mul_one]

fol_theorem strong_ind_bounded (p : Nat) : PA ⊢
    ${FOL.Formula.all (FOL.Formula.imp (belowAll p) p)} →
    ${FOL.Formula.all (belowAll p)} := by
  pintro hs x
  pinduction x with
  | zero =>
    pintro y hy
    pexfalso
    papply Q.not_lt_zero[y]
    passumption
  | succ k ih =>
    pintro y hy
    papply hs[y]
    pintro z hz
    papply ih[z]
    papply lt_of_lt_of_le[z, y, k]
    · passumption
    · papply Q.lt_succ_iff_le[y, k]
      passumption

/-- Strong induction in `PA` for any formula code `p`, with position `0` as the induction variable
and later positions as surrounding parameters. -/
fol_theorem strong_ind (p : Nat) : PA ⊢ ${strongInduction p} := by
  pintro hs
  phave hb : ${FOL.Formula.all (belowAll p)}
  · papply strong_ind_bounded p
    passumption
  · pintro x
    papply hb[S x, x]
    pexact lt_succ_self[x]

/-- The least-number principle in `PA`: every inhabited formula `p` has a least witness. -/
fol_theorem exists_min (p : formula of 1) : PA ⊢ ${leastNumber p} := by
  pintro hex
  pcontradiction
  pintro hnone
  phave noElements : ${FOL.Formula.all (FOL.Formula.neg p)}
  · papply strong_ind (FOL.Formula.neg p)
    pintro x ih hp
    papply hnone
    pexists x
    pconstructor
    · passumption
    · passumption
  · pcases hex with ⟨x, hx⟩
    papply noElements[x]
    passumption

fol_theorem lt_irrefl : PA ⊢ ∀ x, ¬ x < x := by
  pintro x h
  phave hn : ¬ x ≤ x
  · papply lt_iff_le_not_ge[x, x]
    passumption
  · papply hn
    pexact le_refl[x]

fol_theorem not_lt_of_ge : PA ⊢ ∀ x y, y ≤ x → ¬ x < y := by
  pintro x y hle hlt
  phave hp : x ≤ y ∧ ¬ y ≤ x
  · papply lt_iff_le_not_ge[x, y]
    passumption
  · pcases hp with ⟨hxy, hn⟩
    pcontradiction

fol_theorem le_of_eq_left : PA ⊢ ∀ a b c, a = b → b ≤ c → a ≤ c := by
  pintro a b c he h
  pcases h with ⟨k, hk⟩
  pexists k
  prw [he, hk]

fol_theorem le_of_eq_right : PA ⊢ ∀ a b c, a ≤ b → b = c → a ≤ c := by
  pintro a b c h he
  pcases h with ⟨k, hk⟩
  pexists k
  prw [hk, he]

fol_theorem lt_of_eq_left : PA ⊢ ∀ a b c, a = b → b < c → a < c := by
  pintro a b c he h
  pcases h with ⟨k, hk⟩
  pexists k
  prw [he, hk]

fol_theorem lt_of_eq_right : PA ⊢ ∀ a b c, a < b → b = c → a < c := by
  pintro a b c h he
  pcases h with ⟨k, hk⟩
  pexists k
  prw [hk, he]

fol_theorem le_of_lt : PA ⊢ ∀ x y, x < y → x ≤ y := by
  pintro x y h
  papply lt_iff_le_not_ge[x, y]
  passumption

fol_theorem lt_trans : PA ⊢ ∀ x y z, x < y → y < z → x < z := by
  pintro x y z hxy hyz
  papply lt_of_lt_of_le[x, y, z]
  · passumption
  · papply le_of_lt[y, z]
    passumption

fol_theorem lt_or_ge : PA ⊢ ∀ x y, x < y ∨ y ≤ x := by
  pintro x y
  pcases le_total[x, y] with h | h
  · phave alternatives : x < y ∨ x = y
    · papply le_iff_lt_or_eq[x, y]
      passumption
    · pcases alternatives with hlt | he
      · pleft
        passumption
      · pright
        pexists 0
        prw [zero_add, he]
  · pright
    passumption

fol_theorem positive_predecessor : PA ⊢ ∀ m, 0 < m → ∃ k, m = S k := by
  pintro m h
  pcases h with ⟨k, hk⟩
  pexists k
  psymm
  prw [Q.add_succ, Q.add_zero, hk]

end PA

extract_witness FOL.PA.add_assoc FOL.PA.add_comm FOL.PA.add_left_cancel FOL.PA.add_left_comm
  FOL.PA.add_lt_add_iff_left FOL.PA.add_lt_add_of_le_of_lt FOL.PA.add_right_cancel
  FOL.PA.add_right_comm FOL.PA.exists_min FOL.PA.le_add_left FOL.PA.le_add_of_le_right
  FOL.PA.le_add_right FOL.PA.le_antisymm FOL.PA.le_iff_lt_or_eq FOL.PA.le_mul_left
  FOL.PA.le_mul_of_le_left FOL.PA.le_refl FOL.PA.le_succ_of_le FOL.PA.le_succ_self FOL.PA.le_total
  FOL.PA.le_trans FOL.PA.lt_iff_le_not_ge FOL.PA.lt_of_lt_of_le FOL.PA.lt_succ_iff_lt_or_eq
  FOL.PA.lt_succ_of_lt FOL.PA.lt_succ_self FOL.PA.mul_add FOL.PA.mul_assoc FOL.PA.mul_comm
  FOL.PA.mul_le_mul FOL.PA.mul_le_mul_iff_left FOL.PA.mul_le_mul_iff_right FOL.PA.mul_le_mul_left
  FOL.PA.mul_le_mul_right FOL.PA.mul_lt_mul_left FOL.PA.mul_one FOL.PA.mul_pos_iff FOL.PA.one_add
  FOL.PA.one_mul FOL.PA.right_distrib FOL.PA.strong_ind FOL.PA.strong_ind_bounded FOL.PA.succ_add
  FOL.PA.succ_mul FOL.PA.zero_add FOL.PA.zero_mul FOL.PA.zero_or_pos

extract_witness FOL.PA.le_of_eq_right FOL.PA.le_of_lt FOL.PA.lt_of_eq_left FOL.PA.lt_of_eq_right
  FOL.PA.lt_or_ge FOL.PA.not_lt_of_ge FOL.PA.positive_predecessor

end

end FOL
