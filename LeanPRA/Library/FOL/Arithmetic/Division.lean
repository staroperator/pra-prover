module

public import LeanPRA.Library.FOL.Arithmetic.Tactic.Ring

/-!
# Divisibility and division with remainder in PA

This module defines divisibility and Euclidean remainder in the language of arithmetic and proves
their existence, uniqueness, and remainder-preservation properties in `PA`:

- `FOL.Arithmetic.divides a b` states that `b = a * q` for some `q`.
- `FOL.Arithmetic.remainder r b m` states that `r < m` and `b = m * q + r` for some quotient
  `q`.
- `FOL.PA.divides_refl`, `FOL.PA.divides_one`, `FOL.PA.divides_mul_right`, and
  `FOL.PA.divides_trans` establish basic divisibility properties.
- `FOL.PA.remainder_total` proves that every dividend `b` has a remainder modulo any positive `m`.
- `FOL.PA.remainder_unique` proves that the remainder of `b` modulo `m` is unique by comparing
  quotients (`FOL.PA.quotient_ge`).
- `FOL.PA.remainder_add_multiple` and `FOL.PA.remainder_add_divisible` show that adding a
  multiple of the modulus preserves a remainder.
-/

namespace FOL

pra

namespace Arithmetic

/-- `remainder r b m` states that `r` is the Euclidean remainder of `b` modulo `m`, defined as
`r < m ∧ ∃ q, b = m * q + r`. -/
fol_def remainder over Arithmetic : term → term → term → formula := fun r b m =>
  r < m ∧ ∃ q, b = m * q + r

/-- `divides a b` states that `a` divides `b`, defined as `∃ q, b = a * q`. -/
fol_def divides over Arithmetic : term → term → formula := fun a b => ∃ q, b = a * q

end Arithmetic

namespace PA

open Arithmetic

fol_theorem divides_refl : PA ⊢ ∀ a, divides a a := by
  pintro a
  pexists 1
  prw [mul_one]

fol_theorem divides_one : PA ⊢ ∀ a, divides 1 a := by
  pintro a
  pexists a
  prw [one_mul]

fol_theorem divides_mul_right : PA ⊢
    ∀ a b c, divides a b → divides a (b * c) := by
  pintro a b c h
  pcases h with ⟨q, he⟩
  pexists q * c
  prw [he, mul_assoc]

fol_theorem divides_trans : PA ⊢
    ∀ a b c, divides a b → divides b c → divides a c := by
  pintro a b c hab hbc
  pcases hab with ⟨q, he⟩
  pcases hbc with ⟨t, hf⟩
  pexists q * t
  prw [he, hf, mul_assoc]

fol_theorem remainder_self : PA ⊢ ∀ b m, b < m → remainder b b m := by
  pintro b m h
  pconstructor
  · passumption
  · pexists 0
    prw [Q.mul_zero, zero_add]

/-- In `PA`, every dividend `b` has a remainder modulo any positive modulus `m`. -/
fol_theorem remainder_total : PA ⊢ ∀ m b, 0 < m → ∃ r, remainder r b m := by
  pintro m b
  pinduction b with
  | zero =>
    pintro hm
    pexists 0
    papply remainder_self[0, m]
    passumption
  | succ k ih =>
    pintro hm
    phave hex : ∃ r, remainder r k m
    · papply ih
      passumption
    · pcases hex with ⟨r, hr⟩
      pcases hr with ⟨hlt, hq⟩
      pcases hq with ⟨q, heq⟩
      phave hs : S r < m ∨ S r = m
      · papply le_iff_lt_or_eq[S r, m]
        papply Q.succ_le_iff_lt[r, m]
        passumption
      · pcases hs with hsr | hse
        · pexists S r
          pconstructor
          · passumption
          · pexists q
            prw [heq, Q.add_succ]
        · pexists 0
          pconstructor
          · passumption
          · pexists S q
            phave he : S k = m * q + S r
            · prw [heq, Q.add_succ]
            · prw [Q.mul_succ, Q.add_zero, he, hse]

fol_theorem quotient_not_lt : PA ⊢
    ∀ m b q r u s, r < m → b = m * q + r → b = m * u + s → ¬ q < u := by
  pintro m b q r u s hr hq hu hqu
  phave hupper : b < m * S q
  · papply lt_of_eq_left[b, m * q + r, m * S q]
    · passumption
    · papply lt_of_eq_right[m * q + r, m * q + m, m * S q]
      · papply add_lt_add_iff_left[r, m, m * q]
        passumption
      · prw [Q.mul_succ]
  · phave hlower : m * S q ≤ b
    · papply le_of_eq_right[m * S q, m * u + s, b]
      · papply le_trans[m * S q, m * u, m * u + s]
        · papply mul_le_mul_left[S q, u, m]
          papply Q.succ_le_iff_lt[q, u]
          passumption
        · pexact le_add_right[m * u, s]
      · psymm
        passumption
    · papply not_lt_of_ge[b, m * S q]
      · passumption
      · passumption

fol_theorem quotient_ge : PA ⊢ ∀ m b q r u s, r < m → b = m * q + r → b = m * u + s → u ≤ q := by
  pintro m b q r u s hr hq hu
  pcases lt_or_ge[q, u] with hlt | hle
  · pexfalso
    papply quotient_not_lt[m, b, q, r, u, s]
    · passumption
    · passumption
    · passumption
    · passumption
  · passumption

/-- In `PA`, any two remainders of the same dividend `b` and modulus `m` are equal. -/
fol_theorem remainder_unique : PA ⊢
    ∀ r s b m, remainder r b m → remainder s b m → r = s := by
  pintro r s b m hr hs
  pcases hr with ⟨hrlt, hexq⟩
  pcases hexq with ⟨q, hq⟩
  pcases hs with ⟨hslt, hexu⟩
  pcases hexu with ⟨u, hu⟩
  phave he : q = u
  · papply le_antisymm[q, u]
    · papply quotient_ge[m, b, u, s, q, r]
      · passumption
      · passumption
      · passumption
    · papply quotient_ge[m, b, q, r, u, s]
      · passumption
      · passumption
      · passumption
  · papply add_left_cancel[r, s, m * u]
    ptrans b
    · psymm
      prw [hq, he]
    · passumption

fol_theorem remainder_add_multiple : PA ⊢
    ∀ r b m t, remainder r b m → remainder r (b + m * t) m := by
  pintro r b m t hr
  pcases hr with ⟨hlt, hex⟩
  pcases hex with ⟨q, he⟩
  pconstructor
  · passumption
  · pexists q + t
    ptrans (m * q + r) + m * t
    · prw [he]
    · pring

fol_theorem remainder_add_divisible : PA ⊢
    ∀ r b m d t, remainder r b m → divides m d →
    remainder r (b + d * t) m := by
  pintro r b m d t hr hd
  pcases hr with ⟨hlt, hex⟩
  pcases hex with ⟨q, he⟩
  pcases hd with ⟨u, hdq⟩
  pconstructor
  · passumption
  · pexists q + u * t
    ptrans (m * q + r) + (m * u) * t
    · prw [he, hdq]
    · pring

end PA

extract_witness FOL.PA.divides_mul_right FOL.PA.quotient_ge FOL.PA.quotient_not_lt
  FOL.PA.remainder_self FOL.PA.remainder_total FOL.PA.remainder_unique
  FOL.PA.remainder_add_divisible

end

end FOL
