module

public import LeanPRA.Library.FOL.Arithmetic.Bounded

/-!
# Chinese remainder construction for beta moduli in PA

- `Arithmetic.bezout(a, m)` supplies natural-number witnesses to `a * x = 1 + m * y`.
  `PA.bezout_one` and `PA.bezout_mul` build these witnesses for products of moduli.
- `PA.exists_remainder_add_mul` adds a multiple of one modulus to reach a prescribed remainder
  modulo another, using their Bézout relation.
- `Arithmetic.betaModulus(c, i)` is the modulus `1 + (i + 1) * c` at index `i`.
- `Arithmetic.remainderPrefix` records residues satisfying a formula along an initial interval.
- `PA.exists_divides_betaModulus_and_bezout` constructs multiples of processed moduli with
  Bézout identities for the remaining moduli.
- `PA.remainderPrefix_succ` extends a code by one admissible residue.
- `PA.chinese_remainder` constructs a code for a finite family of admissible residues.

The construction assumes pairwise oriented Bézout identities between beta moduli. The formula
parameter uses position zero for the residue and position one for its index. Modulus products
are constructed separately, and bounded induction extends the coded prefix.
-/

namespace FOL

set_option pra.maxDepth 2048

pra

namespace Arithmetic

/-- `bezout(a, m)` states that `a * x = 1 + m * y` for some natural numbers `x` and `y`.
The equation is oriented: the multiple of `a` exceeds the multiple of `m` by one.
In particular, `bezout(0, m)` is always false.

These witnesses supply the modular inverse used in the Chinese remainder construction.
They let `exists_remainder_add_mul` choose a multiple of `a` to add to a number so that it has a
prescribed remainder modulo `m`, while preserving its remainders modulo divisors of `a`.
Using this witness condition directly lets the construction work in natural-number arithmetic
before developing general gcd theory and Bézout's theorem for coprime numbers. -/
fol_def bezout over Arithmetic (a m : term) : formula :=
  ∃ x y, a * x = 1 + m * y

/-- `betaModulus(c, i)` is the modulus `S (S i * c)` at position `i` of a beta code with parameter
`c`. -/
fol_def betaModulus over Arithmetic (c i : term) : term := S (S i * c)

/-- `remainderPrefix (p := p)(c, n, b)` states that `b` supplies a residue satisfying `p` at each
index below `n`. -/
fol_def remainderPrefix over Arithmetic (p : formula of 2) (c n b : term) : formula :=
  ∀ i, i < n → ∃ r, p(i, r) ∧ remainder(r, b, betaModulus(c, i))

end Arithmetic

namespace PA

open Arithmetic

fol_theorem bezout_one : PA ⊢ ∀ m, bezout(1, m) := by
  pintro m
  pexists 1
  pexists 0
  pring

fol_theorem bezout_mul : PA ⊢
    ∀ a b m, bezout(a, m) → bezout(b, m) → bezout(a * b, m) := by
  pintro a b m ha hb
  pcases ha with ⟨x, hx⟩
  pcases hx with ⟨y, he⟩
  pcases hb with ⟨u, hu⟩
  pcases hu with ⟨v, hf⟩
  pexists x * u
  pexists y + v + m * y * v
  ptrans (a * x) * (b * u)
  · pring
  · ptrans (1 + m * y) * (1 + m * v)
    · prw [he, hf]
    · pring

/-- Adjust a residue using a Bézout identity and a multiple with the required remainder. -/
fol_theorem remainder_adjust_eq : PA ⊢ ∀ b d m r x y w,
    d * x = 1 + m * y → b + w = m * b + r → b + d * (x * w) = m * (b + y * w) + r := by
  pintro b d m r x y w he hw
  ptrans b + (d * x) * w
  · psymm
    prw [mul_assoc]
  · ptrans (b + w) + m * (y * w)
    · prw [he, right_distrib, one_mul, mul_assoc, add_assoc]
    · ptrans (m * b + m * (y * w)) + r
      · ptrans (m * b + r) + m * (y * w)
        · prw [hw]
        · pexact add_right_comm[m * b, r, m * (y * w)]
      · prw [left_distrib]

/-- Given `bezout d m` and `r < m`, some multiple `d * t` adjusts `b` so that
`b + d * t` has remainder `r` modulo `m`. -/
fol_theorem exists_remainder_add_mul : PA ⊢
    ∀ b d m r, 0 < m → r < m → bezout(d, m) → ∃ t,
    remainder(r, b + d * t, m) := by
  pintro b d m r hm hr hd
  phave hex : ∃ k, m = S k
  · papply positive_predecessor[m]
    passumption
  · pcases hex with ⟨k, hk⟩
    pcases hd with ⟨x, hx⟩
    pcases hx with ⟨y, he⟩
    pexists x * (r + k * b)
    pconstructor
    · passumption
    · pexists b + y * (r + k * b)
      papply remainder_adjust_eq[b, d, m, r, x, y, r + k * b]
      · pexact he
      · ptrans S k * b + r
        · pring
        · prw [hk]

fol_theorem remainderPrefix_succ_add_mul (p : Nat) : PA ⊢
    ∀ c k b d t r, remainderPrefix (p := ${p})(c, k, b) →
    (∀ i, i < k → divides(betaModulus(c, i), d)) → ${p}[k, r] →
    remainder(r, b + d * t, betaModulus(c, k)) →
    remainderPrefix (p := ${p})(c, S k, b + d * t) := by
  pintro c k b d t r hcode hmultiple hr hrem i hi
  phave cases : i < k ∨ i = k
  · papply lt_succ_iff_lt_or_eq[i, k]
    passumption
  · pcases cases with hik | he
    · phave hex : ∃ w, ${p}[i, w] ∧
          remainder(w, b, betaModulus(c, i))
      · papply hcode[i]
        passumption
      · pcases hex with ⟨w, hw⟩
        pcases hw with ⟨hpw, hremw⟩
        pexists w
        pconstructor
        · passumption
        · papply remainder_add_divisible[w, b, betaModulus(c, i), d, t]
          · passumption
          · papply hmultiple[i]
            passumption
    · psubst he
      pexists r
      pconstructor
      · passumption
      · passumption

fol_theorem divides_betaModulus_mul_of_lt_succ : PA ⊢
    ∀ c k d, (∀ i, i < k → divides(betaModulus(c, i), d)) →
    (∀ i, i < S k → divides(betaModulus(c, i), d * betaModulus(c, k))) := by
  pintro c k d h i hi
  phave cases : i < k ∨ i = k
  · papply lt_succ_iff_lt_or_eq[i, k]
    passumption
  · pcases cases with hik | he
    · papply divides_mul_right[betaModulus(c, i), d,
        betaModulus(c, k)]
      papply h[i]
      passumption
    · psubst he
      pexists d
      pexact mul_comm[d, betaModulus(c, k)]

fol_theorem bezout_mul_betaModulus_of_le : PA ⊢
    ∀ c k l d, (∀ i j, i < j → j < l → bezout(betaModulus(c, i),
    betaModulus(c, j))) → (∀ j, k ≤ j → j < l → bezout(d, betaModulus(c, j))) →
    (∀ j, S k ≤ j → j < l → bezout(d * betaModulus(c, k), betaModulus(c, j))) := by
  pintro c k l d hpairs hfuture j hkj hjl
  papply bezout_mul[d, betaModulus(c, k), betaModulus(c, j)]
  · papply hfuture[j]
    · papply le_trans[k, S k, j]
      · pexact le_succ_self[k]
      · passumption
    · passumption
  · papply hpairs[k, j]
    · papply Q.succ_le_iff_lt[k, j]
      passumption
    · passumption

/-- Pairwise Bézout relations give the multiplier needed at each stage of finite coding. -/
fol_theorem exists_divides_betaModulus_and_bezout : PA ⊢
    ∀ c l n, (∀ i j, i < j → j < l → bezout(betaModulus(c, i),
    betaModulus(c, j))) → ∃ d, (∀ i, i < n → divides(betaModulus(c, i), d)) ∧
    (∀ j, n ≤ j → j < l → bezout(d, betaModulus(c, j))) := by
  pintro c l n
  pinduction n with
  | zero =>
    pintro hpairs
    pexists 1
    pconstructor
    · pintro i hi
      pexfalso
      papply Q.not_lt_zero[i]
      passumption
    · pintro j hj hjl
      pexact bezout_one[betaModulus(c, j)]
  | succ k ih =>
    pintro hpairs
    phave hex : ∃ d, (∀ i, i < k → divides(betaModulus(c, i), d)) ∧
        (∀ j, k ≤ j → j < l → bezout(d, betaModulus(c, j)))
    · papply ih
      passumption
    · pcases hex with ⟨d, hd⟩
      pexists d * betaModulus(c, k)
      pconstructor
      · papply divides_betaModulus_mul_of_lt_succ[c, k, d]
        papply hd
      · papply bezout_mul_betaModulus_of_le[c, k, l, d]
        · passumption
        · papply hd

fol_theorem remainderPrefix_zero (p : Nat) : PA ⊢
    ∀ c, ∃ b, remainderPrefix (p := ${p})(c, 0, b) := by
  pintro c
  pexists 0
  pintro i hi
  pexfalso
  papply Q.not_lt_zero[i]
  passumption

fol_theorem remainderPrefix_succ_of_bezout (p : Nat) : PA ⊢
    ∀ c k b d r, remainderPrefix (p := ${p})(c, k, b) →
    (∀ i, i < k → divides(betaModulus(c, i), d)) →
    bezout(d, betaModulus(c, k)) → ${p}[k, r] → r <
    betaModulus(c, k) → ∃ b, remainderPrefix (p := ${p})(c, S k, b) := by
  pintro c k b d r hcode hmultiple hbezout hpr hrlt
  phave hadjust : ∃ t, remainder(r, b + d * t, betaModulus(c, k))
  · papply exists_remainder_add_mul[b, d, betaModulus(c, k), r]
    · pexact Q.zero_lt_succ[S k * c]
    · passumption
    · passumption
  · pcases hadjust with ⟨t, ht⟩
    pexists b + d * t
    papply PA.remainderPrefix_succ_add_mul (p := fun i r => ${p}[i, r])[c, k, b, d, t, r]
    · passumption
    · passumption
    · passumption
    · passumption

fol_theorem remainderPrefix_succ (p : Nat) : PA ⊢
    ∀ c l k, (∀ i j, i < j → j < l → bezout(betaModulus(c, i),
    betaModulus(c, j))) → k < l → (∃ r, ${p}[k, r] ∧ r < betaModulus(c, k)) →
    (∃ b, remainderPrefix (p := ${p})(c, k, b)) → ∃ b, remainderPrefix
    (p := ${p})(c, S k, b) := by
  pintro c l k hpairs hkl hchoice hcode
  pcases hcode with ⟨b, hb⟩
  phave hdex : ∃ d, (∀ i, i < k → divides(betaModulus(c, i), d)) ∧
      (∀ j, k ≤ j → j < l → bezout(d, betaModulus(c, j)))
  · papply exists_divides_betaModulus_and_bezout[c, l, k]
    passumption
  · pcases hdex with ⟨d, hd⟩
    pcases hd with ⟨hmultiple, hfuture⟩
    pcases hchoice with ⟨r, hr⟩
    papply PA.remainderPrefix_succ_of_bezout (p := fun i r => ${p}[i, r])[c, k, b, d, r]
    · passumption
    · passumption
    · papply hfuture[k]
      · pexact le_refl[k]
      · passumption
    · papply hr
    · papply hr

fol_theorem remainderPrefix_total (p : Nat) : PA ⊢
    ∀ c l n, (∀ i, i < l → ∃ r, ${p}[i, r] ∧ r < betaModulus(c, i)) → (∀ i j, i < j → j <
    l → bezout(betaModulus(c, i), betaModulus(c, j))) → n
    ≤ l → ∃ b, remainderPrefix (p := ${p})(c, n, b) := by
  pintro c l n hchoices hpairs hn
  papply PA.bounded_induction
    (p := fun k => ∃ b, remainderPrefix (p := ${p})(c, k, b))[l, n]
  · papply PA.remainderPrefix_zero (p := fun i r => ${p}[i, r])[c]
  · pintro k hkl ih
    papply PA.remainderPrefix_succ (p := fun i r => ${p}[i, r])[c, l, k]
    · passumption
    · passumption
    · papply hchoices[k]
      passumption
    · passumption
  · passumption

/-- PA realizes a finite family of admissible residues by one number. -/
fol_theorem chinese_remainder (p : Nat) : PA ⊢
    ∀ c l, (∀ i, i < l → ∃ r, ${p}[i, r] ∧ r < betaModulus(c, i)) → (∀ i j, i < j → j < l
    → bezout(betaModulus(c, i), betaModulus(c, j))) → ∃ b,
    remainderPrefix (p := ${p})(c, l, b) := by
  pintro c l hchoices hpairs
  papply PA.remainderPrefix_total (p := fun i r => ${p}[i, r])[c, l, l]
  · passumption
  · passumption
  · pexact le_refl[l]

end PA

extract_witness FOL.PA.chinese_remainder FOL.PA.remainderPrefix_succ_add_mul
  FOL.PA.remainderPrefix_succ FOL.PA.remainderPrefix_succ_of_bezout FOL.PA.remainderPrefix_total
  FOL.PA.remainderPrefix_zero FOL.PA.bezout_mul_betaModulus_of_le
  FOL.PA.exists_divides_betaModulus_and_bezout FOL.PA.divides_betaModulus_mul_of_lt_succ
  FOL.PA.exists_remainder_add_mul FOL.PA.bezout_mul FOL.PA.bezout_one

end

end FOL
