module

public import LeanPRA.Library.FOL.Arithmetic.Division
public import LeanPRA.Library.FOL.DSL.Tactic.Substitution
public meta import LeanPRA.Library.FOL.DSL.Tactic.SchemaApplication

/-!
# Bounded induction and finite bounds in PA

This module proves bounded induction, finite witness bounding, and the existence of a positive
common multiple on initial intervals in `PA`:

- `FOL.Arithmetic.boundedWitnesses p l b` states that every `i < l` has a witness `r ≤ b`
  satisfying `p(i, r)`.
- `FOL.PA.bounded_induction` propagates a unary formula code `p` up to `l` from `p[0]` and the step
  `∀ k, k < l → p[k] → p[S k]`.
- `FOL.PA.finite_witness_bound` proves that if every `i < l` has a witness for `p`, then a single
  bound `b` bounds witnesses for all `i < l`.
- `FOL.PA.finite_common_multiple` proves that every bound `l` has a positive common multiple `a`
  divisible by all `i` with `0 < i ≤ l`.

In `bounded_induction`, position `0` in `p` is the index variable. In `finite_witness_bound`,
position `0` in `p` is the witness `r` and position `1` is the index `i`. Later positions are
surrounding parameters.
-/

namespace FOL

pra

namespace Arithmetic

/-- `boundedWitnesses p l b` states that every index below `l` has a witness for `p` at most `b`,
defined as `∀ i, i < l → ∃ r, p(i, r) ∧ r ≤ b`. -/
fol_def boundedWitnesses over Arithmetic (p : formula of 2) (l b : term) : formula :=
  ∀ i, i < l → ∃ r, p(i, r) ∧ r ≤ b

end Arithmetic

namespace PA

open Arithmetic

/-- Induction in `PA` up to a bound `l`, requiring the step hypothesis only for `k < l`. -/
fol_theorem bounded_induction (p : Nat) : PA ⊢
    ∀ l n, ${p}[0] → (∀ k, k < l → ${p}[k] → ${p}[S k]) → n ≤ l → ${p}[n] := by
  pintro l n
  pinduction n with
  | zero =>
    pintro hzero hstep hbound
    passumption
  | succ k ih =>
    pintro hzero hstep hbound
    papply hstep[k]
    · papply Q.succ_le_iff_lt[k, l]
      passumption
    · papply ih
      · passumption
      · passumption
      · papply le_trans[k, S k, l]
        · pexact le_succ_self[k]
        · passumption

/-- In `PA`, if every index `i < l` has a witness for `p`, then some `b` bounds a witness for each
`i < l`. -/
fol_theorem finite_witness_bound (p : Nat) : PA ⊢
    ∀ l, (∀ i, i < l → ∃ r, ${p}[i, r]) → ∃ b, boundedWitnesses (p := ${p})(l, b) := by
  pintro l
  pinduction l with
  | zero =>
    pintro h
    pexists 0
    pintro i hi
    pexfalso
    papply Q.not_lt_zero[i]
    passumption
  | succ k ih =>
    pintro h
    phave hb : ∃ b, boundedWitnesses (p := ${p})(k, b)
    · papply ih
      pintro i hi
      papply h[i]
      papply lt_of_lt_of_le[i, k, S k]
      · passumption
      · pexact le_succ_self[k]
    · pcases hb with ⟨b, hbound⟩
      phave hr : ∃ r, ${p}[k, r]
      · papply h[k]
        pexact lt_succ_self[k]
      · pcases hr with ⟨r, hpr⟩
        pexists b + r
        pintro i hi
        phave cases : i < k ∨ i = k
        · papply lt_succ_iff_lt_or_eq[i, k]
          passumption
        · pcases cases with hik | he
          · phave hw : ∃ w, ${p}[i, w] ∧ w ≤ b
            · papply hbound[i]
              passumption
            · pcases hw with ⟨w, hwbody⟩
              pcases hwbody with ⟨hpw, hwb⟩
              pexists w
              pconstructor
              · passumption
              · papply le_add_of_le_right[w, b, r]
                passumption
          · pexists r
            pconstructor
            · psubst he
              passumption
            · pexact le_add_left[r, b]

/-- In `PA`, every bound `l` has a positive common multiple `a` divisible by all `i` with
`0 < i ≤ l`. -/
fol_theorem finite_common_multiple : PA ⊢
    ∀ l, ∃ a, 0 < a ∧ ∀ i, 0 < i → i ≤ l → divides(i, a) := by
  pintro l
  pinduction l with
  | zero =>
    pexists 1
    pconstructor
    · pexact Q.zero_lt_succ[0]
    · pintro i hi hle
      pexfalso
      papply not_lt_of_ge[0, i]
      · passumption
      · passumption
  | succ k ih =>
    pcases ih with ⟨a, ha⟩
    pcases ha with ⟨hapos, hall⟩
    pexists a * S k
    pconstructor
    · papply mul_pos_iff[a, S k]
      pconstructor
      · passumption
      · pexact Q.zero_lt_succ[k]
    · pintro i hi hle
      phave cases : i < S k ∨ i = S k
      · papply le_iff_lt_or_eq[i, S k]
        passumption
      · pcases cases with hik | he
        · phave hd : divides(i, a)
          · papply hall[i]
            · passumption
            · papply Q.lt_succ_iff_le[i, k]
              passumption
          · pcases hd with ⟨q, he⟩
            pexists q * S k
            prw [he, mul_assoc]
        · pexists a
          phave hc : a * S k = S k * a
          · pexact mul_comm[a, S k]
          · prw [he, hc]

end PA

extract_witness FOL.PA.bounded_induction FOL.PA.finite_common_multiple FOL.PA.finite_witness_bound

end

end FOL
