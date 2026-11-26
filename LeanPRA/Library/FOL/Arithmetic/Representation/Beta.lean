module

public import LeanPRA.Library.FOL.Arithmetic.Representation.ChineseRemainder
public import LeanPRA.Library.FOL.Arithmetic.Representation.Basic
public import LeanPRA.Library.Nat.Beta

/-!
# Beta coding and representation of finite sequences

- `Arithmetic.beta` is the remainder graph for beta codes; `PA.beta_total` and `PA.beta_unique`
  prove existence and uniqueness of its values.
- `PA.bezout_betaModulus_of_lt` supplies Bézout identities for the chosen moduli.
- `PA.beta_comprehension` codes witnesses of any formula on a finite interval.
- `PA.beta_extend` preserves every earlier entry of a finite beta sequence and
  prescribes its next entry. Its derivation uses beta comprehension.
- `Arithmetic.betaBounded` bounds the quotient for numeral checking in Q. PA proves its equivalence
  with the usual beta relation and proves the same extension property.
- `Q.betaBounded_num_iff` identifies the decoded value at each numeral code and index.
-/

namespace FOL

set_option pra.maxDepth 4096

pra

namespace Arithmetic

/-- `beta(r, b, c, i)` states that `r` is the value of the beta code `(b, c)` at index `i`. -/
fol_def beta over Arithmetic : formula of 4 := fun r b c i =>
  remainder(r, b, Arithmetic.betaModulus(c, i))

end Arithmetic

namespace PA

open Arithmetic

/-- If `a * x = b * y` and `x = y + b²`, then `x` is a Bézout coefficient for
`S a` modulo `S b`. The other coefficient is the predecessor of `y + b`. -/
fol_theorem bezout_succ_of_square_difference : PA ⊢
    ∀ a b x y, 0 < b → a * x = b * y → x = y + b * b → bezout(S a, S b) := by
  pintro a b x y hb hmul hdiff
  phave hpos : 0 < y + b
  · papply lt_of_lt_of_le[0, b, y + b]
    · pexact hb
    · pexact le_add_left[b, y]
  · phave hp : ∃ z, y + b = S z
    · papply positive_predecessor[y + b]
      pexact hpos
    · pcases hp with ⟨z, hz⟩
      pexists x
      pexists z
      papply add_right_cancel[S a * x, 1 + S b * z, S b]
      ptrans a * x + x + S b
      · prw [succ_mul]
      · ptrans b * y + (y + b * b) + S b
        · prw [hmul, hdiff]
        · ptrans 1 + S b * (y + b)
          · pring
          · prw [hz, Q.mul_succ, add_assoc]

fol_theorem bezout_succ_mul_of_mul_eq_add : PA ⊢
    ∀ u v c t, 0 < v * c → v * t = u * t + c → bezout(S (u * c), S (v * c)) := by
  pintro u v c t hpos hstep
  papply bezout_succ_of_square_difference[u * c, v * c,
    (v * v * c) * (v * t), (v * v * c) * (u * t)]
  · pexact hpos
  · pring
  · ptrans (v * v * c) * (u * t + c)
    · prw [hstep]
    · pring

/-- The beta moduli at distinct increasing indices admit an oriented Bézout identity. -/
fol_theorem bezout_betaModulus_of_lt : PA ⊢
    ∀ i j c, 0 < c → i < j → (∀ g, 0 < g → g ≤ j → divides(g, c)) →
    bezout(Arithmetic.betaModulus(c, i), Arithmetic.betaModulus(c, j)) := by
  pintro i j c hc hij hdiv
  pcases hij with ⟨k, hk⟩
  phave hj : j = i + S k
  · ptrans k + S i
    · psymm
      passumption
    · pring
  · phave hg : S k ≤ j
    · pexists i
      prw [hj]
    · phave hd : divides(S k, c)
      · papply hdiv[S k]
        · pexact Q.zero_lt_succ[k]
        · passumption
      · pcases hd with ⟨t, ht⟩
        papply bezout_succ_mul_of_mul_eq_add[S i, S j, c, t]
        · papply mul_pos_iff[S j, c]
          pconstructor
          · pexact Q.zero_lt_succ[j]
          · passumption
        · ptrans S (i + S k) * t
          · prw [hj]
          · ptrans S i * t + S k * t
            · pring
            · prw [ht]

/-- Every beta code has a value at every index. -/
fol_theorem beta_total : PA ⊢ ∀ b c i, ∃ r, Arithmetic.beta(r, b, c, i) := by
  pintro b c i
  papply remainder_total[Arithmetic.betaModulus(c, i), b]
  pexact Q.zero_lt_succ[S i * c]

/-- A beta code has at most one value at each index. -/
fol_theorem beta_unique : PA ⊢
    ∀ r s b c i, Arithmetic.beta(r, b, c, i) → Arithmetic.beta(s, b, c, i) → r = s := by
  pintro r s b c i hr hs
  papply remainder_unique[r, s, b, Arithmetic.betaModulus(c, i)]
  · passumption
  · passumption

fol_theorem lt_betaModulus_mul_succ_of_le : PA ⊢
    ∀ a b i r, 0 < a → r ≤ b → r < Arithmetic.betaModulus(a * S b, i) := by
  pintro a b i r ha hr
  papply Q.lt_succ_iff_le[r, S i * (a * S b)]
  papply le_trans[r, b, S i * (a * S b)]
  · passumption
  · papply le_trans[b, S b, S i * (a * S b)]
    · pexact le_succ_self[b]
    · papply le_trans[S b, a * S b, S i * (a * S b)]
      · papply le_mul_left[S b, a]
        passumption
      · papply le_mul_left[a * S b, S i]
        pexact Q.zero_lt_succ[i]

fol_theorem bezout_betaModulus_mul_succ_of_lt : PA ⊢
    ∀ a b l, 0 < a → (∀ g, 0 < g → g ≤ l → divides(g, a)) → ∀ i j, i < j → j < l →
    bezout(Arithmetic.betaModulus(a * S b, i), Arithmetic.betaModulus(a * S b, j)) := by
  pintro a b l ha hdiv i j hij hjl
  papply bezout_betaModulus_of_lt[i, j, a * S b]
  · papply mul_pos_iff[a, S b]
    pconstructor
    · passumption
    · pexact Q.zero_lt_succ[b]
  · passumption
  · pintro g hg hgj
    papply divides_mul_right[g, a, S b]
    papply hdiv[g]
    · passumption
    · papply le_trans[g, j, l]
      · passumption
      · papply le_of_lt[j, l]
        passumption

/-- Every finite family of inhabited definable sets has a beta code selecting one value
from each set. Each set may have several witnesses. -/
fol_theorem beta_comprehension (p : formula of 2) : PA ⊢
    ∀ l, (∀ i, i < l → ∃ r, p(i, r)) → ∃ b c, ∀ i, i < l → ∃ r, p(i, r) ∧
    Arithmetic.beta(r, b, c, i) := by
  pintro l h
  phave hbound : ∃ bound, (boundedWitnesses p)(l, bound)
  · papply (finite_witness_bound (fun i r => p(i, r)))[l]
    passumption
  · pcases hbound with ⟨bound, hwitnesses⟩
    pcases finite_common_multiple[l] with ⟨a, ha⟩
    pcases ha with ⟨hapos, hdiv⟩
    phave hcode : ∃ b, (remainderPrefix p)(a * S bound, l, b)
    · papply (chinese_remainder (fun i r => p(i, r)))[a * S bound, l]
      · pintro i hi
        phave hex : ∃ r, p(i, r) ∧ r ≤ bound
        · papply hwitnesses[i]
          passumption
        · pcases hex with ⟨r, hr⟩
          pcases hr with ⟨hpr, hrbound⟩
          pexists r
          pconstructor
          · passumption
          · papply lt_betaModulus_mul_succ_of_le[a, bound, i, r]
            · passumption
            · passumption
      · papply bezout_betaModulus_mul_succ_of_lt[a, bound, l]
        · passumption
        · passumption
    · pcases hcode with ⟨b, hb⟩
      pexists b
      pexists a * S bound
      passumption

end PA

namespace Arithmetic

/-- `betaBounded(r, b, c, i)` is the beta relation with its quotient bounded by `b`. -/
fol_def betaBounded over Arithmetic : formula of 4 := fun r b c i =>
  r < Arithmetic.betaModulus(c, i) ∧ ∃ q, q ≤ b ∧ b = Arithmetic.betaModulus(c, i) * q + r

end Arithmetic

namespace PA

open Arithmetic

/-- A finite beta sequence can be extended by one value, preserving all earlier entries. -/
fol_theorem beta_extend : PA ⊢
    ∀ b c n z, ∃ d e, (∀ i r, i < n → Arithmetic.beta(r, b, c, i) → Arithmetic.beta(r, d, e, i)) ∧
    Arithmetic.beta(z, d, e, n) := by
  pintro b c n z
  phave extension : ∃ d e, ∀ i, i < S n → ∃ r,
      ((i < n ∧ Arithmetic.beta(r, b, c, i)) ∨ (i = n ∧ r = z)) ∧
        Arithmetic.beta(r, d, e, i)
  · papply (beta_comprehension
      (fun i r => (i < n ∧ Arithmetic.beta(r, b, c, i)) ∨ (i = n ∧ r = z)))[S n]
    pintro i hi
    phave cases : i < n ∨ i = n
    · papply lt_succ_iff_lt_or_eq[i, n]
      passumption
    · pcases cases with hin | he
      · pcases beta_total[b, c, i] with ⟨r, hr⟩
        pexists r
        pleft
        pconstructor
        · passumption
        · passumption
      · pexists z
        pright
        pconstructor
        · passumption
        · prefl
  · pcases extension with ⟨d, e, hall⟩
    pexists d
    pexists e
    pconstructor
    · pintro i r hin hr
      phave selected : ∃ s,
          ((i < n ∧ Arithmetic.beta(s, b, c, i)) ∨ (i = n ∧ s = z)) ∧
            Arithmetic.beta(s, d, e, i)
      · papply hall[i]
        papply lt_succ_of_lt[i, n]
        passumption
      · pcases selected with ⟨s, choice, value⟩
        pcases choice with hold | hend
        · pcases hold with ⟨hi, hs⟩
          phave eq : r = s
          · papply beta_unique[r, s, b, c, i]
            · passumption
            · passumption
          · psubst eq
            passumption
        · pcases hend with ⟨hi, hs⟩
          pexfalso
          papply not_lt_of_ge[i, n]
          · psubst hi
            pexact le_refl[n]
          · passumption
    · phave selected : ∃ r,
          ((n < n ∧ Arithmetic.beta(r, b, c, n)) ∨ (n = n ∧ r = z)) ∧
            Arithmetic.beta(r, d, e, n)
      · papply hall[n]
        pexact lt_succ_self[n]
      · pcases selected with ⟨r, choice, value⟩
        pcases choice with hold | hend
        · pcases hold with ⟨hi, hr⟩
          pexfalso
          papply not_lt_of_ge[n, n]
          · pexact le_refl[n]
          · passumption
        · pcases hend with ⟨hi, hr⟩
          phave eq : z = r
          · psymm
            passumption
          · psubst eq
            passumption

fol_theorem betaBounded_iff : PA ⊢
    ∀ r b c i, betaBounded(r, b, c, i) ↔ Arithmetic.beta(r, b, c, i) := by
  pintro r b c i
  pconstructor
  · pintro h
    pcases h with ⟨hr, hq⟩
    pcases hq with ⟨q, hq⟩
    pcases hq with ⟨hqb, he⟩
    pconstructor
    · passumption
    · pexists q
      passumption
  · pintro h
    pcases h with ⟨hr, hq⟩
    pcases hq with ⟨q, he⟩
    pconstructor
    · passumption
    · pexists q
      pconstructor
      · papply le_of_eq_right[q, Arithmetic.betaModulus(c, i) * q + r, b]
        · papply le_trans[q, Arithmetic.betaModulus(c, i) * q,
            Arithmetic.betaModulus(c, i) * q + r]
          · papply le_mul_left[q, Arithmetic.betaModulus(c, i)]
            pexact Q.zero_lt_succ[S i * c]
          · pexact le_add_right[Arithmetic.betaModulus(c, i) * q, r]
        · psymm
          passumption
      · passumption

fol_theorem betaBounded_total : PA ⊢ ∀ b c i, ∃ r, betaBounded(r, b, c, i) := by
  pintro b c i
  pcases beta_total[b, c, i] with ⟨r, hr⟩
  pexists r
  papply betaBounded_iff[r, b, c, i]
  passumption

fol_theorem betaBounded_unique : PA ⊢
    ∀ r s b c i, betaBounded(r, b, c, i) → betaBounded(s, b, c, i) → r = s :=
    by
  pintro r s b c i hr hs
  papply beta_unique[r, s, b, c, i]
  · papply betaBounded_iff[r, b, c, i]
    passumption
  · papply betaBounded_iff[s, b, c, i]
    passumption

fol_theorem betaBounded_extend : PA ⊢
    ∀ b c n z, ∃ d e,
    (∀ i r, i < n → betaBounded(r, b, c, i) → betaBounded(r, d, e, i)) ∧
    betaBounded(z, d, e, n) := by
  pintro b c n z
  pcases beta_extend[b, c, n, z] with ⟨d, hd⟩
  pcases hd with ⟨e, he⟩
  pcases he with ⟨earlier, last⟩
  pexists d
  pexists e
  pconstructor
  · pintro i r hi hr
    papply betaBounded_iff[r, d, e, i]
    papply earlier[i, r]
    · passumption
    · papply betaBounded_iff[r, b, c, i]
      passumption
  · papply betaBounded_iff[z, d, e, n]
    passumption

end PA

namespace Q

open Arithmetic

fol_theorem betaModulus_num (c i : Nat) : Q ⊢
    Arithmetic.betaModulus(${num c}, ${num i}) = ${num (S (S i * c))} := by
  have h := mul_num (S i) c
  rw [num_succ] at h
  rw [num_succ]
  prw [h]

fol_theorem betaBounded_num (b c i : Nat) : Q ⊢
    betaBounded(${num (_root_.beta b c i)}, ${num b}, ${num c}, ${num i}) := by
  have hr := lt_num (_root_.beta b c i) (S (S i * c)) (_root_.beta_lt b c i)
  have hq := le_num (b / S (S i * c)) b (div_le_self b (S (S i * c)))
  have hm := betaModulus_num c i
  have hp := mul_num (S (S i * c)) (b / S (S i * c))
  have hs := add_num (S (S i * c) * (b / S (S i * c))) (_root_.beta b c i)
  have he : S (S i * c) * (b / S (S i * c)) + _root_.beta b c i = b :=
    div_mod b (S (S i * c))
  rw [he] at hs
  pconstructor
  · pcases hr with ⟨w, hw⟩
    pexists w
    prw [hw, hm]
  · pexists ${num (b / S (S i * c))}
    pconstructor
    · pexact hq
    · prw [hm, hp, hs]

theorem num_ne_betaModulus_mul_add (b c i r q : Nat) :
    r < S (S i * c) → ¬ r = _root_.beta b c i → (Q ⊢ ${Formula.instantiate language
    (fol_formula[Arithmetic |
      ${num b} ≠ Arithmetic.betaModulus(${num c}, ${num i}) *
        ${Term.var language 0} + ${num r}]) (num q)}) := by
  intro hr hne
  have hn : ¬ b = S (S i * c) * q + r := by
    intro he
    have value := and_right (div_mod_unique b (S (S i * c)) q r
      (_root_.succ_ne_zero (S i * c)) (eq_symm he) hr)
    exact hne (eq_symm value)
  have unequal := num_ne b (S (S i * c) * q + r) hn
  have hm := betaModulus_num c i
  have hp := mul_num (S (S i * c)) q
  have hs := add_num (S (S i * c) * q) r
  pintro he
  papply unequal
  prw [he, hm, hp, hs]

extract_witness num_ne_betaModulus_mul_add

theorem not_betaBounded_num (b c i r : Nat) :
    r < S (S i * c) → ¬ r = _root_.beta b c i →
    (Q ⊢ ¬ betaBounded(${num r}, ${num b}, ${num c}, ${num i})) := by
  intro hr hne
  have all := boundedAll_of_isProofOf
    (fol_formula[Arithmetic |
      ${num b} ≠ Arithmetic.betaModulus(${num c}, ${num i}) *
        ${Term.var language 0} + ${num r}]) (S b)
    (fun q => num_ne_betaModulus_mul_add.witness b c i r q)
    (fun q hq => num_ne_betaModulus_mul_add.witness_correct b c i r q hr hne)
  rw [boundedAll, num_succ b] at all
  pintro h
  pcases h with ⟨hlt, hq⟩
  pcases hq with ⟨q, hq⟩
  pcases hq with ⟨hqb, he⟩
  papply all[q]
  · papply lt_succ_iff_le[q, ${num b}]
    passumption
  · passumption

theorem betaBounded_num_iff_of_eq (b c i r : Nat) :
    r = _root_.beta b c i →
    (Q ⊢ ${Formula.instantiate language (fol_formula[Arithmetic |
      betaBounded(${Term.var language 0}, ${num b}, ${num c}, ${num i}) ↔
        ${Term.var language 0} = ${num (_root_.beta b c i)}]) (num r)}) := by
  intro h
  rw [h]
  pconstructor
  · pintro hr
    prefl
  · pintro hr
    pexact betaBounded_num b c i

theorem betaBounded_num_iff_of_ne (b c i r : Nat) :
    r < S (S i * c) → ¬ r = _root_.beta b c i →
    (Q ⊢ ${Formula.instantiate language (fol_formula[Arithmetic |
      betaBounded(${Term.var language 0}, ${num b}, ${num c}, ${num i}) ↔
        ${Term.var language 0} = ${num (_root_.beta b c i)}]) (num r)}) := by
  intro hr hne
  have hn := not_betaBounded_num b c i r hr hne
  have neq := num_ne r (_root_.beta b c i) hne
  pconstructor
  · pintro h
    pexfalso
    papply hn
    passumption
  · pintro h
    pexfalso
    papply neq
    passumption

extract_witness betaBounded_num_iff_of_eq betaBounded_num_iff_of_ne

/-- `betaBoundedNumIffProof b c i r` builds the Q proof of the beta equivalence for a numeral
remainder `r` below the modulus. -/
def betaBoundedNumIffProof (b c i r : Nat) : Nat := ite (eqb r (_root_.beta b c i))
  (betaBounded_num_iff_of_eq.witness b c i r) (betaBounded_num_iff_of_ne.witness b c i r)

theorem betaBoundedNumIffProof_isProofOf (b c i r : Nat) :
    r < S (S i * c) → IsProofOf language isAxiom
    (Formula.instantiate language (fol_formula[Arithmetic |
      betaBounded(${Term.var language 0}, ${num b}, ${num c}, ${num i}) ↔
        ${Term.var language 0} = ${num (_root_.beta b c i)}]) (num r))
    (betaBoundedNumIffProof b c i r) := by
  intro hr
  by_cases h : r = _root_.beta b c i
  · rw [betaBoundedNumIffProof, and_right (eqb_eq_one r (_root_.beta b c i)) h]
    exact betaBounded_num_iff_of_eq.witness_correct b c i r h
  · rw [betaBoundedNumIffProof, and_right (eqb_eq_zero r (_root_.beta b c i)) h]
    exact betaBounded_num_iff_of_ne.witness_correct b c i r hr h

fol_theorem betaBounded_iff_of_lt (b c i : Nat) : Q ⊢
    ∀ r, r < ${num (S (S i * c))} →
    (betaBounded(r, ${num b}, ${num c}, ${num i}) ↔ r = ${num (_root_.beta b c i)}) := by
  have all := boundedAll_of_isProofOf (fol_formula[Arithmetic |
      betaBounded(${Term.var language 0}, ${num b}, ${num c}, ${num i}) ↔
        ${Term.var language 0} = ${num (_root_.beta b c i)}])
    (S (S i * c)) (fun r => betaBoundedNumIffProof b c i r)
    (fun r hr => betaBoundedNumIffProof_isProofOf b c i r hr)
  rw [boundedAll] at all
  pexact all

fol_theorem betaBounded_num_iff (b c i : Nat) : Q ⊢
    ∀ r, betaBounded(r, ${num b}, ${num c}, ${num i}) ↔ r = ${num (_root_.beta b c i)} :=
    by
  have bounded := betaBounded_iff_of_lt b c i
  have hm := betaModulus_num c i
  pintro r
  pconstructor
  · pintro h
    phave bound : r < ${num (S (S i * c))}
    · pcases h with ⟨hr, hq⟩
      pcases hr with ⟨w, hw⟩
      pexists w
      prw [hw, hm]
    · papply bounded[r]
      · passumption
      · passumption
  · pintro h
    psubst h
    pexact betaBounded_num b c i

end Q

extract_witness FOL.PA.betaBounded_extend FOL.PA.betaBounded_iff FOL.PA.betaBounded_unique
  FOL.PA.beta_extend FOL.Q.betaBounded_iff_of_lt FOL.Q.betaBounded_num_iff

extract_witness FOL.PA.beta_comprehension FOL.PA.bezout_betaModulus_of_lt
  FOL.PA.bezout_betaModulus_mul_succ_of_lt FOL.PA.lt_betaModulus_mul_succ_of_le FOL.PA.beta_total
  FOL.PA.beta_unique FOL.PA.bezout_succ_mul_of_mul_eq_add

end

end FOL
