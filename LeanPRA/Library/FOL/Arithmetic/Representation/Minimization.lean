module

public import LeanPRA.Library.FOL.Arithmetic.Representation.Basic

/-!
# Choosing the least witness

- `Arithmetic.minGraph` chooses the output associated with a least witness of a formula.
- `Q.leastWitness_of_boundedAny` finds a least witness below a fixed numeral bound.
- `Q.minGraph_num_iff_of_le` proves numeralwise representation from one actual
  witness and correctness for witnesses below its code.
- `PA.minGraph_total` and `PA.minGraph_unique` prove totality and uniqueness under their
  stated existence and uniqueness hypotheses.

This least-witness condition is used in the representation proof for primitive recursion.
-/

namespace FOL

set_option pra.maxDepth 4096

pra

namespace Arithmetic

/-- `minGraph (p := p)(y, x)` states that `p(t, x, y)` holds for a witness `t` with every smaller
witness excluded. -/
fol_def minGraph over Arithmetic (p : formula of 3) (y x : term) : formula :=
  ∃ t, p(t, x, y) ∧ ∀ u z, u < t → ¬ p(u, x, z)

/-- `leastWitness (p := p)()` states that some value satisfies `p` and every smaller value is
excluded. -/
fol_def leastWitness over Arithmetic (p : formula of 1) : formula :=
  ∃ t, p(t) ∧ ∀ u, u < t → ¬ p(u)

end Arithmetic

namespace Q

open Arithmetic

fol_theorem leastWitness_of_finiteDisj (p n : Nat) : Q ⊢
    ${finiteDisj n p} → leastWitness (p := ${p})() := by
  sigma_induction n with
  | zero =>
    rw [finiteDisj_zero]
    pintro h
    pexfalso
    passumption
  | succ k ih =>
    rw [finiteDisj_succ]
    have bounded := boundedAny_iff_finiteDisj k p
    pintro h
    pcontradiction
    pintro hn
    phave earlier : ¬ ${finiteDisj k p}
    · pintro he
      papply hn
      papply ih
      passumption
    · phave forbidden : ¬ ${boundedAny k p}
      · pintro hb
        papply earlier
        papply bounded
        passumption
      · pcases h with he | hp
        · papply earlier
          passumption
        · papply hn
          pexists ${num k}
          pconstructor
          · passumption
          · pintro u hu hpu
            papply forbidden
            pexists u
            pconstructor
            · passumption
            · passumption

fol_theorem leastWitness_of_boundedAny (p n : Nat) : Q ⊢
    ${boundedAny n p} → leastWitness (p := ${p})() := by
  pintro h
  papply (leastWitness_of_finiteDisj p n)
  papply (boundedAny_iff_finiteDisj n p)
  passumption

fol_theorem eq_num_of_minGraph_of_le (p a b w : Nat) : Q ⊢
    ${p}[${num w}, ${num a}, ${num b}] → (∀ t y, t ≤ ${num w} → ${p}[t, ${num a}, y] → y = ${num b})
    → ∀ y, minGraph (p := ${p})(y, ${num a}) → y = ${num b} := by
  have alternatives := Provable.gen language isAxiom _ (le_or_gt_num w)
  pintro actual correct y h
  pcases h with ⟨t, ht⟩
  pcases ht with ⟨trace, minimal⟩
  pcases alternatives[t] with bound | above
  · papply correct[t, y]
    · passumption
    · passumption
  · pexfalso
    phave value : ∃ v, v = ${num b}
    · pexists ${num b}
      prefl
    · pcases value with ⟨v, hv⟩
      phave actualValue : ${p}[${num w}, ${num a}, v]
      · psubst hv
        passumption
      · papply minimal[${num w}, v]
        · passumption
        · passumption

fol_theorem minGraph_exists_of_num (p a b w : Nat) : Q ⊢
    ${p}[${num w}, ${num a}, ${num b}] → ∃ y, minGraph (p := ${p})(y, ${num a}) := by
  have least := leastWitness_of_boundedAny (fol_formula[Arithmetic |
      ∃ y, ${Formula.subst (liftSubst (shiftSubst language 1) language 3) language p}
        [${Term.var language 0}, ${num a}, y]]) (S w)
  have bound := lt_num w (S w) (_root_.le_refl (S w))
  rw [leastWitness, boundedAny] at least
  pintro actual
  phave hm : ∃ t, (∃ y, ${p}[t, ${num a}, y]) ∧ ∀ u, u < t → ¬ ∃ y, ${p}[u, ${num a}, y]
  · papply least
    phave value : ∃ v, v = ${num b}
    · pexists ${num b}
      prefl
    · pcases value with ⟨v, hv⟩
      pexists ${num w}
      pconstructor
      · pexact bound
      · pexists v
        psubst hv
        passumption
  · pcases hm with ⟨t, ht⟩
    pcases ht with ⟨value, minimal⟩
    pcases value with ⟨y, hy⟩
    pexists y
    pexists t
    pconstructor
    · passumption
    · pintro u z hu hz
      papply minimal[u]
      · passumption
      · pexists z
        passumption

fol_theorem minGraph_num_iff_of_le (p a b w : Nat) : Q ⊢
    ${p}[${num w}, ${num a}, ${num b}] → (∀ t y, t ≤ ${num w} → ${p}[t, ${num a}, y] → y = ${num b})
    → ∀ y, minGraph (p := ${p})(y, ${num a}) ↔ y = ${num b} := by
  have output := eq_num_of_minGraph_of_le p a b w
  have existence := minGraph_exists_of_num p a b w
  pintro actual correct
  phave all : ∀ y, minGraph (p := ${p})(y, ${num a}) → y = ${num b}
  · papply output
    · passumption
    · passumption
  · phave witnesses : ∃ v, minGraph (p := ${p})(v, ${num a})
    · papply existence
      passumption
    · pintro y
      pconstructor
      · pintro h
        papply all[y]
        passumption
      · pintro hy
        pcases witnesses with ⟨v, hv⟩
        phave he : v = ${num b}
        · papply all[v]
          passumption
        · phave hyve : y = v
          · prw [hy, he]
          · psubst hyve
            passumption

/-- A verified least numeral witness determines every output of the selected graph. -/
fol_theorem minGraph_num_iff (p a w b : Nat) : Q ⊢
    (∀ y, ${p}[${num w}, ${num a}, y] ↔ y = ${num b}) →
    (∀ u z, u < ${num w} → ¬ ${p}[u, ${num a}, z]) → ∀ y, minGraph (p := ${p})(y, ${num a}) ↔ y =
    ${num b} := by
  have alternatives := FOL.Provable.gen language isAxiom _ (ne_num_iff w)
  pintro actual earlier y
  pconstructor
  · pintro h
    pcases h with ⟨t, ht⟩
    pcases ht with ⟨trace, minimal⟩
    phave et : t = ${num w}
    · pcontradiction
      pintro hne
      phave cases : t < ${num w} ∨ ${num w} < t
      · papply alternatives[t]
        passumption
      · pcases cases with hlt | hgt
        · papply earlier[t, y]
          · passumption
          · passumption
        · phave value : ∃ v, v = ${num b}
          · pexists ${num b}
            prefl
          · pcases value with ⟨v, hv⟩
            papply minimal[${num w}, v]
            · passumption
            · papply actual[v]
              passumption
    · phave specialized : ∀ z, ${p}[t, ${num a}, z] ↔ z = ${num b}
      · psubst et
        passumption
      · papply specialized[y]
        passumption
  · pintro hy
    pexists ${num w}
    pconstructor
    · papply actual[y]
      passumption
    · pintro u z hu
      papply earlier[u, z]
      passumption

end Q

namespace PA

open Arithmetic

/-- A total witnessed graph remains total after selecting its least witness. -/
fol_theorem minGraph_total (p : Nat) : PA ⊢
    (∀ x, ∃ t y, ${p}[t, x, y]) → ∀ x, ∃ y, minGraph (p := ${p})(y, x) := by
  pintro total x
  phave selected : ∃ t, (∃ y, ${p}[t, x, y]) ∧
      ∀ u, u < t → ¬ ∃ z, ${p}[u, x, z]
  · papply exists_min (p := fun t => ∃ y, ${p}[t, x, y])
    pexact total[x]
  · pcases selected with ⟨t, ht⟩
    pcases ht with ⟨value, minimal⟩
    pcases value with ⟨y, hy⟩
    pexists y
    pexists t
    pconstructor
    · passumption
    · pintro u z hu hz
      papply minimal[u]
      · passumption
      · pexists z
        passumption

/-- Uniqueness across all witnesses implies uniqueness for the selected graph. -/
fol_theorem minGraph_unique (p : Nat) : PA ⊢
    (∀ x y z t u, ${p}[t, x, y] → ${p}[u, x, z] → y = z) → ∀ x y z, minGraph (p := ${p})(y, x) →
    minGraph (p := ${p})(z, x) → y = z := by
  pintro unique x y z hy hz
  pcases hy with ⟨t, ht⟩
  pcases ht with ⟨valueY, minimalY⟩
  pcases hz with ⟨u, hu⟩
  pcases hu with ⟨valueZ, minimalZ⟩
  papply unique[x, y, z, t, u]
  · passumption
  · passumption

end PA

extract_witness FOL.PA.minGraph_total FOL.PA.minGraph_unique FOL.Q.leastWitness_of_boundedAny
  FOL.Q.leastWitness_of_finiteDisj FOL.Q.minGraph_exists_of_num FOL.Q.eq_num_of_minGraph_of_le
  FOL.Q.minGraph_num_iff_of_le

end

end FOL
