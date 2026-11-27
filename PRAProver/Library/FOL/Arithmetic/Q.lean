module

public import PRAProver.Library.FOL.Common.Proof.Congruence
public import PRAProver.Library.FOL.Arithmetic.Numeral

/-!
# Arithmetic in Q

This module develops basic arithmetic, numeral computation, and bounded quantifier expansions as
checked derivations in Robinson arithmetic (`Q`).

- `Arithmetic.eqNumDisj`, `Arithmetic.finiteConj`, and `Arithmetic.finiteDisj` build
  finite disjunctions and conjunctions over the numerals below a natural number `n`.
- `Arithmetic.boundedAll` and `Arithmetic.boundedAny` express universal and existential
  quantification bounded by `num n`.
- `Q.succ_inj_iff`, `Q.add_eq_zero_iff`, and `Q.succ_le_succ_iff` establish basic
  equality and order properties in `Q`.
- `Q.add_num` and `Q.mul_num` compute sums and products of numerals in `Q` by induction on
  their PRA parameters, and `Q.le_num`, `Q.lt_num`, `Q.not_le_num`, `Q.not_lt_num`,
  and `Q.num_ne` reflect numerical comparisons into `Q` proofs.
- `Q.lt_num_iff` and `Q.le_num_iff` characterize order below a numeral as a finite
  disjunction of equations, and `Q.lt_or_ge_num` and `Q.ne_num_iff` split comparisons with
  a numeral.
- `Q.boundedAll_iff_finiteConj` and `Q.boundedAny_iff_finiteDisj` prove in `Q` that
  numeral-bounded quantifiers are equivalent to finite conjunctions and disjunctions.
-/

namespace FOL

pra

namespace Arithmetic

/-- `eqNumDisj n t` is the finite disjunction `⊥ ∨ t = num 0 ∨ … ∨ t = num (n - 1)` for a
numerical bound `n` and an arithmetic term `t`. -/
fol_def eqNumDisj over Arithmetic (n : Nat) : term → formula := fun t =>
  ${primrec FOL.Formula.falsum
    (fun i A => FOL.Formula.disj A (FOL.Formula.equal language t (num i))) n}

theorem eqNumDisj_zero : ∀ t, eqNumDisj 0 t = FOL.Formula.falsum := fun t => rfl

theorem eqNumDisj_succ :
    ∀ n t, eqNumDisj (S n) t = FOL.Formula.disj (eqNumDisj n t)
    (FOL.Formula.equal language t (num n)) :=
  fun n t => rfl

theorem substWithDepth_eqNumDisj (f : Nat → Nat → Nat) (t d : Nat) :
    ∀ n, FOL.Formula.substWithDepth f language (eqNumDisj n t) d = eqNumDisj n
    (FOL.Term.subst (f d) language t) := by
  intro n
  induction n with k ih
  · rw [eqNumDisj_zero, FOL.Formula.substWithDepth_falsum f, eqNumDisj_zero]
  · rw [eqNumDisj_succ, FOL.Formula.disj, FOL.Formula.neg,
      FOL.Formula.substWithDepth_imp f, FOL.Formula.substWithDepth_imp f,
      FOL.Formula.substWithDepth_falsum f, ih,
      FOL.Formula.substWithDepth_equal f, subst_num (f d)]
    rfl

/-- `finiteConj n p` is the finite conjunction `⊤ ∧ p(num 0) ∧ … ∧ p(num (n - 1))` of the
instances of `p` at numerals below `n`. -/
fol_def finiteConj over Arithmetic (n : Nat) (p : formula of 1) : formula :=
  ${primrec (FOL.Formula.neg FOL.Formula.falsum)
    (fun i A => FOL.Formula.conj A (FOL.Formula.instantiate language p (num i))) n}

/-- `finiteDisj n p` is the finite disjunction `⊥ ∨ p(num 0) ∨ … ∨ p(num (n - 1))` of the
instances of `p` at numerals below `n`. -/
fol_def finiteDisj over Arithmetic (n : Nat) (p : formula of 1) : formula :=
  ${primrec FOL.Formula.falsum
    (fun i A => FOL.Formula.disj A (FOL.Formula.instantiate language p (num i))) n}

theorem finiteConj_zero : ∀ p, finiteConj 0 p = FOL.Formula.neg FOL.Formula.falsum :=
  fun p => rfl

theorem finiteConj_succ :
    ∀ n p, finiteConj (S n) p = FOL.Formula.conj (finiteConj n p)
    (FOL.Formula.instantiate language p (num n)) :=
  fun n p => rfl

theorem finiteDisj_zero : ∀ p, finiteDisj 0 p = FOL.Formula.falsum := fun p => rfl

theorem finiteDisj_succ :
    ∀ n p, finiteDisj (S n) p = FOL.Formula.disj (finiteDisj n p)
    (FOL.Formula.instantiate language p (num n)) :=
  fun n p => rfl

/-- `allEqNumDisj n p` is universal quantification guarded by the finite numeral disjunction,
defined as `∀ x, eqNumDisj n x → p(x)`. -/
fol_def allEqNumDisj over Arithmetic (n p : Nat) : formula :=
  ${FOL.Formula.all (FOL.Formula.imp (eqNumDisj n (FOL.Term.var language 0)) p)}

/-- `anyEqNumDisj n p` is existential quantification guarded by the finite numeral disjunction,
defined as `∃ x, eqNumDisj n x ∧ p(x)`. -/
fol_def anyEqNumDisj over Arithmetic (n p : Nat) : formula :=
  ${FOL.Formula.ex (FOL.Formula.conj (eqNumDisj n (FOL.Term.var language 0)) p)}

/-- `boundedAll n p` states that every number below `num n` satisfies `p`, defined as
`∀ x, x < num n → p(x)`. -/
fol_def boundedAll over Arithmetic (n p : Nat) : formula :=
  ${FOL.Formula.all (FOL.Formula.imp (lt (FOL.Term.var language 0) (num n)) p)}

/-- `boundedAny n p` states that some number below `num n` satisfies `p`, defined as
`∃ x, x < num n ∧ p(x)`. -/
fol_def boundedAny over Arithmetic (n p : Nat) : formula :=
  ${FOL.Formula.ex (FOL.Formula.conj (lt (FOL.Term.var language 0) (num n)) p)}

end Arithmetic

namespace Q

open Arithmetic

fol_theorem _root_.FOL.Q.succ_inj : Q ⊢ ∀ x y, S x = S y → x = y := by
  pexact succ_injective

fol_theorem add_one : Q ⊢ ∀ x, x + 1 = S x := by
  pintro x
  prw [add_succ, add_zero]

fol_theorem succ_inj_iff : Q ⊢ ∀ x y, S x = S y ↔ x = y := by
  pintro x y
  pconstructor
  · pexact Q.succ_inj[x, y]
  · pintro h
    prw [h]

fol_theorem add_eq_zero_iff : Q ⊢ ∀ x y, x + y = 0 ↔ x = 0 ∧ y = 0 := by
  pintro x y
  pconstructor
  · pintro hsum
    pcases zero_or_succ[y] with hy | hex
    · pconstructor
      · prw [hy, add_zero, hsum]
      · passumption
    · pcases hex with ⟨z, hz⟩
      pexfalso
      papply succ_ne_zero[x + z]
      prw [hz, add_succ, hsum]
  · pintro h
    pcases h with ⟨hx, hy⟩
    prw [hx, hy, add_zero]

fol_theorem le_of_add_eq : Q ⊢ ∀ x y z, x + y = z → y ≤ z := by
  pintro x y z h
  pexists x
  passumption

fol_theorem zero_le : Q ⊢ ∀ x, 0 ≤ x := by
  pintro x
  pexists x
  prw [add_zero]

fol_theorem succ_not_le_zero : Q ⊢ ∀ x, ¬ S x ≤ 0 := by
  pintro x h
  pcases h with ⟨z, hz⟩
  papply succ_ne_zero[z + x]
  prw [hz, add_succ]

fol_theorem le_zero_iff_eq_zero : Q ⊢ ∀ x, x ≤ 0 ↔ x = 0 := by
  pintro x
  pconstructor
  · pintro h
    pcases h with ⟨z, hz⟩
    phave hb : z = 0 ∧ x = 0
    · pcases add_eq_zero_iff[z, x] with ⟨forward, backward⟩
      papply forward
      passumption
    · pcases hb with ⟨hz0, hx0⟩
      passumption
  · pintro h
    pexists 0
    prw [h, add_zero]

fol_theorem succ_le_iff_lt : Q ⊢ ∀ x y, S x ≤ y ↔ x < y := by
  pintro x y
  pconstructor
  · passumption
  · passumption

fol_theorem one_le_iff_zero_lt : Q ⊢ ∀ x, 1 ≤ x ↔ 0 < x := by
  pintro x
  pexact succ_le_iff_lt[0, x]

fol_theorem succ_le_succ_iff : Q ⊢ ∀ x y, S x ≤ S y ↔ x ≤ y := by
  pintro x y
  pconstructor
  · pintro h
    pcases h with ⟨z, hz⟩
    pexists z
    papply Q.succ_inj[z + x, y]
    prw [hz, add_succ]
  · pintro h
    pcases h with ⟨z, hz⟩
    pexists z
    prw [add_succ, hz]

fol_theorem not_lt_zero : Q ⊢ ∀ x, ¬ x < 0 := by
  pintro x
  pexact succ_not_le_zero[x]

fol_theorem lt_succ_iff_le : Q ⊢ ∀ x y, x < S y ↔ x ≤ y := by
  pintro x y
  pexact succ_le_succ_iff[x, y]

fol_theorem succ_lt_succ_iff : Q ⊢ ∀ x y, S x < S y ↔ x < y := by
  pintro x y
  pexact succ_le_succ_iff[S x, y]

fol_theorem zero_lt_succ : Q ⊢ ∀ x, 0 < S x := by
  pintro x
  pexists x
  prw [add_succ, add_zero]

fol_theorem mul_one_eq_zero_add : Q ⊢ ∀ x, x * 1 = 0 + x := by
  pintro x
  prw [mul_succ, mul_zero]

end Q

end

open PRAProver.Library.FOL.DSL in
run_cmd do
  registerFormulaBuilder `FOL.Arithmetic.eqNumDisj `FOL.Arithmetic.substWithDepth_eqNumDisj
  registerCalculation `FOL.Arithmetic.eqNumDisj_zero
  registerCalculation `FOL.Arithmetic.eqNumDisj_succ
  registerCalculation `FOL.Arithmetic.finiteConj_zero
  registerCalculation `FOL.Arithmetic.finiteConj_succ
  registerCalculation `FOL.Arithmetic.finiteDisj_zero
  registerCalculation `FOL.Arithmetic.finiteDisj_succ

pra

namespace Q

open Arithmetic

/-- `Q` proves the equation `num a + num b = num (a + b)` for all natural numbers `a` and `b`. -/
fol_theorem add_num (a b : Nat) : Q ⊢ ${num a} + ${num b} = ${num (a + b)} := by
  sigma_induction b with
  | zero =>
    rw [num_zero, _root_.add_zero]
    pexact Q.add_zero[${num a}]
  | succ k ih =>
    rw [num_succ, _root_.add_succ, num_succ]
    prw [Q.add_succ, ih]

/-- `Q` proves the equation `num a * num b = num (a * b)` for all natural numbers `a` and `b`. -/
fol_theorem mul_num (a b : Nat) : Q ⊢ ${num a} * ${num b} = ${num (a * b)} := by
  sigma_induction b with
  | zero =>
    rw [num_zero, _root_.mul_zero, num_zero]
    pexact Q.mul_zero[${num a}]
  | succ k ih =>
    rw [num_succ, _root_.mul_succ]
    ptrans ${num (a * k)} + ${num a}
    · prw [Q.mul_succ, ih]
    · pexact Q.add_num (a * k) a

fol_theorem add_assoc_num (n : Nat) : Q ⊢ ∀ x y, (x + y) + ${num n} = x + (y + (num n)) := by
  sigma_induction n with
  | zero =>
    rw [num_zero]
    pintro x y
    prw [Q.add_zero]
  | succ k ih =>
    rw [num_succ]
    pintro x y
    prw [Q.add_succ, ih]

fol_theorem add_num_cancel (n : Nat) : Q ⊢ ∀ x y, x + ${num n} = y + ${num n} → x = y := by
  sigma_induction n with
  | zero =>
    rw [num_zero]
    pintro x y h
    prw [Q.add_zero, h]
  | succ k ih =>
    rw [num_succ]
    pintro x y h
    papply ih[x, y]
    papply Q.succ_inj[x + ${num k}, y + ${num k}]
    prw [Q.add_succ, h]

fol_theorem succ_add_num (n : Nat) : Q ⊢ ∀ x, S x + ${num n} = S (x + (num n)) := by
  sigma_induction n with
  | zero =>
    rw [num_zero]
    pintro x
    prw [Q.add_zero]
  | succ k ih =>
    rw [num_succ]
    pintro x
    prw [Q.add_succ, ih]

fol_theorem zero_add_num (n : Nat) : Q ⊢ 0 + ${num n} = ${num n} := by
  have h := Q.add_num 0 n
  rw [num_zero, _root_.zero_add] at h
  pexact h

fol_theorem num_succ_ne_zero (n : Nat) : Q ⊢ ${num (S n)} ≠ 0 := by
  rw [num_succ]
  pexact Q.succ_ne_zero[${num n}]

fol_theorem add_le_add_num_iff (n : Nat) : Q ⊢ ∀ x y, x + ${num n} ≤ y + ${num n} ↔ x ≤ y := by
  pintro x y
  pconstructor
  · pintro h
    pcases h with ⟨a, ha⟩
    pexists a
    papply (Q.add_num_cancel n)[a + x, y]
    prw [Q.add_assoc_num n, ha]
  · pintro h
    pcases h with ⟨a, ha⟩
    pexists a
    ptrans (a + x) + ${num n}
    · psymm
      pexact (Q.add_assoc_num n)[a, x]
    · prw [ha]

fol_theorem add_lt_add_num_iff (n : Nat) : Q ⊢ ∀ x y, x + ${num n} < y + ${num n} ↔ x < y := by
  pintro x y
  pconstructor
  · pintro h
    pcases h with ⟨a, ha⟩
    pexists a
    papply (Q.add_num_cancel n)[a + S x, y]
    prw [Q.add_assoc_num n, Q.succ_add_num n, ha]
  · pintro h
    pcases h with ⟨a, ha⟩
    pexists a
    ptrans a + (S x + (num n))
    · prw [Q.succ_add_num n]
    · ptrans (a + S x) + ${num n}
      · psymm
        pexact (Q.add_assoc_num n)[a, S x]
      · prw [ha]

fol_theorem not_le_num_succ_add (b d : Nat) : Q ⊢ ¬ ${num (S d + b)} ≤ ${num b} := by
  have hsum := Q.add_num (S d) b
  pintro h
  pcases h with ⟨a, ha⟩
  phave hz : a + ${num (S d)} = 0
  · papply (Q.add_num_cancel b)[a + ${num (S d)}, 0]
    ptrans a + (${num (S d)} + ${num b})
    · pexact (Q.add_assoc_num b)[a, ${num (S d)}]
    · prw [hsum, Q.zero_add_num b, ha]
  · phave hp : a = 0 ∧ ${num (S d)} = 0
    · papply Q.add_eq_zero_iff[a, ${num (S d)}]
      passumption
    · pcases hp with ⟨ha0, hn0⟩
      papply Q.num_succ_ne_zero d
      passumption

/-- A numerical inequality `a ≤ b` yields a `Q` proof of `num a ≤ num b`. -/
theorem le_num (a b : Nat) : a ≤ b → (Q ⊢ ${num a} ≤ ${num b}) := by
  intro h
  have hsum := Q.add_num (b - a) a
  rw [_root_.sub_add_cancel_of_le b a h] at hsum
  pexists ${num (b - a)}
  pexact hsum

theorem lt_num (a b : Nat) : a < b → (Q ⊢ ${num a} < ${num b}) := by
  intro h
  have hp := Q.le_num (S a) b h
  rw [num_succ] at hp
  pexact hp

theorem not_le_num (a b : Nat) : b < a → (Q ⊢ ¬ ${num a} ≤ ${num b}) := by
  intro h
  have he : S (a - S b) + b = a := by
    rw [_root_.succ_add, ← _root_.add_succ]
    exact _root_.sub_add_cancel_of_le a (S b) h
  rw [← he]
  pexact Q.not_le_num_succ_add b (a - S b)

theorem not_lt_num (a b : Nat) : b ≤ a → (Q ⊢ ¬ ${num a} < ${num b}) := by
  intro h
  have hp := Q.not_le_num (S a) b (and_right (_root_.lt_succ b a) h)
  rw [num_succ] at hp
  pexact hp

theorem num_ne_of_lt (a b : Nat) : a < b → (Q ⊢ ${num a} ≠ ${num b}) := by
  intro hab
  have hn := not_le_num b a hab
  pintro he
  papply hn
  pexists 0
  ptrans ${num b}
  · pexact zero_add_num b
  · psymm
    passumption

theorem num_ne_of_gt (a b : Nat) : b < a → (Q ⊢ ${num a} ≠ ${num b}) := by
  intro hab
  have hn := not_le_num a b hab
  pintro he
  papply hn
  pexists 0
  ptrans ${num a}
  · pexact zero_add_num a
  · passumption

extract_witness num_ne_of_lt num_ne_of_gt

/-- `numNeProof a b` constructs a Q proof that `num a ≠ num b` when `a` and `b` are distinct.
The order test `ltb a b` selects the proof branch directly from `a` and `b`. -/
def numNeProof (a b : Nat) : Nat :=
  ite (ltb a b) (num_ne_of_lt.witness a b) (num_ne_of_gt.witness a b)

theorem numNeProof_checked (a b : Nat) :
    ¬ a = b → IsProofOf language isAxiom (Formula.neg (Formula.equal language (num a) (num b)))
    (numNeProof a b) := by
  intro hne
  by_cases hab : a < b
  · rw [numNeProof, and_right (ltb_eq_one a b) hab]
    exact num_ne_of_lt.witness_correct a b hab
  · have hba : b < a := by
      rcases _root_.lt_or_eq_of_le b a (_root_.le_of_not_lt b a hab) with hlt | heq
      · exact hlt
      · exact false_elim (hne (eq_symm heq))
    rw [numNeProof, and_right (ltb_eq_zero a b) hab]
    exact num_ne_of_gt.witness_correct a b hba

theorem num_ne (a b : Nat) : ¬ a = b → (Q ⊢ ${num a} ≠ ${num b}) :=
  fun h => (numNeProof a b, numNeProof_checked a b h)

fol_theorem eqNumDisj_succ_zero (n : Nat) : Q ⊢ ${eqNumDisj (S n) (num 0)} := by
  sigma_induction n with
  | zero =>
    pright
    prefl
  | succ k ih =>
    pleft
    pexact ih

fol_theorem eqNumDisj_congr (n : Nat) : Q ⊢ free y x |
    x = y → ${eqNumDisj n x} → ${eqNumDisj n y} := by
  sigma_induction n with
  | zero =>
    pintro he h
    passumption
  | succ k ih =>
    pintro he h
    pcases h with hx | hx
    · pleft
      papply ih
      · passumption
      · passumption
    · pright
      prw [he, hx]

fol_theorem eqNumDisj_succ_iff (n : Nat) : Q ⊢ free x |
    ${eqNumDisj (S n) (FOL.Term.app language 0 x)} ↔
    ${eqNumDisj n x} := by
  sigma_induction n with
  | zero =>
    pconstructor
    · pintro h
      pcases h with hf | he
      · passumption
      · papply Q.succ_ne_zero[x]
        passumption
    · pintro hf
      pexfalso
      passumption
  | succ k ih =>
    pconstructor
    · pintro h
      pcases h with hx | he
      · pleft
        papply ih
        passumption
      · pright
        papply Q.succ_inj[x, ${num k}]
        passumption
    · pintro h
      pcases h with hx | he
      · pleft
        papply ih
        passumption
      · pright
        prw [he]

/-- In `Q`, `x < num n` is equivalent to the finite disjunction `eqNumDisj n x` of equations with
numerals below `n`. -/
fol_theorem lt_num_iff (n : Nat) : Q ⊢ free x | x < ${num n} ↔ ${eqNumDisj n x} := by
  sigma_induction n with
  | zero =>
    pconstructor
    · pexact Q.not_lt_zero[x]
    · pintro h
      pexfalso
      passumption
  | succ k ih =>
    have previous := FOL.Provable.gen language Q.isAxiom _ ih
    have congruence := FOL.Provable.gen language Q.isAxiom _
      (FOL.Provable.gen language Q.isAxiom _ (Q.eqNumDisj_congr (S k)))
    have successors := FOL.Provable.gen language Q.isAxiom _
      (Q.eqNumDisj_succ_iff k)
    pconstructor
    · pintro h
      pcases Q.zero_or_succ[x] with hx | hex
      · papply congruence[0, x]
        · psymm
          passumption
        · pexact Q.eqNumDisj_succ_zero k
      · pcases hex with ⟨y, hy⟩
        papply congruence[S y, x]
        · psymm
          passumption
        · papply successors[y]
          papply previous[y]
          pcases h with ⟨a, ha⟩
          pexists a
          papply Q.succ_inj[a + S y, ${num k}]
          prw [hy, Q.add_succ, ha]
    · pintro h
      pcases Q.zero_or_succ[x] with hx | hex
      · pexists ${num k}
        prw [hx, Q.add_succ, Q.add_zero]
      · pcases hex with ⟨y, hy⟩
        phave hc : ${eqNumDisj k y}
        · papply successors[y]
          papply congruence[x, S y]
          · passumption
          · passumption
        · phave hl : y < ${num k}
          · papply previous[y]
            passumption
          · pcases hl with ⟨a, ha⟩
            pexists a
            prw [hy, Q.add_succ, ha]

fol_theorem le_num_iff (n : Nat) : Q ⊢ free x | x ≤ ${num n} ↔ ${eqNumDisj (S n) x} := by
  have strict := FOL.Provable.gen language Q.isAxiom _ (Q.lt_num_iff (S n))
  pconstructor
  · pintro h
    papply strict[x]
    papply Q.lt_succ_iff_le[x, ${num n}]
    passumption
  · pintro h
    papply Q.lt_succ_iff_le[x, ${num n}]
    papply strict[x]
    passumption

fol_theorem eq_or_ge_num (n : Nat) : Q ⊢ free x | ${eqNumDisj n x} ∨ ${num n} ≤ x := by
  sigma_induction n with
  | zero =>
    rw [eqNumDisj_zero]
    rw [num_zero]
    pright
    pexact Q.zero_le[x]
  | succ k ih =>
    rw [eqNumDisj_succ, num_succ]
    pcases ih with h | h
    · pleft
      pleft
      passumption
    · pcases h with ⟨a, ha⟩
      pcases Q.zero_or_succ[a] with hz | hex
      · pleft
        pright
        have z := Q.add_num 0 k
        rw [num_zero, _root_.zero_add] at z
        prw [hz, z, ha]
      · pcases hex with ⟨b, hb⟩
        pright
        pexists b
        prw [hb, Q.add_succ, Q.succ_add_num k, ha]

fol_theorem not_lt_num_of_ge (n : Nat) : Q ⊢ free x | ${num n} ≤ x → ¬ x < ${num n} := by
  pintro hge hlt
  pcases hge with ⟨b, hb⟩
  pcases hlt with ⟨a, ha⟩
  phave hz : a + S b = 0
  · papply (Q.add_num_cancel n)[a + S b, 0]
    prw [Q.add_assoc_num n, Q.succ_add_num n, hb, ha, Q.zero_add_num n]
  · phave he : a = 0 ∧ S b = 0
    · papply Q.add_eq_zero_iff[a, S b]
      passumption
    · pcases he with ⟨ha0, hb0⟩
      papply Q.succ_ne_zero[b]
      passumption

fol_theorem lt_or_ge_num (n : Nat) : Q ⊢ free x | x < ${num n} ∨ ${num n} ≤ x := by
  have cases := FOL.Provable.gen language Q.isAxiom _ (Q.eq_or_ge_num n)
  have strict := FOL.Provable.gen language Q.isAxiom _ (Q.lt_num_iff n)
  pcases cases[x] with h | h
  · pleft
    papply strict[x]
    passumption
  · pright
    passumption

fol_theorem le_or_gt_num (n : Nat) : Q ⊢ free x | x ≤ ${num n} ∨ ${num n} < x := by
  have alternatives := FOL.Provable.gen language Q.isAxiom _
    (Q.lt_or_ge_num (S n))
  pcases alternatives[x] with h | h
  · pleft
    papply Q.lt_succ_iff_le[x, ${num n}]
    passumption
  · pright
    passumption

fol_theorem not_lt_num_iff (n : Nat) : Q ⊢ free x | ¬ x < ${num n} ↔ ${num n} ≤ x := by
  have alternatives := FOL.Provable.gen language Q.isAxiom _ (Q.lt_or_ge_num n)
  have disjoint := FOL.Provable.gen language Q.isAxiom _
    (Q.not_lt_num_of_ge n)
  pconstructor
  · pintro hn
    pcases alternatives[x] with h | h
    · pexfalso
      papply hn
      passumption
    · passumption
  · pexact disjoint[x]

fol_theorem not_le_num_iff (n : Nat) : Q ⊢ free x | ¬ x ≤ ${num n} ↔ ${num n} < x := by
  have complement := FOL.Provable.gen language Q.isAxiom _
    (Q.not_lt_num_iff (S n))
  pconstructor
  · pintro hn
    papply complement[x]
    pintro hlt
    papply hn
    papply Q.lt_succ_iff_le[x, ${num n}]
    passumption
  · pintro hlt hle
    phave hn : ¬ x < S ${num n}
    · papply complement[x]
      passumption
    · papply hn
      papply Q.lt_succ_iff_le[x, ${num n}]
      passumption

fol_theorem not_ge_num_iff (n : Nat) : Q ⊢ free x | ¬ ${num n} ≤ x ↔ x < ${num n} := by
  have alternatives := FOL.Provable.gen language Q.isAxiom _ (Q.lt_or_ge_num n)
  have disjoint := FOL.Provable.gen language Q.isAxiom _
    (Q.not_lt_num_of_ge n)
  pconstructor
  · pintro hn
    pcases alternatives[x] with h | h
    · passumption
    · pexfalso
      papply hn
      passumption
  · pintro hlt hge
    papply disjoint[x]
    · passumption
    · passumption

fol_theorem not_gt_num_iff (n : Nat) : Q ⊢ free x | ¬ ${num n} < x ↔ x ≤ ${num n} := by
  have complement := FOL.Provable.gen language Q.isAxiom _
    (Q.not_ge_num_iff (S n))
  pconstructor
  · pintro hn
    papply Q.lt_succ_iff_le[x, ${num n}]
    papply complement[x]
    passumption
  · pintro hle
    papply complement[x]
    papply Q.lt_succ_iff_le[x, ${num n}]
    passumption

fol_theorem ne_num_iff (n : Nat) : Q ⊢ free x | x ≠ ${num n} ↔ x < ${num n} ∨ ${num n} < x := by
  have alternatives := FOL.Provable.gen language Q.isAxiom _ (Q.le_or_gt_num n)
  have bounded := FOL.Provable.gen language Q.isAxiom _ (Q.le_num_iff n)
  have strict := FOL.Provable.gen language Q.isAxiom _ (Q.lt_num_iff n)
  have irreflexive := Q.not_lt_num n n (_root_.le_refl n)
  pconstructor
  · pintro hn
    pcases alternatives[x] with hle | hgt
    · phave hc : ${eqNumDisj (S n) x}
      · papply bounded[x]
        passumption
      · pcases hc with hl | he
        · pleft
          papply strict[x]
          passumption
        · pexfalso
          papply hn
          passumption
    · pright
      passumption
  · pintro h he
    pcases h with hlt | hgt
    · papply irreflexive
      pcases hlt with ⟨a, ha⟩
      pexists a
      prw [he, ha]
    · papply irreflexive
      pcases hgt with ⟨a, ha⟩
      pexists a
      prw [he, ha]

fol_theorem allEqNumDisj_iff (n p : Nat) : Q ⊢
    ${allEqNumDisj n p} ↔ ${finiteConj n p} := by
  sigma_induction n with
  | zero =>
    pconstructor
    · pintro h hf
      passumption
    · pintro h x hf
      pexfalso
      passumption
  | succ k ih =>
    pcases ih with ⟨forward, backward⟩
    pconstructor
    · pintro h
      pconstructor
      · papply forward
        pintro x hx
        papply h[x]
        pleft
        passumption
      · papply h[${num k}]
        pright
        prefl
    · pintro h
      pcases h with ⟨previous, last⟩
      pintro x hx
      pcases hx with old | he
      · papply backward[x]
        · passumption
        · passumption
      · papply Equality.replace language Q.isAxiom x (num k) p
        · passumption
        · passumption

fol_theorem anyEqNumDisj_iff (n p : Nat) : Q ⊢
    ${anyEqNumDisj n p} ↔ ${finiteDisj n p} := by
  sigma_induction n with
  | zero =>
    pconstructor
    · pintro h
      pcases h with ⟨x, hx⟩
      pcases hx with ⟨hf, hp⟩
      passumption
    · pintro hf
      pexfalso
      passumption
  | succ k ih =>
    pcases ih with ⟨forward, backward⟩
    pconstructor
    · pintro h
      pcases h with ⟨x, hx⟩
      pcases hx with ⟨hc, hp⟩
      pcases hc with old | he
      · pleft
        papply forward
        pexists x
        pconstructor
        · passumption
        · passumption
      · pright
        papply Equality.replace language Q.isAxiom x (num k) p
        · passumption
        · passumption
    · pintro h
      pcases h with previous | last
      · phave hex : ${anyEqNumDisj k p}
        · papply backward
          passumption
        · pcases hex with ⟨x, hx⟩
          pcases hx with ⟨hc, hp⟩
          pexists x
          pconstructor
          · pleft
            passumption
          · passumption
      · pexists ${num k}
        pconstructor
        · pright
          prefl
        · passumption

/-- A numeral-bounded universal quantifier is equivalent in `Q` to its finite conjunction. -/
fol_theorem boundedAll_iff_finiteConj (n p : Nat) : Q ⊢
    ${boundedAll n p} ↔ ${finiteConj n p} := by
  have cases := FOL.Provable.gen language Q.isAxiom _ (Q.lt_num_iff n)
  pcases allEqNumDisj_iff n p with ⟨forward, backward⟩
  pconstructor
  · pintro h
    papply forward
    pintro x hx
    papply h[x]
    papply cases[x]
    passumption
  · pintro h x hx
    papply backward[x]
    · passumption
    · papply cases[x]
      passumption

/-- A numeral-bounded existential quantifier is equivalent in `Q` to its finite disjunction. -/
fol_theorem boundedAny_iff_finiteDisj (n p : Nat) : Q ⊢
    ${boundedAny n p} ↔ ${finiteDisj n p} := by
  have cases := FOL.Provable.gen language Q.isAxiom _ (Q.lt_num_iff n)
  pcases anyEqNumDisj_iff n p with ⟨forward, backward⟩
  pconstructor
  · pintro h
    papply forward
    pcases h with ⟨x, hx⟩
    pcases hx with ⟨hl, hp⟩
    pexists x
    pconstructor
    · papply cases[x]
      passumption
    · passumption
  · pintro h
    phave hex : ${anyEqNumDisj n p}
    · papply backward
      passumption
    · pcases hex with ⟨x, hx⟩
      pcases hx with ⟨hc, hp⟩
      pexists x
      pconstructor
      · papply cases[x]
        passumption
      · passumption

end Q

extract_witness FOL.Q.add_assoc_num FOL.Q.add_eq_zero_iff FOL.Q.add_num_cancel FOL.Q.add_one
  FOL.Q.add_succ FOL.Q.add_zero FOL.Q.allEqNumDisj_iff FOL.Q.anyEqNumDisj_iff
  FOL.Q.boundedAll_iff_finiteConj FOL.Q.boundedAny_iff_finiteDisj FOL.Q.eq_or_ge_num FOL.Q.le_num
  FOL.Q.le_or_gt_num FOL.Q.lt_num FOL.Q.lt_num_iff FOL.Q.lt_or_ge_num FOL.Q.lt_succ_iff_le
  FOL.Q.mul_num FOL.Q.mul_succ FOL.Q.mul_zero FOL.Q.not_le_num_succ_add FOL.Q.not_le_num
  FOL.Q.num_succ_ne_zero FOL.Q.succ_le_iff_lt FOL.Q.succ_le_succ_iff FOL.Q.succ_lt_succ_iff
  FOL.Q.succ_ne_zero FOL.Q.zero_lt_succ FOL.Q.zero_or_succ

end

end FOL
