module

public import LeanPRA.Library.FOL.Arithmetic.Division
public import LeanPRA.Library.FOL.DSL.Tactic

/-!
# Representation: initial functions and arithmetic

Graph formulas put the output at position zero, followed by inputs and any further parameters.

- `Q.Represents f p` states numeralwise representation in Q; `PA.Total p` and `PA.Unique p` state
  PA provability of existence and uniqueness for arbitrary inputs.
- `Arithmetic.constGraph`, `Arithmetic.idGraph`, and `Arithmetic.succGraph` represent the initial
  unary functions.
- `Arithmetic.addGraph` and `Arithmetic.mulGraph` describe addition and multiplication, with Q and
  PA proofs.
- `Arithmetic.pairGraph`, `Arithmetic.leftGraph`, and `Arithmetic.rightGraph` describe Cantor
  pairing and its projections. Q identifies their outputs at numeral inputs, and PA proves totality
  and uniqueness.
- `Q.finiteConjProof` combines explicit numeral proofs into a finite conjunction.
  `Q.boundedAll_of_isProofOf` gives the corresponding numeral-bounded universal statement.

The proof-code functions `Provable.imp_refl.witness` and `Provable.conj_intro.witness` are
compiled from checked propositional proofs. Their `witness_correct` theorems verify the
generated codes.
-/

namespace FOL

set_option pra.maxDepth 4096

pra

namespace Q

open Arithmetic

/-- `Represents f p` states that Q identifies every output of `p` at numeral input `x` with the
numeral for `f x`. The graph has output at position zero and input at position one. -/
def Represents (f : Nat → Nat) (p : Nat) : Prop :=
  ∀ x, Q ⊢ ∀ y, ${p}[${num x}, y] ↔ y = ${num (f x)}

end Q

namespace PA

open Arithmetic

/-- `Total p` states that PA proves the graph `p` has an output on every input. -/
def Total (p : Nat) : Prop := PA ⊢ ∀ x, ∃ y, ${p}[x, y]

/-- `Unique p` states that PA proves any two outputs of the graph `p` on the same input are
equal. -/
def Unique (p : Nat) : Prop :=
  PA ⊢ ∀ x y z, ${p}[x, y] → ${p}[x, z] → y = z

end PA

namespace Arithmetic

/-- `unaryFormula graph` builds a unary graph formula with output at position zero and input at
position one. -/
fol_def unaryFormula over Arithmetic (graph : Nat → Nat → Nat) : formula of 2 :=
  ${graph (Term.var language 0) (Term.var language 1)}

/-- `constGraph (n := n)(y, x)` is the graph formula `y = num n` for the constant function with
value `n`. -/
fol_def constGraph over Arithmetic (n : Nat) (y x : term) : formula := y = ${num n}

/-- `idGraph(y, x)` is the graph formula `y = x` for the identity function. -/
fol_def idGraph over Arithmetic (y x : term) : formula := y = x

/-- `succGraph(y, x)` is the graph formula `y = S x` for the successor function. -/
fol_def succGraph over Arithmetic (y x : term) : formula := y = S x

/-- `addGraph(y, x, z)` is the graph formula `y = x + z` for addition. -/
fol_def addGraph over Arithmetic (y x z : term) : formula := y = x + z

/-- `mulGraph(y, x, z)` is the graph formula `y = x * z` for multiplication. -/
fol_def mulGraph over Arithmetic (y x z : term) : formula := y = x * z

/-- `pairGraph(z, x, y)` is the graph formula for Cantor pairing, characterized by twice its value.
The bounds make the components finite when the code is a numeral and make the code finite when both
components are numerals. -/
fol_def pairGraph over Arithmetic (z x y : term) : formula :=
  x ≤ z ∧ y ≤ z ∧ z ≤ (x + y) * S (x + y) + (x + x) ∧
    z + z = (x + y) * S (x + y) + (x + x)

/-- `leftGraph(y, x)` is the graph formula `∃ z, pairGraph(x, y, z)` for the first component of a
Cantor pair. -/
fol_def leftGraph over Arithmetic (y x : term) : formula := ∃ z, pairGraph(x, y, z)

/-- `rightGraph(y, x)` is the graph formula `∃ z, pairGraph(x, z, y)` for the second component of
a Cantor pair. -/
fol_def rightGraph over Arithmetic (y x : term) : formula := ∃ z, pairGraph(x, z, y)

end Arithmetic

namespace Q

open Arithmetic

/-- `appendProof A B p q` combines a proof `p` of `A` and a proof `q` of `B` into a proof of
`A ∧ B` using two applications of modus ponens. -/
def appendProof (A B : Nat) (p q : Nat) : Nat :=
  Proof.mp' language
    (Proof.mp' language (Provable.conj_intro.witness language isAxiom A B) p) q

theorem appendProof_isProofOf (A B p q : Nat) :
    IsProofOf language isAxiom A p → IsProofOf language isAxiom B q → IsProofOf language
    isAxiom (Formula.conj A B) (appendProof A B p q) := by
  intro hp hq
  rw [appendProof]
  apply IsProofOf.mp' language isAxiom B (Formula.conj A B)
  · apply IsProofOf.mp' language isAxiom A (Formula.imp B (Formula.conj A B))
    · exact Provable.conj_intro.witness_correct language isAxiom A B
    · exact hp
  · exact hq

/-- `finiteConjProof p proof n` builds the conjunction of `proof i` for `i < n`, starting with a
proof of truth. -/
def finiteConjProof (p : Nat) (proof : Nat → Nat) : Nat → Nat := fun n =>
  primrec (Provable.imp_refl.witness language isAxiom Formula.falsum)
    (fun i previous => appendProof (finiteConj i p)
      (Formula.instantiate language p (num i)) previous (proof i)) n

fol_theorem constGraph_num_iff (n x : Nat) : Q ⊢
    ∀ y, constGraph (n := n)(y, ${num x}) ↔ y = ${num n} := by
  pintro y
  pconstructor
  · pintro h
    passumption
  · pintro h
    passumption

fol_theorem idGraph_num_iff (x : Nat) : Q ⊢ ∀ y, idGraph(y, ${num x}) ↔ y = ${num x} := by
  pintro y
  pconstructor
  · pintro h
    passumption
  · pintro h
    passumption

fol_theorem succGraph_num_iff (x : Nat) : Q ⊢
    ∀ y, succGraph(y, ${num x}) ↔ y = ${num (S x)} := by
  rw [num_succ]
  pintro y
  pconstructor
  · pintro h
    passumption
  · pintro h
    passumption

fol_theorem addGraph_num_iff (a b : Nat) : Q ⊢
    ∀ y, addGraph(y, ${num a}, ${num b}) ↔ y = ${num (a + b)} := by
  have sum := add_num a b
  pintro y
  pconstructor
  · pintro h
    prw [h, sum]
  · pintro h
    prw [h, sum]

fol_theorem mulGraph_num_iff (a b : Nat) : Q ⊢
    ∀ y, mulGraph(y, ${num a}, ${num b}) ↔ y = ${num (a * b)} := by
  have product := mul_num a b
  pintro y
  pconstructor
  · pintro h
    prw [h, product]
  · pintro h
    prw [h, product]

/-- Correct numeral-instance proofs give a checked proof of their finite conjunction. -/
theorem finiteConjProof_isProofOf (p n : Nat) (proof : Nat → Nat) :
    (∀ i, i < n → IsProofOf language isAxiom (Formula.instantiate language p (num i)) (proof i)) →
    IsProofOf language isAxiom (finiteConj n p) (finiteConjProof p proof n) := by
  intro supplied
  have prefixes : ∀ k, k ≤ n →
      IsProofOf language isAxiom (finiteConj k p) (finiteConjProof p proof k) := by
    intro k
    induction k with k ih
    · intro hbound
      rw [finiteConj_zero, finiteConjProof]
      exact Provable.imp_refl.witness_correct language isAxiom Formula.falsum
    · intro hbound
      have hk : k ≤ n := le_trans k (S k) n (le_succ_self k) hbound
      have hlt : k < n := hbound
      change IsProofOf language isAxiom
        (Formula.conj (finiteConj k p) (Formula.instantiate language p (num k)))
        (appendProof (finiteConj k p) (Formula.instantiate language p (num k))
          (finiteConjProof p proof k) (proof k))
      exact appendProof_isProofOf _ _ _ _ (ih hk) (supplied k hlt)
  exact prefixes n (le_refl n)

/-- Combine checked proof codes for all numeral instances below `n` into their conjunction. -/
theorem finiteConj_of_isProofOf (p n : Nat) (proof : Nat → Nat) :
    (∀ i, i < n → IsProofOf language isAxiom (Formula.instantiate language p (num i)) (proof i)) →
    (Q ⊢ ${finiteConj n p}) :=
  fun supplied => (finiteConjProof p proof n, finiteConjProof_isProofOf p n proof supplied)

/-- Explicit numeral proof codes establish a numeral-bounded universal statement in Q. -/
theorem boundedAll_of_isProofOf (p n : Nat) (proof : Nat → Nat) :
    (∀ i, i < n → IsProofOf language isAxiom (Formula.instantiate language p (num i)) (proof i)) →
    (Q ⊢ ${boundedAll n p}) := by
  intro supplied
  have all := finiteConj_of_isProofOf p n proof supplied
  papply (boundedAll_iff_finiteConj n p)
  exact all

/-- The Cantor-pair formula holds at the numerals for a pair and its two components. -/
fol_theorem pairGraph_num (a b : Nat) : Q ⊢ pairGraph(${num (pair a b)}, ${num a}, ${num b}) := by
  have hx := le_num a (pair a b) (left_le_pair a b)
  have hy := le_num b (pair a b) (right_le_pair a b)
  have bound : pair a b ≤ (a + b) * S (a + b) + (a + a) := by
    rw [← pair_double]
    exact le_add_right (pair a b) (pair a b)
  have hb := le_num (pair a b) ((a + b) * S (a + b) + (a + a)) bound
  have hs := add_num a b
  have hp := mul_num (a + b) (S (a + b))
  rw [num_succ] at hp
  have ha := add_num a a
  have hd := add_num ((a + b) * S (a + b)) (a + a)
  have hz := add_num (pair a b) (pair a b)
  rw [pair_double] at hz
  phave h : (${num a} + ${num b}) * S (${num a} + ${num b}) +
      (${num a} + ${num a}) = ${num ((a + b) * S (a + b) + (a + a))}
  · prw [hs, hp, ha, hd]
  · pconstructor
    · pexact hx
    · pconstructor
      · pexact hy
      · pconstructor
        · pcases hb with ⟨w, hw⟩
          pexists w
          prw [hw, h]
        · prw [hz, h]

theorem represents_constGraph (n : Nat) :
    Represents (fun _ => n) (unaryFormula (fun y x => constGraph n y x)) := by
  rw [unaryFormula]
  intro x
  pexact (constGraph_num_iff n x)

theorem represents_idGraph : Represents (fun x => x) (unaryFormula (fun y x => idGraph y x)) := by
  rw [unaryFormula]
  intro x
  pexact (idGraph_num_iff x)

theorem represents_succGraph : Represents S (unaryFormula (fun y x => succGraph y x)) := by
  rw [unaryFormula]
  intro x
  pexact (succGraph_num_iff x)

end Q

namespace PA

open Arithmetic

fol_theorem constGraph_total (n : Nat) : PA ⊢ ∀ x, ∃ y, constGraph (n := n)(y, x) := by
  pintro x
  pexists ${num n}
  prefl

fol_theorem constGraph_unique (n : Nat) : PA ⊢
    ∀ x y z, constGraph (n := n)(y, x) → constGraph (n := n)(z, x) → y = z := by
  pintro x y z hy hz
  prw [hy, hz]

fol_theorem idGraph_total : PA ⊢ ∀ x, ∃ y, idGraph(y, x) := by
  pintro x
  pexists x
  prefl

fol_theorem idGraph_unique : PA ⊢ ∀ x y z, idGraph(y, x) → idGraph(z, x) → y = z := by
  pintro x y z hy hz
  prw [hy, hz]

fol_theorem succGraph_total : PA ⊢ ∀ x, ∃ y, succGraph(y, x) := by
  pintro x
  pexists S x
  prefl

fol_theorem succGraph_unique : PA ⊢ ∀ x y z, succGraph(y, x) → succGraph(z, x) → y = z := by
  pintro x y z hy hz
  prw [hy, hz]

fol_theorem addGraph_total : PA ⊢ ∀ x z, ∃ y, addGraph(y, x, z) := by
  pintro x z
  pexists x + z
  prefl

fol_theorem addGraph_unique : PA ⊢ ∀ x z y w, addGraph(y, x, z) → addGraph(w, x, z) → y = w := by
  pintro x z y w hy hw
  prw [hy, hw]

fol_theorem mulGraph_total : PA ⊢ ∀ x z, ∃ y, mulGraph(y, x, z) := by
  pintro x z
  pexists x * z
  prefl

fol_theorem mulGraph_unique : PA ⊢ ∀ x z y w, mulGraph(y, x, z) → mulGraph(w, x, z) → y = w := by
  pintro x z y w hy hw
  prw [hy, hw]

fol_theorem add_add_self : PA ⊢ ∀ x y, (x + y) + (x + y) = (x + x) + (y + y) := by
  pintro x y
  phave h : y + (x + y) = x + (y + y)
  · pexact add_left_comm[y, x, y]
  · prw [add_assoc, h]

fol_theorem triangular_exists : PA ⊢ ∀ n, ∃ t, n ≤ t ∧ t + t = n * S n := by
  pintro n
  pinduction n with
  | zero =>
    pexists 0
    pconstructor
    · pexact Q.zero_le[0]
    · prw [Q.add_zero, zero_mul]
  | succ k ih =>
    pcases ih with ⟨t, ht⟩
    pcases ht with ⟨hlo, he⟩
    pexists t + S k
    pconstructor
    · pexact le_add_left[S k, t]
    · phave h : S k * S (S k) = k * S k + (S k + S k)
      · ptrans S k * S k + S k
        · pexact Q.mul_succ[S k, S k]
        · prw [succ_mul, add_assoc]
      · prw [add_add_self, he, h]

/-- Cantor pairing has an output for every pair of inputs. -/
fol_theorem pairGraph_total : PA ⊢ ∀ x y, ∃ z, pairGraph(z, x, y) := by
  pintro x y
  pcases triangular_exists[x + y] with ⟨t, ht⟩
  pcases ht with ⟨hlo, he⟩
  phave hd : (t + x) + (t + x) = (x + y) * S (x + y) + (x + x)
  · prw [add_add_self, he]
  · pexists t + x
    pconstructor
    · pexact le_add_left[x, t]
    · pconstructor
      · papply le_trans[y, x + y, t + x]
        · pexact le_add_left[y, x]
        · papply le_trans[x + y, t, t + x]
          · passumption
          · pexact le_add_right[t, x]
      · pconstructor
        · pexists t + x
          passumption
        · passumption

fol_theorem add_self_inj : PA ⊢ ∀ x y, x + x = y + y → x = y := by
  pintro x y he
  phave hx : x * 2 = x + x
  · ptrans x * 1 + x
    · pexact Q.mul_succ[x, 1]
    · prw [mul_one]
  · phave hy : y * 2 = y + y
    · ptrans y * 1 + y
      · pexact Q.mul_succ[y, 1]
      · prw [mul_one]
    · phave h : x * 2 = y * 2
      · prw [hx, hy, he]
      · papply le_antisymm[x, y]
        · papply mul_le_mul_iff_right[x, y, 2]
          · pexact Q.zero_lt_succ[1]
          · pexists 0
            prw [zero_add, h]
        · papply mul_le_mul_iff_right[y, x, 2]
          · pexact Q.zero_lt_succ[1]
          · pexists 0
            prw [zero_add, h]

/-- Two outputs of the Cantor-pair formula on the same inputs are equal. -/
fol_theorem pairGraph_unique : PA ⊢ ∀ x y z w, pairGraph(z, x, y) → pairGraph(w, x, y) → z = w := by
  pintro x y z w hz hw
  pcases hz with ⟨hzx, hzr⟩
  pcases hzr with ⟨hzy, hzr⟩
  pcases hzr with ⟨hzb, hze⟩
  pcases hw with ⟨hwx, hwr⟩
  pcases hwr with ⟨hwy, hwr⟩
  pcases hwr with ⟨hwb, hwe⟩
  papply add_self_inj[z, w]
  prw [hze, hwe]

fol_theorem pairGraph_succ_left : PA ⊢ ∀ z x y, pairGraph(z, x, S y) → pairGraph(S z, S x, y) := by
  pintro z x y h
  pcases h with ⟨hx, hr⟩
  pcases hr with ⟨hy, hr⟩
  pcases hr with ⟨hb, he⟩
  phave hn : S z + S z = (S x + y) * S (S x + y) + (S x + S x)
  · prw [Q.add_succ, succ_add, he]
  · pconstructor
    · papply Q.succ_le_succ_iff[x, z]
      passumption
    · pconstructor
      · papply le_trans[y, S y, S z]
        · pexact le_succ_self[y]
        · papply le_trans[S y, z, S z]
          · passumption
          · pexact le_succ_self[z]
      · pconstructor
        · pexists S z
          passumption
        · passumption

fol_theorem pairGraph_succ_right : PA ⊢ ∀ z x, pairGraph(z, x, 0) → pairGraph(S z, 0, S x) := by
  pintro z x h
  pcases h with ⟨hx, hr⟩
  pcases hr with ⟨hy, hr⟩
  pcases hr with ⟨hb, he⟩
  phave hn : S z + S z = (0 + S x) * S (0 + S x) + (0 + 0)
  · prw [zero_add, Q.add_zero, Q.mul_succ, succ_mul, Q.add_succ, succ_add,
      add_assoc, he]
  · pconstructor
    · pexact Q.zero_le[S z]
    · pconstructor
      · papply Q.succ_le_succ_iff[x, z]
        passumption
      · pconstructor
        · pexists S z
          passumption
        · passumption

/-- Every number is the code of a pair. -/
fol_theorem pairGraph_surjective : PA ⊢ ∀ z, ∃ x y, pairGraph(z, x, y) := by
  pintro z
  pinduction z with
  | zero =>
    pexists 0
    pexists 0
    pconstructor
    · pexact Q.zero_le[0]
    · pconstructor
      · pexact Q.zero_le[0]
      · pconstructor
        · pexact Q.zero_le[(0 + 0) * S (0 + 0) + (0 + 0)]
        · prw [Q.add_zero, zero_mul]
  | succ k ih =>
    pcases ih with ⟨x, hex⟩
    pcases hex with ⟨y, hxy⟩
    pcases Q.zero_or_succ[y] with hy | hex
    · pexists 0
      pexists S x
      papply pairGraph_succ_right[k, x]
      phave h : pairGraph(k, x, y) → pairGraph(k, x, 0)
      · psubst hy
        pintro h
        passumption
      · papply h
        passumption
    · pcases hex with ⟨a, hy⟩
      pexists S x
      pexists a
      papply pairGraph_succ_left[k, x, a]
      phave h : pairGraph(k, x, y) → pairGraph(k, x, S a)
      · psubst hy
        pintro h
        passumption
      · papply h
        passumption

fol_theorem cantor_polynomial_succ : PA ⊢ ∀ n, S n * S (S n) = n * S n + (S n + S n) := by
  pintro n
  ptrans S n * S n + S n
  · pexact Q.mul_succ[S n, S n]
  · prw [succ_mul, add_assoc]

fol_theorem cantor_polynomial_lt_succ : PA ⊢ ∀ n x, x ≤ n → n * S n + (x + x) < S n *
    S (S n) := by
  pintro n x hxn
  papply lt_of_eq_right[n * S n + (x + x), n * S n + (S n + S n), S n * S (S n)]
  · papply add_lt_add_iff_left[x + x, S n + S n, n * S n]
    papply add_lt_add_of_le_of_lt[x, S n, x, S n]
    · papply le_succ_of_le[x, n]
      passumption
    · papply Q.lt_succ_iff_le[x, n]
      passumption
  · psymm
    pexact cantor_polynomial_succ[n]

fol_theorem cantor_polynomial_le_of_lt : PA ⊢
    ∀ n m a, n < m → S n * S (S n) ≤ m * S m + (a + a) := by
  pintro n m a hnm
  papply le_trans[S n * S (S n), m * S m, m * S m + (a + a)]
  · papply mul_le_mul[S n, m, S (S n), S m]
    · passumption
    · papply Q.succ_le_succ_iff[S n, m]
      passumption
  · pexact le_add_right[m * S m, a + a]

fol_theorem cantor_polynomial_lt : PA ⊢
    ∀ n m x a, x ≤ n → n < m → n * S n + (x + x) < m * S m + (a + a) := by
  pintro n m x a hxn hnm
  papply lt_of_lt_of_le[n * S n + (x + x), S n * S (S n), m * S m + (a + a)]
  · papply cantor_polynomial_lt_succ[n, x]
    passumption
  · papply cantor_polynomial_le_of_lt[n, m, a]
    passumption

fol_theorem cantor_sum_not_lt : PA ⊢
    ∀ x y a b, (x + y) * S (x + y) + (x + x) = (a + b) * S (a + b) + (a + a) → ¬ x + y < a + b := by
  pintro x y a b he hlt
  papply not_lt_of_ge[(x + y) * S (x + y) + (x + x),
    (a + b) * S (a + b) + (a + a)]
  · pexists 0
    prw [zero_add, he]
  · papply cantor_polynomial_lt[x + y, a + b, x, a]
    · pexact le_add_right[x, y]
    · passumption

fol_theorem cantor_polynomial_injective : PA ⊢
    ∀ x y a b, (x + y) * S (x + y) + (x + x) = (a + b) * S (a + b) + (a + a) → x = a ∧ y = b := by
  pintro x y a b he
  phave hs : x + y = a + b
  · papply le_antisymm[x + y, a + b]
    · pcases lt_or_ge[a + b, x + y] with hlt | hle
      · pexfalso
        papply cantor_sum_not_lt[a, b, x, y]
        · psymm
          passumption
        · passumption
      · passumption
    · pcases lt_or_ge[x + y, a + b] with hlt | hle
      · pexfalso
        papply cantor_sum_not_lt[x, y, a, b]
        · passumption
        · passumption
      · passumption
  · phave hx : x = a
    · papply add_self_inj[x, a]
      papply add_left_cancel[x + x, a + a, (a + b) * S (a + b)]
      prw [hs, he]
    · pconstructor
      · passumption
      · papply add_left_cancel[y, b, a]
        prw [hx, hs]

/-- A Cantor code determines both of its components. -/
fol_theorem pairGraph_injective : PA ⊢
    ∀ z x y a b, pairGraph(z, x, y) → pairGraph(z, a, b) → x = a ∧ y = b := by
  pintro z x y a b hxy hab
  pcases hxy with ⟨hx, hr⟩
  pcases hr with ⟨hy, hr⟩
  pcases hr with ⟨hb, he⟩
  pcases hab with ⟨ha, hr⟩
  pcases hr with ⟨hb, hr⟩
  pcases hr with ⟨hc, hf⟩
  papply cantor_polynomial_injective[x, y, a, b]
  ptrans z + z
  · psymm
    passumption
  · passumption

fol_theorem leftGraph_total : PA ⊢ ∀ z, ∃ x, leftGraph(x, z) := by
  pintro z
  pcases pairGraph_surjective[z] with ⟨x, hex⟩
  pcases hex with ⟨y, h⟩
  pexists x
  pexists y
  passumption

fol_theorem rightGraph_total : PA ⊢ ∀ z, ∃ y, rightGraph(y, z) := by
  pintro z
  pcases pairGraph_surjective[z] with ⟨x, hex⟩
  pcases hex with ⟨y, h⟩
  pexists y
  pexists x
  passumption

fol_theorem leftGraph_unique : PA ⊢ ∀ z x y, leftGraph(x, z) → leftGraph(y, z) → x = y := by
  pintro z x y hx hy
  pcases hx with ⟨a, ha⟩
  pcases hy with ⟨b, hb⟩
  papply pairGraph_injective[z, x, a, y, b]
  · passumption
  · passumption

fol_theorem rightGraph_unique : PA ⊢ ∀ z x y, rightGraph(x, z) → rightGraph(y, z) → x = y := by
  pintro z x y hx hy
  pcases hx with ⟨a, ha⟩
  pcases hy with ⟨b, hb⟩
  papply pairGraph_injective[z, a, x, b, y]
  · passumption
  · passumption

end PA

namespace Q

open Arithmetic

fol_theorem cantor_num (a b : Nat) : Q ⊢
    (${num a} + ${num b}) * S (${num a} + ${num b}) + (${num a} + ${num a}) =
    ${num ((a + b) * S (a + b) + (a + a))} := by
  have hs := add_num a b
  have hp := mul_num (a + b) (S (a + b))
  rw [num_succ] at hp
  have ha := add_num a a
  have hd := add_num ((a + b) * S (a + b)) (a + a)
  prw [hs, hp, ha, hd]

theorem not_pairGraph_num (a b z : Nat) :
    ¬ z = pair a b → (Q ⊢ ¬ pairGraph(${num z}, ${num a}, ${num b})) := by
  intro hne
  have hn : ¬ z + z = (a + b) * S (a + b) + (a + a) := by
    intro h
    apply hne
    apply add_self_inj z (pair a b)
    rw [pair_double]
    exact h
  have unequal := num_ne (z + z) ((a + b) * S (a + b) + (a + a)) hn
  have hz := add_num z z
  have hp := cantor_num a b
  pintro h
  pcases h with ⟨hx, hr⟩
  pcases hr with ⟨hy, hr⟩
  pcases hr with ⟨hb, he⟩
  papply unequal
  ptrans ${num z} + ${num z}
  · psymm
    pexact hz
  · prw [he, hp]

theorem pairGraph_num_iff_of_eq (a b z : Nat) :
    z = pair a b →
    (Q ⊢ ${Formula.instantiate language (fol_formula[Arithmetic |
      pairGraph(${Term.var language 0}, ${num a}, ${num b}) ↔
        ${Term.var language 0} = ${num (pair a b)}]) (num z)}) := by
  intro h
  rw [h]
  pconstructor
  · pintro hp
    prefl
  · pintro he
    pexact (pairGraph_num a b)

theorem pairGraph_num_iff_of_ne (a b z : Nat) :
    ¬ z = pair a b →
    (Q ⊢ ${Formula.instantiate language (fol_formula[Arithmetic |
      pairGraph(${Term.var language 0}, ${num a}, ${num b}) ↔
        ${Term.var language 0} = ${num (pair a b)}]) (num z)}) := by
  intro h
  have hn := not_pairGraph_num a b z h
  have he := num_ne z (pair a b) h
  pconstructor
  · pintro hp
    pexfalso
    papply hn
    passumption
  · pintro hp
    pexfalso
    papply he
    passumption

extract_witness pairGraph_num_iff_of_eq pairGraph_num_iff_of_ne

/-- `pairGraphNumIffProof a b z` builds the Q proof of the pairing equivalence at numerals `a`, `b`,
and `z`. -/
def pairGraphNumIffProof (a b z : Nat) : Nat := ite (eqb z (pair a b))
  (pairGraph_num_iff_of_eq.witness a b z) (pairGraph_num_iff_of_ne.witness a b z)

theorem pairGraphNumIffProof_isProofOf (a b z : Nat) :
    IsProofOf language isAxiom
    (Formula.instantiate language (fol_formula[Arithmetic |
      pairGraph(${Term.var language 0}, ${num a}, ${num b}) ↔
        ${Term.var language 0} = ${num (pair a b)}]) (num z))
    (pairGraphNumIffProof a b z) := by
  by_cases h : z = pair a b
  · rw [pairGraphNumIffProof, and_right (eqb_eq_one z (pair a b)) h]
    exact pairGraph_num_iff_of_eq.witness_correct a b z h
  · rw [pairGraphNumIffProof, and_right (eqb_eq_zero z (pair a b)) h]
    exact pairGraph_num_iff_of_ne.witness_correct a b z h

fol_theorem pairGraph_iff_of_lt (a b n : Nat) : Q ⊢
    ∀ z, z < ${num n} → (pairGraph(z, ${num a}, ${num b}) ↔ z = ${num (pair a b)}) := by
  have h := boundedAll_of_isProofOf (fol_formula[Arithmetic |
      pairGraph(${Term.var language 0}, ${num a}, ${num b}) ↔
        ${Term.var language 0} = ${num (pair a b)}]) n
    (fun z => pairGraphNumIffProof a b z) (fun z hz => pairGraphNumIffProof_isProofOf a b z)
  rw [boundedAll] at h
  pexact h

fol_theorem pairGraph_num_iff (a b : Nat) : Q ⊢
    ∀ z, pairGraph(z, ${num a}, ${num b}) ↔ z = ${num (pair a b)} := by
  have bounded := pairGraph_iff_of_lt a b (S ((a + b) * S (a + b) + (a + a)))
  rw [num_succ] at bounded
  have polynomial := cantor_num a b
  pintro z
  pconstructor
  · pintro h
    phave bound : z ≤ ${num ((a + b) * S (a + b) + (a + a))}
    · pcases h with ⟨hx, hrest⟩
      pcases hrest with ⟨hy, hrest⟩
      pcases hrest with ⟨hz, he⟩
      pcases hz with ⟨w, hw⟩
      pexists w
      prw [hw, polynomial]
    · papply bounded[z]
      · papply lt_succ_iff_le[z, ${num ((a + b) * S (a + b) + (a + a))}]
        passumption
      · passumption
  · pintro he
    psubst he
    pexact (pairGraph_num a b)

theorem pairGraph_components_num_of_eq (z a b : Nat) :
    z = pair a b →
    (Q ⊢ ${Formula.instantiate language (fol_formula[Arithmetic |
      pairGraph(${num z}, ${num a}, ${Term.var language 0}) →
        (${num a} = ${num (unpairLeft z)} ∧
          ${Term.var language 0} = ${num (unpairRight z)})]) (num b)}) := by
  intro h
  rw [h, unpairLeft_pair, unpairRight_pair]
  pintro hg
  pconstructor
  · prefl
  · prefl

theorem pairGraph_components_num_of_ne (z a b : Nat) :
    ¬ z = pair a b →
    (Q ⊢ ${Formula.instantiate language (fol_formula[Arithmetic |
      pairGraph(${num z}, ${num a}, ${Term.var language 0}) →
        (${num a} = ${num (unpairLeft z)} ∧
          ${Term.var language 0} = ${num (unpairRight z)})]) (num b)}) := by
  intro h
  have hn := not_pairGraph_num a b z h
  pintro hg
  pexfalso
  papply hn
  passumption

extract_witness pairGraph_components_num_of_eq pairGraph_components_num_of_ne

/-- `pairGraphComponentsProof z a b` builds the Q proof identifying the components of `num z` at
candidate numerals `a` and `b`. -/
def pairGraphComponentsProof (z a b : Nat) : Nat := ite (eqb z (pair a b))
  (pairGraph_components_num_of_eq.witness z a b) (pairGraph_components_num_of_ne.witness z a b)

theorem pairGraphComponentsProof_isProofOf (z a b : Nat) :
    IsProofOf language isAxiom
    (Formula.instantiate language (fol_formula[Arithmetic |
      pairGraph(${num z}, ${num a}, ${Term.var language 0}) →
        (${num a} = ${num (unpairLeft z)} ∧
          ${Term.var language 0} = ${num (unpairRight z)})]) (num b))
    (pairGraphComponentsProof z a b) := by
  by_cases h : z = pair a b
  · rw [pairGraphComponentsProof, and_right (eqb_eq_one z (pair a b)) h]
    exact pairGraph_components_num_of_eq.witness_correct z a b h
  · rw [pairGraphComponentsProof, and_right (eqb_eq_zero z (pair a b)) h]
    exact pairGraph_components_num_of_ne.witness_correct z a b h

theorem pairGraph_components_num_of_lt_right (z a : Nat) : Q ⊢
    ${Formula.instantiate language (fol_formula[Arithmetic |
      ∀ b, b < ${num (S z)} → pairGraph(${num z}, ${Term.var language 0}, b) →
        (${Term.var language 0} = ${num (unpairLeft z)} ∧
          b = ${num (unpairRight z)})]) (num a)} := by
  have h := boundedAll_of_isProofOf (fol_formula[Arithmetic |
      pairGraph(${num z}, ${num a}, ${Term.var language 0}) →
        (${num a} = ${num (unpairLeft z)} ∧
          ${Term.var language 0} = ${num (unpairRight z)})]) (S z)
    (fun b => pairGraphComponentsProof z a b) (fun b hb => pairGraphComponentsProof_isProofOf z a b)
  rw [boundedAll] at h
  pexact h

extract_witness pairGraph_components_num_of_lt_right

fol_theorem pairGraph_components_num_of_lt (z : Nat) : Q ⊢
    ∀ a b, a < ${num (S z)} → b < ${num (S z)} → (pairGraph(${num z}, a, b) →
      (a = ${num (unpairLeft z)} ∧ b = ${num (unpairRight z)})) := by
  have h := boundedAll_of_isProofOf (fol_formula[Arithmetic |
      ∀ b, b < ${num (S z)} → pairGraph(${num z}, ${Term.var language 0}, b) →
        (${Term.var language 0} = ${num (unpairLeft z)} ∧ b = ${num (unpairRight z)})]) (S z)
    (fun a => pairGraph_components_num_of_lt_right.witness z a)
    (fun a ha => pairGraph_components_num_of_lt_right.witness_correct z a)
  rw [boundedAll] at h
  pintro a b ha hb
  phave ha' : ∀ b, b < ${num (S z)} → (pairGraph(${num z}, a, b) →
      (a = ${num (unpairLeft z)} ∧ b = ${num (unpairRight z)}))
  · papply h[a]
    passumption
  · papply ha'[b]
    passumption

fol_theorem pairGraph_components_num (z : Nat) : Q ⊢
    ∀ a b, pairGraph(${num z}, a, b) →
    (a = ${num (unpairLeft z)} ∧ b = ${num (unpairRight z)}) := by
  have bounded := pairGraph_components_num_of_lt z
  rw [num_succ] at bounded
  pintro a b h
  pcases h with ⟨ha, hrest⟩
  pcases hrest with ⟨hb, hrest⟩
  papply bounded[a, b]
  · papply lt_succ_iff_le[a, ${num z}]
    passumption
  · papply lt_succ_iff_le[b, ${num z}]
    passumption
  · pconstructor
    · pexact ha
    · pconstructor
      · pexact hb
      · pexact hrest

fol_theorem leftGraph_num_iff (n : Nat) : Q ⊢
    ∀ y, leftGraph(y, ${num n}) ↔ y = ${num (unpairLeft n)} := by
  have components := pairGraph_components_num n
  have witness := pairGraph_num (unpairLeft n) (unpairRight n)
  rw [pair_unpair] at witness
  pintro y
  pconstructor
  · pintro h
    pcases h with ⟨z, hz⟩
    papply components[y, z]
    passumption
  · pintro h
    psubst h
    pexists ${num (unpairRight n)}
    pexact witness

fol_theorem rightGraph_num_iff (n : Nat) : Q ⊢
    ∀ y, rightGraph(y, ${num n}) ↔ y = ${num (unpairRight n)} := by
  have components := pairGraph_components_num n
  have witness := pairGraph_num (unpairLeft n) (unpairRight n)
  rw [pair_unpair] at witness
  pintro y
  pconstructor
  · pintro h
    pcases h with ⟨z, hz⟩
    papply components[z, y]
    passumption
  · pintro h
    psubst h
    pexists ${num (unpairLeft n)}
    pexact witness

end Q

extract_witness FOL.PA.cantor_polynomial_injective FOL.PA.cantor_polynomial_le_of_lt
  FOL.PA.cantor_polynomial_lt FOL.PA.cantor_polynomial_lt_succ FOL.PA.cantor_polynomial_succ
  FOL.PA.cantor_sum_not_lt FOL.PA.constGraph_total FOL.PA.constGraph_unique FOL.PA.add_add_self
  FOL.PA.add_self_inj FOL.PA.leftGraph_total FOL.PA.leftGraph_unique FOL.PA.pairGraph_injective
  FOL.PA.pairGraph_succ_left FOL.PA.pairGraph_succ_right FOL.PA.pairGraph_surjective
  FOL.PA.pairGraph_total FOL.PA.pairGraph_unique FOL.PA.rightGraph_total FOL.PA.rightGraph_unique
  FOL.PA.succGraph_total FOL.PA.succGraph_unique FOL.PA.triangular_exists FOL.Q.constGraph_num_iff
  FOL.Q.leftGraph_num_iff FOL.Q.pairGraph_components_num_of_lt FOL.Q.pairGraph_iff_of_lt
  FOL.Q.pairGraph_components_num FOL.Q.pairGraph_num_iff FOL.Q.rightGraph_num_iff
  FOL.Q.succGraph_num_iff

end

end FOL
