module

public import PRAProver.Library.FOL.Arithmetic.Representation.Basic

/-!
# Representation under composition

- `Arithmetic.compGraph` is the graph formula for the composition of two unary functions.
- `Arithmetic.pairCompGraph` pairs the outputs of two programs on the same input.
- `Q.compGraph_num_iff` and `Q.pairCompGraph_num_iff` prove numeralwise
  representation from the two component proofs.
- `PA.compGraph_total` and `PA.compGraph_unique` prove totality and uniqueness from the
  component properties.

The output is at position zero and the input at position one. Further positions are parameters.
-/

namespace FOL

set_option pra.maxDepth 4096

pra

namespace Arithmetic

/-- `(compGraph p q)(y, x)` is the relational composition in which `q` computes an
intermediate value from `x` and `p` computes `y` from that value. -/
fol_def compGraph over Arithmetic (p q : formula of 2) : formula of 2 := fun y x =>
  ∃ u, q(x, u) ∧ p(u, y)

/-- `(pairCompGraph p q)(y, x)` applies `p` and `q` to `x` and pairs their outputs in
`y`. -/
fol_def pairCompGraph over Arithmetic (p q : formula of 2) : formula of 2 :=
  fun y x =>
  ∃ u v, p(x, u) ∧ q(x, v) ∧ pairGraph(y, u, v)

end Arithmetic

namespace Q

open Arithmetic

/-- Numeralwise output equivalences compose directly in Q. -/
fol_theorem compGraph_num_iff (p q : formula of 2) (a b c : Nat) : Q ⊢
    (∀ u, q(${num a}, u) ↔ u = ${num b}) → (∀ y, p(${num b}, y) ↔ y = ${num c}) → ∀ y,
    (compGraph p q)(y, ${num a}) ↔ y = ${num c} := by
  pintro hq hp y
  pconstructor
  · pintro h
    pcases h with ⟨u, hu⟩
    pcases hu with ⟨hqu, hpu⟩
    phave eu : u = ${num b}
    · papply hq[u]
      passumption
    · phave huResult : ∀ z, p(u, z) ↔ z = ${num c}
      · psubst eu
        passumption
      · papply huResult[y]
        passumption
  · pintro hy
    phave witness : ∃ u, u = ${num b}
    · pexists ${num b}
      prefl
    · pcases witness with ⟨u, hu⟩
      pexists u
      pconstructor
      · papply hq[u]
        passumption
      · psubst hu
        papply hp[y]
        passumption

fol_theorem eq_num_of_pairCompGraph (p q : formula of 2) (a b c : Nat) : Q ⊢
    (∀ u, p(${num a}, u) ↔ u = ${num b}) → (∀ v, q(${num a}, v) ↔ v = ${num c}) → ∀ y,
    (pairCompGraph p q)(y, ${num a}) → y = ${num (pair b c)} := by
  have pairing := pairGraph_num_iff b c
  pintro hp hq y
  pintro h
  pcases h with ⟨u, h⟩
  pcases h with ⟨v, h⟩
  pcases h with ⟨hu, h⟩
  pcases h with ⟨hv, huv⟩
  phave eu : u = ${num b}
  · papply hp[u]
    passumption
  · phave ev : v = ${num c}
    · papply hq[v]
      passumption
    · papply pairing[y]
      phave move : pairGraph(y, u, v) → pairGraph(y, ${num b}, ${num c})
      · psubst eu
        psubst ev
        pintro h
        passumption
      · papply move
        passumption

fol_theorem pairCompGraph_of_eq_num (p q : formula of 2) (a b c : Nat) : Q ⊢
    (∀ u, p(${num a}, u) ↔ u = ${num b}) → (∀ v, q(${num a}, v) ↔ v = ${num c}) → ∀ y, y =
    ${num (pair b c)} → (pairCompGraph p q)(y, ${num a}) := by
  have pairing := pairGraph_num_iff b c
  pintro hp hq y
  pintro hy
  phave values : ∃ u v, u = ${num b} ∧ v = ${num c}
  · pexists ${num b}
    pexists ${num c}
    pconstructor
    · prefl
    · prefl
  · pcases values with ⟨u, values⟩
    pcases values with ⟨v, values⟩
    pcases values with ⟨hu, hv⟩
    pexists u
    pexists v
    pconstructor
    · papply hp[u]
      passumption
    · pconstructor
      · papply hq[v]
        passumption
      · psubst hu
        psubst hv
        papply pairing[y]
        passumption

fol_theorem pairCompGraph_num_iff (p q : formula of 2) (a b c : Nat) : Q ⊢
    (∀ u, p(${num a}, u) ↔ u = ${num b}) → (∀ v, q(${num a}, v) ↔ v = ${num c}) → ∀ y,
    (pairCompGraph p q)(y, ${num a}) ↔ y = ${num (pair b c)} := by
  have forward := eq_num_of_pairCompGraph p q a b c
  have backward := pairCompGraph_of_eq_num p q a b c
  pintro hp hq
  phave hf : ∀ y, (pairCompGraph p q)(y, ${num a}) → y = ${num (pair b c)}
  · papply forward
    · passumption
    · passumption
  · phave hb : ∀ y, y = ${num (pair b c)} → (pairCompGraph p q)(y, ${num a})
    · papply backward
      · passumption
      · passumption
    · pintro y
      pconstructor
      · pexact hf[y]
      · pexact hb[y]

/-- Q numeralwise representations are closed under composition. The depth argument reserves
the output and input positions before any further parameters. -/
theorem represents_compGraph (f g : Nat → Nat) (p q : Nat) :
    Represents f p → Represents g q → Represents (fun x => f (g x)) (unaryFormula (fun y x =>
    compGraph (FOL.Formula.subst (FOL.liftSubst (FOL.shiftSubst language 2)
    language 2) language p) (FOL.Formula.subst (FOL.liftSubst
    (FOL.shiftSubst language 2) language 2) language q) y x)) := by
  rw [unaryFormula]
  intro hp hq x
  papply compGraph_num_iff ${p} ${q} x (g x) (f (g x))
  · pexact hq x
  · pexact hp (g x)

end Q

namespace PA

open Arithmetic

fol_theorem compGraph_total (p q : formula of 2) : PA ⊢
    (∀ x, ∃ y, p(x, y)) → (∀ x, ∃ y, q(x, y)) → ∀ x, ∃ y, (compGraph p q)(y, x) := by
  pintro hp hq x
  pcases hq[x] with ⟨u, hu⟩
  pcases hp[u] with ⟨y, hy⟩
  pexists y
  pexists u
  pconstructor
  · passumption
  · passumption

fol_theorem compGraph_unique (p q : formula of 2) : PA ⊢
    (∀ x y z, p(x, y) → p(x, z) → y = z) → (∀ x y z, q(x, y) → q(x, z) → y = z) → ∀ x y
    z, (compGraph p q)(y, x) → (compGraph p q)(z, x) → y = z :=
    by
  pintro hp hq x y z hy hz
  pcases hy with ⟨u, hu⟩
  pcases hu with ⟨hqu, hpu⟩
  pcases hz with ⟨v, hv⟩
  pcases hv with ⟨hqv, hpv⟩
  phave euv : u = v
  · papply hq[x, u, v]
    · passumption
    · passumption
  · papply hp[u, y, z]
    · passumption
    · psubst euv
      passumption

/-- Pairing the outputs of two total graphs gives a total graph. -/
fol_theorem pairCompGraph_total (p q : formula of 2) : PA ⊢
    (∀ x, ∃ y, p(x, y)) → (∀ x, ∃ y, q(x, y)) → ∀ x, ∃ y, (pairCompGraph p q)(y, x) :=
    by
  pintro hp hq x
  pcases hp[x] with ⟨u, hu⟩
  pcases hq[x] with ⟨v, hv⟩
  pcases pairGraph_total[u, v] with ⟨y, hy⟩
  pexists y
  pexists u
  pexists v
  pconstructor
  · passumption
  · pconstructor
    · passumption
    · passumption

fol_theorem pairCompGraph_unique (p q : formula of 2) : PA ⊢
    (∀ x y z, p(x, y) → p(x, z) → y = z) → (∀ x y z, q(x, y) → q(x, z) → y = z) → ∀ x y
    z, (pairCompGraph p q)(y, x) → (pairCompGraph p q)(z, x) → y
    = z := by
  pintro hp hq x y z hy hz
  pcases hy with ⟨a, hy⟩
  pcases hy with ⟨b, hy⟩
  pcases hy with ⟨ha, hy⟩
  pcases hy with ⟨hb, hy⟩
  pcases hz with ⟨c, hz⟩
  pcases hz with ⟨d, hz⟩
  pcases hz with ⟨hc, hz⟩
  pcases hz with ⟨hd, hz⟩
  phave hac : a = c
  · papply hp[x, a, c]
    · passumption
    · passumption
  · phave hbd : b = d
    · papply hq[x, b, d]
      · passumption
      · passumption
    · papply pairGraph_unique[c, d, y, z]
      · phave h : pairGraph(y, a, b) → pairGraph(y, c, d)
        · psubst hac
          psubst hbd
          pintro h
          passumption
        · papply h
          passumption
      · passumption

end PA

extract_witness FOL.PA.compGraph_total FOL.PA.compGraph_unique FOL.PA.pairCompGraph_total
  FOL.PA.pairCompGraph_unique FOL.Q.compGraph_num_iff FOL.Q.pairCompGraph_num_iff
  FOL.Q.pairCompGraph_of_eq_num FOL.Q.eq_num_of_pairCompGraph

end

end FOL
