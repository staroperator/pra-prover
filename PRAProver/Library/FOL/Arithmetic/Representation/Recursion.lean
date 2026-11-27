module

public import PRAProver.Library.FOL.Arithmetic.Representation.Beta
public import PRAProver.Library.FOL.Arithmetic.Representation.Minimization

/-!
# Representation of primitive recursion

The base formula has arguments `(output, parameter)`. The step formula has arguments
`(output, index, accumulator, parameter)`. Further positions are parameters of the formulas.

- `Arithmetic.recursionSteps` and `Arithmetic.recursionSequence` describe the initial value and
  successive steps of a finite sequence. Their lemmas prove restriction, extension, and preservation
  of entries.
- `Arithmetic.recursionGraph` describes the last value of such a sequence. Its zero and successor
  lemmas use extension of sequences and uniqueness of their entries.
- `PA.recursion_total` and `PA.recursion_unique` derive totality and uniqueness from the
  zero and successor rules. The general sequence construction satisfies those rules.
- `Arithmetic.betaSequence` and `Arithmetic.betaRecursionGraph` specialize the construction to the
  beta function. `PA.betaRecursionGraph_zero_intro`, `PA.betaRecursionGraph_zero_elim`,
  `PA.betaRecursionGraph_succ_intro`, and `PA.betaRecursionGraph_succ_elim` give the resulting
  equations.
- `Q.recStepGraph_num_iff` relates the step graph to the paired input of its program.
- `Q.sequenceEntryEq_of_isProofOf` identifies the entries of a fixed coded sequence using checked
  numeral-instance representations of its base and step.
- `Q.betaSequence_of_isProofOf` constructs a sequence proof from its numerical beta code and
  checked base and step instances.
- `Q.recWitness_num_elim` decodes a witness with numeral input and witness code.
- `Arithmetic.leastRecursionGraph` handles the paired inputs of program codes and selects a least
  sequence witness.
- `Q.leastRecursionGraph_num_iff_of_isProofOf` proves its numeral-instance representation from
  checked proofs for the base and the successive steps.
- `PA.betaRecursionGraph_total` and `PA.betaRecursionGraph_unique` prove closure under primitive
  recursion from the corresponding properties of the base and step formulas.
- `PA.leastRecursionGraph_total` and `PA.leastRecursionGraph_unique` establish these properties for
  the graph with paired inputs and a least sequence witness.

The concluding Q and PA results are collected in `Theorems.lean`.
-/

set_option pra.maxDepth 8192

namespace FOL

pra

namespace Arithmetic

/-- `(recursionSteps p q entry)(n, x)` describes a recursive sequence of
length `n` on parameter `x` through an abstract relation `entry` between indices and values. -/
fol_def recursionSteps over Arithmetic (p : formula of 2) (q : formula of 4) (entry : formula of 2)
    : formula of 2 := fun n x =>
  (∃ u, p(x, u) ∧ entry(0, u)) ∧
    ∀ i, i < n → ∃ u v, entry(i, u) ∧ q(x, u, i, v) ∧ entry(S i, v)

/-- `(sequenceExtendable entry)` states that every finite sequence of length `n` can be
extended at index `n` by any prescribed value `z`. -/
fol_def sequenceExtendable over Arithmetic (entry : formula of 4) : formula :=
  ∀ b c n z, ∃ d e,
    (∀ i r, i < n → entry(i, c, b, r) → entry(i, e, d, r)) ∧ entry(n, e, d, z)

/-- `(entryUnique entry)` states that each indexed entry of a fixed code `(b, c)` has at
most one value. -/
fol_def entryUnique over Arithmetic (entry : formula of 4) : formula :=
  ∀ r s b c i, entry(i, c, b, r) → entry(i, c, b, s) → r = s

/-- `(recursionSequence p q entry)(b, c, n, x)` states that `(b, c)` encodes
a finite sequence of length `n` on parameter `x` satisfying the base formula `p` and step formula
`q`. -/
fol_def recursionSequence over Arithmetic (p : formula of 2) (q : formula of 4)
    (entry : formula of 4) : formula of 4 := fun b c n x =>
  (∃ u, p(x, u) ∧ entry(0, c, b, u)) ∧
    ∀ i, i < n → ∃ u v,
      entry(i, c, b, u) ∧ q(x, u, i, v) ∧ entry(S i, c, b, v)

/-- `(recursionGraph p q entry)(y, n, x)` states that `y` is the final value
at index `n` of a coded recursive sequence on parameter `x`. -/
fol_def recursionGraph over Arithmetic (p : formula of 2) (q : formula of 4) (entry : formula of 4)
    : formula of 3 := fun y n x =>
  ∃ b c, (recursionSequence p q entry)(b, c, n, x) ∧
    entry(n, c, b, y)

/-- `(betaSequence p q)(b, c, n, x)` states that the beta code `(b, c)` starts with a
base value for `p` on `x` and satisfies the step graph `q` below `n`. -/
fol_def betaSequence over Arithmetic (p : formula of 2) (q : formula of 4) : formula of 4 :=
  fun b c n x =>
  (∃ u, p(x, u) ∧ betaBounded(u, b, c, 0)) ∧
    ∀ i, i < n → ∃ u v,
      betaBounded(u, b, c, i) ∧ q(x, u, i, v) ∧ betaBounded(v, b, c, S i)

/-- `(betaRecursionGraph p q)(y, n, x)` states that `y` is the value at index `n` of a
beta sequence for `p` and `q` on parameter `x`. -/
fol_def betaRecursionGraph over Arithmetic (p : formula of 2) (q : formula of 4) : formula of 3 :=
  fun y n x =>
  ∃ b c, (betaSequence p q)(b, c, n, x) ∧ betaBounded(y, b, c, n)

/-- `(recStepGraph q)(v, i, u, x)` applies the unary step graph `q` to the encoded triple
`pair x (pair i u)` with output `v`. -/
fol_def recStepGraph over Arithmetic (q : formula of 2) : formula of 4 := fun v i u x =>
  ∃ a b, pairGraph(a, i, u) ∧ pairGraph(b, x, a) ∧ q(b, v)

/-- `recStepFormula q` is the step formula for `q` with positions `(output, index, accumulator,
parameter)`. -/
fol_def recStepFormula over Arithmetic (q : formula of 2) : formula of 4 :=
  ${recStepGraph
    (FOL.Formula.subst
      (FOL.liftSubst (FOL.shiftSubst language 4) language 2)
      language q)
    (Term.var language 0) (Term.var language 1)
    (Term.var language 2) (Term.var language 3)}

theorem recStepFormula_eq (q : Nat) :
    recStepFormula q = recStepGraph
      (FOL.Formula.subst
        (FOL.liftSubst (FOL.shiftSubst language 4) language 2)
        language q)
      (Term.var language 0) (Term.var language 1)
      (Term.var language 2) (Term.var language 3) := rfl

/-- `(recWitness p q)(y, z, t)` states that `t` encodes the beta parameters `(b, c)` of
a computation sequence with output `y` on paired input `z = pair x n`. -/
fol_def recWitness over Arithmetic (p q : formula of 2) : formula of 3 := fun y z t =>
  ∃ x n b c, pairGraph(z, x, n) ∧ pairGraph(t, b, c) ∧
    (betaSequence p (fun a u j v => (recStepGraph q)(v, j, u, a)))(b, c, n, x) ∧
    betaBounded(y, b, c, n)

/-- `recWitnessFormula p q` is the recursion witness formula for `p` and `q` with positions
`(output, input, witness)`. -/
fol_def recWitnessFormula over Arithmetic (p q : formula of 2) : formula of 3 :=
  ${recWitness
    (FOL.Formula.subst
      (FOL.liftSubst (FOL.shiftSubst language 3) language 2)
      language p)
    (FOL.Formula.subst
      (FOL.liftSubst (FOL.shiftSubst language 3) language 2)
      language q)
    (Term.var language 0) (Term.var language 1)
    (Term.var language 2)}

theorem recWitnessFormula_eq (p q : Nat) :
    recWitnessFormula p q = recWitness
      (FOL.Formula.subst
        (FOL.liftSubst (FOL.shiftSubst language 3) language 2)
        language p)
      (FOL.Formula.subst
        (FOL.liftSubst (FOL.shiftSubst language 3) language 2)
        language q)
      (Term.var language 0) (Term.var language 1)
      (Term.var language 2) := rfl

/-- `(leastRecursionGraph p q)(y, x)` selects the output `y` of a least
computation-sequence witness on paired input `x`. This additional condition allows Q to rule out
other outputs at each numeral input. -/
fol_def leastRecursionGraph over Arithmetic (p q : formula of 2) : formula of 2 := fun y x =>
  (minGraph (fun t a v => (recWitness p q)(v, a, t)))(y, x)

end Arithmetic

end

open PRAProver.Library.FOL.DSL in
run_cmd do
  registerCalculation `FOL.Arithmetic.recStepFormula_eq
  registerCalculation `FOL.Arithmetic.recWitnessFormula_eq

pra

namespace PA

open Arithmetic

fol_theorem recursionSteps_mono (p : formula of 2) (q : formula of 4)
    (sourceRel targetRel : formula of 2) : PA ⊢
    ∀ n x, (∀ i r, i < S n → sourceRel(i, r) → targetRel(i, r)) →
    (recursionSteps p q sourceRel)(n, x) → (recursionSteps p q targetRel)(n, x) :=
    by
  pintro n x preserve sequence
  pcases sequence with ⟨base, steps⟩
  pconstructor
  · pcases base with ⟨r, hr⟩
    pcases hr with ⟨hpr, hbr⟩
    pexists r
    pconstructor
    · passumption
    · papply preserve[0, r]
      · pexact Q.zero_lt_succ[n]
      · passumption
  · pintro i hi
    phave old : ∃ a z,
        sourceRel(i, a) ∧ q(x, a, i, z) ∧ sourceRel(S i, z)
    · papply steps[i]
      passumption
    · pcases old with ⟨a, ha⟩
      pcases ha with ⟨z, hz⟩
      pcases hz with ⟨hba, hrest⟩
      pcases hrest with ⟨hqz, hbz⟩
      pexists a
      pexists z
      pconstructor
      · papply preserve[i, a]
        · papply lt_succ_of_lt[i, n]
          passumption
        · passumption
      · pconstructor
        · passumption
        · papply preserve[S i, z]
          · papply Q.succ_lt_succ_iff[i, n]
            passumption
          · passumption

fol_theorem recursionSteps_succ (p : formula of 2) (q : formula of 4)
    (sourceRel : formula of 2) : PA ⊢
    ∀ n x u v, (recursionSteps p q sourceRel)(n, x) →
    sourceRel(n, u) → q(x, u, n, v) → sourceRel(S n, v) →
    (recursionSteps p q sourceRel)(S n, x) := by
  pintro n x u v sequence hu hv last
  pcases sequence with ⟨base, steps⟩
  pconstructor
  · passumption
  · pintro i hi
    phave cases : i < n ∨ i = n
    · papply lt_succ_iff_lt_or_eq[i, n]
      passumption
    · pcases cases with hin | ein
      · papply steps[i]
        passumption
      · psubst ein
        pexists u
        pexists v
        pconstructor
        · passumption
        · pconstructor
          · passumption
          · passumption

fol_theorem exists_exists_mono (p q : formula of 2) : PA ⊢
    (∀ d e, p(e, d) → q(e, d)) → (∃ d e, p(e, d)) → ∃ d e, q(e, d) := by
  pintro transform source
  pcases source with ⟨d, hd⟩
  pcases hd with ⟨e, he⟩
  pexists d
  pexists e
  papply transform[d, e]
  passumption

fol_theorem recursionSequence_of_succ (p : formula of 2) (q entry : formula of 4) : PA ⊢
    ∀ b c n x, (recursionSequence p q entry)(b, c, S n, x) →
    (recursionSequence p q entry)(b, c, n, x) := by
  pintro b c n x h
  pcases h with ⟨base, steps⟩
  pconstructor
  · passumption
  · pintro i hi
    papply steps[i]
    papply lt_succ_of_lt[i, n]
    passumption

fol_theorem recursionSequence_mono (p : formula of 2) (q entry : formula of 4) : PA ⊢
    ∀ b c n x d e, (∀ i r, i < S n → entry(i, c, b, r) → entry(i, e, d, r)) →
    (recursionSequence p q entry)(b, c, n, x) →
    (recursionSequence p q entry)(d, e, n, x) := by
  pintro b c n x d e
  papply (recursionSteps_mono (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i r => entry(i, c, b, r)) (fun i r => entry(i, e, d, r)))[n, x]

fol_theorem recursionSequence_succ (p : formula of 2) (q entry : formula of 4) : PA ⊢
    ∀ b c n x u v, (recursionSequence p q entry)(b, c, n, x) →
    entry(n, c, b, u) → q(x, u, n, v) → entry(S n, c, b, v) →
    (recursionSequence p q entry)(b, c, S n, x) := by
  pintro b c
  papply recursionSteps_succ (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i r => entry(i, c, b, r))

/-- Extend a recursive sequence by one verified step, changing the code when necessary. -/
fol_theorem exists_recursionSequence_succ (p : formula of 2) (q entry : formula of 4) : PA ⊢
    ∀ b c n v x u, (sequenceExtendable entry) →
    (recursionSequence p q entry)(b, c, n, x) → entry(n, c, b, u) → q(x, u, n, v) →
    ∃ d e,
    (recursionSequence p q entry)(d, e, S n, x) ∧
    entry(S n, e, d, v) := by
  pintro b c n v x u extension sequence hu hv
  papply exists_exists_mono
      (fun e d => (∀ i r, i < S n → entry(i, c, b, r) → entry(i, e, d, r)) ∧
      entry(S n, e, d, v)) (fun e d => (recursionSequence p q entry)(d, e, S n, x) ∧
      entry(S n, e, d, v))
  · pintro d e chosen
    pcases chosen with ⟨preserve, last⟩
    pconstructor
    · papply (recursionSequence_succ (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
        (fun i c b r => entry(i, c, b, r)))[d, e, n, x, u, v]
      · papply (recursionSequence_mono (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
          (fun i c b r => entry(i, c, b, r)))[b, c, n, x, d, e]
        · passumption
        · passumption
      · papply preserve[n, u]
        · pexact lt_succ_self[n]
        · passumption
      · passumption
      · passumption
    · passumption
  · pexact extension[b, c, S n, v]

fol_theorem recursionGraph_zero_elim (p : formula of 2) (q entry : formula of 4) : PA ⊢
    ∀ y x, (entryUnique entry) → (recursionGraph p q entry)(y, 0, x) → p(x, y) := by
  pintro y x unique
  pintro h
  pcases h with ⟨b, hb⟩
  pcases hb with ⟨c, hc⟩
  pcases hc with ⟨sequence, hy⟩
  pcases sequence with ⟨base, steps⟩
  pcases base with ⟨u, hu⟩
  pcases hu with ⟨hpu, hub⟩
  phave ey : y = u
  · papply unique[y, u, b, c, 0]
    · passumption
    · passumption
  · psubst ey
    passumption

fol_theorem recursionGraph_zero_intro (p : formula of 2) (q entry : formula of 4) : PA ⊢
    ∀ y x, (sequenceExtendable entry) → p(x, y) →
    (recursionGraph p q entry)(y, 0, x) := by
  pintro y x extension
  pintro h
  pcases extension[0, 0, 0, y] with ⟨b, hb⟩
  pcases hb with ⟨c, hc⟩
  pcases hc with ⟨previous, hy⟩
  pexists b
  pexists c
  pconstructor
  · pconstructor
    · pexists y
      pconstructor
      · passumption
      · passumption
    · pintro i hi
      pexfalso
      papply Q.not_lt_zero[i]
      passumption
  · passumption

fol_theorem recursionGraph_succ_elim (p : formula of 2) (q entry : formula of 4) : PA ⊢
    ∀ y n x, (entryUnique entry) → (recursionGraph p q entry)(y, S n, x) →
    ∃ u, (recursionGraph p q entry)(u, n, x) ∧ q(x, u, n, y) :=
          by
  pintro y n x unique
  pintro h
  pcases h with ⟨b, hb⟩
  pcases hb with ⟨c, hc⟩
  pcases hc with ⟨sequence, hy⟩
  phave previous : (recursionSequence p q entry)(b, c, n, x)
  · papply (recursionSequence_of_succ (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i c b r => entry(i, c, b, r)))[b, c, n, x]
    passumption
  · pcases sequence with ⟨base, steps⟩
    phave nextEntry : ∃ u v,
        entry(n, c, b, u) ∧ q(x, u, n, v) ∧ entry(S n, c, b, v)
    · papply steps[n]
      pexact lt_succ_self[n]
    · pcases nextEntry with ⟨u, hu⟩
      pcases hu with ⟨v, hv⟩
      pcases hv with ⟨hub, hrest⟩
      pcases hrest with ⟨hqv, hvb⟩
      pexists u
      pconstructor
      · pexists b
        pexists c
        pconstructor
        · passumption
        · passumption
      · phave ey : y = v
        · papply unique[y, v, b, c, S n]
          · passumption
          · passumption
        · psubst ey
          passumption

fol_theorem recursionGraph_succ_intro (p : formula of 2) (q entry : formula of 4) : PA ⊢
    ∀ y n x, (sequenceExtendable entry) →
    (∃ u, (recursionGraph p q entry)(u, n, x) ∧ q(x, u, n, y)) →
    (recursionGraph p q entry)(y, S n, x) := by
  pintro y n x extension
  pintro h
  pcases h with ⟨u, hu⟩
  pcases hu with ⟨previous, step⟩
  pcases previous with ⟨b, hb⟩
  pcases hb with ⟨c, hc⟩
  pcases hc with ⟨sequence, value⟩
  papply (exists_recursionSequence_succ (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i c b r => entry(i, c, b, r)))[b, c, n, y, x, u]
  · passumption
  · passumption
  · passumption
  · passumption

fol_theorem recursion_total (p : formula of 2) (q : formula of 4) (graph : formula of 3) : PA ⊢
    (∀ y x, p(x, y) → graph(x, 0, y)) →
    (∀ y n x u, graph(x, n, u) → q(x, u, n, y) → graph(x, S n, y)) → (∀ x, ∃ y, p(x, y))
    → (∀ i u x, ∃ v, q(x, u, i, v)) → ∀ x n, ∃ y, graph(x, n, y) := by
  pintro base step hp hq x n
  pinduction n with
  | zero =>
    pcases hp[x] with ⟨y, hy⟩
    pexists y
    papply base[y, x]
    passumption
  | succ k ih =>
    pcases ih with ⟨u, hu⟩
    pcases hq[k, u, x] with ⟨v, hv⟩
    pexists v
    papply step[v, k, x, u]
    · passumption
    · passumption

fol_theorem recursion_unique (p : formula of 2) (q : formula of 4) (graph : formula of 3) : PA ⊢
    (∀ y x, graph(x, 0, y) → p(x, y)) →
    (∀ y n x, graph(x, S n, y) → ∃ u, graph(x, n, u) ∧ q(x, u, n, y)) →
    (∀ x y z, p(x, y) → p(x, z) → y = z) →
    (∀ i u x y z, q(x, u, i, y) → q(x, u, i, z) → y = z) → ∀ x n y z, graph(x, n, y) →
    graph(x, n, z) → y = z := by
  pintro base step hp hq x n
  pinduction n with
  | zero =>
    pintro y z hy hz
    papply hp[x, y, z]
    · papply base[y, x]
      passumption
    · papply base[z, x]
      passumption
  | succ k ih =>
    pintro y z hy hz
    phave ystep : ∃ u,
        graph(x, k, u) ∧ q(x, u, k, y)
    · papply step[y, k, x]
      passumption
    · pcases ystep with ⟨u, hu⟩
      pcases hu with ⟨recurY, stepY⟩
      phave zstep : ∃ v,
          graph(x, k, v) ∧ q(x, v, k, z)
      · papply step[z, k, x]
        passumption
      · pcases zstep with ⟨v, hv⟩
        pcases hv with ⟨recurZ, stepZ⟩
        phave euv : u = v
        · papply ih[u, v]
          · passumption
          · passumption
        · papply hq[k, u, x, y, z]
          · passumption
          · psubst euv
            passumption

fol_theorem recursionGraph_total (p : formula of 2) (q entry : formula of 4) : PA ⊢
    (sequenceExtendable entry) → (∀ x, ∃ y, p(x, y)) →
    (∀ i u x, ∃ v, q(x, u, i, v)) → ∀ x n, ∃ y, (recursionGraph p q entry)(y, n, x) :=
    by
  pintro extension
  papply recursion_total (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun x n y => (recursionGraph p q entry)(y, n, x))
  · pintro y x
    papply (recursionGraph_zero_intro (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
        (fun i c b r => entry(i, c, b, r)))[y, x]
    passumption
  · pintro y n x u previous step
    papply (recursionGraph_succ_intro (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
        (fun i c b r => entry(i, c, b, r)))[y, n, x]
    · passumption
    · pexists u
      pconstructor
      · passumption
      · passumption

fol_theorem recursionGraph_unique (p : formula of 2) (q entry : formula of 4) : PA ⊢
    (entryUnique entry) → (∀ x y z, p(x, y) → p(x, z) → y = z) →
    (∀ i u x y z, q(x, u, i, y) → q(x, u, i, z) → y = z) →
    ∀ x n y z, (recursionGraph p q entry)(y, n, x) →
    (recursionGraph p q entry)(z, n, x) → y = z := by
  pintro unique
  papply recursion_unique (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun x n y => (recursionGraph p q entry)(y, n, x))
  · pintro y x
    papply (recursionGraph_zero_elim (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
        (fun i c b r => entry(i, c, b, r)))[y, x]
    passumption
  · pintro y n x
    papply (recursionGraph_succ_elim (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
        (fun i c b r => entry(i, c, b, r)))[y, n, x]
    passumption

fol_theorem betaSequence_of_succ (p q : Nat) : PA ⊢
    ∀ b c n x, (betaSequence ${p} ${q})(b, c, S n, x) → (betaSequence ${p} ${q})(b, c, n, x) := by
  pintro b c n x h
  pcases h with ⟨base, steps⟩
  pconstructor
  · passumption
  · pintro i hi
    papply steps[i]
    papply lt_succ_of_lt[i, n]
    passumption

fol_theorem betaSequence_mono (p : formula of 2) (q : formula of 4) : PA ⊢
    ∀ b c n x d e,
    (∀ i r, i < S n → betaBounded(r, b, c, i) → betaBounded(r, d, e, i)) →
    (betaSequence p q)(b, c, n, x) → (betaSequence p q)(d, e, n, x) := by
  pintro b c n x d e
  papply (recursionSteps_mono (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i r => betaBounded(r, b, c, i)) (fun i r => betaBounded(r, d, e, i)))[n, x]

fol_theorem betaSequence_succ (p : formula of 2) (q : formula of 4) : PA ⊢
    ∀ b c n x u v, (betaSequence p q)(b, c, n, x) →
    betaBounded(u, b, c, n) → q(x, u, n, v) → betaBounded(v, b, c, S n) →
    (betaSequence p q)(b, c, S n, x) := by
  pintro b c
  papply recursionSteps_succ (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i r => betaBounded(r, b, c, i))

/-- Extend a recursive sequence by one verified step, changing its beta code when necessary. -/
fol_theorem exists_betaSequence_succ (p : formula of 2) (q : formula of 4) : PA ⊢
    ∀ b c n v x u, (betaSequence p q)(b, c, n, x) →
    betaBounded(u, b, c, n) → q(x, u, n, v) → ∃ d e, (betaSequence p q)(d, e, S n, x) ∧
    betaBounded(v, d, e, S n) :=
            by
  pintro b c n v x u
  papply (exists_recursionSequence_succ (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i c b r => betaBounded(r, b, c, i)))[b, c, n, v, x, u]
  pexact betaBounded_extend

fol_theorem betaRecursionGraph_zero_elim (p : formula of 2) (q : formula of 4) : PA ⊢
    ∀ y x, (betaRecursionGraph p q)(y, 0, x) → p(x, y) := by
  pintro y x
  papply (recursionGraph_zero_elim (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i c b r => betaBounded(r, b, c, i)))[y, x]
  pexact betaBounded_unique

fol_theorem betaRecursionGraph_zero_intro (p : formula of 2) (q : formula of 4) : PA ⊢
    ∀ y x, p(x, y) → (betaRecursionGraph p q)(y, 0, x) := by
  pintro y x
  papply (recursionGraph_zero_intro (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i c b r => betaBounded(r, b, c, i)))[y, x]
  pexact betaBounded_extend

fol_theorem betaRecursionGraph_succ_elim (p : formula of 2) (q : formula of 4) : PA ⊢
    ∀ y n x, (betaRecursionGraph p q)(y, S n, x) →
    ∃ u, (betaRecursionGraph p q)(u, n, x) ∧ q(x, u, n, y) := by
  pintro y n x
  papply (recursionGraph_succ_elim (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i c b r => betaBounded(r, b, c, i)))[y, n, x]
  pexact betaBounded_unique

fol_theorem betaRecursionGraph_succ_intro (p : formula of 2) (q : formula of 4) : PA ⊢
    ∀ y n x, (∃ u, (betaRecursionGraph p q)(u, n, x) ∧ q(x, u, n, y)) →
    (betaRecursionGraph p q)(y, S n, x) := by
  pintro y n x
  papply (recursionGraph_succ_intro (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i c b r => betaBounded(r, b, c, i)))[y, n, x]
  pexact betaBounded_extend

/-- PA proves that primitive recursion is total when the base and step graphs are total. -/
fol_theorem betaRecursionGraph_total (p : formula of 2) (q : formula of 4) : PA ⊢
    (∀ x, ∃ y, p(x, y)) → (∀ i u x, ∃ v, q(x, u, i, v)) →
    ∀ x n, ∃ y, (betaRecursionGraph p q)(y, n, x) := by
  papply recursionGraph_total (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i c b r => betaBounded(r, b, c, i))
  pexact betaBounded_extend

/-- If the base and step graphs have unique outputs, the recursion graph does too. -/
fol_theorem betaRecursionGraph_unique (p : formula of 2) (q : formula of 4) : PA ⊢
    (∀ x y z, p(x, y) → p(x, z) → y = z) →
    (∀ i u x y z, q(x, u, i, y) → q(x, u, i, z) → y = z) → ∀ x n y z,
    (betaRecursionGraph p q)(y, n, x) →
    (betaRecursionGraph p q)(z, n, x) → y = z := by
  papply recursionGraph_unique (fun s r => p(s, r)) (fun t s i r => q(t, s, i, r))
      (fun i c b r => betaBounded(r, b, c, i))
  pexact betaBounded_unique

fol_theorem recStepGraph_total (q : formula of 2) : PA ⊢
    (∀ x, ∃ y, q(x, y)) → ∀ i u x, ∃ v, (recStepGraph q)(v, i, u, x) := by
  pintro hq i u x
  pcases pairGraph_total[i, u] with ⟨a, ha⟩
  pcases pairGraph_total[x, a] with ⟨b, hb⟩
  pcases hq[b] with ⟨v, hv⟩
  pexists v
  pexists a
  pexists b
  pconstructor
  · passumption
  · pconstructor
    · passumption
    · passumption

fol_theorem recStepGraph_unique (q : formula of 2) : PA ⊢
    (∀ x y z, q(x, y) → q(x, z) → y = z) → ∀ i u x v w, (recStepGraph q)(v, i, u, x) →
    (recStepGraph q)(w, i, u, x) → v = w := by
  pintro hq i u x v w hv hw
  pcases hv with ⟨a, hv⟩
  pcases hv with ⟨b, hv⟩
  pcases hv with ⟨ha, hv⟩
  pcases hv with ⟨hb, hqb⟩
  pcases hw with ⟨c, hw⟩
  pcases hw with ⟨d, hw⟩
  pcases hw with ⟨hc, hw⟩
  pcases hw with ⟨hd, hqd⟩
  phave hac : a = c
  · papply pairGraph_unique[i, u, a, c]
    · passumption
    · passumption
  · phave hbd : b = d
    · papply pairGraph_unique[x, c, b, d]
      · phave h : pairGraph(b, x, a) → pairGraph(b, x, c)
        · psubst hac
          pintro h
          passumption
        · papply h
          passumption
      · passumption
    · papply hq[d, v, w]
      · phave h : q(b, v) → q(d, v)
        · psubst hbd
          pintro h
          passumption
        · papply h
          passumption
      · passumption

fol_theorem recWitness_total (p q : formula of 2) : PA ⊢
    (∀ x, ∃ y, p(x, y)) → (∀ x, ∃ y, q(x, y)) → ∀ z, ∃ t y, (recWitness p q)(y, z, t) :=
    by
  pintro hp hq
  phave ht : ∀ x n, ∃ y, (betaRecursionGraph p ${recStepFormula q})(y, n, x)
  · papply betaRecursionGraph_total (fun x y => p(x, y))
      (fun x u i v => ${recStepFormula q}[x, u, i, v])
    · passumption
    · papply recStepGraph_total (fun x y => q(x, y))
      passumption
  · pintro z
    pcases pairGraph_surjective[z] with ⟨x, hex⟩
    pcases hex with ⟨n, hxn⟩
    pcases ht[x, n] with ⟨y, hy⟩
    pcases hy with ⟨b, hex⟩
    pcases hex with ⟨c, hc⟩
    pcases hc with ⟨sequence, last⟩
    pcases pairGraph_total[b, c] with ⟨t, hbc⟩
    pexists t
    pexists y
    pexists x
    pexists n
    pexists b
    pexists c
    pconstructor
    · passumption
    · pconstructor
      · passumption
      · pconstructor
        · passumption
        · passumption

fol_theorem exists_four_project (p q : formula of 2) (r : formula of 4) : PA ⊢
    (∃ x n b c, p(n, x) ∧ q(c, b) ∧ r(x, n, c, b)) → ∃ x n, p(n, x) ∧ ∃ b c,
    r(x, n, c, b) := by
  pintro witness
  pcases witness with ⟨x, witness⟩
  pcases witness with ⟨n, witness⟩
  pcases witness with ⟨b, witness⟩
  pcases witness with ⟨c, witness⟩
  pcases witness with ⟨hp, rest⟩
  pcases rest with ⟨hq, hr⟩
  pexists x
  pexists n
  pconstructor
  · passumption
  · pexists b
    pexists c
    passumption

fol_theorem recWitness_betaRecursionGraph (p q : Nat) : PA ⊢
    ∀ y z t, (recWitness ${p} ${q})(y, z, t) →
    ∃ x n, pairGraph(z, x, n) ∧
    (betaRecursionGraph ${p} ${recStepFormula q})(y, n, x) := by
  pintro y z t
  papply exists_four_project (fun n x => pairGraph(z, x, n)) (fun c b => pairGraph(t, b, c))
      (fun x n c b =>
      (betaSequence ${p} ${recStepFormula q})(b, c, n, x) ∧ betaBounded(y, b, c, n))

fol_theorem pairGraph_exists_unique (p : formula of 3) : PA ⊢
    (∀ x n y v, p(x, n, y) → p(x, n, v) → y = v) → ∀ z y v,
    (∃ x n, pairGraph(z, x, n) ∧ p(x, n, y)) → (∃ x n, pairGraph(z, x, n) ∧ p(x, n, v)) → y =
    v := by
  pintro unique z y v hy hv
  pcases hy with ⟨x, hy⟩
  pcases hy with ⟨n, hy⟩
  pcases hy with ⟨hxn, hpy⟩
  pcases hv with ⟨a, hv⟩
  pcases hv with ⟨m, hv⟩
  pcases hv with ⟨ham, hpv⟩
  phave hx : x = a
  · papply pairGraph_injective[z, x, n, a, m]
    · passumption
    · passumption
  · phave hn : n = m
    · papply pairGraph_injective[z, x, n, a, m]
      · passumption
      · passumption
    · phave move : p(x, n, y) → p(a, m, y)
      · psubst hx
        psubst hn
        pintro h
        passumption
      · papply unique[a, m, y, v]
        · papply move
          passumption
        · passumption

fol_theorem unique_of_forall_imp (p : formula of 2) (q : formula of 3) : PA ⊢
    (∀ x y z, p(x, y) → p(x, z) → y = z) → (∀ y x t, q(t, x, y) → p(x, y)) → ∀ x y z t
    s, q(t, x, y) → q(s, x, z) → y = z := by
  pintro unique project x y z t s hy hz
  papply unique[x, y, z]
  · papply project[y, x, t]
    passumption
  · papply project[z, x, s]
    passumption

fol_theorem recWitness_unique_of_betaRecursionGraph_unique (p q : Nat) : PA ⊢
    (∀ x n y v, (betaRecursionGraph ${p} ${recStepFormula q})(y, n, x) →
      (betaRecursionGraph ${p} ${recStepFormula q})(v, n, x) → y = v) →
    ∀ z y v t s, (recWitness ${p} ${q})(y, z, t) →
    (recWitness ${p} ${q})(v, z, s) → y = v := by
  pintro unique
  papply unique_of_forall_imp
      (fun z y => ∃ x n, pairGraph(z, x, n) ∧
      (betaRecursionGraph ${p} ${recStepFormula q})(y, n, x)) (fun t z y =>
      (recWitness ${p} ${q})(y, z, t))
  · papply pairGraph_exists_unique
      (fun x n y => (betaRecursionGraph ${p} ${recStepFormula q})(y, n, x))
    passumption
  · pexact recWitness_betaRecursionGraph p q

fol_theorem recWitness_unique (p q : formula of 2) : PA ⊢
    (∀ x y z, p(x, y) → p(x, z) → y = z) → (∀ x y z, q(x, y) → q(x, z) → y = z) → ∀ z y
    v t s, (recWitness p q)(y, z, t) → (recWitness p q)(v, z, s)
    → y = v := by
  have rule := recWitness_unique_of_betaRecursionGraph_unique p q
  pintro hp hq
  papply rule
  papply betaRecursionGraph_unique (fun x y => p(x, y))
      (fun x u i v => ${recStepFormula q}[x, u, i, v])
  · passumption
  · papply recStepGraph_unique (fun x y => q(x, y))
    passumption

/-- Total base and step graphs give a total least-witness recursion graph. -/
fol_theorem leastRecursionGraph_total (p q : formula of 2) : PA ⊢
    (∀ x, ∃ y, p(x, y)) → (∀ x, ∃ y, q(x, y)) →
    ∀ x, ∃ y, (leastRecursionGraph p q)(y, x) := by
  have selection := minGraph_total (recWitnessFormula p q)
  have witness := recWitness_total p q
  rw [recWitnessFormula] at selection
  rw [leastRecursionGraph]
  pintro hp hq
  papply selection
  papply witness
  · passumption
  · passumption

/-- Unique base and step outputs give a unique output of the least-witness graph. -/
fol_theorem leastRecursionGraph_unique (p q : formula of 2) : PA ⊢
    (∀ x y z, p(x, y) → p(x, z) → y = z) →
    (∀ x y z, q(x, y) → q(x, z) → y = z) → ∀ x y z,
    (leastRecursionGraph p q)(y, x) →
    (leastRecursionGraph p q)(z, x) → y = z := by
  have selection := minGraph_unique (recWitnessFormula p q)
  have witness := recWitness_unique p q
  rw [recWitnessFormula] at selection
  rw [leastRecursionGraph, leastRecursionGraph]
  pintro hp hq
  papply selection
  papply witness
  · passumption
  · passumption

end PA

namespace Q

open Arithmetic

fol_theorem exists_eq_elim (p q : formula of 1) : Q ⊢
    ∀ a, (∀ x, p(x) → x = a) → (∃ x, p(x) ∧ q(x)) → q(a) := by
  pintro a unique witness
  pcases witness with ⟨x, witness⟩
  pcases witness with ⟨hx, hqx⟩
  phave eq : x = a
  · papply unique[x]
    passumption
  · phave move : q(x) → q(a)
    · psubst eq
      pintro h
      passumption
    · papply move
      passumption

fol_theorem exists_exists_eq_elim (p : formula of 1) (q : formula of 2) (r : formula of 1) : Q ⊢
    ∀ a b, (∀ x, p(x) → x = a) → (∀ y, q(a, y) → y = b) →
    (∃ x y, p(x) ∧ q(x, y) ∧ r(y)) → r(b) := by
  pintro a b firstUnique secondUnique witness
  pcases witness with ⟨x, witness⟩
  pcases witness with ⟨y, witness⟩
  pcases witness with ⟨hx, witness⟩
  pcases witness with ⟨hy, hr⟩
  phave ex : x = a
  · papply firstUnique[x]
    passumption
  · phave ey : y = b
    · papply secondUnique[y]
      phave move : q(x, y) → q(a, y)
      · psubst ex
        pintro h
        passumption
      · papply move
        passumption
    · phave move : r(y) → r(b)
      · psubst ey
        pintro h
        passumption
      · papply move
        passumption

fol_theorem exists_exists_conj_intro (p : formula of 1) (q : formula of 2)
    (r : formula of 1) : Q ⊢
    ∀ a b, p(a) → q(a, b) → r(b) → ∃ x y, p(x) ∧ q(x, y) ∧ r(y) := by
  pintro a b ha hb hr
  pexists a
  pexists b
  pconstructor
  · passumption
  · pconstructor
    · passumption
    · passumption

end Q

namespace Arithmetic

/-- `(representsAt p a b)` states that the graph `p` has output `num b` on
numeral input `num a`. -/
fol_def representsAt over Arithmetic (p : formula of 2) (a : Nat) (b : Nat) : formula :=
  ∀ y, p(${num a}, y) ↔ y = ${num b}

/-- `(stepRepresentsAt q x i u v)` states that the step graph `q`
at numeral parameter `x`, index `i`, and accumulator `u` has output `num v`. -/
fol_def stepRepresentsAt over Arithmetic (q : formula of 4) (x : Nat) (i : Nat) (u : Nat)
    (v : Nat) : formula :=
  ∀ y, q(${num x}, ${num u}, ${num i}, y) ↔ y = ${num v}

/-- `(sequenceEntryEq p q b c n x i r)`
states that if `b` and `c` describe a sequence for `p` and `q`, every value decoded at index `i`
equals `num r`. -/
fol_def sequenceEntryEq over Arithmetic (p : formula of 2) (q : formula of 4) (b : Nat) (c : Nat)
    (n : Nat) (x : Nat) (i : Nat) (r : Nat) : formula :=
  (betaSequence p q)(${num b}, ${num c}, ${num n}, ${num x}) →
    ∀ y, betaBounded(y, ${num b}, ${num c}, ${num i}) → y = ${num r}

end Arithmetic

namespace Q

open Arithmetic

fol_theorem betaBounded_num_unique (b c i : Nat) : Q ⊢
    ∀ y z, betaBounded(y, ${num b}, ${num c}, ${num i}) →
    betaBounded(z, ${num b}, ${num c}, ${num i}) → y = z := by
  have represented := betaBounded_num_iff b c i
  pintro y z hy hz
  phave ey : y = ${num (_root_.beta b c i)}
  · papply represented[y]
    passumption
  · phave ez : z = ${num (_root_.beta b c i)}
    · papply represented[z]
      passumption
    · prw [ey, ez]

theorem sequenceEntryEq_zero_of_isProofOf (p q b c n x r proof : Nat) :
    IsProofOf language isAxiom (representsAt p x r) proof →
    (Q ⊢ ${sequenceEntryEq p q b c n x 0 r}) := by
  intro hb
  have base : Q ⊢ ${representsAt p x (r)} := (proof, hb)
  rw [representsAt] at base
  rw [sequenceEntryEq]
  have unique := betaBounded_num_unique b c 0
  phave entryUnique : ∀ y z, betaBounded(y, ${num b}, ${num c}, 0) →
      betaBounded(z, ${num b}, ${num c}, 0) → y = z
  · pexact unique
  · phave baseValue : ∀ u, ${p}[${num x}, u] ↔ u = ${num r}
    · pexact base
    · pintro seq y hy
      papply entryUnique[y, ${num r}]
      · passumption
      · papply (exists_eq_elim (fun z => ${p}[${num x}, z])
          (fun z => betaBounded(z, ${num b}, ${num c}, 0)))[${num r}]
        · pintro z hz
          papply baseValue[z]
          passumption
        · pcases seq with ⟨initial, steps⟩
          passumption

theorem sequenceEntryEq_succ_of_isProofOf (p q b c n x k r s previous proof : Nat) :
    k < n → IsProofOf language isAxiom (sequenceEntryEq p q b c n x k r) previous → IsProofOf
    language isAxiom (stepRepresentsAt q x k r s) proof → (Q ⊢ ${sequenceEntryEq p q b c n x (S k)
        s}) := by
  intro hk hp hs
  have previous : Q ⊢ ${sequenceEntryEq p q b c n x k r} := (previous, hp)
  have step : Q ⊢ ${stepRepresentsAt q x k (r) (s)} :=
    (proof, hs)
  rw [sequenceEntryEq] at previous
  rw [stepRepresentsAt] at step
  rw [sequenceEntryEq, num_succ]
  have bound := lt_num k n hk
  have unique := betaBounded_num_unique b c (S k)
  rw [num_succ] at unique
  phave entryUnique : ∀ y z, betaBounded(y, ${num b}, ${num c}, S ${num k}) →
      betaBounded(z, ${num b}, ${num c}, S ${num k}) → y = z
  · pexact unique
  · phave past : ${sequenceEntryEq p q b c n x k r}
    · pexact previous
    · phave stepValue : ∀ z, ${q}[${num x}, ${num r}, ${num k}, z] ↔ z = ${num s}
      · pexact step
      · pintro seq y hy
        papply entryUnique[y, ${num s}]
        · passumption
        · papply (exists_exists_eq_elim (fun a => betaBounded(a, ${num b}, ${num c}, ${num k}))
            (fun a v => ${q}[${num x}, a, ${num k}, v])
            (fun v => betaBounded(v, ${num b}, ${num c}, S ${num k})))[${num r}, ${num s}]
          · papply past
            passumption
          · pintro z hz
            papply stepValue[z]
            passumption
          · pcases seq with ⟨initial, steps⟩
            papply steps[${num k}]
            pexact bound

extract_witness sequenceEntryEq_zero_of_isProofOf sequenceEntryEq_succ_of_isProofOf

/-- `sequenceEntryEqProof values proofs p q b c n x base k` constructs a Q proof of
`sequenceEntryEq p q b c n x k (values k)` by primitive recursion on `k`. -/
def sequenceEntryEqProof (values proofs : Nat → Nat) (p q b c n x base : Nat) : Nat → Nat :=
  primrec (sequenceEntryEq_zero_of_isProofOf.witness p q b c n x (values 0) base)
    (fun k previous => sequenceEntryEq_succ_of_isProofOf.witness p q b c n x k (values k) (values (S
        k))
      previous (proofs k))

theorem sequenceEntryEqProof_isProofOf (values proofs : Nat → Nat) (p q b c n x base k : Nat) :
    IsProofOf language isAxiom (representsAt p x (values 0)) base → (∀ i, i < n → IsProofOf
    language isAxiom (stepRepresentsAt q x i (values i) (values (S i))) (proofs i)) → k ≤ n →
    IsProofOf language isAxiom (sequenceEntryEq p q b c n x k (values k))
    (sequenceEntryEqProof values proofs p q b c n x base k) := by
  intro hb hs
  induction k with k ih
  · intro hk
    exact sequenceEntryEq_zero_of_isProofOf.witness_correct p q b c n x (values 0) base hb
  · intro hk
    have previous := ih (le_trans k (S k) n (le_succ_self k) hk)
    exact sequenceEntryEq_succ_of_isProofOf.witness_correct p q b c n x k (values k) (values (S k))
      (sequenceEntryEqProof values proofs p q b c n x base k) (proofs k)
      hk previous (hs k hk)

/-- Checked base and step representations determine every entry of a numeral-length sequence. -/
theorem sequenceEntryEq_of_isProofOf (values proofs : Nat → Nat) (p q b c n x base k : Nat) :
    IsProofOf language isAxiom (representsAt p x (values 0)) base → (∀ i, i < n → IsProofOf
    language isAxiom (stepRepresentsAt q x i (values i) (values (S i))) (proofs i)) → k ≤ n →
    (Q ⊢ ${sequenceEntryEq p q b c n x k (values k)}) := by
  intro hb hs hk
  exact (sequenceEntryEqProof values proofs p q b c n x base k,
    sequenceEntryEqProof_isProofOf values proofs p q b c n x base k hb hs hk)

fol_theorem exists_four_eq_elim (p q : formula of 2) (r : formula of 4) : Q ⊢
    ∀ a b c d, (∀ x y, p(y, x) → x = a ∧ y = b) → (∀ x y, q(y, x) → x = c ∧ y = d) →
    (∃ x y z w, p(y, x) ∧ q(w, z) ∧ r(x, y, w, z)) → r(a, b, d, c) := by
  pintro a b c d inputUnique codeUnique witness
  pcases witness with ⟨x, witness⟩
  pcases witness with ⟨y, witness⟩
  pcases witness with ⟨z, witness⟩
  pcases witness with ⟨w, witness⟩
  pcases witness with ⟨hp, witness⟩
  pcases witness with ⟨hq, hr⟩
  phave inputEqual : x = a ∧ y = b
  · papply inputUnique[x, y]
    passumption
  · pcases inputEqual with ⟨hx, hy⟩
    phave codeEqual : z = c ∧ w = d
    · papply codeUnique[z, w]
      passumption
    · pcases codeEqual with ⟨hz, hw⟩
      phave move : r(x, y, w, z) → r(a, b, d, c)
      · psubst hx
        psubst hy
        psubst hz
        psubst hw
        pintro h
        passumption
      · papply move
        passumption

fol_theorem exists_four_intro (p q : formula of 2) (r : formula of 4) : Q ⊢
    ∀ a b c d, p(b, a) → q(d, c) → r(a, b, d, c) → ∃ x y z w, p(y, x) ∧ q(w, z) ∧
    r(x, y, w, z) := by
  pintro a b c d hp hq hr
  pexists a
  pexists b
  pexists c
  pexists d
  pconstructor
  · passumption
  · pconstructor
    · passumption
    · passumption

fol_theorem recWitness_num_elim (p q z w : Nat) : Q ⊢
    ∀ y, (recWitness ${p} ${q})(y, ${num z}, ${num w}) →
    ((betaSequence ${p} ${recStepFormula q})(${num (unpairLeft w)}, ${num (unpairRight w)},
    ${num (unpairRight z)}, ${num (unpairLeft z)}) ∧ betaBounded(y, ${num (unpairLeft w)},
    ${num (unpairRight w)}, ${num (unpairRight z)})) := by
  have inputParts := pairGraph_components_num z
  have codeParts := pairGraph_components_num w
  pintro y witness
  papply (exists_four_eq_elim (fun n x => pairGraph(${num z}, x, n))
      (fun c b => pairGraph(${num w}, b, c))
      (fun x n c b =>
      (betaSequence ${p} ${recStepFormula q})(b, c, n, x) ∧ betaBounded(y, b, c, n)))[
      ${num (unpairLeft z)}, ${num (unpairRight z)}, ${num (unpairLeft w)},
      ${num (unpairRight w)}]
  · pexact inputParts
  · pexact codeParts
  · passumption

fol_theorem recWitness_intro (p q : Nat) : Q ⊢
    ∀ y z t x n b c, pairGraph(z, x, n) → pairGraph(t, b, c) →
    (betaSequence ${p} ${recStepFormula q})(b, c, n, x) → betaBounded(y, b, c, n) →
    (recWitness ${p} ${q})(y, z, t) := by
  pintro y z t x n b c inputPair codePair sequence last
  papply (exists_four_intro (fun n x => pairGraph(z, x, n)) (fun c b => pairGraph(t, b, c))
      (fun x n c b =>
      (betaSequence ${p} ${recStepFormula q})(b, c, n, x) ∧ betaBounded(y, b, c, n)))[x, n, b, c]
  · passumption
  · passumption
  · pconstructor
    · passumption
    · passumption

theorem exists_betaBounded_of_isProofOf (q b c x i u v proof : Nat) :
    _root_.beta b c i = u → _root_.beta b c (S i) = v → IsProofOf language isAxiom
    (stepRepresentsAt q x i u v) proof →
    (Q ⊢ ${Formula.instantiate language (fol_formula[Arithmetic |
      ∃ u v, betaBounded(u, ${num b}, ${num c}, ${Term.var language 0}) ∧
        ${Formula.subst (liftSubst (shiftSubst language 1) language 4) language q}
          [${num x}, u, ${Term.var language 0}, v] ∧
        betaBounded(v, ${num b}, ${num c}, S ${Term.var language 0})]) (num i)}) := by
  intro hu hv hp
  have current := betaBounded_num b c i
  have next := betaBounded_num b c (S i)
  rw [hu] at current
  rw [hv, num_succ] at next
  have step : Q ⊢ ${stepRepresentsAt q x i u v} := (proof, hp)
  rw [stepRepresentsAt] at step
  phave stepValue : ∀ z, ${q}[${num x}, ${num u}, ${num i}, z] ↔ z = ${num v}
  · pexact step
  · papply (exists_exists_conj_intro (fun a => betaBounded(a, ${num b}, ${num c}, ${num i}))
      (fun a v => ${q}[${num x}, a, ${num i}, v])
      (fun v => betaBounded(v, ${num b}, ${num c}, S ${num i})))[${num u}, ${num v}]
    · pexact current
    · papply stepValue[${num v}]
      prefl
    · pexact next

extract_witness exists_betaBounded_of_isProofOf

/-- Construct a Q proof of the sequence from checked base and step instances and a beta code. -/
theorem betaSequence_of_isProofOf (values proofs : Nat → Nat) (p q b c n x base : Nat) :
    IsProofOf language isAxiom (representsAt p x (values 0)) base → (∀ i, i < n → IsProofOf
    language isAxiom (stepRepresentsAt q x i (values i) (values (S i))) (proofs i)) →
    (∀ i, i ≤ n → _root_.beta b c i = values i) →
    (Q ⊢ (betaSequence ${p} ${q})(${num b}, ${num c}, ${num n}, ${num x})) := by
  intro hb hs encoded
  have steps := boundedAll_of_isProofOf (fol_formula[Arithmetic |
      ∃ u v, betaBounded(u, ${num b}, ${num c}, ${Term.var language 0}) ∧
        ${Formula.subst (liftSubst (shiftSubst language 1) language 4) language q}
          [${num x}, u, ${Term.var language 0}, v] ∧
        betaBounded(v, ${num b}, ${num c}, S ${Term.var language 0})]) n
    (fun i => exists_betaBounded_of_isProofOf.witness
      q b c x i (values i) (values (S i)) (proofs i))
    (fun i hi => exists_betaBounded_of_isProofOf.witness_correct q b c x i (values i) (values (S i))
      (proofs i)
      (encoded i (le_of_lt i n hi)) (encoded (S i) hi) (hs i hi))
  rw [boundedAll] at steps
  have initial : Q ⊢ ${representsAt p x (values 0)} := (base, hb)
  rw [representsAt] at initial
  have value := betaBounded_num b c 0
  rw [encoded 0 (_root_.zero_le n)] at value
  phave initialValue : ∀ u, ${p}[${num x}, u] ↔ u = ${num (values 0)}
  · pexact initial
  · pconstructor
    · phave witness : ∃ u, u = ${num (values 0)}
      · pexists ${num (values 0)}
        prefl
      · pcases witness with ⟨u, hu⟩
        pexists u
        pconstructor
        · papply initialValue[u]
          passumption
        · psubst hu
          pexact value
    · pexact steps

fol_theorem forall_imp_of_and (p : formula) (q r s : formula of 1) : Q ⊢
    (p → ∀ y, q(y) → r(y)) → (∀ y, s(y) → p ∧ q(y)) → ∀ y, s(y) → r(y)
    := by
  pintro output decode y witness
  phave facts : p ∧ q(y)
  · papply decode[y]
    passumption
  · pcases facts with ⟨hp, hq⟩
    phave values : ∀ z, q(z) → r(z)
    · papply output
      passumption
    · papply values[y]
      passumption

theorem eq_num_of_recWitness_of_isProofOf (values proofs : Nat → Nat) (p q x n w base : Nat) :
    IsProofOf language isAxiom (representsAt p x (values 0)) base → (∀ i, i < n → IsProofOf
    language isAxiom (stepRepresentsAt (recStepFormula q) x i (values i) (values (S i))) (proofs i))
        →
    (Q ⊢ ∀ y, (recWitness ${p} ${q})(y, ${num (pair x n)}, ${num w}) → y = ${num (values
    n)}) := by
  intro hb hs
  have determined := sequenceEntryEq_of_isProofOf values proofs p (recStepFormula q)
    (unpairLeft w) (unpairRight w) n x base n hb hs (le_refl n)
  have decoded := recWitness_num_elim p q (pair x n) w
  rw [unpairLeft_pair, unpairRight_pair] at decoded
  rw [sequenceEntryEq] at determined
  papply forall_imp_of_and ((betaSequence ${p} ${recStepFormula q})(${num (unpairLeft w)},
      ${num (unpairRight w)}, ${num n}, ${num x})) (fun y =>
      betaBounded(y, ${num (unpairLeft w)}, ${num (unpairRight w)}, ${num n})) (fun y =>
      y = ${num (values n)}) (fun y => (recWitness ${p} ${q})(y, ${num (pair x n)}, ${num w}))
  · pexact determined
  · pexact decoded

fol_theorem eq_num_of_recStepGraph (q : formula of 2) (x i u v : Nat) : Q ⊢
    (∀ y, q(${num (pair x (pair i u))}, y) ↔ y = ${num v}) →
    ∀ y, (recStepGraph q)(y, ${num i}, ${num u}, ${num x}) → y = ${num v} := by
  have firstPair := pairGraph_num_iff i u
  have secondPair := pairGraph_num_iff x (pair i u)
  pintro hq y witness
  papply hq[y]
  papply (exists_exists_eq_elim (fun a => pairGraph(a, ${num i}, ${num u}))
      (fun a b => pairGraph(b, ${num x}, a))
      (fun b => q(b, y)))[${num (pair i u)}, ${num (pair x (pair i u))}]
  · pintro a ha
    papply firstPair[a]
    passumption
  · pintro b hb
    papply secondPair[b]
    passumption
  · passumption

fol_theorem recStepGraph_of_eq_num (q : formula of 2) (x i u v : Nat) : Q ⊢
    (∀ y, q(${num (pair x (pair i u))}, y) ↔ y = ${num v}) → ∀ y, y = ${num v} →
    (recStepGraph q)(y, ${num i}, ${num u}, ${num x}) := by
  have firstPair := pairGraph_num i u
  have secondPair := pairGraph_num x (pair i u)
  pintro hq y hy
  papply (exists_exists_conj_intro (fun a => pairGraph(a, ${num i}, ${num u}))
      (fun a b => pairGraph(b, ${num x}, a))
      (fun b => q(b, y)))[${num (pair i u)}, ${num (pair x (pair i u))}]
  · pexact firstPair
  · pexact secondPair
  · papply hq[y]
    passumption

fol_theorem recStepGraph_num_iff (q : formula of 2) (x i u v : Nat) : Q ⊢
    (∀ y, q(${num (pair x (pair i u))}, y) ↔ y = ${num v}) →
    ∀ y, (recStepGraph q)(y, ${num i}, ${num u}, ${num x}) ↔ y = ${num v} := by
  have forward := eq_num_of_recStepGraph q x i u v
  have backward := recStepGraph_of_eq_num q x i u v
  pintro hq
  phave hf : ∀ y, (recStepGraph q)(y, ${num i}, ${num u}, ${num x}) → y = ${num v}
  · papply forward
    passumption
  · phave hb : ∀ y, y = ${num v} → (recStepGraph q)(y, ${num i}, ${num u}, ${num x})
    · papply backward
      passumption
    · pintro y
      pconstructor
      · pexact hf[y]
      · pexact hb[y]

theorem eq_num_of_recWitness_instantiate_of_isProofOf (values proofs : Nat → Nat)
    (p q x n w base : Nat) :
    IsProofOf language isAxiom (representsAt p x (values 0)) base → (∀ i, i < n → IsProofOf
    language isAxiom (stepRepresentsAt (recStepFormula q) x i (values i) (values (S i))) (proofs i))
        →
    (Q ⊢ ${Formula.instantiate language (fol_formula[Arithmetic |
      ∀ y, (recWitness ${Formula.subst (liftSubst (shiftSubst language 1) language 2) language p}
        ${Formula.subst (liftSubst (shiftSubst language 1) language 2) language q})(y,
        ${num (pair x n)}, ${Term.var language 0}) → y = ${num (values n)}]) (num w)}) := by
  intro hb hs
  have outputInstance := eq_num_of_recWitness_of_isProofOf values proofs p q x n w base hb hs
  pexact outputInstance

extract_witness eq_num_of_recWitness_instantiate_of_isProofOf

fol_theorem forall_le_of_lt_succ (p : formula of 2) (w r : Nat) : Q ⊢
    (∀ t, t < S ${num w} → ∀ y, p(t, y) → y = ${num r}) → ∀ t y, t ≤ ${num w} → p(t, y) → y =
    ${num r} := by
  pintro bounded t y ht witness
  phave output : ∀ z, p(t, z) → z = ${num r}
  · papply bounded[t]
    papply lt_succ_iff_le[t, ${num w}]
    passumption
  · papply output[y]
    passumption

theorem eq_num_of_recWitness_of_le_of_isProofOf (values proofs : Nat → Nat) (p q x n w base : Nat) :
    IsProofOf language isAxiom (representsAt p x (values 0)) base → (∀ i, i < n → IsProofOf
    language isAxiom (stepRepresentsAt (recStepFormula q) x i (values i) (values (S i))) (proofs i))
        →
    (Q ⊢ ∀ t y, t ≤ ${num w} → (recWitness ${p} ${q})(y, ${num (pair x n)}, t) → y =
    ${num (values n)}) := by
  intro hb hs
  have all := boundedAll_of_isProofOf
    (fol_formula[Arithmetic |
      ∀ y, (recWitness ${Formula.subst (liftSubst (shiftSubst language 1) language 2) language p}
        ${Formula.subst (liftSubst (shiftSubst language 1) language 2) language q})(y,
        ${num (pair x n)}, ${Term.var language 0}) → y = ${num (values n)}]) (S w)
    (fun t => eq_num_of_recWitness_instantiate_of_isProofOf.witness values proofs p q x n t base)
    (fun t ht => eq_num_of_recWitness_instantiate_of_isProofOf.witness_correct
      values proofs p q x n t base hb hs)
  rw [boundedAll, num_succ] at all
  let graph := recWitness (FOL.Formula.subst (FOL.liftSubst (FOL.shiftSubst language 2)
      language 2) language p) (FOL.Formula.subst (FOL.liftSubst
      (FOL.shiftSubst language 2) language 2) language q) (Term.var
      language 0) (num (pair x n)) (Term.var language 1)
  papply forall_le_of_lt_succ ${graph} w (values n)
  pexact all

theorem recWitness_of_isProofOf (values proofs : Nat → Nat) (p q b c x n base : Nat) :
    IsProofOf language isAxiom (representsAt p x (values 0)) base → (∀ i, i < n → IsProofOf
    language isAxiom (stepRepresentsAt (recStepFormula q) x i (values i) (values (S i))) (proofs i))
        →
    (∀ i, i ≤ n → _root_.beta b c i = values i) →
    (Q ⊢ (recWitness ${p} ${q})(${num (values n)}, ${num (pair x n)}, ${num (pair b c)})) := by
  intro hb hs encoded
  have sequence := betaSequence_of_isProofOf values proofs p (recStepFormula q) b c n x base
    hb hs encoded
  have last := betaBounded_num b c n
  rw [encoded n (le_refl n)] at last
  have introduction := recWitness_intro p q
  papply introduction[${num (values n)}, ${num (pair x n)},
    ${num (pair b c)}, ${num x}, ${num n}, ${num b}, ${num c}]
  · pexact pairGraph_num x n
  · pexact pairGraph_num b c
  · pexact sequence
  · pexact last

/-- At a numeral input, Q determines the last value of the recursive sequence from
checked numeral-instance proofs for its base and steps. -/
theorem leastRecursionGraph_num_iff_of_isProofOf (values proofs : Nat → Nat) (p q x n base : Nat) :
    IsProofOf language isAxiom (representsAt p x (values 0)) base → (∀ i, i < n → IsProofOf
    language isAxiom (stepRepresentsAt (recStepFormula q) x i (values i) (values (S i))) (proofs i))
        →
    (Q ⊢ ∀ y, (leastRecursionGraph ${p} ${q})(y, ${num (pair x n)}) ↔ y =
    ${num (values n)}) := by
  intro hb hs
  rcases beta_exists values (S n) with (b, c, entries)
  have encoded : ∀ i, i ≤ n → _root_.beta b c i = values i := by
    intro i hi
    exact entries i (and_right (lt_succ i n) hi)
  have actual := recWitness_of_isProofOf values proofs p q b c x n base hb hs encoded
  have bounded := eq_num_of_recWitness_of_le_of_isProofOf values proofs p q x n (pair b c) base hb
      hs
  have selected := minGraph_num_iff_of_le (recWitnessFormula p q)
    (pair x n) (values n) (pair b c)
  rw [recWitnessFormula] at selected
  rw [leastRecursionGraph]
  papply selected
  · pexact actual
  · pexact bounded

end Q

extract_witness FOL.PA.exists_four_project FOL.PA.exists_exists_mono FOL.PA.pairGraph_exists_unique
  FOL.PA.betaRecursionGraph_total FOL.PA.betaRecursionGraph_unique FOL.PA.leastRecursionGraph_total
  FOL.PA.leastRecursionGraph_unique FOL.PA.recStepGraph_total FOL.PA.recStepGraph_unique
  FOL.PA.recWitness_betaRecursionGraph FOL.PA.recWitness_total FOL.PA.recWitness_unique
  FOL.PA.recWitness_unique_of_betaRecursionGraph_unique FOL.PA.recursionGraph_succ_elim
  FOL.PA.recursionGraph_succ_intro FOL.PA.recursionGraph_total FOL.PA.recursionGraph_unique
  FOL.PA.recursionGraph_zero_elim FOL.PA.recursionGraph_zero_intro FOL.PA.recursionSequence_succ
  FOL.PA.exists_recursionSequence_succ FOL.PA.recursionSequence_mono
  FOL.PA.recursionSequence_of_succ FOL.PA.recursionSteps_succ FOL.PA.recursionSteps_mono
  FOL.PA.recursion_total FOL.PA.recursion_unique FOL.PA.unique_of_forall_imp FOL.Q.exists_four_intro
  FOL.Q.forall_le_of_lt_succ FOL.Q.recStepGraph_num_iff FOL.Q.recStepGraph_of_eq_num
  FOL.Q.eq_num_of_recStepGraph FOL.Q.recWitness_intro

end

end FOL
