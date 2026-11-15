module

public import LeanPRA.Library.FOL.Common.Proof.Equality

/-!
# Congruence under substitution

The numerical proof construction works for every language code and theory membership function.
It traverses term and formula codes, including arbitrary symbol arities and nested quantifiers.

- `FOL.Equality.substitution_congruence` substitutes equal terms at free position zero and
  lowers later free positions by one.
- `FOL.Equality.replace` changes position zero and leaves later free positions unchanged.
-/

pra

namespace FOL.Equality

/-- Store two syntax codes and the code of their equality or equivalence proof. -/
def pack : Nat → Nat → Nat → Nat := fun a b p => pair a (pair b p)

def lhs : Nat → Nat := unpairLeft

def rhs : Nat → Nat := fun r => unpairLeft (unpairRight r)

def proof : Nat → Nat := fun r => unpairRight (unpairRight r)

theorem lhs_pack : ∀ a b p, lhs (pack a b p) = a := by
  intro a b p
  rw [lhs, pack, unpairLeft_pair]

theorem rhs_pack : ∀ a b p, rhs (pack a b p) = b := by
  intro a b p
  rw [rhs, pack, unpairRight_pair, unpairLeft_pair]

theorem proof_pack : ∀ a b p, proof (pack a b p) = p := by
  intro a b p
  rw [proof, pack, unpairRight_pair, unpairRight_pair]

/-- The record stores syntax codes `a` and `b` and a proof of `e → rel a b` in theory `T`. -/
def Record (L : Nat) (T : Nat → Nat) (rel : Nat → Nat → Nat) :
    Nat → Nat → Nat → Nat → QFProp := fun e a b r =>
  lhs r = a ∧ rhs r = b ∧
    FOL.IsProofOf L T (FOL.Formula.imp e (rel a b)) (proof r)

/-- A Boolean test of the record invariant, used in numerical induction. -/
def recordTest (L : Nat) (T : Nat → Nat) (rel : Nat → Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat := fun e a b r =>
  band (eqb (lhs r) a) (band (eqb (rhs r) b)
    (band (FOL.isProof L T (proof r))
      (eqb (FOL.Proof.conclusion (proof r)) (FOL.Formula.imp e (rel a b)))))

theorem recordTest_iff (L : Nat) (T : Nat → Nat) (rel : Nat → Nat → Nat) : ∀ e a b r,
    recordTest L T rel e a b r = 1 ↔ Record L T rel e a b r := by
  intro e a b r
  constructor
  · intro h
    have h1 := and_left (band_eq_one_of_bool _ _ (eqb_bool _ _) (band_bool _ _)) h
    have h2 := and_left (band_eq_one_of_bool _ _ (eqb_bool _ _) (band_bool _ _)) (and_right h1)
    have h3 := and_left (band_eq_one_of_bool _ _ (FOL.isProof_bool _ _ _) (eqb_bool _ _))
      (and_right h2)
    exact (and_left (eqb_eq_one _ _) (and_left h1),
      and_left (eqb_eq_one _ _) (and_left h2), and_left h3,
      and_left (eqb_eq_one _ _) (and_right h3))
  · intro h
    exact band_eq_one_of_eq_one _ _
      (and_right (eqb_eq_one _ _) (and_left h))
      (band_eq_one_of_eq_one _ _ (and_right (eqb_eq_one _ _) (and_left (and_right h)))
        (band_eq_one_of_eq_one _ _ (and_left (and_right (and_right h)))
          (and_right (eqb_eq_one _ _) (and_right (and_right (and_right h))))))

theorem record_pack (L : Nat) (T : Nat → Nat) (rel : Nat → Nat → Nat) : ∀ e a b p,
    FOL.IsProofOf L T (FOL.Formula.imp e (rel a b)) p →
      Record L T rel e a b (pack a b p) := by
  intro e a b p h
  rw [Record, lhs_pack, rhs_pack, proof_pack]
  exact (rfl, rfl, h)

def combineRecord (L : Nat) (T : Nat → Nat) (f : Nat → Nat → Nat)
    (code : Nat → Nat → Nat → Nat → Nat → Nat) :
    Nat → Nat → Nat → Nat := fun e r q =>
  pack (f (lhs r) (lhs q)) (f (rhs r) (rhs q))
    (FOL.Proof.mp' L
      (FOL.Proof.mp' L
        (code e (lhs r) (lhs q) (rhs r) (rhs q)) (proof r)) (proof q))

theorem combineRecord_valid (L : Nat) (T : Nat → Nat) (f src dst : Nat → Nat → Nat)
    (code : Nat → Nat → Nat → Nat → Nat → Nat) :
    (∀ e a b c d, FOL.IsProofOf L T
      (FOL.Formula.imp (FOL.Formula.imp e (src a c))
        (FOL.Formula.imp (FOL.Formula.imp e (src b d))
          (FOL.Formula.imp e (dst (f a b) (f c d))))) (code e a b c d)) →
    ∀ e a b c d r q, Record L T src e a c r → Record L T src e b d q →
      Record L T dst e (f a b) (f c d) (combineRecord L T f code e r q) := by
  intro hc e a b c d r q hr hq
  rw [combineRecord, and_left hr, and_left (and_right hr),
    and_left hq, and_left (and_right hq)]
  apply record_pack L T dst
  have h1 := FOL.IsProofOf.mp' L T
    (FOL.Formula.imp e (src a c))
    (FOL.Formula.imp (FOL.Formula.imp e (src b d))
      (FOL.Formula.imp e (dst (f a b) (f c d))))
    (code e a b c d) (proof r) (hc e a b c d) (and_right (and_right hr))
  exact FOL.IsProofOf.mp' L T
    (FOL.Formula.imp e (src b d)) (FOL.Formula.imp e (dst (f a b) (f c d)))
    (FOL.Proof.mp' L (code e a b c d) (proof r)) (proof q)
    h1 (and_right (and_right hq))

def equation (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat := FOL.Formula.equal L

def antecedent (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat → Nat := fun s t d =>
  equation L T (FOL.Term.shift L d s) (FOL.Term.shift L d t)

def reflexiveRecord (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat := fun e t =>
  pack t t (FOL.Provable.equal_refl_under.witness L T e t)

theorem reflexiveRecord_valid (L : Nat) (T : Nat → Nat) : ∀ e t,
    Record L T (equation L T) e t t (reflexiveRecord L T e t) := by
  intro e t
  exact record_pack L T (equation L T) e t t (FOL.Provable.equal_refl_under.witness L T e t)
    (FOL.Provable.equal_refl_under.witness_correct L T e t)

def variableRecord (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat → Nat → Nat := fun s t d i =>
  let e := antecedent L T s t d;
  ite (ltb i d) (reflexiveRecord L T e (FOL.Term.var L i))
    (ite (eqb (i - d) 0)
      (pack (FOL.Term.shift L d s) (FOL.Term.shift L d t)
        (FOL.Provable.imp_refl.witness L T e))
      (reflexiveRecord L T e (FOL.Term.var L (ite (ltb 0 (i - d)) (pred i) i))))

theorem variableRecord_valid (L : Nat) (T : Nat → Nat) : ∀ s t d i,
    Record L T (equation L T) (antecedent L T s t d)
    (FOL.Term.instantiateAt L 0 s d i)
    (FOL.Term.instantiateAt L 0 t d i) (variableRecord L T s t d i) := by
  intro s t d i
  by_cases h : ltb i d = 0
  · rw [variableRecord]
    repeat first
      | rw [FOL.Term.instantiateAt]
      | rw [h]
      | rw [ite_zero]
    by_cases hi : eqb (i - d) 0 = 0
    · repeat first
        | rw [hi]
        | rw [ite_zero]
      exact reflexiveRecord_valid L T _ _
    · repeat rw [ite_of_ne_zero (eqb (i - d) 0) _ _ hi]
      exact record_pack L T (equation L T) _ _ _ _
        (FOL.Provable.imp_refl.witness_correct L T (antecedent L T s t d))
  · rw [variableRecord]
    repeat first
      | rw [FOL.Term.instantiateAt]
      | rw [ite_of_ne_zero (ltb i d) _ _ h]
    exact reflexiveRecord_valid L T _ _

def premisePrefix (L : Nat) : Nat → Nat → Nat → Nat → Nat → Nat := fun n xs ys C =>
  primrec C (fun i B => FOL.Formula.imp
    (FOL.Formula.equal L (Tuple.get n xs (n - S i)) (Tuple.get n ys (n - S i))) B)

def dischargePremises (L : Nat) (T : Nat → Nat) (f : Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat := fun e n xs ys C =>
  primrec (FOL.Provable.imp_refl.witness L T (FOL.Formula.imp e C)) (fun i p =>
    FOL.Proof.mp' L
      (FOL.Proof.mp' L
        (FOL.Provable.imp_mp_trans_under.witness L T e
          (FOL.Formula.equal L (Tuple.get n xs (n - S i)) (Tuple.get n ys (n - S i)))
          (premisePrefix L n xs ys C i) C) p) (f (n - S i)))

theorem dischargePremises_valid (L : Nat) (T : Nat → Nat) (f : Nat → Nat) :
    ∀ e n xs ys C, ¬ n = 0 →
    (∀ i, i < n → FOL.IsProofOf L T
      (FOL.Formula.imp e (FOL.Formula.equal L (Tuple.get n xs i) (Tuple.get n ys i))) (f i)) →
    ∀ k, FOL.IsProofOf L T
      (FOL.Formula.imp (FOL.Formula.imp e (premisePrefix L n xs ys C k)) (FOL.Formula.imp e C))
      (dischargePremises L T f e n xs ys C k) := by
  intro e n xs ys C hn entries k
  induction k with i ih
  · exact FOL.Provable.imp_refl.witness_correct L T (FOL.Formula.imp e C)
  · let a := FOL.Formula.equal L (Tuple.get n xs (n - S i)) (Tuple.get n ys (n - S i))
    let b := premisePrefix L n xs ys C i
    have hi := sub_lt_of_pos n (S i) (pos_of_ne_zero n hn)
      (pos_of_ne_zero (S i) (succ_ne_zero i))
    have hp := FOL.Provable.imp_mp_trans_under.witness_correct L T e a b C
    have hq := FOL.IsProofOf.mp' L T
      (FOL.Formula.imp (FOL.Formula.imp e b) (FOL.Formula.imp e C))
      (FOL.Formula.imp (FOL.Formula.imp e a)
        (FOL.Formula.imp (FOL.Formula.imp e (FOL.Formula.imp a b)) (FOL.Formula.imp e C)))
      (FOL.Provable.imp_mp_trans_under.witness L T e a b C)
      (dischargePremises L T f e n xs ys C i) hp ih
    exact FOL.IsProofOf.mp' L T (FOL.Formula.imp e a)
      (FOL.Formula.imp (FOL.Formula.imp e (FOL.Formula.imp a b)) (FOL.Formula.imp e C))
      (FOL.Proof.mp' L (FOL.Provable.imp_mp_trans_under.witness L T e a b C)
        (dischargePremises L T f e n xs ys C i)) (f (n - S i)) hq (entries (n - S i) hi)

def congruenceProof (L : Nat) (T : Nat → Nat) (f : Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat := fun e n xs ys C =>
  FOL.Proof.mp' L (dischargePremises L T f e n xs ys C n)
    (FOL.Proof.mp' L
      (FOL.Provable.implication.witness L T (FOL.Formula.equalPremises L n xs ys C) e)
      (FOL.Proof.axiom (FOL.Formula.equalPremises L n xs ys C)))

theorem congruenceProof_valid (L : Nat) (T : Nat → Nat) (f : Nat → Nat) :
    ∀ e n xs ys C, ¬ n = 0 →
    FOL.isLogicalAxiom L (FOL.Formula.equalPremises L n xs ys C) = 1 →
    (∀ i, i < n → FOL.IsProofOf L T
      (FOL.Formula.imp e (FOL.Formula.equal L (Tuple.get n xs i) (Tuple.get n ys i))) (f i)) →
    FOL.IsProofOf L T (FOL.Formula.imp e C) (congruenceProof L T f e n xs ys C) := by
  intro e n xs ys C hn ha entries
  let A := FOL.Formula.equalPremises L n xs ys C
  have ax : FOL.IsProofOf L T A (FOL.Proof.axiom A) :=
    (FOL.isProof_axiom L T A ha, FOL.Proof.conclusion_axiom A)
  have lifted := FOL.IsProofOf.mp' L T A (FOL.Formula.imp e A)
    (FOL.Provable.implication.witness L T A e) (FOL.Proof.axiom A)
    (FOL.Provable.implication.witness_correct L T A e) ax
  exact FOL.IsProofOf.mp' L T (FOL.Formula.imp e A) (FOL.Formula.imp e C)
    (dischargePremises L T f e n xs ys C n)
    (FOL.Proof.mp' L (FOL.Provable.implication.witness L T A e) (FOL.Proof.axiom A))
    (dischargePremises_valid L T f e n xs ys C hn entries n) lifted

def functionRecord (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat → Nat := fun e j rs =>
  let n := FOL.Language.functionArity L j;
  let xs := Tuple.map lhs n rs;
  let ys := Tuple.map rhs n rs;
  pack (FOL.Term.app L j xs) (FOL.Term.app L j ys)
    (congruenceProof L T (fun i => proof (Tuple.get n rs i)) e n xs ys
      (FOL.Formula.equal L (FOL.Term.app L j xs) (FOL.Term.app L j ys)))

theorem functionRecord_valid (L : Nat) (T : Nat → Nat) : ∀ e j rs,
    j < FOL.Language.functionCount L →
    (∀ i, i < FOL.Language.functionArity L j →
      FOL.IsProofOf L T (FOL.Formula.imp e
        (equation L T (lhs (Tuple.get (FOL.Language.functionArity L j) rs i))
          (rhs (Tuple.get (FOL.Language.functionArity L j) rs i))))
        (proof (Tuple.get (FOL.Language.functionArity L j) rs i))) →
    Record L T (equation L T) e
      (FOL.Term.app L j (Tuple.map lhs (FOL.Language.functionArity L j) rs))
      (FOL.Term.app L j (Tuple.map rhs (FOL.Language.functionArity L j) rs))
      (functionRecord L T e j rs) := by
  intro e j rs hj entries
  apply record_pack L T (equation L T)
  apply congruenceProof_valid L T (fun i => proof (Tuple.get (FOL.Language.functionArity L j) rs i))
  · exact succ_ne_zero _
  · exact FOL.isLogicalAxiom_of_functionCongruence L j _ _ hj
  · intro i hi
    rw [Tuple.get_map lhs _ _ i hi, Tuple.get_map rhs _ _ i hi]
    exact entries i hi

/-- Traverse a term at binder depth `d`, substituting `s` and `t` in parallel. -/
def termRecord (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat → Nat → Nat := fun s t d =>
  FOL.Term.rec (variableRecord L T s t d)
    (fun j => reflexiveRecord L T (antecedent L T s t d) (FOL.Term.const L j))
    (functionRecord L T (antecedent L T s t d)) L

theorem termRecord_const (L : Nat) (T : Nat → Nat) : ∀ s t d j,
    j < FOL.Language.constants L → termRecord L T s t d (FOL.Term.const L j) =
      reflexiveRecord L T (antecedent L T s t d) (FOL.Term.const L j) := by
  intro s t d j hj
  exact FOL.Term.rec_const (variableRecord L T s t d)
    (fun j => reflexiveRecord L T (antecedent L T s t d) (FOL.Term.const L j))
    (functionRecord L T (antecedent L T s t d)) L j hj

theorem termRecord_var (L : Nat) (T : Nat → Nat) : ∀ s t d i,
    termRecord L T s t d (FOL.Term.var L i) = variableRecord L T s t d i := by
  intro s t d i
  exact FOL.Term.rec_var (variableRecord L T s t d)
    (fun j => reflexiveRecord L T (antecedent L T s t d) (FOL.Term.const L j))
    (functionRecord L T (antecedent L T s t d)) L i

theorem termRecord_app (L : Nat) (T : Nat → Nat) : ∀ s t d j xs,
    j < FOL.Language.functionCount L → termRecord L T s t d (FOL.Term.app L j xs) =
      functionRecord L T (antecedent L T s t d) j
        (Tuple.map (termRecord L T s t d) (FOL.Language.functionArity L j) xs) := by
  intro s t d j xs hj
  exact FOL.Term.rec_app (variableRecord L T s t d)
    (fun j => reflexiveRecord L T (antecedent L T s t d) (FOL.Term.const L j))
    (functionRecord L T (antecedent L T s t d)) L j xs hj

/-- Mapping record projections preserves componentwise equations. -/
theorem map_records (get record value : Nat → Nat) : ∀ n xs,
    (∀ i, i < n → get (record (Tuple.get n xs i)) = value (Tuple.get n xs i)) →
    Tuple.map get n (Tuple.map record n xs) = Tuple.map value n xs := by
  intro n xs entries
  rw [Tuple.map_map get record]
  exact Tuple.map_congr_of_get_eq (fun x => get (record x)) value n xs entries

def termTest (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat → Nat → Nat := fun s t d a =>
  recordTest L T (equation L T) (antecedent L T s t d)
    (FOL.Term.subst (FOL.Term.instantiateAt L 0 s d) L a)
    (FOL.Term.subst (FOL.Term.instantiateAt L 0 t d) L a) (termRecord L T s t d a)

theorem termTest_eq (L : Nat) (T : Nat → Nat) : ∀ s t d a, termTest L T s t d a =
    recordTest L T (equation L T) (antecedent L T s t d)
      (FOL.Term.subst (FOL.Term.instantiateAt L 0 s d) L a)
      (FOL.Term.subst (FOL.Term.instantiateAt L 0 t d) L a) (termRecord L T s t d a) :=
  fun s t d a => rfl

theorem termRecord_valid (L : Nat) (T : Nat → Nat) (s t d : Nat) : ∀ a,
    Record L T (equation L T) (antecedent L T s t d)
      (FOL.Term.subst (FOL.Term.instantiateAt L 0 s d) L a)
      (FOL.Term.subst (FOL.Term.instantiateAt L 0 t d) L a) (termRecord L T s t d a) := by
  have good : ∀ a, termTest L T s t d a = 1 := by
    apply FOL.Term.induction_eq (termTest L T s t d) (fun _ => 1) L
    · intro j hj
      rw [termTest_eq L T]
      apply and_right (recordTest_iff L T (equation L T) _ _ _ _)
      rw [termRecord_const L T s t d j hj,
        FOL.Term.subst_const (FOL.Term.instantiateAt L 0 s d) L j hj,
        FOL.Term.subst_const (FOL.Term.instantiateAt L 0 t d) L j hj]
      exact reflexiveRecord_valid L T _ _
    · intro i
      rw [termTest_eq L T]
      apply and_right (recordTest_iff L T (equation L T) _ _ _ _)
      rw [termRecord_var L T,
        FOL.Term.subst_var (FOL.Term.instantiateAt L 0 s d),
        FOL.Term.subst_var (FOL.Term.instantiateAt L 0 t d)]
      exact variableRecord_valid L T s t d i
    · intro j xs hj ih
      let n := FOL.Language.functionArity L j
      have entries : ∀ i, i < n → Record L T (equation L T) (antecedent L T s t d)
          (FOL.Term.subst (FOL.Term.instantiateAt L 0 s d) L (Tuple.get n xs i))
          (FOL.Term.subst (FOL.Term.instantiateAt L 0 t d) L (Tuple.get n xs i))
          (termRecord L T s t d (Tuple.get n xs i)) := by
        intro i hi
        have h := ih i hi
        rw [termTest_eq L T] at h
        exact and_left (recordTest_iff L T (equation L T) _ _ _ _) h
      have h := functionRecord_valid L T (antecedent L T s t d) j
        (Tuple.map (termRecord L T s t d) n xs) hj (by
          intro i hi
          rw [Tuple.get_map (termRecord L T s t d) n xs i hi]
          have h := entries i hi
          rw [and_left h, and_left (and_right h)]
          exact and_right (and_right h))
      have hl := map_records lhs (termRecord L T s t d)
        (FOL.Term.subst (FOL.Term.instantiateAt L 0 s d) L) n xs
        (fun i hi => and_left (entries i hi))
      have hr := map_records rhs (termRecord L T s t d)
        (FOL.Term.subst (FOL.Term.instantiateAt L 0 t d) L) n xs
        (fun i hi => and_left (and_right (entries i hi)))
      rw [hl, hr] at h
      rw [termTest_eq L T]
      apply and_right (recordTest_iff L T (equation L T) _ _ _ _)
      rw [termRecord_app L T s t d j xs hj,
        FOL.Term.subst_app (FOL.Term.instantiateAt L 0 s d) L j xs hj,
        FOL.Term.subst_app (FOL.Term.instantiateAt L 0 t d) L j xs hj]
      exact h
  intro a
  have h := good a
  rw [termTest_eq L T] at h
  exact and_left (recordTest_iff L T (equation L T) _ _ _ _) h

def equivalenceFormula : Nat → Nat → Nat := fun a b =>
  FOL.Formula.conj (FOL.Formula.imp a b) (FOL.Formula.imp b a)

def falsumRecord (L : Nat) (T : Nat → Nat) : Nat → Nat := fun e =>
  pack FOL.Formula.falsum FOL.Formula.falsum
    (FOL.Provable.iff_refl_under.witness L T e FOL.Formula.falsum)

theorem falsumRecord_valid (L : Nat) (T : Nat → Nat) : ∀ e,
    Record L T equivalenceFormula e FOL.Formula.falsum FOL.Formula.falsum (falsumRecord L T e) := by
  intro e
  exact record_pack L T equivalenceFormula _ _ _ _
    (FOL.Provable.iff_refl_under.witness_correct L T e _)

def equalityRecord (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat → Nat :=
  combineRecord L T (equation L T)
    (fun e a b c d => FOL.Provable.equal_congr_under.witness L T e a b c d)

theorem equalityRecord_valid (L : Nat) (T : Nat → Nat) : ∀ e a b c d r q,
    Record L T (equation L T) e a c r → Record L T (equation L T) e b d q →
      Record L T equivalenceFormula e (equation L T a b) (equation L T c d)
        (equalityRecord L T e r q) :=
  combineRecord_valid L T (equation L T) (equation L T) equivalenceFormula
    (fun e a b c d => FOL.Provable.equal_congr_under.witness L T e a b c d)
    (fun e a b c d => FOL.Provable.equal_congr_under.witness_correct L T e a b c d)

def implicationRecord (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat → Nat :=
  combineRecord L T FOL.Formula.imp
    (fun e a b c d => FOL.Provable.imp_congr_under.witness L T e a b c d)

theorem implicationRecord_valid (L : Nat) (T : Nat → Nat) : ∀ e a b c d r q,
    Record L T equivalenceFormula e a c r → Record L T equivalenceFormula e b d q →
      Record L T equivalenceFormula e (FOL.Formula.imp a b) (FOL.Formula.imp c d)
        (implicationRecord L T e r q) :=
  combineRecord_valid L T FOL.Formula.imp equivalenceFormula equivalenceFormula
    (fun e a b c d => FOL.Provable.imp_congr_under.witness L T e a b c d)
    (fun e a b c d => FOL.Provable.imp_congr_under.witness_correct L T e a b c d)

theorem antecedent_shift (L : Nat) (T : Nat → Nat) : ∀ s t d,
    FOL.Formula.subst (FOL.shiftSubst L 1) L
      (antecedent L T s t d) = antecedent L T s t (S d) := by
  intro s t d
  rw [antecedent, antecedent, equation, equation,
    FOL.Formula.subst_equal (FOL.shiftSubst L 1),
    ← FOL.Term.shift_eq_subst_shiftSubst, ← FOL.Term.shift_eq_subst_shiftSubst,
    FOL.Term.shift_shift, FOL.Term.shift_shift, add_one]

def universalRecord (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat := fun e r =>
  pack (FOL.Formula.all (lhs r)) (FOL.Formula.all (rhs r))
    (FOL.Proof.mp' L (FOL.Provable.all_congr_under.witness L T e (lhs r) (rhs r))
      (FOL.Proof.gen (FOL.Proof.conclusion (proof r)) (proof r)))

theorem universalRecord_valid (L : Nat) (T : Nat → Nat) : ∀ s t d a b r,
    Record L T equivalenceFormula (antecedent L T s t (S d)) a b r →
      Record L T equivalenceFormula (antecedent L T s t d) (FOL.Formula.all a) (FOL.Formula.all b)
        (universalRecord L T (antecedent L T s t d) r) := by
  intro s t d a b r h
  have checked := and_right (and_right h)
  rw [universalRecord, and_left h, and_left (and_right h), and_right checked]
  apply record_pack L T equivalenceFormula
  have implication := FOL.Provable.all_congr_under.witness_correct L T (antecedent L T s t d) a b
  rw [antecedent_shift L T] at implication
  exact FOL.IsProofOf.mp' L T
    (FOL.Formula.all (FOL.Formula.imp (antecedent L T s t (S d)) (equivalenceFormula a b)))
    (FOL.Formula.imp (antecedent L T s t d)
      (equivalenceFormula (FOL.Formula.all a) (FOL.Formula.all b)))
    (FOL.Provable.all_congr_under.witness L T (antecedent L T s t d) a b)
    (FOL.Proof.gen (FOL.Formula.imp (antecedent L T s t (S d)) (equivalenceFormula a b)) (proof r))
    implication (FOL.IsProofOf.gen L T _ _ checked)

def reverseEquation (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat := fun e r =>
  FOL.Proof.mp' L (FOL.Provable.equal_symm_under.witness L T e (lhs r) (rhs r)) (proof r)

theorem reverseEquation_valid (L : Nat) (T : Nat → Nat) : ∀ e r,
    FOL.IsProofOf L T (FOL.Formula.imp e (equation L T (lhs r) (rhs r))) (proof r) →
    FOL.IsProofOf L T (FOL.Formula.imp e (equation L T (rhs r) (lhs r)))
      (reverseEquation L T e r) := by
  intro e r h
  exact FOL.IsProofOf.mp' L T
    (FOL.Formula.imp e (equation L T (lhs r) (rhs r)))
    (FOL.Formula.imp e (equation L T (rhs r) (lhs r)))
    (FOL.Provable.equal_symm_under.witness L T e (lhs r) (rhs r)) (proof r)
    (FOL.Provable.equal_symm_under.witness_correct L T e (lhs r) (rhs r)) h

def relationRecord (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat → Nat := fun e j rs =>
  let n := FOL.Language.relationArity L j;
  let xs := Tuple.map lhs n rs;
  let ys := Tuple.map rhs n rs;
  let a := FOL.Formula.rel L j xs;
  let b := FOL.Formula.rel L j ys;
  pack a b (FOL.Proof.mp' L
    (FOL.Proof.mp' L (FOL.Provable.iff_intro_under.witness L T e a b)
      (congruenceProof L T (fun i => proof (Tuple.get n rs i)) e n xs ys
        (FOL.Formula.imp a b)))
    (congruenceProof L T (fun i => reverseEquation L T e (Tuple.get n rs i)) e n ys xs
      (FOL.Formula.imp b a)))

theorem relationRecord_valid (L : Nat) (T : Nat → Nat) : ∀ e j rs,
    j < FOL.Language.relationCount L →
    (∀ i, i < FOL.Language.relationArity L j →
      FOL.IsProofOf L T (FOL.Formula.imp e
        (equation L T (lhs (Tuple.get (FOL.Language.relationArity L j) rs i))
          (rhs (Tuple.get (FOL.Language.relationArity L j) rs i))))
        (proof (Tuple.get (FOL.Language.relationArity L j) rs i))) →
    Record L T equivalenceFormula e
      (FOL.Formula.rel L j (Tuple.map lhs (FOL.Language.relationArity L j) rs))
      (FOL.Formula.rel L j (Tuple.map rhs (FOL.Language.relationArity L j) rs))
      (relationRecord L T e j rs) := by
  intro e j rs hj entries
  let n := FOL.Language.relationArity L j
  let xs := Tuple.map lhs n rs
  let ys := Tuple.map rhs n rs
  let a := FOL.Formula.rel L j xs
  let b := FOL.Formula.rel L j ys
  have forward := congruenceProof_valid L T (fun i => proof (Tuple.get n rs i))
    e n xs ys (FOL.Formula.imp a b) (succ_ne_zero _)
    (FOL.isLogicalAxiom_of_relationCongruence L j xs ys hj) (by
      intro i hi
      rw [Tuple.get_map lhs n rs i hi, Tuple.get_map rhs n rs i hi]
      exact entries i hi)
  have backward := congruenceProof_valid L T
    (fun i => reverseEquation L T e (Tuple.get n rs i))
    e n ys xs (FOL.Formula.imp b a) (succ_ne_zero _)
    (FOL.isLogicalAxiom_of_relationCongruence L j ys xs hj) (by
      intro i hi
      rw [Tuple.get_map rhs n rs i hi, Tuple.get_map lhs n rs i hi]
      exact reverseEquation_valid L T e (Tuple.get n rs i) (entries i hi))
  apply record_pack L T equivalenceFormula
  have h := FOL.IsProofOf.mp' L T (FOL.Formula.imp e (FOL.Formula.imp a b))
    (FOL.Formula.imp (FOL.Formula.imp e (FOL.Formula.imp b a))
      (FOL.Formula.imp e (equivalenceFormula a b)))
    (FOL.Provable.iff_intro_under.witness L T e a b)
    (congruenceProof L T (fun i => proof (Tuple.get n rs i)) e n xs ys (FOL.Formula.imp a b))
    (FOL.Provable.iff_intro_under.witness_correct L T e a b) forward
  exact FOL.IsProofOf.mp' L T (FOL.Formula.imp e (FOL.Formula.imp b a))
    (FOL.Formula.imp e (equivalenceFormula a b))
    (FOL.Proof.mp' L (FOL.Provable.iff_intro_under.witness L T e a b)
      (congruenceProof L T (fun i => proof (Tuple.get n rs i)) e n xs ys (FOL.Formula.imp a b)))
    (congruenceProof L T (fun i => reverseEquation L T e (Tuple.get n rs i))
      e n ys xs (FOL.Formula.imp b a)) h backward

/-- Traverse a formula while increasing the substitution depth beneath each quantifier. -/
def formulaRecord (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat → Nat → Nat := fun s t =>
  FOL.Formula.recWithDepth (fun d => falsumRecord L T (antecedent L T s t d))
    (fun d a b => equalityRecord L T (antecedent L T s t d)
      (termRecord L T s t d a) (termRecord L T s t d b))
    (fun d j xs => relationRecord L T (antecedent L T s t d) j
      (Tuple.map (termRecord L T s t d) (FOL.Language.relationArity L j) xs))
    (fun d a b => implicationRecord L T (antecedent L T s t d) a b)
    (fun d a => universalRecord L T (antecedent L T s t d) a) L

theorem formulaRecord_eq (L : Nat) (T : Nat → Nat) : ∀ s t A d, formulaRecord L T s t A d =
    FOL.Formula.recWithDepth (fun d => falsumRecord L T (antecedent L T s t d))
      (fun d a b => equalityRecord L T (antecedent L T s t d)
        (termRecord L T s t d a) (termRecord L T s t d b))
      (fun d j xs => relationRecord L T (antecedent L T s t d) j
        (Tuple.map (termRecord L T s t d) (FOL.Language.relationArity L j) xs))
      (fun d a b => implicationRecord L T (antecedent L T s t d) a b)
      (fun d a => universalRecord L T (antecedent L T s t d) a) L A d :=
  fun s t A d => rfl

theorem formulaRecord_falsum (L : Nat) (T : Nat → Nat) : ∀ s t d,
    formulaRecord L T s t FOL.Formula.falsum d = falsumRecord L T (antecedent L T s t d) := by
  intro s t d
  rw [formulaRecord_eq L T, FOL.Formula.recWithDepth_falsum _ _ _ _ _]

theorem formulaRecord_equal (L : Nat) (T : Nat → Nat) : ∀ s t a b d,
    formulaRecord L T s t (FOL.Formula.equal L a b) d =
      equalityRecord L T (antecedent L T s t d)
        (termRecord L T s t d a) (termRecord L T s t d b) := by
  intro s t a b d
  rw [formulaRecord_eq L T, FOL.Formula.recWithDepth_equal _ _ _ _ _]

theorem formulaRecord_rel (L : Nat) (T : Nat → Nat) : ∀ s t j xs d,
    j < FOL.Language.relationCount L → formulaRecord L T s t (FOL.Formula.rel L j xs) d =
      relationRecord L T (antecedent L T s t d) j
        (Tuple.map (termRecord L T s t d) (FOL.Language.relationArity L j) xs) := by
  intro s t j xs d hj
  rw [formulaRecord_eq L T]
  exact FOL.Formula.recWithDepth_rel _ _ _ _ _ L j xs d hj

theorem formulaRecord_imp (L : Nat) (T : Nat → Nat) : ∀ s t A B d,
    formulaRecord L T s t (FOL.Formula.imp A B) d =
      implicationRecord L T (antecedent L T s t d)
        (formulaRecord L T s t A d) (formulaRecord L T s t B d) := by
  intro s t A B d
  rw [formulaRecord_eq L T s t (FOL.Formula.imp A B) d,
    FOL.Formula.recWithDepth_imp _ _ _ _ _,
    ← formulaRecord_eq L T s t A d, ← formulaRecord_eq L T s t B d]

theorem formulaRecord_all (L : Nat) (T : Nat → Nat) : ∀ s t A d,
    formulaRecord L T s t (FOL.Formula.all A) d =
      universalRecord L T (antecedent L T s t d) (formulaRecord L T s t A (S d)) := by
  intro s t A d
  rw [formulaRecord_eq L T s t (FOL.Formula.all A) d,
    FOL.Formula.recWithDepth_all _ _ _ _ _, ← formulaRecord_eq L T s t A (S d)]

def formulaTest (L : Nat) (T : Nat → Nat) : Nat → Nat → Nat → Nat → Nat := fun s t A d =>
  recordTest L T equivalenceFormula (antecedent L T s t d)
    (FOL.Formula.substWithDepth (FOL.Term.instantiateAt L 0 s) L A d)
    (FOL.Formula.substWithDepth (FOL.Term.instantiateAt L 0 t) L A d)
    (formulaRecord L T s t A d)

theorem formulaTest_eq (L : Nat) (T : Nat → Nat) : ∀ s t A d, formulaTest L T s t A d =
    recordTest L T equivalenceFormula (antecedent L T s t d)
      (FOL.Formula.substWithDepth (FOL.Term.instantiateAt L 0 s) L A d)
      (FOL.Formula.substWithDepth (FOL.Term.instantiateAt L 0 t) L A d)
      (formulaRecord L T s t A d) := fun s t A d => rfl

/-- Every formula traversal produces a checked proof of the required equivalence. -/
theorem formulaRecord_valid (L : Nat) (T : Nat → Nat) (s t : Nat) : ∀ A d,
    Record L T equivalenceFormula (antecedent L T s t d)
      (FOL.Formula.substWithDepth (FOL.Term.instantiateAt L 0 s) L A d)
      (FOL.Formula.substWithDepth (FOL.Term.instantiateAt L 0 t) L A d)
      (formulaRecord L T s t A d) := by
  have good : ∀ A d, formulaTest L T s t A d = 1 := by
    apply FOL.Formula.induction_eq (formulaTest L T s t) (fun _ _ => 1) L
    · intro d
      rw [formulaTest_eq L T]
      apply and_right (recordTest_iff L T equivalenceFormula _ _ _ _)
      rw [formulaRecord_falsum L T,
        FOL.Formula.substWithDepth_falsum (FOL.Term.instantiateAt L 0 s)
          L d,
        FOL.Formula.substWithDepth_falsum (FOL.Term.instantiateAt L 0 t)
          L d]
      exact falsumRecord_valid L T _
    · intro a b d
      rw [formulaTest_eq L T]
      apply and_right (recordTest_iff L T equivalenceFormula _ _ _ _)
      rw [formulaRecord_equal L T,
        FOL.Formula.substWithDepth_equal (FOL.Term.instantiateAt L 0 s)
          L a b d,
        FOL.Formula.substWithDepth_equal (FOL.Term.instantiateAt L 0 t)
          L a b d]
      exact equalityRecord_valid L T _ _ _ _ _ _ _
        (termRecord_valid L T s t d a) (termRecord_valid L T s t d b)
    · intro j xs d hj
      let n := FOL.Language.relationArity L j
      have h := relationRecord_valid L T (antecedent L T s t d) j
        (Tuple.map (termRecord L T s t d) n xs) hj (by
          intro i hi
          rw [Tuple.get_map (termRecord L T s t d) n xs i hi]
          have h := termRecord_valid L T s t d (Tuple.get n xs i)
          rw [and_left h, and_left (and_right h)]
          exact and_right (and_right h))
      have hl := map_records lhs (termRecord L T s t d)
        (FOL.Term.subst (FOL.Term.instantiateAt L 0 s d) L) n xs
        (fun i hi => and_left (termRecord_valid L T s t d (Tuple.get n xs i)))
      have hr := map_records rhs (termRecord L T s t d)
        (FOL.Term.subst (FOL.Term.instantiateAt L 0 t d) L) n xs
        (fun i hi => and_left (and_right (termRecord_valid L T s t d (Tuple.get n xs i))))
      rw [hl, hr] at h
      rw [formulaTest_eq L T]
      apply and_right (recordTest_iff L T equivalenceFormula _ _ _ _)
      rw [formulaRecord_rel L T s t j xs d hj,
        FOL.Formula.substWithDepth_rel (FOL.Term.instantiateAt L 0 s) L j xs d hj,
        FOL.Formula.substWithDepth_rel (FOL.Term.instantiateAt L 0 t) L j xs d hj]
      exact h
    · intro A B d hA hB
      rw [formulaTest_eq L T] at hA
      rw [formulaTest_eq L T] at hB
      rw [formulaTest_eq L T]
      apply and_right (recordTest_iff L T equivalenceFormula _ _ _ _)
      rw [formulaRecord_imp L T,
        FOL.Formula.substWithDepth_imp (FOL.Term.instantiateAt L 0 s)
          L A B d,
        FOL.Formula.substWithDepth_imp (FOL.Term.instantiateAt L 0 t)
          L A B d]
      exact implicationRecord_valid L T _ _ _ _ _ _ _
        (and_left (recordTest_iff L T equivalenceFormula _ _ _ _) hA)
        (and_left (recordTest_iff L T equivalenceFormula _ _ _ _) hB)
    · intro A d hA
      rw [formulaTest_eq L T] at hA
      rw [formulaTest_eq L T]
      apply and_right (recordTest_iff L T equivalenceFormula _ _ _ _)
      rw [formulaRecord_all L T,
        FOL.Formula.substWithDepth_all (FOL.Term.instantiateAt L 0 s)
          L A d,
        FOL.Formula.substWithDepth_all (FOL.Term.instantiateAt L 0 t)
          L A d]
      exact universalRecord_valid L T s t d _ _ _
        (and_left (recordTest_iff L T equivalenceFormula _ _ _ _) hA)
  intro A d
  have h := good A d
  rw [formulaTest_eq L T] at h
  exact and_left (recordTest_iff L T equivalenceFormula _ _ _ _) h

/-- Equal terms give equivalent instances of every formula code `A` in any language `L` and
theory `T`. Instantiation replaces free position zero and lowers each later free position by one. -/
theorem substitution_congruence (L : Nat) (T : Nat → Nat) (s t A : Nat) : FOL.Provable L T
    (FOL.Formula.imp (FOL.Formula.equal L s t)
      (FOL.Formula.conj
        (FOL.Formula.imp (FOL.Formula.instantiate L A s)
          (FOL.Formula.instantiate L A t))
        (FOL.Formula.imp (FOL.Formula.instantiate L A t)
          (FOL.Formula.instantiate L A s)))) := by
  have h := and_right (and_right (formulaRecord_valid L T s t A 0))
  rw [antecedent, equation, FOL.Term.shift_zero, FOL.Term.shift_zero] at h
  exact (proof (formulaRecord L T s t A 0), h)

/-- Replace free position zero by equal terms while keeping later positions fixed. -/
theorem replace (L : Nat) (T : Nat → Nat) (s t A : Nat) : FOL.Provable L T
    (FOL.Formula.imp (FOL.Formula.equal L s t)
      (FOL.Formula.conj
        (FOL.Formula.imp
          (FOL.Formula.subst (FOL.consSubst s (FOL.shiftSubst L 1)) L A)
          (FOL.Formula.subst (FOL.consSubst t (FOL.shiftSubst L 1)) L A))
        (FOL.Formula.imp
          (FOL.Formula.subst (FOL.consSubst t (FOL.shiftSubst L 1)) L A)
          (FOL.Formula.subst (FOL.consSubst s (FOL.shiftSubst L 1)) L A)))) := by
  have h := substitution_congruence L T s t
    (FOL.Formula.subst (FOL.liftSubst (FOL.shiftSubst L 1) L 1) L A)
  rw [FOL.Formula.instantiate_subst_liftSubst (FOL.shiftSubst L 1) L A s,
    FOL.Formula.instantiate_subst_liftSubst (FOL.shiftSubst L 1) L A t] at h
  exact h

end FOL.Equality

extract_witness FOL.Equality.replace FOL.Equality.substitution_congruence

end
