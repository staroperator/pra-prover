module

public import PRAProver.Metatheory.Core.Properties.Normalization.CanonicalForms
import PRAProver.Metatheory.Core.Judgement.Formation

/-!
# Injectivity and separation of computational and logical constructors

- `FormulaHead` and `Predicate.formulaHead` identify logical formula constructors.
- `reducePredicate_head` preserves the head of an already weak-head formula.
- `TermEq.succ_injective`, `lam_injective`, and `zero_ne_succ` cover numerical constructors.
- `PredicateEq.head_eq` and `head_separation` compare weak-head logical constructors.
- `PredicateEq.equal_injective`, `imp_injective`, `and_injective`, and `or_injective` recover
  conversion of corresponding operands.
- `PredicateEq.all_injective`, `ex_injective`, and `lam_injective` recover predicate conversion.
- `no_equality_reflection` exhibits a proof context whose object equality hypothesis leaves
  numerical conversion unchanged.

The conversion results assume a valid environment and allow open, reducible operands. Logical
operand equalities are stated at Prop; predicate lambda bodies keep their displayed sort.
-/

namespace PRAProver.Core.Theory

/-- The irreducible logical constructors of formulas. -/
public inductive FormulaHead where
  | false | true | equal | imp | and | or | all | ex
  deriving DecidableEq, Repr

/-- Return the outermost logical constructor of a predicate, if any. -/
@[expose] public def _root_.PRAProver.Core.Predicate.formulaHead : Predicate → Option FormulaHead
  | .false => some .false
  | .true => some .true
  | .equal .. => some .equal
  | .imp .. => some .imp
  | .and .. => some .and
  | .or .. => some .or
  | .all .. => some .all
  | .ex .. => some .ex
  | _ => none

end PRAProver.Core.Theory

namespace PRAProver.Core

open Theory

/-- Reduction keeps the logical constructor of an already weak-head formula. -/
public theorem reducePredicate_head {E n P Q} (head : PredicateWhnf P)
    (run : reducePredicate n E 0 P = .ok Q) : Q.formulaHead = P.formulaHead := by
  cases n with
  | zero => simp [reducePredicate, exhausted, fail] at run
  | succ n =>
      simp only [reducePredicate, CheckResult.bind_eq_ok] at run
      obtain ⟨R, hR, run⟩ := run
      have eq := whnfPredicate_fixed head hR
      subst R
      cases P <;> simp only [CheckResult.bind_eq_ok, pure, Except.pure,
        Except.ok.injEq, fail] at run <;> try contradiction
      all_goals
        repeat first | obtain ⟨_, _, run⟩ := run | subst Q
        rfl

end PRAProver.Core

namespace PRAProver.Core.Theory

/-- Successor is injective for computational conversion, including on open numerical terms. -/
public theorem TermEq.succ_injective {E Ξ Γ a b} (valid : EnvironmentWF E)
    (eq : TermEq E Ξ Γ (.app .succ a) (.app .succ b) 0) : TermEq E Ξ Γ a b 0 := by
  obtain ⟨left, right⟩ := eq.regularity
  obtain ⟨A, nA, _, eA⟩ := TermEq.normal_form valid left.inv_app.2
  obtain ⟨B, nB, _, eB⟩ := TermEq.normal_form valid right.inv_app.2
  have same := (TermEq.normal_forms_iff valid
    (TermEq.app (.refl .succ) eA) (TermEq.app (.refl .succ) eB)
    (.app .succ nA) (.app .succ nB)).mp eq
  have same' := (Term.app.inj same).2
  exact .trans eA (same' ▸ eB.symm)

/-- Computationally equal numerical lambdas have equal bodies in the extended local context. -/
public theorem TermEq.lam_injective {E Ξ Γ t u k} (valid : EnvironmentWF E)
    (eq : TermEq E Ξ Γ (.lam binderName t) (.lam otherBinderName u) (k + 1)) :
    TermEq E Ξ (0 :: Γ) t u k := by
  obtain ⟨left, right⟩ := eq.regularity
  obtain ⟨i, hi, ht⟩ := left.inv_lam
  obtain ⟨j, hj, hu⟩ := right.inv_lam
  have ei : i = k := Nat.add_right_cancel hi.symm
  have ej : j = k := Nat.add_right_cancel hj.symm
  subst i; subst j
  obtain ⟨T, nT, _, eT⟩ := TermEq.normal_form valid ht
  obtain ⟨U, nU, _, eU⟩ := TermEq.normal_form valid hu
  have same := (TermEq.normal_forms_iff valid (TermEq.lam eT) (TermEq.lam eU)
    (.lam nT) (.lam nU)).mp eq
  have same' := (Term.lam.inj same).2
  exact .trans eT (same' ▸ eU.symm)

/-- Zero is not computationally convertible to successor, even with local variables. -/
public theorem TermEq.zero_ne_succ {E Ξ Γ a} (valid : EnvironmentWF E) :
    ¬ TermEq E Ξ Γ .zero (.app .succ a) 0 := by
  intro eq
  obtain ⟨A, nA, _, eA⟩ := TermEq.normal_form valid eq.regularity.2.inv_app.2
  have same := (TermEq.normal_forms_iff valid (TermEq.refl TermTyping.zero)
    (TermEq.app (.refl .succ) eA) .zero (.app .succ nA)).mp eq
  cases same

end PRAProver.Core.Theory

namespace PRAProver.Core.Theory

private theorem lift_eq {E Ξ Γ P Q k s} (eq : PredicateEq E Ξ Γ P Q ⟨k, s⟩) :
    PredicateEq E Ξ Γ P Q ⟨k, .prop⟩ := by
  cases s with
  | qf => exact .subsumption eq .lift
  | prop => exact eq

/-- Definitionally equal weak-head formulas have the same logical constructor tag. -/
public theorem PredicateEq.head_eq {E Ξ Γ P Q s} (valid : EnvironmentWF E)
    (left : PredicateWhnf P) (right : PredicateWhnf Q)
    (eq : PredicateEq E Ξ Γ P Q ⟨0, s⟩) : P.formulaHead = Q.formulaHead := by
  obtain ⟨n, R, hR⟩ := reducePredicate_of_eq valid eq
  exact (reducePredicate_head left (hR n (by omega)).1).symm.trans
    (reducePredicate_head right (hR n (by omega)).2)

/-- Different logical heads cannot be definitionally equal, regardless of their operands. -/
public theorem PredicateEq.head_separation {E Ξ Γ P Q s} (valid : EnvironmentWF E)
    (left : PredicateWhnf P) (right : PredicateWhnf Q)
    (different : P.formulaHead ≠ Q.formulaHead) : ¬ PredicateEq E Ξ Γ P Q ⟨0, s⟩ :=
  fun eq => different (eq.head_eq valid left right)

/-- Equality of atomic equality formulas converts the corresponding numerical sides. -/
public theorem PredicateEq.equal_injective {E Ξ Γ a b c d s} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ (.equal a b) (.equal c d) ⟨0, s⟩) :
    TermEq E Ξ Γ a c 0 ∧ TermEq E Ξ Γ b d 0 := by
  obtain ⟨left, right⟩ := eq.regularity valid
  obtain ⟨A, nA, _, eA⟩ := TermEq.normal_form valid left.inv_equal.1
  obtain ⟨B, nB, _, eB⟩ := TermEq.normal_form valid left.inv_equal.2.1
  obtain ⟨C, nC, _, eC⟩ := TermEq.normal_form valid right.inv_equal.1
  obtain ⟨D, nD, _, eD⟩ := TermEq.normal_form valid right.inv_equal.2.1
  have eLeft := lift_eq (PredicateEq.equal eA eB)
  have eRight := lift_eq (PredicateEq.equal eC eD)
  have same := (PredicateEq.normal_forms_iff valid eLeft eRight (.equal nA nB)
    (.equal nC nD)).mp (lift_eq eq)
  obtain ⟨rfl, rfl⟩ := Predicate.equal.inj same
  exact ⟨.trans eA eC.symm, .trans eB eD.symm⟩

/-- Conversion of implication formulas converts both corresponding operands at Prop. -/
public theorem PredicateEq.imp_injective {E Ξ Γ A B C D s} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ (.imp A B) (.imp C D) ⟨0, s⟩) :
    PredicateEq E Ξ Γ A C ⟨0, .prop⟩ ∧ PredicateEq E Ξ Γ B D ⟨0, .prop⟩ := by
  obtain ⟨left, right⟩ := eq.regularity valid
  obtain ⟨_, ha, hb, _⟩ := left.inv_imp
  obtain ⟨_, hc, hd, _⟩ := right.inv_imp
  obtain ⟨A', nA, _, eA⟩ := PredicateEq.normal_form valid ha.toProp
  obtain ⟨B', nB, _, eB⟩ := PredicateEq.normal_form valid hb.toProp
  obtain ⟨C', nC, _, eC⟩ := PredicateEq.normal_form valid hc.toProp
  obtain ⟨D', nD, _, eD⟩ := PredicateEq.normal_form valid hd.toProp
  have same := (PredicateEq.normal_forms_iff valid (PredicateEq.imp eA eB)
    (PredicateEq.imp eC eD) (.imp nA nB) (.imp nC nD)).mp (lift_eq eq)
  obtain ⟨rfl, rfl⟩ := Predicate.imp.inj same
  exact ⟨.trans eA eC.symm, .trans eB eD.symm⟩

/-- Conversion of conjunction formulas converts both corresponding operands at Prop. -/
public theorem PredicateEq.and_injective {E Ξ Γ A B C D s} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ (.and A B) (.and C D) ⟨0, s⟩) :
    PredicateEq E Ξ Γ A C ⟨0, .prop⟩ ∧ PredicateEq E Ξ Γ B D ⟨0, .prop⟩ := by
  obtain ⟨left, right⟩ := eq.regularity valid
  obtain ⟨_, ha, hb, _⟩ := left.inv_and
  obtain ⟨_, hc, hd, _⟩ := right.inv_and
  obtain ⟨A', nA, _, eA⟩ := PredicateEq.normal_form valid ha.toProp
  obtain ⟨B', nB, _, eB⟩ := PredicateEq.normal_form valid hb.toProp
  obtain ⟨C', nC, _, eC⟩ := PredicateEq.normal_form valid hc.toProp
  obtain ⟨D', nD, _, eD⟩ := PredicateEq.normal_form valid hd.toProp
  have same := (PredicateEq.normal_forms_iff valid (PredicateEq.and eA eB)
    (PredicateEq.and eC eD) (.and nA nB) (.and nC nD)).mp (lift_eq eq)
  obtain ⟨rfl, rfl⟩ := Predicate.and.inj same
  exact ⟨.trans eA eC.symm, .trans eB eD.symm⟩

/-- Conversion of disjunction formulas converts both corresponding operands at Prop. -/
public theorem PredicateEq.or_injective {E Ξ Γ A B C D s} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ (.or A B) (.or C D) ⟨0, s⟩) :
    PredicateEq E Ξ Γ A C ⟨0, .prop⟩ ∧ PredicateEq E Ξ Γ B D ⟨0, .prop⟩ := by
  obtain ⟨left, right⟩ := eq.regularity valid
  obtain ⟨_, ha, hb, _⟩ := left.inv_or
  obtain ⟨_, hc, hd, _⟩ := right.inv_or
  obtain ⟨A', nA, _, eA⟩ := PredicateEq.normal_form valid ha.toProp
  obtain ⟨B', nB, _, eB⟩ := PredicateEq.normal_form valid hb.toProp
  obtain ⟨C', nC, _, eC⟩ := PredicateEq.normal_form valid hc.toProp
  obtain ⟨D', nD, _, eD⟩ := PredicateEq.normal_form valid hd.toProp
  have same := (PredicateEq.normal_forms_iff valid (PredicateEq.or eA eB)
    (PredicateEq.or eC eD) (.or nA nB) (.or nC nD)).mp (lift_eq eq)
  obtain ⟨rfl, rfl⟩ := Predicate.or.inj same
  exact ⟨.trans eA eC.symm, .trans eB eD.symm⟩

/-- Conversion of universal formulas converts their unary predicates. -/
public theorem PredicateEq.all_injective {E Ξ Γ P Q s} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ (.all P) (.all Q) ⟨0, s⟩) :
    PredicateEq E Ξ Γ P Q ⟨1, .prop⟩ := by
  obtain ⟨left, right⟩ := eq.regularity valid
  obtain ⟨P', nP, _, eP⟩ := PredicateEq.normal_form valid left.inv_all.2
  obtain ⟨Q', nQ, _, eQ⟩ := PredicateEq.normal_form valid right.inv_all.2
  have same := (PredicateEq.normal_forms_iff valid (PredicateEq.all eP)
    (PredicateEq.all eQ) (.all nP) (.all nQ)).mp (lift_eq eq)
  have same' := Predicate.all.inj same
  exact .trans eP (same' ▸ eQ.symm)

/-- Conversion of existential formulas converts their unary predicates. -/
public theorem PredicateEq.ex_injective {E Ξ Γ P Q s} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ (.ex P) (.ex Q) ⟨0, s⟩) :
    PredicateEq E Ξ Γ P Q ⟨1, .prop⟩ := by
  obtain ⟨left, right⟩ := eq.regularity valid
  obtain ⟨P', nP, _, eP⟩ := PredicateEq.normal_form valid left.inv_ex.2
  obtain ⟨Q', nQ, _, eQ⟩ := PredicateEq.normal_form valid right.inv_ex.2
  have same := (PredicateEq.normal_forms_iff valid (PredicateEq.ex eP)
    (PredicateEq.ex eQ) (.ex nP) (.ex nQ)).mp (lift_eq eq)
  have same' := Predicate.ex.inj same
  exact .trans eP (same' ▸ eQ.symm)

/-- Convertible predicate lambdas have convertible bodies at their displayed sort. -/
public theorem PredicateEq.lam_injective {E Ξ Γ P Q k s} (valid : EnvironmentWF E)
    (eq : PredicateEq E Ξ Γ (.lam binderName P) (.lam otherBinderName Q) ⟨k + 1, s⟩) :
    PredicateEq E Ξ (0 :: Γ) P Q ⟨k, s⟩ := by
  obtain ⟨left, right⟩ := eq.regularity valid
  obtain ⟨P', nP, _, eP⟩ := PredicateEq.normal_form valid left.lam_body
  obtain ⟨Q', nQ, _, eQ⟩ := PredicateEq.normal_form valid right.lam_body
  have same := (PredicateEq.normal_forms_iff valid (PredicateEq.lam eP)
    (PredicateEq.lam eQ) (.lam nP) (.lam nQ)).mp eq
  have same' := (Predicate.lam.inj same).2
  exact .trans eP (same' ▸ eQ.symm)

end PRAProver.Core.Theory

namespace PRAProver.Core.Theory

/-- An object equality hypothesis in a formed context leaves computational conversion of `0`
and `succ 0` distinct. -/
public theorem no_equality_reflection {E} (valid : EnvironmentWF E) :
    ∃ Δ, ContextWF E {} [] Δ ∧
      ProofTyping E {} [] Δ (.hyp 0) (.equal .zero (.app .succ .zero)) ∧
      ¬ TermEq E {} [] .zero (.app .succ .zero) 0 := by
  have formed : PredicateTyping E {} [] (.equal .zero (.app .succ .zero)) ⟨0, .prop⟩ :=
    .subsumption (.equal .zero (.app .succ .zero)) .lift
  exact ⟨[.equal .zero (.app .succ .zero)], .cons formed .nil, .hyp rfl,
    TermEq.zero_ne_succ valid⟩

end PRAProver.Core.Theory
