module

public import LeanPRA.Library.FOL.PRA.Provability.D3
meta import LeanPRA.Library.FOL.DSL.Tactic
meta import LeanPRA.Library.Tactic.Witness.Scoped

/-!
# Transitivity of provability in first-order PRA

- `FOL.PRA.equation_complete`: provability of primitive recursive evaluation equations in PRA.
- `FOL.PRA.pr_pr` and `FOL.PRA.pr_pr_num`: the second Hilbert–Bernays–Löb provability condition.
-/

namespace FOL.PRA

pra

/-! ## Syntactic operations -/

/-! ### Encoding `num` -/

theorem const_zero_language : Term.const language 0 = 0 := by
  apply Term.const_of_lt
  rw [FOL.PRA.constants_language]
  exact lt_succ_self 0

theorem eval_num_zero : (PRA ⊢ eval[num.code](zero) = zero) := by
  have hv := eval_num_of_evaluates num.code 0 (num 0) (num.trace 0) (num.computedBy 0)
  have hn : num 0 = 0 := eq_trans num_zero const_zero_language
  have h := eq_subst
    (fun y => (PRA ⊢ eval[num.code](${num 0}) = ${num y})) hn hv
  rw [num_zero] at h
  exact h

/-! ### Proof numbers and bounded instantiation -/

extract_witness FOL.Provable.mp FOL.Provable.gen

extract_witness FOL.PRA.Evaluation.refl FOL.PRA.Evaluation.symm

extract_witness FOL.PRA.Evaluation.congr_eval FOL.PRA.Evaluation.congr_pair

theorem provable_imp_instantiate_of_le (L : Nat) (T : Nat → Nat) : ∀ A t,
    t ≤ Formula.imp (Formula.all A) (Formula.instantiate L A t) →
    FOL.Provable L T (Formula.imp (Formula.all A) (Formula.instantiate L A t)) := by
  intro A t bound
  exact FOL.Provable.axiom L T _ (isLogicalAxiom_of_instantiation L A t bound)

theorem isProofOf_instantiate_of_le (L : Nat) (T : Nat → Nat) : ∀ A t p,
    t ≤ Formula.imp (Formula.all A) (Formula.instantiate L A t) →
    IsProofOf L T (Formula.all A) p →
      IsProofOf L T (Formula.instantiate L A t)
        (Proof.mp (Formula.instantiate L A t)
          (Proof.axiom (Formula.imp (Formula.all A) (Formula.instantiate L A t))) p) := by
  intro A t p bound h
  let F := Formula.imp (Formula.all A) (Formula.instantiate L A t)
  have accepted := isLogicalAxiom_of_instantiation L A t bound
  exact IsProofOf.mp L T (Formula.all A) (Formula.instantiate L A t) (Proof.axiom F) p
    (isProof_axiom L T F accepted, Proof.conclusion_axiom F) h

/-! ### Instantiation of unary equations -/

theorem le_imp_equal_app : ∀ L j p t z,
    t ≤ Formula.imp p (Formula.equal L (Term.app L j t) z) := by
  intro L j p t z
  let u := Term.app L j t
  let b := Formula.equal L u z
  exact le_trans _ u _ (le_of_lt t u (Term.args_lt_app L j t))
    (le_trans u b _ (Formula.le_equal_left L u z)
      (le_of_lt b _ (Formula.right_lt_imp p b)))

derive_fol_pra le_imp_equal_app as le_imp_equal_app_inner

theorem isProofOf_equal_app_of_instantiate (L : Nat) (T : Nat → Nat) : ∀ A j t z p,
    Formula.instantiate L A t = Formula.equal L (Term.app L j t) z →
    IsProofOf L T (Formula.all A) p →
    IsProofOf L T (Formula.equal L (Term.app L j t) z)
      (Proof.mp (Formula.equal L (Term.app L j t) z)
        (Proof.axiom (Formula.imp (Formula.all A) (Formula.equal L (Term.app L j t) z))) p) := by
  intro A j t z p instanceEq accepted
  let U := Formula.all A
  let B := Formula.equal L (Term.app L j t) z
  have bound := le_imp_equal_app L j U t z
  have boundAt := eq_subst (fun b => t ≤ Formula.imp U b) (eq_symm instanceEq) bound
  have used := isProofOf_instantiate_of_le L T A t p boundAt accepted
  exact eq_subst (fun b => IsProofOf L T b (Proof.mp b (Proof.axiom (Formula.imp U b)) p))
    instanceEq used

derive_fol_pra (public := true) isProofOf_equal_app_of_instantiate
  as praProofOf_equal_app_of_instantiate

/-! ### Syntax calculations used in substitution -/

theorem eval_pair_num_of_evaluates (e a b y t : Nat) :
    Primrec.Computation.Evaluates e (pair a b) y t →
    (PRA ⊢ eval[e](pair(${num a}, ${num b})) = ${num y}) := by
  intro h
  exact Evaluation.trans _ _ _ (eval_pair_num e a b) (eval_num_of_evaluates e _ y t h)

theorem functionFamilyMember_zero_language :
    Language.functionFamilyMember language 0 Primrec.Code.zero = 2 := by
  have symbol : ∀ L,
      Language.functionFamilyMember L 0 Primrec.Code.zero = Language.functionCount L :=
    fun L => rfl
  exact eq_trans (symbol language) FOL.PRA.functionCount_language

theorem var_zero_language : Term.var language 0 = 1 := by
  have variableCode : ∀ L, Term.var L 0 = Language.constants L := fun L => rfl
  exact eq_trans (variableCode language) FOL.PRA.constants_language

theorem var_one_language : Term.var language 1 = 5 := by
  rw [Term.var, mul_one, FOL.PRA.constants_language, FOL.PRA.functionCount_language,
    FOL.PRA.functionFamilyCount_language, language, Language.constantFamilyCount_make]
  rfl

theorem num_eq_of_eq (a b : Nat) : a = b → (PRA ⊢ ${num a} = ${num b}) :=
  fun h => eq_subst (fun n => (PRA ⊢ ${num a} = ${num n})) h (Evaluation.refl (num a))

theorem num_succ_eq : ∀ n, (PRA ⊢ ${num (S n)} = succ(${num n})) :=
  fun n => eq_subst (fun y => (PRA ⊢ ${num (S n)} = y)) (num_succ n)
    (Evaluation.refl (num (S n)))

theorem num_one : (PRA ⊢ ${num 1} = succ(zero)) := by
  have h := num_succ_eq 0
  rw [num_zero] at h
  exact h

theorem num_two : (PRA ⊢ ${num 2} = succ(succ(zero))) := by
  prw [num_succ_eq 1, num_one]

theorem num_three : (PRA ⊢ ${num 3} = succ(succ(succ(zero)))) := by
  prw [num_succ_eq 2, num_two]

theorem num_five : (PRA ⊢ ${num 5} = succ(succ(succ(succ(succ(zero)))))) := by
  prw [num_succ_eq 4, num_succ_eq 3, num_succ_eq 2,
      num_succ_eq 1, num_one]

/-! ### Substitution into proof formulas -/

theorem eval_language_code :
    (PRA ⊢ eval[language.code](zero) = ${num language}) := by
  have h := eval_num_of_evaluates language.code 0 language (language.trace 0)
    (language.computedBy 0)
  rw [num_zero] at h
  exact h

theorem eval_functionCount_language :
    (PRA ⊢ eval[Language.functionCount.code](${num language}) = succ(succ(zero))) := by
  have h := eval_num_of_evaluates Language.functionCount.code language _
    (Language.functionCount.trace language) (Language.functionCount.computedBy language)
  rw [FOL.PRA.functionCount_language, num_succ 1, num_succ 0, num_zero] at h
  exact h

theorem eval_functionFamilyCount_language :
    (PRA ⊢ eval[Language.functionFamilyCount.code](${num language}) = succ(zero)) := by
  have h := eval_num_of_evaluates Language.functionFamilyCount.code language _
    (Language.functionFamilyCount.trace language) (Language.functionFamilyCount.computedBy language)
  rw [FOL.PRA.functionFamilyCount_language, num_succ 0, num_zero] at h
  exact h

namespace Substitution

theorem subst_var : ∀ t d i,
    Term.subst (Term.instantiateAt language 0 t d) language (Term.var language i) =
      Term.instantiateAt language 0 t d i :=
  fun t d i => Term.subst_var (Term.instantiateAt language 0 t d) language i

theorem subst_eval : ∀ t d e x,
    Term.subst (Term.instantiateAt language 0 t d) language (Term.app language
      (Language.functionFamilyMember language 0 e) x) =
      Term.app language (Language.functionFamilyMember language 0 e) (Term.subst (Term.instantiateAt
        language 0 t d) language x) := by
  intro t d e x
  exact Term.subst_app_one (Term.instantiateAt language 0 t d) language
    (Language.functionFamilyMember language 0 e) x (FOL.PRA.isFunction_eval e)
    (FOL.PRA.eval_arity e)

theorem subst_succ : ∀ t d x,
    Term.subst (Term.instantiateAt language 0 t d) language (Term.app language 0 x) = Term.app
      language 0 (Term.subst (Term.instantiateAt language 0 t d) language x) :=
  fun t d x => Term.subst_app_one (Term.instantiateAt language 0 t d) language 0 x
    FOL.PRA.isFunction_succ FOL.PRA.succ_arity

theorem subst_pair : ∀ t d a b,
    Term.subst (Term.instantiateAt language 0 t d) language (Term.app language 1 (pair a b)) =
      Term.app language 1 (pair (Term.subst (Term.instantiateAt language 0 t d) language a)
        (Term.subst (Term.instantiateAt language 0 t d) language b)) :=
  fun t d a b => Term.subst_app_two (Term.instantiateAt language 0 t d) language 1 a b
    FOL.PRA.isFunction_pair FOL.PRA.pair_arity

theorem subst_num : ∀ t d n, Term.subst (Term.instantiateAt language 0 t d) language (num n) = num
  n := by
  intro t d n
  exact FOL.PRA.subst_num (Term.instantiateAt language 0 t d) n

theorem zero_lt_constants_language : 0 < Language.constants language := by
  rw [FOL.PRA.constants_language]
  exact lt_succ_self 0

theorem subst_const_zero : ∀ t d, Term.subst (Term.instantiateAt language 0 t d) language
    (Term.const language 0) = Term.const language 0 := by
  intro t d
  exact Term.subst_const (Term.instantiateAt language 0 t d) language 0 (Language.isConstant_of_lt
    language 0 zero_lt_constants_language)

theorem substWithDepth_equal : ∀ t d x y,
    Formula.substWithDepth (Term.instantiateAt language 0 t) language (Formula.equal language x y) d
      =
      Formula.equal language (Term.subst (Term.instantiateAt language 0 t d) language x) (Term.subst
        (Term.instantiateAt language 0 t d) language y) :=
  fun t d x y => Formula.substWithDepth_equal (Term.instantiateAt language 0 t) language x y d

theorem substWithDepth_imp : ∀ t d A B,
    Formula.substWithDepth (Term.instantiateAt language 0 t) language (Formula.imp A B) d =
      Formula.imp (Formula.substWithDepth (Term.instantiateAt language 0 t) language A d)
      (Formula.substWithDepth (Term.instantiateAt language 0 t) language B d) :=
  fun t d A B => Formula.substWithDepth_imp (Term.instantiateAt language 0 t) language A B d

theorem substWithDepth_all : ∀ t d A,
    Formula.substWithDepth (Term.instantiateAt language 0 t) language (Formula.all A) d =
      Formula.all (Formula.substWithDepth (Term.instantiateAt language 0 t) language A (S d)) :=
  fun t d A => Formula.substWithDepth_all (Term.instantiateAt language 0 t) language A d

theorem substWithDepth_falsum : ∀ t d, Formula.substWithDepth (Term.instantiateAt language 0 t)
    language Formula.falsum d = Formula.falsum :=
  fun t d => Formula.substWithDepth_falsum (Term.instantiateAt language 0 t) language d

theorem instantiate_eq_substWithDepth : ∀ A t,
    Formula.instantiate language A t = Formula.substWithDepth (Term.instantiateAt language 0 t)
      language A 0 := fun A t => rfl

theorem subst_var_self : ∀ t d,
    Term.subst (Term.instantiateAt language 0 t d) language (Term.var language d) = Term.shift
      language d t := by
  intro t d
  have test := ltb_eq_zero_of_ge d d (le_refl d)
  rw [subst_var, Term.instantiateAt, test, ite_zero, sub_self, eqb_self, ite_succ]

theorem subst_var_of_lt : ∀ t d i, i < d →
    Term.subst (Term.instantiateAt language 0 t d) language (Term.var language i) = Term.var
      language i := by
  intro t d i bound
  rw [subst_var]
  exact Term.instantiateAt_below language t d i bound

theorem shift_num : ∀ d n, Term.shift language d (num n) = num n := by
  intro d n
  exact eq_trans (Term.shift_eq_subst_shiftSubst language d (num n))
    (FOL.PRA.subst_num (FOL.shiftSubst language d) n)

theorem subst_var_zero_at_zero : ∀ t, Term.subst (Term.instantiateAt language 0 t 0) language 1 =
  Term.shift language 0 t :=
  fun t => eq_trans (eq_congr (Term.subst (Term.instantiateAt language 0 t 0) language) (eq_symm
    var_zero_language)) (subst_var_self t 0)

theorem subst_var_one_at_one : ∀ t, Term.subst (Term.instantiateAt language 0 t 1) language 5 =
  Term.shift language 1 t :=
  fun t => eq_trans (eq_congr (Term.subst (Term.instantiateAt language 0 t 1) language) (eq_symm
    var_one_language)) (subst_var_self t 1)

theorem subst_var_zero_at_one : ∀ t, Term.subst (Term.instantiateAt language 0 t 1) language 1 =
    1 :=
  fun t => eq_trans (eq_congr (Term.subst (Term.instantiateAt language 0 t 1) language) (eq_symm
    var_zero_language))
    (eq_trans (subst_var_of_lt t 1 0 (lt_succ_self 0)) var_zero_language)

theorem subst_zero : ∀ t d, Term.subst (Term.instantiateAt language 0 t d) language 0 = 0 := by
  intro t d
  exact eq_trans (eq_congr (Term.subst (Term.instantiateAt language 0 t d) language)
    (eq_symm const_zero_language)) (eq_trans (subst_const_zero t d) const_zero_language)

theorem instantiate_succ_equation : ∀ L e t, L = language →
    Formula.instantiate L (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 e) 1)
      (Term.app L 0 1)) t =
      (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 e) (Term.shift L 0 t))
        (Term.app L 0 (Term.shift L 0 t))) := by
  intro L e t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_equal, subst_eval, subst_var_zero_at_zero,
    subst_succ, subst_var_zero_at_zero]

theorem instantiate_comp_equation : ∀ L c f g t, L = language →
    Formula.instantiate L (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 c) 1)
      (Term.app L (Language.functionFamilyMember L 0 f) (Term.app L (Language.functionFamilyMember L
      0 g) 1))) t =
      (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 c) (Term.shift L 0 t))
        (Term.app L (Language.functionFamilyMember L 0 f) (Term.app L (Language.functionFamilyMember
        L 0 g) (Term.shift L 0 t)))) := by
  intro L c f g t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_equal, subst_eval, subst_var_zero_at_zero,
    subst_eval, subst_eval, subst_var_zero_at_zero]

theorem instantiate_pair_zero_succ : ∀ L t, L = language →
    Formula.instantiate L (Formula.equal L (Term.app L 1 (pair 0 (Term.app L 0 1))) (Term.app L 0
      (Term.app L 1 (pair 1 0)))) t =
      (Formula.equal L (Term.app L 1 (pair 0 (Term.app L 0 (Term.shift L 0 t)))) (Term.app L 0
        (Term.app L 1 (pair (Term.shift L 0 t) 0)))) := by
  intro L t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_equal, subst_pair, subst_zero, subst_succ,
    subst_var_zero_at_zero, subst_succ, subst_pair, subst_var_zero_at_zero, subst_zero]

theorem instantiate_rec_zero_equation : ∀ L c f t, L = language →
    Formula.instantiate L (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 c)
      (Term.app L 1 (pair 1 0))) (Term.app L (Language.functionFamilyMember L 0 f) 1)) t =
      (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 c) (Term.app L 1 (pair
        (Term.shift L 0 t) 0))) (Term.app L (Language.functionFamilyMember L 0 f) (Term.shift L 0
        t))) := by
  intro L c f t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_equal, subst_eval, subst_pair,
    subst_var_zero_at_zero, subst_zero, subst_eval, subst_var_zero_at_zero]

theorem instantiate_pair_equation : ∀ L c f g t, L = language →
    Formula.instantiate L (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 c) 1)
      (Term.app L 1 (pair (Term.app L (Language.functionFamilyMember L 0 f) 1) (Term.app L
      (Language.functionFamilyMember L 0 g) 1)))) t =
      (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 c) (Term.shift L 0 t))
        (Term.app L 1 (pair (Term.app L (Language.functionFamilyMember L 0 f) (Term.shift L 0 t))
        (Term.app L (Language.functionFamilyMember L 0 g) (Term.shift L 0 t))))) := by
  intro L c f g t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_equal, subst_eval, subst_var_zero_at_zero,
    subst_pair, subst_eval, subst_var_zero_at_zero, subst_eval, subst_var_zero_at_zero]

theorem instantiate_pair_succ_first : ∀ L t, L = language →
    Formula.instantiate L (Formula.all (Formula.equal L (Term.app L 1 (pair (Term.app L 0 5) 1))
      (Term.app L 0 (Term.app L 1 (pair 5 (Term.app L 0 1)))))) t =
      (Formula.all (Formula.equal L (Term.app L 1 (pair (Term.app L 0 (Term.shift L 1 t)) 1))
        (Term.app L 0 (Term.app L 1 (pair (Term.shift L 1 t) (Term.app L 0 1)))))) := by
  intro L t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_all, substWithDepth_equal, subst_pair,
    subst_succ, subst_var_one_at_one, subst_var_zero_at_one, subst_succ, subst_pair,
    subst_var_one_at_one, subst_succ, subst_var_zero_at_one]

theorem instantiate_pair_succ_second : ∀ L a t, L = language →
    Formula.instantiate L (Formula.equal L (Term.app L 1 (pair (Term.app L 0 (num a)) 1)) (Term.app
      L 0 (Term.app L 1 (pair (num a) (Term.app L 0 1))))) t =
      (Formula.equal L (Term.app L 1 (pair (Term.app L 0 (num a)) (Term.shift L 0 t))) (Term.app L 0
        (Term.app L 1 (pair (num a) (Term.app L 0 (Term.shift L 0 t)))))) := by
  intro L a t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_equal, subst_pair, subst_succ, subst_num,
    subst_var_zero_at_zero, subst_succ, subst_pair, subst_num, subst_succ,
    subst_var_zero_at_zero]

theorem instantiate_left_first : ∀ L t, L = language →
    Formula.instantiate L (Formula.all (Formula.equal L (Term.app L (Language.functionFamilyMember L
      0 2) (Term.app L 1 (pair 5 1))) 5)) t =
      (Formula.all (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 2) (Term.app L 1
        (pair (Term.shift L 1 t) 1))) (Term.shift L 1 t))) := by
  intro L t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_all, substWithDepth_equal, subst_eval,
    subst_pair, subst_var_one_at_one, subst_var_zero_at_one]

theorem instantiate_left_second : ∀ L a t, L = language →
    Formula.instantiate L (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 2)
      (Term.app L 1 (pair (num a) 1))) (num a)) t =
      (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 2) (Term.app L 1 (pair (num a)
        (Term.shift L 0 t)))) (num a)) := by
  intro L a t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_equal, subst_eval, subst_pair, subst_num,
    subst_var_zero_at_zero]

theorem instantiate_right_first : ∀ L t, L = language →
    Formula.instantiate L (Formula.all (Formula.equal L (Term.app L (Language.functionFamilyMember L
      0 3) (Term.app L 1 (pair 5 1))) 1)) t =
      (Formula.all (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 3) (Term.app L 1
        (pair (Term.shift L 1 t) 1))) 1)) := by
  intro L t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_all, substWithDepth_equal, subst_eval,
    subst_pair, subst_var_one_at_one, subst_var_zero_at_one]

theorem instantiate_right_second : ∀ L a t, L = language →
    Formula.instantiate L (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 3)
      (Term.app L 1 (pair (num a) 1))) 1) t =
      (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 3) (Term.app L 1 (pair (num a)
        (Term.shift L 0 t)))) (Term.shift L 0 t)) := by
  intro L a t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_equal, subst_eval, subst_pair, subst_num,
    subst_var_zero_at_zero]

theorem instantiate_rec_succ_first : ∀ L c g t, L = language →
    Formula.instantiate L (Formula.all (Formula.equal L (Term.app L (Language.functionFamilyMember L
      0 c) (Term.app L 1 (pair 5 (Term.app L 0 1)))) (Term.app L (Language.functionFamilyMember L 0
      g) (Term.app L 1 (pair 5 (Term.app L 1 (pair 1 (Term.app L (Language.functionFamilyMember L 0
      c) (Term.app L 1 (pair 5 1)))))))))) t =
      (Formula.all (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 c) (Term.app L 1
        (pair (Term.shift L 1 t) (Term.app L 0 1)))) (Term.app L (Language.functionFamilyMember L 0
        g) (Term.app L 1 (pair (Term.shift L 1 t) (Term.app L 1 (pair 1 (Term.app L
        (Language.functionFamilyMember L 0 c) (Term.app L 1 (pair (Term.shift L 1 t) 1)))))))))) :=
          by
  intro L c g t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_all, substWithDepth_equal, subst_eval,
    subst_pair, subst_var_one_at_one, subst_succ, subst_var_zero_at_one, subst_eval, subst_pair,
    subst_var_one_at_one, subst_pair, subst_var_zero_at_one, subst_eval, subst_pair,
    subst_var_one_at_one, subst_var_zero_at_one]

theorem instantiate_rec_succ_second : ∀ L c g a t, L = language →
    Formula.instantiate L (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 c)
      (Term.app L 1 (pair (num a) (Term.app L 0 1)))) (Term.app L (Language.functionFamilyMember L 0
      g) (Term.app L 1 (pair (num a) (Term.app L 1 (pair 1 (Term.app L
      (Language.functionFamilyMember L 0 c) (Term.app L 1 (pair (num a) 1))))))))) t =
      (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 c) (Term.app L 1 (pair (num a)
        (Term.app L 0 (Term.shift L 0 t))))) (Term.app L (Language.functionFamilyMember L 0 g)
        (Term.app L 1 (pair (num a) (Term.app L 1 (pair (Term.shift L 0 t) (Term.app L
        (Language.functionFamilyMember L 0 c) (Term.app L 1 (pair (num a) (Term.shift L 0
        t)))))))))) := by
  intro L c g a t languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, substWithDepth_equal, subst_eval, subst_pair, subst_num,
    subst_succ, subst_var_zero_at_zero, subst_eval, subst_pair, subst_num, subst_pair,
    subst_var_zero_at_zero, subst_eval, subst_pair, subst_num, subst_var_zero_at_zero]

derive_fol_pra shift_num as shift_num_inner

derive_fol_pra instantiate_eq_substWithDepth as instantiate_eq_substWithDepth_inner

derive_fol_pra substWithDepth_equal as substWithDepth_equal_inner

derive_fol_pra substWithDepth_all as substWithDepth_all_inner

derive_fol_pra substWithDepth_imp as substWithDepth_imp_inner

derive_fol_pra substWithDepth_falsum as substWithDepth_falsum_inner

derive_fol_pra subst_eval as subst_eval_inner

derive_fol_pra subst_succ as subst_succ_inner

derive_fol_pra subst_pair as subst_pair_inner

derive_fol_pra subst_num as subst_num_inner

derive_fol_pra subst_var_zero_at_zero as subst_var_zero_at_zero_inner

derive_fol_pra subst_var_one_at_one as subst_var_one_at_one_inner

derive_fol_pra subst_var_zero_at_one as subst_var_zero_at_one_inner

derive_fol_pra subst_zero as subst_zero_inner

derive_fol_pra instantiate_succ_equation as instantiate_succ_equation_inner

derive_fol_pra instantiate_comp_equation as instantiate_comp_equation_inner

derive_fol_pra instantiate_pair_zero_succ as instantiate_pair_zero_succ_inner

derive_fol_pra instantiate_rec_zero_equation as instantiate_rec_zero_equation_inner

derive_fol_pra instantiate_pair_equation as instantiate_pair_equation_inner

derive_fol_pra instantiate_pair_succ_first as instantiate_pair_succ_first_inner

derive_fol_pra instantiate_pair_succ_second as instantiate_pair_succ_second_inner

derive_fol_pra instantiate_left_first as instantiate_left_first_inner

derive_fol_pra instantiate_left_second as instantiate_left_second_inner

derive_fol_pra instantiate_right_first as instantiate_right_first_inner

derive_fol_pra instantiate_right_second as instantiate_right_second_inner

derive_fol_pra instantiate_rec_succ_first as instantiate_rec_succ_first_inner

derive_fol_pra instantiate_rec_succ_second as instantiate_rec_succ_second_inner

end Substitution

/-! ### Shifting `num` at cutoffs zero and one -/

namespace NumShift

fol_def numCode over PRA : term of 1 := fun n =>
  eval[num.code](n)

fol_def succCode over PRA : term of 1 := fun t =>
  eval[Term.app.code](pair(${num language}, pair(zero, t)))

fol_def shiftZeroCode over PRA : term of 1 := fun t =>
  eval[Term.shift.code](pair(${num language}, pair(zero, t)))

derive_fol_pra FOL.PRA.num_succ as num_succ_inner

fol_theorem num_succ_code : PRA ⊢ ∀ n,
    eval[num.code](succ(n)) =
      eval[Term.app.code](pair(${num language}, pair(zero, eval[num.code](n)))) := by
  pintro n
  ptrans eval[Term.app.code](pair(eval[language.code](zero), pair(zero, eval[num.code](n))))
  · pexact num_succ_inner[n]
  · prw [eval_language_code]

fol_theorem lt_succCode : PRA ⊢ ∀ t,
    eval[sub.code](pair(succ(t), succCode(t))) = zero := by
  pintro t
  pexact FOL.PRA.term_args_lt_app[${num language}, zero, t]

fol_theorem shift_num : PRA ⊢ ∀ n, shiftZeroCode(numCode(n)) = numCode(n) := by
  pintro n
  ptrans eval[Term.shift.code](pair(eval[language.code](zero),
    pair(zero, numCode(n))))
  · prw [eval_language_code]
  · pexact Substitution.shift_num_inner[zero, n]

fol_def shiftOneCode over PRA : term of 1 := fun t =>
  eval[Term.shift.code](pair(${num language}, pair(${num 1}, t)))

fol_theorem shift_one_num : PRA ⊢ ∀ n, shiftOneCode(numCode(n)) = numCode(n) := by
  pintro n
  ptrans eval[Term.shift.code](pair(eval[language.code](zero),
    pair(succ(zero), numCode(n))))
  · prw [eval_language_code, num_one]
  · pexact Substitution.shift_num_inner[succ(zero), n]

end NumShift

/-! ### Substitution in indexed applications -/

theorem indexed_application_fields : ∀ L e t,
    Language.functionFamilyCount L = 1 → Language.functionFamilyArity L 0 = 1 →
    Term.head L (Term.app L (Language.functionFamilyMember L 0 e) t) =
        S (Language.functionFamilyMember L 0 e) ∧
      Term.arg L (Term.app L (Language.functionFamilyMember L 0 e) t) = t ∧
      Language.functionSymbolArity L (Language.functionFamilyMember L 0 e) = 1 := by
  intro L e t count arity
  have h : 0 < Language.functionFamilyCount L := by
    rw [count]
    exact lt_succ_self 0
  have valid := Language.isFunction_familyMember L 0 e h
  exact (Term.head_app L _ t valid, Term.arg_app L _ t valid,
    eq_trans (Language.functionSymbolArity_familyMember L 0 e h) arity)

derive_fol_pra indexed_application_fields as indexed_application_fields_inner

theorem functionFamilyArity_language : Language.functionFamilyArity language 0 = 1 :=
  eq_trans (eq_symm (Language.functionSymbolArity_familyMember language 0 0 FOL.PRA.eval_lt))
    (FOL.PRA.eval_arity 0)

theorem eval_functionFamilyArity_language :
    (PRA ⊢ eval[Language.functionFamilyArity.code](pair(${num language}, zero)) = succ(zero)) := by
  let e := Language.functionFamilyArity.code
  let x := pair language 0
  have tree := Language.functionFamilyArity.computedBy x
  have h := Evaluation.trans _ _ _ (eval_pair_num e language 0)
    (eval_num_of_evaluates e x _ (Language.functionFamilyArity.trace x) tree)
  have read := eq_trans (eq_congr₂ Language.functionFamilyArity (unpairLeft_pair language 0)
    (unpairRight_pair language 0)) functionFamilyArity_language
  rw [read, num_succ 0, num_zero] at h
  exact h

fol_def evalSymbol over PRA : term of 1 := fun e =>
  eval[Language.functionFamilyMember.code](pair(${num language}, pair(zero, e)))

fol_def evalApplication over PRA : term of 2 := fun e t =>
  eval[Term.app.code](pair(${num language}, pair(evalSymbol(e), t)))

fol_theorem eval_application_fields : PRA ⊢ ∀ e t,
    eval[Term.head.code](pair(${num language}, evalApplication(e, t))) = succ(evalSymbol(e)) ∧
    eval[Term.arg.code](pair(${num language}, evalApplication(e, t))) = t ∧
    eval[Language.functionSymbolArity.code](pair(${num language}, evalSymbol(e))) = succ(zero) := by
  pintro e t
  papply indexed_application_fields_inner[${num language}, e, t]
  · pexact eval_functionFamilyCount_language
  · pexact eval_functionFamilyArity_language

fol_def evalEquation over PRA : term of 3 := fun e t v =>
  eval[Formula.equal.code](pair(${num language}, pair(evalApplication(e, t), v)))

fol_def succEquation over PRA : term of 2 := fun e t =>
  evalEquation(e, t, NumShift.succCode(t))

fol_theorem instantiate_succEquation : PRA ⊢ ∀ e x,
    eval[Formula.instantiate.code](pair(${num language},
      pair(succEquation(e, ${num 1}), x))) =
      succEquation(e, NumShift.shiftZeroCode(x)) := by
  pintro e x
  ptrans eval[Formula.instantiate.code](pair(${num language},
    pair(succEquation(e, succ(zero)), x)))
  · prw [num_one]
  · papply Substitution.instantiate_succ_equation_inner[${num language}, e, x]
    pexact Evaluation.symm _ _ eval_language_code

fol_theorem instantiate_succEquation_numCode : PRA ⊢ ∀ e n,
    eval[Formula.instantiate.code](pair(${num language},
      pair(succEquation(e, ${num 1}), NumShift.numCode(n)))) =
      succEquation(e, NumShift.numCode(n)) := by
  pintro e n
  ptrans succEquation(e, NumShift.shiftZeroCode(NumShift.numCode(n)))
  · pexact instantiate_succEquation[e, NumShift.numCode(n)]
  · phave h : NumShift.shiftZeroCode(NumShift.numCode(n)) = NumShift.numCode(n)
    · pexact NumShift.shift_num[n]
    prw [h]

/-! ### Constant language input -/

theorem eval_const_language :
    (PRA ⊢ eval[Primrec.Code.const language](zero) = ${num language}) :=
  Evaluation.constant_value language fol_term[PRA | zero]

/-! ## Equation completeness -/

/-! ### Definitions and shared rules

For a program `e`, a proof program `q` takes an input and returns a Hilbert proof number. The
formula `provesEval` says that every returned proof is a Hilbert proof in PRA of the evaluation
equation on `num`. An `EquationProofPair` pairs `q` with a Hilbert proof of `provesEval`.
-/

fol_def syntaxLanguage over PRA : term := eval[Primrec.Code.const language](zero)

fol_def evalSymbolAtLanguage over PRA : term of 1 := fun e =>
  eval[Language.functionFamilyMember.code](pair(syntaxLanguage(), pair(zero, e)))

fol_def evalEquationNum over PRA : term of 3 := fun e x y =>
  eval[Formula.equal.code](pair(syntaxLanguage(), pair(
    eval[Term.app.code](pair(syntaxLanguage(), pair(evalSymbolAtLanguage(e),
      NumShift.numCode(x)))),
    NumShift.numCode(y))))

fol_def praIsProof over PRA : term of 1 := fun p =>
  eval[FOL.isProof.code language isAxiom.code](p)

theorem praIsProof_on_num (p : Nat) :
    FOL.isProof language isAxiom p = 1 → (PRA ⊢ praIsProof(${num p}) = succ(zero)) := by
  intro accepted
  have computes := FOL.isProof.computedBy language isAxiom.code isAxiom isAxiom.trace
    isAxiom.computedBy p
  have unary := eval_num_of_evaluates (FOL.isProof.code language isAxiom.code) p
    (FOL.isProof language isAxiom p)
    (FOL.isProof.trace language isAxiom.code isAxiom isAxiom.trace p) computes
  rw [accepted, num_succ 0, num_zero] at unary
  exact unary

namespace EquationCompleteness

fol_def equationProofOf over PRA (e : Nat) : term → term → term → formula := fun x y p =>
  (proofOf language isAxiom.code (evalEquationNum(${num e}, x, y)) p)

fol_def provesEval over PRA (e q : Nat) : formula :=
  ∀ x, equationProofOf e x eval[e](x) eval[q](x)

fol_theorem equationProofOf_of_eq (e : Nat) : PRA ⊢ ∀ x y p u v r,
    x = u → y = v → p = r →
    equationProofOf e u v r → equationProofOf e x y p := by
  pintro x y p u v r hx hy hp h
  psubst hx
  psubst hy
  psubst hp
  passumption

fol_theorem pr_evalEquationNum_of_provesEval (e q : Nat) : PRA ⊢ (provesEval e q) →
    ∀ x y, eval[e](x) = y →
      (pr language isAxiom.code (evalEquationNum(${num e}, x, y))) := by
  pintro hq x y value
  phave result : y = eval[e](x)
  · psymm
    pexact value
  psubst result
  papply (pr_of_proofOf language isAxiom.code)[
    evalEquationNum(${num e}, x, eval[e](x)), eval[q](x)]
  pexact hq[x]

fol_theorem provesEval_rec_of_rules (f g qf qg base step : Nat) : PRA ⊢
    (provesEval f qf) →
    (provesEval g qg) →
    (∀ x, equationProofOf f x eval[f](x) eval[qf](x) →
      equationProofOf (Primrec.Code.rec f g) pair(x, zero) eval[f](x) eval[base](x)) →
    (∀ x n p, (equationProofOf (Primrec.Code.rec f g) pair(x, n)
        eval[Primrec.Code.rec f g](pair(x, n)) p) →
      (equationProofOf g pair(x, pair(n, eval[Primrec.Code.rec f g](pair(x, n))))
        eval[g](pair(x, pair(n, eval[Primrec.Code.rec f g](pair(x, n)))))
        eval[qg](pair(x, pair(n, eval[Primrec.Code.rec f g](pair(x, n)))))) →
      (equationProofOf (Primrec.Code.rec f g) pair(x, succ(n))
        eval[g](pair(x, pair(n, eval[Primrec.Code.rec f g](pair(x, n)))))
        eval[step](pair(x, pair(n, p))))) →
    (provesEval (Primrec.Code.rec f g) (Primrec.Code.rec base step)) := by
  pintro fProves gProves baseRule stepRule
  phave atPair : ∀ x n, (equationProofOf (Primrec.Code.rec f g) pair(x, n)
      eval[Primrec.Code.rec f g](pair(x, n)) eval[Primrec.Code.rec base step](pair(x, n)))
  · pintro x n
    pinduction n with
    | zero =>
      papply (equationProofOf_of_eq (Primrec.Code.rec f g))[pair(x, zero),
        eval[Primrec.Code.rec f g](pair(x, zero)),
        eval[Primrec.Code.rec base step](pair(x, zero)),
        pair(x, zero), eval[f](x), eval[base](x)]
      · prefl
      · pexact (PRA.eval_rec_zero f g)[x]
      · pexact (PRA.eval_rec_zero base step)[x]
      · papply baseRule[x]
        pexact fProves[x]
    | succ i prev =>
      papply (equationProofOf_of_eq (Primrec.Code.rec f g))[pair(x, succ(i)),
        eval[Primrec.Code.rec f g](pair(x, succ(i))),
        eval[Primrec.Code.rec base step](pair(x, succ(i))), pair(x, succ(i)),
        eval[g](pair(x, pair(i, eval[Primrec.Code.rec f g](pair(x, i))))),
        eval[step](pair(x, pair(i, eval[Primrec.Code.rec base step](pair(x, i)))))]
      · prefl
      · pexact (PRA.eval_rec_succ f g)[x, i]
      · pexact (PRA.eval_rec_succ base step)[x, i]
      · papply stepRule[x, i, eval[Primrec.Code.rec base step](pair(x, i))]
        · pexact prev
        · pexact gProves[pair(x, pair(i, eval[Primrec.Code.rec f g](pair(x, i))))]
  pintro v
  papply (equationProofOf_of_eq (Primrec.Code.rec f g))[v, eval[Primrec.Code.rec f g](v),
    eval[Primrec.Code.rec base step](v), pair(eval[Primrec.Code.left](v),
      eval[Primrec.Code.right](v)),
    eval[Primrec.Code.rec f g](pair(eval[Primrec.Code.left](v), eval[Primrec.Code.right](v))),
    eval[Primrec.Code.rec base step](pair(eval[Primrec.Code.left](v), eval[Primrec.Code.right](v)))]
  · psymm
    pexact PRA.pair_eval_left_right[v]
  · pcongr
    psymm
    pexact PRA.pair_eval_left_right[v]
  · pcongr
    psymm
    pexact PRA.pair_eval_left_right[v]
  · pexact atPair[eval[Primrec.Code.left](v), eval[Primrec.Code.right](v)]

/-- In `pair q p`, the Hilbert proof `p` proves that `q` constructs a proof of the evaluation
equation on `num` at every input. Verifying `p` and reading its conclusion give a quantifier-free
test for induction. -/
def EquationProofPair : Nat → Nat → QFProp := fun e c =>
  IsProofOf language isAxiom (provesEval e (unpairLeft c)) (unpairRight c)

theorem equationProofPair_pair (e q p : Nat) :
    IsProofOf language isAxiom (provesEval e q) p → EquationProofPair e (pair q p) := by
  intro h
  rw [EquationProofPair, unpairLeft_pair, unpairRight_pair]
  exact h

theorem pr_evalEquationNum_of_pair (e c : Nat) : EquationProofPair e c →
    (PRA ⊢ ∀ x y, eval[e](x) = y →
      (pr language isAxiom.code (evalEquationNum(${num e}, x, y)))) := by
  intro h
  exact Provable.mp language isAxiom _ _ (pr_evalEquationNum_of_provesEval e (unpairLeft c))
    (unpairRight c, h)

def isEquationProofPair : Nat → Nat → Nat := fun e c =>
  let a := provesEval e (unpairLeft c);
  let p := unpairRight c;
  band (eqb (FOL.isProof language isAxiom p) 1) (eqb (Proof.conclusion p) a)

theorem isEquationProofPair_iff : ∀ e c,
    ¬ isEquationProofPair e c = 0 ↔ EquationProofPair e c := by
  intro e c
  let a := provesEval e (unpairLeft c)
  let p := unpairRight c
  let k := eqb (FOL.isProof language isAxiom p) 1
  let v := eqb (Proof.conclusion p) a
  have b := bool_eq_one (band k v) (band_bool k v)
  exact iff_trans (and_right b, and_left b) (iff_trans (band_eq_one k v)
    (and_congr (eqb_ne_zero (FOL.isProof language isAxiom p) 1) (eqb_ne_zero
      (Proof.conclusion p) a)))

fol_theorem constant_value (n : Nat) : PRA ⊢ ∀ x, eval[Primrec.Code.const n](x) = ${num n} := by
  repeat rw [Substitution.shift_num]
  exact FOL.Provable.gen language isAxiom
    (Formula.equal language fol_term[PRA | eval[Primrec.Code.const n](${Term.var language 0})]
      (num n)) (Evaluation.constant_value n (Term.var language 0))

def syntaxLanguageProgram : Nat :=
  Primrec.Code.comp (Primrec.Code.const language) Primrec.Code.zero

def numAtProgram (e : Nat) : Nat := Primrec.Code.comp num.code e

fol_theorem num_at_program_value (e : Nat) : PRA ⊢ ∀ x,
    eval[numAtProgram e](x) = NumShift.numCode(eval[e](x)) := by
  rw [numAtProgram]
  pintro x
  pexact (PRA.eval_comp num.code e)[x]

def applicationProgram (symbol arg : Nat) : Nat :=
  Primrec.Code.comp Term.app.code
    (Primrec.Code.pair syntaxLanguageProgram (Primrec.Code.pair symbol arg))

def equationProgram (lhs rhs : Nat) : Nat :=
  Primrec.Code.comp Formula.equal.code
    (Primrec.Code.pair syntaxLanguageProgram (Primrec.Code.pair lhs rhs))

fol_theorem eval_comp_pair (f g h : Nat) : PRA ⊢ ∀ x,
    eval[Primrec.Code.comp f (Primrec.Code.pair g h)](x) =
      eval[f](pair(eval[g](x), eval[h](x))) := by
  pintro x
  ptrans eval[f](eval[Primrec.Code.pair g h](x))
  · pexact (PRA.eval_comp f (Primrec.Code.pair g h))[x]
  · pcongr
    pexact (PRA.eval_pair g h)[x]

fol_theorem language_program_value : PRA ⊢ ∀ x,
    eval[syntaxLanguageProgram](x) = syntaxLanguage() := by
  have code : syntaxLanguageProgram =
      Primrec.Code.comp (Primrec.Code.const language) Primrec.Code.zero := rfl
  rw [code]
  pintro x
  ptrans eval[Primrec.Code.const language](eval[Primrec.Code.zero](x))
  · pexact (PRA.eval_comp (Primrec.Code.const language) Primrec.Code.zero)[x]
  · prw [PRA.eval_zero]

fol_theorem application_program_value (symbol arg : Nat) : PRA ⊢ ∀ x,
    eval[applicationProgram symbol arg](x) =
      eval[Term.app.code](pair(syntaxLanguage(), pair(eval[symbol](x), eval[arg](x)))) := by
  have code : applicationProgram symbol arg =
      Primrec.Code.comp Term.app.code
        (Primrec.Code.pair syntaxLanguageProgram (Primrec.Code.pair symbol arg)) := rfl
  rw [code]
  pintro x
  ptrans eval[Term.app.code](pair(eval[syntaxLanguageProgram](x),
    eval[Primrec.Code.pair symbol arg](x)))
  · pexact (eval_comp_pair Term.app.code syntaxLanguageProgram (Primrec.Code.pair symbol arg))[x]
  · prw [language_program_value, PRA.eval_pair symbol arg]

fol_theorem equation_program_value (lhs rhs : Nat) : PRA ⊢ ∀ x,
    eval[equationProgram lhs rhs](x) =
      eval[Formula.equal.code](pair(syntaxLanguage(), pair(eval[lhs](x), eval[rhs](x)))) := by
  have code : equationProgram lhs rhs =
      Primrec.Code.comp Formula.equal.code
        (Primrec.Code.pair syntaxLanguageProgram (Primrec.Code.pair lhs rhs)) := rfl
  rw [code]
  pintro x
  ptrans eval[Formula.equal.code](pair(eval[syntaxLanguageProgram](x),
    eval[Primrec.Code.pair lhs rhs](x)))
  · pexact (eval_comp_pair Formula.equal.code syntaxLanguageProgram (Primrec.Code.pair lhs rhs))[x]
  · prw [language_program_value, PRA.eval_pair lhs rhs]

def instanceUniversalProgram (allBody : Nat) : Nat :=
  Primrec.Code.comp Formula.all.code (Primrec.Code.const allBody)

def instanceImplicationProgram (result allBody : Nat) : Nat :=
  Primrec.Code.comp Formula.imp.code
    (Primrec.Code.pair (instanceUniversalProgram allBody) result)

def instanceAxiomProgram (result allBody : Nat) : Nat :=
  Primrec.Code.comp Proof.axiom.code (instanceImplicationProgram result allBody)

def instanceProofProgram (result allBody p : Nat) : Nat :=
  Primrec.Code.comp Proof.mp.code (Primrec.Code.pair result
    (Primrec.Code.pair (instanceAxiomProgram result allBody) (Primrec.Code.const p)))

fol_theorem instance_universal_value (allBody : Nat) : PRA ⊢ ∀ x,
    eval[instanceUniversalProgram allBody](x) = eval[Formula.all.code](${num allBody}) := by
  have code : instanceUniversalProgram allBody =
      Primrec.Code.comp Formula.all.code (Primrec.Code.const allBody) := rfl
  rw [code]
  pintro x
  ptrans eval[Formula.all.code](eval[Primrec.Code.const allBody](x))
  · pexact (PRA.eval_comp Formula.all.code (Primrec.Code.const allBody))[x]
  · prw [constant_value allBody]

fol_theorem instance_implication_value (result allBody : Nat) : PRA ⊢ ∀ x,
    eval[instanceImplicationProgram result allBody](x) =
      eval[Formula.imp.code](pair(eval[Formula.all.code](${num allBody}), eval[result](x))) := by
  have code : instanceImplicationProgram result allBody =
      Primrec.Code.comp Formula.imp.code
        (Primrec.Code.pair (instanceUniversalProgram allBody) result) := rfl
  rw [code]
  pintro x
  ptrans eval[Formula.imp.code](pair(eval[instanceUniversalProgram allBody](x), eval[result](x)))
  · pexact (eval_comp_pair Formula.imp.code (instanceUniversalProgram allBody) result)[x]
  · prw [instance_universal_value allBody]

fol_theorem instance_axiom_value (result allBody : Nat) : PRA ⊢ ∀ x,
    eval[instanceAxiomProgram result allBody](x) =
      eval[Proof.axiom.code](eval[Formula.imp.code](pair(
        eval[Formula.all.code](${num allBody}), eval[result](x)))) := by
  have code : instanceAxiomProgram result allBody =
      Primrec.Code.comp Proof.axiom.code (instanceImplicationProgram result allBody) := rfl
  rw [code]
  pintro x
  ptrans eval[Proof.axiom.code](eval[instanceImplicationProgram result allBody](x))
  · pexact (PRA.eval_comp Proof.axiom.code (instanceImplicationProgram result allBody))[x]
  · prw [instance_implication_value result allBody]

fol_def instanceProofAt over PRA (allBody p : Nat) : term of 1 := fun result =>
  eval[Proof.mp.code](pair(result, pair(eval[Proof.axiom.code](eval[Formula.imp.code](pair(
    eval[Formula.all.code](${num allBody}), result))), ${num p})))

fol_theorem instance_program (result allBody p : Nat) : PRA ⊢ ∀ x,
    eval[instanceProofProgram result allBody p](x) =
      (instanceProofAt allBody p)(eval[result](x)) := by
  have code : instanceProofProgram result allBody p =
      Primrec.Code.comp Proof.mp.code (Primrec.Code.pair result
        (Primrec.Code.pair (instanceAxiomProgram result allBody) (Primrec.Code.const p))) := rfl
  rw [code]
  pintro x
  ptrans eval[Proof.mp.code](pair(eval[result](x),
    eval[Primrec.Code.pair (instanceAxiomProgram result allBody) (Primrec.Code.const p)](x)))
  · pexact (eval_comp_pair Proof.mp.code result
      (Primrec.Code.pair (instanceAxiomProgram result allBody) (Primrec.Code.const p)))[x]
  · prw [PRA.eval_pair (instanceAxiomProgram result allBody) (Primrec.Code.const p),
      instance_axiom_value result allBody, constant_value p]

def symbolProgram (e : Nat) : Nat :=
  Primrec.Code.comp Language.functionFamilyMember.code
    (Primrec.Code.pair syntaxLanguageProgram
      (Primrec.Code.pair Primrec.Code.zero (Primrec.Code.const e)))

fol_theorem symbol_program_value (e : Nat) : PRA ⊢ ∀ x,
    eval[symbolProgram e](x) = evalSymbolAtLanguage(${num e}) := by
  have code : symbolProgram e =
      Primrec.Code.comp Language.functionFamilyMember.code
        (Primrec.Code.pair syntaxLanguageProgram
          (Primrec.Code.pair Primrec.Code.zero (Primrec.Code.const e))) := rfl
  rw [code]
  pintro x
  ptrans eval[Language.functionFamilyMember.code](pair(eval[syntaxLanguageProgram](x),
    eval[Primrec.Code.pair Primrec.Code.zero (Primrec.Code.const e)](x)))
  · pexact (eval_comp_pair Language.functionFamilyMember.code syntaxLanguageProgram
      (Primrec.Code.pair Primrec.Code.zero (Primrec.Code.const e)))[x]
  · prw [language_program_value,
      PRA.eval_pair Primrec.Code.zero (Primrec.Code.const e),
      PRA.eval_zero, constant_value e]

theorem ternary_value (program l u v y trace : Nat) :
    Primrec.Computation.Evaluates program (pair l (pair u v)) y trace →
    (PRA ⊢ eval[program](pair(${num l}, pair(${num u}, ${num v}))) = ${num y}) := by
  intro evals
  have h := Evaluation.congr_eval program _ _
    (Evaluation.congr_pair _ _ _ _ (Evaluation.refl (num l)) (pair_num u v))
  exact Evaluation.trans _ _ _ h
    (eval_pair_num_of_evaluates program l (pair u v) y trace evals)

theorem app_value (j v : Nat) :
    (PRA ⊢ eval[Term.app.code](pair(${num language}, pair(${num j}, ${num v}))) =
      ${num (Term.app language j v)}) := by
  let x := pair language (pair j v)
  have h := Term.app.computedBy x
  rw [unpairLeft_pair, unpairRight_pair, unpairLeft_pair, unpairRight_pair] at h
  exact ternary_value Term.app.code language j v _ (Term.app.trace x) h

theorem symbol_value (e : Nat) :
    (PRA ⊢ evalSymbol(${num e}) = ${num (Language.functionFamilyMember language 0 e)}) := by
  let x := pair language (pair 0 e)
  have h := Language.functionFamilyMember.computedBy x
  rw [unpairLeft_pair, unpairRight_pair, unpairLeft_pair, unpairRight_pair] at h
  have result := ternary_value Language.functionFamilyMember.code language 0 e _
    (Language.functionFamilyMember.trace x) h
  rw [num_zero] at result
  exact result

theorem equal_value (u v : Nat) :
    (PRA ⊢ eval[Formula.equal.code](pair(${num language}, pair(${num u}, ${num v}))) =
      ${num (Formula.equal language u v)}) := by
  let x := pair language (pair u v)
  have h := Formula.equal.computedBy x
  rw [unpairLeft_pair, unpairRight_pair, unpairLeft_pair, unpairRight_pair] at h
  exact ternary_value Formula.equal.code language u v _ (Formula.equal.trace x) h

end EquationCompleteness

/-! #### Equality rules inside the proof predicate -/

namespace EqualityRules

def applyOne : Nat → Nat → Nat → Nat := fun A B p =>
  Proof.mp B (Proof.axiom (Formula.imp A B)) p

def applyTwo : Nat → Nat → Nat → Nat → Nat → Nat := fun A B C p q =>
  Proof.mp C (applyOne A (Formula.imp B C) p) q

derive_primrec applyOne applyTwo

theorem isProofOf_applyOne (L : Nat) (T : Nat → Nat) : ∀ A B p,
    isLogicalAxiom L (Formula.imp A B) = 1 →
    IsProofOf L T A p → IsProofOf L T B (applyOne A B p) := by
  intro A B p h hp
  have leaf : IsProofOf L T (Formula.imp A B) (Proof.axiom (Formula.imp A B)) :=
    (isProof_axiom L T _ h, Proof.conclusion_axiom _)
  exact IsProofOf.mp L T A B _ p leaf hp

derive_fol_pra (public := true) isProofOf_applyOne as applyOne_accepted

theorem isProofOf_applyTwo (L : Nat) (T : Nat → Nat) : ∀ A B C p q,
    isLogicalAxiom L (Formula.imp A (Formula.imp B C)) = 1 →
    IsProofOf L T A p → IsProofOf L T B q → IsProofOf L T C (applyTwo A B C p q) := by
  intro A B C p q h hp hq
  exact IsProofOf.mp L T B C _ q (isProofOf_applyOne L T A (Formula.imp B C) p h hp) hq

derive_fol_pra (public := true) isProofOf_applyTwo as applyTwo_accepted

theorem isProofOf_transitivity (L : Nat) (T : Nat → Nat) : ∀ a b c p q,
    IsProofOf L T (Formula.equal L a b) p → IsProofOf L T (Formula.equal L b c) q →
    IsProofOf L T (Formula.equal L a c) (applyTwo (Formula.equal L a b) (Formula.equal L b c)
      (Formula.equal L a c) p q) := by
  intro a b c p q hp hq
  exact isProofOf_applyTwo L T _ _ _ p q (isLogicalAxiom_of_transitivity L a b c) hp hq

derive_fol_pra (public := true) isProofOf_transitivity as transitivity_accepted

theorem isProofOf_symmetry (L : Nat) (T : Nat → Nat) : ∀ a b p,
    IsProofOf L T (Formula.equal L a b) p →
    IsProofOf L T (Formula.equal L b a) (applyOne (Formula.equal L a b) (Formula.equal L b a) p) :=
  fun a b p h => isProofOf_applyOne L T _ _ p (isLogicalAxiom_of_symmetry L a b) h

derive_fol_pra (public := true) isProofOf_symmetry as symmetry_accepted

theorem congruence_unary : ∀ L j x y,
    Language.IsFunction L j →
    Language.functionSymbolArity L j = 1 →
    isLogicalAxiom L (Formula.imp (Formula.equal L x y)
      (Formula.equal L (Term.app L j x) (Term.app L j y))) = 1 := by
  intro L j x y hj arity
  have accepted := isLogicalAxiom_of_functionCongruence L j x y hj
  rw [arity, Formula.equalPremises_one] at accepted
  exact accepted

theorem congruence_binary : ∀ L j x y u v,
    Language.IsFunction L j →
    Language.functionSymbolArity L j = 2 →
    isLogicalAxiom L (Formula.imp (Formula.equal L x u) (Formula.imp (Formula.equal L y v)
      (Formula.equal L (Term.app L j (pair x y)) (Term.app L j (pair u v))))) = 1 := by
  intro L j x y u v hj arity
  have accepted := isLogicalAxiom_of_functionCongruence L j (pair x y) (pair u v) hj
  rw [arity, Formula.equalPremises_two] at accepted
  exact accepted

theorem program_symbol_of_count : ∀ L e, Language.functionFamilyCount L = 1 →
    Language.IsFunction L (Language.functionFamilyMember L 0 e) := by
  intro L e indexed
  apply Language.isFunction_familyMember
  rw [indexed]
  exact lt_succ_self 0

theorem successor_symbol_of_count : ∀ L, Language.functionCount L = 2 →
    Language.IsFunction L 0 := by
  intro L ordinary
  apply Language.isFunction_of_lt
  rw [ordinary]
  rfl

theorem pair_symbol_of_count : ∀ L, Language.functionCount L = 2 →
    Language.IsFunction L 1 := by
  intro L ordinary
  apply Language.isFunction_of_lt
  rw [ordinary]
  rfl

derive_fol_pra pair_symbol_of_count as pair_symbol_of_count_inner

derive_fol_pra program_symbol_of_count as program_symbol_of_count_inner

derive_fol_pra congruence_unary as congruence_unary_inner

derive_fol_pra congruence_binary as congruence_binary_inner

fol_def equalityCode over PRA : term of 3 := fun L a b =>
  eval[Formula.equal.code](pair(L, pair(a, b)))

fol_def applicationCode over PRA : term of 3 := fun L j a =>
  eval[Term.app.code](pair(L, pair(j, a)))

fol_def unaryAxiomCode over PRA : term of 4 := fun L j a b =>
  eval[Formula.imp.code](pair(equalityCode(L, a, b),
    equalityCode(L, applicationCode(L, j, a), applicationCode(L, j, b))))

fol_def binaryAxiomCode over PRA : term of 6 := fun L j a b c d =>
  eval[Formula.imp.code](pair(equalityCode(L, a, c),
    eval[Formula.imp.code](pair(equalityCode(L, b, d), equalityCode(L,
      applicationCode(L, j, eval[pair.code](pair(a, b))),
      applicationCode(L, j, eval[pair.code](pair(c, d))))))))

fol_theorem pair_slot_arity : PRA ⊢
    eval[Language.functionSymbolArity.code](pair(syntaxLanguage(), succ(zero))) =
      succ(succ(zero)) := by
  ptrans eval[Language.functionSymbolArity.code](pair(${num language}, succ(zero)))
  · prw [eval_const_language]
  · let x := pair language 1
    have calculation := Language.functionSymbolArity.computedBy x
    rw [unpairLeft_pair, unpairRight_pair, FOL.PRA.pair_arity] at calculation
    have h := eval_pair_num_of_evaluates Language.functionSymbolArity.code language 1 2
      (Language.functionSymbolArity.trace x) calculation
    rw [num_succ 1, num_succ 0, num_zero] at h
    exact h

fol_theorem program_congruence_axiom : PRA ⊢ ∀ e a b,
    eval[FOL.isLogicalAxiom.code](pair(syntaxLanguage(),
      unaryAxiomCode(syntaxLanguage(), evalSymbolAtLanguage(e), a, b))) = succ(zero) := by
  pintro e a b
  papply congruence_unary_inner[syntaxLanguage(), evalSymbolAtLanguage(e), a, b]
  · papply program_symbol_of_count_inner[syntaxLanguage(), e]
    ptrans eval[Language.functionFamilyCount.code](${num language})
    · prw [eval_const_language]
    · pexact eval_functionFamilyCount_language
  · ptrans eval[Language.functionSymbolArity.code](pair(${num language}, evalSymbol(e)))
    · prw [eval_const_language]
    · pcases eval_application_fields[e, a] with ⟨_, _, arityEq⟩
      pexact arityEq

fol_theorem pair_congruence_axiom : PRA ⊢ ∀ a b c d,
    eval[FOL.isLogicalAxiom.code](pair(syntaxLanguage(), binaryAxiomCode(syntaxLanguage(),
      succ(zero), a, b, c, d))) = succ(zero) := by
  pintro a b c d
  papply congruence_binary_inner[syntaxLanguage(), succ(zero), a, b, c, d]
  · papply pair_symbol_of_count_inner[syntaxLanguage()]
    ptrans eval[Language.functionCount.code](${num language})
    · prw [eval_const_language]
    · pexact eval_functionCount_language
  · pexact pair_slot_arity

derive_fol_pra successor_symbol_of_count as successor_symbol_of_count_inner

fol_theorem successor_symbol_arity : PRA ⊢
    eval[Language.functionSymbolArity.code](pair(syntaxLanguage(), zero)) = succ(zero) := by
  ptrans eval[Language.functionSymbolArity.code](pair(${num language}, zero))
  · prw [eval_const_language]
  · let x := pair language 0
    have calculation := Language.functionSymbolArity.computedBy x
    rw [unpairLeft_pair, unpairRight_pair, FOL.PRA.succ_arity] at calculation
    have h := eval_pair_num_of_evaluates Language.functionSymbolArity.code language 0 1
      (Language.functionSymbolArity.trace x) calculation
    rw [num_succ 0, num_zero] at h
    exact h

fol_theorem successor_congruence_axiom : PRA ⊢ ∀ a b,
    eval[FOL.isLogicalAxiom.code](pair(syntaxLanguage(),
      unaryAxiomCode(syntaxLanguage(), zero, a, b))) = succ(zero) := by
  pintro a b
  papply congruence_unary_inner[syntaxLanguage(), zero, a, b]
  · papply successor_symbol_of_count_inner[syntaxLanguage()]
    ptrans eval[Language.functionCount.code](${num language})
    · prw [eval_const_language]
    · pexact eval_functionCount_language
  · pexact successor_symbol_arity

end EqualityRules

/-! ### Zero -/

namespace EquationCompleteness.Zero

theorem zero_symbol : (PRA ⊢ evalSymbol(${num Primrec.Code.zero}) = ${num 2}) := by
  have h := symbol_value Primrec.Code.zero
  rw [functionFamilyMember_zero_language] at h
  exact h

def evaluationEquation : Nat → Nat := fun t =>
  Formula.equal language
    (Term.app language (Language.functionFamilyMember language 0 Primrec.Code.zero) t)
    (Term.const language 0)

def body : Nat := evaluationEquation (Term.var language 0)

derive_primrec evaluationEquation body

theorem body_instantiates : ∀ t, Formula.instantiate language body t =
    Formula.equal language (Term.app language 2 (Term.shift language 0 t)) 0 := by
  intro t
  rw [body, evaluationEquation, Substitution.instantiate_eq_substWithDepth,
    Substitution.substWithDepth_equal, Substitution.subst_eval, Substitution.subst_var_self,
    Substitution.subst_const_zero, const_zero_language, functionFamilyMember_zero_language]

derive_fol_pra body_instantiates as body_instantiates_inner

fol_theorem universal : PRA ⊢ ∀ x, eval[Primrec.Code.zero](x) = zero := by
  pexact PRA.eval_zero

extract_witness universal

fol_theorem body_instantiate : PRA ⊢ ∀ t,
    eval[Formula.instantiate.code](pair(${num language}, pair(${num body}, t))) =
      eval[Formula.equal.code](pair(${num language},
        pair(eval[Term.app.code](pair(${num language}, pair(${num 2},
          eval[Term.shift.code](pair(${num language}, pair(zero, t)))))), zero))) := by
  have bodyEq := eval_num_of_evaluates body.code 0 body (body.trace 0) (body.computedBy 0)
  rw [num_zero] at bodyEq
  pintro t
  ptrans eval[Formula.equal.code](pair(eval[language.code](zero),
    pair(eval[Term.app.code](pair(eval[language.code](zero),
      pair(succ(succ(zero)), eval[Term.shift.code](pair(eval[language.code](zero),
        pair(zero, t)))))), zero)))
  · ptrans eval[Formula.instantiate.code](pair(eval[language.code](zero),
      pair(eval[body.code](zero), t)))
    · prw [eval_language_code, bodyEq]
    · pexact body_instantiates_inner[t]
  · prw [eval_language_code, num_succ_eq 1, num_one]

fol_def zeroEquationAt over PRA : term of 1 := fun x =>
  eval[Formula.equal.code](pair(${num language},
    pair(eval[Term.app.code](pair(${num language}, pair(${num 2}, x))), zero)))

fol_theorem substitution_at_num : PRA ⊢ ∀ n,
    eval[Formula.instantiate.code](pair(${num language},
      pair(${num body}, NumShift.numCode(n)))) =
        zeroEquationAt(NumShift.numCode(n)) := by
  pintro n
  ptrans zeroEquationAt(NumShift.shiftZeroCode(NumShift.numCode(n)))
  · pexact body_instantiate[NumShift.numCode(n)]
  · phave h : NumShift.shiftZeroCode(NumShift.numCode(n)) = NumShift.numCode(n)
    · pexact NumShift.shift_num[n]
    prw [h]

theorem equation_all_code :
    (PRA ⊢ eval[Formula.all.code](${num body}) = ${num (Formula.all body)}) :=
  eval_num_of_evaluates Formula.all.code body (Formula.all body)
    (Formula.all.trace body) (Formula.all.computedBy body)

fol_def zeroEquationIn over PRA : term of 2 := fun l x =>
  eval[Formula.equal.code](pair(l, pair(eval[Term.app.code](pair(l, pair(${num 2}, x))), zero)))

theorem universal_accepted :
    (PRA ⊢ praIsProof(${num universal.witness}) = succ(zero)) := by
  let p := universal.witness
  have h : IsProofOf language isAxiom (Formula.all body) p := universal.witness_correct
  exact praIsProof_on_num p (and_left h)

theorem universal_concludes :
    (PRA ⊢ eval[Proof.conclusion.code](${num universal.witness}) =
      ${num (Formula.all body)}) := by
  let p := universal.witness
  have h : IsProofOf language isAxiom (Formula.all body) p := universal.witness_correct
  have result := eval_num_of_evaluates Proof.conclusion.code p (Proof.conclusion p)
    (Proof.conclusion.trace p) (Proof.conclusion.computedBy p)
  rw [and_right h] at result
  exact result

fol_def instantiatedEquation over PRA : term of 1 := fun n =>
  zeroEquationIn(eval[Primrec.Code.const language](zero), NumShift.numCode(n))

fol_theorem instance_accepted : PRA ⊢ ∀ n,
    praIsProof((instanceProofAt body universal.witness)(
      instantiatedEquation(n))) = succ(zero) ∧
    eval[Proof.conclusion.code]((instanceProofAt body universal.witness)(
      instantiatedEquation(n))) = zeroEquationAt(NumShift.numCode(n)) := by
  pintro n
  let p := fol_term[PRA | (instanceProofAt body universal.witness)(
    instantiatedEquation(${n}))]
  phave accepted : praIsProof(${p}) = succ(zero) ∧
    eval[Proof.conclusion.code](${p}) = instantiatedEquation(n)
  · papply (praProofOf_equal_app_of_instantiate language isAxiom.code)[${num body},
      ${num 2}, NumShift.numCode(n), zero, ${num universal.witness}]
    · ptrans eval[Formula.instantiate.code](pair(${num language},
      pair(${num body}, NumShift.numCode(n))))
      · prw [eval_const_language]
      · ptrans zeroEquationAt(NumShift.numCode(n))
        · pexact substitution_at_num[n]
        · prw [eval_const_language]
    · pconstructor
      · pexact universal_accepted
      · ptrans ${num (Formula.all body)}
        · pexact universal_concludes
        · psymm
          pexact equation_all_code
  pcases accepted with ⟨valid, conclusion⟩
  pconstructor
  · pexact valid
  · ptrans instantiatedEquation(n)
    · pexact conclusion
    · prw [eval_const_language]

def zeroResultProgram : Nat :=
  equationProgram (applicationProgram (Primrec.Code.const 2) num.code) Primrec.Code.zero

fol_theorem zero_result_program_value : PRA ⊢ ∀ x,
    eval[zeroResultProgram](x) = instantiatedEquation(x) := by
  have code : zeroResultProgram =
      equationProgram (applicationProgram (Primrec.Code.const 2) num.code)
        Primrec.Code.zero := rfl
  rw [code]
  pintro x
  ptrans eval[Formula.equal.code](pair(syntaxLanguage(),
    pair(eval[applicationProgram (Primrec.Code.const 2) num.code](x),
      eval[Primrec.Code.zero](x))))
  · pexact (equation_program_value
      (applicationProgram (Primrec.Code.const 2) num.code) Primrec.Code.zero)[x]
  · prw [application_program_value (Primrec.Code.const 2) num.code,
      constant_value 2, PRA.eval_zero]

def zeroProofProgram : Nat :=
  instanceProofProgram zeroResultProgram body universal.witness

fol_theorem provesEval_zero : PRA ⊢
    (provesEval Primrec.Code.zero zeroProofProgram) := by
  rw [zeroProofProgram]
  pintro x
  papply (equationProofOf_of_eq Primrec.Code.zero)[x, eval[Primrec.Code.zero](x),
    eval[instanceProofProgram zeroResultProgram body universal.witness](x),
    x, zero, (instanceProofAt body universal.witness)(
      instantiatedEquation(x))]
  · prefl
  · pexact PRA.eval_zero[x]
  · ptrans (instanceProofAt body universal.witness)(eval[zeroResultProgram](x))
    · pexact (instance_program zeroResultProgram body universal.witness)[x]
    · prw [zero_result_program_value]
  · pcases instance_accepted[x] with ⟨accepted, result⟩
    pconstructor
    · pexact accepted
    · ptrans zeroEquationAt(NumShift.numCode(x))
      · pexact result
      · prw [eval_const_language, zero_symbol, eval_num_zero]

end EquationCompleteness.Zero

namespace EquationCompleteness

theorem zero_pair_exists : ∃ c, EquationProofPair Primrec.Code.zero c := by
  rcases Zero.provesEval_zero with (p, hp)
  exact (pair Zero.zeroProofProgram p,
    equationProofPair_pair Primrec.Code.zero Zero.zeroProofProgram p hp)

end EquationCompleteness

/-! ### Successor -/

namespace EquationCompleteness.Successor

def body : Nat :=
  Formula.equal language
    (Term.app language (Language.functionFamilyMember language 0 Primrec.Code.succ)
      (Term.var language 0))
    (Term.app language 0 (Term.var language 0))

fol_theorem universal : PRA ⊢ ∀ x, eval[Primrec.Code.succ](x) = succ(x) := by
  pexact PRA.eval_succ

extract_witness universal

theorem body_value :
    (PRA ⊢ succEquation(${num Primrec.Code.succ}, ${num 1}) = ${num body}) := by
  let v := Term.var language 0
  let j := Language.functionFamilyMember language 0 Primrec.Code.succ
  have varEq : (PRA ⊢ ${num 1} = ${num v}) := by
    psymm
    pexact num_eq_of_eq v 1 var_zero_language
  have leftEq : (PRA ⊢ evalApplication(${num Primrec.Code.succ}, ${num 1}) =
      ${num (Term.app language j v)}) := by
    ptrans eval[Term.app.code](pair(${num language}, pair(${num j}, ${num v})))
    · prw [symbol_value Primrec.Code.succ, varEq]
    · pexact app_value j v
  have rightEq : (PRA ⊢ NumShift.succCode(${num 1}) = ${num
    (Term.app language 0 v)}) := by
    ptrans eval[Term.app.code](pair(${num language}, pair(zero, ${num v})))
    · prw [varEq]
    · have h := app_value 0 v
      rw [num_zero] at h
      pexact h
  ptrans eval[Formula.equal.code](pair(${num language},
      pair(${num (Term.app language j v)}, ${num (Term.app language 0 v)})))
  · prw [leftEq, rightEq]
  · exact equal_value (Term.app language j v) (Term.app language 0 v)

fol_theorem substitution_at_num : PRA ⊢ ∀ n,
    eval[Formula.instantiate.code](pair(${num language},
      pair(${num body}, NumShift.numCode(n)))) =
      succEquation(${num Primrec.Code.succ}, NumShift.numCode(n)) := by
  pintro n
  ptrans eval[Formula.instantiate.code](pair(${num language},
    pair(succEquation(${num Primrec.Code.succ}, ${num 1}),
      NumShift.numCode(n))))
  · prw [body_value]
  · pexact instantiate_succEquation_numCode[${num Primrec.Code.succ}, n]

fol_theorem successor_num_program_value : PRA ⊢ ∀ x,
    eval[Primrec.Code.comp num.code Primrec.Code.succ](x) =
      NumShift.numCode(succ(x)) := by
  pintro x
  ptrans eval[num.code](eval[Primrec.Code.succ](x))
  · pexact (PRA.eval_comp num.code Primrec.Code.succ)[x]
  · prw [PRA.eval_succ]

def successorResultProgram : Nat :=
  equationProgram (applicationProgram (symbolProgram Primrec.Code.succ) num.code)
    (Primrec.Code.comp num.code Primrec.Code.succ)

fol_theorem successor_result_program_value : PRA ⊢ ∀ x,
    eval[successorResultProgram](x) = evalEquationNum(${num Primrec.Code.succ}, x, succ(x)) := by
  have code : successorResultProgram =
      equationProgram (applicationProgram (symbolProgram Primrec.Code.succ) num.code)
        (Primrec.Code.comp num.code Primrec.Code.succ) := rfl
  rw [code]
  pintro x
  ptrans eval[Formula.equal.code](pair(syntaxLanguage(),
    pair(eval[applicationProgram (symbolProgram Primrec.Code.succ) num.code](x),
      eval[Primrec.Code.comp num.code Primrec.Code.succ](x))))
  · pexact (equation_program_value (applicationProgram (symbolProgram Primrec.Code.succ) num.code)
      (Primrec.Code.comp num.code Primrec.Code.succ))[x]
  · prw [application_program_value (symbolProgram Primrec.Code.succ) num.code,
      symbol_program_value Primrec.Code.succ,
      successor_num_program_value]

theorem universal_accepted :
    (PRA ⊢ praIsProof(${num universal.witness}) = succ(zero)) := by
  let p := universal.witness
  have h : IsProofOf language isAxiom (Formula.all body) p := universal.witness_correct
  exact praIsProof_on_num p (and_left h)

theorem universal_concludes :
    (PRA ⊢ eval[Proof.conclusion.code](${num universal.witness}) =
      eval[Formula.all.code](${num body})) := by
  let p := universal.witness
  have h : IsProofOf language isAxiom (Formula.all body) p := universal.witness_correct
  have result := eval_num_of_evaluates Proof.conclusion.code p (Proof.conclusion p)
    (Proof.conclusion.trace p) (Proof.conclusion.computedBy p)
  rw [and_right h] at result
  ptrans ${num (Formula.all body)}
  · exact result
  · psymm
    exact eval_num_of_evaluates Formula.all.code body (Formula.all body)
      (Formula.all.trace body) (Formula.all.computedBy body)

fol_theorem instance_accepted : PRA ⊢ ∀ x,
    (equationProofOf Primrec.Code.succ x succ(x)
      (instanceProofAt body universal.witness)(
        evalEquationNum(${num Primrec.Code.succ}, x, succ(x)))) := by
  pintro x
  papply (praProofOf_equal_app_of_instantiate language isAxiom.code)[${num body},
    evalSymbolAtLanguage(${num Primrec.Code.succ}), NumShift.numCode(x),
    NumShift.numCode(succ(x)), ${num universal.witness}]
  · ptrans eval[Formula.instantiate.code](pair(${num language},
      pair(${num body}, NumShift.numCode(x))))
    · prw [eval_const_language]
    · ptrans succEquation(${num Primrec.Code.succ}, NumShift.numCode(x))
      · pexact substitution_at_num[x]
      · prw [eval_const_language, NumShift.num_succ_code]
  · pconstructor
    · pexact universal_accepted
    · pexact universal_concludes

def succProofProgram : Nat :=
  instanceProofProgram successorResultProgram body universal.witness

fol_theorem provesEval_succ : PRA ⊢
    (provesEval Primrec.Code.succ succProofProgram) := by
  rw [succProofProgram]
  pintro x
  papply (equationProofOf_of_eq Primrec.Code.succ)[x, eval[Primrec.Code.succ](x),
    eval[instanceProofProgram successorResultProgram body universal.witness](x), x, succ(x),
    (instanceProofAt body universal.witness)(
      evalEquationNum(${num Primrec.Code.succ}, x, succ(x)))]
  · prefl
  · pexact PRA.eval_succ[x]
  · ptrans (instanceProofAt body universal.witness)(
      eval[successorResultProgram](x))
    · pexact (instance_program successorResultProgram body universal.witness)[x]
    · prw [successor_result_program_value]
  · pexact instance_accepted[x]

end EquationCompleteness.Successor

namespace EquationCompleteness

theorem succ_pair_exists : ∃ c, EquationProofPair Primrec.Code.succ c := by
  rcases Successor.provesEval_succ with (p, hp)
  exact (pair Successor.succProofProgram p,
    equationProofPair_pair Primrec.Code.succ Successor.succProofProgram p hp)

end EquationCompleteness

/-! ### Composition -/

namespace EquationCompleteness.Composition

open NumShift

fol_def applicationCode over PRA : term of 2 := fun e t =>
  eval[Term.app.code](pair(syntaxLanguage(), pair(evalSymbolAtLanguage(e), t)))

fol_def equalityCode over PRA : term of 2 := fun u v =>
  eval[Formula.equal.code](pair(syntaxLanguage(), pair(u, v)))

fol_def compositionEquation over PRA : term of 4 := fun c f g t =>
  equalityCode(applicationCode(c, t), applicationCode(f, applicationCode(g, t)))

fol_def compositionEquationAt over PRA : term of 4 := fun c f g t =>
  evalEquation(c, t, evalApplication(f, evalApplication(g, t)))

fol_theorem code_at_eq_code : PRA ⊢ ∀ c f g t,
    compositionEquationAt(c, f, g, t) = compositionEquation(c, f, g, t) := by
  pintro c f g t
  prw [eval_const_language]

fol_theorem instantiate_composition_shifted : PRA ⊢ ∀ c f g t,
    eval[Formula.instantiate.code](pair(${num language},
      pair(compositionEquationAt(c, f, g, ${num 1}), t))) =
    compositionEquationAt(c, f, g, shiftZeroCode(t)) := by
  pintro c f g t
  ptrans eval[Formula.instantiate.code](pair(${num language},
    pair(compositionEquationAt(c, f, g, succ(zero)), t)))
  · prw [num_one]
  · papply Substitution.instantiate_comp_equation_inner[${num language}, c, f, g, t]
    pexact Evaluation.symm _ _ eval_language_code

def body (f g : Nat) : Nat :=
  fol_formula[PRA | eval[Primrec.Code.comp f g](${Term.var language 0}) =
    eval[f](eval[g](${Term.var language 0}))]

theorem ternary_value (program l a b y trace : Nat) :
    Primrec.Computation.Evaluates program (pair l (pair a b)) y trace →
    (PRA ⊢ eval[program](pair(${num l}, pair(${num a}, ${num b}))) = ${num y}) := by
  intro evals
  have pack := Evaluation.congr_eval program _ _
    (Evaluation.congr_pair _ _ _ _ (Evaluation.refl (num l)) (pair_num a b))
  exact Evaluation.trans _ _ _ pack
    (eval_pair_num_of_evaluates program l (pair a b) y trace evals)

theorem application_value (e t : Nat) :
    (PRA ⊢ evalApplication(${num e}, ${num t}) =
      ${num (Term.app language (Language.functionFamilyMember language 0 e) t)}) := by
  let j := Language.functionFamilyMember language 0 e
  let symbolInput := pair language (pair 0 e)
  have symbolComputation := Language.functionFamilyMember.computedBy symbolInput
  rw [unpairLeft_pair, unpairRight_pair, unpairLeft_pair, unpairRight_pair] at symbolComputation
  have symbolValue := ternary_value Language.functionFamilyMember.code language 0 e j
    (Language.functionFamilyMember.trace symbolInput) symbolComputation
  rw [num_zero] at symbolValue
  let appInput := pair language (pair j t)
  have appComputation := Term.app.computedBy appInput
  rw [unpairLeft_pair, unpairRight_pair, unpairLeft_pair, unpairRight_pair] at appComputation
  ptrans eval[Term.app.code](pair(${num language}, pair(${num j}, ${num t})))
  · prw [symbolValue]
  · exact ternary_value Term.app.code language j t _
      (Term.app.trace appInput) appComputation

theorem equality_value (u v : Nat) :
    (PRA ⊢ eval[Formula.equal.code](pair(${num language}, pair(${num u}, ${num v}))) =
      ${num (Formula.equal language u v)}) := by
  let input := pair language (pair u v)
  have computation := Formula.equal.computedBy input
  rw [unpairLeft_pair, unpairRight_pair, unpairLeft_pair, unpairRight_pair] at computation
  exact ternary_value Formula.equal.code language u v _ (Formula.equal.trace input) computation

theorem body_value (f g : Nat) :
    (PRA ⊢ compositionEquationAt(${num (Primrec.Code.comp f g)}, ${num f}, ${num g},
      ${num 1}) = ${num (body f g)}) := by
  let v := Term.var language 0
  let app := fun e t => Term.app language (Language.functionFamilyMember language 0 e) t
  let l := app (Primrec.Code.comp f g) v
  let r := app f (app g v)
  have varEq : (PRA ⊢ ${num 1} = ${num v}) :=
    Evaluation.symm _ _ (num_eq_of_eq v 1 var_zero_language)
  have leftEq := application_value (Primrec.Code.comp f g) v
  have inner := application_value g v
  have outer := application_value f (app g v)
  ptrans eval[Formula.equal.code](pair(${num language}, pair(${num l}, ${num r})))
  · prw [varEq, leftEq, inner, outer]
  · exact equality_value l r

fol_theorem substitution_at_num (f g : Nat) : PRA ⊢ ∀ x,
    eval[Formula.instantiate.code](pair(${num language},
      pair(${num (body f g)}, numCode(x)))) =
    compositionEquation(${num (Primrec.Code.comp f g)}, ${num f}, ${num g}, numCode(x)) := by
  pintro x
  ptrans eval[Formula.instantiate.code](pair(${num language}, pair(
    compositionEquationAt(${num (Primrec.Code.comp f g)}, ${num f}, ${num g},
      ${num 1}), numCode(x))))
  · prw [body_value f g]
  · ptrans compositionEquationAt(${num (Primrec.Code.comp f g)}, ${num f}, ${num g},
        shiftZeroCode(numCode(x)))
    · pexact instantiate_composition_shifted[
        ${num (Primrec.Code.comp f g)}, ${num f}, ${num g}, numCode(x)]
    · phave shift : shiftZeroCode(numCode(x)) = numCode(x)
      · pexact shift_num[x]
      prw [shift, code_at_eq_code]

fol_theorem universal (f g : Nat) : PRA ⊢ ∀ x,
    eval[Primrec.Code.comp f g](x) = eval[f](eval[g](x)) := by
  pexact PRA.eval_comp f g

theorem all_body_value (f g : Nat) :
    (PRA ⊢ eval[Formula.all.code](${num (body f g)}) = ${num (Formula.all (body f g))}) :=
  eval_num_of_evaluates Formula.all.code (body f g) (Formula.all (body f g))
    (Formula.all.trace (body f g)) (Formula.all.computedBy (body f g))

extract_witness Composition.universal

fol_def praProofOf over PRA : term → term → formula := fun a p =>
  (proofOf language isAxiom.code a p)

fol_def recognizesCongruence over PRA (f : Nat) : formula :=
  ∀ a b, eval[FOL.isLogicalAxiom.code](pair(syntaxLanguage(),
    eval[Formula.imp.code](pair(equalityCode(a, b),
      equalityCode(applicationCode(${num f}, a), applicationCode(${num f}, b)))))) = succ(zero)

def appProgram (e t : Nat) : Nat := applicationProgram (symbolProgram e) t

fol_theorem app_program_value (e t : Nat) : PRA ⊢ ∀ x,
    eval[appProgram e t](x) = applicationCode(${num e}, eval[t](x)) := by
  have code : appProgram e t = applicationProgram (symbolProgram e) t := rfl
  rw [code]
  pintro x
  ptrans eval[Term.app.code](pair(syntaxLanguage(), pair(eval[symbolProgram e](x), eval[t](x))))
  · pexact (application_program_value (symbolProgram e) t)[x]
  · prw [symbol_program_value e]

def oneProgram (a b p : Nat) : Nat :=
  Primrec.Code.comp EqualityRules.applyOne.code (Primrec.Code.pair a (Primrec.Code.pair b p))

def twoProgram (a b c p q : Nat) : Nat :=
  Primrec.Code.comp EqualityRules.applyTwo.code (Primrec.Code.pair a
    (Primrec.Code.pair b (Primrec.Code.pair c (Primrec.Code.pair p q))))

fol_theorem one_program_value (a b p : Nat) : PRA ⊢ ∀ x,
    eval[oneProgram a b p](x) =
      eval[EqualityRules.applyOne.code](pair(eval[a](x), pair(eval[b](x), eval[p](x)))) := by
  have code : oneProgram a b p =
      Primrec.Code.comp EqualityRules.applyOne.code
        (Primrec.Code.pair a (Primrec.Code.pair b p)) := rfl
  rw [code]
  pintro x
  ptrans eval[EqualityRules.applyOne.code](pair(eval[a](x), eval[Primrec.Code.pair b p](x)))
  · pexact (eval_comp_pair EqualityRules.applyOne.code a (Primrec.Code.pair b p))[x]
  · prw [PRA.eval_pair b p]

fol_theorem two_program_value (a b c p q : Nat) : PRA ⊢ ∀ x,
    eval[twoProgram a b c p q](x) = eval[EqualityRules.applyTwo.code](pair(eval[a](x),
      pair(eval[b](x), pair(eval[c](x), pair(eval[p](x), eval[q](x)))))) := by
  have code : twoProgram a b c p q =
      Primrec.Code.comp EqualityRules.applyTwo.code (Primrec.Code.pair a
        (Primrec.Code.pair b (Primrec.Code.pair c (Primrec.Code.pair p q)))) := rfl
  rw [code]
  pintro x
  ptrans eval[EqualityRules.applyTwo.code](pair(eval[a](x),
    eval[Primrec.Code.pair b (Primrec.Code.pair c (Primrec.Code.pair p q))](x)))
  · pexact (eval_comp_pair EqualityRules.applyTwo.code a
      (Primrec.Code.pair b (Primrec.Code.pair c (Primrec.Code.pair p q))))[x]
  · prw [PRA.eval_pair b (Primrec.Code.pair c (Primrec.Code.pair p q)),
      PRA.eval_pair c (Primrec.Code.pair p q), PRA.eval_pair p q]

fol_def congruenceProof over PRA (e : Nat) : term of 3 := fun a b p =>
  eval[EqualityRules.applyOne.code](pair(equalityCode(a, b),
    pair(equalityCode(applicationCode(${num e}, a), applicationCode(${num e}, b)), p)))

fol_def transitivityProof over PRA : term of 5 := fun a b c p q =>
  eval[EqualityRules.applyTwo.code](pair(equalityCode(a, b),
    pair(equalityCode(b, c), pair(equalityCode(a, c), pair(p, q)))))

def congruenceProgram (e a b p : Nat) : Nat :=
  oneProgram (equationProgram a b) (equationProgram (appProgram e a) (appProgram e b)) p

def transitivityProgram (a b c p q : Nat) : Nat :=
  twoProgram (equationProgram a b) (equationProgram b c) (equationProgram a c) p q

fol_theorem congruence_program_value (e a b p : Nat) : PRA ⊢ ∀ x,
    eval[congruenceProgram e a b p](x) =
      (congruenceProof e)(eval[a](x), eval[b](x), eval[p](x)) := by
  have code : congruenceProgram e a b p = oneProgram (equationProgram a b)
      (equationProgram (appProgram e a) (appProgram e b)) p := rfl
  rw [code]
  pintro x
  ptrans eval[EqualityRules.applyOne.code](pair(eval[equationProgram a b](x),
    pair(eval[equationProgram (appProgram e a) (appProgram e b)](x), eval[p](x))))
  · pexact (one_program_value (equationProgram a b)
      (equationProgram (appProgram e a) (appProgram e b)) p)[x]
  · prw [equation_program_value a b,
      equation_program_value (appProgram e a) (appProgram e b),
      app_program_value e a, app_program_value e b]

fol_theorem transitivity_program_value (a b c p q : Nat) : PRA ⊢ ∀ x,
    eval[transitivityProgram a b c p q](x) =
      transitivityProof(eval[a](x), eval[b](x), eval[c](x), eval[p](x), eval[q](x)) := by
  have code : transitivityProgram a b c p q =
      twoProgram (equationProgram a b) (equationProgram b c) (equationProgram a c) p q := rfl
  rw [code]
  pintro x
  ptrans eval[EqualityRules.applyTwo.code](pair(eval[equationProgram a b](x),
    pair(eval[equationProgram b c](x), pair(eval[equationProgram a c](x),
      pair(eval[p](x), eval[q](x))))))
  · pexact (two_program_value (equationProgram a b) (equationProgram b c)
      (equationProgram a c) p q)[x]
  · prw [equation_program_value a b, equation_program_value b c, equation_program_value a c]

fol_theorem congruence_accepted (e : Nat) : PRA ⊢ (recognizesCongruence e) → ∀ a b p,
    praProofOf equalityCode(a, b) p →
    (praProofOf equalityCode(applicationCode(${num e}, a), applicationCode(${num e}, b))
      (congruenceProof e)(a, b, p)) := by
  pintro recognize a b p hp
  papply (EqualityRules.applyOne_accepted language isAxiom.code)[equalityCode(a, b),
    equalityCode(applicationCode(${num e}, a), applicationCode(${num e}, b)), p]
  · pexact recognize[a, b]
  · pexact hp

fol_theorem transitivity_rule : PRA ⊢ ∀ a b c p q,
    praProofOf equalityCode(a, b) p → praProofOf equalityCode(b, c) q →
    praProofOf equalityCode(a, c) transitivityProof(a, b, c, p, q) := by
  pexact EqualityRules.transitivity_accepted language isAxiom.code

fol_def leftTermAt over PRA (f g : Nat) : term of 1 := fun x =>
  applicationCode(${num (Primrec.Code.comp f g)}, numCode(x))

fol_def innerTermAt over PRA (g : Nat) : term of 1 := fun x =>
  applicationCode(${num g}, numCode(x))

fol_def rightTermAt over PRA (f g : Nat) : term of 1 := fun x =>
  applicationCode(${num f}, (innerTermAt g)(x))

fol_def middleTermAt over PRA (f g : Nat) : term of 1 := fun x =>
  applicationCode(${num f}, numCode(eval[g](x)))

fol_def outputTermAt over PRA (f g : Nat) : term of 1 := fun x =>
  numCode(eval[f](eval[g](x)))

def leftTermProgram (f g : Nat) : Nat := appProgram (Primrec.Code.comp f g) num.code

def innerTermProgram (g : Nat) : Nat := appProgram g num.code

def rightTermProgram (f g : Nat) : Nat := appProgram f (innerTermProgram g)

def innerNumProgram (g : Nat) : Nat := Primrec.Code.comp num.code g

def middleTermProgram (f g : Nat) : Nat := appProgram f (innerNumProgram g)

def outputTermProgram (f g : Nat) : Nat := Primrec.Code.comp (innerNumProgram f) g

fol_theorem left_term_value (f g : Nat) : PRA ⊢ ∀ x,
    eval[leftTermProgram f g](x) = (leftTermAt f g)(x) := by
  have code : leftTermProgram f g = appProgram (Primrec.Code.comp f g) num.code := rfl
  rw [code]
  pintro x
  prw [app_program_value (Primrec.Code.comp f g) num.code]

fol_theorem inner_term_value (g : Nat) : PRA ⊢ ∀ x,
    eval[innerTermProgram g](x) = (innerTermAt g)(x) := by
  have code : innerTermProgram g = appProgram g num.code := rfl
  rw [code]
  pintro x
  prw [app_program_value g num.code]

fol_theorem right_term_value (f g : Nat) : PRA ⊢ ∀ x,
    eval[rightTermProgram f g](x) = (rightTermAt f g)(x) := by
  have code : rightTermProgram f g = appProgram f (innerTermProgram g) := rfl
  rw [code]
  pintro x
  prw [app_program_value f (innerTermProgram g), inner_term_value g]

fol_theorem inner_num_value (g : Nat) : PRA ⊢ ∀ x,
    eval[innerNumProgram g](x) = numCode(eval[g](x)) := by
  have code : innerNumProgram g = Primrec.Code.comp num.code g := rfl
  rw [code]
  pintro x
  prw [PRA.eval_comp num.code g]

fol_theorem middle_term_value (f g : Nat) : PRA ⊢ ∀ x,
    eval[middleTermProgram f g](x) = (middleTermAt f g)(x) := by
  have code : middleTermProgram f g = appProgram f (innerNumProgram g) := rfl
  rw [code]
  pintro x
  prw [app_program_value f (innerNumProgram g), inner_num_value g]

fol_theorem output_term_value (f g : Nat) : PRA ⊢ ∀ x,
    eval[outputTermProgram f g](x) = (outputTermAt f g)(x) := by
  have code : outputTermProgram f g = Primrec.Code.comp (innerNumProgram f) g := rfl
  rw [code]
  pintro x
  prw [PRA.eval_comp (innerNumProgram f) g, inner_num_value f]

fol_def instanceAt over PRA (f g : Nat) : term of 1 := fun x =>
  (instanceProofAt (Composition.body f g) (Composition.universal.witness f g))(
      compositionEquation(${num (Primrec.Code.comp f g)}, ${num f}, ${num g}, numCode(x)))

def instanceProgram (f g : Nat) : Nat :=
  instanceProofProgram (equationProgram (leftTermProgram f g) (rightTermProgram f g))
    (Composition.body f g) (Composition.universal.witness f g)

fol_theorem instance_program_value (f g : Nat) : PRA ⊢ ∀ x,
    eval[instanceProgram f g](x) = (instanceAt f g)(x) := by
  have code : instanceProgram f g =
      instanceProofProgram (equationProgram (leftTermProgram f g) (rightTermProgram f g))
        (Composition.body f g) (Composition.universal.witness f g) := rfl
  rw [code]
  pintro x
  prw [instance_program (equationProgram (leftTermProgram f g) (rightTermProgram f g))
      (Composition.body f g) (Composition.universal.witness f g), equation_program_value
      (leftTermProgram f g) (rightTermProgram f g), left_term_value f g, right_term_value f g]

theorem universal_accepted (f g : Nat) :
    (PRA ⊢ (praProofOf eval[Formula.all.code](${num (Composition.body f g)})
      ${num (Composition.universal.witness f g)})) := by
  let p := Composition.universal.witness f g
  have h : IsProofOf language isAxiom (Formula.all (Composition.body f g)) p :=
    Composition.universal.witness_correct f g
  have valid := praIsProof_on_num p (and_left h)
  have concludes := eval_num_of_evaluates Proof.conclusion.code p (Proof.conclusion p)
    (Proof.conclusion.trace p) (Proof.conclusion.computedBy p)
  rw [and_right h] at concludes
  pconstructor
  · exact valid
  · ptrans ${num (Formula.all (Composition.body f g))}
    · exact concludes
    · psymm
      exact Composition.all_body_value f g

fol_theorem instance_accepted (f g : Nat) : PRA ⊢ ∀ x,
    (praProofOf equalityCode((leftTermAt f g)(x), (rightTermAt f g)(x))
      (instanceAt f g)(x)) := by
  pintro x
  papply (praProofOf_equal_app_of_instantiate language isAxiom.code)[
    ${num (Composition.body f g)}, evalSymbolAtLanguage(${num (Primrec.Code.comp f g)}),
    numCode(x), (rightTermAt f g)(x),
    ${num (Composition.universal.witness f g)}]
  · ptrans eval[Formula.instantiate.code](pair(${num language},
      pair(${num (Composition.body f g)}, numCode(x))))
    · prw [eval_const_language]
    · pexact (Composition.substitution_at_num f g)[x]
  · pexact universal_accepted f g

def liftedProofProgram (f g qg : Nat) : Nat :=
  congruenceProgram f (innerTermProgram g) (innerNumProgram g) qg

def tailProofProgram (f g qf qg : Nat) : Nat :=
  transitivityProgram (rightTermProgram f g) (middleTermProgram f g) (outputTermProgram f g)
    (liftedProofProgram f g qg) (Primrec.Code.comp qf g)

def compProofProgram (f g qf qg : Nat) : Nat :=
  transitivityProgram (leftTermProgram f g) (rightTermProgram f g) (outputTermProgram f g)
    (instanceProgram f g) (tailProofProgram f g qf qg)

fol_def liftedProofAt over PRA (f g qg : Nat) : term of 1 := fun x =>
  (congruenceProof f)((innerTermAt g)(x), numCode(eval[g](x)), eval[qg](x))

fol_def tailProofAt over PRA (f g qf qg : Nat) : term of 1 := fun x =>
  transitivityProof((rightTermAt f g)(x), (middleTermAt f g)(x),
    (outputTermAt f g)(x), (liftedProofAt f g qg)(x),
    eval[qf](eval[g](x)))

fol_def compProofAt over PRA (f g qf qg : Nat) : term of 1 := fun x =>
  transitivityProof((leftTermAt f g)(x), (rightTermAt f g)(x),
    (outputTermAt f g)(x), (instanceAt f g)(x),
    (tailProofAt f g qf qg)(x))

fol_theorem lifted_proof_value (f g qg : Nat) : PRA ⊢ ∀ x,
    eval[liftedProofProgram f g qg](x) = (liftedProofAt f g qg)(x) := by
  have code : liftedProofProgram f g qg =
      congruenceProgram f (innerTermProgram g) (innerNumProgram g) qg := rfl
  rw [code]
  pintro x
  prw [congruence_program_value f (innerTermProgram g) (innerNumProgram g) qg,
    inner_term_value g, inner_num_value g]

fol_theorem tail_proof_value (f g qf qg : Nat) : PRA ⊢ ∀ x,
    eval[tailProofProgram f g qf qg](x) =
      (tailProofAt f g qf qg)(x) := by
  have code : tailProofProgram f g qf qg =
      transitivityProgram (rightTermProgram f g) (middleTermProgram f g) (outputTermProgram f g)
        (liftedProofProgram f g qg) (Primrec.Code.comp qf g) := rfl
  rw [code]
  pintro x
  prw [transitivity_program_value (rightTermProgram f g) (middleTermProgram f g)
      (outputTermProgram f g) (liftedProofProgram f g qg)
      (Primrec.Code.comp qf g), right_term_value f g, middle_term_value f g, output_term_value
      f g, lifted_proof_value f g qg, PRA.eval_comp qf g]

fol_theorem comp_proof_program_value (f g qf qg : Nat) : PRA ⊢ ∀ x,
    eval[compProofProgram f g qf qg](x) =
      (compProofAt f g qf qg)(x) := by
  have code : compProofProgram f g qf qg =
      transitivityProgram (leftTermProgram f g) (rightTermProgram f g) (outputTermProgram f g)
        (instanceProgram f g) (tailProofProgram f g qf qg) := rfl
  rw [code]
  pintro x
  prw [transitivity_program_value (leftTermProgram f g) (rightTermProgram f g)
      (outputTermProgram f g) (instanceProgram f g)
      (tailProofProgram f g qf qg), left_term_value f g, right_term_value f
      g, output_term_value f g, instance_program_value f g, tail_proof_value f g qf qg]

/-- A recognized unary congruence axiom and the child proof programs give the composition proof
program. -/
fol_theorem provesEval_comp (f g qf qg : Nat) : PRA ⊢ (recognizesCongruence f) →
    (provesEval f qf) → (provesEval g qg) →
    (provesEval (Primrec.Code.comp f g) (compProofProgram f g qf qg)) := by
  pintro recognize hf hg x
  papply (equationProofOf_of_eq (Primrec.Code.comp f g))[x, eval[Primrec.Code.comp f g](x),
    eval[compProofProgram f g qf qg](x), x, eval[f](eval[g](x)),
    (compProofAt f g qf qg)(x)]
  · prefl
  · pexact (PRA.eval_comp f g)[x]
  · pexact (comp_proof_program_value f g qf qg)[x]
  · papply transitivity_rule[(leftTermAt f g)(x),
      (rightTermAt f g)(x), (outputTermAt f g)(x),
      (instanceAt f g)(x), (tailProofAt f g qf qg)(x)]
    · pexact (instance_accepted f g)[x]
    · papply transitivity_rule[(rightTermAt f g)(x),
        (middleTermAt f g)(x), (outputTermAt f g)(x),
        (liftedProofAt f g qg)(x), eval[qf](eval[g](x))]
      · papply (congruence_accepted f)[(innerTermAt g)(x), numCode(eval[g](x)),
          eval[qg](x)]
        · pexact recognize
        · pexact hg[x]
      · pexact hf[eval[g](x)]

theorem provesEval_comp_of (f g qf qg : Nat) :
    (PRA ⊢ (recognizesCongruence f)) →
    (PRA ⊢ (provesEval f qf)) →
    (PRA ⊢ (provesEval g qg)) →
    (PRA ⊢ (provesEval (Primrec.Code.comp f g) (compProofProgram f g qf qg))) := by
  intro recognize hf hg
  papply provesEval_comp f g qf qg
  · pexact recognize
  · pexact hf
  · pexact hg

end EquationCompleteness.Composition

namespace EquationCompleteness

fol_theorem comp_congruence (f : Nat) : PRA ⊢ (Composition.recognizesCongruence f) := by
  pintro a b
  pexact EqualityRules.program_congruence_axiom[${num f}, a, b]

theorem provesEval_comp_of_children (f g qf qg : Nat) :
    (PRA ⊢ (provesEval f qf)) →
    (PRA ⊢ (provesEval g qg)) →
    (PRA ⊢ (provesEval (Primrec.Code.comp f g) (Composition.compProofProgram f g qf qg))) :=
  Composition.provesEval_comp_of f g qf qg (comp_congruence f)

theorem compose_proofs (f g a b : Nat) :
    EquationProofPair f a → EquationProofPair g b →
    (PRA ⊢ (provesEval ${Primrec.Code.comp f g} ${Composition.compProofProgram f g (unpairLeft a)
    (unpairLeft b)})) := by
  intro hf hg
  exact provesEval_comp_of_children f g (unpairLeft a) (unpairLeft b)
    (unpairRight a, hf) (unpairRight b, hg)

theorem comp_pair_exists : ∀ f g a b,
    EquationProofPair f a → EquationProofPair g b →
    ∃ c, EquationProofPair (Primrec.Code.comp f g) c := by
  intro f g a b ha hb
  let q := Composition.compProofProgram f g (unpairLeft a) (unpairLeft b)
  rcases compose_proofs f g a b ha hb with (p, hp)
  exact (pair q p, equationProofPair_pair (Primrec.Code.comp f g) q p hp)

end EquationCompleteness

/-! ### Pairing on `num` -/

namespace Pair

open NumShift EqualityRules EquationCompleteness.Composition

fol_def pairTermCode over PRA : term of 2 := fun a b =>
  EqualityRules.applicationCode(syntaxLanguage(), succ(zero), eval[pair.code](pair(a, b)))

fol_def successorTermCode over PRA : term of 1 := fun a =>
  EqualityRules.applicationCode(syntaxLanguage(), zero, a)

fol_def pairEquationNum over PRA : term of 2 := fun a b =>
  EqualityRules.equalityCode(syntaxLanguage(), pairTermCode(numCode(a), numCode(b)),
    numCode(pair(a, b)))

fol_def successorProof over PRA : term of 3 := fun a b p =>
  eval[applyOne.code](pair(EqualityRules.equalityCode(syntaxLanguage(), a, b),
    pair(EqualityRules.equalityCode(syntaxLanguage(),
      successorTermCode(a), successorTermCode(b)), p)))

fol_def advanceProof over PRA : term of 5 := fun a b c p q =>
  eval[applyTwo.code](pair(EqualityRules.equalityCode(syntaxLanguage(), a, successorTermCode(b)),
    pair(EqualityRules.equalityCode(syntaxLanguage(), successorTermCode(b), successorTermCode(c)),
      pair(EqualityRules.equalityCode(syntaxLanguage(), a, successorTermCode(c)),
        pair(q, successorProof(b, c, p))))))

fol_theorem successor_proof_accepted : PRA ⊢ ∀ a b p,
    praProofOf EqualityRules.equalityCode(syntaxLanguage(), a, b) p →
    (praProofOf EqualityRules.equalityCode(syntaxLanguage(),
      successorTermCode(a), successorTermCode(b)) successorProof(a, b, p)) := by
  pintro a b p previous
  papply (applyOne_accepted language isAxiom.code)[
    EqualityRules.equalityCode(syntaxLanguage(), a, b),
    EqualityRules.equalityCode(syntaxLanguage(), successorTermCode(a), successorTermCode(b)), p]
  · pexact successor_congruence_axiom[a, b]
  · pexact previous

fol_theorem advance_proof_accepted : PRA ⊢ ∀ a b c p q,
    praProofOf EqualityRules.equalityCode(syntaxLanguage(), b, c) p →
    praProofOf EqualityRules.equalityCode(syntaxLanguage(), a, successorTermCode(b)) q →
    (praProofOf EqualityRules.equalityCode(syntaxLanguage(), a, successorTermCode(c))
      advanceProof(a, b, c, p, q)) := by
  pintro a b c p q previous instanceProof
  papply (transitivity_accepted language isAxiom.code)[a, successorTermCode(b),
    successorTermCode(c), q, successorProof(b, c, p)]
  · pexact instanceProof
  · papply successor_proof_accepted[b, c, p]
    pexact previous

fol_theorem praProofOf_of_eq : PRA ⊢ ∀ A B p q,
    A = B → p = q → praProofOf B q → praProofOf A p := by
  pintro A B p q formulas proofs h
  psubst formulas
  psubst proofs
  pexact h

fol_theorem successor_num_term : PRA ⊢ ∀ a,
    successorTermCode(numCode(a)) = numCode(succ(a)) := by
  pintro a
  ptrans eval[Term.app.code](pair(${num language}, pair(zero, numCode(a))))
  · prw [eval_const_language]
  · psymm
    pexact num_succ_code[a]

fol_def zeroSuccTerm over PRA : term of 1 := fun a =>
  pairTermCode(numCode(zero), successorTermCode(numCode(a)))

fol_def zeroSuccPrevious over PRA : term of 1 := fun a =>
  pairTermCode(numCode(a), numCode(zero))

fol_def zeroSuccAxiomAt over PRA : term of 1 := fun a =>
  EqualityRules.equalityCode(syntaxLanguage(),
    zeroSuccTerm(a), successorTermCode(zeroSuccPrevious(a)))

fol_def zeroSuccAdvance over PRA : term of 3 := fun a p q =>
  advanceProof(zeroSuccTerm(a), zeroSuccPrevious(a), numCode(pair(a, zero)), p, q)

fol_theorem zeroSucc_advance_accepted : PRA ⊢ ∀ a p q,
    praProofOf pairEquationNum(a, zero) p → praProofOf zeroSuccAxiomAt(a) q →
    praProofOf pairEquationNum(zero, succ(a)) zeroSuccAdvance(a, p, q) := by
  pintro a p q previous instanceProof
  papply praProofOf_of_eq[pairEquationNum(zero, succ(a)),
    EqualityRules.equalityCode(syntaxLanguage(),
      zeroSuccTerm(a), successorTermCode(numCode(pair(a, zero)))),
    zeroSuccAdvance(a, p, q), zeroSuccAdvance(a, p, q)]
  · prw [successor_num_term, PRA.pair_zero_succ]
  · prefl
  · papply advance_proof_accepted[zeroSuccTerm(a), zeroSuccPrevious(a),
      numCode(pair(a, zero)), p, q]
    · pexact previous
    · pexact instanceProof

fol_def succLeftTerm over PRA : term of 2 := fun a b =>
  pairTermCode(successorTermCode(numCode(a)), numCode(b))

fol_def succLeftPrevious over PRA : term of 2 := fun a b =>
  pairTermCode(numCode(a), successorTermCode(numCode(b)))

fol_def succLeftAxiomAt over PRA : term of 2 := fun a b =>
  EqualityRules.equalityCode(syntaxLanguage(),
    succLeftTerm(a, b), successorTermCode(succLeftPrevious(a, b)))

fol_def succLeftAdvance over PRA : term of 4 := fun a b p q =>
  advanceProof(succLeftTerm(a, b), succLeftPrevious(a, b), numCode(pair(a, succ(b))), p, q)

fol_theorem succLeft_advance_accepted : PRA ⊢ ∀ a b p q,
    praProofOf pairEquationNum(a, succ(b)) p → praProofOf succLeftAxiomAt(a, b) q →
    praProofOf pairEquationNum(succ(a), b) succLeftAdvance(a, b, p, q) := by
  pintro a b p q previous instanceProof
  papply praProofOf_of_eq[pairEquationNum(succ(a), b),
    EqualityRules.equalityCode(syntaxLanguage(), succLeftTerm(a, b),
      successorTermCode(numCode(pair(a, succ(b))))),
    succLeftAdvance(a, b, p, q), succLeftAdvance(a, b, p, q)]
  · prw [successor_num_term, PRA.pair_succ]
  · prefl
  · papply advance_proof_accepted[succLeftTerm(a, b), succLeftPrevious(a, b),
      numCode(pair(a, succ(b))), p, q]
    · papply praProofOf_of_eq[EqualityRules.equalityCode(syntaxLanguage(), succLeftPrevious(a, b),
        numCode(pair(a, succ(b)))), pairEquationNum(a, succ(b)), p, p]
      · prw [successor_num_term]
      · prefl
      · pexact previous
    · pexact instanceProof

def equation : Nat → Nat → Nat := fun a b =>
  Formula.equal language fol_term[PRA | pair(${num a}, ${num b})] (num (pair a b))

-- Each branch program takes the components needed for its axiom instance and the previous proof.
def advance (D E : Nat → Nat) : Nat → Nat → Nat := fun i p =>
  let a := unpairLeft i;
  let b := unpairRight i;
  ite (eqb b 0) (D (pair a p)) (E (pair a (pair (pred b) p)))

def proofAt (base : Nat) (D E : Nat → Nat) : Nat → Nat :=
  primrec base (advance D E)

def PairProofOf (V F : Nat → Nat) : Nat → Nat → Nat → QFProp := fun a b p =>
  V p = 1 ∧ FOL.Proof.conclusion p = F (pair a b)

derive_primrec advance

derive_primrec proofAt

derive_fol_pra pair_zero_succ_eq as pair_zero_succ_inner

derive_fol_pra pair_succ_eq as pair_succ_inner

theorem advance_at_zero (D E : Nat → Nat) : ∀ i p, unpairRight i = 0 →
    advance D E i p = D (pair (unpairLeft i) p) := by
  intro i p hb
  rw [advance, hb, eqb_self, ite_succ]

theorem advance_at_succ (D E : Nat → Nat) : ∀ i b p, unpairRight i = S b →
    advance D E i p = E (pair (unpairLeft i) (pair b p)) := by
  intro i b p hb
  rw [advance, hb, and_right (eqb_eq_zero (S b) 0) (_root_.succ_ne_zero b), pred_succ,
    ite_zero]

theorem advance_accepted (V F D E : Nat → Nat) :
    (∀ a p, PairProofOf V F a 0 p → PairProofOf V F 0 (S a) (D (pair a p))) →
    (∀ a b p, PairProofOf V F a (S b) p → PairProofOf V F (S a) b (E (pair a (pair b p)))) →
    ∀ i p, PairProofOf V F (unpairLeft i) (unpairRight i) p →
      PairProofOf V F (unpairLeft (S i)) (unpairRight (S i)) (advance D E i p) := by
  intro zeroSucc succLeft i p h
  let a := unpairLeft i
  let b := unpairRight i
  have code : pair a b = i := pair_unpair i
  rcases zero_or_succ_pred b with hb | hb
  · rw [hb] at h
    rw [hb] at code
    have next : pair 0 (S a) = S i := by rw [pair_zero_succ_eq, code]
    rw [advance_at_zero D E i p hb, ← next, unpairLeft_pair, unpairRight_pair]
    exact zeroSucc a p h
  · let j := pred b
    rw [hb] at h
    rw [hb] at code
    have next : pair (S a) j = S i := by rw [pair_succ_eq, code]
    rw [advance_at_succ D E i j p hb, ← next, unpairLeft_pair, unpairRight_pair]
    exact succLeft a j p h

theorem proofAt_accepted (base : Nat) (V F D E : Nat → Nat) : ∀ a b,
    PairProofOf V F 0 0 base →
    (∀ a p, PairProofOf V F a 0 p → PairProofOf V F 0 (S a) (D (pair a p))) →
    (∀ a b p, PairProofOf V F a (S b) p → PairProofOf V F (S a) b (E (pair a (pair b p)))) →
    PairProofOf V F a b (proofAt base D E (pair a b)) := by
  intro a b baseValid zeroSucc succLeft
  have allIndices : ∀ i, PairProofOf V F (unpairLeft i) (unpairRight i) (proofAt base D E i) := by
    intro i
    induction i with i ih
    · change PairProofOf V F 0 0 base
      exact baseValid
    · change PairProofOf V F (unpairLeft (S i)) (unpairRight (S i))
        (advance D E i (proofAt base D E i))
      exact advance_accepted V F D E zeroSucc succLeft i (proofAt base D E i) ih
  have h := allIndices (pair a b)
  rw [unpairLeft_pair, unpairRight_pair] at h
  exact h

derive_fol_pra (public := true) proofAt_accepted as proofAt_accepted_inner

open EquationCompleteness

-- These programs construct the two term codes used in the object-language pairing equations.
def successorTermProgram (a : Nat) : Nat := applicationProgram Primrec.Code.zero a

def pairTermProgram (a b : Nat) : Nat := applicationProgram
  (Primrec.Code.comp Primrec.Code.succ Primrec.Code.zero) (Primrec.Code.pair a b)

def successorProofProgram (a b p : Nat) : Nat :=
  oneProgram (equationProgram a b)
    (equationProgram (successorTermProgram a) (successorTermProgram b)) p

def advanceProofProgram (a b c p q : Nat) : Nat :=
  twoProgram (equationProgram a (successorTermProgram b))
    (equationProgram (successorTermProgram b) (successorTermProgram c))
    (equationProgram a (successorTermProgram c)) q (successorProofProgram b c p)

fol_theorem successor_term_program_value (a : Nat) : PRA ⊢ ∀ x,
    eval[successorTermProgram a](x) = successorTermCode(eval[a](x)) := by
  have code : successorTermProgram a = applicationProgram Primrec.Code.zero a := rfl
  rw [code]
  pintro x
  ptrans eval[Term.app.code](pair(syntaxLanguage(), pair(eval[Primrec.Code.zero](x), eval[a](x))))
  · pexact (application_program_value Primrec.Code.zero a)[x]
  · prw [PRA.eval_zero]

fol_theorem one_index_value : PRA ⊢ ∀ x,
    eval[Primrec.Code.comp Primrec.Code.succ Primrec.Code.zero](x) = succ(zero) := by
  pintro x
  ptrans eval[Primrec.Code.succ](eval[Primrec.Code.zero](x))
  · pexact (PRA.eval_comp Primrec.Code.succ Primrec.Code.zero)[x]
  · prw [PRA.eval_zero, PRA.eval_succ]

fol_theorem pair_term_program_value (a b : Nat) : PRA ⊢ ∀ x,
    eval[pairTermProgram a b](x) = pairTermCode(eval[a](x), eval[b](x)) := by
  have code : pairTermProgram a b =
      applicationProgram (Primrec.Code.comp Primrec.Code.succ Primrec.Code.zero)
        (Primrec.Code.pair a b) := rfl
  rw [code]
  pintro x
  ptrans eval[Term.app.code](pair(syntaxLanguage(), pair(
    eval[Primrec.Code.comp Primrec.Code.succ Primrec.Code.zero](x),
    eval[Primrec.Code.pair a b](x))))
  · pexact (application_program_value (Primrec.Code.comp Primrec.Code.succ Primrec.Code.zero)
      (Primrec.Code.pair a b))[x]
  · prw [FOL.PRA.pair_value, one_index_value, PRA.eval_pair a b]

fol_theorem successor_proof_program_value (a b p : Nat) : PRA ⊢ ∀ x,
    eval[successorProofProgram a b p](x) = successorProof(eval[a](x), eval[b](x), eval[p](x)) := by
  have code : successorProofProgram a b p = oneProgram (equationProgram a b)
      (equationProgram (successorTermProgram a) (successorTermProgram b)) p := rfl
  rw [code]
  pintro x
  ptrans eval[applyOne.code](pair(eval[equationProgram a b](x), pair(
    eval[equationProgram (successorTermProgram a) (successorTermProgram b)](x), eval[p](x))))
  · pexact (one_program_value (equationProgram a b)
      (equationProgram (successorTermProgram a) (successorTermProgram b)) p)[x]
  · prw [equation_program_value a b,
      equation_program_value (successorTermProgram a) (successorTermProgram b),
      successor_term_program_value a, successor_term_program_value b]

fol_theorem advance_proof_program_value (a b c p q : Nat) : PRA ⊢ ∀ x,
    eval[advanceProofProgram a b c p q](x) =
      advanceProof(eval[a](x), eval[b](x), eval[c](x), eval[p](x), eval[q](x)) := by
  have code : advanceProofProgram a b c p q = twoProgram
      (equationProgram a (successorTermProgram b))
      (equationProgram (successorTermProgram b) (successorTermProgram c))
      (equationProgram a (successorTermProgram c)) q (successorProofProgram b c p) := rfl
  rw [code]
  pintro x
  ptrans eval[applyTwo.code](pair(eval[equationProgram a (successorTermProgram b)](x),
    pair(eval[equationProgram (successorTermProgram b) (successorTermProgram c)](x),
      pair(eval[equationProgram a (successorTermProgram c)](x),
        pair(eval[q](x), eval[successorProofProgram b c p](x))))))
  · pexact (two_program_value (equationProgram a (successorTermProgram b))
      (equationProgram (successorTermProgram b) (successorTermProgram c))
      (equationProgram a (successorTermProgram c)) q (successorProofProgram b c p))[x]
  · prw [equation_program_value a (successorTermProgram b),
      equation_program_value (successorTermProgram b) (successorTermProgram c),
      equation_program_value a (successorTermProgram c),
      successor_term_program_value b, successor_term_program_value c,
      successor_proof_program_value b c p]

def zeroSuccProgram (D : Nat) : Nat :=
  let a := Primrec.Code.left;
  let n := numAtProgram a;
  let z := numAtProgram Primrec.Code.zero;
  advanceProofProgram (pairTermProgram z (successorTermProgram n)) (pairTermProgram n z)
    (numAtProgram (Primrec.Code.pair a Primrec.Code.zero)) Primrec.Code.right
    (Primrec.Code.comp D a)

def succLeftProgram (E : Nat) : Nat :=
  let a := Primrec.Code.left;
  let b := Primrec.Code.comp Primrec.Code.left Primrec.Code.right;
  let p := Primrec.Code.comp Primrec.Code.right Primrec.Code.right;
  let n := numAtProgram a;
  let m := numAtProgram b;
  advanceProofProgram (pairTermProgram (successorTermProgram n) m)
    (pairTermProgram n (successorTermProgram m))
    (numAtProgram (Primrec.Code.pair a (Primrec.Code.comp Primrec.Code.succ b))) p
    (Primrec.Code.comp E (Primrec.Code.pair a b))

fol_theorem zeroSucc_program_value (D : Nat) : PRA ⊢ ∀ a p,
    eval[zeroSuccProgram D](pair(a, p)) = zeroSuccAdvance(a, p, eval[D](a)) := by
  let n := numAtProgram Primrec.Code.left
  let z := numAtProgram Primrec.Code.zero
  let l := pairTermProgram z (successorTermProgram n)
  let u := pairTermProgram n z
  let r := numAtProgram (Primrec.Code.pair Primrec.Code.left Primrec.Code.zero)
  let q := Primrec.Code.comp D Primrec.Code.left
  have code : zeroSuccProgram D = advanceProofProgram l u r Primrec.Code.right q := rfl
  rw [code]
  pintro a p
  ptrans advanceProof(eval[l](pair(a, p)), eval[u](pair(a, p)),
    eval[r](pair(a, p)), eval[Primrec.Code.right](pair(a, p)), eval[q](pair(a, p)))
  · pexact (advance_proof_program_value l u r Primrec.Code.right q)[pair(a, p)]
  · prw [pair_term_program_value z (successorTermProgram n), pair_term_program_value n z,
      successor_term_program_value n, num_at_program_value Primrec.Code.left,
      num_at_program_value Primrec.Code.zero,
      num_at_program_value (Primrec.Code.pair Primrec.Code.left Primrec.Code.zero),
      PRA.eval_pair Primrec.Code.left Primrec.Code.zero,
      PRA.eval_comp D Primrec.Code.left, PRA.eval_left, PRA.eval_right, PRA.eval_zero]

fol_theorem succLeft_program_value (E : Nat) : PRA ⊢ ∀ a b p,
    eval[succLeftProgram E](pair(a, pair(b, p))) =
      succLeftAdvance(a, b, p, eval[E](pair(a, b))) := by
  let firstProjection := Primrec.Code.left
  let secondProjection := Primrec.Code.right
  let index := Primrec.Code.comp firstProjection secondProjection
  let previous := Primrec.Code.comp secondProjection secondProjection
  let n := numAtProgram firstProjection
  let m := numAtProgram index
  let l := pairTermProgram (successorTermProgram n) m
  let u := pairTermProgram n (successorTermProgram m)
  let next := Primrec.Code.comp Primrec.Code.succ index
  let r := numAtProgram (Primrec.Code.pair firstProjection next)
  let args := Primrec.Code.pair firstProjection index
  let q := Primrec.Code.comp E args
  have code : succLeftProgram E = advanceProofProgram l u r previous q := rfl
  rw [code]
  pintro a b p
  ptrans advanceProof(eval[l](pair(a, pair(b, p))), eval[u](pair(a, pair(b, p))),
    eval[r](pair(a, pair(b, p))), eval[previous](pair(a, pair(b, p))),
    eval[q](pair(a, pair(b, p))))
  · pexact (advance_proof_program_value l u r previous q)[pair(a, pair(b, p))]
  · prw [pair_term_program_value (successorTermProgram n) m,
      pair_term_program_value n (successorTermProgram m), successor_term_program_value n,
      successor_term_program_value m, num_at_program_value firstProjection,
      num_at_program_value index,
      num_at_program_value (Primrec.Code.pair firstProjection next),
      PRA.eval_pair firstProjection next,
      PRA.eval_comp Primrec.Code.succ index,
      PRA.eval_comp E args, PRA.eval_pair firstProjection index,
      PRA.eval_comp firstProjection secondProjection,
      PRA.eval_comp secondProjection secondProjection,
      PRA.eval_left, PRA.eval_right, PRA.eval_succ]

def pairingEquationProgram : Nat :=
  equationProgram (pairTermProgram (numAtProgram Primrec.Code.left)
    (numAtProgram Primrec.Code.right))
    (numAtProgram (Primrec.Code.pair Primrec.Code.left Primrec.Code.right))

fol_theorem equation_code : PRA ⊢ ∀ a b,
    eval[pairingEquationProgram](pair(a, b)) = pairEquationNum(a, b) := by
  let l := numAtProgram Primrec.Code.left
  let r := numAtProgram Primrec.Code.right
  let v := numAtProgram (Primrec.Code.pair Primrec.Code.left Primrec.Code.right)
  have code : pairingEquationProgram = equationProgram (pairTermProgram l r) v := rfl
  rw [code]
  pintro a b
  ptrans EqualityRules.equalityCode(syntaxLanguage(), eval[pairTermProgram l r](pair(a, b)),
    eval[v](pair(a, b)))
  · pexact (equation_program_value (pairTermProgram l r) v)[pair(a, b)]
  · prw [pair_term_program_value l r, num_at_program_value Primrec.Code.left,
      num_at_program_value Primrec.Code.right,
      num_at_program_value (Primrec.Code.pair Primrec.Code.left Primrec.Code.right),
      PRA.eval_pair Primrec.Code.left Primrec.Code.right, PRA.eval_left, PRA.eval_right]

theorem base_accepted :
    (PRA ⊢ praIsProof(${num pair_num_zero.witness}) =
      succ(zero)) := by
  let p := pair_num_zero.witness
  exact praIsProof_on_num p (and_left pair_num_zero.witness_correct)

theorem base_conclusion : Proof.conclusion pair_num_zero.witness = equation 0 0 :=
  and_right pair_num_zero.witness_correct

fol_theorem pairing_base_accepted : PRA ⊢
    (praProofOf eval[pairingEquationProgram](pair(zero, zero))
    eval[Primrec.Code.const pair_num_zero.witness](zero)) := by
  phave pValue : eval[Primrec.Code.const pair_num_zero.witness](zero) =
      ${num pair_num_zero.witness}
  · pexact (constant_value pair_num_zero.witness)[zero]
  papply praProofOf_of_eq[eval[pairingEquationProgram](pair(zero, zero)),
    ${num (equation 0 0)},
    eval[Primrec.Code.const pair_num_zero.witness](zero), ${num pair_num_zero.witness}]
  · ptrans pairEquationNum(zero, zero)
    · pexact equation_code[zero, zero]
    · have termValue : (PRA ⊢ pairTermCode(zero, zero) =
          ${num (Term.app language 1 0)}) := by
        ptrans eval[Term.app.code](pair(${num language}, pair(${num 1}, zero)))
        · prw [FOL.PRA.pair_value, eval_const_language, PRA.pair_zero_zero, num_one]
        · have h := EquationCompleteness.app_value 1 0
          rw [num_zero] at h
          exact h
      ptrans eval[Formula.equal.code](pair(${num language},
        pair(${num (Term.app language 1 0)}, zero)))
      · prw [termValue, eval_num_zero, PRA.pair_zero_zero, eval_const_language]
      · ptrans ${num (Formula.equal language (Term.app language 1 0) 0)}
        · ptrans eval[Formula.equal.code](pair(${num language},
            pair(${num (Term.app language 1 0)}, ${num 0})))
          · have zeroNumber : (PRA ⊢ ${num 0} = zero) := by
              rw [num_zero]
              prefl
            prw [zeroNumber]
          · pexact EquationCompleteness.equal_value (Term.app language 1 0) 0
        · have result : Formula.equal language (Term.app language 1 0) 0 = equation 0 0 := by
            have packedZero : pair 0 0 = 0 := rfl
            have numZero : num 0 = 0 := eq_trans num_zero const_zero_language
            have inputs : pair (num 0) (num 0) = 0 :=
              eq_trans (eq_congr₂ pair numZero numZero) packedZero
            have pairZero : num (pair 0 0) = 0 := by
              rw [packedZero]
              exact numZero
            change Formula.equal language (Term.app language 1 0) 0 =
              Formula.equal language (Term.app language 1 (pair (num 0) (num 0))) (num (pair 0 0))
            exact eq_symm (eq_congr₂ (Formula.equal language)
              (eq_congr (Term.app language 1) inputs) pairZero)
          pexact num_eq_of_eq (Formula.equal language (Term.app language 1 0) 0)
              (equation 0 0) result
  · pexact pValue
  · pconstructor
    · pexact base_accepted
    · ptrans ${num (Proof.conclusion pair_num_zero.witness)}
      · pexact eval_num_of_evaluates Proof.conclusion.code pair_num_zero.witness _
          (Proof.conclusion.trace pair_num_zero.witness)
          (Proof.conclusion.computedBy pair_num_zero.witness)
      · pexact num_eq_of_eq (Proof.conclusion pair_num_zero.witness)
          (equation 0 0) base_conclusion

/-- Proofs of the two axiom instances suffice to prove the pairing equations. -/
fol_theorem provesPair_of_rules (D E : Nat) : PRA ⊢
    (∀ a, praProofOf zeroSuccAxiomAt(a) eval[D](a)) →
    (∀ a b, praProofOf succLeftAxiomAt(a, b) eval[E](pair(a, b))) →
    ∀ a b, (praProofOf pairEquationNum(a, b)
      eval[proofAt.code pair_num_zero.witness
        (zeroSuccProgram D) (succLeftProgram E)](pair(a, b))) := by
  pintro zeroSucc succLeft a b
  papply praProofOf_of_eq[pairEquationNum(a, b),
    eval[pairingEquationProgram](eval[pair.code](pair(a, b))),
    eval[proofAt.code pair_num_zero.witness
      (zeroSuccProgram D) (succLeftProgram E)](pair(a, b)),
    eval[proofAt.code pair_num_zero.witness
      (zeroSuccProgram D) (succLeftProgram E)](eval[pair.code](pair(a, b)))]
  · prw [FOL.PRA.pair_value, equation_code]
  · prw [FOL.PRA.pair_value]
  · papply (proofAt_accepted_inner pair_num_zero.witness
      (FOL.isProof.code language isAxiom.code) pairingEquationProgram (zeroSuccProgram D)
      (succLeftProgram E))[a, b]
    · papply praProofOf_of_eq[eval[pairingEquationProgram](eval[pair.code](pair(zero, zero))),
        eval[pairingEquationProgram](pair(zero, zero)),
        eval[Primrec.Code.const pair_num_zero.witness](zero),
        eval[Primrec.Code.const pair_num_zero.witness](zero)]
      · prw [FOL.PRA.pair_value]
      · prefl
      · pexact pairing_base_accepted
    · pintro x p previous
      papply praProofOf_of_eq[
        eval[pairingEquationProgram](eval[pair.code](pair(zero, succ(x)))),
        pairEquationNum(zero, succ(x)),
        eval[zeroSuccProgram D](eval[pair.code](pair(x, p))), zeroSuccAdvance(x, p, eval[D](x))]
      · prw [FOL.PRA.pair_value, equation_code]
      · prw [FOL.PRA.pair_value, zeroSucc_program_value D]
      · papply zeroSucc_advance_accepted[x, p, eval[D](x)]
        · papply praProofOf_of_eq[pairEquationNum(x, zero),
            eval[pairingEquationProgram](eval[pair.code](pair(x, zero))), p, p]
          · prw [FOL.PRA.pair_value, equation_code]
          · prefl
          · pexact previous
        · pexact zeroSucc[x]
    · pintro x y p previous
      papply praProofOf_of_eq[
        eval[pairingEquationProgram](eval[pair.code](pair(succ(x), y))),
        pairEquationNum(succ(x), y),
        eval[succLeftProgram E](eval[pair.code](pair(x, eval[pair.code](pair(y, p))))),
        succLeftAdvance(x, y, p, eval[E](pair(x, y)))]
      · prw [FOL.PRA.pair_value, equation_code]
      · prw [FOL.PRA.pair_value, succLeft_program_value E]
      · papply succLeft_advance_accepted[x, y, p, eval[E](pair(x, y))]
        · papply praProofOf_of_eq[pairEquationNum(x, succ(y)),
            eval[pairingEquationProgram](eval[pair.code](pair(x, succ(y)))), p, p]
          · prw [FOL.PRA.pair_value, equation_code]
          · prefl
          · pexact previous
        · pexact succLeft[x, y]

open FOL

fol_def pairCode over PRA : term of 2 := fun t u =>
  eval[Term.app.code](pair(${num language}, pair(succ(zero), eval[pair.code](pair(t, u)))))

fol_def equalCode over PRA : term of 2 := fun t u =>
  eval[Formula.equal.code](pair(${num language}, pair(t, u)))

fol_def zeroSuccCode over PRA : term of 1 := fun t =>
  equalCode(pairCode(zero, succCode(t)), succCode(pairCode(t, zero)))

fol_def succLeftCode over PRA : term of 2 := fun t u =>
  equalCode(pairCode(succCode(t), u), succCode(pairCode(t, succCode(u))))

def zeroSuccBody : Nat :=
  let t := Term.var language 0;
  fol_formula[PRA | pair(zero, succ(${t})) = succ(pair(${t}, zero))]

def succLeftBody : Nat :=
  let t := Term.var language 1;
  let u := Term.var language 0;
  fol_formula[PRA | pair(succ(${t}), ${u}) = succ(pair(${t}, succ(${u})))]

theorem left_lt_pair_term : ∀ L j t u, t < Term.app L j (pair t u) := by
  intro L j t u
  exact lt_of_le_of_lt t (pair t u) _ (_root_.left_le_pair t u)
    (Term.args_lt_app L j (pair t u))

theorem right_lt_pair_term : ∀ L j t u, u < Term.app L j (pair t u) := by
  intro L j t u
  exact lt_of_le_of_lt u (pair t u) _ (_root_.right_le_pair t u)
    (Term.args_lt_app L j (pair t u))

derive_fol_pra left_lt_pair_term as left_lt_pair_term_inner

derive_fol_pra right_lt_pair_term as right_lt_pair_term_inner

theorem term_le_of_lt_chain : ∀ i j k, i < j → j ≤ k → i ≤ k :=
  fun i j k h g => le_of_lt _ _ (lt_of_lt_of_le i j k h g)

theorem term_le_in_imp : ∀ L t u A, t ≤ Formula.imp A (Formula.equal L t u) :=
  fun L t u A => le_trans t (Formula.equal L t u) _ (Formula.le_equal_left L t u)
    (le_of_lt _ _ (Formula.right_lt_imp A (Formula.equal L t u)))

derive_fol_pra term_le_of_lt_chain as term_le_of_lt_chain_inner

derive_fol_pra term_le_in_imp as term_le_in_imp_inner

fol_theorem zeroSucc_le : PRA ⊢ ∀ A t,
    eval[sub.code](pair(t, eval[Formula.imp.code](pair(A, zeroSuccCode(t))))) = zero := by
  pintro A t
  papply term_le_of_lt_chain_inner[t, succCode(t), eval[Formula.imp.code](
    pair(A, zeroSuccCode(t)))]
  · pexact lt_succCode[t]
  · papply term_le_of_lt_chain_inner[succCode(t), pairCode(zero, succCode(t)),
        eval[Formula.imp.code](pair(A, zeroSuccCode(t)))]
    · pexact right_lt_pair_term_inner[${num language}, succ(zero), zero, succCode(t)]
    · pexact term_le_in_imp_inner[${num language}, pairCode(zero, succCode(t)),
        succCode(pairCode(t, zero)), A]

theorem lt_chain : ∀ i j k, i < j → j < k → i < k :=
  fun i j k h g => lt_of_lt_of_le i j k h (le_of_lt j k g)

derive_fol_pra lt_chain as lt_chain_inner

theorem app_value (j a : Nat) :
    (PRA ⊢ eval[Term.app.code](pair(${num language}, pair(${num j}, ${num a}))) =
      ${num (Term.app language j a)}) := by
  let x := pair language (pair j a)
  have h := Term.app.computedBy x
  rw [unpairLeft_pair, unpairRight_pair, unpairLeft_pair, unpairRight_pair] at h
  have packed := Evaluation.congr_eval Term.app.code _ _
    (Evaluation.congr_pair _ _ _ _ (Evaluation.refl (num language)) (pair_num j a))
  exact Evaluation.trans _ _ _ packed
    (eval_pair_num_of_evaluates Term.app.code language (pair j a) _ (Term.app.trace x) h)

theorem equal_value (u v : Nat) :
    (PRA ⊢ equalCode(${num u}, ${num v}) = ${num (Formula.equal language u v)}) := by
  let x := pair language (pair u v)
  have h := Formula.equal.computedBy x
  rw [unpairLeft_pair, unpairRight_pair, unpairLeft_pair, unpairRight_pair] at h
  have packed := Evaluation.congr_eval Formula.equal.code _ _
    (Evaluation.congr_pair _ _ _ _ (Evaluation.refl (num language)) (pair_num u v))
  exact Evaluation.trans _ _ _ packed
    (eval_pair_num_of_evaluates Formula.equal.code language (pair u v) _
      (Formula.equal.trace x) h)

theorem successor_value (t : Nat) :
    (PRA ⊢ succCode(${num t}) = ${num (Term.app language 0 t)}) := by
  have h := app_value 0 t
  rw [num_zero] at h
  exact h

theorem pair_value (t u : Nat) :
    (PRA ⊢ pairCode(${num t}, ${num u}) = ${num (Term.app language 1 (pair t u))}) := by
  have h := app_value 1 (pair t u)
  rw [num_succ 0, num_zero] at h
  ptrans eval[Term.app.code](pair(${num language}, pair(succ(zero), ${num (pair t u)})))
  · prw [FOL.PRA.pair_value, pair_num t u]
  · exact h

theorem all_value (A : Nat) :
    (PRA ⊢ eval[Formula.all.code](${num A}) = ${num (Formula.all A)}) :=
  eval_num_of_evaluates Formula.all.code A _ (Formula.all.trace A) (Formula.all.computedBy A)

theorem zeroSucc_value (t : Nat) :
    (PRA ⊢ zeroSuccCode(${num t}) =
      ${num (Formula.equal language (Term.app language 1 (pair 0 (Term.app language 0 t)))
        (Term.app language 0 (Term.app language 1 (pair t 0))))}) := by
  let a := Term.app language 0 t
  let b := Term.app language 1 (pair t 0)
  let u := Term.app language 1 (pair 0 a)
  let v := Term.app language 0 b
  have l : (PRA ⊢ pairCode(zero, succCode(${num t})) = ${num u}) := by
    have h := pair_value 0 a
    rw [num_zero] at h
    ptrans pairCode(zero, ${num a})
    · prw [successor_value t]
    · exact h
  have r : (PRA ⊢ succCode(pairCode(${num t}, zero)) = ${num v}) := by
    have h := pair_value t 0
    rw [num_zero] at h
    ptrans succCode(${num b})
    · prw [h]
    · exact successor_value b
  ptrans equalCode(${num u}, ${num v})
  · prw [l, r]
  · exact equal_value u v

fol_theorem zeroSucc_body_value : PRA ⊢ zeroSuccCode(${num 1}) = ${num zeroSuccBody} := by
  have bodyCode : zeroSuccBody = Formula.equal language
      (Term.app language 1 (pair 0 (Term.app language 0 (Term.var language 0))))
      (Term.app language 0 (Term.app language 1 (pair (Term.var language 0) 0))) := by
    rw [zeroSuccBody, const_zero_language]
  rw [bodyCode, var_zero_language]
  exact zeroSucc_value 1

fol_theorem zeroSucc_substitution : PRA ⊢ ∀ n,
    eval[Formula.instantiate.code](pair(${num language},
      pair(${num zeroSuccBody}, numCode(n)))) = zeroSuccCode(numCode(n)) := by
  pintro n
  ptrans eval[Formula.instantiate.code](pair(${num language},
    pair(zeroSuccCode(${num 1}), numCode(n))))
  · prw [zeroSucc_body_value]
  · ptrans zeroSuccCode(shiftZeroCode(numCode(n)))
    · ptrans eval[Formula.instantiate.code](pair(${num language},
        pair(zeroSuccCode(succ(zero)), numCode(n))))
      · prw [num_one]
      · papply Substitution.instantiate_pair_zero_succ_inner[${num language}, numCode(n)]
        pexact Evaluation.symm _ _ eval_language_code
    · phave h : shiftZeroCode(numCode(n)) = numCode(n)
      · pexact shift_num[n]
      prw [h]

theorem instantiation_membership (L : Nat) : ∀ A t B,
    Formula.instantiate L A t = B →
    t ≤ Formula.imp (Formula.all A) B →
    isLogicalAxiom L (Formula.imp (Formula.all A) B) = 1 := by
  intro A t B hi hb
  rw [← hi] at hb
  rw [← hi]
  exact isLogicalAxiom_of_instantiation L A t hb

derive_fol_pra instantiation_membership as instantiation_membership_inner

theorem language_value :
    (PRA ⊢ eval[Primrec.Code.const language](zero) = ${num language}) :=
  Evaluation.constant_value language fol_term[PRA | zero]

fol_theorem zeroSucc_substitution_at_constant_language : PRA ⊢ ∀ n,
    eval[Formula.instantiate.code](pair(eval[Primrec.Code.const language](zero),
      pair(${num zeroSuccBody}, numCode(n)))) = zeroSuccCode(numCode(n)) := by
  pintro n
  ptrans eval[Formula.instantiate.code](pair(${num language},
    pair(${num zeroSuccBody}, numCode(n))))
  · prw [language_value]
  · pexact zeroSucc_substitution[n]

fol_theorem zeroSucc_instantiation : PRA ⊢ ∀ n,
    eval[isLogicalAxiom.code](pair(${num language}, eval[Formula.imp.code](pair(
      eval[Formula.all.code](${num zeroSuccBody}), zeroSuccCode(numCode(n)))))) =
      succ(zero) := by
  pintro n
  ptrans eval[isLogicalAxiom.code](pair(eval[Primrec.Code.const language](zero),
    eval[Formula.imp.code](pair(eval[Formula.all.code](${num zeroSuccBody}),
      zeroSuccCode(numCode(n))))))
  · prw [language_value]
  · papply (instantiation_membership_inner language)[${num zeroSuccBody},
      numCode(n), zeroSuccCode(numCode(n))]
    · pexact zeroSucc_substitution_at_constant_language[n]
    · pexact zeroSucc_le[eval[Formula.all.code](${num zeroSuccBody}), numCode(n)]

fol_theorem zeroSucc_universal : PRA ⊢ ∀ y, pair(zero, succ(y)) = succ(pair(y, zero)) := by
  pexact PRA.pair_zero_succ[]

extract_witness zeroSucc_universal

theorem zeroSucc_universal_accepted :
    (PRA ⊢ praIsProof(${num zeroSucc_universal.witness}) =
      succ(zero) ∧ eval[Proof.conclusion.code](${num zeroSucc_universal.witness}) =
        eval[Formula.all.code](${num zeroSuccBody})) := by
  let p := zeroSucc_universal.witness
  have h : IsProofOf language isAxiom (Formula.all zeroSuccBody) p :=
    zeroSucc_universal.witness_correct
  have valid :=  praIsProof_on_num p (and_left h)
  have concludes := eval_num_of_evaluates Proof.conclusion.code p (Proof.conclusion p)
    (Proof.conclusion.trace p) (Proof.conclusion.computedBy p)
  rw [and_right h] at concludes
  pconstructor
  · exact valid
  · ptrans ${num (Formula.all zeroSuccBody)}
    · exact concludes
    · psymm
      exact all_value zeroSuccBody

fol_def shiftedOne over PRA : term of 1 := fun t =>
  eval[Term.shift.code](pair(${num language}, pair(succ(zero), t)))

theorem le_chain : ∀ a b c, a ≤ b → b ≤ c → a ≤ c := le_trans

theorem imp_right_le : ∀ A B, B ≤ Formula.imp A B :=
  fun A B => le_of_lt B (Formula.imp A B) (Formula.right_lt_imp A B)

derive_fol_pra le_chain as le_chain_inner

derive_fol_pra imp_right_le as imp_right_le_inner

fol_theorem succLeft_first_le : PRA ⊢ ∀ A t u,
    eval[sub.code](pair(t, eval[Formula.imp.code](pair(A,
      eval[Formula.all.code](succLeftCode(t, u)))))) = zero := by
  pintro A t u
  papply term_le_of_lt_chain_inner[t, succCode(t), eval[Formula.imp.code](pair(A,
    eval[Formula.all.code](succLeftCode(t, u))))]
  · pexact lt_succCode[t]
  · papply term_le_of_lt_chain_inner[succCode(t), pairCode(succCode(t), u),
      eval[Formula.imp.code](pair(A, eval[Formula.all.code](succLeftCode(t, u))))]
    · pexact left_lt_pair_term_inner[${num language}, succ(zero), succCode(t), u]
    · papply le_chain_inner[pairCode(succCode(t), u), succLeftCode(t, u),
        eval[Formula.imp.code](pair(A, eval[Formula.all.code](succLeftCode(t, u))))]
      · pexact formula_le_equal_left[${num language}, pairCode(succCode(t), u),
          succCode(pairCode(t, succCode(u)))]
      · papply term_le_of_lt_chain_inner[succLeftCode(t, u),
          eval[Formula.all.code](succLeftCode(t, u)),
          eval[Formula.imp.code](pair(A, eval[Formula.all.code](succLeftCode(t, u))))]
        · pexact body_lt_all_inner[succLeftCode(t, u)]
        · pexact imp_right_le_inner[A, eval[Formula.all.code](succLeftCode(t, u))]

fol_theorem succLeft_second_le : PRA ⊢ ∀ A t u,
    eval[sub.code](pair(u, eval[Formula.imp.code](pair(A, succLeftCode(t, u))))) = zero := by
  pintro A t u
  papply term_le_of_lt_chain_inner[u, pairCode(succCode(t), u),
    eval[Formula.imp.code](pair(A, succLeftCode(t, u)))]
  · pexact right_lt_pair_term_inner[${num language}, succ(zero), succCode(t), u]
  · pexact term_le_in_imp_inner[${num language}, pairCode(succCode(t), u),
      succCode(pairCode(t, succCode(u))), A]

fol_theorem shift_one_num : PRA ⊢ ∀ n, shiftedOne(numCode(n)) = numCode(n) := by
  pintro n
  ptrans NumShift.shiftOneCode(numCode(n))
  · prw [num_one]
  · pexact NumShift.shift_one_num[n]

theorem succLeft_value (t u : Nat) :
    (PRA ⊢ succLeftCode(${num t}, ${num u}) =
      ${num (Formula.equal language (Term.app language 1 (pair (Term.app language 0 t) u))
        (Term.app language 0 (Term.app language 1 (pair t (Term.app language 0 u)))))}) := by
  let a := Term.app language 0 t
  let b := Term.app language 0 u
  let l := Term.app language 1 (pair a u)
  let m := Term.app language 1 (pair t b)
  let r := Term.app language 0 m
  have hl : (PRA ⊢ pairCode(succCode(${num t}), ${num u}) = ${num l}) := by
    ptrans pairCode(${num a}, ${num u})
    · prw [successor_value t]
    · exact pair_value a u
  have hm : (PRA ⊢ pairCode(${num t}, succCode(${num u})) = ${num m}) := by
    ptrans pairCode(${num t}, ${num b})
    · prw [successor_value u]
    · exact pair_value t b
  have hr : (PRA ⊢ succCode(pairCode(${num t}, succCode(${num u}))) = ${num r}) := by
    ptrans succCode(${num m})
    · prw [hm]
    · exact successor_value m
  ptrans equalCode(${num l}, ${num r})
  · prw [hl, hr]
  · exact equal_value l r

fol_theorem succLeft_body_value : PRA ⊢ succLeftCode(${num 5}, ${num 1}) = ${num succLeftBody} := by
  have bodyCode : succLeftBody = Formula.equal language
      (Term.app language 1 (pair (Term.app language 0 (Term.var language 1)) (Term.var language 0)))
      (Term.app language 0 (Term.app language 1
        (pair (Term.var language 1) (Term.app language 0 (Term.var language 0))))) := rfl
  rw [bodyCode, var_one_language, var_zero_language]
  exact succLeft_value 5 1

fol_def succLeftOpen over PRA : term of 1 := fun a => succLeftCode(numCode(a), ${num 1})

fol_def succLeftHalf over PRA : term of 1 := fun a => eval[Formula.all.code](succLeftOpen(a))

theorem quantified_body_value :
    (PRA ⊢ eval[Formula.all.code](succLeftCode(${num 5}, ${num 1})) =
      ${num (Formula.all succLeftBody)}) := by
  ptrans eval[Formula.all.code](${num succLeftBody})
  · prw [succLeft_body_value]
  · exact all_value succLeftBody

fol_theorem succLeft_first_substitution : PRA ⊢ ∀ a,
    eval[Formula.instantiate.code](pair(${num language}, pair(${num (Formula.all succLeftBody)},
      numCode(a)))) = succLeftHalf(a) := by
  pintro a
  ptrans eval[Formula.instantiate.code](pair(${num language}, pair(
    eval[Formula.all.code](succLeftCode(${num 5}, ${num 1})), numCode(a))))
  · prw [quantified_body_value]
  · ptrans eval[Formula.all.code](succLeftCode(shiftedOne(numCode(a)), ${num 1}))
    · ptrans eval[Formula.instantiate.code](pair(${num language}, pair(
          eval[Formula.all.code](succLeftCode(succ(succ(succ(succ(succ(zero))))), succ(zero))),
          numCode(a))))
      · prw [num_five, num_one]
      · ptrans eval[Formula.all.code](succLeftCode(shiftedOne(numCode(a)), succ(zero)))
        · papply Substitution.instantiate_pair_succ_first_inner[
            ${num language}, numCode(a)]
          pexact Evaluation.symm _ _ eval_language_code
        · prw [num_one]
    · phave h : shiftedOne(numCode(a)) = numCode(a)
      · pexact shift_one_num[a]
      prw [h]

fol_theorem succLeft_second_substitution : PRA ⊢ ∀ a b,
    eval[Formula.instantiate.code](pair(${num language}, pair(succLeftOpen(a), numCode(b)))) =
      succLeftCode(numCode(a), numCode(b)) := by
  pintro a b
  ptrans succLeftCode(numCode(a), shiftZeroCode(numCode(b)))
  · ptrans eval[Formula.instantiate.code](pair(${num language},
        pair(succLeftCode(numCode(a), succ(zero)), numCode(b))))
    · prw [num_one]
    · papply Substitution.instantiate_pair_succ_second_inner[${num language},
        a, numCode(b)]
      pexact Evaluation.symm _ _ eval_language_code
  · phave h : shiftZeroCode(numCode(b)) = numCode(b)
    · pexact shift_num[b]
    prw [h]

fol_theorem succLeft_first_substitution_at_constant_language : PRA ⊢ ∀ a,
    eval[Formula.instantiate.code](pair(eval[Primrec.Code.const language](zero),
      pair(${num (Formula.all succLeftBody)}, numCode(a)))) = succLeftHalf(a) := by
  pintro a
  ptrans eval[Formula.instantiate.code](pair(${num language},
    pair(${num (Formula.all succLeftBody)}, numCode(a))))
  · prw [language_value]
  · pexact succLeft_first_substitution[a]

fol_theorem succLeft_second_substitution_at_constant_language : PRA ⊢ ∀ a b,
    eval[Formula.instantiate.code](pair(eval[Primrec.Code.const language](zero),
      pair(succLeftOpen(a), numCode(b)))) = succLeftCode(numCode(a), numCode(b)) := by
  pintro a b
  ptrans eval[Formula.instantiate.code](pair(${num language}, pair(succLeftOpen(a), numCode(b))))
  · prw [language_value]
  · pexact succLeft_second_substitution[a, b]

fol_theorem succLeft_first_instantiation : PRA ⊢ ∀ a,
    eval[isLogicalAxiom.code](pair(${num language}, eval[Formula.imp.code](pair(
      eval[Formula.all.code](${num (Formula.all succLeftBody)}),
      succLeftHalf(a))))) = succ(zero) := by
  pintro a
  ptrans eval[isLogicalAxiom.code](pair(eval[Primrec.Code.const language](zero),
    eval[Formula.imp.code](pair(eval[Formula.all.code](${num (Formula.all succLeftBody)}),
      succLeftHalf(a)))))
  · prw [language_value]
  · papply (instantiation_membership_inner language)[${num (Formula.all succLeftBody)},
      numCode(a), succLeftHalf(a)]
    · pexact succLeft_first_substitution_at_constant_language[a]
    · pexact succLeft_first_le[eval[Formula.all.code](${num (Formula.all succLeftBody)}),
        numCode(a), ${num 1}]

fol_theorem succLeft_second_instantiation : PRA ⊢ ∀ a b,
    eval[isLogicalAxiom.code](pair(${num language}, eval[Formula.imp.code](pair(
      succLeftHalf(a), succLeftCode(numCode(a), numCode(b)))))) = succ(zero) := by
  pintro a b
  ptrans eval[isLogicalAxiom.code](pair(eval[Primrec.Code.const language](zero),
    eval[Formula.imp.code](pair(succLeftHalf(a), succLeftCode(numCode(a), numCode(b))))))
  · prw [language_value]
  · papply (instantiation_membership_inner language)[succLeftOpen(a), numCode(b),
      succLeftCode(numCode(a), numCode(b))]
    · pexact succLeft_second_substitution_at_constant_language[a, b]
    · pexact succLeft_second_le[succLeftHalf(a), numCode(a), numCode(b)]

fol_theorem succLeft_universal : PRA ⊢ ∀ x y, pair(succ(x), y) = succ(pair(x, succ(y))) := by
  pexact PRA.pair_succ[]

extract_witness succLeft_universal

def zeroSuccResultProgram : Nat :=
  let x := num.code;
  let z := numAtProgram Primrec.Code.zero;
  equationProgram (pairTermProgram z (successorTermProgram x))
    (successorTermProgram (pairTermProgram x z))

def succLeftResultProgram (a b : Nat) : Nat :=
  equationProgram (pairTermProgram (successorTermProgram a) b)
    (successorTermProgram (pairTermProgram a (successorTermProgram b)))

def succLeftOpenResultProgram : Nat :=
  succLeftResultProgram num.code
    (Primrec.Code.comp Primrec.Code.succ Primrec.Code.zero)

def succLeftHalfResultProgram : Nat := Primrec.Code.comp Formula.all.code succLeftOpenResultProgram

def succLeftFullResultProgram : Nat :=
  succLeftResultProgram (numAtProgram Primrec.Code.left) (numAtProgram Primrec.Code.right)

def zeroSuccInstanceProofProgram : Nat :=
  oneProgram (instanceUniversalProgram zeroSuccBody) zeroSuccResultProgram
    (Primrec.Code.const zeroSucc_universal.witness)

def succLeftFirstProofProgram : Nat :=
  oneProgram (instanceUniversalProgram (Formula.all succLeftBody)) succLeftHalfResultProgram
    (Primrec.Code.const succLeft_universal.witness)

def succLeftInstanceProofProgram : Nat :=
  oneProgram (Primrec.Code.comp succLeftHalfResultProgram Primrec.Code.left)
    succLeftFullResultProgram (Primrec.Code.comp succLeftFirstProofProgram Primrec.Code.left)

fol_theorem zeroSucc_result_program_value : PRA ⊢ ∀ a,
    eval[zeroSuccResultProgram](a) = zeroSuccAxiomAt(a) := by
  let x := num.code
  let z := numAtProgram Primrec.Code.zero
  let l := pairTermProgram z (successorTermProgram x)
  let r := successorTermProgram (pairTermProgram x z)
  have code : zeroSuccResultProgram = equationProgram l r := rfl
  rw [code]
  pintro a
  ptrans EqualityRules.equalityCode(syntaxLanguage(), eval[l](a), eval[r](a))
  · pexact (equation_program_value l r)[a]
  · prw [pair_term_program_value z (successorTermProgram x),
      successor_term_program_value x, successor_term_program_value (pairTermProgram x z),
      pair_term_program_value x z, num_at_program_value Primrec.Code.zero, PRA.eval_zero]

fol_theorem zeroSucc_axiom_code : PRA ⊢ ∀ a,
    zeroSuccAxiomAt(a) = zeroSuccCode(numCode(a)) := by
  pintro a
  prw [eval_const_language, eval_num_zero]

fol_theorem succLeft_axiom_code : PRA ⊢ ∀ a b,
    succLeftAxiomAt(a, b) = succLeftCode(numCode(a), numCode(b)) := by
  pintro a b
  prw [eval_const_language]

fol_theorem succLeft_result_program_value (a b : Nat) : PRA ⊢ ∀ x,
    eval[succLeftResultProgram a b](x) = EqualityRules.equalityCode(syntaxLanguage(),
      pairTermCode(successorTermCode(eval[a](x)), eval[b](x)),
      successorTermCode(pairTermCode(eval[a](x), successorTermCode(eval[b](x))))) := by
  let l := pairTermProgram (successorTermProgram a) b
  let r := successorTermProgram (pairTermProgram a (successorTermProgram b))
  have code : succLeftResultProgram a b = equationProgram l r := rfl
  rw [code]
  pintro x
  ptrans EqualityRules.equalityCode(syntaxLanguage(), eval[l](x), eval[r](x))
  · pexact (equation_program_value l r)[x]
  · prw [pair_term_program_value (successorTermProgram a) b,
      successor_term_program_value a,
      successor_term_program_value (pairTermProgram a (successorTermProgram b)),
      pair_term_program_value a (successorTermProgram b), successor_term_program_value b]

fol_theorem succLeft_open_result_value : PRA ⊢ ∀ a,
    eval[succLeftOpenResultProgram](a) = succLeftOpen(a) := by
  let x := num.code
  let c := Primrec.Code.comp Primrec.Code.succ Primrec.Code.zero
  have code : succLeftOpenResultProgram = succLeftResultProgram x c := rfl
  rw [code]
  pintro a
  ptrans EqualityRules.equalityCode(syntaxLanguage(), pairTermCode(successorTermCode(numCode(a)),
      eval[c](a)), successorTermCode(pairTermCode(numCode(a), successorTermCode(eval[c](a)))))
  · pexact (succLeft_result_program_value x c)[a]
  · prw [eval_const_language, one_index_value, num_one]

fol_theorem succLeft_half_result_value : PRA ⊢ ∀ a,
    eval[succLeftHalfResultProgram](a) = succLeftHalf(a) := by
  have code : succLeftHalfResultProgram =
      Primrec.Code.comp Formula.all.code succLeftOpenResultProgram := rfl
  rw [code]
  pintro a
  ptrans eval[Formula.all.code](eval[succLeftOpenResultProgram](a))
  · pexact (PRA.eval_comp Formula.all.code succLeftOpenResultProgram)[a]
  · prw [succLeft_open_result_value]

fol_theorem succLeft_full_result_value : PRA ⊢ ∀ a b,
    eval[succLeftFullResultProgram](pair(a, b)) = succLeftAxiomAt(a, b) := by
  let l := numAtProgram Primrec.Code.left
  let r := numAtProgram Primrec.Code.right
  have code : succLeftFullResultProgram = succLeftResultProgram l r := rfl
  rw [code]
  pintro a b
  ptrans EqualityRules.equalityCode(syntaxLanguage(),
    pairTermCode(successorTermCode(eval[l](pair(a, b))), eval[r](pair(a, b))),
    successorTermCode(pairTermCode(eval[l](pair(a, b)), successorTermCode(eval[r](pair(a, b))))))
  · pexact (succLeft_result_program_value l r)[pair(a, b)]
  · prw [num_at_program_value Primrec.Code.left, num_at_program_value Primrec.Code.right,
      PRA.eval_left, PRA.eval_right]

fol_theorem succLeft_universal_accepted : PRA ⊢
    (praProofOf eval[Formula.all.code](${num (Formula.all succLeftBody)})
      ${num succLeft_universal.witness}) := by
  let p := succLeft_universal.witness
  have valid : FOL.IsProofOf language isAxiom (Formula.all (Formula.all succLeftBody)) p :=
    succLeft_universal.witness_correct
  have accepted := praIsProof_on_num p (and_left valid)
  have concludes := eval_num_of_evaluates Proof.conclusion.code p (Proof.conclusion p)
    (Proof.conclusion.trace p) (Proof.conclusion.computedBy p)
  rw [and_right valid] at concludes
  pconstructor
  · exact accepted
  · ptrans ${num (Formula.all (Formula.all succLeftBody))}
    · exact concludes
    · psymm
      exact all_value (Formula.all succLeftBody)

fol_theorem zeroSucc_instance_program_value : PRA ⊢ ∀ a,
    eval[zeroSuccInstanceProofProgram](a) =
      eval[applyOne.code](pair(eval[Formula.all.code](${num zeroSuccBody}),
        pair(zeroSuccCode(numCode(a)), ${num zeroSucc_universal.witness}))) := by
  let u := instanceUniversalProgram zeroSuccBody
  let p := Primrec.Code.const zeroSucc_universal.witness
  have code : zeroSuccInstanceProofProgram = oneProgram u zeroSuccResultProgram p := rfl
  rw [code]
  pintro a
  ptrans eval[applyOne.code](pair(eval[u](a), pair(eval[zeroSuccResultProgram](a), eval[p](a))))
  · pexact (one_program_value u zeroSuccResultProgram p)[a]
  · prw [instance_universal_value zeroSuccBody, zeroSucc_result_program_value,
      zeroSucc_axiom_code, constant_value zeroSucc_universal.witness]

fol_theorem succLeft_first_program_value : PRA ⊢ ∀ a,
    eval[succLeftFirstProofProgram](a) =
      eval[applyOne.code](pair(eval[Formula.all.code](${num (Formula.all succLeftBody)}),
        pair(succLeftHalf(a), ${num succLeft_universal.witness}))) := by
  let u := instanceUniversalProgram (Formula.all succLeftBody)
  let p := Primrec.Code.const succLeft_universal.witness
  have code : succLeftFirstProofProgram = oneProgram u succLeftHalfResultProgram p := rfl
  rw [code]
  pintro a
  ptrans eval[applyOne.code](pair(eval[u](a), pair(eval[succLeftHalfResultProgram](a), eval[p](a))))
  · pexact (one_program_value u succLeftHalfResultProgram p)[a]
  · prw [instance_universal_value (Formula.all succLeftBody), succLeft_half_result_value,
      constant_value succLeft_universal.witness]

fol_theorem succLeft_instance_program_value : PRA ⊢ ∀ a b,
    eval[succLeftInstanceProofProgram](pair(a, b)) =
      eval[applyOne.code](pair(succLeftHalf(a),
        pair(succLeftCode(numCode(a), numCode(b)), eval[succLeftFirstProofProgram](a)))) := by
  let u := Primrec.Code.comp succLeftHalfResultProgram Primrec.Code.left
  let p := Primrec.Code.comp succLeftFirstProofProgram Primrec.Code.left
  have code : succLeftInstanceProofProgram = oneProgram u succLeftFullResultProgram p := rfl
  rw [code]
  pintro a b
  ptrans eval[applyOne.code](pair(eval[u](pair(a, b)),
    pair(eval[succLeftFullResultProgram](pair(a, b)), eval[p](pair(a, b)))))
  · pexact (one_program_value u succLeftFullResultProgram p)[pair(a, b)]
  · prw [PRA.eval_comp succLeftHalfResultProgram Primrec.Code.left,
      PRA.eval_comp succLeftFirstProofProgram Primrec.Code.left, PRA.eval_left,
      succLeft_half_result_value, succLeft_full_result_value, succLeft_axiom_code]

fol_theorem zeroSucc_instance_accepted : PRA ⊢ ∀ a,
    praProofOf zeroSuccAxiomAt(a) eval[zeroSuccInstanceProofProgram](a) := by
  pintro a
  papply praProofOf_of_eq[zeroSuccAxiomAt(a), zeroSuccCode(numCode(a)),
    eval[zeroSuccInstanceProofProgram](a),
    eval[applyOne.code](pair(eval[Formula.all.code](${num zeroSuccBody}),
      pair(zeroSuccCode(numCode(a)), ${num zeroSucc_universal.witness})))]
  · pexact zeroSucc_axiom_code[a]
  · pexact zeroSucc_instance_program_value[a]
  · papply (applyOne_accepted language isAxiom.code)[eval[Formula.all.code](${num zeroSuccBody}),
      zeroSuccCode(numCode(a)), ${num zeroSucc_universal.witness}]
    · ptrans eval[isLogicalAxiom.code](pair(${num language}, eval[Formula.imp.code](pair(
        eval[Formula.all.code](${num zeroSuccBody}), zeroSuccCode(numCode(a))))))
      · prw [eval_const_language]
      · pexact zeroSucc_instantiation[a]
    · pexact zeroSucc_universal_accepted

fol_theorem succLeft_first_accepted : PRA ⊢ ∀ a,
    praProofOf succLeftHalf(a) eval[succLeftFirstProofProgram](a) := by
  pintro a
  papply praProofOf_of_eq[succLeftHalf(a), succLeftHalf(a), eval[succLeftFirstProofProgram](a),
    eval[applyOne.code](pair(eval[Formula.all.code](${num (Formula.all succLeftBody)}),
      pair(succLeftHalf(a), ${num succLeft_universal.witness})))]
  · prefl
  · pexact succLeft_first_program_value[a]
  · papply (applyOne_accepted language isAxiom.code)[
      eval[Formula.all.code](${num (Formula.all succLeftBody)}), succLeftHalf(a),
      ${num succLeft_universal.witness}]
    · ptrans eval[isLogicalAxiom.code](pair(${num language}, eval[Formula.imp.code](pair(
        eval[Formula.all.code](${num (Formula.all succLeftBody)}), succLeftHalf(a)))))
      · prw [eval_const_language]
      · pexact succLeft_first_instantiation[a]
    · pexact succLeft_universal_accepted

fol_theorem succLeft_instance_accepted : PRA ⊢ ∀ a b,
    praProofOf succLeftAxiomAt(a, b) eval[succLeftInstanceProofProgram](pair(a, b)) := by
  pintro a b
  papply praProofOf_of_eq[succLeftAxiomAt(a, b), succLeftCode(numCode(a), numCode(b)),
    eval[succLeftInstanceProofProgram](pair(a, b)), eval[applyOne.code](pair(succLeftHalf(a),
      pair(succLeftCode(numCode(a), numCode(b)), eval[succLeftFirstProofProgram](a))))]
  · pexact succLeft_axiom_code[a, b]
  · pexact succLeft_instance_program_value[a, b]
  · papply (applyOne_accepted language isAxiom.code)[succLeftHalf(a),
      succLeftCode(numCode(a), numCode(b)), eval[succLeftFirstProofProgram](a)]
    · ptrans eval[isLogicalAxiom.code](pair(${num language}, eval[Formula.imp.code](pair(
        succLeftHalf(a), succLeftCode(numCode(a), numCode(b))))))
      · prw [eval_const_language]
      · pexact succLeft_second_instantiation[a, b]
    · pexact succLeft_first_accepted[a]

/-- The program that constructs the pairing proof at the packed input `pair a b`. -/
def pairProofProgram : Nat :=
  proofAt.code pair_num_zero.witness
    (zeroSuccProgram zeroSuccInstanceProofProgram) (succLeftProgram succLeftInstanceProofProgram)

fol_theorem provesPair_at : PRA ⊢ ∀ a b,
    praProofOf pairEquationNum(a, b) eval[pairProofProgram](pair(a, b)) := by
  rw [pairProofProgram]
  papply provesPair_of_rules zeroSuccInstanceProofProgram succLeftInstanceProofProgram
  · pexact zeroSucc_instance_accepted
  · pexact succLeft_instance_accepted

end Pair

namespace EquationCompleteness

open NumShift Composition

fol_def pairTermNumAt over PRA : term of 2 := fun a b =>
  Pair.pairTermCode(numCode(a), numCode(b))

fol_def provesPair over PRA (p : Nat) : formula :=
  ∀ a b, (praProofOf equalityCode(pairTermNumAt(a, b), numCode(pair(a, b)))
    eval[p](pair(a, b)))

theorem provesPair_of_program :
    PRA ⊢ (provesPair Pair.pairProofProgram) := by
  pintro a b
  pexact Pair.provesPair_at[a, b]

end EquationCompleteness

/-! ### Projections -/

namespace EquationCompleteness.Projection

open NumShift Composition

fol_def projectionAt over PRA (e : Nat) : term of 3 := fun a b y =>
  equalityCode(applicationCode(${num e}, Pair.pairTermCode(a, b)), y)

fol_def provesProjection over PRA (e ax : Nat) : formula :=
  ∀ a b, (praProofOf (projectionAt e)(numCode(a), numCode(b),
    numCode(eval[e](pair(a, b)))) eval[ax](pair(a, b)))

def pairTermProgram (a b : Nat) : Nat :=
  applicationProgram (Primrec.Code.const 1) (Primrec.Code.pair a b)

fol_theorem pair_term_program_value (a b : Nat) : PRA ⊢ ∀ x,
    eval[pairTermProgram a b](x) = Pair.pairTermCode(eval[a](x), eval[b](x)) := by
  rw [pairTermProgram]
  pintro x
  prw [application_program_value (Primrec.Code.const 1) (Primrec.Code.pair a b),
    constant_value 1, num_one, PRA.eval_pair a b, FOL.PRA.pair_value]

def pairTermNumProgram : Nat :=
  pairTermProgram (numAtProgram Primrec.Code.left) (numAtProgram Primrec.Code.right)

fol_theorem pair_term_num_value : PRA ⊢ ∀ a b,
    eval[pairTermNumProgram](pair(a, b)) = pairTermNumAt(a, b) := by
  rw [pairTermNumProgram]
  pintro a b
  prw [pair_term_program_value (numAtProgram Primrec.Code.left) (numAtProgram Primrec.Code.right),
    num_at_program_value Primrec.Code.left, num_at_program_value Primrec.Code.right,
    PRA.eval_left, PRA.eval_right]

def reverseProgram (a b p : Nat) : Nat := oneProgram (equationProgram a b) (equationProgram b a) p

fol_def reverseProof over PRA : term of 3 := fun a b p =>
  eval[EqualityRules.applyOne.code](pair(equalityCode(a, b), pair(equalityCode(b, a), p)))

fol_theorem reverse_program_value (a b p : Nat) : PRA ⊢ ∀ x,
    eval[reverseProgram a b p](x) = reverseProof(eval[a](x), eval[b](x), eval[p](x)) := by
  rw [reverseProgram]
  pintro x
  prw [one_program_value (equationProgram a b) (equationProgram b a) p,
    equation_program_value a b, equation_program_value b a]

fol_theorem reverse_accepted : PRA ⊢ ∀ a b p,
    praProofOf equalityCode(a, b) p →
    praProofOf equalityCode(b, a) reverseProof(a, b, p) := by
  pexact EqualityRules.symmetry_accepted language isAxiom.code

def liftedPairProgram (e p : Nat) : Nat :=
  congruenceProgram e num.code pairTermNumProgram (reverseProgram pairTermNumProgram num.code p)

def projectionProofProgram (e ax p : Nat) : Nat :=
  transitivityProgram (appProgram e num.code) (appProgram e pairTermNumProgram) (numAtProgram e)
    (liftedPairProgram e p) ax

fol_def reversePairAt over PRA (p : Nat) : term of 2 := fun a b =>
  reverseProof(pairTermNumAt(a, b), numCode(pair(a, b)), eval[p](pair(a, b)))

fol_def liftedPairAt over PRA (e p : Nat) : term of 2 := fun a b =>
  (congruenceProof e)(numCode(pair(a, b)), pairTermNumAt(a, b),
    (reversePairAt p)(a, b))

fol_def projectionProofAt over PRA (e ax p : Nat) : term of 2 := fun a b =>
  transitivityProof(applicationCode(${num e}, numCode(pair(a, b))),
    applicationCode(${num e}, pairTermNumAt(a, b)), numCode(eval[e](pair(a, b))),
    (liftedPairAt e p)(a, b), eval[ax](pair(a, b)))

fol_theorem lifted_pair_value (e p : Nat) : PRA ⊢ ∀ a b,
    eval[liftedPairProgram e p](pair(a, b)) = (liftedPairAt e p)(a, b) := by
  rw [liftedPairProgram]
  pintro a b
  prw [congruence_program_value e num.code pairTermNumProgram
      (reverseProgram pairTermNumProgram num.code p),
    reverse_program_value pairTermNumProgram num.code p, pair_term_num_value]

fol_theorem projection_proof_program_value (e ax p : Nat) : PRA ⊢ ∀ a b,
    eval[projectionProofProgram e ax p](pair(a, b)) =
      (projectionProofAt e ax p)(a, b) := by
  rw [projectionProofProgram]
  pintro a b
  prw [transitivity_program_value (appProgram e num.code) (appProgram e pairTermNumProgram)
      (numAtProgram e)
      (liftedPairProgram e p) ax, app_program_value e num.code, app_program_value e
      pairTermNumProgram, num_at_program_value e, pair_term_num_value, lifted_pair_value e p]

fol_theorem provesEval_of_paired (e q : Nat) : PRA ⊢
    (∀ x y, equationProofOf e pair(x, y) eval[e](pair(x, y)) eval[q](pair(x, y))) →
    (provesEval e q) := by
  pintro paired x
  papply (equationProofOf_of_eq e)[x, eval[e](x), eval[q](x), pair(eval[Primrec.Code.left](x),
    eval[Primrec.Code.right](x)),
    eval[e](pair(eval[Primrec.Code.left](x), eval[Primrec.Code.right](x))),
    eval[q](pair(eval[Primrec.Code.left](x), eval[Primrec.Code.right](x)))]
  · psymm
    pexact PRA.pair_eval_left_right[x]
  · pcongr
    psymm
    pexact PRA.pair_eval_left_right[x]
  · pcongr
    psymm
    pexact PRA.pair_eval_left_right[x]
  · pexact paired[eval[Primrec.Code.left](x), eval[Primrec.Code.right](x)]

fol_theorem provesEval_projection (e ax p : Nat) : PRA ⊢ (recognizesCongruence e) →
    (provesProjection e ax) → (provesPair p) →
    (provesEval e (projectionProofProgram e ax p)) := by
  pintro recognize projection paired
  papply provesEval_of_paired e (projectionProofProgram e ax p)
  pintro a b
  papply (equationProofOf_of_eq e)[pair(a, b), eval[e](pair(a, b)),
    eval[projectionProofProgram e ax p](pair(a, b)), pair(a, b), eval[e](pair(a, b)),
    (projectionProofAt e ax p)(a, b)]
  · prefl
  · prefl
  · pexact (projection_proof_program_value e ax p)[a, b]
  · papply transitivity_rule[applicationCode(${num e}, numCode(pair(a, b))),
      applicationCode(${num e}, pairTermNumAt(a, b)), numCode(eval[e](pair(a, b))),
      (liftedPairAt e p)(a, b), eval[ax](pair(a, b))]
    · papply (congruence_accepted e)[numCode(pair(a, b)), pairTermNumAt(a, b),
        (reversePairAt p)(a, b)]
      · pexact recognize
      · papply reverse_accepted[pairTermNumAt(a, b), numCode(pair(a, b)), eval[p](pair(a, b))]
        pexact paired[a, b]
    · pexact projection[a, b]

def projectionBody (e v : Nat) : Nat :=
  Formula.equal language (Term.app language (Language.functionFamilyMember language 0 e)
    (Term.app language 1 (pair (Term.var language 1) (Term.var language 0))))
    (Term.var language v)

fol_def firstBodyAt over PRA (e : Nat) : term of 1 := fun a =>
  (projectionAt e)(numCode(a), ${num 1}, eval[e](pair(numCode(a), ${num 1})))

fol_def firstResultAt over PRA (e : Nat) : term of 1 := fun a =>
  eval[Formula.all.code]((firstBodyAt e)(a))

fol_def finalResultAt over PRA (e : Nat) : term of 2 := fun a b =>
  (projectionAt e)(numCode(a), numCode(b), numCode(eval[e](pair(a, b))))

fol_def projectionSubstitutions over PRA (e body : Nat) : formula :=
  (∀ a, eval[Formula.instantiate.code](pair(syntaxLanguage(),
    pair(${num (Formula.all body)}, numCode(a)))) = (firstResultAt e)(a)) ∧
  (∀ a b, eval[Formula.instantiate.code](pair(syntaxLanguage(),
    pair((firstBodyAt e)(a), numCode(b)))) = (finalResultAt e)(a, b))

def firstArgumentsProgram : Nat :=
  Primrec.Code.pair (numAtProgram Primrec.Code.left) (Primrec.Code.const 1)

def firstPairTermProgram : Nat :=
  pairTermProgram (numAtProgram Primrec.Code.left) (Primrec.Code.const 1)

def firstBodyProgram (e : Nat) : Nat :=
  equationProgram (appProgram e firstPairTermProgram) (Primrec.Code.comp e firstArgumentsProgram)

def firstResultProgram (e : Nat) : Nat := Primrec.Code.comp Formula.all.code (firstBodyProgram e)

def finalResultProgram (e : Nat) : Nat :=
  equationProgram (appProgram e pairTermNumProgram) (numAtProgram e)

fol_theorem first_arguments_value : PRA ⊢ ∀ a b,
    eval[firstArgumentsProgram](pair(a, b)) = pair(numCode(a), ${num 1}) := by
  rw [firstArgumentsProgram]
  pintro a b
  prw [PRA.eval_pair (numAtProgram Primrec.Code.left) (Primrec.Code.const 1),
    num_at_program_value Primrec.Code.left, PRA.eval_left, constant_value 1]

fol_theorem first_pair_term_value : PRA ⊢ ∀ a b,
    eval[firstPairTermProgram](pair(a, b)) = Pair.pairTermCode(numCode(a), ${num 1}) := by
  rw [firstPairTermProgram]
  pintro a b
  prw [pair_term_program_value (numAtProgram Primrec.Code.left) (Primrec.Code.const 1),
    num_at_program_value Primrec.Code.left, PRA.eval_left, constant_value 1]

fol_theorem first_body_program_value (e : Nat) : PRA ⊢ ∀ a b,
    eval[firstBodyProgram e](pair(a, b)) = (firstBodyAt e)(a) := by
  rw [firstBodyProgram]
  pintro a b
  prw [equation_program_value (appProgram e firstPairTermProgram)
      (Primrec.Code.comp e firstArgumentsProgram), app_program_value e
      firstPairTermProgram, PRA.eval_comp e
      firstArgumentsProgram, first_pair_term_value, first_arguments_value]

fol_theorem first_result_program_value (e : Nat) : PRA ⊢ ∀ a b,
    eval[firstResultProgram e](pair(a, b)) = (firstResultAt e)(a) := by
  rw [firstResultProgram]
  pintro a b
  prw [PRA.eval_comp Formula.all.code (firstBodyProgram e), first_body_program_value e]

fol_theorem final_result_program_value (e : Nat) : PRA ⊢ ∀ a b,
    eval[finalResultProgram e](pair(a, b)) = (finalResultAt e)(a, b) := by
  rw [finalResultProgram]
  pintro a b
  prw [equation_program_value (appProgram e pairTermNumProgram) (numAtProgram e),
    app_program_value e pairTermNumProgram, pair_term_num_value, num_at_program_value e]

def firstProofProgram (e body p : Nat) : Nat :=
  oneProgram (instanceUniversalProgram (Formula.all body))
    (firstResultProgram e) (Primrec.Code.const p)

def axiomProgram (e body p : Nat) : Nat :=
  oneProgram (firstResultProgram e) (finalResultProgram e) (firstProofProgram e body p)

fol_def firstProofAt over PRA (e body p : Nat) : term of 1 := fun a =>
  eval[EqualityRules.applyOne.code](pair(eval[Formula.all.code](${num (Formula.all body)}),
    pair((firstResultAt e)(a), ${num p})))

fol_def axiomProofAt over PRA (e body p : Nat) : term of 2 := fun a b =>
  eval[EqualityRules.applyOne.code](pair((firstResultAt e)(a),
    pair((finalResultAt e)(a, b), (firstProofAt e body p)(a))))

fol_theorem first_proof_program_value (e body p : Nat) : PRA ⊢ ∀ a b,
    eval[firstProofProgram e body p](pair(a, b)) =
      (firstProofAt e body p)(a) := by
  rw [firstProofProgram]
  pintro a b
  prw [one_program_value (instanceUniversalProgram (Formula.all body)) (firstResultProgram e)
      (Primrec.Code.const p), instance_universal_value
      (Formula.all body), first_result_program_value e, constant_value p]

fol_theorem axiom_program_value (e body p : Nat) : PRA ⊢ ∀ a b,
    eval[axiomProgram e body p](pair(a, b)) =
      (axiomProofAt e body p)(a, b) := by
  rw [axiomProgram]
  pintro a b
  prw [one_program_value (firstResultProgram e) (finalResultProgram e)
      (firstProofProgram e body p), first_result_program_value e, final_result_program_value
      e, first_proof_program_value e body p]

fol_theorem lower_first (e : Nat) : PRA ⊢ ∀ A t u y,
    eval[sub.code](pair(t, eval[Formula.imp.code](pair(A,
      eval[Formula.all.code]((projectionAt e)(t, u, y)))))) = zero := by
  pintro A t u y
  papply Pair.term_le_of_lt_chain_inner[t, Pair.pairTermCode(t, u),
    eval[Formula.imp.code](pair(A, eval[Formula.all.code]((projectionAt e)(t, u, y))))]
  · pexact Pair.left_lt_pair_term_inner[syntaxLanguage(), succ(zero), t, u]
  · papply Pair.term_le_of_lt_chain_inner[Pair.pairTermCode(t, u),
      applicationCode(${num e}, Pair.pairTermCode(t, u)),
      eval[Formula.imp.code](pair(A, eval[Formula.all.code]((projectionAt e)(t, u, y))))]
    · pexact FOL.PRA.term_args_lt_app[syntaxLanguage(), evalSymbolAtLanguage(${num e}),
        Pair.pairTermCode(t, u)]
    · papply Pair.le_chain_inner[applicationCode(${num e}, Pair.pairTermCode(t, u)),
        (projectionAt e)(t, u, y),
        eval[Formula.imp.code](pair(A, eval[Formula.all.code]((projectionAt e)(t, u, y))))]
      · pexact FOL.PRA.formula_le_equal_left[syntaxLanguage(),
          applicationCode(${num e}, Pair.pairTermCode(t, u)), y]
      · papply Pair.term_le_of_lt_chain_inner[(projectionAt e)(t, u, y),
          eval[Formula.all.code]((projectionAt e)(t, u, y)),
          eval[Formula.imp.code](pair(A, eval[Formula.all.code]((projectionAt e)(t, u, y))))]
        · pexact Pair.body_lt_all_inner[(projectionAt e)(t, u, y)]
        · pexact Pair.imp_right_le_inner[A,
            eval[Formula.all.code]((projectionAt e)(t, u, y))]

fol_theorem lower_second (e : Nat) : PRA ⊢ ∀ A t u y,
    eval[sub.code](pair(u, eval[Formula.imp.code](pair(A,
      (projectionAt e)(t, u, y))))) = zero := by
  pintro A t u y
  papply Pair.term_le_of_lt_chain_inner[u, Pair.pairTermCode(t, u),
    eval[Formula.imp.code](pair(A, (projectionAt e)(t, u, y)))]
  · pexact Pair.right_lt_pair_term_inner[syntaxLanguage(), succ(zero), t, u]
  · papply Pair.term_le_of_lt_chain_inner[Pair.pairTermCode(t, u),
      applicationCode(${num e}, Pair.pairTermCode(t, u)),
      eval[Formula.imp.code](pair(A, (projectionAt e)(t, u, y)))]
    · pexact FOL.PRA.term_args_lt_app[syntaxLanguage(), evalSymbolAtLanguage(${num e}),
        Pair.pairTermCode(t, u)]
    · pexact Pair.term_le_in_imp_inner[syntaxLanguage(),
        applicationCode(${num e}, Pair.pairTermCode(t, u)), y, A]

fol_theorem isProofOf_projection_axiom (e body p : Nat) : PRA ⊢
    (projectionSubstitutions e body) →
    praProofOf eval[Formula.all.code](${num (Formula.all body)}) ${num p} →
    (provesProjection e (axiomProgram e body p)) := by
  pintro substitutes universal a b
  pcases substitutes with ⟨firstSubstitution, secondSubstitution⟩
  phave firstProof : (praProofOf (firstResultAt e)(a)
      (firstProofAt e body p)(a))
  · papply (EqualityRules.applyOne_accepted language isAxiom.code)[
      eval[Formula.all.code](${num (Formula.all body)}), (firstResultAt e)(a), ${num p}]
    · papply (Pair.instantiation_membership_inner language)[${num (Formula.all body)},
        numCode(a), (firstResultAt e)(a)]
      · pexact firstSubstitution[a]
      · pexact (lower_first e)[eval[Formula.all.code](${num (Formula.all body)}), numCode(a),
          ${num 1}, eval[e](pair(numCode(a), ${num 1}))]
    · pexact universal
  phave initial : (praProofOf (finalResultAt e)(a, b)
      (axiomProofAt e body p)(a, b))
  · papply (EqualityRules.applyOne_accepted language isAxiom.code)[(firstResultAt e)(a),
      (finalResultAt e)(a, b), (firstProofAt e body p)(a)]
    · papply (Pair.instantiation_membership_inner language)[(firstBodyAt e)(a),
        numCode(b), (finalResultAt e)(a, b)]
      · pexact secondSubstitution[a, b]
      · pexact (lower_second e)[(firstResultAt e)(a), numCode(a), numCode(b),
          numCode(eval[e](pair(a, b)))]
    · pexact firstProof
  phave witness : eval[axiomProgram e body p](pair(a, b)) =
      (axiomProofAt e body p)(a, b)
  · pexact (axiom_program_value e body p)[a, b]
  pcases initial with ⟨accepted, conclusion⟩
  pconstructor
  · ptrans praIsProof(
      (axiomProofAt e body p)(a, b))
    · prw [witness]
    · pexact accepted
  · ptrans eval[Proof.conclusion.code]((axiomProofAt e body p)(a, b))
    · prw [witness]
    · pexact conclusion

fol_def quotedPairCode over PRA : term of 2 := fun a b =>
  eval[Term.app.code](pair(${num language}, pair(${num 1}, eval[pair.code](pair(a, b)))))

fol_def quotedProjection over PRA (e : Nat) : term of 3 := fun a b y =>
  Pair.equalCode(FOL.PRA.evalApplication(${num e}, quotedPairCode(a, b)), y)

fol_def projectionEquation over PRA : term of 4 := fun e a b y =>
  Pair.equalCode(FOL.PRA.evalApplication(e, Pair.pairCode(a, b)), y)

theorem quoted_body_value (e v : Nat) :
    (PRA ⊢ (quotedProjection e)(${num 5}, ${num 1}, ${num (Term.var language v)}) =
      ${num (projectionBody e v)}) := by
  let a := Term.var language 1
  let b := Term.var language 0
  let ab := Term.app language 1 (pair a b)
  let lhs := Term.app language (Language.functionFamilyMember language 0 e) ab
  have leftVariable : (PRA ⊢ ${num 5} = ${num a}) :=
    Evaluation.symm _ _ (num_eq_of_eq a 5 var_one_language)
  have rightVariable : (PRA ⊢ ${num 1} = ${num b}) :=
    Evaluation.symm _ _ (num_eq_of_eq b 1 var_zero_language)
  have argument : (PRA ⊢ quotedPairCode(${num 5}, ${num 1}) = ${num ab}) := by
    ptrans Pair.pairCode(${num a}, ${num b})
    · prw [leftVariable, rightVariable, num_one]
    · pexact Pair.pair_value a b
  ptrans Pair.equalCode(${num lhs}, ${num (Term.var language v)})
  · prw [argument, Composition.application_value e ab]
  · have code : projectionBody e v = Formula.equal language lhs (Term.var language v) := rfl
    rw [code]
    pexact Pair.equal_value lhs (Term.var language v)

theorem quoted_forall_body_value (e v : Nat) :
    (PRA ⊢ eval[Formula.all.code]((quotedProjection e)(${num 5}, ${num 1},
      ${num (Term.var language v)})) = ${num (Formula.all (projectionBody e v))}) := by
  ptrans eval[Formula.all.code](${num (projectionBody e v)})
  · prw [quoted_body_value e v]
  · pexact Pair.all_value (projectionBody e v)

fol_theorem left_universal : PRA ⊢ ∀ a b, eval[Primrec.Code.left](pair(a, b)) = a := by
  pexact PRA.eval_left

fol_theorem right_universal : PRA ⊢ ∀ a b, eval[Primrec.Code.right](pair(a, b)) = b := by
  pexact PRA.eval_right

extract_witness left_universal right_universal

theorem universal_accepted (body p : Nat) :
    IsProofOf language isAxiom (Formula.all (Formula.all body)) p →
    (PRA ⊢ praProofOf eval[Formula.all.code](${num (Formula.all body)}) ${num p}) := by
  intro valid
  have accepts := praIsProof_on_num p (and_left valid)
  have concludes := eval_num_of_evaluates Proof.conclusion.code p (Proof.conclusion p)
    (Proof.conclusion.trace p) (Proof.conclusion.computedBy p)
  rw [and_right valid] at concludes
  pconstructor
  · exact accepts
  · ptrans ${num (Formula.all (Formula.all body))}
    · exact concludes
    · psymm
      exact Pair.all_value (Formula.all body)

fol_theorem left_first_shifted : PRA ⊢ ∀ t,
    eval[Formula.instantiate.code](pair(${num language}, pair(eval[Formula.all.code](
      (quotedProjection Primrec.Code.left)(${num 5}, ${num 1}, ${num 5})), t))) =
    eval[Formula.all.code]((quotedProjection Primrec.Code.left)(
      NumShift.shiftOneCode(t), ${num 1},
        NumShift.shiftOneCode(t))) := by
  have code : Primrec.Code.left = 2 := rfl
  rw [code]
  pintro t
  ptrans eval[Formula.instantiate.code](pair(${num language},
    pair(eval[Formula.all.code](projectionEquation(succ(succ(zero)),
      succ(succ(succ(succ(succ(zero))))), succ(zero), succ(succ(succ(succ(succ(zero))))))), t)))
  · prw [num_two, num_five, num_one]
  · ptrans eval[Formula.all.code](projectionEquation(succ(succ(zero)),
      Pair.shiftedOne(t), succ(zero), Pair.shiftedOne(t)))
    · papply Substitution.instantiate_left_first_inner[${num language}, t]
      pexact Evaluation.symm _ _ eval_language_code
    · prw [num_two, num_one]

fol_theorem right_first_shifted : PRA ⊢ ∀ t,
    eval[Formula.instantiate.code](pair(${num language}, pair(eval[Formula.all.code](
      (quotedProjection Primrec.Code.right)(${num 5}, ${num 1}, ${num 1})), t))) =
    eval[Formula.all.code]((quotedProjection Primrec.Code.right)(
      NumShift.shiftOneCode(t), ${num 1}, ${num 1})) := by
  have code : Primrec.Code.right = 3 := rfl
  rw [code]
  pintro t
  ptrans eval[Formula.instantiate.code](pair(${num language},
    pair(eval[Formula.all.code](projectionEquation(succ(succ(succ(zero))),
      succ(succ(succ(succ(succ(zero))))), succ(zero), succ(zero))), t)))
  · prw [num_three, num_five, num_one]
  · ptrans eval[Formula.all.code](projectionEquation(succ(succ(succ(zero))),
      Pair.shiftedOne(t), succ(zero), succ(zero)))
    · papply Substitution.instantiate_right_first_inner[${num language}, t]
      pexact Evaluation.symm _ _ eval_language_code
    · prw [num_three, num_one]

fol_theorem left_second_shifted : PRA ⊢ ∀ a t,
    eval[Formula.instantiate.code](pair(${num language}, pair(
      (quotedProjection Primrec.Code.left)(numCode(a), ${num 1}, numCode(a)), t))) =
    (quotedProjection Primrec.Code.left)(numCode(a), shiftZeroCode(t), numCode(a)) := by
  have code : Primrec.Code.left = 2 := rfl
  rw [code]
  pintro a t
  ptrans eval[Formula.instantiate.code](pair(${num language},
    pair(projectionEquation(succ(succ(zero)), numCode(a), succ(zero), numCode(a)), t)))
  · prw [num_two, num_one]
  · ptrans projectionEquation(succ(succ(zero)), numCode(a), shiftZeroCode(t), numCode(a))
    · papply Substitution.instantiate_left_second_inner[${num language}, a, t]
      pexact Evaluation.symm _ _ eval_language_code
    · prw [num_two, num_one]

fol_theorem right_second_shifted : PRA ⊢ ∀ a t,
    eval[Formula.instantiate.code](pair(${num language}, pair(
      (quotedProjection Primrec.Code.right)(numCode(a), ${num 1}, ${num 1}), t))) =
    (quotedProjection Primrec.Code.right)(numCode(a), shiftZeroCode(t), shiftZeroCode(t)) := by
  have code : Primrec.Code.right = 3 := rfl
  rw [code]
  pintro a t
  ptrans eval[Formula.instantiate.code](pair(${num language},
    pair(projectionEquation(succ(succ(succ(zero))), numCode(a), succ(zero), succ(zero)), t)))
  · prw [num_three, num_one]
  · ptrans projectionEquation(succ(succ(succ(zero))), numCode(a),
      shiftZeroCode(t), shiftZeroCode(t))
    · papply Substitution.instantiate_right_second_inner[${num language}, a, t]
      pexact Evaluation.symm _ _ eval_language_code
    · prw [num_three, num_one]

fol_theorem left_substitutions : PRA ⊢
    (projectionSubstitutions Primrec.Code.left (projectionBody Primrec.Code.left 1)) := by
  pconstructor
  · pintro a
    have variableCode : Term.var language 1 = 5 := var_one_language
    have formulaCode := quoted_forall_body_value Primrec.Code.left 1
    rw [variableCode] at formulaCode
    ptrans eval[Formula.instantiate.code](pair(${num language}, pair(eval[Formula.all.code](
      (quotedProjection Primrec.Code.left)(${num 5}, ${num 1}, ${num 5})), numCode(a))))
    · prw [eval_const_language, formulaCode]
    · ptrans eval[Formula.all.code]((quotedProjection Primrec.Code.left)(
        NumShift.shiftOneCode(numCode(a)), ${num 1},
        NumShift.shiftOneCode(numCode(a))))
      · pexact left_first_shifted[numCode(a)]
      · phave shift : NumShift.shiftOneCode(numCode(a)) = numCode(a)
        · pexact NumShift.shift_one_num[a]
        prw [shift, eval_const_language, num_one, PRA.eval_left]
  · pintro a b
    ptrans eval[Formula.instantiate.code](pair(${num language}, pair(
      (quotedProjection Primrec.Code.left)(numCode(a), ${num 1}, numCode(a)),
      numCode(b))))
    · prw [eval_const_language, num_one, PRA.eval_left]
    · ptrans (quotedProjection Primrec.Code.left)(numCode(a), shiftZeroCode(numCode(b)),
        numCode(a))
      · pexact left_second_shifted[a, numCode(b)]
      · phave shift : shiftZeroCode(numCode(b)) = numCode(b)
        · pexact shift_num[b]
        prw [shift, eval_const_language, num_one, PRA.eval_left]

def leftProofProgram (p : Nat) : Nat :=
  projectionProofProgram Primrec.Code.left
    (axiomProgram Primrec.Code.left (projectionBody Primrec.Code.left 1)
      left_universal.witness) p

fol_theorem provesEval_left (p : Nat) : PRA ⊢ (recognizesCongruence Primrec.Code.left) →
    (provesPair p) → (provesEval Primrec.Code.left (leftProofProgram p)) := by
  rw [leftProofProgram]
  pintro recognized paired
  papply provesEval_projection Primrec.Code.left
      (axiomProgram Primrec.Code.left
      (projectionBody Primrec.Code.left 1) left_universal.witness) p
  · pexact recognized
  · papply isProofOf_projection_axiom Primrec.Code.left
      (projectionBody Primrec.Code.left 1) left_universal.witness
    · pexact left_substitutions
    · pexact universal_accepted
        (projectionBody Primrec.Code.left 1) left_universal.witness left_universal.witness_correct
  · pexact paired

fol_theorem right_substitutions : PRA ⊢
    (projectionSubstitutions Primrec.Code.right (projectionBody Primrec.Code.right 0)) := by
  pconstructor
  · pintro a
    have variableCode : Term.var language 0 = 1 := var_zero_language
    have formulaCode := quoted_forall_body_value Primrec.Code.right 0
    rw [variableCode] at formulaCode
    ptrans eval[Formula.instantiate.code](pair(${num language}, pair(eval[Formula.all.code](
      (quotedProjection Primrec.Code.right)(${num 5}, ${num 1}, ${num 1})), numCode(a))))
    · prw [eval_const_language, formulaCode]
    · ptrans eval[Formula.all.code]((quotedProjection Primrec.Code.right)(
        NumShift.shiftOneCode(numCode(a)), ${num 1}, ${num 1}))
      · pexact right_first_shifted[numCode(a)]
      · phave shift : NumShift.shiftOneCode(numCode(a)) = numCode(a)
        · pexact NumShift.shift_one_num[a]
        prw [shift, eval_const_language, num_one, PRA.eval_right]
  · pintro a b
    ptrans eval[Formula.instantiate.code](pair(${num language}, pair(
      (quotedProjection Primrec.Code.right)(numCode(a), ${num 1}, ${num 1}),
      numCode(b))))
    · prw [eval_const_language, num_one, PRA.eval_right]
    · ptrans (quotedProjection Primrec.Code.right)(numCode(a), shiftZeroCode(numCode(b)),
        shiftZeroCode(numCode(b)))
      · pexact right_second_shifted[a, numCode(b)]
      · phave shift : shiftZeroCode(numCode(b)) = numCode(b)
        · pexact shift_num[b]
        prw [shift, eval_const_language, num_one, PRA.eval_right]

def rightProofProgram (p : Nat) : Nat :=
  projectionProofProgram Primrec.Code.right
    (axiomProgram Primrec.Code.right (projectionBody Primrec.Code.right 0)
      right_universal.witness) p

fol_theorem provesEval_right (p : Nat) : PRA ⊢ (recognizesCongruence Primrec.Code.right) →
    (provesPair p) → (provesEval Primrec.Code.right (rightProofProgram p)) := by
  rw [rightProofProgram]
  pintro recognized paired
  papply provesEval_projection Primrec.Code.right
      (axiomProgram Primrec.Code.right
      (projectionBody Primrec.Code.right 0) right_universal.witness) p
  · pexact recognized
  · papply isProofOf_projection_axiom Primrec.Code.right
      (projectionBody Primrec.Code.right 0) right_universal.witness
    · pexact right_substitutions
    · pexact universal_accepted
        (projectionBody Primrec.Code.right 0) right_universal.witness
        right_universal.witness_correct
  · pexact paired

fol_theorem projection_congruence (e : Nat) : PRA ⊢ (recognizesCongruence e) := by
  pintro a b
  pexact EqualityRules.program_congruence_axiom[${num e}, a, b]

fol_theorem provesEval_left_from_pair (p : Nat) : PRA ⊢ (provesPair p) →
    (provesEval Primrec.Code.left (leftProofProgram p)) := by
  pintro paired
  papply provesEval_left p
  · pexact projection_congruence Primrec.Code.left
  · pexact paired

fol_theorem provesEval_right_from_pair (p : Nat) : PRA ⊢ (provesPair p) →
    (provesEval Primrec.Code.right (rightProofProgram p)) := by
  pintro paired
  papply provesEval_right p
  · pexact projection_congruence Primrec.Code.right
  · pexact paired

end EquationCompleteness.Projection

namespace EquationCompleteness

theorem left_pair_exists : ∃ c, EquationProofPair Primrec.Code.left c := by
  let p := Pair.pairProofProgram
  have proof := Provable.mp language isAxiom _ _ (Projection.provesEval_left_from_pair p)
    provesPair_of_program
  rcases proof with (q, valid)
  exact (pair (Projection.leftProofProgram p) q, equationProofPair_pair Primrec.Code.left _ q valid)

theorem right_pair_exists : ∃ c, EquationProofPair Primrec.Code.right c := by
  let p := Pair.pairProofProgram
  have proof := Provable.mp language isAxiom _ _ (Projection.provesEval_right_from_pair p)
    provesPair_of_program
  rcases proof with (q, valid)
  exact (pair (Projection.rightProofProgram p) q,
    equationProofPair_pair Primrec.Code.right _ q valid)

end EquationCompleteness

/-! ### Pairing two programs -/

namespace EquationCompleteness.Pairing

open NumShift Composition Projection

fol_def pairEquation over PRA : term of 4 := fun e f g t =>
  equalityCode(applicationCode(e, t),
    Pair.pairTermCode(applicationCode(f, t), applicationCode(g, t)))

fol_def quotedEquation over PRA : term of 4 := fun e f g t =>
  Pair.equalCode(FOL.PRA.evalApplication(e, t),
    quotedPairCode(FOL.PRA.evalApplication(f, t), FOL.PRA.evalApplication(g, t)))

fol_def pairEquationAt over PRA : term of 4 := fun e f g t =>
  Pair.equalCode(FOL.PRA.evalApplication(e, t),
    Pair.pairCode(FOL.PRA.evalApplication(f, t), FOL.PRA.evalApplication(g, t)))

def body (f g : Nat) : Nat :=
  let t := Term.var language 0;
  fol_formula[PRA | eval[Primrec.Code.pair f g](${t}) = pair(eval[f](${t}), eval[g](${t}))]

fol_theorem pair_universal (f g : Nat) : PRA ⊢ ∀ x,
    eval[Primrec.Code.pair f g](x) = pair(eval[f](x), eval[g](x)) := by
  pexact PRA.eval_pair f g

extract_witness pair_universal

theorem pair_universal_accepted (f g : Nat) :
    (PRA ⊢ (praProofOf eval[Formula.all.code](${num (body f g)})
      ${num (pair_universal.witness f g)})) := by
  let p := pair_universal.witness f g
  have valid : IsProofOf language isAxiom (Formula.all (body f g)) p :=
    pair_universal.witness_correct f g
  have accepts := praIsProof_on_num p (and_left valid)
  have concludes := eval_num_of_evaluates Proof.conclusion.code p (Proof.conclusion p)
    (Proof.conclusion.trace p) (Proof.conclusion.computedBy p)
  rw [and_right valid] at concludes
  pconstructor
  · exact accepts
  · ptrans ${num (Formula.all (body f g))}
    · exact concludes
    · psymm
      exact Pair.all_value (body f g)

theorem quoted_body_value (f g : Nat) :
    (PRA ⊢ quotedEquation(${num (Primrec.Code.pair f g)}, ${num f}, ${num g}, ${num 1}) =
      ${num (body f g)}) := by
  let t := Term.var language 0
  let c := Primrec.Code.pair f g
  let u := Term.app language (Language.functionFamilyMember language 0 c) t
  let l := Term.app language (Language.functionFamilyMember language 0 f) t
  let r := Term.app language (Language.functionFamilyMember language 0 g) t
  let v := Term.app language 1 (pair l r)
  have variableCode : (PRA ⊢ ${num 1} = ${num t}) :=
    Evaluation.symm _ _ (num_eq_of_eq t 1 var_zero_language)
  have rightValue : (PRA ⊢ quotedPairCode(FOL.PRA.evalApplication(${num f}, ${num t}),
      FOL.PRA.evalApplication(${num g}, ${num t})) = ${num v}) := by
    ptrans Pair.pairCode(${num l}, ${num r})
    · prw [num_one, Composition.application_value f t, Composition.application_value g t]
    · pexact Pair.pair_value l r
  ptrans Pair.equalCode(${num u}, ${num v})
  · prw [variableCode, Composition.application_value c t, rightValue]
  · have code : body f g = Formula.equal language u v := rfl
    rw [code]
    pexact Pair.equal_value u v

fol_theorem quoted_substitution : PRA ⊢ ∀ c f g t,
    eval[Formula.instantiate.code](pair(${num language}, pair(quotedEquation(c, f, g, ${num 1}),
      t))) = quotedEquation(c, f, g, shiftZeroCode(t)) := by
  pintro c f g t
  ptrans eval[Formula.instantiate.code](pair(${num language},
    pair(pairEquationAt(c, f, g, succ(zero)), t)))
  · prw [num_one]
  · ptrans pairEquationAt(c, f, g, shiftZeroCode(t))
    · papply Substitution.instantiate_pair_equation_inner[${num language}, c, f, g, t]
      pexact Evaluation.symm _ _ eval_language_code
    · prw [num_one]

fol_theorem pair_substitution_at_num (f g : Nat) : PRA ⊢ ∀ x,
    eval[Formula.instantiate.code](pair(syntaxLanguage(),
      pair(${num (body f g)}, numCode(x)))) =
    pairEquation(${num (Primrec.Code.pair f g)}, ${num f}, ${num g}, numCode(x)) := by
  pintro x
  ptrans eval[Formula.instantiate.code](pair(${num language}, pair(
    quotedEquation(${num (Primrec.Code.pair f g)}, ${num f}, ${num g}, ${num 1}), numCode(x))))
  · prw [eval_const_language, quoted_body_value f g]
  · ptrans quotedEquation(${num (Primrec.Code.pair f g)}, ${num f}, ${num g},
      shiftZeroCode(numCode(x)))
    · pexact quoted_substitution[
        ${num (Primrec.Code.pair f g)}, ${num f}, ${num g}, numCode(x)]
    · phave shift : shiftZeroCode(numCode(x)) = numCode(x)
      · pexact shift_num[x]
      prw [shift, eval_const_language, num_one]

def axiomLeftProgram (f g : Nat) : Nat := appProgram (Primrec.Code.pair f g) num.code

def axiomRightProgram (f g : Nat) : Nat :=
  pairTermProgram (appProgram f num.code) (appProgram g num.code)

def axiomInstanceProgram (f g : Nat) : Nat :=
  instanceProofProgram (equationProgram (axiomLeftProgram f g) (axiomRightProgram f g))
    (body f g) (pair_universal.witness f g)

fol_def leftAt over PRA (f g : Nat) : term of 1 := fun x =>
  applicationCode(${num (Primrec.Code.pair f g)}, numCode(x))

fol_def middleAt over PRA (f g : Nat) : term of 1 := fun x =>
  Pair.pairTermCode(applicationCode(${num f}, numCode(x)),
    applicationCode(${num g}, numCode(x)))

fol_def pairAt over PRA (f g : Nat) : term of 1 := fun x =>
  Pair.pairTermCode(numCode(eval[f](x)), numCode(eval[g](x)))

fol_def outputAt over PRA (f g : Nat) : term of 1 := fun x =>
  numCode(pair(eval[f](x), eval[g](x)))

fol_def axiomInstanceAt over PRA (f g : Nat) : term of 1 := fun x =>
  (instanceProofAt (body f g) (pair_universal.witness f g))(
    pairEquation(${num (Primrec.Code.pair f g)}, ${num f}, ${num g}, numCode(x)))

fol_theorem axiom_left_value (f g : Nat) : PRA ⊢ ∀ x,
    eval[axiomLeftProgram f g](x) = (leftAt f g)(x) := by
  rw [axiomLeftProgram]
  pintro x
  prw [app_program_value (Primrec.Code.pair f g) num.code]

fol_theorem axiom_right_value (f g : Nat) : PRA ⊢ ∀ x,
    eval[axiomRightProgram f g](x) = (middleAt f g)(x) := by
  rw [axiomRightProgram]
  pintro x
  prw [pair_term_program_value (appProgram f num.code) (appProgram g num.code),
    app_program_value f num.code, app_program_value g num.code]

fol_theorem axiom_instance_value (f g : Nat) : PRA ⊢ ∀ x,
    eval[axiomInstanceProgram f g](x) = (axiomInstanceAt f g)(x) := by
  rw [axiomInstanceProgram]
  pintro x
  prw [instance_program (equationProgram (axiomLeftProgram f g) (axiomRightProgram f g)) (body f g)
      (pair_universal.witness f g), equation_program_value (axiomLeftProgram f g)
      (axiomRightProgram f g), axiom_left_value f g, axiom_right_value f g]

fol_theorem axiom_instance_accepted (f g : Nat) : PRA ⊢ ∀ x,
    (praProofOf equalityCode((leftAt f g)(x), (middleAt f g)(x))
      (axiomInstanceAt f g)(x)) := by
  pintro x
  papply (praProofOf_equal_app_of_instantiate language isAxiom.code)[${num (body f g)},
    evalSymbolAtLanguage(${num (Primrec.Code.pair f g)}), numCode(x),
    (middleAt f g)(x), ${num (pair_universal.witness f g)}]
  · pexact (pair_substitution_at_num f g)[x]
  · pexact pair_universal_accepted f g

fol_def pairCongruenceProof over PRA : term of 6 := fun a b c d p q =>
  eval[EqualityRules.applyTwo.code](pair(equalityCode(a, c),
    pair(equalityCode(b, d),
      pair(equalityCode(Pair.pairTermCode(a, b), Pair.pairTermCode(c, d)), pair(p, q)))))

fol_theorem pair_congruence_accepted : PRA ⊢ ∀ a b c d p q,
    praProofOf equalityCode(a, c) p → praProofOf equalityCode(b, d) q →
    (praProofOf equalityCode(Pair.pairTermCode(a, b), Pair.pairTermCode(c, d))
      pairCongruenceProof(a, b, c, d, p, q)) := by
  pintro a b c d p q lhs rhs
  papply (EqualityRules.applyTwo_accepted language isAxiom.code)[equalityCode(a, c),
    equalityCode(b, d),
    equalityCode(Pair.pairTermCode(a, b), Pair.pairTermCode(c, d)), p, q]
  · pexact EqualityRules.pair_congruence_axiom[a, b, c, d]
  · pexact lhs
  · pexact rhs

def pairCongruenceProgram (a b c d p q : Nat) : Nat :=
  twoProgram (equationProgram a c) (equationProgram b d)
    (equationProgram (pairTermProgram a b) (pairTermProgram c d)) p q

fol_theorem pair_congruence_program_value (a b c d p q : Nat) : PRA ⊢ ∀ x,
    eval[pairCongruenceProgram a b c d p q](x) =
      pairCongruenceProof(eval[a](x), eval[b](x), eval[c](x), eval[d](x),
        eval[p](x), eval[q](x)) := by
  rw [pairCongruenceProgram]
  pintro x
  prw [two_program_value (equationProgram a c) (equationProgram b d)
      (equationProgram (pairTermProgram a b) (pairTermProgram c d)) p q,
    equation_program_value a c, equation_program_value b d,
    equation_program_value (pairTermProgram a b) (pairTermProgram c d),
    pair_term_program_value a b, pair_term_program_value c d]

def childPairProgram (f g : Nat) : Nat := pairTermProgram (numAtProgram f) (numAtProgram g)

def outputProgram (f g : Nat) : Nat := numAtProgram (Primrec.Code.pair f g)

def childCongruenceProgram (f g qf qg : Nat) : Nat :=
  pairCongruenceProgram (appProgram f num.code) (appProgram g num.code)
    (numAtProgram f) (numAtProgram g) qf qg

def pairWitnessProgram (f g p : Nat) : Nat := Primrec.Code.comp p (Primrec.Code.pair f g)

def tailProgram (f g qf qg p : Nat) : Nat :=
  transitivityProgram (axiomRightProgram f g) (childPairProgram f g) (outputProgram f g)
    (childCongruenceProgram f g qf qg) (pairWitnessProgram f g p)

def pairProofProgram (f g qf qg p : Nat) : Nat :=
  transitivityProgram (axiomLeftProgram f g) (axiomRightProgram f g) (outputProgram f g)
    (axiomInstanceProgram f g) (tailProgram f g qf qg p)

fol_def childProofAt over PRA (f g qf qg : Nat) : term of 1 := fun x =>
  pairCongruenceProof(applicationCode(${num f}, numCode(x)),
    applicationCode(${num g}, numCode(x)), numCode(eval[f](x)), numCode(eval[g](x)),
    eval[qf](x), eval[qg](x))

fol_def tailAt over PRA (f g qf qg p : Nat) : term of 1 := fun x =>
  transitivityProof((middleAt f g)(x), (pairAt f g)(x),
    (outputAt f g)(x), (childProofAt f g qf qg)(x),
    eval[p](pair(eval[f](x), eval[g](x))))

fol_def pairProofAt over PRA (f g qf qg p : Nat) : term of 1 := fun x =>
  transitivityProof((leftAt f g)(x), (middleAt f g)(x),
    (outputAt f g)(x), (axiomInstanceAt f g)(x),
    (tailAt f g qf qg p)(x))

fol_theorem child_pair_value (f g : Nat) : PRA ⊢ ∀ x,
    eval[childPairProgram f g](x) = (pairAt f g)(x) := by
  rw [childPairProgram]
  pintro x
  prw [pair_term_program_value (numAtProgram f) (numAtProgram g),
    num_at_program_value f, num_at_program_value g]

fol_theorem output_value (f g : Nat) : PRA ⊢ ∀ x,
    eval[outputProgram f g](x) = (outputAt f g)(x) := by
  rw [outputProgram]
  pintro x
  prw [num_at_program_value (Primrec.Code.pair f g), PRA.eval_pair f g]

fol_theorem child_congruence_value (f g qf qg : Nat) : PRA ⊢ ∀ x,
    eval[childCongruenceProgram f g qf qg](x) =
      (childProofAt f g qf qg)(x) := by
  rw [childCongruenceProgram]
  pintro x
  prw [pair_congruence_program_value (appProgram f num.code) (appProgram g num.code)
      (numAtProgram f)
      (numAtProgram g) qf qg, app_program_value f num.code, app_program_value g
      num.code, num_at_program_value f, num_at_program_value g]

fol_theorem pair_witness_value (f g p : Nat) : PRA ⊢ ∀ x,
    eval[pairWitnessProgram f g p](x) = eval[p](pair(eval[f](x), eval[g](x))) := by
  rw [pairWitnessProgram]
  pexact eval_comp_pair p f g

fol_theorem tail_value (f g qf qg p : Nat) : PRA ⊢ ∀ x,
    eval[tailProgram f g qf qg p](x) =
      (tailAt f g qf qg p)(x) := by
  rw [tailProgram]
  pintro x
  prw [transitivity_program_value (axiomRightProgram f g) (childPairProgram f g)
      (outputProgram f g) (childCongruenceProgram f g qf qg)
      (pairWitnessProgram f g p), axiom_right_value f g, child_pair_value f g, output_value f
      g, child_congruence_value f g qf qg, pair_witness_value f g p]

fol_theorem pair_proof_program_value (f g qf qg p : Nat) : PRA ⊢ ∀ x,
    eval[pairProofProgram f g qf qg p](x) =
      (pairProofAt f g qf qg p)(x) := by
  rw [pairProofProgram]
  pintro x
  prw [transitivity_program_value (axiomLeftProgram f g) (axiomRightProgram f g)
      (outputProgram f g) (axiomInstanceProgram f g)
      (tailProgram f g qf qg p), axiom_left_value f g, axiom_right_value f g, output_value f
      g, axiom_instance_value f g, tail_value f g qf qg p]

fol_theorem provesEval_pair (p f g qf qg : Nat) : PRA ⊢ (provesPair p) →
    (provesEval f qf) → (provesEval g qg) →
    (provesEval (Primrec.Code.pair f g) (pairProofProgram f g qf qg p)) := by
  pintro paired hf hg x
  papply (equationProofOf_of_eq (Primrec.Code.pair f g))[x, eval[Primrec.Code.pair f g](x),
    eval[pairProofProgram f g qf qg p](x), x, pair(eval[f](x), eval[g](x)),
    (pairProofAt f g qf qg p)(x)]
  · prefl
  · pexact (PRA.eval_pair f g)[x]
  · pexact (pair_proof_program_value f g qf qg p)[x]
  · papply transitivity_rule[(leftAt f g)(x), (middleAt f g)(x),
      (outputAt f g)(x), (axiomInstanceAt f g)(x),
      (tailAt f g qf qg p)(x)]
    · pexact (axiom_instance_accepted f g)[x]
    · papply transitivity_rule[(middleAt f g)(x), (pairAt f g)(x),
        (outputAt f g)(x), (childProofAt f g qf qg)(x),
        eval[p](pair(eval[f](x), eval[g](x)))]
      · papply pair_congruence_accepted[applicationCode(${num f}, numCode(x)),
          applicationCode(${num g}, numCode(x)), numCode(eval[f](x)),
          numCode(eval[g](x)), eval[qf](x), eval[qg](x)]
        · pexact hf[x]
        · pexact hg[x]
      · pexact paired[eval[f](x), eval[g](x)]

end EquationCompleteness.Pairing

namespace EquationCompleteness

theorem pair_proofs (f g a b : Nat) : EquationProofPair f a → EquationProofPair g b →
    (PRA ⊢ (provesEval ${Primrec.Code.pair f g} ${Pairing.pairProofProgram f g (unpairLeft a)
    (unpairLeft b) Pair.pairProofProgram})) := by
  intro hf hg
  let p := Pair.pairProofProgram
  have branch := Pairing.provesEval_pair p f g (unpairLeft a) (unpairLeft b)
  have withPair := Provable.mp language isAxiom _ _ branch provesPair_of_program
  have withLeft := Provable.mp language isAxiom _ _ withPair (unpairRight a, hf)
  exact Provable.mp language isAxiom _ _ withLeft (unpairRight b, hg)

theorem pair_pair_exists : ∀ f g a b,
    EquationProofPair f a → EquationProofPair g b →
    ∃ c, EquationProofPair (Primrec.Code.pair f g) c := by
  intro f g a b ha hb
  let k := Pairing.pairProofProgram f g (unpairLeft a) (unpairLeft b) Pair.pairProofProgram
  rcases pair_proofs f g a b ha hb with (p, hp)
  exact (_root_.pair k p, equationProofPair_pair (Primrec.Code.pair f g) k p hp)

end EquationCompleteness

/-! ### Primitive recursion

The proof program uses induction on the recursion counter.
-/

namespace EquationCompleteness.Recursion

open NumShift Composition Projection

def baseProofProgram (f qf make : Nat) : Nat :=
  Primrec.Code.comp make (Primrec.Code.pair Primrec.Code.id (Primrec.Code.pair f qf))

def stepIndexProgram : Nat := Primrec.Code.comp Primrec.Code.left Primrec.Code.right

def stepPreviousProofProgram : Nat := Primrec.Code.comp Primrec.Code.right Primrec.Code.right

def stepValueProgram (f g : Nat) : Nat :=
  Primrec.Code.comp (Primrec.Code.rec f g) (Primrec.Code.pair Primrec.Code.left stepIndexProgram)

def stepChildInputProgram (f g : Nat) : Nat :=
  Primrec.Code.pair Primrec.Code.left (Primrec.Code.pair stepIndexProgram (stepValueProgram f g))

def stepResultsProgram (f g qg : Nat) : Nat :=
  Primrec.Code.pair (Primrec.Code.comp g (stepChildInputProgram f g))
    (Primrec.Code.pair stepPreviousProofProgram (Primrec.Code.comp qg (stepChildInputProgram f g)))

def stepProofProgram (f g qg make : Nat) : Nat :=
  Primrec.Code.comp make (Primrec.Code.pair Primrec.Code.left (Primrec.Code.pair stepIndexProgram
    (Primrec.Code.pair (stepValueProgram f g) (stepResultsProgram f g qg))))

fol_def previousValue over PRA (f g : Nat) : term of 2 := fun x n =>
  eval[Primrec.Code.rec f g](pair(x, n))

fol_def stepArgument over PRA (f g : Nat) : term of 2 := fun x n =>
  pair(x, pair(n, (previousValue f g)(x, n)))

fol_theorem base_proof_program_value (f qf make : Nat) : PRA ⊢ ∀ x,
    eval[baseProofProgram f qf make](x) = eval[make](pair(x, pair(eval[f](x), eval[qf](x)))) := by
  have code : baseProofProgram f qf make =
    Primrec.Code.comp make (Primrec.Code.pair Primrec.Code.id (Primrec.Code.pair f qf)) := rfl
  rw [code]
  pintro x
  prw [eval_comp_pair make Primrec.Code.id (Primrec.Code.pair f qf),
    FOL.PRA.eval_id, PRA.eval_pair f qf]

fol_theorem step_tail_value (e : Nat) : PRA ⊢ ∀ x n p,
    eval[Primrec.Code.comp e Primrec.Code.right](pair(x, pair(n, p))) = eval[e](pair(n, p)) := by
  pintro x n p
  ptrans eval[e](eval[Primrec.Code.right](pair(x, pair(n, p))))
  · pexact (PRA.eval_comp e Primrec.Code.right)[pair(x, pair(n, p))]
  · pcongr
    pexact PRA.eval_right[x, pair(n, p)]

fol_theorem step_index_value : PRA ⊢ ∀ x n p, eval[stepIndexProgram](pair(x, pair(n, p))) = n := by
  have code : stepIndexProgram = Primrec.Code.comp Primrec.Code.left Primrec.Code.right := rfl
  rw [code]
  pintro x n p
  ptrans eval[Primrec.Code.left](pair(n, p))
  · pexact (step_tail_value Primrec.Code.left)[x, n, p]
  · pexact PRA.eval_left[n, p]

fol_theorem step_previous_proof_value : PRA ⊢ ∀ x n p,
    eval[stepPreviousProofProgram](pair(x, pair(n, p))) = p := by
  have code : stepPreviousProofProgram =
      Primrec.Code.comp Primrec.Code.right Primrec.Code.right := rfl
  rw [code]
  pintro x n p
  ptrans eval[Primrec.Code.right](pair(n, p))
  · pexact (step_tail_value Primrec.Code.right)[x, n, p]
  · pexact PRA.eval_right[n, p]

fol_theorem step_value (f g : Nat) : PRA ⊢ ∀ x n p,
    eval[stepValueProgram f g](pair(x, pair(n, p))) = (previousValue f g)(x, n) := by
  have code : stepValueProgram f g = Primrec.Code.comp (Primrec.Code.rec f g)
      (Primrec.Code.pair Primrec.Code.left stepIndexProgram) := rfl
  rw [code]
  pintro x n p
  prw [eval_comp_pair (Primrec.Code.rec f g) Primrec.Code.left stepIndexProgram,
    PRA.eval_left, step_index_value]

fol_theorem step_child_input_value (f g : Nat) : PRA ⊢ ∀ x n p,
    eval[stepChildInputProgram f g](pair(x, pair(n, p))) =
      (stepArgument f g)(x, n) := by
  have code : stepChildInputProgram f g = Primrec.Code.pair Primrec.Code.left
      (Primrec.Code.pair stepIndexProgram (stepValueProgram f g)) := rfl
  rw [code]
  pintro x n p
  prw [PRA.eval_pair Primrec.Code.left (Primrec.Code.pair stepIndexProgram (stepValueProgram f g)),
    PRA.eval_pair stepIndexProgram (stepValueProgram f g), PRA.eval_left, step_index_value,
    step_value f g]

fol_theorem step_child_value (f g e : Nat) : PRA ⊢ ∀ x n p,
    eval[Primrec.Code.comp e (stepChildInputProgram f g)](pair(x, pair(n, p))) =
      eval[e]((stepArgument f g)(x, n)) := by
  pintro x n p
  ptrans eval[e](eval[stepChildInputProgram f g](pair(x, pair(n, p))))
  · pexact (PRA.eval_comp e (stepChildInputProgram f g))[pair(x, pair(n, p))]
  · pcongr
    pexact (step_child_input_value f g)[x, n, p]

fol_theorem step_results_value (f g qg : Nat) : PRA ⊢ ∀ x n p,
    eval[stepResultsProgram f g qg](pair(x, pair(n, p))) =
      pair(eval[g]((stepArgument f g)(x, n)),
        pair(p, eval[qg]((stepArgument f g)(x, n)))) := by
  let gv := Primrec.Code.comp g (stepChildInputProgram f g)
  let bp := Primrec.Code.comp qg (stepChildInputProgram f g)
  have code : stepResultsProgram f g qg =
      Primrec.Code.pair gv (Primrec.Code.pair stepPreviousProofProgram bp) := rfl
  rw [code]
  pintro x n p
  prw [PRA.eval_pair gv (Primrec.Code.pair stepPreviousProofProgram bp),
    PRA.eval_pair stepPreviousProofProgram bp, step_child_value f g g, step_child_value f g qg,
    step_previous_proof_value]

fol_theorem step_proof_program_value (f g qg make : Nat) : PRA ⊢ ∀ x n p,
    eval[stepProofProgram f g qg make](pair(x, pair(n, p))) =
      eval[make](pair(x, pair(n, pair((previousValue f g)(x, n),
        pair(eval[g]((stepArgument f g)(x, n)),
          pair(p, eval[qg]((stepArgument f g)(x, n)))))))) := by
  let rest := Primrec.Code.pair (stepValueProgram f g) (stepResultsProgram f g qg)
  have code : stepProofProgram f g qg make =
    Primrec.Code.comp make (Primrec.Code.pair Primrec.Code.left
      (Primrec.Code.pair stepIndexProgram rest)) :=
    rfl
  rw [code]
  pintro x n p
  prw [eval_comp_pair make Primrec.Code.left (Primrec.Code.pair stepIndexProgram rest),
    PRA.eval_pair stepIndexProgram rest,
    PRA.eval_pair (stepValueProgram f g) (stepResultsProgram f g qg),
    PRA.eval_left, step_index_value, step_value f g, step_results_value f g qg]

fol_theorem provesEval_recursion (f g qf qg zeroProof succProof : Nat) : PRA ⊢
    (provesEval f qf) →
    (provesEval g qg) →
    (∀ x y a, equationProofOf f x y a →
      (equationProofOf (Primrec.Code.rec f g) pair(x, zero) y
        eval[zeroProof](pair(x, pair(y, a))))) →
    (∀ x n u y a b, equationProofOf (Primrec.Code.rec f g) pair(x, n) u a →
      equationProofOf g pair(x, pair(n, u)) y b →
      (equationProofOf (Primrec.Code.rec f g) pair(x, succ(n)) y
        eval[succProof](pair(x, pair(n, pair(u, pair(y, pair(a, b)))))))) →
    (provesEval ${Primrec.Code.rec f g} ${Primrec.Code.rec (baseProofProgram f qf zeroProof)
    (stepProofProgram f g qg succProof)}) := by
  pintro qfCorrect qgCorrect onZero onSucc
  papply provesEval_rec_of_rules f g qf qg (baseProofProgram f qf zeroProof)
      (stepProofProgram f g qg succProof)
  · pexact qfCorrect
  · pexact qgCorrect
  · pintro x child
    papply (equationProofOf_of_eq (Primrec.Code.rec f g))[pair(x, zero), eval[f](x),
      eval[baseProofProgram f qf zeroProof](x), pair(x, zero), eval[f](x),
      eval[zeroProof](pair(x, pair(eval[f](x), eval[qf](x))))]
    · prefl
    · prefl
    · pexact (base_proof_program_value f qf zeroProof)[x]
    · papply onZero[x, eval[f](x), eval[qf](x)]
      pexact child
  · pintro x n p prev child
    papply (equationProofOf_of_eq (Primrec.Code.rec f g))[pair(x, succ(n)),
      eval[g]((stepArgument f g)(x, n)),
      eval[stepProofProgram f g qg succProof](pair(x, pair(n, p))), pair(x, succ(n)),
      eval[g]((stepArgument f g)(x, n)),
      eval[succProof](pair(x, pair(n, pair((previousValue f g)(x, n),
        pair(eval[g]((stepArgument f g)(x, n)),
          pair(p, eval[qg]((stepArgument f g)(x, n))))))))]
    · prefl
    · prefl
    · pexact (step_proof_program_value f g qg succProof)[x, n, p]
    · papply onSucc[x, n, (previousValue f g)(x, n),
        eval[g]((stepArgument f g)(x, n)), p,
        eval[qg]((stepArgument f g)(x, n))]
      · pexact prev
      · pexact child

/-! #### The base case -/

def zeroBody (f g : Nat) : Nat :=
  fol_formula[PRA | eval[Primrec.Code.rec f g](pair(${Term.var language 0}, zero)) =
    eval[f](${Term.var language 0})]

fol_def baseEquationCode over PRA : term of 3 := fun c f t =>
  Pair.equalCode(evalApplication(c, Pair.pairCode(t, zero)), evalApplication(f, t))

fol_def zeroEquation over PRA : term of 3 := fun c f t =>
 equalityCode(
   applicationCode(c, Pair.pairCode(t, zero)),
   applicationCode(f, t))

fol_theorem zero_le : PRA ⊢ ∀ A c f t,
    eval[sub.code](pair(t, eval[Formula.imp.code](pair(A, baseEquationCode(c, f, t))))) = zero := by
  pintro A c f t
  papply Pair.term_le_of_lt_chain_inner[t, Pair.pairCode(t, zero),
    eval[Formula.imp.code](pair(A, baseEquationCode(c, f, t)))]
  · pexact Pair.left_lt_pair_term_inner[${num language}, succ(zero), t, zero]
  · papply Pair.term_le_of_lt_chain_inner[Pair.pairCode(t, zero),
      evalApplication(c, Pair.pairCode(t, zero)),
      eval[Formula.imp.code](pair(A, baseEquationCode(c, f, t)))]
    · pexact FOL.PRA.term_args_lt_app[${num language}, evalSymbol(c), Pair.pairCode(t, zero)]
    · pexact Pair.term_le_in_imp_inner[${num language},
        evalApplication(c, Pair.pairCode(t, zero)), evalApplication(f, t), A]

theorem pair_code_value (t u : Nat) :
    (PRA ⊢ Pair.pairCode(${num t}, ${num u}) =
      ${num (Term.app language 1 (pair t u))}) :=
  Pair.pair_value t u

theorem zero_body_value (f g : Nat) :
    (PRA ⊢ baseEquationCode(${num (Primrec.Code.rec f g)}, ${num f}, ${num 1}) =
      ${num (zeroBody f g)}) := by
  let v := Term.var language 0
  let paired := Term.app language 1 (pair v (Term.const language 0))
  let lhs := Term.app language (Language.functionFamilyMember language 0
    (Primrec.Code.rec f g)) paired
  let rhs := Term.app language (Language.functionFamilyMember language 0 f) v
  have varEq : (PRA ⊢ ${num 1} = ${num v}) :=
    Evaluation.symm _ _ (num_eq_of_eq v 1 var_zero_language)
  have inputEq := pair_code_value v (Term.const language 0)
  have zeroCode : num (Term.const language 0) = num 0 := eq_congr
    (fun n => num n) const_zero_language
  rw [zeroCode, num_zero] at inputEq
  have leftEq :=application_value (Primrec.Code.rec f g) paired
  have rightEq :=application_value f v
  ptrans Pair.equalCode(${num lhs}, ${num rhs})
  · prw [varEq, inputEq, leftEq, rightEq]
  · exact equality_value lhs rhs

fol_theorem zero_substitution_at_num (f g : Nat) : PRA ⊢ ∀ x,
    eval[Formula.instantiate.code](pair(syntaxLanguage(),
      pair(${num (zeroBody f g)}, numCode(x)))) =
    zeroEquation(${num (Primrec.Code.rec f g)}, ${num f}, numCode(x)) := by
  pintro x
  ptrans eval[Formula.instantiate.code](pair(${num language},
    pair(baseEquationCode(${num (Primrec.Code.rec f g)}, ${num f}, ${num 1}),
      numCode(x))))
  · prw [eval_const_language, zero_body_value f g]
  · ptrans baseEquationCode(${num (Primrec.Code.rec f g)}, ${num f}, shiftZeroCode(numCode(x)))
    · ptrans eval[Formula.instantiate.code](pair(${num language}, pair(
          baseEquationCode(${num (Primrec.Code.rec f g)}, ${num f}, succ(zero)), numCode(x))))
      · prw [num_one]
      · papply Substitution.instantiate_rec_zero_equation_inner[${num language},
          ${num (Primrec.Code.rec f g)}, ${num f}, numCode(x)]
        pexact Evaluation.symm _ _ eval_language_code
    · phave unchanged : shiftZeroCode(numCode(x)) = numCode(x)
      · pexact shift_num[x]
      prw [unchanged, eval_const_language]

theorem instance_proof_accepted (L : Nat) (T : Nat → Nat) : ∀ A t B p,
    Formula.instantiate L A t = B → t ≤ Formula.imp (Formula.all A) B →
    IsProofOf L T (Formula.all A) p →
    IsProofOf L T B (Proof.mp B (Proof.axiom (Formula.imp (Formula.all A) B)) p) := by
  intro A t B p step bound universal
  rw [← step]
  rw [← step] at bound
  exact isProofOf_instantiate_of_le L T A t p bound universal

derive_fol_pra (public := true) instance_proof_accepted as isProofOf_instance

fol_theorem zero_universal (f g : Nat) : PRA ⊢ ∀ x,
    eval[Primrec.Code.rec f g](pair(x, zero)) = eval[f](x) := by
  pexact PRA.eval_rec_zero f g

extract_witness zero_universal

theorem zero_universal_accepted (f g : Nat) :
    (PRA ⊢ (praProofOf eval[Formula.all.code](${num (zeroBody f g)})
      ${num (zero_universal.witness f g)})) := by
  let p := zero_universal.witness f g
  let body := zeroBody f g
  have hp : IsProofOf language isAxiom (Formula.all body) p :=
    zero_universal.witness_correct f g
  have valid :=  praIsProof_on_num p (and_left hp)
  have concludes := eval_num_of_evaluates Proof.conclusion.code p (Proof.conclusion p)
    (Proof.conclusion.trace p) (Proof.conclusion.computedBy p)
  rw [and_right hp] at concludes
  pconstructor
  · exact valid
  · ptrans ${num (Formula.all body)}
    · exact concludes
    · psymm
      exact eval_num_of_evaluates Formula.all.code body (Formula.all body)
        (Formula.all.trace body) (Formula.all.computedBy body)

fol_def zeroInstanceProof over PRA (f g : Nat) : term of 1 := fun x =>
  (EquationCompleteness.instanceProofAt (zeroBody f g) (zero_universal.witness f g))(
      zeroEquation(${num (Primrec.Code.rec f g)}, ${num f}, numCode(x)))

theorem zero_instance_accepted (f g : Nat) :
    (PRA ⊢ ∀ x, (praProofOf zeroEquation(${num (Primrec.Code.rec f g)}, ${num f}, numCode(x))
      (zeroInstanceProof f g)(x))) := by
  pintro x
  papply (isProofOf_instance language isAxiom.code)[${num (zeroBody f g)}, numCode(x),
    zeroEquation(${num (Primrec.Code.rec f g)}, ${num f}, numCode(x)),
    ${num (zero_universal.witness f g)}]
  · pexact (zero_substitution_at_num f g)[x]
  · phave bound : eval[sub.code](pair(numCode(x), eval[Formula.imp.code](pair(
        eval[Formula.all.code](${num (zeroBody f g)}),
        baseEquationCode(${num (Primrec.Code.rec f g)}, ${num f}, numCode(x)))))) = zero
    · pexact zero_le[eval[Formula.all.code](${num (zeroBody f g)}),
        ${num (Primrec.Code.rec f g)}, ${num f}, numCode(x)]
    prw [eval_const_language, bound]
  · pexact zero_universal_accepted f g

fol_theorem equationProofOf_conclusion_eq : PRA ⊢
    ∀ A B p, A = B → praProofOf B p → praProofOf A p := by
  pintro A B p same h
  psubst same
  pexact h

theorem lifted_input_accepted (e p : Nat) :
    (PRA ⊢ ∀ x n, (provesPair p) →
      (praProofOf equalityCode(applicationCode(${num e}, numCode(pair(x, n))),
          applicationCode(${num e}, pairTermNumAt(x, n)))
        (liftedPairAt e p)(x, n))) := by
  pintro x n pairing
  papply (congruence_accepted e)[numCode(pair(x, n)), pairTermNumAt(x, n),
    (reversePairAt p)(x, n)]
  · pexact Projection.projection_congruence e
  · papply reverse_accepted[pairTermNumAt(x, n), numCode(pair(x, n)), eval[p](pair(x, n))]
    pexact pairing[x, n]

def basePairProgram : Nat := Primrec.Code.pair Primrec.Code.left Primrec.Code.zero

def baseArgumentProgram : Nat := pairTermProgram (numAtProgram Primrec.Code.left) Primrec.Code.zero

def zeroLeftProgram (f g : Nat) : Nat := appProgram (Primrec.Code.rec f g) baseArgumentProgram

def zeroRightProgram (f : Nat) : Nat := appProgram f (numAtProgram Primrec.Code.left)

def zeroAxiomProgram (f g : Nat) : Nat :=
  instanceProofProgram (equationProgram (zeroLeftProgram f g) (zeroRightProgram f))
    (zeroBody f g) (zero_universal.witness f g)

def zeroInputProgram (f g : Nat) : Nat :=
  appProgram (Primrec.Code.rec f g) (numAtProgram basePairProgram)

def zeroNormalizeProgram (f g p : Nat) : Nat :=
  Primrec.Code.comp (liftedPairProgram (Primrec.Code.rec f g) p) basePairProgram

def zeroTailProgram (f g : Nat) : Nat :=
  transitivityProgram (zeroLeftProgram f g) (zeroRightProgram f) (numAtProgram stepIndexProgram)
    (zeroAxiomProgram f g) stepPreviousProofProgram

/-- Produce the base proof from `pair x (pair y a)`, where `a` proves the base program's value. -/
def makeZeroProgram (f g p : Nat) : Nat :=
  transitivityProgram (zeroInputProgram f g) (zeroLeftProgram f g) (numAtProgram stepIndexProgram)
    (zeroNormalizeProgram f g p) (zeroTailProgram f g)

fol_def numericInput over PRA (e : Nat) : term of 2 := fun x n =>
  applicationCode(${num e}, numCode(pair(x, n)))

fol_def baseLeftAt over PRA (f g : Nat) : term of 1 := fun x =>
  applicationCode(${num (Primrec.Code.rec f g)}, Pair.pairTermCode(numCode(x), zero))

fol_def baseRightAt over PRA (f : Nat) : term of 1 := fun x =>
  applicationCode(${num f}, numCode(x))

fol_def zeroTailAt over PRA (f g : Nat) : term of 3 := fun x y a =>
  transitivityProof((baseLeftAt f g)(x), (baseRightAt f)(x), numCode(y),
    (zeroInstanceProof f g)(x), a)

fol_def makeZeroAt over PRA (f g p : Nat) : term of 3 := fun x y a =>
  transitivityProof((numericInput (Primrec.Code.rec f g))(x, zero),
    (baseLeftAt f g)(x), numCode(y),
    (liftedPairAt (Primrec.Code.rec f g) p)(x, zero),
    (zeroTailAt f g)(x, y, a))

fol_theorem base_pair_value : PRA ⊢ ∀ x y a,
    eval[basePairProgram](pair(x, pair(y, a))) = pair(x, zero) := by
  rw [basePairProgram]
  pintro x y a
  prw [PRA.eval_pair Primrec.Code.left Primrec.Code.zero, PRA.eval_left, PRA.eval_zero]

fol_theorem base_argument_value : PRA ⊢ ∀ x y a,
    eval[baseArgumentProgram](pair(x, pair(y, a))) = Pair.pairTermCode(numCode(x), zero) := by
  rw [baseArgumentProgram]
  pintro x y a
  prw [pair_term_program_value (numAtProgram Primrec.Code.left) Primrec.Code.zero,
    num_at_program_value Primrec.Code.left, PRA.eval_left, PRA.eval_zero]

fol_theorem zero_left_value (f g : Nat) : PRA ⊢ ∀ x y a,
    eval[zeroLeftProgram f g](pair(x, pair(y, a))) = (baseLeftAt f g)(x) := by
  rw [zeroLeftProgram]
  pintro x y a
  prw [app_program_value (Primrec.Code.rec f g) baseArgumentProgram, base_argument_value]

fol_theorem zero_right_value (f : Nat) : PRA ⊢ ∀ x y a,
    eval[zeroRightProgram f](pair(x, pair(y, a))) = (baseRightAt f)(x) := by
  rw [zeroRightProgram]
  pintro x y a
  prw [app_program_value f (numAtProgram Primrec.Code.left),
    num_at_program_value Primrec.Code.left, PRA.eval_left]

fol_theorem zero_axiom_value (f g : Nat) : PRA ⊢ ∀ x y a,
    eval[zeroAxiomProgram f g](pair(x, pair(y, a))) = (zeroInstanceProof f g)(x) := by
  rw [zeroAxiomProgram]
  pintro x y a
  prw [instance_program (equationProgram (zeroLeftProgram f g) (zeroRightProgram f)) (zeroBody f g)
      (zero_universal.witness f g), equation_program_value (zeroLeftProgram f g)
      (zeroRightProgram f), zero_left_value f g, zero_right_value f, eval_const_language]

fol_theorem zero_input_value (f g : Nat) : PRA ⊢ ∀ x y a,
    eval[zeroInputProgram f g](pair(x, pair(y, a))) =
      (numericInput (Primrec.Code.rec f g))(x, zero) := by
  rw [zeroInputProgram]
  pintro x y a
  prw [app_program_value (Primrec.Code.rec f g) (numAtProgram basePairProgram),
    num_at_program_value basePairProgram, base_pair_value]

fol_theorem zero_normalize_value (f g p : Nat) : PRA ⊢ ∀ x y a,
    eval[zeroNormalizeProgram f g p](pair(x, pair(y, a))) =
      (liftedPairAt (Primrec.Code.rec f g) p)(x, zero) := by
  rw [zeroNormalizeProgram]
  pintro x y a
  ptrans eval[liftedPairProgram (Primrec.Code.rec f g) p](pair(x, zero))
  · prw [PRA.eval_comp (liftedPairProgram (Primrec.Code.rec f g) p) basePairProgram,
      base_pair_value]
  · pexact (lifted_pair_value (Primrec.Code.rec f g) p)[x, zero]

fol_theorem zero_tail_value (f g : Nat) : PRA ⊢ ∀ x y a,
    eval[zeroTailProgram f g](pair(x, pair(y, a))) = (zeroTailAt f g)(x, y, a) := by
  rw [zeroTailProgram]
  pintro x y a
  prw [transitivity_program_value (zeroLeftProgram f g) (zeroRightProgram f)
      (numAtProgram stepIndexProgram)
      (zeroAxiomProgram f g) stepPreviousProofProgram, zero_left_value f g, zero_right_value
      f, num_at_program_value stepIndexProgram, step_index_value, zero_axiom_value f
      g, step_previous_proof_value]

fol_theorem make_zero_value (f g p : Nat) : PRA ⊢ ∀ x y a,
    eval[makeZeroProgram f g p](pair(x, pair(y, a))) =
      (makeZeroAt f g p)(x, y, a) := by
  rw [makeZeroProgram]
  pintro x y a
  prw [transitivity_program_value (zeroInputProgram f g) (zeroLeftProgram f g)
      (numAtProgram stepIndexProgram) (zeroNormalizeProgram f g p)
      (zeroTailProgram f g), zero_input_value f g, zero_left_value f g, num_at_program_value
      stepIndexProgram, step_index_value, zero_normalize_value f g p, zero_tail_value f g]

fol_theorem zero_tail_accepted (f g : Nat) : PRA ⊢ ∀ x y a,
    equationProofOf f x y a →
    (praProofOf equalityCode((baseLeftAt f g)(x), numCode(y))
      (zeroTailAt f g)(x, y, a)) := by
  pintro x y a child
  papply transitivity_rule[(baseLeftAt f g)(x), (baseRightAt f)(x),
    numCode(y), (zeroInstanceProof f g)(x), a]
  · papply equationProofOf_conclusion_eq[equalityCode((baseLeftAt f g)(x),
      (baseRightAt f)(x)),
      zeroEquation(${num (Primrec.Code.rec f g)}, ${num f}, numCode(x)),
      (zeroInstanceProof f g)(x)]
    · prw [eval_const_language]
    · pexact (zero_instance_accepted f g)[x]
  · pexact child

fol_theorem make_zero_accepted (f g p : Nat) : PRA ⊢ (provesPair p) →
    ∀ x y a, equationProofOf f x y a →
      (equationProofOf (Primrec.Code.rec f g) pair(x, zero) y
        eval[makeZeroProgram f g p](pair(x, pair(y, a)))) := by
  pintro pairing x y a child
  papply (equationProofOf_of_eq (Primrec.Code.rec f g))[pair(x, zero), y,
    eval[makeZeroProgram f g p](pair(x, pair(y, a))), pair(x, zero), y,
    (makeZeroAt f g p)(x, y, a)]
  · prefl
  · prefl
  · pexact (make_zero_value f g p)[x, y, a]
  · papply transitivity_rule[(numericInput (Primrec.Code.rec f g))(x, zero),
      (baseLeftAt f g)(x), numCode(y),
      (liftedPairAt (Primrec.Code.rec f g) p)(x, zero),
      (zeroTailAt f g)(x, y, a)]
    · papply equationProofOf_conclusion_eq[equalityCode(
        (numericInput (Primrec.Code.rec f g))(x, zero),
        (baseLeftAt f g)(x)), equalityCode((numericInput (Primrec.Code.rec f g))(
          x, zero), applicationCode(${num (Primrec.Code.rec f g)}, pairTermNumAt(x, zero))),
        (liftedPairAt (Primrec.Code.rec f g) p)(x, zero)]
      · prw [eval_num_zero]
      · papply (lifted_input_accepted (Primrec.Code.rec f g) p)[x, zero]
        pexact pairing
    · papply (zero_tail_accepted f g)[x, y, a]
      pexact child

/-! #### The recursion step on `num` -/

def succBody (f g : Nat) : Nat :=
  fol_formula[PRA | eval[Primrec.Code.rec f g](pair(${Term.var language 1},
      succ(${Term.var language 0}))) =
    eval[g](pair(${Term.var language 1}, pair(${Term.var language 0},
      eval[Primrec.Code.rec f g](pair(${Term.var language 1}, ${Term.var language 0})))))]

fol_def succLeft over PRA : term of 3 := fun c t n =>
  evalApplication(c, Pair.pairCode(t, succCode(n)))

fol_def succRight over PRA : term of 4 := fun c g t n =>
  evalApplication(g, Pair.pairCode(t, Pair.pairCode(n, evalApplication(c, Pair.pairCode(t, n)))))

fol_def stepEquationCode over PRA : term of 4 := fun c g t n =>
  Pair.equalCode(succLeft(c, t, n), succRight(c, g, t, n))

theorem succ_body_value (f g : Nat) :
    (PRA ⊢ stepEquationCode(${num (Primrec.Code.rec f g)}, ${num g}, ${num 5}, ${num 1}) =
      ${num (succBody f g)}) := by
  let v := Term.var language 1
  let w := Term.var language 0
  let c := Primrec.Code.rec f g
  let app := fun e t => Term.app language (Language.functionFamilyMember language 0 e) t
  let next := Term.app language 0 w
  let input := Term.app language 1 (pair v next)
  let prevInput := Term.app language 1 (pair v w)
  let prev := app c prevInput
  let inner := Term.app language 1 (pair w prev)
  let outer := Term.app language 1 (pair v inner)
  have hv := num_eq_of_eq 5 v (eq_symm var_one_language)
  have hw := num_eq_of_eq 1 w (eq_symm var_zero_language)
  have nextEq := Pair.successor_value w
  have inputEq := pair_code_value v next
  have prevInputEq := pair_code_value v w
  have innerEq := pair_code_value w prev
  have outerEq := pair_code_value v inner
  have leq := application_value c input
  have prevEq := application_value c prevInput
  have req := application_value g outer
  ptrans Pair.equalCode(${num (app c input)}, ${num (app g outer)})
  · prw [stepEquationCode, Pair.equalCode]
    pcongr
    pcongr
    · prefl
    · pcongr
      · prw [succLeft]
        prw [hv, hw, nextEq, inputEq, leq]
      · prw [succRight]
        prw [hv, hw, prevInputEq, prevEq, innerEq, outerEq, req]
  · prw [Pair.equalCode]
    exact equality_value (app c input) (app g outer)

fol_def succOpen over PRA (f g : Nat) : term of 1 := fun x =>
  stepEquationCode(${num (Primrec.Code.rec f g)}, ${num g}, numCode(x), ${num 1})

fol_def succHalf over PRA (f g : Nat) : term of 1 := fun x =>
  eval[Formula.all.code]((succOpen f g)(x))

fol_def succInstance over PRA (f g : Nat) : term of 2 := fun x n =>
  stepEquationCode(${num (Primrec.Code.rec f g)}, ${num g}, numCode(x), numCode(n))

theorem succ_quantified_body_value (f g : Nat) :
    (PRA ⊢ eval[Formula.all.code](
        stepEquationCode(${num (Primrec.Code.rec f g)}, ${num g}, ${num 5}, ${num 1})) =
      ${num (Formula.all (succBody f g))}) := by
  ptrans eval[Formula.all.code](${num (succBody f g)})
  · prw [succ_body_value f g]
  · exact Pair.all_value (succBody f g)

fol_theorem succ_first_substitution (f g : Nat) : PRA ⊢ ∀ x,
    eval[Formula.instantiate.code](pair(syntaxLanguage(),
      pair(${num (Formula.all (succBody f g))}, numCode(x)))) =
    (succHalf f g)(x) := by
  pintro x
  ptrans eval[Formula.instantiate.code](pair(${num language}, pair(eval[Formula.all.code](
    stepEquationCode(${num (Primrec.Code.rec f g)}, ${num g}, ${num 5}, ${num 1})),
    numCode(x))))
  · prw [eval_const_language, succ_quantified_body_value f g]
  · ptrans eval[Formula.instantiate.code](pair(${num language}, pair(eval[Formula.all.code](
        stepEquationCode(${num (Primrec.Code.rec f g)}, ${num g},
          succ(succ(succ(succ(succ(zero))))), succ(zero))), numCode(x))))
    · prw [num_five, num_one]
    · ptrans eval[Formula.all.code](stepEquationCode(${num (Primrec.Code.rec f g)}, ${num g},
          Pair.shiftedOne(numCode(x)), succ(zero)))
      · papply Substitution.instantiate_rec_succ_first_inner[${num language},
          ${num (Primrec.Code.rec f g)}, ${num g}, numCode(x)]
        pexact Evaluation.symm _ _ eval_language_code
      · phave shifted : Pair.shiftedOne(numCode(x)) = numCode(x)
        · pexact Pair.shift_one_num[x]
        prw [shifted, num_one]

fol_theorem succ_second_substitution (f g : Nat) : PRA ⊢ ∀ x n,
    eval[Formula.instantiate.code](pair(syntaxLanguage(),
      pair((succOpen f g)(x), numCode(n)))) =
    (succInstance f g)(x, n) := by
  pintro x n
  ptrans eval[Formula.instantiate.code](pair(${num language}, pair(
    stepEquationCode(${num (Primrec.Code.rec f g)}, ${num g}, numCode(x), succ(zero)),
    numCode(n))))
  · prw [eval_const_language, num_one]
  · ptrans stepEquationCode(${num (Primrec.Code.rec f g)}, ${num g}, numCode(x),
        shiftZeroCode(numCode(n)))
    · papply Substitution.instantiate_rec_succ_second_inner[${num language},
        ${num (Primrec.Code.rec f g)}, ${num g}, x, numCode(n)]
      pexact Evaluation.symm _ _ eval_language_code
    · prw [shift_num]

fol_theorem parameter_lt_succ_left : PRA ⊢ ∀ c t n,
    eval[sub.code](pair(succ(t), succLeft(c, t, n))) = zero := by
  pintro c t n
  papply Pair.lt_chain_inner[t, Pair.pairCode(t, succCode(n)), succLeft(c, t, n)]
  · pexact Pair.left_lt_pair_term_inner[${num language}, succ(zero), t, succCode(n)]
  · pexact FOL.PRA.term_args_lt_app[${num language}, evalSymbol(c),
      Pair.pairCode(t, succCode(n))]

fol_theorem index_lt_succ_left : PRA ⊢ ∀ c t n,
    eval[sub.code](pair(succ(n), succLeft(c, t, n))) = zero := by
  pintro c t n
  papply Pair.lt_chain_inner[n, succCode(n), succLeft(c, t, n)]
  · pexact lt_succCode[n]
  · papply Pair.lt_chain_inner[succCode(n), Pair.pairCode(t, succCode(n)),
      succLeft(c, t, n)]
    · pexact Pair.right_lt_pair_term_inner[${num language}, succ(zero), t, succCode(n)]
    · pexact FOL.PRA.term_args_lt_app[${num language}, evalSymbol(c),
      Pair.pairCode(t, succCode(n))]

fol_theorem succ_first_le : PRA ⊢ ∀ A c g t n,
    eval[sub.code](pair(t, eval[Formula.imp.code](pair(A,
      eval[Formula.all.code](stepEquationCode(c, g, t, n)))))) = zero := by
  pintro A c g t n
  papply Pair.term_le_of_lt_chain_inner[t, succLeft(c, t, n),
    eval[Formula.imp.code](pair(A, eval[Formula.all.code](stepEquationCode(c, g, t, n))))]
  · pexact parameter_lt_succ_left[c, t, n]
  · papply Pair.le_chain_inner[succLeft(c, t, n), stepEquationCode(c, g, t, n),
      eval[Formula.imp.code](pair(A, eval[Formula.all.code](stepEquationCode(c, g, t, n))))]
    · pexact formula_le_equal_left[${num language}, succLeft(c, t, n), succRight(c, g, t, n)]
    · papply Pair.term_le_of_lt_chain_inner[stepEquationCode(c, g, t, n),
        eval[Formula.all.code](stepEquationCode(c, g, t, n)),
        eval[Formula.imp.code](pair(A, eval[Formula.all.code](stepEquationCode(c, g, t, n))))]
      · pexact Pair.body_lt_all_inner[stepEquationCode(c, g, t, n)]
      · pexact Pair.imp_right_le_inner[A, eval[Formula.all.code](stepEquationCode(c, g, t, n))]

fol_theorem succ_second_le : PRA ⊢ ∀ A c g t n,
    eval[sub.code](pair(n, eval[Formula.imp.code](pair(A, stepEquationCode(c, g, t, n))))) =
    zero := by
  pintro A c g t n
  papply Pair.term_le_of_lt_chain_inner[n, succLeft(c, t, n),
    eval[Formula.imp.code](pair(A, stepEquationCode(c, g, t, n)))]
  · pexact index_lt_succ_left[c, t, n]
  · pexact Pair.term_le_in_imp_inner[${num language}, succLeft(c, t, n),
      succRight(c, g, t, n), A]

fol_theorem succ_universal (f g : Nat) : PRA ⊢ ∀ x n,
    eval[Primrec.Code.rec f g](pair(x, succ(n))) =
      eval[g](pair(x, pair(n, eval[Primrec.Code.rec f g](pair(x, n))))) := by
  pexact PRA.eval_rec_succ f g

extract_witness succ_universal

theorem succ_universal_accepted (f g : Nat) :
    (PRA ⊢ (praProofOf eval[Formula.all.code](${num (Formula.all (succBody f g))})
      ${num (succ_universal.witness f g)})) := by
  let p := succ_universal.witness f g
  let body := Formula.all (succBody f g)
  have hp : IsProofOf language isAxiom (Formula.all body) p :=
    succ_universal.witness_correct f g
  have valid :=  praIsProof_on_num p (and_left hp)
  have concludes := eval_num_of_evaluates Proof.conclusion.code p (Proof.conclusion p)
    (Proof.conclusion.trace p) (Proof.conclusion.computedBy p)
  rw [and_right hp] at concludes
  pconstructor
  · exact valid
  · ptrans ${num (Formula.all body)}
    · exact concludes
    · psymm
      exact Pair.all_value body

fol_def mpInstance over PRA : term of 3 := fun A B p =>
  eval[Proof.mp.code](pair(B, pair(eval[Proof.axiom.code](
    eval[Formula.imp.code](pair(eval[Formula.all.code](A), B))), p)))

fol_def succFirstProof over PRA (f g : Nat) : term of 1 := fun x =>
  mpInstance(${num (Formula.all (succBody f g))}, (succHalf f g)(x),
    ${num (succ_universal.witness f g)})

fol_def succInstanceProof over PRA (f g : Nat) : term of 2 := fun x n =>
  mpInstance((succOpen f g)(x), (succInstance f g)(x, n),
    (succFirstProof f g)(x))

fol_theorem succ_first_accepted (f g : Nat) : PRA ⊢ ∀ x,
    praProofOf (succHalf f g)(x) (succFirstProof f g)(x) := by
  pintro x
  papply (isProofOf_instance language isAxiom.code)[${num (Formula.all (succBody f g))},
    numCode(x), (succHalf f g)(x), ${num (succ_universal.witness f g)}]
  · pexact (succ_first_substitution f g)[x]
  · pexact succ_first_le[eval[Formula.all.code](${num (Formula.all (succBody f g))}),
      ${num (Primrec.Code.rec f g)}, ${num g}, numCode(x), ${num 1}]
  · pexact succ_universal_accepted f g

fol_theorem succ_instance_accepted (f g : Nat) : PRA ⊢ ∀ x n,
    (praProofOf (succInstance f g)(x, n)
      (succInstanceProof f g)(x, n)) := by
  pintro x n
  papply (isProofOf_instance language isAxiom.code)[(succOpen f g)(x),
    numCode(n), (succInstance f g)(x, n), (succFirstProof f g)(x)]
  · pexact (succ_second_substitution f g)[x, n]
  · pexact succ_second_le[(succHalf f g)(x),
      ${num (Primrec.Code.rec f g)}, ${num g}, numCode(x), numCode(n)]
  · pexact (succ_first_accepted f g)[x]

fol_def reflProof over PRA : term of 1 := fun a => eval[Proof.axiom.code](equalityCode(a, a))

fol_def priorAt over PRA (c : Nat) : term of 2 := fun x n =>
  applicationCode(${num c}, pairTermNumAt(x, n))

fol_def priorCongruence over PRA (c p : Nat) : term of 2 := fun x n =>
  (congruenceProof c)(pairTermNumAt(x, n), numCode(pair(x, n)), eval[p](pair(x, n)))

fol_def priorProof over PRA (c p : Nat) : term of 4 := fun x n u a =>
  transitivityProof((priorAt c)(x, n), (numericInput c)(x, n), numCode(u),
    (priorCongruence c p)(x, n), a)

fol_def innerAt over PRA (c : Nat) : term of 2 := fun x n =>
  Pair.pairTermCode(numCode(n), (priorAt c)(x, n))

fol_def innerProof over PRA (c p : Nat) : term of 4 := fun x n u a =>
  transitivityProof((innerAt c)(x, n), pairTermNumAt(n, u), numCode(pair(n, u)),
    Pairing.pairCongruenceProof(numCode(n), (priorAt c)(x, n), numCode(n),
      numCode(u), reflProof(numCode(n)), (priorProof c p)(x, n, u, a)),
    eval[p](pair(n, u)))

fol_def outerAt over PRA (c : Nat) : term of 2 := fun x n =>
  Pair.pairTermCode(numCode(x), (innerAt c)(x, n))

fol_def outerProof over PRA (c p : Nat) : term of 4 := fun x n u a =>
  transitivityProof((outerAt c)(x, n), pairTermNumAt(x, pair(n, u)),
    numCode(pair(x, pair(n, u))),
    Pairing.pairCongruenceProof(numCode(x), (innerAt c)(x, n), numCode(x),
      numCode(pair(n, u)), reflProof(numCode(x)), (innerProof c p)(x, n, u, a)),
    eval[p](pair(x, pair(n, u))))

fol_def stepLeftAt over PRA (c : Nat) : term of 2 := fun x n =>
  applicationCode(${num c},
    Pair.pairTermCode(numCode(x), Pair.successorTermCode(numCode(n))))

fol_def stepRightAt over PRA (c g : Nat) : term of 2 := fun x n =>
  applicationCode(${num g}, (outerAt c)(x, n))

fol_def stepTailAt over PRA (c g p : Nat) : term of 6 := fun x n u y a b =>
  transitivityProof((stepRightAt c g)(x, n),
    applicationCode(${num g}, numCode(pair(x, pair(n, u)))), numCode(y),
    (congruenceProof g)((outerAt c)(x, n), numCode(pair(x, pair(n, u))),
      (outerProof c p)(x, n, u, a)), b)

fol_def stepViaAxiom over PRA (f g p : Nat) : term of 6 := fun x n u y a b =>
  transitivityProof((stepLeftAt (Primrec.Code.rec f g))(x, n),
    (stepRightAt (Primrec.Code.rec f g) g)(x, n), numCode(y),
    (succInstanceProof f g)(x, n),
    (stepTailAt (Primrec.Code.rec f g) g p)(x, n, u, y, a, b))

fol_def makeSuccAt over PRA (f g p : Nat) : term of 6 := fun x n u y a b =>
  transitivityProof((numericInput (Primrec.Code.rec f g))(x, succ(n)),
    (stepLeftAt (Primrec.Code.rec f g))(x, n), numCode(y),
    (liftedPairAt (Primrec.Code.rec f g) p)(x, succ(n)),
    (stepViaAxiom f g p)(x, n, u, y, a, b))

theorem reflexivity_is_logical : ∀ L t, isLogicalAxiom L (Formula.equal L t t) = 1 := by
  intro L t
  change bor _ _ = 1
  apply bor_eq_one_of_right_eq_one
  apply bor_eq_one_of_right_eq_one
  apply bor_eq_one_of_right_eq_one
  apply bor_eq_one_of_right_eq_one
  apply bor_eq_one_of_right_eq_one
  apply bor_eq_one_of_left_eq_one
  rw [LogicalAxiom.isReflexivity]
  repeat first
    | rw [Formula.arg_equal]
    | rw [unpairLeft_pair]
  exact eqb_self _

derive_fol_pra reflexivity_is_logical as reflexivity_is_logical_inner

theorem isProofOf_equal_refl (L : Nat) (T : Nat → Nat) : ∀ t,
    IsProofOf L T (Formula.equal L t t) (Proof.axiom (Formula.equal L t t)) := by
  intro t
  exact (isProof_axiom L T _ (reflexivity_is_logical L t), Proof.conclusion_axiom _)

derive_fol_pra (public := true) isProofOf_equal_refl as reflexivity_proof_accepted

fol_theorem refl_proof_accepted : PRA ⊢ ∀ a,
    praProofOf equalityCode(a, a) reflProof(a) := by
  pexact reflexivity_proof_accepted language isAxiom.code

fol_theorem step_congruence_accepted (e : Nat) : PRA ⊢ ∀ a b h,
    praProofOf equalityCode(a, b) h →
    (praProofOf equalityCode(applicationCode(${num e}, a), applicationCode(${num e}, b))
      (congruenceProof e)(a, b, h)) := by
  papply congruence_accepted e
  pexact projection_congruence e

fol_theorem prior_accepted (c p : Nat) : PRA ⊢ ∀ x n u a,
    (provesPair p) → equationProofOf c pair(x, n) u a →
    (praProofOf equalityCode((priorAt c)(x, n), numCode(u))
      (priorProof c p)(x, n, u, a)) := by
  pintro x n u a pairing previous
  papply transitivity_rule[(priorAt c)(x, n), (numericInput c)(x, n), numCode(u),
    (priorCongruence c p)(x, n), a]
  · papply (step_congruence_accepted c)[pairTermNumAt(x, n), numCode(pair(x, n)),
      eval[p](pair(x, n))]
    pexact pairing[x, n]
  · pexact previous

fol_theorem inner_accepted (c p : Nat) : PRA ⊢ ∀ x n u a,
    (provesPair p) → equationProofOf c pair(x, n) u a →
    (praProofOf equalityCode((innerAt c)(x, n), numCode(pair(n, u)))
      (innerProof c p)(x, n, u, a)) := by
  pintro x n u a pairing previous
  papply transitivity_rule[(innerAt c)(x, n), pairTermNumAt(n, u), numCode(pair(n, u)),
    Pairing.pairCongruenceProof(numCode(n), (priorAt c)(x, n), numCode(n),
      numCode(u), reflProof(numCode(n)), (priorProof c p)(x, n, u, a)),
    eval[p](pair(n, u))]
  · papply Pairing.pair_congruence_accepted[numCode(n), (priorAt c)(x, n),
      numCode(n), numCode(u), reflProof(numCode(n)),
      (priorProof c p)(x, n, u, a)]
    · pexact refl_proof_accepted[numCode(n)]
    · papply (prior_accepted c p)[x, n, u, a]
      · pexact pairing
      · pexact previous
  · pexact pairing[n, u]

fol_theorem outer_accepted (c p : Nat) : PRA ⊢ ∀ x n u a,
    (provesPair p) → equationProofOf c pair(x, n) u a →
    (praProofOf equalityCode((outerAt c)(x, n), numCode(pair(x, pair(n, u))))
      (outerProof c p)(x, n, u, a)) := by
  pintro x n u a pairing previous
  papply transitivity_rule[(outerAt c)(x, n), pairTermNumAt(x, pair(n, u)),
    numCode(pair(x, pair(n, u))),
    Pairing.pairCongruenceProof(numCode(x), (innerAt c)(x, n), numCode(x),
      numCode(pair(n, u)), reflProof(numCode(x)), (innerProof c p)(x, n, u, a)),
    eval[p](pair(x, pair(n, u)))]
  · papply Pairing.pair_congruence_accepted[numCode(x), (innerAt c)(x, n),
      numCode(x), numCode(pair(n, u)), reflProof(numCode(x)),
      (innerProof c p)(x, n, u, a)]
    · pexact refl_proof_accepted[numCode(x)]
    · papply (inner_accepted c p)[x, n, u, a]
      · pexact pairing
      · pexact previous
  · pexact pairing[x, pair(n, u)]

fol_theorem step_tail_accepted (c g p : Nat) : PRA ⊢ ∀ x n u y a b,
    (provesPair p) → equationProofOf c pair(x, n) u a →
    equationProofOf g pair(x, pair(n, u)) y b →
    (praProofOf equalityCode((stepRightAt c g)(x, n), numCode(y))
      (stepTailAt c g p)(x, n, u, y, a, b)) := by
  pintro x n u y a b pairing previous child
  papply transitivity_rule[(stepRightAt c g)(x, n),
    applicationCode(${num g}, numCode(pair(x, pair(n, u)))), numCode(y),
    (congruenceProof g)((outerAt c)(x, n), numCode(pair(x, pair(n, u))),
      (outerProof c p)(x, n, u, a)), b]
  · papply (step_congruence_accepted g)[(outerAt c)(x, n), numCode(pair(x, pair(n, u))),
      (outerProof c p)(x, n, u, a)]
    papply (outer_accepted c p)[x, n, u, a]
    · pexact pairing
    · pexact previous
  · pexact child

fol_theorem step_via_axiom_accepted (f g p : Nat) : PRA ⊢ ∀ x n u y a b,
    (provesPair p) → equationProofOf (Primrec.Code.rec f g) pair(x, n) u a →
    equationProofOf g pair(x, pair(n, u)) y b →
    (praProofOf equalityCode((stepLeftAt (Primrec.Code.rec f g))(x, n), numCode(y))
      (stepViaAxiom f g p)(x, n, u, y, a, b)) := by
  let c := Primrec.Code.rec f g
  pintro x n u y a b pairing previous child
  papply transitivity_rule[(stepLeftAt c)(x, n), (stepRightAt c g)(x, n),
    numCode(y), (succInstanceProof f g)(x, n),
    (stepTailAt c g p)(x, n, u, y, a, b)]
  · papply equationProofOf_conclusion_eq[equalityCode((stepLeftAt c)(x, n),
      (stepRightAt c g)(x, n)), (succInstance f g)(x, n),
      (succInstanceProof f g)(x, n)]
    · prw [eval_const_language]
    · pexact (succ_instance_accepted f g)[x, n]
  · papply (step_tail_accepted c g p)[x, n, u, y, a, b]
    · pexact pairing
    · pexact previous
    · pexact child

fol_theorem step_successor_num : PRA ⊢ ∀ n,
    Pair.successorTermCode(numCode(n)) = numCode(succ(n)) := by
  pintro n
  ptrans eval[Term.app.code](pair(${num language}, pair(zero, numCode(n))))
  · prw [eval_const_language]
  · psymm
    pexact num_succ_code[n]

fol_theorem step_input_accepted (c p : Nat) : PRA ⊢ ∀ x n,
    (provesPair p) →
    (praProofOf equalityCode((numericInput c)(x, succ(n)), (stepLeftAt c)(x, n))
      (liftedPairAt c p)(x, succ(n))) := by
  pintro x n pairing
  papply equationProofOf_conclusion_eq[equalityCode((numericInput c)(x, succ(n)),
    (stepLeftAt c)(x, n)), equalityCode((numericInput c)(x, succ(n)),
    applicationCode(${num c}, pairTermNumAt(x, succ(n)))),
    (liftedPairAt c p)(x, succ(n))]
  · prw [step_successor_num]
  · papply (lifted_input_accepted c p)[x, succ(n)]
    pexact pairing

fol_def acceptedStepInput over PRA (c p : Nat) : formula of 2 := fun x n =>
  (praProofOf equalityCode((numericInput c)(x, succ(n)), (stepLeftAt c)(x, n))
    (liftedPairAt c p)(x, succ(n)))

fol_def acceptedStepAxiom over PRA (f g p : Nat) : formula of 6 := fun x n u y a b =>
  (praProofOf equalityCode((stepLeftAt (Primrec.Code.rec f g))(x, n), numCode(y))
    (stepViaAxiom f g p)(x, n, u, y, a, b))

fol_def acceptedStepResult over PRA (f g p : Nat) : formula of 6 := fun x n u y a b =>
  (equationProofOf (Primrec.Code.rec f g) pair(x, succ(n)) y
    (makeSuccAt f g p)(x, n, u, y, a, b))

fol_theorem open_step_input (f g p : Nat) : PRA ⊢ free b a y u n x |
    (provesPair p) →
    (acceptedStepInput (Primrec.Code.rec f g) p)(x, n) := by
  pexact (step_input_accepted (Primrec.Code.rec f g) p)[x, n]

fol_theorem open_step_axiom (f g p : Nat) : PRA ⊢ free b a y u n x |
    (provesPair p) →
    equationProofOf (Primrec.Code.rec f g) pair(x, n) u a →
    equationProofOf g pair(x, pair(n, u)) y b →
    (acceptedStepAxiom f g p)(x, n, u, y, a, b) := by
  pexact (step_via_axiom_accepted f g p)[x, n, u, y, a, b]

fol_theorem open_step_trans (f g p : Nat) : PRA ⊢ free b a y u n x |
    (acceptedStepInput (Primrec.Code.rec f g) p)(x, n) →
    (acceptedStepAxiom f g p)(x, n, u, y, a, b) →
    (acceptedStepResult f g p)(x, n, u, y, a, b) := by
  let c := Primrec.Code.rec f g
  pexact transitivity_rule[(numericInput c)(x, succ(n)), (stepLeftAt c)(x, n),
    numCode(y), (liftedPairAt c p)(x, succ(n)),
    (stepViaAxiom f g p)(x, n, u, y, a, b)]

fol_theorem combine_implications (H P Q U V C : Nat) : PRA ⊢
    (${H} → ${U}) → (${H} → ${P} → ${Q} → ${V}) → (${U} → ${V} → ${C}) →
    ${H} → ${P} → ${Q} → ${C} := by
  pintro toU toV toC h p q
  papply toC
  · papply toU
    pexact h
  · papply toV
    · pexact h
    · pexact p
    · pexact q

theorem combine_accepted (H P Q U V C : Nat) :
    Provable language isAxiom (Formula.imp H U) →
    Provable language isAxiom (Formula.imp H (Formula.imp P (Formula.imp Q V))) →
    Provable language isAxiom (Formula.imp U (Formula.imp V C)) →
    Provable language isAxiom (Formula.imp H (Formula.imp P (Formula.imp Q C))) := by
  intro toU toV toC
  have h₁ := Provable.mp language isAxiom _ _ (combine_implications H P Q U V C) toU
  have h₂ := Provable.mp language isAxiom _ _ h₁ toV
  exact Provable.mp language isAxiom _ _ h₂ toC

theorem close_step_formula (A : Nat) : Provable language isAxiom A →
    Provable language isAxiom
      (Formula.all (Formula.all (Formula.all (Formula.all (Formula.all (Formula.all A)))))) := by
  intro h
  exact Provable.gen language isAxiom _ (Provable.gen language isAxiom _
    (Provable.gen language isAxiom _ (Provable.gen language isAxiom _
      (Provable.gen language isAxiom _ (Provable.gen language isAxiom _ h)))))

/-! #### Correctness of the recursion step -/

fol_def packedStep over PRA : term of 6 := fun x n u y a b =>
  pair(x, pair(n, pair(u, pair(y, pair(a, b)))))

def afterIndexProgram : Nat := Primrec.Code.comp Primrec.Code.right Primrec.Code.right

fol_theorem after_index_value : PRA ⊢ ∀ x n u y a b,
    eval[afterIndexProgram](packedStep(x, n, u, y, a, b)) = pair(u, pair(y, pair(a, b))) := by
  rw [afterIndexProgram]
  pintro x n u y a b
  prw [PRA.eval_comp Primrec.Code.right Primrec.Code.right, PRA.eval_right]

def afterPreviousProgram : Nat := Primrec.Code.comp Primrec.Code.right afterIndexProgram

fol_theorem after_previous_value : PRA ⊢ ∀ x n u y a b,
    eval[afterPreviousProgram](packedStep(x, n, u, y, a, b)) = pair(y, pair(a, b)) := by
  rw [afterPreviousProgram]
  pintro x n u y a b
  prw [PRA.eval_comp Primrec.Code.right afterIndexProgram, after_index_value, PRA.eval_right]

def afterOutputProgram : Nat := Primrec.Code.comp Primrec.Code.right afterPreviousProgram

fol_theorem after_output_value : PRA ⊢ ∀ x n u y a b,
    eval[afterOutputProgram](packedStep(x, n, u, y, a, b)) = pair(a, b) := by
  rw [afterOutputProgram]
  pintro x n u y a b
  prw [PRA.eval_comp Primrec.Code.right afterPreviousProgram, after_previous_value, PRA.eval_right]

def previousResultFieldProgram : Nat := Primrec.Code.comp Primrec.Code.left afterIndexProgram

fol_theorem previous_result_field_value : PRA ⊢ ∀ x n u y a b,
    eval[previousResultFieldProgram](packedStep(x, n, u, y, a, b)) = u := by
  rw [previousResultFieldProgram]
  pintro x n u y a b
  prw [PRA.eval_comp Primrec.Code.left afterIndexProgram, after_index_value, PRA.eval_left]

def outputFieldProgram : Nat := Primrec.Code.comp Primrec.Code.left afterPreviousProgram

fol_theorem output_field_value : PRA ⊢ ∀ x n u y a b,
    eval[outputFieldProgram](packedStep(x, n, u, y, a, b)) = y := by
  rw [outputFieldProgram]
  pintro x n u y a b
  prw [PRA.eval_comp Primrec.Code.left afterPreviousProgram, after_previous_value, PRA.eval_left]

def previousProofFieldProgram : Nat := Primrec.Code.comp Primrec.Code.left afterOutputProgram

fol_theorem previous_proof_field_value : PRA ⊢ ∀ x n u y a b,
    eval[previousProofFieldProgram](packedStep(x, n, u, y, a, b)) = a := by
  rw [previousProofFieldProgram]
  pintro x n u y a b
  prw [PRA.eval_comp Primrec.Code.left afterOutputProgram, after_output_value, PRA.eval_left]

def childProofFieldProgram : Nat := Primrec.Code.comp Primrec.Code.right afterOutputProgram

fol_theorem child_proof_field_value : PRA ⊢ ∀ x n u y a b,
    eval[childProofFieldProgram](packedStep(x, n, u, y, a, b)) = b := by
  rw [childProofFieldProgram]
  pintro x n u y a b
  prw [PRA.eval_comp Primrec.Code.right afterOutputProgram, after_output_value, PRA.eval_right]

def parameterNumProgram : Nat := numAtProgram Primrec.Code.left

fol_theorem parameter_num_value : PRA ⊢ ∀ x n u y a b,
    eval[parameterNumProgram](packedStep(x, n, u, y, a, b)) = numCode(x) := by
  rw [parameterNumProgram]
  pintro x n u y a b
  prw [num_at_program_value Primrec.Code.left, PRA.eval_left]

def indexNumProgram : Nat := numAtProgram stepIndexProgram

fol_theorem index_num_value : PRA ⊢ ∀ x n u y a b,
    eval[indexNumProgram](packedStep(x, n, u, y, a, b)) = numCode(n) := by
  rw [indexNumProgram]
  pintro x n u y a b
  prw [num_at_program_value stepIndexProgram, step_index_value]

def previousNumProgram : Nat := numAtProgram previousResultFieldProgram

fol_theorem previous_num_value : PRA ⊢ ∀ x n u y a b,
    eval[previousNumProgram](packedStep(x, n, u, y, a, b)) = numCode(u) := by
  rw [previousNumProgram]
  pintro x n u y a b
  prw [num_at_program_value previousResultFieldProgram, previous_result_field_value]

def outputNumProgram : Nat := numAtProgram outputFieldProgram

fol_theorem output_num_value : PRA ⊢ ∀ x n u y a b,
    eval[outputNumProgram](packedStep(x, n, u, y, a, b)) = numCode(y) := by
  rw [outputNumProgram]
  pintro x n u y a b
  prw [num_at_program_value outputFieldProgram, output_field_value]

def nextIndexProgram : Nat := Primrec.Code.comp Primrec.Code.succ stepIndexProgram

fol_theorem next_index_value : PRA ⊢ ∀ x n u y a b,
    eval[nextIndexProgram](packedStep(x, n, u, y, a, b)) = succ(n) := by
  rw [nextIndexProgram]
  pintro x n u y a b
  prw [PRA.eval_comp Primrec.Code.succ stepIndexProgram, step_index_value, PRA.eval_succ]

def previousPairInputProgram : Nat := Primrec.Code.pair Primrec.Code.left stepIndexProgram

fol_theorem previous_pair_input_value : PRA ⊢ ∀ x n u y a b,
    eval[previousPairInputProgram](packedStep(x, n, u, y, a, b)) = pair(x, n) := by
  rw [previousPairInputProgram]
  pintro x n u y a b
  prw [PRA.eval_pair Primrec.Code.left stepIndexProgram, PRA.eval_left, step_index_value]

def nextPairInputProgram : Nat := Primrec.Code.pair Primrec.Code.left nextIndexProgram

fol_theorem next_pair_input_value : PRA ⊢ ∀ x n u y a b,
    eval[nextPairInputProgram](packedStep(x, n, u, y, a, b)) = pair(x, succ(n)) := by
  rw [nextPairInputProgram]
  pintro x n u y a b
  prw [PRA.eval_pair Primrec.Code.left nextIndexProgram, PRA.eval_left, next_index_value]

def innerPairInputProgram : Nat := Primrec.Code.pair stepIndexProgram previousResultFieldProgram

fol_theorem inner_pair_input_value : PRA ⊢ ∀ x n u y a b,
    eval[innerPairInputProgram](packedStep(x, n, u, y, a, b)) = pair(n, u) := by
  rw [innerPairInputProgram]
  pintro x n u y a b
  prw [PRA.eval_pair stepIndexProgram previousResultFieldProgram, step_index_value,
    previous_result_field_value]

def outerPairInputProgram : Nat := Primrec.Code.pair Primrec.Code.left innerPairInputProgram

fol_theorem outer_pair_input_value : PRA ⊢ ∀ x n u y a b,
    eval[outerPairInputProgram](packedStep(x, n, u, y, a, b)) = pair(x, pair(n, u)) := by
  rw [outerPairInputProgram]
  pintro x n u y a b
  prw [PRA.eval_pair Primrec.Code.left innerPairInputProgram, PRA.eval_left,
    inner_pair_input_value]

def priorPairProgram : Nat := pairTermProgram parameterNumProgram indexNumProgram

fol_theorem prior_pair_value : PRA ⊢ ∀ x n u y a b,
    eval[priorPairProgram](packedStep(x, n, u, y, a, b)) = pairTermNumAt(x, n) := by
  rw [priorPairProgram]
  pintro x n u y a b
  prw [pair_term_program_value parameterNumProgram indexNumProgram, parameter_num_value,
    index_num_value]

def priorNumberProgram : Nat := numAtProgram previousPairInputProgram

fol_theorem prior_number_value : PRA ⊢ ∀ x n u y a b,
    eval[priorNumberProgram](packedStep(x, n, u, y, a, b)) = numCode(pair(x, n)) := by
  rw [priorNumberProgram]
  pintro x n u y a b
  prw [num_at_program_value previousPairInputProgram, previous_pair_input_value]

def nextNumberProgram : Nat := numAtProgram nextPairInputProgram

fol_theorem next_number_value : PRA ⊢ ∀ x n u y a b,
    eval[nextNumberProgram](packedStep(x, n, u, y, a, b)) = numCode(pair(x, succ(n))) := by
  rw [nextNumberProgram]
  pintro x n u y a b
  prw [num_at_program_value nextPairInputProgram, next_pair_input_value]

def innerNumberProgram : Nat := numAtProgram innerPairInputProgram

fol_theorem inner_number_program_value : PRA ⊢ ∀ x n u y a b,
    eval[innerNumberProgram](packedStep(x, n, u, y, a, b)) = numCode(pair(n, u)) := by
  rw [innerNumberProgram]
  pintro x n u y a b
  prw [num_at_program_value innerPairInputProgram, inner_pair_input_value]

def outerNumberProgram : Nat := numAtProgram outerPairInputProgram

fol_theorem outer_number_program_value : PRA ⊢ ∀ x n u y a b,
    eval[outerNumberProgram](packedStep(x, n, u, y, a, b)) = numCode(pair(x, pair(n, u))) := by
  rw [outerNumberProgram]
  pintro x n u y a b
  prw [num_at_program_value outerPairInputProgram, outer_pair_input_value]

def previousApplicationProgram (e t n : Nat) : Nat := appProgram e (pairTermProgram t n)

def successorApplicationProgram (e t n : Nat) : Nat :=
  appProgram e (pairTermProgram t (Pair.successorTermProgram n))

def innerArgumentProgram (e t n : Nat) : Nat := pairTermProgram n (previousApplicationProgram e t n)

def outerArgumentProgram (e t n : Nat) : Nat := pairTermProgram t (innerArgumentProgram e t n)

def stepApplicationProgram (e g t n : Nat) : Nat := appProgram g (outerArgumentProgram e t n)

def stepEquationProgram (e g t n : Nat) : Nat :=
  equationProgram (successorApplicationProgram e t n) (stepApplicationProgram e g t n)

fol_theorem previous_application_value (e t n : Nat) : PRA ⊢ ∀ x,
    eval[previousApplicationProgram e t n](x) = applicationCode(${num e},
      Pair.pairTermCode(eval[t](x), eval[n](x))) := by
  rw [previousApplicationProgram]
  pintro x
  prw [app_program_value e (pairTermProgram t n), pair_term_program_value t n]

fol_theorem successor_application_value (e t n : Nat) : PRA ⊢ ∀ x,
    eval[successorApplicationProgram e t n](x) = applicationCode(${num e},
      Pair.pairTermCode(eval[t](x), Pair.successorTermCode(eval[n](x)))) := by
  rw [successorApplicationProgram]
  pintro x
  prw [app_program_value e (pairTermProgram t (Pair.successorTermProgram n)),
    pair_term_program_value t (Pair.successorTermProgram n),
    Pair.successor_term_program_value n]

fol_theorem inner_argument_value (e t n : Nat) : PRA ⊢ ∀ x,
    eval[innerArgumentProgram e t n](x) = Pair.pairTermCode(eval[n](x),
      applicationCode(${num e}, Pair.pairTermCode(eval[t](x), eval[n](x)))) := by
  rw [innerArgumentProgram]
  pintro x
  prw [pair_term_program_value n (previousApplicationProgram e t n),
    previous_application_value e t n]

fol_theorem outer_argument_value (e t n : Nat) : PRA ⊢ ∀ x,
    eval[outerArgumentProgram e t n](x) = Pair.pairTermCode(eval[t](x),
      Pair.pairTermCode(eval[n](x),
        applicationCode(${num e}, Pair.pairTermCode(eval[t](x), eval[n](x))))) := by
  rw [outerArgumentProgram]
  pintro x
  prw [pair_term_program_value t (innerArgumentProgram e t n), inner_argument_value e t n]

fol_theorem step_application_value (e g t n : Nat) : PRA ⊢ ∀ x,
    eval[stepApplicationProgram e g t n](x) = applicationCode(${num g},
      Pair.pairTermCode(eval[t](x), Pair.pairTermCode(eval[n](x),
        applicationCode(${num e}, Pair.pairTermCode(eval[t](x), eval[n](x)))))) := by
  rw [stepApplicationProgram]
  pintro x
  prw [app_program_value g (outerArgumentProgram e t n), outer_argument_value e t n]

fol_theorem step_equation_program_value (e g t n : Nat) : PRA ⊢ ∀ x,
    eval[stepEquationProgram e g t n](x) =
      stepEquationCode(${num e}, ${num g}, eval[t](x), eval[n](x)) := by
  rw [stepEquationProgram]
  pintro x
  prw [equation_program_value (successorApplicationProgram e t n)
      (stepApplicationProgram e g t n), successor_application_value e t
      n, step_application_value e g t n, eval_const_language]

def openAxiomProgram (f g : Nat) : Nat :=
  stepEquationProgram (Primrec.Code.rec f g) g parameterNumProgram (Primrec.Code.const 1)

def fullAxiomProgram (f g : Nat) : Nat :=
  stepEquationProgram (Primrec.Code.rec f g) g parameterNumProgram indexNumProgram

fol_theorem open_axiom_program_value (f g : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[openAxiomProgram f g](packedStep(x, n, u, y, a, b)) =
      (succOpen f g)(x) := by
  rw [openAxiomProgram]
  pintro x n u y a b
  prw [step_equation_program_value (Primrec.Code.rec f g) g parameterNumProgram
      (Primrec.Code.const 1),
    parameter_num_value, constant_value 1]

fol_theorem full_axiom_program_value (f g : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[fullAxiomProgram f g](packedStep(x, n, u, y, a, b)) =
      (succInstance f g)(x, n) := by
  rw [fullAxiomProgram]
  pintro x n u y a b
  prw [step_equation_program_value (Primrec.Code.rec f g) g parameterNumProgram indexNumProgram,
    parameter_num_value, index_num_value]

def firstAxiomProgram (f g : Nat) : Nat :=
  instanceProofProgram (Primrec.Code.comp Formula.all.code (openAxiomProgram f g))
    (Formula.all (succBody f g)) (succ_universal.witness f g)

fol_theorem first_axiom_program_value (f g : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[firstAxiomProgram f g](packedStep(x, n, u, y, a, b)) =
      (succFirstProof f g)(x) := by
  rw [firstAxiomProgram]
  pintro x n u y a b
  prw [instance_program (Primrec.Code.comp Formula.all.code (openAxiomProgram f g))
      (Formula.all (succBody f g)) (succ_universal.witness f g), PRA.eval_comp Formula.all.code
      (openAxiomProgram f g), open_axiom_program_value f g]

def dynamicAxiomLeafProgram (a b : Nat) : Nat :=
  Primrec.Code.comp Proof.axiom.code (Primrec.Code.comp Formula.imp.code
    (Primrec.Code.pair (Primrec.Code.comp Formula.all.code a) b))

def dynamicInstanceProgram (a b p : Nat) : Nat :=
  Primrec.Code.comp Proof.mp.code (Primrec.Code.pair b
    (Primrec.Code.pair (dynamicAxiomLeafProgram a b) p))

fol_theorem dynamic_axiom_leaf_value (a b : Nat) : PRA ⊢ ∀ x,
    eval[dynamicAxiomLeafProgram a b](x) = eval[Proof.axiom.code](eval[Formula.imp.code](pair(
      eval[Formula.all.code](eval[a](x)), eval[b](x)))) := by
  rw [dynamicAxiomLeafProgram]
  pintro x
  prw [PRA.eval_comp Proof.axiom.code
      (Primrec.Code.comp Formula.imp.code
        (Primrec.Code.pair (Primrec.Code.comp Formula.all.code a) b)),
    eval_comp_pair Formula.imp.code (Primrec.Code.comp Formula.all.code a) b,
    PRA.eval_comp Formula.all.code a]

fol_theorem dynamic_instance_value (a b p : Nat) : PRA ⊢ ∀ x,
    eval[dynamicInstanceProgram a b p](x) = mpInstance(eval[a](x), eval[b](x), eval[p](x)) := by
  rw [dynamicInstanceProgram]
  pintro x
  prw [eval_comp_pair Proof.mp.code b (Primrec.Code.pair (dynamicAxiomLeafProgram a b) p),
    PRA.eval_pair (dynamicAxiomLeafProgram a b) p, dynamic_axiom_leaf_value a b]

def successorAxiomProgram (f g : Nat) : Nat :=
  dynamicInstanceProgram (openAxiomProgram f g) (fullAxiomProgram f g) (firstAxiomProgram f g)

fol_theorem successor_axiom_program_value (f g : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[successorAxiomProgram f g](packedStep(x, n, u, y, a, b)) =
      (succInstanceProof f g)(x, n) := by
  rw [successorAxiomProgram]
  pintro x n u y a b
  prw [dynamic_instance_value (openAxiomProgram f g) (fullAxiomProgram f g)
      (firstAxiomProgram f g), open_axiom_program_value f g, full_axiom_program_value f
      g, first_axiom_program_value f g]

def reflexivityProgram (a : Nat) : Nat := Primrec.Code.comp Proof.axiom.code (equationProgram a a)

fol_theorem reflexivity_program_value (a : Nat) : PRA ⊢ ∀ x,
    eval[reflexivityProgram a](x) = reflProof(eval[a](x)) := by
  rw [reflexivityProgram]
  pintro x
  prw [PRA.eval_comp Proof.axiom.code (equationProgram a a), equation_program_value a a]

def priorExpressionProgram (c : Nat) : Nat :=
  previousApplicationProgram c parameterNumProgram indexNumProgram

fol_theorem prior_expression_value (c : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[priorExpressionProgram c](packedStep(x, n, u, y, a, b)) =
      (priorAt c)(x, n) := by
  rw [priorExpressionProgram]
  pintro x n u y a b
  prw [previous_application_value c parameterNumProgram indexNumProgram, parameter_num_value,
    index_num_value]

def priorNumericApplicationProgram (c : Nat) : Nat :=
  appProgram c priorNumberProgram

fol_theorem prior_numeric_application_value (c : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[priorNumericApplicationProgram c](packedStep(x, n, u, y, a, b)) =
      (numericInput c)(x, n) := by
  rw [priorNumericApplicationProgram]
  pintro x n u y a b
  prw [app_program_value c priorNumberProgram, prior_number_value]

def priorCongruenceProgram (c p : Nat) : Nat :=
  congruenceProgram c priorPairProgram priorNumberProgram
    (Primrec.Code.comp p previousPairInputProgram)

fol_theorem prior_congruence_program_value (c p : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[priorCongruenceProgram c p](packedStep(x, n, u, y, a, b)) =
      (priorCongruence c p)(x, n) := by
  rw [priorCongruenceProgram]
  pintro x n u y a b
  prw [congruence_program_value c priorPairProgram priorNumberProgram
      (Primrec.Code.comp p previousPairInputProgram),
    prior_pair_value, prior_number_value, PRA.eval_comp p previousPairInputProgram,
    previous_pair_input_value]

def priorProofProgram (c p : Nat) : Nat :=
  transitivityProgram (priorExpressionProgram c) (priorNumericApplicationProgram c)
    previousNumProgram (priorCongruenceProgram c p) previousProofFieldProgram

fol_theorem prior_proof_program_value (c p : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[priorProofProgram c p](packedStep(x, n, u, y, a, b)) =
      (priorProof c p)(x, n, u, a) := by
  rw [priorProofProgram]
  pintro x n u y a b
  prw [transitivity_program_value (priorExpressionProgram c)
      (priorNumericApplicationProgram c) previousNumProgram
      (priorCongruenceProgram c p) previousProofFieldProgram, prior_expression_value
      c, prior_numeric_application_value c, previous_num_value, prior_congruence_program_value c
      p, previous_proof_field_value]

def innerExpressionProgram (c : Nat) : Nat :=
  innerArgumentProgram c parameterNumProgram indexNumProgram

fol_theorem inner_expression_value (c : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[innerExpressionProgram c](packedStep(x, n, u, y, a, b)) =
      (innerAt c)(x, n) := by
  rw [innerExpressionProgram]
  pintro x n u y a b
  prw [inner_argument_value c parameterNumProgram indexNumProgram, parameter_num_value,
    index_num_value]

def innerMiddleProgram : Nat :=
  pairTermProgram indexNumProgram previousNumProgram

fol_theorem inner_middle_program_value : PRA ⊢ ∀ x n u y a b,
    eval[innerMiddleProgram](packedStep(x, n, u, y, a, b)) =
      pairTermNumAt(n, u) := by
  rw [innerMiddleProgram]
  pintro x n u y a b
  prw [pair_term_program_value indexNumProgram previousNumProgram, index_num_value,
    previous_num_value]

def innerCongruenceProgram (c p : Nat) : Nat :=
  Pairing.pairCongruenceProgram indexNumProgram (priorExpressionProgram c)
    indexNumProgram previousNumProgram (reflexivityProgram indexNumProgram) (priorProofProgram c p)

fol_theorem inner_congruence_program_value (c p : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[innerCongruenceProgram c p](packedStep(x, n, u, y, a, b)) =
      Pairing.pairCongruenceProof(numCode(n), (priorAt c)(x, n), numCode(n),
      numCode(u), reflProof(numCode(n)), (priorProof c p)(x, n, u, a)) := by
  rw [innerCongruenceProgram]
  pintro x n u y a b
  prw [Pairing.pair_congruence_program_value indexNumProgram (priorExpressionProgram c)
      indexNumProgram previousNumProgram (reflexivityProgram indexNumProgram)
      (priorProofProgram c p),
    reflexivity_program_value indexNumProgram, index_num_value, prior_expression_value c,
    previous_num_value, prior_proof_program_value c p]

def innerProofProgram (c p : Nat) : Nat :=
  transitivityProgram (innerExpressionProgram c) innerMiddleProgram innerNumberProgram
    (innerCongruenceProgram c p) (Primrec.Code.comp p innerPairInputProgram)

fol_theorem inner_proof_program_value (c p : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[innerProofProgram c p](packedStep(x, n, u, y, a, b)) =
      (innerProof c p)(x, n, u, a) := by
  rw [innerProofProgram]
  pintro x n u y a b
  prw [transitivity_program_value (innerExpressionProgram c) innerMiddleProgram innerNumberProgram
      (innerCongruenceProgram c p) (Primrec.Code.comp p innerPairInputProgram),
    inner_expression_value c, inner_middle_program_value, inner_number_program_value,
    inner_congruence_program_value c p, PRA.eval_comp p innerPairInputProgram,
    inner_pair_input_value]

def outerExpressionProgram (c : Nat) : Nat :=
  outerArgumentProgram c parameterNumProgram indexNumProgram

fol_theorem outer_expression_value (c : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[outerExpressionProgram c](packedStep(x, n, u, y, a, b)) =
      (outerAt c)(x, n) := by
  rw [outerExpressionProgram]
  pintro x n u y a b
  prw [outer_argument_value c parameterNumProgram indexNumProgram, parameter_num_value,
    index_num_value]

def outerMiddleProgram : Nat :=
  pairTermProgram parameterNumProgram innerNumberProgram

fol_theorem outer_middle_program_value : PRA ⊢ ∀ x n u y a b,
    eval[outerMiddleProgram](packedStep(x, n, u, y, a, b)) =
      pairTermNumAt(x, pair(n, u)) := by
  rw [outerMiddleProgram]
  pintro x n u y a b
  prw [pair_term_program_value parameterNumProgram innerNumberProgram, parameter_num_value,
    inner_number_program_value]

def outerCongruenceProgram (c p : Nat) : Nat :=
  Pairing.pairCongruenceProgram parameterNumProgram (innerExpressionProgram c) parameterNumProgram
    innerNumberProgram (reflexivityProgram parameterNumProgram) (innerProofProgram c p)

fol_theorem outer_congruence_program_value (c p : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[outerCongruenceProgram c p](packedStep(x, n, u, y, a, b)) =
      Pairing.pairCongruenceProof(numCode(x), (innerAt c)(x, n), numCode(x),
      numCode(pair(n, u)), reflProof(numCode(x)),
      (innerProof c p)(x, n, u, a)) := by
  rw [outerCongruenceProgram]
  pintro x n u y a b
  prw [Pairing.pair_congruence_program_value parameterNumProgram (innerExpressionProgram c)
      parameterNumProgram innerNumberProgram (reflexivityProgram parameterNumProgram)
      (innerProofProgram c p),
    reflexivity_program_value parameterNumProgram, parameter_num_value, inner_expression_value c,
    inner_number_program_value, inner_proof_program_value c p]

def outerProofProgram (c p : Nat) : Nat :=
  transitivityProgram (outerExpressionProgram c) outerMiddleProgram outerNumberProgram
    (outerCongruenceProgram c p) (Primrec.Code.comp p outerPairInputProgram)

theorem transitivityProof_congr : ∀ a b c p q u v w r s,
    (PRA ⊢ ${a} = u) → (PRA ⊢ ${b} = v) → (PRA ⊢ ${c} = w) →
    (PRA ⊢ ${p} = r) → (PRA ⊢ ${q} = s) →
    (PRA ⊢ transitivityProof(${a}, ${b}, ${c}, ${p}, ${q}) =
      transitivityProof(${u}, ${v}, ${w}, ${r}, ${s})) := by
  intro a b c p q u v w r s ha hb hc hp hq
  prw [ha, hb, hc, hp, hq]

fol_theorem outer_proof_program_value (c p : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[outerProofProgram c p](packedStep(x, n, u, y, a, b)) =
      (outerProof c p)(x, n, u, a) := by
  rw [outerProofProgram]
  let x := Term.var language 5
  let n := Term.var language 4
  let u := Term.var language 3
  let y := Term.var language 2
  let a := Term.var language 1
  let b := Term.var language 0
  let input := fol_term[PRA | packedStep(${x}, ${n}, ${u}, ${y}, ${a}, ${b})]
  have shape : (PRA ⊢ eval[transitivityProgram (outerExpressionProgram c) outerMiddleProgram
        outerNumberProgram (outerCongruenceProgram c p)
        (Primrec.Code.comp p outerPairInputProgram)](${input}) =
      transitivityProof(eval[outerExpressionProgram c](${input}),
        eval[outerMiddleProgram](${input}), eval[outerNumberProgram](${input}),
        eval[outerCongruenceProgram c p](${input}),
        eval[Primrec.Code.comp p outerPairInputProgram](${input}))) := by
    pexact (transitivity_program_value
        (outerExpressionProgram c) outerMiddleProgram outerNumberProgram
        (outerCongruenceProgram c p) (Primrec.Code.comp p outerPairInputProgram))[${input}]
  have lhs : (PRA ⊢ eval[outerExpressionProgram c](${input}) = (outerAt c)(${x}, ${n})) := by
    pexact (outer_expression_value c)[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have middle : (PRA ⊢ eval[outerMiddleProgram](${input}) =
      pairTermNumAt(${x}, pair(${n}, ${u}))) := by
    pexact outer_middle_program_value[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have rhs : (PRA ⊢ eval[outerNumberProgram](${input}) =
      numCode(pair(${x}, pair(${n}, ${u})))) := by
    pexact outer_number_program_value[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have major : (PRA ⊢ eval[outerCongruenceProgram c p](${input}) =
      Pairing.pairCongruenceProof(numCode(${x}), (innerAt c)(${x}, ${n}),
        numCode(${x}), numCode(pair(${n}, ${u})), reflProof(numCode(${x})),
        (innerProof c p)(${x}, ${n}, ${u}, ${a}))) := by
    pexact (outer_congruence_program_value c p)[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have minor : (PRA ⊢ eval[Primrec.Code.comp p outerPairInputProgram](${input}) =
      eval[p](pair(${x}, pair(${n}, ${u})))) := by
    ptrans eval[p](eval[outerPairInputProgram](${input}))
    · pexact (PRA.eval_comp p outerPairInputProgram)[${input}]
    · pcongr
      pexact outer_pair_input_value[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have value := transitivityProof_congr _ _ _ _ _ _ _ _ _ _ lhs middle rhs major minor
  have result := Evaluation.trans _ _ _ shape value
  repeat apply FOL.Provable.gen language isAxiom _
  exact result

theorem eval_transitivity_program_congr (a b c p q : Nat) : ∀ x u v w r s,
    (PRA ⊢ eval[a](${x}) = u) → (PRA ⊢ eval[b](${x}) = v) →
    (PRA ⊢ eval[c](${x}) = w) → (PRA ⊢ eval[p](${x}) = r) →
    (PRA ⊢ eval[q](${x}) = s) →
    (PRA ⊢ eval[transitivityProgram a b c p q](${x}) =
      transitivityProof(${u}, ${v}, ${w}, ${r}, ${s})) := by
  intro x u v w r s ha hb hc hp hq
  have shape : (PRA ⊢ eval[transitivityProgram a b c p q](${x}) =
      transitivityProof(eval[a](${x}), eval[b](${x}), eval[c](${x}),
        eval[p](${x}), eval[q](${x}))) := by
    pexact (transitivity_program_value a b c p q)[${x}]
  exact Evaluation.trans _ _ _ shape (transitivityProof_congr _ _ _ _ _ _ _ _ _ _ ha hb hc hp hq)

theorem congruenceProof_congr (e : Nat) : ∀ a b p u v q,
    (PRA ⊢ ${a} = u) → (PRA ⊢ ${b} = v) → (PRA ⊢ ${p} = q) →
    (PRA ⊢ (congruenceProof e)(${a}, ${b}, ${p}) =
      (congruenceProof e)(${u}, ${v}, ${q})) := by
  intro a b p u v q ha hb hp
  prw [ha, hb, hp]

theorem eval_congruence_program_congr (e a b p : Nat) : ∀ x u v q,
    (PRA ⊢ eval[a](${x}) = u) → (PRA ⊢ eval[b](${x}) = v) →
    (PRA ⊢ eval[p](${x}) = q) →
    (PRA ⊢ eval[congruenceProgram e a b p](${x}) = (congruenceProof e)(${u}, ${v}, ${q})) := by
  intro x u v q ha hb hp
  have shape : (PRA ⊢ eval[congruenceProgram e a b p](${x}) =
      (congruenceProof e)(eval[a](${x}), eval[b](${x}), eval[p](${x}))) := by
    pexact (congruence_program_value e a b p)[${x}]
  exact Evaluation.trans _ _ _ shape (congruenceProof_congr e _ _ _ _ _ _ ha hb hp)

def stepLeftProgram (c : Nat) : Nat :=
  successorApplicationProgram c parameterNumProgram indexNumProgram

fol_theorem step_left_program_value (c : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[stepLeftProgram c](packedStep(x, n, u, y, a, b)) =
      (stepLeftAt c)(x, n) := by
  rw [stepLeftProgram]
  pintro x n u y a b
  prw [successor_application_value c parameterNumProgram indexNumProgram, parameter_num_value,
    index_num_value]

def stepRightProgram (c g : Nat) : Nat :=
  stepApplicationProgram c g parameterNumProgram indexNumProgram

fol_theorem step_right_program_value (c g : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[stepRightProgram c g](packedStep(x, n, u, y, a, b)) =
      (stepRightAt c g)(x, n) := by
  rw [stepRightProgram]
  pintro x n u y a b
  prw [step_application_value c g parameterNumProgram indexNumProgram, parameter_num_value,
    index_num_value]

def stepChildApplicationProgram (g : Nat) : Nat :=
  appProgram g outerNumberProgram

fol_theorem step_child_application_value (g : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[stepChildApplicationProgram g](packedStep(x, n, u, y, a, b)) =
      applicationCode(${num g}, numCode(pair(x, pair(n, u)))) := by
  rw [stepChildApplicationProgram]
  pintro x n u y a b
  prw [app_program_value g outerNumberProgram, outer_number_program_value]

def stepCongruenceProgram (c g p : Nat) : Nat :=
  congruenceProgram g (outerExpressionProgram c) outerNumberProgram (outerProofProgram c p)

fol_theorem step_congruence_program_value (c g p : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[stepCongruenceProgram c g p](packedStep(x, n, u, y, a, b)) =
      (congruenceProof g)((outerAt c)(x, n), numCode(pair(x, pair(n, u))),
      (outerProof c p)(x, n, u, a)) := by
  rw [stepCongruenceProgram]
  let x := Term.var language 5
  let n := Term.var language 4
  let u := Term.var language 3
  let y := Term.var language 2
  let a := Term.var language 1
  let b := Term.var language 0
  let input := fol_term[PRA | packedStep(${x}, ${n}, ${u}, ${y}, ${a}, ${b})]
  have lhs : (PRA ⊢ eval[outerExpressionProgram c](${input}) =
      (outerAt c)(${x}, ${n})) := by
    pexact (outer_expression_value c)[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have rhs : (PRA ⊢ eval[outerNumberProgram](${input}) =
      numCode(pair(${x}, pair(${n}, ${u})))) := by
    pexact outer_number_program_value[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have proofValue : (PRA ⊢ eval[outerProofProgram c p](${input}) =
      (outerProof c p)(${x}, ${n}, ${u}, ${a})) := by
    pexact (outer_proof_program_value c p)[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have result := eval_congruence_program_congr g (outerExpressionProgram c) outerNumberProgram
    (outerProofProgram c p) input _ _ _ lhs rhs proofValue
  repeat apply FOL.Provable.gen language isAxiom _
  exact result

def stepTailProgram (c g p : Nat) : Nat :=
  transitivityProgram (stepRightProgram c g) (stepChildApplicationProgram g) outputNumProgram
    (stepCongruenceProgram c g p) childProofFieldProgram

fol_theorem step_tail_program_value (c g p : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[stepTailProgram c g p](packedStep(x, n, u, y, a, b)) =
      (stepTailAt c g p)(x, n, u, y, a, b) := by
  rw [stepTailProgram]
  let x := Term.var language 5
  let n := Term.var language 4
  let u := Term.var language 3
  let y := Term.var language 2
  let a := Term.var language 1
  let b := Term.var language 0
  let input := fol_term[PRA | packedStep(${x}, ${n}, ${u}, ${y}, ${a}, ${b})]
  have lhs : (PRA ⊢ eval[stepRightProgram c g](${input}) =
      (stepRightAt c g)(${x}, ${n})) := by
    pexact (step_right_program_value c g)[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have middle : (PRA ⊢ eval[stepChildApplicationProgram g](${input}) =
      applicationCode(${num g}, numCode(pair(${x}, pair(${n}, ${u}))))) := by
    pexact (step_child_application_value g)[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have rhs : (PRA ⊢ eval[outputNumProgram](${input}) =
      numCode(${y})) := by
    pexact output_num_value[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have major : (PRA ⊢ eval[stepCongruenceProgram c g p](${input}) =
      (congruenceProof g)((outerAt c)(${x}, ${n}),
        numCode(pair(${x}, pair(${n}, ${u}))),
        (outerProof c p)(${x}, ${n}, ${u}, ${a}))) := by
    pexact (step_congruence_program_value c g p)[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have minor : (PRA ⊢ eval[childProofFieldProgram](${input}) =
      ${b}) := by
    pexact child_proof_field_value[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have result := eval_transitivity_program_congr (stepRightProgram c g)
    (stepChildApplicationProgram g) outputNumProgram (stepCongruenceProgram c g p)
    childProofFieldProgram input _ _ _ _ _
    lhs middle rhs major minor
  repeat apply FOL.Provable.gen language isAxiom _
  exact result

def stepViaAxiomProgram (f g p : Nat) : Nat :=
  transitivityProgram (stepLeftProgram (Primrec.Code.rec f g))
    (stepRightProgram (Primrec.Code.rec f g) g) outputNumProgram
    (successorAxiomProgram f g) (stepTailProgram (Primrec.Code.rec f g) g p)

fol_theorem step_via_axiom_program_value (f g p : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[stepViaAxiomProgram f g p](packedStep(x, n, u, y, a, b)) =
      (stepViaAxiom f g p)(x, n, u, y, a, b) := by
  rw [stepViaAxiomProgram]
  let x := Term.var language 5
  let n := Term.var language 4
  let u := Term.var language 3
  let y := Term.var language 2
  let a := Term.var language 1
  let b := Term.var language 0
  let input := fol_term[PRA | packedStep(${x}, ${n}, ${u}, ${y}, ${a}, ${b})]
  have lhs : (PRA ⊢ eval[stepLeftProgram (Primrec.Code.rec f g)](${input}) =
      (stepLeftAt (Primrec.Code.rec f g))(${x}, ${n})) := by
    pexact (step_left_program_value (Primrec.Code.rec f g))[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have middle : (PRA ⊢ eval[stepRightProgram (Primrec.Code.rec f g) g](${input}) =
      (stepRightAt (Primrec.Code.rec f g) g)(${x}, ${n})) := by
    pexact (step_right_program_value (Primrec.Code.rec f g) g)[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have rhs : (PRA ⊢ eval[outputNumProgram](${input}) =
      numCode(${y})) := by
    pexact output_num_value[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have major : (PRA ⊢ eval[successorAxiomProgram f g](${input}) =
      (succInstanceProof f g)(${x}, ${n})) := by
    pexact (successor_axiom_program_value f g)[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have minor : (PRA ⊢ eval[stepTailProgram (Primrec.Code.rec f g) g p](${input}) =
      (stepTailAt (Primrec.Code.rec f g) g p)(${x}, ${n}, ${u}, ${y}, ${a}, ${b})) := by
    pexact (step_tail_program_value (Primrec.Code.rec f g) g p)[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have result := eval_transitivity_program_congr (stepLeftProgram (Primrec.Code.rec f g))
    (stepRightProgram (Primrec.Code.rec f g) g) outputNumProgram (successorAxiomProgram f g)
    (stepTailProgram (Primrec.Code.rec f g) g p) input _ _ _ _ _ lhs middle rhs major minor
  repeat apply FOL.Provable.gen language isAxiom _
  exact result

def nextNumericApplicationProgram (c : Nat) : Nat :=
  appProgram c nextNumberProgram

fol_theorem next_numeric_application_value (c : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[nextNumericApplicationProgram c](packedStep(x, n, u, y, a, b)) =
      (numericInput c)(x, succ(n)) := by
  rw [nextNumericApplicationProgram]
  pintro x n u y a b
  prw [app_program_value c nextNumberProgram, next_number_value]

def nextNormalizeProgram (c p : Nat) : Nat :=
  Primrec.Code.comp (liftedPairProgram c p) nextPairInputProgram

fol_theorem next_normalize_value (c p : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[nextNormalizeProgram c p](packedStep(x, n, u, y, a, b)) =
      (liftedPairAt c p)(x, succ(n)) := by
  rw [nextNormalizeProgram]
  pintro x n u y a b
  ptrans eval[liftedPairProgram c p](pair(x, succ(n)))
  · prw [PRA.eval_comp (liftedPairProgram c p) nextPairInputProgram, next_pair_input_value]
  · pexact (lifted_pair_value c p)[x, succ(n)]

/-- Produce the successor proof from `pair x (pair n (pair u (pair y (pair a b))))`. -/
def makeSuccProgram (f g p : Nat) : Nat :=
  transitivityProgram (nextNumericApplicationProgram (Primrec.Code.rec f g))
    (stepLeftProgram (Primrec.Code.rec f g)) outputNumProgram
    (nextNormalizeProgram (Primrec.Code.rec f g) p) (stepViaAxiomProgram f g p)

fol_theorem make_succ_value (f g p : Nat) : PRA ⊢ ∀ x n u y a b,
    eval[makeSuccProgram f g p](packedStep(x, n, u, y, a, b)) =
      (makeSuccAt f g p)(x, n, u, y, a, b) := by
  rw [makeSuccProgram]
  let x := Term.var language 5
  let n := Term.var language 4
  let u := Term.var language 3
  let y := Term.var language 2
  let a := Term.var language 1
  let b := Term.var language 0
  let input := fol_term[PRA | packedStep(${x}, ${n}, ${u}, ${y}, ${a}, ${b})]
  have lhs : (PRA ⊢ eval[nextNumericApplicationProgram (Primrec.Code.rec f g)](${input}) =
      (numericInput (Primrec.Code.rec f g))(${x}, succ(${n}))) := by
    pexact (next_numeric_application_value (Primrec.Code.rec f g))[
      ${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have middle : (PRA ⊢ eval[stepLeftProgram (Primrec.Code.rec f g)](${input}) =
      (stepLeftAt (Primrec.Code.rec f g))(${x}, ${n})) := by
    pexact (step_left_program_value (Primrec.Code.rec f g))[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have rhs : (PRA ⊢ eval[outputNumProgram](${input}) =
      numCode(${y})) := by
    pexact output_num_value[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have major : (PRA ⊢ eval[nextNormalizeProgram (Primrec.Code.rec f g) p](${input}) =
      (liftedPairAt (Primrec.Code.rec f g) p)(${x}, succ(${n}))) := by
    pexact (next_normalize_value (Primrec.Code.rec f g) p)[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have minor : (PRA ⊢ eval[stepViaAxiomProgram f g p](${input}) =
      (stepViaAxiom f g p)(${x}, ${n}, ${u}, ${y}, ${a}, ${b})) := by
    pexact (step_via_axiom_program_value f g p)[${x}, ${n}, ${u}, ${y}, ${a}, ${b}]
  have result := eval_transitivity_program_congr
    (nextNumericApplicationProgram (Primrec.Code.rec f g))
    (stepLeftProgram (Primrec.Code.rec f g)) outputNumProgram
    (nextNormalizeProgram (Primrec.Code.rec f g) p)
    (stepViaAxiomProgram f g p) input _ _ _ _ _ lhs middle rhs major minor
  repeat apply FOL.Provable.gen language isAxiom _
  exact result

/-- The proof program follows the recursion counter to produce a proof at each input. -/
def recProofProgram (f g qf qg p : Nat) : Nat :=
  Primrec.Code.rec (baseProofProgram f qf (makeZeroProgram f g p))
    (stepProofProgram f g qg (makeSuccProgram f g p))

fol_theorem replace_proof_accepted (e : Nat) : PRA ⊢ ∀ x y p q,
    p = q → equationProofOf e x y q → equationProofOf e x y p := by
  pintro x y p q same h
  psubst same
  pexact h

fol_def stepValueEquality over PRA (f g p : Nat) : formula of 6 := fun x n u y a b =>
  eval[makeSuccProgram f g p](packedStep(x, n, u, y, a, b)) =
    (makeSuccAt f g p)(x, n, u, y, a, b)

fol_def stepProofOf over PRA (f g p : Nat) : formula of 6 := fun x n u y a b =>
  (equationProofOf (Primrec.Code.rec f g) pair(x, succ(n)) y
    eval[makeSuccProgram f g p](packedStep(x, n, u, y, a, b)))

fol_theorem open_step_value (f g p : Nat) : PRA ⊢ free b a y u n x |
    (stepValueEquality f g p)(x, n, u, y, a, b) := by
  pexact (make_succ_value f g p)[x, n, u, y, a, b]

fol_theorem open_step_transport (f g p : Nat) : PRA ⊢ free b a y u n x |
    (stepValueEquality f g p)(x, n, u, y, a, b) →
    (acceptedStepResult f g p)(x, n, u, y, a, b) →
    (stepProofOf f g p)(x, n, u, y, a, b) := by
  pexact (replace_proof_accepted (Primrec.Code.rec f g))[pair(x, succ(n)), y,
    eval[makeSuccProgram f g p](packedStep(x, n, u, y, a, b)),
    (makeSuccAt f g p)(x, n, u, y, a, b)]

fol_theorem transport_implications (P Q C D : Nat) : PRA ⊢
    (${C} → ${D}) → (${P} → ${Q} → ${C}) → ${P} → ${Q} → ${D} := by
  pintro transfer rule p q
  papply transfer
  papply rule
  · pexact p
  · pexact q

theorem make_succ_accepted (f g p : Nat) :
    (PRA ⊢ (provesPair p)) →
    (PRA ⊢ ∀ x n u y a b, equationProofOf (Primrec.Code.rec f g) pair(x, n) u a →
      equationProofOf g pair(x, pair(n, u)) y b →
      (equationProofOf (Primrec.Code.rec f g) pair(x, succ(n)) y
        eval[makeSuccProgram f g p](pair(x, pair(n, pair(u, pair(y, pair(a, b)))))))) := by
  intro pairing
  let c := Primrec.Code.rec f g
  let x := Term.var language 5
  let n := Term.var language 4
  let u := Term.var language 3
  let y := Term.var language 2
  let a := Term.var language 1
  let b := Term.var language 0
  let H := fol_formula[PRA | (provesPair p)]
  let P := fol_formula[PRA | equationProofOf c pair(${x}, ${n}) ${u} ${a}]
  let Q := fol_formula[PRA | equationProofOf g pair(${x}, pair(${n}, ${u})) ${y} ${b}]
  let U := fol_formula[PRA | (acceptedStepInput c p)(${x}, ${n})]
  let V := fol_formula[PRA | (acceptedStepAxiom f g p)(
    ${x}, ${n}, ${u}, ${y}, ${a}, ${b})]
  let C := fol_formula[PRA | (acceptedStepResult f g p)(
    ${x}, ${n}, ${u}, ${y}, ${a}, ${b})]
  let D := fol_formula[PRA | (stepProofOf f g p)(
    ${x}, ${n}, ${u}, ${y}, ${a}, ${b})]
  have certified := combine_accepted H P Q U V C
    (open_step_input f g p) (open_step_axiom f g p) (open_step_trans f g p)
  have previous := Provable.mp language isAxiom _ _ certified pairing
  have transfer := Provable.mp language isAxiom _ _
    (open_step_transport f g p) (open_step_value f g p)
  have transport := Provable.mp language isAxiom _ _
    (transport_implications P Q C D) transfer
  exact close_step_formula _ (Provable.mp language isAxiom _ _ transport previous)

fol_theorem apply_closed_recursion_rules (F G Z S C : Nat) : PRA ⊢
    ${Z} → ${S} → (${F} → ${G} → ${Z} → ${S} → ${C}) → ${F} → ${G} → ${C} := by
  pintro base step recurse f g
  papply recurse
  · pexact f
  · pexact g
  · pexact base
  · pexact step

/-- The pairing and child proof programs give a proof program for recursion. -/
theorem provesEval_recursion_from_pair (f g qf qg p : Nat) :
    (PRA ⊢ (provesPair p)) →
    (PRA ⊢ (provesEval f qf) → (provesEval g qg) →
      (provesEval (Primrec.Code.rec f g) (recProofProgram f g qf qg p))) := by
  intro pairing
  let F := fol_formula[PRA | (provesEval f qf)]
  let G := fol_formula[PRA | (provesEval g qg)]
  let H := fol_formula[PRA | (provesPair p)]
  let Z := fol_formula[PRA | ∀ x y a, equationProofOf f x y a →
    (equationProofOf (Primrec.Code.rec f g) pair(x, zero) y
      eval[makeZeroProgram f g p](pair(x, pair(y, a))))]
  let S := fol_formula[PRA | ∀ x n u y a b,
    equationProofOf (Primrec.Code.rec f g) pair(x, n) u a →
    equationProofOf g pair(x, pair(n, u)) y b →
    (equationProofOf (Primrec.Code.rec f g) pair(x, succ(n)) y
      eval[makeSuccProgram f g p](pair(x, pair(n, pair(u, pair(y, pair(a, b)))))))]
  let C := fol_formula[PRA |
    (provesEval (Primrec.Code.rec f g) (recProofProgram f g qf qg p))]
  have base : Provable language isAxiom Z :=
    Provable.mp language isAxiom H Z (make_zero_accepted f g p) pairing
  have step : Provable language isAxiom S := make_succ_accepted f g p pairing
  have applyBase := Provable.mp language isAxiom _ _
    (apply_closed_recursion_rules F G Z S C) base
  have applyStep := Provable.mp language isAxiom _ _ applyBase step
  exact Provable.mp language isAxiom _ _ applyStep
    (provesEval_recursion f g qf qg (makeZeroProgram f g p) (makeSuccProgram f g p))

end EquationCompleteness.Recursion

namespace EquationCompleteness

theorem rec_proofs (f g a b : Nat) : EquationProofPair f a → EquationProofPair g b →
    (PRA ⊢ (provesEval ${Primrec.Code.rec f g} ${Recursion.recProofProgram f g (unpairLeft a)
    (unpairLeft b) Pair.pairProofProgram})) := by
  intro hf hg
  let p := Pair.pairProofProgram
  have withPair := Recursion.provesEval_recursion_from_pair f g (unpairLeft a) (unpairLeft b) p
    provesPair_of_program
  have withBase := Provable.mp language isAxiom _ _ withPair (unpairRight a, hf)
  exact Provable.mp language isAxiom _ _ withBase (unpairRight b, hg)

theorem rec_pair_exists : ∀ f g a b,
    EquationProofPair f a → EquationProofPair g b →
    ∃ c, EquationProofPair (Primrec.Code.rec f g) c := by
  intro f g a b ha hb
  let k := Recursion.recProofProgram f g (unpairLeft a) (unpairLeft b) Pair.pairProofProgram
  rcases rec_proofs f g a b ha hb with (p, hp)
  exact (_root_.pair k p, equationProofPair_pair (Primrec.Code.rec f g) k p hp)

/-! ### Induction on primitive recursive programs -/

extract_scoped_witness pair_pair_exists comp_pair_exists rec_pair_exists

/-- Every evaluation program has a proof program and a Hilbert proof of its correctness. -/
theorem equationProofPair_exists (f : Nat) : ∃ c, EquationProofPair f c := by
  rcases zero_pair_exists with (z, hz)
  rcases succ_pair_exists with (s, hs)
  rcases left_pair_exists with (l, hl)
  rcases right_pair_exists with (r, hr)
  obtain_witness
    onPair, pairing from pair_pair_exists
    onComp, composition from comp_pair_exists
    onRec, recursion from rec_pair_exists
  let witness := Primrec.Code.fold z s l r onPair onComp onRec
  have valid := Primrec.Code.fold_induction EquationProofPair isEquationProofPair z s l r
    onPair onComp onRec isEquationProofPair_iff hz hs hl hr pairing composition recursion
  exact (witness f, valid f)

end EquationCompleteness

/-! ### Equation completeness -/

/-- For a given program, PRA turns an evaluation equation into provability of the instance formed
by applying `num` to the input and output. Both the input and the output are variables of
first-order PRA. -/
theorem equation_complete (f : Nat) :
    (PRA ⊢ ∀ x y, eval[f](x) = y →
      (pr language isAxiom.code (evalEquationNum(${num f}, x, y)))) := by
  rcases EquationCompleteness.equationProofPair_exists f with (c, valid)
  exact EquationCompleteness.pr_evalEquationNum_of_pair f c valid

/-! ## Transitivity of provability -/

namespace ProvabilityTransitivity

/-! ### Existential introduction from two proofs -/

theorem provable_ex_of_instantiate (L : Nat) (T : Nat → Nat) : ∀ A B t,
    Formula.instantiate L A t = B →
    t ≤ Formula.imp (Formula.all (Formula.neg A)) (Formula.neg B) →
    Provable L T B → Provable L T (Formula.ex A) := by
  intro A B t instanceEq bound hB
  let U := Formula.all (Formula.neg A)
  have negEq : Formula.instantiate L (Formula.neg A) t = Formula.neg B := by
    rw [Formula.instantiate_neg, instanceEq]
  have bounded : t ≤ Formula.imp U (Formula.instantiate L (Formula.neg A) t) := by
    rw [negEq]
    exact bound
  have inst := provable_imp_instantiate_of_le L T (Formula.neg A) t bounded
  rw [negEq] at inst
  have introduce := Provable.mp L T _ _
    (Provable.imp_neg_swap L T U B) inst
  exact Provable.mp L T B _ introduce hB

theorem le_imp_neg_conj_equal_app : ∀ L j t y B A,
    t ≤ Formula.imp (Formula.all (Formula.neg A))
      (Formula.neg (Formula.conj (Formula.equal L (Term.app L j t) y) B)) := by
  intro L j t y B A
  let u := Term.app L j t
  let a := Formula.equal L u y
  have leA := le_trans _ _ _ (le_of_lt _ _ (Term.args_lt_app L j t))
    (Formula.le_equal_left L u y)
  have underImp := le_trans _ _ _ leA (le_of_lt _ _ (Formula.left_lt_imp a (Formula.neg B)))
  have underConj := le_trans _ _ _ underImp
    (le_of_lt _ _ (Formula.left_lt_imp (Formula.imp a (Formula.neg B)) Formula.falsum))
  have underNeg := le_trans _ _ _ underConj
    (le_of_lt _ _ (Formula.left_lt_imp (Formula.conj a B) Formula.falsum))
  exact le_trans _ _ _ underNeg (le_of_lt _ _ (Formula.right_lt_imp
    (Formula.all (Formula.neg A)) (Formula.neg (Formula.conj a B))))

theorem provable_ex_of_conj_equal_app (L : Nat) (T : Nat → Nat) : ∀ j t y B A,
    Formula.instantiate L A t =
      Formula.conj (Formula.equal L (Term.app L j t) y) B →
    Provable L T (Formula.equal L (Term.app L j t) y) → Provable L T B →
    Provable L T (Formula.ex A) := by
  intro j t y B A instanceEq valid concluded
  exact provable_ex_of_instantiate L T A _ t instanceEq (le_imp_neg_conj_equal_app L j t y B A)
    (Provable.conj' L T _ B valid concluded)

derive_fol_pra (public := true) provable_ex_of_conj_equal_app as pr_ex_of_conj_equal_app

/-! ### The code of the provability sentence -/

theorem pr_num_eq_ex_proofOf (L T : Nat) : ∀ a,
    pr L T (num a) = Formula.ex (proofOf L T (num a) 1) := by
  intro a
  rw [pr, Substitution.shift_num, var_zero_language]

derive_fol_pra (public := true) pr_num_eq_ex_proofOf as pr_num_eq_ex_proofOf_inner

theorem eval_term_var_zero :
    (PRA ⊢ eval[Term.var.code](pair(${num language}, zero)) = ${num 1}) := by
  let x := pair language 0
  have h := Term.var.computedBy x
  rw [unpairLeft_pair, unpairRight_pair, var_zero_language] at h
  have packed := eval_pair_num Term.var.code language 0
  rw [num_zero] at packed
  ptrans eval[Term.var.code](${num x})
  · exact packed
  · exact eval_num_of_evaluates Term.var.code x 1 (Term.var.trace x) h

theorem proofOf_eq_conj (L T : Nat) : ∀ t, proofOf L T t 1 =
    Formula.conj
      (Formula.equal language
        (Term.app language
          (Language.functionFamilyMember language 0 (FOL.isProof.code L T)) (Term.var language 0))
        (num 1))
      (Formula.equal language
        (Term.app language (Language.functionFamilyMember language 0 Proof.conclusion.code)
          (Term.var language 0))
        t) := by
  intro t
  rw [proofOf, num_succ 0, num_zero, var_zero_language]

derive_fol_pra (public := true) proofOf_eq_conj as proofOf_eq_conj_inner

theorem eval_isProof_program_code (L T : Nat) :
    (PRA ⊢ eval[FOL.isProof.code.code L T](zero) = ${num (FOL.isProof.code L T)}) := by
  have h := eval_num_of_evaluates (FOL.isProof.code.code L T) 0 (FOL.isProof.code L T)
    (FOL.isProof.code.trace L T 0) (FOL.isProof.code.computedBy L T 0)
  rw [num_zero] at h
  exact h

theorem eval_conclusion_program_code :
    (PRA ⊢ eval[Proof.conclusion.code.code](zero) = ${num Proof.conclusion.code}) := by
  have h := eval_num_of_evaluates Proof.conclusion.code.code 0 Proof.conclusion.code
    (Proof.conclusion.code.trace 0) (Proof.conclusion.code.computedBy 0)
  rw [num_zero] at h
  exact h

fol_def evalVarZeroEquation over PRA : term of 2 := fun e rhs =>
  eval[Formula.equal.code](pair(eval[language.code](zero), pair(
    eval[Term.app.code](pair(eval[language.code](zero), pair(
      eval[Language.functionFamilyMember.code](pair(eval[language.code](zero), pair(zero, e))),
      eval[Term.var.code](pair(eval[language.code](zero), zero))))), rhs)))

fol_theorem proofOf_num_eq_conj (L T : Nat) : PRA ⊢ ∀ a,
    eval[proofOf.code L T](pair(eval[num.code](a), succ(zero))) = eval[Formula.conj.code](pair(
      evalEquation(${num (FOL.isProof.code L T)}, ${num 1},
        NumShift.numCode(succ(zero))),
      evalEquation(${num FOL.Proof.conclusion.code}, ${num 1},
        NumShift.numCode(a)))) := by
  pintro a
  ptrans eval[Formula.conj.code](pair(
    evalVarZeroEquation(eval[FOL.isProof.code.code L T](zero),
      NumShift.numCode(succ(zero))),
    evalVarZeroEquation(eval[Proof.conclusion.code.code](zero), NumShift.numCode(a))))
  · pexact (proofOf_eq_conj_inner L T)[NumShift.numCode(a)]
  · prw [evalVarZeroEquation, evalEquation, evalApplication, evalSymbol,
        eval_isProof_program_code L T, eval_language_code, eval_term_var_zero,
        eval_conclusion_program_code]

/-! ### Substitution in the body of the provability formula -/

open FOL.PRA.NumShift Substitution

theorem instantiate_conj_eval_num : ∀ L e y f z p, L = language →
    Formula.instantiate L (Formula.conj (Formula.equal L (Term.app L
      (Language.functionFamilyMember L 0 e) 1) (num y)) (Formula.equal L (Term.app L
      (Language.functionFamilyMember L 0 f) 1) (num z))) (num p) =
      Formula.conj (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 e)
        (num p)) (num y)) (Formula.equal L (Term.app L (Language.functionFamilyMember L 0 f) (num
        p)) (num z)) := by
  intro L e y f z p languageEq
  rw [languageEq]
  rw [instantiate_eq_substWithDepth, Formula.conj, Formula.neg, Formula.neg]
  rw [substWithDepth_imp, substWithDepth_imp, substWithDepth_equal, subst_eval,
    subst_var_zero_at_zero, Substitution.subst_num, substWithDepth_imp, substWithDepth_equal,
    subst_eval, subst_var_zero_at_zero, Substitution.subst_num, substWithDepth_falsum,
    Substitution.shift_num]
  rfl

derive_fol_pra instantiate_conj_eval_num as instantiate_conj_eval_num_inner

fol_theorem instantiate_conj_evalEquation : PRA ⊢ ∀ e y f z p,
    eval[Formula.instantiate.code](pair(${num language}, pair(
      eval[Formula.conj.code](pair(
        evalEquation(e, ${num 1}, numCode(y)),
        evalEquation(f, ${num 1}, numCode(z)))), numCode(p)))) =
    eval[Formula.conj.code](pair(
      evalEquation(e, numCode(p), numCode(y)),
      evalEquation(f, numCode(p), numCode(z)))) := by
  pintro e y f z p
  ptrans eval[Formula.instantiate.code](pair(${num language}, pair(
    eval[Formula.conj.code](pair(
      evalEquation(e, succ(zero), numCode(y)),
      evalEquation(f, succ(zero), numCode(z)))), numCode(p))))
  · prw [evalEquation, evalApplication, num_one]
  · papply instantiate_conj_eval_num_inner[${num language}, e, y, f, z, p]
    pexact Evaluation.symm _ _ eval_language_code

fol_theorem evalEquation_numCode_eq : PRA ⊢ ∀ k p y,
    evalEquation(k, numCode(p), numCode(y)) = evalEquationNum(k, p, y) := by
  pintro k p y
  prw [evalEquation, evalApplication, evalSymbol, evalEquationNum, evalSymbolAtLanguage,
    syntaxLanguage, eval_const_language]

fol_theorem instantiate_conj_isProof_conclusion (L T : Nat) : PRA ⊢ ∀ a p,
    eval[Formula.instantiate.code](pair(syntaxLanguage(), pair(
      eval[Formula.conj.code](pair(
        evalEquation(${num (FOL.isProof.code L T)}, ${num 1},
          NumShift.numCode(succ(zero))),
        evalEquation(${num FOL.Proof.conclusion.code}, ${num 1},
          NumShift.numCode(a)))), numCode(p)))) =
    eval[Formula.conj.code](pair(
      evalEquationNum(${num (FOL.isProof.code L T)}, p, succ(zero)),
      evalEquationNum(${num FOL.Proof.conclusion.code}, p, a))) := by
  pintro a p
  ptrans eval[Formula.instantiate.code](pair(${num language}, pair(
    eval[Formula.conj.code](pair(
      evalEquation(${num (FOL.isProof.code L T)}, ${num 1},
        NumShift.numCode(succ(zero))),
      evalEquation(${num FOL.Proof.conclusion.code}, ${num 1},
        NumShift.numCode(a)))), numCode(p))))
  · prw [syntaxLanguage, eval_const_language]
  · ptrans eval[Formula.conj.code](pair(
      evalEquation(${num (FOL.isProof.code L T)}, numCode(p), numCode(succ(zero))),
      evalEquation(${num FOL.Proof.conclusion.code}, numCode(p), numCode(a))))
    · pexact instantiate_conj_evalEquation[
        ${num (FOL.isProof.code L T)}, succ(zero), ${num FOL.Proof.conclusion.code}, a, p]
    · prw [evalEquation_numCode_eq]

end ProvabilityTransitivity

/-! ### Transitivity of provability -/

open ProvabilityTransitivity

theorem pr_pr (L T : Nat) :
    (PRA ⊢ ∀ a, (pr L T a) →
      (pr language isAxiom.code (eval[pr.code L T](eval[num.code](a))))) := by
  have proofTest := equation_complete (FOL.isProof.code L T)
  have reader := equation_complete FOL.Proof.conclusion.code
  have bodyEquation := proofOf_num_eq_conj L T
  pintro a h
  pcases h with ⟨p, accepted, conclusion⟩
  phave valid : (pr language isAxiom.code
      (evalEquationNum(${num (FOL.isProof.code L T)}, p, succ(zero))))
  · papply proofTest[p, succ(zero)]
    pexact accepted
  phave concluded : (pr language isAxiom.code
      (evalEquationNum(${num FOL.Proof.conclusion.code}, p, a)))
  · papply reader[p, a]
    pexact conclusion
  phave instanceEq :
      eval[Formula.instantiate.code](pair(syntaxLanguage(), pair(
        eval[proofOf.code L T](pair(eval[num.code](a), succ(zero))),
        NumShift.numCode(p)))) =
      eval[Formula.conj.code](pair(
        evalEquationNum(${num (FOL.isProof.code L T)}, p, succ(zero)),
        evalEquationNum(${num FOL.Proof.conclusion.code}, p, a)))
  · ptrans eval[Formula.instantiate.code](pair(syntaxLanguage(), pair(
      eval[Formula.conj.code](pair(
        evalEquation(${num (FOL.isProof.code L T)}, ${num 1},
          NumShift.numCode(succ(zero))),
        evalEquation(${num FOL.Proof.conclusion.code}, ${num 1},
          NumShift.numCode(a)))), NumShift.numCode(p))))
    · phave body : eval[proofOf.code L T](pair(eval[num.code](a), succ(zero))) =
        eval[Formula.conj.code](pair(
          evalEquation(${num (FOL.isProof.code L T)}, ${num 1},
            NumShift.numCode(succ(zero))),
          evalEquation(${num FOL.Proof.conclusion.code}, ${num 1},
            NumShift.numCode(a))))
      · pexact bodyEquation[a]
      prw [body]
    · pexact (instantiate_conj_isProof_conclusion L T)[a, p]
  phave sentenceProof : (pr language isAxiom.code
      (eval[Formula.ex.code](eval[proofOf.code L T](pair(eval[num.code](a), succ(zero))))))
  · papply (pr_ex_of_conj_equal_app language isAxiom.code)[
      evalSymbolAtLanguage(${num (FOL.isProof.code L T)}), NumShift.numCode(p),
      NumShift.numCode(succ(zero)), evalEquationNum(${num FOL.Proof.conclusion.code}, p, a),
      eval[proofOf.code L T](pair(eval[num.code](a), succ(zero)))]
    · pexact instanceEq
    · pexact valid
    · pexact concluded
  pcases sentenceProof with ⟨q, valid, concludes⟩
  pexists q
  pconstructor
  · pexact valid
  · prw [concludes, pr_num_eq_ex_proofOf_inner L T]

/-- **The second Hilbert–Bernays–Löb provability condition:** given a first-order theory `T` and a
formula `A` of language `L`, `PRA ⊢ pr_T(⌜A⌝) → pr_PRA(⌜pr_T(⌜A⌝)⌝)`. Here `T` is represented as a program
code of its axioms.

`pr_PRA` can be extended to `pr_U` for any recursive extension `U` of PRA. -/
theorem pr_pr_num (L T A : Nat) :
    (PRA ⊢ (pr L T ${num A}) → (pr language isAxiom.code ${num (pr L T (num A))})) := by
  have numValue := eval_num_of_evaluates num.code A (num A) (num.trace A) (num.computedBy A)
  have prValue := eval_num_of_evaluates (pr.code L T) (num A) (pr L T (num A))
    (pr.trace L T (num A)) (pr.computedBy L T (num A))
  pintro h
  phave result : (pr language isAxiom.code (eval[pr.code L T](eval[num.code](${num A}))))
  · papply (pr_pr L T)[${num A}]
    pexact h
  pcases result with ⟨q, accepted, conclusion⟩
  pexists q
  pconstructor
  · pexact accepted
  · prw [conclusion, numValue, prValue]

end

end FOL.PRA
