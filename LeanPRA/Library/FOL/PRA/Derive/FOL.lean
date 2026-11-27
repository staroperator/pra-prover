module

public import LeanPRA.Library.FOL.PRA.Derive.Nat

/-!
# First-order syntax and proof verification inside PRA

These translations let first-order PRA reason about the encoded syntax of arbitrary
first-order languages. The provability proofs use them to construct terms and formulas
and verify logical axiom instances.
-/

pra

namespace FOL.PRA

derive_fol_pra FOL.isLogicalAxiom_of_instantiation as instantiation_accepted

derive_fol_pra FOL.Formula.right_lt_imp as formula_right_lt_imp

derive_fol_pra FOL.Formula.le_equal_left as formula_le_equal_left

derive_fol_pra FOL.Term.args_lt_app as term_args_lt_app

end FOL.PRA

namespace FOL.PRA.NumShift

derive_fol_pra FOL.Term.head_app as term_head_app

derive_fol_pra FOL.Term.arg_app as term_arg_app

end FOL.PRA.NumShift

namespace FOL.PRA

derive_fol_pra FOL.isLogicalAxiom_of_implication as implication_accepted

derive_fol_pra FOL.isLogicalAxiom_of_implicationDistribution as distribution_accepted

derive_fol_pra FOL.Formula.left_lt_imp as formula_left_lt_imp

end FOL.PRA

namespace FOL.PRA.EqualityRules

derive_fol_pra FOL.isLogicalAxiom_of_functionCongruence as function_congruence_accepted

derive_fol_pra FOL.Formula.equalPremises_one as equalPremises_one_inner

derive_fol_pra FOL.Formula.equalPremises_two as equalPremises_two_inner

end FOL.PRA.EqualityRules

namespace FOL.PRA.Pair

derive_fol_pra FOL.Formula.body_lt_all as body_lt_all_inner

end FOL.PRA.Pair

end
