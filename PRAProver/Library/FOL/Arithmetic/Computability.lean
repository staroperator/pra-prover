module

public import PRAProver.Library.FOL.Arithmetic.Defs
public import PRAProver.Library.FOL.Common.Computability

/-!
# Primitive-recursive axiom membership for arithmetic

`Q.isAxiom.primrec` and `PA.isAxiom.primrec` give primitive-recursive programs for the
axiom tests, including PA's induction schema. The reflection command constructs numerical
programs, computation-tree builders, and correctness proofs checked in PRA. Their names are
`Q.isAxiom.code`, `Q.isAxiom.trace`, and `Q.isAxiom.computedBy`, and likewise for PA. Both checkers
use the common first-order programs for the operations they share.
-/

namespace FOL

pra

derive_primrec Arithmetic.language Q.succ_ne_zero.formula Q.succ_ne_zero.isAxiom

derive_primrec Q.succ_injective.formula Q.succ_injective.isAxiom Q.zero_or_succ.formula

derive_primrec Q.zero_or_succ.isAxiom Q.add_zero.formula Q.add_zero.isAxiom Q.add_succ.formula

derive_primrec Q.add_succ.isAxiom Q.mul_zero.formula Q.mul_zero.isAxiom Q.mul_succ.formula

derive_primrec Q.mul_succ.isAxiom

derive_primrec Q.isAxiom

derive_primrec PA.induction.formula PA.induction.isInstance PA.induction.isAxiom

derive_primrec PA.isAxiom

end

end FOL
