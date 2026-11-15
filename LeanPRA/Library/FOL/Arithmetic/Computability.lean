module

public import LeanPRA.Library.FOL.Arithmetic.Defs
public meta import LeanPRA.Library.Computability.Tactic

/-!
# Primitive-recursive axiom membership for arithmetic

`Q.isAxiom_primrec` and `PA.isAxiom_primrec` give primitive-recursive programs for the
axiom tests, including PA's induction schema. The reflection command constructs numerical
programs, computation-tree builders, and correctness proofs checked in PRA.
-/

namespace FOL

pra

derive_primrec Q.isAxiom as Q.isAxiom_primrec

derive_primrec PA.isAxiom as PA.isAxiom_primrec

end

end FOL
