module

public import LeanPRA.Library.FOL.PRA.Provability.D1

/-!
# Computing the provability formula

The program for `proofOf` constructs the formula checked by the provability proof.
The derivations first compute the program indices used by the checker and conclusion reader.
-/

pra

namespace FOL.PRA

derive_primrec Primrec.Code.fixLeft Primrec.Code.onRight

derive_primrec Language.constants.code Language.functions.code Language.relations.code
  Language.constantFamilyCount.code Language.functionFamilies.code Language.relationFamilies.code
  Language.functionCount.code Language.relationCount.code Language.functionFamilyCount.code
  Language.relationFamilyCount.code Language.functionFamilyMember.code
  Language.relationFamilyMember.code Language.functionSymbolArity.code
  Language.relationSymbolArity.code

derive_primrec Term.const.code Term.var.code Term.app.code Term.head.code Term.arg.code
  Term.rec.internal.code Term.subst.internal.code Term.shift.code
  Term.instantiateAt.code

derive_primrec Formula.falsum.code Formula.equal.code Formula.rel.code Formula.imp.code
  Formula.all.code Formula.neg.code Formula.head.code Formula.arg.code Formula.relationIndex.code
  Formula.equalPremises.code
  Formula.recWithDepth.internal.code Formula.substWithDepth.internal.code Formula.instantiateAt.code
  Formula.instantiate.code Formula.shift.code

derive_primrec LogicalAxiom.isImplication.code LogicalAxiom.isImplicationDistribution.code
  LogicalAxiom.isContraposition.code LogicalAxiom.isQuantifierImplication.code
  LogicalAxiom.isReflexivity.code LogicalAxiom.isSymmetry.code LogicalAxiom.isTransitivity.code
  LogicalAxiom.isInstantiation.code LogicalAxiom.isFunctionCongruence.code
  LogicalAxiom.isRelationCongruence.code isLogicalAxiom.code

derive_primrec Proof.rule.code Proof.conclusion.code Proof.premises.code Proof.rec.internal.code
  isProof.internal.code

derive_primrec FOL.isProof.code proofOf pr

end FOL.PRA

end
