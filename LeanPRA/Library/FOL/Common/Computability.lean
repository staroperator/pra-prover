module

public import LeanPRA.Library.Computability.Derive.Computability
public import LeanPRA.Library.FOL.Common.Proof

/-!
# Shared programs for first-order proof checkers

The derivations here give numerical programs, computation trees, and correctness proofs that
checkers for different theories can import.

- `FOL.isLogicalAxiom` tests for instances of the logical axiom schemas.
- `FOL.Formula.successorInstance` supplies the substitution used in induction axioms.
- `FOL.Formula.isQuantifierFree` checks the restriction on a quantifier-free induction schema.
- `FOL.Proof.rule`, `FOL.Proof.conclusion`, and `FOL.Proof.premises` read proof tree nodes.
- `FOL.isProof.code L e` fixes the language and axiom test of a unary proof checker.
- `FOL.isProof.computedBy` certifies its computation trees.
-/

namespace FOL

pra

derive_primrec Language.make Language.constants Language.functions Language.relations
  Language.constantFamilyCount Language.functionFamilies Language.relationFamilies
  Language.functionCount Language.relationCount Language.functionFamilyCount
  Language.relationFamilyCount Language.functionArity Language.functionFamilyArity
  Language.functionFamilyMember Language.relationFamilyMember Language.functionSymbolArity
  Language.relationSymbolArity

derive_primrec Term.const Term.var Term.app Term.head Term.arg Term.rec Term.subst
  Term.shift Term.instantiateAt

derive_primrec Formula.falsum Formula.equal Formula.rel Formula.imp Formula.all Formula.neg
  Formula.conj Formula.ex Formula.head Formula.arg Formula.relationIndex Formula.equalPremises
  Formula.recWithDepth Formula.rec Formula.isQuantifierFree
  Formula.substWithDepth Formula.instantiateAt Formula.instantiate Formula.shift
  Formula.successorInstance

derive_primrec consSubst shiftSubst liftSubst Formula.subst

derive_primrec LogicalAxiom.isImplication LogicalAxiom.isImplicationDistribution
  LogicalAxiom.isContraposition LogicalAxiom.isQuantifierImplication LogicalAxiom.isReflexivity
  LogicalAxiom.isSymmetry LogicalAxiom.isTransitivity LogicalAxiom.isInstantiation
  LogicalAxiom.isFunctionCongruence LogicalAxiom.isRelationCongruence isLogicalAxiom

derive_primrec Proof.axiom Proof.mp Proof.rule Proof.conclusion Proof.premises Proof.rec isProof

end

end FOL
