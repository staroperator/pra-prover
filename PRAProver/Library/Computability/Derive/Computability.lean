module

public import PRAProver.Library.Computability.Derive.Nat

/-!
# Derivations for computability

These commands publish codes, traces, and correctness proofs for operations on program
codes and computation trees.
-/

pra

/-! ## Program code operations -/

derive_primrec Primrec.Code.zero Primrec.Code.succ Primrec.Code.left Primrec.Code.right
  Primrec.Code.binary Primrec.Code.pair Primrec.Code.comp Primrec.Code.rec Primrec.Code.const
  Primrec.Code.id Primrec.Code.tag Primrec.Code.args

/-! ## Codes for computing numerical program indices -/

derive_primrec add.code pred.code sub.code mul.code iter.internal.code

derive_primrec ite.code isZero.code isPos.code bnot.code band.code bor.code leb.code ltb.code
  eqb.code

derive_primrec allBelow.internal.code anyBelow.internal.code findBelow.internal.code

derive_primrec triangular.code diagonal.code pair.code unpairLeft.code unpairRight.code

derive_primrec div.code mod.code

derive_primrec Sequence.nil.code Sequence.cons.code Sequence.head.code Sequence.tail.code
  Sequence.drop.code Sequence.get.code Sequence.length.code Sequence.rget.code
  Sequence.generate.internal.code covrec.internal.code

derive_primrec Tuple.get.code Tuple.map.internal.code

/-! ## Computation tree operations -/

derive_primrec Primrec.Computation.program Primrec.Computation.input Primrec.Computation.output
  Primrec.Computation.childLeft Primrec.Computation.childRight Primrec.Computation.checkNode
  Primrec.Computation.isValid

end
