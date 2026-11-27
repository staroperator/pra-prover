module

public import PRAProver.Library.Computability.Derive.Command
public import PRAProver.Library.Nat.Tuple

/-!
# Derivations for numerical operations

These commands publish programs, traces, and correctness proofs for numerical operations.
-/

pra

derive_primrec add pred sub mul iter

derive_primrec ite isZero isPos bnot band bor leb ltb eqb

derive_primrec allBelow anyBelow findBelow

derive_primrec triangular diagonal pair unpairLeft unpairRight

derive_primrec div mod

derive_primrec Sequence.nil Sequence.cons Sequence.head Sequence.tail Sequence.drop Sequence.get
  Sequence.length Sequence.rget Sequence.generate covrec

derive_primrec Tuple.get Tuple.map

derive_primrec (fun x => eqb (unpairLeft x) (unpairRight x)) as Primrec.eqb_pair

end
