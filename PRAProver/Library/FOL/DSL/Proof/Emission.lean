module

public meta import PRAProver.Library.FOL.DSL.Proof.Derivation
public meta import PRAProver.Library.FOL.DSL.Reduction

/-!
# Emission of checked PRA proof data

`derivationProof` constructs an ordinary PRA proof of `FOL.Provable`, using the common Hilbert
constructor lemmas. Derivations used more than once are shared through local proof definitions.
`emitDerivation` checks and publishes a closed result for command-level callers.
-/

public meta section

namespace PRAProver.Library.FOL.DSL

open PRAProver.Library.Tactic.Construction

open Lean hiding Term

open Lean.Elab.Command

open PRAProver.Core

def SchemaArg.variables : SchemaArg → List Name
  | .formula A bs => A.variables.filter (!bs.contains ·)
  | .term t => t.variables
  | .tuple ts => ts.flatMap TermView.variables
  | .number _ | .member .. => []

def SchemaArg.encode (L : Term) (bound fvars : List Name) : SchemaArg → CommandElabM Term
  | .formula A bs => A.encode L (bs ++ bound) fvars
  | .term t => t.encode L bound fvars
  | .tuple ts => return tupleCode (← ts.mapM (TermView.encode L bound fvars))
  | .number n => pure (numeral n)
  | .member b k isRelation =>
    let member := if isRelation then `FOL.Language.relationFamilyMember
      else `FOL.Language.functionFamilyMember
    pure (applyDefinition member [L, numeral b, k])

private partial def schedule (nodes : Array Node) (root : Nat) (positions : List Name) :
    StateM (Array (Node × List Name) × Std.HashMap (Nat × List Name) Nat) Nat := do
  let key := (root, positions)
  if let some i := (← get).2[key]? then return i
  let node := nodes[root]!
  let reason : Reason ← match node.reason with
    | .mp i j => do
      let a ← schedule nodes i positions
      let b ← schedule nodes j positions
      pure (.mp a b)
    | .generalization x i => do
      let a ← schedule nodes i (x :: positions)
      pure (.generalization x a)
    | reason => pure reason
  let i := (← get).1.size
  modify fun (scheduled, cache) =>
    (scheduled.push ({ node with reason }, positions), cache.insert key i)
  return i

/-- Order reachable steps after their dependencies, tracking object variable positions. -/
def scheduleDerivation (graph : Derivation) (root : Nat) (free : List Name) :
    Array (Node × List Name) :=
  ((schedule graph.nodes root free).run (#[], {})).2.1

/-- The ordinary PRA statement that the encoded formula has a checked proof. -/
def provable (L theory A : Term) : Predicate :=
  .app (.definition `FOL.Provable [L, theory] []) A

/-- Transport a derivation along a calculated equality of formula codes. -/
def transportProvable (L theory source target : Term) (proof : Proof) : CommandElabM Proof := do
  if source == target then return proof
  let equality ← calculateClosedEquality source target
  let motive := Predicate.lam `A (provable L.shift theory.shift (.bvar 0))
  return .impElim (.impElim (.forallElim (.forallElim (.eqSubst motive) source) target)
    equality) proof

def shiftHypotheses (count : Nat) (p : Proof) (depth : Nat := 0) : Proof :=
  if count == 0 then p else
  mapProof (fun _ t => t) (fun _ p => p)
    (fun _ d i => .hyp (if i < d then i else i + count)) 0 depth p

/-- Build a PRA proof in the caller's context, sharing intermediate derivations with proof lets.
The supplied proofs may refer to the caller's PRA hypotheses, innermost first. -/
def derivationProof (T : TheoryInfo) (graph : Derivation) (root : Nat)
    (expected : FormulaView) (freeVariables : List Name)
    (parameters : Option (Term × Term) := none) :
    CommandElabM Proof := do
  let (L, theory) := parameters.getD
    (languageTerm T.language, applyDefinition (T.name ++ `isAxiom))
  let scheduled := scheduleDerivation graph root freeVariables
  let uses := scheduled.foldl (fun counts (node, _) => match node.reason with
    | .mp i j => (counts.modify i (· + 1)).modify j (· + 1)
    | .generalization _ i => counts.modify i (· + 1)
    | _ => counts) (Array.replicate scheduled.size 0)
  let mut formulas : Array Term := #[]
  let mut references : Array (Proof × Nat) := #[]
  let mut sharedFormulas : Array Term := #[]
  let mut proofs : Array Proof := #[]
  for (node, localPositions) in scheduled do
    let A ← node.formula.encode L [] localPositions
    let n := proofs.size
    let reference (i : Nat) :=
      shiftHypotheses (n - references[i]!.2) references[i]!.1
    let proof ← match node.reason with
      | .proven proof => do
        if localPositions != freeVariables then
          let original ← node.formula.encode L [] freeVariables
          unless original == A do
            throwError "a supplied object proof needs an explicit change of variable positions"
        pure (Proof.ascribe (provable L theory A) (shiftHypotheses n proof))
      | .lemma name arguments => do
        let arguments ← arguments.mapM (FormulaView.encode L [] localPositions)
        pure (Proof.ascribe (provable L theory A) (applyTheorem name [] (L :: theory :: arguments)))
      | .mp i j => do
        let imp := applyDefinition `FOL.Formula.imp [formulas[j]!, A]
        let transported ← transportProvable L theory formulas[i]! imp (reference i)
        pure (applyTheorem `FOL.Provable.mp [formulas[j]!, A] [L, theory]
          [transported, reference j])
      | .generalization _ i => do
        let quantified := applyDefinition `FOL.Formula.all [formulas[i]!]
        let proof := applyTheorem `FOL.Provable.gen [formulas[i]!] [L, theory] [reference i]
        transportProvable L theory quantified A proof
      | .hypothesis h => throwError "undischarged first-order hypothesis `{h}`"
      | reason => do
        match reason with
          | .logical tag args => do
            let args ← args.mapM (SchemaArg.encode L [] localPositions)
            let a := args[0]!
            let b := args[1]!
            let c := args[2]!
            let imp (a b : Term) := applyDefinition `FOL.Formula.imp [a, b]
            let all (a : Term) := applyDefinition `FOL.Formula.all [a]
            let eq (a b : Term) := applyDefinition `FOL.Formula.equal [L, a, b]
            let neg (a : Term) := applyDefinition `FOL.Formula.neg [a]
            let (schema, lemma, params) ← match tag with
              | 0 => pure (imp a (imp b a), `FOL.Provable.implication, [L, a, b])
              | 1 => pure (imp (imp a (imp b c)) (imp (imp a b) (imp a c)),
                  `FOL.Provable.implicationDistribution, [L, a, b, c])
              | 2 => pure (imp (imp (neg a) (neg b)) (imp b a),
                  `FOL.Provable.contraposition, [L, a, b])
              | 3 => pure (imp (all a) (applyDefinition `FOL.Formula.instantiate [L, a, b]),
                  `FOL.Provable.instantiate, [L, a, b])
              | 4 => pure (imp (all (imp (applyDefinition `FOL.Formula.shift [L, a]) b))
                  (imp a (all b)), `FOL.Provable.quantifierImplication, [L, a, b])
              | 6 => pure (eq a a, `FOL.Provable.reflexivity, [L, a])
              | 7 => pure (imp (eq a b) (eq b a), `FOL.Provable.symmetry, [L, a, b])
              | 8 => pure (imp (eq a b) (imp (eq b c) (eq a c)),
                  `FOL.Provable.transitivity, [L, a, b, c])
              | 9 => pure (applyDefinition `FOL.Formula.equalPremises
                  [L, applyDefinition `FOL.Language.functionSymbolArity [L, a], b, c,
                   eq (applyDefinition `FOL.Term.app [L, a, b])
                      (applyDefinition `FOL.Term.app [L, a, c])],
                  `FOL.Provable.functionCongruence, [L, a, b, c])
              | 10 => pure (applyDefinition `FOL.Formula.equalPremises
                  [L, applyDefinition `FOL.Language.relationSymbolArity [L, a], b, c,
                   imp (applyDefinition `FOL.Formula.rel [L, a, b])
                       (applyDefinition `FOL.Formula.rel [L, a, c])],
                  `FOL.Provable.relationCongruence, [L, a, b, c])
              | _ => throwError "unknown logical axiom family"
            let conditions ← if tag == 9 || tag == 10 then do
                pure [← (symbolProof L a (tag == 10)).run' {}]
              else pure []
            let proof := applyTheorem lemma [] (L :: theory :: params.tail) conditions
            transportProvable L theory schema A proof
          | _ => throwError "expected a logical axiom"
    formulas := formulas.push A
    if uses[references.size]! > 1 then
      sharedFormulas := sharedFormulas.push A
      proofs := proofs.push proof
      references := references.push (.hyp 0, proofs.size)
    else
      references := references.push (proof, proofs.size)
  let result ← expected.encode L [] freeVariables
  let (last, count) := references.back!
  let last := shiftHypotheses (proofs.size - count) last
  let mut proof ← transportProvable L theory formulas.back! result last
  for i in (List.range proofs.size).reverse do
    proof := .letE (Name.mkSimple s!"folStep{i}")
      (provable L theory sharedFormulas[i]!) proofs[i]! proof
  return proof

/-- Publish a closed derivation constructed by a command or an isolated checker test. -/
def emitDerivation (name : Name) (T : TheoryInfo) (graph : Derivation) (root : Nat)
    (source : Syntax) (expected : FormulaView) (freeVariables : List Name) : CommandElabM Unit := do
  let L := languageTerm T.language
  let A ← expected.encode L [] freeVariables
  let proof ← derivationProof T graph root expected freeVariables
  publishChecked (.theoremE ⟨name, [], provable L (applyDefinition (T.name ++ `isAxiom)) A,
    proof⟩) source

end PRAProver.Library.FOL.DSL
