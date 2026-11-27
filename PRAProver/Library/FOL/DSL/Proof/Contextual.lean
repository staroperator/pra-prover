module

public import PRAProver.Library.FOL.Common.Sequent
public meta import PRAProver.Library.FOL.DSL.Proof.Emission
public meta import PRAProver.Library.Tactic.Marker

/-!
# Emission of proofs with local assumptions

A goal with local assumptions is `Sequent L T Γ A`, where `Γ` is a sequence of
formula codes with the newest assumption first. Each assumption is written as a name marker
around its code, and the marker's name is the assumption's name.

- `LocalContext` stores the assumption list as written in the goal together with the decoded
  names and formulas of its entries.
- `provabilityParts?` reads either spelling of a provability statement.
- `provableUnder` forms the statement of a goal with a list of assumptions; `asSequent` and
  `ofSequent` handle the empty assumption list when applying the `Sequent` rules.
- `assumptionProof` and `contextProjection` prove an assumption from the list.
- `shiftedListEquality` proves that mapping `Formula.shift` over an explicit list gives the
  list of shifted entries.
- `contextualProof` translates a derivation under a fixed assumption list using the `Sequent`
  rules. Intermediate proofs used more than once are shared through local proof definitions.
-/

public meta section

namespace PRAProver.Library.FOL.DSL

open Lean Elab Command PRAProver.Core PRAProver.Surface
open PRAProver.Library.Tactic.Construction

/-- The empty list of assumptions. -/
def emptyList : Core.Term := applyDefinition `Sequence.nil

/-- The list `rest` with the newer assumption `a` in front. -/
def consList (a rest : Core.Term) : Core.Term := applyDefinition `Sequence.cons [a, rest]

/-- The local assumptions of a goal: the list as the goal states it, and the name and formula
of each entry with the newest first. -/
structure LocalContext where
  code : Core.Term := emptyList
  entries : List (Name × FormulaView) := []
  deriving Inhabited

/-- The entries of a written-out list as they stand, and the code that follows them. -/
partial def listEntries (Γ : Core.Term) : List Core.Term × Core.Term :=
  match getAppFnArgs Γ with
  | (.definition `Sequence.cons [], [a, rest]) =>
    let (entries, tail) := listEntries rest
    (a :: entries, tail)
  | _ => ([], Γ)

/-- The fold step `fun r B => Formula.imp B r`, with the accumulated conclusion first. -/
def implicationStep : Core.Term :=
  .lam `r (.lam `B (applyDefinition `FOL.Formula.imp [.bvar 0, .bvar 1]))

/-- Fold the assumptions into implications, with the newest next to `A`. -/
def foldImplications (Γ A : Core.Term) : Core.Term :=
  applyDefinition `Sequence.fold [Γ, A] [implicationStep]

/-- The statement `Sequent L T Γ A` of provability under an explicit assumption list. -/
def sequent (L theory Γ A : Core.Term) : Predicate :=
  .app (.app (.definition `FOL.Sequent [L, theory] []) Γ) A

/-- Read the language, theory, conclusion, and optional assumption list of a provability statement.
Both `Sequent` and the expanded `Provable` form are accepted. `depth` bounds the beta reduction
that exposes the statement. -/
def provabilityParts? (depth : Nat) (type : Predicate) :
    Option (Core.Term × Core.Term × Core.Term × Option Core.Term) :=
  match Core.betaReducePredicate depth type with
  | .app (.app (.definition `FOL.Sequent [L, theory] []) Γ) A =>
    some (L, theory, A, some Γ)
  | .app (.definition `FOL.Provable [L, theory] []) code =>
    match getAppFnArgs code with
    | (.definition `Sequence.fold
        [.lam _ (.lam _ (.app (.app (.definition `FOL.Formula.imp []) (.bvar 0)) (.bvar 1)))],
        [Γ, A]) => some (L, theory, A, some Γ)
    | _ => some (L, theory, code, none)
  | _ => none

/-- The statement that `A` is provable from the assumptions `Γ`. An empty list is written as
`Provable L T A`; a nonempty list is written as `Sequent L T Γ A`. -/
def provableUnder (L theory Γ A : Core.Term) : Predicate :=
  if Γ == emptyList then provable L theory A else sequent L theory Γ A

/-- Transport a proof of `Γ ⊢ source` to `Γ ⊢ target` along the proof `equality` of
`source = target`. -/
def transportAlong (L theory Γ source target : Core.Term) (equality proof : Core.Proof) :
    Core.Proof :=
  let motive := Predicate.lam `A (provableUnder L.shift theory.shift Γ.shift (.bvar 0))
  .impElim (.impElim (.forallElim (.forallElim (.eqSubst motive) source) target) equality) proof

/-- Transport a proof of `Γ ⊢ source` to `Γ ⊢ target` along a calculated equality. -/
def transportUnder (L theory Γ source target : Core.Term) (proof : Core.Proof) :
    CommandElabM Core.Proof := do
  if source == target then return proof
  return transportAlong L theory Γ source target (← calculateClosedEquality source target) proof

/-- Present a proof of `Γ ⊢ A` as `Sequent L T Γ A`. With an empty list the given proof states
`Provable L T A`, and `Sequence.fold_nil` supplies the conversion. -/
def asSequent (L theory Γ A : Core.Term) (proof : Core.Proof) : Core.Proof :=
  if Γ == emptyList then
    let motive := Predicate.lam `A (provable L.shift theory.shift (.bvar 0))
    let equality := applyTheorem `Sequence.fold_nil [A] [implicationStep]
    .impElim (.impElim (.forallElim (.forallElim (.eqSubst motive) A) (foldImplications Γ A))
      (mkEqSymm (foldImplications Γ A) A equality)) proof
  else proof

/-- Present a proof of `Sequent L T Γ A` in the form used by `provableUnder`, writing the
empty-context case as `Provable L T A`. -/
def ofSequent (L theory Γ A : Core.Term) (proof : Core.Proof) : Core.Proof :=
  if Γ == emptyList then
    let motive := Predicate.lam `A (provable L.shift theory.shift (.bvar 0))
    .impElim (.impElim (.forallElim (.forallElim (.eqSubst motive) (foldImplications Γ A)) A)
      (applyTheorem `Sequence.fold_nil [A] [implicationStep])) proof
  else proof

/-- Replace the list `source` of a proof of `source ⊢ A` by the equal list `target`. -/
def transportList (L theory source target A : Core.Term)
    (equality proof : Core.Proof) : Core.Proof :=
  let motive := Predicate.lam `G (sequent L.shift theory.shift (.bvar 0) A.shift)
  .impElim (.impElim (.forallElim (.forallElim (.eqSubst motive) source) target) equality) proof

/-- The assumption at position `index` of the written-out list `Γ`, as it stands there, with a
proof that it follows from `Γ`. -/
def assumptionProof (L theory Γ : Core.Term) (index : Nat) : Option (Core.Term × Core.Proof) :=
  let (entries, tail) := listEntries Γ
  let rest (k : Nat) : Core.Term := (entries.drop k).foldr consList tail
  entries[index]?.map fun target =>
    let head := applyTheorem `FOL.Sequent.head [rest (index + 1), target] [L, theory]
    (target, (List.range index).reverse.foldl (fun proof k =>
      applyTheorem `FOL.Sequent.weaken [rest (k + 1), entries[k]!, target] [L, theory]
        [proof]) head)

/-- Prove the formula `target` from the assumption of the list that states it. -/
def contextProjection (L theory : Core.Term) (context : LocalContext) (target : FormulaView)
    (free : List Name) : CommandElabM (Option Core.Proof) := do
  let some index := context.entries.findIdx? (fun (_, a) => a.equiv target) | return none
  let some (entry, proof) := assumptionProof L theory context.code index | return none
  some <$> transportUnder L theory context.code entry (← target.encode L [] free) proof

/-- The list `Sequence.map (Formula.shift L) Γ`. -/
def shiftedList (L Γ : Core.Term) : Core.Term :=
  applyDefinition `Sequence.map [Γ] [.app (.definition `FOL.Formula.shift []) L]

/-- A proof that `shiftedList L Γ` equals `shifted`, for written-out lists of the same length
whose entries correspond by `Formula.shift L`. -/
partial def shiftedListEquality (L Γ shifted : Core.Term) : CommandElabM Core.Proof := do
  let f := Core.Term.app (.definition `FOL.Formula.shift []) L
  match getAppFnArgs Γ, getAppFnArgs shifted with
  | (.definition `Sequence.cons [], [a, rest]), (.definition `Sequence.cons [], [b, rest']) =>
    let head ← calculateClosedEquality (.app f a) b
    let tail ← shiftedListEquality L rest rest'
    let middle := consList (.app f a) (shiftedList L rest)
    return mkEqTrans (shiftedList L Γ) middle shifted
      (applyTheorem `Sequence.map_cons [a, rest] [f])
      (applyTheorem `eq_congr₂ [.app f a, shiftedList L rest, b, rest']
        [.definition `Sequence.cons []] [head, tail])
  | _, _ =>
    unless Γ == emptyList && shifted == emptyList do
      throwError "the local assumptions cannot be shifted: the list is not written out"
    return applyTheorem `Sequence.map_nil [] [f]

/-- Emit a checked PRA proof under a list of local assumptions. -/
partial def contextualProof (T : TheoryInfo) (graph : Derivation) (root : Nat)
    (expected : FormulaView) (context : LocalContext) (free : List Name) :
    CommandElabM Core.Proof := do
  let L := languageTerm T.language
  let theory := applyDefinition (T.name ++ `isAxiom)
  let scheduled := scheduleDerivation graph root free
  let uses := scheduled.foldl (fun counts (node, _) => match node.reason with
    | .mp i j => (counts.modify i (· + 1)).modify j (· + 1)
    | .generalization _ i => counts.modify i (· + 1)
    | _ => counts) (Array.replicate scheduled.size 0)
  -- The goal's list, or its entries written out again beneath binders of the derivation.
  let listAt (positions : List Name) : CommandElabM Core.Term := do
    if positions == free then return context.code
    unless (listEntries context.code).2 == emptyList do
      throwError "the local assumptions cannot be shifted: the list is not written out"
    context.entries.foldrM (fun (_, a) rest => do
      return consList (← a.encode L [] positions) rest) emptyList
  let mut formulas : Array (Core.Term × Core.Term) := #[]
  let mut references : Array (Core.Proof × Nat) := #[]
  let mut sharedFormulas : Array (Core.Term × Core.Term) := #[]
  let mut proofs : Array Core.Proof := #[]
  for (node, positions) in scheduled do
    let G ← listAt positions
    let A ← node.formula.encode L [] positions
    let imp (a b : Core.Term) := applyDefinition `FOL.Formula.imp [a, b]
    let n := proofs.size
    let reference (i : Nat) :=
      shiftHypotheses (n - references[i]!.2) references[i]!.1
    let proof ← match node.reason with
    | .localProof p => do
      unless positions == free do
        throwError "a local object proof needs an explicit change of variable positions"
      pure (shiftHypotheses n p)
    | .mp p q => do
      let B := formulas[q]!.2
      let hp ← transportUnder L theory G formulas[p]!.2 (imp B A) (reference p)
      pure (applyTheorem `FOL.Sequent.mp [G, B, A] [L, theory] [hp, reference q])
    | .generalization x p => do
      if context.entries.any (fun (_, a) => a.variables.contains x) then
        throwError "cannot generalize a position occurring in the local context"
      let B := formulas[p]!.2
      let inner := formulas[p]!.1
      let mapped := shiftedList L G
      let equality ← shiftedListEquality L G inner
      let hp := transportList L theory inner mapped B (mkEqSymm mapped inner equality)
        (reference p)
      let proof := applyTheorem `FOL.Sequent.all_intro [G, B] [L, theory] [hp]
      transportUnder L theory G (applyDefinition `FOL.Formula.all [B]) A proof
    | .hypothesis h => throwError "undischarged first-order hypothesis `{h}`"
    | _ => do
      let leaf := { graph with nodes := #[node] }
      let p ← derivationProof T leaf 0 node.formula positions
      pure (applyTheorem `FOL.Sequent.lift [G, A] [L, theory] [shiftHypotheses n p])
    formulas := formulas.push (G, A)
    if uses[references.size]! > 1 then
      sharedFormulas := sharedFormulas.push (G, A)
      proofs := proofs.push proof
      references := references.push (.hyp 0, proofs.size)
    else
      references := references.push (proof, proofs.size)
  let G := context.code
  let A ← expected.encode L [] free
  let (last, count) := references.back!
  let last := shiftHypotheses (proofs.size - count) last
  let mut proof ← transportUnder L theory G formulas.back!.2 A last
  for i in (List.range proofs.size).reverse do
    let (C, B) := sharedFormulas[i]!
    proof := .letE (Name.mkSimple s!"folContextStep{i}")
      (sequent L theory C B) proofs[i]! proof
  return proof

end PRAProver.Library.FOL.DSL
