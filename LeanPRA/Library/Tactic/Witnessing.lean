module

public meta import LeanPRA.Library.Tactic.Construction

/-!
# Compilation of numerical witnesses

`compileWitness` turns an existential theorem into a numerical program and a checked specification.
`compileProof` performs the same construction in a local proof context. Recursive proof tactics use
the resulting programs as primitive-recursion branches.

The compiler follows constructive introductions, applications, and equality transport. Shared
subproofs become checked numerical definitions. The resulting specification passes through the
ordinary PRA checker before it can be used by another declaration. Generated functions capture
only the local variables used by their bodies; their certificates include the proof premises.

A theorem used inside a compiled proof is compiled once and then reused when each premise is
quantifier-free or an existence statement with a quantifier-free body. An existence premise
`∃ u, Q u` is opened: the program receives `u` as a further argument, and its specification
assumes `Q u`. For example, `(∃ u, Q u) → ∃ v, R v` gives a program `f` and the specification
`∀ u, Q u → R (f u)`. At each use, the number is first computed from the proof supplied for that
premise. Theorems with other premises are replaced by their proofs at each use.
-/

public meta section

namespace LeanPRA.Library.Tactic.Witnessing

open Lean Elab Command LeanPRA.Core
open LeanPRA.Library.Tactic.Construction

private def substitute (s : Core.Subst) : Core.Proof → Core.Proof :=
  mapProof (fun d t => t.subst (Core.Subst.lift d s))
    (fun d a => a.subst (Core.Subst.lift d s)) (fun _ _ i => .hyp i) 0 0

private def substituteHypotheses (s : Nat → Core.Proof) : Core.Proof → Core.Proof :=
  mapProof (fun _ t => t) (fun _ a => a)
    (fun nd hd i => if i < hd then .hyp i else shiftProof (s (i - hd)) nd hd) 0 0

private def substituteHypothesis (p q : Core.Proof) : Core.Proof :=
  substituteHypotheses (fun | 0 => q | i + 1 => .hyp i) p

private def instantiate (fs : List Core.Term) (ps : List Core.Predicate) :
    Core.Proof → Core.Proof :=
  mapProof (fun d t => t.instantiate fs d) (fun d a => a.instantiate fs ps d)
    (fun _ _ i => .hyp i) 0 0

private def checked (result : Core.CheckResult α) : CommandElabM α :=
  match result with
  | .ok a => pure a
  | .error e => throwError "witness extraction: {e.message}"

private def environment : CommandElabM Core.Environment :=
  return LeanPRA.Surface.CoreEnvironment.getState (← getEnv)

private def formulaHead (a : Core.Predicate) : CommandElabM Core.Predicate := do
  checked (Core.whnfPredicate 1024 (← environment) a)

private structure WitnessInfo where
  source : Name
  code : Name
  /-- Whether the existence premises of `source` are arguments of `code`. -/
  opened : Bool := false
  deriving Inhabited

private initialize witnesses : SimplePersistentEnvExtension WitnessInfo (Array WitnessInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

private def eliminateExists (motive target : Core.Predicate) (value body : Core.Proof) :
    Core.Proof :=
  let premise := Core.Predicate.app motive.shift (.bvar 0)
  .impElim (.impElim (.existsElim motive target) value)
    (.forallIntro `w (.lam `w (.imp premise target.shift)) (.impIntro `h premise body))

/-- Prove a theorem of `type` from its compiled program `code` and checked specification `proof`.
With `opened`, each existence premise supplies its number to `code` and to `proof`. -/
private partial def reconstruct (opened : Bool) (type : Core.Predicate) (code : Core.Term)
    (proof : Core.Proof) : CommandElabM Core.Proof := do
  match ← formulaHead type with
  | .all motive =>
    let body ← reconstruct opened (.app motive.shift (.bvar 0)) (.app code.shift (.bvar 0))
      (.forallElim (shiftProof proof 1 0) (.bvar 0))
    return .forallIntro `x motive body
  | .imp a b =>
    if opened then
      if let .ex motive ← formulaHead a then
        -- Inside the branch, `w` is the premise's number and hypothesis `0` its property.
        let body ← reconstruct opened b.shift (.app code.shift (.bvar 0))
          (.impElim (.forallElim (shiftProof proof 1 2) (.bvar 0)) (.hyp 0))
        return .impIntro `h a (eliminateExists motive b (.hyp 0) body)
    let body ← reconstruct opened b code (.impElim (shiftProof proof 0 1) (.hyp 0))
    return .impIntro `h a body
  | .ex motive => return .existsIntro motive code proof
  | _ => throwError "invalid extracted witness specification"

private partial def sourceType (context : Core.Context) (proof : Core.Proof) :
    CommandElabM Core.Predicate := do
  match proof with
  | .ascribe type _ => return type
  | .hyp i =>
    let some type := context.proofs[i]? | throwError "missing witness proof premise"
    return type
  | .theoremE name fs ps =>
    let some (.theoremE declaration) := (← environment).lookup name |
      throwError "unknown theorem `{name}`"
    return declaration.type.instantiate fs ps
  | .existsIntro motive _ _ => return .ex motive
  | .forallIntro _ motive _ => return .all motive
  | .impIntro _ premise body =>
    return .imp premise (← sourceType (context.pushProof premise) body)
  | .forallElim body argument =>
    let .all motive ← formulaHead (← sourceType context body) |
      throwError "expected a universal witness source"
    return .app motive argument
  | .impElim body _ =>
    let .imp _ result ← formulaHead (← sourceType context body) |
      throwError "expected an implication witness source"
    return result
  | .letE _ type _ body => sourceType (context.pushProof type) body
  | .letTerm _ _ body | .letPredicate _ _ body => sourceType context body
  | _ => checked (Core.inferProof 1024 (← environment) context proof)

private structure Extracted where
  witness : Core.Term
  property : Core.Predicate
  proof : Core.Proof

private def localVariables (depth : Nat) : Core.Term → List Nat
  | .bvar i => if i < depth then [] else [i - depth]
  | .lam _ body => localVariables (depth + 1) body
  | .app f x => localVariables depth f ++ localVariables depth x
  | .letE _ x body => localVariables depth x ++ localVariables (depth + 1) body
  | .primrec z step => localVariables depth z ++ localVariables depth step
  | .definition _ fs => fs.flatMap (localVariables depth)
  | _ => []

private def predicateVariables (depth : Nat) : Core.Predicate → List Nat
  | .equal a b => localVariables depth a ++ localVariables depth b
  | .imp a b | .and a b | .or a b | .letPredicate _ a b =>
    predicateVariables depth a ++ predicateVariables depth b
  | .all p | .ex p => predicateVariables depth p
  | .lam _ p => predicateVariables (depth + 1) p
  | .app p a | .letTerm _ a p => predicateVariables depth p ++ localVariables depth a
  | .definition _ fs ps =>
    fs.flatMap (localVariables depth) ++ ps.flatMap (predicateVariables depth)
  | _ => []

private abbrev Variables := List Nat × List Nat

private def joinVariables (a b : Variables) : Variables := (a.1 ++ b.1, a.2 ++ b.2)

private def proofVariables (nd hd : Nat) : Core.Proof → Variables
  | .hyp i => ([], if i < hd then [] else [i - hd])
  | .theoremE _ fs ps =>
    (fs.flatMap (localVariables nd) ++ ps.flatMap (predicateVariables nd), [])
  | .impIntro _ a p => joinVariables (predicateVariables nd a, []) (proofVariables nd (hd + 1) p)
  | .impElim p q | .andIntro p q => joinVariables (proofVariables nd hd p) (proofVariables nd hd q)
  | .andLeft a b | .andRight a b | .orLeft a b | .orRight a b | .existsElim a b =>
    (predicateVariables nd a ++ predicateVariables nd b, [])
  | .orElim a b c =>
    (predicateVariables nd a ++ predicateVariables nd b ++ predicateVariables nd c, [])
  | .falseElim a | .eqSubst a | .induction a | .lem a => (predicateVariables nd a, [])
  | .ascribe a p => joinVariables (predicateVariables nd a, []) (proofVariables nd hd p)
  | .forallIntro _ a p =>
    joinVariables (predicateVariables nd a, []) (proofVariables (nd + 1) hd p)
  | .forallElim p t => joinVariables (proofVariables nd hd p) (localVariables nd t, [])
  | .existsIntro a t p => joinVariables
      (predicateVariables nd a ++ localVariables nd t, []) (proofVariables nd hd p)
  | .letE _ a p q => joinVariables (predicateVariables nd a, [])
      (joinVariables (proofVariables nd hd p) (proofVariables nd (hd + 1) q))
  | .letTerm _ t p => joinVariables (localVariables nd t, []) (proofVariables nd hd p)
  | .letPredicate _ a p => joinVariables (predicateVariables nd a, []) (proofVariables nd hd p)
  | _ => ([], [])

private def programHead (env : Core.Environment) : Nat → Core.Term → Core.CheckResult Core.Term
  | 0, _ => Core.exhausted
  | fuel + 1, term => do
    if let some value ← Core.exposeTerm (fuel + 1) false term then
      return ← programHead env fuel value
    if let some value ← Core.unfoldTermHead env term then
      return ← programHead env fuel value
    return term

private def hasProofReferenceHead : Core.Proof → Bool
  | .theoremE .. | .hyp _ => true
  | .forallElim p _ | .impElim p _ | .ascribe _ p => hasProofReferenceHead p
  | _ => false

private def hasTermReferenceHead (t : Core.Term) : Bool :=
  match (getAppFnArgs t).1 with
  | .definition .. | .bvar _ | .parameter _ => true
  | _ => false

-- Keep name hints in the environment so they follow declaration rollback.
private initialize nextPartIndex : EnvExtension (NameMap Nat) ← registerEnvExtension (pure {})

private def nameWitness (root : Name) (context : Core.Context) (motive : Core.Predicate)
    (value : Extracted) : CommandElabM Extracted := do
  -- Reuse numerical and proof references without publishing another wrapper around them.
  if hasTermReferenceHead value.witness && hasProofReferenceHead value.proof then
    return value
  let env ← environment
  let mut index := ((nextPartIndex.getState (← getEnv)).find? root).getD 0
  while (env.lookup (root ++ Name.mkSimple s!"part{index}")).isSome do index := index + 1
  let name := root ++ Name.mkSimple s!"part{index}"
  let parameters := context.functions.zipIdx.map fun (arity, i) =>
    Core.FunctionParameter.mk arity (Name.num `f i)
  let body ← checked (programHead env 1024 value.witness)
  let used := (localVariables 0 body).eraseDups.mergeSort (· ≤ ·)
  let mut body := body.rename fun i => (used.idxOf? i).getD 0
  for i in [:used.length] do body := .lam (Name.num `x i) body
  publishChecked (.function ⟨name, parameters, used.length, body⟩) (← getRef)
  modifyEnv (nextPartIndex.modifyState · (·.insert root (index + 1)))
  let witness := applyDefinition name (used.reverse.map Core.Term.bvar)
    ((List.range context.functions.length).map Core.Term.parameter)
  let property := Core.Predicate.app motive witness
  let sourceProof := Core.Proof.ascribe property value.proof
  let variables := proofVariables 0 0 sourceProof
  let hypotheses := variables.2.eraseDups.mergeSort (· ≤ ·)
  let premises := hypotheses.map fun i => context.proofs[i]!
  let locals := (variables.1 ++ premises.flatMap (predicateVariables 0)).eraseDups.mergeSort (· ≤ ·)
  let rename := fun i => (locals.idxOf? i).getD 0
  let mut specification := property.rename rename
  let mut proof := substitute (fun i => .bvar (rename i))
    (substituteHypotheses (fun i => .hyp ((hypotheses.idxOf? i).getD 0)) sourceProof)
  for premise in premises do
    let premise := premise.rename rename
    proof := .impIntro `h premise proof
    specification := .imp premise specification
  for i in [:locals.length] do
    let binder := Name.num `x i
    let motive := Core.Predicate.lam binder specification
    proof := .forallIntro binder motive proof
    specification := .all motive
  let theoremParameters := parameters.map fun parameter =>
    Core.Parameter.function parameter.binderName parameter.arity
  let theoremParameters := theoremParameters ++ context.predicates.zipIdx.map fun (sig, i) =>
    Core.Parameter.predicate (Name.num `P i) sig
  publishChecked (.theoremE ⟨name ++ `checked, theoremParameters, specification, proof⟩)
    (← getRef)
  let mut reference := Core.Proof.theoremE (name ++ `checked)
    ((List.range context.functions.length).map Core.Term.parameter)
    ((List.range context.predicates.length).map Core.Predicate.parameter)
  for i in locals.reverse do reference := .forallElim reference (.bvar i)
  for i in hypotheses.reverse do reference := .impElim reference (.hyp i)
  return ⟨witness, property, reference⟩

private def shareWitness (name : Name) (value : Extracted) (motive target : Core.Predicate)
    (body : Extracted) : Extracted :=
  let premise := Core.Predicate.app motive.shift (.bvar 0)
  let type := Core.Predicate.lam name (.imp premise body.property)
  { witness := .letE name value.witness body.witness
    property := .app target (.letE name value.witness body.witness)
    proof := .impElim (.forallElim (.forallIntro name type
      (.impIntro `hw premise body.proof)) value.witness) value.proof }

/-- Whether a theorem of `type` can be compiled once: it concludes with an existence statement,
and each premise is quantifier-free or an existence statement with a quantifier-free body. -/
private partial def hasExistentialResult (context : Core.Context) (type : Core.Predicate) :
    CommandElabM Bool := do
  match ← formulaHead type with
  | .all motive =>
    hasExistentialResult (context.pushLocal 0) (.app motive.shift (.bvar 0))
  | .imp premise result =>
    match Core.inferFormula 1024 (← environment) context premise with
    | .ok .qf => hasExistentialResult (context.pushProof premise) result
    | _ =>
      let .ex motive ← formulaHead premise | return false
      let opened := context.pushLocal 0
      let body := Core.Predicate.app motive.shift (.bvar 0)
      match Core.inferFormula 1024 (← environment) opened body with
      | .ok .qf => hasExistentialResult (opened.pushProof body) result.shift
      | _ => return false
  | .ex _ => return true
  | _ => return false

private def openExistentialBranch : Core.Proof → Core.Proof
  | .forallIntro _ _ (.impIntro _ _ body) => body
  | branch => .impElim (.forallElim (shiftProof branch 1 1) (.bvar 0)) (.hyp 0)

mutual

private partial def proofHead (p : Core.Proof) : CommandElabM Core.Proof := do
  match p with
  | .theoremE n fs ps =>
    let some (.theoremE d) := (← environment).lookup n | throwError "unknown theorem `{n}`"
    if let some info := (witnesses.getState (← getEnv)).find? (·.source == n) then
      return ← reconstruct info.opened (d.type.instantiate fs ps)
        (applyDefinition info.code [] fs) (.theoremE (info.code ++ `checked) fs ps)
    if ← hasExistentialResult { functions := d.functions, predicates := d.predicates } d.type then
      let code := (← getEnv).mainModule ++ `Witnesses ++ n
      compileWitnessCore true n code (← getRef)
      return ← reconstruct true (d.type.instantiate fs ps) (applyDefinition code [] fs)
        (.theoremE (code ++ `checked) fs ps)
    proofHead (instantiate fs ps d.body)
  | .ascribe _ q | .letTerm _ _ q | .letPredicate _ _ q => proofHead q
  | .impElim (.andLeft _ _) q =>
    match ← proofHead q with
    | .andIntro a _ => proofHead a
    | _ => throwError "cannot extract a witness from this conjunction projection"
  | .impElim (.andRight _ _) q =>
    match ← proofHead q with
    | .andIntro _ b => proofHead b
    | _ => throwError "cannot extract a witness from this conjunction projection"
  | .impElim (.impElim (.existsElim _ _) _) _
  | .impElim (.impElim (.forallElim (.forallElim (.eqSubst _) _) _) _) _
  | .impElim (.falseElim _) _ => return p
  | .impElim f a =>
    match ← proofHead f with
    | .impIntro _ _ body => proofHead (substituteHypothesis body a)
    | .letE n ty value body =>
      proofHead (.letE n ty value (.impElim body (shiftProof a 0 1)))
    | .impElim (.impElim (.existsElim motive ty) value) branch =>
      let .imp _ target ← formulaHead ty | throwError "expected an implication elimination"
      proofHead (eliminateExists motive target value
        (.impElim (openExistentialBranch branch) (shiftProof a 1 1)))
    | _ => throwError "the witness depends on an unapplied proof assumption"
  | .forallElim f a =>
    match ← proofHead f with
    | .forallIntro _ _ body => proofHead (substitute (fun | 0 => a | i + 1 => .bvar i) body)
    | .letE n ty value body => proofHead (.letE n ty value (.forallElim body a))
    | .impElim (.impElim (.existsElim source ty) value) branch =>
      let .all motive ← formulaHead ty | throwError "expected a universal elimination"
      proofHead (eliminateExists source (.app motive a) value
        (.forallElim (openExistentialBranch branch) a.shift))
    | _ => throwError "the witness depends on an unapplied universal assumption"
  | .letE n a value body =>
    match ← formulaHead a with
    | .ex _ => return .letE n a value body
    | _ => proofHead (substituteHypothesis body value)
  | _ => return p

private partial def extract (root : Name) (context : Core.Context) (target : Core.Predicate)
    (p : Core.Proof) : CommandElabM Extracted := do
  let p ← proofHead p
  let result ← match p with
    | .existsIntro _ witness proof =>
      let property := Core.Predicate.app target witness
      pure ⟨witness, property, .ascribe property proof⟩
    | .letE n a value body =>
      let .ex motive ← formulaHead a | throwError "expected an existential let"
      let value ← extract root context motive value
      let premise := Core.Predicate.app motive.shift (.bvar 0)
      let body := shiftProof body 1 0
      let body := substituteHypotheses (fun
        | 0 => .existsIntro motive.shift (.bvar 0) (.hyp 0)
        | i + 1 => .hyp (i + 1)) body
      let body ← extract root ((context.pushLocal 0).pushProof premise) target.shift body
      pure (shareWitness n value motive target body)
    | .impElim (.impElim (.existsElim motive _) value) branch =>
      let value ← extract root context motive value
      let premise := Core.Predicate.app motive.shift (.bvar 0)
      let body ← extract root ((context.pushLocal 0).pushProof premise) target.shift
        (openExistentialBranch branch)
      pure (shareWitness `w value motive target body)
    | .impElim (.impElim (.forallElim (.forallElim (.eqSubst motive) lhs) rhs) equality)
        proof =>
      let ty ← sourceType context proof
      let .ex source ← formulaHead ty | throwError "expected existential equality transport"
      let result ← extract root context source proof
      let .ex body ← formulaHead (.app motive.shift (.bvar 0)) |
        throwError "equality transport changes the shape of an existential"
      let property := Core.Predicate.lam `x (.app body result.witness.shift)
      let proof := Core.Proof.impElim
        (.impElim (.forallElim (.forallElim (.eqSubst property) lhs) rhs) equality) result.proof
      pure ⟨result.witness, .app target result.witness,
        .ascribe (.app target result.witness) proof⟩
    | .impElim (.falseElim _) proof =>
      pure ⟨.zero, .app target .zero, .impElim (.falseElim (.app target .zero)) proof⟩
    | _ => throwError "recursive proof branches must provide a constructive numerical witness"
  nameWitness root context target result

private partial def extractArguments (root : Name) (opened : Bool) (context : Core.Context)
    (type : Core.Predicate) (proof : Core.Proof) : CommandElabM (Nat × Extracted) := do
  match ← formulaHead type with
  | .all motive =>
    let body := Core.Proof.forallElim (shiftProof proof 1 0) (.bvar 0)
    let (arity, result) ← extractArguments root opened (context.pushLocal 0)
      (.app motive.shift (.bvar 0)) body
    return (arity + 1, ⟨.lam `x result.witness, .all (.lam `x result.property),
      .forallIntro `x (.lam `x result.property) result.proof⟩)
  | .imp a b =>
    if opened then
      if let .ex motive ← formulaHead a then
        -- The number of an existence premise becomes an argument, and its property a premise.
        let premise := Core.Predicate.app motive.shift (.bvar 0)
        let body := Core.Proof.impElim (shiftProof proof 1 1)
          (.existsIntro motive.shift (.bvar 0) (.hyp 0))
        let (arity, result) ← extractArguments root opened
          ((context.pushLocal 0).pushProof premise) b.shift body
        let property := Core.Predicate.lam `w (.imp premise result.property)
        return (arity + 1, ⟨.lam `w result.witness, .all property,
          .forallIntro `w property (.impIntro `h premise result.proof)⟩)
    let body := Core.Proof.impElim (shiftProof proof 0 1) (.hyp 0)
    let (arity, result) ← extractArguments root opened (context.pushProof a) b body
    return (arity, ⟨result.witness, .imp a result.property, .impIntro `h a result.proof⟩)
  | .ex motive => return (0, ← extract root context motive proof)
  | _ => throwError "the theorem must conclude with an existential formula"

private partial def compileWitnessCore (opened : Bool) (source target : Name) (stx : Syntax) :
    CommandElabM Unit := do
  let env ← environment
  let some (.theoremE d) ← LeanPRA.Surface.resolveDeclaration? env source |
    throwError "expected a PRA theorem"
  let context : Core.Context := { functions := d.functions, predicates := d.predicates }
  let (arity, result) ← extractArguments target opened context d.type d.body
  let parameters := d.parameters.filterMap fun
    | .function n k => some (Core.FunctionParameter.mk k n)
    | _ => none
  publishChecked (.function ⟨target, parameters, arity, result.witness⟩) stx
  publishChecked (.theoremE ⟨target ++ `checked, d.parameters, result.property, result.proof⟩) stx
  modifyEnv (witnesses.addEntry · ⟨d.name, target, opened⟩)

end

/-- Compile an explicit proof in its local context into a numerical witness and its specification.
Numerical universal binders become function arguments. Proof premises remain in the specification.
The source proof and all shared declarations pass through the PRA checker. -/
def compileProof (root : Name) (context : Core.Context) (type : Core.Predicate)
    (proof : Core.Proof) : CommandElabM (Core.Term × Core.Predicate × Core.Proof) := do
  let _ ← checked (Core.checkProof 1024 (← environment) context proof type)
  let (_, result) ← extractArguments root false context type proof
  return (result.witness, result.property, result.proof)

/-- Compile a checked theorem into a numerical function and a checked specification theorem.
The premises of the theorem remain in the specification as they are stated. -/
def compileWitness (source target : Name) (stx : Syntax) : CommandElabM Unit :=
  compileWitnessCore false source target stx

end LeanPRA.Library.Tactic.Witnessing
