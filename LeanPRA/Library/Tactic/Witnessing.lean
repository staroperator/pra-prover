module

public meta import LeanPRA.Library.Tactic.Construction

/-!
# Compilation of numerical witnesses

`compileWitness` and `compileProof` extract numerical programs and correctness proofs from
constructive proofs of existential statements. Recursive proof tactics such as `sigma_induction`
use the extracted programs as primitive-recursion branches.

- `extract_witness thm₁ thm₂ ⋯` compiles each named existential theorem inside a `pra` block.
- `compileWitness` compiles a checked theorem `thm` into the numerical function `thm.witness` and
  the specification theorem `thm.witness_correct`.
- `compileProof` compiles an explicit proof in a local context into `root.witness` and
  `root.witness_correct` under a caller-supplied name `root`, returning a call to the function,
  its property, and a reference to the theorem.
- `elaborateExtractWitness` elaborates the `extract_witness` command by calling `compileWitness`
  on each identifier.

Universal numerical binders and the witnesses of existential premises become function arguments,
and the bodies of existential premises become implication assumptions in the specification. For
example, a theorem of type `(∃ u, Q u) → ∃ v, R v` produces a function `f` and a specification of
type `∀ u, Q u → R (f u)`. Other premises stay in the specification unchanged.

The compiler traverses constructive introductions, eliminations, and equality transport. When a
proof obtains a witness `w` from an intermediate existential statement, the continuation is
compiled for an arbitrary `w` satisfying that statement's body, and the resulting proof is applied
to the intermediate witness term. That term is substituted for `w` in the continuation's witness
term, keeping the entire result in `thm.witness` and `thm.witness_correct`. Both declarations pass
through the PRA checker before publication.

When a compiled proof references another theorem whose conclusion is existential and whose
premises are quantifier-free or existential with quantifier-free bodies, the referenced theorem is
compiled once and reused. At each call site, the witnesses for any existential premises are first
extracted from the premise proofs. A theorem from the current module is compiled under its own
name; an imported theorem is compiled under `<current module>.Witnesses.<theorem>` so that separate
modules publish distinct names. If the referenced theorem's extracted witness is a single variable
or function call and its proof has at most `directLimit` steps, the compiler unfolds the theorem at
each use instead of publishing a separate witness declaration. Theorems with other premise shapes
are also unfolded at each use.
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

/-- Records theorems encountered by the compiler. A compiled theorem is stored with `some root`,
where `root.witness` and `root.witness_correct` are the published declaration names. A short
theorem whose witness is a single variable or function call is stored with `none` and unfolded at
each use. -/
private initialize witnesses :
    SimplePersistentEnvExtension (Name × Option Name) (NameMap (Option Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun roots (source, root) => roots.insert source root
    addImportedFn := fun entries => entries.foldl (init := {}) fun roots entries =>
      entries.foldl (init := roots) fun roots (source, root) => roots.insert source root
  }

private def programName (root : Name) : Name := root ++ `witness

private def correctnessName (root : Name) : Name := root ++ `witness_correct

private def eliminateExists (motive target : Core.Predicate) (value body : Core.Proof) :
    Core.Proof :=
  let premise := Core.Predicate.app motive.shift (.bvar 0)
  .impElim (.impElim (.existsElim motive target) value)
    (.forallIntro `w (.lam `w (.imp premise target.shift)) (.impIntro `h premise body))

/-- Prove a theorem of `type` from its compiled program `code` and checked specification `proof`.
Each existence premise supplies its number to `code` and to `proof`. -/
private partial def reconstruct (type : Core.Predicate) (code : Core.Term)
    (proof : Core.Proof) : CommandElabM Core.Proof := do
  match ← formulaHead type with
  | .all motive =>
    let body ← reconstruct (.app motive.shift (.bvar 0)) (.app code.shift (.bvar 0))
      (.forallElim (shiftProof proof 1 0) (.bvar 0))
    return .forallIntro `x motive body
  | .imp a b =>
    if let .ex motive ← formulaHead a then
      -- Inside the branch, `w` is the premise's number and hypothesis `0` its property.
      let body ← reconstruct b.shift (.app code.shift (.bvar 0))
        (.impElim (.forallElim (shiftProof proof 1 2) (.bvar 0)) (.hyp 0))
      return .impIntro `h a (eliminateExists motive b (.hyp 0) body)
    let body ← reconstruct b code (.impElim (shiftProof proof 0 1) (.hyp 0))
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

private def hasProofReferenceHead : Core.Proof → Bool
  | .theoremE .. | .hyp _ => true
  | .forallElim p _ | .impElim p _ | .ascribe _ p => hasProofReferenceHead p
  | _ => false

private def hasTermReferenceHead (t : Core.Term) : Bool :=
  match (getAppFnArgs t).1 with
  | .definition .. | .bvar _ | .parameter _ => true
  | _ => false

/-- Whether `program`, beneath its outer lambdas, is a variable, zero, or a named function applied
to atomic arguments. -/
private def isCall (program : Core.Term) : Bool :=
  let atom : Core.Term → Bool
    | .bvar _ | .parameter _ | .zero | .definition _ [] => true
    | _ => false
  let rec body : Core.Term → Core.Term
    | .lam _ t => body t
    | t => t
  let (head, arguments) := getAppFnArgs (body program)
  arguments.all atom && match head with
    | .definition _ functions => functions.all atom
    | head => atom head

/-- The number of inference steps in a proof. -/
private def proofSteps : Core.Proof → Nat
  | .impIntro _ _ p | .forallIntro _ _ p | .forallElim p _ | .existsIntro _ _ p
  | .letTerm _ _ p | .letPredicate _ _ p | .ascribe _ p => proofSteps p + 1
  | .impElim p q | .andIntro p q | .letE _ _ p q => proofSteps p + proofSteps q + 1
  | _ => 1

/-- Maximum step count for unfolding a theorem whose witness is a single variable or function call
at each use. Longer proofs are published once as compiled witness declarations. -/
private def directLimit : Nat := 128

private def functionParameters (context : Core.Context) : List Core.FunctionParameter :=
  context.functions.zipIdx.map fun (arity, i) => Core.FunctionParameter.mk arity (Name.num `f i)

/-- Publish `program` as a function `name` taking the local variables that `program` uses, and
return the application of that function to those variables. -/
private def publishProgram (name : Name) (context : Core.Context) (program : Core.Term) :
    CommandElabM Core.Term := do
  let used := (localVariables 0 program).eraseDups.mergeSort (· ≤ ·)
  let mut body := program.rename fun i => (used.idxOf? i).getD 0
  for i in [:used.length] do body := .lam (Name.num `x i) body
  publishChecked (.function ⟨name, functionParameters context, used.length, body⟩) (← getRef)
  return applyDefinition name (used.reverse.map Core.Term.bvar)
    ((List.range context.functions.length).map Core.Term.parameter)

/-- Publish the witness of `value` as the function `root.witness` and its proof as the theorem
`root.witness_correct`, returning the function call, its property, and a reference to the theorem.
The theorem takes the local variables and proof premises used by the proof. -/
private def publishLocal (root : Name) (context : Core.Context) (motive : Core.Predicate)
    (value : Extracted) : CommandElabM Extracted := do
  -- Reuse numerical and proof references without publishing another wrapper around them.
  if hasTermReferenceHead value.witness && hasProofReferenceHead value.proof then
    return value
  let witness ← publishProgram (programName root) context value.witness
  let property := Core.Predicate.app motive witness
  let sourceProof := Core.Proof.ascribe property value.proof
  let variables := proofVariables 0 0 sourceProof
  let hypotheses := variables.2.eraseDups.mergeSort (· ≤ ·)
  let premises := hypotheses.map fun i => context.proofs[i]!
  let locals := variables.1 ++ premises.flatMap (predicateVariables 0)
  let locals := locals.eraseDups.mergeSort (· ≤ ·)
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
  let parameters := (functionParameters context).map fun parameter =>
    Core.Parameter.function parameter.binderName parameter.arity
  let parameters := parameters ++ context.predicates.zipIdx.map fun (sig, i) =>
    Core.Parameter.predicate (Name.num `P i) sig
  publishChecked (.theoremE ⟨correctnessName root, parameters, specification, proof⟩)
    (← getRef)
  let mut reference := Core.Proof.theoremE (correctnessName root)
    ((List.range context.functions.length).map Core.Term.parameter)
    ((List.range context.predicates.length).map Core.Predicate.parameter)
  for i in locals.reverse do reference := .forallElim reference (.bvar i)
  for i in hypotheses.reverse do reference := .impElim reference (.hyp i)
  return ⟨witness, property, reference⟩

/-- Combine the compiled intermediate statement `value` with the compiled continuation `body`.
The continuation was compiled for an arbitrary number `name` with property `motive name`. Its
proof is applied to the program of `value`, which also replaces `name` in the program of `body`. -/
private def shareWitness (name : Name) (value : Extracted) (motive target : Core.Predicate)
    (body : Extracted) : Extracted :=
  let premise := Core.Predicate.app motive.shift (.bvar 0)
  let type := Core.Predicate.lam name (.imp premise body.property)
  let witness := body.witness.subst0 value.witness
  { witness
    property := .app target witness
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
    let compiled (root : Name) := reconstruct (d.type.instantiate fs ps)
      (applyDefinition (programName root) [] fs) (.theoremE (correctnessName root) fs ps)
    match (witnesses.getState (← getEnv)).find? n with
    | some (some root) => return ← compiled root
    | some none => return ← proofHead (instantiate fs ps d.body)
    | none => pure ()
    if ← hasExistentialResult { functions := d.functions, predicates := d.predicates } d.type then
      let env ← getEnv
      let root := if LeanPRA.Surface.CoreEnvironment.isLocal env n then n
        else env.mainModule ++ `Witnesses ++ n
      if ← compileWitnessCore d root false (← getRef) then return ← compiled root
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

private partial def extract (context : Core.Context) (target : Core.Predicate)
    (p : Core.Proof) : CommandElabM Extracted := do
  match ← proofHead p with
  | .existsIntro _ witness proof =>
    let property := Core.Predicate.app target witness
    return ⟨witness, property, .ascribe property proof⟩
  | .letE n a value body =>
    let .ex motive ← formulaHead a | throwError "expected an existential let"
    let value ← extract context motive value
    let premise := Core.Predicate.app motive.shift (.bvar 0)
    let body := shiftProof body 1 0
    let body := substituteHypotheses (fun
      | 0 => .existsIntro motive.shift (.bvar 0) (.hyp 0)
      | i + 1 => .hyp (i + 1)) body
    let body ← extract ((context.pushLocal 0).pushProof premise) target.shift body
    return shareWitness n value motive target body
  | .impElim (.impElim (.existsElim motive _) value) branch =>
    let value ← extract context motive value
    let premise := Core.Predicate.app motive.shift (.bvar 0)
    let body ← extract ((context.pushLocal 0).pushProof premise) target.shift
      (openExistentialBranch branch)
    return shareWitness `w value motive target body
  | .impElim (.impElim (.forallElim (.forallElim (.eqSubst motive) lhs) rhs) equality) proof =>
    let ty ← sourceType context proof
    let .ex source ← formulaHead ty | throwError "expected existential equality transport"
    let result ← extract context source proof
    let .ex body ← formulaHead (.app motive.shift (.bvar 0)) |
      throwError "equality transport changes the shape of an existential"
    let property := Core.Predicate.lam `x (.app body result.witness.shift)
    let proof := Core.Proof.impElim
      (.impElim (.forallElim (.forallElim (.eqSubst property) lhs) rhs) equality) result.proof
    return ⟨result.witness, .app target result.witness,
      .ascribe (.app target result.witness) proof⟩
  | .impElim (.falseElim _) proof =>
    return ⟨.zero, .app target .zero, .impElim (.falseElim (.app target .zero)) proof⟩
  | _ => throwError "recursive proof branches must provide a constructive numerical witness"

/-- Compile `proof` of `type` beneath its numerical binders and premises, returning the argument
count along with the extracted witness, property, and proof. When `publish` is true, the innermost
step publishes `root.witness` and `root.witness_correct` in the local context. When `publish` is
false, `context` contains only declaration parameters, the caller publishes `root.witness`, and the
returned specification refers to `root.witness` by name. -/
private partial def extractArguments (root : Name) (publish : Bool) (context : Core.Context)
    (type : Core.Predicate) (proof : Core.Proof) : CommandElabM (Nat × Extracted) := do
  match ← formulaHead type with
  | .all motive =>
    let body := Core.Proof.forallElim (shiftProof proof 1 0) (.bvar 0)
    let (arity, result) ← extractArguments root publish (context.pushLocal 0)
      (.app motive.shift (.bvar 0)) body
    return (arity + 1, ⟨.lam `x result.witness, .all (.lam `x result.property),
      .forallIntro `x (.lam `x result.property) result.proof⟩)
  | .imp a b =>
    if let .ex motive ← formulaHead a then
      -- The number of an existence premise becomes an argument, and its property a premise.
      let premise := Core.Predicate.app motive.shift (.bvar 0)
      let body := Core.Proof.impElim (shiftProof proof 1 1)
        (.existsIntro motive.shift (.bvar 0) (.hyp 0))
      let (arity, result) ← extractArguments root publish
        ((context.pushLocal 0).pushProof premise) b.shift body
      let property := Core.Predicate.lam `w (.imp premise result.property)
      return (arity + 1, ⟨.lam `w result.witness, .all property,
        .forallIntro `w property (.impIntro `h premise result.proof)⟩)
    let body := Core.Proof.impElim (shiftProof proof 0 1) (.hyp 0)
    let (arity, result) ← extractArguments root publish (context.pushProof a) b body
    return (arity, ⟨result.witness, .imp a result.property, .impIntro `h a result.proof⟩)
  | .ex motive =>
    let result ← extract context motive proof
    if publish then return (0, ← publishLocal root context motive result)
    -- The local variables are the arguments of the program, the first one outermost.
    let call := applyDefinition (programName root)
      ((List.range context.locals.length).reverse.map Core.Term.bvar)
      ((List.range context.functions.length).map Core.Term.parameter)
    let property := Core.Predicate.app motive call
    return (0, ⟨result.witness, property, .ascribe property result.proof⟩)
  | _ => throwError "the theorem must conclude with an existential formula"

/-- Compile the theorem `d` into `root.witness` and `root.witness_correct`, and return whether
those declarations were published. When `always` is false, a theorem whose witness is a single
variable or function call and whose proof has at most `directLimit` steps is recorded with `none`
for unfolding at each use. -/
private partial def compileWitnessCore (d : Core.TheoremDefinition) (root : Name) (always : Bool)
    (stx : Syntax) : CommandElabM Bool := do
  let context : Core.Context := { functions := d.functions, predicates := d.predicates }
  let (arity, result) ← extractArguments root false context d.type d.body
  if !always && isCall result.witness && proofSteps result.proof ≤ directLimit then
    modifyEnv (witnesses.addEntry · (d.name, none))
    return false
  let parameters := d.parameters.filterMap fun
    | .function n k => some (Core.FunctionParameter.mk k n)
    | _ => none
  publishChecked (.function ⟨programName root, parameters, arity, result.witness⟩) stx
  publishChecked
    (.theoremE ⟨correctnessName root, d.parameters, result.property, result.proof⟩) stx
  modifyEnv (witnesses.addEntry · (d.name, some root))
  return true

end

/-- Compile an explicit proof in its local context into the function `root.witness` and the
theorem `root.witness_correct`, returning a call to the function, its property, and a reference to
the theorem. Universal numerical binders and the witnesses of existential premises become function
arguments, while other premises stay in the specification. The published declarations take the
local variables and proof premises from `context` that the proof uses. When the extracted witness
and proof already head-reference existing declarations or variables, they are returned directly. -/
def compileProof (root : Name) (context : Core.Context) (type : Core.Predicate)
    (proof : Core.Proof) : CommandElabM (Core.Term × Core.Predicate × Core.Proof) := do
  let _ ← checked (Core.checkProof 1024 (← environment) context proof type)
  let (_, result) ← extractArguments root true context type proof
  return (result.witness, result.property, result.proof)

/-- Compile a checked theorem `source` into the numerical function `source.witness` and the
specification theorem `source.witness_correct`. Universal numerical binders and the witnesses of
existential premises become function arguments, while other premises stay in the specification. If
`source` has already been compiled under its own name, `compileWitness` leaves the environment
unchanged. Call `compileWitness` in at most one module among modules that are imported together so
that `source.witness` is published only once. -/
def compileWitness (source : Name) (stx : Syntax) : CommandElabM Unit := do
  let some (.theoremE d) ← LeanPRA.Surface.resolveDeclaration? (← environment) source |
    throwError "expected a PRA theorem"
  unless (witnesses.getState (← getEnv)).find? d.name == some (some d.name) do
    discard <| compileWitnessCore d d.name true stx

/-- `extract_witness thm₁ thm₂` compiles each named theorem `thmᵢ` with `compileWitness`,
publishing the function `thmᵢ.witness` and the theorem `thmᵢ.witness_correct`. -/
syntax (name := extractWitness) "extract_witness" (ppSpace colGt ident)+ : praDecl

@[command_elab LeanPRA.Surface.praEntry]
def elaborateExtractWitness : CommandElab := fun stx => do
  let `(praDecl| extract_witness $names:ident*) := stx[0] | throwUnsupportedSyntax
  for name in names do
    withRef name do compileWitness name.getId name

end LeanPRA.Library.Tactic.Witnessing
