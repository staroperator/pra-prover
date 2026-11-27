module

public meta import PRAProver.Surface.Metavariable.State

/-!
# Resolving metavariable assignments

Metavariable assignment resolution and local variable renaming across scopes:

- `resolveTerm` and `resolvePredicate` replace assigned metavariables with their values and adjust
  free local variable indices from the metavariable's creation scope to the current scope.
- `renameTerm` and `renamePredicate` map free local variable indices between two local variable ID
  lists, failing when a variable is absent from the target scope.
- `resolveProof` expands assigned subproofs and substitutes their explicit context arguments.
- `assignProof` checks proof-reference scopes and cycles before storing an assignment.
-/

public meta section
namespace PRAProver.Surface.Metavariable
open Core hiding Term Predicate Proof Context

private def move (source target : List Nat) (i : Nat) : Except Failure Nat := do
  let some id := source[i]? | throw (.invalid "invalid local variable in implicit argument")
  let some index := target.idxOf? id
    | throw (.invalid "implicit argument depends on a variable outside its scope")
  return index

mutual
def renameTerm (source target : List Nat) (depth : Nat) : Term → Except Failure Term
  | .bvar i => if i < depth then pure (.bvar i)
      else return .bvar (depth + (← move source target (i - depth)))
  | .lam n t => return .lam n (← renameTerm source target (depth + 1) t)
  | .app f a =>
    return (.app
      (← renameTerm source target depth f)
      (← renameTerm source target depth a))
  | .letE n a b =>
    return (.letE n
      (← renameTerm source target depth a)
      (← renameTerm source target (depth + 1) b))
  | .primrec b s =>
    return (.primrec
      (← renameTerm source target depth b)
      (← renameTerm source target depth s))
  | .definition n fs => return .definition n (← fs.mapM (renameTerm source target depth))
  | t => pure t
end

mutual
/-- Replace assigned numerical metavariables in `t`, renaming free local variables from each
metavariable's creation scope into `locals`. -/
def resolveTerm (state : State) (locals : List Nat) : Nat → Term → Except Failure Term
  | 0, _ => throw (.exhausted "implicit argument substitution depth")
  | fuel + 1, t => match t with
    | .parameter i =>
      if i < state.baseFunctions then pure t
      else throw (.invalid "rigid numerical parameter outside the declaration")
    | .mvar i =>
      match state.terms[i]? with
      | some u => match u.value with
          | none => pure t
          | some value => do
            let value ← renameTerm u.locals locals 0 value
            resolveTerm state locals fuel value
      | none => throw (.invalid "unknown numerical metavariable")
    | .lam n b => return .lam n (← resolveTerm state (0 :: locals) fuel b)
    | .app f a =>
      return (.app
        (← resolveTerm state locals fuel f)
        (← resolveTerm state locals fuel a))
    | .letE n a b =>
      return (.letE n
        (← resolveTerm state locals fuel a)
        (← resolveTerm state (0 :: locals) fuel b))
    | .primrec b s =>
      return (.primrec
        (← resolveTerm state locals fuel b)
        (← resolveTerm state locals fuel s))
    | .definition n fs => return .definition n (← fs.mapM (resolveTerm state locals fuel))
    | _ => pure t

/-- Replace assigned numerical and predicate metavariables in `p`, renaming free local variables
into `locals`. -/
def resolvePredicate (state : State) (locals : List Nat) :
    Nat → Predicate → Except Failure Predicate
  | 0, _ => throw (.exhausted "implicit argument substitution depth")
  | fuel + 1, p => match p with
    | .parameter i =>
      if i < state.basePredicates then pure p
      else throw (.invalid "rigid predicate parameter outside the declaration")
    | .mvar i =>
      match state.predicates[i]? with
      | some u => match u.value with
        | none => pure p
        | some value => do
          let value ← renamePredicate u.locals locals 0 value
          resolvePredicate state locals fuel value
      | none => throw (.invalid "unknown predicate metavariable")
    | .equal a b =>
      return (.equal
        (← resolveTerm state locals fuel a)
        (← resolveTerm state locals fuel b))
    | .imp a b =>
      return (.imp
        (← resolvePredicate state locals fuel a)
        (← resolvePredicate state locals fuel b))
    | .and a b =>
      return (.and
        (← resolvePredicate state locals fuel a)
        (← resolvePredicate state locals fuel b))
    | .or a b =>
      return (.or
        (← resolvePredicate state locals fuel a)
        (← resolvePredicate state locals fuel b))
    | .all p => return .all (← resolvePredicate state locals fuel p)
    | .ex p => return .ex (← resolvePredicate state locals fuel p)
    | .lam n p => return .lam n (← resolvePredicate state (0 :: locals) fuel p)
    | .app p a =>
      return (.app
        (← resolvePredicate state locals fuel p)
        (← resolveTerm state locals fuel a))
    | .letTerm n a p =>
      return (.letTerm n
        (← resolveTerm state locals fuel a)
        (← resolvePredicate state locals fuel p))
    | .letPredicate n p q =>
      return (.letPredicate n
        (← resolvePredicate state locals fuel p)
        (← resolvePredicate state locals fuel q))
    | .definition n fs ps =>
      return (.definition n
        (← fs.mapM (resolveTerm state locals fuel))
        (← ps.mapM (resolvePredicate state locals fuel)))
    | _ => pure p

def renamePredicate (source target : List Nat) (depth : Nat) :
    Predicate → Except Failure Predicate
  | .equal a b =>
    return (.equal
      (← renameTerm source target depth a)
      (← renameTerm source target depth b))
  | .imp a b =>
    return (.imp
      (← renamePredicate source target depth a)
      (← renamePredicate source target depth b))
  | .and a b =>
    return (.and
      (← renamePredicate source target depth a)
      (← renamePredicate source target depth b))
  | .or a b =>
    return (.or
      (← renamePredicate source target depth a)
      (← renamePredicate source target depth b))
  | .all p => return .all (← renamePredicate source target depth p)
  | .ex p => return .ex (← renamePredicate source target depth p)
  | .lam n p => return .lam n (← renamePredicate source target (depth + 1) p)
  | .app p a =>
    return (.app
      (← renamePredicate source target depth p)
      (← renameTerm source target depth a))
  | .letTerm n a p =>
    return (.letTerm n
      (← renameTerm source target depth a)
      (← renamePredicate source target depth p))
  | .letPredicate n p q =>
    return (.letPredicate n
      (← renamePredicate source target depth p)
      (← renamePredicate source target depth q))
  | .definition n fs ps =>
    return (.definition n
      (← fs.mapM (renameTerm source target depth))
      (← ps.mapM (renamePredicate source target depth)))
  | p => pure p
end

private def checkTermContext (locals : Nat) : Term → Except Failure Unit
  | .bvar i =>
    unless i < locals do throw (.invalid "invalid local variable in implicit argument")
  | .lam _ t => checkTermContext (locals + 1) t
  | .app f a | .primrec f a => do
    checkTermContext locals f
    checkTermContext locals a
  | .letE _ a b => do
    checkTermContext locals a
    checkTermContext (locals + 1) b
  | .definition _ fs => do
    let _ ← fs.mapM (checkTermContext locals)
    pure ()
  | _ => pure ()

private def checkPredicateContext (locals : Nat) : Predicate → Except Failure Unit
  | .equal a b => do
    checkTermContext locals a
    checkTermContext locals b
  | .imp a b | .and a b | .or a b | .letPredicate _ a b => do
    checkPredicateContext locals a
    checkPredicateContext locals b
  | .all p | .ex p => checkPredicateContext locals p
  | .lam _ p => checkPredicateContext (locals + 1) p
  | .app p a => do
    checkPredicateContext locals p
    checkTermContext locals a
  | .letTerm _ a p => do
    checkTermContext locals a
    checkPredicateContext locals p
  | .definition _ fs ps => do
    let _ ← fs.mapM (checkTermContext locals)
    let _ ← ps.mapM (checkPredicateContext locals)
    pure ()
  | _ => pure ()

private def checkProofContext (state : State) (locals : List Nat) (hypotheses : Nat) (p : Proof) :
    Except Failure Unit := do
  let term := checkTermContext locals.length
  let pred := checkPredicateContext locals.length
  match p with
  | .mvar id ts ps =>
    let some entry := state.proofs[id]? | throw (.invalid "unknown proof metavariable")
    unless ts.length == entry.context.locals.length && ps.length == entry.context.proofs.length do
      throw (.invalid "proof metavariable context argument count mismatch")
    for t in ts do term t
    for p in ps do checkProofContext state locals hypotheses p
  | .hyp i =>
    unless i < hypotheses do throw (.invalid "unbound proof hypothesis")
  | .impIntro _ a p =>
    pred a
    checkProofContext state locals (hypotheses + 1) p
  | .forallIntro _ a p =>
    pred a
    checkProofContext state (0 :: locals) hypotheses p
  | .letE _ a p q =>
    pred a
    checkProofContext state locals hypotheses p
    checkProofContext state locals (hypotheses + 1) q
  | .letPredicate _ a p | .ascribe a p =>
    pred a
    checkProofContext state locals hypotheses p
  | .forallElim p t | .letTerm _ t p =>
    term t
    checkProofContext state locals hypotheses p
  | .existsIntro a t p =>
    pred a
    term t
    checkProofContext state locals hypotheses p
  | .impElim p q | .andIntro p q =>
    checkProofContext state locals hypotheses p
    checkProofContext state locals hypotheses q
  | .lem p => pred p
  | .theoremE _ ts ps =>
    for t in ts do term t
    for p in ps do pred p
  | .andLeft a b | .andRight a b | .orLeft a b | .orRight a b | .existsElim a b =>
    pred a
    pred b
  | .orElim a b c =>
    pred a
    pred b
    pred c
  | .falseElim a | .eqSubst a | .induction a => pred a
  | .trueIntro | .eqRefl | .succNeZero | .succInj => pure ()

/-- Resolve proof assignments and embedded numerical and predicate assignments. Each proof
metavariable is resolved in its creation context, then instantiated with the occurrence's context
arguments.
An unassigned proof metavariable is an error. Assignments with unresolved arguments stay as
contextual occurrences so their creation context remains available on a later resolution pass.
`locals` gives numerical local identities, and `hypotheses` counts the available proof hypotheses.
The result uses indices in that context. -/
def resolveProof (state : State) (locals : List Nat) (hypotheses : Nat) (depth : Nat)
    (value : Proof) : Except Failure Proof := do
  checkProofContext state locals hypotheses value
  -- Substitution preserves bounds when stored contexts have their advertised sizes.
  let compactScopes := state.proofs.all fun entry =>
    entry.locals.length == entry.context.locals.length
  go (!hasUnassigned state) compactScopes [] locals hypotheses depth value
where
  go (completeArguments compactScopes : Bool) (visiting locals : List Nat)
      (hypotheses : Nat) :
      Nat → Proof → Except Failure Proof
    | 0, _ => throw (.exhausted "proof substitution depth")
    | fuel + 1, p => do
      let term := resolveTerm state locals fuel
      let pred := resolvePredicate state locals fuel
      let proof := go completeArguments compactScopes visiting locals hypotheses fuel
      let hypothesis := go completeArguments compactScopes visiting locals (hypotheses + 1) fuel
      let numerical := go completeArguments compactScopes visiting (0 :: locals) hypotheses fuel
      match p with
      | .mvar id ts ps =>
        if visiting.contains id then throw (.invalid "cyclic proof metavariable assignment")
        let some entry := state.proofs[id]? | throw (.invalid "unknown proof metavariable")
        unless ts.length == entry.context.locals.length &&
            ps.length == entry.context.proofs.length do
          throw (.invalid "proof metavariable context argument count mismatch")
        let some assigned := entry.value
          | throw (.incomplete s!"unresolved proof metavariable ?p{id}")
        let ts ← ts.mapM term
        let ps ← ps.mapM proof
        let value ← go completeArguments compactScopes (id :: visiting) entry.locals
          entry.context.proofs.length fuel assigned
        -- Filled numerical and predicate entries make successfully resolved arguments complete.
        unless completeArguments ||
            (value.isComplete && ts.all Term.isComplete && ps.all Proof.isComplete) do
          return .mvar id ts ps
        -- Recursive calls check dependencies; argument checks validate their replacements.
        checkProofContext state entry.locals entry.context.proofs.length
          (if compactScopes then assigned else value)
        for t in ts do
          let _ ← renameTerm locals locals 0 t
        let sameTerms := ts.zipIdx.all fun (t, i) => match t with
          | .bvar j => i == j
          | _ => false
        let sameProofs := ps.zipIdx.all fun (p, i) => match p with
          | .hyp j => i == j
          | _ => false
        if sameTerms && sameProofs then return value
        return value.subst (fun i => ts[i]?.getD (.bvar i)) (fun i => ps[i]?.getD (.hyp i))
      | .theoremE n fs ps => return .theoremE n (← fs.mapM term) (← ps.mapM pred)
      | .impIntro n a p => return .impIntro n (← pred a) (← hypothesis p)
      | .impElim p q => return .impElim (← proof p) (← proof q)
      | .andIntro p q => return .andIntro (← proof p) (← proof q)
      | .andLeft a b => return .andLeft (← pred a) (← pred b)
      | .andRight a b => return .andRight (← pred a) (← pred b)
      | .orLeft a b => return .orLeft (← pred a) (← pred b)
      | .orRight a b => return .orRight (← pred a) (← pred b)
      | .orElim a b c => return .orElim (← pred a) (← pred b) (← pred c)
      | .falseElim a => return .falseElim (← pred a)
      | .forallIntro n a p => return .forallIntro n (← pred a) (← numerical p)
      | .forallElim p a => return .forallElim (← proof p) (← term a)
      | .existsIntro a t p => return .existsIntro (← pred a) (← term t) (← proof p)
      | .existsElim a b => return .existsElim (← pred a) (← pred b)
      | .letE n a p q => return .letE n (← pred a) (← proof p) (← hypothesis q)
      | .letTerm n a p => return .letTerm n (← term a) (← proof p)
      | .letPredicate n a p => return .letPredicate n (← pred a) (← proof p)
      | .ascribe a p => return .ascribe (← pred a) (← proof p)
      | .eqRefl => return .eqRefl
      | .eqSubst a => return .eqSubst (← pred a)
      | .succNeZero => return .succNeZero
      | .succInj => return .succInj
      | .lem a => return .lem (← pred a)
      | .induction a => return .induction (← pred a)
      | .hyp i =>
        unless i < hypotheses do throw (.invalid "unbound proof hypothesis")
        pure p
      | .trueIntro => pure p

/-- Proof metavariable references occurring in a proof and its context arguments. -/
def proofMetas : Proof → List Nat
  | .mvar id _ ps => id :: ps.flatMap proofMetas
  | .impIntro _ _ p | .forallIntro _ _ p | .forallElim p _
  | .existsIntro _ _ p | .letTerm _ _ p | .letPredicate _ _ p | .ascribe _ p => proofMetas p
  | .impElim p q | .andIntro p q | .letE _ _ p q => proofMetas p ++ proofMetas q
  | .hyp _ | .trueIntro | .theoremE .. | .eqRefl | .succNeZero | .succInj
  | .andLeft .. | .andRight .. | .orLeft .. | .orRight .. | .orElim ..
  | .falseElim .. | .existsElim .. | .eqSubst .. | .lem _ | .induction _ => []

/-- Assign a proof in its recorded context, checking proof-reference scopes and rejecting
duplicate assignments and cycles.
The caller establishes its formula through elaboration constraints; completion and Core admission
check the resulting proof. -/
def assignProof (depth id : Nat) (value : Proof) : M Unit := do
  let state ← get
  let some entry := state.proofs[id]? | throw (.invalid "unknown proof metavariable")
  unless entry.value.isNone do throw (.invalid "proof metavariable is already assigned")
  match checkProofContext state entry.locals entry.context.proofs.length value with
  | .ok () => pure ()
  | .error error => throw error
  let rec check (path : List Nat) : Nat → Nat → Except Failure Unit
    | 0, _ => throw (.exhausted "proof assignment dependency depth")
    | fuel + 1, dependency => do
      if dependency == id || path.contains dependency then
        throw (.invalid "cyclic proof metavariable assignment")
      let some other := state.proofs[dependency]?
        | throw (.invalid "unknown proof metavariable")
      if let some assigned := other.value then
        for child in proofMetas assigned do check (dependency :: path) fuel child
  for dependency in proofMetas value do
    match check [] depth dependency with
    | .ok () => pure ()
    | .error error => throw error
  set { state with proofs := state.proofs.modify id (fun e => { e with value := some value }) }

/-- Capture a proof in its current context and return a metavariable applied to that context.
The returned occurrence can be placed beneath a binder while the assignment keeps its creation
context for resolving embedded numerical and predicate metavariables. -/
def captureProof (depth : Nat) (type : Predicate) (context : Context) (locals : List Nat)
    (value : Proof) : M Proof := do
  let result ← freshProof type context locals
  let .mvar id _ _ := result | throw (.invalid "expected a proof metavariable")
  assignProof depth id value
  return result

end PRAProver.Surface.Metavariable
