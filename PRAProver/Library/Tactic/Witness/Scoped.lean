module

public meta import PRAProver.Library.Tactic.Witness.Compiler
public meta import PRAProver.Library.Tactic.Induction

/-!
# Scoped extraction of numerical witnesses

Suppose a step of an induction uses `h : ∃ p, Q p`, independently of the induction variable.
One can open `h` before the induction and use the same `p` in every step. Scoped extraction makes
this possible even when `h` occurs inside a helper used by the step proof.

* `extract_scoped_witness step` compiles the proof of `step` with fixed numerical inputs for
  selected closed facts. For `step : ∀ x, ∃ y, R x y` and one such fact `h`, it publishes
  `step.scopedWitness (p : Nat) : Nat → Nat` and
  `step.scopedWitness_correct (p : Nat) : Q p → ∀ x, R x (step.scopedWitness p x)`.
  Both declarations pass through the PRA checker. The function works for any `p` satisfying `Q`.
* `obtain_witness f, hf from step` opens `h` in the current proof and specializes the pair.
  The new goal has an abstract function `f` and `hf : ∀ x, R x (f x)`. When the goal is solved,
  its proof is instantiated with the specialized pair inside the elimination of `h`. Several
  bindings share one opening of each common fact, including across modules.

## Choosing fixed inputs

The default `(params := auto)` examines theorem references in the source proof and its compilable
existential helpers. It reuses previously published ordinary witnesses. For each other reference
the rule is:

```
h(t₁, …, tₙ) : ∃ p, Q p      each tᵢ closed      no predicate arguments      Q quantifier-free
──────────────────────────────────────────────────────────────────────────────────────────────
give the program a fixed input p and its correctness theorem a premise Q p
```

Here `t₁, …, tₙ` are declaration arguments. Closed terms contain no free variables or declaration
parameters. The checker exposes the outer existential by head reduction. Calls to the same theorem
with structurally equal arguments share an input; `h 0` and `h 1` can supply different inputs.
The numbers are ordered by first use in the proof traversal. Each helper takes only what it uses.

`(params := [h₁, h₂])` selects eligible instances of just those named theorems, even when an
ordinary witness exists. Use `[]` to select none. The list filters by theorem name; the actual
arguments still determine which instances are shared. A public pair has one selection policy.

## Using the commands

Inside a `pra` block:

```lean
extract_scoped_witness (params := [fixed]) left_step right_step

theorem both : ∀ x, ∃ a, R x a := by
  obtain_witness
    leftFn, leftCorrect from left_step
    rightFn, rightCorrect from right_step
  intro x
  exact (leftFn x, leftCorrect x)
```

`obtain_witness` accepts source theorems with numerical `∀` binders. For a source with declaration
parameters, apply its generated declarations directly, giving the original parameters first.
-/

public meta section

namespace PRAProver.Library.Tactic.Witness.Scoped

open Lean Elab Command PRAProver.Core PRAProver.Surface
open PRAProver.Library.Tactic.Construction

private structure Ref where
  name : Name
  fs : List PRAProver.Core.Term
  ps : List Predicate
  deriving BEq, Hashable, Inhabited

private partial def closed (depth : Nat) : PRAProver.Core.Term → Bool
  | .bvar i => i < depth
  | .parameter _ => false
  | .lam _ b => closed (depth + 1) b
  | .letE _ v b => closed depth v && closed (depth + 1) b
  | .app a b | .primrec a b => closed depth a && closed depth b
  | .definition _ fs => fs.all (closed depth)
  | .zero | .succ => true

private def refs (p : Proof) (acc : List Ref) : List Ref :=
  match p with
  | .theoremE n fs ps => ⟨n, fs, ps⟩ :: acc
  | .impElim p q | .andIntro p q | .letE _ _ p q => refs p (refs q acc)
  | .forallElim p _ | .forallIntro _ _ p | .impIntro _ _ p | .ascribe _ p
  | .letPredicate _ _ p | .letTerm _ _ p | .existsIntro _ _ p => refs p acc
  | _ => acc

private def replaceRefs (use : Nat → Ref → CommandElabM Proof) (d : Nat)
    (p : Proof) : CommandElabM Proof := do
  match p with
  | .theoremE n fs ps => use d ⟨n, fs, ps⟩
  | .impIntro n a p => return .impIntro n a (← replaceRefs use (d + 1) p)
  | .impElim p q => return .impElim (← replaceRefs use d p) (← replaceRefs use d q)
  | .andIntro p q => return .andIntro (← replaceRefs use d p) (← replaceRefs use d q)
  | .letE n a p q => return .letE n a (← replaceRefs use d p) (← replaceRefs use (d + 1) q)
  | .forallIntro n a p => return .forallIntro n a (← replaceRefs use d p)
  | .forallElim p a => return .forallElim (← replaceRefs use d p) a
  | .existsIntro a t p => return .existsIntro a t (← replaceRefs use d p)
  | .letTerm n t p => return .letTerm n t (← replaceRefs use d p)
  | .letPredicate n a p => return .letPredicate n a (← replaceRefs use d p)
  | .ascribe a p => return .ascribe a (← replaceRefs use d p)
  | p => return p

private structure Rule where
  root : Name
  inputs : List Ref
  deriving Inhabited

private def Rule.program (r : Rule) := r.root ++ `scopedWitness

private def Rule.specification (r : Rule) := r.root ++ `scopedWitness_correct

private inductive Selection where
  | auto
  | only (names : List Name)
  deriving Inhabited, BEq

private structure Plan where
  selection : Selection
  rule : Rule
  deriving Inhabited

-- Only the public pairs and their instructions for opening facts cross module boundaries.
private initialize plans : SimplePersistentEnvExtension Plan (NameMap Plan) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s p => s.insert p.rule.root p
    addImportedFn := fun s => s.foldl (init := {}) fun acc ps =>
      ps.foldl (init := acc) fun acc p => acc.insert p.rule.root p }

private structure Tables where
  eligible : NameMap Bool := {}
  motives : Std.HashMap Ref Predicate := {}
  helpers : NameMap (Option Rule) := {}
  deriving Inhabited

private abbrev CompileM := StateRefT Tables CommandElabM

private def env : CommandElabM PRAProver.Core.Environment :=
  return CoreEnvironment.getState (← getEnv)

private def capture (r : Ref) (d : TheoremDefinition) (selection : Selection) : CompileM Bool := do
  if let .only ns := selection then unless ns.contains r.name do return false
  if (← get).motives.contains r then return true
  unless r.ps.isEmpty && r.fs.all (closed 0) do return false
  let e ← env
  let .ok (.ex motive) := whnfPredicate 1024 e (d.type.instantiate r.fs []) | return false
  let .ok ⟨1, .qf⟩ := inferPredicate 1024 e {} motive | return false
  modify fun s => { s with motives := s.motives.insert r motive }
  return true

private def eligible (d : TheoremDefinition) : CompileM Bool := do
  if let some ok := (← get).eligible.find? d.name then return ok
  let ok ← Compiler.hasExistentialResult { functions := d.functions, predicates := d.predicates }
    d.type
  modify fun s => { s with eligible := s.eligible.insert d.name ok }
  return ok

-- Helpers are memoized for this invocation. A helper built with a different selection can have
-- different arguments. Give internal pairs names under the first new public root of the command.
private partial def compileRule (selection : Selection) (roots : List Name)
    (source : TheoremDefinition) : CompileM (Option Rule) := do
  if let some rule := (← get).helpers.find? source.name then return rule
  let e ← env
  let mut inputs : List Ref := []
  let mut children : NameMap Rule := {}
  let mut captures : Std.HashSet Ref := {}
  let references := if selection == .only [] then [] else (refs source.body []).eraseDups
  for r in references do
    let some (.theoremE d) := e.lookup r.name | continue
    if selection == .auto && (← Compiler.hasPublishedWitness r.name) then continue
    unless ← eligible d do continue
    if ← capture r d selection then
      captures := captures.insert r
      unless inputs.contains r do inputs := inputs ++ [r]
    else if let some child ← compileRule selection roots d then
      children := children.insert r.name child
      for fact in child.inputs do unless inputs.contains fact do inputs := inputs ++ [fact]
  -- A helper with no fixed inputs can follow the ordinary compiler's sharing policy.
  let requested := roots.contains source.name
  if !requested && inputs.isEmpty then
    modify fun s => { s with helpers := s.helpers.insert source.name none }
    return none
  let root := if requested then source.name else roots.head! ++ `scopedWitness ++ source.name
  let rule : Rule := ⟨root, inputs⟩
  let motives := (← get).motives
  let number := fun r => PRAProver.Core.Term.parameter (source.functions.length + inputs.idxOf r)
  let hyp := fun depth r => Proof.hyp (depth + (inputs.length - 1 - inputs.idxOf r))
  let rewrite := fun depth r => do
    if captures.contains r then return .existsIntro motives[r]! (number r) (hyp depth r)
    if let some child := children.find? r.name then
      let some (.theoremE d) := e.lookup r.name | throwError "missing theorem {r.name}"
      let fs := r.fs ++ child.inputs.map number
      let pr := child.inputs.foldl (fun p n => .impElim p (hyp depth n))
        (Proof.theoremE child.specification fs r.ps)
      return ← Compiler.reconstruct (d.type.instantiate r.fs r.ps)
        (applyDefinition child.program [] fs) pr
    return .theoremE r.name r.fs r.ps
  let body ← if inputs.isEmpty then pure source.body else replaceRefs rewrite 0 source.body
  let parameters := source.parameters ++ (List.range inputs.length).map fun i =>
    Parameter.function (Name.mkSimple s!"fixed{i}") 0
  let premises := inputs.map fun r => Predicate.app motives[r]! (number r)
  try
    Compiler.compileWithPremises rule.program rule.specification parameters premises
      source.type body
  catch err => throwError "scoped extraction of `{source.name}`: {err.toMessageData}"
  modify fun s => { s with helpers := s.helpers.insert source.name (some rule) }
  return some rule

declare_syntax_cat witnessParams
syntax ident : witnessParams
syntax "[" ident,* "]" : witnessParams

/-- Compile a scoped program and specification for each theorem, using `params` to choose the
closed facts whose witnesses become fixed inputs. -/
syntax (name := scopedCmd) "extract_scoped_witness" (" (" &"params" " := " witnessParams ")")?
  (ppSpace colGt ident)+ : praDecl

private def sourceTheorem (n : Ident) : CommandElabM TheoremDefinition := withRef n do
  let some (.theoremE d) ← resolveDeclaration? (← env) n.getId |
    throwError "expected a PRA theorem, got `{n}`"
  return d

@[command_elab PRAProver.Surface.praEntry] def elabScoped : CommandElab := fun stx => do
  let `(praDecl| extract_scoped_witness $[(params := $params:witnessParams)]? $names:ident*) :=
    stx[0] | throwUnsupportedSyntax
  let selection ← if let some p := params then
    match p with
    | `(witnessParams| $id:ident) => do
      unless id.getId == `auto do throwErrorAt id "expected `auto` or a list of theorem names"
      pure Selection.auto
    | `(witnessParams| [$ns:ident,*]) => do
      let ds ← ns.getElems.mapM sourceTheorem
      pure (.only ((ds.toList.map (·.name)).eraseDups.mergeSort Name.quickLt))
    | _ => throwUnsupportedSyntax
    else pure Selection.auto
  let mut pending : Array (Ident × TheoremDefinition) := #[]
  for n in names do
    let d ← sourceTheorem n
    if let some p := (plans.getState (← getEnv)).find? d.name then
      unless p.selection == selection do throwErrorAt n
        "`{d.name}.scopedWitness` was already extracted with a different parameter selection"
    else if !pending.any (fun (_, t) => t.name == d.name) then pending := pending.push (n, d)
  let roots := pending.toList.map (·.2.name)
  (do
    for ((n : Ident), d) in pending do withRef n.raw do
      let some rule ← compileRule selection roots d | throwError "missing scoped rule for `{n}`"
      modifyEnv (plans.addEntry · ⟨selection, rule⟩)).run' ({} : Tables)

open PRAProver.Surface.Tactic

declare_syntax_cat scopedBinding
syntax ident ", " ident " from " ident : scopedBinding

/-- Open shared facts once, then bind the specialized programs and their correctness proofs. -/
syntax (name := scopedTac) "obtain_witness" (ppLine colGt scopedBinding)+ : praTactic

/-- Read the compiler's specification with the newly introduced function as the witness.
The quantifiers count the binders between its occurrence and the new function variable. -/
private def abstractSpec (r : Rule) (p : Predicate) : CommandElabM Predicate := do
  let mut p := p
  for _ in r.inputs do
    let .imp _ body := p | throwError "missing fixed premise in `{r.specification}`"
    p := body
  body 0 p
where
  body (depth : Nat) : Predicate → CommandElabM Predicate
    | .all (.lam n p) => return .all (.lam n (← body (depth + 1) p))
    | .imp a b => return .imp a (← body depth b)
    | .app motive witness => do
      let (.definition name _, args) := getAppFnArgs witness | throwError "expected witness call"
      unless name == r.program do throwError "expected `{r.program}` in `{r.specification}`"
      return .app motive (args.foldl .app (.bvar depth))
    | _ => throwError "invalid scoped specification `{r.specification}`"

private abbrev MP := Metavariable.Proof
private abbrev MT := Metavariable.Term
private abbrev MF := Metavariable.Predicate

/-- Wrap a proof in the eliminations of the selected closed facts. Inside the innermost branch,
both the numbers and their checking hypotheses occur in reverse input order. -/
private def openFacts (target : MF) (facts : List (MF × MP)) (proof : MP) : MP :=
  match facts with
  | [] => proof
  | (motive, value) :: rest =>
    let premise : MF := .app motive.shift (.bvar 0)
    let branch := openFacts target.shift rest proof
    .impElim (.impElim (.existsElim motive target) value)
      (.forallIntro `p (.lam `p (.imp premise target.shift)) (.impIntro `hp premise branch))

@[pra_tactic scopedTac] def elabObtain : Tactic := fun stx => do
  let `(praTactic| obtain_witness $bs:scopedBinding*) := stx | throwUnsupportedSyntax
  let rules ← bs.mapM fun b => do
    let `(scopedBinding| $w:ident, $h:ident from $n:ident) := b | throwUnsupportedSyntax
    let d ← sourceTheorem n
    let some plan := (plans.getState (← getEnv)).find? d.name |
      throwErrorAt n "no scoped witness for `{d.name}`; use `extract_scoped_witness` first"
    unless d.parameters.isEmpty do throwErrorAt n
      "`{d.name}` has declaration parameters; apply `{plan.rule.program}` directly"
    return (w, h, plan.rule)
  let reserved := rules.toList.flatMap fun (w, h, _) => [w.getId, h.getId]
  unless reserved.eraseDups.length == reserved.length do
    throwError "give each witness and correctness proof a distinct name"
  let goal ← getGoal
  let inputs := (rules.toList.flatMap (·.2.2.inputs)).eraseDups
  let mut facts : Array (MF × MP) := #[]
  for r in inputs do
    let some (.theoremE d) := goal.environment.lookup r.name | throwError "missing fact `{r.name}`"
    let .ok (.ex motive) := whnfPredicate goal.maxDepth goal.environment
        (d.type.instantiate r.fs r.ps) | throwError "expected existential fact `{r.name}`"
    facts := facts.push (.ofCore motive, .theoremE r.name (r.fs.map Metavariable.Term.ofCore) [])
  let mut bindings := #[]
  let mut functions : List MT := []
  let mut proofs : List MP := []
  for (w, h, rule) in rules do
    let some (.function f) := goal.environment.lookup rule.program | throwError "missing program"
    let some (.theoremE d) := goal.environment.lookup rule.specification |
      throwError "missing specification"
    bindings := bindings.push (.variable w.getId f.arity w)
    bindings := bindings.push (.hypothesis h.getId (.ofCore (← abstractSpec rule d.type)) h)
    let indices := rule.inputs.map fun r => inputs.length - 1 - inputs.idxOf r
    let numbers := indices.map Metavariable.Term.bvar
    functions := .definition rule.program numbers :: functions
    proofs := indices.foldl (fun pr i => .impElim pr (.hyp i))
      (Metavariable.Proof.theoremE rule.specification numbers []) :: proofs
  let ctx ← read
  let old ← mainGoal
  let (next, hole) ← ctx.openGoal old goal.target bindings.toList
  -- Supply the abstract goal's context arguments under the existential binders. The older
  -- variables and hypotheses from the original goal pass through this substitution as well.
  let inner := hole.subst
    (fun i => functions[i]?.getD (.bvar (i - functions.length + inputs.length)))
    (fun i => proofs[i]?.getD (.hyp (i - proofs.length + inputs.length)))
  ctx.assign old (openFacts goal.target facts.toList inner)
  modify fun rest => next :: rest.drop 1

end PRAProver.Library.Tactic.Witness.Scoped
