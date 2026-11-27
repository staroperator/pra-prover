module

public import PRAProver.Library.FOL.PRA.Derive.Evaluation
public meta import PRAProver.Library.Computability.Derive.Command

/-!
# Deriving proofs in first-order PRA

`derive_fol_pra source as target` translates the formula and checked proof body of `source`.
Numerical calls use programs registered by `derive_primrec` on tuples of their arguments.
Derive a shared function once in a module imported by its callers. The command publishes
`target` as a checked PRA theorem of first-order provability. Source induction is replayed
using the first-order induction axiom and a proof that the translated body is quantifier-free.
When a proof calls a theorem with function or predicate arguments, the translator first
abstracts the numerical expressions those arguments use. Calls that differ only in these
numerical expressions can reuse the same checked first-order proof. Under a numerical binder,
replay specializes the proof at the current indices of the captured environments. Source pairing
and its projections use the programs derived from their arithmetic definitions. The first-order
pairing symbol packs program inputs.

Use `derive_fol_pra (public := true) source as target` to use public program indices for
calls whose fixed inputs can be supplied as declaration arguments. Calls that need a
runtime environment use the packed form. If specialization changes the statement, the
command registers the packed proof as `target.internal` and uses it to prove `target`.
Proof replay and registration use the packed form wherever a call needs declaration
parameters.

`register_fol_pra_deriver source as target` checks and registers an existing first-order
proof of the translation of a source theorem with no declaration parameters.

Numerical declaration parameters keep their values. Each function parameter becomes a
program index acting on the tuple of its arguments. For a parameterized function compiled by
`derive_primrec`, the translator supplies the compiled program with its program arguments and
captured values.

## Translation goal

For each checked source proof, the target is a derivation of its translated conclusion in the
first-order theory of PRA, under the translated hypotheses. For a numerical conversion recorded by
the core checker, the target is a first-order proof of equality between the translated endpoints.

In particular, unfolding a definition substitutes the actual parameters into its body. The
translator must prove that evaluating the registered program with those parameters gives the
translation of the instantiated body. At a numerical binder this equation holds for an arbitrary
argument. At a function parameter it compares evaluations at corresponding arguments, with each
callback using its own captured values. The program indices and capture layouts may differ.

The intended construction follows the recorded core step and the compiler's rules for variables,
application, binders and recursion. A missing case should identify the step whose proof could
not be constructed. This substitution law is a proof obligation of `derive_fol_pra`.
-/

meta section

namespace PRAProver.Library.FOL.PRA.Derive.Command

open Lean hiding Term
open Lean.Elab.Command
open PRAProver.Core PRAProver.Surface
open PRAProver.Library.Tactic.Construction
open PRAProver.Library.Computability.Derive.Command
  (captureProgramFunction prepareProgramCall prepareProgramFunction prepareProgramRecursion
    programHead)
open PRAProver.Library.FOL.DSL
open PRAProver.Library.FOL.PRA.Derive.Evaluation
  (evalTerm zeroTerm succTerm mkPair instanceEquality sourceApplication specializeTerm)

private structure Translation where
  depth : Nat
  target : Name
  parameters : List Parameter := []
  sourceFunctions : List Arity := []
  contextual : Bool := false
  -- Callback bodies can be replayed at translated arguments in a different object context.
  inputSlots : List Term := []
  objectLocals : Option Nat := none

private def Translation.parameterTerms (translation : Translation) : List Term :=
  (List.range translation.parameters.length).map Term.parameter

private def Translation.sourceContext (translation : Translation) : Core.Context :=
  { functions := translation.sourceFunctions }

private abbrev DeriveM := ReaderT Translation CommandElabM

private abbrev TheoremCall := Name × Name × List Term × List Predicate

private initialize translatedTheorems :
    SimplePersistentEnvExtension (TheoremCall × Name) (Std.HashMap TheoremCall Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun names (source, target) => names.insert source target
    addImportedFn := fun modules => Id.run do
      let mut names := {}
      for entries in modules do
        for (source, target) in entries do
          names := names.insert source target
      return names
  }

private initialize contextualTheorems :
    SimplePersistentEnvExtension (Name × Name) (Std.HashMap Name Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun names (source, target) => names.insert source target
    addImportedFn := fun modules => Id.run do
      let mut names := {}
      for entries in modules do
        for (source, target) in entries do
          names := names.insert source target
      return names
  }

private initialize parameterizedTheorems :
    SimplePersistentEnvExtension (Name × Name) (Std.HashMap Name Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun names (source, target) => names.insert source target
    addImportedFn := fun modules => Id.run do
      let mut names := {}
      for entries in modules do
        for (source, target) in entries do
          names := names.insert source target
      return names
  }

private def checked {α : Type} (result : CheckResult α) : DeriveM α :=
  match result with
  | .ok value => pure value
  | .error error => throwError "{error.message}"

private def language : Term := applyDefinition `FOL.PRA.language

private def axioms : Term := applyDefinition `FOL.PRA.isAxiom

private def var (i : Nat) : Term := applyDefinition `FOL.Term.var [language, numeral i]

private def equal (a b : Term) : Term := applyDefinition `FOL.Formula.equal [language, a, b]

private def imp (a b : Term) : Term := applyDefinition `FOL.Formula.imp [a, b]

private def all (a : Term) : Term := applyDefinition `FOL.Formula.all [a]

private def falsum : Term := applyDefinition `FOL.Formula.falsum

private def neg (a : Term) : Term := imp a falsum

private def conj (a b : Term) : Term := neg (imp a (neg b))

private def ex (a : Term) : Term := neg (all (neg a))

private def pack : List Term → Term
  | [] => zeroTerm
  | [a] => a
  | a :: rest => mkPair a (pack rest)

private def environment : DeriveM Core.Environment := return CoreEnvironment.getState (← getEnv)

private def whnf (a : Predicate) : DeriveM Predicate := do
  checked (whnfPredicate (← read).depth (← environment) a)

private def Translation.callback (translation : Translation) (i : Nat) : Option (Term × Term) := do
  guard ((translation.sourceFunctions[i]?.getD 0) > 0)
  if translation.contextual then
    return (.parameter i, .parameter (translation.sourceFunctions.length + i))
  let code := applyDefinition `Primrec.Code.comp [.parameter i, applyDefinition `Primrec.Code.right]
  return (code, .zero)

private partial def encodeTerm (locals : Nat) (term : Term) : DeriveM Term := do
  let (head, args) := getAppFnArgs (programHead term)
  match head, args with
  | .letE _ value body, _ => encodeTerm locals (args.foldl .app (body.subst0 value))
  | .bvar i, [] =>
    unless i < locals do throwError "unbound numerical variable {i}"
    return ((← read).inputSlots[i]?).getD (var i)
  | .parameter i, _ =>
    let translation ← read
    if translation.contextual && translation.sourceFunctions.length ≤ i && args.isEmpty then
      return var ((translation.objectLocals.getD locals) + i - translation.sourceFunctions.length)
    let some arity := translation.sourceFunctions[i]? |
      throwError "unknown function parameter {i}"
    unless args.length == arity do
      throwError "function parameter {i} needs all its arguments"
    if arity == 0 then
      return evalTerm (applyDefinition `Primrec.Code.const [.parameter i]) zeroTerm
    let argument := pack (← args.mapM (encodeTerm locals))
    return evalTerm (.parameter i) (if translation.contextual then
      mkPair (var ((translation.objectLocals.getD locals) + i)) argument else argument)
  | .zero, [] => return zeroTerm
  | .succ, [a] => return succTerm (← encodeTerm locals a)
  | .primrec base step, [n] =>
    let (code, inputs) ← prepareProgramRecursion base step (← read).callback
    let fixed := pack (← inputs.mapM fun field =>
      field.foldM (encodeTerm locals) (fun x y => pure (mkPair x y)))
    return evalTerm code (mkPair fixed (← encodeTerm locals n))
  | .definition name actuals, _ => do
    let (code, input) ← prepareProgramCall name actuals args (← read).callback
    return evalTerm code (← input.foldM (encodeTerm locals) (fun a b => pure (mkPair a b)))
  | _, _ => throwError "unsupported numerical expression {repr term}"

private def openMotive (a : Predicate) : Predicate := .app a.shift (.bvar 0)

private inductive FormulaSyntax where
  | falsum
  | equal (locals : Nat) (lhs rhs lhsCode rhsCode : Term)
  | imp (lhs rhs : FormulaSyntax)
  | all (body : FormulaSyntax)

private def FormulaSyntax.code : FormulaSyntax → Term
  | .falsum => Command.falsum
  | .equal _ _ _ a b => Command.equal a b
  | .imp a b => Command.imp a.code b.code
  | .all a => Command.all a.code

private partial def quoteFormula (locals : Nat) (formula : Predicate) :
    DeriveM FormulaSyntax := do
  match ← whnf formula with
  | .false => return .falsum
  | .true => return .imp .falsum .falsum
  | .equal a b => return .equal locals a b (← encodeTerm locals a) (← encodeTerm locals b)
  | .imp a b => return .imp (← quoteFormula locals a) (← quoteFormula locals b)
  | .and a b => return .imp (.imp (← quoteFormula locals a)
      (.imp (← quoteFormula locals b) .falsum)) .falsum
  | .or a b => return .imp (.imp (← quoteFormula locals a) .falsum) (← quoteFormula locals b)
  | .all a => return .all (← quoteFormula (locals + 1) (openMotive a))
  | .ex a =>
    let body ← quoteFormula (locals + 1) (openMotive a)
    return .imp (.all (.imp body .falsum)) .falsum
  | a => throwError "unsupported formula {repr a}"

private def encodeFormula (locals : Nat) (formula : Predicate) : DeriveM Term :=
  return (← quoteFormula locals formula).code

private def rule (name : Name) (args : List Term) (premises : List Proof := []) : Proof :=
  applyTheorem name args [language, axioms] premises

private def lemma (name : Name) (args : List Term) (premises : List Proof := []) : Proof :=
  applyTheorem name [] (language :: axioms :: args) premises

private def lift (Γ a : Term) (p : Proof) : Proof :=
  rule `FOL.Sequent.lift [Γ, a] [p]

private def mp (Γ a b : Term) (p q : Proof) : Proof :=
  rule `FOL.Sequent.mp [Γ, a, b] [p, q]

private def introduce (Γ a b : Term) (p : Proof) : Proof :=
  rule `FOL.Sequent.imp_intro [Γ, a, b] [p]

private def shiftFormula (a : Term) : Term := applyDefinition `FOL.Formula.shift [language, a]

private def instantiateFormula (a x : Term) : Term :=
  applyDefinition `FOL.Formula.instantiate [language, a, x]

private def transportCode (Γ a b : Term) (h p : Proof) : Proof :=
  let motive := Predicate.lam `A (sequent language axioms Γ.shift (.bvar 0))
  .impElim (.impElim (.forallElim (.forallElim (.eqSubst motive) a) b) h) p

private def convertCode (Γ a b : Term) (p : Proof) : DeriveM Proof := do
  if a == b then return p
  return transportCode Γ a b (← calculateClosedEquality a b) p

private def convertInstance (Γ body arg target : Term) (p : Proof)
    (reverse : Bool := false) : DeriveM Proof := do
  let source := instantiateFormula body arg
  let equality ← instanceEquality body arg target
  if reverse then
    return transportCode Γ target source (mkEqSymm source target equality) p
  return transportCode Γ source target equality p

private def reverseEquation (eq : Evaluation.Equation) : Evaluation.Equation :=
  ⟨eq.rhs, eq.lhs, eq.proof?.map fun h =>
    applyTheorem `FOL.PRA.Evaluation.symm [eq.lhs, eq.rhs] [] [h]⟩

-- Read the argument comparisons from the application spine. At numerical arity these
-- arguments translate to first-order terms. Callback comparisons act on program evaluations.
private def argumentConversions (a b : Term) (path : TermConversion) :
    List (Term × Term × TermConversion) :=
  match a, b, path with
  | .app f u, .app g v, .pair h p => (u, v, p) :: argumentConversions f g h
  | .primrec u _, .primrec v _, .pair h _ => [(u, v, h)]
  | _, _, _ => []

private partial def replaySteps (locals : Nat) (t : Term) (args : List Term)
    (h : HeadReduction) : DeriveM (Term × Evaluation.Equation) := do
  let encode := fun x => encodeTerm locals (args.foldl .app x)
  match h with
  | .refl => return (t, Evaluation.unchanged (← encode t))
  | .trans p q =>
    let (u, a) ← replaySteps locals t args p
    let (v, b) ← replaySteps locals u args q
    return (v, a.thenEq b)
  | .function p =>
    let .app f a := t | throwError "expected an application around a function contraction"
    let (g, h) ← replaySteps locals f (a :: args) p
    return (.app g a, h)
  | .counter p =>
    let .app (.primrec b s) a := t | throwError "expected a recursion around a counter contraction"
    let (n, h) ← replaySteps locals a [] p
    let next := Term.app (.primrec b s) n
    let some r := sourceApplication (← environment) (← encode t) (← encode next) [h] |
      throwError "the compiled recursion does not expose its counter"
    return (next, r)
  | .unfold =>
    let .definition name fs := t | throwError "expected a definition at the recorded unfold"
    let some (.function d) := (← environment).lookup name | throwError "missing definition {name}"
    let next := d.body.instantiate fs
    let config ← read
    let (head, ordinary) := getAppFnArgs (programHead (args.foldl .app t))
    let .definition _ actuals := head | throwError "missing program for {name}"
    let (code, fields) ← prepareProgramCall name actuals ordinary config.callback
    let input ← fields.foldM (encodeTerm locals) (fun a b => pure (mkPair a b))
    let y ← encode next
    if evalTerm code input == y then return (next, Evaluation.unchanged y)
    try
      return (next, ← Evaluation.unfoldEquation code input y)
    catch e =>
      if e.isInterrupt then throw e
      throwError "unfolding {repr t} at {repr args}: {e.toMessageData}"
  | _ =>
    let next ← match t, h with
      | .app (.lam _ b) a, .beta | .letE _ a b, .letTerm => pure (b.subst0 a)
      | .app (.primrec b _) .zero, .recZero => pure b
      | .app (.primrec b s) (.app .succ i), .recSucc =>
        pure (.app (.app s i) (.app (.primrec b s) i))
      | _, _ => throwError "invalid recorded contraction at {repr t}"
    let x ← encode t
    let y ← encode next
    if x == y then return (next, Evaluation.unchanged x)
    let q ← try Evaluation.recordedEquation x y h catch e =>
      if e.isInterrupt then throw e
      throwError "recorded {repr h} from {repr t} to {repr next}: {e.toMessageData}"
    return (next, q)

private def replaySide (locals : Nat) (a b x : Term) (h : HeadReduction) :
    DeriveM Evaluation.Equation := do
  let (u, result) ← replaySteps locals a [] h
  unless u == b && result.lhs == x do throwError "the recorded reduction has different endpoints"
  return result

private def parameterConversions (a b : Term) (path : TermConversion) :
    List (Term × Term × TermConversion) :=
  match a, b, path with
  | .app f _, .app g _, .pair h _ => parameterConversions f g h
  | .definition _ fs, .definition _ gs, h =>
    let rec params : List Term → List Term → TermConversion → List (Term × Term × TermConversion)
      | f :: fs, g :: gs, .pair p q => (f, g, p) :: params fs gs q
      | _, _, _ => []
    params fs gs h
  | _, _, _ => []

-- Opening a function comparison places the recorded intermediate terms under a new binder.
private def weakenConversion (cutoff : Nat) : TermConversion → TermConversion
  | .same => .same
  | .pair h p => .pair (weakenConversion cutoff h) (weakenConversion cutoff p)
  | .reduce u v l r h => .reduce (u.shift 1 cutoff) (v.shift 1 cutoff) l r
      (weakenConversion cutoff h)
  | .eta p => .eta (weakenConversion (cutoff + 1) p)
  | .lambda p => .lambda (weakenConversion (cutoff + 1) p)

private def functionBody : Nat → Term → Term → TermConversion → Term × Term × TermConversion
  | 0, f, g, h => (f, g, h)
  | k + 1, .lam _ l, .lam _ r, .lambda p => functionBody k l r p
  | k + 1, f, g, .eta p =>
    functionBody k (.app f.shift (.bvar 0)) (.app g.shift (.bvar 0)) p
  | k + 1, f, g, h =>
    functionBody k (.app f.shift (.bvar 0)) (.app g.shift (.bvar 0))
      (.pair (weakenConversion 0 h) .same)

private def underInputs (locals depth : Nat) (inputs : List Term) (action : DeriveM α) :
    DeriveM α := do
  let config ← read
  let outer ← (List.range locals).mapM fun i =>
    Evaluation.underBinders depth (config.inputSlots[i]?.getD (var i))
  action.run { config with
    inputSlots := inputs.reverse ++ outer
    objectLocals := some (config.objectLocals.getD locals + depth) }

private partial def replayConversion (locals : Nat) (a b x y : Term) (path : TermConversion) :
    DeriveM Evaluation.Equation := do
  if x == y then return Evaluation.unchanged x
  match path with
  | .reduce u v l r rest =>
    let lhs ← replaySide locals a u x l
    let rhs ← replaySide locals b v y r
    let middle ← replayConversion locals u v lhs.rhs rhs.rhs rest
    return (lhs.thenEq middle).thenEq (reverseEquation rhs)
  | .pair .. =>
    if let (.app (.primrec u f) n, .app (.primrec v g) m, .pair (.pair hb hs) hn) :=
        (a, b, path) then
      let base ← replayConversion locals u v (← encodeTerm locals u) (← encodeTerm locals v) hb
      let count ← replayConversion locals n m (← encodeTerm locals n) (← encodeTerm locals m) hn
      let config ← read
      let action : DeriveM Evaluation.Equation := do
        let (l, r, p) := functionBody 2 f g hs
        underInputs locals 2 [var 1, var 0] do
          replayConversion (locals + 2) l r (← encodeTerm (locals + 2) l)
            (← encodeTerm (locals + 2) r) p
      return ← Evaluation.compareRecursor x y base count (action.run config)
    let mut args := []
    for (u, v, h) in argumentConversions a b path do
      let eq ← replayConversion locals u v (← encodeTerm locals u) (← encodeTerm locals v) h
      args := eq :: args
    let parameters := parameterConversions a b path
    let mut rules := []
    if !parameters.isEmpty then
      let .definition name _ := (getAppFnArgs a).1 | throwError "expected a named call"
      let some (.function decl) := (← environment).lookup name |
        throwError "unknown function {name}"
      for ((f, g, h), arity) in parameters.zip decl.functions do
        if arity == 0 then
          let eq ← replayConversion locals f g (← encodeTerm locals f) (← encodeTerm locals g) h
          args := eq :: args
          continue
        if h matches .same then continue
        let (l, r, p) := functionBody arity f g h
        let config ← read
        let (lf, lc) ← prepareProgramFunction arity f config.callback
        let (rf, rc) ← prepareProgramFunction arity g config.callback
        let frame (input : PRAProver.Library.Computability.Derive.Command.ProgramInput) := do
          let term ← input.foldM (encodeTerm locals) (fun x y => pure (mkPair x y))
          Evaluation.captureFrame term
        let atInput := fun depth left right arg => do
          let inputs ← Evaluation.ordinaryInputs arity arg
          let action := underInputs locals depth inputs do
            replayConversion (locals + arity) l r (← encodeTerm (locals + arity) l)
              (← encodeTerm (locals + arity) r) p
          let body ← action.run config
          Evaluation.callbackInstance lf rf left right arg body
        let rule : Evaluation.CallbackComparison := ⟨lf, rf, ← frame lc, ← frame rc, atInput⟩
        rules := rule :: rules
    -- Align the numerical inputs before comparing the two sets of captured callbacks.
    if let ((.definition name fs, _), (.definition _ gs, rightArgs)) :=
        (getAppFnArgs a, getAppFnArgs b) then
      let some (.function decl) := (← environment).lookup name |
        throwError "missing definition {name}"
      let actuals := (decl.functions.zip (fs.zip gs)).map fun (k, f, g) => if k == 0 then g else f
      let intermediate ← encodeTerm locals (rightArgs.foldl .app (.definition name actuals))
      let some numeric := sourceApplication (← environment) x intermediate args |
        throwError "numerical inputs of {name} do not match the core comparison"
      return numeric.thenEq (← Evaluation.compareCall intermediate y rules)
    -- A parameter application (or successor) uses its numerical inputs directly. Transport
    -- their recorded equations before any routing changes the syntax of those inputs.
    let some numeric := sourceApplication (← environment) x y args |
      throwError "cannot lift the recorded argument comparisons from {repr a} to {repr b}"
    return numeric
  | .same =>
    Evaluation.compareCall x y
  | _ => throwError "expected a numerical conversion"

private def sourceTermEquality (locals : Nat) (a b x y : Term) : DeriveM Proof := do
  if x == y then return (Evaluation.unchanged x).proof
  let depth := (← read).depth
  let some path ← checked (termConversion depth (← environment) 0 a b) |
    throwError "the source terms are not definitionally equal"
  try
    return (← replayConversion locals a b x y path).proof
  catch e =>
    if e.isInterrupt then throw e
    throwError "replaying the comparison of {repr a} and {repr b}: {e.toMessageData}"

private abbrev TermEquality := Nat → Term → Term → Term → Term → DeriveM Proof

-- Build the object implication, carrying the source terms down to each equality atom.
private partial def formulaImplication (a b : FormulaSyntax)
    (termEquality : TermEquality := sourceTermEquality) : DeriveM Proof := do
  let A := a.code
  let B := b.code
  if A == B then return lemma `FOL.Provable.imp_refl [A]
  match a, b with
  | .equal locals xa ya x y, .equal _ ua va u v =>
    let Γ := consList A emptyList
    let h := rule `FOL.Sequent.head [emptyList, A]
    let hu ← termEquality locals ua xa u x
    let hv ← termEquality locals ya va y v
    let chain (s t w : Term) (p q : Proof) : Proof :=
      let trans := imp (equal s t) (imp (equal t w) (equal s w))
      mp Γ (equal t w) (equal s w)
        (mp Γ (equal s t) (imp (equal t w) (equal s w))
          (lift Γ trans (lemma `FOL.Provable.transitivity [s, t, w])) p) q
    let h := chain u x y (lift Γ (equal u x) hu) h
    let h := chain u y v h (lift Γ (equal y v) hv)
    return ofSequent language axioms emptyList (imp A B) (introduce emptyList A B h)
  | .imp p q, .imp r s =>
    let P := p.code
    let Q := q.code
    let R := r.code
    let S := s.code
    let context := consList A emptyList
    let Γ := consList R context
    let hp := rule `FOL.Sequent.head [context, R]
    let ha := rule `FOL.Sequent.weaken [context, R, A] [rule `FOL.Sequent.head [emptyList, A]]
    let hp := mp Γ R P (lift Γ (imp R P) (← formulaImplication r p termEquality)) hp
    let hq := mp Γ P Q ha hp
    let hs := mp Γ Q S (lift Γ (imp Q S) (← formulaImplication q s termEquality)) hq
    let h := introduce emptyList A B (introduce context R S hs)
    return ofSequent language axioms emptyList (imp A B) h
  | .all p, .all q =>
    return lemma `FOL.Provable.all_mono [p.code, q.code] [← formulaImplication p q termEquality]
  | _, _ => throwError "source conversion gives different first-order formula shapes"

private structure Scope where
  locals : Nat := 0
  Γ : Term := emptyList

private def Scope.encode (s : Scope) (a : Predicate) : DeriveM Term := encodeFormula s.locals a

-- Shift the written list once. Hypothesis accesses can then use its quoted formulas directly.
private partial def shiftAssumptions (Γ : Term) : DeriveM (Term × Proof) := do
  let f := Term.app (.definition `FOL.Formula.shift []) language
  match getAppFnArgs Γ with
  | (.definition `Sequence.cons [], [a, rest]) =>
    let (b, head) ← QuotedSubstitution.shift a
    let (tail, tailProof) ← shiftAssumptions rest
    let source := shiftedList language Γ
    let middle := consList (.app f a) (shiftedList language rest)
    let target := consList b tail
    let unfold := applyTheorem `Sequence.map_cons [a, rest] [f]
    let congruence := applyTheorem `eq_congr₂ [.app f a, shiftedList language rest, b, tail]
      [.definition `Sequence.cons []] [head, tailProof]
    return (target, mkEqTrans source middle target unfold congruence)
  | _ =>
    unless Γ == emptyList do throwError "expected a written list of local assumptions"
    return (emptyList, applyTheorem `Sequence.map_nil [] [f])

private def Scope.bind (s : Scope) : DeriveM Scope := do
  let (Γ, _) ← shiftAssumptions s.Γ
  return ⟨s.locals + 1, Γ⟩

private def Scope.assume (s : Scope) (a : Term) : Scope := { s with Γ := consList a s.Γ }

private def generalize (s : Scope) (a : Term) (p : Proof) : DeriveM Proof := do
  if s.Γ == emptyList then
    let h := ofSequent language axioms emptyList a p
    return asSequent language axioms emptyList (all a) (rule `FOL.Provable.gen [a] [h])
  let shifted := shiftedList language s.Γ
  let (actual, h) ← shiftAssumptions s.Γ
  let p := transportList language axioms actual shifted a (mkEqSymm shifted actual h) p
  return rule `FOL.Sequent.all_intro [s.Γ, a] [p]

-- Apply equality substitution to the two supplied terms. This also handles a source rewrite
-- whose proof immediately specializes both quantifiers of the substitution rule.
private def substituteAt (s : Scope) (motive : Predicate) (fromTerm toTerm : Term) :
    DeriveM (Term × Proof) := do
  let x ← encodeTerm s.locals fromTerm
  let y ← encodeTerm s.locals toTerm
  let a ← encodeFormula (s.locals + 1) (openMotive motive)
  let atX := instantiateFormula a x
  let atY := instantiateFormula a y
  let forward := imp atX atY
  let backward := imp atY atX
  let e := equal x y
  let Γ := consList e s.Γ
  let equivalence := conj forward backward
  let h := lemma `FOL.Equality.substitution_congruence [x, y, a]
  let h := mp Γ e equivalence (lift Γ (imp e equivalence) h)
    (rule `FOL.Sequent.head [s.Γ, e])
  let h := rule `FOL.Sequent.conj_left [Γ, forward, backward] [h]
  let lhs ← s.encode (.app motive fromTerm)
  let rhs ← s.encode (.app motive toTerm)
  let h₁ ← instanceEquality a x lhs
  let h₂ ← instanceEquality a y rhs
  let equality := applyTheorem `eq_congr₂ [atX, atY, lhs, rhs]
    [.definition `FOL.Formula.imp []] [h₁, h₂]
  let h := transportCode Γ forward (imp lhs rhs) equality h
  let body := imp e (imp lhs rhs)
  return (body, introduce s.Γ e (imp lhs rhs) h)

private def substituteEquality (s : Scope) (motive : Predicate) : DeriveM Proof := do
  let next ← s.bind
  let inner ← next.bind
  let (body, h) ← substituteAt inner (motive.shift 2) (.bvar 1) (.bvar 0)
  generalize s (all body) (← generalize next body h)

private def eliminateExists (s : Scope) (motive target : Predicate) : DeriveM Proof := do
  let a ← encodeFormula (s.locals + 1) (openMotive motive)
  let b ← s.encode target
  let bShift ← encodeFormula (s.locals + 1) target.shift
  let existential := ex a
  let branch := all (imp a bShift)
  let context := consList existential s.Γ
  let Γ := consList branch context
  let witness := rule `FOL.Sequent.head [s.Γ, existential]
  let witness := rule `FOL.Sequent.weaken [context, branch, existential] [witness]
  let branchProof := rule `FOL.Sequent.head [context, branch]
  let (shifted, shiftProof) ← QuotedSubstitution.shift b
  let target := all (imp a (shiftFormula b))
  let branchProof ← if shifted == bShift then
      let motive : Term := .lam `B (all (imp a.shift (.bvar 0)))
      let equality := applyTheorem `eq_congr [bShift, shiftFormula b] [motive]
        [mkEqSymm (shiftFormula b) bShift shiftProof]
      pure (transportCode Γ branch target equality branchProof)
    else convertCode Γ branch target branchProof
  let conclusion := rule `FOL.Sequent.ex_elim_of_all_imp [Γ, a, b] [witness, branchProof]
  return introduce s.Γ existential (imp branch b) (introduce context branch b conclusion)

-- The test examines formula constructors, so the guard works for symbolic program indices.
private partial def quantifierFree (body : Term) : DeriveM Proof := do
  match getAppFnArgs body with
  | (.definition `FOL.Formula.falsum [], []) =>
    return applyTheorem `FOL.Formula.isQuantifierFree_falsum [language]
  | (.definition `FOL.Formula.equal [], [_, a, b]) =>
    return applyTheorem `FOL.Formula.isQuantifierFree_equal [language, a, b]
  | (.definition `FOL.Formula.imp [], [a, b]) =>
    let test := fun f => applyDefinition `FOL.Formula.isQuantifierFree [language, f]
    let ha ← quantifierFree a
    let hb ← quantifierFree b
    let band := applyDefinition `band [test a, test b]
    let unfold := applyTheorem `FOL.Formula.isQuantifierFree_imp [language, a, b]
    let guard := applyTheorem `band_eq_one_of_eq_one [test a, test b] [] [ha, hb]
    return mkEqTrans (test body) band (numeral 1) unfold guard
  | _ => throwError "expected a quantifier-free formula in source induction"

private def replayInduction (s : Scope) (motive type : Predicate) : DeriveM Proof := do
  let body ← encodeFormula (s.locals + 1) (openMotive motive)
  let guard ← quantifierFree body
  let (base, hb) ← QuotedSubstitution.substituteQF body zeroTerm 0
  let (successor, hs) ← QuotedSubstitution.substituteQF body (succTerm (var 0)) 1
  let schema := imp base (imp (all (imp body successor)) (all body))
  let proof := applyTheorem `FOL.PRA.QuotedSubstitution.induction_instances [body, base, successor]
    [] [guard, hb, hs]
  convertCode s.Γ schema (← s.encode type) (lift s.Γ schema proof)

private partial def proveUniversalEquation (s : Scope) (formula : Predicate)
    (termEquality : TermEquality := sourceTermEquality) : DeriveM Proof := do
  match ← whnf formula with
  | .all motive =>
    let inner ← s.bind
    let body := openMotive motive
    let p ← proveUniversalEquation inner body termEquality
    generalize s (← inner.encode body) p
  | .equal a b =>
    let x ← encodeTerm s.locals a
    let y ← encodeTerm s.locals b
    return lift s.Γ (equal x y) (← termEquality s.locals a b x y)
  | _ => throwError "a projection theorem must state a universally quantified equation"

private structure Replay where
  formula : Predicate
  proof : Proof

private def Replay.convert (s : Scope) (r : Replay) (target : Predicate) : DeriveM Proof := do
  let a ← quoteFormula s.locals r.formula
  let b ← quoteFormula s.locals target
  let A := a.code
  let B := b.code
  if A == B then return r.proof
  let h ← formulaImplication a b
  return mp s.Γ A B (lift s.Γ (imp A B) h) r.proof

-- A translation with declaration parameters can serve a call directly when
-- substituting those parameters produces the same packed first-order statement.
private def reuseParameterized (s : Scope) (name : Name) (functions : List Term)
    (formula : Predicate) : DeriveM (Option Proof) := do
  let some target := (parameterizedTheorems.getState (← getEnv))[name]? | return none
  let some (.theoremE packed) := (← environment).lookup target | return none
  let some args := functions.mapM (fun
    | .parameter i => some (Term.parameter i)
    | _ => none) | return none
  let code ← s.encode formula
  unless packed.type.instantiate args [] == provable language axioms code do return none
  return some (lift s.Γ code (applyTheorem target [] args))

private def isReflexivityProof : Proof → Bool
  | .ascribe _ p | .forallIntro _ _ p | .forallElim p _ => isReflexivityProof p
  | .eqRefl => true
  | _ => false

private def appliedTheorem? : Proof → Option Name
  | .forallElim p _ => appliedTheorem? p
  | .theoremE name _ _ => some name
  | _ => none

-- Use the same capture boundaries as the compiler, so callback code remains fixed
-- when the local numerical expressions are supplied to the first-order theorem.
private def abstractArguments (locals : Nat) (arities : List Arity)
    (functions : List Term) (predicates : List Predicate) :
    DeriveM (List Term × List Predicate × List Term) := do
  let mut captures := #[]
  let mut actuals := #[]
  for (arity, f) in arities.zip functions do
    if f == f.shift then
      actuals := actuals.push f
    else
      let (body, values) ← captureProgramFunction arity f
      let mut slots := #[]
      for value in values do
        let i := captures.toList.idxOf value
        if i == captures.size then captures := captures.push value
        slots := slots.push i
      actuals := actuals.push (body.rename fun i => slots[i]!)
  let mut slots := #[]
  for i in List.range locals do
    if predicates.any (fun p => p.shift 1 i != p.shift 1 (i + 1)) then
      let t := Term.bvar i
      let slot := captures.toList.idxOf t
      if slot == captures.size then captures := captures.push t
      slots := slots.push (i, slot)
  let rename := fun i => (slots.find? (·.1 == i)).map (·.2) |>.getD i
  return (actuals.toList, predicates.map (·.rename rename), captures.toList)

private partial def FormulaSyntax.withCode (a : FormulaSyntax) (code : Term) :
    Option FormulaSyntax := do
  match a, getAppFnArgs code with
  | .falsum, (.definition `FOL.Formula.falsum [], []) => return .falsum
  | .equal n lhs rhs _ _, (.definition `FOL.Formula.equal [], [_, x, y]) =>
    return .equal n lhs rhs x y
  | .imp p q, (.definition `FOL.Formula.imp [], [pCode, qCode]) =>
    return .imp (← p.withCode pCode) (← q.withCode qCode)
  | .all p, (.definition `FOL.Formula.all [], [pCode]) => return .all (← p.withCode pCode)
  | _, _ => none

-- A contextual theorem proved at depth zero has free variables for its callback environments.
-- Generalize them before moving its proof under the caller's numerical binders.
private def liftDependency (s : Scope) (translation : Translation) (statement : Predicate)
    (code : Term) (proof : Proof) : DeriveM Proof := do
  if !translation.contextual || s.locals == 0 then return lift s.Γ code proof
  let expected ← (encodeFormula s.locals statement).run translation
  if code == expected then return lift s.Γ code proof
  let mut result := code
  let mut h := proof
  for _ in translation.sourceFunctions do
    h := rule `FOL.Provable.gen [result] [h]
    result := all result
  h := lift s.Γ result h
  for i in (List.range translation.sourceFunctions.length).reverse do
    let (.definition `FOL.Formula.all [], [body]) := getAppFnArgs result |
      throwError "expected a generalized callback environment"
    let x := var (s.locals + i)
    let (next, eq) ← QuotedSubstitution.instantiate body x
    h := rule `FOL.Sequent.all_elim [s.Γ, body, x] [h]
    h := transportCode s.Γ (instantiateFormula body x) next eq h
    result := next
  unless result == expected do throwError "callback environments differ after specialization"
  return h

private partial def replay (s : Scope) (context : Core.Context) (p : Proof)
    (expected : Option Predicate := none) : DeriveM Replay := do
  let infer : DeriveM Predicate := do
    checked (inferProof (← read).depth (← environment) context p)
  let leaf (name : Name) (args : List Term) : DeriveM Replay := do
    let a ← infer
    return ⟨a, lift s.Γ (← s.encode a) (lemma name args)⟩
  match p with
  | .hyp i =>
    let a ← infer
    let some (code, h) := assumptionProof language axioms s.Γ i |
      throwError "missing source hypothesis {i}"
    return ⟨a, ← convertCode s.Γ code (← s.encode a) h⟩
  | .trueIntro => leaf `FOL.Provable.imp_refl [falsum]
  | .impIntro _ a body =>
    let A ← s.encode a
    let conclusion ← match expected with
      | some expected =>
        match ← whnf expected with
        | .imp _ b => pure (some b)
        | _ => pure none
      | none => pure none
    let inner := context.pushProof a
    let child ← replay (s.assume A) inner body conclusion
    return ⟨.imp a child.formula, introduce s.Γ A (← s.encode child.formula) child.proof⟩
  | .impElim f a =>
    let fn ← replay s context f
    let .imp lhs rhs ← whnf fn.formula | throwError "expected a source implication"
    let arg ← replay s context a
    let h ← arg.convert s lhs
    return ⟨rhs, mp s.Γ (← s.encode lhs) (← s.encode rhs) fn.proof h⟩
  | .andIntro a b =>
    let lhs ← replay s context a
    let rhs ← replay s context b
    return ⟨.and lhs.formula rhs.formula, rule `FOL.Sequent.conj_intro
      [s.Γ, ← s.encode lhs.formula, ← s.encode rhs.formula] [lhs.proof, rhs.proof]⟩
  | .andLeft a b => leaf `FOL.Provable.conj_left [← s.encode a, ← s.encode b]
  | .andRight a b => leaf `FOL.Provable.conj_right [← s.encode a, ← s.encode b]
  | .orLeft a b => leaf `FOL.Provable.disj_intro_left [← s.encode a, ← s.encode b]
  | .orRight a b => leaf `FOL.Provable.disj_intro_right [← s.encode a, ← s.encode b]
  | .orElim a b c => leaf `FOL.Provable.disj_elim [← s.encode a, ← s.encode b, ← s.encode c]
  | .falseElim a => leaf `FOL.Provable.falsum_imp [← s.encode a]
  | .lem a => leaf `FOL.Provable.imp_refl [neg (← s.encode a)]
  | .forallIntro _ motive body =>
    let inner ← s.bind
    let a := openMotive motive
    let locals := context.pushLocal 0
    let child ← replay inner locals body (some a)
    let h ← child.convert inner a
    return ⟨.all motive, ← generalize s (← inner.encode a) h⟩
  | .forallElim (.forallElim (.theoremE `eq_symm [] []) a) b =>
    leaf `FOL.Provable.symmetry [← encodeTerm s.locals a, ← encodeTerm s.locals b]
  | .forallElim (.forallElim (.forallElim (.theoremE `eq_trans [] []) a) b) c =>
    leaf `FOL.Provable.transitivity
      [← encodeTerm s.locals a, ← encodeTerm s.locals b, ← encodeTerm s.locals c]
  | .forallElim (.forallElim (.eqSubst motive) a) b =>
    let (_, h) ← substituteAt s motive a b
    return ⟨.imp (.equal a b) (.imp (.app motive a) (.app motive b)), h⟩
  | .forallElim .eqRefl t =>
    let x ← encodeTerm s.locals t
    return ⟨.equal t t, lift s.Γ (equal x x) (lemma `FOL.Provable.reflexivity [x])⟩
  | .forallElim proof argument =>
    -- A recursion equation can use a different program for each choice of base and step.
    -- Prove its applied instance while the caller's numerical arguments are available.
    if let some name := appliedTheorem? proof then
      if let some (.theoremE d) := (← environment).lookup name then
        if !d.parameters.isEmpty && isReflexivityProof d.body then
          let a ← infer
          return ⟨a, ← proveUniversalEquation s a⟩
    let child ← replay s context proof
    let .all motive ← whnf child.formula | throwError "expected a source universal"
    let a := Predicate.app motive argument
    let body ← encodeFormula (s.locals + 1) (openMotive motive)
    let x ← encodeTerm s.locals argument
    let h := rule `FOL.Sequent.all_elim [s.Γ, body, x] [child.proof]
    return ⟨a, ← convertInstance s.Γ body x (← s.encode a) h⟩
  | .existsIntro motive witness proof =>
    let child ← replay s context proof
    let h ← child.convert s (.app motive witness)
    let body ← encodeFormula (s.locals + 1) (openMotive motive)
    let x ← encodeTerm s.locals witness
    let h ← convertInstance s.Γ body x (← s.encode (.app motive witness)) h true
    return ⟨.ex motive, rule `FOL.Sequent.ex_intro [s.Γ, body, x] [h]⟩
  | .existsElim motive target =>
    return ⟨existentialEliminationType motive target, ← eliminateExists s motive target⟩
  | .letE _ a value body =>
    let value ← replay s context value (some a)
    let h ← value.convert s a
    let A ← s.encode a
    let child ← replay (s.assume A) (context.pushProof a) body expected
    let B ← s.encode child.formula
    return ⟨child.formula, mp s.Γ A B (introduce s.Γ A B child.proof) h⟩
  | .letTerm _ _ body | .letPredicate _ _ body => replay s context body expected
  | .ascribe a body =>
    let child ← replay s context body (some a)
    return ⟨a, ← child.convert s a⟩
  | .eqRefl =>
    let x := var 0
    let a := equal x x
    let inner ← s.bind
    let h := lift inner.Γ a (lemma `FOL.Provable.reflexivity [x])
    return ⟨reflexivityType, ← generalize s a h⟩
  | .eqSubst motive => return ⟨substitutionType motive, ← substituteEquality s motive⟩
  | .theoremE `dne [] [a] => leaf `FOL.Provable.neg_neg_elim [← s.encode a]
  | .theoremE name functions predicates =>
    let some (.theoremE declaration) := (← environment).lookup name |
      throwError "missing checked source theorem `{name}`"
    let a := declaration.type.instantiate functions predicates
    if predicates.isEmpty then
      if let some proof ← reuseParameterized s name functions a then
        return ⟨a, proof⟩
    let translation ← read
    if predicates.isEmpty && !declaration.functions.isEmpty &&
        declaration.functions.all (· > 0) then
      let arities := declaration.functions
      let forms ← (arities.zip functions).mapM fun (arity, f) =>
        prepareProgramFunction arity f translation.callback
      let programs := forms.map (·.1)
      let values ← forms.reverse.mapM fun (_, input) =>
        input.foldM (encodeTerm s.locals) (fun a b => pure (mkPair a b))
      let generic := translation.target ++ `contextual ++ name
      let parameters := declaration.parameters.map fun
        | .function n _ => Parameter.function n 0
        | p => p
      let configuration := { translation with
        target := generic
        parameters := parameters
        sourceFunctions := arities
        contextual := true }
      let template ← (encodeFormula 0 declaration.type).run configuration
      let generic := (contextualTheorems.getState (← getEnv))[name]?.getD generic
      if ((contextualTheorems.getState (← getEnv))[name]?).isNone then
        let proof ← (do
          let child ← replay {} configuration.sourceContext declaration.body
            (some declaration.type)
          child.convert {} declaration.type : DeriveM Proof).run configuration
        let mut proof := ofSequent language axioms emptyList template proof
        let mut code := template
        for _ in arities do
          proof := rule `FOL.Provable.gen [code] [proof]
          code := all code
        publishChecked (.theoremE ⟨generic, parameters, provable language axioms code, proof⟩)
          (← getRef)
        modifyEnv (contextualTheorems.addEntry · (name, generic))
      let mut code := (arities.foldl (fun f _ => all f) template).instantiate programs
      let mut proof := lift s.Γ code (applyTheorem generic [] programs)
      for value in values do
        let (.definition `FOL.Formula.all [], [body]) := getAppFnArgs code |
          throwError "missing contextual theorem input binder"
        let (target, equality) ← QuotedSubstitution.instantiate body value
        proof := rule `FOL.Sequent.all_elim [s.Γ, body, value] [proof]
        proof := transportCode s.Γ (instantiateFormula body value) target equality proof
        code := target
      let expected ← quoteFormula s.locals a
      if code == expected.code then return ⟨a, proof⟩
      let some provided := expected.withCode code |
        throwError "contextual theorem has different formula constructors"
      let h ← formulaImplication provided expected
      return ⟨a, mp s.Γ code expected.code (lift s.Γ (imp code expected.code) h) proof⟩

    let dependency := if functions.isEmpty && predicates.isEmpty then
        { translation with parameters := [], sourceFunctions := [], contextual := false }
      else translation
    let parameters := dependency.parameterTerms
    let scope := if parameters.isEmpty then Name.anonymous else translation.target
    let (fs, ps, captures) ← abstractArguments s.locals declaration.functions functions predicates
    let pattern := declaration.type.instantiate fs ps
    let abstract := fun body => captures.foldl (fun b _ => Predicate.all (.lam `env b)) body
    let statement := abstract pattern
    let code ← (encodeFormula 0 statement).run dependency
    let key := (scope, name, fs, ps)
    let translations := translatedTheorems.getState (← getEnv)
    let global := translations[(Name.anonymous, name, fs, ps)]?
    let (target, arguments) ← match global, translations[key]? with
      | some target, _ => pure (target, [])
      | none, some target => pure (target, parameters)
      | none, none => do
        let base := translation.target ++ `dependencies ++ name
        let core ← environment
        let mut target := base
        let mut i := 0
        while (core.lookup target).isSome do
          target := base.appendIndexAfter i
          i := i + 1
        let action : DeriveM Proof := do
          let body := mapProof (fun depth e => e.instantiate fs depth)
            (fun depth p => p.instantiate fs ps depth) (fun _ _ i => .hyp i)
            0 0 declaration.body
          let (_, body) := captures.foldl (fun (type, p) _ =>
            let motive := Predicate.lam `env type
            (.all motive, Proof.forallIntro `env motive p)) (pattern, body)
          try
            let child ← replay {} dependency.sourceContext body (some statement)
            child.convert {} statement
          catch error =>
            if error.isInterrupt then throw error
            throwError "while replaying `{name}`\n{error.toMessageData}"
        let h ← action.run dependency
        let body := ofSequent language axioms emptyList code h
        publishChecked (.theoremE ⟨target, dependency.parameters,
          provable language axioms code, body⟩) (← getRef)
        modifyEnv (translatedTheorems.addEntry · (key, target))
        pure (target, parameters)
    let mut h ← liftDependency s dependency statement code (applyTheorem target [] arguments)
    let mut type := statement
    for capture in captures.reverse do
      let .all motive ← whnf type | throwError "missing abstracted argument"
      let body ← encodeFormula (s.locals + 1) (openMotive motive)
      let argument ← encodeTerm s.locals capture
      h := rule `FOL.Sequent.all_elim [s.Γ, body, argument] [h]
      type := .app motive capture
      h ← convertInstance s.Γ body argument (← s.encode type) h
    return ⟨a, ← convertCode s.Γ (← s.encode type) (← s.encode a) h⟩
  | .succNeZero =>
    let a := neg (equal (succTerm (var 0)) zeroTerm)
    return ⟨successorNonzeroType, lift s.Γ (all a) (applyTheorem `FOL.PRA.succ_ne_zero)⟩
  | .succInj =>
    let x := var 1
    let y := var 0
    let a := imp (equal (succTerm x) (succTerm y)) (equal x y)
    return ⟨successorInjectivityType,
      lift s.Γ (all (all a)) (applyTheorem `FOL.PRA.succ_injective)⟩
  | .induction motive =>
    let type ← infer
    return ⟨type, ← replayInduction s motive type⟩

private def FormulaSyntax.specialize (env : Core.Environment) : FormulaSyntax → FormulaSyntax
  | .equal n a b x y => .equal n a b (specializeTerm env x).rhs (specializeTerm env y).rhs
  | .imp p q => .imp (p.specialize env) (q.specialize env)
  | .all p => .all (p.specialize env)
  | .falsum => .falsum

private def specializedTermEquality (env : Core.Environment) (_ : Nat) (_ _ x y : Term) :
    DeriveM Proof := do
  if x == y then return applyTheorem `FOL.PRA.Evaluation.refl [x]
  let forward := specializeTerm env x
  if forward.rhs == y then return forward.proof
  let reverse := specializeTerm env y
  if reverse.rhs == x then
    return applyTheorem `FOL.PRA.Evaluation.symm [y, x] [] [reverse.proof]
  throwError "cannot relate the packed and specialized program calls"

private def transfer (source : TheoremDefinition) (target : Syntax) (publicCode : Bool) :
    DeriveM Unit := do
  let translation ← read
  let action : DeriveM Unit := do
    let packed ← quoteFormula 0 source.type
    let replayed ← replay {} translation.sourceContext source.body (some source.type)
    let p ← replayed.convert {} source.type
    let proof := ofSequent language axioms emptyList packed.code p
    let env ← environment
    let statement := if publicCode then packed.specialize env else packed
    let specialized := statement.code != packed.code
    let name := translation.target
    let packedName := if specialized then name ++ `internal else name
    let type := provable language axioms packed.code
    publishChecked (.theoremE ⟨packedName, translation.parameters, type, proof⟩) target
    if translation.parameters.isEmpty then
      let key := (Name.anonymous, source.name, [], [])
      modifyEnv (translatedTheorems.addEntry · (key, packedName))
    else
      modifyEnv (parameterizedTheorems.addEntry · (source.name, packedName))
    if specialized then
      let convert ← formulaImplication packed statement (specializedTermEquality env)
      let packedProof := applyTheorem packedName [] translation.parameterTerms
      let proof := rule `FOL.Provable.mp [packed.code, statement.code] [convert, packedProof]
      let type := provable language axioms statement.code
      publishChecked (.theoremE ⟨name, translation.parameters, type, proof⟩) target
  action.run translation

end PRAProver.Library.FOL.PRA.Derive.Command

end

public meta section

namespace PRAProver.Library.FOL.PRA.Derive.Command

open Lean Elab Command PRAProver.Surface
open PRAProver.Library.Tactic.Construction

/-- Use an existing first-order proof when translating a call to a source theorem.
Check the proof against the translation of the source statement before recording it. -/
def registerFolPraDeriver (source target : Name) (functions : List PRAProver.Core.Term := [])
    (predicates : List PRAProver.Core.Predicate := []) : CommandElabM Unit := do
  let core := CoreEnvironment.getState (← getEnv)
  let depth := pra.maxDepth.get (← getOptions)
  let reference := PRAProver.Core.Proof.theoremE source functions predicates
  let type ← match PRAProver.Core.inferProof depth core {} reference with
    | .ok a => pure a
    | .error e => throwError "cannot instantiate `{source}`: {e.message}"
  let code ← (encodeFormula 0 type).run { depth, target }
  let expected := DSL.provable language axioms code
  let core := CoreEnvironment.getState (← getEnv)
  match PRAProver.Core.checkProof depth core {} (applyTheorem target) expected with
  | .error e => throwError "cannot use `{target}` for `{source}`: {e.message}"
  | .ok _ =>
    let key := (Name.anonymous, source, functions, predicates)
    modifyEnv (translatedTheorems.addEntry · (key, target))

declare_syntax_cat folPraPublicOption
syntax "(" &"public" " := " &"true" ")" : folPraPublicOption
syntax (name := deriveFolPra)
  "derive_fol_pra " (folPraPublicOption)? ident " as " ident : praDecl
syntax (name := registerFolPraDeriverCmd)
  "register_fol_pra_deriver " ident " as " ident : praDecl

/-- Register the checked first-order translation of a theorem named in a PRA block. -/
@[command_elab PRAProver.Surface.praEntry]
def elaborateRegisterFolPraDeriver : CommandElab := fun stx => do
  let `(praDecl| register_fol_pra_deriver $source:ident as $target:ident) := stx[0]
    | throwUnsupportedSyntax
  let env := CoreEnvironment.getState (← getEnv)
  let some (.theoremE sourceDecl) ← resolveDeclaration? env source.getId |
    throwErrorAt source "expected a checked PRA source theorem"
  unless sourceDecl.parameters.isEmpty do
    throwErrorAt source "expected a source theorem with no declaration parameters"
  let some (.theoremE targetDecl) ← resolveDeclaration? env target.getId |
    throwErrorAt target "expected a checked first-order PRA theorem"
  withRef target <| registerFolPraDeriver sourceDecl.name targetDecl.name

/-- Publish the first-order derivation of a checked PRA theorem. -/
@[command_elab PRAProver.Surface.praEntry]
def elaborateDeriveFolPra : CommandElab := fun stx => do
  let `(praDecl| derive_fol_pra $[$option:folPraPublicOption]? $source:ident as $target:ident) :=
    stx[0]
    | throwUnsupportedSyntax
  let env := CoreEnvironment.getState (← getEnv)
  let some (.theoremE declaration) ← resolveDeclaration? env source.getId |
    throwErrorAt source "derive_fol_pra expects a checked PRA theorem"
  let ns ← getCurrNamespace
  let name := if target.getId.getRoot == `_root_ then
    target.getId.replacePrefix `_root_ .anonymous
    else ns ++ target.getId
  let parameters : List Core.Parameter ← declaration.parameters.mapM fun
    | .function n _ => pure (.function n 0)
    | _ => throwErrorAt source "expected numerical or function parameters"
  let translation : Translation := {
    depth := pra.maxDepth.get (← getOptions), target := name,
    parameters, sourceFunctions := declaration.functions }
  let initial ← getEnv
  withRef source do
    try
      (transfer declaration target option.isSome).run translation
    catch error =>
      setEnv initial
      if error.isInterrupt then throw error
      throwError "derive_fol_pra: {error.toMessageData}"

end PRAProver.Library.FOL.PRA.Derive.Command
