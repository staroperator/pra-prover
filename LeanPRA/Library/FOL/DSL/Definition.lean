module

public meta import LeanPRA.Library.FOL.DSL.Reduction

/-!
# FOL definitions

`fol_def` gives a name to a term or a formula. The name stands for a PRA function from the
definition's parameters to a syntax code. Contextual syntax arguments carry their surrounding
variables; entering a binder transports them to the extended context.

Results may have explicit slots, written `term of n` or `formula of n`. A lambda names those
slots in an FOL body. A whole `${...}` body supplies a PRA expression whose author determines
the slot layout and surrounding variable context.

For supported bodies with no result slots, the command proves how substitution acts on the
definition. Tactics use this theorem to carry a defined formula through instantiation and
shifting without opening it.
The theorem is named `D.subst` for both term and formula definitions. It describes `Term.subst`
or `Formula.subst`, respectively. A definition whose body has a shape the proof does not cover
has no substitution theorem and is opened when needed. Registered calculation and substitution
equations allow computational constructors to stay symbolic.

- `proveSubstitution` proves the substitution theorem of a definition.
- `elaborateDefinition` elaborates `fol_def`.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL

open LeanPRA.Library.Tactic.Construction

open Lean hiding Term

open Lean.Elab Lean.Elab.Command LeanPRA.Surface

open LeanPRA.Core

/-- The language and ambient substitution of the theorem being proved. -/
private structure SubstitutionGoal where
  language : Term
  f : Term
  parameters : List (Term × SyntaxParameter)

private abbrev SubstitutionM := ReaderT SubstitutionGoal (StateRefT (List Term) CommandElabM)

private def lifted (k : Nat) : SubstitutionM Term := do
  let g ← read
  return applyDefinition `FOL.liftSubst [g.language, numeral k] [g.f]

private def less (a b : Term) : CommandElabM Proof := do
  let h ← calculateClosedEquality (applyDefinition `ltb [a, b]) (numeral 1)
  return .impElim (← projectTheorem false `ltb_eq_one [a, b]) h

/-- From proofs of `old = new` for each entry, a proof of `build olds = build news`. The entries
contain no loose bound variables. -/
private def congruence (build : List Term → Term) (steps : List (Term × Term × Proof)) :
    Proof := Id.run do
  let olds := steps.map (·.1)
  let news := steps.map (·.2.1)
  let source := build olds
  let mut current := source
  let mut proof := Proof.forallElim .eqRefl source
  for ((old, new, step), i) in steps.zipIdx do
    if old == new then continue
    let hole := build (news.take i ++ [Term.bvar 0] ++ olds.drop (i + 1))
    let next := build (news.take (i + 1) ++ olds.drop (i + 1))
    let p := mkEqCongr (.lam `x hole) old new step
    proof := if current == source then p else mkEqTrans source current next proof p
    current := next
  return proof

private def substitutedTerm (f L t : Term) : Term :=
  applyDefinition `FOL.Term.subst [L, t] [f]

private def substitutedFormula (f L A : Term) : Term :=
  applyDefinition `FOL.Formula.subst [L, A] [f]

mutual

/-- Apply the substitution theorem of the definition `info` to its application `info.name fs`
beneath `k` binders. The proof states `Term.subst s L t = result` for a term definition and
`Formula.subst s L t = result` for a formula definition, where `s` is the lifted
substitution. -/
private partial def substDefinition (k : Nat) (info : DefinitionInfo) (fs : List Term) :
    SubstitutionM (Term × Proof) := do
  let g ← read
  let some theoremName := info.substitution |
    throwError "`{info.name}` has no substitution theorem"
  let s ← lifted k
  let values := fs
  let mut steps := []
  for (value, i) in values.zipIdx do
    if let some p := info.syntaxAt? i then
      let depth := k + p.arity
      let (result, proof) ← if p.isFormula then substFormula depth value else substTerm depth value
      let canonical := applyDefinition `FOL.liftSubst [g.language, numeral depth] [g.f]
      let nested := if p.arity == 0 then s else
        applyDefinition `FOL.liftSubst [g.language, numeral p.arity] [s]
      let operation := if p.isFormula then substitutedFormula else substitutedTerm
      let congr := if p.isFormula then `FOL.Formula.subst_congr else `FOL.Term.subst_congr
      let equal := if p.arity == 0 then Proof.forallElim .eqRefl (operation s g.language value)
        else .forallElim (applyTheorem congr [g.language] [nested, canonical]
          [applyTheorem `FOL.liftSubst_liftSubst
            [g.language, numeral p.arity, numeral k] [g.f]]) value
      let proof := if p.isFormula then
          mkEqTrans (operation nested g.language value) (operation canonical g.language value)
            result equal
            (mkEqTrans (substitutedFormula canonical g.language value)
              (applyDefinition `FOL.Formula.substWithDepth [g.language, value, numeral depth]
                [applyDefinition `FOL.liftSubst [g.language] [g.f]]) result
              (mkEqSymm
                (applyDefinition `FOL.Formula.substWithDepth [g.language, value, numeral depth]
                  [applyDefinition `FOL.liftSubst [g.language] [g.f]])
                (substitutedFormula canonical g.language value)
                (applyTheorem `FOL.Formula.substWithDepth_liftSubst
                  [g.language, value, numeral depth] [g.f])) proof)
        else mkEqTrans (operation nested g.language value)
          (operation canonical g.language value) result equal proof
      steps := steps ++ [(p.transport g.language s value, result, proof)]
    else steps := steps ++ [(value, value, .forallElim .eqRefl value)]
  let build (values : List Term) := Term.definition info.name values
  let applied := applyTheorem theoremName [] (s :: values)
  let source := Term.definition info.name fs
  let source := if info.isFormula then substitutedFormula s g.language source
    else substitutedTerm s g.language source
  let middle := build (steps.map (·.1))
  let result := build (steps.map (·.2.1))
  return (result, mkEqTrans source middle result applied (congruence build steps))

/-- Transport an application substitution and prove its action on every position. -/
private partial def substArguments (k : Nat) (values : Term) :
    SubstitutionM (Nat × Term × Proof) := do
  let g ← read
  let L := g.language
  let f ← lifted k
  match values with
  | .definition `FOL.consSubst [t, rest] =>
    let (t', pt) ← substTerm k t
    let (n, rest', pr) ← substArguments k rest
    return (n + 1, .definition `FOL.consSubst [t', rest'],
      applyTheorem `FOL.Term.subst_consSubst_liftSubst [L, numeral n, t, t']
        [f, g.f, rest, rest'] [pt, pr])
  | .definition `FOL.shiftSubst [_, count] =>
    unless count == numeral k do throwError "unexpected application context"
    return (0, values,
      applyTheorem `FOL.Term.subst_liftSubst_shiftSubst_comm [L, count] [g.f])
  | _ => throwError "unsupported application substitution"

private partial def substApplication (k : Nat) (formula : Bool) (values p : Term) :
    SubstitutionM (Term × Proof) := do
  let g ← read
  let some parameter := g.parameters.lookup p |
    throwError "a code argument needs a syntax parameter type"
  let (arity, values', pointwise) ←
    match getAppFnArgs values with
    | (.definition `FOL.liftSubst [shift], [_, n]) => do
      let .definition `FOL.shiftSubst [_, count] := shift |
        throwError "expected a context embedding"
      let some arity := numeralValue? n | throwError "expected a numerical syntax arity"
      let some offset := numeralValue? count | throwError "expected a numerical context size"
      unless k == arity + offset do throwError "syntax context mismatch"
      pure (arity, values,
        applyTheorem `FOL.liftSubst_shift_comm [g.language, n, count] [g.f])
    | _ => substArguments k values
  unless parameter.isFormula == formula && parameter.arity == arity do
    throwError "syntax application kind or arity mismatch"
  let sourceSubstitution ← lifted k
  let liftedParameter := applyDefinition `FOL.liftSubst [g.language, numeral arity] [g.f]
  let transformed := parameter.transport g.language g.f p
  let operation := if formula then substitutedFormula else substitutedTerm
  let result := operation values' g.language transformed
  let lemma := if formula then `FOL.Formula.subst_subst_of_eq
    else `FOL.Term.subst_subst_of_eq
  let proof := .forallElim (applyTheorem lemma [g.language]
    [sourceSubstitution, values, values', liftedParameter] [pointwise]) p
  if arity > 0 then return (result, proof)
  let middle := operation values' g.language (operation liftedParameter g.language p)
  let unlift := if formula then applyTheorem `FOL.Formula.subst_congr [g.language]
      [liftedParameter, g.f] [applyTheorem `FOL.liftSubst_zero [g.language] [g.f]]
    else applyTheorem `FOL.Term.subst_congr [g.language]
      [liftedParameter, g.f] [applyTheorem `FOL.liftSubst_zero [g.language] [g.f]]
  return (result, mkEqTrans (operation sourceSubstitution g.language
    (operation values g.language p)) middle result proof
      (congruence (fun ts => operation values' g.language ts[0]!)
        [(operation liftedParameter g.language p, transformed, .forallElim unlift p)]))

/-- Substitute into the term `t` of a definition body beneath `k` binders. The proof states
`Term.subst (liftSubst f L k) L t = result`. -/
private partial def substTerm (k : Nat) (t : Term) : SubstitutionM (Term × Proof) := do
  let g ← read
  let L := g.language
  let s ← lifted k
  let source := substitutedTerm s L t
  let (head, args) := getAppFnArgs t
  match head, args with
  | .definition `FOL.Term.var [], [_, j] =>
    let some n := numeralValue? j | throwError "unsupported variable position"
    unless n < k do throwError "a definition body refers to a position outside its binders"
    let lt ← less j (numeral k)
    return (t, mkEqTrans source (.app s j) t (applyTheorem `FOL.Term.subst_var [L, j] [s])
      (applyTheorem `FOL.liftSubst_of_lt [L, numeral k, j] [g.f] [lt]))
  | .definition `FOL.Term.const [], [_, j] =>
    let hj ← less j (applyDefinition `FOL.Language.constants [L])
    return (t, applyTheorem `FOL.Term.subst_const [L, j] [s] [hj])
  | .definition `FOL.Term.app [], [_, j, xs] =>
    let hj ← less j (applyDefinition `FOL.Language.functionCount [L])
    let arity ← (calculate (applyDefinition `FOL.Language.functionArity [L, j])).run' {}
    match numeralValue? arity.value, getAppFnArgs xs with
    | some 1, _ =>
      let build (ts : List Term) := applyDefinition `FOL.Term.app [L, j, ts[0]!]
      let (x, px) ← substTerm k xs
      let middle := build [substitutedTerm s L xs]
      return (build [x], mkEqTrans source middle (build [x])
        (applyTheorem `FOL.Term.subst_app_one [L, j, xs] [s] [hj, arity.proof])
        (congruence build [(substitutedTerm s L xs, x, px)]))
    | some 2, (.definition `pair [], [x, y]) =>
      let build (ts : List Term) :=
        applyDefinition `FOL.Term.app [L, j, applyDefinition `pair [ts[0]!, ts[1]!]]
      let (x', px) ← substTerm k x
      let (y', py) ← substTerm k y
      let middle := build [substitutedTerm s L x, substitutedTerm s L y]
      return (build [x', y'], mkEqTrans source middle (build [x', y'])
        (applyTheorem `FOL.Term.subst_app_two [L, j, x, y] [s] [hj, arity.proof])
        (congruence build [(substitutedTerm s L x, x', px), (substitutedTerm s L y, y', py)]))
    | _, _ => throwError "unsupported function arity"
  | .definition `FOL.Term.shift [], [_, count, x] =>
    unless k > 0 && count == numeral k do throwError "unexpected shift in a definition body"
    let .parameter _ := x | throwError "a shifted term must be a parameter of the definition"
    modify (x :: ·)
    return (applyDefinition `FOL.Term.shift [L, count, substitutedTerm g.f L x],
      applyTheorem `FOL.Term.subst_liftSubst_shift [L, count, x] [g.f])
  | .parameter _, [] =>
    let some p := g.parameters.lookup t | throwError "expected a term parameter"
    unless !p.isFormula && k == p.arity do throwError "unexpected term parameter context"
    modify (t :: ·)
    let result := p.transport L g.f t
    if k == 0 then
      return (result, applyTheorem `FOL.Term.subst_liftSubst_zero [L, t] [g.f])
    return (result, .forallElim .eqRefl result)
  | .definition `FOL.Term.subst [values], [_, p] =>
    substApplication k false values p
  | .definition name fs, [] =>
    let some info := (definitions.getState (← getEnv)).find? fun d =>
        d.name == name && !d.isFormula | throwError "unsupported term `{name}`"
    substDefinition k info fs
  | _, _ => throwError "unsupported term in a definition body"

/-- Substitute into the formula `A` of a definition body beneath `k` binders. The proof states
`Formula.substWithDepth (liftSubst f L) L A k = result`. For `neg`, `conj`, `disj`, and `ex`,
the proof is that of the formula they abbreviate. -/
private partial def substFormula (k : Nat) (A : Term) : SubstitutionM (Term × Proof) := do
  let g ← read
  let L := g.language
  let F := applyDefinition `FOL.liftSubst [L] [g.f]
  let depth := numeral k
  let at_ (A : Term) (k : Nat) := applyDefinition `FOL.Formula.substWithDepth [L, A, numeral k] [F]
  let source := at_ A k
  let imp (a b : Term) := applyDefinition `FOL.Formula.imp [a, b]
  let falsum := applyDefinition `FOL.Formula.falsum
  let (head, args) := getAppFnArgs A
  match head, args with
  | .definition `FOL.Formula.falsum [], [] =>
    return (A, applyTheorem `FOL.Formula.substWithDepth_falsum [L, depth] [F])
  | .definition `FOL.Formula.equal [], [_, x, y] =>
    let s ← lifted k
    let build (ts : List Term) := applyDefinition `FOL.Formula.equal [L, ts[0]!, ts[1]!]
    let (x', px) ← substTerm k x
    let (y', py) ← substTerm k y
    let middle := build [substitutedTerm s L x, substitutedTerm s L y]
    return (build [x', y'], mkEqTrans source middle (build [x', y'])
      (applyTheorem `FOL.Formula.substWithDepth_equal [L, x, y, depth] [F])
      (congruence build [(substitutedTerm s L x, x', px), (substitutedTerm s L y, y', py)]))
  | .definition `FOL.Formula.rel [], [_, j, xs] =>
    let s ← lifted k
    let hj ← less j (applyDefinition `FOL.Language.relationCount [L])
    let arityTerm := applyDefinition `FOL.Language.relationArity [L, j]
    let arity ← (calculate arityTerm).run' {}
    let entrywise := applyDefinition `FOL.Term.subst [L] [s]
    let rel (xs : Term) := applyDefinition `FOL.Formula.rel [L, j, xs]
    let mapped (n : Term) := rel (applyDefinition `Tuple.map [n, xs] [entrywise])
    let counted := mkEqTrans source (mapped arityTerm) (mapped arity.value)
      (applyTheorem `FOL.Formula.substWithDepth_rel [L, j, xs, depth] [F] [hj])
      (congruence (fun ts => mapped ts[0]!) [(arityTerm, arity.value, arity.proof)])
    match numeralValue? arity.value, getAppFnArgs xs with
    | some 1, _ =>
      let (x, px) ← substTerm k xs
      let middle := rel (substitutedTerm s L xs)
      let unfolded := mkEqTrans source (mapped arity.value) middle counted
        (congruence (fun ts => rel ts[0]!)
          [(applyDefinition `Tuple.map [arity.value, xs] [entrywise], substitutedTerm s L xs,
            applyTheorem `Tuple.map_one [xs] [entrywise])])
      return (rel x, mkEqTrans source middle (rel x) unfolded
        (congruence (fun ts => rel ts[0]!) [(substitutedTerm s L xs, x, px)]))
    | some 2, (.definition `pair [], [x, y]) =>
      let build (ts : List Term) := rel (applyDefinition `pair [ts[0]!, ts[1]!])
      let (x', px) ← substTerm k x
      let (y', py) ← substTerm k y
      let middle := build [substitutedTerm s L x, substitutedTerm s L y]
      let unfolded := mkEqTrans source (mapped arity.value) middle counted
        (congruence (fun ts => rel ts[0]!)
          [(applyDefinition `Tuple.map [arity.value, xs] [entrywise],
            applyDefinition `pair [substitutedTerm s L x, substitutedTerm s L y],
            applyTheorem `Tuple.map_two [x, y] [entrywise])])
      return (build [x', y'], mkEqTrans source middle (build [x', y']) unfolded
        (congruence build [(substitutedTerm s L x, x', px), (substitutedTerm s L y, y', py)]))
    | _, _ => throwError "unsupported relation arity"
  | .definition `FOL.Formula.imp [], [a, b] =>
    let build (ts : List Term) := imp ts[0]! ts[1]!
    let (a', pa) ← substFormula k a
    let (b', pb) ← substFormula k b
    let middle := build [at_ a k, at_ b k]
    return (build [a', b'], mkEqTrans source middle (build [a', b'])
      (applyTheorem `FOL.Formula.substWithDepth_imp [L, a, b, depth] [F])
      (congruence build [(at_ a k, a', pa), (at_ b k, b', pb)]))
  | .definition `FOL.Formula.all [], [a] =>
    let build (ts : List Term) := applyDefinition `FOL.Formula.all [ts[0]!]
    let (a', pa) ← substFormula (k + 1) a
    let middle := build [at_ a (k + 1)]
    return (build [a'], mkEqTrans source middle (build [a'])
      (applyTheorem `FOL.Formula.substWithDepth_all [L, a, depth] [F])
      (congruence build [(at_ a (k + 1), a', pa)]))
  | .definition `FOL.Formula.neg [], [a] =>
    let (result, proof) ← substFormula k (imp a falsum)
    let (_, [a', _]) := getAppFnArgs result | throwError "unexpected negation result"
    return (applyDefinition `FOL.Formula.neg [a'], proof)
  | .definition `FOL.Formula.conj [], [a, b] =>
    let (result, proof) ← substFormula k (imp (imp a (imp b falsum)) falsum)
    let (_, [inner, _]) := getAppFnArgs result | throwError "unexpected conjunction result"
    let (_, [a', rest]) := getAppFnArgs inner | throwError "unexpected conjunction result"
    let (_, [b', _]) := getAppFnArgs rest | throwError "unexpected conjunction result"
    return (applyDefinition `FOL.Formula.conj [a', b'], proof)
  | .definition `FOL.Formula.disj [], [a, b] =>
    let (result, proof) ← substFormula k (imp (imp a falsum) b)
    let (_, [negated, b']) := getAppFnArgs result | throwError "unexpected disjunction result"
    let (_, [a', _]) := getAppFnArgs negated | throwError "unexpected disjunction result"
    return (applyDefinition `FOL.Formula.disj [a', b'], proof)
  | .definition `FOL.Formula.ex [], [a] =>
    let all (a : Term) := applyDefinition `FOL.Formula.all [a]
    let (result, proof) ← substFormula k (imp (all (imp a falsum)) falsum)
    let (_, [quantified, _]) := getAppFnArgs result | throwError "unexpected existence result"
    let (_, [body]) := getAppFnArgs quantified | throwError "unexpected existence result"
    let (_, [a', _]) := getAppFnArgs body | throwError "unexpected existence result"
    return (applyDefinition `FOL.Formula.ex [a'], proof)
  | .parameter _, [] =>
    let some p := g.parameters.lookup A | throwError "expected a formula parameter"
    unless p.isFormula && k == p.arity do throwError "unexpected formula parameter context"
    let result := p.transport L g.f A
    if k == 0 then return (result, .forallElim .eqRefl result)
    return (result, applyTheorem `FOL.Formula.substWithDepth_liftSubst [L, A, depth] [g.f])
  | .definition `FOL.Formula.subst [values], [_, p] =>
    let (result, proof) ← substApplication k true values p
    return (result, mkEqTrans source (substitutedFormula (← lifted k) L A) result
      (applyTheorem `FOL.Formula.substWithDepth_liftSubst [L, A, depth] [g.f]) proof)
  | .definition name fs, [] =>
    let some info := (definitions.getState (← getEnv)).find? fun d =>
        d.name == name && d.isFormula | throwError "unsupported formula `{name}`"
    let (result, proof) ← substDefinition k info fs
    return (result, mkEqTrans source (substitutedFormula (← lifted k) L A) result
      (applyTheorem `FOL.Formula.substWithDepth_liftSubst [L, A, depth] [g.f]) proof)
  | _, _ => throwError "unsupported formula in a definition body"

end

/-- Generate a checked equation transporting the syntax arguments of a definition. -/
def proveSubstitution (L : LanguageInfo) (info : DefinitionInfo) (source : Syntax) :
    CommandElabM DefinitionInfo := do
  if info.resultArity > 0 then return info
  let environment := CoreEnvironment.getState (← getEnv)
  let some (.function declaration) := environment.lookup info.name | return info
  let count := declaration.parameters.length
  let language := languageTerm L
  let f := Term.parameter 0
  let values := (List.range count).map fun i => Term.parameter (1 + i)
  let body := Core.betaReduceTerm 2048 (declaration.body.instantiate values)
  try
    let syntaxParameters := values.zipIdx.filterMap fun (value, i) =>
      (info.syntaxAt? i).map (value, ·)
    let goal : SubstitutionGoal := ⟨language, f, syntaxParameters⟩
    let action := if info.isFormula then substFormula 0 body else substTerm 0 body
    let ((result, proof), found) ← (action.run goal).run []
    unless found.all (fun value => (syntaxParameters.lookup value).isSome) do
      throwError "ordinary PRA data used as contextual syntax needs an explicit syntax type"
    let termPositions := (List.range count).filter fun i =>
      (info.syntaxAt? i).any (fun p => !p.isFormula && p.arity == 0)
    let arguments := values.zipIdx.map fun (value, i) =>
      if let some p := info.syntaxAt? i then p.transport language f value else value
    let expected := Core.betaReduceTerm 2048 (declaration.body.instantiate arguments)
    unless result == expected do
      throwError "a spliced expression depends on a term of the current scope"
    let lhs := Term.definition info.name values
    let rhs := Term.definition info.name arguments
    let (lhs, proof) := if info.isFormula then (substitutedFormula f language lhs, proof) else
      let unlifted := substitutedTerm (applyDefinition `FOL.liftSubst [language, numeral 0] [f])
        language lhs
      (substitutedTerm f language lhs, mkEqTrans (substitutedTerm f language lhs) unlifted rhs
        (mkEqSymm unlifted (substitutedTerm f language lhs)
          (applyTheorem `FOL.Term.subst_liftSubst_zero [language, lhs] [f])) proof)
    let parameters := Parameter.function `f 1 ::
      declaration.parameters.map (fun p => .function p.binderName p.arity)
    let name := info.name ++ `subst
    publishChecked (.theoremE ⟨name, parameters, Predicate.equal lhs rhs, proof⟩) source
    return { info with substitution := some name, termPositions }
  catch error =>
    if error.isInterrupt then throw error
    return info

@[command_elab LeanPRA.Surface.praEntry]
def elaborateDefinition : CommandElab := fun stx => do
  let (doc, entry) ← match stx[0] with
    | `(praDecl| $doc:docComment $decl:praDecl) => pure (some doc, decl.raw)
    | entry => pure (none, entry)
  let (name, language, ps, formula, arity, slots, body) ← match entry with
    | `(praDecl| fol_def $n:ident over $L:ident $ps:praParam* : term $[of $k:num]? :=
        $[fun $xs:ident* =>]? $t:folTerm) =>
      pure (n, L, ps, false, k.map (·.getNat) |>.getD 0, xs, t.raw)
    | `(praDecl| fol_def $n:ident over $L:ident $ps:praParam* : formula $[of $k:num]? :=
        $[fun $xs:ident* =>]? $a:folFormula) =>
      pure (n, L, ps, true, k.map (·.getNat) |>.getD 0, xs, a.raw)
    | _ => throwUnsupportedSyntax
  let L ← findLanguage language.getId.eraseMacroScopes
  let (binders, syntaxParameters) ← declarationParameters ps
  let (body, scope) ← if let some xs := slots then do
      unless xs.size == arity do throwError "expected {arity} explicit result binders"
      let names := xs.toList.map (·.getId.eraseMacroScopes)
      unless names.eraseDups.length == names.length do
        throwError "duplicate result binder"
      pure (body, names.reverse)
    else if body.isOfKind ``termSplice || body.isOfKind ``formulaSplice then
      pure (body, [])
    else completeApplication body ⟨name.getId, formula, arity⟩ []
  let mut parameters := #[]
  let mut arguments := #[]
  for p in ps do
    let (ids, type) ← match p with
      | `(praParam| ($ids:ident* : $type:praExpr)) => pure (ids, type)
      | `(praParam| {$ids:ident* : $type:praExpr}) => pure (ids, type)
      | _ => throwUnsupportedSyntax
    if syntaxParameterType? type == some (false, 0) then
      for id in ids do arguments := arguments.push id.getId.eraseMacroScopes
    else
      unless arguments.isEmpty do throwErrorAt p "put named parameters before term arguments"
      for id in ids do parameters := parameters.push id.getId.eraseMacroScopes
  let previousData := activeDataParameters.getState (← getEnv)
  modifyEnv (activeDataParameters.setState · (dataParameterNames ps))
  let value ← try
      if formula then formulaExpression L scope body syntaxParameters
      else termExpression L scope body syntaxParameters
    finally modifyEnv (activeDataParameters.setState · previousData)
  let declaration ← `(praDecl| def $name:ident $binders:praParam* : Nat := $value)
  let declaration ← if let some doc := doc then
      `(praDecl| $doc:docComment $declaration:praDecl)
    else pure declaration
  elaborateDeclaration declaration
  let ns ← getCurrNamespace
  let template ← if parameters.isEmpty && arity == 0 then do
      let names ← arguments.mapM (fun n => liftCoreM (mkFreshUserName n))
      let vars := arguments.toList.zip names.toList
      try
        let body ← if formula then Sum.inr <$> parseFormula L vars ⟨body⟩
          else Sum.inl <$> parseTerm L vars ⟨body⟩
        pure (some (names, body))
      catch error =>
        if error.isInterrupt then throw error
        pure none
    else pure none
  let info : DefinitionInfo := {
    name := ns ++ name.getId.eraseMacroScopes
    language := L.name
    parameters, arguments, template, syntaxParameters
    isFormula := formula, resultArity := arity }
  let info ← proveSubstitution L info name
  modifyEnv (definitions.addEntry · info)

end LeanPRA.Library.FOL.DSL
