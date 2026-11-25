module

public meta import LeanPRA.Library.FOL.DSL.Definition

/-!
# Reading symbolic FOL codes

Opaque PRA expressions keep an explicit substitution context, so numerical and function parameters
remain symbolic.

- `readTerm` recovers the visible term constructors.
- `readFormula` recovers the visible logical structure and assigns fresh binder names. A
  definition with a substitution theorem is read as a single formula applied to its term
  arguments.
- `freePositions` identifies surrounding positions visible in constructor code.
- `closedDefinitions` lists the definitions that stay closed when read.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL

open Lean hiding Term
open Lean.Elab.Command LeanPRA.Core
open LeanPRA.Library.Tactic.Construction

def positionName (i : Nat) : Name := .num `_folVariable i

private def unfoldCode (t : Term) : CommandElabM (Option Term) := do
  let (head, args) := getAppFnArgs t
  if let .definition n actuals := head then
    if let some (.function d) := (Surface.CoreEnvironment.getState (← getEnv)).lookup n then
      return some (Core.betaReduceTerm 2048 (args.foldl .app (d.body.instantiate actuals)))
  return none

/-- Read a fixed number of tuple components, using projections on an opaque tuple code. -/
partial def tupleEntries (n : Nat) (value : Term) : CommandElabM (List Term) := do
  if n == 0 then return []
  if n == 1 then return [value]
  let (head, args) := getAppFnArgs value
  if let .definition `pair [] := head then
    if let [a, b] := args then return a :: (← tupleEntries (n - 1) b)
  return applyDefinition `unpairLeft [value] ::
    (← tupleEntries (n - 1) (applyDefinition `unpairRight [value]))

/-- The number of free variable positions that the code `t` mentions beneath `depth` binders.
`closed` lists the definitions that stay closed; the count includes their term arguments. -/
partial def freePositions (closed : Array DefinitionInfo) (t : Term) (depth : Nat := 0) : Nat :=
  let (head, args) := getAppFnArgs t
  match head, args with
  | .definition `FOL.Term.var _, [_, i] => ((numeralValue? i).getD 0 + 1) - depth
  | .definition `FOL.Formula.all _, [a] => freePositions closed a (depth + 1)
  | .definition `FOL.Formula.subst [f], [_, a] =>
    -- Count the substituted positions used by the body, excluding replaced free variables.
    let rec substituted : Nat → Term → Nat
      | 0, _ => 0
      | count + 1, substitution =>
        match getAppFnArgs substitution with
        | (.definition `FOL.consSubst [value, rest], []) =>
          max (freePositions closed value depth) (substituted count rest)
        | (.definition `FOL.shiftSubst [_, offset], []) =>
          ((numeralValue? offset).getD 0 + count + 1) - depth
        | _ => max (freePositions closed substitution depth) (count + 1 - depth)
    substituted (freePositions closed a) f
  | .definition `FOL.consSubst [t, rest], [] =>
    max (freePositions closed t depth) (freePositions closed rest depth)
  | .definition name parameters, args =>
    match closed.find? (·.name == name) with
    | some d =>
      (parameters ++ args).zipIdx.foldl (fun n (value, i) =>
        if let some p := d.syntaxAt? i then
          max n (freePositions closed value (depth + p.arity))
        else n) (d.resultArity - depth)
    | none => args.foldl (fun n a => max n (freePositions closed a depth)) 0
  | _, _ => args.foldl (fun n a => max n (freePositions closed a depth)) 0

/-- The definitions that stay closed when terms and formulas are read in the current scope. -/
def closedDefinitions : CommandElabM (Array DefinitionInfo) := do
  if ← opensDefinitions then return #[]
  let preserve := fol.preserveDisplayNames.get (← getOptions)
  return (definitions.getState (← getEnv)).filter fun d =>
    if d.isFormula then d.substitution.isSome || preserve else d.resultArity == 0

partial def readTerm (L : LanguageInfo) (bound free : List Name) (input : Term)
    (fuel : Nat := 64) : CommandElabM TermView := do
  if fuel == 0 then return .code (languageTerm L) input ((bound ++ free).map TermView.var)
  let value := Core.betaReduceTerm 2048 input
  let (head, args) := getAppFnArgs value
  match head, args with
  | .definition `FOL.Term.var _, [_, i] =>
    if let some index := numeralValue? i then
      return .var ((bound ++ free)[index]?.getD (positionName (index - bound.length)))
  | .definition `FOL.Term.const _, [_, i] =>
    if let (.definition `FOL.Language.constantFamilyMember _, [_, b, k]) := getAppFnArgs i then
      let some index := numeralValue? b | throwError "expected a literal family number"
      return .indexedConst index k
    if let some index := numeralValue? i then
      if index < L.constants.size then return .constant index
      if !L.constantFamilies.isEmpty then
        let q := index - L.constants.size
        return .indexedConst (q % L.constantFamilies.size) (numeral (q / L.constantFamilies.size))
  | .definition `FOL.Term.app _, [_, i, values] =>
    if let (.definition `FOL.Language.functionFamilyMember _, [_, b, k]) := getAppFnArgs i then
      let some index := numeralValue? b | throwError "expected a literal family number"
      let some family := L.functionFamilies[index]? | throwError "invalid family number"
      return .indexedApp index k
        (← (← tupleEntries family.arity values).mapM (fun t => readTerm L bound free t (fuel - 1)))
    if let some index := numeralValue? i then
      let some (_, arity) := L.functions[index]? | throwError "invalid function index"
      return .app index (← (← tupleEntries arity values).mapM
        (fun t => readTerm L bound free t (fuel - 1)))
  | _, _ => pure ()
  if let .letE _ v body := value then return ← readTerm L bound free (body.subst0 v) (fuel - 1)
  if let some (d, values) ← definitionApplication? value then
    unless d.isFormula do
      let language := languageTerm L
      if ← isRegisteredClosedTerm language value then return .code language value []
      if d.substitution.isSome && !d.syntaxParameters.any (fun p => p.isFormula || p.arity > 0) then
        let terms := d.termPositions.map fun i => values[i]!
        let variables := d.termPositions.zipIdx.foldl (fun values (position, i) =>
          values.set position (applyDefinition `FOL.Term.var [language, numeral i])) values
        let arguments ← terms.mapM (readTerm L bound free · (fuel - 1))
        return .code language (d.apply variables) arguments
      return .code language value ((bound ++ free).map TermView.var)
  let reduced ← (calculate value).run' {}
  if reduced.value != value then return ← readTerm L bound free reduced.value (fuel - 1)
  if ← isRegisteredClosedTerm (languageTerm L) value then
    return .code (languageTerm L) value []
  if let .definition n _ := head then
    if (definitions.getState (← getEnv)).any (fun d => d.name == n) then
      if let some next ← unfoldCode value then return ← readTerm L bound free next (fuel - 1)
  return .code (languageTerm L) value ((bound ++ free).map TermView.var)

partial def readFormula (L : LanguageInfo) (bound free : List Name) (input : Term)
    (fuel : Nat := 64) : CommandElabM FormulaView := do
  if fuel == 0 then throwError "FOL formula unfolding limit exhausted"
  let value := Core.betaReduceTerm 2048 input
  let (head, args) := getAppFnArgs value
  match head, args with
  | .definition `FOL.Formula.falsum _, [] => return .falsum
  | .definition `FOL.Formula.equal _, [_, a, b] =>
    return .equal (← readTerm L bound free a) (← readTerm L bound free b)
  | .definition `FOL.Formula.rel _, [_, i, values] =>
    if let (.definition `FOL.Language.relationFamilyMember _, [_, b, k]) := getAppFnArgs i then
      let some index := numeralValue? b | throwError "expected a literal family number"
      let some family := L.relationFamilies[index]? | throwError "invalid family number"
      return .indexedRelation index k
        (← (← tupleEntries family.arity values).mapM (fun t => readTerm L bound free t (fuel - 1)))
    if let some index := numeralValue? i then
      let some (_, arity) := L.relations[index]? | throwError "invalid relation index"
      return .relation index (← (← tupleEntries arity values).mapM (readTerm L bound free ·))
  | .definition `FOL.Formula.imp _, [a, b] =>
    return .imp (← readFormula L bound free a fuel)
      (← readFormula L bound free b fuel)
  | .definition `FOL.Formula.all _, [a] =>
    let name ← liftCoreM (mkFreshUserName `x)
    return .all name (← readFormula L (name :: bound) free a fuel)
  | _, _ => pure ()
  if let .letE _ v body := value then
    return ← readFormula L bound free (body.subst0 v) (fuel - 1)
  -- Explicit term arguments give closed definitions a substitution context of their own.
  if let some (d, values) ← definitionApplication? value then
    if d.isFormula then
      if d.syntaxParameters.any (fun p => p.isFormula || p.arity > 0) then
        return .code (languageTerm L) value ((bound ++ free).map TermView.var)
      let terms := d.termPositions.map fun i => values[i]!
      let variables := d.termPositions.zipIdx.foldl (fun values (position, i) =>
        values.set position (applyDefinition `FOL.Term.var [languageTerm L, numeral i])) values
      let arguments ← terms.mapM (readTerm L bound free ·)
      return .code (languageTerm L) (d.apply variables) arguments
  if fol.preserveDisplayNames.get (← getOptions) then
    if let some (d, _) ← appliedDefinition? value then
      if d.isFormula then
        return .code (languageTerm L) value ((bound ++ free).map TermView.var)
  let reduced ← (calculate value).run' {}
  if reduced.value != value then return ← readFormula L bound free reduced.value (fuel - 1)
  if let .definition `FOL.Formula.subst [f] := head then
    if let [language, body] := args then
      let identity (t : Term) := pure (t, Core.Proof.forallElim .eqRefl t)
      if let some substitution ← normalizeSubstitution identity language f then
        let scope := bound ++ free
        if substitution.substitution.offset ≤ scope.length then
          let values ← substitution.substitution.values.mapM (readTerm L bound free ·)
          let tail := (scope.drop substitution.substitution.offset).map TermView.var
          return .code language body (values ++ tail)
  if let some (canonical, arguments) ← formulaBuilderArguments (languageTerm L) value then
    return .code (languageTerm L) canonical (← arguments.mapM (readTerm L bound free ·))
  if let .definition n _ := head then
    if (definitions.getState (← getEnv)).any (fun d => d.name == n) ||
        [`FOL.Formula.neg, `FOL.Formula.conj, `FOL.Formula.disj, `FOL.Formula.ex].contains n then
      if let some next ← unfoldCode value then return ← readFormula L bound free next (fuel - 1)
  return .code (languageTerm L) value ((bound ++ free).map TermView.var)

end LeanPRA.Library.FOL.DSL
