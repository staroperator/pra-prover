module

public meta import LeanPRA.Library.FOL.DSL.Expression

/-!
# Proof-producing symbolic calculation

This frontend evaluator uses the PRA constructor equations to calculate substitutions and formula
equalities. Pairing codes remain symbolic. Each reduction returns an ordinary PRA equality proof,
assembled from common theorems, congruence, and definitional equality.

A term or formula definition can stay closed during calculation. A substitution theorem lets
the calculation substitute into the arguments while keeping the definition closed.

- `Calculation` stores a resulting expression together with its equality proof.
- `calculate` calculates an expression; `openDefinitions` also opens the named definitions.
- `openHead` opens the definition at the head of a formula code.
- `reconcile` opens definitions at the places where two codes differ.
- `calculateClosedEquality` compares the calculated expressions and constructs a PRA proof of
  their equality.
- `fol.openDefinitions` and `withOpenDefinitions` open every definition.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL

open LeanPRA.Library.Tactic.Construction

open Lean hiding Term

open Lean.Elab.Command

open LeanPRA.Core

structure Calculation where
  value : Term
  proof : Proof

/-- When true, every FOL definition is opened wherever a formula is calculated or read. -/
register_option fol.openDefinitions : Bool := {
  defValue := false
  descr := "open every FOL definition when a formula is calculated or read"
}

/-- Keep named formula codes intact while preparing the goal display. -/
register_option fol.preserveDisplayNames : Bool := {
  defValue := false
  descr := "preserve named formula codes during goal display"
}

/-- Whether every FOL definition is opened in the current scope. -/
def opensDefinitions : CommandElabM Bool := return fol.openDefinitions.get (← getOptions)

/-- Run `x` with every FOL definition opened. -/
def withOpenDefinitions {m : Type → Type} {α : Type} [Monad m] [MonadLiftT CommandElabM m]
    [MonadFinally m] (x : m α) : m α := do
  let saved ← ((do return (← getScope).opts) : CommandElabM Options)
  (modifyScope fun scope => { scope with opts := fol.openDefinitions.set scope.opts true } :
    CommandElabM Unit)
  try x finally (modifyScope fun scope => { scope with opts := saved } : CommandElabM Unit)

private structure ClosedTermRule where
  symbol : Name
  theoremName : Name
  language : Term
  arity : Nat
  parameters : Nat
  deriving Inhabited

private initialize closedTermRules :
    SimplePersistentEnvExtension ClosedTermRule (Array ClosedTermRule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

/-- Register a proved equation `∀ xs, Term.subst f L (symbol xs) = symbol xs`.
The theorem has one unary function parameter `f`; `xs` are numerical universal binders.
This lets symbolic code builders supply their own substitution equations. -/
def registerClosedTerm (symbol theoremName : Name) : CommandElabM Unit := do
  let some (.theoremE declaration) :=
      (Surface.CoreEnvironment.getState (← getEnv)).lookup theoremName |
    throwError "expected a checked PRA theorem `{theoremName}`"
  unless declaration.functions == [1] && declaration.predicates.isEmpty do
    throwError "a closed-term rule requires one unary function parameter"
  let mut type := Core.betaReducePredicate 2048 declaration.type
  let mut arity := 0
  while let .all (.lam _ body) := type do
    arity := arity + 1
    type := body
  let .equal lhs rhs := type | throwError "expected a substitution equation"
  let (.definition `FOL.Term.subst [.parameter 0], [language, code]) := getAppFnArgs lhs |
    throwError "expected substitution by the theorem's function parameter"
  let (.definition name parameters, arguments) := getAppFnArgs code |
    throwError "expected a named term constructor"
  unless name == symbol && parameters ++ arguments == (List.range arity).reverse.map Term.bvar &&
      rhs == code do throwError "the rule must preserve `{symbol}`"
  modifyEnv (closedTermRules.addEntry · ⟨symbol, theoremName, language, arity, parameters.length⟩)

/-- Whether a registered substitution theorem proves that this term code has no free positions. -/
def isRegisteredClosedTerm (L value : Term) : CommandElabM Bool := do
  let (.definition symbol parameters, args) := getAppFnArgs value | return false
  return (closedTermRules.getState (← getEnv)).any fun rule =>
    rule.symbol == symbol && rule.language == L && rule.parameters == parameters.length &&
      rule.arity == parameters.length + args.length

initialize calculations : EnvExtension (Std.HashMap Term Calculation) ←
  registerEnvExtension (pure {})

/-- The stored calculations made with every FOL definition opened. -/
initialize openCalculations : EnvExtension (Std.HashMap Term Calculation) ←
  registerEnvExtension (pure {})

private structure CalculationRule where
  theoremName : Name
  functions : Nat
  variables : Nat
  lhs : Term
  rhs : Term
  deriving Inhabited

private initialize calculationRules :
    SimplePersistentEnvExtension CalculationRule (Array CalculationRule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

private structure FormulaBuilderRule where
  symbol : Name
  language : Term
  arity : Nat
  parameters : Nat
  termArguments : List Nat
  deriving Inhabited

private initialize formulaBuilders :
    SimplePersistentEnvExtension FormulaBuilderRule (Array FormulaBuilderRule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

private def calculationVariables : Term → Option (List Nat × List Nat)
  | .parameter i => some ([i], [])
  | .bvar i => some ([], [i])
  | .zero | .succ => some ([], [])
  | .app f a => do
    let (fs, xs) ← calculationVariables f
    let (gs, ys) ← calculationVariables a
    return (fs ++ gs, xs ++ ys)
  | .definition _ fs => fs.foldlM (fun (ps, xs) value => do
      let (qs, ys) ← calculationVariables value
      return (ps ++ qs, xs ++ ys)) ([], [])
  | _ => none

/-- Add a checked numerical equation to symbolic FOL calculation. Declaration parameters and
universal variables are matched against its left side; the equation may have no proof premises. -/
def registerCalculation (theoremName : Name) : CommandElabM Unit := do
  let some (.theoremE declaration) :=
      (Surface.CoreEnvironment.getState (← getEnv)).lookup theoremName |
    throwError "expected a checked PRA theorem `{theoremName}`"
  unless declaration.predicates.isEmpty do
    throwError "a calculation equation may have only numerical parameters"
  let mut type := Core.betaReducePredicate 2048 declaration.type
  let mut variables := 0
  while let .all (.lam _ body) := type do
    variables := variables + 1
    type := body
  let .equal lhs rhs := type | throwError "expected an equation without proof premises"
  let (.definition _ _, _) := getAppFnArgs lhs |
    throwError "the left side of a calculation equation must apply a named function"
  let some (fs, xs) := calculationVariables lhs |
    throwError "the left side must use variables and named function applications"
  unless (List.range declaration.functions.length).all fs.contains &&
      (List.range variables).all xs.contains do
    throwError "every parameter and universal variable must occur on the left side"
  modifyEnv (calculationRules.addEntry ·
    ⟨theoremName, declaration.functions.length, variables, lhs, rhs⟩)
  modifyEnv (calculations.setState · {})
  modifyEnv (openCalculations.setState · {})

/-- Register a numerical formula builder using its proved substitution equation. The equation
must leave numerical arguments unchanged and substitute each term argument with the same map. -/
def registerFormulaBuilder (symbol theoremName : Name) : CommandElabM Unit := do
  let some (.theoremE declaration) :=
      (Surface.CoreEnvironment.getState (← getEnv)).lookup theoremName |
    throwError "expected a checked PRA theorem `{theoremName}`"
  let mut type := Core.betaReducePredicate 2048 declaration.type
  while let .all (.lam _ body) := type do type := body
  let .equal lhs rhs := type | throwError "expected a substitution equation"
  let (.definition `FOL.Formula.substWithDepth [f], [L, source, depth]) := getAppFnArgs lhs |
    throwError "expected formula substitution on the left side"
  let .parameter fi := f | throwError "the substitution must be a declaration parameter"
  unless declaration.functions[fi]? == some 2 do
    throwError "the substitution parameter must have two numerical arguments"
  let (.definition name parameters, arguments) := getAppFnArgs source |
    throwError "expected a numerical formula builder"
  let (.definition name' parameters', arguments') := getAppFnArgs rhs |
    throwError "the right side must apply the same formula builder"
  let args := parameters ++ arguments
  let values := parameters' ++ arguments'
  unless name == symbol && name' == symbol && args.length == values.length &&
      parameters.length == parameters'.length do
    throwError "the equation must describe substitution through `{symbol}`"
  unless calculationVariables L == some ([], []) do
    throwError "the builder's language must be fixed"
  let numericalVariable (value : Term) := match value with
    | .parameter i => declaration.functions[i]? == some 0
    | .bvar _ => true
    | _ => false
  unless numericalVariable depth && args.all numericalVariable &&
      !args.contains depth && args.eraseDups.length == args.length do
    throwError "the builder arguments and depth must be distinct numerical variables"
  let mut positions := []
  for ((argument, value), i) in (args.zip values).zipIdx do
    if argument == value then continue
    unless value == applyDefinition `FOL.Term.subst [L, argument] [.app f depth] do
      throwError "each term argument must use the same substitution at the same depth"
    positions := positions ++ [i]
  unless !positions.isEmpty do throwError "a formula builder needs at least one term argument"
  registerCalculation theoremName
  modifyEnv (formulaBuilders.addEntry · ⟨symbol, L, args.length, parameters.length, positions⟩)

/-- Separate a registered builder's term arguments from its numerical parameters. The returned
code uses consecutive variable positions for those arguments. -/
def formulaBuilderArguments (L value : Term) : CommandElabM (Option (Term × List Term)) := do
  let (.definition symbol parameters, arguments) := getAppFnArgs value | return none
  let args := parameters ++ arguments
  let some rule := (formulaBuilders.getState (← getEnv)).find? (fun rule =>
      rule.symbol == symbol && rule.language == L && rule.arity == args.length &&
        rule.parameters == parameters.length) | return none
  let mut canonical := args.toArray
  let mut arguments := []
  for (position, i) in rule.termArguments.zipIdx do
    arguments := arguments ++ [args[position]!]
    canonical := canonical.set! position (applyDefinition `FOL.Term.var [L, numeral i])
  let values := canonical.toList
  return some (applyDefinition symbol (values.drop rule.parameters)
    (values.take rule.parameters), arguments)

private abbrev Matches := Array (Option Term) × Array (Option Term)

private def bindMatch (values : Array (Option Term)) (index : Nat) (value : Term) :
    Option (Array (Option Term)) := do
  let entry ← values[index]?
  if let some previous := entry then
    if previous == value then return values else none
  else return values.set! index (some value)

private partial def matchCalculation (pattern value : Term) (bindings : Matches) :
    Option Matches := do
  match pattern, value with
  | .parameter i, _ => return (← bindMatch bindings.1 i value, bindings.2)
  | .bvar i, _ => return (bindings.1, ← bindMatch bindings.2 i value)
  | .app f a, .app g b => matchCalculation a b (← matchCalculation f g bindings)
  | .definition n fs, .definition m gs =>
    unless n == m && fs.length == gs.length do none
    (fs.zip gs).foldlM (fun state (a, b) => matchCalculation a b state) bindings
  | _, _ => if pattern == value then some bindings else none

private def instantiateCalculation (functions variables : List Term) (depth : Nat) : Term → Term
  | .parameter i => functions[i]!.shift depth
  | .bvar i => if i < depth then .bvar i else variables[i - depth]!.shift depth
  | .app f a => .app (instantiateCalculation functions variables depth f)
      (instantiateCalculation functions variables depth a)
  | .lam n body => .lam n (instantiateCalculation functions variables (depth + 1) body)
  | .letE n value body => .letE n (instantiateCalculation functions variables depth value)
      (instantiateCalculation functions variables (depth + 1) body)
  | .primrec base step => .primrec (instantiateCalculation functions variables depth base)
      (instantiateCalculation functions variables depth step)
  | .definition n fs => .definition n (fs.map (instantiateCalculation functions variables depth))
  | t => t

private def calculationRule (input : Term) : CommandElabM (Option Calculation) := do
  for rule in calculationRules.getState (← getEnv) do
    if let some (functions, variables) := matchCalculation rule.lhs input
        (Array.replicate rule.functions none, Array.replicate rule.variables none) then
      if let some functions := functions.toList.mapM id then
        if let some variables := variables.toList.mapM id then
          let result := instantiateCalculation functions variables 0 rule.rhs
          return some ⟨result, applyTheorem rule.theoremName variables.reverse functions⟩
  return none

/-- The results of a calculation so far, and the FOL definitions that it opens by request. -/
structure CalculationState where
  cache : Std.HashMap Term Calculation := {}
  opened : List Name := []

abbrev CalculationM := StateRefT CalculationState CommandElabM

/-- Read a definition that stays closed during calculation. Formulas need a substitution
theorem. Terms with no result slots can also be opened when a substitution needs their body. -/
def definitionApplication? (t : Term) :
    CommandElabM (Option (DefinitionInfo × List Term)) := do
  let .definition name values := t | return none
  let some d := (definitions.getState (← getEnv)).find? (·.name == name) | return none
  unless !(← opensDefinitions) &&
      (if d.isFormula then d.substitution.isSome else d.resultArity == 0) do return none
  return some (d, values)

private def closedDefinition? (t : Term) :
    CalculationM (Option (DefinitionInfo × List Term)) := do
  let some (d, values) ← definitionApplication? t | return none
  if (← get).opened.contains d.name then return none
  return some (d, values)

private def named (t : Term) (n : Name) : Option (List Term × List Term) :=
  match getAppFnArgs t with
  | (.definition m fs, args) => if m == n then some (fs, args) else none
  | _ => none

private def unfoldOnce (t : Term) : CommandElabM (Option Term) := do
  let (head, args) := getAppFnArgs t
  match head with
  | .definition n fs =>
    match (Surface.CoreEnvironment.getState (← getEnv)).lookup n with
    | some (.function d) =>
      return some (Core.betaReduceTerm 2048 (args.foldl .app (d.body.instantiate fs)))
    | _ => return none
  | _ => return none

private def smallArithmetic (n : Name) (args : List Nat) : Option Nat :=
  match n, args with
  | `S, [a] => some (a + 1)
  | `pred, [a] => some (a - 1)
  | `add, [a, b] => some (a + b)
  | `sub, [_, _] => none
  | `mul, [a, b] => some (a * b)
  | `eqb, [_, _] => none
  | `ltb, [_, _] => none
  | `leb, [_, _] => none
  | `isPos, [a] => some (if a == 0 then 0 else 1)
  | `isZero, [a] => some (if a == 0 then 1 else 0)
  | `band, [a, b] => some (if a > 0 && b > 0 then 1 else 0)
  | `bor, [a, b] => some (if a > 0 || b > 0 then 1 else 0)
  | `max, [_, _] => none
  | _, _ => none

private def transparent (n : Name) : Bool :=
  [`primrec, `iter, `eqb, `ltb, `leb, `max, `FOL.Formula.instantiate, `FOL.Formula.shift,
    `FOL.Formula.instantiateAt, `FOL.Term.shift, `FOL.Term.instantiateAt,
    `FOL.Formula.neg, `FOL.Formula.conj, `FOL.Formula.disj, `FOL.Formula.ex,
    `FOL.Formula.isClosed,
    `FOL.Formula.equalPremises, `Tuple.get, `Tuple.map, `Tuple.max, `FOL.Language.functionCount,
    `FOL.Formula.successorInstance,
    `FOL.Language.relationCount, `FOL.Language.functionFamilyCount,
    `FOL.Language.relationFamilyCount,
    `FOL.Language.functionSymbolArity, `FOL.Language.relationSymbolArity
  ].contains n

private partial def differingTerms (a b : Term) : Term × Term :=
  match a, b with
  | .app f x, .app g y =>
    if f != g then differingTerms f g
    else if (numeralValue? x).isSome && (numeralValue? y).isSome then (a, b)
    else differingTerms x y
  | .lam _ p, .lam _ q => differingTerms p q
  | .definition n fs, .definition m gs =>
    if n == m && fs.length == gs.length then
      match (fs.zip gs).find? (fun (f, g) => f != g) with
      | some (f, g) =>
        if (numeralValue? f).isSome && (numeralValue? g).isSome then (a, b)
        else differingTerms f g
      | none => (a, b)
    else (a, b)
  | _, _ => (a, b)

/-- Join proofs of `a = b` and `b = c`. When two of the terms coincide, the proof of the other
equality is the result and no transitivity step is written. -/
private def joinEqualities (a b c : Term) (ab bc : Proof) : Proof :=
  if a == b then bc else if b == c then ab else mkEqTrans a b c ab bc

private def familyMemberParts? (isRelation : Bool) (j : Term) : Option (Term × Term) := do
  let symbol :=
    if isRelation then `FOL.Language.relationFamilyMember else `FOL.Language.functionFamilyMember
  let (_, [_, b, k]) ← named j symbol | none
  return (b, k)

mutual

  partial def calculate (input : Term) : CalculationM Calculation := do
    if let some r := (← get).cache[input]? then return r
    let result ← calculateFresh input
    let result := if input == result.value then ⟨input, .forallElim .eqRefl input⟩ else result
    modify fun state => { state with cache := state.cache.insert input result }
    return result

  private partial def follow (a b : Term) (proof : Proof) : CalculationM Calculation := do
    if a == b then return ⟨a, .forallElim .eqRefl a⟩
    let r ← calculate b
    return ⟨r.value, joinEqualities a b r.value proof r.proof⟩

  partial def calculateEquality (a b : Term) : CalculationM Proof := do
    if a == b then return .forallElim .eqRefl a
    let ra ← calculate a
    let rb ← calculate b
    unless ra.value == rb.value do
      let (lhs, rhs) := differingTerms ra.value rb.value
      throwError "symbolic FOL calculation disagrees at:\n{repr lhs}\n{repr rhs}"
    if rb.value == b then return ra.proof
    return joinEqualities a ra.value b ra.proof (mkEqSymm b rb.value rb.proof)

  private partial def lessProof (a b : Term) : CalculationM Proof := do
    let h ← calculateEquality (applyDefinition `ltb [a, b]) (numeral 1)
    return .impElim (← projectTheorem false `ltb_eq_one [a, b]) h

  partial def constantProof (L j : Term) : CalculationM Proof := do
    let count := applyDefinition `FOL.Language.constantFamilyCount [L]
    if let some (Nat.succ _) := numeralValue? (← calculate count).value then
      let h ← lessProof (numeral 0) count
      return applyTheorem `FOL.Language.isConstant_of_constantFamilyCount_pos [L, j] [] [h]
    let h ← lessProof j (applyDefinition `FOL.Language.constants [L])
    return applyTheorem `FOL.Language.isConstant_of_lt [L, j] [] [h]

  /-- Prove that an ordinary symbol or a family member belongs to the given language. -/
  partial def symbolProof (L j : Term) (isRelation : Bool := false) : CalculationM Proof := do
    let language := `FOL.Language
    let kind := if isRelation then "relation" else "function"
    let predicate := if isRelation then "isRelation" else "isFunction"
    if let some (b, k) := familyMemberParts? isRelation j then
      let count := applyDefinition (language ++ Name.mkSimple (kind ++ "FamilyCount")) [L]
      return applyTheorem (language ++ Name.mkSimple (predicate ++ "_familyMember"))
        [L, b, k] [] [← lessProof b count]
    let count := applyDefinition (language ++ Name.mkSimple (kind ++ "Count")) [L]
    return applyTheorem (language ++ Name.mkSimple (predicate ++ "_of_lt"))
      [L, j] [] [← lessProof j count]

  private partial def calculateFresh (input : Term) : CalculationM Calculation := do
    if fol.preserveDisplayNames.get (← getOptions) then
      if let .definition name _ := input then
        if (definitions.getState (← getEnv)).any (fun d => d.name == name && d.isFormula) then
          return ⟨input, .forallElim .eqRefl input⟩
    let beta := Core.betaReduceTerm 2048 input
    if beta != input then return ← follow input beta (.forallElim .eqRefl input)
    match input with
    | .letE _ value body =>
      let next := body.subst0 value
      return ← follow input next (.forallElim .eqRefl input)
    | .app (.primrec base step) count =>
      let rc ← calculate count
      if let some n := numeralValue? rc.value then
        if n > 64 then throwError "FOL calculation refuses a large primitive-recursion expansion"
        if n == 0 then return ← follow input base (applyTheorem `primrec_zero [base] [step])
        let previous := Term.app (.primrec base step) (numeral (n - 1))
        let value := Term.app (.app step (numeral (n - 1))) previous
        let rp ← calculate previous
        let result := Term.app (.app step (numeral (n - 1))) rp.value
        let h := mkEqCongr (.app step (numeral (n - 1))) previous rp.value rp.proof
        return ← follow input result (mkEqTrans input value result
          (applyTheorem `primrec_succ [base, numeral (n - 1)] [step]) h)
      return ⟨input, .forallElim .eqRefl input⟩
    | _ => pure ()
    let (head, args) := getAppFnArgs input
    if let .definition `ite [] := head then
      if let [condition, yes, no] := args then
        let rc ← calculate condition
        if let some n := numeralValue? rc.value then
          let mid := applyDefinition `ite [rc.value, yes, no]
          let hp := mkEqCongr
            (.lam .anonymous (applyDefinition `ite [.bvar 0, yes.shift, no.shift]))
            condition rc.value rc.proof
          let result := if n == 0 then no else yes
          let branch := if n == 0 then applyTheorem `ite_zero [yes, no]
            else applyTheorem `ite_succ [numeral (n - 1), yes, no]
          return ← follow input result (mkEqTrans input mid result hp branch)
    let mut changed : Array (Nat × Calculation) := #[]
    for (a, i) in args.zipIdx do
      let ra ← calculate a
      if a != ra.value then changed := changed.push (i, ra)
    -- One congruence step replaces up to three arguments by their calculated values.
    let mut current := input
    let mut proof := Proof.forallElim .eqRefl input
    let mut values := args.toArray
    let mut pending := changed.toList
    while !pending.isEmpty do
      let group := pending.take 3
      pending := pending.drop 3
      let count := group.length
      let mut body := (values.map (·.shift count))
      let mut next := values
      for ((i, ra), j) in group.zipIdx do
        body := body.set! i (.bvar (count - 1 - j))
        next := next.set! i ra.value
      let f := (List.range count).foldl (fun f _ => Term.lam .anonymous f)
        (body.foldl .app (head.shift count))
      let congruence := [`eq_congr, `eq_congr₂, `eq_congr₃][count - 1]!
      let step := applyTheorem congruence
        (group.map (fun (i, _) => values[i]!) ++ group.map (·.2.value)) [f] (group.map (·.2.proof))
      let result := next.foldl .app head
      proof := joinEqualities input current result proof step
      current := result
      values := next
    let tail ← calculateHead current
    return ⟨tail.value, joinEqualities input current tail.value proof tail.proof⟩

  /-- Calculate the arguments of a definition that stays closed. -/
  private partial def calculateDefinition (t : Term) (d : DefinitionInfo)
      (values : List Term) : CalculationM Calculation := do
    let name := d.name
    let mut current := values
    let mut proof := Proof.forallElim .eqRefl t
    for (value, i) in values.zipIdx do
      let r ← calculate value
      if r.value == value then continue
      let hole := Term.definition name
        ((current.take i).map (·.shift) ++ [.bvar 0] ++ (current.drop (i + 1)).map (·.shift))
      let next := current.set i r.value
      proof := joinEqualities t (.definition name current) (.definition name next) proof
        (mkEqCongr (.lam `x hole) value r.value r.proof)
      current := next
    return ⟨.definition name current, proof⟩

  /-- Apply the checked substitution theorem while keeping the definition closed. -/
  private partial def substDefinition (L f : Term) (d : DefinitionInfo) (values : List Term) :
      CalculationM (Option Calculation) := do
    unless L == applyDefinition (d.language ++ `language) do return none
    let some theoremName := d.substitution | return none
    let arguments := values.zipIdx.map fun (value, i) =>
      if let some p := d.syntaxAt? i then p.transport L f value else value
    return some ⟨.definition d.name arguments,
      applyTheorem theoremName [] (f :: values)⟩

  private partial def calculateHead (t : Term) : CalculationM Calculation := do
    let opened := (← get).opened
    unless opened.isEmpty do
      if let (.definition name _, _) := getAppFnArgs t then
        if opened.contains name then
          if let some next ← unfoldOnce t then return ← follow t next (.forallElim .eqRefl t)
    if let some (d, values) ← closedDefinition? t then
      let result ← calculateDefinition t d values
      if result.value != t then return ← follow t result.value result.proof
      return result
    if let .definition name values := t then
      if (closedTermRules.getState (← getEnv)).any (·.symbol == name) ||
          (formulaBuilders.getState (← getEnv)).any (·.symbol == name) then
        if let some d := (definitions.getState (← getEnv)).find? (·.name == name) then
          let result ← calculateDefinition t d values
          if result.value != t then return ← follow t result.value result.proof
    if let some result ← calculationRule t then
      return ← follow t result.value result.proof
    let (head, args) := getAppFnArgs t
    if let .succ := head then
      if let [a] := args then
        if let some n := numeralValue? a then return ⟨numeral (n + 1), .forallElim .eqRefl t⟩
    let .definition name fs := head | return ⟨t, .forallElim .eqRefl t⟩
    let normalizeTerm (value : Term) : CommandElabM (Term × Proof) := do
      let result ← (calculate value).run' {}
      return (result.value, result.proof)
    if name == `FOL.consSubst then
      if let [value, tail] := fs then
        if let [index] := args then
          if let some i := numeralValue? index then
            if i == 0 then
              return ← follow t value (applyTheorem `FOL.consSubst_zero [] [value, tail])
            return ← follow t (.app tail (numeral (i - 1)))
              (applyTheorem `FOL.consSubst_succ [numeral (i - 1)] [value, tail])
    if name == `FOL.shiftSubst then
      if let [L, offset] := fs then
        if let [index] := args then
          let result := applyDefinition `FOL.Term.var [L, applyDefinition `add [index, offset]]
          return ← follow t result (.forallElim .eqRefl t)
    if name == `FOL.liftSubst then
      if let [f] := fs then
        if let [L, depth, index] := args then
          let substitutionFunction := applyDefinition name [L, depth] [f]
          if let some result ← normalizeSubstitution normalizeTerm L substitutionFunction then
            return ← follow t (.app (result.substitution.encode L) index)
              (.forallElim result.proof index)
    if name == `FOL.Term.shift then
      if let [L, depth, value] := args then
        return ← follow t (applyDefinition `FOL.Term.subst [L, value]
          [applyDefinition `FOL.shiftSubst [] [L, depth]])
          (applyTheorem `FOL.Term.shift_eq_subst_shiftSubst [L, depth, value])
    if name == `FOL.Formula.shift then
      if let [L, A] := args then
        return ← follow t (applyDefinition `FOL.Formula.subst [L, A]
          [SubstitutionView.encode L ⟨[], 1⟩])
          (applyTheorem `FOL.Formula.shift_eq_subst [L, A])
    if name == `FOL.Formula.instantiate then
      if let [L, A, value] := args then
        return ← follow t (applyDefinition `FOL.Formula.subst [L, A]
          [SubstitutionView.encode L ⟨[value], 0⟩])
          (applyTheorem `FOL.Formula.instantiate_eq_subst [L, A, value])
    if name == `FOL.Formula.subst then
      if let [f] := fs then
        if let [L, A] := args then
          if let some normalized ← normalizeSubstitution normalizeTerm L f then
            let canonical := normalized.substitution.encode L
            if canonical != f then
              let equation := Core.Proof.forallElim
                (applyTheorem `FOL.Formula.subst_congr [L] [f, canonical]
                  [normalized.proof]) A
              return ← follow t (applyDefinition name [L, A] [canonical]) equation
            if normalized.substitution == ⟨[], 0⟩ then
              return ⟨A, applyTheorem `FOL.Formula.subst_shiftSubst_zero [L, A]⟩
            if let some ([g], [_, B]) := named A name then
              if let some inner ← normalizeSubstitution normalizeTerm L g then
                let composition ← composeSubstitutions normalizeTerm L
                  normalized.substitution inner.substitution
                let composed := Term.lam `i
                  (applyDefinition `FOL.Term.subst [L.shift, .app g.shift (.bvar 0)] [f.shift])
                let middle := applyDefinition name [L, B] [composed]
                let result := applyDefinition name [L, B] [composition.substitution.encode L]
                let equation := Core.Proof.forallElim
                  (applyTheorem `FOL.Formula.subst_congr [L]
                    [composed, composition.substitution.encode L] [composition.proof]) B
                return ← follow t result (mkEqTrans t middle result
                  (applyTheorem `FOL.Formula.subst_comp [L, B] [f, g]) equation)
          if let some (d, values) ← closedDefinition? A then
            if d.isFormula then
              if (← normalizeSubstitution normalizeTerm L f).isSome then
                if let some result ← substDefinition L f d values then
                  return ← follow t result.value result.proof
            -- The substitution changes the meaning of the PRA parameters: open the definition.
            if let some next ← unfoldOnce A then
              return ← follow t (applyDefinition name [L, next] [f]) (.forallElim .eqRefl t)
          if let some (_, []) := named A `FOL.Formula.falsum then
            return ⟨A, applyTheorem `FOL.Formula.subst_falsum [L] [f]⟩
          if let some (_, [_, x, y]) := named A `FOL.Formula.equal then
            return ← follow t (applyDefinition `FOL.Formula.equal
              [L, applyDefinition `FOL.Term.subst [L, x] [f],
                applyDefinition `FOL.Term.subst [L, y] [f]])
              (applyTheorem `FOL.Formula.subst_equal [L, x, y] [f])
          if let some (_, [a, b]) := named A `FOL.Formula.imp then
            return ← follow t (applyDefinition `FOL.Formula.imp
              [applyDefinition name [L, a] [f], applyDefinition name [L, b] [f]])
              (applyTheorem `FOL.Formula.subst_imp [L, a, b] [f])
          if let some (_, [a]) := named A `FOL.Formula.all then
            return ← follow t (applyDefinition `FOL.Formula.all
              [applyDefinition name [L, a]
                [applyDefinition `FOL.liftSubst [L, numeral 1] [f]]])
              (applyTheorem `FOL.Formula.subst_all [L, a] [f])
          if (← formulaBuilderArguments L A).isSome || (named A `FOL.Formula.rel).isSome then
            if let some next ← unfoldOnce t then return ← follow t next (.forallElim .eqRefl t)
    if let some ns := args.mapM numeralValue? then
      if ns.all (· ≤ 4096) then
        if let some n := smallArithmetic name ns then return ⟨numeral n, .forallElim .eqRefl t⟩
    if name == `sub then
      if let [a, b] := args then
        if let some x := numeralValue? a then
          if let some y := numeralValue? b then
            if y == 0 then return ⟨a, applyTheorem `sub_zero [a]⟩
            if x == 0 then return ⟨numeral 0, applyTheorem `zero_sub [b]⟩
            return ← follow t (applyDefinition `sub [numeral (x - 1), numeral (y - 1)])
              (applyTheorem `succ_sub_succ [numeral (x - 1), numeral (y - 1)])
    if name == `eqb then
      if let [a, b] := args then
        if a == b then return ⟨numeral 1, applyTheorem `eqb_self [a]⟩
    if name == `iter then
      if let [f] := fs then
        if let [n, x] := args then
          if let some k := numeralValue? n then
            if k == 0 then return ⟨x, applyTheorem `iter_zero [x] [f]⟩
            let previous := applyDefinition `iter [numeral (k - 1), x] [f]
            return ← follow t (.app f previous)
              (applyTheorem `iter_succ [numeral (k - 1), x] [f])
    if name == `Tuple.map then
      if let [f] := fs then
        if let [n, xs] := args then
          if numeralValue? n == some 0 then
            return ⟨numeral 0, applyTheorem `Tuple.map_zero [xs] [f]⟩
          if numeralValue? n == some 1 then
            return ← follow t (.app f xs) (applyTheorem `Tuple.map_one [xs] [f])
          if numeralValue? n == some 2 then
            if let some (_, [x, y]) := named xs `pair then
              return ← follow t (applyDefinition `pair [.app f x, .app f y])
                (applyTheorem `Tuple.map_two [x, y] [f])
          if let some k := numeralValue? n then
            if k > 2 then
              if let some (_, [x, rest]) := named xs `pair then
                return ← follow t (applyDefinition `pair
                  [.app f x, applyDefinition `Tuple.map [numeral (k - 1), rest] [f]])
                  (applyTheorem `Tuple.map_pair_succ [numeral (k - 2), x, rest] [f])
    if name == `Tuple.max then
      if let [n, xs] := args then
        if numeralValue? n == some 1 then
          return ⟨xs, applyTheorem `Tuple.max_one [xs]⟩
        if numeralValue? n == some 2 then
          if let some (_, [x, y]) := named xs `pair then
            return ← follow t (applyDefinition `max [x, y]) (applyTheorem `Tuple.max_two [x, y])
        if numeralValue? n == some 3 then
          if let some (_, [x, yz]) := named xs `pair then
            if let some (_, [y, z]) := named yz `pair then
              return ← follow t (applyDefinition `max [applyDefinition `max [x, y], z])
                (applyTheorem `Tuple.max_three [x, y, z])
    if name == `FOL.Formula.allN then
      if let [n, a] := args then
        if let some k := numeralValue? n then
          if k == 0 then return ⟨a, applyTheorem `FOL.Formula.allN_zero [a]⟩
          let value := applyDefinition `FOL.Formula.all
            [applyDefinition `FOL.Formula.allN [numeral (k - 1), a]]
          return ← follow t value (applyTheorem `FOL.Formula.allN_succ [numeral (k - 1), a])
    if name == `unpairLeft || name == `unpairRight then
      if let [p] := args then
        if let some (_, [a, b]) := named p `pair then
          let (value, lemma) := if name == `unpairLeft then (a, `unpairLeft_pair)
            else (b, `unpairRight_pair)
          return ⟨value, applyTheorem lemma [a, b]⟩
    if name == `Sequence.length then
      if let [xs] := args then
        if let some (_, []) := named xs `Sequence.nil then
          return ⟨numeral 0, applyTheorem `Sequence.length_nil⟩
        if let some (_, [x, rest]) := named xs `Sequence.cons then
          return ← follow t (.app .succ (applyDefinition `Sequence.length [rest]))
            (applyTheorem `Sequence.length_cons [x, rest])
    if name == `Sequence.get then
      if let [xs, index] := args then
        if let some (_, [x, rest]) := named xs `Sequence.cons then
          if let some k := numeralValue? index then
            if k == 0 then return ⟨x, applyTheorem `Sequence.get_cons_zero [x, rest]⟩
            return ← follow t (applyDefinition `Sequence.get [rest, numeral (k - 1)])
              (applyTheorem `Sequence.get_cons_succ [x, rest, numeral (k - 1)])
    let fields := [`FOL.Language.constants, `FOL.Language.functions, `FOL.Language.relations,
      `FOL.Language.constantFamilyCount, `FOL.Language.functionFamilies,
      `FOL.Language.relationFamilies]
    if let some i := fields.idxOf? name then
      if let [L] := args then
        let expanded := (← unfoldOnce L).getD L
        if let some (_, values) := named expanded `FOL.Language.make then
          if let some value := values[i]? then
            let lemma := name.getPrefix ++ Name.mkSimple (name.getString! ++ "_make")
            let mid := applyDefinition name [expanded]
            return ← follow t value (mkEqTrans t mid value (.forallElim .eqRefl t)
              (applyTheorem lemma values))
    if name == `FOL.Language.functionSymbolArity || name == `FOL.Language.relationSymbolArity then
      if let [L, j] := args then
        let isRelation := name == `FOL.Language.relationSymbolArity
        let language := `FOL.Language
        let kind := if isRelation then "relation" else "function"
        if let some (b, k) := familyMemberParts? isRelation j then
          let families := applyDefinition (language ++ Name.mkSimple (kind ++ "Families")) [L]
          let count := applyDefinition (language ++ Name.mkSimple (kind ++ "FamilyCount")) [L]
          let arity := applyDefinition `Sequence.get [families, b]
          let lemma := name.getPrefix ++ Name.mkSimple (name.getString! ++ "_familyMember")
          return ← follow t (.app .succ arity)
            (applyTheorem lemma [L, b, k] [] [← lessProof b count])
        if (numeralValue? j).isSome then
          let entries := applyDefinition
            (if isRelation then `FOL.Language.relations else `FOL.Language.functions) [L]
          let count := applyDefinition (language ++ Name.mkSimple (kind ++ "Count")) [L]
          let lemma := name.getPrefix ++ Name.mkSimple (name.getString! ++ "_of_lt")
          return ← follow t (.app .succ (applyDefinition `Sequence.get [entries, j]))
            (applyTheorem lemma [L, j] [] [← lessProof j count])
    if name == `FOL.Formula.equalPremises then
      if let [L, n, xs, ys, A] := args then
        if numeralValue? n == some 1 then
          return ← follow t
            (applyDefinition `FOL.Formula.imp [applyDefinition `FOL.Formula.equal [L, xs, ys], A])
            (applyTheorem `FOL.Formula.equalPremises_one [L, xs, ys, A])
        if numeralValue? n == some 2 then
          if let some (_, [x, y]) := named xs `pair then
            if let some (_, [u, v]) := named ys `pair then
              let result := applyDefinition `FOL.Formula.imp
                [applyDefinition `FOL.Formula.equal [L, x, u],
                applyDefinition `FOL.Formula.imp [applyDefinition `FOL.Formula.equal [L, y, v], A]]
              return ← follow t result
                (applyTheorem `FOL.Formula.equalPremises_two [L, x, y, u, v, A])
    if name == `FOL.Formula.substWithDepth then
      if let [f] := fs then
        if let [L, A, d] := args then
          if let some (_, []) := named A `FOL.Formula.falsum then
            return ⟨A, applyTheorem `FOL.Formula.substWithDepth_falsum [L, d] [f]⟩
          if let some (_, [_, x, y]) := named A `FOL.Formula.equal then
            let result := applyDefinition `FOL.Formula.equal
              [L, applyDefinition `FOL.Term.subst [L, x] [.app f d],
                applyDefinition `FOL.Term.subst [L, y] [.app f d]]
            return ← follow t result
              (applyTheorem `FOL.Formula.substWithDepth_equal [L, x, y, d] [f])
          if let some (_, [_, j, xs]) := named A `FOL.Formula.rel then
            let hj ← symbolProof L j true
            let result := applyDefinition `FOL.Formula.rel [L, j,
              applyDefinition `Tuple.map
                [applyDefinition `FOL.Language.relationSymbolArity [L, j], xs]
                [applyDefinition `FOL.Term.subst [L] [.app f d]]]
            return ← follow t result
              (applyTheorem `FOL.Formula.substWithDepth_rel [L, j, xs, d] [f] [hj])
          if let some (_, [a, b]) := named A `FOL.Formula.imp then
            let result := applyDefinition `FOL.Formula.imp
              [applyDefinition name [L, a, d] [f], applyDefinition name [L, b, d] [f]]
            return ← follow t result (applyTheorem `FOL.Formula.substWithDepth_imp [L, a, b, d] [f])
          if let some (_, [a]) := named A `FOL.Formula.all then
            let result := applyDefinition `FOL.Formula.all
              [applyDefinition name [L, a, .app .succ d] [f]]
            return ← follow t result (applyTheorem `FOL.Formula.substWithDepth_all [L, a, d] [f])
          if (← closedDefinition? A).isSome then
            if let some next ← unfoldOnce A then
              return ← follow t (applyDefinition name [L, next, d] [f]) (.forallElim .eqRefl t)
    if name == `FOL.Term.subst then
      if let [f] := fs then
        if let [L, a] := args then
          let (head, values) := getAppFnArgs a
          if let .definition symbol parameters := head then
            if let some rule := (closedTermRules.getState (← getEnv)).find? (fun r =>
                r.symbol == symbol && r.language == L && r.parameters == parameters.length &&
                  r.arity == parameters.length + values.length) then
              return ⟨a, applyTheorem rule.theoremName (parameters ++ values) [f]⟩
          if let some (d, values) ← closedDefinition? a then
            unless d.isFormula do
              if let some result ← substDefinition L f d values then
                return ← follow t result.value result.proof
              if let some next ← unfoldOnce a then
                return ← follow t (applyDefinition name [L, next] [f]) (.forallElim .eqRefl t)
          if let some (_, [_, i]) := named a `FOL.Term.var then
            return ← follow t (.app f i) (applyTheorem `FOL.Term.subst_var [L, i] [f])
          if let some (_, [_, i]) := named a `FOL.Term.const then
            let hi ← constantProof L i
            return ⟨a, applyTheorem `FOL.Term.subst_const [L, i] [f] [hi]⟩
          if let some (_, [_, j, xs]) := named a `FOL.Term.app then
            let arity := applyDefinition `FOL.Language.functionSymbolArity [L, j]
            let ar ← calculate arity
            let hj ← symbolProof L j
            if numeralValue? ar.value == some 1 then
              return ← follow t
                (applyDefinition `FOL.Term.app [L, j, applyDefinition name [L, xs] [f]])
                (applyTheorem `FOL.Term.subst_app_one [L, j, xs] [f] [hj, ar.proof])
            if numeralValue? ar.value == some 2 then
              if let some (_, [x, y]) := named xs `pair then
                return ← follow t (applyDefinition `FOL.Term.app [L, j,
                  applyDefinition `pair
                    [applyDefinition name [L, x] [f], applyDefinition name [L, y] [f]]])
                  (applyTheorem `FOL.Term.subst_app_two [L, j, x, y] [f] [hj, ar.proof])
            return ← follow t (applyDefinition `FOL.Term.app [L, j,
              applyDefinition `Tuple.map [arity, xs] [applyDefinition name [L] [f]]])
              (applyTheorem `FOL.Term.subst_app [L, j, xs] [f] [hj])
    if name == `FOL.Formula.bound then
      if let [L, A] := args then
        if let some (_, []) := named A `FOL.Formula.falsum then
          return ⟨numeral 0, applyTheorem `FOL.Formula.bound_falsum [L]⟩
        if let some (_, [_, x, y]) := named A `FOL.Formula.equal then
          return ← follow t
            (applyDefinition `max
              [applyDefinition `FOL.Term.bound [L, x],
                applyDefinition `FOL.Term.bound [L, y]])
            (applyTheorem `FOL.Formula.bound_equal [L, x, y])
        if let some (_, [_, j, xs]) := named A `FOL.Formula.rel then
          let hj ← symbolProof L j true
          let arity := applyDefinition `FOL.Language.relationSymbolArity [L, j]
          return ← follow t (applyDefinition `Tuple.max [arity,
            applyDefinition `Tuple.map [arity, xs] [applyDefinition `FOL.Term.bound [L]]])
            (applyTheorem `FOL.Formula.bound_rel [L, j, xs] [] [hj])
        if let some (_, [a, b]) := named A `FOL.Formula.imp then
          return ← follow t
            (applyDefinition `max [applyDefinition name [L, a], applyDefinition name [L, b]])
            (applyTheorem `FOL.Formula.bound_imp [L, a, b])
        if let some (_, [a]) := named A `FOL.Formula.all then
          return ← follow t (applyDefinition `pred [applyDefinition name [L, a]])
            (applyTheorem `FOL.Formula.bound_all [L, a])
        if (← closedDefinition? A).isSome then
          if let some next ← unfoldOnce A then
            return ← follow t (applyDefinition name [L, next]) (.forallElim .eqRefl t)
    if name == `FOL.Term.bound then
      if let [L, a] := args then
        if (← closedDefinition? a).isSome then
          if let some next ← unfoldOnce a then
            return ← follow t (applyDefinition name [L, next]) (.forallElim .eqRefl t)
        if let some (_, [_, j]) := named a `FOL.Term.const then
          let hj ← constantProof L j
          return ⟨numeral 0, applyTheorem `FOL.Term.bound_const [L, j] [] [hj]⟩
        if let some (_, [_, i]) := named a `FOL.Term.var then
          return ← follow t (.app .succ i) (applyTheorem `FOL.Term.bound_var [L, i])
        if let some (_, [_, j, xs]) := named a `FOL.Term.app then
          let ar ← calculate (applyDefinition `FOL.Language.functionSymbolArity [L, j])
          let hj ← symbolProof L j
          if numeralValue? ar.value == some 1 then
            return ← follow t (applyDefinition name [L, xs])
              (applyTheorem `FOL.Term.bound_app_one [L, j, xs] [] [hj, ar.proof])
          if numeralValue? ar.value == some 2 then
            if let some (_, [x, y]) := named xs `pair then
              return ← follow t
                (applyDefinition `max
                  [applyDefinition name [L, x], applyDefinition name [L, y]])
                (applyTheorem `FOL.Term.bound_app_two [L, j, x, y] [] [hj, ar.proof])
          let arity := applyDefinition `FOL.Language.functionSymbolArity [L, j]
          return ← follow t (applyDefinition `Tuple.max [arity,
            applyDefinition `Tuple.map [arity, xs] [applyDefinition name [L]]])
            (applyTheorem `FOL.Term.bound_app [L, j, xs] [] [hj])
    let registered := (closedTermRules.getState (← getEnv)).any (·.symbol == name) ||
      (formulaBuilders.getState (← getEnv)).any (·.symbol == name)
    if !registered && (definitions.getState (← getEnv)).any (fun d => d.name == name) then
      if let some next ← unfoldOnce t then return ← follow t next (.forallElim .eqRefl t)
    if transparent name || name.getString! == "isAxiom" || name.getString! == "formula" ||
        name.getString! == "isInstance" then
      if let some next ← unfoldOnce t then return ← follow t next (.forallElim .eqRefl t)
    return ⟨t, .forallElim .eqRefl t⟩

end

/-- Open the definition at the head of the formula code `t`. Returns the body of the definition
with the arguments in place, keeping definitions inside the body closed, together with a proof
that `t` equals it. -/
def openHead (t : Term) : CommandElabM (Option Calculation) := do
  let some (d, _) ← definitionApplication? t | return none
  unless d.isFormula do return none
  let some next ← unfoldOnce t | return none
  let result ← (calculate next).run' {}
  return some ⟨result.value,
    joinEqualities t next result.value (.forallElim .eqRefl t) result.proof⟩

/-- Calculate `t` with the definitions `names` opened wherever they occur. -/
def openDefinitions (names : List Name) (t : Term) : CommandElabM Calculation :=
  (calculate t).run' { opened := names }

/-- From proofs of `olds[i] = news[i]`, a proof of `assemble olds = assemble news`. -/
private def congruenceProof (assemble : List Term → Term) (olds news : List Term)
    (proofs : List Proof) : Proof := Id.run do
  let source := assemble olds
  let mut current := source
  let mut proof := Proof.forallElim .eqRefl source
  for ((old, new, step), i) in (olds.zip (news.zip proofs)).zipIdx do
    if old == new then continue
    let hole := assemble
      ((news.take i).map (·.shift) ++ [Term.bvar 0] ++ (olds.drop (i + 1)).map (·.shift))
    let next := assemble (news.take (i + 1) ++ olds.drop (i + 1))
    proof := joinEqualities source current next proof (mkEqCongr (.lam `x hole) old new step)
    current := next
  return proof

/-- Bring two calculated formula codes to a common form by opening definitions only at the places
where the codes differ. A definition that meets a different formula is opened. Two different
definitions are opened in turn, starting with the one declared later. Two uses of the same
definition are compared argument by argument, and both are opened when the arguments do not
agree. Returns the common form `c` with proofs of `a = c` and `b = c`, or `none` when the codes
differ at a place without a definition. -/
partial def reconcile (a b : Term) (fuel : Nat := 64) :
    CalculationM (Option (Term × Proof × Proof)) := do
  if a == b then return some (a, .forallElim .eqRefl a, .forallElim .eqRefl a)
  if fuel == 0 then return none
  let opened (t : Term) : CalculationM (Option Calculation) := do
    let some next ← unfoldOnce t | return none
    let result ← calculate next
    return some ⟨result.value,
      joinEqualities t next result.value (.forallElim .eqRefl t) result.proof⟩
  let openLeft : CalculationM (Option (Term × Proof × Proof)) := do
    let some oa ← opened a | return none
    let some (c, pa, pb) ← reconcile oa.value b (fuel - 1) | return none
    return some (c, joinEqualities a oa.value c oa.proof pa, pb)
  let openRight : CalculationM (Option (Term × Proof × Proof)) := do
    let some ob ← opened b | return none
    let some (c, pa, pb) ← reconcile a ob.value (fuel - 1) | return none
    return some (c, pa, joinEqualities b ob.value c ob.proof pb)
  let entrywise (assemble : List Term → Term) (xs ys : List Term) :
      CalculationM (Option (Term × Proof × Proof)) := do
    let mut common := []
    let mut proofs := []
    let mut proofs' := []
    for (x, y) in xs.zip ys do
      let some (c, px, py) ← reconcile x y (fuel - 1) | return none
      common := common ++ [c]
      proofs := proofs ++ [px]
      proofs' := proofs' ++ [py]
    return some (assemble common, congruenceProof assemble xs common proofs,
      congruenceProof assemble ys common proofs')
  match ← closedDefinition? a, ← closedDefinition? b with
  | some (d, values), some (e, values') =>
    if d.name == e.name then
      if let some result ← entrywise (.definition d.name) values values' then
        return some result
      let some oa ← opened a | return none
      let some ob ← opened b | return none
      let some (c, pa, pb) ← reconcile oa.value ob.value (fuel - 1) | return none
      return some (c, joinEqualities a oa.value c oa.proof pa,
        joinEqualities b ob.value c ob.proof pb)
    let all := definitions.getState (← getEnv)
    let position (name : Name) := (all.findIdx? (·.name == name)).getD 0
    if position d.name < position e.name then openRight else openLeft
  | some _, none => openLeft
  | none, some _ => openRight
  | none, none =>
    let (f, xs) := getAppFnArgs a
    let (g, ys) := getAppFnArgs b
    unless xs.length == ys.length do return none
    match f, g with
    | .definition m fs, .definition n gs =>
      unless m == n && fs.length == gs.length do return none
      let count := fs.length
      entrywise (fun ts => (ts.drop count).foldl .app (.definition m (ts.take count)))
        (fs ++ xs) (gs ++ ys)
    | _, _ =>
      unless f == g && !xs.isEmpty do return none
      entrywise (fun ts => ts.tail.foldl .app ts.head!) (f :: xs) (g :: ys)

/-- Prove `a = b` for two formula codes that agree once some definitions are opened. Only the
definitions at the places where the codes differ are opened. -/
def calculateOpeningEquality (a b : Term) : CommandElabM (Option Proof) := do
  if ← opensDefinitions then return none
  let action : CalculationM (Option Proof) := do
    let ra ← calculate a
    let rb ← calculate b
    let some (c, pa, pb) ← reconcile ra.value rb.value | return none
    let pa := joinEqualities a ra.value c ra.proof pa
    let pb := joinEqualities b rb.value c rb.proof pb
    return some (if c == b then pa else joinEqualities a c b pa (mkEqSymm b c pb))
  let (result, state) ← action.run { cache := calculations.getState (← getEnv) }
  modifyEnv (calculations.setState · state.cache)
  return result

private def calculateStoredEquality (a b : Term) : CommandElabM Proof := do
  let store := if ← opensDefinitions then openCalculations else calculations
  let (proof, state) ← (calculateEquality a b).run { cache := store.getState (← getEnv) }
  modifyEnv (store.setState · state.cache)
  return proof

/-- Prove `a = b` by calculating both sides. Definitions stay closed where their substitution
theorems apply. When the two results differ, the definitions at the places where they differ
are opened; when that does not settle it, the calculation runs again with every definition
opened. -/
def calculateClosedEquality (a b : Term) : CommandElabM Proof := do
  if ← opensDefinitions then return ← calculateStoredEquality a b
  try calculateStoredEquality a b
  catch error =>
    if error.isInterrupt then throw error
    if let some proof ← calculateOpeningEquality a b then return proof
    withOpenDefinitions (calculateStoredEquality a b)

end LeanPRA.Library.FOL.DSL
