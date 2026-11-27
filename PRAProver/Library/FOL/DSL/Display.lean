module

public meta import PRAProver.Library.FOL.DSL.Tactic.Context

/-!
# Display of provability statements

A statement `Sequent L T Γ C` of a declared theory is displayed as a sequent,

```
T;
h₁ : A₁
h₂ : A₂
⊢ C
```

with one assumption per line, the oldest first, and the formulas in FOL notation. Without
assumptions it is displayed as `T ⊢ C`, the form in which theorems are stated. This applies to
every goal, hypothesis, and message.

- `termSyntax` and `formulaSyntax` format a term or formula tree in FOL notation.
- `TermDisplay` lets a language module supply notation for its constants and functions.
- `displayProvable` is the display function registered for `FOL.Provable` and `FOL.Sequent`.

The names of the assumptions are read from their name markers. An object variable is shown by
the local PRA name that stands for its code. A bound variable receives a fresh name, since a
formula code stores de Bruijn indices rather than binder names. The derived connectives `¬`,
`∧`, `∨`, `∃`, and `↔` are shown whenever a formula has their shape. A subformula or subterm
given by an opaque PRA expression is shown as a splice `${…}`. Named formula codes stay visible
even when their definitions have no substitution theorem. Rendering leaves the tactic goal
unchanged.
-/

public meta section

namespace PRAProver.Library.FOL.DSL

open Lean Elab Command PRAProver.Core PRAProver.Surface
open PRAProver.Library.Tactic.Construction
open PRAProver.Library.Tactic (markName markedName? unmarked)

declare_syntax_cat folAssumption
syntax ident " : " folFormula : folAssumption
/-- A sequent as it is displayed. It is not accepted as input. -/
syntax:20 (name := sequentDisplay) atomic(ident ";"
  ppDedent(ppLine (folAssumption ppLine)+ ppRealGroup("⊢ " folFormula))) : praExpr

private def spliceNode (kind : Name) (value : Syntax) (arguments : Option (Array Syntax)) :
    Syntax :=
  let base := #[mkAtom "$", mkAtom "{", value, mkAtom "}"]
  match arguments with
  | none => .node .none kind base
  | some args => .node .none kind
    (base ++ #[mkAtom "[", Syntax.mkSep args (mkAtom ","), mkAtom "]"])

private def parenthesizedTerm (level wanted : Nat) (t : TSyntax `folTerm) :
    CommandElabM (TSyntax `folTerm) :=
  if level < wanted then `(folTerm| ($t)) else pure t

/-- A language-specific term display receives a printer for its children. It returns syntax
with its precedence, or `none` to use the ordinary symbol application. -/
abbrev TermDisplay := LanguageInfo → (TermView → Nat → CommandElabM (TSyntax `folTerm)) →
  TermView → CommandElabM (Option (Nat × TSyntax `folTerm))

/-- `@[fol_term_display symbol]` registers notation for a constant or function named `symbol`.
The display function can inspect the language and arity before choosing a notation. -/
unsafe initialize termDisplayAttribute : KeyedDeclsAttribute TermDisplay ←
  KeyedDeclsAttribute.init {
    builtinName := `builtin_fol_term_display
    name := `fol_term_display
    descr := "display of a first-order term in a language's notation"
    valueTypeName := ``TermDisplay
    evalKey := fun _ stx => return (← Attribute.Builtin.getIdent stx).getId.eraseMacroScopes
  }

/-- An argument of the application form for a PRA value: a name or a numeral as it is, any
other expression as a braced splice. -/
private def argumentSyntax (value : TSyntax `praExpr) : CommandElabM (TSyntax `folArg) := do
  match value with
  | `(praExpr| $id:ident) => `(folArg| $(← `(folFormula| $id:ident)):folFormula)
  | `(praExpr| $n:num) => `(folArg| $n:num)
  | _ => `(folArg| $(← `(folFormula| ${$value:praExpr})):folFormula)

/-- Print a folded definition with its ordinary arguments after the name and its result slots
in a comma-separated list. Parenthesize the ordinary application before slots or where the
surrounding syntax requires an atomic argument. -/
private def namedDefinitionSyntax (L : LanguageInfo) (names : Names) (isFormula : Bool)
    (value : Core.Term) (arguments : List TermView) (level : Nat)
    (showTerm : TermView → Nat → CommandElabM (TSyntax `folTerm)) :
    CommandElabM (Option Syntax) := do
  let some (d, values) ← appliedDefinition? value | return none
  unless d.language == L.name && d.isFormula == isFormula && d.substitution.isSome &&
      arguments.length == d.termPositions.length do return none
  if d.syntaxParameters.any (fun p => p.isFormula || p.arity > 0) then return none
  -- A view of a named application has a numbered placeholder at each term position.
  unless d.termPositions.zipIdx.all (fun (pos, i) =>
      values[pos]? == some (applyDefinition `FOL.Term.var [languageTerm L, numeral i])) do
    return none
  let name := mkIdent (← relativeName d.name names.used)
  let terms := d.termPositions.zip arguments
  let mut slots := #[]
  let mut actuals := #[]
  for ((binder, value), i) in (d.binders.toList.zip values).zipIdx do
    if d.positional.contains binder then
      let some t := terms.lookup i | return none
      slots := slots.push (← showTerm t 0)
      continue
    let mut argument ← if let some t := terms.lookup i then do
      let t ← showTerm t 1024
      pure (⟨mkNode ``formulaArg #[mkNode ``formulaTerm #[t.raw]]⟩ : TSyntax `folArg)
    else argumentSyntax (← delabTerm names value)
    -- Built directly: in a quotation, `(x := a)` would also parse as a PRA named argument.
    if d.implicit.contains binder then
      argument := ⟨mkNode ``namedArg
        #[mkAtom "(", mkIdent binder, mkAtom ":=", argument, mkAtom ")"]⟩
    actuals := actuals.push argument.raw
  if actuals.isEmpty then
    if slots.isEmpty then
      if isFormula then return some (← `(folFormula| $name:ident)).raw
      return some (← `(folTerm| $name:ident)).raw
    if isFormula then return some (← `(folFormula| $name:ident($slots,*))).raw
    return some (← `(folTerm| $name:ident($slots,*))).raw
  if slots.isEmpty && level ≤ Parser.leadPrec then
    let kind := if isFormula then ``formulaApplied else ``termApplied
    return some (mkNode kind #[name.raw, mkNullNode actuals])
  let application := #[mkAtom "(", name.raw, mkNullNode actuals, mkAtom ")"]
  if slots.isEmpty then
    let kind := if isFormula then ``formulaApplication else ``termApplication
    return some (.node .none kind application)
  let kind := if isFormula then ``formulaApplicationSlots else ``termApplicationSlots
  return some (.node .none kind
    (application ++ #[mkAtom "(", Syntax.mkSep slots (mkAtom ","), mkAtom ")"]))

/-- Print a term tree in FOL notation. `level` is the precedence the position requires. -/
partial def termSyntax (L : LanguageInfo) (names : Names) (rename : Name → Name)
    (t : TermView) (level : Nat := 0) : CommandElabM (TSyntax `folTerm) := do
  let symbol : Option Name := match t with
    | .constant i => L.constants[i]?
    | .app i _ => L.functions[i]?.map (·.1)
    | _ => none
  if let some symbol := symbol then
    for display in termDisplayAttribute.getEntries (← getEnv) symbol do
      if let some (precedence, shown) ←
          display.value L (fun child level => termSyntax L names rename child level) t then
        return ← parenthesizedTerm precedence level shown
  match t with
  | .var x => `(folTerm| $(mkIdent (rename x)):ident)
  | .constant i => `(folTerm| $(mkIdent (L.constants[i]?.getD (Name.num `constant i))):ident)
  | .parameter _ _ => throwError "uninstantiated term parameter"
  | .app i args =>
    let name := (L.functions[i]?.map (·.1)).getD (Name.num `function i)
    let args ← args.toArray.mapM (termSyntax L names rename ·)
    `(folTerm| $(mkIdent name):ident($args,*))
  | .indexedConst i k =>
    let some family := L.constantFamilies[i]? | throwError "invalid constant family number"
    let indices ← (← tupleEntries family.indexArity k).toArray.mapM (delabTerm names)
    `(folTerm| $(mkIdent family.name):ident[$indices,*])
  | .indexedApp i k args =>
    let some family := L.functionFamilies[i]? | throwError "invalid family number"
    let args ← args.toArray.mapM (termSyntax L names rename ·)
    let indices ← (← tupleEntries family.indexArity k).toArray.mapM (delabTerm names)
    `(folTerm| $(mkIdent family.name):ident[$indices,*]($args,*))
  | .code _ value arguments => do
    if let some shown ← namedDefinitionSyntax L names false value arguments level
        (fun t prec => termSyntax L names rename t prec) then return ⟨shown⟩
    return ⟨spliceNode ``termSplice (← delabTerm names value) none⟩

private def parenthesizedFormula (level wanted : Nat) (a : TSyntax `folFormula) :
    CommandElabM (TSyntax `folFormula) :=
  if level < wanted then `(folFormula| ($a)) else pure a

/-- Print a formula tree in FOL notation. `used` holds the variable names already visible, and
`level` is the precedence the position requires. -/
partial def formulaSyntax (L : LanguageInfo) (names : Names) (rename : Name → Name)
    (used : List Name) (a : FormulaView) (level : Nat := 0) :
    CommandElabM (TSyntax `folFormula) := do
  let term (t : TermView) := termSyntax L names rename t
  -- Adjacent quantifiers of one kind are shown with one quantifier symbol.
  let quantified (x : Name) (body : FormulaView) (existential : Bool) := do
    let mut x := x
    let mut body := body
    let mut used := used
    let mut renamed : List (Name × Name) := []
    let mut binders : Array Ident := #[]
    repeat
      let stem := if x.eraseMacroScopes.isAnonymous then `x else x.eraseMacroScopes
      let mut candidate := stem
      let mut i := 0
      while used.contains candidate do
        i := i + 1
        candidate := stem.appendAfter (toString i)
      used := candidate :: used
      renamed := (x, candidate) :: renamed
      binders := binders.push (mkIdent candidate)
      match existential, body with
      | false, .all y b =>
        x := y
        body := b
      | true, .imp (.all y (.imp b .falsum)) .falsum =>
        x := y
        body := b
      | _, _ => break
    let pairs := renamed
    let inner ← formulaSyntax L names (fun n => (pairs.lookup n).getD (rename n)) used body
    let quantifier ← if existential then `(folFormula| ∃ $binders:ident*, $inner:folFormula)
      else `(folFormula| ∀ $binders:ident*, $inner:folFormula)
    parenthesizedFormula 1 level quantifier
  -- An equivalence is the conjunction of the two implications.
  if let .imp (.imp (.imp b c) (.imp (.imp c' b') .falsum)) .falsum := a then
    if b.equiv b' && c.equiv c' then
      let b ← formulaSyntax L names rename used b 21
      let c ← formulaSyntax L names rename used c 21
      return ← parenthesizedFormula 20 level (← `(folFormula| $b:folFormula ↔ $c:folFormula))
  match a with
  | .falsum => `(folFormula| ⊥)
  | .equal s t =>
    let s ← term s
    let t ← term t
    parenthesizedFormula 50 level (← `(folFormula| $s:folTerm = $t:folTerm))
  | .relation i args =>
    let name := (L.relations[i]?.map (·.1)).getD (Name.num `relation i)
    let args ← args.toArray.mapM term
    `(folFormula| $(mkIdent name):ident($args,*))
  | .indexedRelation i k args =>
    let some family := L.relationFamilies[i]? | throwError "invalid family number"
    let args ← args.toArray.mapM term
    let indices ← (← tupleEntries family.indexArity k).toArray.mapM (delabTerm names)
    `(folFormula| $(mkIdent family.name):ident[$indices,*]($args,*))
  | .parameter i args =>
    let args ← args.toArray.mapM term
    `(folFormula| $(mkIdent (Name.num `parameter i)):ident($args,*))
  | .imp (.all x (.imp body .falsum)) .falsum => quantified x body true
  | .imp (.imp b (.imp c .falsum)) .falsum =>
    let b ← formulaSyntax L names rename used b 36
    let c ← formulaSyntax L names rename used c 35
    parenthesizedFormula 35 level (← `(folFormula| $b:folFormula ∧ $c:folFormula))
  | .imp (.equal s t) .falsum =>
    let s ← term s
    let t ← term t
    parenthesizedFormula 50 level (← `(folFormula| $s:folTerm ≠ $t:folTerm))
  | .imp b .falsum =>
    let b ← formulaSyntax L names rename used b 40
    parenthesizedFormula 40 level (← `(folFormula| ¬ $b:folFormula))
  | .imp (.imp b .falsum) c =>
    let b ← formulaSyntax L names rename used b 31
    let c ← formulaSyntax L names rename used c 30
    parenthesizedFormula 30 level (← `(folFormula| $b:folFormula ∨ $c:folFormula))
  | .imp b c =>
    let b ← formulaSyntax L names rename used b 26
    let c ← formulaSyntax L names rename used c 25
    parenthesizedFormula 25 level (← `(folFormula| $b:folFormula → $c:folFormula))
  | .all x body => quantified x body false
  | .code _ value arguments =>
    if let some shown ← namedDefinitionSyntax L names true value arguments level
        (fun t prec => termSyntax L names rename t prec) then return ⟨shown⟩
    -- For a formula with only result slots, skip the surrounding context after those slots.
    let (head, _) := getAppFnArgs value
    let known : Array DefinitionInfo := definitions.getState (← getEnv)
    let arguments : List TermView := match head with
      | .definition name _ =>
        match known.find? (·.name == name) with
        | some d =>
          if d.language == L.name && d.isFormula && d.resultArity > 0 &&
              d.syntaxParameters.isEmpty then arguments.take d.resultArity
          else arguments
        | none => arguments
      | _ => arguments
    let value ← delabTerm names value
    let arguments ← arguments.reverse.toArray.mapM term
    return ⟨spliceNode (if arguments.isEmpty then ``formulaSplice else ``formulaSpliceApplication)
      value (if arguments.isEmpty then none else some (arguments.map (·.raw)))⟩

/-- Format a provability statement of a declared theory as a sequent in FOL notation. The
statement is read exactly as the tactics read it, so the display shows the code a tactic holds. -/
@[pra_display FOL.Provable, pra_display FOL.Sequent]
def displayProvable : PredicateDisplay := fun names predicate => do
  let depth ← Surface.getMaxDepth
  let some (language, theory, conclusion, context) := provabilityParts? depth predicate |
    return none
  let some T := (theories.getState (← getEnv)).find? fun T =>
      theory == applyDefinition (T.name ++ `isAxiom) && language == languageTerm T.language |
    return none
  let L := T.language
  let context := context.getD emptyList
  let (entries, tail) := listEntries context
  unless tail == emptyList do return none
  -- An object variable is shown by the local name whose value is its code.
  let variables : List (Nat × Name) := names.termAliases.filterMap fun (name, value) =>
    match value with
    | .letE `_folBoundVariable value (.bvar 0) =>
      match getAppFnArgs value with
      | (.definition `FOL.Term.var [], [_, index]) => (numeralValue? index).map (·, name)
      | _ => none
    | _ => none
  let codes := conclusion :: entries.map unmarked
  let (codes, _) ← ((codes.mapM fun c => return (← calculate c).value).run {})
  let closed ← closedDefinitions
  let count := codes.foldl (fun n c => max n (freePositions closed c))
    (variables.foldl (fun n (i, _) => max n (i + 1)) 0)
  -- A position without a local name is shown as `#i`.
  let free := (List.range count).map fun i =>
    (variables.lookup i).getD (Name.mkSimple s!"#{i}")
  let used := free ++ names.used
  let shown (c : Core.Term) : CommandElabM (TSyntax `folFormula) := do
    formulaSyntax L names id used (← readFormula L [] free c)
  let goal ← shown codes.head!
  let theoryName := mkIdent T.name
  if entries.isEmpty then return some (← `(praExpr| $theoryName:ident ⊢ $goal:folFormula))
  let mut assumptions : Array (TSyntax `folAssumption) := #[]
  for (entry, c) in (entries.zip codes.tail!).reverse do
    let name := ((markedName? entry).map (·.1)).getD `_
    assumptions := assumptions.push
      (← `(folAssumption| $(mkIdent name):ident : $(← shown c):folFormula))
  return some (← `(praExpr| $theoryName:ident; $assumptions* ⊢ $goal:folFormula))

end PRAProver.Library.FOL.DSL
