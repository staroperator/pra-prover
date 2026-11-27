module

public meta import PRAProver.Library.FOL.DSL.Schema

/-!
# Language and theory declarations

Source declarations produce numerical PRA definitions. Frontend metadata records symbol names,
axiom templates and their syntax parameters for subsequent proof elaboration.
Relation declarations require positive arity; `relation P of 0` is rejected.
A fixed axiom given by a named sentence uses that sentence's PRA code directly. A compound
axiom gets a `.formula` declaration whose body refers to the definitions used in the axiom.
An extension tests the parent's membership function together with its new axioms.
`T.isAxiom_of_parent` is a checked PRA proof of inclusion of the parent axiom set.

- `TheoryInfo` stores the language, named axioms and formula schemas used by the frontend.
- `declareLanguage` elaborates symbol declarations into the numerical language definition and
  proves the symbol counts, memberships, and arities of the language: `constants_language`,
  `functionCount_language`, `relationCount_language`, the three family counts,
  `isConstant_c`, `isFunction_f` with `f_arity`, `isRelation_R` with `R_arity`, and for a
  family `F` the bound `F_lt` with `isFunction_F` and `F_arity` quantified over the member.
- `declareTheory` elaborates axioms and formula schemas into a numerical membership test, and
  proves each axiom `ax` of the theory as the theorem `T.ax : ∀ ps, r → T ⊢ A`, where `ps` are
  the parameters of the axiom and `r` its restriction. Tactics apply axioms through these
  theorems, like any other theorem with first-order parameters.
-/

public meta section

namespace PRAProver.Library.FOL.DSL

open PRAProver.Library.Tactic.Construction

open Lean hiding Term

open Lean.Elab.Command

open Lean.Elab (throwUnsupportedSyntax)

open PRAProver.Core

structure TheoryInfo where
  name : Name
  language : LanguageInfo
  axioms : Array AxiomInfo := #[]
  parent : Option Name := none
  inherited : Nat := 0
  deriving Inhabited

initialize theories : SimplePersistentEnvExtension TheoryInfo (Array TheoryInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
  }

def findTheory (name : Name) : CommandElabM TheoryInfo := do
  let name := name.eraseMacroScopes
  let resolved ← PRAProver.Surface.resolveDeclaration?
    (PRAProver.Surface.CoreEnvironment.getState (← getEnv)) (name ++ `isAxiom)
  match (theories.getState (← getEnv)).find? (fun T =>
      resolved.any (·.name == T.name ++ `isAxiom)) with
  | some T => pure T
  | none => throwError "unknown first-order theory `{name}`"

private def familyIndexArity (indices : Array (TSyntax ``folFamilyIndex)) :
    CommandElabM Nat := do
  let mut seen : List Name := []
  for index in indices do
    let `(folFamilyIndex| ($ns:ident* : Nat)) := index | throwUnsupportedSyntax
    for n in ns do
      let name := n.getId.eraseMacroScopes
      if seen.contains name then throwErrorAt n "duplicate index parameter `{name}`"
      seen := name :: seen
  return seen.length

private partial def sequenceLength (xs : Term) : Nat × Proof :=
  match getAppFnArgs xs with
  | (.definition `Sequence.cons [], [x, tail]) =>
    let (n, proof) := sequenceLength tail
    let length := applyDefinition `Sequence.length [xs]
    let tailLength := applyDefinition `Sequence.length [tail]
    (n + 1, mkEqTrans length (.app .succ tailLength) (numeral (n + 1))
      (applyTheorem `Sequence.length_cons [x, tail])
      (mkEqCongr .succ tailLength (numeral n) proof))
  | _ => (0, applyTheorem `Sequence.length_nil)

/-- A proof of `Sequence.get xs i = entry` for the entry at index `i` of a cons sequence. -/
private partial def sequenceGet (xs : Term) (i : Nat) (entry : Term) : Proof :=
  match getAppFnArgs xs, i with
  | (.definition `Sequence.cons [], [x, tail]), 0 => applyTheorem `Sequence.get_cons_zero [x, tail]
  | (.definition `Sequence.cons [], [x, tail]), i + 1 =>
    mkEqTrans (applyDefinition `Sequence.get [xs, numeral (i + 1)])
      (applyDefinition `Sequence.get [tail, numeral i]) entry
      (applyTheorem `Sequence.get_cons_succ [x, tail, numeral i]) (sequenceGet tail i entry)
  | _, _ => .forallElim .eqRefl entry

private def ltPredicate (a b : Term) : Predicate :=
  .app (.app (.definition `LT [] []) a) b

/-- From `count = n`, a proof of `i < count` when `i < n` holds for the numerals. -/
private def ltOfCount (i : Nat) (count : Term) (n : Nat) (countEq : Proof) : Proof :=
  let motive := Predicate.lam `n (ltPredicate (numeral i) (.bvar 0))
  let transport := Proof.forallElim (Proof.forallElim (.eqSubst motive) (numeral n)) count
  .impElim (.impElim transport (mkEqSymm count (numeral n) countEq)) (.forallElim .eqRefl .zero)

private def symbolPredicate (name : Name) (L j : Term) : Predicate :=
  .app (.app (.definition name [] []) L) j

/-- Prove the counts, memberships, and arities of a declared language from its definition. -/
private def publishLanguageTheorems (L : LanguageInfo) (fields : List Term) (source : Syntax) :
    CommandElabM Unit := do
  let language := languageTerm L
  let publish (name : Name) (type : Predicate) (proof : Proof) : CommandElabM Unit :=
    publishChecked (.theoremE ⟨L.name ++ name, [], type, proof⟩) source
  let count (name : Name) (count projection : Name) (entry : Term) (equation : Name) :
      CommandElabM (Nat × Proof) := do
    let total := applyDefinition count [language]
    let (n, lengthProof) := sequenceLength entry
    let proof := mkEqTrans total (applyDefinition `Sequence.length [entry]) (numeral n)
      (mkEqCongr (applyDefinition `Sequence.length) (applyDefinition projection [language])
        entry (applyTheorem equation fields)) lengthProof
    publish name (.equal total (numeral n)) proof
    return (n, proof)
  -- Counts.
  let constants := applyDefinition `FOL.Language.constants [language]
  let constantsEq := applyTheorem `FOL.Language.constants_make fields
  publish `constants_language (.equal constants (numeral L.constants.size)) constantsEq
  let (_, functionCountEq) ← count `functionCount_language `FOL.Language.functionCount
    `FOL.Language.functions fields[1]! `FOL.Language.functions_make
  let (_, relationCountEq) ← count `relationCount_language `FOL.Language.relationCount
    `FOL.Language.relations fields[2]! `FOL.Language.relations_make
  let constantFamilyCount := applyDefinition `FOL.Language.constantFamilyCount [language]
  let constantFamilyCountEq := applyTheorem `FOL.Language.constantFamilyCount_make fields
  publish `constantFamilyCount_language
    (.equal constantFamilyCount (numeral L.constantFamilies.size)) constantFamilyCountEq
  let (_, functionFamilyCountEq) ← count `functionFamilyCount_language
    `FOL.Language.functionFamilyCount `FOL.Language.functionFamilies fields[4]!
    `FOL.Language.functionFamilies_make
  let (_, relationFamilyCountEq) ← count `relationFamilyCount_language
    `FOL.Language.relationFamilyCount `FOL.Language.relationFamilies fields[5]!
    `FOL.Language.relationFamilies_make
  -- Ordinary symbols.
  for (name, i) in L.constants.toList.zipIdx do
    let lt := ltOfCount i constants L.constants.size constantsEq
    publish (Name.mkSimple ("isConstant_" ++ name.toString))
      (symbolPredicate `FOL.Language.IsConstant language (numeral i))
      (applyTheorem `FOL.Language.isConstant_of_lt [language, numeral i] [] [lt])
  let symbols (entries : Array (Name × Nat)) (sequence : Term) (countTerm : Name)
      (countEq : Proof) (membership arityDef symbolArity membershipOfLt arityOfLt
        projection projectionEq : Name) (label : String) : CommandElabM Unit := do
    let total := applyDefinition countTerm [language]
    for ((name, arity), i) in entries.toList.zipIdx do
      let lt := ltOfCount i total entries.size countEq
      publish (Name.mkSimple (label ++ name.toString))
        (symbolPredicate membership language (numeral i))
        (applyTheorem membershipOfLt [language, numeral i] [] [lt])
      -- `symbolArity L i = arityDef L i = S (get sequence i) = arity`.
      let entry := applyDefinition `Sequence.get [applyDefinition projection [language], numeral i]
      let stored := applyDefinition `Sequence.get [sequence, numeral i]
      let getProof := mkEqTrans entry stored (numeral (arity - 1))
        (mkEqCongr (.lam `xs (applyDefinition `Sequence.get [.bvar 0, numeral i]))
          (applyDefinition projection [language]) sequence (applyTheorem projectionEq fields))
        (sequenceGet sequence i (numeral (arity - 1)))
      let arityProof := mkEqCongr .succ entry (numeral (arity - 1)) getProof
      publish (Name.mkSimple (name.toString ++ "_arity"))
        (.equal (applyDefinition symbolArity [language, numeral i]) (numeral arity))
        (mkEqTrans (applyDefinition symbolArity [language, numeral i])
          (applyDefinition arityDef [language, numeral i]) (numeral arity)
          (applyTheorem arityOfLt [language, numeral i] [] [lt]) arityProof)
  symbols L.functions fields[1]! `FOL.Language.functionCount
    functionCountEq `FOL.Language.IsFunction `FOL.Language.functionArity
    `FOL.Language.functionSymbolArity `FOL.Language.isFunction_of_lt
    `FOL.Language.functionSymbolArity_of_lt `FOL.Language.functions `FOL.Language.functions_make
    "isFunction_"
  symbols L.relations fields[2]! `FOL.Language.relationCount
    relationCountEq `FOL.Language.IsRelation `FOL.Language.relationArity
    `FOL.Language.relationSymbolArity `FOL.Language.isRelation_of_lt
    `FOL.Language.relationSymbolArity_of_lt `FOL.Language.relations `FOL.Language.relations_make
    "isRelation_"
  -- Families: a bound on the family number, membership and arity of every member.
  for (family, i) in L.constantFamilies.toList.zipIdx do
    let lt := ltOfCount i constantFamilyCount L.constantFamilies.size constantFamilyCountEq
    publish (Name.mkSimple (family.name.toString ++ "_lt"))
      (ltPredicate (numeral i) constantFamilyCount) lt
    let pos := ltOfCount 0 constantFamilyCount L.constantFamilies.size constantFamilyCountEq
    let member := applyDefinition `FOL.Language.constantFamilyMember [language, numeral i, .bvar 0]
    let motive := Predicate.lam `k (symbolPredicate `FOL.Language.IsConstant language member)
    publish (Name.mkSimple ("isConstant_" ++ family.name.toString)) (.all motive)
      (.forallIntro `k motive (applyTheorem `FOL.Language.isConstant_of_constantFamilyCount_pos
        [language, member] [] [pos]))
  let families (entries : Array FamilyInfo) (sequence : Term) (countTerm : Name)
      (countEq : Proof) (memberDef membership familyArity symbolArity membershipOfMember
        arityOfMember projection projectionEq : Name) (label : String) : CommandElabM Unit := do
    let total := applyDefinition countTerm [language]
    for (family, i) in entries.toList.zipIdx do
      let lt := ltOfCount i total entries.size countEq
      publish (Name.mkSimple (family.name.toString ++ "_lt")) (ltPredicate (numeral i) total) lt
      let member := applyDefinition memberDef [language, numeral i, .bvar 0]
      let motive := Predicate.lam `k (symbolPredicate membership language member)
      publish (Name.mkSimple (label ++ family.name.toString)) (.all motive)
        (.forallIntro `k motive
          (applyTheorem membershipOfMember [language, numeral i, .bvar 0] [] [lt]))
      let entry := applyDefinition `Sequence.get [applyDefinition projection [language], numeral i]
      let stored := applyDefinition `Sequence.get [sequence, numeral i]
      let getProof := mkEqTrans entry stored (numeral (family.arity - 1))
        (mkEqCongr (.lam `xs (applyDefinition `Sequence.get [.bvar 0, numeral i]))
          (applyDefinition projection [language]) sequence (applyTheorem projectionEq fields))
        (sequenceGet sequence i (numeral (family.arity - 1)))
      let arityProof := mkEqCongr .succ entry (numeral (family.arity - 1)) getProof
      let arityMotive := Predicate.lam `k
        (.equal (applyDefinition symbolArity [language, member]) (numeral family.arity))
      publish (Name.mkSimple (family.name.toString ++ "_arity")) (.all arityMotive)
        (.forallIntro `k arityMotive
          (mkEqTrans (applyDefinition symbolArity [language, member])
            (applyDefinition familyArity [language, numeral i]) (numeral family.arity)
            (applyTheorem arityOfMember [language, numeral i, .bvar 0] [] [lt]) arityProof))
  families L.functionFamilies fields[4]! `FOL.Language.functionFamilyCount functionFamilyCountEq
    `FOL.Language.functionFamilyMember `FOL.Language.IsFunction `FOL.Language.functionFamilyArity
    `FOL.Language.functionSymbolArity `FOL.Language.isFunction_familyMember
    `FOL.Language.functionSymbolArity_familyMember `FOL.Language.functionFamilies
    `FOL.Language.functionFamilies_make "isFunction_"
  families L.relationFamilies fields[5]! `FOL.Language.relationFamilyCount relationFamilyCountEq
    `FOL.Language.relationFamilyMember `FOL.Language.IsRelation `FOL.Language.relationFamilyArity
    `FOL.Language.relationSymbolArity `FOL.Language.isRelation_familyMember
    `FOL.Language.relationSymbolArity_familyMember `FOL.Language.relationFamilies
    `FOL.Language.relationFamilies_make "isRelation_"

def declareLanguage (name : Name) (entries : Array Syntax) (source : Syntax) :
    CommandElabM Unit := do
  let mut L : LanguageInfo := { name := (← getCurrNamespace) ++ name }
  let mut used : List Name := []
  for s in entries do
    let (n, k, isRelation, indexArity) ← match s with
      | `(folSymbol| constant $n:ident) => pure (n.getId.eraseMacroScopes, 0, false, 0)
      | `(folSymbol| function $n:ident of $k:num) =>
        pure (n.getId.eraseMacroScopes, k.getNat, false, 0)
      | `(folSymbol| relation $n:ident of $k:num) =>
        pure (n.getId.eraseMacroScopes, k.getNat, true, 0)
      | `(folSymbol| $n:ident $indices:folFamilyIndex* : constant) =>
        pure (n.getId.eraseMacroScopes, 0, false, ← familyIndexArity indices)
      | `(folSymbol| $n:ident $indices:folFamilyIndex* : function of $k:num) =>
        if k.getNat == 0 then throwErrorAt s "function families must have positive arity"
        pure (n.getId.eraseMacroScopes, k.getNat, false, ← familyIndexArity indices)
      | `(folSymbol| $n:ident $indices:folFamilyIndex* : relation of $k:num) =>
        pure (n.getId.eraseMacroScopes, k.getNat, true, ← familyIndexArity indices)
      | _ => throwError "unexpected symbol syntax {repr s}"
    if used.contains n then throwErrorAt s "duplicate symbol `{n}`"
    used := n :: used
    if isRelation then
      if k == 0 then throwErrorAt s "relation symbols must have positive arity"
      if indexArity == 0 then L := { L with relations := L.relations.push (n, k) }
      else L := { L with relationFamilies := L.relationFamilies.push ⟨n, k, indexArity⟩ }
    else if indexArity != 0 && k == 0 then
      L := { L with constantFamilies := L.constantFamilies.push ⟨n, 0, indexArity⟩ }
    else if indexArity != 0 then
      L := { L with functionFamilies := L.functionFamilies.push ⟨n, k, indexArity⟩ }
    else if k == 0 then L := { L with constants := L.constants.push n }
    else L := { L with functions := L.functions.push (n, k) }
  let fields := [numeral L.constants.size,
    sequenceCode (L.functions.toList.map (fun (_, k) => numeral (k - 1))),
    sequenceCode (L.relations.toList.map (fun (_, k) => numeral (k - 1))),
    numeral L.constantFamilies.size,
    sequenceCode (L.functionFamilies.toList.map (fun f => numeral (f.arity - 1))),
    sequenceCode (L.relationFamilies.toList.map (fun f => numeral (f.arity - 1)))]
  publishChecked (.function ⟨L.name ++ `language, [], 0,
    applyDefinition `FOL.Language.make fields⟩) source
  publishLanguageTheorems L fields source
  modifyEnv (languages.addEntry · L)

/-- Publish the theorem `T.ax : ∀ ps, r → T ⊢ A` for an axiom declared by the theory: the
instance of the axiom at its parameters is a member of the axiom set, so it is provable. The
statement writes the instance out as the template at the parameters. An inherited axiom keeps
the theorem of the theory that declared it. -/
private def publishAxiomTheorem (T : TheoryInfo) (index : Nat) (source : Syntax) :
    CommandElabM Unit := do
  let info := T.axioms[index]!
  let L := languageTerm T.language
  let theory := applyDefinition (T.name ++ `isAxiom)
  let axiomName := T.name ++ info.name
  let values := (List.range info.parameters.size).map Term.parameter
  let statement ← encodeTemplate L values.toArray [] info.template
  let type : Predicate := .app (.definition `FOL.Provable [L, theory] []) statement
  let instanceCode := applyDefinition (info.formulaName T.name) values
  let mut membership := applyTheorem (axiomName ++ `isAxiom_of_instance) values
  if info.guard?.isSome then membership := .impElim membership (.hyp 0)
  let mut branches := (T.axioms.toList.drop T.inherited).toArray.map fun info =>
    applyDefinition (T.name ++ info.name ++ `isAxiom) [instanceCode]
  let mut branchIndex := index - T.inherited
  if let some parent := T.parent then
    branches := #[applyDefinition (parent ++ `isAxiom) [instanceCode]] ++ branches
    branchIndex := branchIndex + 1
  let tail (start : Nat) := (branches.toList.drop start).foldr
    (fun a b => applyDefinition `bor [a, b]) (numeral 0)
  let mut accepted := applyTheorem `bor_eq_one_of_left_eq_one
    [branches[branchIndex]!, tail (branchIndex + 1)] [] [membership]
  for j in (List.range branchIndex).reverse do
    accepted := applyTheorem `bor_eq_one_of_right_eq_one [branches[j]!, tail (j + 1)] []
      [accepted]
  let proof := applyTheorem `FOL.Provable.hypothesis [instanceCode] [L, theory] [accepted]
  let (type, proof) := match info.guard? with
    | none => (type, proof)
    | some guard =>
      let premise := Predicate.equal (applyGuard guard values) (numeral 1)
      (.imp premise type, .impIntro `h premise proof)
  let parameters := info.parameters.toList.map fun p => Parameter.function p.name 0
  publishChecked (.theoremE ⟨axiomName, parameters, type, proof⟩) source
  modifyEnv (theoremParameters.addEntry · (axiomName, info.parameters))

def declareTheory (name lang : Name) (parent : Option Name) (entries : Array Syntax)
    (source : Syntax) : CommandElabM Unit := do
  let L ← findLanguage lang
  let mut T : TheoryInfo := { name := (← getCurrNamespace) ++ name, language := L }
  if let some parent := parent then
    let P ← findTheory parent
    unless P.language.name == L.name do throwError "the parent theory uses a different language"
    T := { T with axioms := P.axioms, parent := some P.name, inherited := P.axioms.size }
  for s in entries do
    match s with
    | `(folAxiom| axiom $n:ident $ps:praParam* $[assuming $guard:praExpr]?
        := $a:folFormula) =>
      let axiomName := n.getId.eraseMacroScopes
      if T.axioms.any (fun entry => entry.name == axiomName) then throwErrorAt n "duplicate axiom"
      let mut parameters : Array SyntaxParameter := #[]
      let mut numericalBinders := #[]
      for p in ps do
        let `(praParam| ($ids:ident* : $type:praExpr)) := p | throwUnsupportedSyntax
        let numeric := match type with | `(praExpr| Nat) => true | _ => false
        let kind ← if numeric then pure SyntaxKind.nat else do
          let some (formula, arity) := syntaxParameterType? type |
            throwErrorAt type "an axiom parameter must have a Nat, term, or formula type"
          pure (.syntax formula arity)
        if numeric then numericalBinders := numericalBinders.push p
        for id in ids do
          let name := id.getId.eraseMacroScopes
          if parameters.any (·.name == name) then throwErrorAt id "duplicate axiom parameter"
          parameters := parameters.push ⟨name, kind⟩
      let template ← parseFormula L [] a parameters.toList (useDefinitions := true)
        (numericalBinders := numericalBinders)
      let guard? ← elaborateAxiomGuard ps guard
      T := { T with axioms := T.axioms.push { name := axiomName, parameters, template, guard? } }
    | _ => throwUnsupportedSyntax
  for info in T.axioms do compileAxiom T.name L info source
  let body := (T.axioms.toList.drop T.inherited).foldr (fun info rest => applyDefinition `bor
    [applyDefinition (T.name ++ info.name ++ `isAxiom) [.bvar 0], rest]) (numeral 0)
  let body := if let some parent := T.parent then
    applyDefinition `bor [applyDefinition (parent ++ `isAxiom) [.bvar 0], body] else body
  publishChecked (.function ⟨T.name ++ `isAxiom, [], 1, .lam `A body⟩) source
  if let some parent := T.parent then
    let parentTest := applyDefinition (parent ++ `isAxiom) [.bvar 0]
    let premise := Predicate.equal parentTest (numeral 1)
    let conclusion := Predicate.equal (applyDefinition (T.name ++ `isAxiom) [.bvar 0]) (numeral 1)
    let branches := (getAppFnArgs body).2
    let proof := applyTheorem `bor_eq_one_of_left_eq_one branches [] [.hyp 0]
    publishChecked (.theoremE ⟨T.name ++ `isAxiom_of_parent, [],
      .all (.lam `A (.imp premise conclusion)),
      .forallIntro `A (.lam `A (.imp premise conclusion)) (.impIntro `h premise proof)⟩) source
  for index in [T.inherited:T.axioms.size] do publishAxiomTheorem T index source
  modifyEnv (theories.addEntry · T)

@[command_elab PRAProver.Surface.praEntry]
def elaborateFOLDeclarations : CommandElab := fun stx => do
  let entry := stx[0]
  match entry with
  | `(praDecl| fol_language $n:ident where $ss:folSymbolSeq) =>
    declareLanguage n.getId.eraseMacroScopes ss.raw[0].getSepArgs entry
  | `(praDecl| fol_theory $n:ident over $L:ident $[extends $P:ident]?
      where $ss:folAxiomSeq) =>
    declareTheory n.getId.eraseMacroScopes L.getId.eraseMacroScopes
      (P.map (·.getId.eraseMacroScopes)) ss.raw[0].getSepArgs entry
  | _ => throwUnsupportedSyntax

end PRAProver.Library.FOL.DSL
