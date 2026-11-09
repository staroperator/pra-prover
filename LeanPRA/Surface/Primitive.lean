module

public meta import LeanPRA.Core.Checker
public meta import LeanPRA.Surface.Options

/-!
# PRA primitive declarations

Primitive declarations give names and parameter binders to Core constructors. Their result types
come from the Core checker. Elaboration constructs the primitive head directly, and editor hovers
use its declaration signature.

- `DeclarationSignature` describes the interface of a primitive or a defined declaration.
- `PrimitiveDeclaration` pairs a signature with its Core construction.
- `primitiveDeclarations` checks the fixed primitive interfaces in an empty environment.
- `builtinNames` and `isBuiltinName` reserve primitive names and the type keywords.

Builtin signatures use the following conventions. Braces mark implicit arguments. Induction's
motive is quantifier-free, as required by the PRA language.

```text
S : Nat → Nat
primrec (base : Nat) (step : Nat → Nat → Nat) : Nat → Nat
True : QFProp
False : QFProp
trivial : True
false_elim {P : Prop} : False → P
and_left {P Q : Prop} : P ∧ Q → P
and_right {P Q : Prop} : P ∧ Q → Q
or_left {P Q : Prop} : P → P ∨ Q
or_right {P Q : Prop} : Q → P ∨ Q
or_elim {P Q R : Prop} : P ∨ Q → (P → R) → (Q → R) → R
lem (P : Prop) : P ∨ ¬P
eq_refl : ∀ x, x = x
rfl : ∀ {x}, x = x
eq_subst (P : Nat → Prop) : ∀ {x y}, x = y → P x → P y
exists_elim {P : Nat → Prop} {Q : Prop} : (∃ x, P x) → (∀ x, P x → Q) → Q
succ_ne_zero : ∀ x, ¬S x = 0
succ_inj : ∀ {x y}, S x = S y → x = y
induction {motive : Nat → QFProp} :
  motive 0 → (∀ x, motive x → motive (S x)) → ∀ x, motive x
```
-/

public meta section

namespace LeanPRA.Surface

open Lean

/-- Parameters and result arity of a numerical declaration. -/
structure FunctionSignature where
  name : Name
  parameters : List Core.FunctionParameter
  arity : Core.Arity

/-- Parameters and result signature of a predicate declaration. -/
structure PredicateDeclarationSignature where
  name : Name
  parameters : List Core.Parameter
  signature : Core.PredicateSignature

/-- Parameters and formula of a proof declaration. -/
structure ProofSignature where
  name : Name
  parameters : List Core.Parameter
  type : Core.Predicate

/-- Declaration interfaces used for name resolution, elaboration, and display. -/
inductive DeclarationSignature where
  | function (signature : FunctionSignature)
  | predicate (signature : PredicateDeclarationSignature)
  | theoremE (signature : ProofSignature)

/-- The name displayed for a declaration. -/
def DeclarationSignature.name : DeclarationSignature → Name
  | .function d => d.name
  | .predicate d => d.name
  | .theoremE d => d.name

/-- The expression category produced by a declaration. -/
def DeclarationSignature.kind : DeclarationSignature → Core.DeclarationKind
  | .function _ => .function
  | .predicate _ => .predicate
  | .theoremE _ => .theoremE

/-- Present numerical parameters in the common declaration-parameter format. -/
def FunctionSignature.parameterSignature (d : FunctionSignature) : List Core.Parameter :=
  d.parameters.map fun p => .function p.binderName p.arity

/-- Extract the interface of a checked definition or theorem. -/
def declarationSignature : Core.Declaration → DeclarationSignature
  | .function d => .function ⟨d.name, d.parameters, d.arity⟩
  | .predicate d => .predicate ⟨d.name, d.parameters, d.signature⟩
  | .theoremE d => .theoremE ⟨d.name, d.parameters, d.type⟩

instance : Coe Core.Declaration DeclarationSignature := ⟨declarationSignature⟩

/-- A named primitive head, expressed under its declared schema parameters. -/
structure PrimitiveDeclaration where
  signature : DeclarationSignature
  construction : Core.CheckSubject

private def schemaParameter (name : Name) (arity := 0) (implicit := true)
    (sort := Core.FormulaSort.prop) : Core.Parameter :=
  .predicate ⟨name, implicit⟩ ⟨arity, sort⟩

private def primitiveHeads : List (Name × List Core.Parameter × Core.CheckSubject) := Id.run do
  let p := Core.Predicate.parameter 0
  let q := Core.Predicate.parameter 1
  let r := Core.Predicate.parameter 2
  let pq := [schemaParameter `P, schemaParameter `Q]
  return [
    (`S, [], .term .succ),
    (`primrec, [.function ⟨`base, false⟩ 0, .function ⟨`step, false⟩ 2],
      .term (.primrec (.parameter 0) (.parameter 1))),
    (`True, [], .predicate .true),
    (`False, [], .predicate .false),
    (`trivial, [], .proof .trueIntro),
    (`false_elim, [schemaParameter `P], .proof (.falseElim p)),
    (`and_left, pq, .proof (.andLeft p q)),
    (`and_right, pq, .proof (.andRight p q)),
    (`or_left, pq, .proof (.orLeft p q)),
    (`or_right, pq, .proof (.orRight p q)),
    (`or_elim, pq ++ [schemaParameter `R], .proof (.orElim p q r)),
    (`lem, [schemaParameter `P 0 false], .proof (.lem p)),
    (`eq_refl, [], .proof .eqRefl),
    (`rfl, [], .proof .eqRefl),
    (`eq_subst, [schemaParameter `P 1 false], .proof (.eqSubst p)),
    (`succ_ne_zero, [], .proof .succNeZero),
    (`succ_inj, [], .proof .succInj),
    (`exists_elim, [schemaParameter `P 1, schemaParameter `Q], .proof (.existsElim p q)),
    (`induction, [schemaParameter `motive 1 true .qf], .proof (.induction p))]

/-- Primitive signatures inferred by the Core checker from their constructors. Primitive heads
have no definition bodies in the object environment. -/
initialize primitiveDeclarations : List PrimitiveDeclaration ← do
  primitiveHeads.mapM fun (name, parameters, construction) => do
    let context : Core.Context :=
      { functions := Core.Parameter.functions parameters
        predicates := Core.Parameter.predicates parameters }
    let depth := pra.maxDepth.get {}
    let result : Core.CheckResult DeclarationSignature := match construction with
      | .term t => (Core.inferTerm depth ∅ context t).map fun arity =>
        DeclarationSignature.function ⟨name, parameters.filterMap (fun (p : Core.Parameter) =>
          match p with
          | .function info k => some ⟨k, info⟩ | _ => none), arity⟩
      | .predicate p => (Core.inferPredicate depth ∅ context p).map fun sig =>
        DeclarationSignature.predicate ⟨name, parameters, sig⟩
      | .proof p => (Core.inferProof depth ∅ context p).map fun type =>
        let type : Core.Predicate := if name == `rfl then match type with
          | .all (.lam info body) => .all (.lam { info with isImplicit := true } body)
          | _ => type
        else type
        DeclarationSignature.theoremE ⟨name, parameters, type⟩
    match result with
    | .ok signature => pure ⟨signature, construction⟩
    | .error error => throw (IO.userError s!"invalid PRA primitive `{name}`: {error.message}")

/-- Find a primitive declaration by its fully qualified name. -/
def primitiveDeclaration? (name : Name) : Option PrimitiveDeclaration :=
  primitiveDeclarations.find? (·.signature.name == name)

/-- Reserved names for primitive declarations and the three type keywords. -/
def builtinNames : List Name :=
  [`Nat, `Prop, `QFProp] ++ primitiveDeclarations.map (·.signature.name)

/-- Whether a name belongs to a primitive declaration or type keyword. -/
def isBuiltinName (name : Name) : Bool := builtinNames.contains name

end LeanPRA.Surface
