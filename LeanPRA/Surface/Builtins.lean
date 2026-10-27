module

public meta import LeanPRA.Core.Checker
public meta import LeanPRA.Surface.Options

/-!
# The PRA builtin declarations

Builtin constants are ordinary Core declarations checked before user declarations are loaded.
Their bodies use the primitive Core rules. Elaboration, signature printing, and editor hovers use
these declarations through the same environment as user constants.

- `builtinDeclarations` contains the numerical, predicate, and proof declarations.
- `builtinEnvironment` checks them from the empty Core environment during initialization.
- `builtinNames` lists their names and the type keywords reserved by the frontend.
- `isBuiltinName` tests whether a source declaration name is reserved.

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

private def schemaParameter (name : Name) (arity := 0) (implicit := true)
    (sort := Core.FormulaSort.prop) : Core.Parameter :=
  .predicate ⟨name, implicit⟩ ⟨arity, sort⟩

private def numericalBinders (binders : List (Name × Bool)) (type : Core.Predicate)
    (body : Core.Proof) : Core.Predicate × Core.Proof :=
  binders.foldr (fun (name, implicit) (type, body) =>
    let motive := Core.Predicate.lam ⟨name, implicit⟩ type
    (.all motive, .forallIntro name motive body)) (type, body)

/-- The fixed declarations available in every PRA module. Primitive truth and falsity have their
quantifier-free signatures; they can also be used wherever `Prop` is expected. -/
def builtinDeclarations : List Core.Declaration := Id.run do
  let p := Core.Predicate.parameter 0
  let q := Core.Predicate.parameter 1
  let r := Core.Predicate.parameter 2
  let applyPredicate := Core.Predicate.app
  let x := Core.Term.bvar 1
  let y := Core.Term.bvar 0
  let eq := Core.Predicate.equal x y
  let imp := Core.Predicate.imp
  let intro := Core.Proof.impIntro
  let theoremDecl (name : Name) (parameters : List Core.Parameter)
      (type : Core.Predicate) (body : Core.Proof) :=
    Core.Declaration.theoremE ⟨name, parameters, type, body⟩
  let projection (name : Name) (left : Bool) :=
    let pair := Core.Predicate.and p q
    theoremDecl name [schemaParameter `P, schemaParameter `Q] (imp pair (if left then p else q))
      (intro `h pair (if left then .andLeft (.hyp 0) else .andRight (.hyp 0)))
  let injection (name : Name) (left : Bool) :=
    theoremDecl name [schemaParameter `P, schemaParameter `Q]
      (imp (if left then p else q) (.or p q))
      (intro `h (if left then p else q)
        (if left then .orLeft q (.hyp 0) else .orRight p (.hyp 0)))
  let reflexivity (name : Name) (implicit : Bool) :=
    let value := Core.Term.bvar 0
    let (type, body) := numericalBinders [(`x, implicit)] (.equal value value) (.eqRefl value)
    theoremDecl name [] type body
  let (substType, substBody) := numericalBinders [(`x, true), (`y, true)]
    (imp eq (imp (applyPredicate (p.shift 2) x) (applyPredicate (p.shift 2) y)))
    (intro `e eq (intro `h (applyPredicate (p.shift 2) x) (.eqSubst (p.shift 2) (.hyp 1) (.hyp 0))))
  let value := Core.Term.bvar 0
  let (nonzeroType, nonzeroBody) := numericalBinders [(`x, false)]
    (imp (.equal (.app .succ value) .zero) .false) (.succNeZero value)
  let premise := Core.Predicate.equal (.app .succ x) (.app .succ y)
  let (injectiveType, injectiveBody) := numericalBinders [(`x, true), (`y, true)]
    (imp premise eq) (intro `h premise (.succInj (.hyp 0)))
  let branch := Core.Predicate.all (.lam `x (imp (applyPredicate p.shift (.bvar 0)) q.shift))
  let px := applyPredicate p.shift (.bvar 0)
  let step := Core.Predicate.all (.lam `x (imp px (applyPredicate p.shift (.app .succ (.bvar 0)))))
  let motive := Core.Predicate.lam `x px
  return [
    .function ⟨`S, [], 1, .succ⟩,
    .function ⟨`primrec, [⟨0, `base⟩, ⟨2, `step⟩], 1,
      .lam `n (.primrec (.parameter 0) (.parameter 1) (.bvar 0))⟩,
    .predicate ⟨`True, [], ⟨0, .qf⟩, .true⟩,
    .predicate ⟨`False, [], ⟨0, .qf⟩, .false⟩,
    theoremDecl `trivial [] .true .trueIntro,
    theoremDecl `false_elim [schemaParameter `P] (imp .false p)
      (intro `h .false (.falseElim p (.hyp 0))),
    projection `and_left true, projection `and_right false,
    injection `or_left true, injection `or_right false,
    theoremDecl `or_elim [schemaParameter `P, schemaParameter `Q, schemaParameter `R]
      (imp (.or p q) (imp (imp p r) (imp (imp q r) r)))
      (intro `h (.or p q) (intro `left (imp p r) (intro `right (imp q r)
        (.orElim `hp `hq r (.hyp 2)
          (.impElim (.hyp 2) (.hyp 0)) (.impElim (.hyp 1) (.hyp 0)))))),
    theoremDecl `lem [schemaParameter `P 0 false] (.or p (imp p .false)) (.lem p),
    reflexivity `eq_refl false, reflexivity `rfl true,
    theoremDecl `eq_subst [schemaParameter `P 1 false] substType substBody,
    theoremDecl `succ_ne_zero [] nonzeroType nonzeroBody,
    theoremDecl `succ_inj [] injectiveType injectiveBody,
    theoremDecl `exists_elim [schemaParameter `P 1, schemaParameter `Q]
      (imp (.ex p) (imp branch q))
      (intro `h (.ex p) (intro `branch branch
        (.existsElim `x `hx q (.hyp 1) (.impElim (.forallElim (.hyp 1) (.bvar 0)) (.hyp 0))))),
    theoremDecl `induction [schemaParameter `motive 1 true .qf]
      (imp (applyPredicate p .zero) (imp step (.all motive)))
      (intro `base (applyPredicate p .zero) (intro `step step
        (.forallIntro `x motive (.induction `k `ih p.shift (.hyp 1)
          (.impElim (.forallElim (.hyp 1) (.bvar 0)) (.hyp 0)) (.bvar 0)))))]

/-- The checked initial environment shared by frontend modules. A malformed builtin declaration
stops initialization with the Core checker's error. -/
initialize builtinEnvironment : Core.Environment ← do
  let mut environment : Core.Environment := ∅
  for declaration in builtinDeclarations do
    match Core.checkDeclaration (pra.maxDepth.get {}) environment declaration with
    | .ok accepted => environment := accepted
    | .error error =>
      throw (IO.userError s!"invalid PRA builtin `{declaration.name}`: {error.message}")
  pure environment

/-- Reserved names, derived from the declarations along with the three type keywords. -/
def builtinNames : List Name :=
  [`Nat, `Prop, `QFProp] ++ builtinDeclarations.map Core.Declaration.name

/-- Whether a name belongs to a builtin declaration or type keyword. -/
def isBuiltinName (name : Name) : Bool := builtinNames.contains name

end LeanPRA.Surface
