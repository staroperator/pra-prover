module

public meta import LeanPRA.Surface.Command
public import LeanPRA.Library.Logic

/-!
# Construction of PRA expressions

Helpers for Library metaprograms that build explicit PRA terms and proofs:

- `numeral` and `numeralValue?` construct and read successor numerals.
- `applyDefinition`, `getAppFnArgs`, and `applyTheorem` assemble and decompose applications.
- `mkEqSymm`, `mkEqTrans`, and `mkEqCongr` apply the equality theorems from `Library.Logic`.
- `mapProof` and `shiftProof` transform explicit proofs beneath their binders.
- `proveArithmeticLe` builds numerical inequality proofs from arithmetic and pairing lemmas.
- `sequenceCode` and `tupleCode` construct expressions for the Library's numerical encodings.
- `publishChecked` checks generated declarations and records their source locations.

The caller imports the declarations needed to check the resulting expressions.
-/

public meta section

namespace LeanPRA.Library.Tactic.Construction

open Lean hiding Term

open Core

open Lean.Elab.Command

/-- Construct a PRA numeral from `0` and `succ`. -/
def numeral : Nat → Term
  | 0 => .zero
  | n + 1 => .app .succ (numeral n)

/-- Read the `Nat` value of a numeral built from `0` and `succ`. -/
def numeralValue? : Term → Option Nat
  | .zero => some 0
  | .app .succ n => (numeralValue? n).map (· + 1)
  | _ => none

/-- Apply a named PRA function to its declaration parameters and numerical arguments. -/
def applyDefinition (name : Name) (args : List Term := []) (parameters : List Term := []) :
    Term :=
  args.foldl .app (.definition name parameters)

/-- Split an application spine into its head term and argument list. -/
def getAppFnArgs (t : Term) : Term × List Term := go t [] where
  go : Term → List Term → Term × List Term
    | .app f a, args => go f (a :: args)
    | f, args => (f, args)

/-- Instantiate a PRA theorem and discharge its implication premises in order. -/
def applyTheorem (name : Name) (args : List Term := []) (parameters : List Term := [])
    (premises : List Proof := []) : Proof :=
  premises.foldl .impElim (args.foldl .forallElim (.theoremE name parameters []))

/-- Project one side of a conjunction theorem after instantiating its numerical arguments.
The theorem statement supplies the two formula arguments of the primitive projection. -/
def projectTheorem (right : Bool) (name : Name) (args : List Term := [])
    (parameters : List Term := []) : CommandElabM Proof := do
  let env := Surface.CoreEnvironment.getState (← getEnv)
  let some (.theoremE declaration) := env.lookup name | throwError "unknown theorem {name}"
  let checked {α} (result : CheckResult α) : CommandElabM α :=
    match result with
    | .ok value => pure value
    | .error error => throwError "{error.message}"
  let depth ← Surface.getMaxDepth
  let mut type := declaration.type.instantiate parameters []
  for arg in args do
    let .all motive ← checked (whnfPredicate depth env type)
      | throwError "expected universal theorem {name}"
    type := .app motive arg
  let .and left rightType ← checked (whnfPredicate depth env type)
    | throwError "expected conjunction theorem {name}"
  let head := if right then Proof.andRight left rightType else Proof.andLeft left rightType
  return .impElim head (applyTheorem name args parameters)

/-- Apply `eq_symm` to a proof of `a = b`. -/
def mkEqSymm (a b : Term) (proof : Proof) : Proof :=
  applyTheorem `eq_symm [a, b] [] [proof]

/-- Apply `eq_trans` to proofs of `a = b` and `b = c`. -/
def mkEqTrans (a b c : Term) (left right : Proof) : Proof :=
  applyTheorem `eq_trans [a, b, c] [] [left, right]

/-- Apply `eq_congr` with unary function `f` to a proof of `a = b`. -/
def mkEqCongr (f a b : Term) (proof : Proof) : Proof :=
  applyTheorem `eq_congr [a, b] [f] [proof]

/-- Transform a proof while tracking its numerical and proof binder depths. The callbacks map
terms, predicates, and hypothesis references in their respective binder contexts. -/
def mapProof (tm : Nat → Core.Term → Core.Term)
    (pm : Nat → Core.Predicate → Core.Predicate) (hm : Nat → Nat → Nat → Core.Proof)
    (nd hd : Nat) : Core.Proof → Core.Proof
  | .hyp i => hm nd hd i
  | .theoremE n fs ps => .theoremE n (fs.map (tm nd)) (ps.map (pm nd))
  | .impIntro n a p => .impIntro n (pm nd a) (mapProof tm pm hm nd (hd + 1) p)
  | .impElim p q => .impElim (mapProof tm pm hm nd hd p) (mapProof tm pm hm nd hd q)
  | .andIntro p q => .andIntro (mapProof tm pm hm nd hd p) (mapProof tm pm hm nd hd q)
  | .andLeft a b => .andLeft (pm nd a) (pm nd b)
  | .andRight a b => .andRight (pm nd a) (pm nd b)
  | .orLeft a b => .orLeft (pm nd a) (pm nd b)
  | .orRight a b => .orRight (pm nd a) (pm nd b)
  | .orElim a b c => .orElim (pm nd a) (pm nd b) (pm nd c)
  | .falseElim a => .falseElim (pm nd a)
  | .forallIntro n a p => .forallIntro n (pm nd a) (mapProof tm pm hm (nd + 1) hd p)
  | .forallElim p t => .forallElim (mapProof tm pm hm nd hd p) (tm nd t)
  | .existsIntro a t p => .existsIntro (pm nd a) (tm nd t) (mapProof tm pm hm nd hd p)
  | .existsElim a b => .existsElim (pm nd a) (pm nd b)
  | .letE n a p q => .letE n (pm nd a) (mapProof tm pm hm nd hd p)
      (mapProof tm pm hm nd (hd + 1) q)
  | .letTerm n t p => .letTerm n (tm nd t) (mapProof tm pm hm nd hd p)
  | .letPredicate n a p => .letPredicate n (pm nd a) (mapProof tm pm hm nd hd p)
  | .ascribe a p => .ascribe (pm nd a) (mapProof tm pm hm nd hd p)
  | .eqRefl => .eqRefl
  | .eqSubst a => .eqSubst (pm nd a)
  | .succNeZero => .succNeZero
  | .succInj => .succInj
  | .lem a => .lem (pm nd a)
  | .induction a => .induction (pm nd a)
  | p => p

/-- Raise free numerical variables and free proof hypotheses by the supplied amounts. -/
def shiftProof (p : Core.Proof) (nd hd : Nat) : Core.Proof :=
  mapProof (fun d t => t.shift nd d) (fun d a => a.shift nd d)
    (fun _ d i => .hyp (if i < d then i else i + hd)) 0 0 p

/--
Build a PRA proof of `a ≤ b` using numerals, reflexivity, and monotonicity of addition,
multiplication, and pairing. The caller imports the arithmetic and pairing lemmas used by the
result. Unsupported comparisons raise an elaboration error.
-/
partial def proveArithmeticLe (a b : Term) : CommandElabM Proof := do
  if a == b then return applyTheorem `le_refl [a]
  if numeralValue? a == some 0 then return applyTheorem `zero_le [b]
  if let some x := numeralValue? a then
    if let some y := numeralValue? b then
      if x ≤ y then return .forallElim .eqRefl (numeral 0)
  let (bh, bs) := getAppFnArgs b
  let (ah, as) := getAppFnArgs a
  let trans (mid : Term) (h : Proof) : CommandElabM Proof := do
    return applyTheorem `le_trans [a, mid, b] [] [← proveArithmeticLe a mid, h]
  if let .definition n _ := bh then
    match n, bs with
    | `pair, [x, y] =>
      if ah == bh then
        if let [u, v] := as then
          try
            return applyTheorem `pair_mono [u, v, x, y] []
              [← proveArithmeticLe u x, ← proveArithmeticLe v y]
          catch _ => pure ()
      try
        return ← trans x (applyTheorem `left_le_pair [x, y])
      catch _ => pure ()
      return ← trans y (applyTheorem `right_le_pair [x, y])
    | `add, [x, y] =>
      if ah == bh then
        if let [u, v] := as then
          try
            let mid := applyDefinition `add [x, v]
            return applyTheorem `le_trans [a, mid, b] []
              [applyTheorem `add_le_add_right [u, x, v] [] [← proveArithmeticLe u x],
               applyTheorem `add_le_add_left [v, y, x] [] [← proveArithmeticLe v y]]
          catch _ => pure ()
      try
        return ← trans x (applyTheorem `le_add_right [x, y])
      catch _ => pure ()
      return ← trans y (applyTheorem `le_add_left [x, y])
    | `mul, [x, y] =>
      if ah == bh then
        if let [u, v] := as then
          if u == x then
            return applyTheorem `mul_le_mul_left [v, y, x] [] [← proveArithmeticLe v y]
      if let some k := numeralValue? x then
        if k > 0 then
          return ← trans y (applyTheorem `le_mul_of_pos [y, x] []
            [.forallElim .succNeZero (numeral (k - 1))])
      throwError "cannot establish multiplication bound"
    | `S, [x] => return ← trans x (applyTheorem `le_succ_self [x])
    | _, _ => pure ()
  if bh == .succ then
    if let [x] := bs then return ← trans x (applyTheorem `le_succ_self [x])
  throwError "cannot establish the arithmetic inequality"

/-- Encode entries in order using `Sequence.cons`, terminated by `Sequence.nil`. -/
def sequenceCode (xs : List Term) : Term :=
  xs.foldr (fun x r => applyDefinition `Sequence.cons [x, r]) (applyDefinition `Sequence.nil)

/-- Encode a fixed-length tuple by nested pairs, with a singleton represented by its entry.
The empty list uses zero. -/
def tupleCode : List Term → Term
  | [] => numeral 0
  | [a] => a
  | a :: rest => applyDefinition `pair [a, tupleCode rest]

/-- Check and publish a fully explicit PRA declaration, with its source location. -/
def publishChecked (decl : Core.Declaration) (source : Syntax) : CommandElabM Unit :=
    withRef source do
  let env := Surface.CoreEnvironment.getState (← getEnv)
  let depth ← Surface.getMaxDepth
  -- Generated declarations can contain many copies of the same syntax.
  let decl := ShareCommon.shareCommon' decl
  match Core.checkDeclaration depth env decl with
  | .error e => throwError "PRA declaration `{decl.name}`: {e.message}"
  | .ok checked =>
    modifyEnv (Surface.publishDeclaration · checked decl.name)
    let metadata : Surface.DeclarationMetadata := { location? := ← Surface.sourceLocation source }
    modifyEnv (Surface.declarationMetadata.addEntry · (decl.name, metadata))

end LeanPRA.Library.Tactic.Construction
