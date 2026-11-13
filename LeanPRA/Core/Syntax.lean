module

public import Std.Data.ExtHashMap.Basic

/-!
# Core PRA syntax

Syntax for the PRA language and its core checker:

- `Term` represents numbers and functions on numbers.
- `Predicate` represents formulas and predicates on numbers.
- `Proof` represents proof expressions.
- `Declaration` represents a function definition, predicate definition, or theorem.
- `Parameter` represents a function or predicate parameter of a declaration.
- `BinderInfo` stores a source name and whether Surface inserts an omitted argument.
- `Term.beq` and `Predicate.beq` compare syntax recursively, including binder annotations.

A function's type is its arity, the number of `Nat` arguments it takes. Local variables and proof
hypotheses use separate de Bruijn indices, with `0` for the innermost binder. Function and
predicate parameters also have separate indices, numbered in declaration order within each kind.

Binder annotations guide printing and implicit argument elaboration; `.anonymous` tells the
printer to pick a fresh name. Variable lookup and typing use indices. Structural comparison checks
binder annotations, and definitional equality erases them during normalization.

Each lambda binds one `Nat` variable, and `app` applies to one `Nat` argument. A definition or
theorem reference carries its function and predicate arguments directly; numerical and proof
arguments are applied afterward.
-/

@[expose] public section

namespace LeanPRA.Core

/-- The type `Nat → … → Nat`, represented by the number of `Nat` arguments. -/
abbrev Arity := Nat

/-- Formula sorts: quantifier-free (`qf`) and general propositions (`prop`).
A `qf` formula can be used wherever `prop` is expected. -/
inductive FormulaSort where
  | qf
  | prop
  deriving Repr, BEq, Inhabited

/-- Join of two formula sorts (`qf` only when both inputs are `qf`). -/
def FormulaSort.join (left right : FormulaSort) : FormulaSort :=
  if left == .qf && right == .qf then .qf else .prop

/-- The type of a predicate: its arity and result sort (`qf` or `prop`). -/
structure PredicateSignature where
  arity : Arity
  sort : FormulaSort
  deriving Repr, BEq, Inhabited

/-- A binder's source name and argument visibility. Surface fills implicit arguments before
Core checking; normalization uses anonymous, explicit binders when comparing expressions. -/
structure BinderInfo where
  name : Lean.Name
  isImplicit : Bool := false
  deriving Repr, BEq, Inhabited, Hashable

/-- A binder whose name is chosen by the printer. -/
def BinderInfo.anonymous : BinderInfo := ⟨.anonymous, false⟩

instance : Coe Lean.Name BinderInfo := ⟨fun name => ⟨name, false⟩⟩
instance : Coe BinderInfo Lean.Name := ⟨BinderInfo.name⟩

/-- A parameter of a predicate definition or theorem. A formula parameter has arity `0`.
Function and predicate parameters can be mixed in the signature and are indexed separately in the
body. -/
inductive Parameter where
  | function (binderName : BinderInfo) (arity : Arity)
  | predicate (binderName : BinderInfo) (signature : PredicateSignature)
  deriving Repr, BEq, Inhabited

/-- Arities of the function parameters in `parameters`, in order. -/
def Parameter.functions (parameters : List Parameter) : List Arity :=
  parameters.filterMap fun | .function _ k => some k | .predicate _ _ => none

/-- Signatures of the predicate parameters in `parameters`, in order. -/
def Parameter.predicates (parameters : List Parameter) : List PredicateSignature :=
  parameters.filterMap fun | .function _ _ => none | .predicate _ s => some s

/-- Numerical terms and first-order functions on `Nat`. `lam` binds one `Nat` variable and `app`
applies to one `Nat` argument. Function arguments appear only in `primrec` and `definition`. -/
inductive Term where
  | bvar (index : Nat)
  | parameter (index : Nat)
  | zero
  | succ
  | lam (binderName : Lean.Name) (body : Term)
  | app (function argument : Term)
  | letE (binderName : Lean.Name) (value body : Term)
  | primrec (base step : Term)
  | definition (name : Lean.Name) (functions : List Term)
  deriving Repr, Inhabited, Hashable

mutual

/-- Structural equality on `Term`, including binder annotations. -/
def Term.beq (t u : Term) : Bool :=
  match t, u with
  | .bvar i, .bvar j | .parameter i, .parameter j => i == j
  | .zero, .zero | .succ, .succ => Bool.true
  | .lam n t, .lam m u => n == m && Term.beq t u
  | .app f a, .app g b => Term.beq f g && Term.beq a b
  | .letE n f a, .letE m g b =>
    n == m && Term.beq f g && Term.beq a b
  | .primrec b s, .primrec c t => Term.beq b c && Term.beq s t
  | .definition n fs, .definition m gs => n == m && Term.beqList fs gs
  | _, _ => Bool.false

/-- Structural equality on lists of `Term`. -/
def Term.beqList (ts us : List Term) : Bool :=
  match ts, us with
  | [], [] => Bool.true
  | t :: ts, u :: us => Term.beq t u && Term.beqList ts us
  | _, _ => Bool.false

end

instance : BEq Term := ⟨Term.beq⟩

/-- Formulas and predicates on `Nat`. A formula is a predicate of arity `0`. `lam` binds one `Nat`
variable. The quantifiers `all` and `ex` take a unary predicate. Negation is `imp A false`. -/
inductive Predicate where
  | false
  | true
  | equal (left right : Term)
  | imp (antecedent consequent : Predicate)
  | and (left right : Predicate)
  | or (left right : Predicate)
  | all (predicate : Predicate)
  | ex (predicate : Predicate)
  | parameter (index : Nat)
  | lam (binderName : BinderInfo) (body : Predicate)
  | app (predicate : Predicate) (argument : Term)
  | letTerm (binderName : Lean.Name) (value : Term) (body : Predicate)
  | letPredicate (binderName : Lean.Name) (value body : Predicate)
  | definition (name : Lean.Name) (functions : List Term) (predicates : List Predicate)
  deriving Repr, Inhabited, Hashable

mutual

/-- Structural equality on `Predicate`, including binder annotations. -/
def Predicate.beq (P Q : Predicate) : Bool :=
  match P, Q with
  | .false, .false | .true, .true => Bool.true
  | .equal a b, .equal c d => a == c && b == d
  | .imp A B, .imp C D | .and A B, .and C D | .or A B, .or C D =>
    Predicate.beq A C && Predicate.beq B D
  | .all P, .all Q | .ex P, .ex Q => Predicate.beq P Q
  | .lam n P, .lam m Q => n == m && Predicate.beq P Q
  | .parameter i, .parameter j => i == j
  | .app P a, .app Q b => Predicate.beq P Q && a == b
  | .letTerm n a P, .letTerm m b Q =>
    n == m && a == b && Predicate.beq P Q
  | .letPredicate n P R, .letPredicate m Q S =>
    n == m && Predicate.beq P Q && Predicate.beq R S
  | .definition n fs ps, .definition m gs qs =>
    n == m && fs == gs && Predicate.beqList ps qs
  | _, _ => Bool.false

/-- Structural equality on lists of `Predicate`. -/
def Predicate.beqList (ps qs : List Predicate) : Bool :=
  match ps, qs with
  | [], [] => Bool.true
  | P :: ps, Q :: qs => Predicate.beq P Q && Predicate.beqList ps qs
  | _, _ => Bool.false

end

instance : BEq Predicate := ⟨Predicate.beq⟩

/-- Proof expressions, typed by formulas. A `motive` is a unary predicate; in `induction`, it must
be quantifier-free. `forallIntro` binds a `Nat` variable and `impIntro` binds a proof hypothesis.
Primitive heads carry their schema predicates and expose their full signatures.
`theoremE` instantiates function and predicate parameters;
`forallElim` and `impElim` apply a proof to a term or another proof. -/
inductive Proof where
  | hyp (index : Nat)
  | trueIntro
  | theoremE (name : Lean.Name) (functions : List Term) (predicates : List Predicate)
  | impIntro (binderName : Lean.Name) (antecedent : Predicate) (body : Proof)
  | impElim (function argument : Proof)
  | andIntro (left right : Proof)
  | andLeft (left right : Predicate)
  | andRight (left right : Predicate)
  | orLeft (left right : Predicate)
  | orRight (left right : Predicate)
  | orElim (left right target : Predicate)
  | falseElim (target : Predicate)
  | forallIntro (binderName : Lean.Name) (motive : Predicate) (body : Proof)
  | forallElim (proof : Proof) (argument : Term)
  | existsIntro (motive : Predicate) (witness : Term) (proof : Proof)
  | existsElim (motive target : Predicate)
  | letE (binderName : Lean.Name) (type : Predicate) (value body : Proof)
  | letTerm (binderName : Lean.Name) (value : Term) (body : Proof)
  | letPredicate (binderName : Lean.Name) (value : Predicate) (body : Proof)
  | ascribe (type : Predicate) (proof : Proof)
  | eqRefl
  | eqSubst (motive : Predicate)
  | succNeZero
  | succInj
  | lem (formula : Predicate)
  | induction (motive : Predicate)
  deriving Repr, BEq, Inhabited, Hashable

/-- A function parameter of a `FunctionDefinition`, with its arity and a binder name for printing.
-/
structure FunctionParameter where
  arity : Arity
  binderName : BinderInfo := .anonymous
  deriving Repr, BEq, Inhabited

/-- A function definition, with its function parameters, result arity, and body. -/
structure FunctionDefinition where
  name : Lean.Name
  parameters : List FunctionParameter := []
  arity : Arity
  body : Term
  deriving Repr, BEq

/-- Arities of the function parameters of `d`. -/
def FunctionDefinition.functions (d : FunctionDefinition) : List Arity :=
  d.parameters.map (·.arity)

/-- Convert the parameters of `d` to a list of `Parameter`. -/
def FunctionDefinition.parameterSignature (d : FunctionDefinition) : List Parameter :=
  d.parameters.map fun p => .function p.binderName p.arity

/-- A predicate definition, with its parameters, signature, and body. -/
structure PredicateDefinition where
  name : Lean.Name
  parameters : List Parameter := []
  signature : PredicateSignature
  body : Predicate
  deriving Repr, BEq

/-- A theorem, with its parameters, statement `type`, and proof `body`. -/
structure TheoremDefinition where
  name : Lean.Name
  parameters : List Parameter := []
  type : Predicate
  body : Proof
  deriving Repr, BEq

/-- Arities of the function parameters of `d`. -/
def PredicateDefinition.functions (d : PredicateDefinition) : List Arity :=
  Parameter.functions d.parameters

/-- Signatures of the predicate parameters of `d`. -/
def PredicateDefinition.predicates (d : PredicateDefinition) : List PredicateSignature :=
  Parameter.predicates d.parameters

/-- Arities of the function parameters of `d`. -/
def TheoremDefinition.functions (d : TheoremDefinition) : List Arity :=
  Parameter.functions d.parameters

/-- Signatures of the predicate parameters of `d`. -/
def TheoremDefinition.predicates (d : TheoremDefinition) : List PredicateSignature :=
  Parameter.predicates d.parameters

/-- A top-level declaration: a function definition, predicate definition, or theorem. -/
inductive Declaration where
  | function (definition : FunctionDefinition)
  | predicate (definition : PredicateDefinition)
  | theoremE (definition : TheoremDefinition)
  deriving Repr, BEq

/-- Map from fully qualified names to checked declarations, extended through
`checkDeclaration`. -/
abbrev Environment := Std.ExtHashMap Lean.Name Declaration

/-- Typing context for local variables, declaration parameters, and proof hypotheses.
`locals` and `proofs` are indexed from `0` for the innermost binder; `functions` and `predicates`
follow declaration order. Pushing a local variable shifts variable indices in `proofs`. -/
structure Context where
  locals : List Arity := []
  functions : List Arity := []
  predicates : List PredicateSignature := []
  proofs : List Predicate := []
  deriving Repr, BEq, Inhabited

/-- The name of a declaration. -/
def Declaration.name : Declaration → Lean.Name
  | .function d => d.name
  | .predicate d => d.name
  | .theoremE d => d.name

end LeanPRA.Core
