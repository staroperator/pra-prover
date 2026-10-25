module

public meta import Lean

/-!
# Fixed PRA builtin names

Table of reserved builtin identifiers used by name resolution, elaboration, and printing:

- `builtinNames` lists reserved identifiers and their `BuiltinKind`.
- `isBuiltinName` tests whether an identifier is reserved.
- `isProofPrimitive` tests whether an identifier is a builtin proof constructor.
-/

public meta section

namespace LeanPRA.Surface

open Lean

/-- Category of a builtin identifier: type keyword, function, predicate, or proof primitive. -/
inductive BuiltinKind where
  | type
  | function
  | predicate
  | proof
  deriving BEq

/-- Reserved builtin identifiers and their categories. -/
def builtinNames : List (Name × BuiltinKind) :=
  [(`Nat, .type), (`Prop, .type), (`QFProp, .type), (`S, .function), (`primrec, .function),
   (`True, .predicate), (`False, .predicate), (`rfl, .proof), (`trivial, .proof),
   (`eq_refl, .proof), (`and_left, .proof), (`and_right, .proof), (`or_left, .proof),
   (`or_right, .proof), (`false_elim, .proof), (`succ_ne_zero, .proof), (`succ_inj, .proof),
   (`lem, .proof), (`eq_subst, .proof), (`or_elim, .proof), (`exists_elim, .proof),
   (`induction, .proof)]

/-- Look up the `BuiltinKind` of `name`. -/
def builtinKind? (name : Name) : Option BuiltinKind :=
  (builtinNames.find? (·.1 == name)).map (·.2)

/-- Whether `name` is a reserved builtin identifier. -/
def isBuiltinName (name : Name) : Bool := (builtinKind? name).isSome

/-- Whether `name` is a builtin proof primitive. -/
def isProofPrimitive (name : Name) : Bool := builtinKind? name == some .proof

end LeanPRA.Surface
