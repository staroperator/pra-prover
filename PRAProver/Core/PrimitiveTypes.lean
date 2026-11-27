module

public import PRAProver.Core.Substitution

/-!
# Primitive proof types

These formulas give the types of primitive proof heads. Schema predicates are supplied directly;
ordinary proof and numerical applications supply the remaining arguments.

- `reflexivityType`, `successorNonzeroType`, and `successorInjectivityType` describe
  arithmetic rules.
- `substitutionType` and `existentialEliminationType` describe transport and witness elimination.
- `inductionType` describes induction with a unary quantifier-free motive.
-/

@[expose] public section

namespace PRAProver.Core

/-- The type of equality reflexivity, with the numerical argument explicitly quantified. -/
def reflexivityType : Predicate :=
  .all (.lam ⟨`x, false⟩ (.equal (.bvar 0) (.bvar 0)))

/-- Every successor differs from zero. -/
def successorNonzeroType : Predicate :=
  .all (.lam ⟨`x, false⟩ (.imp (.equal (.app .succ (.bvar 0)) .zero) .false))

/-- Equality of successors implies equality of their predecessors. -/
def successorInjectivityType : Predicate :=
  .all (.lam ⟨`x, true⟩ (.all (.lam ⟨`y, true⟩
    (.imp (.equal (.app .succ (.bvar 1)) (.app .succ (.bvar 0)))
      (.equal (.bvar 1) (.bvar 0))))))

/-- Equality transport for the unary predicate `motive`. -/
def substitutionType (motive : Predicate) : Predicate :=
  .all (.lam ⟨`x, true⟩ (.all (.lam ⟨`y, true⟩
    (.imp (.equal (.bvar 1) (.bvar 0))
      (.imp (.app (motive.shift 2) (.bvar 1)) (.app (motive.shift 2) (.bvar 0)))))))

/-- Eliminate an existential using a universally quantified implication to the outer target. -/
def existentialEliminationType (motive target : Predicate) : Predicate :=
  .imp (.ex motive) (.imp
    (.all (.lam ⟨`x, false⟩ (.imp (.app motive.shift (.bvar 0)) target.shift))) target)

/-- Induction from a base proof and a complete universally quantified step proof. -/
def inductionType (motive : Predicate) : Predicate :=
  .imp (.app motive .zero) (.imp
    (.all (.lam ⟨`x, false⟩
      (.imp (.app motive.shift (.bvar 0)) (.app motive.shift (.app .succ (.bvar 0))))))
    (.all motive))

end PRAProver.Core
