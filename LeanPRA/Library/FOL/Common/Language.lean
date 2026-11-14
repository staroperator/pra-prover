module

public import LeanPRA.Library.Nat.Sequence

/-!
# Finite first-order languages

A language is a numerical triple of a constant count, positive function arities, and positive
relation arities. Arity sequences store predecessors of the positive arities. Equality and the
infinite collection of numerical variable indices are shared by every language.

- `Language.make` packs the three fields into one number, and `Language.constants`,
  `Language.functions`, and `Language.relations` read them back.
- `Language.functionCount` and `Language.relationCount` return the symbol counts.
- `Language.functionArity` and `Language.relationArity` read positive symbol arities.
-/

@[expose] public section

pra

namespace FOL

namespace Language

/--
`Language.make c fs rs` encodes a language with `c` constants as `pair c (pair fs rs)`.
`fs` and `rs` are sequence codes storing the arity minus one of each positive-arity function
and relation, respectively. Symbol indices start at zero within each of the three groups.
-/
def make : Nat → Nat → Nat → Nat := fun c fs rs => pair c (pair fs rs)

/-- `Language.constants L` is the number of constant symbols in language code `L`. -/
def constants : Nat → Nat := unpairLeft

/--
`Language.functions L` is the sequence code of positive function arities minus one in
language code `L`. Entry `j` describes function symbol `j`.
-/
def functions : Nat → Nat := fun L => unpairLeft (unpairRight L)

/--
`Language.relations L` is the sequence code of positive relation arities minus one in
language code `L`. Entry `j` describes positive-arity relation symbol `j`.
-/
def relations : Nat → Nat := fun L => unpairRight (unpairRight L)

/--
`Language.functionCount L` is the number of positive-arity function symbols in language code `L`.
-/
def functionCount : Nat → Nat := fun L => Sequence.length (functions L)

/--
`Language.relationCount L` is the number of positive-arity relation symbols in language code `L`.
-/
def relationCount : Nat → Nat := fun L => Sequence.length (relations L)

/--
`Language.functionArity L j` is the positive arity of function symbol `j` in language code `L`,
for `j < Language.functionCount L`.
-/
def functionArity : Nat → Nat → Nat := fun L j => S (Sequence.get (functions L) j)

/--
`Language.relationArity L j` is the positive arity of relation symbol `j` in language code `L`,
for `j < Language.relationCount L`.
-/
def relationArity : Nat → Nat → Nat := fun L j => S (Sequence.get (relations L) j)

theorem constants_make : ∀ c fs rs, constants (make c fs rs) = c := by
  intro c fs rs
  exact unpairLeft_pair c (pair fs rs)

theorem functions_make : ∀ c fs rs, functions (make c fs rs) = fs := by
  intro c fs rs
  rw [functions, make, unpairRight_pair, unpairLeft_pair]

theorem relations_make : ∀ c fs rs, relations (make c fs rs) = rs := by
  intro c fs rs
  rw [relations, make, unpairRight_pair, unpairRight_pair]

theorem functionCount_make : ∀ c fs rs, functionCount (make c fs rs) = Sequence.length fs := by
  intro c fs rs
  rw [functionCount, functions_make]

theorem functionArity_make : ∀ c fs rs j,
    functionArity (make c fs rs) j = S (Sequence.get fs j) := by
  intro c fs rs j
  rw [functionArity, functions_make]

theorem relationCount_make : ∀ c fs rs,
    relationCount (make c fs rs) = Sequence.length rs := by
  intro c fs rs
  rw [relationCount, relations_make]

end Language

end FOL

end
