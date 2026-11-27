module

public import PRAProver.Library.Nat.DivMod
public import PRAProver.Library.Nat.Sequence

/-!
# First-order languages

A first-order language is encoded as a sextuple `(c, fs, rs, C, F, R)`. The counts `c` and `C`
give the number of ordinary constants and the number of constant families. The sequences `fs` and
`rs` list ordinary functions and relations. The sequences `F` and `R` list function and relation
families. Each entry in these four sequences stores the arity minus one.

An ordinary function such as binary `+` has its own entry in `fs`. A family has one member for each
natural number. For example, one family can supply a symbol for each unary primitive recursive
function. The frontend packs multiple indices into a single member number using `pair`. All members
of a function or relation family have the same positive arity. Different families can have different
arities. Since the four sequences are finite, a language can have infinitely many symbols but only
finitely many distinct arities.

In `Syntax.lean`, a constant is a term on its own and a function application has at least one
argument. With these conventions, each natural number encodes exactly one term and exactly one
formula in a given language, and each term and each formula has a unique code.
-/

@[expose] public section

pra

namespace FOL

namespace Language

/-! ## Signature

- `Language.make` encodes the six fields, and the projections recover them.
- `Language.functionCount` and `Language.relationCount` count ordinary symbols of positive arity.
- `Language.functionArity`, `Language.relationArity`, `Language.functionFamilyArity`, and
  `Language.relationFamilyArity` read arities from the four sequences.
-/

/--
`Language.make c fs rs C F R` encodes `pair c (pair fs (pair rs (pair C (pair F R))))`. The ordinary
constant count is `c` and the constant family count is `C`. Each sequence stores arities minus one.
The sequences `fs` and `rs` describe ordinary functions and relations. The sequences `F` and `R`
describe their indexed families. Indices in each field start at zero.
-/
def make : Nat → Nat → Nat → Nat → Nat → Nat → Nat :=
  fun c fs rs C F R => pair c (pair fs (pair rs (pair C (pair F R))))

/-- The number of ordinary constant symbols in language code `L`. -/
def constants : Nat → Nat := unpairLeft

/-- The sequence of ordinary positive function arities minus one in language code `L`. -/
def functions : Nat → Nat := fun L => unpairLeft (unpairRight L)

/-- The sequence of ordinary relation arities minus one in language code `L`. -/
def relations : Nat → Nat := fun L => unpairLeft (unpairRight (unpairRight L))

/-- The number of indexed constant families in language code `L`. -/
def constantFamilyCount : Nat → Nat :=
  fun L => unpairLeft (unpairRight (unpairRight (unpairRight L)))

/-- The sequence of function-family arities minus one in language code `L`. -/
def functionFamilies : Nat → Nat :=
  fun L => unpairLeft (unpairRight (unpairRight (unpairRight (unpairRight L))))

/-- The sequence of relation-family arities minus one in language code `L`. -/
def relationFamilies : Nat → Nat :=
  fun L => unpairRight (unpairRight (unpairRight (unpairRight (unpairRight L))))

def functionCount : Nat → Nat := fun L => Sequence.length (functions L)

def relationCount : Nat → Nat := fun L => Sequence.length (relations L)

def functionFamilyCount : Nat → Nat := fun L => Sequence.length (functionFamilies L)

def relationFamilyCount : Nat → Nat := fun L => Sequence.length (relationFamilies L)

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

def functionFamilyArity : Nat → Nat → Nat :=
  fun L b => S (Sequence.get (functionFamilies L) b)

def relationFamilyArity : Nat → Nat → Nat :=
  fun L b => S (Sequence.get (relationFamilies L) b)

theorem constants_make : ∀ c fs rs C F R, constants (make c fs rs C F R) = c :=
  fun c fs rs C F R => unpairLeft_pair c (pair fs (pair rs (pair C (pair F R))))

theorem functions_make : ∀ c fs rs C F R, functions (make c fs rs C F R) = fs := by
  intro c fs rs C F R
  rw [functions, make, unpairRight_pair, unpairLeft_pair]

theorem relations_make : ∀ c fs rs C F R, relations (make c fs rs C F R) = rs := by
  intro c fs rs C F R
  rw [relations, make, unpairRight_pair, unpairRight_pair, unpairLeft_pair]

theorem constantFamilyCount_make : ∀ c fs rs C F R,
    constantFamilyCount (make c fs rs C F R) = C := by
  intro c fs rs C F R
  rw [constantFamilyCount, make, unpairRight_pair, unpairRight_pair, unpairRight_pair,
    unpairLeft_pair]

theorem functionFamilies_make : ∀ c fs rs C F R, functionFamilies (make c fs rs C F R) = F := by
  intro c fs rs C F R
  rw [functionFamilies, make, unpairRight_pair, unpairRight_pair, unpairRight_pair,
    unpairRight_pair, unpairLeft_pair]

theorem relationFamilies_make : ∀ c fs rs C F R, relationFamilies (make c fs rs C F R) = R := by
  intro c fs rs C F R
  rw [relationFamilies, make, unpairRight_pair, unpairRight_pair,
    unpairRight_pair, unpairRight_pair, unpairRight_pair]

theorem functionCount_make : ∀ c fs rs C F R,
    functionCount (make c fs rs C F R) = Sequence.length fs := by
  intro c fs rs C F R
  rw [functionCount, functions_make]

theorem functionArity_make : ∀ c fs rs C F R j,
    functionArity (make c fs rs C F R) j = S (Sequence.get fs j) := by
  intro c fs rs C F R j
  rw [functionArity, functions_make]

theorem relationCount_make : ∀ c fs rs C F R,
    relationCount (make c fs rs C F R) = Sequence.length rs := by
  intro c fs rs C F R
  rw [relationCount, relations_make]

/-!
## Constant, function and relation symbols

Constants, functions, and relations are numbered separately. Within each kind, the first `p` indices
name the ordinary symbols. With `f` families of that kind, member `k` of family `b < f` has index
`p + (f * k + b)`.

- `Language.constantFamilyMember`, `Language.functionFamilyMember`, and
  `Language.relationFamilyMember` give the symbol index of a family member.
- `Language.IsConstant`, `Language.IsFunction`, and `Language.IsRelation` test symbol membership.
- `Language.functionSymbolArity` and `Language.relationSymbolArity` give the number of term
  arguments for either an ordinary symbol or a family member.
-/

/-- The constant symbol index for member `k` of family `b < constantFamilyCount L`. -/
def constantFamilyMember : Nat → Nat → Nat → Nat := fun L b k =>
  constants L + (constantFamilyCount L * k + b)

/-- With at least one constant family, every index names a constant. Otherwise, only the
ordinary indices below `constants L` do. -/
def IsConstant : Nat → Nat → QFProp := fun L j =>
  j < constants L ∨ ¬ constantFamilyCount L = 0

theorem isConstant_of_lt : ∀ L j, j < constants L → IsConstant L j := by
  intro L j h
  left
  exact h

theorem isConstant_of_constantFamilyCount_pos : ∀ L j,
    0 < constantFamilyCount L → IsConstant L j := by
  intro L j h
  right
  exact ne_zero_of_pos _ h

/-- The function symbol index for member `k` of family `b < functionFamilyCount L`. -/
def functionFamilyMember : Nat → Nat → Nat → Nat := fun L b k =>
  functionCount L + (functionFamilyCount L * k + b)

/-- The relation symbol index for member `k` of family `b < relationFamilyCount L`. -/
def relationFamilyMember : Nat → Nat → Nat → Nat := fun L b k =>
  relationCount L + (relationFamilyCount L * k + b)

def IsFunction : Nat → Nat → QFProp := fun L j =>
  let p := functionCount L;
  let f := functionFamilyCount L;
  ite (ltb j p) j (p + ((j - p) % f)) < p + f

def IsRelation : Nat → Nat → QFProp := fun L j =>
  let p := relationCount L;
  let f := relationFamilyCount L;
  ite (ltb j p) j (p + ((j - p) % f)) < p + f

/-- The positive number of term arguments of function symbol `j`. -/
def functionSymbolArity : Nat → Nat → Nat := fun L j =>
  let p := functionCount L;
  S (ite (ltb j p) (Sequence.get (functions L) j)
    (Sequence.get (functionFamilies L) ((j - p) % functionFamilyCount L)))

/-- The positive number of term arguments of relation symbol `j`. -/
def relationSymbolArity : Nat → Nat → Nat := fun L j =>
  let p := relationCount L;
  S (ite (ltb j p) (Sequence.get (relations L) j)
    (Sequence.get (relationFamilies L) ((j - p) % relationFamilyCount L)))

theorem functionSymbolArity_pos : ∀ L j, 0 < functionSymbolArity L j :=
  fun L j => and_right (lt_succ 0 _) (zero_le _)

theorem relationSymbolArity_pos : ∀ L j, 0 < relationSymbolArity L j :=
  fun L j => and_right (lt_succ 0 _) (zero_le _)

theorem isFunction_of_lt : ∀ L j, j < functionCount L → IsFunction L j := by
  intro L j h
  rw [IsFunction, and_right (ltb_eq_one j (functionCount L)) h, ite_succ]
  exact lt_of_lt_of_le _ _ _ h (le_add_right _ _)

theorem isFunction_familyMember : ∀ L b k, b < functionFamilyCount L →
    IsFunction L (functionFamilyMember L b k) := by
  intro L b k h
  let p := functionCount L
  let f := functionFamilyCount L
  let j := functionFamilyMember L b k
  have hb : ite (ltb j p) j (p + ((j - p) % f)) = p + b :=
    ite_ltb_mod_mul_add_of_lt p f b k h
  rw [IsFunction, hb]
  exact add_lt_add_left _ _ _ h

theorem functionSymbolArity_of_lt : ∀ L j, j < functionCount L →
    functionSymbolArity L j = functionArity L j := by
  intro L j h
  rw [functionSymbolArity, and_right (ltb_eq_one j (functionCount L)) h, ite_succ]
  rfl

theorem functionSymbolArity_familyMember : ∀ L b k, b < functionFamilyCount L →
    functionSymbolArity L (functionFamilyMember L b k) = functionFamilyArity L b := by
  intro L b k h
  have hf := ne_zero_of_pos _ (lt_of_le_of_lt 0 b _ (zero_le b) h)
  rw [functionSymbolArity, functionFamilyMember, ltb_eq_zero_of_ge _ _ (le_add_right _ _),
    ite_zero, add_sub_self_left, mod_mul_add_of_lt _ k b hf h]
  rfl

theorem functionSymbolArity_ite_ltb_mod : ∀ L j,
    functionSymbolArity L (ite (ltb j (functionCount L)) j
      (functionCount L + ((j - functionCount L) % functionFamilyCount L))) =
      functionSymbolArity L j := by
  intro L j
  exact eq_congr S (ite_ltb_apply_mod_mod (Sequence.get (functions L))
    (Sequence.get (functionFamilies L)) (functionCount L) (functionFamilyCount L) j)

theorem isRelation_of_lt : ∀ L j, j < relationCount L → IsRelation L j := by
  intro L j h
  rw [IsRelation, and_right (ltb_eq_one j (relationCount L)) h, ite_succ]
  exact lt_of_lt_of_le _ _ _ h (le_add_right _ _)

theorem isRelation_familyMember : ∀ L b k, b < relationFamilyCount L →
    IsRelation L (relationFamilyMember L b k) := by
  intro L b k h
  let p := relationCount L
  let f := relationFamilyCount L
  let j := relationFamilyMember L b k
  have hb : ite (ltb j p) j (p + ((j - p) % f)) = p + b :=
    ite_ltb_mod_mul_add_of_lt p f b k h
  rw [IsRelation, hb]
  exact add_lt_add_left _ _ _ h

theorem relationSymbolArity_of_lt : ∀ L j, j < relationCount L →
    relationSymbolArity L j = relationArity L j := by
  intro L j h
  rw [relationSymbolArity, and_right (ltb_eq_one j (relationCount L)) h, ite_succ]
  rfl

theorem relationSymbolArity_familyMember : ∀ L b k, b < relationFamilyCount L →
    relationSymbolArity L (relationFamilyMember L b k) = relationFamilyArity L b := by
  intro L b k h
  have hf := ne_zero_of_pos _ (lt_of_le_of_lt 0 b _ (zero_le b) h)
  rw [relationSymbolArity, relationFamilyMember, ltb_eq_zero_of_ge _ _ (le_add_right _ _),
    ite_zero, add_sub_self_left, mod_mul_add_of_lt _ k b hf h]
  rfl

theorem relationSymbolArity_ite_ltb_mod : ∀ L j,
    relationSymbolArity L (ite (ltb j (relationCount L)) j
      (relationCount L + ((j - relationCount L) % relationFamilyCount L))) =
      relationSymbolArity L j := by
  intro L j
  exact eq_congr S (ite_ltb_apply_mod_mod (Sequence.get (relations L))
    (Sequence.get (relationFamilies L)) (relationCount L) (relationFamilyCount L) j)

end Language

end FOL

end
