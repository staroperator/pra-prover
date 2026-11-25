# FOL declarations and proofs

Modules in `LeanPRA/Library/FOL/DSL` provide a domain-specific language and interactive tactic
framework for declaring first-order languages, theories, definitions, and proofs inside the PRA
language. Each declaration and tactic script elaborates to ordinary numerical syntax codes and
checked PRA proofs of `FOL.Provable`.

Import `LeanPRA.Library.FOL.DSL.Tactic` for the first-order proof tactics. Theory modules
that re-export it also make those tactics available.

## Module organization

| Module | Responsibility |
| --- | --- |
| `Declaration`, `Schema`, `Theory` | Language metadata, parameterized axiom schemas, and theory declarations. |
| `Syntax`, `Quotation`, `Expression` | Command and quotation syntax, variable binding, and theorem elaboration. |
| `Definition` | `fol_def` declarations and automatic generation of substitution theorems. |
| `Substitution`, `Reduction`, `Decoding` | Symbolic substitutions, proof-producing syntax calculation, and formula decoding. |
| `Display` | Sequent and formula formatting for goals, hypotheses, and diagnostics. |
| `Proof/Derivation`, `Proof/Logic`, `Proof/Emission`, `Proof/Contextual` | Hilbert derivation graphs, logical rules, and checked PRA proof emission under local assumptions. |
| `Tactic/Context` | Goal decoding, local assumption management, definition opening, and rule resolution. |
| `Tactic/Basic` | Introductions, exact proofs, backward application, case splits, and propositional and quantifier steps. |
| `Tactic/Rewrite` | Object-level equality proofs by reflexivity, symmetry, transitivity, congruence, and rewriting. |
| `Tactic/Substitution` | Variable replacement across formulas using object-level equations (`psubst`). |
| `Tactic/Induction` | First-order ordinary and strong induction from declared axiom schemas. |
| `Tactic/SchemaApplication` | Instantiation of formula parameters when applying PRA theorems (`papply`). |

## Languages and theories

`fol_language` and `fol_theory` declare first-order signatures and axiom sets:

```lean
fol_language Arith where
  constant zero
  function succ of 1
  function add of 2

fol_theory Base over Arith where
  axiom add_zero := ∀ x, add(x, zero) = x
  axiom add_succ := ∀ x y, add(x, succ(y)) = succ(add(x, y))

fol_theory AddTheory over Arith extends Base where
  axiom induction (p : formula of 1) :=
    p(zero) → (∀ x, p(x) → p(succ(x))) → ∀ x, p(x)
```

- `constant c` declares a constant symbol. `function f of n` and `relation R of n` declare function
  and relation symbols of arity `n` (relations require `n ≥ 1`). Elaboration produces the
  numerical language definition `Arith.language`.
- `d (k : Nat) : constant` declares a family of constants. Write `d[k]` for member `k`.
- `f (k : Nat) : function of n` and `R (k : Nat) : relation of n` (with `n ≥ 1`) declare
  indexed function and relation families. Write `f[k](t₁, ..., tₙ)` or `R[k](t₁, ..., tₙ)` to
  apply member `k`. Inside the brackets, a numerical PRA expression selects the member.
  Object-variable substitution leaves the member indices unchanged.
- A family may take multiple index parameters, such as `f (a b : Nat) : function of 3`,
  applied as `f[a, b](x, y, z)`. Multiple indices are packed in declaration order using the
  fixed-length tuple encoding (for example, `[a, b]` encodes as `pair a b`, while a single index
  `[k]` is `k` itself).
- The numerical language code is the right-nested tuple `(c, fs, rs, C, F, R)`. The counts `c`
  and `C` give the number of ordinary constants and constant families. The sequences `fs`, `rs`,
  `F`, and `R` store arities minus one for ordinary functions and relations and their families.
  Member `k` of constant family `b` has symbol index `c + C * k + b`. All constant families
  share one residue class in the term encoding when `C > 0`. With `C = 0`, term and formula
  codes are unchanged. Function and relation family applications pair the member number with
  the argument tuple.
- `fol_theory T over L` compiles each `axiom` into a numerical instance constructor and boolean
  membership test, then combines them into `T.isAxiom : Nat → Nat`.
- Adding `extends Parent` includes `Parent.isAxiom` in `T.isAxiom` and generates the theorem
  `T.isAxiom_of_parent : ∀ A, Parent.isAxiom A = 1 → T.isAxiom A = 1`. Proofs from a parent
  theory can be used directly in any extending theory.
- Axiom schemas take syntax parameters `(p : formula of n)` or `(t : term of n)`. For membership
  checking, each parameter must have a recoverable occurrence in the axiom template where it is
  applied to the surrounding bound variables in outermost-first order. A term parameter may
  occur inside a function or relation application. Static `fol_def` abbreviations without PRA
  parameters or splices can appear inside axiom templates.
- A numerical parameter such as `(a : Nat)` can occur as a family index. Include an occurrence
  from which the checker can recover `a`. Other indices can be computed from it.
  For example, in `∀ x, f[a + 1](x) = f[a](x)` the checker reads `a` on the right and compares
  the entire formula with the instance at that value.
- To recover a parameter inside a constructor application, call
  `registerAxiomIndexProjection` with the constructor name and the name of a checked PRA theorem
  of the form `∀ a b, project (build a b) = a`. The checker uses the registered projection to
  read that argument from the index, then compares the entire reconstructed formula.
- An `assuming` clause restricts the parameters by an equality of numerical PRA expressions.
  For example,
  `assuming FOL.Formula.isQuantifierFree Arith.language p = 1` permits induction on a
  quantifier-free formula. The axiom checker applies the test to the recovered formula code.
  A restriction `test = 1` is checked as written; any other equality `a = b` is checked as
  `eqb a b = 1`. The generated theorem for introducing an instance requires a proof of the
  restriction.

## Syntax parameters, definitions, and quotations

`axiom`, `fol_def`, and `fol_theorem` share syntax parameter types alongside ordinary PRA
parameters (`Nat`, `Nat → Nat`, and predicates):

- `term` (or `term of 0`) and `formula` (or `formula of 0`) represent a term or formula code in the
  surrounding variable context.
- `term of n` and `formula of n` take `n` explicit term arguments in addition to any captured free
  variables from the surrounding context. The last explicit argument occupies de Bruijn index `0`,
  the preceding argument occupies index `1`, and so on.

### First-order definitions (`fol_def`)

`fol_def` defines a parameterized term or formula constructor over a declared language:

```lean
fol_def double over Arith (x : term) : term := add(x, x)

fol_def le over Arith (x y : term) : formula := ∃ z, add(z, x) = y

fol_def diagonal over Arith (p : formula of 2) (x : term) : formula :=
  ∀ y, p(x, y)

fol_def above over Arith (w x : term) : formula :=
  diagonal (p := fun u v => add(u, v) = w)(x)
```

In a quotation, arity-zero term inputs are passed positionally, as in `double(x)` or
`le(x, y)`. All other inputs use named actuals `(name := ...)` before the positional list.
A syntax input can be supplied as a lambda `(p := fun u v => ...)`, a formula or partial
application `(p := R)`, or an injected numerical code `(p := ${code})`. A named actual is read
as first-order syntax whenever it parses that way, and as a PRA expression otherwise. A `Nat`
input written as a name, an application with spaces, or a parenthesized form is converted
from that first-order reading; any other PRA expression for a `Nat` input is written as a braced
splice `(n := ${expr})`.

Results also accept `term of n` and `formula of n`. A lambda names the explicit result slots:

```lean
fol_def equation over Arith : formula of 2 := fun x y => x = y

fol_def equationAlias over Arith : formula of 2 := equation

fol_def numeral over Arith (n : Nat) : term :=
  ${primrec (FOL.Term.const Arith.language 0)
    (fun _ t => FOL.Term.app Arith.language 0 t) n}
```

Write `equation(x, y)` to fill its slots, or pass `equation` to a `formula of 2` parameter.
Ordinary declaration term arguments come first, followed by the result slots. A computed term
such as `numeral (n := n)()` can likewise be used directly in FOL syntax.

Inputs in the declaration header become PRA declaration parameters. Arrow domains become
ordinary PRA arguments. Both support syntax inputs, and ordinary inputs may mix `Nat`,
`term of n`, and `formula of n` in any order. Each becomes a numerical argument to the
generated PRA function. Header parameters and ordinary arguments each keep their source order.
The body lambda names the ordinary arguments first, then any explicit slots of the result.

`derive_primrec` can compile an ordinary input as part of the program's runtime input.

```lean
fol_def numeralFunction over Arith : Nat → term := fun n =>
  ${primrec (FOL.Term.const Arith.language 0)
    (fun _ t => FOL.Term.app Arith.language 0 t) n}

derive_primrec numeralFunction

fol_def specialize over Arith (t : term) (p : formula of 1) :
    formula of 1 → term → formula := fun q x => p(x) → q(t)
```

Write `numeralFunction n` in a PRA expression and `numeralFunction (n := n)()` in a quotation.
In a quotation, `specialize (p := R) (q := S)(u, v)` supplies `u` for `t` and `v` for `x`.
The returned formula is `R(v) → S(u)`.

The entire body may be `${...}`, including when the result has explicit slots. The author of
the PRA expression supplies its variable context and slot layout: the last result argument
occupies position zero, and captured variables follow the result slots. The annotation records
how callers use the result; it does not check the injected code's free-variable bound or prove
that it has the declared syntax shape. Within an FOL body, splices keep the existing rule that
entering a binder shifts their surrounding variables.

When a term or formula definition `D` has a body whose substitutions can be proved automatically,
`fol_def` generates a theorem `D.subst` for `Term.subst` or `Formula.subst`, respectively. This
pushes substitutions directly into the arguments of `D` without unfolding its body. If a
substitution needs the body of a term definition, it can use a registered equation or open the
definition. Definitions with explicit result slots use unfolding and registered equations.

The definitions and their constructor equations are in
[Common/Substitution.lean](../Common/Substitution.lean).
`Term.subst f L t` replaces each variable of index `i` in the term `t` by `f i`.
`Formula.subst f L A` lifts `f` beneath quantifiers to avoid capture. Its underlying operation,
`Formula.substWithDepth f L A d`, passes the current binder depth and variable index to `f`,
which determines the replacement term.

### Quotations and splices

First-order terms and formulas can be quoted as numerical codes inside ordinary PRA expressions, or
spliced from PRA expressions into FOL syntax:

| Notation | Meaning |
| --- | --- |
| `fol_term[L \| t]` | Numerical code of the first-order term `t` in language `L`. |
| `fol_formula[L \| A]` | Numerical code of the first-order formula `A` in language `L`. |
| `T ⊢ A` | PRA proposition `FOL.Provable L.language T.isAxiom fol_formula[L \| A]`. |
| `T ⊢ free x y \| A` | Provability of `A` with free object variables `x`, `y` bound to variable codes `0`, `1`, ... |
| `${e}` | Splice a numerical PRA expression `e` as a term or formula code, shifting free variables under binders. |
| `${p}[t₁, ..., tₙ]` | Instantiate the first `n` slots of a raw formula code `p` with terms `t₁, ..., tₙ` (with `tₙ` at index `0`). |

```lean
def reflFormula (t : Nat) : Nat :=
  fol_formula[Arith | ${t} = ${t}]

fol_def boundedAll over Arith (b : term) (p : Nat) : formula :=
  ∀ x, le(x, b) → ${p}[x]
```

Inside term quotations, a constant `c` can also be written `c()` to distinguish it from a bound
variable of the same name. Language modules can define custom syntax macros for terms and formulas
and register `@[fol_term_display symbol]` handlers to format goals and diagnostics using that
notation.

## Theorems and local contexts

`fol_theorem` declares a checked PRA theorem whose conclusion is `FOL.Provable`:

```lean
fol_theorem id_imp (n : Nat) (p : formula of 1) : AddTheory ⊢ ∀ x, p(x) → p(x) :=
  ...

fol_theorem open_id_imp : AddTheory ⊢ free x | zero = x → zero = x :=
  ...
```

`free x₁ x₂ ... |` pre-introduces free object variables at the start of the statement and proof.
FOL proofs run inside the standard PRA `by` block, so ordinary PRA tactics (`have`, `let`, `rw`,
`exact`, `induction`, `sigma_induction`) and combinators (`·`, `<;>`, `first`, `try`, `repeat`) can
be freely combined with FOL tactics.

### Sequent display and local assumptions

Inside a proof, a goal with local object assumptions `h₁ : A₁, h₂ : A₂` and conclusion `C`
is represented as `FOL.Sequent L T Γ C`, which unfolds to `FOL.Provable L T` of the iterated
implication from the assumption list `Γ` to `C`. Goals with local assumptions are displayed in
sequent notation with one assumption per line, the oldest first:

```text
T;
h₁ : A₁
h₂ : A₂
⊢ C
```

Proofs from the environment or local PRA hypotheses can be used in a goal when they have no object
assumptions or share the goal's assumption list, and proofs from a parent theory are automatically
lifted along the `extends` chain.

## Logical and structural tactics

In `pexact`, `papply`, and `pcases`, the bracketed list `[t₁, t₂, ...]` instantiates leading
object-level universal quantifiers of the supplied rule. When no object terms are needed, the
brackets can be omitted.

| Tactic | Action |
| --- | --- |
| `pintro x₁ x₂ ...` | Introduce object universal variables (shifting assumptions in `Γ` and binding `xᵢ` at index `0`) or move implication premises into `Γ`. |
| `passumption` | Close the goal using a matching object assumption (or an implication premise in the goal). |
| `pexact h[t₁, ...]` | Close the goal with an assumption, axiom, or theorem `h` instantiated at `t₁, ...`. |
| `pexact ax (p := ...) [t₁, ...]` | Instantiate syntax parameters of an axiom schema `ax` and close the goal. |
| `pexact ax (p := ...) (assuming := h) [t₁, ...]` | Also supply a PRA proof `h` of the restriction of `ax` at these arguments. |
| `pexact (e)[t₁, ...]` | Close the goal with a parenthesized PRA proof expression `e` instantiated at `t₁, ...`. |
| `papply e[t₁, ...]` | Apply `e` (instantiated at `t₁, ...`) backward, projecting through conjunctions if needed and leaving premises as subgoals. |
| `papply thm (p := ...) [t₁, ...]` | Instantiate syntax parameters of a PRA theorem `thm`, calculate the resulting formula, and apply it backward. |
| `pcases e[t₁, ...] with pat` | Eliminate `e[t₁, ...]` and name its components using a pattern. |
| `pconstructor` | Split a conjunction (`A ∧ B`) or equivalence (`A ↔ B`) goal into two subgoals. |
| `pleft`, `pright` | Reduce a disjunction goal `A ∨ B` to `A` or `B`. |
| `pexists t` | Provide the object term `t` as a witness for an existential goal `∃ x, A`. |
| `phave h : A` | Open a subgoal to prove `A`, then add `h : A` to the local assumptions of the main goal. |
| `pexfalso` | Replace the current object goal with `⊥`. |
| `pcontradiction` | When the goal is `⊥`, close it by modus ponens among local assumptions; otherwise replace the goal `A` with `¬¬ A`. |

For a schema with an `assuming` restriction, the restriction must hold at the supplied
arguments. `(assuming := h)` names a PRA proof expression for it, written like an argument of
`exact`. Without it, the tactic looks for a local PRA hypothesis that states the restriction
(or, for a restriction `eqb a b = 1`, the equation `a = b`), then calculates the test; a value
`1` closes it, and a simplified test is compared with the hypotheses again. Otherwise the tactic
reports the required equation.

`pcases e with pat` combines elimination and introductions:

- `⟨x, hx⟩` names an existential witness and its property.
- `⟨ha, hb⟩` names the two parts of a conjunction or equivalence.
- `ha | hb` names the assumption in each of two disjunction branches.
- Patterns nest: `⟨x, (ha, hb) | hc⟩` opens an existential and then a disjunction whose first
  branch contains a conjunction. A longer tuple such as `⟨x, ha, hb⟩` associates to the right.
- `_` ignores a component. Parenthesized tuples `(x, hx)` have the same meaning as `⟨x, hx⟩`.

When `e` is a local hypothesis, it is removed from the resulting branches, so its name can be
reused in the pattern. Patterns affect only the current goal; other pending goals keep their
order. Every `pcases` invocation supplies a `with` pattern.

When `pcontradiction` is used on a goal `A` other than `⊥`, it applies classical
double-negation elimination and leaves `¬ A → ⊥`; follow with `pintro hn` to assume `hn : ¬ A`
with target `⊥`.

```lean
fol_theorem and_symm (p q : formula) : AddTheory ⊢ p ∧ q → q ∧ p := by
  pintro hpq
  pcases hpq with ⟨hp, hq⟩
  pconstructor
  · passumption
  · passumption
```

## Equality and substitution tactics

| Tactic | Action |
| --- | --- |
| `prefl` | Close an equation `t = t` by reflexivity (also discharging any leading implication premises). |
| `psymm` | Replace an equality goal `t = u` with `u = t`. |
| `ptrans u` | Split an equality goal `t = v` into two goals `t = u` and `u = v`. |
| `pcongr` | Reduce `f(t₁, ..., tₙ) = f(u₁, ..., uₙ)` to subgoals `t₁ = u₁`, ..., `tₙ = uₙ`. |
| `prw [r₁, r₂, ...]` | Close an equation by rewriting both sides with equality axioms, theorems, or assumptions `rᵢ` and comparing the results. |
| `prw [D]`, `prw [D] at h` | Open the term or formula definition `D` in the goal or in `h`. |
| `psubst h` | Given an equality proof or assumption `h` of `x = t` for an object variable `x`, replace `x` with `t` throughout the goal formula. |

```lean
fol_theorem le_trans : AddTheory ⊢ ∀ x y z, le(x, y) → le(y, z) → le(x, z) := by
  pintro x y z hxy hyz
  pcases hxy with ⟨a, ha⟩
  pcases hyz with ⟨b, hb⟩
  pexists add(b, a)
  prw [add_assoc, ha, hb]

fol_theorem le_of_eq : AddTheory ⊢ ∀ x y, x = y → le(x, y) := by
  pintro x y h
  psubst h
  pexact le_refl[y]
```

In `prw [r₁, r₂, ...]`, each equality rule `rᵢ` can be a universally quantified equation or a
plain equation from the theory, local assumptions, or PRA environment. Universal variables in a
rule are matched against subterms from the inside out, earlier rules normalize later rules in the
list, and both sides of the target equation are rewritten to a common term. To replace an object
variable inside a non-equality formula (such as a relation or quantifier body), use `psubst`.

### Opening definitions in proofs

Term definitions with no explicit result slots and formula definitions with a `.subst` theorem
stay closed in proof goals until a tactic needs to inspect their body:

- Connective-directed tactics (`pintro`, `pconstructor`, `pleft`, `pright`, `pexists`, `pcases`,
  `papply`, `ptrans`, `psymm`, and `pcongr`) open definitions at the head of the formula they
  inspect while keeping inner definitions closed.
- Matching tactics (`passumption`, `pexact`, and `papply`) reconcile formulas that agree after
  opening definitions, unfolding only at the positions where the two formulas differ.
- `prw [D]` explicitly unfolds `D` in the goal, and `prw [D] at h` unfolds `D` in the local
  assumption `h`.

If a tactic fails while definitions are closed, it automatically retries with all definitions
opened. Setting `set_option fol.openDefinitions true` opens all definitions eagerly in every step.

## Induction

### First-order induction (`pinduction`)

`pinduction` applies an induction axiom schema declared in the active theory:

```lean
fol_theorem zero_add : AddTheory ⊢ ∀ x, add(zero, x) = x := by
  pintro x
  pinduction x using AddTheory.induction (motive := fun n => add(zero, n) = n) with
  | zero =>
    prw [add_zero]
  | succ k ih =>
    prw [add_succ, ih]
```

For a strong induction schema of the form `(∀ x, H(x) → p(x)) → ∀ x, p(x)`, use a single
`step` branch:

```lean
pinduction x using AddTheory.strong_ind with
| step k ih =>
  ...
```

- `x` must be an introduced object variable in the current goal.
- `using schema` is optional when the theory has a single induction schema.
- `(assuming := h)` supplies a PRA proof of the schema's restriction for the motive. Without it,
  the restriction is discharged like an axiom application: from a local PRA hypothesis or by
  calculation. A restriction on quantifier-freeness holds for a motive `${P}[x]` whenever
  `FOL.Formula.isQuantifierFree L P = 1` is a hypothesis, because substitution preserves
  quantifier-freeness.
- `(motive := fun n => A)` is optional and checks that the written motive matches the current goal
  with `x` replaced by `n`.
- In the `succ k ih` (or `step k ih`) branch, `k` is introduced as the object variable and `ih` is
  introduced as a local assumption in the sequent context.
- Surrounding local assumptions remain fixed in the context across all branches. If an assumption
  depends on the induction variable `x`, leave it as an implication in the goal before calling
  `pinduction` so that it is included in the induction motive.

### Meta-level family induction (`sigma_induction`)

Because `FOL.Provable L T A` is an existential statement (`∃ p, Proof L T p A`) with a
quantifier-free matrix, families of theorems parameterized by a PRA number `n : Nat` can be proved
using `sigma_induction`:

```lean
fol_theorem iter_succ_refl (n : Nat) :
    AddTheory ⊢
      ${iter (FOL.Term.app Arith.language 0) n (FOL.Term.const Arith.language 0)} =
      ${iter (FOL.Term.app Arith.language 0) n (FOL.Term.const Arith.language 0)} := by
  sigma_induction n with k ih
  · prefl
  · rw [iter_succ (FOL.Term.app Arith.language 0)]
    pcongr
    exact ih
```

In the `succ k ih` branch, `ih` is a PRA hypothesis proving the `k` instance, which can be passed to
`exact`, `pexact`, or `papply`. The witness compiler extracts a primitive-recursive derivation
constructor and checks its validity proof in the PRA core checker.

## Symbolic calculation hooks

Proof steps frequently compare formula codes after substitution or definition unfolding. The
symbolic evaluator in `Reduction` proves these code equations automatically and provides three
registration hooks for custom syntax builders:

- `registerClosedTerm symbol thm`: register a theorem
  `thm (f : Nat → Nat) : ∀ xs, FOL.Term.subst f L (symbol xs) = symbol xs` so that `symbol xs`
  is treated as a closed term with no free object variables.
- `registerCalculation thm`: register a quantifier-free numerical equation `∀ xs, lhs = rhs`
  without proof premises as a reduction rule during symbolic syntax calculation.
- `registerFormulaBuilder symbol thm`: register a substitution theorem for a custom numerical
  formula constructor `symbol` so the frontend tracks its term arguments across substitutions.
