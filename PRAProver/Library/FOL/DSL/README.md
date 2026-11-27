# FOL declarations and proofs

Modules in `PRAProver/Library/FOL/DSL` provide a domain-specific language and interactive tactic
framework for declaring first-order languages, theories, definitions, and proofs inside the PRA
language. Each declaration and tactic script elaborates to ordinary numerical syntax codes and
checked PRA proofs of `FOL.Provable`.

Import `PRAProver.Library.FOL.DSL.Tactic` for the first-order proof tactics. Theory modules
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
  membership test, then combines them into `T.isAxiom : Nat → Nat`. Each axiom `ax` with
  parameters `ps` and restriction `r` also becomes the theorem `T.ax : ∀ ps, r → T ⊢ A`, proved
  from the membership test. Proofs use axioms through these theorems, exactly like any other
  theorem with term or formula parameters.
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
  `eqb a b = 1`. The theorem `T.ax` takes a proof of the restriction as a PRA antecedent.

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
fol_def double over Arith : term of 1 := fun x => add(x, x)

fol_def le over Arith : formula of 2 := fun x y => ∃ z, add(z, x) = y

fol_def diagonal over Arith (p : formula of 2) : formula of 1 := fun x => ∀ y, p(x, y)

fol_def above over Arith (w : term) : formula of 1 := fun x =>
  (diagonal (fun u v => add(u, v) = w))(x)
```

The header binders are the parameters of the definition. `of n` in the result type is the number
of term slots of the result, and the lambda after `:=` names them. In a quotation, the
application form `(D a₁ … aₘ)` supplies the parameters in declaration order, and the slot list
`(t₁, …, tₙ)` fills the slots: `le(x, y)`, `(diagonal p)(x)`, `(above w)(x)`. A definition
without parameters is written without the application form, and one without slots without the
slot list. First-order application binds tighter than PRA application: `D(…)` and `f[…]` follow
the name without a space. The application form without a slot list may drop its parentheses
where the position accepts a term or formula of any precedence, as in `isTotal p ∧ q` or
`x + num n`; with a slot list, or as an argument of another application form, it keeps them,
since each argument of an application form is atomic. Each argument is parsed both as an atomic
first-order expression and as an atomic PRA expression, and the declared type of the parameter
selects the reading. A `term of n` or
`formula of n` parameter takes the first-order reading: a name, an application such as
`R(u, v)`, a parenthesized term or formula, a lambda `(fun u v => …)`, a numeral when the
language declares numeral notation, or an injected code `${code}`. A `Nat` parameter, or any
other PRA parameter, takes the PRA reading: a name, a numeral, a hole `_`, or a parenthesized
PRA expression such as `(a * k)` or `(f a b)`. So `(a * k)` is the symbol application
`mul(a, k)` for a term parameter and the PRA product for a `Nat` parameter. A braced splice
`${expr}` is needed only where the text has no reading of the wanted kind, such as a bare PRA
name holding a code where a formula parameter is expected. A named argument `(x := a)` fills an
implicit binder `{x : …}`.

Results also accept `term of n` and `formula of n`. A lambda names the explicit result slots:

```lean
fol_def equation over Arith : formula of 2 := fun x y => x = y

fol_def equationAlias over Arith : formula of 2 := equation

fol_def numeral over Arith (n : Nat) : term :=
  ${primrec (FOL.Term.const Arith.language 0)
    (fun _ t => FOL.Term.app Arith.language 0 t) n}
```

Without the lambda, the body is a value of the result type: another definition, a partial
application, or a spliced code whose slots are the de Bruijn indices `0` to `n - 1`. Write
`equation(x, y)` to fill its slots, or pass `equation` to a `formula of 2` parameter. A computed
term such as `(numeral n)` can likewise be used directly in FOL syntax.

Inputs in the declaration header become PRA declaration parameters. Arrow domains become
ordinary PRA arguments. Both support syntax inputs, and ordinary inputs may mix `Nat`,
`term of n`, and `formula of n` in any order. Each becomes a numerical argument to the
generated PRA function. Header parameters and ordinary arguments each keep their source order.
The body lambda names the ordinary arguments first, then the result binders. The result binders
are term parameters of the generated function, placed after the header parameters, so the
function of `le` above is `le x y`.

`derive_primrec` can compile an ordinary input as part of the program's runtime input.

```lean
fol_def numeralFunction over Arith : Nat → term := fun n =>
  ${primrec (FOL.Term.const Arith.language 0)
    (fun _ t => FOL.Term.app Arith.language 0 t) n}

derive_primrec numeralFunction

fol_def specialize over Arith (t : term) (p : formula of 1) :
    formula of 1 → formula of 1 := fun q x => p(x) → q(t)
```

Write `numeralFunction n` in a PRA expression and `(numeralFunction n)` in a quotation. In a
quotation, `(specialize u R S)(v)` supplies `u` for `t`, `R` for `p`, `S` for `q`, and `v` for
the slot `x`. The returned formula is `R(v) → S(u)`.

The entire body may be `${...}`. With result binders, the expression uses them as term codes.
Without result binders, the author of the PRA expression supplies its slot layout and variable
context: the last result slot occupies position zero, and captured variables follow the result
slots. The annotation records how callers use the result; it does not check the injected code's
free-variable bound or prove that it has the declared syntax shape. Within an FOL body, splices
keep the existing rule that entering a binder shifts their surrounding variables.

When a term or formula definition `D` has a body whose substitutions can be proved automatically,
`fol_def` generates a theorem `D.subst` for `Term.subst` or `Formula.subst`, respectively. This
pushes substitutions directly into the arguments of `D` without unfolding its body. If a
substitution needs the body of a term definition, it can use a registered equation or open the
definition. A definition whose result is a raw code with slots, written without result binders,
uses unfolding and registered equations.

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

A rule is a proof reference: a name, a name applied to arguments `h a₁ … aₘ`, the same in
parentheses `(h a₁ … aₘ)`, or a splice `${e}` holding any PRA proof expression. The
parentheses are optional in a tactic. The instantiation list `[t₁, ...]` follows a reference
without a space, so it attaches to a name, a parenthesized reference, or a splice: `h[x]`,
`(thm a b)[x]`, `${e}[x]`. Each argument is read by the declared type of the parameter it
fills, exactly as for a definition: the first-order reading for a term or formula parameter,
and the PRA reading for any other parameter. The parameters of a theorem are its declaration
parameters followed by the universal quantifiers at the front of its statement. A local PRA
hypothesis applied to arguments, such as `h n`, takes PRA arguments.
Names in a proof reference resolve like PRA names, through the current namespace and the open
scopes: an axiom is the theorem `T.ax` that the theory declaration proved, so it is written
`T.ax`, or `ax` inside `namespace T` or after `open T`. A theorem of a parent theory is used the
same way; its proof is carried to the goal's theory.

A proof whose statement has PRA antecedents, such as the restriction of an axiom schema, can be
applied to proofs of them as further arguments. Each antecedent that is left out is discharged
from a local PRA hypothesis that states it or by calculation: for an equation `test = 1`, a
hypothesis `a = b` proves the test `eqb a b`, a conjunction `band a b` needs both parts, a
disjunction `bor a b` needs one part, and a test that calculates to `1` is closed. Otherwise the
tactic reports the required equation.

| Tactic | Action |
| --- | --- |
| `pintro x₁ x₂ ...` | Introduce object universal variables (shifting assumptions in `Γ` and binding `xᵢ` at index `0`) or move implication premises into `Γ`. |
| `passumption` | Close the goal using a matching object assumption (or an implication premise in the goal). |
| `pexact h[t₁, ...]` | Close the goal with an assumption, axiom, or theorem `h` instantiated at `t₁, ...`. |
| `pexact ax a₁ … aₘ`, `pexact (ax a₁ … aₘ)[t₁, ...]` | Instantiate the parameters of an axiom schema or a theorem `ax`, and its leading quantifiers at `t₁, ...`, and close the goal. |
| `pexact ax a₁ … aₘ h` | Also supply a PRA proof `h` of a PRA antecedent of `ax`, such as the restriction of a schema. |
| `pexact ${e}[t₁, ...]` | Close the goal with any PRA proof expression `e` instantiated at `t₁, ...`. |
| `papply e[t₁, ...]` | Apply `e` (instantiated at `t₁, ...`) backward, projecting through conjunctions if needed and leaving premises as subgoals. |
| `papply thm a₁ … aₘ`, `papply (thm a₁ … aₘ)[t₁, ...]` | Apply the theorem `thm` to its parameters, which may be formulas or terms, calculate the resulting formula, and apply it backward. |
| `pcases e[t₁, ...] with pat` | Eliminate `e[t₁, ...]` and name its components using a pattern. |
| `pconstructor` | Split a conjunction (`A ∧ B`) or equivalence (`A ↔ B`) goal into two subgoals. |
| `pleft`, `pright` | Reduce a disjunction goal `A ∨ B` to `A` or `B`. |
| `pexists t` | Provide the object term `t` as a witness for an existential goal `∃ x, A`. |
| `phave h : A` | Open a subgoal to prove `A`, then add `h : A` to the local assumptions of the main goal. |
| `pexfalso` | Replace the current object goal with `⊥`. |
| `pcontradiction` | When the goal is `⊥`, close it by modus ponens among local assumptions; otherwise replace the goal `A` with `¬¬ A`. |

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
| `prw [r₁, r₂, ...]` | On an equality goal, close it by rewriting both sides with the equations `rᵢ` and comparing the results. On any other goal, rewrite the goal with each rule in turn: an equation rewrites the terms it matches, an equivalence `A ↔ B` rewrites the subformulas it matches. `← r` uses a rule from right to left. |
| `prw [r₁, r₂, ...] at h` | Rewrite the local assumption `h` with each rule in turn, as on a goal that is not an equation. `h` keeps its name and its place among the assumptions, and a rule may use any assumption, including ones introduced after `h`. |
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

In `prw [r₁, r₂, ...]`, each rule `rᵢ` is a proof reference to an equation or an equivalence,
possibly universally quantified, from the theory, local assumptions, or PRA environment. On an
equality goal, universal variables in a rule are matched against subterms from the inside out,
earlier rules normalize later rules in the list, and both sides of the target equation are
rewritten to a common term. On any other goal, each rule rewrites once, in the order written:
an equation replaces every occurrence of the first term it matches, inside relations, equations,
implications, and quantifiers, and an equivalence replaces every subformula it matches, under
implications, the derived connectives, and quantifiers. A term in the arguments of a definition
that stays closed is rewritten in place, and the definition stays closed. `psubst` replaces an
object variable by a term throughout the goal in one step.

### Opening definitions in proofs

Formula definitions, and term definitions whose result is not a raw code with slots, stay
closed in proof goals until a tactic needs to inspect their body. A goal therefore keeps the
names it was written with, and the goal display shows the same code the tactics hold:

- Connective-directed tactics (`pintro`, `pconstructor`, `pleft`, `pright`, `pexists`, `pcases`,
  `papply`, `ptrans`, `psymm`, and `pcongr`) open definitions at the head of the formula they
  inspect while keeping inner definitions closed.
- Matching tactics (`passumption`, `pexact`, and `papply`) reconcile formulas that agree after
  opening definitions, unfolding only at the positions where the two formulas differ.
- `prw [D]` explicitly unfolds `D` in the goal, and `prw [D] at h` unfolds `D` in the local
  assumption `h`.

A proof that needs the body of a definition opens it with `prw [D]`. When a tactic fails with
definitions closed, it runs again with every definition opened, and that run is kept only when it
closes the goal without leaving new goals. For example, `prw [h]` closes an equation whose sides
agree only once a definition is opened, and no opened goal is shown. Setting
`set_option fol.openDefinitions true` opens all definitions eagerly in every step.

## Induction

### First-order induction (`pinduction`)

`pinduction` applies the theorem of an induction axiom schema declared in the active theory or
in one of its parent theories:

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
- `using thm` names the theorem of the schema and is optional when the theory has a single
  induction schema.
- `(assuming := h)` supplies a PRA proof of the schema's restriction for the motive. Without it,
  the restriction is discharged like any PRA antecedent: from a local PRA hypothesis or by
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
