# PRA specifications and object files

## File names and build outputs

Specifications use `.pra` and object files use `.prao`, where `o` stands for an object file. Paths
follow Lean's module hierarchy: for example, `PRAProver.Library.Nat.Defs` produces
`PRAProver/Library/Nat/Defs.pra` and `PRAProver/Library/Nat/Defs.prao` under the output directory.
Primitive operations appear directly in expressions.

Other proof systems use similar pairs: [Metamath Zero](https://github.com/digama0/mm0) pairs `.mm0`
specifications with `.mmb` binary proofs and `.mmu` text proofs, and
[Rocq](https://docs.rocq-prover.org/master/refman/practical-tools/coq-commands.html) compiles `.v`
sources into `.vo` object files. PRA pairs readable `.pra` specifications with `.prao` object files
for its own core syntax and typing rules.

Lake's module `pra` facet writes each module's `.pra` and `.prao` pair. The library `pra` facet
collects modules in import order, writes `modules.txt`, and deletes stale `.pra` and `.prao` files.
Modules without PRA declarations produce no pair. Lake writes `.pra-export` build markers under
`.lake/build/ir/` for its own up-to-date tracking; the checker reads only `modules.txt` and the
`.pra` and `.prao` files.

## Readable specifications (`.pra`)

A `.pra` file is a sequence of semicolon-terminated `def` and `theorem` declarations:

```text
def identity (x : Nat) : Nat := x;

theorem reflexive (x : Nat) : (Eq x x);
```

A `def` declaration gives its parameters, return type, and body after `:=`. The final return token
selects the declaration kind: `Nat` declares a function, and `QFProp` or `Prop` declares a
predicate. Types with `k` numerical arguments are written `Nat -> ... -> RESULT` with `k`
occurrences of `Nat ->`. A `theorem` declaration gives its parameters and statement. Parentheses
`(x : T)` mark explicit binders and braces `{x : T}` mark implicit binders; binder visibility is
recorded in the syntax tree, while all arguments are written explicitly at use sites.

The `.pra` syntax is self-contained and uses the fixed core operations directly. Every declaration
is parsed into a core constructor tree and compared for exact equality with the `.prao` declaration
after dropping the theorem proof field. Names, parameter lists, binder visibility, definition
bodies, and theorem statements must match.

### Expressions

Application `(f x y)` is written in parentheses and associates to the left, so `(f x y)` parses as
`((f x) y)`. Parentheses also enclose lambdas, `let` expressions, and applications of primitive
operations. Each lambda binds one `Nat` variable. Term expressions have these forms:

```text
0                              -- zero
succ                           -- successor function
(f x y)                        -- numerical application
(fun (x : Nat) => BODY)         -- numerical lambda
(let f := VALUE; BODY)          -- local term binding (number or function)
(primrec BASE STEP)             -- unary primitive-recursion function
((primrec BASE STEP) ARGUMENT)  -- its numerical application
@Definition[FUNCTION_ACTUALS]   -- function definition reference
```

Predicate expressions use predicate parameters, numerical application `(P x y)`, numerical lambdas
`(fun (x : Nat) => BODY)` or `(fun {x : Nat} => BODY)`, and these forms:

```text
True                    False
(Eq LEFT RIGHT)         (Imp LEFT RIGHT)
(And LEFT RIGHT)        (Or LEFT RIGHT)
(Forall PREDICATE)      (Exists PREDICATE)
@Predicate[FUNCTION_ACTUALS][PREDICATE_ACTUALS]
(check_term NAME := VALUE; BODY)
(check_predicate NAME := VALUE; BODY)
```

Actual-argument lists in brackets are comma-separated. Trailing empty bracket lists may be omitted:
`@P` has no schema arguments, and `@P[][Q]` passes no function arguments and one predicate argument
`Q`. `Forall` and `Exists` take a unary predicate, such as a unary predicate parameter, a unary
predicate definition, or `(fun (x : Nat) => BODY)`.

`check_term` and `check_predicate` represent core `Predicate.letTerm` and `Predicate.letPredicate`
nodes. When Surface elaborates a local term or predicate inside a predicate, it substitutes the
definition into `BODY` and wraps the result in `letTerm` or `letPredicate` so the kernel still
type-checks `VALUE`. In `.pra` syntax, `NAME` records the binder annotation from that wrapper
without introducing a variable in `BODY`. By contrast, `(let f := VALUE; BODY)` in a term binds `f`
as de Bruijn index `0` inside `BODY`.

### Names and variable resolution

Global references start with `@` followed by a dot-separated structural name. Components that are
ordinary ASCII identifiers (`[A-Za-z_][A-Za-z0-9_']*`) and are not reserved keywords are printed
bare; other string components are printed as JSON-escaped UTF-8 strings in double quotes. Numeric
name components are written `#N`, distinguishing `A.#1` from `A."1"`. The anonymous name is `_`,
whereas `"_"` is a one-character string component.

Local variables and declaration parameters are written by name when their name is non-anonymous,
appears once in its binder list, and is not shadowed by an inner binder or another parameter list.
The parser resolves bare term names in `locals` from innermost to outermost binder and then in
`functions` in declaration order; bare predicate names resolve in `predicates` in declaration
order. When a binder name is `_`, duplicated, or shadowed, the printer writes `local[N]`,
`fnarg[N]`, or `predarg[N]`, where `local[0]` is the innermost numerical binder and `fnarg[N]` and
`predarg[N]` index the function and predicate parameter lists from `0`.

Whitespace and `--` comments (to the end of the line) are ignored between tokens. Declarations may
span multiple lines or share a line. Each declaration ends at a `;` token outside `(...)`, `[...]`,
`{...}`, comments, and string literals.

## Object declarations

Each `.prao` file stores a module's declarations in admission order. In tree notation, the three
top-level declaration forms are:

```text
(function NAME PARAMETERS ARITY BODY)
(predicate NAME PARAMETERS (sig ARITY SORT) BODY)
(theorem NAME PARAMETERS STATEMENT PROOF)
```

Here `SORT` is `qf` or `prop`. A structural name is `(name COMPONENT...)` with string and natural
number components. Each entry in `PARAMETERS` is `(funparam BINDER ARITY)` or
`(predparam BINDER (sig ARITY SORT))`, where `BINDER` is `(binder NAME IMPLICIT)` and `IMPLICIT` is
`0` (explicit) or `1` (implicit). The kernel checks constructor tags, categories, and field counts
with `shape` before type-checking. A `.pra` declaration produces the same tree as its `.prao`
counterpart except that a `.pra` theorem has the three fields `NAME`, `PARAMETERS`, and `STATEMENT`.

All remaining term, predicate, and proof constructors match
[`PRAProver/Core/Syntax.lean`](../PRAProver/Core/Syntax.lean). Their wire tags are listed in `TAGS`
in [`src/syntax.rs`](src/syntax.rs) and checked in [`src/kernel.rs`](src/kernel.rs).

`modules.txt` lists each module once in dependency order. Each dot-separated component of a module
name must be non-empty and free of path separators (`/`, `\`, `:`). For each module in
`modules.txt`, the checker opens `<module>.pra` and `<module>.prao` and reads declarations in
lockstep until both files end, starting from an empty environment. Global references may refer
only to declarations admitted earlier.

## Binary encoding (`.prao`)

A `.prao` file begins with the 4-byte ASCII header `PRAO`, followed by one length-prefixed frame per
declaration. Unsigned integers (frame lengths, list lengths, string byte lengths, and `N` nodes) use
unsigned LEB128 encoding: each byte holds 7 bits from least significant to most significant, with
bit 7 set on all bytes except the last. Encodings must be canonical (no trailing zero byte on a
multi-byte integer) and fit in `u64`.

Inside a frame, each syntax node starts with a 1-byte tag:

- `0`: `X::L`, followed by the element count (LEB128) and that many encoded child nodes.
- `1`: `X::S`, followed by the byte length (LEB128) and valid UTF-8 bytes.
- `2`: `X::N`, followed by a `u64` value (LEB128).
- `16 + i`: `X::A(i)`, the atom at index `i` in `TAGS`.

A constructor node `(tag field_1 ... field_k)` is encoded as an `X::L` list whose first element is
the atom `tag` and whose remaining elements are `field_1` through `field_k`. Each frame encodes one
complete declaration tree and must end at the exact byte length given by its frame header.
