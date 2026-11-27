# PRA checker

This Rust package checks exported declarations of the PRA language independently of Lean. It
compares each readable specification with its object file and checks the types of every definition
and theorem proof. It depends only on the Rust standard library.

## Building exports and running the checker

Export from the repository root with the normal build command:

```sh
lake build
```

Exporting is part of the default build. It writes `.pra` specifications, `.prao` object files, and
`modules.txt` under `.lake/build/pra/`. Lake reuses existing exports and regenerates them when their
dependencies change or an output file is missing. Each module has a `pra` build facet that exports
that module's declarations, and the library `pra` facet collects the module list into
`modules.txt`.

To build the library exports explicitly, run `lake build PRAProver:pra`. To update one module and
its imports, run `lake build +PRAProver.Library.Nat.Defs:pra`. Run the library facet before
checking the directory so `modules.txt` lists the current module set.

Then run the checker on the export directory, allowing input records up to 4 GiB:

```sh
cargo run --release --manifest-path checker/Cargo.toml -- .lake/build/pra --max-record-mib 4096
```

The option applies to each specification and object record. It sets an input-size limit;
the memory used by parsing and checking can be larger. The object parser shares identical
subtrees within each record to reduce memory use. It also reuses decoded spans after comparing all
of their bytes and checking their depth. Every proof is checked with the same typing and conversion
rules at either setting.

During conversion, the checker opens the heavier definition first when both heads have
different weights. A definition's weight is one more than the highest weight of a
definition referenced in its body, or one if it has no references. When two heads have
the same weight, the checker opens both in the same step.

`lake build` exports every module containing PRA declarations in the root and Library import
closures. Modules without PRA declarations produce no files. For an exported module such as
`PRAProver.Library.Nat.Defs`, the output directory contains:

- `PRAProver/Library/Nat/Defs.pra`: a readable specification with definition bodies and theorem
  statements.
- `PRAProver/Library/Nat/Defs.prao`: an object file with those declarations and complete theorem
  proofs.
- `modules.txt`: the module names in the order the checker reads them.

File paths follow the module hierarchy, matching Lean's build directories. `modules.txt` lists
dotted module names such as `PRAProver.Library.Nat.Defs`.

## What the checker verifies

Specifications use `def` and `theorem` declarations with named binders, explicit types, and the
core term and predicate operations such as `Eq` and `Forall`. The specification parser builds the
core declaration tree from the `.pra` file and checks that it equals the `.prao` declaration after
removing the theorem proof field.

The checker starts from an empty environment, admits each declaration in order, and stores
definition bodies and theorem statements for later references. It drops each theorem proof after
checking it. Temporary caches reuse syntax validation, substitution, and node counts for shared
subtrees; they are dropped after each traversal. Substitution results are cached separately for
each binder depth. You can copy `.lake/build/pra` to another machine and run the checker without a
Lean installation.

When all modules pass, the checker prints declaration and proof-node counts and phase timings as
JSON and exits with status 0 (`proof_nodes` counts the syntax nodes in theorem proofs, including
binder and type annotations). If any module fails to parse, match, or type-check, the checker
prints an error and exits with status 1.

This checker is an independent executable implementation of the core typing and conversion rules;
the formal soundness and completeness proofs in
[`PRAProver/Metatheory/Core`](../PRAProver/Metatheory/Core) apply to the Lean core checker. Input
limits default to 256 MiB per declaration record, configurable with `--max-record-mib`. Syntax depth
is limited to 2048, and variable indices and arities to 1,000,000. Inputs that exceed a limit
are rejected.

## Source layout

- [`FORMAT.md`](FORMAT.md) describes the `.pra` grammar, `.prao` binary encoding, and naming rules.
- [`src/syntax.rs`](src/syntax.rs) defines the constructor tree representation and tag table.
- [`src/spec.rs`](src/spec.rs) parses `.pra` specifications into constructor trees.
- [`src/parser.rs`](src/parser.rs) decodes `.prao` object files into constructor trees.
- [`src/kernel.rs`](src/kernel.rs) checks constructor shapes, types, definitional equality, and
  proofs.
- [`src/check.rs`](src/check.rs) reads `modules.txt`, matches `.pra` and `.prao` records, and passes
  declarations to the kernel.
- [`src/main.rs`](src/main.rs) provides the command-line interface.

After changing the export format or checker rules, rebuild the exporter and checker and run
`lake build` to regenerate `.lake/build/pra`.
