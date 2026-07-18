# Building

Requires Lean 4 (the toolchain pinned in `lean-toolchain`, installed via
[elan](https://github.com/leanprover/elan)). All dependencies resolve from git;
see `lakefile.lean`.

## First-time setup

```bash
lake update            # resolve the git dependencies + write lake-manifest.json
lake exe cache get     # fetch prebuilt mathlib oleans (skip and mathlib builds from source)
```

## Build the compiler

```bash
lake build
```

The module set is large and the full build is **memory-intensive**. On a
constrained machine, cap the workers and let it resume incrementally:

```bash
taskset -c 0-1 lake build     # ~one Lean worker per core at ~3 GB; re-run to resume
```

## Reproduce the axiom ledger

```bash
lake env lean AxiomAudit.lean     # prints the axioms each end-to-end capstone depends on
```

## Generate the API documentation (docgen4)

```bash
lake -R -Kenv=doc update
lake -R -Kenv=doc build CatCryptCompiler:docs     # output under .lake/build/doc/
```

See [DOCS.md](DOCS.md) for the leanblueprint and Verso documentation options.
