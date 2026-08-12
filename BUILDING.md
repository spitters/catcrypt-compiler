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

The module set is large and the full build is **memory-intensive**. Peak memory
scales with the number of concurrent Lean workers, and `LEAN_NUM_THREADS` is the
knob that bounds them: it sizes the Lean task pool that lake schedules build jobs
onto, and, being an environment variable, is inherited by each worker process, so
it caps worker count and per-process threads together. On a constrained machine
set it low and re-run to resume incrementally:

```bash
LEAN_NUM_THREADS=2 lake build     # ~7-8 concurrent workers; re-run to resume
LEAN_NUM_THREADS=1 lake build     # ~3 concurrent workers, the smallest footprint
```

Unset, lake sizes the pool from the online CPU count (16 workers on a 16-core
box). `taskset` is CPU affinity only and does not cap workers: `taskset -c 0-1
lake build` still starts the full set, time-sharing two cores — the memory cost
without the parallelism. Lake has no `-j`/`--jobs` flag and `LAKE_JOBS` has no
effect. To attribute an out-of-memory kill to a declaration, cap a single file's
process with `lake env lean -M <MB> <file.lean>`, which reports excessive memory
consumption at a source position instead of dying with a signal.

## Run the checks

The gates in `scripts/` are what keeps the package's claims from drifting. All of
these are static — no toolchain, seconds to run — and CI runs each as its own
step:

```bash
bash scripts/check-doc-links.sh              # every relative Markdown file link resolves
bash scripts/rot-guard-build.sh --check      # every compiler module is reached by a build root
bash scripts/handcom-provenance-ratchet.sh   # no new hand-authored Com/Lcmd emit kernel
bash scripts/audit_emit_provenance.sh        # no new untagged hand-written JInstr block
bash scripts/vacuous-theorem-ratchet.sh      # no new vacuous or assumption-shaped security theorem
bash scripts/uc-plumbing-ratchet.sh          # no new plumbing-tagged security statement
bash scripts/proof-cost-ratchet.sh           # no new native_decide or maxHeartbeats bump
bash scripts/lint-lean-prose.sh --docs       # the authority documents state what is, not what changed
```

Each ratchet compares against a baseline in `scripts/` and fails when its count
rises. When a count falls the baseline is rewritten downward; commit the tightened
file, which is what the final CI step checks.

The proof-cost baselines start high — 3450 `native_decide` occurrences over 617
modules, and 122 `maxHeartbeats` bumps above the default — and they are an open
target rather than a settled state. Each `native_decide` runs a computation
inside the build and adds the `ofReduceBool` compiler-trust axiom to what depends
on it; each raised heartbeat budget carries a slow proof. Replacing one with a
structural proof, or moving a test out to a harness, lowers the count and the
ratchet records it.

`scripts/rot-guard-build.sh --build` builds every module in
`scripts/rot-guard/build-roots.txt` as its own target, in batches, so a failure
names the modules it was building rather than dying anonymously partway through a
single job.

Two checks need a build:

```bash
# Per-file `sorry` ratchet, read from the compiler's own hasSorry diagnostic.
bash scripts/sorry-gate.sh --reset
bash scripts/sorry-gate.sh run lake build
bash scripts/sorry-gate.sh --init            # first time only; review and commit the baseline
bash scripts/sorry-gate.sh check             # thereafter

# Per-module elaboration cost.
bash scripts/build-cost-ratchet.sh record CatCrypt/path/To/Module.lean
bash scripts/build-cost-ratchet.sh check
```

To run the cheap ones before every commit:

```bash
git config core.hooksPath .githooks
```

## Reproduce the axiom ledger

```bash
lake env lean AxiomAudit.lean     # prints the axioms each end-to-end capstone depends on
```

## Generate the documentation

API reference (docgen4):

```bash
lake -R -Kenv=doc update
lake -R -Kenv=doc build CatCryptCompiler:docs     # output under .lake/build/doc/
```

Manual (Verso) — the narrative documentation in `docs/`, a package separate from the
compiler library so verso is not a transitive dependency:

```bash
cd docs
lake update                                    # resolve verso + write docs/lake-manifest.json
lake build CompilerManual
lake exe compiler-manual --output _out         # open docs/_out/html-single/index.html
```

Proof blueprint (leanblueprint) — `blueprint/src/content.tex` is the theorem-dependency
outline: each informal statement with the `\lean{...}` name of the formal theorem it
maps to. It is the source text only — the leanblueprint scaffolding (`src/print.tex`,
`src/web.tex`, `src/plastex.cfg`, `src/macros/`, the `lean_decls` wiring) is not
committed, so `leanblueprint pdf` / `leanblueprint web` do not yet run from a fresh
clone.
