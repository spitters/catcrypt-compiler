# Building

Requires Lean 4 (the toolchain pinned in `lean-toolchain`, installed via
[elan](https://github.com/leanprover/elan)) and git. Every dependency resolves from a
public git repository; `lakefile.lean` lists them with their pins:
[`catcryptCore`](https://github.com/spitters/CatCrypt-core) (the CatCrypt methodology
library), `Veir` (below), [`paramTransfer`](https://github.com/spitters/ParamTransfer)
(the proof-transfer bridge), `CompPoly`,
[`hax-lean`](https://github.com/spitters/hax-lean) (the typed hax front) and `mathlib`.

## The Veir dependency

`lakefile.lean` requires `Veir` from the public repository
[spitters/veir-catcrypt](https://github.com/spitters/veir-catcrypt) at tag
`v4.35.0-catcrypt.1`. That repository is a fork of
[VeIR](https://github.com/opencompl/veir): upstream VeIR at commit `ae4fa0a1` with five
CatCrypt dialect folders (`Veir/Dialects/{Catcrypt,Memref,Polynomial,Vector,X86vector}`)
and the toolchain updates to the Lean version this package uses, under VeIR's
Apache-2.0 licence. Lake clones it over https together with the other dependencies,
and no credentials are needed.

## What a build consists of

`lakefile.lean` declares four libraries:

- `CatCryptCompiler`: the compiler and its theorems, including the hax compiler
  `compileA` under `CatCrypt/Crypto/SecureCompilation/Haxc/`;
- `HaxAscent`: the ascent from hax-extracted Rust to the `Corres` calculus, and the
  Rust semantics it ascends to (`HaxAscent/`);
- `CatCryptCompilerExamples`: demos, probes, tests and benchmark drivers;
- `CatCryptCompilerVeir`: the bridge to VeIR.

`CatCryptCompiler` and `HaxAscent` are the default targets of `lake build`; the other
two build on request (`lake build CatCryptCompilerExamples`,
`lake build CatCryptCompilerVeir`), and no module of `CatCryptCompiler` imports one of
theirs. mathlib and the packages it requires come prebuilt from mathlib's cache; the
other dependencies build from source. A single example needs only its import closure:
`lake build <module>` builds that closure and nothing else, and
[GETTING_STARTED.md](GETTING_STARTED.md) starts that way. Peak memory grows with the
number of concurrent Lean workers, which `LEAN_NUM_THREADS` bounds (below). The CI
build job (`.github/workflows/ci.yml`) runs at `LEAN_NUM_THREADS=1` in time-bounded
batches and carries its progress from one run to the next through the build cache.

## First-time setup

```bash
lake update            # resolve the git dependencies and write lake-manifest.json
lake exe cache get     # fetch prebuilt mathlib oleans (without it, mathlib builds from source)
```

`lake-manifest.json` is not tracked; `lake update` writes it from the pins in
`lakefile.lean` and the dependencies' own manifests.

## Build the compiler

```bash
lake build
```

Peak memory scales with the number of concurrent Lean workers, and
`LEAN_NUM_THREADS` bounds them: it sizes the Lean task pool that Lake schedules build
jobs onto, and, being an environment variable, is inherited by each worker process,
so it caps worker count and per-process threads together. On a constrained machine
set it low and re-run to resume incrementally. On a 16-core machine the pool had 16
workers unset, 7 to 8 at `LEAN_NUM_THREADS=2`, and 3 at `LEAN_NUM_THREADS=1`:

```bash
LEAN_NUM_THREADS=2 lake build     # re-run to resume
LEAN_NUM_THREADS=1 lake build     # the smallest footprint
```

`taskset` is CPU affinity only and does not cap workers: `taskset -c 0-1 lake build`
still starts the full set, time-sharing two cores. Lake has no `-j`/`--jobs` flag and
`LAKE_JOBS` has no effect.

The known-answer checks `#kat` and `#kat_kernel` carry wall-clock budgets set on a
development machine: a false check fails the build, and an overrun of the budget is a
warning by default. `CATCRYPT_KAT_STRICT=1` makes an overrun an error, as CI does, and
`CATCRYPT_KAT_MS_SCALE` multiplies every budget for a slower machine (CI sets it to 4).

## Run the hax compiler

The executable `haxc` runs `compileA` on one function of a hax frontend export, the
JSON file that `cargo hax json` writes in the Rust crate:

```bash
lake build haxc
lake exe haxc EXPORT --fn NAME [--name CRATE]
```

Without `--fn` it compiles the last extracted function. On success it prints the
x86-64 AT&T assembly on standard output and exits `0`; when `compileA` refuses the
function it prints the first refusing stage and its construct on standard error and
exits `2`. [PIPELINE.md](PIPELINE.md) lists the stages.

## Run the checks

The gates in `scripts/` compare the package's sources with recorded baselines. They
read the sources and need no build, and CI runs each as its own step:

```bash
bash scripts/check-doc-links.sh              # every relative Markdown file link resolves
bash scripts/check-doc-paths.sh              # every file path in a document code span exists
bash scripts/gen-module-globs.sh --check     # the module list in lakefile.lean is current
bash scripts/ci-only-import-gate.sh          # only a CI-only module imports a CI-only module
bash scripts/rot-guard-build.sh --check      # every compiler module is reached by a build root
bash scripts/handcom-provenance-ratchet.sh   # no new hand-authored Com/Lcmd emit kernel
bash scripts/front-callsite-ratchet.sh       # no new direct rolled-loop combinator call site
bash scripts/audit_emit_provenance.sh        # no new untagged hand-written JInstr block
bash scripts/emit-ct-obligation-ratchet.sh   # every artifact-writing module carries its CT obligation
bash scripts/vacuous-theorem-ratchet.sh      # no new vacuous or assumption-shaped security theorem
bash scripts/ascent-anchor-ratchet.sh        # no new ascent module untied to compiler output or bytes
bash scripts/ascent-nonvacuity-ratchet.sh    # no new ascent judgment without a satisfiability witness
bash scripts/dialect-lowering-ratchet.sh     # every Dialect is classified in scripts/dialect-manifest.txt
bash scripts/leak-kind-wildcard-lint.sh      # no leak-kind function maps a wildcard to the quiet class
bash scripts/proof-cost-ratchet.sh           # no rise in the recorded proof-cost counts
bash scripts/lean-kat-ratchet.sh             # known-answer checks only through #kat and #kat_kernel
bash scripts/lint-lean-prose.sh --docs       # the listed documents contain no banned phrasing
```

Each ratchet compares against a baseline in `scripts/` and fails when its count
rises. When a count falls the ratchet rewrites the baseline downward; commit the
tightened file, which is what the final CI step checks.

`scripts/rot-guard-build.sh --build` builds every module in
`scripts/rot-guard/build-roots.txt` as its own target, in batches, so a failure
names the modules it was building.

Two checks read a build:

```bash
# `sorry` in a build that ended early.
bash scripts/sorry-gate.sh --reset
bash scripts/sorry-gate.sh run bash scripts/rot-guard-build.sh --build
bash scripts/sorry-gate.sh check

# Per-module elaboration cost.
bash scripts/build-cost-ratchet.sh record CatCrypt/path/To/Module.lean
bash scripts/build-cost-ratchet.sh check
```

A complete `lake build` refuses every declaration whose proof reaches `sorryAx`:
`lakefile.lean` passes `-E hasSorry`, which reports Lean's `hasSorry` message as an
error. `scripts/sorry-gate.sh` covers a build that stops early: it reads the log of
the modules that build reached and compares per-file counts with the baseline
`scripts/sorry-baseline.txt`, which allows no such declaration.

## Import structure and rebuild fan-out

An edit to a module rebuilds the modules that import it, directly or
transitively. `scripts/import-fanout.sh` counts them from the import headers,
without a build:

```bash
bash scripts/import-fanout.sh --top 20        # modules with the largest fan-out
bash scripts/import-fanout.sh CatCrypt.Crypto.Jasmin.LowCT
bash scripts/import-fanout.sh --importers CatCrypt.Crypto.Jasmin.LowCT
```

To shrink an import set, add `#min_imports` at the end of a module (from
`Mathlib.Tactic.MinImports`); it prints the smallest import set that elaborates
the module. `lake exe graph --to <Module> graph.dot` draws the import DAG of a
slice. Narrow leaf modules first and build them one small batch at a time, with
`LEAN_NUM_THREADS=1`; a large file split into parts behind a re-exporting root
lowers fan-out only once its importers name the part they use.

Library modules use the module system (`module`, `public import`,
`@[expose]`). Proof bodies are private, so an edit inside a proof does not change
what importers see. Definition bodies are exported where a file opens with
`@[expose] public section`; a module whose definitions nothing downstream
unfolds can drop `@[expose]`, and then an edit to a definition body does not
change what importers see either.

## Diagnosing an out-of-memory kill

An out-of-memory kill ends a build with a signal and names no module. To attribute
the cost to a source position, cap a single file's elaboration:

```bash
lake env lean -M 4000 CatCrypt/path/To/Module.lean
```

`-M` bounds the process's memory in megabytes and reports excessive memory
consumption at a `file:line` instead of dying with a signal. The module's imports
must already be built.

`scripts/check-build-cost.sh` applies this over the modules changed since HEAD: it
elaborates each under the same memory cap and a wall-clock timeout and fails on a
memory overrun or a timeout, after a static lint for proof-cost patterns, such as a
`maxRecDepth`/`maxHeartbeats` budget newly placed on a proof.

```bash
BUILD_COST_STATIC_ONLY=1 bash scripts/check-build-cost.sh   # lint only; the pre-commit hook runs this
bash scripts/check-build-cost.sh --record                   # build and record the per-module cost row
```

`BUILD_COST_TIMEOUT`, `BUILD_COST_MEM_MB`, `BUILD_COST_CORES`, and `FRONT_RE`
(the reflection/emit-front module regex) tune it.

`scripts/ci-only-modules.txt` lists modules that cost more memory than a development
box has, each line carrying the measurement that earned it: the peak resident memory
of one `lean` process, or the `anon-rss` of the kernel's out-of-memory record when the
process was killed before finishing. `check-build-cost.sh` reports a listed module
instead of elaborating it, and fails on a line whose source file is gone. Lake reads
nothing there, so a build that imports a listed module still pays the cost. The list
is empty at present; a line is added only with a figure behind it.

The part checks of the imported Ed25519 blocks (`ed25519_point_add`,
`ed25519_sc_reduce`, `ed25519_sc_muladd`) are `decide +kernel` statements over a
symbolic run of each part of a block. `scripts/ed25519-part-check-gate.sh` evaluates
all twenty-seven statements with the compiled evaluator, from the symbolic executor
(`Ed25519SymExec`), the models and the part maps alone, and fails if any is false:

```bash
bash scripts/ed25519-part-check-gate.sh
```

CI runs it before the full build, so a re-import that falsifies a part check is
reported even when the run ends before the build reaches it. The gate adds no trust;
the kernel proofs are the result.

A memory cap on a cgroup whose working set is `.olean` mmaps is a pressure source,
not a bound: those mapped pages are clean and reclaimable, so a build near the cap
refaults them and reclaim keeps making progress while the machine thrashes. The
signal that a build is against the limit is sustained memory pressure rather than
free-memory headroom; lower `LEAN_NUM_THREADS` to shrink the concurrent working set.

The pre-commit hook in `.githooks/` runs a per-file subset of the static checks on
staged files (prose lint, the proof-cost lint, the build-root manifest check and the
link check). Activate it once per clone:

```bash
git config core.hooksPath .githooks
```

## Check axioms

```bash
lake env lean AxiomAudit.lean     # after the modules it imports are built
```

`AxiomAudit.lean` runs `#print axioms` on the theorems it lists and prints, for each,
the axioms that theorem depends on. To check another theorem, add an import of its
module and a `#print axioms <fully qualified name>` line, in that file or in a scratch
file, and run it the same way. A theorem depends on an axiom only if `#print axioms`
lists it.

The package's `axiom` declarations are listed by

```bash
git grep -nE '^(/--.*-/ *)?axiom [A-Za-z_][^ ]* *(:|\(|\{|\[|$)' -- 'CatCrypt/*.lean'
```

## Generate the documentation

API reference (docgen4):

```bash
lake -R -Kenv=doc update
lake -R -Kenv=doc build CatCryptCompiler:docs     # output under .lake/build/doc/
```

Manual (Verso): the narrative documentation in `docs/` is a Lake package of its own,
with its own toolchain pin (`docs/lean-toolchain`) and its own dependency, verso
(`docs/lakefile.lean`), so verso is not a dependency of the compiler library:

```bash
cd docs
lake update                                    # resolve verso and write docs/lake-manifest.json
lake build CompilerManual
lake exe compiler-manual --output _out         # open docs/_out/html-single/index.html
```

Proof blueprint: `blueprint/src/content.tex` lists the headline statements in
leanblueprint syntax, each with a `\lean{...}` reference to its formal theorem. The
package carries no leanblueprint build files (`web.tex`, `print.tex`,
`plastex.cfg`, macros), so the outline is a source document and `leanblueprint`
does not build it from a clone.
