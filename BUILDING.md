# Building

Requires Lean 4 (the toolchain pinned in `lean-toolchain`, installed via
[elan](https://github.com/leanprover/elan)) and git. Every dependency resolves from a
public git repository; `lakefile.lean` lists them with their pins.

## The Veir dependency

`lakefile.lean` requires `Veir` from the public repository
`https://github.com/spitters/veir-catcrypt` at tag `v4.33.1-catcrypt.1`. That
repository is a fork of [VeIR](https://github.com/opencompl/veir): VeIR `v4.29.0`
with the CatCrypt opcode dialects and the toolchain updates to the Lean version this
package uses, under VeIR's Apache-2.0 licence. Lake clones it over https together with
the other dependencies, and no credentials are needed.

## What a build consists of

The default target (`lake build`) builds the 2390 modules that `lakefile.lean` names
(`grep -c 'Lake.Glob.one' lakefile.lean`). mathlib and the packages it requires come
prebuilt from mathlib's cache; the other dependencies build from source. A single
example needs only its import closure: `lake build <module>` builds that closure and
nothing else, and [GETTING_STARTED.md](GETTING_STARTED.md) starts that way. Peak memory grows with the
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

## Run the checks

The gates in `scripts/` compare the package's sources with recorded baselines. They
read the sources and need no build, and CI runs each as its own step:

```bash
bash scripts/check-doc-links.sh              # every relative Markdown file link resolves
bash scripts/gen-module-globs.sh --check     # the module list in lakefile.lean is current
bash scripts/rot-guard-build.sh --check      # every compiler module is reached by a build root
bash scripts/handcom-provenance-ratchet.sh   # no new hand-authored Com/Lcmd emit kernel
bash scripts/front-callsite-ratchet.sh       # no new direct rolled-loop combinator call site
bash scripts/audit_emit_provenance.sh        # no new untagged hand-written JInstr block
bash scripts/vacuous-theorem-ratchet.sh      # no new vacuous or assumption-shaped security theorem
bash scripts/uc-plumbing-ratchet.sh          # no new plumbing-tagged security statement
bash scripts/proof-cost-ratchet.sh           # no new native_decide or maxHeartbeats bump
bash scripts/lint-lean-prose.sh --docs       # the listed documents contain no banned phrasing
```

Each ratchet compares against a baseline in `scripts/` and fails when its count
rises. When a count falls the ratchet rewrites the baseline downward; commit the
tightened file, which is what the final CI step checks.

Line 1 of `scripts/native-decide-baseline.txt` is the number of `native_decide`
occurrences under `CatCrypt/` outside comments, and each further line gives a count
and a file; line 1 of `scripts/maxheartbeats-baseline.txt` is the number of
`set_option maxHeartbeats` bumps above the default 200000
(`head -1 scripts/native-decide-baseline.txt scripts/maxheartbeats-baseline.txt`).
At this commit the counts are 2120 `native_decide` occurrences in 477 files and 78
bumps. Each `native_decide` runs a computation inside the build and adds a
compiler-trust axiom to the theorems that depend on it; each raised heartbeat budget
carries a slow proof. Replacing one with a structural proof, or moving a test to a
harness, lowers the count and the ratchet records it.

`scripts/rot-guard-build.sh --build` builds every module in
`scripts/rot-guard/build-roots.txt` as its own target, in batches, so a failure
names the modules it was building.

Two checks read a build:

```bash
# `sorry` in a build that stopped early.
bash scripts/sorry-gate.sh --reset
bash scripts/sorry-gate.sh run bash scripts/rot-guard-build.sh --build
bash scripts/sorry-gate.sh --init            # writes scripts/sorry-baseline.txt, which the package does not ship
bash scripts/sorry-gate.sh check

# Per-module elaboration cost.
bash scripts/build-cost-ratchet.sh record CatCrypt/path/To/Module.lean
bash scripts/build-cost-ratchet.sh check
```

A complete `lake build` refuses every declaration whose proof reaches `sorryAx`:
`lakefile.lean` passes `-E hasSorry`, which reports Lean's `hasSorry` message as an
error. `scripts/sorry-gate.sh` covers a build that stops early: it reads the log of
the modules that build reached and compares per-file counts with a baseline file,
`scripts/sorry-baseline.txt`, which `scripts/sorry-gate.sh --init` writes. The
package ships no baseline, so `scripts/sorry-gate.sh check` fails until one is
written. Under `-E hasSorry` the only baseline consistent with a complete build
allows no such declaration.

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
memory overrun or a timeout, after a static lint for proof-cost patterns: a
`native_decide` in a reflection or emit-front module (whose import native-compiles
the pipeline), or a `maxRecDepth`/`maxHeartbeats` budget newly placed on a proof.

```bash
BUILD_COST_STATIC_ONLY=1 bash scripts/check-build-cost.sh   # lint only; the pre-commit hook runs this
bash scripts/check-build-cost.sh --record                   # build and record the per-module cost row
```

`BUILD_COST_TIMEOUT`, `BUILD_COST_MEM_MB`, `BUILD_COST_CORES`, and `FRONT_RE`
(the reflection/emit-front module regex) tune it.

A few modules cost more than a development box has. `scripts/ci-only-modules.txt`
records them, each line carrying the measurement that earned it: the peak resident
memory of one `lean` process, or the `anon-rss` of the kernel's out-of-memory record
when the process was killed before finishing. `check-build-cost.sh` reports a listed
module instead of elaborating it, and fails on a line whose source file is gone.
Lake reads nothing there, so a build that imports one of these still pays the cost —
the list says where the cost is and keeps the gate from reproducing the kill. Add a
line only with a figure behind it.

The entries are the part checks of `ed25519_point_add`, `ed25519_sc_reduce` and
`ed25519_sc_muladd`: `decide +kernel` over a symbolic run of a whole part, one of which
alone reaches 4.84 GB. Splitting them into a module per check was measured and does not
divide the cost, which is one declaration's reduction rather than an accumulation
across a module; cutting a part into shorter runs at a boundary certificate does.

A module that does not build locally still has to stay true. The part checks are
statements about imported blocks, and a re-import can make one false with no build
reporting it, since nothing elaborates the modules that hold them.
`scripts/ed25519-part-check-gate.sh` evaluates all twenty-seven statements with the
compiled evaluator, from the symbolic executor (`Ed25519SymExec`), the models and the
part maps alone, and fails if any is false:

```bash
bash scripts/ed25519-part-check-gate.sh
```

CI runs it before the full build, so it reports even when the run ends before the build
reaches the checks. It adds no trust; the kernel proofs remain the artefact.

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
file, and run it the same way. A theorem whose proof closure uses `native_decide`
lists an additional axiom for it. The number of `axiom` declarations in the package,
with the command that counts them, is in [README.md](README.md#limitations).

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
