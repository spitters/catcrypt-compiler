# Changelog

## Unreleased

Changes since `v0.1.0-alpha.2`.

- `JInstr` covers Jasmin's scalar `x86_op` set except the instructions declined for
  constant time: `inc`, `dec`, `clc`, `stc`, `xchg`, three-operand `imul`, one-operand
  `mul` and `imul`, `shld`, `shrd`, `rcl`, `rcr`, `cmovcc` and `setcc` over the sixteen
  conditions, sized `test`, `bt`, `btr` and `bts`. Register allocation, rescheduling,
  flag liveness, `Mem2Reg`, store-to-load forwarding, secret typing, the cost model, the
  encoder, the printer and the constant-time leakage state each new instruction's reads
  and writes.
- Hand-written assembly: `NasmParse` reads CryptOpt's NASM output, and
  `solinasSquare_correct` proves the CryptOpt `solinas_square` kernel against
  fiat-crypto's `sqr_correct` for `2^255 - 19` ([ASCENT.md](ASCENT.md), "Hand-written
  assembly").
- `addMod251_front_weld` relates the relational compiler's ZMod 251 addition, the
  front's compilation of `r := a + b mod 251` and the ascent's `SRenc` states.
- The dialect classification gate (`scripts/dialect-lowering-ratchet.sh`) runs in this
  package.

## 0.1.0-alpha.2 — 2026-09-13 (pre-release)

Changes since `v0.1.0-alpha.1`. The toolchain, the dependency pins, the module set
and the set of theorems have changed; the list below records the main changes.

- Lean toolchain `v4.33.1` (the release used `v4.30.0`), with mathlib, CompPoly and
  doc-gen4 at `v4.33.1` and the other dependencies pinned by commit or tag. `Veir`
  resolves from the private fork `spitters/veir-catcrypt` (the release required
  `opencompl/veir` at `v4.29.0`); [BUILDING.md](BUILDING.md) describes the access
  it needs.
- The package was resynced from the CatCrypt development and holds 2389 Lean modules
  under `CatCrypt/` (the release held 1851). The library names its modules one by one
  in `lakefile.lean`; `scripts/gen-module-globs.sh` generates the list and CI checks
  that it is fresh.
- The hax front reads the AST and evaluator of hax-lean (`HaxLean.AST`), and the
  simulation theorems for the translation from that AST to LowCT are in
  `CatCrypt/Crypto/Hax/` (for example `haxToLowCT_simulates_program`).
- The ascent (`CatCrypt/Crypto/SecureCompilation/Ascent/`, 11 modules at the release,
  100 now) proves that programs at the compiler's low levels compute Lean
  specifications; [ASCENT.md](ASCENT.md) is its guide.
- Removed theorems: the constant-time and noninterference preservation bridge built
  on `Com.all_com_ct`, which holds of every program, and definitions whose value was
  the constant `True`. [README.md](README.md#limitations) lists the three
  `True`-valued predicates that remain.
- New documentation: `GETTING_STARTED.md`, `DEMO.md`, `EXAMPLES.md`, `PROVENANCE.md`,
  `CAPABILITIES.md`, `bench.md`, and the Verso manual under `docs/`, a separate Lake
  package, so verso is not a dependency of the library. `DOCS.md` was removed.
- New module `CatCrypt/Crypto/SecureCompilation/CompilerHelloDemo.lean`: a routine
  written in Lean as a term of the scalar front's `Thir` input type, lowered by the
  front and compiled to AArch64, with the assembly printed.
- `X86Backend/_MpnFrontCheck.lean` and `X86Backend/_MpnFrontScratch.lean` were
  removed. `Dialects/ByteMemrefFrontPrototype.lean` was removed and returned with the
  resync.
- CI: a push to `master` runs the static gates only; the build job runs on a weekly
  schedule, on demand and on pull requests, and sets `LEAN_NUM_THREADS` to `1` to fit
  the runner memory.

## 0.1.0-alpha.1 — 2026-07-18 (pre-release)

Pre-release research code (SemVer pre-release; major version 0). Interfaces, the
covered source fragment, and the trust surface may change without notice — do not
depend on it as a stable API. The CatCrypt compiler as a standalone Lake package.

- Two fronts (hax/Rust → LowCT → `Com` IR) lowering to one x86/ARM/RISC-V backend,
  packaged as the import-closure of the compiler subtree (1851 modules), free of every
  scheme security proof and of the `MPC`/`Examples` protocol proofs.
- Theorems `rustToJasminCom_endToEnd`, on the `IsCoveredCtl` fragment and with the
  value equation `hAdequacy` as a hypothesis, and `robustCompilation_source_to_x86`
  and `compile_correct_all`, over the lattice dialect.
- The package declared 613 `axiom`s, counted with the command given in
  [README.md](README.md#limitations); `AxiomAudit.lean` prints the axioms of the
  theorems it lists.
- Dependencies resolve from git (`catcryptCore`, `Veir`, `paramTransfer`,
  `CompPoly`, `hax-lean`, `mathlib`); MIT licensed; `CITATION.cff` (ePrint 2026/604).

> Experimental research prototype — not a production tool.
