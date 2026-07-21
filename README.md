# catcrypt-compiler

A verified compiler for cryptography, built inside the Lean 4 proof assistant. A
crypto implementation has three parts: **orchestration** (the protocol and control
spine), **algebra** (field, curve, and polynomial mathematics), and **leaves**
(low-level hand-tuned primitives). CatCrypt gives each part a verified source,
lowers them through typed MLIR-style dialects, and emits constant-time x86-64,
AArch64, and RISC-V as machine bytes inside Lean. A machine-checked proof shows each
emitted kernel denotes its source specification. The correctness proof is over the
compiler, not per primitive, so a new primitive is a recompilation.

> 🚧 **Under construction — experimental research prototype.** The interfaces, the
> covered source fragment, and the emitted surface are evolving; expect breaking
> changes. This is not a production tool.

## The three aspects

- **Orchestration** — Rust, extracted through hax. The extraction eliminates traits,
  generics, closures, and heap references, each step proved correct, and hands the
  covered control spine to the dialect stack.
- **Algebra** — prime-ir. The field, modular-arithmetic, elliptic-curve, and
  polynomial/NTT dialects are the verified analogs of
  [PrimeIR](https://github.com/fractalyze/prime-ir)'s MLIR dialects for cryptography
  — the algebraic tier that structures the compiler over a Jasmin-like substrate. A
  companion Rust library exposes these operations, and a kernel that uses them
  compiles to the matching dialect operation.
- **Leaves** — Jasmin. The word-level Jasmin dialect is the compiler's MLIR
  substrate, and the compiler both compiles to it and imports from it (below).

## The dialect stack, and a two-way verified relationship with Jasmin

The source lowers through typed dialects — an SSA intermediate representation, the
prime-ir algebraic dialects, and the word-level Jasmin dialect — down to an owned
backend that encodes instructions to bytes for x86-64, AArch64, and RISC-V. Every
dialect carries a Lean denotation, and every lowering is a Lean function proved to
preserve it, so a well-typed term denotes its specification by construction. The IR
structure follows [lean-mlir](https://github.com/opencompl/lean-mlir) (via the Veir
library); code generation is CatCrypt's own backend.

The compiler both compiles *to* [Jasmin](https://github.com/jasmin-lang/jasmin) and
imports *from* it, both inside Lean. The algebraic dialects lower to the Jasmin
dialect, which reaches x86 by either the owned bytes-direct encoder or Jasmin's own
verified compiler, reached by printing Jasmin text; and hand-written Jasmin leaves
are imported through the same backend. The external `jasminc` tool is a differential
byte oracle. [PROVENANCE.md](PROVENANCE.md) records the low-level-IR
lineage: AUCurves, bedrock2, Rupicola.

## The guarantee — three obligations

The pipeline preserves three properties from source to emitted bytes.

- **Functional correctness** — the emitted kernel denotes the source specification.
  For the lattice NTT, the compiled code equals the source polynomial multiply. The
  Rust-front result reaches the tracked output over the machine-word semantics and
  covers data-dependent loops.
- **Constant-time** — preserved over the full modern constructor set, including
  data-dependent loops: a loop is constant-time exactly when its guard is public,
  and the analyzer accepts a public-count loop and rejects a secret-dependent one.
- **Security** — proven in the computational model, with hax as the proof anchor.
  Carrying that bound onto the emitted bytes — byte-level transfer — holds for the
  symmetric family and is a roadmap goal for the asymmetric families. Transfer is
  where hax's two roles, compiler frontend and proof entrance, meet: a goal beyond
  the compiler's correctness.

`lake env lean AxiomAudit.lean` prints the axiom ledger of the machine-checked
theorems.

## What this repository contains

The compiler: the two fronts, the dialect stack, the equality-saturation optimizer,
the owned x86-64 / AArch64 / RISC-V backend, and the correctness theorems. The
primitives compiled through it — NIST post-quantum signatures, ML-KEM and ML-DSA,
classical AEAD, hash, and elliptic-curve primitives, and a STARK prover — and their
security chains live in the wider CatCrypt development; this package is the engine
they run through. The [CatCrypt paper](CITATION.cff) describes the full system.

## Source coverage — the language of constant-time crypto

The covered source is the prime-ir algebra and the control spine that cryptography
is written in. It covers straight-line leaf calls, counted and public-condition
loops, branchless select, public-index array access, tuples, byte slices, and
fixed-width and widening integer arithmetic, over the prime-ir algebraic operations;
data-dependent loops are covered too. AES and carry-less-multiply intrinsics enter
through an explicit-SIMD vector front with verified semantics. The language
expresses both constant-time and variable-time kernels: a public-input variable-time
path such as RSA verification is accepted, and a secret-dependent one is rejected.
The relational front compiles Lean specifications directly.

## Trusted base

`AxiomAudit.lean` prints the per-theorem axiom set, checked in CI against a
baseline. The trusted base comprises the cryptographic-hardness assumptions the
protocols rest on; the per-architecture machine model, which for
RISC-V is proved equal to the official Sail specification on the emitted scalar
subset; the cited Jasmin constant-time-preservation theorem; and the fidelity of hax
extraction. The byte-level instruction facts — the decode/encode round-trip and the
arithmetic-carry instructions — are proved theorems, and the owned backend carries
no `jasminc` assumption.

The leaves are verified: symmetric primitives by owned emit in Lean, and arithmetic
and curve leaves by AUCurves and fiat-crypto, carried as cross-prover results. Two
residuals remain: the advanced-pairing mathematics, which mirrors upstream
assumptions and lies outside the compiler-correctness proof, and the byte-level
security transfer for the asymmetric families.

## Build, dependencies, documentation

See [BUILDING.md](BUILDING.md). Dependencies resolve from git:
[`catcryptCore`](https://github.com/spitters/CatCrypt-core) (the CatCrypt
methodology library), `Veir`,
[`paramTransfer`](https://github.com/spitters/ParamTransfer) (the proof-transfer
bridge), `CompPoly`, [`hax-lean`](https://github.com/spitters/hax-lean) (the
typed hax front), `mathlib`. Generating the API reference and the proof blueprint
is covered in [BUILDING.md](BUILDING.md) as well.

## Status and license

Pre-release research prototype (`CHANGELOG.md`) — not a production tool. MIT
(`LICENSE`); please cite the CatCrypt paper (`CITATION.cff`).
