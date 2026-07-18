# catcrypt-compiler

A verified compiler for cryptography, built inside the Lean 4 proof assistant. It
takes a high-level source — hax-extracted Rust, or a relational specification
written in Lean — and emits constant-time machine code as encoded bytes, with a
machine-checked proof that the bytes compute the source specification.

> 🚧 **Under construction — experimental research prototype.** This is an
> experiment in what a *verified* compiler for cryptography, from a high-level
> source to constant-time assembly inside Lean, could look like. It is not a
> production tool; interfaces, the covered source fragment, and the emitted
> surface are still evolving, and breaking changes are expected.

The design follows MLIR. The source lowers through a stack of typed dialects — an
SSA `Com` intermediate representation, per-family crypto dialects that mirror the
prime-IR MLIR op families (field, modular and Montgomery arithmetic, elliptic
curves, polynomial and NTT coefficient forms, pairing), a word-level Jasmin
dialect, and progressive verified rewriting — down to an owned backend that
encodes instructions to bytes for x86-64, AArch64, and RISC-V. Every dialect
carries a Lean denotation and every lowering is a Lean function proved to preserve
it, so a well-typed term denotes its specification by construction.

## The guarantee

One source-to-assembly theorem governs the pipeline. The emitted bytes denote the
source specification (functional correctness), run in constant time, and preserve
the source protocol's security under target-level attackers. A single
denotation-preserving encoding relation drives three uses at once: the
equality-saturation optimizer, the relational compiler, and the transport that
carries a protocol's security bound down to the emitted code.

The end-to-end results are `rustToJasminCom_endToEnd`,
`robustCompilation_source_to_x86`, and `compile_correct_all`. Run
`lake env lean AxiomAudit.lean` to print their axiom ledger.

## What this repository contains

The compiler itself: the two fronts, the dialect stack, the equality-saturation
optimizer, the owned x86-64 / AArch64 / RISC-V backend, and the correctness
theorems — 1851 Lean modules. The primitives compiled through it (the NIST
post-quantum signatures, ML-KEM and ML-DSA, the classical AEAD, hash, and
elliptic-curve primitives, a STARK prover) and their end-to-end security chains
live in the wider CatCrypt development; this package is the engine they run
through. The CatCrypt paper (`CITATION.cff`) describes the full system.

## Source coverage

The hax front compiles a structured fragment of extracted Rust — A-normal form
with structured control flow (`IsCoveredCtl`) — and covers more as the front
grows. The relational front compiles Lean specifications directly.

## Trusted base

The backend is checked against a per-architecture machine model; for RISC-V, that
model is proved equal to the official Sail specification on the emitted scalar
subset. A security claim additionally rests on the protocol's cryptographic-
hardness assumption. The byte-level instruction facts (`decode ∘ encode`,
ADCX/ADOX/MULX) are proved. One `native_decide` reflection axiom discharges an AES
S-box array-size check; `AxiomAudit.lean` reproduces the full ledger.

## Build, dependencies, documentation

See [BUILDING.md](BUILDING.md). Dependencies resolve from git:
[`catcryptCore`](https://github.com/spitters/CatCrypt-core) (the CatCrypt
methodology library), `Veir`,
[`paramTransfer`](https://github.com/spitters/ParamTransfer) (the proof-transfer
bridge), `CompPoly`, [`hax-lean`](https://github.com/spitters/hax-lean) (the
typed hax front), `mathlib`. [DOCS.md](DOCS.md) covers the generated API
reference and the blueprint.

## Status and license

Pre-release research prototype (`CHANGELOG.md`) — not a production tool. MIT
(`LICENSE`); please cite the CatCrypt paper (`CITATION.cff`).
