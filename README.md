# catcrypt-compiler

A verified compiler for cryptography, built inside the Lean 4 proof assistant. A
crypto implementation has three parts: **orchestration** (the protocol and control
spine), **algebra** (field, curve, and polynomial mathematics), and **leaves**
(low-level hand-tuned primitives). CatCrypt gives each part a verified source,
lowers them through typed MLIR-style dialects (close to prime-ir), and emits x86-64,
AArch64, and RISC-V as machine bytes inside Lean. Every lowering is proved to preserve
the denotation, and on each of the three backends the emitted machine block is proved to
compute the source denotation for the straight-line register fragment. Constant time and
robust compilation are proved for parts of the pipeline; the end-to-end statements are
under construction. The [guarantees](#the-guarantees) section names the fragment and
the hypotheses each result carries.
The design also takes inspiration from [AUCurves](https://github.com/AU-COBRA/AUCurves)

Production rust implementation often only emphasize two layers: orchestration in Rust,
and the constant-time-critical code hand-written in assembly, because `rustc` is not
trusted to preserve constant time. A verified constant-time compiler lets each part be 
written at its natural level of abstraction.

> 🚧 **Under construction — experimental research prototype.** The interfaces, the
> covered source fragment, and the emitted surface are evolving; expect breaking
> changes. This is not a production tool.

## The three aspects

- **Orchestration** — Rust, extracted through hax. The extraction eliminates traits,
  generics, closures, and heap references, part of these transformations are proved correct in [hax-lean](https://github.com/spitters/hax-lean), and hands the
  covered control spine to LowCT, a low level constant-time language, and further to the dialect stack.
  These can also be authored directly in a lean AST or in lean surface, using rupicola style relational compilation.
- **Algebra** - The field, modular-arithmetic, elliptic-curve, and
  polynomial/NTT dialects are the verified analogs of
  [PrimeIR](https://github.com/fractalyze/prime-ir)'s MLIR dialects for cryptography
  — the algebraic tier that structures the compiler over a Jasmin-like language, phrased as an MLIR dialect. A
  companion Rust library exposes these operations to hax, and a kernel that uses them
  compiles to the matching dialect operation.
- **Leaves** — Jasmin style structured assembly. Jasmin is presented as an MLIR dialect, and the compiler both compiles to it and imports from it (below).

For example, an ML-KEM protocol is edited where each part lives: the orchestration —
key schedule and message flow — in Rust or Lean; the algebra — the number-theoretic
transform and field arithmetic — in the MLIR/prime-ir dialects, targeted from a Lean
specification by relational compilation; and only the hand-tuned leaves stay at the
assembly level. The verified compiler carries constant time and correctness across
all three, so no part drops to assembly for trust.

## The dialect stack, and a two-way verified relationship with Jasmin

```mermaid
flowchart TD
    RUST["Rust source"] -->|hax| IR
    SPEC["Lean specification"] -->|relational compilation| IR
    IR["SSA IR"] --> ALG["prime-ir algebra dialects"]
    ALG --> JAS["word-level Jasmin dialect"]
    JAS --> BE["backend"]
    BE --> X86["x86-64"]
    BE --> ARM["AArch64"]
    BE --> RV["RISC-V"]
```

*Two source fronts converge on one IR; every arrow is a lowering proved to preserve
the denotation.*

The source lowers through typed dialects — an SSA intermediate representation, the
prime-ir algebraic dialects, and the word-level Jasmin dialect — down to a backend
that encodes instructions to bytes for x86-64, AArch64, and RISC-V. Every
dialect carries a Lean denotation, and every lowering is a Lean function proved to
preserve it, so a well-typed term denotes its specification by construction. The IR
structure follows [lean-mlir](https://github.com/opencompl/lean-mlir) (via the Veir
library); code generation is CatCrypt's own backend, which initiated from a port of
the jasmin compiler. Unverified LLVM code generation is also possible.

The compiler both compiles *to* [Jasmin](https://github.com/jasmin-lang/jasmin) and
imports *from* it, both inside Lean. The algebraic dialects lower to the Jasmin
dialect, which reaches x86 by either the bytes-direct encoder or Jasmin's own
verified compiler, reached by printing Jasmin text; and hand-written Jasmin leaves
are imported through the same backend. 
[PROVENANCE.md](PROVENANCE.md) records the low-level-IR
lineage: AUCurves, bedrock2, Rupicola.

## The guarantees

The pipeline preserves three properties from source to emitted bytes. The
[manual](docs/CompilerManual.lean) states them in full, with the headline theorems.

- **Functional correctness** — each lowering is proved to preserve denotation, so a
  well-typed term over the covered fragment denotes its source specification at every
  dialect boundary. At machine level, `com_x86_e2e` / `com_arm_e2e` / `com_riscv_e2e`
  prove that the compiled block, run on the backend's block semantics, computes the
  source `Com.denote` for a straight-line program over the supported op set in an
  all-`reg 64` context; on the base-ALU subset of that fragment,
  `ComToArmLsem.comToArmLsem_correct` and `ComToRiscvLsem.comToRiscvLsem_correct` add
  that every executed instruction lies in the subset checked against the vendor Sail
  model. The whole-pipeline x86 statement `robustCompilation_source_to_x86` carries a
  lattice-dialect source to the emitted x86 observable, with jasmin's verified compiler
  as an explicit hypothesis. The Rust front's end-to-end result
  (`rustToJasminCom_endToEnd`) agrees with the source over the machine-word semantics on
  the `IsCoveredCtl` fragment, data-dependent loops included. (Example: the lattice NTT
  compiles to the source polynomial multiply.)
- **Constant-time** — preserved over the full modern constructor set, including
  data-dependent loops: a loop is constant-time exactly when its guard is public,
  and the analyzer accepts a public-count loop and rejects a secret-dependent one.
  The constant-time clause is anchored on the x86-64 machine model; the AArch64 and
  RISC-V backends carry functional correctness. An information flow calculus allows
  us to write non-CT code too.
- **Security** — Hax allows us to use a protocol's source both as input to the catcrypt compiler and as a source for proofs in the computational model in CatCrypt, in the spirit of [Last yard](https://eprint.iacr.org/2023/185). Carrying a security bound onto the emitted bytes — byte-level transfer — holds for the symmetric family and is a roadmap goal for the asymmetric families.


## What this repository contains

The compiler: the two fronts, the dialect stack, the equality-saturation optimizer,
the x86-64 / AArch64 / RISC-V backend, and the correctness theorems. Primitive kernels compiled
through it are in this package too: AES-128, GF(2^128), HMAC, Keccak/SHAKE,
Poly1305, SHA-256/512, BLAKE3, the BN254 and BLS12-377 pairing arithmetic, the HAWK
negacyclic and NTRU-HRSS ring multiplies, the FN-DSA emit modules, and the Plonky3 /
Bulletproofs reflect modules. What lives in the wider CatCrypt development is the
security layer — the scheme security proofs and the UC/MPC protocol chains — which
this package's module closure deliberately excludes (see the comment on
`lean_lib CatCryptCompiler` in `lakefile.lean`). The [CatCrypt
paper](https://eprint.iacr.org/2026/604) describes the full system;
[CITATION.cff](CITATION.cff) carries the citation metadata.

## Source coverage — the language of constant-time crypto

The covered source is the prime-ir algebra and the control spine that cryptography
is written in. It covers straight-line leaf calls, counted and public-condition
loops, branchless select, public-index array access, tuples, byte slices, and
fixed-width and widening integer arithmetic, over the prime-ir algebraic operations;
data-dependent loops are covered too. SIMD intrinsics enter through an explicit-SIMD
vector front with verified semantics (for example, AES and carry-less multiplication). The language
expresses both constant-time and variable-time kernels: a public-input variable-time
path such as RSA verification is accepted, and a secret-dependent one is rejected.
The relational front compiles Lean specifications directly.

## Build, dependencies, documentation

[GETTING_STARTED.md](GETTING_STARTED.md) compiles a program in one command;
[DEMO.md](DEMO.md) and [EXAMPLES.md](EXAMPLES.md) walk the two fronts and the
buildable example modules; [bench.md](bench.md) reports the measured performance; the
[manual](docs/CompilerManual.lean) — a [Verso](https://github.com/leanprover/verso)
document — gives the narrative and the headline theorems.

See [BUILDING.md](BUILDING.md). Dependencies resolve from git:
[`catcryptCore`](https://github.com/spitters/CatCrypt-core) (the CatCrypt
methodology library), `Veir`,
[`paramTransfer`](https://github.com/spitters/ParamTransfer) (the proof-transfer
bridge), `CompPoly`, [`hax-lean`](https://github.com/spitters/hax-lean) (the
typed hax front), `mathlib`. Generating the API reference and the proof blueprint
is covered in [BUILDING.md](BUILDING.md) as well.
