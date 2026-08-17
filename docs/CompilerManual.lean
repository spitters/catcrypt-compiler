/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import VersoManual

open Verso.Genre Manual

#doc (Manual) "The CatCrypt verified compiler for cryptography" =>

🚧 _Under construction — experimental research prototype._ This compiler is part of
the CatCrypt project ([ePrint 2026/604](https://eprint.iacr.org/2026/604.pdf)). The
interfaces, the covered source fragment, and the trusted base are evolving. This is
not a production tool.

A crypto implementation has three parts: _orchestration_ (the protocol and control
spine), _algebra_ (field, curve, and polynomial mathematics), and _leaves_
(low-level hand-tuned primitives). CatCrypt gives each part a verified source,
lowers them through a stack of typed MLIR-style dialects, and emits constant-time
x86-64, AArch64, and RISC-V as machine bytes inside the Lean 4 proof assistant. A
machine-checked proof shows the emitted kernel denotes its source specification over
the covered fragment, under the hypotheses each backend's statement carries. The
correctness proof is over the compiler, not per primitive, so a new primitive is a
recompilation.

The API reference is generated separately, by doc-gen4 from the module docstrings
(see `BUILDING.md`), and gives the per-declaration signatures; `AxiomAudit.lean`
prints the axiom ledger of the machine-checked theorems.

# The three aspects

A cryptographic implementation is written, implicitly, at three levels. CatCrypt
makes that structure explicit and gives each level a verified path to machine code.

Crypto today splits that structure by trust rather than by nature: the orchestration
in Rust, but the constant-time-critical code hand-written in assembly, because `rustc`
is not trusted to preserve constant time. A verified compiler removes the split — it
preserves constant time itself, so each part is written at its natural level and
compiled with trust.

_Orchestration_ is the protocol and control spine — the message flow, the key
schedule, the loop structure. Its source is Rust, extracted through
[hax](https://github.com/hacspec/hax). The extraction eliminates trait methods,
generics, closures, and heap references, each step proved correct, and hands the
covered control spine to the dialect stack.

_Algebra_ is the mathematics a cipher runs on — prime fields, modular and Montgomery
arithmetic, elliptic curves, polynomial and NTT forms. CatCrypt's algebraic dialects
are the verified analogs of [PrimeIR](https://github.com/fractalyze/prime-ir)'s MLIR
dialects for cryptography, and they structure the compiler over a Jasmin-like
substrate. A companion Rust library exposes these operations, so a kernel that uses
them compiles to the matching dialect operation.

_Leaves_ are the low-level, hand-tuned primitives — a field multiply, an AES round,
an NTT butterfly. Their language is [Jasmin](https://github.com/jasmin-lang/jasmin),
whose word-level dialect is the compiler's MLIR substrate. The compiler relates to
Jasmin in both directions: it compiles to the Jasmin dialect, and it imports
hand-written Jasmin leaves through the same backend.

An ML-KEM protocol shows the division. The orchestration — key schedule and message
flow — stays in Rust or Lean. The algebra — the number-theoretic transform and field
arithmetic — is expressed in the MLIR/prime-ir dialects, targeted from a Lean
specification by relational compilation. Only the hand-tuned leaves remain at the
assembly level. The verified compiler carries constant time and correctness across
all three, so no part drops to assembly for trust.

# The pipeline

The passes, in order:
`Rust (hax) or Lean spec (relational) → SSA IR → prime-ir algebra → Jasmin dialect → backend → x86-64 / AArch64 / RISC-V bytes`.
Each arrow is a total Lean function proved to preserve the denotation.

The two sources — hax-extracted Rust and Lean relational specifications — feed one
SSA intermediate representation. The relational front relates a specification to a
low-level program by a denotation-preserving relation, in the style of
[Rupicola](https://github.com/mit-plv/rupicola). From the intermediate
representation a source descends through the algebraic dialects and the word-level
Jasmin dialect to a backend that encodes instructions to bytes for x86-64,
AArch64, and RISC-V.

Every dialect carries a Lean denotation, and every lowering is a total Lean function
proved to commute with the two denotations. Chaining the lowerings composes the
per-step preservation proofs into the whole-pipeline result, so a well-typed term
denotes its specification by construction. The intermediate-representation structure
follows [lean-mlir](https://github.com/opencompl/lean-mlir); code generation is
CatCrypt's own backend. `PROVENANCE.md` records the low-level lineage: AUCurves,
bedrock2, Rupicola.

## The two-way relationship with Jasmin

The compiler reaches machine code through Jasmin in two ways, both inside Lean. It
compiles _to_ the Jasmin dialect, which reaches x86 by either the bytes-direct
encoder or Jasmin's own verified compiler, reached by printing Jasmin text. And it
imports _from_ Jasmin: a hand-written Jasmin leaf is parsed into the intermediate
representation and lowered through the same backend. The external `jasminc`
tool is a differential byte oracle.

# The optimizer

Optimization is verified equality saturation. Rewrites populate an e-graph of
equivalent terms, and a cost model selects a representative. Every rewrite is an
instance of the same denotation-preserving relation that drives compilation, so an
optimized term is equal in denotation to its input. The optimizer and the compiler
share one object.

# The guarantee

The pipeline preserves three properties from source to emitted bytes.

_Functional correctness._ Each lowering preserves the denotation, so a well-typed
term over the covered fragment denotes its source specification at every dialect
boundary. For the lattice NTT, the compiled code equals the source polynomial
multiply. At machine level, `com_x86_e2e`, `com_arm_e2e` and `com_riscv_e2e` prove
that the compiled block computes the source `Com.denote` for a straight-line program
over the supported op set in an all-`reg 64` context. The Rust-front result reaches
the tracked output over the machine-word semantics on the `IsCoveredCtl` fragment and
covers data-dependent loops.

_Constant time._ The emitted code preserves constant time over the full modern
constructor set, data-dependent loops included. A loop is constant-time exactly when
its guard is public: the analyzer accepts a public-count loop and rejects a
secret-dependent one. A public-input variable-time kernel, such as an RSA
verification, is accepted, and a secret-dependent one is rejected.

_Security._ Security is proven in the computational model, with hax as the entrance
to those proofs. Carrying a security bound onto the emitted bytes — byte-level
transfer — holds for the symmetric family and is a roadmap goal for the asymmetric
families. Transfer is where hax's two roles, compiler frontend and proof entrance,
meet: a goal beyond the compiler's correctness.

`lake env lean AxiomAudit.lean` prints the axiom ledger of the machine-checked
theorems.

# Headline theorems

Four machine-checked theorems govern the pipeline. `AxiomAudit.lean` prints the
axiom set each one rests on.

_Compiler correctness_ — `Compiler.compile_correct_all`. At lattice parameters `q`,
`n`, decoding the run output of the emitted code `m` equals the source's
per-slot denotation:
```
(chosenModel choice q n).validated
∧ M.decodeOut (M.exec m (M.encodeIn (fun j => runOutputToWords (runProg leafSem m (mapVal V)) j))) i
    = latticeDenote q n V i
```
Five hypotheses are explicit arguments, carried rather than assumed: `hVal`, the
chosen model's own validation proposition; `hLeaf : LeafAgrees leafSem`, the leaf
agreement edge; `hInj`, injectivity of the fresh-name supply; `hPinj`, injectivity
of the whole-function lowering's parameter map; and `hCompile`, the witness that
`compile q n (.lattice q n)` returned `m`. The statement is at the lattice route:
`compile` returns `none` on the front route, whose correctness is
`Compiler.compile_correct_front`. This is an evaluator-level statement: for the
lattice carrier, `exec` is the identity that re-exposes the `Com` evaluator
`runProg`, and `validated` is that carrier's encode∘decode round-trip carried as
`hVal` — so the equation constrains the emitted `Com`'s denotation, not an
instruction-set execution. The theorems that run actual backend instructions are
`CompileCorrectBaseAlu.compile_correct_riscv` / `compile_correct_arm` over the
base-ALU subset, and `com_x86_e2e` at x86.

_Rust front, end to end_ — `CompilerCorrectnessExtracted.rustToJasminCom_endToEnd`. A
hax-extracted source, lowered through the dialect stack to the Jasmin `Com`, denotes
the value the source leaves — `jcom.denote (ctMapValD W) = ctTransTy (w.lookup V')` —
on the `IsCoveredCtl` fragment, data-dependent loops included, with the front's
adequacy edge carried as an explicit hypothesis; the sibling
`rustToJasminCom_endToEnd_unconditional` discharges that edge over the scalar
machine-word semantics `semScalar`.

_Robust source to x86_ — `RobustCompilationPipeline.robustCompilation_source_to_x86`.
For every lattice-dialect source program, the emitted-and-compiled x86 observable is
the decode of the transported source meaning — no drift through lowering, emission,
or the Jasmin compiler — and the emitted code is constant-time at x86. Jasmin's
verified compiler enters as an explicit `JasminVerifiedCompiler` hypothesis,
alongside leaf agreement and the SSA-naming injectivity side conditions.

_Concrete x86 execution_ — `ScalarLinX86Demo.com_x86_e2e`. This is the theorem that
actually runs instructions: for a straight-line `Com` over the all-`reg 64` fragment,
```
(x86Target.runOps s (x86Target.compile (comToRegProg com Γ.length))).regs (comRetName …)
  = Com.denote com V
```
— the emitted ops, executed on the x86 target semantics, land the source `Com`'s
denotation in the result register (`ComOK`/`AllReg64`/`ShiftAmtOK` are the fragment's
coverage hypotheses, not assumptions of the conclusion). Where `compile_correct_all`
stops at the `Com` evaluator under an identity carrier, this closes the last step onto
concrete instruction execution; `ComToArmLsem.comToArmLsem_correct` /
`ComToRiscvLsem.comToRiscvLsem_correct` do the same for AArch64 / RISC-V against the
vendor Sail models over the base-ALU subset.

# The backends and the trusted base

The compiler has one backend for three architectures. The x86-64
backend carries the constant-time clause. The AArch64 and RISC-V backends emit and
run end to end, with `decode ∘ encode` round-trips proved against the transcribed
vendor Sail decode clauses — the emitted RV64I subset for RISC-V, the GP-ALU subset
for AArch64 — and with the emitted block proved to compute the source denotation on
the base-ALU, all-`reg 64` fragment (`ComToArmLsem.comToArmLsem_correct`,
`ComToRiscvLsem.comToRiscvLsem_correct`); the constant-time model is x86. What
grounds the execution semantics differs between the two. For RISC-V, each base-ALU
step of the model is proved to write the value the `execute_RTYPE` clause of the
official [Sail](https://github.com/riscv/sail-riscv) specification writes. For
AArch64 there is no in-tree `sail-arm` execute model, so the steps rest on the
decode round-trip, differential testing against the GNU assembler and qemu, and the
hand-written `ArmModel` semantics.

The trusted base is named. It comprises the cryptographic-hardness assumptions the
protocols rest on; the per-architecture machine model the backend is checked
against; the cited Jasmin constant-time-preservation theorem; and the fidelity of
hax extraction. The byte-level instruction facts — the decode/encode round-trip and
the arithmetic-carry instructions — are proved theorems, and the backend
carries no `jasminc` assumption.

The leaves are verified: symmetric primitives emitted in Lean, and arithmetic and
curve leaves by AUCurves and fiat-crypto, carried as cross-prover results. Two
residuals remain: the advanced-pairing mathematics, which mirrors upstream
assumptions and lies outside the compiler-correctness proof, and the byte-level
security transfer for the asymmetric families.

# Benchmarks

The emitted assembly is measured against the fastest deployed references — Jasmin,
libcrux, fiat-crypto, s2n-bignum, Vale — cycle-for-cycle at matching scope. The
field and bignum kernels are at parity, and the symmetric primitives are at or ahead
of the optimized reference. The measured ratios, the method, and the per-family
coverage are in `bench.md`; the harness that produces them is part of the wider
CatCrypt development, not of this package.

# A worked example

Two programs travel the whole pipeline. One is authored in Lean: a kernel computing
`v2 := v0 · v1` in the shared register waist. The compiler flattens it to a register
program, then lowers that to an AArch64 machine block and to a RISC-V one, with a
theorem for each backend proving the compiled block computes the source denotation.
The general result behind them holds for every supported program, so the kernel is
one instance of it.

The other starts in Rust — a routine that calls the SHA-256 σ₀ leaf. hax extracts it,
the front lowers it to a term with one leaf-call boundary, and linking the σ₀ leaf
proves the compiled program denotes the FIPS 180-4 formula
`(x ror 7) ⊕ (x ror 18) ⊕ (x >> 3)`. This is the two-front path: a compiled outer met
with a fast leaf at one call boundary.

The two modules are `MultiBackendDemo` and `CompileFromHaxLinkExample`. `DEMO.md`
lists the commands to build and inspect them, and `AxiomAudit.lean` prints what the
endpoints rest on.

# Scope

The covered source is the prime-ir algebra and the control spine that cryptography
is written in: straight-line leaf calls, counted and public-condition loops,
branchless select, public-index array access, tuples, byte slices, fixed-width and
widening integer arithmetic, and data-dependent loops, over the algebraic
operations. SIMD intrinsics enter through an explicit-SIMD vector front with
verified semantics. The relational front compiles Lean specifications directly.

Some primitives are present as arithmetic and permutation leaves rather than whole
signers: HAWK is emitted at the NTRU-ring-multiply level, and FN-DSA (Falcon) is
reference-linked because its discrete-Gaussian sampler is variable-time. The
constant-time clause is anchored on the x86 model; AArch64 and RISC-V carry
functional correctness and byte encoding.

# How this documentation is organized

Three layers document the compiler: this manual (the narrative and worked examples),
the API reference (every declaration with its signature, generated by doc-gen4), and
the proof blueprint (the theorem-dependency graph linking each informal statement to
its formal theorem). See `BUILDING.md` for how to build the manual and the API
reference; the blueprint is currently a statement outline without its build
scaffolding.
