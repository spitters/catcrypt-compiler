/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import VersoManual

open Verso.Genre Manual

#doc (Manual) "The CatCrypt verified compiler for cryptography" =>

_Experimental research prototype._ This compiler is part of the CatCrypt project
([ePrint 2026/604](https://eprint.iacr.org/2026/604.pdf)). Its interfaces, the
covered source fragment and the trusted base change without notice. It is not a
production tool.

A cryptographic implementation has three parts: _orchestration_ (the protocol and
its control flow), _algebra_ (field, curve and polynomial arithmetic) and _leaves_
(low-level primitives). CatCrypt accepts each part at its own level of abstraction,
lowers it through typed MLIR-style dialects, and emits x86-64, AArch64 and RISC-V
code inside the Lean 4 proof assistant. The lowering from the SSA intermediate
representation to the Jasmin dialect is proved to preserve the denotation of every
program it accepts. On each of the three backends, a scalar instruction selection is
proved to compute the source denotation of a straight-line program over 64-bit
registers. The package `README.md` states each result with its fragment and its
hypotheses, and `CAPABILITIES.md` records, for each primitive, how its kernel is
produced and which theorems hold for it.

The API reference is generated separately, by doc-gen4 from the module docstrings
(see `BUILDING.md`), and gives the per-declaration signatures;
`lake env lean AxiomAudit.lean` prints the axioms of the theorems that file lists.

# The three aspects

Production Rust implementations of cryptography are usually split into two layers:
orchestration in Rust, and the constant-time-critical code hand-written in assembly,
because `rustc` is not trusted to preserve constant time. A compiler proved to
preserve constant time lets each part be written at its natural level of
abstraction. The chapters below state how far the theorems of this package reach.

_Orchestration_ is the protocol and its control flow: the message flow, the key
schedule, the loop structure. Its source is Rust, exported by
[hax](https://github.com/hacspec/hax) to the typed AST of
[hax-lean](https://github.com/spitters/hax-lean), whose AST and evaluator the
package's hax front reads. hax-lean's own passes (removal of references, local
mutation, loops and early returns) carry denotation-preservation proofs. The hax
export from Rust is outside the proofs, trait methods reach the compiler as named
calls, and complex generic types fall back to an unknown type (hax-lean's
[LIMITATIONS.md](https://github.com/spitters/hax-lean/blob/master/LIMITATIONS.md)). The front translates the program to LowCT, a low-level
constant-time command language, and from there to the dialect stack. Orchestration
can also be written directly in Lean, as a LowCT term or as a Lean function compiled
relationally in the style of Rupicola.

_Algebra_ is the arithmetic a scheme runs on: prime fields, modular and Montgomery
arithmetic, elliptic curves, polynomials. CatCrypt's field, modular-arithmetic,
elliptic-curve and polynomial dialects are Lean dialects with Lean denotations,
modelled on [PrimeIR](https://github.com/fractalyze/prime-ir)'s MLIR dialects for
cryptography. Rust code reaches them through the `primeir-hax` crate, which is not
part of this package: the hax front recognises a call to one of its trait methods by
name and emits a single-operation program in the matching dialect. In this package
none of these dialects has a `Com`-level lowering to the Jasmin dialect;
`VIR/DIALECTS.md` gives the lowering graph.

_Leaves_ are the low-level primitives: a field multiply, an AES round, an NTT
butterfly. Their language is [Jasmin](https://github.com/jasmin-lang/jasmin),
presented as an MLIR-style word-level dialect. The compiler relates to Jasmin in both
directions: it compiles to the Jasmin dialect, and it imports hand-written Jasmin
leaves through the same backend. Inside the dialect stack a leaf call is opaque: in
`catCryptDialect` an `extCall` denotes a default value, so a value statement about a
kernel that calls leaves needs a leaf semantics supplied as a hypothesis.

An ML-KEM implementation illustrates the intended division: the key schedule and
message flow as orchestration, the number-theoretic transform and field arithmetic
as algebra, and the hand-tuned kernels as leaves. The package does not carry ML-KEM
through that division. The route that lowers an NTT multiply to Jasmin passes
through the lattice dialect, which models the NTT and inverse NTT as the identity.
No theorem relates the batched ML-KEM NTT Jasmin text that `VIR/LatticeNttEmit.lean`
renders to the transform; the lane-independence theorems of that module are
instantiated at an identity per-lane block.

# The pipeline

The passes, in order:
`Rust (hax) or Lean spec (relational) → SSA IR → Jasmin dialect → backend → x86-64 / AArch64 / RISC-V`.
The hax export is outside the proofs, and every later arrow is a Lean function. A
lowering returns `none` on a program outside the fragment it accepts, and its
preservation theorem holds whenever it returns a program. The printers that write
assembly text carry no theorem.

The two sources, Rust through hax and Lean specifications, reach one SSA
intermediate representation, `catCryptDialect`. The relational front relates a Lean
specification, through an injective encoding into machine words, to a low-level
program by a denotation-preserving relation, in the style of
[Rupicola](https://github.com/mit-plv/rupicola); in `RelationalFrontMachine` the
related `Com` is written in Lean rather than generated (`DEMO.md`). From the
intermediate representation a program lowers to the word-level Jasmin dialect and
then to a backend that emits assembly text or machine bytes for x86-64, AArch64 and
RISC-V.

The dialects on this path carry Lean denotations. When the lowering from
`catCryptDialect` to the Jasmin dialect succeeds, the lowered program denotes the
transport of the source denotation (`cryptoDialectToJasminCom_denote_eq'`).
`compileVia_comp_correct` composes two dialect lowerings with the Jasmin-IR
evaluator `runProg`, under per-operation transport hypotheses, agreement of the
opaque leaves with the evaluator's leaf semantics, and a straight-line lowered
program. The intermediate-representation structure follows
[lean-mlir](https://github.com/opencompl/lean-mlir), through the Veir library; code
generation is CatCrypt's own backend, which began as a port of the Jasmin compiler;
module names and documents call it the owned backend, and its output owned emit.
`PROVENANCE.md` records the low-level lineage: AUCurves, bedrock2, Rupicola.

## The two-way relationship with Jasmin

The compiler reaches machine code through Jasmin in two ways, both inside Lean. It
compiles _to_ the Jasmin dialect, which reaches x86 through CatCrypt's own backend,
or as printed Jasmin text through Jasmin's compiler `jasminc`; the Jasmin printer is
proved structurally only (`VIR/JasminPrintCorrect.lean`). It also imports _from_
Jasmin: hand-written Jasmin leaves are imported through the same backend, and
`JincParserDemo` parses one `.jinc` leaf into the intermediate representation and
inspects it. A further path prints a
Jasmin program as MLIR text for `mlir-opt`, `mlir-translate` and `llc`. That path has
no end-to-end correctness theorem; `MLIRBackend/Denote.lean` proves the shape of the
emitted text and names the external toolchain's correctness as the opaque
proposition `MlirBackendSemanticsAgrees`.

# The optimizer

The optimizer passes over the `Com` intermediate representation carry
denotation-preservation theorems: common-subexpression elimination, dead-code
elimination, copy propagation and constant folding (`comCSE_denote`,
`comDCE_denote`, `copyProp_denote`, `foldCom_denote`). The constant-folding and saturation
stages assume a known-constant environment consistent with the valuation.
`Pipeline.optPipelineJ` composes four stages that each return their input program,
so its theorems hold for every program. `CatCrypt/Crypto/Optimizer/README.md`
indexes the passes.

No emit driver calls a `Com` pass. The owned emit drivers render an `Lprog` through
`LprogOptPipeline.renderOwned`, which is `renderLprogAtt ∘ optimizeLprogBasicBlocks`.
On each maximal straight-line run of a function body whose instructions the passes
model, it applies reload elimination, spill-pair elimination, the scheduler
`LprogScheduler.scheduleLprog`, copy propagation and load common-subexpression
elimination. `mapBodies_entry_store_preserved` states that the optimized program,
run from a function entry under the labeled semantics `JasminLsemLabeled.lsem`,
reaches the same register map and memory as the source.

## Equality saturation

`Optimizer/Rewrite/Egraph.lean` rewrites a `Com jasminDialect` to a fixpoint. It has
no union-find, no e-classes and no congruence closure: `rewriteCom` rewrites each
binding in place, and `saturateCom` iterates it up to a fuel bound. A rule fires on
a binary register operation whose second operand a known-constant environment
`KEnv` records as a constant: `x + 0`, `x ^^^ 0`, `x ||| 0` and `x * 1` become
`x ||| x`, and `x * 0` and `x &&& 0` become the zero operand. The strength reduction
`x * 2^k = x <<< k` is the lemma `mul_pow2_eq_shl` and is not fired by the engine,
because it needs a fresh binder for the shift amount. Under a `KEnv` consistent with
the valuation, `saturateCom_denote` proves that the output denotes the input's
function, and `saturate_cost_le` that its cost under `comCost` does not increase.
The engine reaches a local fixpoint and does not find a global cost minimum.

Two modules separate untrusted search from verified acceptance.
`ProofCarryingExtraction.RewriteWitness` is an ordered
list of rewrite steps, each carrying a denotation equality, validated by folding
the steps with transitivity; `optimizeChecked` emits a candidate only when its
witness applies, and the input otherwise (`optimizeChecked_denote`).
`EgraphGlobalMin` represents an e-class as a list of members, each with a proof of
denotation equality to a representative, and `extractMin` returns a cheapest member
(`extractMin_cost_min`, `extractMin_denote_eq`); its instances choose among two- and
three-limb multiplication formulas over a commutative ring.

The saturation engine reaches `comAlgebraicPipeline` and
`ComToMLIR.emitFuncCanon`, which are referenced only in the modules that define
them, and no assembly the owned backend emits passes through any module of this
section. In the ascent, `EgraphBlockEquality` takes equal saturations of two
programs as a certificate of equal denotation, and
`BytesToDialectJoin.joinBytes_denote_source` applies it to one encoded block that
computes `x ||| x`, against the source `x + z` under the constant hypothesis
`z = 0`. Compared with the e-graphs of Cranelift, the design keeps the search
outside the trusted base and proves one denotation lemma per rule; it has no e-class
data structure, no rule language, and no extraction integrated with instruction
selection.

## Search over schedules and register allocations

Three modules follow CryptOpt (Kuepper et al., PLDI 2023): a randomized local search
over equivalent forms of a straight-line x86 block, whose winner is validated in
Lean in place of CryptOpt's external equivalence checker.
`RandomizedScheduleSearch.searchBest` runs seeded greedy descent over adjacent
transpositions of instructions with disjoint footprints, ranked by the static
latency and port-pressure proxy `scheduleCost`; `tvCertifiesSwaps_sound` validates a
sequence of swaps, and `hoisted_runBlock_eq_input` and `hoisted3_runBlock_eq_input`
prove the winners for the two- and three-product safegcd accumulate equal to the
input on every machine state. `RandomizedRegAlloc.searchAssign` draws a renaming of
virtual registers and accepts it only when it is injective on the live names and
fits the register pool; `regalloc_runBlock_sound` covers every accepted renaming.
`JointScheduleRegAlloc.searchJoint` searches permutations and renamings as one move
space, and its legality predicate `jointLegal` checks schedule dependencies on the
renamed instructions, which excludes the phase-ordering hazard described for SLOTHY
(Becker et al.).

No emit driver calls the three searches, and no shipped kernel is a search output.
The scheduler on the emit path is the deterministic `LprogScheduler.scheduleLprog`
inside `optimizeLprog` and `renderOwned`; it swaps only adjacent independent
instructions (`bubble_only_indep_swaps`) and preserves `lsemStraight`
(`scheduleBody_lsemStraight`).

The measurements, recorded in the development repository, show no speed gain. On
the safegcd accumulate the search winner is 1.03 to 1.05 times slower than the input
schedule with two products and 1.21 to 1.30 times slower with three
(`bench/cryptopt_safegcd/README.md`, lines 45-55 and 93-101). The same two-product
reordering, unrolled 128 times, measures 1.015 times faster, within run-to-run noise
(`bench/slothy_perf/README.md`, lines 16-22). On the fe25519 schoolbook multiply the
search has eight legal swaps, all neutral under the static proxy
(`feMulBlock_legal_swaps`), and the rescheduled block is within noise of the
baseline (`bench/x25519_fieldmul_compare/README.md`, lines 92-124). These files
attribute the result to the carry chain being the critical path and to the
out-of-order core issuing independent multiplies regardless of their order.

## The ascent

The ascent runs opposite to the lowering. It takes code at one of the compiler's
levels (a `LowCT` command, an x86 block `List (JInstr 64)` or an RV64 block) and
proves a correspondence square `Corres SR P f c`, in the style of AutoCorres, from
its runs to a function `f` on integers, field elements or bit vectors. The code is
given rather than produced by the compiler. The results on linked machine code
cover the Ed25519 blocks `ed25519_point_add` (at the encoded bytes), `ed25519_madd`,
`ed25519_invert`, `ed25519_compress`, `ed25519_sc_reduce` and `ed25519_sc_muladd`,
the fe25519 multiply, square, addition and subtraction, the comb-table select,
s2n-bignum's `bignum_montmul_p384`, and the exported `mpn_and_n` loop.

Two covered kernels are CryptOpt output. `CarryMulCorrect.carryMul_correct` and
`SolinasSquareCorrect.solinasSquare_correct` prove that CryptOpt's
`fiat_curve25519_carry_mul` and `fiat_curve25519_solinas_square` meet fiat-crypto's
`mul_correct` and `sqr_correct` congruences, and `CryptOptAddr` restates both over
byte-addressed memory, under separation hypotheses on the input, output and
stack-frame regions (`carryMul_correct_addr`, `solinasSquare_correct_addr`). Code found by a search outside Lean is thereby
verified after the search, with no part of the search in the trusted base.

Ascent and descent meet at a few theorems. `LegWeld.legWeld` joins a source
program, the Jasmin program the compiler emits for it and an ascent square;
`CorresDescentX86.corres_of_refines_x86` turns a relational-compiler result
`Refines spec frag` into an ascent square for the compiled x86 block;
`PipelineWeld.feSub_raw_source_to_bytes` carries the fe25519 subtraction from a hax
`ImpExpr` source to bytes; and `BytesToDialectJoin` joins decoded bytes to a source
program through equal saturations, on the one example above. `ASCENT.md` describes
the calculus, the tactics and each result with its module.

# The guarantee

_Functional correctness._ The lowering from `catCryptDialect` to the Jasmin dialect
preserves the denotation of every program it accepts. At machine level,
`com_x86_e2e`, `com_arm_e2e` and `com_riscv_e2e` prove, for a straight-line program
over the supported operations (`ComOK`) in a context of 64-bit registers, that the
block produced by each backend's scalar instruction selection, run from a state whose
registers hold the inputs, leaves `Com.denote` in the result register; the x86
statement also assumes that shift amounts are in range. The x86 assembly that the
owned exporters write is printed by `renderLeafFn` or `renderLprogAtt` and assembled
by the GNU assembler. Neither printer carries a theorem, and `x86Target` is not the
selection those exporters run.

The Rust-front theorems start at a LowCT program and end at the Jasmin `Com`
denotation. `rustToJasminCom_endToEnd` holds on `IsCoveredCtl` and takes the value
equation relating the dialect program to the LowCT post-state as the hypothesis
`hAdequacy`. `rustToJasminCom_endToEnd_unconditional` has no adequacy hypothesis and
states the Jasmin value over the machine-word semantics `semScalar` on
`IsCoveredSCtl`. Neither fragment contains a data-dependent loop; for data-dependent
`while` loops, `transU_to_jasminCom_endToEnd` states the Jasmin value over the
fuel-bounded semantics `semU` on `IsCoveredSU`. The translation from hax-lean's AST
to LowCT has its own simulation theorems (`haxToLowCT_simulates_program`), which the
Rust-front statements do not include.

For the NTT, `PolyDialect.nttMul_negacyclic_coeff` proves, under its parameter
hypotheses, that the polynomial dialect's NTT multiply denotes the negacyclic
convolution in `Z_q[X]/(Xⁿ+1)`, and `NttEmitDenotationBridge` proves that the
butterfly-stage sequence, as a value model, computes the full 256-point DFT at
ω = 17 over `ZMod 3329` (`nttIter_succ_eq_ctMergeStage`,
`mlkemNttKernelSpec_eq_polyEval`). That DFT is not FIPS 203's 7-layer transform
modulo `X^256 + 1`, and no theorem relates the owned ML-KEM NTT kernel that
passes the NIST KAT to that model. The lattice-route theorems
(`latticeNttMul_compile_correct`, `robustCompilation_source_to_x86`) are stated over the lattice dialect, whose NTT and
inverse NTT denote the identity and whose base multiply is the coefficient-wise
product.

_Constant time._ At machine level, `toLprogPhysAbi_gather_constant_time` states that
when an exported function body gathers to an x86 instruction block with no labels,
conditional jumps or calls, the block's machine leakage trace (branch decisions and
memory addresses) is the same from any two states. `owned_ct_control_flow` states
the same, from any two states that agree on the public registers, for a block built
from conditionals with public guards and loops with literal trip counts; no theorem
states that the block the recogniser `lcmdToOwnedCF` produces executes as the
exported command does. At source level, the analysis `cmdCT` accepts a
data-dependent loop exactly when its guard is labelled public and its body is
accepted (`cmdCT_RWhileNz_iff`), and `cmdCT_sound` states that an accepted program
run from two public-equivalent states reaches public-equivalent states, under the
per-leaf assumption `LeafCTAssumption` and the hypothesis `CMOVInvariant`. Under a
level table in which every slot is public, as for RSA verification, `cmdCT` accepts
an early-terminating modular-inverse loop, and it rejects the same loop when the
guard is secret (`vartimeInvert_public_only`). No theorem carries the source
analysis of a data-dependent loop to emitted code, and the AArch64 and RISC-V
backends have no constant-time theorems.

_Security._ hax lets one Rust source serve both as compiler input and as the model
for computational security proofs in the wider CatCrypt development, following
[The Last Yard](https://eprint.iacr.org/2023/185). The `*SecurityTie` modules equate
a dependency record built from the `Com` denotations of compiled kernels with the
record the security layer reasons over, and `tie_transfer` carries any property of
the second record to the first. The transfer is at the `Com` denotation; no theorem
in the package carries a security bound to emitted machine code.

# Headline theorems

Four theorems are cited as headlines. `AxiomAudit.lean` prints the axioms each one
rests on.

_RISC-V and AArch64 over the model interface_:
`CompileCorrectAllGenuine.compile_correct_all_genuine`. For a `Com` in the base
arithmetic-logic subset (`ComBaseAlu com`) over a context of 64-bit registers
(`AllReg64 Γ`) and either target, reading the result register out of the model's
execution of the compiled and lowered block on the encoded input equals the source
denotation:
```
genuineReadReg choice
    ((genuineModel choice).decodeOut
      ((genuineModel choice).exec (genuineCode com choice)
        ((genuineModel choice).encodeIn (genuineEncode V choice))))
    (comRetName com Γ.length)
  = Com.denote com V
```
The model's `exec` is the block fold `runRBlock64` for RISC-V and `runBBlock` for
AArch64. The per-target theorems are `CompileCorrectBaseAlu.compile_correct_riscv`
and `compile_correct_arm`. On the lattice route,
`CompilerCorrectness.latticeNttMul_compile_correct` states with no hypothesis that
the lowered Jasmin `Com` of the NTT multiply denotes the source program's value.

_Rust front_: `CompilerCorrectnessExtracted.rustToJasminCom_endToEnd`. For a LowCT
source in `IsCoveredCtl`, given a `RustExec` run, a related entry state, the success
of each pass, and the front's value equation as the hypothesis `hAdequacy`, the
Jasmin `Com` denotes the value that a valuation related to the post-state holds in
the tracked output: `jcom.denote (ctMapValD W) = ctTransTy (w.lookup V')`.
`IsCoveredCtl` contains no data-dependent `while` loop. The sibling
`rustToJasminCom_endToEnd_unconditional` has no adequacy hypothesis and states the
value over `semScalar` on `IsCoveredSCtl`, in which an opaque leaf call returns a
default value.

_Robust source to x86_: `RobustCompilationPipeline.robustCompilation_source_to_x86`.
For a lattice-dialect program lowered to Jasmin, the theorem takes the x86
observable and behaviour as parameters. Its conclusion is the `semRefine` field of
its hypothesis `JasminVerifiedCompiler` applied to the evaluator-level result, so the
statement contains no x86 instruction semantics. The one instance in the package,
`OwnedX86RobustInstance.ownedJasminVerifiedCompiler`, takes the evaluator result as
the observable. Leaf agreement and SSA-naming injectivity are further hypotheses.
The theorem states no constant-time property; constant time of emitted code is
proved at the decoded bytes by `DecodedCT.bytesCTCheck_sound`, with the acceptance
theorems `DecodedCT.mul1Node_bytesCT` and `DecodedCT.feAddFramed_bytesCT`.

_Machine code_: `ScalarLinX86Demo.com_x86_e2e`. For a straight-line `Com` over
`ComOK` in a context of 64-bit registers (`AllReg64`), with shift amounts in range
(`ShiftAmtOK`) and a state `s` whose registers hold the inputs,
```
(x86Target.runOps s (x86Target.compile (comToRegProg com Γ.length))).regs (comRetName …)
  = Com.denote com V
```
that is, running the ops of the scalar selection `x86Target` leaves the source
`Com`'s denotation in the result register. The x86 assembly that the owned exporters
write comes from other routes, which this theorem does not cover.
`ComToArmLsem.comToArmLsem_correct` and `ComToRiscvLsem.comToRiscvLsem_correct` state
the AArch64 and RISC-V results over the machine models `runBBlock` and `runRBlock64`
on the base arithmetic-logic subset, and add that every instruction of the block lies
in that subset.

# The backends and the trusted base

The compiler has one backend with three instruction sets, and only the x86 side has
constant-time theorems. The package contains no Sail source, and no backend is
checked against a Sail model it vendors. For RISC-V, `riscvStep64_sail_grounded`
proves, under an alignment of register names with register numbers, that each base
arithmetic-logic instruction of the model writes the value written by an
`execute_RTYPE` clause copied by hand from `opencompl/sail-riscv-lean` (commit
`9eba3f07`, generated from the [sail-riscv](https://github.com/riscv/sail-riscv)
specification) into `RISCVBackend/SailRiscv64Refinement.lean`, where it runs over a
simplified register-file state monad. For AArch64 no theorem relates the model
semantics `runBBlock` to a Sail execute clause; the model rests on the hand-written
`ArmModel` semantics and on differential testing against the GNU assembler and qemu,
with a harness that is not in this package. The encoders of both backends carry
decode round trips, `decode (encode i) = i`, against decode field splits transcribed
by hand from the sail-arm and sail-riscv decode clauses (`SailArmDecoder`,
`SailRiscvDecoder`, `SailRiscvDecoder64`); these round trips are not conjuncts of the
machine-code theorems.

The trusted base includes the following. The package declares axioms, both
uninterpreted types and operations of the reflection and Vale leaf modules and
propositions about concrete computations and external tools, among them
`bn254_pairing_correct_rocq`. The hax export, the assembly
printers and the GNU assembler are trusted. A theorem depends on an axiom only if
`#print axioms` lists it; the Scope section of `README.md` gives the command that
lists the axioms.

Leaves are trusted or taken as hypotheses. The AES round is the `VAESENC`
instruction. The BLS12-377 field and pairing arithmetic, and the BN254 field
subtraction, addition and inversion, are AUCurves routines called as external
symbols. At the dialect level an opaque leaf call denotes a default value, so a
statement about a kernel that calls leaves takes the leaf semantics as a hypothesis,
such as `LeafAgrees` or the leaf oracles of the BN254 and BLS12-377 denotation
theorems. `CAPABILITIES.md` states, per primitive, which parts are trusted leaves.

# Benchmarks

`bench.md` reports cycle-count ratios measured in the CatCrypt development
repository against production implementations at the same instruction tier
(s2n-bignum, libcrux, `HACL*`, formosa, liboqs and the PQC reference codes), with
the rows where we lead only through an instruction-set extension the production
code does not use listed apart. The 4-way SHA-512, ML-KEM-768 against libcrux,
SDitH, the 8-way SHA-256 and SNOVA are ahead; the field multiplies, X25519,
ChaCha20-Poly1305, AES-CTR and HMAC are at parity; the scalar SHA-2 and Keccak
kernels and the whole-protocol signers are behind. `bench/SCOREBOARD.md` is the
full record with tiers, harness commands and corrections. The harnesses and
references are not in this package, so no ratio can be reproduced from it, and for
most rows the timed object file is not shipped; `bench/PROVENANCE.md` describes the
assembly files that are.

# A worked example

Two example modules exercise the backends and the front.

`MultiBackendDemo` compiles a register program `r := a·b + a`, and a `Com` that
binds one 64-bit multiply, to AArch64 and to RISC-V. For each backend a theorem
equates the run of the machine block with the scalar selection's denotation of the
register program (`kernel_arm`, `kernel_riscv`, `mulCom_arm`, `mulCom_riscv`).
`mulCom_riscv_e2e` states that the RISC-V block leaves `Com.denote mulCom V` in the
result register; it is an instance of `com_riscv_e2e`, which holds for every
supported `Com`, and `com_arm_e2e` is the AArch64 counterpart.

`CompileFromHaxLinkExample` links two front-lowered programs. The outer program
`let r = sha256_sigma0(inp[0]); ret r` is a `Thir` term written in Lean, not a hax
extraction, and the scalar front lowers it to a `Com` with one external call. The
leaf is `ThirToComFront.sigma0Com`, the front lowering of the SHA-256 σ₀ term, which
`sigma0Com_denote` proves equal to the FIPS 180-4 formula for every input word.
`inlineCalls` inlines that kernel at the call, and `linkedExample_correct` proves,
with no hypothesis, that the linked program `linkedSigma0Com` denotes
`x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> 3` for every 32-bit `x`.

The two modules are `CatCrypt.Crypto.SecureCompilation.MultiBackendDemo` and
`CatCrypt.Crypto.SecureCompilation.CompileFromHaxLinkExample`. `EXAMPLES.md` gives
the build command for each, and `AxiomAudit.lean` prints the axioms of the theorems
it lists.

# Scope

The covered source is the prime-ir algebra and the control spine that cryptography
is written in: straight-line leaf calls, counted and public-condition loops,
branchless select, public-index array access, tuples, byte slices, and fixed-width
and widening integer arithmetic, over the prime-ir algebraic operations. The front
also accepts data-dependent loops; the guarantee above states what is proved about
them. SIMD intrinsics enter through an explicit-SIMD vector front with its own
semantics.

Several primitives have kernels in the package without a whole scheme. HAWK is
present as a degree-16 tile of the negacyclic ring multiply over
`Z/1024[x]/(x¹⁶+1)`, whose deployed program is checked against a reference on four
input pairs by `native_decide`, and as the HAWK-512 NTT butterflies (generation
checks only) and pointwise Montgomery multiply (its loop checked on one sample input
at a small instance). NTRU-HRSS is present as a degree-16 tile of the
cyclic ring multiply over `Z/8192[x]/(x¹⁶−1)`, checked in the same way. FN-DSA
(Falcon) is present as the Jasmin text of the verify subtraction and of a CDT base
sampler, both rendered from string templates; no theorem relates either text to its
specification, and no theorem states the constant time of either text or the
statistical-distance bound of the sampler. `CAPABILITIES.md` lists every primitive
with its modules and theorems.

# How this documentation is organized

Three layers document the compiler: this manual (the narrative and worked examples),
the API reference (every declaration with its signature, generated by doc-gen4), and
the blueprint outline `blueprint/src/content.tex`, which lists the headline
statements, each with a reference to its formal theorem. `BUILDING.md` describes how
to build the manual and the API reference. The package carries no leanblueprint
build files, so the outline is a source document only.
