# catcrypt-compiler

A compiler for cryptographic code, written in the Lean 4 proof assistant together
with its correctness proofs. It accepts a program as extracted Rust or as a Lean
specification, lowers it through typed dialects that each carry a Lean denotation,
and emits x86-64, AArch64 and RISC-V code inside Lean. The design draws on
[AUCurves](https://github.com/AU-COBRA/AUCurves), bedrock2, Rupicola and
[Jasmin](https://github.com/jasmin-lang/jasmin) ([PROVENANCE.md](PROVENANCE.md)).

The package builds with the Lean toolchain `v4.33.1` ([lean-toolchain](lean-toolchain));
[BUILDING.md](BUILDING.md) gives the setup.

## The pipeline

Each stage names the theorem that states its correctness; the table below gives the
statements.

1. Rust to LowCT. hax exports Rust to the AST of hax-lean, and
   [`haxToLowCT`](CatCrypt/Crypto/Hax/HaxToLowCT.lean) translates it to the word-level command language
   LowCT: [`haxToLowCT_simulates_program`](CatCrypt/Crypto/Hax/HaxToLowCTSim_Program.lean).
2. A Lean specification to code, by relational compilation in the sense of Rupicola: a
   program is derived from a Lean function together with the proof that relates the
   two. The front [RelationalFront](CatCrypt/Crypto/SecureCompilation/RelationalFront.lean) compiles toward machine
   code ([`addMod251_source_eq_arm`](CatCrypt/Crypto/SecureCompilation/RelationalFrontMachine.lean)), and the reifier
   `reifyImp%` compiles a Lean function to Rust
   ([HAX_RUST.md](HAX_RUST.md#2-pure-lean--rust),
   [`edwardsAdd_endToEnd`](CatCrypt/Hax/ReifyImpEndToEnd.lean)).
3. LowCT to the SSA IR: [`transU_denote`](CatCrypt/Crypto/SecureCompilation/Dialects/TranslateDialectUnifiedDenote.lean).
4. The SSA IR to the Jasmin dialect:
   [`cryptoDialectToJasminCom_denote_eq'`](CatCrypt/Crypto/SecureCompilation/VIR/DialectToJasminComCorrect.lean). Stages 3
   and 4 compose in
   [`rustToJasminCom_endToEnd_unconditional`](CatCrypt/Crypto/SecureCompilation/VIR/CompilerCorrectnessExtracted.lean).
5. Instruction selection to x86-64, AArch64 and RV64:
   [`com_x86_e2e`](CatCrypt/Crypto/SecureCompilation/ScalarLinX86Demo.lean), [`com_arm_e2e`](CatCrypt/Crypto/SecureCompilation/ScalarLinNeutralDemo.lean),
   [`com_riscv_e2e`](CatCrypt/Crypto/SecureCompilation/MultiBackendDemo.lean).
6. Register allocation on x86-64. A checker compares each allocated body with its
   input, which is translation validation
   ([CORRECTNESS.md](CORRECTNESS.md#proofs-checks-and-translation-validation-in-haxc)):
   [`ownedCheckMC_sound`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedLprogTVChecked.lean).
7. Emitted loops in the linear machine model:
   [`whileMem_export_faithful_comL_uncond`](CatCrypt/Crypto/SecureCompilation/VIR/JasminLsemMemSourceTieWhileUncond.lean)
   and the loop theorems of [HEADLINES.md](HEADLINES.md#emitted-loops).
8. Encoding to bytes and statements on decoded bytes:
   [`roundtrip_block`](CatCrypt/Crypto/SecureCompilation/X86Backend/SailX86BlockRoundtrip.lean),
   [`bytesCTCheck_sound`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodedCT.lean).
9. The ascent, from code back to a specification. On the blocks that the backend
   printed it is verified decompilation in the sense of Myreen's decompilation into
   logic ([ASCENT.md](ASCENT.md#verified-decompilation-of-the-projects-compiler-output)):
   [`paShippedBytes_correct`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519PointAddBytes.lean). On code written
   elsewhere: [`s2nMontmulP384_correct_addr`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontmulP384Addr.lean).

## The guarantees

Each row states one result; the Lean name links to its source file.

| What is proved | For which programs | Lean |
|---|---|---|
| An evaluation of a hax-lean program by `evalImp` is matched by a run of the LowCT execution relation `RustExec` on its translation, from related entry states to related exit states. | programs that `haxToLowCT` translates and the scope check `simScope` accepts, under the call-side conditions `FullSimPreconds`, `ProjPreconds` and `ProgramSimArms` | [`haxToLowCT_simulates_program`](CatCrypt/Crypto/Hax/HaxToLowCTSim_Program.lean) |
| The SSA code that the unified translation `transU` produces for a LowCT program at a given entry environment and fuel, followed by any continuation, denotes that continuation at a valuation consistent with the environment the source semantics `semU` returns. The translation unrolls each data-dependent loop to the trip count of that environment. | counted loops, one-armed conditionals, sequencing and data-dependent `while`, nested to any depth (`IsCoveredSU`), when `transU` succeeds and `semU` returns at that fuel | [`transU_denote`](CatCrypt/Crypto/SecureCompilation/Dialects/TranslateDialectUnifiedDenote.lean) |
| Lowering a program of the SSA IR to the Jasmin dialect preserves the value it computes. | every program the lowering accepts | [`cryptoDialectToJasminCom_denote_eq'`](CatCrypt/Crypto/SecureCompilation/VIR/DialectToJasminComCorrect.lean) |
| From LowCT to the Jasmin dialect, the compiled program returns the value that the machine-word semantics `semScalar` of the source leaves in one tracked output variable. | straight-line word code, counted loops and conditionals (`IsCoveredSCtl`) that the translation and the lowering both accept, on entry states where `semScalar` returns | [`rustToJasminCom_endToEnd_unconditional`](CatCrypt/Crypto/SecureCompilation/VIR/CompilerCorrectnessExtracted.lean) |
| The instruction block selected for a Jasmin-dialect program, run from registers holding the inputs, leaves the program's value in the result register, on x86-64, AArch64 and RV64. | straight-line programs over 64-bit registers whose operations are add, sub, mul, and, or, xor, high multiply, immediate shifts and constants (`ComOK`); on x86-64, with immediate shift amounts below `2^64` | [`com_x86_e2e`](CatCrypt/Crypto/SecureCompilation/ScalarLinX86Demo.lean), [`com_arm_e2e`](CatCrypt/Crypto/SecureCompilation/ScalarLinNeutralDemo.lean), [`com_riscv_e2e`](CatCrypt/Crypto/SecureCompilation/MultiBackendDemo.lean) |
| Every halting bounds-checked run of a body from counter `0` is matched by a halting run of its register-allocated form from the same state; the end states agree on the output registers, the arrays and the word memory. | pairs of x86 linear bodies that the checker `ownedCheckMC` accepts | [`ownedCheckMC_sound`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedLprogTVChecked.lean) |
| An emitted loop, run in the linear machine model with memory, leaves the value of the source loop in its accumulator register, when the machine loop halts and its trip count equals the value of the source guard. | data-dependent countdown loops whose guard register is the counter and whose update body is straight-line code in the stack-memory fragment `ScalarMemN` | [`whileMem_export_faithful_comL_uncond`](CatCrypt/Crypto/SecureCompilation/VIR/JasminLsemMemSourceTieWhileUncond.lean) |
| The bytes that the encoder writes for a block decode to the block under the register naming of the allocation, instruction by instruction, with no byte left over. | x86-64 blocks of the instruction forms accepted by `blockCovered` and `mulxRdxOk` | [`roundtrip_block`](CatCrypt/Crypto/SecureCompilation/X86Backend/SailX86BlockRoundtrip.lean) |
| Two runs of a decoded program from index `0`, from states that agree on the public set and with steps that respect the frame separation, have equal leakage traces. | decoded x86-64 programs that the checker `bytesCTCheck` accepts; it accepts the decoded `mpn_mul_1` node and the decoded bytes of `fe25519_add` | [`bytesCTCheck_sound`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodedCT.lean), [`mul1Node_bytesCT`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodedCTKernels.lean), [`feAddFramed_bytesCT`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodedCTKernels.lean) |
| Two runs from states that agree on the public registers leak the same trace of branch events and memory addresses. The statement is about a model of structured control flow; no emitted branch is covered. | conditionals with public guards and loops with literal trip counts, over straight-line blocks whose index registers are public and which write no public register (`CFControlled`) | [`owned_ct_control_flow`](CatCrypt/Crypto/SecureCompilation/X86Backend/MachineConstantTime.lean) |
| A program accepted by the source constant-time analysis, run from two states that agree on public data, ends in states that agree on public data. | programs the analysis `cmdCT` accepts, under `LeafCTAssumption` and `CMOVInvariant` | [`cmdCT_sound`](CatCrypt/Crypto/Jasmin/LowCTCTAnalysis.lean) |
| The encoding of the sum of two elements of `ZMod 251` is the content of the result register after the compiled program runs from registers holding the encoded operands, on AArch64 and RV64. | the relationally compiled field addition `addMod251RealizedKernel` | [`addMod251_source_eq_arm`](CatCrypt/Crypto/SecureCompilation/RelationalFrontMachine.lean), [`addMod251_source_eq_riscv`](CatCrypt/Crypto/SecureCompilation/RelationalFrontMachine.lean) |
| The Rust text printed for a Lean function, as the hax frontend reads it back, evaluates under `evalImp` to the encoding of the function's value, from some fuel on. | the Edwards addition `edwardsAddLean` over any carrier whose encoding holds no control-flow value, with the leaf calls interpreted by the table `edBi` | [`edwardsAdd_endToEnd`](CatCrypt/Hax/ReifyImpEndToEnd.lean) |
| When the reading of a hax literal in the Rust monad returns a value and an environment, the run of the literal under hax-lean's `denote'` returns their encodings, from some fuel on. | every `ImpExpr` literal, for a call interpretation that agrees with the builtin table (`AppOk`) | [`toRustMS_sim`](HaxAscent/RustSemantics/ToRustMS.lean) |
| Total Hoare triples of the reading, with the postcondition that the returned value encodes `f a`, give the function correspondence `FnCorres` between the literal and the Lean function `f`. | every `ImpExpr` literal whose entry environment encodes the environment of the reading, under `AppOk` | [`fnCorres_of_toRustMS_triple`](HaxAscent/RustSemantics/TripleToFnCorres.lean) |
| The shipped x86-64 bytes of the Edwards point addition decode to a block that computes the addition formula. | the imported `ed25519_point_add` block, on disjoint cells and inputs below `2^255 − 19` | [`paShippedBytes_correct`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519PointAddBytes.lean) |
| The imported x86-64 blocks of the Ed25519 implementation store the values of their specifications: the mixed addition; the input raised to `2^255 − 21` modulo `2^255 − 19`; the encoding `y + 2^255 · (x mod 2)` of the affine point; `x mod L`; `(a · b + c) mod L`. | `ed25519_madd`, `ed25519_invert`, `ed25519_compress`, `ed25519_sc_reduce`, `ed25519_sc_muladd`, each under its separation hypotheses between buffers and stack frame; `madd` and `invert` on inputs below `2^255 − 19` and `compress` on a third coordinate below it; `madd` and `compress` for callees that meet their specifications (`MaddCallees`, `CompressCallees`) | [`maddShipped_correct_cross`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519MaddShippedProof.lean), [`invertShipped_correct`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519InvertShippedProof.lean), [`compressShipped_correct_addr`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519CompressShippedProof.lean), [`scReduceShipped_correct_addr`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519ScReduceShippedProof.lean), [`scMuladdShipped_correct_addr`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519ScMuladdShippedProof.lean) |
| With `%rsi`, `%rdx` and `%rdi` pointing at `x`, `y` and the output, and `x · y ≤ 2^384 · p384`, the six output words are below `p384` and equal `x · y · (2^384)⁻¹` in `ZMod p384`. The three buffers may overlap. | s2n-bignum's hand-written `bignum_montmul_p384` as imported, 264 instructions, on the address machine `runBlockA`; the form for inputs below `p384` is `s2nMontmulP384_correct_reduced` | [`s2nMontmulP384_correct_addr`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontmulP384Addr.lean), [`s2nMontmulP384_correct_reduced`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/CertifyThirdPartyDemo.lean) |
| The package's encoding of that block decodes to 264 instructions that store the same Montgomery product at `%rdi`, under the same bound on `x · y`. | the encoded bytes of `bignum_montmul_p384`, on the name-keyed machine `runBlock` | [`s2nMontmulP384Bytes_correct`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontmulP384Bytes.lean) |
| With `%rsi`, `%rdx` and `%rdi` pointing at `x`, `y` and the output, and every input limb below `2^54`, the five radix-`2^51` output words have a value congruent to the product of the values at `x` and `y` modulo `2^255 − 19` (fiat-crypto's `mul_correct`). The output may overlap either input. | CryptOpt's `fiat_curve25519_carry_mul` as imported, 167 instructions, on the address machine `runBlockA`; the two inputs and the 136-byte frame below `%rsp − 128` are pairwise apart, and the output is apart from the frame | [`carryMul_correct_addr`](CatCrypt/Crypto/SecureCompilation/Ascent/CryptOptAddr.lean) |
| With `%rsi` and `%rdi` pointing at `x` and the output, the four output words have a value congruent to the square of the value at `x` modulo `2^255 − 19` (fiat-crypto's `sqr_correct`). | CryptOpt's `fiat_curve25519_solinas_square` as imported, 99 instructions, on `runBlockA`; the input, the output and the 48 bytes from `%rsp − 128` are pairwise apart | [`solinasSquare_correct_addr`](CatCrypt/Crypto/SecureCompilation/Ascent/CryptOptAddr.lean) |
| A body that corresponds to a specification at the fuelled x86 interpreter, placed after a label inside a larger program and followed by a return, satisfies the procedure specification of that label at the instruction set with calls. | bodies that contain no call or return and name `RSP` in no instruction (two Boolean checks), with labels fresh for the prefix and entry states at counter `0` | [`x86_procSpec_of_image_judgement`](CatCrypt/Crypto/SecureCompilation/Ascent/CorresIsaStackFrame.lean) |
| The x86 step of an instruction other than a control instruction commutes with a shift of the program counter and does not read the program; the branch condition does not read the counter. | every function name, prefix, body and suffix | [`x86_stepRelocates`](CatCrypt/Crypto/SecureCompilation/Ascent/CorresIsaRelocX86.lean) |
| ML-KEM (FIPS 203): decompression after compression is within `errorBound d` of the input in the centred distance modulo `q`; the inverse transform inverts the transform; the product in `Rq_kem` is the inverse transform of the base multiplication of the transforms. | compression parameters `1 ≤ d ≤ 12` over `q = 3329`; every coefficient vector; every pair of ring elements | [`decompress_compress_centered`](CatCrypt/Crypto/MLKEM/Compress.lean), [`invNttKem_nttKem`](CatCrypt/Crypto/MLKEM/Spec/Ntt.lean), [`rqKem_mul_eq_invNttKem`](CatCrypt/Crypto/MLKEM/Spec/Ntt.lean) |
| ML-DSA (FIPS 204): the public key, secret key and signature of ML-DSA-65 have 1952, 4032 and 3309 bytes. | the parameter set `MLDSA65Params`; the same module states the sizes of ML-DSA-44 and ML-DSA-87 | [`mldsa65_pk_size`](CatCrypt/Crypto/MLDSA/ConcreteParams.lean), [`mldsa65_sk_size`](CatCrypt/Crypto/MLDSA/ConcreteParams.lean), [`mldsa65_sig_size`](CatCrypt/Crypto/MLDSA/ConcreteParams.lean) |
| ML-DSA: `useHint` applied to the hint that `makeHint` produces returns the high bits of `r + z` modulo `q`. | `0 ≤ r < q`, `−γ2 ≤ z ≤ γ2`, and `γ2` one of the two standard values (`IsGamma2`) | [`useHint_makeHint`](CatCrypt/Crypto/MLDSA/Spec/Rounding.lean) |
| The Montgomery model of the P-256 field satisfies the law of `pow` (the power to the exponent that the little-endian 64-bit limbs encode) and the laws of `from_bytes` and `to_bytes` with encodings of 32 bytes. | valid representations of `fp256MontCtModel`, exponents and byte arrays given as digit arrays | [`fp256MontCtModel_powLaws`](CatCrypt/Crypto/PrimeIR/Proof/Fp256MontBytesPow.lean), [`fp256MontCtModel_byteLaws`](CatCrypt/Crypto/PrimeIR/Proof/Fp256MontBytesPow.lean) |

[HEADLINES.md](HEADLINES.md) states each compiler headline with its hypotheses, and
[NAVIGATION.md](NAVIGATION.md) locates every subsystem and its main theorem.

### Functional correctness

- Dialect lowering. When the lowering from the SSA IR to the Jasmin dialect
  succeeds, the lowered program denotes the transport of the source denotation
  ([`cryptoDialectToJasminCom_denote_eq'`](CatCrypt/Crypto/SecureCompilation/VIR/DialectToJasminComCorrect.lean)). [`compileVia_comp_correct`](CatCrypt/Crypto/SecureCompilation/VIR/LoweringDataComp.lean)
  composes two dialect lowerings and states the result for the Jasmin-IR evaluator
  [`runProg`](CatCrypt/Crypto/SecureCompilation/VIR/JasminPrintSemCorrect.lean), given per-operation transport hypotheses, leaf agreement ([`LeafAgrees`](CatCrypt/Crypto/SecureCompilation/VIR/JasminPrintSemCorrect.lean))
  and a straight-line lowered program. [`fieldToJasminWord_denote`](CatCrypt/Crypto/SecureCompilation/Algebraic/FieldToJasminWord.lean)
  lowers [`fieldDialect`](CatCrypt/Crypto/SecureCompilation/VIR/FieldDialect.lean) programs over a single-word prime field to the Jasmin
  dialect with preserved denotation.
- Rust front. [`rustToJasminCom_endToEnd_unconditional`](CatCrypt/Crypto/SecureCompilation/VIR/CompilerCorrectnessExtracted.lean) equates the Jasmin value with
  the value that the machine-word semantics [`semScalar`](CatCrypt/Crypto/SecureCompilation/Dialects/TranslateDialectScalarDenote.lean) leaves in the tracked output,
  and asserts that a post-state related to the LowCT execution relation [`RustExec`](CatCrypt/Crypto/Jasmin/LowCTExec.lean)
  exists. [`rustToJasminCom_endToEnd_rustexec_adeq_topLevel`](CatCrypt/Crypto/SecureCompilation/Dialects/RustExecSemScalarBridge.lean)
  equates the Jasmin value with the `RustExec` output word on [`IsCoveredAdeq`](CatCrypt/Crypto/SecureCompilation/Dialects/RustExecSemScalarBridge.lean), for
  inputs in `u64` range. [`transU_to_jasminCom_endToEnd`](CatCrypt/Crypto/SecureCompilation/VIR/RustToJasminComWhile.lean)
  extends the statement to data-dependent `while` loops over the fuel-bounded
  semantics [`semU`](CatCrypt/Crypto/SecureCompilation/Dialects/TranslateDialectUnifiedDenote.lean). The translation from hax-lean's AST to LowCT has its own
  simulation theorems ([`haxToLowCT_simulates_program`](CatCrypt/Crypto/Hax/HaxToLowCTSim_Program.lean) and
  siblings, [CatCrypt/Crypto/Hax/AGENTS.md](CatCrypt/Crypto/Hax/AGENTS.md)).
- Machine code. For a straight-line [`Com`](CatCrypt/Crypto/SecureCompilation/VIR/Core.lean) over [`ComOK`](CatCrypt/Crypto/SecureCompilation/ScalarLinDeBruijn.lean) (64-bit add, sub, mul, and,
  or, xor, widening high multiply, immediate shifts, constants), the block that the
  scalar instruction selection produces, run from registers holding the inputs,
  leaves `Com.denote` in the result register ([`com_x86_e2e`](CatCrypt/Crypto/SecureCompilation/ScalarLinX86Demo.lean), [`com_arm_e2e`](CatCrypt/Crypto/SecureCompilation/ScalarLinNeutralDemo.lean), [`com_riscv_e2e`](CatCrypt/Crypto/SecureCompilation/MultiBackendDemo.lean)). [`comToArmLsem_correct`](CatCrypt/Crypto/SecureCompilation/ARMBackend/ComToArmLsem.lean)
  and [`comToRiscvLsem_correct`](CatCrypt/Crypto/SecureCompilation/RISCVBackend/ComToRiscvLsem.lean) restate the result on the
  base arithmetic-logic subset over the [`runBBlock`](CatCrypt/Crypto/SecureCompilation/ARMBackend/ArmModel.lean) and RV64 machine models.
  [`riscvStep64_sail_grounded`](CatCrypt/Crypto/SecureCompilation/RISCVBackend/ComToRiscvLsem.lean) equates each base RV64
  instruction step with an `execute_RTYPE` clause copied from
  [sail-riscv-lean](https://github.com/opencompl/sail-riscv-lean) into
  [SailRiscv64Refinement](CatCrypt/Crypto/SecureCompilation/RISCVBackend/SailRiscv64Refinement.lean). The encoders of both backends carry
  decode round trips against decode field splits transcribed from the Sail decode
  clauses.
- Emitted loops. The `VIR.JasminLsemMem*` theorems run the emitted counter loops,
  fill loops, data-dependent loops, loop nests and nested calls in the linear machine
  model and equate the result with the source denotation ([`ComL.denote`](CatCrypt/Crypto/SecureCompilation/VIR/JasminLprogExport/ExportLoops.lean));
  [HEADLINES.md](HEADLINES.md) lists them.
- Ascent. The ascent proves that a program at one of the compiler's low levels (a
  LowCT command, an x86 or RV64 instruction list, x86 bytes) computes a Lean
  specification ([ASCENT.md](ASCENT.md)). [`paShippedBytes_correct`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Ed25519PointAddBytes.lean) shows that the
  encoded bytes of the imported `ed25519_point_add` block decode to a block that
  computes Edwards addition on inputs below `2^255 − 19`. For code written outside the
  project, [`s2nMontmulP384_correct_addr`](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontmulP384Addr.lean) states the
  Montgomery product of s2n-bignum's P-384 multiplication, and
  [CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md) describes the certification path.

### Constant time

- x86-64, straight-line. [`toLprogPhysAbi_gather_constant_time`](CatCrypt/Crypto/SecureCompilation/X86Backend/AllocCTPreservation.lean):
  an exported function body with direct addressing that gathers to an x86 instruction block leaks the same
  machine trace (branch decisions and memory addresses) from any two states.
  [`owned_lsem_correct_and_robust_straightline`](CatCrypt/Crypto/SecureCompilation/VIR/JasminLsemRobust.lean) pairs functional
  correctness of the linearizer with a leakage trace that reads no register value; the
  trace equality holds for every program of the fragment.
- x86-64, structured control flow, on a model IR. [`owned_ct_control_flow`](CatCrypt/Crypto/SecureCompilation/X86Backend/MachineConstantTime.lean): a block of
  the model IR [`OwnedCF`](CatCrypt/Crypto/SecureCompilation/X86Backend/MachineConstantTime.lean) built from conditionals with public guards and loops with
  literal trip counts leaks the same trace from any two states that agree on the public
  registers. `OwnedCF` is not tied to the emitted [`Lcmd`](CatCrypt/Crypto/SecureCompilation/VIR/JasminLprogExport/Types.lean) or to bytes, so no emitted
  branch is covered.
- x86-64, decoded bytes. [`bytesCTCheck_sound`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodedCT.lean): for a decoded
  program that the checker `bytesCTCheck` accepts, two runs from index `0` whose steps
  respect the frame separation, from states that agree on the public set, have equal
  leakage traces. [`mul1Node_bytesCT`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodedCTKernels.lean) and
  [`feAddFramed_bytesCT`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodedCTKernels.lean) show that the checker accepts the
  decoded `mpn_mul_1` node and the decoded bytes of `fe25519_add`.
- Source. [`cmdCT_sound`](CatCrypt/Crypto/Jasmin/LowCTCTAnalysis.lean): a program accepted by the analysis [`cmdCT`](CatCrypt/Crypto/Jasmin/LowCTCTAnalysis.lean), run from two
  public-equivalent states, reaches public-equivalent states, under the per-leaf
  assumption [`LeafCTAssumption`](CatCrypt/Crypto/Jasmin/LowCTCTAnalysis.lean) and the hypothesis [`CMOVInvariant`](CatCrypt/Crypto/Jasmin/LowCTCTAnalysis.lean) (which holds for a
  select only when its two sources are the same slot; `cmdCT` admits no computation
  on secrets). `cmdCT` accepts a
  data-dependent loop exactly when its guard is public
  ([`cmdCT_RWhileNz_iff`](CatCrypt/Crypto/SecureCompilation/LowCTVartimeLeak.lean)); for example, it accepts the
  early-terminating modular inverse of RSA verification under an all-public level
  table and rejects it under a secret guard ([`vartimeInvert_public_only`](CatCrypt/Crypto/SecureCompilation/VartimeBignumInverse.lean)).

### Security ties

hax lets one Rust source serve as compiler input and as the model for computational
security proofs in the wider CatCrypt development, following
[The Last Yard](https://eprint.iacr.org/2023/185). The `*SecurityTie` modules equate
a dependency record built from the [`Com`](CatCrypt/Crypto/SecureCompilation/VIR/Core.lean) denotations of compiled kernels with the
record the security layer reasons over ([`toRoundDeps_eq_spec`](CatCrypt/Crypto/SecureCompilation/CompileFromHaxSecurityTie.lean)
for the SHA-256 round functions), and [`tie_transfer`](CatCrypt/Crypto/SecureCompilation/CompileFromHaxSecurityTie.lean)
carries any property of that record to the compiled kernels at the `Com` denotation.

## Architecture

A cryptographic implementation has three parts: orchestration (protocol and control
flow), algebra (field, curve and polynomial arithmetic) and leaves (low-level
primitives). Each enters at its own level.

```mermaid
flowchart TD
    RUST["Rust source"] -->|hax| LOWCT["LowCT"]
    SPEC["Lean specification"] -->|relational front| JAS
    LOWCT --> IR["SSA IR (catCryptDialect)"]
    ALG["PrimeIR algebra dialects"] -->|fieldDialect, single-word fields| JAS
    IR --> JAS["Jasmin dialect"]
    JAS --> X86["x86-64"]
    JAS --> ARM["AArch64"]
    JAS --> RV["RISC-V"]
```

- LowCT is the low-level constant-time command language
  ([LowCT.lean](CatCrypt/Crypto/Jasmin/LowCT.lean)), ported from AUCurves. hax-lean's AST
  translates to it, and Lean terms elaborate to it through [`reifyLowCT%`](CatCrypt/Crypto/Jasmin/LowCTReflect.lean).
- [`Com`](CatCrypt/Crypto/SecureCompilation/VIR/Core.lean) is the typed SSA framework, after
  [lean-mlir](https://github.com/opencompl/lean-mlir) through the Veir library. A
  dialect is a set of typed ops with a Lean denotation.
- The SSA IR is the dialect [`catCryptDialect`](CatCrypt/Crypto/SecureCompilation/VIR/CatCryptDialect.lean) over `Com`, the target of the LowCT
  front.
- The Jasmin dialect ([`jasminDialect`](CatCrypt/Crypto/SecureCompilation/VIR/JasminDialect.lean)) is the word-level target of every
  lowering. It reaches machine code through CatCrypt's own backend (the owned
  backend, which began as a port of the Jasmin compiler) or, as printed Jasmin text,
  through `jasminc`. Hand-written Jasmin leaves import through the same backend.
- The PrimeIR dialects ([`fieldDialect`](CatCrypt/Crypto/SecureCompilation/VIR/FieldDialect.lean), [`modArithDialect`](CatCrypt/Crypto/SecureCompilation/VIR/ModArithDialect.lean), [`polyDialect`](CatCrypt/Crypto/SecureCompilation/VIR/PolyDialect.lean),
  [`ecDialect`](CatCrypt/Crypto/SecureCompilation/VIR/EllipticCurveDialect.lean)) follow the MLIR dialects of
  [PrimeIR](https://github.com/fractalyze/prime-ir). Rust reaches them through the
  `primeir-hax` crate, whose traits name each operation
  ([CompileFromHaxPrimeIrFront](CatCrypt/Crypto/SecureCompilation/CompileFromHaxPrimeIrFront.lean)). `fieldDialect` lowers to the Jasmin dialect on
  single-word prime fields; the others carry denotations.
  [DIALECTS.md](CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md) gives the
  lowering graph.
- The relational front ([RelationalFront](CatCrypt/Crypto/SecureCompilation/RelationalFront.lean)) takes a Lean
  operation with an encoding and a proved commuting square to a Jasmin-dialect program
  whose denotation is the encoded operation ([`RealizedKernel`](CatCrypt/Crypto/SecureCompilation/RelationalFront.lean)).

The covered source is the control spine of cryptographic code: straight-line leaf
calls, counted and public-condition loops, data-dependent loops, branchless select,
public-index array access, tuples, byte slices, and fixed-width and widening integer
arithmetic. SIMD intrinsics enter through an explicit-SIMD vector front with its own
semantics ([`translateDialectControlV_denote`](CatCrypt/Crypto/SecureCompilation/Dialects/TranslateDialectVsimdDenote.lean)).

## First example

After the setup in [BUILDING.md](BUILDING.md#first-time-setup):

```bash
lake build CatCrypt.Crypto.SecureCompilation.CompilerHelloDemo
lake env lean CatCrypt/Crypto/SecureCompilation/CompilerHelloDemo.lean
```

The second command runs [CompilerHelloDemo](CatCrypt/Crypto/SecureCompilation/CompilerHelloDemo.lean). It compiles the routine
`fn f(a: u64, b: u64) -> u64 { let t = a.wrapping_mul(b); t.wrapping_add(a) }`, given
as a term of the front's input type, and prints AArch64 assembly.
[`srcArm_correct`](CatCrypt/Crypto/SecureCompilation/CompilerHelloDemo.lean) proves that the compiled block, run from registers
holding the inputs, leaves the denotation of the compiled program in the result
register; it is an instance of [`com_arm_e2e`](CatCrypt/Crypto/SecureCompilation/ScalarLinNeutralDemo.lean).
[GETTING_STARTED.md](GETTING_STARTED.md) explains the run.

## Where to start

- [CompilerHelloDemo](CatCrypt/Crypto/SecureCompilation/CompilerHelloDemo.lean): a two-line routine compiled to
  AArch64 with its correctness theorem; [GETTING_STARTED.md](GETTING_STARTED.md) walks
  through it.
- [Ascent/Demos/Decide.lean](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/Decide.lean): a kernel written in the
  `lowct%` notation lifted to its specification over `ZMod 2^64` by one tactic
  ([ASCENT.md](ASCENT.md#quick-start)).
- [CertifyThirdPartyDemo](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/CertifyThirdPartyDemo.lean): the statement a
  caller uses for s2n-bignum's P-384 Montgomery multiplication, with the decoding of
  its bytes ([CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md)).
- [HEADLINES.md](HEADLINES.md) and [NAVIGATION.md](NAVIGATION.md): each headline theorem
  with its hypotheses, and the location of every subsystem.
- The table below indexes the remaining documents.

## Documentation

| Document | Contents |
|---|---|
| [GETTING_STARTED.md](GETTING_STARTED.md) | the first example |
| [DEMO.md](DEMO.md), [EXAMPLES.md](EXAMPLES.md) | the two fronts on worked examples; buildable example modules |
| [HEADLINES.md](HEADLINES.md) | the headline theorems with their hypotheses |
| [NAVIGATION.md](NAVIGATION.md) | where each subsystem lives, and how to find a theorem |
| [CAPABILITIES.md](CAPABILITIES.md) | each primitive with its modules, theorems and provenance class |
| [CORRECTNESS.md](CORRECTNESS.md) | how correctness is proved: descent, ascent, transfer, and how they compose |
| [ASCENT.md](ASCENT.md) | the ascent from code to Lean specifications |
| [CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md) | certifying existing machine code: the hax reference, the differential oracle and the ascent |
| [HAX_RUST.md](HAX_RUST.md) | Lean to Rust and back through hax |
| [FIELD_TEMPLATES_VS_RUST.md](FIELD_TEMPLATES_VS_RUST.md) | field arithmetic: what the Rust ecosystem does and what the templates add |
| [bench.md](bench.md) | performance ratios against production implementations |
| [BUILDING.md](BUILDING.md) | dependencies, builds, checks, axiom audit, documentation generation |
| [docs/CompilerManual.lean](docs/CompilerManual.lean) | the [Verso](https://github.com/leanprover/verso) manual |
| [CatCrypt/Crypto/SecureCompilation/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md) | the compiler's source directories, with per-directory indexes |

The [CatCrypt paper](https://eprint.iacr.org/2026/604) describes the full system;
[CITATION.cff](CITATION.cff) carries the citation metadata.
