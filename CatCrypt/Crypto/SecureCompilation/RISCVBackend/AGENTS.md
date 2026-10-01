# `RISCVBackend/`: directory index

This directory holds the RV64 backend: a 32-bit-word model (`RState`, `RInst`, the
`*W` instructions used by ChaCha20 and SHA-256), a 64-bit model without a carry flag
(`RState64`, `RInst64`, carries synthesised with `SLTU`), an RVV vector model at a
fixed configuration (VLEN 128, SEW 32; and SEW 16 for `vmulh`), lowerings, GAS
printers, byte encoders with decode round trips, an ELF64 object writer, a register
allocator instance, the RV64 instance of the `ScalarLin` waist with its whole-`Com`
theorems, per-instruction refinements against excerpts of the sail-riscv Lean
output, and kernels lowered through the models. The Sail clauses and the decoder
field splits are copied into the modules by hand; neither sail-riscv nor
sail-riscv-lean is a dependency of the package.

Names below are relative to `CatCrypt.Crypto.SecureCompilation.RISCVBackend`. Most
modules declare into `RISCVBackend.<ModuleName>`. Exceptions: `RiscvModel.lean`,
`RiscvModel64.lean`, `RiscvLowering.lean`, `RiscvLowering64.lean`,
`RiscvAsmPrinter.lean` and `RiscvAsmPrinter64.lean` declare into `RISCVBackend`;
`RvvModel.lean`, `RvvLowering.lean` and `RvvAsmPrinter.lean` into `Rvv`;
`RvvEncoder.lean` into `Rvv.RvvEncoder`; `SailRvvDecoder.lean` into
`Rvv.SailRvvDecoder`; `SailRiscv32Refinement.lean`, `SailRiscv64Refinement.lean` and
`SailRiscvBranchRefinement.lean` into `SailRiscv32Ref`, `SailRiscv64Ref` and
`SailRiscvBranchRef`.

## Models, lowering and printers

| Module | Contents |
|---|---|
| `RiscvModel.lean` | `RState`, `evalRInst`, `runRBlock`; `runBoundedLoopR` with `runBoundedLoopR_eq_runRBlock_unroll` |
| `RiscvLowering.lean` | `ROp → List RInst` (rotates as three-instruction macros, or `RORIW` under `lowerRBlockZbb`); `riscvBlock_lowering_denote`, `riscvBlockZbb_lowering_denote`; `rotl_run_denote`, `rotr_run_denote`, `roriw_run_denote` under freshness hypotheses on the temporary; `qr_rfc_kat` |
| `RiscvModel64.lean`, `RiscvLowering64.lean` | `RState64`, `evalRInst64`, `runRBlock64`; `sltu_add_carry`, `sltu_sub_borrow`; carry, borrow and mask-select macros with `riscvBlock64_lowering_denote` and `native_decide` KATs (`addcc_carry_kat`, `csub_cond1_kat`, ...) |
| `RvvModel.lean`, `RvvLowering.lean`, `RvvAsmPrinter.lean` | `VState`, `evalVInst`, `runVBlock`; the 8×i16 view `VState8x16` with `evalVInst8x16`; `rvvBlock_lowering_denote`; GAS RVV text |
| `RiscvAsmPrinter.lean`, `RiscvAsmPrinter64.lean` | GAS text (`renderRInst`, `renderRInst64`) and linear-scan allocators (`allocGp`, pool `gpPool64`) |
| `RiscvControlFlow.lean` | `loopRBlock`, the GAS lines of a counter loop with a `BNE` back-edge, `loopRBlock_length`; the loop instruction `RLoop` (rendered by `loopRBlock`) with the fuel-bounded execution `runRLoop`, and `looped_eq_unrolled_denote`: a body that decrements the counter runs to the unrolled block |

## Encoders, round trips and objects

- `RiscvEncoder.lean` (`encodeWord`, `encodeRInst`, `encodeBccWord`),
  `RiscvEncoder64.lean` (`encodeWord64`, which returns `none` for `li`),
  `RvvEncoder.lean` (`encodeWord`, `encodeWord8x16`). Operand names are encoded
  directly; there is no allocation argument.
- `SailRiscvDecoder.lean`: `roundtrip_RInst` (`riscvDecode (encodeWord i) = some i`
  when every register name of `i` is in `emittedRegs` and shift counts are below 32),
  `roundtrip_roriw`, and `roundtrip_bcc` for branches (the offset is recovered with
  bit 0 cleared).
- `SailRiscvDecoder64.lean`: `roundtrip_RInst64` for every `RInst64` other than `li`,
  with register names in `emittedRegs64` (`emittedRegs` and `s0..s11`, which covers
  `gpPool64`) and shifts below 64.
- `RiscvBytes64.lean`: `MInst64` (an `RInst64` or `ADDI`), `runM64`; `liSeq`/`expandLi`
  load each `li` constant with `addi`/`slli` (`runM64_expandLi`); `decodeMStream64_encode`
  decodes a block from its little-endian bytes (`encodeMBlock64`); `runM64_phys`
  combines the two with a renaming checked by `RiscvRename64.renGo`.
- `RiscvRename64.lean`: `renameRBlock64` and the liveness checker `renGo`;
  `runRBlock64_rename` preserves the live-out values when `renGo` accepts, so registers
  can be reused once their value is dead. `allocLive64` is an unproved linear scan whose
  output `renGo` checks.
- `SailRvvDecoder.lean`: `roundtrip_rvv` (register names in `vPool`, shifts below 32)
  and `roundtrip_rvv8x16` for `vmulh`.
- `EncoderDiffAudit.lean`: `example`s pinning words with `zero` in each operand slot
  to recorded assembler output.
- `RiscvElfObject.lean`: `buildElfObject` and the multi-leaf variants, the ABI
  scaffolding words, and length and symbol lemmas (`symCount_eq`). The scaffolding
  words (`encLd`, `encSd`, `encJal`, ...) are pinned to assembler output and have no
  decoder case.

## Sail refinements

| Module | Statement | Hypotheses |
|---|---|---|
| `SailRiscv64Refinement.lean` | `rtype_add`, `rtype_sub`, `rtype_and`, `rtype_or`, `rtype_xor`, `rtype_sltu`, `rtype_mul`, `rtype_mulhu`, `itype_mv`, `shiftiop_slli`, `shiftiop_srli`: the value the excerpted clause writes to `rd` equals the `RiscvModel64` op on the operands | `rd.toNat ≠ 0`; shifts below 64 |
| `SailRiscv32Refinement.lean` | `addw_lo32`, ..., `roriw_lo32`, `mv_lo32`: the low 32 bits of the written value equal the `RiscvModel` op on the low 32 bits of the operands | `rd.toNat ≠ 0`; shifts below 32 |
| `SailRiscvBranchRefinement.lean` | `bcmp_taken_eq`: `bcmpTaken c a b = btypeTaken (toBop c) a b` | none; no module imports it |

The Sail state is a flat `BitVec 5 → BitVec 64` register file with a thin state
monad. These theorems are per instruction; none is stated about a block.

## From `Com` to RV64

- `RegToRiscv.lean`: `rvTarget`, the RV64 `ScalarTarget`; `regToROp_denote`
  (`runRBlock64 s (lowerRBlock64 (regToROp p)) = rvTarget.denote p s`). The
  whole-`Com` composition `com_riscv_e2e` is in `../MultiBackendDemo.lean`.
- `ComToRiscvLsem.lean`: `IsBaseAlu`, `ComBaseAlu`, `RegAlign`,
  `riscvStep64_sail_grounded`, `comToRiscvLsem_correct`, `RiscvBaseAluGrounded`,
  `riscvBaseAluModel`.
- `ComToRiscvMulLsem.lean`: the same for base ALU plus `MUL` and `MULHU`
  (`IsArithMul`, `ComArithMul`, `sailClause`, `riscvStepArithMul_sail_grounded`,
  `comToRiscvLsem_correct_mul`, `riscvArithMulModel`). No module imports it.
- `RiscvRegAlloc.lean`: `MachineModel`, `RegMachine` and `MemMachine` instances for
  the 32-bit `RInst`; `renameRBlock_runRBlock`, `riscv_spillStore_establishes`,
  `riscv_reload_sandwich`, `linearScan_slotsSeparated_rv64`, obtained from
  `../../Optimizer/GenericRegAlloc.lean`. There is no allocation theorem
  for `RInst64`.

Kernels: `RiscvBignumKernel.lean` (`bignum_add_p256`), `RiscvMontMulKernel.lean`
(4×4→8 schoolbook), `RiscvSha256Kernel.lean` (SHA-256 compression, base and `Zbb`
lowerings), `RiscvX25519FieldKernel.lean` (field operations, `cswap`, ladder step,
`runBoundedLoopR64`). The `*_lowering_correct*` theorems instantiate the block
lowering theorems; values are checked by `native_decide` on worked vectors
(`addp256_kat_full64`, `mul48_kat_allones64`, `sha256_abc_kat`, `sha256_abc_kat_zbb`,
`feMul_kat_full`). `ladderStep_composition` states only that the ladder-step block
is the concatenation of the field-operation blocks; its value is not checked in Lean.

## Entry-point theorems

| Result | Declaration | Fragment and hypotheses | File |
|---|---|---|---|
| Whole-`Com` value preservation | `ComToRiscvLsem.comToRiscvLsem_correct` | `ComBaseAlu com`, `AllReg64 Γ`, `s.regs = envOf Γ.length V`; the result register holds `Com.denote com V` and every executed instruction satisfies `IsBaseAlu` | `ComToRiscvLsem.lean` |
| The same with `MUL`, `MULHU` | `ComToRiscvMulLsem.comToRiscvLsem_correct_mul` | `ComArithMul com`, same state hypotheses; membership conjunct `IsArithMul` | `ComToRiscvMulLsem.lean` |
| Per-step Sail relation | `ComToRiscvLsem.riscvStep64_sail_grounded` | `IsBaseAlu i`, destination not `zero`/`x0`, `RegAlign s rf nm`, `(nm (rinstD i)).toNat ≠ 0` | `ComToRiscvLsem.lean` |
| Scalar waist | `RegToRiscv.regToROp_denote` | every `RegProg` and `RState64` | `RegToRiscv.lean` |
| Block lowering | `riscvBlock_lowering_denote`, `riscvBlock64_lowering_denote`, `Rvv.rvvBlock_lowering_denote` | all blocks and states | `RiscvLowering.lean`, `RiscvLowering64.lean`, `RvvLowering.lean` |
| Decode round trip | `SailRiscvDecoder64.roundtrip_RInst64` | not `li`, register names in `emittedRegs64`, shifts below 64 | `SailRiscvDecoder64.lean` |
| Block decode round trip | `RiscvBytes64.decodeMStream64_encode` | every instruction `MInstOK` | `RiscvBytes64.lean` |
| Renaming under liveness | `RiscvRename64.runRBlock64_rename` | `renGo ρ b L = some Lin`, states agree on `Lin` | `RiscvRename64.lean` |

## Ascent over RV64

The ascent relates RV64 blocks to abstract specifications through `CorresR`, the
correspondence over `runRBlock64` (`../Ascent/CorresRiscv.lean`). Each `RInst64`
instruction has a leaf (`corresR_add` … `corresR_slli`, `../Ascent/CorresRiscvLeaves.lean`),
and the tactics `corres_sym_rv` and `corres_solve_rv` (`../Ascent/CorresRiscvSolver.lean`)
compose them over a block. `corresR_of_refines` (`../Ascent/CorresDescentRiscv.lean`)
reads the descent theorem `com_riscv_e2e` as a `CorresR`. The demos are
`../Ascent/Demos/Riscv.lean` (`addCarry_ascends`, an add with carry-out) and
`../Ascent/Demos/LeanSourceRiscv.lean` (`add_descent_riscv`, a Lean function through
the descent).

The hand-written kernels are proved over their lowered blocks in
`../Ascent/Demos/RiscvAddP256Proof.lean` (`addp256_correct`) and
`../Ascent/Demos/RiscvFe25519AddSubProof.lean` (`feAdd_correct`, `feSub_correct`,
`feMul121666_correct`, `cswap_correct`). `../Ascent/Demos/RiscvBytesProof.lean` carries
each to the bytes of a physical block (`addp256Bytes_correct`, `feAddBytes_correct`, …):
the bytes decode to instructions that compute the same result, for every machine state,
with inputs in `a0..a7` and the result in `a0..a3` (`cswap` swaps `a0..a3` and
`a4..a7` in place).

The schoolbook multiply and the field multiply and square are proved in
`../Ascent/Demos/RiscvFe25519MulProof.lean` (`mul48_run`, `feMul_correct`,
`feSqr_correct`) and carried to bytes in `../Ascent/Demos/RiscvMulBytesProof.lean`
(`feMulBytes_correct`, `feSqrBytes_correct`, 1033 and 1037 instructions).
`../Ascent/Demos/RiscvX25519LadderStepProof.lean` proves that `ladderStepBlock` computes
`CatCrypt.Util.x25519DoubleAndAdd` (`ladderStep_correct`, for `z2, z3 ≤ 2·p25519`); it is
stated over `runRBlock64` with symbolic names, since its seventeen field elements need
more registers than RV64 has.

Descent output reaches the bytes through `../Ascent/DescentRiscvBytes.lean`:
`com_riscv_bytes` carries `com_riscv_e2e` through a renaming that `renGo` accepts and
`expandLi`, for any `ComOK` program. `../Ascent/Demos/LeanSourceRiscvBytes.lean`
instantiates it on `a + b`, `a - b` and the multiply-accumulate column
`fe25519MacColLoCom` (`addDescentBytes_correct`, `subDescentBytes_correct`,
`macColLoBytes_correct`).

## What is not proved

- `runM64` executes the decoded instructions with `evalRInst64`; that it agrees with
  the Sail model over a whole block is not proved (the Sail refinements are per
  instruction, for the written value). The bytes of `RiscvBytes64.encodeMBlock64` are
  not the ones `RiscvElfObject` or `as` produce: `encLi64` and `as` load constants with
  other sequences.

- The second conjunct of `comToRiscvLsem_correct` and `comToRiscvLsem_correct_mul` is
  membership in the instruction subset. The per-step Sail relation holds under its own
  hypotheses (`RegAlign`, nonzero register numbers), which these theorems do not
  discharge, and no theorem composes the per-step relation over a block.
- The decode round trips are not conjuncts of the whole-`Com` theorems, and no theorem
  maps the names of the compiled `RInst64` block into `emittedRegs`.
- No theorem relates the printers' text to a model. The `loopRBlock` lines are the
  rendering of an `RLoop`, whose execution `runRLoop` follows the label and `BNE`
  back-edge; `looped_eq_unrolled_denote` equates it with the unrolled block when the
  body decrements the counter. `ladder_loop_denote` is about `runBoundedLoopR64`,
  which takes the trip count as an argument.
- The correspondence between the in-file Sail excerpts and the sail-riscv-lean output
  is not checked in the package.

See [AGENTS.md](../AGENTS.md) for the compiler as a whole and
[CAPABILITIES.md](../../../../CAPABILITIES.md) for per-primitive status.
