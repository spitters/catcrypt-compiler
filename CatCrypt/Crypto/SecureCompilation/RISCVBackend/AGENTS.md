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
| `RiscvControlFlow.lean` | `loopRBlock`, the GAS lines of a counter loop with a `BNE` back-edge, `loopRBlock_length`, `loopRBlock_denote` |

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
  under the same `emittedRegs` hypothesis and shifts below 64. `emittedRegs` has 16
  names; the 64-bit allocator pool `gpPool64` also allocates `s2..s11`, for which the
  hypothesis fails.
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
| Decode round trip | `SailRiscvDecoder64.roundtrip_RInst64` | not `li`, register names in `emittedRegs`, shifts below 64 | `SailRiscvDecoder64.lean` |

## What is not proved

- The second conjunct of `comToRiscvLsem_correct` and `comToRiscvLsem_correct_mul` is
  membership in the instruction subset. The per-step Sail relation holds under its own
  hypotheses (`RegAlign`, nonzero register numbers), which these theorems do not
  discharge, and no theorem composes the per-step relation over a block.
- The decode round trips are not conjuncts of the whole-`Com` theorems, and no theorem
  maps the names of the compiled `RInst64` block into `emittedRegs`.
- No theorem relates the printers' text or the `loopRBlock` lines to a model;
  `loopRBlock_denote` and `ladder_loop_denote` equate the semantic loop with the
  unrolled block.
- The correspondence between the in-file Sail excerpts and the sail-riscv-lean output
  is not checked in the package.

See [AGENTS.md](../AGENTS.md) for the compiler as a whole and
[CAPABILITIES.md](../../../../CAPABILITIES.md) for per-primitive status.
