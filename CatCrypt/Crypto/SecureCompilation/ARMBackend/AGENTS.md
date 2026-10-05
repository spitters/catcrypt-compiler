# `ARMBackend/`: directory index

This directory holds the AArch64 backend: a 32-bit `W`-register model (`AState`,
`AInst`) and a 64-bit `X`-register model with a carry flag (`BState`, `BInst`), the
NEON and crypto-extension vector models, one-rule-per-constructor lowerings from
register-named op alphabets, GAS printers, byte encoders with decode round trips,
an ELF64 object writer, register-allocation soundness, the AArch64 instance of the
`ScalarLin` waist with its whole-`Com` theorem, and kernels lowered through the
models. The decoders are hand transcriptions of sail-arm field splits; no sail-arm
checkout is part of the package.

Names below are relative to `CatCrypt.Crypto.SecureCompilation.ARMBackend`. Most
modules declare into `ARMBackend.<ModuleName>`. Exceptions: `ArmModel.lean`,
`ArmLowering.lean` and `ArmAsmPrinter.lean` declare into `ARMBackend`;
`ComToArmFront.lean` into `ComToArm`; `NeonModel.lean`, `NeonLowering.lean` and
`NeonAsmPrinter.lean` into `Neon`; `NeonEncoder.lean` into `Neon.NeonEncoder`;
`SailNeonDecoder.lean` into `Neon.SailNeonDecoder`; `NeonCryptoModel.lean` into
`Neon.Crypto`; `SailArm64Refinement.lean` into `SailArm64Ref`.

## Models, lowering and printers

| Module | Contents |
|---|---|
| `ArmModel.lean` | `AState`, `evalAInst`, `runABlock`; `BState`, `evalBInst`, `runBBlock`; the counter loop `runBoundedLoopA` with `runBoundedLoopA_eq_runABlock_unroll` |
| `ArmLowering.lean` | `AOp → AInst` and `BOp → BInst`; `armBlock_lowering_denote`, `bignumBlock_lowering_denote` (the lowered run equals the fold of the per-op semantics); the RFC 8439 quarter-round KAT `qr_rfc_kat` |
| `ArmAsmPrinter.lean` | GAS text for `AInst` (`renderAInst`), `BInst` (`renderBInst`) and branches; the non-spilling linear-scan allocator `allocGp` and the name map `gpOf` |
| `ArmControlFlow.lean` | `loopABlock`, the GAS lines of a counter loop (label, one body copy, `CBNZ`), with `loopABlock_length`; the loop instruction `ALoop` (rendered by `loopABlock`) with the fuel-bounded execution `runALoop`, and `looped_eq_unrolled_denote`: a body that decrements the counter runs to the unrolled block |
| `NeonModel.lean`, `NeonLowering.lean`, `NeonAsmPrinter.lean` | The 4×u32 register file `NState` and the 8×i16 view `NState8x16` (`evalNInst8x16`); `neonBlock_lowering_denote`; GAS ASIMD text |
| `NeonCryptoModel.lean` | AESE, AESMC, AESD, AESIMC, PMULL, PMULL2 on 128-bit registers: semantics, `neonCryptoBlock_lowering_denote`, encoder, `roundtrip_ncrypt_*`; `aese_aesmc_eq_x86` on the FIPS-197 example |

## Encoders, round trips and objects

- `ArmEncoder.lean`: `encodeAInst`, `encodeBInst`, `encodeABranch`, `encodeBBlock`;
  every instruction is one 4-byte word (`encodeAInst_length`, `encodeBInst_length`).
  `ArmAbiEncoder.lean`: frame and driver words (`STP`/`LDP`, `RET`, `BL`, `SVC`,
  `CMP`), with length lemmas only.
- `SailArmDecoder.lean`: `decodeA64`, `decodeB64`, `decodeBranch` and the per-form
  round trips `roundtrip_ainst_*`, `roundtrip_binst_*`, `roundtrip_abranch_*`. Each
  assumes that every allocated operand name is recovered from its register number;
  `roundtrip_binst_orr` also requires the first source not to be register 31,
  `roundtrip_binst_lsl` a non-zero shift (the amount is a `Fin 64`), and the branch forms an offset in
  range. The decoders leave some A64 discriminant bits unread, so the theorems show
  that encoded words decode back, not that arbitrary words are classified correctly.
- `SailNeonDecoder.lean`: `decodeNeon` and `roundtrip_ninst_*` for ADD, SUB, MUL,
  AND, ORR, EOR, MOV, SHL, USHR. `SQDMULH` (`encodeNInst8x16`) and the `LDR Q`/`STR Q`
  words (`encLdrQ`, `encStrQ`) have no decoder case, and `decodeWord` does not read
  the `Q` bit.
- `EncoderDiffAudit.lean`: `example`s pinning words with register 31 in each operand
  slot to recorded assembler output.
- `ArmElfObject.lean`: `buildElfObject`, `buildElfObjectMulti`,
  `buildElfObjectMultiReloc`; lemmas on section lengths, symbol offsets
  (`symValue_*`), the header (`elf64Header_machine`) and `symCount_eq`.

## Register allocation

- `ArmRegAlloc.lean`: `liveRanges` and the spilling allocator `spillAlloc`;
  `renameABlock_runABlock` (an injective renaming that fixes `wzr` and maps no
  written name to `wzr` commutes with `runABlock`); `spillStore_establishes` and
  `reload_sandwich` over the frame-extended `AMemState`;
  `spillAlloc_slotsSeparated`. No theorem states that the output of `spillAlloc` is
  an injective renaming.
- `ArmRegAllocGeneric.lean`: `MachineModel`, `RegMachine` and `MemMachine` instances
  for `AInst`; `renameABlock_runABlock_generic` obtains the same statement from
  `../../Optimizer/GenericRegAlloc.lean`.
- `ArmBInstRegAlloc.lean`: the 64-bit counterpart tracking the carry flag:
  `renameBBlock_runBBlock`, `regToBOp_alloc_denote` (global injectivity), and
  `regToBOp_alloc_denote_on`, `regToBOp_concreteAlloc_denote` (injectivity of
  `gpOf alloc` on the block names, the decidable `allocValidOn`).
- `ArmAllocValid.lean`: `bbMul_allocValidOn` (by `decide`) and
  `bbMul_concreteAlloc_denote` for one literal allocation of the BabyBear multiply.
  No function builds a `GpAlloc` for a `BInst` block, so there is no allocator
  theorem for that path.

## From `Com` to AArch64

- `ComToArm.lean`: `armTarget`, the AArch64 `ScalarTarget`; `regToBOp_denote`;
  `regProgToArmBytes_spec`, whose second conjunct is only the length
  `4 * (regToBOp p).length`.
- `ComToArmFront.lean`: `eval_*_faithful` (each `RegStmt` effect is the
  `jasminDialect` op at width 64); `bbMul_compiled_eq_hand` and
  `bbMul_machine_eq_denote` for `bbMulReg`.
- `ComToArmLoop.lean`: `loop_waist_denote`, `unrolled_waist_denote`.
- `ComToArmLsem.lean`: `comToArmLsem_correct`, the proposition `ArmBaseAluGrounded`
  and the `MachineModel` `armBaseAluModel` with `exec` the `runBBlock` fold. It
  reuses `ComBaseAlu` from `../RISCVBackend/ComToRiscvLsem.lean`.
- `SailArm64Refinement.lean`: `armStep_transcription_matches_model` equates a
  hand-transcribed execute clause over its own register file with the `ArmModel` op
  functions. It does not mention `evalBInst` or `BState`, and no module imports it.

Kernels: `ArmBignumKernel.lean` (`bignum_add_p256`), `ArmMontMulKernel.lean`
(4×4→8 schoolbook), `ArmSha256Kernel.lean` (one SHA-256 compression),
`ArmX25519FieldKernel.lean` (field operations, `cswap`, the ladder step,
`runBoundedLoopB`). Each `*_lowering_correct` theorem instantiates
`armBlock_lowering_denote` or `bignumBlock_lowering_denote` at the kernel body. The
computed values are checked by `native_decide` on worked vectors (`addp256_kat`,
`mul48_kat_max`, `sha256_abc_kat`, `feMul_kat_full`, `ladderStep_kat`,
`ladder_loop2_runs`); no theorem states an all-inputs arithmetic identity such as
`(x + y) mod p_256`.

## Entry-point theorems

| Result | Declaration | Fragment and hypotheses | File |
|---|---|---|---|
| Whole-`Com` value preservation | `ComToArmLsem.comToArmLsem_correct` | `ComBaseAlu com` (ADD, SUB, AND, ORR, EOR), `AllReg64 Γ`, `s.regs = envOf Γ.length V`; the result register holds `Com.denote com V` and every executed `BInst` satisfies `IsGpAlu` | `ComToArmLsem.lean` |
| Scalar waist | `ComToArm.regToBOp_denote` | every `RegProg` and `BState`; target `armTarget.denote p s`, on unallocated names | `ComToArm.lean` |
| Allocation inside the equality | `ArmBInstRegAlloc.regToBOp_concreteAlloc_denote` | `allocValidOn alloc (lowerBBlock (regToBOp p))` and a `ReindexedOn` start state | `ArmBInstRegAlloc.lean` |
| Loop over the waist | `ComToArmLoop.loop_waist_denote` | every `RegProg` and trip count, on the semantic loop `runBoundedLoopB` | `ComToArmLoop.lean` |
| Block lowering | `armBlock_lowering_denote`, `bignumBlock_lowering_denote`, `Neon.neonBlock_lowering_denote` | all blocks and states | `ArmLowering.lean`, `NeonLowering.lean` |
| Decode round trip | `SailArmDecoder.roundtrip_binst_add` and the other `roundtrip_*` | per instruction, operand names in the register pool | `SailArmDecoder.lean` |

## What is not proved

- The decode round trips are not conjuncts of `comToArmLsem_correct` or
  `regProgToArmBytes_spec`; no theorem composes the encoder, a decoder and
  `runBBlock`.
- No theorem relates `runBBlock` to a Sail execute clause (see
  `SailArm64Refinement.lean` above). The per-instruction semantics is checked against
  the Arm ARM by reading and by external differential tests.
- No theorem relates the text of `ArmAsmPrinter.lean` or `NeonAsmPrinter.lean` to a
  model. The `loopABlock` lines are the rendering of an `ALoop`, whose execution
  `runALoop` follows the label and `CBNZ` back-edge; `looped_eq_unrolled_denote`
  equates it with the unrolled block when the body decrements the counter.
  `ladder_loop_denote` is about `runBoundedLoopB`, which takes the trip count as an
  argument.
- The `mulhs` arm of `evalNInst8x16` is the plain signed high half, while
  `encodeNInst8x16` emits `SQDMULH`, which doubles and saturates; the difference is
  not discharged (see also `../TileBackend/TileS16HighMul.lean`).

See [AGENTS.md](../AGENTS.md) for the compiler as a whole and
[CAPABILITIES.md](../../../../CAPABILITIES.md) for per-primitive status.
