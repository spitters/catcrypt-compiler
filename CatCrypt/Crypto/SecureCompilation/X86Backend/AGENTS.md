# `X86Backend/`: directory index

This directory holds the x86-64 backend: the machine models, lowering from Jasmin
linear programs to x86 instructions, byte encoders and the ELF writer, decode round
trips in the Sail-x86 discipline, register-allocation faithfulness, machine-level
constant time and speculative leakage, the `LowCT`-to-instruction bridges, and the
x86 kernel emitters. Two routes lead from a linear Jasmin program (for example the
output of `VIR.JasminLprogExport.Com.toLprogPhysAbi`) to an artifact: the textual
route `renderLprogAtt`, and the byte route `gatherJBlock6` then `encodeJBlock6`.

Names below are relative to `CatCrypt.Crypto.SecureCompilation.X86Backend`. Most
modules declare into `X86Backend.<ModuleName>`. Exceptions: `JasminModel.lean`
declares into `X86Backend.Jasmin`; `Model.lean`, `Lowering.lean` and
`Preservation.lean` into `X86Backend`; `SailX86BlockRoundtrip.lean` into
`X86Backend.SailX86Decoder`.

## Machine models and lowering

| Module | Contents |
|---|---|
| `Model.lean`, `Lowering.lean`, `Preservation.lean` | The scalar x86 model, lowering of the `lprog` `Lopn` fragment, and per-instruction preservation |
| `JasminModel.lean` | A transcription of Jasmin's Rocq x86 semantics: `JInstr`, `JState`, `runBlock` |
| `TranslationValidation.lean` | Flag and data effects checked against Jasmin's Rocq x86 model |
| `HardwareISAAxioms.lean` | One `HardwareLeafFamily` record per instruction family (SHA-NI, AES-NI, VAES, GFNI, PCLMUL, ADX, BMI2) with its validation tier |
| `LoweringExtended.lean`, `LoweringExtendedCoverage.lean`, `LoweringCoverageCmovSar.lean`, `LoweringCoverageMulxMemSym.lean`, `LegalizeShiftImm.lean` | Coverage of further `Linstr` forms |
| `Cond.lean`, `LoopUnroll.lean`, `LprogControlFlow.lean`, `RejectLoop.lean` | Forward conditionals, unrolled loops, looped control flow, guarded loops |
| `ScfDialect.lean`, `MemrefDialect.lean`, `X86Dialect.lean`, `IndexedAddrEmit.lean` | `scf` and `memref` over the x86 machine, the backend as a `Com` dialect, indexed addressing |
| `JInstrRegMachine.lean`, `JInstrMemMachine.lean`, `JInstrRegMachineSim.lean` | The `MachineModel`, `MemMachine` and `RegMachineSim` instances at which the generic allocation results of `CatCrypt/Crypto/Optimizer/GenericRegAlloc.lean` apply |
| `RunBlockLsemAgree.lean`, `RunBlockLsemAgree*.lean`, `GatherLsemTie.lean` | `runBlock` against `VIR.JasminLsemMem.lsemStraightMem` and `lsemStraight` |

## Encoders, round trips and objects

- `ScalarEncoder.lean`: `encodeJBlock`. `CryptoExtEncoder.lean`: the
  crypto-extension families. `LprogBytes.lean`: `encodeLprog` for looped programs.
- `SailX86Decoder.lean`: per-form round trips (`roundtrip_AluRR`, `roundtrip_0FRR`,
  `roundtrip_MovImm`, `roundtrip_MovImm64`, `roundtrip_ImulImm`, `roundtrip_AluImm`,
  `roundtrip_ShiftImm`). `SailX86BlockRoundtrip.lean`:
  `SailX86Decoder.roundtrip_block`: if every instruction of `block` satisfies
  `blockCovered` and `mulxRdxOk alloc` (the first `MULX` source is allocated to
  `%rdx`), then `decodeJStream block.length (encodeJBlock alloc block)` is
  `some (block.map (renameJ alloc))`, the block with its register names resolved
  through the allocation, and no bytes remain.
  `SailX86CFDecoder.lean`: `rel32` control-flow forms. `SailX86ByteFields.lean`,
  `SailX86Lean.lean`, `SailX86Validation.lean`.
- `ScalarValidation.lean`, `CryptoExtValidation.lean`: encoder output compared with
  `gas` on recorded instances.
- `ElfObject.lean` (`buildElfObject` and the multi-symbol and relocation variants),
  `LinkerReloc.lean`, `LeafBytes.lean` (`emitLeafBytes`), `JInstrFramedEmit.lean`,
  `SpillSlotEncode.lean`, `RodataProbe.lean`, `Ymm256RodataConst.lean`.
- `LprogJInstrBytesAgree.lean`, `LprogJInstrMnemDispatch.lean`, `ResolverAgree.lean`,
  `BlockBytesAgreeExtended.lean`: agreement of `encodeLprog` with `encodeJBlock` on
  the covered fragment. `EncodedBlockCorres.lean` carries an abstract specification
  onto the encoded byte stream.

## Gather and the byte path

- `JInstrGatherExtended.lean` (`gatherJBlock2`), `GatherImmForms.lean`
  (`gatherJBlock6`, `encodeJBlock6`), `GatherFullBody.lean`, `GatherInPlace.lean`,
  `PhysBodyGather.lean`, `FramingReconcile.lean`.
- `ComLegalityToGather.lean`, `ComLegalityToGatherFull.lean`,
  `ComLegalityShiftBridge.lean`, `OptimizedComToElfLegality.lean`: from
  `../Dialects/ComLegality.lean` to gather success.
- ELF drivers: `CompileComToElf.compileComToElf`, `CompileComToElfJInstr*.lean`,
  `CompileComToElfMultiPtr.lean`, `ComToFramedJInstr.comToFramedJInstr`,
  `OptimizedComToElf.lean`, `OptimizedComToElfFull.optimizedCompileComToElf`.
- `X86OptPipelineComposed.lean`: `ValidatedPass`, `composeValidated`. The passes
  `graphColorRAValidated` and `spillSlotReuseValidated` carry `noOpCert`, which
  accepts a block only when the rewrite leaves it unchanged. `X86ComPipeline.lean`,
  `OptimizedEmitWiring.lean`, `OwnedCFOptimize.lean`, `SpillingRAFiring.lean`,
  `CarryChainSelect.lean`, `MulxSelect.lean`, `JInstrFlagLiveness.lean`,
  `RescheduleEquivalence.lean`, `RedundantReloadElim.lean`, `ValidateLowering.lean`,
  `WellFormedX86.lean`.

## The textual path

- `LprogAsmPrinter.lean`: `renderLprogAtt`, which applies no optimization.
  `AsmPrinter.lean`: the printer for `JInstr`. `RustAbiPrinter.lean`: Rust wrappers
  over export signatures.
- `Lprog` passes applied by an emitter: `LcmdReloadElim.lean` (`reloadElimLprog`,
  `renderLprogAttOpt`), `LcmdCopyPropagate.lean` (`copyPropagateLprog`),
  `AdxChainFuse.lean` (`fuseAdxChain`), `FuseMulHi.lean` (`fuseMulHiLprog`),
  `LcmdLea.lean`, `LprogLICM.lean`, `LprogOptPipeline.lean`, `StackZeroize.lean`
  (`zeroizeLprog`).

## Register allocation

- `ToLprogFaithfulAssembled.lean`: `ToLprogFaithfulAssembled.toLprogPhysAbi_faithful_uniform`,
  the store simulation for the linear-scan renaming under `lsemRun`. The other
  `ToLprogFaithful*.lean` modules supply its parts (body, prologue, two-address
  lowering, spill reloads, write side, argument materialization, cover data).
- `BackTranslation.lean`, `VsimdGraphColorRegAlloc.lean` (the vector instance of the
  generic Chaitin-Briggs allocator), `RegAllocSpillCT.lean`
  (`spillRewrite_constant_time`), `Sha256RoundRegAlloc.lean`.

## Constant time and speculation

| Declaration or module | Statement |
|---|---|
| `MachineConstantTime.blockLeak` | The machine leakage trace: branch decisions and memory addresses |
| `MachineConstantTime.owned_ct_control_flow` | Blocks of the model IR `OwnedCF` built from public-guard conditionals and literal-count loops leak the same trace from states agreeing on public registers; `OwnedCF` is not tied to `Lcmd` or bytes, so no emitted branch is covered |
| `AllocCTPreservation.toLprogPhysAbi_gather_constant_time` | A directly addressed export that gathers to an instruction block has a state-independent `blockLeak` |
| `LcmdToOwnedCF.lcmdToOwnedCF` | Recognises exported counted loops and branches as `OwnedCF` |
| `ScalarCompileCorrect.scalarCompile_correct`, `scalarCompileAlloc_constant_time` | The straight-line scalar fragment |
| `SpeculativeCTPreservation.lean` | `sct_source_to_machine_direct`, `sct_source_to_toLprogPhysAbi` |

`CompilableCT.lean`, `ConstantTimeCoverage.lean`, `BignumConstantTime.lean`,
`FrontCTBridge.lean`, `LoopExporterCTBridge.lean`, `PhysExportCTBridge.lean`,
`CFGatherBridge.lean`, `JasminOutputCTValidation.lean`, and
`SpeculativeCTMachine.lean`, `SpeculativeCTControlFlow.lean`,
`SpeculativeCTIndirect.lean`, `SpeculativeCTReturn.lean` carry the remaining cases.

## From `LowCT` to instruction blocks

`LowCTToJInstrCT.lean`, `LowCTSelectCT.lean`, `LowCTMulx.lean`,
`LowCTForCT.lean`, `LowCTMemCT.lean`, `LowCTMemDenote.lean`, `LowCTUnified.lean`,
`LowCTUnifiedMem.lean`, `LowCTCallCompose.lean`, `LowCTMvcgen.lean`
(`compile_correct_triple`), `LowCTITree.lean`, `LowCTITreePRHL.lean`,
`LowCTSecPreserve.lean`, `ImpFrontWiden.lean`.

## Kernel emitters

- Multi-precision: `Mpn*.lean` (front-compiled `mpn` kernels with `*FrontDenote`,
  `*FrontTotal` and `*LsemTie` companions), `Mul48ProvenEmit.lean`,
  `Schoolbook*.lean`, `BignumCarryDecomp.lean`, `Add2Kernel.lean`.
- Field and curve: `Cios4LimbProven.lean`, `Cios6LimbProven.lean`, `MontRedc*.lean`,
  `MontReduceRunBlock.lean`, `Curve4*.lean`, `Curve6*.lean`, `CurveField*.lean`,
  `FieldAddSubTierA.lean`, `FieldSubRunBlock.lean`, `Fe25519*.lean`, `EcJac*.lean`,
  `EcFe*.lean`, `Ed25519PointKernel.lean`, `X25519*.lean`, `Ladder*.lean`,
  `Secp256k1*.lean`, `P256FieldKernel.lean`, `P384FieldKernel.lean`, `Sm2*.lean`,
  `Pasta*.lean`, `Bn254*.lean`, `Bls12381*.lean`.
- Symmetric and hashing: `Chacha4Way*.lean`, `ChaChaQRThirEmit.lean`, `Sha2*.lean`,
  `Sha256*.lean`, `Sha512*.lean`, `Keccak*.lean`, `Blake2*.lean`, `Aes*.lean`,
  `SimdBytesVsimd.lean`, `XtsTweakKernel.lean`,
  `Poly1305Kernel.lean`, `WotsChainEmit.lean`, `TreehashChainEmit.lean`.
- Lattice and FHE: `Fhe*.lean`, `Hawk*.lean`, `Avx2YmmNttUnifiedEmit.lean`,
  `InlinedNttKernel.lean`, `BarrettButterflyKernel.lean`, `ButterflyBlockCom*.lean`.

The correctness evidence differs between kernels: some carry a `runBlock` or front
denotation theorem, and several field multiplies (for example
`Bls12381MontMulKernel.lean`, `Sm2MontMulKernel.lean`) name an external byte-level
test in their docstring as the check of the computed value. Read the docstring and
[CAPABILITIES.md](../../../../CAPABILITIES.md) before describing a kernel.
