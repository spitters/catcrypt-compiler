# `VIR/`: directory index

This directory holds the SSA framework `Com` with its dialects, the lowerings between
dialects and down to `jasminDialect`, the Lean model of Jasmin's linear semantics
`lsem`, the `Lprog` exporter, the end-to-end compiler-correctness and
robust-compilation theorems, and per-kernel emit modules. [DIALECTS.md](DIALECTS.md)
is the dialect map: which dialect lowers to which, and which reach bytes.

Names below are relative to `CatCrypt.Crypto.SecureCompilation.VIR`. Most modules
declare into `VIR.<ModuleName>`; `KeccakF1600FrontComposeShape.lean` declares into
`KeccakF1600FrontComposeProbe` and `JasminPrintCorrect.lean` into `VIR`.

## Framework

`Core.lean` defines `Dialect`, `Ctxt`, `Expr`, `Com` and their denotations;
`CoreM.lean` the effectful denotation. `MergeCom.lean` (`Ctxt.Hom`, renaming),
`MultiCom.lean`, `MultiReturnCom.lean`, `Regions.lean`, `DialectCoproduct.lean`,
`ComInline.lean` and `ComInlineCall.lean` (`extCall` inlining), `Refinement.lean`
and `Print.lean` (textual MLIR) build on it.

## Dialects

The neutral `arith`, `memref`, `vector` and `func` dialects are in `../Dialects/`.

| Tier | Modules |
|---|---|
| SSA crypto IR | `CatCryptDialect.lean` (`catCryptDialect`), `CatCryptOpInfo.lean`, `CatCryptOpProperties.lean`, `CatCryptPrint.lean` |
| Jasmin | `JasminDialect.lean` (`jasminDialect`) |
| Front IR | `ThirDialect.lean` (with the lowering to `jasminDialect` and `lowerThir_denote`) |
| Algebraic | `FieldDialect.lean`, `ModArithDialect.lean`, `EllipticCurveDialect.lean`, `EcEdwardsAffineDialect.lean`, `PolyDialect.lean`, `LatticeDialect.lean`, `TensorExtDialect.lean` |
| Other | `MlirArithDialect.lean`, `MlirMemrefDialect.lean`, `MlirVectorDialect.lean`, `MlirScfDialect.lean`, `MlirPolynomialDialect.lean`, `TileDialect.lean`, `QuantumDialect.lean` |

## Lowerings

- `DialectToJasminCom.lean`: `cryptoDialectToJasminCom`, `Com catCryptDialect` to
  `Com jasminDialect`. `DialectToJasminComCorrect.lean`:
  `DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`, denotation
  preservation under leaf agreement.
- Leaf oracles: `CatCryptLeafOracle.lean` (`SemLeafSpec`, `catCryptDenoteWith`);
  `DialectToJasminComLeaf.lean` (`cryptoDialectToJasminCom_denote_eq_of_transport`,
  for oracle pairs related by `LeafTransport`); `SemScalarLToJasminCom.lean`
  (`semScalarLToJasminCom_denote_eq`, from `semScalarL ls` through the front to the
  jasmin denotation at `IsCoveredSCtl`; `jleafOfAbs`, `leafTransport_leafOfAbs`).
- `LatticeToJasmin.lean`: `lowerLatticeToJasmin`. `LatticeToJasminDenote.lean`
  (`lowerLatticeToJasmin_denote_eq`) and `LatticeToJasminDenoteUncond.lean`
  (`lowerLatticeToJasmin_denote_eq_uncond`).
- `ThirToCatCryptDialect.lean` (`lowerThirToCatCrypt_denote`),
  `ThirToJasminViaCatCrypt.lean`, `ThirToJasminViaCatCryptOrFlat.lean`.
- Algebraic lowerings: `FieldLowering.lean`, `ModArithLowering.lean` and
  `EllipticCurveLowering.lean` (each with `lower_denote_preserved` per operation),
  `PolyLowering.lean`, `FieldToModArithLowering.lean`, `DerivedToFieldLowering.lean`,
  `EcConvertToFieldLowering.lean`.
- Composition and transport: `LoweringDataComp.lean`
  (`LoweringDataComp.compileVia_comp_correct`), `DialectLoweringTransport.lean`,
  `ParamDialectTransport.lean`, `ComParametricityTransport.lean`,
  `ComParamDerive.lean`, `CompilerLoweringRegistry.lean`.
- Control-flow lowerings over the emit substrate: `CifLowering.lean`,
  `CallLowering.lean`, `LoopLowering.lean`, `WhileLowering.lean`,
  `StructuredControlFlow.lean`,
  `WholeFnLowering.lean`, `OpSemCoverage.lean`.

## From `Com jasminDialect` to Jasmin programs

- `JasminPrint.lean`: `lowerComToProg`. `JasminPrintCorrect.lean` states its
  structural properties; `JasminPrintSemCorrect.lean` defines `LeafAgrees` and
  `runProg` and proves `lowerComToProg_sem_eq`.
- `JasminLprogExport.lean`: the `Linear.lprog` producer, including
  `Com.toLprogPhysAbi` and the allocator `physScanSpill`. The
  `JasminLprogExport<Kernel>.lean` modules apply it per kernel.
- `JasminUprogExport.lean` (`Com.toUprog`), `ArrAbiOrch.lean`
  (`Com.toLprogArrAbi`), `JasminAbiEmit.lean`, `JasminBufferReuse.lean`,
  `JasminRegAllocPhase*.lean`, `LprogJasminWellFormed.lean`,
  `UprogJasminWellFormed.lean`.
- `LprogScheduler.lean` (`scheduleLprog`) and `LprogStoreToLoad.lean`
  (`elimReloadsLprog`): `Lprog` passes an emitter may apply.
- Vector printers: `VsimdAsmPrint.lean`, `YmmAsmPrint.lean`, `VpackZmmAsmPrint.lean`,
  with byte encoders `VsimdByteEncoder.lean` and `VsimdChachaByteEncoder.lean`.

## Linear semantics `lsem`

- `JasminLsem.lean`: `lsemStraight` and `lsemRun`. `JasminLsemLabeled.lean`: the
  labeled, program-indexed, fuel-bounded `lsem`.
  `JasminLsemSimulation.lean`: the straight-line linearizer simulation.
- `JasminLsemGeneralFaithful*.lean`: export faithfulness for general `Com`, one
  module per fragment.
- `JasminLsemMem*.lean`, `JasminLsemLoop*.lean`, `JasminLsemCall*.lean`,
  `JasminLsemShift.lean`, `JasminLsemMulCarry.lean`, `JasminLsemSimd.lean`,
  `JasminLsemWidthN.lean`: further fragments. `LsemPortAll.lean` imports them for the
  rot-guard.
  `JasminLsemRobust.lean`: `owned_lsem_correct_straightline` (functional correctness
  of the straight-line linearizer) and the syntactic leak model `lsemLeak`.
- `JasmincSemAlignment.lean`, `JasmincWArrayAlignment.lean`: alignment with Jasmin's
  Coq `psem`. `FrontControlLsem.lean`,
  `GoldenPathLsemFaithful.lean`: front control flow and golden-path exports against
  `lsem`.

## Compiler correctness

| Declaration | Fragment, hypotheses and conclusion | Module |
|---|---|---|
| `CompilerCorrectnessExtracted.rustToJasminCom_endToEnd` | `IsCoveredCtl`; front success, a `RustExec` run, entry `RustStateInterp`, lowering success of `com`, and `hAdequacy`. `com` and the valuation `W` are universally quantified and tied to the translation only through `hAdequacy`, so the value equation of the conclusion is `hAdequacy` transported along the lowering | `CompilerCorrectnessExtracted.lean` |
| `CompilerCorrectnessExtracted.rustToJasminCom_endToEnd_unconditional` | `IsCoveredSCtl`; success of the front, of `RustExec` and of `semScalar`, entry `RustStateInterp` and `ConsistentS`, the output name resolved to the slot `w`, `com` the front continuation closed at `w`, lowering success. Conclusion: a valuation related to the final `RustExec` state exists, and the Jasmin denotation is the `semScalar` output value. `rustToJasminCom_endToEnd_topLevel_unconditional` discharges both entry hypotheses at the empty context | same |
| `RustToJasminComWhile.transU_to_jasminCom_endToEnd` | `IsCoveredSU`; success of `transU fuel`, of `semU fuel` and of the lowering, entry `ConsistentS`, output tracking as above. Conclusion: the Jasmin denotation is the `semU fuel` output value; no `RustExec` conjunct | `RustToJasminComWhile.lean` |
| `CompilerCorrectness.latticeNttMul_compile_correct` | No hypothesis: for all `q`, `n` and `V`, `lowerLatticeToJasmin (tgtCom q n)` denotes the transport of the denotation of `srcCom q n` | `CompilerCorrectness.lean` |
| `CompileCorrectBaseAlu.compile_correct_riscv`, `CompileCorrectBaseAlu.compile_correct_arm` | `ComBaseAlu com` and `AllReg64 Γ` for `com : Com jasminDialect Γ (.reg 64)`. Conclusion: reading the result register after `runRBlock64` (RISC-V) or `runBBlock` (ARM) on the compiled block gives `Com.denote com V`, and every instruction of the block is base-ALU (`IsBaseAlu`) or general-purpose ALU (`IsGpAlu`) | `CompileCorrectBaseAlu.lean` |
| `CompileCorrectAllGenuine.compile_correct_all_genuine` | `ComBaseAlu com` and `AllReg64 Γ`; `GenuineModelChoice` ranges over RISC-V and ARM only. The first conjunct of the previous row, by case on the choice | `CompileCorrectAllGenuine.lean` |

README.md, section "The guarantees", discusses the first four rows. The compiler
`compileA` and its theorems (`haxc_correct_auto`, `haxc_ct_proved_all`) are in
`../Haxc/` ([PIPELINE.md](../../../../PIPELINE.md)).
`RustExecSimulatesUnified.lean` gives the `RustExec` leg for the unified front;
`ExecAdequacy.lean` and `ExecCompleteness.lean` relate the fuel-bounded executor to
the relational semantics.

Over the `psem.v` mirror: `ComJasminBridgeProgram.lean` states the correspondence
`CorresSem` with sequencing (`corresSem_append`, `corresSem_exec`), `Copn` over
registers and flags with `MULX_64`, `ADCX_64` and `CMOVcc_64` results
(`copn_regs_semIr`), `Cfor` with any body (`corresSem_for`) and `Ccall` from a callee
body derivation (`ccall_words_semIr`, `ccall_leaf_of_body`).
`LowCTMirrorTranslate.lean` (`toJasminCmd_translateCmdExt_isSome`) shows that the
JasminAST output of `LowCTToJasmin.toJasminCmd` on `callFreePlusCall` programs has a
mirror translation, and `LowCTMirrorCorres.lean` (`toJasminCmd_corresTrans`,
`toJasminCmd_mirror_exec`) that on `MirrorSimFragment` programs the `RawCode`
translation and the mirror image run to states related by `MirrorHeapCorr`, given a
correspondence for each call. `MirrorSimFragment` admits skips, assertions,
sequences, blocks, function definitions, scalar constants, branches, counted loops,
literal limb stores, selections within one tower type and admitted calls; it excludes
`RLetU64Zero`, which lowers to an integer `0` that the mirror rejects at a word type,
`RWhileNz`, which the `RawCode` translation maps to failure, and `RCloneCall` and
`RCallN`.

## Constant time and robust compilation

- `RobustSafetyContext.lean`: programs with a hole on `Com` (`ComCtx`, `plug_denote`)
  and the compositionality of the label checker `ctSafeJasmin` under plugging;
  `RobustSafetyBackTranslate.lean`: the lattice lowering of a context
  (`plug_lowerCtx`). `RobustSafety.lean` only re-exports its imports.
- `RobustCompilationPipeline.lean`: `JasminVerifiedCompiler` and
  `RobustCompilationPipeline.robustCompilation_source_to_x86`, stated for the lattice
  dialect with the x86 observable as a parameter; it states value preservation and no constant-time property.
  Constant time of emitted code is proved at the decoded bytes by
  `X86Backend.DecodedCT.bytesCTCheck_sound`.
  `OwnedX86RobustInstance.lean`: `ownedJasminVerifiedCompiler`.
- `CTPredicate.lean`, `JasminCTPredicate.lean`, `MaskingPredicate.lean`,
  `ThirCTSafe.lean`, `JForProgCT.lean`.

## Optimization passes on `Com` and `JForProg`

`CommonSubexprElim.lean` / `CommonSubexprElimReal.lean`, `DeadCodeElim*.lean`,
`LoopInvariantHoist*.lean`, `StrengthReduce*.lean`, `SoftwarePipelining*.lean`,
`InstructionSchedule*.lean`, `Peephole.lean`, `PairElimPass.lean`,
`LatticeHoist.lean`, `LatticeLoopHoist.lean`, `RegisterAllocation.lean` (`applyRA`),
`UnrolledComRA.lean`, and `Transforms/` with the driver `Transforms/Optimizer.lean`.

## Whole-program results and front engines

- `Shake256Covered.lean` (`shake256Covered_denote`), `MpnLoopCorrect.lean`
  (`mpnAddN_loop_iterate`), and the other `*Covered.lean` modules, each on one kernel.
- `KeccakF1600FrontComposeShape.lean`: `shapeTranslate_sim` (front success and
  agreement from a shape run), `cryptoDialectToJasminCom_isSome_of_pureLower`.

## Kernel emitters and algebra

- `*Emit.lean`, `*CatCryptEmit.lean`, `*AbstractCom.lean`, `*Bitexact.lean`: kernels
  for ChaCha20, SHA-2, Keccak, Poseidon2, AES, ML-KEM, ML-DSA, Plonky3, sum-check and
  others, and their ties to reference specifications.
- `Bls377*.lean`, `Fp12*.lean`, `CoordinateRing*.lean`, `CurveDivisor.lean`,
  `WeilReciprocity.lean`, `EcPairingCheck*.lean`, `LatticeNTTSemantic.lean`
  (`realNttMul_negacyclic_coeff`), `MLKEM*.lean`: algebraic specifications.
- `ComToVeir*.lean`, `VeirPrinterShim.lean`, `X25519EmitVeir.lean`: translation to
  Veir IR text; `ComToVeirCorrect.lean` states structural properties only.
