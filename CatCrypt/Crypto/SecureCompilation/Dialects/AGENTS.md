# `Dialects/`: directory index

This directory holds the front from the source language `LowCT`
(`CatCrypt/Crypto/Jasmin/LowCT.lean`) to `Com catCryptDialect` and to rolled
`Com jasminDialect` loops, the whole-program denotation theorems for that front, the
neutral `arith`, `memref`, `vector` and `func` dialects with their lowerings to
`jasminDialect`, instruction-selection passes over `Com jasminDialect`, and
leakage and security results stated on `Com catCryptDialect`.

Names below are relative to `CatCrypt.Crypto.SecureCompilation.Dialects`. Several
modules share a namespace other than their file name: `TranslateDialectScalarDenote`,
`TranslateDialectUnifiedDenote`, `TranslateDialectWhileDenote` and
`TranslateDialectCondDenote` declare into `TranslateDialectScalar`;
`TranslateDialectVsimdDenote` into `TranslateDialectVsimd`; the `arith`, `memref`,
`vector` and `func` lowering modules into `Arith`, `Memref`, `Vector` and `Func`;
`RolledFront` and `ComLegality` into `Dialects`.

## The `LowCT → catCryptDialect` front

| Module | Contents |
|---|---|
| `TranslateDialectDirect.lean` | `translateDialect`, a structural recursion over `LowCT` emitting `Com catCryptDialect` |
| `TranslateDialectDirectArms.lean` | Multi-binding arms; `translateDialectFull` |
| `TranslateDialectDirectControl.lean` | `RIfNz` and `RFor` arms; `translateDialectControl` and the coverage predicate `IsCoveredCtl` |
| `TranslateDialectVsimd.lean` | The SIMD arm `translateDialectControlV` and `IsCoveredV` |
| `TranslateDialectFnCall.lean` | `RFnDef` and `RFnCall` arms |
| `TranslateDialectDataWhile.lean`, `TranslateDialectGuardWhile.lean`, `TranslateDialectWhileNode.lean` | Data-dependent `RWhileNz` and comparison guards |
| `TranslateDialectTotality.lean` | Front success on reads-bound covered bodies: `translateDialectFull_total`, `translateDialectControl_total` |
| `CarryChainSelect.lean`, `CarryChainSelectAdequacy.lean` | Carry-chain instruction selection at the front, and the source semantics of the selected windows |

## Whole-program denotation theorems

| Theorem | Fragment | Module |
|---|---|---|
| `TranslateDialectScalar.translateDialectFull_denote`, `TranslateDialectScalar.translateDialectControl_denote` | `IsCoveredS` | `TranslateDialectScalarDenote.lean` |
| `TranslateDialectScalar.translateDialectControl_denote_ctl` | `IsCoveredSCtl` (straight line, `RFor`, `RIfNz`) | same |
| `TranslateDialectScalar.translateDialectFull_denoteWith`, `TranslateDialectScalar.translateDialectControl_denote_ctlWith` | `IsCoveredS`, `IsCoveredSCtl`, at a leaf oracle `ls`: `catCryptDenoteWith ls` against `semScalarL ls`; `translateDialectFull_denote` and `translateDialectControl_denote_ctl` are their instances at `defaultLeaf` | same |
| `TranslateDialectScalar.rWhileNz_whole_denote` | an `RWhileNz` over an `IsCoveredSCtl` body | `TranslateDialectWhileDenote.lean` |
| `TranslateDialectScalar.rCond_whole_denote` | a guarded conditional over an `IsCoveredSCtl` block | `TranslateDialectCondDenote.lean` |
| `TranslateDialectScalar.transU_denote` | `IsCoveredSU`, closed under `RSeq`, `RBlock`, `RFor`, guarded `RIfNz … RSkip` and `RWhileNz`, against the fuel-bounded semantics `semU` | `TranslateDialectUnifiedDenote.lean` |
| `TranslateDialectVsimd.translateDialectControlV_denote` | `IsCoveredV` | `TranslateDialectVsimdDenote.lean` |
| `RustExecSemScalarBridge.rustToJasminCom_endToEnd_rustexec_adeq_topLevel` | `IsCoveredAdeq`: the Jasmin value equals the `RustExec` output word | `RustExecSemScalarBridge.lean` |

`TranslateDialectScalarDenoteSeqExt.lean` widens `IsCoveredSCtl` with control-level
sequencing. `RustExec*Adeq.lean` instantiate the `RustExec` bridge on ARX, ChaCha20,
Keccak and SHA-256 rounds. `FrontendCoincidence*.lean` prove that the two frontend
denotations agree on the base cases, immediate shifts, let-bindings, whole bodies
and at the `RustState` level.

The end-to-end theorems that compose these with the lowering to `jasminDialect`
are in `../VIR/CompilerCorrectnessExtracted.lean` and `../VIR/RustToJasminComWhile.lean`
([VIR/AGENTS.md](../VIR/AGENTS.md)).

## Rolled loops and route selection

- `TranslateDialectRolledLoop.lean`: a `LowCT` loop body to `ComL.forLoopN`;
  `rolledForLoopN_denote` and its vector (`rolledForLoopNV_denote`) and carry
  (`rolledForLoopNC_denote`) variants.
- `TranslateDialectRuntimeLoop.lean`: runtime trip count, `ComL.forLoopNRt`;
  `rolledForLoopNRt_denote`, `rolledForLoopNRtNested_denote`.
- `TranslateDialectRuntimeLoopCarrySelect.lean`, `TranslateDialectRolledFor.lean`,
  `TranslateDialectPhaseCompose.lean`, `FrontSiblingLoops.lean`,
  `TranslateDialectMultiOutPingPong.lean`, `TranslateDialectLoopCallLink.lean`:
  further loop shapes, multi-phase composition, and loop bodies with linked calls.
- `FrontLoopBodyDenote.lean`, `FrontLoopBodyStepC.lean`,
  `FrontLoopBodyNestedStepC.lean`: source adequacy of the loop-body front.
- `RolledFront.lean`: `RolledFront`, a rolled-loop front bundled with the
  denotation it realises.
- `FrontRoutePlan.lean`: `LoopShape`, `BodyFront`, `PostPass`, `OutputForm`,
  `CompilePlan`, `RouteGap`; `analyse` and `compile`. `FrontRoutePlanKernels.lean`
  runs the selector against hand-routed kernels.
- `OrchFront.lean`, `OrchLoopFront.lean`, `OrchestrationFront.lean`: loop-over-call
  and phase-schedule orchestration fronts.
- `*FrontValidate.lean`: one front arm or loop shape run end to end on a small
  kernel.

## Neutral dialects and their lowerings

| Dialect | Definition | Lowering | Denotation theorem |
|---|---|---|---|
| `arith` | `Arith.lean` | `Arith.lowerArithToJasmin` (`ArithToJasmin.lean`) | `Arith.lowerArithToJasmin_denote` (`ArithToJasminDenote.lean`) |
| `memref` | `Memref.lean` | `Memref.lowerMemrefToJasmin` (`MemrefToJasmin.lean`) | `Memref.lowerMemrefToJasmin_denote` (`MemrefToJasminDenote.lean`) |
| `vector` | `Vector.lean` | `Vector.lowerVectorToJasmin` (`VectorToJasmin.lean`) | `Vector.lowerVectorToJasmin_denote` (`VectorToJasminDenote.lean`) |
| `func` | `Func.lean` | `Func.lowerFuncToJasmin` (`FuncToJasmin.lean`) | `Func.lowerFuncToJasmin_denote` (`FuncToJasminDenote.lean`) |

`ArithLegality.lean` identifies the `SupportedOp` set with the lowered `arith`
dialect; `ArithToJasminComOK.lean` shows the lowering preserves `ComOK`;
`ArithExportFaithful.lean` and `ArithFullExportFaithful.lean` place lowered programs
in the `UniformScalarArith` and `ScalarMulCarryN` fragments; `ArithToLprog.lean`
lowers `arith` to `Lprog`. `MlirArithArithAgree.lean` relates the integer fragment of
`../VIR/MlirArithDialect.lean` to `arith`. The `Arith*GoldenPath.lean` and
`MemrefCtGoldenPath.lean` modules restate golden-path kernels at these dialects.

## Instruction selection over `Com jasminDialect`

`AndnSelect.lean`, `CmovSelect.lean`, `RorImmSelect.lean`, `IselGeneralAndn.lean`,
`IselPipelineGeneral.lean` (`rorWalk_denote`), `IselPipeline.lean`,
`IselPipelineRec.lean`, `ArithIselPass.lean`, `ArithIselSoundness.lean`: rewrites
that collapse subtrees into native operations, with their denotation results.
`IselWholeFn.lean` connects them to whole-function emit. `ComLegality.lean` is the
legality check consumed by `../X86Backend/ComLegalityToGather*.lean`.

## Leakage and security on `Com catCryptDialect`

- `CryptoDialectLeakTrace.lean` defines `Com.leakTrace`, which takes no valuation.
  Consequently `CryptoDialectLeakTraceNative.Com.isConstantTime` is
  `∀ _ _ _, Com.leakTrace c = Com.leakTrace c` and `Com.all_com_ct` is
  `fun _ _ _ => rfl`; neither constrains a program.
- `CryptoDialectCTLeak.lean`: the valued leakage `catCT` (branch, address and
  variable-time operand events of `VIR.ComLevelCheck.Com.ctLeak`) and
  `catLevelCheck_sound`; `TranslateDialectCT.lean`: the front check `levelCheckF`
  and `levelCheckF_ct` (an accepted LowCT body translates to a `catCT` program).
- `CryptoDialectLeakFactoring.lean`, `CryptoDialectVerifiedMiddle.lean`
  (`RHP_leakage_verified_middle_dialect`), `ConstantTimeTrait.lean`: structural
  statements over the valuation-free trace; not CT evidence.
- `CryptoDialectSecurity.lean` (`comSdist`), `CryptoDialectSecurityNative.lean`,
  `CatCryptDialectSP.lean` (the `SPComp` interpretation), `CryptoDialectRelCompile.lean`,
  `OtpDialectSecurity.lean`, `MoreDialectSecurity*.lean`.
- `RngLeaf.lean`, `RngRealization.lean`, `RngRealizationFinite.lean`: the `sample`
  operation as an entropy-read leaf, related to uniform `SPComp.sample`.
- `CryptoDialectRustSim.lean`: simulation between Rust state and the front.
