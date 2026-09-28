# `SecureCompilation/`: directory index

This directory holds the compiler: the source fronts, the `Com` SSA framework and its
dialects, the lowerings between dialects, the per-ISA backends, and the correctness,
constant-time and refinement theorems about them. Most module namespaces follow the
file path under `CatCrypt.Crypto.SecureCompilation`; some do not (for example
`Dialects/TranslateDialectUnifiedDenote.lean` declares into
`Dialects.TranslateDialectScalar`), so read a module's `namespace` line before
citing a qualified name. Paths below are relative to this directory unless they start
with `CatCrypt/` or name a document at the package root.

## Documents to read first

- [README.md](../../../README.md), sections "The guarantees" and "Scope": the
  headline theorems with their level and fragment; [HEADLINES.md](../../../HEADLINES.md)
  and [NAVIGATION.md](../../../NAVIGATION.md).
- [DEMO.md](../../../DEMO.md) and [EXAMPLES.md](../../../EXAMPLES.md): worked examples.
- [CAPABILITIES.md](../../../CAPABILITIES.md): per-primitive modules and theorems.
- [VIR/DIALECTS.md](VIR/DIALECTS.md): which dialect lowers to which, and which reach bytes.
- [PipelineMap.lean](PipelineMap.lean): the two hax ingestion pipelines
  (`compileFromHax` and `haxToLowCT`) and what each accepts.
- [Dialects/FrontRoutePlan.lean](Dialects/FrontRoutePlan.lean): the rolled-loop front
  indexed by loop shape, body front, continuation and post-pass; `analyse` classifies
  a `LowCT` source, `compile` dispatches, and an unsupported combination is reported
  as a `RouteGap` naming the axis.
- [ASCENT.md](../../../ASCENT.md) and [Ascent/AGENTS.md](Ascent/AGENTS.md): the
  correspondence proofs from code up to Lean specifications.

## Subdirectories

| Directory | Contents | Index |
|---|---|---|
| `VIR/` | The `Com` framework (`Core.lean`), the dialects, dialect lowerings, the Jasmin linear semantics `lsem`, end-to-end compiler-correctness and robust-compilation theorems, and per-kernel emit modules | [VIR/AGENTS.md](VIR/AGENTS.md) |
| `Dialects/` | The `LowCT → catCryptDialect` front (`translateDialectControl` and its extensions), its whole-program denotation theorems, the neutral `arith`/`memref`/`vector`/`func` dialects, instruction-selection passes, and dialect-level leakage and security | [Dialects/AGENTS.md](Dialects/AGENTS.md) |
| `X86Backend/` | The x86-64 machine model, lowering, encoders, ELF writer, Sail-x86 decode round trips, register-allocation faithfulness, machine constant time, and x86 kernel emitters | [X86Backend/AGENTS.md](X86Backend/AGENTS.md) |
| `Ascent/` | `Corres` refinement from `LowCT`, x86 and RV64 code to Lean specifications | [Ascent/AGENTS.md](Ascent/AGENTS.md) |
| `ARMBackend/` | AArch64 and NEON models, lowering, encoders, allocator, ELF writer; `ARMBackend.ComToArmLsem.comToArmLsem_correct`; decode round trips in `SailArmDecoder.lean`, `SailNeonDecoder.lean` | [ARMBackend/AGENTS.md](ARMBackend/AGENTS.md) |
| `RISCVBackend/` | RISC-V and RVV models, lowering, encoders, ELF writer; `RISCVBackend.ComToRiscvLsem.comToRiscvLsem_correct`, `RISCVBackend.ComToRiscvLsem.riscvStep64_sail_grounded`; decode round trips in `SailRiscvDecoder.lean`, `SailRiscvDecoder64.lean` | [RISCVBackend/AGENTS.md](RISCVBackend/AGENTS.md) |
| `TileBackend/` | A tile-level semantics (`TileModel.lean`) with an emit to NVIDIA Tile IR (`ComToTileIR.lean`), and bridges presenting the AVX2 and AVX-512 packed cores as instances of the shape-generic tile lowering | [TileBackend/AGENTS.md](TileBackend/AGENTS.md) |
| `MLIR/VectorDialect/` | The vector op alphabet, its lowerings to a per-lane scalar program and to AVX-512 instructions, `BitVec` models of x86 SIMD intrinsics, and the auto-vectorizer (`AutoVectorize/`); none of these lowerings produces `Com` | [MLIR/VectorDialect/AGENTS.md](MLIR/VectorDialect/AGENTS.md) |
| `MLIRBackend/` | MLIR text printing (`MLIRBackend.emitFunc` in `ComToMLIR.lean`), the Veir translation (`ComToVeir.lean`), a GPU path through Tile to NVVM (`ComToNvptx.lean`), and the opaque proposition `MLIRBackend.MlirBackendSemanticsAgrees` (`Denote.lean`) | none |
| `Jasmin/` | Jasmin-to-SSA translation targeting `catCryptDialect` with its correctness, and s2n-bignum SSA results transported onto that dialect | none |
| `AUCurvesImport/` | Cross-prover bridges from AUCurves field-multiply leaf specifications to `LeafSem`, and an importer pilot | none |
| `LowCTExtensions/` | Extension lemmas for the `RFor`, `RArrLoad` and `RArrStore` constructors | none |

The optimizer passes live in `CatCrypt/Crypto/Optimizer/`
([README](../Optimizer/README.md)); the source language `LowCT` in
`CatCrypt/Crypto/Jasmin/LowCT.lean` and its elaborator `reifyLowCT%` in
`CatCrypt/Crypto/Jasmin/LowCTReflect.lean`; the hax front `haxToLowCT` in
`CatCrypt/Crypto/Hax/`.

## Top-level modules by role

Fronts from extracted Rust.
- `CompileFromHax.lean`: `compileFromHax` from hax `ImpExpr` through `Thir` to
  `Com jasminDialect`, with `compileFromHax_denote` and `compileFromHax_meets_spec`.
- `CompileFromHaxScope.lean`: the scope predicates `OperandInScope` and `Compiles`,
  and `compileFromHax_isSome_of_compiles`, which discharges front success.
- `ImpExprToThir.lean`, `HaxToThirFront.lean`, `ThirToComFront.lean`,
  `ThirToCryptoDialect.lean`, `CompileFromHaxDialect.lean`: the stages of that front.
- `CompileFromHaxLink.lean`, `CompileFromHaxLinkExample.lean`: the leaf registry and
  linker; `linkedExample_correct` is a linked program with no hypothesis.
- `CompileFromHaxPrimeIrFront.lean`, `CompileFromHaxPrimeIrField.lean` and the other
  `CompileFromHaxPrimeIr*` modules: `primeir-hax` trait calls to field, modular and
  curve operations.
- `CompileFromHax<Primitive>.lean` and `CompileFromHax<Primitive>Tie.lean`: one
  primitive through the front, and its tie to a specification or to a protocol's
  dependency record (`*SecurityTie.lean`).

Relational compilation from Lean specifications.
- `RelationalCompile.lean` (the Rupicola-style core), `RelationalCompileHigh.lean`
  (over `fieldDialect`), `RelationalFront.lean` (the entry point), and the per-curve
  `RelationalFront<Curve>*.lean` modules with the registry
  `RelationalFrontCurveRegistry.lean`.

Shared substrate.
- `CryptoSSA.lean` (types, contexts, variables), `RustStateSubstrate.lean`
  (`RustStateInterp`), `LowCTToCryptoSSA.lean`, `ComBuilder.lean` (named SSA to
  `Com jasminDialect`), `BorrowSafety.lean` and `BorrowToMemoryBridge*.lean`.

Machine-code demonstrations.
- `ScalarLin.lean` (the target-neutral straight-line waist), `ScalarLinX86Demo.lean`,
  `ScalarLinNeutralDemo.lean`, `MultiBackendDemo.lean` (theorems in the table below),
  `CompilerHelloDemo.lean` (prints a compiled program).

Golden paths and kernel emitters.
- `FieldEmitGolden*.lean`, `*GoldenPath.lean`, `Bignum*Emit.lean`,
  `BarrettReduceEmit*.lean`, `Secp256k1PointOp*.lean`, `Secp256k1FeMul*.lean`,
  `Bn254TowerFrontEmit.lean`, `Mersenne31FrontEmit.lean`, `MlkemNtt*.lean`:
  per-primitive kernels built as `Com jasminDialect` and emitted.
  `BigNat*.lean`, `BigInt*.lean`: the variable-width limb carrier and its refinements.

Realization and grounding.
- `KernelRealizesClass.lean`, `GenericKernelRealization.lean`,
  `ProtocolEmitRealizes.lean`: the kernel-realization predicate and registry.
- `Concrete*Realizer.lean`, `*KernelRegistryEntry.lean`, `*ProtocolKernels.lean`,
  `Grounded*.lean` (index in `GroundedPortfolio.lean`): instances per primitive or
  protocol.
- `EcRealizationGeneric.lean`, `EcProjectiveGeneric*.lean`,
  `MontgomeryLadderGeneric.lean`, `QuadExt*Generic.lean`, `CubExtGeneric.lean`:
  curve and extension-field specifications generic in the field.

Constant time and speculation.
- `JasminCTByConstruction.lean` (the index-free fragment of `Com jasminDialect`),
  `ThirCTByConstruction.lean` (`thirDialect`), `FrontJasminCT.lean`: constant time
  by construction.
- `ImpCTGate.lean`, `LowCTCTFlowSensitive.lean`, `LowCTLeakTraceDef.lean`,
  `SourceSecrecyTransfer.lean`, `VarTimeOpDetector.lean`: source-level analyses.
- `SpeculativeCT*.lean`, `TransientTyping.lean`, `BladeSelectiveProtect.lean`:
  speculative leakage at the `LowCT` level.
- `SecureCompileChain.lean`: `secure_compile_constant_time`,
  `secureCompile_constant_time`, `secureCompile_no_branch`.

## Entry-point theorems

Names are relative to `CatCrypt.Crypto.SecureCompilation`; README.md states the
fragment and hypotheses of each.

| Result | Declaration | File |
|---|---|---|
| Dialect lowering preserves denotation | `VIR.DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'` | `VIR/DialectToJasminComCorrect.lean` |
| LowCT to Jasmin `Com`, value equation as hypothesis | `VIR.CompilerCorrectnessExtracted.rustToJasminCom_endToEnd` | `VIR/CompilerCorrectnessExtracted.lean` |
| The same on `IsCoveredSCtl`, no adequacy hypothesis | `VIR.CompilerCorrectnessExtracted.rustToJasminCom_endToEnd_unconditional` | same |
| `RustExec` output on `IsCoveredAdeq` | `Dialects.RustExecSemScalarBridge.rustToJasminCom_endToEnd_rustexec_adeq_topLevel` | `Dialects/RustExecSemScalarBridge.lean` |
| Data-dependent `while` | `VIR.RustToJasminComWhile.transU_to_jasminCom_endToEnd` | `VIR/RustToJasminComWhile.lean` |
| Two composed lowerings under `runProg` | `VIR.LoweringDataComp.compileVia_comp_correct` | `VIR/LoweringDataComp.lean` |
| Lattice route and robust compilation | `VIR.CompilerCorrectness.latticeNttMul_compile_correct`, `VIR.RobustCompilationPipeline.robustCompilation_source_to_x86` | `VIR/` |
| Straight-line machine code per backend | `ScalarLinX86Demo.com_x86_e2e`, `ScalarLinNeutralDemo.com_arm_e2e`, `MultiBackendDemo.com_riscv_e2e` | top level |
| Register-allocation store simulation | `X86Backend.ToLprogFaithfulAssembled.toLprogPhysAbi_faithful_uniform` | `X86Backend/` |
| Machine constant time | `X86Backend.AllocCTPreservation.toLprogPhysAbi_gather_constant_time`, `X86Backend.MachineConstantTime.owned_ct_control_flow` (on the model IR `OwnedCF`; no emitted branch is covered) | `X86Backend/` |

## Facts that are easy to misread

- `Dialects.CryptoDialectLeakTraceNative`: `Com.isConstantTime c` unfolds to
  `∀ _ _ _, Com.leakTrace c = Com.leakTrace c`, and `Com.all_com_ct` is
  `fun _ _ _ => rfl`. The declarations constrain no program. Value-dependent leakage
  is in `Dialects/CryptoDialectLeakTraceValued.lean`,
  `CatCrypt/Crypto/Jasmin/LowCTCTAnalysis.lean` (`cmdCT`) and
  `X86Backend.MachineConstantTime.blockLeak`.
- `X86Backend.LprogAsmPrinter.renderLprogAtt` applies no optimization. The `Lprog`
  passes `reloadElimLprog` (used by `renderLprogAttOpt`), `fuseMulHiLprog`,
  `fuseAdxChain`, `copyPropagateLprog`, `loadCSELprog` (`CatCrypt/Crypto/Optimizer/`),
  `scheduleLprog` and `elimReloadsLprog` are applied by the emitter that calls them.
- A docstring carrying `@kat-target` (for example `BignumAddEmit.lean`) or
  `@bench-only` (`MLIR/VectorDialect/LoweringChoice.lean`) marks a hand-written block
  kept as a test-vector oracle or a measurement, not compiler output. Read the
  docstring before describing a kernel's provenance; a file name does not fix it
  (`ScalarLinX86Demo.lean` holds `com_x86_e2e`).
