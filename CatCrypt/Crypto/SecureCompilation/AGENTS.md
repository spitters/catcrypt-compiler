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
- [PIPELINE.md](../../../PIPELINE.md): the compile line of `compileA`, with the check
  and theorem of each stage.
- [Hax/FrontDomain.lean](../Hax/FrontDomain.lean): `HaxModule.refusal?`, which names
  the first construct of a module outside the domain of the front `haxToNF` of
  `compileA`.
- [Dialects/FrontRoutePlan.lean](Dialects/FrontRoutePlan.lean): the rolled-loop front
  indexed by loop shape, body front, continuation and post-pass; `analyse` classifies
  a `LowCT` source, `compile` dispatches, and an unsupported combination is reported
  as a `RouteGap` naming the axis.
- [ASCENT.md](../../../ASCENT.md) and [Ascent/AGENTS.md](Ascent/AGENTS.md): the
  correspondence proofs from code up to Lean specifications.

## Subdirectories

| Directory | Contents | Index |
|---|---|---|
| `Haxc/` | The hax compiler `haxc`: the entry `compileA` (`ComposeV1.lean`), the linear route `nfChain` (`NFChain.lean`) and the chain `extChain` (`ExtChain.lean`, `NFChainCall.lean`), the field route `fieldRegionFront` (`FieldLowerChain.lean` and the other `Field*.lean` modules), the region back half `compileRegion` (`RegionBackend.lean` and the `Region*.lean` modules), the correctness theorems `haxc_correct_auto` (`RegionLinkCall.lean`) and `haxc_correct_auto_tuple` (`ComposeTuple.lean`), constant time (`haxc_ct_proved_all` in `ComposeCTStraight.lean`; `CT*.lean`), `haxc_gate_proved_all` (`RCInstance.lean`), Jasmin source of a compiled module `jasminOfA` (`ComposeJazz.lean`), and the root of the executable `haxc` (`HaxcMain.lean`) | [PIPELINE.md](../../../PIPELINE.md) |
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
| `Algebraic/` | Field expressions compiled to `fieldDialect` programs (`FieldExprCompile.lean`), their lowering to Jasmin limbs or words per reduction strategy (`FieldToJasminLimbs*.lean`, `FieldToJasminWord.lean`, `ModArithLimbTemplate*.lean`, `Algebraic/FieldLimbs/`, `Algebraic/FieldWord/`), and the curve-point, Poseidon and Poseidon2 kernels built on them | none |
| `CT/` | The constant-time leakage model `CTLeak` at the machine and source levels (`Leakage.lean`, `LowCTLeakage.lean`), the per-ISA timing regimes (`IsaRegime.lean`, `X86Timing.lean`, `ArmTiming.lean`, `RiscvTiming.lean`) and the security levels of hax code (`HaxLevels.lean`) | none |
| `SepLogic/` | Separation logic with footprints over total states (`Core.lean`), contracts of run relations (`Contract.lean`, `ContractX86.lean`) and their instances at the address machine and byte memory | none |
| `SourceSecrecyTransfer/` | `SourceSecrecy` with `SourceSecrecy.toLevelTable` and `SourceSecrecy.declassify` (`Defs.lean`); the transfer theorems are in `SourceSecrecyTransfer.lean` | none |
| `Generated/` | Generated `Hax.TExpr` literals; regenerate them, do not edit them by hand | none |

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
- `GenericKernelRealization.lean`, `ProtocolEmitRealizes.lean`: the
  kernel-realization predicate.
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

- `Dialects.CryptoDialectLeakTrace.Com.leakTrace`
  takes no valuation, so an equality of two such traces constrains no program and is
  not constant-time evidence. Value-dependent leakage on `Com` is `VIR.ComLevelCheck.Com.ctLeak` (at the dialect: `Dialects.CryptoDialectCTLeak.catCT`,
  with the front theorem `Dialects.TranslateDialectCT.levelCheckF_ct`),
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

## Rules for contributors

Emit and output.
- An emit kernel is generated: by the descent over a `LowCT` program written in Lean
  (`reifyLowCT%`, `translateDialectControl`, `cryptoDialectToJasminCom`, the owned
  backend), by relational compilation from a Lean specification
  (`RelationalCompile.lean`), or by a field template. It is never hand-authored as
  `Com`, `Lcmd`, `JInstr` or assembly text: a hand-authored kernel checked against a
  hand-authored specification says nothing about generated code. If a front cannot
  express a kernel, extend the front. The legacy hax fronts `compileFromHax` and
  `haxToLowCT` are not kernel sources. `scripts/handcom-provenance-ratchet.sh` fails
  when the number of hand-authored kernels rises.
- The owned backend produces the artifact. Jasmin source is printed only by
  `Jazz.print` (`CatCrypt/Crypto/Jasmin/JazzPrint.lean`) behind the round-trip gate
  `printChecked` (`CatCrypt/Crypto/Jasmin/JazzRoundTrip.lean`), as `jasminOfA` does
  for `compileA`; a new module does not render Jasmin text from string templates.
- Before reporting that a construct is unsupported, run the domain check of the
  front: `HaxModule.refusal?` for `compileA`, `analyse` of
  `Dialects/FrontRoutePlan.lean` for the rolled-loop `LowCT` front. A dispatched or
  generic capability shares no identifier with the monomorphic form a name search
  looks for, so list the owning directory before concluding that a capability is
  missing.
- Do not claim a backend capability from a kernel docstring; read the printer or
  encoder source.

Register allocation is generic.
- `CatCrypt/Crypto/Optimizer/GraphColoringGeneric.lean` holds the Chaitin-Briggs
  allocator over `[MachineModel I]`, and `CatCrypt/Crypto/Optimizer/GenericRegAlloc.lean`
  the spill soundness over `[MemMachine M]` and `RegMachine`. A new backend supplies
  these instances, not a new allocator; `X86Backend/VsimdGraphColorRegAlloc.lean`,
  `ARMBackend/ArmRegAllocGeneric.lean` and `RISCVBackend/RiscvRegAlloc.lean` are the
  instances. `selectColors` advances spill offsets by its `stride` argument, `8` by
  default: pass the register width for a vector pool, and allocate a vector pool
  through an entry point that names the pool, since a `MachineModel` instance fixes
  one register pool.

Proof cost. Do not prove a property of a large term by reducing the term; state the
property parametrically or structurally, so that the proof's cost does not grow with
the object. The signs are a `set_option maxRecDepth` or `maxHeartbeats` beside a
proof, `rfl` or `decide` on a concrete byte list, a rendered string or a builder at a
concrete depth, and `native_decide` where the claim is a prefix, a length or a shape.
The replacements:
- a prefix of an object: one prefix lemma parametric in the rest, instantiated per
  builder;
- a builder's denotation at depth `n`: generalise over the counter and induct;
- the length of a kernel: per-encoder length lemmas summed through
  `List.length_append` (`CryptoExt.encAvx2Alu_length` in
  `X86Backend/CryptoExtEncoder.lean`; `Chacha4WayQrObjectEmit.emit_length` and
  `Chacha4WayTransposeObjectEmit.encodeTranspose4way_length` are worked examples);
- success of a front (`.isSome`): for `compileFromHax`, the scope predicate
  `Compiles` with `compileFromHax_isSome_of_compiles` (`CompileFromHaxScope.lean`); for
  `translateDialectControl`, the shape interpreter of
  `VIR/KeccakF1600FrontComposeShape.lean` (`shapeTranslate_sim`) with
  `cryptoDialectToJasminCom_isSome_of_pureLower` for the backend;
- a cast such as `(R : ZMod q) ≠ 0`: move the goal off the cast first
  (`ZMod.natCast_eq_zero_iff`) instead of `decide`;
- a property of every statement of a program: a per-statement lemma composed with
  `List.forall_mem_cons`;
- a recursive builder over a concrete carrier: make it parametric in the carrier;
- a program assembled by `++` from list literals: write constructors out in full
  (`RegStmt.mov`) instead of `.mov`, whose elaboration is postponed and redone along
  the chain;
- a membership side condition over names: an inductive over `List.Mem` discharged
  by its constructors, instead of a `Bool` recursion over `String` equality;
- a result threaded through several stages: one lemma per stage with a named
  postcondition bundle (`FrameIdx`, `ConstVals`, `LoadFrame` in
  `Secp256k1PointOpPrologue.lean`);
- a large monolithic `Com` whose long-lived values are SSA bindings: keep the values
  in a frame buffer at compile-time offsets and access them per operation, as
  `X86Backend/Ed25519PointKernel.lean` does, since a variable at de Bruijn depth `d`
  costs `d` cells in the lowering.

`scripts/check-build-cost.sh <Module>` reports a module's elaboration time against
`scripts/build-cost-baseline.tsv`; a module above one second states the reason in its
docstring. A known-answer check in a Lean source is written only with `#kat` or
`#kat_kernel`; vector batteries go to the external harness under `bench/`
(`scripts/lean-kat-ratchet.sh`).

Building. Build the narrowest target, `lake build <Module>`, which builds that
module's import closure; [BUILDING.md](../../../BUILDING.md) gives the full build and
the checks in `scripts/`. After adding or removing a module run
`bash scripts/gen-module-globs.sh`.
