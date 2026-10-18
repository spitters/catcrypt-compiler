# Optimizer

Optimization, scheduling and register-allocation passes over the `Com` IR, the
`LowCT` block IR and the lowered instruction forms (`JInstr`, `Lprog`). Part of the
`CatCryptCompiler` build target, with `SecureCompilation` and `Jasmin`. The families
below differ in what their theorems state, and each entry names the theorem.

## What lives here

- `Com` rewrites over `jasminDialect`: `ComCSE` (`comCSE_denote`), `ComDCE`
  (`comDCE_denote`, generic over the dialect), `CopyProp` (`copyProp_denote`),
  `ConstFold` (`foldCom_denote`), `UncomputePass`, composed in `ComCleanupPipeline`
  (`comCleanup_denote`) and `ComCanonical` (`comCanonical_denote`).
  Each theorem states denotation equality for every valuation; the constant-folding
  and saturation stages assume a known-constant environment consistent with the
  valuation (`KEnv.Consistent`).
- Reduction selection on `LowCT`: `BarrettReduce` (`rustExec_barrettReduce_iff`) and
  `MontgomeryReduce` (`rustExec_montgomeryReduce_iff`), both instances of the call
  renaming of `RenameCalls` (`rustExec_renameCalls_iff`, under `CallsAgree`: the
  leaf specification gives each renamed leaf and its original the same result),
  `ModReduceSelect`, `SolinasFoldChain`.
- Rewrite saturation (no union-find e-graph): the `Rewrite/` subtree, indexed in
  [Rewrite/AGENTS.md](Rewrite/AGENTS.md).
- Translation validation: `TranslationValidation`, `TranslationValidationEgraph`
  (`tvCheckCanon_sound`: a candidate structurally equal to the output of
  `comAlgebraicPipeline` denotes the input), `TranslationValidationSched`,
  `TranslationValidationAll`.
- Register allocation over instruction semantics: `GenericRegAlloc`,
  `GenericRegAllocValidated`, `GenericRegAllocSim`, `JInstrRegAllocScoped`,
  `JInstrRegAllocValidated`, `GraphColoringRegAlloc`, `GraphColoringGeneric`,
  `GraphColoringCoalesce`, `SpillingRegAlloc`, `RandomizedRegAlloc`,
  `UnifiedRegAlloc`, `RegMachineToSim`, `RegAllocLeakTrace`. The simulation
  theorems (for example `regalloc_runBlock_sound_on`, `regalloc_runBlock_checked`)
  state that a renaming injective on the block's names preserves the instruction
  semantics; the decidable no-alias checkers (`noAliasX_sound`, `noAliasOn_sound`)
  discharge that hypothesis for a concrete allocation. The allocator the `Lprog`
  export runs is `physScanSpill`
  (`../SecureCompilation/VIR/JasminLprogExport.lean`), whose whole-function theorem is
  `toLprogPhysAbi_faithful_uniform` (see the package README).
- Spill and frame substrate: `FootprintSpill`, `FootprintValidatedPass`,
  `SpillReloadBlockSound`, `SpillFootprintGeneral`, `SpillSlotReuse`,
  `SpillSlotReuseGeneric`, `ByteMemMachine`.
- Memory residence and loads: `Mem2Reg`, `StoreToLoadForward`, `LoadCSE`,
  `RedundantReloadElim`, `WholeProgramResidence`, `LoopInvariantMotion`.
- Scheduling, search and cost models: `SchedulerPass`, `SchedulerPassValidation`,
  `RandomizedScheduleSearch`, `ScheduleSearchMontMulNtt`, `JointScheduleRegAlloc`,
  `X86CostModel`, `InOrderCostModel`.
- Vectorization: `SLPVectorize`, `Batch8`, `Batch8Emit`, `Batch8EmitProof`,
  `PackedArith256`, `PackedRotate256`, `PackedRotateVsimd`, `KeccakPipeline`.
- Constant time across passes: `SecretType`, `SecretTypePipeline`,
  `SecretTypeScheduler`, `SecretTypeX86`, `SecretTypeVectorize`,
  `SecretTypeAllPasses`.
- `Lattice/`: NTT algebra (convolution theorem, iterative and recursive transforms,
  butterfly passes) and `NttEmitDenotationBridge`, which relates the ML-KEM
  butterfly-stage sequence, as a value model, to `dft` and polynomial evaluation.
- Orchestration and bridges: `Pipeline`, `ComSStmtBridge`, `PipelineSmokeKat`.

## Register allocation

In `../SecureCompilation/VIR/RegisterAllocation.lean`, `linearScanRA_slotOf_eq_id`
states that the `slotOf` map of the linear scan is the identity, and
`linearScanRA_real_slotOfInjectiveOnLive` that simultaneously live binders receive
distinct slots.
