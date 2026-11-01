# Correctness methods: descent, ascent, transfer

A correctness theorem about code in the CatCrypt workspace is proved by one of three
techniques or by a composition of them. A program that a technique cannot express
leads to an extension of that technique (a front construct, an ascent rule, a
registered relation), so every proof stays within the three.

| Technique | Direction | Judgement | Proves |
|---|---|---|---|
| Descent | source to bytes | simulation of each pass | the emitted code has the denotation of its source |
| Ascent | given code to a Lean function | `Corres`, `FnCorres` | the given code computes a stated Lean function |
| Transfer | across a representation | `Related`, `Param` | a fact about abstract values holds of their representations, or conversely |

This package depends on CatCrypt-core, hax-lean and ParamTransfer (`lakefile.lean` gives
the pinned revisions). Paths below are relative to this package unless the text names
another package.

The operation semantics that these theorems are stated over, compared with LLVM, MLIR
`arith` and Rust at every layer, are in
[SEMANTICS.md](CatCrypt/Crypto/SecureCompilation/VIR/SEMANTICS.md).

## Descent: the verified compiler

Descent generates code from a source and proves each lowering a simulation. The
source is therefore the specification: correctness is equivalence to the source (the
Rust reference for extracted code), and known-answer tests are regressions. The chain
runs from the front through `LowCT`, the SSA dialects, `Com jasminDialect` and
`Lprog` to the owned x86, AArch64 and RISC-V encoders. The intended source is
orchestration: Rust above the field interface, with field operations as primeIR calls
and limb-level or bit-level kernels as calls to optimised implementations whose
correctness is a template theorem or an ascent theorem ([ASCENT.md](ASCENT.md)).

A template theorem covers straight-line word arithmetic generated from an algebraic
template: one denotation theorem over every parameter record, a bounds certificate decided
per instance (`boundsOk` with `denote_eq_denoteZ_of_boundsOk`, `SchedOk`), and a bytes
theorem per family, such as `field_correct_bytes` (`Haxc.FieldBytes`) for the field
product, whose only per-instance hypothesis is acceptance by the region back half
`compileRegion`, whose correctness is `compileRegion_correct`.
[FIAT_TEMPLATES.md](FIAT_TEMPLATES.md) gives the template families and the instance
tables with the accepted programs.

- The hax front `haxToLowCT` in `CatCrypt/Crypto/Hax/` lowers hax-lean's `ImpExpr` to
  `LowCT`. Its simulation theorem `haxToLowCT_simulates_programT`
  (`CatCrypt/Crypto/Hax/HaxToLowCTSim_ProgramTower.lean`) holds for builtin tables that
  implement neither `array_update` nor `index`; the earlier form
  `haxToLowCT_simulates_program` assumes that no builtin returns a scalar, which no table
  implementing hax arithmetic satisfies. Its modules carry `deprecated_module`. It serves the kernel producers and the `LowCT` → Rust
  route of [HAX_RUST.md](HAX_RUST.md); `compileA` does not use it (next item). Early exits
  lower to exit-flag form. `scalarizeExitIn`
  (`CatCrypt/Crypto/Hax/HaxToLowCTExitWordOps.lean`) replaces marshalled word calls by
  scalar assignments and unsigned comparisons by their signed forms. `placedUse`
  (`CatCrypt/Crypto/Hax/HaxToLowCTPlaced.lean`) checks that every name is used in the
  heap of its placement. [HAX_RUST.md](HAX_RUST.md) gives the procedures.
- The front of `compileA` is `haxToNF`. It selects bodies with the shape check
  `shapeAccepts` (`CatCrypt/Crypto/Hax/HaxFrontPrepShape.lean`; the body is `nfBody`,
  `Haxc/NFFront.lean`), and the import closure of the headline modules contains no module
  of `haxToLowCT`. The tables the fronts share are in modules of their own: the call names,
  widths and scalar values (`CatCrypt/Crypto/Hax/HaxCallNames.lean`), the acceptance tests
  `FrontOracle` with the body selection (`Hax.HaxFrontOracle`), the `u64` tables
  `hax64Exit` and `hax64WExit` (`Hax.Hax64Table`), the spine and typing facts of a body
  (`Hax.HaxSpine`) and the word results of source runs (`Haxc.WordResult`).
- In the Jasmin `.jinc` importer (`CatCrypt/Crypto/Jasmin/`), `JincParser` and
  `JincToCom` read the straight-line fragment, `JincElab` elaborates it to
  `Com jasminDialect`, and `JincToLowCT` emits `for` and `while` as the loop nodes
  `RFor` and `RWhileNz`. `JincInline` partially evaluates a Jasmin source unit
  (inlining, constant folding, scalar replacement of register arrays).
  `importFunRolled` keeps a loop over an affine counter rolled, as a loop over a
  run-time trip index. The correctness theorem of an imported leaf is stated over the
  `LowCT` or `Com` that the import produces. `KeccakJincImport` takes formosa-keccak's Keccak-f[1600] through this path.
- The scalar front's denotation theorems assume a coverage fragment: `IsCoveredSU` for
  `transU_denote`, `IsCoveredSCtl` for `frontLoopBodyJ_denote` and
  `translateDialectControl_denote_ctl`. `transU` takes the entry environment and emits
  the trace of the body at that environment, with each conditional decided and each loop
  unrolled there. `coveredB` and
  `isCoveredSCtl_of_coveredB` (`CatCrypt/Crypto/SecureCompilation/Dialects/CoveredSCtlDecide.lean`)
  discharge it by `decide`.
- The dialect-tower statements from `LowCT` are `rustToJasminCom_endToEnd_unconditional`
  (`VIR/CompilerCorrectnessExtracted.lean`), which ends at the Jasmin dialect and gives
  each leaf call the default value of its type, and the straight-line demonstrations
  `com_x86_e2e`, `com_arm_e2e` and `com_riscv_e2e`. The three demonstrations compile a
  straight-line, register-only `Com` through the `ScalarTarget` instruction selection
  (`ScalarLin.lean`) into register models whose registers are named by strings, over
  virtual registers without allocation. `robustCompilation_source_to_x86`
  (`VIR/RobustCompilationPipeline.lean`) takes the x86 step as the field `semRefine` of a
  `JasminVerifiedCompiler` record, and its source is the lattice dialect, whose NTT is the
  identity; it is not a statement about an x86 compiler.
  [HEADLINES.md](HEADLINES.md) states each with its hypotheses.
- The hax compiler `haxc` (`CatCrypt/Crypto/SecureCompilation/Haxc/`, executable
  `lake exe haxc`) composes the hax front, the route to the Jasmin dialect, the export to
  `Lprog`, the owned back end and the encoder, and ends at decoded x86 bytes run by the
  address machine `aMachine`. The bytes are read by the package's own decoder
  `decodeLprog` and run on its own x86-64 model `aMachine`; the encoder round trip
  `roundtrip_block` relates the encoder to that decoder. Its general theorems quantify over
  every module the compiler accepts.
  - `haxc_correct_auto` (`Haxc/RegionLinkCall.lean`), value correctness: for a result
    `(P, bytes)` of `compileA m σ fname` on a module whose linked functions have distinct
    names and are linked kernels (`LinkedKernel`), the bytes decode to a program `prog`,
    and from every entry state satisfying the regions of the layout `σ`, every value of a
    source run of `m` is read back by `σ` from a halting run of `prog` on `aMachine`, with
    the stack register restored and the memory outside the stack frame and the pointer
    regions unchanged, or, for a program that calls a linked function, from a halting run
    through the call. The statement is partial correctness: it concerns source runs that
    reach a value.
  - `haxc_ct_proved_all` (`Haxc/ComposeCTStraight.lean`), constant time: for a result of
    `compileA`, every decoding of the bytes is constant time under `ctRegime` between entry
    states that satisfy the regions of `σ` and a precondition `Pre`, agree on its public
    data and from which the module has a source run, given four hypotheses: constant time
    of the translation `haxToNF` (`HaxToNFCTLOn`, a semantic statement about the translated
    program), termination of the prepared source at one fuel on every such entry state
    (`hterm`), labels that agree with the public data of the layout (`PubLabelsOK`) and
    distinct layout names. `haxc_ct_proved_all_of_check` is the same statement with the
    Boolean level check `haxToNFCTBL … = true` in place of `HaxToNFCTLOn`, which it derives
    through `haxToNFCTL_of_haxToNFCTBL`; `haxc_correct_auto_ct_proved_all` joins it with
    value correctness.
  - `haxc_gate_proved_all` and `haxc_rc_proved_all` (`Haxc/RCInstance.lean`): from the
    level check `haxToNFCTBL` and termination of the source on every entry state satisfying
    the regions of `σ` (`hterm`), every decoding of the bytes satisfies the gate conclusion
    `GateConclusion` of CatCrypt-core's `CatCryptCore.Crypto.RCGate` (value correctness and
    constant time together). `haxc_rc_proved_all` restates the gate conclusion as
    `RobustCompilation 0` between the real observation (the result that `σ` reads back from
    the target and the leakage trace of `prog`) and an ideal observation whose trace the
    choice simulator `RCGate.simLeak` (defined by `Classical.epsilon`) picks from the
    public projection `pubOf σ`; a context only chooses the entry state. The conjunct is
    `RCGate.rc_of_gate` at the gate conclusion and determinism of the target result
    (`haxcTgtRes_det`), and it holds for every compiler that satisfies the gate conclusion
    with a deterministic target.

  For a result that pairs an array with one of its words, `haxc_correct_auto_tuple`
  (`Haxc/ComposeTuple.lean`) is the value statement, and `haxc_correct_auto_ct_proved_all`
  and `haxc_correct_auto_tuple_ct_regions` (`Haxc/ComposeCTStraight.lean`) state value
  correctness and constant time together. The worked instances are
  `mpn_and_n_correct_auto` (`Haxc/AndNCorrect.lean`), `ltu_correct_auto`
  (`Haxc/LtuCorrect.lean`), and `mpn_and_n_correct_auto_ct_regions`,
  `mpn_and_n_rc_proved` and `ltu_rc_proved` (`Haxc/WorkedKernelCorollaries.lean`). Each
  keeps the acceptance `compileA … = some (P, bytes)` and, where it states constant time,
  the level check `haxToNFCTB … = true` as hypotheses; `mpn_and_n` is at the layout
  `andAbi4` of three 4-word arrays (`n ≤ 4`).
- `compileA` (`Haxc/ComposeV1.lean`) is `compileARegion` at the pair stage `pairStage m σ`,
  which strips a tail `let y = a[k]; (a, y)` of the entry; `compileARegion` is the region
  compiler `NFEntry.compileR` at the hax entry `haxEntry` and the data of the linked
  functions of the module. Its front is `haxToNF` (`Haxc/NFChain.lean`), whose domain check
  is `HaxModule.refusal?`; its chain is `extChain` (`Haxc/ExtChain.lean`); its back half is
  `compileRegion` (`Haxc/RegionBackend.lean`), with the gate `regionCoB` and the leakage
  checks `regionCtB`. `haxc_correct_auto` is `correct_of_compileARegion` at the pair stage,
  through `compileRegion_correct`. The compile line is
  `compileA = haxToNF → extChain → compileRegion`, and `compileRegion` is the only back
  half; the field modules compile through it as well.
- The image route `CellFoldLReg.routeBW` (`X86Backend/CellFoldLReg.lean`,
  `loop_image_bytesW`) covers loops with carry chains and cell accesses, with a width
  analysis that joins one-bit names at labels (`seedAt`, `imgGateBW_of_old` in
  `X86Backend/ImageAddrSimW.lean`). Inside `routeBW` the call of `ownedCheckMC` is the
  translation validation of register allocation and the other conjuncts are decided
  side conditions, so the route has one validated step. `straightRegW_bytes`
  (`X86Backend/ImageStraightRegW.lean`) takes a register-returning straight-line
  program over `printedAddrWB` to the bytes, and `straightRegW_bytes_ct` is its
  constant-time statement. No stage of `compileA` calls these image routes.
  The compare reload: `cmpReload`
  (`X86Backend/CmpSpillReload.lean`) rewrites a compare whose first operand is a spill
  slot into a copy to the scratch register and a compare on it, and the printed program
  `printedLprog` (`Haxc.BackHalfBase`) passes every body through it. Its semantic
  theorem `cmpReload_lsemFuelMemF` holds for a body accepted by the decidable check
  `cmpReloadOK` (the body is free of the scratch register and of `MULX`). `cmpReload_of_checked` (`X86Backend/CmpSpillEncodable.lean`) shows that the pass
  is the identity on a body the checked encoder accepts.
  `fieldChain_correct_auto` (`Haxc.FieldLowerChain`) composes the field chain front
  with `compileRegion` at every limb count and modulus record, with the front and compile
  equations as hypotheses.
  The constant-time conclusion of `haxc_ct_proved_all` is
  derived from constant time of the translation (`HaxToNFCTLOn`) through the region chain
  (`regionChain_bytes_ct`): the chain passes (`haxToNFCT_of_haxToNFCTB`), the export
  (`regionRef_memFCT`), allocation and printing by translation validation
  (`regionImage_memFCT`) and the bytes (`regionChain_bytes_ct`); `compileRegion` returns
  bytes only if the leakage checks `regionCtB` accept the printed body.
  On a module with linked functions, the calls of the calling body are covered by the
  leakage check `calleeCtB` and `ctCheckRX_sound`. The instances `mpn_and_n_rc_proved` and
  `ltu_rc_proved` (`Haxc.WorkedKernelCorollaries`) are `haxc_rc_proved_all` at `mpn_and_n`
  (layout `andAbi4`) and at `ltu`, with the acceptance by `compileA` and the level check as
  hypotheses. For a loop of field multiplications, `fieldRegionFront_nfCT` (`Haxc.FieldLoopCT`) derives
  the constant-time property of the region program from the level check of the lowered
  program, and `regionChain_bytes_ct` carries it to the bytes of `compileRegion`.
- On `Lprog`, `LprogGpRealloc` re-allocates general-purpose
  registers with an untrusted allocator whose decisions a checked pass validates.
  `ConstIndexFold` rewrites each register-indexed load and store with a known index
  into displacement form (`gatherPrinted_constIndexFoldBody`). Two passes have a
  constant-time module: `LprogGpReallocCT` shows that the re-allocation introduces no
  register-indexed access, and `ConstIndexFoldCT` that the fold and the dead-move
  elimination leave the `runBlock` leakage trace unchanged. `OptimizeBasicBlocksCT`
  gives a body on which copy propagation followed by the gather introduces a
  secret-indexed load. `X86Backend/DecodedCT.lean` checks constant time at the
  shipped bytes.
- The tactic `kernel_rfl` (`CatCrypt/Tactic/KernelRfl.lean`) proves a straight-line
  `semScalar` run lemma by one kernel evaluation of `ScalarStraightRun.runProg`.
  `word_bound` (CatCrypt-core module `CatCryptCore.Tactics.WordBound`) closes
  word-bound side goals.

[HEADLINES.md](HEADLINES.md) lists the headline theorems, and
[NAVIGATION.md](NAVIGATION.md) the directories that hold them.

### Routes as runs of certified pass chains

`VIR/PassChain.lean` defines a chain `Chain P Q` of named steps, its run (the
composite of the steps in `Option`), a certificate `Cert c S T` with one step
certificate per step against semantics `S` and `T`, and `PassChain.Cert.sound`: when
the run of `c` on `p` returns `q`, inputs related by the certificate give outputs
related by it. `PassChain.Cert.ct` is the leakage form. Each high-tier route of `haxc`
is defined as the run of a chain, and the denotation theorem of the route is
`Cert.sound` of the chain's certificate. The shared pieces `comSemOf`, `routeSem`,
`straightStep` and `straightCert` are in `Haxc.RouteChain`.

| Route (module) | Chain and its steps | Certificate and `Cert.sound` consumer | Route theorem |
|---|---|---|---|
| `extChain D` (`Haxc.ExtChain`) | `extChain D`: tuple flattening `flatSameStep`, then `extChainCore D`: output-type check `outTyStep`, `dceStep`, `extCallStep D` (`nfToCatExt` at the declared procedures `D`), `aegraphStep catRules`, `mapStep catToJasmin`, `montifyStep`, `fieldDialectStep`, `lowerSelectsStep`, `rangeNFStep`, `aegraphStep jasminRules`; on a program whose flattening `nfToCat` translates after `dceStep`, it returns what `nfChainPre` returns on the flattened program (`extChain_run_of_nfToCat`) | `extChainCert`, `extChain_denote` | `haxc_correct_auto` |
| `compileField P` (`Haxc.FieldRoute`) | `fieldChainId P` = `limbChainVia (Step.id _) (GoodVB P) (fieldCom P)`: optimisation slot, limb step, identity, `straightStep` | `limbChainViaCert`, `limbChainVia_denote` | `compileField_denote` |
| `compileFieldS S` (`Haxc.FieldRoute`) | `fieldChainSId S` = `limbChainVia (Step.id _) (GoodLB S) (fieldComOf (lowerOpL S))` | `limbChainViaCert`, `limbChainVia_denote` | `compileFieldS_denote` |

The optimisation slot of the field chains is the identity step. A route theorem that keeps
the compile hypothesis holds for every program the back half accepts on that route.
[FIAT_TEMPLATES.md](FIAT_TEMPLATES.md) has the tables per instance.

### Proofs, checks and translation validation in `haxc`

Each leg of `haxc` is a theorem whose hypothesis on the program is a check that the
compiler runs: for a body accepted by the check, the theorem gives the simulation. The
compiler returns `none` when a check fails, so the theorems range over the programs it
accepts. The route to the Jasmin dialect is the chain `extChain` of the previous
subsection, with `extChain_denote`. The checks are of two classes.

- Class D: a decidable predicate on one program, with a soundness theorem. It is the
  side condition of a proved pass.
- Class V: a check that compares the output of a transformation with its input, with a
  soundness theorem for accepted pairs. Register allocation is the class V step of the
  design.

In the table, a name given with a `Haxc.*` module is in
`CatCrypt/Crypto/SecureCompilation/Haxc/`.

| Statement proved | Programs | Check and class | Lean names |
|---|---|---|---|
| An accepted command lies in the guarded coverage fragment `IsCoveredSCtlGuarded` | `LowCT` commands accepted by `coveredGuardedB` | `coveredGuardedB`, D | [`isCoveredSCtlGuarded_of_coveredGuardedB`](CatCrypt/Crypto/SecureCompilation/Dialects/TranslateDialectGuarded.lean) |
| The typed chain of the export, run by `lsemFuelMemF` from the ABI entry, halts with the return register holding the denotation of the program | straight-line programs returning a register, accepted by `straightCertB` | `straightCertB`, D | [`straight_export_faithful_abi`](CatCrypt/Crypto/SecureCompilation/X86Backend/ExportCertStraight.lean) |
| The certified loop node halts under `lsemFuelMemF` from the ABI entry with the output array decoding to the denotation of the program | a program with one runtime-count loop accepted by `singleLoopB` | the export certificate `comLCertNB` (`routeCertB`), V: a certificate, per program, of a fixed export function | [`singleLoop_export_faithful_gate`](CatCrypt/Crypto/SecureCompilation/X86Backend/ExportCertGate.lean) |
| Every halting run of the checked machine on a body from program counter `0` is matched by a halting run of the optimised body from the same state, with at most the same fuel, to a state with the same function name and zero flag and a base equal up to the program counter | whole bodies with labels under the block optimiser `optimizeBasicBlocks`: bodies accepted by `optBlocksMoveFreeOKB`; bodies accepted by `optBlocksOKB`, from states of the bridge invariant `RelInv`; bodies accepted by `keepOKB` with register destinations, given `CopyPropSim` at each straight segment | `optBlocksMoveFreeOKB`, `optBlocksOKB`, D | [`optBlocksMoveFreeOKB_sound`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean), [`optBlocksOKB_sound`](CatCrypt/Crypto/SecureCompilation/X86Backend/OptBlocksComplete.lean), [`optimizeBasicBlocks_wholeBodySim_of_copyPropSim`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean) |
| A pass applied to the straight segments of a body gives the same simulation on the whole body; the scheduler, store-to-load forwarding, spill-pair removal and load CSE are instances | bodies with labels accepted by `keepOKB`, with register destinations for forwarding and load CSE | `keepOKB`, D | [`lsemFuelMemFk_blockRel`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/CfgLift.lean), [`mapStraightRuns_lsemFuelMemF`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean), [`scheduleBody_lsemFuelMemF`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean), [`elimReloads_lsemFuelMemF`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean), [`reloadElimBody_lsemFuelMemF`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean), [`loadCSE_lsemFuelMemF`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean) |
| The fold of a body gathers, and the two blocks run to the same machine state and have the same leakage trace from every initial state | bodies that gather under `gatherPrinted`, under the constant-index fold, on `runBlock` over `JInstr` | `gatherPrinted` | [`foldInstr_lower`](CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFold.lean), [`KEnv.Holds.stepK`](CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFold.lean), [`foldCore_gather`](CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFold.lean), [`gatherPrinted_constIndexFoldBody`](CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFold.lean), [`foldInstr_lower_leak`](CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFoldCT.lean), [`gatherPrinted_constIndexFoldBody_leak`](CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFoldCT.lean) |
| A body and its two-address form, run from one state, end with equal memory and equal values at every name other than the save slot | every body, at `lsemStraight`; `twoAddrBody` is the identity on a body accepted by the printer precondition `twoAddrOK` (`bodyTiedOk`) | `bodyTiedOk`, D | [`twoAddrBody_lsemStraight`](CatCrypt/Crypto/SecureCompilation/X86Backend/TwoAddrLegalize.lean), [`twoAddrBody_of_bodyTiedOk`](CatCrypt/Crypto/SecureCompilation/X86Backend/TwoAddrLegalize.lean) |
| Every halting run of `B` from a state at program counter `0` is matched by a halting run of `B'` from the same state, and the end states agree on the registers `outs`, on the arrays and on the word memory; `ownedCheckML` adds equal leakage traces | pairs `B`, `B'` accepted by `ownedCheckM`, by `ownedCheckMC` (bounds-checked runs) or by `ownedCheckML` (traced runs): the output of register allocation `reallocLprog` against its input | `ownedCheckMC`, `ownedCheckML`, V | [`ownedCheckM_sound`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedLprogTV.lean), [`ownedCheckMC_sound`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedLprogTVChecked.lean), [`ownedCheckML_sound_leak`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedTVLeak.lean) |
| `ownedCheckM` accepts the fold of a body against the body, and a body against its two-address form | non-empty straight-line bodies whose symbolic run lies in the fragment of the checker; for the two-address form, instructions accepted by `twoAddrRouteWF` | `twoAddrRouteWF`, D | [`foldIndexed_ownedCheckM_complete`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedLprogTVDeadImm.lean), [`twoAddr_ownedCheckM_complete`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedLprogTVTwoAddr.lean) |
| Every halting run of a typed body `pre ++ loop` is matched by a halting run of `pre ++ fuseMulHiRM loop` from the same state, with at most four times the fuel | typed bodies accepted by `fuseOKL`, from a base whose registers in the checked list have width 64 | `fuseOKL`, D | [`fuseMulHi_lsemFuelMemF_pre`](CatCrypt/Crypto/SecureCompilation/VIR/JasminLsemFuseMulHi.lean) |
| Every halting run of a function body without its return is matched by a run of the body that the owned back end `ownedLprog` gives it (block optimiser, constant-index fold, register re-allocation, two-address form), with at most five times the fuel, to a state related to the source state by `OwnedObs` (equal function name, flags and word memory, equal arrays off the slot arrays, equal result registers, slot arrays held in their cells) | functions ending in a return whose bodies pass `optBlocksOKB`, `FoldIndexedOK`, `reallocCfgOKB` and `twoAddrOK` | `optBlocksOKB`, `reallocCfgOKB`, `twoAddrOK`, D | [`ownedLprog_lsemFuelMemF`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedLprogFuel.lean) |
| The same for the printed program `printedLprog` (the owned back end followed by the compare reload `cmpReload`), with at most ten times the fuel; the deadWriteRet half and the whole fusion post-pass `regionPostFuse` on programs | as above, with `cmpReloadOK`; for the post-pass, bodies passing the dead-write checks and the fusion check, read through `normMulx` | `cmpReloadOK`, `fuseMulHiOK`, D | `printedLprog_lsemFuelMemF` (`Haxc.PrintedLprogFuel`), `regionPostFuse_lsemFuelMemF` (`Haxc.RegionPostFuseLift`) |
| The printed program of `compileRegion` is `printedLprog (regionPostFuse P0)` for the allocation `P0` of the allocation stage `regionAllocC` | every program `compileRegion` accepts | none | `regionImage_split` (`Haxc.RegionLprogSplit`) |
| Each instruction of the lowering core and its lowering simulate one another up to agreement off the two scratch registers | instructions accepted by `lowerCoreOKB`: two-address operations and conditional moves over registers, two-address operations with a register destination and a spilled second source, one-source legalisation, loads without a spilled base or index | `lowerCoreOKB`, D | [`simS_lowerCore`](CatCrypt/Crypto/SecureCompilation/X86Backend/LowerFuelMemF.lean) |
| A halting run of a body is matched by a halting run of the body framed by the prologue (with the saves of the third and later arguments) and the callee-save restore, with the callee-saved registers restored from their slots | bodies with labels and jumps accepted by `frameInstrOKB`: no scratch register, no save slot, no return, call or base reload | `frameInstrOKB`, D | [`frame_lsemFuelMemF`](CatCrypt/Crypto/SecureCompilation/X86Backend/FrameFuelMemFCfg.lean) |
| Every checked run of the image of the cell body is matched by a run of the address machine on the body, in the image relation with one-bit carries | bodies free of conditional branches whose cell body is accepted by `imgGateBW` and `physImgB`, the physical half of the register-allocation pair | `imgGateBW`, `physImgB`, D | [`image_addr_simBW`](CatCrypt/Crypto/SecureCompilation/X86Backend/ImageAddrCells.lean) |
| Every terminating run of the address machine on the body is matched by a halting run of the machine on the decoded function bytes, with the stack register restored, from entry states related register by register and with equal memory, on runs whose indexed loads miss the red-zone word (`RunSafe`, which `image_addr_simBW` discharges on the route) | printed bodies in the class `printedAddrWB` (with carry chains) or `printedAddrB` | `printedAddrWB`, `printedAddrB`, D | [`printedAddr_simW`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodePrintedAddrW.lean), [`printedAddr_sim`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodePrintedCFG.lean) |
| The function bytes of a body decode to its layout `fundefLayout`, and the bytes of the gated encoder decode to the program `p` | bodies accepted by `decodableLcmd`; bodies accepted by `decodesToB` at `p` | `decodableLcmd`, `decodesToB`, D | [`decodeLprog_encodeLfundefBytes`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodeLayout.lean), [`decodeLprog_of_decodesToB`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodeLayout.lean) |
| Every halting run of `lsemFuelMemF` from a state whose registers satisfy the entry facts is in bounds | bodies accepted by the abstract interpretation `idxInvCheckB` | `idxInvCheckB`, D | [`runIdxOk_of_idxInvCheckB`](CatCrypt/Crypto/SecureCompilation/X86Backend/IdxInvCheck.lean) |
| The decoded function bytes of the printed body are constant time when the source events of the single-loop program are | printed bodies accepted by the route check `routeB` with `ownedCheckML`, with the branches of the loop guard and back edge | `routeB`, D, with `ownedCheckML`, V | [`route_bytes_ct_loop`](CatCrypt/Crypto/SecureCompilation/Haxc/ComposeCTProved.lean) |
| The bytes decode to a program whose runs from entry states that satisfy the regions of the layout, agree on its public data and from which the source runs have equal leakage traces | a source accepted by the level check, and a printed body accepted by `regionCtB` in the gate of `compileRegion` | preservation along the region chain, with translation validation at allocation and printing | `regionChain_bytes_ct` (`Haxc.ComposeCTStraight`) |

On the image routes `ImageAddrRoute.routeB` and `ImageStraightCells.straightCellB`, which
are not stages of `compileA`, one
call of `ownedCheckMC` compares the reference chain with the image of the printed body. The
printed body is the output of the export, the post-pass `fuseMulHiLprog` and the owned
back end `ownedLprog`. For a pair accepted by this call, `ownedCheckMC_sound` therefore
gives the simulation across the block optimiser, the constant-index fold, the
two-address form, the post-pass and register allocation together. The reference side
applies the fusion as `fuseMulHiRM`; for a typed body accepted by `fuseOKL`,
`fuseMulHi_lsemFuelMemF_pre` gives its run.

For a result of `compileA`, under the hypotheses listed for them above (constant time of
the translation or the level check `haxToNFCTBL`, termination of the source at one fuel,
`PubLabelsOK` and distinct layout names), `haxc_ct_proved_all` and `haxc_rc_proved_all`
(`Haxc.ComposeCTStraight`, `Haxc.RCInstance`) give constant time and the gate conclusion
of every decoding of the bytes. `compileA` compiles a structured program, and constant
time of the decoded program follows from constant time of the translation through the
region chain (`regionChain_bytes_ct`).

### Reference semantics of prime-ir calls

The hax interpreter reads a prime-ir field call under the builtin table
`primeirBuiltins p` (`CatCrypt/Hax/PrimeirBuiltins.lean`), which interprets the heads
`mul`, `add`, `sub`, `neg`, `square`, `double` and `inv` on integer arguments modulo
`p`. The extraction emits bare method names, so an integer `mul`, `add` or `sub` and
the field operation of the same name share a head. The field route's theorem
`field_correct_auto` (`Haxc.FieldCorrect`) is stated against
`primeirBuiltins p`, which is the semantics of the source for a function whose
integer-typed calls with these names are field calls. The name table
`defaultFieldTable` (`CatCrypt/Hax/PrimeirNames.lean`) lists the qualified names
beside the bare ones.

## Ascent: correspondence from given code to a specification

Ascent takes existing code, extracted or shipped, and proves a correspondence from
its runs to a Lean function. A second, ordinary proof equates that function with the
handwritten specification. Ascent has two instances, which share one calculus in the
style of AutoCorres.

- In the ascent on extracted Rust (the library `HaxAscent`, which imports Lean, Std,
  Batteries, hax-lean and the refinement module `CatCryptCore.Refinement.Programs` of
  CatCrypt-core; judgement and generator in `HaxAscent/Ascent/`, index
  [CatCrypt/Hax/AGENTS.md](CatCrypt/Hax/AGENTS.md)), `FnCorres bi e entry G f` relates
  the `denote'` run of an `ImpExpr` literal under the builtin table `bi` to a shallow
  function `f`. The generator `Hax.Ascent.Gen.ascendFn` produces `f` and its
  correspondence with no hand-written loop specification. The entry point
  `hax_ascend Ns` runs the generator over a whole haxpipeT extraction and declares
  `Ns.HaxGen.f.gen`, `Ns.HaxGen.f.corres` and `Ns.HaxGen.f.corres_full` per function.
  `#hax_coverage Ns` reports per function. For one literal, the entry points are
  `ascend_reified` and `hax_corres`. A function generic over a trait is monomorphised at
  the extraction's instances (`Monomorphise.lean`, `fnCorres_monomorphise_iff`), and
  `hax_ascend` declares `Ns.HaxGen.f.corres_generic` for the generic literal.
- In the ascent on `LowCT`, x86 and RV64
  (`CatCrypt/Crypto/SecureCompilation/Ascent/`), the judgements `Corres`, `CorresJ` and
  `CorresR` relate a `LowCT` command, an x86 block or an RV64 block to a function on words,
  integers or field elements. `CorresIsa` is the same judgement at the instruction-set
  interpreter `Isa.lsemFuelMemF` (x86-64, AArch64, RV64); `corresIsa_x86_of_corresJ` and
  `corresIsa_arm_of_corresJ` transport a `CorresJ` result to it for blocks whose
  registers and memory do not depend on the flags. Its tactics are `ascend!`, `ascend_expr!`,
  `corres_solve_scalar`, `corres_sym`, `corres_sym_rv` and `mont_bound`.
  [ASCENT.md](ASCENT.md) is the guide, [ASCENT_REFERENCE.md](ASCENT_REFERENCE.md) the
  reference, and [CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md) the
  procedure for third-party machine code.
  [ASCENT_OVERVIEW_HIGHLEVEL.md](ASCENT_OVERVIEW_HIGHLEVEL.md) gives the design, its
  categorical form and its relation to verification-condition generation;
  [ASCENT_OVERVIEW_LEAN.md](ASCENT_OVERVIEW_LEAN.md) maps it to the declarations.

## Transfer: parametricity across representations

Transfer moves a proved statement across a registered relation between an abstract
value and its representation (`ZMod p` and limbs, `UScalar` and in-range `Int`, a
group and its bytes). The engine is the
[ParamTransfer](https://github.com/spitters/ParamTransfer) package (namespace
`Transfer`), a port of Trocq's graded parametricity with `Param (m n) A B`,
`Related enc a b` and `RelatedBinOp`. Its tactics are `param_transfer` and `#transfer`,
which transfer statements and terms; `param_solve` and `rcongr`, which prove a
`Related` goal by descent through registered squares; and `param_auto`, the
coordinating cascade. The README and the tactic guide of that package document them.

A guarded square has a side condition that constrains the abstract operands, such as
`b ≤ a` at `a - b`; a total square is a guarded square with guard `True`. The engine
registers guarded squares as `RelatedBinOpOn`, `RelatedUnOpOn` and `RelatedRelOn`
(ParamTransfer module `Transfer.Base.RelatedOn`). The tactic `param_guard` composes
them and discharges each guard with `transfer_guard_disch` or leaves it as a goal.

In this package, `CatCrypt/Crypto/Bridges/Transfer/HaxIntTransfer.lean` registers bounded
field models of hax integer limbs as ParamTransfer relations,
`CatCrypt/Crypto/Bridges/Transfer/CompilerRegistry.lean` registers the compiler's
preservation lemmas, and `VIR/ParamDescent.lean` and `VIR/ParamDialectTransport.lean`
certify dialect-lowering squares by `param_solve`.

## Choosing a technique

| Situation | Technique |
|---|---|
| New kernel or Rust code that the compiler emits | descent; the source is the specification |
| Extracted Rust function `f` against a handwritten specification | ascent on `ImpExpr` (`hax_ascend`), then equate the generated function with the specification |
| Existing machine code (hand-written, CryptOpt, s2n-bignum) | ascent on x86 |
| Specification and code differ in representation | transfer, after ascent or descent |
| A proved fact needed at another representation | transfer |

For an extracted function `f`, the procedure has four steps: extract with haxpipeT
(`--emit-certified`, or `--emit-classes` for trait-generic code), run
`hax_ascend Ns`, read `#hax_coverage Ns`, and prove `Ns.HaxGen.f.gen` equal to the
specification. The last step uses transfer where the specification is stated over
`ZMod p` or `Int` and the code over words. When the generator reports a function as
failed, the report names the construct, leaf or loop that needs a new rule. Passing
the same extraction through the hax front also yields the emitted bytes.

## Composition of the techniques

The welds are in `CatCrypt/Crypto/SecureCompilation/Ascent/`:

- Over one `LowCT` command that reads no entry variable, `Ascent.legWeld` joins the
  descent refinement `RRefines spec c`, the ascent square `Corres SRwordNT P fa c` and the
  emit leg `rustToJasminCom_endToEnd_unconditional`. Its conclusion is that the emitted
  closed Jasmin program denotes the source step's output word.
- `CorresDescentX86.corres_of_refines_x86` turns a relational-compiler result
  `Refines spec frag` into a simulation of the compiled `ScalarTarget` x86 block under
  `xrun`: from a state reflecting the view, the result register holds slot `dst` of `spec`
  applied to the view, given `ComOK` and `ShiftAmtOK`; `CorresDescentRiscv.corres_of_refines_riscv`
  is the RV64 form, given `ComOK`.
- `Ascent.feSub_raw_source_to_bytes` states hax-lean's `pipeline_correct` for an
  `ImpExpr` whose output word is the constant `feSubSourceWord`, next to the `feSub`
  source tower, which ends at the Jasmin-dialect denotation of the closed kernel `feJcom`;
  the two parts are joined only through that constant, and no conjunct reaches bytes.
- The ascent on `ImpExpr` and the compiler's theorems for the machine code meet at a
  common Lean function: `fnCorres_enc_unique` (`HaxAscent/Ascent/FnCorresUnique.lean`)
  states that two correspondences of the same extracted body, entry and guard have equal
  encoded results at every argument satisfying the guard.
  [ASCENT_OVERVIEW_LEAN.md](ASCENT_OVERVIEW_LEAN.md) and
  [CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md#the-ascent-against-a-hax-reference)
  give the composition.

Transfer enters both other techniques as a proof step: descent certifies dialect
lowerings by `param_solve`, and an ascent result over words reaches a specification
over `ZMod p` through a registered relation.

## Axioms of a theorem

[BUILDING.md](BUILDING.md#check-axioms) describes how to print the axioms on which a
theorem rests; `AxiomAudit.lean` collects the commands for the end-to-end theorems.
