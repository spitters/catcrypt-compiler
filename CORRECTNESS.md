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

The workspace builds against two siblings of this package, the development repository
(CatCrypt) and the ParamTransfer package. Paths below are relative to this package
unless the text names another package.

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
per instance (`boundsOk` with `denote_eq_denoteZ_of_boundsOk`, `SchedOk`), and one bytes
theorem per family (`field_correct_bytes`, `ec_correct_bytes`) whose only per-instance
hypothesis is acceptance by the decided gate of `backend_correct` of the earlier back half
`compileJ`. The
families with a template are fields, lattices, GHASH, towers, RSA and isogeny moduli.
[FIAT_TEMPLATES.md](FIAT_TEMPLATES.md) gives the instance tables with the accepted
programs, the measured ratios against fiat-crypto and the size of the template layer.

- The legacy hax front `haxToLowCT` in `CatCrypt/Crypto/Hax/`, a front of the kernel
  producers outside the pipeline of `compileA`, lowers hax-lean's `ImpExpr` to `LowCT`
  (`haxToLowCT_simulates_program` and its array, tower and literal variants). The
  typed entry point `haxFrontT` (development repository,
  `CatCrypt/Crypto/Hax/HaxFrontT.lean`, `haxFrontT_simulates`) places each name by
  its type. Early exits lower to exit-flag form. `scalarizeExitIn`
  (`CatCrypt/Crypto/Hax/HaxToLowCTExitWordOps.lean`) replaces marshalled word calls by
  scalar assignments and unsigned comparisons by their signed forms. `placedUse`
  (`CatCrypt/Crypto/Hax/HaxToLowCTPlaced.lean`) checks that every name is used in the
  heap of its placement. [HAX_RUST.md](HAX_RUST.md) gives the procedures.
- In the Jasmin `.jinc` importer (`CatCrypt/Crypto/Jasmin/`), `JincParser` and
  `JincToCom` read the straight-line fragment, `JincElab` elaborates it to
  `Com jasminDialect`, and `JincToLowCT` emits `for` and `while` as the loop nodes
  `RFor` and `RWhileNz`. `JincInline` partially evaluates a Jasmin source unit
  (inlining, constant folding, scalar replacement of register arrays).
  `importFunRolled` keeps a loop over an affine counter rolled, as a loop over a
  run-time trip index. The correctness theorem of an imported leaf is stated over the
  `LowCT` or `Com` that the import produces. `KeccakJincImport` takes formosa-keccak's Keccak-f[1600] through this path.
- The scalar front's denotation theorems (`transU_denote`, `frontLoopBodyJ_denote`)
  assume the coverage fragment `IsCoveredSCtl`. `coveredB` and
  `isCoveredSCtl_of_coveredB` (`CatCrypt/Crypto/SecureCompilation/Dialects/CoveredSCtlDecide.lean`)
  discharge it by `decide`.
- The end-to-end theorems are `rustToJasminCom_endToEnd_unconditional`
  (`VIR/CompilerCorrectnessExtracted.lean`), `robustCompilation_source_to_x86`
  (`VIR/RobustCompilationPipeline.lean`; value correctness, no constant-time
  conjunct), and the straight-line demonstrations `com_x86_e2e`, `com_arm_e2e` and
  `com_riscv_e2e`. The three demonstrations compile a straight-line, register-only
  `Com` through the `ScalarTarget` instruction selection (`ScalarLin.lean`).
  [HEADLINES.md](HEADLINES.md) states each with its hypotheses.
- The hax compiler `haxc` (development repository,
  `CatCrypt/Crypto/SecureCompilation/Haxc/`; its layout type `AbiLayout` is in this
  package) composes the hax front, the route to the Jasmin dialect, the export to
  `Lprog`, the owned back end and the encoder, and ends at decoded x86 bytes run by the
  address machine `aMachine`. Its general theorems quantify over every extraction the
  compiler accepts. `haxc_correct_auto` (`ComposeV1.lean`) and, for a result that pairs
  an array with one of its words, `haxc_correct_auto_tuple` (`ComposeTuple.lean`) state
  that every run of the source reading to a value is matched by a halting run on the
  decoded bytes that reads the value back. `haxc_correct_auto_ct_proved_all` and
  `haxc_correct_auto_tuple_ct_regions` (`ComposeCTStraight.lean`) add constant time of
  the decoded program over runs from entry states that agree on the public data of the
  layout. The instances are `mpn_and_n_correct_auto` and
  `mpn_and_n_correct_auto_ct_regions` (`AndNCorrect.lean`, `ComposeCTStraight.lean`),
  `ltu_correct_auto` and `ltu_rc_proved` (`LtuCorrect.lean`, `ComposeCTStraight.lean`),
  and `mpn_mul_1_correct_auto` and `mpn_mul_1_correct_auto_ct_regions`
  (`Mul1Correct.lean`, `Mul1CorrectCT.lean`).
- The compiler entry of `haxc` (modules `Haxc.*` are in the development repository) is
  `compileA`, defined as `compileA m σ fname := compileARegion m σ fname`, with
  `haxc_correct_auto` (`Haxc.ComposeV1`). Its front is `haxToNF` (`Haxc.NFChain`), whose
  domain check is `HaxModule.refusal?`; its chain is `extChain` (`Haxc.NFChainCall`); its
  back half is `compileRegion` (`Haxc.RegionBackend`), with the one gate `regionCoB` and
  the leakage checks `regionCtB`. `haxc_correct_auto` is `NFEntry.compileR_correct` at
  `haxEntry`, through `compileRegion_correct`.
- The earlier back half is `compileJ` (`Haxc.BackHalf`), with the gate `jGateB` and the
  theorem `backend_correct`; `compileA` does not call it, and the field-level byte
  theorems take a hypothesis on it. `backend_correct` is stated over a back-end
  record `ByteTarget` (machine with halting relation, printed program, legality check,
  encoder, layout reading, gate, soundness of the gate); the x86 value `x86ByteTarget`
  is the default of `backEnd` and `compileJ`.
  `jGateB` consists of the image arms of `imageArmB`: six straight
  image arms (register, array, cell, fused cell, and the register arm `v1StraightRWB`
  over the printed class `printedAddrWB`, plain and fused) and two loop image arms
  (`v1LoopB` and `v1LoopWB`), each conjoined with its check on traced runs. The route
  check of `v1LoopWB`, `CellFoldLReg.routeBW` (`X86Backend/CellFoldLReg.lean`,
  `loop_image_bytesW`), covers carry chains and cell accesses, with a width analysis
  that joins one-bit names at labels (`seedAt`, `imgGateBW_of_old` in
  `X86Backend/ImageAddrSimW.lean`). Inside `routeBW` the call of `ownedCheckMC` is the
  translation validation of register allocation and the other conjuncts are decided
  side conditions, so the route has one validated step. `straightRegW_bytes`
  (`X86Backend/ImageStraightRegW.lean`) takes a register-returning straight-line
  program over `printedAddrWB` to the bytes, and `straightRegW_bytes_ct` is its
  constant-time statement. The compare reload: `cmpReload`
  (`X86Backend/CmpSpillReload.lean`) rewrites a compare whose first operand is a spill
  slot into a copy to the scratch register and a compare on it, and the stages
  `backEnd` of `compileJ` print every body through it (`printedLprog`). Its semantic
  theorem `cmpReload_lsemFuelMemF` holds for a body accepted by the decidable check
  `cmpReloadOK` (the body is free of the scratch register and of `MULX`). The gate
  checks the rewritten body against the source program, so the validation of register
  allocation covers the rewrite. `cmpReload_of_checked` (`X86Backend/CmpSpillEncodable.lean`) shows that the pass
  is the identity on a body the checked encoder accepts.
  `fieldChain_correct_auto` (`Haxc.FieldLowerChain`) composes the field chain front
  with `compileJ` at every limb count and modulus record; its instances
  `powLoop_correct_bytes_pow_1` and `powLoop_correct_bytes_pow_p256`
  (`Haxc.PowLoopBytes`, `Haxc.PowLoopBytesP256`) take the route and compile equations
  as hypotheses, each pinned by a known-answer check. The
  tuple entry `compileAT` (`Haxc.ComposeTuple`) calls `compileA`.
  Constant time of the bytes: for every result of `compileA`, `haxc_ct_proved_all`
  (`Haxc.ComposeCTStraight`) gives constant time of every decoding of the bytes, between
  entry states that satisfy the regions of the layout, agree on its public data and from
  which the source runs;
  `haxc_correct_auto_ct_proved_all` and `haxc_gate_proved_all` are the
  joint statement with value correctness and the gate conclusion. The conclusion is
  derived from the level check of the source through the region chain
  (`NFEntry.levelCheck_region_bytes`): the chain passes (`NFEntry.regionCT`), the export
  (`regionRef_memFCT`), allocation and printing by translation validation
  (`regionImage_memFCT`) and the bytes (`regionChain_bytes_ct`); `compileRegion` returns
  bytes only if the leakage checks `regionCtB` accept the printed body, and the theorems
  take `m.linked = []`. In the earlier back half `compileJ`, on a straight-line
  or looped route program the conclusion is derived from the level check
  of the front through the passes: the two loop
  arms and the straight
  register, array, cell and carry-chain register arms, through `straightReg_bytes_ct`
  (`X86Backend/ImageStraightLeak.lean`), `straightArr_bytes_ct`
  (`X86Backend/ImageStraightArrLeak.lean`) and `straightCell_bytes_ct_src`
  (`X86Backend/ImageStraightCellsCT.lean`). Each arm of the gate carries the check on
  traced runs `ownedCheckML`, the leakage form of the register-allocation validation.
  `haxc_rc_proved_all` adds robust compilation under the same hypotheses; UC preservation
  follows from its gate conclusion by `uc_of_gate`. In the earlier back half, the
  loop arm `v1LoopWB` goes
  through `loop_bytesW_ct_src` (`X86Backend/ImageLoopWLeak.lean`) and the register arm
  `v1StraightRWB` through `straightRegW_bytes_ct`; `jGate_bytes_ct` and `compileJ_ct`
  (`Haxc.ComposeCTStraight`) state the result for one accepted program of `compileJ`. The instances `mpn_and_n_rc_proved` and `ltu_rc_proved` are
  `haxc_rc_proved_all` at `mpn_and_n` and at `ltu`.
  For a loop of field multiplications, `fieldLoop_routeCT` (`Haxc.FieldLoopCT`) derives
  the constant-time property of the route program from the level check of the lowered
  program, and `compileJ_ct` carries it to the bytes of `compileJ`; the instances
  `powLoop1_ct'` (one limb, `Haxc.FieldLoopCT`) and `powLoop4_ct'` (P-256,
  `Haxc.PowLoopCTP256`) take the route and compile equations as hypotheses, with the
  trip count public.
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
  `word_bound` (CatCrypt-core, `CatCryptCore/Tactics/WordBound.lean`) closes
  word-bound side goals.

[HEADLINES.md](HEADLINES.md) and [NAVIGATION.md](NAVIGATION.md) record the status of
the results, as do `COMPILER_ROADMAP.md` ("Where we are") and `JINC_IMPORT.md` in the
development repository.

### Routes as runs of certified pass chains

`VIR/PassChain.lean` defines a chain `Chain P Q` of named steps, its run (the
composite of the steps in `Option`), a certificate `Cert c S T` with one step
certificate per step against semantics `S` and `T`, and `PassChain.Cert.sound`: when
the run of `c` on `p` returns `q`, inputs related by the certificate give outputs
related by it. `PassChain.Cert.ct` is the leakage form. Each high-tier route of `haxc`
is defined as the run of a chain, and the denotation theorem of the route is
`Cert.sound` of the chain's certificate. The modules are in the development repository
(`Haxc.*`); the shared pieces `comSemOf`, `routeSem`, `straightStep` and
`straightCert` are in `Haxc.RouteChain`.

| Route (module) | Chain and its steps | Certificate and `Cert.sound` consumer | Route theorem |
|---|---|---|---|
| `extChain D` (`Haxc.NFChainCall`) | `extChain D`: output-type check, `dceStep`, `extCallStep D` (`nfToCatExt` at the declared procedures `D`), `aegraphStep catRules`, `mapStep catToJasmin`, `lowerSelectsStep`, `rangeNFStep`, `aegraphStep jasminRules`; at `D = []` it is `nfChainPre` (`extChain_nil`) | `extChainCert`, `extChain_denote` | `haxc_correct_auto` |
| `compileField P` (`Haxc.FieldRoute`) | `fieldChainId P` = `limbChainVia (Step.id _) (GoodVB P) (fieldCom P)`: optimisation slot, limb step, identity, `straightStep` | `limbChainViaCert`, `limbChainVia_denote` | `compileField_denote` |
| `compileFieldS S` (`Haxc.FieldRoute`) | `fieldChainSId S` = `limbChainVia (Step.id _) (GoodLB S) (fieldComOf (lowerOpL S))` | `limbChainViaCert`, `limbChainVia_denote` | `compileFieldS_denote` |
| `jacAddRoute`, `jacDblRoute` (`Haxc.EcRoute`) | `.get` of the run of `fieldChainId P` on `jacAddProg`, `jacDblProg` | through `compileField_denote` | `p256_jacAdd_correct_bytes`, `p256_jacDbl_correct_bytes` and the `C` variants (`Haxc.EcInstances`), with the compile hypothesis |
| `nttRoute`, `inttRoute` (`Haxc.NttRoute`) | `.get` of the run of `lanesChainId N` = `lanesChainVia (Step.id _)`: optimisation slot, `lanesStep`, `straightStep` | `lanesChainViaCert`, `lanesChainVia_denote` | `nttRoute_denote`, `inttRoute_denote` |
| `nttRouteOf A` (`Haxc.NttRouteSel`) | `.get` of the run of `lanesChain N pure`: value numbering `gvnMR pure`, lane lowering, `straightStep` | `lanesChainCert`, `lanesChain_denote` | `nttRouteOf_denote` |
| `latticeRoute`, `basemulRoute`, `pointwiseRoute`, `accRoute` (`Haxc.LatticeRoute`) | `.get` of the run of `lanesChain M pure`; a non-square program is zero-padded to square | `lanesChainCert`, `lanesChain_denote` | `basemulRoute_denote`, `pointwiseRoute_denote`, `accRoute_denote` |
| `towerRoute P N` (`Haxc.TowerRoute`) | `towerChain P N`: identity, `towerStep` (`towerCom` under `towerGoodB`), identity, `straightStep` | `towerChainCert`, `towerChain_denote` | `fp2_mul_correct_bytes`, `fp2_sqr_correct_bytes`; instances at BN254 and BLS12-381 with the compile hypothesis |

The optimisation slot of the field chains is the identity step.

A route theorem that keeps the compile hypothesis holds for every program the back half
accepts on that route. The acceptance registry of the development repository
(`scripts/acceptance-registry.tsv`) records the accepted programs: among these routes,
`Fp2` multiplication and squaring at BN254 (rows `tower/bn254_fp2_mul`,
`tower/bn254_fp2_sqr`), with the constant-time byte gate passing on both.
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

In the table, a linked name is in this package, and a name given with its module is in
the development repository.

| Statement proved | Programs | Check and class | Lean names |
|---|---|---|---|
| The `LowCT` program of the earlier typed front (not a stage of `compileA`) runs to a state whose result slots agree with the value of every source run that reads to a value | typed bodies accepted by `haxFrontTOk` | `haxFrontTOk`, D | `haxFrontT_simulates_hax64W` (`CatCrypt.Crypto.Hax.HaxFrontHax64W`) |
| An accepted command lies in the guarded coverage fragment `IsCoveredSCtlGuarded` | `LowCT` commands accepted by `coveredGuardedB` | `coveredGuardedB`, D | [`isCoveredSCtlGuarded_of_coveredGuardedB`](CatCrypt/Crypto/SecureCompilation/Dialects/TranslateDialectGuarded.lean) |
| The typed chain of the export, run by `lsemFuelMemF` from the ABI entry, halts with the return register holding the denotation of the program | straight-line programs returning a register, accepted by `straightCertB` | `straightCertB`, D | [`straight_export_faithful_abi`](CatCrypt/Crypto/SecureCompilation/X86Backend/ExportCertStraight.lean) |
| The certified loop node halts under `lsemFuelMemF` from the ABI entry with the output array decoding to the denotation of the program | a program with one runtime-count loop accepted by `singleLoopB` | the export certificate `comLCertNB` (`routeCertB`), V: a certificate, per program, of a fixed export function | [`singleLoop_export_faithful_gate`](CatCrypt/Crypto/SecureCompilation/X86Backend/ExportCertGate.lean) |
| Every halting run of the checked machine on a body from program counter `0` is matched by a halting run of the optimised body from the same state, with at most the same fuel, to a state with the same function name and zero flag and a base equal up to the program counter | whole bodies with labels under the block optimiser `optimizeBasicBlocks`: bodies accepted by `optBlocksMoveFreeOKB`; bodies accepted by `optBlocksOKB`, from states of the bridge invariant `RelInv`; bodies accepted by `keepOKB` with register destinations, given `CopyPropSim` at each straight segment | `optBlocksMoveFreeOKB`, `optBlocksOKB`, D | [`optBlocksMoveFreeOKB_sound`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean), [`optBlocksOKB_sound`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean), [`optimizeBasicBlocks_wholeBodySim_of_copyPropSim`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean) |
| A pass applied to the straight segments of a body gives the same simulation on the whole body; the scheduler, store-to-load forwarding, spill-pair removal and load CSE are instances | bodies with labels accepted by `keepOKB`, with register destinations for forwarding and load CSE | `keepOKB`, D | [`lsemFuelMemFk_blockRel`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/CfgLift.lean), [`mapStraightRuns_lsemFuelMemF`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean), [`scheduleBody_lsemFuelMemF`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean), [`elimReloads_lsemFuelMemF`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean), [`reloadElimBody_lsemFuelMemF`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean), [`loadCSE_lsemFuelMemF`](CatCrypt/Crypto/SecureCompilation/VIR/LsemBridgePass/BlocksCfg.lean) |
| The fold of a body gathers, and the two blocks run to the same machine state and have the same leakage trace from every initial state | bodies that gather under `gatherPrinted`, under the constant-index fold, on `runBlock` over `JInstr` | `gatherPrinted` | [`foldInstr_lower`](CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFold.lean), [`KEnv.Holds.stepK`](CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFold.lean), [`foldCore_gather`](CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFold.lean), [`gatherPrinted_constIndexFoldBody`](CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFold.lean), [`foldInstr_lower_leak`](CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFoldCT.lean), [`gatherPrinted_constIndexFoldBody_leak`](CatCrypt/Crypto/SecureCompilation/X86Backend/ConstIndexFoldCT.lean) |
| A body and its two-address form, run from one state, end with equal memory and equal values at every name other than the save slot | every body, at `lsemStraight`; `twoAddrBody` is the identity on a body accepted by the printer precondition `twoAddrOK` (`bodyTiedOk`) | `bodyTiedOk`, D | [`twoAddrBody_lsemStraight`](CatCrypt/Crypto/SecureCompilation/X86Backend/TwoAddrLegalize.lean), [`twoAddrBody_of_bodyTiedOk`](CatCrypt/Crypto/SecureCompilation/X86Backend/TwoAddrLegalize.lean) |
| Every halting run of `B` from a state at program counter `0` is matched by a halting run of `B'` from the same state, and the end states agree on the registers `outs`, on the arrays and on the word memory; `ownedCheckML` adds equal leakage traces | pairs `B`, `B'` accepted by `ownedCheckM`, by `ownedCheckMC` (bounds-checked runs) or by `ownedCheckML` (traced runs): the output of register allocation `reallocLprog` against its input | `ownedCheckMC`, `ownedCheckML`, V | [`ownedCheckM_sound`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedLprogTV.lean), [`ownedCheckMC_sound`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedLprogTVChecked.lean), [`ownedCheckML_sound_leak`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedTVLeak.lean) |
| `ownedCheckM` accepts the fold of a body against the body, and a body against its two-address form | non-empty straight-line bodies whose symbolic run lies in the fragment of the checker; for the two-address form, instructions accepted by `twoAddrRouteWF` | `twoAddrRouteWF`, D | [`foldIndexed_ownedCheckM_complete`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedLprogTVDeadImm.lean), [`twoAddr_ownedCheckM_complete`](CatCrypt/Crypto/SecureCompilation/X86Backend/OwnedLprogTVTwoAddr.lean) |
| Every halting run of a typed body `pre ++ loop` is matched by a halting run of `pre ++ fuseMulHiRM loop` from the same state, with at most four times the fuel | typed bodies accepted by `fuseOKL`, from a base whose registers in the checked list have width 64 | `fuseOKL`, D | [`fuseMulHi_lsemFuelMemF_pre`](CatCrypt/Crypto/SecureCompilation/VIR/JasminLsemFuseMulHi.lean) |
| Every checked run of the image of the cell body is matched by a run of the address machine on the body, in the image relation with one-bit carries | bodies free of conditional branches whose cell body is accepted by `imgGateBW` and `physImgB`, the physical half of the register-allocation pair | `imgGateBW`, `physImgB`, D | [`image_addr_simBW`](CatCrypt/Crypto/SecureCompilation/X86Backend/ImageAddrCells.lean) |
| Every terminating run of the address machine on the body is matched by a halting run of the machine on the decoded function bytes, with the stack register restored | printed bodies in the class `printedAddrWB` (with carry chains) or `printedAddrB` | `printedAddrWB`, `printedAddrB`, D | [`printedAddr_simW`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodePrintedAddrW.lean), [`printedAddr_sim`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodePrintedCFG.lean) |
| The function bytes of a body decode to its layout `fundefLayout`, and the bytes of the gated encoder decode to the program `p` | bodies accepted by `decodableLcmd`; bodies accepted by `decodesToB` at `p` | `decodableLcmd`, `decodesToB`, D | [`decodeLprog_encodeLfundefBytes`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodeLayout.lean), [`decodeLprog_of_decodesToB`](CatCrypt/Crypto/SecureCompilation/X86Backend/DecodeLayout.lean) |
| Every halting run of `lsemFuelMemF` from a state whose registers satisfy the entry facts is in bounds | bodies accepted by the abstract interpretation `idxInvCheckB` | `idxInvCheckB`, D | [`runIdxOk_of_idxInvCheckB`](CatCrypt/Crypto/SecureCompilation/X86Backend/IdxInvCheck.lean) |
| The decoded function bytes of the printed body are constant time when the source events of the single-loop program are | printed bodies accepted by the route check `routeB` with `ownedCheckML`, free of conditional branches | `routeB`, D, with `ownedCheckML`, V | [`route_bytes_ct`](CatCrypt/Crypto/SecureCompilation/X86Backend/ImageRouteCT.lean) |
| The bytes decode to a program whose runs from entry states that satisfy the regions of the layout, agree on its public data and from which the source runs have equal leakage traces | a source accepted by the level check, and a printed body accepted by `regionCtB` in the gate of `compileRegion` | preservation along the region chain, with translation validation at allocation and printing | `NFEntry.levelCheck_region_bytes` (`Haxc.ComposeCTStraight`) |

On the image routes of the earlier back half (`ImageAddrRoute.routeB`,
`ImageStraightCells.straightCellB`) one
call of `ownedCheckMC` compares the reference chain with the image of the printed body. The
printed body is the output of the export, the post-pass `fuseMulHiLprog` and the owned
back end `ownedLprog`. For a pair accepted by this call, `ownedCheckMC_sound` therefore
gives the simulation across the block optimiser, the constant-index fold, the
two-address form, the post-pass and register allocation together. The reference side
applies the fusion as `fuseMulHiRM`; for a typed body accepted by `fuseOKL`,
`fuseMulHi_lsemFuelMemF_pre` gives its run.

For every result of `compileA`, `haxc_ct_proved_all` and `haxc_rc_proved_all`
(development repository, `Haxc.ComposeCTStraight`) give constant time and robust
compilation of every decoding of the bytes. `compileA` compiles a structured program, and
constant time of the decoded program follows from the level check of the source through
the region chain (`NFEntry.levelCheck_region_bytes`). In the earlier back half `compileJ`, on a
straight-line or looped route program, for a printed body accepted by an image arm of the
gate with its check on traced runs, `jGate_bytes_ct` derives constant time of the bytes
from constant time of the route program, which the level check of the source gives.

### Reference semantics of prime-ir calls

The hax interpreter reads a prime-ir field call under the builtin table
`primeirBuiltins p` (`CatCrypt/Hax/PrimeirBuiltins.lean`), which interprets the heads
`mul`, `add`, `sub`, `neg`, `square`, `double` and `inv` on integer arguments modulo
`p`. The extraction emits bare method names, so an integer `mul`, `add` or `sub` and
the field operation of the same name share a head. The field route's theorem
`field_correct_auto` (development repository, `Haxc.FieldCorrect`) is stated against
`primeirBuiltins p`, which is the semantics of the source for a function whose
integer-typed calls with these names are field calls. The name table
`defaultFieldTable` (`CatCrypt/Hax/PrimeirNames.lean`) lists the qualified names
beside the bare ones.

## Ascent: correspondence from given code to a specification

Ascent takes existing code, extracted or shipped, and proves a correspondence from
its runs to a Lean function. A second, ordinary proof equates that function with the
handwritten specification. Ascent has two instances, which share one calculus in the
style of AutoCorres.

- In the ascent on extracted Rust (the library `HaxAscent`, which depends only on Lean,
  Std, Batteries and hax-lean; judgement and generator in `HaxAscent/Ascent/`, index
  [CatCrypt/Hax/AGENTS.md](CatCrypt/Hax/AGENTS.md)), `FnCorres bi e entry G f` relates
  the `denote'` run of an `ImpExpr` literal under the builtin table `bi` to a shallow
  function `f`. The generator `Hax.Ascent.Gen.ascendFn` produces `f` and its
  correspondence with no hand-written loop specification. The entry point
  `hax_ascend Ns` runs the generator over a whole haxpipeT extraction and declares
  `Ns.HaxGen.f.gen`, `Ns.HaxGen.f.corres` and `Ns.HaxGen.f.corres_full` per function.
  `#hax_coverage Ns` reports per function. For one literal, the entry points are
  `ascend_reified` and `hax_corres`. A function generic over a trait is monomorphised at
  the extraction's instances (`Monomorphise.lean`, `fnCorres_monomorphise_iff`), and
  `hax_ascend` declares `Ns.HaxGen.f.corres_generic` for the generic literal. The
  executable `lake exe asc-cover` (development repository) counts, for each
  extraction, the functions that the descent fronts accept and the generator proves.
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
group and its bytes). The engine is the ParamTransfer package (namespace
`Transfer`), a port of Trocq's graded parametricity with `Param (m n) A B`,
`Related enc a b` and `RelatedBinOp`. Its tactics are `param_transfer` and `#transfer`,
which transfer statements and terms; `param_solve` and `rcongr`, which prove a
`Related` goal by descent through registered squares; and `param_auto`, the
coordinating cascade. The package's `README.md` and `TACTICS.md` document them.

A guarded square has a side condition that constrains the abstract operands, such as
`b ≤ a` at `a - b`; a total square is a guarded square with guard `True`. The engine
registers guarded squares as `RelatedBinOpOn`, `RelatedUnOpOn` and `RelatedRelOn`
(ParamTransfer `Transfer/Base/RelatedOn.lean`). The tactic `param_guard` composes
them and discharges each guard with `transfer_guard_disch` or leaves it as a goal.

In the development repository, `CatCrypt/Crypto/Bridges/Transfer/README.md` indexes
the relations the workspace registers. Its entries for hax-extracted integer code are
`HaxIntTransfer`, `HaxPrimeWord` and `RustMWordTransfer`. In this package,
`CatCrypt/Crypto/Bridges/Transfer/CompilerRegistry.lean` registers the compiler's
preservation lemmas, and `VIR/ParamDescent.lean` and `VIR/ParamDialectTransport.lean`
certify dialect-lowering squares by `param_solve`.

`TRANSFER_BOUNDARY.md` in the development repository uses "transfer" for a different
claim: a security game instantiated over an emitted primitive.

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
the same extraction through the hax front also yields the emitted bytes, and
`asc-cover` reports which functions both techniques reach.

## Composition of the techniques

The welds are in `CatCrypt/Crypto/SecureCompilation/Ascent/`:

- Over one `LowCT` command, `LegWeld.legWeld` joins the descent refinement
  `RRefines spec c`, the ascent square `Corres SRwordNT P fa c` and the emit leg
  `rustToJasminCom_endToEnd_unconditional`. Its conclusion is that the emitted Jasmin
  program denotes the source step's output.
- `CorresDescentX86.corres_of_refines_x86` turns a relational-compiler result
  `Refines spec frag` into a forward simulation of the compiled x86 block;
  `CorresDescentRiscv.corres_of_refines_riscv` is the RV64 form.
- `PipelineWeld.feSub_raw_source_to_bytes` composes hax-lean's `pipeline_correct` with
  the `feSub` source tower, from the raw extracted `ImpExpr` to bytes.
- The ascent on `ImpExpr` and the compiler's theorems for the machine code meet at a
  common Lean function for one extracted function, `maj` of the Hash_DRBG extraction (in
  the development tree): `maj_corresJ_of_fnCorres` gives, for every `f` with
  `FnCorres` for the extracted body, a `CorresJ` result at the block decoded from the
  shipped bytes, and `maj_corresIsa_of_fnCorres` a `CorresIsa x86Isa` result for the
  export's straight-line chain over virtual registers;
  `maj_corresIsa_bytes_of_fnCorres` gives `CorresIsa x86Isa` at the decoded block. All
  three use `fnCorres_enc_unique` (`HaxAscent/Ascent/FnCorresUnique.lean`). The
  shipped `mpn_mul_1` loop has a `CorresIsaRun x86Isa` result (`mul1_corresIsaRun`)
  against its loop specification. For every program the compile gate accepts the
  development tree has the instruction-set judgement against the source denotation
  (`v1Loop_corresIsa`, `jGate_straight_corresIsa`, and with the printed body as the
  program `v1Loop_image_corresIsaRun` and its straight-arm siblings);
  [ASCENT_OVERVIEW_LEAN.md](ASCENT_OVERVIEW_LEAN.md#1-the-problem-and-the-relation-to-descent)
  states which program each is about; see also
  [CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md#the-ascent-against-a-hax-reference).

Transfer enters both other techniques as a proof step: descent certifies dialect
lowerings by `param_solve`, and an ascent result over words reaches a specification
over `ZMod p` through a registered relation.

## Trust ledger

A headline theorem rests on Lean's three foundational axioms (`propext`,
`Classical.choice`, `Quot.sound`) and on the further entries of the declared trust
base, `scripts/headlines_trust_base.txt` in the development repository. Every
`native_decide` entry trusts the Lean code generator on one closed computation. The
table lists the further entries with the headlines that use them.

| Entries | Content | Headlines that use them |
|---|---|---|
| `CatCrypt.Util.ed25519L_prime`, `p25519_prime`, `secp256k1N_prime` | primality of the three published constants; the sources (`CatCrypt/Crypto/Util/ScalarFieldVerified.lean`, `CatCrypt/Crypto/Util/X25519Verified.lean`) declare them as theorems from the Pratt certificates in `CatCrypt/Crypto/Util/*PrimeCert.lean`, which `PrattCertificate.pratt_prime` checks by kernel `decide` | none in the recorded baseline |
| `Ed25519PointAddDecode.paShipped_instrOk` | every instruction of the shipped `ed25519_point_add` block lies in the decoder's covered set | `ed25519_point_add_bytes` |
| `pa_footP1`–`pa_footP10`, `scr_foot1`–`scr_foot8`, `scm_foot1`–`scm_foot9` | memory-footprint scans of the canonical parts of the three shipped Ed25519 blocks | `ed25519_point_add_bytes`, `ed25519_sc_reduce_shipped`, `ed25519_sc_muladd_shipped` |
