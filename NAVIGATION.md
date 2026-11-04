# Navigation

Where the code of the compiler lives: one row per directory or group of directories of
this package, with its content, entry declarations and the document that indexes it.
[PIPELINE.md](PIPELINE.md) gives the stages of the compiler with their checks and
theorems, [CORRECTNESS.md](CORRECTNESS.md) the three correctness techniques,
[HEADLINES.md](HEADLINES.md) the headline theorems, and [BUILDING.md](BUILDING.md) the
build and check commands. Unless a path starts with `HaxAscent/`, `scripts/`, `bench/`
or `docs/`, it is relative to `CatCrypt/Crypto/SecureCompilation/`.

## The hax compiler

The compiler `compileA` (`Haxc/ComposeV1.lean`, executable `lake exe haxc`, root
`Haxc/HaxcMain.lean`) runs the front `haxToNF` (`Haxc/NFChain.lean`, over `impToNF` in
`CatCrypt/Crypto/Hax/ImpToNF.lean`; its domain check `HaxModule.refusal?` is in
`Haxc/NFChain.lean`) from the typed hax `ImpExpr` to `NFProg`, the certified pass chain
`extChain` (`Haxc/ExtChain.lean`: tuple flattening, output-type check, dead-code
elimination, the translation to `catCryptDialect` with the declared procedures, the
e-graph pass, the conversion to `jasminDialect`, Montgomery form, the field dialect step,
select lowering, range analysis and a second e-graph pass), and the back half
`compileRegion` (`Haxc/RegionBackend.lean`: export to `Lprog`, allocation with lowering
and frame, post-fusion, the printed body, the checked encoder, and the gate
`regionCoB && regionCtB`). Its headline theorems are `haxc_correct_auto`
(`Haxc/RegionLinkCall.lean`), `haxc_ct_proved_all` (`Haxc/ComposeCTStraight.lean`), and
`haxc_gate_proved_all` and `haxc_rc_proved_all` (`Haxc/RCInstance.lean`);
[CORRECTNESS.md](CORRECTNESS.md#descent-the-verified-compiler) states them with their
hypotheses. Kernels are
linked code produced by the templates, by `LowCT` written in Lean, by relational
compilation or by the Jasmin importer, and certified by template theorems or by the
ascent.

| Group of `Haxc/` | Modules | Content | Entry |
|---|---|---|---|
| Headlines | `ComposeV1`, `RegionLinkCall`, `ComposeCTStraight`, `RCInstance` | `compileA`, value correctness, constant time, gate conclusion and robust compilation | `compileA`, `haxc_correct_auto`, `haxc_ct_proved_all`, `haxc_rc_proved_all` |
| Front and chain | `NFChain*`, `NFFront*`, `NFToRoute*`, `NFMontify*`, `ExtChain*`, `RouteChain`, `RouteProg` | `haxToNF`, its domain check, the pass chain and its certificate | `haxToNF`, `HaxModule.refusal?`, `extChain_denote` |
| Back half | `Region*`, `BackHalf*`, `PrintedLprogFuel`, `CmpReloadBracket*` | `compileRegion`: export, allocation, post-fusion, printing, encoding and the gate | `compileRegion`, `compileRegion_correct` |
| Constant time | `ComposeCT*`, `CT*`, `FrontLeak*`, `NFChainCT`, `ExtChainCT`, `RegionCallCT` | leakage along the chain and at the bytes | `regionChain_bytes_ct` |
| Completeness | `*Complete*`, `RegionCoComplete`, `ExportComplete`, `FrontComplete` | acceptance by later stages of what earlier stages return | - |
| Field route | `Field*` | field operations through the field dialect into `compileRegion` | `fieldChain_correct_auto`, `field_correct_auto`, `field_correct_bytes` |
| Linked kernels | `LinkedKernel`, `ModuleCalls`, `TraitLinkAccept`, `RegionLink*` | calls of linked functions and their machine contracts | `LinkedKernel`, `compileRegion_correct_linked` |
| Worked kernels | `AndNCorrect`, `LtuCorrect`, `WorkedKernelCorollaries` | the headlines at `mpn_and_n` and `ltu`, with acceptance by `compileA` as a hypothesis | `mpn_and_n_rc_proved`, `ltu_rc_proved` |
| Tooling | `HaxcMain`, `CensusCore`, `Decompile*` | the command line and its refusal report | `refusalReport` |

## Directories

| Directory | Modules | Lines | Content | Entry | Index |
|---|---|---|---|---|---|
| `Haxc/` | 133 | 89.7 k | the hax compiler `compileA` (above) | `compileA` | [PIPELINE.md](PIPELINE.md) |
| `CatCrypt/Crypto/Hax/` | 95 | 79.7 k | the front of `compileA` from `ImpExpr` (`ImpToNF`, `ANormCore`, `Hax64Table`, `HaxFrontOracle`, `HaxFrontPrep*`, `HaxSpine`); the front `haxToLowCT` to `LowCT` used by the kernel producers | `impToNF`, `haxToLowCT_simulates_programT` | [CatCrypt/Crypto/Hax/AGENTS.md](CatCrypt/Crypto/Hax/AGENTS.md) |
| `CatCrypt/Hax/` | 28 | 7.5 k | reading Lean into `ImpExpr` (`reifyImp%`, `reifyField%`), typing of `TExpr`, the prime-ir builtins and names | `primeirBuiltins`, `defaultFieldTable` | [CatCrypt/Hax/AGENTS.md](CatCrypt/Hax/AGENTS.md) |
| `HaxAscent/` | 66 | 25.9 k | the ascent over `ImpExpr`: `Corres`, `FnCorres`, the generator `hax_ascend`, the `RustM` semantics and calculus | `fnCorres_toRustMS_triple_of_kindOf`, `fnCorres_enc_unique` | [ASCENT_OVERVIEW_LEAN.md](ASCENT_OVERVIEW_LEAN.md) |
| `VIR/` | 768 | 369.7 k | the SSA `Com` and its dialects, `NFProg` regions and certified pass chains, lowerings to `jasminDialect`, export to `Lprog` (`VIR/JasminLprogExport/`), the linear and flag machines `lsem`, `lsemFuelMemF`, whole-body passes (`VIR/LsemBridgePass/`), word templates, vector paths, prime-ir dialects, per-primitive kernels | `aegraphStep`, `cryptoDialectToJasminCom`, `exportR_memFCT`, `lsemFuelMemFk_blockRel`, `rustToJasminCom_endToEnd_unconditional` | [VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md), [VIR/DIALECTS.md](CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md), [VIR/SEMANTICS.md](CatCrypt/Crypto/SecureCompilation/VIR/SEMANTICS.md) |
| `X86Backend/` | 580 | 322.7 k | the x86-64 back end: machine models (`runBlock`), register allocation and its translation validation, printed-body passes, the image relation and gates of `compileRegion`, the encoder and decoder, decoded-byte simulation and constant time, linked calls, front-generated kernels | `ownedCheckMC_sound`, `printedAddr_simW`, `decodeLprog_encodeLfundefBytes`, `encodeLfundefBytesChecked`, `haltsC_of_linkedChecks`, `blockLeak_pub_determined` | [X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| `ARMBackend/`, `RISCVBackend/` | 33, 35 | 13.5 k, 11.7 k | AArch64 and RV64 models, encoders and Sail-grounded decoders | `comToArmLsem_correct`, `riscvStep64_sail_grounded` | [ARMBackend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/ARMBackend/AGENTS.md), [RISCVBackend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/RISCVBackend/AGENTS.md) |
| `TileBackend/` | 13 | 4.2 k | NVIDIA Tile IR emitter | - | [TileBackend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/TileBackend/AGENTS.md) |
| `Ascent/` | 290 | 106.4 k | the ascent on `LowCT`, x86 and RV64: `Corres`, `CorresJ`, `CorresIsa`, `ascend!`, the welds between descent and ascent, the address machine `aMachine`; certificates of shipped code (`Ascent/Demos/`) and imported instruction lists (`Ascent/Imported/`) | `corresIsa_x86_of_corresJ`, `paShippedBytes_correct` | [Ascent/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Ascent/AGENTS.md), [ASCENT.md](ASCENT.md), [CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md) |
| `Dialects/` | 152 | 56.4 k | `LowCT` to `catCryptDialect` (`translateDialect*`), leakage models and level checks of NF and `catCryptDialect`, neutral dialects | `transU_denote`, `catLevelCheck_sound` | [Dialects/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Dialects/AGENTS.md) |
| `Algebraic/` | 48 | 18.1 k | field templates (Montgomery, Solinas, unsaturated), Poseidon and Poseidon2 compilation, ZK field emitters | `fieldToJasminWord_denote` | [FIAT_TEMPLATES.md](FIAT_TEMPLATES.md) |
| `CT/`, `SepLogic/` | 9, 16 | 5.7 k, 5.7 k | leakage definitions and timing regimes; separation logic over total states for the export contract | - | - |
| `MLIR/`, `MLIRBackend/` | 27 | 8.0 k | MLIR text and the vector alphabet | - | [MLIR/VectorDialect/AGENTS.md](CatCrypt/Crypto/SecureCompilation/MLIR/VectorDialect/AGENTS.md) |
| `AeneasFront/` | 20 | 5.4 k | the Aeneas front, a second entry `aeneasEntry` of the compiler: squares of the Aeneas scalar and array operations against `hax64WExit` as ParamTransfer instances, stated once for every width (`Scalars`, `Arrays`, over `TableReads`), the reading `nfToRustM` of NF programs in Aeneas `RustM` and its simulation (`NFToRustM`, `Loops`), `reifyAeneas%` with proofs by construction and one guard lemma (`Reify`, `ReifyArrays`), the entry and its constant-time theorem (`Entry`, `EntryCT`); Aeneas test functions compiled to bytes (`Demo/`) | `aeneasEntry_compileR_ct`, `nfToRustM_sim`, `Reify.guardS`, `incrArray_compileR_correct`, `optAdd_compileR_correct` | [AeneasFront/README.md](CatCrypt/Crypto/SecureCompilation/AeneasFront/README.md) |
| `AUCurvesImport/`, `LowCTExtensions/`, `Jasmin/` | 10 | 3.3 k | the AUCurves bridge, `LowCT` extensions, Jasmin helpers | - | - |
| top level of `CatCrypt/Crypto/SecureCompilation/` | 354 | 106.0 k | the hax-to-kernel routes `CompileFromHax*` and their specification ties, relational compilation (`RelationalFront*`), `ScalarLin` straight-line register programs, the THIR kernel generator (`Thir*`), secp256k1 point operations, generic curve and extension-field specifications, speculative constant time, `Com` demonstrations (`*GoldenPath`) | `addMod251_source_eq_arm`, `com_x86_e2e`, `thirToJasmin_denote` | [SecureCompilation/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md), [THIR_GENERATOR.md](THIR_GENERATOR.md), [DEMO.md](DEMO.md) |
| `CatCrypt/Crypto/Jasmin/` | 180 | 84.9 k | `LowCT`, its constant-time analysis and `reifyLowCT%`; the Jasmin AST; the `.jinc` importer; bignum kernels; per-primitive `LowCT` orchestration (`*Reflect`); reference specifications | `cmdCT_sound`, `importFunRolled` | [CatCrypt/Crypto/Jasmin/AGENTS.md](CatCrypt/Crypto/Jasmin/AGENTS.md) |
| `CatCrypt/Crypto/Optimizer/` | 155 | 54.0 k | the acyclic e-graph and range analysis of `extChain`; NTT and lattice pass pipelines; `Com` CSE, DCE, copy propagation, allocators, scheduling, SLP and the rewrite library | `aegraphOptNF_denote` | [Optimizer/README.md](CatCrypt/Crypto/Optimizer/README.md), [Optimizer/Rewrite/AGENTS.md](CatCrypt/Crypto/Optimizer/Rewrite/AGENTS.md) |
| `CatCrypt/Crypto/Mpn/` | 1 | 0.2 k | the haxpipe extraction of the multi-precision kernels, the source of the worked kernels of `Haxc/` | `mpn_and_n_texpr` | - |
| `CatCrypt/Crypto/Pairing/` | 34 | 10.5 k | BN254, BLS and Pasta orchestration over AUCurves leaves | - | [CAPABILITIES.md](CAPABILITIES.md) |
| `CatCrypt/Crypto/PrimeIR/` | 5 | 5.9 k | the primeir-hax extraction and field models | - | [FIAT_TEMPLATES.md](FIAT_TEMPLATES.md) |
| `CatCrypt/Crypto/Util/` | 41 | 4.5 k | prime certificates, reference kernels over `ZMod` | - | - |
| `CatCrypt/Crypto/Vale/` | 35 | 9.7 k | statements for external leaves (fiat-crypto, HACL*, libsecp256k1, Vale) | - | - |
| `CatCrypt/Crypto/Hash/`, `Primitives/`, `MLKEM/`, `MLDSA/` | 42 | 6.8 k | hash, primitive and scheme specifications | - | - |
| `CatCrypt/Crypto/Symbolic/` | 43 | 7.6 k | Dolev-Yao protocol models (EDHOC, MLS, Signal, TLS) | - | - |
| `CatCrypt/Crypto/Bridges/` | 18 | 2.8 k | CoqEAL ports, representation transfer and the compiler's ParamTransfer registry (`Transfer/`) | - | [CORRECTNESS.md](CORRECTNESS.md#transfer-parametricity-across-representations) |
| `CatCrypt/Tactic/`, `CatCrypt/Tactics/` | 14, 37 | 1.1 k, 3.9 k | `kernel_rfl`, preservation combinators, pRHL tactics, re-exports | - | [CatCrypt/Tactic/AGENTS.md](CatCrypt/Tactic/AGENTS.md), [CatCrypt/Tactics/AGENTS.md](CatCrypt/Tactics/AGENTS.md) |
| `CatCrypt/Core/`, `Deep/`, `Relational/` | 39 | 1.4 k | re-exports of CatCrypt-core and small extensions of its relational layer | - | - |
| `bench/` | | | benchmark harnesses, comparisons with external implementations, and the provenance of emitted artifacts | - | [bench.md](bench.md), [bench/PROVENANCE.md](bench/PROVENANCE.md) |
| `docs/`, `blueprint/` | | | the Verso manual and the blueprint | - | [BUILDING.md](BUILDING.md#generate-the-documentation) |

The module counts and line counts are those of the tracked `.lean` files of each
directory. The libraries of `lakefile.lean` are `CatCryptCompiler` (the compiler and its
dependency closure), `CatCryptCompilerExamples` (demonstrations, probes and benchmark
drivers, imported by no module of the first), `CatCryptCompilerVeir` (the VeIR bridge,
built on request) and `HaxAscent`.

## Finding a theorem

- By name: `git grep -n 'theorem NAME'` in this package. A module's namespace can differ
  from its path; read its `namespace` line before citing a qualified name.
- By topic: module docstrings list their results under `## Main results`;
  `git grep -n 'Main results' -- DIR` finds them in a directory.
- By directory: start from the index document of its row above.
- Its axioms: add `#print axioms <name>` to `AxiomAudit.lean` or a scratch file and run
  it as [BUILDING.md](BUILDING.md#check-axioms) describes.
