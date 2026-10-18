# Navigation

Where the code of the compiler lives and why it is there: one row per module family of
this package and of the compiler directories of the development repository
(SSProve-lean), with the family's purpose, its status, who consumes it, its entry
declarations and the document that indexes it. [PIPELINE.md](PIPELINE.md) gives the stages
of the compiler with their checks and theorems, [CORRECTNESS.md](CORRECTNESS.md) the three
correctness techniques, and [HEADLINES.md](HEADLINES.md) the headline theorems.

The compiler `compileA` (development repository, `Haxc/ComposeV1.lean`) runs the front
`haxToNF` (`CatCrypt/Crypto/Hax/ImpToNF.lean`; its domain check `HaxModule.refusal?` is in
`Haxc/NFChain.lean`) from the typed hax `ImpExpr` to `NFProg`, the certified pass chain
`extChain` (`Haxc/NFChainCall.lean`: tuple flattening, output-type check, dead-code
elimination, the translation to `catCryptDialect` with the declared procedures, the e-graph
pass, the conversion to `jasminDialect`, Montgomery form, field inlining, select lowering,
range analysis and a second e-graph pass), and the back half `compileRegion`
(`Haxc/RegionBackend.lean`: export to `Lprog`, allocation with lowering and frame,
post-fusion, the printed body, the checked encoder, and the gate `regionCoB && regionCtB`).
Its headline theorems are `haxc_correct_auto` (`Haxc/RegionLinkCall.lean`) and
`haxc_ct_proved_all` (`Haxc/ComposeCTStraight.lean`). Kernels are linked code produced by
the templates, by LowCT written in Lean, by relational compilation or by the Jasmin
importer, and certified by template theorems or by the ascent.

Generated on 2026-10-18 by `scripts/code-map/gen-code-map.py` (SSProve-lean) from the two trees and `scripts/code-map/annotations.txt`; edit the annotations, not this file.

Status: live (on the path of `compileA` or used by a headline), producer (generates linked kernels), tooling (census, emitters, benches), in-progress (work under way), legacy (earlier route kept), experiment, probe, spec (specifications and models), shim (re-exports), unsorted (not yet classified). Consumers: H in the import closure of a compiler headline module, Hs of another headline only, E of an executable, O imported by another module, N imported by nothing but aggregators, AGG imports only. "used" is the number of declaration lines the proofs of `haxc_correct_auto` and `haxc_ct_proved_all` use.

## catcrypt-compiler

| Family | Files / lines | Purpose | Status | Consumers | Last change | Entry | Doc |
|---|---|---|---|---|---|---|---|
| Hax: RawCode route | 7 / 936 | `ImpExpr` to the Deep `RawCode` | legacy | E 2 O 2 N 2 AGG 1 | 2026-10-13 | - | [CatCrypt/Hax/AGENTS.md](CatCrypt/Hax/AGENTS.md) |
| Hax: source reading and reification | 20 / 6.2 k | Lean to `ImpExpr` (`reifyImp%`), typing of `TExpr`, prime-ir names; the reading of the source in the compiler theorems | live | H 7 Hs 1 E 5 O 3 N 4 | 2026-10-09 | `defaultFieldTable` | [CatCrypt/Hax/AGENTS.md](CatCrypt/Hax/AGENTS.md) |
| HaxAscent | 64 / 24.1 k | ascent over `ImpExpr`: `FnCorres`, `hax_ascend`, the RustM semantics | live | H 15 E 8 O 32 N 7 AGG 2 | 2026-10-15 | `fnCorres_toRustMS_triple_of_kindOf` | [ASCENT_OVERVIEW_LEAN.md](ASCENT_OVERVIEW_LEAN.md) |
| Hax: front of compileA | 21 / 26.3 k | `ImpExpr` to `NFProg` to `catCryptDialect`, with leakage; the domain check of the front | live | H 12 O 7 N 2 | 2026-10-16 | `impToNF` | [PIPELINE.md](PIPELINE.md) |
| Hax: printers | 8 / 4.3 k | LowCT to `ImpExpr` to Rust text, and back | tooling | E 5 O 1 N 2 | 2026-09-28 | - | [HAX_RUST.md](HAX_RUST.md) |
| Hax: probes | 3 / 2.1 k | MLIR image of NF; a Rust subset to LowCT for one program | probe | O 3 | 2026-10-01 | - | - |
| Hax: legacy front haxToLowCT | 66 / 52.7 k | `haxToLowCT` and its simulation proofs, the exit forms and word operations; feeds kernel producers; some tables are still imported by modules of compileA | legacy | H 40 E 4 O 13 N 8 AGG 1 | 2026-10-16 | `haxToLowCT_simulates_program` | [CatCrypt/Crypto/Hax/AGENTS.md](CatCrypt/Crypto/Hax/AGENTS.md) |
| PrimeIR | 5 / 5.9 k | primeir-hax extraction and field models | live | H 4 N 1 | 2026-10-07 | - | [FIAT_TEMPLATES.md](FIAT_TEMPLATES.md) |
| Util | 40 / 4.4 k | prime certificates, reference kernels over `ZMod` | live | H 14 Hs 1 E 14 O 7 AGG 4 | 2026-10-13 | - | - |
| Optimizer: e-graph and range stage | 17 / 10.7 k | acyclic e-graph and range analysis; stages of `extChain` | live | H 11 E 1 O 2 N 3 | 2026-10-14 | `aegraphOptNF_denote` | - |
| Optimizer: lattice | 36 / 5.1 k | NTT algebra and lattice pass pipelines | producer | H 3 Hs 4 E 2 O 7 N 11 AGG 9 | 2026-10-13 | - | [CatCrypt/Crypto/Optimizer/README.md](CatCrypt/Crypto/Optimizer/README.md) |
| Optimizer: other passes | 100 / 39.0 k | Com CSE, DCE, copy propagation, Mem2Reg, LoadCSE, allocators, scheduling, SLP, rewrite library; used by emitters and the back end | producer | H 22 Hs 3 E 25 O 19 N 31 | 2026-10-18 | - | [CatCrypt/Crypto/Optimizer/README.md](CatCrypt/Crypto/Optimizer/README.md), [CatCrypt/Crypto/Optimizer/Rewrite/AGENTS.md](CatCrypt/Crypto/Optimizer/Rewrite/AGENTS.md) |
| Jasmin: LowCT core | 23 / 18.5 k | LowCT, its constant-time analysis, `LowCTToJasmin`, `reifyLowCT%`; the language of kernels written in Lean | producer | H 11 E 3 O 4 N 4 AGG 1 | 2026-10-16 | `cmdCT_sound` | [CatCrypt/Crypto/Jasmin/AGENTS.md](CatCrypt/Crypto/Jasmin/AGENTS.md) |
| Jasmin: AST and semantics | 11 / 3.3 k | Jasmin AST and the semantics of x86 operations | producer | H 3 Hs 2 E 3 O 2 N 1 | 2026-10-14 | - | [CatCrypt/Crypto/Jasmin/AGENTS.md](CatCrypt/Crypto/Jasmin/AGENTS.md) |
| Jasmin: .jinc import | 9 / 9.2 k | `.jinc` source to Com or LowCT to the owned x86 back end | producer | E 7 O 1 N 1 | 2026-10-14 | `importFunRolled` | [CatCrypt/Crypto/Jasmin/AGENTS.md](CatCrypt/Crypto/Jasmin/AGENTS.md), SSProve-lean `JINC_IMPORT.md` |
| Jasmin: bignum and InstrR | 22 / 18.7 k | bignum SSA interpreter and `.jazz` emission | legacy | Hs 1 E 1 O 13 N 7 | 2026-10-14 | - | - |
| Jasmin: text emitters | 5 / 2.8 k | Rust, Jasmin and MLIR text | tooling | H 1 E 2 O 1 N 1 | 2026-10-15 | - | - |
| Jasmin: examples | 42 / 12.1 k | demos and emit drivers | probe | H 6 E 1 O 12 N 23 | 2026-10-02 | - | - |
| Jasmin: specifications | 24 / 7.4 k | reference functions and the Ed25519 compression leaf | spec | H 2 E 9 O 6 N 6 AGG 1 | 2026-10-08 | - | [CatCrypt/Crypto/Jasmin/AGENTS.md](CatCrypt/Crypto/Jasmin/AGENTS.md) |
| Jasmin: reflect surfaces | 42 / 12.8 k | per-primitive LowCT orchestration (`*Reflect`), byte and leaf operations | producer | H 3 Hs 2 E 30 N 7 | 2026-09-27 | - | [CatCrypt/Crypto/Jasmin/AGENTS.md](CatCrypt/Crypto/Jasmin/AGENTS.md) |
| Pairing | 35 / 10.7 k | BN254, BLS and Pasta orchestration over trusted AUCurves leaves | producer | Hs 1 E 13 O 10 N 11 | 2026-10-05 | - | [CAPABILITIES.md](CAPABILITIES.md) |
| Vale and other trusted leaves | 35 / 9.7 k | citation axioms for external leaves (fiat-crypto, HACL*, libsecp256k1, Vale) | spec | H 1 E 17 O 1 N 14 AGG 2 | 2026-10-01 | - | - |
| Symbolic protocol models | 43 / 7.6 k | Dolev-Yao protocol models (EDHOC, MLS, Signal, TLS); not used by the compiler | spec | E 38 N 5 | 2026-09-24 | - | - |
| Specifications | 42 / 6.6 k | hash, primitive and scheme specifications | spec | H 3 Hs 4 E 18 O 9 N 2 AGG 6 | 2026-10-16 | - | - |
| Bridges in the package | 24 / 3.6 k | CoqEAL ports and representation transfer | spec | H 2 Hs 2 O 10 N 10 | 2026-10-14 | - | - |
| Tactics | 51 / 5.1 k | `kernel_rfl`, preservation combinators, pRHL tactics, re-exports | live | Hs 1 E 4 O 6 N 2 AGG 38 | 2026-09-29 | - | [CatCrypt/Tactic/AGENTS.md](CatCrypt/Tactic/AGENTS.md), [CatCrypt/Tactics/AGENTS.md](CatCrypt/Tactics/AGENTS.md) |
| Emit artifacts | 1 / 54 | emit drivers that write artifacts | tooling | E 1 | 2026-09-17 | - | [bench/PROVENANCE.md](bench/PROVENANCE.md) |
| Core shims | 47 / 1.5 k | re-exports of CatCrypt-core and aggregators | shim | N 1 AGG 46 | 2026-10-07 | - | - |
| SC: ties | 41 / 5.8 k | the denotation of a compiled `Com` equals a specification record | spec | E 2 O 33 N 6 | 2026-10-08 | `tie_transfer` | [README.md#security-ties](README.md#security-ties) |
| SC: THIR kernel generator | 79 / 27.4 k | a scalar let-normal IR `Thir` (not rustc THIR; its input is hax-lean `ImpExpr`/`TExpr`) compiled to `Com jasminDialect`; feeds the X86 `*ThirEmit` kernels | producer | H 1 E 9 O 45 N 24 | 2026-10-14 | `thirToJasmin_denote` | [THIR_GENERATOR.md](THIR_GENERATOR.md) |
| SC: relational compilation | 58 / 15.3 k | a Lean operation with a commuting square to a kernel | producer | Hs 10 E 1 O 31 N 16 | 2026-10-15 | `addMod251_source_eq_arm` | [DEMO.md](DEMO.md) |
| SC: grounded and concrete realizers | 63 / 18.2 k | packages stating that a kernel realizes a specification | experiment | Hs 18 O 28 N 17 | 2026-10-13 | - | [CatCrypt/Crypto/SecureCompilation/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md) |
| SC: curve specifications | 10 / 1.9 k | curves and extension fields, generic in the field | spec | Hs 2 E 1 O 3 N 4 | 2026-09-24 | - | [CatCrypt/Crypto/SecureCompilation/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md) |
| SC: ScalarLin | 7 / 1.7 k | straight-line register programs to three instruction sets | live | H 2 Hs 4 O 1 | 2026-10-14 | `com_x86_e2e` | [HEADLINES.md](HEADLINES.md) |
| SC: golden paths | 32 / 9.8 k | hand-written `Com` demonstrations and `orch%` surface syntax | probe | Hs 1 O 18 N 13 | 2026-10-14 | - | [CatCrypt/Crypto/SecureCompilation/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md) |
| SC: hand-written blocks | 15 / 3.2 k | hand-written instruction blocks used as known-answer oracles | legacy | H 1 O 8 N 6 | 2026-09-24 | - | [CatCrypt/Crypto/SecureCompilation/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md) |
| SC: front-compiled field and NTT kernels | 27 / 7.3 k | field and NTT kernels compiled by the LowCT front | producer | H 1 E 11 O 4 N 11 | 2026-10-13 | - | [CatCrypt/Crypto/SecureCompilation/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md) |
| SC: secp256k1 point operations | 26 / 14.6 k | secp256k1 ladder and field bricks through the LowCT front | producer | H 5 O 20 N 1 | 2026-10-14 | - | [CatCrypt/Crypto/SecureCompilation/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md) |
| SC: substrate | 8 / 4.0 k | shared types: `CryptoTy`, range domain, 64-bit memory | live | H 5 E 1 O 1 N 1; used 586 | 2026-10-05 | - | [CatCrypt/Crypto/SecureCompilation/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md) |
| SC: source constant time | 8 / 1.9 k | leakage of LowCT programs | live | H 2 E 2 O 1 N 3 | 2026-10-07 | - | [CatCrypt/Crypto/SecureCompilation/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md) |
| SC: speculative constant time | 7 / 5.3 k | Spectre models | experiment | O 6 N 1 | 2026-09-27 | - | - |
| SC: variable-width bignums | 19 / 3.6 k | variable-width bignum arithmetic | experiment | O 13 N 6 | 2026-09-11 | - | - |
| SC: top level, unsorted | 25 / 4.5 k | top-level modules not yet sorted into families | unsorted | H 5 E 1 O 8 N 9 AGG 2 | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md) |
| VIR: category layer | 11 / 5.4 k | dialects with lowerings as a category; regions and conversions as functors | experiment | O 7 N 4 | 2026-10-14 | - | SSProve-lean `DESIGN.md` |
| VIR: probes and demos | 10 / 2.2 k | probes, smoke tests and demonstrations | probe | H 1 E 1 N 7 AGG 1 | 2026-10-01 | - | - |
| VIR: core | 16 / 4.8 k | the SSA `Com`, its denotation, inlining and dialect sums | live | H 10 E 2 O 4; used 242 | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: NF and the pass chain | 27 / 13.3 k | `NFProg` regions, certified pass chains, leakage of NF; the IR of `extChain` | live | H 25 O 1 N 1; used 4.0 k | 2026-10-15 | `aegraphStep` | [CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md](CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md) |
| VIR: dialects | 12 / 4.9 k | the operation alphabets of `catCryptDialect`, `jasminDialect` and the THIR dialect | live | H 7 E 2 O 1 N 1 AGG 1; used 1.5 k | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md), [CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md](CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md) |
| VIR: lowerings to jasminDialect | 10 / 3.8 k | `cryptoDialectToJasminCom`; the THIR and lattice arms serve earlier routes | live | H 6 E 1 O 2 N 1; used 1.4 k | 2026-10-15 | `cryptoDialectToJasminCom` | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: block lowerings | 9 / 3.4 k | template lowering of operations to blocks | live | H 4 O 2 N 3; used 377 | 2026-10-04 | - | [CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md](CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md) |
| VIR: earlier control flow | 18 / 4.9 k | control flow over the emit substrate; `NFProg` regions carry control flow in `compileA` | legacy | H 2 E 1 O 9 N 6 | 2026-10-03 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: earlier compiler | 11 / 3.2 k | end-to-end theorems before `compileA`: `rustToJasminCom_endToEnd`, `Compiler.compile` | legacy | H 2 E 1 O 4 N 3 AGG 1 | 2026-10-06 | `rustToJasminCom_endToEnd_unconditional` | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: earlier constant-time layer | 10 / 2.8 k | static constant time and robust safety on `Com` | legacy | H 6 E 2 O 1 N 1; used 45 | 2026-10-04 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: .jazz emission | 11 / 11.6 k | `Com` to Jasmin programs and `.jazz` text | legacy | H 5 E 1 O 1 N 4 | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: Jasmin psem mirror | 25 / 11.0 k | alignment with the Coq semantics of Jasmin | experiment | O 21 N 4 | 2026-09-29 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: bounded-loop emission | 7 / 2.9 k | bounded loops in the emit substrate | producer | H 5 E 2 | 2026-09-24 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: export, allocation and ABI | 29 / 24.8 k | export of structured programs to `Lprog`, register allocation and the ABI; the back half of `compileRegion` | live | H 14 E 7 O 7 AGG 1; used 10.0 k | 2026-10-16 | `exportR_memFCT` | SSProve-lean `CatCrypt/Crypto/SecureCompilation/X86Backend/README.md` |
| VIR: earlier lsem machines | 7 / 6.6 k | per-fragment linear machines; the flag machine covers their fragments | legacy | O 5 N 2 | 2026-10-05 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: flag and address machines | 77 / 50.0 k | the linear machine `lsem`, the flag machine `lsemFuelMemF`, export simulation, loops and source ties | live | H 58 O 9 N 10; used 12.1 k | 2026-10-17 | `fuseMulHi_lsemFuelMemF_pre` | [CORRECTNESS.md](CORRECTNESS.md) |
| VIR: post-allocation passes | 12 / 12.4 k | passes on `Lprog` with whole-body theorems at the flag machine | in-progress | H 3 O 9; used 2.4 k | 2026-10-18 | `lsemFuelMemFk_blockRel` | [CORRECTNESS.md](CORRECTNESS.md) |
| VIR: instruction-set abstraction | 14 / 5.2 k | the back end over an instruction set | live | H 6 O 6 N 2; used 1.1 k | 2026-10-18 | - | - |
| VIR: Com optimiser and allocation demos | 39 / 16.6 k | Com-level passes and register-allocation demonstrations | legacy | H 1 E 22 O 4 N 11 AGG 1; used 51 | 2026-10-14 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: templates | 24 / 13.6 k | word templates with certificates: negacyclic NTT, narrow fields, round codecs, GF(2^128) | producer | H 8 O 10 N 5 AGG 1; used 58 | 2026-10-15 | `permProg_spec` | [FIAT_TEMPLATES.md](FIAT_TEMPLATES.md) |
| VIR: MLIR correspondence | 6 / 2.4 k | MLIR models of the dialects; not the emit path | experiment | O 3 N 3 | 2026-10-14 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: VeIR | 11 / 7.6 k | `Com` to VeIR and its LLVM audit | in-progress | E 3 O 5 N 3 | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/VIR/SEMANTICS.md](CatCrypt/Crypto/SecureCompilation/VIR/SEMANTICS.md) |
| VIR: lowering as transport | 13 / 3.4 k | lowerings stated as parametric transports | spec | H 3 E 1 O 5 N 4; used 41 | 2026-10-05 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: covered and validate pins | 21 / 7.5 k | single-program denotation pins through the LowCT front | probe | E 4 O 1 N 16 | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: vector | 53 / 29.5 k | vectorisation, lane maps, tile legalisation, %ymm and %zmm printers | producer | H 2 E 22 O 21 N 8; used 780 | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: kernel ties to specifications | 28 / 9.3 k | kernels tied to FIPS specifications | spec | E 9 O 11 N 8 | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: kernel emitters | 105 / 42.5 k | per-primitive kernels | producer | H 2 E 76 O 9 N 18 | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: primitive kernels | 53 / 20.5 k | per-primitive kernels and their laws (Keccak, Poseidon2, SHA-2, ChaCha20, X25519, HAWK, FHE, Plonky3, mpn) | producer | H 2 Hs 1 E 23 O 14 N 13 | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: algebra dialects | 43 / 15.3 k | the prime-ir dialects `field`, `mod_arith`, `elliptic_curve`, `poly`, `tensor_ext` and their lowerings | producer | H 12 Hs 5 E 7 O 14 N 5; used 287 | 2026-10-13 | - | [CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md](CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md) |
| VIR: specifications | 14 / 2.5 k | Mathlib-level specifications | spec | O 9 N 5 | 2026-10-13 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| VIR: Lean kernel target | 7 / 1.4 k | the Lean kernel as a target | experiment | O 5 N 2 | 2026-10-01 | - | - |
| VIR: unsorted | 30 / 7.9 k | VIR modules not yet sorted into families | unsorted | H 5 E 2 O 12 N 10 AGG 1; used 57 | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| X86: string-templated emitters | 15 / 6.1 k | assembly text built from strings for tests and benches | probe | E 11 O 1 N 3 | 2026-09-24 | - | - |
| X86: probes and demos | 17 / 4.2 k | probes, known-answer pins and demonstrations | probe | H 2 E 6 O 1 N 8; used 74 | 2026-10-17 | - | - |
| X86: dialect models | 3 / 639 | MLIR-style dialect models at the machine level | experiment | H 1 E 1 N 1 | 2026-09-24 | - | - |
| X86: earlier route ends | 16 / 5.0 k | routes and export certificates of the earlier back half | legacy | H 11 O 1 N 4; used 170 | 2026-10-17 | `straight_export_faithful_abi` | [CORRECTNESS.md](CORRECTNESS.md) |
| X86: completeness of the image gate | 15 / 17.0 k | completeness of `physImgB` | in-progress | O 13 N 2 | 2026-10-18 | - | - |
| X86: linked calls | 15 / 10.2 k | callee layout, linked decode, call simulation and its constant time | live | H 13 O 1 N 1; used 5.4 k | 2026-10-15 | `haltsC_of_linkedChecks` | - |
| X86: image relation and gates | 24 / 24.9 k | the image relation between the reference and the printed body; the gates of `compileRegion` | live | H 23 N 1; used 14.7 k | 2026-10-17 | `image_addr_simBW` | [CORRECTNESS.md](CORRECTNESS.md) |
| X86: validators | 11 / 17.9 k | `ownedCheckM`, `ownedCheckMC`, `ownedCheckML` and the bounds invariant | live | H 6 O 3 N 2; used 7.8 k | 2026-10-18 | `ownedCheckMC_sound` | [CORRECTNESS.md](CORRECTNESS.md) |
| X86: decoding | 26 / 24.9 k | decoded-byte simulation and constant time at the bytes | live | H 18 E 1 O 4 N 3; used 12.1 k | 2026-10-17 | `printedAddr_simW`, `decodeLprog_encodeLfundefBytes` | [CORRECTNESS.md](CORRECTNESS.md) |
| X86: encoders and ISA record | 20 / 15.8 k | the encoder, the checked encoder, the instruction-set record, Sail round trips | live | H 10 E 1 O 5 N 4; used 4.0 k | 2026-10-17 | `encodeLfundefBytesChecked` | [CORRECTNESS.md](CORRECTNESS.md) |
| X86: printed-body passes | 27 / 18.1 k | the stages of `printedLprog` and their theorems at the flag machine | live | H 11 O 8 N 8; used 1.8 k | 2026-10-18 | `reallocLprog_lsemFuelMemF`, `twoAddrBody_lsemFuelMemF` | [CORRECTNESS.md](CORRECTNESS.md) |
| X86: optional passes | 14 / 11.6 k | passes that emitters apply after allocation | tooling | H 7 E 3 O 3 N 1; used 435 | 2026-10-18 | - | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: gather and JInstr ELF route | 30 / 12.5 k | `gatherJBlock6`, `composeValidated`, `encodeJBlock6`: an earlier byte route | legacy | H 17 Hs 1 E 4 O 5 N 3; used 304 | 2026-10-16 | - | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: runBlock and lsem agreement | 17 / 7.2 k | `runBlock` against `lsemStraightMem` | experiment | H 1 O 14 N 2 | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: linear-scan faithfulness | 20 / 9.9 k | faithfulness of `toLprogPhysAbi`, an allocator `compileA` does not run | legacy | H 12 E 6 O 1 N 1 | 2026-10-15 | `toLprogPhysAbi_lsem` | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: earlier LowCT compiler | 18 / 6.0 k | source to `JInstr` in four phases | legacy | H 2 O 13 N 3 | 2026-10-14 | - | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: speculative constant time | 9 / 6.0 k | speculation models on `JInstr` | experiment | E 3 O 3 N 3 | 2026-10-15 | - | - |
| X86: block constant time | 3 / 2.3 k | constant time of direct-addressed blocks | live | H 3; used 90 | 2026-10-16 | `blockLeak_pub_determined` | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: machine models | 14 / 8.2 k | `runBlock`, `runBlockA` and the loop semantics of `JInstr` | live | H 10 Hs 1 E 2 O 1; used 1.3 k | 2026-10-14 | - | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: printers | 4 / 3.4 k | AT&T assembly text | tooling | H 3 O 1; used 380 | 2026-10-11 | - | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: THIR emitters | 18 / 4.7 k | kernels compiled by the THIR kernel generator to owned AT&T assembly or Jasmin | producer | E 18 | 2026-09-11 | - | [THIR_GENERATOR.md](THIR_GENERATOR.md) |
| X86: vector | 26 / 11.9 k | vector emit paths and their printers and encoders | producer | E 6 O 13 N 7 | 2026-10-13 | - | SSProve-lean `CatCrypt/Crypto/SecureCompilation/X86Backend/README.md` |
| X86: mpn kernels | 62 / 24.3 k | front-generated multi-precision kernels with their denotation ties | producer | H 17 E 19 O 17 N 9 | 2026-10-14 | - | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: value-proved field and curve blocks | 31 / 12.6 k | field and curve blocks with value proofs over `runBlock` | producer | H 7 Hs 11 E 4 O 9 | 2026-10-05 | - | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: oracle kernels | 29 / 13.4 k | hand-written kernels used as known-answer oracles | probe | H 6 E 17 O 4 N 2 | 2026-10-14 | - | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: runBlock value lemmas | 16 / 6.2 k | value lemmas of field blocks over `runBlock` | producer | H 2 Hs 2 E 7 O 3 N 2 | 2026-10-05 | - | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: front-compiled emitters | 26 / 9.2 k | kernels compiled by the LowCT front and emitted | producer | H 2 E 18 N 6; used 211 | 2026-10-14 | - | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| X86: unsorted | 52 / 19.3 k | X86Backend modules not yet sorted into families | unsorted | H 18 E 7 O 7 N 20; used 422 | 2026-10-18 | - | [CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| Dialects: NF and catCrypt leakage | 8 / 3.3 k | leakage models and level checks of NF and `catCryptDialect` | live | H 8; used 1.4 k | 2026-10-15 | `catLevelCheck_sound` | [CatCrypt/Crypto/SecureCompilation/Dialects/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Dialects/AGENTS.md) |
| Dialects: RustExec bridges | 14 / 6.3 k | `RustExec` against `semScalar` | legacy | H 1 E 1 O 7 N 5 | 2026-10-14 | - | [CatCrypt/Crypto/SecureCompilation/Dialects/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Dialects/AGENTS.md) |
| Dialects: front prototypes | 15 / 3.0 k | small runs of front arms | probe | E 5 N 9 AGG 1 | 2026-09-24 | - | [CatCrypt/Crypto/SecureCompilation/Dialects/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Dialects/AGENTS.md) |
| Dialects: neutral dialects | 34 / 8.2 k | `arith`, `memref`, `vector`, `func` and instruction selection | experiment | E 3 O 16 N 15 | 2026-10-15 | - | [CatCrypt/Crypto/SecureCompilation/Dialects/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Dialects/AGENTS.md) |
| Dialects: LowCT to catCrypt | 79 / 34.2 k | `translateDialect*`, `FrontRoutePlan`, guarded denotations, catCrypt security | producer | H 37 Hs 4 E 7 O 13 N 18 | 2026-10-15 | `transU_denote` | [CatCrypt/Crypto/SecureCompilation/Dialects/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Dialects/AGENTS.md) |
| Ascent: instruction-set judgement | 18 / 9.1 k | `CorresIsa` over the address machine; used by the back half of `compileA` | live | H 15 O 2 N 1; used 662 | 2026-10-17 | `corresIsa_x86_of_corresJ` | [CatCrypt/Crypto/SecureCompilation/Ascent/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Ascent/AGENTS.md) |
| Ascent: certificates of shipped code | 120 / 55.6 k | Ed25519, s2n-bignum and CryptOpt code certified at the bytes; tactic demos | live | H 63 E 2 O 29 N 26 | 2026-10-17 | `paShippedBytes_correct` | [ASCENT.md](ASCENT.md), [CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md) |
| Ascent: calculus and welds | 156 / 42.4 k | `Corres`, `ascend!`, guards, the welds between descent and ascent | live | H 11 E 19 O 74 N 37 AGG 15; used 7 | 2026-10-17 | - | [CatCrypt/Crypto/SecureCompilation/Ascent/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Ascent/AGENTS.md) |
| Algebraic templates | 46 / 17.5 k | field templates (Montgomery, Solinas, unsaturated) and ZK emitters | live | H 18 E 25 O 2 N 1; used 3.5 k | 2026-10-14 | `fieldToJasminWord_denote` | [FIAT_TEMPLATES.md](FIAT_TEMPLATES.md) |
| CT | 9 / 5.7 k | leakage definitions and timing regimes | live | H 6 O 3; used 272 | 2026-10-14 | - | - |
| SepLogic | 14 / 4.7 k | separation logic over total states for the export contract | in-progress | H 10 O 2 N 2 | 2026-10-17 | - | - |
| ARM and RISC-V back ends | 68 / 25.2 k | AArch64 and RV64 models, encoders and Sail decoders | live | H 10 E 31 O 16 N 11 | 2026-10-15 | `comToArmLsem_correct`, `riscvStep64_sail_grounded` | [CatCrypt/Crypto/SecureCompilation/ARMBackend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/ARMBackend/AGENTS.md), [CatCrypt/Crypto/SecureCompilation/RISCVBackend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/RISCVBackend/AGENTS.md) |
| Tile back end | 13 / 4.2 k | NVIDIA Tile IR emitter | experiment | E 9 O 2 N 2 | 2026-10-14 | - | [CatCrypt/Crypto/SecureCompilation/TileBackend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/TileBackend/AGENTS.md) |
| MLIR text | 27 / 8.0 k | MLIR text and the vector alphabet | experiment | H 2 E 1 O 11 N 13 | 2026-10-14 | - | [CatCrypt/Crypto/SecureCompilation/MLIR/VectorDialect/AGENTS.md](CatCrypt/Crypto/SecureCompilation/MLIR/VectorDialect/AGENTS.md) |
| SC: small directories | 12 / 3.8 k | SSA import, the AUCurves bridge, `AbiLayout` | unsorted | H 1 Hs 5 E 1 O 2 N 3; used 213 | 2026-10-13 | - | [CatCrypt/Crypto/SecureCompilation/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md) |

## SSProve-lean

| Family | Files / lines | Purpose | Status | Consumers | Last change | Entry | Doc |
|---|---|---|---|---|---|---|---|
| Haxc: compileA and its headlines | 28 / 26.9 k | `compileA = haxToNF → extChain → compileRegion`, the two headlines and their constant-time chain | live | H 26 N 2; used 15.6 k | 2026-10-18 | `compileA`, `refusal?`, `extChain`, `compileRegion`, `haxc_correct_auto`, `haxc_ct_proved_all` | SSProve-lean `DESIGN.md`, [PIPELINE.md](PIPELINE.md) |
| Haxc: completeness | 23 / 23.6 k | the domain of the front implies acceptance by the back half | in-progress | O 19 N 4 | 2026-10-18 | - | SSProve-lean `DESIGN.md` |
| Haxc: corollaries | 7 / 2.3 k | frame contract, further call shapes, whole-body pass theorems | in-progress | O 3 N 4 | 2026-10-18 | `deadWriteRet_lsemFuelMemF` | SSProve-lean `COMPILER_ROADMAP.md` |
| Haxc: tooling | 15 / 5.9 k | census, emit registry, Rust templates for the benches | tooling | E 10 N 5 | 2026-10-16 | - | SSProve-lean `DESIGN.md` |
| Haxc: field route and templates | 24 / 8.9 k | `fieldRegionFront` into `compileRegion`; template routes to bytes | producer | H 14 E 1 O 4 N 5; used 169 | 2026-10-18 | `fieldChain_correct_auto`, `ec_correct_bytes` | [FIAT_TEMPLATES.md](FIAT_TEMPLATES.md) |
| Haxc: earlier routes | 20 / 5.0 k | the earlier back half and the typed and desugared fronts | legacy | H 14 O 3 N 3; used 203 | 2026-10-15 | - | SSProve-lean `DESIGN.md` |
| Haxc: instances | 19 / 3.9 k | the headlines at named programs and Lean-built inputs | probe | H 6 E 1 O 6 N 6 | 2026-10-18 | - | - |
| SC dev: elliptic-curve blocks | 80 / 31.1 k | value proofs of elliptic-curve blocks over `runBlock` | producer | Hs 11 E 11 O 35 N 23 | 2026-10-05 | - | SSProve-lean `CatCrypt/Crypto/SecureCompilation/X86Backend/README.md` |
| SC dev: VIR emits | 44 / 12.4 k | field-dialect emits and capstones | producer | Hs 1 E 3 O 22 N 18 | 2026-10-14 | - | SSProve-lean `CatCrypt/Crypto/SecureCompilation/VIR/README.md` |
| SC dev: probes | 35 / 4.9 k | known-answer pins | probe | O 4 N 31 | 2026-10-15 | - | - |
| SC dev: VerifiedEval | 18 / 7.6 k | `verified_decide`: a separate compiler from FProg to x86 | experiment | O 12 N 4 AGG 2 | 2026-10-14 | - | SSProve-lean `VERIFIED_EVAL.md` |
| SC dev: MLIR vector leaf | 4 / 3.5 k | the MAYO `.jinc` leaf | producer | E 1 O 1 N 2 | 2026-10-08 | - | SSProve-lean `JINC_IMPORT.md` |
| SC dev: other directories | 3 / 423 | dev modules in directories of the compiler package | unsorted | N 2 AGG 1 | 2026-09-15 | - | - |
| SC dev: THIR ties and relational instances | 33 / 7.8 k | THIR-front ties and per-curve relational instances | legacy | Hs 4 E 3 O 8 N 18 | 2026-10-08 | - | - |
| Hax dev: typed front and runners | 50 / 26.3 k | the typed front `haxFrontT`, the A-normaliser, `HaxRun` runners | legacy | H 16 E 17 O 8 N 8 AGG 1 | 2026-10-16 | `haxFrontT_simulates` | SSProve-lean `DESIGN.md` |
| Jasmin dev: mpn and bignum | 124 / 86.7 k | GMP-class kernels as `.jazz`, s2n-bignum ports, Hoare triples | legacy | Hs 1 E 48 O 47 N 27 AGG 1 | 2026-10-08 | - | SSProve-lean `CatCrypt/Crypto/Jasmin/README.md`, SSProve-lean `CatCrypt/Crypto/Jasmin/AGENTS.md` |
| CompilerSecurity | 47 / 13.3 k | compiler correctness to UC (`HaxcRC`), traced semantics, RHP over LowCT | live | H 5 Hs 6 O 25 N 11 | 2026-10-16 | `uc_of_gate` | - |
| Optimizer dev | 2 / 443 | optimiser modules of the dev tree | unsorted | E 1 N 1 | 2026-09-27 | - | - |
| Bridges: transfer | 23 / 4.7 k | hax word codecs, registries, representation transfer | spec | Hs 3 O 4 N 14 AGG 2 | 2026-10-08 | - | SSProve-lean `CatCrypt/Crypto/Bridges/Transfer/README.md` |
| Bridges: game realizations | 7 / 2.5 k | byte games and emitted operations computing the game operations | spec | Hs 5 O 2 | 2026-10-18 | - | SSProve-lean `TRANSFER_BOUNDARY.md` |
| Bridges: Iris | 140 / 41.8 k | separation logic, step indexing, relational logics, quantum, protocol UC over Iris | experiment | Hs 14 E 57 O 32 N 33 AGG 4 | 2026-10-18 | - | SSProve-lean `CatCrypt/Crypto/Bridges/IrisBridge/AGENTS.md` |
| Bridges: Squirrel | 130 / 11.3 k | symbolic trace proofs ported from Squirrel | experiment | E 6 O 97 N 27 | 2026-09-19 | - | SSProve-lean `CatCrypt/Crypto/Bridges/README.md` |
| Bridges: other frameworks | 85 / 12.3 k | VCVio, CryptHOL, XDijkstra, Loom, ArkLib, CoqEAL, AUCurves, re-export shims | unsorted | E 3 O 30 N 25 AGG 27 | 2026-10-18 | - | SSProve-lean `CatCrypt/Crypto/Bridges/README.md`, SSProve-lean `CatCrypt/Crypto/Bridges/PROGRAM_LOGICS.md` |

## Totals by status

| Status | Files | Lines |
|---|---|---|
| live | 1075 | 521.8 k |
| producer | 1141 | 446.6 k |
| tooling | 47 | 28.1 k |
| in-progress | 82 | 67.7 k |
| legacy | 531 | 286.7 k |
| experiment | 529 | 142.2 k |
| probe | 238 | 69.2 k |
| spec | 304 | 65.0 k |
| shim | 47 | 1.5 k |
| unsorted | 209 | 48.7 k |

## Finding a theorem

- By name: `git grep -n 'theorem NAME'` in this package and in the development
  repository. A module's namespace can differ from its path; read its `namespace` line
  before citing a qualified name.
- By topic: module docstrings list their results under `## Main results`;
  `git grep -n 'Main results' -- DIR` finds them in a directory.
- By directory: start from the index document of its row above.
- Its trust base: add `#print axioms <name>` to `AxiomAudit.lean` or a scratch file and run
  it as [BUILDING.md](BUILDING.md#check-axioms) describes.

The map is generated: the facts of a row (files, lines, consumers, last change) come from
the trees, and its purpose, status, entry declarations and index document from the
annotation table of the generator. A module that no row covers fails the generator's check.

