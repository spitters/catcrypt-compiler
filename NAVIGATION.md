# Navigation

Where each subsystem of the compiler lives, its main theorem, and how to find a
theorem. `SC/` abbreviates `CatCrypt/Crypto/SecureCompilation/`, and theorem names
are relative to `CatCrypt.Crypto.SecureCompilation` unless they begin with
`CatCrypt`. [CORRECTNESS.md](CORRECTNESS.md) orders the subsystems by the three
correctness techniques.

## Subsystems

| Subsystem | Location | Main theorem | Index |
|---|---|---|---|
| LowCT, the source command language | `CatCrypt/Crypto/Jasmin/LowCT.lean` | `CatCrypt.Crypto.Jasmin.LowCT.cmdCT_sound` (constant-time analysis) | [Jasmin/AGENTS.md](CatCrypt/Crypto/Jasmin/AGENTS.md) |
| hax-lean AST to LowCT and back | `CatCrypt/Crypto/Hax/` | `CatCrypt.Crypto.Hax.haxToLowCT_simulates_program` | [Crypto/Hax/AGENTS.md](CatCrypt/Crypto/Hax/AGENTS.md) |
| Reification of `ImpExpr` | `CatCrypt/Hax/` | `CatCrypt.Hax.ReifyImp.edwardsAdd_endToEnd` | [Hax/AGENTS.md](CatCrypt/Hax/AGENTS.md) |
| The ascent over `ImpExpr` (library `HaxAscent`: Lean, Std, Batteries, hax-lean only) | `HaxAscent/Ascent/`, `HaxAscent/RustSemantics/`, `HaxAscent/Calculus/` | `CatCrypt.Hax.RustSemantics.fnCorres_toRustMS_triple_of_kindOf`, `Hax.Ascent.fnCorres_enc_unique` | [Hax/AGENTS.md](CatCrypt/Hax/AGENTS.md), [ASCENT_OVERVIEW_LEAN.md](ASCENT_OVERVIEW_LEAN.md) |
| `thir` front from hax | `SC/CompileFromHax.lean`, `SC/ThirToComFront.lean` | `ThirToComFront.thirToJasmin_denote` | [SC/AGENTS.md](CatCrypt/Crypto/SecureCompilation/AGENTS.md) |
| LowCT front to the SSA IR | `SC/Dialects/` | `Dialects.TranslateDialectScalar.transU_denote` | [Dialects/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Dialects/AGENTS.md) |
| `Com` framework, dialects, lowerings, end-to-end theorems | `SC/VIR/` | `VIR.DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`, `VIR.CompilerCorrectnessExtracted.rustToJasminCom_endToEnd_unconditional` | [VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md), [DIALECTS.md](CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md) |
| PrimeIR field lowering | `SC/Algebraic/` | `Algebraic.FieldToJasminWord.fieldToJasminWord_denote` | [DIALECTS.md](CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md) |
| Linear machine model and emitted loops | `SC/VIR/JasminLsem*.lean` | `VIR.JasminLsemMemSourceTieWhileUncond.whileMem_export_faithful_comL_uncond` | [VIR/AGENTS.md](CatCrypt/Crypto/SecureCompilation/VIR/AGENTS.md) |
| x86-64 backend | `SC/X86Backend/` | `ScalarLinX86Demo.com_x86_e2e`, `X86Backend.MachineConstantTime.owned_ct_control_flow` | [X86Backend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/X86Backend/AGENTS.md) |
| AArch64 backend | `SC/ARMBackend/` | `ScalarLinNeutralDemo.com_arm_e2e`, `ARMBackend.ComToArmLsem.comToArmLsem_correct` | [ARMBackend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/ARMBackend/AGENTS.md) |
| RISC-V backend | `SC/RISCVBackend/` | `MultiBackendDemo.com_riscv_e2e`, `RISCVBackend.ComToRiscvLsem.riscvStep64_sail_grounded` | [RISCVBackend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/RISCVBackend/AGENTS.md) |
| Relational front | `SC/RelationalFrontMachine.lean` | `RelationalFront.addMod251_source_eq_arm` | [DEMO.md](DEMO.md) |
| Ascent | `SC/Ascent/` | `Ascent.Demos.Ed25519PointAddBytes.paShippedBytes_correct`, `Ascent.corresIsa_x86_of_corresJ` | [Ascent/AGENTS.md](CatCrypt/Crypto/SecureCompilation/Ascent/AGENTS.md), [ASCENT.md](ASCENT.md) |
| Certifying third-party machine code | `SC/Ascent/Demos/`, `HaxAscent/Ascent/` | `Ascent.Demos.CertifyThirdPartyDemo.s2nMontmulP384_correct_reduced` | [CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md) |
| Vector dialect and auto-vectorizer | `SC/MLIR/VectorDialect/` | `Dialects.TranslateDialectVsimd.translateDialectControlV_denote` (SIMD front) | [VectorDialect/AGENTS.md](CatCrypt/Crypto/SecureCompilation/MLIR/VectorDialect/AGENTS.md) |
| Tile backend | `SC/TileBackend/` | — | [TileBackend/AGENTS.md](CatCrypt/Crypto/SecureCompilation/TileBackend/AGENTS.md) |
| Rewrite-saturation optimizer | `CatCrypt/Crypto/Optimizer/` | — | [Optimizer/README.md](CatCrypt/Crypto/Optimizer/README.md) |
| Security ties | `SC/CompileFromHaxSecurityTie.lean` | `CompileFromHaxSecurityTie.tie_transfer` | [README.md](README.md#security-ties) |
| Tactics | `CatCrypt/Tactic/`, `CatCrypt/Tactics/` | — | [Tactic/AGENTS.md](CatCrypt/Tactic/AGENTS.md), [Tactics/AGENTS.md](CatCrypt/Tactics/AGENTS.md) |
| Primitive kernels | per primitive | — | [CAPABILITIES.md](CAPABILITIES.md) |
| Emit drivers | `CatCrypt/EmitArtifacts/` | — | [bench/PROVENANCE.md](bench/PROVENANCE.md) |

[HEADLINES.md](HEADLINES.md) states the headline theorems with their hypotheses.

## Finding a theorem

- By name: `git grep -n 'theorem NAME'`. A module's namespace can differ from its
  path (`SC/Dialects/TranslateDialectUnifiedDenote.lean` declares into
  `Dialects.TranslateDialectScalar`); read its `namespace` line before citing a
  qualified name.
- By topic: module docstrings list their results under `## Main results`;
  `git grep -n 'Main results' -- DIR` finds them in a directory.
- By directory: start from the `AGENTS.md` in the table above.
- Its trust base: add `#print axioms <name>` to `AxiomAudit.lean` or a scratch file
  and run it as [BUILDING.md](BUILDING.md#check-axioms) describes.

The library `CatCryptCompiler` holds the compiler and its theorems;
`CatCryptCompilerExamples` holds demos, probes, tests and benchmark drivers.
