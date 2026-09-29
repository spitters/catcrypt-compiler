# Headline theorems of the compiler

Each entry names a theorem of this package, the level it is stated at, and its
hypotheses. Names are relative to `CatCrypt.Crypto.SecureCompilation` and paths to
`CatCrypt/Crypto/SecureCompilation/` unless they begin with `CatCrypt`.
[BUILDING.md](BUILDING.md#check-axioms) explains how to print the axioms of any of
them.

| Area | Theorem |
|---|---|
| Dialect lowering | [`cryptoDialectToJasminCom_denote_eq'`](#dialect-lowering), [`fieldToJasminWord_denote`](#dialect-lowering) |
| LowCT front | [`transU_denote`](#lowct-front), [`translateDialectControlV_denote`](#lowct-front), [`fullScalarmultCovered_denote`](#lowct-front) |
| LowCT to the Jasmin dialect | [`rustToJasminCom_endToEnd_unconditional`](#lowct-to-the-jasmin-dialect), [`rustToJasminCom_endToEnd_rustexec_adeq_topLevel`](#lowct-to-the-jasmin-dialect), [`transU_to_jasminCom_endToEnd`](#lowct-to-the-jasmin-dialect) |
| Lattice route | [`latticeNttMul_compile_correct`](#lattice-route), [`robustCompilation_source_to_x86`](#lattice-route) |
| Machine code | [`com_x86_e2e`, `com_arm_e2e`, `com_riscv_e2e`](#machine-code) |
| Emitted loops | [`loopMem_export_faithful_comL_uncond`](#emitted-loops) and five siblings |
| Constant time | [`toLprogPhysAbi_gather_constant_time`, `owned_ct_control_flow` (model IR; no emitted branch is covered), `cmdCT_sound`](#constant-time) |
| Ascent on imported and shipped code | [`paShippedBytes_correct`](#ascent-on-imported-and-shipped-code) and four siblings |

## Dialect lowering

`VIR.DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`. When the
lowering from the SSA IR `catCryptDialect` to the Jasmin dialect succeeds, the lowered
program denotes the transport of the source denotation.

`Algebraic.FieldToJasminWord.fieldToJasminWord_denote`. A `fieldDialect` program in
the `GoodW p` fragment over a single-word prime field `F : SingleWordField p` lowers
through `lowerK F` to a Jasmin-dialect program whose result on the encoded valuation
is the encoding of the field result.

## LowCT front

`Dialects.TranslateDialectScalar.transU_denote` (module
`Dialects/TranslateDialectUnifiedDenote.lean`). For an `IsCoveredSU` body (counted
`RFor`, `RIfNz`, `RSeq`, data-dependent `RWhileNz` and conditional side effects
`RCond`, nested freely), the SSA IR prefix that `transU` emits denotes the body's
`semU` semantics per tail continuation. Hypotheses: coverage, entry consistency
`ConsistentS vm V env`, success of the front and of `semU`.

`Dialects.TranslateDialectVsimd.translateDialectControlV_denote`. The SIMD vector
front, over `gf2p8mulb`, `vpshufb`, `pclmulqdq` and `aesenc`, emits an SSA IR prefix
that denotes the body's `semV` semantics, for `IsCoveredV` bodies from a
`ConsistentV` entry.

`X86Backend.Fe25519ScalarmultCovered.fullScalarmultCovered_denote`. The whole X25519
scalar multiplication (a 255-step Montgomery-ladder `RFor` followed by the encode
leaf) descends through the front, and the emitted prefix denotes the kernel's
`semScalar` semantics.

## LowCT to the Jasmin dialect

`VIR.CompilerCorrectnessExtracted.rustToJasminCom_endToEnd_unconditional`. For an
`IsCoveredSCtl` source (straight-line arms, counted `RFor` loops, `RIfNz`
conditionals) whose front, return close-off and Jasmin lowering succeed: a run
`RustExec N leafSpec c rs rs'` from a byte-related entry state yields a byte-related
post-state valuation, and the Jasmin program's denotation equals the transport of the
value that `semScalar` leaves in the tracked output. `semScalar` wraps machine words
as the hardware does and gives an opaque leaf call a default value. Hypotheses: the
compilation stages ran, the entry layout invariant `RustStateInterp`, entry
consistency `ConsistentS`, output tracking. The `_topLevel_unconditional` variant
discharges the entry hypotheses for translator-rooted programs.

`Dialects.RustExecSemScalarBridge.rustToJasminCom_endToEnd_rustexec_adeq_topLevel`.
On `IsCoveredAdeq` (64-bit word code without leaf calls or arrays, counted loops, and
conditionals selecting between two constants), for inputs in `u64` range, the Jasmin
value equals the `RustExec` output word.

`VIR.RustToJasminComWhile.transU_to_jasminCom_endToEnd`. On `IsCoveredSU`, the Jasmin
value equals the value of the fuel-bounded semantics `semU`, which includes
data-dependent `while` loops.

## Lattice route

`VIR.CompilerCorrectness.latticeNttMul_compile_correct`. For every modulus `q`, size
`n` and valuation `V`, the NTT-domain rewrite of the coefficient-form polynomial
multiply (`ntt a; ntt b; basemul; invntt`), lowered to the Jasmin dialect, denotes the
transport of the source denotation. The lattice dialect models the NTT and its
inverse as the identity (`VIR/LatticeDialect.lean`).

`VIR.RobustCompilationPipeline.robustCompilation_source_to_x86`. For every
lattice-dialect program and valuation, composed with an x86 compiler given as a
`JasminVerifiedCompiler` record (observable, behaviour): the x86 observable equals
the decoded source denotation. The theorem states no constant-time property.
Constant time of emitted code is proved at the decoded bytes by
`X86Backend.DecodedCT.bytesCTCheck_sound`, with the acceptance theorems
`DecodedCT.mul1Node_bytesCT` (`mpn_mul_1`) and `DecodedCT.feAddFramed_bytesCT`
(`fe25519_add`). Hypotheses: leaf agreement
`LeafAgrees`, injectivity of `freshName` and of the parameter map.

## Machine code

`ScalarLinX86Demo.com_x86_e2e`, `ScalarLinNeutralDemo.com_arm_e2e`,
`MultiBackendDemo.com_riscv_e2e`. For a straight-line `Com` over `ComOK` in a context
of 64-bit registers, the block that the scalar instruction selection
(`ScalarLinX86Demo.x86Target`, `ARMBackend.ComToArm.armTarget`,
`RISCVBackend.RegToRiscv.rvTarget`) produces, run from registers holding the inputs,
leaves `Com.denote` in the result register. The x86 statement assumes shift amounts
in range (`ShiftAmtOK`).

## Emitted loops

Each theorem runs an emitted loop in the linear machine model with memory and
equates the halting state with the source denotation.

- `VIR.JasminLsemMemSourceTieUncond.loopMem_export_faithful_comL_uncond`: a counter
  loop with body `chain ++ writeback` decodes to `ComL.forLoopNRt`'s denotation at the
  runtime trip count. Hypotheses: the update is in `ScalarMemN`, name hygiene, entry
  pins, seed agreement `StoreAgreesM`, and the run schedule.
- `VIR.JasminLsemMemSourceTieUncond.fillLoop_export_faithful_denote`: the in-place
  fill loop `out[i] := a[i]` leaves array cells that decode to the source fold.
- `VIR.JasminLsemMemSourceTieWhileUncond.whileMem_export_faithful_comL_uncond`: the
  data-dependent countdown loop `while (n != 0) { …; n -= 1 }` decodes to
  `ComL.whileNz`'s denotation; the trip count is read off the run.
- `VIR.JasminLsemMemLoopNestInline.inlineNest_closed`: a loop nest of any depth with
  data-dependent per-level trip counts halts on the spec fold's state.
- `VIR.JasminLsemMemFlagNestJoin.flagNest_closed` and
  `VIR.JasminLsemMemFlagNestJoin.guardedFlagLoop_runBounded_general`: the same with
  the emitted `CMP`/`Jcc` zero-trip guards, in the flag machine.
- `VIR.JasminLsemMemChainBridge.calleeRunDN_export_faithful`: a chain of nested calls
  of any depth halts with the spec fold's result.

## Constant time

- `X86Backend.MachineConstantTime.owned_ct_control_flow`: a block of the model IR
  `OwnedCF` built from conditionals with public guards and loops with literal trip
  counts leaks the same trace (branch decisions and memory addresses) from any two
  states that agree on the public registers. `OwnedCF` is not tied to the emitted
  `Lcmd` or to bytes, so no emitted branch is covered.
- `X86Backend.AllocCTPreservation.toLprogPhysAbi_gather_constant_time`: an exported
  function body with direct addressing that gathers to an x86 instruction block leaks
  the same trace from any two states.
- `CatCrypt.Crypto.Jasmin.LowCT.cmdCT_sound` (`CatCrypt/Crypto/Jasmin/LowCTCTAnalysis.lean`):
  a program accepted by `cmdCT`, run from two public-equivalent states, reaches
  public-equivalent states, under `LeafCTAssumption` and `CMOVInvariant`.
  `CMOVInvariant` holds for a select only when its two sources are the same slot, and
  `cmdCT` admits no computation on secrets.

## Ascent on imported and shipped code

- `Ascent.Demos.Ed25519PointAddBytes.paShippedBytes_correct`: the bytes
  `encodeJBlock s2nAlloc ed25519PointAddShippedBlock` decode to a block that, run
  under the address machine `runBlockA`, leaves at `%rdi + 32k` the four coordinates of
  `paSpec` on the eight input coordinates at `%rsi + 32k`; `paSpec_addSpec` ties
  `paSpec` to the Edwards addition law. Hypotheses: disjoint cells, inputs below
  `2^255 − 19`.
- `Ascent.Demos.Ed25519ScReduceShippedProof.scReduceShipped_correct_addr`: the
  imported `ed25519_sc_reduce` block stores the limbs of `x mod L`, below `L`.
- `Ascent.Demos.Ed25519ScMuladdShippedProof.scMuladdShipped_correct_addr`: the
  imported `ed25519_sc_muladd` block stores `(c + a·b) mod L`.
- `VIR.JasminLsemExportShippedAnd.binAnd_export_machine_shipped`: the shipped
  `mpn_and_n` loop body halts with the array its model `JLoopBodyN.denote` gives.
- `Ascent.CryptOptAddr.carryMul_correct_addr`: CryptOpt's
  `fiat_curve25519_carry_mul` block, run under `runBlockA`, stores five words that meet
  fiat-crypto's `mul_correct` congruence against the input words. Hypotheses: input
  regions apart from each other, all three regions apart from the stack frame, input
  limbs below `2^54`. `solinasSquare_correct_addr` states `sqr_correct` for
  `fiat_curve25519_solinas_square`.
