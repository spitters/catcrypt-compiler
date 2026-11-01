# Headline theorems of the compiler

Each entry names a theorem of this package, the level it is stated at, and its
hypotheses. Names are relative to `CatCrypt.Crypto.SecureCompilation` and paths to
`CatCrypt/Crypto/SecureCompilation/` unless they begin with `CatCrypt`.
[BUILDING.md](BUILDING.md#check-axioms) explains how to print the axioms of any of
them.

| Area | Theorem |
|---|---|
| The hax compiler | [`haxc_correct_auto`, `haxc_ct_proved_all`, `haxc_rc_proved_all`](#the-hax-compiler) |
| Dialect lowering | [`cryptoDialectToJasminCom_denote_eq'`](#dialect-lowering), [`fieldToJasminWord_denote`](#dialect-lowering) |
| LowCT front | [`transU_denote`](#lowct-front), [`translateDialectControlV_denote`](#lowct-front), [`fullScalarmultCovered_denote`](#lowct-front) (control skeleton; leaves opaque) |
| LowCT to the Jasmin dialect | [`rustToJasminCom_endToEnd_unconditional`](#lowct-to-the-jasmin-dialect), [`rustToJasminCom_endToEnd_rustexec_adeq_topLevel`](#lowct-to-the-jasmin-dialect), [`transU_to_jasminCom_endToEnd`](#lowct-to-the-jasmin-dialect) |
| Lattice route | [`latticeNttMul_compile_correct`](#lattice-route) (identity NTT), [`robustCompilation_source_to_x86`](#lattice-route) (x86 step assumed) |
| Machine code | [`com_x86_e2e`, `com_arm_e2e`, `com_riscv_e2e`](#machine-code) (virtual registers) |
| Emitted loops | [`singleLoop_export_faithful_gate`](#emitted-loops) and eight siblings |
| Constant time and noninterference | [`bytesCTCheck_sound`, `toLprogPhysAbi_gather_constant_time`, `owned_ct_control_flow` (model IR; no emitted branch is covered), `cmdCT_sound` (noninterference)](#constant-time-and-noninterference) |
| Ascent on transcribed and third-party code | [`paShippedBytes_correct`](#ascent-on-transcribed-and-third-party-code) and three siblings |

## The hax compiler

The bytes that `compileA` returns are read by the package's own decoder `decodeLprog`
and run on its own x86-64 model `aMachine`.

`Haxc.haxc_correct_auto` (`Haxc/RegionLinkCall.lean`). When `compileA m σ fname`
returns `(P, bytes)`, the bytes decode to a program `prog`, and every value of a
source run of `m` (`haxRuns`, under the builtin table `hax64WExit`) from an entry state
satisfying `σ.Regions` is read back by `σ` from a halting run of `prog` on `aMachine`,
which restores the stack register and leaves memory outside the frame and the pointer
regions unchanged; for a module whose translation keeps a call of a linked function,
the run goes through the call to the decoded callee. The statement is partial
correctness: it concerns source runs that reach a value. Hypotheses: the linked
functions have distinct names and are linked kernels (`LinkedKernel`); both hold
without linked functions.

`Haxc.haxc_ct_proved_all` (`Haxc/ComposeCTStraight.lean`). For a result of `compileA`,
every decoding of the bytes is constant time (`ConstantTimeRel`, termination-insensitive)
under the regime `ctRegime`, whose trace records effective addresses, branch outcomes
and the operands of variable-time instructions, between entry states that satisfy
`σ.Regions` and a precondition `Pre`, agree on the public data of `σ`, and from which
the module has a source run. Hypotheses: constant time of the translation `haxToNF` of
the module (`HaxToNFCTLOn`, a semantic statement about the translated program, which
the Boolean level check `haxToNFCTBL` implies by `haxToNFCTL_of_haxToNFCTBL`);
termination of the prepared source at one fuel on every such entry state (`hterm`);
public labels that agree with the public data of the layout (`PubLabelsOK`); distinct
layout names; the linked-function hypotheses above.

`Haxc.haxc_rc_proved_all` (`Haxc/RCInstance.lean`). Under the level check
`haxToNFCTBL`, `hterm` on every entry state satisfying `σ.Regions`, `PubLabelsOK`,
distinct layout names and the linked-function hypotheses, every decoding of the bytes
satisfies the gate conclusion `GateConclusion` of CatCrypt-core's `RCGate` (value
correctness and constant time together; `Haxc.haxc_gate_proved_all`). The second
conjunct restates the gate conclusion as `RobustCompilation 0` between the real
observation (the result read back from the target run and its leakage trace) and an
ideal observation whose trace the choice simulator `RCGate.simLeak`, defined by
`Classical.epsilon`, picks from the public projection `pubOf σ`; a context chooses only
the entry state. That conjunct holds for every compiler that satisfies the gate
conclusion with a deterministic target (`haxcTgtRes_det`).

`Haxc.AndNCorrect.mpn_and_n_rc_proved` and `Haxc.LtuCorrect.ltu_rc_proved`
(`Haxc/WorkedKernelCorollaries.lean`) are `haxc_rc_proved_all` at `mpn_and_n`, under
the layout `andAbi4` of three 4-word arrays (`n ≤ 4`), and at `ltu`. Both keep the
acceptance `compileA … = some (P, bytes)` and the level check `haxToNFCTB … = true` as
hypotheses.

## Dialect lowering

`VIR.DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`. When the
lowering from the SSA IR `catCryptDialect` to the Jasmin dialect succeeds, which
happens only on straight-line programs, the lowered program denotes the transport of
the source denotation. A leaf call (`extCall`) denotes the default value of its type on
both sides, so the statement says nothing about the value of a leaf call.

`Algebraic.FieldToJasminWord.fieldToJasminWord_denote`. A `fieldDialect` program in
the `GoodW p` fragment over a single-word prime field `F : SingleWordField p` lowers
through `lowerK F` to a Jasmin-dialect program whose result on the encoded valuation
is the encoding of the field result.

## LowCT front

`Dialects.TranslateDialectScalar.transU_denote` (module
`Dialects/TranslateDialectUnifiedDenote.lean`). For an `IsCoveredSU` body (counted
`RFor`, `RIfNz`, `RSeq`, data-dependent `RWhileNz` and conditional side effects
`RCond`, nested freely), the SSA IR prefix that `transU` emits denotes the body's
`semU` semantics per tail continuation. `transU` takes the entry environment and emits
the trace of the body at that environment: it decides each conditional and unrolls each
loop there. Hypotheses: coverage, entry consistency `ConsistentS vm V env`, success of
the front and of `semU`.

`Dialects.TranslateDialectVsimd.translateDialectControlV_denote`. The SIMD vector
front, over `gf2p8mulb`, `vpshufb`, `pclmulqdq` and `aesenc`, emits an SSA IR prefix
that denotes the body's `semV` semantics, for `IsCoveredV` bodies from a
`ConsistentV` entry.

`X86Backend.Fe25519ScalarmultCovered.fullScalarmultCovered_denote`. The control
skeleton of the X25519 scalar multiplication (a 255-step `RFor` over the opaque leaf
`x25519_ladder_iter`, followed by the opaque leaf `fe25519_encode`) descends through
the front; both semantics give each leaf the default value of its type, so the
statement concerns the control skeleton only.

## LowCT to the Jasmin dialect

`VIR.CompilerCorrectnessExtracted.rustToJasminCom_endToEnd_unconditional`. For an
`IsCoveredSCtl` source (straight-line arms, counted `RFor` loops, `RIfNz`
conditionals) whose front, return close-off and Jasmin lowering succeed: a run
`RustExec N leafSpec c rs rs'` from a byte-related entry state yields a byte-related
post-state valuation, and the Jasmin program's denotation equals the transport of the
value that `semScalar` leaves in the tracked output. `semScalar` wraps machine words
as the hardware does and gives an opaque leaf call a default value. The `RustExec`
state `rs` is not related to the `semScalar` entry state, so the two conjuncts concern
separate runs. Hypotheses: the compilation stages ran, the entry layout invariant
`RustStateInterp`, entry consistency `ConsistentS`, output tracking. The
`_topLevel_unconditional` variant discharges the entry hypotheses at the empty context
and the empty environment, that is, for programs that read no input.

`Dialects.RustExecSemScalarBridge.rustToJasminCom_endToEnd_rustexec_adeq_topLevel`.
On `IsCoveredAdeq` (64-bit word code without leaf calls or arrays whose expressions
cannot overflow for any `u64` valuation, which excludes `x + y`, `x - y` and `x * y` on
variables; counted loops; conditionals selecting between two constants), for programs
that read no input and write the output outside loops and conditionals, the Jasmin
value equals the `RustExec` output word.

`VIR.RustToJasminComWhile.transU_to_jasminCom_endToEnd`. On `IsCoveredSU`, the Jasmin
program that the front emits for an entry environment, with each `while` loop unrolled
and each conditional decided at that environment, has the value of the fuel-bounded
semantics `semU` at that environment. The emitted program contains no loop.

## Lattice route

`VIR.CompilerCorrectness.latticeNttMul_compile_correct`. For every modulus `q`, size
`n` and valuation `V`, the NTT-domain rewrite of the lattice-dialect operation
`polyMulC` (`ntt a; ntt b; basemul; invntt`), lowered to the Jasmin dialect, denotes the
transport of the source denotation. The lattice dialect defines `ntt` and `invntt` as
the identity and `polyMulC` as the pointwise product (`VIR/LatticeDialect.lean`), and
the Jasmin-dialect semantics of a call on 16-bit arrays is a copy or a pointwise
product whatever its name, so the statement is about the rewrite, not about an NTT.

`VIR.RobustCompilationPipeline.robustCompilation_source_to_x86`. For every
lattice-dialect program and valuation, and for any observable function `x86Behaviour`
that factors through the Jasmin-IR evaluator (the field `semRefine` of a
`JasminVerifiedCompiler` record), that function on the lowered program equals the
decoded source denotation. No x86 model or code occurs in the statement, and it states
no constant-time property. Hypotheses: leaf agreement `LeafAgrees`, injectivity of
`freshName` and of the parameter map.

## Machine code

`ScalarLinX86Demo.com_x86_e2e`, `ScalarLinNeutralDemo.com_arm_e2e`,
`MultiBackendDemo.com_riscv_e2e`. For a straight-line `Com` over `ComOK` in a context
of 64-bit registers, the block that the scalar instruction selection
(`ScalarLinX86Demo.x86Target`, `ARMBackend.ComToArm.armTarget`,
`RISCVBackend.RegToRiscv.rvTarget`) produces, run from virtual registers
`v0 … v(n-1)` holding the inputs in register models whose registers are named by
strings, leaves `Com.denote` in the virtual result register; no register is allocated.
The x86 model's `mulx` takes two explicit sources. The x86 statement assumes shift
amounts in range (`ShiftAmtOK`).

## Emitted loops

`X86Backend.ExportCertGate.singleLoop_export_faithful_gate`. The export node of a
runtime-count loop, for a program with one such loop accepted by `singleLoopB`, halts
under `lsemFuelMemF` from the ABI entry with the output array decoding to the
denotation of the source program, for every valuation.

The first three theorems below run a model of an emitted loop in the linear machine
model with memory (`loopLinstrRM` or `whileLinstrRM` over the body `loopBodyFullMN`, or
the hand-defined fill body `fillBodyM`) and equate the halting state with the source
denotation; the next four relate the flat machine run of a loop nest or call chain to a
structured machine fold; the last is stated at the export node.

- `VIR.JasminLsemMemSourceTieUncond.loopMem_export_faithful_comL_uncond`: a counter
  loop with body `chain ++ writeback`, as the model shape `loopLinstrRM top nReg
  (loopBodyFullMN update nReg)`, decodes to `ComL.forLoopNRt`'s denotation at the
  runtime trip count. Hypotheses: the update is in `ScalarMemN`, name hygiene, entry
  pins, seed agreement `StoreAgreesM`, and the run schedule, which states that the
  machine counter reaches zero after exactly `count` trips.
- `VIR.JasminLsemMemSourceTieUncond.fillLoop_export_faithful_denote`: the in-place
  fill loop `out[i] := a[i]`, after `m` machine trips, leaves array cells that decode to
  the `m`-fold of the source update.
- `VIR.JasminLsemMemSourceTieWhileUncond.whileMem_export_faithful_comL_uncond_trips`:
  the countdown loop `while (n != 0) { …; n -= 1 }`, run as the do-while
  `whileLinstrRM` from a state whose guard register holds the guard value `n > 0`,
  decodes to `ComL.whileNz`'s denotation. A guard of `0` is excluded: the exported
  do-while `whileLcmdNz` has no zero-trip guard.
- `VIR.JasminLsemMemLoopNestInline.inlineNest_closed`: a loop nest of any depth with
  data-dependent per-level trip counts halts on the state of the structured machine
  fold `runIBsL`, when that fold terminates.
- `VIR.JasminLsemMemFlagNestJoin.flagNest_closed` and
  `VIR.JasminLsemMemFlagNestJoin.guardedFlagLoop_runBounded_general`: the same with
  the emitted `CMP`/`Jcc` zero-trip guards, in the flag machine, against the folds
  `runFBsL` and `runBoundedStraightF`; the second assumes the run schedule and a
  non-zero count.
- `VIR.JasminLsemMemChainBridge.calleeRunDN_export_faithful`: a chain of nested calls
  of any depth halts with the result of the machine-level call interpreter
  `lsemStraightMemDN`, when the caller halts on return.
- `VIR.JasminLsemExportShippedAnd.binAnd_export_machine_shipped`: the export node the
  compiler emits for the `mpn_and_n_loop_owned` limb body, run on the linear flag
  machine `lsemFuelMemF`, halts with the array that the source fold
  `JLoopBodyN.denote` of that body gives.

## Constant time and noninterference

- `X86Backend.DecodedCT.bytesCTCheck_sound`: for a decoded x86-64 program that the
  checker `bytesCTCheck` accepts, two runs from index `0` whose steps respect the frame
  separation, from states that agree on the public set, have equal leakage traces; the
  trace records effective address values and branch outcomes.
  `DecodedCT.mul1Node_bytesCT` and `DecodedCT.feAddFramed_bytesCT` show that the
  checker accepts the decoded bytes of the exporter's `mpn_mul_1` body (before
  `optimizeLprog`) and of the hand-written `fe25519_add` kernel.
- `X86Backend.AllocCTPreservation.toLprogPhysAbi_gather_constant_time`: an exported
  function body with direct addressing that gathers to an x86 instruction block has a
  leakage trace (base-register names and displacements) determined by the instruction
  list alone. Address values are covered by `bytesCTCheck_sound`.
- `X86Backend.MachineConstantTime.owned_ct_control_flow`: a block of the model IR
  `OwnedCF` built from conditionals with public guards and loops with literal trip
  counts leaks the same trace (branch events, without direction, and memory accesses as
  base-register name and offset) from any two states that agree on the public
  registers. `OwnedCF` is not tied to the emitted `Lcmd` or to bytes, so no emitted
  branch is covered.
- `CatCrypt.Crypto.Jasmin.LowCT.cmdCT_sound` (`CatCrypt/Crypto/Jasmin/LowCTCTAnalysis.lean`):
  a program accepted by `cmdCT`, run from two public-equivalent states, reaches
  public-equivalent states (output noninterference; the statement has no leakage
  trace), under `CMOVInvariant`. `CMOVInvariant` holds for a select only when its two
  sources are the same slot, and `cmdCT` admits no computation on secret data.

## Ascent on transcribed and third-party code

The `ed25519_*` blocks below are Lean transcriptions of the text that the project's
backend printed, read by an importer whose output a script compares with that text.

- `Ascent.Demos.Ed25519PointAddBytes.paShippedBytes_correct`: the bytes that the
  package's encoder writes for the transcription of the backend's `ed25519_point_add`
  text (`encodeJBlock s2nAlloc ed25519PointAddShippedBlock`) decode to a block that,
  run under the address machine `runBlockA`, leaves at `%rdi + 32k` the four
  coordinates of `paSpec` on the eight input coordinates at `%rsi + 32k`;
  `paSpec_addSpec` ties `paSpec` to the Edwards addition law. The bytes are the
  encoder's, not the assembler's output for that text. Hypotheses: disjoint cells,
  inputs below `2^255 − 19`.
- `Ascent.Demos.Ed25519ScReduceShippedProof.scReduceShipped_correct_addr`: the
  transcribed `ed25519_sc_reduce` block stores the limbs of `x mod L`, below `L`.
  Hypothesis: the output, input and stack cells the block uses occupy pairwise disjoint
  eight-byte ranges (`Separated`).
- `Ascent.Demos.Ed25519ScMuladdShippedProof.scMuladdShipped_correct_addr`: the
  transcribed `ed25519_sc_muladd` block stores `(c + a·b) mod L`. Hypothesis: the
  output, input and stack cells the block uses occupy pairwise disjoint eight-byte
  ranges (`Separated`).
- `Ascent.CryptOptAddr.carryMul_correct_addr`: CryptOpt's
  `fiat_curve25519_carry_mul` block, run under `runBlockA`, stores five words whose
  value is congruent to the product of the input values modulo `2^255 − 19` (the
  congruence of fiat-crypto's `mul_correct`; no bound on the output limbs is stated).
  Hypotheses: input regions apart from each other, all three regions apart from the
  stack frame, input limbs below `2^54`. `solinasSquare_correct_addr` states the
  congruence of `sqr_correct` for `fiat_curve25519_solinas_square`.
