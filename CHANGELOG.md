# Changelog

## Unreleased

Changes since `v0.1.0-alpha.2`.

### 2026-09-16

Ed25519 extended-coordinate point addition, from the algebraic route to assembly
an assembler accepts:

- `Algebraic/Ed25519PointAddEmit.lean`: `pointAddAsm` applies
  `FheMontMulEmit.fuseMulHiLprog` before `LprogOptPipeline.renderOwned`, which
  runs no fusion of its own. Without the pass every widening multiply of the
  Curve25519 limb blocks printed `# UNHANDLED-MULXHI-UNFUSED` — 189 markers and
  no `mulx`, one per `mulhi` of the nine multiply blocks; with it the rendering
  carries 189 `mulx` and no marker.
- `X86Backend/LprogAsmPrinter.lean`: the `CMOV` arm covers a spilled destination
  and a spilled condition. `cmov` admits no memory destination, so a spilled
  select destination runs in a register borrowed around `-128(%rsp)`, as the
  spilled `adcx`/`adox` destination does; a spilled condition is compared against
  zero, `test` admitting at most one memory operand. Bodies with no spilled
  select render byte-identically, checked by re-rendering the comb select kernel
  and the four other emitted Ed25519 kernels.
- `Algebraic/FieldLimbs/Curve25519.lean`: `constBlk` binds each limb's 64-bit
  remainder. `regConst 64 n` denotes `BitVec.ofNat 64 n` for every `n`, but the
  printer emits `n` verbatim, so the three low limbs of the curve constant `2d`
  left the immediate range. `ofNat_mod_two_pow` is the rewrite that keeps
  `constBlk_denote`'s statement unchanged, and with it every emitted immediate is
  below `2 ^ 64`.

The emitted `ed25519_point_add` passes a known-answer test against libsodium's
`crypto_core_ed25519_add`: 576 additions of comb-table points, compressed by the
emitted inversion and compression kernels, byte-identical, with `T₃·Z₃ = X₃·Y₃`
on every raw output (`bench/ed25519_comb_compare/point_add_compare.c`, dev repo).

Frame layout:

- `X86Backend/LprogAsmPrinter.lean`: `frameAddDirective` and a `FRAMEADD`
  directive that `frameSize` adds to both of its branches, so a body can request
  extra frame bytes without replacing the computed layout. The existing `FRAME`
  directive replaces it, which also drops the `bodyHasCall` alignment correction;
  `FRAMEADD` keeps both. It returns `0` for every body that does not carry the
  directive, and no body emits one yet, so every kernel's frame size and every
  qsave and spill offset are unchanged — checked by re-rendering the ten emitted
  Ed25519 artifacts and comparing checksums.
- `X86Backend/LprogBytes.lean`: `carriesNoBytes` accepts `FRAMEADD`. A
  `FRAME`-carrying body is not byte-encodable today, so a rolled kernel that
  requested buffers through `FRAME` would silently lose its byte export.

Route dispatcher:

- `Dialects/FrontRoutePlan.lean`: `RouteGap.bufferResultCallInBody`, with
  `callResultBufferTy`, `comBodyHasBufferCall` and `comLHasBufferCallLoopBody`.
  A rolled-loop body binding a buffer-typed leaf-call result compiles to that gap
  rather than falling through to the loop-body call marshaller, which knows only
  GP and SSE registers and would emit a register move of a multi-word memory
  result. The predicate keys on call results rather than on `stackArr` bindings,
  because `mapTy (.memref n) = .stackArr 64 n` makes every memref accumulator
  `stackArr`-typed. `compile_eq_compileLoop` and `compile_denote` keep their
  statements and their axioms. Emitters that call `rolledForLoopN` directly
  bypass `compile` and so bypass the gap; `comLHasBufferCallLoopBody` is exposed
  for them to assert, and nothing asserts it yet.

Physical faithfulness of width-64 binary arithmetic:

- `X86Backend/ToLprogFaithfulBinopWide.lean`: `BinopWideBinding` covers a
  `regArith` binding at width 64. `ToLprogFaithfulBody.BinopBinding` carries a
  proof that its mnemonic is untagged and hardcodes `MOV` in its block, while
  `physBodyElem` at a `:64` head passes `MOV:64`, which is why the binop arm
  carried `w ≠ 64`. `lsemStep` reads a register-arm mnemonic only through
  `stripWidthTag`, so the difference is a congruence: `lsemStep_congr1`,
  `lsemStep_congr2` and `legalizeBinop_mnem_congr` lift it over the four spill
  shapes, and `BinopWideBinding.maintains` transports the store relation of
  `ToLprogFaithfulWriteSide` across it. The binding carries the operator rather
  than a mnemonic string, so its tag equations are computations and no
  idempotence of `stripWidthTag`, which does not hold in general, is needed.
- `X86Backend/ToLprogFaithfulMulCarrySel.lean`: a `binopWide` constructor on
  `MulCarryBinding` and a `var64` arm on `UniformRegArithMCS` and `CoverDataMCS`.
  No statement changes; the three inductives gain a constructor and every
  `cases` site is inside these modules.
- `X86Backend/ToLprogFaithfulCurve25519Fragment.lean`: `uniformRegArithMCS_eBin`,
  which depends on no axioms. All seven fragment constructors are now available,
  so every binding of every Curve25519 block is a fragment binding.

Not closed by this: `toLprogPhysAbi_faithful_uniformMCS` still does not apply to
a Curve25519 block. The blocks are `MultiReturnCom` with four outputs while the
cover data is stated over the single-return `Com`, and `CoverDataMCS` fixes one
width for the whole binding list, so the blocks' width-1 carry-in constants
cannot sit beside their width-64 bindings.

### 2026-09-15

hax front to LowCT:

- `haxToLowCT_simulates_programW` (`Hax/HaxToLowCTSim_ProgramLoops.lean`): program-level
  simulation with reverse loops (`forFoldRev` over literal bounds, lowered to `RFor` with
  the counter mapped to `hi - 1 - j`), runtime-bound loops (`forFold` from a literal to a
  variable bound, lowered to `RForRuntime`) and data-dependent loops (`whileFold` on a
  scalar guard, lowered to `RWhileNz`), under the checker `simScopeW` and the
  environment invariant `ScalarInv`; `haxToLowCT` and `AnfShaped` gain the `forFoldRev`
  and `whileFold` arms, and `denoteForLoopRev` has unfold equations and the outcome
  dichotomy in `HaxToLowCTSim_AnfShaped_Full`.
- Scalar calls computed in the scalar heap: `haxToLowCT` lowers `let name = scalar#Op(a, b)`
  for the eleven names of `scalarCallNames` (add, sub, mul, and, xor and the six
  comparisons as 0/1) to `RLetU64Zero name (RSeq (RScalarSetExpr name se) body)`, other
  argument shapes staying on `RCall`. The checkers `simScope`, `simScopeL`, `simScopeA` and
  `simScopeF` exclude these names from the tower-call arm, `simScopeW` accepts them when
  the operands are scalar and differ from the bound name, and
  `haxToLowCT_simulates_programW` takes the agreement `ScalarCallsAgree bi` of the builtin
  table with `scalarCallNat`, its leaf hypothesis now excluding the scalar names;
  `progSimW_letBind_scalar` is the new arm, and `progSimW_of_progSimA_tables` transports
  the array simulation from the table with the scalar names undefined.

Block lowering framework:

- `VIR/BlockLoweringCPS.lean`: a coverage predicate `CoveredCom Good` and
  `blockFundamental_on`, which gives whole-program denotation preservation for every
  `Good`-covered program from `Good`-gated block squares; `spliceComK` applies the
  continuation once at a block's return, and `BlockLoweringData.blockLowerComK`
  renames each source block once through a renaming accumulator, with
  `blockLowerComR_denote` and `blockLowerComK_denote_on`.
  `VIR/BlockLoweringCPSDerivedToField.lean` instantiates it at
  `derivedDialect → fieldDialect` (`lowerDerivedToFieldK_denote`,
  `lowerDoubleSquareK_denote`).
- `Algebraic/FieldWord/SingleWord.lean`: `SingleWordField p` packages a 64-bit
  word encoding of `ZMod p` with add, sub, neg, const, copy and multiply blocks as
  `Com jasminDialect` programs over `regArith`/`regConst` and their value theorems
  (`a.lookup V = enc x → b.lookup V = enc y → (mulBlk a b).denote V = enc (x * y)`),
  built from a conditional subtraction `csubW` and a fold reduction proved by
  `toNat` arithmetic. `Algebraic/FieldWord/BabyBear.lean` instantiates it at
  p = 2013265921 on the Poseidon2 multiply (`bbReduce_toNat_eq_mod`, `babyBear`),
  and `Algebraic/FieldWord/KoalaBear.lean` at p = 2130706433 with five folds
  (`reduceW_toNat`, `koalaBear`).
- `VIR/MultiBlockLowering.lean`: `MultiBlockLoweringData d d'` maps a source type to
  a list of target types and each op to a closed multi-result block over the
  flattened argument registers; `lowerMulti` splices the blocks through a renaming
  accumulator, and `multiFundamental_on` gives
  `(L.lowerMulti c).denote (flatVal enc V) = enc (c.denote V)` for covered programs
  from the block square alone, with `multiFundamentalM_on` for multi-result sources
  and `comp`/`comp_fundamental` for the composition of two multi-value lowerings.
  `VIR/MultiBlockLoweringToy.lean` lowers 128-bit additions to two 64-bit registers
  with a carry (`dwLowering_fundamental`, `prog_lowered`).
- `Algebraic/FieldToJasminWord.lean`: for `F : SingleWordField p`, the block lowering
  of the prime fragment of `fieldDialect` to `jasminDialect` with F's blocks,
  the coverage predicate `GoodW p`, `fieldToJasminWord_denote`
  (`(lowerK F c).denote (mapValW F V) = F.enc (c.denote V)` for covered programs),
  and `lowerK_exportFaithful` (lowered programs lie in the scalar fragment of
  `comLsemExportFaithful_of_scalar`). `Algebraic/Poseidon2BabyBearCompile.lean`
  writes the BabyBear width-16 permutation as a step list, proves coverage by
  induction on the list (`run_covered`) and gives `permComAt_lowerK_denote`;
  `Algebraic/Poseidon2BabyBearEmit.lean` renders it (`permAsm`, `hasUnhandled`).
- `Algebraic/FieldLimbs/Curve25519.lean`: `ZMod (2^255 - 19)` as four canonical
  little-endian 64-bit limbs (`enc`, `enc_injective`) and constant-time
  multi-result `jasminDialect` blocks with value theorems: `addBlk_denote`,
  `subBlk_denote`, `negBlk_denote`, `mulBlk_denote` (4×4 schoolbook product, folds by
  2^256 ≡ 38 and two select-based conditional subtractions), `sqrBlk_denote`,
  `constBlk_denote`, `copyBlk_denote`; the blocks use `regArith`, `regConst`,
  `mulhi`, `addCarryLo`/`addCarryHi` and `select`.
  `Algebraic/FieldToJasminLimbs25519.lean`: the `MultiBlockLoweringData` from the
  prime fragment of `fieldDialect` at 2^255 − 19 to four registers per element
  (`loweringL`, `GoodL`, `blockSquareL`, `fieldToJasminLimbs_denote`), with the
  example `mulAddProg_lowered` for `x·y + z`.
- `Algebraic/Poseidon2BabyBearSpec.lean`: `permComAt_spec` states that the compiled
  field-dialect permutation denotes `poseidon2BabyBearPermute` of the input lanes, by a
  slot-vector value semantics (`semRun`, `run_denote`) and per-segment effects
  (`externalRoundSteps_eff`, `internalRoundSteps_eff`, `externalMDSSteps_eff`,
  `internalMDSSteps_eff`, `constSteps_eff`, `permRest_eff`) composed pointwise, with
  the constant slots identified with the round constants and the diagonal
  (`constVal_cExt`, `constVal_cInt`, `constVal_cDiag`); `permJasminAt_spec` composes it
  with `permComAt_lowerK_denote`, so the lowered jasmin program computes the encoding of
  the specification.
- `Algebraic/Ed25519PointAddCompile.lean`: the a = −1 extended-coordinate Edwards
  addition as a 23-binding `Com fieldDialect` program over the eight input coordinates,
  with `pointAddProg_covered`, the value theorems `pointAddProg_m1add` and
  `addSpec_m1add` (the four outputs are the coordinates of `m1add`), and
  `pointAddProg_z3_ne_zero`: the result's `Z` is non-zero for any two points of
  `EdwardsPointExt ed25519Ext`, so the formula has no exceptional case.
  `Algebraic/Ed25519PointAddLower.lean` lowers it through `fieldToJasminLimbs_denote`
  (`pointAddProg_lowered`, `pointAddProg_lowered_m1add`).
- `VIR/MultiReturnCom.lean`: `toComHead` turns a multi-result program into a
  single-return `Com` keeping every binding and returning the first result variable,
  with `toComHead_denote`; the assembly export stores the last `outStoreMap.length`
  bindings in output order, so the returned variable fixes only the register return
  value. `Algebraic/Ed25519PointAddEmit.lean` uses it for the export of the point
  addition (`pointAddCom`, `pointAddLprog`, `pointAddAsm`, `hasUnhandled`), reading the
  32 input limb words through RSI and writing the 16 output words through RDI. What is
  proved reaches the lowered program's denotation; `toLprogPhysAbi` on this body and
  `renderOwned`'s passes are not covered, since the limb blocks' binary arithmetic at
  width 64 is still outside the faithfulness fragment.

x86 backend:

- `X86Backend/ToLprogFaithfulConst.lean`: the physical faithfulness of
  `Com.toLprogPhysAbi` extends from same-width binary `regArith` programs to programs
  that also load constants: `UniformRegArithConst`, `CoverDataConst` (the old cover
  data embeds through `CoverData.toConst`), `physBodyElem_regConst` (a constant
  binding becomes one `MOV dst, #n`), `ConstBinding.maintains`, and
  `toLprogPhysAbi_faithful_uniformConst` with its `_twoPtr` and `_epilogue` forms,
  whose conclusions are those of the `_uniform` theorems. Immediate shifts and
  programs mixing machine widths are outside it.
- `X86Backend/ToLprogFaithfulMulCarrySel.lean`: the same faithfulness extended to
  widening multiplies and carry chains. `MulHiBinding`, `AddCarryLoBinding` and
  `AddCarryHiBinding` with their `maintains` steps rest on
  `remapBlockMaintains2`/`remapBlockMaintains3`, the general remap arm of
  `physBodyElem`, so they need only the destination-injectivity obligation and carry
  no width restriction; `UniformRegArithMCS` and `CoverDataMCS` embed the constant
  fragment (`UniformRegArithConst.toMCS`, `CoverDataConst.toMCS`), and
  `toLprogPhysAbi_faithful_uniformMCS` with `_twoPtr` and `_epilogue` keeps the
  conclusions of the earlier theorems. `select` is covered too, once
  `JasminLsem.applyOpn` gained its `CMOV` arm: `SelectBinding` with its `maintains`
  step, the `select` arms of `UniformRegArithMCS` and `CoverDataMCS`, and the positive
  `lsemStep_select` in place of the earlier `lsemStep_select_eq_none`; the
  whole-program conclusions are unchanged.
- `VIR/JasminLsem.lean`: `applyOpn` models `CMOV` as `selectW (BitVec.setWidth 1 c) a b`
  on the dialect's operand order, the convention `JasminLsemWidthN.lsemStepN` already
  used, with the fidelity lemma `applyOpn_select`; no other mnemonic changes.
- `X86Backend/ToLprogFaithfulCurve25519Fragment.lean`: of the Curve25519 block
  constructors, `eConst`, `eBit`, `eMulhi`, `eAdc`, `eCarry` and `eSel` are inside the
  extended fragment, so every conditional correction of the blocks is
  (`uniformRegArithMCS_eSel`). `eBin`, binary `regArith` at width 64, is outside it: the
  fragment's binop arm carries `w ≠ 64`, which the width-64 mnemonic violates
  (`hasSuffix_withWidthTag_64_binOpName`), so the blocks as programs are not yet in the
  fragment.

- Register-count shifts from the gather's two-source `regArith .shr`/`.shl`/`.sar` export
  lower to one `.shrx`/`.shlx`/`.sarx` instruction: `lowerShiftRegJ` is the first
  alternative of `lowerAluJ2` and `lowerAluJ2InPlace` (`lowerAluJ2_shr_reg`,
  `lowerAluJ2_shl_reg`, `lowerAluJ2_sar_reg`; the immediate-count arms are unchanged,
  `lowerAluJ2_imm_count`). `lowerAluJ2_shr_reg_lsem_agree` and
  `lowerAluJ2_shl_reg_lsem_agree` relate the lowered block to the Lprog semantics when the
  count register holds a value below 64, since that semantics does not mask the count;
  `SAR` has no Lprog arm and no such theorem. `encJ_shr_reg` and
  `encodeJInstr?_lowered_shr_reg` give the block's bytes as `encShiftX`, and the gate
  accepts the P-256 bit-load shift.
- Register-count group-2 shifts: `encShiftCl` encodes `shl`/`shr`/`sar` by `%cl`
  (`REX.W D3 /ext`, round trip `roundtrip_ShiftCl`) when the count register is allocated
  to `%rcx`; `encShiftRegCount` gives no bytes for any other count register, and
  `encodableJInstr` refuses the shape (`encodeJInstr_shl_reg`, `encodeJInstr_shr_reg`,
  `encodeJInstr_sar_reg`), where the earlier arms emitted a count-0 shift; `evalInstr`
  runs `x86_SHR` on that instruction, which writes CF/SF/ZF/PF, so the flag-free
  register-count shift at the `JInstr` level is `.shlx`/`.shrx`/`.sarx`.
- `encShiftX` encodes BMI2 `shlx`/`shrx`/`sarx` (VEX `C4`, map `0F38`, `W1`, `pp` by the
  group-2 extension, opcode `F7`; bytes pinned by `decide` from the SDM fields:
  `encShiftX_shrx_rcx_rax_rdx` = `c4 e2 f3 f7 d0`), the `.shlx`/`.shrx`/`.sarx` arms of
  `encodeJInstr` go through it, and the two-source `Lopn "SHL:64"/"SHR:64"/"SAR:64"
  [val, count]` form of `encodeLopn` emits it (`encodeLopn_shr_regCount_bytes`,
  `encodableLinstrR_shr_regCount`), which is faithful to the value-only `JasminLsem`
  semantics of that form; `x86_SHR_word_eq_SHRX`, `x86_SHL_word_eq_SHLX`,
  `x86_SAR_word_eq_SARX` relate the data words of the two forms for every count.

Jasmin lowering and the psem mirror:

- `RLetU64Zero` lowers to the typed zero `(64u)0` (`Papp1 (Oword_of_int U64) (Pconst 0)`)
  and the `RWhileNz` guard compares against it; the printers render both forms as
  before. `MirrorSimFragment` covers `RLetU64Zero` and `RCloneCall`;
  `corresSem_while` (a count function and `iterFold`) is the `Cwhile` rule over the
  mirror's `Sem`, instantiated as `corresSem_whileNz` with
  `toJasminCmd_whileNz_mirror_exec`; `ccall_arrsN_semIr`, `corresTrans_callN` and the
  swap instance cover multi-output calls; `iterFold_eq_nfold` ties the loop to the
  ascent; witnesses `letZeroSetProg_mirror_exec`, `whileClearProg_mirror_exec`,
  `cloneCallProg_mirror_exec`, `swapCallProg_mirror_exec`.

Dialect front:

- Literal slots: an `RLimbStore ⟨x, .TFp⟩ idx v` whose destination is not yet bound
  (the shape `litTower` produces for literal call arguments) translates to `bvConst 64 v`
  followed by the leaf call `extCall (limbLitLeafName idx)`, which binds the six-limb
  memref; `semScalar` binds the default memref and `semScalarL` the oracle's value at that
  leaf, `translateDialectFull_denoteWith`, the leak factoring, the typed `expand`
  (`[bvConst, extCall:limbLit:idx]` on an unbound destination, `[bvConst, memrefSet]` on
  a bound one) and `rustExecSimulatesDialect` cover the arm; `corresL_of_corres_eqOn`
  (`Ascent/GuardsLeaf.lean`) carries the limb-store leaf rule, since `semScalarL ls`
  and `semScalar` differ on an `RLimbStore` into an unbound destination.

Leak traces:

- `Dialects/CryptoDialectLeakExpansion.lean`: `translateDialectFull_leakTrace_expand`
  and `lowerSExpr_leakTrace_expand` state that the leak-factor trace of the front's
  continuation is `expand` of the LowCT program at the entry typing;
  `selectMaskCont_leakFactorsTrace_eq` and `arrLoadCont_leakFactorsTrace_eq` give the
  select and array-load continuations their traces.
- `notTmp_of_headNe` (a name whose first character is not `_` is not a fresh temporary
  of the `SExpr` lowering) is in `TranslateDialectScalarDenote`, shared by
  `Secp256k1PointOpFrontCovered` and the dev P-256 module.
- `haxToLowCT_simulates_programT`: program-level simulation for builtin tables whose
  results are scalars, under `envAgreesRustT`, the argument-relating leaf condition
  `LeafCallAgreesArgs` and scalar-bound conditions `condsScalar`, for tables
  implementing neither `index` nor `array_update`.
- `haxToLowCT_simulates_programL`: the same for `litTower T` of the lowering, which
  stores literal call arguments in `.TFp` slots with `RLimbStore`, under `simScopeL`
  and `LitStoreAgrees`; `litTower_nil` and `simScopeL_nil` give the case `T = []`.
- `haxToLowCT_simulates_full` is restated as a corollary of
  `haxToLowCT_simulates_program` for programs accepted by `simScope`, with exit-scope
  invariants; `simFull_runs` instantiates all its hypotheses at `let y = leaf(a); y`.
- `pipelineAppInvariants_unsat`: no environment and state satisfy
  `PipelineAppInvariants`.
- `scripts/vacuous-theorem-ratchet.sh` counts hypotheses quantified over every state
  without restriction, with baseline 0.

LowCT to JasminAST:

- `rustExecSimulates` and its inline and empty-registry forms take no leaf hypothesis;
  `rustCallSimulates` and the limb-store, call-N, select and clone-call simulations take
  their implementation hypotheses at the fuel they use, and
  `rustExecSimulates_withCalls` at every fuel `≥ 2`.
- `not_forall_leafImplOk`, `not_forall_leafImplOkNewSid`, `not_forall_callNImplOk`,
  `not_forall_limbStoreImplOk`, `not_forall_selectImplOk`, `not_forall_cloneImplOk`:
  the all-fuel forms of the implementation hypotheses are false.
- `execSopn` gives the pseudo-operations `STORE64`, `CMOV` and `CLONE_TOWER` their heap
  semantics; `limbStoreImplOk_storeLeafSpec`, `selectImplOk_of_two_le`,
  `cloneImplOk_of_two_le`, `leafImplOk_storeLeafSpec` and `callNImplOk_storeLeafSpec`
  state the implementation hypotheses at every fuel `≥ 2`.
- `translateInstrR` keeps the caller scope at `Ccall` and writes the callee's results to
  the call's l-values; `leafImplOk_pureLeafEnv` holds for environments of pure
  functions, `leafImplOkNewSid_addLeafSpec` and `callNImplOk_addCallNLeafSpec` for a
  bytewise-addition leaf, and `addProg_simulates` instantiates
  `rustExecSimulates_withCalls` on a program with such a call.
- `translateCmd_newSid`: `Cfor` keeps the entry scope, so every translated command
  does; `translateFun_countLoop_eval` runs a function body that writes a variable
  before, inside and after a counted loop.
- `toJasminCmd_translateCmdExt_isSome`: `toJasminCmd` output on `callFreePlusCall`
  programs has a `psem.v` mirror translation; `toJasminCmd_corresTrans` and
  `toJasminCmd_mirror_exec` relate the `RawCode` run and the mirror run on
  `MirrorSimFragment`, given a correspondence for each call, with the call rule
  instantiated at a copying function (`corresTrans_call_copy`).
- `sboxArray_size` and `invSboxArray_size` are proved by `decide +kernel`.

The `psem.v` mirror:

- `corresSem_append`, `corresSem_exec`: sequencing of the correspondence `CorresSem`
  over `Sem`, and its reading as a run of `execCmd`.
- `copn_regs_semIr`: `Copn` over register and flag operands, with `x86AsmSem` giving
  `MULX_64`, `ADCX_64` and `CMOVcc_64` their result tuples.
- `corresSem_for`: `Cfor` with any body at `forFold`.
- `ccall_words_semIr`, `ccall_leaf_of_body`: `Ccall` from a derivation of the callee
  body.
- `mulhiLoop_mirror_runBlock`: a mirror loop calling a `MULX` function ends with the
  word the `runBlock` `MULX` loop leaves.

Leaf oracles:

- `cryptoDialectToJasminCom_denote_eq_of_transport`: the jasmin lowering preserves
  denotation for every oracle pair related by `LeafTransport`.
- `semScalar_eq_semScalarL`, `semU_eq_semUL`: the waist semantics at a leaf oracle,
  `semScalarL` and `semUL`, are `semScalar` and `semU` at `defaultLeaf`.
- `rustExec_semScalarL_call`, `rustExec_semScalarL_arrLoadLit`: `RustExec` call and
  literal array-load steps agree with `semScalarL` under `CallAgrees` and
  `ArrLoadAgrees`.
- `ascendGLL_sound`: the total abstraction with abstract leaves, with the leaf rules
  `corresL_call`, `corresL_selectLeaf`, `corresL_arrLoadLitLeaf` and the example
  `leafK_corres`.
- `translateDialectFull_denoteWith`, `translateDialectControl_denote_ctlWith`: front
  preservation at every leaf oracle; `translateDialectFull_denote` and
  `translateDialectControl_denote_ctl` are their instances at `defaultLeaf`.
- `semScalarLToJasminCom_denote_eq`: `semScalarL` through the front and the jasmin
  lowering at an oracle pair related by `LeafTransport`; `leafTransport_leafOfAbs` and
  `leafK_semScalarLToJasminCom`.

Ascent:

- `corresU_whileFun`, `corresU_whileFun_total`: a terminating `RWhileNz` run
  corresponds to the exit state `loopFun` of the abstract loop; `sumLoop_corres` and
  `sumLoop_total` apply them to a summing countdown loop.

Backends:

- `mldsa_ntt_4way_denotation_preserves`, `mlkem_ntt_4way_denotation_preserves`: the
  ML-DSA and ML-KEM 4-way kernel bodies render to the emitted text and, under
  `runNtt4way`, write the Cooley–Tukey butterflies of their input chunks in wrapping
  word arithmetic (`runNtt4way_body`).
- `sboxSpec64_modEq`: the width-64 Poseidon2 BabyBear S-box satisfies
  `sboxSpec64 x · 2^(32·6) ≡ x^7 (mod p)` for `x ≤ 1756563332`; `montMulSpec64_exact`
  states that a REDC step is an exact division when `a·b + (2^32 − 1)·p < 2^64`, and
  `montMulSpec64_step` its bound and congruence.
- `mul2625_decode`, `edwardsAdd2625_decode`: the packed Curve25519 multiply
  `reduce19 (prod19 a b)` decodes to the field product, with no hypothesis on the
  reduction, and the packed Edwards addition to `ed25519AffineAdd` for a limb vector
  decoding to `d`;
  `lmuludq_toNat` gives the 64-bit `VPMULUDQ` lane, and `jccLane_not_dataIndep` and
  `gatherLane_not_dataIndep` state that the data-independence predicate is false on
  lane branches and gathers.
- `lowerAVX512_correct`, `lowerInst_denote`: the AVX-512 instruction semantics
  `AVX512Inst.denote512` is determined by mnemonic family and width; the
  `lowerAVX512_*_w*` theorems state the forms without an instruction and the `exts_*`
  theorems the required CPU extensions.
- `looped_eq_unrolled_denote` (ARM and RISC-V): the loop interpreters `runALoop` and
  `runRLoop` of the emitted label, body and back-edge run to the state of the unrolled
  block when the body decrements the counter.
- `ArmRegAlloc.reload_sandwich`: after a spill store, a block that does not write the
  spilled register leaves the reload a no-op.
- Docstrings of the ARM, RISC-V, vector and tile backends state the content of their
  theorems (`regProgToArmBytes_spec` relates no bytes to semantics;
  `RiscvX25519FieldKernel.ladderStep_composition` is block concatenation).

### Earlier unreleased changes

- `JInstr` covers Jasmin's scalar `x86_op` set except the instructions declined for
  constant time: `inc`, `dec`, `clc`, `stc`, `xchg`, three-operand `imul`, one-operand
  `mul` and `imul`, `shld`, `shrd`, `rcl`, `rcr`, `cmovcc` and `setcc` over the sixteen
  conditions, sized `test`, `bt`, `btr` and `bts`. Register allocation, rescheduling,
  flag liveness, `Mem2Reg`, store-to-load forwarding, secret typing, the cost model, the
  encoder, the printer and the constant-time leakage state each new instruction's reads
  and writes.
- Hand-written assembly: `NasmParse` reads CryptOpt's NASM output, and
  `solinasSquare_correct` proves the CryptOpt `solinas_square` kernel against
  fiat-crypto's `sqr_correct` for `2^255 - 19` ([ASCENT.md](ASCENT.md), "Hand-written
  assembly").
- `addMod251_front_weld` relates the relational compiler's ZMod 251 addition, the
  front's compilation of `r := a + b mod 251` and the ascent's `SRenc` states.
- The dialect classification gate (`scripts/dialect-lowering-ratchet.sh`) runs in this
  package.
- The `Veir` dependency `spitters/veir-catcrypt` is a public repository; a build needs
  no credentials ([BUILDING.md](BUILDING.md#the-veir-dependency)).
- [bench.md](bench.md) states that its ratios were measured in the development
  repository and cannot be reproduced from this package, names the reference each
  ratio was measured against, and marks the rows whose timed object file is not
  shipped; [bench/PROVENANCE.md](bench/PROVENANCE.md) names the declaration or
  executable that writes each shipped assembly file.
- `scripts/check-doc-paths.sh` checks that file paths in document code spans name
  tracked files, and `scripts/lint-lean-prose.sh --docs` covers every tracked
  document.

## 0.1.0-alpha.2 — 2026-09-13 (pre-release)

Changes since `v0.1.0-alpha.1`. The toolchain, the dependency pins, the module set
and the set of theorems have changed; the list below records the main changes.

- Lean toolchain `v4.33.1` (the release used `v4.30.0`), with mathlib, CompPoly and
  doc-gen4 at `v4.33.1` and the other dependencies pinned by commit or tag. `Veir`
  resolves from the fork `spitters/veir-catcrypt`, then private (the release required
  `opencompl/veir` at `v4.29.0`).
- The package was resynced from the CatCrypt development and holds 2389 Lean modules
  under `CatCrypt/` (the release held 1851). The library names its modules one by one
  in `lakefile.lean`; `scripts/gen-module-globs.sh` generates the list and CI checks
  that it is fresh.
- The hax front reads the AST and evaluator of hax-lean (`HaxLean.AST`), and the
  simulation theorems for the translation from that AST to LowCT are in
  `CatCrypt/Crypto/Hax/` (for example `haxToLowCT_simulates_program`).
- The ascent (`CatCrypt/Crypto/SecureCompilation/Ascent/`, 11 modules at the release,
  100 now) proves that programs at the compiler's low levels compute Lean
  specifications; [ASCENT.md](ASCENT.md) is its guide.
- Removed theorems: the constant-time and noninterference preservation bridge built
  on `Com.all_com_ct`, which holds of every program, and definitions whose value was
  the constant `True`. [README.md](README.md#limitations) lists the three
  `True`-valued predicates that remain.
- New documentation: `GETTING_STARTED.md`, `DEMO.md`, `EXAMPLES.md`, `PROVENANCE.md`,
  `CAPABILITIES.md`, `bench.md`, and the Verso manual under `docs/`, a separate Lake
  package, so verso is not a dependency of the library. `DOCS.md` was removed.
- New module `CatCrypt/Crypto/SecureCompilation/CompilerHelloDemo.lean`: a routine
  written in Lean as a term of the scalar front's `Thir` input type, lowered by the
  front and compiled to AArch64, with the assembly printed.
- `X86Backend/_MpnFrontCheck.lean` and `X86Backend/_MpnFrontScratch.lean` were
  removed. `Dialects/ByteMemrefFrontPrototype.lean` was removed and returned with the
  resync.
- CI: a push to `master` runs the static gates only; the build job runs on a weekly
  schedule, on demand and on pull requests, and sets `LEAN_NUM_THREADS` to `1` to fit
  the runner memory.

## 0.1.0-alpha.1 — 2026-07-18 (pre-release)

Pre-release research code (SemVer pre-release; major version 0). Interfaces, the
covered source fragment, and the trust surface may change without notice — do not
depend on it as a stable API. The CatCrypt compiler as a standalone Lake package.

- Two fronts (hax/Rust → LowCT → `Com` IR) lowering to one x86/ARM/RISC-V backend,
  packaged as the import-closure of the compiler subtree (1851 modules), free of every
  scheme security proof and of the `MPC`/`Examples` protocol proofs.
- Theorems `rustToJasminCom_endToEnd`, on the `IsCoveredCtl` fragment and with the
  value equation `hAdequacy` as a hypothesis, and `robustCompilation_source_to_x86`
  and `compile_correct_all`, over the lattice dialect.
- The package declared 613 `axiom`s, counted with the command given in
  [README.md](README.md#limitations); `AxiomAudit.lean` prints the axioms of the
  theorems it lists.
- Dependencies resolve from git (`catcryptCore`, `Veir`, `paramTransfer`,
  `CompPoly`, `hax-lean`, `mathlib`); MIT licensed; `CITATION.cff` (ePrint 2026/604).

> Experimental research prototype — not a production tool.
