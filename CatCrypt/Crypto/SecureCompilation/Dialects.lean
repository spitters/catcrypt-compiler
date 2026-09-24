/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminDenote
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.MemrefToJasminDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.MemrefToJasminDenote
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FuncToJasminDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.FuncToJasminDenote
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.VectorToJasminDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.VectorToJasminDenote
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithLegality
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithLegality
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ComLegality
public import CatCrypt.Crypto.SecureCompilation.Dialects.ComLegality
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.MlirArithArithAgree
public import CatCrypt.Crypto.SecureCompilation.Dialects.MlirArithArithAgree
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceShifts
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceShifts
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ConstantTimeTrait
public import CatCrypt.Crypto.SecureCompilation.Dialects.ConstantTimeTrait
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.RngRealization
public import CatCrypt.Crypto.SecureCompilation.Dialects.RngRealization
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToLprog
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToLprog
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselSoundness
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselSoundness
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselPass
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselPass
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect
public import CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceLet
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceLet
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceRustState
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceRustState
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceBody
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceBody
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.RngRealizationFinite
public import CatCrypt.Crypto.SecureCompilation.Dialects.RngRealizationFinite
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithEmulations
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithEmulations
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.RngLeaf
public import CatCrypt.Crypto.SecureCompilation.Dialects.RngLeaf
-- The crypto dialect's SPComp security interpretation, its security and leak-trace
-- layers, and the direct dialect front.
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
public import CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurity
public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurity
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace
public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurityNative
public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurityNative
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTraceNative
public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTraceNative
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
-- Crypto kernels lifted to the neutral arith dialect: the emit-legality
-- foundation (ArithOK64 + lowerArithToJasmin_ComOK) + the ~50 lifted kernels, each
-- denote=spec + ArithOK64 + lowered ComOK + arm/riscv e2e through the proven lowering.
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminComOK
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminComOK
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithGoldenPathField
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithGoldenPathField
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithHashesGoldenPath
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithHashesGoldenPath
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithAsconGoldenPath
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithAsconGoldenPath
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithArxGoldenPath
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithArxGoldenPath
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithFieldGoldenPath
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithFieldGoldenPath
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithBitwiseGoldenPath
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithBitwiseGoldenPath
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithVarShiftGoldenPath
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithVarShiftGoldenPath
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithFieldMul2x1GoldenPath
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithFieldMul2x1GoldenPath
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.MemrefCtGoldenPath
public import CatCrypt.Crypto.SecureCompilation.Dialects.MemrefCtGoldenPath
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminLoadSymExport
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminLoadSymExport
-- Encoder modules (rot-guarded here rather than in the
-- SecureCompilationAll manifest): the encodeLprog≡encodeJBlock byte-agreement +
-- its native_decide-free mnemonic dispatch, the additive framed/reloc JInstr emit
-- path, and the Linstr→JInstr lowering-coverage superset (ADX + indexed memory).
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFramedEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFramedEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstrLeaq
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstrLeaq
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ResolverAgree
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ResolverAgree
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageMulxMemSym
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageMulxMemSym
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.BlockBytesAgreeExtended
public import CatCrypt.Crypto.SecureCompilation.X86Backend.BlockBytesAgreeExtended
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.FramingReconcile
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FramingReconcile
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.GoldenPathByteIdentityDemo
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GoldenPathByteIdentityDemo
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherLsemTie
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherLsemTie
public meta import CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialect
public import CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialect
public meta import CatCrypt.Crypto.SecureCompilation.Jasmin.S2NBignumSSADialect
public import CatCrypt.Crypto.SecureCompilation.Jasmin.S2NBignumSSADialect
public meta import CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialectNative
public import CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialectNative

/-!
# The upstream-aligned neutral dialects (manifest / rot-guard)

The target-neutral dialects of the MLIR dialect alignment, defined CatCrypt-side (in `Dialects/`, NOT in vendored `VIR/`), each with a
verified `Com <dialect> → Com jasmin` lowering AND a denotation-preservation proof
(the `transTy` framework, mirroring `LatticeToJasminDenote`).

Each import pulls the full triple (dialect + lowering + denote-preservation):

* `arith`  — the neutral integer-arithmetic fragment (the `SupportedOp` set).
* `memref` — `memref.load`/`store` over `stackArr`.
* `func`   — `func.call`/`callN` over `extCall`.
* `vector` — `vector.pack` (AVX-512 8×u64) over `vpackZMM`.

All four are denotation-preserving and axiom-clean (`propext`, `Quot.sound`). This
module forces the whole set so a `Dialect`/`JasminDialect`/framework change can't
silently rot any of them. The neutral op/type names mirror Veir's `OpCode`/`TypeAttr`.

`cf`/`scf` (control flow) are NOT ANF `Com` ops — the VIR `Com` is region-free,
single-return — so they are handled by the bounded-loop-unroll / branch-lowering
machinery, not as dialect-op triples here. The `crypto`/`thir`/`tile` front dialects
are defined elsewhere.

Further results ship alongside the dialect triples:

* `ArithLegality` — the firewall bridge `SupportedOp op ↔ ∃ aop, aop.toJasmin = op
  ∧ aop.width = 64`: the neutral `SupportedOp` jasmin fragment IS exactly the width-64
  image of the `arith` dialect, so the coincidence of the `SupportedOp` firewall with
  `arith` is a *theorem*, robust to firewall refactors.
* `ComLegality` — the verified legality helper: a decidable `comAllSupported :
  Com jasminDialect → Bool` proved equivalent (`comAllSupported_iff`) to the
  propositional `ComSupported` ("every op is in the `SupportedOp` legal set"),
  generalizing the `gatherJBlock`-returns-`none` guard into a typed, proven check
  (`isSupportedOp_iff` + `DecidablePred SupportedOp`).
* `ArithEmulations` — the neutral-arith emulation / conformance suite: the
  branchless idioms `and-not`, `select`-by-mask, and `rotate-right`-by-immediate built
  as derived `Com arithDialect` programs over the neutral op set, each with a
  machine-checked `Com.denote` correctness proof (symbolic width; the `rotateRight`
  corollary at width 64). These emulations ARE the legalization baseline (native
  CMOV/ROR/ANDN are pure-perf ISel below the waist).
* `MlirArithArithAgree` — the front↔back arith tie: the upstream-named
  `mlirArithDialect` (front, over `CryptoTy`, refines `catCryptDialect`) and this
  `arithDialect` (back, over `ArithTy`, lowers to `jasminDialect`) realize IDENTICAL
  `BitVec` semantics on the shared 9-op integer fragment (`addi`/…/`xori`,
  immediate shifts, constant) — proved extensionally (no HEq), so the two `arith`
  dialects are one semantics at two layers, not divergent duplicates.
* `FrontendCoincidence` — the frontend-coincidence base cases: the two denotations
  of a pure-scalar Rust `ImpExpr` — Path A `denoteScalar` (scalar-THIR-direct) and
  Path B `SExpr.evalBV` (the LowCT scalar evaluator) — COINCIDE at `w = 64` under an
  `EnvAgree` predicate, on the full variable/literal/binary-ALU fragment
  (`add/sub/mul/and/xor`). The `.letBind` arm and the shift/rotate arms
  (Path A immediate vs `SExpr` dynamic, no rotate node) are outside this fragment.
* `RngLeaf` — the deterministic entropy-read leaf: the crypto dialect's
  `sampleBit`/`sampleBv n` modeled as total deterministic reads over an `Entropy`
  stream (range + determinism lemmas proved), a lowerable counterpart to the
  sample ops. The probabilistic `SPComp.sample` meaning stays a *separate* security
  interpretation (the uniform-entropy realization is in `RngRealization`).
-/

@[expose] public section
