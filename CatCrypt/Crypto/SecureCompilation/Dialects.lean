/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminDenote
import CatCrypt.Crypto.SecureCompilation.Dialects.MemrefToJasminDenote
import CatCrypt.Crypto.SecureCompilation.Dialects.FuncToJasminDenote
import CatCrypt.Crypto.SecureCompilation.Dialects.VectorToJasminDenote
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithLegality
import CatCrypt.Crypto.SecureCompilation.Dialects.ComLegality
import CatCrypt.Crypto.SecureCompilation.Dialects.MlirArithArithAgree
import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence
import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceShifts
import CatCrypt.Crypto.SecureCompilation.Dialects.ConstantTimeTrait
import CatCrypt.Crypto.SecureCompilation.Dialects.RngRealization
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToLprog
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselSoundness
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithIselPass
import CatCrypt.Crypto.SecureCompilation.Dialects.RorImmSelect
import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceLet
import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceRustState
import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceBody
import CatCrypt.Crypto.SecureCompilation.Dialects.RngRealizationFinite
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithEmulations
import CatCrypt.Crypto.SecureCompilation.Dialects.RngLeaf
-- DR collapse phase 2: the crypto dialect's SPComp security interpretation + the
-- full CryptoSSA ≅ crypto agreement (sample ops included).
import CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurity
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurityNative
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTraceNative
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
-- Item 1 (crypto kernels lifted to the neutral arith dialect): the emit-legality
-- foundation (ArithOK64 + lowerArithToJasmin_ComOK) + the ~50 lifted kernels, each
-- denote=spec + ArithOK64 + lowered ComOK + arm/riscv e2e through the proven lowering.
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminComOK
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithGoldenPathField
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithHashesGoldenPath
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithAsconGoldenPath
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithArxGoldenPath
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithFieldGoldenPath
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithBitwiseGoldenPath
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithVarShiftGoldenPath
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithFieldMul2x1GoldenPath
import CatCrypt.Crypto.SecureCompilation.Dialects.MemrefCtGoldenPath
import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminLoadSymExport
-- D4 collapse encoder-maturation (rot-guarded here to avoid the churning
-- SecureCompilationAll manifest): the encodeLprog≡encodeJBlock byte-agreement +
-- its native_decide-free mnemonic dispatch, the additive framed/reloc JInstr emit
-- path, and the Linstr→JInstr lowering-coverage superset (ADX + indexed memory).
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch
import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFramedEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr
import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstrLeaq
import CatCrypt.Crypto.SecureCompilation.X86Backend.ResolverAgree
import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar
import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageMulxMemSym
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstr
import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended
import CatCrypt.Crypto.SecureCompilation.X86Backend.BlockBytesAgreeExtended
import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather
import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
import CatCrypt.Crypto.SecureCompilation.X86Backend.FramingReconcile
import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody
import CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import CatCrypt.Crypto.SecureCompilation.X86Backend.GoldenPathByteIdentityDemo
import CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialect
import CatCrypt.Crypto.SecureCompilation.Jasmin.S2NBignumSSADialect
import CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialectNative

/-!
# The upstream-aligned neutral dialects (D0 manifest / rot-guard)

The MLIR dialect-alignment restructure's D0 phase: the target-neutral
dialects defined CatCrypt-side (in `Dialects/`, NOT in vendored `VIR/`), each with a
verified `Com <dialect> → Com jasmin` lowering AND a denotation-preservation proof
(the `transTy` framework, mirroring `LatticeToJasminDenote`).

Each import pulls the full triple (dialect + lowering + denote-preservation):

* `arith`  — the neutral integer-arithmetic fragment (the `SupportedOp` set).
* `memref` — `memref.load`/`store` over `stackArr`.
* `func`   — `func.call`/`callN` over `extCall`.
* `vector` — `vector.pack` (AVX-512 8×u64) over `vpackZMM`.

All four are denotation-preserving and axiom-clean (`propext`, `Quot.sound`). This
module forces the whole set so a `Dialect`/`JasminDialect`/framework change can't
silently rot any of them. The neutral op/type names mirror Veir's `OpCode`/`TypeAttr`
(migration contract, plan §0.3).

`cf`/`scf` (control flow) are NOT ANF `Com` ops — the VIR `Com` is region-free,
single-return — so they are handled by the bounded-loop-unroll / branch-lowering
machinery, not as dialect-op triples here. `crypto`/`thir`/`tile` front dialects
already exist (plan §2c).

Two further D0/DR results ship alongside the dialect triples:

* `ArithLegality` — the D0 firewall bridge `SupportedOp op ↔ ∃ aop, aop.toJasmin = op
  ∧ aop.width = 64`: the neutral `SupportedOp` jasmin fragment IS exactly the width-64
  image of the `arith` dialect, so "the `SupportedOp` firewall re-points to `arith`"
  (plan D0/D1) is a *theorem*, robust to firewall refactors.
* `ComLegality` — the D0 verified legality helper: a decidable `comAllSupported :
  Com jasminDialect → Bool` proved equivalent (`comAllSupported_iff`) to the
  propositional `ComSupported` ("every op is in the `SupportedOp` legal set"),
  generalizing the old `gatherJBlock`-returns-`none` guard into a typed, proven check
  (`isSupportedOp_iff` + `DecidablePred SupportedOp`).
* `ArithEmulations` — the D1 neutral-arith emulation / conformance suite: the
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
* `FrontendCoincidence` — the DF keystone (base cases): the two frontend denotations
  of a pure-scalar Rust `ImpExpr` — Path A `denoteScalar` (scalar-THIR-direct) and
  Path B `SExpr.evalBV` (the LowCT scalar evaluator) — COINCIDE at `w = 64` under an
  `EnvAgree` predicate, on the full variable/literal/binary-ALU fragment
  (`add/sub/mul/and/xor`). The `.letBind` extension and the shift/rotate arms
  (Path A immediate vs `SExpr` dynamic, no rotate node) are the analyzed next
  increments — the two ingestion paths become one meaning on the heap-free leaf.
* `RngLeaf` — the DR-randomness deterministic entropy-read leaf: CryptoSSA's
  `sampleBit`/`sampleBv n` modeled as total deterministic reads over an `Entropy`
  stream (range + determinism lemmas proved), the lowerable counterpart to the
  drop-to-`none` at `CryptoToVIR.lean:86,118`. The probabilistic `SPComp.sample`
  meaning stays a *separate* security interpretation (the uniform-entropy realization
  theorem is the next DR step).
-/
