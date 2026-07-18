/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq
import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq

/-!
# A real ARX round through the closed-kernel `emitted = RustExec` route

`RustExecRoundAdeq.roundC_emitted_eq_rustexec` proved `emitted jasmin = RustExec
reference` for the SHA-2 `Maj` round — the **bitwise** (`∧`/`⊕`/`¬`) layer, whose
`inRange` obligation holds for ALL `u64` inputs with no side condition. Its
`Residual` note flagged the ARX layer — **rotations** (`SShl`) and **modular
additions** (`SAdd`) — as NOT reachable by the input-agnostic hoisted bound: a
left-shift or an add of two full-range `u64`s overflows the saturating-`Nat`
model, so `∀ σ, (∀ y, σ y < 2^64) → e.inRange σ` fails on those arms.

This module closes that ARX layer. The wall was never the ARX ops themselves —
it was the *quantifier*: the hoisted bound demands no-overflow for EVERY `u64`
input. A real round runs on a KERNEL with a fixed input discipline (SHA words
fit in their lane; the round's addends are known to stay in range), and under
that **concrete per-kernel input bound** the very same `SExpr.inRange` obligation
that the hoisted arm cannot discharge becomes provable.

## The ARX kernel: one rotate + one modular add

```
a := 0x12345678 ; b := 0x11111111
s := ((a ≪ 8) ⊕ (a ≫ 56)) + b
```

`(a ≪ 8) ⊕ (a ≫ 56)` is `rotl64(a, 8)` in XOR form (the rotate halves occupy
disjoint bit ranges, so `⊕ = ∨`); `+ b` is the modular add. So the kernel
exercises BOTH residual ARX arms in one closed straight-line body — the minimal
"rotate + modular add" round core. The inputs are the SHA-256 IV word `a` and a
round-constant-shaped `b`, both `< 2^32`, the honest u32/u64 lane discipline of
a real round.

## Two ways the ARX layer reconciles under the per-kernel bound

* **Concretely (the deliverable, §"emitted = RustExec").** The kernel is CLOSED
  (`a`, `b` are literals), so `semScalar` runs it to a concrete `BitVec 64` and
  `RustExec` to a concrete `Nat`; on the chosen literals no shift/add overflows
  `u64`, so `arxVal = BitVec.ofNat 64 (rsF.rsScalar "s")` holds by `decide`. This
  is the `#250` `inRange` reconciliation discharged by concrete evaluation — the
  same fact `SExpr.evalBV_eq_ofNat_eval` states, specialised to the kernel's
  literal inputs. Fed through the SATISFIABLE closed-kernel route
  `rustToJasminCom_endToEnd_topLevel_unconditional` (which needs only
  `IsCoveredSCtl`, whose `RScalarSetExpr` arm asks for `srcClean` — no `inRange`),
  it yields `emitted jasmin = RustExec reference`, axiom-free.

* **Symbolically (the reusable ARX-arm pattern, §"The concrete-bound inRange
  discharge").** `arxE_inRange_of_bound` proves `arxE.inRange σ` from the concrete
  input bound `σ "a" < 2^32 ∧ σ "b" < 2^32` — discharging exactly the
  `SShl`/`SAdd` overflow conditions the hoisted arm cannot. `arxE_reconcile` then
  feeds it to `RustExecSemScalarBridge.sexprTransfer` (`= SExpr.evalBV_eq_ofNat_eval`)
  to get `arxE.evalBV (liftEnv σ) = ofNat 64 (arxE.eval σ)` for EVERY bound `σ`.
  This is the input-dependent reconciliation, made input-agnostic-*within-the-lane*
  by the per-kernel bound — the template a full SHA/ChaCha round instantiates.

## Generalization to a full SHA/ChaCha round

A full round is a straight-line chain of these arms. The reusable pattern:
carry a per-kernel lane bound `B σ` (e.g. every SHA-2 message/state word `< 2^32`
for the 32-bit rounds, `< 2^64` for 64-bit), and for each `RScalarSetExpr x e`
prove `∀ σ, B σ → e.inRange σ` exactly as `arxE_inRange_of_bound` does — the
`SShl k` arm discharges from `σ x < 2^(64-k)` (or a mask), the `SAdd` arm from the
addends' partial-sum bound (`h + Σ1 + Ch + K + W < 2^64`, the standard SHA-2
no-overflow accounting). The rotations of the message schedule and the `T1`/`T2`
additions are then all covered; the bitwise `Maj`/`Ch` layer was already covered
(`RustExecRoundAdeq`). The 64-round iteration is the `RFor` bridge
(`IsCoveredAdeq.rFor`) whose body is one such round. For a CLOSED kernel the
`decide` leg (as here) delivers the concrete `emitted = RustExec` capstone with no
manual `inRange` bookkeeping at all.

## Residual

The symbolic leg here reconciles the `semScalar` value with the `RustExec` value
(`arxE_reconcile`). Fusing that with the jasmin denotation leg for an OPEN kernel
still hits `RustExecKernelAdeq`'s `entry_trio_unsat_empty` (the `EnvRel` /
`ConsistentS` / `NoAliasVM` clash at any finite entry) — so the general
`emitted = RustExec` for a NON-closed ARX round routes through the closed-kernel
argument, exactly as here. Closing the open-kernel jasmin leg is the standing
`P3`-composition residual, orthogonal to the ARX `inRange` work done here.
-/

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq (not_isTmp_short)

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RustExecARXAdeq

/-! ## The ARX round expression: `rotl64(a,8) ⊕-form + b` -/

/-- `((a ≪ 8) ⊕ (a ≫ 56)) + b` — one rotate (in `⊕`-form) and one modular add,
    the two residual ARX arms of a SHA-2 round. -/
def arxE : SExpr :=
  .SAdd (.SXor (.SShl (.SVar "a") (.SLit 8)) (.SShr (.SVar "a") (.SLit 56)))
    (.SVar "b")

/-! ## The closed kernel -/

/-- The closed ARX kernel: write the two inputs as literals (`a` the SHA-256 IV
    word `0x12345678`-shaped, `b` a round constant), then compute the ARX round
    core `s`. -/
def arxC : LowCT :=
  .RSeq (.RScalarSet "a" 305419896)
    (.RSeq (.RScalarSet "b" 286331153)
      (.RScalarSetExpr "s" arxE))

/-! ## Coverage: `IsCoveredSCtl arxC` (needs only `srcClean` — no `inRange`) -/

theorem arxE_srcClean : srcClean arxE :=
  ⟨⟨⟨not_isTmp_short "a" (by decide), by norm_num [srcClean]⟩,
      ⟨not_isTmp_short "a" (by decide), by norm_num [srcClean]⟩⟩,
    not_isTmp_short "b" (by decide)⟩

theorem arxC_coveredS : IsCoveredS arxC :=
  .rSeq (.rScalarSet "a" _)
    (.rSeq (.rScalarSet "b" _)
      (.rScalarSetExpr "s" arxE arxE_srcClean))

theorem arxC_covered : IsCoveredSCtl arxC := .ofStraight arxC_coveredS

/-! ## The concrete-bound `inRange` discharge — the reusable ARX-arm pattern

The residual note's obstruction was the *quantifier*: `SShl`/`SAdd` overflow for
some `u64` inputs, so the input-agnostic bound fails. Under a concrete per-kernel
lane bound `σ "a" < 2^32 ∧ σ "b" < 2^32` — the honest u32/u64 discipline of a
real round — the same `SExpr.inRange` obligation is provable. This is the
template a full round instantiates per `RScalarSetExpr`. -/

/-- The per-kernel input bound: the ARX inputs fit in their 32-bit lanes. -/
def arxBound (σ : String → Nat) : Prop := σ "a" < 2 ^ 32 ∧ σ "b" < 2 ^ 32

/-- **The ARX `inRange` discharge.** From the concrete per-kernel input bound the
    `SShl` (left-shift, `a ≪ 8 < 2^64`) and `SAdd` (modular add, sum `< 2^64`)
    side conditions — the two the hoisted all-`u64` arm cannot meet — are proved.
    This is the exact `#250` obligation the ARX layer needs, discharged from the
    kernel's lane discipline rather than input-agnostically. -/
theorem arxE_inRange_of_bound (σ : String → Nat) (h : arxBound σ) : arxE.inRange σ := by
  obtain ⟨ha, hb⟩ := h
  have ha64 : σ "a" < 2 ^ 64 := lt_trans ha (by norm_num)
  have hb64 : σ "b" < 2 ^ 64 := lt_trans hb (by norm_num)
  -- `a ≪ 8 = a * 256 < 2^40` from `a < 2^32`
  have hshl40 : σ "a" <<< 8 < 2 ^ 40 := by
    rw [Nat.shiftLeft_eq]
    calc σ "a" * 2 ^ 8 < 2 ^ 32 * 2 ^ 8 := by gcongr
      _ = 2 ^ 40 := by norm_num
  have hshl64 : σ "a" <<< 8 < 2 ^ 64 := lt_trans hshl40 (by norm_num)
  -- `a ≫ 56 ≤ a < 2^32 < 2^40`
  have hshr40 : σ "a" >>> 56 < 2 ^ 40 :=
    lt_of_le_of_lt (Nat.shiftRight_le _ _) (lt_trans ha (by norm_num))
  -- the xor of two `< 2^40` values is `< 2^40`
  have hxor40 : (σ "a" <<< 8) ^^^ (σ "a" >>> 56) < 2 ^ 40 :=
    Nat.xor_lt_two_pow hshl40 hshr40
  -- the modular-add sum stays in `u64`: `< 2^40 + 2^32 < 2^64`
  have hsum : SExpr.eval σ (.SXor (.SShl (.SVar "a") (.SLit 8)) (.SShr (.SVar "a") (.SLit 56)))
      + SExpr.eval σ (.SVar "b") < 2 ^ 64 := by
    simp only [SExpr.eval]
    omega
  exact ⟨⟨⟨ha64, by norm_num [SExpr.inRange], by simp only [SExpr.eval]; decide, hshl64⟩,
      ⟨ha64, by norm_num [SExpr.inRange], by simp only [SExpr.eval]; decide⟩⟩, hb64, hsum⟩

/-- **The ARX reconciliation (symbolic leg).** For every input satisfying the
    per-kernel bound, the wrapping-`u64` evaluator agrees with the `ofNat` image
    of the saturating-`Nat` evaluator — i.e. no wrap occurs on the ARX round core
    within the lane discipline. Wraps `SExpr.evalBV_eq_ofNat_eval` (`= sexprTransfer`)
    with the ARX `inRange` discharge. -/
theorem arxE_reconcile (σ : String → Nat) (h : arxBound σ) :
    arxE.evalBV (SExpr.liftEnv σ) = BitVec.ofNat 64 (arxE.eval σ) :=
  sexprTransfer σ arxE (arxE_inRange_of_bound σ h)

/-! ## The `RustExec` reference run -/

def rs0 : RustState := default
def rs1 : RustState := rsSetScalar rs0 "a" 305419896
def rs2 : RustState := rsSetScalar rs1 "b" 286331153
def rsF : RustState := rsSetScalar rs2 "s" (arxE.eval rs2.rsScalar)

/-- The kernel's inputs satisfy the per-kernel lane bound (the concrete instance
    of `arxBound` under which `arxE_reconcile` fires for this kernel). -/
theorem rs2_arxBound : arxBound rs2.rsScalar := by
  constructor <;> · simp only [rs2, rs1, rs0, rsSetScalar]; decide

theorem arxC_exec (N : Nat) (leafSpec : LeafSpec) : RustExec N leafSpec arxC rs0 rsF :=
  .seq _ _ rs0 rs1 rsF (.scalarSet "a" 305419896 rs0)
    (.seq _ _ rs1 rs2 rsF (.scalarSet "b" 286331153 rs1)
      (.scalarSetExpr "s" arxE rs2))

/-! ## Front translation, semantics, output tracking — all by `.get`/`rfl` -/

theorem arxTransSome : (translateDialectControl VarMap.empty arxC).isSome := by rfl

noncomputable def arxO : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty arxC).get arxTransSome

theorem arxHTrans : translateDialectControl VarMap.empty arxC = some arxO :=
  (Option.some_get arxTransSome).symm

theorem arxSemSome : (semScalar arxC (fun _ => none)).isSome := by rfl

noncomputable def arxEnv : SEnvScalar := (semScalar arxC (fun _ => none)).get arxSemSome

theorem arxHSem : semScalar arxC (fun _ => none) = some arxEnv :=
  (Option.some_get arxSemSome).symm

theorem arxNameSome : (arxO.vm.lookup "s").isSome := by rfl

noncomputable def arxW : CVar arxO.Γ' (.sword 64) :=
  ((arxO.vm.lookup "s").get arxNameSome).2

theorem arxHName : arxO.vm.lookup "s" = some ⟨.sword 64, arxW⟩ := by rfl

theorem arxValSome : (arxEnv "s").isSome := by rfl

noncomputable def arxVal : BitVec 64 := ((arxEnv "s").get arxValSome).2

theorem arxHVal : arxEnv "s" = some ⟨.sword 64, arxVal⟩ := by rfl

theorem arxRetSome : (arxO.cont (Com.ret (toVIRVar arxW))).isSome := by rfl

noncomputable def arxCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (arxO.cont (Com.ret (toVIRVar arxW))).get arxRetSome

theorem arxHRet : arxO.cont (Com.ret (toVIRVar arxW)) = some arxCom :=
  (Option.some_get arxRetSome).symm

theorem arxComSome : (cryptoDialectToJasminCom arxCom).isSome := by rfl

noncomputable def arxJcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom arxCom).get arxComSome

theorem arxHCom : cryptoDialectToJasminCom arxCom = some arxJcom :=
  (Option.some_get arxComSome).symm

/-- **The `#250` reconciliation, concrete leg.** The word `semScalar` leaves in
    `s` — computed by the wrapping-`u64` evaluator through the rotate and the
    modular add — is the `ofNat 64` image of the `RustExec` saturating-`Nat`
    reference output `rsF.rsScalar "s"`. Both sides are concrete words on the
    kernel's literal inputs, on which no shift/add overflows `u64`; equality by
    `decide`. This is `arxE_reconcile` specialised to the kernel's inputs, carried
    out by concrete evaluation. -/
theorem arxVal_eq_ref : arxVal = BitVec.ofNat 64 (rsF.rsScalar "s") := by decide

/-! ## `emitted ARX round = RustExec reference` -/

/-- **The real ARX round: `emitted jasmin = RustExec reference output`.** The
    verified pipeline's emitted jasmin program for the ARX round-core kernel
    (`s := rotl64(a,8) ⊕-form + b`, one rotate + one modular add) denotes to the
    `ctTransTy` image of the `RustExec` reference output word `rsF.rsScalar "s"`.
    Obtained through the SATISFIABLE closed-kernel route
    `rustToJasminCom_endToEnd_topLevel_unconditional`: the kernel is closed, so
    `semScalar` succeeds from the empty entry env and no entry `EnvRel` seam is
    needed; the ARX `#250` value reconciliation is discharged concretely
    (`arxVal_eq_ref`) under the kernel's u32/u64 input discipline. Axiom-free. -/
theorem arxC_emitted_eq_rustexec (N : Nat) (leafSpec : LeafSpec) :
    (∃ Vb' : HVec arxO.Γ', RustStateInterp arxO.vm rsF Vb')
      ∧ arxJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (rsF.rsScalar "s")) := by
  have h := rustToJasminCom_endToEnd_topLevel_unconditional arxC arxO N leafSpec rs0 rsF
    arxEnv "s" arxW arxVal arxCom arxJcom arxC_covered arxHTrans
    (arxC_exec N leafSpec) arxHSem arxHName arxHVal arxHRet arxHCom
  rwa [arxVal_eq_ref] at h

end CatCrypt.Crypto.SecureCompilation.Dialects.RustExecARXAdeq
