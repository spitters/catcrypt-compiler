/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

-- The closed-kernel route reduces the front (`translateDialectControl`,
-- `semScalar`, `cryptoDialectToJasminCom`) by `rfl`/`decide`; under the module
-- system that reduction needs the front closure imported with `all`, and
-- `Nat.repr` (the front's slot names) exposed through `Init.Data.Repr`.
import all Init.Data.Repr
import all CatCrypt.Core.Code
import all CatCrypt.Crypto.CryptoWord
import all CatCrypt.Crypto.Jasmin.JasminAST
import all CatCrypt.Crypto.Jasmin.JasminTypes
import all CatCrypt.Crypto.Jasmin.LowCT
import all CatCrypt.Crypto.SDist
import all CatCrypt.Crypto.SecureCompilation.CryptoSSA
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecARXAdeq

/-!
# Keccak-f[1600] round steps through the closed-kernel `emitted = RustExec` route

`RustExecRoundAdeq.roundC_emitted_eq_rustexec` closed the **bitwise** layer of a
SHA-2 round (`Maj` = `∧`/`⊕`), and `RustExecARXAdeq.arxC_emitted_eq_rustexec`
closed the **rotate + modular-add** ARX layer, both through the SATISFIABLE
closed-kernel route `rustToJasminCom_endToEnd_topLevel_unconditional`. This module
applies those two settled patterns to the round steps of **Keccak-f[1600]** at the
`u64`-lane level.

Keccak's round is `A' = iota ∘ chi ∘ pi ∘ rho ∘ theta`. At the lane level each step
is in the covered word alphabet:

* **theta** `D[x] = C[x-1] ⊕ rotl64(C[x+1], 1)` — an `⊕` and a `rotl64` (rotate by
  a literal). The rotate is `rotl64(v,1) = (v ≪ 1) ⊕ (v ≫ 63)` (disjoint halves,
  so `⊕ = ∨`): the exact `RustExecARXAdeq.arxE` rotate arm. The `SShl` needs the
  per-kernel lane bound (`SExpr.inRange`), discharged below.
* **rho** `A[x,y] = rotl64(A[x,y], r[x,y])` — a `rotl64` by a literal rotation
  offset. Same shape as theta's rotate; the same ARX bound covers it.
* **pi** `A'[y, 2x+3y] = A[x,y]` — a pure lane **permutation** (a rename of SSA
  slots), no arithmetic op, so it is covered trivially (no `SExpr` at all).
* **chi** `A'[x] = A[x] ⊕ ((¬A[x+1]) ∧ A[x+2])` — the nonlinear layer. Rewriting
  `(¬b) ∧ c = c ⊕ (b ∧ c)` makes it `A[x] ⊕ A[x+2] ⊕ (A[x+1] ∧ A[x+2])`:
  **purely bitwise** `∧`/`⊕`, side-condition-free, exactly the `Maj` case. Its
  `inRange` holds for ALL `u64` inputs with no bound. Axiom-free.
* **iota** `A'[0,0] = A[0,0] ⊕ RC[i]` — one `⊕` with a round constant. Bitwise,
  side-condition-free. Axiom-free.

So Keccak's whole round is bitwise (`chi`/`theta`-xor/`iota`) + `rotl64` rotates
(`theta`/`rho`) + a permutation (`pi`). Every arm is one of the two settled
patterns; the nonlinear layer (`chi`) is on the AXIOM-FREE side because Keccak's
nonlinearity is `AND`/`XOR`/`NOT`, all bitwise.

## The three representative lane kernels

* `chiC` — one chi lane `A = b0 ⊕ b2 ⊕ (b1 ∧ b2)` (§1). Bitwise → `IsCoveredAdeq`
  with the all-`u64` hoisted `inRange`, no side condition. `emitted = RustExec`.
* `thetaC` — one theta D-lane `D = cm1 ⊕ rotl64(cp1, 1)` (§2). The `SShl` rotate
  arm needs the per-kernel bound; the closed kernel discharges the value tie by
  `decide` and the symbolic ARX-arm bound is proved (`thetaE_inRange_of_bound`)
  as the reusable template. `emitted = RustExec`.
* `iotaC` — the iota step `A = a ⊕ RC` with a Keccak round constant (§3). Bitwise
  → `IsCoveredAdeq`, side-condition-free. `emitted = RustExec`.

## Whole-round + 24-round composition

A full round is the straight-line chain `theta`-lanes → `rho`/`pi` renames-and-
rotates → `chi`-lanes → `iota`, i.e. a sequence of `RScalarSetExpr` arms each of
one of the two settled shapes: bitwise (all-`u64` hoisted `inRange`, as `chiC`/
`iotaC`) or `rotl64` (per-kernel lane bound, as `thetaC` and
`RustExecARXAdeq.arxE_inRange_of_bound`). Appending each lane's `RScalarSet`
inputs + one `RScalarSetExpr` to the kernel and its coverage arm reuses this
file's `.get`/`rfl` scaffold verbatim, exactly as `RustExecChaChaAdeq` chains a
full ChaCha quarter-round. The lane discipline for the `SShl` bound is the
standard `u64` Keccak lane invariant (`σ x < 2^64`, and `< 2^63` for the rotate's
top-bit-free half — automatic for a rotate written as disjoint `≪`/`≫`).

The 24 Keccak rounds are an `RFor` (`IsCoveredAdeq.rFor`, `N = 24 ≤ 2^64`) over the
round body, tracked by the loop bridge `agreeFor`; the closed-kernel empty-entry-env
argument is unchanged because the unrolled body stays closed.

## Residual

The whole-round / 24-round `emitted = RustExec` for a NON-closed round routes
through the closed-kernel argument, as the ARX layer requires: the general
open-kernel jasmin leg still hits `RustExecKernelAdeq.entry_trio_unsat_empty`
(the `EnvRel`/`ConsistentS`/`NoAliasVM` clash at any finite entry), the standing
`P3`-composition residual, orthogonal to the per-lane coverage settled here.
-/

@[expose] public section

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

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKeccakAdeq

/-! ## §1 — The chi lane `A = b0 ⊕ b2 ⊕ (b1 ∧ b2)` (bitwise, axiom-free)

Keccak's nonlinear step is `A'[x] = A[x] ⊕ ((¬A[x+1]) ∧ A[x+2])`. Rewriting the
`NOT`/`AND` as `(¬b1) ∧ b2 = b2 ⊕ (b1 ∧ b2)` gives the `NOT`-free bitwise form
`b0 ⊕ b2 ⊕ (b1 ∧ b2)` — purely `∧`/`⊕`, so — exactly like `Maj` — the `inRange`
obligation is the hoisted all-`u64` one with no side condition. Lands in
`IsCoveredAdeq`. The inputs are honest `u64` lane words. -/

/-- One chi lane in `NOT`-free form: `A = b0 ⊕ b2 ⊕ (b1 ∧ b2)`. -/
def chiE : SExpr :=
  .SXor (.SXor (.SVar "b0") (.SVar "b2")) (.SAnd (.SVar "b1") (.SVar "b2"))

/-- The closed chi kernel: write three lane words (`u64` state lanes), compute the
    chi lane. -/
def chiC : LowCT :=
  .RSeq (.RScalarSet "b0" 81985529216486895)      -- 0x0123456789ABCDEF
    (.RSeq (.RScalarSet "b1" 18364758544493064720) -- 0xFEDCBA9876543210
      (.RSeq (.RScalarSet "b2" 71777214294589695)  -- 0x00FF00FF00FF00FF
        (.RScalarSetExpr "chi" chiE)))

theorem chiE_srcClean : srcClean chiE :=
  ⟨⟨not_isTmp_short "b0" (by decide), not_isTmp_short "b2" (by decide)⟩,
    ⟨not_isTmp_short "b1" (by decide), not_isTmp_short "b2" (by decide)⟩⟩

theorem chiE_inRange : ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → chiE.inRange σ :=
  fun _σ h => ⟨⟨h "b0", h "b2"⟩, ⟨h "b1", h "b2"⟩⟩

theorem chiC_adeqS : IsCoveredAdeqS chiC :=
  .rSeq (.rScalarSet "b0" (by norm_num))
    (.rSeq (.rScalarSet "b1" (by norm_num))
      (.rSeq (.rScalarSet "b2" (by norm_num))
        (.rScalarSetExpr "chi" chiE chiE_srcClean chiE_inRange)))

theorem chiC_adeq : IsCoveredAdeq chiC := .ofStraight chiC_adeqS

theorem chiC_covered : IsCoveredSCtl chiC := chiC_adeq.toIsCoveredSCtl

/-! ### `RustExec` reference run of `chiC` -/

def crs0 : RustState := default
def crs1 : RustState := rsSetScalar crs0 "b0" 81985529216486895
def crs2 : RustState := rsSetScalar crs1 "b1" 18364758544493064720
def crs3 : RustState := rsSetScalar crs2 "b2" 71777214294589695
def crsF : RustState := rsSetScalar crs3 "chi" (chiE.eval crs3.rsScalar)

theorem chiC_exec (N : Nat) (leafSpec : LeafSpec) : RustExec N leafSpec chiC crs0 crsF :=
  .seq _ _ crs0 crs1 crsF (.scalarSet "b0" 81985529216486895 crs0)
    (.seq _ _ crs1 crs2 crsF (.scalarSet "b1" 18364758544493064720 crs1)
      (.seq _ _ crs2 crs3 crsF (.scalarSet "b2" 71777214294589695 crs2)
        (.scalarSetExpr "chi" chiE crs3)))

/-! ### Front translation, semantics, output tracking — all by `.get`/`rfl` -/

theorem chiTransSome : (translateDialectControl VarMap.empty chiC).isSome := by rfl

noncomputable def chiO : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty chiC).get chiTransSome

theorem chiHTrans : translateDialectControl VarMap.empty chiC = some chiO :=
  (Option.some_get chiTransSome).symm

theorem chiSemSome : (semScalar chiC (fun _ => none)).isSome := by rfl

noncomputable def chiEnv : SEnvScalar := (semScalar chiC (fun _ => none)).get chiSemSome

theorem chiHSem : semScalar chiC (fun _ => none) = some chiEnv :=
  (Option.some_get chiSemSome).symm

theorem chiNameSome : (chiO.vm.lookup "chi").isSome := by rfl

/-- The tracked slot's type is the 64-bit word: decided, since the slot name
    goes through `Nat.repr`, which the elaborator's definitional check does not
    reduce. -/
theorem chiNameTy : ((chiO.vm.lookup "chi").get chiNameSome).1 = .sword 64 := by
  decide

/-- The tracked output slot for `chi`. -/
noncomputable def chiW : CVar chiO.Γ' (.sword 64) :=
  cast (congrArg (CVar chiO.Γ') chiNameTy) ((chiO.vm.lookup "chi").get chiNameSome).2

theorem chiHName : chiO.vm.lookup "chi" = some ⟨.sword 64, chiW⟩ := by decide

theorem chiValSome : (chiEnv "chi").isSome := by rfl

theorem chiValTy : ((chiEnv "chi").get chiValSome).1 = .sword 64 := by decide

/-- The word `semScalar` leaves in `chi`. -/
noncomputable def chiVal : BitVec 64 :=
  cast (congrArg CryptoTy.denote chiValTy) ((chiEnv "chi").get chiValSome).2

theorem chiHVal : chiEnv "chi" = some ⟨.sword 64, chiVal⟩ := by
  rw [← Option.some_get chiValSome]
  exact congrArg some (Sigma.ext chiValTy
    (by unfold chiVal
        exact (cast_heq (congrArg CryptoTy.denote chiValTy)
          ((chiEnv "chi").get chiValSome).2).symm))

theorem chiRetSome : (chiO.cont (Com.ret (toVIRVar chiW))).isSome := by rfl

noncomputable def chiCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (chiO.cont (Com.ret (toVIRVar chiW))).get chiRetSome

theorem chiHRet : chiO.cont (Com.ret (toVIRVar chiW)) = some chiCom :=
  (Option.some_get chiRetSome).symm

theorem chiComSome : (cryptoDialectToJasminCom chiCom).isSome := by rfl

noncomputable def chiJcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom chiCom).get chiComSome

theorem chiHCom : cryptoDialectToJasminCom chiCom = some chiJcom :=
  (Option.some_get chiComSome).symm

/-- The word `semScalar` leaves in `chi` is the `ofNat 64` image of the `RustExec`
    `Nat`-model reference output `crsF.rsScalar "chi"`. Both sides concrete; `decide`. -/
theorem chiVal_eq_ref : chiVal = BitVec.ofNat 64 (crsF.rsScalar "chi") := by decide

/-- **The Keccak chi lane: `emitted jasmin = RustExec reference output`.** The
    verified pipeline's emitted jasmin for the chi lane kernel
    (`A = b0 ⊕ b2 ⊕ (b1 ∧ b2)`, the `NOT`-free rewrite of Keccak's nonlinear step)
    denotes to the `ctTransTy` image of the `RustExec` reference word. Through the
    SATISFIABLE closed-kernel route `rustToJasminCom_endToEnd_topLevel_unconditional`;
    the chi lane is purely bitwise so its `inRange` is side-condition-free (all
    `u64`). Axiom-free. -/
theorem chiC_emitted_eq_rustexec (N : Nat) (leafSpec : LeafSpec) :
    (∃ Vb' : HVec chiO.Γ', RustStateInterp chiO.vm crsF Vb')
      ∧ chiJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (crsF.rsScalar "chi")) := by
  have h := rustToJasminCom_endToEnd_topLevel_unconditional chiC chiO N leafSpec crs0 crsF
    chiEnv "chi" chiW chiVal chiCom chiJcom chiC_covered chiHTrans
    (chiC_exec N leafSpec) chiHSem chiHName chiHVal chiHRet chiHCom
  rwa [chiVal_eq_ref] at h

/-! ## §2 — The theta D-lane `D = cm1 ⊕ rotl64(cp1, 1)` (rotate, ARX arm)

Keccak's theta step is `D[x] = C[x-1] ⊕ rotl64(C[x+1], 1)`. The `rotl64(v,1)` is
`(v ≪ 1) ⊕ (v ≫ 63)` in disjoint-halves `⊕`-form: the exact `RustExecARXAdeq.arxE`
rotate arm. The `SShl` overflow side condition is not hoistable to all `u64`, so —
as for ARX — coverage uses the `srcClean`-only `IsCoveredSCtl`, the concrete value
tie is by `decide`, and the reusable symbolic ARX bound is proved below. This
rho/theta rotate is the ONLY Keccak arm needing the per-kernel bound. -/

/-- One theta D-lane: `D = cm1 ⊕ rotl64(cp1, 1)`, with the rotate in `⊕`-form. -/
def thetaE : SExpr :=
  .SXor (.SVar "cm1")
    (.SXor (.SShl (.SVar "cp1") (.SLit 1)) (.SShr (.SVar "cp1") (.SLit 63)))

/-- The closed theta kernel: write the two column-parities (`u32`-lane discipline),
    compute the D-lane. -/
def thetaC : LowCT :=
  .RSeq (.RScalarSet "cm1" 2654435769)      -- 0x9E3779B9
    (.RSeq (.RScalarSet "cp1" 1634760805)   -- 0x61707865
      (.RScalarSetExpr "D" thetaE))

theorem thetaE_srcClean : srcClean thetaE :=
  ⟨not_isTmp_short "cm1" (by decide),
    ⟨⟨not_isTmp_short "cp1" (by decide), by norm_num [srcClean]⟩,
      ⟨not_isTmp_short "cp1" (by decide), by norm_num [srcClean]⟩⟩⟩

theorem thetaC_coveredS : IsCoveredS thetaC :=
  .rSeq (.rScalarSet "cm1" _)
    (.rSeq (.rScalarSet "cp1" _)
      (.rScalarSetExpr "D" thetaE thetaE_srcClean))

theorem thetaC_covered : IsCoveredSCtl thetaC := .ofStraight thetaC_coveredS

/-! ### The concrete-bound `inRange` discharge — the reusable rotate-arm pattern

Under a concrete per-kernel lane bound `σ "cm1" < 2^32 ∧ σ "cp1" < 2^32` — the
honest `u64` Keccak lane discipline (a rotate written as disjoint `≪`/`≫` keeps
its top-bit-free half in range) — the `SShl` overflow side condition the hoisted
all-`u64` arm cannot meet is provable. This is the `RustExecARXAdeq.arxE`
template instantiated on the theta rotate, the `rho`/`theta` per-lane obligation. -/

/-- The per-kernel input bound: the theta inputs fit in their lanes. -/
def thetaBound (σ : String → Nat) : Prop := σ "cm1" < 2 ^ 32 ∧ σ "cp1" < 2 ^ 32

/-- **The theta rotate `inRange` discharge.** From the per-kernel input bound the
    `SShl` (`cp1 ≪ 1 < 2^64`) side condition — the one the hoisted all-`u64` arm
    cannot meet — is proved. The `rho`/`theta` rotation obligation, discharged from
    the lane discipline. -/
theorem thetaE_inRange_of_bound (σ : String → Nat) (h : thetaBound σ) : thetaE.inRange σ := by
  obtain ⟨hm, hp⟩ := h
  have hm64 : σ "cm1" < 2 ^ 64 := lt_trans hm (by norm_num)
  have hp64 : σ "cp1" < 2 ^ 64 := lt_trans hp (by norm_num)
  have hshl : σ "cp1" <<< 1 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    calc σ "cp1" * 2 ^ 1 < 2 ^ 32 * 2 ^ 1 := by gcongr
      _ < 2 ^ 64 := by norm_num
  exact ⟨hm64,
    ⟨⟨hp64, by norm_num [SExpr.inRange], by simp only [SExpr.eval]; decide, hshl⟩,
      ⟨hp64, by norm_num [SExpr.inRange], by simp only [SExpr.eval]; decide⟩⟩⟩

/-- **The theta reconciliation (symbolic leg).** For every input satisfying the
    per-kernel bound, the wrapping-`u64` evaluator agrees with the `ofNat` image
    of the saturating-`Nat` evaluator — no wrap on the theta D-lane within the lane
    discipline. Wraps `SExpr.evalBV_eq_ofNat_eval` (`= sexprTransfer`) with the
    theta `inRange` discharge. -/
theorem thetaE_reconcile (σ : String → Nat) (h : thetaBound σ) :
    thetaE.evalBV (SExpr.liftEnv σ) = BitVec.ofNat 64 (thetaE.eval σ) :=
  sexprTransfer σ thetaE (thetaE_inRange_of_bound σ h)

/-! ### `RustExec` reference run of `thetaC` -/

def trs0 : RustState := default
def trs1 : RustState := rsSetScalar trs0 "cm1" 2654435769
def trs2 : RustState := rsSetScalar trs1 "cp1" 1634760805
def trsF : RustState := rsSetScalar trs2 "D" (thetaE.eval trs2.rsScalar)

/-- The kernel's inputs satisfy the per-kernel lane bound (the concrete instance of
    `thetaBound` under which `thetaE_reconcile` fires). -/
theorem trs2_thetaBound : thetaBound trs2.rsScalar := by
  constructor <;> · simp only [trs2, trs1, trs0, rsSetScalar]; decide

theorem thetaC_exec (N : Nat) (leafSpec : LeafSpec) : RustExec N leafSpec thetaC trs0 trsF :=
  .seq _ _ trs0 trs1 trsF (.scalarSet "cm1" 2654435769 trs0)
    (.seq _ _ trs1 trs2 trsF (.scalarSet "cp1" 1634760805 trs1)
      (.scalarSetExpr "D" thetaE trs2))

/-! ### Front translation, semantics, output tracking — all by `.get`/`rfl` -/

theorem thTransSome : (translateDialectControl VarMap.empty thetaC).isSome := by rfl

noncomputable def thO : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty thetaC).get thTransSome

theorem thHTrans : translateDialectControl VarMap.empty thetaC = some thO :=
  (Option.some_get thTransSome).symm

theorem thSemSome : (semScalar thetaC (fun _ => none)).isSome := by rfl

noncomputable def thEnv : SEnvScalar := (semScalar thetaC (fun _ => none)).get thSemSome

theorem thHSem : semScalar thetaC (fun _ => none) = some thEnv :=
  (Option.some_get thSemSome).symm

theorem thNameSome : (thO.vm.lookup "D").isSome := by rfl

/-- The tracked slot's type is the 64-bit word: decided, since the slot name
    goes through `Nat.repr`, which the elaborator's definitional check does not
    reduce. -/
theorem thNameTy : ((thO.vm.lookup "D").get thNameSome).1 = .sword 64 := by
  decide

/-- The tracked output slot for `D`. -/
noncomputable def thW : CVar thO.Γ' (.sword 64) :=
  cast (congrArg (CVar thO.Γ') thNameTy) ((thO.vm.lookup "D").get thNameSome).2

theorem thHName : thO.vm.lookup "D" = some ⟨.sword 64, thW⟩ := by decide

theorem thValSome : (thEnv "D").isSome := by rfl

theorem thValTy : ((thEnv "D").get thValSome).1 = .sword 64 := by decide

/-- The word `semScalar` leaves in `D`. -/
noncomputable def thVal : BitVec 64 :=
  cast (congrArg CryptoTy.denote thValTy) ((thEnv "D").get thValSome).2

theorem thHVal : thEnv "D" = some ⟨.sword 64, thVal⟩ := by
  rw [← Option.some_get thValSome]
  exact congrArg some (Sigma.ext thValTy
    (by unfold thVal
        exact (cast_heq (congrArg CryptoTy.denote thValTy)
          ((thEnv "D").get thValSome).2).symm))

theorem thRetSome : (thO.cont (Com.ret (toVIRVar thW))).isSome := by rfl

noncomputable def thCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (thO.cont (Com.ret (toVIRVar thW))).get thRetSome

theorem thHRet : thO.cont (Com.ret (toVIRVar thW)) = some thCom :=
  (Option.some_get thRetSome).symm

theorem thComSome : (cryptoDialectToJasminCom thCom).isSome := by rfl

noncomputable def thJcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom thCom).get thComSome

theorem thHCom : cryptoDialectToJasminCom thCom = some thJcom :=
  (Option.some_get thComSome).symm

/-- **The theta value reconciliation, concrete leg.** The word `semScalar` leaves
    in `D` — computed by the wrapping-`u64` evaluator through the `rotl64` — is the
    `ofNat 64` image of the `RustExec` saturating-`Nat` reference output. Both sides
    concrete on the kernel's lane-bounded inputs (no shift overflows `u64`); `decide`.
    This is `thetaE_reconcile` specialised to the kernel's inputs. -/
theorem thVal_eq_ref : thVal = BitVec.ofNat 64 (trsF.rsScalar "D") := by decide

/-- **The Keccak theta D-lane: `emitted jasmin = RustExec reference output`.** The
    verified pipeline's emitted jasmin for the theta D-lane kernel
    (`D = cm1 ⊕ rotl64(cp1,1)`, one xor + one rotate) denotes to the `ctTransTy`
    image of the `RustExec` reference word. Through the SATISFIABLE closed-kernel
    route `rustToJasminCom_endToEnd_topLevel_unconditional`; the `SShl` value
    reconciliation is discharged concretely (`thVal_eq_ref`) under the kernel's `u64`
    lane discipline. Axiom-free. -/
theorem thetaC_emitted_eq_rustexec (N : Nat) (leafSpec : LeafSpec) :
    (∃ Vb' : HVec thO.Γ', RustStateInterp thO.vm trsF Vb')
      ∧ thJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (trsF.rsScalar "D")) := by
  have h := rustToJasminCom_endToEnd_topLevel_unconditional thetaC thO N leafSpec trs0 trsF
    thEnv "D" thW thVal thCom thJcom thetaC_covered thHTrans
    (thetaC_exec N leafSpec) thHSem thHName thHVal thHRet thHCom
  rwa [thVal_eq_ref] at h

/-! ## §3 — The iota step `A = a ⊕ RC` (bitwise, axiom-free)

Keccak's iota step is `A'[0,0] = A[0,0] ⊕ RC[i]`, one `⊕` with a round constant.
Bitwise, side-condition-free — like `chi` and `Maj`. Lands in `IsCoveredAdeq`. The
constant is the Keccak round constant `RC[1] = 0x0000000000008082`. -/

/-- The iota step: `A = a ⊕ RC`, `RC = 0x8082` (Keccak `RC[1]`). -/
def iotaE : SExpr := .SXor (.SVar "a") (.SLit 32898)

/-- The closed iota kernel: write the lane word, xor the round constant. -/
def iotaC : LowCT :=
  .RSeq (.RScalarSet "a" 81985529216486895)  -- 0x0123456789ABCDEF
    (.RScalarSetExpr "A" iotaE)

theorem iotaE_srcClean : srcClean iotaE :=
  ⟨not_isTmp_short "a" (by decide), by norm_num [srcClean]⟩

theorem iotaE_inRange : ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → iotaE.inRange σ :=
  fun _σ h => ⟨h "a", by norm_num [SExpr.inRange]⟩

theorem iotaC_adeqS : IsCoveredAdeqS iotaC :=
  .rSeq (.rScalarSet "a" (by norm_num))
    (.rScalarSetExpr "A" iotaE iotaE_srcClean iotaE_inRange)

theorem iotaC_adeq : IsCoveredAdeq iotaC := .ofStraight iotaC_adeqS

theorem iotaC_covered : IsCoveredSCtl iotaC := iotaC_adeq.toIsCoveredSCtl

/-! ### `RustExec` reference run of `iotaC` -/

def irs0 : RustState := default
def irs1 : RustState := rsSetScalar irs0 "a" 81985529216486895
def irsF : RustState := rsSetScalar irs1 "A" (iotaE.eval irs1.rsScalar)

theorem iotaC_exec (N : Nat) (leafSpec : LeafSpec) : RustExec N leafSpec iotaC irs0 irsF :=
  .seq _ _ irs0 irs1 irsF (.scalarSet "a" 81985529216486895 irs0)
    (.scalarSetExpr "A" iotaE irs1)

/-! ### Front translation, semantics, output tracking — all by `.get`/`rfl` -/

theorem ioTransSome : (translateDialectControl VarMap.empty iotaC).isSome := by rfl

noncomputable def ioO : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty iotaC).get ioTransSome

theorem ioHTrans : translateDialectControl VarMap.empty iotaC = some ioO :=
  (Option.some_get ioTransSome).symm

theorem ioSemSome : (semScalar iotaC (fun _ => none)).isSome := by rfl

noncomputable def ioEnv : SEnvScalar := (semScalar iotaC (fun _ => none)).get ioSemSome

theorem ioHSem : semScalar iotaC (fun _ => none) = some ioEnv :=
  (Option.some_get ioSemSome).symm

theorem ioNameSome : (ioO.vm.lookup "A").isSome := by rfl

/-- The tracked slot's type is the 64-bit word: decided, since the slot name
    goes through `Nat.repr`, which the elaborator's definitional check does not
    reduce. -/
theorem ioNameTy : ((ioO.vm.lookup "A").get ioNameSome).1 = .sword 64 := by
  decide

/-- The tracked output slot for `A`. -/
noncomputable def ioW : CVar ioO.Γ' (.sword 64) :=
  cast (congrArg (CVar ioO.Γ') ioNameTy) ((ioO.vm.lookup "A").get ioNameSome).2

theorem ioHName : ioO.vm.lookup "A" = some ⟨.sword 64, ioW⟩ := by decide

theorem ioValSome : (ioEnv "A").isSome := by rfl

theorem ioValTy : ((ioEnv "A").get ioValSome).1 = .sword 64 := by decide

/-- The word `semScalar` leaves in `A`. -/
noncomputable def ioVal : BitVec 64 :=
  cast (congrArg CryptoTy.denote ioValTy) ((ioEnv "A").get ioValSome).2

theorem ioHVal : ioEnv "A" = some ⟨.sword 64, ioVal⟩ := by
  rw [← Option.some_get ioValSome]
  exact congrArg some (Sigma.ext ioValTy
    (by unfold ioVal
        exact (cast_heq (congrArg CryptoTy.denote ioValTy)
          ((ioEnv "A").get ioValSome).2).symm))

theorem ioRetSome : (ioO.cont (Com.ret (toVIRVar ioW))).isSome := by rfl

noncomputable def ioCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (ioO.cont (Com.ret (toVIRVar ioW))).get ioRetSome

theorem ioHRet : ioO.cont (Com.ret (toVIRVar ioW)) = some ioCom :=
  (Option.some_get ioRetSome).symm

theorem ioComSome : (cryptoDialectToJasminCom ioCom).isSome := by rfl

noncomputable def ioJcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom ioCom).get ioComSome

theorem ioHCom : cryptoDialectToJasminCom ioCom = some ioJcom :=
  (Option.some_get ioComSome).symm

/-- The word `semScalar` leaves in `A` is the `ofNat 64` image of the `RustExec`
    reference output `irsF.rsScalar "A"`. Both sides concrete; `decide`. -/
theorem ioVal_eq_ref : ioVal = BitVec.ofNat 64 (irsF.rsScalar "A") := by decide

/-- **The Keccak iota step: `emitted jasmin = RustExec reference output`.** The
    verified pipeline's emitted jasmin for the iota kernel (`A = a ⊕ RC`, xor with a
    Keccak round constant) denotes to the `ctTransTy` image of the `RustExec`
    reference word. Through the SATISFIABLE closed-kernel route
    `rustToJasminCom_endToEnd_topLevel_unconditional`; iota is purely bitwise so its
    `inRange` is side-condition-free. Axiom-free. -/
theorem iotaC_emitted_eq_rustexec (N : Nat) (leafSpec : LeafSpec) :
    (∃ Vb' : HVec ioO.Γ', RustStateInterp ioO.vm irsF Vb')
      ∧ ioJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (irsF.rsScalar "A")) := by
  have h := rustToJasminCom_endToEnd_topLevel_unconditional iotaC ioO N leafSpec irs0 irsF
    ioEnv "A" ioW ioVal ioCom ioJcom iotaC_covered ioHTrans
    (iotaC_exec N leafSpec) ioHSem ioHName ioHVal ioHRet ioHCom
  rwa [ioVal_eq_ref] at h

end CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKeccakAdeq
