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
import all CatCrypt.Crypto.Jasmin.LowCTExec
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

/-!
# Keccak-f[1600] bitwise lane steps through the closed-kernel `emitted = RustExec` route

`RustExecRoundAdeq.roundC_emitted_eq_rustexec` proves `emitted jasmin = RustExec
reference` for the bitwise layer of a SHA-2 round (`Maj`) through the closed-kernel
route `rustToJasminCom_endToEnd_topLevel_unconditional`. This module applies the
same route to the two bitwise steps of Keccak-f[1600] at the `u64`-lane level:

* `chiC` (§1): one chi lane `A = b0 ⊕ b2 ⊕ (b1 ∧ b2)`, the rewriting of
  `A[x] ⊕ ((¬A[x+1]) ∧ A[x+2])` by `(¬b) ∧ c = c ⊕ (b ∧ c)`. Its `inRange`
  obligation holds for every `u64` input, so it lies in `IsCoveredAdeq`.
* `iotaC` (§2): the iota step `A = a ⊕ RC` with the round constant `RC[1]`, also
  in `IsCoveredAdeq`.

On bitwise operations `RustExec` (unbounded naturals) and `semScalar` (wrapping
`BitVec 64`) agree on all `u64` inputs, so `RustExec` is a valid referent here.

The rotate steps theta and rho (`rotl64`, written `(v ≪ k) ⊕ (v ≫ (64 - k))`) are
not covered. `RustExec` evaluates `SShl` over unbounded naturals, so on a lane
`v ≥ 2^(64-k)` its value is not the rotation; the referent for a rotate over full
64-bit lanes is `semScalar`. The pi step is a renaming of lanes and contains no
scalar expression.

The theorems concern closed kernels. The open-kernel jasmin leg meets
`RustExecKernelAdeq.entry_trio_unsat_empty` (the `EnvRel`/`ConsistentS`/`NoAliasVM`
clash at any finite entry) and is outside this module.
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
obligation is the hoisted all-`u64` one with no side condition. Lies in
`IsCoveredAdeq`. The inputs are `u64` lane words. -/

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

/-! ## §2 — The iota step `A = a ⊕ RC` (bitwise, axiom-free)

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
