/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpLsemTie
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpArrMemN
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTrip
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond

/-!
# The emitted `mpn_cmp` loop is an array-carrier fragment member, unconditionally

`MpnCmpLsemTie.cmp_emitted_machine_val` composes the array-accumulator
backend-faithfulness conclusion with `MpnCmpFrontEmit.cmpFold_val_full`, but
takes that conclusion as a hypothesis `hfaithful`.
`JasminLsemMemSourceTieArrUncond.loopMemArr_export_faithful_denote_uncond`
discharges it for the emitted `chain ++ writeback` body of **any** `ArrMemN`
update, given only the counter schedule, the seed and the counter-name hygiene.

This module identifies the front-compiled `cmpUpdate` as an `ArrMemN` member and
instantiates the unconditional export theorem at it, closing
`cmp_emitted_machine_val` with no per-trip simulation hypothesis.

## Main results

* `cmpUpdate_arrMemN` — the front-compiled `mpn_cmp` limb body is a member of the
  array-returning stack-memory fragment `ArrMemN`.
* `cmpLoop_export_faithful_denote` — the export faithfulness conclusion at
  `cmpUpdate`, the shape `cmp_emitted_machine_val` takes as `hfaithful`.
* `cmp_emitted_machine_val_closed` — the machine execution of the emitted
  `mpn_cmp` loop produces an output array whose cell `0` holds the comparison
  sign `cmpSign` of the two operands' `bignumVal`, with no per-trip simulation
  hypothesis.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripCmp

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit (segCells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontDenote
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpLsemTie
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpArrMemN

/-! ## 1. The front-compiled limb body is an `ArrMemN` member -/

/-- **The front-compiled `mpn_cmp` limb body is in the array-returning stack-memory
    fragment.** The front output is a chain of register-producing heads (the three
    array loads, the index arithmetic, the two branch-free comparison blocks and
    the mask select) and one `stackStore` binding, terminated by a `.ret` at the
    output array — the `ArrMemN` shape. -/
theorem cmpUpdate_arrMemN : ArrMemN cmpUpdate :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpArrMemN.cmpUpdate_arrMemN

/-! ## 2. Export faithfulness at `cmpUpdate`, per-trip discharged -/

/-- **The array-accumulator export faithfulness at `cmpUpdate`.** The emitted
    `mpn_cmp` loop's machine run decodes at the accumulator's array slot to the
    source fold `JLoopBodyN.denote ⟨n, cmpUpdate⟩`, with only the counter
    schedule, the seed and the counter-name hygiene as hypotheses — the shape
    `cmp_emitted_machine_val` takes as `hfaithful`. The instantiation of
    `loopMemArr_export_faithful_denote_uncond` at `cmpUpdate` and
    `cmpUpdate_arrMemN`. -/
theorem cmpLoop_export_faithful_denote
    (V : Ctxt.Valuation Gouter)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AO, AO, r64] : Ctxt jasminDialect).length + 2)
      (([AO, AO, r64] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs cmpInvs V) 0 (cmpInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (cmpCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN cmpUpdate nReg)
      ((cmpCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN cmpUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN cmpUpdate nReg)
      (cmpCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (cmpCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN cmpUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN cmpUpdate nReg)))
          ((cmpCount.lookup V).toNat * ((loopBodyArrFullMN cmpUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AO, AO, r64]) 64 NR
            = some (JLoopBodyN.denote ⟨(cmpCount.lookup V).toNat, cmpUpdate⟩
                (Expr.lookupArgs cmpInvs V) (cmpInit.lookup V)) :=
  loopMemArr_export_faithful_denote_uncond cmpUpdate cmpUpdate_arrMemN
    (Expr.lookupArgs cmpInvs V) fn top nReg hna hnr s hfn hpc (cmpInit.lookup V)
    hseed hn0 (cmpCount.lookup V).toNat hm bprev blast bfin hprev hlast hbfin htaken hhalt

/-! ## 3. The unconditional flagship value theorem -/

/-- **The compiled `mpn_cmp` computes the comparison sign, unconditionally.** For a
    nonzero trip count and a zeroed result cell, the emitted machine loop — run
    under `lsemFuelMemL` from a start state with the counter schedule, the seed
    and the counter-name hygiene — halts with an output array whose cell `0` holds
    `cmpSign` of the two operands' `bignumVal` over the limbs `0, …, n - 1`. The
    per-trip array simulation is discharged through `cmpUpdate_arrMemN`, so no
    faithfulness hypothesis remains. -/
theorem cmp_emitted_machine_val_closed
    (V : Ctxt.Valuation Gouter)
    (hn : 0 < (cmpCount.lookup V).toNat)
    (h0 : memGetDyn (cmpInit.lookup V) 0 = 0)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AO, AO, r64] : Ctxt jasminDialect).length + 2)
      (([AO, AO, r64] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs cmpInvs V) 0 (cmpInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (cmpCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN cmpUpdate nReg)
      ((cmpCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN cmpUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN cmpUpdate nReg)
      (cmpCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (cmpCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN cmpUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ (t : LstatePM) (out : Fin NR → BitVec 64),
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN cmpUpdate nReg)))
          ((cmpCount.lookup V).toNat * ((loopBodyArrFullMN cmpUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AO, AO, r64]) 64 NR = some out
        ∧ memGetDyn out 0
            = cmpSign (bignumVal (segCells (apVar.lookup V) 0 (cmpCount.lookup V).toNat))
                (bignumVal (segCells (bpVar.lookup V) 0 (cmpCount.lookup V).toNat)) :=
  cmp_emitted_machine_val V hn h0 fn top nReg
    (loopBodyArrFullMN cmpUpdate nReg) (accRegMN [AO, AO, r64]) s
    (cmpLoop_export_faithful_denote V fn top nReg hna hnr s hfn hpc hseed hn0 hm
      bprev blast bfin hprev hlast hbfin htaken hhalt)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripCmp
