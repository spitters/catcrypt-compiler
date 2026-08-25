/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1LsemTie
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1ArrMemN
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTrip
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond

/-!
# The emitted `mpn_divrem_1` loop is an array-carrier fragment member, unconditionally

`MpnDivRem1LsemTie.divrem_emitted_machine_val` composes the array-accumulator
backend-faithfulness conclusion with `MpnDivRem1FrontDenoteVal.divRtProg_val`, but
takes that conclusion as a hypothesis `hfaithful`.
`JasminLsemMemSourceTieArrUncond.loopMemArr_export_faithful_denote_uncond`
discharges it for the emitted `chain ++ writeback` body of **any** `ArrMemN`
update, given only the counter schedule, the seed and the counter-name hygiene.

This module identifies the front-compiled `divUpdate` as an `ArrMemN` member and
instantiates the unconditional export theorem at it, closing
`divrem_emitted_machine_val` with no per-trip simulation hypothesis.

## Main results

* `divUpdate_arrMemN` — the front-compiled `mpn_divrem_1` limb body is a member of
  the array-returning stack-memory fragment `ArrMemN`.
* `divremLoop_export_faithful_denote` — the export faithfulness conclusion at
  `divUpdate`, the shape `divrem_emitted_machine_val` takes as `hfaithful`.
* `divrem_emitted_machine_val_closed` — the machine execution of the emitted
  `mpn_divrem_1` loop produces an output array that holds the exact Euclidean
  fold `divFold` of the argument registers, under the normalisation
  preconditions and with no per-trip simulation hypothesis.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripDivRem

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontDenote
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1LsemTie

/-! ## 1. The front-compiled limb body is an `ArrMemN` member -/

/-- **The front-compiled `mpn_divrem_1` limb body is in the array-returning
    stack-memory fragment.** The front output is a chain of register-producing
    heads (the index arithmetic, the two array loads, the widening reciprocal
    multiply, the three branch-free comparison blocks and the mask corrections)
    and two `stackStore` bindings — the quotient limb and the new remainder —
    terminated by a `.ret` at the output array — the `ArrMemN` shape. -/
theorem divUpdate_arrMemN : ArrMemN divUpdate :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1ArrMemN.divUpdate_arrMemN

/-! ## 2. Export faithfulness at `divUpdate`, per-trip discharged -/

/-- **The array-accumulator export faithfulness at `divUpdate`.** The emitted
    `mpn_divrem_1` loop's machine run decodes at the accumulator's array slot to
    the source fold `JLoopBodyN.denote ⟨n, divUpdate⟩`, with only the counter
    schedule, the seed and the counter-name hygiene as hypotheses — the shape
    `divrem_emitted_machine_val` takes as `hfaithful`. The instantiation of
    `loopMemArr_export_faithful_denote_uncond` at `divUpdate` and
    `divUpdate_arrMemN`. -/
theorem divremLoop_export_faithful_denote
    (V : Ctxt.Valuation Gouter)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([r64, r64, r64, AU] : Ctxt jasminDialect).length + 2)
      (([r64, r64, r64, AU] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs divInvs V) 0 (divInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (divCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN divUpdate nReg)
      ((divCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN divUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN divUpdate nReg)
      (divCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (divCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN divUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN divUpdate nReg)))
          ((divCount.lookup V).toNat * ((loopBodyArrFullMN divUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [r64, r64, r64, AU]) 64 NR
            = some (JLoopBodyN.denote ⟨(divCount.lookup V).toNat, divUpdate⟩
                (Expr.lookupArgs divInvs V) (divInit.lookup V)) :=
  loopMemArr_export_faithful_denote_uncond divUpdate divUpdate_arrMemN
    (Expr.lookupArgs divInvs V) fn top nReg hna hnr s hfn hpc (divInit.lookup V)
    hseed hn0 (divCount.lookup V).toNat hm bprev blast bfin hprev hlast hbfin htaken hhalt

/-! ## 3. The unconditional flagship value theorem -/

/-- **The compiled `mpn_divrem_1` computes the Euclidean quotient/remainder,
    unconditionally.** Under the normalisation preconditions (divisor `d` with bit
    63 set, correct reciprocal `dinv`, cleared seed cell `RS`, at least one trip,
    top limb index below `RS`), the emitted machine loop — run under
    `lsemFuelMemL` from a start state with the counter schedule, the seed and the
    counter-name hygiene — halts with an output array that decodes to the exact
    Euclidean fold `divFold` of the argument registers. The per-trip array
    simulation is discharged through `divUpdate_arrMemN`, so no faithfulness
    hypothesis remains. -/
theorem divrem_emitted_machine_val_closed
    (V : Ctxt.Valuation Gouter)
    (hrs : RS < NR)
    (htop : (nVar.lookup V).toNat - 1 < RS)
    (h0 : memGetDyn (divInit.lookup V) RS = 0)
    (hd2 : 2 ^ 63 ≤ (dVar.lookup V).toNat)
    (hv : (dinvVar.lookup V).toNat = (2 ^ 128 - 1) / (dVar.lookup V).toNat - 2 ^ 64)
    (hn : 1 ≤ (nVar.lookup V).toNat)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([r64, r64, r64, AU] : Ctxt jasminDialect).length + 2)
      (([r64, r64, r64, AU] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs divInvs V) 0 (divInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (divCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN divUpdate nReg)
      ((divCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN divUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN divUpdate nReg)
      (divCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (divCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN divUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN divUpdate nReg)))
          ((divCount.lookup V).toNat * ((loopBodyArrFullMN divUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [r64, r64, r64, AU]) 64 NR
            = some (divFold (upVar.lookup V) (dVar.lookup V)
                ((nVar.lookup V).toNat - 1) RS (nVar.lookup V).toNat (divInit.lookup V)) :=
  divrem_emitted_machine_val V hrs htop h0 hd2 hv hn fn top nReg
    (loopBodyArrFullMN divUpdate nReg) (accRegMN [r64, r64, r64, AU]) s
    (divremLoop_export_faithful_denote V fn top nReg hna hnr s hfn hpc hseed hn0 hm
      bprev blast bfin hprev hlast hbfin htaken hhalt)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripDivRem
