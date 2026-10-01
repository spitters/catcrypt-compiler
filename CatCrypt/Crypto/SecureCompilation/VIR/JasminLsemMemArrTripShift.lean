/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftLsemTie
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTrip
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond

/-!
# The emitted `mpn_lshift` and `mpn_rshift` loop is an array-carrier fragment member, unconditionally

`MpnShiftLsemTie.lshift_emitted_machine_val` / `rshift_emitted_machine_val`
compose the array-accumulator backend-faithfulness conclusion with
`lshiftFold_val` / `rshiftFold_val`, but take that conclusion as a hypothesis
`hfaithful`.
`JasminLsemMemSourceTieArrUncond.loopMemArr_export_faithful_denote_uncond`
discharges it for the emitted `chain ++ writeback` body of any `ArrMemN` update,
given only the counter schedule, the seed and the counter-name hygiene.

This module identifies the front-compiled `shiftUpdate` as an `ArrMemN` member
and instantiates the unconditional export theorem at it, closing the machine-
value theorems with no per-trip simulation hypothesis.

## Main results

* `shiftUpdate_arrMemN` — the front-compiled funnel body is a member of the
  array-returning stack-memory fragment `ArrMemN`.
* `shiftLoop_export_faithful_denote` — the export faithfulness conclusion at the
  funnel body, the shape the machine-value ties take as `hfaithful`.
* `lshift_emitted_machine_val_closed` — the machine execution of the emitted
  `mpn_lshift` loop produces output cells that `bignumVal`-recombine to
  `up[0..n) · 2^cnt`, with no per-trip simulation hypothesis.
* `rshift_emitted_machine_val_closed` — the same at the
  `value (rp[0..n+1)) · 2^cnt = value (up[0..n)) · 2^64` contract.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripShift

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontDenote
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftLsemTie

/-! ## 1. The front-compiled funnel body is an `ArrMemN` member -/

/-- **The front-compiled funnel body is in the array-returning stack-memory
    fragment.** The front output is a chain of register-producing heads (two
    `stackLoad`s, the complementary shift, the two funnel shifts, the merge and
    the index increment) and two `stackStore` bindings, terminated by a `.ret` at
    the output array — the `ArrMemN` shape. The variable funnel shifts land in the
    generic register-arithmetic head and the `64`/`1` literals in the constant
    head. -/
theorem shiftUpdate_arrMemN : ArrMemN shiftUpdate := by
  unfold shiftUpdate
  repeat first
    | exact ArrMemN.ret _
    | refine ArrMemN.store rfl _ ?_
    | refine ArrMemN.reg _ ?_ ?_
    | exact ScalarMemN.load rfl _ (.ret .here)
    | exact ScalarMemN.mulhi rfl _ (.ret .here)
    | exact ScalarMemN.addLo rfl _ (.ret .here)
    | exact ScalarMemN.addHi rfl _ (.ret .here)
    | exact ScalarMemN.const _ (by decide) rfl _ (.ret .here)
    | exact ScalarMemN.sel rfl _ (.ret .here)
    | exact ScalarMemN.shr (by decide) rfl _ (.ret .here)
    | exact ScalarMemN.shl (by decide) rfl _ (.ret .here)
    | exact ScalarMemN.sar (by decide) rfl _ (.ret .here)
    | exact ScalarMemN.cast rfl _ (.ret .here)
    | exact ScalarMemN.var _ rfl _ (.ret .here)

/-! ## 2. Export faithfulness at the funnel body, per-trip discharged -/

/-- **The array-accumulator export faithfulness at `shiftUpdate`.** The emitted
    funnel-shift loop's machine run decodes at the accumulator's array slot to the
    source fold `JLoopBodyN.denote ⟨n, shiftUpdate⟩`, with only the counter
    schedule, the seed and the counter-name hygiene as hypotheses — the shape the
    machine-value ties take as `hfaithful`. The instantiation of
    `loopMemArr_export_faithful_denote_uncond` at `shiftUpdate` and
    `shiftUpdate_arrMemN`. -/
theorem shiftLoop_export_faithful_denote
    (V : Ctxt.Valuation Gouter)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AU, r64] : Ctxt jasminDialect).length + 2)
      (([AU, r64] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs shiftInvs V) 0 (shiftInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (shiftCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN shiftUpdate nReg)
      ((shiftCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN shiftUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN shiftUpdate nReg)
      (shiftCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (shiftCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN shiftUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN shiftUpdate nReg)))
          ((shiftCount.lookup V).toNat * ((loopBodyArrFullMN shiftUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AU, r64]) 64 NRS
            = some (JLoopBodyN.denote ⟨(shiftCount.lookup V).toNat, shiftUpdate⟩
                (Expr.lookupArgs shiftInvs V) (shiftInit.lookup V)) :=
  loopMemArr_export_faithful_denote_uncond shiftUpdate shiftUpdate_arrMemN
    (Expr.lookupArgs shiftInvs V) fn top nReg hna hnr s hfn hpc (shiftInit.lookup V)
    hseed hn0 (shiftCount.lookup V).toNat hm bprev blast bfin hprev hlast hbfin htaken hhalt

/-! ## 3. The unconditional flagship value theorems -/

/-- **The compiled `mpn_lshift` computes the scaled value, unconditionally.** For
    a trip count within the model's output array, a shift amount at most `64` and
    cell `0` seeded to zero, the emitted machine loop — run under `lsemFuelMemL`
    from a start state with the counter schedule, the seed and the counter-name
    hygiene — halts with output cells `0, …, n` that recombine via `bignumVal` to
    `up[0..n) · 2^cnt`. The per-trip array simulation is discharged through
    `shiftUpdate_arrMemN`, so no faithfulness hypothesis remains. -/
theorem lshift_emitted_machine_val_closed
    (V : Ctxt.Valuation Gouter)
    (hcnt : (shVar.lookup V).toNat ≤ 64)
    (hnr' : (shiftCount.lookup V).toNat < NRS)
    (h0 : memGetDyn (shiftInit.lookup V) 0 = 0)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AU, r64] : Ctxt jasminDialect).length + 2)
      (([AU, r64] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs shiftInvs V) 0 (shiftInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (shiftCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN shiftUpdate nReg)
      ((shiftCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN shiftUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN shiftUpdate nReg)
      (shiftCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (shiftCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN shiftUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ (t : LstatePM) (out : Fin NRS → BitVec 64),
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN shiftUpdate nReg)))
          ((shiftCount.lookup V).toNat * ((loopBodyArrFullMN shiftUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AU, r64]) 64 NRS = some out
        ∧ bignumVal (cells out ((shiftCount.lookup V).toNat + 1))
            = bignumVal (cells (upVar.lookup V) (shiftCount.lookup V).toNat)
                * 2 ^ (shVar.lookup V).toNat :=
  lshift_emitted_machine_val V hcnt hnr' h0 fn top nReg
    (loopBodyArrFullMN shiftUpdate nReg) (accRegMN [AU, r64]) s
    (shiftLoop_export_faithful_denote V fn top nReg hna hnr s hfn hpc hseed hn0 hm
      bprev blast bfin hprev hlast hbfin htaken hhalt)

/-- **The compiled `mpn_rshift` computes the scaled value, unconditionally.** With
    `sh = 64 - cnt` and cell `0` seeded to zero, the emitted machine loop halts
    with output cells that recombine via `bignumVal` to
    `value (rp[0..n+1)) · 2^cnt = value (up[0..n)) · 2^64`, for a `cnt ≤ 64`, with
    no faithfulness hypothesis. -/
theorem rshift_emitted_machine_val_closed
    (V : Ctxt.Valuation Gouter) (cnt : Nat) (hcnt : cnt ≤ 64)
    (hsheq : (shVar.lookup V).toNat = 64 - cnt)
    (hnr' : (shiftCount.lookup V).toNat < NRS)
    (h0 : memGetDyn (shiftInit.lookup V) 0 = 0)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AU, r64] : Ctxt jasminDialect).length + 2)
      (([AU, r64] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs shiftInvs V) 0 (shiftInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (shiftCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN shiftUpdate nReg)
      ((shiftCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN shiftUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN shiftUpdate nReg)
      (shiftCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (shiftCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN shiftUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ (t : LstatePM) (out : Fin NRS → BitVec 64),
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN shiftUpdate nReg)))
          ((shiftCount.lookup V).toNat * ((loopBodyArrFullMN shiftUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AU, r64]) 64 NRS = some out
        ∧ bignumVal (cells out ((shiftCount.lookup V).toNat + 1)) * 2 ^ cnt
            = bignumVal (cells (upVar.lookup V) (shiftCount.lookup V).toNat) * 2 ^ 64 :=
  rshift_emitted_machine_val V cnt hcnt hsheq hnr' h0 fn top nReg
    (loopBodyArrFullMN shiftUpdate nReg) (accRegMN [AU, r64]) s
    (shiftLoop_export_faithful_denote V fn top nReg hna hnr s hfn hpc hseed hn0 hm
      bprev blast bfin hprev hlast hbfin htaken hhalt)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripShift
