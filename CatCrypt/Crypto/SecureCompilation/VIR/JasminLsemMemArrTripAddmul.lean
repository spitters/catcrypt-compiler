/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1LsemTie
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTrip
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond

/-!
# The emitted `mpn_addmul_1` and `mpn_submul_1` loops are array-carrier fragment members, unconditionally

`MpnAddmulSubmul1LsemTie.addmul_emitted_machine_val` / `submul_emitted_machine_val`
compose the array-accumulator backend-faithfulness conclusion with
`addmulFold_val_zero` / `submulFold_val_zero`, but take that conclusion as a
hypothesis `hfaithful`.
`JasminLsemMemSourceTieArrUncond.loopMemArr_export_faithful_denote_uncond`
discharges it for the emitted `chain ++ writeback` body of **any** `ArrMemN`
update, given only the counter schedule, the seed and the counter-name hygiene.

This module identifies the front-compiled `addmulUpdate` / `submulUpdate` as
`ArrMemN` members and instantiates the unconditional export theorem at each,
closing the machine-value theorems with no per-trip simulation hypothesis.

## Main results

* `addmulUpdate_arrMemN` / `submulUpdate_arrMemN` — the front-compiled limb
  bodies are members of the array-returning stack-memory fragment `ArrMemN`.
* `addmulLoop_export_faithful_denote` / `submulLoop_export_faithful_denote` — the
  export faithfulness conclusion at each body, the shape the machine-value tie
  takes as `hfaithful`.
* `addmul_emitted_machine_val_closed` — the machine execution of the emitted
  `mpn_addmul_1` loop produces output cells that `bignumVal`-recombine to the
  multiply-accumulate contract `rp[0..n) + up[0..n) · v`, with no per-trip
  simulation hypothesis.
* `submul_emitted_machine_val_closed` — the same at the multiply-subtract
  contract.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripAddmul

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells NR AR AU r64 Gouter)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontDenote
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1LsemTie

/-! ## 1. The front-compiled limb bodies are `ArrMemN` members -/

/-- **The front-compiled `mpn_addmul_1` limb body is in the array-returning
    stack-memory fragment.** The front output is a chain of register-producing
    heads (three `stackLoad`s, the multiply/carry arithmetic, the accumulate
    step) and two `stackStore` bindings, terminated by a `.ret` at the output
    array — exactly the `ArrMemN` shape. The head of the front term is exposed by
    reduction and the fragment constructors are applied in cascade. -/
theorem addmulUpdate_arrMemN : ArrMemN addmulUpdate := by
  unfold addmulUpdate
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

/-- **The front-compiled `mpn_submul_1` limb body is in the array-returning
    stack-memory fragment.** The multiply-subtract analogue of
    `addmulUpdate_arrMemN`. -/
theorem submulUpdate_arrMemN : ArrMemN submulUpdate := by
  unfold submulUpdate
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

/-! ## 2. Export faithfulness at each body, per-trip discharged -/

/-- **The array-accumulator export faithfulness at `addmulUpdate`.** The emitted
    `mpn_addmul_1` loop's machine run decodes at the accumulator's array slot to
    the source fold `JLoopBodyN.denote ⟨n, addmulUpdate⟩`, with only the counter
    schedule, the seed and the counter-name hygiene as hypotheses — the shape
    `addmul_emitted_machine_val` takes as `hfaithful`. The instantiation of
    `loopMemArr_export_faithful_denote_uncond` at `addmulUpdate` and
    `addmulUpdate_arrMemN`. -/
theorem addmulLoop_export_faithful_denote
    (V : Ctxt.Valuation Gouter)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AU, r64, r64] : Ctxt jasminDialect).length + 2)
      (([AU, r64, r64] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs accInvs V) 0 (accInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (accCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN addmulUpdate nReg)
      ((accCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN addmulUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN addmulUpdate nReg)
      (accCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (accCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN addmulUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN addmulUpdate nReg)))
          ((accCount.lookup V).toNat * ((loopBodyArrFullMN addmulUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AU, r64, r64]) 64 NR
            = some (JLoopBodyN.denote ⟨(accCount.lookup V).toNat, addmulUpdate⟩
                (Expr.lookupArgs accInvs V) (accInit.lookup V)) :=
  loopMemArr_export_faithful_denote_uncond addmulUpdate addmulUpdate_arrMemN
    (Expr.lookupArgs accInvs V) fn top nReg hna hnr s hfn hpc (accInit.lookup V)
    hseed hn0 (accCount.lookup V).toNat hm bprev blast bfin hprev hlast hbfin htaken hhalt

/-- **The array-accumulator export faithfulness at `submulUpdate`.** The
    multiply-subtract analogue of `addmulLoop_export_faithful_denote`. -/
theorem submulLoop_export_faithful_denote
    (V : Ctxt.Valuation Gouter)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AU, r64, r64] : Ctxt jasminDialect).length + 2)
      (([AU, r64, r64] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs accInvs V) 0 (accInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (accCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN submulUpdate nReg)
      ((accCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN submulUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN submulUpdate nReg)
      (accCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (accCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN submulUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN submulUpdate nReg)))
          ((accCount.lookup V).toNat * ((loopBodyArrFullMN submulUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AU, r64, r64]) 64 NR
            = some (JLoopBodyN.denote ⟨(accCount.lookup V).toNat, submulUpdate⟩
                (Expr.lookupArgs accInvs V) (accInit.lookup V)) :=
  loopMemArr_export_faithful_denote_uncond submulUpdate submulUpdate_arrMemN
    (Expr.lookupArgs accInvs V) fn top nReg hna hnr s hfn hpc (accInit.lookup V)
    hseed hn0 (accCount.lookup V).toNat hm bprev blast bfin hprev hlast hbfin htaken hhalt

/-! ## 3. The unconditional flagship value theorems -/

/-- **The compiled `mpn_addmul_1` computes the multiply-accumulate,
    unconditionally.** For a trip count within the model's output array and a
    zeroed carry cell, the emitted machine loop — run under `lsemFuelMemL` from a
    start state with the counter schedule, the seed and the counter-name hygiene
    — halts with output cells `0, …, n-1` and carry cell `n` that recombine via
    `bignumVal` to `rp[0..n) + up[0..n) · v`. The per-trip array simulation is
    discharged through `addmulUpdate_arrMemN`, so no faithfulness hypothesis
    remains. -/
theorem addmul_emitted_machine_val_closed
    (V : Ctxt.Valuation Gouter)
    (hn : (accCount.lookup V).toNat < NR)
    (h0 : memGetDyn (accInit.lookup V) (accCount.lookup V).toNat = 0)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AU, r64, r64] : Ctxt jasminDialect).length + 2)
      (([AU, r64, r64] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs accInvs V) 0 (accInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (accCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN addmulUpdate nReg)
      ((accCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN addmulUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN addmulUpdate nReg)
      (accCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (accCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN addmulUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ (t : LstatePM) (out : Fin NR → BitVec 64),
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN addmulUpdate nReg)))
          ((accCount.lookup V).toNat * ((loopBodyArrFullMN addmulUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AU, r64, r64]) 64 NR = some out
        ∧ (bignumVal (cells out (accCount.lookup V).toNat) : ℤ)
              + (2 ^ 64) ^ (accCount.lookup V).toNat
                  * (memGetDyn out (accCount.lookup V).toNat).toNat
            = (bignumVal (cells (accInit.lookup V) (accCount.lookup V).toNat) : ℤ)
              + (bignumVal (cells (upVarA.lookup V) (accCount.lookup V).toNat) : ℤ)
                  * (vVarA.lookup V).toNat :=
  addmul_emitted_machine_val V hn h0 fn top nReg
    (loopBodyArrFullMN addmulUpdate nReg) (accRegMN [AU, r64, r64]) s
    (addmulLoop_export_faithful_denote V fn top nReg hna hnr s hfn hpc hseed hn0 hm
      bprev blast bfin hprev hlast hbfin htaken hhalt)

/-- **The compiled `mpn_submul_1` computes the multiply-subtract,
    unconditionally.** The multiply-subtract analogue of
    `addmul_emitted_machine_val_closed`: the halt state's array cells and the
    borrow cell recombine via `bignumVal` to
    `rp[0..n) + up[0..n) · v = rp'[0..n) + 2^(64n) · borrow`, with no
    faithfulness hypothesis. -/
theorem submul_emitted_machine_val_closed
    (V : Ctxt.Valuation Gouter)
    (hn : (accCount.lookup V).toNat < NR)
    (h0 : memGetDyn (accInit.lookup V) (accCount.lookup V).toNat = 0)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AU, r64, r64] : Ctxt jasminDialect).length + 2)
      (([AU, r64, r64] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs accInvs V) 0 (accInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (accCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN submulUpdate nReg)
      ((accCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN submulUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN submulUpdate nReg)
      (accCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (accCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN submulUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ (t : LstatePM) (out : Fin NR → BitVec 64),
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN submulUpdate nReg)))
          ((accCount.lookup V).toNat * ((loopBodyArrFullMN submulUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AU, r64, r64]) 64 NR = some out
        ∧ (bignumVal (cells out (accCount.lookup V).toNat) : ℤ)
              + (bignumVal (cells (upVarA.lookup V) (accCount.lookup V).toNat) : ℤ)
                  * (vVarA.lookup V).toNat
            = (bignumVal (cells (accInit.lookup V) (accCount.lookup V).toNat) : ℤ)
              + (2 ^ 64) ^ (accCount.lookup V).toNat
                  * (memGetDyn out (accCount.lookup V).toNat).toNat :=
  submul_emitted_machine_val V hn h0 fn top nReg
    (loopBodyArrFullMN submulUpdate nReg) (accRegMN [AU, r64, r64]) s
    (submulLoop_export_faithful_denote V fn top nReg hna hnr s hfn hpc hseed hn0 hm
      bprev blast bfin hprev hlast hbfin htaken hhalt)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripAddmul
