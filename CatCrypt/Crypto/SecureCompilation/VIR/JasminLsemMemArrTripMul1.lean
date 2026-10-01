/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1LsemTie
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTrip
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond

/-!
# The emitted `mpn_mul_1` loop is an array-carrier fragment member, unconditionally

`MpnMul1LsemTie.mul1_emitted_machine_val` composes the array-accumulator
backend-faithfulness conclusion with `MpnMul1FrontDenote.mul1RtProg_val`, but
takes that conclusion as a hypothesis `hfaithful`.
`JasminLsemMemSourceTieArrUncond.loopMemArr_export_faithful_denote_uncond`
discharges it for the emitted `chain ++ writeback` body of **any** `ArrMemN`
update, given only the counter schedule, the seed and the counter-name hygiene.

This module identifies the front-compiled `mul1Update` as an `ArrMemN` member and
instantiates the unconditional export theorem at it, closing
`mul1_emitted_machine_val` with no per-trip simulation hypothesis.

## Main results

* `mul1Update_arrMemN` — the front-compiled `mpn_mul_1` limb body is a member of
  the array-returning stack-memory fragment `ArrMemN`.
* `mul1Loop_export_faithful_denote` — the export faithfulness conclusion at
  `mul1Update`, the shape `mul1_emitted_machine_val` takes as `hfaithful`.
* `mul1_emitted_machine_val_closed` — the machine execution of the emitted
  `mpn_mul_1` loop produces output cells that `bignumVal`-recombine to
  `up[0..n) * v`, with no per-trip simulation hypothesis.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripMul1

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1LsemTie

/-! ## 1. The front-compiled limb body is an `ArrMemN` member -/

/-- **The front-compiled `mpn_mul_1` limb body is in the array-returning
    stack-memory fragment.** The front output is a chain of register-producing
    heads (two `stackLoad`s, the multiply/carry arithmetic) and two `stackStore`
    bindings, terminated by a `.ret` at the output array — exactly the `ArrMemN`
    shape. The head of the front term is exposed by reduction and the fragment
    constructors are applied in cascade. -/
theorem mul1Update_arrMemN : ArrMemN mul1Update := by
  unfold mul1Update
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

/-! ## 2. Export faithfulness at `mul1Update`, per-trip discharged -/

/-- **The array-accumulator export faithfulness at `mul1Update`.** The emitted
    `mpn_mul_1` loop's machine run decodes at the accumulator's array slot to the
    source fold `JLoopBodyN.denote ⟨n, mul1Update⟩`, with only the counter
    schedule, the seed and the counter-name hygiene as hypotheses — the shape
    `mul1_emitted_machine_val` takes as `hfaithful`. The instantiation of
    `loopMemArr_export_faithful_denote_uncond` at `mul1Update` and
    `mul1Update_arrMemN`. -/
theorem mul1Loop_export_faithful_denote
    (V : Ctxt.Valuation Gouter)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([r64, AU] : Ctxt jasminDialect).length + 2)
      (([r64, AU] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs mul1Invs V) 0 (mul1Init.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (mul1Count.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN mul1Update nReg)
      ((mul1Count.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN mul1Update nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN mul1Update nReg)
      (mul1Count.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (mul1Count.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN mul1Update nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN mul1Update nReg)))
          ((mul1Count.lookup V).toNat * ((loopBodyArrFullMN mul1Update nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [r64, AU]) 64 NR
            = some (JLoopBodyN.denote ⟨(mul1Count.lookup V).toNat, mul1Update⟩
                (Expr.lookupArgs mul1Invs V) (mul1Init.lookup V)) :=
  loopMemArr_export_faithful_denote_uncond mul1Update mul1Update_arrMemN
    (Expr.lookupArgs mul1Invs V) fn top nReg hna hnr s hfn hpc (mul1Init.lookup V)
    hseed hn0 (mul1Count.lookup V).toNat hm bprev blast bfin hprev hlast hbfin htaken hhalt

/-! ## 3. The unconditional flagship value theorem -/

/-- **The compiled `mpn_mul_1` computes the product, unconditionally.** For a
    trip count within the model's output array and a zeroed carry seed, the
    emitted machine loop — run under `lsemFuelMemL` from a start state with the
    counter schedule, the seed and the counter-name hygiene — halts with output
    cells `0, …, n` that recombine via `bignumVal` to `up[0..n) * v`. The
    per-trip array simulation is discharged through `mul1Update_arrMemN`, so no
    faithfulness hypothesis remains. -/
theorem mul1_emitted_machine_val_closed
    (V : Ctxt.Valuation Gouter)
    (hn : (mul1Count.lookup V).toNat < NR)
    (h0 : memGetDyn (mul1Init.lookup V) 0 = 0)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([r64, AU] : Ctxt jasminDialect).length + 2)
      (([r64, AU] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs mul1Invs V) 0 (mul1Init.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (mul1Count.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN mul1Update nReg)
      ((mul1Count.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN mul1Update nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN mul1Update nReg)
      (mul1Count.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (mul1Count.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN mul1Update nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ (t : LstatePM) (out : Fin NR → BitVec 64),
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN mul1Update nReg)))
          ((mul1Count.lookup V).toNat * ((loopBodyArrFullMN mul1Update nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [r64, AU]) 64 NR = some out
        ∧ bignumVal (cells out ((mul1Count.lookup V).toNat + 1))
            = bignumVal (cells (upVar.lookup V) (mul1Count.lookup V).toNat)
                * (vVar.lookup V).toNat :=
  mul1_emitted_machine_val V hn h0 fn top nReg
    (loopBodyArrFullMN mul1Update nReg) (accRegMN [r64, AU]) s
    (mul1Loop_export_faithful_denote V fn top nReg hna hnr s hfn hpc hseed hn0 hm
      bprev blast bfin hprev hlast hbfin htaken hhalt)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripMul1
