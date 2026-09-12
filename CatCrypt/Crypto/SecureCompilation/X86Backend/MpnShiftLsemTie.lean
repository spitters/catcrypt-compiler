/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontDenote
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

/-!
# The machine-execution → integer-spec tie for the emitted `mpn_lshift` and `mpn_rshift` loops

`MpnShiftFrontDenote.shiftRtProg_fold` ends the front-side chain at
`ComL.denote`: the emitted runtime-trip program's denotation is the funnel
word-model fold `shiftFold` of the argument registers.
`JasminLsemMemSourceTieUncond.comL_forLoopNRt_ret_denote_acc` unfolds the front
node `ComL.forLoopNRt`'s denotation to the source loop's `JLoopBodyN.denote`.

The accumulator is the output array `rp` (`accCTy = .memref NRS`, mapped to
`.stackArr 64 NRS = AR`), so `shiftUpdate` is a legal array-accumulator update.

This module composes: given the array-accumulator backend-faithfulness
conclusion at `shiftUpdate` — the emitted machine loop's execution decodes at the
accumulator slot to `JLoopBodyN.denote ⟨n, shiftUpdate⟩` (the shape
`loopMemArr_export_faithful_denote` produces) — the halt state's output cells
recombine via `bignumVal` to the funnel-shift contract in its two readings. The
faithfulness conclusion is taken as a hypothesis here; its unconditional
discharge for this body is completed in `JasminLsemMemArrTripShift`.

## Main results

* `shift_forLoopNRt_denote_eq_fold` — the front node's denotation
  (`ComL.forLoopNRt shiftUpdate … (.ret .here)`) equals the word-model fold
  `shiftFold`.
* `lshift_emitted_machine_val` — the full chain for `mpn_lshift`: the array-
  faithfulness conclusion at `shiftUpdate` composed with `lshiftFold_val`, giving
  output cells that `bignumVal`-recombine to `up[0..n) · 2^cnt`.
* `rshift_emitted_machine_val` — the same for `mpn_rshift`, at the
  `value (rp[0..n+1)) · 2^cnt = value (up[0..n)) · 2^64` contract.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftLsemTie

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM comL_forLoopNRt_ret_denote_acc)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftFrontDenote

/-! ## 1. The front node denotes the word-model fold -/

/-- The word-model fold reached by the emitted funnel-shift loop's denotation:
    the front node's `ComL.denote` equals `shiftFold` of the argument registers,
    for a shift amount at most `64`. -/
theorem shift_forLoopNRt_denote_eq_fold (V : Ctxt.Valuation Gouter)
    (hsh : (shVar.lookup V).toNat ≤ 64) :
    (ComL.forLoopNRt shiftUpdate shiftCount shiftInit shiftInvs (.ret .here)).denote V
      = shiftFold (upVar.lookup V) (shVar.lookup V).toNat
          (shiftCount.lookup V).toNat (shiftInit.lookup V) := by
  have hd := shiftRtProg_denote shiftUpdate_eq V
  have hf := shiftRtProg_fold V hsh
  exact (comL_forLoopNRt_ret_denote_acc shiftUpdate shiftCount shiftInit shiftInvs V).trans
    (Option.some.inj (hd.symm.trans hf))

/-! ## 2. The machine execution computes the funnel shift -/

/-- **The machine execution computes the `mpn_lshift` value.** Given the array-
    accumulator backend-faithfulness conclusion at `shiftUpdate` — the emitted
    machine loop `body` run by `lsemFuelMemL` from a start state `s` decodes at
    the accumulator slot `arrSlot` to the source fold
    `JLoopBodyN.denote ⟨n, shiftUpdate⟩` (the shape
    `loopMemArr_export_faithful_denote` produces) — for a shift amount at most
    `64` and cell `0` seeded to zero, the halt state's output cells `0, …, n`
    recombine via `bignumVal` to `up[0..n) · 2^cnt`. The composition of the
    backend-faithfulness tie with `lshiftFold_val`. -/
theorem lshift_emitted_machine_val
    (V : Ctxt.Valuation Gouter)
    (hcnt : (shVar.lookup V).toNat ≤ 64)
    (hn : (shiftCount.lookup V).toNat < NRS)
    (h0 : memGetDyn (shiftInit.lookup V) 0 = 0)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (arrSlot : String) (s : LstatePM)
    (hfaithful : ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((shiftCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NRS
            = some (JLoopBodyN.denote ⟨(shiftCount.lookup V).toNat, shiftUpdate⟩
                (Expr.lookupArgs shiftInvs V) (shiftInit.lookup V))) :
    ∃ (t : LstatePM) (out : Fin NRS → BitVec 64),
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((shiftCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NRS = some out
        ∧ bignumVal (cells out ((shiftCount.lookup V).toNat + 1))
            = bignumVal (cells (upVar.lookup V) (shiftCount.lookup V).toNat)
                * 2 ^ (shVar.lookup V).toNat := by
  obtain ⟨t, hrun, hdec⟩ := hfaithful
  have hd := shiftRtProg_denote shiftUpdate_eq V
  have hf := shiftRtProg_fold V hcnt
  have heq : JLoopBodyN.denote ⟨(shiftCount.lookup V).toNat, shiftUpdate⟩
        (Expr.lookupArgs shiftInvs V) (shiftInit.lookup V)
      = shiftFold (upVar.lookup V) (shVar.lookup V).toNat
          (shiftCount.lookup V).toNat (shiftInit.lookup V) :=
    Option.some.inj (hd.symm.trans hf)
  refine ⟨t, _, hrun, hdec, ?_⟩
  rw [heq]
  exact lshiftFold_val (upVar.lookup V) (shVar.lookup V).toNat hcnt (shiftInit.lookup V) h0
    (shiftCount.lookup V).toNat hn

/-- **The machine execution computes the `mpn_rshift` value.** With
    `sh = 64 - cnt` and cell `0` seeded to zero, the halt state's output cells
    recombine via `bignumVal` to
    `value (rp[0..n+1)) · 2^cnt = value (up[0..n)) · 2^64`, for a `cnt ≤ 64`. The
    composition of the backend-faithfulness tie with `rshiftFold_val`. -/
theorem rshift_emitted_machine_val
    (V : Ctxt.Valuation Gouter) (cnt : Nat) (hcnt : cnt ≤ 64)
    (hsheq : (shVar.lookup V).toNat = 64 - cnt)
    (hn : (shiftCount.lookup V).toNat < NRS)
    (h0 : memGetDyn (shiftInit.lookup V) 0 = 0)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (arrSlot : String) (s : LstatePM)
    (hfaithful : ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((shiftCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NRS
            = some (JLoopBodyN.denote ⟨(shiftCount.lookup V).toNat, shiftUpdate⟩
                (Expr.lookupArgs shiftInvs V) (shiftInit.lookup V))) :
    ∃ (t : LstatePM) (out : Fin NRS → BitVec 64),
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((shiftCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NRS = some out
        ∧ bignumVal (cells out ((shiftCount.lookup V).toNat + 1)) * 2 ^ cnt
            = bignumVal (cells (upVar.lookup V) (shiftCount.lookup V).toNat) * 2 ^ 64 := by
  obtain ⟨t, hrun, hdec⟩ := hfaithful
  have hd := shiftRtProg_denote shiftUpdate_eq V
  have hf := shiftRtProg_fold V (by omega)
  have heq : JLoopBodyN.denote ⟨(shiftCount.lookup V).toNat, shiftUpdate⟩
        (Expr.lookupArgs shiftInvs V) (shiftInit.lookup V)
      = shiftFold (upVar.lookup V) (shVar.lookup V).toNat
          (shiftCount.lookup V).toNat (shiftInit.lookup V) :=
    Option.some.inj (hd.symm.trans hf)
  refine ⟨t, _, hrun, hdec, ?_⟩
  rw [heq, hsheq]
  exact rshiftFold_val (upVar.lookup V) cnt hcnt (shiftInit.lookup V) h0
    (shiftCount.lookup V).toNat hn

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnShiftLsemTie
