/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontDenoteVal
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

/-!
# The machine-execution → integer-spec tie for the emitted `mpn_divrem_1` loop

`MpnDivRem1FrontEmit.divRem1RtProg_denote` states the emitted runtime-trip
program's denotation as the `JLoopBodyN` fold of the front body `divUpdate`, and
`MpnDivRem1FrontDenoteVal.divRtProg_val` states the same program's denotation as
the exact Euclidean fold `divFold` under the normalisation preconditions (divisor
`d` with bit 63 set, correct reciprocal `dinv`, seed cell `RS` below `d`, at
least one trip, top limb index below `RS`).
`JasminLsemMemSourceTieUncond.loopMemArr_export_faithful_denote` is the general
backend-faithfulness statement for an array-accumulator counter loop: the emitted
machine loop's execution decodes at the accumulator array slot to
`JLoopBodyN.denote ⟨n, update⟩` — the source loop's `n`-fold denotation.

The `mpn_divrem_1` accumulator is the output array `qp` (`accCTy = .memref NR`,
mapped to `mapTy (.memref NR) = .stackArr 64 NR = AQ`), so the array variant is
the type-correct faithfulness form and `divUpdate` is a legal `update` argument.

This module composes the two: given the array-faithfulness conclusion at
`divUpdate`, the emitted machine execution produces an output array whose cells
hold the Euclidean quotient/remainder fold of the dividend by the divisor. The
faithfulness conclusion is taken as a hypothesis of the shape
`loopMemArr_export_faithful_denote` produces; its unconditional discharge for
this body is completed in `JasminLsemMemArrTripDivRem`.

## Main results

* `divrem_emitted_machine_val_rem` — the full chain for `mpn_divrem_1`: the
  array-faithfulness conclusion at `divUpdate` composed with
  `divRtProg_val_rem`, giving an output array that holds the exact Euclidean
  fold `divFold` of the argument registers, under the normalisation
  preconditions with a seed remainder below the divisor.
* `divrem_emitted_machine_val` — its zero-seed instance.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1LsemTie

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontDenote
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontDenoteVal

/-! ## The machine execution computes the Euclidean quotient/remainder fold -/

/-- **The machine execution computes the Euclidean quotient/remainder fold, for
    an incoming remainder.** Given the array-accumulator backend-faithfulness
    conclusion at `divUpdate` — the emitted machine loop `body` run by
    `lsemFuelMemL` from a start state `s` decodes at the accumulator slot
    `arrSlot` to the source fold `JLoopBodyN.denote ⟨n, divUpdate⟩` — and the
    normalisation preconditions of `divRtProg_val_rem` (divisor `d` with bit 63
    set, correct reciprocal `dinv`, seed cell `RS` below `d`, at least one trip,
    top limb index below `RS`), the halt state's output array decodes to the
    exact Euclidean fold `divFold` of the argument registers. -/
theorem divrem_emitted_machine_val_rem
    (V : Ctxt.Valuation Gouter)
    (hrs : RS < NR)
    (htop : (nVar.lookup V).toNat - 1 < RS)
    (h0 : (memGetDyn (divInit.lookup V) RS).toNat < (dVar.lookup V).toNat)
    (hd2 : 2 ^ 63 ≤ (dVar.lookup V).toNat)
    (hv : (dinvVar.lookup V).toNat = (2 ^ 128 - 1) / (dVar.lookup V).toNat - 2 ^ 64)
    (hn : 1 ≤ (nVar.lookup V).toNat)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (arrSlot : String) (s : LstatePM)
    (hfaithful : ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((divCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NR
            = some (JLoopBodyN.denote ⟨(divCount.lookup V).toNat, divUpdate⟩
                (Expr.lookupArgs divInvs V) (divInit.lookup V))) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((divCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NR
            = some (divFold (upVar.lookup V) (dVar.lookup V)
                ((nVar.lookup V).toNat - 1) RS (nVar.lookup V).toNat (divInit.lookup V)) := by
  obtain ⟨t, hrun, hdec⟩ := hfaithful
  have hd := divRem1RtProg_denote (update := divUpdate) divUpdate_eq V
  have hf := divRtProg_val_rem V hrs htop h0 hd2 hv hn
  have heq : JLoopBodyN.denote ⟨(divCount.lookup V).toNat, divUpdate⟩
        (Expr.lookupArgs divInvs V) (divInit.lookup V)
      = divFold (upVar.lookup V) (dVar.lookup V)
          ((nVar.lookup V).toNat - 1) RS (nVar.lookup V).toNat (divInit.lookup V) :=
    Option.some.inj (hd.symm.trans hf)
  exact ⟨t, hrun, hdec.trans (congrArg some heq)⟩

/-- **The machine execution computes the Euclidean quotient/remainder fold.**
    Given the array-accumulator backend-faithfulness conclusion at `divUpdate` —
    the emitted machine loop `body` run by `lsemFuelMemL` from a start state `s`
    decodes at the accumulator slot `arrSlot` to the source fold
    `JLoopBodyN.denote ⟨n, divUpdate⟩` (exactly the shape
    `loopMemArr_export_faithful_denote` produces) — and the normalisation
    preconditions of `divRtProg_val` (divisor `d` with bit 63 set, correct
    reciprocal `dinv`, cleared seed cell `RS`, at least one trip, top limb index
    below `RS`), the halt state's output array decodes to the exact Euclidean
    fold `divFold` of the argument registers. The zero-seed instance of
    `divrem_emitted_machine_val_rem`. -/
theorem divrem_emitted_machine_val
    (V : Ctxt.Valuation Gouter)
    (hrs : RS < NR)
    (htop : (nVar.lookup V).toNat - 1 < RS)
    (h0 : memGetDyn (divInit.lookup V) RS = 0)
    (hd2 : 2 ^ 63 ≤ (dVar.lookup V).toNat)
    (hv : (dinvVar.lookup V).toNat = (2 ^ 128 - 1) / (dVar.lookup V).toNat - 2 ^ 64)
    (hn : 1 ≤ (nVar.lookup V).toNat)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (arrSlot : String) (s : LstatePM)
    (hfaithful : ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((divCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NR
            = some (JLoopBodyN.denote ⟨(divCount.lookup V).toNat, divUpdate⟩
                (Expr.lookupArgs divInvs V) (divInit.lookup V))) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((divCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NR
            = some (divFold (upVar.lookup V) (dVar.lookup V)
                ((nVar.lookup V).toNat - 1) RS (nVar.lookup V).toNat (divInit.lookup V)) :=
  divrem_emitted_machine_val_rem V hrs htop
    (by rw [h0]; exact lt_of_lt_of_le (by simp) hd2) hd2 hv hn fn top nReg body arrSlot s
    hfaithful

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1LsemTie
