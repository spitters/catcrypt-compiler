/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontDenote
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

/-!
# The machine-execution → integer-spec tie for the emitted `mpn_cmp` loop

`MpnCmpFrontDenote.cmpRtProg_fold` ends the front-side chain at `ComL.denote`:
the emitted runtime-trip program's denotation is the memref-carrier fold
`cmpFold`. `JasminLsemMemSourceTieUncond.loopMemArr_export_faithful_denote` is
the general backend-faithfulness statement for an **array-accumulator** counter
loop: the emitted machine loop's execution decodes at the accumulator array slot
to `JLoopBodyN.denote ⟨m, update⟩` — the source loop's `m`-fold denotation.

The comparison accumulator is the one-word output array `rp`
(`accCTy = .memref NR`, mapped to `mapTy (.memref NR) = .stackArr 64 NR = AR`), so
the array variant is the type-correct faithfulness form and `cmpUpdate` is a legal
`update` argument to it.

This module composes the two: given the array-faithfulness conclusion at
`cmpUpdate`, the emitted machine execution produces an output array whose result
cell holds the comparison sign of the two operands. The faithfulness conclusion
is taken as a hypothesis of the shape `loopMemArr_export_faithful_denote`
produces; its unconditional discharge for this body is completed in
`JasminLsemMemArrTripCmp`.

## Main results

* `cmp_emitted_machine_val` — the full chain for `mpn_cmp`: the array-faithfulness
  conclusion at `cmpUpdate` composed with `cmpFold_val_full`, giving an output
  array whose cell `0` holds `cmpSign` of the two operands' `bignumVal`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpLsemTie

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit (segCells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontDenote

/-! ## The machine execution computes the comparison sign -/

/-- **The machine execution computes the comparison sign.** Given the array-
    accumulator backend-faithfulness conclusion at `cmpUpdate` — the emitted
    machine loop `body` run by `lsemFuelMemL` from a start state `s` decodes at
    the accumulator slot `arrSlot` to the source fold
    `JLoopBodyN.denote ⟨n, cmpUpdate⟩` (exactly the shape
    `loopMemArr_export_faithful_denote` produces) — the halt state's output array
    holds in cell `0` the comparison sign `cmpSign` of the two operands'
    `bignumVal` over the limbs `0, …, n - 1`. The composition of the backend-
    faithfulness tie with `cmpFold_val_full`. -/
theorem cmp_emitted_machine_val
    (V : Ctxt.Valuation Gouter)
    (hn : 0 < (cmpCount.lookup V).toNat)
    (h0 : memGetDyn (cmpInit.lookup V) 0 = 0)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (arrSlot : String) (s : LstatePM)
    (hfaithful : ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((cmpCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NR
            = some (JLoopBodyN.denote ⟨(cmpCount.lookup V).toNat, cmpUpdate⟩
                (Expr.lookupArgs cmpInvs V) (cmpInit.lookup V))) :
    ∃ (t : LstatePM) (out : Fin NR → BitVec 64),
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((cmpCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NR = some out
        ∧ memGetDyn out 0
            = cmpSign (bignumVal (segCells (apVar.lookup V) 0 (cmpCount.lookup V).toNat))
                (bignumVal (segCells (bpVar.lookup V) 0 (cmpCount.lookup V).toNat)) := by
  obtain ⟨t, hrun, hdec⟩ := hfaithful
  have hd := cmpRtProg_denote (update := cmpUpdate) cmpUpdate_eq V
  have hf := cmpRtProg_fold V
  have heq : JLoopBodyN.denote ⟨(cmpCount.lookup V).toNat, cmpUpdate⟩
        (Expr.lookupArgs cmpInvs V) (cmpInit.lookup V)
      = cmpFold (apVar.lookup V) (bpVar.lookup V)
          ((cmpCount.lookup V).toNat - 1) (cmpCount.lookup V).toNat (cmpInit.lookup V) :=
    Option.some.inj (hd.symm.trans hf)
  refine ⟨t, _, hrun, hdec, ?_⟩
  rw [heq]
  have htop : (cmpCount.lookup V).toNat - 1 + 1 = (cmpCount.lookup V).toNat := by omega
  have h := cmpFold_val_full (apVar.lookup V) (bpVar.lookup V)
    ((cmpCount.lookup V).toNat - 1) (cmpInit.lookup V) (by decide) h0
  rw [htop] at h
  exact h

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpLsemTie
