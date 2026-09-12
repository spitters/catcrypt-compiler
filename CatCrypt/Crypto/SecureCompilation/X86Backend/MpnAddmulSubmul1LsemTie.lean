/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontDenote
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

/-!
# The machine-execution → integer-spec tie for the emitted `mpn_addmul_1` and `mpn_submul_1` loops

`MpnAddmulSubmul1FrontDenote.addmulRtProg_fold` / `submulRtProg_fold` end the
front-side chain at `ComL.denote`: the emitted runtime-trip programs' denotations
are the word-model fold `accFold addmulLimb` / `accFold submulLimb`.
`JasminLsemMemSourceTieUncond.loopMemArr_export_faithful_denote` is the general
backend-faithfulness statement for an **array-accumulator** counter loop: the
emitted machine loop's execution decodes at the accumulator array slot to
`JLoopBodyN.denote ⟨m, update⟩` — the source loop's `m`-fold denotation.

The multiply-accumulate accumulator is the output array `rp` (`accCTy = .memref NR`,
mapped to `mapTy (.memref NR) = .stackArr 64 NR = AR`), so the array variant is
the type-correct faithfulness form and `addmulUpdate` / `submulUpdate` are legal
`update` arguments to it.

This module composes the two: given the array-faithfulness conclusion at
`addmulUpdate` / `submulUpdate`, the emitted machine execution produces output
cells that recombine via `bignumVal` to the multiply-accumulate / multiply-
subtract contract. The faithfulness conclusion is taken as a hypothesis of the
shape `loopMemArr_export_faithful_denote` produces; its unconditional discharge
for these bodies is completed in `JasminLsemMemArrTripAddmul`.

## Main results

* `addmul_forLoopNRt_denote_eq_fold` / `submul_forLoopNRt_denote_eq_fold` — the
  front node's denotation (`ComL.forLoopNRt update … (.ret .here)`) equals the
  word-model fold `accFold`.
* `addmul_emitted_machine_val` — the full chain for `mpn_addmul_1`: the array-
  faithfulness conclusion at `addmulUpdate` composed with `addmulFold_val_zero`,
  giving output cells that `bignumVal`-recombine to the multiply-accumulate
  contract.
* `submul_emitted_machine_val` — the same for `mpn_submul_1`, at the multiply-
  subtract contract.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1LsemTie

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM comL_forLoopNRt_ret_denote_acc)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells NR AR AU r64 Gouter)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1FrontDenote

/-! ## 1. The front node denotes the word-model fold -/

/-- The word-model fold reached by the emitted `mpn_addmul_1` loop's denotation:
    the front node's `ComL.denote` equals `accFold addmulLimb` of the looked-up
    arguments, the carry cell and the trip count both the runtime `n`. -/
theorem addmul_forLoopNRt_denote_eq_fold (V : Ctxt.Valuation Gouter) :
    (ComL.forLoopNRt addmulUpdate accCount accInit accInvs (.ret .here)).denote V
      = accFold addmulLimb (upVarA.lookup V) (vVarA.lookup V)
          (accCount.lookup V).toNat (accCount.lookup V).toNat (accInit.lookup V) := by
  have hd := addmulRtProg_denote (update := addmulUpdate) addmulUpdate_eq V
  have hf := addmulRtProg_fold V
  exact (comL_forLoopNRt_ret_denote_acc addmulUpdate accCount accInit accInvs V).trans
    (Option.some.inj (hd.symm.trans hf))

/-- The word-model fold reached by the emitted `mpn_submul_1` loop's denotation:
    the front node's `ComL.denote` equals `accFold submulLimb`. -/
theorem submul_forLoopNRt_denote_eq_fold (V : Ctxt.Valuation Gouter) :
    (ComL.forLoopNRt submulUpdate accCount accInit accInvs (.ret .here)).denote V
      = accFold submulLimb (upVarA.lookup V) (vVarA.lookup V)
          (accCount.lookup V).toNat (accCount.lookup V).toNat (accInit.lookup V) := by
  have hd := submulRtProg_denote (update := submulUpdate) submulUpdate_eq V
  have hf := submulRtProg_fold V
  exact (comL_forLoopNRt_ret_denote_acc submulUpdate accCount accInit accInvs V).trans
    (Option.some.inj (hd.symm.trans hf))

/-! ## 2. The machine execution computes the multiply-accumulate / multiply-subtract -/

/-- **The machine execution computes the multiply-accumulate.** Given the array-
    accumulator backend-faithfulness conclusion at `addmulUpdate` — the emitted
    machine loop `body` run by `lsemFuelMemL` from a start state `s` decodes at
    the accumulator slot `arrSlot` to the source fold
    `JLoopBodyN.denote ⟨n, addmulUpdate⟩` (exactly the shape
    `loopMemArr_export_faithful_denote` produces) — the halt state's array cells
    `0, …, n-1` and the carry cell `n` recombine via `bignumVal` to
    `rp[0..n) + up[0..n) · v`. The composition of the backend-faithfulness tie
    with `addmulFold_val_zero`. -/
theorem addmul_emitted_machine_val
    (V : Ctxt.Valuation Gouter)
    (hn : (accCount.lookup V).toNat < NR)
    (h0 : memGetDyn (accInit.lookup V) (accCount.lookup V).toNat = 0)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (arrSlot : String) (s : LstatePM)
    (hfaithful : ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((accCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NR
            = some (JLoopBodyN.denote ⟨(accCount.lookup V).toNat, addmulUpdate⟩
                (Expr.lookupArgs accInvs V) (accInit.lookup V))) :
    ∃ (t : LstatePM) (out : Fin NR → BitVec 64),
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((accCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NR = some out
        ∧ (bignumVal (cells out (accCount.lookup V).toNat) : ℤ)
              + (2 ^ 64) ^ (accCount.lookup V).toNat
                  * (memGetDyn out (accCount.lookup V).toNat).toNat
            = (bignumVal (cells (accInit.lookup V) (accCount.lookup V).toNat) : ℤ)
              + (bignumVal (cells (upVarA.lookup V) (accCount.lookup V).toNat) : ℤ)
                  * (vVarA.lookup V).toNat := by
  obtain ⟨t, hrun, hdec⟩ := hfaithful
  have hd := addmulRtProg_denote (update := addmulUpdate) addmulUpdate_eq V
  have hf := addmulRtProg_fold V
  have heq : JLoopBodyN.denote ⟨(accCount.lookup V).toNat, addmulUpdate⟩
        (Expr.lookupArgs accInvs V) (accInit.lookup V)
      = accFold addmulLimb (upVarA.lookup V) (vVarA.lookup V)
          (accCount.lookup V).toNat (accCount.lookup V).toNat (accInit.lookup V) :=
    Option.some.inj (hd.symm.trans hf)
  refine ⟨t, _, hrun, hdec, ?_⟩
  rw [heq]
  exact addmulFold_val_zero (upVarA.lookup V) (vVarA.lookup V) (accCount.lookup V).toNat hn
    (accInit.lookup V) (accCount.lookup V).toNat (le_refl _) h0

/-- **The machine execution computes the multiply-subtract.** The instance of the
    composition at the multiply-subtract kernel: the halt state's array cells and
    the borrow cell recombine via `bignumVal` to the `mpn_submul_1` contract
    `rp[0..n) + up[0..n) · v = rp'[0..n) + 2^(64n) · borrow`. -/
theorem submul_emitted_machine_val
    (V : Ctxt.Valuation Gouter)
    (hn : (accCount.lookup V).toNat < NR)
    (h0 : memGetDyn (accInit.lookup V) (accCount.lookup V).toNat = 0)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (arrSlot : String) (s : LstatePM)
    (hfaithful : ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((accCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NR
            = some (JLoopBodyN.denote ⟨(accCount.lookup V).toNat, submulUpdate⟩
                (Expr.lookupArgs accInvs V) (accInit.lookup V))) :
    ∃ (t : LstatePM) (out : Fin NR → BitVec 64),
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((accCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NR = some out
        ∧ (bignumVal (cells out (accCount.lookup V).toNat) : ℤ)
              + (bignumVal (cells (upVarA.lookup V) (accCount.lookup V).toNat) : ℤ)
                  * (vVarA.lookup V).toNat
            = (bignumVal (cells (accInit.lookup V) (accCount.lookup V).toNat) : ℤ)
              + (2 ^ 64) ^ (accCount.lookup V).toNat
                  * (memGetDyn out (accCount.lookup V).toNat).toNat := by
  obtain ⟨t, hrun, hdec⟩ := hfaithful
  have hd := submulRtProg_denote (update := submulUpdate) submulUpdate_eq V
  have hf := submulRtProg_fold V
  have heq : JLoopBodyN.denote ⟨(accCount.lookup V).toNat, submulUpdate⟩
        (Expr.lookupArgs accInvs V) (accInit.lookup V)
      = accFold submulLimb (upVarA.lookup V) (vVarA.lookup V)
          (accCount.lookup V).toNat (accCount.lookup V).toNat (accInit.lookup V) :=
    Option.some.inj (hd.symm.trans hf)
  refine ⟨t, _, hrun, hdec, ?_⟩
  rw [heq]
  exact submulFold_val_zero (upVarA.lookup V) (vVarA.lookup V) (accCount.lookup V).toNat hn
    (accInit.lookup V) (accCount.lookup V).toNat (le_refl _) h0

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddmulSubmul1LsemTie
