/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

/-!
# The machine-execution → integer-spec tie for the emitted `mpn_mul_1` loop

`MpnMul1FrontDenote.mul1RtProg_val` ends the front-side chain at `ComL.denote`:
the emitted runtime-trip program's denotation recombines via `bignumVal` to
`up[0..n) * v`. `JasminLsemMemSourceTieUncond.loopMemArr_export_faithful_denote`
is the general backend-faithfulness statement for an **array-accumulator**
counter loop: the emitted machine loop's execution (`lsemFuelMemL` over the
`LinstrRM` model) decodes at the accumulator array slot to
`JLoopBodyN.denote ⟨m, update⟩` — the source loop's `m`-fold denotation.

The `mpn_mul_1` accumulator is the output array `rp` (`accCTy = .memref NR`,
mapped to `mapTy (.memref NR) = .stackArr 64 NR = AR`), so the array variant is
the type-correct faithfulness form, and `mul1Update` is a legal `update`
argument to it.

This module composes the two: given the array-faithfulness conclusion at
`mul1Update` (the machine run decodes to the source fold), the emitted
`mpn_mul_1` loop's machine execution produces output cells that recombine to
`up[0..n) * v`. The faithfulness conclusion is taken as a hypothesis of the
shape `loopMemArr_export_faithful_denote` produces; its discharge for the
`mpn_mul_1` body is the remaining open obligation (a per-trip array simulation
for a general array-returning update chain — the array-return analogue of the
scalar `comToLprog_lsemMem`, which decodes only at a register).

## Main results

* `mul1_forLoopNRt_denote_eq_fold` — the front node's denotation
  (`ComL.forLoopNRt mul1Update … (.ret .here)`, the `loopMemArr_export_*_comL`
  spelling) equals the word-model fold `mul1Fold`.
* `mul1_emitted_machine_val` — the full chain: the array-faithfulness
  conclusion at `mul1Update` composed with `mul1RtProg_val`, giving output
  cells that `bignumVal`-recombine to `up[0..n) * v`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1LsemTie

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM comL_forLoopNRt_ret_denote_acc)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote

/-- The word-model fold reached by both spellings of the emitted loop's
    denotation: the front node's `ComL.denote` and `mul1RtProgOpt`'s. Both
    equal `JLoopBodyN.denote ⟨n, mul1Update⟩` of the looked-up arguments, hence
    `mul1Fold`. -/
theorem mul1_forLoopNRt_denote_eq_fold (V : Ctxt.Valuation Gouter) :
    (ComL.forLoopNRt mul1Update mul1Count mul1Init mul1Invs (.ret .here)).denote V
      = mul1Fold (upVar.lookup V) (vVar.lookup V)
          (mul1Count.lookup V).toNat (mul1Init.lookup V) := by
  have hd := mul1RtProg_denote (update := mul1Update) mul1Update_eq V
  have hf := mul1RtProg_fold V
  exact (comL_forLoopNRt_ret_denote_acc mul1Update mul1Count mul1Init mul1Invs V).trans
    (Option.some.inj (hd.symm.trans hf))

/-- **The machine execution computes the product.** Given the array-accumulator
    backend-faithfulness conclusion at `mul1Update` — the emitted machine loop
    `body` run by `lsemFuelMemL` from a start state `s` decodes at the
    accumulator slot `arrSlot` to the source fold
    `JLoopBodyN.denote ⟨n, mul1Update⟩` (exactly the shape
    `loopMemArr_export_faithful_denote` produces) — the halt state's array cells
    `0, …, n` recombine via `bignumVal` to `up[0..n) * v`. The composition of
    the backend-faithfulness tie with `mul1RtProg_val`. -/
theorem mul1_emitted_machine_val
    (V : Ctxt.Valuation Gouter)
    (hn : (mul1Count.lookup V).toNat < NR)
    (h0 : memGetDyn (mul1Init.lookup V) 0 = 0)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (arrSlot : String) (s : LstatePM)
    (hfaithful : ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((mul1Count.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NR
            = some (JLoopBodyN.denote ⟨(mul1Count.lookup V).toNat, mul1Update⟩
                (Expr.lookupArgs mul1Invs V) (mul1Init.lookup V))) :
    ∃ (t : LstatePM) (out : Fin NR → BitVec 64),
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((mul1Count.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NR = some out
        ∧ bignumVal (cells out ((mul1Count.lookup V).toNat + 1))
            = bignumVal (cells (upVar.lookup V) (mul1Count.lookup V).toNat)
                * (vVar.lookup V).toNat := by
  obtain ⟨t, hrun, hdec⟩ := hfaithful
  have hd := mul1RtProg_denote (update := mul1Update) mul1Update_eq V
  have hf := mul1RtProg_fold V
  have heq : JLoopBodyN.denote ⟨(mul1Count.lookup V).toNat, mul1Update⟩
        (Expr.lookupArgs mul1Invs V) (mul1Init.lookup V)
      = mul1Fold (upVar.lookup V) (vVar.lookup V)
          (mul1Count.lookup V).toNat (mul1Init.lookup V) :=
    Option.some.inj (hd.symm.trans hf)
  refine ⟨t, _, hrun, hdec, ?_⟩
  rw [heq]
  exact mul1Fold_val_zero (upVar.lookup V) (vVar.lookup V) (mul1Init.lookup V)
    (mul1Count.lookup V).toNat hn h0

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1LsemTie
