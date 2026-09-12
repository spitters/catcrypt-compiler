/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

/-!
# The machine-execution → source-semantics tie for the emitted `mpn_and_n`, `mpn_ior_n` and `mpn_xor_n` loops

`MpnLogicalFrontDenote.andRtProg_fold` / `iorRtProg_fold` / `xorRtProg_fold` end
the front-side chain at `ComL.denote`: the emitted runtime-trip programs'
denotations are the elementwise word-model fold `logicFold` at the conjunction,
disjunction and exclusive-or combiners.
`JasminLsemMemSourceTieUncond.comL_forLoopNRt_ret_denote_acc` unfolds the front
node `ComL.forLoopNRt`'s denotation to the source loop's `JLoopBodyN.denote`.

The accumulator is the output array `rp` (`accCTy = .memref NL`, mapped to
`.stackArr 64 NL = AL`), so `andUpdate` / `iorUpdate` / `xorUpdate` are legal
array-accumulator updates.

This module composes: given the array-accumulator backend-faithfulness
conclusion at each body — the emitted machine loop's execution decodes at the
accumulator slot to `JLoopBodyN.denote ⟨n, update⟩`, the shape
`loopMemArr_export_faithful_denote` produces — the halt state's output cells are
the elementwise `List.zipWith` of the two source arrays. The faithfulness
conclusion is taken as a hypothesis here; its unconditional discharge for these
bodies is completed in `JasminLsemMemArrTripLogical`.

## Main results

* `and_forLoopNRt_denote_eq_fold` / `ior_forLoopNRt_denote_eq_fold` /
  `xor_forLoopNRt_denote_eq_fold` — the front node's denotation
  (`ComL.forLoopNRt update … (.ret .here)`) equals the word-model fold
  `logicFold`.
* `and_emitted_machine_val` — the full chain for `mpn_and_n`: the array-
  faithfulness conclusion at `andUpdate` composed with `andFold_cells`, giving
  output cells that are the elementwise conjunction of the two source arrays.
* `ior_emitted_machine_val` / `xor_emitted_machine_val` — the same for
  `mpn_ior_n` and `mpn_xor_n`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalLsemTie

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM comL_forLoopNRt_ret_denote_acc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote

/-! ## 1. The front nodes denote the word-model fold -/

/-- The word-model fold reached by the emitted `mpn_and_n` loop's denotation:
    the front node's `ComL.denote` equals `logicFold` at the conjunction
    combiner, the trip count the runtime `n`. -/
theorem and_forLoopNRt_denote_eq_fold (V : Ctxt.Valuation Gouter) :
    (ComL.forLoopNRt andUpdate logicCount logicInit logicInvs (.ret .here)).denote V
      = logicFold (fun x y => x &&& y) (apVar.lookup V) (bpVar.lookup V)
          (logicCount.lookup V).toNat (logicInit.lookup V) := by
  have hd := logicRtProg_denote andSE andUpdate_eq V
  have hf := andRtProg_fold V
  exact (comL_forLoopNRt_ret_denote_acc andUpdate logicCount logicInit logicInvs V).trans
    (Option.some.inj (hd.symm.trans hf))

/-- The word-model fold reached by the emitted `mpn_ior_n` loop's denotation:
    the front node's `ComL.denote` equals `logicFold` at the disjunction
    combiner. -/
theorem ior_forLoopNRt_denote_eq_fold (V : Ctxt.Valuation Gouter) :
    (ComL.forLoopNRt iorUpdate logicCount logicInit logicInvs (.ret .here)).denote V
      = logicFold (fun x y => x ||| y) (apVar.lookup V) (bpVar.lookup V)
          (logicCount.lookup V).toNat (logicInit.lookup V) := by
  have hd := logicRtProg_denote iorSE iorUpdate_eq V
  have hf := iorRtProg_fold V
  exact (comL_forLoopNRt_ret_denote_acc iorUpdate logicCount logicInit logicInvs V).trans
    (Option.some.inj (hd.symm.trans hf))

/-- The word-model fold reached by the emitted `mpn_xor_n` loop's denotation:
    the front node's `ComL.denote` equals `logicFold` at the exclusive-or
    combiner. -/
theorem xor_forLoopNRt_denote_eq_fold (V : Ctxt.Valuation Gouter) :
    (ComL.forLoopNRt xorUpdate logicCount logicInit logicInvs (.ret .here)).denote V
      = logicFold (fun x y => x ^^^ y) (apVar.lookup V) (bpVar.lookup V)
          (logicCount.lookup V).toNat (logicInit.lookup V) := by
  have hd := logicRtProg_denote xorSE xorUpdate_eq V
  have hf := xorRtProg_fold V
  exact (comL_forLoopNRt_ret_denote_acc xorUpdate logicCount logicInit logicInvs V).trans
    (Option.some.inj (hd.symm.trans hf))

/-! ## 2. The machine execution computes the elementwise operation -/

/-- **The machine execution computes the elementwise conjunction.** Given the
    array-accumulator backend-faithfulness conclusion at `andUpdate` — the
    emitted machine loop `body` run by `lsemFuelMemL` from a start state `s`
    decodes at the accumulator slot `arrSlot` to the source fold
    `JLoopBodyN.denote ⟨n, andUpdate⟩` (the shape
    `loopMemArr_export_faithful_denote` produces) — the halt state's first `n`
    output cells are the elementwise `List.zipWith` conjunction of the two source
    arrays. The composition of the backend-faithfulness tie with
    `andFold_cells`. -/
theorem and_emitted_machine_val
    (V : Ctxt.Valuation Gouter)
    (hn : (logicCount.lookup V).toNat ≤ NL)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (arrSlot : String) (s : LstatePM)
    (hfaithful : ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((logicCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NL
            = some (JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, andUpdate⟩
                (Expr.lookupArgs logicInvs V) (logicInit.lookup V))) :
    ∃ (t : LstatePM) (out : Fin NL → BitVec 64),
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((logicCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NL = some out
        ∧ cells out (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x &&& y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) := by
  obtain ⟨t, hrun, hdec⟩ := hfaithful
  have hd := logicRtProg_denote andSE andUpdate_eq V
  have hf := andRtProg_fold V
  have heq : JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, andUpdate⟩
        (Expr.lookupArgs logicInvs V) (logicInit.lookup V)
      = logicFold (fun x y => x &&& y) (apVar.lookup V) (bpVar.lookup V)
          (logicCount.lookup V).toNat (logicInit.lookup V) :=
    Option.some.inj (hd.symm.trans hf)
  refine ⟨t, _, hrun, hdec, ?_⟩
  rw [heq]
  exact andFold_cells (apVar.lookup V) (bpVar.lookup V) (logicInit.lookup V)
    (logicCount.lookup V).toNat hn

/-- **The machine execution computes the elementwise disjunction.** The
    disjunction analogue of `and_emitted_machine_val`, composed with
    `iorFold_cells`. -/
theorem ior_emitted_machine_val
    (V : Ctxt.Valuation Gouter)
    (hn : (logicCount.lookup V).toNat ≤ NL)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (arrSlot : String) (s : LstatePM)
    (hfaithful : ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((logicCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NL
            = some (JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, iorUpdate⟩
                (Expr.lookupArgs logicInvs V) (logicInit.lookup V))) :
    ∃ (t : LstatePM) (out : Fin NL → BitVec 64),
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((logicCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NL = some out
        ∧ cells out (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x ||| y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) := by
  obtain ⟨t, hrun, hdec⟩ := hfaithful
  have hd := logicRtProg_denote iorSE iorUpdate_eq V
  have hf := iorRtProg_fold V
  have heq : JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, iorUpdate⟩
        (Expr.lookupArgs logicInvs V) (logicInit.lookup V)
      = logicFold (fun x y => x ||| y) (apVar.lookup V) (bpVar.lookup V)
          (logicCount.lookup V).toNat (logicInit.lookup V) :=
    Option.some.inj (hd.symm.trans hf)
  refine ⟨t, _, hrun, hdec, ?_⟩
  rw [heq]
  exact iorFold_cells (apVar.lookup V) (bpVar.lookup V) (logicInit.lookup V)
    (logicCount.lookup V).toNat hn

/-- **The machine execution computes the elementwise exclusive-or.** The
    exclusive-or analogue of `and_emitted_machine_val`, composed with
    `xorFold_cells`. -/
theorem xor_emitted_machine_val
    (V : Ctxt.Valuation Gouter)
    (hn : (logicCount.lookup V).toNat ≤ NL)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (arrSlot : String) (s : LstatePM)
    (hfaithful : ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((logicCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NL
            = some (JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, xorUpdate⟩
                (Expr.lookupArgs logicInvs V) (logicInit.lookup V))) :
    ∃ (t : LstatePM) (out : Fin NL → BitVec 64),
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((logicCount.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot 64 NL = some out
        ∧ cells out (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x ^^^ y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) := by
  obtain ⟨t, hrun, hdec⟩ := hfaithful
  have hd := logicRtProg_denote xorSE xorUpdate_eq V
  have hf := xorRtProg_fold V
  have heq : JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, xorUpdate⟩
        (Expr.lookupArgs logicInvs V) (logicInit.lookup V)
      = logicFold (fun x y => x ^^^ y) (apVar.lookup V) (bpVar.lookup V)
          (logicCount.lookup V).toNat (logicInit.lookup V) :=
    Option.some.inj (hd.symm.trans hf)
  refine ⟨t, _, hrun, hdec, ?_⟩
  rw [heq]
  exact xorFold_cells (apVar.lookup V) (bpVar.lookup V) (logicInit.lookup V)
    (logicCount.lookup V).toNat hn

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalLsemTie
