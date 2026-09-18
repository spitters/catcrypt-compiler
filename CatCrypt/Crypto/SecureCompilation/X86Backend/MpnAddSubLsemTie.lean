/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

/-!
# The machine-execution tie for the emitted `mpn_add_n` / `mpn_sub_n` loops

The carry family's front-compiled limb bodies `addUpdate` / `subUpdate` return a
register (the carry, the borrow), so the scalar-accumulator export theorem
`JasminLsemMemSourceTieUncond.loopMem_export_faithful_denote_uncond` applies once
each body is a member of the stack-memory fragment `ScalarMemN`. This module
proves the two memberships and composes the export theorem with
`MpnAddSubFrontDenote`'s carry (borrow) fold, giving the value of the
accumulator register at the machine loop's halt state, with only the counter
schedule, the seed and the counter-name hygiene as hypotheses.

## Scope

The machine model `lsemStraightMem` over the chain `straightOpsMem` lowers a
`stackStore` binding to a store into a fresh array slot `regName d`, and the
per-trip agreement `StoreAgreesM … (tripValMN invs t acc)` pins the invariant
arrays to their entry values. The output array's argument slot is therefore not
written by the modelled loop, and the theorems here observe the accumulator
register only. The output limbs are stated at the source level by
`MpnAddSubFrontDenote.addLimbBody_run` / `subLimbBody_run`.

## Main results

* `addUpdate_scalarMemN` / `subUpdate_scalarMemN` — the front-compiled limb
  bodies are `ScalarMemN` members.
* `addUpdate_denote_eq` / `subUpdate_denote_eq` — the updates' `n`-fold loop
  denotations are the carry (borrow) folds.
* `add_emitted_machine_carry` / `sub_emitted_machine_borrow` — the machine
  execution of the emitted loop halts with the accumulator register holding the
  carry `(bignumVal a[0..n) + bignumVal b[0..n) + c₀) / 2^(64n)`, respectively
  the borrow, `1` exactly when `bignumVal a[0..n) < bignumVal b[0..n) + bw₀`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubLsemTie

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
  (rolledForLoopNRt_denote)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype
  (N AN vmBody addBodyLowCT)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
  (ΓouterCarry subBodyLowCT vmBodySub)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote

/-! ## 1. Fragment membership -/

/-- The front-compiled `mpn_add_n` limb body is a `ScalarMemN` member: a chain of
    register heads, two `stackLoad`s and one `stackStore`, returning a register. -/
theorem addUpdate_scalarMemN : ScalarMemN addUpdate := by
  unfold addUpdate
  repeat first
    | exact ScalarMemN.ret _
    | refine ScalarMemN.var _ rfl _ ?_
    | refine ScalarMemN.const _ (by decide) rfl _ ?_
    | refine ScalarMemN.shl (by decide) rfl _ ?_
    | refine ScalarMemN.shr (by decide) rfl _ ?_
    | refine ScalarMemN.sel rfl _ ?_
    | refine ScalarMemN.load rfl _ ?_
    | refine ScalarMemN.store rfl _ ?_

/-- The front-compiled `mpn_sub_n` limb body is a `ScalarMemN` member. -/
theorem subUpdate_scalarMemN : ScalarMemN subUpdate := by
  unfold subUpdate
  repeat first
    | exact ScalarMemN.ret _
    | refine ScalarMemN.var _ rfl _ ?_
    | refine ScalarMemN.const _ (by decide) rfl _ ?_
    | refine ScalarMemN.shl (by decide) rfl _ ?_
    | refine ScalarMemN.shr (by decide) rfl _ ?_
    | refine ScalarMemN.sel rfl _ ?_
    | refine ScalarMemN.load rfl _ ?_
    | refine ScalarMemN.store rfl _ ?_

/-! ## 2. The loop denotation at the update -/

/-- The loop invariants `[a, b, out]` of the carry-family loop node. -/
def carryInvs : HVector (fun ty => Ctxt.Var ΓouterCarry ty) [AN, AN, AN] :=
  .cons aVar (.cons bVar (.cons outVar .nil))

/-- The `add` update's `n`-fold loop denotation is the carry fold. -/
theorem addUpdate_denote_eq (V : Ctxt.Valuation ΓouterCarry) :
    JLoopBodyN.denote ⟨(nVar.lookup V).toNat, addUpdate⟩ (Expr.lookupArgs carryInvs V)
        (seedVar.lookup V)
      = addCarryFold (aVar.lookup V) (bVar.lookup V) (nVar.lookup V).toNat
          (seedVar.lookup V) :=
  Option.some.inj ((rolledForLoopNRt_denote (Γouter := ΓouterCarry) (accCTy := .sword 64)
    (invCTys := [.memref N, .memref N, .memref N]) vmBody "cy" addBodyLowCT
    (.there .here) .here carryInvs addUpdate_eq V).symm.trans (addRtProg_fold V))

/-- The `sub` update's `n`-fold loop denotation is the borrow fold. -/
theorem subUpdate_denote_eq (V : Ctxt.Valuation ΓouterCarry) :
    JLoopBodyN.denote ⟨(nVar.lookup V).toNat, subUpdate⟩ (Expr.lookupArgs carryInvs V)
        (seedVar.lookup V)
      = subBorrowFold (aVar.lookup V) (bVar.lookup V) (nVar.lookup V).toNat
          (seedVar.lookup V) :=
  Option.some.inj ((rolledForLoopNRt_denote (Γouter := ΓouterCarry) (accCTy := .sword 64)
    (invCTys := [.memref N, .memref N, .memref N]) vmBodySub "bw" subBodyLowCT
    (.there .here) .here carryInvs subUpdate_eq V).symm.trans (subRtProg_fold V))

/-! ## 3. The machine-level carry and borrow -/

/-- **The emitted `mpn_add_n` loop's machine run returns the carry-out.** For a
    limb count `1 ≤ n ≤ N` and a seed in `{0, 1}`, the emitted `chain ++ writeback`
    loop run under `lsemFuelMemL` from a start state with the counter schedule,
    the seed agreement and the counter-name hygiene halts with the accumulator
    register holding `c ∈ {0, 1}`,
    `c = (bignumVal a[0..n) + bignumVal b[0..n) + seed) / 2^(64n)`. -/
theorem add_emitted_machine_carry
    (V : Ctxt.Valuation ΓouterCarry)
    (hn : (nVar.lookup V).toNat ≤ N) (h0 : (seedVar.lookup V).toNat ≤ 1)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AN, AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN, AN] : Ctxt jasminDialect).length + 2) s.base
      (tripValMN (Expr.lookupArgs carryInvs V) 0 (seedVar.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (nVar.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyFullMN addUpdate nReg)
      ((nVar.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyFullMN addUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyFullMN addUpdate nReg)
      (nVar.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (nVar.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyFullMN addUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ (t : LstatePM) (c : BitVec 64),
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyFullMN addUpdate nReg)))
          ((nVar.lookup V).toNat * ((loopBodyFullMN addUpdate nReg).length + 1)) s
            = some t
        ∧ decodeM t.base (accRegMN [AN, AN, AN]) 64 = some c
        ∧ c.toNat = (bignumVal (cells (aVar.lookup V) (nVar.lookup V).toNat)
              + bignumVal (cells (bVar.lookup V) (nVar.lookup V).toNat)
              + (seedVar.lookup V).toNat) / (2 ^ 64) ^ (nVar.lookup V).toNat
        ∧ c.toNat ≤ 1 := by
  obtain ⟨t, hrun, hdec⟩ := loopMem_export_faithful_denote_uncond addUpdate
    addUpdate_scalarMemN (Expr.lookupArgs carryInvs V) fn top nReg hna hnr s hfn hpc
    (seedVar.lookup V) hseed hn0 _ hm bprev blast bfin hprev hlast hbfin htaken hhalt
  rw [addUpdate_denote_eq] at hdec
  exact ⟨t, _, hrun, hdec,
    addCarryFold_val N (aVar.lookup V) (bVar.lookup V) (seedVar.lookup V) h0 _ hn⟩

/-- **The emitted `mpn_sub_n` loop's machine run returns the borrow-out.** As
    `add_emitted_machine_carry`: the accumulator register at the halt state is
    `1` exactly when `bignumVal a[0..n) < bignumVal b[0..n) + seed`, and `0`
    otherwise. -/
theorem sub_emitted_machine_borrow
    (V : Ctxt.Valuation ΓouterCarry)
    (hn : (nVar.lookup V).toNat ≤ N) (h0 : (seedVar.lookup V).toNat ≤ 1)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AN, AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN, AN] : Ctxt jasminDialect).length + 2) s.base
      (tripValMN (Expr.lookupArgs carryInvs V) 0 (seedVar.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (nVar.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyFullMN subUpdate nReg)
      ((nVar.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyFullMN subUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyFullMN subUpdate nReg)
      (nVar.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (nVar.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyFullMN subUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ (t : LstatePM) (bw : BitVec 64),
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyFullMN subUpdate nReg)))
          ((nVar.lookup V).toNat * ((loopBodyFullMN subUpdate nReg).length + 1)) s
            = some t
        ∧ decodeM t.base (accRegMN [AN, AN, AN]) 64 = some bw
        ∧ bw.toNat = if bignumVal (cells (aVar.lookup V) (nVar.lookup V).toNat)
              < bignumVal (cells (bVar.lookup V) (nVar.lookup V).toNat)
                + (seedVar.lookup V).toNat then 1 else 0 := by
  obtain ⟨t, hrun, hdec⟩ := loopMem_export_faithful_denote_uncond subUpdate
    subUpdate_scalarMemN (Expr.lookupArgs carryInvs V) fn top nReg hna hnr s hfn hpc
    (seedVar.lookup V) hseed hn0 _ hm bprev blast bfin hprev hlast hbfin htaken hhalt
  rw [subUpdate_denote_eq] at hdec
  exact ⟨t, _, hrun, hdec,
    subBorrowFold_val N (aVar.lookup V) (bVar.lookup V) (seedVar.lookup V) h0 _ hn⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubLsemTie
