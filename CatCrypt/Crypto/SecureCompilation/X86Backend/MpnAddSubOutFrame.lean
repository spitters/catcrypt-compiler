/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubLsemTie

/-!
# The invariant-array frame of the emitted `mpn_add_n` / `mpn_sub_n` loops

A scalar-accumulator counter loop carries one `.reg w` accumulator; its array
operands are loop invariants. `JasminLsemMemSourceTieUncond.loopBodyFullMN` is
the emitted `chain ++ writeback` body of such a loop, and its writeback moves
the chain's return register into the accumulator register: no instruction of
the body writes an invariant array's slot.

This module states that frame at the trip states of the emitted body, and
instantiates it at the output array of the carry family, whose loop node takes
`out` as an invariant and whose accumulator is the carry (borrow) register.

## Main results

* `loopMem_invArr_frame` — every trip state of the emitted scalar-accumulator
  loop holds each invariant array's entry value in that array's slot.
* `add_emitted_out_slot` / `sub_emitted_out_slot` — the output array's slot at
  every trip state of the emitted `mpn_add_n` / `mpn_sub_n` loop holds the
  entry array `outVar.lookup V`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubOutFrame

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype (N AN)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit (ΓouterCarry)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubLsemTie

/-- The variable of an invariant inside the loop-body context, past the
    accumulator and the loop index. -/
abbrev invBodyVar {invTys : Ctxt jasminDialect} {wacc : Nat} {t : JasminTy}
    (v : Ctxt.Var invTys t) :
    Ctxt.Var (JasminTy.reg wacc :: JasminTy.reg 64 :: invTys) t :=
  Ctxt.Var.there (s := JasminTy.reg wacc) (Ctxt.Var.there (s := JasminTy.reg 64) v)

/-- **The invariant arrays are framed by the emitted scalar-accumulator loop.**
    For a `ScalarMemN` update and a start state agreeing with the trip-`0`
    valuation, every state reached by `runBoundedLoopMem` on the emitted
    `chain ++ writeback` body reads each invariant array `v`, at its
    `resolveVar` slot, as the entry value `v.lookup invs`. -/
theorem loopMem_invArr_frame {invTys : Ctxt jasminDialect} {wacc : Nat}
    (update : Com jasminDialect (JasminTy.reg wacc :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg wacc))
    (hupd : ScalarMemN update) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (invs : Ctxt.Valuation invTys) (s0 : LstateM) (acc0 : BitVec wacc)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s0
      (tripValMN invs 0 acc0))
    (hn0 : (s0.reg.getW nReg 64).isSome)
    {w n : Nat} (v : Ctxt.Var invTys (JasminTy.stackArr w n))
    (t : Nat) (bt : LstateM)
    (hbt : runBoundedLoopMem (loopBodyFullMN update nReg) t s0 = some bt) :
    bt.getArr (operandName (resolveVar (invTys.length + 2) (invTys.length + 2)
        argName (fun _ => none) (invBodyVar (wacc := wacc) v))) w n
      = some (v.lookup invs) :=
  (loopBodyFullMN_inv update hupd nReg hna hnr invs s0 acc0 hseed hn0 t bt hbt).1.arr
    (invBodyVar (wacc := wacc) v)

/-- The output array's variable among the carry family's invariants
    `[a, b, out]`. -/
abbrev outInvVar : Ctxt.Var ([AN, AN, AN] : Ctxt jasminDialect) AN :=
  .there (.there .here)

/-- **The emitted `mpn_add_n` loop's output slot holds the entry array.** At
    every trip state of the emitted `chain ++ writeback` body, the slot the
    linearizer resolves the `out` invariant to reads as `outVar.lookup V`, the
    array the loop was entered with. -/
theorem add_emitted_out_slot
    (V : Ctxt.Valuation ΓouterCarry) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s0 : LstateM) (acc0 : BitVec 64)
    (hseed : StoreAgreesM (([AN, AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN, AN] : Ctxt jasminDialect).length + 2) s0
      (tripValMN (Expr.lookupArgs carryInvs V) 0 acc0))
    (hn0 : (s0.reg.getW nReg 64).isSome)
    (t : Nat) (bt : LstateM)
    (hbt : runBoundedLoopMem (loopBodyFullMN addUpdate nReg) t s0 = some bt) :
    bt.getArr (operandName (resolveVar
        (([AN, AN, AN] : Ctxt jasminDialect).length + 2)
        (([AN, AN, AN] : Ctxt jasminDialect).length + 2)
        argName (fun _ => none) (invBodyVar (wacc := 64) outInvVar))) 64 N
      = some (outVar.lookup V) :=
  loopMem_invArr_frame addUpdate addUpdate_scalarMemN nReg hna hnr
    (Expr.lookupArgs carryInvs V) s0 acc0 hseed hn0 outInvVar t bt hbt

/-- **The emitted `mpn_sub_n` loop's output slot holds the entry array.** The
    borrow-family analogue of `add_emitted_out_slot`. -/
theorem sub_emitted_out_slot
    (V : Ctxt.Valuation ΓouterCarry) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s0 : LstateM) (acc0 : BitVec 64)
    (hseed : StoreAgreesM (([AN, AN, AN] : Ctxt jasminDialect).length + 2)
      (([AN, AN, AN] : Ctxt jasminDialect).length + 2) s0
      (tripValMN (Expr.lookupArgs carryInvs V) 0 acc0))
    (hn0 : (s0.reg.getW nReg 64).isSome)
    (t : Nat) (bt : LstateM)
    (hbt : runBoundedLoopMem (loopBodyFullMN subUpdate nReg) t s0 = some bt) :
    bt.getArr (operandName (resolveVar
        (([AN, AN, AN] : Ctxt jasminDialect).length + 2)
        (([AN, AN, AN] : Ctxt jasminDialect).length + 2)
        argName (fun _ => none) (invBodyVar (wacc := 64) outInvVar))) 64 N
      = some (outVar.lookup V) :=
  loopMem_invArr_frame subUpdate subUpdate_scalarMemN nReg hna hnr
    (Expr.lookupArgs carryInvs V) s0 acc0 hseed hn0 outInvVar t bt hbt

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubOutFrame
