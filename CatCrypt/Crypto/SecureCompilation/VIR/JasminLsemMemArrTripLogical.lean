/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalLsemTie
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTrip
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond

/-!
# The emitted `mpn_and_n`, `mpn_ior_n` and `mpn_xor_n` loops are array-carrier fragment members, unconditionally

`MpnLogicalLsemTie.and_emitted_machine_val` / `ior_emitted_machine_val` /
`xor_emitted_machine_val` compose the array-accumulator backend-faithfulness
conclusion with `andFold_cells` / `iorFold_cells` / `xorFold_cells`, but take
that conclusion as a hypothesis `hfaithful`.
`JasminLsemMemSourceTieArrUncond.loopMemArr_export_faithful_denote_uncond`
discharges it for the emitted `chain ++ writeback` body of any `ArrMemN` update,
given only the counter schedule, the seed and the counter-name hygiene.

This module identifies the front-compiled `andUpdate` / `iorUpdate` / `xorUpdate`
as `ArrMemN` members and instantiates the unconditional export theorem at each,
closing the machine-value theorems with no per-trip simulation hypothesis.

## Main results

* `andUpdate_arrMemN` / `iorUpdate_arrMemN` / `xorUpdate_arrMemN` — the front-
  compiled limb bodies are members of the array-returning stack-memory fragment
  `ArrMemN`.
* `andLoop_export_faithful_denote` / `iorLoop_export_faithful_denote` /
  `xorLoop_export_faithful_denote` — the export faithfulness conclusion at each
  body, the shape the machine-value tie takes as `hfaithful`.
* `and_emitted_machine_val_closed` / `ior_emitted_machine_val_closed` /
  `xor_emitted_machine_val_closed` — the machine execution of each emitted loop
  produces output cells equal to the elementwise `List.zipWith` of the two source
  arrays, with no per-trip simulation hypothesis.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripLogical

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalFrontDenote
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLogicalLsemTie

/-! ## 1. The front-compiled limb bodies are `ArrMemN` members -/

/-- **The front-compiled `mpn_and_n` limb body is in the array-returning
    stack-memory fragment.** The front output is a chain of register-producing
    heads (two `stackLoad`s and the conjunction) and one `stackStore` binding,
    terminated by a `.ret` at the output array — the `ArrMemN` shape. -/
theorem andUpdate_arrMemN : ArrMemN andUpdate := by
  unfold andUpdate
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

/-- **The front-compiled `mpn_ior_n` limb body is in the array-returning
    stack-memory fragment.** The disjunction analogue of `andUpdate_arrMemN`. -/
theorem iorUpdate_arrMemN : ArrMemN iorUpdate := by
  unfold iorUpdate
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

/-- **The front-compiled `mpn_xor_n` limb body is in the array-returning
    stack-memory fragment.** The exclusive-or analogue of `andUpdate_arrMemN`. -/
theorem xorUpdate_arrMemN : ArrMemN xorUpdate := by
  unfold xorUpdate
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

/-- **The array-accumulator export faithfulness at `andUpdate`.** The emitted
    `mpn_and_n` loop's machine run decodes at the accumulator's array slot to the
    source fold `JLoopBodyN.denote ⟨n, andUpdate⟩`, with only the counter
    schedule, the seed and the counter-name hygiene as hypotheses — the shape
    `and_emitted_machine_val` takes as `hfaithful`. The instantiation of
    `loopMemArr_export_faithful_denote_uncond` at `andUpdate` and
    `andUpdate_arrMemN`. -/
theorem andLoop_export_faithful_denote
    (V : Ctxt.Valuation Gouter)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AL, AL] : Ctxt jasminDialect).length + 2)
      (([AL, AL] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs logicInvs V) 0 (logicInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (logicCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN andUpdate nReg)
      ((logicCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN andUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN andUpdate nReg)
      (logicCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (logicCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN andUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN andUpdate nReg)))
          ((logicCount.lookup V).toNat * ((loopBodyArrFullMN andUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AL, AL]) 64 NL
            = some (JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, andUpdate⟩
                (Expr.lookupArgs logicInvs V) (logicInit.lookup V)) :=
  loopMemArr_export_faithful_denote_uncond andUpdate andUpdate_arrMemN
    (Expr.lookupArgs logicInvs V) fn top nReg hna hnr s hfn hpc (logicInit.lookup V)
    hseed hn0 (logicCount.lookup V).toNat hm bprev blast bfin hprev hlast hbfin htaken hhalt

/-- **The array-accumulator export faithfulness at `iorUpdate`.** The disjunction
    analogue of `andLoop_export_faithful_denote`. -/
theorem iorLoop_export_faithful_denote
    (V : Ctxt.Valuation Gouter)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AL, AL] : Ctxt jasminDialect).length + 2)
      (([AL, AL] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs logicInvs V) 0 (logicInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (logicCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN iorUpdate nReg)
      ((logicCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN iorUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN iorUpdate nReg)
      (logicCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (logicCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN iorUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN iorUpdate nReg)))
          ((logicCount.lookup V).toNat * ((loopBodyArrFullMN iorUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AL, AL]) 64 NL
            = some (JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, iorUpdate⟩
                (Expr.lookupArgs logicInvs V) (logicInit.lookup V)) :=
  loopMemArr_export_faithful_denote_uncond iorUpdate iorUpdate_arrMemN
    (Expr.lookupArgs logicInvs V) fn top nReg hna hnr s hfn hpc (logicInit.lookup V)
    hseed hn0 (logicCount.lookup V).toNat hm bprev blast bfin hprev hlast hbfin htaken hhalt

/-- **The array-accumulator export faithfulness at `xorUpdate`.** The exclusive-or
    analogue of `andLoop_export_faithful_denote`. -/
theorem xorLoop_export_faithful_denote
    (V : Ctxt.Valuation Gouter)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AL, AL] : Ctxt jasminDialect).length + 2)
      (([AL, AL] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs logicInvs V) 0 (logicInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (logicCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN xorUpdate nReg)
      ((logicCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN xorUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN xorUpdate nReg)
      (logicCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (logicCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN xorUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN xorUpdate nReg)))
          ((logicCount.lookup V).toNat * ((loopBodyArrFullMN xorUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AL, AL]) 64 NL
            = some (JLoopBodyN.denote ⟨(logicCount.lookup V).toNat, xorUpdate⟩
                (Expr.lookupArgs logicInvs V) (logicInit.lookup V)) :=
  loopMemArr_export_faithful_denote_uncond xorUpdate xorUpdate_arrMemN
    (Expr.lookupArgs logicInvs V) fn top nReg hna hnr s hfn hpc (logicInit.lookup V)
    hseed hn0 (logicCount.lookup V).toNat hm bprev blast bfin hprev hlast hbfin htaken hhalt

/-! ## 3. The unconditional flagship value theorems -/

/-- **The compiled `mpn_and_n` computes the elementwise conjunction,
    unconditionally.** For a trip count within the model's output array, the
    emitted machine loop — run under `lsemFuelMemL` from a start state with the
    counter schedule, the seed and the counter-name hygiene — halts with output
    cells `0, …, n-1` equal to the elementwise `List.zipWith` conjunction of the
    two source arrays. The per-trip array simulation is discharged through
    `andUpdate_arrMemN`, so no faithfulness hypothesis remains. -/
theorem and_emitted_machine_val_closed
    (V : Ctxt.Valuation Gouter)
    (hn : (logicCount.lookup V).toNat ≤ NL)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AL, AL] : Ctxt jasminDialect).length + 2)
      (([AL, AL] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs logicInvs V) 0 (logicInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (logicCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN andUpdate nReg)
      ((logicCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN andUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN andUpdate nReg)
      (logicCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (logicCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN andUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ (t : LstatePM) (out : Fin NL → BitVec 64),
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN andUpdate nReg)))
          ((logicCount.lookup V).toNat * ((loopBodyArrFullMN andUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AL, AL]) 64 NL = some out
        ∧ cells out (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x &&& y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) :=
  and_emitted_machine_val V hn fn top nReg
    (loopBodyArrFullMN andUpdate nReg) (accRegMN [AL, AL]) s
    (andLoop_export_faithful_denote V fn top nReg hna hnr s hfn hpc hseed hn0 hm
      bprev blast bfin hprev hlast hbfin htaken hhalt)

/-- **The compiled `mpn_ior_n` computes the elementwise disjunction,
    unconditionally.** The disjunction analogue of
    `and_emitted_machine_val_closed`. -/
theorem ior_emitted_machine_val_closed
    (V : Ctxt.Valuation Gouter)
    (hn : (logicCount.lookup V).toNat ≤ NL)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AL, AL] : Ctxt jasminDialect).length + 2)
      (([AL, AL] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs logicInvs V) 0 (logicInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (logicCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN iorUpdate nReg)
      ((logicCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN iorUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN iorUpdate nReg)
      (logicCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (logicCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN iorUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ (t : LstatePM) (out : Fin NL → BitVec 64),
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN iorUpdate nReg)))
          ((logicCount.lookup V).toNat * ((loopBodyArrFullMN iorUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AL, AL]) 64 NL = some out
        ∧ cells out (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x ||| y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) :=
  ior_emitted_machine_val V hn fn top nReg
    (loopBodyArrFullMN iorUpdate nReg) (accRegMN [AL, AL]) s
    (iorLoop_export_faithful_denote V fn top nReg hna hnr s hfn hpc hseed hn0 hm
      bprev blast bfin hprev hlast hbfin htaken hhalt)

/-- **The compiled `mpn_xor_n` computes the elementwise exclusive-or,
    unconditionally.** The exclusive-or analogue of
    `and_emitted_machine_val_closed`. -/
theorem xor_emitted_machine_val_closed
    (V : Ctxt.Valuation Gouter)
    (hn : (logicCount.lookup V).toNat ≤ NL)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (([AL, AL] : Ctxt jasminDialect).length + 2)
      (([AL, AL] : Ctxt jasminDialect).length + 2) s.base
      (tripValArrMN (Expr.lookupArgs logicInvs V) 0 (logicInit.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (logicCount.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN xorUpdate nReg)
      ((logicCount.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN xorUpdate nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN xorUpdate nReg)
      (logicCount.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (logicCount.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN xorUpdate nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ (t : LstatePM) (out : Fin NL → BitVec 64),
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN xorUpdate nReg)))
          ((logicCount.lookup V).toNat * ((loopBodyArrFullMN xorUpdate nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN [AL, AL]) 64 NL = some out
        ∧ cells out (logicCount.lookup V).toNat
            = List.zipWith (fun x y => x ^^^ y)
                (cells (apVar.lookup V) (logicCount.lookup V).toNat)
                (cells (bpVar.lookup V) (logicCount.lookup V).toNat) :=
  xor_emitted_machine_val V hn fn top nReg
    (loopBodyArrFullMN xorUpdate nReg) (accRegMN [AL, AL]) s
    (xorLoop_export_faithful_denote V fn top nReg hna hnr s hfn hpc hseed hn0 hm
      bprev blast bfin hprev hlast hbfin htaken hhalt)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripLogical
