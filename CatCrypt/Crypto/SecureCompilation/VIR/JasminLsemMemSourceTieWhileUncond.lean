/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieWhile
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth

set_option autoImplicit false

/-!
# Unconditional A3-while source tie (`whileMem_export_faithful_comL_uncond`)

`JasminLsemMemSourceTieWhile` ties the emitted data-dependent while to the
source node `ComL.whileNz`, but carries the per-trip simulation `hsim` as a
hypothesis. This file discharges it, the way
`JasminLsemMemSourceTieUncond` (R1) discharges the counter-loop `hsim`: the
committed countdown idiom `while (n != 0) { …; n -= 1 }` iterates exactly the
counter loop's emitted `chain ++ writeback` body `loopBodyFullMN update gReg`
with the counter register *equal to the guard register* — the `SUB gReg ← gReg,
#1` writeback IS the countdown. That body is all-`Lopn` by construction, so:

1. **`runBoundedLoopMemC_allLopn`** (§1): on an all-`Lopn` body the one-level
   call fold `runBoundedLoopMemC` is the plain bounded fold
   `runBoundedLoopMem` — the trip-fold face of
   `lsemStraightMemC_allLopn`. This moves the while route's C-fold trip
   states into the counter family's trip invariant `loopBodyFullMN_inv`.
2. **`whileMem_export_faithful_comL_uncond`** (§2): the composed export
   theorem — same conclusion as the conditional form (the machine run of the
   emitted `whileLinstrRM top gReg [] (loopBodyFullMN update gReg)` decodes at
   the accumulator argument to `ComL.whileNz`'s `ComL.denote`), with `hsim`
   REPLACED by the R1 hypothesis class: the update-shape `hupd : ScalarMemN
   update`, the guard-register name hygiene (`hna`/`hnr`), the seed agreement
   (`hseed`/`hn0`), and the run schedule (`hhalt`/`htrip` — unchanged from the
   conditional form; `htrip` is the countdown-idiom trip identification, part
   of the conditional statement, not of `hsim`). The per-trip simulation is
   proved through `loopBodyFullMN_inv` + `loopBodyFullMN_trip` (never
   re-proved), transported across §1's fold bridge; the `BodyStepOK` side
   condition and the seed decode hold by construction
   (`loopBodyFullMN_isLopn`, `tripAgree_getW_acc`).
3. **`runWhileMem_countdown_halts_trips`** (§3): the **termination
   characterization** for the countdown body class — from a seed with guard
   value `vn` (`0 < vn.toNat ≤ fuel`), the do-while HALTS and
   `whileTripsMem … = vn.toNat`, by induction on the fuel with one
   `loopBodyFullMN_trip` guard decrement per step. `0 < vn.toNat` is required:
   the emitted idiom is body-first (do-while), so a zero seed underflows to
   `2^64 - 1` on entry and the run does not stop at trip `0`.
4. **`whileMem_export_faithful_comL_trips` /
   `whileMem_export_faithful_comL_uncond_trips`** (§4): the export corollaries
   with the run-schedule pair `hhalt`/`htrip` REPLACED by the seed-value
   hypotheses (`hgseed`/`hpos`) via §3; the do-while fuel is pinned to the
   seed, so no fuel parameter remains on the statement surface.

**0 sorries; axioms = {propext, Classical.choice, Quot.sound}.**
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieWhileUncond

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChainBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieWhile

variable {invTys : Ctxt jasminDialect}

/-! ## 1. The all-`Lopn` trip-fold bridge -/

/-- On an all-`Lopn` body, the one-level call trip-fold `runBoundedLoopMemC`
    is the plain bounded fold `runBoundedLoopMem` — the trip-fold face of
    `lsemStraightMemC_allLopn` (both folds peel the body-fold then reset the
    pc to `1`). -/
theorem runBoundedLoopMemC_allLopn (env : LeafEnvM) (body : List LinstrRM)
    (hlopn : ∀ i ∈ body, IsLopn i) :
    ∀ (t : Nat) (s : LstateM),
      runBoundedLoopMemC env body t s = runBoundedLoopMem body t s := by
  intro t
  induction t with
  | zero => intro s; rfl
  | succ k ih =>
      intro s
      rw [runBoundedLoopMemC_succ, runBoundedLoopMem_succ,
        lsemStraightMemC_allLopn env body hlopn s]
      cases lsemStraightMem body s with
      | none => rfl
      | some b => exact ih (b.setLpc 1)

/-! ## 2. The unconditional export theorem -/

/-- **A3 export faithfulness at `ComL.denote`, UNCONDITIONAL per-trip.** The
    `whileMem_export_faithful_comL` upgrade for the countdown idiom: the body
    is the emitted `chain ++ writeback` pass `loopBodyFullMN update gReg` with
    the counter register equal to the guard register (its `SUB gReg ← gReg, #1`
    writeback is the countdown), and the per-trip simulation `hsim` is
    DISCHARGED — `loopBodyFullMN_inv` supplies agreement at every
    `runBoundedLoopMemC` trip state through §1's fold bridge, and
    `loopBodyFullMN_trip` runs one pass. The remaining hypotheses are the
    update shape (`hupd`), the guard-register name hygiene (`hna`/`hnr`), the
    pc/name pins (`hfn`/`hpc`), the seed (`hseed`/`hn0`), and the run schedule
    (`hhalt` — the do-while halts, trip read off the run; `htrip` — the
    data-dependent trip equals the countdown seed, the same trip
    identification the conditional form carries). No hypothesis quantifies
    over internal machine states. -/
theorem whileMem_export_faithful_comL_uncond {Γ : Ctxt jasminDialect} {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update)
    (guardV : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.reg w))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (env : LeafEnvM) (fn : String) (top : LLabel) (gReg : String)
    (hna : ∀ j, gReg ≠ argName j) (hnr : ∀ k, gReg ≠ regName k)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s.base
      (tripValMN (Expr.lookupArgs invsV V) 0 (initV.lookup V)))
    (hn0 : (s.base.reg.getW gReg 64).isSome)
    (fuel : Nat) (bfin : LstateM)
    (hhalt : runWhileMem env (fun b => condNZ b (.reg gReg))
      (loopBodyFullMN update gReg) fuel s.base = some bfin)
    (htrip : whileTripsMem env (fun b => condNZ b (.reg gReg))
        (loopBodyFullMN update gReg) fuel s.base = (guardV.lookup V).toNat) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env
          (singletonProgM fn (whileLinstrRM top gReg [] (loopBodyFullMN update gReg)))
          (whileTripsMem env (fun b => condNZ b (.reg gReg))
              (loopBodyFullMN update gReg) fuel s.base
            * (fuelCostC env (loopBodyFullMN update gReg) + 1)) s = some t
        ∧ decodeM t.base (accRegMN invTys) w
            = some ((ComL.whileNz update guardV initV invsV (.ret .here)).denote V) := by
  refine whileMem_export_faithful_comL update guardV initV invsV V env fn top gReg
    (loopBodyFullMN update gReg)
    (fun i hi => Or.inl (loopBodyFullMN_isLopn update gReg i hi))
    s hfn hpc fuel bfin hhalt htrip (accRegMN invTys)
    (tripAgree_getW_acc hseed) ?_
  -- the per-trip simulation, DISCHARGED through the counter family's invariant
  intro t _ bt acct hbt hdec
  rw [runBoundedLoopMemC_allLopn env _ (loopBodyFullMN_isLopn update gReg)] at hbt
  obtain ⟨hAgt, hnt⟩ := loopBodyFullMN_inv update hupd gReg hna hnr
    (Expr.lookupArgs invsV V) s.base (initV.lookup V) hseed hn0 t bt hbt
  obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnt
  have hacct : decodeM bt (accRegMN invTys) w
      = some (JLoopBodyN.denote ⟨t, update⟩ (Expr.lookupArgs invsV V)
          (initV.lookup V)) := tripAgree_getW_acc hAgt
  rw [hdec] at hacct
  obtain rfl := Option.some.inj hacct
  obtain ⟨bt', hbt', hAg', _⟩ := loopBodyFullMN_trip update hupd gReg hna hnr
    (Expr.lookupArgs invsV V) t _ bt hAgt vn hvn
  refine ⟨bt', ?_, tripAgree_getW_acc hAg'⟩
  rw [lsemStraightMemC_allLopn env _ (loopBodyFullMN_isLopn update gReg)]
  exact hbt'

/-! ## 3. The countdown termination characterization -/

/-- Read the back-edge guard off a register lookup: `condNZ` at `.reg r` is
    exactly "the looked-up 64-bit word is non-zero". -/
theorem condNZ_of_getW {b : LstateM} {r : String} {v : BitVec 64}
    (h : b.reg.getW r 64 = some v) :
    condNZ b (.reg r) = decide (v ≠ 0#64) := by
  unfold condNZ
  rw [show evalOperandN b.reg 64 (.reg r) = some v from h]

/-- **The countdown halts with trip count = the seed.** For the countdown body
    `loopBodyFullMN update gReg` (its `SUB gReg ← gReg, #1` writeback IS the
    guard decrement), from any state agreeing with a trip valuation and holding
    guard value `vn` with `0 < vn.toNat ≤ fuel`: the do-while `runWhileMem`
    HALTS within `fuel`, and the data-dependent trip count `whileTripsMem …`
    equals the seed `vn.toNat`. Induction on the fuel: each trip takes guard
    value `k + 1` to `k` (`loopBodyFullMN_trip` across §1's fold face), and the
    first zero exits. Both side conditions are required: `vn.toNat ≤ fuel`
    because `runWhileMem` spends one fuel unit per trip, and `0 < vn.toNat`
    because the emitted idiom is body-first (do-while) — a zero seed underflows
    to `2^64 - 1` on entry and the run does not stop at trip `0`. -/
theorem runWhileMem_countdown_halts_trips {w : Nat} (env : LeafEnvM)
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update) (gReg : String)
    (hna : ∀ j, gReg ≠ argName j) (hnr : ∀ k, gReg ≠ regName k)
    (invs : Ctxt.Valuation invTys) :
    ∀ (fuel t : Nat) (bt : LstateM) (acc : BitVec w) (vn : BitVec 64),
      StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt
        (tripValMN invs t acc) →
      bt.reg.getW gReg 64 = some vn →
      0 < vn.toNat → vn.toNat ≤ fuel →
      (∃ bfin, runWhileMem env (fun b => condNZ b (.reg gReg))
          (loopBodyFullMN update gReg) fuel bt = some bfin)
        ∧ whileTripsMem env (fun b => condNZ b (.reg gReg))
            (loopBodyFullMN update gReg) fuel bt = vn.toNat := by
  intro fuel
  induction fuel with
  | zero => intro t bt acc vn _ _ hpos hle; omega
  | succ f ih =>
      intro t bt acc vn hAg hvn hpos hle
      obtain ⟨bt', hbt', hAg', hn'⟩ :=
        loopBodyFullMN_trip update hupd gReg hna hnr invs t acc bt hAg vn hvn
      have hC : lsemStraightMemC env (loopBodyFullMN update gReg) bt = some bt' := by
        rw [lsemStraightMemC_allLopn env _ (loopBodyFullMN_isLopn update gReg)]
        exact hbt'
      have hrun : runWhileMem env (fun b => condNZ b (.reg gReg))
          (loopBodyFullMN update gReg) (f + 1) bt
          = if condNZ bt' (.reg gReg)
            then runWhileMem env (fun b => condNZ b (.reg gReg))
              (loopBodyFullMN update gReg) f (bt'.setLpc 1)
            else some bt' := by
        rw [runWhileMem_succ, hC]
      have htr : whileTripsMem env (fun b => condNZ b (.reg gReg))
          (loopBodyFullMN update gReg) (f + 1) bt
          = if condNZ bt' (.reg gReg)
            then whileTripsMem env (fun b => condNZ b (.reg gReg))
              (loopBodyFullMN update gReg) f (bt'.setLpc 1) + 1
            else 1 := by
        rw [whileTripsMem_succ, hC]
      have hcond : condNZ bt' (.reg gReg) = decide (vn - 1#64 ≠ 0#64) :=
        condNZ_of_getW hn'
      by_cases h1 : vn.toNat = 1
      · -- last trip: the decremented guard reads zero, the do-while exits
        have hz : vn - 1#64 = 0#64 := by bv_omega
        have hfalse : condNZ bt' (.reg gReg) = false := by
          rw [hcond, hz]; simp
        rw [hrun, htr, hfalse, if_neg Bool.false_ne_true,
          if_neg Bool.false_ne_true]
        exact ⟨⟨bt', rfl⟩, h1.symm⟩
      · -- taken back-edge: recurse from the decremented guard
        have hsub : (vn - 1#64).toNat = vn.toNat - 1 := by bv_omega
        have hne : vn - 1#64 ≠ 0#64 := by bv_omega
        have htrue : condNZ bt' (.reg gReg) = true := by
          rw [hcond]; exact decide_eq_true hne
        have hn1 : (bt'.setLpc 1).reg.getW gReg 64 = some (vn - 1#64) := by
          rw [show ((bt'.setLpc 1).reg).getW gReg 64 = bt'.reg.getW gReg 64 from
            LstateN.getW_congr_lvm (LstateM.reg_lvm_setLpc bt' 1) gReg 64]
          exact hn'
        obtain ⟨⟨bfin, hfin⟩, htrips⟩ := ih (t + 1) (bt'.setLpc 1) _ (vn - 1#64)
          (StoreAgreesM.setLpc hAg' 1) hn1 (by omega) (by omega)
        rw [hrun, htr, htrue, if_pos rfl, if_pos rfl]
        exact ⟨⟨bfin, hfin⟩, by rw [htrips, hsub]; omega⟩

/-! ## 4. The export corollaries: run schedule replaced by the seed value -/

/-- **A3 export at `ComL.denote` for the countdown body, run schedule
    discharged, per-trip simulation carried.** `whileMem_export_faithful_comL`
    specialized to the countdown body `loopBodyFullMN update gReg`, with the
    run-schedule pair `hhalt`/`htrip` REPLACED by the seed-value hypotheses:
    the guard register seeds the guard variable's value (`hgseed`) and the
    seed is positive (`hpos` — §3's do-while entry condition). §3
    proves halting and the trip identification with the do-while fuel pinned
    to the seed, so no fuel parameter remains. The per-trip simulation `hsim`
    and the accumulator register stay generic (the seed agreement `hseed`
    feeds §3's guard-decrement induction only); the fully discharged form is
    `whileMem_export_faithful_comL_uncond_trips`. -/
theorem whileMem_export_faithful_comL_trips {Γ : Ctxt jasminDialect} {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update)
    (guardV : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.reg w))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (env : LeafEnvM) (fn : String) (top : LLabel) (gReg : String)
    (hna : ∀ j, gReg ≠ argName j) (hnr : ∀ k, gReg ≠ regName k)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s.base
      (tripValMN (Expr.lookupArgs invsV V) 0 (initV.lookup V)))
    (hgseed : s.base.reg.getW gReg 64 = some (guardV.lookup V))
    (hpos : 0 < (guardV.lookup V).toNat)
    (accReg : String)
    (hinit : decodeM s.base accReg w = some (initV.lookup V))
    (hsim : ∀ t, t < (guardV.lookup V).toNat → ∀ (bt : LstateM) (acct : BitVec w),
      runBoundedLoopMemC env (loopBodyFullMN update gReg) t s.base = some bt →
      decodeM bt accReg w = some acct →
      ∃ bt', lsemStraightMemC env (loopBodyFullMN update gReg) bt = some bt'
        ∧ decodeM bt' accReg w
            = some (JLoopBodyN.stepC update (Expr.lookupArgs invsV V) t acct)) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env
          (singletonProgM fn (whileLinstrRM top gReg [] (loopBodyFullMN update gReg)))
          ((guardV.lookup V).toNat
            * (fuelCostC env (loopBodyFullMN update gReg) + 1)) s = some t
        ∧ decodeM t.base accReg w
            = some ((ComL.whileNz update guardV initV invsV (.ret .here)).denote V) := by
  obtain ⟨⟨bfin, hhalt⟩, htrips⟩ := runWhileMem_countdown_halts_trips env update
    hupd gReg hna hnr (Expr.lookupArgs invsV V) (guardV.lookup V).toNat 0 s.base
    (initV.lookup V) (guardV.lookup V) hseed hgseed hpos le_rfl
  obtain ⟨t, ht, hdec⟩ := whileMem_export_faithful_comL update guardV initV invsV V
    env fn top gReg (loopBodyFullMN update gReg)
    (fun i hi => Or.inl (loopBodyFullMN_isLopn update gReg i hi))
    s hfn hpc (guardV.lookup V).toNat bfin hhalt htrips accReg hinit hsim
  exact ⟨t, htrips ▸ ht, hdec⟩

/-- **A3 export at `ComL.denote`, UNCONDITIONAL, run schedule discharged.**
    `whileMem_export_faithful_comL_uncond` with the run-schedule pair
    `hhalt`/`htrip` REPLACED by the seed-value hypotheses via §3 (and `hn0`
    absorbed into `hgseed`): the remaining hypotheses are the update shape
    (`hupd`), the guard-register name hygiene (`hna`/`hnr`), the pc/name pins
    (`hfn`/`hpc`), the seed agreement (`hseed`), the guard seed value
    (`hgseed`) and its positivity (`hpos` — §3's do-while entry
    condition). No hypothesis mentions the run or a fuel budget: halting, the
    trip count and the machine fuel `(guardV.lookup V).toNat * (fuelCostC … +
    1)` are all computed from the seed. -/
theorem whileMem_export_faithful_comL_uncond_trips {Γ : Ctxt jasminDialect} {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update)
    (guardV : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.reg w))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (env : LeafEnvM) (fn : String) (top : LLabel) (gReg : String)
    (hna : ∀ j, gReg ≠ argName j) (hnr : ∀ k, gReg ≠ regName k)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s.base
      (tripValMN (Expr.lookupArgs invsV V) 0 (initV.lookup V)))
    (hgseed : s.base.reg.getW gReg 64 = some (guardV.lookup V))
    (hpos : 0 < (guardV.lookup V).toNat) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env
          (singletonProgM fn (whileLinstrRM top gReg [] (loopBodyFullMN update gReg)))
          ((guardV.lookup V).toNat
            * (fuelCostC env (loopBodyFullMN update gReg) + 1)) s = some t
        ∧ decodeM t.base (accRegMN invTys) w
            = some ((ComL.whileNz update guardV initV invsV (.ret .here)).denote V) := by
  obtain ⟨⟨bfin, hhalt⟩, htrips⟩ := runWhileMem_countdown_halts_trips env update
    hupd gReg hna hnr (Expr.lookupArgs invsV V) (guardV.lookup V).toNat 0 s.base
    (initV.lookup V) (guardV.lookup V) hseed hgseed hpos le_rfl
  obtain ⟨t, ht, hdec⟩ := whileMem_export_faithful_comL_uncond update hupd guardV
    initV invsV V env fn top gReg hna hnr s hfn hpc hseed
    (by rw [hgseed]; rfl) (guardV.lookup V).toNat bfin hhalt htrips
  exact ⟨t, htrips ▸ ht, hdec⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieWhileUncond
