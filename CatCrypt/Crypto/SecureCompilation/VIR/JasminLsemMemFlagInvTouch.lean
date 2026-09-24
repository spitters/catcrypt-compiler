/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieWhileUncond

@[expose] public section

set_option autoImplicit false

/-!
# Invariant-touch loop bodies: export faithfulness under a restoration discipline

The unconditional source-tie export theorems
(`loopMem_export_faithful_denote_uncond`, `whileMem_export_faithful_comL_uncond`)
pin the loop body to EXACTLY the emitted `chain ++ writeback` pass
`loopBodyFullMN update nReg`: their trip invariant preserves the agreement
`StoreAgreesM _ _ bt (tripValMN invs t acc)` — the invariant CARRIER (the
invariant argument registers, the loop index, the accumulator, and the tracked
array regions) — only because the chain's write frame and the three recognized
writeback writes never touch a tracked slot.  A body that WRITES inside the
tracked region anywhere else (a mid-body clobber-then-restore of the
accumulator or an invariant register, or an interleaved flag-`CMP`) falls
outside that body class, and no export theorem applies to it.

This module widens the body class to `touch ++ chain ++ writeback`
(`loopBodyInvTouchMN`), where the `touch` segment MAY write invariant-tracked
state, under the weakest side condition — a **per-trip restoration
discipline**:

* `TouchRestoresMN` (counter machine, `lsemStraightMem`): from any state
  agreeing with a trip valuation, the touch segment runs to completion,
  RE-AGREES with the SAME trip valuation at its end (the region's decoded value
  at the trip boundary is restored — mid-segment states are unconstrained), and
  preserves the counter register's read.
* `TouchRestoresFMN` (flag machine, `runStraightF`): the same discipline over
  the extended `Lopn ∪ MOV ∪ CMP` step `fstepF`, so the touch may SET THE FLAG
  mid-body (`CMP` on tracked registers) — the exit flag is unconstrained (the
  emitted back-edge `CMP` recomputes it).

The discipline is closed under concatenation (`TouchRestoresMN_append` /
`TouchRestoresFMN_append`) and is NOT vacuous: §6 exhibits witnesses —
`accClobberTouch` (save/clobber/restore of the ACCUMULATOR register: the middle
instruction writes a wrong value into the tracked carrier) and `cmpIdxTouch`
(a flag-`CMP` reading the tracked loop-index register inside the body).

## The widened export theorems (same conclusions as the pinned-body forms)

* `loopMem_export_faithful_denote_invTouch` / `_comL_invTouch` — the
  counter-loop exports at `JLoopBodyN.denote` / `ComL.forLoopNRt`'s denotation.
* `whileMem_export_faithful_comL_invTouch` — the countdown-while export at
  `ComL.whileNz`'s denotation.
* `guardedFlagLoop_export_faithful_denote_invTouch` / `_comL_invTouch` — the
  FLAG-machine export: the full `forLoopLcmdNRt` skeleton
  (`guardedFlagLoopLinstrRM` — zero-trip guard + flag back-edge) with an
  invariant-touch body, run by `lsemFuelMemF`, halts on a state whose
  accumulator decodes to the source denotation.  The per-pass fold is
  `runStraightF`, so the touch segment may contain flag-`CMP`s; the emitted
  `chain`/`writeback` halves step through the plain delegate
  (`runStraightF_plain`), pinned by the `PlainLopnBody` side condition on the
  chain (decidable per instance — `plainLopnBodyB`; the writeback's is proved,
  `loopWritebackMN_plain`).

## Walls (out of scope for this class)

* A touch whose write survives the trip boundary (the region durably modified)
  needs a STRENGTHENED invariant carrying the touched cells — the source node
  would have to mention them; no such source node exists in `ComL`.
* A touch interleaved INSIDE the emitted chain: the chain's simulation
  (`lsemStraightMem_straightOps_full`) is atomic; splitting it needs a
  mid-chain agreement notion over the partially-built scratch registers.
* `PlainLopnBody (loopBodyChainMN update)` is a per-instance decidable side
  condition on the flag route, not proved generically over `ScalarMemN`
  linearizations (the counter-machine route does not need it).

**Fully proved; axioms ⊆ {propext, Classical.choice, Quot.sound}.**
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagInvTouch

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
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieWhileUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin

variable {invTys : Ctxt jasminDialect}

/-! ## 1. The restoration discipline -/

/-- **The per-trip restoration discipline (counter machine).**  From ANY state
    agreeing with a trip valuation `tripValMN invs t acc`, the touch segment
    runs to completion under the straight-line body-fold `lsemStraightMem`, re-agrees with
    the SAME trip valuation at its end, and preserves the counter register's
    read.  Mid-segment states are unconstrained — the segment may write
    invariant-tracked registers (accumulator, loop index, invariant args) and
    tracked array regions, as long as the trip-boundary decode is restored. -/
def TouchRestoresMN (invTys : Ctxt jasminDialect) (w : Nat) (touch : List LinstrRM)
    (nReg : String) : Prop :=
  ∀ (invs : Ctxt.Valuation invTys) (t : Nat) (acc : BitVec w) (s : LstateM),
    StoreAgreesM (invTys.length + 2) (invTys.length + 2) s (tripValMN invs t acc) →
    ∃ s', lsemStraightMem touch s = some s'
      ∧ StoreAgreesM (invTys.length + 2) (invTys.length + 2) s' (tripValMN invs t acc)
      ∧ s'.reg.getW nReg 64 = s.reg.getW nReg 64

/-- **The per-trip restoration discipline (flag machine).**  The same
    discipline over the extended straight fold `runStraightF` (`Lopn ∪ reg-copy
    MOV ∪ flag-CMP`): the segment may additionally SET THE FLAG (`CMP` forms) —
    the exit flag is existential (unconstrained; the emitted back-edge `CMP`
    recomputes it before every branch decision). -/
def TouchRestoresFMN (invTys : Ctxt jasminDialect) (w : Nat) (touch : List LinstrRM)
    (nReg : String) : Prop :=
  ∀ (invs : Ctxt.Valuation invTys) (t : Nat) (acc : BitVec w) (s : LstateM) (zf : Bool),
    StoreAgreesM (invTys.length + 2) (invTys.length + 2) s (tripValMN invs t acc) →
    ∃ s' zf', runStraightF touch s zf = some (s', zf')
      ∧ StoreAgreesM (invTys.length + 2) (invTys.length + 2) s' (tripValMN invs t acc)
      ∧ s'.reg.getW nReg 64 = s.reg.getW nReg 64

/-- The empty touch restores (degenerate: the pinned body class is the
    `touch = []` instance of the widened one). -/
theorem TouchRestoresMN_nil (w : Nat) (nReg : String) :
    TouchRestoresMN invTys w [] nReg :=
  fun _ _ _ s h => ⟨s, lsemStraightMem_nil s, h, rfl⟩

/-- The extended straight fold splits over `++`. -/
theorem runStraightF_append (xs ys : List LinstrRM) :
    ∀ (s : LstateM) (zf : Bool),
      runStraightF (xs ++ ys) s zf
        = (runStraightF xs s zf).bind (fun bz => runStraightF ys bz.1 bz.2) := by
  induction xs with
  | nil => intro s zf; simp
  | cons i is ih =>
      intro s zf
      rw [List.cons_append, runStraightF_cons, runStraightF_cons]
      cases fstepF i s zf with
      | none => rfl
      | some bz =>
          rw [Option.bind_some, Option.bind_some]
          exact ih bz.1 bz.2

/-- The restoration discipline is closed under concatenation (counter). -/
theorem TouchRestoresMN_append (w : Nat) (t1 t2 : List LinstrRM) (nReg : String)
    (h1 : TouchRestoresMN invTys w t1 nReg) (h2 : TouchRestoresMN invTys w t2 nReg) :
    TouchRestoresMN invTys w (t1 ++ t2) nReg := by
  intro invs t acc s hag
  obtain ⟨s1, hr1, hAg1, hp1⟩ := h1 invs t acc s hag
  obtain ⟨s2, hr2, hAg2, hp2⟩ := h2 invs t acc s1 hAg1
  exact ⟨s2, by rw [lsemStraightMem_append, hr1, Option.bind_some]; exact hr2,
    hAg2, hp2.trans hp1⟩

/-- The restoration discipline is closed under concatenation (flag). -/
theorem TouchRestoresFMN_append (w : Nat) (t1 t2 : List LinstrRM) (nReg : String)
    (h1 : TouchRestoresFMN invTys w t1 nReg) (h2 : TouchRestoresFMN invTys w t2 nReg) :
    TouchRestoresFMN invTys w (t1 ++ t2) nReg := by
  intro invs t acc s zf hag
  obtain ⟨s1, zf1, hr1, hAg1, hp1⟩ := h1 invs t acc s zf hag
  obtain ⟨s2, zf2, hr2, hAg2, hp2⟩ := h2 invs t acc s1 zf1 hAg1
  exact ⟨s2, zf2, by rw [runStraightF_append, hr1, Option.bind_some]; exact hr2,
    hAg2, hp2.trans hp1⟩

/-- A plain (no `CMP`, no reg-copy `MOV`) restoring touch restores on the flag
    machine too — the flag threads through unchanged. -/
theorem TouchRestoresFMN_of_plain (w : Nat) (touch : List LinstrRM) (nReg : String)
    (hplain : PlainLopnBody touch) (h : TouchRestoresMN invTys w touch nReg) :
    TouchRestoresFMN invTys w touch nReg := by
  intro invs t acc s zf hag
  obtain ⟨s', hrun, hAg, hpres⟩ := h invs t acc s hag
  refine ⟨s', zf, ?_, hAg, hpres⟩
  rw [runStraightF_plain touch hplain s zf, hrun, Option.map_some]

/-- Boolean `PlainLopnBody` checker (per-instance discharge of the chain-plain
    side condition on the flag route). -/
def plainLopnBodyB (body : List LinstrRM) : Bool :=
  body.all (fun i => isLopnB i && (cmpArgs? i).isNone && (movRegArgs? i).isNone)

/-- The Boolean checker is sound for `PlainLopnBody`. -/
theorem plainLopnBodyB_sound {body : List LinstrRM} (h : plainLopnBodyB body = true) :
    PlainLopnBody body := by
  intro i hi
  have hb := List.all_eq_true.mp h i hi
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp hb
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
  exact ⟨isLopnB_isLopn h1, Option.isNone_iff_eq_none.mp h2,
    Option.isNone_iff_eq_none.mp h3⟩

/-! ## 2. The touched body and its per-trip pass (counter machine) -/

/-- **The invariant-touch loop body**: a restoring touch segment in front of
    the emitted `chain ++ writeback` pass.  The touch runs INSIDE every trip
    (between the back-edge and the chain), so the loop body writes
    invariant-tracked state mid-pass. -/
def loopBodyInvTouchMN {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w)) (nReg : String) (touch : List LinstrRM) : List LinstrRM :=
  touch ++ loopBodyFullMN update nReg

/-- Every element of the touched body is an `Lopn`, given the touch is. -/
theorem loopBodyInvTouchMN_isLopn {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w)) (nReg : String) (touch : List LinstrRM)
    (htouch : ∀ i ∈ touch, IsLopn i) :
    ∀ i ∈ loopBodyInvTouchMN update nReg touch, IsLopn i := by
  intro i hi
  rw [loopBodyInvTouchMN, List.mem_append] at hi
  rcases hi with hi | hi
  · exact htouch i hi
  · exact loopBodyFullMN_isLopn update nReg i hi

/-- **The per-trip pass of the touched body.**  One pass of
    `touch ++ chain ++ writeback` from any state agreeing with the trip-`t`
    valuation and holding a readable counter: the touch restores
    (`TouchRestoresMN`), then the pinned pass `loopBodyFullMN_trip` (never
    re-proved) steps the accumulator and decrements the counter. -/
theorem loopBodyInvTouchMN_trip {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htouch : TouchRestoresMN invTys w touch nReg)
    (invs : Ctxt.Valuation invTys) (t : Nat) (acc : BitVec w) (bt : LstateM)
    (hagree : StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt
      (tripValMN invs t acc))
    (vn : BitVec 64) (hn : bt.reg.getW nReg 64 = some vn) :
    ∃ bt', lsemStraightMem (loopBodyInvTouchMN update nReg touch) bt = some bt'
      ∧ StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt'
          (tripValMN invs (t + 1) (JLoopBodyN.stepC update invs t acc))
      ∧ bt'.reg.getW nReg 64 = some (vn - 1#64) := by
  obtain ⟨s1, hrunT, hAgT, hpres⟩ := htouch invs t acc bt hagree
  obtain ⟨bt', hrunB, hAg', hn'⟩ := loopBodyFullMN_trip update hupd nReg hna hnr
    invs t acc s1 hAgT vn (hpres.trans hn)
  refine ⟨bt', ?_, hAg', hn'⟩
  rw [loopBodyInvTouchMN, lsemStraightMem_append, hrunT, Option.bind_some]
  exact hrunB

/-- **The trip invariant of the touched body.**  Every `runBoundedLoopMem` trip
    state agrees with its trip valuation at the source fold, counter readable —
    the touch is denotationally transparent trip-to-trip. -/
theorem loopBodyInvTouchMN_inv {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htouch : TouchRestoresMN invTys w touch nReg)
    (invs : Ctxt.Valuation invTys) (s0 : LstateM) (acc0 : BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s0
      (tripValMN invs 0 acc0))
    (hn0 : (s0.reg.getW nReg 64).isSome) :
    ∀ t (bt : LstateM),
      runBoundedLoopMem (loopBodyInvTouchMN update nReg touch) t s0 = some bt →
      StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt
          (tripValMN invs t (JLoopBodyN.denote ⟨t, update⟩ invs acc0))
        ∧ (bt.reg.getW nReg 64).isSome := by
  intro t
  induction t with
  | zero =>
      intro bt hbt
      rw [runBoundedLoopMem_zero] at hbt
      obtain rfl := Option.some.inj hbt
      exact ⟨hseed, hn0⟩
  | succ k ih =>
      intro bt hbt
      rw [runBoundedLoopMem_succ_right] at hbt
      cases hbk : runBoundedLoopMem (loopBodyInvTouchMN update nReg touch) k s0 with
      | none => rw [hbk] at hbt; simp at hbt
      | some bk =>
          rw [hbk, Option.bind_some] at hbt
          obtain ⟨hAgk, hnk⟩ := ih bk hbk
          obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnk
          obtain ⟨bt', hbt', hAg', hn'⟩ := loopBodyInvTouchMN_trip update hupd nReg
            hna hnr touch htouch invs k (JLoopBodyN.denote ⟨k, update⟩ invs acc0)
            bk hAgk vn hvn
          rw [hbt', Option.map_some] at hbt
          obtain rfl := Option.some.inj hbt
          refine ⟨?_, ?_⟩
          · rw [JLoopBodyN.denote_succ]
            exact StoreAgreesM.setLpc hAg' 1
          · rw [show ((bt'.setLpc 1).reg).getW nReg 64 = bt'.reg.getW nReg 64 from
              LstateN.getW_congr_lvm (LstateM.reg_lvm_setLpc bt' 1) nReg 64, hn']
            rfl

/-! ## 3. The counter-machine export theorems (counter loop + while) -/

/-- **Counter-loop export faithfulness, invariant-touch body.**  As
    `loopMem_export_faithful_denote_uncond`, for the widened body
    `touch ++ chain ++ writeback`: the touch may write invariant-tracked state
    mid-pass; the only new hypotheses are the restoration discipline
    (`htouch`) and the touch's `Lopn` shape (`htLopn`).  Same conclusion — the
    machine run of the emitted loop decodes at the accumulator to the source
    fold `JLoopBodyN.denote`. -/
theorem loopMem_export_faithful_denote_invTouch {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update)
    (invs : Ctxt.Valuation invTys)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htLopn : ∀ i ∈ touch, IsLopn i)
    (htouch : TouchRestoresMN invTys w touch nReg)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (acc0 : BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s.base
      (tripValMN invs 0 acc0))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyInvTouchMN update nReg touch) (m - 1) s.base
      = some bprev)
    (hlast : lsemStraightMem (loopBodyInvTouchMN update nReg touch) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyInvTouchMN update nReg touch) m s.base
      = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi,
      runBoundedLoopMem (loopBodyInvTouchMN update nReg touch) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn
          (loopLinstrRM top nReg (loopBodyInvTouchMN update nReg touch)))
          (m * ((loopBodyInvTouchMN update nReg touch).length + 1)) s = some t
        ∧ decodeM t.base (accRegMN invTys) w
            = some (JLoopBodyN.denote ⟨m, update⟩ invs acc0) := by
  have hinv := loopBodyInvTouchMN_inv update hupd nReg hna hnr touch htouch invs
    s.base acc0 hseed hn0
  refine loopMem_export_faithful_denote update invs fn top nReg
    (loopBodyInvTouchMN update nReg touch)
    (loopBodyInvTouchMN_isLopn update nReg touch htLopn) s hfn hpc m hm
    bprev blast bfin hprev hlast hbfin htaken hhalt (accRegMN invTys) acc0 ?_ ?_
  · exact tripAgree_getW_acc hseed
  · intro t _ bt acct hbt hdec
    obtain ⟨hAgt, hnt⟩ := hinv t bt hbt
    obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnt
    have hacct : decodeM bt (accRegMN invTys) w
        = some (JLoopBodyN.denote ⟨t, update⟩ invs acc0) := tripAgree_getW_acc hAgt
    rw [hdec] at hacct
    obtain rfl := Option.some.inj hacct
    obtain ⟨bt', hbt', hAg', _⟩ := loopBodyInvTouchMN_trip update hupd nReg hna hnr
      touch htouch invs t _ bt hAgt vn hvn
    exact ⟨bt', hbt', tripAgree_getW_acc hAg'⟩

/-- **Counter-loop export faithfulness at `ComL.denote`, invariant-touch body.**  The
    touched loop realises the UNTOUCHED source node `ComL.forLoopNRt` — the
    restoring touch is denotationally transparent. -/
theorem loopMem_export_faithful_comL_invTouch {Γ : Ctxt jasminDialect} {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update)
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.reg w))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htLopn : ∀ i ∈ touch, IsLopn i)
    (htouch : TouchRestoresMN invTys w touch nReg)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s.base
      (tripValMN (Expr.lookupArgs invsV V) 0 (initV.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (count.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyInvTouchMN update nReg touch)
      ((count.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyInvTouchMN update nReg touch) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyInvTouchMN update nReg touch)
      (count.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (count.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyInvTouchMN update nReg touch) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn
          (loopLinstrRM top nReg (loopBodyInvTouchMN update nReg touch)))
          ((count.lookup V).toNat * ((loopBodyInvTouchMN update nReg touch).length + 1))
          s = some t
        ∧ decodeM t.base (accRegMN invTys) w
            = some ((ComL.forLoopNRt update count initV invsV (.ret .here)).denote V) := by
  rw [comL_forLoopNRt_ret_denote]
  exact loopMem_export_faithful_denote_invTouch update hupd (Expr.lookupArgs invsV V)
    fn top nReg hna hnr touch htLopn htouch s hfn hpc (initV.lookup V) hseed hn0 _ hm
    bprev blast bfin hprev hlast hbfin htaken hhalt

/-- **While export faithfulness at `ComL.denote`, invariant-touch body.**  The
    extension of `whileMem_export_faithful_comL_uncond` to the widened body: the
    countdown pass is `touch ++ chain ++ writeback` (the touch restores the
    tracked region and preserves the guard register per trip), and the per-trip
    simulation is DISCHARGED through the touched trip invariant.  Same
    conclusion — the emitted data-dependent while decodes to `ComL.whileNz`'s
    denotation. -/
theorem whileMem_export_faithful_comL_invTouch {Γ : Ctxt jasminDialect} {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update)
    (guardV : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.reg w))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (env : LeafEnvM) (fn : String) (top : LLabel) (gReg : String)
    (hna : ∀ j, gReg ≠ argName j) (hnr : ∀ k, gReg ≠ regName k)
    (touch : List LinstrRM) (htLopn : ∀ i ∈ touch, IsLopn i)
    (htouch : TouchRestoresMN invTys w touch gReg)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s.base
      (tripValMN (Expr.lookupArgs invsV V) 0 (initV.lookup V)))
    (hn0 : (s.base.reg.getW gReg 64).isSome)
    (fuel : Nat) (bfin : LstateM)
    (hhalt : runWhileMem env (fun b => condNZ b (.reg gReg))
      (loopBodyInvTouchMN update gReg touch) fuel s.base = some bfin)
    (htrip : whileTripsMem env (fun b => condNZ b (.reg gReg))
        (loopBodyInvTouchMN update gReg touch) fuel s.base = (guardV.lookup V).toNat) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env
          (singletonProgM fn
            (whileLinstrRM top gReg [] (loopBodyInvTouchMN update gReg touch)))
          (whileTripsMem env (fun b => condNZ b (.reg gReg))
              (loopBodyInvTouchMN update gReg touch) fuel s.base
            * (fuelCostC env (loopBodyInvTouchMN update gReg touch) + 1)) s = some t
        ∧ decodeM t.base (accRegMN invTys) w
            = some ((ComL.whileNz update guardV initV invsV (.ret .here)).denote V) := by
  have hlopn := loopBodyInvTouchMN_isLopn update gReg touch htLopn
  refine whileMem_export_faithful_comL update guardV initV invsV V env fn top gReg
    (loopBodyInvTouchMN update gReg touch)
    (fun i hi => Or.inl (hlopn i hi))
    s hfn hpc fuel bfin hhalt htrip (accRegMN invTys)
    (tripAgree_getW_acc hseed) ?_
  intro t _ bt acct hbt hdec
  rw [runBoundedLoopMemC_allLopn env _ hlopn] at hbt
  obtain ⟨hAgt, hnt⟩ := loopBodyInvTouchMN_inv update hupd gReg hna hnr touch htouch
    (Expr.lookupArgs invsV V) s.base (initV.lookup V) hseed hn0 t bt hbt
  obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnt
  have hacct : decodeM bt (accRegMN invTys) w
      = some (JLoopBodyN.denote ⟨t, update⟩ (Expr.lookupArgs invsV V)
          (initV.lookup V)) := tripAgree_getW_acc hAgt
  rw [hdec] at hacct
  obtain rfl := Option.some.inj hacct
  obtain ⟨bt', hbt', hAg', _⟩ := loopBodyInvTouchMN_trip update hupd gReg hna hnr
    touch htouch (Expr.lookupArgs invsV V) t _ bt hAgt vn hvn
  refine ⟨bt', ?_, tripAgree_getW_acc hAg'⟩
  rw [lsemStraightMemC_allLopn env _ hlopn]
  exact hbt'

/-! ## 4. The flag-machine trip machinery (`runStraightF` / `runBoundedStraightF`)

The flag route steps the touched body with the extended fold, so the touch may
contain flag-`CMP`s.  The emitted `chain`/`writeback` halves step through the
plain delegate (`runStraightF_plain`): the writeback's plainness is proved
below; the chain's is the decidable per-instance side condition
`PlainLopnBody (loopBodyChainMN update)` (checker: `plainLopnBodyB`). -/

/-- The canonical writeback is plain: three `ADD`/`SUB` `Lopn`s — no flag-`CMP`,
    no reg-copy `MOV`. -/
theorem loopWritebackMN_plain {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w)) (nReg : String) :
    PlainLopnBody (loopWritebackMN update nReg) := by
  intro i hi
  simp only [loopWritebackMN, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨⟨_, _, _, rfl⟩, by simp [cmpArgs?, withWidthTag], by simp [movRegArgs?]⟩
  · exact ⟨⟨_, _, _, rfl⟩, by simp [cmpArgs?, withWidthTag], by simp [movRegArgs?]⟩
  · exact ⟨⟨_, _, _, rfl⟩, by simp [cmpArgs?, withWidthTag], by simp [movRegArgs?]⟩

/-- The pinned pass is plain given the chain is (writeback half proved). -/
theorem loopBodyFullMN_plain {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w)) (nReg : String)
    (hchain : PlainLopnBody (loopBodyChainMN update)) :
    PlainLopnBody (loopBodyFullMN update nReg) := by
  intro i hi
  rw [loopBodyFullMN, List.mem_append] at hi
  rcases hi with hi | hi
  · exact hchain i hi
  · exact loopWritebackMN_plain update nReg i hi

/-- **The per-trip pass on the flag machine.**  One `runStraightF` pass of the
    touched body: the touch restores (flag discipline — it may set `zf`), the
    pinned `chain ++ writeback` steps through the plain delegate. -/
theorem loopBodyInvTouchMN_tripF {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htouch : TouchRestoresFMN invTys w touch nReg)
    (hchain : PlainLopnBody (loopBodyChainMN update))
    (invs : Ctxt.Valuation invTys) (t : Nat) (acc : BitVec w) (bt : LstateM)
    (hagree : StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt
      (tripValMN invs t acc))
    (vn : BitVec 64) (hn : bt.reg.getW nReg 64 = some vn) (zf : Bool) :
    ∃ bt' zb, runStraightF (loopBodyInvTouchMN update nReg touch) bt zf
        = some (bt', zb)
      ∧ StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt'
          (tripValMN invs (t + 1) (JLoopBodyN.stepC update invs t acc))
      ∧ bt'.reg.getW nReg 64 = some (vn - 1#64) := by
  obtain ⟨s1, zf1, hrunT, hAgT, hpres⟩ := htouch invs t acc bt zf hagree
  obtain ⟨bt', hrunB, hAg', hn'⟩ := loopBodyFullMN_trip update hupd nReg hna hnr
    invs t acc s1 hAgT vn (hpres.trans hn)
  refine ⟨bt', zf1, ?_, hAg', hn'⟩
  rw [loopBodyInvTouchMN, runStraightF_append, hrunT, Option.bind_some,
    runStraightF_plain _ (loopBodyFullMN_plain update nReg hchain) s1 zf1, hrunB,
    Option.map_some]

/-- Peel the LAST pass off the flag bounded fold. -/
theorem runBoundedStraightF_succ_right (body : List LinstrRM) (q : Nat) :
    ∀ (k : Nat) (s : LstateM),
      runBoundedStraightF body q (k + 1) s
        = (runBoundedStraightF body q k s).bind
            (fun b => (runStraightF body b false).map (fun bz => bz.1.setLpc q)) := by
  intro k
  induction k with
  | zero =>
      intro s
      rw [runBoundedStraightF_succ, runBoundedStraightF_zero, Option.bind_some]
      cases runStraightF body s false with
      | none => rfl
      | some bz => rw [Option.bind_some, Option.map_some, runBoundedStraightF_zero]
  | succ n ih =>
      intro s
      rw [runBoundedStraightF_succ, runBoundedStraightF_succ (k := n)]
      cases runStraightF body s false with
      | none => rfl
      | some bz =>
          rw [Option.bind_some, Option.bind_some]
          exact ih (bz.1.setLpc q)

/-- **The trip invariant on the flag machine.**  Every `runBoundedStraightF`
    trip state of the touched body agrees with its trip valuation at the
    source fold, counter readable. -/
theorem loopBodyInvTouchMN_invF {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htouch : TouchRestoresFMN invTys w touch nReg)
    (hchain : PlainLopnBody (loopBodyChainMN update))
    (invs : Ctxt.Valuation invTys) (q : Nat) (s0 : LstateM) (acc0 : BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s0
      (tripValMN invs 0 acc0))
    (hn0 : (s0.reg.getW nReg 64).isSome) :
    ∀ t (bt : LstateM),
      runBoundedStraightF (loopBodyInvTouchMN update nReg touch) q t s0 = some bt →
      StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt
          (tripValMN invs t (JLoopBodyN.denote ⟨t, update⟩ invs acc0))
        ∧ (bt.reg.getW nReg 64).isSome := by
  intro t
  induction t with
  | zero =>
      intro bt hbt
      rw [runBoundedStraightF_zero] at hbt
      obtain rfl := Option.some.inj hbt
      exact ⟨hseed, hn0⟩
  | succ k ih =>
      intro bt hbt
      rw [runBoundedStraightF_succ_right] at hbt
      cases hbk : runBoundedStraightF (loopBodyInvTouchMN update nReg touch) q k s0 with
      | none => rw [hbk] at hbt; simp at hbt
      | some bk =>
          rw [hbk, Option.bind_some] at hbt
          obtain ⟨hAgk, hnk⟩ := ih bk hbk
          obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnk
          obtain ⟨bt', zb, hbt', hAg', hn'⟩ := loopBodyInvTouchMN_tripF update hupd
            nReg hna hnr touch htouch hchain invs k
            (JLoopBodyN.denote ⟨k, update⟩ invs acc0) bk hAgk vn hvn false
          rw [hbt', Option.map_some] at hbt
          obtain rfl := Option.some.inj hbt
          refine ⟨?_, ?_⟩
          · rw [JLoopBodyN.denote_succ]
            exact StoreAgreesM.setLpc hAg' q
          · rw [getW_setLpc, hn']
            rfl

/-! ## 5. The flag-machine export theorems (the full `forLoopLcmdNRt` skeleton) -/

/-- **Flag-machine export faithfulness, invariant-touch body.**  The full
    emitted `forLoopLcmdNRt` loop skeleton (`guardedFlagLoopLinstrRM` —
    zero-trip guard at pc 0–1, `Llabel top` at 2, body at 3, flag back-edge +
    skip label behind) over the touched body, run by `lsemFuelMemF` from pc 0
    at a NONZERO runtime count: the machine halts (flag set) on a state whose
    accumulator decodes to the source fold `JLoopBodyN.denote ⟨m, update⟩`.
    The touch may write invariant-tracked registers AND set the flag mid-body
    (`TouchRestoresFMN`); the schedule (`hbound`/`htaken`/`hzero`) is at the
    shifted base pc 3, as in `guardedFlagLoop_runBounded_general` (never
    re-proved — this composes it with §4's trip invariant). -/
theorem guardedFlagLoop_export_faithful_denote_invTouch {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update)
    (invs : Ctxt.Valuation invTys)
    (fn : String) (top endL : LLabel) (nReg : String) (hne : top ≠ endL)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htLopn : ∀ i ∈ touch, IsLopn i)
    (htouch : TouchRestoresFMN invTys w touch nReg)
    (hchain : PlainLopnBody (loopBodyChainMN update))
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (acc0 : BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) b0
      (tripValMN invs 0 acc0))
    (v0 : BitVec 64) (hv0 : b0.reg.getW nReg 64 = some v0)
    (hv0ne : (v0 == 0#64) = false)
    (m : Nat) (hm : 0 < m) (bfin : LstateM)
    (hbound : runBoundedStraightF (loopBodyInvTouchMN update nReg touch) 3 m
      (b0.setLpc 3) = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi,
      runBoundedStraightF (loopBodyInvTouchMN update nReg touch) 3 i (b0.setLpc 3)
        = some bi →
      condNZ bi (.reg nReg) = true)
    (hzero : bfin.reg.getW nReg 64 = some 0#64) :
    ∃ (n : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (guardedFlagLoopLinstrRM top endL nReg (loopBodyInvTouchMN update nReg touch)))
          n { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeM t.prog.base (accRegMN invTys) w
            = some (JLoopBodyN.denote ⟨m, update⟩ invs acc0)
        ∧ t.zf = true := by
  have hseed3 : StoreAgreesM (invTys.length + 2) (invTys.length + 2) (b0.setLpc 3)
      (tripValMN invs 0 acc0) := StoreAgreesM.setLpc hseed 3
  have hn03 : ((b0.setLpc 3).reg.getW nReg 64).isSome := by
    rw [getW_setLpc, hv0]
    rfl
  have hinv := loopBodyInvTouchMN_invF update hupd nReg hna hnr touch htouch hchain
    invs 3 (b0.setLpc 3) acc0 hseed3 hn03 m bfin hbound
  have hdec : decodeM bfin (accRegMN invTys) w
      = some (JLoopBodyN.denote ⟨m, update⟩ invs acc0) := tripAgree_getW_acc hinv.1
  obtain ⟨n, t, hrun, hlvm, _hlarr, hzf⟩ := guardedFlagLoop_runBounded_general fn
    top endL nReg (loopBodyInvTouchMN update nReg touch)
    (loopBodyInvTouchMN_isLopn update nReg touch htLopn) hne b0 zf hpc v0 hv0 hv0ne
    m hm bfin hbound htaken hzero
  refine ⟨n, t, hrun, ?_, hzf⟩
  show t.prog.base.reg.getW (accRegMN invTys) w = _
  rw [LstateN.getW_congr_lvm hlvm]
  exact hdec

/-- **Flag-machine export faithfulness at `ComL.denote`, invariant-touch
    body.**  The touched flag-guarded loop realises the untouched source node
    `ComL.forLoopNRt` at trip count `(count.lookup V).toNat`. -/
theorem guardedFlagLoop_export_faithful_comL_invTouch {Γ : Ctxt jasminDialect}
    {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update)
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.reg w))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (fn : String) (top endL : LLabel) (nReg : String) (hne : top ≠ endL)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htLopn : ∀ i ∈ touch, IsLopn i)
    (htouch : TouchRestoresFMN invTys w touch nReg)
    (hchain : PlainLopnBody (loopBodyChainMN update))
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) b0
      (tripValMN (Expr.lookupArgs invsV V) 0 (initV.lookup V)))
    (v0 : BitVec 64) (hv0 : b0.reg.getW nReg 64 = some v0)
    (hv0ne : (v0 == 0#64) = false)
    (hm : 0 < (count.lookup V).toNat) (bfin : LstateM)
    (hbound : runBoundedStraightF (loopBodyInvTouchMN update nReg touch) 3
      (count.lookup V).toNat (b0.setLpc 3) = some bfin)
    (htaken : ∀ i, 0 < i → i < (count.lookup V).toNat → ∀ bi,
      runBoundedStraightF (loopBodyInvTouchMN update nReg touch) 3 i (b0.setLpc 3)
        = some bi →
      condNZ bi (.reg nReg) = true)
    (hzero : bfin.reg.getW nReg 64 = some 0#64) :
    ∃ (n : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (guardedFlagLoopLinstrRM top endL nReg (loopBodyInvTouchMN update nReg touch)))
          n { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeM t.prog.base (accRegMN invTys) w
            = some ((ComL.forLoopNRt update count initV invsV (.ret .here)).denote V)
        ∧ t.zf = true := by
  rw [comL_forLoopNRt_ret_denote]
  exact guardedFlagLoop_export_faithful_denote_invTouch update hupd
    (Expr.lookupArgs invsV V) fn top endL nReg hne hna hnr touch htLopn htouch hchain
    b0 zf hpc (initV.lookup V) hseed v0 hv0 hv0ne _ hm bfin hbound htaken hzero

/-! ## 6. Non-vacuity witnesses

Two touch segments a hand inspection confirms are OUTSIDE the pinned body class
(`loopBodyFullMN` has no instruction writing a tracked slot other than the
recognized writeback, and no flag-`CMP`), with their restoration proofs. -/

/-- **Witness 1 — accumulator save/clobber/restore.**  Saves the ACCUMULATOR
    argument register to a scratch `tmp`, overwrites it with a WRONG value
    (`acc + c`), then restores it — the middle instruction writes inside the
    invariant-tracked carrier region. -/
def accClobberTouch (invTys : Ctxt jasminDialect) (tmp : String) (c : Nat) :
    List LinstrRM :=
  [ (LinstrR.Lopn [.reg tmp] "ADD:64" [.reg (accRegMN invTys), .imm 0],
      MemTag.reg none)
  , (LinstrR.Lopn [.reg (accRegMN invTys)] "ADD:64"
      [.reg (accRegMN invTys), .imm c], MemTag.reg none)
  , (LinstrR.Lopn [.reg (accRegMN invTys)] "ADD:64" [.reg tmp, .imm 0],
      MemTag.reg none) ]

/-- Every witness-1 instruction is an `Lopn`. -/
theorem accClobberTouch_isLopn (invTys : Ctxt jasminDialect) (tmp : String) (c : Nat) :
    ∀ i ∈ accClobberTouch invTys tmp c, IsLopn i := by
  intro i hi
  simp only [accClobberTouch, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩

/-- Witness 1 is plain (three `ADD`s). -/
theorem accClobberTouch_plain (invTys : Ctxt jasminDialect) (tmp : String) (c : Nat) :
    PlainLopnBody (accClobberTouch invTys tmp c) := by
  intro i hi
  simp only [accClobberTouch, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨⟨_, _, _, rfl⟩, by simp [cmpArgs?, withWidthTag], by simp [movRegArgs?]⟩
  · exact ⟨⟨_, _, _, rfl⟩, by simp [cmpArgs?, withWidthTag], by simp [movRegArgs?]⟩
  · exact ⟨⟨_, _, _, rfl⟩, by simp [cmpArgs?, withWidthTag], by simp [movRegArgs?]⟩

/-- **Witness 1 restores.**  Under `tmp` hygiene (`tmp` untracked and distinct
    from the counter) the save/clobber/restore triple satisfies the counter
    discipline: the mid-segment state disagrees with the trip valuation at the
    accumulator slot (it holds `acc + c`), but the trip-boundary decode is
    restored. -/
theorem accClobberTouch_restores (invTys : Ctxt jasminDialect) (w : Nat)
    (tmp : String) (c : Nat) (nReg : String)
    (hta : ∀ j, tmp ≠ argName j) (htr : ∀ k, tmp ≠ regName k)
    (hnt : nReg ≠ tmp) (hnacc : nReg ≠ accRegMN invTys) :
    TouchRestoresMN invTys w (accClobberTouch invTys tmp c) nReg := by
  intro invs t acc s hag
  have hacc : s.reg.getW (accRegMN invTys) w = some acc := tripAgree_getW_acc hag
  -- save: `ADD tmp ← acc, #0`
  have h1 := lsemStepMem_add64Imm tmp (accRegMN invTys) 0 acc s hacc
  rw [show acc + BitVec.ofNat w 0 = acc from by simp] at h1
  have hAg1 : StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      ((s.setReg tmp acc).nextPc) (tripValMN invs t acc) :=
    StoreAgreesM.nextPc (StoreAgreesM.setReg_untracked tmp acc hta htr hag)
  -- clobber: `ADD acc ← acc, #c` — writes the TRACKED accumulator slot
  have hacc1 : ((s.setReg tmp acc).nextPc).reg.getW (accRegMN invTys) w = some acc :=
    tripAgree_getW_acc hAg1
  have h2 := lsemStepMem_add64Imm (accRegMN invTys) (accRegMN invTys) c acc
    ((s.setReg tmp acc).nextPc) hacc1
  have hAg2 : StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      ((((s.setReg tmp acc).nextPc).setReg (accRegMN invTys)
        (acc + BitVec.ofNat w c)).nextPc)
      (tripValMN invs t (acc + BitVec.ofNat w c)) :=
    StoreAgreesM.nextPc (tripAgree_setReg_acc hAg1 (acc + BitVec.ofNat w c))
  -- restore: `ADD acc ← tmp, #0`
  have htmp2 : ((((s.setReg tmp acc).nextPc).setReg (accRegMN invTys)
      (acc + BitVec.ofNat w c)).nextPc).reg.getW tmp w = some acc := by
    rw [LstateM.getW_setReg_nextPc_other _ _ _ _ _
        (show tmp ≠ accRegMN invTys from hta (invTys.length + 1)),
      LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc,
      LstateN.getW_setReg_same]
  have h3 := lsemStepMem_add64Imm (accRegMN invTys) tmp 0 acc
    ((((s.setReg tmp acc).nextPc).setReg (accRegMN invTys)
      (acc + BitVec.ofNat w c)).nextPc) htmp2
  rw [show acc + BitVec.ofNat w 0 = acc from by simp] at h3
  refine ⟨((((s.setReg tmp acc).nextPc.setReg (accRegMN invTys)
      (acc + BitVec.ofNat w c)).nextPc).setReg (accRegMN invTys) acc).nextPc,
    ?_, ?_, ?_⟩
  · rw [accClobberTouch, lsemStraightMem_cons_some h1, lsemStraightMem_cons_some h2,
      lsemStraightMem_cons_some h3, lsemStraightMem_nil]
  · exact StoreAgreesM.nextPc (tripAgree_setReg_acc hAg2 acc)
  · rw [LstateM.getW_setReg_nextPc_other _ _ _ _ _ hnacc,
      LstateM.getW_setReg_nextPc_other _ _ _ _ _ hnacc,
      LstateM.getW_setReg_nextPc_other _ _ _ _ _ hnt]

/-- Witness 1 restores on the flag machine (plain, so the flag threads). -/
theorem accClobberTouch_restoresF (invTys : Ctxt jasminDialect) (w : Nat)
    (tmp : String) (c : Nat) (nReg : String)
    (hta : ∀ j, tmp ≠ argName j) (htr : ∀ k, tmp ≠ regName k)
    (hnt : nReg ≠ tmp) (hnacc : nReg ≠ accRegMN invTys) :
    TouchRestoresFMN invTys w (accClobberTouch invTys tmp c) nReg :=
  TouchRestoresFMN_of_plain w _ nReg (accClobberTouch_plain invTys tmp c)
    (accClobberTouch_restores invTys w tmp c nReg hta htr hnt hnacc)

/-- **Witness 2 — an in-body flag-`CMP` on the tracked loop index.**  The
    emitted invariant-touch form: a `CMP` whose first operand READS the tracked
    loop-index register and whose step SETS the flag mid-body.  Steps only on
    the flag machine (`lsemStraightMem` has no `CMP` arm). -/
def cmpIdxTouch (invTys : Ctxt jasminDialect) (dst : String) (k : Nat) :
    List LinstrRM :=
  [ (LinstrR.Lopn [.reg dst] (withWidthTag 64 "CMP") [.reg (idxRegMN invTys), .imm k],
      MemTag.reg none) ]

/-- Every witness-2 instruction is an `Lopn`. -/
theorem cmpIdxTouch_isLopn (invTys : Ctxt jasminDialect) (dst : String) (k : Nat) :
    ∀ i ∈ cmpIdxTouch invTys dst k, IsLopn i := by
  intro i hi
  simp only [cmpIdxTouch, List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain rfl := hi
  exact ⟨_, _, _, rfl⟩

/-- **Witness 2 restores (flag machine).**  The `CMP` reads the tracked index,
    sets the flag, and leaves the store untouched — restoration is immediate,
    the exit flag is the comparison's result. -/
theorem cmpIdxTouch_restoresF (invTys : Ctxt jasminDialect) (w : Nat)
    (dst : String) (k : Nat) (nReg : String) :
    TouchRestoresFMN invTys w (cmpIdxTouch invTys dst k) nReg := by
  intro invs t acc s zf hag
  have hidx : s.reg.getW (idxRegMN invTys) 64 = some (BitVec.ofNat 64 t) :=
    tripAgree_getW_idx hag
  refine ⟨s.nextPc, BitVec.ofNat 64 t == BitVec.ofNat 64 k, ?_,
    StoreAgreesM.nextPc hag, ?_⟩
  · rw [cmpIdxTouch, runStraightF_cons]
    have hstep : fstepF
        (LinstrR.Lopn [.reg dst] (withWidthTag 64 "CMP")
          [.reg (idxRegMN invTys), .imm k], MemTag.reg none) s zf
        = some (s.nextPc, BitVec.ofNat 64 t == BitVec.ofNat 64 k) := by
      unfold fstepF
      rw [show cmpArgs? (LinstrR.Lopn [.reg dst] (withWidthTag 64 "CMP")
            [.reg (idxRegMN invTys), .imm k], MemTag.reg none)
          = some (.reg (idxRegMN invTys), .imm k) from by simp [cmpArgs?]]
      simp only []
      rw [show evalOperandN s.reg 64 (.reg (idxRegMN invTys))
          = some (BitVec.ofNat 64 t) from hidx]
      rfl
    rw [hstep, Option.bind_some, runStraightF_nil]
  · rw [LstateM.reg_nextPc, LstateN.getW_nextPc]

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagInvTouch
