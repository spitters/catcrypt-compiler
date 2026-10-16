/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift
public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Blocks
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame

/-!
# The basic-block optimiser on whole bodies of the flag machine

`LprogOptPipeline.optimizeBasicBlocks` applies `optRunBody` to every straight segment of
the partition `splitStraightRuns` of a body and keeps every other segment. This module
instantiates the lift of block-local rewrites `CfgLift.lsemFuelMemFk_blockRel` at a body
transform applied to the straight segments, and supplies the per-segment condition of the
stages of `optRunBody` on the fragment with flags `LsemBridge.fragFB`.

## Main definitions

* `mapStraightRuns f` — the transform `f` applied to every straight segment.
* `SegOK ck Inv tag f seg` — the per-segment condition: `f seg` is at most as long, both
  are `Lopn` segments, and `f seg` simulates `seg` (`CfgLift.BlockSim`).
* `WholeBodySim ck Inv fn B B'` — the whole-body statement: a halting run of the checked
  machine on `B` from program counter `0` is matched by a halting run of `B'` with at most
  the same fuel.
* `RelInv A` — the invariant of the bridge: the base is related, with its flags, to a
  uniform-width state.

## Main results

* `mapStraightRuns_lsemFuelMemF`, `optimizeBasicBlocks_lsemFuelMemF` — the whole-body
  statement of a transform applied to the straight segments, and of the optimiser.
* `runIBF_of_segIdxOk` — on the fragment with flags, the in-bounds condition of the checked
  machine gives the in-bounds run of the bridge `LsemBridge.runIBF`.
* `copyPropagateBody_segOK`, `optRunBody_segOK` — the per-segment condition of copy
  propagation and of the five stages on the fragment with flags;
  `copyPropagateBody_lsemFuelMemF` — copy propagation on whole bodies.
* `optRunBody_segOK_of_idxFree`, `optRunBody_segOK_of_cmp` — the five stages on a segment of
  the fragment with flags without indexed access in its optimised form, and on a compare
  segment. The decidable check of the optimiser on a body, `optBlocksOKB`, and its soundness
  `optBlocksOKB_sound` are in `X86Backend.OptBlocksComplete`, after the proof of copy
  propagation for register facts (`CopyPropCfg`) that its register-copy disjunct uses.
* `fstepF_transport`, `fstepF_swap`, `scheduleBody_runStraightF` — the scheduler over the
  extended straight fold `runStraightF`, on every body, with no condition on widths.
* `fstepF_reload`, `heldSoundM_step`, `elimAux_runStraightF` — store-to-load forwarding over
  `runStraightF`, on bodies whose destinations are registers (`dstsRegB`).
* `scheduleBody_segOK`, `elimReloads_segOK`, `scheduleBody_lsemFuelMemF`,
  `elimReloads_lsemFuelMemF` — the two passes on a segment and on whole bodies, under
  `keepOKB` (and `dstsRegB` for forwarding), with the trivial invariant.
* `reloadElimBody_runStraightF`, `loadCSE_runStraightF`, with `reloadElimBody_segOK`,
  `loadCSE_segOK`, `reloadElimBody_lsemFuelMemF`, `loadCSE_lsemFuelMemF` — spill-pair
  reload elimination and load CSE over `runStraightF` and on whole bodies.
* `CopyPropSim`, `optRunBody_runStraightF`, `optRunBody_segOK_of_copyPropSim`,
  `optimizeBasicBlocks_wholeBodySim_of_copyPropSim` — the five stages and the optimiser
  over `runStraightF`, given the statement of copy propagation on each segment.
* `copyPropagateBody_eq_of_noMove`, `optBlocksMoveFreeOKB`, `optBlocksMoveFreeOKB_sound` —
  copy propagation is the identity on a body with no candidate move, and the optimiser on
  such a body under one decidable check, with the trivial invariant.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad (elimReloads elimReloads_length_le)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler (scheduleBody scheduleBody_length)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (copyPropagateBody copyPropagateBody_length_le)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptBlocksMemF (lstateN_ext lstateM_ext)
open CatCrypt.Crypto.Optimizer.LoadCSE
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyProp
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.StoreToLoad
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Scheduler
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Blocks

/-! ## 1. A pass applied to the straight segments of a body -/

/-- A body transform `f` applied to every straight segment of the partition
    `splitStraightRuns`; every other segment is kept. -/
def mapStraightRuns (f : List Linstr → List Linstr) (body : List Linstr) : List Linstr :=
  ((splitStraightRuns body).map fun seg => if bodyIsStraightLine seg then f seg else seg).flatten

theorem optimizeBasicBlocks_eq_mapStraightRuns (body : List Linstr) :
    optimizeBasicBlocks body = mapStraightRuns optRunBody body := rfl

section Lift

variable {ck : Bool} {Inv : LstateM → Prop}

/-- The side conditions of a body transform `f` on one straight segment: the output is at
    most as long, both segments are `Lopn` segments, and the output simulates the input. -/
def SegOK (ck : Bool) (Inv : LstateM → Prop) (tag : LinstrR → MemTag)
    (f : List Linstr → List Linstr) (seg : List Linstr) : Prop :=
  (f seg).length ≤ seg.length
    ∧ (∀ i ∈ seg, IsLopn (i.li_i, tag i.li_i))
    ∧ (∀ i ∈ f seg, IsLopn (i.li_i, tag i.li_i))
    ∧ BlockSim ck Inv (seg.map fun i => (i.li_i, tag i.li_i))
        ((f seg).map fun i => (i.li_i, tag i.li_i))

/-- **The block relation of a pass applied to the straight segments.** Let every
    instruction of the body pass `keepOKB` and every straight segment of the partition
    satisfy `SegOK`. The tagged body and the tagged transformed body are related by
    `BlockRel`. -/
theorem mapStraightRuns_blockRel (tag : LinstrR → MemTag) (f : List Linstr → List Linstr)
    (body : List Linstr)
    (hkeep : ∀ i ∈ body, keepOKB (i.li_i, tag i.li_i) = true)
    (hseg : ∀ seg ∈ splitStraightRuns body, bodyIsStraightLine seg = true →
      SegOK ck Inv tag f seg) :
    BlockRel ck Inv (body.map fun i => (i.li_i, tag i.li_i))
      ((mapStraightRuns f body).map fun i => (i.li_i, tag i.li_i)) := by
  have e1 : (body.map fun i => (i.li_i, tag i.li_i))
      = ((splitStraightRuns body).map
          (fun seg => seg.map fun i => (i.li_i, tag i.li_i))).flatten := by
    rw [← List.map_flatten, splitStraightRuns_flatten]
  have e2 : ((mapStraightRuns f body).map fun i => (i.li_i, tag i.li_i))
      = ((splitStraightRuns body).map
          (fun seg => (if bodyIsStraightLine seg then f seg else seg).map
            fun i => (i.li_i, tag i.li_i))).flatten := by
    rw [mapStraightRuns, List.map_flatten, List.map_map]
    rfl
  rw [e1, e2]
  refine BlockRel.of_segs _ _ _ (fun seg hs => ?_)
  obtain ⟨hne, hgood⟩ := splitStraightRuns_good body seg hs
  by_cases hsl : bodyIsStraightLine seg = true
  · obtain ⟨h1, h2, h3, h4⟩ := hseg seg hs hsl
    right
    simp only [if_pos hsl]
    refine ⟨by simpa using hne, by simpa using h1, ?_, ?_, h4⟩
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
      exact h2 j hj
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
      exact h3 j hj
  · left
    refine ⟨by simp [hsl], fun i hi => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    rcases hgood with ⟨c, rfl, hc⟩ | hst
    · obtain rfl : j = c := by simpa using hj
      refine ctlKeep_of_keepOKB (hkeep j ?_) (fun d o srcs hd => ?_)
      · rw [← splitStraightRuns_flatten body]
        exact List.mem_flatten.2 ⟨[j], hs, hj⟩
      · have hd' : j.li_i = LinstrR.Lopn d o srcs := hd
        simp [isCtlInstr, hd'] at hc
    · exact absurd hst hsl

/-- **A pass applied to the straight segments, on whole bodies of the flag machine.**
    Under the hypotheses of `mapStraightRuns_blockRel` and an invariant independent of the
    program counter, every halting run of the checked machine on the tagged body from
    program counter `0` is matched by a halting run of the tagged transformed body from the
    same state with at most the same fuel; the final states have the same function name
    and zero flag and bases equal up to the program counter. -/
theorem mapStraightRuns_lsemFuelMemF (tag : LinstrR → MemTag)
    (f : List Linstr → List Linstr) (body : List Linstr)
    (hpc : ∀ a p, Inv a → Inv (a.setLpc p))
    (hkeep : ∀ i ∈ body, keepOKB (i.li_i, tag i.li_i) = true)
    (hseg : ∀ seg ∈ splitStraightRuns body, bodyIsStraightLine seg = true →
      SegOK ck Inv tag f seg)
    (fn : String) {fuel : Nat} {s t : LstateMF} (h0 : s.prog.base.lpc = 0)
    (hInv : Inv s.prog.base)
    (h : lsemFuelMemFk ck (singletonProgM fn (body.map fun i => (i.li_i, tag i.li_i)))
      fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel
      ∧ lsemFuelMemF (singletonProgM fn
          ((mapStraightRuns f body).map fun i => (i.li_i, tag i.li_i))) fuel' s = some t'
      ∧ t'.prog.lfn = t.prog.lfn ∧ t'.zf = t.zf ∧ EqPc t.prog.base t'.prog.base
      ∧ Inv t.prog.base := by
  have hB := mapStraightRuns_blockRel tag f body hkeep hseg
  exact lsemFuelMemF_blockRel_entry
    (P := singletonProgM fn (body.map fun i : Linstr => (i.li_i, tag i.li_i)))
    (P' := singletonProgM fn
      ((mapStraightRuns f body).map fun i : Linstr => (i.li_i, tag i.li_i)))
    (show fn = fn from rfl) hpc hB h0 hInv h

/-- A straight segment that `f` keeps satisfies `SegOK`, when it is an `Lopn` segment whose
    steps preserve `Inv`. -/
theorem segOK_of_eq (tag : LinstrR → MemTag) (f : List Linstr → List Linstr)
    (seg : List Linstr) (he : f seg = seg)
    (hl : ∀ i ∈ seg, IsLopn (i.li_i, tag i.li_i))
    (hI : ∀ i ∈ seg, ∀ (s t : LstateM) (zf zt : Bool), Inv s →
      fstepF (i.li_i, tag i.li_i) s zf = some (t, zt) → Inv t) :
    SegOK ck Inv tag f seg := by
  refine ⟨by rw [he], hl, by rw [he]; exact hl, ?_⟩
  rw [he]
  refine BlockSim.of_steps (fun i hi => ?_)
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  exact hI j hj

/-- The statement of a whole-body simulation: every halting run of the checked machine on
    `B` from program counter `0` and a state of `Inv` is matched by a halting run of `B'`
    from the same state with at most the same fuel; the final states have the same
    function name and zero flag and bases equal up to the program counter, and `Inv` holds
    at the final state of `B`. -/
def WholeBodySim (ck : Bool) (Inv : LstateM → Prop) (fn : String)
    (B B' : List LinstrRM) : Prop :=
  ∀ {fuel : Nat} {s t : LstateMF}, s.prog.base.lpc = 0 → Inv s.prog.base →
    lsemFuelMemFk ck (singletonProgM fn B) fuel s = some t →
    ∃ fuel' t', fuel' ≤ fuel ∧ lsemFuelMemF (singletonProgM fn B') fuel' s = some t'
      ∧ t'.prog.lfn = t.prog.lfn ∧ t'.zf = t.zf ∧ EqPc t.prog.base t'.prog.base
      ∧ Inv t.prog.base

/-- **The basic-block optimiser on whole bodies of the flag machine**, under `keepOKB` on
    the body and `SegOK` of `optRunBody` on every straight segment of the partition. -/
theorem optimizeBasicBlocks_lsemFuelMemF (tag : LinstrR → MemTag) (body : List Linstr)
    (hpc : ∀ a p, Inv a → Inv (a.setLpc p))
    (hkeep : ∀ i ∈ body, keepOKB (i.li_i, tag i.li_i) = true)
    (hseg : ∀ seg ∈ splitStraightRuns body, bodyIsStraightLine seg = true →
      SegOK ck Inv tag optRunBody seg) (fn : String) :
    WholeBodySim ck Inv fn (body.map fun i => (i.li_i, tag i.li_i))
      ((optimizeBasicBlocks body).map fun i => (i.li_i, tag i.li_i)) :=
  fun h0 hInv h => mapStraightRuns_lsemFuelMemF tag optRunBody body hpc hkeep hseg fn h0 hInv h

end Lift

/-! ## 2. The length of the optimised segment -/

theorem reloadElimBody_length_le (b : Lcmd) : (reloadElimBody b).length ≤ b.length := by
  unfold reloadElimBody
  split
  · exact (dropReloadsLcmd_sublist b).length_le
  · exact Nat.le_refl _

/-- The five stages never lengthen a body. -/
theorem optRunBody_length_le (body : List Linstr) :
    (optRunBody body).length ≤ body.length := by
  unfold optRunBody
  split
  · rw [loadCSE_length]
    refine (copyPropagateBody_length_le _).trans ?_
    rw [scheduleBody_length]
    exact (reloadElimBody_length_le _).trans (elimReloads_length_le body)
  · exact Nat.le_refl _

/-! ## 3. Segments of the fragment with flags -/

/-- The invariant of the bridge: the base is related, with its flags, to a uniform-width
    state. -/
def RelInv (A : String → Option Nat) (s : LstateM) : Prop := ∃ l, LsemRelF A s l

theorem relInv_setLpc {A : String → Option Nat} (a : LstateM) (p : Nat)
    (h : RelInv A a) : RelInv A (a.setLpc p) := by
  obtain ⟨l, hr⟩ := h
  exact ⟨{ l with lpc := p }, ⟨⟨hr.regs, rfl, hr.arrs⟩, hr.cf, hr.of⟩⟩

/-- On an instruction of the fragment with flags and related states, the in-bounds
    condition of the checked machine is the in-bounds condition of the bridge. -/
theorem inBoundsB_of_baseIdxOk {A : String → Option Nat} {i : LinstrRM}
    (hi : fragFB A i = true) {s : LstateM} {l : Lstate 64} (hr : LsemRel A s l)
    (h : baseIdxOk i s = true) : inBoundsB l i = true := by
  obtain ⟨sh, rfl, -⟩ := fragFB_shape hi
  cases sh with
  | plain sh =>
      cases sh with
      | alu d m a b => rfl
      | movImm d k => rfl
      | load d B x n =>
          simpa [baseIdxOk, idxOkB, idxBelowB, loadStruct?, ShapeF.toInstr, Shape.toInstr,
            inBoundsB, hr.getW x] using h
      | store B x v n =>
          simpa [baseIdxOk, idxOkB, idxBelowB, storeStruct?, ShapeF.toInstr, Shape.toInstr,
            inBoundsB, hr.getW x] using h
  | carry op d a b => rfl
  | mov2 d x b => rfl
  | mulx lo hi b => cases b <;> rfl

/-- **The in-bounds run of the bridge from the in-bounds condition of the checked
    machine.** On a segment of the fragment with flags and related states, `SegIdxOk`
    gives a successful in-bounds run `runIBF`. -/
theorem runIBF_of_segIdxOk {A : String → Option Nat} :
    ∀ (seg : List LinstrRM), (∀ i ∈ seg, fragFB A i = true) →
      ∀ (s : LstateM) (l : Lstate 64) (zf : Bool), LsemRelF A s l → SegIdxOk seg s zf →
        (runIBF seg l).isSome := by
  intro seg
  induction seg with
  | nil => intro _ s l zf _ _; rfl
  | cons i is ih =>
      intro hf s l zf hr hok
      have hi := hf i List.mem_cons_self
      have hb := inBoundsB_of_baseIdxOk hi hr.toLsemRel hok.1
      obtain ⟨s1, l1, hs1, hl1, hr1, -, -⟩ := lsemStepFlag_stepMemF_rel hi hr hb
      obtain ⟨-, hc, hm⟩ := fragFB_plain hi
      have hst : fstepF i s zf = some (s1, zf) := by
        unfold fstepF
        rw [hc, hm, hs1]
        rfl
      have := ih (fun j hj => hf j (List.mem_cons_of_mem _ hj)) s1 l1 zf hr1 (hok.2 s1 zf hst)
      simpa [runIBF, stepIBF, hb, hl1] using this

/-- A tagged body of the fragment with flags is a plain `Lopn` body. -/
theorem plainLopnBody_of_fragFB {A : String → Option Nat} (tag : LinstrR → MemTag)
    (b : List Linstr) (h : ∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true) :
    PlainLopnBody (b.map fun i => (i.li_i, tag i.li_i)) := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  exact fragFB_plain (h j hj)

/-- **The segment simulation of a pass on the fragment with flags.** Let `seg` and `f seg`
    be bodies of the fragment with flags, let the in-bounds run of `f seg` succeed
    wherever the in-bounds run of `seg` does, and let the two bodies run under
    `lsemStraightMemF`, from a state related to a state whose in-bounds runs succeed, to
    states with the same register map, arrays, word memory and flags. Then `f seg`
    simulates `seg` under the invariant `RelInv A`, with the in-bounds premise of the
    checked machine. -/
theorem blockSim_of_fragFB {A : String → Option Nat} (tag : LinstrR → MemTag)
    (f : List Linstr → List Linstr) (seg : List Linstr)
    (hfrag : ∀ i ∈ seg, fragFB A (i.li_i, tag i.li_i) = true)
    (hfrag' : ∀ i ∈ f seg, fragFB A (i.li_i, tag i.li_i) = true)
    (hib' : ∀ l, (runIBF (seg.map fun i => (i.li_i, tag i.li_i)) l).isSome →
      (runIBF ((f seg).map fun i => (i.li_i, tag i.li_i)) l).isSome)
    (hpass : ∀ (s : LstateM) (l : Lstate 64), LsemRelF A s l →
      (runIBF (seg.map fun i => (i.li_i, tag i.li_i)) l).isSome →
      (runIBF ((f seg).map fun i => (i.li_i, tag i.li_i)) l).isSome →
      ∃ u u', lsemStraightMemF ((f seg).map fun i => (i.li_i, tag i.li_i)) s = some u ∧
        lsemStraightMemF (seg.map fun i => (i.li_i, tag i.li_i)) s = some u' ∧
        u.reg.lvm = u'.reg.lvm ∧ u.larr = u'.larr ∧ u.lmem = u'.lmem ∧
        u.cf = u'.cf ∧ u.of = u'.of) :
    BlockSim true (RelInv A) (seg.map fun i => (i.li_i, tag i.li_i))
      ((f seg).map fun i => (i.li_i, tag i.li_i)) := by
  have hB : ∀ i ∈ seg.map (fun i => (i.li_i, tag i.li_i)), fragFB A i = true := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    exact hfrag j hj
  refine BlockSim.of_plain (plainLopnBody_of_fragFB tag seg hfrag)
    (plainLopnBody_of_fragFB tag (f seg) hfrag') (fun s t zf hI hok ht => ?_)
  obtain ⟨l, hr⟩ := hI
  have hib := runIBF_of_segIdxOk _ hB s l zf hr (hok rfl)
  obtain ⟨u, u', hu, hu', h1, h2, h3, h4, h5⟩ := hpass s l hr hib (hib' l hib)
  rw [ht] at hu'
  obtain rfl := Option.some.inj hu'
  obtain ⟨s', l', hs', -, hr', -, -⟩ := lsemStraightFlag_lsemStraightMemF_rel _ s l hB hr hib
  rw [ht] at hs'
  obtain rfl := Option.some.inj hs'
  refine ⟨u, hu, ?_, ⟨l', hr'⟩⟩
  exact lstateM_ext (lstateN_ext h1 rfl) h2 h3 h4 h5

/-! ## 4. The passes -/

/-- **Copy propagation on a segment of the fragment with flags**, where the output is in
    the fragment and its in-bounds run succeeds wherever that of the input does. -/
theorem copyPropagateBody_segOK {A : String → Option Nat} (tag : LinstrR → MemTag)
    (seg : List Linstr) (hfrag : ∀ i ∈ seg, fragFB A (i.li_i, tag i.li_i) = true)
    (hfrag' : ∀ i ∈ copyPropagateBody seg, fragFB A (i.li_i, tag i.li_i) = true)
    (hib' : ∀ l, (runIBF (seg.map fun i => (i.li_i, tag i.li_i)) l).isSome →
      (runIBF ((copyPropagateBody seg).map fun i => (i.li_i, tag i.li_i)) l).isSome) :
    SegOK true (RelInv A) tag copyPropagateBody seg :=
  ⟨copyPropagateBody_length_le seg, fun i hi => (fragFB_plain (hfrag i hi)).1,
    fun i hi => (fragFB_plain (hfrag' i hi)).1,
    blockSim_of_fragFB tag copyPropagateBody seg hfrag hfrag' hib'
      (fun _ _ hr hib hib2 => copyPropagateBody_lsemStraightMemF_F tag seg hfrag hfrag' hr
        hib hib2)⟩

/-- **The five stages on a segment of the fragment with flags**, where the scheduled and
    copy-propagated segment is in the fragment and its in-bounds run succeeds wherever
    that of the input does. -/
theorem optRunBody_segOK {A : String → Option Nat} (tag : LinstrR → MemTag)
    (seg : List Linstr) (hfrag : ∀ i ∈ seg, fragFB A (i.li_i, tag i.li_i) = true)
    (hfrag' : ∀ i ∈ copyPropagateBody (scheduleBody seg),
      fragFB A (i.li_i, tag i.li_i) = true)
    (hib' : ∀ l, (runIBF (seg.map fun i => (i.li_i, tag i.li_i)) l).isSome →
      (runIBF ((copyPropagateBody (scheduleBody seg)).map
        fun i => (i.li_i, tag i.li_i)) l).isSome) :
    SegOK true (RelInv A) tag optRunBody seg := by
  have hout : ∀ i ∈ optRunBody seg, fragFB A (i.li_i, tag i.li_i) = true := by
    rcases optRunBody_eq_of_fragFB tag seg hfrag hfrag' with e | e <;> rw [e]
    · exact hfrag'
    · exact hfrag
  refine ⟨optRunBody_length_le seg, fun i hi => (fragFB_plain (hfrag i hi)).1,
    fun i hi => (fragFB_plain (hout i hi)).1,
    blockSim_of_fragFB tag optRunBody seg hfrag hout (fun l h => ?_)
      (fun s l hr hib _ => optRunBody_lsemStraightMemF_F tag seg hfrag hfrag' hr hib
        (hib' l hib))⟩
  rcases optRunBody_eq_of_fragFB tag seg hfrag hfrag' with e | e <;> rw [e]
  · exact hib' l h
  · exact h

/-! ## 5. The passes on whole bodies -/

/-- **Copy propagation on whole bodies of the flag machine**: applied to the straight
    segments of a body that passes `keepOKB`, with every straight segment and its
    copy-propagated form in the fragment with flags, and the copy-propagated form in
    bounds wherever its input is. -/
theorem copyPropagateBody_lsemFuelMemF {A : String → Option Nat} (tag : LinstrR → MemTag)
    (body : List Linstr) (hkeep : ∀ i ∈ body, keepOKB (i.li_i, tag i.li_i) = true)
    (hfrag : ∀ seg ∈ splitStraightRuns body, bodyIsStraightLine seg = true →
      (∀ i ∈ seg, fragFB A (i.li_i, tag i.li_i) = true)
      ∧ (∀ i ∈ copyPropagateBody seg, fragFB A (i.li_i, tag i.li_i) = true)
      ∧ ∀ l, (runIBF (seg.map fun i => (i.li_i, tag i.li_i)) l).isSome →
        (runIBF ((copyPropagateBody seg).map fun i => (i.li_i, tag i.li_i)) l).isSome)
    (fn : String) :
    WholeBodySim true (RelInv A) fn (body.map fun i => (i.li_i, tag i.li_i))
      ((mapStraightRuns copyPropagateBody body).map fun i => (i.li_i, tag i.li_i)) :=
  fun h0 hInv h => mapStraightRuns_lsemFuelMemF tag copyPropagateBody body relInv_setLpc hkeep
    (fun seg hs hsl => copyPropagateBody_segOK tag seg (hfrag seg hs hsl).1
      (hfrag seg hs hsl).2.1 (hfrag seg hs hsl).2.2) fn h0 hInv h

/-! ## 6. Segments without indexed access and compare segments -/

/-- On a body with no indexed access the in-bounds run is the run with flags. -/
theorem runIBF_eq_of_noArrIdx :
    ∀ (b : List LinstrRM), (∀ i ∈ b, LprogScheduler.hasArrIdx i.1 = false) →
      ∀ l, runIBF b l = lsemStraightFlag b l := by
  intro b
  induction b with
  | nil => intro _ l; rfl
  | cons i is ih =>
      intro h l
      obtain ⟨w, t⟩ := i
      have hb : inBoundsB l (w, t) = true :=
        inBoundsB_of_hasArrIdx (h (w, t) List.mem_cons_self) t l
      simp only [runIBF, stepIBF, hb, if_true, lsemStraightFlag_cons]
      cases lsemStepFlag (w, t) l with
      | none => rfl
      | some l1 => simpa using ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) l1

/-- **The five stages on a segment of the fragment with flags whose optimised form has no
    indexed access.** -/
theorem optRunBody_segOK_of_idxFree {A : String → Option Nat} (tag : LinstrR → MemTag)
    (seg : List Linstr) (hfrag : ∀ i ∈ seg, fragFB A (i.li_i, tag i.li_i) = true)
    (hfrag' : ∀ i ∈ copyPropagateBody (scheduleBody seg),
      fragFB A (i.li_i, tag i.li_i) = true)
    (hidx : ∀ i ∈ copyPropagateBody (scheduleBody seg),
      LprogScheduler.hasArrIdx i.li_i = false) :
    SegOK true (RelInv A) tag optRunBody seg := by
  refine optRunBody_segOK tag seg hfrag hfrag' (fun l h => ?_)
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 h
  have h1 := runIBF_lsemStraightFlag _ l t ht
  rw [← scheduleBody_lsemStraightFlag] at h1
  obtain ⟨t₂, h2, -⟩ := copyPropagateBody_lsemStraightFlag tag tag (scheduleBody seg) l t h1
  rw [runIBF_eq_of_noArrIdx _ (fun i hi => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    exact hidx j hj), h2]
  rfl

/-- An instruction the flag-`CMP` recognizer accepts is an `Lopn`. -/
theorem isLopn_of_cmpArgs {i : LinstrRM} (h : (cmpArgs? i).isSome = true) : IsLopn i := by
  unfold cmpArgs? at h
  split at h
  · next d opn a b heq => exact ⟨_, _, _, heq⟩
  · simp at h

/-- **The compare step preserves the invariant of the bridge**: it writes the zero flag
    and advances the program counter. -/
theorem relInv_fstepF_cmp {A : String → Option Nat} {i : LinstrRM}
    (hc : (cmpArgs? i).isSome = true) {s t : LstateM} {zf zt : Bool} (hI : RelInv A s)
    (h : fstepF i s zf = some (t, zt)) : RelInv A t := by
  unfold fstepF at h
  cases hcm : cmpArgs? i with
  | none => simp [hcm] at hc
  | some ab =>
      obtain ⟨a, b⟩ := ab
      rw [hcm] at h
      simp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact relInv_setLpc s (s.lpc + 1) hI
      · simp at h

/-- **A compare segment under the five stages.** A segment of flag-`CMP` instructions that
    is not a modelled body is kept by `optRunBody` and preserves the invariant. -/
theorem optRunBody_segOK_of_cmp {A : String → Option Nat} (tag : LinstrR → MemTag)
    (seg : List Linstr) (hm : bodyAllModeled seg = false)
    (hc : ∀ i ∈ seg, (cmpArgs? (i.li_i, tag i.li_i)).isSome = true) :
    SegOK true (RelInv A) tag optRunBody seg :=
  segOK_of_eq tag optRunBody seg (by simp [optRunBody, hm])
    (fun i hi => isLopn_of_cmpArgs (hc i hi))
    (fun i hi _ _ _ _ hI h => relInv_fstepF_cmp (hc i hi) hI h)

/-! ## 7. The scheduler over the extended straight fold -/

section StraightF

open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.X86Backend.OptBlocksMemF

/-- An operand read by an instruction evaluates to the same word in two states that agree
    on the hazard tokens of the instruction. -/
theorem evalOperandN_agree {i : LinstrR} {s t : LstateM} (h : Agree i s t) {o : LOperand}
    (ho : srcTok o ∈ readToksSem i) (w : Nat) :
    evalOperandN t.reg w o = evalOperandN s.reg w o := by
  cases o with
  | reg r =>
      simp only [evalOperandN, LstateN.getW]
      rw [h.reg r (mem_T_read ho)]
  | _ => rfl

/-- The flag-`CMP` touches the flags. -/
theorem touchesFlags_of_cmpArgs {i : LinstrRM} (h : (cmpArgs? i).isSome = true) :
    touchesFlags i.1 = true := by
  unfold cmpArgs? at h
  split at h
  · next d opn a b heq =>
      split at h
      · next ho =>
          rw [heq, ho]
          show (!flagFree (withWidthTag 64 "CMP")) = true
          decide
      · simp at h
  · simp at h

/-- A step outside the flag-`CMP` leaves the zero flag. -/
theorem fstepF_zf_of_not_cmp {i : LinstrRM} (hc : cmpArgs? i = none) {s b : LstateM}
    {zf z : Bool} (h : fstepF i s zf = some (b, z)) : z = zf := by
  unfold fstepF at h
  rw [hc] at h
  simp only at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.symm
    · simp at h
  · obtain ⟨b', -, hb⟩ := Option.map_eq_some_iff.mp h
    exact (Prod.mk.inj hb).2.symm

/-- **Transport of an extended straight step.** The step of an instruction without a
    runtime-indexed operand, from a state that agrees with `s` on its hazard tokens and on
    the flags when it touches them, is the step from `s` with its effect applied to that
    state; the zero flag is the one the flag-`CMP` computes, and the incoming one at every
    other instruction. -/
theorem fstepF_transport (i : LinstrRM) (hai : hasArrIdx i.1 = false) {s t : LstateM}
    (h : Agree i.1 s t) (zf zf' : Bool) :
    fstepF i t zf' = (fstepF i s zf).map
      (fun bz => (mergeM i.1 t bz.1, if (cmpArgs? i).isSome then bz.2 else zf')) := by
  obtain ⟨w, tag⟩ := i
  unfold fstepF
  cases hc : cmpArgs? (w, tag) with
  | some ab =>
      obtain ⟨a, b⟩ := ab
      unfold cmpArgs? at hc
      split at hc
      · next d opn a' b' heq =>
          split at hc
          · simp only [Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨rfl, rfl⟩ := hc
            have heq' : w = LinstrR.Lopn [d] opn [a', b'] := heq
            subst heq'
            have ea := evalOperandN_agree h (o := a') (by simp [readToksSem]) 64
            have eb := evalOperandN_agree h (o := b') (by simp [readToksSem]) 64
            simp only [ea, eb]
            cases evalOperandN s.reg 64 a' with
            | none => rfl
            | some va =>
                cases evalOperandN s.reg 64 b' with
                | none => rfl
                | some vb =>
                    simp only [Option.map_some, Option.isSome_some, if_true, Option.some.injEq,
                      Prod.mk.injEq, and_true]
                    have := mergeM_ofReg h s.reg.nextPc
                    rw [mergeN_nextPc h.regAgree.wr] at this
                    exact this.symm
          · cases hc
      · cases hc
  | none =>
      simp only
      cases hm : movRegArgs? (w, tag) with
      | some ds =>
          obtain ⟨dst, src⟩ := ds
          have hshape : ∃ opn, w = LinstrR.Lopn [.reg dst] opn [.reg src] := by
            unfold movRegArgs? at hm
            split at hm
            · next d' opn s' heq =>
                refine ⟨opn, ?_⟩
                have heq' : w = LinstrR.Lopn [.reg d'] opn [.reg s'] := heq
                split_ifs at hm <;> simp only [Option.some.injEq, Prod.mk.injEq] at hm <;>
                  (obtain ⟨rfl, rfl⟩ := hm; exact heq')
            · cases hm
          obtain ⟨opn, rfl⟩ := hshape
          have er : t.reg.lvm src = s.reg.lvm src :=
            (h.reg src (mem_T_read (by simp [readToksSem, srcTok]))).symm
          simp only [readReg, er, Option.map_some, Option.isSome_none, Bool.false_eq_true,
            if_false, Option.some.injEq, Prod.mk.injEq, and_true]
          exact (mergeM_setReg h (by simp [writeToks, opTok]) _).symm
      | none =>
          simp only
          rw [stepMemF_transport (w, tag) hai h]
          cases stepMemF (w, tag) s <;> simp

/-- A successful extended step is its own effect applied to its incoming state. -/
theorem fstepF_mergeM {i : LinstrRM} (hai : hasArrIdx i.1 = false) {s s' : LstateM}
    {zf z : Bool} (h : fstepF i s zf = some (s', z)) : mergeM i.1 s s' = s' := by
  have := fstepF_transport i hai (agree_refl i.1 s) zf zf
  rw [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
  exact this.1.symm

/-- **Adjacent independent instructions commute under the extended straight step.** -/
theorem fstepF_swap (i1 i2 : LinstrRM) (s : LstateM) (zf : Bool)
    (h : indep i1.1 i2.1 = true) :
    (fstepF i1 s zf).bind (fun bz => fstepF i2 bz.1 bz.2)
      = (fstepF i2 s zf).bind (fun bz => fstepF i1 bz.1 bz.2) := by
  have h' : indep i2.1 i1.1 = true := by rw [indep_symm]; exact h
  have ha1 := indep_arrIdx_left h
  have ha2 := indep_arrIdx_right h
  rcases h1 : fstepF i1 s zf with _ | ⟨s1, z1⟩ <;> rcases h2 : fstepF i2 s zf with _ | ⟨s2, z2⟩
  · rfl
  · simp only [Option.bind_none, Option.bind_some]
    rw [fstepF_transport i1 ha1 (agree_after h' (fstepF_mergeM ha2 h2)) zf z2, h1]
    rfl
  · simp only [Option.bind_none, Option.bind_some]
    rw [fstepF_transport i2 ha2 (agree_after h (fstepF_mergeM ha1 h1)) zf z1, h2]
    rfl
  · simp only [Option.bind_some]
    rw [fstepF_transport i2 ha2 (agree_after h (fstepF_mergeM ha1 h1)) zf z1, h2,
      fstepF_transport i1 ha1 (agree_after h' (fstepF_mergeM ha2 h2)) zf z2, h1]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · calc mergeM i2.1 s1 s2 = mergeM i2.1 (mergeM i1.1 s s1) s2 := by
            rw [fstepF_mergeM ha1 h1]
        _ = mergeM i1.1 (mergeM i2.1 s s2) s1 := mergeM_comm h s s1 s2
        _ = mergeM i1.1 s2 s1 := by rw [fstepF_mergeM ha2 h2]
    · cases hc1 : cmpArgs? i1 with
      | some p1 =>
          cases hc2 : cmpArgs? i2 with
          | some p2 =>
              exact absurd ⟨touchesFlags_of_cmpArgs (by rw [hc1]; rfl),
                touchesFlags_of_cmpArgs (by rw [hc2]; rfl)⟩ (indep_flags h)
          | none => simp
      | none =>
          cases hc2 : cmpArgs? i2 with
          | some p2 => simp
          | none =>
              simp only [Option.isSome_none, Bool.false_eq_true, if_false]
              rw [fstepF_zf_of_not_cmp hc1 h1, fstepF_zf_of_not_cmp hc2 h2]

/-- **Adjacent-transposition commutation for `runStraightF`.** -/
theorem runStraightF_swap (i1 i2 : LinstrRM) (rest : List LinstrRM) (s : LstateM) (zf : Bool)
    (h : indep i1.1 i2.1 = true) :
    runStraightF (i1 :: i2 :: rest) s zf = runStraightF (i2 :: i1 :: rest) s zf := by
  have e : ∀ (j k : LinstrRM), runStraightF (j :: k :: rest) s zf
      = ((fstepF j s zf).bind (fun bz => fstepF k bz.1 bz.2)).bind
          (fun bz => runStraightF rest bz.1 bz.2) := by
    intro j k
    rw [runStraightF_cons, Option.bind_assoc]
    rfl
  rw [e, e, fstepF_swap i1 i2 s zf h]

/-- **Schedule soundness over the extended straight fold.** For any tagging of the wire
    instructions by memory tags, any body, any state and any zero flag, the scheduled body
    run by `runStraightF` reaches the same state and zero flag as the input body. -/
theorem scheduleBody_runStraightF (tag : LinstrR → MemTag) (b : List Linstr)
    (s : LstateM) (zf : Bool) :
    runStraightF ((scheduleBody b).map fun i => (i.li_i, tag i.li_i)) s zf
      = runStraightF (b.map fun i => (i.li_i, tag i.li_i)) s zf := by
  have := scheduleBody_run (S := LstateM × Bool)
    (run := fun l p => (runStraightF (l.map fun i => (i, tag i)) p.1 p.2))
    (fun l1 l2 p => by
      simp only [List.map_append]
      exact JasminLsemAddrMem.runStraightF_append _ _ p.1 p.2)
    (fun i1 i2 rest p hi => runStraightF_swap (i1, tag i1) (i2, tag i2) _ p.1 p.2 hi) b (s, zf)
  simpa [List.map_map, Function.comp_def] using this

end StraightF

/-! ## 8. Store-to-load forwarding over the extended straight fold -/

section ReloadF

open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames fstepF_frame_dst)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)

/-- Every destination operand of the instruction is a register. -/
def dstsRegB : LinstrR → Bool
  | .Lopn d _ _ => d.all fun o => match o with
      | .reg _ => true
      | _ => false
  | _ => true

theorem mem_writtenNames_of_dstNames {i : LinstrR} (h : dstsRegB i = true) {r : String}
    (hr : r ∈ dstNames i) : r ∈ writtenNames i := by
  cases i with
  | Lopn d o s =>
      simp only [dstNames, List.mem_flatMap] at hr
      obtain ⟨x, hx, hrx⟩ := hr
      simp only [dstsRegB, List.all_eq_true] at h
      have hxr := h x hx
      cases x with
      | reg n =>
          simp only [opNames, List.mem_singleton] at hrx
          subst hrx
          simp only [writtenNames, List.mem_filterMap]
          exact ⟨.reg r, hx, rfl⟩
      | _ => simp at hxr
  | _ => simp [dstNames] at hr

/-- The environment of the scan agrees with the register file: a register recorded as
    holding a source holds the cell of that source. -/
def HeldSoundM (h : Held) (s : LstateM) : Prop := ∀ p ∈ h, s.reg.lvm p.1 = s.reg.lvm p.2

theorem lvm_setReg_nextPcM (s : LstateM) (d : String) {w : Nat} (v : BitVec w) (r : String) :
    ((s.setReg d v).nextPc).reg.lvm r = if r = d then ⟨w, v⟩ else s.reg.lvm r := by
  by_cases h : r = d <;>
    simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, h]

/-- The step of a reload: the destination takes the cell of the source. -/
theorem fstepF_reload {d k opn : String} (hm : isMovMnem opn = true) (tg : MemTag)
    (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg d] opn [.reg k], tg) s zf
      = some ((s.setReg d (s.reg.lvm k).2).nextPc, zf) := by
  have hmr : movRegArgs? (LinstrR.Lopn [.reg d] opn [.reg k], tg) = some (d, k) := by
    unfold movRegArgs?
    simp only
    by_cases h1 : stripWidthTag opn = "MOV"
    · rw [if_pos h1]
    · have h2 : opn = "MOVQ" := by simpa [isMovMnem, h1] using hm
      subst h2
      rfl
  unfold fstepF
  rw [show cmpArgs? (LinstrR.Lopn [.reg d] opn [.reg k], tg) = none from rfl]
  simp only [hmr, readReg]

/-- A kept step carries the agreement of the environment to the state after. -/
theorem heldSoundM_step {h : Held} {i : LinstrR} (tg : MemTag) (hd : dstsRegB i = true)
    {s t : LstateM} {zf z : Bool} (hs : HeldSoundM h s)
    (hstep : fstepF (i, tg) s zf = some (t, z)) (hkeep : (stepReload h i).1 = true) :
    HeldSoundM (stepReload h i).2 t := by
  cases hr : asReload i with
  | none =>
      rw [stepReload_env_of_notReload hr]
      intro p hp
      obtain ⟨hp1, hn2⟩ := mem_foldl_killSlot _ _ p hp
      obtain ⟨hp2, hn1⟩ := mem_foldl_killReg _ _ p hp1
      rw [(fstepF_frame_dst hstep fun h' => hn1 (mem_writtenNames_of_dstNames hd h')).1,
        (fstepF_frame_dst hstep fun h' => hn2 (mem_writtenNames_of_dstNames hd h')).1]
      exact hs p hp2
  | some dk =>
      obtain ⟨d, k⟩ := dk
      obtain ⟨opn, hm, rfl⟩ := asReload_shape hr
      rw [fstepF_reload hm, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, -⟩ := hstep
      have henv : (stepReload h (LinstrR.Lopn [.reg d] opn [.reg k])).2
          = ((h.killReg d).killSlot d).set d k := by
        cases hf : h.find d with
        | none => simp [stepReload, hr, hf]
        | some k' =>
            by_cases hk : k' = k
            · simp [stepReload, hr, hf, hk] at hkeep
            · simp [stepReload, hr, hf, hk]
      rw [henv]
      intro p hp
      rcases mem_set hp with ⟨hp1, hne⟩ | rfl
      · obtain ⟨hp2, hn2⟩ := mem_killSlot hp1
        obtain ⟨hp3, -⟩ := mem_killReg hp2
        rw [lvm_setReg_nextPcM, lvm_setReg_nextPcM, if_neg hne, if_neg hn2]
        exact hs p hp3
      · rw [lvm_setReg_nextPcM, lvm_setReg_nextPcM, if_pos rfl]
        split
        · rfl
        · rfl

/-- A dropped reload steps to its incoming state up to the program counter. -/
theorem fstepF_drop {h : Held} {i : LinstrR} (tg : MemTag) {s : LstateM} (zf : Bool)
    (hs : HeldSoundM h s) (hdrop : (stepReload h i).1 = false) :
    ∃ b, fstepF (i, tg) s zf = some (b, zf) ∧ EqPc s b := by
  obtain ⟨d, k, hr, hf⟩ := stepReload_drop_is_held_reload h i hdrop
  have hdk : s.reg.lvm d = s.reg.lvm k := hs (d, k) (mem_of_find hf)
  obtain ⟨opn, hm, rfl⟩ := asReload_shape hr
  refine ⟨_, fstepF_reload hm tg s zf, ?_⟩
  refine lstateM_ext (lstateN_ext ?_ rfl) rfl rfl rfl rfl
  funext r
  rw [lvm_setReg_nextPcM]
  split
  · next hrd =>
      subst hrd
      exact hdk.symm
  · rfl

/-- **The scan over the extended straight fold.** From an environment that agrees with the
    start state, a run of a body whose destinations are registers is matched by the run of
    the scanned body from any state equal up to the program counter, with the same zero
    flag and final states equal up to the program counter. -/
theorem elimAux_runStraightF (tag : LinstrR → MemTag) : ∀ (body : List Linstr) (h : Held)
    (s t : LstateM) (zf : Bool), (∀ i ∈ body, dstsRegB i.li_i = true) →
    HeldSoundM h s → EqPc s t →
    ∀ s₂ z₂, runStraightF (body.map fun i => (i.li_i, tag i.li_i)) s zf = some (s₂, z₂) →
      ∃ t₂, runStraightF ((elimAux h body).map fun i => (i.li_i, tag i.li_i)) t zf
          = some (t₂, z₂) ∧ EqPc s₂ t₂ := by
  intro body
  induction body with
  | nil =>
      intro h s t zf _ _ hst s₂ z₂ hrun
      simp only [List.map_nil, runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨t, rfl, hst⟩
  | cons i is ih =>
      intro h s t zf hd hs hst s₂ z₂ hrun
      have hdi := hd i List.mem_cons_self
      have hdis : ∀ j ∈ is, dstsRegB j.li_i = true := fun j hj => hd j (List.mem_cons_of_mem _ hj)
      simp only [List.map_cons, runStraightF_cons] at hrun
      rw [elimAux_cons]
      cases hstep : fstepF (i.li_i, tag i.li_i) s zf with
      | none => rw [hstep] at hrun; simp at hrun
      | some bz =>
          obtain ⟨s₁, z₁⟩ := bz
          rw [hstep, Option.bind_some] at hrun
          by_cases hk : (stepReload h i.li_i).1 = true
          · rw [if_pos hk]
            have ht : t = s.setLpc t.lpc := hst
            have hstep' : fstepF (i.li_i, tag i.li_i) t zf
                = some (s₁.setLpc (t.lpc + 1), z₁) := by
              rw [ht, fstepF_setLpc, hstep]
              rfl
            simp only [List.map_cons, runStraightF_cons, hstep', Option.bind_some]
            exact ih _ s₁ _ z₁ hdis (heldSoundM_step _ hdi hs hstep hk)
              (EqPc.refl_setLpc s₁ _) s₂ z₂ hrun
          · have hdrop : (stepReload h i.li_i).1 = false := by simpa using hk
            rw [if_neg hk, stepReload_env_of_drop hdrop]
            obtain ⟨b, hb, hsb⟩ := fstepF_drop (tag i.li_i) zf hs hdrop
            rw [hb, Option.some.injEq, Prod.mk.injEq] at hstep
            obtain ⟨rfl, rfl⟩ := hstep
            have hb' : b = s.setLpc b.lpc := hsb
            refine ih h b t zf hdis ?_ ((EqPc.symm hsb).trans hst) s₂ z₂ hrun
            intro p hp
            rw [hb']
            exact hs p hp

end ReloadF

/-! ## 9. The scheduler and store-to-load forwarding on whole bodies -/

section WholeF

variable {ck : Bool} {Inv : LstateM → Prop}

/-- An instruction of a straight segment that passes `keepOKB` is an `Lopn`. -/
theorem isLopn_of_keepOKB_of_straight {seg : List Linstr}
    (hsl : bodyIsStraightLine seg = true) {i : Linstr} (hi : i ∈ seg) (tag : LinstrR → MemTag)
    (hk : keepOKB (i.li_i, tag i.li_i) = true) : IsLopn (i.li_i, tag i.li_i) := by
  simp only [bodyIsStraightLine, List.all_eq_true] at hsl
  have h1 := hsl i hi
  obtain ⟨ii, w⟩ := i
  cases w with
  | Lopn d o s => exact ⟨d, o, s, rfl⟩
  | _ => first | (simp [keepOKB] at hk; done) | simp at h1

/-- **The scheduler on a straight `Lopn` segment**, for any invariant the run of the
    segment preserves. -/
theorem scheduleBody_segOK (tag : LinstrR → MemTag) (seg : List Linstr)
    (hl : ∀ i ∈ seg, IsLopn (i.li_i, tag i.li_i))
    (hInv : ∀ (s t : LstateM) (zf zt : Bool), Inv s →
      runStraightF (seg.map fun i => (i.li_i, tag i.li_i)) s zf = some (t, zt) → Inv t) :
    SegOK ck Inv tag scheduleBody seg :=
  ⟨(scheduleBody_length seg).le, hl,
    fun i hi => hl i ((LprogScheduler.scheduleBody_perm seg).mem_iff.1 hi),
    BlockSim.of_same (fun s t zf zt hI _ hr =>
      ⟨t, by rw [scheduleBody_runStraightF]; exact hr, rfl, hInv s t zf zt hI hr⟩)⟩

/-- **Store-to-load forwarding on a straight `Lopn` segment whose destinations are
    registers**, for any invariant the run of the segment preserves. -/
theorem elimReloads_segOK (tag : LinstrR → MemTag) (seg : List Linstr)
    (hl : ∀ i ∈ seg, IsLopn (i.li_i, tag i.li_i))
    (hd : ∀ i ∈ seg, dstsRegB i.li_i = true)
    (hInv : ∀ (s t : LstateM) (zf zt : Bool), Inv s →
      runStraightF (seg.map fun i => (i.li_i, tag i.li_i)) s zf = some (t, zt) → Inv t) :
    SegOK ck Inv tag elimReloads seg :=
  ⟨elimReloads_length_le seg, hl,
    fun i hi => hl i ((LprogStoreToLoad.elimReloads_sublist seg).subset hi),
    BlockSim.of_same (fun s t zf zt hI _ hr => by
      obtain ⟨t₂, h2, hE⟩ := elimAux_runStraightF tag seg [] s s zf hd
        (fun p hp => by simp at hp) rfl t zt hr
      exact ⟨t₂, h2, hE, hInv s t zf zt hI hr⟩)⟩

/-- **The scheduler on whole bodies of the flag machine**: applied to the straight segments
    of a body that passes `keepOKB`. -/
theorem scheduleBody_lsemFuelMemF (tag : LinstrR → MemTag) (body : List Linstr)
    (hkeep : ∀ i ∈ body, keepOKB (i.li_i, tag i.li_i) = true) (fn : String) :
    WholeBodySim ck (fun _ => True) fn (body.map fun i => (i.li_i, tag i.li_i))
      ((mapStraightRuns scheduleBody body).map fun i => (i.li_i, tag i.li_i)) :=
  fun h0 hInv h => mapStraightRuns_lsemFuelMemF tag scheduleBody body (fun _ _ _ => trivial)
    hkeep (fun seg hs hsl => scheduleBody_segOK tag seg
      (fun i hi => isLopn_of_keepOKB_of_straight hsl hi tag (hkeep i (by
        rw [← splitStraightRuns_flatten body]
        exact List.mem_flatten.2 ⟨seg, hs, hi⟩)))
      (fun _ _ _ _ _ _ => trivial)) fn h0 hInv h

/-- **Store-to-load forwarding on whole bodies of the flag machine**: applied to the
    straight segments of a body that passes `keepOKB` and whose destinations are
    registers. -/
theorem elimReloads_lsemFuelMemF (tag : LinstrR → MemTag) (body : List Linstr)
    (hkeep : ∀ i ∈ body, keepOKB (i.li_i, tag i.li_i) = true)
    (hd : ∀ i ∈ body, dstsRegB i.li_i = true) (fn : String) :
    WholeBodySim ck (fun _ => True) fn (body.map fun i => (i.li_i, tag i.li_i))
      ((mapStraightRuns elimReloads body).map fun i => (i.li_i, tag i.li_i)) := by
  have hmem : ∀ seg ∈ splitStraightRuns body, ∀ i ∈ seg, i ∈ body := by
    intro seg hs i hi
    rw [← splitStraightRuns_flatten body]
    exact List.mem_flatten.2 ⟨seg, hs, hi⟩
  intro fuel s t h0 hInv h
  exact mapStraightRuns_lsemFuelMemF tag elimReloads body
    (fun _ _ _ => trivial) hkeep (fun seg hs hsl => elimReloads_segOK tag seg
      (fun i hi => isLopn_of_keepOKB_of_straight hsl hi tag (hkeep i (hmem seg hs i hi)))
      (fun i hi => hd i (hmem seg hs i hi))
      (fun _ _ _ _ _ _ => trivial)) fn h0 hInv h

end WholeF

/-! ## 10. Spill-pair reload elimination over the extended straight fold -/

section PairF

open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad (isMovMnem)

/-- The two 64-bit move mnemonics are move mnemonics. -/
theorem isMovMnem_of_mov64 {mn : String} (h : (mn == "MOV:64" || mn == "MOVQ") = true) :
    isMovMnem mn = true := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide +kernel

/-- A move into a register that holds the cell of the source leaves the state, up to the
    program counter. -/
theorem setReg_nextPc_eqPc (s : LstateM) {d k : String} (h : s.reg.lvm d = s.reg.lvm k) :
    EqPc s ((s.setReg d (s.reg.lvm k).2).nextPc) := by
  refine lstateM_ext (lstateN_ext ?_ rfl) rfl rfl rfl rfl
  funext r
  rw [lvm_setReg_nextPcM]
  split
  · next hrd =>
      subst hrd
      exact h.symm
  · rfl

/-- The deletion inside `consDropL` over the extended straight fold. -/
theorem consDropL_runStraightF (tag : LinstrR → MemTag) (i : Linstr) (k : Lcmd)
    (s t : LstateM) (zf : Bool) (hst : EqPc s t) (s₂ : LstateM) (z₂ : Bool)
    (hrun : runStraightF ((i :: k).map fun i => (i.li_i, tag i.li_i)) s zf = some (s₂, z₂)) :
    ∃ t₂, runStraightF ((consDropL i k).map fun i => (i.li_i, tag i.li_i)) t zf
        = some (t₂, z₂) ∧ EqPc s₂ t₂ := by
  cases k with
  | nil => exact runStraightF_eqPc _ hst hrun
  | cons j rest =>
    rw [consDropL]
    split
    · rename_i h
      obtain ⟨slot, r, mn, hi, hj, hslot, hreg, hmn⟩ := eq_of_isRedundantReloadL h
      have hmm := isMovMnem_of_mov64 hmn
      simp only [List.map_cons, runStraightF_cons, hi, hj] at hrun
      rw [fstepF_reload hmm, Option.bind_some, fstepF_reload hmm, Option.bind_some] at hrun
      have hsl : ((s.setReg slot (s.reg.lvm r).2).nextPc).reg.lvm r
          = ((s.setReg slot (s.reg.lvm r).2).nextPc).reg.lvm slot := by
        rw [lvm_setReg_nextPcM, lvm_setReg_nextPcM, if_neg (slot_ne_reg hslot hreg),
          if_pos rfl]
      obtain ⟨u, hu, hEu⟩ := runStraightF_eqPc _ (EqPc.symm (setReg_nextPc_eqPc _ hsl)) hrun
      have hmid : runStraightF ((i :: rest).map fun i => (i.li_i, tag i.li_i)) s zf
          = some (u, z₂) := by
        simp only [List.map_cons, runStraightF_cons, hi]
        rw [fstepF_reload hmm, Option.bind_some]
        exact hu
      obtain ⟨t₂, ht, hEt⟩ := runStraightF_eqPc _ hst hmid
      exact ⟨t₂, ht, hEu.trans hEt⟩
    · exact runStraightF_eqPc _ hst hrun

/-- The sweep over the extended straight fold. -/
theorem dropReloadsLcmd_runStraightF (tag : LinstrR → MemTag) : ∀ (b : Lcmd) (s t : LstateM)
    (zf : Bool), EqPc s t →
    ∀ s₂ z₂, runStraightF (b.map fun i => (i.li_i, tag i.li_i)) s zf = some (s₂, z₂) →
      ∃ t₂, runStraightF ((dropReloadsLcmd b).map fun i => (i.li_i, tag i.li_i)) t zf
          = some (t₂, z₂) ∧ EqPc s₂ t₂ := by
  intro b
  induction b with
  | nil => intro s t zf hst s₂ z₂ hrun; exact runStraightF_eqPc _ hst hrun
  | cons i rest ih =>
    intro s t zf hst s₂ z₂ hrun
    rw [dropReloadsLcmd_cons]
    simp only [List.map_cons, runStraightF_cons] at hrun
    cases hstep : fstepF (i.li_i, tag i.li_i) s zf with
    | none => rw [hstep] at hrun; simp at hrun
    | some bz =>
      obtain ⟨s₁, z₁⟩ := bz
      rw [hstep, Option.bind_some] at hrun
      obtain ⟨u₂, hu, hsu⟩ := ih s₁ s₁ z₁ rfl s₂ z₂ hrun
      have hmid : runStraightF
          ((i :: dropReloadsLcmd rest).map fun i => (i.li_i, tag i.li_i)) s zf
            = some (u₂, z₂) := by
        simp only [List.map_cons, runStraightF_cons, hstep, Option.bind_some]
        exact hu
      obtain ⟨t₂, ht, hut⟩ :=
        consDropL_runStraightF tag i (dropReloadsLcmd rest) s t zf hst u₂ z₂ hmid
      exact ⟨t₂, ht, hsu.trans hut⟩

/-- **Spill-pair reload elimination over the extended straight fold.** A run of a body is
    matched by the run of the swept body from any state equal up to the program counter,
    with the same zero flag and final states equal up to the program counter. -/
theorem reloadElimBody_runStraightF (tag : LinstrR → MemTag) (b : Lcmd) (s t : LstateM)
    (zf : Bool) (hst : EqPc s t) (s₂ : LstateM) (z₂ : Bool)
    (hrun : runStraightF (b.map fun i => (i.li_i, tag i.li_i)) s zf = some (s₂, z₂)) :
    ∃ t₂, runStraightF ((reloadElimBody b).map fun i => (i.li_i, tag i.li_i)) t zf
        = some (t₂, z₂) ∧ EqPc s₂ t₂ := by
  unfold reloadElimBody
  split
  · exact dropReloadsLcmd_runStraightF tag b s t zf hst s₂ z₂ hrun
  · exact runStraightF_eqPc _ hst hrun

theorem reloadElimBody_sublist (b : Lcmd) : (reloadElimBody b).Sublist b := by
  unfold reloadElimBody
  split
  · exact dropReloadsLcmd_sublist b
  · exact List.Sublist.refl b

end PairF

/-! ## 11. Load CSE over the extended straight fold -/

section LoadF

open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad (writtenNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (fstepF_frame_dst)

/-- The load environment agrees with the register file: a register recorded as holding a
    slot holds the cell of that slot. -/
def EnvSoundM (h : LoadEnv) (s : LstateM) : Prop :=
  ∀ k r : String, (k, r) ∈ h → s.reg.lvm r = s.reg.lvm k

/-- The rewritten instruction steps as the input instruction does. -/
theorem stepLoad_fstepF (h : LoadEnv) (i : Linstr) (tg tg' : MemTag) (s : LstateM) (zf : Bool)
    (hs : EnvSoundM h s) (htg : (stepLoad h i).1 = i → tg' = tg) :
    fstepF ((stepLoad h i).1.li_i, tg') s zf = fstepF (i.li_i, tg) s zf := by
  rcases stepLoad_cases h i with hid | ⟨d, sn, r, mn, ha, hf, hrd, heq⟩
  · rw [htg hid, hid]
  · obtain ⟨hi, hm⟩ := asWideReload_eq ha
    have hmm := isMovMnem_of_mov64 hm
    rw [heq, hi]
    simp only
    rw [fstepF_reload hmm, fstepF_reload hmm, hs sn r (LprogStoreToLoad.mem_of_find hf)]

/-- A step preserves the agreement of the load environment, at an instruction whose
    destinations are registers. -/
theorem stepLoad_envSoundM (h : LoadEnv) (i : Linstr) (tg : MemTag)
    (hd : dstsRegB i.li_i = true) {s s' : LstateM} {zf z : Bool} (hs : EnvSoundM h s)
    (hstep : fstepF (i.li_i, tg) s zf = some (s', z)) : EnvSoundM (stepLoad h i).2 s' := by
  cases hr : asWideReload i.li_i with
  | none =>
      rw [stepLoad_env_of_not_wideReload h i hr]
      intro k r hk
      obtain ⟨hk1, hkw⟩ := mem_foldl_killSlot _ _ _ hk
      obtain ⟨hk0, hrw⟩ := mem_foldl_killReg _ _ _ hk1
      rw [(fstepF_frame_dst hstep fun h' => hrw (mem_writtenNames_of_dstNames hd h')).1,
        (fstepF_frame_dst hstep fun h' => hkw (mem_writtenNames_of_dstNames hd h')).1]
      exact hs k r hk0
  | some dsm =>
      obtain ⟨d, sn, mn⟩ := dsm
      obtain ⟨hi, hm⟩ := asWideReload_eq hr
      rw [stepLoad_env_of_wideReload h i hr]
      rw [hi, fstepF_reload (isMovMnem_of_mov64 hm), Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, -⟩ := hstep
      intro k r hk
      rcases LprogStoreToLoad.mem_set hk with ⟨hk1, hne⟩ | heq
      · obtain ⟨hk2, hkd⟩ := mem_killSlot hk1
        obtain ⟨hk3, hrd⟩ := mem_killReg hk2
        rw [lvm_setReg_nextPcM, lvm_setReg_nextPcM, if_neg hrd, if_neg hkd]
        exact hs k r hk3
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [lvm_setReg_nextPcM, lvm_setReg_nextPcM, if_pos rfl]
        split
        · rfl
        · rfl

/-- The scan over the extended straight fold, from every state its environment agrees
    with. -/
theorem loadCSEAux_runStraightF (tag : LinstrR → MemTag) : ∀ (body : List Linstr)
    (h : LoadEnv) (s : LstateM) (zf : Bool), (∀ i ∈ body, dstsRegB i.li_i = true) →
    EnvSoundM h s →
    runStraightF ((loadCSEAux h body).map fun i => (i.li_i, tag i.li_i)) s zf
      = runStraightF (body.map fun i => (i.li_i, tag i.li_i)) s zf := by
  intro body
  induction body with
  | nil => intro _ _ _ _ _; rfl
  | cons i is ih =>
      intro h s zf hd hs
      rw [loadCSEAux_cons]
      simp only [List.map_cons, runStraightF_cons]
      rw [stepLoad_fstepF h i (tag i.li_i) (tag (stepLoad h i).1.li_i) s zf hs
        (fun e => by rw [e])]
      cases hst : fstepF (i.li_i, tag i.li_i) s zf with
      | none => rfl
      | some bz =>
          simp only [Option.bind_some]
          exact ih _ bz.1 bz.2 (fun j hj => hd j (List.mem_cons_of_mem _ hj))
            (stepLoad_envSoundM h i _ (hd i List.mem_cons_self) hs hst)

/-- **Load CSE over the extended straight fold.** On a body whose destinations are
    registers, the rewritten body runs to the state and zero flag of the input body. -/
theorem loadCSE_runStraightF (tag : LinstrR → MemTag) (body : List Linstr)
    (hd : ∀ i ∈ body, dstsRegB i.li_i = true) (s : LstateM) (zf : Bool) :
    runStraightF ((loadCSE body).map fun i => (i.li_i, tag i.li_i)) s zf
      = runStraightF (body.map fun i => (i.li_i, tag i.li_i)) s zf := by
  rw [loadCSE_eq]
  exact loadCSEAux_runStraightF tag body [] s zf hd (fun _ _ hk => by simp at hk)

/-- The scan keeps a body of `Lopn` instructions a body of `Lopn` instructions. -/
theorem loadCSEAux_isLopn (tag : LinstrR → MemTag) : ∀ (body : List Linstr) (h : LoadEnv),
    (∀ i ∈ body, IsLopn (i.li_i, tag i.li_i)) →
    ∀ j ∈ loadCSEAux h body, IsLopn (j.li_i, tag j.li_i) := by
  intro body
  induction body with
  | nil => intro _ _ j hj; simp [loadCSEAux] at hj
  | cons i is ih =>
      intro h hl j hj
      rw [loadCSEAux_cons, List.mem_cons] at hj
      rcases hj with rfl | hj
      · rcases stepLoad_li_i_cases h i with e | ⟨a, b, c, e⟩
        · obtain ⟨d, o, srcs, hd⟩ := hl i List.mem_cons_self
          exact ⟨d, o, srcs, e.trans hd⟩
        · exact ⟨a, b, c, e⟩
      · exact ih _ (fun k hk => hl k (List.mem_cons_of_mem _ hk)) j hj

end LoadF

/-! ## 12. Spill-pair elimination and load CSE on whole bodies -/

section WholeG

variable {ck : Bool} {Inv : LstateM → Prop}

/-- **Spill-pair reload elimination on a straight `Lopn` segment**, for any invariant the
    run of the segment preserves. -/
theorem reloadElimBody_segOK (tag : LinstrR → MemTag) (seg : List Linstr)
    (hl : ∀ i ∈ seg, IsLopn (i.li_i, tag i.li_i))
    (hInv : ∀ (s t : LstateM) (zf zt : Bool), Inv s →
      runStraightF (seg.map fun i => (i.li_i, tag i.li_i)) s zf = some (t, zt) → Inv t) :
    SegOK ck Inv tag reloadElimBody seg :=
  ⟨reloadElimBody_length_le seg, hl,
    fun i hi => hl i ((reloadElimBody_sublist seg).subset hi),
    BlockSim.of_same (fun s t zf zt hI _ hr => by
      obtain ⟨t₂, h2, hE⟩ := reloadElimBody_runStraightF tag seg s s zf rfl t zt hr
      exact ⟨t₂, h2, hE, hInv s t zf zt hI hr⟩)⟩

/-- **Load CSE on a straight `Lopn` segment whose destinations are registers**, for any
    invariant the run of the segment preserves. -/
theorem loadCSE_segOK (tag : LinstrR → MemTag) (seg : List Linstr)
    (hl : ∀ i ∈ seg, IsLopn (i.li_i, tag i.li_i))
    (hd : ∀ i ∈ seg, dstsRegB i.li_i = true)
    (hInv : ∀ (s t : LstateM) (zf zt : Bool), Inv s →
      runStraightF (seg.map fun i => (i.li_i, tag i.li_i)) s zf = some (t, zt) → Inv t) :
    SegOK ck Inv tag loadCSE seg :=
  ⟨(loadCSE_length seg).le, hl,
    fun i hi => loadCSEAux_isLopn tag seg [] hl i (by rw [← loadCSE_eq]; exact hi),
    BlockSim.of_same (fun s t zf zt hI _ hr =>
      ⟨t, by rw [loadCSE_runStraightF tag seg hd]; exact hr, rfl, hInv s t zf zt hI hr⟩)⟩

theorem mem_body_of_mem_splitStraightRuns {body seg : List Linstr}
    (hs : seg ∈ splitStraightRuns body) {i : Linstr} (hi : i ∈ seg) : i ∈ body := by
  rw [← splitStraightRuns_flatten body]
  exact List.mem_flatten.2 ⟨seg, hs, hi⟩

/-- **Spill-pair reload elimination on whole bodies of the flag machine**: applied to the
    straight segments of a body that passes `keepOKB`. -/
theorem reloadElimBody_lsemFuelMemF (tag : LinstrR → MemTag) (body : List Linstr)
    (hkeep : ∀ i ∈ body, keepOKB (i.li_i, tag i.li_i) = true) (fn : String) :
    WholeBodySim ck (fun _ => True) fn (body.map fun i => (i.li_i, tag i.li_i))
      ((mapStraightRuns reloadElimBody body).map fun i => (i.li_i, tag i.li_i)) := by
  intro fuel s t h0 hInv h
  exact mapStraightRuns_lsemFuelMemF tag reloadElimBody body (fun _ _ _ => trivial) hkeep
    (fun seg hs hsl => reloadElimBody_segOK tag seg
      (fun i hi => isLopn_of_keepOKB_of_straight hsl hi tag
        (hkeep i (mem_body_of_mem_splitStraightRuns hs hi)))
      (fun _ _ _ _ _ _ => trivial)) fn h0 hInv h

/-- **Load CSE on whole bodies of the flag machine**: applied to the straight segments of a
    body that passes `keepOKB` and whose destinations are registers. -/
theorem loadCSE_lsemFuelMemF (tag : LinstrR → MemTag) (body : List Linstr)
    (hkeep : ∀ i ∈ body, keepOKB (i.li_i, tag i.li_i) = true)
    (hd : ∀ i ∈ body, dstsRegB i.li_i = true) (fn : String) :
    WholeBodySim ck (fun _ => True) fn (body.map fun i => (i.li_i, tag i.li_i))
      ((mapStraightRuns loadCSE body).map fun i => (i.li_i, tag i.li_i)) := by
  intro fuel s t h0 hInv h
  exact mapStraightRuns_lsemFuelMemF tag loadCSE body (fun _ _ _ => trivial) hkeep
    (fun seg hs hsl => loadCSE_segOK tag seg
      (fun i hi => isLopn_of_keepOKB_of_straight hsl hi tag
        (hkeep i (mem_body_of_mem_splitStraightRuns hs hi)))
      (fun i hi => hd i (mem_body_of_mem_splitStraightRuns hs hi))
      (fun _ _ _ _ _ _ => trivial)) fn h0 hInv h

end WholeG

/-! ## 13. The five stages over the extended straight fold, given copy propagation -/

section FiveF

open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (instrShape copyPropagateBody_sublist_shape)

variable {ck : Bool} {Inv : LstateM → Prop}

/-- The statement of copy propagation on one body over the extended straight fold: a run of
    the body is matched by a run of the copy-propagated body from the same state, with the
    same zero flag and final states equal up to the program counter. -/
def CopyPropSim (tag : LinstrR → MemTag) (body : Lcmd) : Prop :=
  ∀ (s : LstateM) (zf : Bool) (s₂ : LstateM) (z₂ : Bool),
    runStraightF (body.map fun i => (i.li_i, tag i.li_i)) s zf = some (s₂, z₂) →
    ∃ t₂, runStraightF ((copyPropagateBody body).map fun i => (i.li_i, tag i.li_i)) s zf
        = some (t₂, z₂) ∧ EqPc s₂ t₂

/-- The destinations of an instruction are a function of its shape. -/
theorem dstsRegB_eq_of_shape {i j : Linstr} (h : instrShape i = instrShape j) :
    dstsRegB j.li_i = dstsRegB i.li_i := by
  have h1 := congrArg (fun x => x.2.1) h
  cases hi : i.li_i with
  | Lopn d o s =>
      cases hj : j.li_i with
      | Lopn d' o' s' =>
          simp only [instrShape, hi, hj, Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, -⟩ := h1
          rfl
      | _ => simp [instrShape, hi, hj] at h1
  | _ =>
      cases hj : j.li_i with
      | Lopn d' o' s' => simp [instrShape, hi, hj] at h1
      | _ => rfl

/-- Being an `Lopn` is a function of the shape. -/
theorem isLopn_of_shape (tag : LinstrR → MemTag) {i j : Linstr}
    (h : instrShape i = instrShape j) (hl : IsLopn (i.li_i, tag i.li_i)) :
    IsLopn (j.li_i, tag j.li_i) := by
  have h1 := congrArg (fun x => x.2.1) h
  obtain ⟨d, o, s, hd⟩ := hl
  have hd' : i.li_i = LinstrR.Lopn d o s := hd
  cases hj : j.li_i with
  | Lopn d' o' s' => exact ⟨d', o', s', rfl⟩
  | _ => simp [instrShape, hd', hj] at h1

/-- An instruction of the copy-propagated body has the shape of an instruction of the
    body. -/
theorem exists_shape_of_mem_copyPropagateBody {body : Lcmd} {j : Linstr}
    (hj : j ∈ copyPropagateBody body) : ∃ i ∈ body, instrShape i = instrShape j := by
  have hsub := (copyPropagateBody_sublist_shape body).subset (List.mem_map_of_mem hj)
  rw [List.mem_map] at hsub
  exact hsub

/-- The first three stages keep every instruction of the segment. -/
theorem mem_of_mem_three_stages {seg : List Linstr} {i : Linstr}
    (hi : i ∈ scheduleBody (reloadElimBody (elimReloads seg))) : i ∈ seg :=
  (LprogStoreToLoad.elimReloads_sublist seg).subset
    ((reloadElimBody_sublist _).subset
      ((LprogScheduler.scheduleBody_perm _).mem_iff.1 hi))

/-- **The five stages over the extended straight fold, given copy propagation.** On a
    segment whose destinations are registers, and given `CopyPropSim` at the segment after
    the first three stages, a run of the segment is matched by a run of `optRunBody` of the
    segment from the same state, with the same zero flag and final states equal up to the
    program counter. -/
theorem optRunBody_runStraightF (tag : LinstrR → MemTag) (seg : List Linstr)
    (hd : ∀ i ∈ seg, dstsRegB i.li_i = true)
    (hcp : CopyPropSim tag (scheduleBody (reloadElimBody (elimReloads seg))))
    (s : LstateM) (zf : Bool) (s₂ : LstateM) (z₂ : Bool)
    (hrun : runStraightF (seg.map fun i => (i.li_i, tag i.li_i)) s zf = some (s₂, z₂)) :
    ∃ t₂, runStraightF ((optRunBody seg).map fun i => (i.li_i, tag i.li_i)) s zf
        = some (t₂, z₂) ∧ EqPc s₂ t₂ := by
  unfold optRunBody
  split
  · obtain ⟨t₁, h1, e1⟩ := elimAux_runStraightF tag seg [] s s zf hd
      (fun p hp => by simp at hp) rfl s₂ z₂ hrun
    obtain ⟨t₂, h2, e2⟩ := reloadElimBody_runStraightF tag (elimReloads seg) s s zf rfl t₁ z₂ h1
    rw [← scheduleBody_runStraightF] at h2
    obtain ⟨t₄, h4, e4⟩ := hcp s zf t₂ z₂ h2
    refine ⟨t₄, ?_, (e1.trans e2).trans e4⟩
    rw [loadCSE_runStraightF tag _ (fun j hj => ?_)]
    · exact h4
    · obtain ⟨i, hi, hsh⟩ := exists_shape_of_mem_copyPropagateBody hj
      rw [dstsRegB_eq_of_shape hsh]
      exact hd i (mem_of_mem_three_stages hi)
  · exact ⟨s₂, hrun, rfl⟩

/-- The five stages keep a segment of `Lopn` instructions a segment of `Lopn`
    instructions. -/
theorem optRunBody_isLopn (tag : LinstrR → MemTag) (seg : List Linstr)
    (hl : ∀ i ∈ seg, IsLopn (i.li_i, tag i.li_i)) :
    ∀ j ∈ optRunBody seg, IsLopn (j.li_i, tag j.li_i) := by
  unfold optRunBody
  split
  · intro j hj
    rw [loadCSE_eq] at hj
    refine loadCSEAux_isLopn tag _ [] (fun k hk => ?_) j hj
    obtain ⟨i, hi, hsh⟩ := exists_shape_of_mem_copyPropagateBody hk
    exact isLopn_of_shape tag hsh (hl i (mem_of_mem_three_stages hi))
  · exact hl

/-- **The five stages on a straight `Lopn` segment whose destinations are registers, given
    copy propagation**, for any invariant the run of the segment preserves. -/
theorem optRunBody_segOK_of_copyPropSim (tag : LinstrR → MemTag) (seg : List Linstr)
    (hl : ∀ i ∈ seg, IsLopn (i.li_i, tag i.li_i))
    (hd : ∀ i ∈ seg, dstsRegB i.li_i = true)
    (hcp : CopyPropSim tag (scheduleBody (reloadElimBody (elimReloads seg))))
    (hInv : ∀ (s t : LstateM) (zf zt : Bool), Inv s →
      runStraightF (seg.map fun i => (i.li_i, tag i.li_i)) s zf = some (t, zt) → Inv t) :
    SegOK ck Inv tag optRunBody seg :=
  ⟨optRunBody_length_le seg, hl, optRunBody_isLopn tag seg hl,
    BlockSim.of_same (fun s t zf zt hI _ hr => by
      obtain ⟨t₂, h2, hE⟩ := optRunBody_runStraightF tag seg hd hcp s zf t zt hr
      exact ⟨t₂, h2, hE, hInv s t zf zt hI hr⟩)⟩

/-- **The basic-block optimiser on whole bodies of the flag machine, given copy
    propagation.** For a body that passes `keepOKB`, whose destinations are registers, and
    with `CopyPropSim` at every straight segment after the first three stages, every
    halting run of `lsemFuelMemFk ck` on the tagged body from program counter `0` is
    matched by a halting run of the tagged optimised body from the same state with at most
    the same fuel, to a state with the same function name and zero flag and a base equal
    up to the program counter. -/
theorem optimizeBasicBlocks_wholeBodySim_of_copyPropSim (tag : LinstrR → MemTag)
    (body : List Linstr) (hkeep : ∀ i ∈ body, keepOKB (i.li_i, tag i.li_i) = true)
    (hd : ∀ i ∈ body, dstsRegB i.li_i = true)
    (hcp : ∀ seg ∈ splitStraightRuns body, bodyIsStraightLine seg = true →
      CopyPropSim tag (scheduleBody (reloadElimBody (elimReloads seg))))
    (fn : String) :
    WholeBodySim ck (fun _ => True) fn (body.map fun i => (i.li_i, tag i.li_i))
      ((optimizeBasicBlocks body).map fun i => (i.li_i, tag i.li_i)) :=
  optimizeBasicBlocks_lsemFuelMemF tag body (fun _ _ _ => trivial) hkeep
    (fun seg hs hsl => optRunBody_segOK_of_copyPropSim tag seg
      (fun i hi => isLopn_of_keepOKB_of_straight hsl hi tag
        (hkeep i (mem_body_of_mem_splitStraightRuns hs hi)))
      (fun i hi => hd i (mem_body_of_mem_splitStraightRuns hs hi))
      (hcp seg hs hsl) (fun _ _ _ _ _ _ => trivial)) fn

end FiveF

/-! ## 14. Bodies without a candidate move -/

section MoveFree

open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (moveShape propagateAux deadElimStep deadElimBody rewriteOperand lookupFact killFacts
    MoveFact physGPs)

variable {ck : Bool}

theorem rewriteOperand_nil (w : Nat) (a : Bool) (ds : Option String) (o : LOperand) :
    rewriteOperand [] w a ds o = o := by
  cases o with
  | reg u =>
      simp only [rewriteOperand, lookupFact, List.findSome?_nil]
      split <;> rfl
  | _ => rfl

theorem foldl_killFacts_nil (rs : List String) :
    rs.foldl killFacts ([] : List MoveFact) = [] := by
  induction rs with
  | nil => rfl
  | cons r rest ih => exact ih

/-- Forward propagation from no facts is the identity on a body with no candidate move. -/
theorem propagateAux_nil_eq_of_noMove :
    ∀ (body : Lcmd), (∀ i ∈ body, moveShape i = none) → propagateAux [] body = body := by
  intro body
  induction body with
  | nil => intro _; rfl
  | cons i rest ih =>
      intro h
      have hrest := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
      have hi0 := h i List.mem_cons_self
      obtain ⟨ii, w⟩ := i
      cases w with
      | Lopn dsts opn srcs =>
          have hmap : ∀ (x : Nat) (a : Bool) (ds : Option String),
              srcs.map (rewriteOperand [] x a ds) = srcs := fun x a ds => by
            rw [List.map_congr_left (fun o _ => rewriteOperand_nil x a ds o), List.map_id']
          simp only [propagateAux, hmap, foldl_killFacts_nil, hi0, hrest]
          split <;> rfl
      | _ => simp only [propagateAux, hrest]

theorem deadElimStep_snd_of_noMove (i : Linstr) (h : moveShape i = none)
    (p : List String × Lcmd) : (deadElimStep i p).2 = i :: p.2 := by
  obtain ⟨live, acc⟩ := p
  simp only [deadElimStep, h]
  split
  · split <;> simp
  · rfl

/-- Dead-move elimination is the identity on a body with no candidate move. -/
theorem deadElimBody_eq_of_noMove (body : Lcmd) (h : ∀ i ∈ body, moveShape i = none) :
    deadElimBody body = body := by
  have key : ∀ (b : Lcmd), (∀ i ∈ b, moveShape i = none) → ∀ p : List String × Lcmd,
      (b.foldr deadElimStep p).2 = b ++ p.2 := by
    intro b
    induction b with
    | nil => intro _ p; rfl
    | cons i rest ih =>
        intro hb p
        rw [List.foldr_cons, deadElimStep_snd_of_noMove i (hb i List.mem_cons_self),
          ih (fun j hj => hb j (List.mem_cons_of_mem _ hj))]
        rfl
  have := key body h (physGPs, [])
  simpa [deadElimBody] using this

/-- Copy propagation is the identity on a body with no candidate move. -/
theorem copyPropagateBody_eq_of_noMove (body : Lcmd) (h : ∀ i ∈ body, moveShape i = none) :
    copyPropagateBody body = body := by
  unfold copyPropagateBody
  rw [propagateAux_nil_eq_of_noMove body h, deadElimBody_eq_of_noMove body h]

theorem copyPropSim_of_noMove (tag : LinstrR → MemTag) (body : Lcmd)
    (h : ∀ i ∈ body, moveShape i = none) : CopyPropSim tag body := by
  intro s zf s₂ z₂ hrun
  exact ⟨s₂, by rw [copyPropagateBody_eq_of_noMove body h]; exact hrun, rfl⟩

/-- **The check of the optimiser on a body with no candidate move**: every instruction
    passes `keepOKB`, has register destinations, and is not a candidate move of copy
    propagation. -/
def optBlocksMoveFreeOKB (tag : LinstrR → MemTag) (body : List Linstr) : Bool :=
  body.all fun i =>
    keepOKB (i.li_i, tag i.li_i) && dstsRegB i.li_i && (moveShape i).isNone

/-- **Soundness of the check: the basic-block optimiser on a body with no candidate
    move.** For a body that passes `optBlocksMoveFreeOKB`, every halting run of
    `lsemFuelMemFk ck` on the tagged body from program counter `0` is matched by a halting
    run of the tagged optimised body from the same state with at most the same fuel, to a
    state with the same function name and zero flag and a base equal up to the program
    counter. -/
theorem optBlocksMoveFreeOKB_sound {tag : LinstrR → MemTag} {body : List Linstr}
    (h : optBlocksMoveFreeOKB tag body = true) (fn : String) :
    WholeBodySim ck (fun _ => True) fn (body.map fun i => (i.li_i, tag i.li_i))
      ((optimizeBasicBlocks body).map fun i => (i.li_i, tag i.li_i)) := by
  simp only [optBlocksMoveFreeOKB, List.all_eq_true, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at h
  exact optimizeBasicBlocks_wholeBodySim_of_copyPropSim tag body (fun i hi => (h i hi).1.1)
    (fun i hi => (h i hi).1.2)
    (fun seg hs _ => copyPropSim_of_noMove tag _ (fun i hi =>
      (h i (mem_body_of_mem_splitStraightRuns hs (mem_of_mem_three_stages hi))).2)) fn

end MoveFree

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg
