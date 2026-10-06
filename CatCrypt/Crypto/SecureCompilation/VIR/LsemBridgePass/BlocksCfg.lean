/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift
public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Blocks

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
* `scheduleBody_segOK`, `elimReloads_segOK`, `copyPropagateBody_segOK`,
  `optRunBody_segOK` — the per-segment condition of each pass on the fragment with flags.
* `scheduleBody_lsemFuelMemF`, `elimReloads_lsemFuelMemF`,
  `copyPropagateBody_lsemFuelMemF` — the passes on whole bodies.
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

/-- **The scheduler on a segment of the fragment with flags.** -/
theorem scheduleBody_segOK {A : String → Option Nat} (tag : LinstrR → MemTag)
    (seg : List Linstr) (hfrag : ∀ i ∈ seg, fragFB A (i.li_i, tag i.li_i) = true) :
    SegOK true (RelInv A) tag scheduleBody seg := by
  have hfrag' : ∀ i ∈ scheduleBody seg, fragFB A (i.li_i, tag i.li_i) = true :=
    fun i hi => hfrag i ((LprogScheduler.scheduleBody_perm seg).mem_iff.1 hi)
  refine ⟨(scheduleBody_length seg).le, fun i hi => (fragFB_plain (hfrag i hi)).1,
    fun i hi => (fragFB_plain (hfrag' i hi)).1,
    blockSim_of_fragFB tag scheduleBody seg hfrag hfrag'
      (fun l h => by rw [runIBF_scheduleBody]; exact h) (fun s l hr hib _ => ?_)⟩
  obtain ⟨u, u', -, hu, hu', -, -, hreg, hA, hM, hc, ho, -, -⟩ :=
    scheduleBody_lsemStraightMemF_F tag seg hfrag hr hib
  exact ⟨u, u', hu, hu', by rw [hreg], hA, hM, hc, ho⟩

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

/-- **Store-to-load forwarding on a segment of the fragment with flags**, where the pass
    is the identity. -/
theorem elimReloads_segOK {A : String → Option Nat} (tag : LinstrR → MemTag)
    (seg : List Linstr) (hfrag : ∀ i ∈ seg, fragFB A (i.li_i, tag i.li_i) = true) :
    SegOK true (RelInv A) tag elimReloads seg := by
  have e := elimReloads_eq_of_fragFB tag seg hfrag
  have hfrag' : ∀ i ∈ elimReloads seg, fragFB A (i.li_i, tag i.li_i) = true := by
    rw [e]; exact hfrag
  refine ⟨elimReloads_length_le seg, fun i hi => (fragFB_plain (hfrag i hi)).1,
    fun i hi => (fragFB_plain (hfrag' i hi)).1,
    blockSim_of_fragFB tag elimReloads seg hfrag hfrag' (fun l h => by rw [e]; exact h)
      (fun s l hr hib _ => ?_)⟩
  have hB : ∀ i ∈ seg.map (fun i => (i.li_i, tag i.li_i)), fragFB A i = true := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    exact hfrag j hj
  obtain ⟨s', l', hs', -, -, -, -⟩ := lsemStraightFlag_lsemStraightMemF_rel _ s l hB hr hib
  exact ⟨s', s', by rw [e]; exact hs', hs', rfl, rfl, rfl, rfl, rfl⟩

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

/-- **The scheduler on whole bodies of the flag machine**: applied to the straight segments
    of a body that passes `keepOKB` and whose straight segments are in the fragment with
    flags. -/
theorem scheduleBody_lsemFuelMemF {A : String → Option Nat} (tag : LinstrR → MemTag)
    (body : List Linstr) (hkeep : ∀ i ∈ body, keepOKB (i.li_i, tag i.li_i) = true)
    (hfrag : ∀ seg ∈ splitStraightRuns body, bodyIsStraightLine seg = true →
      ∀ i ∈ seg, fragFB A (i.li_i, tag i.li_i) = true) (fn : String) :
    WholeBodySim true (RelInv A) fn (body.map fun i => (i.li_i, tag i.li_i))
      ((mapStraightRuns scheduleBody body).map fun i => (i.li_i, tag i.li_i)) :=
  fun h0 hInv h => mapStraightRuns_lsemFuelMemF tag scheduleBody body relInv_setLpc hkeep
    (fun seg hs hsl => scheduleBody_segOK tag seg (hfrag seg hs hsl)) fn h0 hInv h

/-- **Store-to-load forwarding on whole bodies of the flag machine**, under the hypotheses
    of `scheduleBody_lsemFuelMemF`. -/
theorem elimReloads_lsemFuelMemF {A : String → Option Nat} (tag : LinstrR → MemTag)
    (body : List Linstr) (hkeep : ∀ i ∈ body, keepOKB (i.li_i, tag i.li_i) = true)
    (hfrag : ∀ seg ∈ splitStraightRuns body, bodyIsStraightLine seg = true →
      ∀ i ∈ seg, fragFB A (i.li_i, tag i.li_i) = true) (fn : String) :
    WholeBodySim true (RelInv A) fn (body.map fun i => (i.li_i, tag i.li_i))
      ((mapStraightRuns elimReloads body).map fun i => (i.li_i, tag i.li_i)) :=
  fun h0 hInv h => mapStraightRuns_lsemFuelMemF tag elimReloads body relInv_setLpc hkeep
    (fun seg hs hsl => elimReloads_segOK tag seg (hfrag seg hs hsl)) fn h0 hInv h

/-- **Copy propagation on whole bodies of the flag machine**: under the hypotheses of
    `scheduleBody_lsemFuelMemF`, with every copy-propagated straight segment in the
    fragment and in bounds wherever its input is. -/
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

/-! ## 6. The decidable check of the optimiser on a body -/

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

/-- The check of the optimiser on one straight segment: a segment of flag-`CMP`
    instructions outside the modelled bodies, or a segment of the fragment with flags whose
    scheduled and copy-propagated form is in the fragment and has no indexed access. -/
def optSegOKB (A : String → Option Nat) (tag : LinstrR → MemTag) (seg : List Linstr) : Bool :=
  (!bodyAllModeled seg && seg.all fun i => (cmpArgs? (i.li_i, tag i.li_i)).isSome)
    || (seg.all (fun i => fragFB A (i.li_i, tag i.li_i))
        && (copyPropagateBody (scheduleBody seg)).all
            (fun i => fragFB A (i.li_i, tag i.li_i) && !LprogScheduler.hasArrIdx i.li_i))

/-- **The check of the optimiser on a body**: every instruction passes `keepOKB` and every
    straight segment of the partition passes `optSegOKB`. -/
def optBlocksOKB (A : String → Option Nat) (tag : LinstrR → MemTag) (body : List Linstr) :
    Bool :=
  body.all (fun i => keepOKB (i.li_i, tag i.li_i))
    && (splitStraightRuns body).all
        (fun seg => !bodyIsStraightLine seg || optSegOKB A tag seg)

theorem optSegOKB_sound {A : String → Option Nat} {tag : LinstrR → MemTag}
    {seg : List Linstr} (h : optSegOKB A tag seg = true) :
    SegOK true (RelInv A) tag optRunBody seg := by
  unfold optSegOKB at h
  rw [Bool.or_eq_true] at h
  rcases h with h1 | h2
  · simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h1
    exact optRunBody_segOK_of_cmp tag seg h1.1 h1.2
  · simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h2
    exact optRunBody_segOK_of_idxFree tag seg h2.1 (fun i hi => (h2.2 i hi).1)
      (fun i hi => (h2.2 i hi).2)

/-- **Soundness of the check: the basic-block optimiser on a checked body.** For a body
    that passes `optBlocksOKB`, every halting run of the checked machine on the tagged body
    from program counter `0` and a state of `RelInv A` is matched by a halting run of the
    tagged optimised body from the same state with at most the same fuel, to a state with
    the same function name and zero flag and a base equal up to the program counter. -/
theorem optBlocksOKB_sound {A : String → Option Nat} {tag : LinstrR → MemTag}
    {body : List Linstr} (h : optBlocksOKB A tag body = true) (fn : String) :
    WholeBodySim true (RelInv A) fn (body.map fun i => (i.li_i, tag i.li_i))
      ((optimizeBasicBlocks body).map fun i => (i.li_i, tag i.li_i)) := by
  simp only [optBlocksOKB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  refine optimizeBasicBlocks_lsemFuelMemF tag body relInv_setLpc h.1
    (fun seg hs hsl => optSegOKB_sound ?_) fn
  rcases h.2 seg hs with h' | h'
  · rw [hsl] at h'
    cases h'
  · exact h'

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg
