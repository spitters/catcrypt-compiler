/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrc

@[expose] public section

set_option autoImplicit false

/-!
# The virtual body of the register allocation check at an explicit fuel

`ImageAddrSrc.src_chain` and `ImageAddrSrc.src_chain_fuse` match a halting run of the
exported node `seeds ++ loop` at fuel `fuel` by a halting run of the virtual body at some
fuel. The moves `pre0` in front cost their length, the copies `movesOf ps` cost one step per
pair, and the renamed loop runs step for step, so the virtual body halts at fuel
`pre0.length + fuel + ps.length`; the fusion of the renamed loop multiplies that fuel by at
most four. This module states both results at those fuels, in the form "the virtual body
halts in one state at every fuel from the bound on", and derives the statements of
`ImageAddrSrc` from them.

## Main definitions

* `srcFuel`: the fuel `pre0Len + fuel + psLen` of the virtual body.
* `srcFuseFuel`: the fuel `srcFuel pre0Len psLen fuel * 4` of the virtual body with the
  renamed loop fused.

## Main results

* `renameLoop_sim_fuel`, `renameLoop_getArr_fuel`: `JasminLsemRenameLoop.renameLoop_sim` and
  `renameLoop_getArr` with the renamed body run at fuel `fuel + ps.length`.
* `src_chain_fuel`: the virtual body halts in one state at every fuel from `srcFuel` on.
* `src_chain_fuse_fuel`: the virtual body with the renamed loop fused halts in one state at
  every fuel from `srcFuseFuel` on.
* `src_chain_of_fuel`, `src_chain_fuse_of_fuel`: the statements of `ImageAddrSrc.src_chain`
  and `ImageAddrSrc.src_chain_fuse`, from the forms at an explicit fuel.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrcFuel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrc
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_lsemFuelMemF)

/-- The fuel of the virtual body `pre0 ++ seeds ++ movesOf ps ++ loop.map (renRM (renOf ps))`
    for a run of the node at fuel `fuel`: the length of `pre0`, the fuel of the node and one
    step per pair of `ps`. -/
def srcFuel (pre0Len psLen fuel : Nat) : Nat := pre0Len + fuel + psLen

/-- The fuel of the virtual body with the renamed loop fused. -/
def srcFuseFuel (pre0Len psLen fuel : Nat) : Nat := srcFuel pre0Len psLen fuel * 4

/-- A halting run of `lsemFuelMemF` returns the same state at every larger fuel. -/
theorem lsemFuelMemF_le (P : LprogM) {n k : Nat} {s t : LstateMF}
    (h : lsemFuelMemF P n s = some t) (hk : n ≤ k) : lsemFuelMemF P k s = some t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [← x86Isa_lsemFuelMemF] at h ⊢
  exact x86Isa.lsemFuelMemF_add P n d s t h

/-- **The loop renamed behind the copies, at an explicit fuel.** Under the hypotheses of
    `renameLoop_sim`, a halting run of `pre ++ loop` at fuel `fuel` is matched by a halting
    run of `pre ++ movesOf ps ++ map (renRM (renOf ps)) loop` at fuel `fuel + ps.length`, the
    final states related as in `renameLoop_sim`. -/
theorem renameLoop_sim_fuel (fn : String) (pre loop : List LinstrRM)
    (ps : List (String × String))
    (N : String → Prop) (hpre : ∀ i ∈ pre, IsLopn i) (hloop : ∀ i ∈ loop, CtlOK i)
    (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (b0 : LstateM) (zf : Bool) (h0 : b0.lpc = 0)
    (hA : ∀ b1 z1, runStraightF pre b0 zf = some (b1, z1) →
      ∀ r, N r → b1.larr (renOf ps r) = b1.larr r)
    (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (pre ++ loop)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some t) :
    ∃ t', lsemFuelMemF (singletonProgM fn (pre ++ movesOf ps ++ loop.map (renRM (renOf ps))))
        (fuel + ps.length) { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ ∃ tl tl', t = shiftS pre.length tl ∧ t' = shiftS (pre.length + ps.length) tl'
        ∧ RelF (renOf ps) N tl tl' := by
  have hpos : ∀ j, j < pre.length →
      (singletonProgM fn (pre ++ loop)).body[b0.lpc + j]? = pre[j]? := fun j hj => by
    simp only [singletonProgM, h0, Nat.zero_add]
    exact List.getElem?_append_left hj
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le
    (lsemFuelMemF_seg_fuel _ fn rfl pre b0 zf fuel t hpre hpos hrun)
  rw [lsemFuelMemF_segF _ fn rfl pre b0 zf f hpre hpos] at hrun
  cases hp : runStraightF pre b0 zf with
  | none => simp [hp] at hrun
  | some bz =>
      obtain ⟨b1, z1⟩ := bz
      rw [hp, Option.bind_some] at hrun
      have hpc : b1.lpc = pre.length := by
        rw [runStraightF_lpc pre b0 zf b1 z1 hp, h0, Nat.zero_add]
      have hsh : ({ prog := { base := b1, lfn := fn }, zf := z1 } : LstateMF)
          = shiftS pre.length { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 } := by
        simp only [shiftS, LstateM.lpc_setLpc, Nat.zero_add, ← hpc]
        rfl
      rw [hsh] at hrun
      obtain ⟨tl, htl, rfl⟩ := lsemFuelMemF_of_prefix fn pre loop hpre hloop f _ t hrun
      have hR : RelF (renOf ps) N { prog := { base := b1.setLpc 0, lfn := fn }, zf := z1 }
          { prog := { base := (movesState ps b1).setLpc 0, lfn := fn }, zf := z1 } := by
        obtain ⟨hl, hm, hc, ho⟩ := movesState_larr ps b1
        refine ⟨⟨⟨rfl, fun r hr => ?_⟩, fun r hr => ?_, hm⟩, rfl, rfl, hc, ho⟩
        · show (movesState ps b1).reg.lvm (renOf ps r) = b1.reg.lvm r
          by_cases hm' : r ∈ ps.map Prod.fst
          · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hm'
            rw [hren p hp']
            exact movesState_target ps hnd hts b1 p hp'
          · rw [renOf_of_not_mem hm']
            refine movesState_other ps b1 r fun hmem => ?_
            obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hmem
            exact hfresh p hp' hr
        · show (movesState ps b1).larr (renOf ps r) = b1.larr r
          rw [hl]
          exact hA b1 z1 hp r hr
      obtain ⟨tl', htl', hRt⟩ := lsemFuelMemF_map_renRM hσ fn loop hn hcond f hR htl
      have hpre' : ∀ i ∈ pre ++ movesOf ps, IsLopn i := by
        intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact hpre i hi
        · exact movesOf_isLopn ps i hi
      have hB' : ∀ i ∈ loop.map (renRM (renOf ps)), CtlOK i := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        exact ctlOK_renRM _ (hloop j hj)
      have hrunPre : runStraightF (pre ++ movesOf ps) b0 zf = some (movesState ps b1, z1) := by
        rw [JasminLsemAddrMem.runStraightF_append, hp, Option.bind_some,
          runStraightF_movesOf]
      obtain ⟨t', ht', hRs⟩ := lsemFuelMemF_prepend fn (pre ++ movesOf ps)
        (loop.map (renRM (renOf ps))) hpre' hB' b0 (movesState ps b1) zf z1 h0 hrunPre f tl'
        htl'
      refine ⟨t', ?_, tl, tl', rfl, ?_, hRt⟩
      · rw [List.length_append, movesOf_length] at ht'
        rw [show pre.length + f + ps.length = pre.length + ps.length + f by omega]
        exact ht'
      · rw [hRs.eq_shiftS, List.length_append, movesOf_length]

/-- **The array result of the renamed loop, at an explicit fuel.** Under the hypotheses of
    `renameLoop_getArr`, the renamed body halts at fuel `fuel + ps.length` in a state that
    holds at `renOf ps out` the array the run of `pre ++ loop` ends with at `out`. -/
theorem renameLoop_getArr_fuel (fn : String) (pre loop : List LinstrRM)
    (ps : List (String × String))
    (N : String → Prop) (hpre : ∀ i ∈ pre, IsLopn i) (hloop : ∀ i ∈ loop, CtlOK i)
    (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (b0 : LstateM) (zf : Bool) (h0 : b0.lpc = 0)
    (hA : ∀ b1 z1, runStraightF pre b0 zf = some (b1, z1) →
      ∀ r, N r → b1.larr (renOf ps r) = b1.larr r)
    (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (pre ++ loop)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some t)
    (out : String) (hout : N out) (w n : Nat) :
    ∃ t', lsemFuelMemF (singletonProgM fn (pre ++ movesOf ps ++ loop.map (renRM (renOf ps))))
        (fuel + ps.length) { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ t'.prog.base.getArr (renOf ps out) w n = t.prog.base.getArr out w n := by
  obtain ⟨t', ht', tl, tl', rfl, rfl, hR⟩ := renameLoop_sim_fuel fn pre loop ps N hpre hloop
    hcond hσ hn hnd hts hren hfresh b0 zf h0 hA fuel t hrun
  exact ⟨_, ht', by rw [shiftS_getArr, shiftS_getArr]; exact hR.1.getArr hout w n⟩

/-- **The virtual body from the exported node, at an explicit fuel.** Under the hypotheses of
    `src_chain`, the virtual body halts in one state at every fuel from
    `srcFuel pre0.length ps.length fuel` on, and the array of the renamed name of `out` in
    that state is the array of `out` at the end of the node. -/
theorem src_chain_fuel (fn : String) (pre0 seeds loop : List LinstrRM)
    (ps : List (String × String))
    (N : String → Prop) (hpre0 : ∀ i ∈ pre0, IsLopn i) (hseeds : ∀ i ∈ seeds, IsLopn i)
    (hloop : ∀ i ∈ loop, CtlOK i) (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (b0 b1 : LstateM) (zf : Bool) (h0 : b0.lpc = 0)
    (hpr : runStraightF pre0 b0 zf = some (b1, zf)) (hb1 : b1.setLpc 0 = b0)
    (hA : ∀ b2 z2, runStraightF (pre0 ++ seeds) b0 zf = some (b2, z2) →
      ∀ r, N r → b2.larr (renOf ps r) = b2.larr r)
    (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (seeds ++ loop)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some t)
    (out : String) (hout : N out) (w n : Nat) :
    ∃ t', (∀ k, srcFuel pre0.length ps.length fuel ≤ k → lsemFuelMemF
        (singletonProgM fn (pre0 ++ seeds ++ movesOf ps ++ loop.map (renRM (renOf ps))))
        k { prog := { base := b0, lfn := fn }, zf := zf } = some t')
      ∧ t'.prog.base.getArr (renOf ps out) w n = t.prog.base.getArr out w n := by
  have hB : ∀ i ∈ seeds ++ loop, CtlOK i := by
    intro i hi
    rcases List.mem_append.mp hi with h | h
    · exact Or.inl (hseeds i h)
    · exact hloop i h
  rw [← hb1] at hrun
  obtain ⟨t1, ht1, hR⟩ :=
    lsemFuelMemF_prepend fn pre0 (seeds ++ loop) hpre0 hB b0 b1 zf zf h0 hpr fuel t hrun
  rw [← List.append_assoc] at ht1
  have hpre : ∀ i ∈ pre0 ++ seeds, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with h | h
    · exact hpre0 i h
    · exact hseeds i h
  obtain ⟨t', ht', harr⟩ := renameLoop_getArr_fuel fn (pre0 ++ seeds) loop ps N hpre hloop
    hcond hσ hn hnd hts hren hfresh b0 zf h0 hA _ t1 ht1 out hout w n
  refine ⟨t', fun k hk => lsemFuelMemF_le _ ht' hk, ?_⟩
  rw [harr, hR.base, getArr_shift]

/-- **The virtual body with the fusion, at an explicit fuel.** Under the hypotheses of
    `src_chain_fuse`, the virtual body with the renamed loop fused halts in one state at
    every fuel from `srcFuseFuel pre0.length ps.length fuel` on, and the array of the renamed
    name of `out` in that state is the array of `out` at the end of the node. -/
theorem src_chain_fuse_fuel (fn : String) (pre0 seeds loop : List LinstrRM)
    (ps : List (String × String)) (N : String → Prop) (hpre0 : ∀ i ∈ pre0, IsLopn i)
    (hseeds : ∀ i ∈ seeds, IsLopn i)
    (hloop : ∀ i ∈ loop, CtlOK i) (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (b0 b1 : LstateM) (zf : Bool) (h0 : b0.lpc = 0)
    (hpr : runStraightF pre0 b0 zf = some (b1, zf)) (hb1 : b1.setLpc 0 = b0)
    (hA : ∀ b2 z2, runStraightF (pre0 ++ seeds) b0 zf = some (b2, z2) →
      ∀ r, N r → b2.larr (renOf ps r) = b2.larr r)
    {E : List String}
    (hfuse : fuseOKL E (fuseLoPre (pre0 ++ seeds ++ movesOf ps) (loop.map (renRM (renOf ps))))
      (pre0 ++ seeds ++ movesOf ps ++ loop.map (renRM (renOf ps))) = true)
    (hE : E64 E b0)
    (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (seeds ++ loop)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some t)
    (out : String) (hout : N out) (hkept : KeptN (renOf ps out)) (w n : Nat) :
    ∃ t', (∀ k, srcFuseFuel pre0.length ps.length fuel ≤ k → lsemFuelMemF
        (singletonProgM fn (pre0 ++ seeds ++ movesOf ps
          ++ fuseMulHiRM (loop.map (renRM (renOf ps)))))
        k { prog := { base := b0, lfn := fn }, zf := zf } = some t')
      ∧ t'.prog.base.getArr (renOf ps out) w n = t.prog.base.getArr out w n := by
  obtain ⟨t1, ht1, harr⟩ := src_chain_fuel fn pre0 seeds loop ps N hpre0 hseeds hloop hcond hσ
    hn hnd hts hren hfresh b0 b1 zf h0 hpr hb1 hA fuel t hrun out hout w n
  obtain ⟨f2, t2, hf2, ht2, hag, -, -⟩ :=
    fuseMulHi_lsemFuelMemF_pre hfuse fn _ t1 h0 hE _ (ht1 _ (Nat.le_refl _))
  refine ⟨t2, fun k hk => lsemFuelMemF_le _ ht2 (hf2.trans hk), ?_⟩
  rw [← harr]
  unfold LstateM.getArr
  rw [hag.arr _ hkept]

/-- The statement of `ImageAddrSrc.src_chain`, from `src_chain_fuel` at the fuel
    `srcFuel pre0.length ps.length fuel`. -/
theorem src_chain_of_fuel (fn : String) (pre0 seeds loop : List LinstrRM)
    (ps : List (String × String))
    (N : String → Prop) (hpre0 : ∀ i ∈ pre0, IsLopn i) (hseeds : ∀ i ∈ seeds, IsLopn i)
    (hloop : ∀ i ∈ loop, CtlOK i) (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (b0 b1 : LstateM) (zf : Bool) (h0 : b0.lpc = 0)
    (hpr : runStraightF pre0 b0 zf = some (b1, zf)) (hb1 : b1.setLpc 0 = b0)
    (hA : ∀ b2 z2, runStraightF (pre0 ++ seeds) b0 zf = some (b2, z2) →
      ∀ r, N r → b2.larr (renOf ps r) = b2.larr r)
    (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (seeds ++ loop)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some t)
    (out : String) (hout : N out) (w n : Nat) :
    ∃ fuel' t', lsemFuelMemF
        (singletonProgM fn (pre0 ++ seeds ++ movesOf ps ++ loop.map (renRM (renOf ps))))
        fuel' { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ t'.prog.base.getArr (renOf ps out) w n = t.prog.base.getArr out w n := by
  obtain ⟨t', hk, harr⟩ := src_chain_fuel fn pre0 seeds loop ps N hpre0 hseeds hloop hcond hσ
    hn hnd hts hren hfresh b0 b1 zf h0 hpr hb1 hA fuel t hrun out hout w n
  exact ⟨_, t', hk _ (Nat.le_refl _), harr⟩

/-- The statement of `ImageAddrSrc.src_chain_fuse`, from `src_chain_fuse_fuel` at the fuel
    `srcFuseFuel pre0.length ps.length fuel`. -/
theorem src_chain_fuse_of_fuel (fn : String) (pre0 seeds loop : List LinstrRM)
    (ps : List (String × String)) (N : String → Prop) (hpre0 : ∀ i ∈ pre0, IsLopn i)
    (hseeds : ∀ i ∈ seeds, IsLopn i)
    (hloop : ∀ i ∈ loop, CtlOK i) (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (b0 b1 : LstateM) (zf : Bool) (h0 : b0.lpc = 0)
    (hpr : runStraightF pre0 b0 zf = some (b1, zf)) (hb1 : b1.setLpc 0 = b0)
    (hA : ∀ b2 z2, runStraightF (pre0 ++ seeds) b0 zf = some (b2, z2) →
      ∀ r, N r → b2.larr (renOf ps r) = b2.larr r)
    {E : List String}
    (hfuse : fuseOKL E (fuseLoPre (pre0 ++ seeds ++ movesOf ps) (loop.map (renRM (renOf ps))))
      (pre0 ++ seeds ++ movesOf ps ++ loop.map (renRM (renOf ps))) = true)
    (hE : E64 E b0)
    (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (seeds ++ loop)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some t)
    (out : String) (hout : N out) (hkept : KeptN (renOf ps out)) (w n : Nat) :
    ∃ fuel' t', lsemFuelMemF
        (singletonProgM fn (pre0 ++ seeds ++ movesOf ps
          ++ fuseMulHiRM (loop.map (renRM (renOf ps)))))
        fuel' { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ t'.prog.base.getArr (renOf ps out) w n = t.prog.base.getArr out w n := by
  obtain ⟨t', hk, harr⟩ := src_chain_fuse_fuel fn pre0 seeds loop ps N hpre0 hseeds hloop
    hcond hσ hn hnd hts hren hfresh b0 b1 zf h0 hpr hb1 hA hfuse hE fuel t hrun out hout
    hkept w n
  exact ⟨_, t', hk _ (Nat.le_refl _), harr⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrcFuel
