/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

@[expose] public section

set_option autoImplicit false

/-!
# The virtual body of the register allocation check, from the exported node

The register allocation checker compares the image of a printed body with a virtual body
built from the exported node `seeds ++ loop`: a prefix `pre0` of moves that leaves the entry
state unchanged (the copies of the argument registers), the seeds, the copies `movesOf ps`
of the loop-carried names into their renamed names, and the loop renamed by `renOf ps`, with
its widening multiplies fused (`fuseMulHiRM`) when the route asks for it. This module derives
a halting run of that virtual body from a halting run of the exported node, with the array of
a name of the node at the end of its run the array of the renamed name at the end of the run
of the virtual body (`src_chain`), and through the fusion when it applies (`src_chain_fuse`).

## Main results

* `getArr_shift`: the arrays of a state do not depend on its program counter.
* `ImageAddrSrcFuel.renameLoop_sim_fuel`, `ImageAddrSrcFuel.src_chain_fuel`,
  `ImageAddrSrcFuel.src_chain_fuse_fuel`: the virtual body halts in one state at every fuel
  from `ImageAddrSrcFuel.srcFuel`, with the fusion `ImageAddrSrcFuel.srcFuseFuel`, on.
* `src_chain`: the moves in front, the copies and the renamed loop.
* `src_chain_fuse`: the same followed by the fusion of the renamed loop.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

theorem getArr_shift (b : LstateM) (p : Nat) (A : String) (w n : Nat) :
    (b.setLpc p).getArr A w n = b.getArr A w n := by
  unfold LstateM.getArr LstateM.setLpc
  rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrc

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
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)

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

/-- An instruction set whose steps contain those of `x86Isa` and whose further steps are local
    calls takes the step of `x86Isa` at every copy of `movesOf ps`: a copy is no shadow
    instruction of a call. -/
theorem movesOf_agree {I : Isa} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao) (ps : List (String × String)) :
    ∀ i ∈ movesOf ps, ∀ (Q : LprogM) (s : LstateMF), I.step Q i s = x86Isa.step Q i s := by
  intro i hi Q s
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  refine Isa.CallLocal.step_eq I hle hcl Q ?_ s
  simp only [JasminLsemExportLower.movWire, LprogIsa.shadowCall?]
  rfl

/-- **The loop renamed behind the copies, at an explicit fuel, at an instruction set with local
    calls.** For an instruction set `I` whose steps contain those of `x86Isa` and whose further
    steps are local calls, under the hypotheses of `renameLoop_sim` and a prefix `pre` at whose
    instructions the step of `I` is the step of `x86Isa` (every instruction that is no shadow
    instruction of a call, by `Isa.CallLocal.step_eq`), a halting run of `I` on `pre ++ loop`
    at fuel `fuel` is matched by a halting run of `I` on
    `pre ++ movesOf ps ++ map (renRM (renOf ps)) loop` at fuel `fuel + ps.length`, the final
    states related as in `renameLoop_sim`. -/
theorem renameLoop_sim_fuel_calls {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    (fn : String)
    (pre loop : List LinstrRM) (ps : List (String × String))
    (N : String → Prop) (hpre : ∀ i ∈ pre, IsLopn i)
    (hagree : ∀ i ∈ pre, ∀ (Q : LprogM) (s : LstateMF), I.step Q i s = x86Isa.step Q i s)
    (hloop : ∀ i ∈ loop, CtlOK i)
    (hcond : ∀ i ∈ loop, CondOK i) (hσ : RenOn (renOf ps) N)
    (hn : ∀ i ∈ loop, ∀ n ∈ instrNames i.1, N n) (hnd : (ps.map Prod.snd).Nodup)
    (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) (hren : ∀ p ∈ ps, renOf ps p.1 = p.2)
    (hfresh : ∀ p ∈ ps, ¬ N p.2) (b0 : LstateM) (zf : Bool) (h0 : b0.lpc = 0)
    (hA : ∀ b1 z1, runStraightF pre b0 zf = some (b1, z1) →
      ∀ r, N r → b1.larr (renOf ps r) = b1.larr r)
    (fuel : Nat) (t : LstateMF)
    (hrun : I.lsemFuelMemF (singletonProgM fn (pre ++ loop)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some t) :
    ∃ t', I.lsemFuelMemF
        (singletonProgM fn (pre ++ movesOf ps ++ loop.map (renRM (renOf ps))))
        (fuel + ps.length) { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ ∃ tl tl', t = shiftS pre.length tl ∧ t' = shiftS (pre.length + ps.length) tl'
        ∧ RelF (renOf ps) N tl tl' := by
  have hpos : ∀ j, j < pre.length →
      (singletonProgM fn (pre ++ loop)).body[b0.lpc + j]? = pre[j]? := fun j hj => by
    simp only [singletonProgM, h0, Nat.zero_add]
    exact List.getElem?_append_left hj
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le
    (lsemFuelMemF_seg_fuel_calls hcl _ fn rfl pre b0 zf fuel t hpre hpos hrun)
  rw [lsemFuelMemF_segF_agree _ fn rfl pre b0 zf f hpre hagree hpos] at hrun
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
      obtain ⟨tl, htl, rfl⟩ :=
        lsemFuelMemF_of_prefix_calls hle hcl fn pre loop hpre hloop f _ t hrun
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
      obtain ⟨tl', htl', hRt⟩ :=
        lsemFuelMemF_map_renRM_calls hle hcl hσ fn loop hn hcond f hR htl
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
      obtain ⟨t', ht', hRs⟩ := lsemFuelMemF_prepend_calls hle hcl fn (pre ++ movesOf ps)
        (loop.map (renRM (renOf ps))) hpre' hB' b0 (movesState ps b1) zf z1 h0 hrunPre f tl'
        htl'
      refine ⟨t', ?_, tl, tl', rfl, ?_, hRt⟩
      · rw [List.length_append, movesOf_length] at ht'
        rw [show pre.length + f + ps.length = pre.length + ps.length + f by omega]
        exact ht'
      · rw [hRs.eq_shiftS, List.length_append, movesOf_length]

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
  rw [← x86Isa_lsemFuelMemF] at hrun ⊢
  exact renameLoop_sim_fuel_calls (Isa.StepLe.refl x86Isa)
    (Isa.CallLocal.refl x86Isa (fun _ _ => none)) fn pre loop ps N hpre
    (fun _ _ _ _ => rfl) hloop hcond hσ hn hnd hts hren hfresh b0 zf h0 hA fuel t hrun

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

/-- **The virtual body from the exported node, at an explicit fuel.** Let `pre0` be moves
    that leave the entry base `b0` unchanged but for the program counter, and let the renaming
    `ps` of the loop satisfy the conditions of `renameLoop_sim` behind `pre0 ++ seeds`. For a
    halting run of the node `seeds ++ loop` from `b0` at fuel `fuel`, the virtual body halts
    in one state at every fuel from `srcFuel pre0.length ps.length fuel` on, and the array of
    the renamed name of `out` in that state is the array of `out` at the end of the node. -/
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

/-- **The virtual body with the fusion, at an explicit fuel.** Under the conditions of
    `src_chain_fuel`, and the fusion check `fuseOKL` of the renamed loop behind
    `pre0 ++ seeds ++ movesOf ps` at registers `E` of width `64` at entry, the virtual body
    with the renamed loop fused halts in one state at every fuel from
    `srcFuseFuel pre0.length ps.length fuel` on, and the array of the renamed name of `out`, a
    name other than `R15`, in that state is the array of `out` at the end of the node. -/
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

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrcFuel

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

/-- **The virtual body from the exported node.** Let `pre0` be moves that leave the entry
    base `b0` unchanged but for the program counter, and let the renaming `ps` of the loop
    satisfy the conditions of `renameLoop_sim` behind `pre0 ++ seeds`. A halting run of the
    node `seeds ++ loop` from `b0` is matched by a halting run of
    `pre0 ++ seeds ++ movesOf ps ++ loop.map (renRM (renOf ps))` from `b0`, in which the array
    of the renamed name of `out` at the end is the array of `out` at the end of the node. -/
theorem src_chain (fn : String) (pre0 seeds loop : List LinstrRM) (ps : List (String × String))
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
      ∧ t'.prog.base.getArr (renOf ps out) w n = t.prog.base.getArr out w n :=
  (ImageAddrSrcFuel.src_chain_fuel fn pre0 seeds loop ps N hpre0 hseeds hloop hcond hσ hn hnd
    hts hren hfresh b0 b1 zf h0 hpr hb1 hA fuel t hrun out hout w n).elim
    fun t' h => ⟨_, t', h.1 _ (Nat.le_refl _), h.2⟩

/-- **The virtual body from the exported node, with the fusion.** Under the conditions of
    `src_chain`, and the fusion check `fuseOKL` of the renamed loop behind
    `pre0 ++ seeds ++ movesOf ps` at registers `E` of width `64` at entry, a halting run of the
    node is matched by a halting run of the virtual body with the renamed loop fused, in which
    the array of the renamed name of `out`, a name other than `R15`, is the array of
    `out` at the end of the node. -/
theorem src_chain_fuse (fn : String) (pre0 seeds loop : List LinstrRM)
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
      ∧ t'.prog.base.getArr (renOf ps out) w n = t.prog.base.getArr out w n :=
  (ImageAddrSrcFuel.src_chain_fuse_fuel fn pre0 seeds loop ps N hpre0 hseeds hloop hcond hσ hn
    hnd hts hren hfresh b0 b1 zf h0 hpr hb1 hA hfuse hE fuel t hrun out hout hkept w n).elim
    fun t' h => ⟨_, t', h.1 _ (Nat.le_refl _), h.2⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrc
