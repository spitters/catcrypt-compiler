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
  obtain ⟨fuel', t', ht', harr⟩ := renameLoop_getArr fn (pre0 ++ seeds) loop ps N hpre hloop
    hcond hσ hn hnd hts hren hfresh b0 zf h0 hA _ t1 ht1 out hout w n
  refine ⟨fuel', t', ht', ?_⟩
  rw [harr, hR.base, getArr_shift]

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
      ∧ t'.prog.base.getArr (renOf ps out) w n = t.prog.base.getArr out w n := by
  obtain ⟨f1, t1, ht1, harr⟩ := src_chain fn pre0 seeds loop ps N hpre0 hseeds hloop hcond hσ
    hn hnd hts hren hfresh b0 b1 zf h0 hpr hb1 hA fuel t hrun out hout w n
  obtain ⟨f2, t2, -, ht2, hag, -, -⟩ := fuseMulHi_lsemFuelMemF_pre hfuse fn _ t1 h0 hE f1 ht1
  refine ⟨f2, t2, ht2, ?_⟩
  rw [← harr]
  unfold LstateM.getArr
  rw [hag.arr _ hkept]

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSrc
