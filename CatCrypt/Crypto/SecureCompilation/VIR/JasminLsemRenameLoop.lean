/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites

@[expose] public section

set_option autoImplicit false

/-!
# A loop renamed behind copies of its carried names

A virtual body `pre ++ loop` keeps the values its loop carries under virtual names. Behind a
register allocation the same values sit in other registers or frame slots, and at the loop
head they need not sit where they sat at the entry. For a list `ps` of pairs `(x, y)`, the
body `pre ++ movesOf ps ++ map (renRM (renOf ps)) loop` copies each `x` into `y` after the
prefix and runs the loop with every `x` replaced by `y`. This module proves that every halting
run of `pre ++ loop` on the flag machine `lsemFuelMemF` is matched by a halting run of the
renamed body into a state related by the renaming.

## Main results

* `renOf`, `movesOf`, `movesState`: the renaming of the pairs, their copies and the state
  the copies leave.
* `runStraightF_movesOf`, `movesState_target`, `movesState_other`, `movesState_larr`: the
  copies run to `movesState`, which holds each source's value at its target and keeps every
  other register, the arrays, the word memory and the flags.
* `renOf_of_not_mem`, `ctlOK_renRM`: the renaming off the sources, and the covered
  instructions under a renaming.
* `lsemFuelMemF_seg_fuel`: a halting run through a straight segment at the program counter
  spends at least its length in fuel.
* `renameLoop_sim`: the simulation of `pre ++ loop` by the renamed body.
* `shiftS_getArr`, `shiftS_getW`, `renameLoop_getArr`: the array result of `pre ++ loop` read
  back at the renamed name in the final state of the renamed body.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix

/-! ## 1. The copies -/

/-- The renaming of a list of pairs `(x, y)`: `x` to the `y` of its first pair, the identity
    off the first components. -/
def renOf (ps : List (String × String)) (n : String) : String :=
  ((ps.find? (·.1 == n)).map (·.2)).getD n

/-- The copies `MOV:64 y, x` of the pairs `(x, y)`, in order. -/
def movesOf (ps : List (String × String)) : List LinstrRM :=
  ps.map fun p => (movWire p.2 p.1 "MOV:64", .reg none)

/-- The base the copies of `ps` leave from `b`. -/
def movesState : List (String × String) → LstateM → LstateM
  | [], b => b
  | p :: ps, b => movesState ps ((b.setReg p.2 (b.reg.lvm p.1).2).nextPc)

theorem runStraightF_movesOf (ps : List (String × String)) :
    ∀ (b : LstateM) (zf : Bool), runStraightF (movesOf ps) b zf = some (movesState ps b, zf) := by
  induction ps with
  | nil => intro b zf; rfl
  | cons p ps ih =>
      intro b zf
      simp only [movesOf, List.map_cons, runStraightF_cons]
      rw [fstepF_movWire _ _ _ _ rfl, Option.bind_some]
      exact ih _ _

theorem movesOf_isLopn (ps : List (String × String)) : ∀ i ∈ movesOf ps, IsLopn i := by
  intro i hi
  simp only [movesOf, List.mem_map] at hi
  obtain ⟨p, -, rfl⟩ := hi
  exact ⟨_, _, _, rfl⟩

theorem movesOf_length (ps : List (String × String)) : (movesOf ps).length = ps.length := by
  simp [movesOf]

theorem movesState_other (ps : List (String × String)) :
    ∀ (b : LstateM) (r : String), r ∉ ps.map Prod.snd →
      (movesState ps b).reg.lvm r = b.reg.lvm r := by
  induction ps with
  | nil => intro b r _; rfl
  | cons p ps ih =>
      intro b r hr
      simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [movesState, ih _ r hr.2]
      simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, LstateN.setReg, hr.1]

theorem movesState_larr (ps : List (String × String)) :
    ∀ b : LstateM, (movesState ps b).larr = b.larr ∧ (movesState ps b).lmem = b.lmem
      ∧ (movesState ps b).cf = b.cf ∧ (movesState ps b).of = b.of := by
  induction ps with
  | nil => intro b; exact ⟨rfl, rfl, rfl, rfl⟩
  | cons p ps ih =>
      intro b
      obtain ⟨h1, h2, h3, h4⟩ := ih ((b.setReg p.2 (b.reg.lvm p.1).2).nextPc)
      exact ⟨h1, h2, h3, h4⟩

theorem movesState_lpc (ps : List (String × String)) :
    ∀ b : LstateM, (movesState ps b).lpc = b.lpc + ps.length := by
  induction ps with
  | nil => intro b; rfl
  | cons p ps ih =>
      intro b
      rw [movesState, ih]
      simp only [LstateM.lpc, LstateM.nextPc, LstateM.setReg, LstateN.nextPc, LstateN.setReg,
        List.length_cons]
      omega

/-- The copies leave at each target `y` the value the base held at its source `x`, when the
    targets are pairwise distinct and no target is a source. -/
theorem movesState_target (ps : List (String × String))
    (hnd : (ps.map Prod.snd).Nodup) (hts : ∀ p ∈ ps, ∀ q ∈ ps, q.2 ≠ p.1) :
    ∀ (b : LstateM), ∀ p ∈ ps, (movesState ps b).reg.lvm p.2 = b.reg.lvm p.1 := by
  induction ps with
  | nil => intro b p hp; cases hp
  | cons q ps ih =>
      intro b p hp
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [movesState]
      rcases List.mem_cons.mp hp with rfl | hp
      · rw [movesState_other ps _ p.2 hnd.1]
        simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, LstateN.setReg]
      · rw [ih hnd.2 (fun a ha c hc => hts a (List.mem_cons_of_mem _ ha) c
          (List.mem_cons_of_mem _ hc)) _ p hp]
        have hne : p.1 ≠ q.2 := fun h => hts p (List.mem_cons_of_mem _ hp) q
          List.mem_cons_self h.symm
        simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, LstateN.setReg, hne]

/-! ## 2. Fuel through a straight segment -/

/-- A halting run that starts at a straight segment of `Lopn` instructions spends at least the
    length of the segment in fuel. -/
theorem lsemFuelMemF_seg_fuel (P : LprogM) (fn : String) (hfn : fn = P.lfn) :
    ∀ (seg : List LinstrRM) (b0 : LstateM) (zf : Bool) (k : Nat) (t : LstateMF),
      (∀ i ∈ seg, IsLopn i) →
      (∀ j, j < seg.length → P.body[b0.lpc + j]? = seg[j]?) →
      lsemFuelMemF P k { prog := { base := b0, lfn := fn }, zf := zf } = some t →
      seg.length ≤ k := by
  intro seg
  induction seg with
  | nil => intro _ _ _ _ _ _ _; exact Nat.zero_le _
  | cons i seg ih =>
      intro b0 zf k t hl hpos h
      have hfetch : findInstrMem P { base := b0, lfn := fn } = some i := by
        unfold findInstrMem
        rw [if_pos hfn]
        simpa using hpos 0 (by simp)
      cases k with
      | zero => simp [lsemFuelMemF, hfetch] at h
      | succ k =>
          rw [lsemFuelMemF, hfetch] at h
          simp only at h
          rw [evalInstrPMemF_isLopn P i _ (hl i List.mem_cons_self)] at h
          cases hb : fstepF i b0 zf with
          | none => simp [hb] at h
          | some bz =>
              obtain ⟨b1, z1⟩ := bz
              simp only [hb, Option.map_some] at h
              have hpc := fstepF_lpc_succ _ _ _ _ _ hb
              have := ih b1 z1 k t (fun j hj => hl j (List.mem_cons_of_mem _ hj))
                (fun j hj => by
                  rw [hpc, Nat.add_assoc, Nat.add_comm 1 j]
                  simpa using hpos (j + 1) (by simp; omega)) h
              simp only [List.length_cons]
              omega

/-! ## 3. The renamed loop -/

theorem renOf_of_not_mem {ps : List (String × String)} {r : String}
    (h : r ∉ ps.map Prod.fst) : renOf ps r = r := by
  unfold renOf
  rw [List.find?_eq_none.mpr (fun p hp => by
    simp only [beq_iff_eq]
    rintro rfl
    exact h (List.mem_map_of_mem hp))]
  rfl

theorem ctlOK_renRM (σ : String → String) {i : LinstrRM} (h : CtlOK i) : CtlOK (renRM σ i) := by
  obtain ⟨w, tag⟩ := i
  rcases h with ⟨d, o, s, hd⟩ | ⟨kd, l, hw⟩ | ⟨c, l, hw, hcc⟩ | ⟨tgt, hw⟩
  · simp only at hd
    subst hd
    exact Or.inl ⟨_, _, _, rfl⟩
  · simp only at hw
    subst hw
    exact Or.inr (Or.inl ⟨kd, l, rfl⟩)
  · simp only at hw
    subst hw
    exact Or.inr (Or.inr (Or.inl ⟨c, l, rfl, hcc⟩))
  · simp only at hw
    subst hw
    exact Or.inr (Or.inr (Or.inr ⟨tgt, rfl⟩))

/-- **The loop renamed behind the copies.** Let `pre` be a straight prefix and `loop` a body of
    `Lopn` instructions, labels, zero-flag conditionals and gotos, with no `MULX`, whose names
    lie in `N`. Let the pairs `ps` have pairwise distinct targets outside `N`, no target among
    the sources, and their renaming `renOf ps` usable on `N` and sending each source to its
    target. If the state the prefix leaves holds at each renamed array name the array of its
    source, then every halting run of `pre ++ loop` from a base at program counter `0` is
    matched by a halting run of `pre ++ movesOf ps ++ map (renRM (renOf ps)) loop` from the same
    base; the final states, with their program counters moved back by the lengths of the code
    in front of the loop, are related by `RelF (renOf ps) N`. -/
theorem renameLoop_sim (fn : String) (pre loop : List LinstrRM) (ps : List (String × String))
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
    ∃ fuel' t', lsemFuelMemF (singletonProgM fn (pre ++ movesOf ps ++ loop.map (renRM (renOf ps))))
        fuel' { prog := { base := b0, lfn := fn }, zf := zf } = some t'
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
      refine ⟨(pre ++ movesOf ps).length + f, t', ?_, tl, tl', rfl, ?_, hRt⟩
      · exact ht'
      · rw [hRs.eq_shiftS, List.length_append, movesOf_length]

/-! ## 4. The result read back at the renamed name -/

theorem shiftS_getArr (d : Nat) (s : LstateMF) (r : String) (w n : Nat) :
    (shiftS d s).prog.base.getArr r w n = s.prog.base.getArr r w n := rfl

theorem shiftS_getW (d : Nat) (s : LstateMF) (r : String) (w : Nat) :
    (shiftS d s).prog.base.reg.getW r w = s.prog.base.reg.getW r w := rfl

/-- **The array result of the renamed loop.** Under the hypotheses of `renameLoop_sim`, for an
    array name `out` of `N`, the renamed body halts in a state that holds at `renOf ps out`
    the array the run of `pre ++ loop` ends with at `out`. -/
theorem renameLoop_getArr (fn : String) (pre loop : List LinstrRM) (ps : List (String × String))
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
    ∃ fuel' t', lsemFuelMemF (singletonProgM fn (pre ++ movesOf ps ++ loop.map (renRM (renOf ps))))
        fuel' { prog := { base := b0, lfn := fn }, zf := zf } = some t'
      ∧ t'.prog.base.getArr (renOf ps out) w n = t.prog.base.getArr out w n := by
  obtain ⟨fuel', t', ht', tl, tl', rfl, rfl, hR⟩ := renameLoop_sim fn pre loop ps N hpre hloop
    hcond hσ hn hnd hts hren hfresh b0 zf h0 hA fuel t hrun
  exact ⟨fuel', _, ht', by rw [shiftS_getArr, shiftS_getArr]; exact hR.1.getArr hout w n⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop
