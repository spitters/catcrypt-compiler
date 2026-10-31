/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPostFuseLift
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# The basic-block optimiser commutes with the width reading of `MULX`

`RegionPostFuseLift.normMulxBody` reads every two-output `MULX` of a body at its width `MULX:64`.
The basic-block optimiser `LprogOptPipeline.optimizeBasicBlocks` reads an instruction only
through `isCtlInstr`, `instrModeled` and its flag effect, and each of these takes the same value
on `MULX` and on `MULX:64`; it rewrites only segments in the modelled fragment, which contains
no `MULX` and whose passes emit no mnemonic outside their input. The optimiser therefore
commutes with `normMulxBody`.

## Main results

* `splitStraightRunsAux_normMulxBody`: the segmentation commutes with the width reading.
* `optRunBody_normMulxBody`: the optimiser of one segment commutes with the width reading.
* `optimizeBasicBlocks_normMulxBody`: the basic-block optimiser commutes with `normMulxBody`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxOpt

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (normMulx)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPostFuseLift (normMulxBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdFlags
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (copyPropagateBody copyPropagateBody_mnems instrMnem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim
  (reloadElimBody reloadElimBody_sublist)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler (scheduleBody scheduleBody_perm)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad (elimReloads elimReloads_sublist)
open CatCrypt.Crypto.Optimizer.LoadCSE (loadCSE loadCSE_mnem_mem)

/-- One instruction read with its `MULX` at width `MULX:64`; the map of `normMulxBody`. -/
def normI (j : Linstr) : Linstr := ⟨j.li_ii, normMulx j.li_i⟩

/-- `MULX:64` strips to the base `MULX`. -/
theorem stripWidthTag_mulx64 : stripWidthTag (withWidthTag 64 "MULX") = "MULX" := by
  decide +kernel

/-- The untagged `MULX` is its own base. -/
theorem stripWidthTag_mulx : stripWidthTag "MULX" = "MULX" := by
  decide +kernel

/-- `MULX:64` is no count-tagged immediate shift. -/
theorem parseImmShiftMnem_mulx64 : parseImmShiftMnem (withWidthTag 64 "MULX") = none := by
  decide +kernel

/-- `MULX` is no count-tagged immediate shift. -/
theorem parseImmShiftMnem_mulx : parseImmShiftMnem "MULX" = none := by
  decide +kernel

/-- An instruction without the mnemonic `MULX` is fixed by the width reading. -/
theorem normI_of_mnem (j : Linstr) (h : instrMnem j ≠ some "MULX") : normI j = j := by
  rcases j with ⟨ii, ins⟩
  cases ins <;> simp_all [normI, normMulx, instrMnem]

/-- The width reading keeps the control-flow test. -/
theorem isCtlInstr_normI (j : Linstr) : isCtlInstr (normI j) = isCtlInstr j := by
  rcases j with ⟨ii, ins⟩
  cases ins <;> simp [normI, normMulx, isCtlInstr]

/-- The width reading keeps the flag effect. -/
theorem flagEffect_normI (j : Linstr) : flagEffect (normI j) = flagEffect j := by
  rcases j with ⟨ii, ins⟩
  cases ins with
  | Lopn ds o ss =>
    by_cases ho : o = "MULX"
    · subst ho
      simp only [normI, normMulx, ite_true, flagEffect, opnEffect, stripWidthTag_mulx64,
        stripWidthTag_mulx]
    · simp [normI, normMulx, ho]
  | _ => simp [normI, normMulx]

/-- An `Lopn` whose mnemonic strips to `MULX` and is no immediate shift is outside the
    modelled fragment. -/
theorem instrModeled_lopn_mulx (ii : Nat) (ds : List LOperand) (o : String)
    (ss : List LOperand) (h1 : stripWidthTag o = "MULX") (h2 : parseImmShiftMnem o = none) :
    instrModeled ⟨ii, .Lopn ds o ss⟩ = false := by
  unfold instrModeled
  split
  · grind only [Option.isSome_iff_ne_none]
  · rfl

/-- An instruction with the mnemonic `MULX` is outside the modelled fragment. -/
theorem instrModeled_of_mnem (j : Linstr) (h : instrMnem j = some "MULX") :
    instrModeled j = false := by
  rcases j with ⟨ii, ins⟩
  cases ins <;> simp only [instrMnem, Option.some.injEq, reduceCtorEq] at h
  subst h
  exact instrModeled_lopn_mulx _ _ _ _ stripWidthTag_mulx parseImmShiftMnem_mulx

/-- The width reading keeps membership in the modelled fragment. -/
theorem instrModeled_normI (j : Linstr) : instrModeled (normI j) = instrModeled j := by
  rcases j with ⟨ii, ins⟩
  cases ins with
  | Lopn ds o ss =>
    by_cases ho : o = "MULX"
    · subst ho
      simp only [normI, normMulx, ite_true]
      rw [instrModeled_lopn_mulx _ _ _ _ stripWidthTag_mulx64 parseImmShiftMnem_mulx64,
        instrModeled_lopn_mulx _ _ _ _ stripWidthTag_mulx parseImmShiftMnem_mulx]
    · simp [normI, normMulx, ho]
  | _ => simp [normI, normMulx]

/-- The width reading keeps flag neutrality. -/
theorem flagNeutral_normI (j : Linstr) : flagNeutral (normI j) = flagNeutral j := by
  rcases j with ⟨ii, ins⟩
  have h := flagEffect_normI ⟨ii, ins⟩
  cases ins <;> simp_all [normI, normMulx, flagNeutral]

/-- The width reading keeps the full-flag-writer test. -/
theorem flagKill_normI (j : Linstr) : flagKill (normI j) = flagKill j := by
  simp [flagKill, flagEffect_normI]

/-- The forward flag-liveness scan takes the same value on the width reading. -/
theorem flagsLiveAux_normI (b : Bool) (l : List Linstr) :
    flagsLiveAux b (l.map normI) = flagsLiveAux b l := by
  induction l generalizing b with
  | nil => rfl
  | cons i rest ih => simp only [List.map_cons, flagsLiveAux, flagEffect_normI, ih]

/-- Flag liveness takes the same value on the width reading. -/
theorem flagsLive_normI (l : List Linstr) : flagsLive (l.map normI) = flagsLive l :=
  flagsLiveAux_normI false l

/-- `flagHold` takes the same value on the width reading. -/
theorem flagHold_normI (cur l : List Linstr) :
    flagHold (cur.map normI) (l.map normI) = flagHold cur l := by
  simp [flagHold, flagsLive_normI, Function.comp_def, flagNeutral_normI]

/-- `pinStart` takes the same value on the width reading. -/
theorem pinStart_normI (cur : List Linstr) : pinStart (cur.map normI) = pinStart cur := by
  induction cur with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, pinStart, ih, List.any_map, Function.comp_def, flagKill_normI,
      flagNeutral_normI]

/-- `flushRun` commutes with the width reading. -/
theorem flushRun_normI (cur l : List Linstr) :
    flushRun (cur.map normI) (l.map normI) = (flushRun cur l).map (List.map normI) := by
  simp only [flushRun, flagsLive_normI, pinStart_normI, ← List.map_take, ← List.map_drop]
  split <;> split <;> simp_all [Function.comp_def]

/-- The segmentation of `splitStraightRunsAux` commutes with the width reading. -/
theorem splitStraightRunsAux_normMulxBody (cur l : List Linstr) :
    splitStraightRunsAux (cur.map normI) (l.map normI)
      = (splitStraightRunsAux cur l).map (List.map normI) := by
  induction l generalizing cur with
  | nil => cases cur <;> simp [splitStraightRunsAux]
  | cons i rest ih =>
    have hc := flushRun_normI cur (i :: rest)
    have hh := flagHold_normI cur (i :: rest)
    have ih1 := ih (cur ++ [i])
    have ih0 := ih []
    simp only [List.map_cons, List.map_append, List.map_nil] at hc hh ih1 ih0
    simp only [List.map_cons, splitStraightRunsAux, isCtlInstr_normI, instrModeled_normI, hh]
    split
    · simp [hc, ih0]
    · split
      · exact ih1
      · cases cur <;> simp [ih0]

/-- The width reading keeps a body straight-line. -/
theorem bodyIsStraightLine_normI (seg : List Linstr) :
    bodyIsStraightLine (seg.map normI) = bodyIsStraightLine seg := by
  induction seg with
  | nil => rfl
  | cons i rest ih => rw [List.map_cons, bodyIsStraightLine_cons, bodyIsStraightLine_cons,
      isCtlInstr_normI, ih]

/-- The width reading keeps a body inside the modelled fragment. -/
theorem bodyAllModeled_normI (seg : List Linstr) :
    bodyAllModeled (seg.map normI) = bodyAllModeled seg := by
  simp [bodyAllModeled, List.all_map, Function.comp_def, instrModeled_normI]

/-- Every instruction of the optimised modelled segment carries a mnemonic other than
    `MULX`. -/
theorem optRunBody_mnem (seg : List Linstr) (hm : bodyAllModeled seg = true) :
    ∀ j ∈ optRunBody seg, instrMnem j ≠ some "MULX" := by
  have hmn : ∀ j : Linstr, instrMnem j = CatCrypt.Crypto.Optimizer.LoadCSE.mnemOf j.li_i := by
    intro j
    rcases j with ⟨_, ins⟩
    cases ins <;> rfl
  intro j hj hmx
  simp only [optRunBody, hm, ite_true] at hj
  obtain ⟨j1, hj1, he1⟩ := loadCSE_mnem_mem _ j hj
  obtain ⟨j2, hj2, he2⟩ := List.mem_map.1
    ((copyPropagateBody_mnems _).subset (List.mem_map_of_mem (f := instrMnem) hj1))
  have hj2' : j2 ∈ seg := (elimReloads_sublist seg).subset
    ((reloadElimBody_sublist _).subset ((scheduleBody_perm _).subset hj2))
  have hmod := List.all_eq_true.mp hm j2 hj2'
  rw [instrModeled_of_mnem j2 (by rw [he2, hmn, he1, ← hmn, hmx])] at hmod
  exact absurd hmod (by decide)

/-- The optimiser of one segment commutes with the width reading. -/
theorem optRunBody_normMulxBody (seg : List Linstr) :
    optRunBody (seg.map normI) = (optRunBody seg).map normI := by
  by_cases hm : bodyAllModeled seg = true
  · have hseg : seg.map normI = seg := by
      refine (List.map_congr_left fun j hj => normI_of_mnem j fun h => ?_).trans
        (List.map_id _)
      have := List.all_eq_true.mp hm j hj
      rw [instrModeled_of_mnem j h] at this
      exact absurd this (by decide)
    have hout : (optRunBody seg).map normI = optRunBody seg :=
      (List.map_congr_left fun j hj => normI_of_mnem j (optRunBody_mnem seg hm j hj)).trans
        (List.map_id _)
    rw [hseg, hout]
  · have hm' : bodyAllModeled (seg.map normI) = false := by
      simpa [bodyAllModeled_normI] using hm
    simp [optRunBody, hm', hm]

/-- The basic-block optimiser commutes with the width reading of every instruction. -/
theorem optimizeBasicBlocks_map_normI (b : Lcmd) :
    optimizeBasicBlocks (b.map normI) = (optimizeBasicBlocks b).map normI := by
  have h0 := splitStraightRunsAux_normMulxBody [] b
  simp only [List.map_nil] at h0
  simp only [optimizeBasicBlocks, splitStraightRuns, h0, List.map_map,
    List.map_flatten]
  congr 1
  refine List.map_congr_left fun seg _ => ?_
  simp only [Function.comp_apply, bodyIsStraightLine_normI, optRunBody_normMulxBody]
  split <;> rfl

/-- **The basic-block optimiser commutes with `normMulxBody`**, the reading of every `MULX` at its
    width `MULX:64`. -/
theorem optimizeBasicBlocks_normMulxBody (b : Lcmd) :
    optimizeBasicBlocks (normMulxBody b) = normMulxBody (optimizeBasicBlocks b) :=
  optimizeBasicBlocks_map_normI b

end CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxOpt
