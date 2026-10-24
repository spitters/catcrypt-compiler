/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Common

/-!
# Redundant-reload elimination over the uniform-width run with flags

`LprogStoreToLoad.elimReloads` deletes a reload `MOV R ← K` when the held environment
records that `R` already holds `K`. This module proves that the pass preserves the run
`LsemBridge.lsemStraightFlag`, the uniform-width run that carries the flags `cf`, `of`:
where the input body runs, the output body runs to a state with the same registers, the
same word memory and the same flags.

The pass deletes only single-destination, single-source moves. Such an instruction is
accepted by none of the three recognizers of the flag layer
(`Common.lsemStepFlag_one_src`), so it neither reads nor writes a flag and its deletion
keeps both flags. The invariant `LprogStoreToLoad.HeldSound` reads the state through the
register map only, and a kept step changes only the registers `writtenNames` lists
(`Common.lsemStepFlag_lvm_of_not_written`), including a carry-family step and a widening
multiply, which `lsemStep` does not take.

The fragment with flags `LsemBridge.fragFB` has no single-source register move, so the pass
is the identity on a body of the fragment (`elimReloads_eq_of_fragFB`) and the statement on
the flag machine is an equality of runs with no side condition.

## Main definitions

This module defines no new notion; it states `LprogStoreToLoad.elimReloads` over
`LsemBridge.lsemStraightFlag`.

## Main results

* `heldSound_stepF` — a kept step with flags preserves `HeldSound`.
* `lsemStepFlag_drop` — a dropped reload steps to a state with the same registers, word
  memory and flags.
* `elimAux_simF` — the scan is a forward simulation up to `Common.SameF`.
* `elimReloads_lsemStraightFlag` — the pass preserves the run with flags.
* `elimReloads_eq_of_fragFB`, `elimReloads_lsemStraightMemF_F` — the pass on a body of the
  fragment with flags, and on the flag machine.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.StoreToLoad

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyProp
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Common

/-! ## 1. The invariant under a step with flags -/

/-- `HeldSound` reads the state through the register map only. -/
theorem heldSound_of_lvm {h : Held} {s t : Lstate 64} (hs : HeldSound h s)
    (e : t.lvm = s.lvm) : HeldSound h t := by
  intro p hp
  rw [e]
  exact hs p hp

/-- A kept step with flags carries the environment agreement from the state before to the
    state after. -/
theorem heldSound_stepF {h : Held} {i : LinstrR} (tg : MemTag) {s t : Lstate 64}
    (hs : HeldSound h s) (hstep : lsemStepFlag (i, tg) s = some t)
    (hkeep : (stepReload h i).1 = true) : HeldSound (stepReload h i).2 t := by
  cases hst : lsemStep i s with
  | some b =>
    rw [lsemStepFlag_of_lsemStep (i := (i, tg)) hst, Option.some.injEq] at hstep
    subst hstep
    exact heldSound_of_lvm (heldSound_step hs hst hkeep) (withALUFlagsL_lvm _ _ _)
  | none =>
    have hr : asReload i = none := by
      cases hr : asReload i with
      | none => rfl
      | some dk =>
        obtain ⟨d, k⟩ := dk
        rw [lsemStep_asReload hr s] at hst
        exact absurd hst (by simp)
    rw [stepReload_env_of_notReload hr]
    intro p hp
    obtain ⟨hp1, hn2⟩ := mem_foldl_killSlot _ _ p hp
    obtain ⟨hp2, hn1⟩ := mem_foldl_killReg _ _ p hp1
    rw [lsemStepFlag_lvm_of_not_written hstep hn1, lsemStepFlag_lvm_of_not_written hstep hn2]
    exact hs p hp2

/-- A dropped reload steps with flags to a state with the same registers, word memory and
    flags. -/
theorem lsemStepFlag_drop {h : Held} {i : LinstrR} (tg : MemTag) {s : Lstate 64}
    (hs : HeldSound h s) (hdrop : (stepReload h i).1 = false) :
    ∃ b, lsemStepFlag (i, tg) s = some b ∧ SameF b s := by
  obtain ⟨d, k, hr, hf⟩ := stepReload_drop_is_held_reload h i hdrop
  have hdk : s.lvm d = s.lvm k := hs _ (mem_of_find hf)
  obtain ⟨opn, hm, rfl⟩ := asReload_shape hr
  refine ⟨(s.setReg d (s.lvm k)).nextPc,
    by rw [lsemStepFlag_one_src, lsemStep_asReload hr s], ?_, rfl, rfl, rfl⟩
  funext r
  simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
  by_cases hrd : r = d
  · subst hrd; simp [hdk]
  · simp [hrd]

/-! ## 2. The scan -/

/-- **The scan is a forward simulation with the flags equal.** From an environment that
    agrees with the start state, a body that runs to completion under `lsemStraightFlag` is
    matched by the scanned body from any state with the same registers, word memory and
    flags, and the two results have the same registers, word memory and flags. -/
theorem elimAux_simF (tag : LinstrR → MemTag) : ∀ (body : List Linstr) (h : Held)
    (s t : Lstate 64), HeldSound h s → SameF s t →
    ∀ s₂, lsemStraightFlag (body.map fun i => (i.li_i, tag i.li_i)) s = some s₂ →
      ∃ t₂, lsemStraightFlag ((elimAux h body).map fun i => (i.li_i, tag i.li_i)) t = some t₂
        ∧ SameF s₂ t₂ := by
  intro body
  induction body with
  | nil =>
    intro h s t _ hst s₂ hrun
    simp only [List.map_nil, lsemStraightFlag_nil, Option.some.injEq] at hrun
    subst hrun
    exact ⟨t, rfl, hst⟩
  | cons i is ih =>
    intro h s t hs hst s₂ hrun
    simp only [List.map_cons, lsemStraightFlag_cons] at hrun
    rw [elimAux_cons]
    cases hstep : lsemStepFlag (i.li_i, tag i.li_i) s with
    | none => rw [hstep] at hrun; exact absurd hrun (by simp)
    | some s₁ =>
      rw [hstep, Option.bind_some] at hrun
      by_cases hk : (stepReload h i.li_i).1 = true
      · rw [ite_eq_left hk]
        obtain ⟨t₁, ht₁, hst₁⟩ := lsemStepFlag_sameF (i.li_i, tag i.li_i) hst hstep
        simp only [List.map_cons, lsemStraightFlag_cons, ht₁, Option.bind_some]
        exact ih _ s₁ t₁ (heldSound_stepF _ hs hstep hk) hst₁ s₂ hrun
      · have hdrop : (stepReload h i.li_i).1 = false := by simpa using hk
        rw [ite_eq_right hk, stepReload_env_of_drop hdrop]
        obtain ⟨b, hb, hbs⟩ := lsemStepFlag_drop (tag i.li_i) hs hdrop
        rw [hb] at hstep
        obtain rfl := Option.some.inj hstep
        exact ih h b t (heldSound_of_lvm hs hbs.1) (hbs.trans hst) s₂ hrun

/-! ## 3. The pass -/

/-- **Redundant-reload elimination preserves the run with flags.** On every body and every
    start state from which the input runs to completion under `lsemStraightFlag`, the
    output runs to completion and reaches a state with the same register map, the same
    word memory and the same flags, for any tagging of the input and of the output. The
    program counter is lower by the number of deleted instructions. -/
theorem elimReloads_lsemStraightFlag (tag tag' : LinstrR → MemTag) (body : List Linstr)
    (s s₂ : Lstate 64)
    (hrun : lsemStraightFlag (body.map fun i => (i.li_i, tag i.li_i)) s = some s₂) :
    ∃ t₂, lsemStraightFlag ((elimReloads body).map fun i => (i.li_i, tag' i.li_i)) s
        = some t₂
      ∧ t₂.lvm = s₂.lvm ∧ t₂.lmem = s₂.lmem ∧ t₂.cf = s₂.cf ∧ t₂.of = s₂.of := by
  rw [lsemStraightFlag_tag tag tag'] at hrun
  obtain ⟨t₂, ht, hsame⟩ :=
    elimAux_simF tag' body [] s s (heldSound_nil s) (SameF.refl s) s₂ hrun
  exact ⟨t₂, ht, hsame.symm⟩

/-! ## 4. The fragment with flags and the flag machine -/

/-- No instruction of the fragment with flags is a reload. -/
theorem asReload_of_fragFB {A : String → Option Nat} {w : LinstrR} {tg : MemTag}
    (h : fragFB A (w, tg) = true) : asReload w = none := by
  cases hr : asReload w with
  | none => rfl
  | some dk =>
    obtain ⟨d, k⟩ := dk
    obtain ⟨opn, -, hw⟩ := asReload_shape hr
    exact absurd hw (fragFB_ne_mov1 h d opn k)

/-- The scan keeps every instruction of a body of the fragment with flags. -/
theorem elimAux_eq_of_fragFB {A : String → Option Nat} (tag : LinstrR → MemTag) :
    ∀ (b : List Linstr) (h : Held), (∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true) →
      elimAux h b = b := by
  intro b
  induction b with
  | nil => intro h _; rfl
  | cons i is ih =>
    intro h hfrag
    have hr := asReload_of_fragFB (hfrag i List.mem_cons_self)
    have hk : (stepReload h i.li_i).1 = true := by simp [stepReload, hr]
    rw [elimAux_cons, ite_eq_left hk, ih _ fun j hj => hfrag j (List.mem_cons_of_mem i hj)]

/-- **The pass is the identity on the fragment with flags.** The fragment has no
    single-source register move, so no instruction of the body is a reload. -/
theorem elimReloads_eq_of_fragFB {A : String → Option Nat} (tag : LinstrR → MemTag)
    (b : List Linstr) (hfrag : ∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true) :
    elimReloads b = b :=
  elimAux_eq_of_fragFB tag b [] hfrag

/-- **Redundant-reload elimination on the flag machine.** On a body of the fragment with
    flags the output body runs under `lsemStraightMemF` as the input body does. -/
theorem elimReloads_lsemStraightMemF_F {A : String → Option Nat} (tag : LinstrR → MemTag)
    (b : List Linstr) (hfrag : ∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true)
    (s : LstateM) :
    lsemStraightMemF ((elimReloads b).map fun i => (i.li_i, tag i.li_i)) s
      = lsemStraightMemF (b.map fun i => (i.li_i, tag i.li_i)) s := by
  rw [elimReloads_eq_of_fragFB tag b hfrag]

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.StoreToLoad
