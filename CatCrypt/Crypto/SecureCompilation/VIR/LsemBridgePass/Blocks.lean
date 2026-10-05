/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.StoreToLoad
public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Scheduler
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# The basic-block optimiser over the uniform-width run with flags

`LprogOptPipeline.optimizeBasicBlocks` partitions a body into segments and applies
`optRunBody` to each straight-line segment. `optRunBody` composes five stages on a body of
modelled instructions, in this order:

1. `LprogStoreToLoad.elimReloads` deletes a reload whose register holds its source;
2. `LcmdReloadElim.reloadElimBody` deletes the reload of an adjacent spill store and reload;
3. `LprogScheduler.scheduleBody` swaps adjacent independent instructions;
4. `LcmdCopyPropagate.copyPropagateBody` rewrites register sources and deletes dead moves;
5. `Optimizer.LoadCSE.loadCSE` redirects the source of a reload to a register holding it.

This module proves that stages 2 and 5 preserve the run `LsemBridge.lsemStraightFlag`, and
composes the five stage lemmas: where the input body runs, the optimised body runs to a
state with the same registers, the same word memory and the same flags.

Stages 1, 2 and 5 delete or rewrite only single-destination, single-source moves. Such an
instruction is accepted by none of the recognizers of the flag layer
(`Common.lsemStepFlag_one_src`), so no stage deletes, moves or rewrites an instruction that
writes a flag, and the composed statement has no side condition on the flags. The
scheduler keeps the order of flag-touching instructions through its independence test, and
copy propagation deletes only moves.

The fragment with flags `LsemBridge.fragFB` has no single-source register move, so stages
1, 2 and 5 are the identity on a body of the fragment
(`StoreToLoad.elimReloads_eq_of_fragFB`, `reloadElimBody_eq_of_fragFB`,
`loadCSE_eq_of_fragFB`).

## Main definitions

This module defines no new notion; it states the stages of
`LprogOptPipeline.optimizeBasicBlocks` over `LsemBridge.lsemStraightFlag`.

## Main results

* `reloadElimBody_lsemStraightFlag` — spill-pair reload elimination preserves the run with
  flags.
* `loadCSE_lsemStraightFlag` — load CSE preserves the run with flags, as an equality of
  runs.
* `optRunBody_lsemStraightFlag` — the five stages composed.
* `optimizeBasicBlocks_lsemStraightFlag` — the basic-block optimiser on a body.
* `optimizeLprogBasicBlocks_lsemStraightFlag` — the optimiser on a function of a program.
* `reloadElimBody_eq_of_fragFB`, `loadCSE_eq_of_fragFB` — stages 2 and 5 on the fragment
  with flags.
* `optRunBody_lsemStraightMemF_F` — the five stages on the flag machine through
  `Scheduler.scheduleBody_lsemStraightMemF_F` and
  `CopyProp.copyPropagateBody_lsemStraightMemF_F`, for an input body and a scheduled and
  copy-propagated body in `fragFB` whose in-bounds runs succeed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Blocks

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridge
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
  (elimReloads writtenNames mem_of_find)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler (scheduleBody)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (getFundef)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate (copyPropagateBody)
open CatCrypt.Crypto.Optimizer.LoadCSE
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyProp
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Common
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.StoreToLoad
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Scheduler

/-! ## 1. Spill-pair reload elimination -/

/-- The reload of a slot that holds the register's word steps with flags to a state with
    the same registers, word memory and flags. -/
theorem lsemStepFlag_reload_sameF {slot r mn : String} (hm : isMov64 mn = true) (tg : MemTag)
    {s₁ : Lstate 64} (hslot : s₁.lvm slot = s₁.lvm r) :
    ∃ b, lsemStepFlag (.Lopn [.reg r] mn [.reg slot], tg) s₁ = some b ∧ SameF b s₁ := by
  refine ⟨(s₁.setReg r (s₁.lvm slot)).nextPc, ?_, ?_, rfl, rfl, rfl⟩
  · rw [lsemStepFlag_one_src]
    simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, applyOpn_mov64 hm]
  · rw [hslot]
    simp only [Lstate.nextPc, lvm_setReg_self]

/-- The deletion inside `consDropL` is a forward simulation with the flags equal. -/
theorem consDropL_simF (tag : LinstrR → MemTag) (i : Linstr) (k : Lcmd) (s t : Lstate 64)
    (hst : SameF s t) (s₂ : Lstate 64)
    (hrun : lsemStraightFlag ((i :: k).map fun i => (i.li_i, tag i.li_i)) s = some s₂) :
    ∃ t₂, lsemStraightFlag ((consDropL i k).map fun i => (i.li_i, tag i.li_i)) t = some t₂
      ∧ SameF s₂ t₂ := by
  cases k with
  | nil => exact lsemStraightFlag_sameF _ s t hst s₂ hrun
  | cons j rest =>
    rw [consDropL]
    split
    · rename_i h
      obtain ⟨slot, r, mn, hi, hj, hslot, hreg, hmn⟩ := eq_of_isRedundantReloadL h
      simp only [List.map_cons, lsemStraightFlag_cons, hi, hj] at hrun ⊢
      rw [lsemStepFlag_one_src, lsemStep_spill_store hmn, Option.bind_some] at hrun
      have hsl : ((s.setReg slot (s.lvm r)).nextPc).lvm slot
          = ((s.setReg slot (s.lvm r)).nextPc).lvm r := by
        simp [Lstate.nextPc, Lstate.setReg, slot_ne_reg hslot hreg]
      obtain ⟨b, hb, hbs⟩ := lsemStepFlag_reload_sameF hmn
        (tag (.Lopn [.reg r] mn [.reg slot])) hsl
      rw [lsemStraightFlag_cons, hb, Option.bind_some] at hrun
      have hstore : lsemStepFlag (.Lopn [.reg slot] mn [.reg r],
          tag (.Lopn [.reg slot] mn [.reg r])) s = some ((s.setReg slot (s.lvm r)).nextPc) := by
        rw [lsemStepFlag_one_src, lsemStep_spill_store hmn]
      obtain ⟨t₁, ht₁, h₁⟩ := lsemStepFlag_sameF _ hst hstore
      rw [ht₁, Option.bind_some]
      exact lsemStraightFlag_sameF _ b t₁ (hbs.trans h₁) s₂ hrun
    · exact lsemStraightFlag_sameF _ s t hst s₂ hrun

/-- The sweep is a forward simulation with the flags equal. -/
theorem dropReloadsLcmd_simF (tag : LinstrR → MemTag) : ∀ (b : Lcmd) (s t : Lstate 64),
    SameF s t → ∀ s₂, lsemStraightFlag (b.map fun i => (i.li_i, tag i.li_i)) s = some s₂ →
      ∃ t₂, lsemStraightFlag ((dropReloadsLcmd b).map fun i => (i.li_i, tag i.li_i)) t
          = some t₂ ∧ SameF s₂ t₂ := by
  intro b
  induction b with
  | nil => intro s t hst s₂ hrun; exact lsemStraightFlag_sameF _ s t hst s₂ hrun
  | cons i rest ih =>
    intro s t hst s₂ hrun
    rw [dropReloadsLcmd_cons]
    simp only [List.map_cons, lsemStraightFlag_cons] at hrun
    cases hstep : lsemStepFlag (i.li_i, tag i.li_i) s with
    | none => rw [hstep] at hrun; exact absurd hrun (by simp)
    | some s₁ =>
      rw [hstep, Option.bind_some] at hrun
      obtain ⟨u₂, hu, hsu⟩ := ih s₁ s₁ (SameF.refl s₁) s₂ hrun
      have hmid : lsemStraightFlag
          ((i :: dropReloadsLcmd rest).map fun i => (i.li_i, tag i.li_i)) s = some u₂ := by
        simp only [List.map_cons, lsemStraightFlag_cons, hstep, Option.bind_some]
        exact hu
      obtain ⟨t₂, ht, hut⟩ := consDropL_simF tag i (dropReloadsLcmd rest) s t hst u₂ hmid
      exact ⟨t₂, ht, hsu.trans hut⟩

/-- The guarded sweep is a forward simulation with the flags equal. -/
theorem reloadElimBody_simF (tag : LinstrR → MemTag) (b : Lcmd) (s t : Lstate 64)
    (hst : SameF s t) (s₂ : Lstate 64)
    (hrun : lsemStraightFlag (b.map fun i => (i.li_i, tag i.li_i)) s = some s₂) :
    ∃ t₂, lsemStraightFlag ((reloadElimBody b).map fun i => (i.li_i, tag i.li_i)) t = some t₂
      ∧ SameF s₂ t₂ := by
  unfold reloadElimBody
  split
  · exact dropReloadsLcmd_simF tag b s t hst s₂ hrun
  · exact lsemStraightFlag_sameF _ s t hst s₂ hrun

/-- **Spill-pair reload elimination preserves the run with flags.** On every body and every
    start state from which the input runs to completion under `lsemStraightFlag`, the
    output runs to completion and reaches a state with the same register map, the same
    word memory and the same flags, for any tagging of the input and of the output. -/
theorem reloadElimBody_lsemStraightFlag (tag tag' : LinstrR → MemTag) (b : Lcmd)
    (s s₂ : Lstate 64)
    (hrun : lsemStraightFlag (b.map fun i => (i.li_i, tag i.li_i)) s = some s₂) :
    ∃ t₂, lsemStraightFlag ((reloadElimBody b).map fun i => (i.li_i, tag' i.li_i)) s
        = some t₂
      ∧ t₂.lvm = s₂.lvm ∧ t₂.lmem = s₂.lmem ∧ t₂.cf = s₂.cf ∧ t₂.of = s₂.of := by
  rw [lsemStraightFlag_tag tag tag'] at hrun
  obtain ⟨t₂, ht, hsame⟩ := reloadElimBody_simF tag' b s s (SameF.refl s) s₂ hrun
  exact ⟨t₂, ht, hsame.symm⟩

/-! ## 2. Load CSE -/

/-- The rewritten instruction steps with flags as the input instruction does. -/
theorem stepLoad_lsemStepFlag (h : LoadEnv) (i : Linstr) (tg : MemTag) (s : Lstate 64)
    (hs : EnvSound h s) :
    lsemStepFlag ((stepLoad h i).1.li_i, tg) s = lsemStepFlag (i.li_i, tg) s := by
  rcases stepLoad_cases h i with hid | ⟨d, sn, r, mn, ha, hf, hrd, heq⟩
  · rw [hid]
  · obtain ⟨hi, _⟩ := asWideReload_eq ha
    have hl := stepLoad_lsemStep h i s hs
    rw [heq, hi] at hl
    rw [heq, hi]
    simp only [lsemStepFlag_one_src]
    exact hl

/-- A step with flags preserves the environment invariant. -/
theorem stepLoad_envSoundF (h : LoadEnv) (i : Linstr) (tg : MemTag) (s s' : Lstate 64)
    (hs : EnvSound h s) (hstep : lsemStepFlag (i.li_i, tg) s = some s') :
    EnvSound (stepLoad h i).2 s' := by
  cases hst : lsemStep i.li_i s with
  | some b =>
    rw [lsemStepFlag_of_lsemStep (i := (i.li_i, tg)) hst, Option.some.injEq] at hstep
    subst hstep
    intro k r hk
    rw [withALUFlagsL_lvm]
    exact stepLoad_envSound h i s b hs hst k r hk
  | none =>
    have hr : asWideReload i.li_i = none := by
      cases hr : asWideReload i.li_i with
      | none => rfl
      | some dsm =>
        obtain ⟨d, sn, mn⟩ := dsm
        obtain ⟨hi, hm⟩ := asWideReload_eq hr
        rw [hi] at hst
        simp only [lsemStep, List.map_cons, List.map_nil, evalOperand,
          applyOpn_of_isMov64Mnem hm, reduceCtorEq] at hst
    intro k r hk
    rw [stepLoad_env_of_not_wideReload h i hr] at hk
    obtain ⟨hk1, hkw⟩ := mem_foldl_killSlot _ _ _ hk
    obtain ⟨hk0, hrw⟩ := mem_foldl_killReg _ _ _ hk1
    rw [lsemStepFlag_lvm_of_not_written hstep hrw, lsemStepFlag_lvm_of_not_written hstep hkw]
    exact hs k r hk0

/-- The scan preserves the run with flags from every state its environment agrees with. -/
theorem loadCSEAux_lsemStraightFlag (tag : LinstrR → MemTag) (h : LoadEnv)
    (body : List Linstr) (s : Lstate 64) (hs : EnvSound h s) :
    lsemStraightFlag ((loadCSEAux h body).map fun i => (i.li_i, tag i.li_i)) s
      = lsemStraightFlag (body.map fun i => (i.li_i, tag i.li_i)) s := by
  induction body generalizing h s with
  | nil => rfl
  | cons i is ih =>
    rw [loadCSEAux_cons]
    simp only [List.map_cons, lsemStraightFlag_cons]
    rw [lsemStepFlag_tag (stepLoad h i).1.li_i (tag (stepLoad h i).1.li_i) (tag i.li_i),
      stepLoad_lsemStepFlag h i (tag i.li_i) s hs]
    cases hst : lsemStepFlag (i.li_i, tag i.li_i) s with
    | none => rfl
    | some s' => exact ih (stepLoad h i).2 s' (stepLoad_envSoundF h i _ s s' hs hst)

/-- **Load CSE preserves the run with flags.** On every body and every start state the
    rewritten body's `lsemStraightFlag` result is the input's: the same register map, word
    memory, flags and program counter. -/
theorem loadCSE_lsemStraightFlag (tag : LinstrR → MemTag) (body : List Linstr)
    (s : Lstate 64) :
    lsemStraightFlag ((loadCSE body).map fun i => (i.li_i, tag i.li_i)) s
      = lsemStraightFlag (body.map fun i => (i.li_i, tag i.li_i)) s := by
  rw [loadCSE_eq]
  exact loadCSEAux_lsemStraightFlag tag [] body s (envSound_nil s)

/-! ## 3. The five stages composed -/

/-- **The stages of one run, composed, are a forward simulation with the flags equal.** -/
theorem optRunBody_simF (tag : LinstrR → MemTag) (body : List Linstr) (s t : Lstate 64)
    (hst : SameF s t) (s₂ : Lstate 64)
    (hrun : lsemStraightFlag (body.map fun i => (i.li_i, tag i.li_i)) s = some s₂) :
    ∃ t₂, lsemStraightFlag ((optRunBody body).map fun i => (i.li_i, tag i.li_i)) t = some t₂
      ∧ SameF s₂ t₂ := by
  unfold optRunBody
  split
  · obtain ⟨a₁, h₁, e₁⟩ := elimAux_simF tag body [] s s
      (LprogStoreToLoad.heldSound_nil s) (SameF.refl s) s₂ hrun
    obtain ⟨a₂, h₂, e₂⟩ := reloadElimBody_simF tag (elimReloads body) s s (SameF.refl s) a₁ h₁
    rw [← scheduleBody_lsemStraightFlag tag] at h₂
    obtain ⟨a₃, h₃, e₃⟩ := copyPropagateBody_lsemStraightFlag tag tag _ s a₂ h₂
    rw [← loadCSE_lsemStraightFlag tag] at h₃
    obtain ⟨t₂, ht, e₄⟩ := lsemStraightFlag_sameF _ s t hst a₃ h₃
    exact ⟨t₂, ht, (e₁.trans e₂).trans ((SameF.symm e₃).trans e₄)⟩
  · exact lsemStraightFlag_sameF _ s t hst s₂ hrun

/-- **The five stages preserve the run with flags.** On every body and every start state
    from which the input runs to completion under `lsemStraightFlag`, `optRunBody` runs to
    completion and reaches a state with the same register map, the same word memory and the
    same flags, for any tagging of the input and of the output. -/
theorem optRunBody_lsemStraightFlag (tag tag' : LinstrR → MemTag) (body : List Linstr)
    (s s₂ : Lstate 64)
    (hrun : lsemStraightFlag (body.map fun i => (i.li_i, tag i.li_i)) s = some s₂) :
    ∃ t₂, lsemStraightFlag ((optRunBody body).map fun i => (i.li_i, tag' i.li_i)) s
        = some t₂
      ∧ t₂.lvm = s₂.lvm ∧ t₂.lmem = s₂.lmem ∧ t₂.cf = s₂.cf ∧ t₂.of = s₂.of := by
  rw [lsemStraightFlag_tag tag tag'] at hrun
  obtain ⟨t₂, ht, hsame⟩ := optRunBody_simF tag' body s s (SameF.refl s) s₂ hrun
  exact ⟨t₂, ht, hsame.symm⟩

/-! ## 4. The basic-block optimiser -/

/-- The optimiser on one segment is a forward simulation with the flags equal. -/
theorem optSeg_simF (tag : LinstrR → MemTag) (seg : List Linstr) (s t : Lstate 64)
    (hst : SameF s t) (s₂ : Lstate 64)
    (hrun : lsemStraightFlag (seg.map fun i => (i.li_i, tag i.li_i)) s = some s₂) :
    ∃ t₂, lsemStraightFlag ((optSeg seg).map fun i => (i.li_i, tag i.li_i)) t = some t₂
      ∧ SameF s₂ t₂ := by
  unfold optSeg
  split
  · exact optRunBody_simF tag seg s t hst s₂ hrun
  · exact lsemStraightFlag_sameF _ s t hst s₂ hrun

/-- The optimiser on a list of segments is a forward simulation with the flags equal. -/
theorem optSegs_simF (tag : LinstrR → MemTag) : ∀ (segs : List (List Linstr))
    (s t : Lstate 64), SameF s t →
    ∀ s₂, lsemStraightFlag (segs.flatten.map fun i => (i.li_i, tag i.li_i)) s = some s₂ →
      ∃ t₂, lsemStraightFlag (((segs.map optSeg).flatten).map fun i => (i.li_i, tag i.li_i)) t
          = some t₂ ∧ SameF s₂ t₂ := by
  intro segs
  induction segs with
  | nil => intro s t hst s₂ hrun; exact lsemStraightFlag_sameF _ s t hst s₂ hrun
  | cons seg rest ih =>
    intro s t hst s₂ hrun
    simp only [List.flatten_cons, List.map_cons, List.map_append,
      lsemStraightFlag_append] at hrun ⊢
    cases h₁ : lsemStraightFlag (seg.map fun i => (i.li_i, tag i.li_i)) s with
    | none => rw [h₁] at hrun; exact absurd hrun (by simp)
    | some s₁ =>
      rw [h₁, Option.bind_some] at hrun
      obtain ⟨t₁, ht₁, e₁⟩ := optSeg_simF tag seg s t hst s₁ h₁
      rw [ht₁, Option.bind_some]
      exact ih s₁ t₁ e₁ s₂ hrun

/-- **The basic-block optimiser preserves the run with flags.** On every body and every
    start state from which the input runs to completion under `lsemStraightFlag`, the
    optimised body runs to completion and reaches a state with the same register map, the
    same word memory and the same flags, for any tagging of the input and of the output. -/
theorem optimizeBasicBlocks_lsemStraightFlag (tag tag' : LinstrR → MemTag)
    (body : List Linstr) (s s₂ : Lstate 64)
    (hrun : lsemStraightFlag (body.map fun i => (i.li_i, tag i.li_i)) s = some s₂) :
    ∃ t₂, lsemStraightFlag ((optimizeBasicBlocks body).map fun i => (i.li_i, tag' i.li_i)) s
        = some t₂
      ∧ t₂.lvm = s₂.lvm ∧ t₂.lmem = s₂.lmem ∧ t₂.cf = s₂.cf ∧ t₂.of = s₂.of := by
  rw [lsemStraightFlag_tag tag tag', ← splitStraightRuns_flatten body] at hrun
  obtain ⟨t₂, ht, hsame⟩ :=
    optSegs_simF tag' (splitStraightRuns body) s s (SameF.refl s) s₂ hrun
  rw [← optimizeBasicBlocks_eq_optSeg] at ht
  exact ⟨t₂, ht, hsame.symm⟩

/-- **The basic-block optimiser on a program preserves the run with flags of every function
    body.** A function `fd` of `P` is a function of the optimised program whose body is
    `optimizeBasicBlocks fd.lfd_body`, and that body runs under `lsemStraightFlag` to a
    state with the same register map, word memory and flags as the body of `fd`. -/
theorem optimizeLprogBasicBlocks_lsemStraightFlag (tag tag' : LinstrR → MemTag) (P : Lprog)
    (fn : String) (fd : Lfundef) (hfd : getFundef P fn = some fd) (s s₂ : Lstate 64)
    (hrun : lsemStraightFlag (fd.lfd_body.map fun i => (i.li_i, tag i.li_i)) s = some s₂) :
    ∃ fd' t₂, getFundef (optimizeLprogBasicBlocks P) fn = some fd'
      ∧ fd'.lfd_body = optimizeBasicBlocks fd.lfd_body
      ∧ lsemStraightFlag (fd'.lfd_body.map fun i => (i.li_i, tag' i.li_i)) s = some t₂
      ∧ t₂.lvm = s₂.lvm ∧ t₂.lmem = s₂.lmem ∧ t₂.cf = s₂.cf ∧ t₂.of = s₂.of := by
  obtain ⟨t₂, ht, hrest⟩ := optimizeBasicBlocks_lsemStraightFlag tag tag' fd.lfd_body s s₂ hrun
  refine ⟨{ fd with lfd_body := optimizeBasicBlocks fd.lfd_body }, t₂, ?_, rfl, ht, hrest⟩
  rw [optimizeLprogBasicBlocks, getFundef_mapBodies, hfd]
  rfl

/-! ## 5. Stages 2 and 5 on the fragment with flags -/

/-- No instruction of the fragment with flags is a spill reload. -/
theorem spillLoadKey_of_fragFB {A : String → Option Nat} (tag : LinstrR → MemTag)
    {j : Linstr} (h : fragFB A (j.li_i, tag j.li_i) = true) : spillLoadKey j = none := by
  cases hk : spillLoadKey j with
  | none => rfl
  | some q =>
    obtain ⟨slot, r, mn⟩ := q
    obtain ⟨hj, -, -, -⟩ := spillLoadKey_eq hk
    exact absurd hj (fragFB_ne_mov1 h r mn slot)

/-- The sweep keeps every instruction of a body of the fragment with flags. -/
theorem dropReloadsLcmd_eq_of_fragFB {A : String → Option Nat} (tag : LinstrR → MemTag)
    (b : Lcmd) (hfrag : ∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true) :
    dropReloadsLcmd b = b := by
  induction b with
  | nil => rfl
  | cons i rest ih =>
    rw [dropReloadsLcmd_cons, ih fun j hj => hfrag j (List.mem_cons_of_mem i hj)]
    cases rest with
    | nil => rfl
    | cons j rest' =>
      have hj := spillLoadKey_of_fragFB tag
        (hfrag j (List.mem_cons_of_mem i List.mem_cons_self))
      have hno : isRedundantReloadL i j = false := by
        unfold isRedundantReloadL
        rw [hj]
        split <;> first | rfl | simp_all
      rw [consDropL, hno]
      rfl

/-- **Spill-pair reload elimination is the identity on the fragment with flags.** -/
theorem reloadElimBody_eq_of_fragFB {A : String → Option Nat} (tag : LinstrR → MemTag)
    (b : Lcmd) (hfrag : ∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true) :
    reloadElimBody b = b := by
  unfold reloadElimBody
  split
  · exact dropReloadsLcmd_eq_of_fragFB tag b hfrag
  · rfl

/-- The scan rewrites no instruction of a body of the fragment with flags. -/
theorem loadCSEAux_eq_of_fragFB {A : String → Option Nat} (tag : LinstrR → MemTag) :
    ∀ (b : List Linstr) (h : LoadEnv), (∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true) →
      loadCSEAux h b = b := by
  intro b
  induction b with
  | nil => intro h _; rfl
  | cons i rest ih =>
    intro h hfrag
    have hid : (stepLoad h i).1 = i := by
      refine stepLoad_unchanged_of_no_cross h i ?_
      intro d s r mn ha _
      obtain ⟨hi, -⟩ := asWideReload_eq ha
      exact absurd hi (fragFB_ne_mov1 (hfrag i List.mem_cons_self) d mn s)
    rw [loadCSEAux_cons, hid, ih _ fun j hj => hfrag j (List.mem_cons_of_mem i hj)]

/-- **Load CSE is the identity on the fragment with flags.** -/
theorem loadCSE_eq_of_fragFB {A : String → Option Nat} (tag : LinstrR → MemTag)
    (b : List Linstr) (hfrag : ∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true) :
    loadCSE b = b := by
  rw [loadCSE_eq]
  exact loadCSEAux_eq_of_fragFB tag b [] hfrag

/-! ## 6. The five stages on the flag machine -/

/-- On a body of the fragment with flags whose scheduled and copy-propagated body is in the
    fragment, `optRunBody` is scheduling followed by copy propagation, or the identity. -/
theorem optRunBody_eq_of_fragFB {A : String → Option Nat} (tag : LinstrR → MemTag)
    (b : List Linstr) (hfrag : ∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true)
    (hfrag' : ∀ i ∈ copyPropagateBody (scheduleBody b), fragFB A (i.li_i, tag i.li_i) = true) :
    optRunBody b = copyPropagateBody (scheduleBody b) ∨ optRunBody b = b := by
  unfold optRunBody
  split
  · left
    rw [elimReloads_eq_of_fragFB tag b hfrag, reloadElimBody_eq_of_fragFB tag b hfrag,
      loadCSE_eq_of_fragFB tag _ hfrag']
  · right; rfl

/-- **The five stages on the flag machine through the bridge with flags.** Let the input
    body and its scheduled and copy-propagated body be bodies of the fragment with flags
    whose in-bounds runs from `l` succeed. From a state related to `l` with its flags,
    `optRunBody b` and `b` run under `lsemStraightMemF` to states with the same registers,
    arrays, word memory and flags. -/
theorem optRunBody_lsemStraightMemF_F {A : String → Option Nat} (tag : LinstrR → MemTag)
    (b : List Linstr) (hfrag : ∀ i ∈ b, fragFB A (i.li_i, tag i.li_i) = true)
    (hfrag' : ∀ i ∈ copyPropagateBody (scheduleBody b), fragFB A (i.li_i, tag i.li_i) = true)
    {s : LstateM} {l : Lstate 64} (hr : LsemRelF A s l)
    (hib : (runIBF (b.map fun i => (i.li_i, tag i.li_i)) l).isSome)
    (hib' : (runIBF ((copyPropagateBody (scheduleBody b)).map
      fun i => (i.li_i, tag i.li_i)) l).isSome) :
    ∃ u u',
      lsemStraightMemF ((optRunBody b).map fun i => (i.li_i, tag i.li_i)) s = some u ∧
      lsemStraightMemF (b.map fun i => (i.li_i, tag i.li_i)) s = some u' ∧
      u.reg.lvm = u'.reg.lvm ∧ u.larr = u'.larr ∧ u.lmem = u'.lmem ∧
      u.cf = u'.cf ∧ u.of = u'.of := by
  have hsfrag : ∀ i ∈ scheduleBody b, fragFB A (i.li_i, tag i.li_i) = true :=
    fun i hi => hfrag i ((LprogScheduler.scheduleBody_perm b).mem_iff.1 hi)
  obtain ⟨v, u', t, hv, hu', -, -, hreg, hA, hM, hc, ho, -, -⟩ :=
    scheduleBody_lsemStraightMemF_F tag b hfrag hr hib
  rcases optRunBody_eq_of_fragFB tag b hfrag hfrag' with e | e
  · obtain ⟨u, v', hu, hv', h1, h2, h3, h4, h5⟩ :=
      copyPropagateBody_lsemStraightMemF_F tag (scheduleBody b) hsfrag hfrag' hr
        (by rw [runIBF_scheduleBody]; exact hib) hib'
    rw [hv] at hv'
    obtain rfl := Option.some.inj hv'
    exact ⟨u, u', by rw [e]; exact hu, hu', h1.trans (by rw [hreg]), h2.trans hA,
      h3.trans hM, h4.trans hc, h5.trans ho⟩
  · exact ⟨u', u', by rw [e]; exact hu', hu', rfl, rfl, rfl, rfl, rfl⟩

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.Blocks
