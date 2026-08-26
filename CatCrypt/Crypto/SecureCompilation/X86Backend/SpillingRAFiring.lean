/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
import CatCrypt.Crypto.Optimizer.SpillFootprintGeneral

/-!
# The graph-coloring register allocator as a firing footprint-validated pass

`X86OptPipelineComposed.graphColorRAValidated` wraps the graph-coloring allocator
behind the conservative no-op gate (`dead := fun _ => []`), so it fires only on
blocks it leaves unchanged. This module adds the *firing* form, gated by the
footprint certificate rather than the no-op gate.

`graphColorRAValidatedFiring pinned frameBase spillBase` sets
`f b := spillReloadBlock (graphColorAlloc pinned frameBase b) spillBase b`, a
decidable per-block certificate `chk b` that conjoins the three hypotheses of
`SpillFootprintGeneral.spillReloadBlock_footprintSound_general`
(`SpillWellFormed`, `readsAfterDef`, `blockAvoids`), and a nonempty dead set
`dead b := deadCells spillBase (graphColorAlloc pinned frameBase b)`. Its
`sem_sound` is discharged from that general theorem; its `ct_sound` from
`spillReloadBlock_allDirect`.

The firing pipeline `firingValidatedPipeline` swaps the no-op-gated allocator in
`defaultValidatedPipeline` for this firing pass. Its capstone
`firingValidatedPipeline_sound_fp` concludes `agreeExcept (composedDead …) …`
through `composeValidated_sound_fp`. The default pipeline's full-equality
capstones are unchanged: this is an additive footprint-form demonstrator, not a
replacement of the default pipeline.

`firingExampleBlock` is a straight-line SSA block whose register pressure exceeds
the allocator pool, so `graphColorAlloc` spills: `graphColorRAValidatedFiring`'s
certificate fires and its dead set is nonempty, whereas the no-op-gated
`graphColorRAValidated` rejects (its dead set stays empty).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SpillingRAFiring

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
  (JInstr JState runBlock evalInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
  (allDirect allDirect_mem_isDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (IsDirect)
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc
  (Slot spillReloadBlock spillSlotOf reloadsOf storesOf spillRewriteInstr_eq)
open CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc (graphColorAlloc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
  (ValidatedPass composeValidated composedDead agreeExcept composeValidated_sound_fp
    graphColorRAValidated storeToLoadForwardValidated dropIdMovsValidated fuseMulxValidated
    mem2regValidated)

/-! ## 1. The spill/reload materialization preserves the constant-time class -/

/-- **`spillReloadBlock` preserves `allDirect`.** The inserted reload loads and spill
    stores are direct-addressing (`loadMem`/`storeMem` against the spill base at a
    constant offset), so materializing the spill of an `allDirect` block keeps every
    instruction direct. -/
theorem spillReloadBlock_allDirect (decisions : List (String × Slot)) (spillBase : String)
    (block : List (JInstr 64)) (h : allDirect block = true) :
    allDirect (spillReloadBlock decisions spillBase block) = true := by
  rw [allDirect, List.all_eq_true]
  intro j hj
  rw [decide_eq_true_eq]
  rw [spillReloadBlock, List.mem_flatMap] at hj
  obtain ⟨i, hi, hji⟩ := hj
  rw [spillRewriteInstr_eq, List.mem_append] at hji
  rcases hji with hjr | hjm
  · rw [reloadsOf, List.mem_filterMap] at hjr
    obtain ⟨n, _, hmap⟩ := hjr
    cases hs : spillSlotOf decisions n with
    | none => rw [hs] at hmap; simp at hmap
    | some off =>
      rw [hs] at hmap
      simp only [Option.map_some, Option.some.injEq] at hmap
      subst hmap; simp [IsDirect]
  · rw [List.mem_cons] at hjm
    rcases hjm with rfl | hjs
    · exact allDirect_mem_isDirect block h _ hi
    · rw [storesOf, List.mem_filterMap] at hjs
      obtain ⟨n, _, hmap⟩ := hjs
      cases hs : spillSlotOf decisions n with
      | none => rw [hs] at hmap; simp at hmap
      | some off =>
        rw [hs] at hmap
        simp only [Option.map_some, Option.some.injEq] at hmap
        subst hmap; simp [IsDirect]

/-! ## 2. The firing footprint-validated pass -/

/-- The decidable firing certificate: the three hypotheses of
    `SpillFootprintGeneral.spillReloadBlock_footprintSound_general` on the
    allocator's decisions — the block is `SpillWellFormed`, its spilled reads are all
    predefined (`readsAfterDef`), and no instruction addresses a dead spill cell
    (`blockAvoids`). -/
def firingCert (pinned : GpAlloc) (frameBase : Int) (spillBase : String)
    (b : List (JInstr 64)) : Bool :=
  CatCrypt.Crypto.Optimizer.SpillReloadBlockSound.SpillWellFormed
      (graphColorAlloc pinned frameBase b) spillBase b
    && CatCrypt.Crypto.Optimizer.SpillFootprintGeneral.readsAfterDef
      (graphColorAlloc pinned frameBase b) b
    && CatCrypt.Crypto.Optimizer.FootprintValidated.blockAvoids
      (CatCrypt.Crypto.Optimizer.FootprintValidated.deadCells spillBase
        (graphColorAlloc pinned frameBase b)) b

/-- **The graph-coloring register allocator as a firing footprint-validated pass.**
    The rewrite materializes the allocator's spill decisions
    (`spillReloadBlock (graphColorAlloc …) spillBase`); the certificate `firingCert`
    decides the footprint-soundness hypotheses; the dead set is the spill frame cells
    the materialization disturbs. Semantic soundness is the footprint agreement of
    `spillReloadBlock_footprintSound_general`; constant-time preservation is
    `spillReloadBlock_allDirect`. -/
def graphColorRAValidatedFiring (pinned : GpAlloc) (frameBase : Int)
    (spillBase : String) : ValidatedPass where
  f := fun b => spillReloadBlock (graphColorAlloc pinned frameBase b) spillBase b
  chk := firingCert pinned frameBase spillBase
  dead := fun b =>
    CatCrypt.Crypto.Optimizer.FootprintValidated.deadCells spillBase
      (graphColorAlloc pinned frameBase b)
  sem_sound := fun b hc s => by
    unfold firingCert at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    obtain ⟨⟨hwf, hrd⟩, havoid⟩ := hc
    exact CatCrypt.Crypto.Optimizer.SpillFootprintGeneral.spillReloadBlock_footprintSound_general
      (graphColorAlloc pinned frameBase b) spillBase b hwf hrd havoid s
  ct_sound := fun b _ hd =>
    spillReloadBlock_allDirect (graphColorAlloc pinned frameBase b) spillBase b hd

/-! ## 3. The firing pipeline and its footprint capstone -/

/-- **The firing validated pipeline.** The content passes of
    `defaultValidatedPipeline` (store-to-load forwarding, the identity-mov drop,
    MUL→MULX fusion, mem2reg) followed by the firing graph-coloring allocator in
    place of the no-op-gated one.
    Every pass is gated by its decidable certificate, so `composeValidated` over this
    list agrees with the input modulo the accumulated dead set on every state. -/
def firingValidatedPipeline (prot : List (String × Int)) (pinned : GpAlloc)
    (frameBase : Int) (spillBase : String) : List ValidatedPass :=
  [ storeToLoadForwardValidated,
    dropIdMovsValidated,
    fuseMulxValidated,
    mem2regValidated prot,
    graphColorRAValidatedFiring pinned frameBase spillBase ]

/-- **Footprint-form capstone.** The firing pipeline lands in a `runBlock` final state
    that agrees with the input's modulo the accumulated dead set
    `composedDead (firingValidatedPipeline …) b`, on every state — no side hypothesis.
    An instance of `composeValidated_sound_fp`. The accumulated dead set is nonempty
    when the firing allocator's certificate fires, so this is a footprint agreement,
    not full-state equality. -/
theorem firingValidatedPipeline_sound_fp (prot : List (String × Int)) (pinned : GpAlloc)
    (frameBase : Int) (spillBase : String) (b : List (JInstr 64)) (s : JState 64) :
    agreeExcept (composedDead (firingValidatedPipeline prot pinned frameBase spillBase) b)
      (runBlock s (composeValidated (firingValidatedPipeline prot pinned frameBase spillBase) b))
      (runBlock s b) :=
  composeValidated_sound_fp (firingValidatedPipeline prot pinned frameBase spillBase) b s

/-! ## 4. A concrete block on which the firing pass fires beyond identity -/

/-- A straight-line SSA block: sixteen values loaded from the input frame `%rdi`,
    each stored to the output frame `%rsi`. Every value is defined once and used
    once, all sixteen are simultaneously live between the loads and the stores, and
    no instruction addresses the spill base `%rbp`. The peak pressure (sixteen)
    exceeds the twelve-register allocator pool, so `graphColorAlloc` spills. -/
def firingExampleBlock : List (JInstr 64) :=
  (List.range 16).map (fun i : Nat => JInstr.loadMem s!"v{i}" "%rdi" (8 * (i : Int)))
    ++ (List.range 16).map (fun i : Nat => JInstr.storeMem "%rsi" (8 * (i : Int)) (.reg s!"v{i}"))

/-- **The firing allocator's certificate fires on `firingExampleBlock`.** -/
theorem firing_chk_true :
    (graphColorRAValidatedFiring [] 0 "%rbp").chk firingExampleBlock = true := by
  native_decide

/-- **The firing allocator's dead set is nonempty on `firingExampleBlock`** — the
    allocator spills, so the materialization disturbs at least one frame cell. -/
theorem firing_dead_nonempty :
    (graphColorRAValidatedFiring [] 0 "%rbp").dead firingExampleBlock ≠ [] := by
  native_decide

/-- **The no-op-gated allocator rejects `firingExampleBlock`.** Its certificate fires
    only where the spill rewrite is the identity, which here it is not. -/
theorem conservative_chk_false :
    (graphColorRAValidated [] 0 "%rbp").chk firingExampleBlock = false := by
  native_decide

/-- **The no-op-gated allocator's dead set is empty** on every block, including the
    firing example — the contrast with `firing_dead_nonempty`. -/
theorem conservative_dead_nil :
    (graphColorRAValidated [] 0 "%rbp").dead firingExampleBlock = [] := rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.SpillingRAFiring
