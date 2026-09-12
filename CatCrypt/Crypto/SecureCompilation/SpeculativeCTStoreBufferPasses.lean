/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SpeculativeCTStoreBuffer
public import CatCrypt.Crypto.SecureCompilation.SpeculativeCTMask
public import CatCrypt.Crypto.SecureCompilation.BladeSelectiveProtect
public import CatCrypt.Crypto.SecureCompilation.TransientTyping

/-!
# The speculative-protection passes against the store-buffer observer

`SpeculativeCTFence.insertFences`, `SpeculativeCTMask.insertMasks` and
`BladeSelectiveProtect.insertSelective` place their barriers as
`LowCT.RAssert` markers carrying a distinguished label, and their observers
(`specObsF`, `specObsM`) read that label. `SpeculativeCTStoreBuffer.specRun`
does not: it maps every `RAssert` to `(σ, [])`. This module states the
consequence and gives the restatements that survive.

## Contents

* Each of the three passes is an identity for `specRun`
  (`specRun_insertFences`, `specRun_insertMasks`, `specRun_insertSelective`),
  hence for `SpeculativelyConstantTimeSB` and for the committed trace.
* Each pass therefore restates in the drained regimes: from
  `ArchConstantTimeSB` on the source, the pass output is speculatively
  constant-time at window `0` for every predictor, and under `neverSpeculate`
  for every window.
* At an open window each pass restates from the source's `cmdCT` acceptance
  together with `SpeculativeCTStoreBuffer.SelectAgrees`, under a
  `PublicDrivenSB` predictor.
* Each pass fails to restate from `cmdCT` alone against a bypassing predictor:
  on `SpeculativeCTStoreBuffer.StlGadget.stlGadget`, whose `cmdCT` acceptance and
  path coverage hold and which fails `SelectAgrees`, the pass output separates
  the two `PublicEquiv` states under `alwaysBypass` at window `2`.
* `TransientTyping.TransTyped` accepts `stlGadget` and `archLeakGadget`, so the
  transient typing discipline gives neither `SpeculativelyConstantTimeSB` nor
  `ArchConstantTimeSB`.

## Scope

The drained-regime restatements take `ArchConstantTimeSB` as a hypothesis; they
say nothing about `cmdCT`, which by `SpeculativeCTStoreBuffer.cmdCT_not_imp_ArchCT`
does not imply it. Carrying an unconstrained-predictor guarantee over to the
store-buffer observer requires a store-buffer semantics in which a barrier
flushes the buffer and closes the window, and a transient function for the
mispredicted arm; `specRun` has neither.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SpeculativeCTStoreBufferPasses

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.SpeculativeCT
open CatCrypt.Crypto.SecureCompilation.SpeculativeCTStoreBuffer
open CatCrypt.Crypto.SecureCompilation.SpeculativeCTStoreBuffer.StlGadget

/-! ## 1. Barrier markers under the store-buffer run

`specRun` maps `RAssert` to the identity on the speculative state with an empty
trace, so a marker prefixed to a command contributes nothing. -/

/-- A leading assertion marker leaves the store-buffer run of the command it
    prefixes unchanged. -/
@[simp] theorem specRun_RSeq_RAssert (leafSpec : LeafSpec) (O : SpecOracle)
    (σ : SpecState) (s : String) (c : LowCT) :
    specRun leafSpec O σ (.RSeq (.RAssert s) c) = specRun leafSpec O σ c := by
  simp [specRun]

@[simp] theorem specRun_fenced (leafSpec : LeafSpec) (O : SpecOracle)
    (σ : SpecState) (c : LowCT) :
    specRun leafSpec O σ (fenced c) = specRun leafSpec O σ c :=
  specRun_RSeq_RAssert leafSpec O σ fenceLabel c

@[simp] theorem specRun_fenceGuard (leafSpec : LeafSpec) (O : SpecOracle)
    (σ : SpecState) (c : LowCT) :
    specRun leafSpec O σ (fenceGuard c) = specRun leafSpec O σ c :=
  specRun_RSeq_RAssert leafSpec O σ guardLabel c

@[simp] theorem specRun_masked (leafSpec : LeafSpec) (O : SpecOracle)
    (σ : SpecState) (c : LowCT) :
    specRun leafSpec O σ (masked c) = specRun leafSpec O σ c :=
  specRun_RSeq_RAssert leafSpec O σ maskLabel c

@[simp] theorem specRun_selFence (leafSpec : LeafSpec) (O : SpecOracle)
    (σ : SpecState) (b : Bool) (c : LowCT) :
    specRun leafSpec O σ (selFence b c) = specRun leafSpec O σ c := by
  cases b <;> simp [selFence]

/-! ## 2. The three passes are identities for `specRun` -/

/-- The fence pass does not change the store-buffer run: every `RFence` and
    every `RGuard` is an `RAssert`, which `specRun` skips. -/
theorem specRun_insertFences (leafSpec : LeafSpec) (O : SpecOracle)
    (σ : SpecState) (c : LowCT) :
    specRun leafSpec O σ (insertFences c) = specRun leafSpec O σ c := by
  induction c generalizing σ with
  | RSeq c1 c2 ih1 ih2 => simp only [insertFences, specRun, ih1, ih2]
  | RLetZero x t body ih => simp only [insertFences, specRun, ih]
  | RLetU64Zero x body ih => simp only [insertFences, specRun, ih]
  | RBlock body ih => simp only [insertFences, specRun, ih]
  | RFnDef n p r body cont ihB ihC => simp only [insertFences, specRun, ihB, ihC]
  | RIfNz cond ct cf ihCt ihCf =>
      simp only [insertFences, specRun, specRun_fenced, ihCt, ihCf]
  | RWhileNz cond body ih =>
      simp only [insertFences, specRun, specRun_fenced, ih]
  | RFor x n body ih => simp only [insertFences, specRun, specRun_fenced, ih]
  | RCall f dest args => simp only [insertFences, specRun_fenceGuard]
  | RArrLoad dst src idx => simp only [insertFences, specRun_fenceGuard]
  | RArrStore arr idx src => simp only [insertFences, specRun_fenceGuard]
  | _ => rfl

/-- The mask pass does not change the store-buffer run: every `RMask` is an
    `RAssert`, which `specRun` skips. -/
theorem specRun_insertMasks (leafSpec : LeafSpec) (O : SpecOracle)
    (σ : SpecState) (c : LowCT) :
    specRun leafSpec O σ (insertMasks c) = specRun leafSpec O σ c := by
  induction c generalizing σ with
  | RSeq c1 c2 ih1 ih2 => simp only [insertMasks, specRun, ih1, ih2]
  | RLetZero x t body ih => simp only [insertMasks, specRun, ih]
  | RLetU64Zero x body ih => simp only [insertMasks, specRun, ih]
  | RBlock body ih => simp only [insertMasks, specRun, ih]
  | RFnDef n p r body cont ihB ihC => simp only [insertMasks, specRun, ihB, ihC]
  | RIfNz cond ct cf ihCt ihCf => simp only [insertMasks, specRun, ihCt, ihCf]
  | RWhileNz cond body ih => simp only [insertMasks, specRun, ih]
  | RFor x n body ih => simp only [insertMasks, specRun, ih]
  | RArrLoad dst src idx => simp only [insertMasks, specRun_masked]
  | _ => rfl

/-- The selective pass does not change the store-buffer run, for every
    protection set. -/
theorem specRun_insertSelective (leafSpec : LeafSpec) (O : SpecOracle)
    (protectSet : ProtectSet) (σ : SpecState) (c : LowCT) :
    specRun leafSpec O σ (insertSelective protectSet c) = specRun leafSpec O σ c := by
  induction c generalizing σ with
  | RSeq c1 c2 ih1 ih2 => simp only [insertSelective, specRun, ih1, ih2]
  | RLetZero x t body ih => simp only [insertSelective, specRun, ih]
  | RLetU64Zero x body ih => simp only [insertSelective, specRun, ih]
  | RBlock body ih => simp only [insertSelective, specRun, ih]
  | RFnDef n p r body cont ihB ihC =>
      simp only [insertSelective, specRun, ihB, ihC]
  | RIfNz cond ct cf ihCt ihCf =>
      simp only [insertSelective, specRun, specRun_selFence, ihCt, ihCf]
  | RWhileNz cond body ih =>
      simp only [insertSelective, specRun, specRun_selFence, ih]
  | RFor x n body ih => simp only [insertSelective, specRun, ih]
  | RCall f dest args => simp only [insertSelective, specRun_fenceGuard]
  | RArrLoad dst src idx => simp only [insertSelective, specRun_fenceGuard]
  | RArrStore arr idx src => simp only [insertSelective, specRun_fenceGuard]
  | _ => rfl

/-! ## 3. Speculative and committed constant-time transfer along the passes

Since the passes leave `specRun` fixed, they leave both store-buffer predicates
fixed. -/

theorem sctSB_insertFences_iff (leafSpec : LeafSpec) (window : Nat)
    (O : SpecOracle) (lt : LevelTable) (c : LowCT) :
    SpeculativelyConstantTimeSB leafSpec window O lt (insertFences c)
      ↔ SpeculativelyConstantTimeSB leafSpec window O lt c := by
  constructor <;> intro h rs1 rs2 hEq <;>
    simpa only [specRun_insertFences] using h rs1 rs2 hEq

theorem sctSB_insertMasks_iff (leafSpec : LeafSpec) (window : Nat)
    (O : SpecOracle) (lt : LevelTable) (c : LowCT) :
    SpeculativelyConstantTimeSB leafSpec window O lt (insertMasks c)
      ↔ SpeculativelyConstantTimeSB leafSpec window O lt c := by
  constructor <;> intro h rs1 rs2 hEq <;>
    simpa only [specRun_insertMasks] using h rs1 rs2 hEq

theorem sctSB_insertSelective_iff (leafSpec : LeafSpec) (window : Nat)
    (O : SpecOracle) (protectSet : ProtectSet) (lt : LevelTable) (c : LowCT) :
    SpeculativelyConstantTimeSB leafSpec window O lt (insertSelective protectSet c)
      ↔ SpeculativelyConstantTimeSB leafSpec window O lt c := by
  constructor <;> intro h rs1 rs2 hEq <;>
    simpa only [specRun_insertSelective] using h rs1 rs2 hEq

/-- The committed trace of the fenced program is the committed trace of the
    source, read off the never-speculate projection of `specRun`. -/
theorem archRun_trace_insertFences (leafSpec : LeafSpec) (rs : RustState)
    (c : LowCT) :
    (archRun leafSpec rs (insertFences c)).2 = (archRun leafSpec rs c).2 := by
  have h1 : (specRun leafSpec neverSpeculate ⟨rs, [], 0⟩ (insertFences c)).2
      = (archRun leafSpec rs (insertFences c)).2 :=
    (specRun_neverSpeculate leafSpec (insertFences c) ⟨rs, [], 0⟩).2
  have h2 : (specRun leafSpec neverSpeculate ⟨rs, [], 0⟩ c).2
      = (archRun leafSpec rs c).2 :=
    (specRun_neverSpeculate leafSpec c ⟨rs, [], 0⟩).2
  rw [← h1, ← h2, specRun_insertFences]

/-- The committed trace of the mask-hardened program is the committed trace of
    the source. -/
theorem archRun_trace_insertMasks (leafSpec : LeafSpec) (rs : RustState)
    (c : LowCT) :
    (archRun leafSpec rs (insertMasks c)).2 = (archRun leafSpec rs c).2 := by
  have h1 : (specRun leafSpec neverSpeculate ⟨rs, [], 0⟩ (insertMasks c)).2
      = (archRun leafSpec rs (insertMasks c)).2 :=
    (specRun_neverSpeculate leafSpec (insertMasks c) ⟨rs, [], 0⟩).2
  have h2 : (specRun leafSpec neverSpeculate ⟨rs, [], 0⟩ c).2
      = (archRun leafSpec rs c).2 :=
    (specRun_neverSpeculate leafSpec c ⟨rs, [], 0⟩).2
  rw [← h1, ← h2, specRun_insertMasks]

/-- The committed trace of the selectively protected program is the committed
    trace of the source. -/
theorem archRun_trace_insertSelective (leafSpec : LeafSpec)
    (protectSet : ProtectSet) (rs : RustState) (c : LowCT) :
    (archRun leafSpec rs (insertSelective protectSet c)).2
      = (archRun leafSpec rs c).2 := by
  have h1 : (specRun leafSpec neverSpeculate ⟨rs, [], 0⟩
        (insertSelective protectSet c)).2
      = (archRun leafSpec rs (insertSelective protectSet c)).2 :=
    (specRun_neverSpeculate leafSpec (insertSelective protectSet c) ⟨rs, [], 0⟩).2
  have h2 : (specRun leafSpec neverSpeculate ⟨rs, [], 0⟩ c).2
      = (archRun leafSpec rs c).2 :=
    (specRun_neverSpeculate leafSpec c ⟨rs, [], 0⟩).2
  rw [← h1, ← h2, specRun_insertSelective]

/-! ## 4. The drained-regime restatements

`window_zero_SCT` and `neverSpeculate_SCT` are the two regimes in which
`SpeculativelyConstantTimeSB` follows from `ArchConstantTimeSB`. Composing them
with the transfer results of §3 gives, for each pass, the statement that
replaces its `cmdCT`-hypothesised headline. -/

/-- The fenced program is speculatively constant-time against the store-buffer
    observer at window `0`, for every predictor. -/
theorem insertFences_SCT_SB_window_zero (leafSpec : LeafSpec) (O : SpecOracle)
    (lt : LevelTable) (c : LowCT) (h : ArchConstantTimeSB leafSpec lt c) :
    SpeculativelyConstantTimeSB leafSpec 0 O lt (insertFences c) :=
  (sctSB_insertFences_iff leafSpec 0 O lt c).mpr (window_zero_SCT leafSpec O lt c h)

/-- The fenced program is speculatively constant-time against the store-buffer
    observer under the never-speculate predictor, for every window. -/
theorem insertFences_SCT_SB_neverSpeculate (leafSpec : LeafSpec) (window : Nat)
    (lt : LevelTable) (c : LowCT) (h : ArchConstantTimeSB leafSpec lt c) :
    SpeculativelyConstantTimeSB leafSpec window neverSpeculate lt (insertFences c) :=
  (sctSB_insertFences_iff leafSpec window neverSpeculate lt c).mpr
    (neverSpeculate_SCT leafSpec window lt c h)

/-- The mask-hardened program is speculatively constant-time against the
    store-buffer observer at window `0`, for every predictor. -/
theorem insertMasks_SCT_SB_window_zero (leafSpec : LeafSpec) (O : SpecOracle)
    (lt : LevelTable) (c : LowCT) (h : ArchConstantTimeSB leafSpec lt c) :
    SpeculativelyConstantTimeSB leafSpec 0 O lt (insertMasks c) :=
  (sctSB_insertMasks_iff leafSpec 0 O lt c).mpr (window_zero_SCT leafSpec O lt c h)

/-- The mask-hardened program is speculatively constant-time against the
    store-buffer observer under the never-speculate predictor, for every
    window. -/
theorem insertMasks_SCT_SB_neverSpeculate (leafSpec : LeafSpec) (window : Nat)
    (lt : LevelTable) (c : LowCT) (h : ArchConstantTimeSB leafSpec lt c) :
    SpeculativelyConstantTimeSB leafSpec window neverSpeculate lt (insertMasks c) :=
  (sctSB_insertMasks_iff leafSpec window neverSpeculate lt c).mpr
    (neverSpeculate_SCT leafSpec window lt c h)

/-- The selectively protected program is speculatively constant-time against the
    store-buffer observer at window `0`, for every predictor and every
    protection set. -/
theorem insertSelective_SCT_SB_window_zero (leafSpec : LeafSpec) (O : SpecOracle)
    (protectSet : ProtectSet) (lt : LevelTable) (c : LowCT)
    (h : ArchConstantTimeSB leafSpec lt c) :
    SpeculativelyConstantTimeSB leafSpec 0 O lt (insertSelective protectSet c) :=
  (sctSB_insertSelective_iff leafSpec 0 O protectSet lt c).mpr
    (window_zero_SCT leafSpec O lt c h)

/-- The selectively protected program is speculatively constant-time against the
    store-buffer observer under the never-speculate predictor, for every window
    and every protection set. -/
theorem insertSelective_SCT_SB_neverSpeculate (leafSpec : LeafSpec) (window : Nat)
    (protectSet : ProtectSet) (lt : LevelTable) (c : LowCT)
    (h : ArchConstantTimeSB leafSpec lt c) :
    SpeculativelyConstantTimeSB leafSpec window neverSpeculate lt
      (insertSelective protectSet c) :=
  (sctSB_insertSelective_iff leafSpec window neverSpeculate protectSet lt c).mpr
    (neverSpeculate_SCT leafSpec window lt c h)

/-! ## 5. The passes against a bypassing predictor

`StlGadget.stlGadget` satisfies the hypothesis of each pass's headline result —
`cmdCT` acceptance, and for the selective pass also path coverage. Its image
under each pass separates the two `PublicEquiv` states under `alwaysBypass` at
window `2`. -/

/-- The protection set containing every site. -/
def protectAll : ProtectSet := fun _ => true

theorem stlGadget_coversAllPaths : coversAllPaths protectAll stlGadget = true := by
  decide

/-- The fence pass does not make the store-to-load gadget speculatively
    constant-time against the store-buffer observer. -/
theorem insertFences_not_SCT_SB :
    ¬ SpeculativelyConstantTimeSB leafSpecByte 2 alwaysBypass stlLevels
        (insertFences stlGadget) := by
  intro h
  exact absurd ((sctSB_insertFences_iff leafSpecByte 2 alwaysBypass stlLevels
      stlGadget).mp h (stlState 0) (stlState 1) (stlState_publicEquiv 0 1))
    stlGadget_speculative_leak

/-- The mask pass does not make the store-to-load gadget speculatively
    constant-time against the store-buffer observer. -/
theorem insertMasks_not_SCT_SB :
    ¬ SpeculativelyConstantTimeSB leafSpecByte 2 alwaysBypass stlLevels
        (insertMasks stlGadget) := by
  intro h
  exact absurd ((sctSB_insertMasks_iff leafSpecByte 2 alwaysBypass stlLevels
      stlGadget).mp h (stlState 0) (stlState 1) (stlState_publicEquiv 0 1))
    stlGadget_speculative_leak

/-- The selective pass does not make the store-to-load gadget speculatively
    constant-time against the store-buffer observer, even with every site
    protected. -/
theorem insertSelective_not_SCT_SB :
    ¬ SpeculativelyConstantTimeSB leafSpecByte 2 alwaysBypass stlLevels
        (insertSelective protectAll stlGadget) := by
  intro h
  exact absurd ((sctSB_insertSelective_iff leafSpecByte 2 alwaysBypass protectAll
      stlLevels stlGadget).mp h (stlState 0) (stlState 1) (stlState_publicEquiv 0 1))
    stlGadget_speculative_leak

/-- Each pass's headline hypotheses hold on the store-to-load gadget while its
    image under the pass leaks under the store-buffer observer. -/
theorem passes_not_SCT_SB :
    cmdCT stlGadget stlLevels LeafCTTable.canonical = true ∧
      coversAllPaths protectAll stlGadget = true ∧
        ¬ SpeculativelyConstantTimeSB leafSpecByte 2 alwaysBypass stlLevels
            (insertFences stlGadget) ∧
          ¬ SpeculativelyConstantTimeSB leafSpecByte 2 alwaysBypass stlLevels
              (insertMasks stlGadget) ∧
            ¬ SpeculativelyConstantTimeSB leafSpecByte 2 alwaysBypass stlLevels
                (insertSelective protectAll stlGadget) :=
  ⟨stlGadget_cmdCT, stlGadget_coversAllPaths, insertFences_not_SCT_SB,
    insertMasks_not_SCT_SB, insertSelective_not_SCT_SB⟩

/-! ## 6. Transient typing against the store-buffer observer

`TransientTyping.TransTyped` conjoins `cmdCT` on the architecturally erased
table with a side condition forbidding a `Transient` address slot. A table whose
image avoids `Transient` satisfies the side condition everywhere, so on such a
table the judgment is `cmdCT`. -/

open CatCrypt.Crypto.SecureCompilation.TransientTyping

/-- The transient table of the store-to-load gadget: the two-level table
    `stlLevels` embedded into the three-point lattice, so no slot is
    `Transient`. -/
def ttStl : TransTable := fun x => embedSecret (stlLevels x)

theorem archErase_ttStl : archErase ttStl = stlLevels := by
  funext x
  exact archEraseLevel_embedSecret (stlLevels x)

/-- The store-to-load gadget is transient-well-typed. -/
theorem stlGadget_transTyped :
    TransTyped ttStl stlGadget LeafCTTable.canonical = true := by
  decide

/-- The gadget whose committed run already leaks is transient-well-typed. -/
theorem archLeakGadget_transTyped :
    TransTyped ttStl archLeakGadget LeafCTTable.canonical = true := by
  decide

/-- Transient well-typedness gives neither speculative nor committed
    constant-time against the store-buffer observer. -/
theorem transTyped_not_imp_SB :
    TransTyped ttStl stlGadget LeafCTTable.canonical = true ∧
      ¬ SpeculativelyConstantTimeSB leafSpecByte 2 alwaysBypass
          (archErase ttStl) stlGadget ∧
        TransTyped ttStl archLeakGadget LeafCTTable.canonical = true ∧
          ¬ ArchConstantTimeSB leafSpecByte (archErase ttStl) archLeakGadget := by
  refine ⟨stlGadget_transTyped, ?_, archLeakGadget_transTyped, ?_⟩
  · rw [archErase_ttStl]; exact cmdCT_not_imp_SCT.2.2
  · rw [archErase_ttStl]; exact cmdCT_not_imp_ArchCT.2

/-- With `ArchConstantTimeSB` in place of the typing judgment, the drained
    regimes give speculative constant-time against the store-buffer observer. -/
theorem transTyped_table_SCT_SB_window_zero (leafSpec : LeafSpec) (O : SpecOracle)
    (tt : TransTable) (c : LowCT)
    (h : ArchConstantTimeSB leafSpec (archErase tt) c) :
    SpeculativelyConstantTimeSB leafSpec 0 O (archErase tt) c :=
  window_zero_SCT leafSpec O (archErase tt) c h

/-- The never-speculate companion of `transTyped_table_SCT_SB_window_zero`. -/
theorem transTyped_table_SCT_SB_neverSpeculate (leafSpec : LeafSpec) (window : Nat)
    (tt : TransTable) (c : LowCT)
    (h : ArchConstantTimeSB leafSpec (archErase tt) c) :
    SpeculativelyConstantTimeSB leafSpec window neverSpeculate (archErase tt) c :=
  neverSpeculate_SCT leafSpec window (archErase tt) c h

/-! ## 7. The passes at an open window

`SpeculativeCTStoreBuffer.cmdCT_cmov_publicDriven_imp_SCT_SB` gives speculative
constant-time against the store-buffer observer at every window, not only in the
drained regimes of §4. Since each pass is an identity for `specRun`, the
statement transfers to the pass output from the source's `cmdCT` acceptance and
`SelectAgrees`, under a public-driven predictor.

`insertFences_not_SCT_SB`, `insertMasks_not_SCT_SB` and
`insertSelective_not_SCT_SB` remain: `stlGadget` fails `SelectAgrees`. -/

/-- The fenced program is speculatively constant-time against the store-buffer
    observer at every window, under a public-driven predictor. -/
theorem insertFences_SCT_SB (leafSpec : LeafSpec) (window : Nat) (lt : LevelTable)
    (leafCT : LeafCTTable) {O : SpecOracle} (hO : PublicDrivenSB lt O) (c : LowCT)
    (hCT : cmdCT c lt leafCT = true) (hSA : SelectAgrees c) :
    SpeculativelyConstantTimeSB leafSpec window O lt (insertFences c) :=
  (sctSB_insertFences_iff leafSpec window O lt c).mpr
    (cmdCT_cmov_publicDriven_imp_SCT_SB leafSpec window lt leafCT hO c hCT hSA)

/-- The mask-hardened program is speculatively constant-time against the
    store-buffer observer at every window, under a public-driven predictor. -/
theorem insertMasks_SCT_SB (leafSpec : LeafSpec) (window : Nat) (lt : LevelTable)
    (leafCT : LeafCTTable) {O : SpecOracle} (hO : PublicDrivenSB lt O) (c : LowCT)
    (hCT : cmdCT c lt leafCT = true) (hSA : SelectAgrees c) :
    SpeculativelyConstantTimeSB leafSpec window O lt (insertMasks c) :=
  (sctSB_insertMasks_iff leafSpec window O lt c).mpr
    (cmdCT_cmov_publicDriven_imp_SCT_SB leafSpec window lt leafCT hO c hCT hSA)

/-- The selectively protected program is speculatively constant-time against the
    store-buffer observer at every window, under a public-driven predictor and for
    every protection set. -/
theorem insertSelective_SCT_SB (leafSpec : LeafSpec) (window : Nat)
    (protectSet : ProtectSet) (lt : LevelTable) (leafCT : LeafCTTable)
    {O : SpecOracle} (hO : PublicDrivenSB lt O) (c : LowCT)
    (hCT : cmdCT c lt leafCT = true) (hSA : SelectAgrees c) :
    SpeculativelyConstantTimeSB leafSpec window O lt (insertSelective protectSet c) :=
  (sctSB_insertSelective_iff leafSpec window O protectSet lt c).mpr
    (cmdCT_cmov_publicDriven_imp_SCT_SB leafSpec window lt leafCT hO c hCT hSA)

/-- The three passes applied to the conditional-move gadget, whose selector is
    `Secret` and whose speculative trace contains a transient forward. -/
theorem passes_SCT_SB_cmovStlGadget (window : Nat) :
    SpeculativelyConstantTimeSB leafSpecByte window alwaysBypass stlLevels
        (insertFences cmovStlGadget) ∧
      SpeculativelyConstantTimeSB leafSpecByte window alwaysBypass stlLevels
        (insertMasks cmovStlGadget) ∧
      SpeculativelyConstantTimeSB leafSpecByte window alwaysBypass stlLevels
        (insertSelective protectAll cmovStlGadget) :=
  ⟨insertFences_SCT_SB leafSpecByte window stlLevels LeafCTTable.canonical
      (alwaysBypass_publicDriven stlLevels) cmovStlGadget cmovStlGadget_cmdCT
      cmovStlGadget_selectAgrees,
   insertMasks_SCT_SB leafSpecByte window stlLevels LeafCTTable.canonical
      (alwaysBypass_publicDriven stlLevels) cmovStlGadget cmovStlGadget_cmdCT
      cmovStlGadget_selectAgrees,
   insertSelective_SCT_SB leafSpecByte window protectAll stlLevels
      LeafCTTable.canonical (alwaysBypass_publicDriven stlLevels) cmovStlGadget
      cmovStlGadget_cmdCT cmovStlGadget_selectAgrees⟩

end CatCrypt.Crypto.SecureCompilation.SpeculativeCTStoreBufferPasses
