/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRA

/-!
# Interference separation for the class-aware allocator

`ToLprogFaithfulRA` proves `physMap_no_collision` for `physAssign`, the
single-pool linear scan. The shipped table is `bodyPhysTable body =
physTableClassed (bodyTrace body) (bodyVecSlots body) (bodyReservedGP body)`,
which runs two independent scans (GP and vector) and concatenates them with the
vector indices offset by `vectorBase`. This module carries the separation over
to that table and to the name level, giving the live-out interference condition
`hinj` of `ToLprogFaithfulWriteSide.legalizeBinop_storeRel_step` as a theorem
about the allocator.

## Contents

* **§1 `physLoc` on concatenation and offset.** How a slot reads its location out
  of `gpAssign ++ vecAssign.map (· + vectorBase)`.
* **§2 physical-index bound.** The scan hands out indices below
  `numRegs + hulls.size + items.length`: registers below `numRegs` and one cell
  per step at worst. Below `vectorBase` this keeps the GP half out of the vector
  half's index range.
* **§3 `physAssignClassed_no_collision`.** Two distinct slots with overlapping
  conservative live ranges get distinct physical indices from the class-aware
  assignment, for any reserved GP and vector pools.
* **§4 the table.** `physMapTabled (physTableClassed …)` reports the assignment's
  location on the slot universe, so §3 transfers to the shipped table.
* **§5 liveness.** `LiveAt`, and that a slot whose live range contains a trace
  position is an item of `physLiveItems`.
* **§6 `physRename_hinj_liveOutNames`.** The name-level statement: at a trace
  position `pos`, among the names live out at `pos`, only the head's destination
  shares the destination's physical register.

## Scope

The index bound of §2 is a hypothesis of the body-level results in the form
`numGPRegs + (physLiveItems tr).length ≤ vectorBase`: a GP allocation that spills
into more than `vectorBase - numGPRegs` stack cells would take indices
`physRegName` renders as vector names.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRA
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill

/-! ## 1. `physLoc` on a concatenation and on an offset assignment -/

/-- A slot located in the left half of a concatenated assignment reads that
    location out of the concatenation. -/
theorem physLoc_append_of_left {l₁ l₂ : List (Nat × Nat)} {t p : Nat}
    (h : physLoc l₁ t = some p) : physLoc (l₁ ++ l₂) t = some p := by
  unfold physLoc at h ⊢
  rw [List.find?_append]
  cases hf : l₁.find? (fun q => q.1 == t) with
  | some q => simp only [hf, Option.map_some] at h ⊢; exact h
  | none => rw [hf] at h; exact absurd h (by simp)

/-- A slot absent from the left half of a concatenated assignment reads its
    location out of the right half. -/
theorem physLoc_append_of_none {l₁ l₂ : List (Nat × Nat)} {t : Nat}
    (h : physLoc l₁ t = none) : physLoc (l₁ ++ l₂) t = physLoc l₂ t := by
  unfold physLoc at h ⊢
  rw [List.find?_append]
  cases hf : l₁.find? (fun q => q.1 == t) with
  | some q => rw [hf] at h; exact absurd h (by simp)
  | none => simp

/-- Offsetting every physical index of an assignment offsets the location it
    reports. -/
theorem physLoc_map_add (k : Nat) :
    ∀ (l : List (Nat × Nat)) (t : Nat),
      physLoc (l.map (fun q => (q.1, q.2 + k))) t = (physLoc l t).map (· + k) := by
  intro l
  induction l with
  | nil => intro t; simp [physLoc]
  | cons q rest ih =>
    intro t
    rw [List.map_cons, physLoc_cons, physLoc_cons]
    by_cases hq : q.1 = t
    · simp [hq]
    · simp only [hq, if_neg, not_false_iff]
      exact ih t

/-! ## 2. The physical indices the scan hands out are bounded -/

/-- `allocCell` adds at most one cell. -/
theorem allocCell_size_le (hulls : CellHulls) (st en : Nat) :
    (allocCell hulls st en).2.size ≤ hulls.size + 1 := by
  simp only [allocCell]
  split
  · simp [Array.set!]
  · simp

/-- The cell index `allocCell` returns is at most the current cell count. -/
theorem allocCell_fst_le (hulls : CellHulls) (st en : Nat) :
    (allocCell hulls st en).1 ≤ hulls.size := by
  rw [allocCell_fst]
  exact firstFittingCell_le hulls st en hulls.size 0 (by omega) (by omega)

/-- One step hands out a physical index below `numRegs + hulls.size + 1`, given
    that the in-flight allocations hold pool registers. -/
theorem physScanSpillStep_phys_lt {numRegs : Nat} {uses : Array Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en B : Nat} {reserved : List Nat}
    (hB : numRegs + hulls.size + 1 ≤ B)
    (hact : ∀ a ∈ act, a.phys < numRegs)
    (hacc : ∀ q ∈ acc, q.2 < B) :
    ∀ q ∈ (physScanSpillStep numRegs uses act hulls acc s st en reserved).2.2,
      q.2 < B := by
  simp only [physScanSpillStep]
  split
  next ph hfr =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · have : ph < numRegs := freeRegIn_lt hfr
      omega
    · exact hacc q hq'
  next hfr =>
    split
    next far hv =>
      split
      next hp =>
        intro q hq
        have hfarAct : far ∈ act := (List.mem_filter.mp (spillVictim_mem hv)).1
        rcases List.mem_cons.mp hq with rfl | hq'
        · have := allocCell_fst_le hulls far.st far.en
          simp only []
          omega
        · rcases List.mem_cons.mp hq' with rfl | hq''
          · have := hact far hfarAct
            simp only []
            omega
          · exact hacc q hq''
      next hp =>
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · have := allocCell_fst_le hulls st en
          simp only []
          omega
        · exact hacc q hq'
    next hv =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · have := allocCell_fst_le hulls st en
        simp only []
        omega
      · exact hacc q hq'

/-- One step keeps the in-flight allocations on pool registers. -/
theorem physScanSpillStep_act_lt {numRegs : Nat} {uses : Array Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en : Nat} {reserved : List Nat}
    (hact : ∀ a ∈ act, a.phys < numRegs) :
    ∀ a ∈ (physScanSpillStep numRegs uses act hulls acc s st en reserved).1,
      a.phys < numRegs := by
  have hfil : ∀ (p : PhysActive → Bool) (l : List PhysActive) (a : PhysActive),
      a ∈ l.filter p → a ∈ l := fun _ _ _ ha => (List.mem_filter.mp ha).1
  simp only [physScanSpillStep]
  split
  next ph hfr =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact freeRegIn_lt hfr
    · exact hact a (hfil _ _ _ ha')
  next hfr =>
    split
    next far hv =>
      split
      next hp =>
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact hact far (List.mem_filter.mp (spillVictim_mem hv)).1
        · exact hact a (hfil _ _ _ (hfil _ _ _ ha'))
      next hp => intro a ha; exact hact a (hfil _ _ _ ha)
    next hv => intro a ha; exact hact a (hfil _ _ _ ha)

/-- One step's cell array grows by at most one. -/
theorem physScanSpillStep_hulls_le {numRegs : Nat} {uses : Array Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en : Nat} {reserved : List Nat} :
    (physScanSpillStep numRegs uses act hulls acc s st en reserved).2.1.size
      ≤ hulls.size + 1 := by
  simp only [physScanSpillStep]
  split
  next ph hfr => exact Nat.le_succ _
  next hfr =>
    split
    next far hv =>
      split
      next hp => exact allocCell_size_le hulls far.st far.en
      next hp => exact allocCell_size_le hulls st en
    next hv => exact allocCell_size_le hulls st en

/-- **The scan's physical indices are bounded.** The pool registers sit below
    `numRegs` and each step opens at most one stack cell, so every index the scan
    records is below `numRegs + hulls.size + items.length`. -/
theorem physScanSpill_phys_lt (numRegs : Nat) (uses : Array Nat) (reserved : List Nat) :
    ∀ (items : List (Nat × Nat × Nat)) (act : List PhysActive) (hulls : CellHulls)
      (acc : List (Nat × Nat)) (B : Nat),
      numRegs + hulls.size + items.length ≤ B →
      (∀ a ∈ act, a.phys < numRegs) →
      (∀ q ∈ acc, q.2 < B) →
      ∀ q ∈ physScanSpill numRegs uses items act hulls acc reserved, q.2 < B := by
  intro items
  induction items with
  | nil => intro act hulls acc B _ _ hacc q hq; exact hacc q hq
  | cons it rest ih =>
    intro act hulls acc B hB hact hacc q hq
    obtain ⟨s, stt, enn⟩ := it
    simp only [physScanSpill] at hq
    refine ih _ _ _ B ?_ (physScanSpillStep_act_lt hact) ?_ q hq
    · refine Nat.le_trans
        (Nat.add_le_add_right (Nat.add_le_add_left physScanSpillStep_hulls_le _) _) ?_
      simp only [List.length_cons] at hB
      omega
    · refine physScanSpillStep_phys_lt ?_ hact hacc
      simp only [List.length_cons] at hB
      omega

/-! ## 3. The class-aware assignment separates overlapping live slots -/

/-- The GP half of the class-aware assignment: the linear scan over the live
    items of GP class, over the GP pool less `reserved`. -/
def gpHalf (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved : List Nat) : List (Nat × Nat) :=
  physScanSpill numGPRegs (physLiveData tr).2
    ((physLiveItems tr).filter (fun it => !slotIsVec vecArr it.1)) [] #[] [] reserved

/-- The vector half of the class-aware assignment, before the `vectorBase`
    offset, over the vector pool less `reservedVec`. -/
def vecHalf (tr : List PhysEvent) (vecArr : Array Bool)
    (reservedVec : List Nat) : List (Nat × Nat) :=
  physScanSpill numVecRegs (physLiveData tr).2
    ((physLiveItems tr).filter (fun it => slotIsVec vecArr it.1)) [] #[] [] reservedVec

/-- The class-aware assignment is the GP half followed by the offset vector
    half. -/
theorem physAssignClassed_eq (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved reservedVec : List Nat) :
    physAssignClassed tr vecArr reserved reservedVec
      = gpHalf tr vecArr reserved
        ++ (vecHalf tr vecArr reservedVec).map (fun q => (q.1, q.2 + vectorBase)) := rfl

/-- Filtering keeps the scan's input contract. -/
theorem itemsSorted_filter {items : List (Nat × Nat × Nat)}
    (h : ItemsSorted items) (p : Nat × Nat × Nat → Bool) : ItemsSorted (items.filter p) :=
  List.Pairwise.sublist (List.filter_sublist) h

/-- Each half's item list carries each slot's `physLiveRange`. -/
theorem filter_range (tr : List PhysEvent) (p : Nat × Nat × Nat → Bool) :
    ∀ it ∈ (physLiveItems tr).filter p, physLiveRange tr it.1 = (it.2.1, it.2.2) :=
  fun it hit => physLiveItems_range tr it (List.mem_filter.mp hit).1

/-- The GP half's physical indices stay below `vectorBase`, given that the live
    item count leaves room for one stack cell per item. -/
theorem gpHalf_lt_vectorBase {tr : List PhysEvent} {vecArr : Array Bool}
    {reserved : List Nat}
    (hfit : numGPRegs + (physLiveItems tr).length ≤ vectorBase) :
    ∀ q ∈ gpHalf tr vecArr reserved, q.2 < vectorBase := by
  refine physScanSpill_phys_lt numGPRegs (physLiveData tr).2 reserved _ [] #[] []
    vectorBase ?_ (by simp) (by simp)
  have := List.length_filter_le (fun it => !slotIsVec vecArr it.1) (physLiveItems tr)
  simpa using by omega

/-- A GP-half location is below `vectorBase`. -/
theorem gpHalf_physLoc_lt {tr : List PhysEvent} {vecArr : Array Bool} {t p : Nat}
    {reserved : List Nat}
    (hfit : numGPRegs + (physLiveItems tr).length ≤ vectorBase)
    (h : physLoc (gpHalf tr vecArr reserved) t = some p) : p < vectorBase := by
  unfold physLoc at h
  cases hf : (gpHalf tr vecArr reserved).find? (fun q => q.1 == t) with
  | some q =>
    rw [hf] at h
    have : q.2 = p := by simpa using h
    exact this ▸ gpHalf_lt_vectorBase hfit q (List.mem_of_find?_eq_some hf)
  | none => rw [hf] at h; exact absurd h (by simp)

/-- **The class-aware assignment is collision-free.** Two distinct slots whose
    conservative live ranges overlap never receive the same physical index from
    `physAssignClassed`: the GP scan and the vector scan are each collision-free
    on their own item list, and the `vectorBase` offset keeps the two pools
    apart. -/
theorem physAssignClassed_no_collision (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved reservedVec : List Nat)
    (hfit : numGPRegs + (physLiveItems tr).length ≤ vectorBase)
    {t₁ t₂ p : Nat} (hne : t₁ ≠ t₂)
    (h1 : physLoc (physAssignClassed tr vecArr reserved reservedVec) t₁ = some p)
    (h2 : physLoc (physAssignClassed tr vecArr reserved reservedVec) t₂ = some p) :
    ¬ physRangesOverlap (physLiveRange tr t₁) (physLiveRange tr t₂) := by
  rw [physAssignClassed_eq] at h1 h2
  cases hg1 : physLoc (gpHalf tr vecArr reserved) t₁ with
  | some p₁ =>
    rw [physLoc_append_of_left hg1] at h1
    cases h1
    cases hg2 : physLoc (gpHalf tr vecArr reserved) t₂ with
    | some p₂ =>
      rw [physLoc_append_of_left hg2] at h2
      cases h2
      exact physScanSpill_no_collision numGPRegs (physLiveData tr).2 reserved
        (physLiveRange tr) _
        (itemsSorted_filter (physLiveItems_sorted tr) _) (filter_range tr _) hne hg1 hg2
    | none =>
      rw [physLoc_append_of_none hg2, physLoc_map_add] at h2
      cases hv2 : physLoc (vecHalf tr vecArr reservedVec) t₂ with
      | some q₂ =>
        rw [hv2] at h2
        have hle : vectorBase ≤ p := by
          simp only [Option.map_some, Option.some.injEq] at h2
          omega
        exact absurd (gpHalf_physLoc_lt hfit hg1) (by omega)
      | none => rw [hv2] at h2; exact absurd h2 (by simp)
  | none =>
    rw [physLoc_append_of_none hg1, physLoc_map_add] at h1
    cases hv1 : physLoc (vecHalf tr vecArr reservedVec) t₁ with
    | none => rw [hv1] at h1; exact absurd h1 (by simp)
    | some q₁ =>
      rw [hv1] at h1
      have hp1 : q₁ + vectorBase = p := by simpa using h1
      cases hg2 : physLoc (gpHalf tr vecArr reserved) t₂ with
      | some p₂ =>
        rw [physLoc_append_of_left hg2] at h2
        cases h2
        exact absurd (gpHalf_physLoc_lt hfit hg2) (by omega)
      | none =>
        rw [physLoc_append_of_none hg2, physLoc_map_add] at h2
        cases hv2 : physLoc (vecHalf tr vecArr reservedVec) t₂ with
        | none => rw [hv2] at h2; exact absurd h2 (by simp)
        | some q₂ =>
          rw [hv2] at h2
          have hp2 : q₂ + vectorBase = p := by simpa using h2
          have hq : q₁ = q₂ := by omega
          subst hq
          exact physScanSpill_no_collision numVecRegs (physLiveData tr).2 reservedVec
            (physLiveRange tr) _
            (itemsSorted_filter (physLiveItems_sorted tr) _) (filter_range tr _) hne hv1 hv2

/-- Every live slot gets a location from the class-aware assignment: it is an
    item of the scan of its own class, and that scan assigns every item. -/
theorem physAssignClassed_physLoc_live (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved reservedVec : List Nat) {s : Nat}
    (hs : ∃ it ∈ physLiveItems tr, it.1 = s) :
    physLoc (physAssignClassed tr vecArr reserved reservedVec) s ≠ none := by
  obtain ⟨it, hit, rfl⟩ := hs
  rw [physAssignClassed_eq]
  by_cases hv : slotIsVec vecArr it.1
  · have hmem : it ∈ (physLiveItems tr).filter (fun i => slotIsVec vecArr i.1) :=
      List.mem_filter.mpr ⟨hit, by simpa using hv⟩
    have hvloc : physLoc (vecHalf tr vecArr reservedVec) it.1 ≠ none :=
      physScanSpill_assigns numVecRegs (physLiveData tr).2 reservedVec _ [] #[] [] it hmem
    cases hg : physLoc (gpHalf tr vecArr reserved) it.1 with
    | some p => rw [physLoc_append_of_left hg]; simp
    | none =>
      rw [physLoc_append_of_none hg, physLoc_map_add]
      cases hvv : physLoc (vecHalf tr vecArr reservedVec) it.1 with
      | some q => simp
      | none => exact absurd hvv hvloc
  · have hmem : it ∈ (physLiveItems tr).filter (fun i => !slotIsVec vecArr i.1) :=
      List.mem_filter.mpr ⟨hit, by simpa using hv⟩
    have hgloc : physLoc (gpHalf tr vecArr reserved) it.1 ≠ none :=
      physScanSpill_assigns numGPRegs (physLiveData tr).2 reserved _ [] #[] [] it hmem
    cases hg : physLoc (gpHalf tr vecArr reserved) it.1 with
    | some p => rw [physLoc_append_of_left hg]; simp
    | none => exact absurd hg hgloc

/-! ## 4. The lookup table reports the assignment -/

/-- `physMapTabled` over the class-aware table reports the location the
    class-aware assignment recorded, on the slot universe. -/
theorem physMapTabled_physTableClassed_of_physLoc {tr : List PhysEvent} {vecArr : Array Bool}
    {reserved reservedVec : List Nat}
    {s p : Nat} (hs : s < physUniverse tr)
    (h : physLoc (physAssignClassed tr vecArr reserved reservedVec) s = some p) :
    physMapTabled (physTableClassed tr vecArr reserved reservedVec) s = p := by
  unfold physMapTabled physTableClassed physLoc at *
  rw [Array.getElem?_map, Array.getElem?_range]
  simp only [hs, ↓reduceIte, Option.map_some, Option.getD_some]
  cases hf : (physAssignClassed tr vecArr reserved reservedVec).find? (fun q => q.1 == s) with
  | some q => rw [hf] at h; simpa using h
  | none => rw [hf] at h; exact absurd h (by simp)

/-- **The shipped table separates overlapping live slots.** Two distinct live
    slots of `tr` whose ranges overlap get distinct entries in
    `physTableClassed`. -/
theorem physTableClassed_no_collision (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved reservedVec : List Nat)
    (hfit : numGPRegs + (physLiveItems tr).length ≤ vectorBase)
    {t₁ t₂ : Nat} (hne : t₁ ≠ t₂)
    (hu1 : t₁ < physUniverse tr) (hu2 : t₂ < physUniverse tr)
    (hl1 : ∃ it ∈ physLiveItems tr, it.1 = t₁)
    (hl2 : ∃ it ∈ physLiveItems tr, it.1 = t₂)
    (hov : physRangesOverlap (physLiveRange tr t₁) (physLiveRange tr t₂)) :
    physMapTabled (physTableClassed tr vecArr reserved reservedVec) t₁
      ≠ physMapTabled (physTableClassed tr vecArr reserved reservedVec) t₂ := by
  intro heq
  cases h1 : physLoc (physAssignClassed tr vecArr reserved reservedVec) t₁ with
  | none => exact physAssignClassed_physLoc_live tr vecArr reserved reservedVec hl1 h1
  | some p₁ =>
    cases h2 : physLoc (physAssignClassed tr vecArr reserved reservedVec) t₂ with
    | none => exact physAssignClassed_physLoc_live tr vecArr reserved reservedVec hl2 h2
    | some p₂ =>
      have e1 := physMapTabled_physTableClassed_of_physLoc (vecArr := vecArr) hu1 h1
      have e2 := physMapTabled_physTableClassed_of_physLoc (vecArr := vecArr) hu2 h2
      have hpp : p₁ = p₂ := by rw [← e1, ← e2]; exact heq
      subst hpp
      exact physAssignClassed_no_collision tr vecArr reserved reservedVec hfit hne h1 h2 hov

/-! ## 5. Liveness: a slot whose range contains a trace position is an item -/

/-- A slot is **live at** trace position `pos` when its conservative live range
    contains `pos`. -/
def LiveAt (tr : List PhysEvent) (pos s : Nat) : Prop :=
  (physLiveRange tr s).1 ≤ pos ∧ pos ≤ (physLiveRange tr s).2

/-- A slot is **live out at** trace position `pos` when its conservative live
    range starts no later than `pos` and ends after it: the slot is still read
    after the head at `pos`. -/
def LiveOutAt (tr : List PhysEvent) (pos s : Nat) : Prop :=
  (physLiveRange tr s).1 ≤ pos ∧ pos < (physLiveRange tr s).2

theorem LiveOutAt.liveAt {tr : List PhysEvent} {pos s : Nat}
    (h : LiveOutAt tr pos s) : LiveAt tr pos s := ⟨h.1, Nat.le_of_lt h.2⟩

/-- Two slots live at the same trace position have overlapping ranges. -/
theorem overlap_of_liveAt {tr : List PhysEvent} {pos t₁ t₂ : Nat}
    (h1 : LiveAt tr pos t₁) (h2 : LiveAt tr pos t₂) :
    physRangesOverlap (physLiveRange tr t₁) (physLiveRange tr t₂) := by
  obtain ⟨ha1, hb1⟩ := h1
  obtain ⟨ha2, hb2⟩ := h2
  simp only [physRangesOverlap, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- A `foldl`-max is at least its seed. -/
theorem le_foldl_max : ∀ (l : List Nat) (init : Nat), init ≤ l.foldl Nat.max init := by
  intro l
  induction l with
  | nil => intro init; exact Nat.le_refl _
  | cons a rest ih =>
    intro init
    exact Nat.le_trans (Nat.le_max_left init a) (ih (Nat.max init a))

/-- A `foldl`-max dominates every element. -/
theorem mem_le_foldl_max : ∀ (l : List Nat) (init x : Nat),
    x ∈ l → x ≤ l.foldl Nat.max init := by
  intro l
  induction l with
  | nil => intro _ _ hx; exact absurd hx (by simp)
  | cons a rest ih =>
    intro init x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.le_trans (Nat.le_max_right init x) (le_foldl_max rest (Nat.max init x))
    · exact ih (Nat.max init a) x hx'

/-- A slot an event touches is inside the slot universe. -/
theorem lt_physUniverse_of_touched {tr : List PhysEvent} {e : PhysEvent} {s : Nat}
    (he : e ∈ tr) (hs : s ∈ e.touched) : s < physUniverse tr := by
  have hmem : s ∈ tr.flatMap PhysEvent.touched := List.mem_flatMap.mpr ⟨e, he, hs⟩
  have := mem_le_foldl_max (tr.flatMap PhysEvent.touched) 0 s hmem
  unfold physUniverse
  omega

/-- A slot whose first touch is inside the trace is touched by an event of the
    trace. -/
theorem touched_of_physFirstTouch_lt {tr : List PhysEvent} {s : Nat}
    (h : physFirstTouch tr s < tr.length) : ∃ e ∈ tr, s ∈ e.touched := by
  unfold physFirstTouch at h
  cases hf : tr.zipIdx.find? (fun p => p.1.touched.contains s) with
  | none => rw [hf] at h; simp at h
  | some q =>
    refine ⟨q.1, ?_, ?_⟩
    · have hq : q ∈ tr.zipIdx := List.mem_of_find?_eq_some hf
      have : q.1 ∈ tr.zipIdx.map Prod.fst := List.mem_map_of_mem hq
      simpa using this
    · have := List.find?_some hf
      simpa using this

/-- A slot whose live range starts inside the trace is an item of
    `physLiveItems`. -/
theorem physLiveItems_mem_of_start_lt {tr : List PhysEvent} {s : Nat}
    (hs : s < physUniverse tr) (hst : (physLiveRange tr s).1 < tr.length) :
    ∃ it ∈ physLiveItems tr, it.1 = s := by
  refine ⟨(s, (physLiveRange tr s).1, (physLiveRange tr s).2), ?_, rfl⟩
  simp only [physLiveItems, physLiveData, kernelMergeSort_eq]
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filterMap]
  exact ⟨s, List.mem_range.mpr hs, by simp only [hst, if_pos]⟩

/-- A slot live at a trace position inside the trace is an item of
    `physLiveItems`, and is inside the slot universe. -/
theorem live_item_of_liveAt {tr : List PhysEvent} {pos s : Nat}
    (hpos : pos < tr.length) (h : LiveAt tr pos s) :
    s < physUniverse tr ∧ ∃ it ∈ physLiveItems tr, it.1 = s := by
  have hst : (physLiveRange tr s).1 < tr.length := Nat.lt_of_le_of_lt h.1 hpos
  have hft : physFirstTouch tr s < tr.length := hst
  obtain ⟨e, he, hse⟩ := touched_of_physFirstTouch_lt hft
  have hu : s < physUniverse tr := lt_physUniverse_of_touched he hse
  exact ⟨hu, physLiveItems_mem_of_start_lt hu hst⟩

/-! ## 6. The live-out interference condition as a theorem -/

/-- **The live-out interference condition.** At a trace position `pos` inside the
    body's trace, a name live at `pos` that shares the destination's physical
    register with the destination is the destination. This is the `hinj` of
    `ToLprogFaithfulWriteSide.legalizeBinop_storeRel_step` and of
    `ToLprogFaithfulBody.binopBlockMaintains`, at the liveness the allocator
    itself works against.

    `hfit` scopes the statement to a live-slot count that leaves the GP pool
    below `vectorBase`. -/
theorem physRename_hinj_of_liveAt {body : Lcmd} {pos : Nat} {m nDst : String}
    (hfit : numGPRegs + (physLiveItems (bodyTrace body)).length ≤ vectorBase)
    (hpos : pos < (bodyTrace body).length)
    (hm : m ∈ bodyNames body) (hnDst : nDst ∈ bodyNames body)
    (hmLive : LiveAt (bodyTrace body) pos (nameSlot body m))
    (hdLive : LiveAt (bodyTrace body) pos (nameSlot body nDst))
    (h : physRename body (bodyPhysTable body) m
      = physRename body (bodyPhysTable body) nDst) : m = nDst := by
  refine physRename_injOn_live hm hnDst ?_ h
  intro hmap
  by_contra hslot
  obtain ⟨hu1, hi1⟩ := live_item_of_liveAt hpos hmLive
  obtain ⟨hu2, hi2⟩ := live_item_of_liveAt hpos hdLive
  unfold bodyPhysTable at hmap
  exact physTableClassed_no_collision (bodyTrace body) (bodyVecSlots body)
    (bodyReservedGP body) [] hfit hslot hu1 hu2 hi1 hi2
    (overlap_of_liveAt hmLive hdLive) hmap

/-- The names of a body live out after the head at trace position `pos`: their
    slot's conservative live range starts no later than `pos` and ends after
    it. -/
def liveOutNames (body : Lcmd) (pos : Nat) : List String :=
  (bodyNames body).filter (fun n =>
    decide ((physLiveRange (bodyTrace body) (nameSlot body n)).1 ≤ pos)
      && decide (pos < (physLiveRange (bodyTrace body) (nameSlot body n)).2))

/-- **`hinj` at the concrete live-out set.** Instantiating
    `legalizeBinop_storeRel_step`'s `Lout` at `liveOutNames body pos` discharges
    its interference hypothesis, for a destination whose own slot is live at
    `pos`. -/
theorem physRename_hinj_liveOutNames {body : Lcmd} {pos : Nat} {nDst : String}
    (hfit : numGPRegs + (physLiveItems (bodyTrace body)).length ≤ vectorBase)
    (hpos : pos < (bodyTrace body).length)
    (hnDst : nDst ∈ bodyNames body)
    (hdLive : LiveAt (bodyTrace body) pos (nameSlot body nDst)) :
    ∀ m ∈ liveOutNames body pos,
      physRename body (bodyPhysTable body) m = physRename body (bodyPhysTable body) nDst →
        m = nDst := by
  intro m hm h
  rw [liveOutNames, List.mem_filter] at hm
  obtain ⟨hmem, hlive⟩ := hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hlive
  exact physRename_hinj_of_liveAt hfit hpos hmem hnDst
    (LiveOutAt.liveAt ⟨hlive.1, hlive.2⟩) hdLive h

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference
