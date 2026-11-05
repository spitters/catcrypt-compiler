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
* **§2′ pieces of split intervals.** `physScanSpill_phys_lt_noPiece`: with pieces
  (`pieceOf`), the bound of §2 holds with the items that are no pieces, since a piece
  opens no stack cell on balance (`physScanSpillStep_cells_le`).
* **§2″ the input of the scan with splitting.** `splitScanInput` is sorted, names each
  slot once and carries the ranges `splitRange` (`splitScanInput_sorted`,
  `splitScanInput_range`); its items that are no pieces are the live items.
* **§3 `physAssignClassed_no_collision`.** Two distinct slots with overlapping
  conservative live ranges get distinct physical indices from the class-aware
  assignment, for any reserved GP and vector pools and at every split configuration.
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
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)

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
    · simp only [hq, ite_eq_right, not_false_iff]
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
    {s st en B : Nat} {reserved : List Nat} {pieceOf : Nat → Option Nat}
    (hB : numRegs + hulls.size + 1 ≤ B)
    (hact : ∀ a ∈ act, a.phys < numRegs)
    (hacc : ∀ q ∈ acc, q.2 < B) :
    ∀ q ∈ (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).2.2,
      q.2 < B := by
  have hspill : ∀ (st' en' : Nat) (q : Nat × Nat),
      q ∈ (s, numRegs + (allocCell hulls st' en').1) :: acc → q.2 < B := by
    intro st' en' q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · have := allocCell_fst_le hulls st' en'
      simp only []
      omega
    · exact hacc q hq'
  simp only [physScanSpillStep, physScanSpillLose]
  split
  next => exact hacc
  next =>
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
          have hfarAct : far ∈ act :=
            (List.mem_filter.mp (List.mem_filter.mp (spillVictim_mem hv)).1).1
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
          split
          next => exact hacc
          next => exact hspill st en
      next hv =>
        split
        next => exact hacc
        next => exact hspill st en

/-- One step keeps the in-flight allocations on pool registers. -/
theorem physScanSpillStep_act_lt {numRegs : Nat} {uses : Array Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en : Nat} {reserved : List Nat} {pieceOf : Nat → Option Nat}
    (hact : ∀ a ∈ act, a.phys < numRegs) :
    ∀ a ∈ (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).1,
      a.phys < numRegs := by
  have hfil : ∀ (p : PhysActive → Bool) (l : List PhysActive) (a : PhysActive),
      a ∈ l.filter p → a ∈ l := fun _ _ _ ha => (List.mem_filter.mp ha).1
  simp only [physScanSpillStep, physScanSpillLose]
  split
  next => intro a ha; exact hact a (hfil _ _ _ ha)
  next =>
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
          · exact hact far (hfil _ _ _ (hfil _ _ _ (spillVictim_mem hv)))
          · exact hact a (hfil _ _ _ (hfil _ _ _ ha'))
        next hp => split <;> (intro a ha; exact hact a (hfil _ _ _ ha))
      next hv => split <;> (intro a ha; exact hact a (hfil _ _ _ ha))

/-- One step's cell array grows by at most one. -/
theorem physScanSpillStep_hulls_le {numRegs : Nat} {uses : Array Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en : Nat} {reserved : List Nat} {pieceOf : Nat → Option Nat} :
    (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).2.1.size
      ≤ hulls.size + 1 := by
  simp only [physScanSpillStep, physScanSpillLose]
  split
  next => exact Nat.le_succ _
  next =>
    split
    next ph hfr => exact Nat.le_succ _
    next hfr =>
      split
      next far hv =>
        split
        next hp => exact allocCell_size_le hulls far.st far.en
        next hp =>
          split
          next => exact Nat.le_succ _
          next => exact allocCell_size_le hulls st en
      next hv =>
        split
        next => exact Nat.le_succ _
        next => exact allocCell_size_le hulls st en

/-- **The scan's physical indices are bounded.** The pool registers sit below
    `numRegs` and each step opens at most one stack cell, so every index the scan
    records is below `numRegs + hulls.size + items.length`. -/
theorem physScanSpill_phys_lt (numRegs : Nat) (uses : Array Nat) (reserved : List Nat)
    {pieceOf : Nat → Option Nat} :
    ∀ (items : List (Nat × Nat × Nat)) (act : List PhysActive) (hulls : CellHulls)
      (acc : List (Nat × Nat)) (B : Nat),
      numRegs + hulls.size + items.length ≤ B →
      (∀ a ∈ act, a.phys < numRegs) →
      (∀ q ∈ acc, q.2 < B) →
      ∀ q ∈ physScanSpill numRegs uses items act hulls acc reserved pieceOf, q.2 < B := by
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

/-! ## 2′. The physical-index bound with pieces of split intervals

A piece of a split interval (`physScanSpillStep` at `pieceOf`) opens no stack cell of its own:
when it takes the register of a resident value, that value, which is no piece, leaves the
in-flight allocations for a cell. The cells and the in-flight allocations that are no pieces
together grow by at most one at each item that is no piece, so the bound of §2 holds with the
items that are no pieces in place of all items. -/

/-- An in-flight allocation is **no piece** under `pieceOf` when its slot has no parent. -/
def noPiece (pieceOf : Nat → Option Nat) (a : PhysActive) : Bool := (pieceOf a.slot).isNone

/-- Removing by a filter an element that a count counts lowers the count by one. -/
theorem countP_filter_succ_le {l : List PhysActive} {p q : PhysActive → Bool}
    {x : PhysActive} (hx : x ∈ l) (hp : p x = true) (hq : q x = false) :
    (l.filter q).countP p + 1 ≤ l.countP p := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    have hle := (List.filter_sublist (p := q) (l := l)).countP_le (p := p)
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp only [List.filter_cons, hq, List.countP_cons, hp]
      simp
      omega
    · have := ih hx'
      by_cases hqa : q a = true <;> by_cases hpa : p a = true <;>
        simp [hqa, hpa] <;> omega

/-- One step: the cells and the in-flight allocations that are no pieces grow by at most
    one, and only at an interval that is no piece. -/
theorem physScanSpillStep_cells_le {numRegs : Nat} {uses : Array Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en : Nat} {reserved : List Nat} {pieceOf : Nat → Option Nat} :
    (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).2.1.size
      + (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).1.countP
          (noPiece pieceOf)
      ≤ hulls.size + act.countP (noPiece pieceOf) + (if (pieceOf s).isNone then 1 else 0) := by
  have h0 := (List.filter_sublist (p := fun a : PhysActive => decide (a.en ≥ st))
    (l := act)).countP_le (p := noPiece pieceOf)
  by_cases hsk : pieceSkip numRegs pieceOf acc s = true
  · simp only [physScanSpillStep, hsk, ↓reduceIte]
    omega
  cases hfr : freeRegIn numRegs
      ((act.filter (fun a => decide (a.en ≥ st))).map PhysActive.phys) reserved with
  | some ph =>
    simp only [physScanSpillStep, hsk, hfr, Bool.false_eq_true, ↓reduceIte]
    rw [List.countP_cons]
    simp only [noPiece]
    by_cases hn : (pieceOf s).isNone = true <;> simp only [hn, ↓reduceIte] <;> omega
  | none =>
    cases hv : spillVictim st uses ((act.filter (fun a => decide (a.en ≥ st))).filter
        (fun a => (pieceOf a.slot).isNone)) with
    | some far =>
      by_cases hp : spillPrefer st uses far ⟨st, en, numRegs, s⟩ = true
      · simp only [physScanSpillStep, hsk, hfr, hv, hp, Bool.false_eq_true, ↓reduceIte]
        have hfar := List.mem_filter.mp (spillVictim_mem hv)
        have hlt := countP_filter_succ_le (p := noPiece pieceOf)
          (q := fun a => a.phys != far.phys) hfar.1 (by simpa [noPiece] using hfar.2)
          (by simp)
        have := allocCell_size_le hulls far.st far.en
        rw [List.countP_cons]
        simp only [noPiece] at hlt ⊢
        by_cases hn : (pieceOf s).isNone = true <;> simp only [hn, ↓reduceIte] at hlt ⊢ <;> omega
      · by_cases hs : (pieceOf s).isSome = true
        · simp only [physScanSpillStep, physScanSpillLose, hsk, hfr, hv, hp, hs,
            Bool.false_eq_true, ↓reduceIte]
          omega
        · simp only [physScanSpillStep, physScanSpillLose, hsk, hfr, hv, hp, hs,
            Bool.false_eq_true, ↓reduceIte]
          have := allocCell_size_le hulls st en
          simp only [Bool.not_eq_true, Option.isSome_eq_false_iff] at hs
          simp only [hs, ↓reduceIte]
          omega
    | none =>
      by_cases hs : (pieceOf s).isSome = true
      · simp only [physScanSpillStep, physScanSpillLose, hsk, hfr, hv, hs,
          Bool.false_eq_true, ↓reduceIte]
        omega
      · simp only [physScanSpillStep, physScanSpillLose, hsk, hfr, hv, hs,
          Bool.false_eq_true, ↓reduceIte]
        have := allocCell_size_le hulls st en
        simp only [Bool.not_eq_true, Option.isSome_eq_false_iff] at hs
        simp only [hs, ↓reduceIte]
        omega

/-- One step hands out a physical index below `B` when `B` leaves room for the cells, the
    in-flight allocations that are no pieces and the interval if it is no piece. -/
theorem physScanSpillStep_phys_lt_noPiece {numRegs : Nat} {uses : Array Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en B : Nat} {reserved : List Nat} {pieceOf : Nat → Option Nat}
    (hB : numRegs + hulls.size + act.countP (noPiece pieceOf)
      + (if (pieceOf s).isNone then 1 else 0) ≤ B)
    (hact : ∀ a ∈ act, a.phys < numRegs)
    (hacc : ∀ q ∈ acc, q.2 < B) :
    ∀ q ∈ (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).2.2,
      q.2 < B := by
  have hcons : ∀ (st' en' : Nat), numRegs + hulls.size + 1 ≤ B →
      ∀ q ∈ (s, numRegs + (allocCell hulls st' en').1) :: acc, q.2 < B := by
    intro st' en' hb q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · have := allocCell_fst_le hulls st' en'
      dsimp only
      omega
    · exact hacc q hq'
  by_cases hsk : pieceSkip numRegs pieceOf acc s = true
  · simp only [physScanSpillStep, hsk, ↓reduceIte]
    exact hacc
  cases hfr : freeRegIn numRegs
      ((act.filter (fun a => decide (a.en ≥ st))).map PhysActive.phys) reserved with
  | some ph =>
    simp only [physScanSpillStep, hsk, hfr, Bool.false_eq_true, ↓reduceIte]
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · have : ph < numRegs := freeRegIn_lt hfr
      dsimp only
      omega
    · exact hacc q hq'
  | none =>
    cases hv : spillVictim st uses ((act.filter (fun a => decide (a.en ≥ st))).filter
        (fun a => (pieceOf a.slot).isNone)) with
    | some far =>
      by_cases hp : spillPrefer st uses far ⟨st, en, numRegs, s⟩ = true
      · simp only [physScanSpillStep, hsk, hfr, hv, hp, Bool.false_eq_true, ↓reduceIte]
        intro q hq
        have hfar := List.mem_filter.mp (spillVictim_mem hv)
        have hfarAct : far ∈ act := (List.mem_filter.mp hfar.1).1
        have hpos : 0 < act.countP (noPiece pieceOf) :=
          List.countP_pos_iff.mpr ⟨far, hfarAct, by simpa [noPiece] using hfar.2⟩
        rcases List.mem_cons.mp hq with rfl | hq'
        · have := allocCell_fst_le hulls far.st far.en
          dsimp only
          omega
        · rcases List.mem_cons.mp hq' with rfl | hq''
          · have := hact far hfarAct
            dsimp only
            omega
          · exact hacc q hq''
      · by_cases hs : (pieceOf s).isSome = true
        · simp only [physScanSpillStep, physScanSpillLose, hsk, hfr, hv, hp, hs,
            Bool.false_eq_true, ↓reduceIte]
          exact hacc
        · simp only [physScanSpillStep, physScanSpillLose, hsk, hfr, hv, hp, hs,
            Bool.false_eq_true, ↓reduceIte]
          simp only [Bool.not_eq_true, Option.isSome_eq_false_iff] at hs
          simp only [hs, ↓reduceIte] at hB
          exact hcons st en (by omega)
    | none =>
      by_cases hs : (pieceOf s).isSome = true
      · simp only [physScanSpillStep, physScanSpillLose, hsk, hfr, hv, hs,
          Bool.false_eq_true, ↓reduceIte]
        exact hacc
      · simp only [physScanSpillStep, physScanSpillLose, hsk, hfr, hv, hs,
          Bool.false_eq_true, ↓reduceIte]
        simp only [Bool.not_eq_true, Option.isSome_eq_false_iff] at hs
        simp only [hs, ↓reduceIte] at hB
        exact hcons st en (by omega)

/-- **The scan's physical indices are bounded, pieces of split intervals included.** Every
    index the scan records is below `numRegs` plus the cells, the in-flight allocations that
    are no pieces and the items that are no pieces. -/
theorem physScanSpill_phys_lt_noPiece (numRegs : Nat) (uses : Array Nat) (reserved : List Nat)
    {pieceOf : Nat → Option Nat} :
    ∀ (items : List (Nat × Nat × Nat)) (act : List PhysActive) (hulls : CellHulls)
      (acc : List (Nat × Nat)) (B : Nat),
      numRegs + hulls.size + act.countP (noPiece pieceOf)
        + items.countP (fun it => (pieceOf it.1).isNone) ≤ B →
      (∀ a ∈ act, a.phys < numRegs) →
      (∀ q ∈ acc, q.2 < B) →
      ∀ q ∈ physScanSpill numRegs uses items act hulls acc reserved pieceOf, q.2 < B := by
  intro items
  induction items with
  | nil => intro act hulls acc B _ _ hacc q hq; exact hacc q hq
  | cons it rest ih =>
    intro act hulls acc B hB hact hacc q hq
    obtain ⟨s, stt, enn⟩ := it
    simp only [physScanSpill] at hq
    rw [List.countP_cons] at hB
    dsimp only at hB
    refine ih _ _ _ B ?_ (physScanSpillStep_act_lt hact) ?_ q hq
    · have := physScanSpillStep_cells_le (numRegs := numRegs) (uses := uses) (act := act)
        (hulls := hulls) (acc := acc) (s := s) (st := stt) (en := enn) (reserved := reserved)
        (pieceOf := pieceOf)
      generalize physScanSpillStep numRegs uses act hulls acc s stt enn reserved pieceOf = r at this ⊢
      generalize r.2.1.size = k at *
      omega
    · refine physScanSpillStep_phys_lt_noPiece ?_ hact hacc
      omega

/-! ## 2″. The input of the scan with splitting -/

section SplitInput

variable {items : List (Nat × Nat × Nat)} {uses : Array Nat} {univ : Nat}
  {cands : List (Nat × Nat × Nat × Nat)}

/-- The items of the scan with splitting are a permutation of the items followed by the
    pieces. -/
theorem splitScanInput_perm :
    (splitScanInput items uses univ cands).1.Perm (items ++ splitIntervalPieces univ cands) := by
  simp only [splitScanInput, kernelMergeSort_eq]
  exact List.mergeSort_perm _ _

/-- A piece of the split is the interval of slot `univ + j` over the range of candidate
    `j`. -/
theorem mem_splitIntervalPieces {it : Nat × Nat × Nat} :
    it ∈ splitIntervalPieces univ cands
      ↔ ∃ j c, cands[j]? = some c ∧ it = (univ + j, c.2.1, c.2.2.1) := by
  simp only [splitIntervalPieces, List.mem_map]
  constructor
  · rintro ⟨⟨c, j⟩, hm, rfl⟩
    exact ⟨j, c, List.mem_zipIdx_iff_getElem?.mp hm, rfl⟩
  · rintro ⟨j, c, hc, rfl⟩
    exact ⟨(c, j), List.mem_zipIdx_iff_getElem?.mpr hc, rfl⟩

/-- No slot below `univ` is a piece. -/
theorem splitScanInput_parent_lt {s : Nat} (hs : s < univ) :
    (splitScanInput items uses univ cands).2.2 s = none := by
  simp only [splitScanInput]
  rw [ite_eq_right (by omega)]

/-- The slot `univ + j` of a piece is a piece. -/
theorem splitScanInput_parent_piece {j : Nat} {c : Nat × Nat × Nat × Nat}
    (h : cands[j]? = some c) :
    (splitScanInput items uses univ cands).2.2 (univ + j) = some c.1 := by
  simp only [splitScanInput, Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
  rw [List.getElem?_toArray, List.getElem?_map, h]
  rfl

/-- The items of the scan with splitting that are no pieces are the items, counted. -/
theorem splitScanInput_countP (hlt : ∀ it ∈ items, it.1 < univ) :
    (splitScanInput items uses univ cands).1.countP
        (fun it => ((splitScanInput items uses univ cands).2.2 it.1).isNone)
      = items.length := by
  rw [splitScanInput_perm.countP_eq, List.countP_append,
    List.countP_eq_length.mpr (fun it hit => by
      rw [splitScanInput_parent_lt (hlt it hit)]; rfl),
    List.countP_eq_zero.mpr (fun it hit => by
      obtain ⟨j, c, hc, rfl⟩ := mem_splitIntervalPieces.mp hit
      rw [splitScanInput_parent_piece hc]
      simp)]
  simp

/-- The range of a slot of the scan with splitting: `R s` below `univ`, and the range of
    candidate `s - univ` at a piece. -/
def splitRange (R : Nat → Nat × Nat) (univ : Nat) (cands : List (Nat × Nat × Nat × Nat))
    (s : Nat) : Nat × Nat :=
  if s < univ then R s
  else match cands[s - univ]? with
    | some c => (c.2.1, c.2.2.1)
    | none => (0, 0)

/-- Every item of the scan with splitting carries its `splitRange`. -/
theorem splitScanInput_range {R : Nat → Nat × Nat} (hlt : ∀ it ∈ items, it.1 < univ)
    (hR : ∀ it ∈ items, R it.1 = (it.2.1, it.2.2)) :
    ∀ it ∈ (splitScanInput items uses univ cands).1,
      splitRange R univ cands it.1 = (it.2.1, it.2.2) := by
  intro it hit
  rcases List.mem_append.mp (splitScanInput_perm.mem_iff.mp hit) with h | h
  · rw [splitRange, ite_eq_left (hlt it h)]
    exact hR it h
  · obtain ⟨j, c, hc, rfl⟩ := mem_splitIntervalPieces.mp h
    simp only [splitRange, Nat.not_lt.mpr (Nat.le_add_right univ j), ite_false,
      Nat.add_sub_cancel_left, hc]

/-- The items of the scan with splitting meet the scan's input contract. -/
theorem splitScanInput_sorted (hlt : ∀ it ∈ items, it.1 < univ)
    (hnd : items.Pairwise (fun a b => ¬ a.1 = b.1)) :
    ItemsSorted (splitScanInput items uses univ cands).1 := by
  refine List.Pairwise.and ?_ ?_
  · simp only [splitScanInput, kernelMergeSort_eq]
    refine (List.pairwise_mergeSort liveCmp_trans liveCmp_total _).imp ?_
    intro a b h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    omega
  · refine (splitScanInput_perm.pairwise_iff (fun h he => h he.symm)).mpr ?_
    refine List.pairwise_append.mpr ⟨hnd, ?_, ?_⟩
    · rw [List.pairwise_iff_getElem]
      intro i k hi hk hik
      simp only [splitIntervalPieces, List.getElem_map, List.getElem_zipIdx]
      omega
    · intro a ha b hb
      obtain ⟨j, c, -, rfl⟩ := mem_splitIntervalPieces.mp hb
      have := hlt a ha
      simp only []
      omega

end SplitInput

/-! ## 3. The class-aware assignment separates overlapping live slots -/

/-- The candidate pieces of the general-purpose slots of `tr` under `cfg`. -/
def gpCands (tr : List PhysEvent) (vecArr : Array Bool) (cfg : SplitCfg) :
    List (Nat × Nat × Nat × Nat) :=
  (splitCands tr (physUniverse tr) cfg).filter (fun c => !slotIsVec vecArr c.1)

/-- The input of the general-purpose scan with splitting under `cfg`. -/
def gpSplitInput (tr : List PhysEvent) (vecArr : Array Bool) (cfg : SplitCfg) :
    List (Nat × Nat × Nat) × Array Nat × (Nat → Option Nat) :=
  splitScanInput ((physLiveItems tr).filter (fun it => !slotIsVec vecArr it.1))
    (physLiveData tr).2 (physUniverse tr) (gpCands tr vecArr cfg)

/-- The GP half of the class-aware assignment: the linear scan over the live
    items of GP class, over the GP pool less `reserved`; at a split configuration, the scan
    over those items and the candidate pieces of the GP slots (`gpSplitInput`). -/
def gpHalf (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved : List Nat) (split : Option SplitCfg := none) : List (Nat × Nat) :=
  match split with
  | none =>
      physScanSpill numGPRegs (physLiveData tr).2
        ((physLiveItems tr).filter (fun it => !slotIsVec vecArr it.1)) [] #[] [] reserved
  | some cfg =>
      physScanSpill numGPRegs (gpSplitInput tr vecArr cfg).2.1 (gpSplitInput tr vecArr cfg).1
        [] #[] [] reserved (gpSplitInput tr vecArr cfg).2.2

/-- The vector half of the class-aware assignment, before the `vectorBase`
    offset, over the vector pool less `reservedVec`. -/
def vecHalf (tr : List PhysEvent) (vecArr : Array Bool)
    (reservedVec : List Nat) : List (Nat × Nat) :=
  physScanSpill numVecRegs (physLiveData tr).2
    ((physLiveItems tr).filter (fun it => slotIsVec vecArr it.1)) [] #[] [] reservedVec

/-- The class-aware assignment is the GP half followed by the offset vector
    half. -/
theorem physAssignClassed_eq (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved reservedVec : List Nat) (split : Option SplitCfg) :
    physAssignClassed tr vecArr reserved reservedVec x86Abi split
      = gpHalf tr vecArr reserved split
        ++ (vecHalf tr vecArr reservedVec).map (fun q => (q.1, q.2 + vectorBase)) := by
  cases split <;> rfl

/-- Filtering keeps the scan's input contract. -/
theorem itemsSorted_filter {items : List (Nat × Nat × Nat)}
    (h : ItemsSorted items) (p : Nat × Nat × Nat → Bool) : ItemsSorted (items.filter p) :=
  List.Pairwise.sublist (List.filter_sublist) h

/-- Each half's item list carries each slot's `physLiveRange`. -/
theorem filter_range (tr : List PhysEvent) (p : Nat × Nat × Nat → Bool) :
    ∀ it ∈ (physLiveItems tr).filter p, physLiveRange tr it.1 = (it.2.1, it.2.2) :=
  fun it hit => physLiveItems_range tr it (List.mem_filter.mp hit).1

/-- Every live item is a slot of the universe. -/
theorem physLiveItems_lt (tr : List PhysEvent) :
    ∀ it ∈ physLiveItems tr, it.1 < physUniverse tr := by
  intro it hit
  simp only [physLiveItems, physLiveData, kernelMergeSort_eq] at hit
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filterMap] at hit
  obtain ⟨a, ha, hfa⟩ := hit
  split at hfa
  · cases hfa
    exact List.mem_range.mp ha
  · cases hfa

/-- The GP items of a filter of the live items are slots of the universe. -/
theorem filter_lt (tr : List PhysEvent) (p : Nat × Nat × Nat → Bool) :
    ∀ it ∈ (physLiveItems tr).filter p, it.1 < physUniverse tr :=
  fun it hit => physLiveItems_lt tr it (List.mem_filter.mp hit).1

/-- The GP half's physical indices stay below `vectorBase`, given that the live
    item count leaves room for one stack cell per item. -/
theorem gpHalf_lt_vectorBase {tr : List PhysEvent} {vecArr : Array Bool}
    {reserved : List Nat} {split : Option SplitCfg}
    (hfit : numGPRegs + (physLiveItems tr).length ≤ vectorBase) :
    ∀ q ∈ gpHalf tr vecArr reserved split, q.2 < vectorBase := by
  have := List.length_filter_le (fun it => !slotIsVec vecArr it.1) (physLiveItems tr)
  cases split with
  | none =>
    refine physScanSpill_phys_lt numGPRegs (physLiveData tr).2 reserved _ [] #[] []
      vectorBase ?_ (by simp) (by simp)
    simpa using by omega
  | some cfg =>
    refine physScanSpill_phys_lt_noPiece numGPRegs _ reserved _ [] #[] [] vectorBase ?_
      (by simp) (by simp)
    rw [gpSplitInput, splitScanInput_countP (filter_lt tr _)]
    simpa using by omega

/-- A GP-half location is below `vectorBase`. -/
theorem gpHalf_physLoc_lt {tr : List PhysEvent} {vecArr : Array Bool} {t p : Nat}
    {reserved : List Nat} {split : Option SplitCfg}
    (hfit : numGPRegs + (physLiveItems tr).length ≤ vectorBase)
    (h : physLoc (gpHalf tr vecArr reserved split) t = some p) : p < vectorBase := by
  unfold physLoc at h
  cases hf : (gpHalf tr vecArr reserved split).find? (fun q => q.1 == t) with
  | some q =>
    rw [hf] at h
    have : q.2 = p := by simpa using h
    exact this ▸ gpHalf_lt_vectorBase hfit q (List.mem_of_find?_eq_some hf)
  | none => rw [hf] at h; exact absurd h (by simp)

/-- The GP half is collision-free on the slots of the universe: two distinct slots whose
    live ranges overlap never get the same location. -/
theorem gpHalf_no_collision (tr : List PhysEvent) (vecArr : Array Bool) (reserved : List Nat)
    (split : Option SplitCfg) {t₁ t₂ p : Nat} (hne : t₁ ≠ t₂)
    (hu1 : t₁ < physUniverse tr) (hu2 : t₂ < physUniverse tr)
    (h1 : physLoc (gpHalf tr vecArr reserved split) t₁ = some p)
    (h2 : physLoc (gpHalf tr vecArr reserved split) t₂ = some p) :
    ¬ physRangesOverlap (physLiveRange tr t₁) (physLiveRange tr t₂) := by
  cases split with
  | none =>
    exact physScanSpill_no_collision numGPRegs (physLiveData tr).2 reserved
      (physLiveRange tr) _
      (itemsSorted_filter (physLiveItems_sorted tr) _) (filter_range tr _) hne h1 h2
  | some cfg =>
    have h := physScanSpill_no_collision numGPRegs _ reserved
      (splitRange (physLiveRange tr) (physUniverse tr) (gpCands tr vecArr cfg)) _
      (splitScanInput_sorted (filter_lt tr _)
        ((physLiveItems_slots_nodup tr).sublist List.filter_sublist))
      (splitScanInput_range (filter_lt tr _) (filter_range tr _)) hne h1 h2
    simpa only [splitRange, hu1, hu2, ↓reduceIte] using h

/-- **The class-aware assignment is collision-free.** Two distinct slots of the universe
    whose conservative live ranges overlap never receive the same physical index from
    `physAssignClassed`, at every split configuration: the GP scan and the vector scan are
    each collision-free on their own item list, and the `vectorBase` offset keeps the two
    pools apart. -/
theorem physAssignClassed_no_collision (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved reservedVec : List Nat)
    (hfit : numGPRegs + (physLiveItems tr).length ≤ vectorBase)
    {t₁ t₂ p : Nat} (hne : t₁ ≠ t₂) {split : Option SplitCfg}
    (hu1 : t₁ < physUniverse tr) (hu2 : t₂ < physUniverse tr)
    (h1 : physLoc (physAssignClassed tr vecArr reserved reservedVec x86Abi split) t₁ = some p)
    (h2 : physLoc (physAssignClassed tr vecArr reserved reservedVec x86Abi split) t₂ = some p) :
    ¬ physRangesOverlap (physLiveRange tr t₁) (physLiveRange tr t₂) := by
  rw [physAssignClassed_eq] at h1 h2
  cases hg1 : physLoc (gpHalf tr vecArr reserved split) t₁ with
  | some p₁ =>
    rw [physLoc_append_of_left hg1] at h1
    cases h1
    cases hg2 : physLoc (gpHalf tr vecArr reserved split) t₂ with
    | some p₂ =>
      rw [physLoc_append_of_left hg2] at h2
      cases h2
      exact gpHalf_no_collision tr vecArr reserved split hne hu1 hu2 hg1 hg2
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
      cases hg2 : physLoc (gpHalf tr vecArr reserved split) t₂ with
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

/-- Every live GP item gets a location from the GP half, at every split configuration. -/
theorem gpHalf_physLoc_live (tr : List PhysEvent) (vecArr : Array Bool) (reserved : List Nat)
    (split : Option SplitCfg) {it : Nat × Nat × Nat}
    (hit : it ∈ (physLiveItems tr).filter (fun i => !slotIsVec vecArr i.1)) :
    physLoc (gpHalf tr vecArr reserved split) it.1 ≠ none := by
  cases split with
  | none => exact physScanSpill_assigns numGPRegs (physLiveData tr).2 reserved _ [] #[] [] it hit rfl
  | some cfg =>
    exact physScanSpill_assigns numGPRegs _ reserved _ [] #[] [] it
      (splitScanInput_perm.mem_iff.mpr (List.mem_append_left _ hit))
      (splitScanInput_parent_lt (filter_lt tr _ it hit))

/-- Every live slot gets a location from the class-aware assignment: it is an
    item of the scan of its own class, and that scan assigns every item. -/
theorem physAssignClassed_physLoc_live (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved reservedVec : List Nat) {s : Nat} {split : Option SplitCfg}
    (hs : ∃ it ∈ physLiveItems tr, it.1 = s) :
    physLoc (physAssignClassed tr vecArr reserved reservedVec x86Abi split) s ≠ none := by
  obtain ⟨it, hit, rfl⟩ := hs
  rw [physAssignClassed_eq]
  by_cases hv : slotIsVec vecArr it.1
  · have hmem : it ∈ (physLiveItems tr).filter (fun i => slotIsVec vecArr i.1) :=
      List.mem_filter.mpr ⟨hit, by simpa using hv⟩
    have hvloc : physLoc (vecHalf tr vecArr reservedVec) it.1 ≠ none :=
      physScanSpill_assigns numVecRegs (physLiveData tr).2 reservedVec _ [] #[] [] it hmem rfl
    cases hg : physLoc (gpHalf tr vecArr reserved split) it.1 with
    | some p => rw [physLoc_append_of_left hg]; simp
    | none =>
      rw [physLoc_append_of_none hg, physLoc_map_add]
      cases hvv : physLoc (vecHalf tr vecArr reservedVec) it.1 with
      | some q => simp
      | none => exact absurd hvv hvloc
  · have hmem : it ∈ (physLiveItems tr).filter (fun i => !slotIsVec vecArr i.1) :=
      List.mem_filter.mpr ⟨hit, by simpa using hv⟩
    have hgloc := gpHalf_physLoc_live tr vecArr reserved split hmem
    cases hg : physLoc (gpHalf tr vecArr reserved split) it.1 with
    | some p => rw [physLoc_append_of_left hg]; simp
    | none => exact absurd hg hgloc

/-! ## 4. The lookup table reports the assignment -/

/-- `physMapTabled` over the class-aware table reports the location the
    class-aware assignment recorded, on the slot universe. -/
theorem physMapTabled_physTableClassed_of_physLoc {tr : List PhysEvent} {vecArr : Array Bool}
    {reserved reservedVec : List Nat} {split : Option SplitCfg}
    {s p : Nat} (hs : s < physUniverse tr)
    (h : physLoc (physAssignClassed tr vecArr reserved reservedVec x86Abi split) s = some p) :
    physMapTabled (physTableClassed tr vecArr reserved reservedVec x86Abi split) s = p := by
  unfold physMapTabled physTableClassed physLoc at *
  rw [Array.getElem?_map, Array.getElem?_range]
  simp only [hs, ↓reduceIte, Option.map_some, Option.getD_some]
  cases hf : (physAssignClassed tr vecArr reserved reservedVec x86Abi split).find?
      (fun q => q.1 == s) with
  | some q => rw [hf] at h; simpa using h
  | none => rw [hf] at h; exact absurd h (by simp)

/-- **The shipped table separates overlapping live slots.** Two distinct live
    slots of `tr` whose ranges overlap get distinct entries in
    `physTableClassed`, at every split configuration. -/
theorem physTableClassed_no_collision (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved reservedVec : List Nat)
    (hfit : numGPRegs + (physLiveItems tr).length ≤ vectorBase)
    {t₁ t₂ : Nat} (hne : t₁ ≠ t₂)
    (hu1 : t₁ < physUniverse tr) (hu2 : t₂ < physUniverse tr)
    (hl1 : ∃ it ∈ physLiveItems tr, it.1 = t₁)
    (hl2 : ∃ it ∈ physLiveItems tr, it.1 = t₂)
    (hov : physRangesOverlap (physLiveRange tr t₁) (physLiveRange tr t₂))
    {split : Option SplitCfg} :
    physMapTabled (physTableClassed tr vecArr reserved reservedVec x86Abi split) t₁
      ≠ physMapTabled (physTableClassed tr vecArr reserved reservedVec x86Abi split) t₂ := by
  intro heq
  cases h1 : physLoc (physAssignClassed tr vecArr reserved reservedVec x86Abi split) t₁ with
  | none => exact physAssignClassed_physLoc_live tr vecArr reserved reservedVec hl1 h1
  | some p₁ =>
    cases h2 : physLoc (physAssignClassed tr vecArr reserved reservedVec x86Abi split) t₂ with
    | none => exact physAssignClassed_physLoc_live tr vecArr reserved reservedVec hl2 h2
    | some p₂ =>
      have e1 := physMapTabled_physTableClassed_of_physLoc (vecArr := vecArr) hu1 h1
      have e2 := physMapTabled_physTableClassed_of_physLoc (vecArr := vecArr) hu2 h2
      have hpp : p₁ = p₂ := by rw [← e1, ← e2]; exact heq
      subst hpp
      exact physAssignClassed_no_collision tr vecArr reserved reservedVec hfit hne hu1 hu2 h1 h2
        hov

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
  exact ⟨s, List.mem_range.mpr hs, by simp only [hst, ite_eq_left]⟩

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
