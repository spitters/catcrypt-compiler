/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary

/-!
# Allocation facts for `CoverData`: the bounded linear scan assigns distinct locations

`ToLprogFaithfulNary.physBody_lsem_result_uniform` is unconditional in
`BodyCover` for an arbitrary-length `UniformRegArith` `Com`, given a threaded
`CoverData` whose per-binding payload carries the two head-naming facts and the
RA-correctness facts `hcol` (two-address collapse) and `hinj` (renaming
injectivity, inside each `BinopBinding`). This module characterizes the shipped
allocator (`physScanSpillStep` / `physScanSpill` / `physAssign` / `physMap`,
`JasminLprogExport.lean` §7c) and proves that it never gives two overlapping
live ranges the same physical location.

## The allocator

`physMap tr s` looks `s` up in `physAssign tr`, which runs `physScanSpill` — a
Poletto–Sarkar linear scan over a bounded pool of `numGPRegs` registers with a
separate pool of stack cells. Each live interval is one `physScanSpillStep`: the
register allocations whose range ended are reclaimed, and the interval takes the
lowest free register (`freeRegIn`). When no register is free, `spillVictim` ranks
the register-resident values by spill cost, the winner is compared against the
incoming interval, and the higher-ranked of the two goes to a stack cell for its
**whole** range (`allocCell`). Each cell carries the `(minStart, maxEnd)` hull of
every range placed in it, and `firstFittingCell` admits a range only into a cell
whose hull is disjoint from it.

**Consequence for `hcol`.** The step does not prefer a binding's first source
`s0`'s register for its destination `dst` — it takes the lowest free register, so
`hcol` (`physRename dst = physRename s0`) is a derived side-condition, not a
structural fact. The lowering is robust to its failure (the collapse-or-mov
dichotomy, §5).

**Consequence for `hinj`.** `physMap` is deliberately not globally injective: it
reuses a location across slots whose live ranges do not overlap. Injectivity
holds exactly on slots whose ranges overlap, which is what §4 proves.

## What this module proves

* **§1 `physLoc`, overlap arithmetic.** The location a slot reads back out of an
  assignment list, and the three arithmetic facts the invariant needs
  (`physRangesOverlap_comm`, `not_overlap_of_end_lt`, `not_overlap_of_hull`).

* **§2 the cell pool.** `firstFittingCell_disjoint` (the cell `allocCell` picks
  has a hull disjoint from the incoming range), `allocCell_covers` (the chosen
  cell's hull covers the range after the placement) and `allocCell_mono` (the
  placement only widens hulls). These are the facts that make cell reuse safe
  against the *whole* range of a spilled value rather than against the values
  live at the spill point.

* **§3 `ScanInv`.** The running invariant: the in-flight register allocations sit
  on distinct in-pool registers and agree with the assignment list; every
  register-located slot is either still in flight or already dead; every
  cell-located slot's range is inside its cell's hull; and no two distinct slots
  with the same location have overlapping ranges. `inv_take_reg`,
  `inv_evict` and `inv_spill_incoming` re-establish it for the three arms of
  `physScanSpillStep`; `physScanSpillStep_ScanInv` assembles them and
  `physScanSpill_ScanInv` threads it over the whole scan.

* **§4 `physScanSpill_no_collision` / `physAssign_no_collision` /
  `physMap_no_collision`.** For two distinct slots whose live ranges overlap, the
  scan assigns different physical locations — registers and stack cells alike.
  `physLiveItems_sorted` and `physLiveItems_range` discharge the scan's input
  hypotheses (starts non-decreasing, slots distinct, ranges agreeing with
  `physLiveRange`) for the shipped item list, so `physAssign_no_collision` and
  `physMap_no_collision` are hypothesis-free in the trace.

* **§5 `lowerTwoAddr_dichotomy` / `lowerTwoAddr_collapse_of_eq`.** The
  collapse-or-mov dichotomy: `lowerTwoAddr` is exactly the collapse form when the
  physical `dst = s0`, and the `legalizeMov`-prefixed form otherwise. So `hcol`
  selects the collapse branch; its negation routes through the already-discharged
  `legalizeMov` prefix. `hcol` is never required — it is an optimization the RA
  may or may not enable, and the lowering is faithful either way.

* **§6 `physRegName_injOn_gp` / `physRegName_gp_ne_spill` /
  `physRegName_injOn_spill` / `physRegName_inj`.** The rendering layer of `hinj`,
  global: `physRegName` is injective on the GP-register block (via
  `gpRegNames_nodup`), never confuses a GP index with a spill index, and is
  injective on the spill block — the last bottoming out in the decimal-string
  injectivity `toDigits_inj`/`toString_nat_inj` (proved here from the Batteries
  `Nat.toDigits` recurrence; Mathlib/Batteries has no `Nat.repr` injectivity
  lemma).

* **§6 `nameSlot_injOn`.** The naming layer of `hinj`, on the live set:
  `nameSlot body n = (bodyNames body).idxOf n` is injective on names that occur in
  the body (`List.getElem_idxOf` left inverse). It is not globally injective
  (absent names collapse to the sentinel slot), which is why `hinj` is
  live-set-scoped.

* **§7 `physRename_injOn_live`.** The composition: with the rendering layer
  (`physRegName_inj`, global) and the naming layer (`nameSlot_injOn`, live) both
  discharged, `hinj` reduces to the single slot-level fact that `physMapTabled
  tbl` is injective on the source/destination slots — which §4 supplies for
  `physTable`-shaped tables whose slots are live and overlapping.

## Residual

`physRename_injOn_live` takes the slot-level injectivity as the hypothesis
`hslot`. Feeding it from §4 for a concrete binding needs two facts about the
`Lcmd` layer that are not proved here: that `physMapTabled (physTable tr)` agrees
with `physMap tr` on the slots in range (a `physTable`-scatter fact), and that
the two slots of a binop's destination and source are live and have overlapping
`physLiveRange`s at that binding (a liveness fact about `physEvents`). Both are
statements about the trace `physEvents body` produces, not about the allocator.

§4 covers `physAssign`, the single-pool scan. `physAssignClassed` runs two
independent `physScanSpill` calls over the GP and vector item lists and
concatenates them with the vector indices offset by `vectorBase`; each scan
satisfies `physScanSpill_no_collision` on its own item list, but the argument
that the concatenation keeps the two pools apart is not carried out here.

`RegMachineSim.jinstr_renameBlock_sound` (`JInstrRegMachineSim.lean`:202) proves
per-block RA soundness for a uniform renaming `ρ` over the `JInstr 64`/`JState 64`
machine, under a global `Function.Injective ρ`. It does not transfer to
`physBody`/`Lstate` directly: `physBody` is not a uniform renaming (it interleaves
the two-address `mov`s and the spill reloads through `legalizeBinop`), and it
requires global injectivity while `physMap` is injective on overlapping slots
alone. So the missing bridge is the overlap-restricted re-proof of the
maintenance step over `Lstate` for the non-uniform `physBody` emission, which is
why `ToLprogFaithfulWriteSide` carries `hinj` as a per-block liveness hypothesis.
This module supplies the RA-side fact such a re-proof consumes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRA

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## 1. Locations and overlap arithmetic

`physAssign` accumulates `(slot, phys)` pairs most-recent-first, and both
`physMap` and `physTable` read a slot's location with `find?`. `physLoc` names
that read. -/

/-- The physical location an assignment list gives a slot, `none` when the slot
    was never assigned. -/
def physLoc (acc : List (Nat × Nat)) (s : Nat) : Option Nat :=
  (acc.find? (fun p => p.1 == s)).map Prod.snd

@[simp] theorem physLoc_nil (s : Nat) : physLoc [] s = none := rfl

/-- A newer assignment shadows the rest of the list. -/
theorem physLoc_cons (a b : Nat) (acc : List (Nat × Nat)) (s : Nat) :
    physLoc ((a, b) :: acc) s = if a = s then some b else physLoc acc s := by
  unfold physLoc
  rw [List.find?_cons]
  by_cases h : a = s
  · simp [h]
  · have hb : (a == s) = false := by simpa using h
    simp [hb, h]

/-- Range overlap is symmetric. -/
theorem physRangesOverlap_comm (r1 r2 : Nat × Nat) :
    physRangesOverlap r1 r2 = physRangesOverlap r2 r1 := by
  simp [physRangesOverlap, Bool.and_comm]

/-- A range that ended before `st` does not overlap `[st, en]`. -/
theorem not_overlap_of_end_lt {r : Nat × Nat} {st en : Nat} (h : r.2 < st) :
    ¬ physRangesOverlap r (st, en) := by
  simp only [physRangesOverlap, Bool.and_eq_true, decide_eq_true_eq, not_and]
  omega

/-- A range inside a hull inherits the hull's disjointness. -/
theorem not_overlap_of_hull {r h R : Nat × Nat} (hlo : h.1 ≤ r.1) (hhi : r.2 ≤ h.2)
    (hd : ¬ physRangesOverlap h R) : ¬ physRangesOverlap r R := by
  simp only [physRangesOverlap, Bool.and_eq_true, decide_eq_true_eq, not_and] at hd ⊢
  omega

/-! ## 2. The cell pool

Cell reuse is decided against a cell's hull, so what the placement guarantees is
disjointness from the hull, and the hull covers every range placed in the cell.
Together those give pairwise disjointness of the ranges sharing a cell. -/

/-- An index with an element is inside the array. -/
theorem lt_size_of_getElem? {α : Type} {a : Array α} {j : Nat} {x : α}
    (h : a[j]? = some x) : j < a.size := by
  rcases Nat.lt_or_ge j a.size with hj | hj
  · exact hj
  · rw [Array.getElem?_eq_none hj] at h
    exact absurd h (by simp)

/-- `firstFittingCell` scanning from `i ≤ hulls.size` stops at `hulls.size` at the
    latest. -/
theorem firstFittingCell_le (hulls : CellHulls) (st en : Nat) :
    ∀ (n i : Nat), hulls.size - i ≤ n → i ≤ hulls.size →
      firstFittingCell hulls st en i ≤ hulls.size := by
  intro n
  induction n with
  | zero =>
    intro i hn hi
    rw [firstFittingCell]
    have : ¬ i < hulls.size := by omega
    simp [this, hi]
  | succ n ih =>
    intro i hn hi
    rw [firstFittingCell]
    by_cases hlt : i < hulls.size
    · simp only [hlt, dite_eq_left]
      by_cases hov : physRangesOverlap hulls[i] (st, en)
      · simp only [hov, ite_eq_left]
        exact ih (i + 1) (by omega) (by omega)
      · simp only [hov, Bool.false_eq_true, ite_eq_right, not_false_iff]
        omega
    · simp [hlt, hi]

/-- When `firstFittingCell` stops at an existing cell, that cell's hull is
    disjoint from `[st, en]`. -/
theorem firstFittingCell_disjoint (hulls : CellHulls) (st en : Nat) :
    ∀ (n i : Nat), hulls.size - i ≤ n →
      ∀ h, hulls[firstFittingCell hulls st en i]? = some h →
        ¬ physRangesOverlap h (st, en) := by
  intro n
  induction n with
  | zero =>
    intro i hn h hh
    rw [firstFittingCell] at hh
    have hge : ¬ i < hulls.size := by omega
    simp only [hge, dite_eq_right, not_false_iff] at hh
    rw [Array.getElem?_eq_none (by omega)] at hh
    exact absurd hh (by simp)
  | succ n ih =>
    intro i hn h hh
    rw [firstFittingCell] at hh
    by_cases hlt : i < hulls.size
    · simp only [hlt, dite_eq_left] at hh
      by_cases hov : physRangesOverlap hulls[i] (st, en)
      · simp only [hov, ite_eq_left] at hh
        exact ih (i + 1) (by omega) h hh
      · simp only [hov, Bool.false_eq_true, ite_eq_right, not_false_iff] at hh
        rw [Array.getElem?_eq_getElem hlt] at hh
        cases hh
        exact hov
    · simp only [hlt, dite_eq_right, not_false_iff] at hh
      rw [Array.getElem?_eq_none (by omega)] at hh
      exact absurd hh (by simp)

/-- The cell index `allocCell` returns. -/
theorem allocCell_fst (hulls : CellHulls) (st en : Nat) :
    (allocCell hulls st en).1 = firstFittingCell hulls st en 0 := by
  simp only [allocCell]
  split <;> rfl

/-- The cell `allocCell` places `[st, en]` into had a hull disjoint from it. -/
theorem allocCell_disjoint (hulls : CellHulls) (st en : Nat) (h : Nat × Nat)
    (hh : hulls[(allocCell hulls st en).1]? = some h) :
    ¬ physRangesOverlap h (st, en) := by
  rw [allocCell_fst] at hh
  exact firstFittingCell_disjoint hulls st en hulls.size 0 (by omega) h hh

/-- After the placement the chosen cell's hull covers `[st, en]`. -/
theorem allocCell_covers (hulls : CellHulls) (st en : Nat) :
    ∃ h', (allocCell hulls st en).2[(allocCell hulls st en).1]? = some h'
      ∧ h'.1 ≤ st ∧ en ≤ h'.2 := by
  simp only [allocCell]
  cases hc : hulls[firstFittingCell hulls st en 0]? with
  | some c =>
    refine ⟨(Nat.min c.1 st, Nat.max c.2 en), ?_, Nat.min_le_right _ _, Nat.le_max_right _ _⟩
    have hlt : firstFittingCell hulls st en 0 < hulls.size := lt_size_of_getElem? hc
    simp [Array.set!, hlt]
  | none =>
    refine ⟨(st, en), ?_, Nat.le_refl _, Nat.le_refl _⟩
    have hge : hulls.size ≤ firstFittingCell hulls st en 0 := by
      rcases Nat.lt_or_ge (firstFittingCell hulls st en 0) hulls.size with hlt | hge
      · rw [Array.getElem?_eq_getElem hlt] at hc; exact absurd hc (by simp)
      · exact hge
    have hle : firstFittingCell hulls st en 0 ≤ hulls.size :=
      firstFittingCell_le hulls st en hulls.size 0 (by omega) (by omega)
    have heq : firstFittingCell hulls st en 0 = hulls.size := by omega
    rw [heq]
    exact Array.getElem?_push_size

/-- A placement only widens the existing hulls. -/
theorem allocCell_mono (hulls : CellHulls) (st en : Nat) (j : Nat) (h : Nat × Nat)
    (hj : hulls[j]? = some h) :
    ∃ h', (allocCell hulls st en).2[j]? = some h' ∧ h'.1 ≤ h.1 ∧ h.2 ≤ h'.2 := by
  simp only [allocCell]
  cases hc : hulls[firstFittingCell hulls st en 0]? with
  | some c =>
    have hlt : firstFittingCell hulls st en 0 < hulls.size := lt_size_of_getElem? hc
    by_cases hje : firstFittingCell hulls st en 0 = j
    · subst hje
      rw [hc] at hj
      have hhc : h = c := by simpa using hj.symm
      subst hhc
      exact ⟨(Nat.min h.1 st, Nat.max h.2 en),
        by simp [Array.set!, hlt],
        Nat.min_le_left _ _, Nat.le_max_left _ _⟩
    · exact ⟨h, by simp [Array.set!, hje, hj], Nat.le_refl _, Nat.le_refl _⟩
  | none =>
    refine ⟨h, ?_, Nat.le_refl _, Nat.le_refl _⟩
    have hjlt : j < hulls.size := lt_size_of_getElem? hj
    rw [Array.getElem?_push]
    have hne : ¬ j = hulls.size := by omega
    simp [hne, hj]

/-! ## 3. The scan invariant

`ScanInv numRegs rg pos act hulls acc` is the state the scan carries after
processing every interval that starts before `pos`: `act` are the register
allocations still in flight, `hulls` the cell hulls, `acc` the assignment list.
`rg` is the ground-truth live range of each slot. -/

/-- The state the bounded scan maintains. `noColl` is the property the allocation
    is for: distinct slots with the same physical location have disjoint ranges. -/
structure ScanInv (numRegs : Nat) (rg : Nat → Nat × Nat) (pos : Nat)
    (act : List PhysActive) (hulls : CellHulls) (acc : List (Nat × Nat)) : Prop where
  /-- In-flight allocations use pool registers. -/
  bound : ∀ a ∈ act, a.phys < numRegs
  /-- In-flight allocations hold pairwise-distinct registers. -/
  nodup : (act.map PhysActive.phys).Nodup
  /-- An in-flight allocation carries its slot's range. -/
  range : ∀ a ∈ act, rg a.slot = (a.st, a.en)
  /-- An in-flight allocation is what its slot reads back. -/
  actLoc : ∀ a ∈ act, physLoc acc a.slot = some a.phys
  /-- A register-located slot is either in flight or already dead. -/
  regLive : ∀ t ph, ph < numRegs → physLoc acc t = some ph →
    (∃ a ∈ act, a.slot = t ∧ a.phys = ph) ∨ (rg t).2 < pos
  /-- A cell-located slot's range is inside its cell's hull. -/
  cell : ∀ t i, physLoc acc t = some (numRegs + i) →
    ∃ h, hulls[i]? = some h ∧ h.1 ≤ (rg t).1 ∧ (rg t).2 ≤ h.2
  /-- Distinct slots sharing a location have disjoint ranges. -/
  noColl : ∀ t₁ t₂ p, t₁ ≠ t₂ → physLoc acc t₁ = some p → physLoc acc t₂ = some p →
    ¬ physRangesOverlap (rg t₁) (rg t₂)

/-- Distinct registers separate the in-flight allocations. -/
theorem phys_inj_of_nodup : ∀ {l : List PhysActive}, (l.map PhysActive.phys).Nodup →
    ∀ {a b : PhysActive}, a ∈ l → b ∈ l → a.phys = b.phys → a = b := by
  intro l
  induction l with
  | nil => intro _ a b ha; exact absurd ha (by simp)
  | cons c rest ih =>
    intro hnd a b ha hb hab
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (hab ▸ List.mem_map_of_mem hb') hnd.1
    · exact absurd (hab ▸ List.mem_map_of_mem ha') hnd.1
    · exact ih hnd.2 ha' hb' hab

/-- Reclaiming allocations keeps their registers distinct. -/
theorem nodup_phys_filter {l : List PhysActive} (p : PhysActive → Bool)
    (h : (l.map PhysActive.phys).Nodup) : ((l.filter p).map PhysActive.phys).Nodup :=
  h.sublist (List.filter_sublist.map PhysActive.phys)

/-- An allocation dropped by the reclamation filter ended before `st`. -/
theorem dead_of_not_filtered {act : List PhysActive} {st : Nat} {a : PhysActive}
    (hmem : a ∈ act) (h : a ∉ act.filter (fun a => a.en ≥ st)) : a.en < st := by
  rcases Nat.lt_or_ge a.en st with hlt | hge
  · exact hlt
  · exact absurd (List.mem_filter.mpr ⟨hmem, by simpa using hge⟩) h

/-- A slot on a register that no surviving allocation holds is dead at `st`. -/
theorem end_lt_of_no_live_holder {numRegs : Nat} {rg : Nat → Nat × Nat} {pos : Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    (inv : ScanInv numRegs rg pos act hulls acc) {st t ph : Nat}
    (hpos : pos ≤ st) (hph : ph < numRegs) (hloc : physLoc acc t = some ph)
    (hno : ∀ a ∈ act.filter (fun a => a.en ≥ st), ¬(a.slot = t ∧ a.phys = ph)) :
    (rg t).2 < st := by
  rcases inv.regLive t ph hph hloc with ⟨a, ha, hs, hp⟩ | hd
  · by_cases hf : a ∈ act.filter (fun a => a.en ≥ st)
    · exact absurd ⟨hs, hp⟩ (hno a hf)
    · have hlt : a.en < st := dead_of_not_filtered ha hf
      have hr : rg t = (a.st, a.en) := hs ▸ inv.range a ha
      rw [hr]; exact hlt
  · omega

/-- A dead range does not overlap an interval starting at `st`. -/
theorem not_overlap_dead_left {rg : Nat → Nat × Nat} {t s st en : Nat}
    (hrg : rg s = (st, en)) (hd : (rg t).2 < st) : ¬ physRangesOverlap (rg s) (rg t) := by
  rw [hrg, physRangesOverlap_comm]
  exact not_overlap_of_end_lt hd

/-- A dead range does not overlap an interval starting at `st`. -/
theorem not_overlap_dead_right {rg : Nat → Nat × Nat} {t s st en : Nat}
    (hrg : rg s = (st, en)) (hd : (rg t).2 < st) : ¬ physRangesOverlap (rg t) (rg s) := by
  rw [hrg]
  exact not_overlap_of_end_lt hd

/-! ### The three arms of one scan step -/

/-- The incoming interval takes a free register. -/
theorem inv_take_reg {numRegs : Nat} {rg : Nat → Nat × Nat} {pos : Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en ph : Nat} {reserved : List Nat}
    (inv : ScanInv numRegs rg pos act hulls acc)
    (hpos : pos ≤ st) (hrg : rg s = (st, en))
    (hact : ∀ a ∈ act, a.slot ≠ s)
    (hfr : freeRegIn numRegs
      ((act.filter (fun a => a.en ≥ st)).map PhysActive.phys) reserved = some ph) :
    ScanInv numRegs rg st
      (⟨st, en, ph, s⟩ :: act.filter (fun a => a.en ≥ st)) hulls ((s, ph) :: acc) := by
  have hphlt : ph < numRegs := freeRegIn_lt hfr
  have hfree : ph ∉ (act.filter (fun a => a.en ≥ st)).map PhysActive.phys :=
    freeRegIn_not_mem hfr
  have hdead : ∀ t, physLoc acc t = some ph → (rg t).2 < st := by
    intro t hloc
    refine end_lt_of_no_live_holder inv hpos hphlt hloc ?_
    intro a ha hcon
    exact hfree (hcon.2 ▸ List.mem_map_of_mem ha)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hphlt
    · exact inv.bound a (List.mem_filter.mp ha').1
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨hfree, nodup_phys_filter _ inv.nodup⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hrg
    · exact inv.range a (List.mem_filter.mp ha').1
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [physLoc_cons, ite_eq_left rfl]
    · have hne : ¬ s = a.slot := fun h => hact a (List.mem_filter.mp ha').1 h.symm
      rw [physLoc_cons, ite_eq_right hne]
      exact inv.actLoc a (List.mem_filter.mp ha').1
  · intro t ph' hph' hloc
    rw [physLoc_cons] at hloc
    by_cases hts : s = t
    · subst hts
      exact Or.inl ⟨⟨st, en, ph, s⟩, List.mem_cons_self, rfl, by simp at hloc; omega⟩
    · rw [ite_eq_right hts] at hloc
      rcases inv.regLive t ph' hph' hloc with ⟨a, ha, hs, hp⟩ | hd
      · by_cases hf : a ∈ act.filter (fun a => a.en ≥ st)
        · exact Or.inl ⟨a, List.mem_cons_of_mem _ hf, hs, hp⟩
        · refine Or.inr ?_
          have hr : rg t = (a.st, a.en) := hs ▸ inv.range a ha
          rw [hr]
          exact dead_of_not_filtered ha hf
      · exact Or.inr (by omega)
  · intro t i hloc
    rw [physLoc_cons] at hloc
    by_cases hts : s = t
    · rw [ite_eq_left hts] at hloc
      exact absurd (by simpa using hloc) (by omega)
    · rw [ite_eq_right hts] at hloc
      exact inv.cell t i hloc
  · intro t₁ t₂ p hne h1 h2
    rw [physLoc_cons] at h1 h2
    by_cases h1s : s = t₁ <;> by_cases h2s : s = t₂
    · exact absurd (h1s ▸ h2s) hne
    · rw [ite_eq_left h1s] at h1
      rw [ite_eq_right h2s] at h2
      have hp : p = ph := by simpa using h1.symm
      subst hp
      subst h1s
      exact not_overlap_dead_left hrg (hdead t₂ h2)
    · rw [ite_eq_right h1s] at h1
      rw [ite_eq_left h2s] at h2
      have hp : p = ph := by simpa using h2.symm
      subst hp
      subst h2s
      exact not_overlap_dead_right hrg (hdead t₁ h1)
    · rw [ite_eq_right h1s] at h1
      rw [ite_eq_right h2s] at h2
      exact inv.noColl t₁ t₂ p hne h1 h2

/-- The incoming interval is the one that goes to a stack cell. -/
theorem inv_spill_incoming {numRegs : Nat} {rg : Nat → Nat × Nat} {pos : Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en : Nat}
    (inv : ScanInv numRegs rg pos act hulls acc)
    (hpos : pos ≤ st) (hrg : rg s = (st, en))
    (hact : ∀ a ∈ act, a.slot ≠ s) :
    ScanInv numRegs rg st (act.filter (fun a => a.en ≥ st))
      (allocCell hulls st en).2
      ((s, numRegs + (allocCell hulls st en).1) :: acc) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; exact inv.bound a (List.mem_filter.mp ha).1
  · exact nodup_phys_filter _ inv.nodup
  · intro a ha; exact inv.range a (List.mem_filter.mp ha).1
  · intro a ha
    have hne : ¬ s = a.slot := fun h => hact a (List.mem_filter.mp ha).1 h.symm
    rw [physLoc_cons, ite_eq_right hne]
    exact inv.actLoc a (List.mem_filter.mp ha).1
  · intro t ph hph hloc
    rw [physLoc_cons] at hloc
    by_cases hts : s = t
    · rw [ite_eq_left hts] at hloc
      exact absurd (by simpa using hloc) (by omega)
    · rw [ite_eq_right hts] at hloc
      rcases inv.regLive t ph hph hloc with ⟨a, ha, hs, hp⟩ | hd
      · by_cases hf : a ∈ act.filter (fun a => a.en ≥ st)
        · exact Or.inl ⟨a, hf, hs, hp⟩
        · refine Or.inr ?_
          have hr : rg t = (a.st, a.en) := hs ▸ inv.range a ha
          rw [hr]
          exact dead_of_not_filtered ha hf
      · exact Or.inr (by omega)
  · intro t i hloc
    rw [physLoc_cons] at hloc
    by_cases hts : s = t
    · rw [ite_eq_left hts] at hloc
      have hi : (allocCell hulls st en).1 = i := by simpa using hloc
      obtain ⟨h', hh', c1, c2⟩ := allocCell_covers hulls st en
      rw [hi] at hh'
      exact ⟨h', hh', by rw [← hts, hrg]; exact c1, by rw [← hts, hrg]; exact c2⟩
    · rw [ite_eq_right hts] at hloc
      obtain ⟨h, hh, c1, c2⟩ := inv.cell t i hloc
      obtain ⟨h', hh', m1, m2⟩ := allocCell_mono hulls st en i h hh
      exact ⟨h', hh', by omega, by omega⟩
  · intro t₁ t₂ p hne h1 h2
    rw [physLoc_cons] at h1 h2
    by_cases h1s : s = t₁ <;> by_cases h2s : s = t₂
    · exact absurd (h1s ▸ h2s) hne
    · rw [ite_eq_left h1s] at h1
      rw [ite_eq_right h2s] at h2
      have hp : numRegs + (allocCell hulls st en).1 = p := by simpa using h1
      subst hp
      obtain ⟨h, hh, c1, c2⟩ := inv.cell t₂ (allocCell hulls st en).1 h2
      have hdis := allocCell_disjoint hulls st en h hh
      rw [← h1s, hrg, physRangesOverlap_comm]
      exact not_overlap_of_hull c1 c2 hdis
    · rw [ite_eq_right h1s] at h1
      rw [ite_eq_left h2s] at h2
      have hp : numRegs + (allocCell hulls st en).1 = p := by simpa using h2
      subst hp
      obtain ⟨h, hh, c1, c2⟩ := inv.cell t₁ (allocCell hulls st en).1 h1
      have hdis := allocCell_disjoint hulls st en h hh
      rw [← h2s, hrg]
      exact not_overlap_of_hull c1 c2 hdis
    · rw [ite_eq_right h1s] at h1
      rw [ite_eq_right h2s] at h2
      exact inv.noColl t₁ t₂ p hne h1 h2

/-- A register-resident value is evicted to a stack cell for its whole range and
    the incoming interval takes the register it vacates. -/
theorem inv_evict {numRegs : Nat} {rg : Nat → Nat × Nat} {pos : Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en : Nat} {far : PhysActive}
    (inv : ScanInv numRegs rg pos act hulls acc)
    (hpos : pos ≤ st) (hrg : rg s = (st, en))
    (hact : ∀ a ∈ act, a.slot ≠ s)
    (hfar : far ∈ act.filter (fun a => a.en ≥ st)) :
    ScanInv numRegs rg st
      (⟨st, en, far.phys, s⟩ ::
        (act.filter (fun a => a.en ≥ st)).filter (fun a => a.phys != far.phys))
      (allocCell hulls far.st far.en).2
      ((far.slot, numRegs + (allocCell hulls far.st far.en).1) ::
        (s, far.phys) :: acc) := by
  have hfarAct : far ∈ act := (List.mem_filter.mp hfar).1
  have hfarLt : far.phys < numRegs := inv.bound far hfarAct
  have hfarRg : rg far.slot = (far.st, far.en) := inv.range far hfarAct
  have hfarLoc : physLoc acc far.slot = some far.phys := inv.actLoc far hfarAct
  have hfarS : ¬ far.slot = s := hact far hfarAct
  have hndF : ((act.filter (fun a => a.en ≥ st)).map PhysActive.phys).Nodup :=
    nodup_phys_filter _ inv.nodup
  have hdeadFar : ∀ t, ¬ t = far.slot → physLoc acc t = some far.phys → (rg t).2 < st := by
    intro t htf hloc
    refine end_lt_of_no_live_holder inv hpos hfarLt hloc ?_
    intro a ha hcon
    have hafar : a = far := phys_inj_of_nodup hndF ha hfar hcon.2
    subst hafar
    exact htf hcon.1.symm
  have hslotFar : ∀ a ∈ act.filter (fun a => a.en ≥ st), ¬ a.phys = far.phys →
      ¬ a.slot = far.slot := by
    intro a ha hp hs
    exact hp (by
      have h1 := inv.actLoc a (List.mem_filter.mp ha).1
      rw [hs, hfarLoc] at h1
      simpa using h1.symm)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hfarLt
    · exact inv.bound a (List.mem_filter.mp (List.mem_filter.mp ha').1).1
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_phys_filter _ hndF⟩
    simp only [List.mem_map, not_exists, not_and]
    intro x hx hxp
    have hne := (List.mem_filter.mp hx).2
    simp [hxp] at hne
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hrg
    · exact inv.range a (List.mem_filter.mp (List.mem_filter.mp ha').1).1
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [physLoc_cons, ite_eq_right hfarS, physLoc_cons, ite_eq_left rfl]
    · have haf : a ∈ act.filter (fun a => a.en ≥ st) := (List.mem_filter.mp ha').1
      have hpne : ¬ a.phys = far.phys := by
        have := (List.mem_filter.mp ha').2
        simpa using this
      have h1 : ¬ far.slot = a.slot := fun h => hslotFar a haf hpne h.symm
      have h2 : ¬ s = a.slot := fun h => hact a (List.mem_filter.mp haf).1 h.symm
      rw [physLoc_cons, ite_eq_right h1, physLoc_cons, ite_eq_right h2]
      exact inv.actLoc a (List.mem_filter.mp haf).1
  · intro t ph hph hloc
    rw [physLoc_cons, physLoc_cons] at hloc
    by_cases hf1 : far.slot = t
    · rw [ite_eq_left hf1] at hloc
      exact absurd (by simpa using hloc) (by omega)
    · rw [ite_eq_right hf1] at hloc
      by_cases hs1 : s = t
      · rw [ite_eq_left hs1] at hloc
        refine Or.inl ⟨⟨st, en, far.phys, s⟩, List.mem_cons_self, hs1, ?_⟩
        simpa using hloc
      · rw [ite_eq_right hs1] at hloc
        rcases inv.regLive t ph hph hloc with ⟨a, ha, hs, hp⟩ | hd
        · by_cases hfl : a ∈ act.filter (fun a => a.en ≥ st)
          · by_cases hpf : a.phys = far.phys
            · have heq : a = far := phys_inj_of_nodup hndF hfl hfar hpf
              have hst : far.slot = t := by rw [← heq]; exact hs
              exact absurd hst hf1
            · refine Or.inl ⟨a, List.mem_cons_of_mem _ ?_, hs, hp⟩
              exact List.mem_filter.mpr ⟨hfl, by simpa using hpf⟩
          · refine Or.inr ?_
            have hr : rg t = (a.st, a.en) := hs ▸ inv.range a ha
            rw [hr]
            exact dead_of_not_filtered ha hfl
        · exact Or.inr (by omega)
  · intro t i hloc
    rw [physLoc_cons, physLoc_cons] at hloc
    by_cases hf1 : far.slot = t
    · rw [ite_eq_left hf1] at hloc
      have hi : (allocCell hulls far.st far.en).1 = i := by simpa using hloc
      obtain ⟨h', hh', c1, c2⟩ := allocCell_covers hulls far.st far.en
      rw [hi] at hh'
      exact ⟨h', hh', by rw [← hf1, hfarRg]; exact c1, by rw [← hf1, hfarRg]; exact c2⟩
    · rw [ite_eq_right hf1] at hloc
      by_cases hs1 : s = t
      · rw [ite_eq_left hs1] at hloc
        exact absurd (by simpa using hloc) (by omega)
      · rw [ite_eq_right hs1] at hloc
        obtain ⟨h, hh, c1, c2⟩ := inv.cell t i hloc
        obtain ⟨h', hh', m1, m2⟩ := allocCell_mono hulls far.st far.en i h hh
        exact ⟨h', hh', by omega, by omega⟩
  · intro t₁ t₂ p hne h1 h2
    rw [physLoc_cons, physLoc_cons] at h1 h2
    by_cases hf1 : far.slot = t₁
    · rw [ite_eq_left hf1] at h1
      by_cases hf2 : far.slot = t₂
      · exact absurd (hf1 ▸ hf2) hne
      · rw [ite_eq_right hf2] at h2
        by_cases hs2 : s = t₂
        · rw [ite_eq_left hs2] at h2
          have hcon : numRegs + (allocCell hulls far.st far.en).1 = far.phys := by
            simpa using h1.trans h2.symm
          exact absurd hcon (by omega)
        · rw [ite_eq_right hs2] at h2
          have hp : numRegs + (allocCell hulls far.st far.en).1 = p := by simpa using h1
          subst hp
          obtain ⟨h, hh, c1, c2⟩ := inv.cell t₂ (allocCell hulls far.st far.en).1 h2
          have hdis := allocCell_disjoint hulls far.st far.en h hh
          rw [← hf1, hfarRg, physRangesOverlap_comm]
          exact not_overlap_of_hull c1 c2 hdis
    · rw [ite_eq_right hf1] at h1
      by_cases hs1 : s = t₁
      · rw [ite_eq_left hs1] at h1
        by_cases hf2 : far.slot = t₂
        · rw [ite_eq_left hf2] at h2
          have hcon : far.phys = numRegs + (allocCell hulls far.st far.en).1 := by
            simpa using h1.trans h2.symm
          exact absurd hcon (by omega)
        · rw [ite_eq_right hf2] at h2
          by_cases hs2 : s = t₂
          · exact absurd (hs1 ▸ hs2) hne
          · rw [ite_eq_right hs2] at h2
            have hp : far.phys = p := by simpa using h1
            subst hp
            rw [← hs1]
            exact not_overlap_dead_left hrg (hdeadFar t₂ (fun h => hf2 h.symm) h2)
      · rw [ite_eq_right hs1] at h1
        by_cases hf2 : far.slot = t₂
        · rw [ite_eq_left hf2] at h2
          have hp : numRegs + (allocCell hulls far.st far.en).1 = p := by simpa using h2
          subst hp
          obtain ⟨h, hh, c1, c2⟩ := inv.cell t₁ (allocCell hulls far.st far.en).1 h1
          have hdis := allocCell_disjoint hulls far.st far.en h hh
          rw [← hf2, hfarRg]
          exact not_overlap_of_hull c1 c2 hdis
        · rw [ite_eq_right hf2] at h2
          by_cases hs2 : s = t₂
          · rw [ite_eq_left hs2] at h2
            have hp : far.phys = p := by simpa using h2
            subst hp
            rw [← hs2]
            exact not_overlap_dead_right hrg (hdeadFar t₁ (fun h => hf1 h.symm) h1)
          · rw [ite_eq_right hs2] at h2
            exact inv.noColl t₁ t₂ p hne h1 h2

/-- An interval that takes no location leaves the invariant at its start, with the ended
    allocations reclaimed. -/
theorem inv_skip {numRegs : Nat} {rg : Nat → Nat × Nat} {pos : Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)} {st : Nat}
    (inv : ScanInv numRegs rg pos act hulls acc) (hpos : pos ≤ st) :
    ScanInv numRegs rg st (act.filter (fun a => a.en ≥ st)) hulls acc := by
  refine ⟨?_, ?_, ?_, ?_, ?_, inv.cell, inv.noColl⟩
  · intro a ha; exact inv.bound a (List.mem_filter.mp ha).1
  · exact nodup_phys_filter _ inv.nodup
  · intro a ha; exact inv.range a (List.mem_filter.mp ha).1
  · intro a ha; exact inv.actLoc a (List.mem_filter.mp ha).1
  · intro t ph hph hloc
    rcases inv.regLive t ph hph hloc with ⟨a, ha, hs, hp⟩ | hd
    · by_cases hf : a ∈ act.filter (fun a => a.en ≥ st)
      · exact Or.inl ⟨a, hf, hs, hp⟩
      · refine Or.inr ?_
        have hr : rg t = (a.st, a.en) := hs ▸ inv.range a ha
        rw [hr]
        exact dead_of_not_filtered ha hf
    · exact Or.inr (by omega)

/-- The victim of a step is an allocation that survives the reclamation. -/
theorem victim_mem {st : Nat} {uses : Array Nat} {act : List PhysActive}
    {pieceOf : Nat → Option Nat} {far : PhysActive}
    (hv : spillVictim st uses ((act.filter (fun a => a.en ≥ st)).filter
      (fun a => (pieceOf a.slot).isNone)) = some far) :
    far ∈ act.filter (fun a => a.en ≥ st) :=
  (List.mem_filter.mp (spillVictim_mem hv)).1

/-! ### One step and the whole scan -/

/-- One `physScanSpillStep` re-establishes `ScanInv` at the interval's start. -/
theorem physScanSpillStep_ScanInv {numRegs : Nat} {uses : Array Nat}
    {rg : Nat → Nat × Nat} {pos : Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en : Nat} {reserved : List Nat} {pieceOf : Nat → Option Nat}
    (inv : ScanInv numRegs rg pos act hulls acc)
    (hpos : pos ≤ st) (hrg : rg s = (st, en))
    (hact : ∀ a ∈ act, a.slot ≠ s) :
    ScanInv numRegs rg st
      (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).1
      (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).2.1
      (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).2.2 := by
  simp only [physScanSpillStep, physScanSpillLose]
  split
  next => exact inv_skip inv hpos
  next =>
    split
    next ph hfr => exact inv_take_reg inv hpos hrg hact hfr
    next hfr =>
      split
      next far hv =>
        split
        next hp => exact inv_evict inv hpos hrg hact (victim_mem hv)
        next hp =>
          split
          next => exact inv_skip inv hpos
          next => exact inv_spill_incoming inv hpos hrg hact
      next hv =>
        split
        next => exact inv_skip inv hpos
        next => exact inv_spill_incoming inv hpos hrg hact

/-- A step does not assign a slot other than the one it processes. -/
theorem physScanSpillStep_fresh {numRegs : Nat} {uses : Array Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en t : Nat} {reserved : List Nat} {pieceOf : Nat → Option Nat}
    (h1 : physLoc acc t = none) (h2 : ¬ s = t) (h3 : ∀ a ∈ act, ¬ a.slot = t) :
    physLoc (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).2.2 t
      = none := by
  simp only [physScanSpillStep, physScanSpillLose]
  split
  next => exact h1
  next =>
    split
    next ph hfr => rw [physLoc_cons, ite_eq_right h2]; exact h1
    next hfr =>
      split
      next far hv =>
        split
        next hp =>
          have hfarAct : far ∈ act := (List.mem_filter.mp (victim_mem hv)).1
          rw [physLoc_cons, ite_eq_right (h3 far hfarAct), physLoc_cons, ite_eq_right h2]
          exact h1
        next hp =>
          split
          next => exact h1
          next => rw [physLoc_cons, ite_eq_right h2]; exact h1
      next hv =>
        split
        next => exact h1
        next => rw [physLoc_cons, ite_eq_right h2]; exact h1

/-- A step keeps out of the in-flight allocations every slot it does not process. -/
theorem physScanSpillStep_act_slot {numRegs : Nat} {uses : Array Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en t : Nat} {reserved : List Nat} {pieceOf : Nat → Option Nat}
    (h2 : ¬ s = t) (h3 : ∀ a ∈ act, ¬ a.slot = t) :
    ∀ a ∈ (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).1,
      ¬ a.slot = t := by
  have hfil : ∀ (p : PhysActive → Bool) (l : List PhysActive),
      (∀ a ∈ l, ¬ a.slot = t) → ∀ a ∈ l.filter p, ¬ a.slot = t :=
    fun _ _ hl a ha => hl a (List.mem_filter.mp ha).1
  simp only [physScanSpillStep, physScanSpillLose]
  split
  next => exact hfil _ _ h3
  next =>
    split
    next ph hfr =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact h2
      · exact hfil _ _ h3 a ha'
    next hfr =>
      split
      next far hv =>
        split
        next hp =>
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha'
          · exact h2
          · exact hfil _ _ (hfil _ _ h3) a ha'
        next hp => split <;> exact hfil _ _ h3
      next hv => split <;> exact hfil _ _ h3

/-- The scan's input contract: intervals in non-decreasing start order, one per
    slot. -/
def ItemsSorted (items : List (Nat × Nat × Nat)) : Prop :=
  items.Pairwise (fun a b => a.2.1 ≤ b.2.1 ∧ ¬ a.1 = b.1)

/-- `ScanInv` threads over the whole scan, pieces of split intervals included. -/
theorem physScanSpill_ScanInv (numRegs : Nat) (uses : Array Nat) (reserved : List Nat)
    (rg : Nat → Nat × Nat) {pieceOf : Nat → Option Nat} :
    ∀ (items : List (Nat × Nat × Nat)) (pos : Nat) (act : List PhysActive)
      (hulls : CellHulls) (acc : List (Nat × Nat)),
      ScanInv numRegs rg pos act hulls acc →
      ItemsSorted items →
      (∀ it ∈ items, pos ≤ it.2.1 ∧ rg it.1 = (it.2.1, it.2.2) ∧
        physLoc acc it.1 = none ∧ ∀ a ∈ act, ¬ a.slot = it.1) →
      ∃ pos' act' hulls',
        ScanInv numRegs rg pos' act' hulls'
          (physScanSpill numRegs uses items act hulls acc reserved pieceOf) := by
  intro items
  induction items with
  | nil => intro pos act hulls acc inv _ _; exact ⟨pos, act, hulls, inv⟩
  | cons it rest ih =>
    intro pos act hulls acc inv hsort hok
    obtain ⟨s, stt, enn⟩ := it
    obtain ⟨hp, hr, hf, ha⟩ := hok _ List.mem_cons_self
    rw [ItemsSorted, List.pairwise_cons] at hsort
    simp only [physScanSpill]
    refine ih stt (physScanSpillStep numRegs uses act hulls acc s stt enn reserved pieceOf).1
      (physScanSpillStep numRegs uses act hulls acc s stt enn reserved pieceOf).2.1
      (physScanSpillStep numRegs uses act hulls acc s stt enn reserved pieceOf).2.2
      (physScanSpillStep_ScanInv inv hp hr (fun a hA => ha a hA)) hsort.2 ?_
    intro it' hit'
    obtain ⟨hle, hnem⟩ := hsort.1 it' hit'
    obtain ⟨_, hr', hf', ha'⟩ := hok it' (List.mem_cons_of_mem _ hit')
    exact ⟨hle, hr', physScanSpillStep_fresh hf' hnem ha',
      physScanSpillStep_act_slot hnem ha'⟩

/-! ### Every processed slot other than a piece ends up with a location -/

theorem physLoc_cons_ne_none (p : Nat × Nat) (acc : List (Nat × Nat)) (t : Nat)
    (h : physLoc acc t ≠ none) : physLoc (p :: acc) t ≠ none := by
  obtain ⟨a, b⟩ := p
  rw [physLoc_cons]
  by_cases hat : a = t
  · simp [hat]
  · simpa [hat] using h

theorem physScanSpillStep_keeps {numRegs : Nat} {uses : Array Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en t : Nat} {reserved : List Nat} {pieceOf : Nat → Option Nat}
    (h : physLoc acc t ≠ none) :
    physLoc (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).2.2 t
      ≠ none := by
  simp only [physScanSpillStep, physScanSpillLose]
  split
  next => exact h
  next =>
    split
    next ph hfr => exact physLoc_cons_ne_none _ _ _ h
    next hfr =>
      split
      next far hv =>
        split
        next hp => exact physLoc_cons_ne_none _ _ _ (physLoc_cons_ne_none _ _ _ h)
        next hp =>
          split
          next => exact h
          next => exact physLoc_cons_ne_none _ _ _ h
      next hv =>
        split
        next => exact h
        next => exact physLoc_cons_ne_none _ _ _ h

theorem physScanSpillStep_assigns {numRegs : Nat} {uses : Array Nat}
    {act : List PhysActive} {hulls : CellHulls} {acc : List (Nat × Nat)}
    {s st en : Nat} {reserved : List Nat} {pieceOf : Nat → Option Nat}
    (hs : pieceOf s = none) :
    physLoc (physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).2.2 s
      ≠ none := by
  have hskip : pieceSkip numRegs pieceOf acc s = false := by
    simp [pieceSkip, hs]
  simp only [physScanSpillStep, physScanSpillLose, hskip, hs, Bool.false_eq_true, ite_false,
    Option.isSome_none]
  split
  next ph hfr => rw [physLoc_cons, ite_eq_left rfl]; simp
  next hfr =>
    split
    next far hv =>
      split
      next hp =>
        rw [physLoc_cons]
        by_cases hfs : far.slot = s
        · simp [hfs]
        · rw [ite_eq_right hfs, physLoc_cons, ite_eq_left rfl]; simp
      next hp => rw [physLoc_cons, ite_eq_left rfl]; simp
    next hv => rw [physLoc_cons, ite_eq_left rfl]; simp

theorem physScanSpill_keeps (numRegs : Nat) (uses : Array Nat) (reserved : List Nat)
    {pieceOf : Nat → Option Nat} :
    ∀ (items : List (Nat × Nat × Nat)) (act : List PhysActive) (hulls : CellHulls)
      (acc : List (Nat × Nat)) (t : Nat), physLoc acc t ≠ none →
      physLoc (physScanSpill numRegs uses items act hulls acc reserved pieceOf) t ≠ none := by
  intro items
  induction items with
  | nil => intro act hulls acc t h; exact h
  | cons it rest ih =>
    intro act hulls acc t h
    obtain ⟨s, stt, enn⟩ := it
    simp only [physScanSpill]
    exact ih _ _ _ t (physScanSpillStep_keeps h)

/-- Every item of the scan that is no piece receives a location. -/
theorem physScanSpill_assigns (numRegs : Nat) (uses : Array Nat) (reserved : List Nat)
    {pieceOf : Nat → Option Nat} :
    ∀ (items : List (Nat × Nat × Nat)) (act : List PhysActive) (hulls : CellHulls)
      (acc : List (Nat × Nat)), ∀ it ∈ items, pieceOf it.1 = none →
      physLoc (physScanSpill numRegs uses items act hulls acc reserved pieceOf) it.1
        ≠ none := by
  intro items
  induction items with
  | nil => intro _ _ _ it hit; exact absurd hit (by simp)
  | cons it0 rest ih =>
    intro act hulls acc it hit hpc
    obtain ⟨s, stt, enn⟩ := it0
    simp only [physScanSpill]
    rcases List.mem_cons.mp hit with rfl | hit'
    · exact physScanSpill_keeps numRegs uses reserved rest _ _ _ _
        (physScanSpillStep_assigns hpc)
    · exact ih _ _ _ it hit' hpc

/-! ## 4. The allocation is collision-free

The scan-level statement, then its instance for the shipped item list
`physLiveItems` and the shipped table `physAssign`/`physMap`. -/

/-- Two distinct slots whose ranges overlap never receive the same physical
    location from the bounded scan. The slots range over the items, pieces of split
    intervals included (`pieceOf`): a piece that holds a register over its range shares it
    with no slot or piece whose range overlaps. -/
theorem physScanSpill_no_collision (numRegs : Nat) (uses : Array Nat) (reserved : List Nat)
    (rg : Nat → Nat × Nat) (items : List (Nat × Nat × Nat))
    (hsort : ItemsSorted items)
    (hrg : ∀ it ∈ items, rg it.1 = (it.2.1, it.2.2))
    {pieceOf : Nat → Option Nat}
    {t₁ t₂ p : Nat} (hne : t₁ ≠ t₂)
    (h1 : physLoc (physScanSpill numRegs uses items [] #[] [] reserved pieceOf) t₁ = some p)
    (h2 : physLoc (physScanSpill numRegs uses items [] #[] [] reserved pieceOf) t₂ = some p) :
    ¬ physRangesOverlap (rg t₁) (rg t₂) := by
  obtain ⟨_, _, _, inv⟩ :=
    physScanSpill_ScanInv numRegs uses reserved rg (pieceOf := pieceOf) items 0 [] #[] []
      ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
      hsort (fun it hit => ⟨Nat.zero_le _, hrg it hit, rfl, by simp⟩)
  exact inv.noColl t₁ t₂ p hne h1 h2

theorem liveCmp_trans : ∀ (a b c : Nat × Nat × Nat),
    (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1 ≤ b.1)) = true →
    (b.2.1 < c.2.1 || (b.2.1 == c.2.1 && b.1 ≤ c.1)) = true →
    (a.2.1 < c.2.1 || (a.2.1 == c.2.1 && a.1 ≤ c.1)) = true := by
  intro a b c hab hbc
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hab hbc ⊢
  omega

theorem liveCmp_total : ∀ (a b : Nat × Nat × Nat),
    ((a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1 ≤ b.1))
      || (b.2.1 < a.2.1 || (b.2.1 == a.2.1 && b.1 ≤ a.1))) = true := by
  intro a b
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

/-- The shipped item list names each live slot once. -/
theorem physLiveItems_slots_nodup (tr : List PhysEvent) :
    (physLiveItems tr).Pairwise (fun a b => ¬ a.1 = b.1) := by
  simp only [physLiveItems, physLiveData, kernelMergeSort_eq]
  refine ((List.mergeSort_perm _ _).pairwise_iff (fun h he => h he.symm)).mpr ?_
  rw [List.pairwise_filterMap]
  refine List.nodup_range.imp ?_
  intro a b hab x hx y hy
  by_cases ha : (physLiveRange tr a).1 < tr.length
  · by_cases hb : (physLiveRange tr b).1 < tr.length
    · simp only [ha, hb, ite_eq_left, Option.some.injEq] at hx hy
      rw [← hx, ← hy]; exact hab
    · simp only [hb, ite_eq_right, not_false_iff] at hy
      exact absurd hy (by simp)
  · simp only [ha, ite_eq_right, not_false_iff] at hx
    exact absurd hx (by simp)

/-- The shipped item list meets the scan's input contract. -/
theorem physLiveItems_sorted (tr : List PhysEvent) : ItemsSorted (physLiveItems tr) := by
  refine List.Pairwise.and ?_ (physLiveItems_slots_nodup tr)
  simp only [physLiveItems, physLiveData, kernelMergeSort_eq]
  refine (List.pairwise_mergeSort liveCmp_trans liveCmp_total _).imp ?_
  intro a b h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  omega

/-- The shipped item list carries each slot's `physLiveRange`. -/
theorem physLiveItems_range (tr : List PhysEvent) :
    ∀ it ∈ physLiveItems tr, physLiveRange tr it.1 = (it.2.1, it.2.2) := by
  intro it hit
  simp only [physLiveItems, physLiveData, kernelMergeSort_eq] at hit
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filterMap] at hit
  obtain ⟨a, _, hfa⟩ := hit
  by_cases ha : (physLiveRange tr a).1 < tr.length
  · simp only [ha, ite_eq_left, Option.some.injEq] at hfa
    rw [← hfa]
  · simp only [ha, ite_eq_right, not_false_iff] at hfa
    exact absurd hfa (by simp)

/-- Two distinct slots whose conservative live ranges overlap never receive the
    same physical location from `physAssign`. -/
theorem physAssign_no_collision (tr : List PhysEvent) {t₁ t₂ p : Nat} (hne : t₁ ≠ t₂)
    (h1 : physLoc (physAssign tr) t₁ = some p) (h2 : physLoc (physAssign tr) t₂ = some p) :
    ¬ physRangesOverlap (physLiveRange tr t₁) (physLiveRange tr t₂) :=
  physScanSpill_no_collision numGPRegs (physLiveData tr).2 [] (physLiveRange tr)
    (physLiveData tr).1 (physLiveItems_sorted tr) (physLiveItems_range tr) hne h1 h2

/-- `physMap` reports the location `physAssign` recorded. -/
theorem physMap_eq_of_physLoc {tr : List PhysEvent} {s p : Nat}
    (h : physLoc (physAssign tr) s = some p) : physMap tr s = p := by
  unfold physMap
  unfold physLoc at h
  cases hfind : (physAssign tr).find? (fun q => q.1 == s) with
  | some q => rw [hfind] at h; simpa using h
  | none => rw [hfind] at h; exact absurd h (by simp)

/-- Every live slot is assigned. -/
theorem physAssign_physLoc_live (tr : List PhysEvent) {s : Nat}
    (hs : ∃ it ∈ physLiveItems tr, it.1 = s) : physLoc (physAssign tr) s ≠ none := by
  obtain ⟨it, hit, rfl⟩ := hs
  exact physScanSpill_assigns numGPRegs (physLiveData tr).2 []
    (physLiveData tr).1 [] #[] [] it hit rfl

/-- The physical location `physMap` reports separates any two distinct live slots
    whose ranges overlap — registers and stack cells alike. -/
theorem physMap_no_collision (tr : List PhysEvent) {t₁ t₂ : Nat} (hne : t₁ ≠ t₂)
    (hl1 : ∃ it ∈ physLiveItems tr, it.1 = t₁)
    (hl2 : ∃ it ∈ physLiveItems tr, it.1 = t₂)
    (hov : physRangesOverlap (physLiveRange tr t₁) (physLiveRange tr t₂)) :
    physMap tr t₁ ≠ physMap tr t₂ := by
  intro heq
  cases h1 : physLoc (physAssign tr) t₁ with
  | none => exact physAssign_physLoc_live tr hl1 h1
  | some p₁ =>
    cases h2 : physLoc (physAssign tr) t₂ with
    | none => exact physAssign_physLoc_live tr hl2 h2
    | some p₂ =>
      have e1 := physMap_eq_of_physLoc h1
      have e2 := physMap_eq_of_physLoc h2
      have hpp : p₁ = p₂ := by rw [← e1, ← e2]; exact heq
      subst hpp
      exact physAssign_no_collision tr hne h1 h2 hov

/-! ## 5. The collapse-or-mov dichotomy of `lowerTwoAddr`

`physScanSpillStep` does **not** structurally place a binop's `dst` on its first
source's register (it picks the lowest free register in the pool). So `hcol`
(`physRename dst = physRename s0`) is a *derived side-condition*, not a
structural fact of the RA. The lowering is robust to its failure:
`lowerTwoAddr` branches on `dst = s0`. When `hcol` holds (physical `dst = s0`), the leading `mov` collapses;
when it fails, `lowerTwoAddr` emits the `legalizeMov dst s0` prefix — the case
already discharged by the two-address probe's `dst ≠ s0` arm. We make the
dichotomy explicit as a definitional case split, so the `hcol`/`mov` split is a
provable fact about `lowerTwoAddr` (not an assumption). -/

/-- **The collapse-or-mov dichotomy.** On the 32-bit (`MOV`) path,
    `lowerTwoAddr` is *exactly* the collapse form `legalizeBinop dst s1 opn` when
    `dst = s0`, the scratch form `scratchBinop s0 s1 opn` followed by the store of `R15`
    when `dst ≠ s0` is a spill slot, and the mov-prefixed form `legalizeMov dst s0 ++
    legalizeBinop dst s1 opn` otherwise. Hence `hcol` (which forces the physical
    `dst = s0`) selects the collapse branch; its negation routes through the
    already-handled `legalizeMov` prefix. The collapse is therefore never
    *required* — it is an optimization the RA may or may not enable, and the
    lowering is faithful either way. -/
theorem lowerTwoAddr_dichotomy (dst s0 s1 opn : String) :
    lowerTwoAddr (.reg dst) (.reg s0) (.reg s1) opn "MOV"
      = (if dst = s0
          then legalizeBinop (.reg dst) (.reg s1) opn "MOV"
          else if (LOperand.reg dst).isSpill then
            scratchBinop (.reg s0) (.reg s1) opn "MOV"
              ++ [.Lopn [.reg dst] "MOV" [.reg reloadScratch]]
          else legalizeMov (.reg dst) (.reg s0) "MOV"
                ++ legalizeBinop (.reg dst) (.reg s1) opn "MOV") := by
  unfold lowerTwoAddr
  rw [materializeWideImm_MOV]
  by_cases h : (LOperand.reg dst) = (LOperand.reg s0)
  · have hds : dst = s0 := by injection h
    simp [hds]
  · have hds : dst ≠ s0 := fun he => h (by rw [he])
    simp [hds]

/-- The `hcol` collapse condition `physRename body tbl s0 = physRename body tbl
    (dst)` is precisely the equality of the *physical* operand names the lowering
    branches on: when it holds, `lowerTwoAddr` (over the physical names) takes the
    collapse branch. This ties the abstract `hcol` carried in `CoverData` to the
    concrete `dst = s0` test of `lowerTwoAddr_dichotomy`. -/
theorem lowerTwoAddr_collapse_of_eq (dst s0 s1 opn : String) (hcol : dst = s0) :
    lowerTwoAddr (.reg dst) (.reg s0) (.reg s1) opn "MOV"
      = legalizeBinop (.reg dst) (.reg s1) opn "MOV" := by
  rw [lowerTwoAddr_dichotomy, ite_eq_left hcol]

/-! ## 6. `physRegName` injectivity — the rendering layer of `hinj`

`hinj` is `physRename`-injectivity into a binding's destination:
`physRename = physRegName ∘ physMapTabled tbl ∘ nameSlot`. It composes three
injectivities: `nameSlot` injective on distinct live names, `physMap` injective
on overlapping slots (§4), and `physRegName` injective on the slot-index range.
The last is a finite/arithmetic fact discharged here. -/

/-- No GP register name begins with the character `'k'`; the spill names
    `"k." ++ …` and `"kv." ++ …` all begin with `'k'`. The character-level
    discriminator that separates the register blocks from the spill blocks. -/
theorem gpRegNames_head_ne_k : ∀ r ∈ gpRegNames, r.toList.head? ≠ some 'k' := by decide

/-- No vector register name begins with the character `'k'`. -/
theorem vectorRegNames_head_ne_k : ∀ r ∈ vectorRegNames, r.toList.head? ≠ some 'k' := by
  decide

/-- A GP spill name `"k." ++ toString n` begins with `'k'`. -/
theorem kdot_head_eq_k (n : Nat) : ("k." ++ toString n).toList.head? = some 'k' := by
  simp [String.toList_append]

/-- A vector spill name `"kv." ++ toString n` begins with `'k'`. -/
theorem kvdot_head_eq_k (n : Nat) : ("kv." ++ toString n).toList.head? = some 'k' := by
  simp [String.toList_append]

/-- `gpRegNames` has no duplicate entries. -/
theorem gpRegNames_nodup : gpRegNames.Nodup := by decide

/-- `vectorRegNames` has no duplicate entries. -/
theorem vectorRegNames_nodup : vectorRegNames.Nodup := by decide

/-- The GP and vector register names are disjoint. -/
theorem gpRegName_ne_vecRegName : ∀ r ∈ gpRegNames, ∀ v ∈ vectorRegNames, r ≠ v := by decide

/-- A GP register name is never a `"k."`-spill name. -/
theorem gpRegName_ne_kdot {r : String} (hr : r ∈ gpRegNames) (n : Nat) :
    r ≠ "k." ++ toString n := by
  intro he
  exact gpRegNames_head_ne_k r hr (by rw [he, kdot_head_eq_k])

/-- A GP register name is never a `"kv."`-spill name. -/
theorem gpRegName_ne_kvdot {r : String} (hr : r ∈ gpRegNames) (n : Nat) :
    r ≠ "kv." ++ toString n := by
  intro he
  exact gpRegNames_head_ne_k r hr (by rw [he, kvdot_head_eq_k])

/-- A vector register name is never a `"k."`-spill name. -/
theorem vecRegName_ne_kdot {r : String} (hr : r ∈ vectorRegNames) (n : Nat) :
    r ≠ "k." ++ toString n := by
  intro he
  exact vectorRegNames_head_ne_k r hr (by rw [he, kdot_head_eq_k])

/-- A vector register name is never a `"kv."`-spill name. -/
theorem vecRegName_ne_kvdot {r : String} (hr : r ∈ vectorRegNames) (n : Nat) :
    r ≠ "kv." ++ toString n := by
  intro he
  exact vectorRegNames_head_ne_k r hr (by rw [he, kvdot_head_eq_k])

/-- The two spill blocks are distinguished by their second character. -/
theorem kdot_ne_kvdot (n m : Nat) : "k." ++ toString n ≠ "kv." ++ toString m := by
  intro he
  have h := congrArg (fun s : String => s.toList.tail.head?) he
  simp [String.toList_append] at h

/-- The GP pool sits strictly below the vector pool's base index. -/
theorem numGPRegs_lt_vectorBase : numGPRegs < vectorBase := by decide

/-- A GP-block index renders to the GP register name at that index. -/
theorem physRegName_gp_eq {a : Nat} (ha : a < gpRegNames.length) :
    physRegName a = gpRegNames[a] := by
  have hv := numGPRegs_lt_vectorBase
  have ha2 : a < numGPRegs := by simpa [numGPRegs] using ha
  unfold physRegName
  rw [ite_eq_right (by omega), List.getElem?_eq_getElem ha]

/-- A vector-block index renders to the vector register name at that index. -/
theorem physRegName_vec_eq {a : Nat} (ha : vectorBase ≤ a)
    (hb : a - vectorBase < vectorRegNames.length) :
    physRegName a = vectorRegNames[a - vectorBase] := by
  unfold physRegName
  rw [ite_eq_left (by omega)]
  dsimp only
  rw [List.getElem?_eq_getElem hb]

/-- A GP-block index renders to a GP register name. -/
theorem physRegName_gp_mem {a : Nat} (ha : a < numGPRegs) :
    ∃ r ∈ gpRegNames, physRegName a = r := by
  have ha' : a < gpRegNames.length := by simpa [numGPRegs] using ha
  exact ⟨gpRegNames[a], List.getElem_mem ha', physRegName_gp_eq ha'⟩

/-- A vector-block index renders to a vector register name. -/
theorem physRegName_vec_mem {a : Nat} (ha : vectorBase ≤ a) (hb : a - vectorBase < numVecRegs) :
    ∃ r ∈ vectorRegNames, physRegName a = r := by
  have hb' : a - vectorBase < vectorRegNames.length := by simpa [numVecRegs] using hb
  exact ⟨vectorRegNames[a - vectorBase], List.getElem_mem hb', physRegName_vec_eq ha hb'⟩

/-- **`physRegName` injective on the GP-register block.** Two physical indices
    both below `numGPRegs` render to the same name only if equal — the
    duplicate-free `gpRegNames` (`gpRegNames_nodup`) makes `physRegName` injective
    on `[0, numGPRegs)`, the registers the allocator hands out in the no-spill
    (common) case. The rendering layer of `hinj` on the GP block. -/
theorem physRegName_injOn_gp {a b : Nat} (ha : a < numGPRegs) (hb : b < numGPRegs)
    (hab : physRegName a = physRegName b) : a = b := by
  have ha' : a < gpRegNames.length := by simpa [numGPRegs] using ha
  have hb' : b < gpRegNames.length := by simpa [numGPRegs] using hb
  rw [physRegName_gp_eq ha', physRegName_gp_eq hb'] at hab
  exact (List.Nodup.getElem_inj_iff gpRegNames_nodup (hi := ha') (hj := hb')).mp hab

/-- **`physRegName` injective on the vector-register block.** -/
theorem physRegName_injOn_vec {a b : Nat} (ha : vectorBase ≤ a) (hb : vectorBase ≤ b)
    (ha2 : a - vectorBase < numVecRegs) (hb2 : b - vectorBase < numVecRegs)
    (hab : physRegName a = physRegName b) : a = b := by
  have ha' : a - vectorBase < vectorRegNames.length := by simpa [numVecRegs] using ha2
  have hb' : b - vectorBase < vectorRegNames.length := by simpa [numVecRegs] using hb2
  rw [physRegName_vec_eq ha ha', physRegName_vec_eq hb hb'] at hab
  have := (List.Nodup.getElem_inj_iff vectorRegNames_nodup (hi := ha') (hj := hb')).mp hab
  omega

/-! ### `Nat.toDigits 10` injectivity — the decimal-rendering atom of the spill block

`physRegName`'s spill names are `"k." ++ toString (phys - numGPRegs)`, so spill-
block injectivity bottoms out in injectivity of `toString` on `Nat`
(= `Nat.repr = String.ofList ∘ Nat.toDigits 10`). Mathlib/Batteries has **no**
`Nat.repr`/`Nat.toDigits` injectivity lemma, so we prove the decimal-string
injectivity from the Batteries recurrence (`toDigits_append_toDigits`,
`toDigits_of_lt_base`) by strong induction. -/

/-- One decimal-digit peel: for `n ≥ 10`, `toDigits 10 n` is the digits of `n/10`
    followed by the units digit `(n%10).digitChar`. Derived from
    `Nat.toDigits_append_toDigits`. -/
theorem toDigits_rec (n : Nat) (hn : 10 ≤ n) :
    Nat.toDigits 10 n = Nat.toDigits 10 (n / 10) ++ [(n % 10).digitChar] := by
  have h1 : 0 < n / 10 := Nat.div_pos hn (by decide)
  have h2 : n % 10 < 10 := Nat.mod_lt _ (by decide)
  have hkey := Nat.toDigits_append_toDigits (b := 10) (n := n / 10) (d := n % 10)
    (by decide) h1 h2
  rw [Nat.toDigits_of_lt_base h2] at hkey
  rw [hkey]; congr 1; omega

/-- The decimal rendering of any `Nat` is non-empty. -/
theorem toDigits_ne_nil (k : Nat) : Nat.toDigits 10 k ≠ [] := by
  by_cases hk : k < 10
  · rw [Nat.toDigits_of_lt_base hk]; simp
  · rw [toDigits_rec k (by omega)]; simp

/-- `Nat.digitChar` is injective on `[0, 10)` (the base-10 digit alphabet). -/
theorem digitChar_inj10 : ∀ a < 10, ∀ b < 10, Nat.digitChar a = Nat.digitChar b → a = b := by
  decide

/-- **`Nat.toDigits 10` is injective.** Proved by strong induction on `m`: the
    `< 10` × `< 10` case is `digitChar` injectivity; mixed-length cases are length
    contradictions (`toDigits_ne_nil`); the `≥ 10` × `≥ 10` case peels the units
    digit (`toDigits_rec`, `List.append_singleton_inj`) and recurses on `·/10`.
    The decimal-string atom Mathlib/Batteries lacks. -/
theorem toDigits_inj : ∀ (m n : Nat), Nat.toDigits 10 m = Nat.toDigits 10 n → m = n := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro n h
    by_cases hm : m < 10 <;> by_cases hn : n < 10
    · rw [Nat.toDigits_of_lt_base hm, Nat.toDigits_of_lt_base hn] at h
      simp only [List.cons.injEq, and_true] at h
      exact digitChar_inj10 m hm n hn h
    · exfalso
      rw [Nat.toDigits_of_lt_base hm, toDigits_rec n (by omega)] at h
      have hl := congrArg List.length h
      have hpos : 0 < (Nat.toDigits 10 (n / 10)).length :=
        List.length_pos_iff.mpr (toDigits_ne_nil (n / 10))
      simp only [List.length_cons, List.length_nil, List.length_append] at hl
      omega
    · exfalso
      rw [Nat.toDigits_of_lt_base hn, toDigits_rec m (by omega)] at h
      have hl := congrArg List.length h
      have hpos : 0 < (Nat.toDigits 10 (m / 10)).length :=
        List.length_pos_iff.mpr (toDigits_ne_nil (m / 10))
      simp only [List.length_cons, List.length_nil, List.length_append] at hl
      omega
    · rw [toDigits_rec m (by omega), toDigits_rec n (by omega)] at h
      obtain ⟨hpre, hlast⟩ := List.append_singleton_inj.mp h
      have hmod : m % 10 = n % 10 :=
        digitChar_inj10 _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) hlast
      have hdiv : m / 10 = n / 10 := ih (m / 10) (by omega) (n / 10) hpre
      omega

/-- **`toString` is injective on `Nat`.** Since `toString k = Nat.repr k =
    String.ofList (Nat.toDigits 10 k)`, this follows from `toDigits_inj` through
    `String.ofList` injectivity (`String.toList_ofList`). -/
theorem toString_nat_inj (m n : Nat) (h : toString m = toString n) : m = n := by
  have hr : ∀ k : Nat, toString k = String.ofList (Nat.toDigits 10 k) := fun _ => rfl
  rw [hr, hr] at h
  have ht := congrArg String.toList h
  rw [String.toList_ofList, String.toList_ofList] at ht
  exact toDigits_inj m n ht

/-- The GP spill name `physRegName` renders for a scalar index `≥ numGPRegs`. -/
theorem physRegName_spill_eq {a : Nat} (ha : numGPRegs ≤ a) (hv : a < vectorBase) :
    physRegName a = "k." ++ toString (a - numGPRegs) := by
  unfold physRegName
  rw [ite_eq_right (by omega), List.getElem?_eq_none (by simpa [numGPRegs] using ha)]
  rfl

/-- The vector spill name `physRegName` renders for a vector index beyond the
    vector register file. -/
theorem physRegName_vspill_eq {a : Nat} (ha : vectorBase ≤ a)
    (hb : numVecRegs ≤ a - vectorBase) :
    physRegName a = "kv." ++ toString (a - vectorBase - numVecRegs) := by
  unfold physRegName
  rw [ite_eq_left (by omega)]
  dsimp only
  rw [List.getElem?_eq_none (by simpa [numVecRegs] using hb)]

/-- **`physRegName` injective on the GP spill block.** Two scalar indices
    `≥ numGPRegs` render to the same `"k." ++ toString (·-numGPRegs)` name only if
    equal — by `toString_nat_inj` on the offsets. -/
theorem physRegName_injOn_spill {a b : Nat} (ha : numGPRegs ≤ a) (hb : numGPRegs ≤ b)
    (hva : a < vectorBase) (hvb : b < vectorBase)
    (hab : physRegName a = physRegName b) : a = b := by
  rw [physRegName_spill_eq ha hva, physRegName_spill_eq hb hvb] at hab
  have hoff : toString (a - numGPRegs) = toString (b - numGPRegs) :=
    (String.append_right_inj "k.").mp hab
  have : a - numGPRegs = b - numGPRegs := toString_nat_inj _ _ hoff
  omega

/-- **`physRegName` injective on the vector spill block.** -/
theorem physRegName_injOn_vspill {a b : Nat} (ha : vectorBase ≤ a) (hb : vectorBase ≤ b)
    (ha2 : numVecRegs ≤ a - vectorBase) (hb2 : numVecRegs ≤ b - vectorBase)
    (hab : physRegName a = physRegName b) : a = b := by
  rw [physRegName_vspill_eq ha ha2, physRegName_vspill_eq hb hb2] at hab
  have hoff : toString (a - vectorBase - numVecRegs) = toString (b - vectorBase - numVecRegs) :=
    (String.append_right_inj "kv.").mp hab
  have : a - vectorBase - numVecRegs = b - vectorBase - numVecRegs := toString_nat_inj _ _ hoff
  omega

/-! ### `nameSlot` injectivity on the live set

`nameSlot body n = (bodyNames body).idxOf n` is the first-appearance rank of `n`.
On names that **occur** in the body (`n ∈ bodyNames body` — the live set), the
rank is a left inverse of indexing (`List.getElem_idxOf`), so distinct live names
get distinct slots. (It is *not* globally injective: every name absent from
`bodyNames` collapses onto the out-of-universe sentinel `bodyNames.length`, which
is exactly why `hinj` is scoped to the live set.) -/

/-- **`nameSlot` injective on live names.** Two names that both occur in the body
    (`∈ bodyNames body`) with the same first-appearance rank are equal. The
    name-level seed of `hinj`, restricted (as it must be) to the live set. -/
theorem nameSlot_injOn {body : Lcmd} {m n : String}
    (hm : m ∈ bodyNames body) (hn : n ∈ bodyNames body)
    (h : nameSlot body m = nameSlot body n) : m = n := by
  unfold nameSlot at h
  have hra := List.getElem_idxOf (x := m) (xs := bodyNames body)
    (List.idxOf_lt_length_iff.mpr hm)
  have hrb := List.getElem_idxOf (x := n) (xs := bodyNames body)
    (List.idxOf_lt_length_iff.mpr hn)
  rw [← hra, ← hrb]; simp only [h]

/-- **`physRegName` is injective on the scalar pool.** The GP block
    (`< numGPRegs`) and the GP spill block are each injective and are separated by
    their leading character. -/
theorem physRegName_injOn_scalar {a b : Nat} (hva : a < vectorBase) (hvb : b < vectorBase)
    (hab : physRegName a = physRegName b) : a = b := by
  rcases Nat.lt_or_ge a numGPRegs with ha | ha <;> rcases Nat.lt_or_ge b numGPRegs with hb | hb
  · exact physRegName_injOn_gp ha hb hab
  · obtain ⟨r, hr, hre⟩ := physRegName_gp_mem ha
    rw [hre, physRegName_spill_eq hb hvb] at hab
    exact absurd hab (gpRegName_ne_kdot hr _)
  · obtain ⟨r, hr, hre⟩ := physRegName_gp_mem hb
    rw [hre, physRegName_spill_eq ha hva] at hab
    exact absurd hab.symm (gpRegName_ne_kdot hr _)
  · exact physRegName_injOn_spill ha hb hva hvb hab

/-- **`physRegName` is injective on the vector pool.** -/
theorem physRegName_injOn_vector {a b : Nat} (hva : vectorBase ≤ a) (hvb : vectorBase ≤ b)
    (hab : physRegName a = physRegName b) : a = b := by
  rcases Nat.lt_or_ge (a - vectorBase) numVecRegs with ha | ha <;>
    rcases Nat.lt_or_ge (b - vectorBase) numVecRegs with hb | hb
  · exact physRegName_injOn_vec hva hvb ha hb hab
  · obtain ⟨r, hr, hre⟩ := physRegName_vec_mem hva ha
    rw [hre, physRegName_vspill_eq hvb hb] at hab
    exact absurd hab (vecRegName_ne_kvdot hr _)
  · obtain ⟨r, hr, hre⟩ := physRegName_vec_mem hvb hb
    rw [hre, physRegName_vspill_eq hva ha] at hab
    exact absurd hab.symm (vecRegName_ne_kvdot hr _)
  · exact physRegName_injOn_vspill hva hvb ha hb hab

/-- **`physRegName` keeps the scalar and vector pools apart.** -/
theorem physRegName_scalar_ne_vector {a b : Nat} (hva : a < vectorBase) (hvb : vectorBase ≤ b) :
    physRegName a ≠ physRegName b := by
  rcases Nat.lt_or_ge a numGPRegs with ha | ha <;>
    rcases Nat.lt_or_ge (b - vectorBase) numVecRegs with hb | hb
  · obtain ⟨r, hr, hre⟩ := physRegName_gp_mem ha
    obtain ⟨v, hv, hve⟩ := physRegName_vec_mem hvb hb
    rw [hre, hve]
    exact gpRegName_ne_vecRegName r hr v hv
  · obtain ⟨r, hr, hre⟩ := physRegName_gp_mem ha
    rw [hre, physRegName_vspill_eq hvb hb]
    exact gpRegName_ne_kvdot hr _
  · obtain ⟨v, hv, hve⟩ := physRegName_vec_mem hvb hb
    rw [hve, physRegName_spill_eq ha hva]
    exact fun he => vecRegName_ne_kdot hv _ he.symm
  · rw [physRegName_spill_eq ha hva, physRegName_vspill_eq hvb hb]
    exact kdot_ne_kvdot _ _

/-- **`physRegName` is globally injective.** The scalar pool
    (`physRegName_injOn_scalar`) and the vector pool
    (`physRegName_injOn_vector`) are each injective and disjoint
    (`physRegName_scalar_ne_vector`), so `physRegName` is injective on all of
    `Nat` — the full rendering layer of `hinj`, hypothesis-free. -/
theorem physRegName_inj {a b : Nat} (hab : physRegName a = physRegName b) : a = b := by
  rcases Nat.lt_or_ge a vectorBase with ha | ha <;> rcases Nat.lt_or_ge b vectorBase with hb | hb
  · exact physRegName_injOn_scalar ha hb hab
  · exact absurd hab (physRegName_scalar_ne_vector ha hb)
  · exact absurd hab.symm (physRegName_scalar_ne_vector hb ha)
  · exact physRegName_injOn_vector ha hb hab

/-! ## 7. Composing the rendering and naming layers of `hinj`

`hinj` (carried in each `BinopBinding`) is
`∀ m, physRename body tbl m = physRename body tbl nDst → m = nDst`, where
`physRename body tbl n = physRegName (physMapTabled tbl (nameSlot body n))`
(definitionally). This module discharges two of its three composed
injectivities outright: `physRegName` (the rendering layer, global,
`physRegName_inj`) and `nameSlot` (the naming layer, on the live set,
`nameSlot_injOn`). The remaining factor is `physMapTabled (physTable …)`
injectivity on overlapping slots, which §4 supplies for `physMap`. `hinj`
reduces to exactly that single slot-level hypothesis. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill in
/-- **`hinj` reduced to slot-level RA injectivity.** With the two rendering/naming
    layers discharged here (`physRegName_inj` global, `nameSlot_injOn` on the live
    set), the per-binding destination injectivity `hinj` follows from the single
    remaining fact `hslot`: `physMapTabled tbl` maps the (distinct, live) source
    slot and destination slot to distinct physical registers, which
    `physMap_no_collision` (§4) supplies for a `physTable`-shaped `tbl` whose two
    slots are live and overlapping. `physRename body tbl n` unfolds to
    `physRegName (physMapTabled tbl (nameSlot body n))` by `rfl`. -/
theorem physRename_injOn_live {body : Lcmd} {tbl : Array Nat} {m nDst : String}
    (hm : m ∈ bodyNames body) (hnDst : nDst ∈ bodyNames body)
    (hslot : physMapTabled tbl (nameSlot body m) = physMapTabled tbl (nameSlot body nDst) →
      nameSlot body m = nameSlot body nDst)
    (h : physRename body tbl m = physRename body tbl nDst) : m = nDst := by
  -- peel the rendering layer (physRegName injective, global)
  have hmap : physMapTabled tbl (nameSlot body m) = physMapTabled tbl (nameSlot body nDst) :=
    physRegName_inj h
  -- peel the RA slot layer (the residual hypothesis), then the naming layer
  exact nameSlot_injOn hm hnDst (hslot hmap)

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRA
