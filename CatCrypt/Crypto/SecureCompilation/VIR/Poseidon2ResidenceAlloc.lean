/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Interference-aware register-residence allocator

A residence-coalescing map for the owned-RA producer that assigns each `Com`
binding a physical-slot index by first-fit over its live range, so two bindings
share a slot only when their live ranges do not overlap.

The live range of a binding is `[firstTouch, lastTouch]` over the body's
`PhysEvent` trace (definition index to last-use index). `allocFold` places the
ranges, in start order, into the cell pool of `JasminLprogExport`
(`allocCell`/`firstFittingCell`): a range reuses a cell only when the cell's hull
is disjoint from it. `allocFold_pairwise_disj` proves that ranges sharing a cell
are pairwise non-overlapping — the interference-freedom the naive
same-logical-slot coalescing lacks.

`residenceOfBody` runs the allocator over the **emit-time** body
(`materializeShiftCountImms body`, the body the residence rename runs against),
so a binding's live range ends at its last surviving read rather than at a read
that a later pass removes. It uses `bodyTraceOut`, whose appended output-read
event keeps every designated output live to the epilogue store, and returns one
physical-slot index per body binding in program order (length `numBindings body`).

## Main definitions

* `allocFold`: first-fit placement of live ranges into the cell pool.
* `firstFitColors`: colours a live-range trace, scattering binding → cell.
* `residenceOfBody`: the `Array Nat` residence map `Com.toLprogPhysAbi` consumes.

## Main results

* `allocFold_pairwise_disj`: ranges placed in the same cell are pairwise
  non-overlapping — interference-freedom, proved over an abstract range list so
  its cost is independent of the body size.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## 0. Cell-pool disjointness lemmas

`X86Backend.ToLprogFaithfulRA` proves these for the same `allocCell`/
`firstFittingCell` primitives. They are restated here so this allocator's
interference proof depends only on `JasminLprogExport` (the emit modules the
`ToLprogFaithfulRA` closure pulls in are not needed to run or verify the
first-fit coloring). -/

/-- An index with an element is inside the array. -/
theorem lt_size_of_getElem? {α : Type} {a : Array α} {j : Nat} {x : α}
    (h : a[j]? = some x) : j < a.size := by
  rcases Nat.lt_or_ge j a.size with hj | hj
  · exact hj
  · rw [Array.getElem?_eq_none hj] at h
    exact absurd h (by simp)

/-- Range overlap is symmetric. -/
theorem physRangesOverlap_comm (r1 r2 : Nat × Nat) :
    physRangesOverlap r1 r2 = physRangesOverlap r2 r1 := by
  simp [physRangesOverlap, Bool.and_comm]

/-- A range inside a hull inherits the hull's disjointness. -/
theorem not_overlap_of_hull {r h R : Nat × Nat} (hlo : h.1 ≤ r.1) (hhi : r.2 ≤ h.2)
    (hd : ¬ physRangesOverlap h R) : ¬ physRangesOverlap r R := by
  simp only [physRangesOverlap, Bool.and_eq_true, decide_eq_true_eq, not_and] at hd ⊢
  omega

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
    · simp only [hlt, dif_pos]
      by_cases hov : physRangesOverlap hulls[i] (st, en)
      · simp only [hov, if_pos]
        exact ih (i + 1) (by omega) (by omega)
      · simp only [hov, Bool.false_eq_true, if_neg, not_false_iff]
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
    simp only [hge, dif_neg, not_false_iff] at hh
    rw [Array.getElem?_eq_none (by omega)] at hh
    exact absurd hh (by simp)
  | succ n ih =>
    intro i hn h hh
    rw [firstFittingCell] at hh
    by_cases hlt : i < hulls.size
    · simp only [hlt, dif_pos] at hh
      by_cases hov : physRangesOverlap hulls[i] (st, en)
      · simp only [hov, if_pos] at hh
        exact ih (i + 1) (by omega) h hh
      · simp only [hov, Bool.false_eq_true, if_neg, not_false_iff] at hh
        rw [Array.getElem?_eq_getElem hlt] at hh
        cases hh
        exact hov
    · simp only [hlt, dif_neg, not_false_iff] at hh
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
    rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hjlt)]
    exact hj

/-! ## 1. The first-fit fold over live ranges -/

/-- A placed live range: `(rank, cell, start, end)` — the logical slot `rank`
    assigned physical cell `cell`, whose live range is `[start, end]`. -/
abbrev Placement := Nat × Nat × Nat × Nat

/-- The physical cell of a placement. -/
def pCell (p : Placement) : Nat := p.2.1

/-- The live range of a placement. -/
def pRange (p : Placement) : Nat × Nat := (p.2.2.1, p.2.2.2)

/-- First-fit placement of live ranges into the cell pool. Each `(rank, st, en)`
    is put in the lowest cell whose hull is disjoint from `[st, en]` (widening
    that cell's hull) or a fresh cell (`allocCell`); the assignment is prepended
    to the accumulator. Ranges are expected in start order (`physLiveItems`). -/
def allocFold : List (Nat × Nat × Nat) → CellHulls → List Placement →
    CellHulls × List Placement
  | [], hulls, acc => (hulls, acc)
  | (s, st, en) :: rest, hulls, acc =>
      let r := allocCell hulls st en
      allocFold rest r.2 ((s, r.1, st, en) :: acc)

/-- Two placements interfere-freely: sharing a cell forces disjoint ranges. -/
def DisjRel (a b : Placement) : Prop :=
  pCell a = pCell b → ¬ physRangesOverlap (pRange a) (pRange b)

/-- Every placement's cell hull covers its range. -/
def CoverInv (hulls : CellHulls) (acc : List Placement) : Prop :=
  ∀ p ∈ acc, ∃ h, hulls[pCell p]? = some h ∧ h.1 ≤ (pRange p).1 ∧ (pRange p).2 ≤ h.2

/-! ## 2. Interference-freedom of the first-fit coloring -/

/-- A range covered by a cell hull disjoint from `R` is itself disjoint from `R`.
    The covering `pRange p ⊆ h` transports `h`'s disjointness down. -/
theorem placement_not_overlap {p : Placement} {h R : Nat × Nat}
    (hlo : h.1 ≤ (pRange p).1) (hhi : (pRange p).2 ≤ h.2)
    (hd : ¬ physRangesOverlap h R) : ¬ physRangesOverlap (pRange p) R :=
  not_overlap_of_hull hlo hhi hd

/-- **Step:** placing `[st, en]` into `allocCell hulls st en` is interference-free
    against every already-placed range that lands in the same cell, and the cover
    invariant is preserved. -/
theorem allocFold_step (hulls : CellHulls) (acc : List Placement) (s st en : Nat)
    (hcov : CoverInv hulls acc) :
    (∀ p ∈ acc, DisjRel (s, (allocCell hulls st en).1, st, en) p) ∧
      CoverInv (allocCell hulls st en).2
        ((s, (allocCell hulls st en).1, st, en) :: acc) := by
  refine ⟨?_, ?_⟩
  · -- interference-freedom of the new placement against each old same-cell one
    intro p hp hcelleq
    -- `hcelleq : pCell (s, (allocCell hulls st en).1, st, en) = pCell p`
    have hpcell : pCell p = (allocCell hulls st en).1 := by
      simpa [pCell] using hcelleq.symm
    obtain ⟨h, hh, hlo, hhi⟩ := hcov p hp
    rw [hpcell] at hh
    -- `hh : hulls[cell]? = some h`; `allocCell_disjoint` gives `¬ overlap h (st,en)`
    have hdis : ¬ physRangesOverlap h (st, en) :=
      allocCell_disjoint hulls st en h hh
    have hpd : ¬ physRangesOverlap (pRange p) (st, en) :=
      placement_not_overlap hlo hhi hdis
    -- goal: `¬ overlap (pRange (s,cell,st,en)) (pRange p)`; `pRange … = (st,en)`
    show ¬ physRangesOverlap (st, en) (pRange p)
    rw [physRangesOverlap_comm]
    exact hpd
  · -- cover invariant preserved
    intro p hp
    rcases List.mem_cons.mp hp with hnew | hold
    · -- the new placement
      subst hnew
      obtain ⟨h', hh', hlo', hhi'⟩ := allocCell_covers hulls st en
      exact ⟨h', hh', by simpa [pRange] using hlo', by simpa [pRange] using hhi'⟩
    · -- an old placement: its hull only widened
      obtain ⟨h, hh, hlo, hhi⟩ := hcov p hold
      obtain ⟨h', hh', hmlo, hmhi⟩ := allocCell_mono hulls st en (pCell p) h hh
      exact ⟨h', hh', Nat.le_trans hmlo hlo, Nat.le_trans hhi hmhi⟩

/-- **Interference-freedom (invariant form):** starting from any hulls/acc that
    already satisfy the cover invariant and a pairwise-disjoint coloring, the fold
    keeps both. -/
theorem allocFold_inv (items : List (Nat × Nat × Nat)) :
    ∀ (hulls : CellHulls) (acc : List Placement),
      CoverInv hulls acc → acc.Pairwise DisjRel →
        CoverInv (allocFold items hulls acc).1 (allocFold items hulls acc).2 ∧
          (allocFold items hulls acc).2.Pairwise DisjRel := by
  induction items with
  | nil => intro hulls acc hcov hpw; exact ⟨hcov, hpw⟩
  | cons it rest ih =>
    obtain ⟨s, st, en⟩ := it
    intro hulls acc hcov hpw
    obtain ⟨hstepdisj, hstepcov⟩ := allocFold_step hulls acc s st en hcov
    have hpw' : ((s, (allocCell hulls st en).1, st, en) :: acc).Pairwise DisjRel :=
      List.Pairwise.cons hstepdisj hpw
    have := ih (allocCell hulls st en).2
      ((s, (allocCell hulls st en).1, st, en) :: acc) hstepcov hpw'
    simpa [allocFold] using this

/-- **The first-fit coloring is interference-free.** Every pair of placed ranges
    that share a physical cell has non-overlapping live ranges. -/
theorem allocFold_pairwise_disj (items : List (Nat × Nat × Nat)) :
    (allocFold items #[] []).2.Pairwise DisjRel :=
  (allocFold_inv items #[] [] (by intro p hp; simp at hp) List.Pairwise.nil).2

/-! ## 3. Residence array for a body -/

/-- The first-fit color of each logical slot as an array keyed by slot index.
    Runs `allocFold` over the live ranges (`physLiveItems`, start-sorted) and
    scatters each `(rank, cell)` into a slot-indexed array. -/
def firstFitColors (tr : List PhysEvent) : Array Nat := Id.run do
  let mut arr : Array Nat := Array.replicate (physUniverse tr) 0
  for p in (allocFold (physLiveItems tr) #[] []).2 do
    let s := p.1
    if s < arr.size then arr := arr.set! s (pCell p)
  return arr

/-- **The interference-aware residence map for a body**: one physical-cell index
    per binding in program order (length `numBindings body`).

    The coloring and the binding-ordinal map both run over the **emit-time** body
    `emitBody = materializeShiftCountImms body` — the same body the residence
    rename (`comToLfundefPhysAbi`) collapses onto residence slots. Computing
    liveness on `emitBody` (rather than the raw `comToLfundef` body) drops the
    reads that a post-pass removes before emit: `materializeShiftCountImms`
    rewrites each `SHL`/`SHR`'s `regConst`-defined count source `.reg nm` to an
    `.imm`, so the count slot is not read at the shift. A slot's live range
    therefore ends at its last *surviving* read, giving the precise last-use
    interference rather than the raw body's over-approximation, so fewer cells are
    needed and the working set stays register-resident.

    `emitBody` is a `body.map`: it preserves the `Lopn` count and order and every
    destination operand, so `numBindings`, the binding-ordinal positions, and each
    event's write slot (`ev.wr`) are unchanged from `body` — only the vanished
    shift-count reads shorten live ranges. The binding-ordinal indexing
    `residenceArraySlotOf` relies on is preserved. (`expandCallShadows`, the other
    pre-rename pass, is the identity on the call-free bodies this residence
    targets and — unlike `materializeShiftCountImms` — inserts marshalling
    instructions that would shift the binding ordinals, so it is not applied
    here.)

    The coloring runs over `bodyTraceOut emitBody outStoreMap`, whose appended
    output-read event keeps every designated output live to the epilogue store, so
    no two simultaneously live values receive the same cell. The `n`-th entry is
    the cell of the `n`-th binding's defined value (`(bodyTrace emitBody)`'s `n`-th
    event writes it), matching `residenceArraySlotOf`'s binding-ordinal indexing. -/
def residenceOfBody (body : Lcmd) (outStoreMap : OutStoreMap) : Array Nat :=
  let emitBody := materializeShiftCountImms body
  let colorByRank := firstFitColors (bodyTraceOut emitBody outStoreMap)
  ((bodyTrace emitBody).map (fun ev => colorByRank[ev.wr]?.getD 0)).toArray

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
