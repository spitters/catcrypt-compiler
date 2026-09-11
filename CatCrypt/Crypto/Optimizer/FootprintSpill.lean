/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Optimizer.GenericRegAlloc
public import CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-!
# Peak-pressure-minimizing ("reversible pebbling" / footprint) allocation (#xxx)

`GenericRegAlloc` computes the live-range structure of a straight-line block
(`liveRanges`), the register pressure at a position (`pressureAt`), and the peak
pressure over the block (`peakPressure`) — the count the physical-register pool
must hold to be spill-free. `SpillingRegAlloc` then *places* an allocation: when
the pool is full, it spills the farthest-ending live interval to a frame cell.

This module adds the **IR-level lever that minimizes peak pressure itself** — the
classical analogue of reversible pebbling. A spill decision does not just relocate
a value; by storing a value right after its definition and reloading it only
immediately before its next use, the value is **no longer live** at the
intermediate positions, so it is no longer counted toward the simultaneous-live
footprint there. Iterating this *footprint spill* over a chosen eviction set drives
`peakPressure` down. We work directly on the structural `List LiveRange` object
(the footprint), independent of any `MachineModel` instance — the live ranges are
exactly the pebbling graph, and soundness here is the structural invariant
(pointwise pressure non-increase + live-range well-formedness/containment), with the
end-to-end value identity left to the KAT, per the `SpillingRegAlloc`/`GenericRegAlloc`
translation-validation discipline.

## The reversible-pebbling / ecdsa.fail peak-qubit lever

In reversible (quantum) compilation, **peak register pressure here = peak number of
simultaneously-live qubits there** — the live-range list is the pebble graph, and a
pebble on a vertex is a value held live in a register/qubit. Reversible *pebbling*
trades **recomputation** (the reload, an extra op) for **fewer simultaneously-held
pebbles** (lower peak width): a value is uncomputed/spilled after its def and
recomputed/reloaded right before its use, so the qubit it occupied is free in
between. `footprintSpill` is exactly that move at the IR level — `truncateRangeAt`
shortens a value's live range to a single program point (its def), modelling
store-after-def + reload-before-use, which removes it from the live set everywhere
in between.

For the ecdsa.fail attack cost model (`CatCrypt/Quantum/EcdsaFail`), the resource
**score is a product** over the cost factors, one of which is the **peak qubit
width** (the reversible point-add's simultaneously-live ancillas). Lowering the peak
live-register count via footprint spilling therefore lowers the qubit factor of that
product directly — the same lever as ancilla uncompute (`Optimizer.UncomputePass`),
phrased on the live-range footprint instead of the binder tree. This is the
register-allocation side of the peak-qubit-width reduction.

## What is built and proved (structural, no new custom axioms)

* `truncateRangeAt` / `footprintSpill`: the eviction rewrite on `List LiveRange` —
  shorten each evicted name's live range to `[def, def]` (a pebble removed for all
  later positions).
* `lrPressureAt` / `lrPeak`: the live-range-list-level pressure / peak (the
  `pressureAt` / `peakPressure` shape, lifted off `MachineModel` so the pass is a
  pure live-range-to-live-range transform).
* `footprintSpill_pressure_le` (pointwise) ⟹ `footprintSpill_peak_le`:
  `lrPeak (footprintSpill ev lrs) ≤ lrPeak lrs` — the footprint never grows.
* `footprintSpill_valid`: every truncated range stays well-formed
  (`defIdx ≤ lastUse`) and is contained in the original range — the structural
  non-overlap-preservation a placement on top of it relies on.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.FootprintSpill

open CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-! ## 1. The footprint-spill rewrite on live ranges

A `LiveRange ⟨name, defIdx, lastUse⟩` occupies a register/qubit at every position
in the closed interval `[defIdx, lastUse]`. *Footprint-spilling* the name shortens
its interval to the single point `[defIdx, defIdx]`: the value is stored right after
its def and reloaded only just before its use, so it holds no register/qubit at any
position strictly after `defIdx`. This is the pebble-removal move. -/

/-- Truncate the live range of `name` to its definition point `[defIdx, defIdx]`.
    Other names are untouched. Models store-after-def + reload-before-use: the value
    occupies its register only at its definition, freeing it everywhere later. -/
def truncateRangeAt (name : String) (lr : LiveRange) : LiveRange :=
  if lr.name = name then ⟨lr.name, lr.defIdx, lr.defIdx⟩ else lr

/-- Footprint-spill an **eviction set** `ev` of names: shorten each evicted name's
    live range to its definition point. The peak-pressure-minimizing rewrite — the
    classical analogue of reversible pebbling (recompute/reload in exchange for a
    smaller simultaneously-live footprint). -/
def footprintSpill (ev : List String) (lrs : List LiveRange) : List LiveRange :=
  lrs.map (fun lr => if ev.contains lr.name then ⟨lr.name, lr.defIdx, lr.defIdx⟩ else lr)

/-! ## 2. Live-range-list-level pressure and peak

`GenericRegAlloc.pressureAt` / `peakPressure` are stated over a block via
`[MachineModel I]` (they call `liveRanges`). The footprint pass is a pure
live-range-to-live-range transform, so we lift the pressure / peak to operate
directly on a `List LiveRange` — the same counting (`defIdx ≤ i ≤ lastUse`), but on
the footprint object the pass rewrites. -/

/-- Register pressure at position `i`: the number of live ranges whose closed
    interval `[defIdx, lastUse]` contains `i`. The `pressureAt` count, on the bare
    live-range list. -/
def lrPressureAt (lrs : List LiveRange) (i : Nat) : Nat :=
  (lrs.filter (fun l => l.defIdx ≤ i ∧ i ≤ l.lastUse)).length

/-- The span the peak is taken over: one past the maximum `lastUse` (every interval
    lies within `[0, span)`), so `lrPeak` ranges over all positions any value is live. -/
def lrSpan (lrs : List LiveRange) : Nat :=
  (lrs.map LiveRange.lastUse).foldl max 0 + 1

/-- Peak register pressure over a live-range list — the maximum simultaneously-live
    count = the minimum spill-free pool size = the peak qubit width in the pebbling
    reading. -/
def lrPeak (lrs : List LiveRange) : Nat :=
  ((List.range (lrSpan lrs)).map (lrPressureAt lrs)).foldl max 0

/-! ## 3. Well-formedness and per-element interval containment

A live range is **well-formed** when `defIdx ≤ lastUse` — every name is read/written
no earlier than it is defined (the `SpillingRegAlloc.sanity_liveranges_wellformed`
invariant the analysis maintains). Under well-formedness, truncating to `[d,d]` keeps
the interval *contained in* the original `[d,l]`, so footprint-spilling can only
remove a value from the live set at a position, never add one. -/

/-- A live-range list is well-formed when every range has `defIdx ≤ lastUse`. -/
def WellFormed (lrs : List LiveRange) : Prop :=
  ∀ lr ∈ lrs, lr.defIdx ≤ lr.lastUse

/-- The footprint-spill map of one well-formed range. -/
def spillOne (ev : List String) (lr : LiveRange) : LiveRange :=
  if ev.contains lr.name then ⟨lr.name, lr.defIdx, lr.defIdx⟩ else lr

/-- `footprintSpill` is the map of `spillOne`. -/
theorem footprintSpill_eq_map (ev : List String) (lrs : List LiveRange) :
    footprintSpill ev lrs = lrs.map (spillOne ev) := rfl

/-- The truncating map shrinks each interval: if a position `i` is live for the
    *rewritten* range, it was live for the original — provided the original was
    well-formed (`defIdx ≤ lastUse`). At a name's def point `d` it stays live;
    everywhere `> d` an evicted name drops out. The per-element interval-containment
    fact behind pointwise pressure non-increase. -/
theorem spillOne_live_imp (ev : List String) (i : Nat) (lr : LiveRange)
    (hwf : lr.defIdx ≤ lr.lastUse)
    (h : (spillOne ev lr).defIdx ≤ i ∧ i ≤ (spillOne ev lr).lastUse) :
    lr.defIdx ≤ i ∧ i ≤ lr.lastUse := by
  unfold spillOne at h
  by_cases hc : ev.contains lr.name
  · simp only [hc, if_true] at h
    -- truncated to [defIdx, defIdx]: i = defIdx, and defIdx ≤ lastUse by hwf
    exact ⟨h.1, Nat.le_trans h.2 hwf⟩
  · simp only [hc, Bool.false_eq_true, if_false] at h
    exact h

/-- `spillOne` preserves a range's `name`. -/
theorem spillOne_name (ev : List String) (lr : LiveRange) :
    (spillOne ev lr).name = lr.name := by
  unfold spillOne; split <;> rfl

/-- `spillOne` preserves a range's `defIdx`. -/
theorem spillOne_defIdx (ev : List String) (lr : LiveRange) :
    (spillOne ev lr).defIdx = lr.defIdx := by
  unfold spillOne; split <;> rfl

/-- For a well-formed range, `spillOne` never grows its `lastUse` (it only
    shortens: an evicted range's `lastUse` drops to `defIdx ≤` the original). -/
theorem spillOne_lastUse_le (ev : List String) (lr : LiveRange)
    (hwf : lr.defIdx ≤ lr.lastUse) :
    (spillOne ev lr).lastUse ≤ lr.lastUse := by
  unfold spillOne
  split
  · exact hwf
  · exact Nat.le_refl _

/-! ## 4. Pointwise pressure non-increase, peak non-increase

The footprint spill never *adds* a value to the live set at any position
(`spillOne_live_imp`), so the per-position pressure can only drop. We prove the
pointwise bound by induction on the live-range list (each surviving rewritten
element maps back to a surviving original element), then lift it to the peak via the
`foldl max` monotonicity already used for `peakPressure`. -/

/-- **Pointwise pressure non-increase.** For a well-formed live-range list, the
    register pressure at every position after footprint-spilling is at most the
    pressure before. The keystone for `footprintSpill_peak_le`. -/
theorem footprintSpill_pressure_le (ev : List String) (lrs : List LiveRange)
    (hwf : WellFormed lrs) (i : Nat) :
    lrPressureAt (footprintSpill ev lrs) i ≤ lrPressureAt lrs i := by
  rw [footprintSpill_eq_map]
  unfold lrPressureAt
  induction lrs with
  | nil => simp
  | cons hd tl ih =>
    have hwf' : WellFormed tl := fun lr hl => hwf lr (List.mem_cons_of_mem _ hl)
    have hwfhd : hd.defIdx ≤ hd.lastUse := hwf hd (List.mem_cons_self ..)
    have ihtl := ih hwf'
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    by_cases hbig : (spillOne ev hd).defIdx ≤ i ∧ i ≤ (spillOne ev hd).lastUse
    · -- rewritten head live at i ⇒ original head live at i too
      have horig : hd.defIdx ≤ i ∧ i ≤ hd.lastUse := spillOne_live_imp ev i hd hwfhd hbig
      rw [if_pos (by simpa using hbig), if_pos (by simpa using horig),
        List.length_cons, List.length_cons]
      exact Nat.succ_le_succ ihtl
    · -- rewritten head dead at i: it is dropped, length unchanged on the left
      rw [if_neg (by simpa using hbig)]
      by_cases horig : hd.defIdx ≤ i ∧ i ≤ hd.lastUse
      · rw [if_pos (by simpa using horig), List.length_cons]
        exact Nat.le_trans ihtl (Nat.le_succ _)
      · rw [if_neg (by simpa using horig)]
        exact ihtl

/-! ### 4b. `foldl max` over a mapped range: the two bounds the peak needs

`lrPeak` is `(List.range n).map f |>.foldl max 0` — the same `foldl max 0` shape as
`GenericRegAlloc.peakPressure`. We need (i) every term is `≤` the fold, and (ii) the
fold is `≤` any common upper bound of the terms. Both are short inductions with a
strengthened accumulator. -/

/-- Generic accumulator bound: `foldl max a l ≤ B` when `a ≤ B` and every element is
    `≤ B`. -/
theorem foldl_max_le {a B : Nat} : ∀ (l : List Nat),
    a ≤ B → (∀ x ∈ l, x ≤ B) → l.foldl max a ≤ B
  | [], ha, _ => ha
  | x :: xs, ha, hx => by
    apply foldl_max_le xs
    · exact Nat.max_le.mpr ⟨ha, hx x (List.mem_cons_self ..)⟩
    · exact fun y hy => hx y (List.mem_cons_of_mem _ hy)

/-- The accumulator only grows: `a ≤ foldl max a l`. -/
theorem le_foldl_max {a : Nat} : ∀ (l : List Nat), a ≤ l.foldl max a
  | [] => Nat.le_refl _
  | x :: xs => Nat.le_trans (Nat.le_max_left a x) (le_foldl_max xs)

/-- Every element is `≤` the fold: `x ∈ l → x ≤ foldl max a l`. -/
theorem mem_le_foldl_max {a : Nat} : ∀ (l : List Nat) (x : Nat),
    x ∈ l → x ≤ l.foldl max a
  | y :: ys, x, hx => by
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact Nat.le_trans (Nat.le_max_right a x) (le_foldl_max ys)
    · exact mem_le_foldl_max ys x h

/-- The peak is an upper bound of the pressure at every position in the span. -/
theorem lrPressureAt_le_lrPeak (lrs : List LiveRange) {i : Nat}
    (hi : i < lrSpan lrs) : lrPressureAt lrs i ≤ lrPeak lrs := by
  apply mem_le_foldl_max
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-! ### 4c. The footprint never grows the span

Truncation only lowers each `lastUse`, so the maximum `lastUse` — hence `lrSpan` — can
only shrink. A position outside the spilled span contributes zero pressure on both
sides, so restricting the peak to the spilled span loses nothing. -/

/-- Footprint-spilling never grows the span (each `lastUse` can only drop). -/
theorem footprintSpill_span_le (ev : List String) (lrs : List LiveRange)
    (hwf : WellFormed lrs) : lrSpan (footprintSpill ev lrs) ≤ lrSpan lrs := by
  unfold lrSpan
  rw [footprintSpill_eq_map]
  refine Nat.succ_le_succ ?_
  -- max over mapped lastUse ≤ max over original lastUse
  apply foldl_max_le
  · exact le_foldl_max _
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨lr, hlr, rfl⟩ := hx
    rw [List.mem_map] at hlr
    obtain ⟨lr0, hlr0, rfl⟩ := hlr
    -- (spillOne ev lr0).lastUse ≤ original max
    have hwf0 : lr0.defIdx ≤ lr0.lastUse := hwf lr0 hlr0
    refine Nat.le_trans (spillOne_lastUse_le ev lr0 hwf0) ?_
    exact mem_le_foldl_max _ _ (List.mem_map.mpr ⟨lr0, hlr0, rfl⟩)

/-! ## 5. Peak non-increase: the deliverable

The classical reversible-pebbling guarantee: footprint-spilling never raises the peak
register/qubit footprint. Bound the spilled peak by its per-position pressures
(`foldl_max_le`), each of which is `≤` the original pressure (`footprintSpill_pressure_le`)
and hence `≤` the original peak (`lrPressureAt_le_lrPeak`) — using that the spilled span
is within the original span (`footprintSpill_span_le`). -/

/-- **Peak-pressure non-increase (the deliverable).** For a well-formed live-range
    list, footprint-spilling any eviction set never grows the peak register pressure —
    the minimum spill-free pool size, equivalently the peak simultaneously-live qubit
    width in the reversible-pebbling reading. The IR-level lever that lowers the
    qubit factor of the ecdsa.fail cost-model product. -/
theorem footprintSpill_peak_le (ev : List String) (lrs : List LiveRange)
    (hwf : WellFormed lrs) :
    lrPeak (footprintSpill ev lrs) ≤ lrPeak lrs := by
  unfold lrPeak
  apply foldl_max_le
  · exact Nat.zero_le _
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [List.mem_range] at hi
    -- pressure(spill, i) ≤ pressure(lrs, i) ≤ peak(lrs)
    refine Nat.le_trans (footprintSpill_pressure_le ev lrs hwf i) ?_
    -- i < lrSpan (spill) ≤ lrSpan lrs, so i is in the original span
    have hi' : i < lrSpan lrs := Nat.lt_of_lt_of_le hi (footprintSpill_span_le ev lrs hwf)
    exact lrPressureAt_le_lrPeak lrs hi'

/-! ## 6. Live-range validity preservation

A placement layered on top of the footprint pass relies on the rewritten ranges
staying well-formed (so the non-overlap discipline of `GenericRegAlloc.linearScan` /
`SpillingRegAlloc.sanity_liveranges_wellformed` still holds) and on each rewritten
range being **contained in** the original (so no value is made live at a position it
was not — the structural soundness side of the pass). -/

/-- **Validity preservation.** Footprint-spilling a well-formed live-range list yields
    a well-formed list (every rewritten range still has `defIdx ≤ lastUse`), and each
    rewritten range is contained in the original (same `name` and `defIdx`, `lastUse`
    only shortened). The structural invariant a placement on top of the pass relies
    on. -/
theorem footprintSpill_valid (ev : List String) (lrs : List LiveRange)
    (hwf : WellFormed lrs) :
    WellFormed (footprintSpill ev lrs) ∧
      ∀ lr ∈ footprintSpill ev lrs, ∃ lr0 ∈ lrs,
        lr.name = lr0.name ∧ lr.defIdx = lr0.defIdx ∧ lr.lastUse ≤ lr0.lastUse := by
  rw [footprintSpill_eq_map]
  refine ⟨?_, ?_⟩
  · intro lr hlr
    rw [List.mem_map] at hlr
    obtain ⟨lr0, hlr0, rfl⟩ := hlr
    -- well-formed: spilled range [d,d] has d ≤ d; untouched range keeps wf
    unfold spillOne
    split
    · exact Nat.le_refl _
    · exact hwf lr0 hlr0
  · intro lr hlr
    rw [List.mem_map] at hlr
    obtain ⟨lr0, hlr0, rfl⟩ := hlr
    exact ⟨lr0, hlr0, spillOne_name ev lr0, spillOne_defIdx ev lr0,
      spillOne_lastUse_le ev lr0 (hwf lr0 hlr0)⟩

/-! ## 7. Demonstrator (testable)

A non-vacuous witness, in the `SpillingRegAlloc` §7/§8 style: a body of 4 names all
live to the end has peak pressure 4; evicting two of them with `footprintSpill` cuts
the peak — the footprint lever actually fires. -/

/-- 4 names defined at indices 0..3 and all last-used at index 4 (the "fan-in"
    shape): all four are simultaneously live at position 4, peak pressure 4. -/
def fanInRanges : List LiveRange :=
  [ ⟨"a", 0, 4⟩, ⟨"b", 1, 4⟩, ⟨"c", 2, 4⟩, ⟨"d", 3, 4⟩ ]

/-- `fanInRanges` is well-formed. -/
theorem fanInRanges_wf : WellFormed fanInRanges := by
  intro lr hlr
  simp only [fanInRanges, List.mem_cons, List.not_mem_nil, or_false] at hlr
  rcases hlr with h | h | h | h <;> subst h <;> decide

/-- Peak pressure of the fan-in body is 4 (all four live at index 4). -/
theorem fanIn_peak : lrPeak fanInRanges = 4 := by native_decide

/-- Footprint-spilling `a` and `b` (truncating their ranges to their def points)
    drops the peak below 4 — the lever fires. -/
theorem fanIn_spill_lowers : lrPeak (footprintSpill ["a", "b"] fanInRanges) < 4 := by
  native_decide

/-- Concretely the peak drops to 2 after evicting `a` and `b`: only `c, d` remain
    live at index 4, so the simultaneously-live footprint halves. -/
theorem fanIn_spill_peak : lrPeak (footprintSpill ["a", "b"] fanInRanges) = 2 := by
  native_decide

end CatCrypt.Crypto.Optimizer.FootprintSpill
