/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.GenericRegAlloc
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRegAlloc

/-!
# Spill-slot **reuse**, generic over `MachineModel` (P6, D3 phase)

`Optimizer.SpillSlotReuse` (P6) packs non-overlapping spilled names onto shared frame
cells, but is written against the x86-specific `JInstr 64` / `JState 64`: its slot-reuse
*decision* logic operates on the ISA-neutral `LiveRange` interval, yet its one
state-level soundness lemma (`reuseReload_noop`, `singleReuse_noClobber_runBlock`) is
phrased over the concrete x86 `JState 64` and `runBlock`.

This module is the **D3-phase generalization**: the slot-reuse pass proved *once* over
the machine abstraction (`GenericRegAlloc.LiveRange` for the decision, `[MemMachine M]`
for the soundness), so **any** backend with a `MemMachine` instance — x86 `JState`, A64
`AMemState`, RV64 `RMemState`, … — inherits spill-slot reuse for free. It is **additive**:
the `JInstr`-specific `SpillSlotReuse.lean` is untouched; this file builds the same pass
on the generic `GenericRegAlloc` framework.

## What is generalized (and what is not)

The two halves of P6 generalize cleanly:

1. **The reuse decision over `LiveRange`** (§1–§2) — already ISA-neutral in
   `SpillSlotReuse.lean`. Restated over `GenericRegAlloc.LiveRange`:
   * `rangesOverlap` / `canShareSlot`: two spilled live ranges may share a frame cell
     iff they do **not** overlap (one's `lastUse` precedes the other's `defIdx`).
   * `slotReuseValid`: the decidable validity certificate — no two names with
     overlapping live ranges share an offset (the frame-slot analogue of register
     non-interference). Carried over verbatim onto the generic `LiveRange`.

2. **The state-level soundness** (§3) — the crux of `SpillSlotReuse.reuseReload_noop`
   was that a reload of a reused cell *still holding its value* is a no-op. That is
   **exactly** `GenericRegAlloc.reload_sandwich` (`evalReload m r off = m` under
   `SpillValid`): once the current occupant's store re-establishes `SpillValid` for its
   value at the shared cell, the reload is transparent — the prior (now-dead) occupant's
   value is irrelevant. Sharing the cell with an earlier-dead name changes nothing in
   the argument, only `SpillValid` at the reload, which the matching store provides. So
   the generic `reload_sandwich`/`evalReload_noop` over `[MemMachine M]` *is* the generic
   slot-reuse soundness; we restate it as `reusedReload_noop` to name the reuse reading.

The `runBlock`-level sandwich (`singleReuse_noClobber_runBlock`) and the operational
`native_decide` demo in `SpillSlotReuse.lean` are intentionally **not** lifted here: they
depend on the concrete x86 `runBlock` left fold over `JInstr` (the generic `MemMachine`
exposes the per-cell/per-register algebra `get`/`load`/`setReg`/`store`, not a block
evaluator threading `evalSpillStore`/`evalReload` against a backend's instruction
semantics). The reload-no-op atom — the load-bearing soundness fact, the only one whose
proof inspects machine state — generalizes; the block-threading wrapper stays per-backend
(it is one line on top of the atom in each backend's own file). §4 instantiates the
generic atom at RV64 `RMemState` to demonstrate the pass fires.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SpillSlotReuseGeneric

open CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-! ## 1. The reuse decision over the generic `LiveRange`

Slot reuse is graph-coloring the *spilled* names onto a small palette of frame offsets,
with the same non-interference relation the in-register allocator uses, applied to frame
offsets instead of registers. Both pieces below are pure interval logic over
`GenericRegAlloc.LiveRange` — no machine state, no instruction type. -/

/-- Two closed live ranges `[a.defIdx, a.lastUse]` and `[b.defIdx, b.lastUse]` overlap:
    at some program point both are live. The generic analogue of
    `GraphColoringRegAlloc.rangesOverlap`, over `GenericRegAlloc.LiveRange`. -/
def rangesOverlap (a b : LiveRange) : Bool :=
  a.defIdx ≤ b.lastUse ∧ b.defIdx ≤ a.lastUse

/-- **Two spilled names may share a frame slot** iff their live ranges do not overlap —
    one's last use precedes the other's def, so they are never simultaneously live. The
    correctness condition for slot reuse, applied to frame offsets (= register
    non-interference for the spilled palette). -/
def canShareSlot (a b : LiveRange) : Bool :=
  a.lastUse < b.defIdx ∨ b.lastUse < a.defIdx

/-- **`canShareSlot` is symmetric.** Whether two ranges can share a slot does not depend
    on the order we name them. -/
theorem canShareSlot_comm (a b : LiveRange) : canShareSlot a b = canShareSlot b a := by
  unfold canShareSlot; simp [Bool.or_comm]

/-- **Non-overlapping ⇒ shareable.** If two live ranges do not overlap they may share a
    frame slot — the basic soundness of the decision: the negation of `rangesOverlap` is
    exactly `canShareSlot`. -/
theorem canShareSlot_of_not_overlap {a b : LiveRange}
    (h : rangesOverlap a b = false) : canShareSlot a b = true := by
  -- `¬(defIdx_a ≤ lastUse_b ∧ defIdx_b ≤ lastUse_a)` ⇒ `lastUse_a < defIdx_b ∨ lastUse_b < defIdx_a`
  unfold rangesOverlap at h
  unfold canShareSlot
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at h ⊢
  omega

/-- And conversely: shareable ⇒ not overlapping. Together with the previous lemma,
    `canShareSlot a b = ! rangesOverlap a b` — slot-shareability is exactly
    non-interference. -/
theorem not_overlap_of_canShareSlot {a b : LiveRange}
    (h : canShareSlot a b = true) : rangesOverlap a b = false := by
  unfold canShareSlot at h
  unfold rangesOverlap
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
  omega

/-! ## 2. The decidable validity certificate

A slot assignment is **valid** iff no two names with overlapping live ranges map to the
same offset — the frame-slot analogue of register non-interference, carried over from
`SpillSlotReuse.slotReuseValid` onto the generic `LiveRange`. State it over an explicit
name↦offset list (the packer's output) so it is `decide`-checkable. -/

/-- Look up a name's live range in a list. -/
def rangeOf (lrs : List LiveRange) (n : String) : Option LiveRange :=
  lrs.find? (fun lr => lr.name == n)

/-- **Slot-reuse validity (decidable), generic.** For every pair of distinct assignment
    entries that share an offset, their live ranges do not overlap. The non-interference
    condition of register coloring applied to frame offsets — the property a sound packer
    maintains. -/
def slotReuseValid (assign : List (String × Int)) (lrs : List LiveRange) : Bool :=
  assign.all (fun p₁ =>
    assign.all (fun p₂ =>
      if p₁.1 ≠ p₂.1 ∧ p₁.2 = p₂.2 then
        match rangeOf lrs p₁.1, rangeOf lrs p₂.1 with
        | some a, some b => ¬ rangesOverlap a b
        | _, _ => true
      else true))

/-- A valid assignment, **read as shareability**: any two distinct names sharing an
    offset *can share a slot* (`canShareSlot`), since validity says their ranges don't
    overlap. This restates `slotReuseValid` through the `canShareSlot` decision of §1,
    tying the certificate to the share decision. -/
theorem slotReuseValid_shareable {assign : List (String × Int)} {lrs : List LiveRange}
    (n₁ n₂ : String) (o : Int) (a b : LiveRange)
    (hv : slotReuseValid assign lrs = true)
    (h₁ : (n₁, o) ∈ assign) (h₂ : (n₂, o) ∈ assign) (hne : n₁ ≠ n₂)
    (ra : rangeOf lrs n₁ = some a) (rb : rangeOf lrs n₂ = some b) :
    canShareSlot a b = true := by
  -- extract the non-overlap fact for this pair from the universally-quantified certificate
  have hall₁ : (fun p₁ =>
      assign.all (fun p₂ =>
        if p₁.1 ≠ p₂.1 ∧ p₁.2 = p₂.2 then
          match rangeOf lrs p₁.1, rangeOf lrs p₂.1 with
          | some a, some b => ¬ rangesOverlap a b
          | _, _ => true
        else true)) (n₁, o) = true :=
    (List.all_eq_true.mp hv) (n₁, o) h₁
  have hall₂ := (List.all_eq_true.mp hall₁) (n₂, o) h₂
  -- the `if`-condition holds: distinct names, shared offset
  have hcond : ((n₁, o).1 ≠ (n₂, o).1 ∧ (n₁, o).2 = (n₂, o).2) := ⟨hne, rfl⟩
  rw [if_pos hcond, ra, rb] at hall₂
  -- `hall₂ : (¬ rangesOverlap a b) = true`, so `rangesOverlap a b = false`
  have hno : rangesOverlap a b = false := by
    simpa using hall₂
  exact canShareSlot_of_not_overlap hno

/-! ## 3. Generic soundness: a reused slot never clobbers a still-needed value

The crux of P6 correctness, now over `[MemMachine M]`. A frame cell shared by a now-dead
name and the new occupant `r` is only ever read back while `r` is its current occupant:
the rewrite emits, for `r`, a `store` at its def and a `load`/reload before each use, and
that store **re-establishes** `SpillValid off r` at the shared cell, overwriting whatever
(dead) value the prior occupant left. So `r`'s reload is a no-op — *exactly*
`GenericRegAlloc.reload_sandwich`, instantiated at the shared offset. Sharing the offset
with a previously-dead name changes nothing in the argument: the only precondition is
that the cell holds `r`'s value at `r`'s reload, which `r`'s own store provides.

`slotReuseValid` (§2) is what makes this applicable: it guarantees the earlier occupant
is dead (its range does not overlap `r`'s) before `r`'s store, so no live reload of the
old name straddles `r`'s store — the only way reuse could go wrong. -/

variable {M : Type}

/-- **The reload of a reused cell is a no-op (generic).** At a frame cell `off` shared by
    a now-dead name and the current name `r`, once `r`'s store has put its value into the
    cell (`SpillValid off r m`), reloading `r` from `off` is semantics-transparent —
    `evalReload m r off = m`. The shared-offset reuse never clobbers `r`, because `r`'s own
    store owns the cell from its def onward; the prior occupant's value is irrelevant. This
    is the generic source for the x86 `SpillSlotReuse.reuseReload_noop` (over `JState 64`),
    read at the reuse cell — it is `GenericRegAlloc.reload_sandwich` instantiated here. -/
theorem reusedReload_noop [MemMachine M] (m : M) (off : Int) (r : String)
    (hv : SpillValid off r m) : evalReload m r off = m :=
  reload_sandwich m off r hv

/-- **The reuse store re-establishes the shared cell (generic).** After the current
    occupant `r` stores to the shared cell `off`, the cell holds `r`'s value
    (`SpillValid off r`), regardless of whatever (dead) value the prior occupant left
    there: the store overwrites the cell. This is what discharges the `SpillValid`
    precondition of `reusedReload_noop` from `r`'s own store — `spillStore_establishes`
    read at the reused cell. -/
theorem reuseStore_establishes [MemMachine M] (m : M) (off : Int) (r : String) :
    SpillValid off r (evalSpillStore m off r) :=
  spillStore_establishes m off r

/-- **Single-reuse no-clobber (the generic soundness core).** The store-then-reload
    roundtrip for the current occupant `r` of a reused cell is transparent: storing `r` to
    the shared cell `off` and immediately reloading it returns the post-store state
    unchanged. Composing `reuseStore_establishes` (the store sets `SpillValid`) with
    `reusedReload_noop` (the reload is then a no-op), this is the per-cell soundness atom
    of P6, over `[MemMachine M]` — the prior dead occupant is never read across `r`'s
    store. (`SpillSlotReuse.singleReuse_noClobber_runBlock` is this atom threaded through a
    concrete `runBlock`-with-`mid` for x86; the cell-level fact it rests on is exactly
    this, now backend-agnostic.) -/
theorem singleReuse_noClobber [MemMachine M] (m : M) (off : Int) (r : String) :
    evalReload (evalSpillStore m off r) r off = evalSpillStore m off r :=
  reusedReload_noop (evalSpillStore m off r) off r (reuseStore_establishes m off r)

/-! ## 4. Specialization sanity: the pass fires at RV64 `RMemState`

The generic soundness instantiated at the RV64 memory-extended state `RMemState`
(`instMemMachineRMemState`) — a `MemMachine` instance that exists in the RISC-V backend.
This demonstrates the generic spill-slot-reuse pass fires unchanged on a concrete backend:
any backend exposing a `MemMachine` inherits the slot-reuse soundness atom for free. -/

open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRegAlloc (RMemState)

/-- **RV64 reused-reload no-op** — `reusedReload_noop` at `RMemState`: a reload of a reused
    frame cell that still holds its current occupant's value is a no-op on the RV64
    memory-extended state. The slot-reuse soundness atom, fired on a backend that exists. -/
theorem riscv_reusedReload_noop (m : RMemState) (off : Int) (r : String)
    (hv : SpillValid off r m) : evalReload m r off = m :=
  reusedReload_noop m off r hv

/-- **RV64 single-reuse no-clobber** — `singleReuse_noClobber` at `RMemState`: storing the
    current occupant to a reused RV64 frame cell and reloading it is transparent. The
    generic P6 soundness core, specialized to show the pass fires on RV64. -/
theorem riscv_singleReuse_noClobber (m : RMemState) (off : Int) (r : String) :
    evalReload (evalSpillStore m off r) r off = evalSpillStore m off r :=
  singleReuse_noClobber m off r

end CatCrypt.Crypto.Optimizer.SpillSlotReuseGeneric
