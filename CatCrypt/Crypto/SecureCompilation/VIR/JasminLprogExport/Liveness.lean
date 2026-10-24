/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.List.Sort.Basic
import all Init.Data.String.Slice
import all Init.Data.String.Search
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import Std.Data.HashMap
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Proofs
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Proofs

/-!
# Point-wise liveness and interference checking of a register assignment

Backward point-wise liveness over the physical slot trace, a Boolean
interference checker for a proposed residence map, and its soundness.

## Main definitions

* `liveOuts`: live-out slot sets of a trace.
* `interferenceOkB`, `InterferenceRespected`: the checker and its property.

## Main results

* `interferenceOk_of_boolB`: soundness of the checker.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ### 7e. Precise point-wise liveness + interference checker (Phase 0 RA TV)

The `PhysNoCollision` check above (`physSummary` / `physRangesOverlap`) uses the
**conservative interval** liveness `[firstTouch, lastTouch]`: a slot is treated
as live across the entire span between its first and last touch. That interval
is sound for the fresh-SSA per-binding trace (each SSA name is touched in one
contiguous window) but is **wrong for a residence-collapsed body**: a residence
class such as `sc0` / `prod1` / a lane is touched all over the permutation, so
its interval spans nearly the whole body and would spuriously interfere with
everything — the interval check cannot tell the *aliasing* collapse (two values
that must coexist mapped onto one class) from a *legitimate* in-place reuse.

This block adds the **precise point-wise gen/kill** liveness used by a real
register allocator and a translation-validation interference checker that runs
on the *fresh-SSA* trace against a **proposed** logical→physical map `ρ`
(e.g. `residenceArraySlotOf (slotTraceArr ())`). The body is straight-line (a
let-chain, no control flow), so liveness is a single backward pass:

  `live_in[i]  = (live_out[i] \ {wr i}) ∪ rds i`
  `live_out[i] = live_in[i+1]`,    `live_out[last] = ∅`.

The checker rejects a map `ρ` iff at some point two *distinct* fresh-SSA slots
that are simultaneously live (or a def vs. a slot live just after it) are mapped
to the **same** physical/residence class — exactly the
two-address side-condition `dst ≠ src1` of `twoAddr_denote`, lifted to "no two
coexisting logical values share a register". -/

/-- Per-event **live-out** sets of a straight-line `PhysEvent` trace, in program
    order: `liveOuts tr` has the same length as `tr`, and its `i`-th entry is the
    set of slots live immediately *after* event `i` (= live-in of event `i+1`,
    `∅` after the last event). Computed by one backward pass:
    threading the running live-in set right-to-left, each event prepends its own
    live-out (the successor's live-in) to the result.

    Returns the pair `(liveInOfHead, liveOuts)`; `liveInOfHead` is the set live
    before the first event (only needed internally to seed the recursion). -/
def liveAux : List PhysEvent → List Nat × List (List Nat)
  | [] => ([], [])
  | ev :: rest =>
      let (succIn, outsRest) := liveAux rest
      -- live-out of `ev` is the live-in of its successor (`succIn`), `∅` if last.
      let liveOutEv := succIn
      -- live-in of `ev` = (live-out \ {def}) ∪ uses.
      let liveInEv := (liveOutEv.filter (· != ev.wr)) ++ ev.rds
      (liveInEv, liveOutEv :: outsRest)

/-- **Compiled** live-out pass: a rolling array of "next-use distance" is avoided
    in favour of a rolling *live set* carried as a `Std.HashMap Nat Unit` (a slot
    set), updated event-by-event from the END of the trace. For each event we
    snapshot the current live set as that event's live-out, then apply gen/kill
    (`kill def`, `gen uses`) to obtain the predecessor's live set. The set stays
    ≤ K (the max number of simultaneously-live residence classes — 25 for
    Poseidon2), so each step is `O(K)` and the whole pass is `O(n·K)` with no
    per-point materialization beyond the snapshot list. Mirrors
    `physLiveDataImpl`'s single-array discipline (build-cost precedent);
    handles the 107k-binding body without stack overflow (tail-accumulating). -/
@[inline] def liveOutsImpl (tr : List PhysEvent) : List (List Nat) := Id.run do
  -- Walk events from last to first over the reversed list (no indexed access,
  -- so no `Inhabited PhysEvent` is needed). `live` is the live-in of the
  -- successor event = live-out of the current event; snapshot it, then apply
  -- kill (def) / gen (uses) to obtain the predecessor's live-in. Prepending the
  -- snapshots while walking the reversed trace yields program order directly.
  let mut live : Std.HashMap Nat Unit := {}
  let mut outs : List (List Nat) := []
  for ev in tr.reverse do
    outs := live.keys :: outs          -- live-out of this event
    live := live.erase ev.wr           -- kill def
    for u in ev.rds do                 -- gen uses
      live := live.insert u ()
  return outs

/-- The per-event live-out sets of a trace (length = `tr.length`). The pure spec
    uses the structural backward recursion `liveAux`; `@[implemented_by]` swaps
    in the rolling-set array pass `liveOutsImpl` for native execution on the
    107k-binding body (no per-point stack frame, no super-linear set copies). -/
@[implemented_by liveOutsImpl]
def liveOuts (tr : List PhysEvent) : List (List Nat) := (liveAux tr).2

/-- The proposed-map interference predicate at one point: among the slots in a
    live set `ls`, no two *distinct* slots are mapped by `ρ` to the same class.
    Callers pass `wr i :: live_out[i]` so the def-clobbers-live-out edge is
    included. -/
def liveSetInterferenceOkB (ρ : Nat → Nat) (ls : List Nat) : Bool :=
  ls.all (fun a => ls.all (fun b => if a == b then true else ρ a != ρ b))

/-- **Interference checker** for a proposed logical→physical map `ρ` over the
    straight-line fresh-SSA trace `tr`. For every program point `i` the slots
    that are simultaneously live (the def `wr i` together with `live_out[i]`)
    must receive pairwise-distinct images under `ρ`. The def is included in the
    live set at its own point precisely so the **def-clobbers-live-out** edge is
    checked: if `wr i`'s residence class collides with a *different* value still
    live after `i`, the destructive write would clobber it — this is the edge
    that catches the Poseidon2 MDS lane/scratch aliasing.

    `true` ⇒ `ρ` is interference-respecting (sound, see `interferenceOk_of_boolB`).
    `false` ⇒ a real conflicting pair exists at some point. -/
def interferenceOkB (tr : List PhysEvent) (ρ : Nat → Nat) : Bool :=
  (tr.zip (liveOuts tr)).all (fun p =>
    let ev := p.1
    let lo := p.2
    liveSetInterferenceOkB ρ (ev.wr :: lo))

/-- The proposition the Boolean checker decides: at every program point, the
    def together with the live-out slots receive pairwise-distinct `ρ`-images. -/
def InterferenceRespected (tr : List PhysEvent) (ρ : Nat → Nat) : Prop :=
  ∀ p ∈ tr.zip (liveOuts tr),
    ∀ a ∈ (p.1.wr :: p.2), ∀ b ∈ (p.1.wr :: p.2), a ≠ b → ρ a ≠ ρ b

/-- **Soundness bridge**: the Boolean interference checker implies the
    `InterferenceRespected` proposition. Mirrors `physNoCollision_of_boolB`. -/
theorem interferenceOk_of_boolB (tr : List PhysEvent) (ρ : Nat → Nat)
    (h : interferenceOkB tr ρ = true) : InterferenceRespected tr ρ := by
  intro p hp a ha b hb hne
  have hpoint := List.all_eq_true.mp h p hp
  -- `hpoint : liveSetInterferenceOkB ρ (p.1.wr :: p.2) = true`
  simp only [liveSetInterferenceOkB] at hpoint
  have ha' := List.all_eq_true.mp hpoint a ha
  have hb' := List.all_eq_true.mp ha' b hb
  by_cases heq : a == b
  · simp only [beq_iff_eq] at heq; exact absurd heq hne
  · simp only [heq, Bool.false_eq_true, ite_false] at hb'
    simpa [bne, beq_iff_eq] using hb'

/-! ### 7f. The fresh-SSA trace and the proposed residence map

To run the checker against a residence proposal `slotOfBinding`, the *fresh-SSA*
trace (one unique slot per binding) is paired with the map
`ρ = slotOfBinding ∘ (slot → binding-ordinal)`. For the canonical
first-appearance slot indexing of `bodyTrace`, the def slot of the `n`-th
`Lopn` is its own first-appearance rank; the proposed map sends that rank to the
residence class `slotOfBinding n`. The helper below builds `ρ` as an `Array`
lookup keyed by def-slot for the common case where slot = binding ordinal (true
for the fresh-SSA export, where each binding introduces exactly one new name).
-/

/-- The proposed logical→physical map as an array keyed by fresh-SSA def-slot:
    `ρ s = slots[s]` (identity outside the residence universe). For the
    fresh-SSA Poseidon2 trace the `n`-th def slot is `n`, so this is exactly
    `residenceArraySlotOf (slotTraceArr ())`. -/
def proposedRho (slots : Array Nat) : Nat → Nat := residenceArraySlotOf slots

/-- **Identity (fresh-SSA) allocation is always interference-respecting.** With
    `ρ = id` distinct slots never collide, so the checker accepts every trace —
    confirming the checker is not vacuously `false`. -/
theorem interferenceOkB_id (tr : List PhysEvent) : interferenceOkB tr id = true := by
  simp only [interferenceOkB, liveSetInterferenceOkB, List.all_eq_true]
  intro p _ a _ b _
  by_cases h : a == b
  · simp [h]
  · have hf : (a == b) = false := by simpa using h
    simp only [hf, Bool.false_eq_true, ite_false, id_eq, bne, Bool.not_false]

/-! ### 7g. Phase-0 demonstration witnesses

A *correct* fresh-SSA fragment (distinct slot per def, identity map) is accepted,
and a small fragment reproducing the **MDS lane/scratch aliasing pattern** of
`Poseidon2WholePermCom.recApplyMat4` / `recColSums` is REJECTED by the proposed
residence map. The pattern: two distinct logical values are simultaneously live
(e.g. a product `prod1` accumulated while a lane value is still needed) yet the
residence proposal maps both onto the same class — the def of one clobbers the
other before its last use. -/

/-- A 4-binding **correct** fragment: slot 0 read by 1, slot 1 read by 2, etc. —
    no two coexisting values share a slot. Identity map accepts it. -/
def demoTraceOk : List PhysEvent :=
  [ { wr := 0, rds := [] },
    { wr := 1, rds := [0] },
    { wr := 2, rds := [1] },
    { wr := 3, rds := [2, 1] } ]

/-- A fragment reproducing the MDS aliasing: binding 0 defines value `A` (slot 0),
    binding 1 defines value `B` (slot 1); binding 2 reads BOTH `A` and `B`
    (so both are live after binding 1), and binding 3 also reads both — both `A`
    and `B` are simultaneously live across bindings 1–3. A residence proposal
    that coalesces slot 0 and slot 1 onto the same class is unsound here. -/
def demoTraceAlias : List PhysEvent :=
  [ { wr := 0, rds := [] },
    { wr := 1, rds := [] },
    { wr := 2, rds := [0, 1] },
    { wr := 3, rds := [0, 1] } ]

/-- The aliasing residence proposal: collapse slots 0 and 1 onto class 0. -/
def demoRhoAlias : Array Nat := #[0, 0, 2, 3]

/-- **Sanity (positive):** the correct fresh-SSA fragment is accepted under the
    identity map. -/
theorem demoTraceOk_accepts : interferenceOkB demoTraceOk id = true := by
  decide

/-- **Phase-0 reject demonstration (small witness):** the precise point-wise
    checker REJECTS the residence proposal that coalesces two simultaneously-live
    values — the exact MDS-aliasing shape from `recApplyMat4`/`recColSums`. The
    conservative-interval `physNoCollisionB` cannot express this rejection;
    the point-wise checker does. -/
theorem demoTraceAlias_rejects :
    interferenceOkB demoTraceAlias (proposedRho demoRhoAlias) = false := by
  decide

/-- **Phase-0 reject demonstration (positive control):** the SAME aliasing trace
    is ACCEPTED by the identity (fresh-SSA) map — so the rejection above is
    caused by the residence proposal, not by the trace being intrinsically
    unallocatable. -/
theorem demoTraceAlias_id_accepts : interferenceOkB demoTraceAlias id = true := by
  decide

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
