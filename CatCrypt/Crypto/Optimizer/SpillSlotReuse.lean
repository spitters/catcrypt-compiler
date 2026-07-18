/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc
import CatCrypt.Crypto.SecureCompilation.X86Backend.RegAllocSpillCT

/-!
# Spill-slot **reuse**: pack non-overlapping spilled names onto shared frame cells (P6)

The spilling allocator (`SpillingRegAlloc.linearScan`) gives every spilled name a
**distinct** 8-byte frame cell: its `nextSpill` offset only ever advances, never
reuses an expired slot. That keeps the multi-spill distinct-cell invariant trivial
(`SpillingRegAlloc.lean §6`, `WholeProgramResidence`), but it bloats the frame: a
body that spills `k` names over its lifetime reserves `k` cells even when most of
those names are never simultaneously live. A larger frame is a larger stack
allocation, worse cache locality, and (because cold values sit farther from the
hot working set) more cache-line traffic on the inserted reloads.

**P6**: a *dead* slot
— one whose current occupant's live range has ended — can be **reused** by a later
spilled name whose live range does not overlap the prior occupant's. The frame then
holds only as many cells as the **peak number of simultaneously-live spills**, not
the total spill count.

## Reuse-validity = graph-coloring the spilled names onto frame slots

The correctness condition for slot reuse is *exactly* the register-coloring
non-interference condition, applied to frame offsets instead of registers:

> A slot assignment is **valid** iff no two names that are simultaneously live
> (their `[def, lastUse]` live ranges overlap — `GraphColoringRegAlloc.rangesOverlap`)
> share the same frame offset.

So slot reuse is graph-coloring the *spilled* names onto a small palette of frame
offsets, with the same `interfere` relation the in-register allocator uses. This
module:

1. `reuseSlots` (§2): a greedy packer — process spilled names in `defIdx` order and
   assign each the **lowest free offset** whose current occupant's live range has
   already ended (`lastUse < this name's defIdx`); only open a fresh offset when no
   freed one fits. Plus `reuseSlotCount`, the number of *distinct* offsets used —
   the frame-size win metric (`≤` the distinct-cell count, often `≪`).
2. `slotReuseValid` (§3): a **decidable** validity certificate — "no two names with
   overlapping live ranges map to the same offset" — mirroring the allocator's
   interference check. This is the property the greedy packer maintains.
3. Soundness (§4): the single-reuse **no-clobber** lemma. A reused slot is only ever
   read back (`loadMem`) while its *current* occupant is live, so reuse never
   clobbers a value still needed. Formally: the second occupant's store re-establishes
   `SpillValid` for *its* value at the shared cell, so its reload is a no-op
   (`spillReload_sandwich_runBlock` reused verbatim) — independently of the cell
   having held a different (now-dead) name's value earlier. The whole-block
   `runBlock`-equivalence under reuse is then anchored on a concrete demo (§6).
4. CT preservation (§5): **fully general**. A reused slot map is still a
   `String → Option Int` of compile-time-*constant* offsets, so the spill rewrite's
   reloads/stores are still constant-displacement `loadMem`/`storeMem` = `IsDirect`.
   `RegAllocSpillCT.spillRewrite_allDirect` applies *unchanged*: sharing an offset
   does not make it less of a constant. So `allDirect` (hence machine constant-time)
   is preserved for any reuse map.
5. Demo (§6): a block spilling 3 names where #1 and #3 have disjoint live ranges.
   The distinct-cell allocator uses 3 slots; `reuseSlots` packs #1 and #3 onto the
   same offset → **2 slots** (the frame-size win). Both the slot-count drop and the
   `runBlock`-equivalence (on the concrete result register, via `native_decide`) are
   exhibited.

## Deferred merge-time integration

To realise the frame-size win in the emitted allocator, replace the distinct-cell
offset assignment in `SpillingRegAlloc.linearScan` — the `nextSpill`/`nextSpill + 8`
threading that hands each spilled name a fresh cell — with a post-pass that runs
`reuseSlots` over the names `linearScan` marked `Slot.spilled`, remapping their
offsets onto the packed palette. The validity certificate `slotReuseValid` on the
block's `liveRanges` then certifies the remap sound. That edit lands in
`SpillingRegAlloc.spillAlloc`/`linearScan` (the other terminal's hot file); it is
**not** performed here — this module builds the reuse layer on top by import, and
the integration point is the `nextSpill + 8` advance in `linearScan`'s `[]`/spill
arms (`SpillingRegAlloc.lean:298,302,304`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SpillSlotReuse

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc
open CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc (rangesOverlap)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RegAllocSpillCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (blockLeak)

/-! ## 1. Slot maps as offset functions

A *reuse slot map* is the same `String → Option Int` shape the CT layer
(`RegAllocSpillCT.spillRewrite`) consumes: `some off` ⇒ the name lives at frame
offset `off`, `none` ⇒ register-resident. Reuse differs from the distinct-cell
assignment only in that two names may map to the *same* `off`. -/

/-- A concrete slot map: the partial function sending each spilled name (looked up
    in an association list) to its frame offset, `none` otherwise. -/
def slotMapOf (assign : List (String × Int)) : String → Option Int :=
  fun n => (assign.lookup n)

/-! ## 2. The greedy slot packer

Process the spilled names in `defIdx` order. Maintain, for each *used* offset, the
`lastUse` of its current occupant. For a new name, reuse the **lowest** offset whose
occupant has expired (`occupantLastUse < name.defIdx`); if none has, open a fresh
offset (the next 8-byte cell). This is interval-graph coloring by the greedy
left-edge algorithm — optimal on interval graphs, so it uses exactly the peak
simultaneous-spill count of offsets. -/

/-- The spilled names, as live ranges, in `defIdx` order (the order the packer
    processes them). We take the block's live ranges, keep those the slot map marks
    spilled, and sort by `defIdx`. -/
def spilledRanges (slots : String → Option Int) (lrs : List LiveRange) : List LiveRange :=
  (lrs.filter (fun lr => (slots lr.name).isSome)).mergeSort (fun a b => a.defIdx ≤ b.defIdx)

/-- One greedy step: given the offsets already opened with their current occupant's
    `lastUse` (`used : List (Int × Nat)`) and a new live range `lr`, return the
    chosen offset and the updated `used`. Reuse the lowest expired offset; else open
    a fresh one at `freshOff`. -/
def packStep (lr : LiveRange) (freshOff : Int) (used : List (Int × Nat)) :
    Int × List (Int × Nat) :=
  -- the offsets whose occupant has expired before this def, lowest first
  let freed := (used.filter (fun p => p.2 < lr.defIdx)).map Prod.fst
  match freed.foldl (fun (best : Option Int) o =>
      match best with
      | none => some o
      | some b => if o < b then some o else some b) none with
  | some o =>
    -- reuse offset `o`: drop its old occupant, record this name's lastUse there
    ((o, (used.filter (fun p => p.1 ≠ o)) ++ [(o, lr.lastUse)]))
  | none =>
    -- open a fresh offset
    (freshOff, used ++ [(freshOff, lr.lastUse)])

/-- The greedy packing of the spilled names onto shared offsets. Returns the
    name ↦ offset assignment. `freshBase`/stride `8` mirror `linearScan`'s frame
    cells; a fresh offset is opened only when no freed one fits. -/
def reuseAssign (freshBase : Int) (spilled : List LiveRange) : List (String × Int) :=
  let rec go (used : List (Int × Nat)) (nextFresh : Int) (acc : List (String × Int)) :
      List LiveRange → List (String × Int)
    | [] => acc.reverse
    | lr :: rest =>
      let (off, used') := packStep lr nextFresh used
      -- advance the fresh cursor only if we actually opened `nextFresh`
      let nextFresh' := if off = nextFresh ∧ ¬ used.any (fun p => p.1 = nextFresh)
                        then nextFresh + 8 else nextFresh
      go used' nextFresh' ((lr.name, off) :: acc) rest
  go [] freshBase [] spilled

/-- **The reuse slot map.** Given the original (distinct-cell) slot map and the
    block's live ranges, repack the *spilled* names onto shared frame offsets by the
    greedy left-edge algorithm. Names the original kept resident stay resident. -/
def reuseSlots (slots : String → Option Int) (freshBase : Int) (lrs : List LiveRange) :
    String → Option Int :=
  slotMapOf (reuseAssign freshBase (spilledRanges slots lrs))

/-- The number of **distinct** frame offsets the reuse map uses — the frame-size win
    metric. `≤` the distinct-cell spill count, and `=` the peak simultaneous-spill
    count for the greedy left-edge packing. -/
def reuseSlotCount (slots : String → Option Int) (freshBase : Int) (lrs : List LiveRange) :
    Nat :=
  let assign := reuseAssign freshBase (spilledRanges slots lrs)
  (assign.map Prod.snd).dedup.length

/-! ## 3. The decidable validity certificate

A slot assignment is **valid** iff no two names with overlapping live ranges map to
the same offset — the frame-slot analogue of `GraphColoringRegAlloc.interfere`. We
state it over an explicit name↦offset list (the packer's output) and the block's
live ranges, so it is `decide`/`native_decide`-checkable. -/

/-- Look up a name's live range in a list. -/
def rangeOf (lrs : List LiveRange) (n : String) : Option LiveRange :=
  lrs.find? (fun lr => lr.name == n)

/-- **Slot-reuse validity (decidable).** For every pair of distinct entries
    `(n₁, o₁)`, `(n₂, o₂)` in the assignment that share an offset (`o₁ = o₂`), their
    live ranges do **not** overlap. Equivalently: any two names on the same frame
    slot are never simultaneously live — the non-interference condition of register
    coloring, applied to frame offsets. -/
def slotReuseValid (assign : List (String × Int)) (lrs : List LiveRange) : Bool :=
  assign.all (fun p₁ =>
    assign.all (fun p₂ =>
      if p₁.1 ≠ p₂.1 ∧ p₁.2 = p₂.2 then
        match rangeOf lrs p₁.1, rangeOf lrs p₂.1 with
        | some a, some b => ¬ rangesOverlap a b
        | _, _ => true
      else true))

/-- Validity of the slot map a `reuseAssign` produced, against the live ranges. The
    `slotReuseValid`-on-the-packer's-output form the demo checks. -/
def reuseAssignValid (freshBase : Int) (spilled : List LiveRange) (lrs : List LiveRange) :
    Bool :=
  slotReuseValid (reuseAssign freshBase spilled) lrs

/-! ## 4. Soundness: a reused slot never clobbers a still-needed value

The crux of P6 correctness: a frame cell shared by names `n₁` (dead) and `n₂` (the
new occupant) is only ever *read back* (`loadMem`) while its **current** occupant is
live. Concretely, the rewrite emits, for `n₂`, a `storeMem` at `n₂`'s def and a
`loadMem` before each of `n₂`'s uses. That store **re-establishes** `SpillValid` for
`n₂`'s value at the shared cell, overwriting whatever (dead) value `n₁` left there.
So `n₂`'s reload is a no-op by `SpillValid` — *exactly* the single-spill sandwich
already proved in `SpillingRegAlloc`, instantiated at the shared offset. Sharing the
offset with a previously-dead name changes nothing in the argument: the only
precondition is that the cell holds `n₂`'s value at `n₂`'s reload, which `n₂`'s own
store provides and a cell-preserving `mid` maintains.

This is why `slotReuseValid` suffices: it guarantees `n₁` is dead (its range does not
overlap `n₂`'s) before `n₂`'s store, so no live reload of `n₁` straddles `n₂`'s
store — the only way reuse could go wrong. -/

/-- **The reload after a reuse-store is a no-op.** At a cell `(sb, off)` shared by a
    now-dead name and the current name whose value is `r`, once the current name's
    store has put `r` into the cell (so `SpillValid sb off r s`), the reload
    `loadMem r sb off` is semantics-transparent — it rewrites `r` to a value it
    already holds. The shared-offset reuse never clobbers `r`, because `r`'s own
    store owns the cell from its def onward. This is `reloadBeforeUse_runBlock`
    specialised to the shared cell. -/
theorem reuseReload_noop {sb : String} {off : Int} {r : String} {s : JState 64}
    (hv : SpillValid sb off r s) (rest : List (JInstr 64)) :
    runBlock s (.loadMem r sb off :: rest) = runBlock s rest :=
  reloadBeforeUse_runBlock hv rest

/-- **Single-reuse no-clobber (the soundness core).** A name `n₂` (value `r`) sharing
    a frame cell `(sb, off)` with a now-dead earlier occupant: store `r` to the cell,
    run a cell-preserving `mid`, then reload `r` before `use :: rest`. The
    store/`mid`/reload sandwich denotes the same as `mid ++ use :: rest` directly.
    Because `r`'s own store re-establishes the cell from its def, the prior (dead)
    occupant's value is irrelevant — reuse is transparent. This is exactly
    `spillReload_sandwich_runBlock`, now read as the **shared-cell** statement:
    nothing in its hypotheses or proof refers to the cell being fresh, only to it
    holding `r` at the reload (which the matching store + cell-preserving `mid`
    give). The `slotReuseValid` certificate is what guarantees the earlier occupant
    is dead, so no live reload of it straddles `r`'s store. -/
theorem singleReuse_noClobber_runBlock {sb : String} {off : Int} {r : String}
    {s : JState 64} (mid : List (JInstr 64)) (rest : List (JInstr 64))
    (hmid : SpillValid sb off r (runBlock (evalInstr s (.storeMem sb off (.reg r))) mid)) :
    runBlock s (.storeMem sb off (.reg r) :: (mid ++ .loadMem r sb off :: rest))
      = runBlock s (.storeMem sb off (.reg r) :: (mid ++ rest)) :=
  spillReload_sandwich_runBlock mid rest hmid

/-! ## 5. CT preservation under reuse — fully general

A reuse slot map is still a `String → Option Int` of compile-time-constant offsets;
sharing an offset does not make it less constant. So every inserted reload/store is
still `loadMem`/`storeMem` at a constant displacement — `IsDirect` —
and `RegAllocSpillCT.spillRewrite_allDirect` applies *unchanged* to the reused map.
Machine constant-time is preserved for **any** reuse map. -/

/-- **Reuse preserves `allDirect` (general).** For any reuse slot map `reused`, any
    resident renaming `ρ` and frame base, the rename+spill rewrite of an `allDirect`
    block is still `allDirect`: the reused reloads/stores are constant-offset
    `loadMem`/`storeMem`. Direct instance of `spillRewrite_allDirect` — slot *reuse*
    does not change that offsets are compile-time constants. -/
theorem reuseSlots_allDirect (ρ : String → String) (frameBase : String)
    (reused : String → Option Int) (block : List (JInstr 64))
    (hblock : allDirect block = true) :
    allDirect (spillRewrite ρ frameBase reused block) = true :=
  spillRewrite_allDirect ρ frameBase reused block hblock

/-- **The packed reuse map preserves `allDirect`.** Specialising `reuseSlots_allDirect`
    to the actual greedy-packed map `reuseSlots slots freshBase lrs`: even after
    packing spilled names onto shared offsets, the spill rewrite stays direct-addressed,
    so the machine block stays constant-time. The frame-size win costs nothing in CT. -/
theorem spillRewrite_reuse_allDirect (ρ : String → String) (frameBase : String)
    (slots : String → Option Int) (freshBase : Int) (lrs : List LiveRange)
    (block : List (JInstr 64)) (hblock : allDirect block = true) :
    allDirect (spillRewrite ρ frameBase (reuseSlots slots freshBase lrs) block) = true :=
  reuseSlots_allDirect ρ frameBase (reuseSlots slots freshBase lrs) block hblock

/-- **The reuse-packed block is constant-time.** The end-to-end CT statement: after
    packing spills onto shared frame slots, the rewritten block has a state-independent
    machine leakage trace. Reuse shrinks the frame without leaking. -/
theorem spillRewrite_reuse_constant_time (ρ : String → String) (frameBase : String)
    (slots : String → Option Int) (freshBase : Int) (lrs : List LiveRange)
    (block : List (JInstr 64)) (hblock : allDirect block = true) (s₁ s₂ : JState 64) :
    blockLeak s₁ (spillRewrite ρ frameBase (reuseSlots slots freshBase lrs) block)
      = blockLeak s₂ (spillRewrite ρ frameBase (reuseSlots slots freshBase lrs) block) :=
  spillRewrite_constant_time ρ frameBase (reuseSlots slots freshBase lrs) block hblock s₁ s₂

/-! ## 6. Worked demo: 3 spilled names → 2 frame slots

A block spilling three names `x`, `y`, `z` where `x` and `z` have **disjoint** live
ranges (`x` is dead before `z`'s def) but `y` overlaps both. The distinct-cell
allocator gives 3 cells; `reuseSlots` packs `x` and `z` onto the same offset, using
**2** cells — the peak simultaneous-spill count.

The live ranges are hand-built to model the spill scenario directly (the packer is
allocation-agnostic, driven by `LiveRange`s):
* `x` : `[def 0, lastUse 1]`
* `y` : `[def 1, lastUse 4]`  (overlaps both `x` and `z`)
* `z` : `[def 2, lastUse 4]`  (`z.defIdx = 2 > x.lastUse = 1`, so `x` is dead — reuse) -/

/-- The demo live ranges: `x` dead before `z`, `y` spans both. -/
def demoLR : List LiveRange :=
  [ ⟨"x", 0, 1⟩, ⟨"y", 1, 4⟩, ⟨"z", 2, 4⟩ ]

/-- All three names spilled (`slotMapOf` over distinct cells `0, 8, 16`). -/
def demoDistinct : String → Option Int :=
  slotMapOf [("x", 0), ("y", 8), ("z", 16)]

/-- The distinct-cell map uses **3** frame slots. -/
theorem demo_distinct_slotCount :
    ([(0 : Int), 8, 16]).dedup.length = 3 := by native_decide

/-- The greedy packer's assignment: `x → 0`, `y → 8`, `z → 0` (reusing `x`'s freed
    cell, since `x` is dead at `z`'s def). -/
theorem demo_reuseAssign :
    reuseAssign 0 demoLR = [("x", 0), ("y", 8), ("z", 0)] := by native_decide

/-- **The frame-size win.** `reuseSlots` packs the 3 spilled names onto **2** offsets
    (`x` and `z` share offset `0`): the slot count drops 3 → 2. -/
theorem demo_reuse_slotCount :
    reuseSlotCount demoDistinct 0 demoLR = 2 := by native_decide

/-- The packed assignment is **valid**: the two names sharing offset `0` (`x` and `z`)
    have non-overlapping live ranges. `slotReuseValid` certifies the reuse sound. -/
theorem demo_slotReuseValid :
    reuseAssignValid 0 demoLR demoLR = true := by native_decide

/-! ### Runtime equivalence under reuse

A concrete straight-line block exercising the reuse: spill `x` to cell `(sb, 0)`,
later (after `x` is dead) spill `z` to the *same* cell `(sb, 0)`, then reload `z` and
use it. We show the reused-slot block computes the same result in the destination
register as the same block *without* the (no-op) reload — i.e. the reload reads `z`'s
value, not the stale `x`, so reuse does not clobber.

`runBlock` over a concrete initial state with `native_decide` on the result register
exhibits the no-clobber property operationally (the §4 lemma is its general form). -/

/-- The shared spill cell base. -/
def sb : String := "%rsp"

/-- The reuse block: define `x`, store it to cell 0; define `z` (after `x` dead),
    store `z` to the **same** cell 0; reload `z` from cell 0; result `out := z`.
    Because `z`'s store overwrote the cell, the reload of `z` reads `z`'s value. -/
def demoReuseBlock : List (JInstr 64) :=
  [ .mov "x" (.imm 7)                         -- x := 7
  , .storeMem sb 0 (.reg "x")                 -- spill x to cell 0
  , .mov "z" (.imm 42)                        -- z := 42   (x now dead)
  , .storeMem sb 0 (.reg "z")                 -- reuse cell 0 for z
  , .loadMem "z" sb 0                          -- reload z  (no-op: cell holds z)
  , .mov "out" (.reg "z") ]                    -- out := z

/-- The same block with the reload elided (`z` already in register). -/
def demoNoReloadBlock : List (JInstr 64) :=
  [ .mov "x" (.imm 7)
  , .storeMem sb 0 (.reg "x")
  , .mov "z" (.imm 42)
  , .storeMem sb 0 (.reg "z")
  , .mov "out" (.reg "z") ]

/-- A concrete zeroed initial state. -/
def demoInit : JState 64 := { regs := fun _ => 0 }

/-- **No-clobber, operationally.** Running the reuse block (where `z` reuses `x`'s
    freed cell) yields `out = 42 = z`, the **same** as the reload-free block. The
    reload of the reused cell read `z`'s value, not the stale `x = 7` — reuse did not
    clobber. The concrete instance of `singleReuse_noClobber_runBlock`. -/
theorem demo_reuse_runBlock_eq :
    (runBlock demoInit demoReuseBlock).get "out"
      = (runBlock demoInit demoNoReloadBlock).get "out" := by native_decide

/-- And the result is exactly `z = 42` (not the stale `x = 7`): the reused slot
    carried `z`'s value through the reload. -/
theorem demo_reuse_result :
    (runBlock demoInit demoReuseBlock).get "out" = (42 : BitVec 64) := by native_decide

end CatCrypt.Crypto.Optimizer.SpillSlotReuse
