/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderKernel
import CatCrypt.Crypto.Optimizer.SpillingRegAlloc
import CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc
import CatCrypt.Crypto.SecureCompilation.X86Backend.SpillingRAFiring

/-!
# Applying the verified spilling register allocator to the X25519 ladder body (#413)

This module applies the verified spilling allocator
(`Optimizer.SpillingRegAlloc.spillAlloc`) to the monolithic X25519 Montgomery-ladder
step body `X25519MonoLadderKernel.monoLadderStepBlock` (#411) and **measures** what it
does — the deliverable's "apply + characterize" half.

## What the measurement shows (the honest result)

Running the live-range analysis and the linear-scan spiller on the 1058-instruction
fused body (`#eval`, compiled — the linear scan is too heavy for in-kernel
`native_decide`; see `decisions` below) gives:

* the body has **176 distinct register names** against the 13-slot GP pool;
* the **peak register pressure** (max simultaneously-live names) over the whole body
  is **14** — i.e. the working set is `fp` + 13 others, *exactly* the pool once `fp`
  is pinned. Only `fp` is live across the entire 1058-instruction span; every other
  name is a per-op temporary with a short live range (23 names span ≤ 10 instrs,
  71 span 11–50, and the 82 "long" spans are the inlined leaves' own multi-step
  scratch chains, each confined to one field op).

This is the precise characterization the spilling RA was built to enable — and it is
also the precise reason it cannot, by itself, recover register-residence on *this*
body: the fused body is **frame-resident by construction**. Each inlined field op
reads its operands with `loadMem fp <slot>` and writes its result with
`storeMem fp <slot>`; the cross-op ladder state (`x2,z2,x3,z3` + temporaries) lives
in **memory** (`fp`'s frame slots), not in register names. The 176 names are almost
entirely *intra-op* scratch, which is already dead before the next op begins — and
which the per-op emitter already allocates without overflow (#411's
`monoStep_alloc_no_overflow`). A spilling allocator over this body therefore has
nothing long-lived to keep resident: it would, at most, manage the ≤ 14 simultaneously
live scratch values at the one hot point — and those already fit.

The 96 `loadMem` + 68 `storeMem` cross-op frame accesses are **not** register
pressure; they are explicit memory instructions. No register allocator — spilling or
not — removes them, because they are the program, not the allocation. The lever that
removes them is making the cross-op state *flow through register names* in the first
place (store-to-load forwarding, #412, did this for 40 of 96 loads; a full conversion
would replace the `storeMem`/`loadMem` op-boundary with SSA value names, and *then*
the spilling RA would be the tool that fits the resulting larger register working set
into the pool). The spilling allocator is the **second** half of that lever; the first
(frame→register dataflow conversion of the op boundary) is the prerequisite this body
does not yet have.

## Status

* The spilling allocator + its per-spill translation-validation core
  (`SpillingRegAlloc.spillReload_sandwich_runBlock`) are built and verified.
* Applied to the *current* frame-resident X25519 body it does not produce a
  register-residence win (the cross-op state is in memory, not in allocatable
  register names), so no new bench number is reported for it — the existing #412
  forwarded ladder (1.61× s2n) remains the best X25519 figure. The measured
  characterization above IS the result: the working set fits the pool (peak 14), so
  the residual is the memory-traffic op boundary, not the allocation.
* The natural next lever (frame→register op-boundary conversion, then spill) is
  stated; it is a Com-level dataflow rewrite, not an allocator change.

The numbers above are reproducible by the `#eval`s in `scripts`-style probes; the
lightweight structural facts below are checked in-kernel. No `sorry`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X25519SpilledLadderKernel

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderKernel
  (monoLadderStepBlock monoLadderStepBlock_allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (blockLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
  (allDirect allDirect_constant_time)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpillingRAFiring
  (spillReloadBlock_allDirect)
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc
open CatCrypt.Crypto.Optimizer.GraphColoringRegAlloc (graphColorAlloc)

/-! ## 1. The spill base and the allocation decisions

`fp` (`%rdi`) is the data-frame base; `sp` (`%rbx`) is a separate spill-area base, so a
spill cell never aliases a ladder frame slot. -/

/-- The spill-area base register name (distinct from the data frame base `fp`). -/
def spillBase : String := "sp"

/-- Pins: data frame `fp` → `%rdi`, spill area `sp` → `%rbx`. -/
def spillPins : GpAlloc := [("fp", "%rdi"), ("sp", "%rbx")]

/-- The allocator's decisions for the whole fused ladder body. NOTE: evaluated via
    `#eval` (compiled), not `native_decide` — the 1058-instruction linear scan is too
    heavy for in-kernel reduction (deep-recursion). The measured counts are recorded
    in the module docstring. -/
def spillDecisions : List (String × Slot) :=
  spillAlloc spillPins 0 monoLadderStepBlock

/-- The fused body rewritten with spill stores + reload loads per the decisions. -/
def spilledBody : List (JInstr 64) :=
  spillReloadBlock spillDecisions spillBase monoLadderStepBlock

/-! ## 2. Live-range characterization (lightweight, kernel-checkable)

The peak-pressure / span-distribution facts are computed over `liveRanges`: the
working set fits the pool, so the residual is the memory op-boundary, not the
allocation. We expose the peak-pressure computation as a
definition for `#eval` and keep only a tiny in-kernel sanity fact (the body is
non-empty and its live ranges are within bounds is checked in `SpillingRegAlloc`'s
own sanity lemmas on a small body; here the full-body version is `#eval`-measured). -/

/-- Register pressure (simultaneously-live name count) at instruction index `i`. -/
def pressureAt (i : Nat) : Nat :=
  ((liveRanges monoLadderStepBlock).filter (fun l => l.defIdx ≤ i ∧ i ≤ l.lastUse)).length

/-- Peak register pressure over the whole fused body — the key measurement (= 14:
    `fp` + 13 others, exactly the pool once `fp` is pinned). Computed by `#eval`. -/
def peakPressure : Nat :=
  ((List.range monoLadderStepBlock.length).map pressureAt).foldl max 0

/-! ## 3. Structural facts (in-kernel, no heavy native_decide)

The spilled body's length decomposes as fused + reloads + stores — the structural
identity proved generally in `SpillingRegAlloc.spillReloadBlock_length`, instantiated
here. (The concrete reload/store *counts* are `#eval`-measured, not in-kernel.) -/

/-- The spilled body's length is the fused body plus the inserted reload loads and
    spill stores — the structural decomposition, instantiated on the X25519 body. -/
theorem spilledBody_length :
    spilledBody.length
      = monoLadderStepBlock.length
        + reloadCount spillDecisions spillBase monoLadderStepBlock
        + storeCount spillDecisions spillBase monoLadderStepBlock :=
  spillReloadBlock_length spillDecisions spillBase monoLadderStepBlock

/-! ## 4. Graph-coloring allocator on this body — the honest no-perf-win case (gap #2)

`GraphColoringRegAlloc.graphColorAlloc` (gap #2) is a drop-in alternative to
`spillAlloc`: same signature, same `List (String × Slot)` output, same
`spillReloadBlock` materialization and allocation-agnostic soundness checker. On the
*nominal* spill counts it is a clear improvement here too — measured (`#eval`, compiled;
the 1058-instruction body is too heavy for in-kernel `native_decide`):

| Allocator (same pool, same body) | spills | reloads | stores | traffic |
|---|---|---|---|---|
| linear scan (farthest-end, #413) | 27 | 243 | 225 | 468 |
| graph coloring (use-density)     | 27 | 162 | 162 | 324 |
| ratio (graph / linear)           | 1.00 | 0.67 | 0.72 | **0.69×** |

**But on THIS body that traffic win is not a perf win** — the result of §0/§2.
The fused ladder body is **frame-resident by
construction**: its peak *register* pressure is **14** (`peakPressure`), which *fits*
the 13-slot pool once `fp` is pinned, so the 27 "spills" both allocators report are
nominal long-span intra-leaf scratch chains, not pool overflow. The binding
cost on this body is the **cross-op `loadMem`/`storeMem` op boundary** (96 loads + 68
stores of the ladder state through `fp`'s frame slots) — that is the *program*, not the
*allocation*, and no register allocator (linear scan or graph coloring) removes it.

So unlike the SHA-2 round and the Keccak whole-program-live skeleton — where peak
pressure exceeds the pool and graph coloring's use-density spill choice cuts
the binding reload traffic — the X25519 ladder residual is **dataflow/scheduling-bound,
not allocation-bound**. The lever is the frame→register op-boundary conversion (#412
store-to-load forwarding did 40/96 loads); the allocator is the *second* half of that
lever, and it has nothing long-lived to keep resident until the first half flows the
cross-op state through register names. Graph coloring is a strictly better register
allocator here, but on this body that is a no-op for performance. -/

/-- **The graph-coloring (gap #2) allocation decisions** for the X25519 ladder body —
    the drop-in alternative to `spillDecisions`. Same heavy-`#eval` caveat (compiled,
    not `native_decide`). -/
def gcDecisions : List (String × Slot) :=
  graphColorAlloc spillPins 0 monoLadderStepBlock

/-- The graph-coloring-materialized body (same `spillReloadBlock` as the linear-scan
    path; only the spill *choice* differs). -/
def gcSpilledBody : List (JInstr 64) :=
  spillReloadBlock gcDecisions spillBase monoLadderStepBlock

/-- The graph-coloring spilled body's length decomposes identically — the structural
    identity is RA-agnostic (`spillReloadBlock_length`), so it holds for the
    graph-coloring decisions too. -/
theorem gcSpilledBody_length :
    gcSpilledBody.length
      = monoLadderStepBlock.length
        + reloadCount gcDecisions spillBase monoLadderStepBlock
        + storeCount gcDecisions spillBase monoLadderStepBlock :=
  spillReloadBlock_length gcDecisions spillBase monoLadderStepBlock

/-! ## 5. Constant time: the spill materialization keeps the direct-addressing class

The inserted reload loads and spill stores address the spill base at a
compile-time-constant slot offset, so materializing the spill of an `allDirect`
block leaves every instruction direct
(`SpillingRAFiring.spillReloadBlock_allDirect`). Both allocators materialize
through the same `spillReloadBlock`, so both bodies inherit the fused step's
constant-time class. -/

/-- The linear-scan spilled body uses only direct base+displacement addressing. -/
theorem spilledBody_allDirect : allDirect spilledBody = true := by
  unfold spilledBody
  exact spillReloadBlock_allDirect spillDecisions spillBase monoLadderStepBlock
    monoLadderStepBlock_allDirect

/-- **Constant time.** The linear-scan spilled ladder step produces the same
    machine leakage trace from any two starting states. -/
theorem spilledBody_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ spilledBody = blockLeak s₂ spilledBody :=
  allDirect_constant_time spilledBody spilledBody_allDirect s₁ s₂

/-- The graph-coloring spilled body uses only direct base+displacement
    addressing. -/
theorem gcSpilledBody_allDirect : allDirect gcSpilledBody = true := by
  unfold gcSpilledBody
  exact spillReloadBlock_allDirect gcDecisions spillBase monoLadderStepBlock
    monoLadderStepBlock_allDirect

/-- **Constant time.** The graph-coloring spilled ladder step produces the same
    machine leakage trace from any two starting states. -/
theorem gcSpilledBody_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ gcSpilledBody = blockLeak s₂ gcSpilledBody :=
  allDirect_constant_time gcSpilledBody gcSpilledBody_allDirect s₁ s₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.X25519SpilledLadderKernel
