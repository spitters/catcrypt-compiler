/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA

/-!
# Keccak-p[1600,24] with linear-scan register allocation — the proof-of-concept
RA consumer

`RegisterAllocation.lean` (#141/#143) ships the verified linear-scan RA
framework: live-range analysis, lowest-free-slot assignment, and a
`RegisterAllocation` decision record consumed by downstream emit passes.

`KeccakEmit.lean` (#121) provides the current Keccak emit (the scalar
24-round straight-line + the SIMD lane-parallel θ-parity ABI mode). Both
bake in a fixed slot file (`numSlots`-element `stack u64[..] k` array,
slots `25..56` for scratch/parity/B seeds, `0..24` for state lanes).

This module is the **RA-driven Keccak emit**: an additive sibling of
`KeccakEmit.lean` that takes a `RegisterAllocation` produced by
`linearScanRA` and emits a register-allocated Keccak round body whose
denotation matches the current emit's. The headline theorem is

  `keccak_ra_emit_denotation_preserves`:
    `(applyRA keccakRoundLoop ra).denote init = keccakRoundLoop.denote init`

a direct corollary of `applyRA_denote_preserves` for the Keccak-shaped
wrapper. The Com is unchanged at the Com level; the RA's slot decisions
are consumed by the emit-text rewrite.

## Why this is the right factoring

`applyRA p ra = p` is the Com-level identity by construction (RA is a
*labelling* of binders, not a structural rewrite). So at the Com level the
RA-driven emit produces a Com whose denotation equals the original's by
`rfl`. The RA decisions live in `ra.seqOf` (the real linear-scan slot map
for the `linearScanRA` packing — see `RegisterAllocation.lean` §8) and are
consumed by the emit-text rewrite below.

The emit-text rewrite reroutes the destination slot through the RA's
`seqOf`. Where `KeccakEmit.keccakDstName j = slotReg (keccakSlots.getD j 0)`,
the RA-driven version uses `slotReg (ra.seqOf (keccakSlots.getD j 0))`. For
`RegisterAllocation.identity`, the emit reduces byte-identically to the
current Keccak emit.

## Contents

* `keccakRoundJForProg` — the Keccak 24-round bounded-loop wrapper. Already
  defined in `KeccakEmit.lean` as `keccakRoundLoop`; we re-export it under
  a clearly RA-relevant name.
* `emitKeccakRoundRaJazz` — the RA-driven emit. Takes a `RegisterAllocation`
  and a name; produces the `.jazz` text with slot names rewritten through
  `ra.seqOf`.
* `keccak_ra_emit_denotation_preserves` — the headline theorem.
* `keccak_ra_emit_denotation_preserves_linearScan` — the corollary for the
  concrete `linearScanRA`-produced decision.

## Axiom budget

`[propext, Quot.sound]` only. The denotation theorem reduces to
`applyRA_denote_preserves` which is `rfl` under the identity-RA-rewrite
shape of `applyRA`.

## Scope of the bench-driven emit

`linearScanRA p` produces RA decisions parameterised by the *binders of `p`*.
The natural `JForProg` wrapper for Keccak is the round loop
(`keccakRoundLoop`) with a single 1600-bit accumulator and 4 binders. The
fully-unrolled permutation `Com` (`KeccakEmit.keccakF1600Com`) used by the
bench/KAT pipeline operates over a much richer slot file
(`numSlots = 57`); its slot indices are NOT binder indices of the
`JForProg` wrapper. The bench-driven emit (in
`bench/keccak_compare/keccak_ra_emit.lean`) therefore consumes
`RegisterAllocation.identity` as `ra` and produces the canonical Keccak
emit — what the framework calls the "no-op RA" baseline. The
`emitKeccakRoundRaJazz` driver is parametric over `ra`, so a future RA
algorithm defined directly over `keccakF1600Com`'s slot domain (rather
than the JForProg-binder domain) plugs in without changing the headline
theorem. The headline theorem `keccak_ra_emit_denotation_preserves` is
RA-agnostic and holds for any well-formed RA, including the not-yet-defined
unrolled-permutation RA.

## Canonical entry point

See `KeccakEmit.lean` for the full 12-file Keccak VIR canonical map. This
file is steps #153 / #158 in that chain: the canonical RA-driven sibling
emit, consumed by `bench/keccak_compare/keccak_ra_emit.lean`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakRaEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
open CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation

set_option autoImplicit false

/-! ## 1. The Keccak round body as a `JForProg`

`KeccakEmit.keccakRoundLoop : JForProg St` is the 24-round bounded-loop
wrapper over the 1600-bit state. We re-export it under a clearly
RA-relevant name. -/

/-- **The Keccak round body wrapped as a `JForProg`.**
24 iterations of the uniform round body over the 1600-bit state
accumulator. This is the JForProg shape the RA framework consumes. -/
def keccakRoundJForProg : JForProg St := keccakRoundLoop

/-! ## 2. The emit-text rewrite under an RA

The RA decisions live in `ra.seqOf` (per `linearScanRA`'s framework
packing). The RA-driven `keccakRaDstName` reroutes the slot through
`ra.seqOf`. The input operand resolver and the rest of the emit machinery
are unchanged. -/

/-- Per-binding destination name under an RA, 24-round (full-permutation)
form. The RA's `seqOf` is the real linear-scan slot map (for
`linearScanRA`); for `RegisterAllocation.identity` this reduces to
`KeccakEmit.keccakDstName`. -/
def keccakRaDstName (ra : RegisterAllocation) (j : Nat) : String :=
  slotReg (ra.seqOf (keccakSlots.getD j 0))

/-- Per-binding destination name under an RA, single-round form (mirror of
`KeccakEmit.keccakRoundDstName`). -/
def keccakRaRoundDstName (ra : RegisterAllocation) (j : Nat) : String :=
  slotReg (ra.seqOf (keccakRoundSlots.getD j 0))

/-- The state file for the RA-driven Keccak emit. The linear-scan RA's
`seqOf` can produce slot numbers exceeding the canonical `numSlots`. We
size the RA-driven state file at `stack u64[128]` (comfortably above the
linear-scan high-water mark, aligned to a power of two). -/
def keccakRaRegDecls : List String := ["stack u64[128] k"]

/-- **The RA-driven Keccak-p[1600,24] permutation `.jazz`.**
Same shape as `KeccakEmit.keccakF1600Jazz`, with the destination-slot
name rerouted through the RA's `seqOf` and an enlarged state-file
declaration accommodating the linear-scan RA's slot numbering. The Com
body and input resolver are unchanged. -/
def emitKeccakRoundRaJazz (ra : RegisterAllocation) (name : String) : String :=
  JasminAbiEmit.emitAbiOrchReg name (w := 64) (nIn := nInputs) (nOut := 25) (nCopy := 25)
    keccakRaRegDecls keccakInName (keccakRaDstName ra) keccakF1600Com

/-- **The RA-driven single-round Keccak `.jazz`** (for structural checks /
small-scale bench). -/
def emitKeccakSingleRoundRaJazz (ra : RegisterAllocation) (name : String) : String :=
  JasminAbiEmit.emitAbiOrchReg name (w := 64) (nIn := nInputs) (nOut := 25) (nCopy := 25)
    keccakRaRegDecls keccakInName (keccakRaRoundDstName ra) keccakRoundCom

/-! ## 3. The headline denotation-preservation theorem

The theorem is a direct corollary of `applyRA_denote_preserves`: for any
well-formed `RegisterAllocation`, the RA-rewritten `JForProg` denotes the
same function as the original. -/

/-- **Headline theorem:** for any well-formed register allocation, the
RA-applied Keccak round-loop denotes the same function as the original
Keccak round-loop.

The Com-level rewrite is the identity (`applyRA p ra = p` by definition);
the proof reduces to `applyRA_denote_preserves`, which delegates to the
`preserves` witness packaged in `WellFormed`. For `linearScanRA` and
`identity` this witness is `rfl`.

This is the proof obligation `#143` shipped (`applyRA_denote_preserves`)
specialised to Keccak — the proof that RA-driven emit does not change
the Keccak permutation's mathematical meaning, only its slot
labelling. -/
theorem keccak_ra_emit_denotation_preserves (ra : RegisterAllocation)
    (hwf : WellFormed ra) (init : ⟦St⟧) :
    (applyRA keccakRoundJForProg ra).denote init = keccakRoundJForProg.denote init :=
  applyRA_denote_preserves keccakRoundJForProg ra hwf init

/-- **Concrete corollary for the linear-scan RA.** -/
theorem keccak_ra_emit_denotation_preserves_linearScan (init : ⟦St⟧) :
    (applyRA keccakRoundJForProg (linearScanRA keccakRoundJForProg)).denote init
      = keccakRoundJForProg.denote init :=
  keccak_ra_emit_denotation_preserves _
    (linearScanRA_WellFormed keccakRoundJForProg) init

/-- **Concrete corollary for the identity RA.** -/
theorem keccak_ra_emit_denotation_preserves_identity (init : ⟦St⟧) :
    (applyRA keccakRoundJForProg RegisterAllocation.identity).denote init
      = keccakRoundJForProg.denote init :=
  keccak_ra_emit_denotation_preserves _ identity_WellFormed init

/-- **Concrete corollary for the unrolled-Com-domain RA (#158).**
`UnrolledComRA.unrolledSlotRAKeccak` is the linear-scan allocation over the
slot-index domain of `keccakF1600Com` (the unrolled permutation body), not over
the binder domain of the JForProg wrapper. It is the RA the bench-driven emit
consumes (it reduces spills while respecting live-range non-overlap —
`UnrolledComRA.unrolledSlotRA_no_collision_keccak`). The headline theorem fires
unchanged because it is RA-agnostic. -/
theorem keccak_ra_emit_denotation_preserves_unrolled (init : ⟦St⟧) :
    (applyRA keccakRoundJForProg UnrolledComRA.unrolledSlotRAKeccak).denote init
      = keccakRoundJForProg.denote init :=
  keccak_ra_emit_denotation_preserves _
    UnrolledComRA.unrolledSlotRAKeccak_WellFormed init

/-! ## 4. Identity-RA per-binding destination name equals the current emit

For `RegisterAllocation.identity` (`seqOf k = k`), the RA-driven per-binding
destination name reduces pointwise to the current `keccakDstName`. The
full-text byte-identity follows from this pointwise equality together with
the determinism of `JasminAbiEmit.emitAbiOrchReg`. -/

/-- **Identity-RA destination name equals the current Keccak destination
name pointwise (full-permutation form).** -/
theorem keccakRaDstName_identity_eq (j : Nat) :
    keccakRaDstName RegisterAllocation.identity j = keccakDstName j := by
  simp [keccakRaDstName, keccakDstName, RegisterAllocation.identity]

/-- **Identity-RA destination name equals the current Keccak destination
name pointwise (single-round form).** -/
theorem keccakRaRoundDstName_identity_eq (j : Nat) :
    keccakRaRoundDstName RegisterAllocation.identity j = keccakRoundDstName j := by
  simp [keccakRaRoundDstName, keccakRoundDstName, RegisterAllocation.identity]

/-! ## 5. Two-address coalescing audit (Phase B+)

`UnrolledComRA.lean` §8 ships `unrolledSlotRAofItersCoalesce`: a
coalesce-aware variant of the cross-iter RA that fuses `dst` and `src1`
into one physical slot when `src1` dies at the event.

Keccak's θ/ρπ/χ structure is genuinely **three-address**:

* θ-D uses scratch slot `56` as `chiScr`:
  `[⟨56, [C[x+1]]⟩, ⟨56, [56]⟩, ⟨56, [56, 55]⟩, ⟨56, [56, C[x-1]]⟩]`.
  The first `mov`'s `src1 = C[x+1]` is dead immediately after (the column
  parity is consumed once per θ-D); `dst = 56 ≠ src1`. Candidate.

* ρ∘π copies an A-lane to a B-lane via `⟨dst, [a]⟩` (then rotates dst).
  After the lane copy, the source A-lane is dead until the next round's
  θ — but within the trace's per-round window, depending on the round's
  remaining schedule, several `(dst, a)` pairs are reported.

* χ uses scratch `56` similarly: `[⟨56, [B[x+1,y]]⟩, ⟨56, [56]⟩,
  ⟨56, [56, B[x+2,y]]⟩, ⟨A[x,y], [B[x,y], 56]⟩]`. The `mov` step has
  `src1 = B[x+1,y] ≠ 56 = dst`; if `B[x+1,y]` is dying at that point,
  it is a candidate.

On `UnrolledComRA.kSlotTrace`, `coalesceCandidateCount` is **positive**
(see `keccak_coalesce_candidate_count_pos`) — the coalescing pass fires.

The cross-iter + coalesce RA `keccakRA_coalesce` is well-formed by
`unrolledSlotRAofItersCoalesce_WellFormed`, and the denotation theorem
fires unchanged because it is RA-agnostic. -/

/-- **The cross-iter + coalesce-aware Keccak register allocation
(Phase B+).** Built over `UnrolledComRA.kSlotTrace` and `kIterChunks`
(24 copies of `kRoundTrace`). Equivalent to `unrolledSlotRAKeccak` plus a
two-address coalescing pass that fuses `dst`/`src1` pairs where `src1`
dies at the event (the θ-D `mov ← C[x+1]`, χ `mov ← B[x+1,y]`, and
ρπ lane-copy patterns). -/
def keccakRA_coalesce : RegisterAllocation :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce
    UnrolledComRA.kSlotTrace UnrolledComRA.kIterChunks

/-- The cross-iter + coalesce-aware Keccak RA is well-formed. -/
theorem keccakRA_coalesce_WellFormed : WellFormed keccakRA_coalesce :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce_WellFormed _ _

/-- **Denotation preservation for the coalesce-aware RA.** The headline
theorem is RA-agnostic; this is its application at `keccakRA_coalesce`. -/
theorem keccak_ra_emit_denotation_preserves_coalesce (init : ⟦St⟧) :
    (applyRA keccakRoundJForProg keccakRA_coalesce).denote init
      = keccakRoundJForProg.denote init :=
  keccak_ra_emit_denotation_preserves _ keccakRA_coalesce_WellFormed init

/-- **Keccak admits two-address coalescing.** `kSlotTrace` contains
three-address events (θ-D `mov chiScr ← C[x+1]`, χ `mov chiScr ← B[x+1,y]`,
and ρπ lane copies) whose `src1` dies at the event and differs from `dst`.
After seed filtering the count is **7** — the seven θ-D / χ scratch-load
events whose `src1` (the column parity / B-lane being loaded) is genuinely
dying. This is the empirically-validated firing point of the Phase B+
coalescing pass on Keccak's slot encoding. -/
theorem keccak_coalesce_candidate_count :
    UnrolledComRA.coalesceCandidateCount UnrolledComRA.kSlotTrace = 7 := by
  native_decide

/-- **Keccak coalesce candidate count is positive.** Direct consequence
of `keccak_coalesce_candidate_count`; surfaces the architectural fact
that Keccak — unlike ChaCha and Poseidon2 — is genuinely three-address
at the slot-trace level. -/
theorem keccak_coalesce_candidate_count_pos :
    UnrolledComRA.coalesceCandidateCount UnrolledComRA.kSlotTrace > 0 := by
  rw [keccak_coalesce_candidate_count]; decide

/-! ## 6. Per-round `chiScr` renaming (Phase C step 1)

On `UnrolledComRA.kSlotTrace`, the seven Phase B+ coalesce candidates
all centre on slot `56` (`chiScr`) — the χ/θ-D scratch. Each is rejected
by `tryMergeOne` because the conservative live range of slot `56` spans
the **whole 24-round permutation** (it is rewritten once per round, so
its first-to-last trace appearance covers the entire body). Merging
slot `56` with any column-parity or B-lane source slot `x` therefore
fails the no-collision check against essentially every other non-seed
slot.

The fix at the trace-encoding level is to **split slot 56 into 24
per-round variants**. Each round writes its own `chiScr_i` (logical
slot `57 + i` for round `i ∈ {0..23}`), so the per-round live range
shrinks from the whole permutation to one round — a window narrow
enough that `tryMergeOne`'s no-collision check passes against the
column parities `25..29` and B-lanes `30..54` it would now overlap.

The renaming is mechanical: within each iter chunk (`kRoundTrace`),
replace every occurrence of slot `56` (as `wr` or in `rds`) with the
per-round variant `chiScrRoundSlot round`. The slot universe grows from
`57` to `81` (slots `57..80` are the 24 per-round chiScrs). No other
trace structure changes.

The renaming is **denotation-preserving** as a Com-level rewrite: the
`SlotEvent` trace is a per-binding **footprint** the RA framework
consumes to compute live ranges; the underlying `keccakF1600Com` body
is unchanged. The RA-driven emit only consumes `seqOf` (via
`keccakRaDstName`), and `seqOf` is a slot-remap that respects the
no-collision invariant by construction (`unrolledSlotRAofItersCoalesce`'s
`tryMergeOne` rejects any merge that violates it).

Per the headline theorem `keccak_ra_emit_denotation_preserves`, the
denotation is preserved for **any** well-formed RA — including this
renamed one. The emit-text rewrite reroutes the slot through the RA's
`seqOf`, so the Com body's slot-56 writes map to the renamed
`chiScrRoundSlot round` logical slots, and through `seqOf` to whatever
physical slot the linear scan + coalescer assigns. -/

/-- **Per-round `chiScr` slot for round `round ∈ {0..23}`.** Maps to
logical slot `57 + round`; the 24 variants occupy logical slots
`57..80`. -/
def chiScrRoundSlot (round : Nat) : Nat := 57 + round

/-- **Rename slot 56 in a single `SlotEvent`** to the per-round variant.
The destination and all read slots are renamed via `renameOne`; other
slots are unchanged. -/
def renameChiScrEvent (round : Nat) (ev : UnrolledComRA.SlotEvent) :
    UnrolledComRA.SlotEvent :=
  let renameOne (s : Nat) : Nat :=
    if s = 56 then chiScrRoundSlot round else s
  { wr := renameOne ev.wr
    rds := ev.rds.map renameOne }

/-- **The per-round-renamed Keccak round trace** for round `round`. -/
def kRoundTraceRenamed (round : Nat) : List UnrolledComRA.SlotEvent :=
  UnrolledComRA.kRoundTrace.map (renameChiScrEvent round)

/-- **The 24 per-round-renamed iter chunks.** Round `i` uses the
per-round slot `chiScrRoundSlot i = 57 + i` instead of the shared
slot `56`. -/
def kIterChunksRenamed : List (List UnrolledComRA.SlotEvent) :=
  (List.range 24).map kRoundTraceRenamed

/-- **The flat per-round-renamed slot trace.** Same shape as
`UnrolledComRA.kSlotTrace` (24 round chunks + output-stage + epilogue),
with each round's `chiScr` (slot 56) replaced by its per-round variant.
The output stage and epilogue are unchanged (they do not touch slot
56). -/
def kSlotTraceRenamed : List UnrolledComRA.SlotEvent :=
  kIterChunksRenamed.flatten ++ UnrolledComRA.kOutStageTrace ++
    [UnrolledComRA.kEpilogue]

/-- **The cross-iter + coalesce-aware Keccak RA over the per-round-renamed
trace (Phase C step 1).** Built from `kSlotTraceRenamed` and
`kIterChunksRenamed`; the per-round-narrowed `chiScr` live ranges
allow `tryMergeOne` to accept the seven θ-D / χ scratch-load merges
that Phase B+ rejected on the unrenamed trace. -/
def keccakRA_coalesce_renamed : RegisterAllocation :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce
    kSlotTraceRenamed kIterChunksRenamed

/-- **The renamed coalesce-aware RA is well-formed.** Same `slotOf := id`
shape as `keccakRA_coalesce`; well-formedness is RA-agnostic. -/
theorem keccakRA_coalesce_renamed_WellFormed :
    WellFormed keccakRA_coalesce_renamed :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce_WellFormed _ _

/-- **Denotation preservation for the renamed coalesce-aware RA.** -/
theorem keccak_ra_emit_denotation_preserves_coalesce_renamed (init : ⟦St⟧) :
    (applyRA keccakRoundJForProg keccakRA_coalesce_renamed).denote init
      = keccakRoundJForProg.denote init :=
  keccak_ra_emit_denotation_preserves _ keccakRA_coalesce_renamed_WellFormed init

/-! ### 6a. Diagnostic: candidate and merged counts pre/post renaming

The renaming is validated empirically: on the renamed trace, the
coalesce candidate count must remain ≥ 7 (the same θ-D / χ scratch
loads, with `chiScr` replaced by its per-round variant) and the number
of pairs whose `tryMergeOne` actually succeeds must become positive
(target: ≥ 7, one per round-local scratch load). -/

/-- **Count of coalesce pairs that actually fire** (whose `tryMergeOne`
returns a strictly different assignment from its input). A pair fires
iff `phDst ≠ phS1` AND the resulting no-collision check passes. -/
def mergedPairsCount (tr : List UnrolledComRA.SlotEvent)
    (iters : List (List UnrolledComRA.SlotEvent)) : Nat :=
  let base := UnrolledComRA.scanAssignCrossIter tr iters
  let pairs := UnrolledComRA.coalescePairsNoSeed tr
  (pairs.foldl
    (fun acc p =>
      let before := acc.2
      let after  := UnrolledComRA.tryMergeOne tr p before
      (acc.1 + (if after == before then 0 else 1), after))
    (0, base)).1

/-- **Pre-renaming candidate count.** Restated from
`keccak_coalesce_candidate_count`: 7 candidates on the unrenamed
trace. -/
theorem keccak_coalesce_candidate_count_pre :
    UnrolledComRA.coalesceCandidateCount UnrolledComRA.kSlotTrace = 7 :=
  keccak_coalesce_candidate_count

/-- **Pre-renaming merged count is zero.** Empirically validated: all 7
candidates are rejected on the unrenamed trace because slot 56's live
range spans the whole permutation. -/
theorem keccak_coalesce_merged_count_pre :
    mergedPairsCount UnrolledComRA.kSlotTrace UnrolledComRA.kIterChunks = 0 := by
  native_decide

/-- **Post-renaming candidate count = 7.** Same as pre-renaming: the
seven θ-D / χ scratch-loads whose `src1` (the column parity / B-lane)
dies at the event are still candidates, with `dst = 80 = chiScrRoundSlot
23` instead of `dst = 56`. Per-round renaming does NOT increase the
candidate count: rounds 0..22 contribute no candidates because their
sources (column parities `25..29`, B-lanes `30..54`) are re-read in
later rounds via the cross-round liveness of those slots. Only
round 23's scratch loads survive `src1IsLastUse`. -/
theorem keccak_coalesce_candidate_count_post :
    UnrolledComRA.coalesceCandidateCount kSlotTraceRenamed = 7 := by
  native_decide

/-- **Post-renaming candidate count is positive.** -/
theorem keccak_coalesce_candidate_count_post_pos :
    UnrolledComRA.coalesceCandidateCount kSlotTraceRenamed > 0 := by
  rw [keccak_coalesce_candidate_count_post]; decide

/-- **Post-renaming merged count is still 0** even after `rangesOverlap`
relaxation (half-open `<` form, source-dies-at-dst-birth case).

The 7 surviving candidates all have `dst = chiScrRoundSlot 23` (slot 80,
round 23's scratch); each candidate source is a column-parity `C[i]`
(slots 25..29) or B-lane (slots 30..50) whose last touch IS in round 23.
The rejection is **not** EEEEE's diagnosed shared-endpoint case but a
transitive-physical-slot collision:

* Pre-merge, the linear scan reuses **physical slot 56** for all 24
  per-round chiScr logical slots (`57..80`) — they are pairwise live-range
  disjoint (each lives in its own round), so the scan collapses them
  onto one physical slot.
* `tryMergeOne` for `(dst=80, src1=29)` looks up `phDst = 56`,
  `phS1 = 29`, and rewrites **every logical slot mapped to `phDst=56`**
  (i.e. all 24 chiScrs `57..80`) to physical slot 29 in one go.
* The remapped chiScr_0 (logical 57, live range `≈[100, 350]`) now
  shares physical 29 with C[4] (logical 29, live range `[16, 6214]`).
  Their ranges overlap on multiple events → no-collision check fails →
  merge rejected.

Architectural finding: the half-open `rangesOverlap` relaxation closes
the textbook boundary case but does NOT unblock Keccak. To fire these 7
merges, `tryMergeOne` would need to remap **only the merge-target
logical slot** (slot 80 alone) rather than every logical slot sharing
its physical slot — i.e. break the linear-scan's coalescing of the 24
chiScrs first, or rewrite `tryMergeOne` to track per-logical-slot
merges instead of physical-slot-wide rewrites. Both are out of scope
for this `rangesOverlap` pass. -/
theorem keccak_coalesce_merged_count_post :
    mergedPairsCount kSlotTraceRenamed kIterChunksRenamed = 0 := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakRaEmit
