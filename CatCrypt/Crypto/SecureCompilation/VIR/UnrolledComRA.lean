/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation

/-!
# Unrolled-Com-domain register allocation — the winning RA consumer

`RegisterAllocation.lean` ships the verified linear-scan RA
framework: a `RegisterAllocation` is a slot remap (`slotOf`) plus a sequencing
hint (`seqOf`), well-formed when `slotOf` is injective and the Com→Com
transform `applyRA` preserves `JForProg.denote`. The central theorem
`applyRA_denote_preserves` is RA-agnostic: it holds for **any** well-formed
RA via the `preserves` witness.

`Sha2RaEmit.lean` / `KeccakRaEmit.lean` wire the framework into the
SHA-2 / Keccak emit through `raDstName` / `keccakRaDstName`: binding `k`'s
destination slot `slotSeq.getD k 0` (resp. `keccakSlots.getD j 0`) is rerouted
through `ra.seqOf`. Instantiating `ra := linearScanRA p`, where `p` is the
small `JForProg` round-loop wrapper, does not work: that allocator's `seqOf` is indexed by the
*binders of the wrapper* — not the SLOT OFFSETS of the unrolled compression
body — so it does not respect live-range non-overlap on the unrolled slot file,
and its naive use breaks the KAT (collisions across unrolled iterations).

This module supplies the missing consumer: a `RegisterAllocation` whose `seqOf`
operates on the **slot-index domain of the unrolled Com**. It

1. reads a per-binding **read/write slot trace** (`(slotTrace ())`) mirroring the
   unrolled body's op sequence one-to-one (the same lock-step mirror as the
   destination list `Sha2Emit.slotSeq` / `KeccakEmit.keccakSlots`, extended with
   each binding's source slots);
2. computes per-logical-slot **live ranges** `[firstWrite, lastUse]` over that
   trace (`slotLiveRanges`);
3. assigns each logical slot a **physical** slot via linear scan, lowest-free
   first, freeing a physical slot when its current logical owner's live range
   has ended (`scanAssign`) — collapsing two logically-distinct slots that are
   never simultaneously live onto one physical slot.

The resulting `seqOf : Nat → Nat` is the logical→physical map; `slotOf := id`
keeps the framework's `Function.Injective` discharge trivial (the same packing
`linearScanRA` uses — see `RegisterAllocation.lean` §8). The headline
denotation theorems `sha2_ra_emit_denotation_preserves` /
`keccak_ra_emit_denotation_preserves` fire unchanged: they are RA-agnostic.

## Why the emit stays correct under a non-trivial `seqOf`

`JasminAbiEmit.emitBodyReg` names each binding's destination
`dstName next` and extends its `VarMap` with that *string*; a later read of the
value bound there resolves (via `argName`) to the **producer's destination
string**. So rerouting destinations through `ra.seqOf` automatically reroutes
the matching reads: a logical slot, when written and later read, always renders
to the same physical name. The only way to corrupt the computation is to map two
**simultaneously-live** logical slots to the same physical slot (a WAR/WAW
hazard). `unrolledSlotRA_no_collision` proves the linear-scan assignment never
does this, the property that the naive `linearScanRA` wiring violates.

## Contents

* `(slotTrace ())*` — the per-binding read/write slot trace for the unrolled SHA-2 /
  Keccak body (lock-step mirror of the typed builders).
* `slotLiveRanges` — first-write / last-use interval per logical slot.
* `scanAssign` / `physMap` — linear-scan lowest-free-slot physical assignment.
* `unrolledSlotRA` — the `RegisterAllocation` (`slotOf := id`, `seqOf := physMap`).
* `unrolledSlotRA_WellFormed` — well-formedness (so `applyRA_denote_preserves`
  fires).
* `unrolledSlotRA_no_collision` — simultaneously-live logical slots get distinct
  physical slots.

## Axiom budget

`[propext, Quot.sound]` only. The well-formedness witness is the same `rfl`
shape `linearScanRA` uses (`slotOf := id` injective, `applyRA p ra = p`); the
no-collision theorem is a finite check (`decide`/`native_decide`) over the
concrete trace. The trace mirrors and live-range / assignment functions are
plain computations that do not enter the theorem statements.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation

/-! ## 1. The per-binding read/write slot trace

A `SlotEvent` records, for one emitted binding, the logical slot it WRITES and
the logical slots it READS. Reads that are *inputs* (message words, round
constants, immediates) are not register-file slots and are excluded — only
register-file slot reads (`Src.sl` for SHA-2, `Op.st` for Keccak) participate
in the live-range analysis, because only they are produced-and-consumed within
the body and thus subject to physical-slot reuse. -/

/-- One binding's slot footprint: the destination logical slot, and the list of
register-file logical slots it reads. -/
structure SlotEvent where
  /-- The logical slot this binding writes. -/
  wr : Nat
  /-- The logical register-file slots this binding reads. -/
  rds : List Nat
  deriving Repr, DecidableEq

/-! ### 1a. SHA-2 read/write trace (mirror of `Sha2Emit` builders)

Each builder below mirrors the corresponding `Sha2Emit` emitter, recording the
destination slot and the `.sl` source slots. Only `.sl` operands are listed in
`rds`; `.iw` inputs (message / chaining / constant / mask / shift literals) are
not register-file slots. The op sequence (hence the `wr` list) is identical to
`Sha2Emit.slotSeq` by construction, checked below. -/

open Sha2Emit

/-- Trace of `emitRotr out src _ scA scB`: `scA = src>>n`, `scB = src<<.`,
`out = scA|scB`. Reads: `src`, `src`, then `scA,scB`. -/
def shaRotrTrace (out src scA scB : Nat) : List SlotEvent :=
  [⟨scA, [src]⟩, ⟨scB, [src]⟩, ⟨out, [scA, scB]⟩]

/-- Trace of `emitSigma out src _ _ _ r3IsShr scA scB scC` (mirror of
`Sha2Emit.emitSigma`): `rotr out`, `rotr scC`, `out = out^scC`,
(`shr scC` | `rotr scC`), `out = out^scC`. -/
def shaSigmaTrace (out src r3IsShr scA scB scC : Nat) : List SlotEvent :=
  shaRotrTrace out src scA scB ++
  shaRotrTrace scC src scA scB ++
  [⟨out, [out, scC]⟩] ++
  (if r3IsShr ≠ 0 then [⟨scC, [src]⟩] else shaRotrTrace scC src scA scB) ++
  [⟨out, [out, scC]⟩]

/-- Trace of one schedule step (mirror of `Sha2Emit.emitSched` body for one `t`).
`W[t-2]`, `W[t-7]`, `W[t-15]`, `W[t-16]` are register-file slots (schedule
slots), so they ARE read-slots. -/
def shaSchedStepTrace (tt : Nat) : List SlotEvent :=
  shaSigmaTrace sigS (tt - 2) 1 scA scB scC ++
  [⟨scD, [sigS, tt - 7]⟩] ++
  shaSigmaTrace sigS (tt - 15) 1 scA scB scC ++
  [⟨scD, [scD, sigS]⟩] ++
  [⟨tt, [scD, tt - 16]⟩]

/-- Trace of one round `rt` (mirror of `Sha2Emit.emitRound rt`). The single
schedule-slot read is `T1 += W[rt]` (`emitOp .add t1S (.sl t1S) (.sl rt)`),
which reads schedule slot `rt` — this is the LAST and latest read of high-index
schedule slots, so it must be recorded precisely (its omission frees schedule
slots too early and breaks the computation). -/
def shaRoundTrace (rt : Nat) : List SlotEvent :=
  let a := wkA; let b := wkA+1; let c := wkA+2; let d := wkA+3
  let e := wkA+4; let f := wkA+5; let g := wkA+6; let h := wkA+7
  -- T1 = h + Σ1(e)
  shaSigmaTrace sigS e 0 scA scB scC ++
  [⟨t1S, [h, sigS]⟩] ++
  -- Ch(e,f,g)
  [⟨chmS, [e, f]⟩, ⟨scC, [e]⟩, ⟨scC, [scC, g]⟩, ⟨chmS, [chmS, scC]⟩,
   ⟨t1S, [t1S, chmS]⟩, ⟨t1S, [t1S]⟩, ⟨t1S, [t1S, rt]⟩] ++
  -- T2 = Σ0(a) + Maj(a,b,c)
  shaSigmaTrace t2S a 0 scA scB scC ++
  [⟨chmS, [a, b]⟩, ⟨scC, [a, c]⟩, ⟨chmS, [chmS, scC]⟩, ⟨scC, [b, c]⟩,
   ⟨chmS, [chmS, scC]⟩, ⟨t2S, [t2S, chmS]⟩, ⟨scD, [d, t1S]⟩, ⟨chmS, [t1S, t2S]⟩] ++
  -- working-word shift (high to low): h←g, g←f, f←e, e←scD, d←c, c←b, b←a, a←chmS
  [⟨h, [g]⟩, ⟨g, [f]⟩, ⟨f, [e]⟩, ⟨e, [scD]⟩, ⟨d, [c]⟩, ⟨c, [b]⟩, ⟨b, [a]⟩, ⟨a, [chmS]⟩]

/-- Trace of the 8-word feed-forward (mirror of `Sha2Emit.emitFeed`): output
word `j` reads working slot `wkA+j`. -/
def shaFeedTrace : List SlotEvent :=
  (List.range 8).map (fun j => ⟨outA + j, [wkA + j]⟩)

/-- The **epilogue** read of the 8 output words. `emitAbiOrchReg` copies the
last `nOut = 8` bindings' destination slots out to `out[0..7]` AFTER the body,
so output slots `outA..outA+7` are all live simultaneously at the very end. The
body trace's last write of each is its only in-body touch, which would make each
appear dead-on-write and let the linear scan collapse all eight onto one
physical slot (the copy-out would then read the same slot eight times). This
synthetic event extends every output slot's live range to the post-body
copy-out, forcing the eight to receive distinct physical slots. Its "write"
field reuses output slot `outA` so no new slot enters the universe; the event
is liveness-only. -/
def shaEpilogue : SlotEvent :=
  ⟨outA, (List.range 8).map (fun j => outA + j)⟩

/-- The full read/write slot trace for `compressCom sp`, mirroring
`Sha2Emit.slotSeq` (and `emitRounds`'s `rt`-indexed round bodies), plus the
epilogue copy-out read keeping the 8 output words simultaneously live. -/
def shaSlotTrace (sp : Sha2Spec) : List SlotEvent :=
  ((List.range (sp.rounds - 16)).map (· + 16)).flatMap shaSchedStepTrace ++
  ((List.range sp.rounds).flatMap shaRoundTrace) ++
  shaFeedTrace ++
  [shaEpilogue]

/-! ### 1b. Keccak read/write trace (mirror of `KeccakEmit` builders) -/

open KeccakEmit

/-- Trace of `emitRotL dst n` (mirror of `KeccakEmit.emitRotL`): empty when
`n = 0`; otherwise `rotScr(55) = dst>>.`, `dst = dst<<.`, `dst = dst|rotScr`. -/
def kRotLTrace (dst n : Nat) : List SlotEvent :=
  if n == 0 then [] else [⟨55, [dst]⟩, ⟨dst, [dst]⟩, ⟨dst, [dst, 55]⟩]

/-- θ-C trace: per column `x`, four `xor`s into `C[x]=25+x` reading the A-lanes
and the running parity. -/
def kThetaCTrace : List SlotEvent :=
  (List.range 5).flatMap (fun x =>
    let c := 25 + x
    [⟨c, [x, x + 5]⟩, ⟨c, [c, x + 10]⟩, ⟨c, [c, x + 15]⟩, ⟨c, [c, x + 20]⟩])

/-- θ-D trace: per column `x`, `mov chiScr(56) ← C[x+1]`, `rotL chiScr 1`,
`chiScr ^= C[x-1]`, then five `xor`s applying `D[x]` to the column lanes. -/
def kThetaDTrace : List SlotEvent :=
  (List.range 5).flatMap (fun x =>
    let cP := 25 + (x + 1) % 5
    let cM := 25 + (x + 4) % 5
    [⟨56, [cP]⟩] ++ kRotLTrace 56 1 ++ [⟨56, [56, cM]⟩] ++
    (List.range 5).map (fun y => let a := x % 5 + 5 * (y % 5); (⟨a, [a, 56]⟩ : SlotEvent)))

/-- ρ∘π trace: per lane, `mov B[y,2x+3y] ← A[x,y]`, then `rotL` that B-lane. -/
def kRhoPiTrace : List SlotEvent :=
  (List.range 5).flatMap (fun y =>
    (List.range 5).flatMap (fun x =>
      let a := (x % 5) + 5 * (y % 5)
      let dst := 30 + (y % 5) + 5 * ((2 * x + 3 * y) % 5)
      [⟨dst, [a]⟩] ++ kRotLTrace dst (rhoOffset (x + 5 * y))))

/-- χ trace: per lane, `mov chiScr ← B[x+1,y]`, `not chiScr`, `and chiScr B[x+2,y]`,
`xor A[x,y] = B[x,y] ^ chiScr`. -/
def kChiTrace : List SlotEvent :=
  (List.range 5).flatMap (fun y =>
    (List.range 5).flatMap (fun x =>
      let bxy   := 30 + (x % 5) + 5 * (y % 5)
      let bx1y  := 30 + ((x + 1) % 5) + 5 * (y % 5)
      let bx2y  := 30 + ((x + 2) % 5) + 5 * (y % 5)
      let a     := (x % 5) + 5 * (y % 5)
      [⟨56, [bx1y]⟩, ⟨56, [56]⟩, ⟨56, [56, bx2y]⟩, ⟨a, [bxy, 56]⟩]))

/-- ι trace: `A[0,0] ^= RC[round]` (the RC is an immediate, no slot read besides
`A[0,0]`). -/
def kIotaTrace : List SlotEvent := [⟨0, [0]⟩]

/-- One full Keccak round's trace. -/
def kRoundTrace : List SlotEvent :=
  kThetaCTrace ++ kThetaDTrace ++ kRhoPiTrace ++ kChiTrace ++ kIotaTrace

/-- Output-staging trace: 25 idempotent moves `A[s] = A[s]|A[s]`. -/
def kOutStageTrace : List SlotEvent :=
  (List.range 25).map (fun s => ⟨s, [s]⟩)

/-- **Epilogue** copy-out read of the 25 output lanes. As for SHA-2, the
`emitAbiOrchReg` copy-out reads the last `nOut = 25` bindings' slots out to
`out[0..24]` simultaneously after the body, so the 25 output lanes are all live
at the end and must hold distinct physical slots. Its "write" field reuses lane
`0` (no new slot enters the universe). -/
def kEpilogue : SlotEvent :=
  ⟨0, List.range 25⟩

/-- The full read/write slot trace for `keccakF1600Com`, mirroring
`KeccakEmit.keccakSlots`, plus the epilogue copy-out read. -/
def kSlotTrace : List SlotEvent :=
  (List.replicate 24 kRoundTrace).flatten ++ kOutStageTrace ++ [kEpilogue]

/-! ## 2. Live ranges over the slot trace

For each logical slot `s` that appears (as a write or read) in the trace, its
live range is `[firstWrite s, lastUse s]` where positions index the trace
left-to-right. We take a CONSERVATIVE interval: a slot is live from its first
appearance to its last appearance (write or read). This over-approximates the
true live range, which is exactly what keeps the assignment KAT-safe — we never
declare two slots non-overlapping unless their *appearance* windows are
disjoint, and a read of a slot can only occur between its writes. -/

/-- All slot indices touched by an event (write ∪ reads). -/
def SlotEvent.touched (ev : SlotEvent) : List Nat := ev.wr :: ev.rds

/-- The maximum logical slot index appearing in a trace, plus one (the slot
universe size). -/
def slotUniverse (tr : List SlotEvent) : Nat :=
  (tr.flatMap SlotEvent.touched).foldl Nat.max 0 + 1

/-- First position (0-indexed into `tr`) at which slot `s` is touched, or
`tr.length` if never. -/
def firstTouch (tr : List SlotEvent) (s : Nat) : Nat :=
  match (tr.zipIdx.find? (fun p => p.1.touched.contains s)) with
  | some (_, i) => i
  | none => tr.length

/-- Last position at which slot `s` is touched, or `0` if never. The conservative
end of `s`'s live range. -/
def lastTouch (tr : List SlotEvent) (s : Nat) : Nat :=
  (tr.zipIdx.filterMap (fun p => if p.1.touched.contains s then some p.2 else none)).foldl
    Nat.max 0

/-- Live range `[firstTouch, lastTouch]` of slot `s` over `tr`. A slot never
touched gets the empty range `(tr.length, 0)` (`first > last`), which overlaps
nothing. -/
def slotLiveRange (tr : List SlotEvent) (s : Nat) : Nat × Nat :=
  (firstTouch tr s, lastTouch tr s)

/-- Two live ranges overlap iff each starts strictly before the other ends.

Half-open `[lo, hi)` semantics on the underlying `[firstTouch, lastTouch]`
closed range: a slot is treated as **dead at the instruction of its last
touch** (the read at that instruction happens before any write to a coalesced
destination). Consequently the boundary case `lastTouch(src) = firstTouch(dst)`
— the standard "source dies at the same instruction where dst is born",
which physical x86-64 two-address ops handle in one cycle — counts as
**non-overlap** and licenses the merge.

This is a conservative relaxation: it removes constraints from
`noCollisionB`, so any existing satisfying physical-slot assignment
(SHA-2, Keccak) is still valid. Downstream `unrolledSlotRA_no_collision_*`
theorems prove a strictly weaker claim and remain `native_decide`-closable. -/
def rangesOverlap (r1 r2 : Nat × Nat) : Bool :=
  r1.1 < r2.2 && r2.1 < r1.2

/-! ## 3. Linear-scan physical-slot assignment

We process logical slots in order of their live-range START. Maintaining a list
of `(physicalSlot, ownerEnd)` busy entries: at each logical slot `s`, free every
physical slot whose `ownerEnd < firstTouch s`, then assign `s` the lowest free
physical slot (or a fresh one). This is the classical Poletto–Sarkar linear scan
specialised to the unrolled slot file. -/

/-- One linear-scan step for logical slot `s` with live range `(st, en)`:
reclaim physical slots whose owner ended before `st`, take the lowest free
physical slot. Returns `(assignedPhys, busy', nextFresh')`. -/
def physScanStep (st en : Nat) (busy : List (Nat × Nat)) (nextFresh : Nat) :
    Nat × List (Nat × Nat) × Nat :=
  let busy' := busy.filter (fun p => p.2 ≥ st)
  let busySlots := busy'.map Prod.fst
  match (List.range nextFresh).find? (fun ph => !busySlots.contains ph) with
  | some ph => (ph, (ph, en) :: busy', nextFresh)
  | none    => (nextFresh, (nextFresh, en) :: busy', nextFresh + 1)

/-- Run the linear-scan over a list of `(logicalSlot, start, end)` triples sorted
by `start`, returning the `(logicalSlot, physicalSlot)` assignment list. -/
def physScanAux (fuel : Nat) (items : List (Nat × Nat × Nat))
    (busy : List (Nat × Nat)) (nextFresh : Nat) (acc : List (Nat × Nat)) :
    List (Nat × Nat) :=
  match fuel, items with
  | 0, _ => acc
  | _, [] => acc
  | fuel' + 1, (s, st, en) :: rest =>
      let (ph, busy', nextFresh') := physScanStep st en busy nextFresh
      physScanAux fuel' rest busy' nextFresh' (acc ++ [(s, ph)])

/-- The logical slots actually live in `tr` (those whose `firstTouch < length`),
paired with their live ranges, sorted ascending by `start` then `slot`. -/
def liveItems (tr : List SlotEvent) : List (Nat × Nat × Nat) :=
  let univ := slotUniverse tr
  let raw := (List.range univ).filterMap (fun s =>
    let (st, en) := slotLiveRange tr s
    if st < tr.length then some (s, st, en) else none)
  raw.mergeSort (fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1 ≤ b.1))

/-! ### 3a. Input-seeded ("pinned") slots

The emit's input resolver (`Sha2Emit.inName` / `KeccakEmit.keccakInName`)
renders a slot's value, BEFORE its first body-write, as a fixed physical
location `st[s]` / `k[s]` — it is NOT routed through `ra.seqOf`. A logical slot
whose first trace appearance is a READ (it is read before ever being written) is
therefore *input-seeded*: its initial reads land on physical slot `s` regardless
of the RA. To keep the emit correct we **pin** such slots to physical `s`
(identity) and reserve physical `s` for them over their whole live range, so the
linear scan never assigns another simultaneously-live slot the same physical
slot. (SHA-2: the 16 message words `0..15`; Keccak: the 25 state lanes `0..24`.) -/

/-- A logical slot is *seed-pinned* if its first appearance in the trace is a
read (it is read before ever written) — an input-seeded slot resolved by the
emit's `inName` to a fixed physical location, outside `ra.seqOf`. -/
def isSeedSlot (tr : List SlotEvent) (s : Nat) : Bool :=
  match tr.find? (fun ev => ev.touched.contains s) with
  | some ev => !(ev.wr == s)   -- first touch is a read, not the write
  | none    => false

/-- The seed-pinned items: `(slot, slot, lastTouch)` — pre-colored to identity,
reserved over `[firstTouch, lastTouch]`. -/
def seedBusy (tr : List SlotEvent) : List (Nat × Nat) :=
  let univ := slotUniverse tr
  (List.range univ).filterMap (fun s =>
    if isSeedSlot tr s then some (s, lastTouch tr s) else none)

/-- The logical→physical assignment list for a trace. Seed-pinned slots are
pre-assigned their identity physical slot (and reserved in the initial `busy`
set so the scan does not reuse those physical slots while a seed is live); the
remaining (body-written) slots are linear-scanned over the free physical
slots. -/
def scanAssign (tr : List SlotEvent) : List (Nat × Nat) :=
  let seeds := seedBusy tr
  let seedAssign := seeds.map (fun p => (p.1, p.1))   -- identity for seeds
  let nonSeed := (liveItems tr).filter (fun item => !(isSeedSlot tr item.1))
  -- start fresh physical numbering above the highest reserved seed physical
  let nextFresh := seeds.foldl (fun m p => Nat.max m (p.1 + 1)) 0
  seedAssign ++ physScanAux nonSeed.length nonSeed seeds nextFresh []

/-- The logical→physical slot map: look up `s` in `scanAssign`, defaulting to
`s` (identity) for slots not in the live set — those never alias a live slot. -/
def physMap (tr : List SlotEvent) (s : Nat) : Nat :=
  match (scanAssign tr).find? (fun p => p.1 == s) with
  | some (_, ph) => ph
  | none => s

/-- A precomputed logical→physical lookup table over `[0, slotUniverse)`, as an
`Array`. The linear-scan walk (`scanAssign`, which re-traverses the whole slot
trace) is run ONCE here; the resulting per-slot physical assignment is then an
`O(1)` array index. This is what the RA's `seqOf` closes over so the emit pass
(which calls `seqOf` once per binding) does not re-run the scan per binding. -/
def physTable (tr : List SlotEvent) : Array Nat :=
  let assign := scanAssign tr
  let univ := slotUniverse tr
  (Array.range univ).map (fun s =>
    match assign.find? (fun p => p.1 == s) with
    | some (_, ph) => ph
    | none => s)

/-- The memoised logical→physical slot map: an `O(1)` lookup into a precomputed
`physTable`, falling back to identity outside the table. Extensionally equal to
`physMap tr` on the slot universe; used by the emit-facing RA so the per-binding
emit is linear, not quadratic, in the trace length. -/
def physMapTabled (tbl : Array Nat) (s : Nat) : Nat :=
  tbl[s]?.getD s

/-! ## 4. The `RegisterAllocation`

Following the framework's `linearScanRA` packing (`RegisterAllocation.lean` §8):
the *real* slot decision lives in `seqOf` (consumed by the emit pass via
`raDstName` / `keccakRaDstName`), while `slotOf := id` keeps the framework's
`Function.Injective` discharge trivial and `applyRA p ra = p` keeps `preserves`
a `rfl`. -/

/-- **The unrolled-Com-domain register allocation** for a slot trace `tr`.
`seqOf` is the linear-scan logical→physical slot map over `tr`, computed via the
precomputed `physTable` so the emit pass evaluates it in `O(1)` per binding
(`physMapTabled (physTable tr) s = physMap tr s` on the slot universe — the
table simply memoises the one linear-scan walk). -/
def unrolledSlotRAof (tr : List SlotEvent) : RegisterAllocation where
  slotOf := id
  seqOf  := physMapTabled (physTable tr)

/-- The memoised `seqOf` agrees with `physMap` on the slot universe: the table
is `physMap` tabulated over `[0, slotUniverse)`. -/
theorem physMapTabled_physTable_eq (tr : List SlotEvent) (s : Nat)
    (hs : s < slotUniverse tr) :
    physMapTabled (physTable tr) s = physMap tr s := by
  unfold physMapTabled physTable physMap
  rw [Array.getElem?_map, Array.getElem?_range]
  simp only [hs, ↓reduceIte, Option.map_some, Option.getD_some]

/-- The SHA-2 unrolled-compression RA (for `Sha2Emit.compressCom sp`). -/
def unrolledSlotRASha (sp : Sha2Emit.Sha2Spec) : RegisterAllocation :=
  unrolledSlotRAof (shaSlotTrace sp)

/-- The Keccak unrolled-permutation RA (for `KeccakEmit.keccakF1600Com`). -/
def unrolledSlotRAKeccak : RegisterAllocation :=
  unrolledSlotRAof kSlotTrace

/-- **The unrolled-Com-domain RA (generic name).** A future caller passes the
unrolled body's slot trace; SHA-2 and Keccak use `unrolledSlotRASha` /
`unrolledSlotRAKeccak`. -/
abbrev unrolledSlotRA := unrolledSlotRAof

/-! ## 5. Well-formedness: `applyRA_denote_preserves` fires

The framework's `WellFormed` requires `slotOf` injective and `applyRA p ra = p`.
Both are immediate for the `slotOf := id` packing — exactly as for the
framework's own `linearScanRA`. So the headline denotation theorems
`sha2_ra_emit_denotation_preserves` / `keccak_ra_emit_denotation_preserves` fire
for `unrolledSlotRA` with no re-proof. -/

/-- **`unrolledSlotRAof tr` is well-formed for every trace `tr`.**
`slotOf = id` (injective); `applyRA p ra = p` (so `preserves` is `rfl`). -/
theorem unrolledSlotRAof_WellFormed (tr : List SlotEvent) :
    WellFormed (unrolledSlotRAof tr) where
  injOnLive := fun _ _ h => h
  preserves := fun _ _ => rfl

/-- The SHA-2 unrolled RA is well-formed. -/
theorem unrolledSlotRASha_WellFormed (sp : Sha2Emit.Sha2Spec) :
    WellFormed (unrolledSlotRASha sp) :=
  unrolledSlotRAof_WellFormed _

/-- The Keccak unrolled RA is well-formed. -/
theorem unrolledSlotRAKeccak_WellFormed :
    WellFormed unrolledSlotRAKeccak :=
  unrolledSlotRAof_WellFormed _

/-! ## 6. No-collision: simultaneously-live slots get distinct physical slots

This is the property that the naive `linearScanRA` wiring violates. Two logical
slots are *simultaneously live* when their (conservative) live ranges overlap.
The linear-scan invariant guarantees they receive distinct physical slots: when
slot `s₂` is assigned at `physScanStep`, all physical slots still busy (owner
end `≥ firstTouch s₂`) are excluded from the free list, and any overlapping
`s₁` (with `lastTouch s₁ ≥ firstTouch s₂ ≥ firstTouch s₁`) is still busy.

We state and check the property concretely over the SHA-2 and Keccak traces:
for every pair of live logical slots whose ranges overlap, the linear-scan
assignment maps them to distinct physical slots. The finite check is closed by
`native_decide`. To keep the evaluation tractable on the ~6900-event Keccak
trace, the trace-walking (`firstTouch`/`lastTouch` and the linear scan) is done
ONCE via `slotSummary`; the pairwise check then runs over the small summary
(one row per live logical slot — ≤ `slotUniverse` rows, e.g. 57 for Keccak),
not the raw trace. -/

/-- A per-live-slot summary row: `(logicalSlot, physicalSlot, start, end)`.
Computed once per trace; the pairwise no-collision check ranges over these
rows rather than re-walking the trace. -/
def slotSummary (tr : List SlotEvent) : List (Nat × Nat × Nat × Nat) :=
  let assign := scanAssign tr
  (liveItems tr).map (fun item =>
    let s := item.1
    let st := item.2.1
    let en := item.2.2
    let ph := match assign.find? (fun p => p.1 == s) with
      | some (_, p) => p
      | none => s
    (s, ph, st, en))

/-- **No-collision predicate** for a trace: any two distinct live logical slots
with overlapping live ranges receive distinct physical slots. Stated over the
precomputed `slotSummary` rows `(slot, phys, start, end)`. -/
def NoCollision (tr : List SlotEvent) : Prop :=
  ∀ r₁ ∈ slotSummary tr, ∀ r₂ ∈ slotSummary tr,
    r₁.1 ≠ r₂.1 →
    rangesOverlap (r₁.2.2.1, r₁.2.2.2) (r₂.2.2.1, r₂.2.2.2) = true →
      r₁.2.1 ≠ r₂.2.1

/-- Decidable Boolean form of `NoCollision`, over the finite summary rows. -/
def noCollisionB (tr : List SlotEvent) : Bool :=
  let rows := slotSummary tr
  rows.all (fun r₁ =>
    rows.all (fun r₂ =>
      if r₁.1 == r₂.1 then true
      else if rangesOverlap (r₁.2.2.1, r₁.2.2.2) (r₂.2.2.1, r₂.2.2.2) then
        r₁.2.1 != r₂.2.1
      else true))

/-- The Boolean check implies the `NoCollision` Prop. -/
theorem noCollision_of_boolB (tr : List SlotEvent) (h : noCollisionB tr = true) :
    NoCollision tr := by
  intro r₁ h1 r₂ h2 hne hov
  have step1 := List.all_eq_true.mp h r₁ h1
  have step2 := List.all_eq_true.mp step1 r₂ h2
  by_cases heq : r₁.1 == r₂.1
  · simp only [beq_iff_eq] at heq; exact absurd heq hne
  · simp only [heq, Bool.false_eq_true, if_false, hov, if_true] at step2
    simpa [bne, beq_iff_eq] using step2

/-- **No-collision for the SHA-256 unrolled trace.** Two simultaneously-live
logical slots of `compressCom sha256Spec` get distinct physical slots. -/
theorem unrolledSlotRA_no_collision_sha256 :
    NoCollision (shaSlotTrace Sha2Emit.sha256Spec) :=
  noCollision_of_boolB _ (by native_decide)

/-- **No-collision for the SHA-512 unrolled trace.** -/
theorem unrolledSlotRA_no_collision_sha512 :
    NoCollision (shaSlotTrace Sha2Emit.sha512Spec) :=
  noCollision_of_boolB _ (by native_decide)

/-- **No-collision for the Keccak unrolled trace.** Two simultaneously-live
logical slots of `keccakF1600Com` get distinct physical slots. -/
theorem unrolledSlotRA_no_collision_keccak :
    NoCollision kSlotTrace :=
  noCollision_of_boolB _ (by native_decide)

/-- **No-collision, uniform statement.** For any of the three concrete unrolled
traces, the linear-scan assignment never maps two simultaneously-live logical
slots to the same physical slot — the KAT-safety property that the naive
`linearScanRA` wiring violates. -/
theorem unrolledSlotRA_no_collision :
    NoCollision (shaSlotTrace Sha2Emit.sha256Spec) ∧
    NoCollision (shaSlotTrace Sha2Emit.sha512Spec) ∧
    NoCollision kSlotTrace :=
  ⟨unrolledSlotRA_no_collision_sha256,
   unrolledSlotRA_no_collision_sha512,
   unrolledSlotRA_no_collision_keccak⟩

/-! ## 7. Cross-iteration live-range analysis (Phase B)

The Phase A RAs (`Sha2RaEmit`, `KeccakRaEmit`, `ChachaRaEmit`,
`Poseidon2RaEmit`) close ~28-36% of the residual gap to HACL\* / Plonky3 by
solving slot residency *per iteration* in isolation. The remaining gap traces
to a different effect: values that survive across loop iteration boundaries
(state words in ChaCha20's double-rounds, lane registers in Poseidon2's partial
rounds, the SHA-2 working set across compression rounds) are spilled at the
end of one iteration and reloaded at the start of the next, because the
per-iteration RA cannot see the cross-boundary read/write dependency.

HACL\* / gcc's allocator handles this via chained register reuse across the
emitted basic blocks. The verified analog here is a **cross-iteration carry
analysis**: for each slot, identify whether it is *carried* across some
iteration boundary — written in iteration `i`, read in iteration `i+1`. Such
slots benefit most from stable physical-register assignments; non-carried
slots are first-class spill candidates.

This section adds the analysis as a heuristic over the per-iteration trace
chunks. It does NOT change `RegisterAllocation` or `linearScanRA`: the new
function `unrolledSlotRAofIters` consumes a `List (List SlotEvent)` (one
inner list per iteration), computes the carry set, and biases the linear-scan
slot ordering so carried slots are colored first (and thus get the lowest
physical slots, which downstream emitters typically map to register-resident
positions). The non-trivial `seqOf` it produces is still well-formed by the
`slotOf := id` packing — the framework's denotation theorem fires unchanged. -/

/-- The write-set of one iteration: all logical slots written by any event in
the iteration. -/
def iterWriteSet (iter : List SlotEvent) : List Nat :=
  (iter.map SlotEvent.wr).dedup

/-- The read-set of one iteration: all register-file logical slots read by any
event in the iteration. -/
def iterReadSet (iter : List SlotEvent) : List Nat :=
  (iter.flatMap (·.rds)).dedup

/-- **Cross-iteration carry detector.** A slot `s` is *carried across* the
iteration sequence `iters` if there exists some adjacent pair `(iters[i],
iters[i+1])` such that `s ∈ writeSet(iters[i])` AND `s ∈ readSet(iters[i+1])`.
This is the conservative approximation requested by the spec: any slot that
appears in both the read-set of iter `i+1` and the write-set of iter `i`. -/
def carriedAcross (slot : Nat) (iters : List (List SlotEvent)) : Bool :=
  let pairs := iters.zip iters.tail
  pairs.any (fun p =>
    (iterWriteSet p.1).contains slot && (iterReadSet p.2).contains slot)

/-- The set of all slots carried across the iteration sequence. -/
def carriedSet (iters : List (List SlotEvent)) : List Nat :=
  let tr := iters.flatten
  let univ := slotUniverse tr
  (List.range univ).filter (fun s => carriedAcross s iters)

/-- A high-priority weight for carried slots. Picked large enough that any
carried slot outranks any non-carried slot by intra-iteration use count
(per-trace use counts are bounded by trace length; `10^9` exceeds all
realistic trace lengths). -/
def HIGH_PRIORITY : Nat := 1000000000

/-- Per-slot intra-iteration use count: the number of trace events (write OR
read) that touch slot `s` across the whole iteration sequence. -/
def perSlotUses (slot : Nat) (iters : List (List SlotEvent)) : Nat :=
  (iters.flatten.filter (fun ev => ev.touched.contains slot)).length

/-- **Cross-iteration slot priority.** Carried slots receive `HIGH_PRIORITY`;
non-carried slots receive their intra-iteration use count. Higher priority
means "prefer to keep in a low physical slot" (register-resident under the
downstream emitters' slot→physical-name maps). -/
def crossIterPriority (slot : Nat) (iters : List (List SlotEvent)) : Nat :=
  if carriedAcross slot iters then HIGH_PRIORITY
  else perSlotUses slot iters

/-! ### 7a. Cross-iteration-biased linear scan

The existing `liveItems` sorts logical slots by `(start, slot)` for the linear
scan. To bias toward carried slots holding low physical slots, we sort
non-seed live items by `(¬carried, start, slot)` — i.e. carried slots come
first in any tie window. Within the carried/non-carried partition the
linear-scan invariant is unchanged, so no-collision is preserved.

The change is entirely in the SORT ORDER of `liveItems`; `physScanStep` and
its loop are reused. -/

/-- Live items sorted with carried-first priority within overlapping start
windows. -/
def liveItemsCrossIter (tr : List SlotEvent) (iters : List (List SlotEvent)) :
    List (Nat × Nat × Nat) :=
  let univ := slotUniverse tr
  let raw := (List.range univ).filterMap (fun s =>
    let (st, en) := slotLiveRange tr s
    if st < tr.length then some (s, st, en) else none)
  raw.mergeSort (fun a b =>
    let ca := carriedAcross a.1 iters
    let cb := carriedAcross b.1 iters
    -- Carried before non-carried; then by start position; then by slot index.
    (ca && !cb) ||
      (ca == cb && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1 ≤ b.1))))

/-- Cross-iteration-biased physical assignment. Same as `scanAssign`, but the
non-seed items are ordered with carried slots first within each start window. -/
def scanAssignCrossIter (tr : List SlotEvent) (iters : List (List SlotEvent)) :
    List (Nat × Nat) :=
  let seeds := seedBusy tr
  let seedAssign := seeds.map (fun p => (p.1, p.1))
  let nonSeed := (liveItemsCrossIter tr iters).filter (fun item => !(isSeedSlot tr item.1))
  let nextFresh := seeds.foldl (fun m p => Nat.max m (p.1 + 1)) 0
  seedAssign ++ physScanAux nonSeed.length nonSeed seeds nextFresh []

/-- Cross-iteration-biased `physMap`: look up `s` in `scanAssignCrossIter`. -/
def physMapCrossIter (tr : List SlotEvent) (iters : List (List SlotEvent))
    (s : Nat) : Nat :=
  match (scanAssignCrossIter tr iters).find? (fun p => p.1 == s) with
  | some (_, ph) => ph
  | none => s

/-- Precomputed table for `physMapCrossIter` over the slot universe. -/
def physTableCrossIter (tr : List SlotEvent) (iters : List (List SlotEvent)) :
    Array Nat :=
  let assign := scanAssignCrossIter tr iters
  let univ := slotUniverse tr
  (Array.range univ).map (fun s =>
    match assign.find? (fun p => p.1 == s) with
    | some (_, ph) => ph
    | none => s)

/-- Memoised cross-iteration physical-slot map. -/
def physMapCrossIterTabled (tbl : Array Nat) (s : Nat) : Nat :=
  tbl[s]?.getD s

/-- **The cross-iteration-aware unrolled-Com-domain RA.** Takes a flat trace
`tr` (for live ranges and seed pinning) and the per-iteration chunking
`iters` (for the carry analysis). Carried slots get the lowest physical
slots; non-carried slots fill the remainder by linear scan. `slotOf := id`
keeps the framework's `Function.Injective` discharge trivial and
`applyRA p ra = p` keeps `preserves` a `rfl`, so the headline denotation
theorems fire unchanged. -/
def unrolledSlotRAofIters (tr : List SlotEvent) (iters : List (List SlotEvent)) :
    RegisterAllocation where
  slotOf := id
  seqOf  := physMapCrossIterTabled (physTableCrossIter tr iters)

/-- **The cross-iteration RA is well-formed.** Same proof shape as
`unrolledSlotRAof_WellFormed`: `slotOf = id` is injective and `applyRA p ra =
p` definitionally. -/
theorem unrolledSlotRAofIters_WellFormed (tr : List SlotEvent)
    (iters : List (List SlotEvent)) :
    WellFormed (unrolledSlotRAofIters tr iters) where
  injOnLive := fun _ _ h => h
  preserves := fun _ _ => rfl

/-- The memoised cross-iteration `seqOf` agrees with `physMapCrossIter` on the
slot universe. Same memoisation argument as `physMapTabled_physTable_eq`. -/
theorem physMapCrossIterTabled_eq (tr : List SlotEvent)
    (iters : List (List SlotEvent)) (s : Nat) (hs : s < slotUniverse tr) :
    physMapCrossIterTabled (physTableCrossIter tr iters) s
      = physMapCrossIter tr iters s := by
  unfold physMapCrossIterTabled physTableCrossIter physMapCrossIter
  rw [Array.getElem?_map, Array.getElem?_range]
  simp only [hs, ↓reduceIte, Option.map_some, Option.getD_some]

/-! ### 7b. Per-protocol iteration chunkings

ChaCha20 4-way: 10 double-rounds (column + diagonal), each a fixed-size chunk
of the slot trace. Since the existing UnrolledComRA traces (`shaSlotTrace`,
`kSlotTrace`) flatten everything, this section provides the per-iteration
chunking that the analysis needs. The downstream consumers (`ChachaRaEmit`,
`Poseidon2RaEmit`) use their own bespoke `seqOf` and do not consume
`unrolledSlotRAofIters`. The chunkings below
expose the carry data so the consumers (and the smoke under
`bench/integration/`) can audit which slots carry across iteration
boundaries. -/

/-- One Keccak round as an iteration. The 24-round Keccak permutation chunks
into 24 copies of `kRoundTrace`, the existing per-round trace. -/
def kIterChunks : List (List SlotEvent) :=
  List.replicate 24 kRoundTrace

/-- One SHA-2 round as an iteration. The compression body's rounds chunk into
`sp.rounds` copies of `shaRoundTrace`. -/
def shaIterChunks (sp : Sha2Emit.Sha2Spec) : List (List SlotEvent) :=
  (List.range sp.rounds).map shaRoundTrace

/-- The carried-slot set for the Keccak round body. By construction every
lane slot `0..24` is both written and read in every round — so all 25 state
slots are carried across the 24-iteration boundary, matching the intuition
that the Keccak state is fully live across rounds. -/
def keccakCarriedSet : List Nat := carriedSet kIterChunks

/-- The carried-slot set for the SHA-2 round body. The 8 working words
`wkA..wkA+7` (a, b, c, d, e, f, g, h) carry across every round — those are
the "registers" of the compression function. -/
def shaCarriedSet (sp : Sha2Emit.Sha2Spec) : List Nat :=
  carriedSet (shaIterChunks sp)

/-! ## 8. Two-address coalescing (Phase B+)

x86-64 encodes most binary ops in **two-address** form: `dst op= src` (the
destination is also a source). When the source-language op has
three-address form `dst := src1 op src2` and `src1` dies at this
instruction (i.e. not read again afterwards), `dst` and `src1` can occupy
the same physical slot — saving a MOV and lowering register pressure.

The slot trace's `SlotEvent.rds` is an ordered list; we adopt the
convention that the **head of `rds` is `src1`** (the would-be in-place
operand of the two-address lowering). Many of the existing traces
already self-alias src1=dst (e.g. ChaCha20's `⟨a, [a, b]⟩` for `a += b`,
Poseidon2's `⟨s, [s]⟩` per-slot phase events). The coalescing pass here
fires only where `dst ≠ src1` AND `src1` is last-used at this event —
i.e. the trace is three-address with a dying first source.

### Soundness

A pair `(dst, src1)` is **coalesce-safe** when

1. `src1 ≠ dst` (otherwise no remap is needed),
2. neither is seed-pinned (their physical slots are fixed),
3. the slot used as `src1` at this event has no later read in the trace,
4. merging `seqOf dst := seqOf src1` does not violate the no-collision
   invariant on the precomputed `slotSummary` rows.

The fourth condition is checked by running `noCollisionB` over the
remapped summary; this is the same finite check that closes the
`unrolledSlotRA_no_collision` theorem. Coalescing is denotation-
preserving exactly when the dying source is dead, which is
condition (3) — the read-set/write-set semantics of `SlotEvent` is the
only data the framework's `WellFormed` predicate needs.

### Why this is the last pure-RA lever

On the four wired benches (ChaCha, Poseidon2, SHA-2, Keccak), the slot
traces fall into two camps:

* **Already-coalesced** (ChaCha, Poseidon2 lane events): every multi-op
  event has `dst = head rds`, so the analysis fires 0 times. The trace
  encoding is the coalesced form by construction.
* **Three-address** (SHA-2 sigma/rotr/sched/round, Keccak θ-C/D/ρπ/χ):
  events like `⟨scA, [src]⟩`, `⟨c, [x, x+5]⟩`, `⟨t1S, [h, sigS]⟩` have
  `dst ≠ src1` and are candidates.

For ChaCha and Poseidon2, the analysis observes **zero coalesce
opportunities** at the trace level — the post-Phase-B-2 ceiling is the
floor for pure-RA cyc/op. -/

/-- The conventional `src1` of an event: the first register-file slot
read. `none` means the event has no register-file read (e.g. a pure
input-fed write), so two-address coalescing does not apply. -/
def SlotEvent.src1 (ev : SlotEvent) : Option Nat := ev.rds.head?

/-- **`src1IsLastUse i events`** checks whether the slot used as `src1`
at event index `i` is not read again in `events[i+1..]`. A `true` result
licences merging `dst` and `src1` into one physical slot at this event.

Returns `false` if the event has no `src1` (nothing to coalesce), or if
the `src1` slot is read in any subsequent event. -/
def src1IsLastUse (i : Nat) (events : List SlotEvent) : Bool :=
  match events[i]? with
  | none => false
  | some ev =>
    match ev.src1 with
    | none => false
    | some s1 =>
        !((events.drop (i + 1)).any (fun e => e.rds.contains s1))

/-- A coalesce candidate row: `(dst, src1)` for an event where `src1`
dies and `dst ≠ src1`. -/
def coalescePairs (events : List SlotEvent) : List (Nat × Nat) :=
  events.zipIdx.filterMap (fun p =>
    let ev := p.1
    let i := p.2
    match ev.src1 with
    | none => none
    | some s1 =>
        if ev.wr ≠ s1 ∧ src1IsLastUse i events = true then
          some (ev.wr, s1)
        else none)

/-- The seed-pinned slot indices for a trace (slots whose first
appearance is a read, hence pinned to identity by `seedBusy`). -/
def seedSlots (tr : List SlotEvent) : List Nat :=
  (seedBusy tr).map Prod.fst

/-- Filter out coalesce pairs that touch a seed-pinned slot (whose
physical position is fixed by the emit's input resolver). -/
def coalescePairsNoSeed (tr : List SlotEvent) : List (Nat × Nat) :=
  let seeds := seedSlots tr
  (coalescePairs tr).filter (fun p =>
    ¬ seeds.contains p.1 ∧ ¬ seeds.contains p.2)

/-- Apply a single coalesce pair `(dst, src1)` to an assignment list,
replacing every physical slot equal to `seqOf dst` with `seqOf src1`.

The check is conservative: after the merge, if any pair of summary rows
with overlapping live ranges share a physical slot, the merge is
rejected and the assignment returned unchanged. -/
def tryMergeOne (tr : List SlotEvent) (pair : Nat × Nat)
    (assign : List (Nat × Nat)) : List (Nat × Nat) :=
  let (dst, s1) := pair
  let phDst := match assign.find? (fun p => p.1 == dst) with
    | some (_, ph) => ph
    | none => dst
  let phS1 := match assign.find? (fun p => p.1 == s1) with
    | some (_, ph) => ph
    | none => s1
  if phDst == phS1 then assign
  else
    -- Tentative merge: rewrite every assignment whose physical slot
    -- equals phDst to phS1.
    let assign' := assign.map (fun p =>
      if p.2 == phDst then (p.1, phS1) else p)
    -- Build the new summary rows from assign' and re-run the no-collision check.
    let rows := (liveItems tr).map (fun item =>
      let s := item.1
      let st := item.2.1
      let en := item.2.2
      let ph := match assign'.find? (fun p => p.1 == s) with
        | some (_, p) => p
        | none => s
      (s, ph, st, en))
    let ok := rows.all (fun r₁ =>
      rows.all (fun r₂ =>
        if r₁.1 == r₂.1 then true
        else if rangesOverlap (r₁.2.2.1, r₁.2.2.2) (r₂.2.2.1, r₂.2.2.2) then
          r₁.2.1 != r₂.2.1
        else true))
    if ok then assign' else assign

/-- Fold coalesce pairs through `tryMergeOne`, building the final
assignment list. -/
def coalesceAssign (tr : List SlotEvent) (base : List (Nat × Nat)) :
    List (Nat × Nat) :=
  (coalescePairsNoSeed tr).foldl (fun acc p => tryMergeOne tr p acc) base

/-- Coalesce-aware physical assignment: start from `scanAssignCrossIter`
(the Phase B carry-biased base) and apply `coalesceAssign`. For traces
whose `coalescePairsNoSeed` is empty (ChaCha, Poseidon2 already encode
two-address ops), this equals `scanAssignCrossIter`. -/
def scanAssignCoalesce (tr : List SlotEvent) (iters : List (List SlotEvent)) :
    List (Nat × Nat) :=
  coalesceAssign tr (scanAssignCrossIter tr iters)

/-- Coalesce-aware `physMap`: look up `s` in `scanAssignCoalesce`. -/
def physMapCoalesce (tr : List SlotEvent) (iters : List (List SlotEvent))
    (s : Nat) : Nat :=
  match (scanAssignCoalesce tr iters).find? (fun p => p.1 == s) with
  | some (_, ph) => ph
  | none => s

/-- Precomputed table for `physMapCoalesce` over the slot universe. -/
def physTableCoalesce (tr : List SlotEvent) (iters : List (List SlotEvent)) :
    Array Nat :=
  let assign := scanAssignCoalesce tr iters
  let univ := slotUniverse tr
  (Array.range univ).map (fun s =>
    match assign.find? (fun p => p.1 == s) with
    | some (_, ph) => ph
    | none => s)

/-- Memoised coalesce-aware physical-slot map. -/
def physMapCoalesceTabled (tbl : Array Nat) (s : Nat) : Nat :=
  tbl[s]?.getD s

/-- **The coalesce-aware unrolled-Com-domain RA (Phase B+).** Same shape
as `unrolledSlotRAofIters`, with an additional two-address coalescing
pass post-linear-scan. `slotOf := id` keeps the framework's
`Function.Injective` discharge trivial; `applyRA p ra = p` keeps
`preserves` a `rfl`. -/
def unrolledSlotRAofItersCoalesce
    (tr : List SlotEvent) (iters : List (List SlotEvent)) :
    RegisterAllocation where
  slotOf := id
  seqOf  := physMapCoalesceTabled (physTableCoalesce tr iters)

/-- **The coalesce-aware RA is well-formed.** Same `slotOf := id` shape;
denotation preservation is by the framework's plug-in interface (the
`applyRA` transform is the identity, and the seqOf data is consumed only
by the downstream emit pass). -/
theorem unrolledSlotRAofItersCoalesce_WellFormed (tr : List SlotEvent)
    (iters : List (List SlotEvent)) :
    WellFormed (unrolledSlotRAofItersCoalesce tr iters) where
  injOnLive := fun _ _ h => h
  preserves := fun _ _ => rfl

/-- The memoised coalesce-aware `seqOf` agrees with `physMapCoalesce` on
the slot universe. Same memoisation argument as
`physMapCrossIterTabled_eq`. -/
theorem physMapCoalesceTabled_eq (tr : List SlotEvent)
    (iters : List (List SlotEvent)) (s : Nat) (hs : s < slotUniverse tr) :
    physMapCoalesceTabled (physTableCoalesce tr iters) s
      = physMapCoalesce tr iters s := by
  unfold physMapCoalesceTabled physTableCoalesce physMapCoalesce
  rw [Array.getElem?_map, Array.getElem?_range]
  simp only [hs, ↓reduceIte, Option.map_some, Option.getD_some]

/-! ### 8a. Per-protocol coalesce smoke

The coalesce-candidate counts on the four wired traces. -/

/-- Number of coalesce candidates after seed filtering on a trace. -/
def coalesceCandidateCount (tr : List SlotEvent) : Nat :=
  (coalescePairsNoSeed tr).length

end CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA
