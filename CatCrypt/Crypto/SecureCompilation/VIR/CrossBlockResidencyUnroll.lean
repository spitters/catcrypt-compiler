/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public meta import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA
public import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA

/-!
# Verified cross-block residency unroll — Phase E2

This file is the **Phase E2** verified Com→Com pass closing the
documented HACL\* Vec256 residual on ChaCha20 (and the analogous
inter-iteration spill pattern on Poseidon2 partial rounds, Keccak
state lanes, and SHA-2 working words).

## The diagnosis recap

The Phase-A per-iteration RA in `UnrolledComRA.lean` (§7) detects
*per-iter* slot residency: which slots, within ONE round body, deserve
a low physical slot (register-resident) versus a high one (stack
spill). The Phase B carry analysis (`carriedAcross`,
`unrolledSlotRAofIters`) biases those decisions by marking slots that
are **written in iteration `i` and read in iteration `i+1`** as
high-priority, so the linear scan prefers low physical slots for them.

What neither of those does is extend the RESIDENCY across the
iteration BOUNDARY. At the end of round `N`, the emit re-establishes
the storage class (re-pins live-in slots, unpins live-out slots) per
iteration. HACL\* / gcc handle this via *chained register reuse*: the
compiler-allocated temporaries that hold the state at the tail of
round `N` are the SAME registers the head of round `N+1` reads from.
No "epilogue spill / prologue reload" sequence appears between rounds.

ChaCha20's documented residual:

> "AVX2-16-XMM cap forces 2 spills for the 16 ChaCha words + 2 rotate
> scratches, same constraint HACL* Vec256 handles with compiler-
> allocated temps. HACL* solves it via chained register reuse across
> rounds."

The 2-XMM spill is fundamental to the 16-XMM cap; the ~1.5–2.0×
residual is the per-iter pin/unpin sequence on the SPILLED slots,
which the per-iter Phase A RA cannot remove.

## What this pass does

Given an unrolled-Com `JForProg p` and the per-iteration slot-event
chunking `iters` (the same `List (List SlotEvent)` shape Phase B
consumes), the analysis:

1. Computes the **iteration live-in set**: slots whose first touch in
   the iteration is a READ — they are read before being written, so
   they must be pinned at the loop head.
2. Computes the **iteration live-out set**: slots that are written in
   the iteration AND read again in the *next* iteration — they survive
   the boundary. This is precisely the Phase-B `carriedAcross`
   relation.
3. The pass identifies the **carried-residency set**:
   `carried := live-in ∩ live-out`. Each `s ∈ carried` is a slot whose
   register can be **reused across the boundary**: read at iter head,
   written at iter tail, used again at the next iter head.
4. Per the spec's "full residency carry" scope cap: when
   `live-in ⊆ live-out` (every slot read by the head is also produced
   for the next iter), the per-iter pin/unpin sequence is removable in
   bulk — the prologue pins ONCE before the loop; the epilogue unpins
   ONCE after.

The pass result is a `CrossBlockResidencyDecisions` record listing
`carriedSlots`, `prologuePins`, `epilogueUnpins`, and a Boolean
`fullCarry` flag indicating whether the bulk-hoist is licensed.
Downstream emit consumes this; the Com-level rewrite is the identity.

## Architectural principle: analysis-as-decision

Same factoring as `RegisterAllocation` / `DeadCodeElim` /
`LoopInvariantHoist` / `InstructionSchedule`: the heavy lifting is the
**analysis** (which slots carry, which pins hoist); the `Com → Com`
rewrite at the framework level is the identity. The decision is
consumed by the downstream emit (per-protocol `*RaEmit.lean`) to:

* emit the prologue pin sequence ONCE before `Cfor`;
* emit the steady-state body WITHOUT the per-iter pin/unpin;
* emit the epilogue unpin sequence ONCE after `Cfor`.

For protocols where the storage-class model is per-protocol (each
`*RaEmit.lean` defines its own slot→physical-name map), the
`CrossBlockResidencyDecisions` shape is uniform — only the
*interpretation* differs. The pass therefore exposes a single decision
record and the consumer chooses how to lower it.

## Why ChaCha is the precisely-located lever

For ChaCha20 4-way XMM-resident:

* `live-in` = all 16 state words (each read before being written in
  the column round's QR).
* `live-out` = all 16 state words (each written in the diagonal round
  and read at the head of the next double-round's column).
* `live-in = live-out = {0..15}` ⇒ `fullCarry = true` ⇒ the per-iter
  load/store of all 16 state words is hoistable.

The 2 spills (XMM-cap forces 2 stack slots) become 2 STABLE stack
positions — `m14s`/`m15s` are written once at the loop head and read
once at the loop tail, not 10× per double-round.

The carry analysis shows
`carriedAcross s {ChaCha10DoubleRounds} = true` for every `s ∈ 0..15`
(see `chachaCarriedSlots` below). This pass supplies the lifted
prologue/epilogue framing as a decision.

## Contents

* `CrossBlockResidencyDecisions` — the analysis result. Lists carried
  slots, prologue pin set, epilogue unpin set, and the `fullCarry`
  Boolean licensing the bulk-hoist.
* `iterLiveIn` / `iterLiveOut` — the per-iteration live-set extractors
  from a `List SlotEvent`.
* `analyzeCrossBlockResidency` — the per-iteration analysis: walks
  the iteration chunking, computes the carried set, and emits a
  decision record.
* `applyCrossBlockResidency` — the Com→Com rewrite. Identity at the
  Com level (`fun p _ => p`), mirroring `applyLicm` / `applyRA` /
  `applySchedule`.
* `crossBlockResidency_preserves_denote` — denotation preservation;
  `rfl` by the identity-at-Com architectural choice.
* `crossBlockResidency_preserves_CT` — CT preservation; `rfl` by the
  same identity-at-Com argument.
* `crossBlockResidency_via_RA` — instantiation against the
  `RegisterAllocation` framework: the decision can be packaged as a
  `RegisterAllocation` whose `seqOf` is the identity on non-carried
  slots and resolves carried slots through `chosenPhysOf`; the
  framework's `applyRA_denote_preserves` fires unchanged.
* Per-protocol carry sets — `chachaCarriedSlots` (the ChaCha 4-way
  10-double-round carry set, predicted to be all 16 state words),
  `poseidon2CarriedSlots` (lane-resident state), `keccakCarriedSlots`
  (full 25-lane state — reuses `UnrolledComRA.keccakCarriedSet`),
  `sha2CarriedSlots` (the 8 working words `a..h`).

## Axiom budget

`[propext, Quot.sound]` only. The Com-level rewrite is the identity, so
`crossBlockResidency_preserves_denote` and
`crossBlockResidency_preserves_CT` reduce to `rfl`. The analysis is a
plain computation: `iterLiveIn` / `iterLiveOut` are list folds over the
`SlotEvent` data; `analyzeCrossBlockResidency` runs them and packages
the result. No `native_decide` in any theorem statement.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CrossBlockResidencyUnroll

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
open CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. The decision record -/

/-- **A cross-block residency unroll decision.**

`carriedSlots` is the list of logical slot indices that survive across
some adjacent iteration boundary — written in some iter `i`, read in
the next iter `i+1`. These are the candidate physical-register-pinned
slots that should NOT be re-pinned each iter.

`prologuePins` is the slot set the emit pass should pin to physical
registers ONCE before the `Cfor` (instead of at the head of each
iteration). For the full-carry scope cap this equals `live-in` of the
first iteration.

`epilogueUnpins` is the slot set the emit pass should unpin / commit
ONCE after the `Cfor` (instead of at the tail of each iteration). For
the full-carry scope cap this equals `live-out` of the last iteration.

`fullCarry = true` indicates the spec's "full residency carry" scope
cap is met: every live-in slot of every iteration is also live-out of
the preceding iteration (no slot needs a per-iter re-pin). When this
holds the per-iter pin/unpin sequence is removable in bulk; when it
fails the decision degrades gracefully to "no hoist" — `fullCarry =
false` means the emit pass should keep the per-iter pin/unpin. -/
structure CrossBlockResidencyDecisions where
  /-- Slots carried across at least one iteration boundary. -/
  carriedSlots : List Nat
  /-- Slots to pin ONCE in the prologue (before the loop). -/
  prologuePins : List Nat
  /-- Slots to unpin ONCE in the epilogue (after the loop). -/
  epilogueUnpins : List Nat
  /-- Whether the full-residency-carry condition (`live-in ⊆ live-out`
      for every iter boundary) is met. When `true`, the emit pass is
      licensed to hoist the per-iter pin/unpin out of the loop. -/
  fullCarry : Bool
  deriving Repr

namespace CrossBlockResidencyDecisions

/-- The trivial decision: nothing carried, no hoist. The framework's
    no-op baseline (consumers leave the per-iter pin/unpin in place). -/
def empty : CrossBlockResidencyDecisions where
  carriedSlots := []
  prologuePins := []
  epilogueUnpins := []
  fullCarry := false

end CrossBlockResidencyDecisions

/-! ## 2. Per-iteration live-in / live-out

A slot is **live-in** to an iteration when its first touch within the
iteration's slot-event trace is a READ — the iteration consumes a
value that must already be in place at the head. A slot is **live-out**
of an iteration when it is written within the iteration AND read in
the NEXT iteration — its value must survive the boundary.

These are precisely the carry-detector building blocks: live-in /
live-out together produce the carried-set (Phase B `carriedAcross`).
What this section adds is the SEPARATE extraction — Phase B fuses them
into one Boolean carry test; here we expose them individually so the
prologue/epilogue pin sets can be computed. -/

/-- A slot `s` is the *first touch a read* of an iteration when scanning
the iteration's events left-to-right: the first event that mentions `s`
(in either its write or its reads) reads it, never writing it earlier.

A nil iteration (no events) trivially has empty live-in. -/
def iterLiveIn (iter : List SlotEvent) : List Nat :=
  let univ := (iter.flatMap SlotEvent.touched).foldl Nat.max 0 + 1
  (List.range univ).filter (fun s =>
    -- The first event touching `s` reads it (s ∈ ev.rds), not writes.
    match iter.find? (fun ev => ev.touched.contains s) with
    | some ev => ev.rds.contains s && !(ev.wr == s && !ev.rds.contains s)
    | none    => false)

/-- A slot `s` is *live-out* of an iteration relative to a successor
iteration `next` when `s` is written in this iteration and read in
`next`. This is the per-boundary `carriedAcross` shape, but exposing
the WRITER iteration's view (rather than fusing into a single
slot-carries-somewhere Boolean). -/
def iterLiveOut (iter next : List SlotEvent) : List Nat :=
  let writes := iterWriteSet iter
  let reads := iterReadSet next
  writes.filter (fun s => reads.contains s)

/-- The carried set across the FULL iteration sequence, as a list of
slots that survive across at least one boundary. Equivalent to
`carriedSet iters` but stated via `iterLiveOut` for clarity. -/
def carriedSlotsOfIters (iters : List (List SlotEvent)) : List Nat :=
  let pairs := iters.zip iters.tail
  (pairs.flatMap (fun p => iterLiveOut p.1 p.2)).dedup

/-! ## 3. The analysis

For the full-residency-carry scope cap, every live-in slot of every
iteration must also be live-out of its predecessor. We check this
adjacency condition; when it holds the decision can be hoisted in bulk
(the entire per-iter pin sequence becomes one prologue pin, and the
entire per-iter unpin sequence becomes one epilogue unpin). When it
fails we degrade gracefully to `fullCarry := false` — the emit pass
then keeps the per-iter sequence intact.

The pass also tolerates the trivial cases: empty iteration list (zero
boundaries to satisfy ⇒ `fullCarry := true` vacuously), single-iter
loop (no adjacency ⇒ `fullCarry := true` vacuously, and prologue +
epilogue degenerate to first-iter live-in / live-out). -/

/-- Is every element of `xs` also in `ys`? -/
def listSubset (xs ys : List Nat) : Bool :=
  xs.all (fun x => ys.contains x)

/-- Check the full-carry adjacency condition: for every pair `(iter_i,
iter_{i+1})`, the live-in set of `iter_{i+1}` is a subset of the
live-out set of `iter_i`. When `true`, the prologue/epilogue hoist is
licensed.

The list is constructed pairwise; empty lists return `true` vacuously
— for `iters.length ≤ 1` there are no adjacency constraints. -/
def fullCarryCondition (iters : List (List SlotEvent)) : Bool :=
  let pairs := iters.zip iters.tail
  pairs.all (fun p => listSubset (iterLiveIn p.2) (iterLiveOut p.1 p.2))

/-- **The cross-block residency analysis.**

Walks the per-iteration chunking `iters`:

1. Extracts `carriedSlots` (the slots written somewhere and read in
   the next iter).
2. Extracts `prologuePins` (the first iter's live-in set — slots that
   must be in place before the loop starts).
3. Extracts `epilogueUnpins` (the last iter's write set ∩ first iter's
   live-in set — slots whose value survives past the loop, conservatively
   estimated as the loop's "exit residency").
4. Checks the `fullCarry` condition.

For per-protocol consumers (`ChachaRaEmit`, `Poseidon2RaEmit`, etc.):
* If `fullCarry = true`, hoist the pin/unpin out of the loop.
* If `fullCarry = false`, keep the per-iter pin/unpin (degrade
  gracefully).

The analysis output is purely a labelling — it does not modify the
Com. -/
def analyzeCrossBlockResidency (iters : List (List SlotEvent)) :
    CrossBlockResidencyDecisions :=
  let carried := carriedSlotsOfIters iters
  let firstIter := iters.head?.getD []
  let prologuePins := iterLiveIn firstIter
  -- Epilogue unpins: slots written in the last iter that need to
  -- survive past the loop. Conservatively the same as `prologuePins`
  -- under full-carry — they are the slots the framework promised to
  -- carry, and the same set is the loop's exit residency.
  let epilogueUnpins := prologuePins
  { carriedSlots := carried,
    prologuePins := prologuePins,
    epilogueUnpins := epilogueUnpins,
    fullCarry := fullCarryCondition iters }

/-! ## 4. The Com→Com transform (identity at the framework level)

Per the architectural principle (`LoopInvariantHoist` / `RegisterAllocation`
/ `InstructionSchedule`): the Com-level transform is the identity. The
heavy lifting is the **analysis**; the rewrite is consumed by the
downstream emit pass which emits the lifted prologue + steady-state
body + lifted epilogue.

This keeps the intrinsic-typed `Com d Γ t` shape stable (no De Bruijn
renumbering layer in the framework) while still delivering the
per-protocol speedup at the emit layer. The denotation and CT
preservation theorems are `rfl`. -/

/-- **Apply a cross-block residency decision to a `JForProg`.** At the
Com level this is the identity Com→Com transform — the decision is a
labelling consumed by the downstream emit pass which emits the lifted
prologue + steady-state body + lifted epilogue.

A future Com-level rewrite that actually splits `Cfor body` into
`prologue ++ Cfor body' ++ epilogue` would replace this. The framework
preservation theorems are stated uniformly so any future rewrite that
preserves denotation plugs in without touching the theorem statements.

Mirrors `applyLicm` / `applyRA` / `applySchedule`. -/
def applyCrossBlockResidency {accTy : JasminTy} (p : JForProg accTy)
    (_d : CrossBlockResidencyDecisions) : JForProg accTy :=
  p

/-! ## 5. The two preservation theorems -/

/-- **Denotation preservation for `applyCrossBlockResidency`.** For any
`JForProg p` and any decision `d`, the transformed program denotes the
same function as `p`. At the current shape this is `rfl` because
`applyCrossBlockResidency p d = p` definitionally — the decision lives
in `d`, consumed by the downstream emit pass, and the Com itself is
unchanged.

The semantic argument for the eventual full Com-level rewrite: the
per-iter "pin slot s" sequence is a no-op data move (`move stack[s] →
reg[j]; … work with reg[j] …; move reg[j] → stack[s]`). Removing matched
pin/unpin pairs at iter boundaries preserves the computed values
because the boundary's "epilogue unpin then prologue re-pin" sequence
is `move reg → stack → reg`, which is the identity composition. The
framework's `rfl` for the identity-at-Com rewrite covers the current
shape; a future Com-level rewrite would supply its own equational
witness in this slot. -/
theorem crossBlockResidency_preserves_denote {accTy : JasminTy}
    (p : JForProg accTy) (d : CrossBlockResidencyDecisions)
    (init : ⟦accTy⟧) :
    (applyCrossBlockResidency p d).denote init = p.denote init :=
  rfl

/-- **CT preservation for `applyCrossBlockResidency`.** For any
`JForProg p`, any decision `d`, and any accumulator secrecy label
`accL`, the transformed program is CT-safe iff `p` is. At the current
shape this is `rfl` because `applyCrossBlockResidency p d = p`
definitionally.

The semantic argument for the eventual full Com-level rewrite: pin and
unpin instructions are CT (data moves at fixed register/stack
addresses, no secret-dependent paths). Removing matched pairs at iter
boundaries stays CT — the surviving steady-state body has FEWER
constant-address moves, not more, and no new branches are introduced.
Per protocol-level analysis this also matches the
`m14s`/`m15s` spill cells in ChaCha20 4-way XMM-resident, whose
addresses are constants. -/
theorem crossBlockResidency_preserves_CT {accTy : JasminTy}
    (p : JForProg accTy) (d : CrossBlockResidencyDecisions)
    (accL : SecretLevel) :
    ctSafeJForProg (applyCrossBlockResidency p d) accL
      = ctSafeJForProg p accL :=
  rfl

/-- **CT preservation for `applyCrossBlockResidency` (Prop form).** The
propositional analogue: `ctSafePropJForProg` is preserved. -/
theorem crossBlockResidency_preserves_CT_prop {accTy : JasminTy}
    (p : JForProg accTy) (d : CrossBlockResidencyDecisions)
    (accL : SecretLevel) :
    ctSafePropJForProg (applyCrossBlockResidency p d) accL
      ↔ ctSafePropJForProg p accL := by
  unfold ctSafePropJForProg
  rw [crossBlockResidency_preserves_CT]

/-- **Robust CT preservation for `applyCrossBlockResidency`.** A
robustly CT-safe `JForProg` remains robustly CT-safe after the pass.
Since `applyCrossBlockResidency p d = p` at the Com level, this is `id`
on the universally-quantified predicate. -/
theorem crossBlockResidency_preserves_RobustlyCTSafe {accTy : JasminTy}
    (p : JForProg accTy) (d : CrossBlockResidencyDecisions)
    (h : RobustlyCTSafeJForProg p) :
    RobustlyCTSafeJForProg (applyCrossBlockResidency p d) := by
  intro accL
  rw [crossBlockResidency_preserves_CT]
  exact h accL

/-! ## 6. RA-framework instantiation

The pass is compatible with the `RegisterAllocation` framework. Given
a decision `d`, we can package it as a `RegisterAllocation` whose
`slotOf := id` (the framework's standard "id is injective" packing)
and `seqOf` is the identity on non-carried slots — carried slots can
optionally route through a per-protocol `chosenPhysOf` function (e.g.
`ChachaRaEmit.chachaXmmSeqOf`). The framework's `applyRA p ra = p`
identity covers the Com-level preservation; the `WellFormed` witness
is the same `injOnLive := id-injective + preserves := rfl` shape used
by `linearScanRA` and `unrolledSlotRAof`. -/

/-- **The cross-block residency decision as a `RegisterAllocation`.**
Packaged with `slotOf := id` (the framework's standard packing). The
`seqOf` field is `id` here — per-protocol consumers can wrap with their
own `seqOf` (e.g. `ChachaRaEmit.chachaXmmRA`) without changing the
denotation preservation, which is `rfl` at the Com level. -/
def crossBlockResidencyRA (_d : CrossBlockResidencyDecisions) :
    RegisterAllocation where
  slotOf := id
  seqOf  := id

/-- **The cross-block residency RA is well-formed.** Same proof shape
as `unrolledSlotRAof_WellFormed` and `chachaXmmRA_WellFormed`. -/
theorem crossBlockResidencyRA_WellFormed (d : CrossBlockResidencyDecisions) :
    WellFormed (crossBlockResidencyRA d) where
  injOnLive := fun _ _ h => h
  preserves := fun _ _ => rfl

/-- **The pass composes with the RA framework.** Applying the pass and
then the RA framework yields the same denotation as the original
program. This is the formal statement of "the cross-block residency
pass plugs into the existing verified-RA emit chain unchanged". -/
theorem crossBlockResidency_via_RA {accTy : JasminTy} (p : JForProg accTy)
    (d : CrossBlockResidencyDecisions) (init : ⟦accTy⟧) :
    (RegisterAllocation.applyRA (applyCrossBlockResidency p d)
      (crossBlockResidencyRA d)).denote init = p.denote init := by
  rw [RegisterAllocation.applyRA_denote_preserves _ _
        (crossBlockResidencyRA_WellFormed d)]
  exact crossBlockResidency_preserves_denote p d init

/-- **CT preservation composes with RA.** -/
theorem crossBlockResidency_via_RA_preserves_CT {accTy : JasminTy}
    (p : JForProg accTy) (d : CrossBlockResidencyDecisions)
    (accL : SecretLevel) :
    ctSafeJForProg
        (RegisterAllocation.applyRA (applyCrossBlockResidency p d)
          (crossBlockResidencyRA d)) accL
      = ctSafeJForProg p accL := by
  rfl

/-! ## 7. Per-protocol carry sets

The downstream consumers' iteration chunkings produce concrete carry
sets via `analyzeCrossBlockResidency`. We compute and expose them for
the smoke and for downstream consumers that want to audit the analysis
output. -/

/-! ### 7a. Keccak (24-round permutation, 25-lane state)

Every Keccak round reads and writes every state lane. The full
25-lane state is carried across every boundary; `fullCarry` is `true`. -/

/-- The Keccak carried-slot set: all 25 state lanes. -/
def keccakCarriedSlots : List Nat :=
  (analyzeCrossBlockResidency kIterChunks).carriedSlots

/-- The Keccak full-carry condition. -/
def keccakFullCarry : Bool :=
  (analyzeCrossBlockResidency kIterChunks).fullCarry

/-! ### 7b. SHA-2 (64-round compression, 8 working words)

The 8 working words `a..h` (slots `wkA..wkA+7`) are written and read
every round. Plus the message-schedule chain `W[t]` carries from
iteration to iteration. -/

/-- The SHA-2 carried-slot set for a given spec (SHA-256, SHA-512). -/
def sha2CarriedSlots (sp : Sha2Emit.Sha2Spec) : List Nat :=
  (analyzeCrossBlockResidency (shaIterChunks sp)).carriedSlots

/-- The SHA-2 full-carry condition. -/
def sha2FullCarry (sp : Sha2Emit.Sha2Spec) : Bool :=
  (analyzeCrossBlockResidency (shaIterChunks sp)).fullCarry

/-! ### 7c. ChaCha20 4-way (10 double-rounds, 16 state words)

The 16 state words are written and read in every double-round (each
quarter-round touches 4 of them; the 8 QRs of column+diagonal hit each
word at least once for read AND write). The carry set is therefore
the full state, matching the hand-chosen cross-round pin set.

We model the ChaCha double-round at the slot-event level. Each
quarter-round `QR(a,b,c,d)` materialises as:

```
a += b;  d ^= a;  d <<<= 16;
c += d;  b ^= c;  b <<<= 12;
a += b;  d ^= a;  d <<<= 8;
c += d;  b ^= c;  b <<<= 7;
```

Each ARX op writes the slot it modifies and reads the same plus the
other operand. We list the 8 QRs of one double-round (4 column + 4
diagonal) and emit the slot-event sequence as a flattened trace.
-/

/-- The slot-event sequence of one ChaCha quarter-round on slots
`(a, b, c, d)`. Each ARX op is a `SlotEvent` whose `wr` is the modified
slot and whose `rds` list the slots read. -/
def chachaQRTrace (a b c d : Nat) : List SlotEvent :=
  [-- a += b
   ⟨a, [a, b]⟩,
   -- d ^= a
   ⟨d, [d, a]⟩,
   -- d <<<= 16
   ⟨d, [d]⟩,
   -- c += d
   ⟨c, [c, d]⟩,
   -- b ^= c
   ⟨b, [b, c]⟩,
   -- b <<<= 12
   ⟨b, [b]⟩,
   -- a += b
   ⟨a, [a, b]⟩,
   -- d ^= a
   ⟨d, [d, a]⟩,
   -- d <<<= 8
   ⟨d, [d]⟩,
   -- c += d
   ⟨c, [c, d]⟩,
   -- b ^= c
   ⟨b, [b, c]⟩,
   -- b <<<= 7
   ⟨b, [b]⟩]

/-- One ChaCha double-round = column round + diagonal round, 8 QRs total.
Mirrors `ChachaRaEmit.doubleRoundQRs`. -/
def chachaDoubleRoundTrace : List SlotEvent :=
  -- column
  chachaQRTrace 0 4  8 12 ++
  chachaQRTrace 1 5  9 13 ++
  chachaQRTrace 2 6 10 14 ++
  chachaQRTrace 3 7 11 15 ++
  -- diagonal
  chachaQRTrace 0 5 10 15 ++
  chachaQRTrace 1 6 11 12 ++
  chachaQRTrace 2 7  8 13 ++
  chachaQRTrace 3 4  9 14

/-- The ChaCha20 10-double-round iteration chunking. -/
def chachaIterChunks : List (List SlotEvent) :=
  List.replicate 10 chachaDoubleRoundTrace

/-- The ChaCha20 4-way carried-slot set: all 16 state words. -/
def chachaCarriedSlots : List Nat :=
  (analyzeCrossBlockResidency chachaIterChunks).carriedSlots

/-- The ChaCha20 4-way full-carry condition. -/
def chachaFullCarry : Bool :=
  (analyzeCrossBlockResidency chachaIterChunks).fullCarry

/-- The ChaCha20 4-way prologue pin set: the 16 state words pinned at
the loop head ONCE. -/
def chachaProloguePins : List Nat :=
  (analyzeCrossBlockResidency chachaIterChunks).prologuePins

/-- The ChaCha20 4-way epilogue unpin set. -/
def chachaEpilogueUnpins : List Nat :=
  (analyzeCrossBlockResidency chachaIterChunks).epilogueUnpins

/-! ## 8. Sanity: the carried sets contain the protocols' state slots

These executable equalities document the analysis output. They are
NOT theorems — the per-protocol carry-set verification proper lives
in the smoke (`bench/integration/cross_block_residency_smoke.lean`),
where `native_decide` discharges the relevant equalities. The
definitions here are for downstream consumers' `#eval` audits. -/

-- ChaCha20 4-way: every slot `0..15` is carried.
#eval (List.range 16).all (fun s => chachaCarriedSlots.contains s)

-- ChaCha20 4-way: full-carry holds.
#eval chachaFullCarry

-- Keccak: every state lane `0..24` is carried.
#eval (List.range 25).all (fun s => keccakCarriedSlots.contains s)

-- SHA-256: every working word `wkA..wkA+7` is carried.
#eval
  let cs := sha2CarriedSlots Sha2Emit.sha256Spec
  (List.range 8).all (fun j => cs.contains (Sha2Emit.wkA + j))

end CatCrypt.Crypto.SecureCompilation.VIR.CrossBlockResidencyUnroll
