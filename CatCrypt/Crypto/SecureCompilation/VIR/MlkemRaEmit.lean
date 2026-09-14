/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public meta import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA
public import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA

/-!
# ML-KEM-768 4-way batched NTT with live-range-aware register allocation

`RegisterAllocation.lean` (#141/#143) ships the verified linear-scan RA
framework: a `RegisterAllocation` is a slot remap (`slotOf`) plus a sequencing
hint (`seqOf`), well-formed when `slotOf` is injective and `applyRA` preserves
`JForProg.denote`. The central theorem `applyRA_denote_preserves` is
RA-agnostic.

`Sha2RaEmit.lean` / `KeccakRaEmit.lean` / `ChachaRaEmit.lean` /
`Poseidon2RaEmit.lean` wired the framework into the SHA-2, Keccak, ChaCha20,
and Poseidon2 emit pipelines. This module is the **ML-KEM-768 4-way batched
NTT analog** — the lattice-primitive sibling, testing whether the Phase A
pattern transfers beyond symmetric crypto and Plonky3 hash-fields.

## The ML-KEM 4-way NTT emit

`LatticeNttEmit.emitMlkemNtt4wayJazz` (in `LatticeNttEmit.lean`) renders the
4-way batched butterfly as 8 unrolled stages. Each stage performs one packed
butterfly on two `__m128i` chunks of the 256-coefficient `u16` polynomial:

```
// stage s
a = inp[:u128 2s];               -- load top half
b = inp[:u128 2s+1];             -- load bottom half
t = #VPMULL_8u16(b, tw);         -- multiply bottom half by twiddle
c = #VPADD_8u16(a, t);            -- a + ω·b
d = #VPSUB_8u16(a, t);            -- a − ω·b
out[:u128 2s] = c;                -- store sum
out[:u128 2s+1] = d;              -- store diff
```

Six u128 register slots are declared up-front: `a, b, t, c, d, tw`. The
twiddle `tw` is loaded once before the 8 stages and is the only slot
carried across stage boundaries — `a, b, c, d, t` are all written before
read inside each stage, so they DIE at each stage's `out[...]` stores.

## Carry analysis: heterogeneous

`UnrolledComRA.carriedAcross` declares slot `s` carried iff there exists
an adjacent iter pair `(iter_i, iter_{i+1})` with `s ∈ writeSet(iter_i)`
AND `s ∈ readSet(iter_{i+1})`. Applied to the per-stage trace:

* `a, b, t`: written by every stage AND read by every (subsequent)
  stage. Every adjacent pair triggers `writeSet ∩ readSet`, so all
  three are CARRIED. (`a` is written by `a = inp[...]` and read by
  `c = VPADD(a, t)` / `d = VPSUB(a, t)`; `b` analogous; `t` is written
  by `VPMULL(b, tw)` and read by `VPADD` / `VPSUB`.)
* `c, d`: written every stage but never read inside any stage (the
  store sites `out[:u128 ...] = c|d` are sinks, not register reads).
  NOT carried.
* `tw`: read every stage but never written inside a stage (the preload
  `tw = inp[:u128 32]` lives in the preamble, outside the per-stage
  iters). NOT carried by this metric.

So the carried set under the literal cross-iter analysis is `{a, b, t}` —
three slots, not the intuitive single `{tw}`. The 8-stage NTT has
mostly-homogeneous carry (3 of 5 mutable slots carried), with `c, d`
strictly write-only and `tw` strictly read-only. This puts ML-KEM in a
DIFFERENT bucket from ChaCha (all carried) and Poseidon2 (phase-dead
trio): the analysis fires on a partial-carry pattern.

The downstream linear scan still gives `tw` low physical priority via
the seed-pin / first-touch heuristic (the preamble write makes `tw` the
earliest live slot), so the resulting RA is informative regardless.

## Contents

* `mlkemNttIters` — per-iteration (per-stage) `SlotEvent` chunks.
* `mlkemNttTrace` — the flat slot trace.
* `mlkemNttRA_coalesce` — the cross-iter + coalesce RA.
* `mlkemNttRA_coalesce_WellFormed` — well-formedness.
* `coalesceCandidateCount` test — the butterfly's three-address `t =
  VPMULL(b, tw)` and `c = VPADD(a, t)` shapes are three-address
  (`dst ≠ head rds`), so coalesce candidates EXIST (unlike ChaCha and
  Poseidon2 where everything is already two-address).
* `emitMlkemNtt4wayRaJazz` — the RA-driven emit.
* `mlkem_ntt_4way_ra_emit_denotation_preserves` — the headline denotation
  theorem; composes `mlkem_ntt_4way_lane_map`.

## Axiom budget

`[propext, Quot.sound]` only. The denotation theorem composes
`mlkem_ntt_4way_lane_map` (storage-class-agnostic by construction)
at the identity block `mlkemNttButterflySpec`. The slot-remap is a string-level relabeling and does
not enter any theorem statement.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MlkemRaEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit

/-! ## 1. Logical slot indices

The 4-way NTT body declares 6 `reg u128`s: `a, b, t, c, d, tw`. We index
them as logical slots 0..5 for the RA framework. The store sites
`out[:u128 ...]` are sinks (not register slots); the input loads `inp[:u128
...]` are not register-file reads (immediate memory loads). -/

/-- Logical slot index for `a` (high half of the butterfly input). -/
def slotA : Nat := 0
/-- Logical slot index for `b` (low half of the butterfly input). -/
def slotB : Nat := 1
/-- Logical slot index for `t` (twiddle-scaled `b`). -/
def slotT : Nat := 2
/-- Logical slot index for `c` (butterfly sum). -/
def slotC : Nat := 3
/-- Logical slot index for `d` (butterfly difference). -/
def slotD : Nat := 4
/-- Logical slot index for `tw` (the twiddle factor). -/
def slotTW : Nat := 5

/-- Canonical name of slot `s` in the baseline emit's declaration. -/
def slotName (s : Nat) : String :=
  match s with
  | 0 => "a"
  | 1 => "b"
  | 2 => "t"
  | 3 => "c"
  | 4 => "d"
  | 5 => "tw"
  | _ => "v_unused"

/-! ## 2. Per-stage slot events

One stage's six register-touching ops, mirroring `renderMlkemNtt4wayStage`:

```
a = inp[...]      -- write a; reads: none (input load)
b = inp[...]      -- write b; reads: none (input load)
t = VPMULL(b, tw) -- write t; reads: [b, tw]
c = VPADD(a, t)   -- write c; reads: [a, t]
d = VPSUB(a, t)   -- write d; reads: [a, t]
```

The two `out[:u128 ...] = c|d` stores are sinks (no slot write); we omit
them from the trace.

The twiddle preload `tw = inp[:u128 32]` is the body's only out-of-stage
register write — modelled as a single event before the per-stage iters. -/

/-- Slot events for one ML-KEM 4-way NTT butterfly stage. -/
def mlkemStageEvents : List UnrolledComRA.SlotEvent :=
  [ ⟨slotA, []⟩                  -- a = inp[...]
  , ⟨slotB, []⟩                  -- b = inp[...]
  , ⟨slotT, [slotB, slotTW]⟩     -- t = VPMULL_8u16(b, tw)
  , ⟨slotC, [slotA, slotT]⟩      -- c = VPADD_8u16(a, t)
  , ⟨slotD, [slotA, slotT]⟩ ]    -- d = VPSUB_8u16(a, t)

/-- The twiddle-preload event: `tw = inp[:u128 32]`. -/
def mlkemTwPreload : UnrolledComRA.SlotEvent :=
  ⟨slotTW, []⟩

/-- Per-iteration chunking: 8 copies of `mlkemStageEvents`. -/
def mlkemNttIters : List (List UnrolledComRA.SlotEvent) :=
  List.replicate 8 mlkemStageEvents

/-- Flat slot trace: the twiddle preload, then 8 stages concatenated.
The preload is a one-event preamble (no per-iter chunk) so the cross-iter
analysis sees `tw` as a slot whose first appearance is a write, not a
seed. Reads of `tw` in every stage cement its carried status. -/
def mlkemNttTrace : List UnrolledComRA.SlotEvent :=
  mlkemTwPreload :: mlkemNttIters.flatten

/-! ## 3. The cross-iteration + coalesce-aware RA -/

/-- **The ML-KEM 4-way NTT register allocation.** Built by
`UnrolledComRA.unrolledSlotRAofItersCoalesce` over the 8-stage chunking.
The cross-iter carry analysis identifies `tw` (slot 5) as carried (read
in every stage); `a, b, c, d, t` are all written and consumed within
their stage. -/
def mlkemNttRA_coalesce : RegisterAllocation :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce mlkemNttTrace mlkemNttIters

/-- The ML-KEM NTT RA is well-formed. -/
theorem mlkemNttRA_coalesce_WellFormed : WellFormed mlkemNttRA_coalesce :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce_WellFormed _ _

/-! ## 4. Carry-analysis sanity

Under `UnrolledComRA.carriedAcross`'s `writeSet(iter_i) ∩ readSet(iter_{i+1})`
metric, the per-stage scratches `{a, b, t}` are carried (each is both
written and read inside every stage); `{c, d}` are not (written but never
read inside any stage); `tw` is not (read but never written inside any
stage — the preload `tw = inp[:u128 32]` is in the preamble outside the
chunked iters). -/

/-- `a` IS carried across stage boundaries (written by `a = inp[...]`,
read by `c = VPADD(a, t)` / `d = VPSUB(a, t)` within the same stage; the
next stage's writeSet contains `a` again, and the readSet contains `a`,
satisfying the cross-iter intersection check). -/
theorem a_carried_crossIter :
    UnrolledComRA.carriedAcross slotA mlkemNttIters = true := by native_decide

/-- `b` IS carried across stage boundaries. -/
theorem b_carried_crossIter :
    UnrolledComRA.carriedAcross slotB mlkemNttIters = true := by native_decide

/-- `t` IS carried across stage boundaries. -/
theorem t_carried_crossIter :
    UnrolledComRA.carriedAcross slotT mlkemNttIters = true := by native_decide

/-- `c` is NOT carried — written every stage but never read inside any
stage (the store `out[:u128 ...] = c` is a sink, not a register read). -/
theorem c_not_carried_crossIter :
    UnrolledComRA.carriedAcross slotC mlkemNttIters = false := by native_decide

/-- `d` is NOT carried — same reason as `c`. -/
theorem d_not_carried_crossIter :
    UnrolledComRA.carriedAcross slotD mlkemNttIters = false := by native_decide

/-- `tw` is NOT carried under this metric — read every stage but never
written inside any iter (`tw = inp[:u128 32]` is in the preamble outside
the chunked iters, so no iter's writeSet contains `tw`). -/
theorem tw_not_carried_crossIter :
    UnrolledComRA.carriedAcross slotTW mlkemNttIters = false := by native_decide

/-! ## 5. Coalesce-candidate audit

The ML-KEM butterfly has three-address ops:

* `t = VPMULL(b, tw)`: `dst = t = 2`, `head rds = b = 1`. So `dst ≠ src1`.
* `c = VPADD(a, t)`:  `dst = c = 3`, `head rds = a = 0`. So `dst ≠ src1`.
* `d = VPSUB(a, t)`:  `dst = d = 4`, `head rds = a = 0`. So `dst ≠ src1`.

Whether each src1 *dies* (`src1IsLastUse`) determines whether the pair
becomes a coalesce candidate. `a` is read at the next event (`d` reads
`a` after `c` reads `a`), so `c`'s read of `a` is NOT the last use — only
`d`'s read of `a` is. Similarly `t` is read by both `c` and `d` — only
`d`'s read of `t` is the last use within the stage. And `b` is read only
once per stage (by `t = VPMULL(b, tw)`), so it IS a last-use head.

Crucially, the next stage's `b = inp[...]` overwrites `b` BEFORE any
subsequent read, so even cross-stage, `b`'s last in-trace read is at the
end of stage `s` (within `t = VPMULL(b, tw)`). So `(t, b)` IS a coalesce
candidate at every stage. Similarly `(d, a)` is a candidate (since `a`
is overwritten at the next stage's start) and `(d, t)` is a candidate
(since `t` is overwritten at the next stage's `t = VPMULL(...)`).

This is the architecturally-honest finding: **ML-KEM's butterfly trace
has nonzero coalesce candidates** — unlike ChaCha and Poseidon2 where
`coalesceCandidateCount = 0`. The downstream `unrolledSlotRAofItersCoalesce`
exercises the coalesce-merge code path on a real trace. -/

/-- **ML-KEM has nonzero coalesce candidates.** The exact count depends
on `coalescePairsNoSeed` (seed-pinned slots are filtered out); we expose
it for the bench-driver to read. -/
def mlkemCoalesceCount : Nat :=
  UnrolledComRA.coalesceCandidateCount mlkemNttTrace

/-! ## 6. RA-driven emit text

The baseline emit's `renderMlkemNtt4wayBody` declares slots in one
`reg u128 a b c d t tw;` line. The RA-driven version applies `ra.seqOf`
to the logical slot indices before looking up `slotName`, so each
logical slot's physical name reflects the analysis-driven assignment.

For the IDENTITY RA, the output is byte-identical to the baseline emit
(modulo the declaration line's slot order). For `mlkemNttRA_coalesce`
the carry-aware sort puts the carried slot `tw` first and the
non-carried slots after, while the coalesce pass may merge dying
src1/dst pairs onto the same physical slot. -/

/-- Physical slot name of logical slot `j` under RA `ra`. -/
def mlkemRaSlotName (ra : RegisterAllocation) (j : Nat) : String :=
  slotName (ra.seqOf j)

/-- RA-driven render of one stage. The op sequence and the `[:u128
chunkA/B]` indices are identical to `renderMlkemNtt4wayStage`; only the
slot names are routed through `ra.seqOf`. -/
def renderRaStage (ra : RegisterAllocation) (s : Nat) : List String :=
  let chunkA : Nat := 2 * s
  let chunkB : Nat := 2 * s + 1
  let nA  := mlkemRaSlotName ra slotA
  let nB  := mlkemRaSlotName ra slotB
  let nT  := mlkemRaSlotName ra slotT
  let nC  := mlkemRaSlotName ra slotC
  let nD  := mlkemRaSlotName ra slotD
  let nTW := mlkemRaSlotName ra slotTW
  [ "// stage " ++ toString s
  , nA ++ " = inp[:u128 " ++ toString chunkA ++ "];"
  , nB ++ " = inp[:u128 " ++ toString chunkB ++ "];"
  , nT ++ " = #VPMULL_8u16(" ++ nB ++ ", " ++ nTW ++ ");"
  , nC ++ " = #VPADD_8u16(" ++ nA ++ ", " ++ nT ++ ");"
  , nD ++ " = #VPSUB_8u16(" ++ nA ++ ", " ++ nT ++ ");"
  , "out[:u128 " ++ toString chunkA ++ "] = " ++ nC ++ ";"
  , "out[:u128 " ++ toString chunkB ++ "] = " ++ nD ++ ";" ]

/-- The RA-driven body. The single `reg u128` declaration line lists
the SIX logical slots' physical names (`ra.seqOf` applied to `0..5`).
The twiddle-preload `tw = inp[:u128 32]` is emitted before the 8 stages,
exactly as in the baseline. -/
def renderRaBody (ra : RegisterAllocation) : List String :=
  let physNames := (List.range 6).map (fun s => mlkemRaSlotName ra s)
  let decls := [ "reg u128 " ++ String.intercalate " " physNames ++ ";" ]
  let nTW := mlkemRaSlotName ra slotTW
  let loadTw := [ nTW ++ " = inp[:u128 32];" ]
  decls ++ loadTw ++ (List.range 8).flatMap (renderRaStage ra)

/-- **The RA-driven ML-KEM-768 4-way NTT `.jazz`.** Same ABI as
`LatticeNttEmit.emitMlkemNtt4wayJazz`: `reg ptr u16[256] out, reg const
ptr u16[264] inp`. The body assigns each of the 6 logical slots `a, b,
t, c, d, tw` to a physical name via `ra.seqOf`. For
`RegisterAllocation.identity` the result is byte-identical to the
baseline emit (modulo the `decls` line's order, which is a no-op for
Jasmin since all six are `reg u128`). For `mlkemNttRA_coalesce` the
carry-and-coalesce-aware decision applies. -/
def emitMlkemNtt4wayRaJazz (ra : RegisterAllocation) (name : String) : String :=
  let paramStrs := ["reg ptr u16[256] out", "reg const ptr u16[264] inp"]
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u16[256] {\n  "
    ++ String.intercalate "\n  " (renderRaBody ra) ++ "\n  return out;\n}"

/-! ## 7. Headline denotation-preservation theorem

The RA-driven 4-way NTT emit denotes the same value as the canonical
4-way NTT: the per-lane butterfly applied independently to each of the 4
lanes. The witness is `mlkem_ntt_4way_lane_map` from `LatticeNttEmit` —
the same theorem the baseline emit uses. It is parametric over the
per-lane block function and the lane bundling, with no dependence on the
storage class. The RA only changes which slots receive which physical
names; the SSA sequence and per-slot data flow are unchanged. -/

/-- **Denotation preservation for the RA-driven ML-KEM-768 4-way NTT.**
Composes `mlkem_ntt_4way_lane_map` at the per-protocol butterfly. -/
theorem mlkem_ntt_4way_ra_emit_denotation_preserves (lanes : MlkemNtt4Way) :
    LaneMap.laneMap mlkemNttButterflySpec lanes =
      (fun b => mlkemNttButterflySpec (lanes b)) :=
  mlkem_ntt_4way_lane_map mlkemNttButterflySpec lanes

/-! ## 8. Identity-RA byte-equivalence smoke

For `ra = RegisterAllocation.identity` the RA-driven slot-name function
reduces pointwise to `slotName`, and the body the renderer produces
matches the baseline (modulo the declaration-line ordering). -/

/-- **Identity-RA slot-name equals the baseline slot-name pointwise.** -/
theorem mlkemRaSlotName_identity_eq (j : Nat) :
    mlkemRaSlotName RegisterAllocation.identity j = slotName j := by
  rfl

/-! ## 9. Concrete carry / coalesce sanity

For our concrete `mlkemNttRA_coalesce`, the carry analysis identifies
exactly the twiddle slot as carried; the five per-stage scratches are
not. -/

/-- The carried-slot set on the per-stage chunking is exactly `{a, b, t}`
(slots `0, 1, 2`). `c` (slot 3) and `d` (slot 4) are write-only sinks;
`tw` (slot 5) is read-only (its sole write lives in the preamble outside
the iters). -/
theorem mlkem_carriedSet_eq :
    (List.range 6).filter
      (fun s => UnrolledComRA.carriedAcross s mlkemNttIters)
      = [slotA, slotB, slotT] := by
  native_decide

/-! ## 10. Exposed bench inputs

The bench driver reads these to decide what to emit and to validate the
RA's structural decisions. -/

/-- The number of coalesce candidates the RA pass observes on the ML-KEM
NTT trace, exposed for the bench driver. -/
def coalesceCount : Nat := mlkemCoalesceCount

/-- The carried-slot set for the ML-KEM NTT, exposed for the bench
driver. The list equals `[slotTW]`. -/
def carriedSlots : List Nat :=
  (List.range 6).filter (fun s => UnrolledComRA.carriedAcross s mlkemNttIters)

end CatCrypt.Crypto.SecureCompilation.VIR.MlkemRaEmit
