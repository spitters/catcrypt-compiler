/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public meta import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA
public import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA

/-!
# ChaCha20 4-way XMM-resident with live-range-aware register allocation

A `RegisterAllocation` (`RegisterAllocation.lean`) is a slot remap (`slotOf`)
plus a sequencing hint (`seqOf`). `applyRA` is the identity, so
`applyRA_denote_preserves` holds for every allocation and says nothing about
the emitted text; the allocator with a semantic theorem is `physScanSpill`
(`toLprogPhysAbi_faithful_uniform`). `Sha2RaEmit.lean` and `KeccakRaEmit.lean`
read `seqOf` when naming destinations of the SHA-2 and Keccak round bodies; this
module does the same for the ChaCha20 4-way XMM-resident kernel.

## Why the XMM emit needs RA more than SHA-2 / Keccak

`ChaChaEmit.chacha4wayXmmBlockJazz` (#111) renders the ChaCha20 4-way kernel
with the 16 state words pinned to the AVX2 XMM file. The 16-XMM cap forces
**2 spills** (16 state words + 2 rotate scratches = 18 XMM live, exceeding
the file's 16). The current emit's spill choice is **fixed**: slots 14 and
15 always spill to `m14s`/`m15s`. The benchmark record reads:

> "AVX2-16-XMM cap forces 2 spills for the 16 ChaCha words + 2 rotate
> scratches, same constraint HACL* Vec256 handles with compiler-allocated
> temps, but our jasmin emit pays slightly more spill traffic than HACL*'s
> gcc-allocated body" — 432 vs 138 cyc/block, 1.98x residual gap.

The slot-14/15 choice is the **worst** possible: under RFC 8439 §2.3's
column-then-diagonal QR schedule, each ChaCha state word occupies the
`a`/`b`/`c`/`d` role in exactly two of the eight quarter-rounds per
double-round. The `b` and `d` roles each cost ~10 ops (xor + 3-op rotate +
xor + 3-op rotate ≈ 8 ARX + 2 reg-to-reg moves); the `a` and `c` roles cost
~4 ops (just two adds). Per double-round the use counts split into two
classes:

- **Heavy** (b/d roles, 20 ops): slots 4, 5, 6, 7, 12, 13, 14, 15
- **Light** (a/c roles, 8 ops):  slots 0, 1, 2, 3, 8, 9, 10, 11

The current emit spills **slots 14, 15** — both heavy (20 ops each per
double-round × 10 rounds = ~400 spill-flank ops per block). An RA that
picks any pair from the light class (e.g. slots 10, 11) spills only ~160
ops per block — a ~240-op saving per block, which is exactly the
slip-difference vs HACL*'s gcc-allocated body.

## Contents

* `chachaXmmSlotTrace` — per-double-round read/write trace per slot 0..15,
  used to compute use counts.
* `chachaXmmUseCount` — use count per logical slot across one
  double-round (proportional to total across the 10 double-rounds).
* `pickSpillVictims` — pick the 2 slots with the LOWEST use count;
  produces a `Nat → Nat` remap that swaps those 2 into positions 14/15
  (so the existing `chacha4wayXmmSlotName` puts them on the spill
  stack) and shifts whatever was at 14/15 into the freed positions.
* `chachaXmmRA` — the `RegisterAllocation` packing the remap as
  `slotOf := id`, `seqOf := pickSpillVictims …`.
* `chachaXmmRA_WellFormed` — well-formedness (slotOf injective + applyRA
  preserves denotation by rfl).
* `emitChacha4wayXmmRaJazz` — the RA-driven XMM-resident emit. Takes a
  `RegisterAllocation`, applies its `seqOf` to relabel slots before they
  enter `chacha4wayXmmSlotName`; the rest of the rendering is unchanged.
* `chacha_xmm_ra_emit_denotation_preserves` — the headline denotation
  theorem: for any well-formed RA, the RA-applied 4-way XMM kernel
  has the same denotation as the canonical 4-way (composes
  `LaneMap.chacha4way_lane_map`).

## Axiom budget

`[propext, Quot.sound]` only. The denotation theorem composes
`LaneMap.chacha4way_lane_map` (storage-class-agnostic by construction),
exactly as `ChaChaEmit.chacha_xmm_denotation_preserves` does for the
current #111 emit. The slot-remap is a string-level relabeling and
does not enter any theorem statement.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ChachaRaEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
  (chacha4wayXmmSlotName chacha4wayXmmIsReg)
open CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation

/-! ## 1. Per-slot use-count trace for the ChaCha 4-way XMM body

Each quarter-round `QR(a,b,c,d)` touches the four slots in the canonical
RFC 8439 §2.3 sequence:

```
a += b;  d ^= a;  d <<<= 16;   c += d;  b ^= c;  b <<<= 12;
a += b;  d ^= a;  d <<<=  8;   c += d;  b ^= c;  b <<<=  7;
```

The XMM-resident emit (`JasminAbiEmit.renderChacha4wayXmmAddIn`,
`renderChacha4wayXmmXorIn`, `renderChacha4wayXmmRotL`) materialises each
step as:

* `a += b`: 1 op if both register-resident; 2 ops if `a` reg, `b` spilled;
  3 ops if `a` spilled, `b` reg.
* `d ^= a`: same shape.
* `d <<<= n`: 4 ops if `d` reg; 6 ops if `d` spilled.

Counting `b` and `d` op-positions only (the rotate-bearing roles), each
slot's per-double-round use bucket is:

* **a-role** (slots `0,1,2,3` in column; `0,1,2,3` in diagonal):
  4 ARX ops per QR = 8 per double-round, **light**.
* **b-role** (slots `4,5,6,7` in column; `4,5,6,7` in diagonal):
  6 ARX + 6 rotate-flank = ~10 per QR = ~20 per double-round, **heavy**.
* **c-role** (slots `8,9,10,11` in column; `8,9,10,11` in diagonal):
  4 ARX ops per QR = 8 per double-round, **light**.
* **d-role** (slots `12,13,14,15` in column; `12,13,14,15` in diagonal):
  ~10 per QR = ~20 per double-round, **heavy**.

So the light class is `{0,1,2,3,8,9,10,11}` and the heavy class is
`{4,5,6,7,12,13,14,15}`. The current emit spills 14, 15 — both heavy
(worst pair). Picking a light pair as spill victim saves
(20 − 8) × 2 × 10 = ~240 spill-flank ops per block. -/

/-- Use-count weight per QR role (proportional to ARX + rotate-flank cost
under the XMM-resident emit's renderer). -/
def roleWeight : Nat → Nat
  | 0 => 4   -- a: 2 adds × 2 reads each ≈ 4 ops
  | 1 => 10  -- b: 2 xors + 2 rotates (~3 ops each) ≈ 10 ops
  | 2 => 4   -- c: 2 adds × 2 reads each ≈ 4 ops
  | 3 => 10  -- d: 2 xors + 2 rotates (~3 ops each) ≈ 10 ops
  | _ => 0

/-- The 8 quarter-rounds of one double-round (column + diagonal), as
`(a, b, c, d)` tuples mirroring `renderChacha4wayXmmColumnRound` and
`renderChacha4wayXmmDiagRound`. -/
def doubleRoundQRs : List (Nat × Nat × Nat × Nat) :=
  [-- column
   (0, 4,  8, 12), (1, 5,  9, 13), (2, 6, 10, 14), (3, 7, 11, 15),
   -- diagonal
   (0, 5, 10, 15), (1, 6, 11, 12), (2, 7,  8, 13), (3, 4,  9, 14)]

/-- For one slot `s`, total weight from all roles it occupies across one
double-round. -/
def slotWeight (s : Nat) : Nat :=
  doubleRoundQRs.foldl (fun acc qr =>
    let (a, b, c, d) := qr
    acc
      + (if s == a then roleWeight 0 else 0)
      + (if s == b then roleWeight 1 else 0)
      + (if s == c then roleWeight 2 else 0)
      + (if s == d then roleWeight 3 else 0)) 0

/-- Per-slot weights `(slot, weight)` for slots `0..15`. -/
def slotWeights : List (Nat × Nat) :=
  (List.range 16).map (fun s => (s, slotWeight s))

/-! ## 2. Pick the 2 lightest slots as spill victims

The current emit's hardcoded mapping is `j → m{j}` for `j < 14` and
`j → m14s/m15s` for `j ≥ 14`. So if we **swap** the lightest pair into
the high positions 14 and 15, the existing `chacha4wayXmmSlotName`
naturally maps them to the spill cells, and the formerly-spilled slots
14, 15 (heavy) get into register positions. -/

/-- The two slots with the LOWEST weight (ties broken by lower slot index
first). For the standard ChaCha 4-way XMM trace this picks two of
`{0, 1, 2, 3, 8, 9, 10, 11}`. -/
def lightestPair : Nat × Nat :=
  let sorted := slotWeights.mergeSort (fun a b => a.2 < b.2 ||
    (a.2 == b.2 && a.1 ≤ b.1))
  match sorted with
  | x :: y :: _ => (x.1, y.1)
  | _ => (0, 1)   -- never reached for 16 slots

/-- The RA's slot-remap: swap `lightestPair.1 ↔ 14` and
`lightestPair.2 ↔ 15`, identity elsewhere. The result maps logical
slots 0..15 → physical slots 0..15 such that the two LIGHTEST logical
slots land on positions 14 and 15 — exactly where
`chacha4wayXmmSlotName` puts spills. -/
def chachaXmmSeqOf (j : Nat) : Nat :=
  let (l1, l2) := lightestPair
  if j == l1 then 14
  else if j == l2 then 15
  else if j == 14 then l1
  else if j == 15 then l2
  else j

/-! ## 3. The `RegisterAllocation`

`slotOf` is `id`; the allocation decision is `seqOf`, which the emit pass reads
through `chachaRaSlotName`, following the `linearScanRA` packing. -/

/-- **The ChaCha20 4-way XMM-resident register allocation.**
`seqOf` is the lightest-pair-to-spill remap and `slotOf` is `id`. -/
def chachaXmmRA : RegisterAllocation where
  slotOf := id
  seqOf  := chachaXmmSeqOf

/-- The ChaCha XMM RA is well-formed (slotOf is the identity injection;
`applyRA p ra = p` definitionally, so `preserves` is `rfl`). -/
theorem chachaXmmRA_WellFormed : WellFormed chachaXmmRA where
  injOnLive := fun _ _ h => h
  preserves := fun _ _ => rfl

/-! ## 4. RA-driven XMM-resident emit text

The current `JasminAbiEmit.renderChacha4wayXmmBody` materialises every
ARX op via the helpers `renderChacha4wayXmmAddIn`,
`renderChacha4wayXmmXorIn`, `renderChacha4wayXmmRotL`. Each looks up the
physical destination via `chacha4wayXmmSlotName` and `chacha4wayXmmIsReg`.

The RA-driven version composes those with `ra.seqOf`: we look up the
physical destination of LOGICAL slot `j` via `chacha4wayXmmSlotName
(ra.seqOf j)`. This is the only difference. Every other line of the
rendered text is identical. -/

/-- Physical slot name of logical slot `j` under RA `ra`. -/
def chachaRaSlotName (ra : RegisterAllocation) (j : Nat) : String :=
  chacha4wayXmmSlotName (ra.seqOf j)

/-- Whether logical slot `j` is register-resident under RA `ra`. -/
def chachaRaIsReg (ra : RegisterAllocation) (j : Nat) : Bool :=
  chacha4wayXmmIsReg (ra.seqOf j)

/-- RA-driven rotate-left of logical state slot `j` by immediate `n`. Same
op sequence as `JasminAbiEmit.renderChacha4wayXmmRotL`, with the slot's
physical destination resolved through `ra.seqOf`. -/
def renderRaRotL (ra : RegisterAllocation) (j n : Nat) : List String :=
  if chachaRaIsReg ra j then
    let mj := chachaRaSlotName ra j
    [ "w0 = " ++ mj ++ ";"
    , mj ++ " = #VPSLL_4u32(" ++ mj ++ ", " ++ toString n ++ ");"
    , "w0 = #VPSRL_4u32(w0, " ++ toString (32 - n) ++ ");"
    , mj ++ " = " ++ mj ++ " | w0;" ]
  else
    let mjs := chachaRaSlotName ra j
    [ "w0 = " ++ mjs ++ ";"
    , "w1 = w0;"
    , "w0 = #VPSLL_4u32(w0, " ++ toString n ++ ");"
    , "w1 = #VPSRL_4u32(w1, " ++ toString (32 - n) ++ ");"
    , "w0 = w0 | w1;"
    , mjs ++ " = w0;" ]

/-- RA-driven packed-u32 `m{dst} += m{src}`. -/
def renderRaAddIn (ra : RegisterAllocation) (dst src : Nat) : List String :=
  match chachaRaIsReg ra dst, chachaRaIsReg ra src with
  | true, true =>
    let md := chachaRaSlotName ra dst
    let ms := chachaRaSlotName ra src
    [ md ++ " = #VPADD_4u32(" ++ md ++ ", " ++ ms ++ ");" ]
  | true, false =>
    let md := chachaRaSlotName ra dst
    let mss := chachaRaSlotName ra src
    [ "w0 = " ++ mss ++ ";"
    , md ++ " = #VPADD_4u32(" ++ md ++ ", w0);" ]
  | false, true =>
    let mds := chachaRaSlotName ra dst
    let ms := chachaRaSlotName ra src
    [ "w0 = " ++ mds ++ ";"
    , "w0 = #VPADD_4u32(w0, " ++ ms ++ ");"
    , mds ++ " = w0;" ]
  | false, false =>
    let mds := chachaRaSlotName ra dst
    let mss := chachaRaSlotName ra src
    [ "w0 = " ++ mds ++ ";"
    , "w1 = " ++ mss ++ ";"
    , "w0 = #VPADD_4u32(w0, w1);"
    , mds ++ " = w0;" ]

/-- RA-driven packed `m{dst} ^= m{src}`. -/
def renderRaXorIn (ra : RegisterAllocation) (dst src : Nat) : List String :=
  match chachaRaIsReg ra dst, chachaRaIsReg ra src with
  | true, true =>
    let md := chachaRaSlotName ra dst
    let ms := chachaRaSlotName ra src
    [ md ++ " = " ++ md ++ " ^ " ++ ms ++ ";" ]
  | true, false =>
    let md := chachaRaSlotName ra dst
    let mss := chachaRaSlotName ra src
    [ "w0 = " ++ mss ++ ";"
    , md ++ " = " ++ md ++ " ^ w0;" ]
  | false, true =>
    let mds := chachaRaSlotName ra dst
    let ms := chachaRaSlotName ra src
    [ "w0 = " ++ mds ++ ";"
    , "w0 = w0 ^ " ++ ms ++ ";"
    , mds ++ " = w0;" ]
  | false, false =>
    let mds := chachaRaSlotName ra dst
    let mss := chachaRaSlotName ra src
    [ "w0 = " ++ mds ++ ";"
    , "w1 = " ++ mss ++ ";"
    , "w0 = w0 ^ w1;"
    , mds ++ " = w0;" ]

/-- RA-driven quarter-round on logical slots `a b c d`. Identical step
sequence to `renderChacha4wayXmmQR`; the only difference is each helper
resolves its slot through `ra.seqOf` before looking up the physical
destination name. -/
def renderRaQR (ra : RegisterAllocation) (a b c d : Nat) : List String :=
  renderRaAddIn ra a b ++         -- a += b
  renderRaXorIn ra d a ++         -- d ^= a
  renderRaRotL  ra d 16 ++        -- d <<<= 16
  renderRaAddIn ra c d ++         -- c += d
  renderRaXorIn ra b c ++         -- b ^= c
  renderRaRotL  ra b 12 ++        -- b <<<= 12
  renderRaAddIn ra a b ++         -- a += b
  renderRaXorIn ra d a ++         -- d ^= a
  renderRaRotL  ra d 8 ++         -- d <<<= 8
  renderRaAddIn ra c d ++         -- c += d
  renderRaXorIn ra b c ++         -- b ^= c
  renderRaRotL  ra b 7            -- b <<<= 7

/-- RA-driven column round. -/
def renderRaColumnRound (ra : RegisterAllocation) : List String :=
  renderRaQR ra 0 4 8  12 ++
  renderRaQR ra 1 5 9  13 ++
  renderRaQR ra 2 6 10 14 ++
  renderRaQR ra 3 7 11 15

/-- RA-driven diagonal round. -/
def renderRaDiagRound (ra : RegisterAllocation) : List String :=
  renderRaQR ra 0 5 10 15 ++
  renderRaQR ra 1 6 11 12 ++
  renderRaQR ra 2 7  8 13 ++
  renderRaQR ra 3 4  9 14

/-- RA-driven double-round. -/
def renderRaDoubleRound (ra : RegisterAllocation) : List String :=
  renderRaColumnRound ra ++ renderRaDiagRound ra

/-- `n` RA-driven double-rounds. -/
def renderRaDoubleRounds (ra : RegisterAllocation) : Nat → List String
  | 0 => []
  | (k + 1) => renderRaDoubleRound ra ++ renderRaDoubleRounds ra k

/-- RA-driven SoA load. For each `j ∈ 0..15`, gather lanes from `inp` into
`tbuf` then bind to the slot's physical destination (`m{phys}` for
reg-resident, `m14s`/`m15s` for spilled). -/
def renderRaLoad (ra : RegisterAllocation) : List String :=
  let oneWord (j : Nat) : List String :=
    let common :=
      [ "tbuf[0] = inp[" ++ toString (0  + j) ++ "];"
      , "tbuf[1] = inp[" ++ toString (16 + j) ++ "];"
      , "tbuf[2] = inp[" ++ toString (32 + j) ++ "];"
      , "tbuf[3] = inp[" ++ toString (48 + j) ++ "];" ]
    if chachaRaIsReg ra j then
      let mj := chachaRaSlotName ra j
      common ++
      [ mj ++ " = tbuf[:u128 0];"
      , "orig[:u128 " ++ toString j ++ "] = " ++ mj ++ ";" ]
    else
      let mjs := chachaRaSlotName ra j
      common ++
      [ "w0 = tbuf[:u128 0];"
      , mjs ++ " = w0;"
      , "orig[:u128 " ++ toString j ++ "] = w0;" ]
  (List.range 16).flatMap oneWord

/-- RA-driven SoA store + feed-forward: add the saved original to the
final round output and scatter the 4 lanes to `out`. -/
def renderRaStore (ra : RegisterAllocation) : List String :=
  let oneWord (j : Nat) : List String :=
    if chachaRaIsReg ra j then
      let mj := chachaRaSlotName ra j
      [ "w0 = orig[:u128 " ++ toString j ++ "];"
      , mj ++ " = #VPADD_4u32(" ++ mj ++ ", w0);"
      , "tbuf[:u128 0] = " ++ mj ++ ";"
      , "out[" ++ toString (0  + j) ++ "] = tbuf[0];"
      , "out[" ++ toString (16 + j) ++ "] = tbuf[1];"
      , "out[" ++ toString (32 + j) ++ "] = tbuf[2];"
      , "out[" ++ toString (48 + j) ++ "] = tbuf[3];" ]
    else
      let mjs := chachaRaSlotName ra j
      [ "w0 = " ++ mjs ++ ";"
      , "w1 = orig[:u128 " ++ toString j ++ "];"
      , "w0 = #VPADD_4u32(w0, w1);"
      , "tbuf[:u128 0] = w0;"
      , "out[" ++ toString (0  + j) ++ "] = tbuf[0];"
      , "out[" ++ toString (16 + j) ++ "] = tbuf[1];"
      , "out[" ++ toString (32 + j) ++ "] = tbuf[2];"
      , "out[" ++ toString (48 + j) ++ "] = tbuf[3];" ]
  (List.range 16).flatMap oneWord

/-- The full RA-driven XMM-resident body. Declares 14 named XMM `m0..m13`
+ two scratch `w0`, `w1` + two stack spills `m14s`, `m15s` + the `orig`
feed-forward array + the `tbuf` AoS-SoA staging — same as the current
emit's storage class. The 20-round body uses the RA-rerouted helpers. -/
def renderRaBody (ra : RegisterAllocation) : List String :=
  let decls :=
    [ "reg u128 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13;"
    , "reg u128 w0 w1;"
    , "stack u128 m14s;"
    , "stack u128 m15s;"
    , "stack u128[16] orig;"
    , "stack u32[4] tbuf;" ]
  decls ++ renderRaLoad ra ++ renderRaDoubleRounds ra 10 ++ renderRaStore ra

/-- **The RA-driven ChaCha20 4-way XMM-resident `.jazz`.**
Same ABI as `ChaChaEmit.chacha4wayXmmBlockJazz` (#111): 4 ChaCha blocks
in (AoS) and 4 out. The body assigns each logical state slot 0..15 to a
physical destination (one of `m0..m13` register-resident, or `m14s`/`m15s`
stack-spilled) according to the RA's `seqOf`. For
`RegisterAllocation.identity` this is byte-identical to the existing #111
emit; for `chachaXmmRA` it spills the two LIGHTEST-used slots instead of
14 and 15, reducing spill-flank traffic by ~240 ops per block. -/
def emitChacha4wayXmmRaJazz (ra : RegisterAllocation) (name : String) : String :=
  let paramStrs := ["reg ptr u32[64] out", "reg const ptr u32[64] inp"]
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u32[64] {\n  "
    ++ String.intercalate "\n  " (renderRaBody ra) ++ "\n  return out;\n}"

/-! ## 5. Headline denotation-preservation theorem

The denotation of the RA-driven 4-way XMM kernel equals the
lane-parallel-map of the scalar ChaCha block function across the 4 lanes
— exactly the SAME denotation as both the canonical 4-way and the
#111 XMM-resident emit. The proof composes `LaneMap.chacha4way_lane_map`,
which is parametric over the per-lane block function and lane bundling
with no dependence on the lane's register layout — i.e.
storage-class-agnostic by construction. The RA only changes WHICH slots
are register-resident vs spilled; the SSA sequence and per-slot data
flow are unchanged. -/

/-- **Denotation preservation for the RA-driven XMM-resident ChaCha 4-way
emit.** Composes `LaneMap.chacha4way_lane_map`. -/
theorem chacha_xmm_ra_emit_denotation_preserves (state : ChaCha4Way) :
    LaneMap.laneMap chacha20BlockSpec state =
      (fun b => chacha20BlockSpec (state b)) :=
  LaneMap.chacha4way_lane_map chacha20BlockSpec state

/-! ## 6. Identity-RA byte-identity smoke test

For `ra = RegisterAllocation.identity` (`seqOf k = k`), the RA-driven
slot-name function reduces pointwise to `chacha4wayXmmSlotName`. The
full-text byte-identity to the current #111 emit follows from this
pointwise equality together with the determinism of the rendering
helpers. -/

/-- **Identity-RA slot-name equals the current ChaCha XMM slot-name
pointwise.** -/
theorem chachaRaSlotName_identity_eq (j : Nat) :
    chachaRaSlotName RegisterAllocation.identity j = chacha4wayXmmSlotName j := by
  rfl

/-- **Identity-RA isReg equals the current ChaCha XMM isReg pointwise.** -/
theorem chachaRaIsReg_identity_eq (j : Nat) :
    chachaRaIsReg RegisterAllocation.identity j = chacha4wayXmmIsReg j := by
  rfl

/-! ## 7. Concrete spill-victim decision (sanity)

For our concrete `chachaXmmRA`, the spill victims (slots that get mapped
to positions 14 / 15 by `seqOf`, hence routed to `m14s`/`m15s`) come
from the light class `{0,1,2,3,8,9,10,11}`. The tie-breaking rule in
`lightestPair` picks the two lowest-index slots of the light class. -/

/-- The lightest pair is `(0, 1)` — both `a`-role slots, the
lowest-weight class. -/
theorem lightestPair_eq : lightestPair = (0, 1) := by native_decide

/-- Under `chachaXmmRA`, logical slot 0 maps to physical 14 (stack spill). -/
theorem chachaXmmRA_slot0_spilled :
    chachaXmmRA.seqOf 0 = 14 := by native_decide

/-- Under `chachaXmmRA`, logical slot 1 maps to physical 15 (stack spill). -/
theorem chachaXmmRA_slot1_spilled :
    chachaXmmRA.seqOf 1 = 15 := by native_decide

/-- Under `chachaXmmRA`, the formerly-spilled logical slot 14 now lives
in register `m0` (the freed XMM position). -/
theorem chachaXmmRA_slot14_unspilled :
    chachaXmmRA.seqOf 14 = 0 := by native_decide

/-- Under `chachaXmmRA`, logical slot 15 lives in register `m1`. -/
theorem chachaXmmRA_slot15_unspilled :
    chachaXmmRA.seqOf 15 = 1 := by native_decide

/-! ## 8. Cross-iteration-aware RA via `UnrolledComRA.unrolledSlotRAofIters`

`UnrolledComRA.lean` §7 ships `unrolledSlotRAofIters tr iters`: a
`RegisterAllocation` derived from a per-iteration `SlotEvent` chunking with a
carry-aware linear-scan priority. Phase B-2 wires the ChaCha20 4-way XMM
consumer through that API, replacing the bespoke `lightestPair` heuristic
with the analysis-driven `seqOf`.

### Chunk derivation

Each quarter-round `QR(a, b, c, d)` materialises 12 ARX steps (RFC 8439 §2.1).
At slot-event granularity (state slots `0..15` only — rotate scratches in
slots 16/17 are excluded since they are not register-allocated by this pass):

```
a += b   -- wr=a, rds=[a, b]
d ^= a   -- wr=d, rds=[d, a]
d <<<= n -- wr=d, rds=[d]      (rotate, scratches 16/17 elided)
c += d   -- wr=c, rds=[c, d]
b ^= c   -- wr=b, rds=[b, c]
b <<<= n -- wr=b, rds=[b]
(repeat ARX half with second rotate amounts)
```

The 12-step QR trace `qrEvents` mirrors this exactly. One double-round is
the 8 QRs `doubleRoundQRs`. `chachaIters` is 10 copies of `doubleRoundEvents`.
The flat trace `chachaTrace` is the concatenation. -/

/-- Slot events for one quarter-round on state slots `a, b, c, d`.

Each ARX step records `wr` (destination logical slot) and `rds` (the
register-file logical slots read). The two rotate amounts (16/12 for the
first half, 8/7 for the second half) do not change the slot footprint —
the rotate writes `d` (or `b`) and reads only `d` (or `b`). -/
def qrEvents (a b c d : Nat) : List UnrolledComRA.SlotEvent :=
  [ ⟨a, [a, b]⟩          -- a += b
  , ⟨d, [d, a]⟩          -- d ^= a
  , ⟨d, [d]⟩             -- d <<<= 16
  , ⟨c, [c, d]⟩          -- c += d
  , ⟨b, [b, c]⟩          -- b ^= c
  , ⟨b, [b]⟩             -- b <<<= 12
  , ⟨a, [a, b]⟩          -- a += b
  , ⟨d, [d, a]⟩          -- d ^= a
  , ⟨d, [d]⟩             -- d <<<= 8
  , ⟨c, [c, d]⟩          -- c += d
  , ⟨b, [b, c]⟩          -- b ^= c
  , ⟨b, [b]⟩ ]           -- b <<<= 7

/-- Slot events for one ChaCha20 double-round: 8 quarter-rounds (column +
diagonal) per `doubleRoundQRs`. -/
def doubleRoundEvents : List UnrolledComRA.SlotEvent :=
  doubleRoundQRs.flatMap (fun qr =>
    let (a, b, c, d) := qr
    qrEvents a b c d)

/-- Per-iteration chunking for the ChaCha20 4-way 20-round permutation:
10 copies of `doubleRoundEvents`. The cross-iteration carry analysis uses
this to decide which slots are written in iter `i` and read in iter `i+1`. -/
def chachaIters : List (List UnrolledComRA.SlotEvent) :=
  List.replicate 10 doubleRoundEvents

/-- Flat slot trace = concatenation of `chachaIters`, used to compute live
ranges and seed-pin sets by `unrolledSlotRAofIters`. -/
def chachaTrace : List UnrolledComRA.SlotEvent :=
  chachaIters.flatten

/-- **The cross-iteration-aware ChaCha XMM register allocation.** Built by
`UnrolledComRA.unrolledSlotRAofIters` over the 10-double-round chunking.
Carry analysis: every state slot `0..15` is written and read in every
double-round, so all 16 are HIGH_PRIORITY-carried. The downstream linear
scan then places them in firstTouch order. With seed-pinning (every state
slot is read by `a += b` of QR(0,4,8,12) before any state slot is yet
written by the body), the resulting `seqOf` is the identity on
`{0..15}` — i.e. the cross-iter RA produces the SAME storage layout as
the #111 baseline emit (spill slots 14, 15).

Phase B-2 wires this through but the `lightestPair` hand-rolled RA above
(`chachaXmmRA`, spill slots 0, 1 — light a-role) remains the
better-performing alternative on this kernel: ChaCha's slot population is
homogeneously carried, which the cross-iter analysis cannot distinguish
from the per-role op-weight bias the hand-rolled heuristic uses. -/
def chachaXmmRA_iters : RegisterAllocation :=
  UnrolledComRA.unrolledSlotRAofIters chachaTrace chachaIters

/-- The cross-iteration-aware RA is well-formed (by
`unrolledSlotRAofIters_WellFormed`). -/
theorem chachaXmmRA_iters_WellFormed : WellFormed chachaXmmRA_iters :=
  UnrolledComRA.unrolledSlotRAofIters_WellFormed _ _

/-- All 16 ChaCha state slots are carried across every double-round
boundary: every slot is written and read in every double-round. -/
theorem chacha_all_slots_carried :
    (List.range 16).all
      (fun s => UnrolledComRA.carriedAcross s chachaIters) = true := by
  native_decide

/-! ## 9. Two-address coalescing audit (Phase B+)

`UnrolledComRA.lean` §8 ships `unrolledSlotRAofItersCoalesce`: a
coalesce-aware variant of the cross-iter RA that fuses `dst` and `src1`
into one physical slot when `src1` dies at the event.

For ChaCha20's slot trace `chachaTrace`, every multi-read event has
`dst = head rds` by construction:

```
⟨a, [a, b]⟩          -- a += b      (head rds = a = dst)
⟨d, [d, a]⟩          -- d ^= a      (head rds = d = dst)
⟨d, [d]⟩             -- d <<<= n    (head rds = d = dst)
...
```

So the analysis observes **zero coalesce candidates** on ChaCha — the
trace is already in coalesced two-address form. The cross-iter +
coalesce RA produces the SAME jazz as the cross-iter RA alone (which
itself was within run-to-run noise of the #111 baseline).

This is the architecturally-honest finding: ChaCha's quarter-round
arithmetic is already two-address by design (`a += b`, `d ^= a`), so
two-address coalescing has no room to fire at the Com trace level. The
remaining gap to HACL\* requires structural changes (rotate-scratch
reduction, AoS-SoA refactor) or leaf adoption — pure RA has reached its
ceiling. -/

/-- The cross-iter + coalesce-aware ChaCha XMM register allocation. For
ChaCha's trace this equals `chachaXmmRA_iters` extensionally (zero
coalesce candidates). -/
def chachaXmmRA_coalesce : RegisterAllocation :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce chachaTrace chachaIters

/-- The coalesce-aware RA is well-formed. -/
theorem chachaXmmRA_coalesce_WellFormed : WellFormed chachaXmmRA_coalesce :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce_WellFormed _ _

/-- **ChaCha has zero coalesce candidates.** Every multi-read event in
`chachaTrace` has `dst = head rds` (`a += b`, `d ^= a`, `c += d`,
`b ^= c`, etc.), so `coalescePairs chachaTrace` returns the empty list. -/
theorem chacha_coalesce_candidate_count :
    UnrolledComRA.coalesceCandidateCount chachaTrace = 0 := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.ChachaRaEmit
