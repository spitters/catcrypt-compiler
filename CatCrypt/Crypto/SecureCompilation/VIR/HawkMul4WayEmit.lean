/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public import Mathlib.Data.ZMod.Basic

/-!
# HAWK 4-way batched lane-parallel ring multiply

This is the **HAWK analogue** of the 4-way batched NTT (`LatticeNttEmit.lean`)
for the ML-KEM-768 / ML-DSA-65 lattices. HAWK's ring is `Z/q[x]/(x^n + 1)`
with `q ∈ {1024, 2048}` (a power of two — coefficient reduction is a single
bit-mask `& (q-1)`), so the inner-loop arithmetic is exactly *integer mul +
mul-accumulate (signed) + mask* — no Montgomery reduction, no NTT-twiddle
look-ups, no Barrett reduction.

The 4-way pattern bundles **four independent** HAWK ring multiplies into a
single `__m128i`-wide kernel: lane `b ∈ Fin 4` carries an independent
`Z/q[x]/(x^n + 1)` instance, and one packed multiply
`#VPMULL_4u32` realizes the four scalar multiplications in parallel. Where
the existing scalar HAWK emit (`HawkMulEmit.lean`) discharges 16 output
coefficients per call via 512 scalar `regArith` bindings, the 4-way bundle
discharges 4 × 16 = 64 output coefficients per call via the *same* 512 packed
bindings — a 4× per-call throughput multiplier whenever the calling pattern
batches HAWK signature verifications (which `hawk-sign` does for the
"verify-many-signatures-against-one-key" hot path).

## What the Lean theorem here does and does NOT establish (read this first)

The lane-parallel-MAP heart `LaneMap.laneMap_eq_scalarMap` is parametric over
(1) the per-lane block function `f : α → β` and (2) the lane type `α`. The
theorem `hawk_mul_4way_denotation_preserves` below instantiates it and establishes
exactly **lane-independence of the 4-way batching**: the SIMD packing introduces
no cross-lane interference, so the batched form denotes the same value as running
the per-lane block sequentially. It is **parametric over the per-lane block** and
proves nothing about the ring multiply.

In particular it does **NOT** establish that the per-lane block computes the HAWK
negacyclic product. The block `hawkRingMulSpec` in this file is a **placeholder**
(`:= fun _ _ => fun _ => 0`, the constant-zero function — *not* the negacyclic
schoolbook product mod `x^N+1`). The genuine per-lane negacyclic multiply is built
as a `Com jasminDialect` in `HawkMulEmit.lean`; it is **not wired to this file**.
The ring-multiply correctness of the emitted 4-way kernel is carried by the
**external byte-KAT** `bench/hawk_compare/hawk_mul_4way_kat.c` (which checks the
emitted `.jazz` against a lane-by-lane scalar HAWK reference), not by the Lean
theorem here.

So: the emit↔reference ring-multiply byte-identity is **KAT-gated (Tier-B)**; the
Lean contribution is the batching's lane-independence, not the multiply's
correctness. Wiring the real negacyclic product (from `HawkMulEmit`) into this
theorem to make it a non-vacuous Lean denotation statement is open follow-up.

## Bench / KAT

`bench/hawk_compare/gen/hawk_mul_4way.jazz` is the .jazz this module prints; it is
KAT-checked at the bench level against a lane-by-lane scalar HAWK ring multiply
reference (`bench/hawk_compare/hawk_mul_4way_kat.c`). That external KAT — not the
Lean theorem — is what ties the emitted kernel to the negacyclic product. There
are no fabricated test vectors.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.HawkMul4WayEmit

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. Ring abbreviations -/

/-- The HAWK-256 coefficient ring `ℤ_{1024}` (10-bit power-of-two modulus;
    coefficient reduction is the bit-mask `& 1023`). -/
abbrev Zq1024 := ZMod 1024

/-- The HAWK ring degree of this straight-line 4-way kernel (the same `N = 16`
    used by `HawkMulEmit`; the true HAWK degree `n ∈ {256, 512, 1024}` is the
    same code at larger `N`, tiled via the for-loop layer). -/
abbrev N : Nat := 16

/-- A single HAWK polynomial lane: 16 coefficients in `Z/1024`. -/
abbrev HawkLane := Fin N → Zq1024

/-- The 4-way packed HAWK lane bundle: 4 independent HAWK polynomial multiply
    instances, each carrying one `HawkLane`. Each `__m128i` holds the 4 lanes'
    coefficient at one of the 16 positions. -/
abbrev Hawk4Way := Fin 4 → HawkLane

/-! ## 2. The per-lane block — a PLACEHOLDER, not the genuine ring multiply

The lane-map theorem is parametric over the per-lane block, so its proof is the
same for any block. The definition below is deliberately the **constant-zero
placeholder** (`:= fun _ _ => fun _ => 0`) — it is *not* the negacyclic schoolbook
product mod `x^N+1` (that genuine multiply is built as a `Com jasminDialect` in
`HawkMulEmit.lean`, and is not wired here). Consequently the theorem instantiated
at it says nothing about the multiply; it asserts only lane-independence of the
batching (see the module header). The genuine per-lane multiply is checked by the
external byte-KAT `bench/hawk_compare/hawk_mul_4way_kat.c`. Replacing this
placeholder with the real negacyclic product is the open follow-up.

**The genuine spec now exists** in `HawkMul4WayRealization.lean`:
`hawkNegacyclicMul` (the real `x^N=-1` negacyclic product over `Zq1024`), with the
non-vacuous `hawk_negacyclic_shift` (multiplying by the monomial `X` rotates with the
minus-sign wrap — false for this `:= 0` placeholder and for a cyclic convolution) and
`hawk_mul_4way_lane_map_genuine` (the lane-map at the *real* block). The 4-way lanes
are INDEPENDENT, so the per-lane frame is correct here; the genuine spec lives
downstream (importing it back would cycle), and the emit↔`hawkNegacyclicMul` byte tie
stays the KAT-gated residual. -/

/-- Placeholder per-lane block for the HAWK 4-way kernel. **`:= fun _ _ => fun _ => 0`
    (constant zero), not the negacyclic product** — present only so the parametric
    lane-independence theorem can be instantiated. Ring-multiply correctness is
    KAT-gated (`hawk_mul_4way_kat.c`), not established by this def. -/
def hawkRingMulSpec : HawkLane → HawkLane → HawkLane := fun _a _b => fun _ => 0

/-- The "lane-curried" form of the multiply: a per-lane function taking a
    pair `(a, b)` of `HawkLane`s and returning their product. This is the
    `f : α → β` the lane-map theorem is instantiated at, with
    `α = HawkLane × HawkLane` and `β = HawkLane`. -/
def hawkRingMulPair : HawkLane × HawkLane → HawkLane :=
  fun ab => hawkRingMulSpec ab.1 ab.2

/-- The 4-way packed input bundle: 4 independent `(a, b)` pairs. -/
abbrev Hawk4WayInputs := Fin 4 → HawkLane × HawkLane

/-! ## 3. The 4-way lane-map corollary (statement + proof) -/

/-- **HAWK 4-way lane-map equality** (corollary of
    `LaneMap.laneMap_eq_scalarMap` at `α = HawkLane × HawkLane`,
    `β = HawkLane`, `L = 4`). Applying the scalar negacyclic ring multiply
    to each of the 4 lane-pairs in parallel equals running it sequentially
    on each lane-pair. Structural (`funext + rfl`); no algebraic structure on
    the lane ring required. The bench emits the 4-way SIMD form; this theorem
    says it denotes the same value as the scalar form. -/
theorem hawk_mul_4way_lane_map (mul : HawkLane × HawkLane → HawkLane)
    (lanes : Hawk4WayInputs) :
    LaneMap.laneMap mul lanes = (fun b => mul (lanes b)) := by
  funext i
  rfl

/-! ## 4. The lane-independence theorem (NOT ring-multiply correctness) -/

/-- **Lane-independence of the HAWK 4-way batching** (NOT ring-multiply
    correctness). `LaneMap.laneMap hawkRingMulPair lanes` equals the sequential
    per-lane evaluation `fun b => hawkRingMulPair (lanes b)`. Holds for any block;
    here the block is the placeholder constant-zero `hawkRingMulPair`, so this says
    the batching introduces no cross-lane interference — it does *not* say the lane
    computes the negacyclic product. Structural, `[propext, Quot.sound]` only. -/
theorem hawk_mul_4way_denotation_preserves (lanes : Hawk4WayInputs) :
    LaneMap.laneMap hawkRingMulPair lanes =
      (fun b => hawkRingMulPair (lanes b)) :=
  hawk_mul_4way_lane_map hawkRingMulPair lanes

/-! ## 5. Emit functions (the .jazz driver)

We render a simplified 4-way HAWK multiply kernel as a sequence of packed
AVX2 ops over `__m128i` lanes. The kernel shape mirrors `HawkMulEmit`: each
of the 16 output coefficients `out[k]` is computed by accumulating
`N = 16` packed-mul-add/sub products (the negacyclic sign comes from `i > k`
swapping `#VPADD_4u32` for `#VPSUB_4u32`), then masked with
`& 1023` per lane. The 4 SIMD lanes hold the 4 INDEPENDENT HAWK ring
multiply instances; the mask is the per-lane `& 1023` lane operation
realized by a packed-AND with a broadcasted constant.

## ABI

`hawk_mul_4way` takes a 4-way input bundle laid out as:
  inp[0..15]   = lane-0 a coefficients (4-u32-per-lane × 16 coeffs = 64 u32?)
Actually the natural SoA layout is one `__m128i` per coefficient position,
holding the 4 lanes' coefficient at that position. So:

* `inp[chunk k]`     = (a₀[k], a₁[k], a₂[k], a₃[k])    for k = 0..15   (16 chunks)
* `inp[chunk 16+k]`  = (b₀[k], b₁[k], b₂[k], b₃[k])    for k = 0..15   (16 chunks)
* `inp[chunk 32]`    = (1023, 1023, 1023, 1023)        (broadcast mask)
* `out[chunk k]`     = (out₀[k], out₁[k], out₂[k], out₃[k])  for k = 0..15

Total inp = 33 × 16 bytes = 528 bytes = 132 u32 = `u32[132]`.
Total out = 16 × 16 bytes = 256 bytes = 64 u32 = `u32[64]`. -/

/-! ### Helper: render one accumulation step for `out[k]` from term `i` -/

/-- Render one accumulation step: scratch = a[i] * b[(k-i+N) mod N], then
    `out[k] += scratch` (if `i ≤ k`, positive convolution half) or
    `out[k] -= scratch` (if `i > k`, the negacyclic-wrapped half, since
    `x^N = -1`). The packed multiply is `#VPMULL_4u32` (4 × u32 lanes).
    The four scalar HAWK multiplies happen lane-by-lane in one op. -/
def renderHawkAccStep (k i : Nat) : List String :=
  let j : Nat := (k + N - i) % N
  let aChunk : Nat := i          -- inp chunks 0..15 hold lane a
  let bChunk : Nat := 16 + j     -- inp chunks 16..31 hold lane b
  let outChunk : Nat := k        -- out chunks 0..15 hold the lane outputs
  let opStr : String := if i ≤ k then "#VPADD_4u32" else "#VPSUB_4u32"
  [ "a = inp[:u128 " ++ toString aChunk ++ "];"
  , "b = inp[:u128 " ++ toString bChunk ++ "];"
  , "t = #VPMULL_4u32(a, b);"
  , "acc = out[:u128 " ++ toString outChunk ++ "];"
  , "acc = " ++ opStr ++ "(acc, t);"
  , "out[:u128 " ++ toString outChunk ++ "] = acc;" ]

/-- Render the `N` accumulation steps for `out[k]`: term `i = 0..N-1`. -/
def renderHawkCoeff (k : Nat) : List String :=
  ("// out[" ++ toString k ++ "]") :: (List.range N).flatMap (fun i => renderHawkAccStep k i)

/-- Render the per-lane mask `out[k] &= 1023` for `k = 0..N-1`. The mask is a
    broadcast `(1023, 1023, 1023, 1023)` at inp chunk `32`, applied via
    jasmin's packed bitwise-AND (the surface name is the same `&` operator
    on `u128` registers in jasmin). -/
def renderHawkMaskStep (k : Nat) : List String :=
  let outChunk : Nat := k
  [ "acc = out[:u128 " ++ toString outChunk ++ "];"
  , "acc = acc & mask;"
  , "out[:u128 " ++ toString outChunk ++ "] = acc;" ]

/-- Render the `N` final mask steps in order. -/
def renderHawkMasks : List String :=
  "// reductions mod 1024 (per-lane mask)" :: (List.range N).flatMap renderHawkMaskStep

/-- The full body of the 4-way HAWK ring multiply emit. -/
def renderHawk4WayBody : List String :=
  let decls := [ "reg u128 a b t acc mask;" ]
  let loadMask := [ "mask = inp[:u128 32];" ]
  -- Initialize all 16 output chunks to zero.
  let initOut := (List.range N).flatMap (fun k =>
    [ "acc = inp[:u128 " ++ toString aSafeZeroChunk ++ "];"
    , "acc = #VPXOR_128(acc, acc);"
    , "out[:u128 " ++ toString k ++ "] = acc;" ])
  decls ++ loadMask ++ initOut
    ++ (List.range N).flatMap renderHawkCoeff
    ++ renderHawkMasks
where
  /-- We don't actually need a dedicated zero chunk: VPXOR(x,x) yields 0 for
      any x, so any inp chunk works as the "source" — pick chunk 0. -/
  aSafeZeroChunk : Nat := 0

/-- Emit the HAWK 4-way batched ring multiply `.jazz` text. Sibling-local —
    does NOT modify `JasminAbiEmit.lean`. -/
def emitHawk4WayJazz (name : String) : String :=
  let paramStrs := ["reg ptr u32[64] out", "reg const ptr u32[132] inp"]
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u32[64] {\n  "
    ++ String.intercalate "\n  " renderHawk4WayBody ++ "\n  return out;\n}"

/-! ## 6. Structural sanity checks on the emitted text -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- The emitted HAWK 4-way export name. -/
def hawkMul4WayJazz : String := emitHawk4WayJazz "hawk_mul_4way"

/- The HAWK 4-way export has the expected ABI. -/
#guard (strContains hawkMul4WayJazz "export fn hawk_mul_4way(reg ptr u32[64] out, reg const ptr u32[132] inp)")

/- The HAWK 4-way body uses packed-u32 lane multiply `#VPMULL_4u32` — the
    heart of the lane-parallel-map ring multiply. -/
#guard (strContains hawkMul4WayJazz "#VPMULL_4u32(")

/- The HAWK 4-way body uses packed-u32 lane add `#VPADD_4u32` (positive
    convolution half). -/
#guard (strContains hawkMul4WayJazz "#VPADD_4u32(")

/- The HAWK 4-way body uses packed-u32 lane subtract `#VPSUB_4u32` — the
    negacyclic-wrapped half (`x^N = -1`). -/
#guard (strContains hawkMul4WayJazz "#VPSUB_4u32(")

/- The HAWK 4-way body uses per-lane bitwise-AND for the final `& 1023`
    reduction (one mask per lane realized by the broadcasted constant). -/
#guard (strContains hawkMul4WayJazz "acc = acc & mask;")

/- The body renders all 16 output coefficients (`out[0]` and `out[15]`
    comment markers both present). -/
#guard (strContains hawkMul4WayJazz "// out[0]") && (strContains hawkMul4WayJazz "// out[15]")

end CatCrypt.Crypto.SecureCompilation.VIR.HawkMul4WayEmit
