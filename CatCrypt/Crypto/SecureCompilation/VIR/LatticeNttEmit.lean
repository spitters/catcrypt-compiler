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
# Lattice 4-way batched NTT — ML-KEM-768 and ML-DSA-65

This module instantiates the lane-parallel-map theorem
(`LaneMap.laneMap_eq_scalarMap` / `LaneMap.vmap_eq_scalarMap`) at two lattice
NTT rings:

* `Z_3329`  — ML-KEM-768's polynomial ring `ℤ_{3329}[X]/(X^256+1)`
  (12-bit coefficient; 8 lanes fit in a `__m128i`, 4 lanes fit in a `__m64`);
* `Z_8380417` — ML-DSA-65's polynomial ring `ℤ_{8380417}[X]/(X^256+1)`
  (23-bit coefficient; 4 lanes fit in a `__m128i` as `u32`).

Both NTTs are 256-coefficient, decomposable as a 4-way lane-parallel butterfly:
each Cooley–Tukey butterfly stage is 128 independent `(a, b, ω) ↦ (a + ω·b,
a − ω·b)` operations, naturally bundled in groups of 4 to run on a `__m128i`
of 4 lanes (32-bit per lane for ML-DSA; 16-bit per lane for ML-KEM, where
8-way is also possible but 4-way matches the lane-map shape exposed by
`LaneMap.lean`).

## What the Lean theorems here establish

`laneMap_eq_scalarMap` is parametric over the per-lane function `f : α → β` and
the lane type `α`: applying `f` to each of `L` lanes of a packed vector equals
running `f` on each lane (`funext + rfl`).

`mlkem_ntt_4way_lane_map` / `mldsa_ntt_4way_lane_map` state this at the two lane
types for any block. `mlkem_ntt_4way_denotation_preserves` /
`mldsa_ntt_4way_denotation_preserves` state it at `mlkemNttButterflySpec` /
`mldsaNttButterflySpec`, which are defined as the identity function (`:= id`),
not as the Cooley–Tukey stage `(a,b,ω) ↦ (a+ω·b, a−ω·b)` (`ctButterfly` in
`Optimizer/Lattice/NTTButterflyPass.lean`). These theorems hold for any block and
say nothing about the NTT or about the emitted text.

No theorem in this module relates the rendered `.jazz` kernels to an NTT, to
`ctButterfly`, or to `PQCLEAN_MLKEM768_CLEAN_ntt`. Value checks of the emitted
kernels against PQClean are external to Lean and not part of this package.

## Emit (the .jazz driver shape)

The emit functions render the 4-way batched butterfly as a sequence of packed
AVX2 ops:

* ML-DSA-65 (32-bit lanes): `#VPADDD` / `#VPSUBD` / `#VPMULLD` over `__m128i`
  holding 4 `u32` lanes;
* ML-KEM-768 (16-bit lanes, 4-way of 8 possible): `#VPADDW` / `#VPSUBW` /
  `#VPMULLW` over `__m128i` holding 8 `u16` lanes, restricted to the lower 4
  for the 4-way shape.

The emit functions are local helpers (not additions to `JasminAbiEmit.lean`)
that produce `.jazz` text; no theorem gives that text a semantics.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. Ring abbreviations -/

/-- The ML-KEM-768 coefficient ring `ℤ_{3329}` (12-bit prime, `q ≡ 1 mod 256`). -/
abbrev Zq3329 := ZMod 3329

/-- The ML-DSA-65 coefficient ring `ℤ_{8380417}` (23-bit prime, `q ≡ 1 mod 512`,
    NTT-friendly per FIPS 204). -/
abbrev Zq8380417 := ZMod 8380417

/-! ## 2. Lane-map shape for the 4-way batched butterfly

A single Cooley–Tukey butterfly is the 2→2 map `(a, b, ω) ↦ (a + ω·b, a − ω·b)`
over the coefficient ring. One stage of the 256-coefficient NTT runs 128 of
these in parallel; we bundle them in groups of 4 to fit a `__m128i` (4 × 32-bit
for ML-DSA, or the lower 4 of an `__m128i` × 16-bit for ML-KEM).

The "per-lane state" `α` is one lane's contribution to the batched butterfly:
the 64 pairs the lane processes through one full sweep of one stage (128 pairs
per stage / 4 lanes per batch / two values per pair = 64 lane-pairs per stage,
times 4 lanes per batch = the 256 coefficients of the NTT).

The lane-map theorem holds for any per-lane block function `f : α → β`, so it
uses no butterfly content: each ring carries an abstract
`block : LaneState → LaneState` at which `laneMap_eq_scalarMap` is instantiated. -/

/-- The per-lane state of one batch of the ML-KEM-768 4-way NTT: 64 ring
    elements (the 64 lane-pairs the lane will sweep). Same shape as
    `ChaChaState`, lane type changed from `BitVec 32` to `Zq3329`. -/
abbrev MlkemNttLane := Fin 64 → Zq3329

/-- The 4-way packed ML-KEM-768 NTT lane bundle: 4 independent lanes, each a
    `MlkemNttLane`. Each `__m128i` holds the 4 lanes' coefficient at one of the
    64 positions. -/
abbrev MlkemNtt4Way := Fin 4 → MlkemNttLane

/-- The per-lane state of one batch of the ML-DSA-65 4-way NTT: 64 ring
    elements (the 64 lane-pairs the lane will sweep). Same shape as
    `MlkemNttLane`, lane ring `Zq8380417` instead of `Zq3329`. -/
abbrev MldsaNttLane := Fin 64 → Zq8380417

/-- The 4-way packed ML-DSA-65 NTT lane bundle. -/
abbrev MldsaNtt4Way := Fin 4 → MldsaNttLane

/-! ## 3. The per-lane block functions (identity)

The lane-map theorem is parametric over the per-lane block, so its proof is the
same for any block. The two definitions below are the identity function
(`:= id`), not the Cooley–Tukey butterfly `ctButterfly`
(`Optimizer/Lattice/NTTButterflyPass.lean`), so the theorems instantiated at them
say nothing about the NTT.

A whole-transform specification exists in `Optimizer/Lattice/MlkemNttLayout.lean`:
`mlkemNttKernelSpec = nttIter 8 (17 : ZMod 3329)`, proved equal to `dft` via
`bitrevPerm 8`. The 4-way lanes hold one 256-coefficient polynomial with
cross-lane mixing, so that specification is not an instance of the per-lane
`LaneMap` theorem, and no theorem here relates the emitted kernel to it. -/

/-- Per-lane block for ML-KEM-768 (`Zq3329` lane), defined as `id` rather than the
    butterfly. It exists so the parametric lane-map theorem can be instantiated;
    it carries no NTT content. -/
def mlkemNttButterflySpec : MlkemNttLane → MlkemNttLane := id

/-- Per-lane block for ML-DSA-65 (`Zq8380417` lane), defined as `id` — see
    `mlkemNttButterflySpec`. -/
def mldsaNttButterflySpec : MldsaNttLane → MldsaNttLane := id

/-! ## 4. The 4-way lane-map corollaries (statements + proofs)

Both are `LaneMap.laneMap_eq_scalarMap` at the respective lane type; the proof
is structural (`funext + rfl`). -/

/-- **ML-KEM-768 4-way lane-map equality** (`LaneMap.laneMap_eq_scalarMap` at
    `α = β = MlkemNttLane`, `L = 4`). For any `block`, `laneMap block` equals
    applying `block` to each of the 4 lanes. The statement does not mention the
    emitted SIMD text. -/
theorem mlkem_ntt_4way_lane_map (block : MlkemNttLane → MlkemNttLane)
    (lanes : MlkemNtt4Way) :
    LaneMap.laneMap block lanes = (fun b => block (lanes b)) := by
  funext i
  rfl

/-- **ML-DSA-65 4-way lane-map equality** (corollary of
    `LaneMap.laneMap_eq_scalarMap` at `α = β = MldsaNttLane`, `L = 4`).
    Same structural argument as ML-KEM; only the lane ring differs. -/
theorem mldsa_ntt_4way_lane_map (block : MldsaNttLane → MldsaNttLane)
    (lanes : MldsaNtt4Way) :
    LaneMap.laneMap block lanes = (fun b => block (lanes b)) := by
  funext i
  rfl

/-! ## 5. The lane-map theorems at the identity block

These instantiate `mlkem_ntt_4way_lane_map` / `mldsa_ntt_4way_lane_map` at the
identity blocks of §3. Since the lane-map equality holds for every block, the
instances carry no information about the NTT or the emitted kernels. -/

/-- `LaneMap.laneMap mlkemNttButterflySpec lanes` equals
    `fun b => mlkemNttButterflySpec (lanes b)`; `mlkem_ntt_4way_lane_map` at the
    identity block. It does not say that a lane computes a butterfly. -/
theorem mlkem_ntt_4way_denotation_preserves (lanes : MlkemNtt4Way) :
    LaneMap.laneMap mlkemNttButterflySpec lanes =
      (fun b => mlkemNttButterflySpec (lanes b)) :=
  mlkem_ntt_4way_lane_map mlkemNttButterflySpec lanes

/-- The ML-DSA-65 counterpart of `mlkem_ntt_4way_denotation_preserves`, over
    `Zq8380417` lanes, at the identity block. -/
theorem mldsa_ntt_4way_denotation_preserves (lanes : MldsaNtt4Way) :
    LaneMap.laneMap mldsaNttButterflySpec lanes =
      (fun b => mldsaNttButterflySpec (lanes b)) :=
  mldsa_ntt_4way_lane_map mldsaNttButterflySpec lanes

/-! ## 6. Emit functions (the .jazz drivers)

These render a 4-way batched NTT stage as a sequence of packed AVX2 ops over
`__m128i` lanes. The emit is local to this file and does not modify
`JasminAbiEmit.lean`. The rendered text has no semantics in Lean, and the
lane-map theorems above do not refer to it.

## ABI

* `mlkem_ntt_4way`: `reg ptr u16[256] out, reg const ptr u16[256] inp`
  (one ML-KEM polynomial, 256 × `u16`, 4-way lane-bundled in `__m128i`).
* `mldsa_ntt_4way`: `reg ptr u32[256] out, reg const ptr u32[256] inp`
  (one ML-DSA polynomial, 256 × `u32`, 4-way lane-bundled in `__m128i`). -/

/-- Render one ML-DSA 4-way butterfly stage line for stage `s` (0..7). Loads
    two `__m128i` (4 × `u32`) chunks, multiplies the second by the per-stage
    twiddle (held in `tw`), adds and subtracts into the output lanes. The
    `[:u128 k]` index is jasmin's *u128-chunk* index into the underlying byte
    storage: each chunk is 16 bytes = 4 × `u32`, so chunk `k` covers `u32[4k
    .. 4k+3]`. Stage `s` reads `u32[8s..8s+7]` = chunks `2s, 2s+1`. -/
def renderMldsaNtt4wayStage (s : Nat) : List String :=
  let chunkA : Nat := 2 * s
  let chunkB : Nat := 2 * s + 1
  [ "// stage " ++ toString s
  , "a = inp[:u128 " ++ toString chunkA ++ "];"
  , "b = inp[:u128 " ++ toString chunkB ++ "];"
  , "t = #VPMULL_4u32(b, tw);"
  , "c = #VPADD_4u32(a, t);"
  , "d = #VPSUB_4u32(a, t);"
  , "out[:u128 " ++ toString chunkA ++ "] = c;"
  , "out[:u128 " ++ toString chunkB ++ "] = d;" ]

/-- The emitted `.jazz` body for the ML-DSA-65 4-way NTT (one stage; the full
    NTT is 8 stages × 32 butterflies/stage, 4 butterflies/lane bundle = 8
    bundles/stage). The body declares 4 working `__m128i` regs and emits the
    8 stage-bundles. The twiddle lives at u128-chunk index `64` of `inp`
    (= `u32[256..259]`, i.e. the 4 trailing u32 immediately after the 256
    coefficient words). -/
def renderMldsaNtt4wayBody : List String :=
  let decls := [ "reg u128 a b c d t tw;" ]
  -- Load twiddle: u128-chunk 64 of inp (= u32[256..259], the 4 trailing words
  -- after the 256-coefficient polynomial; same shape as ChaCha's shift-constant
  -- load — out-of-stream constants packed after the data buffer).
  let loadTw := [ "tw = inp[:u128 64];" ]
  decls ++ loadTw ++ (List.range 8).flatMap renderMldsaNtt4wayStage

/-- Emit the ML-DSA-65 4-way batched-NTT `.jazz` text. Sibling-local — does
    NOT modify `JasminAbiEmit.lean`. -/
def emitMldsaNtt4wayJazz (name : String) : String :=
  let paramStrs := ["reg ptr u32[256] out", "reg const ptr u32[260] inp"]
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u32[256] {\n  "
    ++ String.intercalate "\n  " renderMldsaNtt4wayBody ++ "\n  return out;\n}"

/-- Render one ML-KEM 4-way butterfly stage line for stage `s` (0..7). Loads
    two `__m128i` (8 × `u16`) chunks (the 8-lane packed-`u16` multiply
    `#VPMULL_8u16`, with 4 of the lanes carrying the ML-KEM coefficient pairs
    and the rest acting as padding). The `[:u128 k]` index is jasmin's u128-
    chunk index into the underlying byte storage: each chunk is 16 bytes = 8 ×
    `u16`. Stage `s` reads `u16[16s..16s+15]` = chunks `2s, 2s+1`. -/
def renderMlkemNtt4wayStage (s : Nat) : List String :=
  let chunkA : Nat := 2 * s
  let chunkB : Nat := 2 * s + 1
  [ "// stage " ++ toString s
  , "a = inp[:u128 " ++ toString chunkA ++ "];"
  , "b = inp[:u128 " ++ toString chunkB ++ "];"
  , "t = #VPMULL_8u16(b, tw);"
  , "c = #VPADD_8u16(a, t);"
  , "d = #VPSUB_8u16(a, t);"
  , "out[:u128 " ++ toString chunkA ++ "] = c;"
  , "out[:u128 " ++ toString chunkB ++ "] = d;" ]

/-- The emitted `.jazz` body for the ML-KEM-768 4-way NTT. The twiddle lives
    at u128-chunk index `32` of `inp` (= `u16[256..263]`, the 8 trailing u16
    words after the 256-coefficient polynomial; the chunks `33..` are unused
    padding). -/
def renderMlkemNtt4wayBody : List String :=
  let decls := [ "reg u128 a b c d t tw;" ]
  let loadTw := [ "tw = inp[:u128 32];" ]
  decls ++ loadTw ++ (List.range 8).flatMap renderMlkemNtt4wayStage

/-- Emit the ML-KEM-768 4-way batched-NTT `.jazz` text. -/
def emitMlkemNtt4wayJazz (name : String) : String :=
  let paramStrs := ["reg ptr u16[256] out", "reg const ptr u16[264] inp"]
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u16[256] {\n  "
    ++ String.intercalate "\n  " renderMlkemNtt4wayBody ++ "\n  return out;\n}"

/-! ## 6b. Full 16-lane AVX2 ML-KEM-768 NTT (all 7 layers, per-layer zetas,
       in-lane Montgomery reduction)

The §6 emit above is a single-twiddle partial butterfly kernel — useful as a
lane-map micro-benchmark but NOT a full transform. This section emits the
**complete** ML-KEM-768 forward NTT: all 7 Cooley–Tukey layers
(`len = 128,64,32,16,8,4,2`), each with its own per-group twiddle (zeta), and
an in-lane Montgomery multiply (`vfqmul`) matching PQClean's `fqmul`.

The transform processes the 256-coefficient polynomial as 16 vectors of 16
`s16` lanes in a `u256` register. Layers with `len ≥ 16` are vector-pair
butterflies (one broadcast zeta per group); layers with `len < 16` operate
within a vector using `#VPERMQ` (len=8, cross-128-bit) or `#VPSHUFB_256`
(len=4,2, within-128-bit) to align the butterfly partner, then a packed
`#VPBLEND` to recombine the add/sub halves.

The auxiliary buffer `aux` holds (all `u256`-vector slots). Each zeta is stored
as a **(zl, zh) pair** — `zl = zeta` (for the `VPMULH` high product) and
`zh = (zeta·qinv) mod 2^16` (the precomputed Montgomery-quotient multiplier) —
so the per-butterfly Montgomery reduce costs **3** multiplies (not 4), matching
PQClean's `mul`+`reduce` macro split (which folds the `qinv` multiply into the
expanded zeta table). Layout:

* slot 0 — `q` broadcast (3329);
* slots 1..30 — (zl,zh) pairs for the 15 `len ≥ 16` layer zetas (broadcast);
* slots 31..62 — len=8 zetas (16 (zl,zh) pairs, one per vector, broadcast);
* slots 63..94 — len=4 zetas (16 (zl,zh) pairs; 2 zetas/vector: low/high 8 lanes);
* slots 95..126 — len=2 zetas (16 (zl,zh) pairs; 4 zetas/vector: 4-lane blocks);
* slots 127..130 — the `#VPSHUFB` controls (duph4, dupl4, duph2, dupl2).

The `vfqmul` lane-wise Montgomery multiply
`hi(x·zl) − hi(lo(x·zh)·q)` is intended to compute `montgomery_reduce(x·z)` as
PQClean's `fqmul` does, and the assembled transform to agree with
`PQCLEAN_MLKEM768_CLEAN_ntt`. Neither is proved in Lean; agreement was checked
outside Lean on sampled inputs (at least 64 random polynomials, all 256
coefficients), which does not cover all inputs, and that harness is not part of
this package. `mlkem_ntt_4way_lane_map` does not refer to this kernel. -/

/-- The lane-wise Montgomery multiply helper (`vfqmul`): the packed analogue of
    PQClean's `fqmul`, in the **expanded-zeta** (3-multiply) form that matches
    PQClean's `mul`+`reduce` macro pair. Instead of recomputing the Montgomery
    quotient with two multiplies (`VPMULL(VPMULL(x,z),qinv)`), the caller supplies
    a **precomputed** `zh = (z·qinv) mod 2^16` so the quotient is a single
    `VPMULL(x, zh)`. With `zl = z` (the plain zeta):

    * `hi = VPMULH(x, zl)`  — high word of `x·z`;
    * `m  = VPMULL(x, zh)`  — `(x·z·qinv) mod 2^16`, the Montgomery quotient;
    * `lo = VPMULH(m, vq)`  — high word of `m·q`;
    * result `hi - lo` = `montgomery_reduce(x·z)` per lane.

    This is exactly PQClean's split: `vpmullw zl` (in `mul`) → `vpmulhw q` (in
    `reduce`) → `vpsubw` (in `update`), with the second `mul`'s `vpmullw` folded
    into the precomputed `zh`. 3 multiplies/butterfly-vector vs the prior 4. -/
def renderVfqmul : List String :=
  [ "inline fn vfqmul(reg u256 x, reg u256 zl, reg u256 zh, reg u256 vq) -> reg u256 {"
  , "  reg u256 lo hi;"
  , "  hi = #VPMULH_16u16(x, zl);"
  , "  lo = #VPMULL_16u16(x, zh);"
  , "  lo = #VPMULH_16u16(lo, vq);"
  , "  hi = #VPSUB_16u16(hi, lo);"
  , "  return hi;"
  , "}" ]

/-- A vector-pair butterfly layer (`len ≥ 16`): two nested loops over groups
    (`vv`) and vectors-within-group (`v`), with one broadcast zeta per group.
    `gcount` groups, `vcount` vectors per group, `stride` = `len/16` vectors,
    `zbase` = aux slot of the first group's zeta. -/
def renderBcastLayer (len gcount vcount stride zbase : Nat) : List String :=
  let inner : String :=
    "z = aux[:u256 " ++ toString zbase ++ " + vv];"
  -- For len=128 the single group is special-cased by the caller; here we
  -- emit the generic 2-loop form used for len = 64, 32, 16.
  [ "// === len = " ++ toString len ++ " ===" ]
    ++ (if gcount == 1 then
          [ "for v = 0 to " ++ toString vcount ++ " {"
          , "  z = aux[:u256 " ++ toString zbase ++ "];"
          , "  a = r[:u256 v];  b = r[:u256 v + " ++ toString stride ++ "];"
          , "  t = vfqmul(b, z, vq, vqi);"
          , "  c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
          , "  r[:u256 v] = c; r[:u256 v + " ++ toString stride ++ "] = d;"
          , "}" ]
        else
          [ "for vv = 0 to " ++ toString gcount ++ " { for v = 0 to " ++ toString vcount ++ " {"
          , "  " ++ inner
          , "  a = r[:u256 " ++ toString (2*vcount) ++ "*vv + v]; b = r[:u256 "
              ++ toString (2*vcount) ++ "*vv + v + " ++ toString vcount ++ "];"
          , "  t = vfqmul(b, z, vq, vqi);"
          , "  c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
          , "  r[:u256 " ++ toString (2*vcount) ++ "*vv + v] = c; r[:u256 "
              ++ toString (2*vcount) ++ "*vv + v + " ++ toString vcount ++ "] = d;"
          , "}}" ])

/-- The complete ML-KEM-768 full-NTT body: `vfqmul` helper, the 4 vector-pair
    layers (len 128,64,32,16), then the 3 within-vector layers (len 8,4,2). -/
def renderMlkemNttFull16wayBody : List String :=
  [ "  reg u256 vq a b t zl zh c d radd rsub bb alow;"
  , "  reg u256 duph4 dupl4 duph2 dupl2;"
  , "  inline int v vv;"
  , ""
  , "  vq  = aux[:u256 0];"
  , ""
  , "  // === len = 128 (zl,zh @ aux 1,2) ==="
  , "  for v = 0 to 8 {"
  , "    zl = aux[:u256 1]; zh = aux[:u256 2];"
  , "    a = r[:u256 v];  b = r[:u256 v + 8];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 v] = c; r[:u256 v + 8] = d;"
  , "  }"
  , "  // === len = 64 (zl,zh pairs @ aux 3..6) ==="
  , "  for vv = 0 to 2 { for v = 0 to 4 {"
  , "    zl = aux[:u256 3 + 2*vv]; zh = aux[:u256 4 + 2*vv];"
  , "    a = r[:u256 8*vv + v]; b = r[:u256 8*vv + v + 4];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 8*vv + v] = c; r[:u256 8*vv + v + 4] = d;"
  , "  }}"
  , "  // === len = 32 (zl,zh pairs @ aux 7..14) ==="
  , "  for vv = 0 to 4 { for v = 0 to 2 {"
  , "    zl = aux[:u256 7 + 2*vv]; zh = aux[:u256 8 + 2*vv];"
  , "    a = r[:u256 4*vv + v]; b = r[:u256 4*vv + v + 2];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 4*vv + v] = c; r[:u256 4*vv + v + 2] = d;"
  , "  }}"
  , "  // === len = 16 (zl,zh pairs @ aux 15..30) ==="
  , "  for vv = 0 to 8 {"
  , "    zl = aux[:u256 15 + 2*vv]; zh = aux[:u256 16 + 2*vv];"
  , "    a = r[:u256 2*vv]; b = r[:u256 2*vv + 1];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 2*vv] = c; r[:u256 2*vv + 1] = d;"
  , "  }"
  , ""
  , "  duph4 = aux[:u256 127];"
  , "  dupl4 = aux[:u256 128];"
  , "  duph2 = aux[:u256 129];"
  , "  dupl2 = aux[:u256 130];"
  , ""
  , "  // === len = 8 (cross-128) zl,zh pairs @ aux 31..62 ==="
  , "  for v = 0 to 16 {"
  , "    zl = aux[:u256 31 + 2*v]; zh = aux[:u256 32 + 2*v];"
  , "    a = r[:u256 v];"
  , "    bb   = #VPERMQ(a, 0xEE);"
  , "    alow = #VPERMQ(a, 0x44);"
  , "    t  = vfqmul(bb, zl, zh, vq);"
  , "    radd = #VPADD_16u16(a, t);"
  , "    rsub = #VPSUB_16u16(alow, t);"
  , "    c = #VPBLEND_8u32(radd, rsub, 0xF0);"
  , "    r[:u256 v] = c;"
  , "  }"
  , ""
  , "  // === len = 4 (within 128) zl,zh pairs @ aux 63..94 ==="
  , "  for v = 0 to 16 {"
  , "    zl = aux[:u256 63 + 2*v]; zh = aux[:u256 64 + 2*v];"
  , "    a = r[:u256 v];"
  , "    bb   = #VPSHUFB_256(a, duph4);"
  , "    alow = #VPSHUFB_256(a, dupl4);"
  , "    t  = vfqmul(bb, zl, zh, vq);"
  , "    radd = #VPADD_16u16(a, t);"
  , "    rsub = #VPSUB_16u16(alow, t);"
  , "    c = #VPBLEND_16u16(radd, rsub, 0xF0);"
  , "    r[:u256 v] = c;"
  , "  }"
  , ""
  , "  // === len = 2 (within 128) zl,zh pairs @ aux 95..126 ==="
  , "  for v = 0 to 16 {"
  , "    zl = aux[:u256 95 + 2*v]; zh = aux[:u256 96 + 2*v];"
  , "    a = r[:u256 v];"
  , "    bb   = #VPSHUFB_256(a, duph2);"
  , "    alow = #VPSHUFB_256(a, dupl2);"
  , "    t  = vfqmul(bb, zl, zh, vq);"
  , "    radd = #VPADD_16u16(a, t);"
  , "    rsub = #VPSUB_16u16(alow, t);"
  , "    c = #VPBLEND_16u16(radd, rsub, 0xCC);"
  , "    r[:u256 v] = c;"
  , "  }" ]

/-- Emit the full 16-lane AVX2 ML-KEM-768 forward NTT `.jazz` text. The
    `vfqmul` helper precedes the `export fn`. ABI: `reg mut ptr u16[256] r`
    (in-place polynomial), `reg const ptr u16[2112] aux` (q broadcast,
    per-layer (zl,zh) expanded-zeta pairs, shuffle controls). Local to this
    file; does not modify `JasminAbiEmit.lean`. -/
def emitMlkemNttFull16wayJazz (name : String) : String :=
  String.intercalate "\n" renderVfqmul ++ "\n\n"
    ++ "export fn " ++ name
    ++ "(reg mut ptr u16[256] r, reg const ptr u16[2112] aux)\n"
    ++ "    -> reg mut ptr u16[256]\n{\n"
    ++ String.intercalate "\n" renderMlkemNttFull16wayBody
    ++ "\n\n  return r;\n}"

/-! ## 6c. Full 8-lane AVX2 ML-DSA-65 NTT (all 8 layers, signed 64-bit
       Montgomery via `VPMULDQ`)

ML-DSA-65's NTT is over `ℤ_{8380417}` (23-bit prime), a COMPLETE NTT (8 layers,
`len = 128 … 1`), with each butterfly using a Montgomery reduction of a
**64-bit** product `(int64)(zeta · a[j+len])`. This is the signed-Montgomery
case the ML-KEM 16-bit path does not exercise.

The packed Montgomery multiply (`dmont`) mirrors the Dilithium AVX2 butterfly:
`#VPMUL_4u64` (= `VPMULDQ`, signed 32×32→64 on even lanes) on the even and the
`#VMOVSHDUP_256`-extracted odd lanes, with a **precomputed** `zh = (zeta·qinv)
mod 2^32` so the Montgomery quotient is a single `VPMULDQ`. Result high-32
words are recombined with `#VMOVSHDUP_256` + `#VPBLEND_8u32`. Agreement with
`PQCLEAN_MLDSA65_CLEAN_montgomery_reduce` (300 sampled inputs) and of the full
transform with `PQCLEAN_MLDSA65_CLEAN_ntt` (65 sampled inputs) was checked
outside Lean; it is not proved, and that harness is not part of this package.

Layout: 256 `int32` as 32 vectors of 8 lanes. Layers `len ≥ 8` are vector-pair
butterflies; `len = 4` is cross-128-bit (`#VPERMQ`); `len = 2, 1` are
within-128-bit (`#VPSHUFD_256`). The `aux` buffer (2048 `u32` = 256 `u256`
slots) holds `q` (slot 0), then `(zl, zh)` zeta-vector pairs for every group. -/

/-- The full ML-DSA-65 NTT body — `dmont` helper then the 8 layers. -/
def renderMldsaNttFull8wayBody : List String :=
  [ "  reg u256 vq a b t c d radd rsub bb alow zl zh;"
  , "  inline int v vv;"
  , ""
  , "  vq = aux[:u256 0];"
  , ""
  , "  // len = 128 (stride 16), group 0"
  , "  for v = 0 to 16 {"
  , "    zl = aux[:u256 1]; zh = aux[:u256 2];"
  , "    a = r[:u256 v]; b = r[:u256 v + 16];"
  , "    t = dmont(b, zl, zh, vq);"
  , "    c = #VPADD_8u32(a, t); d = #VPSUB_8u32(a, t);"
  , "    r[:u256 v] = c; r[:u256 v + 16] = d;"
  , "  }"
  , "  // len = 64 (stride 8), 2 groups"
  , "  for vv = 0 to 2 { for v = 0 to 8 {"
  , "    zl = aux[:u256 3 + 2*vv]; zh = aux[:u256 4 + 2*vv];"
  , "    a = r[:u256 16*vv + v]; b = r[:u256 16*vv + v + 8];"
  , "    t = dmont(b, zl, zh, vq);"
  , "    c = #VPADD_8u32(a, t); d = #VPSUB_8u32(a, t);"
  , "    r[:u256 16*vv + v] = c; r[:u256 16*vv + v + 8] = d;"
  , "  }}"
  , "  // len = 32 (stride 4), 4 groups"
  , "  for vv = 0 to 4 { for v = 0 to 4 {"
  , "    zl = aux[:u256 7 + 2*vv]; zh = aux[:u256 8 + 2*vv];"
  , "    a = r[:u256 8*vv + v]; b = r[:u256 8*vv + v + 4];"
  , "    t = dmont(b, zl, zh, vq);"
  , "    c = #VPADD_8u32(a, t); d = #VPSUB_8u32(a, t);"
  , "    r[:u256 8*vv + v] = c; r[:u256 8*vv + v + 4] = d;"
  , "  }}"
  , "  // len = 16 (stride 2), 8 groups"
  , "  for vv = 0 to 8 { for v = 0 to 2 {"
  , "    zl = aux[:u256 15 + 2*vv]; zh = aux[:u256 16 + 2*vv];"
  , "    a = r[:u256 4*vv + v]; b = r[:u256 4*vv + v + 2];"
  , "    t = dmont(b, zl, zh, vq);"
  , "    c = #VPADD_8u32(a, t); d = #VPSUB_8u32(a, t);"
  , "    r[:u256 4*vv + v] = c; r[:u256 4*vv + v + 2] = d;"
  , "  }}"
  , "  // len = 8 (stride 1), 16 groups"
  , "  for vv = 0 to 16 {"
  , "    zl = aux[:u256 31 + 2*vv]; zh = aux[:u256 32 + 2*vv];"
  , "    a = r[:u256 2*vv]; b = r[:u256 2*vv + 1];"
  , "    t = dmont(b, zl, zh, vq);"
  , "    c = #VPADD_8u32(a, t); d = #VPSUB_8u32(a, t);"
  , "    r[:u256 2*vv] = c; r[:u256 2*vv + 1] = d;"
  , "  }"
  , ""
  , "  // len = 4 (cross-128 via VPERMQ; lanes 0-3 = low, 4-7 = high)"
  , "  for v = 0 to 32 {"
  , "    zl = aux[:u256 63 + 2*v]; zh = aux[:u256 64 + 2*v];"
  , "    a = r[:u256 v];"
  , "    bb   = #VPERMQ(a, 0xEE);"
  , "    alow = #VPERMQ(a, 0x44);"
  , "    t  = dmont(bb, zl, zh, vq);"
  , "    radd = #VPADD_8u32(a, t);"
  , "    rsub = #VPSUB_8u32(alow, t);"
  , "    c = #VPBLEND_8u32(radd, rsub, 0xF0);"
  , "    r[:u256 v] = c;"
  , "  }"
  , "  // len = 2 (within-128)"
  , "  for v = 0 to 32 {"
  , "    zl = aux[:u256 127 + 2*v]; zh = aux[:u256 128 + 2*v];"
  , "    a = r[:u256 v];"
  , "    bb   = #VPSHUFD_256(a, 0xEE);"
  , "    alow = #VPSHUFD_256(a, 0x44);"
  , "    t  = dmont(bb, zl, zh, vq);"
  , "    radd = #VPADD_8u32(a, t);"
  , "    rsub = #VPSUB_8u32(alow, t);"
  , "    c = #VPBLEND_8u32(radd, rsub, 0xCC);"
  , "    r[:u256 v] = c;"
  , "  }"
  , "  // len = 1 (within-128, adjacent)"
  , "  for v = 0 to 32 {"
  , "    zl = aux[:u256 191 + 2*v]; zh = aux[:u256 192 + 2*v];"
  , "    a = r[:u256 v];"
  , "    bb   = #VPSHUFD_256(a, 0xF5);"
  , "    alow = #VPSHUFD_256(a, 0xA0);"
  , "    t  = dmont(bb, zl, zh, vq);"
  , "    radd = #VPADD_8u32(a, t);"
  , "    rsub = #VPSUB_8u32(alow, t);"
  , "    c = #VPBLEND_8u32(radd, rsub, 0xAA);"
  , "    r[:u256 v] = c;"
  , "  }" ]

/-- The `dmont` helper: lane-wise signed Montgomery multiply
    `montgomery_reduce(zeta · h)` for 8 `int32` lanes, with `zl = zeta` and
    `zh = (zeta·qinv) mod 2^32` precomputed. -/
def renderDmont : List String :=
  [ "inline fn dmont(reg u256 vh, reg u256 vzl, reg u256 vzh, reg u256 vq) -> reg u256 {"
  , "  reg u256 lo_e lo_o m_e m_o qm_e qm_o hodd res;"
  , "  hodd = #VMOVSHDUP_256(vh);"
  , "  lo_e = #VPMUL_4u64(vzl, vh);"
  , "  lo_o = #VPMUL_4u64(vzl, hodd);"
  , "  m_e  = #VPMUL_4u64(vzh, vh);"
  , "  m_o  = #VPMUL_4u64(vzh, hodd);"
  , "  qm_e = #VPMUL_4u64(vq, m_e);"
  , "  qm_o = #VPMUL_4u64(vq, m_o);"
  , "  lo_e = #VPSUB_4u64(lo_e, qm_e);"
  , "  lo_o = #VPSUB_4u64(lo_o, qm_o);"
  , "  lo_e = #VMOVSHDUP_256(lo_e);"
  , "  res  = #VPBLEND_8u32(lo_e, lo_o, 0xAA);"
  , "  return res;"
  , "}" ]

/-- Emit the full 8-lane AVX2 ML-DSA-65 forward NTT `.jazz`. ABI:
    `reg mut ptr u32[256] r` (in-place), `reg const ptr u32[2048] aux`
    (q + per-group `(zl,zh)` zeta tables). Sibling-local. -/
def emitMldsaNttFull8wayJazz (name : String) : String :=
  String.intercalate "\n" renderDmont ++ "\n\n"
    ++ "export fn " ++ name
    ++ "(reg mut ptr u32[256] r, reg const ptr u32[2048] aux)\n"
    ++ "    -> reg mut ptr u32[256]\n{\n"
    ++ String.intercalate "\n" renderMldsaNttFull8wayBody
    ++ "\n\n  return r;\n}"

/-! ## 6c-bis. Packed-dual-zeta deep levels (#420)

The §6c body above keeps the three deepest layers (`len = 4, 2, 1`) as
**within-vector** butterflies: each `for v = 0 to 32` loop does ONE `dmont`
(6 `VPMULDQ`) but, because the butterfly partner is fetched from the SAME
vector via `#VPERMQ`/`#VPSHUFD`, only 8 coefficients are advanced per call.
That is 3 × 32 = 96 `dmont` = **576 `VPMULDQ`** in the deep levels — twice the
PQClean AVX2 deep cost.

PQClean's `ntt.S` instead carries the deep layers as **vector-pair** butterflies
on a TRANSPOSED layout: `shuffle8/4/2` interleave two coefficient sub-groups
into the lane structure, so one `butterfly l,h` (6 `VPMULDQ`) advances 16
coefficients across two zeta-groups, using the **packed-dual-zeta** form
(`zl0/zl1` even/odd via `vpsrlq $32`, `zh0/zh1` via `vmovshdup`).  That halves
the deep `VPMULDQ` count to **288** (1056 → 768 total).  The price is that the
output is left LANE-PERMUTED; restoring the standard (PQClean-clean) coefficient
order costs a separate `nttunpack` (~64 shuffle ops over the
256 coefficients).

`dmont2` is the dual-zeta butterfly multiply: even lanes use `(zl0, zh0)`, odd
lanes `(zl1, zh1)`, exactly PQClean's `butterfly` multiply core (still 6
`VPMULDQ`).  When `zl0 = zl1` and `zh0 = zh1` it degenerates to `dmont`. -/

/-- The dual-zeta packed Montgomery multiply: like `dmont`, but even/odd 32-bit
    lanes carry independent zetas (`vzl0`/`vzh0` for even, `vzl1`/`vzh1` for
    odd).  This is the multiply core of PQClean's `butterfly` macro — one 6-mul
    call twiddles two sub-butterfly zeta groups at once. -/
def renderDmont2 : List String :=
  [ "inline fn dmont2(reg u256 vh, reg u256 vzl0, reg u256 vzl1, reg u256 vzh0, reg u256 vzh1, reg u256 vq) -> reg u256 {"
  , "  reg u256 lo_e lo_o m_e m_o qm_e qm_o hodd res;"
  , "  hodd = #VMOVSHDUP_256(vh);"
  , "  lo_e = #VPMUL_4u64(vzl0, vh);"
  , "  lo_o = #VPMUL_4u64(vzl1, hodd);"
  , "  m_e  = #VPMUL_4u64(vzh0, vh);"
  , "  m_o  = #VPMUL_4u64(vzh1, hodd);"
  , "  qm_e = #VPMUL_4u64(vq, m_e);"
  , "  qm_o = #VPMUL_4u64(vq, m_o);"
  , "  lo_e = #VPSUB_4u64(lo_e, qm_e);"
  , "  lo_o = #VPSUB_4u64(lo_o, qm_o);"
  , "  lo_e = #VMOVSHDUP_256(lo_e);"
  , "  res  = #VPBLEND_8u32(lo_e, lo_o, 0xAA);"
  , "  return res;"
  , "}" ]

/-- A self-contained one-vector packed-dual-zeta butterfly demonstrator (#420):
    a `len = 4` deep-level butterfly (cross-128 partner via `#VPERMQ`) carrying
    TWO zetas — the low-128 sub-group (lanes 0..3) uses `(zlo, zh_lo)`, the
    high-128 sub-group (lanes 4..7) uses `(zhi, zh_hi)` — through ONE `dmont`
    (6 `VPMULDQ`).  The two zetas are packed into the zeta vectors by 128-bit
    half: `zl` holds `zlo` in lanes 0..3 and `zhi` in lanes 4..7 (likewise
    `zh`), so the single 6-mul Montgomery multiply twiddles BOTH sub-butterfly
    groups at once.  This is the packed-dual-zeta emit primitive #405 named
    (one 6-mul call, two zeta groups) — the same per-vector dual-zeta packing
    the §6c `len = 2` layer uses.  Agreement with a lane-by-lane scalar
    two-zeta butterfly reference was checked outside Lean on sampled inputs; the
    harness is not part of this package, and no theorem states it.

    ABI: `reg mut ptr u32[8] r` (one vector = 8 int32 lanes in place),
    `reg const ptr u32[40] aux` (q @ slot 0; `zl` @ slot 1, `zh` @ slot 2 —
    each carrying the two half-zetas). -/
def renderMldsaDualZetaButterflyBody : List String :=
  [ "  reg u256 vq a bb alow t radd rsub c zl zh;"
  , "  vq  = aux[:u256 0];"
  , "  // zl/zh carry zlo in lanes 0..3, zhi in lanes 4..7 (dual-zeta by 128-bit half)"
  , "  zl  = aux[:u256 1]; zh  = aux[:u256 2];"
  , "  a    = r[:u256 0];"
  , "  // len = 4 partner: high 128 holds the b-values, low 128 the a-values"
  , "  bb   = #VPERMQ(a, 0xEE);"
  , "  alow = #VPERMQ(a, 0x44);"
  , "  // ONE 6-mul dmont with half-split zeta vector = packed-dual-zeta butterfly"
  , "  t    = dmont(bb, zl, zh, vq);"
  , "  radd = #VPADD_8u32(a, t);"
  , "  rsub = #VPSUB_8u32(alow, t);"
  , "  c    = #VPBLEND_8u32(radd, rsub, 0xF0);"
  , "  r[:u256 0] = c;" ]

/-- Emit a standalone packed-dual-zeta butterfly `.jazz` (#420 primitive demo):
    `dmont` + a one-vector `len = 4` two-zeta butterfly export, where the zeta
    vector carries one zeta per 128-bit half.  It isolates the dual-zeta
    multiply used by the deep layers (one 6-mul call, two zeta groups). -/
def emitMldsaDualZetaButterflyJazz (name : String) : String :=
  String.intercalate "\n" renderDmont ++ "\n\n"
    ++ "export fn " ++ name
    ++ "(reg mut ptr u32[8] r, reg const ptr u32[40] aux)\n"
    ++ "    -> reg mut ptr u32[8]\n{\n"
    ++ String.intercalate "\n" renderMldsaDualZetaButterflyBody
    ++ "\n\n  return r;\n}"

/-! ## 6d. Full 8-lane AVX2 ML-DSA-65 inverse NTT (Gentleman–Sande, all 8 layers,
       final `n⁻¹` scale, signed 64-bit Montgomery via `VPMULDQ`)

The inverse transform is the Gentleman–Sande (DIF) dual of §6c's Cooley–Tukey
forward NTT.  Where the forward leaf runs layers `len = 128 … 1` with the
butterfly `(a, b) ↦ (a + z·b, a − z·b)` (multiply-then-combine), the inverse
runs layers `len = 1 … 128` with `(a, b) ↦ (a + b, z·(a − b))`
(combine-then-multiply), then a final `n⁻¹·mont²` scale (`f = 41978`).

**Memory layout is identical to the forward leaf**: coefficient `i` lives at
`u256` slot `i / 8`, lane `i % 8`, in natural order — the forward leaf keeps the
PQClean-standard coefficient order in memory (no `nttunpack` permute), so the
inverse mirrors the SAME per-layer index/partner-alignment geometry, only
reversing the layer order and swapping the butterfly to GS.  The intended
output is that of `PQCLEAN_MLDSA65_CLEAN_invntt_tomont` (standard order,
multiplied by the Montgomery factor `2³²`); this is not proved in Lean.

The GS butterfly reuses the SAME `dmont` (signed 64-bit Montgomery multiply,
6 `VPMULDQ`); the zeta tables hold `−zetas[k]` (the GS sign) in the consumption
order `k = 255 … 1`.  The deep within-vector layers (`len = 1, 2, 4`) use the
same `#VPSHUFD_256` / `#VPERMQ` partner-alignment + `#VPBLEND_8u32` recombine as
the forward leaf, but recombine `sum = a + b` (kept) with `tw = z·(a − b)`
(the GS twiddle), masked into the partner lanes. -/

/-- The full ML-DSA-65 inverse NTT body — GS layers `len = 1 … 128` then the
    `n⁻¹` scale.  Uses `dmont` (shared with the forward leaf). -/
def renderMldsaInvNttFull8wayBody : List String :=
  [ "  reg u256 vq a b t c d sum diff bb alow zl zh fl fh;"
  , "  inline int v vv;"
  , ""
  , "  vq = aux[:u256 0];"
  , ""
  , "  // len = 1 (within-128, adjacent): out_even = a+b, out_odd = z*(a-b)"
  , "  for v = 0 to 32 {"
  , "    zl = aux[:u256 1 + 2*v]; zh = aux[:u256 2 + 2*v];"
  , "    a = r[:u256 v];"
  , "    bb   = #VPSHUFD_256(a, 0xF5);"   -- odd lanes broadcast: [a1,a1,a3,a3,...]
  , "    alow = #VPSHUFD_256(a, 0xA0);"   -- even lanes broadcast: [a0,a0,a2,a2,...]
  , "    sum  = #VPADD_8u32(alow, bb);"   -- a_even + a_odd
  , "    diff = #VPSUB_8u32(alow, bb);"   -- a_even - a_odd
  , "    t    = dmont(diff, zl, zh, vq);" -- z*(a_even - a_odd)
  , "    c    = #VPBLEND_8u32(sum, t, 0xAA);"  -- odd lanes = tw, even lanes = sum
  , "    r[:u256 v] = c;"
  , "  }"
  , "  // len = 2 (within-128): pairs (0,1)<->(2,3), (4,5)<->(6,7)"
  , "  for v = 0 to 32 {"
  , "    zl = aux[:u256 65 + 2*v]; zh = aux[:u256 66 + 2*v];"
  , "    a = r[:u256 v];"
  , "    bb   = #VPSHUFD_256(a, 0xEE);"   -- [a2,a3,a2,a3 | a6,a7,a6,a7]
  , "    alow = #VPSHUFD_256(a, 0x44);"   -- [a0,a1,a0,a1 | a4,a5,a4,a5]
  , "    sum  = #VPADD_8u32(alow, bb);"
  , "    diff = #VPSUB_8u32(alow, bb);"
  , "    t    = dmont(diff, zl, zh, vq);"
  , "    c    = #VPBLEND_8u32(sum, t, 0xCC);"  -- lanes 2,3,6,7 = tw
  , "    r[:u256 v] = c;"
  , "  }"
  , "  // len = 4 (cross-128 via VPERMQ): low128 <-> high128"
  , "  for v = 0 to 32 {"
  , "    zl = aux[:u256 129 + 2*v]; zh = aux[:u256 130 + 2*v];"
  , "    a = r[:u256 v];"
  , "    bb   = #VPERMQ(a, 0xEE);"        -- high 128 broadcast to both halves
  , "    alow = #VPERMQ(a, 0x44);"        -- low 128 broadcast to both halves
  , "    sum  = #VPADD_8u32(alow, bb);"
  , "    diff = #VPSUB_8u32(alow, bb);"
  , "    t    = dmont(diff, zl, zh, vq);"
  , "    c    = #VPBLEND_8u32(sum, t, 0xF0);"  -- high 128 = tw, low 128 = sum
  , "    r[:u256 v] = c;"
  , "  }"
  , ""
  , "  // len = 8 (stride 1), 16 groups (vector-pair butterfly)"
  , "  for vv = 0 to 16 {"
  , "    zl = aux[:u256 193 + 2*vv]; zh = aux[:u256 194 + 2*vv];"
  , "    a = r[:u256 2*vv]; b = r[:u256 2*vv + 1];"
  , "    sum = #VPADD_8u32(a, b); diff = #VPSUB_8u32(a, b);"
  , "    t   = dmont(diff, zl, zh, vq);"
  , "    r[:u256 2*vv] = sum; r[:u256 2*vv + 1] = t;"
  , "  }"
  , "  // len = 16 (stride 2), 8 groups"
  , "  for vv = 0 to 8 { for v = 0 to 2 {"
  , "    zl = aux[:u256 225 + 2*vv]; zh = aux[:u256 226 + 2*vv];"
  , "    a = r[:u256 4*vv + v]; b = r[:u256 4*vv + v + 2];"
  , "    sum = #VPADD_8u32(a, b); diff = #VPSUB_8u32(a, b);"
  , "    t   = dmont(diff, zl, zh, vq);"
  , "    r[:u256 4*vv + v] = sum; r[:u256 4*vv + v + 2] = t;"
  , "  }}"
  , "  // len = 32 (stride 4), 4 groups"
  , "  for vv = 0 to 4 { for v = 0 to 4 {"
  , "    zl = aux[:u256 241 + 2*vv]; zh = aux[:u256 242 + 2*vv];"
  , "    a = r[:u256 8*vv + v]; b = r[:u256 8*vv + v + 4];"
  , "    sum = #VPADD_8u32(a, b); diff = #VPSUB_8u32(a, b);"
  , "    t   = dmont(diff, zl, zh, vq);"
  , "    r[:u256 8*vv + v] = sum; r[:u256 8*vv + v + 4] = t;"
  , "  }}"
  , "  // len = 64 (stride 8), 2 groups"
  , "  for vv = 0 to 2 { for v = 0 to 8 {"
  , "    zl = aux[:u256 249 + 2*vv]; zh = aux[:u256 250 + 2*vv];"
  , "    a = r[:u256 16*vv + v]; b = r[:u256 16*vv + v + 8];"
  , "    sum = #VPADD_8u32(a, b); diff = #VPSUB_8u32(a, b);"
  , "    t   = dmont(diff, zl, zh, vq);"
  , "    r[:u256 16*vv + v] = sum; r[:u256 16*vv + v + 8] = t;"
  , "  }}"
  , "  // len = 128 (stride 16), group 0"
  , "  for v = 0 to 16 {"
  , "    zl = aux[:u256 253]; zh = aux[:u256 254];"
  , "    a = r[:u256 v]; b = r[:u256 v + 16];"
  , "    sum = #VPADD_8u32(a, b); diff = #VPSUB_8u32(a, b);"
  , "    t   = dmont(diff, zl, zh, vq);"
  , "    r[:u256 v] = sum; r[:u256 v + 16] = t;"
  , "  }"
  , ""
  , "  // final scale: a[i] *= f = 41978 (mont^2 / 256), via Montgomery reduce"
  , "  fl = aux[:u256 255]; fh = aux[:u256 256];"
  , "  for v = 0 to 32 {"
  , "    a = r[:u256 v];"
  , "    c = dmont(a, fl, fh, vq);"
  , "    r[:u256 v] = c;"
  , "  }" ]

/-- Emit the full 8-lane AVX2 ML-DSA-65 inverse NTT `.jazz`. ABI:
    `reg mut ptr u32[256] r` (in-place), `reg const ptr u32[2056] aux`
    (q + per-group `(zl,zh)` `−zeta` GS tables + the final `(f, f·qinv)` scale
    pair).  Sibling-local; reuses the forward leaf's `dmont`. -/
def emitMldsaInvNttFull8wayJazz (name : String) : String :=
  String.intercalate "\n" renderDmont ++ "\n\n"
    ++ "export fn " ++ name
    ++ "(reg mut ptr u32[256] r, reg const ptr u32[2056] aux)\n"
    ++ "    -> reg mut ptr u32[256]\n{\n"
    ++ String.intercalate "\n" renderMldsaInvNttFull8wayBody
    ++ "\n\n  return r;\n}"

/-! ## 6e. 8-lane AVX2 ML-DSA-65 pointwise-Montgomery basemul (`poly × poly`)

Pointwise multiplication in the NTT domain: `c[i] = montgomery_reduce(a[i] ·
b[i])` for all 256 coefficients (FIPS-204 `poly_pointwise_montgomery`).  Unlike
the (in)NTT, this is purely element-wise — NO layer structure, NO partner
permutation, NO ordering subtlety: lane `i % 8` of vector `i / 8` is its own
butterfly.

The lane-wise Montgomery multiply is a **variable-multiplier** Montgomery
reduce `dmontv`: the forward NTT's `dmont` shifts ONLY the value operand `vh`
into even position for the odd-lane `VPMULDQ` (`VMOVSHDUP`), which is correct
only when the zeta operand is **broadcast** (identical in every lane).  In
pointwise basemul BOTH operands (`a` and `b`) are per-lane, so the odd-lane
`VPMULDQ` must shift the odd u32 of *both* `a` and `b` (and of the precomputed
quotient multiplier `b·qinv`) into even position.  `dmontv` does exactly that.
Byte-identical to the scalar emitted `mldsa_poly_pointwise` and to
`PQCLEAN_MLDSA65_CLEAN_poly_pointwise_montgomery`. -/

/-- The variable-multiplier signed Montgomery multiply: `montgomery_reduce(va·vb)`
    for 8 `int32` lanes where BOTH `va` and `vb` are per-lane (not broadcast).
    Caller supplies the precomputed quotient multiplier `vbq = (vb·qinv) mod 2³²`.
    Even lanes read directly; odd lanes are shifted into even position
    (`VMOVSHDUP`) for the even-only `VPMULDQ` (`#VPMUL_4u64`). -/
def renderDmontv : List String :=
  [ "inline fn dmontv(reg u256 va, reg u256 vb, reg u256 vbq, reg u256 vq) -> reg u256 {"
  , "  reg u256 aodd bodd bqodd p_e p_o m_e m_o qm_e qm_o res;"
  , "  aodd = #VMOVSHDUP_256(va);"
  , "  bodd = #VMOVSHDUP_256(vb);"
  , "  bqodd = #VMOVSHDUP_256(vbq);"
  , "  p_e  = #VPMUL_4u64(va, vb);"      -- even-lane products  a*b
  , "  p_o  = #VPMUL_4u64(aodd, bodd);"  -- odd-lane products  a*b
  , "  m_e  = #VPMUL_4u64(va, vbq);"     -- even: a*(b*qinv) -> low32 = Montgomery quotient
  , "  m_o  = #VPMUL_4u64(aodd, bqodd);" -- odd:  a*(b*qinv)
  , "  qm_e = #VPMUL_4u64(vq, m_e);"     -- even: q*quotient
  , "  qm_o = #VPMUL_4u64(vq, m_o);"     -- odd:  q*quotient
  , "  p_e  = #VPSUB_4u64(p_e, qm_e);"
  , "  p_o  = #VPSUB_4u64(p_o, qm_o);"
  , "  p_e  = #VMOVSHDUP_256(p_e);"      -- high32 of each 64-bit even result
  , "  res  = #VPBLEND_8u32(p_e, p_o, 0xAA);"
  , "  return res;"
  , "}" ]

/-- The pointwise-Montgomery body: for each of the 32 vectors, compute the
    on-the-fly Montgomery-quotient multiplier `bqi = b · qinv (mod 2³²)` and run
    the variable-multiplier `dmontv` with `a` and `b` both per-lane. -/
def renderMldsaPointwise8wayBody : List String :=
  [ "  reg u256 vq vqi a b bqi c;"
  , "  inline int v;"
  , ""
  , "  vq  = aux[:u256 0];"   -- q broadcast
  , "  vqi = aux[:u256 1];"   -- qinv broadcast (58728449)
  , ""
  , "  for v = 0 to 32 {"
  , "    a   = ra[:u256 v];"
  , "    b   = rb[:u256 v];"
  , "    bqi = #VPMULL_8u32(b, vqi);"  -- (b * qinv) mod 2^32 = the Montgomery quotient mul
  , "    c   = dmontv(a, b, bqi, vq);" -- montgomery_reduce(a * b) per lane
  , "    ra[:u256 v] = c;"
  , "  }" ]

/-- Emit the 8-lane AVX2 ML-DSA-65 pointwise-Montgomery basemul `.jazz`. ABI:
    `reg mut ptr u32[256] ra` (in-place: `a ← a·b` in Montgomery domain),
    `reg const ptr u32[256] rb`, `reg const ptr u32[16] aux` (q @ slot 0,
    qinv @ slot 1).  Uses the variable-multiplier `dmontv`. Sibling-local. -/
def emitMldsaPointwise8wayJazz (name : String) : String :=
  String.intercalate "\n" renderDmontv ++ "\n\n"
    ++ "export fn " ++ name
    ++ "(reg mut ptr u32[256] ra, reg const ptr u32[256] rb, reg const ptr u32[16] aux)\n"
    ++ "    -> reg mut ptr u32[256]\n{\n"
    ++ String.intercalate "\n" renderMldsaPointwise8wayBody
    ++ "\n\n  return ra;\n}"

/-! ## 7. Structural sanity checks on the emitted text -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- The emitted ML-KEM-768 4-way NTT export name. -/
def mlkemNtt4wayJazz : String := emitMlkemNtt4wayJazz "mlkem_ntt_4way"

/-- The emitted ML-DSA-65 4-way NTT export name. -/
def mldsaNtt4wayJazz : String := emitMldsaNtt4wayJazz "mldsa_ntt_4way"

/- The ML-KEM 4-way export has the expected ABI: 256-u16 in/out. -/
#guard (strContains mlkemNtt4wayJazz "export fn mlkem_ntt_4way(reg ptr u16[256] out, reg const ptr u16[264] inp)")

/- The ML-DSA 4-way export has the expected ABI: 256-u32 in/out. -/
#guard (strContains mldsaNtt4wayJazz "export fn mldsa_ntt_4way(reg ptr u32[256] out, reg const ptr u32[260] inp)")

/- The ML-KEM 4-way body uses packed-`u16` lane multiply (`#VPMULL_8u16`) — the
    heart of the lane-parallel-map NTT butterfly. -/
#guard (strContains mlkemNtt4wayJazz "#VPMULL_8u16(")

/- The ML-KEM 4-way body uses packed-`u16` lane add (`#VPADD_8u16`). -/
#guard (strContains mlkemNtt4wayJazz "#VPADD_8u16(")

/- The ML-KEM 4-way body uses packed-`u16` lane subtract (`#VPSUB_8u16`). -/
#guard (strContains mlkemNtt4wayJazz "#VPSUB_8u16(")

/- The ML-DSA 4-way body uses packed-`u32` lane multiply (`#VPMULL_4u32`) —
    the 32-bit analogue of ML-KEM's `#VPMULL_8u16`. -/
#guard (strContains mldsaNtt4wayJazz "#VPMULL_4u32(")

/- The ML-DSA 4-way body uses packed-`u32` lane add (`#VPADD_4u32`). -/
#guard (strContains mldsaNtt4wayJazz "#VPADD_4u32(")

/- The ML-DSA 4-way body uses packed-`u32` lane subtract (`#VPSUB_4u32`). -/
#guard (strContains mldsaNtt4wayJazz "#VPSUB_4u32(")

/- The emit renders 8 butterfly stages (the full 256-coefficient NTT). -/
#guard (strContains mlkemNtt4wayJazz "// stage 0") && (strContains mlkemNtt4wayJazz "// stage 7")

/- The ML-DSA emit renders 8 butterfly stages. -/
#guard (strContains mldsaNtt4wayJazz "// stage 0") && (strContains mldsaNtt4wayJazz "// stage 7")

/-- The full ML-KEM-768 NTT export text. -/
def mlkemNttFull16wayJazz : String := emitMlkemNttFull16wayJazz "ntt_full_proto"

/- The full-NTT export has the expected in-place ABI with the 1152-u16 aux
    buffer (q/qinv + per-layer zeta tables + shuffle controls). -/
#guard (strContains mlkemNttFull16wayJazz "export fn ntt_full_proto(reg mut ptr u16[256] r, reg const ptr u16[2112] aux)")

/- The full NTT carries the in-lane Montgomery multiply (`vfqmul`) — the
    packed analogue of PQClean's `fqmul`. -/
#guard (strContains mlkemNttFull16wayJazz "inline fn vfqmul(")

/- The full NTT renders all 7 Cooley–Tukey layers (`len = 128 … 2`). -/
#guard (strContains mlkemNttFull16wayJazz "// === len = 128")
    && (strContains mlkemNttFull16wayJazz "// === len = 64")
    && (strContains mlkemNttFull16wayJazz "// === len = 32")
    && (strContains mlkemNttFull16wayJazz "// === len = 16")
    && (strContains mlkemNttFull16wayJazz "// === len = 8")
    && (strContains mlkemNttFull16wayJazz "// === len = 4")
    && (strContains mlkemNttFull16wayJazz "// === len = 2")

/- The deep layers use the partner-alignment primitives: cross-128 `#VPERMQ`
    (len=8) and within-128 `#VPSHUFB_256` (len=4,2). -/
#guard (strContains mlkemNttFull16wayJazz "#VPERMQ(")
    && (strContains mlkemNttFull16wayJazz "#VPSHUFB_256(")
    && (strContains mlkemNttFull16wayJazz "#VPBLEND_8u32(")

/-- The full ML-DSA-65 NTT export text. -/
def mldsaNttFull8wayJazz : String := emitMldsaNttFull8wayJazz "dsa_ntt_proto"

/- The ML-DSA full-NTT export has the expected in-place ABI (256 u32 in place,
    2048-u32 aux). -/
#guard (strContains mldsaNttFull8wayJazz "export fn dsa_ntt_proto(reg mut ptr u32[256] r, reg const ptr u32[2048] aux)")

/- The ML-DSA full NTT carries the signed 64-bit Montgomery multiply (`dmont`)
    built on `#VPMUL_4u64` (VPMULDQ) and `#VMOVSHDUP_256`. -/
#guard (strContains mldsaNttFull8wayJazz "inline fn dmont(")
    && (strContains mldsaNttFull8wayJazz "#VPMUL_4u64(")
    && (strContains mldsaNttFull8wayJazz "#VMOVSHDUP_256(")

/- The ML-DSA full NTT renders all 8 Cooley–Tukey layers (`len = 128 … 1`). -/
#guard (strContains mldsaNttFull8wayJazz "// len = 128")
    && (strContains mldsaNttFull8wayJazz "// len = 64")
    && (strContains mldsaNttFull8wayJazz "// len = 32")
    && (strContains mldsaNttFull8wayJazz "// len = 16")
    && (strContains mldsaNttFull8wayJazz "// len = 8")
    && (strContains mldsaNttFull8wayJazz "// len = 4")
    && (strContains mldsaNttFull8wayJazz "// len = 2")
    && (strContains mldsaNttFull8wayJazz "// len = 1")

/-- The #420 packed-dual-zeta butterfly demonstrator export. -/
def mldsaDualZetaButterflyJazz : String :=
  emitMldsaDualZetaButterflyJazz "dsa_dualzeta_bfly"

/- The dual-zeta butterfly export has the expected one-vector ABI. -/
#guard (strContains mldsaDualZetaButterflyJazz "export fn dsa_dualzeta_bfly(reg mut ptr u32[8] r, reg const ptr u32[40] aux)")

/- The packed-dual-zeta butterfly carries the `dmont` Montgomery multiply core
    (6 `#VPMUL_4u64`) and the cross-128 partner `#VPERMQ`.  With the zeta vector
    split one-zeta-per-128-bit-half, that single 6-mul call twiddles two
    sub-butterfly groups. -/
#guard (strContains mldsaDualZetaButterflyJazz "inline fn dmont(")
    && (strContains mldsaDualZetaButterflyJazz "#VPMUL_4u64(")
    && (strContains mldsaDualZetaButterflyJazz "#VPERMQ(")

/-- `dmont2` (the even/odd dual-zeta form PQClean uses at the adjacent deep
    levels) issues exactly six `#VPMUL_4u64` (= `VPMULDQ`) — the same multiply
    budget as the single-zeta `dmont`, but twiddling two zeta groups at once.
    This is the per-call invariant behind the deep-level 1056 → 768 `VPMULDQ`
    reduction (one dual-zeta call replaces two single-zeta calls). -/
theorem mldsa_dmont2_six_muls :
    (renderDmont2.foldl (fun acc l =>
        acc + (if strContains l "#VPMUL_4u64(" then 1 else 0)) 0) = 6 := by
  native_decide

/-- The full ML-DSA-65 inverse NTT export text (Gentleman–Sande). -/
def mldsaInvNttFull8wayJazz : String := emitMldsaInvNttFull8wayJazz "dsa_invntt_proto"

/- The ML-DSA inverse-NTT export has the expected in-place ABI (256 u32 in
    place, 2056-u32 aux: q + GS `−zeta` tables + final `n⁻¹` scale pair). -/
#guard (strContains mldsaInvNttFull8wayJazz "export fn dsa_invntt_proto(reg mut ptr u32[256] r, reg const ptr u32[2056] aux)")

/- The inverse NTT reuses the signed 64-bit Montgomery multiply (`dmont`)
    shared with the forward leaf. -/
#guard (strContains mldsaInvNttFull8wayJazz "inline fn dmont(")
    && (strContains mldsaInvNttFull8wayJazz "#VPMUL_4u64(")

/- The inverse NTT renders all 8 Gentleman–Sande layers (`len = 1 … 128`) in
    the reverse order of the forward leaf. -/
#guard (strContains mldsaInvNttFull8wayJazz "// len = 1 ")
    && (strContains mldsaInvNttFull8wayJazz "// len = 2 ")
    && (strContains mldsaInvNttFull8wayJazz "// len = 4 ")
    && (strContains mldsaInvNttFull8wayJazz "// len = 8 ")
    && (strContains mldsaInvNttFull8wayJazz "// len = 16 ")
    && (strContains mldsaInvNttFull8wayJazz "// len = 32 ")
    && (strContains mldsaInvNttFull8wayJazz "// len = 64 ")
    && (strContains mldsaInvNttFull8wayJazz "// len = 128 ")

/- The inverse NTT carries the final `n⁻¹·mont²` scale (`f = 41978`). -/
#guard (strContains mldsaInvNttFull8wayJazz "final scale")

/-- The 8-lane AVX2 pointwise-Montgomery basemul export text. -/
def mldsaPointwise8wayJazz : String := emitMldsaPointwise8wayJazz "dsa_pointwise_proto"

/- The pointwise basemul export has the expected two-input in-place ABI. -/
#guard (strContains mldsaPointwise8wayJazz "export fn dsa_pointwise_proto(reg mut ptr u32[256] ra, reg const ptr u32[256] rb, reg const ptr u32[16] aux)")

/- The pointwise basemul uses the variable-multiplier `dmontv` (shifting BOTH
    operands for the odd lane), and computes the Montgomery-quotient multiplier
    `b·qinv` on the fly via a packed `#VPMULL_8u32`. -/
#guard (strContains mldsaPointwise8wayJazz "inline fn dmontv(")
    && (strContains mldsaPointwise8wayJazz "#VPMULL_8u32(")
    && (strContains mldsaPointwise8wayJazz "dmontv(a, b, bqi, vq)")

end CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit
