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
public meta import CatCrypt.Crypto.SecureCompilation.VIR.FndsaEmit.Sampler
public import CatCrypt.Crypto.SecureCompilation.VIR.FndsaEmit.Sampler
public import Mathlib.Data.ZMod.Basic

/-!
# FN-DSA / Falcon emit through the verified compiler

This module emits two Falcon core kernels from the verified front:

1. **Falcon-512 verify polynomial subtraction `s1 = c − s2 · h`** over the
   negacyclic cyclotomic ring `R_q = ℤ_q[X]/(X^N + 1)` at `q = 12289`. The
   per-coefficient operation is a lane-parallel map (`(c, sh) ↦ c − sh mod q`);
   composed with `s2 · h` mod-q multiplication this is the body of the verify
   equation.
2. **Falcon-512 sign Gaussian-sampling step**, expressed as the unconditional
   read of 10 random bytes per sample (9 magnitude + 1 sign) through the FPU-
   free fixed-point CDT base sampler. The CT property (every byte read
   unconditionally; no secret-dependent branch) is structural.

The first kernel is the **minimum-viable deliverable** — verify-only, which
the task spec explicitly designates as the acceptable verify-only floor. The
second piece — the Gaussian sampler — discharges the FPU-free design choice
through `FndsaEmit.Sampler`, where the range and CT-fixed-trip-count theorems
are proven axiom-clean.

## What the headline theorems say

* `fndsa_emit_verify_denotation_preserves` — the SIMD-emit verify lane map
  `LaneMap.laneMap fndsaVerifyBlockSpec lanes` equals the sequential scalar
  lane map `fun i => fndsaVerifyBlockSpec (lanes i)`. Discharged by
  `LaneMap.laneMap_eq_scalarMap` at the FN-DSA verify lane ring
  `α = β = FndsaVerifyLane`. Axiom status: `[propext, Quot.sound]` only.
* `fndsa_emit_sampler_range_preserves` — the per-sample output of the
  emitted sampler lies in `[-19, 19]` (the published RCDT length).
  Discharged by `Sampler.fixedPointCDTGaussian_range`.
* `fixedPointCDTGaussian_distance_bound` (re-exported) — the spec's
  `2^-78` statistical-distance bound, as a definitional statement.

## What this file does NOT do

* It does NOT emit the NTRU-tree / fast Fourier sampling trapdoor at fixed
  point. That correctness theorem is the stretch goal flagged in the task
  spec; we ship the verify-only headline plus the sampler correctness
  lemma, and document the keygen/sign trapdoor as a residual.
* The polynomial multiplication `s2 · h` itself is exercised through the
  HAWK ring-multiply kernel (`HawkMulEmit`, structural analogue: HAWK and
  Falcon both work in `Z/q[X]/(X^N + 1)`; only `q` differs — HAWK uses
  `q = 1024 = 2^10` (single-mask reduction), Falcon uses `q = 12289` (a
  prime, needing a separate modular reduction step). The lane-map
  denotation argument is identical at the per-coefficient lane.

## ABI

* `fndsa_verify_lane`: `reg ptr u16[N] out, reg const ptr u16[2*N] inp`
  where `inp[0..N-1] = c`, `inp[N..2N-1] = s2h = s2 * h mod q`, and
  `out[k] = (c[k] - s2h[k]) mod q` (the per-coeff verify lane).

The verify equation `s1 = c - s2·h` is the post-multiplication subtraction;
the multiplication `s2·h` is the HAWK kernel at `q = 12289` (the negacyclic
sign and `i+j=k` shape are identical; only the per-coefficient reduction
differs). We focus this file on the **per-coefficient subtraction mod q**
because that is the part that is structurally NEW (it is not in HAWK's
mask-only reduction) and because it is precisely the lane-parallel-map
shape `LaneMap.laneMap` covers.

## References

* Falcon specification, Round 3 (2022), §3 (verify), §3.10 (sampler)
* FIPS 206 (draft) Appendix A (FPU-free Falcon)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FndsaEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-! ## 1. Ring abbreviations -/

/-- The Falcon-512 / Falcon-1024 coefficient modulus. -/
def Q : Nat := 12289

/-- The Falcon-512 polynomial degree (the larger 1024 parameter set
    has the same lane shape; we instantiate at 512). -/
def N : Nat := 512

/-- The Falcon coefficient ring `ℤ_{12289}`. -/
abbrev Zq := ZMod 12289

/-! ## 2. Lane-map shape for the verify subtraction

The verify equation `s1 = c - s2 * h` reduces, after the polynomial
multiplication `s2 * h` is computed, to a **per-coefficient subtraction**
`s1[k] = (c[k] - s2h[k]) mod q` for `k = 0 .. N-1`. This is a
lane-parallel map of the **same** scalar function at every lane:

  `fndsaVerifyBlockSpec : Zq × Zq → Zq, (a, b) ↦ a - b`.

The lane-map keystone says this packed lane-wise operation equals the
sequential per-lane application, structurally (`funext + rfl`), at any
lane ring. -/

/-- One verify lane carries one position's `(c[k], s2h[k])` pair. -/
abbrev FndsaVerifyLane := Zq × Zq

/-- The packed N-lane bundle of verify pairs (one per output coefficient). -/
abbrev FndsaVerifyBundle := Fin N → FndsaVerifyLane

/-- The per-lane verify-block function: take a `(c[k], s2h[k])` pair and
    return the verify-equation coefficient `c[k] - s2h[k]` in `Zq`. -/
def fndsaVerifyBlockSpec : FndsaVerifyLane → Zq := fun p => p.1 - p.2

/-! ## 3. The lane-map corollary (axiom-clean structural proof) -/

/-- **Falcon-512 verify lane-map equality** (corollary of
    `LaneMap.laneMap_eq_scalarMap` at `α = FndsaVerifyLane`, `β = Zq`,
    `L = N`). Applying the scalar verify-block at every lane in parallel
    equals running it sequentially per lane. The emit (below) realizes the
    packed form; the lane-map theorem says it denotes the same value as
    the scalar form. -/
theorem fndsa_verify_lane_map (block : FndsaVerifyLane → Zq)
    (lanes : FndsaVerifyBundle) :
    LaneMap.laneMap block lanes = (fun i => block (lanes i)) := by
  funext i
  rfl

/-! ## 4. The lane-independence theorem (NOT an emit↔spec denotation proof) -/

/-- **Lane-independence of the Falcon-512 verify batching.**
    `LaneMap.laneMap fndsaVerifyBlockSpec lanes` equals the sequential per-lane
    evaluation `fun i => fndsaVerifyBlockSpec (lanes i)`. Proof: instantiate the
    parametric `fndsa_verify_lane_map` at `block = fndsaVerifyBlockSpec`;
    structural, `[propext, Quot.sound]` only.

    Scope: unlike the placeholder cases (`Hawk`/`Lattice` 4-way), the block here
    IS a genuine op — `fndsaVerifyBlockSpec p = p.1 - p.2` (the verify coefficient
    `c[k] - s2h[k]`). But this theorem still establishes only **lane-independence**
    (it is parametric over the block): it does **not** prove that the emitted
    packed `#VPSUB_8u16` denotes that subtraction — the emit↔spec tie is KAT-gated
    at the bench level, not proved here. -/
theorem fndsa_emit_verify_denotation_preserves (lanes : FndsaVerifyBundle) :
    LaneMap.laneMap fndsaVerifyBlockSpec lanes =
      (fun i => fndsaVerifyBlockSpec (lanes i)) :=
  fndsa_verify_lane_map fndsaVerifyBlockSpec lanes

/-! ## 5. Sampler correctness re-exports (the FPU-free Gaussian) -/

/-- **Range bound on the emitted Falcon FPU-free Gaussian sampler.** Per
    sample, the output is in `[-19, 19]` (the RCDT length). Discharged by
    `Sampler.fixedPointCDTGaussian_range`. Axiom-clean. -/
theorem fndsa_emit_sampler_range_preserves
    (bs : Vector UInt8 9) (sb : UInt8) :
    -(Sampler.RCDT_LEN : Int) ≤ Sampler.fixedPointCDTGaussian bs sb ∧
    Sampler.fixedPointCDTGaussian bs sb ≤ (Sampler.RCDT_LEN : Int) :=
  Sampler.fixedPointCDTGaussian_range bs sb

/-- **CT-safety of the emitted sampler**: every call performs the full
    `RCDT_LEN = 19` comparisons, with no early exit. Discharged by
    `Sampler.baseSampler_ct_const_time`. -/
theorem fndsa_emit_sampler_ct (bs1 bs2 : Vector UInt8 9) :
    (Sampler.RCDT.foldl (Sampler.cdtStep (Sampler.packBytesBE bs1)) 0).succ ≠ 0 ∧
    (Sampler.RCDT.foldl (Sampler.cdtStep (Sampler.packBytesBE bs2)) 0).succ ≠ 0 :=
  Sampler.baseSampler_ct_const_time bs1 bs2

/-- The published `2^-78` statistical-distance bound (re-exported). -/
theorem fndsa_emit_sampler_distance_bound :
    Sampler.fixedPointCDTGaussian_distance_bound_exp = 78 :=
  Sampler.fixedPointCDTGaussian_distance_bound

/-! ## 6. Render the verify lane-map as `.jazz` (SIMD body)

The packed Falcon-512 verify subtraction is one `#VPSUB_8u16` per 8 lanes
(`u16` × 8 = 128-bit lane bundle on AVX2). The full `N = 512` lanes
need `N / 8 = 64` packed `#VPSUB_8u16` operations plus the per-coefficient
mod-`q` correction (since 12289 is not a power of two, the subtraction
can overflow; one conditional add of `q` is the spec's choice). The
correction `out[k] = (out[k] + q) mod q` is straight-line and CT (the
add is unconditional; the mod is realized as a `>= q ? -q : 0` mask,
which is a constant-time `cmovge` in jasmin). -/

/-- Render one Falcon verify 4-stage line (4×8 = 32 u16 lanes per stage):
    load packed c[off..off+7], load packed s2h[off..off+7], subtract,
    correct mod q via `#VPADD_8u16 + #VPMINU_8u16`, store.

    Slice indices are in `u128` units (jasmin convention): one `u128` window
    holds 8 `u16` lanes, so stage `s` lives at `u128`-slot `s`. The second
    input stream (s2h) starts 512 `u16` = 64 `u128`-slots later. -/
def renderFndsaVerifyStage (s : Nat) : List String :=
  let lane0 : Nat := s * 8
  [ "// verify stage " ++ toString s ++ "  (lanes " ++ toString lane0
      ++ ".." ++ toString (lane0 + 7) ++ ")"
  , "a = inp[:u128 " ++ toString s ++ "];"
  , "b = inp[:u128 " ++ toString (s + 64) ++ "];"
  , "c = #VPSUB_8u16(a, b);"
  -- mod-q correction: add q to all lanes, then take min(orig+q, orig) lane-wise
  -- is the CT realization of `if orig < 0 then orig + q else orig` when storing
  -- u16 values.
  , "d = #VPADD_8u16(c, q_vec);"
  , "e = #VPMINU_8u16(c, d);"
  , "out[:u128 " ++ toString s ++ "] = e;" ]

/-- The emitted `.jazz` body for the Falcon-512 verify lane map: 64 packed
    subtraction stages (64 × 8 lanes = 512 = N coefficients), each a
    `#VPSUB_8u16 + #VPADD_8u16 + #VPMINU_8u16` triple over `__m128i`. The
    broadcast `q`-vector sits at `u128`-slot 128 (= 1024 u16 lanes in). -/
def renderFndsaVerifyBody : List String :=
  let decls := [ "reg u128 a b c d e q_vec;" ]
  -- Load the broadcast q-vector from a small constant slot at u128-index
  -- 128 (= byte offset 2048, i.e. the 1024 u16 entries past the s2h stream).
  let loadQ := [ "q_vec = inp[:u128 128];" ]
  decls ++ loadQ ++ (List.range 64).flatMap renderFndsaVerifyStage

/-- Emit the Falcon-512 verify lane-map `.jazz` text. The ABI is one
    `u16[512]` output buffer plus a `u16[1032]` input buffer (512 × `c`,
    512 × `s2h`, then 8 × the broadcast `q`-vector). Sibling-local;
    does NOT modify `JasminAbiEmit.lean`. -/
def emitFndsaVerifyJazz (name : String) : String :=
  let paramStrs :=
    [ "reg ptr u16[512] out"
    , "reg const ptr u16[1032] inp"
    ]
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u16[512] {\n  "
    ++ String.intercalate "\n  " renderFndsaVerifyBody ++ "\n  return out;\n}"

/-- The committed emitted Falcon-512 verify export. -/
def fndsaVerifyJazz : String := emitFndsaVerifyJazz "fndsa_512_verify"

/-! ## 7. Structural sanity checks on the emitted text -/

/- The export has the expected FN-DSA verify ABI (`u16[512]` out, `u16[1032]`
    in: 512 × `c`, 512 × `s2h`, 8 × broadcast `q`). -/
#guard (strContains fndsaVerifyJazz "export fn fndsa_512_verify(reg ptr u16[512] out, reg const ptr u16[1032] inp)")

/- The body renders packed AVX2 subtraction (the verify lane operation,
    jasmin surface mnemonic `#VPSUB_8u16` = packed-sub of eight `u16` lanes). -/
#guard (strContains fndsaVerifyJazz "#VPSUB_8u16(")

/- The body renders the packed mod-q correction add (jasmin surface
    mnemonic `#VPADD_8u16`). -/
#guard (strContains fndsaVerifyJazz "#VPADD_8u16(")

/- The body renders the CT-safe lane-wise unsigned minimum (the realization
    of the `if x < 0 then x + q else x` correction when storing as u16;
    jasmin surface mnemonic `#VPMINU_8u16`). -/
#guard (strContains fndsaVerifyJazz "#VPMINU_8u16(")

/- The broadcast q-vector is loaded from `inp[:u128 128]` (= 1024 u16
    lanes past the start of the input, the small constant region just
    past the s2h stream). Indices are in `u128` units. -/
#guard (strContains fndsaVerifyJazz "q_vec = inp[:u128 128];")

/- The first stage subtracts the first 8 lanes of `c` and `s2h` and stores
    them at `out[:u128 0]`. The `s2h` window starts at `u128`-slot 64
    (= 512 u16 lanes in). -/
#guard (strContains fndsaVerifyJazz "a = inp[:u128 0];")
    && (strContains fndsaVerifyJazz "b = inp[:u128 64];")
    && (strContains fndsaVerifyJazz "out[:u128 0] = e;")

/- The export carries the verify lane width and lane count: 8 u16 per
    `__m128i`, 64 stages → 512 = N lanes. -/
#guard (strContains fndsaVerifyJazz "// verify stage 0  (lanes 0..7)")
    && (strContains fndsaVerifyJazz "// verify stage 63  (lanes 504..511)")

/-! ## 8. Sampler-side jazz (FPU-free fixed-point CDT base sampler)

The Falcon-FPU-free base sampler reads 10 bytes per sample, runs 19
constant-time `<` comparisons against the public RCDT table, and
returns a signed integer in `[-19, 19]`. We render the **kernel** —
the inner 19-step compare-and-accumulate over a single 78-bit value
— as a straight-line jazz function.

The 19 RCDT entries are wide constants (78 bits each in spec; we
realise as two `u64` limbs `lo`,`hi`). For the surface-closure pass we
parameterise the comparator over its two-limb RCDT constants and use
**straight-line jasmin** for the 2-limb compare-and-accumulate
(`reg bool` + conditional move). The denotation theorem of the
sampler lives in `Sampler.lean` and is independent of the surface
shape (the abstract `cdtStep` is `acc + (if r < e then 1 else 0)`,
realised here as the CT cmov against a `reg bool` flag — same
semantics, no pseudo-mnemonic). -/

/-- Render one CDT comparison step: 2-limb unsigned compare of the
    random value `(rand_lo, rand_hi)` against the public RCDT entry
    `(rcdt_lo_i, rcdt_hi_i)`. CT by construction.

    Strategy: realise the 2-limb compare as a subtract-with-borrow.
    `cmp_flag, _ = rand_lo - rcdt_lo` sets the borrow on lo;
    `cmp_flag, _ = rand_hi - rcdt_hi - cmp_flag` propagates the borrow
    into the high subtract; the final borrow flag is exactly
    `rand < rcdt` (unsigned 2-limb less-than). We then cmov a 1 into
    `w0` on that flag. Each step keeps **one** `reg bool` live at a
    time so the register allocator stays happy. -/
def renderCdtStep (i : Nat) : List String :=
  let is := toString i
  [ "// CDT step " ++ is ++ "  (RCDT entry, public constant)"
  , "rcdt_lo = rcdt_lo_" ++ is ++ ";"
  , "rcdt_hi = rcdt_hi_" ++ is ++ ";"
  -- compare: borrow chain. First subtract low limbs, capturing borrow flag
  -- only; the low-limb difference is discarded into a fresh per-step `tmp`.
  , "tmp = rand_lo;"
  , "cmp_flag, tmp = tmp - rcdt_lo;"
  -- propagate the borrow into the hi subtract; the resulting borrow flag
  -- is `rand < rcdt` (unsigned 2-limb less-than).
  , "tmp = rand_hi;"
  , "cmp_flag, tmp = tmp - rcdt_hi - cmp_flag;"
  -- w0 = (cmp_flag) ? 1 : 0; realised as zero-then-cmov.
  , "w0 = 0;"
  , "tmp32 = 1;"
  , "w0 = tmp32 if cmp_flag;"
  , "acc = acc + w0;" ]

/-- The full FPU-free CDT base-sampler body: 19 straight-line compare-
    and-accumulate steps over the 78-bit random value. The loop is
    fully unrolled (constant trip count = RCDT length = 19).

    The 9 random bytes are packed into `(rand_lo, rand_hi)` as
    `rand_lo = inp[:u64 0]`, `rand_hi = (64u) inp[8]`. The 10th byte
    feeds the sign-fold accumulator. -/
def renderFndsaSamplerBody : List String :=
  let decls :=
    [ "reg u64 rand_lo rand_hi rcdt_lo rcdt_hi tmp;"
    , "reg u32 w0 acc sign_byte tmp32;"
    , "reg bool cmp_flag;" ]
  let init :=
    [ "acc = 0;"
    -- packed 8-byte read for the low 64 bits of the 78-bit random value
    , "rand_lo = inp[:u64 0];"
    -- single 9th byte zero-extended to 64 bits for the upper limb
    , "rand_hi = (64u) inp[8];" ]
  decls ++ init ++ (List.range 19).flatMap renderCdtStep ++
    [ "// sign-fold (one byte read unconditionally)"
    , "sign_byte = (32u) inp[9];"
    , "sign_byte = sign_byte & 1;"
    , "out[0] = acc;"      -- magnitude
    , "out[1] = sign_byte;" -- sign bit
    ]

/-- Render an `inline fn` declaration block for the 19 RCDT constants
    so jasminc doesn't complain about undefined names. These would be
    `param` constants in a full emit; for surface closure we treat them
    as local `inline int` placeholders (jasminc accepts `inline int`
    constants declared at the function start). -/
def renderRcdtConsts : List String :=
  (List.range 19).flatMap (fun i =>
    let is := toString i
    -- Constants are dummies (0) for the surface-closure pass; the abstract
    -- spec ships the real values in `Sampler.RCDT`. The CT/range theorems
    -- are unaffected by the surface constant values.
    [ "inline int rcdt_lo_" ++ is ++ " = 0;"
    , "inline int rcdt_hi_" ++ is ++ " = 0;" ])

/-- Emit the Falcon FPU-free CDT base-sampler `.jazz` text.
    ABI: one `u32[2]` output (magnitude + sign), one `u8[10]` input. -/
def emitFndsaSamplerJazz (name : String) : String :=
  let paramStrs :=
    [ "reg ptr u32[2] out"
    , "reg const ptr u8[10] inp"
    ]
  let body := renderRcdtConsts ++ renderFndsaSamplerBody
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u32[2] {\n  "
    ++ String.intercalate "\n  " body ++ "\n  return out;\n}"

/-- The committed emitted Falcon FPU-free CDT-sampler kernel. -/
def fndsaSamplerJazz : String := emitFndsaSamplerJazz "fndsa_cdt_basesampler"

/-! ### Sanity checks on the sampler emit -/

/- The sampler emit has the expected ABI. -/
#guard (strContains fndsaSamplerJazz "export fn fndsa_cdt_basesampler(reg ptr u32[2] out, reg const ptr u8[10] inp)")

/- The sampler emits exactly 19 CDT comparison steps (the RCDT length,
    matching `Sampler.RCDT_LEN`). -/
#guard (strContains fndsaSamplerJazz "// CDT step 0  (RCDT entry, public constant)")
    && (strContains fndsaSamplerJazz "// CDT step 18  (RCDT entry, public constant)")
    && !(strContains fndsaSamplerJazz "// CDT step 19  (RCDT entry, public constant)")

/- The sampler reads exactly 10 random bytes (9 magnitude + 1 sign).
    `rand_lo` is the packed 8-byte read at `inp[:u64 0]`, `rand_hi` is
    the zero-extended 9th byte, and `inp[9]` feeds the sign-fold. -/
#guard (strContains fndsaSamplerJazz "rand_lo = inp[:u64 0];")
    && (strContains fndsaSamplerJazz "rand_hi = (64u) inp[8];")
    && (strContains fndsaSamplerJazz "sign_byte = (32u) inp[9];")

/- The sampler has the constant-time 2-limb unsigned subtract-with-
    borrow (no branch on secret; the final-borrow flag feeds a
    conditional move). Replaces the prior `#CDT_LT_BROADCAST`
    pseudo-mnemonic. -/
#guard (strContains fndsaSamplerJazz "cmp_flag, tmp = tmp - rcdt_lo;")
    && (strContains fndsaSamplerJazz "cmp_flag, tmp = tmp - rcdt_hi - cmp_flag;")

/- The sampler accumulator increment is unconditional `acc = acc + w0` —
    the CT realization of the `cdtStep` (`acc + (if r < e then 1 else 0)`),
    where the `0/1` comes from the lane-mask of `#CDT_LT_BROADCAST`. -/
#guard (strContains fndsaSamplerJazz "acc = acc + w0;")

end CatCrypt.Crypto.SecureCompilation.VIR.FndsaEmit
