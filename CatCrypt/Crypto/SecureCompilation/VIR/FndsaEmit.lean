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
# FN-DSA / Falcon `.jazz` text for two kernels

This module renders the Jasmin source text of two Falcon kernels:

1. **Falcon-512 verify polynomial subtraction `s1 = c − s2 · h`**, the
   per-coefficient step `(c, sh) ↦ c − sh mod q` at `q = 12289`, as 64 packed
   AVX2 stages (`emitFndsaVerifyJazz`).
2. **The FPU-free fixed-point CDT base sampler**, as 19 unrolled two-limb
   compare-and-accumulate steps (`emitFndsaSamplerJazz`).

Both texts are produced by `String` templates. They do not pass through the
verified front (`LowCT → Com → jasmin`), and no theorem relates either text to
a specification: not to `fndsaVerifyBlockSpec`, and not to
`Sampler.baseSampler` or `Sampler.fixedPointCDTGaussian`. In the sampler
text the 19 RCDT constants are placeholders rendered as `0`, and the random
value is read little-endian (`inp[:u64 0]` low, `inp[8]` high), whereas
`Sampler.packBytesBE` packs big-endian. The `#guard`s check substrings of the
rendered text.

## Main results

* `fndsa_verify_lane_map` — for any lane function `block`, the lane map
  `LaneMap.laneMap block lanes` equals `fun i => block (lanes i)`; a
  definitional identity about the Lean specification, not about the rendered
  text.
* The range bound of the Lean sampler function is
  `Sampler.fixedPointCDTGaussian_range`.

## Not stated in Lean

* Agreement of either rendered text with its specification.
* Constant time of either rendered text.
* The statistical-distance bound of the Falcon sampler.
* The NTRU-tree / fast Fourier sampling trapdoor and the polynomial
  multiplication `s2 · h`.

## ABI

* `fndsa_verify_lane`: `reg ptr u16[N] out, reg const ptr u16[2*N] inp`
  where `inp[0..N-1] = c`, `inp[N..2N-1] = s2h = s2 * h mod q`, and
  `out[k] = (c[k] - s2h[k]) mod q` (the per-coeff verify lane), as intended
  by the template; no theorem states it.
* `fndsa_cdt_basesampler`: `reg ptr u32[2] out, reg const ptr u8[10] inp`.

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

`fndsa_verify_lane_map` states that the lane map of a block function equals
its per-lane application, by `funext` and `rfl`. -/

/-- One verify lane carries one position's `(c[k], s2h[k])` pair. -/
abbrev FndsaVerifyLane := Zq × Zq

/-- The packed N-lane bundle of verify pairs (one per output coefficient). -/
abbrev FndsaVerifyBundle := Fin N → FndsaVerifyLane

/-- The per-lane verify-block function: take a `(c[k], s2h[k])` pair and
    return the verify-equation coefficient `c[k] - s2h[k]` in `Zq`. -/
def fndsaVerifyBlockSpec : FndsaVerifyLane → Zq := fun p => p.1 - p.2

/-! ## 3. The lane-map identity -/

/-- **Falcon-512 verify lane-map identity.** For any lane function `block`,
    the lane map `LaneMap.laneMap block lanes` equals the per-lane
    application `fun i => block (lanes i)`. The statement concerns Lean
    functions only; it says nothing about the rendered `.jazz` text. -/
theorem fndsa_verify_lane_map (block : FndsaVerifyLane → Zq)
    (lanes : FndsaVerifyBundle) :
    LaneMap.laneMap block lanes = (fun i => block (lanes i)) := by
  funext i
  rfl

/-! ## 4. Render the verify subtraction as `.jazz` (SIMD body)

The template renders one `#VPSUB_8u16` per 8 lanes (`u16` × 8 in one
`u128`), 64 stages for `N = 512` lanes, each followed by the correction
pair `#VPADD_8u16` / `#VPMINU_8u16` against a broadcast `q`-vector. -/

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
  -- as the branch-free form of `if orig < 0 then orig + q else orig` on u16.
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

/-! ## 5. Substring checks on the rendered verify text -/

/- The export has the expected FN-DSA verify ABI (`u16[512]` out, `u16[1032]`
    in: 512 × `c`, 512 × `s2h`, 8 × broadcast `q`). -/
#guard (strContains fndsaVerifyJazz "export fn fndsa_512_verify(reg ptr u16[512] out, reg const ptr u16[1032] inp)")

/- The body renders packed AVX2 subtraction (the verify lane operation,
    jasmin surface mnemonic `#VPSUB_8u16` = packed-sub of eight `u16` lanes). -/
#guard (strContains fndsaVerifyJazz "#VPSUB_8u16(")

/- The body renders the packed mod-q correction add (jasmin surface
    mnemonic `#VPADD_8u16`). -/
#guard (strContains fndsaVerifyJazz "#VPADD_8u16(")

/- The body renders the lane-wise unsigned minimum (the intended realization
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

/-! ## 6. Sampler text (FPU-free fixed-point CDT base sampler)

The template renders 19 unrolled compare-and-accumulate steps over a
two-limb random value `(rand_lo, rand_hi)`, each comparing against a
two-limb constant `(rcdt_lo_i, rcdt_hi_i)` by a subtract-with-borrow and a
conditional move. The constants are placeholders rendered as `0`
(`renderRcdtConsts`), so the text does not carry the table `Sampler.RCDT`.
No theorem relates the text to `Sampler.cdtStep` or `Sampler.baseSampler`. -/

/-- Render one CDT comparison step: a 2-limb subtract-with-borrow of the
    constant `(rcdt_lo_i, rcdt_hi_i)` from the random value
    `(rand_lo, rand_hi)`, whose final borrow flag selects `1` into `w0`,
    followed by `acc = acc + w0`. -/
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

/-- The CDT base-sampler body text: 19 unrolled compare-and-accumulate
    steps. The 9 random bytes are read into `(rand_lo, rand_hi)` as
    `rand_lo = inp[:u64 0]` (little-endian) and `rand_hi = (64u) inp[8]`;
    the 10th byte gives the sign bit. -/
def renderFndsaSamplerBody : List String :=
  let decls :=
    [ "reg u64 rand_lo rand_hi rcdt_lo rcdt_hi tmp;"
    , "reg u32 w0 acc sign_byte tmp32;"
    , "reg bool cmp_flag;" ]
  let init :=
    [ "acc = 0;"
    -- 8-byte read for the low limb of the random value
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

/-- The declarations of the 19 two-limb RCDT constants as `inline int`
    placeholders, every one rendered as `0`. The table values of
    `Sampler.RCDT` do not appear in the rendered text. -/
def renderRcdtConsts : List String :=
  (List.range 19).flatMap (fun i =>
    let is := toString i
    [ "inline int rcdt_lo_" ++ is ++ " = 0;"
    , "inline int rcdt_hi_" ++ is ++ " = 0;" ])

/-- The Falcon FPU-free CDT base-sampler `.jazz` text, rendered from the
    templates above. ABI: one `u32[2]` output (magnitude + sign), one
    `u8[10]` input. -/
def emitFndsaSamplerJazz (name : String) : String :=
  let paramStrs :=
    [ "reg ptr u32[2] out"
    , "reg const ptr u8[10] inp"
    ]
  let body := renderRcdtConsts ++ renderFndsaSamplerBody
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u32[2] {\n  "
    ++ String.intercalate "\n  " body ++ "\n  return out;\n}"

/-- The rendered Falcon FPU-free CDT-sampler text. -/
def fndsaSamplerJazz : String := emitFndsaSamplerJazz "fndsa_cdt_basesampler"

/-! ### Substring checks on the rendered sampler text -/

/- The sampler text has the expected ABI. -/
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

/- The sampler text contains the 2-limb subtract-with-borrow whose final
    borrow flag feeds a conditional move. -/
#guard (strContains fndsaSamplerJazz "cmp_flag, tmp = tmp - rcdt_lo;")
    && (strContains fndsaSamplerJazz "cmp_flag, tmp = tmp - rcdt_hi - cmp_flag;")

/- The sampler text contains the accumulator increment `acc = acc + w0`. -/
#guard (strContains fndsaSamplerJazz "acc = acc + w0;")

end CatCrypt.Crypto.SecureCompilation.VIR.FndsaEmit
