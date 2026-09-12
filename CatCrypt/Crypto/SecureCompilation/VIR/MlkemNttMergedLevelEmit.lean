/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit

/-!
# Merged-level transposed dual-zeta ML-KEM-768 forward NTT (16-lane AVX2)

The `LatticeNttEmit.emitMlkemNttFull16wayJazz` emit runs the three deepest
Cooley–Tukey layers (`len = 8, 4, 2`) as **within-vector** butterflies: the
butterfly partner is fetched from the same `u256` via `#VPERMQ`/`#VPSHUFB_256`,
so a 3-multiply `vfqmul` advances only 8 coefficients per call and half the lane
multiplies are the discarded partner half.

This module emits the alternative **merged-level transposed** structure: after
the two `len = 128` vector-pair layers, the six remaining layers
(`len = 64, 32, 16, 8, 4, 2`) run over one 128-coefficient half at a time, kept in
eight `u256` registers, with `#VPERM2I128`/`#VPUNPCK*`/`#VMOVSLDUP`/shift-blend
transposes (`__shuffle8/4/2/1`) re-aligning the butterfly partner into a paired
vector between layers. Each layer is then a full `__butterfly64x`
(four packed `#VPMULL_16u16` + four `#VPMULH_16u16` + a `reduce`, twelve
multiplies advancing 64 coefficients), and the deepest layer uses the packed
**dual-zeta** form (even/odd 128-bit halves carry independent zetas). The result
is 168 multiplies for the whole transform against the within-vector emit's 240.

The emitted body is the packed AVX2 forward NTT structure of the reference AVX2
Kyber/ML-KEM implementation (PQClean `ntt.S`, formosa-crypto `_poly_ntt`): the
`__butterfly64x`, `__shuffle8/4/2/1`, and `__red16x` helpers and the expanded
zeta table `jzetas_exp` are transcribed from that reference.

## Coefficient layout

The transform leaves its 256 output coefficients in the reference AVX2 order —
the vperm/vpunpck-permuted, Barrett-reduced order the reference `ntt_avx` and
`_poly_ntt` produce, which their matching `basemul`/`invntt` consume. It is a
fixed permutation (and no residual scale, the zetas being Montgomery-form) of the
standard `PQCLEAN_MLKEM768_CLEAN_ntt` order. A KEM wiring using this leaf must
consume that same order.

## What the Lean theorem here establishes

As with `LatticeNttEmit`, the Lean contribution is the **lane-independence** of
the packed butterfly (`mlkem_ntt_merged_lane_map`, a reuse of the
`mlkem_ntt_4way_lane_map` lemma): the packed form denotes the same value as the
per-lane block run sequentially, for any per-lane block. It does not establish the
NTT itself. The transform's NTT correctness is gated by the external bench
`bench/mlkem_compare/mlkem_ntt_avx2_bench.c`, which compares the emitted output,
position-for-position mod `q`, against the reference `PQCLEAN_MLKEM768_AVX2_ntt_avx`
(itself validated a coefficient-multiset match to `PQCLEAN_MLKEM768_CLEAN_ntt`),
and the emitted coefficient multiset against `PQCLEAN_MLKEM768_CLEAN_ntt`.

Axiom status of the theorem: `[propext, Quot.sound]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MlkemNttMergedLevelEmit

open CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit

/-! ## 1. The expanded zeta table (`jzetas_exp`, 400 × `u16`)

The packed/expanded zeta constants of the reference AVX2 ML-KEM forward NTT: for
each layer, the low-multiply (`zeta · qinv mod 2^16`) and high-multiply (`zeta`)
vectors, broadcast for the shallow layers and packed for the transposed deep
layers. Transcribed from the reference. -/

/-- The 400 `u16` values of `jzetas_exp`, in table order. -/
def jzetasExp : List Nat :=
  [ 31499, 31499, 2571, 2571, 14746, 14746, 2970, 2970, 13525, 13525, 13525, 13525, 13525, 13525, 13525, 13525,
    53134, 53134, 53134, 53134, 53134, 53134, 53134, 53134, 1493, 1493, 1493, 1493, 1493, 1493, 1493, 1493,
    1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 44630, 44630, 44630, 44630, 27758, 27758, 27758, 27758,
    61737, 61737, 61737, 61737, 49846, 49846, 49846, 49846, 3158, 3158, 3158, 3158, 622, 622, 622, 622,
    1577, 1577, 1577, 1577, 182, 182, 182, 182, 59709, 59709, 17364, 17364, 39176, 39176, 36479, 36479,
    5572, 5572, 64434, 64434, 21439, 21439, 39295, 39295, 573, 573, 2004, 2004, 264, 264, 383, 383,
    2500, 2500, 1458, 1458, 1727, 1727, 3199, 3199, 59847, 59020, 1497, 30967, 41972, 20179, 20711, 25081,
    52740, 26617, 16065, 53095, 9135, 64887, 39550, 27837, 1223, 652, 2777, 1015, 2036, 1491, 3047, 1785,
    516, 3321, 3009, 2663, 1711, 2167, 126, 1469, 65202, 54059, 33310, 20494, 37798, 945, 50654, 6182,
    32011, 10631, 29176, 36775, 47051, 17561, 51106, 60261, 2226, 555, 2078, 1550, 422, 177, 3038, 1574,
    3083, 1159, 2552, 2727, 1739, 2457, 418, 3173, 11182, 13387, 51303, 43881, 13131, 60950, 23093, 5493,
    33034, 30318, 46795, 12639, 20100, 18525, 19529, 52918, 430, 843, 871, 105, 587, 3094, 2869, 1653,
    778, 3182, 1483, 1119, 644, 349, 329, 3254, 788, 788, 1812, 1812, 28191, 28191, 28191, 28191,
    28191, 28191, 28191, 28191, 48842, 48842, 48842, 48842, 48842, 48842, 48842, 48842, 287, 287, 287, 287,
    287, 287, 287, 287, 202, 202, 202, 202, 202, 202, 202, 202, 10690, 10690, 10690, 10690,
    1359, 1359, 1359, 1359, 54335, 54335, 54335, 54335, 31164, 31164, 31164, 31164, 962, 962, 962, 962,
    2127, 2127, 2127, 2127, 1855, 1855, 1855, 1855, 1468, 1468, 1468, 1468, 37464, 37464, 24313, 24313,
    55004, 55004, 8800, 8800, 18427, 18427, 8859, 8859, 26676, 26676, 49374, 49374, 2648, 2648, 1017, 1017,
    732, 732, 608, 608, 1787, 1787, 411, 411, 3124, 3124, 1758, 1758, 19884, 37287, 49650, 56638,
    37227, 9076, 35338, 18250, 13427, 14017, 36381, 52780, 16832, 4312, 41381, 47622, 2476, 3239, 3058, 830,
    107, 1908, 3082, 2378, 2931, 961, 1821, 2604, 448, 2264, 677, 2054, 34353, 25435, 58154, 24392,
    44610, 10946, 24215, 16990, 10336, 57603, 43035, 10907, 31637, 28644, 23998, 48114, 817, 603, 1322, 1864,
    2114, 1218, 2455, 2142, 2144, 2051, 1819, 2459, 3221, 996, 958, 1522, 20297, 2146, 15356, 33152,
    59257, 50634, 54492, 14470, 44039, 45338, 23211, 48094, 41677, 45279, 7757, 23132, 1097, 610, 2044, 384,
    3193, 1994, 220, 1670, 1799, 794, 2475, 478, 3021, 991, 1869, 1628, 0, 0, 0, 0 ]

/-- Render a `u16[n]` jasmin global-array declaration from a `List Nat`. -/
def renderU16Global (name : String) (vals : List Nat) : String :=
  "u16[" ++ toString vals.length ++ "] " ++ name ++ " = {"
    ++ String.intercalate ", " (vals.map toString) ++ "};"

/-! ## 2. Inline helpers (butterfly, transposes, Barrett reduce) -/

/-- The packed dual-zeta Cooley–Tukey butterfly over four `u256` low/high pairs:
    `zl0/zh0` twiddle the first two high vectors, `zl1/zh1` the second two. Eight
    lane multiplies (`#VPMULL_16u16` × 4, `#VPMULH_16u16` × 4) plus the four
    quotient `#VPMULH_16u16(·, q)` — twelve multiplies advancing 64 coefficients. -/
def renderButterfly64x : List String :=
  [ "inline fn __butterfly64x("
      ++ "reg u256 rl0 rl1 rl2 rl3 rh0 rh1 rh2 rh3 zl0 zl1 zh0 zh1 qx16)"
  , "    -> reg u256, reg u256, reg u256, reg u256, reg u256, reg u256, reg u256, reg u256 {"
  , "  reg u256 t0 t1 t2 t3 t4 t5 t6 t7;"
  , "  t0 = #VPMULL_16u16(zl0, rh0);"
  , "  t1 = #VPMULH_16u16(zh0, rh0);"
  , "  t2 = #VPMULL_16u16(zl0, rh1);"
  , "  t3 = #VPMULH_16u16(zh0, rh1);"
  , "  t4 = #VPMULL_16u16(zl1, rh2);"
  , "  t5 = #VPMULH_16u16(zh1, rh2);"
  , "  t6 = #VPMULL_16u16(zl1, rh3);"
  , "  t7 = #VPMULH_16u16(zh1, rh3);"
  , "  t0 = #VPMULH_16u16(t0, qx16);"
  , "  t2 = #VPMULH_16u16(t2, qx16);"
  , "  t4 = #VPMULH_16u16(t4, qx16);"
  , "  t6 = #VPMULH_16u16(t6, qx16);"
  , "  rh1 = #VPSUB_16u16(rl1, t3);"
  , "  rl1 = #VPADD_16u16(t3, rl1);"
  , "  rh0 = #VPSUB_16u16(rl0, t1);"
  , "  rl0 = #VPADD_16u16(t1, rl0);"
  , "  rh3 = #VPSUB_16u16(rl3, t7);"
  , "  rl3 = #VPADD_16u16(t7, rl3);"
  , "  rh2 = #VPSUB_16u16(rl2, t5);"
  , "  rl2 = #VPADD_16u16(t5, rl2);"
  , "  rh0 = #VPADD_16u16(t0, rh0);"
  , "  rl0 = #VPSUB_16u16(rl0, t0);"
  , "  rh1 = #VPADD_16u16(t2, rh1);"
  , "  rl1 = #VPSUB_16u16(rl1, t2);"
  , "  rh2 = #VPADD_16u16(t4, rh2);"
  , "  rl2 = #VPSUB_16u16(rl2, t4);"
  , "  rh3 = #VPADD_16u16(t6, rh3);"
  , "  rl3 = #VPSUB_16u16(rl3, t6);"
  , "  return rl0, rl1, rl2, rl3, rh0, rh1, rh2, rh3;"
  , "}" ]

/-- Barrett reduce of one `u256` of 16 `s16` lanes to the canonical range. -/
def renderRed16x : List String :=
  [ "inline fn __red16x(reg u256 r, reg u256 qx16, reg u256 vx16) -> reg u256 {"
  , "  reg u256 x;"
  , "  x = #VPMULH_16u16(r, vx16);"
  , "  x = #VPSRA_16u16(x, 10);"
  , "  x = #VPMULL_16u16(x, qx16);"
  , "  r = #VPSUB_16u16(r, x);"
  , "  return r;"
  , "}" ]

/-- The four transpose helpers aligning butterfly partners across `u256`
    registers: `__shuffle8` (cross-128 via `#VPERM2I128`), `__shuffle4`
    (qword via `#VPUNPCK*_4u64`), `__shuffle2` (dword via `#VMOVSLDUP`/shift +
    blend), `__shuffle1` (word via 32-bit shift + `#VPBLEND_16u16`). -/
def renderShuffles : List String :=
  [ "inline fn __shuffle8(reg u256 a, reg u256 b) -> reg u256, reg u256 {"
  , "  reg u256 r0 r1;"
  , "  r0 = #VPERM2I128(a, b, 0x20);"
  , "  r1 = #VPERM2I128(a, b, 0x31);"
  , "  return r0, r1;"
  , "}"
  , "inline fn __shuffle4(reg u256 a, reg u256 b) -> reg u256, reg u256 {"
  , "  reg u256 r0 r1;"
  , "  r0 = #VPUNPCKL_4u64(a, b);"
  , "  r1 = #VPUNPCKH_4u64(a, b);"
  , "  return r0, r1;"
  , "}"
  , "inline fn __shuffle2(reg u256 a, reg u256 b) -> reg u256, reg u256 {"
  , "  reg u256 t0 t1;"
  , "  t0 = #VMOVSLDUP_256(b);"
  , "  t0 = #VPBLEND_8u32(a, t0, 0xAA);"
  , "  a = #VPSRL_4u64(a, 32);"
  , "  t1 = #VPBLEND_8u32(a, b, 0xAA);"
  , "  return t0, t1;"
  , "}"
  , "inline fn __shuffle1(reg u256 a, reg u256 b) -> reg u256, reg u256 {"
  , "  reg u256 r0 r1 t0 t1;"
  , "  t0 = #VPSLL_8u32(b, 16);"
  , "  r0 = #VPBLEND_16u16(a, t0, 0xAA);"
  , "  t1 = #VPSRL_8u32(a, 16);"
  , "  r1 = #VPBLEND_16u16(t1, b, 0xAA);"
  , "  return r0, r1;"
  , "}" ]

/-! ## 3. The merged-level forward NTT body -/

/-- The `_poly_ntt` body: two `len = 128` vector-pair butterfly blocks (over the
    two 128-coefficient halves), then a two-iteration loop over the halves running
    the merged `len = 64 … 2` layers with the `__shuffle*` transposes and the
    deepest `len = 2` dual-zeta layer, then the permuted store.

    `reduce = true` inserts a per-vector Barrett reduce (`__red16x`) before the
    store, bringing coefficients to the canonical range (matching the reference
    `_poly_ntt`); `reduce = false` leaves the output unreduced (matching the
    reference `ntt_avx`, whose consumer `basemul` reduces), saving the 32 reduce
    multiplies. -/
def renderMergedNttBody (reduce : Bool) : List String :=
  let redBlock : List String :=
    if reduce then
      [ ""
      , "    vx16 = jvx16[:u256 0];"
      , "    r0 = __red16x(r0, qx16, vx16);"
      , "    r4 = __red16x(r4, qx16, vx16);"
      , "    r2 = __red16x(r2, qx16, vx16);"
      , "    r6 = __red16x(r6, qx16, vx16);"
      , "    r1 = __red16x(r1, qx16, vx16);"
      , "    r5 = __red16x(r5, qx16, vx16);"
      , "    r3 = __red16x(r3, qx16, vx16);"
      , "    r7 = __red16x(r7, qx16, vx16);" ]
    else []
  [ "  reg u256 zeta0 zeta1 zeta2 zeta3 r0 r1 r2 r3 r4 r5 r6 r7 qx16 vx16;"
  , "  reg ptr u16[400] zetasp;"
  , "  inline int i;"
  , ""
  , "  zetasp = jzetas_exp;"
  , "  qx16 = jqx16[:u256 0];"
  , ""
  , "  zeta0 = #VPBROADCAST_8u32(zetasp[:u32 0]);"
  , "  zeta1 = #VPBROADCAST_8u32(zetasp[:u32 1]);"
  , ""
  , "  r0 = rp.[:u256 32*0];"
  , "  r1 = rp.[:u256 32*1];"
  , "  r2 = rp.[:u256 32*2];"
  , "  r3 = rp.[:u256 32*3];"
  , "  r4 = rp.[:u256 32*8];"
  , "  r5 = rp.[:u256 32*9];"
  , "  r6 = rp.[:u256 32*10];"
  , "  r7 = rp.[:u256 32*11];"
  , "  r0, r1, r2, r3, r4, r5, r6, r7 = __butterfly64x(r0, r1, r2, r3, r4, r5, r6, r7, zeta0, zeta0, zeta1, zeta1, qx16);"
  , "  rp.[:u256 32*0] = r0;"
  , "  rp.[:u256 32*1] = r1;"
  , "  rp.[:u256 32*2] = r2;"
  , "  rp.[:u256 32*3] = r3;"
  , "  rp.[:u256 32*8] = r4;"
  , "  rp.[:u256 32*9] = r5;"
  , "  rp.[:u256 32*10] = r6;"
  , "  rp.[:u256 32*11] = r7;"
  , ""
  , "  r0 = rp.[:u256 32*4];"
  , "  r1 = rp.[:u256 32*5];"
  , "  r2 = rp.[:u256 32*6];"
  , "  r3 = rp.[:u256 32*7];"
  , "  r4 = rp.[:u256 32*12];"
  , "  r5 = rp.[:u256 32*13];"
  , "  r6 = rp.[:u256 32*14];"
  , "  r7 = rp.[:u256 32*15];"
  , "  r0, r1, r2, r3, r4, r5, r6, r7 = __butterfly64x(r0, r1, r2, r3, r4, r5, r6, r7, zeta0, zeta0, zeta1, zeta1, qx16);"
  , "  rp.[:u256 32*12] = r4;"
  , "  rp.[:u256 32*13] = r5;"
  , "  rp.[:u256 32*14] = r6;"
  , "  rp.[:u256 32*15] = r7;"
  , ""
  , "  for i = 0 to 2 {"
  , "    // level 1 (len = 64)"
  , "    zeta0 = #VPBROADCAST_8u32(zetasp.[:u32 8 + 392*i]);"
  , "    zeta1 = #VPBROADCAST_8u32(zetasp.[:u32 12 + 392*i]);"
  , "    if (i == 0) {"
  , "      r4 = r0; r5 = r1; r6 = r2; r7 = r3;"
  , "    } else {"
  , "      r4 = rp.[:u256 32*4+256*i];"
  , "      r5 = rp.[:u256 32*5+256*i];"
  , "      r6 = rp.[:u256 32*6+256*i];"
  , "      r7 = rp.[:u256 32*7+256*i];"
  , "    }"
  , "    r0 = rp.[:u256 32*0+256*i];"
  , "    r1 = rp.[:u256 32*1+256*i];"
  , "    r2 = rp.[:u256 32*2+256*i];"
  , "    r3 = rp.[:u256 32*3+256*i];"
  , "    r0, r1, r2, r3, r4, r5, r6, r7 = __butterfly64x(r0, r1, r2, r3, r4, r5, r6, r7, zeta0, zeta0, zeta1, zeta1, qx16);"
  , ""
  , "    // level 2 (len = 32)"
  , "    zeta0 = zetasp.[:u256 16 + 392*i];"
  , "    zeta1 = zetasp.[:u256 48 + 392*i];"
  , "    r0, r4 = __shuffle8(r0, r4);"
  , "    r1, r5 = __shuffle8(r1, r5);"
  , "    r2, r6 = __shuffle8(r2, r6);"
  , "    r3, r7 = __shuffle8(r3, r7);"
  , "    r0, r4, r1, r5, r2, r6, r3, r7 = __butterfly64x(r0, r4, r1, r5, r2, r6, r3, r7, zeta0, zeta0, zeta1, zeta1, qx16);"
  , ""
  , "    // level 3 (len = 16)"
  , "    zeta0 = zetasp.[:u256 80 + 392*i];"
  , "    zeta1 = zetasp.[:u256 112 + 392*i];"
  , "    r0, r2 = __shuffle4(r0, r2);"
  , "    r4, r6 = __shuffle4(r4, r6);"
  , "    r1, r3 = __shuffle4(r1, r3);"
  , "    r5, r7 = __shuffle4(r5, r7);"
  , "    r0, r2, r4, r6, r1, r3, r5, r7 = __butterfly64x(r0, r2, r4, r6, r1, r3, r5, r7, zeta0, zeta0, zeta1, zeta1, qx16);"
  , ""
  , "    // level 4 (len = 8)"
  , "    zeta0 = zetasp.[:u256 144 + 392*i];"
  , "    zeta1 = zetasp.[:u256 176 + 392*i];"
  , "    r0, r1 = __shuffle2(r0, r1);"
  , "    r2, r3 = __shuffle2(r2, r3);"
  , "    r4, r5 = __shuffle2(r4, r5);"
  , "    r6, r7 = __shuffle2(r6, r7);"
  , "    r0, r1, r2, r3, r4, r5, r6, r7 = __butterfly64x(r0, r1, r2, r3, r4, r5, r6, r7, zeta0, zeta0, zeta1, zeta1, qx16);"
  , ""
  , "    // level 5 (len = 4)"
  , "    zeta0 = zetasp.[:u256 208 + 392*i];"
  , "    zeta1 = zetasp.[:u256 240 + 392*i];"
  , "    r0, r4 = __shuffle1(r0, r4);"
  , "    r1, r5 = __shuffle1(r1, r5);"
  , "    r2, r6 = __shuffle1(r2, r6);"
  , "    r3, r7 = __shuffle1(r3, r7);"
  , "    r0, r4, r1, r5, r2, r6, r3, r7 = __butterfly64x(r0, r4, r1, r5, r2, r6, r3, r7, zeta0, zeta0, zeta1, zeta1, qx16);"
  , ""
  , "    // level 6 (len = 2, packed dual-zeta)"
  , "    zeta0 = zetasp.[:u256 272 + 392*i];"
  , "    zeta2 = zetasp.[:u256 304 + 392*i];"
  , "    zeta1 = zetasp.[:u256 336 + 392*i];"
  , "    zeta3 = zetasp.[:u256 368 + 392*i];"
  , "    r0, r4, r2, r6, r1, r5, r3, r7 = __butterfly64x(r0, r4, r2, r6, r1, r5, r3, r7, zeta0, zeta1, zeta2, zeta3, qx16);" ]
  ++ redBlock ++
  [ ""
  , "    rp.[:u256 32*0+256*i] = r0;"
  , "    rp.[:u256 32*1+256*i] = r4;"
  , "    rp.[:u256 32*2+256*i] = r1;"
  , "    rp.[:u256 32*3+256*i] = r5;"
  , "    rp.[:u256 32*4+256*i] = r2;"
  , "    rp.[:u256 32*5+256*i] = r6;"
  , "    rp.[:u256 32*6+256*i] = r3;"
  , "    rp.[:u256 32*7+256*i] = r7;"
  , "  }" ]

/-- Emit the merged-level transposed dual-zeta ML-KEM-768 forward NTT `.jazz`.
    Self-contained: the expanded zeta table `jzetas_exp`, the modulus broadcast
    `jqx16`, and the Barrett constant `jvx16` are emitted as globals; the export
    takes only the in-place polynomial pointer. -/
def emitMlkemNttMergedLevelJazz (name : String) (reduce : Bool := false) : String :=
  String.intercalate "\n"
    ([ renderU16Global "jqx16" (List.replicate 16 3329) ]
     ++ (if reduce then [ renderU16Global "jvx16" (List.replicate 16 20159) ] else [])
     ++ [ renderU16Global "jzetas_exp" jzetasExp, "" ]
     ++ (if reduce then renderRed16x ++ [""] else [])
     ++ renderShuffles ++ [""] ++ renderButterfly64x ++ [""]
     ++ [ "export fn " ++ name ++ "(reg mut ptr u16[256] rp) -> reg mut ptr u16[256] {" ]
     ++ renderMergedNttBody reduce
     ++ [ "  return rp;", "}" ])

/-! ## 4. Denotation: lane-independence of the packed butterfly

The packed `__butterfly64x` applies its per-lane block independently across the
16 `s16` lanes of each `u256`; this reuses the `mlkem_ntt_4way_lane_map` lemma
(`LatticeNttEmit`) for its lane-independence. The NTT correctness of the
assembled transform is the external bench gate (module header). -/

/-- **Lane-independence of the merged-level packed butterfly** (NOT NTT
    correctness). A reuse of `mlkem_ntt_4way_lane_map`: applying any per-lane block
    to the packed lanes equals running it per lane. `[propext, Quot.sound]`. -/
theorem mlkem_ntt_merged_lane_map (block : MlkemNttLane → MlkemNttLane)
    (lanes : MlkemNtt4Way) :
    LaneMap.laneMap block lanes = (fun b => block (lanes b)) :=
  mlkem_ntt_4way_lane_map block lanes

set_option maxRecDepth 2000 in
/-- The zeta table has the expected length (400 `u16`). -/
theorem jzetasExp_length : jzetasExp.length = 400 := by rfl

end CatCrypt.Crypto.SecureCompilation.VIR.MlkemNttMergedLevelEmit
