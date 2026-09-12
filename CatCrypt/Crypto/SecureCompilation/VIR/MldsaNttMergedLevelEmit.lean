/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit

/-!
# Merged-level transposed dual-zeta ML-DSA-65 forward NTT (8-lane AVX2)

The `LatticeNttEmit.emitMldsaNttFull8wayJazz` emit runs the three deepest
Cooley–Tukey layers (`len = 4, 2, 1`) as **within-vector** butterflies: the
butterfly partner is fetched from the same `u256` via `#VPERMQ`/`#VPSHUFD_256`,
so a 6-multiply `dmont` advances only 8 coefficients per call and half the lane
multiplies are the discarded partner half.

This module emits the alternative **merged-level transposed** structure over
`ℤ_{8380417}` (23-bit prime, four `u32` lanes per `__m128i`, eight per `u256`):
after the two shallow layers (`len = 128, 64`, run as stride-4 vector-pair
butterflies over four groups), the six remaining layers
(`len = 32, 16, 8, 4, 2, 1`) run over one 64-coefficient quarter at a time, kept
in eight `u256` registers, with `#VPERM2I128`/`#VPUNPCK*`/`#VMOVSLDUP`/shift-blend
transposes (`shuffle8/4/2`) re-aligning the butterfly partner into a paired
vector between layers. Each layer is then a full vector-pair butterfly
(`dmont2` — six `#VPMUL_4u64` advancing 16 coefficients across two zeta groups),
and the three deepest layers (`len = 4, 2, 1`) use the packed **dual-zeta** form
(even/odd 32-bit lanes carry independent zetas, obtained by `#VPSRL_4u64` on the
`zeta·qinv` vector and `#VMOVSHDUP_256` on the `zeta` vector).

The emitted body is the packed AVX2 forward NTT structure of the reference
PQClean ML-DSA-65 implementation (`ntt.S`, `PQCLEAN_MLDSA65_AVX2_ntt_avx`): the
`butterfly` and `shuffle8/4/2` macros and the expanded zeta table `qdata`
(`_ZETAS`/`_ZETAS_QINV`) are transcribed from that reference, with the fused
`butterfly` split into the reused `dmont2` multiply plus a `#VPADD_8u32` /
`#VPSUB_8u32` combine.

## Coefficient layout

The transform leaves its 256 output coefficients in the reference AVX2 order —
the vperm/vpunpck-permuted, Montgomery-domain order the reference `ntt_avx`
produces (its consumer `poly_nttunpack` restores the natural order). It is a
fixed permutation, times the Montgomery factor `2³² mod q`, of the standard
`PQCLEAN_MLDSA65_CLEAN_ntt` order. A consumer using this leaf must consume that
same order (as PQClean's own `basemul` does).

## What the Lean theorem here establishes

As with `LatticeNttEmit`, the Lean contribution is the **lane-independence** of
the packed butterfly (`mldsa_ntt_merged_lane_map`, a reuse of the
`mldsa_ntt_4way_lane_map` lemma): the packed form denotes the same value as the
per-lane block run sequentially, for any per-lane block. It does not establish the
NTT itself. The transform's NTT correctness is gated by the external bench
`bench/mldsa_compare/mldsa_ntt_merged_bench.c`, which compares the emitted output,
position-for-position mod `q`, against the reference `PQCLEAN_MLDSA65_AVX2_ntt_avx`,
and the emitted coefficient multiset (mod `q`) against `PQCLEAN_MLDSA65_CLEAN_ntt`.

Axiom status of the theorem: `[propext, Quot.sound]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MldsaNttMergedLevelEmit

open CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit

/-! ## 1. The expanded zeta table (`qdata`, 624 × `u32`)

The packed/expanded constant table of the reference AVX2 ML-DSA forward NTT, in
`_8XQ` / `_8XQINV` / `_8XDIV_QINV` / `_8XDIV` / `_ZETAS_QINV` / `_ZETAS` order (the
`PQCLEAN_MLDSA65_AVX2_qdata` array). Each `int32` is stored as its `u32`
two's-complement value. The forward NTT reads `_8XQ` (element 0, the modulus
broadcast) and the `_ZETAS_QINV` (element 32) / `_ZETAS` (element 328) regions;
the remaining slots (`_8XDIV*`) serve the inverse transform and are carried for
layout fidelity. -/

/-- The 624 `u32` values of `qdata`, in table order. -/
def mldsaQdata : List Nat :=
  [ 8380417, 8380417, 8380417, 8380417, 8380417, 8380417, 8380417, 8380417,
    58728449, 58728449, 58728449, 58728449, 58728449, 58728449, 58728449, 58728449,
    4286571514, 4286571514, 4286571514, 4286571514, 4286571514, 4286571514, 4286571514, 4286571514,
    41978, 41978, 41978, 41978, 41978, 41978, 41978, 41978,
    4143920607, 1830765815, 2365092098, 2367190275, 1640767044, 1477910808, 1612161320, 1640734244,
    308362795, 308362795, 308362795, 308362795, 2479442219, 2479442219, 2479442219, 2479442219,
    2920293549, 2920293549, 2920293549, 2920293549, 3203396735, 3203396735, 3203396735, 3203396735,
    2365471349, 2365471349, 2365471349, 2365471349, 515185417, 515185417, 515185417, 515185417,
    4009269833, 4009269833, 4009269833, 4009269833, 625853735, 625853735, 625853735, 625853735,
    1727305304, 1727305304, 2082316400, 2082316400, 2929984932, 2929984932, 858240904, 858240904,
    1806278032, 1806278032, 222489248, 222489248, 3948214632, 3948214632, 684667771, 684667771,
    1654287830, 1654287830, 3416390375, 3416390375, 3037299959, 3037299959, 3546348696, 3546348696,
    329347125, 329347125, 1837364258, 1837364258, 2851951105, 2851951105, 3124553157, 3124553157,
    2448829031, 2663740960, 2890437837, 1838055109, 1594295555, 3217993772, 2396243924, 3700530863,
    4092966277, 3818983036, 3733539478, 1797021249, 3233154048, 2059733581, 2633455260, 3189990749,
    2544742973, 3393301206, 418987550, 1831915353, 2369610815, 992097815, 879957084, 2024403852,
    1484874664, 2658884506, 4009578358, 2311428179, 2799830324, 3344890928, 2580159828, 3342528301,
    2720048869, 1350681039, 2150987357, 1599739335, 3009113973, 3301961842, 2854179456, 568627424,
    3511832818, 3706177080, 289871779, 3032963693, 2135294594, 3276211771, 3405106141, 1665705315,
    1321868265, 1225434135, 2510335232, 666258756, 675310538, 2739026248, 2295461228, 2795485345,
    3599787116, 2919790274, 1777179795, 334803717, 4116200997, 3776715076, 1957047970, 1146323031,
    3640183937, 2320807961, 1651689966, 140455867, 3255555954, 1955560694, 1529189038, 2163945418,
    4047609477, 1518161567, 4208002123, 1708872713, 1787797779, 1638590967, 4174321108, 2625006690,
    3378645744, 1155548552, 2143745726, 1210558298, 3033505406, 3976620480, 628664287, 2565662728,
    1422575624, 1424130038, 3109636832, 235321234, 168022240, 1206536194, 985155484, 3400906713,
    4294068883, 2931507058, 3689067253, 2027833504, 14253662, 1014493059, 863641633, 1819892093,
    2124962073, 3071365863, 2374500069, 2657181980, 2758378776, 694382729, 235104446, 3249905124,
    831969619, 3994518533, 756955444, 4034654491, 1554794072, 1339088280, 2254908606, 3441491109,
    2247696700, 2571150583, 2703367493, 3854143128, 1119856484, 1544891539, 155290192, 3321189834,
    991903578, 912367099, 4250273159, 1176904444, 3873414682, 3476595338, 1747917558, 3969039574,
    908452108, 1851023419, 3118215577, 2940438916, 4222276798, 3980682559, 985022747, 963438279,
    3216007321, 604552167, 3273017868, 608791570, 173440395, 2168875160, 2978348060, 3255596954,
    6087993, 4184841204, 565464272, 2536867379, 2694037935, 879867909, 2485210924, 400711272,
    1363007700, 30313375, 3968541936, 1683520342, 3777667302, 2027935492, 2922348676, 128353682,
    3171085633, 137583815, 3659512378, 3652194385, 45766801, 671509323, 2224365118, 419615363,
    1216882040, 4024376808, 3018162168, 371462360, 2937869239, 3910808763, 827959816, 3698622823,
    702390549, 4015461863, 4034542766, 4223092186, 3086300125, 2795363370, 2036925262, 3754546870,
    746144248, 2874008610, 2032221021, 1904936414, 1257750362, 1926727420, 1931587462, 1258381762,
    885133339, 1629985060, 1967222129, 6363718, 3007044496, 1136965286, 1779436847, 1116720494,
    1042326957, 1405999311, 713994583, 940195359, 2752470159, 2061661095, 3411811697, 1726753853,
    2747014592, 394851342, 283780712, 776003547, 1123958025, 201262505, 1934038751, 374860238,
    4290991583, 25847, 4292358402, 4294448387, 237124, 4294189336, 4294091048, 466468,
    1826347, 1826347, 1826347, 1826347, 2353451, 2353451, 2353451, 2353451,
    4294608045, 4294608045, 4294608045, 4294608045, 4292875391, 4292875391, 4292875391, 4292875391,
    3119733, 3119733, 3119733, 3119733, 4292082441, 4292082441, 4292082441, 4292082441,
    3111497, 3111497, 3111497, 3111497, 2680103, 2680103, 2680103, 2680103,
    2725464, 2725464, 1024112, 1024112, 4293887396, 4293887396, 3585928, 3585928,
    4294417808, 4294417808, 4293847712, 4293847712, 2619752, 2619752, 4292858747, 4292858747,
    4292849110, 4292849110, 4291107559, 4291107559, 4293567735, 4293567735, 4291689624, 4291689624,
    1757237, 1757237, 4294947874, 4294947874, 4010497, 4010497, 280005, 280005,
    2706023, 95776, 3077325, 3530437, 4293305603, 4291375148, 4292429780, 3915439,
    4291106181, 4291923580, 3574422, 4292099649, 3539968, 4294666829, 2348700, 4294427997,
    4293268029, 4293323478, 3505694, 4291145561, 3507263, 4292826647, 4293366876, 3699596,
    811944, 531354, 954230, 3881043, 3900724, 4292410416, 2071892, 4292169517,
    4291036901, 4291289551, 4293514845, 2176455, 4293709685, 4290883698, 4291777152, 4291334368,
    3412210, 2147896, 4291999651, 4294556269, 4294296194, 4294944315, 4294585309, 1852771,
    4291623913, 508951, 44288, 904516, 4291242954, 1653064, 2389356, 759969,
    189548, 3159746, 4292557971, 1315589, 1285669, 4294154564, 4291948194, 4291338327,
    4293438593, 4291926041, 3475950, 4293382075, 1939314, 4293967094, 4291809966, 126922,
    4293983877, 2715295, 4291273803, 4292490249, 4293738771, 4293659127, 1349076, 4293536866,
    264944, 3097992, 4293867198, 3958618, 4294958718, 4291717568, 4294756319, 4293650440,
    4291414024, 4293115894, 4294789856, 1341330, 4293382368, 4293527554, 4291086236, 3839961,
    2091667, 4291624818, 266997, 4291446944, 900702, 495491, 4294311969, 4291410301,
    342297, 3437287, 2842341, 4055324, 4291200280, 4291973257, 4293634238, 4294516196,
    4293687635, 1500165, 4294424884, 4292383003, 4292953688, 1957272, 4291783870, 810149,
    4291928380, 2213111, 4294540613, 4293299864, 4292028260, 183443, 4294412880, 3937738,
    3407706, 2244091, 2434439, 4291207932, 1859098, 4293354122, 4291844854, 4294442198,
    286988, 4291625019, 2691481, 1247620, 1250494, 1869119, 1237275, 1312455,
    1917081, 777191, 4292135436, 4291243026, 2432395, 3369112, 162844, 1652634,
    3523897, 4293991412, 1723600, 4293862963, 4292731311, 4293990405, 3919660, 1400424,
    2316500, 4292520863, 4293731568, 4293770070, 909542, 4294924036, 2031748, 4294198674,
    4292529473, 1735879, 4292377146, 2486353, 2635921, 1903435, 4291649086, 3306115,
    4292420984, 2235880, 4293296120, 594136, 2454455, 185531, 1616392, 4291273063,
    3866901, 1717735, 4293164206, 4294706650, 4294546397, 1612842, 4294918990, 4294121142,
    3817976, 4291404834, 3513181, 4291773918, 819034, 4294444796, 3207046, 4291371458,
    4108315, 203044, 1265009, 1595974, 4291419024, 4293916326, 4293537071, 4293004654,
    4293592493, 3406031, 4293120343, 4291190303, 4294802575, 4293759911, 3014001, 4293168189,
    269760, 472078, 1910376, 4291133403, 4292680969, 4291421609, 4293605087, 1976782 ]

/-- Render a `u32[n]` jasmin global-array declaration from a `List Nat`. -/
def renderU32Global (name : String) (vals : List Nat) : String :=
  "u32[" ++ toString vals.length ++ "] " ++ name ++ " = {"
    ++ String.intercalate ", " (vals.map toString) ++ "};"

/-! ## 2. Inline helpers (butterfly, transposes) -/

/-- The fused dual-zeta Cooley–Tukey butterfly `(l, h) ↦ (l + t, l − t)` with
    `t = montgomery_reduce(zeta · h)`: the reused `dmont2` supplies the packed
    dual-zeta Montgomery multiply (even lanes twiddled by `(zl0, zh0)`, odd lanes
    by `(zl1, zh1)`), then a `#VPADD_8u32` / `#VPSUB_8u32` combine. -/
def renderBfly : List String :=
  [ "inline fn bfly("
      ++ "reg u256 l, reg u256 h, reg u256 zl0, reg u256 zl1, reg u256 zh0, reg u256 zh1, reg u256 vq)"
  , "    -> reg u256, reg u256 {"
  , "  reg u256 t;"
  , "  t = dmont2(h, zl0, zl1, zh0, zh1, vq);"
  , "  h = #VPSUB_8u32(l, t);"
  , "  l = #VPADD_8u32(l, t);"
  , "  return l, h;"
  , "}" ]

/-- The three transpose helpers aligning butterfly partners across `u256`
    registers: `shuffle8` (cross-128 via `#VPERM2I128`), `shuffle4` (qword via
    `#VPUNPCK*_4u64`), `shuffle2` (dword via `#VMOVSLDUP`/shift + blend). -/
def renderShuffles : List String :=
  [ "inline fn shuffle8(reg u256 a, reg u256 b) -> reg u256, reg u256 {"
  , "  reg u256 r0 r1;"
  , "  r0 = #VPERM2I128(a, b, 0x20);"
  , "  r1 = #VPERM2I128(a, b, 0x31);"
  , "  return r0, r1;"
  , "}"
  , "inline fn shuffle4(reg u256 a, reg u256 b) -> reg u256, reg u256 {"
  , "  reg u256 r0 r1;"
  , "  r0 = #VPUNPCKL_4u64(a, b);"
  , "  r1 = #VPUNPCKH_4u64(a, b);"
  , "  return r0, r1;"
  , "}"
  , "inline fn shuffle2(reg u256 a, reg u256 b) -> reg u256, reg u256 {"
  , "  reg u256 t0 t1 aa;"
  , "  t0 = #VMOVSLDUP_256(b);"
  , "  t0 = #VPBLEND_8u32(a, t0, 0xAA);"
  , "  aa = #VPSRL_4u64(a, 32);"
  , "  t1 = #VPBLEND_8u32(aa, b, 0xAA);"
  , "  return t0, t1;"
  , "}" ]

/-! ## 3. The merged-level forward NTT body

The body follows the reference `ntt.S` register schedule. `renderLevels0t1`
runs the two shallow layers (`len = 128, 64`) as a stride-4 vector-pair sweep
over four groups (`off = 0, 1, 2, 3`, group `off` covering `u256` slots
`off, 4+off, …, 28+off`). `renderLevels2t7` runs the six deep layers
(`len = 32 … 1`) over the four contiguous 64-coefficient quarters
(`off = 0, 1, 2, 3`, quarter `off` covering `u256` slots `8·off … 8·off+7`),
with a transpose between layers and the packed dual-zeta form at the three
deepest layers. The `zeta·qinv` region (`_ZETAS_QINV`) sits at `u32` element 32,
the `zeta` region (`_ZETAS`) at element 328; `u256`-aligned layer zetas index
`qd[:u256 k]` (element `8k`), per-butterfly broadcasts index `qd[:u32 e]`. -/

/-- A single-zeta butterfly call line (`zl0 = zl1`, `zh0 = zh1`). -/
def bflyLine (lo hi : String) : String :=
  lo ++ ", " ++ hi ++ " = bfly(" ++ lo ++ ", " ++ hi ++ ", zl, zl, zh, zh, vq);"

/-- A dual-zeta butterfly call line (split `zl1 = zl>>32`, `zh1 = movshdup zh`). -/
def bflyLine2 (lo hi : String) : String :=
  lo ++ ", " ++ hi ++ " = bfly(" ++ lo ++ ", " ++ hi ++ ", zl, zl1, zh, zh1, vq);"

/-- A shuffle call line `outLo, outHi = shuffleN(inA, inB);`. -/
def shufLine (op outLo outHi inA inB : String) : String :=
  outLo ++ ", " ++ outHi ++ " = " ++ op ++ "(" ++ inA ++ ", " ++ inB ++ ");"

/-- Load a `u256`-aligned zeta pair for a deep layer: `zl` is the actual
    multiplier `zeta` (`_ZETAS`), `zh` the Montgomery-quotient multiplier
    `zeta·qinv` (`_ZETAS_QINV`) — the argument convention `dmont2` expects. -/
def loadZetaVec (qinvBase zetaBase off : Nat) : List String :=
  [ "zl = qd[:u256 " ++ toString ((328 + zetaBase + 8 * off) / 8) ++ "];"
  , "zh = qd[:u256 " ++ toString ((32 + qinvBase + 8 * off) / 8) ++ "];" ]

/-- Split the loaded zeta pair into its odd-lane partners for the dual-zeta form:
    the odd `zeta` lanes via `#VMOVSHDUP_256`, the odd `zeta·qinv` lanes via
    `#VPSRL_4u64` by 32. -/
def splitZeta : List String :=
  [ "zl1 = #VMOVSHDUP_256(zl);"
  , "zh1 = #VPSRL_4u64(zh, 32);" ]

/-- Broadcast a single zeta pair to all lanes: `zl = zeta` (`_ZETAS + e`),
    `zh = zeta·qinv` (`_ZETAS_QINV + e`). -/
def bcastZeta (e : Nat) : List String :=
  [ "zl = #VPBROADCAST_8u32(qd[:u32 " ++ toString (328 + e) ++ "]);"
  , "zh = #VPBROADCAST_8u32(qd[:u32 " ++ toString (32 + e) ++ "]);" ]

/-- The two shallow layers (`len = 128, 64`) for group `off` (0..3): a stride-4
    vector-pair sweep over `u256` slots `off, 4+off, …, 28+off`. -/
def renderLevels0t1 (off : Nat) : List String :=
  let idx (k : Nat) : String := toString (k + off)
  let load : List String :=
    [ "y4  = rp[:u256 " ++ idx 0  ++ "];"
    , "y5  = rp[:u256 " ++ idx 4  ++ "];"
    , "y6  = rp[:u256 " ++ idx 8  ++ "];"
    , "y7  = rp[:u256 " ++ idx 12 ++ "];"
    , "y8  = rp[:u256 " ++ idx 16 ++ "];"
    , "y9  = rp[:u256 " ++ idx 20 ++ "];"
    , "y10 = rp[:u256 " ++ idx 24 ++ "];"
    , "y11 = rp[:u256 " ++ idx 28 ++ "];" ]
  let level0 : List String :=
    bcastZeta 1 ++ [ bflyLine "y4" "y8", bflyLine "y5" "y9", bflyLine "y6" "y10", bflyLine "y7" "y11" ]
  let level1 : List String :=
    bcastZeta 2 ++ [ bflyLine "y4" "y6", bflyLine "y5" "y7" ]
      ++ bcastZeta 3 ++ [ bflyLine "y8" "y10", bflyLine "y9" "y11" ]
  let store : List String :=
    [ "rp[:u256 " ++ idx 0  ++ "] = y4;"
    , "rp[:u256 " ++ idx 4  ++ "] = y5;"
    , "rp[:u256 " ++ idx 8  ++ "] = y6;"
    , "rp[:u256 " ++ idx 12 ++ "] = y7;"
    , "rp[:u256 " ++ idx 16 ++ "] = y8;"
    , "rp[:u256 " ++ idx 20 ++ "] = y9;"
    , "rp[:u256 " ++ idx 24 ++ "] = y10;"
    , "rp[:u256 " ++ idx 28 ++ "] = y11;" ]
  [ "// ==== levels 0t1 (len 128, 64), group " ++ toString off ++ " ====" ]
    ++ load ++ [ "// level 0 (len = 128)" ] ++ level0
    ++ [ "// level 1 (len = 64)" ] ++ level1 ++ store

/-- The six deep layers (`len = 32 … 1`) for quarter `off` (0..3): eight
    contiguous `u256` slots `8·off … 8·off+7`, with `shuffle8/4/2` transposes
    and the packed dual-zeta form at `len = 4, 2, 1`. -/
def renderLevels2t7 (off : Nat) : List String :=
  let base := 8 * off
  let slot (k : Nat) : String := toString (base + k)
  let load : List String :=
    [ "y4  = rp[:u256 " ++ slot 0 ++ "];"
    , "y5  = rp[:u256 " ++ slot 1 ++ "];"
    , "y6  = rp[:u256 " ++ slot 2 ++ "];"
    , "y7  = rp[:u256 " ++ slot 3 ++ "];"
    , "y8  = rp[:u256 " ++ slot 4 ++ "];"
    , "y9  = rp[:u256 " ++ slot 5 ++ "];"
    , "y10 = rp[:u256 " ++ slot 6 ++ "];"
    , "y11 = rp[:u256 " ++ slot 7 ++ "];" ]
  let level2 : List String :=
    [ "// level 2 (len = 32)" ] ++ bcastZeta (4 + off)
      ++ [ bflyLine "y4" "y8", bflyLine "y5" "y9", bflyLine "y6" "y10", bflyLine "y7" "y11"
         , shufLine "shuffle8" "y3" "y8" "y4" "y8"
         , shufLine "shuffle8" "y4" "y9" "y5" "y9"
         , shufLine "shuffle8" "y5" "y10" "y6" "y10"
         , shufLine "shuffle8" "y6" "y11" "y7" "y11" ]
  let level3 : List String :=
    [ "// level 3 (len = 16)" ] ++ loadZetaVec 8 8 off
      ++ [ bflyLine "y3" "y5", bflyLine "y8" "y10", bflyLine "y4" "y6", bflyLine "y9" "y11"
         , shufLine "shuffle4" "y7" "y5" "y3" "y5"
         , shufLine "shuffle4" "y3" "y10" "y8" "y10"
         , shufLine "shuffle4" "y8" "y6" "y4" "y6"
         , shufLine "shuffle4" "y4" "y11" "y9" "y11" ]
  let level4 : List String :=
    [ "// level 4 (len = 8)" ] ++ loadZetaVec 40 40 off
      ++ [ bflyLine "y7" "y8", bflyLine "y5" "y6", bflyLine "y3" "y4", bflyLine "y10" "y11"
         , shufLine "shuffle2" "y9" "y8" "y7" "y8"
         , shufLine "shuffle2" "y7" "y6" "y5" "y6"
         , shufLine "shuffle2" "y5" "y4" "y3" "y4"
         , shufLine "shuffle2" "y3" "y11" "y10" "y11" ]
  let level5 : List String :=
    [ "// level 5 (len = 4, dual-zeta)" ] ++ loadZetaVec 72 72 off ++ splitZeta
      ++ [ bflyLine2 "y9" "y5", bflyLine2 "y8" "y4", bflyLine2 "y7" "y3", bflyLine2 "y6" "y11" ]
  let level6 : List String :=
    [ "// level 6 (len = 2, dual-zeta)" ] ++ loadZetaVec 104 104 off ++ splitZeta
      ++ [ bflyLine2 "y9" "y7", bflyLine2 "y8" "y6" ]
      ++ loadZetaVec 136 136 off ++ splitZeta
      ++ [ bflyLine2 "y5" "y3", bflyLine2 "y4" "y11" ]
  let level7 : List String :=
    [ "// level 7 (len = 1, dual-zeta)" ] ++ loadZetaVec 168 168 off ++ splitZeta
      ++ [ bflyLine2 "y9" "y8" ]
      ++ loadZetaVec 200 200 off ++ splitZeta ++ [ bflyLine2 "y7" "y6" ]
      ++ loadZetaVec 232 232 off ++ splitZeta ++ [ bflyLine2 "y5" "y4" ]
      ++ loadZetaVec 264 264 off ++ splitZeta ++ [ bflyLine2 "y3" "y11" ]
  let store : List String :=
    [ "rp[:u256 " ++ slot 0 ++ "] = y9;"
    , "rp[:u256 " ++ slot 1 ++ "] = y8;"
    , "rp[:u256 " ++ slot 2 ++ "] = y7;"
    , "rp[:u256 " ++ slot 3 ++ "] = y6;"
    , "rp[:u256 " ++ slot 4 ++ "] = y5;"
    , "rp[:u256 " ++ slot 5 ++ "] = y4;"
    , "rp[:u256 " ++ slot 6 ++ "] = y3;"
    , "rp[:u256 " ++ slot 7 ++ "] = y11;" ]
  [ "// ==== levels 2t7 (len 32..1), quarter " ++ toString off ++ " ====" ]
    ++ load ++ level2 ++ level3 ++ level4 ++ level5 ++ level6 ++ level7 ++ store

/-- The merged-level forward NTT body: register declarations, the `qdata` pointer
    and modulus broadcast, then the four `levels0t1` groups and four `levels2t7`
    quarters. -/
def renderMergedNttBody : List String :=
  [ "  reg u256 vq y3 y4 y5 y6 y7 y8 y9 y10 y11 zl zh zl1 zh1;"
  , "  reg ptr u32[624] qd;"
  , ""
  , "  qd = mldsa_qdata;"
  , "  vq = qd[:u256 0];"
  , "" ]
  ++ (List.range 4).flatMap (fun off => renderLevels0t1 off ++ [""])
  ++ (List.range 4).flatMap (fun off => renderLevels2t7 off ++ [""])

/-- Emit the merged-level transposed dual-zeta ML-DSA-65 forward NTT `.jazz`.
    Self-contained: the expanded zeta table `mldsa_qdata` is emitted as a global;
    the export takes only the in-place polynomial pointer. Reuses `dmont2`
    (`LatticeNttEmit`) as the dual-zeta Montgomery multiply core. -/
def emitMldsaNttMergedLevelJazz (name : String) : String :=
  String.intercalate "\n"
    ([ renderU32Global "mldsa_qdata" mldsaQdata, "" ]
     ++ renderDmont2 ++ [""] ++ renderShuffles ++ [""] ++ renderBfly ++ [""]
     ++ [ "export fn " ++ name ++ "(reg mut ptr u32[256] rp) -> reg mut ptr u32[256] {" ]
     ++ renderMergedNttBody
     ++ [ "  return rp;", "}" ])

/-! ## 4. Denotation: lane-independence of the packed butterfly

The packed `bfly` applies its per-lane block independently across the eight
`s32` lanes of each `u256`; this reuses the `mldsa_ntt_4way_lane_map` lemma
(`LatticeNttEmit`) for its lane-independence. The NTT correctness of the
assembled transform is the external bench gate (module header). -/

/-- **Lane-independence of the merged-level packed butterfly** (NOT NTT
    correctness). A reuse of `mldsa_ntt_4way_lane_map`: applying any per-lane
    block to the packed lanes equals running it per lane. `[propext, Quot.sound]`. -/
theorem mldsa_ntt_merged_lane_map (block : MldsaNttLane → MldsaNttLane)
    (lanes : MldsaNtt4Way) :
    LaneMap.laneMap block lanes = (fun b => block (lanes b)) :=
  mldsa_ntt_4way_lane_map block lanes

set_option maxRecDepth 4000 in
/-- The zeta table has the expected length (624 `u32`). -/
theorem mldsaQdata_length : mldsaQdata.length = 624 := by rfl

/-! ## 5. Structural sanity checks on the emitted text -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- The emitted merged-level ML-DSA-65 NTT text. -/
def mldsaNttMergedJazz : String := emitMldsaNttMergedLevelJazz "dsa_ntt_merged"

/- The merged export has the expected in-place ABI (256 u32 in place). -/
#guard (strContains mldsaNttMergedJazz "export fn dsa_ntt_merged(reg mut ptr u32[256] rp) -> reg mut ptr u32[256]")

/- The merged body carries the reused dual-zeta Montgomery multiply (`dmont2`)
    and the fused butterfly (`bfly`). -/
#guard (strContains mldsaNttMergedJazz "inline fn dmont2(")
    && (strContains mldsaNttMergedJazz "inline fn bfly(")

/- The merged body carries the three transpose helpers. -/
#guard (strContains mldsaNttMergedJazz "inline fn shuffle8(")
    && (strContains mldsaNttMergedJazz "inline fn shuffle4(")
    && (strContains mldsaNttMergedJazz "inline fn shuffle2(")

/- The merged body renders all 8 Cooley–Tukey layers (`len = 128 … 1`). -/
#guard (strContains mldsaNttMergedJazz "// level 0 (len = 128)")
    && (strContains mldsaNttMergedJazz "// level 1 (len = 64)")
    && (strContains mldsaNttMergedJazz "// level 2 (len = 32)")
    && (strContains mldsaNttMergedJazz "// level 3 (len = 16)")
    && (strContains mldsaNttMergedJazz "// level 4 (len = 8)")
    && (strContains mldsaNttMergedJazz "// level 5 (len = 4, dual-zeta)")
    && (strContains mldsaNttMergedJazz "// level 6 (len = 2, dual-zeta)")
    && (strContains mldsaNttMergedJazz "// level 7 (len = 1, dual-zeta)")

/- The deepest layers use the packed dual-zeta split (`#VMOVSHDUP_256` on the
    `zeta` vector, `#VPSRL_4u64` on the `zeta·qinv` vector). -/
#guard (strContains mldsaNttMergedJazz "zl1 = #VMOVSHDUP_256(zl);")
    && (strContains mldsaNttMergedJazz "zh1 = #VPSRL_4u64(zh, 32);")

end CatCrypt.Crypto.SecureCompilation.VIR.MldsaNttMergedLevelEmit
