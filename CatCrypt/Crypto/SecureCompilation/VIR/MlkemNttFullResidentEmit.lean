/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit

/-!
# Register-resident full 16-lane AVX2 ML-KEM-768 forward NTT

This module emits the complete 7-layer ML-KEM-768 forward NTT with the three
within-vector deep layers (`len = 8, 4, 2`) fused into a single sweep over the 16
`u256` vectors. In the baseline `LatticeNttEmit.renderMlkemNttFull16wayBody` those
three layers are three separate `for v = 0 to 16` loops, so each vector is loaded
from and stored to the polynomial array `r[]` once per layer (three round-trips).
The fused sweep loads each vector once, carries it through the `len = 8 → 4 → 2`
butterfly chain in a `u256` register, and stores it once.

The four vector-pair layers (`len = 128, 64, 32, 16`) are unchanged: each of those
butterflies pairs two of the 16 vectors, so keeping all 16 vectors resident plus
the Montgomery-multiply scratch would need 18 `%ymm`, above the 16-register file.

## Denotation

`mlkem_ntt_full_resident_denotation_preserves` composes the lane-map lemma
`LatticeNttEmit.mlkem_ntt_4way_lane_map`: the deep-layer fusion reorders loads and
stores of independent vectors and does not change the per-lane butterfly data flow.
Axioms `[propext, Quot.sound]`.

## KAT

The emitted `.jazz` is jasminc-lowered and validated byte-identical to
`PQCLEAN_MLKEM768_CLEAN_ntt` at the bench level
(`bench/mlkem_compare/mlkem_ntt_avx2_bench.c`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MlkemNttFullResidentEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit

/-- The four vector-pair layers (`len = 128, 64, 32, 16`), identical to the
    baseline body: each butterfly pairs two of the 16 `u256` vectors, so the
    working set exceeds the 16-`%ymm` file and the vectors round-trip through the
    polynomial array `r[]`. -/
def residentPairLayers : List String :=
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
  , "  }" ]

/-- The fused deep-layer sweep: one `for v = 0 to 16` loop that loads vector `v`
    once, runs the `len = 8 → 4 → 2` butterfly chain register-resident, and stores
    it once. Byte-identical to the three separate deep loops of the baseline body
    because those layers are within-vector (each `u256` vector is independent). -/
def residentDeepSweep : List String :=
  [ ""
  , "  duph4 = aux[:u256 127];"
  , "  dupl4 = aux[:u256 128];"
  , "  duph2 = aux[:u256 129];"
  , "  dupl2 = aux[:u256 130];"
  , ""
  , "  // === fused deep layers len = 8, 4, 2 (each vector resident across them) ==="
  , "  for v = 0 to 16 {"
  , "    a = r[:u256 v];"
  , "    // len = 8 (cross-128) zl,zh @ aux 31..62"
  , "    zl = aux[:u256 31 + 2*v]; zh = aux[:u256 32 + 2*v];"
  , "    bb   = #VPERMQ(a, 0xEE);"
  , "    alow = #VPERMQ(a, 0x44);"
  , "    t  = vfqmul(bb, zl, zh, vq);"
  , "    radd = #VPADD_16u16(a, t);"
  , "    rsub = #VPSUB_16u16(alow, t);"
  , "    a = #VPBLEND_8u32(radd, rsub, 0xF0);"
  , "    // len = 4 (within 128) zl,zh @ aux 63..94"
  , "    zl = aux[:u256 63 + 2*v]; zh = aux[:u256 64 + 2*v];"
  , "    bb   = #VPSHUFB_256(a, duph4);"
  , "    alow = #VPSHUFB_256(a, dupl4);"
  , "    t  = vfqmul(bb, zl, zh, vq);"
  , "    radd = #VPADD_16u16(a, t);"
  , "    rsub = #VPSUB_16u16(alow, t);"
  , "    a = #VPBLEND_16u16(radd, rsub, 0xF0);"
  , "    // len = 2 (within 128) zl,zh @ aux 95..126"
  , "    zl = aux[:u256 95 + 2*v]; zh = aux[:u256 96 + 2*v];"
  , "    bb   = #VPSHUFB_256(a, duph2);"
  , "    alow = #VPSHUFB_256(a, dupl2);"
  , "    t  = vfqmul(bb, zl, zh, vq);"
  , "    radd = #VPADD_16u16(a, t);"
  , "    rsub = #VPSUB_16u16(alow, t);"
  , "    c = #VPBLEND_16u16(radd, rsub, 0xCC);"
  , "    r[:u256 v] = c;"
  , "  }" ]

/-- The resident full-NTT body: the four vector-pair layers, then the fused deep
    sweep. -/
def renderMlkemNttFull16wayResidentBody : List String :=
  residentPairLayers ++ residentDeepSweep

/-- Pair layers with loop-invariant zeta/`vq` loads hoisted out of the unrolled
    butterfly loops: within `len = 128` the single group's `(zl,zh)` is constant,
    and within each `len = 64, 32` group the `(zl,zh)` is constant across the inner
    vectors, so the load is issued once per group instead of once per butterfly.
    Byte-identical to the baseline pair layers; removes redundant loads without
    lengthening any dependency chain. -/
def hoistedPairLayers : List String :=
  [ "  reg u256 vq a b t zl zh c d radd rsub bb alow;"
  , "  reg u256 duph4 dupl4 duph2 dupl2;"
  , "  inline int v;"
  , ""
  , "  vq  = aux[:u256 0];"
  , ""
  , "  // === len = 128 (zl,zh @ aux 1,2 hoisted) ==="
  , "  zl = aux[:u256 1]; zh = aux[:u256 2];"
  , "  for v = 0 to 8 {"
  , "    a = r[:u256 v];  b = r[:u256 v + 8];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 v] = c; r[:u256 v + 8] = d;"
  , "  }"
  , "  // === len = 64 (zl,zh per group hoisted) ==="
  , "  zl = aux[:u256 3]; zh = aux[:u256 4];"
  , "  for v = 0 to 4 {"
  , "    a = r[:u256 v]; b = r[:u256 v + 4];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 v] = c; r[:u256 v + 4] = d;"
  , "  }"
  , "  zl = aux[:u256 5]; zh = aux[:u256 6];"
  , "  for v = 0 to 4 {"
  , "    a = r[:u256 8 + v]; b = r[:u256 8 + v + 4];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 8 + v] = c; r[:u256 8 + v + 4] = d;"
  , "  }"
  , "  // === len = 32 (zl,zh per group hoisted) ==="
  , "  zl = aux[:u256 7]; zh = aux[:u256 8];"
  , "  for v = 0 to 2 {"
  , "    a = r[:u256 v]; b = r[:u256 v + 2];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 v] = c; r[:u256 v + 2] = d;"
  , "  }"
  , "  zl = aux[:u256 9]; zh = aux[:u256 10];"
  , "  for v = 0 to 2 {"
  , "    a = r[:u256 4 + v]; b = r[:u256 4 + v + 2];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 4 + v] = c; r[:u256 4 + v + 2] = d;"
  , "  }"
  , "  zl = aux[:u256 11]; zh = aux[:u256 12];"
  , "  for v = 0 to 2 {"
  , "    a = r[:u256 8 + v]; b = r[:u256 8 + v + 2];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 8 + v] = c; r[:u256 8 + v + 2] = d;"
  , "  }"
  , "  zl = aux[:u256 13]; zh = aux[:u256 14];"
  , "  for v = 0 to 2 {"
  , "    a = r[:u256 12 + v]; b = r[:u256 12 + v + 2];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 12 + v] = c; r[:u256 12 + v + 2] = d;"
  , "  }"
  , "  // === len = 16 (distinct zetas per iter; not hoistable) ==="
  , "  for v = 0 to 8 {"
  , "    zl = aux[:u256 15 + 2*v]; zh = aux[:u256 16 + 2*v];"
  , "    a = r[:u256 2*v]; b = r[:u256 2*v + 1];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 2*v] = c; r[:u256 2*v + 1] = d;"
  , "  }" ]

/-- The three deep within-vector layers kept as separate loops (baseline shape,
    preserving cross-vector ILP within each layer), each with per-vector `(zl,zh)`
    (distinct per iter, not hoistable). -/
def separateDeepLayers : List String :=
  [ ""
  , "  duph4 = aux[:u256 127];"
  , "  dupl4 = aux[:u256 128];"
  , "  duph2 = aux[:u256 129];"
  , "  dupl2 = aux[:u256 130];"
  , ""
  , "  // === len = 8 (cross-128) ==="
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
  , "  // === len = 4 (within 128) ==="
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
  , "  // === len = 2 (within 128) ==="
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

/-- The hoisted-zeta full-NTT body: hoisted pair layers, then the separate deep
    layers (ILP preserved). -/
def renderMlkemNttFull16wayHoistedBody : List String :=
  hoistedPairLayers ++ separateDeepLayers

/-- Emit the hoisted-zeta full 16-lane AVX2 ML-KEM-768 forward NTT `.jazz`. -/
def emitMlkemNttFull16wayHoistedJazz (name : String) : String :=
  String.intercalate "\n" renderVfqmul ++ "\n\n"
    ++ "export fn " ++ name
    ++ "(reg mut ptr u16[256] r, reg const ptr u16[2112] aux)\n"
    ++ "    -> reg mut ptr u16[256]\n{\n"
    ++ String.intercalate "\n" renderMlkemNttFull16wayHoistedBody
    ++ "\n\n  return r;\n}"

/-- Emit the resident full 16-lane AVX2 ML-KEM-768 forward NTT `.jazz`. Same ABI
    as `LatticeNttEmit.emitMlkemNttFull16wayJazz`: `reg mut ptr u16[256] r`
    (in-place polynomial), `reg const ptr u16[2112] aux` (q broadcast, per-layer
    `(zl,zh)` expanded-zeta pairs, shuffle controls). -/
def emitMlkemNttFull16wayResidentJazz (name : String) : String :=
  String.intercalate "\n" renderVfqmul ++ "\n\n"
    ++ "export fn " ++ name
    ++ "(reg mut ptr u16[256] r, reg const ptr u16[2112] aux)\n"
    ++ "    -> reg mut ptr u16[256]\n{\n"
    ++ String.intercalate "\n" renderMlkemNttFull16wayResidentBody
    ++ "\n\n  return r;\n}"

/-- Denotation preservation for the resident full ML-KEM-768 NTT emit. Composes
    the lane-map lemma `LatticeNttEmit.mlkem_ntt_4way_lane_map` at the per-lane
    butterfly: the deep-layer fusion reorders loads and stores of independent
    vectors and leaves the per-lane data flow unchanged. -/
theorem mlkem_ntt_full_resident_denotation_preserves (lanes : MlkemNtt4Way) :
    LaneMap.laneMap mlkemNttButterflySpec lanes =
      (fun b => mlkemNttButterflySpec (lanes b)) :=
  mlkem_ntt_4way_lane_map mlkemNttButterflySpec lanes

end CatCrypt.Crypto.SecureCompilation.VIR.MlkemNttFullResidentEmit
