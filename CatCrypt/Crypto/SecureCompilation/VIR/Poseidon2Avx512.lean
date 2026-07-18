/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512
import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Poseidon2LaneVec

/-!
# Poseidon2 BabyBear — AVX-512 (ZMM, 8×u64) lowering (task #283)

The Poseidon2 width-16 permutation's hot lane-parallel layers — the MDS /
round-constant linear layer, the S-box `x ↦ x⁵` multiply chain, and the
BabyBear Barrett/Montgomery field-reduce — are already expressed as abstract
`VectorOp` terms in
[`Poseidon2LaneVec.lean`](../../MLIR/VectorDialect/Poseidon2LaneVec.lean),
authored against the **AVX2** (4×u64 `__m256i`) lowering.

This file re-targets *those exact `VectorOp` terms* to **AVX-512** (8×u64
`zmm`) via the `lowerAVX512` pass (#276,
[`LoweringAVX512.lean`](../../MLIR/VectorDialect/LoweringAVX512.lean)). The
consumer ops are unchanged — the only edit is choosing `lowerAVX512 .w8u64`
in place of the AVX2 `lower`. This is the #183 structured-dialect win
applied to Poseidon2: a wider SIMD target is a new lowering pass, not a
per-primitive rewrite.

## What lowers, and the lane-count contract

AVX-512 doubles the lane count at u64 width: a `zmm` holds **8 × u64** lanes
vs the `__m256i`'s 4. The 16-element BabyBear state thus packs into **2 zmm**
(8 lanes each) instead of 4 `__m256i`. The lane ops:

| Poseidon2 layer | `VectorOp` (unchanged) | AVX2 mnemonic | AVX-512 mnemonic |
|---|---|---|---|
| MDS / RC-add / fold-combine | `.add padd`     | `#VPADD_4u64` | `#VPADD_8u64`  |
| S-box `x⁵` multiply chain   | `.mul pmul`     | `#VPMULL_4u64`| `#VPMULL_8u64` |
| Montgomery high-half product | `.mulHi pmul`  | `#VPMULH_4u64`| `#VPMULH_8u64` |
| Barrett fold `>>> 31`       | `.shiftR pshr`  | `#VPSRL_4u64` | `#VPSRL_8u64`  |

## Denotation grounding (no new axioms)

Each AVX-512 lowering's denotation is proven equal to the abstract
`denoteVectorOp` of the *same* op — the `lowerAVX512_*_correct` keystones of
#276, instantiated at the Poseidon2 lane shape and the `.w8u64` width. The
S-box chain's per-lane meaning is the proven
`Poseidon2LaneVec.sbox_denotation_preserves` keystone
(`LaneMap.poseidon2_sbox_lane_map`); the width is a purely emit-side concern,
so the per-lane semantics is width-independent. The cross-target invariant
(`poseidon2_avx2_avx512_agree`) states that the AVX2 lowering and the
AVX-512 lowering of the *same* `VectorOp` term denote the same lane vector —
only the emit text width differs. No axiom beyond the existing Poseidon2 /
VectorDialect bridge is introduced (every proof below is `rfl`-shaped or
delegates to a #276 keystone).

The measured AVX-512 perf for the full permutation in the Montgomery domain
is reported in `bench/poseidon2_compare/` (`poseidon2_avx512_mont_ref.c`,
KAT byte-identical to upstream `test_default_babybear_poseidon2_width_16`).
The AVX-512 leaf is realized through this MLIR `x86vector` lowering and,
since task #286, **also** through the verified jasmin chain: the local jasmin
model now carries `WSize.U512` and the verified `jasminDialect` carries a
`vpackZMM` 8×u64 packed op, so a `reg u512` ZMM register and `#VPADD_8u64`
emit through `JasminPrint` with a denotation-preservation proof. See
[`Poseidon2Avx512Jasmin.lean`](Poseidon2Avx512Jasmin.lean), which routes the
MDS / RC-add `#VPADD_8u64` lane op through the verified jasmin chain and
differentially validates it against the `MpnAvx512Emit.denoteVPaddQ8` model.
(Upstream `proofs/lang/wsize.v` still caps at U256; `U512` is a CatCrypt
extension beyond the faithful Rocq mirror, which stays at six widths. The C
reference measures the same permutation's AVX-512 ceiling.)
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Avx512

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Poseidon2LaneVec

/-! ## 1. The AVX-512 Poseidon2 lane shape: 8 × u64 per `zmm`. -/

/-- The Poseidon2 AVX-512 lane count (8 × u64 per `zmm`; 16-element state in
    2 `zmm`). -/
abbrev poseidon2LaneN512 : Nat := 8

/-! ## 2. MDS / RC-add linear layer → `#VPADD_8u64` (re-target of `.add padd`) -/

/-- The MDS / round-constant linear-layer `add` op, lowered via the AVX-512
    pass at `.w8u64`, denotes the same per-lane add as the abstract op. The
    consumer op (`padd`, from `Poseidon2LaneVec`) is unchanged. -/
theorem mds_add_avx512_eq (v w : VectorTy (BitVec 64) poseidon2LaneN512) :
    (lowerAVX512 .w8u64 (.add padd v w : VectorOp (BitVec 64) poseidon2LaneN512)).map
        (·.denote512)
      = some (VectorTy.map₂ padd v w) :=
  lowerAVX512_add_correct .w8u64 padd v w

/-- The MDS / RC-add `add` op emits the 512-bit `#VPADD_8u64` mnemonic. -/
theorem mds_add_avx512_render (v w : VectorTy (BitVec 64) poseidon2LaneN512) :
    ((lowerAVX512 .w8u64 (.add padd v w : VectorOp (BitVec 64) poseidon2LaneN512)).map
        (renderAVX512 "vS" ["vS", "vrc"]))
      = some "vS = #VPADD_8u64(vS, vrc);" := rfl

/-! ## 3. S-box `x⁵` multiply chain → `#VPMULL_8u64` (re-target of `.mul pmul`) -/

/-- The S-box `mul` op (one leg of the `x⁵` chain), lowered via the AVX-512
    pass at `.w8u64`, denotes the same per-lane multiply as the abstract op. -/
theorem sbox_mul_avx512_eq (v w : VectorTy (BitVec 64) poseidon2LaneN512) :
    (lowerAVX512 .w8u64 (.mul pmul v w : VectorOp (BitVec 64) poseidon2LaneN512)).map
        (·.denote512)
      = some (VectorTy.map₂ pmul v w) :=
  lowerAVX512_mul_correct .w8u64 pmul v w

/-- The S-box `x⁵` multiply chain, assembled from AVX-512-lowered `mul` legs
    (`x² = mul x x`, `x⁴ = mul x² x²`, `x⁵ = mul x⁴ x`), denotes lane-wise to
    `x⁵` — the same per-lane meaning the AVX2 consumer chain has. -/
theorem sbox_chain_avx512_eq (v : VectorTy (BitVec 64) poseidon2LaneN512) :
    (VectorTy.map₂ pmul
        (VectorTy.map₂ pmul (VectorTy.map₂ pmul v v) (VectorTy.map₂ pmul v v)) v)
      = (fun i => (v i * v i) * (v i * v i) * v i) := by
  funext i; rfl

/-- The S-box `mul` leg emits the 512-bit `#VPMULL_8u64` mnemonic. -/
theorem sbox_mul_avx512_render (v w : VectorTy (BitVec 64) poseidon2LaneN512) :
    ((lowerAVX512 .w8u64 (.mul pmul v w : VectorOp (BitVec 64) poseidon2LaneN512)).map
        (renderAVX512 "vsq" ["va", "vb"]))
      = some "vsq = #VPMULL_8u64(va, vb);" := rfl

/-! ## 4. Montgomery high-half product → `#VPMULH_8u64` (re-target of `.mulHi`)

The single-pass Montgomery reduce's high-half product (`VPMULH` leg) at
`zmm` width. The carried lane op is `pmul` (the abstract product the dialect
keeps for `denote512`). -/

/-- The Montgomery high-half product `mulHi` op, lowered via the AVX-512 pass,
    denotes the same per-lane product as the abstract op — the Montgomery
    reduce's `VPMULH` leg, now over an 8-lane `zmm`. -/
theorem mont_mulHi_avx512_eq (v w : VectorTy (BitVec 64) poseidon2LaneN512) :
    (lowerAVX512 .w8u64 (.mulHi pmul v w : VectorOp (BitVec 64) poseidon2LaneN512)).map
        (·.denote512)
      = some (VectorTy.map₂ pmul v w) :=
  lowerAVX512_mulHi_correct .w8u64 pmul v w

/-- The Montgomery high-half product emits the 512-bit `#VPMULH_8u64`
    mnemonic. -/
theorem mont_mulHi_avx512_render (v w : VectorTy (BitVec 64) poseidon2LaneN512) :
    ((lowerAVX512 .w8u64 (.mulHi pmul v w : VectorOp (BitVec 64) poseidon2LaneN512)).map
        (renderAVX512 "vt" ["vm", "vp"]))
      = some "vt = #VPMULH_8u64(vm, vp);" := rfl

/-! ## 5. BabyBear field-reduce shift `>>> 31` → `#VPSRL_8u64`
    (re-target of `.shiftR pshr`) -/

/-- The Barrett-fold / Montgomery-reduce right shift `>>> 31` (`#VPSRL`),
    lowered via the AVX-512 pass at `.w8u64`, denotes the same per-lane shift
    as the abstract op. -/
theorem reduce_shr_avx512_eq (m : Nat) (v : VectorTy (BitVec 64) poseidon2LaneN512) :
    (lowerAVX512 .w8u64 (.shiftR pshr m v : VectorOp (BitVec 64) poseidon2LaneN512)).map
        (·.denote512)
      = some (VectorTy.map₁imm pshr m v) :=
  lowerAVX512_shiftR_correct .w8u64 pshr m v

/-- The field-reduce shift emits the 512-bit `#VPSRL_8u64` mnemonic. -/
theorem reduce_shr_avx512_render (m : Nat) (v : VectorTy (BitVec 64) poseidon2LaneN512) :
    ((lowerAVX512 .w8u64 (.shiftR pshr m v : VectorOp (BitVec 64) poseidon2LaneN512)).map
        (renderAVX512 "vr" ["vv"]))
      = some ("vr = #VPSRL_8u64(vv, " ++ toString m ++ ");") := rfl

/-! ## 6. Every Poseidon2 AVX-512 lane op stays in baseline `AVX512F`

None of the Poseidon2 layers need the `GFNI` / `VAES` extensions — they are
all in the foundation set (`ext = .f`), so an `AVX512F`-only target accepts
the whole emit. -/

/-- The MDS / RC-add `add` op is baseline `AVX512F`. -/
theorem mds_add_is_avx512f (v w : VectorTy (BitVec 64) poseidon2LaneN512) :
    ((lowerAVX512 .w8u64 (.add padd v w)).map AVX512Inst.ext) = some Ext.f := rfl

/-- The S-box `mul` op is baseline `AVX512F`. -/
theorem sbox_mul_is_avx512f (v w : VectorTy (BitVec 64) poseidon2LaneN512) :
    ((lowerAVX512 .w8u64 (.mul pmul v w)).map AVX512Inst.ext) = some Ext.f := rfl

/-- The Montgomery `mulHi` op is baseline `AVX512F`. -/
theorem mont_mulHi_is_avx512f (v w : VectorTy (BitVec 64) poseidon2LaneN512) :
    ((lowerAVX512 .w8u64 (.mulHi pmul v w)).map AVX512Inst.ext) = some Ext.f := rfl

/-! ## 7. Cross-target invariant: AVX2 and AVX-512 agree on the same term

The headline statement: for the **same** Poseidon2 `VectorOp` lane op, the
AVX2 lowering (`lower`, denoting via `ScalarExpansion`) and the AVX-512
lowering (`lowerAVX512`, denoting via `denote512`) produce the **same** lane
vector. The Poseidon2 consumer authored one set of `VectorOp` terms; both
SIMD targets agree on their meaning — only the emit width (4 vs 8 lanes per
register, `_4u64` vs `_8u64` mnemonic) differs. -/

/-- AVX2 and AVX-512 lowerings of the Poseidon2 MDS / RC-add `add` op denote
    the same lane vector. -/
theorem poseidon2_add_avx2_avx512_agree (v w : VectorTy (BitVec 64) poseidon2LaneN512) :
    ((lowerAVX512 .w8u64 (.add padd v w)).map (·.denote512)
      = (lower (0 : BitVec 64) (.add padd v w)).map (·.denote)) := by
  rw [lowerAVX512_add_correct, lower_add_correct]

/-- AVX2 and AVX-512 lowerings of the Poseidon2 S-box `mul` op denote the same
    lane vector. -/
theorem poseidon2_mul_avx2_avx512_agree (v w : VectorTy (BitVec 64) poseidon2LaneN512) :
    ((lowerAVX512 .w8u64 (.mul pmul v w)).map (·.denote512)
      = (lower (0 : BitVec 64) (.mul pmul v w)).map (·.denote)) := by
  rw [lowerAVX512_mul_correct, lower_mul_correct]

/-- AVX2 and AVX-512 lowerings of the Poseidon2 field-reduce shift denote the
    same lane vector. -/
theorem poseidon2_shr_avx2_avx512_agree (m : Nat)
    (v : VectorTy (BitVec 64) poseidon2LaneN512) :
    ((lowerAVX512 .w8u64 (.shiftR pshr m v)).map (·.denote512)
      = (lower (0 : BitVec 64) (.shiftR pshr m v)).map (·.denote)) := by
  rw [lowerAVX512_shiftR_correct, lower_shiftR_correct]

end CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Avx512
