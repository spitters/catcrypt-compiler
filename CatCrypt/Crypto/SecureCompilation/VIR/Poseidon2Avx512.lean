/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.String.Defs
import all CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Poseidon2LaneVec

/-!
# Poseidon2 BabyBear — AVX-512 (ZMM, 8×u64) lowering

The lane operations of the Poseidon2 width-16 permutation over `u64` lanes — the
MDS / round-constant add `padd`, the S-box multiply `pmul` and the reduce shift
`pshr` of [`Poseidon2LaneVec.lean`](../../MLIR/VectorDialect/Poseidon2LaneVec.lean)
— lowered at 8×u64 by the AVX-512 pass `lowerAVX512`
([`LoweringAVX512.lean`](../../MLIR/VectorDialect/LoweringAVX512.lean)), whose
instruction semantics is determined by mnemonic and width.

| Poseidon2 layer | lane op | AVX-512 instruction | features |
|---|---|---|---|
| MDS / RC-add | `padd` | `VPADDQ` (`#VPADD_8u64`) | `AVX512F` |
| S-box multiply | `pmul` | `VPMULLQ` (`#VPMULL_8u64`) | `AVX512F`, `AVX512DQ` |
| reduce shift | `pshr` | `VPSRLQ` (`#VPSRL_8u64`) | `AVX512F` |

The high half of a 64-bit product has no AVX-512 instruction, and the lowering
rejects it (`mont_mulHi_avx512_rejected`); a Montgomery reduce on `u64` lanes is
written with `VPMULUDQ`, which the pass does not cover.

Each `*_avx512_eq` theorem states that the lowered instruction writes the lane
vector of the lane op; each `*_avx2_avx512_agree` theorem states that the AVX2
lowering `lower` and the AVX-512 lowering write the same lane vector.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Avx512

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Poseidon2LaneVec

/-! ## 1. The AVX-512 Poseidon2 lane shape: 8 × u64 per `zmm`. -/

/-- The Poseidon2 AVX-512 lane count (8 × u64 per `zmm`; 16-element state in
    2 `zmm`). -/
abbrev poseidon2LaneN512 : Nat := 8

/-! ## 2. MDS / RC-add → `VPADDQ` -/

/-- The MDS / round-constant add lowers to an instruction writing `padd` lane-wise. -/
theorem mds_add_avx512_eq (L : LeafSem) (v w : Zmm .w8u64) :
    (lowerAVX512 (.bin .add v w)).map (fun i => i.denote512 L)
      = some (VectorTy.map₂ padd v w) := by
  show some ((lowerInst (.bin .add v w : LaneOp .w8u64)).denote512 L) = _
  exact congrArg some (funext fun i => binMnem_laneSem_eq .add 64 (v i) (w i))

/-- The MDS / RC-add emits `#VPADD_8u64`. -/
theorem mds_add_avx512_render (v w : Zmm .w8u64) :
    (lowerAVX512 (.bin .add v w)).map (renderAVX512 "vS" ["vS", "vrc"])
      = some "vS = #VPADD_8u64(vS, vrc);" := by
  show some (renderAVX512 "vS" ["vS", "vrc"] (lowerInst (.bin .add v w : LaneOp .w8u64))) = _
  simp only [lowerInst, renderAVX512, LaneBin.mnem, BinMnem.name, LaneWidth.suffix, List.take,
    String.intercalate_cons_cons, String.intercalate_singleton]
  rfl

/-! ## 3. S-box multiply → `VPMULLQ` -/

/-- The S-box multiply lowers to an instruction writing `pmul` lane-wise. -/
theorem sbox_mul_avx512_eq (L : LeafSem) (v w : Zmm .w8u64) :
    (lowerAVX512 (.bin .mulLo v w)).map (fun i => i.denote512 L)
      = some (VectorTy.map₂ pmul v w) := by
  show some ((lowerInst (.bin .mulLo v w : LaneOp .w8u64)).denote512 L) = _
  exact congrArg some (funext fun i => binMnem_laneSem_eq .mulLo 64 (v i) (w i))

/-- The S-box `x⁵` chain of lane multiplies, `x² = x·x`, `x⁴ = x²·x²`,
    `x⁵ = x⁴·x`, is `(x·x)·(x·x)·x` in every lane. -/
theorem sbox_chain_avx512_eq (v : VectorTy (BitVec 64) poseidon2LaneN512) :
    (VectorTy.map₂ pmul
        (VectorTy.map₂ pmul (VectorTy.map₂ pmul v v) (VectorTy.map₂ pmul v v)) v)
      = (fun i => (v i * v i) * (v i * v i) * v i) := by
  funext i; rfl

/-- The S-box multiply emits `#VPMULL_8u64`. -/
theorem sbox_mul_avx512_render (v w : Zmm .w8u64) :
    (lowerAVX512 (.bin .mulLo v w)).map (renderAVX512 "vsq" ["va", "vb"])
      = some "vsq = #VPMULL_8u64(va, vb);" := by
  show some (renderAVX512 "vsq" ["va", "vb"] (lowerInst (.bin .mulLo v w : LaneOp .w8u64))) = _
  simp only [lowerInst, renderAVX512, LaneBin.mnem, BinMnem.name, LaneWidth.suffix, List.take,
    String.intercalate_cons_cons, String.intercalate_singleton]
  rfl

/-! ## 4. The 64-bit high-half product has no instruction -/

/-- The high half of the unsigned 64-bit product is rejected at 8×u64. -/
theorem mont_mulHi_avx512_rejected (v w : Zmm .w8u64) :
    lowerAVX512 (.bin .mulHiU v w) = none := rfl

/-! ## 5. Reduce shift → `VPSRLQ` -/

/-- The reduce right shift lowers to an instruction writing `pshr · m` lane-wise. -/
theorem reduce_shr_avx512_eq (L : LeafSem) (m : Nat) (v : Zmm .w8u64) :
    (lowerAVX512 (.shift .shr m v)).map (fun i => i.denote512 L)
      = some (VectorTy.map₁imm pshr m v) := by
  show some ((lowerInst (.shift .shr m v : LaneOp .w8u64)).denote512 L) = _
  exact congrArg some (funext fun i => shiftMnem_laneSem_eq .shr 64 m (v i))

/-- The reduce shift emits `#VPSRL_8u64`. -/
theorem reduce_shr_avx512_render (m : Nat) (v : Zmm .w8u64) :
    (lowerAVX512 (.shift .shr m v)).map (renderAVX512 "vr" ["vv"])
      = some ("vr = #VPSRL_8u64(vv, " ++ toString m ++ ");") := rfl

/-! ## 6. Required CPU features -/

/-- `VPADDQ` requires `AVX512F` only. -/
theorem mds_add_is_avx512f (v w : Zmm .w8u64) :
    (lowerInst (.bin .add v w)).exts = [.f] := rfl

/-- `VPMULLQ` requires `AVX512DQ`. -/
theorem sbox_mul_requires_avx512dq (v w : Zmm .w8u64) :
    (lowerInst (.bin .mulLo v w)).exts = [.f, .dq] := rfl

/-- `VPSRLQ` requires `AVX512F` only. -/
theorem reduce_shr_is_avx512f (m : Nat) (v : Zmm .w8u64) :
    (lowerInst (.shift .shr m v)).exts = [.f] := rfl

/-! ## 7. AVX2 and AVX-512 lowerings agree

For the add, multiply and shift on 8 lanes, the AVX2 lowering `lower` (denoting
via `ScalarExpansion`) and the AVX-512 lowering write the same lane vector. -/

/-- The two lowerings of the MDS / RC-add write the same lane vector. -/
theorem poseidon2_add_avx2_avx512_agree (L : LeafSem) (v w : Zmm .w8u64) :
    (lowerAVX512 (.bin .add v w)).map (fun i => i.denote512 L)
      = (lower (0 : BitVec 64) (.add padd v w : VectorOp (BitVec 64) poseidon2LaneN512)).map
          (·.denote) := by
  rw [lower_add_correct]
  exact mds_add_avx512_eq L v w

/-- The two lowerings of the S-box multiply write the same lane vector. -/
theorem poseidon2_mul_avx2_avx512_agree (L : LeafSem) (v w : Zmm .w8u64) :
    (lowerAVX512 (.bin .mulLo v w)).map (fun i => i.denote512 L)
      = (lower (0 : BitVec 64) (.mul pmul v w : VectorOp (BitVec 64) poseidon2LaneN512)).map
          (·.denote) := by
  rw [lower_mul_correct]
  exact sbox_mul_avx512_eq L v w

/-- The two lowerings of the reduce shift write the same lane vector. -/
theorem poseidon2_shr_avx2_avx512_agree (L : LeafSem) (m : Nat) (v : Zmm .w8u64) :
    (lowerAVX512 (.shift .shr m v)).map (fun i => i.denote512 L)
      = (lower (0 : BitVec 64) (.shiftR pshr m v : VectorOp (BitVec 64) poseidon2LaneN512)).map
          (·.denote) := by
  rw [lower_shiftR_correct]
  exact reduce_shr_avx512_eq L m v

end CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Avx512
