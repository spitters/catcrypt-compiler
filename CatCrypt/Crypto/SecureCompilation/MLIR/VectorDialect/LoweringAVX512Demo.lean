/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Types
import all CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Ops
import all CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Denote
import all CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Lowering
import all CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512
import all CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.ConsumerDemo
import all CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MldsaNtt4WayVec
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.ConsumerDemo
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MldsaNtt4WayVec

/-!
# AVX-512 lowering of existing `VectorOp` terms

In the structured `VectorOp` dialect, a SIMD width is supported by a lowering
pass over `VectorOp` terms; `LoweringAVX512.lean` defines the AVX-512 pass
`lowerAVX512`. This file applies that pass to `VectorOp` terms and lane ops
defined in `ConsumerDemo.lean` and `MldsaNtt4WayVec.lean` for the AVX2 lowering
`lower`, without modifying them, and states:

* the AVX-512 lowering of the ChaCha 4-way add step denotes `vpadd4u32_spec`
  (`chacha_add_avx512_eq_spec`), and the AVX2 and AVX-512 lowerings of that step
  denote the same lane vector (`chacha_add_avx2_avx512_agree`);
* the AVX-512 lowerings of `VectorOp.mulHi mulHi16` and
  `VectorOp.shiftRA shiftRA16` denote the per-lane `mulHi16` and `shiftRA16`
  (`mldsa_mulHi_avx512_eq`, `mldsa_shiftRA_avx512_eq`);
* the rendered 512-bit mnemonic lines (`chacha_add_avx512_render`,
  `mldsa_reduction_avx512_render`).

## Terms taken from other modules

* `ConsumerDemo.vpadd4u32_vectorOp` — the ChaCha 4-way packed-add kernel step,
  defined for the AVX2 path and passed to `lowerAVX512` as is.
* `MldsaNtt4WayVec.mulHi16` / `shiftRA16` — the ML-DSA / ML-KEM Montgomery /
  Barrett reduction lane ops, defined for the AVX2 `VPMULH` / `VPSRA`. The
  `VectorOp.mulHi` / `VectorOp.shiftRA` terms over them are lowered to the
  512-bit `#VPMULH_32u16` / `#VPSRA_32u16` mnemonics.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512Demo

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.ConsumerDemo
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MldsaNtt4WayVec

/-! ## 1. ChaCha 4-way packed add at 512-bit width

`vpadd4u32_vectorOp a b` is the kernel step defined in `ConsumerDemo.lean`
for the AVX2 lowering. The `VectorOp` constructors are polymorphic in the lane
count, and `lowerAVX512` takes the target width as an argument. The statements
below use the 4-lane shape of `vpadd4u32_vectorOp` at width `.w16u32`. -/

/-- The AVX-512 lowering of the ChaCha 4-way `add` kernel step
    `vpadd4u32_vectorOp a b` succeeds and denotes `vpadd4u32_spec a b`. -/
theorem chacha_add_avx512_eq_spec (a b : W32x4) :
    (lowerAVX512 .w16u32 (vpadd4u32_vectorOp a b)).map (·.denote512)
      = some (vpadd4u32_spec a b) := by
  -- `vpadd4u32_vectorOp a b = .add (·+·) a b`; the AVX-512 pass denotes `map₂`;
  -- `vpadd4u32_spec a b = fun i => a i + b i = map₂ (·+·) a b`.
  rfl

/-- The AVX-512 lowering of `vpadd4u32_vectorOp a b`, rendered with output `c`
    and operands `a`, `b`, is the mnemonic line `c = #VPADD_16u32(a, b);`. -/
theorem chacha_add_avx512_render (a b : W32x4) :
    ((lowerAVX512 .w16u32 (vpadd4u32_vectorOp a b)).map
        (renderAVX512 "c" ["a", "b"]))
      = some "c = #VPADD_16u32(a, b);" := by
  simp only [vpadd4u32_vectorOp, lowerAVX512, Option.map, renderAVX512, List.take,
    String.intercalate_cons_cons, String.intercalate_singleton]
  rfl

/-! ## 2. ML-DSA / ML-KEM Montgomery reduction — same ops, 512-bit `zmm`

`mulHi16` (`VPMULHW`) and `shiftRA16` (`VPSRAW`) are the reduction lane ops
defined in `MldsaNtt4WayVec.lean` for the AVX2 path. The `VectorOp.mulHi` /
`VectorOp.shiftRA` terms over them are lowered at width `w32u16`: a `zmm` holds
32 × u16 lanes (an AVX2 `__m256i` holds 16). -/

/-- The high-half multiply (`VPMULH`) leg of Montgomery reduction, lowered via
    the AVX-512 pass at width `w32u16`, succeeds and denotes the per-lane
    `mulHi16` over 32 lanes. -/
theorem mldsa_mulHi_avx512_eq (v w : VectorTy (BitVec 16) 32) :
    (lowerAVX512 .w32u16 (.mulHi mulHi16 v w : VectorOp (BitVec 16) 32)).map
        (·.denote512)
      = some (fun i => mulHi16 (v i) (w i)) := rfl

/-- The signed shift (`VPSRA`) leg, lowered via the AVX-512 pass, denotes the
    `shiftRA16` per lane over 32 lanes. -/
theorem mldsa_shiftRA_avx512_eq (m : Nat) (v : VectorTy (BitVec 16) 32) :
    (lowerAVX512 .w32u16 (.shiftRA shiftRA16 m v : VectorOp (BitVec 16) 32)).map
        (·.denote512)
      = some (fun i => shiftRA16 (v i) m) := rfl

/-- The two reduction legs, lowered at width `w32u16` and rendered, are the
    512-bit mnemonic lines `#VPMULH_32u16` and `#VPSRA_32u16`. -/
theorem mldsa_reduction_avx512_render (v w : VectorTy (BitVec 16) 32) (m : Nat) :
    ((lowerAVX512 .w32u16 (.mulHi mulHi16 v w)).map (renderAVX512 "t" ["m", "q"]))
        = some "t = #VPMULH_32u16(m, q);"
      ∧ ((lowerAVX512 .w32u16 (.shiftRA shiftRA16 m v)).map
          (renderAVX512 "r" ["a"]))
        = some ("r = #VPSRA_32u16(a, " ++ toString m ++ ");") := by
  refine ⟨?_, rfl⟩
  simp only [lowerAVX512, Option.map, renderAVX512, List.take,
    String.intercalate_cons_cons, String.intercalate_singleton]
  rfl

/-! ## 3. Cross-target consistency on the ChaCha add step

For the `VectorOp` term `vpadd4u32_vectorOp a b`, the AVX2 lowering (`lower`,
denoting via `ScalarExpansion`) and the AVX-512 lowering (`lowerAVX512`,
denoting via `denote512`) give the same lane vector, as `Option` values. -/

/-- For the ChaCha 4-way `add` step, the AVX2 lowering and the AVX-512 lowering
    denote the same lane vector (as `Option` values). -/
theorem chacha_add_avx2_avx512_agree (a b : W32x4) :
    ((lowerAVX512 .w16u32 (vpadd4u32_vectorOp a b)).map (·.denote512)
      = (lower initW32 (vpadd4u32_vectorOp a b)).map (·.denote)) := by
  -- `vpadd4u32_vectorOp a b = .add (·+·) a b`.  AVX-512 side denotes `map₂`;
  -- AVX2 side's `ScalarExpansion` also denotes `map₂` (by `lower_add_correct`).
  -- Both reduce to `some (map₂ (·+·) a b)`.
  show (lowerAVX512 .w16u32 (.add _ a b)).map (·.denote512)
      = (lower initW32 (.add _ a b)).map (·.denote)
  rw [lowerAVX512_add_correct, lower_add_correct]

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512Demo
