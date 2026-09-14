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
import all CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MldsaNtt4WayVec
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MldsaNtt4WayVec

/-!
# AVX-512 lowering of lane operations used by the AVX2 kernels

`LoweringAVX512.lean` defines the AVX-512 pass `lowerAVX512` with an instruction
semantics determined by mnemonic and width. This file applies it to the lane
operations of the AVX2 kernels and states:

* the 16×u32 lane add lowers to `VPADDD` and writes the lane sums
  (`add_avx512_eq`), agreeing with the AVX2 lowering `lower` of the same dialect op
  (`add_avx2_avx512_agree`);
* the unsigned high-half multiply `MldsaNtt4WayVec.mulHi16` and the arithmetic
  shift `MldsaNtt4WayVec.shiftRA16` lower at 32×u16 to `VPMULHUW` and `VPSRAW`
  and write the per-lane `mulHi16` and `shiftRA16` (`mldsa_mulHi_avx512_eq`,
  `mldsa_shiftRA_avx512_eq`);
* the rendered mnemonic lines (`add_avx512_render`, `mldsa_reduction_avx512_render`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512Demo

open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.MldsaNtt4WayVec

/-! ## 1. Lane add at 16 × u32 -/

/-- The 16×u32 lane add lowers to an instruction that writes `a i + b i`. -/
theorem add_avx512_eq (L : LeafSem) (a b : Zmm .w16u32) :
    (lowerAVX512 (.bin .add a b)).map (fun i => i.denote512 L)
      = some (fun i => a i + b i) := by
  show some ((lowerInst (.bin .add a b : LaneOp .w16u32)).denote512 L) = _
  exact congrArg some (funext fun i => binMnem_laneSem_eq .add 32 (a i) (b i))

/-- The lane add at 16×u32, rendered with output `c` and operands `a`, `b`. -/
theorem add_avx512_render (a b : Zmm .w16u32) :
    (lowerAVX512 (.bin .add a b)).map (renderAVX512 "c" ["a", "b"])
      = some "c = #VPADD_16u32(a, b);" := by
  show some (renderAVX512 "c" ["a", "b"] (lowerInst (.bin .add a b : LaneOp .w16u32))) = _
  simp only [lowerInst, renderAVX512, LaneBin.mnem, BinMnem.name, LaneWidth.suffix, List.take,
    String.intercalate_cons_cons, String.intercalate_singleton]
  rfl

/-- The AVX2 lowering `lower` and the AVX-512 lowering of the 16-lane `u32` add
    write the same lane vector. -/
theorem add_avx2_avx512_agree (L : LeafSem) (a b : Zmm .w16u32) :
    (lowerAVX512 (.bin .add a b)).map (fun i => i.denote512 L)
      = (lower (0 : BitVec 32) (.add (· + ·) a b : VectorOp (BitVec 32) 16)).map
          (·.denote) := by
  rw [lower_add_correct]
  show some ((lowerInst (.bin .add a b : LaneOp .w16u32)).denote512 L) = _
  exact congrArg some (funext fun i => binMnem_laneSem_eq .add 32 (a i) (b i))

/-! ## 2. Montgomery reduction lane ops at 32 × u16

`mulHi16` is the high half of the unsigned 32-bit product (`VPMULHUW`), and
`shiftRA16` the arithmetic shift (`VPSRAW`). -/

/-- `VPMULHUW` at 32×u16 writes `mulHi16 (v i) (u i)`. -/
theorem mldsa_mulHi_avx512_eq (L : LeafSem) (v u : Zmm .w32u16) :
    (lowerAVX512 (.bin .mulHiU v u)).map (fun i => i.denote512 L)
      = some (fun i => mulHi16 (v i) (u i)) := by
  show some ((lowerInst (.bin .mulHiU v u : LaneOp .w32u16)).denote512 L) = _
  exact congrArg some (funext fun i => binMnem_laneSem_eq .mulHiU 16 (v i) (u i))

/-- `VPSRAW` at 32×u16 writes `shiftRA16 (v i) m`. -/
theorem mldsa_shiftRA_avx512_eq (L : LeafSem) (m : Nat) (v : Zmm .w32u16) :
    (lowerAVX512 (.shift .sar m v)).map (fun i => i.denote512 L)
      = some (fun i => shiftRA16 (v i) m) := by
  show some ((lowerInst (.shift .sar m v : LaneOp .w32u16)).denote512 L) = _
  exact congrArg some (funext fun i => shiftMnem_laneSem_eq .sar 16 m (v i))

/-- The two reduction ops at 32×u16, rendered. -/
theorem mldsa_reduction_avx512_render (v u : Zmm .w32u16) (m : Nat) :
    (lowerAVX512 (.bin .mulHiU v u)).map (renderAVX512 "t" ["m", "q"])
        = some "t = #VPMULHU_32u16(m, q);"
      ∧ (lowerAVX512 (.shift .sar m v)).map (renderAVX512 "r" ["a"])
        = some ("r = #VPSRA_32u16(a, " ++ toString m ++ ");") := by
  refine ⟨?_, rfl⟩
  show some (renderAVX512 "t" ["m", "q"] (lowerInst (.bin .mulHiU v u : LaneOp .w32u16))) = _
  simp only [lowerInst, renderAVX512, LaneBin.mnem, BinMnem.name, LaneWidth.suffix, List.take,
    String.intercalate_cons_cons, String.intercalate_singleton]
  rfl

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.LoweringAVX512Demo
