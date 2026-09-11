/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.YmmDialectOps
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.FinCases
public import Std.Tactic.BVDecide

/-!
# Packed lane rotate for the 256-bit YMM op set (AVX2 8-lane, SLH-DSA batch8)

The SLH-DSA multi-buffer batch8 hashes eight independent SHA-256 lanes in a
256-bit YMM register (8×`u32`). SHA-256's Σ/σ mixing needs a packed dword
rotate, which AVX2 has no single instruction for (`VPROLD` is AVX-512). This
file adds the packed 8-lane rotate and its per-lane denotation over the existing
`YmmOp` shift/or ops (`VPSLLD`/`VPSRLD`/`VPOR`), in the same 8×`u32` lane model
as `yDwordW`/`yOfDwordsW`.

## Main results

* `v256PackRolW`: the semantic 8×`u32` packed rotate.
* `v256Rol32_lane`: lane `k` of the packed rotate equals the scalar `rotateLeft`.
* `packedRol32_avx2_realizes256`: the rotate expressed over the existing 256-bit
  ops (`vpslldW`, `vpsrldW`, `vporW`) realizes the per-lane scalar rotate.
* `v256PackRolW_is_scalar_laneMap`: the packed rotate is `LaneMap.scalarMap` of
  the scalar rotate — the batch8 denotation-preservation shape.

On AVX2 the rotate is realized as a three-op macro over ops already in the set:
`VPSLLD` + `VPSRLD` + `VPOR`, i.e. `rol(a, imm) = (a <<< imm) ||| (a >>> (w - imm))`
per lane. No new `YmmOp` constructor and no new byte encoder are required; the
packed rotate is a derived op whose denotation is proved from the existing ops.

## Contents

* `packFold32_lane256` — the 8-lane packing round-trip kernel.
* `v256PackRolW` — the semantic packed rotate (8×`u32`): lane `j` rotates by `imm`.
* `v256Rol32_lane` — lane `k` of the packed rotate equals the scalar
  `BitVec.rotateLeft imm` of lane `k`.
* `rol32_synth` — the scalar rotate equals the `shl`/`shr`/`or` synthesis.
* `vpslldW_uniform_lane` / `vpsrldW_uniform_lane` — lane `k` of `vpslldW`/`vpsrldW`
  is the per-lane scalar shift.
* `packedRol32_avx2_realizes256` — lane `k` of `vporW (vpslldW a imm)
  (vpsrldW a (32 - imm))` equals the scalar `rotateLeft imm`, for `imm < 32`.
* `v256PackRolW_is_scalar_laneMap` — the packed rotate is the `LaneMap.scalarMap`
  of the scalar rotate over the eight unpacked lanes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.PackedRotate256

open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
  (vpslldW vpsrldW vporW yDwordW yOfDwordsW)

/-- **Generic 8-lane packing round-trip.** Reading lane `k` (the `[32k, 32k+32)`
    slice) of a fold-`OR` of `setWidth`-widened, lane-shifted `u32` values returns
    the `k`-th lane value `g k`, for any per-lane function `g`. This is the packing
    kernel behind every 8×`u32` lane lemma. -/
theorem packFold32_lane256 (g : Nat → BitVec 32) (k : Fin 8) :
    BitVec.extractLsb' (32 * k.val) 32
      ((List.range 8).foldl (fun acc j => acc ||| ((g j).setWidth 256 <<< (32 * j))) 0)
      = g k.val := by
  fin_cases k <;> simp only [List.range, List.range.loop, List.foldl] <;> bv_decide

/-- The semantic packed lane rotate on a 256-bit YMM register (8×`u32`): lane `j`
    of the result is lane `j` of `a` rotated left by `imm`. This is the packed
    denotation an AVX2-macro rotate realizes. -/
def v256PackRolW (imm : Nat) (a : BitVec 256) : BitVec 256 :=
  (List.range 8).foldl
    (fun acc j =>
      acc ||| (((BitVec.extractLsb' (32 * j) 32 a).rotateLeft imm).setWidth 256 <<< (32 * j))) 0

/-- **Per-lane realization of the packed rotate.** Reading lane `k` of
    `v256PackRolW imm a` equals the scalar `BitVec.rotateLeft imm` of lane `k` of
    `a`. Holds for an arbitrary (symbolic) rotate amount `imm`. -/
theorem v256Rol32_lane (imm : Nat) (a : BitVec 256) (k : Fin 8) :
    BitVec.extractLsb' (32 * k.val) 32 (v256PackRolW imm a)
      = (BitVec.extractLsb' (32 * k.val) 32 a).rotateLeft imm :=
  packFold32_lane256 (fun j => (BitVec.extractLsb' (32 * j) 32 a).rotateLeft imm) k

/-- The scalar 32-bit rotate is the `shl`/`shr`/`or` synthesis
    `(x <<< imm) ||| (x >>> (32 - imm))`, for `imm < 32`. This is the AVX2
    realization of one lane's rotate as `VPSLLD` + `VPSRLD` + `VPOR`. -/
theorem rol32_synth (x : BitVec 32) (imm : Nat) (h : imm < 32) :
    x.rotateLeft imm = (x <<< imm) ||| (x >>> (32 - imm)) := by
  rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt h]

/-- A uniform packed left shift via `vpslldW`: lane `k` of `vpslldW a c` is lane
    `k` of `a` shifted left by `c` (`VPSLLD`). -/
theorem vpslldW_uniform_lane (a : BitVec 256) (c : Nat) (k : Fin 8) :
    BitVec.extractLsb' (32 * k.val) 32 (vpslldW a c)
      = (BitVec.extractLsb' (32 * k.val) 32 a) <<< c := by
  fin_cases k <;>
    simp only [vpslldW, yOfDwordsW, yDwordW, Fin.foldl_succ, Fin.foldl_zero, Fin.isValue,
      Fin.val_zero, Fin.val_succ] <;>
    bv_decide

/-- A uniform packed right shift via `vpsrldW`: lane `k` of `vpsrldW a c` is lane
    `k` of `a` shifted right by `c` (`VPSRLD`). -/
theorem vpsrldW_uniform_lane (a : BitVec 256) (c : Nat) (k : Fin 8) :
    BitVec.extractLsb' (32 * k.val) 32 (vpsrldW a c)
      = (BitVec.extractLsb' (32 * k.val) 32 a) >>> c := by
  fin_cases k <;>
    simp only [vpsrldW, yOfDwordsW, yDwordW, Fin.foldl_succ, Fin.foldl_zero, Fin.isValue,
      Fin.val_zero, Fin.val_succ] <;>
    bv_decide

/-- **Packed rotate realized over the existing 256-bit op set.** Lane `k` of the
    AVX2 realization — `vpslldW a imm` OR-ed with `vpsrldW a (32 - imm)`, i.e.
    `VPSLLD ∨ VPSRLD` fused by `VPOR` — equals the scalar `BitVec.rotateLeft imm`
    of lane `k`, for `imm < 32`. Both shifts are ops already in the set, so this
    adds a packed rotate with no new `YmmOp` constructor. -/
theorem packedRol32_avx2_realizes256 (a : BitVec 256) (imm : Nat) (h : imm < 32) (k : Fin 8) :
    BitVec.extractLsb' (32 * k.val) 32 (vporW (vpslldW a imm) (vpsrldW a (32 - imm)))
      = (BitVec.extractLsb' (32 * k.val) 32 a).rotateLeft imm := by
  rw [vporW, BitVec.extractLsb'_or, vpslldW_uniform_lane, vpsrldW_uniform_lane,
    rol32_synth _ imm h]

/-- The packed rotate, read lane-by-lane, is the `LaneMap.scalarMap` of the scalar
    rotate over the eight unpacked lanes — the packed rotate is the lane-parallel
    map of `BitVec.rotateLeft imm`, the denotation shape the batch8 pass composes. -/
theorem v256PackRolW_is_scalar_laneMap (imm : Nat) (a : BitVec 256) :
    (fun k : Fin 8 => BitVec.extractLsb' (32 * k.val) 32 (v256PackRolW imm a))
      = CatCrypt.Crypto.SecureCompilation.VIR.LaneMap.scalarMap
          (fun x => x.rotateLeft imm)
          (fun k : Fin 8 => BitVec.extractLsb' (32 * k.val) 32 a) := by
  funext k
  rw [v256Rol32_lane]
  rfl

end CatCrypt.Crypto.Optimizer.PackedRotate256
