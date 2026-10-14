/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.FinCases
public import Std.Tactic.BVDecide

/-!
# Packed lane rotate for the `vsimd` op set

The five packable ALU ops of the SLP vectorizer (`SLPVectorize.LaneOp`:
`add`/`xor`/`or`/`shl`/`shr`) lower to `VPADDD`/`VPXOR`/`VPOR`/`VPSLLD`/`VPSRLD`.
They have no packed rotate, which SHA-256's Σ/σ mixing needs (each `Σ0`, `Σ1`,
`σ0`, `σ1` is a XOR of three per-lane rotates of a 32-bit word). This file adds
the packed rotate and its per-lane denotation, in the same 4×`u32` lane model as
`v128Pack32_lane` and `SLPVectorize.slpGroup_denote`.

## Main results

* `v128PackRolW`: the semantic 4×`u32` packed rotate.
* `v128Rol32_lane`: lane `k` of the packed rotate equals the scalar `rotateLeft`.
* `packedRol32_avx2_realizes`: the rotate expressed over the existing `vsimd` ops
  (`VPSLLD`, `VPSRLD`, `VPOR`) realizes the per-lane scalar rotate.
* `v128PackRolW_is_scalar_laneMap`: the packed rotate is `LaneMap.scalarMap` of the
  scalar rotate — the denotation-preservation shape a batch pass composes.

On AVX2 (the SLH-DSA multi-buffer target) there is no single-instruction packed
dword rotate — `VPROLD` is AVX-512. The rotate is realized as a three-op macro
over ops already in the set: `VPSLLD` + `VPSRLD` + `VPOR`, i.e.
`rol(a, imm) = (a <<< imm) ||| (a >>> (w - imm))` per lane. So no new `SimdOp`
constructor and no new byte encoder are required; the packed rotate is a derived
op whose denotation is proved from the existing `v128PackLanesW` ops.

## Contents

* `v128PackRolW` — the semantic packed rotate (4×`u32`): lane `j` rotates by `imm`.
* `v128Rol32_lane` — per-lane realization: lane `k` of the packed rotate equals
  the scalar `BitVec.rotateLeft imm` of lane `k`. The `vmap`-style denotation
  obligation the vectorizer carries for every lane op.
* `rol32_synth` — the scalar rotate equals the `shl`/`shr`/`or` synthesis.
* `vpslld_uniform_lane` / `vpsrld_uniform_lane` — a uniform-immediate packed shift
  (`VPSLLD`/`VPSRLD` with a broadcast count) via the real `v128PackLanesW` op is
  the per-lane scalar shift.
* `packedRol32_avx2_realizes` — the composite: lane `k` of the AVX2 realization
  (`v128PackLanesW .shl` `|||` `v128PackLanesW .shr`, with broadcast counts)
  equals the scalar `rotateLeft imm`, for `imm < 32`. This is the packed rotate
  expressed and proved entirely over ops already in the `vsimd` set.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.PackedRotate

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp v128PackLanesW)

/-- **Generic 4-lane packing round-trip.** Reading lane `k` (the `[32k, 32k+32)`
    slice) of a fold-`OR` of `setWidth`-widened, lane-shifted `u32` values returns
    the `k`-th lane value `g k`, for any per-lane function `g`. This is the packing
    kernel behind every 4×`u32` lane lemma; `v128Pack32_lane` is its instance at
    `g j = bop.apply (lane j a) (lane j b)`, and `v128Rol32_lane` its instance at
    `g j = (lane j a).rotateLeft imm`. -/
theorem packFold32_lane (g : Nat → BitVec 32) (k : Fin 4) :
    BitVec.extractLsb' (32 * k.val) 32
      ((List.range 4).foldl (fun acc j => acc ||| ((g j).setWidth 128 <<< (32 * j))) 0)
      = g k.val := by
  fin_cases k <;> simp only [List.range, List.range.loop, List.foldl] <;> bv_decide

/-- The semantic packed lane rotate on a 128-bit XMM register (4×`u32`): lane `j`
    of the result is lane `j` of `a` rotated left by `imm`. This is the packed
    denotation a `VPROLD`/AVX2-macro rotate realizes — the rotate analogue of
    `v128PackLanesW`. -/
def v128PackRolW (imm : Nat) (a : BitVec 128) : BitVec 128 :=
  (List.range 4).foldl
    (fun acc j =>
      acc ||| (((BitVec.extractLsb' (32 * j) 32 a).rotateLeft imm).setWidth 128 <<< (32 * j))) 0

/-- **Per-lane realization of the packed rotate.** Reading lane `k` of
    `v128PackRolW imm a` equals the scalar `BitVec.rotateLeft imm` of lane `k` of
    `a`. Holds for an arbitrary (symbolic) rotate amount `imm`. This is the
    `vmap₂_eq_scalar`-style denotation obligation: the packed rotate computes the
    per-lane scalar rotate. -/
theorem v128Rol32_lane (imm : Nat) (a : BitVec 128) (k : Fin 4) :
    BitVec.extractLsb' (32 * k.val) 32 (v128PackRolW imm a)
      = (BitVec.extractLsb' (32 * k.val) 32 a).rotateLeft imm :=
  packFold32_lane (fun j => (BitVec.extractLsb' (32 * j) 32 a).rotateLeft imm) k

/-- The scalar 32-bit rotate is the `shl`/`shr`/`or` synthesis
    `(x <<< imm) ||| (x >>> (32 - imm))`, for `imm < 32`. This is the AVX2
    realization of one lane's rotate as `VPSLLD` + `VPSRLD` + `VPOR`. -/
theorem rol32_synth (x : BitVec 32) (imm : Nat) (h : imm < 32) :
    x.rotateLeft imm = (x <<< imm) ||| (x >>> (32 - imm)) := by
  rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt h]

/-- Broadcast a 32-bit count into all four `u32` lanes of a 128-bit register — the
    immediate operand of a uniform packed shift (`VPSLLD xmm, imm` reads one count
    for every lane). -/
def bcast32 (c : BitVec 32) : BitVec 128 :=
  (c.setWidth 128) ||| (c.setWidth 128 <<< 32) ||| (c.setWidth 128 <<< 64) ||| (c.setWidth 128 <<< 96)

/-- A uniform packed left shift via the real `v128PackLanesW 32 .shl` op with a
    broadcast count: lane `k` is lane `k` of `a` shifted left by `c` (`VPSLLD`). -/
theorem vpslld_uniform_lane (a : BitVec 128) (c : BitVec 32) (k : Fin 4) :
    BitVec.extractLsb' (32 * k.val) 32 (v128PackLanesW 32 .shl a (bcast32 c))
      = (BitVec.extractLsb' (32 * k.val) 32 a) <<< c := by
  fin_cases k <;>
    simp only [v128PackLanesW, bcast32, List.range, List.range.loop, List.foldl, JasminBinOp.applyLane] <;>
    bv_decide

/-- A uniform packed right shift via the real `v128PackLanesW 32 .shr` op with a
    broadcast count: lane `k` is lane `k` of `a` shifted right by `c` (`VPSRLD`). -/
theorem vpsrld_uniform_lane (a : BitVec 128) (c : BitVec 32) (k : Fin 4) :
    BitVec.extractLsb' (32 * k.val) 32 (v128PackLanesW 32 .shr a (bcast32 c))
      = (BitVec.extractLsb' (32 * k.val) 32 a) >>> c := by
  fin_cases k <;>
    simp only [v128PackLanesW, bcast32, List.range, List.range.loop, List.foldl, JasminBinOp.applyLane] <;>
    bv_decide

/-- **Packed rotate realized over the existing `vsimd` op set.** Lane `k` of the
    AVX2 realization — `v128PackLanesW 32 .shl a (bcast imm)` OR-ed with
    `v128PackLanesW 32 .shr a (bcast (32 - imm))`, i.e. `VPSLLD ∨ VPSRLD` fused by
    `VPOR` — equals the scalar `BitVec.rotateLeft imm` of lane `k`, for `imm < 32`.
    Both shifts are ops already in the set, so this adds a packed rotate with no
    new `SimdOp` constructor. -/
theorem packedRol32_avx2_realizes (a : BitVec 128) (imm : Nat) (h : imm < 32) (k : Fin 4) :
    BitVec.extractLsb' (32 * k.val) 32
      ((v128PackLanesW 32 .shl a (bcast32 (BitVec.ofNat 32 imm)))
        ||| (v128PackLanesW 32 .shr a (bcast32 (BitVec.ofNat 32 (32 - imm)))))
      = (BitVec.extractLsb' (32 * k.val) 32 a).rotateLeft imm := by
  rw [BitVec.extractLsb'_or, vpslld_uniform_lane, vpsrld_uniform_lane, rol32_synth _ imm h]
  congr 1
  · rw [BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : imm < 2 ^ 32)]
  · rw [BitVec.ushiftRight_eq', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 32 - imm < 2 ^ 32)]

/-- The packed rotate, read lane-by-lane, is the `LaneMap.scalarMap` of the scalar
    rotate over the four unpacked lanes — the packed rotate is the lane-parallel
    map of `BitVec.rotateLeft imm`. Instance of the lane-map denotation idiom
    (`LaneMap.laneMap_eq_scalarMap`) for the packed rotate. -/
theorem v128PackRolW_is_scalar_laneMap (imm : Nat) (a : BitVec 128) :
    (fun k : Fin 4 => BitVec.extractLsb' (32 * k.val) 32 (v128PackRolW imm a))
      = CatCrypt.Crypto.SecureCompilation.VIR.LaneMap.scalarMap
          (fun x => x.rotateLeft imm)
          (fun k : Fin 4 => BitVec.extractLsb' (32 * k.val) 32 a) := by
  funext k
  rw [v128Rol32_lane]
  rfl

end CatCrypt.Crypto.Optimizer.PackedRotate
