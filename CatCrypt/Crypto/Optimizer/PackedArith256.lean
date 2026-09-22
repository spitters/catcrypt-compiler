/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.YmmDialectOps
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public import CatCrypt.Crypto.Optimizer.PackedRotate256
public import Mathlib.Tactic.FinCases
public import Std.Tactic.BVDecide

/-!
# Packed lane arithmetic and bitwise ops for the 256-bit YMM op set (AVX2 8-lane, SLH-DSA batch8)

The SLH-DSA multi-buffer batch8 transform hashes eight independent SHA-256 lanes
in a 256-bit YMM register (8×`u32`). Alongside the packed rotate/shift half in
`PackedRotate256.lean`, the message schedule and compression use packed dword
add (`VPADDD`) and the packed bitwise ops (`VPXOR`/`VPOR`/`VPAND`). This file
proves that each such packed op computes the scalar op on every one of the eight
dword lanes, in the 8×`u32` lane model of `yDwordW`/`yOfDwordsW`.

## Main results

* `vpadddW_lane`: dword lane `k` of `vpadddW a b` is `yDwordW a k + yDwordW b k`.
* `vpxorW_lane`: dword lane `k` of `vpxorW a b` is `yDwordW a k ^^^ yDwordW b k`.
* `vporW_lane`: dword lane `k` of `vporW a b` is `yDwordW a k ||| yDwordW b k`.
* `vpandW_lane`: dword lane `k` of `vpandW a b` is `yDwordW a k &&& yDwordW b k`.
* `vpadddW_is_scalar_vmap₂` / `vpxorW_is_scalar_vmap₂` / `vporW_is_scalar_vmap₂`
  / `vpandW_is_scalar_vmap₂`: the packed op, read lane-by-lane, is the binary
  lane-parallel map `LaneMap.vmap₂` of the scalar op over the eight unpacked
  lanes — the denotation shape the batch8 pass composes.

The add op is stated over `yOfDwordsW` (its defining reassembly), so its lane
lemma is the packing round-trip proved lane-by-lane. The bitwise ops are the
whole-register operations `a ^^^ b` / `a ||| b` / `a &&& b`, so their lane
lemmas are the `BitVec.extractLsb'` distribution over the bitwise operation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.PackedArith256

open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
  (vpadddW vpxorW vporW vpandW vpsubdW vpmulldW vpandnW vpsradW yDwordW yOfDwordsW)

/-- **Packed 8-lane dword add per lane.** Dword lane `k` of `vpadddW a b`
    (`VPADDD`, 8×`u32` wrapping add) is the sum of lane `k` of `a` and lane `k`
    of `b`. -/
theorem vpadddW_lane (a b : BitVec 256) (k : Fin 8) :
    yDwordW (vpadddW a b) k.val = yDwordW a k.val + yDwordW b k.val := by
  fin_cases k <;>
    simp only [vpadddW, yOfDwordsW, yDwordW, Fin.foldl_succ, Fin.foldl_zero, Fin.isValue,
      Fin.val_zero, Fin.val_succ] <;>
    bv_decide

/-- **Packed dword XOR per lane.** Dword lane `k` of `vpxorW a b` (`VPXOR`,
    bitwise XOR of the two registers) is the XOR of lane `k` of `a` and `b`. -/
theorem vpxorW_lane (a b : BitVec 256) (k : Fin 8) :
    yDwordW (vpxorW a b) k.val = yDwordW a k.val ^^^ yDwordW b k.val := by
  simp only [vpxorW, yDwordW, BitVec.extractLsb'_xor]

/-- **Packed dword OR per lane.** Dword lane `k` of `vporW a b` (`VPOR`, bitwise
    OR of the two registers) is the OR of lane `k` of `a` and `b`. -/
theorem vporW_lane (a b : BitVec 256) (k : Fin 8) :
    yDwordW (vporW a b) k.val = yDwordW a k.val ||| yDwordW b k.val := by
  simp only [vporW, yDwordW, BitVec.extractLsb'_or]

/-- **Packed dword AND per lane.** Dword lane `k` of `vpandW a b` (`VPAND`,
    bitwise AND of the two registers) is the AND of lane `k` of `a` and `b`. -/
theorem vpandW_lane (a b : BitVec 256) (k : Fin 8) :
    yDwordW (vpandW a b) k.val = yDwordW a k.val &&& yDwordW b k.val := by
  simp only [vpandW, yDwordW, BitVec.extractLsb'_and]

/-! ## Binary lane-parallel-map packaging

Each packed op, read lane-by-lane, is `LaneMap.vmap₂` of the scalar op over the
eight unpacked lanes — the binary analogue of `PackedRotate256`'s
`v256PackRolW_is_scalar_laneMap`, and the denotation shape the batch8 pass
composes. -/

/-- The packed dword add is the binary lane-parallel map `LaneMap.vmap₂ (· + ·)`
    of the scalar add over the eight unpacked lanes. -/
theorem vpadddW_is_scalar_vmap₂ (a b : BitVec 256) :
    (fun k : Fin 8 => yDwordW (vpadddW a b) k.val)
      = CatCrypt.Crypto.SecureCompilation.VIR.LaneMap.vmap₂ (· + ·)
          (fun k : Fin 8 => yDwordW a k.val)
          (fun k : Fin 8 => yDwordW b k.val) := by
  funext k
  rw [vpadddW_lane]
  rfl

/-- The packed dword XOR is the binary lane-parallel map `LaneMap.vmap₂ (· ^^^ ·)`
    of the scalar XOR over the eight unpacked lanes. -/
theorem vpxorW_is_scalar_vmap₂ (a b : BitVec 256) :
    (fun k : Fin 8 => yDwordW (vpxorW a b) k.val)
      = CatCrypt.Crypto.SecureCompilation.VIR.LaneMap.vmap₂ (· ^^^ ·)
          (fun k : Fin 8 => yDwordW a k.val)
          (fun k : Fin 8 => yDwordW b k.val) := by
  funext k
  rw [vpxorW_lane]
  rfl

/-- The packed dword OR is the binary lane-parallel map `LaneMap.vmap₂ (· ||| ·)`
    of the scalar OR over the eight unpacked lanes. -/
theorem vporW_is_scalar_vmap₂ (a b : BitVec 256) :
    (fun k : Fin 8 => yDwordW (vporW a b) k.val)
      = CatCrypt.Crypto.SecureCompilation.VIR.LaneMap.vmap₂ (· ||| ·)
          (fun k : Fin 8 => yDwordW a k.val)
          (fun k : Fin 8 => yDwordW b k.val) := by
  funext k
  rw [vporW_lane]
  rfl

/-- The packed dword AND is the binary lane-parallel map `LaneMap.vmap₂ (· &&& ·)`
    of the scalar AND over the eight unpacked lanes. -/
theorem vpandW_is_scalar_vmap₂ (a b : BitVec 256) :
    (fun k : Fin 8 => yDwordW (vpandW a b) k.val)
      = CatCrypt.Crypto.SecureCompilation.VIR.LaneMap.vmap₂ (· &&& ·)
          (fun k : Fin 8 => yDwordW a k.val)
          (fun k : Fin 8 => yDwordW b k.val) := by
  funext k
  rw [vpandW_lane]
  rfl

/-! ## The arithmetic of lattice coefficients

The lanes `batch8` needs to widen per-coefficient lattice arithmetic: subtract,
the low-word product, the and-not of a mask, and the sign-replicating shift that
Montgomery and Barrett reductions use. -/

/-- **Packed dword subtract per lane.** Lane `k` of `vpsubdW a b` (`VPSUBD`) is
    the wrapping difference of lane `k` of `a` and `b`. -/
theorem vpsubdW_lane (a b : BitVec 256) (k : Fin 8) :
    yDwordW (vpsubdW a b) k.val = yDwordW a k.val - yDwordW b k.val := by
  fin_cases k <;>
    simp only [vpsubdW, yOfDwordsW, yDwordW, Fin.foldl_succ, Fin.foldl_zero, Fin.isValue,
      Fin.val_zero, Fin.val_succ] <;>
    bv_decide

/-- **Packed dword low product per lane.** Lane `k` of `vpmulldW a b` (`VPMULLD`)
    is the low 32 bits of the product of lane `k` of `a` and `b`. -/
theorem vpmulldW_lane (a b : BitVec 256) (k : Fin 8) :
    yDwordW (vpmulldW a b) k.val = yDwordW a k.val * yDwordW b k.val := by
  fin_cases k <;>
    simp only [vpmulldW, yOfDwordsW, yDwordW, Fin.foldl_succ, Fin.foldl_zero, Fin.isValue,
      Fin.val_zero, Fin.val_succ] <;>
    bv_decide

/-- **Packed and-not per lane.** Lane `k` of `vpandnW a b` (`VPANDN`) is the
    complement of lane `k` of `a` AND-ed with lane `k` of `b`. -/
theorem vpandnW_lane (a b : BitVec 256) (k : Fin 8) :
    yDwordW (vpandnW a b) k.val = (~~~yDwordW a k.val) &&& yDwordW b k.val := by
  fin_cases k <;> simp only [vpandnW, yDwordW] <;> bv_decide

/-- **Packed arithmetic shift right per lane.** Lane `k` of `vpsradW a c`
    (`VPSRAD`) is lane `k` of `a` shifted right by `c` with the sign replicated. -/
theorem vpsradW_uniform_lane (a : BitVec 256) (c : Nat) (k : Fin 8) :
    BitVec.extractLsb' (32 * k.val) 32 (vpsradW a c)
      = (BitVec.extractLsb' (32 * k.val) 32 a).sshiftRight c := by
  fin_cases k <;>
    simp only [vpsradW, yOfDwordsW, yDwordW, Fin.foldl_succ, Fin.foldl_zero, Fin.isValue,
      Fin.val_zero, Fin.val_succ] <;>
    bv_decide

end CatCrypt.Crypto.Optimizer.PackedArith256
