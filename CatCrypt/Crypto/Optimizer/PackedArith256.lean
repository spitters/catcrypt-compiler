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
* `yWordW_yOfWordsW` / `yDwordW_yOfDwordsW` / `yQwordW_yOfQwordsW` /
  `yByteW_yOfBytesW`: the packing round trips at 16/32/64/8-bit lanes.
* `vpaddwW_lane` … `vpblendwW_lane`, `vpmaddwdW_lane` … `vpsigndW_lane`: the
  16-bit and 32-bit lane equations of the ML-KEM AVX2 arithmetic.
* `vpermdW_lane`, `vpunpck{l,h}{dq,qdq}W_lane`, `vpack{ssdw,sswb}W_lane`,
  `vpsrldqW_half`, `vperm2i128W_half`: the cross-lane ops, stated per 128-bit
  half where the instruction acts per half.

The add op is stated over `yOfDwordsW` (its defining reassembly), so its lane
lemma is the packing round-trip proved lane-by-lane. The bitwise ops are the
whole-register operations `a ^^^ b` / `a ||| b` / `a &&& b`, so their lane
lemmas are the `BitVec.extractLsb'` distribution over the bitwise operation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.PackedArith256

open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
  (vpadddW vpxorW vporW vpandW vpsubdW vpmulldW vpandnW vpsradW vpsllvdW vpsrlvdW
    yDwordW yOfDwordsW yQwordW yOfQwordsW yWordW yOfWordsW yByteW yOfBytesW yHalfW
    satI32toI16W satI16toI8W perm2i128SelW
    vpaddwW vpsubwW vpmullwW vpmulhwW vpmaddwdW vpcmpgtwW vpcmpgtdW vpcmpeqdW
    vpsllwW vpsrlwW vpsrawW vpabsdW vpsigndW vpacksswbW vpackssdwW vpermdW
    vpunpckldqW vpunpckhdqW vpunpcklqdqW vpunpckhqdqW vpblendwW vpsrldqW vperm2i128W)

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

/-- **Variable packed left shift per lane.** Dword lane `k` of `vpsllvdW a b`
    (`VPSLLVD`, 8×`u32` shift left by a per-lane count vector) is lane `k` of `a`
    shifted left by the `.toNat` of lane `k` of `b`. -/
theorem vpsllvdW_lane (a b : BitVec 256) (k : Fin 8) :
    BitVec.extractLsb' (32 * k.val) 32 (vpsllvdW a b)
      = (BitVec.extractLsb' (32 * k.val) 32 a) <<< (BitVec.extractLsb' (32 * k.val) 32 b).toNat := by
  fin_cases k <;>
    simp only [vpsllvdW, yOfDwordsW, yDwordW, Fin.foldl_succ, Fin.foldl_zero, Fin.isValue,
      Fin.val_zero, Fin.val_succ] <;>
    bv_decide

/-- **Variable packed right shift per lane.** Dword lane `k` of `vpsrlvdW a b`
    (`VPSRLVD`, 8×`u32` shift right by a per-lane count vector) is lane `k` of `a`
    shifted right by the `.toNat` of lane `k` of `b`. -/
theorem vpsrlvdW_lane (a b : BitVec 256) (k : Fin 8) :
    BitVec.extractLsb' (32 * k.val) 32 (vpsrlvdW a b)
      = (BitVec.extractLsb' (32 * k.val) 32 a) >>> (BitVec.extractLsb' (32 * k.val) 32 b).toNat := by
  fin_cases k <;>
    simp only [vpsrlvdW, yOfDwordsW, yDwordW, Fin.foldl_succ, Fin.foldl_zero, Fin.isValue,
      Fin.val_zero, Fin.val_succ] <;>
    bv_decide

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

/-! ## Packing round trips

Reading lane `k` back out of a register assembled from a lane function `f`
gives `f k`, at each of the four lane widths. The lane function is first
rewritten through a `Nat`-indexed `g`, so that after unrolling every lane is the
atom `g n` for a numeral `n` and `bv_decide` sees one atom per lane. Every lane
equation below is an instance of one of these. -/

/-- Word lane `k` of `yOfWordsW f` is `f k`. -/
theorem yWordW_yOfWordsW (f : Fin 16 → BitVec 16) (k : Fin 16) :
    yWordW (yOfWordsW f) k.val = f k := by
  obtain ⟨g, rfl⟩ : ∃ g : Nat → BitVec 16, f = fun j => g j.val :=
    ⟨fun n => if h : n < 16 then f ⟨n, h⟩ else 0, funext fun j => by simp [j.isLt]⟩
  fin_cases k <;>
    simp only [yOfWordsW, yWordW, Fin.foldl_succ, Fin.foldl_zero, Fin.val_succ, Fin.isValue,
      Fin.coe_ofNat_eq_mod, Nat.reduceAdd, Nat.zero_mod] <;>
    bv_decide

/-- Dword lane `k` of `yOfDwordsW f` is `f k`. -/
theorem yDwordW_yOfDwordsW (f : Fin 8 → BitVec 32) (k : Fin 8) :
    yDwordW (yOfDwordsW f) k.val = f k := by
  obtain ⟨g, rfl⟩ : ∃ g : Nat → BitVec 32, f = fun j => g j.val :=
    ⟨fun n => if h : n < 8 then f ⟨n, h⟩ else 0, funext fun j => by simp [j.isLt]⟩
  fin_cases k <;>
    simp only [yOfDwordsW, yDwordW, Fin.foldl_succ, Fin.foldl_zero, Fin.val_succ, Fin.isValue,
      Fin.coe_ofNat_eq_mod, Nat.reduceAdd, Nat.zero_mod] <;>
    bv_decide

/-- Qword lane `k` of `yOfQwordsW f` is `f k`. -/
theorem yQwordW_yOfQwordsW (f : Fin 4 → BitVec 64) (k : Fin 4) :
    yQwordW (yOfQwordsW f) k.val = f k := by
  obtain ⟨g, rfl⟩ : ∃ g : Nat → BitVec 64, f = fun j => g j.val :=
    ⟨fun n => if h : n < 4 then f ⟨n, h⟩ else 0, funext fun j => by simp [j.isLt]⟩
  fin_cases k <;>
    simp only [yOfQwordsW, yQwordW, Fin.foldl_succ, Fin.foldl_zero, Fin.val_succ, Fin.isValue,
      Fin.coe_ofNat_eq_mod, Nat.reduceAdd, Nat.zero_mod] <;>
    bv_decide

/-- Byte lane `k` of `yOfBytesW f` is `f k`. -/
theorem yByteW_yOfBytesW (f : Fin 32 → BitVec 8) (k : Fin 32) :
    yByteW (yOfBytesW f) k.val = f k := by
  obtain ⟨g, rfl⟩ : ∃ g : Nat → BitVec 8, f = fun j => g j.val :=
    ⟨fun n => if h : n < 32 then f ⟨n, h⟩ else 0, funext fun j => by simp [j.isLt]⟩
  fin_cases k <;>
    simp only [yOfBytesW, yByteW, Fin.foldl_succ, Fin.foldl_zero, Fin.val_succ, Fin.isValue,
      Fin.coe_ofNat_eq_mod, Nat.reduceAdd, Nat.zero_mod] <;>
    bv_decide

/-- Word lane `n < 16` of `yOfWordsW f` is `f n`. -/
theorem yWordW_yOfWordsW_of_lt (f : Fin 16 → BitVec 16) (n : Nat) (hn : n < 16) :
    yWordW (yOfWordsW f) n = f ⟨n, hn⟩ :=
  yWordW_yOfWordsW f ⟨n, hn⟩

/-- Dword lane `n < 8` of `yOfDwordsW f` is `f n`. -/
theorem yDwordW_yOfDwordsW_of_lt (f : Fin 8 → BitVec 32) (n : Nat) (hn : n < 8) :
    yDwordW (yOfDwordsW f) n = f ⟨n, hn⟩ :=
  yDwordW_yOfDwordsW f ⟨n, hn⟩

/-- Qword lane `n < 4` of `yOfQwordsW f` is `f n`. -/
theorem yQwordW_yOfQwordsW_of_lt (f : Fin 4 → BitVec 64) (n : Nat) (hn : n < 4) :
    yQwordW (yOfQwordsW f) n = f ⟨n, hn⟩ :=
  yQwordW_yOfQwordsW f ⟨n, hn⟩

/-- Byte lane `n < 32` of `yOfBytesW f` is `f n`. -/
theorem yByteW_yOfBytesW_of_lt (f : Fin 32 → BitVec 8) (n : Nat) (hn : n < 32) :
    yByteW (yOfBytesW f) n = f ⟨n, hn⟩ :=
  yByteW_yOfBytesW f ⟨n, hn⟩

/-! ## The 16-bit lane arithmetic

The word-lane ops of ML-KEM's AVX2 arithmetic: wrapping add, subtract and low
product, the signed high product, the signed comparison mask, the three
immediate shifts, and the per-word blend. -/

/-- Word lane `k` of `vpaddwW a b` (`VPADDW`) is the wrapping sum of lane `k`
    of `a` and `b`. -/
theorem vpaddwW_lane (a b : BitVec 256) (k : Fin 16) :
    yWordW (vpaddwW a b) k.val = yWordW a k.val + yWordW b k.val :=
  yWordW_yOfWordsW _ k

/-- Word lane `k` of `vpsubwW a b` (`VPSUBW`) is the wrapping difference of
    lane `k` of `a` and `b`. -/
theorem vpsubwW_lane (a b : BitVec 256) (k : Fin 16) :
    yWordW (vpsubwW a b) k.val = yWordW a k.val - yWordW b k.val :=
  yWordW_yOfWordsW _ k

/-- Word lane `k` of `vpmullwW a b` (`VPMULLW`) is the low 16 bits of the
    product of lane `k` of `a` and `b`. -/
theorem vpmullwW_lane (a b : BitVec 256) (k : Fin 16) :
    yWordW (vpmullwW a b) k.val = yWordW a k.val * yWordW b k.val :=
  yWordW_yOfWordsW _ k

/-- Word lane `k` of `vpmulhwW a b` (`VPMULHW`) is bits `16‥31` of the signed
    32-bit product of lane `k` of `a` and `b`. -/
theorem vpmulhwW_lane (a b : BitVec 256) (k : Fin 16) :
    yWordW (vpmulhwW a b) k.val
      = BitVec.extractLsb' 16 16
          (BitVec.signExtend 32 (yWordW a k.val) * BitVec.signExtend 32 (yWordW b k.val)) :=
  yWordW_yOfWordsW _ k

/-- Word lane `k` of `vpcmpgtwW a b` (`VPCMPGTW`) is all ones when lane `k` of
    `a` is signed greater than lane `k` of `b`, and zero otherwise. -/
theorem vpcmpgtwW_lane (a b : BitVec 256) (k : Fin 16) :
    yWordW (vpcmpgtwW a b) k.val
      = if (yWordW b k.val).slt (yWordW a k.val) then BitVec.allOnes 16 else 0 :=
  yWordW_yOfWordsW _ k

/-- Word lane `k` of `vpsllwW a c` (`VPSLLW`) is lane `k` of `a` shifted left
    by `c`; a count of 16 or more gives zero. -/
theorem vpsllwW_lane (a : BitVec 256) (c : Nat) (k : Fin 16) :
    yWordW (vpsllwW a c) k.val = yWordW a k.val <<< c :=
  yWordW_yOfWordsW _ k

/-- Word lane `k` of `vpsrlwW a c` (`VPSRLW`) is lane `k` of `a` shifted right
    by `c`, zero filled; a count of 16 or more gives zero. -/
theorem vpsrlwW_lane (a : BitVec 256) (c : Nat) (k : Fin 16) :
    yWordW (vpsrlwW a c) k.val = yWordW a k.val >>> c :=
  yWordW_yOfWordsW _ k

/-- Word lane `k` of `vpsrawW a c` (`VPSRAW`) is lane `k` of `a` shifted right
    by `c` with the sign replicated. -/
theorem vpsrawW_lane (a : BitVec 256) (c : Nat) (k : Fin 16) :
    yWordW (vpsrawW a c) k.val = (yWordW a k.val).sshiftRight c :=
  yWordW_yOfWordsW _ k

/-- Word lane `k` of `vpblendwW a b imm` (`VPBLENDW`) is lane `k` of `b` when
    bit `k mod 8` of `imm` is set and lane `k` of `a` otherwise. -/
theorem vpblendwW_lane (a b : BitVec 256) (imm : Nat) (k : Fin 16) :
    yWordW (vpblendwW a b imm) k.val
      = if (imm >>> (k.val % 8)) &&& 1 = 1 then yWordW b k.val else yWordW a k.val :=
  yWordW_yOfWordsW _ k

/-! ## The 32-bit lane arithmetic -/

/-- Dword lane `k` of `vpmaddwdW a b` (`VPMADDWD`) is the 32-bit sum of the
    signed products of word lanes `2k` and `2k+1` of `a` and `b`. -/
theorem vpmaddwdW_lane (a b : BitVec 256) (k : Fin 8) :
    yDwordW (vpmaddwdW a b) k.val
      = BitVec.signExtend 32 (yWordW a (2 * k.val)) * BitVec.signExtend 32 (yWordW b (2 * k.val))
        + BitVec.signExtend 32 (yWordW a (2 * k.val + 1))
          * BitVec.signExtend 32 (yWordW b (2 * k.val + 1)) :=
  yDwordW_yOfDwordsW _ k

/-- Dword lane `k` of `vpcmpgtdW a b` (`VPCMPGTD`) is all ones when lane `k` of
    `a` is signed greater than lane `k` of `b`, and zero otherwise. -/
theorem vpcmpgtdW_lane (a b : BitVec 256) (k : Fin 8) :
    yDwordW (vpcmpgtdW a b) k.val
      = if (yDwordW b k.val).slt (yDwordW a k.val) then BitVec.allOnes 32 else 0 :=
  yDwordW_yOfDwordsW _ k

/-- Dword lane `k` of `vpcmpeqdW a b` (`VPCMPEQD`) is all ones when lane `k` of
    `a` equals lane `k` of `b`, and zero otherwise. -/
theorem vpcmpeqdW_lane (a b : BitVec 256) (k : Fin 8) :
    yDwordW (vpcmpeqdW a b) k.val
      = if yDwordW a k.val = yDwordW b k.val then BitVec.allOnes 32 else 0 :=
  yDwordW_yOfDwordsW _ k

/-- Dword lane `k` of `vpabsdW a` (`VPABSD`) is the absolute value of the signed
    lane `k` of `a`. -/
theorem vpabsdW_lane (a : BitVec 256) (k : Fin 8) :
    yDwordW (vpabsdW a) k.val = (yDwordW a k.val).abs :=
  yDwordW_yOfDwordsW _ k

/-- Dword lane `k` of `vpsigndW a b` (`VPSIGND`) is lane `k` of `a` negated,
    zeroed or kept as lane `k` of `b` is negative, zero or positive. -/
theorem vpsigndW_lane (a b : BitVec 256) (k : Fin 8) :
    yDwordW (vpsigndW a b) k.val
      = if (yDwordW b k.val).msb then -(yDwordW a k.val)
        else if yDwordW b k.val = 0 then 0 else yDwordW a k.val :=
  yDwordW_yOfDwordsW _ k

/-! ## The cross-lane ops

Pack and unpack act on each 128-bit half `h` separately; `vpermd` and
`vperm2i128` cross the halves. -/

/-- Dword lane `k` of `vpermdW idx a` (`VPERMD`) is dword `idx[k] mod 8` of
    `a`. -/
theorem vpermdW_lane (idx a : BitVec 256) (k : Fin 8) :
    yDwordW (vpermdW idx a) k.val = yDwordW a ((yDwordW idx k.val).toNat % 8) :=
  yDwordW_yOfDwordsW _ k

/-- In half `h`, `vpunpckldqW a b` (`VPUNPCKLDQ`) interleaves dwords `4h` and
    `4h+1` of `a` and `b`: dword `4h+2j` is `a[4h+j]` and dword `4h+2j+1` is
    `b[4h+j]`, for `j < 2`. -/
theorem vpunpckldqW_lane (a b : BitVec 256) (h j : Fin 2) :
    yDwordW (vpunpckldqW a b) (4 * h.val + 2 * j.val) = yDwordW a (4 * h.val + j.val) ∧
    yDwordW (vpunpckldqW a b) (4 * h.val + 2 * j.val + 1) = yDwordW b (4 * h.val + j.val) := by
  simp (disch := omega) only [vpunpckldqW, yDwordW_yOfDwordsW_of_lt]
  fin_cases h <;> fin_cases j <;> simp

/-- In half `h`, `vpunpckhdqW a b` (`VPUNPCKHDQ`) interleaves dwords `4h+2` and
    `4h+3` of `a` and `b`: dword `4h+2j` is `a[4h+2+j]` and dword `4h+2j+1` is
    `b[4h+2+j]`, for `j < 2`. -/
theorem vpunpckhdqW_lane (a b : BitVec 256) (h j : Fin 2) :
    yDwordW (vpunpckhdqW a b) (4 * h.val + 2 * j.val) = yDwordW a (4 * h.val + 2 + j.val) ∧
    yDwordW (vpunpckhdqW a b) (4 * h.val + 2 * j.val + 1)
      = yDwordW b (4 * h.val + 2 + j.val) := by
  simp (disch := omega) only [vpunpckhdqW, yDwordW_yOfDwordsW_of_lt]
  fin_cases h <;> fin_cases j <;> simp

/-- In half `h`, `vpunpcklqdqW a b` (`VPUNPCKLQDQ`) has qwords `a[2h], b[2h]`. -/
theorem vpunpcklqdqW_lane (a b : BitVec 256) (h : Fin 2) :
    yQwordW (vpunpcklqdqW a b) (2 * h.val) = yQwordW a (2 * h.val) ∧
    yQwordW (vpunpcklqdqW a b) (2 * h.val + 1) = yQwordW b (2 * h.val) := by
  simp (disch := omega) only [vpunpcklqdqW, yQwordW_yOfQwordsW_of_lt]
  fin_cases h <;> simp

/-- In half `h`, `vpunpckhqdqW a b` (`VPUNPCKHQDQ`) has qwords
    `a[2h+1], b[2h+1]`. -/
theorem vpunpckhqdqW_lane (a b : BitVec 256) (h : Fin 2) :
    yQwordW (vpunpckhqdqW a b) (2 * h.val) = yQwordW a (2 * h.val + 1) ∧
    yQwordW (vpunpckhqdqW a b) (2 * h.val + 1) = yQwordW b (2 * h.val + 1) := by
  simp (disch := omega) only [vpunpckhqdqW, yQwordW_yOfQwordsW_of_lt]
  fin_cases h <;> simp

/-- In half `h`, `vpackssdwW a b` (`VPACKSSDW`) has as word `8h+j` the
    saturated dword `a[4h+j]` and as word `8h+4+j` the saturated dword
    `b[4h+j]`, for `j < 4`. -/
theorem vpackssdwW_lane (a b : BitVec 256) (h : Fin 2) (j : Fin 4) :
    yWordW (vpackssdwW a b) (8 * h.val + j.val) = satI32toI16W (yDwordW a (4 * h.val + j.val)) ∧
    yWordW (vpackssdwW a b) (8 * h.val + 4 + j.val)
      = satI32toI16W (yDwordW b (4 * h.val + j.val)) := by
  simp (disch := omega) only [vpackssdwW, yWordW_yOfWordsW_of_lt]
  fin_cases h <;> fin_cases j <;> simp

/-- In half `h`, `vpacksswbW a b` (`VPACKSSWB`) has as byte `16h+j` the
    saturated word `a[8h+j]` and as byte `16h+8+j` the saturated word
    `b[8h+j]`, for `j < 8`. -/
theorem vpacksswbW_lane (a b : BitVec 256) (h : Fin 2) (j : Fin 8) :
    yByteW (vpacksswbW a b) (16 * h.val + j.val) = satI16toI8W (yWordW a (8 * h.val + j.val)) ∧
    yByteW (vpacksswbW a b) (16 * h.val + 8 + j.val)
      = satI16toI8W (yWordW b (8 * h.val + j.val)) := by
  simp (disch := omega) only [vpacksswbW, yByteW_yOfBytesW_of_lt]
  fin_cases h <;> fin_cases j <;> simp

/-- Half `h` of `vpsrldqW a c` (`VPSRLDQ`) is half `h` of `a` shifted right by
    `c` bytes, zero filled; a count of 16 or more clears the half. -/
theorem vpsrldqW_half (a : BitVec 256) (c : Nat) (h : Fin 2) :
    yHalfW (vpsrldqW a c) h.val = yHalfW a h.val >>> (8 * c) := by
  fin_cases h <;> simp only [vpsrldqW, yHalfW] <;> bv_decide

/-- Half `h` of `vperm2i128W a b imm` (`VPERM2I128`) is the half that the
    control field in bits `4h‥4h+3` of `imm` selects. -/
theorem vperm2i128W_half (a b : BitVec 256) (imm : Nat) (h : Fin 2) :
    yHalfW (vperm2i128W a b imm) h.val = perm2i128SelW a b (imm >>> (4 * h.val)) := by
  fin_cases h <;>
    simp only [vperm2i128W, yHalfW, Nat.mul_zero, Nat.mul_one, Nat.shiftRight_zero] <;>
    bv_decide

end CatCrypt.Crypto.Optimizer.PackedArith256
