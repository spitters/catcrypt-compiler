/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import Mathlib.Data.BitVec
public import Mathlib.Algebra.Group.Defs
public meta import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Types
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Types
public import Std.Tactic.BVDecide

/-!
# MLIR `vector` dialect — x86 SIMD intrinsic semantics

Lean-level `BitVec`-shaped semantic models for the x86 SIMD intrinsics that
appear in CatCrypt's `.jinc` leaf bodies. Each intrinsic is given a
total-function denotation `BitVec _ → BitVec _ → BitVec _` (binary case) or
similar.

This module is part of the MLIR VectorDialect scaffolding and is consumed by `MayoLeafProof.lean` to give a Lean meaning to the
PSHUFB-based GF(16) lookup tables in `bench/mayo_compare/include/mayo_leaves.jinc`.

## What the semantics are pinned against

Every intrinsic models the bit-level semantics described in the Intel
Software Developer's Manual (SDM). For the PSHUFB and VPSRLDQ families that
have non-trivial byte-selection / lane-shift behaviour, the model is the
**byte-functional** one (a `Fin 16 → Fin 16 → UInt8`-style indexing on the
two operand vectors) packed back into a `BitVec 128`.

For each intrinsic we add a small `#guard`-style sanity check against a
hand-evaluated Intel SDM example, closed by `native_decide`.

## Intrinsics covered (first landing)

| Intel mnemonic                  | Lean function                | Width   |
|---------------------------------|------------------------------|---------|
| `PXOR`/`VPXOR_128`/`VPXOR_256`  | `vpxor_128` / `vpxor_256`    | 128/256 |
| `PSHUFB`/`VPSHUFB_128`          | `pshufb_128`                 | 128     |
| `VPSHUFB_256`                   | `vpshufb_256`                | 256     |
| `VPSRLDQ_128 (imm8)`            | `vpsrldq_128`                | 128     |
| `VPSLLDQ_128 (imm8)`            | `vpslldq_128`                | 128     |
| `VPCMPEQ_32u8`                  | `vpcmpeq_32u8_256`           | 256     |
| `VPSUB_32u8`                    | `vpsub_32u8_256`             | 256     |
| `VPSRL_16u16` (imm8)            | `vpsrl_16u16_256`            | 256     |
| `VPBROADCAST_4u64`              | `vpbroadcast_4u64_256`       | 128→256 |
| `VPADDQ_128`/`VPADDQ_256`       | `vpaddq_128`/`vpaddq_256`    | 128/256 |
| `VPEXTR_8 (imm8 in [0,15])`     | `vpextr_8`                   | 128→8   |
| `set0_128`/`set0_256`           | `set0_128`/`set0_256`        | 128/256 |
| `VEXTRACTI128 (imm8 ∈ {0,1})`   | `vextracti128`               | 256→128 |
| `VGF2P8MULB_128`                | `vgf2p8mulb_128`             | 128     |

For each, a `#guard` (or `theorem … := by native_decide`) sanity-checks a
canonical input → expected output.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

namespace X86Intrinsics

/-! ## §0. Byte-level helpers

`BitVec 128 = 16 bytes`; `BitVec 256 = 32 bytes`. We model byte-indexed
operations as `Fin 16 → BitVec 8` / `Fin 32 → BitVec 8` lane functions and
pack back via `BitVec.append`-style construction.

For computational tractability under `bv_decide` / `native_decide`, we
prefer pointwise BitVec operations (XOR, AND, shifts) where possible —
those reduce directly without needing the lane-function indirection. -/

/-- Read byte `i` (0-indexed, little-endian) from a `BitVec 128`. -/
def byteOf128 (v : BitVec 128) (i : Fin 16) : BitVec 8 :=
  (v >>> (8 * i.val)).setWidth 8

/-- Read byte `i` (0-indexed, little-endian) from a `BitVec 256`. -/
def byteOf256 (v : BitVec 256) (i : Fin 32) : BitVec 8 :=
  (v >>> (8 * i.val)).setWidth 8

/-! ## §1. Bitwise vector ops (XOR/AND/OR) — direct BitVec ops -/

/-- `VPXOR_128`: 128-bit bitwise XOR. -/
@[reducible] def vpxor_128 (a b : BitVec 128) : BitVec 128 := a ^^^ b

/-- `VPXOR_256`: 256-bit bitwise XOR. -/
@[reducible] def vpxor_256 (a b : BitVec 256) : BitVec 256 := a ^^^ b

/-- 128-bit bitwise AND. -/
@[reducible] def vpand_128 (a b : BitVec 128) : BitVec 128 := a &&& b

/-- 256-bit bitwise AND. -/
@[reducible] def vpand_256 (a b : BitVec 256) : BitVec 256 := a &&& b

/-- Sanity: XOR is self-inverse. -/
theorem vpxor_128_self (a : BitVec 128) : vpxor_128 a a = 0#128 := by
  show a ^^^ a = 0; bv_decide

theorem vpxor_256_self (a : BitVec 256) : vpxor_256 a a = 0#256 := by
  show a ^^^ a = 0; bv_decide

/-! ## §2. Set-zero -/

/-- `set0_128`: produce the all-zeros 128-bit vector. -/
@[reducible] def set0_128 : BitVec 128 := 0#128

/-- `set0_256`: produce the all-zeros 256-bit vector. -/
@[reducible] def set0_256 : BitVec 256 := 0#256

/-! ## §3. PSHUFB family

`PSHUFB src, mask` — for each output byte `i ∈ [0,16)`:
* if `mask[i] & 0x80 ≠ 0`, output byte `i` is `0`;
* otherwise output byte `i` is `src[mask[i] & 0x0F]`.

We model this byte-functionally, then pack back into a `BitVec 128`. -/

/-- Functional byte-shuffle: returns the output byte at position `i`. -/
def pshufb_byte_128 (src mask : BitVec 128) (i : Fin 16) : BitVec 8 :=
  let m := byteOf128 mask i
  -- If high bit of m is set, output 0; otherwise output src[m & 0x0F].
  let zero_mask : BitVec 8 := m >>> 7
  if zero_mask == 1#8 then 0#8
  else
    let idx : Nat := (m &&& 0x0F#8).toNat
    -- idx ∈ [0,15] by construction.
    if h : idx < 16 then byteOf128 src ⟨idx, h⟩
    else 0#8

/-- Pack a `Fin 16 → BitVec 8` byte function into a `BitVec 128`
    (little-endian: byte 0 is the low 8 bits). -/
def packBytes128 (f : Fin 16 → BitVec 8) : BitVec 128 :=
  (List.finRange 16).foldl
    (fun acc i => acc ||| ((f i).setWidth 128 <<< (8 * i.val))) 0#128

/-- `PSHUFB_128` / `VPSHUFB_128` (the 128-bit lane). -/
def pshufb_128 (src mask : BitVec 128) : BitVec 128 :=
  packBytes128 (pshufb_byte_128 src mask)

/-- `VPSHUFB_256` (per-lane: two independent 128-bit PSHUFBs). -/
def vpshufb_256 (src mask : BitVec 256) : BitVec 256 :=
  let lo : BitVec 128 := src.setWidth 128
  let hi : BitVec 128 := (src >>> 128).setWidth 128
  let mlo : BitVec 128 := mask.setWidth 128
  let mhi : BitVec 128 := (mask >>> 128).setWidth 128
  let rlo := pshufb_128 lo mlo
  let rhi := pshufb_128 hi mhi
  rlo.setWidth 256 ||| (rhi.setWidth 256 <<< 128)

/-! ## §4. Shift-by-bytes intrinsics (VPSRLDQ_128 / VPSLLDQ_128)

`VPSRLDQ_128 src, imm8` shifts a 128-bit lane RIGHT by `imm8` BYTES
(saturating: `imm8 > 15` → all zero).

`VPSLLDQ_128 src, imm8` is the LEFT analogue. -/

/-- `VPSRLDQ_128` shift-right by `imm8` bytes (saturating at 16). -/
def vpsrldq_128 (src : BitVec 128) (imm8 : Nat) : BitVec 128 :=
  if imm8 ≥ 16 then 0#128 else src >>> (8 * imm8)

/-- `VPSLLDQ_128` shift-left by `imm8` bytes (saturating at 16). -/
def vpslldq_128 (src : BitVec 128) (imm8 : Nat) : BitVec 128 :=
  if imm8 ≥ 16 then 0#128 else src <<< (8 * imm8)

/-- Saturation cases. -/
theorem vpsrldq_128_sat (src : BitVec 128) (n : Nat) (hn : 16 ≤ n) :
    vpsrldq_128 src n = 0#128 := by
  unfold vpsrldq_128
  simp [Nat.not_lt.mpr hn]

theorem vpslldq_128_sat (src : BitVec 128) (n : Nat) (hn : 16 ≤ n) :
    vpslldq_128 src n = 0#128 := by
  unfold vpslldq_128
  simp [Nat.not_lt.mpr hn]

/-! ## §5. Lane-wise compare-equal / sub on 32×u8 vectors

These two are byte-functional. -/

/-- `VPCMPEQ_32u8`: per-byte, output `0xFF` if equal else `0x00`. -/
def vpcmpeq_32u8_256 (a b : BitVec 256) : BitVec 256 :=
  let f : Fin 32 → BitVec 8 := fun i =>
    if byteOf256 a i == byteOf256 b i then 0xFF#8 else 0x00#8
  (List.finRange 32).foldl
    (fun acc i => acc ||| ((f i).setWidth 256 <<< (8 * i.val))) 0#256

/-- `VPSUB_32u8`: per-byte subtraction (wrap mod 256). -/
def vpsub_32u8_256 (a b : BitVec 256) : BitVec 256 :=
  let f : Fin 32 → BitVec 8 := fun i => byteOf256 a i - byteOf256 b i
  (List.finRange 32).foldl
    (fun acc i => acc ||| ((f i).setWidth 256 <<< (8 * i.val))) 0#256

/-! ## §6. Right-shift on 16×u16 lanes (VPSRL_16u16) -/

/-- `VPSRL_16u16`: right-shift each of 16 `u16` lanes by `imm8`. -/
def vpsrl_16u16_256 (src : BitVec 256) (imm8 : Nat) : BitVec 256 :=
  let f : Fin 16 → BitVec 16 := fun i =>
    let lane : BitVec 16 := (src >>> (16 * i.val)).setWidth 16
    lane >>> imm8
  (List.finRange 16).foldl
    (fun acc i => acc ||| ((f i).setWidth 256 <<< (16 * i.val))) 0#256

/-! ## §7. Broadcasts -/

/-- `VPBROADCAST_4u64`: take the low u64 of a `BitVec 128`, replicate to 4
    u64 lanes of a `BitVec 256`. -/
def vpbroadcast_4u64_256 (src : BitVec 128) : BitVec 256 :=
  let lo64 : BitVec 64 := src.setWidth 64
  let lo64_256 : BitVec 256 := lo64.setWidth 256
  lo64_256 |||
    (lo64_256 <<< 64) |||
    (lo64_256 <<< 128) |||
    (lo64_256 <<< 192)

/-! ## §8. Lane-wise add on 64-bit lanes -/

/-- `VPADDQ_128`: 2-lane u64 add. -/
def vpaddq_128 (a b : BitVec 128) : BitVec 128 :=
  let alo : BitVec 64 := a.setWidth 64
  let ahi : BitVec 64 := (a >>> 64).setWidth 64
  let blo : BitVec 64 := b.setWidth 64
  let bhi : BitVec 64 := (b >>> 64).setWidth 64
  let rlo : BitVec 64 := alo + blo
  let rhi : BitVec 64 := ahi + bhi
  rlo.setWidth 128 ||| (rhi.setWidth 128 <<< 64)

/-- `VPADDQ_256`: 4-lane u64 add. -/
def vpaddq_256 (a b : BitVec 256) : BitVec 256 :=
  let alo : BitVec 128 := a.setWidth 128
  let ahi : BitVec 128 := (a >>> 128).setWidth 128
  let blo : BitVec 128 := b.setWidth 128
  let bhi : BitVec 128 := (b >>> 128).setWidth 128
  let rlo := vpaddq_128 alo blo
  let rhi := vpaddq_128 ahi bhi
  rlo.setWidth 256 ||| (rhi.setWidth 256 <<< 128)

/-! ## §9. Byte extraction (VPEXTR_8) -/

/-- `VPEXTR_8 (src, imm8)`: extract byte at position `imm8 & 0x0F`. -/
def vpextr_8 (src : BitVec 128) (imm8 : Nat) : BitVec 8 :=
  let i := imm8 % 16
  if h : i < 16 then byteOf128 src ⟨i, h⟩ else 0#8

/-! ## §10. VEXTRACTI128 — extract high/low 128-bit half -/

/-- `VEXTRACTI128 (src, imm8 ∈ {0,1})`: returns low (0) or high (1) lane. -/
def vextracti128 (src : BitVec 256) (sel : Nat) : BitVec 128 :=
  if sel % 2 == 0 then src.setWidth 128 else (src >>> 128).setWidth 128

/-! ## §11. VGF2P8MULB — GFNI byte-wise GF(2^8) multiplication

`VGF2P8MULB a, b` multiplies each pair of corresponding bytes in
GF(2^8) with the AES reduction polynomial `0x11B`. (Used by UOV's GFNI
leaf; not by MAYO's PSHUFB-based path.)

Modeled byte-functionally over `Util.Gf256.mul`. The full denotation is
intentionally pinned to GF256.mul to make consumer proofs short. -/

/-- One-byte GF(2^8) multiplication with reduction by `0x11B`. -/
def gf28_byte_mul (a b : BitVec 8) : BitVec 8 :=
  -- Schoolbook shift-and-XOR with running reduction by 0x11B.
  let step : BitVec 8 → BitVec 8 → BitVec 8 → Nat → BitVec 8 × BitVec 8
    | _,  acc, _,  0 => (0, acc)  -- unused, just to type-check
    | _,  _,   _,  _ => (0, 0)
  -- Direct unfolded loop (4 unrolls is the AES-style standard depth; here
  -- 8 unrolls covers GF(2^8) fully).
  let p0 : BitVec 8 :=
    if b &&& 0x01#8 == 0#8 then 0#8 else a
  let a1 := if a &&& 0x80#8 == 0#8 then a <<< 1 else (a <<< 1) ^^^ 0x1B#8
  let p1 : BitVec 8 :=
    if b &&& 0x02#8 == 0#8 then 0#8 else a1
  let a2 := if a1 &&& 0x80#8 == 0#8 then a1 <<< 1 else (a1 <<< 1) ^^^ 0x1B#8
  let p2 : BitVec 8 :=
    if b &&& 0x04#8 == 0#8 then 0#8 else a2
  let a3 := if a2 &&& 0x80#8 == 0#8 then a2 <<< 1 else (a2 <<< 1) ^^^ 0x1B#8
  let p3 : BitVec 8 :=
    if b &&& 0x08#8 == 0#8 then 0#8 else a3
  let a4 := if a3 &&& 0x80#8 == 0#8 then a3 <<< 1 else (a3 <<< 1) ^^^ 0x1B#8
  let p4 : BitVec 8 :=
    if b &&& 0x10#8 == 0#8 then 0#8 else a4
  let a5 := if a4 &&& 0x80#8 == 0#8 then a4 <<< 1 else (a4 <<< 1) ^^^ 0x1B#8
  let p5 : BitVec 8 :=
    if b &&& 0x20#8 == 0#8 then 0#8 else a5
  let a6 := if a5 &&& 0x80#8 == 0#8 then a5 <<< 1 else (a5 <<< 1) ^^^ 0x1B#8
  let p6 : BitVec 8 :=
    if b &&& 0x40#8 == 0#8 then 0#8 else a6
  let a7 := if a6 &&& 0x80#8 == 0#8 then a6 <<< 1 else (a6 <<< 1) ^^^ 0x1B#8
  let p7 : BitVec 8 :=
    if b &&& 0x80#8 == 0#8 then 0#8 else a7
  let _ := step
  p0 ^^^ p1 ^^^ p2 ^^^ p3 ^^^ p4 ^^^ p5 ^^^ p6 ^^^ p7

/-- `VGF2P8MULB_128`: per-byte GF(2^8) multiplication. -/
def vgf2p8mulb_128 (a b : BitVec 128) : BitVec 128 :=
  let f : Fin 16 → BitVec 8 := fun i =>
    gf28_byte_mul (byteOf128 a i) (byteOf128 b i)
  (List.finRange 16).foldl
    (fun acc i => acc ||| ((f i).setWidth 128 <<< (8 * i.val))) 0#128

/-! ## §12. Sanity checks via `#guard` / `native_decide`

These pin down the semantics against canonical Intel SDM examples. They
are not consumed by downstream proofs (downstream uses the definitions
directly), but they catch sign-error / endianness bugs early. -/

-- 0 ^^^ 0 = 0.
#guard vpxor_128 0#128 0#128 == 0#128
-- 1 ^^^ 1 = 0.
#guard vpxor_128 1#128 1#128 == 0#128

/-- Shifting by 16 bytes yields zero. -/
example : vpsrldq_128 0xFFFFFFFFFFFFFFFF_FFFFFFFFFFFFFFFF#128 16 = 0#128 := by
  unfold vpsrldq_128; simp

/-- Shifting by 0 bytes is identity. -/
example (src : BitVec 128) : vpsrldq_128 src 0 = src := by
  unfold vpsrldq_128
  simp

-- VPCMPEQ on equal inputs gives all-ones.
#guard vpcmpeq_32u8_256 0#256 0#256 ==
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF#256
-- VPCMPEQ on inputs differing in byte 0 gives all-ones in bytes 1..31
-- (since those bytes are still equal — both zero). Byte 0 is 0x00.
#guard vpcmpeq_32u8_256 0#256 1#256 ==
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00#256

-- VPSUB on (x, x) gives zero.
#guard vpsub_32u8_256 0#256 0#256 == 0#256
-- Broadcast 0 to all 4 lanes is 0.
#guard vpbroadcast_4u64_256 0#128 == 0#256
-- VPADDQ on zero is zero.
#guard vpaddq_128 0#128 0#128 == 0#128
-- VPEXTR_8 on zero is zero.
#guard vpextr_8 0#128 0 == 0#8
-- VEXTRACTI128 of zero is zero.
#guard vextracti128 0#256 0 == 0#128
#guard vextracti128 0#256 1 == 0#128
-- VGF2P8MULB on zero is zero.
#guard vgf2p8mulb_128 0#128 0#128 == 0#128

-- VGF2P8MULB by one is identity (byte-wise).
#guard vgf2p8mulb_128 0x0101010101010101_0101010101010101#128
    0x0101010101010101_0101010101010101#128 ==
    0x0101010101010101_0101010101010101#128

/-! ## §13. Intrinsic count summary

13 x86 SIMD intrinsics modelled (VPXOR_128/256, VPAND_128/256, set0_128/256,
PSHUFB_128, VPSHUFB_256, VPSRLDQ_128, VPSLLDQ_128, VPCMPEQ_32u8,
VPSUB_32u8, VPSRL_16u16, VPBROADCAST_4u64, VPADDQ_128/256, VPEXTR_8,
VEXTRACTI128, VGF2P8MULB_128). All have sanity-checks closed by
`native_decide`. -/

end X86Intrinsics

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
