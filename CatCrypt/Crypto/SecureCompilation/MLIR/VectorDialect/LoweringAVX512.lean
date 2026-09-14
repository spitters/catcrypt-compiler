/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Denote

/-!
# MLIR `vector` dialect — AVX-512 lowering pass

A second lowering target for the `vector` dialect, next to the AVX2 / per-lane
`ScalarExpansion` lowering in [`Lowering.lean`](Lowering.lean). A vector operation
at a `zmm` lane width is lowered to one AVX-512 instruction.

This file defines:

* `LaneWidth` — the lane shape of a `zmm` register (8×u64, 16×u32, 32×u16,
  64×u8, 4×u128), with `Zmm w` the lane vector at width `w`;
* `AVX512Inst w` — an instruction: a mnemonic family (`BinMnem`, `ShiftMnem`,
  `VPBROADCAST`, `VPERM`, `VGF2P8AFFINEQB`, `VAESENC`) and its operands, with no
  stored lane function;
* `AVX512Inst.denote512` — the value an instruction writes, determined by its
  family and width: lane arithmetic on `toNat` / `toInt` (`BinMnem.laneSem`,
  `ShiftMnem.laneSem`), the permute by index lanes reduced modulo the lane count,
  and, for `VGF2P8AFFINEQB` and `VAESENC`, the byte affine map and the AES round
  of a `LeafSem` parameter;
* `AVX512Inst.valid` — whether an x86 instruction exists for the family at the
  width, and `AVX512Inst.exts` — the CPUID features it requires;
* `LaneOp w` — the source operations (lane add, subtract, xor, and, or, low and
  signed/unsigned high multiply, shifts, broadcast, permute, GF(2) affine, AES
  round) and `LaneOp.toVectorOp`, the dialect `VectorOp` each denotes, with
  `BitVec` lane functions (`+`, `*`, `<<<`, `sshiftRight`, the high half of the
  double-width product via `signExtend`/`setWidth` and `extractLsb'`);
* `lowerAVX512` — instruction selection, returning `none` when no instruction
  exists for the operation at the width.

## What the theorems state

`lowerInst_denote` / `lowerAVX512_correct`: the selected instruction, under
`denote512`, writes the lane vector that `denoteVectorOp` gives for the dialect
op. The proof goes through one lemma per family relating the instruction
semantics to the `BitVec` lane function (`binMnem_laneSem_eq`,
`shiftMnem_laneSem_eq`); for example `VPMULHW` is the floor quotient
`(a·b) / 2^e` of the signed product (`vpmulhw_laneSem`), and a logical shift by a
count of at least `e` writes `0`.

Instruction existence: `VPMULHW` / `VPMULHUW` exist only on 16-bit lanes, there
is no byte multiply or byte shift, and no lane arithmetic on 128-bit lanes except
bitwise ops; `lowerAVX512` returns `none` for those (`lowerAVX512_mulHiS_w16u32`,
`lowerAVX512_mulHiU_w8u64`, `lowerAVX512_mulLo_w64u8`, `lowerAVX512_shift_w64u8`).
Required features: byte and word forms need `AVX512BW`, `VPMULLQ` needs
`AVX512DQ`, `VPERMB` needs `AVX512_VBMI`, `VGF2P8AFFINEQB` needs `GFNI`,
`VAESENC` needs `VAES` (`exts_mulLo_w8u64`, `exts_add_w64u8`, `exts_perm_w64u8`).

## Scope

The semantics is per lane; masking, memory operands and the EVEX encoding are
not modelled. `renderAVX512` prints the jasmin-style mnemonic line; no theorem
relates the printed text to `denote512`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect

/-! ## 1. Lane widths, features and instructions -/

/-- The lane shape of a `zmm` register: lane count and lane word width. -/
inductive LaneWidth where
  /-- 8 × u64 lanes. -/
  | w8u64
  /-- 16 × u32 lanes. -/
  | w16u32
  /-- 32 × u16 lanes. -/
  | w32u16
  /-- 64 × u8 lanes. -/
  | w64u8
  /-- 4 × u128 lanes. -/
  | w4u128
  deriving DecidableEq, Repr

/-- The `_<lanes><elt>` mnemonic suffix string for a width. -/
def LaneWidth.suffix : LaneWidth → String
  | .w8u64  => "8u64"
  | .w16u32 => "16u32"
  | .w32u16 => "32u16"
  | .w64u8  => "64u8"
  | .w4u128 => "4u128"

/-- The lane count of a `zmm` register at a width. -/
@[reducible] def LaneWidth.lanes : LaneWidth → Nat
  | .w8u64  => 8
  | .w16u32 => 16
  | .w32u16 => 32
  | .w64u8  => 64
  | .w4u128 => 4

/-- The lane word width in bits. -/
@[reducible] def LaneWidth.elt : LaneWidth → Nat
  | .w8u64  => 64
  | .w16u32 => 32
  | .w32u16 => 16
  | .w64u8  => 8
  | .w4u128 => 128

theorem LaneWidth.lanes_pos (w : LaneWidth) : 0 < w.lanes := by
  cases w <;> decide

/-- A lane index fits in a lane word. -/
theorem LaneWidth.lanes_le (w : LaneWidth) : w.lanes ≤ 2 ^ w.elt := by
  cases w <;> decide

/-- A `zmm` value as `w.lanes` lanes of `w.elt`-bit words. -/
abbrev Zmm (w : LaneWidth) : Type := VectorTy (BitVec w.elt) w.lanes

/-- CPUID feature flags an AVX-512 instruction form requires. -/
inductive Ext where
  /-- `AVX512F`. -/
  | f
  /-- `AVX512BW` (byte and word lane forms). -/
  | bw
  /-- `AVX512DQ` (`VPMULLQ`, the 128-bit lane broadcast `VBROADCASTI64X2`). -/
  | dq
  /-- `AVX512_VBMI` (`VPERMB`). -/
  | vbmi
  /-- `GFNI`. -/
  | gfni
  /-- `VAES`. -/
  | vaes
  deriving DecidableEq, Repr

/-- Binary lane-wise instruction families. -/
inductive BinMnem where
  /-- `VPADDB/W/D/Q`. -/
  | vpadd
  /-- `VPSUBB/W/D/Q`. -/
  | vpsub
  /-- `VPXORD/Q`. -/
  | vpxor
  /-- `VPANDD/Q`. -/
  | vpand
  /-- `VPORD/Q`. -/
  | vpor
  /-- `VPMULLW/D/Q`. -/
  | vpmull
  /-- `VPMULHW`: high half of the signed product. -/
  | vpmulhw
  /-- `VPMULHUW`: high half of the unsigned product. -/
  | vpmulhuw
  deriving DecidableEq, Repr

/-- Shift-by-immediate instruction families. -/
inductive ShiftMnem where
  /-- `VPSLLW/D/Q`. -/
  | vpsll
  /-- `VPSRLW/D/Q`. -/
  | vpsrl
  /-- `VPSRAW/D/Q`. -/
  | vpsra
  deriving DecidableEq, Repr

/-- An AVX-512 instruction at a lane width: a mnemonic family and its operands. -/
inductive AVX512Inst : LaneWidth → Type where
  /-- `VPBROADCASTB/W/D/Q`, `VBROADCASTI64X2`: every lane is `x`. -/
  | vpbroadcast {w : LaneWidth} (x : BitVec w.elt) : AVX512Inst w
  /-- A binary lane-wise instruction. -/
  | bin {w : LaneWidth} (m : BinMnem) (v u : Zmm w) : AVX512Inst w
  /-- A shift by the immediate `count`. -/
  | shift {w : LaneWidth} (m : ShiftMnem) (count : Nat) (v : Zmm w) : AVX512Inst w
  /-- `VPERMB/W/D/Q`: lane `i` is lane `idx i mod lanes` of `v`. -/
  | vperm {w : LaneWidth} (idx v : Zmm w) : AVX512Inst w
  /-- `VGF2P8AFFINEQB`: byte `i` of `x` under the matrix in qword `i / 8` of `mat`,
      xor the immediate `imm`. -/
  | vgf2p8affineqb (x : Zmm .w64u8) (mat : Zmm .w8u64) (imm : BitVec 8) : AVX512Inst .w64u8
  /-- `VAESENC`: one AES encryption round per 128-bit lane. -/
  | vaesenc (s k : Zmm .w4u128) : AVX512Inst .w4u128

/-! ## 2. Instruction semantics -/

/-- The lane semantics of a binary instruction family on `e`-bit words, in
    natural-number and integer arithmetic. -/
def BinMnem.laneSem : BinMnem → (e : Nat) → BitVec e → BitVec e → BitVec e
  | .vpadd, e, a, b => BitVec.ofNat e (a.toNat + b.toNat)
  | .vpsub, e, a, b => BitVec.ofNat e (a.toNat + (2 ^ e - b.toNat))
  | .vpxor, e, a, b => BitVec.ofNat e (a.toNat ^^^ b.toNat)
  | .vpand, e, a, b => BitVec.ofNat e (a.toNat &&& b.toNat)
  | .vpor, e, a, b => BitVec.ofNat e (a.toNat ||| b.toNat)
  | .vpmull, e, a, b => BitVec.ofNat e (a.toNat * b.toNat)
  | .vpmulhw, e, a, b => BitVec.ofInt e ((a.toInt * b.toInt) / 2 ^ e)
  | .vpmulhuw, e, a, b => BitVec.ofNat e (a.toNat * b.toNat / 2 ^ e)

/-- The lane semantics of a shift family on `e`-bit words. A logical shift by a
    count of at least `e` writes `0`; the arithmetic shift writes the floor
    quotient by `2^count`, which for a count of at least `e − 1` is `0` or `−1`. -/
def ShiftMnem.laneSem : ShiftMnem → (e : Nat) → Nat → BitVec e → BitVec e
  | .vpsll, e, c, a => if c < e then BitVec.ofNat e (a.toNat * 2 ^ c) else 0
  | .vpsrl, e, c, a => if c < e then BitVec.ofNat e (a.toNat / 2 ^ c) else 0
  | .vpsra, e, c, a => BitVec.ofInt e (a.toInt / 2 ^ c)

/-- The per-byte GF(2) affine map and the AES round, as parameters of the
    semantics of `VGF2P8AFFINEQB` and `VAESENC`. `VIR.GfniEmit.gfniAffine8` and
    `VIR.VAESEmit.denoteVAES .vaesenc` are instances. -/
structure LeafSem where
  /-- The affine map of a byte under an 8×8 matrix packed in a qword. -/
  gf2p8affine : BitVec 64 → BitVec 8 → BitVec 8
  /-- One AES encryption round of a state under a round key. -/
  aesenc : BitVec 128 → BitVec 128 → BitVec 128

/-- The value an instruction writes, determined by its mnemonic family and width. -/
def AVX512Inst.denote512 (L : LeafSem) : {w : LaneWidth} → AVX512Inst w → Zmm w
  | _, .vpbroadcast x => fun _ => x
  | w, .bin m v u => fun i => m.laneSem w.elt (v i) (u i)
  | w, .shift m c v => fun i => m.laneSem w.elt c (v i)
  | w, .vperm idx v => fun i => v ⟨(idx i).toNat % w.lanes, Nat.mod_lt _ w.lanes_pos⟩
  | _, .vgf2p8affineqb x mat imm => fun i =>
      L.gf2p8affine (mat ⟨i.val / 8, by have := i.isLt; simp only [LaneWidth.lanes] at this ⊢; omega⟩)
        (x i) ^^^ imm
  | _, .vaesenc s k => fun i => L.aesenc (s i) (k i)

/-- Whether an x86 instruction exists for the family at the width. -/
def AVX512Inst.valid : {w : LaneWidth} → AVX512Inst w → Bool
  | _, .vpbroadcast _ => true
  | w, .bin m _ _ =>
      match m, w with
      | .vpxor, _ | .vpand, _ | .vpor, _ => true
      | _, .w4u128 => false
      | .vpmull, .w64u8 => false
      | .vpmulhw, .w32u16 | .vpmulhuw, .w32u16 => true
      | .vpmulhw, _ | .vpmulhuw, _ => false
      | _, _ => true
  | w, .shift _ _ _ =>
      match w with
      | .w64u8 | .w4u128 => false
      | _ => true
  | w, .vperm _ _ =>
      match w with
      | .w4u128 => false
      | _ => true
  | _, .vgf2p8affineqb _ _ _ => true
  | _, .vaesenc _ _ => true

/-- The CPUID features the instruction form requires. -/
def AVX512Inst.exts : {w : LaneWidth} → AVX512Inst w → List Ext
  | w, .vpbroadcast _ =>
      match w with
      | .w32u16 | .w64u8 => [.f, .bw]
      | .w4u128 => [.f, .dq]
      | _ => [.f]
  | w, .bin m _ _ =>
      match m, w with
      | .vpxor, _ | .vpand, _ | .vpor, _ => [.f]
      | .vpmull, .w8u64 => [.f, .dq]
      | _, .w32u16 | _, .w64u8 => [.f, .bw]
      | _, _ => [.f]
  | w, .shift _ _ _ =>
      match w with
      | .w32u16 => [.f, .bw]
      | _ => [.f]
  | w, .vperm _ _ =>
      match w with
      | .w64u8 => [.f, .vbmi]
      | .w32u16 => [.f, .bw]
      | _ => [.f]
  | _, .vgf2p8affineqb _ _ _ => [.f, .gfni]
  | _, .vaesenc _ _ => [.f, .vaes]

/-! ## 3. Source operations -/

/-- The high half of the signed `2e`-bit product. -/
def laneMulHiS (e : Nat) (a b : BitVec e) : BitVec e :=
  (a.signExtend (2 * e) * b.signExtend (2 * e)).extractLsb' e e

/-- The high half of the unsigned `2e`-bit product. -/
def laneMulHiU (e : Nat) (a b : BitVec e) : BitVec e :=
  (a.setWidth (2 * e) * b.setWidth (2 * e)).extractLsb' e e

/-- Binary lane operations. -/
inductive LaneBin where
  | add | sub | xor | and | or | mulLo | mulHiS | mulHiU
  deriving DecidableEq, Repr

/-- Shift operations. -/
inductive LaneShift where
  | shl | shr | sar
  deriving DecidableEq, Repr

/-- The `BitVec` function of a binary lane operation. -/
def LaneBin.fn : LaneBin → (e : Nat) → BitVec e → BitVec e → BitVec e
  | .add, _ => (· + ·)
  | .sub, _ => (· - ·)
  | .xor, _ => (· ^^^ ·)
  | .and, _ => (· &&& ·)
  | .or, _ => (· ||| ·)
  | .mulLo, _ => (· * ·)
  | .mulHiS, e => laneMulHiS e
  | .mulHiU, e => laneMulHiU e

/-- The `BitVec` function of a shift. -/
def LaneShift.fn : LaneShift → (e : Nat) → BitVec e → Nat → BitVec e
  | .shl, _ => fun a m => a <<< m
  | .shr, _ => fun a m => a >>> m
  | .sar, _ => fun a m => a.sshiftRight m

/-- A vector operation at a `zmm` lane width, named by its lane operation. -/
inductive LaneOp : LaneWidth → Type where
  /-- Every lane is `x`. -/
  | broadcast {w : LaneWidth} (x : BitVec w.elt) : LaneOp w
  /-- A binary lane operation. -/
  | bin {w : LaneWidth} (op : LaneBin) (v u : Zmm w) : LaneOp w
  /-- A shift by `m`. -/
  | shift {w : LaneWidth} (op : LaneShift) (m : Nat) (v : Zmm w) : LaneOp w
  /-- Lane `i` is lane `π i` of `v`. -/
  | perm {w : LaneWidth} (π : Fin w.lanes → Fin w.lanes) (v : Zmm w) : LaneOp w
  /-- The byte affine map under matrix `M`, xor `b`. -/
  | affine (M : BitVec 64) (b : BitVec 8) (v : Zmm .w64u8) : LaneOp .w64u8
  /-- One AES round per lane. -/
  | aesRound (s k : Zmm .w4u128) : LaneOp .w4u128

/-- The dialect `VectorOp` a lane op denotes. -/
def LaneOp.toVectorOp (L : LeafSem) :
    {w : LaneWidth} → LaneOp w → VectorOp (BitVec w.elt) w.lanes
  | _, .broadcast x => .broadcast x
  | w, .bin op v u =>
      match op with
      | .mulLo => .mul (LaneBin.fn .mulLo w.elt) v u
      | .mulHiS => .mulHi (LaneBin.fn .mulHiS w.elt) v u
      | .mulHiU => .mulHi (LaneBin.fn .mulHiU w.elt) v u
      | op => .add (op.fn w.elt) v u
  | w, .shift op m v =>
      match op with
      | .shl => .shiftL (LaneShift.fn .shl w.elt) m v
      | .shr => .shiftR (LaneShift.fn .shr w.elt) m v
      | .sar => .shiftRA (LaneShift.fn .sar w.elt) m v
  | _, .perm π v => .shuffle v π
  | _, .affine M b v => .affineByte (fun x => L.gf2p8affine M x ^^^ b) v
  | _, .aesRound s k => .aesRound L.aesenc s k

/-! ## 4. Instruction selection -/

/-- The instruction family for a binary lane operation. -/
def LaneBin.mnem : LaneBin → BinMnem
  | .add => .vpadd
  | .sub => .vpsub
  | .xor => .vpxor
  | .and => .vpand
  | .or => .vpor
  | .mulLo => .vpmull
  | .mulHiS => .vpmulhw
  | .mulHiU => .vpmulhuw

/-- The instruction family for a shift. -/
def LaneShift.mnem : LaneShift → ShiftMnem
  | .shl => .vpsll
  | .shr => .vpsrl
  | .sar => .vpsra

/-- The instruction selected for a lane op. The permutation `π` becomes the index
    vector with lane `i` holding `π i`; the affine matrix is broadcast to the eight
    matrix qwords. -/
def lowerInst : {w : LaneWidth} → LaneOp w → AVX512Inst w
  | _, .broadcast x => .vpbroadcast x
  | _, .bin op v u => .bin op.mnem v u
  | _, .shift op m v => .shift op.mnem m v
  | w, .perm π v => .vperm (fun i => BitVec.ofNat w.elt (π i).val) v
  | _, .affine M b v => .vgf2p8affineqb v (fun _ => M) b
  | _, .aesRound s k => .vaesenc s k

/-- The AVX-512 lowering pass: the selected instruction when an x86 instruction
    exists for it at the width, `none` otherwise. -/
def lowerAVX512 {w : LaneWidth} (t : LaneOp w) : Option (AVX512Inst w) :=
  if (lowerInst t).valid then some (lowerInst t) else none

/-! ## 5. Lane lemmas: instruction semantics equals the `BitVec` function -/

/-- `(z mod t²) / t ≡ z / t (mod t)` for `t > 0`. -/
theorem int_emod_sq_ediv_emod (z t : Int) (ht : 0 < t) :
    (z % (t * t)) / t % t = (z / t) % t := by
  have hz : z = z % (t * t) + t * (t * (z / (t * t))) := by
    rw [← Int.mul_assoc]; exact (Int.emod_add_mul_ediv z (t * t)).symm
  have h2 : z / t % t = (z % (t * t) + t * (t * (z / (t * t)))) / t % t := by rw [← hz]
  rw [h2, Int.add_mul_ediv_left _ _ (Int.ne_of_gt ht), Int.add_mul_emod_self_left]

/-- The `VPMULHUW` lane semantics equals `laneMulHiU`. -/
theorem vpmulhuw_laneSem (e : Nat) (a b : BitVec e) :
    BitVec.ofNat e (a.toNat * b.toNat / 2 ^ e) = laneMulHiU e a b := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  have hab' : a.toNat * b.toNat < 2 ^ e * 2 ^ e := Nat.mul_lt_mul_of_lt_of_lt ha hb
  have hab : a.toNat * b.toNat < 2 ^ (2 * e) := by
    rw [Nat.two_mul, Nat.pow_add]; exact hab'
  have hq : a.toNat * b.toNat / 2 ^ e < 2 ^ e := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos e)]; exact hab'
  have hle : 2 ^ e ≤ 2 ^ (2 * e) := Nat.pow_le_pow_right (by decide) (by omega)
  have ha2 : a.toNat % 2 ^ (2 * e) = a.toNat := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ha hle)
  have hb2 : b.toNat % 2 ^ (2 * e) = b.toNat := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb hle)
  simp only [laneMulHiU, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, BitVec.toNat_mul,
    BitVec.toNat_setWidth, ha2, hb2, Nat.mod_eq_of_lt hab, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hq]

/-- The `VPMULHW` lane semantics equals `laneMulHiS`. -/
theorem vpmulhw_laneSem (e : Nat) (a b : BitVec e) :
    BitVec.ofInt e ((a.toInt * b.toInt) / 2 ^ e) = laneMulHiS e a b := by
  apply BitVec.eq_of_toNat_eq
  have hP : (a.signExtend (2 * e) * b.signExtend (2 * e)).toNat
      = ((a.toInt * b.toInt) % ((2 : Int) ^ e * 2 ^ e)).toNat := by
    have hb : a.signExtend (2 * e) * b.signExtend (2 * e)
        = BitVec.ofInt (2 * e) (a.toInt * b.toInt) := by
      apply BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by omega),
        BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt]
    rw [hb, BitVec.toNat_ofInt]
    congr 2
    rw [Nat.two_mul, Nat.pow_add]
    simp
  rw [laneMulHiS, BitVec.extractLsb'_toNat, hP, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow]
  have ht : (0 : Int) < 2 ^ e := Int.pow_pos (by decide : (0 : Int) < 2)
  have hr : 0 ≤ a.toInt * b.toInt % (2 ^ e * 2 ^ e) :=
    Int.emod_nonneg _ (Int.ne_of_gt (Int.mul_pos ht ht))
  have hcast : ((2 ^ e : Nat) : Int) = 2 ^ e := by simp
  rw [hcast, ← int_emod_sq_ediv_emod _ _ ht]
  generalize a.toInt * b.toInt % (2 ^ e * 2 ^ e) = r at hr ⊢
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  rw [← hcast, ← Int.natCast_ediv, ← Int.natCast_emod, Int.toNat_natCast, Int.toNat_natCast]

/-- Each binary family's lane semantics equals the `BitVec` function of the lane
    operation lowered to it. -/
theorem binMnem_laneSem_eq (op : LaneBin) (e : Nat) (a b : BitVec e) :
    op.mnem.laneSem e a b = op.fn e a b := by
  cases op <;> simp only [LaneBin.mnem, BinMnem.laneSem, LaneBin.fn]
  · apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_sub]
    rw [Nat.add_comm]
  · apply BitVec.eq_of_toNat_eq; simp
  · apply BitVec.eq_of_toNat_eq; simp
  · apply BitVec.eq_of_toNat_eq; simp
  · apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]
  · exact vpmulhw_laneSem e a b
  · exact vpmulhuw_laneSem e a b

/-- Each shift family's lane semantics equals the `BitVec` shift lowered to it. -/
theorem shiftMnem_laneSem_eq (op : LaneShift) (e c : Nat) (a : BitVec e) :
    op.mnem.laneSem e c a = op.fn e a c := by
  cases op <;> simp only [LaneShift.mnem, ShiftMnem.laneSem, LaneShift.fn]
  · apply BitVec.eq_of_toNat_eq
    split
    · simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    · rename_i h
      simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      exact (Nat.mod_eq_zero_of_dvd
        (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_left _ _))).symm
  · apply BitVec.eq_of_toNat_eq
    have ha := a.isLt
    split
    · simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)
    · rename_i h
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact (Nat.div_eq_of_lt
        (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
  · have h := BitVec.ofInt_toInt (x := a.sshiftRight c)
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow] at h
    exact h

/-! ## 6. Lowering correctness -/

/-- **Instruction selection is correct.** The selected instruction, under
    `denote512`, writes the lane vector the dialect op denotes. -/
theorem lowerInst_denote (L : LeafSem) {w : LaneWidth} (t : LaneOp w) :
    VectorOp.Result.vec ((lowerInst t).denote512 L) = denoteVectorOp (t.toVectorOp L) := by
  cases t with
  | broadcast x => rfl
  | bin op v u =>
    cases op <;>
      simp only [lowerInst, AVX512Inst.denote512, LaneOp.toVectorOp, denoteVectorOp,
        binMnem_laneSem_eq]
  | shift op m v =>
    cases op <;>
      simp only [lowerInst, AVX512Inst.denote512, LaneOp.toVectorOp, denoteVectorOp,
        shiftMnem_laneSem_eq]
  | perm π v =>
    simp only [lowerInst, AVX512Inst.denote512, LaneOp.toVectorOp, denoteVectorOp]
    congr 1
    funext i
    congr 1
    apply Fin.ext
    simp only [BitVec.toNat_ofNat]
    have h1 := (π i).isLt
    have h2 := w.lanes_le
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 h2), Nat.mod_eq_of_lt h1]
  | affine M b v => rfl
  | aesRound s k => rfl

/-- **AVX-512 lowering correctness.** When `lowerAVX512 t` returns an instruction,
    that instruction writes the lane vector the dialect op denotes. -/
theorem lowerAVX512_correct (L : LeafSem) {w : LaneWidth} (t : LaneOp w) (i : AVX512Inst w)
    (h : lowerAVX512 t = some i) :
    VectorOp.Result.vec (i.denote512 L) = denoteVectorOp (t.toVectorOp L) := by
  unfold lowerAVX512 at h
  split at h
  · cases h; exact lowerInst_denote L t
  · cases h

/-- The lowering of an op with an instruction, mapped through `denote512`. -/
theorem lowerAVX512_map_denote (L : LeafSem) {w : LaneWidth} (t : LaneOp w)
    (hv : (lowerInst t).valid = true) :
    (lowerAVX512 t).map (fun i => VectorOp.Result.vec (i.denote512 L))
      = some (denoteVectorOp (t.toVectorOp L)) := by
  simp only [lowerAVX512, hv, if_true, Option.map_some, lowerInst_denote]

/-! ## 7. Rejected forms and required features -/

/-- There is no 32-bit high-half multiply instruction. -/
theorem lowerAVX512_mulHiS_w16u32 (v u : Zmm .w16u32) :
    lowerAVX512 (.bin .mulHiS v u) = none := rfl

/-- There is no 64-bit high-half multiply instruction. -/
theorem lowerAVX512_mulHiU_w8u64 (v u : Zmm .w8u64) :
    lowerAVX512 (.bin .mulHiU v u) = none := rfl

/-- There is no byte multiply instruction. -/
theorem lowerAVX512_mulLo_w64u8 (v u : Zmm .w64u8) :
    lowerAVX512 (.bin .mulLo v u) = none := rfl

/-- There is no byte shift instruction. -/
theorem lowerAVX512_shift_w64u8 (op : LaneShift) (m : Nat) (v : Zmm .w64u8) :
    lowerAVX512 (.shift op m v) = none := by
  cases op <;> rfl

/-- `VPMULLQ` requires `AVX512DQ`. -/
theorem exts_mulLo_w8u64 (v u : Zmm .w8u64) :
    (lowerInst (.bin .mulLo v u)).exts = [.f, .dq] := rfl

/-- `VPADDB` requires `AVX512BW`. -/
theorem exts_add_w64u8 (v u : Zmm .w64u8) :
    (lowerInst (.bin .add v u)).exts = [.f, .bw] := rfl

/-- `VPERMB` requires `AVX512_VBMI`. -/
theorem exts_perm_w64u8 (π : Fin 64 → Fin 64) (v : Zmm .w64u8) :
    (lowerInst (.perm π v : LaneOp .w64u8)).exts = [.f, .vbmi] := rfl

/-! ## 8. Rendering -/

/-- The jasmin mnemonic prefix of a binary family. -/
def BinMnem.name : BinMnem → String
  | .vpadd => "#VPADD"
  | .vpsub => "#VPSUB"
  | .vpxor => "#VPXOR"
  | .vpand => "#VPAND"
  | .vpor => "#VPOR"
  | .vpmull => "#VPMULL"
  | .vpmulhw => "#VPMULH"
  | .vpmulhuw => "#VPMULHU"

/-- The jasmin mnemonic prefix of a shift family. -/
def ShiftMnem.name : ShiftMnem → String
  | .vpsll => "#VPSLL"
  | .vpsrl => "#VPSRL"
  | .vpsra => "#VPSRA"

/-- Render an AVX-512 instruction to its mnemonic line, given string operand
    names. -/
def renderAVX512 (dst : String) (srcs : List String) :
    {w : LaneWidth} → AVX512Inst w → String
  | w, .vpbroadcast _ => dst ++ " = #VPBROADCAST_" ++ w.suffix ++ "(" ++ srcs.headD "x" ++ ");"
  | w, .bin m _ _ =>
      dst ++ " = " ++ m.name ++ "_" ++ w.suffix ++ "("
        ++ String.intercalate ", " (srcs.take 2) ++ ");"
  | w, .shift m c _ =>
      dst ++ " = " ++ m.name ++ "_" ++ w.suffix ++ "(" ++ srcs.headD "v" ++ ", "
        ++ toString c ++ ");"
  | w, .vperm _ _ =>
      dst ++ " = #VPERM_" ++ w.suffix ++ "(" ++ String.intercalate ", " (srcs.take 2) ++ ");"
  | _, .vgf2p8affineqb _ _ imm =>
      dst ++ " = #VGF2P8AFFINEQB_512(" ++ String.intercalate ", " (srcs.take 2) ++ ", "
        ++ toString imm.toNat ++ ");"
  | _, .vaesenc _ _ =>
      dst ++ " = #VAESENC_512(" ++ String.intercalate ", " (srcs.take 2) ++ ");"

end CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect
