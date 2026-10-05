/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.Encode

/-!
# Bitwise operations, shifts, rotations and wrapping arithmetic: runtime against Aeneas

The width families of the leaf audit's section 2.3 other than `cast#w`
(`Casts.lean`). The printer renders a tagged name `op#<w>` as `Hax.op_w w` for an
unsigned operand and `op#i<w>` as `Hax.op_iw w` for a signed one (`HaxAdapter`'s
`intTypeTag?`); an untagged name is the `Int` operation of the runtime, unrelated
to either scalar's width or sign.

## Main results

| runtime name | runtime operation | Aeneas operation | class | theorem |
|---|---|---|---|---|
| `BitXor#w` | `Hax.bitxor_w w` | `x ^^^ y` (unsigned) | 1 | `bitxor_w_u_square` |
| `BitXor#iw` | `Hax.bitxor_iw w` | `x ^^^ y` (signed) | 1 | `bitxor_iw_square` |
| `BitXor` | `Hax.bitxor` | `x ^^^ y` | 1 unsigned, 2 signed | `bitxor_u_square`, `bitxor_i_counterexample` |
| `BitAnd#w` | `Hax.bitand_w w` | `x &&& y` (unsigned) | 1 | `bitand_w_u_square` |
| `BitAnd#iw` | `Hax.bitand_iw w` | `x &&& y` (signed) | 1 | `bitand_iw_square` |
| `BitAnd` | `Hax.bitand` | `x &&& y` | 1 unsigned, 2 signed | `bitand_u_square`, `bitand_i_counterexample` |
| `BitOr#w` | `Hax.bitor_w w` | `x \|\|\| y` (unsigned) | 1 | `bitor_w_u_square` |
| `BitOr#iw` | `Hax.bitor_iw w` | `x \|\|\| y` (signed) | 1 | `bitor_iw_square` |
| `BitOr` | `Hax.bitor` | `x \|\|\| y` | 1 unsigned, 2 signed | `bitor_u_square`, `bitor_i_counterexample` |
| `Shr#w` | `Hax.shr_w w` | `x >>> s` (unsigned) | 1 | `shr_w_u_square` |
| `Shr#iw` | `Hax.shr_iw w` | `x >>> s` (signed, arithmetic) | 1 | `shr_iw_square` |
| `Shr` | `Hax.shr` | `x >>> s` | 1 unsigned, 2 signed | `shr_u_square`, `shr_i_counterexample` |
| `Shl#w` | `Hax.shl_w w` | `x <<< s` (unsigned) | 1 | `shl_w_u_square` |
| `Shl#iw` | `Hax.shl_iw w` | `x <<< s` (signed) | 1 | `shl_iw_square` |
| `Shl` | `Hax.shl` | `x <<< s` | 2 | `shl_u_counterexample`, `shl_i_counterexample` |
| `Not#w` | `Hax.bitnot_w w` | `~~~x` (unsigned) | 1 | `bitnot_w_u_square` |
| `Not#iw` | `Hax.bitnot_iw w` | `~~~x` (signed) | 1 | `bitnot_iw_square` |
| `rotate_right#w` | `Hax.rotate_right_w w` | `rotate_right x s` (unsigned) | 1 | `rotate_right_w_u_square` |
| `rotate_right#iw` | `Hax.rotate_right_iw w` | `rotate_right x s` (signed) | 1 | `rotate_right_iw_square` |
| `rotate_right` | `Hax.rotate_right` | `rotate_right x s` | 1 at `u64`, 2 otherwise | `rotate_right_u64_square`, `rotate_right_u32_counterexample`, `rotate_right_i_counterexample` |
| `wrapping_add#w` | `Hax.wrapping_add_w w` | `wrapping_add x y` (unsigned) | 1 | `wrapping_add_w_u_square` |
| `wrapping_add#iw` | `Hax.wrapping_add_iw w` | `wrapping_add x y` (signed) | 1 | `wrapping_add_iw_square` |
| `wrapping_add` | `Hax.wrapping_add` | `wrapping_add x y` | 2 | `wrapping_add_u_counterexample`, `wrapping_add_i_counterexample` |
| `wrapping_mul#w` | `Hax.wrapping_mul_w w` | `wrapping_mul x y` (unsigned) | 1 | `wrapping_mul_w_u_square` |
| `wrapping_mul#iw` | `Hax.wrapping_mul_iw w` | `wrapping_mul x y` (signed) | 1 | `wrapping_mul_iw_square` |
| `wrapping_mul` | `Hax.wrapping_mul` | `wrapping_mul x y` | 2 | `wrapping_mul_u_counterexample`, `wrapping_mul_i_counterexample` |

`overflowing_sub#w` is not among the audited names; `overflowing_sub_w_square`
states its square at a borrow (an unsigned case, unrelated to signedness).

The remaining counterexamples are for the UNTAGGED name, reached only when the
extraction pipeline cannot resolve the operand's type; the runtime then computes
over `Int` with no width or sign information, so these hold regardless of the
signed-width fix: `shr_i_counterexample` is `-8i64 >> 1` (Aeneas `-4`, runtime
`0`); `shl_u_counterexample` is `128u8 << 1` (Aeneas `0`, runtime `256`, the
unbounded shift); `shl_i_counterexample` is `1i8 << 7` (Aeneas `-128`, runtime
`128`); `rotate_right_u32_counterexample` is `1u32.rotate_right(1)` (Aeneas
`2^31`, runtime `2^63`, the rotation at width 64); `wrapping_add_u_counterexample`
is `255u8.wrapping_add(1)` (Aeneas `0`, runtime `256`); `wrapping_mul_u_counterexample`
is `16u8.wrapping_mul(16)` (Aeneas `0`, runtime `256`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std

/-- Unsigned `^` agrees with `Hax.bitxor_w` at the operand width. -/
theorem bitxor_w_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (x ^^^ y))
      (pure (Hax.bitxor_w ty.numBits (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv ^^^ y.bv).toNat : Int) = Hax.bitxor_w _ (x.bv.toNat : Int) (y.bv.toNat : Int)
  simp [Hax.bitxor_w, Nat.mod_eq_of_lt x.hBounds, Nat.mod_eq_of_lt y.hBounds]

/-- Unsigned `^` agrees with the untagged `Hax.bitxor`. -/
theorem bitxor_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (x ^^^ y)) (pure (Hax.bitxor (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv ^^^ y.bv).toNat : Int) = Hax.bitxor (x.bv.toNat : Int) (y.bv.toNat : Int)
  simp [Hax.bitxor]

/-- Signed `^` agrees with `Hax.bitxor_iw` at the operand width: both act on the
    two's-complement unsigned representative and read the result back signed. -/
theorem bitxor_iw_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (lift (x ^^^ y))
      (pure (Hax.bitxor_iw ty.numBits (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show (x.bv ^^^ y.bv).toInt = Hax.bitxor_iw ty.numBits x.val y.val
  simp only [Hax.bitxor_iw, iscalar_cast_uw, Hax.bitxor_w, Int.toNat_natCast]
  rw [Nat.mod_eq_of_lt x.bv.isLt, Nat.mod_eq_of_lt y.bv.isLt, BitVec.toInt_eq_toNat_bmod]
  congr 2

/-- Signed `^` is not related to the untagged `Hax.bitxor`: `-1i8 ^ 5i8` is `-6` in
    Aeneas and `5` in the runtime. -/
theorem bitxor_i_counterexample :
    ¬ RCompOk EncRel (lift ((-1)#i8 ^^^ 5#i8))
      (pure (Hax.bitxor (enc (-1)#i8) (enc 5#i8)) : Id Int) := by
  rw [rcompOk_lift]
  show ¬ (_ : Int) = _
  decide +kernel

/-- Unsigned `&` agrees with `Hax.bitand_w` at the operand width. -/
theorem bitand_w_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (x &&& y))
      (pure (Hax.bitand_w ty.numBits (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv &&& y.bv).toNat : Int) = Hax.bitand_w _ (x.bv.toNat : Int) (y.bv.toNat : Int)
  simp [Hax.bitand_w, Nat.mod_eq_of_lt x.hBounds, Nat.mod_eq_of_lt y.hBounds]

/-- Unsigned `&` agrees with the untagged `Hax.bitand`. -/
theorem bitand_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (x &&& y)) (pure (Hax.bitand (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv &&& y.bv).toNat : Int) = Hax.bitand (x.bv.toNat : Int) (y.bv.toNat : Int)
  simp [Hax.bitand]

/-- Signed `&` agrees with `Hax.bitand_iw` at the operand width. -/
theorem bitand_iw_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (lift (x &&& y))
      (pure (Hax.bitand_iw ty.numBits (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show (x.bv &&& y.bv).toInt = Hax.bitand_iw ty.numBits x.val y.val
  simp only [Hax.bitand_iw, iscalar_cast_uw, Hax.bitand_w, Int.toNat_natCast]
  rw [Nat.mod_eq_of_lt x.bv.isLt, Nat.mod_eq_of_lt y.bv.isLt, BitVec.toInt_eq_toNat_bmod]
  congr 2

/-- Signed `&` is not related to the untagged `Hax.bitand`: `-1i8 & 5i8` is `5` in
    Aeneas and `0` in the runtime. -/
theorem bitand_i_counterexample :
    ¬ RCompOk EncRel (lift ((-1)#i8 &&& 5#i8))
      (pure (Hax.bitand (enc (-1)#i8) (enc 5#i8)) : Id Int) := by
  rw [rcompOk_lift]
  show ¬ (_ : Int) = _
  decide +kernel

/-- Unsigned `|` agrees with `Hax.bitor_w` at the operand width. -/
theorem bitor_w_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (x ||| y))
      (pure (Hax.bitor_w ty.numBits (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv ||| y.bv).toNat : Int) = Hax.bitor_w _ (x.bv.toNat : Int) (y.bv.toNat : Int)
  simp [Hax.bitor_w, Nat.mod_eq_of_lt x.hBounds, Nat.mod_eq_of_lt y.hBounds]

/-- Unsigned `|` agrees with the untagged `Hax.bitor`. -/
theorem bitor_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (x ||| y)) (pure (Hax.bitor (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv ||| y.bv).toNat : Int) = Hax.bitor (x.bv.toNat : Int) (y.bv.toNat : Int)
  simp [Hax.bitor]

/-- Signed `|` agrees with `Hax.bitor_iw` at the operand width. -/
theorem bitor_iw_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (lift (x ||| y))
      (pure (Hax.bitor_iw ty.numBits (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show (x.bv ||| y.bv).toInt = Hax.bitor_iw ty.numBits x.val y.val
  simp only [Hax.bitor_iw, iscalar_cast_uw, Hax.bitor_w, Int.toNat_natCast]
  rw [Nat.mod_eq_of_lt x.bv.isLt, Nat.mod_eq_of_lt y.bv.isLt, BitVec.toInt_eq_toNat_bmod]
  congr 2

/-- Signed `|` is not related to the untagged `Hax.bitor`: `-1i8 | 5i8` is `-1` in
    Aeneas and `5` in the runtime. -/
theorem bitor_i_counterexample :
    ¬ RCompOk EncRel (lift ((-1)#i8 ||| 5#i8))
      (pure (Hax.bitor (enc (-1)#i8) (enc 5#i8)) : Id Int) := by
  rw [rcompOk_lift]
  show ¬ (_ : Int) = _
  decide +kernel

/-- Unsigned `>>` returns, when the shift amount is below the width, the value
    `Hax.shr_w` computes. -/
theorem shr_w_u_square {ty tys : UScalarTy} (x : UScalar ty) (s : UScalar tys) :
    RCompOk EncRel (x >>> s) (pure (Hax.shr_w ty.numBits (enc x) (enc s)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  change UScalar.shiftRight x s.val = _ at h
  unfold UScalar.shiftRight at h
  split at h
  · cases h
    show ((x.bv.ushiftRight s.val).toNat : Int) = Hax.shr_w _ (x.val : Int) (s.val : Int)
    simp [Hax.shr_w, Nat.mod_eq_of_lt x.hBounds]
  · cases h

/-- Unsigned `>>` returns, when the shift amount is below the width, the value the
    untagged `Hax.shr` computes. -/
theorem shr_u_square {ty tys : UScalarTy} (x : UScalar ty) (s : UScalar tys) :
    RCompOk EncRel (x >>> s) (pure (Hax.shr (enc x) (enc s)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  change UScalar.shiftRight x s.val = _ at h
  unfold UScalar.shiftRight at h
  split at h
  · cases h
    show ((x.bv.ushiftRight s.val).toNat : Int) = Hax.shr (x.val : Int) (s.val : Int)
    simp [Hax.shr]
  · cases h

/-- Signed `>>` returns, when the shift amount is below the width, the value
    `Hax.shr_iw` computes: an arithmetic (sign-extending) shift, already within
    signed range, that `Hax.smod2w` leaves unchanged. -/
theorem shr_iw_square {ty : IScalarTy} {tys : UScalarTy} (x : IScalar ty) (s : UScalar tys) :
    RCompOk EncRel (x >>> s) (pure (Hax.shr_iw ty.numBits (enc x) (enc s)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  change IScalar.shiftRight x s.val = _ at h
  unfold IScalar.shiftRight at h
  split at h
  · cases h
    show (x.bv.sshiftRight s.val).toInt = Hax.shr_iw ty.numBits (x.val : Int) (s.val : Int)
    show (x.bv.sshiftRight s.val).toInt = Hax.smod2w ty.numBits (x.bv.toInt >>> s.val)
    rw [← BitVec.toInt_sshiftRight]
    show (x.bv.sshiftRight s.val).toInt = Int.bmod ((x.bv.sshiftRight s.val).toInt) _
    rw [BitVec.toInt_eq_toNat_bmod (x.bv.sshiftRight s.val), Int.bmod_bmod]
  · cases h

/-- Signed `>>` is not related to the untagged `Hax.shr`: `-8i64 >> 1` is `-4` in
    Aeneas (arithmetic shift) and `0` in the runtime. -/
theorem shr_i_counterexample :
    ¬ RCompOk EncRel ((-8)#i64 >>> 1#u32)
      (pure (Hax.shr (enc (-8)#i64) (enc 1#u32)) : Id Int) := by
  refine not_rcompOk_of ⟨BitVec.sshiftRight ((-8)#i64).bv 1⟩ ?_ ?_
  · show IScalar.shiftRight (-8)#i64 (1#u32).val = _
    unfold IScalar.shiftRight
    rw [if_pos (by decide +kernel)]
    rfl
  · show ¬ (_ : Int) = _
    decide +kernel

/-- Unsigned `<<` returns, when the shift amount is below the width, the value
    `Hax.shl_w` computes. -/
theorem shl_w_u_square {ty tys : UScalarTy} (x : UScalar ty) (s : UScalar tys) :
    RCompOk EncRel (x <<< s) (pure (Hax.shl_w ty.numBits (enc x) (enc s)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  change UScalar.shiftLeft x s.val = _ at h
  unfold UScalar.shiftLeft at h
  split at h
  · cases h
    show ((x.bv.shiftLeft s.val).toNat : Int) = Hax.shl_w _ (x.val : Int) (s.val : Int)
    simp only [Hax.shl_w, Hax.mod2w, Int.toNat_natCast, UScalar.val]
    rfl
  · cases h

/-- Signed `<<` returns, when the shift amount is below the width, the value
    `Hax.shl_iw` computes. -/
theorem shl_iw_square {ty : IScalarTy} {tys : UScalarTy} (x : IScalar ty) (s : UScalar tys) :
    RCompOk EncRel (x <<< s) (pure (Hax.shl_iw ty.numBits (enc x) (enc s)) : Id Int) := by
  rw [rcompOk_iff]
  intro a h
  change IScalar.shiftLeft x s.val = _ at h
  unfold IScalar.shiftLeft at h
  split at h
  · cases h
    show (x.bv.shiftLeft s.val).toInt = Hax.shl_iw ty.numBits (x.val : Int) (s.val : Int)
    show (x.bv.shiftLeft s.val).toInt =
      Hax.smod2w ty.numBits (Hax.shl_w ty.numBits (Hax.cast_uw ty.numBits x.val) s.val)
    rw [iscalar_cast_uw, Hax.shl_w, Hax.mod2w, Int.toNat_natCast,
      BitVec.toInt_eq_toNat_bmod (x.bv.shiftLeft s.val)]
    congr 2
  · cases h

/-- Unsigned `<<` is not related to the untagged `Hax.shl`, which does not
    truncate: `128u8 << 1` is `0` in Aeneas and `256` in the runtime. -/
theorem shl_u_counterexample :
    ¬ RCompOk EncRel (128#u8 <<< 1#u32)
      (pure (Hax.shl (enc 128#u8) (enc 1#u32)) : Id Int) := by
  refine not_rcompOk_of ⟨BitVec.shiftLeft (128#u8).bv 1⟩ ?_ ?_
  · show UScalar.shiftLeft 128#u8 (1#u32).val = _
    unfold UScalar.shiftLeft
    rw [if_pos (by decide +kernel)]
    rfl
  · show ¬ (_ : Int) = _
    decide +kernel

/-- Signed `<<` is not related to the untagged `Hax.shl`: `1i8 << 7` is `-128` in
    Aeneas and `128` in the runtime. -/
theorem shl_i_counterexample :
    ¬ RCompOk EncRel (1#i8 <<< 7#u32)
      (pure (Hax.shl (enc 1#i8) (enc 7#u32)) : Id Int) := by
  refine not_rcompOk_of ⟨BitVec.shiftLeft (1#i8).bv 7⟩ ?_ ?_
  · show IScalar.shiftLeft 1#i8 (7#u32).val = _
    unfold IScalar.shiftLeft
    rw [if_pos (by decide +kernel)]
    rfl
  · show ¬ (_ : Int) = _
    decide +kernel

/-- The complement of an unsigned scalar agrees with `Hax.bitnot_w` at its width. -/
theorem bitnot_w_u_square {ty : UScalarTy} (x : UScalar ty) :
    RCompOk EncRel (lift (~~~x)) (pure (Hax.bitnot_w ty.numBits (enc x)) : Id Int) := by
  rw [rcompOk_lift]
  show ((~~~x.bv).toNat : Int) = Hax.bitnot_w _ (x.val : Int)
  simp [Hax.bitnot_w, BitVec.toNat_not, Nat.mod_eq_of_lt x.hBounds]

/-- The complement of a signed scalar agrees with `Hax.bitnot_iw` at its width. -/
theorem bitnot_iw_square {ty : IScalarTy} (x : IScalar ty) :
    RCompOk EncRel (lift (~~~x)) (pure (Hax.bitnot_iw ty.numBits (enc x)) : Id Int) := by
  rw [rcompOk_lift]
  show (~~~x.bv).toInt = Hax.bitnot_iw ty.numBits x.val
  simp only [Hax.bitnot_iw, iscalar_cast_uw, Hax.bitnot_w, Int.toNat_natCast]
  rw [Nat.mod_eq_of_lt x.bv.isLt, BitVec.toInt_eq_toNat_bmod]
  congr 2
  rw [BitVec.toNat_not]

/-- Unsigned `rotate_right` agrees with `Hax.rotate_right_w` at the operand width. -/
theorem rotate_right_w_u_square {ty : UScalarTy} (x : UScalar ty) (s : U32) :
    RCompOk EncRel (lift (UScalar.rotate_right x s))
      (pure (Hax.rotate_right_w ty.numBits (enc x) (enc s)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv.rotateRight s.val).toNat : Int) = Hax.rotate_right_w _ (x.val : Int) (s.val : Int)
  simp only [Hax.rotate_right_w, Hax.mod2w, Int.toNat_natCast, BitVec.toNat_rotateRight,
    Nat.or_mod_two_pow, UScalar.val, Nat.mod_eq_of_lt x.bv.isLt]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.bv.isLt)]

/-- `u64::rotate_right` agrees with the untagged `Hax.rotate_right`, which rotates
    within 64 bits. -/
theorem rotate_right_u64_square (x : U64) (s : U32) :
    RCompOk EncRel (lift (UScalar.rotate_right x s))
      (pure (Hax.rotate_right (enc x) (enc s)) : Id Int) := by
  have h := rotate_right_w_u_square x s
  rw [rcompOk_lift, encRel_iff] at h ⊢
  rw [h]
  have hx : x.val < 2 ^ 64 := x.hBounds
  simp only [Hax.rotate_right_w, Hax.rotate_right, Hax.mod2w, Int.toNat_natCast, enc_uscalar,
    UScalarTy.numBits, Nat.mod_eq_of_lt hx]

/-- `u32::rotate_right` is not related to the untagged `Hax.rotate_right`:
    `1u32.rotate_right(1)` is `2^31` in Aeneas and `2^63` in the runtime. -/
theorem rotate_right_u32_counterexample :
    ¬ RCompOk EncRel (lift (UScalar.rotate_right 1#u32 1#u32))
      (pure (Hax.rotate_right (enc 1#u32) (enc 1#u32)) : Id Int) := by
  rw [rcompOk_lift]
  show ¬ (_ : Int) = _
  decide +kernel

/-- Rotating the all-ones vector by `0` leaves it unchanged. -/
theorem rotateRight_allOnes_zero (w : Nat) :
    (BitVec.allOnes w).rotateRight 0 = BitVec.allOnes w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.zero_mod, Nat.shiftRight_zero, Nat.sub_zero, Nat.shiftLeft_eq,
    Nat.mul_mod_left, Nat.or_zero]

/-- Signed `rotate_right` agrees with `Hax.rotate_right_iw` at the operand width. -/
theorem rotate_right_iw_square {ty : IScalarTy} (x : IScalar ty) (s : U32) :
    RCompOk EncRel (lift (IScalar.rotate_right x s))
      (pure (Hax.rotate_right_iw ty.numBits (enc x) (enc s)) : Id Int) := by
  rw [rcompOk_lift]
  show (x.bv.rotateRight s.val).toInt = Hax.rotate_right_iw ty.numBits (x.val : Int) (s.val : Int)
  show (x.bv.rotateRight s.val).toInt =
    Hax.smod2w ty.numBits (Hax.rotate_right_w ty.numBits (Hax.cast_uw ty.numBits x.val) s.val)
  rw [iscalar_cast_uw]
  have hcore : Hax.rotate_right_w ty.numBits (x.bv.toNat : Int) s.val =
      ((x.bv.rotateRight s.val).toNat : Int) := by
    simp only [Hax.rotate_right_w, Hax.mod2w, Int.toNat_natCast, BitVec.toNat_rotateRight,
      Nat.or_mod_two_pow, Nat.mod_eq_of_lt x.bv.isLt]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.bv.isLt)]
  rw [hcore, BitVec.toInt_eq_toNat_bmod, Hax.smod2w]

/-- Signed `rotate_right` is not related to the untagged `Hax.rotate_right`:
    rotating `-1` by `0` gives `-1` in Aeneas and `0` in the runtime, at every signed
    type. -/
theorem rotate_right_i_counterexample (ty : IScalarTy) :
    ¬ RCompOk EncRel (lift (IScalar.rotate_right (iMinusOne ty) 0#u32))
      (pure (Hax.rotate_right (enc (iMinusOne ty)) (enc 0#u32)) : Id Int) := by
  rw [rcompOk_lift, encRel_iff]
  simp only [enc_iscalar, iMinusOne_val]
  show ¬ ((BitVec.allOnes ty.numBits).rotateRight (0#u32).val).toInt = _
  simp only [Hax.rotate_right]
  show ¬ ((BitVec.allOnes ty.numBits).rotateRight 0).toInt = _
  rw [rotateRight_allOnes_zero, allOnes_toInt]
  simp

/-- Unsigned `wrapping_add` agrees with `Hax.wrapping_add_w` at the operand width. -/
theorem wrapping_add_w_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (UScalar.wrapping_add x y))
      (pure (Hax.wrapping_add_w ty.numBits (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv + y.bv).toNat : Int) = Hax.wrapping_add_w _ (x.val : Int) (y.val : Int)
  simp only [Hax.wrapping_add_w, Hax.mod2w, BitVec.toNat_add, UScalar.val]
  rw [← Int.natCast_add, Int.toNat_natCast]

/-- Signed `wrapping_add` agrees with `Hax.wrapping_add_iw` at the operand width. -/
theorem wrapping_add_iw_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (lift (IScalar.wrapping_add x y))
      (pure (Hax.wrapping_add_iw ty.numBits (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show (x.bv + y.bv).toInt = Hax.wrapping_add_iw ty.numBits (x.val : Int) (y.val : Int)
  simp only [Hax.wrapping_add_iw, Hax.smod2w, IScalar.val]
  rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_add]
  apply bmodCongr
  rw [Int.add_emod x.bv.toInt y.bv.toInt, iscalar_mod, iscalar_mod]
  simp

/-- Unsigned `wrapping_add` is not related to the untagged `Hax.wrapping_add`, which
    does not wrap: `255u8.wrapping_add(1)` is `0` in Aeneas and `256` in the runtime. -/
theorem wrapping_add_u_counterexample :
    ¬ RCompOk EncRel (lift (UScalar.wrapping_add 255#u8 1#u8))
      (pure (Hax.wrapping_add (enc 255#u8) (enc 1#u8)) : Id Int) := by
  rw [rcompOk_lift]
  show ¬ (_ : Int) = _
  decide +kernel

/-- Signed `wrapping_add` is not related to the untagged `Hax.wrapping_add`:
    `127i8.wrapping_add(1)` is `-128` in Aeneas and `128` in the runtime. -/
theorem wrapping_add_i_counterexample :
    ¬ RCompOk EncRel (lift (IScalar.wrapping_add 127#i8 1#i8))
      (pure (Hax.wrapping_add (enc 127#i8) (enc 1#i8)) : Id Int) := by
  rw [rcompOk_lift]
  show ¬ (_ : Int) = _
  decide +kernel

/-- Unsigned `wrapping_mul` agrees with `Hax.wrapping_mul_w` at the operand width. -/
theorem wrapping_mul_w_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (UScalar.wrapping_mul x y))
      (pure (Hax.wrapping_mul_w ty.numBits (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv * y.bv).toNat : Int) = Hax.wrapping_mul_w _ (x.val : Int) (y.val : Int)
  simp only [Hax.wrapping_mul_w, Hax.mod2w, BitVec.toNat_mul, UScalar.val]
  rw [← Int.natCast_mul, Int.toNat_natCast]

/-- Signed `wrapping_mul` agrees with `Hax.wrapping_mul_iw` at the operand width. -/
theorem wrapping_mul_iw_square {ty : IScalarTy} (x y : IScalar ty) :
    RCompOk EncRel (lift (IScalar.wrapping_mul x y))
      (pure (Hax.wrapping_mul_iw ty.numBits (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show (x.bv * y.bv).toInt = Hax.wrapping_mul_iw ty.numBits (x.val : Int) (y.val : Int)
  simp only [Hax.wrapping_mul_iw, Hax.smod2w, IScalar.val]
  rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_mul]
  apply bmodCongr
  rw [Int.mul_emod x.bv.toInt y.bv.toInt, iscalar_mod, iscalar_mod]
  simp

/-- Unsigned `wrapping_mul` is not related to the untagged `Hax.wrapping_mul`, which
    does not wrap: `16u8.wrapping_mul(16)` is `0` in Aeneas and `256` in the runtime. -/
theorem wrapping_mul_u_counterexample :
    ¬ RCompOk EncRel (lift (UScalar.wrapping_mul 16#u8 16#u8))
      (pure (Hax.wrapping_mul (enc 16#u8) (enc 16#u8)) : Id Int) := by
  rw [rcompOk_lift]
  show ¬ (_ : Int) = _
  decide +kernel

/-- Signed `wrapping_mul` is not related to the untagged `Hax.wrapping_mul`:
    `(-128i8).wrapping_mul(-1)` is `-128` in Aeneas and `128` in the runtime. -/
theorem wrapping_mul_i_counterexample :
    ¬ RCompOk EncRel (lift (IScalar.wrapping_mul (-128)#i8 (-1)#i8))
      (pure (Hax.wrapping_mul (enc (-128)#i8) (enc (-1)#i8)) : Id Int) := by
  rw [rcompOk_lift]
  show ¬ (_ : Int) = _
  decide +kernel

/-- Unsigned `overflowing_sub` at a borrow agrees with `Hax.overflowing_sub_w`:
    `0u8.overflowing_sub(1)` is `(255, true)` in both Aeneas and the runtime. -/
theorem overflowing_sub_w_square :
    RCompOk EncRel (lift (UScalar.overflowing_sub 0#u8 1#u8))
      (pure (Hax.overflowing_sub_w 8 (enc 0#u8) (enc 1#u8)) : Id (Int × Bool)) := by
  rw [rcompOk_lift]
  show (_ : Int × Bool) = _
  decide +kernel

end CatCrypt.Hax.RustSemantics
