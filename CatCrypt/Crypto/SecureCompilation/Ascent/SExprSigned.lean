/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt
public meta import Std.Tactic.BVDecide.Reflect
public import Std.Tactic.BVDecide

/-!
# Signed word operations as scalar expressions

A signed integer `z` of `i8` to `i64` is held in a `u64` slot as its 64-bit two's
complement `BitVec.ofInt 64 z`.  The expressions below compute the signed operations on
such slots with the operations `lowerSExpr` lowers (`SAdd`, `SSub`, `SMul`, `SAnd`,
`SXor`, `SShl`, `SShr`, literals); `SAsr` and `SLt` have no lowering arm.

* sign extension from `w` bits, `((e &&& (2^w - 1)) ^^^ 2^(w-1)) - 2^(w-1)`
  (`sextSExpr`), the two's complement of the residue of the value in
  `[-2^(w-1), 2^(w-1))`;
* the arithmetic shift right `((a ^^^ m) >>> k) ^^^ m` with the sign mask
  `m = 0 - (a >>> 63)` (`asrSExpr`);
* the signed comparison `a <ₛ b` as the unsigned comparison `ltExpr` of the operands
  with their sign bits flipped (`sltSExpr`).

## Main results

* `signExtend_setWidth_ofInt` — sign extension from `w` bits of the two's complement of
  `z` is the two's complement of `z.bmod (2^w)`.
* `evalBV_sextSExpr`, `evalBV_sextSExpr_ofInt` — the value of `sextSExpr`.
* `evalBV_asrSExpr`, `sshiftRight_ofInt` — the value of `asrSExpr`, and the arithmetic
  shift of an `i64` value as `Int.shiftRight`.
* `evalBV_sltSExpr`, `slt_ofInt` — the value of `sltSExpr`, and the signed comparison of
  two `i64` values as the integer comparison.
* `ofInt_sub`, `ofInt_shiftLeft`, `ofInt_bmod64`, `toNat_ofInt_and_mask` — the
  two's complement of a difference, of a product by `2^k`, of a residue modulo `2^64`,
  and the low `w` bits of a two's complement.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt (ltExpr ltWord evalBV_ltExpr)

/-! ### Two's complement of integers -/

/-- Sign extension from `w` bits of the two's complement of `z` is the two's complement
    of the residue of `z` modulo `2^w` in `[-2^(w-1), 2^(w-1))`. -/
theorem signExtend_setWidth_ofInt (z : Int) {w : Nat} (hw : w ≤ 64) :
    ((BitVec.ofInt 64 z).setWidth w).signExtend 64 = BitVec.ofInt 64 (z.bmod (2 ^ w)) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le hw, BitVec.toInt_ofInt, BitVec.toInt_setWidth,
    BitVec.toNat_ofInt]
  have hd : (((2 ^ w : Nat)) : Int) ∣ ((2 ^ 64 : Nat) : Int) := by
    exact_mod_cast Nat.pow_dvd_pow 2 hw
  have hmod := Int.emod_emod_of_dvd z hd
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  have h1 : (z % ((2 ^ 64 : Nat) : Int)).bmod (2 ^ w) = z.bmod (2 ^ w) := by
    simp only [Int.bmod, hmod]
  rw [h1]
  symm
  apply Int.bmod_eq_of_le
  · have := @Int.le_bmod z (2 ^ w) (by positivity)
    have h3 : ((2 : Nat) ^ w : Int) / 2 ≤ (2 ^ 64 : Nat) / 2 :=
      Int.ediv_le_ediv (by decide) (by exact_mod_cast Nat.pow_le_pow_right (by decide) hw)
    push_cast at *; omega
  · have := @Int.bmod_lt z (2 ^ w) (by positivity)
    have h3 : ((2 : Nat) ^ w + 1 : Int) / 2 ≤ ((2 ^ 64 : Nat) + 1) / 2 :=
      Int.ediv_le_ediv (by decide)
        (by have := Nat.pow_le_pow_right (n := 2) (by decide) hw; omega)
    push_cast at *; omega

/-- The two's complement of a residue modulo `2^64` is the two's complement of the
    integer. -/
theorem ofInt_bmod64 (z : Int) : BitVec.ofInt 64 (z.bmod (2 ^ 64)) = BitVec.ofInt 64 z := by
  have h := signExtend_setWidth_ofInt z (w := 64) (le_refl _)
  rw [← h]
  simp

/-- The two's complement of a difference is the difference of the two's complements. -/
theorem ofInt_sub (x y : Int) :
    BitVec.ofInt 64 (x - y) = BitVec.ofInt 64 x - BitVec.ofInt 64 y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- The two's complement of `x · 2^k` is the two's complement of `x` shifted left by
    `k`. -/
theorem ofInt_shiftLeft (x : Int) (k : Nat) :
    BitVec.ofInt 64 x <<< k = BitVec.ofInt 64 (x * 2 ^ k) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofInt_mul]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_twoPow, BitVec.toNat_ofInt]
  have : ((2 : Int) ^ k) = ((2 ^ k : Nat) : Int) := by push_cast; rfl
  rw [this, ← Int.natCast_emod]
  simp only [Int.toNat_natCast]

/-- The low `w` bits of the two's complement of `z` are the residue of `z` modulo
    `2^w`. -/
theorem toNat_ofInt_and_mask (z : Int) {w : Nat} (hw : w ≤ 64) :
    (BitVec.ofInt 64 z &&& BitVec.ofNat 64 (2 ^ w - 1)).toNat = (z % 2 ^ w).toNat := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  have hlt : 2 ^ w - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hw
    have : 0 < 2 ^ w := by positivity
    omega
  rw [Nat.mod_eq_of_lt hlt, Nat.and_two_pow_sub_one_eq_mod]
  have hd : (((2 ^ w : Nat)) : Int) ∣ ((2 ^ 64 : Nat) : Int) := by
    exact_mod_cast Nat.pow_dvd_pow 2 hw
  have hmod := Int.emod_emod_of_dvd z hd
  have hnn : 0 ≤ z % ((2 ^ 64 : Nat) : Int) := Int.emod_nonneg _ (by positivity)
  have h2 : (((z % ((2 ^ 64 : Nat) : Int)).toNat % 2 ^ w : Nat) : Int) = z % 2 ^ w := by
    rw [Int.natCast_mod, Int.toNat_of_nonneg hnn]
    push_cast at hmod ⊢
    exact hmod
  rw [← h2, Int.toNat_natCast]

/-! ### Sign extension -/

/-- Sign extension from `w` bits: for `w < 64`, the low `w` bits of `e` with the sign
    bit flipped, minus the sign bit; for `w = 64`, `e`. -/
def sextSExpr (w : Nat) (e : SExpr) : SExpr :=
  if w = 64 then e
  else .SSub (.SXor (.SAnd e (.SLit (2 ^ w - 1))) (.SLit (2 ^ (w - 1)))) (.SLit (2 ^ (w - 1)))

/-- `sextSExpr w e` evaluates to the sign extension from `w` bits of the value of `e`. -/
theorem evalBV_sextSExpr {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (β : String → BitVec 64) (e : SExpr) :
    (sextSExpr w e).evalBV β = ((e.evalBV β).setWidth w).signExtend 64 := by
  rcases hw with rfl | rfl | rfl | rfl
  · simp only [sextSExpr, show ¬ ((8 : Nat) = 64) from by decide, ite_false, SExpr.evalBV]
    generalize e.evalBV β = v
    bv_decide
  · simp only [sextSExpr, show ¬ ((16 : Nat) = 64) from by decide, ite_false, SExpr.evalBV]
    generalize e.evalBV β = v
    bv_decide
  · simp only [sextSExpr, show ¬ ((32 : Nat) = 64) from by decide, ite_false, SExpr.evalBV]
    generalize e.evalBV β = v
    bv_decide
  · simp [sextSExpr]

/-- On a value that is the two's complement of `z`, `sextSExpr w` evaluates to the two's
    complement of `z.bmod (2^w)`. -/
theorem evalBV_sextSExpr_ofInt {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (β : String → BitVec 64) {e : SExpr} {z : Int} (he : e.evalBV β = BitVec.ofInt 64 z) :
    (sextSExpr w e).evalBV β = BitVec.ofInt 64 (z.bmod (2 ^ w)) := by
  rw [evalBV_sextSExpr hw, he]
  exact signExtend_setWidth_ofInt z (by omega)

/-! ### Arithmetic shift right -/

/-- The sign mask of a word: all ones when its bit `63` is set, zero otherwise. -/
def signMaskSExpr (a : SExpr) : SExpr := .SSub (.SLit 0) (.SShr a (.SLit 63))

/-- The arithmetic shift right of `a` by `k`: `a` complemented when negative, shifted
    logically, and complemented back. -/
def asrSExpr (a k : SExpr) : SExpr := .SXor (.SShr (.SXor a (signMaskSExpr a)) k) (signMaskSExpr a)

/-- The arithmetic shift of a word through its sign mask `m`: complement by `m`, shift
    logically, complement by `m`. -/
theorem asr_word (v n : BitVec 64) :
    ((v ^^^ ((0 : BitVec 64) - (v >>> (63 : Nat)))) >>> n.toNat) ^^^
      ((0 : BitVec 64) - (v >>> (63 : Nat))) = v.sshiftRight n.toNat := by
  have e1 : v.sshiftRight n.toNat = v.sshiftRight' n := rfl
  have e2 : ((v ^^^ ((0 : BitVec 64) - (v >>> (63 : Nat)))) >>> n.toNat) =
      ((v ^^^ ((0 : BitVec 64) - (v >>> (63 : Nat)))) >>> n) := rfl
  rw [e1, e2]
  bv_decide

/-- `asrSExpr a k` evaluates to the arithmetic shift of the value of `a` by the value of
    `k` masked by `VIR.shiftMask 64`. -/
theorem evalBV_asrSExpr (β : String → BitVec 64) (a k : SExpr) :
    (asrSExpr a k).evalBV β
      = (a.evalBV β).sshiftRight (VIR.shiftMask 64 (k.evalBV β).toNat) := by
  simp only [asrSExpr, signMaskSExpr, SExpr.evalBV]
  rw [show BitVec.ofNat 64 0 = (0 : BitVec 64) from rfl,
    show (BitVec.ofNat 64 63).toNat = 63 from rfl,
    VIR.shiftMask_of_lt (by decide : 63 < 64)]
  have h := asr_word (a.evalBV β) (BitVec.ofNat 64 (VIR.shiftMask 64 (k.evalBV β).toNat))
  rwa [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_trans (VIR.shiftMask_lt_64 _) (by decide))] at h

/-- The arithmetic shift of the two's complement of an `i64` value `z` is the two's
    complement of `z` shifted right as an integer. -/
theorem sshiftRight_ofInt {z : Int} (h1 : -2 ^ 63 ≤ z) (h2 : z < 2 ^ 63) (k : Nat) :
    (BitVec.ofInt 64 z).sshiftRight k = BitVec.ofInt 64 (z >>> k) := by
  have hz : (BitVec.ofInt 64 z).toInt = z := by
    rw [BitVec.toInt_ofInt]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, hz, BitVec.toInt_ofInt]
  have hs : z >>> k = z / 2 ^ k := Int.shiftRight_eq_div_pow z k
  have hp : (0 : Int) < 2 ^ k := by positivity
  have hlo : -2 ^ 63 ≤ z / 2 ^ k := by
    rw [Int.le_ediv_iff_mul_le hp]
    have : (1 : Int) ≤ 2 ^ k := by omega
    nlinarith
  have hhi : z / 2 ^ k < 2 ^ 63 := by
    by_cases hz0 : z < 0
    · have : z / 2 ^ k ≤ 0 := Int.ediv_nonpos_of_nonpos_of_neg (by omega) hp
      omega
    · exact lt_of_le_of_lt (Int.ediv_le_self _ (by omega)) h2
  rw [hs]
  symm
  exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)

/-! ### Signed comparison -/

/-- The signed comparison of two words is the unsigned comparison of the words with their
    sign bits flipped. -/
theorem slt_word (x y : BitVec 64) :
    (if (x ^^^ BitVec.ofNat 64 (2 ^ 63)).toNat < (y ^^^ BitVec.ofNat 64 (2 ^ 63)).toNat
      then (1 : BitVec 64) else 0) = if x.slt y then 1 else 0 := by
  have hs : (x ^^^ BitVec.ofNat 64 (2 ^ 63)).ult (y ^^^ BitVec.ofNat 64 (2 ^ 63)) = x.slt y := by
    bv_decide
  rw [← hs]
  simp [BitVec.ult]

/-- The signed comparison `a <ₛ b`: the unsigned comparison of the operands with their
    sign bits flipped. -/
def sltSExpr (a b : SExpr) : SExpr :=
  ltExpr (.SXor a (.SLit (2 ^ 63))) (.SXor b (.SLit (2 ^ 63)))

/-- `sltSExpr a b` evaluates to `1` when the value of `a` is below the value of `b` as
    signed words, and to `0` otherwise. -/
theorem evalBV_sltSExpr (β : String → BitVec 64) (a b : SExpr) :
    (sltSExpr a b).evalBV β = if (a.evalBV β).slt (b.evalBV β) then 1 else 0 := by
  simp only [sltSExpr, evalBV_ltExpr, ltWord, SExpr.evalBV]
  exact slt_word _ _

/-- The signed comparison of the two's complements of two `i64` values is the integer
    comparison. -/
theorem slt_ofInt {a b : Int} (ha1 : -2 ^ 63 ≤ a) (ha2 : a < 2 ^ 63) (hb1 : -2 ^ 63 ≤ b)
    (hb2 : b < 2 ^ 63) : (BitVec.ofInt 64 a).slt (BitVec.ofInt 64 b) = decide (a < b) := by
  have hA : (BitVec.ofInt 64 a).toInt = a := by
    rw [BitVec.toInt_ofInt]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  have hB : (BitVec.ofInt 64 b).toInt = b := by
    rw [BitVec.toInt_ofInt]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, hA, hB, decide_eq_true_iff]

end CatCrypt.Crypto.SecureCompilation.Ascent
