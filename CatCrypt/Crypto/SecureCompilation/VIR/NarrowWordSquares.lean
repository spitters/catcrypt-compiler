/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import Transfer.Base.RelatedOn

/-!
# Narrow words held in 64-bit registers: the squares of the operations

A value `v : BitVec w` of a register of width `w ≤ 64` is held in a 64-bit register `x` in
one of two ways. The *strict* relation is `x = v.setWidth 64`: the high `64 - w` bits are zero.
The *lazy* relation is `x.setWidth w = v`: the high bits are arbitrary. The strict relation is
the lazy one together with `HighZero w x`, `x.toNat < 2 ^ w` (`eq_setWidth_iff`), and the mask
`x &&& maskW w`, the conjunction with the constant `2 ^ w - 1`, sends a lazy representative to
the strict one (`and_maskW`).

The squares of this module are stated along the encoding `lowW w = BitVec.setWidth w` from
`BitVec 64` to `BitVec w`, as instances of the ParamTransfer classes `RelatedBinOp`,
`RelatedUnOp`, `RelatedBinOpOn`, `RelatedUnOpOn` and `RelatedRelOn`, at every width `w` with
`w ≤ 64` (the class `WordLe64`), or `w ≤ 32` for the operations whose `w`-bit form masks a shift
count to five bits. Each square names the 64-bit form of a `w`-bit operation of
`jasminDialect`:

* addition, subtraction, multiplication, the bitwise operations, the complement, a left shift
  by an immediate, the select and the data word of a carry-chain addition commute with
  `lowW w` on every operand (total squares);
* the logical right shift by an immediate needs the high bits of the operand zero, the
  rotation is the shift pair `(x >>> k) ||| (x <<< (w - k))` on such an operand, and the
  arithmetic right shift is the shift to the top of the register followed by the arithmetic
  shift by `64 - w + k` (total);
* a register shift masks its count to five bits at `w ≤ 32` (`JasminBinOp.apply`), so its
  64-bit form shifts by the count conjoined with `31`, on a count with zero high bits;
* the high word of the product at `w ≤ 32` is the 64-bit product shifted right by `w`, on
  operands with zero high bits; the comparisons agree on such operands;
* the mask is the identity along `lowW w`.

## Main definitions

* `lowW`, `maskW`, `HighZero`, `WordLe64`, `WordLe32`.

## Main results

* `eq_setWidth_iff`, `and_maskW`, `highZero_and_maskW` — the strict relation, and the mask.
* `addSq`, `subSq`, `mulSq`, `andSq`, `orSq`, `xorSq`, `andnSq`, `notSq`, `shlImmSq`,
  `selectSq`, `addCarryLoSq`, `maskSq`, `sarImmSq` — the total squares.
* `shrImmSq`, `rorImmSq`, `shlRegSq`, `shrRegSq`, `mulhiSq`, `cmpSq` — the guarded squares.
* `constSq`, `carryOutBit_wide`, `castW_wide` — the constant, the carry bit and the casts.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

open Transfer
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The encoding, the mask and the strict relation -/

/-- The encoding of a 64-bit register as a `w`-bit word: its low `w` bits. -/
abbrev lowW (w : Nat) : BitVec 64 → BitVec w := BitVec.setWidth w

/-- The mask of width `w`: the 64-bit constant `2 ^ w - 1`. -/
def maskW (w : Nat) : BitVec 64 := BitVec.ofNat 64 (2 ^ w - 1)

/-- The high `64 - w` bits of a 64-bit register are zero. -/
def HighZero (w : Nat) (x : BitVec 64) : Prop := x.toNat < 2 ^ w

/-- A width of at most `64` bits. -/
class WordLe64 (w : Nat) : Prop where
  /-- The bound. -/
  le : w ≤ 64

/-- A width of at most `32` bits: the widths at which a register shift masks its count to
    five bits. -/
class WordLe32 (w : Nat) : Prop where
  /-- The bound. -/
  le : w ≤ 32

/-- A width of at most `32` bits is a width of at most `64` bits. -/
instance (priority := low) WordLe32.toWordLe64 (w : Nat) [h : WordLe32 w] : WordLe64 w :=
  ⟨Nat.le_trans h.le (by decide)⟩

/-- The width `8`. -/
instance : WordLe32 8 := ⟨by decide⟩
/-- The width `16`. -/
instance : WordLe32 16 := ⟨by decide⟩
/-- The width `32`. -/
instance : WordLe32 32 := ⟨by decide⟩
/-- The width `64`. -/
instance : WordLe64 64 := ⟨by decide⟩

/-- The bound `2 ^ w ≤ 2 ^ 64` at a width of at most `64` bits. -/
theorem two_pow_le_64 {w : Nat} (hw : w ≤ 64) : 2 ^ w ≤ 2 ^ 64 :=
  Nat.pow_le_pow_right (by decide) hw

/-- The mask of width `w` is the all-ones word of width `w`, zero-extended. -/
theorem maskW_eq {w : Nat} (hw : w ≤ 64) : maskW w = (BitVec.allOnes w).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have h1 := two_pow_le_64 hw
  have h2 : 0 < 2 ^ w := Nat.two_pow_pos w
  simp only [maskW, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_allOnes]

/-- **The mask.** Conjoining with the mask of width `w` zero-extends the low `w` bits. -/
theorem and_maskW {w : Nat} (hw : w ≤ 64) (x : BitVec 64) :
    x &&& maskW w = (lowW w x).setWidth 64 := by
  rw [maskW_eq hw]
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_allOnes]
  by_cases h : i < w <;> simp [h, hi]

/-- **The strict relation** is the lazy relation with zero high bits. -/
theorem eq_setWidth_iff {w : Nat} (hw : w ≤ 64) (x : BitVec 64) (v : BitVec w) :
    x = v.setWidth 64 ↔ lowW w x = v ∧ HighZero w x := by
  have h1 := two_pow_le_64 hw
  constructor
  · rintro rfl
    refine ⟨by simp [BitVec.setWidth_setWidth_of_le _ hw], ?_⟩
    simp only [HighZero, BitVec.toNat_setWidth]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) v.isLt
  · rintro ⟨rfl, h⟩
    apply BitVec.eq_of_toNat_eq
    simp only [lowW, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt x.isLt]

/-- A zero-extended word has zero high bits. -/
theorem highZero_setWidth {w : Nat} (hw : w ≤ 64) (v : BitVec w) :
    HighZero w (v.setWidth 64) :=
  ((eq_setWidth_iff hw _ v).mp rfl).2

/-- A zero-extended word is encoded as itself. -/
theorem lowW_setWidth {w : Nat} (hw : w ≤ 64) (v : BitVec w) : lowW w (v.setWidth 64) = v :=
  ((eq_setWidth_iff hw _ v).mp rfl).1

/-- A masked register has zero high bits. -/
theorem highZero_and_maskW {w : Nat} (hw : w ≤ 64) (x : BitVec 64) :
    HighZero w (x &&& maskW w) := by
  rw [and_maskW hw]
  exact highZero_setWidth hw _

/-- A register with zero high bits is the zero extension of its encoding. -/
theorem eq_of_highZero {w : Nat} (hw : w ≤ 64) {x : BitVec 64} (h : HighZero w x) :
    x = (lowW w x).setWidth 64 :=
  (eq_setWidth_iff hw x _).mpr ⟨rfl, h⟩

/-! ## 2. The total squares -/

section Total

variable {w : Nat} [hw : WordLe64 w]

/-- The square of addition. -/
instance addSq : RelatedBinOp (lowW w) (· + ·) (· + ·) where
  comm x y := BitVec.setWidth_add x y hw.le

/-- The square of multiplication. -/
instance mulSq : RelatedBinOp (lowW w) (· * ·) (· * ·) where
  comm x y := BitVec.setWidth_mul x y hw.le

/-- The square of subtraction. -/
instance subSq : RelatedBinOp (lowW w) (· - ·) (· - ·) where
  comm x y := by
    simp only [lowW, BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ hw.le,
      BitVec.setWidth_neg_of_le hw.le]

/-- The square of conjunction. -/
instance andSq : RelatedBinOp (lowW w) (· &&& ·) (· &&& ·) where
  comm _ _ := BitVec.setWidth_and

/-- The square of disjunction. -/
instance orSq : RelatedBinOp (lowW w) (· ||| ·) (· ||| ·) where
  comm _ _ := BitVec.setWidth_or

/-- The square of exclusive disjunction. -/
instance xorSq : RelatedBinOp (lowW w) (· ^^^ ·) (· ^^^ ·) where
  comm _ _ := BitVec.setWidth_xor

/-- The square of the complement. -/
instance notSq : RelatedUnOp (lowW w) (~~~ ·) (~~~ ·) where
  comm _ := BitVec.setWidth_not hw.le

/-- The square of the conjunction with a complemented first argument. -/
instance andnSq : RelatedBinOp (lowW w) (fun a b => ~~~a &&& b) (fun a b => ~~~a &&& b) where
  comm _ _ := by simp only [lowW, BitVec.setWidth_and, BitVec.setWidth_not hw.le]

/-- The square of the left shift by an immediate. -/
instance shlImmSq (k : Nat) : RelatedUnOp (lowW w) (· <<< k) (· <<< k) where
  comm _ := BitVec.setWidth_shiftLeft_of_le hw.le

/-- The square of the select on a condition bit. -/
instance selectSq (c : BitVec 1) : RelatedBinOp (lowW w) (selectW c) (selectW c) where
  comm x y := by unfold selectW; split <;> rfl

/-- The square of the data word of a carry-chain addition with carry-in `c`. -/
instance addCarryLoSq (c : BitVec 1) :
    RelatedBinOp (lowW w) (fun x y => x + y + BitVec.ofNat 64 c.toNat)
      (fun a b => addCarryWord a b c) where
  comm x y := by
    simp only [lowW, addCarryWord, BitVec.setWidth_add _ _ hw.le]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have := c.isLt
    have h1 : 2 ≤ 2 ^ w ∨ w = 0 := by
      rcases Nat.eq_zero_or_pos w with h | h
      · exact Or.inr h
      · exact Or.inl (Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) h))
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rcases h1 with h1 | rfl
    · rw [Nat.mod_eq_of_lt (by omega : c.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    · simp

/-- The mask is the identity along the encoding. -/
instance maskSq : RelatedUnOp (lowW w) (· &&& maskW w) id where
  comm x := by
    rw [and_maskW hw.le]
    exact lowW_setWidth hw.le _

/-- The arithmetic right shift by `k` at width `w` is the shift of the word to the top of the
    register followed by the arithmetic shift by `64 - w + k`. -/
instance sarImmSq (k : Nat) :
    RelatedUnOp (lowW w) (fun x => (x <<< (64 - w)).sshiftRight (64 - w + k))
      (fun a => a.sshiftRight k) where
  comm x := by
    have hle := hw.le
    ext i hi
    simp only [lowW, BitVec.getElem_setWidth, BitVec.getElem_sshiftRight,
      BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.msb_eq_getLsbD_last]
    by_cases hk : k + i < w
    · have h1 : ¬ 64 ≤ i := by omega
      have h2 : 64 - w + k + i < 64 := by omega
      simp [h1, h2, hk, show ¬ 64 - w + k + i < 64 - w by omega,
        show 64 - w + k + i - (64 - w) = k + i by omega, show k + i < 64 by omega]
    · have h1 : ¬ 64 ≤ i := by omega
      have hw0 : 0 < w := by omega
      have h2 : ¬ 64 - w + k + i < 64 := by omega
      simp [h1, h2, hk, show ¬ (64 - 1 < 64 - w) by omega,
          show 64 - 1 - (64 - w) = w - 1 by omega, show w - 1 < 64 by omega,
          show w - 1 < w by omega]

end Total

/-! ## 3. The guarded squares -/

section Guarded

variable {w : Nat} [hw : WordLe64 w]

/-- On a register with zero high bits, the logical right shift commutes with the encoding. -/
instance shrImmSq (k : Nat) : RelatedUnOpOn (lowW w) (HighZero w) (· >>> k) (· >>> k) where
  comm x hx := by
    conv_lhs => rw [eq_of_highZero hw.le hx]
    rw [← BitVec.setWidth_ushiftRight (by exact hw.le : w ≤ 64)]
    exact lowW_setWidth hw.le _

/-- On a register with zero high bits, the rotation by `k` is the pair of shifts by `k % w`
    and `w - k % w`, joined by a disjunction. -/
instance rorImmSq (k : Nat) :
    RelatedUnOpOn (lowW w) (HighZero w)
      (fun x => (x >>> (k % w)) ||| (x <<< (w - k % w))) (fun a => a.rotateRight k) where
  comm x hx := by
    have hle := hw.le
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0; exact Subsingleton.elim _ _
    have hkw : k % w < w := Nat.mod_lt _ h0
    rw [BitVec.rotateRight_def]
    simp only [lowW, BitVec.setWidth_or]
    congr 1
    · exact (shrImmSq (w := w) (k % w)).comm x hx
    · exact BitVec.setWidth_shiftLeft_of_le hle

end Guarded

/-- At a width of at most `32` bits a shift count is masked to five bits. -/
theorem shiftMask_of_le32 {w : Nat} (h : w ≤ 32) (k : Nat) : shiftMask w k = k % 32 := by
  unfold shiftMask
  simp [show w ≠ 64 by omega, h]

/-- The count conjoined with `31` is the count modulo `32`. -/
theorem toNat_and_31 (y : BitVec 64) : (y &&& BitVec.ofNat 64 31).toNat = y.toNat % 32 := by
  rw [BitVec.toNat_and, show (BitVec.ofNat 64 31).toNat = 2 ^ 5 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

section Guarded32

variable {w : Nat} [hw : WordLe32 w]

/-- A register shift left at width `w ≤ 32` masks its count to five bits; its 64-bit form
    shifts by the count conjoined with `31`. -/
instance shlRegSq :
    RelatedBinOpOn (lowW w) (fun _ y => HighZero w y)
      (fun x y => JasminBinOp.apply .shl x (y &&& BitVec.ofNat 64 31))
      (JasminBinOp.apply .shl) where
  comm x y hy := by
    have hle : w ≤ 64 := WordLe64.le
    simp only [JasminBinOp.apply, shiftMask_64, toNat_and_31, shiftMask_of_le32 hw.le, lowW,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show y.toNat < 2 ^ w from hy),
      Nat.mod_eq_of_lt (show y.toNat % 32 < 64 by omega)]
    exact BitVec.setWidth_shiftLeft_of_le hle

/-- A register shift right at width `w ≤ 32`, on operands with zero high bits. -/
instance shrRegSq :
    RelatedBinOpOn (lowW w) (fun x y => HighZero w x ∧ HighZero w y)
      (fun x y => JasminBinOp.apply .shr x (y &&& BitVec.ofNat 64 31))
      (JasminBinOp.apply .shr) where
  comm x y h := by
    simp only [JasminBinOp.apply, shiftMask_64, toNat_and_31, shiftMask_of_le32 hw.le,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show y.toNat < 2 ^ w from h.2),
      Nat.mod_eq_of_lt (show y.toNat % 32 < 64 by omega)]
    exact (shrImmSq (w := w) _).comm x h.1

/-- The high word of the product at width `w ≤ 32` is the 64-bit product shifted right by
    `w`, on operands with zero high bits. -/
instance mulhiSq :
    RelatedBinOpOn (lowW w) (fun x y => HighZero w x ∧ HighZero w y)
      (fun x y => (x * y) >>> w) mulHiW where
  comm x y h := by
    have hx : x.toNat < 2 ^ w := h.1
    have hy : y.toNat < 2 ^ w := h.2
    have hxy : x.toNat * y.toNat < 2 ^ 64 := by
      have h32 : 2 ^ w ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hw.le
      calc x.toNat * y.toNat < 2 ^ 32 * 2 ^ 32 :=
            Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)
        _ = 2 ^ 64 := by rw [← Nat.pow_add]
    apply BitVec.eq_of_toNat_eq
    simp only [lowW, mulHiW, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
      Nat.mod_eq_of_lt hxy]

/-- The carry bit of a carry-chain addition at width `w ≤ 32` is bit `w` of the 64-bit sum of
    the zero extensions. -/
theorem carryOutBit_wide (a b : BitVec w) (c : BitVec 1) :
    carryOutBit a b c =
      ((a.setWidth 64 + b.setWidth 64 + BitVec.ofNat 64 c.toNat) >>> w).setWidth 1 := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have h32 : 2 ^ w ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hw.le
  have h64 : 2 ^ 64 = 2 ^ 32 * 2 ^ 32 := by rw [← Nat.pow_add]
  have hs : a.toNat + b.toNat + c.toNat < 2 ^ 64 := by omega
  have hp : 0 < 2 ^ w := Nat.two_pow_pos w
  apply BitVec.eq_of_toNat_eq
  simp only [carryOutBit, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show a.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show a.toNat + b.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt hs]
  split
  · rename_i hge
    rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    rfl
  · rename_i hlt
    rw [Nat.div_eq_of_lt (by omega)]
    rfl

end Guarded32

section Compare

variable {w : Nat} [hw : WordLe64 w]

/-- A comparison of zero-extended words is the comparison of the words. -/
theorem holds_setWidth (c : JasminCmp) (a b : BitVec w) :
    c.holds (a.setWidth 64) (b.setWidth 64) = c.holds a b := by
  have h1 := two_pow_le_64 hw.le
  have ha : (a.setWidth 64).toNat = a.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := a.isLt; omega)]
  have hb : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  have heq : (a.setWidth 64 = b.setWidth 64) ↔ a = b := by
    rw [← BitVec.toNat_inj, ha, hb, BitVec.toNat_inj]
  cases c <;> simp [JasminCmp.holds, BitVec.ult, BitVec.ule, bne, ha, hb, heq]

/-- On operands with zero high bits the comparisons agree with the comparisons of the
    encodings. -/
instance cmpSq (c : JasminCmp) :
    RelatedRelOn (lowW w) (fun x y => HighZero w x ∧ HighZero w y)
      (fun x y => c.holds x y = true) (fun a b => c.holds a b = true) where
  iff x y h := by
    rw [eq_of_highZero hw.le h.1, eq_of_highZero hw.le h.2, holds_setWidth,
      lowW_setWidth hw.le, lowW_setWidth hw.le]

/-- The comparison bit of zero-extended words. -/
theorem cmpBit_setWidth (c : JasminCmp) (a b : BitVec w) :
    cmpBit c (a.setWidth 64) (b.setWidth 64) = cmpBit c a b := by
  simp only [cmpBit, holds_setWidth]

omit hw in
/-- **The constant.** The 64-bit constant `n % 2 ^ w` is the zero extension of the `w`-bit
    constant `n`. -/
theorem constSq (n : Nat) : BitVec.ofNat 64 (n % 2 ^ w) = (BitVec.ofNat w n).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]

end Compare

end CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords
