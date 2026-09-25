/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.SingleWord

/-!
# Mersenne-31 single-word field blocks

The `SingleWordField` instance at the Mersenne prime `P = 2³¹ − 1` under the
canonical encoding. Since `2³¹ ≡ 1 (mod P)`, the multiplication block computes the
62-bit product, applies the fold by `C = 1` twice and ends with one conditional
subtract. From `x < 2⁶²` the two folds give the bounds `2³²` and
`2³¹ + 2 < 2 P`.

## Main definitions

* `m31Enc`: the canonical encoding `ZMod P → BitVec 64`.
* `reduceW`, `mulW`: the reduction and multiplication word functions.
* `mulBlk`: the multiplication block.
* `mersenne31`: the `SingleWordField P` record.

## Main results

* `reduceW_toNat`: `(reduceW x).toNat = x.toNat % P` for `x < 2⁶²`.
* `mulW_realizes`: `mulW (m31Enc x) (m31Enc y) = m31Enc (x * y)`.
* `mulBlk_denote`: the multiplication block denotes `m31Enc (x * y)` on variables
  holding `m31Enc x` and `m31Enc y`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mersenne31

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- The Mersenne prime `2³¹ − 1`. -/
abbrev P : Nat := 2147483647

/-- The fold multiplier `2³¹ mod P = 1`. -/
abbrev C : Nat := 1

theorem two_P_le : 2 * P ≤ 2 ^ 63 := by norm_num

theorem C_lt : C < 2 ^ 31 := by norm_num

theorem two_pow_sub_C : 2 ^ 31 - C = P := by norm_num

/-- The canonical encoding of Mersenne-31 elements. -/
abbrev m31Enc : ZMod P → BitVec 64 := canonEnc P

/-! ## 1. Word functions -/

/-- The reduction: two folds by `C`, then one conditional subtract. -/
def reduceW (x : BitVec 64) : BitVec 64 :=
  csubW P (foldW C (foldW C x))

/-- The multiplication word function: the wrapping product, then `reduceW`. -/
def mulW (a b : BitVec 64) : BitVec 64 := reduceW (a * b)

theorem foldW_mod_P (y : BitVec 64) (hy : y.toNat < 2 ^ 62) :
    (foldW C y).toNat % P = y.toNat % P := by
  have h := foldW_mod C C_lt y hy
  rwa [two_pow_sub_C] at h

/-- The two-fold, one-csub reduction is reduction modulo `P` below `2⁶²`. -/
theorem reduceW_toNat (x : BitVec 64) (hx : x.toNat < 2 ^ 62) :
    (reduceW x).toNat = x.toNat % P := by
  have h1 : (foldW C x).toNat < 4294967296 :=
    lt_of_lt_of_le (foldW_bound C C_lt x (2 ^ 62) le_rfl hx) (by norm_num)
  have h2 : (foldW C (foldW C x)).toNat < 2147483650 :=
    lt_of_lt_of_le (foldW_bound C C_lt _ 4294967296 (by norm_num) h1) (by norm_num)
  unfold reduceW
  rw [csubW_toNat P two_P_le _ (lt_of_lt_of_le h2 (by norm_num)),
    foldW_mod_P _ (lt_trans h1 (by norm_num)), foldW_mod_P _ hx]

theorem mulW_realizes (x y : ZMod P) : mulW (m31Enc x) (m31Enc y) = m31Enc (x * y) := by
  have hx : x.val < 2147483647 := ZMod.val_lt x
  have hy : y.val < 2147483647 := ZMod.val_lt y
  have hlt : x.val * y.val < 2 ^ 62 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' hx hy) (by norm_num)
  have hprod : (m31Enc x * m31Enc y).toNat = x.val * y.val := by
    rw [BitVec.toNat_mul, canonEnc_toNat (by norm_num), canonEnc_toNat (by norm_num)]
    exact Nat.mod_eq_of_lt (lt_trans hlt (by norm_num))
  apply eq_canonEnc_of_toNat (by norm_num)
  show (reduceW (m31Enc x * m31Enc y)).toNat = _
  rw [reduceW_toNat _ (by rw [hprod]; exact hlt), hprod, ZMod.val_mul]

/-! ## 2. The multiplication block -/

/-- The Mersenne-31 multiplication block: multiply, two folds by `C`, one
    conditional subtract of `P`. -/
def mulBlk {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64) : Com jasminDialect Γ w64 :=
  foldMulBlk C 2 P a b

theorem mulBlk_value {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (mulBlk a b).denote V = mulW (lk a V) (lk b V) := by
  unfold mulBlk
  rw [foldMulBlk_denote]
  rfl

theorem mulBlk_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) (x y : ZMod P) (ha : a.lookup V = m31Enc x)
    (hb : b.lookup V = m31Enc y) : (mulBlk a b).denote V = m31Enc (x * y) := by
  rw [mulBlk_value, show lk a V = m31Enc x from ha, show lk b V = m31Enc y from hb]
  exact mulW_realizes x y

/-! ## 3. The record -/

/-- The Mersenne-31 `SingleWordField` on canonical representatives. -/
def mersenne31 : SingleWordField P :=
  SingleWordField.ofCanonical P two_P_le mulBlk mulBlk_denote

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mersenne31
