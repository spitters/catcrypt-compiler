/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.SingleWord

/-!
# Goldilocks single-word field blocks

The `SingleWordField` instance at the Goldilocks prime `P = 2⁶⁴ − 2³² + 1` (the
Plonky2/Plonky3 64-bit field) under the canonical encoding `x ↦ BitVec.ofNat 64 x.val`.
Since `2 P > 2⁶³`, the conditional subtract `csubW` and `SingleWordField.ofCanonical`
of `SingleWord` do not apply; every block here is built from `regArith` and `regConst`
bindings of `jasminDialect` alone, with the carry and borrow of a 64-bit addition
computed from bitwise operations.

With `ε = 2³² − 1 = 2⁶⁴ − P`:

* addition adds the words, adds `ε` on a carry out (which subtracts `P` modulo `2⁶⁴`),
  and canonicalises;
* subtraction subtracts the words and subtracts `ε` on a borrow (which adds `P`);
* negation is subtraction from `0`;
* multiplication forms the 128-bit product `hi · 2⁶⁴ + lo` from four 32 × 32-bit
  partial products, then applies the Plonky3 `reduce128`: with `hi = h₁ · 2³² + h₀`,
  `lo − h₁` with `P` added on a borrow, plus `h₀ · ε` with `P` subtracted on a carry,
  using `2⁶⁴ ≡ ε` and `2⁹⁶ ≡ −1 (mod P)`; a final canonicalisation lands in `[0, P)`.

## Main definitions

* `carryW a b s`: the carry-out bit `((a & b) | (¬s & (a | b))) >>> 63` of `s = a + b`.
* `selW c`: the mask select `(0 − c) & ε`.
* `canonW`, `addCW`, `addW`, `subW`, `negW`, `hiW`, `loW`, `reduceW`, `mulW`: the word
  functions.
* `carryBlk`, `selBlk`, `canonBlk`, `addCBlk`, `reduceBlk`, `glAddBlk`, `glSubBlk`,
  `glNegBlk`, `glMulBlk`: the `Com jasminDialect` blocks computing them.
* `goldilocks`: the `SingleWordField P` record.

## Main results

* `carryW_toNat`: `(carryW a b (a + b)).toNat = (a.toNat + b.toNat) / 2⁶⁴`.
* `canonW_toNat`: `(canonW t).toNat = t.toNat % P` for every word `t`.
* `prodW_toNat`: `hiW x y` and `loW x y` are the high and low words of `x · y`.
* `reduceW_toNat`: `(reduceW hi lo).toNat = (hi · 2⁶⁴ + lo) % P` for all words.
* `addW_realizes`, `subW_realizes`, `negW_realizes`, `mulW_realizes`: the word functions
  realise the field operations under the canonical encoding.
* `glAddBlk_denote`, `glSubBlk_denote`, `glNegBlk_denote`, `glMulBlk_denote`: the value
  theorems of the blocks.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Goldilocks

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (spliceCom spliceCom_denote)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord

/-- The Goldilocks prime `2⁶⁴ − 2³² + 1`. -/
abbrev P : Nat := 18446744069414584321

/-- `ε = 2³² − 1 = 2⁶⁴ − P`. -/
abbrev EPS : Nat := 4294967295

/-- `ε` as a word. -/
abbrev E : BitVec 64 := BitVec.ofNat 64 EPS

/-! ## 1. Carry and mask select -/

/-- The carry-out bit of `s = a + b`, computed as the top bit of
    `(a & b) | (¬s & (a | b))`. -/
def carryW (a b s : BitVec 64) : BitVec 64 :=
  ((a &&& b) ||| ((~~~s) &&& (a ||| b))) >>> (63 : Nat)

theorem ushiftRight63_toNat (x : BitVec 64) :
    (x >>> (63 : Nat)).toNat = (x.getLsbD 63).toNat := by
  have h := BitVec.msb_eq_decide x
  rw [BitVec.msb_eq_getLsbD_last] at h
  simp only [Nat.add_one_sub_one] at h
  rw [h, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  by_cases hx : 2 ^ 63 ≤ x.toNat
  · rw [decide_eq_true hx, Bool.toNat_true]; omega
  · rw [decide_eq_false hx, Bool.toNat_false]; omega

theorem carryW_toNat (a b : BitVec 64) :
    (carryW a b (a + b)).toNat = (a.toNat + b.toNat) / 2 ^ 64 := by
  have hc : (a.toNat + b.toNat) / 2 ^ 64 = (BitVec.carry 64 a b false).toNat := by
    rw [BitVec.carry_width]
    have := a.isLt; have := b.isLt
    by_cases h : a.toNat + b.toNat + false.toNat ≥ 2 ^ 64
    · rw [decide_eq_true h, Bool.toNat_true]; simp only [Bool.toNat_false] at h; omega
    · rw [decide_eq_false h, Bool.toNat_false]; simp only [Bool.toNat_false] at h; omega
  rw [hc, BitVec.carry_succ 63]
  unfold carryW
  rw [ushiftRight63_toNat]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_add (by omega : 63 < 64)]
  generalize a.getLsbD 63 = x
  generalize b.getLsbD 63 = y
  generalize BitVec.carry 63 a b false = z
  cases x <;> cases y <;> cases z <;> rfl

/-- `carryW (a − b) b a` is the borrow bit of `a − b`, since `(a − b) + b = a`. -/
theorem borrowW_toNat (a b : BitVec 64) :
    (carryW (a - b) b a).toNat = ((a - b).toNat + b.toNat) / 2 ^ 64 := by
  have h := carryW_toNat (a - b) b
  rwa [BitVec.sub_add_cancel] at h

theorem E_toNat : E.toNat = EPS := rfl

/-- The mask select `(0 − c) & ε`: `ε` when `c = 1`, `0` when `c = 0`. -/
def selW (c : BitVec 64) : BitVec 64 := (0 - c) &&& E

theorem selW_toNat (c : BitVec 64) (hc : c.toNat ≤ 1) : (selW c).toNat = c.toNat * EPS := by
  rcases (by omega : c.toNat = 0 ∨ c.toNat = 1) with h | h
  · rw [show c = 0#64 from BitVec.eq_of_toNat_eq (by simpa using h)]; rfl
  · rw [show c = 1#64 from BitVec.eq_of_toNat_eq (by simpa using h)]; rfl

theorem carryW_le (a b : BitVec 64) : (carryW a b (a + b)).toNat ≤ 1 := by
  rw [carryW_toNat]; have := a.isLt; have := b.isLt; omega

theorem borrowW_le (a b : BitVec 64) : (carryW (a - b) b a).toNat ≤ 1 := by
  rw [borrowW_toNat]; have := (a - b).isLt; have := b.isLt; omega

/-! ## 2. Canonicalisation, addition and subtraction -/

/-- Canonicalisation of a word: subtract `P` when the word is at least `P`, detected
    as the carry out of `t + ε`. -/
def canonW (t : BitVec 64) : BitVec 64 := t + selW (carryW t E (t + E))

theorem canonW_toNat (t : BitVec 64) : (canonW t).toNat = t.toNat % P := by
  unfold canonW
  rw [BitVec.toNat_add, selW_toNat _ (carryW_le _ _), carryW_toNat, E_toNat]
  have := t.isLt
  simp only [P, EPS, Nat.reducePow] at *
  rcases Nat.lt_or_ge t.toNat 18446744069414584321 with h | h
  · rw [Nat.div_eq_of_lt (by omega : t.toNat + 4294967295 < 18446744073709551616),
      Nat.mod_eq_of_lt h]
    omega
  · rw [show (t.toNat + 4294967295) / 18446744073709551616 = 1 by omega, Nat.mod_eq_sub_mod h,
      Nat.mod_eq_of_lt (by omega : t.toNat - 18446744069414584321 < 18446744069414584321)]
    omega

/-- Word addition with `ε` added on a carry out: `x + y` when the sum fits in 64 bits,
    otherwise `x + y − P`. -/
def addCW (x y : BitVec 64) : BitVec 64 := x + y + selW (carryW x y (x + y))

theorem addCW_toNat (x y : BitVec 64) (h : x.toNat + y.toNat < 2 ^ 64 + P) :
    (addCW x y).toNat = if x.toNat + y.toNat < 2 ^ 64 then x.toNat + y.toNat
      else x.toNat + y.toNat - P := by
  unfold addCW
  rw [BitVec.toNat_add, BitVec.toNat_add, selW_toNat _ (carryW_le _ _), carryW_toNat]
  simp only [P, EPS, Nat.reducePow] at *
  split_ifs with h'
  · rw [Nat.div_eq_of_lt h', Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt h',
      Nat.mod_eq_of_lt h']
  · rw [show (x.toNat + y.toNat) / 18446744073709551616 = 1 by omega, Nat.one_mul]
    omega

/-- Word subtraction with `ε` subtracted on a borrow: `x − y` when `y ≤ x`, otherwise
    `x + P − y`. -/
def subW (x y : BitVec 64) : BitVec 64 :=
  x - y - selW (carryW (x - y) y x)

theorem subW_val (x y : BitVec 64) (hy : y.toNat ≤ P) :
    (subW x y).toNat = if x.toNat < y.toNat then x.toNat + P - y.toNat
      else x.toNat - y.toNat := by
  unfold subW
  rw [BitVec.toNat_sub, selW_toNat _ (borrowW_le _ _), borrowW_toNat, BitVec.toNat_sub]
  have := x.isLt
  simp only [P, EPS, Nat.reducePow] at *
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega : 18446744073709551616 - y.toNat + x.toNat
        < 18446744073709551616),
      show (18446744073709551616 - y.toNat + x.toNat + y.toNat) / 18446744073709551616 = 1
        by omega, Nat.one_mul]
    omega
  · rw [show (18446744073709551616 - y.toNat + x.toNat) % 18446744073709551616
        = x.toNat - y.toNat by omega,
      show (x.toNat - y.toNat + y.toNat) / 18446744073709551616 = 0 by omega, Nat.zero_mul,
      Nat.sub_zero]
    omega

/-- Addition: `addCW`, then canonicalisation. -/
def addW (x y : BitVec 64) : BitVec 64 := canonW (addCW x y)

theorem addW_toNat (x y : BitVec 64) (hy : y.toNat < P) :
    (addW x y).toNat = (x.toNat + y.toNat) % P := by
  have hP : P < 2 ^ 64 := by norm_num
  unfold addW
  rw [canonW_toNat, addCW_toNat _ _ (by omega)]
  split_ifs with h
  · rfl
  · rw [Nat.mod_eq_sub_mod (by omega : P ≤ x.toNat + y.toNat)]

theorem subW_toNat (x y : BitVec 64) (hx : x.toNat < P) (hy : y.toNat < P) :
    (subW x y).toNat = (x.toNat + (P - y.toNat)) % P := by
  rw [subW_val _ _ hy.le]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show x.toNat + (P - y.toNat) = x.toNat - y.toNat + P by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

/-! ## 3. Multiplication -/

/-- The low 32-bit half `x & (2³² − 1)`. -/
def lo32 (x : BitVec 64) : BitVec 64 := x &&& E

/-- The high 32-bit half `x >>> 32`. -/
def hi32 (x : BitVec 64) : BitVec 64 := x >>> (32 : Nat)

/-- The middle partial-product sum `x₀ y₁ + x₁ y₀` (modulo `2⁶⁴`). -/
def midW (x y : BitVec 64) : BitVec 64 := lo32 x * hi32 y + hi32 x * lo32 y

/-- The low partial product `x₀ y₀`. -/
def llW (x y : BitVec 64) : BitVec 64 := lo32 x * lo32 y

/-- The low word of the 128-bit product `x · y`. -/
def loW (x y : BitVec 64) : BitVec 64 := llW x y + (midW x y <<< (32 : Nat))

/-- The high word of the 128-bit product `x · y`. -/
def hiW (x y : BitVec 64) : BitVec 64 :=
  hi32 x * hi32 y + (midW x y >>> (32 : Nat))
    + (carryW (lo32 x * hi32 y) (hi32 x * lo32 y) (midW x y) <<< (32 : Nat))
    + carryW (llW x y) (midW x y <<< (32 : Nat)) (loW x y)

theorem lo32_toNat (x : BitVec 64) : (lo32 x).toNat = x.toNat % 2 ^ 32 := by
  unfold lo32
  rw [BitVec.toNat_and, E_toNat, show EPS = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem hi32_toNat (x : BitVec 64) : (hi32 x).toNat = x.toNat / 2 ^ 32 := by
  unfold hi32
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem shl32_toNat (x : BitVec 64) :
    (x <<< (32 : Nat)).toNat = x.toNat * 2 ^ 32 % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem mul32_toNat (x y : BitVec 64) (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mul_lt_mul'' hx hy) (by norm_num))

/-- `hiW x y` and `loW x y` are the high and low words of the 128-bit product. -/
theorem prodW_toNat (x y : BitVec 64) :
    (hiW x y).toNat * 2 ^ 64 + (loW x y).toNat = x.toNat * y.toNat := by
  have hx0 : (lo32 x).toNat < 2 ^ 32 := by rw [lo32_toNat]; exact Nat.mod_lt _ (by norm_num)
  have hy0 : (lo32 y).toNat < 2 ^ 32 := by rw [lo32_toNat]; exact Nat.mod_lt _ (by norm_num)
  have hx1 : (hi32 x).toNat < 2 ^ 32 := by
    rw [hi32_toNat]; exact Nat.div_lt_of_lt_mul (by have := x.isLt; omega)
  have hy1 : (hi32 y).toNat < 2 ^ 32 := by
    rw [hi32_toNat]; exact Nat.div_lt_of_lt_mul (by have := y.isLt; omega)
  have hxy : x.toNat * y.toNat = (hi32 x).toNat * (hi32 y).toNat * 2 ^ 64
      + ((lo32 x).toNat * (hi32 y).toNat + (hi32 x).toNat * (lo32 y).toNat) * 2 ^ 32
      + (lo32 x).toNat * (lo32 y).toNat := by
    rw [lo32_toNat, lo32_toNat, hi32_toNat, hi32_toNat]
    conv_lhs => rw [← Nat.div_add_mod x.toNat (2 ^ 32), ← Nat.div_add_mod y.toNat (2 ^ 32)]
    ring
  have hlt : x.toNat * y.toNat < 2 ^ 128 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' x.isLt y.isLt) (by norm_num)
  have hb : ∀ a b : Nat, a < 2 ^ 32 → b < 2 ^ 32 → a * b ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    fun a b ha hb => Nat.mul_le_mul (by omega) (by omega)
  have bll := hb _ _ hx0 hy0
  have blh := hb _ _ hx0 hy1
  have bhl := hb _ _ hx1 hy0
  have bhh := hb _ _ hx1 hy1
  unfold hiW loW midW llW
  simp only [BitVec.toNat_add, carryW_toNat, shl32_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, mul32_toNat _ _ hx0 hy0, mul32_toNat _ _ hx0 hy1,
    mul32_toNat _ _ hx1 hy0, mul32_toNat _ _ hx1 hy1]
  generalize (lo32 x).toNat * (lo32 y).toNat = ll at *
  generalize (lo32 x).toNat * (hi32 y).toNat = lh at *
  generalize (hi32 x).toNat * (lo32 y).toNat = hl at *
  generalize (hi32 x).toNat * (hi32 y).toNat = hh at *
  generalize x.toNat * y.toNat = xy at *
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at *
  omega

/-- The Plonky3 `reduce128` of a 128-bit value `hi · 2⁶⁴ + lo`, followed by
    canonicalisation: with `hi = h₁ · 2³² + h₀`, it computes `lo − h₁` (adding `P` on a
    borrow), adds `h₀ · ε` (subtracting `P` on a carry), and canonicalises. -/
def reduceW (hi lo : BitVec 64) : BitVec 64 :=
  canonW (addCW (subW lo (hi32 hi)) (lo32 hi * E))

theorem modP_congr {v w : Nat} (k j : Nat) (h : w + j * P = v + k * P) : v % P = w % P := by
  have := congrArg (· % P) h
  simp only [Nat.add_mul_mod_self_right] at this
  exact this.symm

theorem reduceW_toNat (hi lo : BitVec 64) :
    (reduceW hi lo).toNat = (hi.toNat * 2 ^ 64 + lo.toNat) % P := by
  have hH1 : (hi32 hi).toNat < 2 ^ 32 := by
    rw [hi32_toNat]; exact Nat.div_lt_of_lt_mul (by have := hi.isLt; omega)
  have hH0 : hi.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have ht1 : (lo32 hi * E).toNat = hi.toNat % 2 ^ 32 * 4294967295 := by
    rw [BitVec.toNat_mul, lo32_toNat, E_toNat]
    exact Nat.mod_eq_of_lt (by simp only [EPS]; omega)
  have hu := (subW lo (hi32 hi)).isLt
  have hsum : (subW lo (hi32 hi)).toNat + (lo32 hi * E).toNat < 2 ^ 64 + P := by
    rw [ht1]; simp only [P]; omega
  unfold reduceW
  rw [canonW_toNat, addCW_toNat _ _ hsum, ht1, subW_val _ _ (by simp only [P]; omega),
    hi32_toNat]
  have hl := lo.isLt
  have hh := hi.isLt
  split_ifs <;>
  first
  | exact modP_congr (hi.toNat / 2 ^ 32 * (2 ^ 32 + 1) + hi.toNat % 2 ^ 32) 0
      (by simp only [P, Nat.reducePow] at *; omega)
  | exact modP_congr (hi.toNat / 2 ^ 32 * (2 ^ 32 + 1) + hi.toNat % 2 ^ 32) 1
      (by simp only [P, Nat.reducePow] at *; omega)
  | exact modP_congr (hi.toNat / 2 ^ 32 * (2 ^ 32 + 1) + hi.toNat % 2 ^ 32 + 1) 0
      (by simp only [P, Nat.reducePow] at *; omega)

/-- Multiplication: the 128-bit product from four 32 × 32-bit partial products, then
    `reduceW`. -/
def mulW (x y : BitVec 64) : BitVec 64 := reduceW (hiW x y) (loW x y)

theorem mulW_toNat (x y : BitVec 64) : (mulW x y).toNat = x.toNat * y.toNat % P := by
  unfold mulW
  rw [reduceW_toNat, prodW_toNat]

/-- Negation: `subW 0 x`. -/
def negW (x : BitVec 64) : BitVec 64 := subW 0 x

/-! ## 4. Field correctness under the canonical encoding -/

/-- The canonical encoding of Goldilocks elements. -/
abbrev glEnc : ZMod P → BitVec 64 := canonEnc P

theorem P_le : P ≤ 2 ^ 64 := by norm_num

theorem glEnc_toNat (x : ZMod P) : (glEnc x).toNat = x.val := canonEnc_toNat P_le x

theorem glEnc_lt (x : ZMod P) : (glEnc x).toNat < P := by
  rw [glEnc_toNat]; exact ZMod.val_lt x

theorem addW_realizes (x y : ZMod P) : addW (glEnc x) (glEnc y) = glEnc (x + y) := by
  apply eq_canonEnc_of_toNat P_le
  rw [addW_toNat _ _ (glEnc_lt y), glEnc_toNat, glEnc_toNat, ZMod.val_add]

theorem subW_realizes (x y : ZMod P) : subW (glEnc x) (glEnc y) = glEnc (x - y) := by
  apply eq_canonEnc_of_toNat P_le
  rw [subW_toNat _ _ (glEnc_lt x) (glEnc_lt y), glEnc_toNat, glEnc_toNat]
  have hy := ZMod.val_lt y
  have hcast : x - y = (((x.val + (P - y.val)) : Nat) : ZMod P) := by
    rw [Nat.cast_add, Nat.cast_sub hy.le, ZMod.natCast_self]
    simp only [ZMod.natCast_zmod_val]
    ring
  rw [hcast, ZMod.val_natCast]

theorem negW_realizes (x : ZMod P) : negW (glEnc x) = glEnc (-x) := by
  have h := subW_realizes 0 x
  rw [zero_sub] at h
  exact h

theorem mulW_realizes (x y : ZMod P) : mulW (glEnc x) (glEnc y) = glEnc (x * y) := by
  apply eq_canonEnc_of_toNat P_le
  rw [mulW_toNat, glEnc_toNat, glEnc_toNat, ZMod.val_mul]

/-! ## 5. Blocks -/

/-- The block computing `carryW a b s`. -/
def carryBlk {Γ : Ctxt jasminDialect} (a b s : Ctxt.Var Γ w64) : Com jasminDialect Γ w64 :=
  spliceCom (binBlk .and a b) <|
  spliceCom (binBlk .or a.there b.there) <|
  spliceCom (binBlk .andn s.there.there .here) <|
  spliceCom (binBlk .or (.there (.there .here)) .here) <|
  binLitBlk .shr .here 63

theorem carryBlk_denote {Γ : Ctxt jasminDialect} (a b s : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) :
    (carryBlk a b s).denote V = carryW (lk a V) (lk b V) (lk s V) := by
  unfold carryBlk
  simp only [spliceCom_denote, binBlk_denote, binLitBlk_denote]
  rfl

/-- The block computing `selW c`. -/
def selBlk {Γ : Ctxt jasminDialect} (c : Ctxt.Var Γ w64) : Com jasminDialect Γ w64 :=
  spliceCom (litBlk 0) <|
  spliceCom (binBlk .sub .here c.there) <|
  binLitBlk .and .here EPS

theorem selBlk_denote {Γ : Ctxt jasminDialect} (c : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (selBlk c).denote V = selW (lk c V) := by
  unfold selBlk
  simp only [spliceCom_denote, binBlk_denote, binLitBlk_denote, litBlk_denote]
  rfl

/-- The block computing `canonW t`. -/
def canonBlk {Γ : Ctxt jasminDialect} (t : Ctxt.Var Γ w64) : Com jasminDialect Γ w64 :=
  spliceCom (litBlk EPS) <|
  spliceCom (binBlk .add t.there .here) <|
  spliceCom (carryBlk t.there.there (.there .here) .here) <|
  spliceCom (selBlk .here) <|
  binBlk .add t.there.there.there.there .here

theorem canonBlk_denote {Γ : Ctxt jasminDialect} (t : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (canonBlk t).denote V = canonW (lk t V) := by
  unfold canonBlk
  simp only [spliceCom_denote, binBlk_denote, litBlk_denote, carryBlk_denote,
    selBlk_denote]
  rfl

/-- The block computing `addCW x y`. -/
def addCBlk {Γ : Ctxt jasminDialect} (x y : Ctxt.Var Γ w64) : Com jasminDialect Γ w64 :=
  spliceCom (binBlk .add x y) <|
  spliceCom (carryBlk x.there y.there .here) <|
  spliceCom (selBlk .here) <|
  binBlk .add (.there (.there .here)) .here

theorem addCBlk_denote {Γ : Ctxt jasminDialect} (x y : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (addCBlk x y).denote V = addCW (lk x V) (lk y V) := by
  unfold addCBlk
  simp only [spliceCom_denote, binBlk_denote, carryBlk_denote, selBlk_denote]
  rfl

/-- The subtraction block, computing `subW x y`. -/
def glSubBlk {Γ : Ctxt jasminDialect} (x y : Ctxt.Var Γ w64) : Com jasminDialect Γ w64 :=
  spliceCom (binBlk .sub x y) <|
  spliceCom (carryBlk .here y.there x.there) <|
  spliceCom (selBlk .here) <|
  binBlk .sub (.there (.there .here)) .here

theorem glSubBlk_value {Γ : Ctxt jasminDialect} (x y : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (glSubBlk x y).denote V = subW (lk x V) (lk y V) := by
  unfold glSubBlk
  simp only [spliceCom_denote, binBlk_denote, carryBlk_denote, selBlk_denote]
  rfl

/-- The addition block, computing `addW x y`. -/
def glAddBlk {Γ : Ctxt jasminDialect} (x y : Ctxt.Var Γ w64) : Com jasminDialect Γ w64 :=
  spliceCom (addCBlk x y) (canonBlk .here)

theorem glAddBlk_value {Γ : Ctxt jasminDialect} (x y : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (glAddBlk x y).denote V = addW (lk x V) (lk y V) := by
  unfold glAddBlk
  rw [spliceCom_denote, canonBlk_denote, addCBlk_denote]
  rfl

/-- The negation block, computing `negW x`. -/
def glNegBlk {Γ : Ctxt jasminDialect} (x : Ctxt.Var Γ w64) : Com jasminDialect Γ w64 :=
  spliceCom (litBlk 0) (glSubBlk .here x.there)

theorem glNegBlk_value {Γ : Ctxt jasminDialect} (x : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (glNegBlk x).denote V = negW (lk x V) := by
  unfold glNegBlk
  rw [spliceCom_denote, glSubBlk_value]
  rfl

/-- The block computing `reduceW hi lo`. -/
def reduceBlk {Γ : Ctxt jasminDialect} (hi lo : Ctxt.Var Γ w64) : Com jasminDialect Γ w64 :=
  spliceCom (binLitBlk .shr hi 32) <|
  spliceCom (glSubBlk lo.there .here) <|
  spliceCom (binLitBlk .and hi.there.there EPS) <|
  spliceCom (binLitBlk .mul .here EPS) <|
  spliceCom (addCBlk (.there (.there .here)) .here) <|
  canonBlk .here

theorem reduceBlk_denote {Γ : Ctxt jasminDialect} (hi lo : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (reduceBlk hi lo).denote V = reduceW (lk hi V) (lk lo V) := by
  unfold reduceBlk
  simp only [spliceCom_denote, binLitBlk_denote, glSubBlk_value, addCBlk_denote,
    canonBlk_denote]
  rfl

/-- The multiplication block, computing `mulW x y`: the four partial products, the
    128-bit product words `lo` and `hi`, then `reduceBlk`. -/
def glMulBlk {Γ : Ctxt jasminDialect} (x y : Ctxt.Var Γ w64) : Com jasminDialect Γ w64 :=
  spliceCom (binLitBlk .and x EPS) <|
  spliceCom (binLitBlk .shr x.there 32) <|
  spliceCom (binLitBlk .and y.there.there EPS) <|
  spliceCom (binLitBlk .shr y.there.there.there 32) <|
  -- context: y1 y0 x1 x0
  spliceCom (binBlk .mul Ctxt.Var.here.there.there.there Ctxt.Var.here.there) <|
  -- ll y1 y0 x1 x0
  spliceCom (binBlk .mul Ctxt.Var.here.there.there.there.there Ctxt.Var.here.there) <|
  -- lh ll y1 y0 x1 x0
  spliceCom (binBlk .mul Ctxt.Var.here.there.there.there.there
    Ctxt.Var.here.there.there.there) <|
  -- hl lh ll y1 y0 x1 x0
  spliceCom (binBlk .add Ctxt.Var.here.there .here) <|
  -- mid hl lh ll y1 y0 x1 x0
  spliceCom (binLitBlk .shl .here 32) <|
  -- ms mid hl lh ll y1 y0 x1 x0
  spliceCom (binBlk .add Ctxt.Var.here.there.there.there.there .here) <|
  -- lo ms mid hl lh ll y1 y0 x1 x0
  spliceCom (binBlk .mul Ctxt.Var.here.there.there.there.there.there.there.there.there
    Ctxt.Var.here.there.there.there.there.there.there) <|
  -- hh lo ms mid hl lh ll y1 y0 x1 x0
  spliceCom (binLitBlk .shr Ctxt.Var.here.there.there.there 32) <|
  -- mh hh lo ms mid hl lh ll
  spliceCom (binBlk .add Ctxt.Var.here.there .here) <|
  -- a1 mh hh lo ms mid hl lh ll
  spliceCom (carryBlk Ctxt.Var.here.there.there.there.there.there.there.there
    Ctxt.Var.here.there.there.there.there.there.there
    Ctxt.Var.here.there.there.there.there.there) <|
  -- c1 a1 mh hh lo ms mid hl lh ll
  spliceCom (binLitBlk .shl .here 32) <|
  -- c1s c1 a1 mh hh lo ms mid hl lh ll
  spliceCom (binBlk .add Ctxt.Var.here.there.there .here) <|
  -- a2 c1s c1 a1 mh hh lo ms mid hl lh ll
  spliceCom (carryBlk
    Ctxt.Var.here.there.there.there.there.there.there.there.there.there.there.there
    Ctxt.Var.here.there.there.there.there.there.there.there
    Ctxt.Var.here.there.there.there.there.there.there) <|
  -- c2 a2 c1s c1 a1 mh hh lo
  spliceCom (binBlk .add Ctxt.Var.here.there .here) <|
  -- hi c2 a2 c1s c1 a1 mh hh lo
  reduceBlk .here Ctxt.Var.here.there.there.there.there.there.there.there.there

theorem glMulBlk_value {Γ : Ctxt jasminDialect} (x y : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) : (glMulBlk x y).denote V = mulW (lk x V) (lk y V) := by
  unfold glMulBlk
  simp only [spliceCom_denote, binBlk_denote, binLitBlk_denote, carryBlk_denote,
    reduceBlk_denote]
  rfl

/-! ## 6. The record -/

theorem glAddBlk_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) (x y : ZMod P) (ha : a.lookup V = glEnc x)
    (hb : b.lookup V = glEnc y) : (glAddBlk a b).denote V = glEnc (x + y) := by
  rw [glAddBlk_value, show lk a V = glEnc x from ha, show lk b V = glEnc y from hb]
  exact addW_realizes x y

theorem glSubBlk_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) (x y : ZMod P) (ha : a.lookup V = glEnc x)
    (hb : b.lookup V = glEnc y) : (glSubBlk a b).denote V = glEnc (x - y) := by
  rw [glSubBlk_value, show lk a V = glEnc x from ha, show lk b V = glEnc y from hb]
  exact subW_realizes x y

theorem glMulBlk_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) (x y : ZMod P) (ha : a.lookup V = glEnc x)
    (hb : b.lookup V = glEnc y) : (glMulBlk a b).denote V = glEnc (x * y) := by
  rw [glMulBlk_value, show lk a V = glEnc x from ha, show lk b V = glEnc y from hb]
  exact mulW_realizes x y

theorem glNegBlk_denote {Γ : Ctxt jasminDialect} (a : Ctxt.Var Γ w64)
    (V : Ctxt.Valuation Γ) (x : ZMod P) (ha : a.lookup V = glEnc x) :
    (glNegBlk a).denote V = glEnc (-x) := by
  rw [glNegBlk_value, show lk a V = glEnc x from ha]
  exact negW_realizes x

/-- The Goldilocks `SingleWordField` on canonical representatives. -/
def goldilocks : SingleWordField P where
  enc := glEnc
  enc_injective := canonEnc_injective P_le
  addBlk := glAddBlk
  subBlk := glSubBlk
  mulBlk := glMulBlk
  negBlk := glNegBlk
  constBlk := FieldWord.constBlk P
  copyBlk := FieldWord.copyBlk
  addBlk_denote := glAddBlk_denote
  subBlk_denote := glSubBlk_denote
  mulBlk_denote := glMulBlk_denote
  negBlk_denote := glNegBlk_denote
  constBlk_denote V x := FieldWord.constBlk_denote x V
  copyBlk_denote a V x ha := FieldWord.copyBlk_denote glEnc a V x ha

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Goldilocks
