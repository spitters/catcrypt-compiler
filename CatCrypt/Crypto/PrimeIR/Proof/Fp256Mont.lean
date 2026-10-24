/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.PrimeIR.Extraction.Fp256Mont_haxpipe
public import CatCrypt.Crypto.Util.P256Verified
public import CatCrypt.Hax.FoldRange
public import CatCrypt.Crypto.Bridges.Transfer.HaxIntTransfer
public import CatCrypt.Crypto.PrimeIR.Proof.FieldModel

/-!
# The Montgomery P-256 field of `primeir-hax`

Specifications of the limb functions of `fp256_mont.rs` as the extraction
`Primeir` carries them. A field element is four little-endian 64-bit limbs of
`value · R mod p` in `[0, p)`, with `R = 2^256` and `p` the P-256 prime. Each
loop of the extraction is unrolled into its four iterations and each word of a
carry chain is described by its low word, its carry and the identity between
them, so every statement holds for all inputs in range.

## Main definitions

* `W64`, `val4` — a 64-bit word, and the integer of four limbs.
* `Canon` — four in-range limbs whose integer is below `p`.
* `montVal` — the field element of canonical limbs: their integer times `R⁻¹`.
* `redc1`, `mmOuter` — one reduction round and one outer iteration of
  `mont_mul_limbs`.

## Main results

* `add_limbs_spec`, `sub_limbs_spec`, `select_limbs_mask`, `reduce_once_spec` —
  the limb helpers.
* `add_mod_spec`, `sub_mod_spec` — modular sum and difference of canonical limbs.
* `redc1_spec`, `mmOuter_spec` — one reduction round adds `u0 · p` and divides by
  `2^64`; one outer iteration keeps the running value below `2p`.
* `mont_mul_limbs_spec` — the Montgomery multiplication returns canonical limbs
  `r` with `r · 2^256 = a · b + M · p`.
* `rnd_spec`, `mont_reduce_spec` — the in-place reduction of eight words below
  `p · 2^256`.
* `mont_sqr_limbs_spec` — the squaring (triangle, doubling, diagonal, reduction)
  returns canonical limbs `r` with `r · 2^256 = a · a + M · p`.
* `mont_mul_limbs_val`, `mont_sqr_limbs_val`, `add_mod_val`, `sub_mod_val`,
  `neg_val`, `ct_select_val`, `montVal_R`, `montVal_zero` — the operations on
  `montVal`.
* `sqr_n_val`, `pow_c1_limbs_val`, `Field_inv_val` — repeated squaring, the
  addition chain `x ^ ((p - 3) / 4)` and the Fermat inverse `Field::inv`.
* `CtField_ct_eq_eq`, `CtField_is_zero_eq`, `to_canonical_limbs_val` — `ct_eq` as a
  fold over the limbs, `is_zero`, and the map out of the Montgomery domain.
* `fp256MontCtModel` — the `CtFieldModel` of the `Field` and `CtField` instances of
  `Fp256Mont`, valued in `Fp256` on canonical limbs.
* `fp256MontModel` — the `BoundedFieldModel` of `Fp256` on canonical limbs.

`Field_inv`, `CtField_ct_eq` and `CtField_is_zero` are the extracted methods of
the `Field` and `CtField` implementations of `Fp256Mont`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PrimeIR.Fp256Mont

open Primeir

/-! ## Counting loops -/

/-- A `Hax.whileFold` whose state `mk s j` carries a counter `j` tested against
    `n`, steps `s` with `g` and increments the counter, is the `Hax.foldRange` of
    `g`. -/
theorem whileFold_count_gen {S σ : Type} (mk : σ → Int → S) (n : Int)
    (g : Int → σ → σ) (f : S → ControlFlow S S)
    (hf : ∀ s j, f (mk s j) =
      if Hax.lt j n then Hax.cfContinue (mk (g j s) (Hax.add j (1 : Int)))
      else Hax.cfBreak (mk s j)) :
    ∀ (m : Nat) (i : Int) (s : σ), i + m = n →
      Hax.whileFold (mk s i) (fun _ => true) f
        = ControlFlow.Break (mk (Hax.foldRange i n s g) n) := by
  intro m i s hm
  refine Hax.whileFold_eq_of_fuel (n := m + 1) ?_
  induction m generalizing i s with
  | zero =>
    have hin : i = n := by simpa using hm
    subst hin
    simp [Hax.whileFoldFuel, hf, Hax.lt, Hax.cfBreak, Hax.foldRange_stop]
  | succ m ih =>
    have hlt : i < n := by push_cast at hm; omega
    have hstep := ih (i + 1) (g i s) (by push_cast at hm ⊢; omega)
    rw [Hax.whileFoldFuel]
    simp only [hf, Hax.lt, hlt, decide_true, ite_true, Hax.cfContinue, Hax.add]
    rw [hstep, Hax.foldRange_step _ _ _ _ hlt]

/-- A four-step range unrolls. -/
theorem foldRange_four {α : Type} (init : α) (f : Int → α → α) :
    Hax.foldRange 0 4 init f = f 3 (f 2 (f 1 (f 0 init))) := by
  rw [Hax.foldRange_step _ _ _ _ (by norm_num), Hax.foldRange_step _ _ _ _ (by norm_num),
    Hax.foldRange_step _ _ _ _ (by norm_num), Hax.foldRange_step _ _ _ _ (by norm_num),
    Hax.foldRange_stop _ _ _ _ (by norm_num)]
  norm_num

/-! ## Width operations on in-range values -/

/-- A width cast of a nonnegative value is reduction modulo `2^w`. -/
theorem castVal_mod {w : Nat} {x : Int} (h0 : 0 ≤ x) : Hax.castVal_w w x = x % 2 ^ w :=
  Hax.castVal_w_eq_emod h0

/-- A width cast of an in-range value is the value. -/
theorem castVal_of_lt {w : Nat} {x : Int} (h0 : 0 ≤ x) (h : x < 2 ^ w) :
    Hax.castVal_w w x = x :=
  Hax.castVal_w_of_lt h0 h

/-- A right shift of an in-range value is division by a power of two. -/
theorem shr_of_lt {w : Nat} {x : Int} (b : Nat) (h0 : 0 ≤ x) (h : x < 2 ^ w) :
    Hax.shr_w w x (b : Int) = x / 2 ^ b :=
  Hax.shr_w_natCast_of_lt b h0 h

/-- A left shift of a nonnegative value multiplies by a power of two and truncates to
    the width. -/
theorem shl_of_nonneg {w : Nat} {x : Int} (b : Nat) (h0 : 0 ≤ x) :
    Hax.shl_w w x (b : Int) = x * 2 ^ b % 2 ^ w := by
  simp only [Hax.shl_w, Hax.mod2w, Int.toNat_natCast, Nat.shiftLeft_eq]
  rw [Int.natCast_mod]
  push_cast [Int.toNat_of_nonneg h0]
  rfl

/-! ## One word of a carry chain -/

/-- One word of an addition chain: the low word and the carry of `x + y + c`. -/
theorem adc_spec {x y c : Int} (hx0 : 0 ≤ x) (hx : x < 2 ^ 64) (hy0 : 0 ≤ y)
    (hy : y < 2 ^ 64) (hc0 : 0 ≤ c) (hc : c ≤ 1) :
    ∃ lo hi : Int,
      Hax.castVal_w 64 (Hax.add (Hax.add (Hax.castVal_w 128 x) (Hax.castVal_w 128 y)) c) = lo ∧
      Hax.shr_w 128 (Hax.add (Hax.add (Hax.castVal_w 128 x) (Hax.castVal_w 128 y)) c) 64 = hi ∧
      0 ≤ lo ∧ lo < 2 ^ 64 ∧ 0 ≤ hi ∧ hi ≤ 1 ∧ lo + 2 ^ 64 * hi = x + y + c := by
  rw [castVal_of_lt hx0 (by omega), castVal_of_lt hy0 (by omega)]
  simp only [Hax.add]
  refine ⟨_, _, rfl, rfl, ?_⟩
  rw [castVal_mod (by omega), show ((64 : Int)) = ((64 : Nat) : Int) from rfl,
    shr_of_lt 64 (by omega) (by omega)]
  omega

/-- One word of a multiply-accumulate chain: the low word and the carry of
    `x + y * z + c`. -/
theorem mac_spec {x y z c : Int} (hx0 : 0 ≤ x) (hx : x < 2 ^ 64) (hy0 : 0 ≤ y)
    (hy : y < 2 ^ 64) (hz0 : 0 ≤ z) (hz : z < 2 ^ 64) (hc0 : 0 ≤ c) (hc : c < 2 ^ 64) :
    ∃ lo hi : Int,
      Hax.castVal_w 64 (Hax.add (Hax.add (Hax.castVal_w 128 x)
        (Hax.mul (Hax.castVal_w 128 y) (Hax.castVal_w 128 z))) c) = lo ∧
      Hax.shr_w 128 (Hax.add (Hax.add (Hax.castVal_w 128 x)
        (Hax.mul (Hax.castVal_w 128 y) (Hax.castVal_w 128 z))) c) 64 = hi ∧
      0 ≤ lo ∧ lo < 2 ^ 64 ∧ 0 ≤ hi ∧ hi < 2 ^ 64 ∧ lo + 2 ^ 64 * hi = x + y * z + c := by
  rw [castVal_of_lt hx0 (by omega), castVal_of_lt hy0 (by omega),
    castVal_of_lt hz0 (by omega)]
  simp only [Hax.add, Hax.mul]
  refine ⟨_, _, rfl, rfl, ?_⟩
  have hyz0 : 0 ≤ y * z := mul_nonneg hy0 hz0
  have hyz : y * z ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    mul_le_mul (by omega) (by omega) hz0 (by omega)
  rw [castVal_mod (by omega), show ((64 : Int)) = ((64 : Nat) : Int) from rfl,
    shr_of_lt 64 (by omega) (by omega)]
  omega

/-- The low word of `x + y + c` as the extraction computes it. -/
def adcLo (x y c : Int) : Int :=
  Hax.castVal_w 64 (Hax.add (Hax.add (Hax.castVal_w 128 x) (Hax.castVal_w 128 y)) c)

/-- The carry of `x + y + c` as the extraction computes it. -/
def adcHi (x y c : Int) : Int :=
  Hax.shr_w 128 (Hax.add (Hax.add (Hax.castVal_w 128 x) (Hax.castVal_w 128 y)) c) 64

theorem adc_facts {x y c : Int} (hx0 : 0 ≤ x) (hx : x < 2 ^ 64) (hy0 : 0 ≤ y)
    (hy : y < 2 ^ 64) (hc0 : 0 ≤ c) (hc : c ≤ 1) :
    0 ≤ adcLo x y c ∧ adcLo x y c < 2 ^ 64 ∧ 0 ≤ adcHi x y c ∧ adcHi x y c ≤ 1 ∧
      adcLo x y c + 2 ^ 64 * adcHi x y c = x + y + c := by
  obtain ⟨lo, hi, e1, e2, h⟩ := adc_spec hx0 hx hy0 hy hc0 hc
  simp only [adcLo, adcHi, e1, e2]; exact h

/-- Masking with `1` is parity. -/
theorem bitand_one {w : Nat} {v : Int} (h0 : 0 ≤ v) (h : v < 2 ^ w) (hw : 1 ≤ w) :
    Hax.bitand_w w v 1 = v % 2 := by
  have hm : v.toNat % 2 ^ w = v.toNat := by
    apply Nat.mod_eq_of_lt
    have hc : (v.toNat : Int) < ((2 ^ w : Nat) : Int) := by
      rw [Int.toNat_of_nonneg h0]; push_cast; exact h
    exact_mod_cast hc
  have h1 : (1 : Int).toNat % 2 ^ w = 1 := by
    simp only [Int.toNat_one]
    exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  simp only [Hax.bitand_w, hm, h1, Nat.and_one_is_mod]
  omega

/-- The low word of `x - y - b` as the extraction computes it. -/
def sbbLo (x y b : Int) : Int :=
  Hax.castVal_w 64 (Hax.wrapping_sub_w 128 (Hax.wrapping_sub_w 128 (Hax.castVal_w 128 x)
    (Hax.castVal_w 128 y)) (Hax.castVal_w 128 b))

/-- The borrow of `x - y - b` as the extraction computes it. -/
def sbbHi (x y b : Int) : Int :=
  Hax.castVal_w 64 (Hax.bitand_w 128 (Hax.shr_w 128 (Hax.wrapping_sub_w 128
    (Hax.wrapping_sub_w 128 (Hax.castVal_w 128 x) (Hax.castVal_w 128 y))
    (Hax.castVal_w 128 b)) 64) 1)

theorem sbb_facts {x y b : Int} (hx0 : 0 ≤ x) (hx : x < 2 ^ 64) (hy0 : 0 ≤ y)
    (hy : y < 2 ^ 64) (hb0 : 0 ≤ b) (hb : b ≤ 1) :
    0 ≤ sbbLo x y b ∧ sbbLo x y b < 2 ^ 64 ∧ 0 ≤ sbbHi x y b ∧ sbbHi x y b ≤ 1 ∧
      sbbLo x y b - 2 ^ 64 * sbbHi x y b = x - y - b := by
  have hws : ∀ u v : Int, Hax.wrapping_sub_w 128 u v = Hax.castVal_w 128 (u - v + 2 ^ 128) :=
    fun _ _ => rfl
  have hd : Hax.wrapping_sub_w 128 (Hax.wrapping_sub_w 128 (Hax.castVal_w 128 x)
      (Hax.castVal_w 128 y)) (Hax.castVal_w 128 b) = (x - y - b) % 2 ^ 128 := by
    rw [castVal_of_lt hx0 (by omega), castVal_of_lt hy0 (by omega),
      castVal_of_lt hb0 (by omega), hws x y, castVal_mod (by omega), hws,
      castVal_mod (by omega)]
    omega
  have hd0 : 0 ≤ (x - y - b) % 2 ^ 128 := by omega
  have hd1 : (x - y - b) % 2 ^ 128 < 2 ^ 128 := by omega
  simp only [sbbLo, sbbHi, hd]
  rw [show ((64 : Int)) = ((64 : Nat) : Int) from rfl, shr_of_lt 64 hd0 hd1,
    bitand_one (by omega) (by omega) (by norm_num), castVal_mod hd0, castVal_mod (by omega)]
  omega

/-! ## Limb vectors -/

/-- `x` is a 64-bit word. -/
def W64 (x : Int) : Prop := 0 ≤ x ∧ x < 2 ^ 64

/-- The integer of four little-endian 64-bit limbs. -/
def val4 (x0 x1 x2 x3 : Int) : Int := x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3

/-! ## Masks on words -/

theorem toNat_mod64 {x : Int} (hx : W64 x) : x.toNat % 2 ^ 64 = x.toNat := by
  apply Nat.mod_eq_of_lt
  have hc : (x.toNat : Int) < ((2 ^ 64 : Nat) : Int) := by
    rw [Int.toNat_of_nonneg hx.1]; push_cast; exact hx.2
  exact_mod_cast hc

theorem ones_toNat : ((2 : Int) ^ 64 - 1).toNat % 2 ^ 64 = 2 ^ 64 - 1 := by
  rw [show ((2 : Int) ^ 64 - 1) = ((2 ^ 64 - 1 : Nat) : Int) by norm_num, Int.toNat_natCast]
  norm_num

theorem bitand_ones {x : Int} (hx : W64 x) : Hax.bitand_w 64 x (2 ^ 64 - 1) = x := by
  simp only [Hax.bitand_w, toNat_mod64 hx, ones_toNat, Nat.and_two_pow_sub_one_eq_mod]
  rw [Int.toNat_of_nonneg hx.1]

theorem bitand_zero (x : Int) : Hax.bitand_w 64 x 0 = 0 := by
  simp [Hax.bitand_w]

theorem bitor_zero {x : Int} (hx : W64 x) : Hax.bitor_w 64 x 0 = x := by
  simp [Hax.bitor_w, Int.toNat_of_nonneg hx.1]
  exact Int.emod_eq_of_lt hx.1 hx.2

theorem zero_bitor {x : Int} (hx : W64 x) : Hax.bitor_w 64 0 x = x := by
  simp [Hax.bitor_w, Int.toNat_of_nonneg hx.1]
  exact Int.emod_eq_of_lt hx.1 hx.2

theorem bitnot_zero : Hax.bitnot_w 64 0 = 2 ^ 64 - 1 := by
  simp [Hax.bitnot_w]

theorem bitnot_ones : Hax.bitnot_w 64 (2 ^ 64 - 1) = 0 := by
  simp only [Hax.bitnot_w, ones_toNat]; norm_num

/-- The word select of the extraction under the all-zeros or all-ones mask. -/
theorem selW_zero {x y : Int} (hy : W64 y) :
    Hax.bitor_w 64 (Hax.bitand_w 64 x 0) (Hax.bitand_w 64 y (Hax.bitnot_w 64 0)) = y := by
  rw [bitand_zero, bitnot_zero, bitand_ones hy, zero_bitor hy]

theorem selW_ones {x y : Int} (hx : W64 x) :
    Hax.bitor_w 64 (Hax.bitand_w 64 x (2 ^ 64 - 1))
      (Hax.bitand_w 64 y (Hax.bitnot_w 64 (2 ^ 64 - 1))) = x := by
  rw [bitnot_ones, bitand_zero, bitand_ones hx, bitor_zero hx]

/-- The P-256 prime as an integer literal. -/
def pZ : Int := 115792089210356248762697446949407573530086143415290314195533631308867097853951

theorem two_mul_or_one (n : Nat) : 2 * n ||| 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_or]
  rcases i with _ | i <;> simp [Nat.testBit_succ, Nat.mul_add_div]

/-- One word of the doubling loop of `mont_sqr_limbs`: the word shifted left by one
    with the incoming bit, and the outgoing top bit. -/
theorem dbl_facts {x b : Int} (hx : W64 x) (hb : b = 0 ∨ b = 1) :
    W64 (Hax.bitor_w 64 (Hax.shl_w 64 x 1) b) ∧ (Hax.shr_w 64 x 63 = 0 ∨ Hax.shr_w 64 x 63 = 1) ∧
      Hax.bitor_w 64 (Hax.shl_w 64 x 1) b + 2 ^ 64 * Hax.shr_w 64 x 63 = 2 * x + b := by
  have hs : Hax.shl_w 64 x 1 = x * 2 % 2 ^ 64 := shl_of_nonneg 1 hx.1
  have hr : Hax.shr_w 64 x 63 = x / 2 ^ 63 := shr_of_lt 63 hx.1 hx.2
  have hm0 : 0 ≤ x * 2 % 2 ^ 64 := Int.emod_nonneg _ (by norm_num)
  have hm1 : x * 2 % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by norm_num)
  have hor : Hax.bitor_w 64 (x * 2 % 2 ^ 64) b = x * 2 % 2 ^ 64 + b := by
    rcases hb with rfl | rfl
    · rw [bitor_zero ⟨hm0, hm1⟩, add_zero]
    · have hev : x * 2 % 2 ^ 64 = 2 * (x % 2 ^ 63) := by unfold W64 at hx; omega
      have hlt : 2 * (x % 2 ^ 63) + 1 < 2 ^ 64 := by omega
      obtain ⟨n, hn⟩ : ∃ n : Nat, x % 2 ^ 63 = n := ⟨(x % 2 ^ 63).toNat, by omega⟩
      rw [hn] at hlt
      simp only [Hax.bitor_w, hev, hn]
      have h1 : (2 * (n : Int)).toNat = 2 * n := by omega
      have h2 : 2 * n < 2 ^ 64 := by omega
      rw [h1, Nat.mod_eq_of_lt h2, Int.toNat_one, Nat.one_mod_two_pow (by norm_num),
        two_mul_or_one]
      push_cast; ring
  rw [hs, hr, hor]
  unfold W64 at *
  refine ⟨⟨by omega, by rcases hb with rfl | rfl <;> omega⟩, by omega, by omega⟩

/-! ## Word shifts at fixed amounts -/

/-! ## Word shifts at fixed amounts -/

theorem shr64_32 {m : Int} (hm : W64 m) : Hax.shr_w 64 m 32 = m / 2 ^ 32 :=
  shr_of_lt 32 hm.1 hm.2

theorem shl64_32 {m : Int} (hm : W64 m) : Hax.shl_w 64 m 32 = m * 2 ^ 32 % 2 ^ 64 :=
  shl_of_nonneg 32 hm.1

theorem shr128_64 {s : Int} (h0 : 0 ≤ s) (h : s < 2 ^ 128) :
    Hax.shr_w 128 s 64 = s / 2 ^ 64 :=
  shr_of_lt 64 h0 h

theorem cast128 {x : Int} (h0 : 0 ≤ x) (h : x < 2 ^ 128) : Hax.castVal_w 128 x = x :=
  castVal_of_lt h0 h

theorem cast64 {x : Int} (h0 : 0 ≤ x) : Hax.castVal_w 64 x = x % 2 ^ 64 :=
  castVal_mod h0

theorem split64 (S : Int) : S % 2 ^ 64 + 2 ^ 64 * (S / 2 ^ 64) = S := by
  omega

theorem div64_bound {S k : Int} (h0 : 0 ≤ S) (h : S < 2 ^ 64 * k) :
    0 ≤ S / 2 ^ 64 ∧ S / 2 ^ 64 < k := by
  omega

variable [PrimeirDeps]

theorem N0INV_eq : N0INV = 1 := rfl

theorem POLY3_eq : POLY3 = 18446744069414584321 := rfl

/-- One reduction round of `mont_mul_limbs` on the six accumulator words
    `u0, …, u5`: the words after adding `u0 · p` and dropping the low word. -/
def redc1 (u0 u1 u2 u3 u4 u5 : Int) : Array Int :=
  let m := Hax.wrapping_mul_w 64 u0 N0INV
  let mp := Hax.mul (Hax.castVal_w 128 m) (Hax.castVal_w 128 POLY3)
  let s1 := Hax.add (Hax.castVal_w 128 u1) (Hax.castVal_w 128 (Hax.shl_w 64 m (32 : Int)))
  let s2 := Hax.add (Hax.add (Hax.castVal_w 128 u2) (Hax.castVal_w 128 (Hax.shr_w 64 m (32 : Int)))) (Hax.shr_w 128 s1 (64 : Int))
  let s3 := Hax.add (Hax.add (Hax.castVal_w 128 u3) (Hax.castVal_w 128 (Hax.castVal_w 64 mp))) (Hax.shr_w 128 s2 (64 : Int))
  let s4 := Hax.add (Hax.add (Hax.castVal_w 128 u4) (Hax.shr_w 128 mp (64 : Int))) (Hax.shr_w 128 s3 (64 : Int))
  let s5 := Hax.add (Hax.castVal_w 128 u5) (Hax.shr_w 128 s4 (64 : Int))
  #[Hax.castVal_w 64 s1, Hax.castVal_w 64 s2, Hax.castVal_w 64 s3, Hax.castVal_w 64 s4,
    Hax.castVal_w 64 s5, 0]

set_option exponentiation.threshold 512 in
/-- A reduction round adds `u0 · p` to the six-word accumulator and divides by
    `2^64`; below `2p · 2^64` the result has five words. -/
theorem redc1_spec {u0 u1 u2 u3 u4 u5 : Int} (h0 : W64 u0) (h1 : W64 u1) (h2 : W64 u2)
    (h3 : W64 u3) (h4 : W64 u4) (h5 : W64 u5)
    (hU : val4 u0 u1 u2 u3 + 2 ^ 256 * u4 + 2 ^ 320 * u5 + u0 * pZ < 2 * pZ * 2 ^ 64) :
    ∃ v0 v1 v2 v3 v4 : Int, redc1 u0 u1 u2 u3 u4 u5 = #[v0, v1, v2, v3, v4, 0] ∧
      W64 v0 ∧ W64 v1 ∧ W64 v2 ∧ W64 v3 ∧ W64 v4 ∧
      (val4 v0 v1 v2 v3 + 2 ^ 256 * v4) * 2 ^ 64
        = val4 u0 u1 u2 u3 + 2 ^ 256 * u4 + 2 ^ 320 * u5 + u0 * pZ := by
  unfold W64 at *
  have hm : Hax.wrapping_mul_w 64 u0 N0INV = u0 := by
    rw [N0INV_eq]; simp only [Hax.wrapping_mul_w, mul_one]
    exact castVal_of_lt h0.1 h0.2
  unfold redc1
  simp only [hm, POLY3_eq, cast128 h1.1 (by omega), cast128 h2.1 (by omega),
    cast128 h3.1 (by omega), cast128 h4.1 (by omega), cast128 h5.1 (by omega),
    cast128 h0.1 (by omega), cast128 (show (0 : Int) ≤ 18446744069414584321 by norm_num)
      (by norm_num), shl64_32 h0, shr64_32 h0, Hax.add, Hax.mul]
  rw [cast128 (x := u0 * 2 ^ 32 % 2 ^ 64) (by omega) (by omega),
    cast128 (x := u0 / 2 ^ 32) (by omega) (by omega),
    cast64 (x := u0 * 18446744069414584321) (by omega),
    cast128 (x := u0 * 18446744069414584321 % 2 ^ 64) (by omega) (by omega),
    shr128_64 (s := u0 * 18446744069414584321) (by omega) (by omega)]
  have et : u0 * 2 ^ 32 % 2 ^ 64 + 2 ^ 64 * (u0 / 2 ^ 32) = u0 * 2 ^ 32 := by omega
  have emp := split64 (u0 * 18446744069414584321)
  have bmp0 : 0 ≤ u0 * 18446744069414584321 % 2 ^ 64 := Int.emod_nonneg _ (by norm_num)
  have bmp1 : 0 ≤ u0 * 18446744069414584321 / 2 ^ 64 := by omega
  have bmp2 : u0 * 18446744069414584321 / 2 ^ 64 < 2 ^ 64 := by omega
  have bmp3 : u0 * 18446744069414584321 % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by norm_num)
  have bt0 : 0 ≤ u0 * 2 ^ 32 % 2 ^ 64 := Int.emod_nonneg _ (by norm_num)
  have bt1 : u0 * 2 ^ 32 % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by norm_num)
  have bq0 : 0 ≤ u0 / 2 ^ 32 := by omega
  have bq1 : u0 / 2 ^ 32 < 2 ^ 32 := by omega
  clear hm
  generalize hS1 : u1 + u0 * 2 ^ 32 % 2 ^ 64 = S1
  have b1 : 0 ≤ S1 ∧ S1 < 2 ^ 65 := by constructor <;> linarith [h1.1, h1.2]
  rw [shr128_64 (s := S1) b1.1 (by linarith [b1.2])]
  have c1 : 0 ≤ S1 / 2 ^ 64 ∧ S1 / 2 ^ 64 < 2 := div64_bound b1.1 (by linarith [b1.2])
  have e1 := split64 S1
  generalize hS2 : u2 + u0 / 2 ^ 32 + S1 / 2 ^ 64 = S2
  have b2 : 0 ≤ S2 ∧ S2 < 2 ^ 65 := by constructor <;> linarith [h2.1, h2.2]
  rw [shr128_64 (s := S2) b2.1 (by linarith [b2.2])]
  have c2 : 0 ≤ S2 / 2 ^ 64 ∧ S2 / 2 ^ 64 < 2 := div64_bound b2.1 (by linarith [b2.2])
  have e2 := split64 S2
  generalize hS3 : u3 + u0 * 18446744069414584321 % 2 ^ 64 + S2 / 2 ^ 64 = S3
  have b3 : 0 ≤ S3 ∧ S3 < 2 ^ 66 := by constructor <;> linarith [h3.1, h3.2]
  rw [shr128_64 (s := S3) b3.1 (by linarith [b3.2])]
  have c3 : 0 ≤ S3 / 2 ^ 64 ∧ S3 / 2 ^ 64 < 4 := div64_bound b3.1 (by linarith [b3.2])
  have e3 := split64 S3
  generalize hS4 : u4 + u0 * 18446744069414584321 / 2 ^ 64 + S3 / 2 ^ 64 = S4
  have b4 : 0 ≤ S4 ∧ S4 < 2 ^ 66 := by constructor <;> linarith [h4.1, h4.2]
  rw [shr128_64 (s := S4) b4.1 (by linarith [b4.2])]
  have c4 : 0 ≤ S4 / 2 ^ 64 ∧ S4 / 2 ^ 64 < 4 := div64_bound b4.1 (by linarith [b4.2])
  have e4 := split64 S4
  generalize hS5 : u5 + S4 / 2 ^ 64 = S5
  have b5 : 0 ≤ S5 := by linarith [h5.1]
  have m1 : 0 ≤ S1 % 2 ^ 64 ∧ S1 % 2 ^ 64 < 2 ^ 64 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have m2 : 0 ≤ S2 % 2 ^ 64 ∧ S2 % 2 ^ 64 < 2 ^ 64 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have m3 : 0 ≤ S3 % 2 ^ 64 ∧ S3 % 2 ^ 64 < 2 ^ 64 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have m4 : 0 ≤ S4 % 2 ^ 64 ∧ S4 % 2 ^ 64 < 2 ^ 64 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have hkey : (S1 % 2 ^ 64 + 2 ^ 64 * (S2 % 2 ^ 64) + 2 ^ 128 * (S3 % 2 ^ 64)
      + 2 ^ 192 * (S4 % 2 ^ 64) + 2 ^ 256 * S5) * 2 ^ 64
      = val4 u0 u1 u2 u3 + 2 ^ 256 * u4 + 2 ^ 320 * u5 + u0 * pZ := by
    unfold val4 pZ
    linear_combination (2 ^ 64 : Int) * e1 + (2 ^ 128 : Int) * e2 + (2 ^ 192 : Int) * e3
      + (2 ^ 256 : Int) * e4 - (2 ^ 64 : Int) * hS1 - (2 ^ 128 : Int) * hS2
      - (2 ^ 192 : Int) * hS3 - (2 ^ 256 : Int) * hS4 - (2 ^ 320 : Int) * hS5
      + (2 ^ 64 : Int) * et + (2 ^ 192 : Int) * emp
  have hS5b : S5 < 2 ^ 64 := by
    unfold pZ at hU hkey
    linarith [m1.1, m2.1, m3.1, m4.1]
  rw [cast64 b1.1, cast64 b2.1, cast64 b3.1, cast64 b4.1, castVal_of_lt (w := 64) b5 hS5b]
  refine ⟨_, _, _, _, _, rfl, m1, m2, m3, m4, ⟨b5, hS5b⟩, ?_⟩
  rw [← hkey]; unfold val4; ring

/-- The low word of `x + y * z + c` as the extraction computes it. -/
def macLo (x y z c : Int) : Int :=
  Hax.castVal_w 64 (Hax.add (Hax.add (Hax.castVal_w 128 x)
    (Hax.mul (Hax.castVal_w 128 y) (Hax.castVal_w 128 z))) c)

/-- The carry of `x + y * z + c` as the extraction computes it. -/
def macHi (x y z c : Int) : Int :=
  Hax.shr_w 128 (Hax.add (Hax.add (Hax.castVal_w 128 x)
    (Hax.mul (Hax.castVal_w 128 y) (Hax.castVal_w 128 z))) c) 64

omit [PrimeirDeps] in
theorem mac_facts {x y z c : Int} (hx : W64 x) (hy : W64 y) (hz : W64 z) (hc : W64 c) :
    W64 (macLo x y z c) ∧ W64 (macHi x y z c) ∧
      macLo x y z c + 2 ^ 64 * macHi x y z c = x + y * z + c := by
  obtain ⟨lo, hi, e1, e2, h⟩ := mac_spec hx.1 hx.2 hy.1 hy.2 hz.1 hz.2 hc.1 hc.2
  simp only [macLo, macHi, e1, e2, W64]
  exact ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩

/-- The body of the outer loop of `mont_mul_limbs` at index `i`: the row
    `acc += a · b[i]` followed by one reduction round. -/
def mmOuter (a b : Array Int) (i : Int) (acc : Array Int) : Array Int :=
  let bi := Hax.castVal_w 128 (Hax.index b i)
  let carry := (0 : Int)
  let j := (0 : Int)
  let _wf := Hax.whileFold (acc, carry, j) (fun _ => true) fun (acc, carry, j) =>
    if Hax.lt j (4 : Int) then
      let s := Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index acc j)) (Hax.mul (Hax.castVal_w 128 (Hax.index a j)) bi)) carry
      let acc := (Hax.array_update acc j (Hax.castVal_w 64 s) : Array (Int))
      let carry := Hax.shr_w 128 s (64 : Int)
      let j := Hax.add j (1 : Int)
      Hax.cfContinue (acc, carry, j)
    else
      Hax.cfBreak (acc, carry, j)
  let (acc, carry, _j) := _wf.merge
  let s := Hax.add (Hax.castVal_w 128 (Hax.index acc (4 : Int))) carry
  let acc := (Hax.array_update acc (4 : Int) (Hax.castVal_w 64 s) : Array (Int))
  let acc := (Hax.array_update acc (5 : Int) (Hax.castVal_w 64 (Hax.shr_w 128 s (64 : Int))) : Array (Int))
  let m := Hax.wrapping_mul_w 64 (Hax.index acc (0 : Int)) N0INV
  let mp := Hax.mul (Hax.castVal_w 128 m) (Hax.castVal_w 128 POLY3)
  let s1 := Hax.add (Hax.castVal_w 128 (Hax.index acc (1 : Int))) (Hax.castVal_w 128 (Hax.shl_w 64 m (32 : Int)))
  let s2 := Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index acc (2 : Int))) (Hax.castVal_w 128 (Hax.shr_w 64 m (32 : Int)))) (Hax.shr_w 128 s1 (64 : Int))
  let s3 := Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index acc (3 : Int))) (Hax.castVal_w 128 (Hax.castVal_w 64 mp))) (Hax.shr_w 128 s2 (64 : Int))
  let s4 := Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index acc (4 : Int))) (Hax.shr_w 128 mp (64 : Int))) (Hax.shr_w 128 s3 (64 : Int))
  let s5 := Hax.add (Hax.castVal_w 128 (Hax.index acc (5 : Int))) (Hax.shr_w 128 s4 (64 : Int))
  let acc := (Hax.array_update acc (0 : Int) (Hax.castVal_w 64 s1) : Array (Int))
  let acc := (Hax.array_update acc (1 : Int) (Hax.castVal_w 64 s2) : Array (Int))
  let acc := (Hax.array_update acc (2 : Int) (Hax.castVal_w 64 s3) : Array (Int))
  let acc := (Hax.array_update acc (3 : Int) (Hax.castVal_w 64 s4) : Array (Int))
  let acc := (Hax.array_update acc (4 : Int) (Hax.castVal_w 64 s5) : Array (Int))
  let acc := (Hax.array_update acc (5 : Int) (0 : Int) : Array (Int))
  acc

/-- `mont_mul_limbs` is `reduce_once` of four iterations of `mmOuter` from the
    zero accumulator. -/
theorem mont_mul_limbs_eq (a b : Array Int) :
    mont_mul_limbs a b =
      let acc := Hax.foldRange 0 4 (Hax.repeat_ (0 : Int) (6 : Int)) (mmOuter a b)
      reduce_once #[Hax.index acc 0, Hax.index acc 1, Hax.index acc 2, Hax.index acc 3]
        (Hax.index acc 4) := by
  unfold mont_mul_limbs
  dsimp only
  rw [whileFold_count_gen (fun (s : Array Int) (j : Int) => (s, j)) 4 (mmOuter a b)
    _ (fun s j => rfl) 4 0 (Hax.repeat_ (0 : Int) (6 : Int)) (by norm_num)]
  rfl

/-- One step of the multiply-accumulate row of `mont_mul_limbs`: word `j` of the
    accumulator plus `a[j] · z` plus the carry. -/
def mmRow (a : Array Int) (z : Int) (j : Int) (s : Array Int × Int) : Array Int × Int :=
  (Hax.array_update s.1 j (macLo (Hax.index s.1 j) (Hax.index a j) z s.2),
    macHi (Hax.index s.1 j) (Hax.index a j) z s.2)

/-- The part of the outer loop body of `mont_mul_limbs` after the row: the top
    words and one reduction round. -/
def mmPost (acc : Array Int) (carry : Int) : Array Int :=
  let s := Hax.add (Hax.castVal_w 128 (Hax.index acc (4 : Int))) carry
  let acc := (Hax.array_update acc (4 : Int) (Hax.castVal_w 64 s) : Array (Int))
  let acc := (Hax.array_update acc (5 : Int) (Hax.castVal_w 64 (Hax.shr_w 128 s (64 : Int))) : Array (Int))
  let m := Hax.wrapping_mul_w 64 (Hax.index acc (0 : Int)) N0INV
  let mp := Hax.mul (Hax.castVal_w 128 m) (Hax.castVal_w 128 POLY3)
  let s1 := Hax.add (Hax.castVal_w 128 (Hax.index acc (1 : Int))) (Hax.castVal_w 128 (Hax.shl_w 64 m (32 : Int)))
  let s2 := Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index acc (2 : Int))) (Hax.castVal_w 128 (Hax.shr_w 64 m (32 : Int)))) (Hax.shr_w 128 s1 (64 : Int))
  let s3 := Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index acc (3 : Int))) (Hax.castVal_w 128 (Hax.castVal_w 64 mp))) (Hax.shr_w 128 s2 (64 : Int))
  let s4 := Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index acc (4 : Int))) (Hax.shr_w 128 mp (64 : Int))) (Hax.shr_w 128 s3 (64 : Int))
  let s5 := Hax.add (Hax.castVal_w 128 (Hax.index acc (5 : Int))) (Hax.shr_w 128 s4 (64 : Int))
  let acc := (Hax.array_update acc (0 : Int) (Hax.castVal_w 64 s1) : Array (Int))
  let acc := (Hax.array_update acc (1 : Int) (Hax.castVal_w 64 s2) : Array (Int))
  let acc := (Hax.array_update acc (2 : Int) (Hax.castVal_w 64 s3) : Array (Int))
  let acc := (Hax.array_update acc (3 : Int) (Hax.castVal_w 64 s4) : Array (Int))
  let acc := (Hax.array_update acc (4 : Int) (Hax.castVal_w 64 s5) : Array (Int))
  let acc := (Hax.array_update acc (5 : Int) (0 : Int) : Array (Int))
  acc

theorem mmOuter_split (a b : Array Int) (i : Int) (acc : Array Int) :
    mmOuter a b i acc =
      mmPost (Hax.foldRange 0 4 (acc, 0) (mmRow a (Hax.index b i))).1
        (Hax.foldRange 0 4 (acc, 0) (mmRow a (Hax.index b i))).2 := by
  unfold mmOuter
  dsimp only
  rw [whileFold_count_gen (fun (s : Array Int × Int) (j : Int) => (s.1, s.2, j)) 4
    (mmRow a (Hax.index b i)) _ (fun s j => rfl) 4 0 (acc, 0) (by norm_num)]
  rfl

section Lit6

omit [PrimeirDeps]

variable (a b c d e f v : Int)

theorem idx6_0 : Hax.index #[a, b, c, d, e, f] 0 = a := rfl
theorem idx6_1 : Hax.index #[a, b, c, d, e, f] 1 = b := rfl
theorem idx6_2 : Hax.index #[a, b, c, d, e, f] 2 = c := rfl
theorem idx6_3 : Hax.index #[a, b, c, d, e, f] 3 = d := rfl
theorem idx6_4 : Hax.index #[a, b, c, d, e, f] 4 = e := rfl
theorem idx6_5 : Hax.index #[a, b, c, d, e, f] 5 = f := rfl
theorem upd6_0 : Hax.array_update #[a, b, c, d, e, f] 0 v = #[v, b, c, d, e, f] := rfl
theorem upd6_1 : Hax.array_update #[a, b, c, d, e, f] 1 v = #[a, v, c, d, e, f] := rfl
theorem upd6_2 : Hax.array_update #[a, b, c, d, e, f] 2 v = #[a, b, v, d, e, f] := rfl
theorem upd6_3 : Hax.array_update #[a, b, c, d, e, f] 3 v = #[a, b, c, v, e, f] := rfl
theorem upd6_4 : Hax.array_update #[a, b, c, d, e, f] 4 v = #[a, b, c, d, v, f] := rfl
theorem upd6_5 : Hax.array_update #[a, b, c, d, e, f] 5 v = #[a, b, c, d, e, v] := rfl

end Lit6

theorem mmPost_eq (y0 y1 y2 y3 x4 x5 c : Int) :
    mmPost #[y0, y1, y2, y3, x4, x5] c =
      redc1 y0 y1 y2 y3 (Hax.castVal_w 64 (Hax.add (Hax.castVal_w 128 x4) c))
        (Hax.castVal_w 64 (Hax.shr_w 128 (Hax.add (Hax.castVal_w 128 x4) c) 64)) := by
  unfold mmPost redc1
  simp only [idx6_0, idx6_1, idx6_2, idx6_3, idx6_4, idx6_5, upd6_0, upd6_1, upd6_2, upd6_3,
    upd6_4, upd6_5]

omit [PrimeirDeps] in
theorem mmRow_0 (a : Array Int) (z x0 x1 x2 x3 x4 x5 c : Int) :
    mmRow a z 0 (#[x0, x1, x2, x3, x4, x5], c) =
      (#[macLo x0 (Hax.index a 0) z c, x1, x2, x3, x4, x5], macHi x0 (Hax.index a 0) z c) := by
  simp [mmRow, Hax.array_update, Hax.index]

omit [PrimeirDeps] in
theorem mmRow_1 (a : Array Int) (z x0 x1 x2 x3 x4 x5 c : Int) :
    mmRow a z 1 (#[x0, x1, x2, x3, x4, x5], c) =
      (#[x0, macLo x1 (Hax.index a 1) z c, x2, x3, x4, x5], macHi x1 (Hax.index a 1) z c) := by
  simp [mmRow, Hax.array_update, Hax.index]

omit [PrimeirDeps] in
theorem mmRow_2 (a : Array Int) (z x0 x1 x2 x3 x4 x5 c : Int) :
    mmRow a z 2 (#[x0, x1, x2, x3, x4, x5], c) =
      (#[x0, x1, macLo x2 (Hax.index a 2) z c, x3, x4, x5], macHi x2 (Hax.index a 2) z c) := by
  simp [mmRow, Hax.array_update, Hax.index]

omit [PrimeirDeps] in
theorem mmRow_3 (a : Array Int) (z x0 x1 x2 x3 x4 x5 c : Int) :
    mmRow a z 3 (#[x0, x1, x2, x3, x4, x5], c) =
      (#[x0, x1, x2, macLo x3 (Hax.index a 3) z c, x4, x5], macHi x3 (Hax.index a 3) z c) := by
  simp [mmRow, Hax.array_update, Hax.index]

/-- `mmOuter` on a literal accumulator: the multiply-accumulate row, then
    `redc1`. -/
theorem mmOuter_eq (a : Array Int) (x0 x1 x2 x3 x4 x5 : Int) (b : Array Int) (i : Int) :
    mmOuter a b i #[x0, x1, x2, x3, x4, x5] =
      let z := Hax.index b i
      let c0 := macHi x0 (Hax.index a 0) z 0
      let c1 := macHi x1 (Hax.index a 1) z c0
      let c2 := macHi x2 (Hax.index a 2) z c1
      let c3 := macHi x3 (Hax.index a 3) z c2
      let s := Hax.add (Hax.castVal_w 128 x4) c3
      redc1 (macLo x0 (Hax.index a 0) z 0) (macLo x1 (Hax.index a 1) z c0)
        (macLo x2 (Hax.index a 2) z c1) (macLo x3 (Hax.index a 3) z c2)
        (Hax.castVal_w 64 s) (Hax.castVal_w 64 (Hax.shr_w 128 s 64)) := by
  rw [mmOuter_split, foldRange_four, mmRow_0, mmRow_1, mmRow_2, mmRow_3]
  exact mmPost_eq _ _ _ _ _ _ _

section Lit4

omit [PrimeirDeps]

variable (a b c d : Int)

theorem idx4_0 : Hax.index #[a, b, c, d] 0 = a := rfl
theorem idx4_1 : Hax.index #[a, b, c, d] 1 = b := rfl
theorem idx4_2 : Hax.index #[a, b, c, d] 2 = c := rfl
theorem idx4_3 : Hax.index #[a, b, c, d] 3 = d := rfl

end Lit4

set_option exponentiation.threshold 512 in
/-- One outer iteration of `mont_mul_limbs`: with `a` canonical and the running
    value `V` below `2p`, the next value `V'` is below `2p` and
    `V' · 2^64 = V + a · b[i] + m · p` for some `m`. -/
theorem mmOuter_spec {a0 a1 a2 a3 x0 x1 x2 x3 x4 : Int} {b : Array Int} {i : Int}
    (ha0 : W64 a0) (ha1 : W64 a1) (ha2 : W64 a2) (ha3 : W64 a3) (hA : val4 a0 a1 a2 a3 < pZ)
    (hz : W64 (Hax.index b i)) (hx0 : W64 x0) (hx1 : W64 x1) (hx2 : W64 x2) (hx3 : W64 x3)
    (hx4 : W64 x4) (hV : val4 x0 x1 x2 x3 + 2 ^ 256 * x4 < 2 * pZ) :
    ∃ y0 y1 y2 y3 y4 m : Int,
      mmOuter #[a0, a1, a2, a3] b i #[x0, x1, x2, x3, x4, 0] = #[y0, y1, y2, y3, y4, 0] ∧
      W64 y0 ∧ W64 y1 ∧ W64 y2 ∧ W64 y3 ∧ W64 y4 ∧
      val4 y0 y1 y2 y3 + 2 ^ 256 * y4 < 2 * pZ ∧
      (val4 y0 y1 y2 y3 + 2 ^ 256 * y4) * 2 ^ 64
        = val4 x0 x1 x2 x3 + 2 ^ 256 * x4 + val4 a0 a1 a2 a3 * Hax.index b i + m * pZ := by
  rw [mmOuter_eq]
  simp only [idx4_0, idx4_1, idx4_2, idx4_3]
  generalize Hax.index b i = z at hz ⊢
  have hzero : W64 0 := by norm_num [W64]
  obtain ⟨l0, k0, e0⟩ := mac_facts hx0 ha0 hz hzero
  obtain ⟨l1, k1, e1⟩ := mac_facts hx1 ha1 hz k0
  obtain ⟨l2, k2, e2⟩ := mac_facts hx2 ha2 hz k1
  obtain ⟨l3, k3, e3⟩ := mac_facts hx3 ha3 hz k2
  generalize macLo x3 a3 z (macHi x2 a2 z (macHi x1 a1 z (macHi x0 a0 z 0))) = y3 at *
  generalize macHi x3 a3 z (macHi x2 a2 z (macHi x1 a1 z (macHi x0 a0 z 0))) = c3 at *
  generalize macLo x2 a2 z (macHi x1 a1 z (macHi x0 a0 z 0)) = y2 at *
  generalize macHi x2 a2 z (macHi x1 a1 z (macHi x0 a0 z 0)) = c2 at *
  generalize macLo x1 a1 z (macHi x0 a0 z 0) = y1 at *
  generalize macHi x1 a1 z (macHi x0 a0 z 0) = c1 at *
  generalize macLo x0 a0 z 0 = y0 at *
  generalize macHi x0 a0 z 0 = c0 at *
  unfold W64 at *
  have hs : Hax.add (Hax.castVal_w 128 x4) c3 = x4 + c3 := by
    rw [cast128 hx4.1 (by linarith [hx4.2])]; rfl
  have hsd := div64_bound (S := x4 + c3) (k := 2) (by linarith [hx4.1, k3.1])
    (by linarith [hx4.2, k3.2])
  rw [hs, cast64 (by linarith [hx4.1, k3.1]),
    shr128_64 (by linarith [hx4.1, k3.1]) (by linarith [hx4.2, k3.2]),
    castVal_of_lt (w := 64) hsd.1 (by linarith [hsd.2])]
  have hsm : 0 ≤ (x4 + c3) % 2 ^ 64 ∧ (x4 + c3) % 2 ^ 64 < 2 ^ 64 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have hss := split64 (x4 + c3)
  have hAz : val4 a0 a1 a2 a3 * z ≤ (pZ - 1) * (2 ^ 64 - 1) :=
    mul_le_mul (by linarith) (by linarith [hz.2]) hz.1 (by unfold pZ; norm_num)
  have hAz0 : 0 ≤ val4 a0 a1 a2 a3 * z :=
    mul_nonneg (by unfold val4 at *; linarith [ha0.1, ha1.1, ha2.1, ha3.1]) hz.1
  have hU : val4 y0 y1 y2 y3 + 2 ^ 256 * ((x4 + c3) % 2 ^ 64) + 2 ^ 320 * ((x4 + c3) / 2 ^ 64)
      = val4 x0 x1 x2 x3 + 2 ^ 256 * x4 + val4 a0 a1 a2 a3 * z := by
    unfold val4
    linear_combination e0 + (2 ^ 64 : Int) * e1 + (2 ^ 128 : Int) * e2 + (2 ^ 192 : Int) * e3
      + (2 ^ 256 : Int) * hss
  have hy0p : y0 * pZ ≤ (2 ^ 64 - 1) * pZ :=
    mul_le_mul_of_nonneg_right (by linarith [l0.2]) (by unfold pZ; norm_num)
  have hbound : val4 x0 x1 x2 x3 + 2 ^ 256 * x4 + val4 a0 a1 a2 a3 * z + y0 * pZ
      < 2 * pZ * 2 ^ 64 := by
    linarith only [hV, hAz, hy0p]
  obtain ⟨v0, v1, v2, v3, v4, he, hv0, hv1, hv2, hv3, hv4, hv⟩ :=
    redc1_spec l0 l1 l2 l3 hsm ⟨hsd.1, by linarith [hsd.2]⟩ (by rw [hU]; exact hbound)
  refine ⟨v0, v1, v2, v3, v4, y0, he, hv0, hv1, hv2, hv3, hv4, ?_, ?_⟩
  · have : (val4 v0 v1 v2 v3 + 2 ^ 256 * v4) * 2 ^ 64 < 2 * pZ * 2 ^ 64 := by
      rw [hv, hU]; exact hbound
    linarith only [this]
  · rw [hv, hU]

omit [PrimeirDeps] in
theorem bit_of_lt_two {w : Int} (h0 : 0 ≤ w) (h : w < 2) : w = 0 ∨ w = 1 := by omega

omit [PrimeirDeps] in
theorem val4_nonneg {x0 x1 x2 x3 : Int} (h0 : W64 x0) (h1 : W64 x1) (h2 : W64 x2)
    (h3 : W64 x3) : 0 ≤ val4 x0 x1 x2 x3 := by
  unfold val4; unfold W64 at *; linarith [h0.1, h1.1, h2.1, h3.1]

omit [PrimeirDeps] in
theorem val4_lt {x0 x1 x2 x3 : Int} (h0 : W64 x0) (h1 : W64 x1) (h2 : W64 x2)
    (h3 : W64 x3) : val4 x0 x1 x2 x3 < 2 ^ 256 := by
  unfold val4; unfold W64 at *; linarith [h0.2, h1.2, h2.2, h3.2]

omit [PrimeirDeps] in
theorem splitP (X : Int) : X % pZ + pZ * (X / pZ) = X := by
  unfold pZ; omega

theorem mask_of_zero : mask_of 0 = 0 := by
  simp [mask_of, Hax.wrapping_sub_w, Hax.mod2w]

theorem mask_of_one : mask_of 1 = 2 ^ 64 - 1 := by
  simp [mask_of, Hax.wrapping_sub_w, Hax.mod2w]

theorem add_limbs_eq (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    add_limbs #[a0, a1, a2, a3] #[b0, b1, b2, b3] =
      (#[adcLo a0 b0 0, adcLo a1 b1 (adcHi a0 b0 0),
        adcLo a2 b2 (adcHi a1 b1 (adcHi a0 b0 0)),
        adcLo a3 b3 (adcHi a2 b2 (adcHi a1 b1 (adcHi a0 b0 0)))],
       Hax.castVal_w 64 (adcHi a3 b3 (adcHi a2 b2 (adcHi a1 b1 (adcHi a0 b0 0))))) := by
  unfold add_limbs
  dsimp only
  rw [whileFold_count_gen (fun (s : Array Int × Int) (j : Int) => (s.1, s.2, j)) 4
    (fun i s => (Hax.array_update s.1 i (adcLo (Hax.index #[a0, a1, a2, a3] i)
      (Hax.index #[b0, b1, b2, b3] i) s.2),
      adcHi (Hax.index #[a0, a1, a2, a3] i) (Hax.index #[b0, b1, b2, b3] i) s.2))
    _ (fun s j => rfl) 4 0 ((Hax.repeat_ (0 : Int) (4 : Int)), 0) (by norm_num)]
  simp [foldRange_four, ControlFlow.merge, Hax.array_update, Hax.index, Hax.repeat_]

/-- `add_limbs` on in-range limbs: four in-range words and a carry bit whose
    value is the sum of the two 256-bit integers. -/
theorem add_limbs_spec {a0 a1 a2 a3 b0 b1 b2 b3 : Int} (ha0 : W64 a0) (ha1 : W64 a1)
    (ha2 : W64 a2) (ha3 : W64 a3) (hb0 : W64 b0) (hb1 : W64 b1) (hb2 : W64 b2)
    (hb3 : W64 b3) :
    ∃ r0 r1 r2 r3 c : Int,
      add_limbs #[a0, a1, a2, a3] #[b0, b1, b2, b3] = (#[r0, r1, r2, r3], c) ∧
      W64 r0 ∧ W64 r1 ∧ W64 r2 ∧ W64 r3 ∧ 0 ≤ c ∧ c ≤ 1 ∧
      val4 r0 r1 r2 r3 + 2 ^ 256 * c = val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3 := by
  rw [add_limbs_eq]
  unfold W64 at *
  have f0 := adc_facts ha0.1 ha0.2 hb0.1 hb0.2 le_rfl zero_le_one
  have f1 := adc_facts ha1.1 ha1.2 hb1.1 hb1.2 f0.2.2.1 f0.2.2.2.1
  have f2 := adc_facts ha2.1 ha2.2 hb2.1 hb2.2 f1.2.2.1 f1.2.2.2.1
  have f3 := adc_facts ha3.1 ha3.2 hb3.1 hb3.2 f2.2.2.1 f2.2.2.2.1
  rw [castVal_of_lt f3.2.2.1 (by omega)]
  refine ⟨_, _, _, _, _, rfl, ⟨f0.1, f0.2.1⟩, ⟨f1.1, f1.2.1⟩, ⟨f2.1, f2.2.1⟩, ⟨f3.1, f3.2.1⟩,
    f3.2.2.1, f3.2.2.2.1, ?_⟩
  unfold val4
  omega

theorem sub_limbs_eq (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    sub_limbs #[a0, a1, a2, a3] #[b0, b1, b2, b3] =
      (#[sbbLo a0 b0 0, sbbLo a1 b1 (sbbHi a0 b0 0),
        sbbLo a2 b2 (sbbHi a1 b1 (sbbHi a0 b0 0)),
        sbbLo a3 b3 (sbbHi a2 b2 (sbbHi a1 b1 (sbbHi a0 b0 0)))],
       sbbHi a3 b3 (sbbHi a2 b2 (sbbHi a1 b1 (sbbHi a0 b0 0)))) := by
  unfold sub_limbs
  dsimp only
  rw [whileFold_count_gen (fun (s : Array Int × Int) (j : Int) => (s.1, s.2, j)) 4
    (fun i s => (Hax.array_update s.1 i (sbbLo (Hax.index #[a0, a1, a2, a3] i)
      (Hax.index #[b0, b1, b2, b3] i) s.2),
      sbbHi (Hax.index #[a0, a1, a2, a3] i) (Hax.index #[b0, b1, b2, b3] i) s.2))
    _ (fun s j => rfl) 4 0 ((Hax.repeat_ (0 : Int) (4 : Int)), 0) (by norm_num)]
  rw [foldRange_four]
  simp only [ControlFlow.merge, Hax.repeat_]
  simp [Hax.array_update, Hax.index]

/-- `sub_limbs` on in-range limbs: four in-range words and a borrow bit whose
    value is the difference of the two 256-bit integers. -/
theorem sub_limbs_spec {a0 a1 a2 a3 b0 b1 b2 b3 : Int} (ha0 : W64 a0) (ha1 : W64 a1)
    (ha2 : W64 a2) (ha3 : W64 a3) (hb0 : W64 b0) (hb1 : W64 b1) (hb2 : W64 b2)
    (hb3 : W64 b3) :
    ∃ r0 r1 r2 r3 c : Int,
      sub_limbs #[a0, a1, a2, a3] #[b0, b1, b2, b3] = (#[r0, r1, r2, r3], c) ∧
      W64 r0 ∧ W64 r1 ∧ W64 r2 ∧ W64 r3 ∧ 0 ≤ c ∧ c ≤ 1 ∧
      val4 r0 r1 r2 r3 - 2 ^ 256 * c = val4 a0 a1 a2 a3 - val4 b0 b1 b2 b3 := by
  rw [sub_limbs_eq]
  unfold W64 at *
  have f0 := sbb_facts ha0.1 ha0.2 hb0.1 hb0.2 le_rfl zero_le_one
  have f1 := sbb_facts ha1.1 ha1.2 hb1.1 hb1.2 f0.2.2.1 f0.2.2.2.1
  have f2 := sbb_facts ha2.1 ha2.2 hb2.1 hb2.2 f1.2.2.1 f1.2.2.2.1
  have f3 := sbb_facts ha3.1 ha3.2 hb3.1 hb3.2 f2.2.2.1 f2.2.2.2.1
  refine ⟨_, _, _, _, _, rfl, ⟨f0.1, f0.2.1⟩, ⟨f1.1, f1.2.1⟩, ⟨f2.1, f2.2.1⟩, ⟨f3.1, f3.2.1⟩,
    f3.2.2.1, f3.2.2.2.1, ?_⟩
  unfold val4
  omega

/-- The word select of the extraction. -/
def selW (m x y : Int) : Int :=
  Hax.bitor_w 64 (Hax.bitand_w 64 x m) (Hax.bitand_w 64 y (Hax.bitnot_w 64 m))

theorem select_limbs_eq (m x0 x1 x2 x3 y0 y1 y2 y3 : Int) :
    select_limbs m #[x0, x1, x2, x3] #[y0, y1, y2, y3] =
      #[selW m x0 y0, selW m x1 y1, selW m x2 y2, selW m x3 y3] := by
  unfold select_limbs
  dsimp only
  rw [whileFold_count_gen (fun (s : Array Int) (j : Int) => (s, j)) 4
    (fun i s => Hax.array_update s i (selW m (Hax.index #[x0, x1, x2, x3] i)
      (Hax.index #[y0, y1, y2, y3] i)))
    _ (fun s j => rfl) 4 0 (Hax.repeat_ (0 : Int) (4 : Int)) (by norm_num)]
  rw [foldRange_four]
  simp only [ControlFlow.merge, Hax.repeat_]
  simp [Hax.array_update, Hax.index]

/-- `select_limbs` under the mask of a bit selects the first vector on `1` and the
    second on `0`. -/
theorem select_limbs_mask {t x0 x1 x2 x3 y0 y1 y2 y3 : Int} (ht : t = 0 ∨ t = 1)
    (hx0 : W64 x0) (hx1 : W64 x1) (hx2 : W64 x2) (hx3 : W64 x3)
    (hy0 : W64 y0) (hy1 : W64 y1) (hy2 : W64 y2) (hy3 : W64 y3) :
    select_limbs (mask_of t) #[x0, x1, x2, x3] #[y0, y1, y2, y3] =
      if t = 1 then #[x0, x1, x2, x3] else #[y0, y1, y2, y3] := by
  rw [select_limbs_eq]
  rcases ht with rfl | rfl
  · simp only [mask_of_zero, selW, selW_zero hy0, selW_zero hy1, selW_zero hy2,
      selW_zero hy3]
    simp
  · simp only [mask_of_one, selW, selW_ones hx0, selW_ones hx1, selW_ones hx2,
      selW_ones hx3]
    simp

/-! ## The modulus -/

theorem P_LIMBS_eq : P_LIMBS = #[18446744073709551615, 4294967295, 0,
    18446744069414584321] := rfl

omit [PrimeirDeps] in
theorem val4_P : val4 18446744073709551615 4294967295 0 18446744069414584321 = pZ := by
  norm_num [val4, pZ]

omit [PrimeirDeps] in
theorem take_eq {h b : Int} (hh : h = 0 ∨ h = 1) (hb : b = 0 ∨ b = 1) :
    Hax.bitor_w 64 h (Hax.bitxor_w 64 b 1) = if h = 1 ∨ b = 0 then 1 else 0 := by
  rcases hh with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- `reduce_once` on a value below `2p`, given as four in-range words and a top
    bit: four in-range words of the value reduced modulo `p`. -/
theorem reduce_once_spec {x0 x1 x2 x3 h : Int} (hx0 : W64 x0) (hx1 : W64 x1)
    (hx2 : W64 x2) (hx3 : W64 x3) (hh : h = 0 ∨ h = 1)
    (hlt : val4 x0 x1 x2 x3 + 2 ^ 256 * h < 2 * pZ) :
    ∃ r0 r1 r2 r3 : Int, reduce_once #[x0, x1, x2, x3] h = #[r0, r1, r2, r3] ∧
      W64 r0 ∧ W64 r1 ∧ W64 r2 ∧ W64 r3 ∧
      val4 r0 r1 r2 r3 = (val4 x0 x1 x2 x3 + 2 ^ 256 * h) % pZ := by
  have hp0 : W64 18446744073709551615 := by norm_num [W64]
  have hp1 : W64 4294967295 := by norm_num [W64]
  have hp2 : W64 0 := by norm_num [W64]
  have hp3 : W64 18446744069414584321 := by norm_num [W64]
  obtain ⟨d0, d1, d2, d3, b, he, hd0, hd1, hd2, hd3, hb0, hb1, hv⟩ :=
    sub_limbs_spec hx0 hx1 hx2 hx3 hp0 hp1 hp2 hp3
  have hb : b = 0 ∨ b = 1 := by omega
  unfold reduce_once
  rw [P_LIMBS_eq, he]
  dsimp only
  rw [take_eq hh hb]
  rw [val4_P] at hv
  have hX0 : 0 ≤ val4 x0 x1 x2 x3 := by unfold val4 W64 at *; omega
  have hX1 : val4 x0 x1 x2 x3 < 2 ^ 256 := by unfold val4 W64 at *; omega
  have hD0 : 0 ≤ val4 d0 d1 d2 d3 := by unfold val4 W64 at *; omega
  have hD1 : val4 d0 d1 d2 d3 < 2 ^ 256 := by unfold val4 W64 at *; omega
  by_cases hc : h = 1 ∨ b = 0
  · rw [ite_eq_left hc, select_limbs_mask (Or.inr rfl) hd0 hd1 hd2 hd3 hx0 hx1 hx2 hx3, ite_eq_left rfl]
    refine ⟨_, _, _, _, rfl, hd0, hd1, hd2, hd3, ?_⟩
    unfold pZ at *
    omega
  · rw [ite_eq_right hc, select_limbs_mask (Or.inl rfl) hd0 hd1 hd2 hd3 hx0 hx1 hx2 hx3,
      ite_eq_right (by norm_num)]
    refine ⟨_, _, _, _, rfl, hx0, hx1, hx2, hx3, ?_⟩
    unfold pZ at *
    omega

/-! ## Modular addition and subtraction -/

/-- `add_mod` on canonical limbs: canonical limbs of the sum modulo `p`. -/
theorem add_mod_spec {a0 a1 a2 a3 b0 b1 b2 b3 : Int} (ha0 : W64 a0) (ha1 : W64 a1)
    (ha2 : W64 a2) (ha3 : W64 a3) (hb0 : W64 b0) (hb1 : W64 b1) (hb2 : W64 b2)
    (hb3 : W64 b3) (ha : val4 a0 a1 a2 a3 < pZ) (hb : val4 b0 b1 b2 b3 < pZ) :
    ∃ r0 r1 r2 r3 : Int, add_mod #[a0, a1, a2, a3] #[b0, b1, b2, b3] = #[r0, r1, r2, r3] ∧
      W64 r0 ∧ W64 r1 ∧ W64 r2 ∧ W64 r3 ∧
      val4 r0 r1 r2 r3 = (val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3) % pZ := by
  obtain ⟨s0, s1, s2, s3, c, he, hs0, hs1, hs2, hs3, hc0, hc1, hv⟩ :=
    add_limbs_spec ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  unfold add_mod
  rw [he]
  dsimp only
  have hA : 0 ≤ val4 a0 a1 a2 a3 := by unfold val4 W64 at *; omega
  have hB : 0 ≤ val4 b0 b1 b2 b3 := by unfold val4 W64 at *; omega
  rw [← hv]
  exact reduce_once_spec hs0 hs1 hs2 hs3 (by omega) (by omega)

/-- `sub_mod` on canonical limbs: canonical limbs of the difference modulo `p`. -/
theorem sub_mod_spec {a0 a1 a2 a3 b0 b1 b2 b3 : Int} (ha0 : W64 a0) (ha1 : W64 a1)
    (ha2 : W64 a2) (ha3 : W64 a3) (hb0 : W64 b0) (hb1 : W64 b1) (hb2 : W64 b2)
    (hb3 : W64 b3) (ha : val4 a0 a1 a2 a3 < pZ) (hb : val4 b0 b1 b2 b3 < pZ) :
    ∃ r0 r1 r2 r3 : Int, sub_mod #[a0, a1, a2, a3] #[b0, b1, b2, b3] = #[r0, r1, r2, r3] ∧
      W64 r0 ∧ W64 r1 ∧ W64 r2 ∧ W64 r3 ∧
      val4 r0 r1 r2 r3 = (val4 a0 a1 a2 a3 - val4 b0 b1 b2 b3) % pZ := by
  obtain ⟨d0, d1, d2, d3, w, he, hd0, hd1, hd2, hd3, hw0, hw1, hv⟩ :=
    sub_limbs_spec ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  unfold sub_mod
  rw [he]
  dsimp only
  rw [whileFold_count_gen (fun (s : Array Int) (j : Int) => (s, j)) 4
    (fun i s => Hax.array_update s i (Hax.bitand_w 64 (Hax.index P_LIMBS i) (mask_of w)))
    _ (fun s j => rfl) 4 0 (Hax.repeat_ (0 : Int) (4 : Int)) (by norm_num)]
  rw [foldRange_four]
  simp only [ControlFlow.merge, Hax.repeat_, P_LIMBS_eq]
  have haddend : ∀ m : Int, (Hax.array_update (Hax.array_update (Hax.array_update
      (Hax.array_update (List.replicate (Int.toNat 4) (0 : Int)).toArray 0
        (Hax.bitand_w 64 (Hax.index #[18446744073709551615, 4294967295, 0,
          18446744069414584321] 0) m)) 1
        (Hax.bitand_w 64 (Hax.index #[18446744073709551615, 4294967295, 0,
          18446744069414584321] 1) m)) 2
        (Hax.bitand_w 64 (Hax.index #[18446744073709551615, 4294967295, 0,
          18446744069414584321] 2) m)) 3
        (Hax.bitand_w 64 (Hax.index #[18446744073709551615, 4294967295, 0,
          18446744069414584321] 3) m)) =
      #[Hax.bitand_w 64 18446744073709551615 m, Hax.bitand_w 64 4294967295 m,
        Hax.bitand_w 64 0 m, Hax.bitand_w 64 18446744069414584321 m] := by
    intro m; simp [Hax.array_update, Hax.index]
  rw [haddend]
  have hA : 0 ≤ val4 a0 a1 a2 a3 := by unfold val4 W64 at *; omega
  have hB : 0 ≤ val4 b0 b1 b2 b3 := by unfold val4 W64 at *; omega
  have hD0 : 0 ≤ val4 d0 d1 d2 d3 := by unfold val4 W64 at *; omega
  have hD1 : val4 d0 d1 d2 d3 < 2 ^ 256 := by unfold val4 W64 at *; omega
  have hz : W64 0 := by norm_num [W64]
  rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
  · simp only [mask_of_zero, bitand_zero]
    obtain ⟨r0, r1, r2, r3, c, he2, hr0, hr1, hr2, hr3, hc0, hc1, hv2⟩ :=
      add_limbs_spec hd0 hd1 hd2 hd3 hz hz hz hz
    rw [he2]
    refine ⟨_, _, _, _, rfl, hr0, hr1, hr2, hr3, ?_⟩
    have hR0 : 0 ≤ val4 r0 r1 r2 r3 := by unfold val4 W64 at *; omega
    have hR1 : val4 r0 r1 r2 r3 < 2 ^ 256 := by unfold val4 W64 at *; omega
    have h00 : val4 0 0 0 0 = 0 := by norm_num [val4]
    unfold pZ at *
    omega
  · have hp0 : W64 18446744073709551615 := by norm_num [W64]
    have hp1 : W64 4294967295 := by norm_num [W64]
    have hp3 : W64 18446744069414584321 := by norm_num [W64]
    simp only [mask_of_one, bitand_ones hp0, bitand_ones hp1, bitand_ones hz,
      bitand_ones hp3]
    obtain ⟨r0, r1, r2, r3, c, he2, hr0, hr1, hr2, hr3, hc0, hc1, hv2⟩ :=
      add_limbs_spec hd0 hd1 hd2 hd3 hp0 hp1 hz hp3
    rw [he2]
    refine ⟨_, _, _, _, rfl, hr0, hr1, hr2, hr3, ?_⟩
    have hR0 : 0 ≤ val4 r0 r1 r2 r3 := by unfold val4 W64 at *; omega
    have hR1 : val4 r0 r1 r2 r3 < 2 ^ 256 := by unfold val4 W64 at *; omega
    rw [val4_P] at hv2
    unfold pZ at *
    omega

/-! ## Montgomery multiplication -/

/-- The Montgomery multiplication of `mont_mul_limbs` on canonical limbs:
    canonical limbs `r` with `r · 2^256 ≡ a · b (mod p)`. -/
theorem mont_mul_limbs_spec {a0 a1 a2 a3 b0 b1 b2 b3 : Int} (ha0 : W64 a0) (ha1 : W64 a1)
    (ha2 : W64 a2) (ha3 : W64 a3) (hb0 : W64 b0) (hb1 : W64 b1) (hb2 : W64 b2)
    (hb3 : W64 b3) (ha : val4 a0 a1 a2 a3 < pZ) :
    ∃ r0 r1 r2 r3 M : Int,
      mont_mul_limbs #[a0, a1, a2, a3] #[b0, b1, b2, b3] = #[r0, r1, r2, r3] ∧
      W64 r0 ∧ W64 r1 ∧ W64 r2 ∧ W64 r3 ∧ val4 r0 r1 r2 r3 < pZ ∧
      val4 r0 r1 r2 r3 * 2 ^ 256 = val4 a0 a1 a2 a3 * val4 b0 b1 b2 b3 + M * pZ := by
  rw [mont_mul_limbs_eq]
  dsimp only
  rw [foldRange_four, show Hax.repeat_ (0 : Int) (6 : Int) = #[0, 0, 0, 0, 0, 0] from rfl]
  have hz : W64 0 := by norm_num [W64]
  have hp : (0 : Int) < pZ := by unfold pZ; norm_num
  obtain ⟨p0, p1, p2, p3, p4, m0, he0, hp0, hp1, hp2, hp3, hp4, hlt0, hv0⟩ :=
    mmOuter_spec (b := #[b0, b1, b2, b3]) (i := 0) ha0 ha1 ha2 ha3 ha (by rw [idx4_0]; exact hb0)
      hz hz hz hz hz (by norm_num [val4]; linarith)
  rw [he0]
  obtain ⟨q0, q1, q2, q3, q4, m1, he1, hq0, hq1, hq2, hq3, hq4, hlt1, hv1⟩ :=
    mmOuter_spec (b := #[b0, b1, b2, b3]) (i := 1) ha0 ha1 ha2 ha3 ha (by rw [idx4_1]; exact hb1)
      hp0 hp1 hp2 hp3 hp4 hlt0
  rw [he1]
  obtain ⟨s0, s1, s2, s3, s4, m2, he2, hs0, hs1, hs2, hs3, hs4, hlt2, hv2⟩ :=
    mmOuter_spec (b := #[b0, b1, b2, b3]) (i := 2) ha0 ha1 ha2 ha3 ha (by rw [idx4_2]; exact hb2)
      hq0 hq1 hq2 hq3 hq4 hlt1
  rw [he2]
  obtain ⟨t0, t1, t2, t3, t4, m3, he3, ht0, ht1, ht2, ht3, ht4, hlt3, hv3⟩ :=
    mmOuter_spec (b := #[b0, b1, b2, b3]) (i := 3) ha0 ha1 ha2 ha3 ha (by rw [idx4_3]; exact hb3)
      hs0 hs1 hs2 hs3 hs4 hlt2
  rw [he3]
  simp only [idx4_0, idx4_1, idx4_2, idx4_3] at hv0 hv1 hv2 hv3
  simp only [idx6_0, idx6_1, idx6_2, idx6_3, idx6_4]
  have hT0 := val4_nonneg ht0 ht1 ht2 ht3
  have ht4b : t4 = 0 ∨ t4 = 1 := by
    refine bit_of_lt_two ht4.1 ?_
    by_contra hcon
    have h2 : (2 : Int) * 2 ^ 256 ≤ 2 ^ 256 * t4 := by linarith
    have hpz : pZ < 2 ^ 256 := by unfold pZ; norm_num
    linarith only [h2, hpz, hT0, hlt3]
  obtain ⟨r0, r1, r2, r3, her, hr0, hr1, hr2, hr3, hrv⟩ :=
    reduce_once_spec ht0 ht1 ht2 ht3 ht4b hlt3
  refine ⟨r0, r1, r2, r3,
    m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3
      - (val4 t0 t1 t2 t3 + 2 ^ 256 * t4) / pZ * 2 ^ 256,
    her, hr0, hr1, hr2, hr3, ?_, ?_⟩
  · rw [hrv]; exact Int.emod_lt_of_pos _ hp
  · have hdiv := splitP (val4 t0 t1 t2 t3 + 2 ^ 256 * t4)
    rw [hrv]
    have h00 : val4 0 0 0 0 = 0 := by norm_num [val4]
    rw [h00] at hv0
    have hB : val4 b0 b1 b2 b3 = b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3 := rfl
    rw [hB]
    linear_combination (2 ^ 192 : Int) * hv3 + (2 ^ 128 : Int) * hv2 + (2 ^ 64 : Int) * hv1
      + hv0 + (2 ^ 256 : Int) * hdiv

/-! ## The Montgomery valuation -/

open CatCrypt.Util (P256 Fp256)

omit [PrimeirDeps] in
theorem pZ_eq : pZ = ((P256 : ℕ) : ℤ) := by
  unfold pZ; norm_num [P256]

omit [PrimeirDeps] in
theorem intCast_pZ : ((pZ : ℤ) : Fp256) = 0 := by
  rw [pZ_eq, Int.cast_natCast, ZMod.natCast_self]

omit [PrimeirDeps] in
theorem intCast_emod_pZ (X : ℤ) : (((X % pZ : ℤ)) : Fp256) = (X : Fp256) := by
  rw [pZ_eq, ZMod.intCast_mod]

omit [PrimeirDeps] in
theorem two_pow_ne_zero : ((2 : Fp256) ^ 256) ≠ 0 := by
  apply pow_ne_zero
  intro h
  have h2 : ((2 : ℕ) : Fp256) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  norm_num [P256] at this

/-- The four limbs of `a` denote an integer in `[0, p)`. -/
def Canon (a : Array Int) : Prop :=
  ∃ x0 x1 x2 x3 : Int, a = #[x0, x1, x2, x3] ∧ W64 x0 ∧ W64 x1 ∧ W64 x2 ∧ W64 x3 ∧
    val4 x0 x1 x2 x3 < pZ

/-- The integer of the four limbs of `a`. -/
def limbVal (a : Array Int) : Int :=
  val4 (Hax.index a 0) (Hax.index a 1) (Hax.index a 2) (Hax.index a 3)

omit [PrimeirDeps] in
@[simp] theorem limbVal_lit (x0 x1 x2 x3 : Int) : limbVal #[x0, x1, x2, x3] = val4 x0 x1 x2 x3 :=
  rfl

/-- The field element four Montgomery-domain limbs stand for: their integer
    times `R⁻¹` with `R = 2^256`. -/
noncomputable def montVal (a : Array Int) : Fp256 :=
  ((limbVal a : ℤ) : Fp256) * ((2 : Fp256) ^ 256)⁻¹

/-! ## Field operations on canonical limbs -/

/-- `mont_mul_limbs` computes the field product of the Montgomery values. -/
theorem mont_mul_limbs_val {a b : Array Int} (ha : Canon a) (hb : Canon b) :
    Canon (mont_mul_limbs a b) ∧ montVal (mont_mul_limbs a b) = montVal a * montVal b := by
  obtain ⟨a0, a1, a2, a3, rfl, ha0, ha1, ha2, ha3, hA⟩ := ha
  obtain ⟨b0, b1, b2, b3, rfl, hb0, hb1, hb2, hb3, hB⟩ := hb
  obtain ⟨r0, r1, r2, r3, M, he, hr0, hr1, hr2, hr3, hR, hv⟩ :=
    mont_mul_limbs_spec ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hA
  rw [he]
  refine ⟨⟨r0, r1, r2, r3, rfl, hr0, hr1, hr2, hr3, hR⟩, ?_⟩
  have hc : ((val4 r0 r1 r2 r3 : ℤ) : Fp256) * (2 : Fp256) ^ 256
      = ((val4 a0 a1 a2 a3 : ℤ) : Fp256) * ((val4 b0 b1 b2 b3 : ℤ) : Fp256) := by
    have := congrArg (fun x : ℤ => (x : Fp256)) hv
    simp only [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_ofNat, intCast_pZ,
      mul_zero, add_zero] at this
    exact this
  simp only [montVal, limbVal_lit]
  have hR0 := two_pow_ne_zero
  have hr : ((val4 r0 r1 r2 r3 : ℤ) : Fp256) = ((val4 a0 a1 a2 a3 : ℤ) : Fp256)
      * ((val4 b0 b1 b2 b3 : ℤ) : Fp256) * ((2 : Fp256) ^ 256)⁻¹ := by
    rw [← hc, mul_assoc, mul_inv_cancel₀ hR0, mul_one]
  rw [hr]; ring

omit [PrimeirDeps] in
theorem canon_of_emod {r0 r1 r2 r3 X : Int} (hr0 : W64 r0) (hr1 : W64 r1) (hr2 : W64 r2)
    (hr3 : W64 r3) (hv : val4 r0 r1 r2 r3 = X % pZ) :
    Canon #[r0, r1, r2, r3] ∧ montVal #[r0, r1, r2, r3] = (X : Fp256) * ((2 : Fp256) ^ 256)⁻¹ := by
  refine ⟨⟨r0, r1, r2, r3, rfl, hr0, hr1, hr2, hr3, ?_⟩, ?_⟩
  · rw [hv]; exact Int.emod_lt_of_pos _ (by unfold pZ; norm_num)
  · simp only [montVal, limbVal_lit, hv, intCast_emod_pZ]

/-- `add_mod` computes the field sum of the Montgomery values. -/
theorem add_mod_val {a b : Array Int} (ha : Canon a) (hb : Canon b) :
    Canon (add_mod a b) ∧ montVal (add_mod a b) = montVal a + montVal b := by
  obtain ⟨a0, a1, a2, a3, rfl, ha0, ha1, ha2, ha3, hA⟩ := ha
  obtain ⟨b0, b1, b2, b3, rfl, hb0, hb1, hb2, hb3, hB⟩ := hb
  obtain ⟨r0, r1, r2, r3, he, hr0, hr1, hr2, hr3, hv⟩ :=
    add_mod_spec ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hA hB
  rw [he]
  obtain ⟨hc, hm⟩ := canon_of_emod hr0 hr1 hr2 hr3 hv
  refine ⟨hc, ?_⟩
  rw [hm]; simp only [montVal, limbVal_lit]; push_cast; ring

/-- `sub_mod` computes the field difference of the Montgomery values. -/
theorem sub_mod_val {a b : Array Int} (ha : Canon a) (hb : Canon b) :
    Canon (sub_mod a b) ∧ montVal (sub_mod a b) = montVal a - montVal b := by
  obtain ⟨a0, a1, a2, a3, rfl, ha0, ha1, ha2, ha3, hA⟩ := ha
  obtain ⟨b0, b1, b2, b3, rfl, hb0, hb1, hb2, hb3, hB⟩ := hb
  obtain ⟨r0, r1, r2, r3, he, hr0, hr1, hr2, hr3, hv⟩ :=
    sub_mod_spec ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hA hB
  rw [he]
  obtain ⟨hc, hm⟩ := canon_of_emod hr0 hr1 hr2 hr3 hv
  refine ⟨hc, ?_⟩
  rw [hm]; simp only [montVal, limbVal_lit]; push_cast; ring

omit [PrimeirDeps] in
theorem canon_zero : Canon #[0, 0, 0, 0] :=
  ⟨0, 0, 0, 0, rfl, by norm_num [W64], by norm_num [W64], by norm_num [W64], by norm_num [W64],
    by norm_num [val4, pZ]⟩

omit [PrimeirDeps] in
/-- The all-zero limb array has Montgomery value `0`. -/
theorem montVal_zero : montVal #[0, 0, 0, 0] = 0 := by
  simp [montVal, val4]

/-- The negation of `Field::neg`, `sub_mod` from zero, computes the field
    negation of the Montgomery value. -/
theorem neg_val {a : Array Int} (ha : Canon a) :
    Canon (sub_mod #[0, 0, 0, 0] a) ∧ montVal (sub_mod #[0, 0, 0, 0] a) = - montVal a := by
  obtain ⟨h1, h2⟩ := sub_mod_val canon_zero ha
  exact ⟨h1, by rw [h2, montVal_zero, zero_sub]⟩

/-- The selection of `CtField::ct_select`, `select_limbs` under the mask of the
    bit, selects the first argument on `1` and the second on `0`. -/
theorem ct_select_val {c : Int} {a b : Array Int} (hc : c = 0 ∨ c = 1) (ha : Canon a)
    (hb : Canon b) : select_limbs (mask_of c) a b = if c = 1 then a else b := by
  obtain ⟨a0, a1, a2, a3, rfl, ha0, ha1, ha2, ha3, -⟩ := ha
  obtain ⟨b0, b1, b2, b3, rfl, hb0, hb1, hb2, hb3, -⟩ := hb
  exact select_limbs_mask hc ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3

theorem R_LIMBS_eq : R_LIMBS = #[1, 18446744069414584320, 18446744073709551615, 4294967294] :=
  rfl

theorem canon_R : Canon R_LIMBS := by
  rw [R_LIMBS_eq]
  exact ⟨_, _, _, _, rfl, by norm_num [W64], by norm_num [W64], by norm_num [W64],
    by norm_num [W64], by norm_num [val4, pZ]⟩

/-- `R_LIMBS`, the `ONE` of `Field`, has Montgomery value `1`. -/
theorem montVal_R : montVal R_LIMBS = 1 := by
  rw [R_LIMBS_eq]
  have hv : val4 1 18446744069414584320 18446744073709551615 4294967294 = 2 ^ 256 % pZ := by
    norm_num [val4, pZ]
  simp only [montVal, limbVal_lit, hv, intCast_emod_pZ]
  rw [Int.cast_pow, Int.cast_ofNat]
  exact mul_inv_cancel₀ two_pow_ne_zero

/-! ## The in-place reduction `mont_reduce` -/

section Lit8

omit [PrimeirDeps]

variable (a b c d e f g h v : Int)

theorem idx8_0 : Hax.index #[a, b, c, d, e, f, g, h] 0 = a := rfl
theorem idx8_1 : Hax.index #[a, b, c, d, e, f, g, h] 1 = b := rfl
theorem idx8_2 : Hax.index #[a, b, c, d, e, f, g, h] 2 = c := rfl
theorem idx8_3 : Hax.index #[a, b, c, d, e, f, g, h] 3 = d := rfl
theorem idx8_4 : Hax.index #[a, b, c, d, e, f, g, h] 4 = e := rfl
theorem idx8_5 : Hax.index #[a, b, c, d, e, f, g, h] 5 = f := rfl
theorem idx8_6 : Hax.index #[a, b, c, d, e, f, g, h] 6 = g := rfl
theorem idx8_7 : Hax.index #[a, b, c, d, e, f, g, h] 7 = h := rfl
theorem upd8_0 : Hax.array_update #[a, b, c, d, e, f, g, h] 0 v = #[v, b, c, d, e, f, g, h] := rfl
theorem upd8_1 : Hax.array_update #[a, b, c, d, e, f, g, h] 1 v = #[a, v, c, d, e, f, g, h] := rfl
theorem upd8_2 : Hax.array_update #[a, b, c, d, e, f, g, h] 2 v = #[a, b, v, d, e, f, g, h] := rfl
theorem upd8_3 : Hax.array_update #[a, b, c, d, e, f, g, h] 3 v = #[a, b, c, v, e, f, g, h] := rfl
theorem upd8_4 : Hax.array_update #[a, b, c, d, e, f, g, h] 4 v = #[a, b, c, d, v, f, g, h] := rfl
theorem upd8_5 : Hax.array_update #[a, b, c, d, e, f, g, h] 5 v = #[a, b, c, d, e, v, g, h] := rfl
theorem upd8_6 : Hax.array_update #[a, b, c, d, e, f, g, h] 6 v = #[a, b, c, d, e, f, v, h] := rfl
theorem upd8_7 : Hax.array_update #[a, b, c, d, e, f, g, h] 7 v = #[a, b, c, d, e, f, g, v] := rfl
theorem idx5_0 : Hax.index #[a, b, c, d, e] 0 = a := rfl
theorem idx5_1 : Hax.index #[a, b, c, d, e] 1 = b := rfl
theorem idx5_2 : Hax.index #[a, b, c, d, e] 2 = c := rfl
theorem idx5_3 : Hax.index #[a, b, c, d, e] 3 = d := rfl
theorem idx5_4 : Hax.index #[a, b, c, d, e] 4 = e := rfl

end Lit8

/-- One round of `mont_reduce` on the words `u0, …, u4` at its position and the
    pending carry: the four new words and the carry out, in that order. -/
def rnd (u0 u1 u2 u3 u4 pend : Int) : Array Int :=
  let m := Hax.wrapping_mul_w 64 u0 N0INV
  let mp := Hax.mul (Hax.castVal_w 128 m) (Hax.castVal_w 128 POLY3)
  let s1 := Hax.add (Hax.castVal_w 128 u1) (Hax.castVal_w 128 (Hax.shl_w 64 m (32 : Int)))
  let s2 := Hax.add (Hax.add (Hax.castVal_w 128 u2) (Hax.castVal_w 128 (Hax.shr_w 64 m (32 : Int)))) (Hax.shr_w 128 s1 (64 : Int))
  let s3 := Hax.add (Hax.add (Hax.castVal_w 128 u3) (Hax.castVal_w 128 (Hax.castVal_w 64 mp))) (Hax.shr_w 128 s2 (64 : Int))
  let s4 := Hax.add (Hax.add (Hax.add (Hax.castVal_w 128 u4) (Hax.shr_w 128 mp (64 : Int))) (Hax.shr_w 128 s3 (64 : Int))) (Hax.castVal_w 128 pend)
  #[Hax.castVal_w 64 s1, Hax.castVal_w 64 s2, Hax.castVal_w 64 s3, Hax.castVal_w 64 s4,
    Hax.castVal_w 64 (Hax.shr_w 128 s4 (64 : Int))]

set_option exponentiation.threshold 512 in
/-- A round of `mont_reduce` adds `u0 · p` at its position and moves the value up
    by a word, with the pending carry at the weight of `u4`. -/
theorem rnd_spec {u0 u1 u2 u3 u4 pend : Int} (h0 : W64 u0) (h1 : W64 u1) (h2 : W64 u2)
    (h3 : W64 u3) (h4 : W64 u4) (h5 : W64 pend) :
    ∃ v1 v2 v3 v4 w : Int, rnd u0 u1 u2 u3 u4 pend = #[v1, v2, v3, v4, w] ∧
      W64 v1 ∧ W64 v2 ∧ W64 v3 ∧ W64 v4 ∧ W64 w ∧
      2 ^ 64 * (val4 v1 v2 v3 v4 + 2 ^ 256 * w)
        = val4 u0 u1 u2 u3 + 2 ^ 256 * (u4 + pend) + u0 * pZ := by
  unfold W64 at *
  have hm : Hax.wrapping_mul_w 64 u0 N0INV = u0 := by
    rw [N0INV_eq]; simp only [Hax.wrapping_mul_w, mul_one]
    exact castVal_of_lt h0.1 h0.2
  unfold rnd
  simp only [hm, POLY3_eq, cast128 h1.1 (by omega), cast128 h2.1 (by omega),
    cast128 h3.1 (by omega), cast128 h4.1 (by omega), cast128 h5.1 (by omega),
    cast128 h0.1 (by omega), cast128 (show (0 : Int) ≤ 18446744069414584321 by norm_num)
      (by norm_num), shl64_32 h0, shr64_32 h0, Hax.add, Hax.mul]
  rw [cast128 (x := u0 * 2 ^ 32 % 2 ^ 64) (by omega) (by omega),
    cast128 (x := u0 / 2 ^ 32) (by omega) (by omega),
    cast64 (x := u0 * 18446744069414584321) (by omega),
    cast128 (x := u0 * 18446744069414584321 % 2 ^ 64) (by omega) (by omega),
    shr128_64 (s := u0 * 18446744069414584321) (by omega) (by omega)]
  have et : u0 * 2 ^ 32 % 2 ^ 64 + 2 ^ 64 * (u0 / 2 ^ 32) = u0 * 2 ^ 32 := by omega
  have emp := split64 (u0 * 18446744069414584321)
  have bmp0 : 0 ≤ u0 * 18446744069414584321 % 2 ^ 64 := Int.emod_nonneg _ (by norm_num)
  have bmp3 : u0 * 18446744069414584321 % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by norm_num)
  have bmp1 : 0 ≤ u0 * 18446744069414584321 / 2 ^ 64 := by omega
  have bmp2 : u0 * 18446744069414584321 / 2 ^ 64 < 2 ^ 64 := by omega
  have bt0 : 0 ≤ u0 * 2 ^ 32 % 2 ^ 64 := Int.emod_nonneg _ (by norm_num)
  have bt1 : u0 * 2 ^ 32 % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by norm_num)
  have bq0 : 0 ≤ u0 / 2 ^ 32 := by omega
  have bq1 : u0 / 2 ^ 32 < 2 ^ 32 := by omega
  clear hm
  generalize hS1 : u1 + u0 * 2 ^ 32 % 2 ^ 64 = S1
  have b1 : 0 ≤ S1 ∧ S1 < 2 ^ 65 := by constructor <;> linarith [h1.1, h1.2]
  rw [shr128_64 (s := S1) b1.1 (by linarith [b1.2])]
  have c1 : 0 ≤ S1 / 2 ^ 64 ∧ S1 / 2 ^ 64 < 2 := div64_bound b1.1 (by linarith [b1.2])
  have e1 := split64 S1
  generalize hS2 : u2 + u0 / 2 ^ 32 + S1 / 2 ^ 64 = S2
  have b2 : 0 ≤ S2 ∧ S2 < 2 ^ 65 := by constructor <;> linarith [h2.1, h2.2]
  rw [shr128_64 (s := S2) b2.1 (by linarith [b2.2])]
  have c2 : 0 ≤ S2 / 2 ^ 64 ∧ S2 / 2 ^ 64 < 2 := div64_bound b2.1 (by linarith [b2.2])
  have e2 := split64 S2
  generalize hS3 : u3 + u0 * 18446744069414584321 % 2 ^ 64 + S2 / 2 ^ 64 = S3
  have b3 : 0 ≤ S3 ∧ S3 < 2 ^ 66 := by constructor <;> linarith [h3.1, h3.2]
  rw [shr128_64 (s := S3) b3.1 (by linarith [b3.2])]
  have c3 : 0 ≤ S3 / 2 ^ 64 ∧ S3 / 2 ^ 64 < 4 := div64_bound b3.1 (by linarith [b3.2])
  have e3 := split64 S3
  generalize hS4 : u4 + u0 * 18446744069414584321 / 2 ^ 64 + S3 / 2 ^ 64 + pend = S4
  have b4 : 0 ≤ S4 ∧ S4 < 2 ^ 66 := by constructor <;> linarith [h4.1, h4.2, h5.1, h5.2]
  rw [shr128_64 (s := S4) b4.1 (by linarith [b4.2])]
  have c4 : 0 ≤ S4 / 2 ^ 64 ∧ S4 / 2 ^ 64 < 4 := div64_bound b4.1 (by linarith [b4.2])
  have e4 := split64 S4
  have m1 : 0 ≤ S1 % 2 ^ 64 ∧ S1 % 2 ^ 64 < 2 ^ 64 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have m2 : 0 ≤ S2 % 2 ^ 64 ∧ S2 % 2 ^ 64 < 2 ^ 64 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have m3 : 0 ≤ S3 % 2 ^ 64 ∧ S3 % 2 ^ 64 < 2 ^ 64 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have m4 : 0 ≤ S4 % 2 ^ 64 ∧ S4 % 2 ^ 64 < 2 ^ 64 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  rw [cast64 b1.1, cast64 b2.1, cast64 b3.1, cast64 b4.1,
    castVal_of_lt (w := 64) c4.1 (by linarith [c4.2])]
  refine ⟨_, _, _, _, _, rfl, m1, m2, m3, m4, ⟨c4.1, by linarith [c4.2]⟩, ?_⟩
  unfold val4 pZ
  linear_combination (2 ^ 64 : Int) * e1 + (2 ^ 128 : Int) * e2 + (2 ^ 192 : Int) * e3
    + (2 ^ 256 : Int) * e4 - (2 ^ 64 : Int) * hS1 - (2 ^ 128 : Int) * hS2
    - (2 ^ 192 : Int) * hS3 - (2 ^ 256 : Int) * hS4
    + (2 ^ 64 : Int) * et + (2 ^ 192 : Int) * emp

/-- The loop body of `mont_reduce` at index `i` on the words and the pending carry. -/
def mrBody (i : Int) (st : Array Int × Int) : Array Int × Int :=
  let t := st.1
  let pend := st.2
  let m := Hax.wrapping_mul_w 64 (Hax.index t i) N0INV
  let mp := Hax.mul (Hax.castVal_w 128 m) (Hax.castVal_w 128 POLY3)
  let s1 := Hax.add (Hax.castVal_w 128 (Hax.index t (Hax.add i (1 : Int)))) (Hax.castVal_w 128 (Hax.shl_w 64 m (32 : Int)))
  let t := Hax.array_update t (Hax.add i (1 : Int)) (Hax.castVal_w 64 s1)
  let s2 := Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index t (Hax.add i (2 : Int)))) (Hax.castVal_w 128 (Hax.shr_w 64 m (32 : Int)))) (Hax.shr_w 128 s1 (64 : Int))
  let t := Hax.array_update t (Hax.add i (2 : Int)) (Hax.castVal_w 64 s2)
  let s3 := Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index t (Hax.add i (3 : Int)))) (Hax.castVal_w 128 (Hax.castVal_w 64 mp))) (Hax.shr_w 128 s2 (64 : Int))
  let t := Hax.array_update t (Hax.add i (3 : Int)) (Hax.castVal_w 64 s3)
  let s4 := Hax.add (Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index t (Hax.add i (4 : Int)))) (Hax.shr_w 128 mp (64 : Int))) (Hax.shr_w 128 s3 (64 : Int))) (Hax.castVal_w 128 pend)
  let t := Hax.array_update t (Hax.add i (4 : Int)) (Hax.castVal_w 64 s4)
  let pend := Hax.castVal_w 64 (Hax.shr_w 128 s4 (64 : Int))
  (t, pend)

/-- `mont_reduce` is `reduce_once` of four rounds of `mrBody`. -/
theorem mont_reduce_eq (t : Array Int) :
    mont_reduce t =
      let st := Hax.foldRange 0 4 (t, 0) mrBody
      reduce_once #[Hax.index st.1 4, Hax.index st.1 5, Hax.index st.1 6, Hax.index st.1 7]
        st.2 := by
  unfold mont_reduce
  dsimp only
  rw [whileFold_count_gen (fun (s : Array Int × Int) (j : Int) => (s.1, s.2, j)) 4 mrBody
    _ (fun s j => rfl) 4 0 (t, 0) (by norm_num)]
  rfl

theorem mrBody_0 (t0 t1 t2 t3 t4 t5 t6 t7 q : Int) :
    mrBody 0 (#[t0, t1, t2, t3, t4, t5, t6, t7], q) =
      let r := rnd t0 t1 t2 t3 t4 q
      (#[t0, Hax.index r 0, Hax.index r 1, Hax.index r 2, Hax.index r 3, t5, t6, t7],
        Hax.index r 4) := by
  unfold mrBody rnd
  simp only [Hax.add, Int.reduceAdd, idx8_0, idx8_1, idx8_2, idx8_3, idx8_4, upd8_1, upd8_2,
    upd8_3, upd8_4, idx5_0, idx5_1, idx5_2, idx5_3, idx5_4]

theorem mrBody_1 (t0 t1 t2 t3 t4 t5 t6 t7 q : Int) :
    mrBody 1 (#[t0, t1, t2, t3, t4, t5, t6, t7], q) =
      let r := rnd t1 t2 t3 t4 t5 q
      (#[t0, t1, Hax.index r 0, Hax.index r 1, Hax.index r 2, Hax.index r 3, t6, t7],
        Hax.index r 4) := by
  unfold mrBody rnd
  simp only [Hax.add, Int.reduceAdd, idx8_1, idx8_2, idx8_3, idx8_4, idx8_5, upd8_2, upd8_3,
    upd8_4, upd8_5, idx5_0, idx5_1, idx5_2, idx5_3, idx5_4]

theorem mrBody_2 (t0 t1 t2 t3 t4 t5 t6 t7 q : Int) :
    mrBody 2 (#[t0, t1, t2, t3, t4, t5, t6, t7], q) =
      let r := rnd t2 t3 t4 t5 t6 q
      (#[t0, t1, t2, Hax.index r 0, Hax.index r 1, Hax.index r 2, Hax.index r 3, t7],
        Hax.index r 4) := by
  unfold mrBody rnd
  simp only [Hax.add, Int.reduceAdd, idx8_2, idx8_3, idx8_4, idx8_5, idx8_6, upd8_3, upd8_4,
    upd8_5, upd8_6, idx5_0, idx5_1, idx5_2, idx5_3, idx5_4]

theorem mrBody_3 (t0 t1 t2 t3 t4 t5 t6 t7 q : Int) :
    mrBody 3 (#[t0, t1, t2, t3, t4, t5, t6, t7], q) =
      let r := rnd t3 t4 t5 t6 t7 q
      (#[t0, t1, t2, t3, Hax.index r 0, Hax.index r 1, Hax.index r 2, Hax.index r 3],
        Hax.index r 4) := by
  unfold mrBody rnd
  simp only [Hax.add, Int.reduceAdd, idx8_3, idx8_4, idx8_5, idx8_6, idx8_7, upd8_4, upd8_5,
    upd8_6, upd8_7, idx5_0, idx5_1, idx5_2, idx5_3, idx5_4]

set_option exponentiation.threshold 1024 in
/-- `mont_reduce` of eight in-range words whose integer `T` is below `p · 2^256`:
    canonical limbs `r` with `r · 2^256 = T + M · p`. -/
theorem mont_reduce_spec {t0 t1 t2 t3 t4 t5 t6 t7 : Int} (h0 : W64 t0) (h1 : W64 t1)
    (h2 : W64 t2) (h3 : W64 t3) (h4 : W64 t4) (h5 : W64 t5) (h6 : W64 t6) (h7 : W64 t7)
    (hT : val4 t0 t1 t2 t3 + 2 ^ 256 * val4 t4 t5 t6 t7 < pZ * 2 ^ 256) :
    ∃ r0 r1 r2 r3 M : Int,
      mont_reduce #[t0, t1, t2, t3, t4, t5, t6, t7] = #[r0, r1, r2, r3] ∧
      W64 r0 ∧ W64 r1 ∧ W64 r2 ∧ W64 r3 ∧ val4 r0 r1 r2 r3 < pZ ∧
      val4 r0 r1 r2 r3 * 2 ^ 256 = val4 t0 t1 t2 t3 + 2 ^ 256 * val4 t4 t5 t6 t7 + M * pZ := by
  rw [mont_reduce_eq]
  dsimp only
  have hz : W64 0 := by norm_num [W64]
  have hp : (0 : Int) < pZ := by unfold pZ; norm_num
  rw [foldRange_four, mrBody_0]
  obtain ⟨a1, a2, a3, a4, w0, he0, ha1, ha2, ha3, ha4, hw0, hv0⟩ := rnd_spec h0 h1 h2 h3 h4 hz
  dsimp only
  rw [he0]
  simp only [idx5_0, idx5_1, idx5_2, idx5_3, idx5_4]
  rw [mrBody_1]
  obtain ⟨b2, b3, b4, b5, w1, he1, hb2, hb3, hb4, hb5, hw1, hv1⟩ :=
    rnd_spec ha1 ha2 ha3 ha4 h5 hw0
  dsimp only
  rw [he1]
  simp only [idx5_0, idx5_1, idx5_2, idx5_3, idx5_4]
  rw [mrBody_2]
  obtain ⟨c3, c4, c5, c6, w2, he2, hc3, hc4, hc5, hc6, hw2, hv2⟩ :=
    rnd_spec hb2 hb3 hb4 hb5 h6 hw1
  dsimp only
  rw [he2]
  simp only [idx5_0, idx5_1, idx5_2, idx5_3, idx5_4]
  rw [mrBody_3]
  obtain ⟨d4, d5, d6, d7, w3, he3, hd4, hd5, hd6, hd7, hw3, hv3⟩ :=
    rnd_spec hc3 hc4 hc5 hc6 h7 hw2
  dsimp only
  rw [he3]
  simp only [idx5_0, idx5_1, idx5_2, idx5_3, idx5_4, idx8_4, idx8_5, idx8_6, idx8_7]
  have hkey : (val4 d4 d5 d6 d7 + 2 ^ 256 * w3) * 2 ^ 256
      = val4 t0 t1 t2 t3 + 2 ^ 256 * val4 t4 t5 t6 t7 + val4 t0 a1 b2 c3 * pZ := by
    unfold val4 at *
    linear_combination (2 ^ 192 : Int) * hv3 + (2 ^ 128 : Int) * hv2 + (2 ^ 64 : Int) * hv1
      + hv0
  have hM := val4_lt h0 ha1 hb2 hc3
  have hMp : val4 t0 a1 b2 c3 * pZ ≤ (2 ^ 256 - 1) * pZ :=
    mul_le_mul_of_nonneg_right (by linarith) hp.le
  have hV : val4 d4 d5 d6 d7 + 2 ^ 256 * w3 < 2 * pZ := by
    have : (val4 d4 d5 d6 d7 + 2 ^ 256 * w3) * 2 ^ 256 < 2 * pZ * 2 ^ 256 := by
      rw [hkey]; linarith only [hT, hMp, hp]
    linarith only [this]
  have hD0 := val4_nonneg hd4 hd5 hd6 hd7
  have hw3b : w3 = 0 ∨ w3 = 1 := by
    refine bit_of_lt_two hw3.1 ?_
    by_contra hcon
    have h2 : (2 : Int) * 2 ^ 256 ≤ 2 ^ 256 * w3 := by linarith
    have hpz : pZ < 2 ^ 256 := by unfold pZ; norm_num
    linarith only [h2, hpz, hD0, hV]
  obtain ⟨r0, r1, r2, r3, her, hr0, hr1, hr2, hr3, hrv⟩ :=
    reduce_once_spec hd4 hd5 hd6 hd7 hw3b hV
  refine ⟨r0, r1, r2, r3,
    val4 t0 a1 b2 c3 - (val4 d4 d5 d6 d7 + 2 ^ 256 * w3) / pZ * 2 ^ 256,
    her, hr0, hr1, hr2, hr3, ?_, ?_⟩
  · rw [hrv]; exact Int.emod_lt_of_pos _ hp
  · have hdiv := splitP (val4 d4 d5 d6 d7 + 2 ^ 256 * w3)
    rw [hrv]
    linear_combination hkey + (2 ^ 256 : Int) * hdiv

/-! ## The squaring `mont_sqr_limbs` -/

/-- One step of a triangle row of `mont_sqr_limbs`: word `i + j` plus
    `a[i] · a[j]` plus the carry. -/
def sqRow (a : Array Int) (i j : Int) (s : Array Int × Int) : Array Int × Int :=
  (Hax.array_update s.1 (Hax.add i j)
    (macLo (Hax.index s.1 (Hax.add i j)) (Hax.index a i) (Hax.index a j) s.2),
    macHi (Hax.index s.1 (Hax.add i j)) (Hax.index a i) (Hax.index a j) s.2)

/-- Row `i` of the strict upper triangle of `a · a` in `mont_sqr_limbs`. -/
def sqTri (a : Array Int) (i : Int) (t : Array Int) : Array Int :=
  let carry := (0 : Int)
  let j := Hax.add i (1 : Int)
  let _wf := Hax.whileFold (t, carry, j) (fun _ => true) fun (t, carry, j) =>
    if Hax.lt j (4 : Int) then
      let s := Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index t (Hax.add i j))) (Hax.mul (Hax.castVal_w 128 (Hax.index a i)) (Hax.castVal_w 128 (Hax.index a j)))) carry
      let t := (Hax.array_update t (Hax.add i j) (Hax.castVal_w 64 s) : Array (Int))
      let carry := Hax.shr_w 128 s (64 : Int)
      let j := Hax.add j (1 : Int)
      Hax.cfContinue (t, carry, j)
    else
      Hax.cfBreak (t, carry, j)
  let (t, carry, _j) := _wf.merge
  let t := (Hax.array_update t (Hax.add i (4 : Int)) (Hax.castVal_w 64 carry) : Array (Int))
  t

/-- One step of the doubling loop of `mont_sqr_limbs`. -/
def dblBody (k : Int) (st : Array Int × Int) : Array Int × Int :=
  let t := st.1
  let bit := st.2
  let top := Hax.shr_w 64 (Hax.index t k) (63 : Int)
  let t := (Hax.array_update t k (Hax.bitor_w 64 (Hax.shl_w 64 (Hax.index t k) (1 : Int)) bit) : Array (Int))
  (t, top)

/-- One step of the diagonal loop of `mont_sqr_limbs`. -/
def diagBody (a : Array Int) (i : Int) (st : Array Int × Int) : Array Int × Int :=
  let t := st.1
  let c := st.2
  let sq := Hax.mul (Hax.castVal_w 128 (Hax.index a i)) (Hax.castVal_w 128 (Hax.index a i))
  let s := Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index t (Hax.mul (2 : Int) i))) (Hax.castVal_w 128 (Hax.castVal_w 64 sq))) c
  let t := (Hax.array_update t (Hax.mul (2 : Int) i) (Hax.castVal_w 64 s) : Array (Int))
  let s2 := Hax.add (Hax.add (Hax.castVal_w 128 (Hax.index t (Hax.add (Hax.mul (2 : Int) i) (1 : Int)))) (Hax.shr_w 128 sq (64 : Int))) (Hax.shr_w 128 s (64 : Int))
  let t := (Hax.array_update t (Hax.add (Hax.mul (2 : Int) i) (1 : Int)) (Hax.castVal_w 64 s2) : Array (Int))
  let c := Hax.shr_w 128 s2 (64 : Int)
  (t, c)

/-- `mont_sqr_limbs` is `mont_reduce` of the triangle, doubled, plus the diagonal. -/
theorem mont_sqr_limbs_eq (a : Array Int) :
    mont_sqr_limbs a = mont_reduce
      (Hax.foldRange 0 4 ((Hax.foldRange 0 8
        (Hax.foldRange 0 4 (Hax.repeat_ (0 : Int) (8 : Int)) (sqTri a), 0) dblBody).1, 0)
        (diagBody a)).1 := by
  unfold mont_sqr_limbs
  dsimp only
  rw [whileFold_count_gen (fun (s : Array Int) (j : Int) => (s, j)) 4 (sqTri a)
    _ (fun s j => rfl) 4 0 _ (by norm_num)]
  dsimp only [ControlFlow.merge]
  rw [whileFold_count_gen (fun (s : Array Int × Int) (j : Int) => (s.1, s.2, j)) 4 (diagBody a)
    _ (fun s j => rfl) 4 0 (_, 0) (by norm_num)]
  dsimp only [ControlFlow.merge]
  rw [whileFold_count_gen (fun (s : Array Int × Int) (j : Int) => (s.1, s.2, j)) 8 dblBody
    _ (fun s j => rfl) 8 0 (_, 0) (by norm_num)]

omit [PrimeirDeps] in
theorem sqTri_eq (a : Array Int) (i : Int) (t : Array Int) (m : Nat)
    (hm : Hax.add i 1 + (m : Int) = 4) :
    sqTri a i t =
      Hax.array_update (Hax.foldRange (Hax.add i 1) 4 (t, 0) (sqRow a i)).1 (Hax.add i 4)
        (Hax.castVal_w 64 (Hax.foldRange (Hax.add i 1) 4 (t, 0) (sqRow a i)).2) := by
  unfold sqTri
  dsimp only
  rw [whileFold_count_gen (fun (s : Array Int × Int) (j : Int) => (s.1, s.2, j)) 4 (sqRow a i)
    _ (fun s j => rfl) m (Hax.add i 1) (t, 0) hm]
  rfl

section Unroll

omit [PrimeirDeps]

variable {α : Type} (init : α) (f : Int → α → α)

theorem fr14 : Hax.foldRange 1 4 init f = f 3 (f 2 (f 1 init)) := by
  rw [Hax.foldRange_step _ _ _ _ (by norm_num), Hax.foldRange_step _ _ _ _ (by norm_num),
    Hax.foldRange_step _ _ _ _ (by norm_num), Hax.foldRange_stop _ _ _ _ (by norm_num)]
  norm_num

theorem fr24 : Hax.foldRange 2 4 init f = f 3 (f 2 init) := by
  rw [Hax.foldRange_step _ _ _ _ (by norm_num), Hax.foldRange_step _ _ _ _ (by norm_num),
    Hax.foldRange_stop _ _ _ _ (by norm_num)]
  norm_num

theorem fr34 : Hax.foldRange 3 4 init f = f 3 init := by
  rw [Hax.foldRange_step _ _ _ _ (by norm_num), Hax.foldRange_stop _ _ _ _ (by norm_num)]

theorem fr44 : Hax.foldRange 4 4 init f = init :=
  Hax.foldRange_stop _ _ _ _ (by norm_num)

end Unroll

omit [PrimeirDeps] in
theorem sqTri_0 (a : Array Int) (t0 t1 t2 t3 t4 t5 t6 t7 : Int) :
    sqTri a 0 #[t0, t1, t2, t3, t4, t5, t6, t7] =
      let c1 := macHi t1 (Hax.index a 0) (Hax.index a 1) 0
      let c2 := macHi t2 (Hax.index a 0) (Hax.index a 2) c1
      let c3 := macHi t3 (Hax.index a 0) (Hax.index a 3) c2
      #[t0, macLo t1 (Hax.index a 0) (Hax.index a 1) 0,
        macLo t2 (Hax.index a 0) (Hax.index a 2) c1,
        macLo t3 (Hax.index a 0) (Hax.index a 3) c2, Hax.castVal_w 64 c3, t5, t6, t7] := by
  rw [sqTri_eq a 0 _ 3 (by norm_num [Hax.add])]
  simp only [Hax.add, Int.reduceAdd, fr14, sqRow, idx8_1, idx8_2, idx8_3, upd8_1, upd8_2,
    upd8_3, upd8_4]

omit [PrimeirDeps] in
theorem sqTri_1 (a : Array Int) (t0 t1 t2 t3 t4 t5 t6 t7 : Int) :
    sqTri a 1 #[t0, t1, t2, t3, t4, t5, t6, t7] =
      let c1 := macHi t3 (Hax.index a 1) (Hax.index a 2) 0
      let c2 := macHi t4 (Hax.index a 1) (Hax.index a 3) c1
      #[t0, t1, t2, macLo t3 (Hax.index a 1) (Hax.index a 2) 0,
        macLo t4 (Hax.index a 1) (Hax.index a 3) c1, Hax.castVal_w 64 c2, t6, t7] := by
  rw [sqTri_eq a 1 _ 2 (by norm_num [Hax.add])]
  simp only [Hax.add, Int.reduceAdd, fr24, sqRow, idx8_3, idx8_4, upd8_3, upd8_4, upd8_5]

omit [PrimeirDeps] in
theorem sqTri_2 (a : Array Int) (t0 t1 t2 t3 t4 t5 t6 t7 : Int) :
    sqTri a 2 #[t0, t1, t2, t3, t4, t5, t6, t7] =
      #[t0, t1, t2, t3, t4, macLo t5 (Hax.index a 2) (Hax.index a 3) 0,
        Hax.castVal_w 64 (macHi t5 (Hax.index a 2) (Hax.index a 3) 0), t7] := by
  rw [sqTri_eq a 2 _ 1 (by norm_num [Hax.add])]
  simp only [Hax.add, Int.reduceAdd, fr34, sqRow, idx8_5, upd8_5, upd8_6]

omit [PrimeirDeps] in
theorem sqTri_3 (a : Array Int) (t0 t1 t2 t3 t4 t5 t6 t7 : Int) :
    sqTri a 3 #[t0, t1, t2, t3, t4, t5, t6, t7] =
      #[t0, t1, t2, t3, t4, t5, t6, Hax.castVal_w 64 0] := by
  rw [sqTri_eq a 3 _ 0 (by norm_num [Hax.add])]
  simp only [Hax.add, Int.reduceAdd, fr44, upd8_7]

omit [PrimeirDeps] in
theorem fr08 {α : Type} (init : α) (f : Int → α → α) :
    Hax.foldRange 0 8 init f = f 7 (f 6 (f 5 (f 4 (f 3 (f 2 (f 1 (f 0 init))))))) := by
  simp only [Hax.foldRange_step _ _ _ _ (show (0 : Int) < 8 by norm_num),
    Hax.foldRange_step _ _ _ _ (show (0 + 1 : Int) < 8 by norm_num)]
  rw [Hax.foldRange_step _ _ _ _ (by norm_num), Hax.foldRange_step _ _ _ _ (by norm_num),
    Hax.foldRange_step _ _ _ _ (by norm_num), Hax.foldRange_step _ _ _ _ (by norm_num),
    Hax.foldRange_step _ _ _ _ (by norm_num), Hax.foldRange_step _ _ _ _ (by norm_num),
    Hax.foldRange_stop _ _ _ _ (by norm_num)]
  norm_num

/-- The doubled word with the incoming bit, as the extraction computes it. -/
def dblW (x b : Int) : Int := Hax.bitor_w 64 (Hax.shl_w 64 x 1) b

omit [PrimeirDeps] in
theorem dblW_facts {x b : Int} (hx : W64 x) (hb : b = 0 ∨ b = 1) :
    W64 (dblW x b) ∧ (Hax.shr_w 64 x 63 = 0 ∨ Hax.shr_w 64 x 63 = 1) ∧
      dblW x b + 2 ^ 64 * Hax.shr_w 64 x 63 = 2 * x + b :=
  dbl_facts hx hb

section Dbl

omit [PrimeirDeps]

variable (t0 t1 t2 t3 t4 t5 t6 t7 b : Int)

theorem dblBody_0 : dblBody 0 (#[t0, t1, t2, t3, t4, t5, t6, t7], b) =
    (#[dblW t0 b, t1, t2, t3, t4, t5, t6, t7], Hax.shr_w 64 t0 63) := by
  simp only [dblBody, dblW, idx8_0, upd8_0]
theorem dblBody_1 : dblBody 1 (#[t0, t1, t2, t3, t4, t5, t6, t7], b) =
    (#[t0, dblW t1 b, t2, t3, t4, t5, t6, t7], Hax.shr_w 64 t1 63) := by
  simp only [dblBody, dblW, idx8_1, upd8_1]
theorem dblBody_2 : dblBody 2 (#[t0, t1, t2, t3, t4, t5, t6, t7], b) =
    (#[t0, t1, dblW t2 b, t3, t4, t5, t6, t7], Hax.shr_w 64 t2 63) := by
  simp only [dblBody, dblW, idx8_2, upd8_2]
theorem dblBody_3 : dblBody 3 (#[t0, t1, t2, t3, t4, t5, t6, t7], b) =
    (#[t0, t1, t2, dblW t3 b, t4, t5, t6, t7], Hax.shr_w 64 t3 63) := by
  simp only [dblBody, dblW, idx8_3, upd8_3]
theorem dblBody_4 : dblBody 4 (#[t0, t1, t2, t3, t4, t5, t6, t7], b) =
    (#[t0, t1, t2, t3, dblW t4 b, t5, t6, t7], Hax.shr_w 64 t4 63) := by
  simp only [dblBody, dblW, idx8_4, upd8_4]
theorem dblBody_5 : dblBody 5 (#[t0, t1, t2, t3, t4, t5, t6, t7], b) =
    (#[t0, t1, t2, t3, t4, dblW t5 b, t6, t7], Hax.shr_w 64 t5 63) := by
  simp only [dblBody, dblW, idx8_5, upd8_5]
theorem dblBody_6 : dblBody 6 (#[t0, t1, t2, t3, t4, t5, t6, t7], b) =
    (#[t0, t1, t2, t3, t4, t5, dblW t6 b, t7], Hax.shr_w 64 t6 63) := by
  simp only [dblBody, dblW, idx8_6, upd8_6]
theorem dblBody_7 : dblBody 7 (#[t0, t1, t2, t3, t4, t5, t6, t7], b) =
    (#[t0, t1, t2, t3, t4, t5, t6, dblW t7 b], Hax.shr_w 64 t7 63) := by
  simp only [dblBody, dblW, idx8_7, upd8_7]

end Dbl

/-- The first sum of a diagonal step: word `2i`, the low word of `q`, the carry. -/
def dgS (x q c : Int) : Int :=
  Hax.add (Hax.add (Hax.castVal_w 128 x) (Hax.castVal_w 128 (Hax.castVal_w 64 q))) c

/-- The second sum of a diagonal step: word `2i+1`, the high word of `q`, the carry
    of the first sum. -/
def dgS2 (y q s : Int) : Int :=
  Hax.add (Hax.add (Hax.castVal_w 128 y) (Hax.shr_w 128 q 64)) (Hax.shr_w 128 s 64)

/-- The square `a[i] · a[i]` as the extraction computes it. -/
def sqA (a : Array Int) (i : Int) : Int :=
  Hax.mul (Hax.castVal_w 128 (Hax.index a i)) (Hax.castVal_w 128 (Hax.index a i))

section Diag

omit [PrimeirDeps]

variable (a : Array Int) (t0 t1 t2 t3 t4 t5 t6 t7 c : Int)

theorem diagBody_0 : diagBody a 0 (#[t0, t1, t2, t3, t4, t5, t6, t7], c) =
    (#[Hax.castVal_w 64 (dgS t0 (sqA a 0) c),
      Hax.castVal_w 64 (dgS2 t1 (sqA a 0) (dgS t0 (sqA a 0) c)), t2, t3, t4, t5, t6, t7],
      Hax.shr_w 128 (dgS2 t1 (sqA a 0) (dgS t0 (sqA a 0) c)) 64) := by
  simp only [diagBody, dgS, dgS2, sqA, Hax.mul, Hax.add, Int.reduceMul, Int.reduceAdd,
    idx8_0, idx8_1, upd8_0, upd8_1]
theorem diagBody_1 : diagBody a 1 (#[t0, t1, t2, t3, t4, t5, t6, t7], c) =
    (#[t0, t1, Hax.castVal_w 64 (dgS t2 (sqA a 1) c),
      Hax.castVal_w 64 (dgS2 t3 (sqA a 1) (dgS t2 (sqA a 1) c)), t4, t5, t6, t7],
      Hax.shr_w 128 (dgS2 t3 (sqA a 1) (dgS t2 (sqA a 1) c)) 64) := by
  simp only [diagBody, dgS, dgS2, sqA, Hax.mul, Hax.add, Int.reduceMul, Int.reduceAdd,
    idx8_2, idx8_3, upd8_2, upd8_3]
theorem diagBody_2 : diagBody a 2 (#[t0, t1, t2, t3, t4, t5, t6, t7], c) =
    (#[t0, t1, t2, t3, Hax.castVal_w 64 (dgS t4 (sqA a 2) c),
      Hax.castVal_w 64 (dgS2 t5 (sqA a 2) (dgS t4 (sqA a 2) c)), t6, t7],
      Hax.shr_w 128 (dgS2 t5 (sqA a 2) (dgS t4 (sqA a 2) c)) 64) := by
  simp only [diagBody, dgS, dgS2, sqA, Hax.mul, Hax.add, Int.reduceMul, Int.reduceAdd,
    idx8_4, idx8_5, upd8_4, upd8_5]
theorem diagBody_3 : diagBody a 3 (#[t0, t1, t2, t3, t4, t5, t6, t7], c) =
    (#[t0, t1, t2, t3, t4, t5, Hax.castVal_w 64 (dgS t6 (sqA a 3) c),
      Hax.castVal_w 64 (dgS2 t7 (sqA a 3) (dgS t6 (sqA a 3) c))],
      Hax.shr_w 128 (dgS2 t7 (sqA a 3) (dgS t6 (sqA a 3) c)) 64) := by
  simp only [diagBody, dgS, dgS2, sqA, Hax.mul, Hax.add, Int.reduceMul, Int.reduceAdd,
    idx8_6, idx8_7, upd8_6, upd8_7]

end Diag

omit [PrimeirDeps] in
/-- The extracted square of an in-range word is its square. -/
theorem sqA_eq {a : Array Int} {i : Int} (h : W64 (Hax.index a i)) :
    sqA a i = Hax.index a i * Hax.index a i := by
  unfold sqA
  rw [cast128 h.1 (by linarith [h.2])]; rfl

omit [PrimeirDeps] in
/-- One diagonal step adds `u^2` and the carry at words `2i, 2i+1`. -/
theorem diag_facts {u q x y c : Int} (hq : q = u * u) (hu : W64 u) (hx : W64 x)
    (hy : W64 y) (hc : c = 0 ∨ c = 1) :
    W64 (Hax.castVal_w 64 (dgS x q c)) ∧ W64 (Hax.castVal_w 64 (dgS2 y q (dgS x q c))) ∧
      (Hax.shr_w 128 (dgS2 y q (dgS x q c)) 64 = 0 ∨
        Hax.shr_w 128 (dgS2 y q (dgS x q c)) 64 = 1) ∧
      Hax.castVal_w 64 (dgS x q c) + 2 ^ 64 * Hax.castVal_w 64 (dgS2 y q (dgS x q c))
        + 2 ^ 128 * Hax.shr_w 128 (dgS2 y q (dgS x q c)) 64
        = x + 2 ^ 64 * y + u * u + c := by
  unfold W64 at *
  have hc0 : 0 ≤ c ∧ c ≤ 1 := by rcases hc with rfl | rfl <;> norm_num
  have hq0 : 0 ≤ q := by rw [hq]; exact mul_nonneg hu.1 hu.1
  have hq1 : q < 2 ^ 64 * (2 ^ 64 - 1) := by
    rw [hq]; nlinarith [hu.1, hu.2]
  have hqd := div64_bound hq0 hq1
  have hqm : 0 ≤ q % 2 ^ 64 ∧ q % 2 ^ 64 < 2 ^ 64 :=
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  have eq := split64 q
  unfold dgS dgS2
  rw [cast64 hq0, cast128 hqm.1 (by linarith [hqm.2]), cast128 hx.1 (by linarith [hx.2]),
    cast128 hy.1 (by linarith [hy.2]), shr128_64 hq0 (by linarith)]
  simp only [Hax.add]
  generalize hS : x + q % 2 ^ 64 + c = S
  have hSb : 0 ≤ S ∧ S < 2 ^ 64 * 2 := by constructor <;> linarith
  have hSd := div64_bound hSb.1 hSb.2
  have eS := split64 S
  rw [shr128_64 hSb.1 (by linarith), cast64 hSb.1]
  generalize hS2 : y + q / 2 ^ 64 + S / 2 ^ 64 = S2
  have hS2b : 0 ≤ S2 ∧ S2 < 2 ^ 64 * 2 := by constructor <;> linarith
  have hS2d := div64_bound hS2b.1 hS2b.2
  have eS2 := split64 S2
  rw [shr128_64 hS2b.1 (by linarith), cast64 hS2b.1]
  refine ⟨⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩,
    ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩,
    bit_of_lt_two hS2d.1 hS2d.2, ?_⟩
  rw [← hq]
  linear_combination eS + (2 ^ 64 : Int) * eS2 - hS - (2 ^ 64 : Int) * hS2 + eq

set_option exponentiation.threshold 1024 in
/-- The Montgomery squaring of `mont_sqr_limbs` on canonical limbs: canonical limbs
    `r` with `r · 2^256 = a · a + M · p`. -/
theorem mont_sqr_limbs_spec {a0 a1 a2 a3 : Int} (ha0 : W64 a0) (ha1 : W64 a1) (ha2 : W64 a2)
    (ha3 : W64 a3) (ha : val4 a0 a1 a2 a3 < pZ) :
    ∃ r0 r1 r2 r3 M : Int,
      mont_sqr_limbs #[a0, a1, a2, a3] = #[r0, r1, r2, r3] ∧
      W64 r0 ∧ W64 r1 ∧ W64 r2 ∧ W64 r3 ∧ val4 r0 r1 r2 r3 < pZ ∧
      val4 r0 r1 r2 r3 * 2 ^ 256 = val4 a0 a1 a2 a3 * val4 a0 a1 a2 a3 + M * pZ := by
  have hz : W64 0 := by norm_num [W64]
  rw [mont_sqr_limbs_eq, foldRange_four _ (sqTri _),
    show Hax.repeat_ (0 : Int) (8 : Int) = #[0, 0, 0, 0, 0, 0, 0, 0] from rfl, sqTri_0]
  dsimp only
  simp only [idx4_0, idx4_1, idx4_2, idx4_3]
  -- row 0
  obtain ⟨l1, k1, e1⟩ := mac_facts hz ha0 ha1 hz
  obtain ⟨l2, k2, e2⟩ := mac_facts hz ha0 ha2 k1
  obtain ⟨l3, k3, e3⟩ := mac_facts hz ha0 ha3 k2
  rw [castVal_of_lt (w := 64) k3.1 k3.2]
  generalize macLo 0 a0 a3 (macHi 0 a0 a2 (macHi 0 a0 a1 0)) = y3 at *
  generalize macHi 0 a0 a3 (macHi 0 a0 a2 (macHi 0 a0 a1 0)) = c3 at *
  generalize macLo 0 a0 a2 (macHi 0 a0 a1 0) = y2 at *
  generalize macHi 0 a0 a2 (macHi 0 a0 a1 0) = c2 at *
  generalize macLo 0 a0 a1 0 = y1 at *
  generalize macHi 0 a0 a1 0 = c1 at *
  -- row 1
  rw [sqTri_1]
  dsimp only
  simp only [idx4_1, idx4_2, idx4_3]
  obtain ⟨l4, k4, e4⟩ := mac_facts l3 ha1 ha2 hz
  obtain ⟨l5, k5, e5⟩ := mac_facts k3 ha1 ha3 k4
  rw [castVal_of_lt (w := 64) k5.1 k5.2]
  generalize macLo c3 a1 a3 (macHi y3 a1 a2 0) = y4 at *
  generalize macHi c3 a1 a3 (macHi y3 a1 a2 0) = c5 at *
  generalize macLo y3 a1 a2 0 = y3' at *
  generalize macHi y3 a1 a2 0 = c4 at *
  -- row 2 and row 3
  rw [sqTri_2]
  simp only [idx4_2, idx4_3]
  obtain ⟨l6, k6, e6⟩ := mac_facts k5 ha2 ha3 hz
  rw [castVal_of_lt (w := 64) k6.1 k6.2, sqTri_3, castVal_of_lt (w := 64) le_rfl (by norm_num)]
  generalize macLo c5 a2 a3 0 = y5 at *
  generalize macHi c5 a2 a3 0 = c6 at *
  -- doubling
  rw [fr08, dblBody_0]
  obtain ⟨g0, h1, f0⟩ := dblW_facts hz (Or.inl rfl)
  generalize dblW 0 0 = d0 at *
  generalize Hax.shr_w 64 0 63 = b1 at *
  rw [dblBody_1]
  obtain ⟨g1, h2, f1⟩ := dblW_facts l1 h1
  generalize dblW y1 b1 = d1 at *
  generalize Hax.shr_w 64 y1 63 = b2 at *
  rw [dblBody_2]
  obtain ⟨g2, h3, f2⟩ := dblW_facts l2 h2
  generalize dblW y2 b2 = d2 at *
  generalize Hax.shr_w 64 y2 63 = b3 at *
  rw [dblBody_3]
  obtain ⟨g3, h4, f3⟩ := dblW_facts l4 h3
  generalize dblW y3' b3 = d3 at *
  generalize Hax.shr_w 64 y3' 63 = b4 at *
  rw [dblBody_4]
  obtain ⟨g4, h5, f4⟩ := dblW_facts l5 h4
  generalize dblW y4 b4 = d4 at *
  generalize Hax.shr_w 64 y4 63 = b5 at *
  rw [dblBody_5]
  obtain ⟨g5, h6, f5⟩ := dblW_facts l6 h5
  generalize dblW y5 b5 = d5 at *
  generalize Hax.shr_w 64 y5 63 = b6 at *
  rw [dblBody_6]
  obtain ⟨g6, h7, f6⟩ := dblW_facts k6 h6
  generalize dblW c6 b6 = d6 at *
  generalize Hax.shr_w 64 c6 63 = b7 at *
  rw [dblBody_7]
  obtain ⟨g7, h8, f7⟩ := dblW_facts hz h7
  generalize dblW 0 b7 = d7 at *
  generalize Hax.shr_w 64 0 63 = b8 at *
  -- diagonal
  simp only []
  rw [foldRange_four _ (diagBody _), diagBody_0]
  have hs0 : sqA #[a0, a1, a2, a3] 0 = a0 * a0 := sqA_eq (by rw [idx4_0]; exact ha0)
  obtain ⟨p0, p1, pc1, pe1⟩ := diag_facts hs0 ha0 g0 g1 (Or.inl rfl)
  generalize sqA #[a0, a1, a2, a3] 0 = q0 at *
  generalize dgS2 d1 q0 (dgS d0 q0 0) = S2 at *
  generalize dgS d0 q0 0 = S1 at *
  generalize Hax.castVal_w 64 S1 = f0' at *
  generalize Hax.castVal_w 64 S2 = f1' at *
  generalize Hax.shr_w 128 S2 64 = w1 at *
  rw [diagBody_1]
  have hs1 : sqA #[a0, a1, a2, a3] 1 = a1 * a1 := sqA_eq (by rw [idx4_1]; exact ha1)
  obtain ⟨p2, p3, pc2, pe2⟩ := diag_facts hs1 ha1 g2 g3 pc1
  generalize sqA #[a0, a1, a2, a3] 1 = q1 at *
  generalize dgS2 d3 q1 (dgS d2 q1 w1) = S4 at *
  generalize dgS d2 q1 w1 = S3 at *
  generalize Hax.castVal_w 64 S3 = f2' at *
  generalize Hax.castVal_w 64 S4 = f3' at *
  generalize Hax.shr_w 128 S4 64 = w2 at *
  rw [diagBody_2]
  have hs2 : sqA #[a0, a1, a2, a3] 2 = a2 * a2 := sqA_eq (by rw [idx4_2]; exact ha2)
  obtain ⟨p4, p5, pc3, pe3⟩ := diag_facts hs2 ha2 g4 g5 pc2
  generalize sqA #[a0, a1, a2, a3] 2 = q2 at *
  generalize dgS2 d5 q2 (dgS d4 q2 w2) = S6 at *
  generalize dgS d4 q2 w2 = S5 at *
  generalize Hax.castVal_w 64 S5 = f4' at *
  generalize Hax.castVal_w 64 S6 = f5' at *
  generalize Hax.shr_w 128 S6 64 = w3 at *
  rw [diagBody_3]
  have hs3 : sqA #[a0, a1, a2, a3] 3 = a3 * a3 := sqA_eq (by rw [idx4_3]; exact ha3)
  obtain ⟨p6, p7, pc4, pe4⟩ := diag_facts hs3 ha3 g6 g7 pc3
  generalize sqA #[a0, a1, a2, a3] 3 = q3 at *
  generalize dgS2 d7 q3 (dgS d6 q3 w3) = S8 at *
  generalize dgS d6 q3 w3 = S7 at *
  generalize Hax.castVal_w 64 S7 = f6' at *
  generalize Hax.castVal_w 64 S8 = f7' at *
  generalize Hax.shr_w 128 S8 64 = w4 at *
  -- the product
  have hb8 : b8 = 0 := by
    rcases h7 with rfl | rfl <;> rcases h8 with rfl | rfl <;> unfold W64 at g7 <;> linarith
  have hA0 := val4_nonneg ha0 ha1 ha2 ha3
  have hsum : val4 f0' f1' f2' f3' + 2 ^ 256 * val4 f4' f5' f6' f7' + 2 ^ 512 * w4
      = val4 a0 a1 a2 a3 * val4 a0 a1 a2 a3 := by
    unfold val4
    linear_combination pe1 + (2 ^ 128 : Int) * pe2 + (2 ^ 256 : Int) * pe3
      + (2 ^ 384 : Int) * pe4 + f0 + (2 ^ 64 : Int) * f1 + (2 ^ 128 : Int) * f2
      + (2 ^ 192 : Int) * f3 + (2 ^ 256 : Int) * f4 + (2 ^ 320 : Int) * f5
      + (2 ^ 384 : Int) * f6 + (2 ^ 448 : Int) * f7 - (2 ^ 512 : Int) * hb8
      + 2 * ((2 ^ 64 : Int) * e1 + (2 ^ 128 : Int) * e2 + (2 ^ 192 : Int) * e3
        + (2 ^ 192 : Int) * e4 + (2 ^ 256 : Int) * e5 + (2 ^ 320 : Int) * e6)
  have hpz : pZ < 2 ^ 256 := by unfold pZ; norm_num
  have hle : val4 a0 a1 a2 a3 * val4 a0 a1 a2 a3 ≤ val4 a0 a1 a2 a3 * 2 ^ 256 :=
    mul_le_mul_of_nonneg_left (by linarith) hA0
  have hlt : val4 a0 a1 a2 a3 * 2 ^ 256 < pZ * 2 ^ 256 :=
    mul_lt_mul_of_pos_right ha (by norm_num)
  have hT0 : 0 ≤ val4 f0' f1' f2' f3' + 2 ^ 256 * val4 f4' f5' f6' f7' := by
    have := val4_nonneg p0 p1 p2 p3; have := val4_nonneg p4 p5 p6 p7; positivity
  have hw4 : w4 = 0 := by
    rcases pc4 with h | h
    · exact h
    · exfalso; rw [h] at hsum; linarith only [hsum, hT0, hle, hlt, hpz]
  rw [hw4, mul_zero, add_zero] at hsum
  obtain ⟨r0, r1, r2, r3, M, he, hr0, hr1, hr2, hr3, hR, hv⟩ :=
    mont_reduce_spec p0 p1 p2 p3 p4 p5 p6 p7 (by rw [hsum]; linarith only [hle, hlt])
  exact ⟨r0, r1, r2, r3, M, he, hr0, hr1, hr2, hr3, hR, by rw [hv, hsum]⟩

/-! ## Squaring, repeated squaring, the addition chain and the inverse -/

/-- `mont_sqr_limbs` computes the field square of the Montgomery value. -/
theorem mont_sqr_limbs_val {a : Array Int} (ha : Canon a) :
    Canon (mont_sqr_limbs a) ∧ montVal (mont_sqr_limbs a) = montVal a ^ 2 := by
  obtain ⟨a0, a1, a2, a3, rfl, ha0, ha1, ha2, ha3, hA⟩ := ha
  obtain ⟨r0, r1, r2, r3, M, he, hr0, hr1, hr2, hr3, hR, hv⟩ :=
    mont_sqr_limbs_spec ha0 ha1 ha2 ha3 hA
  rw [he]
  refine ⟨⟨r0, r1, r2, r3, rfl, hr0, hr1, hr2, hr3, hR⟩, ?_⟩
  have hc : ((val4 r0 r1 r2 r3 : ℤ) : Fp256) * (2 : Fp256) ^ 256
      = ((val4 a0 a1 a2 a3 : ℤ) : Fp256) * ((val4 a0 a1 a2 a3 : ℤ) : Fp256) := by
    have := congrArg (fun x : ℤ => (x : Fp256)) hv
    simp only [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_ofNat, intCast_pZ,
      mul_zero, add_zero] at this
    exact this
  simp only [montVal, limbVal_lit]
  have hR0 := two_pow_ne_zero
  have hr : ((val4 r0 r1 r2 r3 : ℤ) : Fp256) = ((val4 a0 a1 a2 a3 : ℤ) : Fp256)
      * ((val4 a0 a1 a2 a3 : ℤ) : Fp256) * ((2 : Fp256) ^ 256)⁻¹ := by
    rw [← hc, mul_assoc, mul_inv_cancel₀ hR0, mul_one]
  rw [hr]; ring

/-- `sqr_n a n` is `n` Montgomery squarings: the value `x ^ 2 ^ n`. -/
theorem sqr_n_val {a : Array Int} (ha : Canon a) (n : Nat) :
    Canon (sqr_n a n) ∧ montVal (sqr_n a n) = montVal a ^ 2 ^ n := by
  unfold sqr_n
  dsimp only
  rw [whileFold_count_gen (fun (s : Array Int) (j : Int) => (s, j)) (n : Int)
    (fun _ r => mont_sqr_limbs r) _ (fun s j => rfl) n 0 a (by simp)]
  dsimp only [ControlFlow.merge]
  have key := Hax.foldRange_induct (P := fun (i : Int) r => Canon r ∧
      montVal r = montVal a ^ 2 ^ i.toNat) (lo := 0) (hi := (n : Int))
    (f := fun _ r => mont_sqr_limbs r) (init := a) (by positivity) ⟨ha, by simp⟩ (by
      intro i r hi _ ⟨hc, hv⟩
      obtain ⟨hc', hv'⟩ := mont_sqr_limbs_val hc
      refine ⟨hc', ?_⟩
      rw [hv', hv, show (i + 1).toNat = i.toNat + 1 by omega, pow_succ 2, pow_mul])
  simpa using key

/-- The step of the addition chain: `n` squarings of `a`, then a multiplication
    by `b`. -/
theorem sq_mul_val {a b : Array Int} (ha : Canon a) (hb : Canon b) (n : Nat) :
    Canon (mont_mul_limbs (sqr_n a n) b) ∧
      montVal (mont_mul_limbs (sqr_n a n) b) = montVal a ^ 2 ^ n * montVal b := by
  obtain ⟨h1, h2⟩ := sqr_n_val ha n
  obtain ⟨h3, h4⟩ := mont_mul_limbs_val h1 hb
  exact ⟨h3, by rw [h4, h2]⟩

/-- `pow_c1_limbs` computes the power `x ^ ((p - 3) / 4)` of the Montgomery
    value. -/
theorem pow_c1_limbs_val {a : Array Int} (ha : Canon a) :
    Canon (pow_c1_limbs a) ∧ montVal (pow_c1_limbs a) = montVal a ^ ((P256 - 3) / 4) := by
  unfold pow_c1_limbs
  dsimp only
  obtain ⟨C2, V2⟩ := sq_mul_val ha ha 1
  obtain ⟨C4, V4⟩ := sq_mul_val C2 C2 2
  obtain ⟨C8, V8⟩ := sq_mul_val C4 C4 4
  obtain ⟨C16, V16⟩ := sq_mul_val C8 C8 8
  obtain ⟨C32, V32⟩ := sq_mul_val C16 C16 16
  obtain ⟨D1, W1⟩ := sq_mul_val C32 ha 32
  obtain ⟨D2, W2⟩ := sq_mul_val D1 C32 128
  obtain ⟨D3, W3⟩ := sq_mul_val D2 C32 32
  obtain ⟨D4, W4⟩ := sq_mul_val D3 C16 16
  obtain ⟨D5, W5⟩ := sq_mul_val D4 C8 8
  obtain ⟨D6, W6⟩ := sq_mul_val D5 C4 4
  obtain ⟨D7, W7⟩ := sq_mul_val D6 C2 2
  simp only [Nat.cast_ofNat, Nat.cast_one] at *
  refine ⟨D7, ?_⟩
  rw [W7, W6, W5, W4, W3, W2, W1, V32, V16, V8, V4, V2]
  norm_num [P256]
  ring

omit [PrimeirDeps] in
/-- `Field::inv` of `Fp256Mont` is `pow_c1_limbs`, two squarings and a
    multiplication by the argument. -/
theorem Field_inv_eq (a : Array Int) :
    Field_inv a = mont_mul_limbs (sqr_n (pow_c1_limbs a) 2) a := rfl

/-- `Field::inv` returns canonical limbs, and the field inverse at a nonzero
    Montgomery value. -/
theorem Field_inv_val {a : Array Int} (ha : Canon a) :
    Canon (Field_inv a) ∧ (montVal a ≠ 0 → montVal (Field_inv a) = (montVal a)⁻¹) := by
  obtain ⟨C, V⟩ := pow_c1_limbs_val ha
  obtain ⟨C', V'⟩ := sq_mul_val C ha 2
  simp only [Nat.cast_ofNat] at C' V'
  rw [Field_inv_eq]
  refine ⟨C', fun hx => ?_⟩
  rw [V', V, ← pow_mul]
  have hf := ZMod.pow_card_sub_one_eq_one hx
  have he : (P256 - 3) / 4 * 2 ^ 2 + 1 + 1 = P256 - 1 := by norm_num [P256]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, ← pow_succ, he, hf]

omit [PrimeirDeps] in
theorem montVal_eq_zero_iff {a : Array Int} (ha : Canon a) : montVal a = 0 ↔ limbVal a = 0 := by
  obtain ⟨x0, x1, x2, x3, rfl, h0, h1, h2, h3, hx⟩ := ha
  have hn := val4_nonneg h0 h1 h2 h3
  simp only [montVal, limbVal_lit, mul_eq_zero, inv_eq_zero, two_pow_ne_zero, or_false]
  constructor
  · intro h
    rw [pZ_eq] at hx
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    obtain ⟨k, hk⟩ := this
    rcases lt_trichotomy k 0 with hk0 | rfl | hk0
    · nlinarith
    · simpa using hk
    · nlinarith
  · intro h; rw [h]; simp

omit [PrimeirDeps] in
theorem bitxor_zero {x : Int} (hx : W64 x) : Hax.bitxor_w 64 x 0 = x := by
  simp [Hax.bitxor_w, Int.toNat_of_nonneg hx.1]
  exact Int.emod_eq_of_lt hx.1 hx.2

omit [PrimeirDeps] in
theorem bitor_W {u v : Int} (hu : W64 u) (hv : W64 v) :
    W64 (Hax.bitor_w 64 u v) ∧ (Hax.bitor_w 64 u v = 0 ↔ u = 0 ∧ v = 0) := by
  have hu' := toNat_mod64 hu
  have hv' := toNat_mod64 hv
  have hul : u.toNat < 2 ^ 64 := by unfold W64 at hu; omega
  have hvl : v.toNat < 2 ^ 64 := by unfold W64 at hv; omega
  simp only [Hax.bitor_w, hu', hv']
  refine ⟨⟨by positivity, ?_⟩, ?_⟩
  · have := Nat.or_lt_two_pow hul hvl
    exact_mod_cast this
  · rw [show ((u.toNat ||| v.toNat : ℕ) : ℤ) = 0 ↔ (u.toNat ||| v.toNat) = 0 by
      exact_mod_cast Iff.rfl, Nat.or_eq_zero_iff]
    unfold W64 at hu hv; omega

omit [PrimeirDeps] in
theorem top_bit {d : Int} (hd : W64 d) :
    Hax.shr_w 64 (Hax.bitor_w 64 d (Hax.wrapping_neg_w 64 d)) 63 = if d = 0 then 0 else 1 := by
  split_ifs with h0
  · subst h0; simp [Hax.wrapping_neg_w, Hax.mod2w, Hax.bitor_w, Hax.shr_w]
  · have hn : Hax.wrapping_neg_w 64 d = 2 ^ 64 - d := by
      simp only [Hax.wrapping_neg_w]
      unfold W64 at hd
      push_cast
      exact castVal_of_lt (w := 64) (by omega) (by omega)
    have hN : W64 (2 ^ 64 - d) := by unfold W64 at *; omega
    obtain ⟨hW, -⟩ := bitor_W hd hN
    rw [hn]
    have hs := shr_of_lt (w := 64) 63 hW.1 hW.2
    rw [show ((63 : ℕ) : ℤ) = 63 from rfl] at hs
    rw [hs]
    simp only [Hax.bitor_w, toNat_mod64 hd, toNat_mod64 hN]
    have hD : d.toNat < 2 ^ 64 := by unfold W64 at hd; omega
    have hsum : d.toNat + (2 ^ 64 - d).toNat = 2 ^ 64 := by unfold W64 at hd; omega
    have hpos : 0 < d.toNat := by unfold W64 at hd; omega
    have hor : (d.toNat ||| (2 ^ 64 - d).toNat) / 2 ^ 63
        = d.toNat / 2 ^ 63 ||| (2 ^ 64 - d).toNat / 2 ^ 63 := by
      rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_or_distrib, Nat.shiftRight_eq_div_pow,
        Nat.shiftRight_eq_div_pow]
    have key : ((d.toNat ||| (2 ^ 64 - d).toNat : ℕ) : ℤ) / 2 ^ 63
        = (((d.toNat ||| (2 ^ 64 - d).toNat) / 2 ^ 63 : ℕ) : ℤ) := by push_cast; rfl
    rw [key, hor]
    have h1 : d.toNat / 2 ^ 63 = 0 ∨ d.toNat / 2 ^ 63 = 1 := by omega
    have h2 : (2 ^ 64 - d).toNat / 2 ^ 63 = 0 ∨ (2 ^ 64 - d).toNat / 2 ^ 63 = 1 := by omega
    have h3 : ¬ (d.toNat / 2 ^ 63 = 0 ∧ (2 ^ 64 - d).toNat / 2 ^ 63 = 0) := by omega
    generalize d.toNat / 2 ^ 63 = u at h1 h3 ⊢
    generalize (2 ^ 64 - d).toNat / 2 ^ 63 = v at h2 h3 ⊢
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact absurd ⟨rfl, rfl⟩ h3
    all_goals rfl

omit [PrimeirDeps] in
/-- `CtField::ct_eq` of `Fp256Mont`: the or of the limb differences, then
    `1 - ((diff | diff.wrapping_neg()) >> 63)`. -/
theorem CtField_ct_eq_eq (x y : Array Int) :
    CtField_ct_eq x y =
      let diff := Hax.foldRange 0 4 (0 : Int) fun i diff =>
        Hax.bitor_w 64 diff (Hax.bitxor_w 64 (Hax.index x i) (Hax.index y i))
      Hax.sub 1 (Hax.shr_w 64 (Hax.bitor_w 64 diff (Hax.wrapping_neg_w 64 diff)) 63) := by
  unfold CtField_ct_eq «Fp256Mont.0»
  dsimp only
  rw [whileFold_count_gen (fun (s : Int) (j : Int) => (s, j)) 4
    (fun i diff => Hax.bitor_w 64 diff (Hax.bitxor_w 64 (Hax.index x i) (Hax.index y i)))
    _ (fun s j => rfl) 4 0 0 (by norm_num)]
  rfl

omit [PrimeirDeps] in
/-- `Field::ZERO` of `Fp256Mont` is the zero limbs. -/
theorem Field_ZERO_eq : Field_ZERO = #[0, 0, 0, 0] := rfl

omit [PrimeirDeps] in
/-- `CtField::is_zero` of `Fp256Mont` is the indicator of the Montgomery value `0`. -/
theorem CtField_is_zero_eq {a : Array Int} (ha : Canon a) :
    CtField_is_zero a = if montVal a = 0 then 1 else 0 := by
  simp only [montVal_eq_zero_iff ha]
  obtain ⟨x0, x1, x2, x3, rfl, h0, h1, h2, h3, -⟩ := ha
  rw [CtField_is_zero, CtField_ct_eq_eq, Field_ZERO_eq]
  dsimp only
  rw [foldRange_four]
  simp only [idx4_0, idx4_1, idx4_2, idx4_3, bitxor_zero h0, bitxor_zero h1, bitxor_zero h2,
    bitxor_zero h3, limbVal_lit]
  have hz : W64 0 := by norm_num [W64]
  obtain ⟨w1, z1⟩ := bitor_W hz h0
  obtain ⟨w2, z2⟩ := bitor_W w1 h1
  obtain ⟨w3, z3⟩ := bitor_W w2 h2
  obtain ⟨w4, z4⟩ := bitor_W w3 h3
  rw [top_bit w4]
  have hv : val4 x0 x1 x2 x3 = 0 ↔ x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
    unfold val4; unfold W64 at h0 h1 h2 h3; omega
  by_cases hc : x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0
  · rw [ite_eq_left (z4.mpr ⟨z3.mpr ⟨z2.mpr ⟨z1.mpr ⟨rfl, hc.1⟩, hc.2.1⟩, hc.2.2.1⟩, hc.2.2.2⟩)]
    simp [hv.mpr hc, Hax.sub]
  · rw [ite_eq_right (by tauto)]
    have h : ¬ val4 x0 x1 x2 x3 = 0 := fun h => hc (hv.mp h)
    simp [h, Hax.sub]

/-- `to_canonical_limbs` returns canonical limbs of the integer `(montVal a).val`:
    their integer, cast to the field, is the Montgomery value. -/
theorem to_canonical_limbs_val {a : Array Int} (ha : Canon a) :
    ∃ r0 r1 r2 r3 : Int, Fp256Mont_to_canonical_limbs a = #[r0, r1, r2, r3] ∧
      W64 r0 ∧ W64 r1 ∧ W64 r2 ∧ W64 r3 ∧ val4 r0 r1 r2 r3 < pZ ∧
      ((val4 r0 r1 r2 r3 : ℤ) : Fp256) = montVal a := by
  obtain ⟨a0, a1, a2, a3, rfl, ha0, ha1, ha2, ha3, hA⟩ := ha
  have h1 : W64 1 := by norm_num [W64]
  have hz : W64 0 := by norm_num [W64]
  obtain ⟨r0, r1, r2, r3, M, he, hr0, hr1, hr2, hr3, hR, hv⟩ :=
    mont_mul_limbs_spec ha0 ha1 ha2 ha3 h1 hz hz hz hA
  refine ⟨r0, r1, r2, r3, he, hr0, hr1, hr2, hr3, hR, ?_⟩
  have hc : ((val4 r0 r1 r2 r3 : ℤ) : Fp256) * (2 : Fp256) ^ 256
      = ((val4 a0 a1 a2 a3 : ℤ) : Fp256) := by
    have := congrArg (fun x : ℤ => (x : Fp256)) hv
    have h1' : val4 1 0 0 0 = 1 := by norm_num [val4]
    simp only [h1', mul_one, Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_ofNat,
      intCast_pZ, mul_zero, add_zero] at this
    exact this
  simp only [montVal, limbVal_lit]
  rw [← hc, mul_assoc, mul_inv_cancel₀ two_pow_ne_zero, mul_one]

/-! ## The field model of the emitted instances -/

open CatCrypt.Crypto.Bridges.Transfer.HaxInt (BoundedFieldModel)

/-- The `Field` and `CtField` instances of `Fp256Mont` in the extraction as a field
    model of `Fp256`: canonical limbs valued by `montVal`. -/
noncomputable def fp256MontCtModel : CtFieldModel Fp256Mont_T Fp256 where
  val := montVal
  Valid := Canon
  zero_eq := montVal_zero
  zero_valid := canon_zero
  one_eq := montVal_R
  one_valid := canon_R
  add_eq _ _ ha hb := (add_mod_val ha hb).2
  add_valid _ _ ha hb := (add_mod_val ha hb).1
  sub_eq _ _ ha hb := (sub_mod_val ha hb).2
  sub_valid _ _ ha hb := (sub_mod_val ha hb).1
  mul_eq _ _ ha hb := (mont_mul_limbs_val ha hb).2
  mul_valid _ _ ha hb := (mont_mul_limbs_val ha hb).1
  neg_eq _ ha := (neg_val ha).2
  neg_valid _ ha := (neg_val ha).1
  square_eq _ ha := (mont_sqr_limbs_val ha).2
  square_valid _ ha := (mont_sqr_limbs_val ha).1
  double_eq _ ha := ((add_mod_val ha ha).2).trans (two_mul _).symm
  double_valid _ ha := (add_mod_val ha ha).1
  inv_eq _ ha h := (Field_inv_val ha).2 h
  inv_valid _ ha := (Field_inv_val ha).1
  ct_select_eq c a b hc ha hb := by
    rw [show Primeir.CtField.ct_select c a b = select_limbs (mask_of c) a b from rfl,
      ct_select_val hc ha hb]
    split_ifs <;> rfl
  ct_select_valid c a b hc ha hb := by
    rw [show Primeir.CtField.ct_select c a b = select_limbs (mask_of c) a b from rfl,
      ct_select_val hc ha hb]
    split_ifs <;> assumption
  is_zero_eq _ ha := CtField_is_zero_eq ha

/-- The Montgomery P-256 field of `fp256_mont.rs` as a bounded field model: the
    `BoundedFieldModel` of `fp256MontCtModel`, whose operations are the methods of
    the `Field` and `CtField` instances of `Fp256Mont`. -/
noncomputable def fp256MontModel : BoundedFieldModel Fp256 :=
  fp256MontCtModel.toBounded

end CatCrypt.Crypto.PrimeIR.Fp256Mont
