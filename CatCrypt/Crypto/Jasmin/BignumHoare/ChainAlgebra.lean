/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.BignumExec
public import CatCrypt.Crypto.Jasmin.Hoare
public import CatCrypt.Crypto.Jasmin.S2NBignumSSA
public import CatCrypt.Crypto.Jasmin.BignumHoare.Sqr4Algebra

@[expose] public section

set_option autoImplicit false

/-!
# Chain-algebra keystones for the bignum-port Hoare triples

The 4-limb SBB / ADC chain identities, formulated as pure BitVec / Nat
equations, plus the algoNat-on-`BitVec 256` wrappers and the embedded
phase Hoare triples for `double_p25519` / `sub_p25519`. Discharged
via `bv_decide`.

## Why a separate module?

These twelve theorems use `bv_decide` on 256-bit chains, which compiles
each goal to a SAT instance. Per-declaration RAM peaks ≈ 8 GiB; co-located
with the rest of `BignumHoare` they pushed cumulative elaboration past
the 14 GiB host RAM ceiling. Splitting them into a dependent module lets
each elaborate once in its own process; downstream files (`BignumHoare`,
the orphan companion files, `ModP25519Final`) import the cached `.olean`.

This file extends the same `CatCrypt.Crypto.Jasmin.BignumHoare` namespace
as its parent — declarations are addressable as `BignumHoare.sbb_chain_algoNat`
etc., the same path they had pre-split.
-/

namespace CatCrypt.Crypto.Jasmin.BignumHoare

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Hoare

/-! ### 256-bit algebraic helper — Phase 3 closure

The 4-limb SBB-chain + mask-cmov pattern computes algoNat. State this
as a clean BitVec 64 identity; bv_decide handles it.

Below we use a stripped form: given 4 input limbs and the SBB borrow
flags, the output limb equals the mask-cmov result. The full chain
identity factors through this. -/

/-- Per-limb identity: `mask AND a OR (¬mask) AND t = if borrow then a else t`. -/
theorem mask_cmov_per_limb (a t : BitVec 64) (borrow : BitVec 64)
    (h_borrow : borrow = 0 ∨ borrow = 1) :
    (-borrow &&& a) ||| (((-borrow) ^^^ (BitVec.allOnes 64)) &&& t)
      = if borrow = 1 then a else t := by
  rcases h_borrow with hb | hb <;> subst hb <;> bv_decide

/-- The 4-limb SBB chain on (a, p25519) at the BitVec 256 level:
    output as a 256-bit value equals `a` if `a < p`, else `a - p`. -/
theorem sbb_chain_bv256
    (a0 a1 a2 a3 : BitVec 64) :
    let p0 : BitVec 64 := 0xFFFFFFFFFFFFFFED
    let pmid : BitVec 64 := 0xFFFFFFFFFFFFFFFF
    let p3 : BitVec 64 := 0x7FFFFFFFFFFFFFFF
    let cf0 := if a0.ult p0 then (1 : BitVec 64) else 0
    let t0 := a0 - p0
    let cf1 := (if a1.ult pmid then (1 : BitVec 64) else 0) |||
               (if (a1 - pmid).ult (cf0 &&& 1) then 1 else 0)
    let t1 := a1 - pmid - (cf0 &&& 1)
    let cf2 := (if a2.ult pmid then (1 : BitVec 64) else 0) |||
               (if (a2 - pmid).ult (cf1 &&& 1) then 1 else 0)
    let t2 := a2 - pmid - (cf1 &&& 1)
    let cf3 := (if a3.ult p3 then (1 : BitVec 64) else 0) |||
               (if (a3 - p3).ult (cf2 &&& 1) then 1 else 0)
    let t3 := a3 - p3 - (cf2 &&& 1)
    let mask : BitVec 64 := -(cf3 &&& 1)
    let nmask : BitVec 64 := mask ^^^ (BitVec.allOnes 64)
    let a256 : BitVec 256 := a3 ++ a2 ++ a1 ++ a0
    let p256 : BitVec 256 := 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED
    let o0 := (mask &&& a0) ||| (nmask &&& t0)
    let o1 := (mask &&& a1) ||| (nmask &&& t1)
    let o2 := (mask &&& a2) ||| (nmask &&& t2)
    let o3 := (mask &&& a3) ||| (nmask &&& t3)
    let o256 : BitVec 256 := o3 ++ o2 ++ o1 ++ o0
    o256 = if a256.ult p256 then a256 else a256 - p256 := by
  bv_decide

/-! ### Wrapper: produces algoNat-of-Nat-decoding given the BitVec 256
    chain result. -/

theorem sbb_chain_algoNat
    (a0 a1 a2 a3 : BitVec 64) :
    let p0 : BitVec 64 := 0xFFFFFFFFFFFFFFED
    let pmid : BitVec 64 := 0xFFFFFFFFFFFFFFFF
    let p3 : BitVec 64 := 0x7FFFFFFFFFFFFFFF
    let cf0 := if a0.ult p0 then (1 : BitVec 64) else 0
    let t0 := a0 - p0
    let cf1 := (if a1.ult pmid then (1 : BitVec 64) else 0) |||
               (if (a1 - pmid).ult (cf0 &&& 1) then 1 else 0)
    let t1 := a1 - pmid - (cf0 &&& 1)
    let cf2 := (if a2.ult pmid then (1 : BitVec 64) else 0) |||
               (if (a2 - pmid).ult (cf1 &&& 1) then 1 else 0)
    let t2 := a2 - pmid - (cf1 &&& 1)
    let cf3 := (if a3.ult p3 then (1 : BitVec 64) else 0) |||
               (if (a3 - p3).ult (cf2 &&& 1) then 1 else 0)
    let t3 := a3 - p3 - (cf2 &&& 1)
    let mask : BitVec 64 := -(cf3 &&& 1)
    let nmask : BitVec 64 := mask ^^^ (BitVec.allOnes 64)
    let o0 := (mask &&& a0) ||| (nmask &&& t0)
    let o1 := (mask &&& a1) ||| (nmask &&& t1)
    let o2 := (mask &&& a2) ||| (nmask &&& t2)
    let o3 := (mask &&& a3) ||| (nmask &&& t3)
    o0.toNat + o1.toNat * 2^64 + o2.toNat * 2^128 + o3.toNat * 2^192 =
      S2NBignumSSA.BignumModP25519_4.algoNat
        (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192) := by
  intro p0 pmid p3 cf0 t0 cf1 t1 cf2 t2 cf3 t3 mask nmask o0 o1 o2 o3
  rw [← toNat_concat_4limbs o0 o1 o2 o3, ← toNat_concat_4limbs a0 a1 a2 a3]
  rw [sbb_chain_bv256 a0 a1 a2 a3]
  unfold S2NBignumSSA.BignumModP25519_4.algoNat
  set a256 : BitVec 256 := a3 ++ a2 ++ a1 ++ a0
  set p256 : BitVec 256 := 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED
  have hp256_toNat : p256.toNat = 2^255 - 19 := by decide
  by_cases h : a256.ult p256
  · rw [if_pos h]
    have : ¬ a256.toNat ≥ 2^255 - 19 := by
      rw [BitVec.ult_iff_lt, BitVec.lt_def, hp256_toNat] at h
      omega
    rw [if_neg this]
  · rw [if_neg h]
    rw [BitVec.ult_iff_lt] at h
    rw [BitVec.lt_def] at h
    have h_le : p256 ≤ a256 := by rw [BitVec.le_def]; omega
    have h_ge : a256.toNat ≥ 2^255 - 19 := by
      rw [hp256_toNat] at *
      omega
    rw [if_pos h_ge]
    rw [BitVec.toNat_sub_of_le h_le, hp256_toNat]

/-! ### Phase 4 foundational helper — 4-limb ADC chain = BitVec 256 add

Used across all ports that have an ADC chain (double, sub's add-back,
montmul's accumulator, etc.). Proves the 4-limb add-with-carry chain
implements `a + b` at the BitVec 256 level. -/

theorem adc_chain_eq_add_bv256
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    let cy0 := if (a0 + b0).ult a0 then (1 : BitVec 64) else 0
    let r0 := a0 + b0
    let cy1 := (if (a1 + b1).ult a1 then (1 : BitVec 64) else 0) |||
               (if (a1 + b1 + (cy0 &&& 1)).ult (cy0 &&& 1) then 1 else 0)
    let r1 := a1 + b1 + (cy0 &&& 1)
    let cy2 := (if (a2 + b2).ult a2 then (1 : BitVec 64) else 0) |||
               (if (a2 + b2 + (cy1 &&& 1)).ult (cy1 &&& 1) then 1 else 0)
    let r2 := a2 + b2 + (cy1 &&& 1)
    let _cy3 := (if (a3 + b3).ult a3 then (1 : BitVec 64) else 0) |||
                (if (a3 + b3 + (cy2 &&& 1)).ult (cy2 &&& 1) then 1 else 0)
    let r3 := a3 + b3 + (cy2 &&& 1)
    let a256 : BitVec 256 := a3 ++ a2 ++ a1 ++ a0
    let b256 : BitVec 256 := b3 ++ b2 ++ b1 ++ b0
    let r256 : BitVec 256 := r3 ++ r2 ++ r1 ++ r0
    r256 = a256 + b256 := by
  bv_decide

/-- 4-limb SBB chain = BitVec 256 subtraction. -/
theorem sbb_chain_eq_sub_bv256
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    let cf0 := if a0.ult b0 then (1 : BitVec 64) else 0
    let t0 := a0 - b0
    let cf1 := (if a1.ult b1 then (1 : BitVec 64) else 0) |||
               (if (a1 - b1).ult (cf0 &&& 1) then 1 else 0)
    let t1 := a1 - b1 - (cf0 &&& 1)
    let cf2 := (if a2.ult b2 then (1 : BitVec 64) else 0) |||
               (if (a2 - b2).ult (cf1 &&& 1) then 1 else 0)
    let t2 := a2 - b2 - (cf1 &&& 1)
    let _cf3 := (if a3.ult b3 then (1 : BitVec 64) else 0) |||
                (if (a3 - b3).ult (cf2 &&& 1) then 1 else 0)
    let t3 := a3 - b3 - (cf2 &&& 1)
    let a256 : BitVec 256 := a3 ++ a2 ++ a1 ++ a0
    let b256 : BitVec 256 := b3 ++ b2 ++ b1 ++ b0
    let t256 : BitVec 256 := t3 ++ t2 ++ t1 ++ t0
    t256 = a256 - b256 := by
  bv_decide

/-! ### BignumDoubleP25519

The 4-limb (ADC then SBB then mask-cmov) chain on input a<p produces
the canonical reduction of `2a mod p`. Identity at the BitVec 256
level. Same pattern as `sbb_chain_bv256`, but with an ADC chain
prefix to compute `r = a + a`. -/

theorem double_p25519_chain_bv256
    (a0 a1 a2 a3 : BitVec 64) :
    let p0 : BitVec 64 := 0xFFFFFFFFFFFFFFED
    let pmid : BitVec 64 := 0xFFFFFFFFFFFFFFFF
    let p3 : BitVec 64 := 0x7FFFFFFFFFFFFFFF
    let cy0 := if (a0 + a0).ult a0 then (1 : BitVec 64) else 0
    let r0 := a0 + a0
    let cy1 := (if (a1 + a1).ult a1 then (1 : BitVec 64) else 0) |||
               (if (a1 + a1 + (cy0 &&& 1)).ult (cy0 &&& 1) then 1 else 0)
    let r1 := a1 + a1 + (cy0 &&& 1)
    let cy2 := (if (a2 + a2).ult a2 then (1 : BitVec 64) else 0) |||
               (if (a2 + a2 + (cy1 &&& 1)).ult (cy1 &&& 1) then 1 else 0)
    let r2 := a2 + a2 + (cy1 &&& 1)
    let cy3 := (if (a3 + a3).ult a3 then (1 : BitVec 64) else 0) |||
               (if (a3 + a3 + (cy2 &&& 1)).ult (cy2 &&& 1) then 1 else 0)
    let r3 := a3 + a3 + (cy2 &&& 1)
    let cf0 := if r0.ult p0 then (1 : BitVec 64) else 0
    let t0 := r0 - p0
    let cf1 := (if r1.ult pmid then (1 : BitVec 64) else 0) |||
               (if (r1 - pmid).ult (cf0 &&& 1) then 1 else 0)
    let t1 := r1 - pmid - (cf0 &&& 1)
    let cf2 := (if r2.ult pmid then (1 : BitVec 64) else 0) |||
               (if (r2 - pmid).ult (cf1 &&& 1) then 1 else 0)
    let t2 := r2 - pmid - (cf1 &&& 1)
    let cf3 := (if r3.ult p3 then (1 : BitVec 64) else 0) |||
               (if (r3 - p3).ult (cf2 &&& 1) then 1 else 0)
    let t3 := r3 - p3 - (cf2 &&& 1)
    let mask : BitVec 64 := -(cf3 &&& 1)
    let nmask : BitVec 64 := mask ^^^ (BitVec.allOnes 64)
    let r256 : BitVec 256 := r3 ++ r2 ++ r1 ++ r0
    let p256 : BitVec 256 := 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED
    let o0 := (mask &&& r0) ||| (nmask &&& t0)
    let o1 := (mask &&& r1) ||| (nmask &&& t1)
    let o2 := (mask &&& r2) ||| (nmask &&& t2)
    let o3 := (mask &&& r3) ||| (nmask &&& t3)
    let o256 : BitVec 256 := o3 ++ o2 ++ o1 ++ o0
    o256 = if r256.ult p256 then r256 else r256 - p256 := by
  bv_decide

/-! ### BignumSubP25519

Two-input shape: SBB chain on `(a, b)` produces `t = (a - b) mod B`;
mask = -borrow_final. Output = `t + (mask AND p)` mod B. -/

theorem sub_p25519_chain_bv256
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    let p0 : BitVec 64 := 0xFFFFFFFFFFFFFFED
    let pmid : BitVec 64 := 0xFFFFFFFFFFFFFFFF
    let p3 : BitVec 64 := 0x7FFFFFFFFFFFFFFF
    let cf0 := if a0.ult b0 then (1 : BitVec 64) else 0
    let t0 := a0 - b0
    let cf1 := (if a1.ult b1 then (1 : BitVec 64) else 0) |||
               (if (a1 - b1).ult (cf0 &&& 1) then 1 else 0)
    let t1 := a1 - b1 - (cf0 &&& 1)
    let cf2 := (if a2.ult b2 then (1 : BitVec 64) else 0) |||
               (if (a2 - b2).ult (cf1 &&& 1) then 1 else 0)
    let t2 := a2 - b2 - (cf1 &&& 1)
    let cf3 := (if a3.ult b3 then (1 : BitVec 64) else 0) |||
               (if (a3 - b3).ult (cf2 &&& 1) then 1 else 0)
    let t3 := a3 - b3 - (cf2 &&& 1)
    let mask : BitVec 64 := -(cf3 &&& 1)
    let mp0 := mask &&& p0
    let mp3 := mask &&& p3
    let cy0 := if (t0 + mp0).ult t0 then (1 : BitVec 64) else 0
    let s0 := t0 + mp0
    let cy1 := (if (t1 + mask).ult t1 then (1 : BitVec 64) else 0) |||
               (if (t1 + mask + (cy0 &&& 1)).ult (cy0 &&& 1) then 1 else 0)
    let s1 := t1 + mask + (cy0 &&& 1)
    let cy2 := (if (t2 + mask).ult t2 then (1 : BitVec 64) else 0) |||
               (if (t2 + mask + (cy1 &&& 1)).ult (cy1 &&& 1) then 1 else 0)
    let s2 := t2 + mask + (cy1 &&& 1)
    let _cy3 := (if (t3 + mp3).ult t3 then (1 : BitVec 64) else 0) |||
                (if (t3 + mp3 + (cy2 &&& 1)).ult (cy2 &&& 1) then 1 else 0)
    let s3 := t3 + mp3 + (cy2 &&& 1)
    let a256 : BitVec 256 := a3 ++ a2 ++ a1 ++ a0
    let b256 : BitVec 256 := b3 ++ b2 ++ b1 ++ b0
    let p256 : BitVec 256 := 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED
    let s256 : BitVec 256 := s3 ++ s2 ++ s1 ++ s0
    s256 = if a256.ult b256 then a256 - b256 + p256 else a256 - b256 := by
  bv_decide (config := { timeout := 120 })

/-! ### Phase 4 — abstracted algoNat lemmas

Reformulated at the BitVec 256 level (no chain duplication). Per-port
applications use `adc_chain_eq_add_bv256` / `sbb_chain_eq_sub_bv256`
to bridge the chain output. -/

/-- For `bignum_double_p25519`: with `a < p`, the conditional-subtract
    output equals `algoNat a`. -/
theorem double_p25519_algoNat_bv256
    (a256 : BitVec 256)
    (h_bound : a256.toNat < 2^255 - 19) :
    let p256 : BitVec 256 := 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED
    (if (a256 + a256).ult p256 then a256 + a256 else (a256 + a256) - p256).toNat =
      S2NBignumSSA.BignumDoubleP25519.algoNat a256.toNat := by
  intro p256
  have hp256_toNat : p256.toNat = 2^255 - 19 := by decide
  have h_a_lt : a256.toNat < 2^256 := a256.isLt
  have h_2a_lt : 2 * a256.toNat < 2^256 := by omega
  have h_add_toNat : (a256 + a256).toNat = 2 * a256.toNat := by
    rw [BitVec.toNat_add]; omega
  unfold S2NBignumSSA.BignumDoubleP25519.algoNat
  by_cases h : (a256 + a256).ult p256
  · rw [if_pos h]
    rw [BitVec.ult_iff_lt, BitVec.lt_def, h_add_toNat, hp256_toNat] at h
    have : ¬ (2 * a256.toNat) % (2^256) ≥ 2^255 - 19 := by
      rw [Nat.mod_eq_of_lt h_2a_lt]; omega
    rw [if_neg this, h_add_toNat, Nat.mod_eq_of_lt h_2a_lt]
  · rw [if_neg h]
    rw [BitVec.ult_iff_lt, BitVec.lt_def] at h
    have h_le : p256 ≤ a256 + a256 := by
      rw [BitVec.le_def]; rw [h_add_toNat] at h; omega
    have h_ge : (2 * a256.toNat) % (2^256) ≥ 2^255 - 19 := by
      rw [Nat.mod_eq_of_lt h_2a_lt]; rw [h_add_toNat, hp256_toNat] at h; omega
    rw [if_pos h_ge, BitVec.toNat_sub_of_le h_le, h_add_toNat,
        Nat.mod_eq_of_lt h_2a_lt, hp256_toNat]

/-- Per-limb wrapper for `bignum_double_p25519`: the 4-limb (ADC then
    SBB then mask-cmov) chain on input `a < p` produces the canonical
    reduction of `2a mod p` at the Nat level. -/
theorem double_p25519_chain_algoNat
    (a0 a1 a2 a3 : BitVec 64)
    (h_bound : a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 +
                  a3.toNat * 2^192 < 2^255 - 19) :
    let p0 : BitVec 64 := 0xFFFFFFFFFFFFFFED
    let pmid : BitVec 64 := 0xFFFFFFFFFFFFFFFF
    let p3 : BitVec 64 := 0x7FFFFFFFFFFFFFFF
    let cy0 := if (a0 + a0).ult a0 then (1 : BitVec 64) else 0
    let r0 := a0 + a0
    let cy1 := (if (a1 + a1).ult a1 then (1 : BitVec 64) else 0) |||
               (if (a1 + a1 + (cy0 &&& 1)).ult (cy0 &&& 1) then 1 else 0)
    let r1 := a1 + a1 + (cy0 &&& 1)
    let cy2 := (if (a2 + a2).ult a2 then (1 : BitVec 64) else 0) |||
               (if (a2 + a2 + (cy1 &&& 1)).ult (cy1 &&& 1) then 1 else 0)
    let r2 := a2 + a2 + (cy1 &&& 1)
    let _cy3 := (if (a3 + a3).ult a3 then (1 : BitVec 64) else 0) |||
                (if (a3 + a3 + (cy2 &&& 1)).ult (cy2 &&& 1) then 1 else 0)
    let r3 := a3 + a3 + (cy2 &&& 1)
    let cf0 := if r0.ult p0 then (1 : BitVec 64) else 0
    let t0 := r0 - p0
    let cf1 := (if r1.ult pmid then (1 : BitVec 64) else 0) |||
               (if (r1 - pmid).ult (cf0 &&& 1) then 1 else 0)
    let t1 := r1 - pmid - (cf0 &&& 1)
    let cf2 := (if r2.ult pmid then (1 : BitVec 64) else 0) |||
               (if (r2 - pmid).ult (cf1 &&& 1) then 1 else 0)
    let t2 := r2 - pmid - (cf1 &&& 1)
    let cf3 := (if r3.ult p3 then (1 : BitVec 64) else 0) |||
               (if (r3 - p3).ult (cf2 &&& 1) then 1 else 0)
    let t3 := r3 - p3 - (cf2 &&& 1)
    let mask : BitVec 64 := -(cf3 &&& 1)
    let nmask : BitVec 64 := mask ^^^ (BitVec.allOnes 64)
    let o0 := (mask &&& r0) ||| (nmask &&& t0)
    let o1 := (mask &&& r1) ||| (nmask &&& t1)
    let o2 := (mask &&& r2) ||| (nmask &&& t2)
    let o3 := (mask &&& r3) ||| (nmask &&& t3)
    o0.toNat + o1.toNat * 2^64 + o2.toNat * 2^128 + o3.toNat * 2^192 =
      S2NBignumSSA.BignumDoubleP25519.algoNat
        (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192) := by
  intro p0 pmid p3 cy0 r0 cy1 r1 cy2 r2 _cy3 r3 cf0 t0 cf1 t1 cf2 t2 cf3 t3
        mask nmask o0 o1 o2 o3
  rw [← toNat_concat_4limbs o0 o1 o2 o3]
  rw [double_p25519_chain_bv256 a0 a1 a2 a3]
  have h_r256 : (r3 ++ r2 ++ r1 ++ r0 : BitVec 256) =
      (a3 ++ a2 ++ a1 ++ a0 : BitVec 256) + (a3 ++ a2 ++ a1 ++ a0 : BitVec 256) :=
    adc_chain_eq_add_bv256 a0 a1 a2 a3 a0 a1 a2 a3
  rw [h_r256, ← toNat_concat_4limbs a0 a1 a2 a3]
  apply double_p25519_algoNat_bv256
  rw [toNat_concat_4limbs]
  exact h_bound

/-- Bridge: `addCarryIn`'s carry-out `.1` equals the `chain_algoNat`'s
    second-disjunct formulation. Both correctly compute the ADC carry,
    but use different `.ult` arguments syntactically. Provable by
    `bv_decide` since `cin &&& 1 ∈ {0, 1}`. -/
theorem addCarryIn_carry_eq_chain (a b cin : BitVec 64) :
    (BignumExec.addCarryIn a b cin).1 =
      (if (a + b).ult a then (1 : BitVec 64) else 0) |||
      (if (a + b + (cin &&& 1)).ult (cin &&& 1) then 1 else 0) := by
  unfold BignumExec.addCarryIn
  bv_decide

/-- Bridge: `subBorrowIn`'s borrow-out `.1` equals the `chain_algoNat`'s
    second-disjunct formulation. Mirrors `addCarryIn_carry_eq_chain` for
    the SBB chain in `sub_p25519_phaseB_triple`. Provable by `rfl` (the
    chain form is exactly the definition). -/
theorem subBorrowIn_borrow_eq_chain (a b cin : BitVec 64) :
    (BignumExec.subBorrowIn a b cin).1 =
      (if a.ult b then (1 : BitVec 64) else 0) |||
      (if (a - b).ult (cin &&& 1) then 1 else 0) := rfl

/-- Bridge: `subBorrow`'s borrow-out `.1` equals the `chain_algoNat`'s
    first-limb formulation. By `rfl`. -/
theorem subBorrow_borrow_eq_chain (a b : BitVec 64) :
    (BignumExec.subBorrow a b).1 = if a.ult b then (1 : BitVec 64) else 0 := rfl

/-- Bridge: `subBorrowIn`'s difference output `.2` equals
    `a - b - (cin &&& 1)`. By `rfl`. -/
theorem subBorrowIn_diff_eq (a b cin : BitVec 64) :
    (BignumExec.subBorrowIn a b cin).2 = a - b - (cin &&& 1) := rfl

/-- Bridge: `subBorrow`'s difference output `.2` equals `a - b`. By `rfl`. -/
theorem subBorrow_diff_eq (a b : BitVec 64) :
    (BignumExec.subBorrow a b).2 = a - b := rfl

/-- For `bignum_sub_p25519`: SBB-then-add-back-of-p output equals
    `algoNat a b`. -/
theorem sub_p25519_algoNat_bv256
    (a256 b256 : BitVec 256) :
    let p256 : BitVec 256 := 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED
    (if a256.ult b256 then a256 - b256 + p256 else a256 - b256).toNat =
      S2NBignumSSA.BignumSubP25519.algoNat a256.toNat b256.toNat := by
  intro p256
  have hp256_toNat : p256.toNat = 2^255 - 19 := by decide
  have ha : a256.toNat < 2^256 := a256.isLt
  have hb : b256.toNat < 2^256 := b256.isLt
  show (if a256.ult b256 then a256 - b256 + p256 else a256 - b256).toNat =
    (if a256.toNat ≥ b256.toNat then a256.toNat - b256.toNat
     else (a256.toNat + 2^256 - b256.toNat + (2^255 - 19)) % 2^256)
  by_cases h : a256.ult b256
  · rw [if_pos h]
    rw [BitVec.ult_iff_lt, BitVec.lt_def] at h
    have : ¬ a256.toNat ≥ b256.toNat := by omega
    rw [if_neg this, BitVec.toNat_add, BitVec.toNat_sub, hp256_toNat]
    have h_inner_lt : (2^256 - b256.toNat + a256.toNat) < 2^256 := by omega
    rw [Nat.mod_eq_of_lt h_inner_lt]
    congr 1; omega
  · rw [if_neg h]
    rw [BitVec.ult_iff_lt] at h
    have h_le : b256 ≤ a256 := by
      rw [BitVec.le_def]; rw [BitVec.lt_def] at h; omega
    have h_ge : a256.toNat ≥ b256.toNat := by rw [BitVec.le_def] at h_le; exact h_le
    rw [if_pos h_ge, BitVec.toNat_sub_of_le h_le]

/-- Per-limb wrapper for `bignum_sub_p25519`: the 4-limb (SBB then
    mask then masked-p ADC) chain produces the canonical `(a − b) mod p`
    at the Nat level. -/
theorem sub_p25519_chain_algoNat
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    let p0 : BitVec 64 := 0xFFFFFFFFFFFFFFED
    let pmid : BitVec 64 := 0xFFFFFFFFFFFFFFFF
    let p3 : BitVec 64 := 0x7FFFFFFFFFFFFFFF
    let cf0 := if a0.ult b0 then (1 : BitVec 64) else 0
    let t0 := a0 - b0
    let cf1 := (if a1.ult b1 then (1 : BitVec 64) else 0) |||
               (if (a1 - b1).ult (cf0 &&& 1) then 1 else 0)
    let t1 := a1 - b1 - (cf0 &&& 1)
    let cf2 := (if a2.ult b2 then (1 : BitVec 64) else 0) |||
               (if (a2 - b2).ult (cf1 &&& 1) then 1 else 0)
    let t2 := a2 - b2 - (cf1 &&& 1)
    let cf3 := (if a3.ult b3 then (1 : BitVec 64) else 0) |||
               (if (a3 - b3).ult (cf2 &&& 1) then 1 else 0)
    let t3 := a3 - b3 - (cf2 &&& 1)
    let mask : BitVec 64 := -(cf3 &&& 1)
    let mp0 := mask &&& p0
    let mp3 := mask &&& p3
    let cy0 := if (t0 + mp0).ult t0 then (1 : BitVec 64) else 0
    let s0 := t0 + mp0
    let cy1 := (if (t1 + mask).ult t1 then (1 : BitVec 64) else 0) |||
               (if (t1 + mask + (cy0 &&& 1)).ult (cy0 &&& 1) then 1 else 0)
    let s1 := t1 + mask + (cy0 &&& 1)
    let cy2 := (if (t2 + mask).ult t2 then (1 : BitVec 64) else 0) |||
               (if (t2 + mask + (cy1 &&& 1)).ult (cy1 &&& 1) then 1 else 0)
    let s2 := t2 + mask + (cy1 &&& 1)
    let _cy3' := (if (t3 + mp3).ult t3 then (1 : BitVec 64) else 0) |||
                 (if (t3 + mp3 + (cy2 &&& 1)).ult (cy2 &&& 1) then 1 else 0)
    let s3 := t3 + mp3 + (cy2 &&& 1)
    s0.toNat + s1.toNat * 2^64 + s2.toNat * 2^128 + s3.toNat * 2^192 =
      S2NBignumSSA.BignumSubP25519.algoNat
        (a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192)
        (b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192) := by
  intro p0 pmid p3 cf0 t0 cf1 t1 cf2 t2 cf3 t3 mask mp0 mp3
        cy0 s0 cy1 s1 cy2 s2 _cy3' s3
  rw [← toNat_concat_4limbs s0 s1 s2 s3]
  rw [sub_p25519_chain_bv256 a0 a1 a2 a3 b0 b1 b2 b3]
  rw [← toNat_concat_4limbs a0 a1 a2 a3, ← toNat_concat_4limbs b0 b1 b2 b3]
  exact sub_p25519_algoNat_bv256 (a3 ++ a2 ++ a1 ++ a0) (b3 ++ b2 ++ b1 ++ b0)

end CatCrypt.Crypto.Jasmin.BignumHoare
