/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit

/-!
# Barrett field-reduction law for the emitted Plonky3 NTT butterfly

`Plonky3NttButterflyEmit` emits the BabyBear multiplicative reduction
(`p = 2013265921 = 2^31 − 2^27 + 1`) as a **Barrett** reduction built only from
`regArith` `mul/shr/sub/and/add` (doc lines ~34–44 of that file):
```
  hi = x >> 30
  q  = (hi * MU) >> 32        -- MU = ⌊2^62 / p⌋ = 2290649223
  t  = x − q·p                -- t ∈ [0, 2p)
  wb = csub(t)                -- one branchless conditional subtract
```
This file gives that emitted sequence a standalone Lean definition
(`barrettReduceMU`) matching the word arithmetic exactly, and proves it equals
the field reduction `x % p` for any `x < 2^62` (`barrettReduceMU_correct`), and
hence that the butterfly's `bbMul` step (`a · b` for canonical `a, b < p`) is the
field product (`barrettMul_correct`). This discharges the Barrett-reduction law
that `Plonky3NttButterflyEmit` previously left KAT-witnessed.

## The Barrett quotient bound (the classic `t ∈ [0, 2p)`)

Writing `x = h·2^30 + r₀` (`r₀ < 2^30`), `h·MU = q·2^32 + r₁` (`r₁ < 2^32`), and
`MU·p = 2^62 − s` with `s = 2^62 mod p = 796358521` (`0 < s < p`), the estimate
`t = x − q·p` satisfies the exact identity
```
  t · 2^32 = r₀ · 2^32 + h · s + r₁ · p          (†)
```
From (†): `t ≥ 0` (the RHS is a sum of non-negatives, and `q·p ≤ x`), and since
`r₀ < 2^30`, `h < 2^32`, `r₁ < 2^32`,
```
  t · 2^32 < 2^30 · 2^32 + 2^32 · s + 2^32 · p
  ⟹  t < 2^30 + s + p = 3883366266 < 2 · p = 4026531842,
```
so a single conditional subtract canonicalises `t` into `[0, p)`. This is the
standard Barrett bound; the asymmetric shifts `(30, 32)` make the slack tight
(empirical max `t ≈ 3.84·10^9`, well below `2p`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3BarrettLaw

open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit

/-- The Barrett constant `MU = ⌊2^62 / p⌋ = 2290649223`, as a `BitVec 64`. -/
def bbMU : BitVec 64 := 2290649223

/-- `bbMU.toNat = 2290649223`. -/
theorem bbMU_toNat : bbMU.toNat = 2290649223 := by decide

/-- **The emitted Barrett reduction sequence** for one BabyBear multiplicative
    reduction: `hi = x >> 30`, `q = (hi · MU) >> 32`, `t = x − q·p`, then one
    conditional subtract `bbCsub`. Matches `Plonky3NttButterflyEmit`'s `regArith`
    body line-for-line. -/
def barrettReduceMU (x : BitVec 64) : BitVec 64 :=
  let hi := x >>> (30 : Nat)
  let q := (hi * bbMU) >>> (32 : Nat)
  let t := x - q * bbP
  bbCsub t

/-- The Barrett estimate's `.toNat`, with no 64-bit overflow, for `x < 2^62`.
    `hi = X / 2^30`, `q = (hi · MU) / 2^32` (the `hi · MU` product fits in 64
    bits since `hi, MU < 2^32`). -/
theorem barrett_q_toNat (x : BitVec 64) (hx : x.toNat < 2 ^ 62) :
    (((x >>> (30 : Nat)) * bbMU) >>> (32 : Nat)).toNat
      = (x.toNat / 2 ^ 30 * 2290649223) / 2 ^ 32 := by
  have hhi : (x >>> (30 : Nat)).toNat = x.toNat / 2 ^ 30 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hhilt : x.toNat / 2 ^ 30 < 2 ^ 32 := by
    apply Nat.div_lt_of_lt_mul; omega
  -- hi * MU < 2^64, so the BitVec product carries no wraparound
  have hprodlt : x.toNat / 2 ^ 30 * 2290649223 < 2 ^ 64 := by
    have hle : x.toNat / 2 ^ 30 * 2290649223 ≤ (2 ^ 32 - 1) * 2290649223 := by
      gcongr; omega
    have hb : (2 ^ 32 - 1) * 2290649223 < 2 ^ 64 := by norm_num
    exact lt_of_le_of_lt hle hb
  have hmul : ((x >>> (30 : Nat)) * bbMU).toNat = x.toNat / 2 ^ 30 * 2290649223 := by
    rw [BitVec.toNat_mul, hhi, bbMU_toNat, Nat.mod_eq_of_lt hprodlt]
  rw [BitVec.toNat_ushiftRight, hmul, Nat.shiftRight_eq_div_pow]

/-- **The Barrett quotient never overshoots:** `q · p ≤ x` (so `t = x − q·p ≥ 0`),
    via `q·2^32 ≤ h·MU`, `MU·p ≤ 2^62`, `h·2^30 ≤ x`. -/
theorem barrett_q_mul_p_le (x : BitVec 64) :
    (x.toNat / 2 ^ 30 * 2290649223 / 2 ^ 32) * 2013265921 ≤ x.toNat := by
  set h := x.toNat / 2 ^ 30 with hh
  set q := h * 2290649223 / 2 ^ 32 with hq
  -- q * 2^32 ≤ h * MU
  have h1 : q * 2 ^ 32 ≤ h * 2290649223 := Nat.div_mul_le_self _ _
  -- h * 2^30 ≤ x
  have h2 : h * 2 ^ 30 ≤ x.toNat := Nat.div_mul_le_self _ _
  -- MU * p ≤ 2^62
  have h3 : (2290649223 : Nat) * 2013265921 ≤ 2 ^ 62 := by norm_num
  -- q*p*2^32 ≤ h*MU*p ≤ h*2^62 = h*2^30*2^32 ≤ x*2^32
  have key : q * 2013265921 * 2 ^ 32 ≤ x.toNat * 2 ^ 32 := by
    calc q * 2013265921 * 2 ^ 32 = q * 2 ^ 32 * 2013265921 := by ring
      _ ≤ h * 2290649223 * 2013265921 := by
          exact Nat.mul_le_mul_right _ h1
      _ = h * (2290649223 * 2013265921) := by ring
      _ ≤ h * 2 ^ 62 := by exact Nat.mul_le_mul_left _ h3
      _ = h * 2 ^ 30 * 2 ^ 32 := by ring
      _ ≤ x.toNat * 2 ^ 32 := by exact Nat.mul_le_mul_right _ h2
  exact Nat.le_of_mul_le_mul_right key (by norm_num)

/-- **The Barrett estimate undershoots by less than `2p`:** `x < q·p + 2p`.
    From the exact identity `t·2^32 = r₀·2^32 + h·s + r₁·p` with
    `r₀ < 2^30`, `h < 2^32`, `r₁ < 2^32`, `s = 2^62 − MU·p = 796358521`. -/
theorem barrett_x_lt (x : BitVec 64) (hx : x.toNat < 2 ^ 62) :
    x.toNat < (x.toNat / 2 ^ 30 * 2290649223 / 2 ^ 32) * 2013265921
      + 2 * 2013265921 := by
  set h := x.toNat / 2 ^ 30 with hh
  set q := h * 2290649223 / 2 ^ 32 with hq
  -- decompositions: x = h*2^30 + r0, h*MU = q*2^32 + r1
  have hr0 : x.toNat = h * 2 ^ 30 + x.toNat % 2 ^ 30 := by
    rw [hh]; rw [Nat.div_add_mod' x.toNat (2 ^ 30)]
  have hr0lt : x.toNat % 2 ^ 30 < 2 ^ 30 := Nat.mod_lt _ (by norm_num)
  have hr1 : h * 2290649223 = q * 2 ^ 32 + h * 2290649223 % 2 ^ 32 := by
    rw [hq]; rw [Nat.div_add_mod' (h * 2290649223) (2 ^ 32)]
  have hr1lt : h * 2290649223 % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hhlt : h < 2 ^ 32 := by rw [hh]; apply Nat.div_lt_of_lt_mul; omega
  -- the key exact identity: t*2^32 = r0*2^32 + h*s + r1*p  with MU*p = 2^62 - s
  -- equivalently  x*2^32 = q*p*2^32 + r0*2^32 + h*s + r1*p
  set r0 := x.toNat % 2 ^ 30 with hr0d
  set r1 := h * 2290649223 % 2 ^ 32 with hr1d
  have hMUp : (2290649223 : Nat) * 2013265921 = 2 ^ 62 - 796358521 := by norm_num
  -- multiply the x-identity by 2^32 and substitute h*MU
  have ident : x.toNat * 2 ^ 32
      = q * 2013265921 * 2 ^ 32 + (r0 * 2 ^ 32 + h * 796358521 + r1 * 2013265921) := by
    have e1 : x.toNat * 2 ^ 32 = h * 2 ^ 62 + r0 * 2 ^ 32 := by
      conv_lhs => rw [hr0]
      ring
    -- h * 2^62 = h*MU*p + h*s   (since MU*p = 2^62 - s, and s < 2^62)
    have e2 : h * 2 ^ 62 = h * (2290649223 * 2013265921) + h * 796358521 := by
      rw [hMUp]
      have : (2 : Nat) ^ 62 = (2 ^ 62 - 796358521) + 796358521 := by norm_num
      conv_lhs => rw [this]
      ring
    -- h*MU*p = (q*2^32 + r1)*p = q*p*2^32 + r1*p
    have e3 : h * (2290649223 * 2013265921) = q * 2013265921 * 2 ^ 32 + r1 * 2013265921 := by
      have : h * (2290649223 * 2013265921) = (h * 2290649223) * 2013265921 := by ring
      rw [this, hr1]; ring
    rw [e1, e2, e3]; ring
  -- bound the remainder term: r0*2^32 + h*s + r1*p < (2^30 + s + p) * 2^32 < 2p*2^32
  have rem_lt : r0 * 2 ^ 32 + h * 796358521 + r1 * 2013265921 < 2 * 2013265921 * 2 ^ 32 := by
    have b0 : r0 * 2 ^ 32 ≤ (2 ^ 30 - 1) * 2 ^ 32 := by gcongr; omega
    have b1 : h * 796358521 ≤ (2 ^ 32 - 1) * 796358521 := by gcongr; omega
    have b2 : r1 * 2013265921 ≤ (2 ^ 32 - 1) * 2013265921 := by gcongr; omega
    have bnum : (2 ^ 30 - 1) * 2 ^ 32 + (2 ^ 32 - 1) * 796358521
        + (2 ^ 32 - 1) * 2013265921 < 2 * 2013265921 * 2 ^ 32 := by norm_num
    calc r0 * 2 ^ 32 + h * 796358521 + r1 * 2013265921
        ≤ (2 ^ 30 - 1) * 2 ^ 32 + (2 ^ 32 - 1) * 796358521
            + (2 ^ 32 - 1) * 2013265921 :=
          Nat.add_le_add (Nat.add_le_add b0 b1) b2
      _ < 2 * 2013265921 * 2 ^ 32 := bnum
  -- combine: x*2^32 = q*p*2^32 + rem < q*p*2^32 + 2p*2^32, cancel 2^32
  have hlt32 : x.toNat * 2 ^ 32 < (q * 2013265921 + 2 * 2013265921) * 2 ^ 32 := by
    rw [ident]
    have he : (q * 2013265921 + 2 * 2013265921) * 2 ^ 32
        = q * 2013265921 * 2 ^ 32 + 2 * 2013265921 * 2 ^ 32 := by ring
    rw [he]
    exact Nat.add_lt_add_left rem_lt _
  exact Nat.lt_of_mul_lt_mul_right hlt32

/-- **`barrettReduceMU` is the BabyBear field reduction.** For any `x < 2^62`
    (in particular any product of two canonical residues), the emitted Barrett
    sequence equals `x % p`. The estimate `q` satisfies `q·p ≤ x < q·p + 2p`
    (`barrett_q_mul_p_le`, `barrett_x_lt`), so `t = x − q·p ∈ [0, 2p)` and the
    single `bbCsub` canonicalises it. -/
theorem barrettReduceMU_correct (x : BitVec 64) (hx : x.toNat < 2 ^ 62) :
    barrettReduceMU x = x % bbP := by
  -- abbreviations matching the def
  set q := x.toNat / 2 ^ 30 * 2290649223 / 2 ^ 32 with hq
  have hqle : q * 2013265921 ≤ x.toNat := barrett_q_mul_p_le x
  have hxlt : x.toNat < q * 2013265921 + 2 * 2013265921 := barrett_x_lt x hx
  -- the BitVec quotient term q (as a BitVec); its toNat
  set qbv := ((x >>> (30 : Nat)) * bbMU) >>> (32 : Nat) with hqbv
  have hqbv_toNat : qbv.toNat = q := by rw [hqbv, barrett_q_toNat x hx, ← hq]
  -- q*p < 2^64 (so the BitVec product q*P doesn't wrap)
  have hqp_lt : q * 2013265921 < 2 ^ 64 :=
    lt_of_le_of_lt hqle (lt_of_lt_of_le hx (by norm_num))
  have hqp_toNat : (qbv * bbP).toNat = q * 2013265921 := by
    rw [BitVec.toNat_mul, hqbv_toNat, bbP_toNat, Nat.mod_eq_of_lt hqp_lt]
  -- t = x - q*P, with q*P ≤ x, so toNat subtracts without wrap
  set t := x - qbv * bbP with ht
  have hle : qbv * bbP ≤ x := by rw [BitVec.le_def, hqp_toNat]; exact hqle
  have ht_toNat : t.toNat = x.toNat - q * 2013265921 := by
    rw [ht, BitVec.toNat_sub_of_le hle, hqp_toNat]
  -- t < 2p (BitVec), from t.toNat < 2p
  have ht_lt2p : t < 2 * (2013265921 : BitVec 64) := by
    have h2p : (2 * (2013265921 : BitVec 64)).toNat = 4026531842 := by decide
    rw [BitVec.lt_def, h2p, ht_toNat]; omega
  -- the Nat residue equality: (x - q*p) % p = x % p (since q*p ≤ x)
  have hmodNat : t.toNat % 2013265921 = x.toNat % 2013265921 := by
    rw [ht_toNat]
    have hsum : x.toNat - q * 2013265921 + q * 2013265921 = x.toNat := by omega
    conv_rhs => rw [← hsum]
    rw [Nat.add_mul_mod_self_right]
  -- barrettReduceMU x = bbCsub t = t % p = x % p
  show bbCsub t = x % bbP
  rw [bbCsub_correct t ht_lt2p]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_umod, bbP_toNat]
  exact hmodNat

/-- **The butterfly's `bbMul` step is the BabyBear field product.** For canonical
    `a, b < p`, the product `a · b < p^2 < 2^62`, so the Barrett reduction of the
    word product equals `(a · b) % p` — the field multiply realised by the
    emitted NTT butterfly. -/
theorem barrettMul_correct (a b : BitVec 64) (ha : a < bbP) (hb : b < bbP) :
    barrettReduceMU (a * b) = (a * b) % bbP := by
  have ha' : a.toNat < 2013265921 := by
    have := (BitVec.lt_def).mp ha; simpa [bbP, BitVec.toNat_ofNat] using this
  have hb' : b.toNat < 2013265921 := by
    have := (BitVec.lt_def).mp hb; simpa [bbP, BitVec.toNat_ofNat] using this
  have hprod : (a * b).toNat < 2 ^ 62 := by
    rw [BitVec.toNat_mul]
    have hlt : a.toNat * b.toNat < 2013265921 * 2013265921 := Nat.mul_lt_mul'' ha' hb'
    have hle : a.toNat * b.toNat % 2 ^ 64 ≤ a.toNat * b.toNat := Nat.mod_le _ _
    have : a.toNat * b.toNat < 2 ^ 62 := lt_of_lt_of_le hlt (by norm_num)
    omega
  exact barrettReduceMU_correct (a * b) hprod

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3BarrettLaw
