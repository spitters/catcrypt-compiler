/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaMontgomery
import Mathlib
import Std.Tactic.BVDecide

/-!
# The abstract ML-DSA signed-Montgomery congruence (`ZMod`/`Int`, not SAT)

`CompileFromHaxMldsaMontgomery` proves `mldsaMontgomery_compiles` — the verified
compiler emits the explicit emit form `mldsaMontgomeryForm a` — but documents that
the **abstract** Montgomery congruence *walls under `bv_decide`*: the body chains
two 64×64 multiplies (`a·QINV` and `t·q`), whose bit-blasted SAT instance times
out.

This module discharges that congruence by **`Int`/`ZMod` algebra**, not SAT.
With `q = 8380417`, `QINV = 58728449` (`QINV·q ≡ 1 (mod 2³²)`), `R = 2³²`, the
signed Montgomery reduce computes

```
t0  = a · QINV          (BitVec 64)
t   = (int32) t0        = sshiftRight (t0 <<< 32) 32   -- low int32, sign-extended
tq  = t · q
d   = a − tq
r   = d >>ₐ 32          (= sshiftRight d 32)
```

The two facts we prove:

* **Divisibility (unconditional).** The low 32 bits of `d = a − t·q` are zero, so
  `2³² ∣ d.toInt`. This is a *mod-2³²* fact: truncating to `BitVec 32` is a ring
  hom, `t ≡ t0 ≡ a·QINV (mod 2³²)`, and `QINV·q ≡ 1 (mod 2³²)`, hence
  `d ≡ a − a·QINV·q ≡ a − a = 0 (mod 2³²)`. The only 32-bit multiply involved
  collapses to the *constant* identity `QINV·q = 1` in `BitVec 32` (decidable),
  composed with `mul_assoc` — no 64×64 product is ever bit-blasted.

* **Exact shift + congruence (under the FIPS-204 no-overflow bound).** Because
  `2³² ∣ d.toInt`, the arithmetic shift is exact division: `r.toInt · 2³² =
  d.toInt`. Under `|a.toInt| ≤ q·2³¹` (FIPS-204 precondition) the int64
  subtraction `a − t·q` does not overflow (`|t.toInt| < 2³¹` because `t` is an
  `int32`, so `|t·q| < 2⁵⁴`, and `|a| < 2⁵⁵`, sum `< 2⁶³`), so `d.toInt =
  a.toInt − t.toInt·q` *exactly*; reducing mod `q` kills `t.toInt·q` and gives
  `r.toInt · 2³² ≡ a.toInt (mod q)`.

The headline theorem is `mldsaMontgomery_montgomery_congruence`. No `bv_decide`
is run on a 64×64 product; the only `bv_decide` calls are pure shift/truncation
lemmas and a `BitVec 32` constant.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaMontgomeryTie

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaMontgomery

/-- ML-DSA prime modulus `q` (FIPS-204). -/
def q : Int := 8380417

/-- The Montgomery quotient register `t = (int32)(a·QINV)`, as the explicit
    `BitVec 64` sub-expression of `mldsaMontgomeryForm`. -/
def montT (a : BitVec 64) : BitVec 64 :=
  BitVec.sshiftRight ((a * 58728449) <<< (32 : Nat)) 32

/-! ## Divisibility: the low 32 bits of `d = a − t·q` vanish -/

/-- The `(int32)` cast `sshiftRight (X <<< 32) 32` is the sign-extension of the
    low 32 bits: it agrees with `X` on those bits. (Pure shift fact, no product.) -/
theorem montT_setWidth_eq (a : BitVec 64) :
    BitVec.setWidth 32 (montT a) = BitVec.setWidth 32 (a * 58728449) := by
  unfold montT; bv_decide

/-- The low 32 bits of `d = a − t·q` are zero. Proven entirely mod `2³²`: the
    truncation `setWidth 32` is a ring hom, `t ≡ a·QINV (mod 2³²)`, and the only
    multiply that survives is the *constant* `QINV·q = 1` in `BitVec 32`. -/
theorem mont_low32_zero (a : BitVec 64) :
    BitVec.setWidth 32 (a - montT a * 8380417) = 0 := by
  have hlow := montT_setWidth_eq a
  have e1 : BitVec.setWidth 32 (a - montT a * 8380417)
      = BitVec.setWidth 32 a - BitVec.setWidth 32 (montT a * 8380417) := by bv_decide
  rw [e1, BitVec.setWidth_mul _ _ (by norm_num), hlow,
    BitVec.setWidth_mul _ _ (by norm_num)]
  have c8 : BitVec.setWidth 32 (8380417 : BitVec 64) = (8380417 : BitVec 32) := by bv_decide
  have c5 : BitVec.setWidth 32 (58728449 : BitVec 64) = (58728449 : BitVec 32) := by bv_decide
  have hconst : (58728449 : BitVec 32) * 8380417 = 1 := by bv_decide
  rw [c8, c5, mul_assoc, hconst, mul_one, sub_self]

/-- `2³² ∣ d.toInt` over `ℤ`, lifted from the mod-`2³²` divisibility of `d.toNat`. -/
theorem mont_dvd_toInt (a : BitVec 64) :
    (2 : Int) ^ 32 ∣ (a - montT a * 8380417).toInt := by
  have hlz := mont_low32_zero a
  generalize hd : a - montT a * 8380417 = d at *
  have hnat : d.toNat % 2 ^ 32 = 0 := by
    have := congrArg BitVec.toNat hlz
    simpa [BitVec.toNat_setWidth] using this
  have hn : (2 : Int) ^ 32 ∣ (d.toNat : Int) := by
    have : (2 ^ 32 : Nat) ∣ d.toNat := Nat.dvd_of_mod_eq_zero hnat
    exact_mod_cast Int.natCast_dvd_natCast.mpr this
  have hb : ((2 : Nat) ^ 64 : Int) ∣ (d.toInt - (d.toNat : Int)) := by
    rw [BitVec.toInt_eq_toNat_bmod]; exact Int.dvd_bmod_sub_self
  have h32_64 : (2 : Int) ^ 32 ∣ ((2 : Nat) ^ 64 : Int) := ⟨2 ^ 32, by norm_num⟩
  have hsub : (2 : Int) ^ 32 ∣ (d.toInt - (d.toNat : Int)) := dvd_trans h32_64 hb
  have := dvd_add hsub hn
  simpa using this

/-! ## The arithmetic shift is exact division by `2³²` -/

/-- Because `2³² ∣ d.toInt`, the arithmetic right shift by 32 is exact integer
    division: `r.toInt · 2³² = d.toInt`. -/
theorem mont_shift_exact (a : BitVec 64) :
    (BitVec.sshiftRight (a - montT a * 8380417) 32).toInt * 2 ^ 32
      = (a - montT a * 8380417).toInt := by
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  obtain ⟨k, hk⟩ := mont_dvd_toInt a
  rw [hk]; push_cast
  rw [Int.mul_ediv_cancel_left _ (by norm_num), mul_comm]

/-! ## The Montgomery quotient `t` is a sign-extended `int32` -/

/-- `t = (int32)(a·QINV)` is the sign-extension of the low 32 bits of `a·QINV`.
    (Pure shift fact; split out so its `bv_decide` reflection proof is kernel-checked
    in isolation.) -/
theorem montT_eq_signExtend (a : BitVec 64) :
    montT a = BitVec.signExtend 64 (BitVec.setWidth 32 (a * 58728449)) := by
  unfold montT; bv_decide

/-- `t = (int32)(a·QINV)` lands in the signed `int32` range `[-2³¹, 2³¹)`. -/
theorem montT_toInt_bounds (a : BitVec 64) :
    -(2 ^ 31) ≤ (montT a).toInt ∧ (montT a).toInt < 2 ^ 31 := by
  rw [montT_eq_signExtend]
  generalize BitVec.setWidth 32 (a * 58728449) = y
  have hle := BitVec.le_toInt y
  have hlt := @BitVec.toInt_lt 32 y
  rw [BitVec.toInt_signExtend, show min 64 32 = 32 from rfl,
    Int.bmod_eq_of_le (by simpa using hle) (by simpa using hlt)]
  exact ⟨by simpa using hle, by simpa using hlt⟩

/-! ## No-overflow: the products and subtraction stay in range -/

/-- `tq = t·q` does not overflow `int64`: `|t·q| < 2³¹·q < 2⁵⁴`. -/
theorem mont_tq_toInt (a : BitVec 64) :
    (montT a * 8380417).toInt = (montT a).toInt * 8380417 := by
  obtain ⟨hle, hlt⟩ := montT_toInt_bounds a
  rw [BitVec.toInt_mul]
  have hc : (8380417 : BitVec 64).toInt = 8380417 := by simp
  rw [hc]
  have b1 : -((2 : Int) ^ 64 / 2) ≤ (montT a).toInt * 8380417 := by
    have h := mul_le_mul_of_nonneg_right hle (by norm_num : (0 : Int) ≤ 8380417)
    norm_num at h ⊢; nlinarith [h]
  have b2 : (montT a).toInt * 8380417 < ((2 : Int) ^ 64 + 1) / 2 := by
    have h := mul_lt_mul_of_pos_right hlt (by norm_num : (0 : Int) < 8380417)
    norm_num at h ⊢; nlinarith [h]
  have := Int.bmod_eq_of_le (m := 2 ^ 64) (n := (montT a).toInt * 8380417) b1 b2
  simpa using this

/-- Under the FIPS-204 bound `|a.toInt| ≤ q·2³¹`, the subtraction `d = a − t·q`
    does not overflow, so `d.toInt = a.toInt − t.toInt·q` exactly. -/
theorem mont_d_toInt (a : BitVec 64)
    (ha_lo : -(8380417 * 2 ^ 31) ≤ a.toInt) (ha_hi : a.toInt ≤ 8380417 * 2 ^ 31) :
    (a - montT a * 8380417).toInt = a.toInt - (montT a).toInt * 8380417 := by
  obtain ⟨htle, htlt⟩ := montT_toInt_bounds a
  rw [BitVec.toInt_sub, mont_tq_toInt a]
  have b1 : -((2 : Int) ^ 64 / 2) ≤ a.toInt - (montT a).toInt * 8380417 := by
    have h := mul_lt_mul_of_pos_right htlt (by norm_num : (0 : Int) < 8380417)
    norm_num at h ha_lo ⊢; nlinarith [h, ha_lo]
  have b2 : a.toInt - (montT a).toInt * 8380417 < ((2 : Int) ^ 64 + 1) / 2 := by
    have h := mul_le_mul_of_nonneg_right htle (by norm_num : (0 : Int) ≤ 8380417)
    norm_num at h ha_hi ⊢; nlinarith [h, ha_hi]
  have := Int.bmod_eq_of_le (m := 2 ^ 64) (n := a.toInt - (montT a).toInt * 8380417) b1 b2
  simpa using this

/-! ## The abstract signed-Montgomery congruence -/

/-- **ML-DSA signed-Montgomery congruence.** For the emitted Montgomery-reduce
    form `mldsaMontgomeryForm` (`q = 8380417`, `QINV = 58728449`, `R = 2³²`),
    under the FIPS-204 no-overflow bound `|a| ≤ q·2³¹`,

    `(mldsaMontgomeryForm a).toInt · 2³² ≡ a.toInt (mod q)`.

    Equivalently `r·R ≡ a (mod q)`, the defining property of Montgomery reduction
    (`r ≡ a·R⁻¹ mod q`). Proved by `Int`/`ZMod` algebra — the divisibility of
    `a − t·q` by `2³²` (a mod-`2³²` fact reducing to the *constant* identity
    `QINV·q = 1` in `BitVec 32`), exact division by the arithmetic shift, and the
    no-overflow bound that makes the int64 subtraction exact. No 64×64 product is
    ever bit-blasted (the route `bv_decide` walled on). -/
theorem mldsaMontgomery_montgomery_congruence (a : BitVec 64)
    (ha_lo : -(8380417 * 2 ^ 31) ≤ a.toInt) (ha_hi : a.toInt ≤ 8380417 * 2 ^ 31) :
    (mldsaMontgomeryForm a).toInt * 2 ^ 32 ≡ a.toInt [ZMOD q] := by
  -- `mldsaMontgomeryForm a` is definitionally `sshiftRight (a − montT a * 8380417) 32`
  have hform : mldsaMontgomeryForm a
      = BitVec.sshiftRight (a - montT a * 8380417) 32 := rfl
  rw [hform, mont_shift_exact a, mont_d_toInt a ha_lo ha_hi]
  -- now: a.toInt − t.toInt·q ≡ a.toInt (mod q), since q ∣ t.toInt·q
  unfold q
  have : a.toInt - (montT a).toInt * 8380417 = a.toInt - 8380417 * (montT a).toInt := by ring
  rw [this]
  exact (Int.modEq_iff_dvd.mpr ⟨(montT a).toInt, by ring⟩)

/-- The same congruence stated as an explicit multiple of `q` (the multiple-of-`q`
    form `montgomery_reduce` removes, mirroring how `reduce32` stated its tie):
    `a − r·2³² = t·q` exactly, under the FIPS-204 bound. -/
theorem mldsaMontgomery_sub_eq_mul_q (a : BitVec 64)
    (ha_lo : -(8380417 * 2 ^ 31) ≤ a.toInt) (ha_hi : a.toInt ≤ 8380417 * 2 ^ 31) :
    a.toInt - (mldsaMontgomeryForm a).toInt * 2 ^ 32 = (montT a).toInt * 8380417 := by
  have hform : mldsaMontgomeryForm a
      = BitVec.sshiftRight (a - montT a * 8380417) 32 := rfl
  rw [hform, mont_shift_exact a, mont_d_toInt a ha_lo ha_hi]; ring

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaMontgomeryTie
