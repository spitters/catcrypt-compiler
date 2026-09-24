/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# Exactness of the du = 10 compression magic number

`magic10_exact`: for every ML-KEM coefficient `x < 3329`, the multiply/shift form
`(((x<<10)+1665)·1290167) >> 32 & 0x3ff` equals the FIPS 203 rounding division
`(((x<<10)+1664)/3329) & 0x3ff`.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BarrettCompress10Exact

/-- The `polyvec_compress` (du = 10) magic-number form, matching
    `CompressEmit.magicCompress10`:
    `(((x<<10)+1665)·1290167) >> 32 & 0x3ff`. -/
def magicC10 (x : Nat) : Nat :=
  ((((x <<< 10) + 1665) * 1290167) >>> 32) &&& 1023

/-- The FIPS-203 rounding division for du = 10, matching
    `CompressEmit.refDivCompress 10`:
    `(((x<<10)+1664)/3329) & 0x3ff`. -/
def refC10 (x : Nat) : Nat :=
  (((x <<< 10) + 1664) / 3329) &&& 1023

/-- The central quotient identity: the round-down reciprocal multiply/shift
    equals the true rounding division, for every coefficient `x ∈ [0, 3329)`.
    `1290167 = ⌊2^32/3329⌋`, `3329·1290167 = 2^32 − 1353`. -/
theorem magic10_quot (x : Nat) (hx : x < 3329) :
    (((x * 1024 + 1665) * 1290167) / 4294967296) = ((x * 1024 + 1664) / 3329) := by
  have hdm := Nat.div_add_mod (x * 1024 + 1664) 3329
  have hmod : (x * 1024 + 1664) % 3329 < 3329 := Nat.mod_lt _ (by omega)
  -- The round-down reciprocal `1290167 = ⌊2^32/3329⌋` satisfies
  -- `3329·1290167 = 2^32 − 1353`, so the numerator increment `+1665` (vs `+1664`)
  -- compensates the under-approximation `1353·N/2^32`.  The only place the two
  -- quotients could diverge is when the true remainder is `0` *and* the quotient
  -- exceeds `953` (`1353·954 > 1290167`); but `3329·q = 1024·x + 1664` with
  -- `x < 3329` forces `q ≡ 640 (mod 1024)`, so that quotient is `640 ≤ 953`.
  -- The `r = 0` vs `r ≥ 1` split hands `omega` exactly this modular obstruction.
  have hcore : 1353 * ((x * 1024 + 1664) / 3329)
      ≤ ((x * 1024 + 1664) % 3329 + 1) * 1290167 := by
    rcases Nat.lt_or_ge ((x * 1024 + 1664) % 3329) 1 with h | h <;> omega
  omega

/-- **Reciprocal exactness, du = 10.** The magic-number multiply/shift equals the
    rounding division-by-`3329`, for every coefficient `x ∈ [0, 3329)`. -/
theorem magic10_exact (x : Nat) (hx : x < 3329) : magicC10 x = refC10 x := by
  unfold magicC10 refC10
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 10 = 1024 from rfl, show (2 : Nat) ^ 32 = 4294967296 from rfl,
    magic10_quot x hx]
