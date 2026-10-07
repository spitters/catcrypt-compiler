/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.Int.Notation

/-!
# FIPS 204 rounding functions over the integers

The definitions of the ML-DSA rounding, decomposition and hint algorithms of FIPS 204,
Section 7.4, as functions on `ℤ`: `Power2Round` (Algorithm 35), `Decompose`
(Algorithm 36), `HighBits` and `LowBits` (Algorithms 37 and 38), `MakeHint`
(Algorithm 39) and `UseHint` (Algorithm 40). The modulus is `q = 8380417` and the
dropped-bit count is `13`; `Decompose` and the functions derived from it take `γ₂` as an
argument.

This module holds the definitions only and imports nothing beyond the integers. The
specification module `MLDSA.Spec.Rounding` proves the range and round-trip properties, and
`VIR.RoundCodec` proves that the word templates compute these functions.

## Main definitions

* `Fips204.q`, `Fips204.twoPowD`: the modulus and `2 ^ 13`.
* `Fips204.modPm`: the centred remainder `r mod± α` in `(-α/2, α/2]`.
* `Fips204.power2Round`, `Fips204.decompose`, `Fips204.highBits`, `Fips204.lowBits`,
  `Fips204.makeHint`, `Fips204.useHint`: Algorithms 35 to 40.

## References
* NIST FIPS 204 (2024), Section 7.4, Algorithms 35-40
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RoundCodec.Fips204

/-- The ML-DSA modulus. -/
def q : ℤ := 8380417

/-- `2 ^ 13`, the `Power2Round` scaling factor. -/
def twoPowD : ℤ := 8192

/-- `modPm x α` is the representative of `x` modulo `α` in `(-α/2, α/2]`,
for even `α`. -/
def modPm (x α : ℤ) : ℤ :=
  let r := x % α
  if r > α / 2 then r - α else r

/-- `Power2Round` (FIPS 204, Algorithm 35): splits `r mod q` into a high part
scaled by `2 ^ 13` and a centred low part. -/
def power2Round (r : ℤ) : ℤ × ℤ :=
  let rp := r % q
  let r0 := modPm rp twoPowD
  ((rp - r0) / twoPowD, r0)

/-- `Decompose` (FIPS 204, Algorithm 36): splits `r mod q` into a high part
scaled by `2 * γ2` and a centred low part, with the high part wrapped to `0`
at the top of the range. -/
def decompose (γ2 r : ℤ) : ℤ × ℤ :=
  let rp := r % q
  let r0 := modPm rp (2 * γ2)
  if rp - r0 = q - 1 then (0, r0 - 1) else ((rp - r0) / (2 * γ2), r0)

/-- `HighBits` (FIPS 204, Algorithm 37). -/
def highBits (γ2 r : ℤ) : ℤ := (decompose γ2 r).1

/-- `LowBits` (FIPS 204, Algorithm 38). -/
def lowBits (γ2 r : ℤ) : ℤ := (decompose γ2 r).2

/-- `MakeHint` (FIPS 204, Algorithm 39): whether adding `z` changes the high
bits of `r`. -/
def makeHint (γ2 z r : ℤ) : Bool := decide (highBits γ2 r ≠ highBits γ2 (r + z))

/-- `UseHint` (FIPS 204, Algorithm 40): recovers the high bits of `r + z` from
the high bits of `r` and the hint bit. -/
def useHint (γ2 : ℤ) (h : Bool) (r : ℤ) : ℤ :=
  let m := (q - 1) / (2 * γ2)
  let r1 := (decompose γ2 r).1
  let r0 := (decompose γ2 r).2
  if h = true ∧ 0 < r0 then (r1 + 1) % m
  else if h = true then (r1 - 1) % m
  else r1

end CatCrypt.Crypto.SecureCompilation.VIR.RoundCodec.Fips204
