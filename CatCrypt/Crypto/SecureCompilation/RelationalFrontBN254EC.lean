/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RelationalFrontBN254
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# BN254 `G1` PROJECTIVE (Jacobian) point-add / point-double over the abstract base field

`RelationalFrontBN254.lean` realizes the BN254 base-field **ADD** and **MUL** relationally
over a 4×64-bit limb carrier (the abstract `ZMod bn254Q` add/mul through the emitted reducing
kernels).  This module advances the multi-limb-EC-over-BN254 residual at the next level up:
the `G1` **elliptic-curve point-add / point-double coordinate formulas**, written over the
abstract base field `ZMod bn254Q`, proved to realize the affine short-Weierstrass group law
in the generic chart.

It mirrors `RelationalFrontPallasEC.lean` (which does exactly this for Pallas over
`ZMod pallasQ`), but over the BN254 base field and self-contained (BN254's `G1` is
`y² = x³ + 3`, i.e. `a = 0`, `b = 3`; the chord/tangent coordinate maps do not depend on `b`,
so the realization ties below are `b`-agnostic — identical algebra to the Pallas case).

## The abstract field

The BN254 base field is `ZMod bn254Q` for the genuine 254-bit prime `bn254Q`
(defined in `RelationalFrontBN254.lean`).  The repo carries `bn254Q` as a `Nat` modulus
(the canonical alt_bn128 / Barreto–Naehrig base prime).  We parameterize the realization ties
by a **hypothesis** `[Fact (Nat.Prime bn254Q)]` (a section variable — *not* an asserted axiom,
so the file stays axiom-clean): under that hypothesis Mathlib infers `Field (ZMod bn254Q)`,
and the small numerals `2, 3` are nonzero (the characteristic is the 254-bit prime, far
larger than `2` or `3`).

## The Jacobian group law (the spec the field-leaf schedule realizes)

For `a = 0`:

**`dbl-2009-l`** (point double `2·(X,Y,Z)`):
```
   S = 4·X·Y² ; M = 3·X² ; X' = M² − 2S ; Y' = M·(S − X') − 8·Y⁴ ; Z' = 2·Y·Z
```
**`add-2007-bl`** (point add, `Z₁ = Z₂ = 1` mixed-add chart — affine table point into a
Jacobian accumulator):
```
   H = X₂ − X₁ ; r = Y₂ − Y₁ ;
   X' = r² − H³ − 2·X₁·H² ; Y' = r·(X₁·H² − X') − Y₁·H³ ; Z' = H
```

## The denote-tie to the affine group law (the correctness oracle)

`bn254JacToAffine (X,Y,Z) = (X·(Z²)⁻¹, Y·(Z³)⁻¹)` (one inverse, of `Z`).  The headline ties
are pure field-algebra identities:

* `bn254_jacDouble_realizes_affineDbl` — `bn254JacToAffine (bn254JacDouble (x,y,1)) =
  bn254AffineDbl (bn254TangentSlope x y) (x,y)`;
* `bn254_jacAdd_realizes_affineAdd` — `bn254JacToAffine (bn254JacAddZ1 (x₁,y₁,1) (x₂,y₂,1))
  = bn254AffineAdd ((y₂−y₁)·(x₂−x₁)⁻¹) (x₁,y₁) (x₂,y₂)` (distinct `x`).

So the projective group law, projected back to affine via *one* inverse, equals the affine
short-Weierstrass group law — the projective accumulation computes the same `G1` group
element, with the inverse amortized to the final conversion.

## Scope (the honest caveat)

The ties are the **generic-chart** identities (`Z = 1`, distinct/doubling branches, nonzero
`y`), which hold by `field_simp; ring`.  The exceptional cases (vertical line / point at
infinity) and the all-pairs group-law completeness are *not* attempted here — exactly the
generic-chart scope of the Pallas version.

0 sorries; no new custom axioms (primality is a section hypothesis, not an asserted axiom);
the field-algebra ties are unconditional given the field structure.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

/-! ## 1. The abstract BN254 base field, and small-numeral nonvanishing

Under the (hypothesized) primality of `bn254Q`, `ZMod bn254Q` is a field, and the small
constants `2, 3` introduced by `dbl-2009-l` / the tangent slope are nonzero (the
characteristic is the 254-bit prime, far larger than `3`). -/

section Field

variable [Fact (Nat.Prime bn254Q)]

/-- A nonzero `Nat` below `bn254Q` is nonzero in `ZMod bn254Q` (the characteristic is the
    prime, which exceeds `n`).  Mirrors `pallas_natCast_ne_zero`. -/
theorem bn254_natCast_ne_zero (n : ℕ) (h0 : 0 < n) (hlt : n < bn254Q) :
    ((n : ℕ) : ZMod bn254Q) ≠ 0 := by
  intro hz
  have hdvd : (bn254Q : ℕ) ∣ n := (CharP.cast_eq_zero_iff (ZMod bn254Q) bn254Q n).mp hz
  exact absurd (Nat.le_of_dvd h0 hdvd) (by omega)

/-- A small numeral literal is nonzero in `ZMod bn254Q`. -/
theorem bn254_nz (n : ℕ) (h0 : 0 < n) (hlt : n < bn254Q) : (n : ZMod bn254Q) ≠ 0 := by
  have := bn254_natCast_ne_zero n h0 hlt; exact_mod_cast this

theorem bn254_two_ne_zero : (2 : ZMod bn254Q) ≠ 0 :=
  bn254_nz 2 (by norm_num) (by norm_num [bn254Q])
theorem bn254_three_ne_zero : (3 : ZMod bn254Q) ≠ 0 :=
  bn254_nz 3 (by norm_num) (by norm_num [bn254Q])
theorem bn254_four_ne_zero : (4 : ZMod bn254Q) ≠ 0 :=
  bn254_nz 4 (by norm_num) (by norm_num [bn254Q])
theorem bn254_eight_ne_zero : (8 : ZMod bn254Q) ≠ 0 :=
  bn254_nz 8 (by norm_num) (by norm_num [bn254Q])

end Field

/-! ## 2. The affine `G1` point and the chord/tangent coordinate maps

The short-Weierstrass affine point-add (distinct points) and point-double (tangent)
coordinate formulas over `ZMod bn254Q`, written field-agnostically (built only from
`*`/`+`/`−`/`⁻¹`).  Exactly mirror `pallasAffineRx`/`pallasAffineRy`/`pallasAffineAdd`/
`pallasTangentSlope`/`pallasAffineDbl`. -/

/-- An affine BN254 `G1` point `(x, y)` over the base field `ZMod bn254Q`. -/
structure BN254Point where
  /-- Affine `x`-coordinate. -/
  x : ZMod bn254Q
  /-- Affine `y`-coordinate. -/
  y : ZMod bn254Q

/-- The short-Weierstrass affine point-add `x`-coordinate map: `x₃ = λ² − x₁ − x₂`. -/
def bn254AffineRx (lam x1 x2 : ZMod bn254Q) : ZMod bn254Q := lam * lam - x1 - x2

/-- The short-Weierstrass affine point-add `y`-coordinate map: `y₃ = λ·(x₁ − x₃) − y₁`. -/
def bn254AffineRy (lam x1 x3 y1 : ZMod bn254Q) : ZMod bn254Q := lam * (x1 - x3) - y1

/-- The full affine point-add coordinate formula, given the precomputed chord slope `λ`. -/
def bn254AffineAdd (lam : ZMod bn254Q) (P Q : BN254Point) : BN254Point :=
  let x3 := bn254AffineRx lam P.x Q.x
  { x := x3, y := bn254AffineRy lam P.x x3 P.y }

/-- The short-Weierstrass tangent slope at an affine point `(x, y)` on `y² = x³ + 3`
    (`a = 0`): `λ = (3·x²)·(2·y)⁻¹`. -/
def bn254TangentSlope (x y : ZMod bn254Q) : ZMod bn254Q := (3 * (x * x)) * (2 * y)⁻¹

/-- The full affine point-double coordinate formula, given the precomputed tangent slope `λ`.
    Reuses `bn254AffineRx`/`bn254AffineRy` with `x₂ = x₁ = x`. -/
def bn254AffineDbl (lam : ZMod bn254Q) (P : BN254Point) : BN254Point :=
  let x3 := bn254AffineRx lam P.x P.x
  { x := x3, y := bn254AffineRy lam P.x x3 P.y }

/-! ## 3. The Jacobian point and the inversion-free projective group law

A Jacobian point `(X, Y, Z)` represents the affine point `(X·Z⁻², Y·Z⁻³)`.  The
`dbl-2009-l` / `add-2007-bl` formulas for `a = 0` compute the group law with **no inverse**
(only `*`/`+`/`−`); the single inverse is deferred to the final affine conversion
`bn254JacToAffine`. -/

/-- A Jacobian projective `G1` point `(X, Y, Z)` over `ZMod bn254Q`.  Represents the affine
    point `(X·Z⁻², Y·Z⁻³)`; `Z = 0` is the point at infinity. -/
structure BN254JacPoint where
  /-- Jacobian `X`. -/
  X : ZMod bn254Q
  /-- Jacobian `Y`. -/
  Y : ZMod bn254Q
  /-- Jacobian `Z` (`Z = 0` ⇒ point at infinity). -/
  Z : ZMod bn254Q

/-- The affine-embedding of an affine point `(x, y)` as the Jacobian point `(x, y, 1)`. -/
def BN254JacPoint.ofAffine (P : BN254Point) : BN254JacPoint := { X := P.x, Y := P.y, Z := 1 }

/-- The **one-inverse** Jacobian→affine conversion `(X, Y, Z) ↦ (X·(Z²)⁻¹, Y·(Z³)⁻¹)`. -/
def bn254JacToAffine (J : BN254JacPoint) : BN254Point :=
  { x := J.X * (J.Z ^ 2)⁻¹, y := J.Y * (J.Z ^ 3)⁻¹ }

/-- The `dbl-2009-l` Jacobian point-double for `a = 0`: `S = 4XY²`, `M = 3X²`,
    `X' = M² − 2S`, `Y' = M·(S − X') − 8Y⁴`, `Z' = 2YZ`.  **No inverse.** -/
def bn254JacDouble (J : BN254JacPoint) : BN254JacPoint :=
  let S := 4 * J.X * J.Y ^ 2
  let M := 3 * J.X ^ 2
  let Xp := M ^ 2 - 2 * S
  { X := Xp, Y := M * (S - Xp) - 8 * J.Y ^ 4, Z := 2 * J.Y * J.Z }

/-- The `add-2007-bl` Jacobian point-add in the `Z = 1` chart (both inputs affine, the
    mixed-add form the windowed / Pippenger loops drive): `H = X₂ − X₁`, `r = Y₂ − Y₁`,
    `X' = r² − H³ − 2X₁H²`, `Y' = r·(X₁H² − X') − Y₁H³`, `Z' = H`.  **No inverse.** -/
def bn254JacAddZ1 (J K : BN254JacPoint) : BN254JacPoint :=
  let H := K.X - J.X
  let r := K.Y - J.Y
  let Xp := r ^ 2 - H ^ 3 - 2 * J.X * H ^ 2
  { X := Xp, Y := r * (J.X * H ^ 2 - Xp) - J.Y * H ^ 3, Z := H }

/-! ## 4. The denote-tie to the affine group law (the correctness oracle)

`bn254JacToAffine` of the projective double/add, on affine-embedded inputs, equals the affine
`bn254AffineDbl`/`bn254AffineAdd` at the same chord/tangent slope.  Pure field-algebra
identities — the projective accumulation computes the same `G1` group element, with the
inverse amortized.  These require the field structure (`Fact (Nat.Prime bn254Q)`). -/

section Realization

variable [Fact (Nat.Prime bn254Q)]

/-- **The projective double realizes the affine double.**  Converting the `dbl-2009-l`
    Jacobian double of the affine-embedded `(x, y)` back to affine (one inverse) yields
    exactly `bn254AffineDbl` at the tangent slope — in the generic chart (`y ≠ 0`). -/
theorem bn254_jacDouble_realizes_affineDbl (P : BN254Point) (hy : P.y ≠ 0) :
    bn254JacToAffine (bn254JacDouble (BN254JacPoint.ofAffine P))
      = bn254AffineDbl (bn254TangentSlope P.x P.y) P := by
  have h2 : (2 : ZMod bn254Q) ≠ 0 := bn254_two_ne_zero
  have h3 : (3 : ZMod bn254Q) ≠ 0 := bn254_three_ne_zero
  have h4 : (4 : ZMod bn254Q) ≠ 0 := bn254_four_ne_zero
  have h8 : (8 : ZMod bn254Q) ≠ 0 := bn254_eight_ne_zero
  obtain ⟨x, y⟩ := P
  refine BN254Point.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [bn254JacDouble, BN254JacPoint.ofAffine, bn254AffineRx,
      bn254TangentSlope, mul_one]
    field_simp [hy, h2, h3, h4, h8]
    ring
  · simp only [bn254JacDouble, BN254JacPoint.ofAffine, bn254AffineRx,
      bn254AffineRy, bn254TangentSlope, mul_one]
    field_simp [hy, h2, h3, h4, h8]
    ring

/-- **The projective add realizes the affine add (distinct points).**  Converting the
    `add-2007-bl` Jacobian add of two affine-embedded distinct points back to affine (one
    inverse) yields exactly `bn254AffineAdd` at the chord slope — generic chart
    (`x₂ ≠ x₁`). -/
theorem bn254_jacAdd_realizes_affineAdd (P Q : BN254Point) (hx : Q.x - P.x ≠ 0) :
    bn254JacToAffine (bn254JacAddZ1 (BN254JacPoint.ofAffine P) (BN254JacPoint.ofAffine Q))
      = bn254AffineAdd ((Q.y - P.y) * (Q.x - P.x)⁻¹) P Q := by
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  refine BN254Point.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [bn254JacAddZ1, BN254JacPoint.ofAffine, bn254AffineRx]
    field_simp
    ring
  · simp only [bn254JacAddZ1, BN254JacPoint.ofAffine, bn254AffineRx,
      bn254AffineRy]
    field_simp
    ring

end Realization

end CatCrypt.Crypto.SecureCompilation.RelationalFront
