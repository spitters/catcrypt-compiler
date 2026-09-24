/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontPallas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Pallas `G1` PROJECTIVE (Jacobian) point-add / point-double over the abstract base field

`RelationalFrontPallas.lean` realizes the Pallas base-field **ADD** and **MUL** relationally
over a 4×64-bit limb carrier (the abstract `ZMod pallasQ` add/mul through the emitted reducing
kernels).  This module advances the multi-limb-EC-over-Pallas residual at the next level up:
the `G1` **elliptic-curve point-add / point-double coordinate formulas**, written over the
abstract base field `ZMod pallasQ`, proved to realize the affine short-Weierstrass group law
in the generic chart.

It mirrors `RelationalFrontBls377EC.lean` (which does exactly this for BLS12-377 over
`ZMod bls377Q`), but over the Pallas base field and self-contained (Pallas's `G1` is
`y² = x³ + 5`, i.e. `a = 0`, `b = 5`; the chord/tangent coordinate maps do not depend on `b`,
so the realization ties below are `b`-agnostic — identical algebra to the BLS12-377 case).

## The abstract field

The Pallas base field is `ZMod pallasQ` for the 255-bit prime `pallasQ`
(defined in `RelationalFrontPallas.lean`).  The repo carries `pallasQ` as a `Nat` modulus
(the canonical Pasta Pallas base prime).  We parameterize the realization ties by a
**hypothesis** `[Fact (Nat.Prime pallasQ)]` (a section variable — *not* an asserted axiom,
so the file stays axiom-clean): under that hypothesis Mathlib infers `Field (ZMod pallasQ)`,
and the small numerals `2, 3` are nonzero (the characteristic is the 255-bit prime, far
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

`pallasJacToAffine (X,Y,Z) = (X·(Z²)⁻¹, Y·(Z³)⁻¹)` (one inverse, of `Z`).  The headline ties
are pure field-algebra identities:

* `pallas_jacDouble_realizes_affineDbl` — `pallasJacToAffine (pallasJacDouble (x,y,1)) =
  pallasAffineDbl (pallasTangentSlope x y) (x,y)`;
* `pallas_jacAdd_realizes_affineAdd` — `pallasJacToAffine (pallasJacAddZ1 (x₁,y₁,1) (x₂,y₂,1))
  = pallasAffineAdd ((y₂−y₁)·(x₂−x₁)⁻¹) (x₁,y₁) (x₂,y₂)` (distinct `x`).

So the projective group law, projected back to affine via *one* inverse, equals the affine
short-Weierstrass group law — the projective accumulation computes the same `G1` group
element, with the inverse amortized to the final conversion.

## Scope

The ties are the **generic-chart** identities (`Z = 1`, distinct/doubling branches, nonzero
`y`), which hold by `field_simp; ring`.  The exceptional cases (vertical line / point at
infinity) and the all-pairs group-law completeness are *not* attempted here — exactly the
generic-chart scope of the BLS12-377 version.

All goals closed; no new custom axioms (primality is a section hypothesis, not an asserted axiom);
the field-algebra ties are unconditional given the field structure.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

/-! ## 1. The abstract Pallas base field, and small-numeral nonvanishing

Under the (hypothesized) primality of `pallasQ`, `ZMod pallasQ` is a field, and the small
constants `2, 3` introduced by `dbl-2009-l` / the tangent slope are nonzero (the
characteristic is the 255-bit prime, far larger than `3`). -/

section Field

variable [Fact (Nat.Prime pallasQ)]

/-- A nonzero `Nat` below `pallasQ` is nonzero in `ZMod pallasQ` (the characteristic is the
    prime, which exceeds `n`).  Mirrors `bls377_natCast_ne_zero`. -/
theorem pallas_natCast_ne_zero (n : ℕ) (h0 : 0 < n) (hlt : n < pallasQ) :
    ((n : ℕ) : ZMod pallasQ) ≠ 0 := by
  intro hz
  have hdvd : (pallasQ : ℕ) ∣ n := (CharP.cast_eq_zero_iff (ZMod pallasQ) pallasQ n).mp hz
  exact absurd (Nat.le_of_dvd h0 hdvd) (by omega)

/-- A small numeral literal is nonzero in `ZMod pallasQ`. -/
theorem pallas_nz (n : ℕ) (h0 : 0 < n) (hlt : n < pallasQ) : (n : ZMod pallasQ) ≠ 0 := by
  have := pallas_natCast_ne_zero n h0 hlt; exact_mod_cast this

theorem pallas_two_ne_zero : (2 : ZMod pallasQ) ≠ 0 :=
  pallas_nz 2 (by norm_num) (by norm_num [pallasQ])
theorem pallas_three_ne_zero : (3 : ZMod pallasQ) ≠ 0 :=
  pallas_nz 3 (by norm_num) (by norm_num [pallasQ])
theorem pallas_four_ne_zero : (4 : ZMod pallasQ) ≠ 0 :=
  pallas_nz 4 (by norm_num) (by norm_num [pallasQ])
theorem pallas_eight_ne_zero : (8 : ZMod pallasQ) ≠ 0 :=
  pallas_nz 8 (by norm_num) (by norm_num [pallasQ])

end Field

/-! ## 2. The affine `G1` point and the chord/tangent coordinate maps

The short-Weierstrass affine point-add (distinct points) and point-double (tangent)
coordinate formulas over `ZMod pallasQ`, written field-agnostically (built only from
`*`/`+`/`−`/`⁻¹`).  Exactly mirror `bls377AffineRx`/`bls377AffineRy`/`bls377AffineAdd`/
`bls377TangentSlope`/`bls377AffineDbl`. -/

/-- An affine Pallas `G1` point `(x, y)` over the base field `ZMod pallasQ`. -/
structure PallasPoint where
  /-- Affine `x`-coordinate. -/
  x : ZMod pallasQ
  /-- Affine `y`-coordinate. -/
  y : ZMod pallasQ

/-- The short-Weierstrass affine point-add `x`-coordinate map: `x₃ = λ² − x₁ − x₂`. -/
def pallasAffineRx (lam x1 x2 : ZMod pallasQ) : ZMod pallasQ := lam * lam - x1 - x2

/-- The short-Weierstrass affine point-add `y`-coordinate map: `y₃ = λ·(x₁ − x₃) − y₁`. -/
def pallasAffineRy (lam x1 x3 y1 : ZMod pallasQ) : ZMod pallasQ := lam * (x1 - x3) - y1

/-- The full affine point-add coordinate formula, given the precomputed chord slope `λ`. -/
def pallasAffineAdd (lam : ZMod pallasQ) (P Q : PallasPoint) : PallasPoint :=
  let x3 := pallasAffineRx lam P.x Q.x
  { x := x3, y := pallasAffineRy lam P.x x3 P.y }

/-- The short-Weierstrass tangent slope at an affine point `(x, y)` on `y² = x³ + 5`
    (`a = 0`): `λ = (3·x²)·(2·y)⁻¹`. -/
def pallasTangentSlope (x y : ZMod pallasQ) : ZMod pallasQ := (3 * (x * x)) * (2 * y)⁻¹

/-- The full affine point-double coordinate formula, given the precomputed tangent slope `λ`.
    Reuses `pallasAffineRx`/`pallasAffineRy` with `x₂ = x₁ = x`. -/
def pallasAffineDbl (lam : ZMod pallasQ) (P : PallasPoint) : PallasPoint :=
  let x3 := pallasAffineRx lam P.x P.x
  { x := x3, y := pallasAffineRy lam P.x x3 P.y }

/-! ## 3. The Jacobian point and the inversion-free projective group law

A Jacobian point `(X, Y, Z)` represents the affine point `(X·Z⁻², Y·Z⁻³)`.  The
`dbl-2009-l` / `add-2007-bl` formulas for `a = 0` compute the group law with **no inverse**
(only `*`/`+`/`−`); the single inverse is deferred to the final affine conversion
`pallasJacToAffine`. -/

/-- A Jacobian projective `G1` point `(X, Y, Z)` over `ZMod pallasQ`.  Represents the affine
    point `(X·Z⁻², Y·Z⁻³)`; `Z = 0` is the point at infinity. -/
structure PallasJacPoint where
  /-- Jacobian `X`. -/
  X : ZMod pallasQ
  /-- Jacobian `Y`. -/
  Y : ZMod pallasQ
  /-- Jacobian `Z` (`Z = 0` ⇒ point at infinity). -/
  Z : ZMod pallasQ

/-- The affine-embedding of an affine point `(x, y)` as the Jacobian point `(x, y, 1)`. -/
def PallasJacPoint.ofAffine (P : PallasPoint) : PallasJacPoint := { X := P.x, Y := P.y, Z := 1 }

/-- The **one-inverse** Jacobian→affine conversion `(X, Y, Z) ↦ (X·(Z²)⁻¹, Y·(Z³)⁻¹)`. -/
def pallasJacToAffine (J : PallasJacPoint) : PallasPoint :=
  { x := J.X * (J.Z ^ 2)⁻¹, y := J.Y * (J.Z ^ 3)⁻¹ }

/-- The `dbl-2009-l` Jacobian point-double for `a = 0`: `S = 4XY²`, `M = 3X²`,
    `X' = M² − 2S`, `Y' = M·(S − X') − 8Y⁴`, `Z' = 2YZ`.  **No inverse.** -/
def pallasJacDouble (J : PallasJacPoint) : PallasJacPoint :=
  let S := 4 * J.X * J.Y ^ 2
  let M := 3 * J.X ^ 2
  let Xp := M ^ 2 - 2 * S
  { X := Xp, Y := M * (S - Xp) - 8 * J.Y ^ 4, Z := 2 * J.Y * J.Z }

/-- The `add-2007-bl` Jacobian point-add in the `Z = 1` chart (both inputs affine, the
    mixed-add form the windowed / Pippenger loops drive): `H = X₂ − X₁`, `r = Y₂ − Y₁`,
    `X' = r² − H³ − 2X₁H²`, `Y' = r·(X₁H² − X') − Y₁H³`, `Z' = H`.  **No inverse.** -/
def pallasJacAddZ1 (J K : PallasJacPoint) : PallasJacPoint :=
  let H := K.X - J.X
  let r := K.Y - J.Y
  let Xp := r ^ 2 - H ^ 3 - 2 * J.X * H ^ 2
  { X := Xp, Y := r * (J.X * H ^ 2 - Xp) - J.Y * H ^ 3, Z := H }

/-! ## 4. The denote-tie to the affine group law (the correctness oracle)

`pallasJacToAffine` of the projective double/add, on affine-embedded inputs, equals the affine
`pallasAffineDbl`/`pallasAffineAdd` at the same chord/tangent slope.  Pure field-algebra
identities — the projective accumulation computes the same `G1` group element, with the
inverse amortized.  These require the field structure (`Fact (Nat.Prime pallasQ)`). -/

section Realization

variable [Fact (Nat.Prime pallasQ)]

/-- **The projective double realizes the affine double.**  Converting the `dbl-2009-l`
    Jacobian double of the affine-embedded `(x, y)` back to affine (one inverse) yields
    exactly `pallasAffineDbl` at the tangent slope — in the generic chart (`y ≠ 0`). -/
theorem pallas_jacDouble_realizes_affineDbl (P : PallasPoint) (hy : P.y ≠ 0) :
    pallasJacToAffine (pallasJacDouble (PallasJacPoint.ofAffine P))
      = pallasAffineDbl (pallasTangentSlope P.x P.y) P := by
  have h2 : (2 : ZMod pallasQ) ≠ 0 := pallas_two_ne_zero
  have h3 : (3 : ZMod pallasQ) ≠ 0 := pallas_three_ne_zero
  have h4 : (4 : ZMod pallasQ) ≠ 0 := pallas_four_ne_zero
  have h8 : (8 : ZMod pallasQ) ≠ 0 := pallas_eight_ne_zero
  obtain ⟨x, y⟩ := P
  refine PallasPoint.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [pallasJacDouble, PallasJacPoint.ofAffine, pallasAffineRx,
      pallasTangentSlope, mul_one]
    field_simp [hy, h2, h3, h4, h8]
    ring
  · simp only [pallasJacDouble, PallasJacPoint.ofAffine, pallasAffineRx,
      pallasAffineRy, pallasTangentSlope, mul_one]
    field_simp [hy, h2, h3, h4, h8]
    ring

/-- **The projective add realizes the affine add (distinct points).**  Converting the
    `add-2007-bl` Jacobian add of two affine-embedded distinct points back to affine (one
    inverse) yields exactly `pallasAffineAdd` at the chord slope — generic chart
    (`x₂ ≠ x₁`). -/
theorem pallas_jacAdd_realizes_affineAdd (P Q : PallasPoint) (hx : Q.x - P.x ≠ 0) :
    pallasJacToAffine (pallasJacAddZ1 (PallasJacPoint.ofAffine P) (PallasJacPoint.ofAffine Q))
      = pallasAffineAdd ((Q.y - P.y) * (Q.x - P.x)⁻¹) P Q := by
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  refine PallasPoint.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [pallasJacAddZ1, PallasJacPoint.ofAffine, pallasAffineRx]
    field_simp
    ring
  · simp only [pallasJacAddZ1, PallasJacPoint.ofAffine, pallasAffineRx,
      pallasAffineRy]
    field_simp
    ring

end Realization

end CatCrypt.Crypto.SecureCompilation.RelationalFront
