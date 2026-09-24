/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Add
public import Mathlib.Tactic.NormNum.Prime
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Add
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# BLS12-377 `G1` PROJECTIVE (Jacobian) point-add / point-double over the abstract base field

`RelationalFrontBls377Add.lean` realizes the `bls12_377` base-field **ADD** relationally
over a 6×64-bit limb carrier (the abstract `ZMod bls377Q` add through the emitted reducing
kernel).  This module advances the multi-limb-EC-over-`bls12_377` residual at the next
level up: the `G1` **elliptic-curve point-add / point-double coordinate formulas**, written
over the abstract base field `ZMod bls377Q`, proved to realize the affine short-Weierstrass
group law in the generic chart.

It mirrors `Pairing/BLS12381ProjectiveEmit.lean` (which does exactly this for BLS12-381 over
`FpBLS`), but over the `bls12_377` base field and self-contained (BLS12-377's `G1` is
`y² = x³ + 1`, i.e. `a = 0`, `b = 1`; the chord/tangent coordinate maps do not depend on `b`,
so the realization ties below are `b`-agnostic — identical algebra to the BLS12-381 case).

## The abstract field

The `bls12_377` base field is `ZMod bls377Q` for the 377-bit prime `bls377Q`
(defined in `RelationalFrontBls377Add.lean`).  The repo carries `bls377Q` only as a `Nat`
modulus (its primality is the well-known SnarkVM/Zexe base-field characteristic, not
discharged in Lean — a 377-bit Miller–Rabin does not terminate under `native_decide`).  We
therefore parameterize the realization ties by a **hypothesis** `[Fact (Nat.Prime bls377Q)]`
(a section variable — *not* an asserted axiom, so the file stays axiom-clean): under that
hypothesis Mathlib infers `Field (ZMod bls377Q)`, and the small numerals `2, 3` are nonzero
(the characteristic is the 377-bit prime, far larger than `2` or `3`).

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

`bls377JacToAffine (X,Y,Z) = (X·(Z²)⁻¹, Y·(Z³)⁻¹)` (one inverse, of `Z`).  The headline ties
are pure field-algebra identities:

* `bls377_jacDouble_realizes_affineDbl` — `bls377JacToAffine (bls377JacDouble (x,y,1)) =
  bls377AffineDbl (bls377TangentSlope x y) (x,y)`;
* `bls377_jacAdd_realizes_affineAdd` — `bls377JacToAffine (bls377JacAddZ1 (x₁,y₁,1) (x₂,y₂,1))
  = bls377AffineAdd ((y₂−y₁)·(x₂−x₁)⁻¹) (x₁,y₁) (x₂,y₂)` (distinct `x`).

So the projective group law, projected back to affine via *one* inverse, equals the affine
short-Weierstrass group law — the projective accumulation computes the same `G1` group
element, with the inverse amortized to the final conversion.

## Scope

The ties are the **generic-chart** identities (`Z = 1`, distinct/doubling branches, nonzero
`y`), which hold by `field_simp; ring`.  The exceptional cases (vertical line / point at
infinity) and the all-pairs group-law completeness are *not* attempted here — exactly the
generic-chart scope of the BLS12-381 version.

0 sorries; no new custom axioms (primality is a section hypothesis, not an asserted axiom);
the field-algebra ties are unconditional given the field structure.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

/-! ## 1. The abstract `bls12_377` base field, and small-numeral nonvanishing

Under the (hypothesized) primality of `bls377Q`, `ZMod bls377Q` is a field, and the small
constants `2, 3` introduced by `dbl-2009-l` / the tangent slope are nonzero (the
characteristic is the 377-bit prime, far larger than `3`). -/

section Field

variable [Fact (Nat.Prime bls377Q)]

/-- A nonzero `Nat` below `bls377Q` is nonzero in `ZMod bls377Q` (the characteristic is the
    prime, which exceeds `n`).  Mirrors `BLS12381ProjectiveEmit.fp_natCast_ne_zero`. -/
theorem bls377_natCast_ne_zero (n : ℕ) (h0 : 0 < n) (hlt : n < bls377Q) :
    ((n : ℕ) : ZMod bls377Q) ≠ 0 := by
  intro hz
  have hdvd : (bls377Q : ℕ) ∣ n := (CharP.cast_eq_zero_iff (ZMod bls377Q) bls377Q n).mp hz
  exact absurd (Nat.le_of_dvd h0 hdvd) (by omega)

/-- A small numeral literal is nonzero in `ZMod bls377Q`. -/
theorem bls377_nz (n : ℕ) (h0 : 0 < n) (hlt : n < bls377Q) : (n : ZMod bls377Q) ≠ 0 := by
  have := bls377_natCast_ne_zero n h0 hlt; exact_mod_cast this

theorem bls377_two_ne_zero : (2 : ZMod bls377Q) ≠ 0 :=
  bls377_nz 2 (by norm_num) (by norm_num [bls377Q])
theorem bls377_three_ne_zero : (3 : ZMod bls377Q) ≠ 0 :=
  bls377_nz 3 (by norm_num) (by norm_num [bls377Q])
theorem bls377_four_ne_zero : (4 : ZMod bls377Q) ≠ 0 :=
  bls377_nz 4 (by norm_num) (by norm_num [bls377Q])
theorem bls377_eight_ne_zero : (8 : ZMod bls377Q) ≠ 0 :=
  bls377_nz 8 (by norm_num) (by norm_num [bls377Q])

end Field

/-! ## 2. The affine `G1` point and the chord/tangent coordinate maps

The short-Weierstrass affine point-add (distinct points) and point-double (tangent)
coordinate formulas over `ZMod bls377Q`, written field-agnostically (built only from
`*`/`+`/`−`/`⁻¹`).  Exactly mirror `blsAffineRx`/`blsAffineRy`/`blsAffineAdd`/
`blsTangentSlope`/`blsAffineDbl` from `Util/BLS12381Verified.lean`. -/

/-- An affine `bls12_377` `G1` point `(x, y)` over the base field `ZMod bls377Q`. -/
structure Bls377Point where
  /-- Affine `x`-coordinate. -/
  x : ZMod bls377Q
  /-- Affine `y`-coordinate. -/
  y : ZMod bls377Q

/-- The short-Weierstrass affine point-add `x`-coordinate map: `x₃ = λ² − x₁ − x₂`. -/
def bls377AffineRx (lam x1 x2 : ZMod bls377Q) : ZMod bls377Q := lam * lam - x1 - x2

/-- The short-Weierstrass affine point-add `y`-coordinate map: `y₃ = λ·(x₁ − x₃) − y₁`. -/
def bls377AffineRy (lam x1 x3 y1 : ZMod bls377Q) : ZMod bls377Q := lam * (x1 - x3) - y1

/-- The full affine point-add coordinate formula, given the precomputed chord slope `λ`. -/
def bls377AffineAdd (lam : ZMod bls377Q) (P Q : Bls377Point) : Bls377Point :=
  let x3 := bls377AffineRx lam P.x Q.x
  { x := x3, y := bls377AffineRy lam P.x x3 P.y }

/-- The short-Weierstrass tangent slope at an affine point `(x, y)` on `y² = x³ + 1`
    (`a = 0`): `λ = (3·x²)·(2·y)⁻¹`. -/
def bls377TangentSlope (x y : ZMod bls377Q) : ZMod bls377Q := (3 * (x * x)) * (2 * y)⁻¹

/-- The full affine point-double coordinate formula, given the precomputed tangent slope `λ`.
    Reuses `bls377AffineRx`/`bls377AffineRy` with `x₂ = x₁ = x`. -/
def bls377AffineDbl (lam : ZMod bls377Q) (P : Bls377Point) : Bls377Point :=
  let x3 := bls377AffineRx lam P.x P.x
  { x := x3, y := bls377AffineRy lam P.x x3 P.y }

/-! ## 3. The Jacobian point and the inversion-free projective group law

A Jacobian point `(X, Y, Z)` represents the affine point `(X·Z⁻², Y·Z⁻³)`.  The
`dbl-2009-l` / `add-2007-bl` formulas for `a = 0` compute the group law with **no inverse**
(only `*`/`+`/`−`); the single inverse is deferred to the final affine conversion
`bls377JacToAffine`. -/

/-- A Jacobian projective `G1` point `(X, Y, Z)` over `ZMod bls377Q`.  Represents the affine
    point `(X·Z⁻², Y·Z⁻³)`; `Z = 0` is the point at infinity. -/
structure Bls377JacPoint where
  /-- Jacobian `X`. -/
  X : ZMod bls377Q
  /-- Jacobian `Y`. -/
  Y : ZMod bls377Q
  /-- Jacobian `Z` (`Z = 0` ⇒ point at infinity). -/
  Z : ZMod bls377Q

/-- The affine-embedding of an affine point `(x, y)` as the Jacobian point `(x, y, 1)`. -/
def Bls377JacPoint.ofAffine (P : Bls377Point) : Bls377JacPoint := { X := P.x, Y := P.y, Z := 1 }

/-- The **one-inverse** Jacobian→affine conversion `(X, Y, Z) ↦ (X·(Z²)⁻¹, Y·(Z³)⁻¹)`. -/
def bls377JacToAffine (J : Bls377JacPoint) : Bls377Point :=
  { x := J.X * (J.Z ^ 2)⁻¹, y := J.Y * (J.Z ^ 3)⁻¹ }

/-- The `dbl-2009-l` Jacobian point-double for `a = 0`: `S = 4XY²`, `M = 3X²`,
    `X' = M² − 2S`, `Y' = M·(S − X') − 8Y⁴`, `Z' = 2YZ`.  **No inverse.** -/
def bls377JacDouble (J : Bls377JacPoint) : Bls377JacPoint :=
  let S := 4 * J.X * J.Y ^ 2
  let M := 3 * J.X ^ 2
  let Xp := M ^ 2 - 2 * S
  { X := Xp, Y := M * (S - Xp) - 8 * J.Y ^ 4, Z := 2 * J.Y * J.Z }

/-- The `add-2007-bl` Jacobian point-add in the `Z = 1` chart (both inputs affine, the
    mixed-add form the windowed / Pippenger loops drive): `H = X₂ − X₁`, `r = Y₂ − Y₁`,
    `X' = r² − H³ − 2X₁H²`, `Y' = r·(X₁H² − X') − Y₁H³`, `Z' = H`.  **No inverse.** -/
def bls377JacAddZ1 (J K : Bls377JacPoint) : Bls377JacPoint :=
  let H := K.X - J.X
  let r := K.Y - J.Y
  let Xp := r ^ 2 - H ^ 3 - 2 * J.X * H ^ 2
  { X := Xp, Y := r * (J.X * H ^ 2 - Xp) - J.Y * H ^ 3, Z := H }

/-! ## 4. The denote-tie to the affine group law (the correctness oracle)

`bls377JacToAffine` of the projective double/add, on affine-embedded inputs, equals the affine
`bls377AffineDbl`/`bls377AffineAdd` at the same chord/tangent slope.  Pure field-algebra
identities — the projective accumulation computes the same `G1` group element, with the
inverse amortized.  These require the field structure (`Fact (Nat.Prime bls377Q)`). -/

section Realization

variable [Fact (Nat.Prime bls377Q)]

/-- **The projective double realizes the affine double.**  Converting the `dbl-2009-l`
    Jacobian double of the affine-embedded `(x, y)` back to affine (one inverse) yields
    exactly `bls377AffineDbl` at the tangent slope — in the generic chart (`y ≠ 0`). -/
theorem bls377_jacDouble_realizes_affineDbl (P : Bls377Point) (hy : P.y ≠ 0) :
    bls377JacToAffine (bls377JacDouble (Bls377JacPoint.ofAffine P))
      = bls377AffineDbl (bls377TangentSlope P.x P.y) P := by
  have h2 : (2 : ZMod bls377Q) ≠ 0 := bls377_two_ne_zero
  have h3 : (3 : ZMod bls377Q) ≠ 0 := bls377_three_ne_zero
  have h4 : (4 : ZMod bls377Q) ≠ 0 := bls377_four_ne_zero
  have h8 : (8 : ZMod bls377Q) ≠ 0 := bls377_eight_ne_zero
  obtain ⟨x, y⟩ := P
  refine Bls377Point.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [bls377JacDouble, Bls377JacPoint.ofAffine, bls377AffineRx,
      bls377TangentSlope, mul_one]
    field_simp [hy, h2, h3, h4, h8]
    ring
  · simp only [bls377JacDouble, Bls377JacPoint.ofAffine, bls377AffineRx,
      bls377AffineRy, bls377TangentSlope, mul_one]
    field_simp [hy, h2, h3, h4, h8]
    ring

/-- **The projective add realizes the affine add (distinct points).**  Converting the
    `add-2007-bl` Jacobian add of two affine-embedded distinct points back to affine (one
    inverse) yields exactly `bls377AffineAdd` at the chord slope — generic chart
    (`x₂ ≠ x₁`). -/
theorem bls377_jacAdd_realizes_affineAdd (P Q : Bls377Point) (hx : Q.x - P.x ≠ 0) :
    bls377JacToAffine (bls377JacAddZ1 (Bls377JacPoint.ofAffine P) (Bls377JacPoint.ofAffine Q))
      = bls377AffineAdd ((Q.y - P.y) * (Q.x - P.x)⁻¹) P Q := by
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  refine Bls377Point.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [bls377JacAddZ1, Bls377JacPoint.ofAffine, bls377AffineRx]
    field_simp
    ring
  · simp only [bls377JacAddZ1, Bls377JacPoint.ofAffine, bls377AffineRx,
      bls377AffineRy]
    field_simp
    ring

end Realization

end CatCrypt.Crypto.SecureCompilation.RelationalFront
