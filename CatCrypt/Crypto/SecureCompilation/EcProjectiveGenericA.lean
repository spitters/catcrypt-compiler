/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric

/-!
# Short-Weierstrass Jacobian point-double with the curve coefficient `a`

`EcRealizationGeneric` and `EcProjectiveGeneric` state the Jacobian point-double for curves
`y² = x³ + b` (`a = 0`). This module states the double for `y² = x³ + a·x + b` over an
abstract `[Field F]`, beside those declarations, with the same affine-side maps
`ecAffineDbl` / `ecAffineRx` / `ecAffineRy`.

## The formula

A Jacobian point `(X, Y, Z)` represents the affine point `(X·(Z²)⁻¹, Y·(Z³)⁻¹)`. The double is
```
   S = 4·X·Y² ; M = 3·X² + a·Z⁴ ; X' = M² − 2S ; Y' = M·(S − X') − 8·Y⁴ ; Z' = 2·Y·Z
```
(`jacDoubleGenA`). At `a = −3` the slope numerator factors as `M = 3·(X − Z²)·(X + Z²)`
(`jacDoubleGenM3`, the `dbl-2001-b` specialisation), which costs two field multiplies
(`Z²`, `(X − Z²)·(X + Z²)`) against four for `3·X² + a·Z⁴` (`X²`, `Z²`, `Z⁴`, `a·Z⁴`).
`jacDoubleGenM3_eq` identifies the two at `a = −3`, and `jacDoubleGenA_zero` identifies
`jacDoubleGenA 0` with `EcProjectiveGeneric.jacDoubleGen`.

## Scope

The realization ties are the generic-chart identities (`Z ≠ 0`, `Y ≠ 0`, doubling branch),
proved by `field_simp; ring`, at the generality of the `a = 0` theorems they parallel.

`@canonical_parametric`: parametric over the base field and the coefficient `a`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.EcProjectiveGenericA

open CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric
open CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric

universe u

variable {F : Type u} [Field F]

/-! ## 1. The tangent slope and the `Z = 1` chart double -/

/-- The short-Weierstrass tangent slope at an affine point `(x, y)` on
    `y² = x³ + a·x + b`: `λ = (3·x² + a)·(2·y)⁻¹`. -/
def ecTangentSlopeA (x y a : F) : F := (3 * (x * x) + a) * (2 * y)⁻¹

/-- At `a = 0` the tangent slope is `EcRealizationGeneric.ecTangentSlope`. -/
theorem ecTangentSlopeA_zero (x y : F) : ecTangentSlopeA x y 0 = ecTangentSlope x y := by
  simp only [ecTangentSlopeA, ecTangentSlope, add_zero]

/-- The Jacobian point-double with coefficient `a`: `S = 4XY²`, `M = 3X² + aZ⁴`,
    `X' = M² − 2S`, `Y' = M·(S − X') − 8Y⁴`, `Z' = 2YZ`. No inverse. -/
def ecJacDoubleA (a : F) (J : ECJacPoint F) : ECJacPoint F :=
  let S := 4 * J.X * J.Y ^ 2
  let M := 3 * J.X ^ 2 + a * J.Z ^ 4
  let Xp := M ^ 2 - 2 * S
  { X := Xp, Y := M * (S - Xp) - 8 * J.Y ^ 4, Z := 2 * J.Y * J.Z }

set_option linter.unusedVariables false in
/-- The Jacobian double with coefficient `a`, applied to the affine embedding `(x, y, 1)` and
    converted back to affine, is `ecAffineDbl` at the tangent slope `(3x² + a)/(2y)` of the
    curve `y² = x³ + a·x + b`, in the generic chart `y ≠ 0`. The four numeral hypotheses are
    those of `EcRealizationGeneric.ec_jacDouble_realizes_affineDbl`. -/
theorem ec_jacDoubleA_realizes_affineDbl
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h4 : (4 : F) ≠ 0) (h8 : (8 : F) ≠ 0)
    (a : F) (P : ECAffPoint F) (hy : P.y ≠ 0) :
    ecJacToAffine (ecJacDoubleA a (ECJacPoint.ofAffine P))
      = ecAffineDbl (ecTangentSlopeA P.x P.y a) P := by
  obtain ⟨x, y⟩ := P
  refine ECAffPoint.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [ecJacDoubleA, ECJacPoint.ofAffine, ecAffineRx, ecTangentSlopeA, mul_one,
      one_pow]
    field_simp
    ring
  · simp only [ecJacDoubleA, ECJacPoint.ofAffine, ecAffineRx, ecAffineRy, ecTangentSlopeA,
      mul_one, one_pow]
    field_simp
    ring

/-! ## 2. The general-`Z` double and its `a = −3` form -/

/-- The Jacobian point-double with coefficient `a` at general `Z`, as a raw coordinate
    triple: `S = 4XY²`, `M = 3X² + aZ⁴`, `X' = M² − 2S`, `Y' = M·(S − X') − 8Y⁴`,
    `Z' = 2YZ`. No inverse. -/
def jacDoubleGenA (a X Y Z : F) : F × F × F :=
  let S := 4 * X * Y ^ 2
  let M := 3 * X ^ 2 + a * Z ^ 4
  let Xp := M ^ 2 - 2 * S
  (Xp, M * (S - Xp) - 8 * Y ^ 4, 2 * Y * Z)

/-- The `a = −3` Jacobian point-double (`dbl-2001-b`): `S = 4XY²`,
    `M = 3·(X − Z²)·(X + Z²)`, `X' = M² − 2S`, `Y' = M·(S − X') − 8Y⁴`, `Z' = 2YZ`. -/
def jacDoubleGenM3 (X Y Z : F) : F × F × F :=
  let S := 4 * X * Y ^ 2
  let M := 3 * ((X - Z ^ 2) * (X + Z ^ 2))
  let Xp := M ^ 2 - 2 * S
  (Xp, M * (S - Xp) - 8 * Y ^ 4, 2 * Y * Z)

/-- The `dbl-2001-b` factorisation: `jacDoubleGenM3` is `jacDoubleGenA` at `a = −3`. -/
theorem jacDoubleGenM3_eq (X Y Z : F) : jacDoubleGenM3 X Y Z = jacDoubleGenA (-3) X Y Z := by
  have hM : 3 * ((X - Z ^ 2) * (X + Z ^ 2)) = 3 * X ^ 2 + (-3) * Z ^ 4 := by ring
  simp only [jacDoubleGenM3, jacDoubleGenA, hM]

/-- At `a = 0`, `jacDoubleGenA` is `EcProjectiveGeneric.jacDoubleGen`. -/
theorem jacDoubleGenA_zero (X Y Z : F) : jacDoubleGenA 0 X Y Z = jacDoubleGen X Y Z := by
  simp only [jacDoubleGenA, jacDoubleGen, zero_mul, add_zero]

/-- The output `Z'`-coordinate of `jacDoubleGenA` is `2·Y·Z`. -/
@[simp] theorem jacDoubleGenA_Zp (a X Y Z : F) : (jacDoubleGenA a X Y Z).2.2 = 2 * Y * Z := rfl

/-- The output `Z'`-coordinate `2·Y·Z` of `jacDoubleGenA` is nonzero when `2`, `Y`, `Z` are
    nonzero. -/
theorem jacDoubleGenA_Zp_ne_zero
    (h2 : (2 : F) ≠ 0) {a X Y Z : F} (hY : Y ≠ 0) (hZ : Z ≠ 0) :
    (jacDoubleGenA a X Y Z).2.2 ≠ 0 := by
  simp only [jacDoubleGenA_Zp]
  exact mul_ne_zero (mul_ne_zero h2 hY) hZ

set_option linter.unusedVariables false in
/-- The general-`Z` Jacobian double with coefficient `a`, converted back to affine, is
    `ecAffineDbl` at the tangent slope `(3x² + a)/(2y)` of the projected input
    `(X·(Z²)⁻¹, Y·(Z³)⁻¹)`, in the generic chart `Z ≠ 0`, `Y ≠ 0`. The numeral hypotheses
    are those of `EcProjectiveGeneric.jacDoubleGen_realizes`. -/
theorem jacDoubleGenA_realizes
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h4 : (4 : F) ≠ 0) (h8 : (8 : F) ≠ 0)
    (a X Y Z : F) (hZ : Z ≠ 0) (hY : Y ≠ 0)
    (hZ' : (jacDoubleGenA a X Y Z).2.2 ≠ 0) :
    jacToAffineGen (jacDoubleGenA a X Y Z).1 (jacDoubleGenA a X Y Z).2.1
        (jacDoubleGenA a X Y Z).2.2 hZ'
      = ecAffineDbl (ecTangentSlopeA (X * (Z ^ 2)⁻¹) (Y * (Z ^ 3)⁻¹) a)
          (jacToAffineGen X Y Z hZ) := by
  refine ECAffPoint.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [jacDoubleGenA, jacToAffineGen, ecAffineRx, ecTangentSlopeA]
    field_simp
    ring
  · simp only [jacDoubleGenA, jacToAffineGen, ecAffineRx, ecAffineRy, ecTangentSlopeA]
    field_simp
    ring

end CatCrypt.Crypto.SecureCompilation.EcProjectiveGenericA
