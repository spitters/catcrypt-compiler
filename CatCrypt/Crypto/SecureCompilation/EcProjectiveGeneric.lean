/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric

/-!
# Generic short-Weierstrass (`a = 0`) Jacobian point-double for general `Z`

`EcRealizationGeneric.lean` proves the `dbl-2009-l` projective point-double realizes the affine
double, but only in the **`Z = 1` chart** (the affine-embedding `ECJacPoint.ofAffine` always
sets `Z = 1`).  In a windowed / Pippenger scalar-multiplication loop the accumulator is a
*general* Jacobian point with `Z ≠ 1`, so the in-loop double feeds a general-`Z` representative.

This module extends the realization to **general `Z`**.  A Jacobian point `(X, Y, Z)` represents
the affine point `(X·(Z²)⁻¹, Y·(Z³)⁻¹)`; we prove that the `dbl-2009-l` double of such a point,
projected back to affine, equals the affine double `ecAffineDbl` of the projected input at the
tangent slope of that projected input.  The `Z = 1` version of `EcRealizationGeneric` is the
special case.

## The general-`Z` Jacobian double (`a = 0`)

`jacToAffineGen (X, Y, Z) = (X·(Z²)⁻¹, Y·(Z³)⁻¹)` (requires `Z ≠ 0`).

`dbl-2009-l`:
```
   S = 4·X·Y² ; M = 3·X² ; X' = M² − 2S ; Y' = M·(S − X') − 8·Y⁴ ; Z' = 2·Y·Z
```

The well-definedness side-condition `Z' = 2·Y·Z ≠ 0` holds when `2, Y, Z` are all nonzero,
which is `jacDoubleGen_Zp_ne_zero`.

## Scope

The tie is the **generic-chart** identity (general `Z ≠ 0`, doubling branch, nonzero `y`); it
holds by `field_simp; ring`.  This reuses the affine-side maps `ecAffineDbl` / `ecTangentSlope`
of `EcRealizationGeneric` verbatim — only the Jacobian side is generalized off the `Z = 1` chart.

This is the **canonical parametric form** (`@canonical_parametric` — genuinely parametric over
the base field).  0 sorries; no custom axioms; the field-algebra tie is unconditional given the
field structure plus the four numeral-nonvanishing hypotheses and `Z ≠ 0`, `Y ≠ 0`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric

open CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric

universe u

variable {F : Type u} [Field F]

/-! ## 1. The general-`Z` Jacobian→affine conversion and the `dbl-2009-l` double -/

/-- The general-`Z` Jacobian→affine conversion `(X, Y, Z) ↦ (X·(Z²)⁻¹, Y·(Z³)⁻¹)`.
    Requires `Z ≠ 0` (the point is not at infinity); the hypothesis is carried so the realization
    statement can mention the projected input directly. -/
def jacToAffineGen (X Y Z : F) (_hZ : Z ≠ 0) : ECAffPoint F :=
  { x := X * (Z ^ 2)⁻¹, y := Y * (Z ^ 3)⁻¹ }

/-- The `dbl-2009-l` Jacobian point-double for `a = 0` at general `Z`: `S = 4XY²`, `M = 3X²`,
    `X' = M² − 2S`, `Y' = M·(S − X') − 8Y⁴`, `Z' = 2YZ`.  **No inverse.**  Returns the raw
    coordinate triple `(X', Y', Z')`. -/
def jacDoubleGen (X Y Z : F) : F × F × F :=
  let S := 4 * X * Y ^ 2
  let M := 3 * X ^ 2
  let Xp := M ^ 2 - 2 * S
  (Xp, M * (S - Xp) - 8 * Y ^ 4, 2 * Y * Z)

/-- The output `Z'`-coordinate `2·Y·Z` of `jacDoubleGen` is the third component. -/
@[simp] theorem jacDoubleGen_Zp (X Y Z : F) : (jacDoubleGen X Y Z).2.2 = 2 * Y * Z := rfl

/-! ## 2. Well-definedness: the doubled point is again off infinity -/

/-- **Well-definedness of the general-`Z` double.**  The output `Z'`-coordinate `2·Y·Z` is
    nonzero whenever `2`, `Y`, `Z` are all nonzero — so `jacDoubleGen` maps an affine
    (non-infinity) representative to another affine representative, and the result can again be
    fed to `jacToAffineGen`. -/
theorem jacDoubleGen_Zp_ne_zero
    (h2 : (2 : F) ≠ 0) {X Y Z : F} (hY : Y ≠ 0) (hZ : Z ≠ 0) :
    (jacDoubleGen X Y Z).2.2 ≠ 0 := by
  simp only [jacDoubleGen_Zp]
  exact mul_ne_zero (mul_ne_zero h2 hY) hZ

/-! ## 3. The denote-tie to the affine group law at general `Z` -/

set_option linter.unusedVariables false in
/-- **The general-`Z` projective double realizes the affine double.**  Converting the
    `dbl-2009-l` Jacobian double of a general-`Z` representative `(X, Y, Z)` back to affine (one
    inverse) yields exactly `ecAffineDbl` at the tangent slope of the **projected** input
    `(X·(Z²)⁻¹, Y·(Z³)⁻¹)` — in the generic chart (`Z ≠ 0`, `Y ≠ 0`).  The four numeral
    hypotheses are the stable per-curve interface (all consequences of `p > 8`).  The `Z = 1`
    special case is `EcRealizationGeneric.ec_jacDouble_realizes_affineDbl`. -/
theorem jacDoubleGen_realizes
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h4 : (4 : F) ≠ 0) (h8 : (8 : F) ≠ 0)
    (X Y Z : F) (hZ : Z ≠ 0) (hY : Y ≠ 0)
    (hZ' : (jacDoubleGen X Y Z).2.2 ≠ 0) :
    jacToAffineGen (jacDoubleGen X Y Z).1 (jacDoubleGen X Y Z).2.1
        (jacDoubleGen X Y Z).2.2 hZ'
      = ecAffineDbl (ecTangentSlope (X * (Z ^ 2)⁻¹) (Y * (Z ^ 3)⁻¹))
          (jacToAffineGen X Y Z hZ) := by
  refine ECAffPoint.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [jacDoubleGen, jacToAffineGen, ecAffineRx, ecTangentSlope]
    field_simp
    ring
  · simp only [jacDoubleGen, jacToAffineGen, ecAffineRx, ecAffineRy, ecTangentSlope]
    field_simp
    ring

end CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric
