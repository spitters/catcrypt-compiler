/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric

/-!
# Generic short-Weierstrass (`a = 0`) Jacobian point-add for two general-`Z` points

`EcRealizationGeneric.lean` proves the `add-2007-bl` projective point-add realizes the affine
chord-add, but only in the **`Z₁ = Z₂ = 1` mixed-add chart** (`ecJacAddZ1`, both inputs the
affine-embedding `ECJacPoint.ofAffine` with `Z = 1`).  `EcProjectiveGeneric.lean` extends the
**double** to a single general-`Z` representative.  In a windowed / Pippenger scalar-multiplication
loop the running accumulator is a *general* Jacobian point with `Z ≠ 1`, and so is the table
entry being added, so the in-loop add feeds **two** general-`Z` representatives.

This module supplies the missing piece: the **full general-`Z`** `add-2007-bl` Jacobian add,
both points off the `Z = 1` chart, realizing the affine chord-add of the two affine-projected
inputs.  Together with `EcProjectiveGeneric.jacDoubleGen_realizes` it is the complete general-`Z`
projective group law that an accumulation loop drives.

## The general-`Z` Jacobian add (`a = 0`, `add-2007-bl`)

A Jacobian point `(X, Y, Z)` represents the affine point `(X·(Z²)⁻¹, Y·(Z³)⁻¹)` (`jacToAffineGen`,
from `EcProjectiveGeneric`; requires `Z ≠ 0`).  For two such points `(X₁, Y₁, Z₁)`, `(X₂, Y₂, Z₂)`:
```
   U₁ = X₁·Z₂² ; U₂ = X₂·Z₁² ; S₁ = Y₁·Z₂³ ; S₂ = Y₂·Z₁³
   H = U₂ − U₁ ; r = S₂ − S₁
   X₃ = r² − H³ − 2·U₁·H² ; Y₃ = r·(U₁·H² − X₃) − S₁·H³ ; Z₃ = Z₁·Z₂·H
```
**No inverse** — only `*`/`+`/`−`; the single inverse is deferred to the final `jacToAffineGen`
conversion.  This is the standard `add-2007-bl` formula; the `Z₁ = Z₂ = 1` mixed-add chart
`EcRealizationGeneric.ecJacAddZ1` is the special case `U₁ = X₁`, `U₂ = X₂`, `S₁ = Y₁`, `S₂ = Y₂`,
`Z₃ = H`.

The well-definedness side-condition `Z₃ = Z₁·Z₂·H ≠ 0` holds when `Z₁`, `Z₂` are nonzero and the
two affine-projected `x`-coordinates differ (`H = U₂ − U₁ ≠ 0`, the generic add chart) —
`jacAddGen_Zp_ne_zero`.

## The chord slope

The affine chord slope of the two projected points `P = (X₁·(Z₁²)⁻¹, Y₁·(Z₁³)⁻¹)`,
`Q = (X₂·(Z₂²)⁻¹, Y₂·(Z₂³)⁻¹)` is `λ = (Q.y − P.y)·(Q.x − P.x)⁻¹`, exactly the slope argument of
`EcRealizationGeneric.ec_jacAdd_realizes_affineAdd`.  The realization states the projected add
equals `ecAffineAdd λ P Q` at this slope — the same affine oracle, only the Jacobian side is
generalized off the `Z = 1` chart to two general-`Z` representatives.

## Scope

The tie is the **generic-chart** identity (general `Z₁, Z₂ ≠ 0`, distinct projected `x`, i.e.
`H ≠ 0`); it holds by `field_simp; ring` once `field_simp` is supplied the `H`, `H²`, `H³`
nonvanishing facts (all consequences of `H ≠ 0`).  The exceptional cases (equal `x` / vertical
line / point at infinity) and all-pairs group-law completeness are out of scope — exactly the
generic-chart scope of the per-curve versions.

This is the **canonical parametric form** (`@canonical_parametric` — genuinely parametric over
the base field).  0 sorries; no custom axioms; the field-algebra tie is unconditional given the
field structure plus `Z₁ ≠ 0`, `Z₂ ≠ 0`, `H ≠ 0`.  The add formula introduces no numerals (unlike
the double's `2, 3, 4, 8`), so no numeral-nonvanishing hypotheses are needed.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric

open CatCrypt.Crypto.SecureCompilation.EcRealizationGeneric

universe u

variable {F : Type u} [Field F]

/-! ## 1. The general-`Z` `add-2007-bl` Jacobian add -/

/-- The `add-2007-bl` Jacobian point-add for `a = 0` at general `Z₁, Z₂`:
    `U₁ = X₁Z₂²`, `U₂ = X₂Z₁²`, `S₁ = Y₁Z₂³`, `S₂ = Y₂Z₁³`, `H = U₂ − U₁`, `r = S₂ − S₁`,
    `X₃ = r² − H³ − 2U₁H²`, `Y₃ = r·(U₁H² − X₃) − S₁H³`, `Z₃ = Z₁Z₂H`.  **No inverse.**
    Returns the raw coordinate triple `(X₃, Y₃, Z₃)`. -/
def jacAddGen (X1 Y1 Z1 X2 Y2 Z2 : F) : F × F × F :=
  let U1 := X1 * Z2 ^ 2
  let U2 := X2 * Z1 ^ 2
  let S1 := Y1 * Z2 ^ 3
  let S2 := Y2 * Z1 ^ 3
  let H := U2 - U1
  let r := S2 - S1
  let Xp := r ^ 2 - H ^ 3 - 2 * U1 * H ^ 2
  (Xp, r * (U1 * H ^ 2 - Xp) - S1 * H ^ 3, Z1 * Z2 * H)

/-- The output `Z₃`-coordinate `Z₁·Z₂·(X₂Z₁² − X₁Z₂²)` of `jacAddGen` is the third component. -/
@[simp] theorem jacAddGen_Zp (X1 Y1 Z1 X2 Y2 Z2 : F) :
    (jacAddGen X1 Y1 Z1 X2 Y2 Z2).2.2 = Z1 * Z2 * (X2 * Z1 ^ 2 - X1 * Z2 ^ 2) := rfl

/-! ## 2. Well-definedness: the summed point is again off infinity -/

/-- **Well-definedness of the general-`Z` add.**  The output `Z₃`-coordinate `Z₁·Z₂·H` is nonzero
    whenever `Z₁`, `Z₂` are nonzero and the two affine-projected `x`-coordinates differ
    (`H = X₂Z₁² − X₁Z₂² ≠ 0`, the generic add chart) — so `jacAddGen` maps two affine
    (non-infinity) representatives to another affine representative, and the result can again be
    fed to `jacToAffineGen`. -/
theorem jacAddGen_Zp_ne_zero {X1 Y1 Z1 X2 Y2 Z2 : F}
    (hZ1 : Z1 ≠ 0) (hZ2 : Z2 ≠ 0) (hH : X2 * Z1 ^ 2 - X1 * Z2 ^ 2 ≠ 0) :
    (jacAddGen X1 Y1 Z1 X2 Y2 Z2).2.2 ≠ 0 := by
  simp only [jacAddGen_Zp]
  exact mul_ne_zero (mul_ne_zero hZ1 hZ2) hH

/-! ## 3. The denote-tie to the affine chord-add at general `Z₁, Z₂` -/

set_option linter.unusedVariables false in
/-- **The general-`Z` projective add realizes the affine chord-add.**  Converting the
    `add-2007-bl` Jacobian add of two general-`Z` representatives `(X₁, Y₁, Z₁)`, `(X₂, Y₂, Z₂)`
    back to affine (one inverse) yields exactly `ecAffineAdd` at the chord slope
    `(Q.y − P.y)·(Q.x − P.x)⁻¹` of the **projected** inputs
    `P = (X₁·(Z₁²)⁻¹, Y₁·(Z₁³)⁻¹)`, `Q = (X₂·(Z₂²)⁻¹, Y₂·(Z₂³)⁻¹)` — in the generic chart
    (`Z₁, Z₂ ≠ 0`, distinct projected `x`, i.e. `H = X₂Z₁² − X₁Z₂² ≠ 0`).  No numeral hypotheses
    are needed: the `add-2007-bl` formula introduces none.  The `Z₁ = Z₂ = 1` special case is
    `EcRealizationGeneric.ec_jacAdd_realizes_affineAdd`. -/
theorem jacAddGen_realizes
    (X1 Y1 Z1 X2 Y2 Z2 : F) (hZ1 : Z1 ≠ 0) (hZ2 : Z2 ≠ 0)
    (hH : X2 * Z1 ^ 2 - X1 * Z2 ^ 2 ≠ 0)
    (hZ3 : (jacAddGen X1 Y1 Z1 X2 Y2 Z2).2.2 ≠ 0) :
    jacToAffineGen (jacAddGen X1 Y1 Z1 X2 Y2 Z2).1 (jacAddGen X1 Y1 Z1 X2 Y2 Z2).2.1
        (jacAddGen X1 Y1 Z1 X2 Y2 Z2).2.2 hZ3
      = ecAffineAdd
          (((jacToAffineGen X2 Y2 Z2 hZ2).y - (jacToAffineGen X1 Y1 Z1 hZ1).y)
            * ((jacToAffineGen X2 Y2 Z2 hZ2).x - (jacToAffineGen X1 Y1 Z1 hZ1).x)⁻¹)
          (jacToAffineGen X1 Y1 Z1 hZ1) (jacToAffineGen X2 Y2 Z2 hZ2) := by
  -- The chord slope's squaring/cubing in `ecAffineRx`/`ecAffineRy` leaves `field_simp` with
  -- denominators that are `H`, `H²`, `H³` in expanded (degree 2/4/6) normal form.  We discharge
  -- each from `hH : H ≠ 0` so `field_simp` can clear them; the residue is a `ring` identity.
  have hHa : Z1 ^ 2 * X2 - Z2 ^ 2 * X1 ≠ 0 := by
    intro h; exact hH (by linear_combination h)
  have hHb : -(Z1 ^ 2 * Z2 ^ 2 * X2 * X1 * 2) + Z1 ^ 4 * X2 ^ 2 + Z2 ^ 4 * X1 ^ 2 ≠ 0 := by
    intro h
    have : (X2 * Z1 ^ 2 - X1 * Z2 ^ 2) ^ 2 = 0 := by linear_combination h
    exact hH (pow_eq_zero_iff (by norm_num) |>.mp this)
  have hHc : -(Z1 ^ 2 * Z2 ^ 2 * X1 * X2 * 2) + Z1 ^ 4 * X2 ^ 2 + Z2 ^ 4 * X1 ^ 2 ≠ 0 := by
    intro h; exact hHb (by linear_combination h)
  have hHd : Z1 ^ 2 * Z2 ^ 4 * X1 ^ 2 * X2 * 3 - Z1 ^ 4 * Z2 ^ 2 * X1 * X2 ^ 2 * 3
      + Z1 ^ 6 * X2 ^ 3 - Z2 ^ 6 * X1 ^ 3 ≠ 0 := by
    intro h
    have : (X2 * Z1 ^ 2 - X1 * Z2 ^ 2) ^ 3 = 0 := by linear_combination h
    exact hH (pow_eq_zero_iff (by norm_num) |>.mp this)
  refine ECAffPoint.mk.injEq .. ▸ ⟨?_, ?_⟩
  · simp only [jacAddGen, jacToAffineGen, ecAffineRx]
    field_simp [hHa, hHb, hHc, hHd]
    ring
  · simp only [jacAddGen, jacToAffineGen, ecAffineRx, ecAffineRy]
    field_simp [hHa, hHb, hHc, hHd]
    ring

/-! ## 4. Consolidation witness: a per-curve general-`Z` add is a one-line instance

Every per-curve EC file specializes `F := ZMod p` for that curve's base-field prime `p`; the
general-`Z` add introduces no numerals, so a per-curve add realization is recovered by pure
`@`-instantiation with **no new algebra**.  We witness the genericity at the concrete field `ℚ`,
which carries a `Field` instance without a primality side-hypothesis. -/

section Witness

/-- A per-curve general-`Z` point-add realization at `ℚ`, obtained purely by instantiating the
    generic theorem — no `field_simp`/`ring` here.  This is the shape every per-curve EC file
    takes: `@jacAddGen_realizes (ZMod p) _ …`. -/
example (X1 Y1 Z1 X2 Y2 Z2 : ℚ) (hZ1 : Z1 ≠ 0) (hZ2 : Z2 ≠ 0)
    (hH : X2 * Z1 ^ 2 - X1 * Z2 ^ 2 ≠ 0)
    (hZ3 : (jacAddGen X1 Y1 Z1 X2 Y2 Z2).2.2 ≠ 0) :
    jacToAffineGen (jacAddGen X1 Y1 Z1 X2 Y2 Z2).1 (jacAddGen X1 Y1 Z1 X2 Y2 Z2).2.1
        (jacAddGen X1 Y1 Z1 X2 Y2 Z2).2.2 hZ3
      = ecAffineAdd
          (((jacToAffineGen X2 Y2 Z2 hZ2).y - (jacToAffineGen X1 Y1 Z1 hZ1).y)
            * ((jacToAffineGen X2 Y2 Z2 hZ2).x - (jacToAffineGen X1 Y1 Z1 hZ1).x)⁻¹)
          (jacToAffineGen X1 Y1 Z1 hZ1) (jacToAffineGen X2 Y2 Z2 hZ2) :=
  jacAddGen_realizes X1 Y1 Z1 X2 Y2 Z2 hZ1 hZ2 hH hZ3

end Witness

end CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric
