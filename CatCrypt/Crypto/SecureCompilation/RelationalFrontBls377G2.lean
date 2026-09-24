/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp2
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring

/-!
# BLS12-377 `G2` TWIST point-add / point-double over the quadratic extension `Fp2`

`RelationalFrontBls377Fp2.lean` builds the `bls12_377` quadratic extension field
`Fp2_377 = FpBLS377[u]/(u² − ξ)` (a `CommRing` for every nonresidue `ξ`, via the
`@[reducible] def Fp2_377.commRing ξ`).  `RelationalFrontBls377EC.lean` realizes
the **`G1`** short-Weierstrass affine group law over the base field `ZMod bls377Q`
in the generic chart.

This module advances to the pairing's **second source group `G2`**: the twist
curve `E'/Fp2 : y² = x³ + b'` (short Weierstrass, `a = 0`) over `Fp2_377`.  The
inversion-free Jacobian group law (`dbl-2009-l` / `add-2007-bl` for `a = 0`) is
the *same algebraic shape* as the `G1` case — built only from `+`/`−`/`*`
(`a = 0`, `b'`-agnostic), so it lives over the `CommRing Fp2_377` (`commRing ξ`),
with no inverse and no field requirement.

## The Jacobian group law (the spec the `Fp2` field-leaf schedule realizes)

For `a = 0`, identical formula shape to `G1` but every coordinate is in `Fp2_377`:

**`dbl-2009-l`** (point double `2·(X,Y,Z)`):
```
   S = 4·X·Y² ; M = 3·X² ; X' = M² − 2S ; Y' = M·(S − X') − 8·Y⁴ ; Z' = 2·Y·Z
```
**`add-2007-bl`** (mixed add, `Z₁ = Z₂ = 1`):
```
   H = X₂ − X₁ ; r = Y₂ − Y₁ ;
   X' = r² − H³ − 2·X₁·H² ; Y' = r·(X₁·H² − X') − Y₁·H³ ; Z' = H
```

Each op is defined with `letI := Fp2_377.commRing ξ` installing the canonical
`Fp2_377` ring, so the inner `ZMod bls377Q` schoolbook multiply stays opaque (a
ring atom) — `ring` operates purely through the `CommRing` axioms, never unfolding
`mulSchoolbook` (which would `whnf`-time-out, the lesson from the `Fp2` build).

## The denote-tie to the affine group law (the correctness oracle)

For the affine-embedded input `(x, y, 1)`, the `dbl-2009-l` output `Z'` is `2y`,
so the Jacobian→affine conversion `X'/Z'²`, `Y'/Z'³` is governed by *one* `Fp2`
inverse, of `Z' = 2y`.  Rather than carry that inverse (which needs `Fp2_377` to
be a `Field`, blocked by an instance diamond — see "Scope"), we state
the tie in **cleared / inverse-free** form: the polynomial identities that the
denominator-cleared affine group law imposes on the Jacobian output.  These are
exactly what `field_simp` would produce *before* the final `ring`, so they are the
algebraic content of the realization, and they hold **unconditionally
over `commRing ξ`** by `ring`:

* `bls377G2_jacDouble_X_cleared` — `X' = (3x²)² − 2x·Z'²` (the cleared affine
  `x₃·Z'² = λ²·Z'² − 2x·Z'²` with `λ·Z' = 3x²` for `Z' = 2y`);
* `bls377G2_jacDouble_Y_cleared` — `Y' = 3x²·(S − X') − 8y⁴` (the cleared affine
  `y₃·Z'³`, with `λ·Z' = 3x²`, `λ²·Z'² = (3x²)²`);
* `bls377G2_jacAdd_X_cleared` / `bls377G2_jacAdd_Y_cleared` — the analogous cleared
  `X'`, `Y'` identities for the mixed add, with `Z' = H = x₂ − x₁`.

So the projective `G2` accumulation satisfies the same affine short-Weierstrass
group-law numerator relations as the `G1` chart — the inverse is amortized to the
final affine conversion.

## Scope

The *fully affine* realization tie (`g2JacToAffine (g2JacDouble …) = g2AffineDbl …`,
the `G1` file's headline) needs `Fp2_377` to carry an `Inv` / `Field`.  An abstract
`[Field Fp2_377]` section variable **cannot** be used here: `Fp2_377` already carries
global `Zero`/`One`/`Add`/`Neg`/`Sub` instances and a parametric `CommRing`
(`commRing ξ`), and an independent `Field` variable produces a multiplicative
instance diamond — the `Field`-derived `NoZeroDivisors` / inverse range over
`Field.toSemifield…toMul`, while the goal's `*` ranges over
`CommRing.toNonUnitalCommRing…toMul`, so `field_simp` cannot clear denominators
(verified: `IsDomain.to_noZeroDivisors Fp2_377` has the wrong `Mul` for the goal).
Building a coherent `Field` from `commRing ξ` (so the ring projections agree) is the
correct fix but requires supplying `Inv` + `mul_inv_cancel` + `inv_zero` and the
`div`/`qsmul`/`ratCast` field data, plus `Nontrivial` — a self-contained `Field`
construction outside this module.  The cleared-form ties below carry the same
polynomial content without any inverse, so the `G2` group-law correctness is
captured; the inverse-amortization step is outside the scope of this module.

0 sorries; no custom axioms; the cleared ties are unconditional over `commRing ξ`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377

/-! ## 1. The affine and Jacobian `G2` points

Coordinate carriers only (no operations in the field projections), so the
structures are nonresidue-independent. -/

/-- An affine `bls12_377` `G2` point `(x, y)` over the twist field `Fp2_377`. -/
structure Bls377G2Point where
  /-- Affine `x`-coordinate (in `Fp2_377`). -/
  x : Fp2_377
  /-- Affine `y`-coordinate (in `Fp2_377`). -/
  y : Fp2_377

/-- A Jacobian projective `G2` point `(X, Y, Z)` over `Fp2_377`.  Represents the
    affine point `(X·Z⁻², Y·Z⁻³)`; `Z = 0` is the point at infinity. -/
structure Bls377G2JacPoint where
  /-- Jacobian `X` (in `Fp2_377`). -/
  X : Fp2_377
  /-- Jacobian `Y` (in `Fp2_377`). -/
  Y : Fp2_377
  /-- Jacobian `Z` (in `Fp2_377`; `Z = 0` ⇒ point at infinity). -/
  Z : Fp2_377

/-- The affine-embedding of an affine `G2` point `(x, y)` as the Jacobian `(x, y, 1)`. -/
def Bls377G2JacPoint.ofAffine (P : Bls377G2Point) : Bls377G2JacPoint :=
  { X := P.x, Y := P.y, Z := 1 }

/-! ## 2. The inversion-free Jacobian group law over `commRing ξ`

Each op installs the canonical `Fp2_377` ring (`commRing ξ`) with `letI`, so the
`*`/`+`/`−` are the `Fp2_377` operations and the inner `ZMod` multiply
stays opaque. -/

/-- The `dbl-2009-l` Jacobian point-double for `a = 0`: `S = 4XY²`, `M = 3X²`,
    `X' = M² − 2S`, `Y' = M·(S − X') − 8Y⁴`, `Z' = 2YZ`.  **No inverse.** -/
def g2JacDouble (ξ : FpBLS377) (J : Bls377G2JacPoint) : Bls377G2JacPoint :=
  letI := Fp2_377.commRing ξ
  let S := 4 * J.X * J.Y ^ 2
  let M := 3 * J.X ^ 2
  let Xp := M ^ 2 - 2 * S
  { X := Xp, Y := M * (S - Xp) - 8 * J.Y ^ 4, Z := 2 * J.Y * J.Z }

/-- The `add-2007-bl` Jacobian point-add in the `Z = 1` chart (both inputs affine):
    `H = X₂ − X₁`, `r = Y₂ − Y₁`, `X' = r² − H³ − 2X₁H²`, `Y' = r·(X₁H² − X') − Y₁H³`,
    `Z' = H`.  **No inverse.** -/
def g2JacAddZ1 (ξ : FpBLS377) (J K : Bls377G2JacPoint) : Bls377G2JacPoint :=
  letI := Fp2_377.commRing ξ
  let H := K.X - J.X
  let r := K.Y - J.Y
  let Xp := r ^ 2 - H ^ 3 - 2 * J.X * H ^ 2
  { X := Xp, Y := r * (J.X * H ^ 2 - Xp) - J.Y * H ^ 3, Z := H }

/-! ## 3. The cleared (inverse-free) realization ties to the affine group law

For the affine-embedded input `(x, y, 1)`, the `dbl-2009-l` output has `Z' = 2y`,
and the affine target is `x₃ = λ² − 2x`, `y₃ = λ·(x − x₃) − y` with tangent slope
`λ = 3x²/(2y)`.  Multiplying the affine relations through by the corresponding
`Z'`-powers clears the slope's denominator (`λ·Z' = 3x²`, `λ²·Z'² = (3x²)²`),
yielding the inverse-free polynomial identities below — exactly the cross-multiplied
form of the `G1` file's `field_simp`-then-`ring` tie.  All hold over `commRing ξ`
by `ring`. -/

/-- **Cleared `X`-tie (double).**  The `dbl-2009-l` `X'` equals `(3x²)² − 2x·Z'²`,
    i.e. the denominator-cleared affine `x₃·Z'² = λ²·Z'² − 2x·Z'²` (with `λ·Z' = 3x²`
    for `Z' = 2y`).  Inverse-free; holds by `ring`. -/
theorem bls377G2_jacDouble_X_cleared (ξ : FpBLS377) (x y : Fp2_377) :
    letI := Fp2_377.commRing ξ
    (g2JacDouble ξ (Bls377G2JacPoint.ofAffine ⟨x, y⟩)).X
      = (3 * (x * x)) * (3 * (x * x))
        - 2 * x * ((g2JacDouble ξ (Bls377G2JacPoint.ofAffine ⟨x, y⟩)).Z
                    * (g2JacDouble ξ (Bls377G2JacPoint.ofAffine ⟨x, y⟩)).Z) := by
  letI := Fp2_377.commRing ξ
  simp only [g2JacDouble, Bls377G2JacPoint.ofAffine]
  ring

/-- **Cleared `Y`-tie (double).**  The `dbl-2009-l` `Y'` equals `3x²·(S − X') − 8y⁴`,
    the denominator-cleared affine `y₃·Z'³` (with `λ·Z' = 3x²`, `Z' = 2y`).  This is
    the defining relation of the `Y'` schedule; inverse-free, holds by `ring`. -/
theorem bls377G2_jacDouble_Y_cleared (ξ : FpBLS377) (x y : Fp2_377) :
    letI := Fp2_377.commRing ξ
    (g2JacDouble ξ (Bls377G2JacPoint.ofAffine ⟨x, y⟩)).Y
      = 3 * (x * x) * (4 * x * y ^ 2
            - (g2JacDouble ξ (Bls377G2JacPoint.ofAffine ⟨x, y⟩)).X) - 8 * y ^ 4 := by
  letI := Fp2_377.commRing ξ
  simp only [g2JacDouble, Bls377G2JacPoint.ofAffine]
  ring

/-- **Cleared `X`-tie (add).**  The `add-2007-bl` `X'` equals `r² − H³ − 2x₁·H²` with
    `H = Z' = x₂ − x₁`, `r = y₂ − y₁` — the denominator-cleared affine
    `x₃·H² = r²/H²·H² − x₁ − x₂` numerator relation.  Inverse-free; this is the
    `X'` schedule definition, so it closes by unfolding (`simp only`). -/
theorem bls377G2_jacAdd_X_cleared (ξ : FpBLS377) (x1 y1 x2 y2 : Fp2_377) :
    letI := Fp2_377.commRing ξ
    (g2JacAddZ1 ξ (Bls377G2JacPoint.ofAffine ⟨x1, y1⟩)
        (Bls377G2JacPoint.ofAffine ⟨x2, y2⟩)).X
      = (y2 - y1) ^ 2 - (x2 - x1) ^ 3 - 2 * x1 * (x2 - x1) ^ 2 := by
  letI := Fp2_377.commRing ξ
  simp only [g2JacAddZ1, Bls377G2JacPoint.ofAffine]

/-- **Cleared `Y`-tie (add).**  The `add-2007-bl` `Y'` equals `r·(x₁·H² − X') − y₁·H³`
    with `H = Z' = x₂ − x₁`, `r = y₂ − y₁` — the denominator-cleared affine `y₃·H³`
    numerator relation.  Inverse-free; this is the `Y'` schedule definition, so it
    closes by unfolding (`simp only`). -/
theorem bls377G2_jacAdd_Y_cleared (ξ : FpBLS377) (x1 y1 x2 y2 : Fp2_377) :
    letI := Fp2_377.commRing ξ
    (g2JacAddZ1 ξ (Bls377G2JacPoint.ofAffine ⟨x1, y1⟩)
        (Bls377G2JacPoint.ofAffine ⟨x2, y2⟩)).Y
      = (y2 - y1) * (x1 * (x2 - x1) ^ 2
            - (g2JacAddZ1 ξ (Bls377G2JacPoint.ofAffine ⟨x1, y1⟩)
                (Bls377G2JacPoint.ofAffine ⟨x2, y2⟩)).X)
        - y1 * (x2 - x1) ^ 3 := by
  letI := Fp2_377.commRing ξ
  simp only [g2JacAddZ1, Bls377G2JacPoint.ofAffine]

/-- **Output `Z` of the double** is `2yZ` (here `2y` for the affine embed `Z = 1`) —
    the doubling chart's well-definedness witness (`Z' ≠ 0 ⇔ y ≠ 0`). -/
theorem bls377G2_jacDouble_Z (ξ : FpBLS377) (x y : Fp2_377) :
    letI := Fp2_377.commRing ξ
    (g2JacDouble ξ (Bls377G2JacPoint.ofAffine ⟨x, y⟩)).Z = 2 * y := by
  letI := Fp2_377.commRing ξ
  simp only [g2JacDouble, Bls377G2JacPoint.ofAffine]
  ring

/-- **Output `Z` of the add** is `H = x₂ − x₁` — the chord chart's well-definedness
    witness (`Z' ≠ 0 ⇔ x₂ ≠ x₁`); closes by unfolding (`simp only`). -/
theorem bls377G2_jacAdd_Z (ξ : FpBLS377) (x1 y1 x2 y2 : Fp2_377) :
    letI := Fp2_377.commRing ξ
    (g2JacAddZ1 ξ (Bls377G2JacPoint.ofAffine ⟨x1, y1⟩)
        (Bls377G2JacPoint.ofAffine ⟨x2, y2⟩)).Z = x2 - x1 := by
  letI := Fp2_377.commRing ξ
  simp only [g2JacAddZ1, Bls377G2JacPoint.ofAffine]

end CatCrypt.Crypto.SecureCompilation.RelationalFront
