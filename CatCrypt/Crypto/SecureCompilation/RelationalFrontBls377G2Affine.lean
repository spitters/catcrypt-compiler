/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377G2
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377Fp2Inv
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# BLS12-377 `G2` Jacobian→affine projection and the affine group-law realization

`RelationalFrontBls377G2.lean` proved the `bls12_377` `G2` twist group law in
**denominator-cleared** form: the cross-multiplied numerator identities
`bls377G2_jacDouble_X_cleared` / `_Y_cleared` (and the add analogues) over the
inverse-free `commRing ξ` instance.  It deferred the *fully affine* realization
tie (`g2JacToAffine (g2JacDouble …) = g2AffineDbl …`) because that needs an
`Fp2_377` inverse, and an abstract `[Field Fp2_377]` section variable produced a
multiplicative-instance diamond (the `Field`-derived `*` ranges over a different
`Mul` than the goal's `commRing ξ` multiply, so `field_simp` could not clear
denominators).

`RelationalFrontBls377Fp2Inv.lean` removed that obstruction: it provides an
**explicit** conjugate-over-norm inverse `inv ξ x` (built *over* the `commRing ξ`
instance — no `Field` instance, no diamond) together with the cancellation law
`mul_inv (hx : norm ξ x ≠ 0) : x * inv ξ x = 1`.  This module uses that explicit
inverse to close the deferred `G2` affine group-law tie.

## What this module proves

* `g2JacToAffine ξ J` — the Jacobian→affine projection `(X·(Z²)⁻¹, Y·(Z³)⁻¹)`
  using the **explicit** `inv` (not a `Field` `⁻¹`);
* `g2AffineDbl ξ x y` — the affine short-Weierstrass tangent-double
  `λ = 3x²/(2y)`, `x₃ = λ² − 2x`, `y₃ = λ(x − x₃) − y`, with the slope's
  denominator inverted by the explicit `inv`;
* `g2AffineAdd ξ x₁ y₁ x₂ y₂` — the affine chord-add `λ = (y₂−y₁)/(x₂−x₁)`,
  `x₃ = λ² − x₁ − x₂`, `y₃ = λ(x₁ − x₃) − y₁`;
* `bls377G2_affine_double_realizes` — `g2JacToAffine (g2JacDouble (ofAffine ⟨x,y⟩))
  = g2AffineDbl ξ x y` in the generic chart, under `norm ξ (2y) ≠ 0`;
* `bls377G2_affine_add_realizes` — the analogous tie for the chord-add, under
  `norm ξ (x₂−x₁) ≠ 0`.

## Method (the inverse cancellation)

The cleared identities give `X' = (3x²)² − 2x·Z'²` and `Y' = 3x²·(S − X') − 8y⁴`
(double), with `Z' = 2y`.  Projecting through the explicit inverse,
`X'·inv(Z'·Z')` cancels via `mul_inv`: the `2x·Z'²` summand contributes
`2x·(Z'² · inv(Z'²)) = 2x·1`, while the `(3x²)²` summand keeps one `inv(Z'²)`.
The slope `λ = 3x²·inv(Z')` then satisfies `λ² = (3x²)²·inv(Z')² =
(3x²)²·inv(Z'²)` by the inverse-multiplicativity helper `inv_mul_inv` (proved
from `mul_inv`/`inv_mul` by uniqueness of two-sided inverses, **not** from a
`Field` instance).  All multiplications stay opaque over `commRing ξ`; the
cancellation is the pure-algebra `c·b·inv b = c·(b·inv b) = c·1 = c` shape.

## Scope

The realization is conditioned on the slope denominator's norm being nonzero
(`norm ξ (2y) ≠ 0` for the double, `norm ξ (x₂−x₁) ≠ 0` for the add).  That is
exactly the generic-chart hypothesis (`2y ≠ 0`, resp. `x₂ ≠ x₁`) under which
`ξ` being a non-residue makes the norm nonzero (`norm_ne_zero_iff_of_nonresidue`,
whose non-residue hypothesis is the unproved number-theoretic fact about the
concrete twist nonresidue).  We do not wire the inverse down to the emitted
6-limb base kernels.  The Jacobian→affine projection and both group-law
realizations are the deliverables — closing the tie `RelationalFrontBls377G2`
deferred.

All goals closed; no custom axioms; the realizations hold over `commRing ξ` under the
stated norm-nonzero hypotheses.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalFront

open CatCrypt.Crypto.SecureCompilation.RelationalFront.Fp2_377

/-! ## 1. Inverse multiplicativity over `commRing ξ` (no `Field` instance)

The explicit `inv` is multiplicative on products with nonzero norms.  We do not
have a `Field Fp2_377` instance, so we prove this from the two-sided cancellation
laws (`mul_inv`, `inv_mul`) by uniqueness of inverses. -/

/-- **`norm` of a product is nonzero when both factors' norms are.** Immediate
    from `norm_mul` (`norm (x·y) = norm x · norm y`) and the base field being a
    domain. -/
theorem norm_mul_ne_zero [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377) (x y : Fp2_377)
    (hx : Fp2_377.norm ξ x ≠ 0) (hy : Fp2_377.norm ξ y ≠ 0) :
    letI := Fp2_377.commRing ξ
    Fp2_377.norm ξ (x * y) ≠ 0 := by
  letI := Fp2_377.commRing ξ
  rw [Fp2_377.norm_mul]
  exact mul_ne_zero hx hy

/-- **The explicit inverse is multiplicative** (`inv ξ (a·b) = inv ξ a · inv ξ b`)
    whenever both norms are nonzero — proved from `mul_inv`/`inv_mul` by
    uniqueness of two-sided inverses, **without** a `Field Fp2_377` instance.
    Both `inv ξ (a·b)` and `inv ξ a · inv ξ b` are right inverses of `a·b`, and
    `a·b` is left-invertible (`inv_mul` on `a·b`), so the right inverse is
    unique. -/
theorem inv_mul_inv [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377) (a b : Fp2_377)
    (ha : Fp2_377.norm ξ a ≠ 0) (hb : Fp2_377.norm ξ b ≠ 0) :
    letI := Fp2_377.commRing ξ
    Fp2_377.inv ξ (a * b) = Fp2_377.inv ξ a * Fp2_377.inv ξ b := by
  letI := Fp2_377.commRing ξ
  have hab : Fp2_377.norm ξ (a * b) ≠ 0 := norm_mul_ne_zero ξ a b ha hb
  -- (a·b)·(inv a · inv b) = (a·inv a)·(b·inv b) = 1 (commutative ring rearrange).
  have hright : (a * b) * (Fp2_377.inv ξ a * Fp2_377.inv ξ b) = 1 := by
    have : (a * b) * (Fp2_377.inv ξ a * Fp2_377.inv ξ b)
        = (a * Fp2_377.inv ξ a) * (b * Fp2_377.inv ξ b) := by ring
    rw [this, Fp2_377.mul_inv ξ a ha, Fp2_377.mul_inv ξ b hb, mul_one]
  -- inv(a·b) = inv(a·b)·1 = inv(a·b)·((a·b)·(inv a·inv b))
  --         = (inv(a·b)·(a·b))·(inv a·inv b) = 1·(inv a·inv b) = inv a·inv b.
  calc Fp2_377.inv ξ (a * b)
      = Fp2_377.inv ξ (a * b) * ((a * b) * (Fp2_377.inv ξ a * Fp2_377.inv ξ b)) := by
        rw [hright, mul_one]
    _ = (Fp2_377.inv ξ (a * b) * (a * b)) * (Fp2_377.inv ξ a * Fp2_377.inv ξ b) := by
        ring
    _ = Fp2_377.inv ξ a * Fp2_377.inv ξ b := by
        rw [Fp2_377.inv_mul ξ (a * b) hab, one_mul]

/-! ## 2. The Jacobian→affine projection and the affine group-law maps -/

/-- The **Jacobian→affine projection** `(X, Y, Z) ↦ (X·(Z²)⁻¹, Y·(Z³)⁻¹)`, using
    the **explicit** inverse `inv ξ` (not a `Field` `⁻¹`).  Well-defined when
    `Z ≠ 0` (`norm ξ (Z²)`, `norm ξ (Z³)` nonzero). -/
noncomputable def g2JacToAffine [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (J : Bls377G2JacPoint) : Bls377G2Point :=
  letI := Fp2_377.commRing ξ
  { x := J.X * Fp2_377.inv ξ (J.Z * J.Z)
    y := J.Y * Fp2_377.inv ξ (J.Z * J.Z * J.Z) }

/-- The **affine short-Weierstrass tangent-double** (`a = 0`): slope
    `λ = 3x²·inv(2y)`, `x₃ = λ² − 2x`, `y₃ = λ·(x − x₃) − y`.  The slope's
    denominator `2y` is inverted by the explicit `inv ξ`. -/
noncomputable def g2AffineDbl [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (x y : Fp2_377) : Bls377G2Point :=
  letI := Fp2_377.commRing ξ
  let lam : Fp2_377 := (3 * (x * x)) * Fp2_377.inv ξ (2 * y)
  let x3 : Fp2_377 := lam * lam - 2 * x
  { x := x3, y := lam * (x - x3) - y }

/-- The **affine chord-add**: slope `λ = (y₂−y₁)·inv(x₂−x₁)`,
    `x₃ = λ² − x₁ − x₂`, `y₃ = λ·(x₁ − x₃) − y₁`.  The slope's denominator
    `x₂ − x₁` is inverted by the explicit `inv ξ`. -/
noncomputable def g2AffineAdd [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (x1 y1 x2 y2 : Fp2_377) : Bls377G2Point :=
  letI := Fp2_377.commRing ξ
  let lam : Fp2_377 := (y2 - y1) * Fp2_377.inv ξ (x2 - x1)
  let x3 : Fp2_377 := lam * lam - x1 - x2
  { x := x3, y := lam * (x1 - x3) - y1 }

/-! ## 3. The affine realization ties — closing the deferred `G2` tie

We project the Jacobian double / add through the explicit inverse and recover the
affine group-law map.  The cleared numerator identities from
`RelationalFrontBls377G2` supply `X' = … `, `Y' = …`; the explicit `inv`'s
cancellation law converts those into the affine coordinates. -/

/-- **The `G2` affine double realization.**  Projecting the Jacobian double of the
    affine-embedded `(x, y, 1)` through `g2JacToAffine` recovers the affine
    tangent-double `g2AffineDbl ξ x y`, in the generic chart where the slope
    denominator's norm is nonzero (`norm ξ (2y) ≠ 0`).  This is the fully affine
    `G2` group-law tie that `RelationalFrontBls377G2` deferred for lack of an
    `Fp2_377` inverse; the explicit `inv` and its multiplicativity close it. -/
theorem bls377G2_affine_double_realizes [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (x y : Fp2_377)
    (hy : letI := Fp2_377.commRing ξ; Fp2_377.norm ξ (2 * y) ≠ 0) :
    g2JacToAffine ξ (g2JacDouble ξ (Bls377G2JacPoint.ofAffine ⟨x, y⟩))
      = g2AffineDbl ξ x y := by
  letI := Fp2_377.commRing ξ
  -- Abbreviate the doubling output `Z' = 2y`, and its square/cube.
  have hZZne : Fp2_377.norm ξ (2 * y * (2 * y)) ≠ 0 := norm_mul_ne_zero ξ _ _ hy hy
  have hZ3ne : Fp2_377.norm ξ (2 * y * (2 * y) * (2 * y)) ≠ 0 :=
    norm_mul_ne_zero ξ _ _ hZZne hy
  -- Cancellation of `Z'²` and `Z'³` against their explicit inverses.
  have hcZZ : (2 * y * (2 * y)) * Fp2_377.inv ξ (2 * y * (2 * y)) = 1 :=
    Fp2_377.mul_inv ξ _ hZZne
  have hcZ3 : (2 * y * (2 * y) * (2 * y)) * Fp2_377.inv ξ (2 * y * (2 * y) * (2 * y)) = 1 :=
    Fp2_377.mul_inv ξ _ hZ3ne
  -- Single-power cancellation `Z'·inv Z' = 1`, and multiplicativity of `inv`
  -- collapsing `inv (Z'·Z')`, `inv (Z'³)` to powers of `inv Z'`.
  have hcZ : (2 * y) * Fp2_377.inv ξ (2 * y) = 1 := Fp2_377.mul_inv ξ _ hy
  -- The squared cancellation `(2y)²·(inv 2y)² = 1`, from `hcZ` by `(2yt)²−1 =
  -- (2yt−1)(2yt+1)`.
  have hsq : (2 * y) * (2 * y) * (Fp2_377.inv ξ (2 * y) * Fp2_377.inv ξ (2 * y)) = 1 := by
    linear_combination (2 * y * Fp2_377.inv ξ (2 * y) + 1) * hcZ
  have he2 : Fp2_377.inv ξ (2 * y * (2 * y))
      = Fp2_377.inv ξ (2 * y) * Fp2_377.inv ξ (2 * y) := inv_mul_inv ξ (2 * y) (2 * y) hy hy
  have he3 : Fp2_377.inv ξ (2 * y * (2 * y) * (2 * y))
      = Fp2_377.inv ξ (2 * y) * Fp2_377.inv ξ (2 * y) * Fp2_377.inv ξ (2 * y) := by
    rw [inv_mul_inv ξ (2 * y * (2 * y)) (2 * y) hZZne hy, he2]
  simp only [g2JacToAffine, g2AffineDbl, bls377G2_jacDouble_Z]
  congr 1
  · -- x-coordinate
    rw [bls377G2_jacDouble_X_cleared, bls377G2_jacDouble_Z, he2]
    linear_combination (-(2 * x) * (1 + 2 * y * Fp2_377.inv ξ (2 * y))) * hcZ
  · -- y-coordinate
    rw [bls377G2_jacDouble_Y_cleared, bls377G2_jacDouble_X_cleared, bls377G2_jacDouble_Z,
      he3]
    linear_combination (-y) * hcZ
      + (Fp2_377.inv ξ (2 * y) * (9 * x ^ 3 - 2 * y ^ 2)) * hsq


/-- **The `G2` affine chord-add realization.**  Projecting the Jacobian mixed-add
    of the affine-embedded `(x₁, y₁, 1)`, `(x₂, y₂, 1)` through `g2JacToAffine`
    recovers the affine chord-add `g2AffineAdd ξ x₁ y₁ x₂ y₂`, in the generic
    chart where the slope denominator's norm is nonzero (`norm ξ (x₂−x₁) ≠ 0`). -/
theorem bls377G2_affine_add_realizes [Fact (Nat.Prime bls377Q)] (ξ : FpBLS377)
    (x1 y1 x2 y2 : Fp2_377) (hH : Fp2_377.norm ξ (x2 - x1) ≠ 0) :
    g2JacToAffine ξ (g2JacAddZ1 ξ (Bls377G2JacPoint.ofAffine ⟨x1, y1⟩)
        (Bls377G2JacPoint.ofAffine ⟨x2, y2⟩))
      = g2AffineAdd ξ x1 y1 x2 y2 := by
  letI := Fp2_377.commRing ξ
  -- Abbreviate the chord output `Z' = H = x₂ − x₁`, with its square and cube.
  have hHHne : Fp2_377.norm ξ ((x2 - x1) * (x2 - x1)) ≠ 0 := norm_mul_ne_zero ξ _ _ hH hH
  have hH3ne : Fp2_377.norm ξ ((x2 - x1) * (x2 - x1) * (x2 - x1)) ≠ 0 :=
    norm_mul_ne_zero ξ _ _ hHHne hH
  -- Single/squared cancellation `H·inv H = 1`, `H²·(inv H)² = 1`, and the
  -- inverse-multiplicativity collapse of `inv (H²)`, `inv (H³)` to powers of `inv H`.
  have hcH : (x2 - x1) * Fp2_377.inv ξ (x2 - x1) = 1 := Fp2_377.mul_inv ξ _ hH
  have hsq : (x2 - x1) * (x2 - x1)
      * (Fp2_377.inv ξ (x2 - x1) * Fp2_377.inv ξ (x2 - x1)) = 1 := by
    linear_combination ((x2 - x1) * Fp2_377.inv ξ (x2 - x1) + 1) * hcH
  have he2 : Fp2_377.inv ξ ((x2 - x1) * (x2 - x1))
      = Fp2_377.inv ξ (x2 - x1) * Fp2_377.inv ξ (x2 - x1) :=
    inv_mul_inv ξ (x2 - x1) (x2 - x1) hH hH
  have he3 : Fp2_377.inv ξ ((x2 - x1) * (x2 - x1) * (x2 - x1))
      = Fp2_377.inv ξ (x2 - x1) * Fp2_377.inv ξ (x2 - x1) * Fp2_377.inv ξ (x2 - x1) := by
    rw [inv_mul_inv ξ ((x2 - x1) * (x2 - x1)) (x2 - x1) hHHne hH, he2]
  have hcube : (x2 - x1) * (x2 - x1) * (x2 - x1)
      * (Fp2_377.inv ξ (x2 - x1) * Fp2_377.inv ξ (x2 - x1) * Fp2_377.inv ξ (x2 - x1)) = 1 := by
    linear_combination ((x2 - x1) * (x2 - x1) * (Fp2_377.inv ξ (x2 - x1) * Fp2_377.inv ξ (x2 - x1))
      + (x2 - x1) * Fp2_377.inv ξ (x2 - x1) + 1) * hcH
  simp only [g2JacToAffine, g2AffineAdd, bls377G2_jacAdd_Z]
  congr 1
  · -- x-coordinate
    rw [bls377G2_jacAdd_X_cleared, he2]
    linear_combination (-(x1 + x2)) * hsq
  · -- y-coordinate
    rw [bls377G2_jacAdd_Y_cleared, bls377G2_jacAdd_X_cleared, he3]
    linear_combination (3 * (y2 - y1) * x1 * Fp2_377.inv ξ (x2 - x1)) * hsq
      + ((y2 - y1) - y1) * hcube + (-(y2 - y1)) * hcH

end CatCrypt.Crypto.SecureCompilation.RelationalFront
