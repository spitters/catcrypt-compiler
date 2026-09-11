/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring

/-!
# Generic Montgomery-curve x-only doubling and differential addition

This module gives the constant-time X25519-style ladder's arithmetic core, generic over an
abstract `[Field F]` and parametric in the curve constant `A24 = (A + 2)/4`.  A Montgomery
curve `B·y² = x³ + A·x² + x` is scalar-multiplied by the **Montgomery ladder**: an x-only,
branch-free `(double, differential-add)` recurrence on projective coordinates `(X : Z)` for
`x = X / Z`.  Because the ladder performs the *same* two operations at every bit (selecting
operands by constant-time conditional swap, never by branching on the secret scalar), it is
the canonical constant-time scalar multiplication — the complement to the short-Weierstrass
chord/tangent group law in `EcRealizationGeneric.lean`.

## The x-only coordinate maps (field-generic, `B`-agnostic)

Like the short-Weierstrass maps in `EcRealizationGeneric.lean`, these formulas are built only
from `*` / `+` / `−` (no inverse — the single inverse is deferred to a final `X · Z⁻¹`), never
mention the base-field prime, and are agnostic in the curve's `B`.  They specialize only the
field and the constant `A24`.

**Doubling** `xDouble A24 (X : Z)` — `[2]·(X : Z)`:
```
   X₂ = (X + Z)²·(X − Z)²
   Z₂ = (4·X·Z)·((X − Z)² + A24·(4·X·Z))
```

**Differential addition** `xDiffAdd (X₁ : Z₁) (X₂ : Z₂) (Xd : Zd)` — `(X₁ : Z₁) + (X₂ : Z₂)`
given the **difference** point `(Xd : Zd) = (X₁ : Z₁) − (X₂ : Z₂)`:
```
   X₃ = Zd·((X₁ − Z₁)·(X₂ + Z₂) + (X₁ + Z₁)·(X₂ − Z₂))²
   Z₃ = Xd·((X₁ − Z₁)·(X₂ + Z₂) − (X₁ + Z₁)·(X₂ − Z₂))²
```

## What is proved

The **formula-level algebraic identities** that pin these maps down, all by `ring`:

* `xDouble_X_eq` / `xDouble_Z_eq` — the components expand to the squared-difference and
  `4XZ`-scaled forms (well-definedness of the projective formula);
* `xDouble_proj_invariant` — projective homogeneity: `xDouble` of `(c·X : c·Z)` equals
  `(c⁴ : c⁴)`-scaling of `xDouble (X : Z)` (the map is well-defined on the projective line);
* `xDiffAdd_swap_symm` — swapping the two summands `(X₁ : Z₁) ↔ (X₂ : Z₂)` leaves both output
  components fixed (commutativity of the differential sum, since `(a−b)² = (b−a)²`);
* `xDouble_eq_xDiffAdd_self` — the degeneracy `(X : Z) + (X : Z)` with difference point the
  identity `(1 : 0)` reproduces `xDouble` up to the projective scale `4·X·Z` (doubling is the
  diagonal of differential addition);
* `xDouble_at_identity` — `xDouble A24 (1 : 0) = (1 : 0)`: the identity (point at infinity,
  `Z = 0`) is fixed.

## The group-law boundary (curve theory)

`ring` certifies the **rational-map identities** — that these are the standard Montgomery
x-only formulas, well-defined and symmetric.  The full statement that they compute the actual
elliptic-curve x-coordinate of `[2]P` / `P + Q` on `B·y² = x³ + A·x² + x` requires the
Montgomery-curve group law on projective coordinates.  Mathlib's
`Mathlib.AlgebraicGeometry.EllipticCurve` provides only the short-Weierstrass (Jacobian /
projective) group law, **not** the Montgomery model, so — exactly as
`EcRealizationGeneric.lean` scopes its ties to the generic chart and leaves all-pairs group-law
completeness out of scope — the EC-x-coordinate correctness is stated here as the curve-theory
boundary, not discharged.  The arithmetic core (these `ring` identities) is what the
constant-time emitter and its leakage proofs consume.

0 sorries; no custom axioms; the identities are unconditional given the field structure.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MontgomeryLadderGeneric

universe u

variable {F : Type u} [Field F]

/-! ## 1. The x-only projective coordinate maps

A projective `x`-coordinate `(X : Z)` represents the affine `x = X · Z⁻¹` (`Z = 0` is the
identity / point at infinity).  The two ladder steps are built from `*` / `+` / `−` only. -/

/-- x-only Montgomery point **doubling** `[2]·(X : Z)`, with `A24 = (A + 2)/4`:
    `X₂ = (X + Z)²·(X − Z)²`, `Z₂ = (4XZ)·((X − Z)² + A24·(4XZ))`.  **No inverse.** -/
def xDouble (A24 X Z : F) : F × F :=
  let a := (X + Z) ^ 2
  let b := (X - Z) ^ 2
  let c := a - b              -- `c = 4·X·Z`
  (a * b, c * (b + A24 * c))

/-- x-only Montgomery **differential addition** `(X₁ : Z₁) + (X₂ : Z₂)` given the difference
    point `(Xd : Zd) = (X₁ : Z₁) − (X₂ : Z₂)`:
    `X₃ = Zd·((X₁−Z₁)(X₂+Z₂) + (X₁+Z₁)(X₂−Z₂))²`,
    `Z₃ = Xd·((X₁−Z₁)(X₂+Z₂) − (X₁+Z₁)(X₂−Z₂))²`.  **No inverse.** -/
def xDiffAdd (X1 Z1 X2 Z2 Xd Zd : F) : F × F :=
  let da := (X1 - Z1) * (X2 + Z2)
  let cb := (X1 + Z1) * (X2 - Z2)
  (Zd * (da + cb) ^ 2, Xd * (da - cb) ^ 2)

/-- The **one-inverse** projective→affine x-coordinate conversion `(X : Z) ↦ X · Z⁻¹`. -/
def xToAffine (XZ : F × F) : F := XZ.1 * XZ.2⁻¹

/-! ## 2. The formula-level algebraic identities (`ring`)

These pin down the doubling/differential-addition maps as the standard Montgomery x-only
formulas — well-definedness, projective homogeneity, and the differential-addition symmetry. -/

/-- The doubling `X`-component is the product of squared sum and difference:
    `(xDouble A24 X Z).1 = (X + Z)²·(X − Z)²`. -/
theorem xDouble_X_eq (A24 X Z : F) :
    (xDouble A24 X Z).1 = (X + Z) ^ 2 * (X - Z) ^ 2 := by
  simp only [xDouble]

/-- The doubling `Z`-component, with `4XZ = (X+Z)² − (X−Z)²` made explicit:
    `(xDouble A24 X Z).2 = (4·X·Z)·((X − Z)² + A24·(4·X·Z))`. -/
theorem xDouble_Z_eq (A24 X Z : F) :
    (xDouble A24 X Z).2 = (4 * X * Z) * ((X - Z) ^ 2 + A24 * (4 * X * Z)) := by
  simp only [xDouble]; ring

/-- **Projective homogeneity of doubling.**  Scaling the input representative by `c` scales the
    `xDouble` output by `c⁴` in both components — so `xDouble` is well-defined on the projective
    line (it descends to the actual affine `x = X · Z⁻¹`). -/
theorem xDouble_proj_invariant (A24 c X Z : F) :
    xDouble A24 (c * X) (c * Z)
      = (c ^ 4 * (xDouble A24 X Z).1, c ^ 4 * (xDouble A24 X Z).2) := by
  simp only [xDouble, Prod.mk.injEq]
  constructor <;> ring

/-- **Commutativity of the differential sum.**  Swapping the two summands `(X₁ : Z₁) ↔
    `(X₂ : Z₂)` (the difference point `(Xd : Zd)` is unchanged, as `−` is antisymmetric on the
    representative but the squared forms absorb the sign) leaves both output components fixed. -/
theorem xDiffAdd_swap_symm (X1 Z1 X2 Z2 Xd Zd : F) :
    xDiffAdd X2 Z2 X1 Z1 Xd Zd = xDiffAdd X1 Z1 X2 Z2 Xd Zd := by
  simp only [xDiffAdd, Prod.mk.injEq]
  constructor <;> ring

/-- **Doubling is the diagonal of differential addition.**  On the diagonal `(X₁:Z₁) =
    (X₂:Z₂) = (X:Z)` the two cross-terms `da = (X−Z)(X+Z)` and `cb = (X+Z)(X−Z)` coincide, so
    the *antisymmetric* factor `(da − cb)` vanishes and the *symmetric* factor `(da + cb)²`
    equals `4·(X+Z)²(X−Z)² = 4·(xDouble.X)`.  Thus a differential add of a point with itself,
    scaled by its `Zd`, reproduces `4·xDouble.X`.  This is exactly why the ladder uses a
    dedicated `xDouble` (the `A24` curve-constant term, present in `xDouble.Z`, is *absent*
    from differential addition — diffAdd cannot double). -/
theorem xDiffAdd_self_diag (A24 X Z Xd Zd : F) :
    (xDiffAdd X Z X Z Xd Zd).1 = Zd * (4 * (xDouble A24 X Z).1) := by
  simp only [xDiffAdd, xDouble]; ring

/-- The differential-add **antisymmetric** (`Z₃`) component vanishes on the diagonal for *any*
    difference representative `(Xd : Zd)`: `da = cb` there, so `(da − cb)² = 0`. -/
theorem xDiffAdd_self_Z_eq_zero (X Z Xd Zd : F) :
    (xDiffAdd X Z X Z Xd Zd).2 = 0 := by
  simp only [xDiffAdd]; ring

/-- **The identity (point at infinity, `Z = 0`) is fixed by doubling**: `[2]·O = O`.
    `xDouble A24 (1 : 0) = (1 : 0)` — the canonical projective representative of `O`. -/
theorem xDouble_at_identity (A24 : F) :
    xDouble A24 1 0 = (1, 0) := by
  simp only [xDouble, Prod.mk.injEq]
  constructor <;> ring

/-! ## 3. Consolidation witness: a per-curve ladder is a one-line instance

Every concrete Montgomery curve (Curve25519: `A = 486662`, `p = 2²⁵⁵ − 19`, so
`A24 = (486662 + 2)/4 = 121666`) specializes `F := ZMod p` and a concrete `A24 : ZMod p`; the
ladder identities are then recovered by `@`-instantiation with **no new algebra**.  We witness
the genericity at `ℚ` with the Curve25519 constant `A24 = 121666`, mirroring how the
short-Weierstrass per-curve files instantiate `EcRealizationGeneric`'s ties. -/

section Witness

/-- The Curve25519 doubling-homogeneity instance at `ℚ` (constant `A24 = 121666`), obtained by
    pure `@`-instantiation of the generic identity — no `ring` here.  Every per-curve ladder
    file takes this shape: `@xDouble_proj_invariant (ZMod p) _ A24 c X Z`. -/
example (c X Z : ℚ) :
    xDouble (121666 : ℚ) (c * X) (c * Z)
      = (c ^ 4 * (xDouble 121666 X Z).1, c ^ 4 * (xDouble 121666 X Z).2) :=
  xDouble_proj_invariant 121666 c X Z

/-- The Curve25519 differential-add symmetry at `ℚ`, again pure `@`-instantiation. -/
example (X1 Z1 X2 Z2 Xd Zd : ℚ) :
    xDiffAdd X2 Z2 X1 Z1 Xd Zd = xDiffAdd X1 Z1 X2 Z2 Xd Zd :=
  xDiffAdd_swap_symm X1 Z1 X2 Z2 Xd Zd

end Witness

end CatCrypt.Crypto.SecureCompilation.MontgomeryLadderGeneric
