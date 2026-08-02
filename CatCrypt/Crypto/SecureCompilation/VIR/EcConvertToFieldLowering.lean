/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.EcConvertFieldEmit
import Mathlib.Algebra.Field.ZMod

/-!
# `ecConvertDialect` → `fieldDialect` per-coordinate lowering

`ecConvertDialect` (`VIR/EcConvertOps.lean`) has two ops,
`EcConvertOp.affineToJacobian` and `EcConvertOp.jacobianToAffine`, whose operand
types are coordinate *tuples* (`⟦affine p⟧ = ZMod p × ZMod p`,
`⟦jacobian p⟧ = ZMod p × ZMod p × ZMod p`).  `fieldDialect`'s types are single
field elements (`FieldTy.fp p`), so a tuple has no single `fieldDialect` type and
the 1:1 `mapTy` frameworks (`ComParametricityTransport.LoweringData`,
`FieldDialectBlockDescent.BlockLoweringData`) do not apply.  The lowering here is
per output coordinate: one `Com fieldDialect` schedule per component, and a joint
theorem stating that the tuple of schedule denotations equals the op's
denotation.

The invert-first Jacobian → affine schedules are
`EcConvertFieldEmit.jacToAffXProg` / `jacToAffYProg`, which follow the leaf
`EcConvertOps.jacobianToAffineF` in taking `Z⁻¹` and then its powers.  This
module adds the affine → Jacobian schedules, the square-first Jacobian → affine
schedules `(X·(Z²)⁻¹, Y·(Z³)⁻¹)` used by the curve emit kernels, the joint
op-level ties for both directions and both orders, the schedule-level round trip,
and the two `Z`-dependent facts.

The `ecConvertDialect` ops are single-point, so the lowering is single-point: it
spends one inverse per point.  The batched normalisation a Pippenger MSM output
needs — accumulate the `Z²`/`Z³` denominators across points, clear them with one
inverse — is not expressible against a single-point op signature and lives in
`Pairing/BLS12381GroupEmit.wireBatchInv`.

## Main definitions

* `Γaff` — the affine input context `[fp p, fp p]` carrying `x, y`.
* `affVal` — the valuation `⟨x, y⟩` of `Γaff`.
* `affToJacXProg`, `affToJacYProg`, `affToJacZProg` — the three
  `Com fieldDialect` output-coordinate schedules of `affineToJacobian`
  (`fCopy x`, `fCopy y`, `fConst 1`).
* `jacToAffXSqProg`, `jacToAffYSqProg` — the square-first Jacobian → affine
  coordinate schedules `X·(Z²)⁻¹` / `Y·(Z³)⁻¹`.
* `fpDenote` — a schedule's denotation at type `ZMod p`, the projection field
  arithmetic on a denotation is stated through.

## Main results

Hypothesis-free:

* `affToJacX_denote`, `affToJacY_denote`, `affToJacZ_denote` — each affine →
  Jacobian schedule denotes to its component of
  `EcConvertOps.affineToJacobianF`.
* `affToJac_op_denote` — the triple of affine → Jacobian schedules equals
  `ecConvertDenote.denote (.affineToJacobian p)` on the same input.
* `jacToAff_op_denote` — the pair of Jacobian → affine schedules equals
  `ecConvertDenote.denote (.jacobianToAffine p)` on the same input.
* `field_roundtrip` — running the affine → Jacobian schedules and feeding their
  outputs to the Jacobian → affine schedules returns the input affine point.
* `jacToAff_at_zero` — at `Z = 0` the Jacobian → affine schedules return
  `(0, 0)`, the short-Weierstrass identity sentinel, since `(0 : ZMod p)⁻¹ = 0`.

Carrying a hypothesis:

* `jacToAffXSq_eq_jacToAffX`, `jacToAffYSq_eq_jacToAffY` (`[Fact p.Prime]`) — the
  square-first and invert-first coordinate schedules denote equally.
* `jacToAffSq_op_denote` (`[Fact p.Prime]`) — the pair of square-first schedules
  equals `ecConvertDenote.denote (.jacobianToAffine p)`.
* `jacToAffX_scales_back`, `jacToAffY_scales_back`, `jacToAff_scales_back`
  (`[Fact p.Prime]`, `Z ≠ 0`) — scaling the schedule output back by `λ = Z` under
  the Jacobian weights recovers `(X, Y, Z)`, so the output is a representative of
  the input's projective class.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EcConvertToFieldLowering

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.EcConvertOps
open CatCrypt.Crypto.SecureCompilation.VIR.EcConvertFieldEmit

variable {p : Nat}

/-! ## 1. The affine input context

`Γaff = [fp p, fp p]` holds the affine coordinates `x, y` at indices `0, 1`. -/

/-- The affine input context: the coordinates `x, y`. -/
abbrev Γaff (p : Nat) : Ctxt fieldDialect :=
  [FieldTy.fp p, FieldTy.fp p]

/-- De Bruijn variable for `x` (index 0). -/
def vAx : Ctxt.Var (Γaff p) (FieldTy.fp p) := .here

/-- De Bruijn variable for `y` (index 1). -/
def vAy : Ctxt.Var (Γaff p) (FieldTy.fp p) := .there .here

/-- The valuation `⟨x, y⟩` of `Γaff`. -/
def affVal (x y : ZMod p) : Ctxt.Valuation (Γaff p) :=
  .cons x (.cons y .nil)

/-- The denotation of a `Com fieldDialect` schedule ending in `fp p`, at type
    `ZMod p`.  `⟦FieldTy.fp p⟧` reduces to `ZMod p` for unification but not for
    instance search, so field arithmetic on a schedule's denotation is stated
    through this projection. -/
def fpDenote {Γ : Ctxt fieldDialect} (c : Com fieldDialect Γ (FieldTy.fp p))
    (V : Ctxt.Valuation Γ) : ZMod p := c.denote V

/-! ## 2. The affine → Jacobian output-coordinate schedules

`affineToJacobian` is the `Z = 1` embedding `(x, y) ↦ (x, y, 1)`, so the three
output coordinates are two copies and one constant:

    affToJacXProg : x₃ = fCopy x
    affToJacYProg : y₃ = fCopy y
    affToJacZProg : z₃ = fConst 1
-/

/-- The Jacobian `X = x` output schedule of `affineToJacobian`. -/
def affToJacXProg : Com fieldDialect (Γaff p) (FieldTy.fp p) :=
  .var (.mk (.fCopy p) rfl (.cons vAx .nil)) (.ret .here)

/-- The Jacobian `Y = y` output schedule of `affineToJacobian`. -/
def affToJacYProg : Com fieldDialect (Γaff p) (FieldTy.fp p) :=
  .var (.mk (.fCopy p) rfl (.cons vAy .nil)) (.ret .here)

/-- The Jacobian `Z = 1` output schedule of `affineToJacobian`. -/
def affToJacZProg : Com fieldDialect (Γaff p) (FieldTy.fp p) :=
  .var (.mk (.fConst p 1) rfl .nil) (.ret .here)

/-! ## 3. Per-coordinate denotation ties (hypothesis-free)

Each schedule denotes to its component of `EcConvertOps.affineToJacobianF`. -/

/-- `affToJacXProg` denotes to the first component of `affineToJacobianF`. -/
theorem affToJacX_denote (x y : ZMod p) :
    (affToJacXProg (p := p)).denote (affVal x y)
      = (affineToJacobianF p (x, y)).1 := rfl

/-- `affToJacYProg` denotes to the second component of `affineToJacobianF`. -/
theorem affToJacY_denote (x y : ZMod p) :
    (affToJacYProg (p := p)).denote (affVal x y)
      = (affineToJacobianF p (x, y)).2.1 := rfl

/-- `affToJacZProg` denotes to the third component of `affineToJacobianF`, the
    constant `1`. -/
theorem affToJacZ_denote (x y : ZMod p) :
    (affToJacZProg (p := p)).denote (affVal x y)
      = (affineToJacobianF p (x, y)).2.2 := rfl

/-! ## 4. The joint op-level ties (hypothesis-free)

For each op, the tuple of output-coordinate schedule denotations equals the
`ecConvertDialect` op denotation on the corresponding input. -/

/-- The triple of affine → Jacobian schedules equals the `affineToJacobian` op
    denotation. -/
theorem affToJac_op_denote (x y : ZMod p) :
    ((affToJacXProg (p := p)).denote (affVal x y),
     (affToJacYProg (p := p)).denote (affVal x y),
     (affToJacZProg (p := p)).denote (affVal x y))
      = ecConvertDenote.denote (.affineToJacobian p) (.cons (x, y) .nil) := rfl

/-- The pair of Jacobian → affine schedules equals the `jacobianToAffine` op
    denotation.  `jacobianToAffineF` is total, so this needs no condition on
    `Z`. -/
theorem jacToAff_op_denote (X Y Z : ZMod p) :
    ((jacToAffXProg (p := p)).denote (eval X Y Z),
     (jacToAffYProg (p := p)).denote (eval X Y Z))
      = ecConvertDenote.denote (.jacobianToAffine p) (.cons (X, Y, Z) .nil) :=
  jacToAff_denote X Y Z

/-! ## 5. The schedule-level round trip (hypothesis-free) -/

/-- Running the affine → Jacobian schedules and feeding their three outputs to
    the Jacobian → affine schedules returns the input affine point — the
    schedule-level form of `EcConvertOps.jacobianToAffine_affineToJacobian`. -/
theorem field_roundtrip (x y : ZMod p) :
    ((jacToAffXProg (p := p)).denote
        (eval ((affToJacXProg (p := p)).denote (affVal x y))
              ((affToJacYProg (p := p)).denote (affVal x y))
              ((affToJacZProg (p := p)).denote (affVal x y))),
     (jacToAffYProg (p := p)).denote
        (eval ((affToJacXProg (p := p)).denote (affVal x y))
              ((affToJacYProg (p := p)).denote (affVal x y))
              ((affToJacZProg (p := p)).denote (affVal x y))))
      = (x, y) :=
  (jacToAff_denote x y 1).trans (jacobianToAffine_affineToJacobian (x, y))

/-! ## 6. The square-first Jacobian → affine schedules

`EcConvertOps.jacobianToAffineF` and the `EcConvertFieldEmit` schedules invert
first and then take powers: `(X·(Z⁻¹)², Y·(Z⁻¹)³)`.  The curve emit kernels
(`Pairing/BLS12381ProjectiveEmit.lean`, `Pairing/BN254ProjectiveEmit.lean`) take
powers first and then invert: `(X·(Z²)⁻¹, Y·(Z³)⁻¹)`.  The two orders compute the
same value over a prime field.  In the square-first order the inverse is applied
to the denominators `Z²`, `Z³` themselves, which is the shape a batch multiplies
together to clear with a single inverse
(`Pairing/BLS12381GroupEmit.wireBatchInv`).

    jacToAffXSqProg : Com fieldDialect [fp p, fp p, fp p] (fp p)   over (X, Y, Z)
        z2  = fMul Z Z       -- Z²
        zi2 = fInv z2        -- (Z²)⁻¹
        rx  = fMul X zi2     -- X·(Z²)⁻¹
        ret rx
    jacToAffYSqProg : Com fieldDialect [fp p, fp p, fp p] (fp p)   over (X, Y, Z)
        z2  = fMul Z Z       -- Z²
        z3  = fMul z2 Z      -- Z³
        zi3 = fInv z3        -- (Z³)⁻¹
        ry  = fMul Y zi3     -- Y·(Z³)⁻¹
        ret ry
-/

/-- The affine `x = X·(Z²)⁻¹` coordinate schedule: square, invert, multiply. -/
def jacToAffXSqProg : Com fieldDialect (Γ₀ p) (FieldTy.fp p) :=
  -- z2 = Z * Z            (Z at idx 2)
  .var (.mk (.fMul p) rfl (.cons vZ (.cons vZ .nil)))
  -- zi2 = (z2)⁻¹          (z2 at idx 0)
  (.var (.mk (.fInv p) rfl (.cons .here .nil))
  -- rx = X * zi2          (X shifted twice → idx 2, zi2 at idx 0)
  (.var (.mk (.fMul p) rfl
      (.cons (.there (.there vX)) (.cons .here .nil)))
  (.ret .here)))

/-- The affine `y = Y·(Z³)⁻¹` coordinate schedule: square, cube, invert,
    multiply. -/
def jacToAffYSqProg : Com fieldDialect (Γ₀ p) (FieldTy.fp p) :=
  -- z2 = Z * Z            (Z at idx 2)
  .var (.mk (.fMul p) rfl (.cons vZ (.cons vZ .nil)))
  -- z3 = z2 * Z           (z2 at idx 0, Z shifted once → idx 3)
  (.var (.mk (.fMul p) rfl (.cons .here (.cons (.there vZ) .nil)))
  -- zi3 = (z3)⁻¹          (z3 at idx 0)
  (.var (.mk (.fInv p) rfl (.cons .here .nil))
  -- ry = Y * zi3          (Y shifted three times → idx 4, zi3 at idx 0)
  (.var (.mk (.fMul p) rfl
      (.cons (.there (.there (.there vY))) (.cons .here .nil)))
  (.ret .here))))

/-- `jacToAffXSqProg` denotes the native form `X · (Z · Z)⁻¹`. -/
theorem jacToAffXSq_field_denote (X Y Z : ZMod p) :
    (jacToAffXSqProg (p := p)).denote (eval X Y Z) = X * (Z * Z)⁻¹ := rfl

/-- `jacToAffYSqProg` denotes the native form `Y · ((Z · Z) · Z)⁻¹`. -/
theorem jacToAffYSq_field_denote (X Y Z : ZMod p) :
    (jacToAffYSqProg (p := p)).denote (eval X Y Z) = Y * (Z * Z * Z)⁻¹ := rfl

/-- Over a prime field the two `x`-coordinate schedules agree: squaring before
    inverting gives the same value as inverting before squaring. -/
theorem jacToAffXSq_eq_jacToAffX [Fact p.Prime] (X Y Z : ZMod p) :
    fpDenote (jacToAffXSqProg (p := p)) (eval X Y Z)
      = fpDenote (jacToAffXProg (p := p)) (eval X Y Z) := by
  show X * (Z * Z)⁻¹ = X * (Z⁻¹ * Z⁻¹)
  rw [mul_inv]

/-- Over a prime field the two `y`-coordinate schedules agree: cubing before
    inverting gives the same value as inverting before cubing. -/
theorem jacToAffYSq_eq_jacToAffY [Fact p.Prime] (X Y Z : ZMod p) :
    fpDenote (jacToAffYSqProg (p := p)) (eval X Y Z)
      = fpDenote (jacToAffYProg (p := p)) (eval X Y Z) := by
  show Y * (Z * Z * Z)⁻¹ = Y * (Z⁻¹ * Z⁻¹ * Z⁻¹)
  rw [mul_inv, mul_inv]

/-- Over a prime field the pair of square-first schedules equals the
    `jacobianToAffine` op denotation, the same tie `jacToAff_op_denote` gives for
    the invert-first pair. -/
theorem jacToAffSq_op_denote [Fact p.Prime] (X Y Z : ZMod p) :
    ((jacToAffXSqProg (p := p)).denote (eval X Y Z),
     (jacToAffYSqProg (p := p)).denote (eval X Y Z))
      = ecConvertDenote.denote (.jacobianToAffine p) (.cons (X, Y, Z) .nil) := by
  rw [show (jacToAffXSqProg (p := p)).denote (eval X Y Z)
        = (jacToAffXProg (p := p)).denote (eval X Y Z) from
      jacToAffXSq_eq_jacToAffX X Y Z,
    show (jacToAffYSqProg (p := p)).denote (eval X Y Z)
        = (jacToAffYProg (p := p)).denote (eval X Y Z) from
      jacToAffYSq_eq_jacToAffY X Y Z]
  exact jacToAff_op_denote X Y Z

/-! ## 7. The two `Z`-dependent facts

`jacobianToAffineF` is total because `(0 : ZMod p)⁻¹ = 0`; at `Z = 0` the
schedules return `(0, 0)`.  Faithfulness to the projective quotient — the output
being a representative of the input's class — is the `Z ≠ 0` statement. -/

/-- At `Z = 0` the Jacobian → affine schedules return `(0, 0)`, the
    short-Weierstrass identity sentinel. -/
theorem jacToAff_at_zero (X Y : ZMod p) :
    ((jacToAffXProg (p := p)).denote (eval X Y 0),
     (jacToAffYProg (p := p)).denote (eval X Y 0))
      = ((0 : ZMod p), (0 : ZMod p)) := by
  rw [jacToAffX_field_denote, jacToAffY_field_denote, ZMod.inv_zero]
  simp

/-- For `Z ≠ 0` over a prime field, the `x`-coordinate schedule scaled by `Z²`
    recovers the input `X`. -/
theorem jacToAffX_scales_back [Fact p.Prime] (X Y Z : ZMod p) (hZ : Z ≠ 0) :
    fpDenote (jacToAffXProg (p := p)) (eval X Y Z) * Z ^ 2 = X := by
  show X * (Z⁻¹ * Z⁻¹) * Z ^ 2 = X
  have h : Z⁻¹ * Z = 1 := ZMod.inv_mul_of_unit Z (isUnit_iff_ne_zero.mpr hZ)
  calc X * (Z⁻¹ * Z⁻¹) * Z ^ 2 = X * (Z⁻¹ * Z) * (Z⁻¹ * Z) := by ring
    _ = X := by rw [h]; ring

/-- For `Z ≠ 0` over a prime field, the `y`-coordinate schedule scaled by `Z³`
    recovers the input `Y`. -/
theorem jacToAffY_scales_back [Fact p.Prime] (X Y Z : ZMod p) (hZ : Z ≠ 0) :
    fpDenote (jacToAffYProg (p := p)) (eval X Y Z) * Z ^ 3 = Y := by
  show Y * (Z⁻¹ * Z⁻¹ * Z⁻¹) * Z ^ 3 = Y
  have h : Z⁻¹ * Z = 1 := ZMod.inv_mul_of_unit Z (isUnit_iff_ne_zero.mpr hZ)
  calc Y * (Z⁻¹ * Z⁻¹ * Z⁻¹) * Z ^ 3
      = Y * (Z⁻¹ * Z) * (Z⁻¹ * Z) * (Z⁻¹ * Z) := by ring
    _ = Y := by rw [h]; ring

/-- For `Z ≠ 0` over a prime field, scaling the schedule output back by `λ = Z`
    under the Jacobian weights `(λ²x, λ³y, λ)` recovers `(X, Y, Z)`: the affine
    point the schedules compute is a representative of the input's projective
    class. -/
theorem jacToAff_scales_back [Fact p.Prime] (X Y Z : ZMod p) (hZ : Z ≠ 0) :
    (fpDenote (jacToAffXProg (p := p)) (eval X Y Z) * Z ^ 2,
     fpDenote (jacToAffYProg (p := p)) (eval X Y Z) * Z ^ 3, Z)
      = (X, Y, Z) := by
  rw [jacToAffX_scales_back X Y Z hZ, jacToAffY_scales_back X Y Z hZ]

/-! ## 8. Concrete check

Over `ZMod 7`, the affine point `(2, 3)` embeds to the Jacobian triple `(2, 3, 1)`
through the three affine → Jacobian schedules. -/

example :
    ((affToJacXProg (p := 7)).denote (affVal 2 3),
     (affToJacYProg (p := 7)).denote (affVal 2 3),
     (affToJacZProg (p := 7)).denote (affVal 2 3))
      = ((2, 3, 1) : ZMod 7 × ZMod 7 × ZMod 7) := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.EcConvertToFieldLowering
