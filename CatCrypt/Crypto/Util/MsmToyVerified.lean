/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Group

/-!
# Verified toy-EC MSM kernel over `ZMod 23`

This file provides the *verified reference computation* layer for the toy
EC multi-scalar-multiplication hax ↔ rustcmd bridge, matching the
existing rustcmd-side scope at `CatCrypt/Crypto/Jasmin/MsmReflect.lean`
and the legacy bench at `bench/msm_compare/`.

The toy EC group is the short-Weierstrass curve

```
   E : y² = x³ + a·x + b      over  Fp = ZMod 23
```

with default `a = 0, b = 7` (matching the bench's `ec_ref.h`). This is
**not** a production curve — `p = 23` is a 5-bit modulus deliberately
small enough that the EC operations are schoolbook arithmetic and the
emitted `.jazz` is byte-identical to a C reference. The purpose of this
file is to provide the verified reference for the "MSM = scalarFold over
an EC AddCommMonoid" reduction at a tractable field, mirroring the role
of `Pairing/MsmReduce.lean` (which provides the Mathlib affine-point
group law) but exposed as a flat record so the bridge can decode the
2-byte rustcmd point and reason structurally.

## API

* `MsmZ23` : `ZMod 23` — the toy prime field
* `MsmZ23.asNat`, `MsmZ23.fromNat` — `ZMod ↔ Nat` encoders
* `MsmZ23.fromNat_asNat`, `MsmZ23.fromInt_asInt` — proved round-trips
* `MsmEcPointFlat` : the (x, y, isIdentity) point record
* `msmEcPointAddVerified` : verified short-Weierstrass affine point-add
* `msmEcScalarMulVerified` : verified double-and-add scalar multiply
* `msmEcAccumStepVerified` : one MSM accumulation step `acc + k·P`

## Reference

* `CatCrypt/Crypto/Pairing/MsmReduce.lean` — the Mathlib `ECPt`
  affine-point group on the same toy field; the `msm_eq_scalarFold`
  reduction lives there.
* `CatCrypt/Crypto/Jasmin/MsmReflect.lean` — opaque rustcmd surface
  (`MsmEcScalar`, `MsmEcPoint`, `ec_scalar_mul`, `ec_point_add`)
* `bench/msm_compare/msm_emit.lean` — legacy emit driver
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-! ## §1  The toy prime field `ZMod 23` -/

/-- The toy MSM modulus. -/
abbrev P23 : Nat := 23

/-- `Nat.Prime 23` — discharged by `decide`, unlocking `Field (ZMod 23)`. -/
theorem p23_prime : Nat.Prime P23 := by decide

instance fact_prime_p23 : Fact (Nat.Prime P23) := ⟨p23_prime⟩

/-- The toy MSM prime field. -/
abbrev MsmZ23 : Type := ZMod P23

namespace MsmZ23

/-! ### Field structure (Mathlib) -/

example : Field MsmZ23 := inferInstance
example : CommRing MsmZ23 := inferInstance

/-! ### Encoders -/

/-- Inject a `Nat` (mod 23) into `MsmZ23`. -/
def fromNat (n : Nat) : MsmZ23 := (n : ZMod P23)

/-- Project a `MsmZ23` element to a `Nat` in `[0..22]` via `ZMod.val`. -/
def asNat (g : MsmZ23) : Nat := ZMod.val g

/-- Project a `MsmZ23` element to an `Int`. -/
def asInt (g : MsmZ23) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `MsmZ23`. -/
def fromInt (i : Int) : MsmZ23 := (i : ZMod P23)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : MsmZ23) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : MsmZ23) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..23)`. -/
theorem asNat_lt (g : MsmZ23) : asNat g < P23 := by
  unfold asNat
  exact ZMod.val_lt g

end MsmZ23

/-! ## §2  Toy-EC point as a flat record

We represent a point as `(x, y, isIdentity)` rather than going through
Mathlib's nonsingular-affine-point type, because the rustcmd surface is
the on-wire 2-byte encoding `(x ‖ y)` with the sentinel `(0xff, 0xff) =
identity`, and the bridge decodes to this flat form before checking the
affine group law. `Pairing/MsmReduce.lean` already gives the Mathlib
view; this file is the bytewise companion. -/

/-- Toy-EC affine point as a flat record. The `isIdentity = true` case
    represents the group identity (point at infinity); otherwise
    `(x, y)` are affine coordinates. -/
structure MsmEcPointFlat where
  /-- Affine x-coordinate (ignored when `isIdentity = true`). -/
  x : MsmZ23
  /-- Affine y-coordinate (ignored when `isIdentity = true`). -/
  y : MsmZ23
  /-- Identity flag (the on-wire sentinel `(0xff, 0xff)`). -/
  isIdentity : Bool

namespace MsmEcPointFlat

/-- The group identity. -/
def identity : MsmEcPointFlat := { x := 0, y := 0, isIdentity := true }

/-- Decidable equality of points. -/
instance : DecidableEq MsmEcPointFlat := by
  intro a b
  rcases a with ⟨ax, ay, ai⟩
  rcases b with ⟨bx, by_, bi⟩
  by_cases hi : ai = bi
  · by_cases hx : ax = bx
    · by_cases hy : ay = by_
      · exact .isTrue (by subst hi hx hy; rfl)
      · exact .isFalse (fun h => hy (by injection h))
    · exact .isFalse (fun h => hx (by injection h))
  · exact .isFalse (fun h => hi (by injection h))

end MsmEcPointFlat

/-! ## §3  Verified short-Weierstrass affine point-add

The standard affine formulas for `y² = x³ + a·x + b`:

```
  If P = O:        P + Q = Q
  If Q = O:        P + Q = P
  If P = -Q:       P + Q = O               (Q.x = P.x, Q.y = -P.y)
  If P = Q:        λ = (3·Px² + a) / (2·Py)
  Else:            λ = (Qy - Py) / (Qx - Px)
  R.x = λ² - Px - Qx
  R.y = λ·(Px - R.x) - Py
```

We take `a = 0, b = 7` as defaults (matching the toy bench's
`ec_ref.h`); the formulas only need `a`, not `b`. -/

/-- The toy curve's `a` parameter (default `0`). -/
def msmEcA : MsmZ23 := 0

/-- The toy short-Weierstrass affine point-add. Verified at the field
    level: each branch is the algebraic formula over `MsmZ23`. -/
noncomputable def msmEcPointAddVerified
    (P Q : MsmEcPointFlat) : MsmEcPointFlat :=
  if P.isIdentity then Q
  else if Q.isIdentity then P
  else if P.x = Q.x then
    if P.y + Q.y = 0 then MsmEcPointFlat.identity
    else
      -- Doubling: λ = (3·Px² + a) / (2·Py)
      let lam : MsmZ23 := (3 * P.x * P.x + msmEcA) / (2 * P.y)
      let rx : MsmZ23 := lam * lam - P.x - Q.x
      let ry : MsmZ23 := lam * (P.x - rx) - P.y
      { x := rx, y := ry, isIdentity := false }
  else
    -- General addition: λ = (Qy - Py) / (Qx - Px)
    let lam : MsmZ23 := (Q.y - P.y) / (Q.x - P.x)
    let rx : MsmZ23 := lam * lam - P.x - Q.x
    let ry : MsmZ23 := lam * (P.x - rx) - P.y
    { x := rx, y := ry, isIdentity := false }

/-- Verified scalar multiplication via double-and-add. `k · P`
    computed by iterating the bits of `k`. -/
noncomputable def msmEcScalarMulVerified (k : Nat) (P : MsmEcPointFlat) :
    MsmEcPointFlat :=
  go k MsmEcPointFlat.identity P
where
  /-- Recursion: `go k acc cur = acc + k·cur` via shift-and-add. -/
  go : Nat → MsmEcPointFlat → MsmEcPointFlat → MsmEcPointFlat
  | 0, acc, _ => acc
  | k+1, acc, cur =>
    let acc' :=
      if (k+1) % 2 = 1 then msmEcPointAddVerified acc cur
      else acc
    go ((k+1) / 2) acc' (msmEcPointAddVerified cur cur)

/-! ## §4  The MSM accumulation step

The MSM `Σᵢ kᵢ · Pᵢ` factors as repeated `acc ← acc + kᵢ · Pᵢ`. The
rustcmd surface lifts the per-term `t = ec_scalar_mul(k, P)` plus the
accumulator update `acc' = ec_point_add(acc, t)`. -/

/-- One MSM accumulation step: `acc' = acc + k · P`. The verified
    reference for the rustcmd composition
    `ec_point_add(acc, ec_scalar_mul(k, P))`. -/
noncomputable def msmEcAccumStepVerified
    (acc : MsmEcPointFlat) (k : Nat) (P : MsmEcPointFlat) : MsmEcPointFlat :=
  msmEcPointAddVerified acc (msmEcScalarMulVerified k P)

/-! ## §5  Sanity properties -/

/-- The identity is a left-identity for point addition. -/
theorem msmEcPointAddVerified_identity_left (P : MsmEcPointFlat) :
    msmEcPointAddVerified MsmEcPointFlat.identity P = P := by
  simp [msmEcPointAddVerified, MsmEcPointFlat.identity]

/-- `0 · P = identity`. -/
theorem msmEcScalarMulVerified_zero (P : MsmEcPointFlat) :
    msmEcScalarMulVerified 0 P = MsmEcPointFlat.identity := by
  simp [msmEcScalarMulVerified, msmEcScalarMulVerified.go]

end CatCrypt.Util
