/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public meta import CatCrypt.Crypto.Util.Secp256k1PPrimeCert
public import CatCrypt.Crypto.Util.Secp256k1PPrimeCert
public import Mathlib.Tactic.Ring

/-!
# Verified secp256k1 inner kernels over `ZMod (2^256 − 2^32 − 977)`

This file provides the *verified reference computation* layer for the
secp256k1 (Bitcoin / ECDSA) field tie, mirroring the role of
`Util/P256Verified.lean` (over the NIST P-256 prime) and
`Util/X25519Verified.lean` (over `ZMod (2^255 − 19)`).

secp256k1 (SEC 2 v2 §2.4.1, `y² = x³ + 7`) operates over the 256-bit prime
field

```
   FpSecp256k1 = ℤ / p ℤ,   p = 2^256 − 2^32 − 977.
```

`secp256k1_prime : Nat.Prime p` is discharged by a recursive Lucas/Pratt
certificate (`Secp256k1PPrimeCert.secp256k1Plit_prime`): its Fermat and
witness checks are kernel `decide` over fast modular exponentiation, so the
proof carries no `native_decide` reduction axiom. `p` is the secp256k1
base-field characteristic; it is needed to *state* the field structure (the
realization tie uses only the `ZMod p` `CommRing` laws, which do not depend
on primality).

## API

* `Secp256k1P` : the secp256k1 base-field prime `p`
* `secp256k1_prime` : `Nat.Prime Secp256k1P` (proved via `Secp256k1PPrimeCert`)
* `FpSecp256k1` : `ZMod Secp256k1P` — the secp256k1 prime field
* `FpSecp256k1.fromNat/asNat/fromInt/asInt` — encoders + round-trips
* `secp256k1B` : the curve constant `b = 7`
* `Secp256k1Point` : an affine point `(x, y)` over `FpSecp256k1`
* `secp256k1AffineRx`/`Ry`/`AffineAdd` : the short-Weierstrass affine
  point-add coordinate formula (distinct points), the verified reference the
  emitted field kernels must realize.

## Reference

* SEC 2 v2, §2.4.1 (secp256k1)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-! ## §1  The secp256k1 modulus and field -/

/-- The secp256k1 base-field modulus `p = 2^256 − 2^32 − 977`. -/
abbrev Secp256k1P : Nat := 2^256 - 2^32 - 977

/-- Concrete value of `p` (the standard secp256k1 prime). -/
example :
    Secp256k1P = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  decide

/-- `Nat.Prime p` for `p = 2^256 − 2^32 − 977`. Standard secp256k1
    base-field characteristic; Lean's `native_decide` doesn't terminate on a
    256-bit Miller–Rabin in a reasonable time, so we take primality as a named
    axiom (the `Fact` instance below carries it through Mathlib's
    `ZMod`-as-field machinery). -/
theorem secp256k1_prime : Nat.Prime Secp256k1P :=
  CatCrypt.Crypto.Util.Secp256k1PPrimeCert.secp256k1Plit_prime

/-- Wrap primality as a `Fact` so `Field (ZMod Secp256k1P)` is inferred
    automatically by Mathlib. -/
instance fact_prime_secp256k1 : Fact (Nat.Prime Secp256k1P) := ⟨secp256k1_prime⟩

/-- The secp256k1 prime field. An `abbrev` so the `ZMod` field/ring structure
    flows through transparently. -/
abbrev FpSecp256k1 : Type := ZMod Secp256k1P

namespace FpSecp256k1

/-! ## §2  Field structure (inherited from `Mathlib.Data.ZMod.Basic`) -/

example : Field FpSecp256k1 := inferInstance
example : CommRing FpSecp256k1 := inferInstance

/-! ## §3  Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod `p`) into `FpSecp256k1`. -/
def fromNat (n : Nat) : FpSecp256k1 := (n : ZMod Secp256k1P)

/-- Project an `FpSecp256k1` element to a `Nat` in `[0..p)`. -/
def asNat (g : FpSecp256k1) : Nat := ZMod.val g

/-- Project an `FpSecp256k1` element to an `Int`. -/
def asInt (g : FpSecp256k1) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `FpSecp256k1`. -/
def fromInt (i : Int) : FpSecp256k1 := (i : ZMod Secp256k1P)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : FpSecp256k1) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : FpSecp256k1) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..p)`. -/
theorem asNat_lt (g : FpSecp256k1) : asNat g < Secp256k1P := ZMod.val_lt g

end FpSecp256k1

/-! ## §4  The secp256k1 curve and the affine point-add coordinate formula

secp256k1 is the short-Weierstrass curve `y² = x³ + a·x + b` with `a = 0`
and `b = 7`. The affine point-add of two distinct points `P = (x₁, y₁)`,
`Q = (x₂, y₂)` is

```
   λ   = (y₂ − y₁) / (x₂ − x₁)
   x₃  = λ² − x₁ − x₂
   y₃  = λ·(x₁ − x₃) − y₁
```

identical in shape to the NIST P-256 formula (`Util/P256Verified.lean`); only
the field prime and curve constants differ. The two coordinate maps are
*polynomial* in `λ` and the inputs (built only from `FpSecp256k1`'s `*`/`−`);
`λ` carries the one field inverse. -/

/-- The secp256k1 curve constant `a = 0`. -/
def secp256k1A : FpSecp256k1 := 0

/-- The secp256k1 curve constant `b = 7`. -/
def secp256k1B : FpSecp256k1 := 7

/-- An affine secp256k1 point `(x, y)` over `FpSecp256k1`. -/
structure Secp256k1Point where
  /-- Affine `x`-coordinate. -/
  x : FpSecp256k1
  /-- Affine `y`-coordinate. -/
  y : FpSecp256k1

/-- The short-Weierstrass affine point-add `x`-coordinate map (distinct
    points): `x₃ = λ² − x₁ − x₂`. -/
def secp256k1AffineRx (lam x1 x2 : FpSecp256k1) : FpSecp256k1 := lam * lam - x1 - x2

/-- The short-Weierstrass affine point-add `y`-coordinate map (distinct
    points): `y₃ = λ·(x₁ − x₃) − y₁`. -/
def secp256k1AffineRy (lam x1 x3 y1 : FpSecp256k1) : FpSecp256k1 := lam * (x1 - x3) - y1

/-- The full affine point-add coordinate formula, given the precomputed
    slope `λ`. -/
def secp256k1AffineAdd (lam : FpSecp256k1) (P Q : Secp256k1Point) : Secp256k1Point :=
  let x3 := secp256k1AffineRx lam P.x Q.x
  { x := x3, y := secp256k1AffineRy lam P.x x3 P.y }

/-! ## §5  The point-doubling tangent slope and the doubling formula

The chord–tangent doubling of `P = (x, y)` on the short-Weierstrass curve
`y² = x³ + a·x + b` uses the **tangent slope** `λ = (3·x² + a) / (2·y)`. For
secp256k1, `a = 0`, so the numerator is `3·x²`. The doubling reuses the
*same* `x₃`/`y₃` coordinate maps as the distinct-point add, evaluated at
`x₁ = x₂ = x`, `y₁ = y`:

```
   λ   = 3·x² · (2·y)⁻¹
   x₃  = λ² − x − x        (= secp256k1AffineRx λ x x)
   y₃  = λ·(x − x₃) − y    (= secp256k1AffineRy λ x x₃ y)
```

These are the abstract references the emitted field-leaf doubling
(`Secp256k1GroupEmit.emittedDouble`) realizes. -/

/-- The secp256k1 affine doubling **tangent-slope numerator** `3·x² + a`
    (`= 3·x²` since `a = 0`). -/
def secp256k1DoubleNum (x : FpSecp256k1) : FpSecp256k1 := 3 * (x * x) + secp256k1A

/-- The secp256k1 affine doubling **tangent slope** `λ = (3·x² + a) / (2·y)`. -/
def secp256k1DoubleLam (x y : FpSecp256k1) : FpSecp256k1 :=
  secp256k1DoubleNum x * (2 * y)⁻¹

/-- The full affine point-doubling coordinate formula, given the precomputed
    tangent slope `λ`. Reuses the add's `x₃`/`y₃` coordinate maps at
    `x₁ = x₂ = x`, `y₁ = y`. -/
def secp256k1AffineDouble (lam : FpSecp256k1) (P : Secp256k1Point) : Secp256k1Point :=
  let x3 := secp256k1AffineRx lam P.x P.x
  { x := x3, y := secp256k1AffineRy lam P.x x3 P.y }

/-! ## §6  The scalar-multiplication double-and-add ladder

`[k]·B` is the left-to-right double-and-add ladder over the accumulator/base
pair `(acc, base)`: each scalar bit (MSB→LSB) doubles the accumulator and
conditionally adds the base point. The slopes are computed field-agnostically
from the coordinates, so the step is a pure function of the points — the
abstract reference the emitted field-leaf double-and-add loop must realize. -/

/-- The chord slope `λ = (y₂ − y₁) / (x₂ − x₁)` for the distinct-point add. -/
def secp256k1AddLam (P Q : Secp256k1Point) : FpSecp256k1 :=
  (Q.y - P.y) * (Q.x - P.x)⁻¹

/-- Distinct-point add with the slope computed from the two points. -/
def secp256k1Add (P Q : Secp256k1Point) : Secp256k1Point :=
  secp256k1AffineAdd (secp256k1AddLam P Q) P Q

/-- Point doubling with the tangent slope computed from the point. -/
def secp256k1Double (P : Secp256k1Point) : Secp256k1Point :=
  secp256k1AffineDouble (secp256k1DoubleLam P.x P.y) P

/-- One double-and-add ladder step on the accumulator/base pair, for a given
    scalar bit: double the accumulator, then conditionally add the base. The
    base is carried unchanged. -/
def secp256k1ScalarStep (bit : Bool) (st : Secp256k1Point × Secp256k1Point) :
    Secp256k1Point × Secp256k1Point :=
  let acc := secp256k1Double st.1
  (if bit then secp256k1Add acc st.2 else acc, st.2)

/-- The double-and-add ladder: fold `secp256k1ScalarStep` over the scalar bits
    (MSB→LSB). The abstract `[k]·B` reference the emitted bounded loop
    realizes. -/
def secp256k1ScalarMul (bits : List Bool) (st : Secp256k1Point × Secp256k1Point) :
    Secp256k1Point × Secp256k1Point :=
  bits.foldl (fun acc b => secp256k1ScalarStep b acc) st

end CatCrypt.Util
