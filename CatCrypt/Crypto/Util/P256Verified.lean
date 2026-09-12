/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public meta import CatCrypt.Crypto.Util.P256PrimeCert
public import CatCrypt.Crypto.Util.P256PrimeCert
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring

/-!
# Verified NIST P-256 inner kernels over `ZMod (2^256 - 2^224 + 2^192 + 2^96 - 1)`

This file provides the *verified reference computation* layer for the
NIST P-256 (secp256r1) field tie, mirroring the role of
`Util/X25519Verified.lean` (over `ZMod (2^255 - 19)`) and
`Util/MsmToyVerified.lean` (over `ZMod 23`).

P-256 (FIPS 186-4 / TLS / EDHOC, `y² = x³ − 3·x + b`) operates over the
256-bit prime field

```
   Fp256 = ℤ / p ℤ,   p = 2^256 − 2^224 + 2^192 + 2^96 − 1.
```

`p256_prime : Nat.Prime p` is discharged by a recursive Lucas/Pratt
certificate (`P256PrimeCert.p256lit_prime`): its Fermat and witness checks
are kernel `decide` over fast modular exponentiation, so the proof carries no
`native_decide` reduction axiom. `p` is the FIPS 186-4 P-256 base-field
characteristic; it is needed to *state* the field structure (the realization
tie below uses only the `ZMod p` `CommRing` laws, which do not depend on
primality).

## API

* `P256` : the P-256 base-field prime `p` (as a `Nat`)
* `p256_prime` : `Nat.Prime P256` (proved via `P256PrimeCert`; the `Fact`
  instance below carries it through Mathlib's `ZMod`-as-field machinery)
* `Fp256` : `ZMod P256` — the P-256 prime field
* `Fp256.fromNat`, `Fp256.asNat`, `Fp256.fromInt`, `Fp256.asInt` — encoders
* `Fp256.fromNat_asNat`, `Fp256.fromInt_asInt` — proved encoder round-trips
* `p256B` : the curve constant `b`
* `P256Point` : an affine point `(x, y)` over `Fp256`
* `p256AffineAdd` : the short-Weierstrass affine point-add coordinate
  formula (distinct points), over `Fp256`, written field-agnostically —
  the verified reference the emitted field kernels must realize.

## Reference

* FIPS 186-4, Appendix D.1.2.3 (NIST P-256 domain parameters)
* SEC 2 v2, §2.4.2 (secp256r1)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-! ## §1  The P-256 modulus and field

`p = 2^256 − 2^224 + 2^192 + 2^96 − 1` is a 256-bit prime, discharged via the
Lucas/Pratt certificate `P256PrimeCert.p256lit_prime` (kernel `decide`) and
carried through a `Fact` instance — see the file header. -/

/-- The NIST P-256 base-field modulus `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`. -/
abbrev P256 : Nat := 2^256 - 2^224 + 2^192 + 2^96 - 1

/-- Concrete value of `p` (the standard FIPS 186-4 P-256 prime). -/
example :
    P256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951 := by
  decide

/-- `Nat.Prime p` for `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, discharged via
    the Lucas/Pratt certificate `P256PrimeCert.p256lit_prime` (kernel
    `decide`); the `Fact` instance below carries it through Mathlib's
    `ZMod`-as-field machinery. -/
theorem p256_prime : Nat.Prime P256 :=
  CatCrypt.Crypto.Util.P256PrimeCert.p256lit_prime

/-- Wrap primality as a `Fact` so `Field (ZMod P256)` is inferred
    automatically by Mathlib. -/
instance fact_prime_p256 : Fact (Nat.Prime P256) := ⟨p256_prime⟩

/-- The NIST P-256 prime field. An `abbrev` so the `ZMod` field/ring
    structure flows through transparently. -/
abbrev Fp256 : Type := ZMod P256

namespace Fp256

/-! ## §2  Field structure (inherited from `Mathlib.Data.ZMod.Basic`) -/

example : Field Fp256 := inferInstance
example : CommRing Fp256 := inferInstance

/-! ## §3  Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod `p`) into `Fp256`. -/
def fromNat (n : Nat) : Fp256 := (n : ZMod P256)

/-- Project an `Fp256` element to a `Nat` in `[0..p)` via Mathlib's
    canonical `ZMod.val`. -/
def asNat (g : Fp256) : Nat := ZMod.val g

/-- Project an `Fp256` element to an `Int`. -/
def asInt (g : Fp256) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `Fp256` (Mathlib's canonical coercion). -/
def fromInt (i : Int) : Fp256 := (i : ZMod P256)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : Fp256) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : Fp256) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..p)`. -/
theorem asNat_lt (g : Fp256) : asNat g < P256 := ZMod.val_lt g

end Fp256

/-! ## §4  The P-256 curve and the affine point-add coordinate formula

P-256 is the short-Weierstrass curve `y² = x³ + a·x + b` with `a = −3`
and `b` the FIPS 186-4 constant. The affine point-add of two distinct
points `P = (x₁, y₁)`, `Q = (x₂, y₂)` is

```
   λ   = (y₂ − y₁) / (x₂ − x₁)
   x₃  = λ² − x₁ − x₂
   y₃  = λ·(x₁ − x₃) − y₁
```

The two coordinate maps `x₃`, `y₃` are *polynomial* in `λ` and the inputs
(built only from `Fp256`'s `*`/`−`); `λ` itself carries the one field
inverse. The emitted P-256 group leaf computes this formula on top of the
AUCurves-verified fiat-crypto field ops; the realization tie
(`P256/EmittedFieldRealization.lean`) shows the emitted residue field
kernels realize exactly the `*`/`−` these maps consume. -/

/-- The P-256 curve constant `a = −3`. -/
def p256A : Fp256 := -3

/-- The P-256 curve constant `b` (FIPS 186-4, Appendix D.1.2.3). -/
def p256B : Fp256 :=
  (41058363725152142129326129780047268409114441015993725554835256314039467401291 : Nat)

/-- An affine P-256 point `(x, y)` over `Fp256`. (We model the affine
    coordinate arithmetic; the point at infinity is handled at the group
    layer above.) -/
structure P256Point where
  /-- Affine `x`-coordinate. -/
  x : Fp256
  /-- Affine `y`-coordinate. -/
  y : Fp256

/-- The short-Weierstrass affine point-add `x`-coordinate map (distinct
    points), as a function of the slope `λ` and the two input
    `x`-coordinates: `x₃ = λ² − x₁ − x₂`. -/
def p256AffineRx (lam x1 x2 : Fp256) : Fp256 := lam * lam - x1 - x2

/-- The short-Weierstrass affine point-add `y`-coordinate map (distinct
    points): `y₃ = λ·(x₁ − x₃) − y₁`. -/
def p256AffineRy (lam x1 x3 y1 : Fp256) : Fp256 := lam * (x1 - x3) - y1

/-- The full affine point-add coordinate formula, given the precomputed
    slope `λ`. -/
def p256AffineAdd (lam : Fp256) (P Q : P256Point) : P256Point :=
  let x3 := p256AffineRx lam P.x Q.x
  { x := x3, y := p256AffineRy lam P.x x3 P.y }

/-! ## §5  The affine point-doubling coordinate formula

The chord-tangent doubling of a point `P = (x, y)` on `y² = x³ + a·x + b`
uses the **tangent slope**

```
   λ   = (3·x² + a) / (2·y)
   x₃  = λ² − 2·x
   y₃  = λ·(x − x₃) − y
```

For P-256, `a = −3`, so the tangent-slope numerator is `3·x² − 3`. The two
coordinate maps `x₃`, `y₃` are **the same** `p256AffineRx`/`p256AffineRy`
as the distinct-point add, evaluated at `x₁ = x₂ = x` and `y₁ = y` — only
the slope differs (tangent vs. chord). This is why the emitted doubling
reuses the add's `x₃`/`y₃` field-leaf chains, prepended with a different
slope chain. -/

/-- The P-256 affine doubling **tangent-slope numerator** `3·x² + a`
    (`= 3·x² − 3` since `a = −3`), as a field-agnostic expression. -/
def p256DoubleNum (x : Fp256) : Fp256 := 3 * (x * x) + p256A

/-- The P-256 affine doubling **tangent slope** `λ = (3·x² + a) / (2·y)`. -/
def p256DoubleLam (x y : Fp256) : Fp256 := p256DoubleNum x * (2 * y)⁻¹

/-- The full affine point-doubling coordinate formula, given the precomputed
    tangent slope `λ`. Reuses the add's `x₃`/`y₃` coordinate maps at
    `x₁ = x₂ = x`, `y₁ = y`: `x₃ = λ² − 2·x`, `y₃ = λ·(x − x₃) − y`. -/
def p256AffineDouble (lam : Fp256) (P : P256Point) : P256Point :=
  let x3 := p256AffineRx lam P.x P.x
  { x := x3, y := p256AffineRy lam P.x x3 P.y }

/-! ## §6  The scalar-multiplication double-and-add ladder

Scalar multiplication `[k]·B` over the group is the left-to-right
double-and-add ladder: starting from an accumulator, each scalar bit
(MSB→LSB) **doubles** the accumulator and **conditionally adds** the base
point when the bit is set:

```
   acc ↦ double(acc) ;  if bit then acc ↦ acc + B
```

We model the accumulator-doubling slope and the chord-add slope
*field-agnostically* and define the per-bit step on `P256Point` pairs
`(acc, base)` (the base is carried unchanged). The full ladder is the
`List.foldl` of this step over the scalar-bit list — exactly the iteration
the emitted bounded loop performs. The slopes are computed from the field
coordinates (`p256DoubleLam` for the tangent, the chord slope for the add),
so the step is a pure function of the points; this is the abstract reference
the emitted field-leaf composition (double + conditional-add) must realize
through the loop. -/

/-- The chord slope `λ = (y₂ − y₁) / (x₂ − x₁)` for the distinct-point add
    (field-agnostic). -/
def p256AddLam (P Q : P256Point) : Fp256 := (Q.y - P.y) * (Q.x - P.x)⁻¹

/-- Distinct-point add with the slope computed from the two points. -/
def p256Add (P Q : P256Point) : P256Point := p256AffineAdd (p256AddLam P Q) P Q

/-- Point doubling with the tangent slope computed from the point. -/
def p256Double (P : P256Point) : P256Point :=
  p256AffineDouble (p256DoubleLam P.x P.y) P

/-- One double-and-add ladder step on the accumulator/base pair, for a given
    scalar bit: double the accumulator, then conditionally add the base. The
    base is carried unchanged. -/
def p256ScalarStep (bit : Bool) (st : P256Point × P256Point) : P256Point × P256Point :=
  let acc := p256Double st.1
  (if bit then p256Add acc st.2 else acc, st.2)

/-- The double-and-add ladder: fold `p256ScalarStep` over the scalar bits
    (MSB→LSB) from the initial accumulator/base pair. This is the abstract
    `[k]·B` reference the emitted bounded loop realizes. -/
def p256ScalarMul (bits : List Bool) (st : P256Point × P256Point) :
    P256Point × P256Point :=
  bits.foldl (fun acc b => p256ScalarStep b acc) st

end CatCrypt.Util
