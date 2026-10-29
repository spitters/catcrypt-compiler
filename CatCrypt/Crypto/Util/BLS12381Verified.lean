/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public meta import CatCrypt.Crypto.Util.BLS12381PPrimeCert
public import CatCrypt.Crypto.Util.BLS12381PPrimeCert
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring
public import CatCryptCore.Tactics.GrindChar

/-!
# Verified BLS12-381 inner kernels over `ZMod p_BLS`

This file provides the *verified reference computation* layer for the
BLS12-381 `G1` base-field tie, mirroring `Util/BN254Verified.lean` and
`Util/P256Verified.lean`.

BLS12-381 (the IETF / Ethereum-2 pairing curve) has `G1` the
short-Weierstrass curve `y² = x³ + 4` over the 381-bit base-field prime

```
   Fp_BLS = ℤ / p ℤ,
   p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
     = 4002409555221667393417789825735904156556882819939007885332
         058136124031650490837864442687629129015664037894272559787.
```

`bls12381_prime : Nat.Prime p` is discharged by a recursive Lucas/Pratt
certificate (`BLS12381PPrimeCert.bls12381Plit_prime`): its Fermat and witness
checks are kernel `decide` over fast modular exponentiation, so the proof
carries no `native_decide` reduction axiom (the same route as
`p256_prime`/`bn254_prime`). `p` is the BLS12-381 base-field characteristic;
it is needed to *state* the field structure (the realization ties below use
only the `ZMod p` `CommRing` laws, which do not depend on primality).

## API

* `BLS12381` : the BLS12-381 base-field prime `p` (as a `Nat`)
* `bls12381_prime` : `Nat.Prime BLS12381` (proved via `BLS12381PPrimeCert`; the `Fact` instance
  below carries it through Mathlib's `ZMod`-as-field machinery)
* `FpBLS` : `ZMod BLS12381` — the BLS12-381 prime field
* `FpBLS.fromNat`, `FpBLS.asNat`, `FpBLS.fromInt`, `FpBLS.asInt` — encoders
* `FpBLS.fromNat_asNat`, `FpBLS.fromInt_asInt` — proved encoder round-trips
* `bls12381B` : the `G1` curve constant `b = 4`
* `BLSPoint` : an affine point `(x, y)` over `FpBLS`
* `blsAffineAdd` : the short-Weierstrass affine point-add coordinate
  formula (distinct points), over `FpBLS`, written field-agnostically —
  the verified reference the emitted field kernels must realize.

## Reference

* RFC 9380 §8.8.1 / IETF BLS12-381 ciphersuite (`G1`: `y² = x³ + 4`)
* `bls12-381-safe-rust` (AUCurves verified-bedrock2 tower, 6 limbs)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-! ## §1  The BLS12-381 modulus and field

`p = 0x1a0111ea…aaab` is a 381-bit prime, discharged via the Lucas/Pratt
certificate `BLS12381PPrimeCert.bls12381Plit_prime` (kernel `decide`) and
carried through a `Fact` instance — see the file header. -/

/-- The BLS12-381 base-field modulus `p` (the standard `0x1a0111ea…aaab`). -/
abbrev BLS12381 : Nat :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

/-- `Nat.Prime p` for the BLS12-381 base-field prime. Standard BLS12-381
    base-field characteristic; Lean's `native_decide` doesn't terminate on a
    381-bit Miller–Rabin in a reasonable time, so we take primality as a named
    axiom (the `Fact` instance below carries it through Mathlib's
    `ZMod`-as-field machinery). -/
theorem bls12381_prime : Nat.Prime BLS12381 :=
  CatCrypt.Crypto.Util.BLS12381PPrimeCert.bls12381Plit_prime

/-- Wrap primality as a `Fact` so `Field (ZMod BLS12381)` is inferred
    automatically by Mathlib. -/
instance fact_prime_bls12381 : Fact (Nat.Prime BLS12381) := ⟨bls12381_prime⟩

/-- The BLS12-381 prime field. An `abbrev` so the `ZMod` field/ring structure
    flows through transparently. -/
abbrev FpBLS : Type := ZMod BLS12381

-- grind reduces mod p in FpBLS: a literal characteristic (grind_char_numeral).
grind_char_numeral FpBLS

namespace FpBLS

/-! ## §2  Field structure (inherited from `Mathlib.Data.ZMod.Basic`) -/

example : Field FpBLS := inferInstance
example : CommRing FpBLS := inferInstance

/-! ## §3  Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod `p`) into `FpBLS`. -/
def fromNat (n : Nat) : FpBLS := (n : ZMod BLS12381)

/-- Project an `FpBLS` element to a `Nat` in `[0..p)` via Mathlib's canonical
    `ZMod.val`. -/
def asNat (g : FpBLS) : Nat := ZMod.val g

/-- Project an `FpBLS` element to an `Int`. -/
def asInt (g : FpBLS) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `FpBLS` (Mathlib's canonical coercion). -/
def fromInt (i : Int) : FpBLS := (i : ZMod BLS12381)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : FpBLS) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : FpBLS) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..p)`. -/
theorem asNat_lt (g : FpBLS) : asNat g < BLS12381 := ZMod.val_lt g

end FpBLS

/-! ## §4  The BLS12-381 `G1` curve and the affine point-add coordinate formula

`G1` is the short-Weierstrass curve `y² = x³ + a·x + b` with `a = 0` and
`b = 4`. The affine point-add of two distinct points `P = (x₁, y₁)`,
`Q = (x₂, y₂)` is

```
   λ   = (y₂ − y₁) / (x₂ − x₁)
   x₃  = λ² − x₁ − x₂
   y₃  = λ·(x₁ − x₃) − y₁
```

The two coordinate maps `x₃`, `y₃` are *polynomial* in `λ` and the inputs
(built only from `FpBLS`'s `*`/`−`); `λ` itself carries the one field
inverse. The emitted BLS12-381 `G1` group leaf computes this formula on top
of the AUCurves-verified `bls12-381-safe-rust` field ops; the realization
tie (`BLS12381/EmittedFieldRealization.lean`) shows the emitted residue
field kernels realize exactly the `*`/`−` these maps consume. -/

/-- The BLS12-381 `G1` curve constant `a = 0`. -/
def bls12381A : FpBLS := 0

/-- The BLS12-381 `G1` curve constant `b = 4` (`y² = x³ + 4`). -/
def bls12381B : FpBLS := 4

/-- An affine BLS12-381 `G1` point `(x, y)` over `FpBLS`. (We model the affine
    coordinate arithmetic; the point at infinity is handled at the group
    layer above.) -/
structure BLSPoint where
  /-- Affine `x`-coordinate. -/
  x : FpBLS
  /-- Affine `y`-coordinate. -/
  y : FpBLS

/-- The short-Weierstrass affine point-add `x`-coordinate map (distinct
    points): `x₃ = λ² − x₁ − x₂`. -/
def blsAffineRx (lam x1 x2 : FpBLS) : FpBLS := lam * lam - x1 - x2

/-- The short-Weierstrass affine point-add `y`-coordinate map (distinct
    points): `y₃ = λ·(x₁ − x₃) − y₁`. -/
def blsAffineRy (lam x1 x3 y1 : FpBLS) : FpBLS := lam * (x1 - x3) - y1

/-- The full affine point-add coordinate formula, given the precomputed
    slope `λ`. -/
def blsAffineAdd (lam : FpBLS) (P Q : BLSPoint) : BLSPoint :=
  let x3 := blsAffineRx lam P.x Q.x
  { x := x3, y := blsAffineRy lam P.x x3 P.y }

/-! ## §5  The BLS12-381 `G1` affine point-double coordinate formula

For the tangent doubling of a single affine point `P = (x, y)` on
`y² = x³ + 4` (so `a = 0`), the standard `dbl-2009-l` formula is

```
   λ   = (3·x²) / (2·y)
   x₃  = λ² − 2·x
   y₃  = λ·(x − x₃) − y
```

The slope `λ` carries the one field inverse (`(2y)⁻¹`); the coordinate maps
reuse the *same* `blsAffineRx`/`blsAffineRy` polynomial maps as the chord add
(with `x₂ = x₁ = x`).  This is the verified reference the emitted field-leaf
double kernel realizes, matching the EllipticCurve dialect's `tangentSlope`
(`(3x² + a)·(2y)⁻¹` at `a = 0`). -/

/-- The short-Weierstrass tangent slope at an affine point `(x, y)` on
    `y² = x³ + 4` (`a = 0`): `λ = (3·x²)·(2·y)⁻¹`. -/
def blsTangentSlope (x y : FpBLS) : FpBLS := (3 * (x * x)) * (2 * y)⁻¹

/-- The full affine point-double coordinate formula, given the precomputed
    tangent slope `λ`.  Reuses `blsAffineRx`/`blsAffineRy` with `x₂ = x₁ = x`. -/
def blsAffineDbl (lam : FpBLS) (P : BLSPoint) : BLSPoint :=
  let x3 := blsAffineRx lam P.x P.x
  { x := x3, y := blsAffineRy lam P.x x3 P.y }

end CatCrypt.Util
