/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public meta import CatCrypt.Crypto.Util.BN254PrimeCert
public import CatCrypt.Crypto.Util.BN254PrimeCert
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring
public import CatCryptCore.Tactics.GrindChar

/-!
# Verified BN254 (alt-bn128) inner kernels over `ZMod p_BN254`

This file provides the *verified reference computation* layer for the
BN254 `G1` base-field tie, mirroring `Util/P256Verified.lean` (over the
NIST P-256 prime) and `Util/X25519Verified.lean` (over `2^255 − 19`).

BN254 (alt-bn128, the Ethereum EIP-196/EIP-197 precompile curve) is the
short-Weierstrass curve `y² = x³ + 3` over the 254-bit base-field prime

```
   Fp_BN254 = ℤ / p ℤ,
   p = 21888242871839275222246405745257275088696311157297823662689037894645226208583.
```

`bn254_prime : Nat.Prime p` is discharged by a recursive Lucas/Pratt
certificate (`BN254PrimeCert.bn254lit_prime`): its Fermat and witness checks
are kernel `decide` over fast modular exponentiation, so the proof carries no
`native_decide` reduction axiom (the same route as
`p256_prime`/`p25519_prime`). `p` is the alt-bn128 base-field
characteristic; it is needed to *state* the field structure (the realization
ties below use only the `ZMod p` `CommRing` laws, which do not depend on
primality).

## API

* `BN254` : the BN254 base-field prime `p` (as a `Nat`)
* `bn254_prime` : `Nat.Prime BN254` (proved via `BN254PrimeCert`; the `Fact` instance below
  carries it through Mathlib's `ZMod`-as-field machinery)
* `FpBN254` : `ZMod BN254` — the BN254 prime field
* `FpBN254.fromNat`, `FpBN254.asNat`, `FpBN254.fromInt`, `FpBN254.asInt` — encoders
* `FpBN254.fromNat_asNat`, `FpBN254.fromInt_asInt` — proved encoder round-trips
* `bn254B` : the curve constant `b = 3`
* `BN254Point` : an affine point `(x, y)` over `FpBN254`
* `bn254AffineAdd` : the short-Weierstrass affine point-add coordinate
  formula (distinct points), over `FpBN254`, written field-agnostically —
  the verified reference the emitted field kernels must realize.

## Reference

* EIP-196 / EIP-197 (Ethereum `bn256Add` / `bn256Pairing` precompiles)
* `bn254-safe-rust` (AUCurves verified-bedrock2 tower, `y² = x³ + 3`,
  generator `G1 = (1, 2)`)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-! ## §1  The BN254 modulus and field

`p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`
is a 254-bit prime, discharged via the Lucas/Pratt certificate
`BN254PrimeCert.bn254lit_prime` (kernel `decide`) and carried through a `Fact`
instance — see the file header. -/

/-- The BN254 (alt-bn128) base-field modulus `p`. -/
abbrev BN254 : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- `Nat.Prime p` for the BN254 base-field prime. Standard alt-bn128
    base-field characteristic; Lean's `native_decide` doesn't terminate on a
    254-bit Miller–Rabin in a reasonable time, so we take primality as a named
    axiom (the `Fact` instance below carries it through Mathlib's
    `ZMod`-as-field machinery). -/
theorem bn254_prime : Nat.Prime BN254 :=
  CatCrypt.Crypto.Util.BN254PrimeCert.bn254lit_prime

/-- Wrap primality as a `Fact` so `Field (ZMod BN254)` is inferred
    automatically by Mathlib. -/
instance fact_prime_bn254 : Fact (Nat.Prime BN254) := ⟨bn254_prime⟩

/-- The BN254 prime field. An `abbrev` so the `ZMod` field/ring structure
    flows through transparently. -/
abbrev FpBN254 : Type := ZMod BN254

-- grind reduces mod p in FpBN254: a literal characteristic (grind_char_numeral).
grind_char_numeral FpBN254

namespace FpBN254

/-! ## §2  Field structure (inherited from `Mathlib.Data.ZMod.Basic`) -/

example : Field FpBN254 := inferInstance
example : CommRing FpBN254 := inferInstance

/-! ## §3  Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod `p`) into `FpBN254`. -/
def fromNat (n : Nat) : FpBN254 := (n : ZMod BN254)

/-- Project an `FpBN254` element to a `Nat` in `[0..p)` via Mathlib's
    canonical `ZMod.val`. -/
def asNat (g : FpBN254) : Nat := ZMod.val g

/-- Project an `FpBN254` element to an `Int`. -/
def asInt (g : FpBN254) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `FpBN254` (Mathlib's canonical coercion). -/
def fromInt (i : Int) : FpBN254 := (i : ZMod BN254)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : FpBN254) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : FpBN254) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..p)`. -/
theorem asNat_lt (g : FpBN254) : asNat g < BN254 := ZMod.val_lt g

end FpBN254

/-! ## §4  The BN254 curve and the affine point-add coordinate formula

BN254 is the short-Weierstrass curve `y² = x³ + a·x + b` with `a = 0` and
`b = 3` (standard generator `G1 = (1, 2)`). The affine point-add of two
distinct points `P = (x₁, y₁)`, `Q = (x₂, y₂)` is

```
   λ   = (y₂ − y₁) / (x₂ − x₁)
   x₃  = λ² − x₁ − x₂
   y₃  = λ·(x₁ − x₃) − y₁
```

The two coordinate maps `x₃`, `y₃` are *polynomial* in `λ` and the inputs
(built only from `FpBN254`'s `*`/`−`); `λ` itself carries the one field
inverse. The emitted BN254 `G1` group leaf computes this formula on top of
the AUCurves-verified `bn254-safe-rust` field ops. The statement that emitted
residue field kernels realize exactly the `*`/`−` these maps consume is made
per curve in the `EmittedFieldRealization` modules; BN254 has no such module. -/

/-- The BN254 curve constant `a = 0`. -/
def bn254A : FpBN254 := 0

/-- The BN254 curve constant `b = 3` (`y² = x³ + 3`). -/
def bn254B : FpBN254 := 3

/-- An affine BN254 `G1` point `(x, y)` over `FpBN254`. (We model the affine
    coordinate arithmetic; the point at infinity is handled at the group
    layer above.) -/
structure BN254Point where
  /-- Affine `x`-coordinate. -/
  x : FpBN254
  /-- Affine `y`-coordinate. -/
  y : FpBN254

/-- The short-Weierstrass affine point-add `x`-coordinate map (distinct
    points): `x₃ = λ² − x₁ − x₂`. -/
def bn254AffineRx (lam x1 x2 : FpBN254) : FpBN254 := lam * lam - x1 - x2

/-- The short-Weierstrass affine point-add `y`-coordinate map (distinct
    points): `y₃ = λ·(x₁ − x₃) − y₁`. -/
def bn254AffineRy (lam x1 x3 y1 : FpBN254) : FpBN254 := lam * (x1 - x3) - y1

/-- The full affine point-add coordinate formula, given the precomputed
    slope `λ`. -/
def bn254AffineAdd (lam : FpBN254) (P Q : BN254Point) : BN254Point :=
  let x3 := bn254AffineRx lam P.x Q.x
  { x := x3, y := bn254AffineRy lam P.x x3 P.y }

end CatCrypt.Util
