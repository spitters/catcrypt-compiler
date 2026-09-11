/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public meta import CatCrypt.Crypto.Util.P25519PrimeCert
public import CatCrypt.Crypto.Util.P25519PrimeCert
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring

/-!
# Verified Curve25519 inner kernels over `ZMod (2^255 - 19)`

This file provides the *verified reference computation* layer for the
X25519 hax ↔ rustcmd bridge, mirroring the role of
`MAYO/MqEvalVerified.lean` (over `Gf16`), `UOV/EvalMqVerified.lean`
(over `Gf256`), and `Falcon512Verified.lean` (over `ZMod 12289`).

X25519 (RFC 7748) operates over the prime field

```
   Fp25519 = ℤ / (2^255 − 19) ℤ
```

`p = 2^255 − 19` is prime (Curve25519 design constant). `p25519_prime :
Nat.Prime (2^255 - 19)` is discharged by a recursive Lucas/Pratt certificate
(`P25519PrimeCert.p25519lit_prime`): its Fermat and witness checks are kernel
`decide` over fast modular exponentiation, so the proof carries no
`native_decide` reduction axiom.

The bridge claim does not depend on the modulus being prime: it is
operational (the leaf computes the algebraic formula on the bijected inputs),
the field structure is only needed to state the formula, and the rustcmd's
leaf-axiom side never invokes inversion (Montgomery-ladder steps use only
+, −, ×).

## API

* `Fp25519` : `ZMod (2^255 - 19)` — the Curve25519 prime field
* `Fp25519.asNat`, `Fp25519.fromNat` — `ZMod ↔ Nat` encoders
* `Fp25519.fromInt_asInt` — proved encoder round-trip
* `X25519State` : the (X₂, Z₂, X₃, Z₃) algebraic accumulator
* `x25519CSwap` : conditional swap of `(X₂, Z₂)` and `(X₃, Z₃)`
* `x25519DoubleAndAdd` : RFC 7748 §5 double-and-add step
* `x25519LadderStepVerified` : one Montgomery-ladder iteration over Fp25519
  — the verified reference for the opaque rustcmd leaf
  `x25519_ladder_iter`

The bridge file (`X25519/X25519HaxLowCTBridge.lean`) reduces the
rustcmd leaf claim to an identity at this verified-spec level.

## Reference

* RFC 7748: Elliptic Curves for Security, §5 (X25519, Montgomery ladder)
* RFC 7748 §5.2: KAT vectors for X25519 with the Curve25519 base point
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-! ## §1  The Curve25519 modulus and field

`p = 2^255 − 19` is a 256-bit prime, discharged via the Lucas/Pratt
certificate `P25519PrimeCert.p25519lit_prime` (kernel `decide`) and carried
through a `Fact (Nat.Prime _)` instance — see the file header. -/

/-- The Curve25519 modulus `p = 2^255 − 19`. -/
abbrev P25519 : Nat := 2^255 - 19

/-- Concrete value of `p` (the standard Curve25519 prime). -/
example : P25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
  decide

/-- `Nat.Prime p` for `p = 2^255 − 19`, discharged via the Lucas/Pratt
    certificate `P25519PrimeCert.p25519lit_prime` (kernel `decide`); the
    `Fact` instance below carries it through Mathlib's `ZMod`-as-field
    machinery. -/
theorem p25519_prime : Nat.Prime P25519 :=
  CatCrypt.Crypto.Util.P25519PrimeCert.p25519lit_prime

/-- Wrap primality as a `Fact` so `Field (ZMod P25519)` is inferred
    automatically by Mathlib. -/
instance fact_prime_p25519 : Fact (Nat.Prime P25519) := ⟨p25519_prime⟩

/-- The Curve25519 prime field. An `abbrev` so the `ZMod` field/ring
    structure flows through transparently. -/
abbrev Fp25519 : Type := ZMod P25519

namespace Fp25519

/-! ## §2  Field structure (inherited from `Mathlib.Data.ZMod.Basic`) -/

example : Field Fp25519 := inferInstance
example : CommRing Fp25519 := inferInstance

/-! ## §3  Encoders to/from Nat, Int -/

/-- Inject a `Nat` (mod `p`) into `Fp25519`. -/
def fromNat (n : Nat) : Fp25519 := (n : ZMod P25519)

/-- Project an `Fp25519` element to a `Nat` in `[0..p)` via Mathlib's
    canonical `ZMod.val`. -/
def asNat (g : Fp25519) : Nat := ZMod.val g

/-- Project an `Fp25519` element to an `Int`. -/
def asInt (g : Fp25519) : Int := (ZMod.val g : Int)

/-- Inject an `Int` into `Fp25519` (Mathlib's canonical coercion). -/
def fromInt (i : Int) : Fp25519 := (i : ZMod P25519)

/-- Round-trip on the `Nat` encoder. -/
theorem fromNat_asNat (g : Fp25519) : fromNat (asNat g) = g := by
  unfold fromNat asNat
  exact ZMod.natCast_zmod_val g

/-- Round-trip on the `Int` encoder. -/
theorem fromInt_asInt (g : Fp25519) : fromInt (asInt g) = g := by
  unfold fromInt asInt
  push_cast
  exact ZMod.natCast_zmod_val g

/-- `asNat` lands in `[0..p)`. -/
theorem asNat_lt (g : Fp25519) : asNat g < P25519 := by
  unfold asNat
  exact ZMod.val_lt g

end Fp25519

/-! ## §4  X25519 Montgomery-ladder accumulator

RFC 7748 §5 carries four field elements (X₂, Z₂, X₃, Z₃) — the
projective Montgomery coordinates of the running accumulator pair — plus
the (scalar bit, base x-coordinate) parameters that the per-iteration
body consults. The opaque rustcmd surface (`X25519LadderState`,
`TBytes 192` = 24 × u64-limb bundle) packs all six 32-byte field
elements `[x2 | z2 | x3 | z3 | scalar | base]`; the algebraic
accumulator below is the field-element decomposition of the same
state. -/

/-- The X25519 ladder accumulator (algebraic form): the four Montgomery
    coordinates `(X₂, Z₂, X₃, Z₃)`, the current scalar (an integer in
    `[0, 2^255)` — the byte-encoded clamped scalar), and the base point
    x-coordinate (an `Fp25519` element). -/
structure X25519State where
  /-- Doubled-point X coordinate. -/
  x2 : Fp25519
  /-- Doubled-point Z coordinate. -/
  z2 : Fp25519
  /-- Differential-add X coordinate. -/
  x3 : Fp25519
  /-- Differential-add Z coordinate. -/
  z3 : Fp25519
  /-- The 256-bit clamped scalar (RFC 7748 §5: low 3 bits cleared, bit
      254 set). Stored as a `Nat`. -/
  scalar : Nat
  /-- The base point x-coordinate. -/
  baseX : Fp25519

namespace X25519State

/-- Initial ladder state per RFC 7748 §5: `x2 = 1, z2 = 0, x3 = u, z3 = 1`. -/
def init (scalar : Nat) (baseX : Fp25519) : X25519State :=
  { x2 := 1, z2 := 0, x3 := baseX, z3 := 1, scalar := scalar, baseX := baseX }

end X25519State

/-! ## §5  Ladder primitives

The RFC 7748 §5 ladder step computes:

```
  K1 = (X3 - Z3) * (X2 + Z2)
  K2 = (X3 + Z3) * (X2 - Z2)
  X3' = (K1 + K2)^2
  Z3' = u * (K1 - K2)^2
  X2' = ((X2 + Z2)^2) * ((X2 - Z2)^2)
  Z2' = ((X2 + Z2)^2 - (X2 - Z2)^2) *
        (((X2 + Z2)^2 - (X2 - Z2)^2) * a24 + (X2 + Z2)^2)
```

with `a24 = 121665` (Curve25519's `(A-2)/4` constant where `A = 486662`).
The `cswap` step interchanges `(X2, Z2) ↔ (X3, Z3)` based on the current
scalar bit. -/

/-- The Curve25519 ladder constant `a24 = (A − 2) / 4` where the curve
    is `y² = x³ + A·x² + x` with `A = 486662`. -/
def x25519A24 : Fp25519 := (121665 : Nat)

/-- Conditional swap of the two Montgomery coordinate pairs.
    If `bit = true`, swap `(X2, Z2)` and `(X3, Z3)`; else leave as-is.
    Implemented as a branchless conditional in the rustcmd; here we use
    `if … then … else …` since we don't model timing. -/
def x25519CSwap (bit : Bool) (s : X25519State) : X25519State :=
  if bit then
    { s with x2 := s.x3, z2 := s.z3, x3 := s.x2, z3 := s.z2 }
  else
    s

/-- RFC 7748 §5 double-and-add. Computes the next `(X2, Z2, X3, Z3)`
    from the current state, *without* the cswap. -/
def x25519DoubleAndAdd (s : X25519State) : X25519State :=
  let A := s.x2 + s.z2
  let AA := A * A
  let B := s.x2 - s.z2
  let BB := B * B
  let E := AA - BB
  let C := s.x3 + s.z3
  let D := s.x3 - s.z3
  let DA := D * A
  let CB := C * B
  let x3' := (DA + CB) * (DA + CB)
  let z3' := s.baseX * ((DA - CB) * (DA - CB))
  let x2' := AA * BB
  let z2' := E * (AA + x25519A24 * E)
  { s with x2 := x2', z2 := z2', x3 := x3', z3 := z3' }

/-- Extract the bit at position `i` (LSB indexing) from the clamped
    scalar. -/
def x25519ScalarBit (s : X25519State) (i : Nat) : Bool :=
  (s.scalar / (2^i)) % 2 = 1

/-- **One iteration of the Curve25519 Montgomery ladder.** RFC 7748 §5:
    `cswap` based on the current bit, then `double-and-add`, then
    `cswap` again to canonicalize. The `i`-th step of the 255-iteration
    ladder. This is the **verified reference** for the opaque rustcmd
    leaf `x25519_ladder_iter`. -/
def x25519LadderStepVerified (i : Nat) (s : X25519State) : X25519State :=
  let bit := x25519ScalarBit s i
  let s' := x25519CSwap bit s
  let s'' := x25519DoubleAndAdd s'
  x25519CSwap bit s''

/-! ## §6  Sanity properties

These structural identities are not required by the bridge layer
(which reduces to the cross-side leaf identity, not aggregates), but
they document the API. -/

/-- A double-swap with the same bit is the identity. -/
theorem x25519CSwap_involutive (bit : Bool) (s : X25519State) :
    x25519CSwap bit (x25519CSwap bit s) = s := by
  cases bit <;> simp [x25519CSwap]

/-- The cswap on `bit = false` is a no-op. -/
theorem x25519CSwap_false (s : X25519State) :
    x25519CSwap false s = s := by
  simp [x25519CSwap]

/-! ## §7  The Ed25519 twisted-Edwards group law (affine)

Ed25519 (RFC 8032 §5.1) is the twisted-Edwards curve

```
   −x² + y² = 1 + d·x²·y²,   d = −121665/121666,   a = −1
```

over the **same** prime field `Fp25519 = ZMod (2^255 − 19)` the X25519
Montgomery ladder uses. The affine complete addition law for two points
`P = (x₁, y₁)`, `Q = (x₂, y₂)` is (RFC 8032 §5.1.4, with `a = −1`):

```
   x₃ = (x₁·y₂ + y₁·x₂) / (1 + d·x₁·x₂·y₁·y₂)
   y₃ = (y₁·y₂ + x₁·x₂) / (1 − d·x₁·x₂·y₁·y₂)
```

The two coordinate numerators and the two denominators are **polynomial** in
the inputs (built only from `Fp25519`'s `*`/`+`/`−`); the two field inverses
are the only non-polynomial step. This is the verified reference the emitted
Ed25519 point-add (`EdDSA/Ed25519GroupEmit.lean`, a composition over the
verified `feMul/feAdd/feSub` field leaves + the AUCurves field inverse)
must realize — the twisted-Edwards analogue of `p256AffineAdd`. -/

/-- The Ed25519 twisted-Edwards curve constant `d = −121665/121666`
    (RFC 8032 §5.1). Stored as the canonical residue. -/
def ed25519D : Fp25519 :=
  (37095705934669439343138083508754565189542113879843219016388785533085940283555 : Nat)

/-- A point on the Ed25519 curve in affine coordinates `(x, y)` over
    `Fp25519`. -/
structure Ed25519Point where
  /-- Affine `x`-coordinate. -/
  x : Fp25519
  /-- Affine `y`-coordinate. -/
  y : Fp25519

/-- The Ed25519 affine point-add `x`-numerator: `x₁·y₂ + y₁·x₂`. -/
def ed25519AddXNum (x1 y1 x2 y2 : Fp25519) : Fp25519 := x1 * y2 + y1 * x2

/-- The Ed25519 affine point-add `y`-numerator: `y₁·y₂ + x₁·x₂` (using
    `a = −1`, so `y₁·y₂ − a·x₁·x₂ = y₁·y₂ + x₁·x₂`). -/
def ed25519AddYNum (x1 y1 x2 y2 : Fp25519) : Fp25519 := y1 * y2 + x1 * x2

/-- The common product `t = d·x₁·x₂·y₁·y₂`; the two denominators are
    `1 ± t`. -/
def ed25519AddT (x1 y1 x2 y2 : Fp25519) : Fp25519 :=
  ed25519D * x1 * x2 * y1 * y2

/-- The Ed25519 affine point-add `x`-coordinate map:
    `x₃ = (x₁·y₂ + y₁·x₂) · (1 + t)⁻¹` where `t = d·x₁·x₂·y₁·y₂`. -/
def ed25519AffineRx (x1 y1 x2 y2 : Fp25519) : Fp25519 :=
  ed25519AddXNum x1 y1 x2 y2 * (1 + ed25519AddT x1 y1 x2 y2)⁻¹

/-- The Ed25519 affine point-add `y`-coordinate map:
    `y₃ = (y₁·y₂ + x₁·x₂) · (1 − t)⁻¹` where `t = d·x₁·x₂·y₁·y₂`. -/
def ed25519AffineRy (x1 y1 x2 y2 : Fp25519) : Fp25519 :=
  ed25519AddYNum x1 y1 x2 y2 * (1 - ed25519AddT x1 y1 x2 y2)⁻¹

/-- The full Ed25519 affine point-add (complete addition law, `a = −1`). -/
def ed25519AffineAdd (P Q : Ed25519Point) : Ed25519Point :=
  { x := ed25519AffineRx P.x P.y Q.x Q.y,
    y := ed25519AffineRy P.x P.y Q.x Q.y }

/-- Adding the neutral element `(0, 1)` on the right is the identity on the
    `y`-coordinate's numerator (sanity check on the formula direction). -/
theorem ed25519AddYNum_neutral_right (x1 y1 : Fp25519) :
    ed25519AddYNum x1 y1 0 1 = y1 := by
  simp [ed25519AddYNum]

/-! ## §8  Ed25519 point-doubling and the scalar-mul double-and-add ladder

The twisted-Edwards complete addition law is **unified**: doubling `[2]P` is
just `P + P`. So the doubling formula is `ed25519AffineAdd P P`, with the
*same* numerators / `1 ± t` denominators evaluated at `x₁ = x₂ = x`,
`y₁ = y₂ = y`:

```
   t   = d·x²·y²
   x₃  = 2·x·y / (1 + t)        (= ed25519AffineRx x y x y)
   y₃  = (y² + x²) / (1 − t)    (= ed25519AffineRy x y x y)
```

No separate tangent-slope chain is needed (unlike short-Weierstrass): the
emitted field-leaf doubling `Ed25519GroupEmit.emittedEdwardsDouble` is the
add Coms instantiated at `P = Q`. The scalar-mul ladder then folds the
double-and-conditional-add step over the scalar bits — the abstract `[k]·B`
reference the emitted bounded loop realizes. -/

/-- Ed25519 point doubling: `[2]P = P + P` under the unified addition law. -/
def ed25519Double (P : Ed25519Point) : Ed25519Point := ed25519AffineAdd P P

/-- One double-and-add ladder step on the accumulator/base pair, for a given
    scalar bit: double the accumulator, then conditionally add the base (under
    the unified addition law). The base is carried unchanged. -/
def ed25519ScalarStep (bit : Bool) (st : Ed25519Point × Ed25519Point) :
    Ed25519Point × Ed25519Point :=
  let acc := ed25519Double st.1
  (if bit then ed25519AffineAdd acc st.2 else acc, st.2)

/-- The double-and-add ladder: fold `ed25519ScalarStep` over the scalar bits
    (MSB→LSB). The abstract `[k]·B` reference the emitted bounded loop
    realizes. -/
def ed25519ScalarMul (bits : List Bool) (st : Ed25519Point × Ed25519Point) :
    Ed25519Point × Ed25519Point :=
  bits.foldl (fun acc b => ed25519ScalarStep b acc) st

end CatCrypt.Util
