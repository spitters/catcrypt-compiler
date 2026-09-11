/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul
public import CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul_CompPoly
public import CompPoly.Univariate.NTT.FastMul

/-!
# Pass 3.1 — CompPoly algebraic discharge (Stage F)

This file makes the CompPoly link in
`NTTPolyMul_CompPoly.lean` **load-bearing**: it imports
`CompPoly.Univariate.NTT.FastMul` and exposes a theorem that converts the
algebraic identity `fastMulImpl D p q = p * q` (under `Domain.fits`) into a
concrete `RustVal`-level equality of two encoded products.

## What this file provides

* `PolyEncoding (q n : Nat)` — a structure that encodes/decodes between
  the concrete `RustVal (.TPolyMod q n)` byte representation and an
  abstract `CPolynomial (ZMod q)`.  The encoding is the user's choice
  (little-endian byte packing, Montgomery domain, NTT-domain, …); only the
  *round-trip* properties matter at this level.
* `polyMul_leaf_agreement` — the core algebraic theorem.  Given a `Domain`
  parameter `D : Domain (ZMod q)`, an encoding, and `Domain.fits` on the
  decoded operands, the encoded `fastMulImpl` result equals the encoded
  canonical product.  This is the load-bearing fact: a one-line transport
  through `CompPoly.NTT.fastMulImpl_eq_mul`.

## What this file does **not** provide

* A full `LeafSpec` constructor that satisfies `nttAgreesPolyMul`
  out-of-the-box.  Building one requires dependent-type plumbing
  (matching on `dt = .TPolyMod q n` inside `LeafSpec.call` with the
  appropriate `cast`/`Eq.mpr`) and a decision on how the byte
  representation maps to coefficients — both are protocol-specific.
* A concrete `PolyEncoding 3329 256` for ML-KEM-768 (or
  `PolyEncoding 8380417 256` for ML-DSA-65).  Those are byte-layout
  decisions belonging to the protocol bridge, not the framework.

## Composing with `nttAgreesPolyMul_of_pointwise`

A protocol bridge that wants to discharge `nttAgreesPolyMul leafSpec q n`
for its concrete `LeafSpec` follows this pattern:

1. Define `enc : PolyEncoding q n` matching the bridge's byte layout.
2. Choose `D : Domain (ZMod q)` with `D.n ≥ 2 * n` (large enough for the
   convolution of two degree-`< n` polynomials), where `[Fact (Nat.Prime q)]`
   gives the `Field (ZMod q)` instance.
3. Build the LeafSpec so that the NTT-named leaf computes
   `enc.encode (fastMulImpl D (enc.decode a) (enc.decode b))` and the
   `"poly_mul"` / `"polymul"` leaves compute
   `enc.encode (enc.decode a * enc.decode b)` (shape-matched cases),
   and all three names agree elsewhere.
4. Use `polyMul_leaf_agreement` to discharge the shape-matched-cases
   pointwise equality.
5. Feed the resulting pointwise hypotheses into
   `nttAgreesPolyMul_of_pointwise`.

The negacyclic concern (ML-KEM/ML-DSA work mod `X^n + 1`, not `X^N - 1`
which CompPoly's cyclic `Domain` provides) is handled at step (3) by
choosing `D` of size `2 * n` and folding the high half of the cyclic
product into the low half via the negacyclic relation `X^n ≡ -1`.  The
encoding-side handles this; CompPoly delivers the cyclic product.

## Algebraic content

`CompPoly.CPolynomial.NTT.fastMulImpl_eq_mul` says: under
`Domain.fits D p.val q.val`, the NTT-backed implementation
`fastMulImpl D p q` equals canonical polynomial multiplication
`p * q : CPolynomial R`.  That's the entire algebraic content; everything
else here is plumbing.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul

open CompPoly.CPolynomial.NTT (Domain)
open CompPoly.CPolynomial.NTT.FastMul (fastMulImpl fastMulImpl_eq_mul)
open CompPoly (CPolynomial)
open CatCrypt.Crypto.Jasmin.LowCT (TowerType RustVal)

/-! ## §1  Polynomial encoding

A `PolyEncoding (q n : Nat)` specifies how to convert between concrete
`RustVal (.TPolyMod q n)` byte arrays and abstract `CPolynomial (ZMod q)`
values.

The structure carries `encode` / `decode` functions; consumers may add
round-trip properties (`decode_encode`, `encode_decode`) as needed for
their bridge.  The framework's algebraic theorem
(`polyMul_leaf_agreement`) only needs the functions to exist — round-trip
is the consumer's obligation to discharge when needed.

`[Fact (Nat.Prime q)]` is required because `Domain (ZMod q)` needs a
`Field` instance, which `ZMod q` has iff `q` is prime.  ML-KEM-768
(`q = 3329`) and ML-DSA-65 (`q = 8380417`) are both prime, so the
instance is available in those protocols. -/

/-- Encoding/decoding between `RustVal (.TPolyMod q n)` byte arrays and
    an abstract `CPolynomial R` over a field `R`.  The structure is
    intentionally minimal — only the functions in each direction — to
    leave the round-trip discipline (which direction is exact, which is
    the canonical representative) to the consumer.

    Consumers typically specialise `R := ZMod q` with `[Fact (Nat.Prime q)]`
    supplied at the use site to obtain `Field (ZMod q)`.  The framework
    keeps `R` abstract so the algebraic theorems do not commit to a
    specific coefficient type. -/
structure PolyEncoding (q n : Nat) (R : Type*) [Field R] where
  /-- Encode an abstract polynomial into a concrete byte array. -/
  encode : CPolynomial R → RustVal (.TPolyMod q n)
  /-- Decode a concrete byte array back into a polynomial. -/
  decode : RustVal (.TPolyMod q n) → CPolynomial R

/-! ## §2  Core algebraic theorem -/

/-- **Stage F core**: under `Domain.fits`, the encoded NTT-backed product
    equals the encoded canonical product.

    This is the **load-bearing** algebraic fact for the NTT poly-mul
    pass.  It is a one-step transport through
    `CompPoly.CPolynomial.NTT.fastMulImpl_eq_mul`:

    `fastMulImpl D p q = p * q`  (under `Domain.fits D p.val q.val`)

    applied to `p = enc.decode a` and `q = enc.decode b`, then `congr`'d
    through `enc.encode`. -/
theorem polyMul_leaf_agreement
    {q n : Nat} {R : Type*} [Field R] [BEq R] [LawfulBEq R]
    (D : Domain R) (enc : PolyEncoding q n R)
    (a b : RustVal (.TPolyMod q n))
    (hfits : Domain.fits D (enc.decode a).val (enc.decode b).val) :
    enc.encode (fastMulImpl D (enc.decode a) (enc.decode b)) =
      enc.encode (enc.decode a * enc.decode b) := by
  congr 1
  exact fastMulImpl_eq_mul D _ _ hfits

/-! ## §3  Decoded form

A variant stating the same agreement at the *decoded* level — useful when
the protocol bridge prefers to reason about `CPolynomial`-level products
before applying `encode` once at the end. -/

/-- Decoded variant of `polyMul_leaf_agreement`: the `fastMulImpl`-derived
    polynomial equals the canonical product polynomial, no encoding step. -/
theorem polyMul_leaf_agreement_decoded
    {q n : Nat} {R : Type*} [Field R] [BEq R] [LawfulBEq R]
    (D : Domain R) (enc : PolyEncoding q n R)
    (a b : RustVal (.TPolyMod q n))
    (hfits : Domain.fits D (enc.decode a).val (enc.decode b).val) :
    fastMulImpl D (enc.decode a) (enc.decode b) =
      enc.decode a * enc.decode b :=
  fastMulImpl_eq_mul D _ _ hfits

/-! ## §4  Composition with the plumbing bridge

Together with `nttAgreesPolyMul_of_pointwise` (from
`NTTPolyMul_CompPoly.lean`), `polyMul_leaf_agreement` gives a protocol
bridge the algebraic shape it needs.  The bridge supplies:

1. A `LeafSpec` whose recognised leaves at the PolyMod shape compute
   `enc.encode (fastMulImpl D ...)` (for the NTT name) and
   `enc.encode ((decode a) * (decode b))` (for `"poly_mul"` /
   `"polymul"`).
2. Off-shape agreement (the three names return identical values on
   non-PolyMod inputs).

The shape-matched-cases pointwise equality follows from
`polyMul_leaf_agreement`; the off-shape agreement is the consumer's
construction (typically arranged so all three names share a common
fallback path).  Both feed into `nttAgreesPolyMul_of_pointwise` to
discharge `nttAgreesPolyMul leafSpec q n`. -/

end CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul
