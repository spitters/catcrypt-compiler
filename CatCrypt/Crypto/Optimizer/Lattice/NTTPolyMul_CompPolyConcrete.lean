/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul
public import CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul_CompPoly
public import CatCrypt.Crypto.Optimizer.Lattice.NTTPolyEncoding
public import CompPoly.Univariate.NTT.FastMul

/-!
# CompPoly algebraic discharge for the NTT poly-mul pass

This module makes the CompPoly link in
`NTTPolyMul_CompPoly.lean` **formal**: it re-exports, from
`NTTPolyEncoding.lean`, a theorem that converts the
algebraic identity `fastMulImpl D p q = p * q` (under `Domain.fits`) into a
concrete `RustVal`-level equality of two encoded products, and describes how a
protocol bridge composes it with `nttAgreesPolyMul_of_pointwise`.

## Declarations used (defined in `NTTPolyEncoding.lean`)

* `PolyEncoding (q n : Nat)` — a structure that encodes/decodes between
  the concrete `RustVal (.TPolyMod q n)` byte representation and an
  abstract `CPolynomial (ZMod q)`.  The encoding is the user's choice
  (little-endian byte packing, Montgomery domain, NTT-domain, …); only the
  *round-trip* properties matter at this level.
* `polyMul_leaf_agreement` — the core algebraic theorem.  Given a `Domain`
  parameter `D : Domain (ZMod q)`, an encoding, and `Domain.fits` on the
  decoded operands, the encoded `fastMulImpl` result equals the encoded
  canonical product.  This is the key fact: a one-line transport
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

/-! ## Composition with the plumbing bridge

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
