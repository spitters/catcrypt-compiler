/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTTypes
public import CompPoly.Univariate.NTT.FastMul

/-!
# Polynomial encodings and the NTT poly-mul leaf agreement

`PolyEncoding (q n : Nat) R` converts between the concrete
`RustVal (.TPolyMod q n)` byte representation and an abstract `CPolynomial R`
over a field `R`. `polyMul_leaf_agreement` states that, under `Domain.fits`, the
encoded `fastMulImpl` product equals the encoded canonical product;
`polyMul_leaf_agreement_decoded` states the same equality before encoding. Both
are one-step transports through `CompPoly.CPolynomial.NTT.fastMulImpl_eq_mul`.

The module depends on CompPoly and on `LowCTTypes` (for `RustVal`) only.

## Main results

* `polyMul_leaf_agreement`: under `Domain.fits`, the encoded `fastMulImpl` product is
  the encoded canonical product.
* `polyMul_leaf_agreement_decoded`: the same equality before encoding.
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

/-- **Core theorem**: under `Domain.fits`, the encoded NTT-backed product
    equals the encoded canonical product.

    This is the key algebraic fact for the NTT poly-mul
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

end CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul
