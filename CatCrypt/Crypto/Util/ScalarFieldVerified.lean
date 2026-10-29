/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import CatCrypt.Crypto.Util.VestaPrimeCert
public import CatCrypt.Crypto.Util.Ed25519LPrimeCert
public import CatCrypt.Crypto.Util.P256NPrimeCert
public import CatCrypt.Crypto.Util.Secp256k1NPrimeCert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Group
public import CatCryptCore.Tactics.GrindChar

/-!
# Verified scalar-field (`ZMod n`) references for ECDSA / EdDSA

`Util/Secp256k1Verified.lean` and `Util/P256Verified.lean` model the curve's
**base field** `ZMod p` (the field over which the affine point coordinates and
the group law live). The companion to a curve's base field is its **scalar
field** `ZMod n`, where `n` is the order of the cyclic group (the number of
points). The ECDSA / EdDSA signing and verification *scalars* — the nonce
inverse `s⁻¹`, `u₁ = z·s⁻¹`, `u₂ = r·s⁻¹`, the signature scalar
`s = k⁻¹·(z + r·d)`, and EdDSA's `S = r + H·a` — are arithmetic in `ZMod n`,
NOT in the base field.

This file is the `ZMod n` analogue of the `Util/*Verified.lean` base-field
files: it fixes the three production group orders and provides the abstract
scalar references that the emitted scalar-field-leaf compositions
(`<Curve>ScalarEmit.lean`) realize.

## The three scalar fields

| Curve      | order `n` (the group order) |
|------------|-----------------------------|
| secp256k1  | `n = 2²⁵⁶ − 432420386565659656852420866394968145599` (the SEC 2 v2 order) |
| NIST P-256 | the FIPS 186-4 P-256 order |
| Ed25519    | `L = 2²⁵² + 27742317777372353535851937790883648493` (RFC 8032 §5.1) |

All three orders are prime (the curves are chosen with prime-order groups), so
each scalar field is a `Field`, and `s⁻¹` is the field inverse — the
same algebra the emitted Montgomery-mul + Bernstein–Yang safegcd inverse
realize, only at modulus `n` instead of `p`.

## API (per curve `C`)

* `C.N`        : the group order (a `Nat`)
* `C.n_prime`  : `Nat.Prime C.N`, discharged by a Lucas certificate (the orders
                 are the standard published group orders)
* `Fn<C>`      : `ZMod C.N` — the scalar field
* `Fn<C>.fromNat/asNat` : encoders + round-trip
* the abstract ECDSA scalar references (`ecdsaU1/ecdsaU2/ecdsaSignS`) and the
  EdDSA reference (`eddsaSignS`), as pure `ZMod n` expressions.

## References

* SEC 2 v2 §2.4.1 (secp256k1 order `n`)
* FIPS 186-4 (P-256 order `n`)
* RFC 8032 §5.1 (Ed25519 order `L`)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Util

/-! ## §1  secp256k1 scalar field `ZMod n` -/

/-- The secp256k1 group order
    `n = 2²⁵⁶ − 432420386565659656852420866394968145599`
    (SEC 2 v2 §2.4.1). -/
abbrev Secp256k1N : Nat :=
  115792089237316195423570985008687907852837564279074904382605163141518161494337

/-- The published secp256k1 order is below `2²⁵⁶` (a 256-bit scalar). -/
theorem secp256k1N_lt : Secp256k1N < 2 ^ 256 := by decide

/-- `Nat.Prime n` for the secp256k1 group order (the secp256k1 group has prime
    order), discharged by the Lucas certificate
    `Secp256k1NPrimeCert.secp256k1Nlit_prime`. -/
theorem secp256k1N_prime : Nat.Prime Secp256k1N :=
  CatCrypt.Crypto.Util.Secp256k1NPrimeCert.secp256k1Nlit_prime

/-- `Fact`-wrap the order primality so `Field (ZMod Secp256k1N)` is inferred. -/
instance fact_prime_secp256k1N : Fact (Nat.Prime Secp256k1N) := ⟨secp256k1N_prime⟩

/-- The secp256k1 scalar field. -/
abbrev FnSecp256k1 : Type := ZMod Secp256k1N

-- grind reduces mod n in FnSecp256k1: a literal characteristic (grind_char_numeral).
grind_char_numeral FnSecp256k1

/-! ## §2  NIST P-256 scalar field `ZMod n` -/

/-- The NIST P-256 group order `n` (FIPS 186-4). -/
abbrev P256N : Nat :=
  115792089210356248762697446949407573529996955224135760342422259061068512044369

/-- The P-256 order is a 256-bit scalar. -/
theorem p256N_lt : P256N < 2 ^ 256 := by decide

/-- `Nat.Prime n` for the P-256 group order (FIPS 186-4 published prime order). -/
theorem p256N_prime : Nat.Prime P256N :=
  CatCrypt.Crypto.Util.P256NPrimeCert.p256Nlit_prime

/-- `Fact`-wrap the P-256 order primality. -/
instance fact_prime_p256N : Fact (Nat.Prime P256N) := ⟨p256N_prime⟩

/-- The P-256 scalar field. -/
abbrev FnP256 : Type := ZMod P256N

-- grind reduces mod n in FnP256: a literal characteristic (grind_char_numeral).
grind_char_numeral FnP256

/-! ## §3  Ed25519 scalar field `ZMod L` -/

/-- The Ed25519 group order
    `L = 2²⁵² + 27742317777372353535851937790883648493` (RFC 8032 §5.1). -/
abbrev Ed25519L : Nat :=
  7237005577332262213973186563042994240857116359379907606001950938285454250989

/-- `L = 2²⁵² + 27742317777372353535851937790883648493`. -/
theorem ed25519L_eq : Ed25519L = 2 ^ 252 + 27742317777372353535851937790883648493 := by
  decide

/-- `Nat.Prime L` for the Ed25519 group order (RFC 8032 published prime order). -/
theorem ed25519L_prime : Nat.Prime Ed25519L :=
  CatCrypt.Crypto.Util.Ed25519LPrimeCert.ed25519Llit_prime

/-- `Fact`-wrap the Ed25519 order primality. -/
instance fact_prime_ed25519L : Fact (Nat.Prime Ed25519L) := ⟨ed25519L_prime⟩

/-- The Ed25519 scalar field. -/
abbrev FnEd25519 : Type := ZMod Ed25519L

-- grind reduces mod n in FnEd25519: a literal characteristic (grind_char_numeral).
grind_char_numeral FnEd25519

/-! ## §3b  Pasta Pallas scalar field `ZMod n` (the Pasta-cycle order)

The Pasta cycle (Hopwood, 2020) is a pair of curves Pallas / Vesta whose orders
interlock: `|E_Pallas| = q_Vesta` and `|E_Vesta| = q_Pallas`, both prime. So the
**Pallas group order is exactly the Vesta base-field prime**
`vestaQ = 2²⁵⁴ + 45560315531506369815346746415080538113`
(`RelationalFrontVesta.vestaQ`). There is no separate constant to introduce —
the Pallas scalar field `ZMod n` *is* `ZMod vestaQ`, and the published Pasta
primality of `vestaQ` is the published primality of the Pallas order. -/

/-- The Pasta Pallas group order `n = |E_Pallas| = q_Vesta`, the Vesta base-field
    prime (Hopwood, 2020). The Pasta cycle makes the Pallas order coincide with
    the Vesta base prime, so this is the same `Nat` literal as
    `RelationalFrontVesta.vestaQ`. -/
abbrev PallasN : Nat :=
  0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

/-- The Pallas order is below `2²⁵⁵`. -/
theorem pallasN_lt : PallasN < 2 ^ 255 := by decide

/-- `Nat.Prime n` for the Pasta Pallas group order. By the Pasta cycle this is
    the Vesta base-field prime `vestaQ` (Hopwood, "The Pasta Curves for Halo 2 and
    Beyond", 2020), discharged by the Lucas certificate
    `VestaPrimeCert.vestalit_prime`. -/
theorem pallasN_prime : Nat.Prime PallasN :=
  CatCrypt.Crypto.Util.VestaPrimeCert.vestalit_prime

/-- `Fact`-wrap the Pallas order primality so `Field (ZMod PallasN)` is inferred. -/
instance fact_prime_pallasN : Fact (Nat.Prime PallasN) := ⟨pallasN_prime⟩

/-- The Pasta Pallas scalar field. -/
abbrev FnPallas : Type := ZMod PallasN

-- grind reduces mod n in FnPallas: a literal characteristic (grind_char_numeral).
grind_char_numeral FnPallas

/-! ## §4  Generic scalar-field encoders + the ECDSA / EdDSA references

The scalar references are *uniform* across the curves — they are the same
`ZMod n` expressions, only the modulus differs. We state them generically over
any `[Field K]` so they instantiate at every scalar field, then record the
concrete ECDSA / EdDSA wirings each emit module ties its composition to. -/

section Generic

variable {K : Type*} [Field K]

/-- The ECDSA verifier scalar `u₁ = z·s⁻¹ mod n`. -/
def ecdsaU1 (z s : K) : K := z * s⁻¹

/-- The ECDSA verifier scalar `u₂ = r·s⁻¹ mod n`. -/
def ecdsaU2 (r s : K) : K := r * s⁻¹

/-- The ECDSA signing scalar `s = k⁻¹·(z + r·d) mod n` (the value the signer
    emits; the nonce-inverse `k⁻¹` is the owned constant-time safegcd inverse). -/
def ecdsaSignS (k z r d : K) : K := k⁻¹ * (z + r * d)

/-- The EdDSA signing scalar `S = r + H·a mod L` (RFC 8032 §5.1.6). Here `r` is
    the per-message nonce reduced mod `L`, `H` is the challenge hash reduced mod
    `L`, and `a` is the clamped secret scalar. No inverse — a single
    multiply-add in `ZMod L`. -/
def eddsaSignS (r h a : K) : K := r + h * a

/-- The signing scalar is the multiplicative inverse of the recomputed verify
    scalar in the obvious sense: `u₁ = z·s⁻¹` and `u₂ = r·s⁻¹` share the single
    inverse `s⁻¹`, so computing `s⁻¹` once (the owned safegcd inverse) and two
    multiplies (owned Montgomery mul) yields both. -/
theorem ecdsaU_shared_inverse (z r s : K) :
    ecdsaU1 z s = z * s⁻¹ ∧ ecdsaU2 r s = r * s⁻¹ := ⟨rfl, rfl⟩

/-- ECDSA sign/verify consistency at the scalar level: if `s = k⁻¹·(z + r·d)`
    with `s ≠ 0` and `k ≠ 0`, then `u₁ + u₂·d = k` — the identity the
    verification equation `u₁·G + u₂·Q = k·G = R` rests on (`Q = d·G`). This is
    the purely-scalar core of ECDSA soundness, all in the owned scalar field. -/
theorem ecdsa_sign_verify_scalar_consistency (k z r d : K)
    (hk : k ≠ 0) (hs : z + r * d ≠ 0) :
    ecdsaU1 z (ecdsaSignS k z r d) + ecdsaU2 r (ecdsaSignS k z r d) * d = k := by
  unfold ecdsaU1 ecdsaU2 ecdsaSignS
  have hkinv : k⁻¹ ≠ 0 := inv_ne_zero hk
  field_simp

end Generic

end CatCrypt.Util
