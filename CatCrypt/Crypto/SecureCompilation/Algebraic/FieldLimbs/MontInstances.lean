/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont
public import CatCrypt.Crypto.Util.P384PPrimeCert
public import CatCrypt.Crypto.Util.BLS12381PPrimeCert

/-!
# Montgomery records at the 384-bit curve primes and a 4096-bit RSA modulus

`Mont.LimbParams` records, each with `nInv = -p⁻¹ mod 2^64`:

* `p384`: the NIST P-384 base prime `2^384 - 2^128 - 2^96 + 2^32 - 1`
  (`P384PPrimeCert.p384Plit`), six limbs, `nInv = 0x100000001`.
* `bls12381`: the BLS12-381 base prime (`BLS12381PPrimeCert.bls12381Plit`), six limbs,
  `nInv = 0x89f3fffcfffcfffd`.
* `rsa4096`: the modulus of the RFC 9474 Appendix A RSA test key, 64 limbs,
  `nInv = 0x056225998c4e0183`.

The two primes are the literals of their primality certificates. Every side condition,
`nInv_spec` included, is a closed statement on `ℕ` checked by `decide`. The block theorems
are the generic theorems of `FieldLimbs.Mont` at these records.

## Main definitions

* `p384`, `bls12381`, `rsa4096`: the records.

## Main results

* `p384_mulBlk_denote`, `bls12381_mulBlk_denote`, `rsa4096_mulBlk_denote`: the Montgomery
  multiplication block at each modulus denotes the Montgomery form of the product.
* `p384_invBlk_denote_inv`, `bls12381_invBlk_denote_inv`: the inversion block at each
  prime, from its primality certificate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.MontInstances

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (w64 nv)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont

/-! ## 1. The records -/

set_option exponentiation.threshold 600 in
/-- The NIST P-384 base prime with `nInv = 0x100000001`. -/
def p384 : LimbParams 6 where
  p := CatCrypt.Crypto.Util.P384PPrimeCert.p384Plit
  nInv := 0x100000001
  one_lt := by decide
  p_odd := by decide
  p_lt := by decide
  nInv_lt := by decide
  nInv_spec := by decide

set_option exponentiation.threshold 600 in
/-- The BLS12-381 base prime with `nInv = 0x89f3fffcfffcfffd`. -/
def bls12381 : LimbParams 6 where
  p := CatCrypt.Crypto.Util.BLS12381PPrimeCert.bls12381Plit
  nInv := 0x89f3fffcfffcfffd
  one_lt := by decide
  p_odd := by decide
  p_lt := by decide
  nInv_lt := by decide
  nInv_spec := by decide

/-- The modulus `n` of the 4096-bit RSA test key of RFC 9474, Appendix A
    (`chaum-hax/tests/rfc9474_kat.rs`, `N_HEX`), over 64 limbs, with
    `nInv = 0x056225998c4e0183`. The modulus is composite; the Montgomery template needs
    only an odd modulus. -/
def rsa4096 : LimbParams 64 where
  p := 0xaec4d69addc70b990ea66a5e70603b6fee27aafebd08f2d94cbe1250c556e047a928d635c3f45ee9b66d1bc628a03bac9b7c3f416fe20dabea8f3d7b4bbf7f963be335d2328d67e6c13ee4a8f955e05a3283720d3e1f139c38e43e0338ad058a9495c53377fc35be64d208f89b4aa721bf7f7d3fef837be2a80e0f8adf0bcd1eec5bb040443a2b2792fdca522a7472aed74f31a1ebe1eebc1f408660a0543dfe2a850f106a617ec6685573702eaaa21a5640a5dcaf9b74e397fa3af18a2f1b7c03ba91a6336158de420d63188ee143866ee415735d155b7c2d854d795b7bc236cffd71542df34234221a0413e142d8c61355cc44d45bda94204974557ac2704cd8b593f035a5724b1adf442e78c542cd4414fce6f1298182fb6d8e53cef1adfd2e90e1e4deec52999bdc6c29144e8d52a125232c8c6d75c706ea3cc06841c7bda33568c63a6c03817f722b50fcf898237d788a4400869e44d90a3020923dc646388abcc914315215fcd1bae11b1c751fd52443aac8f601087d8d42737c18a3fa11ecd4131ecae017ae0a14acfc4ef85b83c19fed33cfd1cd629da2c4c09e222b398e18d822f77bb378dea3cb360b605e5aa58b20edc29d000a66bd177c682a17e7eb12a63ef7c2e4183e0d898f3d6bf567ba8ae84f84f1d23bf8b8e261c3729e2fa6d07b832e07cddd1d14f55325c6f924267957121902dc19b3b32948bdead5
  nInv := 0x056225998c4e0183
  one_lt := by decide
  p_odd := by decide
  p_lt := by decide +kernel
  nInv_lt := by decide
  nInv_spec := by decide

/-! ## 2. Multiplication and inversion at each modulus -/

section Blocks

variable {Γ : Ctxt jasminDialect} (W : Valuation Γ) (xs ys : List (Var Γ w64))

theorem p384_mulBlk_denote (hxs : xs.length = 6) (hys : ys.length = 6) (x y : ZMod p384.p)
    (hx : nv W xs = (x * R p384).val) (hy : nv W ys = (y * R p384).val) :
    (mulBlk p384 xs ys).denote W = enc p384 (x * y) :=
  mulBlk_denote p384 W xs ys hxs hys x y hx hy

theorem bls12381_mulBlk_denote (hxs : xs.length = 6) (hys : ys.length = 6)
    (x y : ZMod bls12381.p) (hx : nv W xs = (x * R bls12381).val)
    (hy : nv W ys = (y * R bls12381).val) :
    (mulBlk bls12381 xs ys).denote W = enc bls12381 (x * y) :=
  mulBlk_denote bls12381 W xs ys hxs hys x y hx hy

theorem rsa4096_mulBlk_denote (hxs : xs.length = 64) (hys : ys.length = 64)
    (x y : ZMod rsa4096.p) (hx : nv W xs = (x * R rsa4096).val)
    (hy : nv W ys = (y * R rsa4096).val) :
    (mulBlk rsa4096 xs ys).denote W = enc rsa4096 (x * y) :=
  mulBlk_denote rsa4096 W xs ys hxs hys x y hx hy

theorem p384_invBlk_denote_inv (hxs : xs.length = 6) (x : ZMod p384.p)
    (hx : nv W xs = (x * R p384).val) :
    (invBlk p384 xs).denote W = enc p384 x⁻¹ :=
  invBlk_denote_inv p384 CatCrypt.Crypto.Util.P384PPrimeCert.p384Plit_prime W xs hxs x hx

theorem bls12381_invBlk_denote_inv (hxs : xs.length = 6) (x : ZMod bls12381.p)
    (hx : nv W xs = (x * R bls12381).val) :
    (invBlk bls12381 xs).denote W = enc bls12381 x⁻¹ :=
  invBlk_denote_inv bls12381 CatCrypt.Crypto.Util.BLS12381PPrimeCert.bls12381Plit_prime W xs
    hxs x hx

end Blocks

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.MontInstances
