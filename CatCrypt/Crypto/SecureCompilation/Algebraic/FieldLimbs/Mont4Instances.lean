/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4
public import CatCrypt.Crypto.Util.P256Verified
public import CatCrypt.Crypto.Util.Secp256k1Verified
public import CatCrypt.Crypto.Util.ScalarFieldVerified
public import CatCrypt.Crypto.Util.SM2PPrimeCert
public import CatCrypt.Crypto.Util.BN254Verified

/-!
# Four-limb Montgomery moduli of the 256-bit elliptic-curve fields

`Mont4Prime` records for six moduli below `2^256`, each with `nInv = -p⁻¹ mod 2^64`:

* `p256`: the NIST P-256 base prime `CatCrypt.Util.P256` (FIPS 186-4), `nInv = 1`.
* `secp256k1`: the secp256k1 base prime `CatCrypt.Util.Secp256k1P` (SEC 2 v2 §2.4.1),
  `nInv = 0xd838091dd2253531`.
* `sm2`: the SM2 base prime `2^256 - 2^224 - 2^96 + 2^64 - 1` (GB/T 32918.5), `nInv = 1`.
* `p256n`: the P-256 group order `CatCrypt.Util.P256N`, `nInv = 0xccd1c8aaee00bc4f`.
* `secp256k1n`: the secp256k1 group order `CatCrypt.Util.Secp256k1N`,
  `nInv = 0x4b0dff665588b13f`.
* `bn254`: the BN254 (alt_bn128) base prime `CatCrypt.Util.BN254`, below `2^254`,
  `nInv = 0x87d20782e4866389`.

The moduli other than `sm2` are the spec constants themselves, so the records carry no
transcribed value; each `nInv` is checked by `nInv_spec`.

## Main definitions

* `p256`, `secp256k1`, `sm2`, `p256n`, `secp256k1n`, `bn254`: the records.

## Main results

* `p256_mulBlk_denote`, `secp256k1_mulBlk_denote`, `sm2_mulBlk_denote`,
  `p256n_mulBlk_denote`, `secp256k1n_mulBlk_denote`, `bn254_mulBlk_denote`: the
  Montgomery multiplication block at each modulus denotes the Montgomery form of the
  product.
* `bn254_addBlk_denote`: the addition block at the BN254 modulus.
* `p256_invBlk_denote_inv`, `secp256k1_invBlk_denote_inv`, `sm2_invBlk_denote_inv`,
  `p256n_invBlk_denote_inv`, `secp256k1n_invBlk_denote_inv`, `bn254_invBlk_denote_inv`:
  the inversion block at each prime, from its primality certificate.
* `sm2_p_hex`: the SM2 modulus equals its published hexadecimal value.
* `sm2_prime`: the SM2 modulus is prime.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4Instances

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (w64 nv)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4

/-! ## 1. The records -/

/-- The NIST P-256 base prime with `nInv = 1`. -/
def p256 : Mont4Prime where
  p := CatCrypt.Util.P256
  nInv := 1
  one_lt := by decide
  p_odd := by decide
  p_lt := by decide
  nInv_lt := by decide
  nInv_spec := by decide

/-- The secp256k1 base prime with `nInv = 0xd838091dd2253531`. -/
def secp256k1 : Mont4Prime where
  p := CatCrypt.Util.Secp256k1P
  nInv := 0xd838091dd2253531
  one_lt := by decide
  p_odd := by decide
  p_lt := by decide
  nInv_lt := by decide
  nInv_spec := by decide

/-- The SM2 base prime `2^256 - 2^224 - 2^96 + 2^64 - 1` with `nInv = 1`. -/
def sm2 : Mont4Prime where
  p := 2 ^ 256 - 2 ^ 224 - 2 ^ 96 + 2 ^ 64 - 1
  nInv := 1
  one_lt := by decide
  p_odd := by decide
  p_lt := by decide
  nInv_lt := by decide
  nInv_spec := by decide

/-- The P-256 group order with `nInv = 0xccd1c8aaee00bc4f`. -/
def p256n : Mont4Prime where
  p := CatCrypt.Util.P256N
  nInv := 0xccd1c8aaee00bc4f
  one_lt := by decide
  p_odd := by decide
  p_lt := by decide
  nInv_lt := by decide
  nInv_spec := by decide

/-- The secp256k1 group order with `nInv = 0x4b0dff665588b13f`. -/
def secp256k1n : Mont4Prime where
  p := CatCrypt.Util.Secp256k1N
  nInv := 0x4b0dff665588b13f
  one_lt := by decide
  p_odd := by decide
  p_lt := by decide
  nInv_lt := by decide
  nInv_spec := by decide

/-- The BN254 (alt_bn128) base prime with `nInv = 0x87d20782e4866389`. -/
def bn254 : Mont4Prime where
  p := CatCrypt.Util.BN254
  nInv := 0x87d20782e4866389
  one_lt := by decide
  p_odd := by decide
  p_lt := by decide
  nInv_lt := by decide
  nInv_spec := by decide

/-- The SM2 modulus is the published value
    `FFFFFFFE FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF 00000000 FFFFFFFF FFFFFFFF`. -/
theorem sm2_p_hex :
    sm2.p = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF := by
  decide

/-- The SM2 modulus is prime, by the Lucas certificate `SM2PPrimeCert.sm2Plit_prime`. -/
theorem sm2_prime : sm2.p.Prime := by
  rw [sm2_p_hex]
  exact CatCrypt.Crypto.Util.SM2PPrimeCert.sm2Plit_prime

/-! ## 2. Multiplication at each modulus, addition at BN254 -/

section Blocks

variable {Γ : Ctxt jasminDialect} (W : Valuation Γ) (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Var Γ w64)

theorem p256_mulBlk_denote (x y : ZMod p256.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R p256).val)
    (hy : nv W [y₀, y₁, y₂, y₃] = (y * R p256).val) :
    (mulBlk p256 x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc p256 (x * y) :=
  mulBlk_denote p256 W _ _ _ _ _ _ _ _ x y hx hy

theorem secp256k1_mulBlk_denote (x y : ZMod secp256k1.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R secp256k1).val)
    (hy : nv W [y₀, y₁, y₂, y₃] = (y * R secp256k1).val) :
    (mulBlk secp256k1 x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc secp256k1 (x * y) :=
  mulBlk_denote secp256k1 W _ _ _ _ _ _ _ _ x y hx hy

theorem sm2_mulBlk_denote (x y : ZMod sm2.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R sm2).val)
    (hy : nv W [y₀, y₁, y₂, y₃] = (y * R sm2).val) :
    (mulBlk sm2 x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc sm2 (x * y) :=
  mulBlk_denote sm2 W _ _ _ _ _ _ _ _ x y hx hy

theorem p256n_mulBlk_denote (x y : ZMod p256n.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R p256n).val)
    (hy : nv W [y₀, y₁, y₂, y₃] = (y * R p256n).val) :
    (mulBlk p256n x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc p256n (x * y) :=
  mulBlk_denote p256n W _ _ _ _ _ _ _ _ x y hx hy

theorem secp256k1n_mulBlk_denote (x y : ZMod secp256k1n.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R secp256k1n).val)
    (hy : nv W [y₀, y₁, y₂, y₃] = (y * R secp256k1n).val) :
    (mulBlk secp256k1n x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc secp256k1n (x * y) :=
  mulBlk_denote secp256k1n W _ _ _ _ _ _ _ _ x y hx hy

theorem bn254_mulBlk_denote (x y : ZMod bn254.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R bn254).val)
    (hy : nv W [y₀, y₁, y₂, y₃] = (y * R bn254).val) :
    (mulBlk bn254 x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc bn254 (x * y) :=
  mulBlk_denote bn254 W _ _ _ _ _ _ _ _ x y hx hy

theorem bn254_addBlk_denote (x y : ZMod bn254.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R bn254).val)
    (hy : nv W [y₀, y₁, y₂, y₃] = (y * R bn254).val) :
    (addBlk bn254 x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃).denote W = enc bn254 (x + y) :=
  addBlk_denote bn254 W _ _ _ _ _ _ _ _ x y hx hy

/-! ## 3. Inversion at the certified primes -/

theorem p256_invBlk_denote_inv (x : ZMod p256.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R p256).val) :
    (invBlk p256 x₀ x₁ x₂ x₃).denote W = enc p256 x⁻¹ :=
  invBlk_denote_inv p256 CatCrypt.Util.p256_prime W _ _ _ _ x hx

theorem secp256k1_invBlk_denote_inv (x : ZMod secp256k1.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R secp256k1).val) :
    (invBlk secp256k1 x₀ x₁ x₂ x₃).denote W = enc secp256k1 x⁻¹ :=
  invBlk_denote_inv secp256k1 CatCrypt.Util.secp256k1_prime W _ _ _ _ x hx

theorem sm2_invBlk_denote_inv (x : ZMod sm2.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R sm2).val) :
    (invBlk sm2 x₀ x₁ x₂ x₃).denote W = enc sm2 x⁻¹ :=
  invBlk_denote_inv sm2 sm2_prime W _ _ _ _ x hx

theorem p256n_invBlk_denote_inv (x : ZMod p256n.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R p256n).val) :
    (invBlk p256n x₀ x₁ x₂ x₃).denote W = enc p256n x⁻¹ :=
  invBlk_denote_inv p256n CatCrypt.Util.p256N_prime W _ _ _ _ x hx

theorem secp256k1n_invBlk_denote_inv (x : ZMod secp256k1n.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R secp256k1n).val) :
    (invBlk secp256k1n x₀ x₁ x₂ x₃).denote W = enc secp256k1n x⁻¹ :=
  invBlk_denote_inv secp256k1n CatCrypt.Util.secp256k1N_prime W _ _ _ _ x hx

theorem bn254_invBlk_denote_inv (x : ZMod bn254.p)
    (hx : nv W [x₀, x₁, x₂, x₃] = (x * R bn254).val) :
    (invBlk bn254 x₀ x₁ x₂ x₃).denote W = enc bn254 x⁻¹ :=
  invBlk_denote_inv bn254 CatCrypt.Util.bn254_prime W _ _ _ _ x hx

end Blocks

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4Instances
