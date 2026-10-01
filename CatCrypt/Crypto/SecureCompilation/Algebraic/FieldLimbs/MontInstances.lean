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
# Six-limb Montgomery moduli of the 384-bit elliptic-curve base fields

`Mont.LimbParams 6` records for two moduli below `2^384`, each with
`nInv = -p⁻¹ mod 2^64`:

* `p384`: the NIST P-384 base prime `2^384 - 2^128 - 2^96 + 2^32 - 1`
  (`P384PPrimeCert.p384Plit`), `nInv = 0x100000001`.
* `bls12381`: the BLS12-381 base prime (`BLS12381PPrimeCert.bls12381Plit`),
  `nInv = 0x89f3fffcfffcfffd`.

Each modulus is the literal of its primality certificate, and each `nInv` is checked by
`nInv_spec`. The block theorems are the generic theorems of `FieldLimbs.Mont` at these
records.

## Main definitions

* `p384`, `bls12381`: the records.

## Main results

* `p384_mulBlk_denote`, `bls12381_mulBlk_denote`: the Montgomery multiplication block
  at each modulus denotes the Montgomery form of the product.
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
