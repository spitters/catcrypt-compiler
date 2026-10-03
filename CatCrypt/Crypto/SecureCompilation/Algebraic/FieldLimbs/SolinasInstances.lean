/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas

/-!
# Solinas moduli of Curve25519, secp256k1, Poly1305 and P-521

`Solinas.SolinasParams n` records for four moduli `p = 2^k - c`:

* `curve25519`: `2^255 - 19` on four limbs.
* `secp256k1`: `2^256 - 2^32 - 977` on four limbs (`k = 256`, a split at a limb
  boundary).
* `poly1305`: `2^130 - 5` on three limbs (`k = 130`, a split two bits into limb `2`).
* `p521`: `2^521 - 1` on nine limbs (`k = 521 = 8 · 64 + 9`, a split nine bits into
  limb `8`; with `c = 1` each fold is the Mersenne fold `v ↦ ⌊v / 2^521⌋ + v mod 2^521`).

The side conditions are checked by `decide`. The block theorems are the generic
theorems of `FieldLimbs.Solinas` at these records.

## Main definitions

* `curve25519`, `secp256k1`, `poly1305`, `p521`: the records.

## Main results

* `curve25519_p`, `secp256k1_p`, `poly1305_p`, `p521_p`: the moduli.
* `curve25519_mulBlk_denote`, `secp256k1_mulBlk_denote`, `poly1305_mulBlk_denote`,
  `p521_mulBlk_denote` and the `addBlk`, `subBlk` analogues: the blocks at each modulus.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.SolinasInstances

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (w64 nv)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas

/-! ## 1. The records -/

/-- `2^255 - 19` on four limbs. -/
def curve25519 : SolinasParams 4 where
  k := 255
  c := 19
  c_odd := by decide
  c_lt := by decide
  k_ge := by decide
  k_le := by decide
  cc_lt := by decide

/-- `2^256 - (2^32 + 977)` on four limbs. -/
def secp256k1 : SolinasParams 4 where
  k := 256
  c := 2 ^ 32 + 977
  c_odd := by decide
  c_lt := by decide
  k_ge := by decide
  k_le := by decide
  cc_lt := by decide

/-- `2^130 - 5` on three limbs. -/
def poly1305 : SolinasParams 3 where
  k := 130
  c := 5
  c_odd := by decide
  c_lt := by decide
  k_ge := by decide
  k_le := by decide
  cc_lt := by decide

/-- The Mersenne prime `2^521 - 1` on nine limbs. -/
def p521 : SolinasParams 9 where
  k := 521
  c := 1
  c_odd := by decide
  c_lt := by decide
  k_ge := by decide
  k_le := by decide
  cc_lt := by decide +kernel

theorem curve25519_p : p curve25519 = 2 ^ 255 - 19 := rfl

theorem secp256k1_p : p secp256k1 = 2 ^ 256 - 2 ^ 32 - 977 := rfl

theorem poly1305_p : p poly1305 = 2 ^ 130 - 5 := rfl

theorem p521_p : p p521 = 2 ^ 521 - 1 := by decide +kernel

/-! ## 2. The blocks at each modulus -/

section Blocks

variable {Γ : Ctxt jasminDialect} (W : Valuation Γ) (xs ys : List (Var Γ w64))

theorem curve25519_mulBlk_denote (hxs : xs.length = 4) (hys : ys.length = 4)
    (x y : ZMod (2 ^ 255 - 19)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (mulBlk curve25519 xs ys).denote W = enc curve25519 (x * y) :=
  mulBlk_denote curve25519 W xs ys hxs hys x y hx hy

theorem curve25519_addBlk_denote (hxs : xs.length = 4) (hys : ys.length = 4)
    (x y : ZMod (2 ^ 255 - 19)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (addBlk curve25519 xs ys).denote W = enc curve25519 (x + y) :=
  addBlk_denote curve25519 W xs ys hxs hys x y hx hy

theorem curve25519_subBlk_denote (hxs : xs.length = 4) (hys : ys.length = 4)
    (x y : ZMod (2 ^ 255 - 19)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (subBlk curve25519 xs ys).denote W = enc curve25519 (x - y) :=
  subBlk_denote curve25519 W xs ys hxs hys x y hx hy

theorem secp256k1_mulBlk_denote (hxs : xs.length = 4) (hys : ys.length = 4)
    (x y : ZMod (2 ^ 256 - 2 ^ 32 - 977)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (mulBlk secp256k1 xs ys).denote W = enc secp256k1 (x * y) :=
  mulBlk_denote secp256k1 W xs ys hxs hys x y hx hy

theorem secp256k1_addBlk_denote (hxs : xs.length = 4) (hys : ys.length = 4)
    (x y : ZMod (2 ^ 256 - 2 ^ 32 - 977)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (addBlk secp256k1 xs ys).denote W = enc secp256k1 (x + y) :=
  addBlk_denote secp256k1 W xs ys hxs hys x y hx hy

theorem secp256k1_subBlk_denote (hxs : xs.length = 4) (hys : ys.length = 4)
    (x y : ZMod (2 ^ 256 - 2 ^ 32 - 977)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (subBlk secp256k1 xs ys).denote W = enc secp256k1 (x - y) :=
  subBlk_denote secp256k1 W xs ys hxs hys x y hx hy

theorem poly1305_mulBlk_denote (hxs : xs.length = 3) (hys : ys.length = 3)
    (x y : ZMod (2 ^ 130 - 5)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (mulBlk poly1305 xs ys).denote W = enc poly1305 (x * y) :=
  mulBlk_denote poly1305 W xs ys hxs hys x y hx hy

theorem poly1305_addBlk_denote (hxs : xs.length = 3) (hys : ys.length = 3)
    (x y : ZMod (2 ^ 130 - 5)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (addBlk poly1305 xs ys).denote W = enc poly1305 (x + y) :=
  addBlk_denote poly1305 W xs ys hxs hys x y hx hy

theorem poly1305_subBlk_denote (hxs : xs.length = 3) (hys : ys.length = 3)
    (x y : ZMod (2 ^ 130 - 5)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (subBlk poly1305 xs ys).denote W = enc poly1305 (x - y) :=
  subBlk_denote poly1305 W xs ys hxs hys x y hx hy

set_option exponentiation.threshold 521 in
theorem p521_mulBlk_denote (hxs : xs.length = 9) (hys : ys.length = 9)
    (x y : ZMod (p p521)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (mulBlk p521 xs ys).denote W = enc p521 (x * y) :=
  mulBlk_denote p521 W xs ys hxs hys x y hx hy

set_option exponentiation.threshold 521 in
theorem p521_addBlk_denote (hxs : xs.length = 9) (hys : ys.length = 9)
    (x y : ZMod (p p521)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (addBlk p521 xs ys).denote W = enc p521 (x + y) :=
  addBlk_denote p521 W xs ys hxs hys x y hx hy

set_option exponentiation.threshold 521 in
theorem p521_subBlk_denote (hxs : xs.length = 9) (hys : ys.length = 9)
    (x y : ZMod (p p521)) (hx : nv W xs = x.val) (hy : nv W ys = y.val) :
    (subBlk p521 xs ys).denote W = enc p521 (x - y) :=
  subBlk_denote p521 W xs ys hxs hys x y hx hy

end Blocks

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.SolinasInstances
