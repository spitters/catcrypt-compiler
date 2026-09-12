/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Fp12_377ValBridge
public import CatCrypt.Crypto.SecureCompilation.VIR.Fp12Gt

/-!
# The `Fp12Val bls377Q ≃ Fp12_377` carrier equivalence, with `_mul`/`_one` transport

`Fp12_377ValBridge` builds the componentwise carrier maps between the dialect GT
value `FieldDialect.Fp12Val bls377Q` and the relational-front pairing field
`RelationalFront.Fp12_377`, proves they are mutually inverse, and proves the
forward map `toFp12` carries the relational-front multiply to the dialect
β-parametric multiply at the BLS12-377 non-residues (`toFp12_mul_bls377`,
`ξ₂ = −5`, `ξ₆ = u`).

This file bundles those maps into a single `Equiv` `Fp12Val bls377Q ≃ Fp12_377`
and exposes the transport interface the BLS12-377 pairing discharge consumes — the
same interface `Fp12PairingEmitInstance` uses on the BLS12-381 side
(`ofTower_mul` / `ofTower_one` + injectivity):

* `bls377Equiv` — the coordinate equivalence, `ofFp12` forward, `toFp12` back.
* `toFp12_one` / `ofFp12_one` — the maps carry the multiplicative unit to the unit
  (both units are the structural `⟨⟨⟨1,0⟩,0,0⟩,0⟩` element, independent of the
  non-residue).
* `ofFp12_mul_bls377` — the `ofFp12` direction of `toFp12_mul_bls377`: the dialect
  β-parametric product `Fp12Val.mulBeta (−5) 0` is carried to the relational-front
  `Fp12_377` multiply at the BLS12-377 non-residues.  Derived from
  `toFp12_mul_bls377` and the bijection.
* `ofFp12_add` / `ofFp12_sub` — the additive-carrier direction of `toFp12_add` /
  `toFp12_sub`.

The pairing value `RelationalFrontBls377MillerLoop.millerLoop` / the concrete
`Bls377MillerSteps.concretePairing` are valued in `Fp12_377`; `toFp12` transports
them into the dialect GT carrier `Fp12Val bls377Q`, where the curve-generic
`pairingCheck2` / `pairingCheckDialect` op applies at `p = bls377Q`.

Every obligation is proved (no axiom, no `sorry`); the transport lemmas reduce to
the ring-hom facts of `Fp12_377ValBridge` plus the `toFp12`/`ofFp12` bijection.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Fp12_377ValBridge

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.RelationalFront

/-! ## 1. The coordinate equivalence -/

/-- The BLS12-377 GT carrier equivalence: the dialect value `Fp12Val bls377Q` and
    the relational-front pairing field `Fp12_377` are componentwise inverse, so
    they are equivalent.  `ofFp12` forward, `toFp12` back. -/
def bls377Equiv : Fp12Val bls377Q ≃ Fp12_377 where
  toFun := ofFp12
  invFun := toFp12
  left_inv := toFp12_ofFp12
  right_inv := ofFp12_toFp12

@[simp] theorem bls377Equiv_apply (x : Fp12Val bls377Q) : bls377Equiv x = ofFp12 x := rfl
@[simp] theorem bls377Equiv_symm_apply (x : Fp12_377) :
    bls377Equiv.symm x = toFp12 x := rfl

/-! ## 2. Unit compatibility (`_one`) -/

/-- `toFp12` carries the relational-front unit to the dialect unit. -/
theorem toFp12_one : toFp12 (1 : Fp12_377) = (1 : Fp12Val bls377Q) := rfl

/-- `ofFp12` carries the dialect unit to the relational-front unit. -/
theorem ofFp12_one : ofFp12 (1 : Fp12Val bls377Q) = (1 : Fp12_377) := rfl

/-! ## 3. Product compatibility in the `ofFp12` direction (BLS12-377 non-residues) -/

/-- The dialect β-parametric product `Fp12Val.mulBeta (−5) 0` is carried by
    `ofFp12` to the relational-front `Fp12_377` multiply at the BLS12-377
    non-residues (`ξ₂ = −5`, `ξ₆ = u`).  The `ofFp12` direction of
    `toFp12_mul_bls377`, derived through the `toFp12`/`ofFp12` bijection. -/
theorem ofFp12_mul_bls377 (a b : Fp12Val bls377Q) :
    ofFp12 (Fp12Val.mulBeta bls377Beta bls377Xi0 a b)
      = Fp12_377.mulSchoolbook bls377Beta bls377Xi6 (ofFp12 a) (ofFp12 b) := by
  apply toFp12_injective
  simp only [toFp12_ofFp12, toFp12_mul_bls377]

/-! ## 4. Additive compatibility in the `ofFp12` direction -/

/-- `ofFp12` carries the dialect add to the relational-front add. -/
theorem ofFp12_add (a b : Fp12Val bls377Q) :
    ofFp12 (Fp12Val.add a b) = ofFp12 a + ofFp12 b := by
  apply toFp12_injective
  simp only [toFp12_ofFp12, toFp12_add]

/-- `ofFp12` carries the dialect sub to the relational-front sub. -/
theorem ofFp12_sub (a b : Fp12Val bls377Q) :
    ofFp12 (Fp12Val.sub a b) = ofFp12 a - ofFp12 b := by
  apply toFp12_injective
  simp only [toFp12_ofFp12, toFp12_sub]

end CatCrypt.Crypto.SecureCompilation.VIR.Fp12_377ValBridge
