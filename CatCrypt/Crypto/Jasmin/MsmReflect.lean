/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# Toy-EC MSM reflect surface — pairing-ZK shared MSM kernel via the verified front

This file is the **toy EC (Z/23) analogue** of `Secp256k1Reflect.lean` /
`P256Reflect.lean`: it adds toy-EC opaque surface types (`MsmEcScalar`,
`MsmEcPoint`) and `@[rust_cmd_pattern]` registrations so that a pure-Lean
MSM-term kernel can be lifted through the verified compiler chain
`LowCT → CryptoSSA → Com → jasmin`, **without** editing
`LowCTReflect.lean`'s `knownOps` table.

## Toy EC group (matches the legacy `bench/msm_compare/msm_emit.lean`)

The toy EC group is `y² = x³ + a·x + b` over `Fp = Z/23`
(`Pairing.MsmReduce.toyW`), matching `ec_ref.h`'s `P=23`. A curve point
on the wire is two little-endian field bytes `(x ‖ y)`, 2 bytes total;
a scalar is one byte. This is a clearly-labelled small/model EC group
that *validates* the "MSM = scalarFold over the EC AddCommMonoid"
reduction (`Pairing.MsmReduce.msm_eq_scalarFold`) at a field where the EC
ops are schoolbook modular arithmetic.

| Lean axiom              | Leaf name (.jazz)      | TowerType    |
|------------------------|------------------------|--------------|
| `ec_scalar_mul`         | `ec_scalar_mul`        | `TBytes 2`   |
| `ec_point_add`          | `ec_point_add`         | `TBytes 2`   |

## Per-term MSM body

The full `for i = 0 to L { acc += k_i · P_i }` MSM is built around this
Reflect surface's per-term body (same approach as
`Secp256k1Reflect`/`P256Reflect`): the rustcmd lifts ONE iteration body
`t = ec_scalar_mul(k, P)`, and the verified loop layer (or the legacy
emit's hand-written `for`) wraps the iteration.

## L2↔L3 hax bridge

The toy EC group has NO hax extraction (the production analogue lives in
BLS12-381 / secp256k1 / P-256). The MSM bench is a **toy/model**
artefact validating the `scalarFold_eq_hsum` reduction at a tractable
field — its bridge to hax is the production-curve siblings, not a hax
extraction of the toy curve itself. The named hypothesis
`MsmToyECCorrect` records the bridge target (the production hax
extractions of secp256k1 / P-256 / BLS12-381 are the in-scope ones).

## Reflection→front gap (same pattern as Secp256k1Reflect/UovReflect)

`reifyLowCT%` doesn't consult the `LowCTPattern` registry, so we
register the leaves via `@[rust_cmd_pattern]` and hand-build the
`LowCT` body the reifier *would* produce.

## References

* `bench/msm_compare/msm_emit.lean` — legacy Tier C emit (kept as
  out-of-chain reference)
* `CatCrypt/Crypto/Pairing/MsmReduce.lean` — `msm_eq_scalarFold`,
  `ECPt`, `EcLeafAgrees`, the toy-EC reduction this file glues into
  the verified front
-/

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque toy-EC surface types

The toy EC group lives over `Fp = ZMod 23` (a single byte, low 5 bits
used; one byte holds one Fp element). A point is `(x ‖ y)` = 2 bytes; a
scalar is 1 byte. -/

/-- A toy-EC scalar (one byte, the Z/23 representative). Opaque. -/
axiom MsmEcScalar : Type
/-- Axiomatic inhabitant. -/ axiom MsmEcScalar.default : MsmEcScalar
noncomputable instance : Inhabited MsmEcScalar := ⟨MsmEcScalar.default⟩

/-- A toy-EC affine point `(x ‖ y)` over Z/23. 2 bytes. The identity is
    the on-wire sentinel `(0xff, 0xff)`. Opaque. -/
axiom MsmEcPoint : Type
/-- Axiomatic inhabitant. -/ axiom MsmEcPoint.default : MsmEcPoint
noncomputable instance : Inhabited MsmEcPoint := ⟨MsmEcPoint.default⟩

/-! ## 2. Toy-EC leaves -/

/-- Toy-EC scalar multiplication `R = k · P` over Z/23. Opaque; the
    jasmin shim implements double-and-add over `ZMod 23`. -/
axiom ec_scalar_mul : MsmEcScalar → MsmEcPoint → MsmEcPoint

/-- Toy-EC point addition `R = P + Q` over Z/23. Opaque; the jasmin
    shim implements the short-Weierstrass affine point-add formula over
    `ZMod 23`, with the on-wire `(0xff, 0xff)` identity sentinel. -/
axiom ec_point_add : MsmEcPoint → MsmEcPoint → MsmEcPoint

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

/-- Register `ec_scalar_mul` → leaf `ec_scalar_mul`. -/
@[rust_cmd_pattern]
def msmEcScalarMulPattern : LowCTPattern where
  name      := "ec_scalar_mul"
  fnHead    := ``ec_scalar_mul
  arity     := 2
  towerType := .TBytes 2   -- 2-byte result point (x ‖ y)

/-- Register `ec_point_add` → leaf `ec_point_add`. -/
@[rust_cmd_pattern]
def msmEcPointAddPattern : LowCTPattern where
  name      := "ec_point_add"
  fnHead    := ``ec_point_add
  arity     := 2
  towerType := .TBytes 2   -- 2-byte result point

/-! ## 4. Toy-EC tower-type abbreviations -/

/-- Tower type of a toy-EC scalar. -/
def msmEcScalarTowerType : TowerType := .TBytes 1

/-- Tower type of a toy-EC point. -/
def msmEcPointTowerType : TowerType := .TBytes 2

private def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean toy-EC kernel function -/

/-- One MSM term: `t = ec_scalar_mul(k, P)`, the lane op of `scalarFold`. -/
noncomputable def msmEcTermLean (k : MsmEcScalar) (P : MsmEcPoint) : MsmEcPoint :=
  ec_scalar_mul k P

/-! ## 6. Hand-built `LowCT` body -/

/-- The `LowCT` body for the per-term MSM. -/
def msmEcTermBody : LowCT :=
  let k_l      := loc "k"        msmEcScalarTowerType
  let P_l      := loc "P"        msmEcPointTowerType
  let result_l := loc "__result" msmEcPointTowerType
  .RSeq .RSkip
    (.RCall "ec_scalar_mul" result_l [k_l, P_l])

/-- `ReifiedFunc` bundle for the MSM-term kernel. -/
def msmEcTermReified : ReifiedFunc :=
  { args    := [("k", msmEcScalarTowerType),
                ("P", msmEcPointTowerType)]
    body    := msmEcTermBody
    retName := "__result" }

/-! ## 7. Inspection -/

#eval msmEcTermReified.args.map Prod.fst              -- [k, P]
#eval msmEcTermReified.args.length                    -- 2
#eval msmEcTermReified.retName                        -- __result

end CatCrypt.Crypto.Jasmin.LowCTReflect
