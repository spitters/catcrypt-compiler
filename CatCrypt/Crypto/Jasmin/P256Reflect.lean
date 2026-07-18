/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# P-256 reflect surface — scalar-mul MSM + ECDSA-verify kernels via the
verified front

This file is the **P-256 (NIST FIPS 186-4) analogue** of `Secp256k1Reflect.lean`:
it adds P-256-specific opaque surface types (`P256Scalar`, `P256Point`) and
`@[rust_cmd_pattern]` registrations so that pure-Lean P-256 kernels
(scalar-mul, point-add, ECDSA-verify 2-term MSM) can be lifted through the
verified compiler chain `LowCT → CryptoSSA → Com → jasmin`, **without**
editing `LowCTReflect.lean`'s `knownOps` table.

## Two kernels (matches the legacy `bench/p256_compare/p256_emit.lean`)

* **`p256MsmTermLean`** — one term of the scalar-mul MSM `Σ_i k_i·P_i`:
  `p256_scalar_mul(k_i, P_i)`. Tier-A artefact for one fold step.
* **`p256EcdsaVerifyLean`** — `R' = u₁·G + u₂·Q` in ECDSA-P256 verify:
  two `p256_scalar_mul` leaves + one `p256_point_add` leaf.

## Leaf surface (AUCurves verified-bedrock2 field tower)

The leaves are the P-256 group law built over the AUCurves verified-bedrock2
field tower (`p256-safe-rust`: fiat `fp_add/sub/mul/square/opp` + Bernstein–
Yang `fp_inv`). The Pairing.P256Emit theory proves `MsmReduce.msm_eq_scalarFold`
over the production P-256 group; this file is the Tier A glue carrying
that into the verified front-end.

## Reflection→front gap (same pattern as Secp256k1Reflect)

`reifyLowCT%` doesn't consult the `LowCTPattern` registry, so we
register each leaf via `@[rust_cmd_pattern]`, then hand-build the
`LowCT` body the reifier *would* produce.

## References

* FIPS 186-4: Digital Signature Standard (DSS), Appendix D.1.2.3 (P-256)
* `bench/p256_compare/p256_emit.lean` — legacy Tier C emit (kept as
  out-of-chain reference)
* `CatCrypt/Crypto/Pairing/P256Emit.lean` — `msmFold_eq_msm`,
  `ecdsaVerifyCom_denote`, the production-group reduction this file glues
  into the verified front
-/

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque P-256 surface types

A P-256 field element `Fp` is 4 little-endian `u64` limbs = 32 bytes
(matching fiat-crypto `[u64;4]` Montgomery layout). On the wire an affine
point is `(x ‖ y)` = 64 bytes; a scalar is 32 bytes. -/

/-- A P-256 scalar (an element of `Fn`, mod the P-256 group order). 32
    bytes on the wire. Opaque. -/
axiom P256Scalar : Type
/-- Axiomatic inhabitant. -/ axiom P256Scalar.default : P256Scalar
noncomputable instance : Inhabited P256Scalar := ⟨P256Scalar.default⟩

/-- A P-256 affine point `(x ‖ y)`. 64 bytes on the wire. Opaque. -/
axiom P256Point : Type
/-- Axiomatic inhabitant. -/ axiom P256Point.default : P256Point
noncomputable instance : Inhabited P256Point := ⟨P256Point.default⟩

/-! ## 2. P-256 leaves -/

/-- P-256 scalar multiplication `R = k · P`. Opaque; the jasmin shim
    issues the ladder over the AUCurves-verified field leaves. -/
axiom p256_scalar_mul : P256Scalar → P256Point → P256Point

/-- P-256 point addition `R = P + Q`. Opaque; the jasmin shim implements
    the short-Weierstrass affine point-add formula over the AUCurves-
    verified field leaves. -/
axiom p256_point_add : P256Point → P256Point → P256Point

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

/-- Register `p256_scalar_mul` → leaf `p256_scalar_mul`. -/
@[rust_cmd_pattern]
def p256ScalarMulPattern : LowCTPattern where
  name      := "p256_scalar_mul"
  fnHead    := ``p256_scalar_mul
  arity     := 2
  towerType := .TBytes 64

/-- Register `p256_point_add` → leaf `p256_point_add`. -/
@[rust_cmd_pattern]
def p256PointAddPattern : LowCTPattern where
  name      := "p256_point_add"
  fnHead    := ``p256_point_add
  arity     := 2
  towerType := .TBytes 64

/-! ## 4. P-256 tower-type abbreviations -/

/-- Tower type of a P-256 scalar. -/
def p256ScalarTowerType : TowerType := .TBytes 32

/-- Tower type of a P-256 affine point. -/
def p256PointTowerType : TowerType := .TBytes 64

private def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean P-256 kernel functions — the specs -/

/-- One MSM term: `t = p256_scalar_mul(k, P)`. -/
noncomputable def p256MsmTermLean (k : P256Scalar) (P : P256Point) : P256Point :=
  p256_scalar_mul k P

/-- ECDSA-P256-verify: `R' = u₁·G + u₂·Q`. -/
noncomputable def p256EcdsaVerifyLean
    (u1 : P256Scalar) (G : P256Point)
    (u2 : P256Scalar) (Q : P256Point) : P256Point :=
  p256_point_add (p256_scalar_mul u1 G) (p256_scalar_mul u2 Q)

/-! ## 6. Hand-built `LowCT` bodies -/

/-- The `LowCT` body for the per-term MSM. -/
def p256MsmTermBody : LowCT :=
  let k_l      := loc "k"        p256ScalarTowerType
  let P_l      := loc "P"        p256PointTowerType
  let result_l := loc "__result" p256PointTowerType
  .RSeq .RSkip
    (.RCall "p256_scalar_mul" result_l [k_l, P_l])

/-- `ReifiedFunc` bundle for the MSM-term kernel. -/
def p256MsmTermReified : ReifiedFunc :=
  { args    := [("k", p256ScalarTowerType),
                ("P", p256PointTowerType)]
    body    := p256MsmTermBody
    retName := "__result" }

/-- The `LowCT` body for ECDSA verify. -/
def p256EcdsaVerifyBody : LowCT :=
  let u1_l     := loc "u1"       p256ScalarTowerType
  let G_l      := loc "G"        p256PointTowerType
  let u2_l     := loc "u2"       p256ScalarTowerType
  let Q_l      := loc "Q"        p256PointTowerType
  let t1_l     := loc "t1"       p256PointTowerType
  let t2_l     := loc "t2"       p256PointTowerType
  let result_l := loc "__result" p256PointTowerType
  .RSeq (.RSeq (.RSeq .RSkip
    (.RCall "p256_scalar_mul" t1_l [u1_l, G_l]))
    (.RCall "p256_scalar_mul" t2_l [u2_l, Q_l]))
    (.RCall "p256_point_add" result_l [t1_l, t2_l])

/-- `ReifiedFunc` bundle for the ECDSA-verify kernel. -/
def p256EcdsaVerifyReified : ReifiedFunc :=
  { args    := [("u1", p256ScalarTowerType),
                ("G",  p256PointTowerType),
                ("u2", p256ScalarTowerType),
                ("Q",  p256PointTowerType)]
    body    := p256EcdsaVerifyBody
    retName := "__result" }

/-! ## 7. Inspection -/

#eval p256MsmTermReified.args.map Prod.fst              -- [k, P]
#eval p256MsmTermReified.args.length                    -- 2
#eval p256EcdsaVerifyReified.args.map Prod.fst          -- [u1, G, u2, Q]
#eval p256EcdsaVerifyReified.args.length                -- 4

end CatCrypt.Crypto.Jasmin.LowCTReflect
