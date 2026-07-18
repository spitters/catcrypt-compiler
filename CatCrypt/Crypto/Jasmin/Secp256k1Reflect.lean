/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# secp256k1 reflect surface — scalar-mul MSM + ECDSA-verify kernels via the
verified front

This file is the **secp256k1 analogue** of `FalconReflect.lean` / `UovReflect.lean`:
it adds secp256k1-specific opaque surface types (`Secp256k1Scalar`, `Secp256k1Point`)
and `@[rust_cmd_pattern]` registrations so that pure-Lean secp256k1 kernels
(scalar-mul, point-add, ECDSA-verify 2-term MSM) can be lifted through the
verified compiler chain `LowCT → CryptoSSA → Com → jasmin`, **without**
editing `LowCTReflect.lean`'s `knownOps` table.

## Two kernels (matches the legacy `bench/secp256k1_compare/secp256k1_emit.lean`)

* **`secp256k1MsmTermLean`** — one term of the scalar-mul MSM
  `Σ_i k_i · P_i`: `secp256k1_scalar_mul(k_i, P_i)` followed by
  `secp256k1_point_add(acc, t)`. The orchestration is what the verified
  front emits.

* **`secp256k1EcdsaVerifyLean`** — the recomputed point `R' = u₁·G + u₂·Q`
  in ECDSA verify: two `secp256k1_scalar_mul` leaves accumulated by one
  `secp256k1_point_add` leaf.

## Leaf surface (AUCurves verified-bedrock2 field tower)

The leaves are the secp256k1 group law built over the AUCurves
verified-bedrock2 field tower (`secp256k1-safe-rust`: fiat `fp_add/sub/mul/
square/opp` + Bernstein–Yang `fp_inv`). The Pairing.Secp256k1Emit theory
proves `MsmReduce.msm_eq_scalarFold` over the production secp256k1 group;
this file is the Tier A glue carrying that into the verified front-end.

| Lean axiom              | Leaf name (.jazz)         | TowerType    |
|------------------------|---------------------------|--------------|
| `secp256k1_scalar_mul`  | `secp256k1_scalar_mul`    | `TBytes 64`  |
| `secp256k1_point_add`   | `secp256k1_point_add`     | `TBytes 64`  |

## LowCT-expressivity gap (documented)

The full MSM `Σ_{i=0}^{L-1} k_i·P_i` is a `for i = 0 to L: acc += k_i·P_i`
nested loop — `LowCT` is straight-line `RSeq`/`RCall` only, so the outer
`for` over `i` is not directly expressible. We use the same approach as
`MayoReflect` / `UovReflect`: register the per-term leaf bodies, and emit
the straight-line one-iteration body through the verified front. The
multi-term orchestration (the `for i = 0 to L` wrapper) is the natural
extension once `RFor` lands in `LowCT` (out of scope here — same gap as
the MAYO/UOV per-component projection).

## Reflection→front gap (same pattern as MayoReflect/UovReflect)

`reifyLowCT%` reads only `LowCTReflect.knownOps`, not the dynamic
`LowCTPattern` registry, so `reifyLowCT% secp256k1MsmTermLean` would
error. We follow the established pattern: register each leaf in the
`LowCTPattern` registry via `@[rust_cmd_pattern]`, then **hand-build the
`LowCT`** the reifier *would* produce. Downstream (`translate →
cprogToJasminCom → emitAbiOrchRegPtr`) is the unmodified verified front.

## References

* SEC 2: Recommended Elliptic Curve Domain Parameters, §2.4.1 (secp256k1)
* `bench/secp256k1_compare/secp256k1_emit.lean` — legacy Tier C emit (kept
  as out-of-chain reference, superseded by `scalar_mul_from_rustcmd.lean`)
* `CatCrypt/Crypto/Pairing/Secp256k1Emit.lean` — `msmFold_eq_msm`,
  `ecdsaVerifyCom_denote`, the production-group reduction this file glues
  into the verified front
* `CatCrypt/Crypto/Jasmin/UovReflect.lean` — sibling reference for the
  hand-built-body around `@[rust_cmd_pattern]` registration
-/

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque secp256k1 surface types

A secp256k1 field element `Fp` is 4 little-endian `u64` limbs = 32 bytes,
matching the fiat-crypto `[u64;4]` Montgomery layout. On the wire an
affine **EC point** is `(x ‖ y)`, two `Fp`s = 64 bytes; a **scalar** (an
`Fn` element mod the group order `n`) is also 32 bytes. -/

/-- A secp256k1 scalar (an element of `Fn`, `Fn = ZMod n` where `n` is the
    secp256k1 group order). 32 bytes on the wire. Opaque on the Lean side;
    the leaf `secp256k1_scalar_mul` reads 32 bytes for the scalar input.
    The reifier encodes this as `TBytes 32` (memref 4 u64-limbs). -/
axiom Secp256k1Scalar : Type
/-- Axiomatic inhabitant. -/ axiom Secp256k1Scalar.default : Secp256k1Scalar
noncomputable instance : Inhabited Secp256k1Scalar := ⟨Secp256k1Scalar.default⟩

/-- A secp256k1 affine point `(x ‖ y)`. 64 bytes on the wire (two 32-byte
    field elements). Opaque; the leaves implement the group law over the
    AUCurves verified field tower. The reifier encodes this as `TBytes 64`
    (memref 8 u64-limbs). -/
axiom Secp256k1Point : Type
/-- Axiomatic inhabitant. -/ axiom Secp256k1Point.default : Secp256k1Point
noncomputable instance : Inhabited Secp256k1Point := ⟨Secp256k1Point.default⟩

/-! ## 2. secp256k1 leaves (axioms = opaque jasmin function symbols)

The two leaves are the secp256k1 group law primitives. The trusted
edge: the **field arith** (`fp_add/sub/mul/square/inv/opp`) is AUCurves
verified-CT; the **group law** (scalar-mul, point-add) is the standard
short-Weierstrass formulas applied to those verified field ops, kept as
the trusted leaf edge (same honest stance as `Bls12381Emit`). -/

/-- secp256k1 scalar multiplication `R = k · P` (standard double-and-add /
    Montgomery ladder). Opaque here — the jasmin shim issues the actual
    ladder over the AUCurves-verified field leaves. -/
axiom secp256k1_scalar_mul : Secp256k1Scalar → Secp256k1Point → Secp256k1Point

/-- secp256k1 point addition `R = P + Q` (the standard short-Weierstrass
    affine point-add formula, with the special-case logic for `P = Q`,
    `P = -Q`, and the point-at-infinity). Opaque; the jasmin shim
    implements the formula over the AUCurves-verified field leaves. -/
axiom secp256k1_point_add : Secp256k1Point → Secp256k1Point → Secp256k1Point

/-! ## 3. `@[rust_cmd_pattern]` registrations -/

/-- Register `secp256k1_scalar_mul` → leaf `secp256k1_scalar_mul`. Result
    is a 64-byte point. -/
@[rust_cmd_pattern]
def secp256k1ScalarMulPattern : LowCTPattern where
  name      := "secp256k1_scalar_mul"
  fnHead    := ``secp256k1_scalar_mul
  arity     := 2
  towerType := .TBytes 64   -- 64-byte result point

/-- Register `secp256k1_point_add` → leaf `secp256k1_point_add`. Result is
    a 64-byte point. -/
@[rust_cmd_pattern]
def secp256k1PointAddPattern : LowCTPattern where
  name      := "secp256k1_point_add"
  fnHead    := ``secp256k1_point_add
  arity     := 2
  towerType := .TBytes 64   -- 64-byte result point

/-! ## 4. secp256k1 tower-type abbreviations -/

/-- Tower type of a secp256k1 scalar (`Fn` element). -/
def secp256k1ScalarTowerType : TowerType := .TBytes 32

/-- Tower type of a secp256k1 affine point. -/
def secp256k1PointTowerType : TowerType := .TBytes 64

private def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean secp256k1 kernel functions — the specs -/

/-- One MSM term: compute `t = secp256k1_scalar_mul(k, P)`. (The full
    `for`-loop wrapper around `acc ↦ acc + k_i·P_i` is the outer Tier-A
    scope; this body covers one fold step, the leaf the reifier sees.) -/
noncomputable def secp256k1MsmTermLean (k : Secp256k1Scalar) (P : Secp256k1Point) :
    Secp256k1Point :=
  secp256k1_scalar_mul k P

/-- ECDSA-verify recomputed point `R' = u₁·G + u₂·Q`. Two scalar-mul
    leaves + one point-add leaf — exactly the legacy emit shape. -/
noncomputable def secp256k1EcdsaVerifyLean
    (u1 : Secp256k1Scalar) (G : Secp256k1Point)
    (u2 : Secp256k1Scalar) (Q : Secp256k1Point) : Secp256k1Point :=
  secp256k1_point_add (secp256k1_scalar_mul u1 G) (secp256k1_scalar_mul u2 Q)

/-! ## 6. Hand-built `LowCT` bodies (the front-end input)

Each is a chain of `RSeq` / `RCall` mirroring the let-chain in the pure-Lean
spec above. The leaf names match the `@[rust_cmd_pattern]` registrations. -/

/-- The `LowCT` body the reifier *would* produce for the per-term MSM
    `t = secp256k1_scalar_mul(k, P)`. -/
def secp256k1MsmTermBody : LowCT :=
  let k_l      := loc "k"        secp256k1ScalarTowerType
  let P_l      := loc "P"        secp256k1PointTowerType
  let result_l := loc "__result" secp256k1PointTowerType
  .RSeq .RSkip
    (.RCall "secp256k1_scalar_mul" result_l [k_l, P_l])

/-- `ReifiedFunc` bundle for the MSM-term kernel. -/
def secp256k1MsmTermReified : ReifiedFunc :=
  { args    := [("k", secp256k1ScalarTowerType),
                ("P", secp256k1PointTowerType)]
    body    := secp256k1MsmTermBody
    retName := "__result" }

/-- The `LowCT` body for the ECDSA-verify `R' = u₁·G + u₂·Q` chain:

    ```
    t1 = secp256k1_scalar_mul(u1, G)
    t2 = secp256k1_scalar_mul(u2, Q)
    __result = secp256k1_point_add(t1, t2)
    ```
-/
def secp256k1EcdsaVerifyBody : LowCT :=
  let u1_l     := loc "u1"       secp256k1ScalarTowerType
  let G_l      := loc "G"        secp256k1PointTowerType
  let u2_l     := loc "u2"       secp256k1ScalarTowerType
  let Q_l      := loc "Q"        secp256k1PointTowerType
  let t1_l     := loc "t1"       secp256k1PointTowerType
  let t2_l     := loc "t2"       secp256k1PointTowerType
  let result_l := loc "__result" secp256k1PointTowerType
  .RSeq (.RSeq (.RSeq .RSkip
    (.RCall "secp256k1_scalar_mul" t1_l [u1_l, G_l]))
    (.RCall "secp256k1_scalar_mul" t2_l [u2_l, Q_l]))
    (.RCall "secp256k1_point_add" result_l [t1_l, t2_l])

/-- `ReifiedFunc` bundle for the ECDSA-verify kernel. -/
def secp256k1EcdsaVerifyReified : ReifiedFunc :=
  { args    := [("u1", secp256k1ScalarTowerType),
                ("G",  secp256k1PointTowerType),
                ("u2", secp256k1ScalarTowerType),
                ("Q",  secp256k1PointTowerType)]
    body    := secp256k1EcdsaVerifyBody
    retName := "__result" }

/-! ## 7. Inspection -/

#eval secp256k1MsmTermReified.args.map Prod.fst              -- [k, P]
#eval secp256k1MsmTermReified.args.length                    -- 2
#eval secp256k1MsmTermReified.retName                        -- __result
#eval secp256k1EcdsaVerifyReified.args.map Prod.fst          -- [u1, G, u2, Q]
#eval secp256k1EcdsaVerifyReified.args.length                -- 4

end CatCrypt.Crypto.Jasmin.LowCTReflect
