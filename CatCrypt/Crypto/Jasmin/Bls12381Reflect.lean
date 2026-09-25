/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# BLS12-381 reflect surface — G1 MSM + pairing-product kernels through the verified front

This file is the EC/pairing analogue of `FalconReflect.lean` / `UovReflect.lean`:
it adds BLS12-381 specific opaque surface types and `@[rust_cmd_pattern]`
registrations so that pure-Lean BLS12-381 G1 MSM orchestration, Groth16
pairing-product verification, and KZG opening verification can be lifted
through the verified compiler chain `LowCT → catCryptDialect → Com → jasmin`,
**without** editing `LowCTReflect.lean`'s `knownOps` table.

Three downstream drivers consume this surface:

* `bench/bls12381_compare/g1_msm_from_rustcmd.lean` — G1 MSM step (one scalar-mul
  + one G1-add); the orchestration produced by the verified front is the
  per-term step of `Σ_i k_i · P_i`.
* `bench/groth16_compare/verifier_from_rustcmd.lean` — Groth16 pairing-product
  `e(αG1,βG2) · e(L,γG2) · e(C,δG2)` (3 `bls12_pairing` leaves + 2 `fp12_mul`
  leaves, left-associated).
* `bench/kzg_compare/opening_verifier_from_rustcmd.lean` — KZG opening verifier
  LHS pairing (one `bls12_pairing` leaf).

## BLS12-381 width table

| Lean name               | Bytes | TowerType    | encodeTy (memref u64 limbs) |
|-------------------------|------:|--------------|----------------------------:|
| `BlsFp` (Fp scalar)     |    48 | `TBytes 48`  | 6                           |
| `BlsScalar` (Fr scalar) |    32 | `TBytes 32`  | 4                           |
| `BlsG1Point`            |    96 | `TBytes 96`  | 12                          |
| `BlsG2Point`            |   192 | `TBytes 192` | 24                          |
| `BlsFp12`               |   576 | `TBytes 576` | 72                          |

These widths match the string-templated emit (`bench/bls12381_compare/bls12381_emit.lean`)
and the AUCurves crate's on-wire layout.

## What's verified / what's trusted

The leaves are the AUCurves verified-bedrock2 BLS12-381 tower
(`bls12-381-safe-rust`): fiat-crypto `Fp` field leaves, the extracted
`Fp2/Fp6/Fp12` tower, `miller_loop`, `final_exp`, `fp12_mul`. AUCurves verifies
the FIELD/PAIRING tower; the G1/G2 group add law stays trusted (the same
hybrid `aucurves_backend.rs` records). The leaf-name binding in
`CatCrypt/Crypto/Pairing/Bls12381AUCurves.lean` documents which crate symbol
realises each leaf.

## Reflection→front gap (same as `UovReflect` / `MayoReflect`)

`reifyLowCT%` reads only `LowCTReflect.knownOps`, not the dynamic
`LowCTPattern` registry, so `reifyLowCT% g1MsmStepLean` would error. We
follow the established pattern: define the pure-Lean kernel for documentation,
register each leaf in the `LowCTPattern` registry via `@[rust_cmd_pattern]`,
then **hand-build the `LowCT`** the reifier *would* produce. Downstream
(`translate → cryptoDialectToJasminCom → emitAbiOrchRegPtr`) is the unmodified verified
front.

## LowCT-expressivity gap (documented)

`LowCT` is straight-line `RSeq`/`RCall`; the full MSM `Σ_{i=0}^{L-1} k_i·P_i`
loop is not expressible inside one `LowCT` body without a `for`-construct.
We emit ONE iteration of the MSM step (scalar-mul + G1-add) as the
compiler-traced body; the outer `for i = 0 to L` loop sits in the calling
.jazz alongside the include. This is the same scope as the string-templated
emit's `g1MsmLoopBody` — one body per iteration — but the body is the image
of a pure-Lean function under the verified front, not hand-typed string
text.

## References

* AUCurves: `bls12-381-safe-rust` crate (verified-bedrock2)
* `CatCrypt/Crypto/Pairing/Bls12381Emit.lean` — abstract `BlsPrimitives`,
  `EcLeafAgrees`, `PairingLeavesAgree`, `msmFold_eq_msm`, `groth16VerifyRhsCom_denote`
* `CatCrypt/Crypto/Pairing/Bls12381AUCurves.lean` — AUCurves-symbol binding
* `bench/bls12381_compare/bls12381_emit.lean` — string-templated emit
* `CatCrypt/Crypto/Jasmin/UovReflect.lean` — canonical leaf-shim reference
* Hax bridge: a BLS12-381 hax tree exists (`bls-hax/`, `EUDIW/`); the bridge
  is mechanizable but kept as a named hypothesis here (the AUCurves
  field/pairing leaves are the verified production witness; the hax bridge
  would tie the Rust spec to the same leaves).
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. Opaque BLS12-381 surface types

All BLS12-381 computations decompose into opaque on-wire byte blobs of the
widths above. We surface one opaque type per width; the reifier encodes
each as `TBytes n` (per the width table), and `encodeTy` lays them out as
`memref ((n+7)/8)`. -/

opaque BlsScalar.Impl : NonemptyType.{0}
/-- A BLS12-381 `Fr` scalar (32 bytes, little-endian Montgomery). -/
def BlsScalar : Type := BlsScalar.Impl.type
instance : Nonempty BlsScalar := BlsScalar.Impl.property
/-- An inhabitant. -/ noncomputable opaque BlsScalar.default : BlsScalar
noncomputable instance : Inhabited BlsScalar := ⟨BlsScalar.default⟩

opaque BlsG1Point.Impl : NonemptyType.{0}
/-- A BLS12-381 G1 point in the AUCurves on-wire layout (96 bytes:
    two `Fp` coordinates × 48 bytes). -/
def BlsG1Point : Type := BlsG1Point.Impl.type
instance : Nonempty BlsG1Point := BlsG1Point.Impl.property
/-- An inhabitant. -/ noncomputable opaque BlsG1Point.default : BlsG1Point
noncomputable instance : Inhabited BlsG1Point := ⟨BlsG1Point.default⟩

opaque BlsG2Point.Impl : NonemptyType.{0}
/-- A BLS12-381 G2 point in the AUCurves on-wire layout (192 bytes:
    two `Fp2` coordinates × 96 bytes). -/
def BlsG2Point : Type := BlsG2Point.Impl.type
instance : Nonempty BlsG2Point := BlsG2Point.Impl.property
/-- An inhabitant. -/ noncomputable opaque BlsG2Point.default : BlsG2Point
noncomputable instance : Inhabited BlsG2Point := ⟨BlsG2Point.default⟩

opaque BlsFp12.Impl : NonemptyType.{0}
/-- A BLS12-381 `Fp12` (GT) element (576 bytes: twelve `Fp` coordinates × 48
    bytes). The pairing output / `fp12_mul` operand. -/
def BlsFp12 : Type := BlsFp12.Impl.type
instance : Nonempty BlsFp12 := BlsFp12.Impl.property
/-- An inhabitant. -/ noncomputable opaque BlsFp12.default : BlsFp12
noncomputable instance : Inhabited BlsFp12 := ⟨BlsFp12.default⟩

/-! ## 2. BLS12-381 leaves (opaque constants = jasmin function symbols)

The five canonical leaves of the BLS12-381 pairing-based-verifier suite —
the same set carried by `Bls12381Emit.EcLeafAgrees` / `PairingLeavesAgree`. -/

/-- `bls_g1_scalar_mul k P = k · P` over the BLS12-381 G1 group. AUCurves-adjacent:
    the affine group law over the verified `Fp` ops (group-law trusted edge). -/
noncomputable opaque bls_g1_scalar_mul : BlsScalar → BlsG1Point → BlsG1Point

/-- `bls_g1_add P Q = P + Q` over the BLS12-381 G1 group. AUCurves-adjacent. -/
noncomputable opaque bls_g1_add : BlsG1Point → BlsG1Point → BlsG1Point

/-- `bls12_pairing P Q = e(P, Q) ∈ Fp12` — the BLS12-381 optimal-Ate pairing
    (`miller_loop` then `final_exp`). VERIFIED in AUCurves. -/
noncomputable opaque bls12_pairing : BlsG1Point → BlsG2Point → BlsFp12

/-- `bls_fp12_mul a b = a · b` over `Fp12` (the GT product). VERIFIED in AUCurves. -/
noncomputable opaque bls_fp12_mul : BlsFp12 → BlsFp12 → BlsFp12

/-! ## 3. `@[rust_cmd_pattern]` registrations

Each leaf is registered with the leaf name the .jazz include realises. The
`towerType` field gives the *destination* TowerType; the argument TowerTypes
come from the caller's `VarMap`. -/

/-- Register `bls_g1_scalar_mul` → leaf `bls_g1_scalar_mul`. -/
@[rust_cmd_pattern]
def blsG1ScalarMulPattern : LowCTPattern where
  name      := "bls_g1_scalar_mul"
  fnHead    := ``bls_g1_scalar_mul
  arity     := 2
  towerType := .TBytes 96   -- G1 point output

/-- Register `bls_g1_add` → leaf `bls_g1_add`. -/
@[rust_cmd_pattern]
def blsG1AddPattern : LowCTPattern where
  name      := "bls_g1_add"
  fnHead    := ``bls_g1_add
  arity     := 2
  towerType := .TBytes 96   -- G1 point output

/-- Register `bls12_pairing` → leaf `bls12_pairing`. -/
@[rust_cmd_pattern]
def bls12PairingPattern : LowCTPattern where
  name      := "bls12_pairing"
  fnHead    := ``bls12_pairing
  arity     := 2
  towerType := .TBytes 576  -- Fp12 output

/-- Register `bls_fp12_mul` → leaf `bls_fp12_mul`. -/
@[rust_cmd_pattern]
def blsFp12MulPattern : LowCTPattern where
  name      := "bls_fp12_mul"
  fnHead    := ``bls_fp12_mul
  arity     := 2
  towerType := .TBytes 576  -- Fp12 output

/-! ## 4. BLS12-381 tower-type abbreviations -/

/-- TowerType of a BLS12-381 `Fr` scalar. -/
def blsScalarTowerType : TowerType := .TBytes 32
/-- TowerType of a BLS12-381 G1 point. -/
def blsG1PointTowerType : TowerType := .TBytes 96
/-- TowerType of a BLS12-381 G2 point. -/
def blsG2PointTowerType : TowerType := .TBytes 192
/-- TowerType of a BLS12-381 `Fp12` element. -/
def blsFp12TowerType : TowerType := .TBytes 576

def locBls12381 (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-! ## 5. Pure-Lean BLS12-381 kernel functions — the specs

Documentation only; the reifier doesn't consult these at lift time
(see "Reflection→front gap" above). The hand-built `LowCT` bodies below
mirror these let-chains one-for-one. -/

/-- G1 MSM per-term step: `acc' = acc + k · P`. One scalar-mul leaf (`k · P` into
    a fresh term), one G1-add leaf (term into the accumulator). The outer
    `for i = 0 to L` loop iterating over `(k_i, P_i)` sits in the calling .jazz
    (the legacy `g1MsmLoopBody` shape).

    Denotes to one step of `scalarFold` over the G1 `AddCommMonoid`
    (`Bls12381Emit.msmFold_eq_msm`). -/
noncomputable def blsG1MsmStepLean (acc : BlsG1Point) (k : BlsScalar)
    (p : BlsG1Point) : BlsG1Point :=
  bls_g1_add acc (bls_g1_scalar_mul k p)

/-- Groth16 verifier RHS pairing product:
    `e1 = e(aG1, bG2)`, `e2 = e(lG1, gG2)`, `e3 = e(cG1, dG2)`, output =
    `(e1 · e2) · e3`. Three pairing leaves + two `fp12_mul` leaves, left-associated.

    Denotes to `fp12Mul (fp12Mul (e αG1 βG2) (e L γG2)) (e C δG2)`
    (`Bls12381Emit.groth16VerifyRhsCom_denote`). -/
noncomputable def groth16VerifierLean
    (aG1 : BlsG1Point) (bG2 : BlsG2Point)
    (lG1 : BlsG1Point) (gG2 : BlsG2Point)
    (cG1 : BlsG1Point) (dG2 : BlsG2Point) : BlsFp12 :=
  let e1 := bls12_pairing aG1 bG2
  let e2 := bls12_pairing lG1 gG2
  let e3 := bls12_pairing cG1 dG2
  bls_fp12_mul (bls_fp12_mul e1 e2) e3

/-- KZG opening verifier LHS pairing: one pairing leaf `e(P, Q)`. Denotes to
    the LHS of the KZG opening-pairing equation (`Bls12381Emit.kzgVerifyLhsCom_denote`). -/
noncomputable def kzgOpeningVerifierLean (p : BlsG1Point) (q : BlsG2Point) : BlsFp12 :=
  bls12_pairing p q

/-! ## 6. Hand-built `LowCT` bodies (the front-end input)

Each is one or more `RSeq RSkip (RCall leaf result [args])` — the same shape
`reifyLowCT%`'s final-op walker produces. The leaf names match the
`@[rust_cmd_pattern]` registrations above. -/

/-- The `LowCT` body the reifier *would* produce for `blsG1MsmStepLean`.
    Two-call chain: first scalar-mul into `__term`, then G1-add into `__result`. -/
def blsG1MsmStepBody : LowCT :=
  let acc_l    := locBls12381 "acc"      blsG1PointTowerType
  let k_l      := locBls12381 "k"        blsScalarTowerType
  let p_l      := locBls12381 "p"        blsG1PointTowerType
  let term_l   := locBls12381 "__term"   blsG1PointTowerType
  let result_l := locBls12381 "__result" blsG1PointTowerType
  .RSeq
    (.RSeq .RSkip
      (.RCall "bls_g1_scalar_mul" term_l [k_l, p_l]))
    (.RCall "bls_g1_add" result_l [acc_l, term_l])

/-- `ReifiedFunc` bundle for the G1 MSM step. -/
def blsG1MsmStepReified : ReifiedFunc :=
  { args    := [("acc", blsG1PointTowerType),
                ("k",   blsScalarTowerType),
                ("p",   blsG1PointTowerType)]
    body    := blsG1MsmStepBody
    retName := "__result" }

/-- The `LowCT` body for `groth16VerifierLean`. Five-call chain:
    3 pairings into `__e1`/`__e2`/`__e3`, then `__t = __e1 · __e2`, then
    `__result = __t · __e3`. -/
def groth16VerifierBody : LowCT :=
  let aG1_l    := locBls12381 "aG1"      blsG1PointTowerType
  let bG2_l    := locBls12381 "bG2"      blsG2PointTowerType
  let lG1_l    := locBls12381 "lG1"      blsG1PointTowerType
  let gG2_l    := locBls12381 "gG2"      blsG2PointTowerType
  let cG1_l    := locBls12381 "cG1"      blsG1PointTowerType
  let dG2_l    := locBls12381 "dG2"      blsG2PointTowerType
  let e1_l     := locBls12381 "__e1"     blsFp12TowerType
  let e2_l     := locBls12381 "__e2"     blsFp12TowerType
  let e3_l     := locBls12381 "__e3"     blsFp12TowerType
  let t_l      := locBls12381 "__t"      blsFp12TowerType
  let result_l := locBls12381 "__result" blsFp12TowerType
  .RSeq
    (.RSeq
      (.RSeq
        (.RSeq
          (.RSeq .RSkip
            (.RCall "bls12_pairing" e1_l [aG1_l, bG2_l]))
          (.RCall "bls12_pairing" e2_l [lG1_l, gG2_l]))
        (.RCall "bls12_pairing" e3_l [cG1_l, dG2_l]))
      (.RCall "bls_fp12_mul" t_l [e1_l, e2_l]))
    (.RCall "bls_fp12_mul" result_l [t_l, e3_l])

/-- `ReifiedFunc` bundle for the Groth16 verifier. -/
def groth16VerifierReified : ReifiedFunc :=
  { args    := [("aG1", blsG1PointTowerType), ("bG2", blsG2PointTowerType),
                ("lG1", blsG1PointTowerType), ("gG2", blsG2PointTowerType),
                ("cG1", blsG1PointTowerType), ("dG2", blsG2PointTowerType)]
    body    := groth16VerifierBody
    retName := "__result" }

/-- The `LowCT` body for `kzgOpeningVerifierLean`. Single pairing call. -/
def kzgOpeningVerifierBody : LowCT :=
  let p_l      := locBls12381 "p"        blsG1PointTowerType
  let q_l      := locBls12381 "q"        blsG2PointTowerType
  let result_l := locBls12381 "__result" blsFp12TowerType
  .RSeq .RSkip
    (.RCall "bls12_pairing" result_l [p_l, q_l])

/-- `ReifiedFunc` bundle for the KZG opening verifier LHS pairing. -/
def kzgOpeningVerifierReified : ReifiedFunc :=
  { args    := [("p", blsG1PointTowerType), ("q", blsG2PointTowerType)]
    body    := kzgOpeningVerifierBody
    retName := "__result" }

/-! ## 7. Inspection -/

#eval blsG1MsmStepReified.args.map Prod.fst              -- [acc, k, p]
#eval blsG1MsmStepReified.args.length                    -- 3
#eval blsG1MsmStepReified.retName                        -- __result
#eval groth16VerifierReified.args.length                 -- 6
#eval kzgOpeningVerifierReified.args.length              -- 2

end CatCrypt.Crypto.Jasmin.LowCTReflect
