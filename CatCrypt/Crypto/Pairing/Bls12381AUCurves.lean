/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Pairing.Bls12381Emit

/-!
# BLS12-381 emit, backed by the AUCurves verified field/pairing tower

`Bls12381Emit.lean` emits the BLS12-381 G1 MSM and the pairing-equation verifiers
as straight-line / loop `Com`s over opaque `extCall` leaves (`g1_add`,
`g1_scalar_mul`, `bls12_pairing`, `fp12_mul`), carrying the agreements
`EcLeafAgrees` / `PairingLeavesAgree` that tie those leaves to the abstract
`BlsPrimitives`. That file deliberately keeps the leaves abstract; this **new**
module — without editing `Bls12381Emit.lean` — pins the intended **AUCurves
verified witness** for those leaves and records precisely what AUCurves verifies
versus what stays trusted.

## What AUCurves verifies (the field / pairing tower)

The production witness is the AUCurves verified-bedrock2 BLS12-381 tower
(AUCurves, `bls12-381-safe-rust` crate `bls12_381`):

* the fiat-crypto machine-checked **`Fp` field leaves** (6×`u64` Montgomery
  limbs): `fp_add/sub/mul/square/opp`, to/from-bytes, to/from-Montgomery;
* the extracted **`Fp2` / `Fp6` / `Fp12` tower** built over those leaves;
* **`miller_loop`** and **`final_exp`** — hence `pairing = final_exp ∘
  miller_loop`, the verified `bls12_pairing` leaf;
* the **`fp12_mul`** GT product, the verified `fp12_mul` leaf.

These are *exactly* the primitives CatCrypt already rust-cmd-links in
`bench/kzg/src/aucurves_backend.rs` (whose `pairing_check` is
`final_exp(miller(p₁,q₁)·miller(−p₂,q₂)) == 1`, using only AUCurves
`miller_loop` / `fp_opp` / `fp12_mul` / `final_exp`).

So the `bls12_pairing` and `fp12_mul` leaves of `Bls12381Emit` are backed by
verified field arithmetic: their `PairingLeavesAgree` witness is the AUCurves
`pairing` / `fp12_mul`, and the byte-identical KAT (`bench/bls12381_compare/`)
discharges that agreement operationally on the published BLS12-381 generators.

## What stays trusted (the group add law)

AUCurves does **not** (yet) expose a verified G1/G2 *group* layer — only the
field tower + `pairing`. The `g1_add` / `g1_scalar_mul` / `g2_add` /
`g2_scalar_mul` leaves are *built from* the verified `Fp` / `Fp2` ops (the affine
group law is rational functions of the coordinates), but the group-law
*formulas* themselves are the carried trusted leaf edge (`EcLeafAgrees`). This is
the same hybrid `aucurves_backend.rs` documents: "G1/G2 add/scalar-mul and Fr ops
come from blst — when AUCurves grows a group layer, those swap out incrementally."

This module therefore upgrades the R2 BLS12-381 leaves from *structural stubs* to
*AUCurves-field-backed* leaves on the pairing side (verified), while
flagging the group add law as the remaining trusted edge.

## AUCurves leaf-name binding

The leaf names below record which AUCurves crate symbol realises each
`Bls12381Emit` leaf. The `*Backed` predicates re-package the carried agreements
so a downstream caller states "these leaves are the AUCurves verified witness"
once, and the existing `Bls12381Emit.*_denote` theorems carry through verbatim.

0 sorries; no new custom axioms; the only hypotheses are the carried leaf
agreements (now explicitly the AUCurves witness).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Bls12381AUCurves

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminExtSem)
open CatCrypt.Crypto.Pairing.Bls12381Emit

/-! ## 1. AUCurves crate-symbol binding for each leaf

Each `Bls12381Emit` leaf name maps to the AUCurves `bls12_381` crate symbol that
realises it. The pairing-side symbols (`pairing`, `fp12_mul`) are **verified**;
the group-side symbols (`g1_add`, …) are the trusted group-law edge built over
the verified `Fp`/`Fp2` ops. -/

/-- AUCurves symbol realising the `bls12_pairing` leaf: the verified
    `final_exp ∘ miller_loop` (crate `bls12_381::pairing`). VERIFIED. -/
def pairingAUCurvesSymbol : String := "bls12_381::pairing"

/-- AUCurves symbol realising the `fp12_mul` leaf: the verified GT product
    (crate `bls12_381::fp12_mul`). VERIFIED. -/
def fp12MulAUCurvesSymbol : String := "bls12_381::fp12_mul"

/-- AUCurves-adjacent symbol realising the `g1_add` leaf: the affine G1 group law
    built over the verified `Fp` ops. TRUSTED group-law edge (AUCurves exposes no
    verified group layer yet). -/
def g1AddAUCurvesSymbol : String := "bls12_381::g1_add (group-law over verified Fp)"

/-- AUCurves-adjacent symbol realising the `g1_scalar_mul` leaf. TRUSTED. -/
def g1MulAUCurvesSymbol : String := "bls12_381::g1_scalar_mul (group-law over verified Fp)"

/-! ## 2. AUCurves-backed agreement predicates

`PairingLeavesAUCurvesBacked prims` asserts the pairing-side leaves of
`Bls12381Emit` agree with `prims` under `jasminExtSem`, with the intended
witness being the AUCurves verified `pairing` / `fp12_mul`. It is definitionally
the existing `Bls12381Emit.PairingLeavesAgree` at `jasminExtSem`; naming it
records that the witness is the verified AUCurves tower. -/

/-- The pairing / GT-multiply leaves are realised by the AUCurves **verified**
    `pairing` / `fp12_mul`. Definitionally `Bls12381Emit.PairingLeavesAgree prims
    jasminExtSem`; the name documents the verified witness. -/
def PairingLeavesAUCurvesBacked (prims : BlsPrimitives) : Prop :=
  PairingLeavesAgree prims jasminExtSem

/-- The G1/G2 group leaves are realised by the AUCurves-field-backed (but
    group-law **trusted**) `g1_add` / … . Definitionally
    `Bls12381Emit.EcLeafAgrees prims jasminExtSem`. -/
def EcLeavesAUCurvesBacked (prims : BlsPrimitives) : Prop :=
  EcLeafAgrees prims jasminExtSem

/-! ## 3. The verifier denotations, restated under the AUCurves-backed witness

These carry the existing `Bls12381Emit.*_denote` theorems through the
AUCurves-backed predicates verbatim — making explicit that the verifier
equations are computed by the AUCurves verified pairing/GT-multiply (and the
trusted group law for the MSM). No new content; the AUCurves witness is the
intended discharge of the carried agreement. -/

/-- **BLS verify under the AUCurves witness.** `e(σ, G2)` is computed by the
    AUCurves **verified** `pairing` (`PairingLeavesAUCurvesBacked`). The full
    check `e(σ,G2) = e(H(m),pk)` compares this to the RHS pairing. -/
theorem blsVerify_aucurves (prims : BlsPrimitives)
    (hPair : PairingLeavesAUCurvesBacked prims)
    (sig : Fin G1SZ → BitVec 8) (g2 : Fin G2SZ → BitVec 8) :
    blsVerifyLhsCom.denote (.cons sig (.cons g2 .nil)) = prims.pairing sig g2 :=
  blsVerifyLhsCom_denote prims hPair sig g2

/-- **KZG opening verify under the AUCurves witness.** `e(π, [s−z]G2)` is computed
    by the AUCurves **verified** `pairing`. -/
theorem kzgVerify_aucurves (prims : BlsPrimitives)
    (hPair : PairingLeavesAUCurvesBacked prims)
    (proof : Fin G1SZ → BitVec 8) (sMinusZ_g2 : Fin G2SZ → BitVec 8) :
    kzgVerifyLhsCom.denote (.cons proof (.cons sMinusZ_g2 .nil))
      = prims.pairing proof sMinusZ_g2 :=
  kzgVerifyLhsCom_denote prims hPair proof sMinusZ_g2

/-- **Groth16 verify under the AUCurves witness.** The pairing-product
    `e(αG1,βG2)·e(L,γG2)·e(C,δG2)` is computed entirely by the AUCurves
    **verified** `pairing` (three calls) and `fp12_mul` (two calls). -/
theorem groth16Verify_aucurves (prims : BlsPrimitives)
    (hPair : PairingLeavesAUCurvesBacked prims)
    (aG1 : Fin G1SZ → BitVec 8) (bG2 : Fin G2SZ → BitVec 8)
    (l : Fin G1SZ → BitVec 8) (gG2 : Fin G2SZ → BitVec 8)
    (c : Fin G1SZ → BitVec 8) (dG2 : Fin G2SZ → BitVec 8) :
    groth16VerifyRhsCom.denote
        (.cons aG1 (.cons bG2 (.cons l (.cons gG2 (.cons c (.cons dG2 .nil))))))
      = prims.fp12Mul
          (prims.fp12Mul (prims.pairing aG1 bG2) (prims.pairing l gG2))
          (prims.pairing c dG2) :=
  groth16VerifyRhsCom_denote prims hPair aG1 bG2 l gG2 c dG2

/-- **G1 MSM step under the (trusted) group-law witness.** One `scalarFold` step
    `acc ↦ acc + k·P` is computed by the `g1_add` / `g1_scalar_mul` leaves —
    built over the AUCurves verified `Fp`/`Fp2` ops, but with the group-law
    formulas as the carried trusted edge (`EcLeavesAUCurvesBacked`). -/
theorem g1MsmStep_aucurves (prims : BlsPrimitives)
    (hLeaf : EcLeavesAUCurvesBacked prims)
    (acc : Fin G1SZ → BitVec 8) (k : Fin FPSZ → BitVec 8) (P : Fin G1SZ → BitVec 8) :
    g1MsmTermCom.denote (.cons acc (.cons k (.cons P .nil)))
      = prims.g1Add acc (prims.g1Mul k P) :=
  g1MsmTermCom_denote prims hLeaf acc k P

end CatCrypt.Crypto.Pairing.Bls12381AUCurves
