/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Pairing.Bn254Emit

/-!
# BN254 pairing + G1-MSM leaves: leaf-oracle-parametric denotation

The deployed BN254 `buildOrchCom`-generated straight-line kernels
`Bn254Emit.pairingCom` (a single `bn254_pairing` leaf) and
`Bn254Emit.g1MsmTermCom` (one `bn254_g1_scalar_mul` leaf accumulated by one
`bn254_g1_add` leaf) are denoted by `Bn254Emit.pairingCom_denote` /
`Bn254Emit.g1MsmTermCom_denote` against a leaf oracle `leafSem : LeafSem` passed as
a parameter, threaded through the `DialectDenote jasminDialect` instance
`JasminDialect.jasminDenoteWith leafSem` (whose `extCall` arm consults `leafSem`
and whose every other arm delegates to `jasminDenote`). This module supplies the
oracles that parameter is instantiated at.

* `bn254Oracle prims` — a concrete leaf oracle realising the BN254 group + pairing
  primitives (`prims.g1Add` / `prims.g1Mul` / `prims.g2Add` / `prims.g2Mul` on the
  G1/G2 signatures, `prims.pairing` on the pairing signature, `prims.fp12Mul` on
  the `fp12_mul` signature), with `bn254Oracle_ecAgrees` / `bn254Oracle_pairingAgrees`
  proving it satisfies the leaf agreements `EcLeafAgrees` / `PairingLeavesAgree`,
  so the hypotheses of the `Bn254Emit` denotation theorems are satisfiable for
  every `prims`.
* `bn254LeafOracle` / `bn254LeafOracle_ecAgrees` / `bn254LeafOracle_pairingAgrees`
  — the leaf oracle for the deployed primitives, defined as
  `bn254Oracle bn254DeployedPrims`, and its agreements, theorems that hold by
  construction of the oracle. They relate the oracle to the primitives and say
  nothing about the emitted leaf code; `BN254G1LeafBridge` proves the byte-level
  projective `g1_add` spec equal to the encoded affine group law.
* `pairingCom_denote` / `g1MsmTermCom_denote` — the deployed kernels at the
  deployed oracle.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Bn254Denote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Pairing.Bn254Emit

/-! ## 1. A concrete leaf oracle realising the BN254 group + pairing primitives -/

/-- A leaf oracle realising the six BN254 primitives, dispatched by dialect
    signature: on the G1 add / scalar-mul signatures it returns `prims.g1Add` /
    `prims.g1Mul`, on the G2 add / scalar-mul signatures `prims.g2Add` /
    `prims.g2Mul`, on the pairing signature `prims.pairing`, on the `fp12_mul`
    signature `prims.fp12Mul`, and it is `JasminTy.default` on any other leaf. This
    inhabits `LeafSem` — the shape a validated AUCurves binding takes. -/
def bn254Oracle (prims : Bn254Primitives) : LeafSem :=
  fun _name argTys retTy =>
    match argTys, retTy with
    | [.stackArr 8 64, .stackArr 8 64], .stackArr 8 64 =>
        fun args => prims.g1Add args.head args.tail.head
    | [.stackArr 8 32, .stackArr 8 64], .stackArr 8 64 =>
        fun args => prims.g1Mul args.head args.tail.head
    | [.stackArr 8 128, .stackArr 8 128], .stackArr 8 128 =>
        fun args => prims.g2Add args.head args.tail.head
    | [.stackArr 8 32, .stackArr 8 128], .stackArr 8 128 =>
        fun args => prims.g2Mul args.head args.tail.head
    | [.stackArr 8 64, .stackArr 8 128], .stackArr 8 384 =>
        fun args => prims.pairing args.head args.tail.head
    | [.stackArr 8 384, .stackArr 8 384], .stackArr 8 384 =>
        fun args => prims.fp12Mul args.head args.tail.head
    | _, retTy => fun _ => JasminTy.default retTy

/-- `bn254Oracle prims` realises the G1/G2 group primitives: it satisfies
    `EcLeafAgrees prims` — by `rfl` in each component, because the four group
    signatures select the intended match arms. -/
theorem bn254Oracle_ecAgrees (prims : Bn254Primitives) :
    EcLeafAgrees prims (bn254Oracle prims) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro args; rfl)

/-- `bn254Oracle prims` realises the pairing primitives: it satisfies
    `PairingLeavesAgree prims` — by `rfl` in each component, because the pairing /
    `fp12_mul` signatures select the intended match arms. -/
theorem bn254Oracle_pairingAgrees (prims : Bn254Primitives) :
    PairingLeavesAgree prims (bn254Oracle prims) := by
  refine ⟨?_, ?_⟩ <;> (intro args; rfl)

/-! ## 2. The deployed leaf oracle + the kernels at that oracle -/

/-- `Bn254Primitives` is inhabited (all fields are functions into `BitVec 8`), so
    the deployed primitives can be introduced as an opaque constant. -/
instance : Inhabited Bn254Primitives :=
  ⟨{ g1Add := fun _ _ _ => 0, g1Mul := fun _ _ _ => 0, g2Add := fun _ _ _ => 0,
     g2Mul := fun _ _ _ => 0, pairing := fun _ _ _ => 0, fp12Mul := fun _ _ _ => 0 }⟩

/-- An abstract constant standing for the BN254 primitives the deployed code
    targets. Opaque — uninterpreted for proofs. -/
opaque bn254DeployedPrims : Bn254Primitives

/-- The leaf oracle for the deployed primitives, `bn254Oracle bn254DeployedPrims`. Opaque, so the kernel
    does not unfold it; `spec` carries its defining equation. -/
opaque bn254LeafOracle.spec : { o : LeafSem // o = bn254Oracle bn254DeployedPrims } := ⟨_, rfl⟩

/-- The deployed leaf oracle, `bn254Oracle bn254DeployedPrims`, read through the opaque `bn254LeafOracle.spec`. -/
def bn254LeafOracle : LeafSem := bn254LeafOracle.spec.val

/-- The deployed leaf oracle realises the BN254 G1/G2 group primitives. It holds by
    construction: the oracle is defined from the primitives. Relating the
    emitted leaves to the primitives is a separate statement, not made here. -/
theorem bn254LeafOracle_ecAgrees :
    EcLeafAgrees bn254DeployedPrims bn254LeafOracle := by
  rw [show bn254LeafOracle = bn254Oracle bn254DeployedPrims from bn254LeafOracle.spec.property]
  exact bn254Oracle_ecAgrees _

/-- The deployed leaf oracle realises the BN254 pairing primitives. It holds by
    construction: the oracle is defined from the primitives. Relating the
    emitted leaves to the primitives is a separate statement, not made here. -/
theorem bn254LeafOracle_pairingAgrees :
    PairingLeavesAgree bn254DeployedPrims bn254LeafOracle := by
  rw [show bn254LeafOracle = bn254Oracle bn254DeployedPrims from bn254LeafOracle.spec.property]
  exact bn254Oracle_pairingAgrees _

/-- **The deployed single BN254 pairing at the deployed oracle.** The deployed
    `Bn254Emit.pairingCom`, denoted through `jasminDenoteWith bn254LeafOracle`,
    computes `pairing P Q` for the deployed primitives: what the orchestration
    computes when the leaf computes its primitive. The statement carries no
    assumption; the leaf agreement `bn254LeafOracle_pairingAgrees` holds by
    construction of the oracle. -/
theorem pairingCom_denote (p : Fin G1SZ → BitVec 8) (q : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bn254LeafOracle) _ _
        Bn254Emit.pairingCom
        (.cons p (.cons q .nil))
      = bn254DeployedPrims.pairing p q :=
  Bn254Emit.pairingCom_denote bn254LeafOracle bn254DeployedPrims
    bn254LeafOracle_pairingAgrees p q

/-- **The deployed G1 MSM step at the deployed oracle.** The deployed
    `Bn254Emit.g1MsmTermCom`, denoted through `jasminDenoteWith bn254LeafOracle`,
    computes `g1Add acc (g1Mul k P)` for the deployed primitives: what the
    orchestration computes when each leaf computes its primitive. The statement
    carries no assumption; the leaf agreement `bn254LeafOracle_ecAgrees` holds by
    construction of the oracle. -/
theorem g1MsmTermCom_denote
    (acc : Fin G1SZ → BitVec 8) (k : Fin FPSZ → BitVec 8) (P : Fin G1SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bn254LeafOracle) _ _
        Bn254Emit.g1MsmTermCom
        (.cons acc (.cons k (.cons P .nil)))
      = bn254DeployedPrims.g1Add acc (bn254DeployedPrims.g1Mul k P) :=
  Bn254Emit.g1MsmTermCom_denote bn254LeafOracle bn254DeployedPrims
    bn254LeafOracle_ecAgrees acc k P

end CatCrypt.Crypto.Pairing.Bn254Denote
