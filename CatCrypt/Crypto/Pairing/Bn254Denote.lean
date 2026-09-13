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
`bn254_g1_add` leaf) are denoted here against an **abstract** leaf oracle
`leafSem : LeafSem`, threaded through the `DialectDenote jasminDialect` instance
`JasminDialect.jasminDenoteWith leafSem` (whose `extCall` arm consults `leafSem`
and whose every other arm delegates to `jasminDenote`).

* `bn254Oracle prims` — a concrete leaf oracle realising the BN254 group + pairing
  primitives (`prims.g1Add` / `prims.g1Mul` / `prims.g2Add` / `prims.g2Mul` on the
  G1/G2 signatures, `prims.pairing` on the pairing signature, `prims.fp12Mul` on
  the `fp12_mul` signature), with `bn254Oracle_ecAgrees` / `bn254Oracle_pairingAgrees`
  proving it satisfies the leaf agreements `EcLeafAgrees` / `PairingLeavesAgree`.
* `pairingCom_denoteWith` / `g1MsmTermCom_denoteWith` — the deployed kernels,
  evaluated with any leaf oracle realising the relevant primitives, compute
  `prims.pairing P Q` and `prims.g1Add acc (prims.g1Mul k P)`.
* `bn254LeafOracle` / `bn254LeafOracle_ecAgrees` / `bn254LeafOracle_pairingAgrees`
  — the leaf oracle for the deployed primitives and its agreements, named axioms
  (the leaf edges; a leaf proof or a jasmin/AUCurves bridge would establish them).
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

/-! ## 2. Value of the deployed `Com`s under a realising leaf oracle -/

/-- **The deployed single BN254 pairing, evaluated with a leaf oracle.** For a leaf
    oracle `leafSem` realising the pairing primitives, the deployed
    `Bn254Emit.pairingCom` — denoted through `jasminDenoteWith leafSem` — computes
    `prims.pairing P Q`. The single `extCall` arm unfolds to a `leafSem` call, and
    the pairing agreement rewrite closes it. -/
theorem pairingCom_denoteWith (leafSem : LeafSem) (prims : Bn254Primitives)
    (h : PairingLeavesAgree prims leafSem)
    (p : Fin G1SZ → BitVec 8) (q : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        Bn254Emit.pairingCom
        (.cons p (.cons q .nil))
      = prims.pairing p q := by
  rw [Bn254Emit.pairingCom_eq_shadow]
  obtain ⟨hP, _⟩ := h
  show leafSem pairingLeafName pairingArgTys gtRetTy (.cons p (.cons q .nil))
      = prims.pairing p q
  rw [hP (.cons p (.cons q .nil))]
  rfl

/-- **The deployed G1 MSM step, evaluated with a leaf oracle.** For a leaf oracle
    `leafSem` realising the G1 group primitives (`EcLeafAgrees prims leafSem`), the
    deployed `Bn254Emit.g1MsmTermCom` — denoted through `jasminDenoteWith leafSem`
    — computes `prims.g1Add acc (prims.g1Mul k P)` (the `scalarFold` step
    `acc + k·P`). The scalar-mul and point-add `extCall` arms each unfold to a
    `leafSem` call, and the two carried agreements close it. -/
theorem g1MsmTermCom_denoteWith (leafSem : LeafSem) (prims : Bn254Primitives)
    (h : EcLeafAgrees prims leafSem)
    (acc : Fin G1SZ → BitVec 8) (k : Fin FPSZ → BitVec 8) (P : Fin G1SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        Bn254Emit.g1MsmTermCom
        (.cons acc (.cons k (.cons P .nil)))
      = prims.g1Add acc (prims.g1Mul k P) := by
  rw [Bn254Emit.g1MsmTermCom_eq_shadow]
  obtain ⟨hAdd, hMul, _, _⟩ := h
  show leafSem g1AddLeafName g1AddArgTys g1RetTy
        (.cons acc (.cons (leafSem g1MulLeafName g1MulArgTys g1RetTy
                            (.cons k (.cons P .nil))) .nil))
      = prims.g1Add acc (prims.g1Mul k P)
  rw [hMul (.cons k (.cons P .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hAdd (.cons acc (.cons (prims.g1Mul k P) .nil))]
  rfl

/-! ## 3. The deployed leaf oracle + the kernels at that oracle -/

/-- `Bn254Primitives` is inhabited (all fields are functions into `BitVec 8`), so
    the deployed primitives can be introduced as an opaque constant. -/
instance : Inhabited Bn254Primitives :=
  ⟨{ g1Add := fun _ _ _ => 0, g1Mul := fun _ _ _ => 0, g2Add := fun _ _ _ => 0,
     g2Mul := fun _ _ _ => 0, pairing := fun _ _ _ => 0, fp12Mul := fun _ _ _ => 0 }⟩

/-- An abstract constant standing for the BN254 primitives the deployed code
    targets. Opaque — uninterpreted for proofs. -/
opaque bn254DeployedPrims : Bn254Primitives

/-- The leaf oracle for the deployed primitives,
    `bn254Oracle bn254DeployedPrims` sealed as `opaque`; the seal keeps the
    agreements below named hypotheses. -/
opaque bn254LeafOracle : LeafSem := bn254Oracle bn254DeployedPrims

/-- The leaf agreement: the deployed leaf oracle realises the BN254 G1/G2 group
    primitives. A named axiom. Establishing it means bridging the emitted leaf to
    the primitive spec — a leaf proof, or a jasmin/AUCurves bridge — which this
    file does not do. -/
axiom bn254LeafOracle_ecAgrees :
    EcLeafAgrees bn254DeployedPrims bn254LeafOracle

/-- The leaf agreement: the deployed leaf oracle realises the BN254 pairing
    primitives. A named axiom. Establishing it means bridging the emitted leaf to
    the primitive spec — a leaf proof, or a jasmin/AUCurves bridge — which this
    file does not do. -/
axiom bn254LeafOracle_pairingAgrees :
    PairingLeavesAgree bn254DeployedPrims bn254LeafOracle

/-- **The deployed single BN254 pairing at the deployed oracle.** The deployed
    `Bn254Emit.pairingCom`, denoted through `jasminDenoteWith bn254LeafOracle`,
    computes `pairing P Q` for the deployed primitives. The orchestration is
    Lean-proven; the only assumption is the leaf trust edge
    `bn254LeafOracle_pairingAgrees`. -/
theorem pairingCom_denote (p : Fin G1SZ → BitVec 8) (q : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bn254LeafOracle) _ _
        Bn254Emit.pairingCom
        (.cons p (.cons q .nil))
      = bn254DeployedPrims.pairing p q :=
  pairingCom_denoteWith bn254LeafOracle bn254DeployedPrims
    bn254LeafOracle_pairingAgrees p q

/-- **The deployed G1 MSM step at the deployed oracle.** The deployed
    `Bn254Emit.g1MsmTermCom`, denoted through `jasminDenoteWith bn254LeafOracle`,
    computes `g1Add acc (g1Mul k P)` for the deployed primitives. The
    orchestration is Lean-proven; the only assumption is the leaf trust edge
    `bn254LeafOracle_ecAgrees`. -/
theorem g1MsmTermCom_denote
    (acc : Fin G1SZ → BitVec 8) (k : Fin FPSZ → BitVec 8) (P : Fin G1SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bn254LeafOracle) _ _
        Bn254Emit.g1MsmTermCom
        (.cons acc (.cons k (.cons P .nil)))
      = bn254DeployedPrims.g1Add acc (bn254DeployedPrims.g1Mul k P) :=
  g1MsmTermCom_denoteWith bn254LeafOracle bn254DeployedPrims
    bn254LeafOracle_ecAgrees acc k P

end CatCrypt.Crypto.Pairing.Bn254Denote
