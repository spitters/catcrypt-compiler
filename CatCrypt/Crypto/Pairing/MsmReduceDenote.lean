/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Pairing.MsmReduce

/-!
# MSM-step EC leaves: leaf-oracle-parametric denotation

The deployed `buildOrchCom`-generated straight-line MSM-step kernel
`MsmReduce.msmTermCom` — one `ec_scalar_mul` leaf accumulated by one
`ec_point_add` leaf, the `scalarFold` body `acc ↦ acc + k_i·P_i` — is denoted
here against an **abstract** leaf oracle `leafSem : EcLeafSem`, threaded through
the `DialectDenote jasminDialect` instance `JasminDialect.jasminDenoteWith leafSem`
(whose `extCall` arm consults `leafSem` and whose every other arm delegates to
`jasminDenote`).

* `msmOracle prims` — a concrete leaf oracle realising the EC primitives
  (`prims.pointAdd` on the `ec_point_add` signature, `prims.scalarMul` on the
  `ec_scalar_mul` signature), with `msmOracle_agrees` proving it satisfies the
  leaf agreement `EcLeafAgrees`.
* `msmTermCom_denoteWith` — the deployed MSM step, evaluated with any leaf oracle
  realising the EC primitives, computes `prims.pointAdd acc (prims.scalarMul k P)`.
* `msmLeafOracle` / `msmLeafOracle_agrees` — the leaf oracle for the deployed
  primitives and its agreement, a named axiom (the leaf edge; a leaf proof or a
  jasmin/EC-reference bridge would establish it).
* `msmTermCom_denote` — the deployed MSM step at the deployed oracle.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.MsmReduceDenote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Pairing.MsmReduce

/-! ## 1. A concrete leaf oracle realising the EC primitives -/

/-- A leaf oracle realising the two EC primitives, dispatched by dialect signature:
    on the `ec_point_add` signature (two `2·WSZ`-byte points) it returns
    `prims.pointAdd`, on the `ec_scalar_mul` signature (a `WSZ`-byte scalar and a
    `2·WSZ`-byte point) it returns `prims.scalarMul`, and it is `JasminTy.default`
    on any other leaf. This inhabits `EcLeafSem` — the shape a validated
    schoolbook-EC binding takes. -/
def msmOracle (prims : EcPrimitives) : EcLeafSem :=
  fun _name argTys retTy =>
    match argTys, retTy with
    | [.stackArr 8 2, .stackArr 8 2], .stackArr 8 2 =>
        fun args => prims.pointAdd args.head args.tail.head
    | [.stackArr 8 1, .stackArr 8 2], .stackArr 8 2 =>
        fun args => prims.scalarMul args.head args.tail.head
    | _, retTy => fun _ => JasminTy.default retTy

/-- `msmOracle prims` realises the EC primitives: it satisfies `EcLeafAgrees prims`
    — by `rfl` in each component, because the `ec_point_add` / `ec_scalar_mul`
    signatures select the intended match arms. -/
theorem msmOracle_agrees (prims : EcPrimitives) :
    EcLeafAgrees prims (msmOracle prims) := by
  refine ⟨?_, ?_⟩ <;> (intro args; rfl)

/-! ## 2. Value of the deployed `Com` under a realising leaf oracle -/

/-- **The deployed MSM step, evaluated with a leaf oracle.** For a leaf oracle
    `leafSem` realising the EC primitives (`EcLeafAgrees prims leafSem`), the
    deployed `MsmReduce.msmTermCom` — denoted through `jasminDenoteWith leafSem` —
    computes `prims.pointAdd acc (prims.scalarMul k P)` (the running-accumulator
    step `acc + k·P` of the left-fold). The scalar-mul and point-add `extCall` arms
    each unfold to a `leafSem` call, and the two carried agreements close it. -/
theorem msmTermCom_denoteWith (leafSem : EcLeafSem) (prims : EcPrimitives)
    (h : EcLeafAgrees prims leafSem)
    (acc : Fin (2 * WSZ) → BitVec 8) (k : Fin WSZ → BitVec 8)
    (P : Fin (2 * WSZ) → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        MsmReduce.msmTermCom
        (.cons acc (.cons k (.cons P .nil)))
      = prims.pointAdd acc (prims.scalarMul k P) := by
  rw [MsmReduce.msmTermCom_eq_shadow]
  obtain ⟨hAdd, hMul⟩ := h
  show leafSem ecAddLeafName ecAddArgTys ecAddRetTy
        (.cons acc (.cons (leafSem ecMulLeafName ecMulArgTys ecMulRetTy
                            (.cons k (.cons P .nil))) .nil))
      = prims.pointAdd acc (prims.scalarMul k P)
  rw [hMul (.cons k (.cons P .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hAdd (.cons acc (.cons (prims.scalarMul k P) .nil))]
  simp only [HVector.head, HVector.tail]

/-! ## 3. The deployed leaf oracle + the kernel at that oracle -/

/-- `EcPrimitives` is inhabited (both fields are functions into `BitVec 8`), so the
    deployed primitives can be introduced as an opaque constant. -/
instance : Inhabited EcPrimitives :=
  ⟨{ pointAdd := fun _ _ _ => 0, scalarMul := fun _ _ _ => 0 }⟩

/-- An abstract constant standing for the EC primitives the deployed code targets.
    Opaque — uninterpreted for proofs. -/
opaque msmDeployedPrims : EcPrimitives

/-- The leaf oracle for the deployed primitives, `msmOracle msmDeployedPrims`
    sealed as `opaque`; the seal keeps the agreement below a named hypothesis. -/
opaque msmLeafOracle : EcLeafSem := msmOracle msmDeployedPrims

/-- The leaf agreement: the deployed leaf oracle realises the EC primitives. A
    named axiom. Establishing it means bridging the emitted leaf to the primitive
    spec — a leaf proof, or a jasmin/EC-reference bridge — which this file does
    not do. -/
axiom msmLeafOracle_agrees :
    EcLeafAgrees msmDeployedPrims msmLeafOracle

/-- **The deployed MSM step at the deployed oracle.** The deployed
    `MsmReduce.msmTermCom`, denoted through `jasminDenoteWith msmLeafOracle`,
    computes `pointAdd acc (scalarMul k P)` for the deployed primitives. The
    orchestration is Lean-proven; the only assumption is the leaf trust edge
    `msmLeafOracle_agrees`. -/
theorem msmTermCom_denote
    (acc : Fin (2 * WSZ) → BitVec 8) (k : Fin WSZ → BitVec 8)
    (P : Fin (2 * WSZ) → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith msmLeafOracle) _ _
        MsmReduce.msmTermCom
        (.cons acc (.cons k (.cons P .nil)))
      = msmDeployedPrims.pointAdd acc (msmDeployedPrims.scalarMul k P) :=
  msmTermCom_denoteWith msmLeafOracle msmDeployedPrims msmLeafOracle_agrees acc k P

end CatCrypt.Crypto.Pairing.MsmReduceDenote
