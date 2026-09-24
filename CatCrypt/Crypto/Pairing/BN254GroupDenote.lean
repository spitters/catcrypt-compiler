/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Pairing.BN254GroupEmit

/-!
# BN254 `G1` point-add field-leaf `Com`s: leaf-oracle-parametric denotation

The deployed BN254 `G1` short-Weierstrass point-add kernels
`BN254GroupEmit.lamCom` (the slope `(Qy − Py)·(Qx − Px)⁻¹`),
`BN254GroupEmit.bn254AddxCom` (`x₃ = λ·λ − x₁ − x₂`), and
`BN254GroupEmit.bn254AddyCom` (`y₃ = λ·(x₁ − x₃) − y₁`) — each a
`buildOrchCom`-generated straight-line `Com` over the `fp_*` field leaves — are
denoted by `BN254GroupEmit.lamCom_denoteWith` / `bn254AddxCom_denoteWith` /
`bn254AddyCom_denoteWith` against a leaf oracle `leafSem : LeafSem` passed as a
parameter, threaded through the `DialectDenote jasminDialect` instance
`JasminDialect.jasminDenoteWith leafSem` (whose `extCall` arm consults `leafSem`
and whose every other arm delegates to `jasminDenote`). This module supplies the
oracles that parameter is instantiated at.

* `bn254FieldOracle prims` — a concrete leaf oracle realising the four BN254
  base-field primitives (`prims.mul`/`prims.sub`/`prims.add` on the binary
  signature, `prims.inv` on the unary signature), dispatched by leaf name and
  signature, with `bn254FieldOracle_agrees` proving it satisfies the leaf
  agreement `FieldLeafAgrees`, so the agreement hypothesis of the
  `BN254GroupEmit` denotation theorems is satisfiable for every `prims`.
* `bn254GroupLeafOracle` / `bn254GroupLeafOracle_agrees` — the leaf oracle for
  the deployed primitives, defined as `bn254FieldOracle bn254GroupDeployedPrims`,
  and its agreement, a theorem that holds by construction of the oracle. It
  relates the oracle to the primitives and says nothing about the emitted `fp_*`
  leaf code; `FieldLeafBridge_BLS_BN254` proves the agreement for a concrete
  codec-based primitive whose operations are the base-field operations.
* `lamCom_denote` / `bn254AddxCom_denote` / `bn254AddyCom_denote` — the deployed
  kernels at the deployed oracle.

`bn254FieldOracle prims` is an abstract constant standing for the field
primitives the deployed code targets; the coordinate realization over `FpBN254`
(via `wireToFp`, under `FieldRealizes`) is the separate `BN254GroupEmit.*Com_denote`
layer, stated for the same leaf-model parameter.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.BN254GroupDenote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Pairing.BN254GroupEmit

/-! ## 1. A concrete leaf oracle realising the BN254 base-field primitives -/

/-- A leaf oracle realising the four BN254 base-field primitives, dispatched by
    leaf name and signature: on the binary signature the `bn254_fp_mul` /
    `bn254_fp_sub` / `bn254_fp_add` names return `prims.mul` / `prims.sub` /
    `prims.add`, on the unary signature the `bn254_invert_divstep_sat` name
    returns `prims.inv`, and it is `JasminTy.default` on any other leaf. This
    inhabits `LeafSem` — the shape a validated AUCurves field binding takes. -/
def bn254FieldOracle (prims : FieldPrimitives) : LeafSem :=
  fun name argTys retTy =>
    match name, argTys, retTy with
    | "bn254_fp_mul", [.stackArr 8 32, .stackArr 8 32], .stackArr 8 32 =>
        fun args => prims.mul args.head args.tail.head
    | "bn254_fp_sub", [.stackArr 8 32, .stackArr 8 32], .stackArr 8 32 =>
        fun args => prims.sub args.head args.tail.head
    | "bn254_fp_add", [.stackArr 8 32, .stackArr 8 32], .stackArr 8 32 =>
        fun args => prims.add args.head args.tail.head
    | "bn254_invert_divstep_sat", [.stackArr 8 32], .stackArr 8 32 =>
        fun args => prims.inv args.head
    | _, _, retTy => fun _ => JasminTy.default retTy

/-- `bn254FieldOracle prims` realises the base-field primitives: it satisfies
    `FieldLeafAgrees prims` — by `rfl` in each component, because the `fp_*` leaf
    names + signatures select the intended match arms. -/
theorem bn254FieldOracle_agrees (prims : FieldPrimitives) :
    FieldLeafAgrees prims (bn254FieldOracle prims) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro args; rfl)

/-! ## 2. The deployed leaf oracle + the kernels at that oracle -/

/-- `FieldPrimitives` is inhabited (all fields are functions into `FpWire`), so
    the deployed primitives can be introduced as an opaque constant. -/
instance : Inhabited FieldPrimitives :=
  ⟨{ mul := fun _ _ => 0, sub := fun _ _ => 0, add := fun _ _ => 0, inv := fun _ => 0 }⟩

/-- An abstract constant standing for the BN254 base-field primitives the
    deployed code targets. Opaque — uninterpreted for proofs. -/
opaque bn254GroupDeployedPrims : FieldPrimitives

/-- The leaf oracle for the deployed primitives, `bn254FieldOracle bn254GroupDeployedPrims`. Opaque, so the kernel
    does not unfold it; `spec` carries its defining equation. -/
opaque bn254GroupLeafOracle.spec : { o : LeafSem // o = bn254FieldOracle bn254GroupDeployedPrims } := ⟨_, rfl⟩

/-- The deployed leaf oracle, `bn254FieldOracle bn254GroupDeployedPrims`, read through the opaque `bn254GroupLeafOracle.spec`. -/
def bn254GroupLeafOracle : LeafSem := bn254GroupLeafOracle.spec.val

/-- The deployed leaf oracle realises the BN254 base-field primitives. It holds by
    construction: the oracle is defined from the primitives. Relating the
    emitted leaves to the primitives is a separate statement, not made here. -/
theorem bn254GroupLeafOracle_agrees :
    FieldLeafAgrees bn254GroupDeployedPrims bn254GroupLeafOracle := by
  rw [show bn254GroupLeafOracle = bn254FieldOracle bn254GroupDeployedPrims from bn254GroupLeafOracle.spec.property]
  exact bn254FieldOracle_agrees _

/-- **The deployed slope kernel at the deployed oracle.** The deployed
    `BN254GroupEmit.lamCom`, denoted through `jasminDenoteWith bn254GroupLeafOracle`,
    computes `mul (sub Qy Py) (inv (sub Qx Px))` for the deployed primitives:
    what the orchestration computes when each leaf computes its primitive. The
    statement carries no assumption; the leaf agreement
    `bn254GroupLeafOracle_agrees` holds by construction of the oracle. -/
theorem lamCom_denote (Px Py Qx Qy : FpWire) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bn254GroupLeafOracle) _ _
        BN254GroupEmit.lamCom
        (.cons Px (.cons Py (.cons Qx (.cons Qy .nil))))
      = bn254GroupDeployedPrims.mul (bn254GroupDeployedPrims.sub Qy Py)
          (bn254GroupDeployedPrims.inv (bn254GroupDeployedPrims.sub Qx Px)) :=
  lamCom_denoteWith bn254GroupLeafOracle bn254GroupDeployedPrims
    bn254GroupLeafOracle_agrees Px Py Qx Qy

/-- **The deployed `x₃` kernel at the deployed oracle.** The deployed
    `BN254GroupEmit.bn254AddxCom`, denoted through
    `jasminDenoteWith bn254GroupLeafOracle`, computes `sub (sub (mul lam lam) Px) Qx`
    for the deployed primitives. The statement carries no assumption; the leaf
    agreement `bn254GroupLeafOracle_agrees` holds by construction of the oracle. -/
theorem bn254AddxCom_denote (lam Px Qx : FpWire) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bn254GroupLeafOracle) _ _
        BN254GroupEmit.bn254AddxCom
        (.cons lam (.cons Px (.cons Qx .nil)))
      = bn254GroupDeployedPrims.sub
          (bn254GroupDeployedPrims.sub (bn254GroupDeployedPrims.mul lam lam) Px) Qx :=
  bn254AddxCom_denoteWith bn254GroupLeafOracle bn254GroupDeployedPrims
    bn254GroupLeafOracle_agrees lam Px Qx

/-- **The deployed `y₃` kernel at the deployed oracle.** The deployed
    `BN254GroupEmit.bn254AddyCom`, denoted through
    `jasminDenoteWith bn254GroupLeafOracle`, computes `sub (mul lam (sub Px Rx)) Py`
    for the deployed primitives. The statement carries no assumption; the leaf
    agreement `bn254GroupLeafOracle_agrees` holds by construction of the oracle. -/
theorem bn254AddyCom_denote (lam Px Rx Py : FpWire) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bn254GroupLeafOracle) _ _
        BN254GroupEmit.bn254AddyCom
        (.cons lam (.cons Px (.cons Rx (.cons Py .nil))))
      = bn254GroupDeployedPrims.sub
          (bn254GroupDeployedPrims.mul lam (bn254GroupDeployedPrims.sub Px Rx)) Py :=
  bn254AddyCom_denoteWith bn254GroupLeafOracle bn254GroupDeployedPrims
    bn254GroupLeafOracle_agrees lam Px Rx Py

end CatCrypt.Crypto.Pairing.BN254GroupDenote
