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
denoted here against an **abstract** leaf oracle `leafSem : LeafSem`, threaded
through the `DialectDenote jasminDialect` instance
`JasminDialect.jasminDenoteWith leafSem` (whose `extCall` arm consults `leafSem`
and whose every other arm delegates to `jasminDenote`).

* `bn254FieldOracle prims` — a concrete leaf oracle realising the four BN254
  base-field primitives (`prims.mul`/`prims.sub`/`prims.add` on the binary
  signature, `prims.inv` on the unary signature), dispatched by leaf name and
  signature, with `bn254FieldOracle_agrees` proving it satisfies the leaf
  agreement `FieldLeafAgrees`.
* `lamCom_denoteWith` / `bn254AddxCom_denoteWith` / `bn254AddyCom_denoteWith` —
  the deployed kernels, evaluated with any leaf oracle realising the field
  primitives, compute the corresponding `fp_*`-primitive composition.
* `bn254GroupLeafOracle` / `bn254GroupLeafOracle_agrees` — the leaf oracle for
  the deployed primitives and its agreement, a named axiom (the leaf edge;
  establishing it means bridging the emitted `fp_*` leaves to the primitive spec
  — a leaf proof or a jasmin/AUCurves bridge).
* `lamCom_denote` / `bn254AddxCom_denote` / `bn254AddyCom_denote` — the deployed
  kernels at the deployed oracle.

`bn254FieldOracle prims` is an abstract constant standing for the field
primitives the deployed code targets; the coordinate realization over `FpBN254`
(via `wireToFp`) is the separate `BN254GroupEmit.*Com_denote` layer.
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

/-! ## 2. Value of the deployed `Com`s under a realising leaf oracle -/

/-- **The deployed slope kernel, evaluated with a leaf oracle.** For a leaf
    oracle `leafSem` realising the base-field primitives, the deployed
    `BN254GroupEmit.lamCom` — denoted through `jasminDenoteWith leafSem` —
    computes the `fp_*` composition `mul (sub Qy Py) (inv (sub Qx Px))`. The four
    field `extCall` arms each unfold to a `leafSem` call, and the carried
    agreements close it. -/
theorem lamCom_denoteWith (leafSem : LeafSem) (prims : FieldPrimitives)
    (h : FieldLeafAgrees prims leafSem)
    (Px Py Qx Qy : FpWire) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        BN254GroupEmit.lamCom
        (.cons Px (.cons Py (.cons Qx (.cons Qy .nil))))
      = prims.mul (prims.sub Qy Py) (prims.inv (prims.sub Qx Px)) := by
  rw [BN254GroupEmit.lamCom_eq_shadow]
  obtain ⟨hMul, hSub, _hAdd, hInv⟩ := h
  show leafSem mulLeafName binArgTys feRetTy
        (.cons (leafSem subLeafName binArgTys feRetTy (.cons Qy (.cons Py .nil)))
          (.cons (leafSem invLeafName unArgTys feRetTy
            (.cons (leafSem subLeafName binArgTys feRetTy
              (.cons Qx (.cons Px .nil))) .nil)) .nil))
      = prims.mul (prims.sub Qy Py) (prims.inv (prims.sub Qx Px))
  rw [hSub (.cons Qy (.cons Py .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hSub (.cons Qx (.cons Px .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hInv (.cons (prims.sub Qx Px) .nil)]
  simp only [HVector.head]
  rw [hMul (.cons (prims.sub Qy Py) (.cons (prims.inv (prims.sub Qx Px)) .nil))]
  simp only [HVector.head, HVector.tail]

/-- **The deployed `x₃` kernel, evaluated with a leaf oracle.** For a leaf oracle
    `leafSem` realising the base-field primitives, the deployed
    `BN254GroupEmit.bn254AddxCom` — denoted through `jasminDenoteWith leafSem` —
    computes `sub (sub (mul lam lam) Px) Qx` (the `x₃ = λ·λ − x₁ − x₂` chain). -/
theorem bn254AddxCom_denoteWith (leafSem : LeafSem) (prims : FieldPrimitives)
    (h : FieldLeafAgrees prims leafSem)
    (lam Px Qx : FpWire) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        BN254GroupEmit.bn254AddxCom
        (.cons lam (.cons Px (.cons Qx .nil)))
      = prims.sub (prims.sub (prims.mul lam lam) Px) Qx := by
  rw [BN254GroupEmit.bn254AddxCom_eq_shadow]
  obtain ⟨hMul, hSub, _hAdd, _⟩ := h
  show leafSem subLeafName binArgTys feRetTy
        (.cons (leafSem subLeafName binArgTys feRetTy
          (.cons (leafSem mulLeafName binArgTys feRetTy (.cons lam (.cons lam .nil)))
            (.cons Px .nil))) (.cons Qx .nil))
      = prims.sub (prims.sub (prims.mul lam lam) Px) Qx
  rw [hMul (.cons lam (.cons lam .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hSub (.cons (prims.mul lam lam) (.cons Px .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hSub (.cons (prims.sub (prims.mul lam lam) Px) (.cons Qx .nil))]
  simp only [HVector.head, HVector.tail]

/-- **The deployed `y₃` kernel, evaluated with a leaf oracle.** For a leaf oracle
    `leafSem` realising the base-field primitives, the deployed
    `BN254GroupEmit.bn254AddyCom` — denoted through `jasminDenoteWith leafSem` —
    computes `sub (mul lam (sub Px Rx)) Py` (the `y₃ = λ·(x₁ − x₃) − y₁` chain). -/
theorem bn254AddyCom_denoteWith (leafSem : LeafSem) (prims : FieldPrimitives)
    (h : FieldLeafAgrees prims leafSem)
    (lam Px Rx Py : FpWire) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        BN254GroupEmit.bn254AddyCom
        (.cons lam (.cons Px (.cons Rx (.cons Py .nil))))
      = prims.sub (prims.mul lam (prims.sub Px Rx)) Py := by
  rw [BN254GroupEmit.bn254AddyCom_eq_shadow]
  obtain ⟨hMul, hSub, _hAdd, _⟩ := h
  show leafSem subLeafName binArgTys feRetTy
        (.cons (leafSem mulLeafName binArgTys feRetTy
          (.cons lam (.cons (leafSem subLeafName binArgTys feRetTy
            (.cons Px (.cons Rx .nil))) .nil))) (.cons Py .nil))
      = prims.sub (prims.mul lam (prims.sub Px Rx)) Py
  rw [hSub (.cons Px (.cons Rx .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hMul (.cons lam (.cons (prims.sub Px Rx) .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hSub (.cons (prims.mul lam (prims.sub Px Rx)) (.cons Py .nil))]
  simp only [HVector.head, HVector.tail]

/-! ## 3. The deployed leaf oracle + the kernels at that oracle -/

/-- `FieldPrimitives` is inhabited (all fields are functions into `FpWire`), so
    the deployed primitives can be introduced as an opaque constant. -/
instance : Inhabited FieldPrimitives :=
  ⟨{ mul := fun _ _ => 0, sub := fun _ _ => 0, add := fun _ _ => 0, inv := fun _ => 0 }⟩

/-- An abstract constant standing for the BN254 base-field primitives the
    deployed code targets. Opaque — uninterpreted for proofs. -/
opaque bn254GroupDeployedPrims : FieldPrimitives

/-- The leaf oracle for the deployed primitives,
    `bn254FieldOracle bn254GroupDeployedPrims` sealed as `opaque`; the seal keeps
    the agreement below a named hypothesis. -/
opaque bn254GroupLeafOracle : LeafSem := bn254FieldOracle bn254GroupDeployedPrims

/-- The leaf agreement: the deployed leaf oracle realises the BN254 base-field
    primitives. A named axiom. Establishing it means bridging the emitted `fp_*`
    leaves to the primitive spec — a leaf proof, or a jasmin/AUCurves bridge —
    which this file does not do. -/
axiom bn254GroupLeafOracle_agrees :
    FieldLeafAgrees bn254GroupDeployedPrims bn254GroupLeafOracle

/-- **The deployed slope kernel at the deployed oracle.** The deployed
    `BN254GroupEmit.lamCom`, denoted through `jasminDenoteWith bn254GroupLeafOracle`,
    computes `mul (sub Qy Py) (inv (sub Qx Px))` for the deployed primitives. The
    orchestration is Lean-proven; the only assumption is the leaf trust edge
    `bn254GroupLeafOracle_agrees`. -/
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
    for the deployed primitives, on the leaf trust edge
    `bn254GroupLeafOracle_agrees`. -/
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
    for the deployed primitives, on the leaf trust edge
    `bn254GroupLeafOracle_agrees`. -/
theorem bn254AddyCom_denote (lam Px Rx Py : FpWire) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bn254GroupLeafOracle) _ _
        BN254GroupEmit.bn254AddyCom
        (.cons lam (.cons Px (.cons Rx (.cons Py .nil))))
      = bn254GroupDeployedPrims.sub
          (bn254GroupDeployedPrims.mul lam (bn254GroupDeployedPrims.sub Px Rx)) Py :=
  bn254AddyCom_denoteWith bn254GroupLeafOracle bn254GroupDeployedPrims
    bn254GroupLeafOracle_agrees lam Px Rx Py

end CatCrypt.Crypto.Pairing.BN254GroupDenote
