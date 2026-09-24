/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Pairing.Bls12_377Emit

/-!
# BLS12-377 emit: leaf-oracle-parametric denotation of the eight deployed `Com`s

The eight deployed BLS12-377 orchestration `Com`s of `Pairing.Bls12_377Emit` —
the five `Fp` field kernels (`fieldAddCom` / `fieldSubCom` / `fieldMulCom` /
`fieldSquareCom` / `fieldInvCom`), the single-pairing kernel `pairingCom`, the
GT product `fp12MulCom`, and the pairing-product verifier `pairingProductCom` —
are denoted by the `Bls12_377Emit.<name>Com_denote` theorems against a leaf oracle
`leafSem : LeafSem` passed as a parameter, threaded through the
`DialectDenote jasminDialect` instance `JasminDialect.jasminDenoteWith leafSem`
(whose `extCall` arm consults `leafSem` and whose every other arm delegates to
`jasminDenote`). Each computes the abstract-primitive value: a field op
`op(x, y)`, a pairing `e(P, Q)`, a GT product `a · b`, or the pairing product
`e(P₁,Q₁) · e(P₂,Q₂)`. This module supplies the oracles that parameter is
instantiated at.

* `bls377Oracle prims` — a concrete leaf oracle realising all seven BLS12-377
  leaves (the five field ops, the pairing, and the GT product) from a
  `Bls377Primitives` interface, with `bls377Oracle_fieldAgrees` /
  `bls377Oracle_pairingAgrees` proving it satisfies the field and pairing leaf
  agreement bundles, so the hypotheses of the `Bls12_377Emit` denotation
  theorems are satisfiable for every `prims`.
* `bls377Prims` / `bls377LeafOracle` / `bls377LeafOracle_agrees` — the deployed
  primitives, the leaf oracle for them (defined as `bls377Oracle bls377Prims`),
  and the leaf agreement bundle, a theorem that holds by construction of the
  oracle. It relates the oracle to the primitives and says nothing about the
  emitted leaf code.
* `<name>Com_denote` — each deployed `Com` at the deployed oracle.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Bls12_377Denote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Pairing.Bls12_377Emit

/-! ## 1. A concrete leaf oracle realising the BLS12-377 primitives -/

/-- A leaf oracle realising the seven BLS12-377 leaves from a `Bls377Primitives`
    interface. It dispatches on the leaf name and signature: the three binary
    `Fp` ops (`bls377_add` / `bls377_sub` / `bls377_mul`, arg widths `48 / 48`,
    result width `48`) return `prims.fieldAdd` / `prims.fieldSub` / `prims.fieldMul`;
    the two unary `Fp` ops (`bls377_square` / `bls377_inv`, arg width `48`) return
    `prims.fieldSquare` / `prims.fieldInv`; the pairing (`bls377_pairing`, arg
    widths `96 / 192`, GT width `576`) returns `prims.pairing`; the GT product
    (`bls377_Fp12_mul`, arg widths `576 / 576`) returns `prims.fp12Mul`; and it is
    `JasminTy.default` on any other leaf. This inhabits `LeafSem` — the shape a
    validated AUCurves binding takes. -/
def bls377Oracle (prims : Bls377Primitives) : LeafSem :=
  fun name argTys retTy =>
    match name, argTys, retTy with
    | "bls377_add", [.stackArr 8 48, .stackArr 8 48], .stackArr 8 48 =>
        fun args => prims.fieldAdd args.head args.tail.head
    | "bls377_sub", [.stackArr 8 48, .stackArr 8 48], .stackArr 8 48 =>
        fun args => prims.fieldSub args.head args.tail.head
    | "bls377_mul", [.stackArr 8 48, .stackArr 8 48], .stackArr 8 48 =>
        fun args => prims.fieldMul args.head args.tail.head
    | "bls377_square", [.stackArr 8 48], .stackArr 8 48 =>
        fun args => prims.fieldSquare args.head
    | "bls377_inv", [.stackArr 8 48], .stackArr 8 48 =>
        fun args => prims.fieldInv args.head
    | "bls377_pairing", [.stackArr 8 96, .stackArr 8 192], .stackArr 8 576 =>
        fun args => prims.pairing args.head args.tail.head
    | "bls377_Fp12_mul", [.stackArr 8 576, .stackArr 8 576], .stackArr 8 576 =>
        fun args => prims.fp12Mul args.head args.tail.head
    | _, _, retTy => fun _ => JasminTy.default retTy

/-- `bls377Oracle prims` realises the five `Fp` field primitives: it satisfies
    `Bls377FieldLeavesAgree prims` — by `rfl` in each component, because the
    field-leaf name + signature selects the intended match arm. -/
theorem bls377Oracle_fieldAgrees (prims : Bls377Primitives) :
    Bls377FieldLeavesAgree prims (bls377Oracle prims) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro args; rfl)

/-- `bls377Oracle prims` realises the pairing and GT-product primitives: it
    satisfies `Bls377PairingLeavesAgree prims` — by `rfl` in each component. -/
theorem bls377Oracle_pairingAgrees (prims : Bls377Primitives) :
    Bls377PairingLeavesAgree prims (bls377Oracle prims) := by
  refine ⟨?_, ?_⟩ <;> (intro args; rfl)

/-! ## 2. The deployed leaf oracle + each `Com` at that oracle -/

/-- `Bls377Primitives` is inhabited (all fields are functions into `Fin _ → BitVec 8`,
    which has a zero element), so the deployed primitives can be introduced as an
    opaque constant. -/
instance : Inhabited Bls377Primitives :=
  ⟨{ fieldAdd := fun _ _ => 0, fieldSub := fun _ _ => 0, fieldMul := fun _ _ => 0,
     fieldSquare := fun _ => 0, fieldInv := fun _ => 0,
     pairing := fun _ _ => 0, fp12Mul := fun _ _ => 0 }⟩

/-- An abstract constant standing for the BLS12-377 primitives the deployed code
    targets. Opaque — uninterpreted for proofs. -/
opaque bls377Prims : Bls377Primitives

/-- The leaf oracle for the deployed primitives, `bls377Oracle bls377Prims`. Opaque, so the kernel
    does not unfold it; `spec` carries its defining equation. -/
opaque bls377LeafOracle.spec : { o : LeafSem // o = bls377Oracle bls377Prims } := ⟨_, rfl⟩

/-- The deployed leaf oracle, `bls377Oracle bls377Prims`, read through the opaque `bls377LeafOracle.spec`. -/
def bls377LeafOracle : LeafSem := bls377LeafOracle.spec.val

/-- The deployed leaf oracle realises the BLS12-377 field and pairing primitives. It holds by
    construction: the oracle is defined from the primitives. Relating the
    emitted leaves to the primitives is a separate statement, not made here. -/
theorem bls377LeafOracle_agrees :
    Bls377FieldLeavesAgree bls377Prims bls377LeafOracle ∧
    Bls377PairingLeavesAgree bls377Prims bls377LeafOracle := by
  rw [show bls377LeafOracle = bls377Oracle bls377Prims from bls377LeafOracle.spec.property]
  exact ⟨bls377Oracle_fieldAgrees _, bls377Oracle_pairingAgrees _⟩

/-- **The deployed field-add kernel at the deployed oracle.** Computes
    `bls377Prims.fieldAdd x y`: what the orchestration computes when the leaf
    computes its primitive. The statement carries no assumption; the leaf
    agreement `bls377LeafOracle_agrees` holds by construction of the oracle. -/
theorem fieldAddCom_denote (x y : Fin FPSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bls377LeafOracle) _ _
        Bls12_377Emit.fieldAddCom (.cons x (.cons y .nil))
      = bls377Prims.fieldAdd x y :=
  Bls12_377Emit.fieldAddCom_denote bls377LeafOracle bls377Prims bls377LeafOracle_agrees.1 x y

/-- **The deployed field-sub kernel at the deployed oracle.** Computes
    `bls377Prims.fieldSub x y`. -/
theorem fieldSubCom_denote (x y : Fin FPSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bls377LeafOracle) _ _
        Bls12_377Emit.fieldSubCom (.cons x (.cons y .nil))
      = bls377Prims.fieldSub x y :=
  Bls12_377Emit.fieldSubCom_denote bls377LeafOracle bls377Prims bls377LeafOracle_agrees.1 x y

/-- **The deployed field-multiply kernel at the deployed oracle.** Computes
    `bls377Prims.fieldMul x y`. -/
theorem fieldMulCom_denote (x y : Fin FPSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bls377LeafOracle) _ _
        Bls12_377Emit.fieldMulCom (.cons x (.cons y .nil))
      = bls377Prims.fieldMul x y :=
  Bls12_377Emit.fieldMulCom_denote bls377LeafOracle bls377Prims bls377LeafOracle_agrees.1 x y

/-- **The deployed field-square kernel at the deployed oracle.** Computes
    `bls377Prims.fieldSquare x`. -/
theorem fieldSquareCom_denote (x : Fin FPSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bls377LeafOracle) _ _
        Bls12_377Emit.fieldSquareCom (.cons x .nil)
      = bls377Prims.fieldSquare x :=
  Bls12_377Emit.fieldSquareCom_denote bls377LeafOracle bls377Prims bls377LeafOracle_agrees.1 x

/-- **The deployed field-inverse kernel at the deployed oracle.** Computes
    `bls377Prims.fieldInv x`. -/
theorem fieldInvCom_denote (x : Fin FPSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bls377LeafOracle) _ _
        Bls12_377Emit.fieldInvCom (.cons x .nil)
      = bls377Prims.fieldInv x :=
  Bls12_377Emit.fieldInvCom_denote bls377LeafOracle bls377Prims bls377LeafOracle_agrees.1 x

/-- **The deployed single-pairing kernel at the deployed oracle.** Computes
    `bls377Prims.pairing P Q`. -/
theorem pairingCom_denote (p : Fin G1SZ → BitVec 8) (q : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bls377LeafOracle) _ _
        Bls12_377Emit.pairingCom (.cons p (.cons q .nil))
      = bls377Prims.pairing p q :=
  Bls12_377Emit.pairingCom_denote bls377LeafOracle bls377Prims bls377LeafOracle_agrees.2 p q

/-- **The deployed GT-product kernel at the deployed oracle.** Computes
    `bls377Prims.fp12Mul a b`. -/
theorem fp12MulCom_denote (a b : Fin GTSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bls377LeafOracle) _ _
        Bls12_377Emit.fp12MulCom (.cons a (.cons b .nil))
      = bls377Prims.fp12Mul a b :=
  Bls12_377Emit.fp12MulCom_denote bls377LeafOracle bls377Prims bls377LeafOracle_agrees.2 a b

/-- **The deployed pairing-product verifier at the deployed oracle.** Computes
    `bls377Prims.fp12Mul (bls377Prims.pairing P₁ Q₁) (bls377Prims.pairing P₂ Q₂)`
    for the deployed primitives: what the orchestration computes when each leaf
    computes its primitive. The statement carries no assumption; the leaf
    agreement `bls377LeafOracle_agrees` holds by construction of the oracle. -/
theorem pairingProductCom_denote
    (p1 : Fin G1SZ → BitVec 8) (q1 : Fin G2SZ → BitVec 8)
    (p2 : Fin G1SZ → BitVec 8) (q2 : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bls377LeafOracle) _ _
        Bls12_377Emit.pairingProductCom
        (.cons p1 (.cons q1 (.cons p2 (.cons q2 .nil))))
      = bls377Prims.fp12Mul (bls377Prims.pairing p1 q1) (bls377Prims.pairing p2 q2) :=
  Bls12_377Emit.pairingProductCom_denote bls377LeafOracle bls377Prims bls377LeafOracle_agrees.2
    p1 q1 p2 q2

end CatCrypt.Crypto.Pairing.Bls12_377Denote
