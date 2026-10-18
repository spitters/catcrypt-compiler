/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Pairing.Bn254Emit

/-!
# EIP-197 pairing-product verifier: leaf-oracle-parametric denotation

The deployed `Bn254Emit.eip197VerifyCom` — the `buildOrchCom`-generated
straight-line `Com` of two `pairing` leaves accumulated by one `fp12_mul` leaf —
is denoted by `Bn254Emit.eip197VerifyCom_denote` against a leaf oracle
`leafSem : LeafSem` passed as a parameter, threaded through the
`DialectDenote jasminDialect` instance `JasminDialect.jasminDenoteWith leafSem`
(whose `extCall` arm consults `leafSem` and whose every other arm delegates to
`jasminDenote`). This module supplies the oracles that parameter is instantiated
at.

## Main results

* `pairingOracle prims` — a concrete leaf oracle realising the BN254 pairing-side
  primitives (`prims.pairing` on the pairing signature, `prims.fp12Mul` on the
  `fp12_mul` signature), with `pairingOracle_agrees` proving it satisfies the
  leaf agreement `PairingLeavesAgree`, so the hypothesis of
  `Bn254Emit.eip197VerifyCom_denote` is satisfiable for every `prims`.
* `eip197LeafOracle` / `eip197LeafOracle_agrees` — the leaf oracle for the
  deployed primitives, defined as `pairingOracle deployedPrims`, and its
  agreement, a theorem that holds by construction of the oracle. It relates the
  oracle to the primitives and says nothing about the emitted leaf code;
  `Bn254PairingTransport` derives the verifier's field value for any `prims`
  satisfying the AUCurves specs, stated as the hypothesis `RocqTransport prims`.
* `eip197VerifyCom_denote` — the deployed verifier at the deployed oracle.

The bespoke evaluator `eip197DenoteWith` (+ `eip197DenoteWith_eq`) gives the same
value directly over the known 3-phase schedule, independent of the `Com`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Eip197Denote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Pairing.Bn254Emit

/-! ## 1. A concrete leaf oracle realising the pairing primitives -/

/-- A leaf oracle realising the two BN254 pairing-side primitives: on the pairing
    signature (arg widths `64 / 128`, GT return width `384`) it returns
    `prims.pairing`, on the `fp12_mul` signature (arg widths `384 / 384`) it
    returns `prims.fp12Mul`, and it is `JasminTy.default` on any other leaf. This
    inhabits `LeafSem` — the shape a validated AUCurves binding takes. -/
def pairingOracle (prims : Bn254Primitives) : LeafSem :=
  fun _name argTys retTy =>
    match argTys, retTy with
    | [.stackArr 8 64, .stackArr 8 128], .stackArr 8 384 =>
        fun args => prims.pairing args.head args.tail.head
    | [.stackArr 8 384, .stackArr 8 384], .stackArr 8 384 =>
        fun args => prims.fp12Mul args.head args.tail.head
    | _, retTy => fun _ => JasminTy.default retTy

/-- `pairingOracle prims` realises the pairing primitives: it satisfies
    `PairingLeavesAgree prims` — by `rfl` in each component, because the
    pairing / `fp12_mul` signatures select the intended match arms. -/
theorem pairingOracle_agrees (prims : Bn254Primitives) :
    PairingLeavesAgree prims (pairingOracle prims) := by
  refine ⟨?_, ?_⟩
  · intro args; rfl
  · intro args; rfl

/-! ## 2. The deployed leaf oracle + the verifier at that oracle -/

/-- `Bn254Primitives` is inhabited (all fields are functions into `BitVec 8`), so
    the deployed primitives can be introduced as an opaque constant. -/
instance : Inhabited Bn254Primitives :=
  ⟨{ g1Add := fun _ _ _ => 0, g1Mul := fun _ _ _ => 0, g2Add := fun _ _ _ => 0,
     g2Mul := fun _ _ _ => 0, pairing := fun _ _ _ => 0, fp12Mul := fun _ _ _ => 0 }⟩

/-- An abstract constant standing for the BN254 primitives the deployed code
    targets. Opaque — uninterpreted for proofs. -/
opaque deployedPrims : Bn254Primitives

/-- The leaf oracle for the deployed primitives, `pairingOracle deployedPrims`. Opaque, so the kernel
    does not unfold it; `spec` carries its defining equation. -/
opaque eip197LeafOracle.spec : { o : LeafSem // o = pairingOracle deployedPrims } := ⟨_, rfl⟩

/-- The deployed leaf oracle, `pairingOracle deployedPrims`, read through the opaque `eip197LeafOracle.spec`. -/
def eip197LeafOracle : LeafSem := eip197LeafOracle.spec.val

/-- The deployed leaf oracle realises the pairing primitives. It holds by
    construction: the oracle is defined from the primitives. Relating the
    emitted leaves to the primitives is a separate statement, not made here. -/
theorem eip197LeafOracle_agrees :
    PairingLeavesAgree deployedPrims eip197LeafOracle := by
  rw [show eip197LeafOracle = pairingOracle deployedPrims from eip197LeafOracle.spec.property]
  exact pairingOracle_agrees _

/-- **The deployed EIP-197 verifier at the deployed oracle.** The deployed
    `Bn254Emit.eip197VerifyCom`, denoted through `jasminDenoteWith eip197LeafOracle`,
    computes `fp12Mul (pairing P₁ Q₁) (pairing P₂ Q₂)` for the deployed
    primitives: what the orchestration computes when each leaf computes its
    primitive. The statement carries no assumption; the leaf agreement
    `eip197LeafOracle_agrees` holds by construction of the oracle. -/
theorem eip197VerifyCom_denote
    (p1 : Fin G1SZ → BitVec 8) (q1 : Fin G2SZ → BitVec 8)
    (p2 : Fin G1SZ → BitVec 8) (q2 : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith eip197LeafOracle) _ _
        Bn254Emit.eip197VerifyCom
        (.cons p1 (.cons q1 (.cons p2 (.cons q2 .nil))))
      = deployedPrims.fp12Mul (deployedPrims.pairing p1 q1)
          (deployedPrims.pairing p2 q2) :=
  Bn254Emit.eip197VerifyCom_denote eip197LeafOracle deployedPrims eip197LeafOracle_agrees
    p1 q1 p2 q2

/-! ## 4. The schedule evaluator (same value, independent of the `Com`) -/

/-- The EIP-197 2-pair product `e(P₁,Q₁) · e(P₂,Q₂)` evaluated directly over the
    known 3-phase schedule against a leaf oracle `leafSem`: two `pairing` leaves
    fed to one `fp12_mul` leaf. -/
def eip197DenoteWith (leafSem : LeafSem)
    (p1 : Fin G1SZ → BitVec 8) (q1 : Fin G2SZ → BitVec 8)
    (p2 : Fin G1SZ → BitVec 8) (q2 : Fin G2SZ → BitVec 8) : Fin GTSZ → BitVec 8 :=
  leafSem fp12MulLeafName fp12MulArgTys gtRetTy
    (.cons (leafSem pairingLeafName pairingArgTys gtRetTy (.cons p1 (.cons q1 .nil)))
      (.cons (leafSem pairingLeafName pairingArgTys gtRetTy (.cons p2 (.cons q2 .nil)))
        .nil))

/-- The schedule evaluator, with a leaf oracle `leafSem` realising the pairing
    primitives, computes `prims.fp12Mul (prims.pairing P₁ Q₁) (prims.pairing P₂ Q₂)`. -/
theorem eip197DenoteWith_eq (leafSem : LeafSem) (prims : Bn254Primitives)
    (h : PairingLeavesAgree prims leafSem)
    (p1 : Fin G1SZ → BitVec 8) (q1 : Fin G2SZ → BitVec 8)
    (p2 : Fin G1SZ → BitVec 8) (q2 : Fin G2SZ → BitVec 8) :
    eip197DenoteWith leafSem p1 q1 p2 q2
      = prims.fp12Mul (prims.pairing p1 q1) (prims.pairing p2 q2) := by
  obtain ⟨hP, hM⟩ := h
  unfold eip197DenoteWith
  rw [hP (.cons p1 (.cons q1 .nil)), hP (.cons p2 (.cons q2 .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hM (.cons (prims.pairing p1 q1) (.cons (prims.pairing p2 q2) .nil))]
  simp only [HVector.head, HVector.tail]

end CatCrypt.Crypto.Pairing.Eip197Denote
