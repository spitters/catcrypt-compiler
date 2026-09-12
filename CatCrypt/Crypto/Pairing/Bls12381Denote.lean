/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Pairing.Bls12381Emit

/-!
# BLS12-381 emit: leaf-oracle-parametric denotation of the deployed verifier `Com`s

The four deployed BLS12-381 orchestration `Com`s — the G1 MSM step
(`Bls12381Emit.g1MsmTermCom`), the single-pairing BLS/KZG verifier LHS
(`Bls12381Emit.blsVerifyLhsCom`, `Bls12381Emit.kzgVerifyLhsCom`), and the
three-pairing Groth16 verifier RHS product (`Bls12381Emit.groth16VerifyRhsCom`) —
are denoted here against an **abstract** leaf oracle `leafSem : LeafSem`, threaded
through the `DialectDenote jasminDialect` instance
`JasminDialect.jasminDenoteWith leafSem` (whose `extCall` arm consults `leafSem`
and whose every other arm delegates to `jasminDenote`). This is the two-level
compiler design of `Pairing.Eip197Denote`, at the BLS12-381 leaves.

* `bls12381Oracle prims` — a concrete leaf oracle realising every BLS12-381
  primitive the four `Com`s use (G1/G2 point-add + scalar-mul, the pairing, the
  GT product), with `bls12381Oracle_ecAgrees` / `bls12381Oracle_pairingAgrees`
  proving it satisfies the leaf agreements `EcLeafAgrees` / `PairingLeavesAgree`.
* `*Com_denoteWith` — each deployed `Com`, evaluated with any leaf oracle
  realising the primitives it uses, computes the abstract value (a G1 MSM step,
  a pairing, or the left-associated three-pairing product).
* `bls12381LeafOracle` / `bls12381LeafOracle_ecAgrees` /
  `bls12381LeafOracle_pairingAgrees` — the leaf oracle for the deployed
  primitives and its agreements, named axioms (the leaf edges; a leaf proof or a
  jasmin/AUCurves bridge would establish them).
* `*Com_denote` — each deployed `Com` at the deployed oracle.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Bls12381Denote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Pairing.Bls12381Emit

/-! ## 1. A concrete leaf oracle realising the BLS12-381 primitives -/

/-- A leaf oracle realising the six BLS12-381 primitives, selecting each by its
    dialect signature (arg widths / return width, all distinct): G1 point-add
    (`96 / 96 → 96`), G1 scalar-mul (`48 / 96 → 96`), G2 point-add
    (`192 / 192 → 192`), G2 scalar-mul (`48 / 192 → 192`), the pairing
    (`96 / 192 → 576`), and the GT product (`576 / 576 → 576`). It is
    `JasminTy.default` on any other leaf. This inhabits `LeafSem` — the shape a
    validated AUCurves group/pairing binding takes. -/
def bls12381Oracle (prims : BlsPrimitives) : LeafSem :=
  fun _name argTys retTy =>
    match argTys, retTy with
    | [.stackArr 8 96, .stackArr 8 96], .stackArr 8 96 =>
        fun args => prims.g1Add args.head args.tail.head
    | [.stackArr 8 48, .stackArr 8 96], .stackArr 8 96 =>
        fun args => prims.g1Mul args.head args.tail.head
    | [.stackArr 8 192, .stackArr 8 192], .stackArr 8 192 =>
        fun args => prims.g2Add args.head args.tail.head
    | [.stackArr 8 48, .stackArr 8 192], .stackArr 8 192 =>
        fun args => prims.g2Mul args.head args.tail.head
    | [.stackArr 8 96, .stackArr 8 192], .stackArr 8 576 =>
        fun args => prims.pairing args.head args.tail.head
    | [.stackArr 8 576, .stackArr 8 576], .stackArr 8 576 =>
        fun args => prims.fp12Mul args.head args.tail.head
    | _, retTy => fun _ => JasminTy.default retTy

/-- `bls12381Oracle prims` realises the EC group primitives: it satisfies
    `EcLeafAgrees prims` — by `rfl` in each of the four components, because the
    G1/G2 add / scalar-mul signatures select the intended match arms. -/
theorem bls12381Oracle_ecAgrees (prims : BlsPrimitives) :
    EcLeafAgrees prims (bls12381Oracle prims) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro args; rfl)

/-- `bls12381Oracle prims` realises the pairing-side primitives: it satisfies
    `PairingLeavesAgree prims` — by `rfl` in each component, because the pairing /
    `fp12_mul` signatures select the intended match arms. -/
theorem bls12381Oracle_pairingAgrees (prims : BlsPrimitives) :
    PairingLeavesAgree prims (bls12381Oracle prims) := by
  refine ⟨?_, ?_⟩ <;> (intro args; rfl)

/-! ## 2. Value of the deployed `Com`s under a realising leaf oracle -/

/-- **The deployed G1 MSM step, evaluated with a leaf oracle.** For a leaf oracle
    `leafSem` realising the EC group primitives (`EcLeafAgrees prims leafSem`), the
    deployed `Bls12381Emit.g1MsmTermCom` — denoted through the enabler instance
    `jasminDenoteWith leafSem` — computes `prims.g1Add acc (prims.g1Mul k P)`, the
    `scalarFold` body `acc + k·P`. -/
theorem g1MsmTermCom_denoteWith (leafSem : LeafSem) (prims : BlsPrimitives)
    (h : EcLeafAgrees prims leafSem)
    (acc : Fin G1SZ → BitVec 8) (k : Fin FPSZ → BitVec 8) (P : Fin G1SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        Bls12381Emit.g1MsmTermCom
        (.cons acc (.cons k (.cons P .nil)))
      = prims.g1Add acc (prims.g1Mul k P) := by
  rw [Bls12381Emit.g1MsmTermCom_eq_shadow]
  obtain ⟨hAdd, hMul, _, _⟩ := h
  show leafSem g1AddLeafName g1AddArgTys g1RetTy
        (.cons acc (.cons (leafSem g1MulLeafName g1MulArgTys g1RetTy
                            (.cons k (.cons P .nil))) .nil))
      = prims.g1Add acc (prims.g1Mul k P)
  rw [hMul (.cons k (.cons P .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hAdd (.cons acc (.cons (prims.g1Mul k P) .nil))]
  simp only [HVector.head, HVector.tail]

/-- **The deployed BLS-verify LHS, evaluated with a leaf oracle.** For a leaf
    oracle `leafSem` realising the pairing primitives
    (`PairingLeavesAgree prims leafSem`), the deployed
    `Bls12381Emit.blsVerifyLhsCom` — denoted through `jasminDenoteWith leafSem` —
    computes `prims.pairing σ G2`. The full check `e(σ,G2) = e(H(m),pk)` is the
    caller comparing this to the RHS pairing. -/
theorem blsVerifyLhsCom_denoteWith (leafSem : LeafSem) (prims : BlsPrimitives)
    (h : PairingLeavesAgree prims leafSem)
    (sig : Fin G1SZ → BitVec 8) (g2 : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        Bls12381Emit.blsVerifyLhsCom
        (.cons sig (.cons g2 .nil))
      = prims.pairing sig g2 := by
  rw [Bls12381Emit.blsVerifyLhsCom_eq_shadow]
  obtain ⟨hP, _⟩ := h
  show leafSem pairingLeafName pairingArgTys gtRetTy
        (.cons sig (.cons g2 .nil)) = prims.pairing sig g2
  rw [hP (.cons sig (.cons g2 .nil))]
  simp only [HVector.head, HVector.tail]

/-- **The deployed KZG-verify LHS, evaluated with a leaf oracle.** For a leaf
    oracle `leafSem` realising the pairing primitives
    (`PairingLeavesAgree prims leafSem`), the deployed
    `Bls12381Emit.kzgVerifyLhsCom` — denoted through `jasminDenoteWith leafSem` —
    computes `prims.pairing π ([s−z]G2)`. The full check is the caller comparing
    this to the RHS pairing `e(C−[y]G1, G2)`. -/
theorem kzgVerifyLhsCom_denoteWith (leafSem : LeafSem) (prims : BlsPrimitives)
    (h : PairingLeavesAgree prims leafSem)
    (proof : Fin G1SZ → BitVec 8) (sMinusZ_g2 : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        Bls12381Emit.kzgVerifyLhsCom
        (.cons proof (.cons sMinusZ_g2 .nil))
      = prims.pairing proof sMinusZ_g2 := by
  rw [Bls12381Emit.kzgVerifyLhsCom_eq_shadow]
  obtain ⟨hP, _⟩ := h
  show leafSem pairingLeafName pairingArgTys gtRetTy
        (.cons proof (.cons sMinusZ_g2 .nil)) = prims.pairing proof sMinusZ_g2
  rw [hP (.cons proof (.cons sMinusZ_g2 .nil))]
  simp only [HVector.head, HVector.tail]

/-- **The deployed Groth16 verifier RHS product, evaluated with a leaf oracle.**
    For a leaf oracle `leafSem` realising the pairing primitives
    (`PairingLeavesAgree prims leafSem`), the deployed
    `Bls12381Emit.groth16VerifyRhsCom` — denoted through `jasminDenoteWith leafSem`
    — computes the left-associated product of three pairings
    `prims.fp12Mul (prims.fp12Mul (e αG1 βG2) (e L γG2)) (e C δG2)`. The verifier
    checks this equals `e(A, B)`. -/
theorem groth16VerifyRhsCom_denoteWith (leafSem : LeafSem) (prims : BlsPrimitives)
    (h : PairingLeavesAgree prims leafSem)
    (aG1 : Fin G1SZ → BitVec 8) (bG2 : Fin G2SZ → BitVec 8)
    (l : Fin G1SZ → BitVec 8) (gG2 : Fin G2SZ → BitVec 8)
    (c : Fin G1SZ → BitVec 8) (dG2 : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        Bls12381Emit.groth16VerifyRhsCom
        (.cons aG1 (.cons bG2 (.cons l (.cons gG2 (.cons c (.cons dG2 .nil))))))
      = prims.fp12Mul
          (prims.fp12Mul (prims.pairing aG1 bG2) (prims.pairing l gG2))
          (prims.pairing c dG2) := by
  rw [Bls12381Emit.groth16VerifyRhsCom_eq_shadow]
  obtain ⟨hP, hM⟩ := h
  show leafSem fp12MulLeafName fp12MulArgTys gtRetTy
        (.cons (leafSem fp12MulLeafName fp12MulArgTys gtRetTy
                  (.cons (leafSem pairingLeafName pairingArgTys gtRetTy
                            (.cons aG1 (.cons bG2 .nil)))
                    (.cons (leafSem pairingLeafName pairingArgTys gtRetTy
                              (.cons l (.cons gG2 .nil))) .nil)))
          (.cons (leafSem pairingLeafName pairingArgTys gtRetTy
                    (.cons c (.cons dG2 .nil))) .nil))
      = prims.fp12Mul
          (prims.fp12Mul (prims.pairing aG1 bG2) (prims.pairing l gG2))
          (prims.pairing c dG2)
  rw [hP (.cons aG1 (.cons bG2 .nil)), hP (.cons l (.cons gG2 .nil)),
      hP (.cons c (.cons dG2 .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hM (.cons (prims.pairing aG1 bG2) (.cons (prims.pairing l gG2) .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hM (.cons (prims.fp12Mul (prims.pairing aG1 bG2) (prims.pairing l gG2))
            (.cons (prims.pairing c dG2) .nil))]
  simp only [HVector.head, HVector.tail]

/-! ## 3. The deployed leaf oracle + the verifiers at that oracle -/

/-- `BlsPrimitives` is inhabited (all fields are functions into `BitVec 8`), so the
    deployed primitives can be introduced as an opaque constant. -/
instance : Inhabited BlsPrimitives :=
  ⟨{ g1Add := fun _ _ _ => 0, g1Mul := fun _ _ _ => 0, g2Add := fun _ _ _ => 0,
     g2Mul := fun _ _ _ => 0, pairing := fun _ _ _ => 0, fp12Mul := fun _ _ _ => 0 }⟩

/-- An abstract constant standing for the BLS12-381 primitives the deployed code
    targets. Opaque — uninterpreted for proofs. -/
opaque deployedPrims : BlsPrimitives

/-- The leaf oracle for the deployed primitives, `bls12381Oracle deployedPrims`
    sealed as `opaque`; the seal keeps the agreements below named hypotheses. -/
opaque bls12381LeafOracle : LeafSem := bls12381Oracle deployedPrims

/-- The leaf agreement: the deployed leaf oracle realises the BLS12-381 EC group
    primitives. A named axiom. Establishing it means bridging the emitted leaf to
    the primitive spec — a leaf proof, or a jasmin/AUCurves bridge — which this
    file does not do. -/
axiom bls12381LeafOracle_ecAgrees :
    EcLeafAgrees deployedPrims bls12381LeafOracle

/-- The leaf agreement: the deployed leaf oracle realises the BLS12-381
    pairing-side primitives. A named axiom. Establishing it means bridging the
    emitted leaf to the primitive spec — a leaf proof, or a jasmin/AUCurves
    bridge — which this file does not do. -/
axiom bls12381LeafOracle_pairingAgrees :
    PairingLeavesAgree deployedPrims bls12381LeafOracle

/-- **The deployed G1 MSM step at the deployed oracle.** `Bls12381Emit.g1MsmTermCom`,
    denoted through `jasminDenoteWith bls12381LeafOracle`, computes
    `g1Add acc (g1Mul k P)` for the deployed primitives. -/
theorem g1MsmTermCom_denote
    (acc : Fin G1SZ → BitVec 8) (k : Fin FPSZ → BitVec 8) (P : Fin G1SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bls12381LeafOracle) _ _
        Bls12381Emit.g1MsmTermCom
        (.cons acc (.cons k (.cons P .nil)))
      = deployedPrims.g1Add acc (deployedPrims.g1Mul k P) :=
  g1MsmTermCom_denoteWith bls12381LeafOracle deployedPrims
    bls12381LeafOracle_ecAgrees acc k P

/-- **The deployed BLS-verify LHS at the deployed oracle.** `Bls12381Emit.blsVerifyLhsCom`,
    denoted through `jasminDenoteWith bls12381LeafOracle`, computes
    `pairing σ G2` for the deployed primitives. -/
theorem blsVerifyLhsCom_denote
    (sig : Fin G1SZ → BitVec 8) (g2 : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bls12381LeafOracle) _ _
        Bls12381Emit.blsVerifyLhsCom
        (.cons sig (.cons g2 .nil))
      = deployedPrims.pairing sig g2 :=
  blsVerifyLhsCom_denoteWith bls12381LeafOracle deployedPrims
    bls12381LeafOracle_pairingAgrees sig g2

/-- **The deployed KZG-verify LHS at the deployed oracle.** `Bls12381Emit.kzgVerifyLhsCom`,
    denoted through `jasminDenoteWith bls12381LeafOracle`, computes
    `pairing π ([s−z]G2)` for the deployed primitives. -/
theorem kzgVerifyLhsCom_denote
    (proof : Fin G1SZ → BitVec 8) (sMinusZ_g2 : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bls12381LeafOracle) _ _
        Bls12381Emit.kzgVerifyLhsCom
        (.cons proof (.cons sMinusZ_g2 .nil))
      = deployedPrims.pairing proof sMinusZ_g2 :=
  kzgVerifyLhsCom_denoteWith bls12381LeafOracle deployedPrims
    bls12381LeafOracle_pairingAgrees proof sMinusZ_g2

/-- **The deployed Groth16 verifier RHS product at the deployed oracle.**
    `Bls12381Emit.groth16VerifyRhsCom`, denoted through
    `jasminDenoteWith bls12381LeafOracle`, computes the left-associated three-pairing
    product `fp12Mul (fp12Mul (e αG1 βG2) (e L γG2)) (e C δG2)` for the deployed
    primitives. -/
theorem groth16VerifyRhsCom_denote
    (aG1 : Fin G1SZ → BitVec 8) (bG2 : Fin G2SZ → BitVec 8)
    (l : Fin G1SZ → BitVec 8) (gG2 : Fin G2SZ → BitVec 8)
    (c : Fin G1SZ → BitVec 8) (dG2 : Fin G2SZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bls12381LeafOracle) _ _
        Bls12381Emit.groth16VerifyRhsCom
        (.cons aG1 (.cons bG2 (.cons l (.cons gG2 (.cons c (.cons dG2 .nil))))))
      = deployedPrims.fp12Mul
          (deployedPrims.fp12Mul (deployedPrims.pairing aG1 bG2)
            (deployedPrims.pairing l gG2))
          (deployedPrims.pairing c dG2) :=
  groth16VerifyRhsCom_denoteWith bls12381LeafOracle deployedPrims
    bls12381LeafOracle_pairingAgrees aG1 bG2 l gG2 c dG2

end CatCrypt.Crypto.Pairing.Bls12381Denote
