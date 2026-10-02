/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveLoweringJacobian
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsMont4
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsSolinas
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4Instances
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.SolinasInstances
public import CatCrypt.Crypto.Util.BN254Verified

/-!
# The Jacobian group law over 64-bit limbs

The Jacobian lowerings `jacAddProg` and `jacDblProg` of the EllipticCurve ops `padd` and
`pdbl` (`VIR/EllipticCurveLoweringJacobian`) lowered further to `jasminDialect` by the
four-limb Montgomery lowering `FieldToJasminLimbsMont4` and by the Solinas lowering
`FieldToJasminLimbsSolinas`. The value theorems are proved once, for every modulus
record and every curve record; a curve is an instance by direct application.

Each value statement has two conjuncts: the lowered program maps the limb encodings of
the input coordinates to the limb encoding of output coordinate `i` of the Jacobian
formula, and the output triple represents the op's denotation, `ECParams.add`, which
`toECPoint_add` identifies with Mathlib's point addition on `toW C`. The preconditions of
the addition are those of `padd_lowers_to_jacobian`: affine, on-curve, distinct inputs.

## Main definitions

* `JacAddMont4`, `JacDblMont4`, `JacAddSolinas`, `JacDblSolinas`: the value statements.
* `bn254Mont`: the BN254 base prime as a four-limb Montgomery record
  (`Mont4Instances.bn254`).
* `p256Curve`, `secp256k1Curve`, `bn254Curve`: the short-Weierstrass records of P-256
  (`a = −3`), secp256k1 (`a = 0`, `b = 7`) and BN254 `G1` (`a = 0`, `b = 3`).

## Main results

* `jacAddProg_covered`, `jacDblProg_covered`: every binding satisfies any predicate that
  holds of the six operation shapes the programs use.
* `jacAdd_mont4`, `jacDbl_mont4`: the value theorems over four Montgomery limbs.
* `jacAdd_solinas`, `jacDbl_solinas`: the value theorems over `n` Solinas limbs.
* `p256_jacAdd`, `p256_jacDbl`, `secp256k1_jacAdd`, `secp256k1_jacDbl`, `bn254_jacAdd`,
  `bn254_jacDbl`: the instances.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.EcJacobianLimbs

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect.JacLower
open CatCrypt.Crypto.SecureCompilation.EcProjectiveGeneric (jacAddGen)
open CatCrypt.Crypto.SecureCompilation.EcProjectiveGenericA (jacDoubleGenA)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4 (Mont4Prime)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas (SolinasParams)

/-! ## 1. Coverage -/

section Coverage

variable {p : Nat} (Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop)
  (hA : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eAdd a b))
  (hS : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eSub a b))
  (hM : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eMul a b))
  (hQ : ∀ {Γ : Ctxt fieldDialect} (a : Var Γ (FieldTy.fp p)), Good (eSq a))
  (hD : ∀ {Γ : Ctxt fieldDialect} (a : Var Γ (FieldTy.fp p)), Good (eDbl a))
  (hC : ∀ {Γ : Ctxt fieldDialect} (c : ZMod p), Good (eConst (Γ := Γ) c))

include hS hM hQ hD in
theorem jacAddProg_covered (i : Fin 3) : CoveredCom Good (jacAddProg p i) :=
  ⟨hQ _, hQ _, hM _ _, hM _ _, hM _ _, hM _ _, hM _ _, hM _ _, hS _ _, hS _ _, hQ _,
    hM _ _, hM _ _, hQ _, hS _ _, hD _, hS _ _, hS _ _, hM _ _, hM _ _, hS _ _, hM _ _,
    hM _ _, trivial⟩

include hA hS hM hQ hD hC in
theorem jacDblProg_covered (a : ZMod p) (i : Fin 3) : CoveredCom Good (jacDblProg p a i) :=
  ⟨hQ _, hQ _, hQ _, hQ _, hQ _, hC _, hM _ _, hD _, hA _ _, hA _ _, hM _ _, hD _, hD _,
    hQ _, hD _, hS _ _, hS _ _, hM _ _, hD _, hD _, hD _, hS _ _, hM _ _, hD _, trivial⟩

end Coverage

/-! ## 2. Four Montgomery limbs -/

section Mont4

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsMont4

variable (P : Mont4Prime)

theorem jacAddProg_coveredV (i : Fin 3) : CoveredCom (GoodV P) (jacAddProg P.p i) :=
  jacAddProg_covered (GoodV P) (fun _ _ => Or.inr (Or.inl rfl))
    (fun _ _ => Or.inl (Or.inr (Or.inl rfl)))
    (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (fun _ => Or.inr (Or.inr (Or.inr (Or.inl rfl)))) i

theorem jacDblProg_coveredV (a : ZMod P.p) (i : Fin 3) :
    CoveredCom (GoodV P) (jacDblProg P.p a i) :=
  jacDblProg_covered (GoodV P) (fun _ _ => Or.inl (Or.inl rfl))
    (fun _ _ => Or.inr (Or.inl rfl)) (fun _ _ => Or.inl (Or.inr (Or.inl rfl)))
    (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (fun _ => Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (fun c => Or.inl (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩)))) a i

variable [Fact P.p.Prime]

/-- The value statement of the addition over four Montgomery limbs: the lowered program
    maps the limbs of the input coordinates to the limbs of coordinate `i` of
    `jacAddGen`, and that triple represents `C.add` of the represented inputs. -/
def JacAddMont4 (C : ECParams P.p) (J1 J2 : ZMod P.p × ZMod P.p × ZMod P.p) : Prop :=
  (∀ i : Fin 3, ((loweringL P).lowerMulti (jacAddProg P.p i)).denote
      (flatVal (fun {t} x => encL P (t := t) x) (jacVal2 J1 J2))
      = encL P (t := .fp P.p)
          (coord (jacAddGen J1.1 J1.2.1 J1.2.2 J2.1 J2.2.1 J2.2.2) i : ZMod P.p)) ∧
    jacToPoint (jacAddGen J1.1 J1.2.1 J1.2.2 J2.1 J2.2.1 J2.2.2)
      = paddF C (jacToPoint J1) (jacToPoint J2)

/-- The value statement of the doubling over four Montgomery limbs: the lowered program
    maps the limbs of the input coordinates to the limbs of coordinate `i` of
    `jacDoubleGenA C.a`, and that triple represents `C.add P P` of the represented point. -/
def JacDblMont4 (C : ECParams P.p) (J : ZMod P.p × ZMod P.p × ZMod P.p) : Prop :=
  (∀ i : Fin 3, ((loweringL P).lowerMulti (jacDblProg P.p C.a i)).denote
      (flatVal (fun {t} x => encL P (t := t) x) (jacVal1 J))
      = encL P (t := .fp P.p) (coord (jacDoubleGenA C.a J.1 J.2.1 J.2.2) i : ZMod P.p)) ∧
    jacToPoint (jacDoubleGenA C.a J.1 J.2.1 J.2.2) = pdblF C (jacToPoint J)

/-- **The addition over four Montgomery limbs**, for affine, on-curve, distinct inputs. -/
theorem jacAdd_mont4 (C : ECParams P.p) (J1 J2 : ZMod P.p × ZMod P.p × ZMod P.p)
    (hZ1 : J1.2.2 ≠ 0) (hZ2 : J2.2.2 ≠ 0)
    (hC1 : C.onCurve (J1.1 * (J1.2.2 ^ 2)⁻¹) (J1.2.1 * (J1.2.2 ^ 3)⁻¹))
    (hC2 : C.onCurve (J2.1 * (J2.2.2 ^ 2)⁻¹) (J2.2.1 * (J2.2.2 ^ 3)⁻¹))
    (hne : jacToPoint J1 ≠ jacToPoint J2) : JacAddMont4 P C J1 J2 :=
  ⟨fun i => by
    rw [fieldToJasminLimbsMont4_denoteV P _ (jacAddProg_coveredV P i), jacAddProg_denote],
    padd_lowers_to_jacobian C J1 J2 hZ1 hZ2 hC1 hC2 hne⟩

/-- **The doubling over four Montgomery limbs**, for every input triple. -/
theorem jacDbl_mont4 (hp2 : P.p ≠ 2) (C : ECParams P.p)
    (J : ZMod P.p × ZMod P.p × ZMod P.p) : JacDblMont4 P C J :=
  ⟨fun i => by
    rw [fieldToJasminLimbsMont4_denoteV P _ (jacDblProg_coveredV P C.a i), jacDblProg_denote],
    pdbl_lowers_to_jacobian hp2 C J⟩

end Mont4

/-! ## 3. Solinas limbs -/

section Solinas

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsSolinas

variable {n : Nat} (S : SolinasParams n)

theorem jacAddProg_coveredL (i : Fin 3) : CoveredCom (GoodL S) (jacAddProg (Solinas.p S) i) :=
  jacAddProg_covered (GoodL S) (fun _ _ => Or.inr (Or.inl rfl))
    (fun _ _ => Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) i

theorem jacDblProg_coveredL (a : ZMod (Solinas.p S)) (i : Fin 3) :
    CoveredCom (GoodL S) (jacDblProg (Solinas.p S) a i) :=
  jacDblProg_covered (GoodL S) (fun _ _ => Or.inl rfl) (fun _ _ => Or.inr (Or.inl rfl))
    (fun _ _ => Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
    (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (fun c => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))))) a i

variable [Fact (Nat.Prime (Solinas.p S))]

/-- The value statement of the addition over Solinas limbs, as `JacAddMont4`. -/
def JacAddSolinas (C : ECParams (Solinas.p S))
    (J1 J2 : ZMod (Solinas.p S) × ZMod (Solinas.p S) × ZMod (Solinas.p S)) : Prop :=
  (∀ i : Fin 3, ((loweringL S).lowerMulti (jacAddProg (Solinas.p S) i)).denote
      (flatVal (fun {t} x => encL S (t := t) x) (jacVal2 J1 J2))
      = encL S (t := .fp (Solinas.p S))
          (coord (jacAddGen J1.1 J1.2.1 J1.2.2 J2.1 J2.2.1 J2.2.2) i : ZMod (Solinas.p S))) ∧
    jacToPoint (jacAddGen J1.1 J1.2.1 J1.2.2 J2.1 J2.2.1 J2.2.2)
      = paddF C (jacToPoint J1) (jacToPoint J2)

/-- The value statement of the doubling over Solinas limbs, as `JacDblMont4`. -/
def JacDblSolinas (C : ECParams (Solinas.p S))
    (J : ZMod (Solinas.p S) × ZMod (Solinas.p S) × ZMod (Solinas.p S)) : Prop :=
  (∀ i : Fin 3, ((loweringL S).lowerMulti (jacDblProg (Solinas.p S) C.a i)).denote
      (flatVal (fun {t} x => encL S (t := t) x) (jacVal1 J))
      = encL S (t := .fp (Solinas.p S))
          (coord (jacDoubleGenA C.a J.1 J.2.1 J.2.2) i : ZMod (Solinas.p S))) ∧
    jacToPoint (jacDoubleGenA C.a J.1 J.2.1 J.2.2) = pdblF C (jacToPoint J)

/-- **The addition over Solinas limbs**, for affine, on-curve, distinct inputs. -/
theorem jacAdd_solinas (C : ECParams (Solinas.p S))
    (J1 J2 : ZMod (Solinas.p S) × ZMod (Solinas.p S) × ZMod (Solinas.p S))
    (hZ1 : J1.2.2 ≠ 0) (hZ2 : J2.2.2 ≠ 0)
    (hC1 : C.onCurve (J1.1 * (J1.2.2 ^ 2)⁻¹) (J1.2.1 * (J1.2.2 ^ 3)⁻¹))
    (hC2 : C.onCurve (J2.1 * (J2.2.2 ^ 2)⁻¹) (J2.2.1 * (J2.2.2 ^ 3)⁻¹))
    (hne : jacToPoint J1 ≠ jacToPoint J2) : JacAddSolinas S C J1 J2 :=
  ⟨fun i => by
    rw [fieldToJasminLimbs_denote S _ (jacAddProg_coveredL S i), jacAddProg_denote],
    padd_lowers_to_jacobian C J1 J2 hZ1 hZ2 hC1 hC2 hne⟩

/-- **The doubling over Solinas limbs**, for every input triple. -/
theorem jacDbl_solinas (hp2 : Solinas.p S ≠ 2) (C : ECParams (Solinas.p S))
    (J : ZMod (Solinas.p S) × ZMod (Solinas.p S) × ZMod (Solinas.p S)) :
    JacDblSolinas S C J :=
  ⟨fun i => by
    rw [fieldToJasminLimbs_denote S _ (jacDblProg_coveredL S C.a i), jacDblProg_denote],
    pdbl_lowers_to_jacobian hp2 C J⟩

end Solinas

/-! ## 4. Instances -/

section Instances

/-- The BN254 base prime as a four-limb Montgomery record: `Mont4Instances.bn254`. -/
abbrev bn254Mont : Mont4Prime := Mont4Instances.bn254

instance fact_prime_p256 : Fact (Nat.Prime Mont4Instances.p256.p) := CatCrypt.Util.fact_prime_p256

instance fact_prime_bn254 : Fact (Nat.Prime bn254Mont.p) := CatCrypt.Util.fact_prime_bn254

instance fact_prime_secp256k1 : Fact (Nat.Prime (Solinas.p SolinasInstances.secp256k1)) :=
  ⟨by rw [SolinasInstances.secp256k1_p]; exact CatCrypt.Util.secp256k1_prime⟩

/-- NIST P-256: `y² = x³ − 3x + b`. -/
def p256Curve : ECParams Mont4Instances.p256.p :=
  ⟨-3, 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b⟩

/-- secp256k1: `y² = x³ + 7`, over the Solinas record. -/
def secp256k1Curve : ECParams (Solinas.p SolinasInstances.secp256k1) := ⟨0, 7⟩

/-- BN254 `G1`: `y² = x³ + 3`. -/
def bn254Curve : ECParams bn254Mont.p := ⟨0, 3⟩

/-- The input triples of a curve over the modulus `q`. -/
abbrev Jac (q : Nat) : Type := ZMod q × ZMod q × ZMod q

theorem p256_jacAdd (J1 J2 : Jac Mont4Instances.p256.p) (hZ1 : J1.2.2 ≠ 0) (hZ2 : J2.2.2 ≠ 0)
    (hC1 : p256Curve.onCurve (J1.1 * (J1.2.2 ^ 2)⁻¹) (J1.2.1 * (J1.2.2 ^ 3)⁻¹))
    (hC2 : p256Curve.onCurve (J2.1 * (J2.2.2 ^ 2)⁻¹) (J2.2.1 * (J2.2.2 ^ 3)⁻¹))
    (hne : jacToPoint J1 ≠ jacToPoint J2) :
    JacAddMont4 Mont4Instances.p256 p256Curve J1 J2 :=
  jacAdd_mont4 _ _ J1 J2 hZ1 hZ2 hC1 hC2 hne

theorem p256_jacDbl (J : Jac Mont4Instances.p256.p) :
    JacDblMont4 Mont4Instances.p256 p256Curve J :=
  jacDbl_mont4 _ (by decide) _ J

theorem bn254_jacAdd (J1 J2 : Jac bn254Mont.p) (hZ1 : J1.2.2 ≠ 0) (hZ2 : J2.2.2 ≠ 0)
    (hC1 : bn254Curve.onCurve (J1.1 * (J1.2.2 ^ 2)⁻¹) (J1.2.1 * (J1.2.2 ^ 3)⁻¹))
    (hC2 : bn254Curve.onCurve (J2.1 * (J2.2.2 ^ 2)⁻¹) (J2.2.1 * (J2.2.2 ^ 3)⁻¹))
    (hne : jacToPoint J1 ≠ jacToPoint J2) : JacAddMont4 bn254Mont bn254Curve J1 J2 :=
  jacAdd_mont4 _ _ J1 J2 hZ1 hZ2 hC1 hC2 hne

theorem bn254_jacDbl (J : Jac bn254Mont.p) : JacDblMont4 bn254Mont bn254Curve J :=
  jacDbl_mont4 _ (by decide) _ J

theorem secp256k1_jacAdd (J1 J2 : Jac (Solinas.p SolinasInstances.secp256k1))
    (hZ1 : J1.2.2 ≠ 0) (hZ2 : J2.2.2 ≠ 0)
    (hC1 : secp256k1Curve.onCurve (J1.1 * (J1.2.2 ^ 2)⁻¹) (J1.2.1 * (J1.2.2 ^ 3)⁻¹))
    (hC2 : secp256k1Curve.onCurve (J2.1 * (J2.2.2 ^ 2)⁻¹) (J2.2.1 * (J2.2.2 ^ 3)⁻¹))
    (hne : jacToPoint J1 ≠ jacToPoint J2) :
    JacAddSolinas SolinasInstances.secp256k1 secp256k1Curve J1 J2 :=
  jacAdd_solinas _ _ J1 J2 hZ1 hZ2 hC1 hC2 hne

theorem secp256k1_jacDbl (J : Jac (Solinas.p SolinasInstances.secp256k1)) :
    JacDblSolinas SolinasInstances.secp256k1 secp256k1Curve J :=
  jacDbl_solinas _ (by decide) _ J

end Instances

end CatCrypt.Crypto.SecureCompilation.Algebraic.EcJacobianLimbs
