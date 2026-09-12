/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.VectorReduce
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.Pairing.MsmReduce
public import CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront

/-!
# Production NIST P-256 emit: EC group leaves, the scalar-mul / MSM reduction over
  the production group, and the ECDSA-P256 verification equation

The P-256 analogue of `Secp256k1Emit.lean` (which itself mirrors
`MsmReduce` / `Bls12381Emit`): the same `VectorReduce.scalarFold_eq_hsum` core
over the production P-256 group, the EC point-add / scalar-mul as opaque
`extCall` leaves (`EcLeafAgrees`), plus the **ECDSA-P256 verification equation**
`R' = u₁·G + u₂·Q` emitted as a straight-line `Com` of the EC leaves.

P-256 (secp256r1 / prime256v1) is the TLS / EDHOC / FIPS 186-4 curve
`y² = x³ − 3x + b` over the 256-bit prime `p = 2²⁵⁶ − 2²²⁴ + 2¹⁹² + 2⁹⁶ − 1`.

## No new machinery — the AUCurves-leaf story

What AUCurves verifies for P-256 is the **field tower**: `p256-safe-rust` exposes
the machine-checked `fiat-crypto/fiat-rust/p256_64` field ops
(`fp_add/sub/mul/square/opp`, to/from-bytes, to/from-Montgomery) plus the
Bernstein–Yang constant-time inverse `fp_inv` (verified against
`src/Arithmetic/safegcd/divsteps_p256_half.v`). The **group law** (point-add,
scalar-mul) is *built from* those verified field ops; we keep it as the carried
trusted leaf edge — the same honest stance as `Bls12381Emit` (AUCurves verifies
the field/pairing tower; the group add law stays trusted). The KAT
(`bench/p256_compare/`) exercises those verified field leaves on the **published
FIPS 186-4 P-256 base-point** coordinates.

## Wire layout

A P-256 field element `Fp` is 4 little-endian `u64` limbs = `32` bytes (`FESZ`),
matching `fiat_p256_montgomery_domain_field_element` (`[u64;4]`). An affine **EC
point** is `(x ‖ y)`, two `Fp`s = `2·FESZ = 64` bytes; a **scalar** is `32`
bytes.

0 sorries; the only hypotheses are the opaque EC-leaf agreements
(`EcLeafAgrees`), the edge carried throughout this theory.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.P256Emit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VectorReduce
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
open scoped BigOperators

/-! ## 1. Production wire widths -/

/-- A P-256 field element `Fp` on the wire: `32` bytes (4 little-endian `u64`
    limbs), matching the fiat-crypto `[u64;4]` Montgomery layout. -/
def FESZ : Nat := 32

/-- An affine P-256 point on the wire: `(x ‖ y)`, two `Fp`s = `64` bytes. -/
def PTSZ : Nat := 2 * FESZ

/-! ## 2. The scalar-mul / MSM reduction over the production group -/

section MSM

variable {G : Type*} [AddCommMonoid G] {L : ℕ}

/-- The MSM as the **horizontal reduction** `hsum` over the P-256 group. -/
def msm (k : Fin L → ℕ) (P : Fin L → G) : G :=
  hsum (fun i => (k i) • (P i))

/-- The MSM as the **sequential left-fold** `scalarFold` the emitter produces. -/
def msmFold (k : Fin L → ℕ) (P : Fin L → G) : G :=
  scalarFold (fun i => (k i) • (P i))

/-- **MSM reduction (P-256 lane).** The P-256 MSM reduces to
    `scalarFold` over the production group `AddCommMonoid`. This is
    `VectorReduce.scalarFold_eq_hsum` at the P-256 lane — no new content. -/
theorem msmFold_eq_msm (k : Fin L → ℕ) (P : Fin L → G) :
    msmFold k P = msm k P :=
  scalarFold_eq_hsum (fun i => (k i) • (P i))

/-- The P-256 MSM computes `Σ_i k_i · P_i` (the ECDSA verifier's `u₁·G + u₂·Q`
    is the `L = 2` instance). -/
theorem msm_isSum (k : Fin L → ℕ) (P : Fin L → G) :
    msm k P = ∑ i, (k i) • (P i) := by
  simp only [msm, hsum]

end MSM

/-! ## 3. The EC leaf spec (opaque `extCall`, carried agreement) -/

/-- The leaf name the front emits for P-256 point-add. -/
def addLeafName : String := "p256_point_add"

/-- The leaf name the front emits for P-256 scalar-multiply. -/
def mulLeafName : String := "p256_scalar_mul"

/-- Point-add leaf signature. -/
def addArgTys : List JasminTy := [.stackArr 8 PTSZ, .stackArr 8 PTSZ]
/-- Scalar-mul leaf signature. -/
def mulArgTys : List JasminTy := [.stackArr 8 FESZ, .stackArr 8 PTSZ]
/-- Both leaves return an affine P-256 point. -/
def ptRetTy : JasminTy := .stackArr 8 PTSZ

/-- The leaf-semantics carrier (reusing `MsmReduce.EcLeafSem`). -/
abbrev LeafSem : Type := MsmReduce.EcLeafSem

/-- The abstract P-256 primitive interface: a point-add and a scalar-multiply on
    the on-wire affine representation. -/
structure P256Primitives where
  /-- EC point addition `P + Q`. -/
  pointAdd : (Fin PTSZ → BitVec 8) → (Fin PTSZ → BitVec 8) → (Fin PTSZ → BitVec 8)
  /-- EC scalar multiplication `k · P`. -/
  scalarMul : (Fin FESZ → BitVec 8) → (Fin PTSZ → BitVec 8) → (Fin PTSZ → BitVec 8)

/-- Point-add leaf agreement. -/
def AddLeafAgrees (prims : P256Primitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) addArgTys,
    leafSem addLeafName addArgTys ptRetTy args = prims.pointAdd (args.head) (args.tail.head)

/-- Scalar-mul leaf agreement. -/
def MulLeafAgrees (prims : P256Primitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) mulArgTys,
    leafSem mulLeafName mulArgTys ptRetTy args = prims.scalarMul (args.head) (args.tail.head)

/-- The full P-256 EC-leaf agreement. The AUCurves-field-backed group leaves are
    the intended witness (`bench/p256_compare/`). -/
def EcLeafAgrees (prims : P256Primitives) (leafSem : LeafSem) : Prop :=
  AddLeafAgrees prims leafSem ∧ MulLeafAgrees prims leafSem

/-! ## 4. Leaf `Expr` builders + denotation (the `extCall` bridge point) -/

/-- Build the point-add leaf `Expr`. -/
def addLeafExpr {Γ : Ctxt jasminDialect} (P Q : Ctxt.Var Γ (.stackArr 8 PTSZ)) :
    Expr jasminDialect Γ ptRetTy :=
  { op := .extCall addLeafName addArgTys ptRetTy, retTy_eq := rfl,
    args := .cons P (.cons Q .nil) }

/-- Build the scalar-mul leaf `Expr`. -/
def mulLeafExpr {Γ : Ctxt jasminDialect}
    (k : Ctxt.Var Γ (.stackArr 8 FESZ)) (P : Ctxt.Var Γ (.stackArr 8 PTSZ)) :
    Expr jasminDialect Γ ptRetTy :=
  { op := .extCall mulLeafName mulArgTys ptRetTy, retTy_eq := rfl,
    args := .cons k (.cons P .nil) }

/-- The point-add leaf `Expr` denotes to `jasminExtSem` of the looked-up points.
    By `rfl`. -/
theorem addLeafExpr_denote {Γ : Ctxt jasminDialect}
    (P Q : Ctxt.Var Γ (.stackArr 8 PTSZ)) (V : Ctxt.Valuation Γ) :
    (addLeafExpr P Q).denote V
      = jasminExtSem addLeafName addArgTys ptRetTy
          (.cons (P.lookup V) (.cons (Q.lookup V) .nil)) :=
  rfl

/-- The scalar-mul leaf `Expr` denotes to `jasminExtSem` of the looked-up scalar +
    point. By `rfl`. -/
theorem mulLeafExpr_denote {Γ : Ctxt jasminDialect}
    (k : Ctxt.Var Γ (.stackArr 8 FESZ)) (P : Ctxt.Var Γ (.stackArr 8 PTSZ))
    (V : Ctxt.Valuation Γ) :
    (mulLeafExpr k P).denote V
      = jasminExtSem mulLeafName mulArgTys ptRetTy
          (.cons (k.lookup V) (.cons (P.lookup V) .nil)) :=
  rfl

/-! ## 5. One MSM term, with the denotation carry -/

/-- One MSM step as an orchestrating `Com` over `(acc, k, P)` — the **hand shadow**
    (the denote reference). The `scalarFold` body `acc ↦ acc + k_i·P_i`. -/
def msmTermComShadow :
    Com jasminDialect
      [.stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ]
      (.stackArr 8 PTSZ) :=
  .var (mulLeafExpr
          (Γ := [.stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ])
          (.there .here) (.there (.there .here)))
    (.var (addLeafExpr
            (Γ := [.stackArr 8 PTSZ, .stackArr 8 PTSZ,
                   .stackArr 8 FESZ, .stackArr 8 PTSZ])
            (.there .here) .here)
      (.ret .here))

/-- The MSM-step input context `[acc, k, P]`. Root slots: `acc = 2, k = 1, P = 0`. -/
def msmTermCtxt : Ctxt jasminDialect :=
  [.stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ]

/-- The MSM step as an `OrchestrationFront` phase schedule over `[acc, k, P]`.
    `t = scalar_mul(k, P)` (slots `[1, 0]`, result slot `3`),
    `out = point_add(acc, t)` (slots `[2, 3]`, result slot `4`, returned). -/
def msmTermSchedule : List CallPhase :=
  [ { leaf := mulLeafName, argTys := mulArgTys, retTy := ptRetTy, argSlots := [1, 0] }
  , { leaf := addLeafName, argTys := addArgTys, retTy := ptRetTy, argSlots := [2, 3] } ]

/-- **Generation gate.** The front resolves the MSM-step schedule. -/
theorem msmTermCom_isSome :
    (buildOrchCom msmTermCtxt msmTermSchedule 4 ptRetTy).isSome = true := by rfl

/-- **The deployed MSM-step kernel, front-sourced** by `buildOrchCom` from
    `msmTermSchedule`. Definitionally the hand shadow (`msmTermCom_eq_shadow`). -/
def msmTermCom :
    Com jasminDialect
      [.stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ]
      (.stackArr 8 PTSZ) :=
  (buildOrchCom msmTermCtxt msmTermSchedule 4 ptRetTy).get msmTermCom_isSome

/-- **Exactness.** The front-sourced `msmTermCom` is definitionally the hand
    shadow — the auto-resolved de-Bruijn operand chains coincide with the
    hand-threaded `.here`/`.there` chains. -/
theorem msmTermCom_eq_shadow : msmTermCom = msmTermComShadow := by rfl

/-- **Proof carry for one MSM step (hand shadow).** Denotes to
    `prims.pointAdd acc (prims.scalarMul k P)` under `EcLeafAgrees prims
    jasminExtSem`. Mirror of `MsmReduce.msmTermCom_denote`. -/
theorem msmTermComShadow_denote (prims : P256Primitives)
    (hLeaf : EcLeafAgrees prims jasminExtSem)
    (acc : Fin PTSZ → BitVec 8) (k : Fin FESZ → BitVec 8) (P : Fin PTSZ → BitVec 8) :
    msmTermComShadow.denote (.cons acc (.cons k (.cons P .nil)))
      = prims.pointAdd acc (prims.scalarMul k P) := by
  obtain ⟨hAdd, hMul⟩ := hLeaf
  show jasminExtSem addLeafName addArgTys ptRetTy
        (.cons acc (.cons (jasminExtSem mulLeafName mulArgTys ptRetTy
                            (.cons k (.cons P .nil))) .nil))
      = prims.pointAdd acc (prims.scalarMul k P)
  rw [hMul (.cons k (.cons P .nil))]
  show jasminExtSem addLeafName addArgTys ptRetTy
        (.cons acc (.cons (prims.scalarMul k P) .nil))
      = prims.pointAdd acc (prims.scalarMul k P)
  rw [hAdd (.cons acc (.cons (prims.scalarMul k P) .nil))]
  rfl

/-- **Proof carry for one MSM step (front-sourced deployed).** Via
    `msmTermCom_eq_shadow` + the shadow's denote, so downstream users of
    `msmTermCom` by name are unaffected by the front-sourcing. -/
theorem msmTermCom_denote (prims : P256Primitives)
    (hLeaf : EcLeafAgrees prims jasminExtSem)
    (acc : Fin PTSZ → BitVec 8) (k : Fin FESZ → BitVec 8) (P : Fin PTSZ → BitVec 8) :
    msmTermCom.denote (.cons acc (.cons k (.cons P .nil)))
      = prims.pointAdd acc (prims.scalarMul k P) := by
  rw [msmTermCom_eq_shadow]; exact msmTermComShadow_denote prims hLeaf acc k P

/-! ## 6. The ECDSA-P256 verification equation (straight-line `Com` of EC leaves)

ECDSA-P256 verification recomputes `R' = u₁·G + u₂·Q` (`u₁ = z·s⁻¹`, `u₂ = r·s⁻¹`,
`G` the base point, `Q` the public key) and accepts iff `R'.x mod n = r`. The
group computation is a 2-term MSM: two scalar-mul leaves accumulated by one
point-add leaf. -/

/-- ECDSA-P256 verify, the recomputed point `R' = u₁·G + u₂·Q` — the **hand
    shadow**. ABI: `Γ = [u₁, G, u₂, Q]`. -/
def ecdsaVerifyComShadow :
    Com jasminDialect
      [.stackArr 8 FESZ, .stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ]
      (.stackArr 8 PTSZ) :=
  .var (mulLeafExpr
          (Γ := [.stackArr 8 FESZ, .stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ])
          .here (.there .here))                                 -- t1 = u1·G
    (.var (mulLeafExpr
            (Γ := [.stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ,
                   .stackArr 8 FESZ, .stackArr 8 PTSZ])
            (.there (.there (.there .here)))                    -- u2
            (.there (.there (.there (.there .here)))))          -- Q
      (.var (addLeafExpr
              (Γ := [.stackArr 8 PTSZ, .stackArr 8 PTSZ, .stackArr 8 FESZ,
                     .stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ])
              (.there .here) .here)                             -- t1 + t2
        (.ret .here)))

/-- The ECDSA-verify input context `[u₁, G, u₂, Q]`. Root slots:
    `u₁ = 3, G = 2, u₂ = 1, Q = 0`. -/
def ecdsaVerifyCtxt : Ctxt jasminDialect :=
  [.stackArr 8 FESZ, .stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ]

/-- The ECDSA-verify group step as an `OrchestrationFront` phase schedule over
    `[u₁, G, u₂, Q]`. `t₁ = scalar_mul(u₁, G)` (slots `[3, 2]`, result slot `4`),
    `t₂ = scalar_mul(u₂, Q)` (slots `[1, 0]`, result slot `5`),
    `R' = point_add(t₁, t₂)` (slots `[4, 5]`, result slot `6`, returned). -/
def ecdsaVerifySchedule : List CallPhase :=
  [ { leaf := mulLeafName, argTys := mulArgTys, retTy := ptRetTy, argSlots := [3, 2] }
  , { leaf := mulLeafName, argTys := mulArgTys, retTy := ptRetTy, argSlots := [1, 0] }
  , { leaf := addLeafName, argTys := addArgTys, retTy := ptRetTy, argSlots := [4, 5] } ]

/-- **Generation gate.** The front resolves the ECDSA-verify schedule. -/
theorem ecdsaVerifyCom_isSome :
    (buildOrchCom ecdsaVerifyCtxt ecdsaVerifySchedule 6 ptRetTy).isSome = true := by rfl

/-- **The deployed ECDSA-verify kernel, front-sourced** by `buildOrchCom`.
    Definitionally the hand shadow (`ecdsaVerifyCom_eq_shadow`). -/
def ecdsaVerifyCom :
    Com jasminDialect
      [.stackArr 8 FESZ, .stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ]
      (.stackArr 8 PTSZ) :=
  (buildOrchCom ecdsaVerifyCtxt ecdsaVerifySchedule 6 ptRetTy).get ecdsaVerifyCom_isSome

/-- **Exactness.** `ecdsaVerifyCom` is definitionally the hand shadow. -/
theorem ecdsaVerifyCom_eq_shadow : ecdsaVerifyCom = ecdsaVerifyComShadow := by rfl

/-- **ECDSA-P256 verify denotation (hand shadow).** The recomputed point
    `R' = u₁·G + u₂·Q` denotes to
    `prims.pointAdd (prims.scalarMul u₁ G) (prims.scalarMul u₂ Q)` under the
    carried `EcLeafAgrees`. The verifier accepts iff `R'.x mod n = r`.
    The 2-term MSM (`msm` at `L = 2`) at the leaf level. -/
theorem ecdsaVerifyComShadow_denote (prims : P256Primitives)
    (hLeaf : EcLeafAgrees prims jasminExtSem)
    (u1 : Fin FESZ → BitVec 8) (G : Fin PTSZ → BitVec 8)
    (u2 : Fin FESZ → BitVec 8) (Q : Fin PTSZ → BitVec 8) :
    ecdsaVerifyComShadow.denote (.cons u1 (.cons G (.cons u2 (.cons Q .nil))))
      = prims.pointAdd (prims.scalarMul u1 G) (prims.scalarMul u2 Q) := by
  obtain ⟨hAdd, hMul⟩ := hLeaf
  show jasminExtSem addLeafName addArgTys ptRetTy
        (.cons (jasminExtSem mulLeafName mulArgTys ptRetTy (.cons u1 (.cons G .nil)))
          (.cons (jasminExtSem mulLeafName mulArgTys ptRetTy (.cons u2 (.cons Q .nil)))
            .nil))
      = prims.pointAdd (prims.scalarMul u1 G) (prims.scalarMul u2 Q)
  rw [hMul (.cons u1 (.cons G .nil)), hMul (.cons u2 (.cons Q .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hAdd (.cons (prims.scalarMul u1 G) (.cons (prims.scalarMul u2 Q) .nil))]
  rfl

/-- **ECDSA-P256 verify denotation (front-sourced deployed).** Via
    `ecdsaVerifyCom_eq_shadow` + the shadow's denote. -/
theorem ecdsaVerifyCom_denote (prims : P256Primitives)
    (hLeaf : EcLeafAgrees prims jasminExtSem)
    (u1 : Fin FESZ → BitVec 8) (G : Fin PTSZ → BitVec 8)
    (u2 : Fin FESZ → BitVec 8) (Q : Fin PTSZ → BitVec 8) :
    ecdsaVerifyCom.denote (.cons u1 (.cons G (.cons u2 (.cons Q .nil))))
      = prims.pointAdd (prims.scalarMul u1 G) (prims.scalarMul u2 Q) := by
  rw [ecdsaVerifyCom_eq_shadow]
  exact ecdsaVerifyComShadow_denote prims hLeaf u1 G u2 Q

end CatCrypt.Crypto.Pairing.P256Emit
