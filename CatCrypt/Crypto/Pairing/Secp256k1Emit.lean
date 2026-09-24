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
# Production secp256k1 emit: EC group leaves, the scalar-mul / MSM reduction over
  the production group, and the ECDSA verification equation

`MsmReduce.lean` validated the **MSM = `scalarFold` over the EC group** reduction
on a *toy* curve (`ZMod 23`), with the EC point-add / scalar-mul as opaque
`extCall` leaves (`MsmReduce.EcLeafAgrees`). `Bls12381Emit.lean` lifted it to the
production BLS12-381 G1 group + pairing. This file is the **secp256k1 analogue**:
the same `VectorReduce.scalarFold_eq_hsum` core over the production secp256k1
group, the same opaque-leaf edge, plus the **ECDSA verification equation**
`R =? u₁·G + u₂·Q` emitted as a straight-line `Com` of the EC leaves.

secp256k1 is the Bitcoin / Schnorr-FROST / ECDSA curve (`y² = x³ + 7` over the
256-bit prime field `Fp` with `p = 2²⁵⁶ − 2³² − 977`).

## No new machinery — the AUCurves-leaf story

The positioning is exactly the FAEST symmetric-leaf / AUCurves-leaf pattern of
`MsmReduce` / `Bls12381Emit`: the EC point-add / scalar-mul are **leaves** (no new
VIR machinery), emitted as opaque `extCall`s whose *agreement* (`EcLeafAgrees`)
ties the opaque leaf to the abstract EC primitive. What AUCurves verifies for
secp256k1 is precisely the **field tower**: `secp256k1-safe-rust` exposes the
machine-checked `fiat-crypto/fiat-rust/secp256k1_montgomery_64` field ops
(`fp_add/sub/mul/square/opp`, to/from-bytes, to/from-Montgomery) plus a
Bernstein–Yang constant-time inverse `fp_inv` (verified against the convergence
certificate `src/Arithmetic/safegcd/divsteps_secp256k1_half.v`). The **group
law** (point-add, scalar-mul) is *built from* those verified field ops; we keep
it as the trusted leaf edge (the same stance as `Bls12381Emit`,
where AUCurves verifies the field/pairing tower and the group add law stays
trusted). The KAT (`bench/secp256k1_compare/`) exercises those verified field
leaves on the **published SEC 2 / Bitcoin generator** coordinates.

## The production secp256k1 group (the AddCommMonoid lane)

As in `VectorReduce` / `Bls12381Emit`, the only algebraic fact the reduction
needs is that the lane type is an `AddCommMonoid` (associativity + commutativity
let the accumulation reassociate / reorder). We take the production secp256k1
group as an abstract `[AddCommMonoid G]` (the secp256k1 group is a cyclic abelian
group of prime order `n`). The toy `MsmReduce.ECPt` over `ZMod 23` is the
concrete `AddCommMonoid` instance that *validates* the same reduction at a field
where the EC ops are schoolbook.

## Wire layout (production widths)

A secp256k1 field element `Fp` is 4 little-endian `u64` limbs = `32` bytes
(`FESZ`), matching `fiat_secp256k1_montgomery_montgomery_domain_field_element`
(`[u64;4]`). On the wire an affine **EC point** is `(x ‖ y)`, two `Fp`s =
`2·FESZ = 64` bytes; a **scalar** (an `Fn` element mod `n`) is also `32` bytes.

All goals closed; the only hypotheses are the opaque EC-leaf agreements
(`EcLeafAgrees prims leafSem`) at the leaf-model parameter `leafSem`: each
denotation theorem denotes its `Com` through `jasminDenoteWith leafSem`, and
`secp256k1Oracle_agrees` shows the agreement is satisfiable for every `prims`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Secp256k1Emit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VectorReduce
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
open scoped BigOperators

/-! ## 1. Production wire widths -/

/-- A secp256k1 field element `Fp` on the wire: `32` bytes (4 little-endian `u64`
    limbs), matching the fiat-crypto `[u64;4]` Montgomery layout. -/
def FESZ : Nat := 32

/-- An affine secp256k1 point on the wire: `(x ‖ y)`, two `Fp`s = `64` bytes. -/
def PTSZ : Nat := 2 * FESZ

/-! ## 2. The scalar-mul / MSM reduction over the production group

The MSM `Σ_i k_i · P_i` over the secp256k1 group. The only algebraic fact the
reduction needs is that the lane type is an `AddCommMonoid`; we take the
production group as an abstract `[AddCommMonoid G]`. This is
`MsmReduce.msm_eq_scalarFold` re-stated at the production lane. -/

section MSM

variable {G : Type*} [AddCommMonoid G] {L : ℕ}

/-- The MSM as the **horizontal reduction** `hsum` over the secp256k1 group of the
    per-term scalar-multiples `k_i • P_i`. -/
def msm (k : Fin L → ℕ) (P : Fin L → G) : G :=
  hsum (fun i => (k i) • (P i))

/-- The MSM as the **sequential left-fold** `scalarFold` the straight-line emitter
    produces: `((0 + k₀·P₀) + k₁·P₁) + ⋯`. -/
def msmFold (k : Fin L → ℕ) (P : Fin L → G) : G :=
  scalarFold (fun i => (k i) • (P i))

/-- **MSM reduction (secp256k1 lane).** The secp256k1 MSM reduces to
    `scalarFold` over the production group `AddCommMonoid`: the sequential
    left-fold equals the horizontal reduction. This is
    `VectorReduce.scalarFold_eq_hsum` at the secp256k1 lane — no new content. -/
theorem msmFold_eq_msm (k : Fin L → ℕ) (P : Fin L → G) :
    msmFold k P = msm k P :=
  scalarFold_eq_hsum (fun i => (k i) • (P i))

/-- The secp256k1 MSM computes the mathematical multi-scalar multiplication
    `Σ_i k_i · P_i` (the value the ECDSA verifier's `u₁·G + u₂·Q` is an instance
    of, at `L = 2`). -/
theorem msm_isSum (k : Fin L → ℕ) (P : Fin L → G) :
    msm k P = ∑ i, (k i) • (P i) := by
  simp only [msm, hsum]

end MSM

/-! ## 3. The EC leaf spec (opaque `extCall`, carried agreement)

The point-add and scalar-mul are the **EC leaf** (`MsmReduce.EcLeafAgrees` shape,
at production widths). The leaf-semantics carrier reuses `MsmReduce.EcLeafSem`. -/

/-- The leaf name the front emits for secp256k1 point-add. -/
def addLeafName : String := "secp256k1_point_add"

/-- The leaf name the front emits for secp256k1 scalar-multiply. -/
def mulLeafName : String := "secp256k1_scalar_mul"

/-- Point-add leaf signature: `(P, Q : stackArr 8 PTSZ) → R : stackArr 8 PTSZ`. -/
def addArgTys : List JasminTy := [.stackArr 8 PTSZ, .stackArr 8 PTSZ]
/-- Scalar-mul leaf signature: `(k : stackArr 8 FESZ, P : stackArr 8 PTSZ) → R`. -/
def mulArgTys : List JasminTy := [.stackArr 8 FESZ, .stackArr 8 PTSZ]
/-- Both leaves return an affine secp256k1 point. -/
def ptRetTy : JasminTy := .stackArr 8 PTSZ

/-- The leaf-semantics carrier (reusing `MsmReduce.EcLeafSem`: the exact shape of
    `jasminExtSem`). A concrete binding (the AUCurves-field-backed group leaves)
    is a value of this type. -/
abbrev LeafSem : Type := MsmReduce.EcLeafSem

/-- The abstract secp256k1 primitive interface the emit orchestrates: a point-add
    and a scalar-multiply on the on-wire `2·FESZ`-byte affine representation. -/
structure Secp256k1Primitives where
  /-- EC point addition `P + Q`. -/
  pointAdd : (Fin PTSZ → BitVec 8) → (Fin PTSZ → BitVec 8) → (Fin PTSZ → BitVec 8)
  /-- EC scalar multiplication `k · P` (scalar `k` as `FESZ` bytes). -/
  scalarMul : (Fin FESZ → BitVec 8) → (Fin PTSZ → BitVec 8) → (Fin PTSZ → BitVec 8)

/-- Point-add leaf agreement. -/
def AddLeafAgrees (prims : Secp256k1Primitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) addArgTys,
    leafSem addLeafName addArgTys ptRetTy args = prims.pointAdd (args.head) (args.tail.head)

/-- Scalar-mul leaf agreement. -/
def MulLeafAgrees (prims : Secp256k1Primitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) mulArgTys,
    leafSem mulLeafName mulArgTys ptRetTy args = prims.scalarMul (args.head) (args.tail.head)

/-- The full secp256k1 EC-leaf agreement: the leaf realises both EC primitives on
    both leaf names. The AUCurves-field-backed group leaves are the intended
    witness (`bench/secp256k1_compare/`). -/
def EcLeafAgrees (prims : Secp256k1Primitives) (leafSem : LeafSem) : Prop :=
  AddLeafAgrees prims leafSem ∧ MulLeafAgrees prims leafSem

/-! ## 4. Leaf `Expr` builders + denotation (the `extCall` bridge point) -/

/-- Build the point-add leaf `Expr` from two point variables. -/
def addLeafExpr {Γ : Ctxt jasminDialect} (P Q : Ctxt.Var Γ (.stackArr 8 PTSZ)) :
    Expr jasminDialect Γ ptRetTy :=
  { op := .extCall addLeafName addArgTys ptRetTy, retTy_eq := rfl,
    args := .cons P (.cons Q .nil) }

/-- Build the scalar-mul leaf `Expr` from a scalar variable and a point. -/
def mulLeafExpr {Γ : Ctxt jasminDialect}
    (k : Ctxt.Var Γ (.stackArr 8 FESZ)) (P : Ctxt.Var Γ (.stackArr 8 PTSZ)) :
    Expr jasminDialect Γ ptRetTy :=
  { op := .extCall mulLeafName mulArgTys ptRetTy, retTy_eq := rfl,
    args := .cons k (.cons P .nil) }

/-- Denoted through `jasminDenoteWith leafSem`, the point-add leaf `Expr` is
    `leafSem` of the looked-up points. By `rfl`. -/
theorem addLeafExpr_denote (leafSem : LeafSem) {Γ : Ctxt jasminDialect}
    (P Q : Ctxt.Var Γ (.stackArr 8 PTSZ)) (V : Ctxt.Valuation Γ) :
    @Expr.denote _ _ _ (jasminDenoteWith leafSem) _ _ (addLeafExpr P Q) V
      = leafSem addLeafName addArgTys ptRetTy
          (.cons (P.lookup V) (.cons (Q.lookup V) .nil)) :=
  rfl

/-- Denoted through `jasminDenoteWith leafSem`, the scalar-mul leaf `Expr` is
    `leafSem` of the looked-up scalar and point. By `rfl`. -/
theorem mulLeafExpr_denote (leafSem : LeafSem) {Γ : Ctxt jasminDialect}
    (k : Ctxt.Var Γ (.stackArr 8 FESZ)) (P : Ctxt.Var Γ (.stackArr 8 PTSZ))
    (V : Ctxt.Valuation Γ) :
    @Expr.denote _ _ _ (jasminDenoteWith leafSem) _ _ (mulLeafExpr k P) V
      = leafSem mulLeafName mulArgTys ptRetTy
          (.cons (k.lookup V) (.cons (P.lookup V) .nil)) :=
  rfl

/-- A leaf oracle realising the two secp256k1 primitives, selected by dialect
    signature: on the point-add signature (`64 / 64 → 64`) it returns
    `prims.pointAdd`, on the scalar-mul signature (`32 / 64 → 64`) it returns
    `prims.scalarMul`, and it is `JasminTy.default` on any other leaf. -/
def secp256k1Oracle (prims : Secp256k1Primitives) : LeafSem :=
  fun _name argTys retTy =>
    match argTys, retTy with
    | [.stackArr 8 64, .stackArr 8 64], .stackArr 8 64 =>
        fun args => prims.pointAdd args.head args.tail.head
    | [.stackArr 8 32, .stackArr 8 64], .stackArr 8 64 =>
        fun args => prims.scalarMul args.head args.tail.head
    | _, retTy => fun _ => JasminTy.default retTy

/-- `secp256k1Oracle prims` satisfies `EcLeafAgrees prims`, so the agreement
    hypothesis of the denotation theorems below is satisfiable for every `prims`.
    By `rfl` in each component: the two leaf signatures select the intended match
    arms. -/
theorem secp256k1Oracle_agrees (prims : Secp256k1Primitives) :
    EcLeafAgrees prims (secp256k1Oracle prims) := by
  refine ⟨?_, ?_⟩ <;> (intro args; rfl)

/-! ## 5. One MSM term, with the denotation carry

Production analogue of `MsmReduce.msmTermCom` / `Bls12381Emit.g1MsmTermCom`: one
MSM step `acc ↦ acc + k_i · P_i`, built from the two EC leaves, denoting to
`prims.pointAdd acc (prims.scalarMul k P)` through `jasminDenoteWith leafSem` for
every leaf oracle `leafSem` satisfying `EcLeafAgrees`. -/

/-- One MSM step as an orchestrating `Com` over `(acc, k, P)` — the **hand
    shadow**: first the scalar-mul leaf `t = secp256k1_scalar_mul(k, P)`, then the
    point-add leaf `out = secp256k1_point_add(acc, t)`. The `scalarFold` body
    `acc ↦ acc + k_i·P_i`. -/
def msmTermComShadow :
    Com jasminDialect
      [.stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ]
      (.stackArr 8 PTSZ) :=
  -- Γ = [acc, k, P]
  .var (mulLeafExpr
          (Γ := [.stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ])
          (.there .here) (.there (.there .here)))
    -- Γ' = [t, acc, k, P]
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

/-- **The deployed MSM step, evaluated with a leaf oracle.** For a leaf oracle
    `leafSem` realising the secp256k1 primitives (`EcLeafAgrees prims leafSem`),
    the deployed `msmTermCom`, denoted through `jasminDenoteWith leafSem`, computes
    `prims.pointAdd acc (prims.scalarMul k P)` — `acc + k·P`, the `scalarFold`
    body at the leaf level. The leaf model is the parameter `leafSem`;
    `secp256k1Oracle_agrees` shows the hypothesis is satisfiable. -/
theorem msmTermCom_denote (leafSem : LeafSem) (prims : Secp256k1Primitives)
    (hLeaf : EcLeafAgrees prims leafSem)
    (acc : Fin PTSZ → BitVec 8) (k : Fin FESZ → BitVec 8) (P : Fin PTSZ → BitVec 8) :
    @Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
        msmTermCom (.cons acc (.cons k (.cons P .nil)))
      = prims.pointAdd acc (prims.scalarMul k P) := by
  rw [msmTermCom_eq_shadow]
  obtain ⟨hAdd, hMul⟩ := hLeaf
  show leafSem addLeafName addArgTys ptRetTy
        (.cons acc (.cons (leafSem mulLeafName mulArgTys ptRetTy
                            (.cons k (.cons P .nil))) .nil))
      = prims.pointAdd acc (prims.scalarMul k P)
  rw [hMul (.cons k (.cons P .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hAdd (.cons acc (.cons (prims.scalarMul k P) .nil))]
  rfl

/-! ## 6. The ECDSA verification equation (straight-line `Com` of EC leaves)

ECDSA verification recomputes `R' = u₁·G + u₂·Q` (where `u₁ = z·s⁻¹`, `u₂ = r·s⁻¹`,
`G` the base point, `Q` the public key) and accepts iff `R'.x mod n = r`. The
group computation `u₁·G + u₂·Q` is exactly a 2-term MSM: two scalar-mul leaves
accumulated by one point-add leaf. We emit it as a straight-line `Com` and prove
its denotation through `jasminDenoteWith leafSem` is
`prims.pointAdd (prims.scalarMul u₁ G) (prims.scalarMul u₂ Q)` under
`EcLeafAgrees prims leafSem`. The final `x mod n = r` check is the caller's
equality test on the denoted point. -/

/-- ECDSA verify, the recomputed point `R' = u₁·G + u₂·Q` — the **hand shadow**. A
    straight-line `Com`: two scalar-mul leaves (`u₁·G`, `u₂·Q`) then one point-add
    leaf. ABI: `Γ = [u₁, G, u₂, Q]` (scalar, point, scalar, point). -/
def ecdsaVerifyComShadow :
    Com jasminDialect
      [.stackArr 8 FESZ, .stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ]
      (.stackArr 8 PTSZ) :=
  -- Γ0 = [u1, G, u2, Q]
  .var (mulLeafExpr
          (Γ := [.stackArr 8 FESZ, .stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ])
          .here (.there .here))                                 -- t1 = u1·G
    -- Γ1 = [t1, u1, G, u2, Q]
    (.var (mulLeafExpr
            (Γ := [.stackArr 8 PTSZ, .stackArr 8 FESZ, .stackArr 8 PTSZ,
                   .stackArr 8 FESZ, .stackArr 8 PTSZ])
            (.there (.there (.there .here)))                    -- u2
            (.there (.there (.there (.there .here)))))          -- Q
      -- Γ2 = [t2, t1, u1, G, u2, Q]
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

/-- **The deployed ECDSA verifier, evaluated with a leaf oracle.** For a leaf
    oracle `leafSem` realising the secp256k1 primitives
    (`EcLeafAgrees prims leafSem`), the recomputed point `R' = u₁·G + u₂·Q` of
    `ecdsaVerifyCom`, denoted through `jasminDenoteWith leafSem`, is
    `prims.pointAdd (prims.scalarMul u₁ G) (prims.scalarMul u₂ Q)`: the 2-term MSM
    (`msm` at `L = 2`) at the leaf level. The verifier accepts iff
    `R'.x mod n = r` (the caller's equality test). -/
theorem ecdsaVerifyCom_denote (leafSem : LeafSem) (prims : Secp256k1Primitives)
    (hLeaf : EcLeafAgrees prims leafSem)
    (u1 : Fin FESZ → BitVec 8) (G : Fin PTSZ → BitVec 8)
    (u2 : Fin FESZ → BitVec 8) (Q : Fin PTSZ → BitVec 8) :
    @Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
        ecdsaVerifyCom (.cons u1 (.cons G (.cons u2 (.cons Q .nil))))
      = prims.pointAdd (prims.scalarMul u1 G) (prims.scalarMul u2 Q) := by
  rw [ecdsaVerifyCom_eq_shadow]
  obtain ⟨hAdd, hMul⟩ := hLeaf
  show leafSem addLeafName addArgTys ptRetTy
        (.cons (leafSem mulLeafName mulArgTys ptRetTy (.cons u1 (.cons G .nil)))
          (.cons (leafSem mulLeafName mulArgTys ptRetTy (.cons u2 (.cons Q .nil)))
            .nil))
      = prims.pointAdd (prims.scalarMul u1 G) (prims.scalarMul u2 Q)
  rw [hMul (.cons u1 (.cons G .nil)), hMul (.cons u2 (.cons Q .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hAdd (.cons (prims.scalarMul u1 G) (.cons (prims.scalarMul u2 Q) .nil))]
  rfl

end CatCrypt.Crypto.Pairing.Secp256k1Emit
