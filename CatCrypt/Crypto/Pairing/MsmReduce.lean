/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import CatCrypt.Crypto.SecureCompilation.VIR.VectorReduce
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront

/-!
# The pairing-ZK shared hot kernel: multi-scalar multiplication (MSM) over an EC group

The shared prover/commitment computation of the pairing-based zero-knowledge systems —
**Groth16**, **KZG**, and **Bulletproofs** — is a single hot computation: a
**multi-scalar multiplication**
`MSM(k, P) = Σ_{i=0}^{L-1} k_i · P_i`
over an elliptic-curve group, where each `k_i` is a scalar and each `P_i` an EC
point. Groth16's proof is three group elements assembled from MSMs over the SRS;
KZG's commitment `C = Σ_i φ_i · [τ^i]₁` is an MSM over the powers-of-τ; a
Bulletproofs round computes `L_i, R_i` as `n/2`-length MSMs over the generator
vectors (`CatCrypt/Crypto/Jasmin/Bulletproofs.lean`, the inner-product argument).

## No new machinery — MSM is the committed `scalarFold` reduction at a new lane

An MSM is a **reduction over the EC group**, not new content. Each term `k_i · P_i`
is an EC *scalar-multiply* (the lane op); the terms are accumulated by EC
*point-add* (the horizontal-sum op). That is exactly the
`VectorReduce.scalarFold_eq_hsum` core — the verified heart of the vectorizer —
instantiated at the EC-group lane: the lane type is an `AddCommMonoid` (the EC
group is an `AddCommGroup`, hence `AddCommMonoid`), which is the *only* algebraic
fact the reduction needs (associativity + commutativity let the accumulation
reassociate/reorder). So:

* the **GF(2^128)** dot (FAEST QuickSilver,
  `FAEST/GlueVectorization.quicksilver_dot_vectorizes`) is `scalarFold_eq_hsum` at
  the GF(2^128) *ring* lane;
* the **Frodo matmul** row (`VectorReduce.vmul_hsum_eq_scalarFold`) is it at the
  `BitVec 16` *ring* lane;
* the **MSM** here is the *same theorem* at the EC-*group* lane — the "7th lane"
  is an additive group, the per-term op is scalar-multiply `k_i • P_i` rather
  than a ring product. `msm_eq_scalarFold` below is that instantiation; it carries
  **no new proof obligation** beyond the committed core.

## The concrete EC group (the AddCommMonoid lane)

`ECPt a b := (toyW a b).toAffine.Point` is Mathlib's nonsingular-affine-point type
on a short-Weierstrass curve `y² = x³ + a·x + b` over the prime field
`Fp = ZMod 23`. Mathlib proves it an `AddCommGroup` for free (the affine group law);
that `AddCommGroup` is the `AddCommMonoid` the reduction core requires. This is a
**clearly-labelled small/model EC group** that *validates* the
"MSM = scalarFold over the EC AddCommMonoid" reduction (`msm_eq_scalarFold`).
It is the lattice/GF analogue: the production AUCurves/fiat BLS12-381 G1 (the
`scalar_mul` / `g1_add` leaves wired in `CatCrypt/Crypto/{KZG,ECDSA}`) is the same
shape at a 381-bit field; this file pins the reduction at a concrete field where
the EC ops are schoolbook modular arithmetic, so the emitted kernel + the C
reference are byte-identical (`bench/msm_compare/`).

## The EC leaf

The per-term scalar-multiply and the accumulating point-add are the protocol's
EC **leaf** — exactly the FAEST symmetric-leaf pattern (a leaf semantics plus
its agreement): the front-end emits them as opaque `extCall`s in the
Jasmin dialect, and the *agreement* (`EcLeafAgrees`) ties the opaque leaf
semantics to the abstract EC primitives. This is the same opaque-leaf edge every
emit-correctness theorem carries — never an admitted proof. The KAT under
`bench/msm_compare/` discharges it operationally: the emitted EC point-add /
scalar-mul leaves are byte-identical to a schoolbook EC reference over the same
small field.

The **pairing / Miller-loop** (needed for *verification* — `e(A,B)·e(C,D) = …`)
is a *separate* AUCurves leaf (`Jasmin/BLS12_381/EvalChain.lean`'s final-exp
chain is its post-processing); it is the remaining piece for full Groth16/KZG
*verify* and is out of scope here. This file is the *prover/commitment* MSM
substrate the three systems share.

All goals closed; the only hypotheses are the opaque EC-leaf agreements
(`EcLeafAgrees`), the edge carried throughout this theory.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.MsmReduce

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VectorReduce
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
open WeierstrassCurve
open scoped BigOperators

/-! ## 1. The concrete EC group (the AddCommMonoid lane) -/

/-- The toy modulus: a small prime so `ZMod 23` is a field (and the EC affine
    group law / `AddCommGroup` on its points is available). -/
abbrev p : ℕ := 23

/-- `Nat.Prime 23` — discharged by `decide` (small prime), unlocking
    `Field (ZMod 23)`. -/
theorem p_prime : Nat.Prime p := by decide

/-- Register primality as a typeclass fact, unlocking `Field (ZMod 23)` and hence
    the affine-point `AddCommGroup`. -/
instance factP : Fact (Nat.Prime p) := ⟨p_prime⟩

/-- The toy base field `Fp = ZMod 23` (a `Field` via `factP`). -/
abbrev Fp : Type := ZMod p

/-- A short-Weierstrass curve `y² = x³ + a·x + b` over `Fp` (the `a₁=a₂=a₃=0`
    form), as a Mathlib `WeierstrassCurve`. -/
noncomputable def toyW (a b : Fp) : WeierstrassCurve Fp where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := a
  a₆ := b

/-- **The EC-group lane.** The nonsingular affine points of the toy curve —
    Mathlib's `WeierstrassCurve.Affine.Point`, which carries a proved
    `AddCommGroup` (the affine group law). This `AddCommGroup` *is* the
    `AddCommMonoid` the `scalarFold` reduction core needs; it is the concrete EC
    group the MSM accumulates over. -/
abbrev ECPt (a b : Fp) : Type := (toyW a b).toAffine.Point

/-- The EC group is an `AddCommGroup` (free from Mathlib). -/
noncomputable example (a b : Fp) : AddCommGroup (ECPt a b) := inferInstance

/-- Hence an `AddCommMonoid` — the lane structure the reduction core requires. -/
noncomputable example (a b : Fp) : AddCommMonoid (ECPt a b) := inferInstance

/-! ## 2. The MSM and its reduction to `scalarFold`

`MSM(k, P) = Σ_i k_i · P_i` where `k_i · P_i` is EC scalar-mul (`nsmul`, the lane
op `•`) and `Σ` is iterated EC point-add (the horizontal sum `hsum`). The
straight-line emitter computes this as the sequential left-fold `scalarFold` over
the per-term scalar-multiples; the SIMD/parallel realization reassociates into a
tree `hsum`. They agree because the EC group is an `AddCommMonoid`. -/

/-- The multi-scalar multiplication as the **horizontal reduction** `hsum` over
    the EC group of the per-term scalar-multiples `k_i • P_i` — the mathematical
    value `Σ_i k_i · P_i` the parallel/tree realization computes. -/
noncomputable def msm {a b : Fp} {L : ℕ} (k : Fin L → ℕ) (P : Fin L → ECPt a b) :
    ECPt a b :=
  hsum (fun i => (k i) • (P i))

/-- The MSM as the **sequential left-fold** `scalarFold` the straight-line emitter
    produces: `((0 + k₀·P₀) + k₁·P₁) + ⋯`, EC point-adds threaded left to right. -/
noncomputable def msmFold {a b : Fp} {L : ℕ} (k : Fin L → ℕ) (P : Fin L → ECPt a b) :
    ECPt a b :=
  scalarFold (fun i => (k i) • (P i))

/-- **MSM reduction.** The MSM reduces to `scalarFold` over the EC
    `AddCommMonoid`: the sequential left-fold of the EC scalar-multiples
    (`msmFold`, what the straight-line emitter produces) equals their horizontal
    reduction (`msm`, what a packed scalar-mul + tree point-add computes). This is
    `VectorReduce.scalarFold_eq_hsum` instantiated at the EC-group lane — **no new
    content**: the EC group's `AddCommMonoid` laws (associativity + commutativity)
    are exactly what let the accumulation reassociate/reorder. The pairing-ZK
    substrate (Groth16 / KZG / Bulletproofs all assemble their proofs/commitments
    from MSMs) is therefore the committed `scalarFold` reduction at a new lane. -/
theorem msm_eq_scalarFold {a b : Fp} {L : ℕ} (k : Fin L → ℕ) (P : Fin L → ECPt a b) :
    msmFold k P = msm k P :=
  scalarFold_eq_hsum (fun i => (k i) • (P i))

/-- The MSM computes the mathematical multi-scalar multiplication `Σ_i k_i · P_i`
    (the spec Groth16 / KZG / Bulletproofs need their commitments to realize). -/
theorem msm_isSum {a b : Fp} {L : ℕ} (k : Fin L → ℕ) (P : Fin L → ECPt a b) :
    msm k P = ∑ i, (k i) • (P i) := by
  simp only [msm, hsum]

/-- The per-term EC scalar-multiplies are a pure lane-wise map (each term
    independent), so packing the `(k_i, P_i)` pairs and applying scalar-mul
    lane-wise computes exactly the per-term scalar-multiples — trivially
    denotation-preserving, no reassociation (the reduction `msm_eq_scalarFold` is
    where the `AddCommMonoid` laws are used). -/
theorem msm_lanewise {a b : Fp} {L : ℕ} (k : Fin L → ℕ) (P : Fin L → ECPt a b)
    (i : Fin L) :
    (fun j => (k j) • (P j)) i = (k i) • (P i) := rfl

/-! ## 3. The EC leaf spec (opaque `extCall`, carried agreement)

The per-term scalar-multiply and the accumulating point-add are the EC **leaf**.
We declare the leaf spec in the FAEST leaf shape: a named-leaf
semantics carrier (`EcLeafSem`, same shape as `jasminExtSem`), the abstract EC
primitives (`EcPrimitives`), and the agreement (`EcLeafAgrees`) tying the opaque
leaf to those primitives. The leaf is *opaque*; its agreement is the carried
obligation, never an admitted proof. -/

/-- The leaf name the front-end emits for the EC point-add (the accumulator op). -/
def ecAddLeafName : String := "ec_point_add"

/-- The leaf name the front-end emits for the EC scalar-multiply (the per-term op). -/
def ecMulLeafName : String := "ec_scalar_mul"

/-- An EC point on the wire: `WSZ`-byte little-endian affine coordinates
    `(x ‖ y)`, a `2·WSZ`-byte stack array. `WSZ` is the per-coordinate byte width
    (for the toy field, 1 byte suffices; for BLS12-381 G1 it is 48). -/
def WSZ : Nat := 1

/-- Dialect signature of the EC point-add leaf:
    `(P : stackArr 8 (2·WSZ), Q : stackArr 8 (2·WSZ)) → R : stackArr 8 (2·WSZ)`. -/
def ecAddArgTys : List JasminTy := [.stackArr 8 (2 * WSZ), .stackArr 8 (2 * WSZ)]

/-- Return type of the EC point-add leaf (one curve point). -/
def ecAddRetTy : JasminTy := .stackArr 8 (2 * WSZ)

/-- Dialect signature of the EC scalar-multiply leaf:
    `(k : stackArr 8 WSZ, P : stackArr 8 (2·WSZ)) → R : stackArr 8 (2·WSZ)`. -/
def ecMulArgTys : List JasminTy := [.stackArr 8 WSZ, .stackArr 8 (2 * WSZ)]

/-- Return type of the EC scalar-multiply leaf (one curve point). -/
def ecMulRetTy : JasminTy := .stackArr 8 (2 * WSZ)

/-- External-leaf semantics carrier: the exact shape of `jasminExtSem`
    (and `FaestLeafSem`), opaque. A concrete binding (the validated EC leaves) is
    a value of this type. -/
abbrev EcLeafSem : Type :=
  (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
    HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧

/-- The abstract EC-primitive interface the MSM orchestrates: a point-add and a
    scalar-multiply on the on-wire `2·WSZ`-byte point representation. The MSM
    security/correctness reasons against this interface; the KAT confirms the
    bound leaves realise it (schoolbook EC over the same field, byte-identical). -/
structure EcPrimitives where
  /-- EC point addition `P + Q` on the wire representation. -/
  pointAdd : (Fin (2 * WSZ) → BitVec 8) → (Fin (2 * WSZ) → BitVec 8) →
    (Fin (2 * WSZ) → BitVec 8)
  /-- EC scalar multiplication `k · P` (scalar `k` as `WSZ` bytes, point `P` as
      `2·WSZ` bytes). -/
  scalarMul : (Fin WSZ → BitVec 8) → (Fin (2 * WSZ) → BitVec 8) →
    (Fin (2 * WSZ) → BitVec 8)

/-- EC point-add leaf agreement: on the `ec_point_add` signature, the leaf
    semantics is `prims.pointAdd` of its two point arguments. -/
def EcAddLeafAgrees (prims : EcPrimitives) (leafSem : EcLeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) ecAddArgTys,
    leafSem ecAddLeafName ecAddArgTys ecAddRetTy args
      = prims.pointAdd (args.head) (args.tail.head)

/-- EC scalar-multiply leaf agreement: on the `ec_scalar_mul` signature, the leaf
    semantics is `prims.scalarMul` of its scalar and point arguments. -/
def EcMulLeafAgrees (prims : EcPrimitives) (leafSem : EcLeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) ecMulArgTys,
    leafSem ecMulLeafName ecMulArgTys ecMulRetTy args
      = prims.scalarMul (args.head) (args.tail.head)

/-- The full EC-leaf agreement: `leafSem` realises both EC primitives on both
    leaf names. The validated schoolbook EC point-add + scalar-mul leaves are the
    intended witness (`bench/msm_compare/`). -/
def EcLeafAgrees (prims : EcPrimitives) (leafSem : EcLeafSem) : Prop :=
  EcAddLeafAgrees prims leafSem ∧ EcMulLeafAgrees prims leafSem

/-! ## 4. Leaf `Expr` builders + denotation (the `extCall` bridge point) -/

/-- Build the EC point-add leaf `Expr` from two point variables in scope. -/
def ecAddLeafExpr {Γ : Ctxt jasminDialect}
    (P Q : Ctxt.Var Γ (.stackArr 8 (2 * WSZ))) :
    Expr jasminDialect Γ ecAddRetTy :=
  { op := .extCall ecAddLeafName ecAddArgTys ecAddRetTy
    retTy_eq := rfl
    args := .cons P (.cons Q .nil) }

/-- Build the EC scalar-multiply leaf `Expr` from a scalar variable and a point
    variable in scope. -/
def ecMulLeafExpr {Γ : Ctxt jasminDialect}
    (k : Ctxt.Var Γ (.stackArr 8 WSZ)) (P : Ctxt.Var Γ (.stackArr 8 (2 * WSZ))) :
    Expr jasminDialect Γ ecMulRetTy :=
  { op := .extCall ecMulLeafName ecMulArgTys ecMulRetTy
    retTy_eq := rfl
    args := .cons k (.cons P .nil) }

/-- Denoted through `jasminDenoteWith leafSem`, the EC point-add leaf `Expr` is
    (under any valuation) `leafSem` of the looked-up points. By `rfl`;
    `EcAddLeafAgrees` at `leafSem` rewrites it to `prims.pointAdd`. -/
theorem ecAddLeafExpr_denote (leafSem : EcLeafSem) {Γ : Ctxt jasminDialect}
    (P Q : Ctxt.Var Γ (.stackArr 8 (2 * WSZ))) (V : Ctxt.Valuation Γ) :
    @Expr.denote _ _ _ (jasminDenoteWith leafSem) _ _ (ecAddLeafExpr P Q) V
      = leafSem ecAddLeafName ecAddArgTys ecAddRetTy
          (.cons (P.lookup V) (.cons (Q.lookup V) .nil)) :=
  rfl

/-- Denoted through `jasminDenoteWith leafSem`, the EC scalar-multiply leaf `Expr`
    is (under any valuation) `leafSem` of the looked-up scalar and point. By
    `rfl`. -/
theorem ecMulLeafExpr_denote (leafSem : EcLeafSem) {Γ : Ctxt jasminDialect}
    (k : Ctxt.Var Γ (.stackArr 8 WSZ)) (P : Ctxt.Var Γ (.stackArr 8 (2 * WSZ)))
    (V : Ctxt.Valuation Γ) :
    @Expr.denote _ _ _ (jasminDenoteWith leafSem) _ _ (ecMulLeafExpr k P) V
      = leafSem ecMulLeafName ecMulArgTys ecMulRetTy
          (.cons (k.lookup V) (.cons (P.lookup V) .nil)) :=
  rfl

/-! ## 5. A leaf-orchestrated MSM term, with the denotation carry

A single MSM term `k_i · P_i` accumulated into the running sum: `acc + (k · P)`.
`msmTermCom` is the orchestrating `Com` (one scalar-mul leaf, then one point-add
leaf); `msmTermCom_denote` proves its denotation through `jasminDenoteWith
leafSem` is `prims.pointAdd acc (prims.scalarMul k P)` for every leaf oracle
`leafSem` satisfying `EcLeafAgrees` — exactly the
`scalarFold` step `acc + k_i • P_i`, at the leaf level. The full straight-line
MSM is this step folded `L` times, matched at the EC-group lane by
`msm_eq_scalarFold`. -/

/-- One MSM step as an orchestrating `Com` over `(acc, k, P)` — the **hand
    shadow** (the denote reference): first the EC scalar-multiply leaf
    `t = ec_scalar_mul(k, P)`, then the EC point-add leaf `out = ec_point_add(acc,
    t)`. This is the `scalarFold` body `acc ↦ acc + k_i • P_i` built from the two
    EC leaves. -/
def msmTermComShadow :
    Com jasminDialect
      [.stackArr 8 (2 * WSZ), .stackArr 8 WSZ, .stackArr 8 (2 * WSZ)]
      (.stackArr 8 (2 * WSZ)) :=
  -- Γ = [acc, k, P]
  .var (ecMulLeafExpr
          (Γ := [.stackArr 8 (2 * WSZ), .stackArr 8 WSZ, .stackArr 8 (2 * WSZ)])
          (.there .here) (.there (.there .here)))
    -- Γ' = [t, acc, k, P]
    (.var (ecAddLeafExpr
            (Γ := [.stackArr 8 (2 * WSZ), .stackArr 8 (2 * WSZ),
                   .stackArr 8 WSZ, .stackArr 8 (2 * WSZ)])
            (.there .here) .here)
      (.ret .here))

/-- The input context of the MSM-step kernel: `[acc, k, P]`. -/
def msmTermCtxt : Ctxt jasminDialect :=
  [.stackArr 8 (2 * WSZ), .stackArr 8 WSZ, .stackArr 8 (2 * WSZ)]

/-- The MSM-step kernel as an `OrchestrationFront` phase schedule over `[acc, k,
    P]`. Root slots on the inputs: `acc = 2, k = 1, P = 0`.
    `t = ec_scalar_mul(k, P)` (slots `[1, 0]`, result slot `3`),
    `out = ec_point_add(acc, t)` (slots `[2, 3]`, result slot `4`, returned). -/
def msmTermSchedule : List CallPhase :=
  [ { leaf := ecMulLeafName, argTys := ecMulArgTys, retTy := ecMulRetTy, argSlots := [1, 0] }
  , { leaf := ecAddLeafName, argTys := ecAddArgTys, retTy := ecAddRetTy, argSlots := [2, 3] } ]

/-- **Generation gate.** The front resolves the MSM-step schedule. -/
theorem msmTermCom_isSome :
    (buildOrchCom msmTermCtxt msmTermSchedule 4 (.stackArr 8 (2 * WSZ))).isSome = true := by
  rfl

/-- **The deployed MSM-step kernel, front-sourced** by `buildOrchCom` from
    `msmTermSchedule`. Definitionally the hand shadow (`msmTermCom_eq_shadow`). -/
def msmTermCom :
    Com jasminDialect
      [.stackArr 8 (2 * WSZ), .stackArr 8 WSZ, .stackArr 8 (2 * WSZ)]
      (.stackArr 8 (2 * WSZ)) :=
  (buildOrchCom msmTermCtxt msmTermSchedule 4 (.stackArr 8 (2 * WSZ))).get msmTermCom_isSome

/-- **Exactness.** The front-sourced deployed `msmTermCom` is definitionally the
    hand shadow — the auto-resolved de-Bruijn operand chains coincide with the
    hand-threaded `.here`/`.there` chains. -/
theorem msmTermCom_eq_shadow : msmTermCom = msmTermComShadow := by rfl

/-- **The deployed MSM step, evaluated with a leaf oracle.** For a leaf oracle
    `leafSem` realising the EC primitives (`EcLeafAgrees prims leafSem`), the
    deployed `msmTermCom`, denoted through `jasminDenoteWith leafSem`, computes
    `prims.pointAdd acc (prims.scalarMul k P)`: the running-accumulator step
    `acc + k·P` of the left-fold. The scalar-mul and point-add `extCall` arms each
    unfold to a `leafSem` call, and the two agreements rewrite them to the abstract
    EC primitives. The leaf model is the parameter `leafSem`; `MsmReduceDenote`
    instantiates it at a concrete oracle. -/
theorem msmTermCom_denote (leafSem : EcLeafSem) (prims : EcPrimitives)
    (hLeaf : EcLeafAgrees prims leafSem)
    (acc : Fin (2 * WSZ) → BitVec 8) (k : Fin WSZ → BitVec 8)
    (P : Fin (2 * WSZ) → BitVec 8) :
    @Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
        msmTermCom (.cons acc (.cons k (.cons P .nil)))
      = prims.pointAdd acc (prims.scalarMul k P) := by
  rw [msmTermCom_eq_shadow]
  obtain ⟨hAdd, hMul⟩ := hLeaf
  show leafSem ecAddLeafName ecAddArgTys ecAddRetTy
        (.cons acc (.cons (leafSem ecMulLeafName ecMulArgTys ecMulRetTy
                            (.cons k (.cons P .nil))) .nil))
      = prims.pointAdd acc (prims.scalarMul k P)
  rw [hMul (.cons k (.cons P .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hAdd (.cons acc (.cons (prims.scalarMul k P) .nil))]
  rfl

end CatCrypt.Crypto.Pairing.MsmReduce
