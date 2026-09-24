/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Pairing.Bn254MillerEmit

/-!
# BN254 Miller / final-exponentiation kernels: leaf-oracle-parametric denotation

The three deployed `Bn254MillerEmit` kernels — the cyclotomic `pow_u` step
(`cycloPowStepCom`), the final-exponentiation easy part (`finalExpEasyCom`), and
the fused-line Miller doubling step (`millerDoubleStepCom`) — are denoted by the
`Bn254MillerEmit.*Com_denote` theorems against a leaf oracle `leafSem : LeafSem`
passed as a parameter, threaded through the `DialectDenote jasminDialect` instance
`JasminDialect.jasminDenoteWith leafSem` (whose `extCall` arm consults `leafSem`
and whose every other arm delegates to `jasminDenote`). This module supplies the
oracles that parameter is instantiated at.

* `bn254MillerOracle prims` — a concrete leaf oracle realising the BN254
  pairing-algorithm tower primitives (the `Fp2` add / square / inverse / multiply
  leaves, the sparse `make_line`, and the `Fp12` square / multiply / conjugate /
  Frobenius / cyclotomic-square leaves), with `bn254MillerOracle_agrees` proving
  it satisfies `Bn254MillerLeavesAgree`, so the hypothesis of the
  `Bn254MillerEmit` denotation theorems is satisfiable for every `prims`.
* `bn254MillerLeafOracle` / `bn254MillerLeafOracle_agrees` — the leaf oracle for
  the deployed primitives, defined as `bn254MillerOracle deployedMillerPrims`, and
  its agreement, a theorem that holds by construction of the oracle. It relates
  the oracle to the primitives and says nothing about the emitted leaf code.
* `cycloPowStepCom_denote` / `finalExpEasyCom_denote` / `millerDoubleStepCom_denote`
  — each deployed kernel at the deployed oracle.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Bn254MillerDenote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Pairing.Bn254Emit
open CatCrypt.Crypto.Pairing.Bn254MillerEmit

/-! ## 1. A concrete leaf oracle realising the pairing-algorithm primitives -/

/-- A leaf oracle realising the BN254 Miller / final-exp tower primitives. On each
    tower-leaf signature it selects the intended abstract primitive by name — the
    `Fp2` binary leaves (`add` / `mul`, both `[64, 64] → 64`), the `Fp2` unary
    leaves (`square` / `inv`, both `[64] → 64`), the sparse-line leaf
    (`[64, 64, 64, 32, 32] → 384`), the `Fp12` unary leaves (`square` / `conjugate`
    / `frobenius` / `cyclotomic_square`, all `[384] → 384`), and the `Fp12` binary
    multiply (`[384, 384] → 384`) — and is `JasminTy.default` on any other leaf.
    This inhabits `LeafSem` — the shape a validated AUCurves binding takes. -/
def bn254MillerOracle (prims : Bn254MillerPrimitives) : LeafSem :=
  fun name argTys retTy =>
    match argTys, retTy with
    | [.stackArr 8 64, .stackArr 8 64], .stackArr 8 64 =>
        fun args =>
          if name = fp2AddLeafName then prims.fp2Add args.head args.tail.head
          else prims.fp2Mul args.head args.tail.head
    | [.stackArr 8 64], .stackArr 8 64 =>
        fun args =>
          if name = fp2SquareLeafName then prims.fp2Square args.head
          else prims.fp2Inv args.head
    | [.stackArr 8 64, .stackArr 8 64, .stackArr 8 64, .stackArr 8 32, .stackArr 8 32],
        .stackArr 8 384 =>
        fun args =>
          prims.makeLine args.head args.tail.head args.tail.tail.head
            args.tail.tail.tail.head args.tail.tail.tail.tail.head
    | [.stackArr 8 384], .stackArr 8 384 =>
        fun args =>
          if name = fp12SquareLeafName then prims.fp12Square args.head
          else if name = fp12ConjLeafName then prims.fp12Conj args.head
          else if name = fp12FrobLeafName then prims.fp12Frob args.head
          else prims.fp12CycloSquare args.head
    | [.stackArr 8 384, .stackArr 8 384], .stackArr 8 384 =>
        fun args => prims.fp12Mul args.head args.tail.head
    | _, retTy => fun _ => JasminTy.default retTy

/-- `bn254MillerOracle prims` realises the tower primitives: it satisfies
    `Bn254MillerLeavesAgree prims` — by `rfl` in each component, because each
    tower-leaf signature (and, within a shared signature, its name) selects the
    intended match arm. -/
theorem bn254MillerOracle_agrees (prims : Bn254MillerPrimitives) :
    Bn254MillerLeavesAgree prims (bn254MillerOracle prims) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro args; rfl)

/-! ## 2. The deployed leaf oracle + the kernels at that oracle -/

/-- `Bn254MillerPrimitives` is inhabited (every field is a function into
    `BitVec 8`), so the deployed primitives can be introduced as an opaque
    constant. -/
instance : Inhabited Bn254MillerPrimitives :=
  ⟨{ fp2Add := fun _ _ _ => 0, fp2Square := fun _ _ => 0, fp2Inv := fun _ _ => 0,
     fp2Mul := fun _ _ _ => 0, makeLine := fun _ _ _ _ _ _ => 0,
     fp12Square := fun _ _ => 0, fp12Mul := fun _ _ _ => 0, fp12Conj := fun _ _ => 0,
     fp12Frob := fun _ _ => 0, fp12CycloSquare := fun _ _ => 0 }⟩

/-- An abstract constant standing for the BN254 tower primitives the deployed code
    targets. Opaque — uninterpreted for proofs. -/
opaque deployedMillerPrims : Bn254MillerPrimitives

/-- The leaf oracle for the deployed primitives, `bn254MillerOracle deployedMillerPrims`. Opaque, so the kernel
    does not unfold it; `spec` carries its defining equation. -/
opaque bn254MillerLeafOracle.spec : { o : LeafSem // o = bn254MillerOracle deployedMillerPrims } := ⟨_, rfl⟩

/-- The deployed leaf oracle, `bn254MillerOracle deployedMillerPrims`, read through the opaque `bn254MillerLeafOracle.spec`. -/
def bn254MillerLeafOracle : LeafSem := bn254MillerLeafOracle.spec.val

/-- The deployed leaf oracle realises the BN254 tower primitives. It holds by
    construction: the oracle is defined from the primitives. Relating the
    emitted leaves to the primitives is a separate statement, not made here. -/
theorem bn254MillerLeafOracle_agrees :
    Bn254MillerLeavesAgree deployedMillerPrims bn254MillerLeafOracle := by
  rw [show bn254MillerLeafOracle = bn254MillerOracle deployedMillerPrims from bn254MillerLeafOracle.spec.property]
  exact bn254MillerOracle_agrees _

/-- **The deployed cyclotomic pow-step at the deployed oracle.** Denoted through
    `jasminDenoteWith bn254MillerLeafOracle`, `cycloPowStepCom` computes
    `fp12Mul (fp12CycloSquare r) base`: what the orchestration computes when each
    leaf computes its primitive. The statement carries no assumption; the leaf
    agreement `bn254MillerLeafOracle_agrees` holds by construction of the
    oracle. -/
theorem cycloPowStepCom_denote (r base : Fin GTSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bn254MillerLeafOracle) _ _
        cycloPowStepCom (.cons r (.cons base .nil))
      = deployedMillerPrims.fp12Mul (deployedMillerPrims.fp12CycloSquare r) base :=
  Bn254MillerEmit.cycloPowStepCom_denote bn254MillerLeafOracle deployedMillerPrims
    bn254MillerLeafOracle_agrees r base

/-- **The deployed final-exp easy part at the deployed oracle.** Denoted through
    `jasminDenoteWith bn254MillerLeafOracle`, `finalExpEasyCom` computes
    `r · frob²(r)` with `r = conj(f)·conj(f)`. -/
theorem finalExpEasyCom_denote (f : Fin GTSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bn254MillerLeafOracle) _ _
        finalExpEasyCom (.cons f .nil)
      = (let cf := deployedMillerPrims.fp12Conj f
         let r  := deployedMillerPrims.fp12Mul cf cf
         deployedMillerPrims.fp12Mul r
           (deployedMillerPrims.fp12Frob (deployedMillerPrims.fp12Frob r))) :=
  Bn254MillerEmit.finalExpEasyCom_denote bn254MillerLeafOracle deployedMillerPrims
    bn254MillerLeafOracle_agrees f

/-- **The deployed fused-line Miller doubling step at the deployed oracle.**
    Denoted through `jasminDenoteWith bn254MillerLeafOracle`, `millerDoubleStepCom`
    computes `f² · make_line(λ, tₓ, t_y, pₓ, p_y)` with `λ = 3·tₓ² · (2·t_y)⁻¹`. -/
theorem millerDoubleStepCom_denote
    (f : Fin GTSZ → BitVec 8) (tx ty : Fin FP2SZ → BitVec 8)
    (px py : Fin FPSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bn254MillerLeafOracle) _ _
        millerDoubleStepCom (.cons f (.cons tx (.cons ty (.cons px (.cons py .nil)))))
      = (let tx2  := deployedMillerPrims.fp2Square tx
         let lamN := deployedMillerPrims.fp2Add (deployedMillerPrims.fp2Add tx2 tx2) tx2
         let tyI  := deployedMillerPrims.fp2Inv (deployedMillerPrims.fp2Add ty ty)
         let lam  := deployedMillerPrims.fp2Mul lamN tyI
         let line := deployedMillerPrims.makeLine lam tx ty px py
         deployedMillerPrims.fp12Mul (deployedMillerPrims.fp12Square f) line) :=
  Bn254MillerEmit.millerDoubleStepCom_denote bn254MillerLeafOracle deployedMillerPrims
    bn254MillerLeafOracle_agrees f tx ty px py

end CatCrypt.Crypto.Pairing.Bn254MillerDenote
