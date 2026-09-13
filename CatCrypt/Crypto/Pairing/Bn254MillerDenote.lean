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
the fused-line Miller doubling step (`millerDoubleStepCom`) — are denoted here
against an **abstract** leaf oracle `leafSem : LeafSem`, threaded through the
`DialectDenote jasminDialect` instance `JasminDialect.jasminDenoteWith leafSem`
(whose `extCall` arm consults `leafSem` and whose every other arm delegates to
`jasminDenote`).

* `bn254MillerOracle prims` — a concrete leaf oracle realising the BN254
  pairing-algorithm tower primitives (the `Fp2` add / square / inverse / multiply
  leaves, the sparse `make_line`, and the `Fp12` square / multiply / conjugate /
  Frobenius / cyclotomic-square leaves), with `bn254MillerOracle_agrees` proving
  it satisfies `Bn254MillerLeavesAgree`.
* `cycloPowStepCom_denoteWith` / `finalExpEasyCom_denoteWith` /
  `millerDoubleStepCom_denoteWith` — each deployed kernel, evaluated with any leaf
  oracle realising the tower primitives, computes its abstract algorithmic step.
* `bn254MillerLeafOracle` / `bn254MillerLeafOracle_agrees` — the leaf oracle for
  the deployed primitives and its agreement, a named axiom (the leaf edge; a leaf
  proof or a jasmin/AUCurves bridge would establish it).
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

/-! ## 2. Value of the deployed kernels under a realising leaf oracle -/

/-- **The deployed cyclotomic pow-step, evaluated with a leaf oracle.** For a leaf
    oracle realising the tower primitives, `cycloPowStepCom` — denoted through
    `jasminDenoteWith leafSem` — computes `fp12Mul (fp12CycloSquare r) base`, one
    square-and-multiply iteration with the compressed cyclotomic square. -/
theorem cycloPowStepCom_denoteWith (leafSem : LeafSem) (prims : Bn254MillerPrimitives)
    (h : Bn254MillerLeavesAgree prims leafSem)
    (r base : Fin GTSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        cycloPowStepCom (.cons r (.cons base .nil))
      = prims.fp12Mul (prims.fp12CycloSquare r) base := by
  rw [cycloPowStepCom_eq_shadow]
  show leafSem fp12MulLeafName fp12MulArgTys gtRetTy
        (.cons (leafSem fp12CycloSquareLeafName fp12UnArgTys gtRetTy (.cons r .nil))
          (.cons base .nil))
      = prims.fp12Mul (prims.fp12CycloSquare r) base
  rw [h.fp12CycloSquare (.cons r .nil)]
  simp only [HVector.head]
  rw [h.fp12Mul (.cons (prims.fp12CycloSquare r) (.cons base .nil))]
  rfl

/-- **The deployed final-exp easy part, evaluated with a leaf oracle.** For a leaf
    oracle realising the tower primitives, `finalExpEasyCom` — denoted through
    `jasminDenoteWith leafSem` — computes `r · frob²(r)` with `r = conj(f)·conj(f)`. -/
theorem finalExpEasyCom_denoteWith (leafSem : LeafSem) (prims : Bn254MillerPrimitives)
    (h : Bn254MillerLeavesAgree prims leafSem)
    (f : Fin GTSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        finalExpEasyCom (.cons f .nil)
      = (let cf := prims.fp12Conj f
         let r  := prims.fp12Mul cf cf
         prims.fp12Mul r (prims.fp12Frob (prims.fp12Frob r))) := by
  rw [finalExpEasyCom_eq_shadow]
  show leafSem fp12MulLeafName fp12MulArgTys gtRetTy
        (.cons (leafSem fp12MulLeafName fp12MulArgTys gtRetTy
                  (.cons (leafSem fp12ConjLeafName fp12UnArgTys gtRetTy (.cons f .nil))
                    (.cons (leafSem fp12ConjLeafName fp12UnArgTys gtRetTy (.cons f .nil)) .nil)))
          (.cons (leafSem fp12FrobLeafName fp12UnArgTys gtRetTy
                    (.cons (leafSem fp12FrobLeafName fp12UnArgTys gtRetTy
                              (.cons (leafSem fp12MulLeafName fp12MulArgTys gtRetTy
                                        (.cons (leafSem fp12ConjLeafName fp12UnArgTys gtRetTy (.cons f .nil))
                                          (.cons (leafSem fp12ConjLeafName fp12UnArgTys gtRetTy (.cons f .nil)) .nil))) .nil)) .nil)) .nil))
      = _
  rw [h.fp12Conj (.cons f .nil)]
  simp only [HVector.head]
  rw [h.fp12Mul (.cons (prims.fp12Conj f) (.cons (prims.fp12Conj f) .nil))]
  simp only [HVector.head, HVector.tail]
  rw [h.fp12Frob (.cons (prims.fp12Mul (prims.fp12Conj f) (prims.fp12Conj f)) .nil)]
  simp only [HVector.head]
  rw [h.fp12Frob (.cons (prims.fp12Frob (prims.fp12Mul (prims.fp12Conj f) (prims.fp12Conj f))) .nil)]
  simp only [HVector.head]
  exact h.fp12Mul _

/-- **The deployed fused-line Miller doubling step, evaluated with a leaf oracle.**
    For a leaf oracle realising the tower primitives, `millerDoubleStepCom` —
    denoted through `jasminDenoteWith leafSem` — computes the abstract doubling
    step `f² · make_line(λ, tₓ, t_y, pₓ, p_y)` with `λ = 3·tₓ² · (2·t_y)⁻¹`. -/
theorem millerDoubleStepCom_denoteWith (leafSem : LeafSem) (prims : Bn254MillerPrimitives)
    (h : Bn254MillerLeavesAgree prims leafSem)
    (f : Fin GTSZ → BitVec 8) (tx ty : Fin FP2SZ → BitVec 8)
    (px py : Fin FPSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        millerDoubleStepCom (.cons f (.cons tx (.cons ty (.cons px (.cons py .nil)))))
      = (let tx2  := prims.fp2Square tx
         let lamN := prims.fp2Add (prims.fp2Add tx2 tx2) tx2
         let tyI  := prims.fp2Inv (prims.fp2Add ty ty)
         let lam  := prims.fp2Mul lamN tyI
         let line := prims.makeLine lam tx ty px py
         prims.fp12Mul (prims.fp12Square f) line) := by
  rw [millerDoubleStepCom_eq_shadow]
  have hLHS : @Com.denote _ _ _ (JasminDialect.jasminDenoteWith leafSem) _ _
        millerDoubleStepComShadow
        (.cons f (.cons tx (.cons ty (.cons px (.cons py .nil)))))
      = leafSem fp12MulLeafName fp12MulArgTys gtRetTy
          (.cons (leafSem fp12SquareLeafName fp12UnArgTys gtRetTy (.cons f .nil))
            (.cons (leafSem makeLineLeafName makeLineArgTys gtRetTy
              (.cons (leafSem fp2MulLeafName fp2BinArgTys fp2RetTy
                (.cons (leafSem fp2AddLeafName fp2BinArgTys fp2RetTy
                  (.cons (leafSem fp2AddLeafName fp2BinArgTys fp2RetTy
                    (.cons (leafSem fp2SquareLeafName fp2UnArgTys fp2RetTy (.cons tx .nil))
                      (.cons (leafSem fp2SquareLeafName fp2UnArgTys fp2RetTy (.cons tx .nil)) .nil)))
                    (.cons (leafSem fp2SquareLeafName fp2UnArgTys fp2RetTy (.cons tx .nil)) .nil)))
                  (.cons (leafSem fp2InvLeafName fp2UnArgTys fp2RetTy
                    (.cons (leafSem fp2AddLeafName fp2BinArgTys fp2RetTy
                      (.cons ty (.cons ty .nil))) .nil)) .nil)))
                (.cons tx (.cons ty (.cons px (.cons py .nil)))))) .nil)) := rfl
  rw [hLHS]
  exact (h.fp12Mul _).trans (congrArg₂ prims.fp12Mul (h.fp12Square _)
    ((h.makeLine _).trans (congrArg (fun l => prims.makeLine l tx ty px py)
      ((h.fp2Mul _).trans (congrArg₂ prims.fp2Mul
        ((h.fp2Add _).trans (congrArg₂ prims.fp2Add
          ((h.fp2Add _).trans (congrArg₂ prims.fp2Add (h.fp2Square _) (h.fp2Square _)))
          (h.fp2Square _)))
        ((h.fp2Inv _).trans (congrArg prims.fp2Inv (h.fp2Add _))))))))

/-! ## 3. The deployed leaf oracle + the kernels at that oracle -/

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

/-- The leaf oracle for the deployed primitives,
    `bn254MillerOracle deployedMillerPrims` sealed as `opaque`; the seal keeps the
    agreement below a named hypothesis. -/
opaque bn254MillerLeafOracle : LeafSem := bn254MillerOracle deployedMillerPrims

/-- The leaf agreement: the deployed leaf oracle realises the BN254 tower
    primitives. A named axiom. Establishing it means bridging the emitted leaf to
    the primitive spec — a leaf proof, or a jasmin/AUCurves bridge — which this
    file does not do. -/
axiom bn254MillerLeafOracle_agrees :
    Bn254MillerLeavesAgree deployedMillerPrims bn254MillerLeafOracle

/-- **The deployed cyclotomic pow-step at the deployed oracle.** Denoted through
    `jasminDenoteWith bn254MillerLeafOracle`, `cycloPowStepCom` computes
    `fp12Mul (fp12CycloSquare r) base`. The orchestration is Lean-proven; the only
    assumption is the leaf trust edge `bn254MillerLeafOracle_agrees`. -/
theorem cycloPowStepCom_denote (r base : Fin GTSZ → BitVec 8) :
    @Com.denote _ _ _ (JasminDialect.jasminDenoteWith bn254MillerLeafOracle) _ _
        cycloPowStepCom (.cons r (.cons base .nil))
      = deployedMillerPrims.fp12Mul (deployedMillerPrims.fp12CycloSquare r) base :=
  cycloPowStepCom_denoteWith bn254MillerLeafOracle deployedMillerPrims
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
  finalExpEasyCom_denoteWith bn254MillerLeafOracle deployedMillerPrims
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
  millerDoubleStepCom_denoteWith bn254MillerLeafOracle deployedMillerPrims
    bn254MillerLeafOracle_agrees f tx ty px py

end CatCrypt.Crypto.Pairing.Bn254MillerDenote
