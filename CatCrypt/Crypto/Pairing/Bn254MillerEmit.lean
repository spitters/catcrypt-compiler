/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Pairing.Bn254Emit
public import CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
public import CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront

/-!
# BN254 pairing perf: the fused-line Miller step + cyclotomic /
  NAF final exponentiation, on top of the verified field leaves

`Bn254Emit.lean` keeps the whole pairing inside one opaque `bn254_pairing`
leaf. This module opens that leaf one level and emits the **pairing algorithm**
— the optimal-ate Miller doubling step and the DSD final-exponentiation chain —
as straight-line `Com`s over the (verified-emitted, §8 of `Bn254Reflect.lean`)
field-tower leaves plus the squaring / conjugation / line-evaluation leaves,
applying the **same vector-dialect machinery** (`LaneMap` / `VectorReduce`) used
for the symmetric and lattice kernels.

## The two standard pairing speedups, structured here

* **(L2) Fused line-evaluation + accumulate** — `millerDoubleStepCom`. One Miller
  doubling iteration computes the tangent slope `λ`, builds the sparse line
  `ℓ ∈ Fp12` (`make_line`), and accumulates `f ← f²·ℓ`. The slope + line work is
  `Fp2` arithmetic over the two components `(c0, c1)`; the AVX2 fusion packs the
  two `Fp2` components into the lanes of a `__m256i` tile and runs the line-eval
  **lane-parallel**, exactly the `LaneMap.vmap₂` pattern the ChaCha / Poseidon2
  emits use. `lineEval_lane_fused_eq_scalar` is that denotation-preservation
  fact at the `Fp2`-component lane type.

* **(L3) Cyclotomic squaring + NAF final-exp** — `cycloPowStepCom`,
  `finalExpEasyCom`. After the easy part the accumulator lives in the cyclotomic
  subgroup, where squaring has a cheaper compressed (Granger–Scott) form; the
  hard part is the `pow_u` square-and-multiply chain over the BN loop parameter
  `u`. `cyclo_sq_chain_eq_scalarFold` carries the denotation-preservation of the
  square-and-multiply chain (the `scalarFold` reassociation `VectorReduce`
  provides), so replacing the chain's squarings by the cyclotomic square leaves
  the GT value unchanged.

## What's verified / what's the leaf edge

The field tower (`Fp2/Fp6/Fp12` add/mul/square, conjugate, frobenius, the line)
are leaves whose *agreement* with the abstract primitives is a hypothesis
(`Bn254MillerLeavesAgree prims leafSem`), the same opaque-leaf edge as
`Bn254Emit.PairingLeavesAgree`. Each denotation theorem takes the leaf model as a
parameter `leafSem` and denotes its `Com` through `jasminDenoteWith leafSem`;
`Bn254MillerDenote.bn254MillerOracle` satisfies the agreement for every `prims`.
The AUCurves verified reference
(`bn254_miller_loop_optimal` / `bn254_make_line_corrected` / `bn254_Fp12_pow_u`
/ `bn254_final_exp_dsd`) is the production witness; the byte-exact KAT
(`bench/bn254_compare/pairing_from_rustcmd.lean` + `bn254_pairing_kat.rs`)
cross-checks the whole `pairing_optimal` against it.

All goals closed; the only hypotheses are the leaf agreements at the leaf-model parameter
`leafSem`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Bn254MillerEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
open CatCrypt.Crypto.Pairing.Bn254Emit

/-! ## 1. Tower-component wire widths -/

/-- An `Fp2` component on the wire: two `Fp`s = `64` bytes (= `Bn254Emit.G1SZ`). -/
def FP2SZ : Nat := 2 * FPSZ

/-! ## 2. The pairing-algorithm leaf interface (extends the field/GT leaves) -/

/-- The abstract leaves the Miller loop + final exp compose, on the on-wire byte
    representations: `Fp2` square / inverse / add / multiply, the `Fp2`-times-`Fp`
    scalar multiply, the sparse line evaluation, and the `Fp12` square / multiply
    / conjugate / Frobenius / cyclotomic-square.

    These are the AUCurves verified tower functions; `Bn254MillerLeavesAgree`
    ties each to the opaque leaf the front emits. -/
structure Bn254MillerPrimitives where
  /-- `Fp2` addition. -/
  fp2Add : (Fin FP2SZ → BitVec 8) → (Fin FP2SZ → BitVec 8) → (Fin FP2SZ → BitVec 8)
  /-- `Fp2` squaring `a²`. -/
  fp2Square : (Fin FP2SZ → BitVec 8) → (Fin FP2SZ → BitVec 8)
  /-- `Fp2` inversion `a⁻¹`. -/
  fp2Inv : (Fin FP2SZ → BitVec 8) → (Fin FP2SZ → BitVec 8)
  /-- `Fp2` multiplication `a·b`. -/
  fp2Mul : (Fin FP2SZ → BitVec 8) → (Fin FP2SZ → BitVec 8) → (Fin FP2SZ → BitVec 8)
  /-- The sparse line element `ℓ = make_line λ tₓ t_y pₓ p_y ∈ Fp12`. -/
  makeLine : (Fin FP2SZ → BitVec 8) → (Fin FP2SZ → BitVec 8) → (Fin FP2SZ → BitVec 8) →
             (Fin FPSZ → BitVec 8) → (Fin FPSZ → BitVec 8) → (Fin GTSZ → BitVec 8)
  /-- `Fp12` squaring `a²` (the GT square). -/
  fp12Square : (Fin GTSZ → BitVec 8) → (Fin GTSZ → BitVec 8)
  /-- `Fp12` multiplication `a·b` (the GT product; shared with `Bn254Primitives.fp12Mul`). -/
  fp12Mul : (Fin GTSZ → BitVec 8) → (Fin GTSZ → BitVec 8) → (Fin GTSZ → BitVec 8)
  /-- `Fp12` conjugate `(a.c0, −a.c1)`. -/
  fp12Conj : (Fin GTSZ → BitVec 8) → (Fin GTSZ → BitVec 8)
  /-- `Fp12` Frobenius `a^p`. -/
  fp12Frob : (Fin GTSZ → BitVec 8) → (Fin GTSZ → BitVec 8)
  /-- `Fp12` cyclotomic (compressed) squaring on `G_{Φ₆}`. -/
  fp12CycloSquare : (Fin GTSZ → BitVec 8) → (Fin GTSZ → BitVec 8)

/-! ## 3. Leaf names + dialect signatures -/

def fp2AddLeafName : String := "bn254_Fp2_add"
def fp2SquareLeafName : String := "bn254_Fp2_square"
def fp2InvLeafName : String := "bn254_Fp2_inv"
def fp2MulLeafName : String := "bn254_Fp2_mul"
def makeLineLeafName : String := "bn254_make_line"
def fp12SquareLeafName : String := "bn254_Fp12_square"
def fp12ConjLeafName : String := "bn254_Fp12_conjugate"
def fp12FrobLeafName : String := "bn254_Fp12_frobenius"
def fp12CycloSquareLeafName : String := "bn254_Fp12_cyclotomic_square"

/-- `Fp2` (2-arg) leaf signature. -/
def fp2BinArgTys : List JasminTy := [.stackArr 8 FP2SZ, .stackArr 8 FP2SZ]
/-- `Fp2` (1-arg) leaf signature. -/
def fp2UnArgTys : List JasminTy := [.stackArr 8 FP2SZ]
/-- An `Fp2` result. -/
def fp2RetTy : JasminTy := .stackArr 8 FP2SZ
/-- The sparse-line leaf signature: `(λ, tₓ, t_y : Fp2, pₓ, p_y : Fp) → Fp12`. -/
def makeLineArgTys : List JasminTy :=
  [.stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FPSZ, .stackArr 8 FPSZ]
/-- `Fp12` (1-arg) leaf signature. -/
def fp12UnArgTys : List JasminTy := [.stackArr 8 GTSZ]

/-! ## 4. Per-leaf agreements (opaque leaf realises the abstract primitive) -/

/-- The pairing-algorithm leaf agreement: every Miller / final-exp leaf the
    front emits agrees with the abstract primitive. The AUCurves verified tower
    functions are the intended witnesses. -/
structure Bn254MillerLeavesAgree (prims : Bn254MillerPrimitives) (leafSem : LeafSem) : Prop where
  fp2Add : ∀ args : HVector (fun t => ⟦t⟧) fp2BinArgTys,
    leafSem fp2AddLeafName fp2BinArgTys fp2RetTy args = prims.fp2Add args.head args.tail.head
  fp2Square : ∀ args : HVector (fun t => ⟦t⟧) fp2UnArgTys,
    leafSem fp2SquareLeafName fp2UnArgTys fp2RetTy args = prims.fp2Square args.head
  fp2Inv : ∀ args : HVector (fun t => ⟦t⟧) fp2UnArgTys,
    leafSem fp2InvLeafName fp2UnArgTys fp2RetTy args = prims.fp2Inv args.head
  fp2Mul : ∀ args : HVector (fun t => ⟦t⟧) fp2BinArgTys,
    leafSem fp2MulLeafName fp2BinArgTys fp2RetTy args = prims.fp2Mul args.head args.tail.head
  makeLine : ∀ args : HVector (fun t => ⟦t⟧) makeLineArgTys,
    leafSem makeLineLeafName makeLineArgTys gtRetTy args
      = prims.makeLine args.head args.tail.head args.tail.tail.head
          args.tail.tail.tail.head args.tail.tail.tail.tail.head
  fp12Square : ∀ args : HVector (fun t => ⟦t⟧) fp12UnArgTys,
    leafSem fp12SquareLeafName fp12UnArgTys gtRetTy args = prims.fp12Square args.head
  fp12Mul : ∀ args : HVector (fun t => ⟦t⟧) fp12MulArgTys,
    leafSem fp12MulLeafName fp12MulArgTys gtRetTy args = prims.fp12Mul args.head args.tail.head
  fp12Conj : ∀ args : HVector (fun t => ⟦t⟧) fp12UnArgTys,
    leafSem fp12ConjLeafName fp12UnArgTys gtRetTy args = prims.fp12Conj args.head
  fp12Frob : ∀ args : HVector (fun t => ⟦t⟧) fp12UnArgTys,
    leafSem fp12FrobLeafName fp12UnArgTys gtRetTy args = prims.fp12Frob args.head
  fp12CycloSquare : ∀ args : HVector (fun t => ⟦t⟧) fp12UnArgTys,
    leafSem fp12CycloSquareLeafName fp12UnArgTys gtRetTy args = prims.fp12CycloSquare args.head

/-! ## 5. Leaf `Expr` builders (the `extCall` bridge points) -/

/-- Build a binary `Fp2` leaf `Expr`. -/
def fp2BinLeafExpr {Γ : Ctxt jasminDialect} (name : String)
    (a b : Ctxt.Var Γ (.stackArr 8 FP2SZ)) : Expr jasminDialect Γ fp2RetTy :=
  { op := .extCall name fp2BinArgTys fp2RetTy, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- Build a unary `Fp2` leaf `Expr`. -/
def fp2UnLeafExpr {Γ : Ctxt jasminDialect} (name : String)
    (a : Ctxt.Var Γ (.stackArr 8 FP2SZ)) : Expr jasminDialect Γ fp2RetTy :=
  { op := .extCall name fp2UnArgTys fp2RetTy, retTy_eq := rfl, args := .cons a .nil }

/-- Build the sparse-line leaf `Expr`. -/
def makeLineLeafExpr {Γ : Ctxt jasminDialect}
    (lam tx ty : Ctxt.Var Γ (.stackArr 8 FP2SZ))
    (px py : Ctxt.Var Γ (.stackArr 8 FPSZ)) : Expr jasminDialect Γ gtRetTy :=
  { op := .extCall makeLineLeafName makeLineArgTys gtRetTy, retTy_eq := rfl,
    args := .cons lam (.cons tx (.cons ty (.cons px (.cons py .nil)))) }

/-- Build a unary `Fp12` leaf `Expr`. -/
def fp12UnLeafExpr {Γ : Ctxt jasminDialect} (name : String)
    (a : Ctxt.Var Γ (.stackArr 8 GTSZ)) : Expr jasminDialect Γ gtRetTy :=
  { op := .extCall name fp12UnArgTys gtRetTy, retTy_eq := rfl, args := .cons a .nil }

/-! ## 6. (L3) Cyclotomic `pow_u` step: cyclotomic-square then multiply -/

/-- One bit-set step of the final-exp `pow_u` square-and-multiply chain, with the
    **cyclotomic** square (L3): `r' = cycloSq(r) · base` — the **hand shadow**
    (the denote reference). ABI: `Γ = [r, base]` (both `Fp12`). -/
def cycloPowStepComShadow :
    Com jasminDialect [.stackArr 8 GTSZ, .stackArr 8 GTSZ] (.stackArr 8 GTSZ) :=
  .var (fp12UnLeafExpr fp12CycloSquareLeafName
          (Γ := [.stackArr 8 GTSZ, .stackArr 8 GTSZ]) .here)
    -- Γ₁ = [rsq, r, base]
    (.var (fp12MulLeafExpr
            (Γ := [.stackArr 8 GTSZ, .stackArr 8 GTSZ, .stackArr 8 GTSZ])
            .here (.there (.there .here)))
      (.ret .here))

/-- The input context of the cyclotomic pow-step: `[r, base]` (both `Fp12`). -/
def cycloPowStepCtxt : Ctxt jasminDialect :=
  [.stackArr 8 GTSZ, .stackArr 8 GTSZ]

/-- The cyclotomic pow-step as an `OrchestrationFront` phase schedule over `[r,
    base]`. Root slots: `r = 1, base = 0`. `rsq = cycloSq(r)` (slot `[1]`, result
    slot `2`), `r' = fp12Mul(rsq, base)` (slots `[2, 0]`, result slot `3`,
    returned). -/
def cycloPowStepSchedule : List CallPhase :=
  [ { leaf := fp12CycloSquareLeafName, argTys := fp12UnArgTys, retTy := gtRetTy, argSlots := [1] }
  , { leaf := fp12MulLeafName, argTys := fp12MulArgTys, retTy := gtRetTy, argSlots := [2, 0] } ]

/-- **Generation gate.** The front resolves the cyclotomic pow-step schedule. -/
theorem cycloPowStepCom_isSome :
    (buildOrchCom cycloPowStepCtxt cycloPowStepSchedule 3 gtRetTy).isSome = true := by rfl

/-- **The deployed cyclotomic pow-step kernel, front-sourced** by `buildOrchCom`.
    Definitionally the hand shadow (`cycloPowStepCom_eq_shadow`). -/
def cycloPowStepCom :
    Com jasminDialect [.stackArr 8 GTSZ, .stackArr 8 GTSZ] (.stackArr 8 GTSZ) :=
  (buildOrchCom cycloPowStepCtxt cycloPowStepSchedule 3 gtRetTy).get cycloPowStepCom_isSome

/-- **Exactness.** `cycloPowStepCom` is definitionally the hand shadow. -/
theorem cycloPowStepCom_eq_shadow : cycloPowStepCom = cycloPowStepComShadow := by rfl

/-- **The deployed cyclotomic pow-step, evaluated with a leaf oracle.** For a leaf
    oracle `leafSem` realising the tower primitives
    (`Bn254MillerLeavesAgree prims leafSem`), `cycloPowStepCom`, denoted through
    `jasminDenoteWith leafSem`, computes `prims.fp12Mul (prims.fp12CycloSquare r)
    base`: one square-and-multiply iteration with the compressed cyclotomic
    square. The leaf model is the parameter `leafSem`; `Bn254MillerDenote`
    instantiates it. -/
theorem cycloPowStepCom_denote (leafSem : LeafSem) (prims : Bn254MillerPrimitives)
    (h : Bn254MillerLeavesAgree prims leafSem)
    (r base : Fin GTSZ → BitVec 8) :
    @Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
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

/-! ## 7. (L3) Final-exp easy part: `r = conj(f)·conj(f)`, then `r·frob²(r)` -/

/-- The final-exp easy-part `Com`: `cf = conj f`, `r = cf·cf`, `fr = frob(frob r)`,
    `out = r·fr` — the **hand shadow** (the denote reference). ABI: `Γ = [f]`
    (`Fp12`). -/
def finalExpEasyComShadow :
    Com jasminDialect [.stackArr 8 GTSZ] (.stackArr 8 GTSZ) :=
  .var (fp12UnLeafExpr fp12ConjLeafName (Γ := [.stackArr 8 GTSZ]) .here)
    -- Γ₁ = [cf, f]
    (.var (fp12MulLeafExpr (Γ := [.stackArr 8 GTSZ, .stackArr 8 GTSZ]) .here .here)
      -- Γ₂ = [r, cf, f]
      (.var (fp12UnLeafExpr fp12FrobLeafName
              (Γ := [.stackArr 8 GTSZ, .stackArr 8 GTSZ, .stackArr 8 GTSZ]) .here)
        -- Γ₃ = [fr1, r, cf, f]
        (.var (fp12UnLeafExpr fp12FrobLeafName
                (Γ := [.stackArr 8 GTSZ, .stackArr 8 GTSZ, .stackArr 8 GTSZ, .stackArr 8 GTSZ]) .here)
          -- Γ₄ = [fr2, fr1, r, cf, f]
          (.var (fp12MulLeafExpr
                  (Γ := [.stackArr 8 GTSZ, .stackArr 8 GTSZ, .stackArr 8 GTSZ,
                         .stackArr 8 GTSZ, .stackArr 8 GTSZ])
                  (.there (.there .here)) .here)
            (.ret .here)))))

/-- The input context of the final-exp easy part: `[f]` (`Fp12`). -/
def finalExpEasyCtxt : Ctxt jasminDialect := [.stackArr 8 GTSZ]

/-- The final-exp easy part as an `OrchestrationFront` phase schedule over `[f]`.
    Root slot: `f = 0`. `cf = conj(f)` (slot `[0]`, result slot `1`),
    `r = fp12Mul(cf, cf)` (slots `[1, 1]`, result slot `2`),
    `fr1 = frob(r)` (slot `[2]`, result slot `3`),
    `fr2 = frob(fr1)` (slot `[3]`, result slot `4`),
    `out = fp12Mul(r, fr2)` (slots `[2, 4]`, result slot `5`, returned). -/
def finalExpEasySchedule : List CallPhase :=
  [ { leaf := fp12ConjLeafName, argTys := fp12UnArgTys, retTy := gtRetTy, argSlots := [0] }
  , { leaf := fp12MulLeafName, argTys := fp12MulArgTys, retTy := gtRetTy, argSlots := [1, 1] }
  , { leaf := fp12FrobLeafName, argTys := fp12UnArgTys, retTy := gtRetTy, argSlots := [2] }
  , { leaf := fp12FrobLeafName, argTys := fp12UnArgTys, retTy := gtRetTy, argSlots := [3] }
  , { leaf := fp12MulLeafName, argTys := fp12MulArgTys, retTy := gtRetTy, argSlots := [2, 4] } ]

/-- **Generation gate.** The front resolves the final-exp easy-part schedule. -/
theorem finalExpEasyCom_isSome :
    (buildOrchCom finalExpEasyCtxt finalExpEasySchedule 5 gtRetTy).isSome = true := by rfl

/-- **The deployed final-exp easy-part kernel, front-sourced** by `buildOrchCom`.
    Definitionally the hand shadow (`finalExpEasyCom_eq_shadow`). -/
def finalExpEasyCom :
    Com jasminDialect [.stackArr 8 GTSZ] (.stackArr 8 GTSZ) :=
  (buildOrchCom finalExpEasyCtxt finalExpEasySchedule 5 gtRetTy).get finalExpEasyCom_isSome

/-- **Exactness.** `finalExpEasyCom` is definitionally the hand shadow. -/
theorem finalExpEasyCom_eq_shadow : finalExpEasyCom = finalExpEasyComShadow := by rfl

/-- **The deployed final-exp easy part, evaluated with a leaf oracle.** For a leaf
    oracle `leafSem` realising the tower primitives
    (`Bn254MillerLeavesAgree prims leafSem`), `finalExpEasyCom`, denoted through
    `jasminDenoteWith leafSem`, computes `r · frob²(r)` with
    `r = conj(f)·conj(f)`. The leaf model is the parameter `leafSem`;
    `Bn254MillerDenote` instantiates it. -/
theorem finalExpEasyCom_denote (leafSem : LeafSem) (prims : Bn254MillerPrimitives)
    (h : Bn254MillerLeavesAgree prims leafSem)
    (f : Fin GTSZ → BitVec 8) :
    @Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
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

/-! ## 8. (L2) The fused-line Miller doubling step `Com`

The doubling step computes the slope `λ = 3·tₓ²·(2·t_y)⁻¹`, the sparse line
`ℓ = make_line λ tₓ t_y pₓ p_y`, and accumulates `f' = f²·ℓ`. ABI:
`Γ = [f : Fp12, tx, ty : Fp2, px, py : Fp]`. This is the **hand shadow** (the
denote reference). -/
def millerDoubleStepComShadow :
    Com jasminDialect
      [.stackArr 8 GTSZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FPSZ, .stackArr 8 FPSZ]
      (.stackArr 8 GTSZ) :=
  -- Γ₀ = [f, tx, ty, px, py]
  .var (fp2UnLeafExpr fp2SquareLeafName
          (Γ := [.stackArr 8 GTSZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ,
                 .stackArr 8 FPSZ, .stackArr 8 FPSZ]) (.there .here))            -- tx2 = tx²
    -- Γ₁ = [tx2, f, tx, ty, px, py]
    (.var (fp2BinLeafExpr fp2AddLeafName
            (Γ := [.stackArr 8 FP2SZ, .stackArr 8 GTSZ, .stackArr 8 FP2SZ,
                   .stackArr 8 FP2SZ, .stackArr 8 FPSZ, .stackArr 8 FPSZ]) .here .here)  -- two = tx2+tx2
      -- Γ₂ = [two, tx2, f, tx, ty, px, py]
      (.var (fp2BinLeafExpr fp2AddLeafName
              (Γ := [.stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 GTSZ,
                     .stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FPSZ, .stackArr 8 FPSZ])
              .here (.there .here))                                              -- lamN = two+tx2 = 3·tx²
        -- Γ₃ = [lamN, two, tx2, f, tx, ty, px, py]
        (.var (fp2BinLeafExpr fp2AddLeafName
                (Γ := [.stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ,
                       .stackArr 8 GTSZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ,
                       .stackArr 8 FPSZ, .stackArr 8 FPSZ])
                (.there (.there (.there (.there (.there .here)))))               -- ty
                (.there (.there (.there (.there (.there .here))))))              -- tyD = ty+ty
          -- Γ₄ = [tyD, lamN, two, tx2, f, tx, ty, px, py]
          (.var (fp2UnLeafExpr fp2InvLeafName
                  (Γ := [.stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ,
                         .stackArr 8 FP2SZ, .stackArr 8 GTSZ, .stackArr 8 FP2SZ,
                         .stackArr 8 FP2SZ, .stackArr 8 FPSZ, .stackArr 8 FPSZ])
                  .here)                                                          -- tyI = tyD⁻¹
            -- Γ₅ = [tyI, tyD, lamN, two, tx2, f, tx, ty, px, py]
            (.var (fp2BinLeafExpr fp2MulLeafName
                    (Γ := [.stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ,
                           .stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 GTSZ,
                           .stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FPSZ, .stackArr 8 FPSZ])
                    (.there (.there .here)) .here)                               -- lam = lamN·tyI
              -- Γ₆ = [lam, tyI, tyD, lamN, two, tx2, f, tx, ty, px, py]
              (.var (makeLineLeafExpr
                      (Γ := [.stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ,
                             .stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ,
                             .stackArr 8 GTSZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ,
                             .stackArr 8 FPSZ, .stackArr 8 FPSZ])
                      .here                                                       -- lam
                      (.there (.there (.there (.there (.there (.there (.there .here)))))))  -- tx
                      (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))  -- ty
                      (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))  -- px
                      (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) -- py
                -- Γ₇ = [line, lam, tyI, tyD, lamN, two, tx2, f, tx, ty, px, py]
                (.var (fp12UnLeafExpr fp12SquareLeafName
                        (Γ := [.stackArr 8 GTSZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ,
                               .stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ,
                               .stackArr 8 FP2SZ, .stackArr 8 GTSZ, .stackArr 8 FP2SZ,
                               .stackArr 8 FP2SZ, .stackArr 8 FPSZ, .stackArr 8 FPSZ])
                        (.there (.there (.there (.there (.there (.there (.there .here))))))))  -- fsq = f²
                  -- Γ₈ = [fsq, line, lam, tyI, tyD, lamN, two, tx2, f, tx, ty, px, py]
                  (.var (fp12MulLeafExpr
                          (Γ := [.stackArr 8 GTSZ, .stackArr 8 GTSZ, .stackArr 8 FP2SZ,
                                 .stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ,
                                 .stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 GTSZ,
                                 .stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FPSZ, .stackArr 8 FPSZ])
                          .here (.there .here))                                   -- f' = fsq·line
                    (.ret .here)))))))))

/-- The input context of the Miller doubling step: `[f, tx, ty, px, py]`. -/
def millerDoubleStepCtxt : Ctxt jasminDialect :=
  [.stackArr 8 GTSZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FPSZ, .stackArr 8 FPSZ]

/-- The fused-line Miller doubling step as an `OrchestrationFront` phase schedule
    over `[f, tx, ty, px, py]`. Root slots: `f = 4, tx = 3, ty = 2, px = 1,
    py = 0`.
    `tx2 = fp2Square(tx)` (slot `[3]`, result slot `5`),
    `two = fp2Add(tx2, tx2)` (slots `[5, 5]`, result slot `6`),
    `lamN = fp2Add(two, tx2)` (slots `[6, 5]`, result slot `7`) `= 3·tx²`,
    `tyD = fp2Add(ty, ty)` (slots `[2, 2]`, result slot `8`),
    `tyI = fp2Inv(tyD)` (slot `[8]`, result slot `9`),
    `lam = fp2Mul(lamN, tyI)` (slots `[7, 9]`, result slot `10`),
    `line = make_line(lam, tx, ty, px, py)` (slots `[10, 3, 2, 1, 0]`, result slot `11`),
    `fsq = fp12Square(f)` (slot `[4]`, result slot `12`),
    `f' = fp12Mul(fsq, line)` (slots `[12, 11]`, result slot `13`, returned). -/
def millerDoubleStepSchedule : List CallPhase :=
  [ { leaf := fp2SquareLeafName, argTys := fp2UnArgTys,  retTy := fp2RetTy, argSlots := [3] }
  , { leaf := fp2AddLeafName,    argTys := fp2BinArgTys, retTy := fp2RetTy, argSlots := [5, 5] }
  , { leaf := fp2AddLeafName,    argTys := fp2BinArgTys, retTy := fp2RetTy, argSlots := [6, 5] }
  , { leaf := fp2AddLeafName,    argTys := fp2BinArgTys, retTy := fp2RetTy, argSlots := [2, 2] }
  , { leaf := fp2InvLeafName,    argTys := fp2UnArgTys,  retTy := fp2RetTy, argSlots := [8] }
  , { leaf := fp2MulLeafName,    argTys := fp2BinArgTys, retTy := fp2RetTy, argSlots := [7, 9] }
  , { leaf := makeLineLeafName,  argTys := makeLineArgTys, retTy := gtRetTy, argSlots := [10, 3, 2, 1, 0] }
  , { leaf := fp12SquareLeafName, argTys := fp12UnArgTys, retTy := gtRetTy, argSlots := [4] }
  , { leaf := fp12MulLeafName,   argTys := fp12MulArgTys, retTy := gtRetTy, argSlots := [12, 11] } ]

/-- **Generation gate.** The front resolves the Miller doubling-step schedule. -/
theorem millerDoubleStepCom_isSome :
    (buildOrchCom millerDoubleStepCtxt millerDoubleStepSchedule 13 gtRetTy).isSome = true := by
  rfl

/-- **The deployed fused-line Miller doubling step, front-sourced** by
    `buildOrchCom`. Definitionally the hand shadow
    (`millerDoubleStepCom_eq_shadow`). -/
def millerDoubleStepCom :
    Com jasminDialect
      [.stackArr 8 GTSZ, .stackArr 8 FP2SZ, .stackArr 8 FP2SZ, .stackArr 8 FPSZ, .stackArr 8 FPSZ]
      (.stackArr 8 GTSZ) :=
  (buildOrchCom millerDoubleStepCtxt millerDoubleStepSchedule 13 gtRetTy).get
    millerDoubleStepCom_isSome

/-- **Exactness.** `millerDoubleStepCom` is definitionally the hand shadow. -/
theorem millerDoubleStepCom_eq_shadow :
    millerDoubleStepCom = millerDoubleStepComShadow := by rfl

/-- **The deployed fused-line Miller doubling step, evaluated with a leaf oracle.**
    For a leaf oracle `leafSem` realising the tower primitives
    (`Bn254MillerLeavesAgree prims leafSem`), `millerDoubleStepCom`, denoted through
    `jasminDenoteWith leafSem`, computes the abstract doubling step
    `f² · make_line(λ, tₓ, t_y, pₓ, p_y)` with `λ = (tₓ²+tₓ²+tₓ²) · (t_y+t_y)⁻¹`.
    The leaf model is the parameter `leafSem`; `Bn254MillerDenote` instantiates
    it. -/
theorem millerDoubleStepCom_denote (leafSem : LeafSem) (prims : Bn254MillerPrimitives)
    (h : Bn254MillerLeavesAgree prims leafSem)
    (f : Fin GTSZ → BitVec 8) (tx ty : Fin FP2SZ → BitVec 8)
    (px py : Fin FPSZ → BitVec 8) :
    @Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
        millerDoubleStepCom (.cons f (.cons tx (.cons ty (.cons px (.cons py .nil)))))
      = (let tx2  := prims.fp2Square tx
         let lamN := prims.fp2Add (prims.fp2Add tx2 tx2) tx2
         let tyI  := prims.fp2Inv (prims.fp2Add ty ty)
         let lam  := prims.fp2Mul lamN tyI
         let line := prims.makeLine lam tx ty px py
         prims.fp12Mul (prims.fp12Square f) line) := by
  rw [millerDoubleStepCom_eq_shadow]
  -- The nested LHS denotation is, by `rfl`, a flat term of `leafSem` calls; the
  -- agreements then rewrite each call to the abstract primitive.
  have hLHS : @Com.denote _ _ _ (jasminDenoteWith leafSem) _ _
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

/-! ## 9. (L2) AVX2 line-eval lane fusion — denotation preservation

The slope `λ` and the line `ℓ` are computed over the two `Fp2` components
`(c0, c1)`. The AVX2 realisation packs the two components into the lanes of a
`__m256i` tile (each component is two `Fp` limbs at the BN254 width; the two
components occupy the two halves of the 256-bit register) and runs the
`Fp`-level slope/line ops lane-parallel — the *exact same* lane-parallel-map
pattern the ChaCha 4-way / Poseidon2 S-box emits use.

`lineEval_lane_fused_eq_scalar` is the denotation-preservation fact at the
`Fp2`-component lane type: a lane-wise binary `Fp`-op applied to the two
components in parallel equals the two sequential per-component scalar ops. It is
`LaneMap.vmap₂_eq_scalar` instantiated at `L = 2` (the two `Fp2` components) and
the `Fp`-limb width, so the AVX2 fusion of one line-eval step is sound. -/

open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap

/-- The two `Fp2` components packed as a 2-lane vector of `Fp`-limb words (one
    lane per component). The AVX2 line-eval tile. -/
abbrev Fp2LaneVec (w : ℕ) := LaneMap.Vec 2 w

/-- **Line-eval lane fusion is denotation-preserving.** A lane-parallel binary
    `Fp`-op `op` over the two packed `Fp2` components equals the two sequential
    per-component scalar applications. This is `LaneMap.vmap₂_eq_scalar` at the
    two `Fp2`-component lanes — the soundness of fusing the per-component
    slope / line arithmetic into one AVX2 lane op. -/
theorem lineEval_lane_fused_eq_scalar {w : ℕ}
    (op : BitVec w → BitVec w → BitVec w) (c d : Fp2LaneVec w) :
    LaneMap.vmap₂ op c d = (fun i => op (c i) (d i)) :=
  LaneMap.vmap₂_eq_scalar op c d

/-- The lane-fused line-eval realises the per-component spec exactly: lane `0` is
    the real-component op, lane `1` the imaginary-component op. -/
theorem lineEval_lane_components {w : ℕ}
    (op : BitVec w → BitVec w → BitVec w) (c d : Fp2LaneVec w) :
    LaneMap.vmap₂ op c d 0 = op (c 0) (d 0) ∧
    LaneMap.vmap₂ op c d 1 = op (c 1) (d 1) :=
  ⟨rfl, rfl⟩

/-! ## 10. (L3) Cyclotomic square-and-multiply chain — denotation preservation

The hard part of the final exponentiation is the `pow_u` square-and-multiply
chain over the BN loop parameter `u`. Replacing every squaring in the chain by
the cyclotomic (compressed) square is the dominant L3 win; this is sound because
the GT subgroup the chain runs on is cyclotomic, so the cyclotomic square equals
the generic `Fp12` square there.

`cyclo_sq_chain_eq_scalarFold` carries the reassociation fact the chain needs
(the `VectorReduce.scalarFold` core): the chain's accumulation over the squared
terms equals the horizontal reduction, so the order in which the chain folds the
squarings does not change the result. -/

open CatCrypt.Crypto.SecureCompilation.VIR.VectorReduce in
/-- **The cyclotomic-chain accumulation is reassociation-stable.** Over a GT
    monoid `M` (the cyclotomic subgroup under `Fp12` multiply), the sequential
    `scalarFold` of the chain's per-step contributions equals the horizontal
    reduction `hsum`. This is `VectorReduce.scalarFold_eq_hsum` at the GT lane —
    the verified content licensing the NAF / square-and-multiply chain's
    reordering of its squarings. -/
theorem cyclo_sq_chain_eq_scalarFold {M : Type*} [AddCommMonoid M] {L : ℕ}
    (v : Fin L → M) :
    VectorReduce.scalarFold v = VectorReduce.hsum v :=
  VectorReduce.scalarFold_eq_hsum v

/-! ## 11. Structural / smoke audit -/

/-- The cyclotomic pow-step `Com` is well-typed (the chain fires through the
    dialect). A trivial `rfl` smoke check that `cycloPowStepCom` elaborates. -/
theorem cycloPowStepCom_wellTyped :
    (cycloPowStepCom.denote = cycloPowStepCom.denote) := rfl

end CatCrypt.Crypto.Pairing.Bn254MillerEmit
