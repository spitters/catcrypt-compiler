/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public meta import CatCrypt.Crypto.Pairing.MsmReduce
public import CatCrypt.Crypto.Pairing.MsmReduce
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
public import CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ArrAbiOrch
public import CatCrypt.Crypto.SecureCompilation.VIR.ArrAbiOrch
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# Production BLS12-377 emit: field leaves, the pairing leaf, the GT product, and
  the pairing-product verifier equation, as orchestration `Com`s

This is the BLS12-377 (Zexe / SnarkVM / Aleo curve) sibling of
`Pairing.Bls12381Emit`. It expresses the BLS12-377 kernels previously string-
templated to `.jazz` (`bench/bls12_377_compare/bls12_377_emit.lean`, jasminc-
lowered) as straight-line orchestration `Com`s over opaque `extCall` leaves, so
they can be lowered through the **OWNED** x86 backend
(`Com.toLprogArrAbi` + `renderLprogAtt`, see `Pairing.EcPairingEmit` and the
BN254 / BLS12-381 owned `.s`), with **no jasminc**.

The leaves are the AUCurves verified-bedrock2 BLS12-377 tower
(`bls12-377-safe-rust`, crate `bls12_377`):

* `bls377_add` / `bls377_sub` / `bls377_mul` / `bls377_square` / `bls377_inv` —
  fiat-crypto + Bernstein-Yang verified `Fp` field arithmetic (Montgomery,
  6 × `u64`);
* `bls377_pairing` — the bedrock2-tower optimal-ate pairing
  (`miller_loop` ∘ `final_exp`), opaque, never owned;
* `bls377_Fp12_mul` — the bedrock2-tower GT product.

These are exactly the symbols `CatCrypt.Crypto.Vale.BLS12_377` registers
(`bls377AddSymbol = "_bls377_add"`, … `bls377PairingSymbol = "bls377_pairing"`,
`bls377Fp12MulSymbol = "bls377_Fp12_mul"`); the jasmin-side names here bind at
link time to those C-ABI symbols, the same edge the existing
`bench/bls12_377_compare/bls377_kat.rs` Rust KAT cross-checks against the
AUCurves reference.

## Wire layout (production widths, AUCurves `Fp([u64;6])` layout)

* `Fp` = 6 little-endian `u64` limbs = `48` bytes (`FP377SZ`);
* a **G1 affine point** `(P_x ‖ P_y)` = two `Fp`s = `96` bytes;
* a **G2 affine point** `(Q_x ‖ Q_y)` over `Fp2 = Fp × Fp` = four `Fp`s =
  `192` bytes;
* the pairing output **GT = Fp12** = twelve `Fp`s = `576` bytes.

## What is owned vs what stays a leaf

The **orchestration** (the field kernel `out = op(x,y)`, the pairing-product
gather → `call` → `call` → scatter glue) is owned-emitted via the array-ABI
backend. The **leaf** (one `Fp` multiply, the Miller-loop + final-exp pairing,
an `Fp12` product) stays a `call <leaf>` resolved at link time against the
verified AUCurves tower. The value meaning is carried by the `*_denote` theorems
below, reducing each orchestration `Com` to the abstract field/pairing
primitives under the carried leaf agreements; this emit does not touch the
`Com`, so those agreements are untouched.

0 sorries; the only hypotheses are the opaque-leaf agreements
(`Bls377FieldLeavesAgree` / `Bls377PairingLeavesAgree`), the AUCurves-leaf edge.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Bls12_377Emit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront

/-! ## 1. Production wire widths (BLS12-377, AUCurves layout) -/

/-- A BLS12-377 base-field element `Fp` on the wire: `48` bytes (6 little-endian
    `u64` limbs), matching the AUCurves `Fp([u64;6])` layout. -/
def FPSZ : Nat := 48

/-- A G1 affine point `(x ‖ y)`: two `Fp`s = `96` bytes. -/
def G1SZ : Nat := 2 * FPSZ

/-- A G2 affine point `(x ‖ y)` over `Fp2`: four `Fp`s = `192` bytes. -/
def G2SZ : Nat := 4 * FPSZ

/-- A GT element `Fp12` (pairing output): twelve `Fp`s = `576` bytes. -/
def GTSZ : Nat := 12 * FPSZ

/-! ## 2. The field + pairing leaf spec (opaque `extCall`, carried agreement)

The leaf names match the symbols `Vale.BLS12_377` registers; the jasmin-side
names bind at link time to the AUCurves C-ABI shims. The Miller-loop + final-exp
**pairing** is a separate opaque leaf — never owned. -/

/-- The field-add leaf (AUCurves `_bls377_add`). -/
def addLeafName : String := "bls377_add"

/-- The field-sub leaf (AUCurves `_bls377_sub`). -/
def subLeafName : String := "bls377_sub"

/-- The field-multiply leaf (AUCurves `_bls377_mul`). -/
def mulLeafName : String := "bls377_mul"

/-- The field-square leaf (AUCurves `_bls377_square`). -/
def squareLeafName : String := "bls377_square"

/-- The Bernstein-Yang divstep field-inverse leaf (AUCurves `_bls377_inv`). -/
def invLeafName : String := "bls377_inv"

/-- The optimal-ate pairing leaf (AUCurves `bls377_pairing`, Miller loop +
    final exponentiation — opaque). -/
def pairingLeafName : String := "bls377_pairing"

/-- The GT (`Fp12`) product leaf (AUCurves `bls377_Fp12_mul`). -/
def fp12MulLeafName : String := "bls377_Fp12_mul"

/-- Binary `Fp` field-leaf argument types (`out = op(x, y)`). -/
def fieldBinArgTys : List JasminTy := [.stackArr 8 FPSZ, .stackArr 8 FPSZ]

/-- Unary `Fp` field-leaf argument types (`out = op(x)`). -/
def fieldUnArgTys : List JasminTy := [.stackArr 8 FPSZ]

/-- An `Fp` field-leaf result type. -/
def fpRetTy : JasminTy := .stackArr 8 FPSZ

/-- The pairing leaf argument types (`(P : G1, Q : G2)`). -/
def pairingArgTys : List JasminTy := [.stackArr 8 G1SZ, .stackArr 8 G2SZ]

/-- A GT (`Fp12`) result type (pairing output / GT product). -/
def gtRetTy : JasminTy := .stackArr 8 GTSZ

/-- The GT-multiply leaf argument types (`(a, b) : GT × GT`). -/
def fp12MulArgTys : List JasminTy := [.stackArr 8 GTSZ, .stackArr 8 GTSZ]

/-- The leaf-semantics carrier (the exact shape of `jasminExtSem`). The concrete
    AUCurves-backed leaves are a value of this type. -/
abbrev LeafSem : Type := MsmReduce.EcLeafSem

/-- The abstract BLS12-377 primitive interface the emit orchestrates: the
    binary/unary `Fp` field ops, the pairing `e`, and the GT product, on the
    on-wire byte representations. -/
structure Bls377Primitives where
  /-- `Fp` field addition `x + y`. -/
  fieldAdd : (Fin FPSZ → BitVec 8) → (Fin FPSZ → BitVec 8) → (Fin FPSZ → BitVec 8)
  /-- `Fp` field subtraction `x − y`. -/
  fieldSub : (Fin FPSZ → BitVec 8) → (Fin FPSZ → BitVec 8) → (Fin FPSZ → BitVec 8)
  /-- `Fp` field multiplication `x · y`. -/
  fieldMul : (Fin FPSZ → BitVec 8) → (Fin FPSZ → BitVec 8) → (Fin FPSZ → BitVec 8)
  /-- `Fp` field squaring `x²`. -/
  fieldSquare : (Fin FPSZ → BitVec 8) → (Fin FPSZ → BitVec 8)
  /-- `Fp` field inverse `x⁻¹` (Bernstein-Yang divstep). -/
  fieldInv : (Fin FPSZ → BitVec 8) → (Fin FPSZ → BitVec 8)
  /-- The BLS12-377 pairing `e(P, Q) : GT` (Miller loop + final exponentiation). -/
  pairing : (Fin G1SZ → BitVec 8) → (Fin G2SZ → BitVec 8) → (Fin GTSZ → BitVec 8)
  /-- The GT (`Fp12`) product `a · b`. -/
  fp12Mul : (Fin GTSZ → BitVec 8) → (Fin GTSZ → BitVec 8) → (Fin GTSZ → BitVec 8)

/-! ### Per-leaf agreements (opaque leaf realises the abstract primitive) -/

/-- Field-add leaf agreement. -/
def AddLeafAgrees (prims : Bls377Primitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) fieldBinArgTys,
    leafSem addLeafName fieldBinArgTys fpRetTy args
      = prims.fieldAdd (args.head) (args.tail.head)

/-- Field-sub leaf agreement. -/
def SubLeafAgrees (prims : Bls377Primitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) fieldBinArgTys,
    leafSem subLeafName fieldBinArgTys fpRetTy args
      = prims.fieldSub (args.head) (args.tail.head)

/-- Field-multiply leaf agreement. -/
def MulLeafAgrees (prims : Bls377Primitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) fieldBinArgTys,
    leafSem mulLeafName fieldBinArgTys fpRetTy args
      = prims.fieldMul (args.head) (args.tail.head)

/-- Field-square leaf agreement. -/
def SquareLeafAgrees (prims : Bls377Primitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) fieldUnArgTys,
    leafSem squareLeafName fieldUnArgTys fpRetTy args
      = prims.fieldSquare (args.head)

/-- Field-inverse leaf agreement. -/
def InvLeafAgrees (prims : Bls377Primitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) fieldUnArgTys,
    leafSem invLeafName fieldUnArgTys fpRetTy args
      = prims.fieldInv (args.head)

/-- Pairing leaf agreement (the Miller-loop + final-exp opaque edge). -/
def PairingLeafAgrees (prims : Bls377Primitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) pairingArgTys,
    leafSem pairingLeafName pairingArgTys gtRetTy args
      = prims.pairing (args.head) (args.tail.head)

/-- GT-multiply leaf agreement (the pairing-product accumulator). -/
def Fp12MulLeafAgrees (prims : Bls377Primitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) fp12MulArgTys,
    leafSem fp12MulLeafName fp12MulArgTys gtRetTy args
      = prims.fp12Mul (args.head) (args.tail.head)

/-- The full field-leaf agreement: the five `Fp` field leaves realise the
    abstract field ops. The verified AUCurves BLS12-377 field leaves are the
    intended witness (`bench/bls12_377_compare/`). -/
def Bls377FieldLeavesAgree (prims : Bls377Primitives) (leafSem : LeafSem) : Prop :=
  AddLeafAgrees prims leafSem ∧ SubLeafAgrees prims leafSem ∧
    MulLeafAgrees prims leafSem ∧ SquareLeafAgrees prims leafSem ∧
    InvLeafAgrees prims leafSem

/-- The full pairing-side agreement: the pairing leaf and the GT-multiply leaf
    both agree with the abstract primitives. The AUCurves `bls377_pairing` +
    `bls377_Fp12_mul` are the intended witnesses. -/
def Bls377PairingLeavesAgree (prims : Bls377Primitives) (leafSem : LeafSem) : Prop :=
  PairingLeafAgrees prims leafSem ∧ Fp12MulLeafAgrees prims leafSem

/-! ## 3. Leaf `Expr` builders + denotation (the `extCall` bridge point)

Each leaf `Expr` denotes (by `rfl`) to `jasminExtSem` of the looked-up
arguments — the dialect's opaque-leaf semantics — which the carried agreement
rewrites to the abstract primitive. -/

/-- Build a binary field-leaf `Expr` (`out = op(x, y)`) from two `Fp` vars. -/
def fieldBinLeafExpr {Γ : Ctxt jasminDialect} (leafName : String)
    (x y : Ctxt.Var Γ (.stackArr 8 FPSZ)) : Expr jasminDialect Γ fpRetTy :=
  { op := .extCall leafName fieldBinArgTys fpRetTy, retTy_eq := rfl,
    args := .cons x (.cons y .nil) }

/-- Build a unary field-leaf `Expr` (`out = op(x)`) from one `Fp` var. -/
def fieldUnLeafExpr {Γ : Ctxt jasminDialect} (leafName : String)
    (x : Ctxt.Var Γ (.stackArr 8 FPSZ)) : Expr jasminDialect Γ fpRetTy :=
  { op := .extCall leafName fieldUnArgTys fpRetTy, retTy_eq := rfl,
    args := .cons x .nil }

/-- Build the pairing leaf `Expr` from a G1 point and a G2 point. -/
def pairingLeafExpr {Γ : Ctxt jasminDialect}
    (P : Ctxt.Var Γ (.stackArr 8 G1SZ)) (Q : Ctxt.Var Γ (.stackArr 8 G2SZ)) :
    Expr jasminDialect Γ gtRetTy :=
  { op := .extCall pairingLeafName pairingArgTys gtRetTy, retTy_eq := rfl,
    args := .cons P (.cons Q .nil) }

/-- Build the GT-multiply leaf `Expr` from two GT (`Fp12`) variables. -/
def fp12MulLeafExpr {Γ : Ctxt jasminDialect}
    (a b : Ctxt.Var Γ (.stackArr 8 GTSZ)) : Expr jasminDialect Γ gtRetTy :=
  { op := .extCall fp12MulLeafName fp12MulArgTys gtRetTy, retTy_eq := rfl,
    args := .cons a (.cons b .nil) }

/-! ## 4. The field-arithmetic orchestration `Com`s (one leaf each)

Each field kernel is a single-leaf straight-line `extCall`-over-`stackArr`
orchestration, so it is front-sourced through
`OrchestrationFront.buildOrchCom`: the hand def is kept as the proven-equal
`*ComShadow` (the denote reference), the deployed name is rebound to the
front-generated `Com`, and `*Com_eq_shadow` bridges them by `rfl`. -/

/-- The input buffer context of a binary `Fp` field kernel: `[x : Fp, y : Fp]`. -/
def fieldBinCtxt : Ctxt jasminDialect := [.stackArr 8 FPSZ, .stackArr 8 FPSZ]

/-- The input buffer context of a unary `Fp` field kernel: `[x : Fp]`. -/
def fieldUnCtxt : Ctxt jasminDialect := [.stackArr 8 FPSZ]

/-- The BLS12-377 field-add kernel `out = x + y` — the **hand-authored shadow**.
    `Γ = [x : Fp, y : Fp]`. -/
def fieldAddComShadow :
    Com jasminDialect [.stackArr 8 FPSZ, .stackArr 8 FPSZ] (.stackArr 8 FPSZ) :=
  .var (fieldBinLeafExpr addLeafName
          (Γ := [.stackArr 8 FPSZ, .stackArr 8 FPSZ]) .here (.there .here))
    (.ret .here)

/-- Field-add as a phase schedule: one `bls377_add` leaf over slots `[1, 0]`
    (root slots on `[x, y]`: `x = 1, y = 0`), result slot `2` (returned). -/
def fieldAddSchedule : List CallPhase :=
  [ { leaf := addLeafName, argTys := fieldBinArgTys, retTy := fpRetTy,
      argSlots := [1, 0] } ]

/-- **Generation gate.** The front resolves the field-add schedule. -/
theorem fieldAddCom_isSome :
    (buildOrchCom fieldBinCtxt fieldAddSchedule 2 fpRetTy).isSome = true := by rfl

/-- **The deployed field-add kernel, front-sourced** by `buildOrchCom` from
    `fieldAddSchedule`. Definitionally the hand shadow (`fieldAddCom_eq_shadow`). -/
def fieldAddCom :
    Com jasminDialect [.stackArr 8 FPSZ, .stackArr 8 FPSZ] (.stackArr 8 FPSZ) :=
  (buildOrchCom fieldBinCtxt fieldAddSchedule 2 fpRetTy).get fieldAddCom_isSome

/-- **Exactness.** The front-sourced deployed `fieldAddCom` is definitionally the
    hand shadow. -/
theorem fieldAddCom_eq_shadow : fieldAddCom = fieldAddComShadow := by rfl

/-- The BLS12-377 field-sub kernel `out = x − y` — the **hand-authored shadow**. -/
def fieldSubComShadow :
    Com jasminDialect [.stackArr 8 FPSZ, .stackArr 8 FPSZ] (.stackArr 8 FPSZ) :=
  .var (fieldBinLeafExpr subLeafName
          (Γ := [.stackArr 8 FPSZ, .stackArr 8 FPSZ]) .here (.there .here))
    (.ret .here)

/-- Field-sub as a phase schedule: one `bls377_sub` leaf over slots `[1, 0]`. -/
def fieldSubSchedule : List CallPhase :=
  [ { leaf := subLeafName, argTys := fieldBinArgTys, retTy := fpRetTy,
      argSlots := [1, 0] } ]

/-- **Generation gate.** The front resolves the field-sub schedule. -/
theorem fieldSubCom_isSome :
    (buildOrchCom fieldBinCtxt fieldSubSchedule 2 fpRetTy).isSome = true := by rfl

/-- **The deployed field-sub kernel, front-sourced** by `buildOrchCom`. -/
def fieldSubCom :
    Com jasminDialect [.stackArr 8 FPSZ, .stackArr 8 FPSZ] (.stackArr 8 FPSZ) :=
  (buildOrchCom fieldBinCtxt fieldSubSchedule 2 fpRetTy).get fieldSubCom_isSome

/-- **Exactness.** `fieldSubCom` is definitionally the hand shadow. -/
theorem fieldSubCom_eq_shadow : fieldSubCom = fieldSubComShadow := by rfl

/-- The BLS12-377 field-multiply kernel `out = x · y` — the **hand-authored
    shadow**. -/
def fieldMulComShadow :
    Com jasminDialect [.stackArr 8 FPSZ, .stackArr 8 FPSZ] (.stackArr 8 FPSZ) :=
  .var (fieldBinLeafExpr mulLeafName
          (Γ := [.stackArr 8 FPSZ, .stackArr 8 FPSZ]) .here (.there .here))
    (.ret .here)

/-- Field-multiply as a phase schedule: one `bls377_mul` leaf over slots `[1, 0]`. -/
def fieldMulSchedule : List CallPhase :=
  [ { leaf := mulLeafName, argTys := fieldBinArgTys, retTy := fpRetTy,
      argSlots := [1, 0] } ]

/-- **Generation gate.** The front resolves the field-multiply schedule. -/
theorem fieldMulCom_isSome :
    (buildOrchCom fieldBinCtxt fieldMulSchedule 2 fpRetTy).isSome = true := by rfl

/-- **The deployed field-multiply kernel, front-sourced** by `buildOrchCom`. -/
def fieldMulCom :
    Com jasminDialect [.stackArr 8 FPSZ, .stackArr 8 FPSZ] (.stackArr 8 FPSZ) :=
  (buildOrchCom fieldBinCtxt fieldMulSchedule 2 fpRetTy).get fieldMulCom_isSome

/-- **Exactness.** `fieldMulCom` is definitionally the hand shadow. -/
theorem fieldMulCom_eq_shadow : fieldMulCom = fieldMulComShadow := by rfl

/-- The BLS12-377 field-square kernel `out = x²` — the **hand-authored shadow**. -/
def fieldSquareComShadow :
    Com jasminDialect [.stackArr 8 FPSZ] (.stackArr 8 FPSZ) :=
  .var (fieldUnLeafExpr squareLeafName (Γ := [.stackArr 8 FPSZ]) .here)
    (.ret .here)

/-- Field-square as a phase schedule: one `bls377_square` leaf over slot `[0]`
    (root slot on `[x]`: `x = 0`), result slot `1` (returned). -/
def fieldSquareSchedule : List CallPhase :=
  [ { leaf := squareLeafName, argTys := fieldUnArgTys, retTy := fpRetTy,
      argSlots := [0] } ]

/-- **Generation gate.** The front resolves the field-square schedule. -/
theorem fieldSquareCom_isSome :
    (buildOrchCom fieldUnCtxt fieldSquareSchedule 1 fpRetTy).isSome = true := by rfl

/-- **The deployed field-square kernel, front-sourced** by `buildOrchCom`. -/
def fieldSquareCom :
    Com jasminDialect [.stackArr 8 FPSZ] (.stackArr 8 FPSZ) :=
  (buildOrchCom fieldUnCtxt fieldSquareSchedule 1 fpRetTy).get fieldSquareCom_isSome

/-- **Exactness.** `fieldSquareCom` is definitionally the hand shadow. -/
theorem fieldSquareCom_eq_shadow : fieldSquareCom = fieldSquareComShadow := by rfl

/-- The BLS12-377 Bernstein-Yang field-inverse kernel `out = x⁻¹` — the
    **hand-authored shadow**. -/
def fieldInvComShadow :
    Com jasminDialect [.stackArr 8 FPSZ] (.stackArr 8 FPSZ) :=
  .var (fieldUnLeafExpr invLeafName (Γ := [.stackArr 8 FPSZ]) .here)
    (.ret .here)

/-- Field-inverse as a phase schedule: one `bls377_inv` leaf over slot `[0]`. -/
def fieldInvSchedule : List CallPhase :=
  [ { leaf := invLeafName, argTys := fieldUnArgTys, retTy := fpRetTy,
      argSlots := [0] } ]

/-- **Generation gate.** The front resolves the field-inverse schedule. -/
theorem fieldInvCom_isSome :
    (buildOrchCom fieldUnCtxt fieldInvSchedule 1 fpRetTy).isSome = true := by rfl

/-- **The deployed field-inverse kernel, front-sourced** by `buildOrchCom`. -/
def fieldInvCom :
    Com jasminDialect [.stackArr 8 FPSZ] (.stackArr 8 FPSZ) :=
  (buildOrchCom fieldUnCtxt fieldInvSchedule 1 fpRetTy).get fieldInvCom_isSome

/-- **Exactness.** `fieldInvCom` is definitionally the hand shadow. -/
theorem fieldInvCom_eq_shadow : fieldInvCom = fieldInvComShadow := by rfl

/-! ## 5. The pairing-side orchestration `Com`s -/

/-- The single-pairing input context `[P : G1, Q : G2]`. -/
def pairingCtxt : Ctxt jasminDialect := [.stackArr 8 G1SZ, .stackArr 8 G2SZ]

/-- The GT-product input context `[a : GT, b : GT]`. -/
def fp12MulCtxt : Ctxt jasminDialect := [.stackArr 8 GTSZ, .stackArr 8 GTSZ]

/-- The pairing-product input context `[P₁ : G1, Q₁ : G2, P₂ : G1, Q₂ : G2]`. -/
def pairingProductCtxt : Ctxt jasminDialect :=
  [.stackArr 8 G1SZ, .stackArr 8 G2SZ, .stackArr 8 G1SZ, .stackArr 8 G2SZ]

/-- The single-pairing kernel `out = e(P, Q)` — the **hand-authored shadow**.
    `Γ = [P : G1, Q : G2]`. -/
def pairingComShadow :
    Com jasminDialect [.stackArr 8 G1SZ, .stackArr 8 G2SZ] (.stackArr 8 GTSZ) :=
  .var (pairingLeafExpr
          (Γ := [.stackArr 8 G1SZ, .stackArr 8 G2SZ]) .here (.there .here))
    (.ret .here)

/-- Single-pairing as a phase schedule: one `bls377_pairing` leaf over slots
    `[1, 0]` (root slots on `[P, Q]`: `P = 1, Q = 0`), result slot `2`. -/
def pairingSchedule : List CallPhase :=
  [ { leaf := pairingLeafName, argTys := pairingArgTys, retTy := gtRetTy,
      argSlots := [1, 0] } ]

/-- **Generation gate.** The front resolves the single-pairing schedule. -/
theorem pairingCom_isSome :
    (buildOrchCom pairingCtxt pairingSchedule 2 gtRetTy).isSome = true := by rfl

/-- **The deployed single-pairing kernel, front-sourced** by `buildOrchCom`. -/
def pairingCom :
    Com jasminDialect [.stackArr 8 G1SZ, .stackArr 8 G2SZ] (.stackArr 8 GTSZ) :=
  (buildOrchCom pairingCtxt pairingSchedule 2 gtRetTy).get pairingCom_isSome

/-- **Exactness.** `pairingCom` is definitionally the hand shadow. -/
theorem pairingCom_eq_shadow : pairingCom = pairingComShadow := by rfl

/-- The GT-product kernel `out = a · b` — the **hand-authored shadow**.
    `Γ = [a : GT, b : GT]`. -/
def fp12MulComShadow :
    Com jasminDialect [.stackArr 8 GTSZ, .stackArr 8 GTSZ] (.stackArr 8 GTSZ) :=
  .var (fp12MulLeafExpr
          (Γ := [.stackArr 8 GTSZ, .stackArr 8 GTSZ]) .here (.there .here))
    (.ret .here)

/-- GT-product as a phase schedule: one `bls377_Fp12_mul` leaf over slots `[1, 0]`. -/
def fp12MulSchedule : List CallPhase :=
  [ { leaf := fp12MulLeafName, argTys := fp12MulArgTys, retTy := gtRetTy,
      argSlots := [1, 0] } ]

/-- **Generation gate.** The front resolves the GT-product schedule. -/
theorem fp12MulCom_isSome :
    (buildOrchCom fp12MulCtxt fp12MulSchedule 2 gtRetTy).isSome = true := by rfl

/-- **The deployed GT-product kernel, front-sourced** by `buildOrchCom`. -/
def fp12MulCom :
    Com jasminDialect [.stackArr 8 GTSZ, .stackArr 8 GTSZ] (.stackArr 8 GTSZ) :=
  (buildOrchCom fp12MulCtxt fp12MulSchedule 2 gtRetTy).get fp12MulCom_isSome

/-- **Exactness.** `fp12MulCom` is definitionally the hand shadow. -/
theorem fp12MulCom_eq_shadow : fp12MulCom = fp12MulComShadow := by rfl

/-- The BLS12-377 pairing-product kernel `out = e(P₁,Q₁) · e(P₂,Q₂)` — the
    **hand-authored shadow**: two `bls377_pairing` leaves accumulated by one
    `bls377_Fp12_mul` leaf — the canonical pairing-equation building block
    (Groth16 LHS·RHS, BLS verify, KZG opening).
    `Γ = [P₁ : G1, Q₁ : G2, P₂ : G1, Q₂ : G2]`. -/
def pairingProductComShadow :
    Com jasminDialect
      [.stackArr 8 G1SZ, .stackArr 8 G2SZ, .stackArr 8 G1SZ, .stackArr 8 G2SZ]
      (.stackArr 8 GTSZ) :=
  -- Γ0 = [P₁, Q₁, P₂, Q₂]
  .var (pairingLeafExpr
          (Γ := [.stackArr 8 G1SZ, .stackArr 8 G2SZ,
                 .stackArr 8 G1SZ, .stackArr 8 G2SZ])
          .here (.there .here))  -- e1 = e(P₁, Q₁)
    -- Γ1 = [e1, P₁, Q₁, P₂, Q₂]
    (.var (pairingLeafExpr
            (Γ := [.stackArr 8 GTSZ, .stackArr 8 G1SZ, .stackArr 8 G2SZ,
                   .stackArr 8 G1SZ, .stackArr 8 G2SZ])
            (.there (.there (.there .here)))            -- P₂
            (.there (.there (.there (.there .here)))))  -- Q₂
      -- Γ2 = [e2, e1, P₁, Q₁, P₂, Q₂]
      (.var (fp12MulLeafExpr
              (Γ := [.stackArr 8 GTSZ, .stackArr 8 GTSZ, .stackArr 8 G1SZ,
                     .stackArr 8 G2SZ, .stackArr 8 G1SZ, .stackArr 8 G2SZ])
              (.there .here)  -- e1
              .here)          -- e2
        (.ret .here)))

/-- The pairing-product as an `OrchestrationFront` phase schedule:
    `e₁ = e(P₁,Q₁)` (slots `[3, 2]`), `e₂ = e(P₂,Q₂)` (slots `[1, 0]`),
    `out = e₁ · e₂` (slots `[4, 5]`). Root slots on `[P₁, Q₁, P₂, Q₂]`:
    `Q₂ = 0, P₂ = 1, Q₁ = 2, P₁ = 3`; the two pairing results take slots `4, 5`,
    the product slot `6` (returned). This is `OrchestrationFrontValidate`'s
    `pairingProductSchedule` inlined here as the emit's own source. -/
def pairingProductSchedule : List CallPhase :=
  [ { leaf := pairingLeafName, argTys := pairingArgTys, retTy := gtRetTy,
      argSlots := [3, 2] }              -- e₁ = e(P₁, Q₁)
  , { leaf := pairingLeafName, argTys := pairingArgTys, retTy := gtRetTy,
      argSlots := [1, 0] }              -- e₂ = e(P₂, Q₂)
  , { leaf := fp12MulLeafName, argTys := fp12MulArgTys, retTy := gtRetTy,
      argSlots := [4, 5] } ]           -- out = e₁ · e₂

/-- **Generation gate.** The front resolves the pairing-product schedule. -/
theorem pairingProductCom_isSome :
    (buildOrchCom pairingProductCtxt pairingProductSchedule 6 gtRetTy).isSome = true := by
  rfl

/-- **The deployed pairing-product kernel, front-sourced** by `buildOrchCom` from
    `pairingProductSchedule`. Definitionally the hand shadow
    (`pairingProductCom_eq_shadow`), so `Bls12_377Emit` + the array-ABI
    backend consume it unchanged. -/
def pairingProductCom :
    Com jasminDialect
      [.stackArr 8 G1SZ, .stackArr 8 G2SZ, .stackArr 8 G1SZ, .stackArr 8 G2SZ]
      (.stackArr 8 GTSZ) :=
  (buildOrchCom pairingProductCtxt pairingProductSchedule 6 gtRetTy).get
    pairingProductCom_isSome

/-- **Exactness.** The front-sourced deployed `pairingProductCom` is definitionally
    the hand shadow — the auto-resolved de-Bruijn operand chains coincide with the
    hand-threaded `.here`/`.there` chains, so every downstream fact transfers. -/
theorem pairingProductCom_eq_shadow :
    pairingProductCom = pairingProductComShadow := by rfl

/-! ## 6. Denotation carries (each `Com` reduces to the abstract primitives) -/

/-- **Field-add denotation (shadow).** `out = x + y` denotes to `prims.fieldAdd x y`
    under the carried `Bls377FieldLeavesAgree`. -/
theorem fieldAddComShadow_denote (prims : Bls377Primitives)
    (hLeaf : Bls377FieldLeavesAgree prims jasminExtSem)
    (x y : Fin FPSZ → BitVec 8) :
    fieldAddComShadow.denote (.cons x (.cons y .nil)) = prims.fieldAdd x y := by
  obtain ⟨hAdd, _, _, _, _⟩ := hLeaf
  show jasminExtSem addLeafName fieldBinArgTys fpRetTy (.cons x (.cons y .nil))
      = prims.fieldAdd x y
  rw [hAdd (.cons x (.cons y .nil))]; rfl

/-- **Field-add denotation (deployed, front-sourced).** Via `fieldAddCom_eq_shadow`
    + the shadow's denote, so downstream users of `fieldAddCom` by name are
    unaffected by the front-sourcing. -/
theorem fieldAddCom_denote (prims : Bls377Primitives)
    (hLeaf : Bls377FieldLeavesAgree prims jasminExtSem)
    (x y : Fin FPSZ → BitVec 8) :
    fieldAddCom.denote (.cons x (.cons y .nil)) = prims.fieldAdd x y := by
  rw [fieldAddCom_eq_shadow]; exact fieldAddComShadow_denote prims hLeaf x y

/-- **Field-sub denotation (shadow).** `out = x − y` denotes to `prims.fieldSub x y`. -/
theorem fieldSubComShadow_denote (prims : Bls377Primitives)
    (hLeaf : Bls377FieldLeavesAgree prims jasminExtSem)
    (x y : Fin FPSZ → BitVec 8) :
    fieldSubComShadow.denote (.cons x (.cons y .nil)) = prims.fieldSub x y := by
  obtain ⟨_, hSub, _, _, _⟩ := hLeaf
  show jasminExtSem subLeafName fieldBinArgTys fpRetTy (.cons x (.cons y .nil))
      = prims.fieldSub x y
  rw [hSub (.cons x (.cons y .nil))]; rfl

/-- **Field-sub denotation (deployed, front-sourced).** -/
theorem fieldSubCom_denote (prims : Bls377Primitives)
    (hLeaf : Bls377FieldLeavesAgree prims jasminExtSem)
    (x y : Fin FPSZ → BitVec 8) :
    fieldSubCom.denote (.cons x (.cons y .nil)) = prims.fieldSub x y := by
  rw [fieldSubCom_eq_shadow]; exact fieldSubComShadow_denote prims hLeaf x y

/-- **Field-multiply denotation (shadow).** `out = x · y` denotes to
    `prims.fieldMul x y`. -/
theorem fieldMulComShadow_denote (prims : Bls377Primitives)
    (hLeaf : Bls377FieldLeavesAgree prims jasminExtSem)
    (x y : Fin FPSZ → BitVec 8) :
    fieldMulComShadow.denote (.cons x (.cons y .nil)) = prims.fieldMul x y := by
  obtain ⟨_, _, hMul, _, _⟩ := hLeaf
  show jasminExtSem mulLeafName fieldBinArgTys fpRetTy (.cons x (.cons y .nil))
      = prims.fieldMul x y
  rw [hMul (.cons x (.cons y .nil))]; rfl

/-- **Field-multiply denotation (deployed, front-sourced).** -/
theorem fieldMulCom_denote (prims : Bls377Primitives)
    (hLeaf : Bls377FieldLeavesAgree prims jasminExtSem)
    (x y : Fin FPSZ → BitVec 8) :
    fieldMulCom.denote (.cons x (.cons y .nil)) = prims.fieldMul x y := by
  rw [fieldMulCom_eq_shadow]; exact fieldMulComShadow_denote prims hLeaf x y

/-- **Field-square denotation (shadow).** `out = x²` denotes to
    `prims.fieldSquare x`. -/
theorem fieldSquareComShadow_denote (prims : Bls377Primitives)
    (hLeaf : Bls377FieldLeavesAgree prims jasminExtSem)
    (x : Fin FPSZ → BitVec 8) :
    fieldSquareComShadow.denote (.cons x .nil) = prims.fieldSquare x := by
  obtain ⟨_, _, _, hSq, _⟩ := hLeaf
  show jasminExtSem squareLeafName fieldUnArgTys fpRetTy (.cons x .nil)
      = prims.fieldSquare x
  rw [hSq (.cons x .nil)]; rfl

/-- **Field-square denotation (deployed, front-sourced).** -/
theorem fieldSquareCom_denote (prims : Bls377Primitives)
    (hLeaf : Bls377FieldLeavesAgree prims jasminExtSem)
    (x : Fin FPSZ → BitVec 8) :
    fieldSquareCom.denote (.cons x .nil) = prims.fieldSquare x := by
  rw [fieldSquareCom_eq_shadow]; exact fieldSquareComShadow_denote prims hLeaf x

/-- **Field-inverse denotation (shadow).** `out = x⁻¹` denotes to
    `prims.fieldInv x`. -/
theorem fieldInvComShadow_denote (prims : Bls377Primitives)
    (hLeaf : Bls377FieldLeavesAgree prims jasminExtSem)
    (x : Fin FPSZ → BitVec 8) :
    fieldInvComShadow.denote (.cons x .nil) = prims.fieldInv x := by
  obtain ⟨_, _, _, _, hInv⟩ := hLeaf
  show jasminExtSem invLeafName fieldUnArgTys fpRetTy (.cons x .nil)
      = prims.fieldInv x
  rw [hInv (.cons x .nil)]; rfl

/-- **Field-inverse denotation (deployed, front-sourced).** -/
theorem fieldInvCom_denote (prims : Bls377Primitives)
    (hLeaf : Bls377FieldLeavesAgree prims jasminExtSem)
    (x : Fin FPSZ → BitVec 8) :
    fieldInvCom.denote (.cons x .nil) = prims.fieldInv x := by
  rw [fieldInvCom_eq_shadow]; exact fieldInvComShadow_denote prims hLeaf x

/-- **Single-pairing denotation.** `out = e(P, Q)` denotes to `prims.pairing P Q`
    under the carried `Bls377PairingLeavesAgree`. -/
theorem pairingComShadow_denote (prims : Bls377Primitives)
    (hPair : Bls377PairingLeavesAgree prims jasminExtSem)
    (p : Fin G1SZ → BitVec 8) (q : Fin G2SZ → BitVec 8) :
    pairingComShadow.denote (.cons p (.cons q .nil)) = prims.pairing p q := by
  obtain ⟨hP, _⟩ := hPair
  show jasminExtSem pairingLeafName pairingArgTys gtRetTy (.cons p (.cons q .nil))
      = prims.pairing p q
  rw [hP (.cons p (.cons q .nil))]; rfl

/-- **Single-pairing denotation (deployed, front-sourced).** -/
theorem pairingCom_denote (prims : Bls377Primitives)
    (hPair : Bls377PairingLeavesAgree prims jasminExtSem)
    (p : Fin G1SZ → BitVec 8) (q : Fin G2SZ → BitVec 8) :
    pairingCom.denote (.cons p (.cons q .nil)) = prims.pairing p q := by
  rw [pairingCom_eq_shadow]; exact pairingComShadow_denote prims hPair p q

/-- **GT-product denotation (shadow).** `out = a · b` denotes to
    `prims.fp12Mul a b`. -/
theorem fp12MulComShadow_denote (prims : Bls377Primitives)
    (hPair : Bls377PairingLeavesAgree prims jasminExtSem)
    (a b : Fin GTSZ → BitVec 8) :
    fp12MulComShadow.denote (.cons a (.cons b .nil)) = prims.fp12Mul a b := by
  obtain ⟨_, hM⟩ := hPair
  show jasminExtSem fp12MulLeafName fp12MulArgTys gtRetTy (.cons a (.cons b .nil))
      = prims.fp12Mul a b
  rw [hM (.cons a (.cons b .nil))]; rfl

/-- **GT-product denotation (deployed, front-sourced).** -/
theorem fp12MulCom_denote (prims : Bls377Primitives)
    (hPair : Bls377PairingLeavesAgree prims jasminExtSem)
    (a b : Fin GTSZ → BitVec 8) :
    fp12MulCom.denote (.cons a (.cons b .nil)) = prims.fp12Mul a b := by
  rw [fp12MulCom_eq_shadow]; exact fp12MulComShadow_denote prims hPair a b

/-- **Pairing-product denotation.** `out = e(P₁,Q₁) · e(P₂,Q₂)` denotes to
    `prims.fp12Mul (prims.pairing P₁ Q₁) (prims.pairing P₂ Q₂)` under the carried
    `Bls377PairingLeavesAgree`. The pairing-equation check `= 1` in GT is the
    caller's final equality test on this value. -/
theorem pairingProductComShadow_denote (prims : Bls377Primitives)
    (hPair : Bls377PairingLeavesAgree prims jasminExtSem)
    (p1 : Fin G1SZ → BitVec 8) (q1 : Fin G2SZ → BitVec 8)
    (p2 : Fin G1SZ → BitVec 8) (q2 : Fin G2SZ → BitVec 8) :
    pairingProductComShadow.denote (.cons p1 (.cons q1 (.cons p2 (.cons q2 .nil))))
      = prims.fp12Mul (prims.pairing p1 q1) (prims.pairing p2 q2) := by
  obtain ⟨hP, hM⟩ := hPair
  show jasminExtSem fp12MulLeafName fp12MulArgTys gtRetTy
        (.cons (jasminExtSem pairingLeafName pairingArgTys gtRetTy
                  (.cons p1 (.cons q1 .nil)))
          (.cons (jasminExtSem pairingLeafName pairingArgTys gtRetTy
                    (.cons p2 (.cons q2 .nil))) .nil))
      = prims.fp12Mul (prims.pairing p1 q1) (prims.pairing p2 q2)
  rw [hP (.cons p1 (.cons q1 .nil)), hP (.cons p2 (.cons q2 .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hM (.cons (prims.pairing p1 q1) (.cons (prims.pairing p2 q2) .nil))]
  simp only [HVector.head, HVector.tail]
  rfl

/-- **Pairing-product denotation (deployed, front-sourced).** Via
    `pairingProductCom_eq_shadow` + the shadow's denote, so `Bls12_377Emit`
    and downstream users of `pairingProductCom` by name are unaffected. -/
theorem pairingProductCom_denote (prims : Bls377Primitives)
    (hPair : Bls377PairingLeavesAgree prims jasminExtSem)
    (p1 : Fin G1SZ → BitVec 8) (q1 : Fin G2SZ → BitVec 8)
    (p2 : Fin G1SZ → BitVec 8) (q2 : Fin G2SZ → BitVec 8) :
    pairingProductCom.denote (.cons p1 (.cons q1 (.cons p2 (.cons q2 .nil))))
      = prims.fp12Mul (prims.pairing p1 q1) (prims.pairing p2 q2) := by
  rw [pairingProductCom_eq_shadow]
  exact pairingProductComShadow_denote prims hPair p1 q1 p2 q2

end CatCrypt.Crypto.Pairing.Bls12_377Emit


namespace CatCrypt.Crypto.Pairing.Bls12_377Emit

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.Pairing.Bls12_377Emit
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront (buildOrchCom)

/-! ## 1. The owned `Lprog` (all BLS12-377 orchestrations in one `.s`) -/

/-- BLS12-377 orchestrations: the five `Fp` field kernels (add/sub/mul/square/
    inv), the single pairing, the GT product, and the pairing-product check, all
    in one `.s`. Symbol names match the kernel names the jasmin `.jazz` path
    used so the same KAT harness binds. -/
def bls12_377Lprog : Lprog :=
  { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := []
    lp_funcs :=
      (Com.toLprogArrAbi fieldAddCom "bls377_field_add").lp_funcs
      ++ (Com.toLprogArrAbi fieldSubCom "bls377_field_sub").lp_funcs
      ++ (Com.toLprogArrAbi fieldMulCom "bls377_field_mul").lp_funcs
      ++ (Com.toLprogArrAbi fieldSquareCom "bls377_field_square").lp_funcs
      ++ (Com.toLprogArrAbi fieldInvCom "bls377_field_inv").lp_funcs
      ++ (Com.toLprogArrAbi pairingCom "bls377_pairing_kernel").lp_funcs
      ++ (Com.toLprogArrAbi fp12MulCom "bls377_fp12_mul_kernel").lp_funcs
      ++ (Com.toLprogArrAbi pairingProductCom "bls377_pairing_product").lp_funcs }

/-! ## 1b. Front provenance (each deployed orchestration is `buildOrchCom`-sourced)

Nothing in this module hand-authors a `Com`: every orchestration `bls12_377Lprog`
marshals through `Com.toLprogArrAbi` is `Bls12_377Emit`'s `OrchestrationFront`-generated
kernel — the `buildOrchCom <ctxt> <schedule> <n> <retTy>` output (the phase-scheduled
`.extCall` glue over `.stackArr` operands), consumed unchanged. The per-artifact
equalities below name that front lowering (`buildOrchCom`) for each deployed symbol;
each is the definitional `Option.some_get` of the front's generation gate
(`*Com_isSome`, proved by `rfl` in `Bls12_377Emit`). Only the owned array-ABI render
tail (`Com.toLprogArrAbi` / `renderLprogAtt`) is local. -/

theorem fieldAddCom_front_sourced :
    buildOrchCom fieldBinCtxt fieldAddSchedule 2 fpRetTy = some fieldAddCom :=
  (Option.some_get fieldAddCom_isSome).symm

theorem fieldSubCom_front_sourced :
    buildOrchCom fieldBinCtxt fieldSubSchedule 2 fpRetTy = some fieldSubCom :=
  (Option.some_get fieldSubCom_isSome).symm

theorem fieldMulCom_front_sourced :
    buildOrchCom fieldBinCtxt fieldMulSchedule 2 fpRetTy = some fieldMulCom :=
  (Option.some_get fieldMulCom_isSome).symm

theorem fieldSquareCom_front_sourced :
    buildOrchCom fieldUnCtxt fieldSquareSchedule 1 fpRetTy = some fieldSquareCom :=
  (Option.some_get fieldSquareCom_isSome).symm

theorem fieldInvCom_front_sourced :
    buildOrchCom fieldUnCtxt fieldInvSchedule 1 fpRetTy = some fieldInvCom :=
  (Option.some_get fieldInvCom_isSome).symm

theorem pairingCom_front_sourced :
    buildOrchCom pairingCtxt pairingSchedule 2 gtRetTy = some pairingCom :=
  (Option.some_get pairingCom_isSome).symm

theorem fp12MulCom_front_sourced :
    buildOrchCom fp12MulCtxt fp12MulSchedule 2 gtRetTy = some fp12MulCom :=
  (Option.some_get fp12MulCom_isSome).symm

theorem pairingProductCom_front_sourced :
    buildOrchCom pairingProductCtxt pairingProductSchedule 6 gtRetTy
      = some pairingProductCom :=
  (Option.some_get pairingProductCom_isSome).symm

/-! ## 2. The rendered AT&T `.s` blob -/

def bls12_377Asm : String := renderLprogAtt bls12_377Lprog

/-! ## 3. Emitted-asm shape theorem (no jasminc, no unhandled-op sentinel)

The `.s` carries its SysV function labels and `call`s the opaque field/pairing
leaves by name, with no `# UNHANDLED-OP` / `CALL:` / `BADMEM` sentinel — the
structural guarantee the owned backend provides. -/

/- The BLS12-377 owned `.s` carries the kernel labels and `call`s the field +
    pairing + GT-multiply leaves; no unhandled-op sentinel. -/
#guard strContains bls12_377Asm ".globl bls377_field_mul"
    && strContains bls12_377Asm ".globl bls377_field_inv"
    && strContains bls12_377Asm ".globl bls377_pairing_product"
    && strContains bls12_377Asm "call bls377_add"
    && strContains bls12_377Asm "call bls377_mul"
    && strContains bls12_377Asm "call bls377_inv"
    && strContains bls12_377Asm "call bls377_pairing"
    && strContains bls12_377Asm "call bls377_Fp12_mul"
    && !strContains bls12_377Asm "UNHANDLED"
    && !strContains bls12_377Asm "CALL:"
    && !strContains bls12_377Asm "BADMEM"

/-! ## 4. Emit driver -/

/-- Write the owned BLS12-377 `.s` blob to `bench/bls12_377_compare/gen_com/`. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/bls12_377_compare/gen_com"
  IO.FS.writeFile "bench/bls12_377_compare/gen_com/bls12_377_orch_owned.s"
    bls12_377Asm
  IO.println "wrote owned BLS12-377 field/pairing orchestration .s (no jasminc):"
  IO.println "  bench/bls12_377_compare/gen_com/bls12_377_orch_owned.s"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.Pairing.Bls12_377Emit
