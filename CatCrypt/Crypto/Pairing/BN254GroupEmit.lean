/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.Pairing.BN254EmittedFieldRealization
public import CatCrypt.Crypto.Pairing.BatchInverse
public import CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront

/-!
# Production BN254 `G1` group law emitted as a COMPOSITION over verified field leaves

`Pairing/Bn254Emit.lean` emits the BN254 `G1` group law as an **opaque
`extCall` group leaf** (`bn254_g1_add`): the whole short-Weierstrass formula
is one black box, the carried trusted edge (`EcLeafAgrees`). That leaves the
AUCurves-verified field tower (`bn254-safe-rust` `fp_add/sub/mul` + the Fermat
inverse) *disconnected* from the emitted group op — `Util/BN254Verified.lean`
and `BN254/EmittedFieldRealization.lean` realize the field kernels and the
affine coordinate maps, but the tie did not reach the emitted full group op.

This module closes that gap **the way P-256 / X25519 do it**: it controls the
export granularity and emits the affine point-add as a straight-line `Com` over
the **field leaves** (`fp_mul`, `fp_sub`, `fp_inv`) — *not* a single opaque
`bn254_g1_add` leaf. The short-Weierstrass distinct-point add

```
   λ   = (y₂ − y₁) · (x₂ − x₁)⁻¹
   x₃  = λ·λ − x₁ − x₂
   y₃  = λ·(x₁ − x₃) − y₁
```

is built as a chain of `fp_*` `extCall`s, and the `Com` denotation is proved
equal to `bn254AffineAdd` over `FpBN254` (`Util/BN254Verified.lean`) under

1. a **field-leaf agreement** (`FieldLeafAgrees`): the dialect leaf semantics
   `jasminExtSem` on the `fp_*` leaf names is the abstract field primitive —
   the same opaque-leaf edge `Bn254Emit` carries, but now at the *field*
   granularity (one `fp_mul`/`fp_sub`/`fp_inv` per leaf), and
2. a **field realization** (`FieldRealizes`): each field primitive, transported
   by the canonical-residue interpretation `wireToFp`, equals `FpBN254`'s native
   `*`/`−`/`⁻¹`. This is exactly `EmittedFieldRealization.feMul_realizes_mul`
   etc. lifted to the wire primitive — the AUCurves field tower.

Composing (1)+(2), `emittedAffineAdd_realizes` ties the field-leaf composition
to the abstract `G1` group op — the **full-group realization** P-256 has, now
for BN254 `G1`, with no opaque group leaf in the emitted term.

## Honesty boundary

The emitted point-add term genuinely contains only `fp_mul`/`fp_sub`/`fp_inv`
`extCall`s — there is no hidden `bn254_g1_add` leaf. The slope `λ` carries the
one base-field inverse (`fp_inv`); the two coordinate maps are polynomial in
`λ`. **Scope:** this is the `G1` base-field group add only. The pairing tower
(`Fp2`/`Fp6`/`Fp12` + Miller loop + final exponentiation) is **not** lifted —
it remains the documented opaque-leaf edge of `Pairing/Bn254Emit.lean`
(`PairingLeafAgrees`).

The KAT (`bench/bn254_group_compare/`) checks the re-emitted point-add is
byte-identical to the production `G1` add on the EIP-196 generator chain.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.BN254GroupEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront
open CatCrypt.Util

/-! ## 1. Wire layout for a BN254 base-field element -/

/-- A BN254 base-field element on the wire: `32` bytes (4 little-endian `u64`
    limbs), matching the AUCurves `Fp([u64;4])` layout. -/
def FESZ : Nat := 32

/-- The on-wire field-element type. -/
abbrev FpWire : Type := Fin FESZ → BitVec 8

/-! ## 2. The field-leaf spec (opaque `extCall`, carried agreement) — the
    AUCurves-verified field ops, NOT a group leaf -/

/-- Leaf name the front emits for the BN254 base-field Montgomery multiply.

    **Own-emit wiring (BN254 field-mul):** this resolves at link time to the
    in-Lean-x86-backend-emitted CIOS Montgomery multiply
    `bn254_mont_mul_x86_from_lean`
    (`SecureCompilation/X86Backend/Bn254MontMulKernel.lean`, a 4-iteration CIOS
    MULX + dual ADCX/ADOX kernel through the OWNED x86 backend, the BN254 analog
    of the BLS12-381 `Bls12381MontMulKernel` #490), **replacing the adopted
    fiat-crypto/bedrock2 WBW Montgomery tower** (`bn254-safe-rust`) that BN254
    was the last production curve to still adopt for its `Fp` multiply (per the
    #489 cross-curve audit, `bench/CROSS_CURVE_AUDIT.md`).  With the divstep
    inverse already own-routed (`invLeafName`, #489), this lifts the BN254 `G1`
    base-field group law to own-emitted end-to-end down to `fp_mul`/`fp_sub`/
    `fp_inv`.  The emitted block is `runBlock`-verified
    (`bn254MontMulBlock_lowering_correct`) and overflow-free
    (`bn254MontMulAlloc_no_overflow`); value-level correctness
    (`a·b·R⁻¹ mod p`) is the external KAT `bench/bn254_fieldmul_compare`
    (lean == adopted-fiat-bedrock2 == GMP, 8×8 corners + 50000 random). -/
def mulLeafName : String := "bn254_fp_mul"
/-- Leaf name for the AUCurves BN254 field subtract. -/
def subLeafName : String := "bn254_fp_sub"
/-- Leaf name for the AUCurves BN254 field add (used by a doubling slope). -/
def addLeafName : String := "bn254_fp_add"
/-- Leaf name for the AUCurves BN254 base-field inverse.

    **#489 safegcd-uniform wiring:** this routes to the AUCurves verified-CT
    Bernstein–Yang safegcd **divstep** inverter `bn254_invert_divstep_sat`
    (`Vale/SafegcdBN254.lean`, 10 outer × 59 = 590 divsteps over 5-limb
    Signed62), replacing the prior Fermat `a^{p−2}` addition-chain
    (`bn254_inv`, `Vale/BN254.lean`).  BN254 was the one production curve whose
    `Fp` inverse was still Fermat while the sibling P-curves and BLS12-381
    already routed through the divstep leaf; the cross-curve audit (#489)
    flipped it onto the same recipe that put the BLS12-381 inverse at ~1.10×
    blst's own divstep (#488).  The C symbol that resolves at link time is
    `safegcd_bn254_invert` (AUCurves staticlib re-exporting
    `bn254_invert_divstep_sat`).  Value-level correctness is the AUCurves
    `x · invert(x) ≡ 1 (mod p)` round-trip KAT
    (`safegcd_bn254.rs::tests::bn254_invert_times_self_is_one`). -/
def invLeafName : String := "bn254_invert_divstep_sat"

/-- Binary field-leaf signature (`fp_mul`, `fp_sub`). -/
def binArgTys : List JasminTy := [.stackArr 8 FESZ, .stackArr 8 FESZ]
/-- Unary field-leaf signature (`fp_inv`). -/
def unArgTys : List JasminTy := [.stackArr 8 FESZ]
/-- Every field leaf returns a field element. -/
def feRetTy : JasminTy := .stackArr 8 FESZ

/-- The leaf-semantics carrier — the exact shape of `jasminExtSem`. -/
abbrev LeafSem : Type :=
  (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
    HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧

/-- The abstract BN254 **field** primitive interface (NOT the group): the three
    field ops the affine point-add is built from, on the on-wire field
    representation. These are the AUCurves `fp_mul/sub/inv`. -/
structure FieldPrimitives where
  /-- Field multiply `a · b`. -/
  mul : FpWire → FpWire → FpWire
  /-- Field subtract `a − b`. -/
  sub : FpWire → FpWire → FpWire
  /-- Field add `a + b`. -/
  add : FpWire → FpWire → FpWire
  /-- Field inverse `a⁻¹`. -/
  inv : FpWire → FpWire

/-- Field-multiply leaf agreement. -/
def MulLeafAgrees (prims : FieldPrimitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) binArgTys,
    leafSem mulLeafName binArgTys feRetTy args = prims.mul (args.head) (args.tail.head)

/-- Field-subtract leaf agreement. -/
def SubLeafAgrees (prims : FieldPrimitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) binArgTys,
    leafSem subLeafName binArgTys feRetTy args = prims.sub (args.head) (args.tail.head)

/-- Field-add leaf agreement. -/
def AddLeafAgrees (prims : FieldPrimitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) binArgTys,
    leafSem addLeafName binArgTys feRetTy args = prims.add (args.head) (args.tail.head)

/-- Field-inverse leaf agreement. -/
def InvLeafAgrees (prims : FieldPrimitives) (leafSem : LeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) unArgTys,
    leafSem invLeafName unArgTys feRetTy args = prims.inv (args.head)

/-- The full field-leaf agreement: `leafSem` realises all four field
    primitives on the four `fp_*` leaf names. The AUCurves `bn254-safe-rust`
    field leaves are the intended witness. -/
def FieldLeafAgrees (prims : FieldPrimitives) (leafSem : LeafSem) : Prop :=
  MulLeafAgrees prims leafSem ∧ SubLeafAgrees prims leafSem
    ∧ AddLeafAgrees prims leafSem ∧ InvLeafAgrees prims leafSem

/-! ## 3. The canonical-residue interpretation `wireToFp` and the field
    realization edge -/

/-- The canonical-residue interpretation of an on-wire field element as an
    `FpBN254` element. -/
opaque wireToFp : FpWire → FpBN254

/-- **The field realization edge** (the AUCurves field tower, carried at the
    wire-primitive level). Each field primitive, transported by `wireToFp`,
    computes `FpBN254`'s native operation. This is
    `EmittedFieldRealization.feMul_realizes_mul`/`feSub_realizes_sub` (and the
    inverse analogue) lifted to the wire primitive — the commuting square the
    AUCurves machine-checked field ops satisfy. -/
structure FieldRealizes (prims : FieldPrimitives) : Prop where
  /-- `wireToFp (mul a b) = wireToFp a * wireToFp b`. -/
  mul_realizes : ∀ a b, wireToFp (prims.mul a b) = wireToFp a * wireToFp b
  /-- `wireToFp (sub a b) = wireToFp a - wireToFp b`. -/
  sub_realizes : ∀ a b, wireToFp (prims.sub a b) = wireToFp a - wireToFp b
  /-- `wireToFp (add a b) = wireToFp a + wireToFp b`. -/
  add_realizes : ∀ a b, wireToFp (prims.add a b) = wireToFp a + wireToFp b
  /-- `wireToFp (inv a) = (wireToFp a)⁻¹`. -/
  inv_realizes : ∀ a, wireToFp (prims.inv a) = (wireToFp a)⁻¹

/-! ## 4. Field-leaf `Expr` builders + denotation (the `extCall` bridge point) -/

/-- Build a binary field-leaf `Expr` (`fp_mul`/`fp_sub`) from two field
    variables in scope. -/
def binLeafExpr {Γ : Ctxt jasminDialect} (name : String)
    (a b : Ctxt.Var Γ (.stackArr 8 FESZ)) : Expr jasminDialect Γ feRetTy :=
  { op := .extCall name binArgTys feRetTy, retTy_eq := rfl,
    args := .cons a (.cons b .nil) }

/-- Build a unary field-leaf `Expr` (`fp_inv`) from one field variable. -/
def unLeafExpr {Γ : Ctxt jasminDialect} (name : String)
    (a : Ctxt.Var Γ (.stackArr 8 FESZ)) : Expr jasminDialect Γ feRetTy :=
  { op := .extCall name unArgTys feRetTy, retTy_eq := rfl, args := .cons a .nil }

/-- A binary field-leaf `Expr` denotes to `jasminExtSem` of the looked-up
    operands. By `rfl`. -/
theorem binLeafExpr_denote {Γ : Ctxt jasminDialect} (name : String)
    (a b : Ctxt.Var Γ (.stackArr 8 FESZ)) (V : Ctxt.Valuation Γ) :
    (binLeafExpr name a b).denote V
      = jasminExtSem name binArgTys feRetTy
          (.cons (a.lookup V) (.cons (b.lookup V) .nil)) :=
  rfl

/-- A unary field-leaf `Expr` denotes to `jasminExtSem` of the looked-up
    operand. By `rfl`. -/
theorem unLeafExpr_denote {Γ : Ctxt jasminDialect} (name : String)
    (a : Ctxt.Var Γ (.stackArr 8 FESZ)) (V : Ctxt.Valuation Γ) :
    (unLeafExpr name a).denote V
      = jasminExtSem name unArgTys feRetTy (.cons (a.lookup V) .nil) :=
  rfl

/-! ## 5. The slope `λ = (Qy − Py) · (Qx − Px)⁻¹` as a field-leaf `Com`

ABI: `Γ = [Px, Py, Qx, Qy]`. Emits `t1 = fp_sub(Qy, Py)`, `t2 = fp_sub(Qx, Px)`,
`t3 = fp_inv(t2)`, `λ = fp_mul(t1, t3)`. Four field leaves, no group leaf. -/

/-- The input context of the slope kernel: `[Px, Py, Qx, Qy]` (four field
    elements). -/
def feQuadCtxt : Ctxt jasminDialect :=
  [.stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ]

/-- The input context of the `x₃` kernel: `[lam, Px, Qx]` (three field
    elements). -/
def feTripleCtxt : Ctxt jasminDialect :=
  [.stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ]

/-- The slope `λ` Com over the four input coordinates — the **hand-authored
    shadow** (the denote reference). -/
def lamComShadow :
    Com jasminDialect
      [.stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ]
      (.stackArr 8 FESZ) :=
  -- Γ = [Px, Py, Qx, Qy]
  .var (binLeafExpr subLeafName
          (Γ := [.stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ])
          (.there (.there (.there .here))) (.there .here))               -- t1 = Qy − Py
    -- Γ = [t1, Px, Py, Qx, Qy]
    (.var (binLeafExpr subLeafName
            (.there (.there (.there .here))) (.there .here))             -- t2 = Qx − Px
      -- Γ = [t2, t1, Px, Py, Qx, Qy]
      (.var (unLeafExpr invLeafName .here)                               -- t3 = t2⁻¹
        -- Γ = [t3, t2, t1, Px, Py, Qx, Qy]
        (.var (binLeafExpr mulLeafName (.there (.there .here)) .here)    -- λ = t1 · t3
          (.ret .here))))

/-- The slope `λ` as an `OrchestrationFront` phase schedule over `[Px, Py, Qx,
    Qy]`. Root slots on the inputs: `Px = 3, Py = 2, Qx = 1, Qy = 0`.
    `t₁ = fp_sub(Qy, Py)` (slots `[0, 2]`, result slot `4`),
    `t₂ = fp_sub(Qx, Px)` (slots `[1, 3]`, result slot `5`),
    `t₃ = fp_inv(t₂)` (slot `[5]`, result slot `6`),
    `λ = fp_mul(t₁, t₃)` (slots `[4, 6]`, result slot `7`, returned). -/
def lamSchedule : List CallPhase :=
  [ { leaf := subLeafName, argTys := binArgTys, retTy := feRetTy, argSlots := [0, 2] }
  , { leaf := subLeafName, argTys := binArgTys, retTy := feRetTy, argSlots := [1, 3] }
  , { leaf := invLeafName, argTys := unArgTys,  retTy := feRetTy, argSlots := [5] }
  , { leaf := mulLeafName, argTys := binArgTys, retTy := feRetTy, argSlots := [4, 6] } ]

/-- **Generation gate.** The front resolves the slope schedule. -/
theorem lamCom_isSome :
    (buildOrchCom feQuadCtxt lamSchedule 7 feRetTy).isSome = true := by rfl

/-- **The deployed slope kernel, front-sourced** by `buildOrchCom` from
    `lamSchedule`. Definitionally the hand shadow (`lamCom_eq_shadow`). -/
def lamCom :
    Com jasminDialect
      [.stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ]
      (.stackArr 8 FESZ) :=
  (buildOrchCom feQuadCtxt lamSchedule 7 feRetTy).get lamCom_isSome

/-- **Exactness.** The front-sourced deployed `lamCom` is definitionally the hand
    shadow — the auto-resolved de-Bruijn operand chains coincide with the
    hand-threaded `.here`/`.there` chains. -/
theorem lamCom_eq_shadow : lamCom = lamComShadow := by rfl

/-- **The slope Com denotes to the abstract slope** `(Qy − Py) · (Qx − Px)⁻¹`
    over `FpBN254`, under the field-leaf agreement and the field realization. No
    opaque group leaf is involved — only `fp_sub`/`fp_inv`/`fp_mul`. -/
theorem lamComShadow_denote (prims : FieldPrimitives)
    (hLeaf : FieldLeafAgrees prims jasminExtSem) (hReal : FieldRealizes prims)
    (Px Py Qx Qy : FpWire) :
    wireToFp (lamComShadow.denote (.cons Px (.cons Py (.cons Qx (.cons Qy .nil)))))
      = (wireToFp Qy - wireToFp Py) * (wireToFp Qx - wireToFp Px)⁻¹ := by
  obtain ⟨hMul, hSub, _hAdd, hInv⟩ := hLeaf
  show wireToFp (jasminExtSem mulLeafName binArgTys feRetTy
        (.cons (jasminExtSem subLeafName binArgTys feRetTy (.cons Qy (.cons Py .nil)))
          (.cons (jasminExtSem invLeafName unArgTys feRetTy
            (.cons (jasminExtSem subLeafName binArgTys feRetTy
              (.cons Qx (.cons Px .nil))) .nil)) .nil)))
      = (wireToFp Qy - wireToFp Py) * (wireToFp Qx - wireToFp Px)⁻¹
  rw [hSub (.cons Qy (.cons Py .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hSub (.cons Qx (.cons Px .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hInv (.cons (prims.sub Qx Px) .nil)]
  simp only [HVector.head]
  rw [hMul (.cons (prims.sub Qy Py) (.cons (prims.inv (prims.sub Qx Px)) .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hReal.mul_realizes, hReal.sub_realizes, hReal.inv_realizes, hReal.sub_realizes]

/-- **The deployed slope Com denotes the abstract slope** (front-sourced). Via
    `lamCom_eq_shadow` + the shadow's denote, so downstream users of `lamCom` by
    name are unaffected by the front-sourcing. -/
theorem lamCom_denote (prims : FieldPrimitives)
    (hLeaf : FieldLeafAgrees prims jasminExtSem) (hReal : FieldRealizes prims)
    (Px Py Qx Qy : FpWire) :
    wireToFp (lamCom.denote (.cons Px (.cons Py (.cons Qx (.cons Qy .nil)))))
      = (wireToFp Qy - wireToFp Py) * (wireToFp Qx - wireToFp Px)⁻¹ := by
  rw [lamCom_eq_shadow]; exact lamComShadow_denote prims hLeaf hReal Px Py Qx Qy

/-! ## 6. The `x₃` coordinate `x₃ = λ·λ − x₁ − x₂` as a field-leaf `Com`

ABI: `Γ = [lam, Px, Qx]`. Emits `s = fp_mul(lam, lam)`, `t = fp_sub(s, Px)`,
`x₃ = fp_sub(t, Qx)`. -/

/-- The `x₃` Com given the precomputed slope residue — the **hand-authored
    shadow**. -/
def bn254AddxComShadow :
    Com jasminDialect
      [.stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ]
      (.stackArr 8 FESZ) :=
  -- Γ = [lam, Px, Qx]
  .var (binLeafExpr mulLeafName
          (Γ := [.stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ])
          .here .here)                                                   -- s = lam · lam
    -- Γ = [s, lam, Px, Qx]
    (.var (binLeafExpr subLeafName .here (.there (.there .here)))        -- t = s − Px
      -- Γ = [t, s, lam, Px, Qx]
      (.var (binLeafExpr subLeafName .here (.there (.there (.there (.there .here)))))  -- x3 = t − Qx
        (.ret .here)))

/-- The `x₃` kernel as an `OrchestrationFront` phase schedule over `[lam, Px,
    Qx]`. Root slots: `lam = 2, Px = 1, Qx = 0`. `s = fp_mul(lam, lam)` (slots
    `[2, 2]`, result slot `3`), `t = fp_sub(s, Px)` (slots `[3, 1]`, result slot
    `4`), `x₃ = fp_sub(t, Qx)` (slots `[4, 0]`, result slot `5`, returned). -/
def bn254AddxSchedule : List CallPhase :=
  [ { leaf := mulLeafName, argTys := binArgTys, retTy := feRetTy, argSlots := [2, 2] }
  , { leaf := subLeafName, argTys := binArgTys, retTy := feRetTy, argSlots := [3, 1] }
  , { leaf := subLeafName, argTys := binArgTys, retTy := feRetTy, argSlots := [4, 0] } ]

/-- **Generation gate.** The front resolves the `x₃` schedule. -/
theorem bn254AddxCom_isSome :
    (buildOrchCom feTripleCtxt bn254AddxSchedule 5 feRetTy).isSome = true := by rfl

/-- **The deployed `x₃` kernel, front-sourced** by `buildOrchCom`. Definitionally
    the hand shadow (`bn254AddxCom_eq_shadow`). -/
def bn254AddxCom :
    Com jasminDialect
      [.stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ]
      (.stackArr 8 FESZ) :=
  (buildOrchCom feTripleCtxt bn254AddxSchedule 5 feRetTy).get bn254AddxCom_isSome

/-- **Exactness.** `bn254AddxCom` is definitionally the hand shadow. -/
theorem bn254AddxCom_eq_shadow : bn254AddxCom = bn254AddxComShadow := by rfl

/-- **The `x₃` Com realizes `bn254AffineRx` (`λ·λ − x₁ − x₂`)** over `FpBN254`,
    under the field-leaf agreement + realization. Built only from `fp_mul` and
    `fp_sub` leaves. -/
theorem bn254AddxComShadow_denote (prims : FieldPrimitives)
    (hLeaf : FieldLeafAgrees prims jasminExtSem) (hReal : FieldRealizes prims)
    (lam Px Qx : FpWire) :
    wireToFp (bn254AddxComShadow.denote (.cons lam (.cons Px (.cons Qx .nil))))
      = bn254AffineRx (wireToFp lam) (wireToFp Px) (wireToFp Qx) := by
  obtain ⟨hMul, hSub, _hAdd, _⟩ := hLeaf
  unfold bn254AffineRx
  show wireToFp (jasminExtSem subLeafName binArgTys feRetTy
        (.cons (jasminExtSem subLeafName binArgTys feRetTy
          (.cons (jasminExtSem mulLeafName binArgTys feRetTy (.cons lam (.cons lam .nil)))
            (.cons Px .nil))) (.cons Qx .nil)))
      = wireToFp lam * wireToFp lam - wireToFp Px - wireToFp Qx
  rw [hMul (.cons lam (.cons lam .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hSub (.cons (prims.mul lam lam) (.cons Px .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hSub (.cons (prims.sub (prims.mul lam lam) Px) (.cons Qx .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hReal.sub_realizes, hReal.sub_realizes, hReal.mul_realizes]

/-- **The deployed `x₃` Com realizes `bn254AffineRx`** (front-sourced). Via
    `bn254AddxCom_eq_shadow` + the shadow's denote. -/
theorem bn254AddxCom_denote (prims : FieldPrimitives)
    (hLeaf : FieldLeafAgrees prims jasminExtSem) (hReal : FieldRealizes prims)
    (lam Px Qx : FpWire) :
    wireToFp (bn254AddxCom.denote (.cons lam (.cons Px (.cons Qx .nil))))
      = bn254AffineRx (wireToFp lam) (wireToFp Px) (wireToFp Qx) := by
  rw [bn254AddxCom_eq_shadow]; exact bn254AddxComShadow_denote prims hLeaf hReal lam Px Qx

/-! ## 7. The `y₃` coordinate `y₃ = λ·(x₁ − x₃) − y₁` as a field-leaf `Com`

ABI: `Γ = [lam, Px, Rx, Py]`. Emits `d = fp_sub(Px, Rx)`, `m = fp_mul(lam, d)`,
`y₃ = fp_sub(m, Py)`. -/

/-- The `y₃` Com given the slope residue and the already-computed `Rx` — the
    **hand-authored shadow**. -/
def bn254AddyComShadow :
    Com jasminDialect
      [.stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ]
      (.stackArr 8 FESZ) :=
  -- Γ = [lam, Px, Rx, Py]
  .var (binLeafExpr subLeafName
          (Γ := [.stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ])
          (.there .here) (.there (.there .here)))                        -- d = Px − Rx
    -- Γ = [d, lam, Px, Rx, Py]
    (.var (binLeafExpr mulLeafName (.there .here) .here)                 -- m = lam · d
      -- Γ = [m, d, lam, Px, Rx, Py]
      (.var (binLeafExpr subLeafName .here (.there (.there (.there (.there (.there .here)))))) -- y3 = m − Py
        (.ret .here)))

/-- The `y₃` kernel as an `OrchestrationFront` phase schedule over `[lam, Px, Rx,
    Py]`. Root slots: `lam = 3, Px = 2, Rx = 1, Py = 0`. `d = fp_sub(Px, Rx)`
    (slots `[2, 1]`, result slot `4`), `m = fp_mul(lam, d)` (slots `[3, 4]`,
    result slot `5`), `y₃ = fp_sub(m, Py)` (slots `[5, 0]`, result slot `6`,
    returned). -/
def bn254AddySchedule : List CallPhase :=
  [ { leaf := subLeafName, argTys := binArgTys, retTy := feRetTy, argSlots := [2, 1] }
  , { leaf := mulLeafName, argTys := binArgTys, retTy := feRetTy, argSlots := [3, 4] }
  , { leaf := subLeafName, argTys := binArgTys, retTy := feRetTy, argSlots := [5, 0] } ]

/-- **Generation gate.** The front resolves the `y₃` schedule. -/
theorem bn254AddyCom_isSome :
    (buildOrchCom feQuadCtxt bn254AddySchedule 6 feRetTy).isSome = true := by rfl

/-- **The deployed `y₃` kernel, front-sourced** by `buildOrchCom`. Definitionally
    the hand shadow (`bn254AddyCom_eq_shadow`). -/
def bn254AddyCom :
    Com jasminDialect
      [.stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ, .stackArr 8 FESZ]
      (.stackArr 8 FESZ) :=
  (buildOrchCom feQuadCtxt bn254AddySchedule 6 feRetTy).get bn254AddyCom_isSome

/-- **Exactness.** `bn254AddyCom` is definitionally the hand shadow. -/
theorem bn254AddyCom_eq_shadow : bn254AddyCom = bn254AddyComShadow := by rfl

/-- **The `y₃` Com realizes `bn254AffineRy` (`λ·(x₁ − x₃) − y₁`)** over
    `FpBN254`, under the field-leaf agreement + realization. Built only from
    `fp_sub` and `fp_mul` leaves. -/
theorem bn254AddyComShadow_denote (prims : FieldPrimitives)
    (hLeaf : FieldLeafAgrees prims jasminExtSem) (hReal : FieldRealizes prims)
    (lam Px Rx Py : FpWire) :
    wireToFp (bn254AddyComShadow.denote (.cons lam (.cons Px (.cons Rx (.cons Py .nil)))))
      = bn254AffineRy (wireToFp lam) (wireToFp Px) (wireToFp Rx) (wireToFp Py) := by
  obtain ⟨hMul, hSub, _hAdd, _⟩ := hLeaf
  unfold bn254AffineRy
  show wireToFp (jasminExtSem subLeafName binArgTys feRetTy
        (.cons (jasminExtSem mulLeafName binArgTys feRetTy
          (.cons lam (.cons (jasminExtSem subLeafName binArgTys feRetTy
            (.cons Px (.cons Rx .nil))) .nil))) (.cons Py .nil)))
      = wireToFp lam * (wireToFp Px - wireToFp Rx) - wireToFp Py
  rw [hSub (.cons Px (.cons Rx .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hMul (.cons lam (.cons (prims.sub Px Rx) .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hSub (.cons (prims.mul lam (prims.sub Px Rx)) (.cons Py .nil))]
  simp only [HVector.head, HVector.tail]
  rw [hReal.sub_realizes, hReal.mul_realizes, hReal.sub_realizes]

/-- **The deployed `y₃` Com realizes `bn254AffineRy`** (front-sourced). Via
    `bn254AddyCom_eq_shadow` + the shadow's denote. -/
theorem bn254AddyCom_denote (prims : FieldPrimitives)
    (hLeaf : FieldLeafAgrees prims jasminExtSem) (hReal : FieldRealizes prims)
    (lam Px Rx Py : FpWire) :
    wireToFp (bn254AddyCom.denote (.cons lam (.cons Px (.cons Rx (.cons Py .nil)))))
      = bn254AffineRy (wireToFp lam) (wireToFp Px) (wireToFp Rx) (wireToFp Py) := by
  rw [bn254AddyCom_eq_shadow]
  exact bn254AddyComShadow_denote prims hLeaf hReal lam Px Rx Py

/-! ## 8. The full emitted affine point-add realizes `bn254AffineAdd` -/

/-- An on-wire affine point: the two coordinates as field words. -/
structure WirePoint where
  /-- Affine `x`-coordinate. -/
  x : FpWire
  /-- Affine `y`-coordinate. -/
  y : FpWire

/-- Interpret an on-wire point as an abstract `BN254Point`. -/
def WirePoint.toAlg (P : WirePoint) : BN254Point :=
  { x := wireToFp P.x, y := wireToFp P.y }

/-- The emitted affine point-add as the composition of the three field-leaf
    `Com`s: compute `λ`, then `x₃` via `bn254AddxCom`, then `y₃` via
    `bn254AddyCom` (which consumes `x₃`). -/
def emittedAffineAdd (P Q : WirePoint) : WirePoint :=
  let lam := lamCom.denote (.cons P.x (.cons P.y (.cons Q.x (.cons Q.y .nil))))
  let rx := bn254AddxCom.denote (.cons lam (.cons P.x (.cons Q.x .nil)))
  let ry := bn254AddyCom.denote (.cons lam (.cons P.x (.cons rx (.cons P.y .nil))))
  { x := rx, y := ry }

/-- **The emitted field-leaf composition realizes the abstract `G1` group op.**

    The on-wire affine point-add, assembled from the slope / `x₃` / `y₃`
    field-leaf `Com`s and interpreted through `wireToFp` coordinate-wise, equals
    `bn254AffineAdd` over `FpBN254` applied to the interpreted slope and points —
    where the interpreted slope is exactly `(Qy − Py)·(Qx − Px)⁻¹`. The
    full-group realization, with the emitted term a genuine field-leaf
    composition (no opaque `bn254_g1_add`). -/
theorem emittedAffineAdd_realizes (prims : FieldPrimitives)
    (hLeaf : FieldLeafAgrees prims jasminExtSem) (hReal : FieldRealizes prims)
    (P Q : WirePoint) :
    (emittedAffineAdd P Q).toAlg
      = bn254AffineAdd
          ((wireToFp Q.y - wireToFp P.y) * (wireToFp Q.x - wireToFp P.x)⁻¹)
          P.toAlg Q.toAlg := by
  unfold emittedAffineAdd bn254AffineAdd WirePoint.toAlg
  refine BN254Point.mk.injEq .. ▸ ⟨?_, ?_⟩
  · -- x-coordinate
    rw [bn254AddxCom_denote prims hLeaf hReal, lamCom_denote prims hLeaf hReal]
  · -- y-coordinate; the inner `x₃` is `bn254AffineRx` of the interpreted slope
    rw [bn254AddyCom_denote prims hLeaf hReal, lamCom_denote prims hLeaf hReal,
      bn254AddxCom_denote prims hLeaf hReal, lamCom_denote prims hLeaf hReal]

/-! ## 6. Batched affine conversion via Montgomery's trick

Converting a batch of `G1` points to affine, or computing a batch of chord
denominators `(x₂ − x₁)` for a multi-point add / table precompute, needs one
field inverse **per point**. The naive path emits `n` `bn254_invert_divstep_sat`
leaves (each a Bernstein–Yang safegcd `divstep` chain over this 254-bit prime,
10 outer × 59 = 590 divsteps, ~9× a field multiply per the #488 BLS12-381
measurement). **Montgomery's trick** (`Pairing/BatchInverse`) emits **one**
`fp_inv` leaf plus `fp_mul` leaves and recovers each `aᵢ⁻¹`.

`wireUnwind`/`wireBatchInv` build that schedule from the *same*
`FieldPrimitives.{mul, inv}` the affine point-add already uses, so the only new
emitted leaf shapes are `bn254_fp_mul` and a single `bn254_invert_divstep_sat`. The
realization theorem `wireBatchInv_realizes` proves the interpreted batched result
is bit-identical to the per-point inversion `as.map (·⁻¹)`, under the *same*
`FieldRealizes` edge the rest of this module carries.

The in-loop Pippenger/MSM add is projective and inversion-free; the win is in the
table-setup / multi-point projective→affine conversion. -/

/-- Wire-level trailing product `aᵢ · ⋯ · a_{n-1}` of a nonempty tail, built from
    `prims.mul`. -/
def trailingProd (prims : FieldPrimitives) : FpWire → List FpWire → FpWire
  | a, []      => a
  | a, b :: bs => prims.mul a (trailingProd prims b bs)

/-- `wireToFp` of a wire trailing product is the field product of the interpreted
    elements. -/
theorem trailingProd_realizes (prims : FieldPrimitives) (hReal : FieldRealizes prims) :
    ∀ (a : FpWire) (as : List FpWire),
      wireToFp (trailingProd prims a as) = (wireToFp a) * (as.map wireToFp).prod
  | a, []      => by simp [trailingProd]
  | a, b :: bs => by
    simp only [trailingProd, List.map_cons, List.prod_cons]
    rw [hReal.mul_realizes, trailingProd_realizes prims hReal b bs, ← mul_assoc]

/-- Wire-level backward unwind built from `prims.mul`. `u` is the wire inverse of
    the total product of the whole batch. Mirrors `BatchInverse.unwind`. -/
def wireUnwind (prims : FieldPrimitives) : List FpWire → FpWire → List FpWire
  | [],          _ => []
  | [_],         u => [u]
  | a :: b :: bs, u =>
      prims.mul u (trailingProd prims b bs)
        :: wireUnwind prims (b :: bs) (prims.mul u a)

/-- `wireToFp` of the wire unwind is the field-generic `BatchInverse.unwind` of
    the interpreted inputs and inverse. -/
theorem wireUnwind_realizes (prims : FieldPrimitives) (hReal : FieldRealizes prims) :
    ∀ (as : List FpWire) (u : FpWire),
      (wireUnwind prims as u).map wireToFp
        = BatchInverse.unwind (as.map wireToFp) (wireToFp u)
  | [],          u => by simp [wireUnwind]
  | [a],         u => by simp [wireUnwind, BatchInverse.unwind]
  | a :: b :: bs, u => by
    simp only [wireUnwind, List.map_cons, BatchInverse.unwind_cons]
    refine List.cons.injEq .. |>.mpr ⟨?_, ?_⟩
    · rw [hReal.mul_realizes, trailingProd_realizes prims hReal]
      simp [List.prod_cons]
    · rw [wireUnwind_realizes prims hReal (b :: bs) (prims.mul u a),
        hReal.mul_realizes]
      simp [List.map_cons]

/-- Montgomery's batch inversion at the wire level: one `fp_inv` of the total
    product, then unwind. Exactly **one** `bn254_invert_divstep_sat` leaf. -/
def wireBatchInv (prims : FieldPrimitives) : List FpWire → List FpWire
  | []      => []
  | a :: as => wireUnwind prims (a :: as) (prims.inv (trailingProd prims a as))

/-- **Batch-inversion realization (bit-identical to per-point inversion).** When
    every interpreted input is nonzero, the emitted batched inverse — one
    `bn254_invert_divstep_sat` leaf plus `bn254_fp_mul` leaves — interprets to exactly the
    per-point inverses `(wireToFp aᵢ)⁻¹`. Proved from
    `BatchInverse.unwind_eq_map_inv` via the unwind/trailing-product realizations
    and the `FieldRealizes.inv_realizes` edge. -/
theorem wireBatchInv_realizes (prims : FieldPrimitives) (hReal : FieldRealizes prims)
    (as : List FpWire) (h : ∀ a ∈ as, wireToFp a ≠ 0) :
    (wireBatchInv prims as).map wireToFp = (as.map wireToFp).map (·⁻¹) := by
  cases as with
  | nil => simp [wireBatchInv]
  | cons a as =>
    simp only [wireBatchInv]
    rw [wireUnwind_realizes prims hReal, hReal.inv_realizes,
      trailingProd_realizes prims hReal]
    have hprod : wireToFp a * (as.map wireToFp).prod = ((a :: as).map wireToFp).prod := by
      simp [List.map_cons, List.prod_cons]
    rw [hprod]
    have hne : ∀ x ∈ (a :: as).map wireToFp, x ≠ 0 := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact h y hy
    exact (BatchInverse.unwind_eq_map_inv ((a :: as).map wireToFp) hne)

end CatCrypt.Crypto.Pairing.BN254GroupEmit
