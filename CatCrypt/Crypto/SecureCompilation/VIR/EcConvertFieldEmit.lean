/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.EcConvertOps
public import Mathlib.Tactic.Ring

/-!
# Jacobian → affine point conversion on the HIGH FIELD DIALECT

The elliptic-curve `convert_point_type` Jacobian → affine normalisation of
fractalyze/prime-ir — factored as the standalone correspondence op
`EcConvertOps.jacobianToAffineF p (X, Y, Z) = (X·(Z⁻¹)², Y·(Z⁻¹)³)` — is here
realised as **two `Com fieldDialect` coordinate schedules** over the primitive
`FieldOp` leaves, exactly mirroring `EcPointAddFieldEmit.ecAddX3Prog` /
`ecAddY3Prog` (a `Com fieldDialect` returns ONE `fp` value, so the two output
coordinates split into two schedules):

    jacToAffXProg : Com fieldDialect [fp p, fp p, fp p] (fp p)   over (X, Y, Z)
        zi  = fInv Z        -- Z⁻¹
        zi2 = fMul zi zi    -- Z⁻¹ · Z⁻¹     (= (Z⁻¹)²)
        rx  = fMul X zi2    -- X · (Z⁻¹)²
        ret rx
    jacToAffYProg : Com fieldDialect [fp p, fp p, fp p] (fp p)   over (X, Y, Z)
        zi  = fInv Z
        zi2 = fMul zi zi
        zi3 = fMul zi2 zi   -- (Z⁻¹·Z⁻¹)·Z⁻¹  (= (Z⁻¹)³)
        ry  = fMul Y zi3    -- Y · (Z⁻¹)³
        ret ry

The field-op denotations are `ZMod p`'s native `⁻¹`/`*`, so each schedule denotes
(`rfl`) to the native product form `X · (Z⁻¹ · Z⁻¹)` / `Y · ((Z⁻¹ · Z⁻¹) · Z⁻¹)`;
a `ring` step rewrites those into the `(Z⁻¹)²`/`(Z⁻¹)³` powers of the
`jacobianToAffineF` leaf.

## What is proved here

* `jacToAffXProg` / `jacToAffYProg` — the two `Com fieldDialect` coordinate
  schedules over `Γ₀ = [fp p, fp p, fp p]` (the Jacobian inputs `X, Y, Z`), built
  straight from `FieldOp.fInv`/`FieldOp.fMul`.
* `jacToAffX_field_denote` / `jacToAffY_field_denote` — the native-product `rfl`
  denotation of each schedule.
* `jacToAffX_eq` / `jacToAffY_eq` — each schedule equals the corresponding
  component of the `EcConvertOps` leaf (`X·(Z⁻¹)²` / `Y·(Z⁻¹)³`, by `ring`).
* `jacToAff_denote` — the pair `(jacToAffXProg.denote …, jacToAffYProg.denote …)`
  equals the whole `EcConvertOps.jacobianToAffineF p (X, Y, Z)` — the field
  schedule REALISES prime-ir's `convert_point_type` (Jacobian → affine).

The companion `affine → Jacobian` direction is the constant `Z = 1` store
`(x, y) ↦ (x, y, 1)` (`EcConvertOps.affineToJacobianF`); it needs no field
arithmetic, so it has no field schedule here.

## Classification (read `VIR/DIALECTS.md`)

This is a **denote-preserving `fieldDialect` schedule**, NOT an emit-wired
kernel.  Each coordinate schedule descends to jasmin/bytes through the certified
`FieldDescent.fieldComToJasmin_denote` (`Com fieldDialect → Com jasminDialect`,
Stage-2 base-field word realization carried as the explicit `hVarJ`/`hOpJ`/`hExtJ`
hypotheses, GMP-KAT-gated), exactly as `EcPointAddFieldEmit.ecAddX3Jasmin_denote`
— we cite that descent here, we do not wire it (the bytes-reaching coordinate
conversion still flows through the existing `affToPoint` / MSM-normalise
`BatchInverse` kernels).

**All goals closed.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.EcConvertFieldEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.EcConvertOps

variable {p : Nat}

/-! ## 1. The input context and the De Bruijn variables

`Γ₀ = [fp p, fp p, fp p]` holds the Jacobian coordinates `X, Y, Z` at indices
`0, 1, 2`. -/

/-- The starting context: the Jacobian coordinates `X, Y, Z`. -/
abbrev Γ₀ (p : Nat) : Ctxt fieldDialect :=
  [FieldTy.fp p, FieldTy.fp p, FieldTy.fp p]

/-- De Bruijn variable for `X` (index 0). -/
def vX : Ctxt.Var (Γ₀ p) (FieldTy.fp p) := .here
/-- `Y` (index 1). -/
def vY : Ctxt.Var (Γ₀ p) (FieldTy.fp p) := .there .here
/-- `Z` (index 2). -/
def vZ : Ctxt.Var (Γ₀ p) (FieldTy.fp p) := .there (.there .here)

/-- The valuation `⟨X, Y, Z⟩`. -/
def eval (X Y Z : ZMod p) : Ctxt.Valuation (Γ₀ p) :=
  .cons X (.cons Y (.cons Z .nil))

/-! ## 2. The `x₃ = X·(Z⁻¹)²` coordinate schedule as a `Com fieldDialect`

    zi  = fInv Z         -- Z⁻¹;          X → 1, Y → 2, Z → 3
    zi2 = fMul zi zi     -- Z⁻¹·Z⁻¹;      zi → 1, X → 2
    rx  = fMul X zi2     -- X·(Z⁻¹)²;     zi2 → 0, X → 2
    ret rx
-/

/-- The affine `x = X·(Z⁻¹)²` coordinate schedule as a `Com fieldDialect` over
    `Γ₀`, ending in `fp p`. -/
def jacToAffXProg : Com fieldDialect (Γ₀ p) (FieldTy.fp p) :=
  -- zi = Z⁻¹             (Z at idx 2)
  .var (.mk (.fInv p) rfl (.cons vZ .nil))
  -- zi2 = zi * zi        (zi at idx 0)
  (.var (.mk (.fMul p) rfl (.cons .here (.cons .here .nil)))
  -- rx = X * zi2         (X shifted twice → idx 2, zi2 at idx 0)
  (.var (.mk (.fMul p) rfl
      (.cons (.there (.there vX)) (.cons .here .nil)))
  (.ret .here)))

/-! ## 3. The `y₃ = Y·(Z⁻¹)³` coordinate schedule as a `Com fieldDialect`

    zi  = fInv Z         -- Z⁻¹;            X → 1, Y → 2, Z → 3
    zi2 = fMul zi zi     -- Z⁻¹·Z⁻¹;        zi → 1
    zi3 = fMul zi2 zi    -- (Z⁻¹·Z⁻¹)·Z⁻¹;  zi2 → 0, zi → 1
    ry  = fMul Y zi3     -- Y·(Z⁻¹)³;       zi3 → 0, Y → 4
    ret ry
-/

/-- The affine `y = Y·(Z⁻¹)³` coordinate schedule as a `Com fieldDialect` over
    `Γ₀`, ending in `fp p`. -/
def jacToAffYProg : Com fieldDialect (Γ₀ p) (FieldTy.fp p) :=
  -- zi = Z⁻¹             (Z at idx 2)
  .var (.mk (.fInv p) rfl (.cons vZ .nil))
  -- zi2 = zi * zi        (zi at idx 0)
  (.var (.mk (.fMul p) rfl (.cons .here (.cons .here .nil)))
  -- zi3 = zi2 * zi       (zi2 at idx 0, zi at idx 1)
  (.var (.mk (.fMul p) rfl (.cons .here (.cons (.there .here) .nil)))
  -- ry = Y * zi3         (Y shifted three times → idx 4, zi3 at idx 0)
  (.var (.mk (.fMul p) rfl
      (.cons (.there (.there (.there vY))) (.cons .here .nil)))
  (.ret .here))))

/-! ## 4. The denotation ties — native-product `rfl`, then the `(Z⁻¹)ⁿ` leaf form

The field-op denotations `fInvF`/`fMulF` are `ZMod p`'s native `⁻¹`/`*`, so each
schedule denotes (`rfl`) to a native product; `ring` rewrites those into the
`(Z⁻¹)²`/`(Z⁻¹)³` powers of `EcConvertOps.jacobianToAffineF`. -/

/-- **`jacToAffXProg` denotes the native product `X · (Z⁻¹ · Z⁻¹)`.** -/
theorem jacToAffX_field_denote (X Y Z : ZMod p) :
    (jacToAffXProg (p := p)).denote (eval X Y Z) = X * (Z⁻¹ * Z⁻¹) := rfl

/-- **`jacToAffYProg` denotes the native product `Y · ((Z⁻¹ · Z⁻¹) · Z⁻¹)`.** -/
theorem jacToAffY_field_denote (X Y Z : ZMod p) :
    (jacToAffYProg (p := p)).denote (eval X Y Z) = Y * (Z⁻¹ * Z⁻¹ * Z⁻¹) := rfl

/-- **`jacToAffXProg` equals the `x`-component of the conversion leaf
    `X·(Z⁻¹)²`.** -/
theorem jacToAffX_eq (X Y Z : ZMod p) :
    (jacToAffXProg (p := p)).denote (eval X Y Z)
      = (jacobianToAffineF p (X, Y, Z)).1 := by
  rw [jacToAffX_field_denote]; ring_nf

/-- **`jacToAffYProg` equals the `y`-component of the conversion leaf
    `Y·(Z⁻¹)³`.** -/
theorem jacToAffY_eq (X Y Z : ZMod p) :
    (jacToAffYProg (p := p)).denote (eval X Y Z)
      = (jacobianToAffineF p (X, Y, Z)).2 := by
  rw [jacToAffY_field_denote]; ring_nf

/-! ## 5. The conversion tie — the pair re-wraps to `jacobianToAffineF`

The pair of coordinate schedules equals the whole `EcConvertOps` leaf — the field
schedules REALISE prime-ir's `convert_point_type` (Jacobian → affine). -/

/-- **The Jacobian → affine conversion tie.**  The pair of field-dialect
    coordinate Coms `(jacToAffXProg, jacToAffYProg)` equals the abstract
    conversion leaf `EcConvertOps.jacobianToAffineF p (X, Y, Z)`. -/
theorem jacToAff_denote (X Y Z : ZMod p) :
    ((jacToAffXProg (p := p)).denote (eval X Y Z),
     (jacToAffYProg (p := p)).denote (eval X Y Z))
      = jacobianToAffineF p (X, Y, Z) := by
  rw [jacToAffX_eq, jacToAffY_eq]

/-! ## 6. Tiny concrete smoke check (NOT a kernel KAT)

Over `ZMod 7`, on the Jacobian point `(X, Y, Z) = (2, 3, 1)` (already normalised,
`Z = 1` so `Z⁻¹ = 1`): the conversion is the identity on `(X, Y)`, returning
`(2, 3)`. -/

example :
    ((jacToAffXProg (p := 7)).denote (eval 2 3 1),
     (jacToAffYProg (p := 7)).denote (eval 2 3 1))
      = ((2, 3) : ZMod 7 × ZMod 7) := by with_unfolding_all rfl

end CatCrypt.Crypto.SecureCompilation.VIR.EcConvertFieldEmit
