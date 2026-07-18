/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.Optimizer

/-!
# `ed25519_compress` as a `Com catCryptDialect` program

A **parallel** `Com`-level handle for the Ed25519 point-compression
operation, alongside the `LowCT`-level `CompressEmit.ed25519_compress_cmd`.

## Why a parallel `Com` value?

`CompressEmit.lean` operates on `LowCT`, the byte-buffer / out-pointer
IR. `Optimizer.optimize` operates on `Com catCryptDialect`, the SSA IR
over `CryptoTy`. A direct `LowCT → Com` bridge would be a sizeable
extra piece of infrastructure (it would need to map every leaf's
byte-buffer ABI to the `CryptoTy.memref`/`extCall` shape). Instead we
expose a *hand-authored* `Com` value that mirrors the seven-leaf
decomposition documented in `CompressEmit.lean`, and *use that* as the
input to `optimize`.

This is sufficient for the optimizer wiring goal: it gives a `Com`
value to optimize, and `Optimizer.optimize_denote_eq` immediately gives
denotational preservation. Linking this `Com` back to the `LowCT`
emit at the byte-level is the job of
`CompressEmitDenoteCorrect.lean`, which proves the semantic correctness
of the `LowCT` against the algebraic spec.

## Encoding choice

We model each 40-byte field element as `CryptoTy.memref 5` (5×64-bit
limbs, matching fiat-crypto's packed Curve25519 layout). The 200-byte
XYZT bundle is `CryptoTy.memref 25` (= 5 elements × 5 limbs). The
32-byte output is `CryptoTy.memref 4` (4×64-bit limbs).

These widths are immaterial for the *optimizer wiring*: the optimizer
preserves denotation regardless of the exact widths used, and the
`extCall` ops are denotationally opaque (return the default value of
the result type — see `CatCryptDialect.lean`'s `catCryptDenote`).

The widths are also consistent with the existing `X25519Program.lean`
convention (`Fp25519 := CryptoTy.memref 5`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Ed25519.CompressCom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

/-! ## §1  Type aliases (mirrors `X25519Program.Fp25519`) -/

/-- A 40-byte (5×64-bit limb) field-element slot. -/
abbrev Fp25519Ty : CryptoTy := .memref 5

/-- The 200-byte XYZT input bundle (25×64-bit limbs = 5 field elements). -/
abbrev XYZTTy : CryptoTy := .memref 25

/-- The 32-byte compressed output (4×64-bit limbs). -/
abbrev CompressedTy : CryptoTy := .memref 4

/-! ## §2  Leaf builders -/

/-- `xyzt_slot_x` extracts the X coordinate slot from the XYZT bundle. -/
def xyztSlotXExpr {Γ : Ctxt catCryptDialect} (xyzt : Ctxt.Var Γ XYZTTy) :
    Expr catCryptDialect Γ Fp25519Ty :=
  { op := .extCall "xyzt_slot_x" [XYZTTy] Fp25519Ty
    retTy_eq := rfl
    args := .cons xyzt .nil }

/-- `xyzt_slot_y` extracts the Y coordinate. -/
def xyztSlotYExpr {Γ : Ctxt catCryptDialect} (xyzt : Ctxt.Var Γ XYZTTy) :
    Expr catCryptDialect Γ Fp25519Ty :=
  { op := .extCall "xyzt_slot_y" [XYZTTy] Fp25519Ty
    retTy_eq := rfl
    args := .cons xyzt .nil }

/-- `xyzt_slot_z` extracts the Z coordinate. -/
def xyztSlotZExpr {Γ : Ctxt catCryptDialect} (xyzt : Ctxt.Var Γ XYZTTy) :
    Expr catCryptDialect Γ Fp25519Ty :=
  { op := .extCall "xyzt_slot_z" [XYZTTy] Fp25519Ty
    retTy_eq := rfl
    args := .cons xyzt .nil }

/-- `fe25519_invert_slot` computes the multiplicative inverse Z⁻¹. -/
def fe25519InvertSlotExpr {Γ : Ctxt catCryptDialect}
    (z : Ctxt.Var Γ Fp25519Ty) : Expr catCryptDialect Γ Fp25519Ty :=
  { op := .extCall "fe25519_invert_slot" [Fp25519Ty] Fp25519Ty
    retTy_eq := rfl
    args := .cons z .nil }

/-- `fe25519_mul_slot` multiplies two 40-byte field elements. -/
def fe25519MulSlotExpr {Γ : Ctxt catCryptDialect}
    (a b : Ctxt.Var Γ Fp25519Ty) : Expr catCryptDialect Γ Fp25519Ty :=
  { op := .extCall "fe25519_mul_slot" [Fp25519Ty, Fp25519Ty] Fp25519Ty
    retTy_eq := rfl
    args := .cons a (.cons b .nil) }

/-- `fe25519_pack_sign` packs (Y_aff, X_aff) into 32 bytes with the sign bit. -/
def fe25519PackSignExpr {Γ : Ctxt catCryptDialect}
    (y x : Ctxt.Var Γ Fp25519Ty) : Expr catCryptDialect Γ CompressedTy :=
  { op := .extCall "fe25519_pack_sign" [Fp25519Ty, Fp25519Ty] CompressedTy
    retTy_eq := rfl
    args := .cons y (.cons x .nil) }

/-! ## §3  Compress as a `Com`

Context: a single 200-byte XYZT bundle.  Return: 32-byte compressed
output.

Mirrors the seven-leaf sequence in `CompressEmit.ed25519_compress_cmd`:
```
let x_slot = xyzt_slot_x(xyzt)
let y_slot = xyzt_slot_y(xyzt)
let z_slot = xyzt_slot_z(xyzt)
let z_inv  = fe25519_invert_slot(z_slot)
let y_aff  = fe25519_mul_slot(y_slot, z_inv)
let x_aff  = fe25519_mul_slot(x_slot, z_inv)
let out    = fe25519_pack_sign(y_aff, x_aff)
ret out
``` -/

/-- Context: just the XYZT input. -/
abbrev CompressCtx : Ctxt catCryptDialect := [XYZTTy]

/-- The compress program as `Com catCryptDialect CompressCtx CompressedTy`. -/
def compressCom : Com catCryptDialect CompressCtx CompressedTy :=
  -- .here = xyzt (200-byte input).
  let xyzt : Ctxt.Var CompressCtx XYZTTy := .here
  -- let x_slot = xyzt_slot_x(xyzt)
  .var (xyztSlotXExpr xyzt)
    -- Γ' = Fp25519Ty :: CompressCtx; x_slot at .here, xyzt at .there .here.
    (.var (xyztSlotYExpr (.there xyzt))
      -- y_slot at .here, x_slot at .there .here, xyzt at .there .there .here.
      (.var (xyztSlotZExpr (.there (.there xyzt)))
        -- z_slot at .here, y_slot at .there .here, x_slot at .there².here.
        (.var (fe25519InvertSlotExpr .here)
          -- z_inv at .here, z_slot at .there .here, y_slot at .there².here,
          -- x_slot at .there³.here.
          (.var (fe25519MulSlotExpr (.there (.there .here)) .here)
            -- After this var: Γ₅ has 5 entries (excl. XYZT at bottom).
            -- y_aff at .here, z_inv at .there .here, z_slot at .there².here,
            -- y_slot at .there³.here, x_slot at .there⁴.here.
            -- Compute x_aff = mul(x_slot, z_inv).
            (.var (fe25519MulSlotExpr
                    (.there (.there (.there (.there .here))))   -- x_slot
                    (.there .here))                              -- z_inv
              -- After this var: x_aff at .here, y_aff at .there .here.
              (.var (fe25519PackSignExpr (.there .here) .here)
                -- After this var: out at .here.
                (.ret .here)))))))

/-! ## §4  Optimizer wiring

`Optimizer.optimize` is denote-preserving; applying it to `compressCom`
gives a denotation-equivalent `Com`. The peephole pass currently only
rewrites self-`bvXor`/`bvSub`, neither of which appears in
`compressCom`, so the optimizer is a no-op here — but the wiring is
ready for future passes that *do* fire on this kind of `extCall`-heavy
program. -/

/-- The compress program after one pass of the optimizer. -/
def optimizedCompressCom : Com catCryptDialect CompressCtx CompressedTy :=
  Optimizer.optimize compressCom

/-- **Optimizer correctness for compress** (the deliverable promised in
    `Optimizer.lean`'s "Compress emission wiring" docstring): the
    optimized compress denotes to exactly the same thing as the
    unoptimized version.  An immediate corollary of the generic
    `Optimizer.optimize_denote_eq`. -/
theorem optimizedCompressCom_denote_eq (V : Ctxt.Valuation CompressCtx) :
    optimizedCompressCom.denote V = compressCom.denote V := by
  exact Optimizer.optimize_denote_eq compressCom V

/-! ## §5  Smoke tests

Concrete checks at a default valuation: both the unoptimized and
optimized programs return the same `CompressedTy` value. The
`extCall` denotation is opaque (returns `CryptoTy.default`), so the
concrete value at the default valuation is the all-zeros memref. -/

/-- A default valuation: the XYZT input is the all-zeros memref. -/
def defaultValuation : Ctxt.Valuation CompressCtx :=
  HVector.cons (default : (CryptoTy.denote XYZTTy)) HVector.nil

/-- Concrete smoke test: at the default XYZT input, the optimized
    compress matches the unoptimized compress. -/
example : optimizedCompressCom.denote defaultValuation =
          compressCom.denote defaultValuation :=
  optimizedCompressCom_denote_eq _

end CatCrypt.Crypto.Jasmin.Ed25519.CompressCom
