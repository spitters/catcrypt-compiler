/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyContext

/-!
# Lowering of lattice contexts commutes with linking

`RobustSafetyContext.lowerCtx` lowers a lattice context (a `Com` with a hole) to a
Jasmin context in lockstep with `lowerLatticeToJasmin`. This module proves that
the context-level lowering commutes with linking, and records that every binding
the lowering emits is an `extCall`.

## Main results

* `plug_lowerCtx` — plugging the lowered context with the lowered program equals
  lowering the plugged source program.
* `ctSafeJasmin_plug_lowerCtx` — consequently the label checker `ctSafeJasmin`
  returns the same value on both sides.
* `lowerExpr_op_is_extCall` — every binding emitted by `lowerExpr` is an
  `extCall`, so the image of `lowerCtx` contains no `stackLoad` / `stackStore`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyBackTranslate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyContext

/-- **Commutation of lowering with linking.** Plugging the lowered context
    `lowerCtx C` with the lowered program `lowerLatticeToJasmin p` equals the
    lowering of the plugged source program `lowerLatticeToJasmin (plug C p)`.
    Proved by induction on the lattice context `C`. -/
theorem plug_lowerCtx {Γh : Ctxt latticeDialect} {th : LatticeTy} :
    {Γ : Ctxt latticeDialect} →
    (C : ComCtx latticeDialect Γh th Γ) → (p : Com latticeDialect Γh th) →
    ComCtx.plug (lowerCtx C) (lowerLatticeToJasmin p)
      = lowerLatticeToJasmin (ComCtx.plug C p)
  | _, .hole, _ => by simp only [lowerCtx, ComCtx.plug_hole]
  | _, .var e C, p => by
      simp only [lowerCtx, ComCtx.plug, lowerLatticeToJasmin, plug_lowerCtx C p]

/-- For a context in the image of `lowerCtx`, the label checker returns the same
    value on the linked target program and on the lowered linked source program,
    under any labelling. Immediate from `plug_lowerCtx`. -/
theorem ctSafeJasmin_plug_lowerCtx
    {Γ : Ctxt latticeDialect} {t : LatticeTy} {Δ₀ : Ctxt latticeDialect}
    (C₀ : ComCtx latticeDialect Γ t Δ₀) (c : Com latticeDialect Γ t)
    (L : LabelCtxt (Δ₀.map tau)) :
    ctSafeJasmin (ComCtx.plug (lowerCtx C₀) (lowerLatticeToJasmin c)) L
      = ctSafeJasmin (lowerLatticeToJasmin (ComCtx.plug C₀ c)) L := by
  rw [plug_lowerCtx C₀ c]

/-- Every binding emitted by `lowerExpr` is an `extCall`, hence never a
    `stackLoad`/`stackStore`; the image of `lowerCtx` therefore excludes
    contexts such as `RobustSafetyContext.hostileCtx`. -/
theorem lowerExpr_op_is_extCall {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (e : Expr latticeDialect Γ t) :
    ∃ name argTys retTy,
      (lowerExpr e).op = JasminOp.extCall name argTys retTy :=
  jasminOpOf_is_extCall e.op

end CatCrypt.Crypto.SecureCompilation.VIR.RobustSafetyBackTranslate
