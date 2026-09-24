/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful

@[expose] public section

set_option autoImplicit false

/-!
# The lowered scalar `arith` `Com` is in the `UniformScalarArith` fragment

For the scalar `arith` fragment at a fixed width `w` (ops that lower to `regArith`/
`regConst` — `addi`/`subi`/`muli`/`andi`/`ori`/`xori`/`constant`, excluding
`mului_extended_hi` and the immediate shifts, which lower to the `LstateN` N-state ops),
the `toJasmin` lowering lands in `UniformScalarArith w`. Composed with
`JasminLsemGeneralFaithful.comLsemExportFaithful_of_scalar`, this gives the
`lsem` export faithfulness `ComLsemExportFaithful` for scalar-`arith`-lowered programs —
the real (non-`True`) content of the export gate for that fragment.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithExportFaithful

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Dialects.Arith
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful

/-- The scalar `arith` ops — `toJasmin` image `regArith`/`regConst`. -/
def isScalarOp : ArithOp → Bool
  | .addi _ | .subi _ | .muli _ | .andi _ | .ori _ | .xori _ | .constant _ _ => true
  | .mului_extended_hi _ | .shrui_imm _ _ | .shli_imm _ _ => false

/-- A scalar-only `arith` program at uniform width `w`: every binding is an `isScalarOp`
    at result `.int w` (matching `UniformScalarArith`'s single-width discipline). -/
inductive ScalarArithW (w : Nat) : {Γ : Ctxt arithDialect} →
    Com arithDialect Γ (.int w) → Prop where
  | ret {Γ : Ctxt arithDialect} (v : Ctxt.Var Γ (.int w)) : ScalarArithW w (.ret v)
  | var {Γ : Ctxt arithDialect} (e : Expr arithDialect Γ (.int w)) (hsc : isScalarOp e.op)
      {body : Com arithDialect (.int w :: Γ) (.int w)} (hbody : ScalarArithW w body) :
      ScalarArithW w (.var e body)

/-- **The lowered scalar-`arith` `Com` is `UniformScalarArith`.** Each scalar op's
    `toJasmin` image is a `regArith`/`regConst` head at the uniform width `w`. -/
theorem lowerArithToJasmin_uniformScalar {w : Nat} {Γ : Ctxt arithDialect}
    {com : Com arithDialect Γ (.int w)} (h : ScalarArithW w com) :
    UniformScalarArith w (lowerArithToJasmin com) := by
  induction h with
  | ret v => exact UniformScalarArith.ret (mapVar v)
  | var e hsc hbody ih =>
      obtain ⟨op, hret, args⟩ := e
      cases op with
      | addi w' => cases hret; exact UniformScalarArith.var .add _ _ ih
      | subi w' => cases hret; exact UniformScalarArith.var .sub _ _ ih
      | muli w' => cases hret; exact UniformScalarArith.var .mul _ _ ih
      | andi w' => cases hret; exact UniformScalarArith.var .and _ _ ih
      | ori w' => cases hret; exact UniformScalarArith.var .or _ _ ih
      | xori w' => cases hret; exact UniformScalarArith.var .xor _ _ ih
      | constant w' n => cases hret; exact UniformScalarArith.const n _ _ ih
      | mului_extended_hi w' => simp [isScalarOp] at hsc
      | shrui_imm w' n => simp [isScalarOp] at hsc
      | shli_imm w' n => simp [isScalarOp] at hsc

/-- **`lsem` export faithfulness for a scalar-`arith` program.** With the lowered
    argument context uniform-width `w`, the `toJasmin`-lowered scalar-`arith` `Com`
    satisfies `ComLsemExportFaithful`: its emitted singleton program, run under the labeled
    program-indexed `lsem` from the encoded inputs, decodes to `Com.denote` for every
    valuation. This is the real (non-`True`) content of the export gate
    `JasminLprogExport.LprogExportFaithful` for the scalar-`arith` fragment, discharged via
    `comLsemExportFaithful_of_scalar` and the lowering witness. -/
theorem arith_scalar_export_faithful {w : Nat} {Γ : Ctxt arithDialect}
    {com : Com arithDialect Γ (.int w)} (h : ScalarArithW w com)
    (hu : UniformCtxt w (Γ.map ArithTy.toJasmin)) (fn : String) :
    ComLsemExportFaithful (lowerArithToJasmin com) fn
        (lowerArithToJasmin_uniformScalar h).ret_ty :=
  comLsemExportFaithful_of_scalar (lowerArithToJasmin_uniformScalar h) hu fn

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithExportFaithful
