/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasmin
import CatCrypt.Crypto.SecureCompilation.Dialects.ArithLegality

set_option autoImplicit false

/-!
# `lowerArithToJasmin` preserves `ComOK` (so lifted `arith` kernels emit)

The denotational half of the arith→jasmin lowering is `lowerArithToJasmin_denote`
(unconditional). This file closes the *emit-legality* half: a width-64 `arith`
`Com` lowers to a jasmin `Com` in the `ComOK` straight-line fragment, so the lifted
kernel rides the existing golden-path emit (`com_arm_e2e` / `com_riscv_e2e`).

`ArithOK64` is the arith-side legality predicate (every op width 64, result `i64`);
`lowerArithToJasmin_ComOK` discharges `ComOK` of the image by `arith_toJasmin_supported`
(itself built on the `SupportedOp` smart constructors). With the denote lemma, this
is the full arith-source → backend connection: write once at the neutral level,
emit through the proven lowering.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Arith

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn (SupportedOp ComOK)

/-- The arith-side legality predicate the front consumes: a straight-line `i64`
    `Com` whose every bound op is width 64 (the exact preimage of `ComOK` under
    `lowerArithToJasmin`). -/
inductive ArithOK64 : {Γ : Ctxt arithDialect} → Com arithDialect Γ (.int 64) → Prop where
  | ret {Γ : Ctxt arithDialect} (v : Ctxt.Var Γ (.int 64)) : ArithOK64 (.ret v)
  | var {Γ : Ctxt arithDialect} {e : Expr arithDialect Γ (.int 64)}
      {body : Com arithDialect ((.int 64) :: Γ) (.int 64)}
      (hw : e.op.width = 64) (hbody : ArithOK64 body) : ArithOK64 (.var e body)

/-- **Emit-legality preservation.** A width-64 `arith` `Com` lowers into the
    supported jasmin straight-line fragment, so the image is `ComOK` and rides
    `com_arm_e2e` / `com_riscv_e2e`. -/
theorem lowerArithToJasmin_ComOK {Γ : Ctxt arithDialect} {com : Com arithDialect Γ (.int 64)}
    (h : ArithOK64 com) : ComOK (lowerArithToJasmin com) := by
  induction h with
  | ret v => exact ComOK.ret _
  | var hw _ ih => exact ComOK.var (arith_toJasmin_supported _ hw) ih

end CatCrypt.Crypto.SecureCompilation.Dialects.Arith
