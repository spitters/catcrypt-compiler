/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

set_option autoImplicit false

/-!
# `lsem`-faithful export of a golden-path kernel

`comToLprog_faithful_straightline` is the faithfulness theorem on the uniform-`regArith`
straight-line fragment: a `Com`'s linearizer-emitted body, run under `lsem` from the
encoded inputs and decoded at the result register, equals `Com.denote`. This file
instantiates it at the field-add core `fieldAddCom` (`fieldAddCom_lsem_faithful`).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.GoldenPathLsemFaithful

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath

/-- `fieldAddCom` is in the uniform-`regArith` straight-line fragment (a single `add`). -/
theorem fieldAddCom_uniform : UniformRegArith 64 fieldAddCom :=
  UniformRegArith.var .add rfl (.cons (.there .here) (.cons .here .nil))
    (UniformRegArith.ret .here)

/-- The two-input context `[reg 64, reg 64]` is uniform-width 64 (the empty context
    extended by `UniformCtxt.cons` twice). -/
theorem ctxt_uniform : UniformCtxt 64 ([.reg 64, .reg 64] : Ctxt jasminDialect) :=
  UniformCtxt.cons (UniformCtxt.cons (by intro τ v; cases v))

/-- `fieldAddCom`'s linearizer-emitted straight-line body, run under `lsem` from the
    encoded inputs and decoded at the result register, equals `fieldAddCom.denote` for
    every valuation. -/
theorem fieldAddCom_lsem_faithful
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect)) :
    (lsemStraight (straightOps 2 fieldAddCom 2) (encode V)).map
        (fun st' => decode st' (comRetReg 2 argName fieldAddCom 2))
      = some (fieldAddCom_uniform.ret_ty ▸ fieldAddCom.denote V : ⟦(JasminTy.reg 64)⟧) :=
  comToLprog_faithful_straightline fieldAddCom_uniform ctxt_uniform V

/-- `fieldMulLoCom` is in the uniform-`regArith` straight-line fragment (a single `mul`). -/
theorem fieldMulLoCom_uniform : UniformRegArith 64 fieldMulLoCom :=
  UniformRegArith.var .mul rfl (.cons (.there .here) (.cons .here .nil))
    (UniformRegArith.ret .here)

/-- `fieldMulLoCom`'s linearizer-emitted straight-line body, run under `lsem` from the
    encoded inputs and decoded at the result register, equals `fieldMulLoCom.denote` for
    every valuation. -/
theorem fieldMulLoCom_lsem_faithful
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect)) :
    (lsemStraight (straightOps 2 fieldMulLoCom 2) (encode V)).map
        (fun st' => decode st' (comRetReg 2 argName fieldMulLoCom 2))
      = some (fieldMulLoCom_uniform.ret_ty ▸ fieldMulLoCom.denote V : ⟦(JasminTy.reg 64)⟧) :=
  comToLprog_faithful_straightline fieldMulLoCom_uniform ctxt_uniform V

/-- The three-input context `[reg 64, reg 64, reg 64]` is uniform-width 64. -/
theorem ctxt_uniform3 : UniformCtxt 64 ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect) :=
  UniformCtxt.cons (UniformCtxt.cons (UniformCtxt.cons (by intro τ v; cases v)))

/-- `fieldAdcCom` is in the uniform-`regArith` straight-line fragment (two `add`s:
    `t := a + b`, `r := t + cin`). -/
theorem fieldAdcCom_uniform : UniformRegArith 64 fieldAdcCom :=
  UniformRegArith.var .add rfl (.cons .here (.cons (.there .here) .nil))
    (UniformRegArith.var .add rfl
      (.cons .here (.cons (.there (.there (.there .here))) .nil))
      (UniformRegArith.ret .here))

/-- `fieldAdcCom`'s linearizer-emitted straight-line body, run under `lsem` from the
    encoded inputs and decoded at the result register, equals `fieldAdcCom.denote` for
    every valuation. -/
theorem fieldAdcCom_lsem_faithful
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64] : Ctxt jasminDialect)) :
    (lsemStraight (straightOps 3 fieldAdcCom 3) (encode V)).map
        (fun st' => decode st' (comRetReg 3 argName fieldAdcCom 3))
      = some (fieldAdcCom_uniform.ret_ty ▸ fieldAdcCom.denote V : ⟦(JasminTy.reg 64)⟧) :=
  comToLprog_faithful_straightline fieldAdcCom_uniform ctxt_uniform3 V

/-- `fieldMulHiCom` is in the mul/carry straight-line fragment (a single `mulhi`, the one
    field ALU kernel outside the `regArith`-only fragment). -/
theorem fieldMulHiCom_mc : ScalarMulCarryN fieldMulHiCom :=
  ScalarMulCarryN.mulhi rfl (.cons (.there .here) (.cons .here .nil))
    (ScalarMulCarryN.ret .here)

/-- `fieldMulHiCom`'s linearizer-emitted body, run under the mul/carry `lsem` from the
    encoded inputs and decoded at the result register, equals `fieldMulHiCom.denote` for
    every valuation. -/
theorem fieldMulHiCom_lsem_faithful
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect)) :
    (lsemStraightMC (straightOpsMC 2 fieldMulHiCom 2) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg 2 argName fieldMulHiCom 2) 64)
      = some ((rfl : (JasminTy.reg 64) = .reg 64) ▸ fieldMulHiCom.denote V
          : ⟦(JasminTy.reg 64)⟧) :=
  comToLprog_faithful_mulcarry fieldMulHiCom_mc rfl V

end CatCrypt.Crypto.SecureCompilation.VIR.GoldenPathLsemFaithful
