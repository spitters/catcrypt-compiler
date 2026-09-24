/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC

@[expose] public section

set_option autoImplicit false

/-!
# The lowered full-`arith` `Com` is in the `ScalarMulCarryN` fragment

`ArithExportFaithful` covers the *scalar* `arith` fragment (the ALU + materialised
constant ops that lower to `regArith`/`regConst`), landing in `UniformScalarArith`.
This module lifts the whole `arith` op set — adding the widening-high multiply
`mului_extended_hi` (↦ `mulhi`) and the immediate shifts `shrui_imm`/`shli_imm`
(↦ `shrImm`/`shlImm`) — into the mul/carry fragment `ScalarMulCarryN`. Composed with
`JasminLsemGeneralFaithfulMC.comLsemExportFaithfulMC_of_mulcarry`, this gives the
`lsem` export faithfulness `ComLsemExportFaithfulMC` for *every* `arith`-lowered
program at a uniform width, not just the scalar sub-fragment.

The `FullArithW` predicate carries the two side conditions the mul/carry constructors
need on top of the head shape: the immediate shift counts are in range (`n < 2 ^ w`,
required by `ScalarMulCarryN.shr`/`shl`) and a materialised constant's width is on the
two wire-distinguished widths (`w = 64 ∨ w = 32`, required by `ScalarMulCarryN.const`
— the only width information a nullary `regConst` carries on the wire). Both hold for
the residence-renamed bodies the linearizer emits (`w ∈ {32, 64}`; shift counts
`< w ≤ 2 ^ w`).
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ArithFullExportFaithful

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Dialects.Arith
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithfulMC

/-- A full-`arith` program at uniform width `w`: every binding is one of the `arith`
    ops whose `toJasmin` image is a `regArith`/`regConst`/`mulhi`/`shrImm`/`shlImm`
    head at the uniform width `w`. The immediate-shift bindings carry the in-range
    side condition `n < 2 ^ w`; the materialised-constant bindings carry the
    wire-width side condition `w = 64 ∨ w = 32`. This subsumes
    `ArithExportFaithful.ScalarArithW` (the `regArith`/`regConst`-only sub-fragment),
    adding the widening-high multiply and the immediate shifts. -/
inductive FullArithW (w : Nat) : {Γ : Ctxt arithDialect} →
    Com arithDialect Γ (.int w) → Prop where
  | ret {Γ : Ctxt arithDialect} (v : Ctxt.Var Γ (.int w)) : FullArithW w (.ret v)
  | alu {Γ : Ctxt arithDialect}
      (e : Expr arithDialect Γ (.int w))
      (hsc : e.op = .addi w ∨ e.op = .subi w ∨ e.op = .muli w ∨
             e.op = .andi w ∨ e.op = .ori w ∨ e.op = .xori w)
      {body : Com arithDialect (.int w :: Γ) (.int w)} (hbody : FullArithW w body) :
      FullArithW w (.var e body)
  | const {Γ : Ctxt arithDialect} (n : Nat) (hwn : w = 64 ∨ w = 32)
      (e : Expr arithDialect Γ (.int w)) (hop : e.op = .constant w n)
      {body : Com arithDialect (.int w :: Γ) (.int w)} (hbody : FullArithW w body) :
      FullArithW w (.var e body)
  | mulhi {Γ : Ctxt arithDialect}
      (e : Expr arithDialect Γ (.int w)) (hop : e.op = .mului_extended_hi w)
      {body : Com arithDialect (.int w :: Γ) (.int w)} (hbody : FullArithW w body) :
      FullArithW w (.var e body)
  | shr {Γ : Ctxt arithDialect} (n : Nat) (hn : n < 2 ^ w)
      (e : Expr arithDialect Γ (.int w)) (hop : e.op = .shrui_imm w n)
      {body : Com arithDialect (.int w :: Γ) (.int w)} (hbody : FullArithW w body) :
      FullArithW w (.var e body)
  | shl {Γ : Ctxt arithDialect} (n : Nat) (hn : n < 2 ^ w)
      (e : Expr arithDialect Γ (.int w)) (hop : e.op = .shli_imm w n)
      {body : Com arithDialect (.int w :: Γ) (.int w)} (hbody : FullArithW w body) :
      FullArithW w (.var e body)

/-- **The lowered full-`arith` `Com` is `ScalarMulCarryN`.** Each binding's `toJasmin`
    image is a `regArith`/`regConst`/`mulhi`/`shrImm`/`shlImm` head at the uniform
    width `w`, in the mul/carry fragment. -/
theorem lowerArithToJasmin_fullArith {w : Nat} {Γ : Ctxt arithDialect}
    {com : Com arithDialect Γ (.int w)} (h : FullArithW w com) :
    ScalarMulCarryN (lowerArithToJasmin com) := by
  induction h with
  | ret v => exact ScalarMulCarryN.ret (mapVar v)
  | alu e hsc hbody ih =>
      obtain ⟨op, hret, args⟩ := e
      rcases hsc with h | h | h | h | h | h <;>
        (subst h; cases hret)
      · exact ScalarMulCarryN.var .add _ _ ih
      · exact ScalarMulCarryN.var .sub _ _ ih
      · exact ScalarMulCarryN.var .mul _ _ ih
      · exact ScalarMulCarryN.var .and _ _ ih
      · exact ScalarMulCarryN.var .or _ _ ih
      · exact ScalarMulCarryN.var .xor _ _ ih
  | const n hwn e hop hbody ih =>
      obtain ⟨op, hret, args⟩ := e
      subst hop; cases hret
      exact ScalarMulCarryN.const n hwn _ _ ih
  | mulhi e hop hbody ih =>
      obtain ⟨op, hret, args⟩ := e
      subst hop; cases hret
      exact ScalarMulCarryN.mulhi _ _ ih
  | shr n hn e hop hbody ih =>
      obtain ⟨op, hret, args⟩ := e
      subst hop; cases hret
      exact ScalarMulCarryN.shr hn _ _ ih
  | shl n hn e hop hbody ih =>
      obtain ⟨op, hret, args⟩ := e
      subst hop; cases hret
      exact ScalarMulCarryN.shl hn _ _ ih

/-- **`lsem` export faithfulness for a full-`arith` program.** The
    `toJasmin`-lowered full-`arith` `Com` (ALU + materialised constant + widening-high
    multiply + immediate shifts, at a uniform width `w`) satisfies
    `ComLsemExportFaithfulMC`: its emitted singleton program, run under the labeled
    program-indexed `lsem` from the encoded inputs, decodes to `Com.denote` for every
    valuation. This is the real (non-`True`) content of the export gate for the *whole*
    `arith` fragment, discharged via `comLsemExportFaithfulMC_of_mulcarry` and the
    lowering witness — extending `ArithExportFaithful.arith_scalar_export_faithful`
    from the `regArith`/`regConst` scalar sub-fragment to `mulhi`/`shrImm`/`shlImm`. -/
theorem arith_full_export_faithful {w : Nat} {Γ : Ctxt arithDialect}
    {com : Com arithDialect Γ (.int w)} (h : FullArithW w com) (fn : String) :
    ComLsemExportFaithfulMC (lowerArithToJasmin com) fn (rfl : ArithTy.toJasmin (.int w) = .reg w) :=
  comLsemExportFaithfulMC_of_mulcarry (lowerArithToJasmin_fullArith h) rfl fn

end CatCrypt.Crypto.SecureCompilation.Dialects.ArithFullExportFaithful
