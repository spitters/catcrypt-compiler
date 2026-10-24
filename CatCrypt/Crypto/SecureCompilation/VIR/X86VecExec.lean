/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach

/-!
# The vector operations of `x86vec` on the vector machine

Each operation of `x86vec` that has a register form in `VecMach.VInstr` is executed by one
instruction: when the source registers of the instruction hold the operands of the
operation, widened to 512 bits, `VecMach.vexec` writes the value of the operation to the
destination register. A masked instruction reads its mask register, and the operation
carries the value of that register; `vpternlog` and the masked duplicate read the
destination, which holds an operand.

The operations `cst` and `bcst` (constant loads from the data table) and `sra` have no
constructor in `VInstr`.

## Main results

* `vexec_lw`, `vexec_shi`, `vexec_dup`, `vexec_dupMerge`, `vexec_mova`, `vexec_perm`,
  `vexec_blend`, `vexec_rol`, `vexec_tern` — one instruction executes one operation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.X86VecExec

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode LOp wr semLW semShImm semDup
  semMerge semPerm semRol semTern)
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach (VState VInstr vexec)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-- The register written by `setZ` holds the written value. -/
theorem setZ_zmm_self (v : VState) (d : Fin 32) (x : BitVec 512) : (v.setZ d x).zmm d = x :=
  ite_eq_left rfl

variable (m : Mode) (s : AState × VState)

/-- **`VInstr.op` executes `X86VecOp.lw`.** With the source registers holding the operands,
    the destination holds the value of the operation. -/
theorem vexec_lw (L : Nat) (o : LOp) (s2 s1 d : Fin 32) (a b : BitVec m.act)
    (h1 : s.2.zmm s1 = up m a) (h2 : s.2.zmm s2 = up m b) :
    (vexec m s (.op L o s2 s1 d)).2.zmm d =
      up m (DialectDenote.denote (d := x86vec) (.lw m L o) (.cons a (.cons b .nil))) := by
  have e : up m (DialectDenote.denote (d := x86vec) (.lw m L o) (.cons a (.cons b .nil))) =
      wr m (semLW L o (s.2.zmm s1) (s.2.zmm s2)) := by
    rw [h1, h2]
    exact up_dn m _
  exact (setZ_zmm_self _ _ _).trans e.symm

/-- **`VInstr.shi` executes `X86VecOp.shi`.** -/
theorem vexec_shi (L : Nat) (left : Bool) (imm : Nat) (r d : Fin 32) (a : BitVec m.act)
    (h1 : s.2.zmm r = up m a) :
    (vexec m s (.shi L left imm r d)).2.zmm d =
      up m (DialectDenote.denote (d := x86vec) (.shi m L left imm) (.cons a .nil)) := by
  have e : up m (DialectDenote.denote (d := x86vec) (.shi m L left imm) (.cons a .nil)) =
      wr m (semShImm L left imm (s.2.zmm r)) := by
    rw [h1]
    exact up_dn m _
  exact (setZ_zmm_self _ _ _).trans e.symm

/-- **`VInstr.dup` without a mask executes `X86VecOp.dup`.** -/
theorem vexec_dup (odd : Bool) (r d : Fin 32) (a : BitVec m.act) (h1 : s.2.zmm r = up m a) :
    (vexec m s (.dup odd r d none)).2.zmm d =
      up m (DialectDenote.denote (d := x86vec) (.dup m odd) (.cons a .nil)) := by
  have e : up m (DialectDenote.denote (d := x86vec) (.dup m odd) (.cons a .nil)) =
      wr m (semDup odd (s.2.zmm r)) := by
    rw [h1]
    exact up_dn m _
  exact (setZ_zmm_self _ _ _).trans e.symm

/-- **`VInstr.dup` under a mask register executes `X86VecOp.dupMerge`** at the value of the
    mask register, with the destination holding the second operand. -/
theorem vexec_dupMerge (odd : Bool) (r d : Fin 32) (k : Fin 8) (a old : BitVec m.act)
    (h1 : s.2.zmm r = up m a) (hd : s.2.zmm d = up m old) :
    (vexec m s (.dup odd r d (some k))).2.zmm d =
      up m (DialectDenote.denote (d := x86vec) (.dupMerge m odd (s.2.kr k))
        (.cons a (.cons old .nil))) := by
  have e : up m (DialectDenote.denote (d := x86vec) (.dupMerge m odd (s.2.kr k))
        (.cons a (.cons old .nil))) =
      wr m (semMerge (s.2.kr k) (semDup odd (s.2.zmm r)) (s.2.zmm d)) := by
    rw [h1, hd]
    exact up_dn m _
  exact (setZ_zmm_self _ _ _).trans e.symm

/-- **`VInstr.mova` executes `X86VecOp.mova`.** -/
theorem vexec_mova (r d : Fin 32) (a : BitVec m.act) (h1 : s.2.zmm r = up m a) :
    (vexec m s (.mova r d)).2.zmm d =
      up m (DialectDenote.denote (d := x86vec) (.mova m) (.cons a .nil)) := by
  have e : up m (DialectDenote.denote (d := x86vec) (.mova m) (.cons a .nil)) =
      wr m (s.2.zmm r) := by
    rw [h1]
    exact up_dn m _
  exact (setZ_zmm_self _ _ _).trans e.symm

/-- **`VInstr.perm` executes `X86VecOp.perm`.** -/
theorem vexec_perm (x i d : Fin 32) (a b : BitVec m.act)
    (h1 : s.2.zmm x = up m a) (h2 : s.2.zmm i = up m b) :
    (vexec m s (.perm x i d)).2.zmm d =
      up m (DialectDenote.denote (d := x86vec) (.perm m) (.cons a (.cons b .nil))) := by
  have e : up m (DialectDenote.denote (d := x86vec) (.perm m) (.cons a (.cons b .nil))) =
      wr m (semPerm (m.act / 32) (s.2.zmm x) (s.2.zmm i)) := by
    rw [h1, h2]
    exact up_dn m _
  exact (setZ_zmm_self _ _ _).trans e.symm

/-- **`VInstr.blend` executes `X86VecOp.blend`** at the value of the mask register. -/
theorem vexec_blend (k : Fin 8) (x y d : Fin 32) (a b : BitVec m.act)
    (h1 : s.2.zmm x = up m a) (h2 : s.2.zmm y = up m b) :
    (vexec m s (.blend k x y d)).2.zmm d =
      up m (DialectDenote.denote (d := x86vec) (.blend m (s.2.kr k))
        (.cons a (.cons b .nil))) := by
  have e : up m (DialectDenote.denote (d := x86vec) (.blend m (s.2.kr k))
        (.cons a (.cons b .nil))) = wr m (semMerge (s.2.kr k) (s.2.zmm x) (s.2.zmm y)) := by
    rw [h1, h2]
    exact up_dn m _
  exact (setZ_zmm_self _ _ _).trans e.symm

/-- **`VInstr.rol` executes `X86VecOp.rol`.** -/
theorem vexec_rol (L imm : Nat) (r d : Fin 32) (a : BitVec m.act) (h1 : s.2.zmm r = up m a) :
    (vexec m s (.rol L imm r d)).2.zmm d =
      up m (DialectDenote.denote (d := x86vec) (.rol m L imm) (.cons a .nil)) := by
  have e : up m (DialectDenote.denote (d := x86vec) (.rol m L imm) (.cons a .nil)) =
      wr m (semRol L imm (s.2.zmm r)) := by
    rw [h1]
    exact up_dn m _
  exact (setZ_zmm_self _ _ _).trans e.symm

/-- **`VInstr.tern` executes `X86VecOp.tern`**, with the destination holding the first
    operand. -/
theorem vexec_tern (L : Nat) (imm : BitVec 8) (s3 s2 d : Fin 32) (a b c : BitVec m.act)
    (hd : s.2.zmm d = up m a) (h2 : s.2.zmm s2 = up m b) (h3 : s.2.zmm s3 = up m c) :
    (vexec m s (.tern L imm s3 s2 d)).2.zmm d =
      up m (DialectDenote.denote (d := x86vec) (.tern m L imm)
        (.cons a (.cons b (.cons c .nil)))) := by
  have e : up m (DialectDenote.denote (d := x86vec) (.tern m L imm)
        (.cons a (.cons b (.cons c .nil)))) =
      wr m (semTern imm (s.2.zmm d) (s.2.zmm s2) (s.2.zmm s3)) := by
    rw [hd, h2, h3]
    exact up_dn m _
  exact (setZ_zmm_self _ _ _).trans e.symm

end CatCrypt.Crypto.SecureCompilation.VIR.X86VecExec
