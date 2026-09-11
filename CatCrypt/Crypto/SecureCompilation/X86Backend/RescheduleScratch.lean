/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrRegMachine
public import CatCrypt.Crypto.Optimizer.SpillingRegAlloc


@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RescheduleScratch

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc

theorem JState.ext {w : Nat} {s t : JState w}
    (hr : s.regs = t.regs) (hf : s.flags = t.flags) (hm : s.mem = t.mem) : s = t := by
  cases s; cases t; simp_all

theorem eval_setReg_notMem (s : JState 64) (src : JOperand)
    (r : String) (v : BitVec 64) (h : ¬ r ∈ AsmPrinter.srcNames src) :
    src.eval (s.setReg r v) = src.eval s := by
  cases src with
  | reg rr =>
    simp only [JOperand.eval, JState.get, JState.setReg]
    simp only [AsmPrinter.srcNames, List.mem_singleton] at h
    simp [Ne.symm h]
  | imm _ => rfl

-- The mulx × adcx arm in isolation, with abstract products.
example (s : JState 64) (dh1 dl1 : String) (a1 b1 : JOperand) (dst2 : String) (src2 : JOperand)
    (h11 : dh1 ≠ dst2) (h21 : dl1 ≠ dst2)
    (ha1_dst2 : ¬ dst2 ∈ AsmPrinter.srcNames a1)
    (hb1_dst2 : ¬ dst2 ∈ AsmPrinter.srcNames b1)
    (hsrc2_dh1 : ¬ dh1 ∈ AsmPrinter.srcNames src2)
    (hsrc2_dl1 : ¬ dl1 ∈ AsmPrinter.srcNames src2) :
    evalInstr (evalInstr s (.mulx dh1 dl1 a1 b1)) (.adcx dst2 src2)
      = evalInstr (evalInstr s (.adcx dst2 src2)) (.mulx dh1 dl1 a1 b1) := by
  -- s1 := mulx step; s2 := adcx step.  Keep both products ABSTRACT.
  -- LHS adcx args evaluated in s1 collapse to s; RHS mulx args in s2 collapse to s.
  simp only [evalInstr]
  -- Operand-eval helper specialized: eval in the adcx-record state = eval in s,
  -- for operands not reading dst2.
  have heval_a1 : ∀ co res, JOperand.eval
      { regs := fun r' => if r' = dst2 then res else s.regs r',
        flags := { cf := co, pf := s.flags.pf, zf := s.flags.zf,
                   sf := s.flags.sf, of := s.flags.of }, mem := s.mem } a1
      = JOperand.eval s a1 := by
    intro co res
    cases a1 with
    | reg rr =>
      simp only [JOperand.eval, JState.get]
      simp only [AsmPrinter.srcNames, List.mem_singleton] at ha1_dst2
      simp [Ne.symm ha1_dst2]
    | imm _ => rfl
  have heval_b1 : ∀ co res, JOperand.eval
      { regs := fun r' => if r' = dst2 then res else s.regs r',
        flags := { cf := co, pf := s.flags.pf, zf := s.flags.zf,
                   sf := s.flags.sf, of := s.flags.of }, mem := s.mem } b1
      = JOperand.eval s b1 := by
    intro co res
    cases b1 with
    | reg rr =>
      simp only [JOperand.eval, JState.get]
      simp only [AsmPrinter.srcNames, List.mem_singleton] at hb1_dst2
      simp [Ne.symm hb1_dst2]
    | imm _ => rfl
  -- LHS adcx args: get dst2 / flagB cf / eval src2 in s1 collapse to s.
  have hget_dst2 : ((s.setReg dl1 (x86_MULX_lo_hi (JOperand.eval s a1) (JOperand.eval s b1)).fst).setReg dh1
        (x86_MULX_lo_hi (JOperand.eval s a1) (JOperand.eval s b1)).snd).get dst2 = s.get dst2 := by
    simp [JState.get, JState.setReg, Ne.symm h11, Ne.symm h21]
  have hflagcf : ((s.setReg dl1 (x86_MULX_lo_hi (JOperand.eval s a1) (JOperand.eval s b1)).fst).setReg dh1
        (x86_MULX_lo_hi (JOperand.eval s a1) (JOperand.eval s b1)).snd).flagB (fun x => x.cf)
      = s.flagB (fun x => x.cf) := by
    simp [JState.flagB, JState.setReg]
  have hsrc2 : JOperand.eval
      ((s.setReg dl1 (x86_MULX_lo_hi (JOperand.eval s a1) (JOperand.eval s b1)).fst).setReg dh1
        (x86_MULX_lo_hi (JOperand.eval s a1) (JOperand.eval s b1)).snd) src2 = JOperand.eval s src2 :=
    (eval_setReg_notMem _ src2 dh1 _ hsrc2_dh1).trans (eval_setReg_notMem _ src2 dl1 _ hsrc2_dl1)
  rw [hget_dst2, hflagcf, hsrc2, heval_a1, heval_b1]
  -- Now both products are the SAME abstract terms; finish by register/flag bookkeeping.
  apply JState.ext
  · funext r
    by_cases hr_dh1 : r = dh1 <;> by_cases hr_dl1 : r = dl1 <;> by_cases hr_dst2 : r = dst2 <;>
      simp_all [JState.setReg, JState.get, Ne.symm]
  · simp [JState.setReg]
  · simp [JState.setReg]

-- The mulx × adox arm: adox reads/writes OF.
example (s : JState 64) (dh1 dl1 : String) (a1 b1 : JOperand) (dst2 : String) (src2 : JOperand)
    (h11 : dh1 ≠ dst2) (h21 : dl1 ≠ dst2)
    (ha1_dst2 : ¬ dst2 ∈ AsmPrinter.srcNames a1)
    (hb1_dst2 : ¬ dst2 ∈ AsmPrinter.srcNames b1)
    (hsrc2_dh1 : ¬ dh1 ∈ AsmPrinter.srcNames src2)
    (hsrc2_dl1 : ¬ dl1 ∈ AsmPrinter.srcNames src2) :
    evalInstr (evalInstr s (.mulx dh1 dl1 a1 b1)) (.adox dst2 src2)
      = evalInstr (evalInstr s (.adox dst2 src2)) (.mulx dh1 dl1 a1 b1) := by
  simp only [evalInstr]
  have heval_a1 : ∀ co res, JOperand.eval
      { regs := fun r' => if r' = dst2 then res else s.regs r',
        flags := { cf := s.flags.cf, pf := s.flags.pf, zf := s.flags.zf,
                   sf := s.flags.sf, of := co }, mem := s.mem } a1
      = JOperand.eval s a1 := by
    intro co res
    cases a1 with
    | reg rr =>
      simp only [JOperand.eval, JState.get]
      simp only [AsmPrinter.srcNames, List.mem_singleton] at ha1_dst2
      simp [Ne.symm ha1_dst2]
    | imm _ => rfl
  have heval_b1 : ∀ co res, JOperand.eval
      { regs := fun r' => if r' = dst2 then res else s.regs r',
        flags := { cf := s.flags.cf, pf := s.flags.pf, zf := s.flags.zf,
                   sf := s.flags.sf, of := co }, mem := s.mem } b1
      = JOperand.eval s b1 := by
    intro co res
    cases b1 with
    | reg rr =>
      simp only [JOperand.eval, JState.get]
      simp only [AsmPrinter.srcNames, List.mem_singleton] at hb1_dst2
      simp [Ne.symm hb1_dst2]
    | imm _ => rfl
  have hget_dst2 : ((s.setReg dl1 (x86_MULX_lo_hi (JOperand.eval s a1) (JOperand.eval s b1)).fst).setReg dh1
        (x86_MULX_lo_hi (JOperand.eval s a1) (JOperand.eval s b1)).snd).get dst2 = s.get dst2 := by
    simp [JState.get, JState.setReg, Ne.symm h11, Ne.symm h21]
  have hflagof : ((s.setReg dl1 (x86_MULX_lo_hi (JOperand.eval s a1) (JOperand.eval s b1)).fst).setReg dh1
        (x86_MULX_lo_hi (JOperand.eval s a1) (JOperand.eval s b1)).snd).flagB (fun x => x.of)
      = s.flagB (fun x => x.of) := by
    simp [JState.flagB, JState.setReg]
  have hsrc2 : JOperand.eval
      ((s.setReg dl1 (x86_MULX_lo_hi (JOperand.eval s a1) (JOperand.eval s b1)).fst).setReg dh1
        (x86_MULX_lo_hi (JOperand.eval s a1) (JOperand.eval s b1)).snd) src2 = JOperand.eval s src2 :=
    (eval_setReg_notMem _ src2 dh1 _ hsrc2_dh1).trans (eval_setReg_notMem _ src2 dl1 _ hsrc2_dl1)
  rw [hget_dst2, hflagof, hsrc2, heval_a1, heval_b1]
  apply JState.ext
  · funext r
    by_cases hr_dh1 : r = dh1 <;> by_cases hr_dl1 : r = dl1 <;> by_cases hr_dst2 : r = dst2 <;>
      simp_all [JState.setReg, JState.get, Ne.symm]
  · simp [JState.setReg]
  · simp [JState.setReg]

end CatCrypt.Crypto.SecureCompilation.X86Backend.RescheduleScratch
