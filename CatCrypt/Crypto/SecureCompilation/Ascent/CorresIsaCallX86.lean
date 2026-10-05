/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCall
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaX86

/-!
# A return appended to a body: step agreement at the x86, AArch64 and subset instruction sets

The lemmas `IsaCall.steps_snoc_ret_prefix` and `IsaCall.steps_snoc_ret` extend a halting run
of a body `B` without calls to the body `B ++ [Lret]` under `isa.withCalls`, given that the
step of `isa` on every instruction of `B` is the same on the two programs. This module proves
that hypothesis for the x86 instruction set `x86Isa` and for every instruction set whose step
is `LprogIsa.subsetStep`, for every instruction and every state.

The step `evalInstrPMemF` of `x86Isa` reads the program in three places, and in no other:

* the flag-reading conditional (`flagCondCC?`, the `Lcond` on a condition code) resolves
  its label with `evalJumpMem`;
* the counter conditional `Lcond` of `evalInstrPMemL` resolves its label with `evalJumpMem`;
* `Lgoto (fn, l)` of `evalInstrPMemL` compares `fn` with the name `P.lfn` of the function
  and resolves `l` with `evalJumpMem`.

`evalJumpMem` reads the body through the label search `findLabelMem` only, which a trailing
return does not change (`IsaCall.findLabelMem_snoc_ret`), and the two programs have the same
function name. The compare, the register copy, `Llabel`, the arithmetic, carry-family and
flag-quiet instructions, and the instructions without a step do not read the program.

The step `subsetStep` reads the program through the control step `ctlStep` and the core step
`coreStep`, in the same three ways.

## Main results

* `evalJumpMem_snoc_ret`, `evalInstrPMemL_snoc_ret`: a jump and a step of the labelled memref
  machine are the same on a body and on the body followed by a return.
* `x86Isa_step_snoc_ret`: the step of `x86Isa` is the same on the two programs.
* `x86_steps_snoc_ret_prefix`, `x86_steps_snoc_ret`: the two return lemmas at `x86Isa`,
  without the step-agreement hypothesis.
* `coreStep_snoc_ret`, `subsetStep_snoc_ret`, `step_snoc_ret_of_subsetStep`: the step of an
  instruction-set subset is the same on the two programs.
* `armIsa_step_snoc_ret`, `arm_steps_snoc_ret_prefix`, `arm_steps_snoc_ret`: the AArch64
  instances.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

namespace IsaCall

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LLabel LOperand LinstrR)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM LstatePM singletonProgM
  findLabelMem evalJumpMem evalInstrPMemL)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF evalInstrPMemF)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa isCall isCtl ctlStep coreStep
  subsetStep)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_step)
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmIsa (armIsa armIsa_step)

/-! ## 1. The labelled memref machine -/

/-- A jump resolves its label the same way in a body and in the body followed by a
    return. -/
theorem evalJumpMem_snoc_ret (fn : String) (B : List LinstrRM) (tag : MemTag) (l : LLabel)
    (s : LstatePM) :
    evalJumpMem (singletonProgM fn (B ++ [(.Lret, tag)])) l s =
      evalJumpMem (singletonProgM fn B) l s := by
  simp only [evalJumpMem, singletonProgM, findLabelMem_snoc_ret]

/-- The step of the labelled memref machine is the same on a body and on the body followed
    by a return. -/
theorem evalInstrPMemL_snoc_ret (fn : String) (B : List LinstrRM) (tag : MemTag)
    (i : LinstrRM) (s : LstatePM) :
    evalInstrPMemL (singletonProgM fn (B ++ [(.Lret, tag)])) i s =
      evalInstrPMemL (singletonProgM fn B) i s := by
  obtain ⟨w, t⟩ := i
  cases w with
  | Lcond c l => simp only [evalInstrPMemL, evalJumpMem_snoc_ret]
  | Lgoto p =>
      obtain ⟨f, l⟩ := p
      simp only [evalInstrPMemL, evalJumpMem_snoc_ret]
      rfl
  | _ => rfl

/-! ## 2. The x86 instruction set -/

/-- **Step agreement at x86.** The step of `x86Isa` on any instruction from any state is the
    same on the body `B` followed by a return and on `B`. -/
theorem x86Isa_step_snoc_ret (fn : String) (B : List LinstrRM) (tag : MemTag) (i : LinstrRM)
    (s : LstateMF) :
    x86Isa.step (singletonProgM fn (B ++ [(.Lret, tag)])) i s =
      x86Isa.step (singletonProgM fn B) i s := by
  rw [x86Isa_step]
  simp only [evalInstrPMemF, evalJumpMem_snoc_ret, evalInstrPMemL_snoc_ret]

/-- **The body of a procedure followed by its return, up to the return, at x86**:
    `steps_snoc_ret_prefix` at `x86Isa` with the step agreement proved. -/
theorem x86_steps_snoc_ret_prefix {fn : String} {B : List LinstrRM} {tag : MemTag}
    {k : Nat} {m m' : LstateMF} (hB : ∀ i ∈ B, isCall i.fst = false)
    (hrun : x86Isa.lsemFuelMemF (singletonProgM fn B) k m = some m')
    (hend : atPc (singletonProgM fn B) B.length m') :
    ∃ n, n ≤ k ∧ Steps x86Isa.withCalls (singletonProgM fn (B ++ [(.Lret, tag)])) n m m' ∧
      atPc (singletonProgM fn (B ++ [(.Lret, tag)])) B.length m' :=
  steps_snoc_ret_prefix x86Isa hB (fun i _ s => x86Isa_step_snoc_ret fn B tag i s) hrun hend

/-- **The body of a procedure followed by its return, at x86**: `steps_snoc_ret` at `x86Isa`
    with the step agreement proved. -/
theorem x86_steps_snoc_ret {fn : String} {B : List LinstrRM} {tag : MemTag}
    {k r : Nat} {v : BitVec 64} {m m' : LstateMF} (hB : ∀ i ∈ B, isCall i.fst = false)
    (hrun : x86Isa.lsemFuelMemF (singletonProgM fn B) k m = some m')
    (hend : atPc (singletonProgM fn B) B.length m')
    (hsp : m'.prog.base.reg.getW x86Isa.sp 64 = some (v - 8))
    (hra : m'.prog.base.lmem x86Isa.sp (v - 8).toInt = BitVec.ofNat 64 r) (hr : r < 2 ^ 64) :
    ∃ n, n ≤ k ∧
      Steps x86Isa.withCalls (singletonProgM fn (B ++ [(.Lret, tag)])) (n + 1) m
        (retState x86Isa.sp v r m') ∧
      atPc (singletonProgM fn (B ++ [(.Lret, tag)])) r (retState x86Isa.sp v r m') :=
  steps_snoc_ret x86Isa hB (fun i _ s => x86Isa_step_snoc_ret fn B tag i s) hrun hend hsp hra
    hr

/-! ## 3. Instruction-set subsets -/

/-- The control step is the same on a body and on the body followed by a return. -/
theorem ctlStep_snoc_ret (cond : LstateMF → LOperand → Bool) (fn : String)
    (B : List LinstrRM) (tag : MemTag) (i : LinstrRM) (s : LstateMF) :
    ctlStep cond (singletonProgM fn (B ++ [(.Lret, tag)])) i s =
      ctlStep cond (singletonProgM fn B) i s := by
  obtain ⟨w, t⟩ := i
  cases w with
  | Lcond c l => simp only [ctlStep, evalJumpMem_snoc_ret]
  | Lgoto p =>
      obtain ⟨f, l⟩ := p
      simp only [ctlStep, evalJumpMem_snoc_ret]
      rfl
  | _ => rfl

/-- The core step is the same on a body and on the body followed by a return. -/
theorem coreStep_snoc_ret (fn : String) (B : List LinstrRM) (tag : MemTag) (i : LinstrRM)
    (s : LstateMF) :
    coreStep (singletonProgM fn (B ++ [(.Lret, tag)])) i s =
      coreStep (singletonProgM fn B) i s := by
  simp only [coreStep, evalInstrPMemL_snoc_ret]

/-- **Step agreement for a subset.** The step `subsetStep bases cond ext` on any instruction
    from any state is the same on the body `B` followed by a return and on `B`. -/
theorem subsetStep_snoc_ret (bases : List String) (cond : LstateMF → LOperand → Bool)
    (ext : LinstrRM → LstateMF → Option (Option LstateMF)) (fn : String)
    (B : List LinstrRM) (tag : MemTag) (i : LinstrRM) (s : LstateMF) :
    subsetStep bases cond ext (singletonProgM fn (B ++ [(.Lret, tag)])) i s =
      subsetStep bases cond ext (singletonProgM fn B) i s := by
  simp only [subsetStep, ctlStep_snoc_ret, coreStep_snoc_ret]

/-- Step agreement for an instruction set whose step is a `subsetStep`. -/
theorem step_snoc_ret_of_subsetStep (isa : Isa) {bases : List String}
    {cond : LstateMF → LOperand → Bool}
    {ext : LinstrRM → LstateMF → Option (Option LstateMF)}
    (h : isa.step = subsetStep bases cond ext) (fn : String) (B : List LinstrRM)
    (tag : MemTag) (i : LinstrRM) (s : LstateMF) :
    isa.step (singletonProgM fn (B ++ [(.Lret, tag)])) i s =
      isa.step (singletonProgM fn B) i s := by
  rw [h]
  exact subsetStep_snoc_ret bases cond ext fn B tag i s

/-! ## 4. The AArch64 instruction set -/

/-- **Step agreement at AArch64.** The step of `armIsa` on any instruction from any state is
    the same on the body `B` followed by a return and on `B`. -/
theorem armIsa_step_snoc_ret (fn : String) (B : List LinstrRM) (tag : MemTag) (i : LinstrRM)
    (s : LstateMF) :
    armIsa.step (singletonProgM fn (B ++ [(.Lret, tag)])) i s =
      armIsa.step (singletonProgM fn B) i s :=
  step_snoc_ret_of_subsetStep armIsa armIsa_step fn B tag i s

/-- `steps_snoc_ret_prefix` at `armIsa` with the step agreement proved. -/
theorem arm_steps_snoc_ret_prefix {fn : String} {B : List LinstrRM} {tag : MemTag}
    {k : Nat} {m m' : LstateMF} (hB : ∀ i ∈ B, isCall i.fst = false)
    (hrun : armIsa.lsemFuelMemF (singletonProgM fn B) k m = some m')
    (hend : atPc (singletonProgM fn B) B.length m') :
    ∃ n, n ≤ k ∧ Steps armIsa.withCalls (singletonProgM fn (B ++ [(.Lret, tag)])) n m m' ∧
      atPc (singletonProgM fn (B ++ [(.Lret, tag)])) B.length m' :=
  steps_snoc_ret_prefix armIsa hB (fun i _ s => armIsa_step_snoc_ret fn B tag i s) hrun hend

/-- `steps_snoc_ret` at `armIsa` with the step agreement proved. -/
theorem arm_steps_snoc_ret {fn : String} {B : List LinstrRM} {tag : MemTag}
    {k r : Nat} {v : BitVec 64} {m m' : LstateMF} (hB : ∀ i ∈ B, isCall i.fst = false)
    (hrun : armIsa.lsemFuelMemF (singletonProgM fn B) k m = some m')
    (hend : atPc (singletonProgM fn B) B.length m')
    (hsp : m'.prog.base.reg.getW armIsa.sp 64 = some (v - 8))
    (hra : m'.prog.base.lmem armIsa.sp (v - 8).toInt = BitVec.ofNat 64 r) (hr : r < 2 ^ 64) :
    ∃ n, n ≤ k ∧
      Steps armIsa.withCalls (singletonProgM fn (B ++ [(.Lret, tag)])) (n + 1) m
        (retState armIsa.sp v r m') ∧
      atPc (singletonProgM fn (B ++ [(.Lret, tag)])) r (retState armIsa.sp v r m') :=
  steps_snoc_ret armIsa hB (fun i _ s => armIsa_step_snoc_ret fn B tag i s) hrun hend hsp hra
    hr

end IsaCall

end CatCrypt.Crypto.SecureCompilation.Ascent
