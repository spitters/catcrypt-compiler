/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaData

@[expose] public section

set_option autoImplicit false

/-!
# The instruction-set record of the `Lprog` back end: semantics fields

An `Isa` extends the data record `IsaData` of `VIR.LprogIsaData` (register file, calling convention
and the mnemonic data of the two-address legaliser) by the step semantics of one instruction
set over the flag-extended memref state `LstateMF`: a whole-instruction step `step`, the branch-condition evaluation
`condEval`, and the obligation `step_ctl` that on a control instruction (`Llabel`, `Lcond`,
`Lgoto`) the step is the control step `ctlStep condEval`, shared by every instruction set.
The state types and their flag bits `zf`, `cf`, `of` are fixed; an instruction set decides
through `step` which instructions write them.

The interpreters `Isa.lsemFuelMemF`, `Isa.evalInstrPMemFk`, `Isa.lsemFuelMemFk` and the
predicate `Isa.RunIdxOk` have the recursion of `JasminLsemMemFlagGuard.lsemFuelMemF` and of
the checked machine of `JasminLsemMemChecked`, with the step taken from the record. The x86
instance, whose step is `evalInstrPMemF`, is `X86Backend.X86Isa.x86Isa`; at that instance each
generic interpreter is the existing one by `rfl`.

Call and return are a second shared step, `callStep`, over the stack pointer `sp` of the
calling convention: `Lcall none (fn, l)` pushes the return address (the counter after the
call, as a word) to the word memory cell of `sp` at the decremented stack pointer and jumps
to `l`; `Lcall (some r) (fn, l)` writes the return address to the register `r` and jumps;
`Lret` sets the counter to the word of the memory cell the stack pointer addresses and
increments the stack pointer. `Isa.withCalls I` is the record `I` whose step is `callStep`
on `Lcall` and `Lret` and the step of `I` on every other instruction. The control
instructions `isCtl` and the obligation `step_ctl` do not mention calls, so the step of an
instance on `Lcall` and `Lret` is unconstrained, and `I.withCalls` is the instruction set
in which they have the shared meaning. On a program without `Lcall` and `Lret` the runs of
`I.withCalls` and `I` are equal (`Isa.withCalls_lsemFuelMemF`).

The keep marker `isKeep` of `VIR.LprogIsaData` has a third shared step, `keepStep`, which
advances the program counter and changes nothing else. `Isa.withKeep I` is the record `I`
whose step on a keep marker is `keepStep`; the steps of the control instructions and of
every other instruction are those of `I`.

A call of a separately provided procedure is, at this level, one instruction: the shadow
`callShadow dst f srcs`, an `Lopn` with the mnemonic `"CALL:" ++ f`. A table `ProcTable`
gives a summary `ProcSummary` (arity, a partial function on words, the positions of
array arguments and the length and function of a word-array result) to each procedure name,
and `Isa.withProcs I T` is the record `I` whose step on a shadow instruction of a
symbol of `T` is the step `procStep` of its summary. The step writes a word result to the
register of the destination and a word-array result to its array carrier (`retRes`).
Return addresses and the stack pointer do not appear in this step.

## Main results

* `ctlStep`, `isCtl`, `Isa`: the shared control step and the record.
* `Isa.lsemFuelMemF_halt`, `Isa.lsemFuelMemF_step`: the run equations.
* `Isa.lsemFuelMemF_add`, `Isa.lsemFuelMemF_of_runL`: a successful run is stable under more
  fuel, and a straight stretch at the end of the body runs as `Isa.runL`.
* `Isa.lsemFuelMemFk_false`, `Isa.lsemFuelMemF_of_checked`, `Isa.lsemFuelMemFk_of_runIdxOk`,
  `Isa.runIdxOk_of_checked`: the checked run against the unchecked one.
* `Isa.step_label`, `Isa.step_cond`, `Isa.step_goto`: the control step of every instance.
* `isCall`, `callStep`, `Isa.withCalls`: the call and return step and the instruction set
  that carries it.
* `Isa.step_call`, `Isa.step_call_link`, `Isa.step_ret`, `Isa.withCalls_step_of_not_call`:
  the step of `I.withCalls` on a call, on a return and on every other instruction.
* `Isa.withCalls_lsemFuelMemF`: the run of `I.withCalls` on a program without calls.
* `keepStep`, `Isa.withKeep`, `Isa.withKeep_step_keep`, `Isa.withKeep_step_of_not_keep`: the
  step of the keep marker and the instruction set that carries it.
* `ProcSummary`, `ProcTable`, `callShadow`, `procStep`, `Isa.withProcs`: procedure
  summaries and the instruction set that carries them.
* `CallRes`, `ProcSummary.result`, `ProcSummary.result_of_out`, `retArr`, `retRes`,
  `ProcSummary.RetWord`, `procStep_of_retWord`: the result of a call, a word or a word array, its write to the
  destination, and the step of a summary without a word-array result.
* `argsRead`, `argsRead_none`, `argsRead_congr`, `procStep_of_wordOnly`: the argument words
  of a call, which read word operands from the registers and array operands from the array
  carrier, and the step of a summary without array arguments.
* `Isa.withProcs_step_callShadow`, `Isa.withProcs_step_of_none`, `Isa.withProcs_empty`: the
  step of `I.withProcs T` on a shadow instruction and on every other instruction, and the
  instruction set at the table without procedures.
* `Isa.StepLe`, `Isa.RefusesProcs`, `Isa.withProcs_stepLe`: every step of an instruction
  set that refuses the shadow instructions of `T` is a step of the set with the summaries
  of `T`.
* `callMnem_ne`, `eq_callShadow_of_shadowCall?`, `loadStruct?_callShadow`,
  `storeStruct?_callShadow`: the shape of a shadow instruction of a call.
* `Isa.CallLocal`, `Isa.CallLocal.step_eq`, `Isa.withProcs_callLocal`: the steps of an
  instruction set beyond another are shadow instructions whose result (a word or a word
  array) depends on the argument words only and which write only the destination and the
  program counter; off the shadow instructions the two steps agree; the instruction set with
  the summaries of a table is such an extension.
* `Isa.CallLocalWord`, `Isa.CallLocalWord.callLocal`, `Isa.withProcs_callLocalWord`,
  `Isa.withProcs_callLocal_wordOnly`: the same with a word result at every call, and the
  instruction set with the summaries of a table without word-array results.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked

/-- The control instructions: labels, conditional jumps and gotos. -/
def isCtl : LinstrR → Bool
  | .Llabel _ _ => true
  | .Lcond _ _ => true
  | .Lgoto _ => true
  | _ => false

/-- **The control step**, shared by every instruction set: `Llabel` advances the pc,
    `Lcond c l` jumps to `l` when `condEval s c` and advances the pc otherwise, and
    `Lgoto (fn, l)` jumps to `l` within the function `fn` of the program. Any other
    instruction has no control step. -/
def ctlStep (condEval : LstateMF → LOperand → Bool) (P : LprogM) (i : LinstrRM)
    (s : LstateMF) : Option LstateMF :=
  match i.fst with
  | .Llabel _ _ => some { s with prog := { s.prog with base := s.prog.base.nextPc } }
  | .Lcond c l =>
      if condEval s c then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else some { s with prog := { s.prog with base := s.prog.base.nextPc } }
  | .Lgoto (fn, l) =>
      if fn = P.lfn then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else none
  | _ => none

/-- **The step of the keep marker**, shared by every instruction set: the program counter
    advances; the registers, the memory and the flags are unchanged. -/
def keepStep (s : LstateMF) : LstateMF :=
  { s with prog := { s.prog with base := s.prog.base.nextPc } }

/-- A keep marker is not a control instruction. -/
theorem isKeep_of_isCtl {i : LinstrR} (h : isCtl i = true) : isKeep i = false := by
  cases i <;> simp_all [isCtl, isKeep]

/-- The call and return instructions. -/
def isCall : LinstrR → Bool
  | .Lcall _ _ => true
  | .Lret => true
  | _ => false

/-- The return address of a call taken at the state `s`: the counter after the call, as a
    word. -/
def retAddr (s : LstateMF) : BitVec 64 := BitVec.ofNat 64 (s.prog.base.lpc + 1)

/-- The state `s` with the return address pushed on the stack whose pointer register `sp`
    holds `v`: the word memory cell of `sp` at `v - 8` holds the return address, and `sp`
    holds `v - 8`. -/
def pushRet (sp : String) (v : BitVec 64) (s : LstateMF) : LstateMF :=
  { s with prog := { s.prog with base :=
      (s.prog.base.storeMemC sp (v - 8).toInt (retAddr s)).setReg sp (v - 8) } }

/-- The state `s` with the return address written to the register `r`. -/
def linkRet (r : String) (s : LstateMF) : LstateMF :=
  { s with prog := { s.prog with base := s.prog.base.setReg r (retAddr s) } }

/-- The state `s` after a return through the stack whose pointer register `sp` holds `v`:
    the counter is the word of the memory cell of `sp` at `v`, and `sp` holds `v + 8`. -/
def popRet (sp : String) (v : BitVec 64) (s : LstateMF) : LstateMF :=
  { s with prog := { s.prog with base :=
      (s.prog.base.setReg sp (v + 8)).setLpc (s.prog.base.lmem sp v.toInt).toNat } }

/-- **The call and return step**, shared by every instruction set, over the stack pointer
    register `sp`. `Lcall none (fn, l)` pushes the return address (`pushRet`) and jumps to
    `l` within the function `fn` of the program; `Lcall (some r) (fn, l)` writes the return
    address to the register `r` (`linkRet`) and jumps to `l`; `Lret` pops the return address
    into the counter (`popRet`). A call or a return whose stack pointer does not hold a
    word of width `64`, and any other instruction, has no step. -/
def callStep (sp : String) (P : LprogM) (i : LinstrRM) (s : LstateMF) : Option LstateMF :=
  match i.fst with
  | .Lcall none (fn, l) =>
      if fn = P.lfn then
        (s.prog.base.reg.getW sp 64).bind fun v =>
          (evalJumpMem P l (pushRet sp v s).prog).map (fun p => { s with prog := p })
      else none
  | .Lcall (some r) (fn, l) =>
      if fn = P.lfn then
        (evalJumpMem P l (linkRet r s).prog).map (fun p => { s with prog := p })
      else none
  | .Lret => (s.prog.base.reg.getW sp 64).map fun v => popRet sp v s
  | _ => none

/-- **The instruction-set record of the `Lprog` back end**: the data `IsaData` (register
    file, calling convention, legaliser mnemonic data), the step of one instruction over the
    flag-extended memref state, the evaluation of a branch condition, and the obligation that
    the step of a control instruction is the shared control step under that evaluation. -/
structure Isa : Type extends IsaData where
  /-- The step of one instruction of the program `P` from a state. -/
  step : LprogM → LinstrRM → LstateMF → Option LstateMF
  /-- Whether the branch condition holds in a state. -/
  condEval : LstateMF → LOperand → Bool
  /-- On a control instruction the step is the shared control step. -/
  step_ctl : ∀ (P : LprogM) (i : LinstrRM) (s : LstateMF), isCtl i.fst = true →
    step P i s = ctlStep condEval P i s

namespace Isa

variable (I : Isa)

/-- The step of a label advances the pc. -/
theorem step_label (P : LprogM) (k : LabelKind) (l : LLabel) (tag : MemTag) (s : LstateMF) :
    I.step P (.Llabel k l, tag) s =
      some { s with prog := { s.prog with base := s.prog.base.nextPc } } :=
  I.step_ctl P _ s rfl

/-- The step of a conditional jump: jump when the condition holds, else advance the pc. -/
theorem step_cond (P : LprogM) (c : LOperand) (l : LLabel) (tag : MemTag) (s : LstateMF) :
    I.step P (.Lcond c l, tag) s =
      if I.condEval s c = true then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else some { s with prog := { s.prog with base := s.prog.base.nextPc } } :=
  I.step_ctl P _ s rfl

/-- The step of a goto: a jump within the function of the program, none otherwise. -/
theorem step_goto (P : LprogM) (x : String) (l : LLabel) (tag : MemTag) (s : LstateMF) :
    I.step P (.Lgoto (x, l), tag) s =
      if x = P.lfn then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else none :=
  I.step_ctl P _ s rfl

/-- The steps of a list of instructions, in order. -/
def runL (P : LprogM) : List LinstrRM → LstateMF → Option LstateMF
  | [], s => some s
  | i :: is, s => (I.step P i s).bind (runL P is)

/-- Fetch and step. -/
def lsemStepPMemF (P : LprogM) (s : LstateMF) : Option LstateMF :=
  match findInstrMem P s.prog with
  | some i => I.step P i s
  | none => none

/-- The fuel-stepped interpreter of the instruction set: iterate `step`, halting
    (returning the state) when `findInstrMem` is `none`. -/
def lsemFuelMemF (P : LprogM) : Nat → LstateMF → Option LstateMF
  | 0, s => match findInstrMem P s.prog with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrMem P s.prog with
      | none => some s
      | some i =>
          match I.step P i s with
          | some s' => lsemFuelMemF P fuel s'
          | none => none

/-- A halted state takes no step. -/
theorem lsemFuelMemF_halt (P : LprogM) (fuel : Nat) (s : LstateMF)
    (h : findInstrMem P s.prog = none) : I.lsemFuelMemF P fuel s = some s := by
  cases fuel <;> simp [lsemFuelMemF, h]

/-- One fetched-and-evaluated step under the fuel iterator. -/
theorem lsemFuelMemF_step (P : LprogM) (fuel : Nat) (i : LinstrRM) (s s' : LstateMF)
    (hfetch : findInstrMem P s.prog = some i) (heval : I.step P i s = some s') :
    I.lsemFuelMemF P (fuel + 1) s = I.lsemFuelMemF P fuel s' := by
  simp only [lsemFuelMemF, hfetch, heval]

/-- A successful run returns the same state at every larger fuel. -/
theorem lsemFuelMemF_add (P : LprogM) :
    ∀ (n k : Nat) (s t : LstateMF), I.lsemFuelMemF P n s = some t →
      I.lsemFuelMemF P (n + k) s = some t := by
  intro n
  induction n with
  | zero =>
      intro k s t h
      simp only [lsemFuelMemF] at h
      split at h
      · next hf => cases h; rw [Nat.zero_add]; exact I.lsemFuelMemF_halt P k s hf
      · cases h
  | succ n ih =>
      intro k s t h
      rw [Nat.add_right_comm]
      simp only [lsemFuelMemF] at h ⊢
      cases hf : findInstrMem P s.prog with
      | none => simp only [hf] at h ⊢; exact h
      | some i =>
          simp only [hf] at h ⊢
          cases hs : I.step P i s with
          | none => simp only [hs, reduceCtorEq] at h
          | some s' => simp only [hs] at h ⊢; exact ih k s' t h

/-- **A straight stretch at the end of the body.** When the body of `P` is `pre ++ rest`, the
    state is in the function of `P` at counter `pre.length`, and every step of an instruction
    of `rest` stays in the function and advances the counter by one, the run of `P` with fuel
    `rest.length` is the run `Isa.runL` of the instructions of `rest`. -/
theorem lsemFuelMemF_of_runL (P : LprogM) :
    ∀ (rest pre : List LinstrRM) (s t : LstateMF), P.body = pre ++ rest →
      s.prog.lfn = P.lfn → s.prog.base.lpc = pre.length →
      (∀ i ∈ rest, ∀ u u', I.step P i u = some u' →
        u'.prog.lfn = u.prog.lfn ∧ u'.prog.base.lpc = u.prog.base.lpc + 1) →
      I.runL P rest s = some t → I.lsemFuelMemF P rest.length s = some t := by
  intro rest
  induction rest with
  | nil =>
      intro pre s t hbody hfn hpc _ hrun
      cases hrun
      refine I.lsemFuelMemF_halt P 0 s ?_
      simp only [findInstrMem, hfn, if_true, hbody, List.append_nil, hpc,
        List.getElem?_eq_none (le_refl _)]
  | cons i rest ih =>
      intro pre s t hbody hfn hpc hstep hrun
      simp only [runL, Option.bind_eq_some_iff] at hrun
      obtain ⟨u, hu, hrun⟩ := hrun
      have hfetch : findInstrMem P s.prog = some i := by
        simp only [findInstrMem, hfn, if_true, hbody, hpc, List.getElem?_append_right
          (le_refl _), Nat.sub_self, List.getElem?_cons_zero]
      rw [List.length_cons, I.lsemFuelMemF_step P _ i s u hfetch hu]
      obtain ⟨hufn, hupc⟩ := hstep i (List.mem_cons_self ..) s u hu
      exact ih (pre ++ [i]) u t (by rw [hbody, List.append_assoc]; rfl) (hufn.trans hfn)
        (by rw [hupc, hpc, List.length_append, List.length_singleton])
        (fun j hj => hstep j (List.mem_cons_of_mem i hj)) hrun

/-- The checked step: with `ck`, the step when the instruction is in bounds (`idxOkB`) and
    none otherwise; without `ck`, the step. -/
def evalInstrPMemFk (ck : Bool) (P : LprogM) (i : LinstrRM) (s : LstateMF) :
    Option LstateMF :=
  if ck && !idxOkB i s then none else I.step P i s

/-- The run of the checked step, with the recursion of `lsemFuelMemF`. -/
def lsemFuelMemFk (ck : Bool) (P : LprogM) : Nat → LstateMF → Option LstateMF
  | 0, s => match findInstrMem P s.prog with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrMem P s.prog with
      | none => some s
      | some i =>
          match I.evalInstrPMemFk ck P i s with
          | some s' => lsemFuelMemFk ck P fuel s'
          | none => none

@[simp] theorem evalInstrPMemFk_false (P : LprogM) (i : LinstrRM) (s : LstateMF) :
    I.evalInstrPMemFk false P i s = I.step P i s := by
  simp [evalInstrPMemFk]

theorem evalInstrPMemFk_true (P : LprogM) (i : LinstrRM) (s : LstateMF) :
    I.evalInstrPMemFk true P i s = if idxOkB i s then I.step P i s else none := by
  cases h : idxOkB i s <;> simp [evalInstrPMemFk, h]

/-- A checked step is a step. -/
theorem step_of_k {ck : Bool} {P : LprogM} {i : LinstrRM} {s s' : LstateMF}
    (h : I.evalInstrPMemFk ck P i s = some s') : I.step P i s = some s' := by
  unfold evalInstrPMemFk at h
  split at h
  · cases h
  · exact h

/-- A successful checked step is in bounds. -/
theorem idxOkB_of_checked {P : LprogM} {i : LinstrRM} {s s' : LstateMF}
    (h : I.evalInstrPMemFk true P i s = some s') : idxOkB i s = true := by
  rw [evalInstrPMemFk_true] at h
  cases hb : idxOkB i s
  · simp [hb] at h
  · rfl

/-- The unchecked instance of the checked run is the run. -/
theorem lsemFuelMemFk_false (P : LprogM) :
    ∀ (fuel : Nat) (s : LstateMF), I.lsemFuelMemFk false P fuel s = I.lsemFuelMemF P fuel s
  | 0, s => by
      cases hf : findInstrMem P s.prog <;> simp only [lsemFuelMemFk, lsemFuelMemF, hf]
  | fuel + 1, s => by
      cases hf : findInstrMem P s.prog with
      | none => simp only [lsemFuelMemFk, lsemFuelMemF, hf]
      | some i =>
          simp only [lsemFuelMemFk, lsemFuelMemF, hf, evalInstrPMemFk_false]
          cases I.step P i s with
          | none => rfl
          | some s' => exact lsemFuelMemFk_false P fuel s'

theorem lsemFuelMemFk_halt (ck : Bool) (P : LprogM) (fuel : Nat) (s : LstateMF)
    (h : findInstrMem P s.prog = none) : I.lsemFuelMemFk ck P fuel s = some s := by
  cases fuel <;> simp [lsemFuelMemFk, h]

theorem lsemFuelMemFk_step (ck : Bool) (P : LprogM) (fuel : Nat) (i : LinstrRM)
    (s s' : LstateMF) (hfetch : findInstrMem P s.prog = some i)
    (heval : I.evalInstrPMemFk ck P i s = some s') :
    I.lsemFuelMemFk ck P (fuel + 1) s = I.lsemFuelMemFk ck P fuel s' := by
  simp only [lsemFuelMemFk, hfetch, heval]

/-- A halting checked run is a halting run, to the same state. -/
theorem lsemFuelMemF_of_checked {ck : Bool} (P : LprogM) :
    ∀ (fuel : Nat) (s t : LstateMF), I.lsemFuelMemFk ck P fuel s = some t →
      I.lsemFuelMemF P fuel s = some t
  | 0, s, t, h => by
      cases hf : findInstrMem P s.prog <;>
        simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢ <;> exact h
  | fuel + 1, s, t, h => by
      cases hf : findInstrMem P s.prog with
      | none => simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢; exact h
      | some i =>
          simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢
          cases he : I.evalInstrPMemFk ck P i s with
          | none => simp [he] at h
          | some s' =>
              rw [he] at h
              simp only [I.step_of_k he]
              exact lsemFuelMemF_of_checked P fuel s' t h

/-- Every state that a run of at most `fuel` steps steps from is in bounds at the
    instruction it fetches. -/
def RunIdxOk (P : LprogM) : Nat → LstateMF → Prop
  | 0, _ => True
  | fuel + 1, s =>
      ∀ i, findInstrMem P s.prog = some i →
        idxOkB i s = true ∧ ∀ s', I.step P i s = some s' → RunIdxOk P fuel s'

/-- A halting run whose accesses are in bounds is a halting checked run, to the same
    state. -/
theorem lsemFuelMemFk_of_runIdxOk (ck : Bool) (P : LprogM) :
    ∀ (fuel : Nat) (s t : LstateMF), I.lsemFuelMemF P fuel s = some t → I.RunIdxOk P fuel s →
      I.lsemFuelMemFk ck P fuel s = some t
  | 0, s, t, h, _ => by
      cases hf : findInstrMem P s.prog <;>
        simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢ <;> exact h
  | fuel + 1, s, t, h, hok => by
      cases hf : findInstrMem P s.prog with
      | none => simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢; exact h
      | some i =>
          simp only [lsemFuelMemFk, lsemFuelMemF, hf] at h ⊢
          obtain ⟨hi, hnext⟩ := hok i hf
          cases he : I.step P i s with
          | none => simp [he] at h
          | some s' =>
              rw [he] at h
              have hk : I.evalInstrPMemFk ck P i s = some s' := by
                simp [evalInstrPMemFk, hi, he]
              simp only [hk]
              exact lsemFuelMemFk_of_runIdxOk ck P fuel s' t h (hnext s' he)

/-- A halting checked run is in bounds: every state it steps from fetches an instruction
    in bounds. -/
theorem runIdxOk_of_checked (P : LprogM) :
    ∀ (fuel : Nat) (s t : LstateMF), I.lsemFuelMemFk true P fuel s = some t →
      I.RunIdxOk P fuel s
  | 0, _, _, _ => trivial
  | fuel + 1, s, t, h => by
      intro i hf
      simp only [lsemFuelMemFk, hf] at h
      cases he : I.evalInstrPMemFk true P i s with
      | none => simp [he] at h
      | some s' =>
          rw [he] at h
          refine ⟨I.idxOkB_of_checked he, fun s'' he' => ?_⟩
          rw [I.step_of_k he] at he'
          cases he'
          exact runIdxOk_of_checked P fuel s' t h

/-! ## Call and return -/

/-- **The instruction set with call and return.** The record `I` with its step replaced, on
    `Lcall` and `Lret`, by the call and return step `callStep` over the stack pointer
    `I.sp`; the step of every other instruction, the data and the branch condition are those
    of `I`. -/
def withCalls : Isa :=
  { I with
    step := fun P i s => if isCall i.fst = true then callStep I.sp P i s else I.step P i s
    step_ctl := fun P i s h => by
      have hc : isCall i.fst = false := by
        cases hi : i.fst <;> simp_all [isCtl, isCall]
      simp only [hc, Bool.false_eq_true, if_false]
      exact I.step_ctl P i s h }

@[simp] theorem withCalls_toIsaData : I.withCalls.toIsaData = I.toIsaData := rfl

@[simp] theorem withCalls_condEval : I.withCalls.condEval = I.condEval := rfl

/-- The step of an instruction other than a call or a return is the step of `I`. -/
theorem withCalls_step_of_not_call (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (h : isCall i.fst = false) : I.withCalls.step P i s = I.step P i s := by
  simp only [withCalls, h, Bool.false_eq_true, if_false]

/-- The step of a call through the stack: push the return address and jump within the
    function of the program, none otherwise. -/
theorem step_call (P : LprogM) (x : String) (l : LLabel) (tag : MemTag) (s : LstateMF) :
    I.withCalls.step P (.Lcall none (x, l), tag) s =
      if x = P.lfn then
        (s.prog.base.reg.getW I.sp 64).bind fun v =>
          (evalJumpMem P l (pushRet I.sp v s).prog).map (fun p => { s with prog := p })
      else none :=
  rfl

/-- The step of a call through a link register: write the return address to the register
    and jump within the function of the program, none otherwise. -/
theorem step_call_link (P : LprogM) (r x : String) (l : LLabel) (tag : MemTag)
    (s : LstateMF) :
    I.withCalls.step P (.Lcall (some r) (x, l), tag) s =
      if x = P.lfn then
        (evalJumpMem P l (linkRet r s).prog).map (fun p => { s with prog := p })
      else none :=
  rfl

/-- The step of a return: pop the return address into the counter. -/
theorem step_ret (P : LprogM) (tag : MemTag) (s : LstateMF) :
    I.withCalls.step P (.Lret, tag) s =
      (s.prog.base.reg.getW I.sp 64).map fun v => popRet I.sp v s :=
  rfl

/-- On a program without call and return instructions the run of `I.withCalls` is the run
    of `I`. -/
theorem withCalls_lsemFuelMemF (P : LprogM) (hP : ∀ i ∈ P.body, isCall i.fst = false) :
    ∀ (fuel : Nat) (s : LstateMF),
      I.withCalls.lsemFuelMemF P fuel s = I.lsemFuelMemF P fuel s
  | 0, s => by
      cases hf : findInstrMem P s.prog <;> simp only [lsemFuelMemF, hf]
  | fuel + 1, s => by
      cases hf : findInstrMem P s.prog with
      | none => simp only [lsemFuelMemF, hf]
      | some i =>
          have hi : i ∈ P.body := by
            unfold findInstrMem at hf
            split at hf
            · exact List.mem_of_getElem? hf
            · cases hf
          simp only [lsemFuelMemF, hf, I.withCalls_step_of_not_call P i s (hP i hi)]
          cases I.step P i s with
          | none => rfl
          | some s' => exact withCalls_lsemFuelMemF P hP fuel s'

/-! ## The keep marker -/

/-- **The instruction set with the keep marker.** The record `I` with its step replaced, on
    a keep marker `isKeep`, by `keepStep`; the step of every other instruction, the data and
    the branch condition are those of `I`. -/
def withKeep : Isa :=
  { I with
    step := fun P i s => if isKeep i.fst = true then some (keepStep s) else I.step P i s
    step_ctl := fun P i s h => by
      simp only [isKeep_of_isCtl h, Bool.false_eq_true, if_false]
      exact I.step_ctl P i s h }

@[simp] theorem withKeep_toIsaData : I.withKeep.toIsaData = I.toIsaData := rfl

@[simp] theorem withKeep_condEval : I.withKeep.condEval = I.condEval := rfl

/-- **The keep marker is a no-op** of `I.withKeep`: the step advances the program counter
    and changes nothing else. -/
theorem withKeep_step_keep (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (h : isKeep i.fst = true) : I.withKeep.step P i s = some (keepStep s) := by
  simp only [withKeep, h, if_true]

/-- The step of an instruction other than a keep marker is the step of `I`. -/
theorem withKeep_step_of_not_keep (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (h : isKeep i.fst = false) : I.withKeep.step P i s = I.step P i s := by
  simp only [withKeep, h, Bool.false_eq_true, if_false]

/-- The step of `I.withKeep` on the keep marker `keepTouch ctr r`. -/
theorem withKeep_step_keepTouch (P : LprogM) (ctr r : String) (tag : MemTag) (s : LstateMF) :
    I.withKeep.step P (keepTouch ctr r, tag) s = some (keepStep s) :=
  I.withKeep_step_keep P _ s rfl

end Isa

/-! ## Procedure summaries -/

/-- A procedure summary: the number of arguments, a partial function from the argument
    words to the result word, the positions of the array arguments with their lengths
    in words, and the length of a word-array result with a partial function from the
    argument words to that array. The argument words are the words of the arguments in
    order, an array argument contributing all its words. -/
structure ProcSummary where
  /-- The number of arguments. -/
  arity : Nat
  /-- The result word at the argument words; `none` is a refusal. -/
  run : List (BitVec 64) → Option (BitVec 64)
  /-- The length in words of the array argument at a position; `none` at a word
      argument. -/
  arrArgs : Nat → Option Nat := fun _ => none
  /-- The length in words of the word-array result; `none` at a summary without one. -/
  out : Option Nat := none
  /-- The word-array result of length `n` at the argument words; `none` is a refusal. The
      step reads it at the length `out` only. -/
  runOut : (n : Nat) → List (BitVec 64) → Option (Fin n → BitVec 64) := fun _ _ => none

/-- A summary whose every argument is a word. -/
def ProcSummary.WordOnly (pr : ProcSummary) : Prop :=
  pr.arrArgs = fun _ => none

/-- A summary without a word-array result. -/
def ProcSummary.RetWord (pr : ProcSummary) : Prop :=
  pr.out = none

/-- The result of a call: a word, or an array of `n` words. -/
inductive CallRes : Type where
  /-- A word result. -/
  | word (r : BitVec 64)
  /-- A word-array result of length `n`. -/
  | arr {n : Nat} (a : Fin n → BitVec 64)

/-- The result of a summary at the argument words: the word of `run` where it is defined,
    and otherwise the array of `runOut` at the length `out`. -/
def ProcSummary.result (pr : ProcSummary) (vs : List (BitVec 64)) : Option CallRes :=
  match pr.run vs with
  | some r => some (.word r)
  | none =>
      match pr.out with
      | none => none
      | some n => (pr.runOut n vs).map CallRes.arr

/-- **The result of a summary without a word-array result is the word of `run`.** -/
theorem ProcSummary.result_of_retWord {pr : ProcSummary} (h : pr.RetWord)
    (vs : List (BitVec 64)) : pr.result vs = (pr.run vs).map CallRes.word := by
  unfold result
  rw [show pr.out = none from h]
  cases pr.run vs <;> rfl

/-- **The result of a summary with a word-array result of length `n`**, at argument words
    where `run` is undefined, is the array of `runOut n`. -/
theorem ProcSummary.result_of_out {pr : ProcSummary} {n : Nat} (h : pr.out = some n)
    {vs : List (BitVec 64)} (hr : pr.run vs = none) :
    pr.result vs = (pr.runOut n vs).map CallRes.arr := by
  unfold result
  rw [hr, h]

/-- A table of procedure summaries by symbol name. -/
abbrev ProcTable : Type := String → Option ProcSummary

/-- The table without procedures. -/
def ProcTable.empty : ProcTable := fun _ => none

/-- The shadow instruction of a call of the symbol `f` on the operands `srcs` with the
    result in the register `dst`. -/
def callShadow (dst f : String) (srcs : List LOperand) : LinstrR :=
  .Lopn [.reg dst] ("CALL:" ++ f) srcs

/-- The destination, the symbol and the operands of a shadow instruction of a call. -/
def shadowCall? : LinstrR → Option (String × String × List LOperand)
  | .Lopn [.reg dst] opn srcs =>
      if "CALL:".toList.isPrefixOf opn.toList then
        some (dst, String.ofList (opn.toList.drop "CALL:".toList.length), srcs)
      else none
  | _ => none

theorem shadowCall?_callShadow (dst f : String) (srcs : List LOperand) :
    shadowCall? (callShadow dst f srcs) = some (dst, f, srcs) := by
  simp only [callShadow, shadowCall?]
  rw [String.toList_append]
  simp [List.isPrefixOf, String.ofList_toList]

/-- The mnemonic of a shadow instruction is no mnemonic without the prefix `"CALL:"`. -/
theorem callMnem_ne {f x : String} (hx : "CALL:".toList.isPrefixOf x.toList = false) :
    "CALL:" ++ f ≠ x := by
  rintro rfl
  rw [String.toList_append] at hx
  simp [List.isPrefixOf] at hx

/-- An instruction is the shadow instruction of a call exactly when `shadowCall?` reads it. -/
theorem eq_callShadow_of_shadowCall? {i : LinstrR} {dst f : String} {srcs : List LOperand}
    (h : shadowCall? i = some (dst, f, srcs)) : i = callShadow dst f srcs := by
  unfold shadowCall? at h
  split at h
  · rename_i dst' opn srcs'
    split at h
    · rename_i hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hpre := (List.prefix_iff_eq_append).mp (List.isPrefixOf_iff_prefix.mp hp)
      simp only [callShadow, LinstrR.Lopn.injEq, true_and, and_true]
      apply String.toList_injective
      rw [String.toList_append]
      simpa using hpre.symm
    · cases h
  · cases h

/-- A shadow instruction of a call is no runtime-indexed load. -/
theorem loadStruct?_callShadow (dst f : String) (srcs : List LOperand) :
    loadStruct? (callShadow dst f srcs) = none := by
  unfold loadStruct? callShadow
  split
  · next heq =>
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, -⟩ := heq
      exact if_neg (callMnem_ne (by decide))
  · rfl

/-- A shadow instruction of a call is no runtime-indexed store. -/
theorem storeStruct?_callShadow (dst f : String) (srcs : List LOperand) :
    storeStruct? (callShadow dst f srcs) = none := by
  unfold storeStruct? callShadow
  split
  · next heq =>
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, -⟩ := heq
      exact if_neg (callMnem_ne (by decide))
  · rfl

/-- A control instruction is no shadow instruction of a call. -/
theorem shadowCall?_of_isCtl {i : LinstrR} (h : isCtl i = true) : shadowCall? i = none := by
  cases i <;> simp_all [isCtl, shadowCall?]

/-- The summary, the destination and the operands of a shadow instruction of a call of a
    symbol of the table `T`. -/
def procCall? (T : ProcTable) (i : LinstrR) : Option (ProcSummary × String × List LOperand) :=
  (shadowCall? i).bind fun q => (T q.2.1).map fun pr => (pr, q.1, q.2.2)

@[simp] theorem procCall?_empty (i : LinstrR) : procCall? ProcTable.empty i = none := by
  simp [procCall?, ProcTable.empty]

theorem procCall?_callShadow (T : ProcTable) (dst f : String) (srcs : List LOperand) :
    procCall? T (callShadow dst f srcs) = (T f).map fun pr => (pr, dst, srcs) := by
  simp only [procCall?, shadowCall?_callShadow, Option.bind_some]

/-- The state `s` with the word `r` in the register `dst` and the program counter
    advanced. -/
def retWord (dst : String) (r : BitVec 64) (s : LstateMF) : LstateMF :=
  { s with prog := { s.prog with base := (s.prog.base.setReg dst r).nextPc } }

/-- The state `s` with the array `a` in the array carrier of `dst` and the program counter
    advanced. -/
def retArr (dst : String) {n : Nat} (a : Fin n → BitVec 64) (s : LstateMF) : LstateMF :=
  { s with prog := { s.prog with base := (s.prog.base.setArr dst a).nextPc } }

/-- The state `s` with the result `x` of a call at the destination `dst` (`retWord` for a
    word, `retArr` for an array) and the program counter advanced. -/
def retRes (dst : String) : CallRes → LstateMF → LstateMF
  | .word r => retWord dst r
  | .arr a => retArr dst a

@[simp] theorem retRes_word (dst : String) (r : BitVec 64) (s : LstateMF) :
    retRes dst (.word r) s = retWord dst r s := rfl

@[simp] theorem retRes_arr (dst : String) {n : Nat} (a : Fin n → BitVec 64) (s : LstateMF) :
    retRes dst (.arr a) s = retArr dst a s := rfl

/-- The result of a call advances the program counter. -/
theorem lpc_retRes (dst : String) (x : CallRes) (s : LstateMF) :
    (retRes dst x s).prog.base.lpc = s.prog.base.lpc + 1 := by
  cases x <;> rfl

/-- The result of a call keeps the function name. -/
theorem lfn_retRes (dst : String) (x : CallRes) (s : LstateMF) :
    (retRes dst x s).prog.lfn = s.prog.lfn := by
  cases x <;> rfl

/-- The words of the operand `o` at the argument position `i`, for the array positions
    `aa`: at a word position the word of the operand, at an array position of length `n`
    the `n` words of the array carrier of the register name of the operand. -/
def argRead (aa : Nat → Option Nat) (b : LstateM) (i : Nat) (o : LOperand) :
    Option (List (BitVec 64)) :=
  match aa i with
  | none => (evalOperandN b.reg 64 o).map fun v => [v]
  | some n =>
      match o with
      | .reg A => (b.getArr A 64 n).map List.ofFn
      | _ => none

/-- The argument words of the operands `srcs` from the argument position `i`, for the array
    positions `aa`: the words of each operand (`argRead`), in order. -/
def argsRead (aa : Nat → Option Nat) (b : LstateM) : Nat → List LOperand →
    Option (List (BitVec 64))
  | _, [] => some []
  | i, o :: os => (argRead aa b i o).bind fun v => (argsRead aa b (i + 1) os).map (v ++ ·)

/-- **Without array positions the argument words are the words of the operands.** -/
theorem argsRead_none (b : LstateM) :
    ∀ (i : Nat) (srcs : List LOperand),
      argsRead (fun _ => none) b i srcs = srcs.mapM (evalOperandN b.reg 64)
  | _, [] => rfl
  | i, o :: os => by
      rw [argsRead, List.mapM_cons, argsRead_none b (i + 1) os]
      simp only [argRead]
      cases evalOperandN b.reg 64 o <;> cases os.mapM (evalOperandN b.reg 64) <;> rfl

/-- **The argument words read only the operand values and the array carrier.** -/
theorem argsRead_congr (aa : Nat → Option Nat) {b b' : LstateM}
    (hla : b'.larr = b.larr) :
    ∀ (i : Nat) (srcs : List LOperand),
      (∀ o ∈ srcs, evalOperandN b'.reg 64 o = evalOperandN b.reg 64 o) →
      argsRead aa b' i srcs = argsRead aa b i srcs
  | _, [], _ => rfl
  | i, o :: os, h => by
      have ho : argRead aa b' i o = argRead aa b i o := by
        unfold argRead
        split
        · rw [h o (List.mem_cons_self ..)]
        · split
          · unfold LstateM.getArr
            rw [hla]
          · rfl
      rw [argsRead, argsRead, ho,
        argsRead_congr aa hla (i + 1) os fun o' ho' => h o' (List.mem_cons_of_mem _ ho')]

/-- The argument words of register operands at two states that agree on the registers and
    on the array carrier are equal. -/
theorem argsRead_regs_congr (aa : Nat → Option Nat) {b b' : LstateM}
    (hla : b'.larr = b.larr) (i : Nat) {xs : List String}
    (h : ∀ x ∈ xs, b'.reg.lvm x = b.reg.lvm x) :
    argsRead aa b' i (xs.map LOperand.reg) = argsRead aa b i (xs.map LOperand.reg) := by
  refine argsRead_congr aa hla i _ fun o ho => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ho
  simp only [evalOperandN]
  unfold LstateN.getW
  rw [h x hx]

/-- **The step of a procedure summary** on the operands `srcs` with the destination `dst`:
    read the argument words of the operands (`argsRead` at the array positions of the
    summary), take the result of the summary (`ProcSummary.result`) and write it to `dst`
    (`retRes`: a word to the register, an array to the array carrier), advancing the
    program counter. A number of operands other than the arity, an unreadable operand and
    a refusal of the summary have no step. -/
def procStep (pr : ProcSummary) (dst : String) (srcs : List LOperand) (s : LstateMF) :
    Option LstateMF :=
  if srcs.length = pr.arity then
    (argsRead pr.arrArgs s.prog.base 0 srcs).bind fun vs =>
      (pr.result vs).map fun x => retRes dst x s
  else none

/-- **The step of a summary without a word-array result** writes the word of `run` to the
    register `dst`. -/
theorem procStep_of_retWord {pr : ProcSummary} (h : pr.RetWord) (dst : String)
    (srcs : List LOperand) (s : LstateMF) :
    procStep pr dst srcs s =
      if srcs.length = pr.arity then
        (argsRead pr.arrArgs s.prog.base 0 srcs).bind fun vs =>
          (pr.run vs).map fun r => retWord dst r s
      else none := by
  unfold procStep
  simp only [ProcSummary.result_of_retWord h, Option.map_map]
  rfl

/-- **The step of a summary on words** reads the operands as words. -/
theorem procStep_of_wordOnly {pr : ProcSummary} (h : pr.WordOnly) (hr : pr.RetWord)
    (dst : String) (srcs : List LOperand) (s : LstateMF) :
    procStep pr dst srcs s =
      if srcs.length = pr.arity then
        (srcs.mapM (evalOperandN s.prog.base.reg 64)).bind fun vs =>
          (pr.run vs).map fun r => retWord dst r s
      else none := by
  rw [procStep_of_retWord hr, h, argsRead_none]

namespace Isa

variable (I : Isa)

/-- **The instruction set with procedure summaries.** The record `I` with its step
    replaced, on a shadow instruction of a call of a symbol of the table `T`, by the step
    `procStep` of the summary of the symbol; the step of every other instruction, the data
    and the branch condition are those of `I`. -/
def withProcs (T : ProcTable) : Isa :=
  { I with
    step := fun P i s =>
      match procCall? T i.fst with
      | some q => procStep q.1 q.2.1 q.2.2 s
      | none => I.step P i s
    step_ctl := fun P i s h => by
      simp only [procCall?, shadowCall?_of_isCtl h, Option.bind_none]
      exact I.step_ctl P i s h }

@[simp] theorem withProcs_toIsaData (T : ProcTable) : (I.withProcs T).toIsaData = I.toIsaData :=
  rfl

@[simp] theorem withProcs_condEval (T : ProcTable) : (I.withProcs T).condEval = I.condEval :=
  rfl

/-- The step of the shadow instruction of a call of a symbol of the table is the step of
    its summary. -/
theorem withProcs_step_callShadow (T : ProcTable) {f : String} {pr : ProcSummary}
    (hf : T f = some pr) (P : LprogM) (dst : String) (srcs : List LOperand) (tag : MemTag)
    (s : LstateMF) :
    (I.withProcs T).step P (callShadow dst f srcs, tag) s = procStep pr dst srcs s := by
  simp only [withProcs, procCall?_callShadow, hf, Option.map_some]

/-- The step of an instruction that is no shadow instruction of a call of a symbol of the
    table is the step of `I`. -/
theorem withProcs_step_of_none (T : ProcTable) (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (h : procCall? T i.fst = none) : (I.withProcs T).step P i s = I.step P i s := by
  simp only [withProcs, h]

/-- **At the table without procedures the instruction set is `I`.** -/
@[simp] theorem withProcs_empty : I.withProcs ProcTable.empty = I := by
  cases I
  simp only [withProcs, procCall?_empty]

/-- Every step of `I` is a step of `J`, to the same state. -/
def StepLe (J : Isa) : Prop :=
  ∀ (P : LprogM) (i : LinstrRM) (s s' : LstateMF), I.step P i s = some s' →
    J.step P i s = some s'

theorem StepLe.refl : I.StepLe I := fun _ _ _ _ h => h

/-- `I` has no step on a shadow instruction of a call of a symbol of the table `T`. -/
def RefusesProcs (T : ProcTable) : Prop :=
  ∀ (P : LprogM) (i : LinstrRM) (s : LstateMF), procCall? T i.fst ≠ none → I.step P i s = none

/-- Every instruction set refuses the procedures of the table without procedures. -/
theorem refusesProcs_empty : I.RefusesProcs ProcTable.empty :=
  fun _ i _ h => absurd (procCall?_empty i.fst) h

/-- Every step of an instruction set that refuses the procedures of `T` is a step of the
    instruction set with the summaries of `T`. -/
theorem withProcs_stepLe {T : ProcTable} (h : I.RefusesProcs T) : I.StepLe (I.withProcs T) := by
  intro P i s s' hs
  cases hq : procCall? T i.fst with
  | none => rw [I.withProcs_step_of_none T P i s hq]; exact hs
  | some q => rw [h P i s (by rw [hq]; exact Option.some_ne_none q)] at hs; cases hs

/-- **The steps of `I` beyond `J` are local calls**, with the array positions `aa f` of each
    symbol `f`. Every step of `I` is a step of `J` to the same state, or a step of a shadow
    instruction `callShadow dst f srcs` that writes a result `x` (a word or a word array) to
    `dst` and advances the program counter (`retRes dst x`), and that `I` takes, to the
    result `x` again, at every program, tag, destination and state on every list of as many
    operands whose argument words (`argsRead (aa f)`) are those of `srcs`. The result thus
    depends on the operand values and on the array carrier at the array positions only, and
    the step writes only the destination and the program counter. -/
def CallLocal (J : Isa) (aa : String → Nat → Option Nat) : Prop :=
  ∀ (P : LprogM) (i : LinstrRM) (s t : LstateMF), I.step P i s = some t →
    J.step P i s = some t ∨
      ∃ (dst f : String) (srcs : List LOperand) (x : CallRes),
        i.1 = callShadow dst f srcs ∧ t = retRes dst x s ∧
        ∀ (P' : LprogM) (tag : MemTag) (dst' : String) (srcs' : List LOperand) (s' : LstateMF),
          srcs'.length = srcs.length →
          argsRead (aa f) s'.prog.base 0 srcs' = argsRead (aa f) s.prog.base 0 srcs →
          I.step P' (callShadow dst' f srcs', tag) s' = some (retRes dst' x s')

/-- Every instruction set is call-local over itself. -/
theorem CallLocal.refl (aa : String → Nat → Option Nat) : I.CallLocal I aa :=
  fun _ _ _ _ h => Or.inl h

/-- **The steps of `I` beyond `J` are local calls with word results**: `CallLocal` with a
    word `r` written to the register `dst` (`retWord dst r`) at every call. -/
def CallLocalWord (J : Isa) (aa : String → Nat → Option Nat) : Prop :=
  ∀ (P : LprogM) (i : LinstrRM) (s t : LstateMF), I.step P i s = some t →
    J.step P i s = some t ∨
      ∃ (dst f : String) (srcs : List LOperand) (r : BitVec 64),
        i.1 = callShadow dst f srcs ∧ t = retWord dst r s ∧
        ∀ (P' : LprogM) (tag : MemTag) (dst' : String) (srcs' : List LOperand) (s' : LstateMF),
          srcs'.length = srcs.length →
          argsRead (aa f) s'.prog.base 0 srcs' = argsRead (aa f) s.prog.base 0 srcs →
          I.step P' (callShadow dst' f srcs', tag) s' = some (retWord dst' r s')

/-- Local calls with word results are local calls. -/
theorem CallLocalWord.callLocal {J : Isa} {aa : String → Nat → Option Nat}
    (h : I.CallLocalWord J aa) : I.CallLocal J aa := by
  intro P i s t hs
  rcases h P i s t hs with hx | ⟨dst, f, srcs, r, hi, ht, hfwd⟩
  · exact Or.inl hx
  · exact Or.inr ⟨dst, f, srcs, .word r, hi, ht, hfwd⟩

/-- Every instruction set is call-local with word results over itself. -/
theorem CallLocalWord.refl (aa : String → Nat → Option Nat) : I.CallLocalWord I aa :=
  fun _ _ _ _ h => Or.inl h

/-- **Off the shadow instructions the steps agree.** When every step of `J` is a step of `I`
    and the steps of `I` beyond `J` are local calls, the step of `I` at an instruction that is
    no shadow instruction of a call is the step of `J`. -/
theorem CallLocal.step_eq {J : Isa} {aa : String → Nat → Option Nat} (hle : J.StepLe I)
    (hcl : I.CallLocal J aa) (P : LprogM) {i : LinstrRM} (hi : shadowCall? i.1 = none)
    (s : LstateMF) : I.step P i s = J.step P i s := by
  cases hI : I.step P i s with
  | some t =>
      rcases hcl P i s t hI with h | ⟨dst, f, srcs, x, hsh, -, -⟩
      · exact h.symm
      · rw [hsh, shadowCall?_callShadow] at hi
        cases hi
  | none =>
      cases hJ : J.step P i s with
      | none => rfl
      | some t => rw [hle P i s t hJ] at hI; cases hI

/-- The array positions of the summaries of a table, by symbol; no array position at a
    symbol without a summary. -/
def procArrArgs (T : ProcTable) (f : String) : Nat → Option Nat :=
  match T f with
  | some pr => pr.arrArgs
  | none => fun _ => none

/-- **The steps of `I.withProcs T` beyond `I` are local calls** at the array positions of the
    summaries. -/
theorem withProcs_callLocal (T : ProcTable) : (I.withProcs T).CallLocal I (procArrArgs T) := by
  intro P i s t h
  cases hq : procCall? T i.1 with
  | none => rw [I.withProcs_step_of_none T P i s hq] at h; exact Or.inl h
  | some q =>
      obtain ⟨pr, dst, srcs⟩ := q
      right
      simp only [procCall?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨⟨dst₀, f, srcs₀⟩, hsh, pr', hf, hpr⟩ := hq
      simp only [Prod.mk.injEq] at hpr
      obtain ⟨rfl, rfl, rfl⟩ := hpr
      have hi := eq_callShadow_of_shadowCall? hsh
      have hstep : (I.withProcs T).step P i s = procStep pr' dst₀ srcs₀ s := by
        obtain ⟨w, tag⟩ := i
        simp only at hi
        subst hi
        exact I.withProcs_step_callShadow T hf P dst₀ srcs₀ tag s
      rw [hstep] at h
      unfold procStep at h
      split at h
      · rename_i hlen
        obtain ⟨vs, hvs, hrun⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hrun
        have haa : procArrArgs T f = pr'.arrArgs := by simp only [procArrArgs, hf]
        refine ⟨dst₀, f, srcs₀, x, hi, rfl, fun P' tag dst' srcs' s' hl hrd => ?_⟩
        rw [I.withProcs_step_callShadow T hf P' dst' srcs' tag s', procStep,
          if_pos (hl.trans hlen), ← haa, hrd, haa, hvs, Option.bind_some, hx, Option.map_some]
      · cases h

/-- **The steps of `I.withProcs T` beyond `I` are local calls with word results** at the
    array positions of the summaries, for a table of summaries without word-array results. -/
theorem withProcs_callLocalWord (T : ProcTable) (hR : ∀ f pr, T f = some pr → pr.RetWord) :
    (I.withProcs T).CallLocalWord I (procArrArgs T) := by
  intro P i s t h
  cases hq : procCall? T i.1 with
  | none => rw [I.withProcs_step_of_none T P i s hq] at h; exact Or.inl h
  | some q =>
      obtain ⟨pr, dst, srcs⟩ := q
      right
      simp only [procCall?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨⟨dst₀, f, srcs₀⟩, hsh, pr', hf, hpr⟩ := hq
      simp only [Prod.mk.injEq] at hpr
      obtain ⟨rfl, rfl, rfl⟩ := hpr
      have hi := eq_callShadow_of_shadowCall? hsh
      have hstep : (I.withProcs T).step P i s = procStep pr' dst₀ srcs₀ s := by
        obtain ⟨w, tag⟩ := i
        simp only at hi
        subst hi
        exact I.withProcs_step_callShadow T hf P dst₀ srcs₀ tag s
      have hrw := hR f pr' hf
      rw [hstep, procStep_of_retWord hrw] at h
      split at h
      · rename_i hlen
        obtain ⟨vs, hvs, hrun⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hrun
        have haa : procArrArgs T f = pr'.arrArgs := by simp only [procArrArgs, hf]
        refine ⟨dst₀, f, srcs₀, r, hi, rfl, fun P' tag dst' srcs' s' hl hrd => ?_⟩
        rw [I.withProcs_step_callShadow T hf P' dst' srcs' tag s', procStep_of_retWord hrw,
          if_pos (hl.trans hlen), ← haa, hrd, haa, hvs, Option.bind_some, hr, Option.map_some]
      · cases h

/-- **At a table of summaries on words without word-array results, the steps of
    `I.withProcs T` beyond `I` are local calls on words with word results.** -/
theorem withProcs_callLocal_wordOnly {T : ProcTable}
    (hT : ∀ f pr, T f = some pr → pr.WordOnly) (hR : ∀ f pr, T f = some pr → pr.RetWord) :
    (I.withProcs T).CallLocalWord I (fun _ _ => none) := by
  have h : procArrArgs T = fun _ _ => none := by
    funext f
    unfold procArrArgs
    cases hf : T f with
    | none => rfl
    | some pr => exact hT f pr hf
  rw [← h]
  exact I.withProcs_callLocalWord T hR

end Isa

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
