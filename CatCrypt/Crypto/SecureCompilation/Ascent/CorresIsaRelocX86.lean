/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaReloc

/-!
# Relocation of a body at the x86 instruction set

The relocation statements of `IsaCall` (`steps_relocate`, `steps_relocate_withCalls`,
`procSpec_relocate_of_corresIsa`, `procSpec_labelled_of_corresIsa`) take the hypothesis
`StepRelocates isa fn pre B post`: the branch condition of `isa` does not read the program
counter, and the step of a non-control instruction commutes with the shift of the counter and
does not depend on the program. This module proves that hypothesis for the x86 instruction set
`x86Isa`, for every function name and every `pre`, `B` and `post`, with no condition on the
instructions of `B`.

The step `evalInstrPMemF` of `x86Isa` on an instruction that is not a control instruction
reads the registers, the arrays, the word memory and the flags of the state, writes them, and
advances the counter by one. It reads the counter nowhere, and it reads the program only in
the arms of the control instructions. The proof follows the chain of delegations of the step:
the register steps `lsemStepN`, `lsemStepSh`, `lsemStepMC` and `lsemStepCast` on the register
file, the memory step `lsemStepMem`, the flag helpers `withALUFlags`, `carryStep` and
`wideStep` on the base state, and `evalInstrPMemF` on the flag state. Each lemma states that
the step from a state with the counter set to `q` is the step from the state, followed by
setting the counter to `q + 1`.

## Main results

* `lsemStepN_setLpc`, `lsemStepSh_setLpc`, `lsemStepMC_setLpc`, `lsemStepCast_setLpc`: the
  register steps from a register file with the counter replaced.
* `lsemStepMem_setLpc`, `withALUFlags_setLpc`, `carryStep_setLpc`, `wideStep_setLpc`: the
  memory step and the flag helpers from a base state with the counter replaced.
* `evalInstrPMemF_goto`: the step of a non-control instruction on any program from a state
  with the counter set to `q` is the step on any other program from the state, followed by
  setting the counter to `q + 1`.
* `evalInstrPMemF_lpc_succ_of_not_ctl`, `evalInstrPMemF_shiftPc`: a non-control step advances
  the counter by one, and commutes with the shift of the counter.
* `decC_shiftPc`: the branch condition does not read the counter.
* `x86_stepRelocates`: `StepRelocates x86Isa fn pre B post`.
* `x86_steps_relocate`, `x86_steps_relocate_withCalls`, `x86_corresIsa_relocate_run`,
  `x86_corresIsa_relocate_run_withCalls`, `x86_procSpec_relocate_of_corresIsa`,
  `x86_procSpec_labelled_of_corresIsa`: the relocation statements at `x86Isa` without the
  hypothesis `StepRelocates`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

namespace IsaCall

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa isCall isCtl)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_step x86Isa_condEval)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (decC)

/-! ## 1. The register file -/

/-- A register read at an expected width does not read the counter. -/
theorem getW_setLpc (s : LstateN) (q : Nat) (r : String) (w : Nat) :
    LstateN.getW { s with lpc := q } r w = s.getW r w := rfl

/-- A width-tagged register read does not read the counter. -/
theorem readReg_setLpc (s : LstateN) (q : Nat) (o : LOperand) :
    readReg { s with lpc := q } o = readReg s o := by
  cases o <;> rfl

/-- The evaluation of an operand does not read the counter. -/
theorem evalOperandN_setLpc (s : LstateN) (q : Nat) (w : Nat) (o : LOperand) :
    evalOperandN { s with lpc := q } w o = evalOperandN s w o := by
  cases o <;> rfl

/-- The two-source operation with an immediate first source, from a register file with the
    counter set to `q`. -/
theorem immFirstN_setLpc (s : LstateN) (q : Nat) (dst opn : String) (n : Nat) (b : LOperand) :
    immFirstN { s with lpc := q } dst opn n b =
      (immFirstN s dst opn n b).map (fun u => { u with lpc := q + 1 }) := by
  unfold immFirstN
  rw [evalOperandN_setLpc]
  split
  · rw [Option.map_map]; rfl
  · rfl

/-- **The width-aware register step and the counter.** The step from a register file with
    the counter set to `q` is the step from the register file, followed by setting the counter
    to `q + 1`. -/
theorem lsemStepN_setLpc (i : LinstrR) (s : LstateN) (q : Nat) :
    lsemStepN i { s with lpc := q } =
      (lsemStepN i s).map (fun u => { u with lpc := q + 1 }) := by
  unfold lsemStepN
  simp only [getW_setLpc, readReg_setLpc, evalOperandN_setLpc, immFirstN_setLpc]
  repeat' split
  all_goals rfl

/-- The shift-aware register step from a register file with the counter set to `q`. -/
theorem lsemStepSh_setLpc (i : LinstrR) (s : LstateN) (q : Nat) :
    lsemStepSh i { s with lpc := q } =
      (lsemStepSh i s).map (fun u => { u with lpc := q + 1 }) := by
  unfold lsemStepSh
  simp only [readReg_setLpc, lsemStepN_setLpc]
  repeat' split
  all_goals rfl

/-- The multiply and carry register step from a register file with the counter set to
    `q`. -/
theorem lsemStepMC_setLpc (i : LinstrR) (s : LstateN) (q : Nat) :
    lsemStepMC i { s with lpc := q } =
      (lsemStepMC i s).map (fun u => { u with lpc := q + 1 }) := by
  unfold lsemStepMC
  simp only [getW_setLpc, readReg_setLpc, lsemStepSh_setLpc]
  repeat' split
  all_goals rfl

/-- The typed register step from a register file with the counter set to `q`. -/
theorem lsemStepCast_setLpc (i : LinstrRT) (s : LstateN) (q : Nat) :
    lsemStepCast i { s with lpc := q } =
      (lsemStepCast i s).map (fun u => { u with lpc := q + 1 }) := by
  unfold lsemStepCast
  simp only [readReg_setLpc, lsemStepMC_setLpc]
  repeat' split
  all_goals rfl

/-! ## 2. The base state -/

/-- The register file of a base state with the counter set to `q`. -/
theorem reg_setLpc (s : LstateM) (q : Nat) : (s.setLpc q).reg = { s.reg with lpc := q } := rfl

/-- An array read does not read the counter. -/
theorem getArr_setLpc (s : LstateM) (q : Nat) (r : String) (w n : Nat) :
    (s.setLpc q).getArr r w n = s.getArr r w n := rfl

/-- **The memory step and the counter.** The step from a base state with the counter set to
    `q` is the step from the base state, followed by setting the counter to `q + 1`. -/
theorem lsemStepMem_setLpc (i : LinstrRM) (s : LstateM) (q : Nat) :
    lsemStepMem i (s.setLpc q) = (lsemStepMem i s).map (fun b => b.setLpc (q + 1)) := by
  unfold lsemStepMem
  simp only [reg_setLpc, getArr_setLpc, getW_setLpc, lsemStepCast_setLpc]
  repeat' split
  all_goals first | rfl | (simp only [Option.map_map]; rfl)

/-- The flags an instruction writes do not depend on the counter of the pre-state, and
    writing them commutes with setting the counter of the post-state. -/
theorem withALUFlags_setLpc (i : LinstrRM) (s b : LstateM) (q q' : Nat) :
    withALUFlags i (s.setLpc q) (b.setLpc q') = (withALUFlags i s b).setLpc q' := by
  unfold withALUFlags
  simp only [reg_setLpc, evalOperandN_setLpc]
  repeat' split
  all_goals rfl

/-- The carry-family step from a base state with the counter set to `q`. -/
theorem carryStep_setLpc (op : CarryOp) (d : String) (a b : LOperand) (s : LstateM)
    (q : Nat) :
    VIR.JasminLsemMemFlagGuard.carryStep op d a b (s.setLpc q) =
      (VIR.JasminLsemMemFlagGuard.carryStep op d a b s).map (fun u => u.setLpc (q + 1)) := by
  unfold VIR.JasminLsemMemFlagGuard.carryStep
  simp only [reg_setLpc, evalOperandN_setLpc]
  repeat' split
  all_goals rfl

/-- The flag-quiet lift step from a base state with the counter set to `q`. -/
theorem wideStep_setLpc (w : WideOp) (s : LstateM) (q : Nat) :
    wideStep w (s.setLpc q) = (wideStep w s).map (fun u => u.setLpc (q + 1)) := by
  unfold wideStep
  simp only [reg_setLpc, evalOperandN_setLpc]
  repeat' split
  all_goals rfl

/-! ## 3. The flag state -/

/-- An instruction that is not a control instruction is not a flag-reading conditional. -/
theorem flagCondCC?_of_not_ctl {i : LinstrRM} (hi : isCtl i.fst = false) :
    flagCondCC? i = none := by
  unfold flagCondCC?
  split <;> simp_all [isCtl]

/-- On an instruction that is not a control instruction, the step of the labelled memref
    machine is the memory step on the base state; it does not read the program. -/
theorem evalInstrPMemL_of_not_ctl (P : LprogM) {i : LinstrRM} (hi : isCtl i.fst = false)
    (s : LstatePM) :
    evalInstrPMemL P i s = (lsemStepMem i s.base).map (fun b => { s with base := b }) := by
  unfold evalInstrPMemL
  split <;> simp_all [isCtl]

/-- **The x86 step of a non-control instruction and the counter.** For an instruction `i`
    that is not a control instruction and any two programs `P` and `P'`, the step on `P'`
    from the state `s` with the counter set to `q` is the step on `P` from `s`, followed by
    setting the counter to `q + 1`. -/
theorem evalInstrPMemF_goto (P P' : LprogM) {i : LinstrRM} (hi : isCtl i.fst = false)
    (s : LstateMF) (q : Nat) :
    evalInstrPMemF P' i (goto s q) =
      (evalInstrPMemF P i s).map (fun u => goto u (q + 1)) := by
  unfold evalInstrPMemF
  simp only [flagCondCC?_of_not_ctl hi, evalInstrPMemL_of_not_ctl _ hi, goto, reg_setLpc,
    evalOperandN_setLpc, readReg_setLpc, lsemStepMem_setLpc, carryStep_setLpc,
    wideStep_setLpc]
  cases hc : cmpArgs? i with
  | some ab =>
      simp only []
      repeat' split
      all_goals rfl
  | none =>
      simp only []
      cases hm : movRegArgs? i with
      | some ds =>
          simp only []
          repeat' split
          all_goals rfl
      | none =>
          simp only []
          cases hs : lsemStepMem i s.prog.base with
          | some b =>
              simp only [Option.map_some, withALUFlags_setLpc]
          | none =>
              simp only [Option.map_none]
              cases hk : carryArgs? i with
              | some p =>
                  simp only [Option.map_map]
                  rfl
              | none =>
                  simp only []
                  cases hw : wideArgs? i with
                  | some w =>
                      simp only [Option.map_map]
                      rfl
                  | none => rfl

/-- A successful x86 step of a non-control instruction advances the counter by one. -/
theorem evalInstrPMemF_lpc_succ_of_not_ctl (P : LprogM) {i : LinstrRM}
    (hi : isCtl i.fst = false) {s u : LstateMF} (h : evalInstrPMemF P i s = some u) :
    u.prog.base.lpc = s.prog.base.lpc + 1 := by
  have hg := evalInstrPMemF_goto P P hi s s.prog.base.lpc
  rw [goto_lpc_self, h] at hg
  have hu : u = goto u (s.prog.base.lpc + 1) := Option.some.inj hg
  rw [hu]
  rfl

/-- **The x86 step of a non-control instruction and the shift of the counter.** For an
    instruction `i` that is not a control instruction and any two programs `P` and `P'`, a
    step on `P` from `s` to `u` is a step on `P'` from `shiftPc k s` to `shiftPc k u`. -/
theorem evalInstrPMemF_shiftPc (P P' : LprogM) {i : LinstrRM} (hi : isCtl i.fst = false)
    (k : Nat) {s u : LstateMF} (h : evalInstrPMemF P i s = some u) :
    evalInstrPMemF P' i (shiftPc k s) = some (shiftPc k u) := by
  have hpc := evalInstrPMemF_lpc_succ_of_not_ctl P hi h
  unfold shiftPc
  rw [evalInstrPMemF_goto P P' hi, h, hpc]
  rfl

/-- The branch condition of the x86 instruction set does not read the counter. -/
theorem decC_shiftPc (k : Nat) (s : LstateMF) (c : LOperand) :
    decC (shiftPc k s) c = decC s c := rfl

/-! ## 4. The relocation hypothesis and the relocation statements at x86 -/

/-- **The steps of the x86 instruction set relocate.** `StepRelocates x86Isa fn pre B post`
    holds for every function name `fn` and all lists `pre`, `B` and `post`: the branch
    condition does not read the counter, and the step of a non-control instruction commutes
    with the shift of the counter and does not read the program. -/
theorem x86_stepRelocates (fn : String) (pre B post : List LinstrRM) :
    StepRelocates x86Isa fn pre B post := by
  refine ⟨fun s c => ?_, fun i _ hi s u h => ?_⟩
  · rw [x86Isa_condEval]
    exact decC_shiftPc pre.length s c
  · rw [x86Isa_step] at h ⊢
    exact evalInstrPMemF_shiftPc _ _ hi pre.length h

/-- **Relocation of a segment at x86**: `steps_relocate` at `x86Isa` without the hypothesis
    `StepRelocates`. When no label of `B` is declared in `pre`, a segment on `B` from `s` to
    `t` is a segment on `pre ++ B ++ post` with the same number of steps from
    `shiftPc pre.length s` to `shiftPc pre.length t`. -/
theorem x86_steps_relocate (fn : String) {pre B : List LinstrRM} (post : List LinstrRM)
    (hfresh : LabelsFresh pre B) {n : Nat} {s t : LstateMF}
    (h : Steps x86Isa (singletonProgM fn B) n s t) :
    Steps x86Isa (singletonProgM fn (pre ++ B ++ post)) n (shiftPc pre.length s)
      (shiftPc pre.length t) :=
  steps_relocate x86Isa fn post (x86_stepRelocates fn pre B post) hfresh h

/-- **Relocation of a segment of a body without calls at x86 with calls**:
    `steps_relocate_withCalls` at `x86Isa` without the hypothesis `StepRelocates`. -/
theorem x86_steps_relocate_withCalls (fn : String) {pre B : List LinstrRM}
    (post : List LinstrRM) (hB : ∀ i ∈ B, isCall i.fst = false) (hfresh : LabelsFresh pre B)
    {n : Nat} {s t : LstateMF} (h : Steps x86Isa (singletonProgM fn B) n s t) :
    Steps x86Isa.withCalls (singletonProgM fn (pre ++ B ++ post)) n (shiftPc pre.length s)
      (shiftPc pre.length t) :=
  steps_relocate_withCalls x86Isa fn post hB (x86_stepRelocates fn pre B post) hfresh h

section Generic

variable {A : Type}

/-- **The run of the larger program from a shifted entry state, at x86**:
    `corresIsa_relocate_run` at `x86Isa` without the hypothesis `StepRelocates`. -/
theorem x86_corresIsa_relocate_run {fn : String} {pre B : List LinstrRM}
    (post : List LinstrRM) {SR : LstateMF → A → Prop} {Pre : A → Prop} {fa : A → A}
    {fuel : Nat} (hfresh : LabelsFresh pre B)
    (h : CorresIsa x86Isa (singletonProgM fn B) SR Pre fa fuel) {m : LstateMF} {a : A}
    (hSR : SR m a) (hPre : Pre a) :
    ∃ n m', n ≤ fuel ∧
      Steps x86Isa (singletonProgM fn (pre ++ B ++ post)) n (shiftPc pre.length m)
        (shiftPc pre.length m') ∧
      Halted (singletonProgM fn B) m' ∧ SR m' (fa a) :=
  corresIsa_relocate_run x86Isa post (x86_stepRelocates fn pre B post) hfresh h hSR hPre

/-- **The run of the larger program at x86 with calls**: `corresIsa_relocate_run_withCalls`
    at `x86Isa` without the hypothesis `StepRelocates`. -/
theorem x86_corresIsa_relocate_run_withCalls {fn : String} {pre B : List LinstrRM}
    (post : List LinstrRM) {SR : LstateMF → A → Prop} {Pre : A → Prop} {fa : A → A}
    {Frame : LstateMF → LstateMF → Prop} {fuel : Nat}
    (hB : ∀ i ∈ B, isCall i.fst = false) (hfresh : LabelsFresh pre B)
    (h : CorresIsa x86Isa (singletonProgM fn B) SR Pre fa fuel)
    (hexit : ExitFrame x86Isa fn B SR Pre Frame fuel) {m : LstateMF} {a : A}
    (hSR : SR m a) (hPre : Pre a) :
    ∃ n m', n ≤ fuel ∧
      Steps x86Isa.withCalls (singletonProgM fn (pre ++ B ++ post)) n
        (shiftPc pre.length m) (shiftPc pre.length m') ∧
      atPc (singletonProgM fn (pre ++ B ++ post)) (pre.length + B.length)
        (shiftPc pre.length m') ∧
      SR m' (fa a) ∧ Frame m m' ∧ RetFrame x86Isa.sp m m' :=
  corresIsa_relocate_run_withCalls x86Isa post hB (x86_stepRelocates fn pre B post) hfresh h
    hexit hSR hPre

/-- **The procedure specification of a relocated callee at x86**:
    `procSpec_relocate_of_corresIsa` at `x86Isa` without the hypothesis `StepRelocates`. Let
    `B` contain no call and no return, correspond to `fa` at fuel `fuel` and satisfy the exit
    contract `ExitFrame`, and let no label of `B` be declared in `pre`. For every label `l`,
    the program `pre ++ B ++ Lret :: post` satisfies at `x86Isa.withCalls` the specification
    of a procedure at `l` that returns at the counter `pre.length + B.length`. -/
theorem x86_procSpec_relocate_of_corresIsa {fn : String} {pre B : List LinstrRM}
    (post : List LinstrRM) (tag : MemTag) (l : LLabel) {SR : LstateMF → A → Prop}
    {Pre : A → Prop} {fa : A → A} {Frame : LstateMF → LstateMF → Prop} {fuel : Nat}
    (hB : ∀ i ∈ B, isCall i.fst = false) (hfresh : LabelsFresh pre B)
    (h : CorresIsa x86Isa (singletonProgM fn B) SR Pre fa fuel)
    (hexit : ExitFrame x86Isa fn B SR Pre Frame fuel) :
    ProcSpec x86Isa.withCalls (singletonProgM fn (pre ++ B ++ (.Lret, tag) :: post)) l
      (pre.length + B.length) (relocRel pre.length SR) Pre fa (relocFrame pre.length Frame)
      fuel :=
  procSpec_relocate_of_corresIsa x86Isa post tag l hB (x86_stepRelocates fn pre B _) hfresh h
    hexit

/-- **The procedure specification of a labelled callee inside a larger program at x86**:
    `procSpec_labelled_of_corresIsa` at `x86Isa` without the hypothesis `StepRelocates`. The
    body `B` is placed after the declaration of the label `l` that follows `pre`; the callee
    is entered at the counter `pre.length + 1` and returns at the counter
    `pre.length + 1 + B.length`. -/
theorem x86_procSpec_labelled_of_corresIsa {fn : String} {pre B : List LinstrRM}
    (post : List LinstrRM) (kind : LabelKind) (tagl tag : MemTag) (l : LLabel)
    {SR : LstateMF → A → Prop} {Pre : A → Prop} {fa : A → A}
    {Frame : LstateMF → LstateMF → Prop} {fuel : Nat}
    (hB : ∀ i ∈ B, isCall i.fst = false)
    (hfresh : LabelsFresh (pre ++ [(.Llabel kind l, tagl)]) B)
    (h : CorresIsa x86Isa (singletonProgM fn B) SR Pre fa fuel)
    (hexit : ExitFrame x86Isa fn B SR Pre Frame fuel) :
    ProcSpec x86Isa.withCalls
      (singletonProgM fn (pre ++ [(.Llabel kind l, tagl)] ++ B ++ (.Lret, tag) :: post)) l
      (pre.length + 1 + B.length) (relocRel (pre.length + 1) SR) Pre fa
      (relocFrame (pre.length + 1) Frame) fuel :=
  procSpec_labelled_of_corresIsa x86Isa post kind tagl tag l hB
    (x86_stepRelocates fn _ B _) hfresh h hexit

end Generic

end IsaCall

end CatCrypt.Crypto.SecureCompilation.Ascent
