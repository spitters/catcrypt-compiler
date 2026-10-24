/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaRelocX86
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaNode

/-!
# The stack pointer and its cell under a body that names neither

A call step writes the stack pointer register and the memory cell it addresses
(`LprogIsa.pushRet`). The word memory of the flag machine is keyed by the name of the base
register and an integer offset, so the cell a call writes is the cell of the name of the
stack pointer at the value of the stack pointer. A body no instruction of which names the
stack pointer, as a register, as the base or the index of an indexed access or as the base of
a cell, neither reads nor writes that register and that cell: its step commutes with the
state modification `spFrame sp v w`, which sets the register `sp` to `v` and the cell of `sp`
at `v` to `w`.

The commutation gives, from a correspondence of the body on a relation `SR`, the
correspondence on the relation `spRel sp SR` (a state related by `SR` with the stack pointer
and its cell replaced), the exit contract `IsaCall.ExitFrame` on that relation, and the
procedure specification of the body placed after a label and followed by a return. The entry
relation of that specification holds at the state after a call step from a caller whose
state apart from the stack pointer is related by `SR`.

The condition `SpFree sp i` on an instruction excludes the name `sp` from the names the
step reads (`JasminLsemAddrCongr.readsI`, which counts the base of a cell name
`mem.<sp>.<off>` as a read of `sp`), from the names it writes
(`JasminLsemStepFrame.dstNames`), from the base of a compile-time-offset load or store and
from the operand of a conditional jump. `spFreeB` decides it on the operands.

## Main results

* `spFrame`, `SpFree`, `spFreeB`, `spFree_of_spFreeB`: the state modification, the condition
  on an instruction and its Boolean check.
* `fstepF_setReg`, `fstepF_storeMemC`, `fstepF_spM`: the straight step of the flag machine
  commutes with a write of the register, of the cell, and of both.
* `x86_step_spFrame`, `x86_lsemStepPMemF_spFrame`, `x86_lsemFuelMemF_spFrame`,
  `x86_steps_spFrame`: the step, the fetched step, the run and a segment of `x86Isa` commute
  with `spFrame`.
* `lsemFuelMemF_atPc_length`, `x86_lsemFuelMemF_atPc_length`: a run from a counter within
  the body halts at the counter after the last instruction.
* `spRel`, `SpFrameRun`, `x86_corresIsa_spRel`, `x86_exitFrame_of_spFree`: the relation with
  a replaced stack pointer, the correspondence on it and the exit contract.
* `x86_procSpec_of_body_judgement`: the procedure specification of a labelled body followed
  by a return, from the correspondence of the body at its own entry relation.
* `spRel_callEntry`: the entry relation of that specification holds after a call step.
* `phaseSR_entry_bound`, `x86_procSpec_of_image_judgement`, `phaseSR_spRel_callEntry`: the
  specification and its entry relation after a call step for a judgement on the two-phase
  relation `phaseSR`, with the conditions on the body as Boolean checks.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

namespace IsaCall

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (fstepF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames fstepF_frame_dst)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (readsI srcNames cellBase
  NAgree MAgree ORel fstepF_congr)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa isCall isCtl ctlStep retAddr pushRet)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_step x86Isa_condEval)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (decC ccPol)

/-! ## 1. The state modification and the condition on an instruction -/

/-- The base state `s` with the register `sp` holding `v` and the memory cell of `sp` at `v`
    holding `w`. -/
def spM (sp : String) (v w : BitVec 64) (s : LstateM) : LstateM :=
  (s.storeMemC sp v.toInt w).setReg sp v

/-- **The stack pointer and its cell replaced.** The state `s` with the register `sp` holding
    `v` and the memory cell of `sp` at `v` holding `w`; the counter, the function name, every
    other register, the arrays, every other memory cell and the flags are those of `s`. -/
def spFrame (sp : String) (v w : BitVec 64) (s : LstateMF) : LstateMF :=
  { s with prog := { s.prog with base := spM sp v w s.prog.base } }

/-- The state with the return address pushed is the state with the stack pointer and its
    cell replaced. -/
theorem pushRet_eq_spFrame (sp : String) (v : BitVec 64) (s : LstateMF) :
    pushRet sp v s = spFrame sp (v - 8) (retAddr s) s := rfl

/-- **An instruction that does not name `sp`.** The step of the instruction does not read the
    name `sp`, does not write it, addresses no memory cell of the base `sp` at a compile-time
    offset, and is no conditional jump on the register `sp`. -/
structure SpFree (sp : String) (i : LinstrR) : Prop where
  /-- The step does not read the name `sp`. -/
  reads : ¬ readsI i sp
  /-- The step does not write the name `sp`. -/
  writes : sp ∉ dstNames i
  /-- A compile-time-offset load is not at the base `sp`. -/
  loadC : ∀ d b off, loadCStruct? i = some (d, b, off) → b ≠ sp
  /-- A compile-time-offset store is not at the base `sp`. -/
  storeC : ∀ b off x, storeCStruct? i = some (b, off, x) → b ≠ sp
  /-- The instruction is no conditional jump on the register `sp`. -/
  cond : ∀ l, i ≠ .Lcond (.reg sp) l

/-- The operand names `sp`: as a register, as the base of a cell name `mem.<sp>.<off>`, as
    the base of an array element, or as the base or the index of an indexed element. -/
def opSpB (sp : String) : LOperand → Bool
  | .reg r => r == sp || cellBase (.reg r) == some sp
  | .arr b _ => b == sp
  | .arrIdx b i _ => b == sp || i == sp
  | .imm _ => false

/-- **The Boolean check of `SpFree`**: `sp` is neither the empty name nor `RDX`, no operand
    of an `Lopn` names `sp`, and the operand of a conditional jump does not name `sp`. -/
def spFreeB (sp : String) (i : LinstrR) : Bool :=
  sp != "" && sp != "RDX" &&
    match i with
    | .Lopn ds _ ss => !(ds ++ ss).any (opSpB sp)
    | .Lcond c _ => !opSpB sp c
    | _ => true

/-- The Boolean check `spFreeB` is sound for `SpFree`. -/
theorem spFree_of_spFreeB {sp : String} {i : LinstrR} (h : spFreeB sp i = true) :
    SpFree sp i := by
  simp only [spFreeB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  cases i with
  | Lopn ds o ss =>
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at h3
      refine ⟨?_, ?_, ?_, ?_, fun l he => by cases he⟩
      · rintro (he | ⟨he, -⟩ | he | he)
        · exact h1 he
        · exact h2 he
        · obtain ⟨x, hx, hr⟩ := List.mem_flatMap.1 he
          have := h3 x (List.mem_append_right _ hx)
          cases x <;> simp_all [srcNames, opSpB]
          rcases hr with rfl | rfl <;> simp_all
        · obtain ⟨x, hx, hr⟩ := List.mem_filterMap.1 he
          have := h3 x hx
          cases x <;> simp_all [cellBase, opSpB]
      · intro he
        obtain ⟨x, hx, hr⟩ := List.mem_flatMap.1 he
        have := h3 x (List.mem_append_left _ hx)
        cases x <;> simp_all [opNames, opSpB]
        rcases hr with rfl | rfl <;> simp_all
      · intro d b off hl he
        unfold loadCStruct? at hl
        split at hl
        · split at hl
          · cases hl
            rename_i heq
            cases heq
            have := h3 (.arr b off) (by simp)
            simp [opSpB, he] at this
          · cases hl
        · cases hl
      · intro b off x hl he
        unfold storeCStruct? at hl
        split at hl
        · split at hl
          · cases hl
            rename_i heq
            cases heq
            have := h3 (.arr b off) (by simp)
            simp [opSpB, he] at this
          · cases hl
        · cases hl
  | Lcond c l =>
      refine ⟨?_, by simp [dstNames], by simp [loadCStruct?], by simp [storeCStruct?], ?_⟩
      · rintro (he | ⟨he, -⟩ | he)
        · exact h1 he
        · exact h2 he
        · exact he
      · intro l' he
        cases he
        simp [opSpB] at h3
  | _ =>
      refine ⟨?_, by simp [dstNames], by simp [loadCStruct?], by simp [storeCStruct?],
        fun l he => by cases he⟩
      rintro (he | ⟨he, -⟩ | he)
      · exact h1 he
      · exact h2 he
      · exact he

/-- The Boolean check of `SpFree` on every instruction of a body. -/
def spFreeBodyB (sp : String) (B : List LinstrRM) : Bool := B.all fun i => spFreeB sp i.fst

/-- The Boolean check `spFreeBodyB` is sound: no instruction of the body names `sp`. -/
theorem spFree_of_spFreeBodyB {sp : String} {B : List LinstrRM}
    (h : spFreeBodyB sp B = true) : ∀ i ∈ B, SpFree sp i.fst := fun i hi =>
  spFree_of_spFreeB (List.all_eq_true.1 h i hi)

/-! ## 2. The straight step and the register -/

/-- Two base states with equal components are equal. -/
theorem lstateM_ext {s t : LstateM} (h1 : s.reg.lvm = t.reg.lvm) (h2 : s.reg.lpc = t.reg.lpc)
    (h3 : s.larr = t.larr) (h4 : s.lmem = t.lmem) (h5 : s.cf = t.cf) (h6 : s.of = t.of) :
    s = t := by
  obtain ⟨⟨_, _⟩, _, _, _, _⟩ := s
  obtain ⟨⟨_, _⟩, _, _, _, _⟩ := t
  dsimp only at h1 h2 h3 h4 h5 h6
  subst_vars
  rfl

/-- **The straight step and a register it does not name.** When the step of `i` neither
    reads nor writes the name `sp`, the step from the state with `sp` set to `v` is the step
    from the state, followed by setting `sp` to `v`. -/
theorem fstepF_setReg {sp : String} {i : LinstrRM} (hr : ¬ readsI i.fst sp)
    (hw : sp ∉ dstNames i.fst) (s : LstateM) (zf : Bool) {n : Nat} (v : BitVec n) :
    fstepF i (s.setReg sp v) zf = (fstepF i s zf).map (fun p => (p.1.setReg sp v, p.2)) := by
  have hag : MAgree (readsI i.fst) s (s.setReg sp v) :=
    ⟨⟨rfl, fun r hr' => by
      have hne : r ≠ sp := fun h => hr (h ▸ hr')
      simp [LstateM.setReg, LstateN.setReg, hne]⟩, rfl, rfl, rfl, rfl⟩
  have hc := fstepF_congr i hag zf
  cases hs : fstepF i s zf with
  | none =>
      rw [hs] at hc
      cases ht : fstepF i (s.setReg sp v) zf with
      | none => rfl
      | some b => rw [ht] at hc; cases hc
  | some a =>
      rw [hs] at hc
      cases ht : fstepF i (s.setReg sp v) zf with
      | none => rw [ht] at hc; cases hc
      | some b =>
          rw [ht] at hc
          obtain ⟨a1, az⟩ := a
          obtain ⟨b1, bz⟩ := b
          cases hc with
          | some hab =>
              obtain ⟨⟨⟨hpc, hreg⟩, harr, hmem, hcf, hof⟩, hz⟩ := hab
              have hfr := (fstepF_frame_dst ht hw).1
              refine congrArg some (Prod.ext
                (lstateM_ext ?_ hpc.symm harr.symm hmem.symm hcf.symm hof.symm) hz.symm)
              funext r
              by_cases hrs : r = sp
              · subst hrs
                rw [hfr]
                simp [LstateM.setReg, LstateN.setReg]
              · have e1 : (a1.setReg sp v).reg.lvm r = a1.reg.lvm r := by
                  simp [LstateM.setReg, LstateN.setReg, hrs]
                have e2 : (s.setReg sp v).reg.lvm r = s.reg.lvm r := by
                  simp [LstateM.setReg, LstateN.setReg, hrs]
                rw [e1]
                rcases hreg r with h | ⟨h1, h2⟩
                · exact h.symm
                · exact h2.trans (e2.trans h1.symm)

/-! ## 3. The straight step and the memory cell -/

/-- An array read does not read the word memory. -/
theorem getArr_storeMemC (s : LstateM) (b : String) (o : Int) (x : BitVec 64) (r : String)
    (w n : Nat) : (s.storeMemC b o x).getArr r w n = s.getArr r w n := rfl

/-- Two writes of the word memory at different bases commute. -/
theorem storeMemC_comm (s : LstateM) {b b' : String} (h : b ≠ b') (o o' : Int)
    (x x' : BitVec 64) :
    (s.storeMemC b o x).storeMemC b' o' x' = (s.storeMemC b' o' x').storeMemC b o x := by
  refine lstateM_ext rfl rfl rfl ?_ rfl rfl
  funext c k
  simp only [LstateM.storeMemC]
  split_ifs <;> simp_all

/-- **The memory step and a memory cell it does not address.** When no compile-time-offset
    load or store of `i` is at the base `sp`, the step from the state with a cell of `sp`
    written is the step from the state, followed by the write. -/
theorem lsemStepMem_storeMemC {sp : String} {i : LinstrRM}
    (hl : ∀ d b off, loadCStruct? i.fst = some (d, b, off) → b ≠ sp)
    (hs : ∀ b off x, storeCStruct? i.fst = some (b, off, x) → b ≠ sp)
    (s : LstateM) (o : Int) (x : BitVec 64) :
    lsemStepMem i (s.storeMemC sp o x) =
      (lsemStepMem i s).map (fun u => u.storeMemC sp o x) := by
  unfold lsemStepMem
  simp only [LstateM.reg_storeMemC, getArr_storeMemC]
  repeat' split
  all_goals first
    | rfl
    | (simp only [Option.map_map]; rfl)
    | (have hne := hl _ _ _ (by assumption)
       simp only [Option.map_some, LstateM.storeMemC, hne, false_and, ite_false]
       rfl)
    | (have hne := hs _ _ _ (by assumption)
       simp only [Option.map_some]
       exact congrArg (fun u : LstateM => some u.nextPc) (storeMemC_comm s (Ne.symm hne) _ _ _ _))

/-- The flags an instruction writes do not depend on the word memory, and writing them
    commutes with a write of the word memory. -/
theorem withALUFlags_storeMemC (i : LinstrRM) (s b : LstateM) (sp : String) (o : Int)
    (x : BitVec 64) :
    withALUFlags i (s.storeMemC sp o x) (b.storeMemC sp o x) =
      (withALUFlags i s b).storeMemC sp o x := by
  unfold withALUFlags
  simp only [LstateM.reg_storeMemC]
  repeat' split
  all_goals rfl

/-- The carry-family step from a state with a memory cell written. -/
theorem carryStep_storeMemC (op : CarryOp) (d : String) (a b : LOperand) (s : LstateM)
    (sp : String) (o : Int) (x : BitVec 64) :
    VIR.JasminLsemMemFlagGuard.carryStep op d a b (s.storeMemC sp o x) =
      (VIR.JasminLsemMemFlagGuard.carryStep op d a b s).map
        (fun u => u.storeMemC sp o x) := by
  unfold VIR.JasminLsemMemFlagGuard.carryStep
  simp only [LstateM.reg_storeMemC]
  repeat' split
  all_goals rfl

/-- The flag-quiet lift step from a state with a memory cell written. -/
theorem wideStep_storeMemC (wo : WideOp) (s : LstateM) (sp : String) (o : Int)
    (x : BitVec 64) :
    wideStep wo (s.storeMemC sp o x) = (wideStep wo s).map (fun u => u.storeMemC sp o x) := by
  unfold wideStep
  simp only [LstateM.reg_storeMemC]
  repeat' split
  all_goals rfl

/-- The straight step on the base state from a state with a memory cell of `sp` written,
    when no compile-time-offset load or store of `i` is at the base `sp`. -/
theorem stepMemF_storeMemC {sp : String} {i : LinstrRM}
    (hl : ∀ d b off, loadCStruct? i.fst = some (d, b, off) → b ≠ sp)
    (hs : ∀ b off x, storeCStruct? i.fst = some (b, off, x) → b ≠ sp)
    (s : LstateM) (o : Int) (x : BitVec 64) :
    stepMemF i (s.storeMemC sp o x) = (stepMemF i s).map (fun u => u.storeMemC sp o x) := by
  unfold stepMemF
  rw [lsemStepMem_storeMemC hl hs]
  cases hm : lsemStepMem i s with
  | some b => simp only [Option.map_some, withALUFlags_storeMemC]
  | none =>
      simp only [Option.map_none]
      cases hk : carryArgs? i with
      | some p =>
          obtain ⟨op, d, a, b⟩ := p
          simp only [carryStep_storeMemC]
      | none =>
          simp only []
          cases hw : wideArgs? i with
          | some wo => simp only [wideStep_storeMemC]
          | none => rfl

/-- **The straight step and a memory cell it does not address.** When no compile-time-offset
    load or store of `i` is at the base `sp`, the step from the state with a cell of `sp`
    written is the step from the state, followed by the write. -/
theorem fstepF_storeMemC {sp : String} {i : LinstrRM}
    (hl : ∀ d b off, loadCStruct? i.fst = some (d, b, off) → b ≠ sp)
    (hs : ∀ b off x, storeCStruct? i.fst = some (b, off, x) → b ≠ sp)
    (s : LstateM) (zf : Bool) (o : Int) (x : BitVec 64) :
    fstepF i (s.storeMemC sp o x) zf =
      (fstepF i s zf).map (fun p => (p.1.storeMemC sp o x, p.2)) := by
  unfold fstepF
  simp only [LstateM.reg_storeMemC, stepMemF_storeMemC hl hs]
  repeat' split
  all_goals first | rfl | (simp only [Option.map_map]; rfl)

/-- **The straight step and the stack pointer with its cell.** For an instruction that does
    not name `sp`, the step from the state with `sp` and its cell replaced is the step from
    the state, followed by the replacement. -/
theorem fstepF_spM {sp : String} {i : LinstrRM} (h : SpFree sp i.fst) (v w : BitVec 64)
    (s : LstateM) (zf : Bool) :
    fstepF i (spM sp v w s) zf = (fstepF i s zf).map (fun p => (spM sp v w p.1, p.2)) := by
  unfold spM
  rw [fstepF_setReg h.reads h.writes, fstepF_storeMemC h.loadC h.storeC, Option.map_map]
  rfl

/-! ## 4. The step, the run and a segment of the x86 instruction set -/

/-- **The x86 step of a non-control instruction is the straight step.** On an instruction
    that is not a control instruction, the step of the flag machine is `fstepF` on the base
    state; the function name is unchanged. -/
theorem evalInstrPMemF_eq_fstepF_of_not_ctl (P : LprogM) {i : LinstrRM}
    (hi : isCtl i.fst = false) (s : LstateMF) :
    evalInstrPMemF P i s =
      (fstepF i s.prog.base s.zf).map
        (fun bz => { prog := { s.prog with base := bz.1 }, zf := bz.2 }) := by
  unfold evalInstrPMemF fstepF stepMemF
  cases hc : cmpArgs? i with
  | some ab =>
      obtain ⟨a, b⟩ := ab
      simp only []
      cases ha : evalOperandN s.prog.base.reg 64 a with
      | none => cases hb : evalOperandN s.prog.base.reg 64 b <;> rfl
      | some va =>
          cases hb : evalOperandN s.prog.base.reg 64 b with
          | none => rfl
          | some vb => rfl
  | none =>
      simp only []
      cases hm : movRegArgs? i with
      | some ds =>
          obtain ⟨dst, src⟩ := ds
          simp only []
          cases hr : readReg s.prog.base.reg (.reg src) with
          | none => rfl
          | some wv => obtain ⟨w, v⟩ := wv; rfl
      | none =>
          simp only [flagCondCC?_of_not_ctl hi]
          rw [evalInstrPMemL_of_not_ctl P hi]
          cases lsemStepMem i s.prog.base with
          | some b => rfl
          | none =>
              simp only [Option.map_none]
              cases carryArgs? i with
              | none =>
                  cases wideArgs? i with
                  | none => rfl
                  | some w =>
                      simp only []
                      cases wideStep w s.prog.base <;> rfl
              | some q =>
                  obtain ⟨op, d, a, b⟩ := q
                  simp only []
                  cases VIR.JasminLsemMemFlagGuard.carryStep op d a b s.prog.base <;> rfl

/-- The branch condition of the x86 instruction set on an operand other than the register
    `sp` does not read `sp` and its cell. -/
theorem decC_spFrame {sp : String} (v w : BitVec 64) (s : LstateMF) {c : LOperand}
    (hc : c ≠ .reg sp) : decC (spFrame sp v w s) c = decC s c := by
  unfold decC
  cases ccPol c with
  | some pol => rfl
  | none =>
      show condNZ (spM sp v w s.prog.base) c = condNZ s.prog.base c
      unfold condNZ
      have he : evalOperandN (spM sp v w s.prog.base).reg 64 c =
          evalOperandN s.prog.base.reg 64 c := by
        cases c with
        | reg r =>
            exact LstateN.getW_setReg_other _ sp r v 64 (fun h => hc (by rw [h]))
        | _ => rfl
      rw [he]

/-- **The x86 step commutes with the replacement of the stack pointer and its cell.** For an
    instruction that does not name `sp` and every program `P`, the step from `spFrame sp v w s`
    is the step from `s`, followed by `spFrame sp v w`. -/
theorem x86_step_spFrame (P : LprogM) {sp : String} {i : LinstrRM} (h : SpFree sp i.fst)
    (v w : BitVec 64) (s : LstateMF) :
    x86Isa.step P i (spFrame sp v w s) = (x86Isa.step P i s).map (spFrame sp v w) := by
  by_cases hc : isCtl i.fst = true
  · rw [x86Isa.step_ctl P i _ hc, x86Isa.step_ctl P i _ hc, x86Isa_condEval]
    obtain ⟨wi, t⟩ := i
    cases wi with
    | Llabel k l => rfl
    | Lcond c l =>
        have hcc : c ≠ .reg sp := fun he => h.cond l (by rw [he])
        simp only [ctlStep, decC_spFrame v w s hcc]
        split
        · unfold evalJumpMem
          cases findLabelMem l P.body <;> rfl
        · rfl
    | Lgoto tgt =>
        obtain ⟨f, l⟩ := tgt
        simp only [ctlStep]
        split
        · unfold evalJumpMem
          cases findLabelMem l P.body <;> rfl
        · rfl
    | _ => simp [isCtl] at hc
  · have hn : isCtl i.fst = false := by simpa using hc
    rw [x86Isa_step, evalInstrPMemF_eq_fstepF_of_not_ctl P hn,
      evalInstrPMemF_eq_fstepF_of_not_ctl P hn]
    show (fstepF i (spM sp v w s.prog.base) s.zf).map _ = _
    rw [fstepF_spM h, Option.map_map, Option.map_map]
    rfl

/-- The fetch does not read the stack pointer and its cell. -/
theorem findInstrMem_spFrame (P : LprogM) (sp : String) (v w : BitVec 64) (s : LstateMF) :
    findInstrMem P (spFrame sp v w s).prog = findInstrMem P s.prog := rfl

/-- An instruction the fetch returns is an instruction of the body. -/
theorem mem_of_findInstrMem {P : LprogM} {p : LstatePM} {i : LinstrRM}
    (h : findInstrMem P p = some i) : i ∈ P.body := by
  unfold findInstrMem at h
  split at h
  · exact List.mem_of_getElem? h
  · cases h

/-- **The fetched x86 step commutes with the replacement of the stack pointer and its
    cell**, on a program no instruction of which names `sp`. -/
theorem x86_lsemStepPMemF_spFrame {P : LprogM} {sp : String}
    (hP : ∀ i ∈ P.body, SpFree sp i.fst) (v w : BitVec 64) (s : LstateMF) :
    x86Isa.lsemStepPMemF P (spFrame sp v w s) =
      (x86Isa.lsemStepPMemF P s).map (spFrame sp v w) := by
  cases hf : findInstrMem P s.prog with
  | none => simp only [Isa.lsemStepPMemF, findInstrMem_spFrame, hf, Option.map_none]
  | some i =>
      simp only [Isa.lsemStepPMemF, findInstrMem_spFrame, hf]
      exact x86_step_spFrame P (hP i (mem_of_findInstrMem hf)) v w s

/-- **The x86 run commutes with the replacement of the stack pointer and its cell.** On a
    program no instruction of which names `sp`, the run at fuel `k` from `spFrame sp v w s`
    is the run from `s`, followed by `spFrame sp v w`. -/
theorem x86_lsemFuelMemF_spFrame {P : LprogM} {sp : String}
    (hP : ∀ i ∈ P.body, SpFree sp i.fst) (v w : BitVec 64) :
    ∀ (k : Nat) (s : LstateMF), x86Isa.lsemFuelMemF P k (spFrame sp v w s) =
      (x86Isa.lsemFuelMemF P k s).map (spFrame sp v w)
  | 0, s => by
      cases hf : findInstrMem P s.prog <;>
        simp [Isa.lsemFuelMemF, findInstrMem_spFrame, hf]
  | k + 1, s => by
      cases hf : findInstrMem P s.prog with
      | none =>
          rw [x86Isa.lsemFuelMemF_halt P _ s hf,
            x86Isa.lsemFuelMemF_halt P _ _ ((findInstrMem_spFrame P sp v w s).trans hf)]
          rfl
      | some i =>
          have hstep := x86_step_spFrame P (hP i (mem_of_findInstrMem hf)) v w s
          cases hs : x86Isa.step P i s with
          | none =>
              rw [hs] at hstep
              simp [Isa.lsemFuelMemF, findInstrMem_spFrame, hf, hs, hstep]
          | some u =>
              rw [hs] at hstep
              rw [x86Isa.lsemFuelMemF_step P k i s u hf hs,
                x86Isa.lsemFuelMemF_step P k i _ _
                  ((findInstrMem_spFrame P sp v w s).trans hf) hstep]
              exact x86_lsemFuelMemF_spFrame hP v w k u

/-- **A segment of the x86 instruction set under the replacement of the stack pointer and
    its cell.** On a program no instruction of which names `sp`, a segment from `s` to `t`
    is a segment with the same number of steps from `spFrame sp v w s` to
    `spFrame sp v w t`. -/
theorem x86_steps_spFrame {P : LprogM} {sp : String} (hP : ∀ i ∈ P.body, SpFree sp i.fst)
    (v w : BitVec 64) {n : Nat} {s t : LstateMF} (h : Steps x86Isa P n s t) :
    Steps x86Isa P n (spFrame sp v w s) (spFrame sp v w t) :=
  steps_of_step_sim x86Isa x86Isa (spFrame sp v w)
    (fun s u hu => by rw [x86_lsemStepPMemF_spFrame hP, hu]; rfl) h

/-! ## 5. The counter at the end of a run -/

/-- A jump stays in the function and lands within the body or at its end. -/
theorem evalJumpMem_lpc_le {P : LprogM} {l : LLabel} {p p' : LstatePM}
    (h : evalJumpMem P l p = some p') : p'.lfn = p.lfn ∧ p'.base.lpc ≤ P.body.length := by
  unfold evalJumpMem at h
  split at h
  · rename_i pc hpc
    cases h
    have hlt := VIR.JasminLsemLabeled.findLabel_lt_length l _ pc hpc
    rw [List.length_map] at hlt
    exact ⟨rfl, hlt⟩
  · cases h

/-- **One step stays within the body.** Let every step of a non-control instruction of `B`
    keep the function name and advance the counter by one. A step of `isa` on `B` from a
    state at which an instruction is fetched keeps the function name and reaches a counter
    at most the length of `B`. -/
theorem step_lpc_le (isa : Isa) {fn : String} {B : List LinstrRM}
    (hstep : ∀ i ∈ B, isCtl i.fst = false → ∀ s u,
      isa.step (singletonProgM fn B) i s = some u →
        u.prog.lfn = s.prog.lfn ∧ u.prog.base.lpc = s.prog.base.lpc + 1)
    {i : LinstrRM} {s u : LstateMF}
    (hf : findInstrMem (singletonProgM fn B) s.prog = some i)
    (hs : isa.step (singletonProgM fn B) i s = some u) :
    u.prog.lfn = s.prog.lfn ∧ u.prog.base.lpc ≤ B.length := by
  have hi : i ∈ B := mem_of_findInstrMem hf
  have hlt : s.prog.base.lpc < B.length := by
    unfold findInstrMem at hf
    split at hf
    · exact (List.getElem?_eq_some_iff.1 hf).1
    · cases hf
  by_cases hc : isCtl i.fst = true
  · rw [isa.step_ctl _ i s hc] at hs
    obtain ⟨wi, t⟩ := i
    cases wi with
    | Llabel k l =>
        cases hs
        exact ⟨rfl, hlt⟩
    | Lcond c l =>
        simp only [ctlStep] at hs
        split at hs
        · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hs
          exact evalJumpMem_lpc_le hp
        · cases hs
          exact ⟨rfl, hlt⟩
    | Lgoto tgt =>
        obtain ⟨f, l⟩ := tgt
        simp only [ctlStep] at hs
        split at hs
        · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hs
          exact evalJumpMem_lpc_le hp
        · cases hs
    | _ => simp [isCtl] at hc
  · obtain ⟨h1, h2⟩ := hstep i hi (by simpa using hc) s u hs
    exact ⟨h1, by rw [h2]; exact hlt⟩

/-- **A run ends at the counter after the last instruction.** Let every step of a
    non-control instruction of `B` keep the function name and advance the counter by one. A
    run of `isa` on `B` from a state in the function `fn` at a counter at most the length of
    `B` returns a state in `fn` at the counter `B.length`. -/
theorem lsemFuelMemF_atPc_length (isa : Isa) {fn : String} {B : List LinstrRM}
    (hstep : ∀ i ∈ B, isCtl i.fst = false → ∀ s u,
      isa.step (singletonProgM fn B) i s = some u →
        u.prog.lfn = s.prog.lfn ∧ u.prog.base.lpc = s.prog.base.lpc + 1) :
    ∀ (k : Nat) (m m' : LstateMF), isa.lsemFuelMemF (singletonProgM fn B) k m = some m' →
      m.prog.lfn = fn → m.prog.base.lpc ≤ B.length → atPc (singletonProgM fn B) B.length m' := by
  have hhalt : ∀ m : LstateMF, findInstrMem (singletonProgM fn B) m.prog = none →
      m.prog.lfn = fn → m.prog.base.lpc ≤ B.length → atPc (singletonProgM fn B) B.length m := by
    intro m hf hfn hpc
    refine ⟨hfn, ?_⟩
    unfold findInstrMem at hf
    rw [ite_eq_left (show m.prog.lfn = (singletonProgM fn B).lfn from hfn)] at hf
    exact Nat.le_antisymm hpc (List.getElem?_eq_none_iff.1 hf)
  intro k
  induction k with
  | zero =>
      intro m m' h hfn hpc
      cases hf : findInstrMem (singletonProgM fn B) m.prog with
      | none =>
          rw [isa.lsemFuelMemF_halt _ 0 m hf] at h
          cases h
          exact hhalt m hf hfn hpc
      | some i => simp [Isa.lsemFuelMemF, hf] at h
  | succ k ih =>
      intro m m' h hfn hpc
      cases hf : findInstrMem (singletonProgM fn B) m.prog with
      | none =>
          rw [isa.lsemFuelMemF_halt _ _ m hf] at h
          cases h
          exact hhalt m hf hfn hpc
      | some i =>
          cases hs : isa.step (singletonProgM fn B) i m with
          | none => simp [Isa.lsemFuelMemF, hf, hs] at h
          | some u =>
              rw [isa.lsemFuelMemF_step _ k i m u hf hs] at h
              obtain ⟨hl, hp⟩ := step_lpc_le isa hstep hf hs
              exact ih u m' h (hl.trans hfn) hp

/-- **A run of the x86 instruction set ends at the counter after the last instruction.** A
    run of `x86Isa` on `B` from a state in the function `fn` at a counter at most the length
    of `B` returns a state in `fn` at the counter `B.length`, for every body `B`. -/
theorem x86_lsemFuelMemF_atPc_length {fn : String} {B : List LinstrRM} {k : Nat}
    {m m' : LstateMF} (h : x86Isa.lsemFuelMemF (singletonProgM fn B) k m = some m')
    (hfn : m.prog.lfn = fn) (hpc : m.prog.base.lpc ≤ B.length) :
    atPc (singletonProgM fn B) B.length m' := by
  refine lsemFuelMemF_atPc_length x86Isa (fun i _ hi s u hs => ?_) k m m' h hfn hpc
  rw [x86Isa_step] at hs
  refine ⟨?_, evalInstrPMemF_lpc_succ_of_not_ctl _ hi hs⟩
  rw [evalInstrPMemF_eq_fstepF_of_not_ctl _ hi] at hs
  obtain ⟨bz, -, rfl⟩ := Option.map_eq_some_iff.1 hs
  rfl

/-! ## 6. The relation with a replaced stack pointer, and the exit contract -/

section Generic

variable {A : Type}

/-- **The relation `SR` up to the stack pointer and its cell.** The state is a state related
    by `SR` with the register `sp` and the memory cell it addresses replaced. -/
def spRel (sp : String) (SR : LstateMF → A → Prop) : LstateMF → A → Prop :=
  fun m a => ∃ (v w : BitVec 64) (m₀ : LstateMF), m = spFrame sp v w m₀ ∧ SR m₀ a

/-- **The frame of a run up to the stack pointer and its cell.** The two states are the
    entry and end states of a run of `isa` on `P` at fuel `fuel`, both with the register
    `sp` holding the same word and the memory cell it addresses holding the same word. -/
def SpFrameRun (sp : String) (isa : Isa) (P : LprogM) (fuel : Nat) :
    LstateMF → LstateMF → Prop :=
  fun m m' => ∃ (v w : BitVec 64) (m₀ t₀ : LstateMF),
    m = spFrame sp v w m₀ ∧ m' = spFrame sp v w t₀ ∧ isa.lsemFuelMemF P fuel m₀ = some t₀

/-- Two states with the stack pointer and its cell replaced by the same words satisfy the
    return address contract. -/
theorem retFrame_spFrame (sp : String) (v w : BitVec 64) (m t : LstateMF) :
    RetFrame sp (spFrame sp v w m) (spFrame sp v w t) := by
  intro v' hv
  have h1 : ∀ u : LstateMF, (spFrame sp v w u).prog.base.reg.getW sp 64 = some v :=
    fun u => LstateN.getW_setReg_same _ sp v
  rw [h1 m] at hv
  cases hv
  refine ⟨h1 t, ?_⟩
  simp [spFrame, spM, LstateM.storeMemC]

/-- **The correspondence up to the stack pointer and its cell.** A body no instruction of
    which names `RSP`, and that corresponds to `fa` on the relation `SR`, corresponds to `fa`
    at the same fuel on `spRel "RSP" SR`. -/
theorem x86_corresIsa_spRel {P : LprogM} {SR : LstateMF → A → Prop} {Pre : A → Prop}
    {fa : A → A} {fuel : Nat} (hP : ∀ i ∈ P.body, SpFree "RSP" i.fst)
    (h : CorresIsa x86Isa P SR Pre fa fuel) :
    CorresIsa x86Isa P (spRel "RSP" SR) Pre fa fuel := by
  rintro m a ⟨v, w, m₀, rfl, hSR⟩ hPre
  obtain ⟨t, hrun, hSR'⟩ := h m₀ a hSR hPre
  exact ⟨spFrame "RSP" v w t, by rw [x86_lsemFuelMemF_spFrame hP, hrun]; rfl,
    v, w, t, rfl, hSR'⟩

/-- **The exit contract of a body that does not name the stack pointer.** Let no instruction
    of `B` name `RSP`, and let every state related by `SR` under `Pre` be in the function
    `fn` at a counter at most the length of `B`. Every run of `B` from a state related by
    `spRel "RSP" SR` halts at the counter `B.length`, its entry and end states are the entry
    and end states of a run with the stack pointer and its cell replaced (`SpFrameRun`), and
    they satisfy the return address contract. -/
theorem x86_exitFrame_of_spFree {fn : String} {B : List LinstrRM} {SR : LstateMF → A → Prop}
    {Pre : A → Prop} {fuel : Nat} (hP : ∀ i ∈ B, SpFree "RSP" i.fst)
    (hentry : ∀ m a, SR m a → Pre a → m.prog.lfn = fn ∧ m.prog.base.lpc ≤ B.length) :
    ExitFrame x86Isa fn B (spRel "RSP" SR) Pre
      (SpFrameRun "RSP" x86Isa (singletonProgM fn B) fuel) fuel := by
  rintro m a m' ⟨v, w, m₀, rfl, hSR⟩ hPre hrun
  rw [x86_lsemFuelMemF_spFrame (P := singletonProgM fn B) hP] at hrun
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 hrun
  obtain ⟨hfn, hpc⟩ := hentry m₀ a hSR hPre
  obtain ⟨h1, h2⟩ := x86_lsemFuelMemF_atPc_length ht hfn hpc
  exact ⟨⟨h1, h2⟩, ⟨v, w, m₀, t, rfl, rfl, ht⟩, retFrame_spFrame "RSP" v w m₀ t⟩

/-- **The procedure specification of a labelled body, from the correspondence of the body
    at its own entry relation.** Let `B` contain no call and no return and name `RSP` in no
    instruction, let no label of `B` be declared in `pre` or be `l`, let `B` correspond to
    `fa` at fuel `fuel` on the relation `SR`, and let every state related by `SR` under `Pre`
    be in the function `fn` at a counter at most the length of `B`. The program
    `pre ++ Llabel l :: B ++ Lret :: post` satisfies at `x86Isa.withCalls` the specification
    of a procedure at `l` that returns at the counter `pre.length + 1 + B.length`. Its entry
    relation is `SR` up to the stack pointer and its cell, at the offset of the body; the
    stack pointer and the cell it addresses are those of the entry at the return. -/
theorem x86_procSpec_of_body_judgement {fn : String} {pre B : List LinstrRM}
    (post : List LinstrRM) (kind : LabelKind) (tagl tag : MemTag) (l : LLabel)
    {SR : LstateMF → A → Prop} {Pre : A → Prop} {fa : A → A} {fuel : Nat}
    (hB : ∀ i ∈ B, isCall i.fst = false) (hP : ∀ i ∈ B, SpFree "RSP" i.fst)
    (hfresh : LabelsFresh (pre ++ [(.Llabel kind l, tagl)]) B)
    (h : CorresIsa x86Isa (singletonProgM fn B) SR Pre fa fuel)
    (hentry : ∀ m a, SR m a → Pre a → m.prog.lfn = fn ∧ m.prog.base.lpc ≤ B.length) :
    ProcSpec x86Isa.withCalls
      (singletonProgM fn (pre ++ [(.Llabel kind l, tagl)] ++ B ++ (.Lret, tag) :: post)) l
      (pre.length + 1 + B.length) (relocRel (pre.length + 1) (spRel "RSP" SR)) Pre fa
      (relocFrame (pre.length + 1) (SpFrameRun "RSP" x86Isa (singletonProgM fn B) fuel))
      fuel :=
  x86_procSpec_labelled_of_corresIsa post kind tagl tag l hB hfresh
    (x86_corresIsa_spRel (P := singletonProgM fn B) hP h) (x86_exitFrame_of_spFree hP hentry)

/-- **The entry relation holds after a call step.** Let `m₀` be related by `SR` to `a` at
    the counter `0`. The caller state `m₀` with the stack pointer `sp` holding `v`, at any
    counter `k`, has the stack pointer readable at width `64`, and the state after its call
    step to a label declared at the index `q` is related to `a` by `spRel sp SR` at the
    offset `q + 1`. -/
theorem spRel_callEntry {SR : LstateMF → A → Prop} (sp : String) (v : BitVec 64) (q k : Nat)
    {m₀ : LstateMF} {a : A} (hSR : SR m₀ a) (hpc : m₀.prog.base.lpc = 0) :
    (goto { m₀ with prog := { m₀.prog with base := m₀.prog.base.setReg sp v } }
        k).prog.base.reg.getW sp 64 = some v ∧
      relocRel (q + 1) (spRel sp SR)
        (callEntry sp v q
          (goto { m₀ with prog := { m₀.prog with base := m₀.prog.base.setReg sp v } } k)) a := by
  refine ⟨LstateN.getW_setReg_same _ sp v, relocRel_callEntry sp v q _ ?_⟩
  refine ⟨v - 8, BitVec.ofNat 64 (k + 1), m₀, ?_, hSR⟩
  obtain ⟨⟨b, lfn⟩, zf⟩ := m₀
  simp only [callEntry, goto, pushRet, spFrame, spM, retAddr, LstateMF.mk.injEq,
    LstatePM.mk.injEq, and_true]
  refine lstateM_ext ?_ hpc.symm rfl rfl rfl rfl
  funext r
  by_cases hr : r = sp <;> simp [LstateM.setReg, LstateN.setReg, LstateM.setLpc,
    LstateM.storeMemC, hr]

end Generic

/-! ## 7. A judgement on the two-phase relation -/

section TwoPhase

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)

variable {O : Type}

/-- A state related by the two-phase relation under the two-phase precondition is in the
    function `fn` at a counter at most `n`, when every entry state is at the counter `0`. -/
theorem phaseSR_entry_bound {fn : String} {Entry : AState → LstateM → Bool → Prop}
    {dec : LstateM → Option O} {layout : List RInstr} {Exit : AState → AState → O → Prop}
    {PreS : AState → Prop} (hE : ∀ sa b zf, Entry sa b zf → b.reg.lpc = 0) (n : Nat)
    (m : LstateMF) (a : PhaseAbs O) (hSR : phaseSR fn Entry dec layout Exit m a)
    (hPre : phasePre PreS a) : m.prog.lfn = fn ∧ m.prog.base.lpc ≤ n := by
  unfold phaseSR at hSR
  rw [hPre.1] at hSR
  have h0 : m.prog.base.lpc = 0 := hE _ _ _ hSR.2
  exact ⟨hSR.1, by rw [h0]; exact Nat.zero_le _⟩

/-- **The procedure specification of the image of a body, from its judgement at a fixed entry
    state.** Let the body `B` contain no call and no return (`isCall`) and name `RSP` in no
    instruction (`spFreeBodyB`), both decided on `B`; let no label of `B` be declared in
    `pre` or be `l`; let `B` correspond at fuel `fuel` to `phaseAbs spec` on the two-phase
    relation of an entry relation `Entry` whose states are at the counter `0`. The program
    `pre ++ Llabel l :: B ++ Lret :: post` satisfies at `x86Isa.withCalls` the specification
    of a procedure at `l` that returns at the counter `pre.length + 1 + B.length`, with the
    entry relation the two-phase relation up to the stack pointer and its cell, at the
    offset of the body. -/
theorem x86_procSpec_of_image_judgement {fn : String} {pre B : List LinstrRM}
    (post : List LinstrRM) (kind : LabelKind) (tagl tag : MemTag) (l : LLabel)
    {Entry : AState → LstateM → Bool → Prop} {dec : LstateM → Option O}
    {layout : List RInstr} {Exit : AState → AState → O → Prop} {PreS : AState → Prop}
    {spec : AState → O} {fuel : Nat}
    (hcall : (B.all fun i => !isCall i.fst) = true) (hsp : spFreeBodyB "RSP" B = true)
    (hfresh : LabelsFresh (pre ++ [(.Llabel kind l, tagl)]) B)
    (hE : ∀ sa b zf, Entry sa b zf → b.reg.lpc = 0)
    (h : CorresIsa x86Isa (singletonProgM fn B) (phaseSR fn Entry dec layout Exit)
      (phasePre PreS) (phaseAbs spec) fuel) :
    ProcSpec x86Isa.withCalls
      (singletonProgM fn (pre ++ [(.Llabel kind l, tagl)] ++ B ++ (.Lret, tag) :: post)) l
      (pre.length + 1 + B.length)
      (relocRel (pre.length + 1) (spRel "RSP" (phaseSR fn Entry dec layout Exit)))
      (phasePre PreS) (phaseAbs spec)
      (relocFrame (pre.length + 1) (SpFrameRun "RSP" x86Isa (singletonProgM fn B) fuel))
      fuel :=
  x86_procSpec_of_body_judgement post kind tagl tag l
    (fun i hi => by simpa using List.all_eq_true.1 hcall i hi)
    (spFree_of_spFreeBodyB hsp) hfresh h (phaseSR_entry_bound hE B.length)

/-- **The entry relation of the image specification holds after a call step.** Let `b` be an
    entry state of `Entry` at `sa` with the zero flag `zf`, at the counter `0`. The caller
    state with the base `b`, the stack pointer `RSP` holding `v`, in the function `fn` at any
    counter `k`, has the stack pointer readable at width `64`, and the state after its call
    step to a label declared at the index `q` is related at the offset `q + 1`, up to the
    stack pointer and its cell, to the abstract state of `sa` before the run. -/
theorem phaseSR_spRel_callEntry {fn : String} {Entry : AState → LstateM → Bool → Prop}
    (dec : LstateM → Option O) (layout : List RInstr) (Exit : AState → AState → O → Prop)
    {sa : AState} {b : LstateM} {zf : Bool} (hEnt : Entry sa b zf) (hpc : b.reg.lpc = 0)
    (v : BitVec 64) (q k : Nat) :
    (goto { prog := { base := b.setReg "RSP" v, lfn := fn }, zf := zf }
        k).prog.base.reg.getW "RSP" 64 = some v ∧
      relocRel (q + 1) (spRel "RSP" (phaseSR fn Entry dec layout Exit))
        (callEntry "RSP" v q
          (goto { prog := { base := b.setReg "RSP" v, lfn := fn }, zf := zf } k))
        ({ sa := sa, out := none } : PhaseAbs O) :=
  spRel_callEntry "RSP" v q k
    (m₀ := { prog := { base := b, lfn := fn }, zf := zf })
    (SR := phaseSR fn Entry dec layout Exit) (a := { sa := sa, out := none })
    ⟨rfl, hEnt⟩ hpc

end TwoPhase

end IsaCall

end CatCrypt.Crypto.SecureCompilation.Ascent
