/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg

/-!
# Substitution of equal registers in the sources of an instruction

Copy propagation rewrites a register source of an instruction to a register that holds the
same cell. This module proves that such a rewriting does not change the step of the flag
machine: `mapI g i` is the instruction `i` with every register source `n` replaced by
`g n`, and when `g n` holds the cell of `n` for every `n`, the extended straight step
`fstepF` of `mapI g i` is the step of `i`.

## Main definitions

* `mapReg g`, `mapI g` — the renaming of the register sources of an operand and of an
  instruction.

## Main results

* `lsemStepN_mapI`, `lsemStepSh_mapI`, `lsemStepMC_mapI`, `lsemStepCast_mapI`,
  `lsemStepMem_mapI`, `stepMemF_mapI` — the layers of the step.
* `fstepF_mapI` — the extended straight step.
* `FactsOkM`, `fstepF_rewrite`, `factsOkM_step` — register facts of forward propagation on
  the flag machine: the step of a rewritten instruction, and the facts after a step.
* `cpRegOKB`, `TagShape`, `propagateAux_runStraightF` — forward propagation over the
  extended straight fold, on a body with register destinations and no immediate candidate
  move, for a tagging that depends on destinations and mnemonic only.
* `DeadElimSim`, `copyPropSim_of_deadElimSim` — copy propagation over the extended straight
  fold, given the statement of dead-move elimination at the propagated body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyPropCfg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin

/-! ## 1. The renaming of register sources -/

/-- An operand with its register renamed by `g`; other operands are kept. -/
def mapReg (g : String → String) : LOperand → LOperand
  | .reg n => .reg (g n)
  | o => o

/-- An instruction with every register source renamed by `g`. -/
def mapI (g : String → String) : LinstrR → LinstrR
  | .Lopn d o srcs => .Lopn d o (srcs.map (mapReg g))
  | i => i

@[simp] theorem mapReg_reg (g : String → String) (n : String) :
    mapReg g (.reg n) = .reg (g n) := rfl

@[simp] theorem mapReg_imm (g : String → String) (k : Nat) : mapReg g (.imm k) = .imm k := rfl

@[simp] theorem mapReg_arr (g : String → String) (b : String) (k : Nat) :
    mapReg g (.arr b k) = .arr b k := rfl

@[simp] theorem mapReg_arrIdx (g : String → String) (b x : String) (k : Nat) :
    mapReg g (.arrIdx b x k) = .arrIdx b x k := rfl

section Operand

variable {g : String → String} {s : LstateN} (hg : ∀ n, s.lvm (g n) = s.lvm n)
include hg

theorem getW_map (n : String) (w : Nat) : s.getW (g n) w = s.getW n w := by
  unfold LstateN.getW
  rw [hg n]

theorem readReg_map (n : String) : readReg s (.reg (g n)) = readReg s (.reg n) := by
  simp only [readReg, hg n]

theorem readReg_mapReg (o : LOperand) : readReg s (mapReg g o) = readReg s o := by
  cases o with
  | reg n => simp only [mapReg, readReg, hg n]
  | _ => rfl

theorem evalOperandN_mapReg (w : Nat) (o : LOperand) :
    evalOperandN s w (mapReg g o) = evalOperandN s w o := by
  cases o with
  | reg n => simp only [mapReg, evalOperandN, getW_map hg]
  | _ => rfl

theorem getW_operandName_mapReg (o : LOperand) (w : Nat) :
    s.getW (operandName (mapReg g o)) w = s.getW (operandName o) w := by
  cases o with
  | reg n => simp only [mapReg, operandName, getW_map hg]
  | _ => rfl

theorem immFirstN_mapReg (dst opn : String) (n : Nat) (b : LOperand) :
    immFirstN s dst opn n (mapReg g b) = immFirstN s dst opn n b := by
  unfold immFirstN
  rw [evalOperandN_mapReg hg]

/-- The width-aware step under a renaming of register sources to registers with the same
    cells. -/
theorem lsemStepN_mapI (i : LinstrR) : lsemStepN (mapI g i) s = lsemStepN i s := by
  cases i with
  | Lopn d o srcs =>
      rcases d with _ | ⟨d0, _ | ⟨d1, dr⟩⟩
      · rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, r⟩⟩⟩⟩ <;> simp [mapI, lsemStepN]
      · cases d0 <;>
          rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, r⟩⟩⟩⟩ <;>
          (try cases a) <;>
          simp [mapI, lsemStepN, readReg_mapReg hg, evalOperandN_mapReg hg,
            immFirstN_mapReg hg, getW_map hg, readReg_map hg, operandName]
      · rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, r⟩⟩⟩⟩ <;> simp [mapI, lsemStepN]
  | _ => rfl

/-- The shift-aware step under a renaming of register sources. -/
theorem lsemStepSh_mapI (i : LinstrR) : lsemStepSh (mapI g i) s = lsemStepSh i s := by
  have hN := lsemStepN_mapI hg i
  cases i with
  | Lopn d o srcs =>
      rcases d with _ | ⟨d0, _ | ⟨d1, dr⟩⟩
      · rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
          simp only [mapI, List.map, lsemStepSh, sarStruct?] at hN ⊢ <;> exact hN
      · cases d0 <;>
          rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
          (try cases a) <;> (try cases b) <;>
          simp only [mapI, List.map, mapReg_reg, mapReg_imm, mapReg_arr, mapReg_arrIdx,
            lsemStepSh, sarStruct?] at hN ⊢ <;>
          first
            | exact hN
            | (by_cases hc : stripWidthTag o = "SAR"
               · simp only [hc, ↓reduceIte, readReg_map hg]
               · simp only [hc, ↓reduceIte]
                 exact hN)
      · rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
          simp only [mapI, List.map, lsemStepSh, sarStruct?] at hN ⊢ <;> exact hN
  | _ => rfl

/-- The mul/carry-aware step under a renaming of register sources. -/
theorem lsemStepMC_mapI (i : LinstrR) : lsemStepMC (mapI g i) s = lsemStepMC i s := by
  have hS := lsemStepSh_mapI hg i
  cases i with
  | Lopn d o srcs =>
      rcases d with _ | ⟨d0, _ | ⟨d1, dr⟩⟩
      · rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, r⟩⟩⟩⟩ <;>
          simp only [mapI, List.map, lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?,
            sbbStruct?, sbbhiStruct?] at hS ⊢ <;> exact hS
      · cases d0 <;>
          rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, r⟩⟩⟩⟩ <;>
          (try cases a) <;> (try cases b) <;> (try cases c) <;>
          simp only [mapI, List.map, mapReg_reg, mapReg_imm, mapReg_arr, mapReg_arrIdx,
            lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?, sbbhiStruct?]
            at hS ⊢ <;>
          first
            | exact hS
            | (split_ifs <;>
                first
                  | exact hS
                  | simp only [readReg_map hg, getW_map hg])
      · rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, r⟩⟩⟩⟩ <;>
          simp only [mapI, List.map, lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?,
            sbbStruct?, sbbhiStruct?] at hS ⊢ <;> exact hS
  | _ => rfl

omit hg in
theorem movImmStruct?_mapI (i : LinstrR) : movImmStruct? (mapI g i) = movImmStruct? i := by
  cases i with
  | Lopn d o srcs =>
      rcases srcs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> (try cases a) <;>
        first | rfl | simp [mapI, movImmStruct?]
  | _ => rfl

/-- The cast-aware step under a renaming of register sources. -/
theorem lsemStepCast_mapI (i : LinstrR) (cd : Option Nat) :
    lsemStepCast (mapI g i, cd) s = lsemStepCast (i, cd) s := by
  have hM := lsemStepMC_mapI hg i
  have hI := movImmStruct?_mapI (g := g) i
  cases i with
  | Lopn d o srcs =>
      rcases d with _ | ⟨d0, _ | ⟨d1, dr⟩⟩
      · rcases srcs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;>
          simp only [lsemStepCast, hI] <;>
          simp only [mapI, List.map, castStruct?] at hM ⊢ <;> rw [hM]
      · cases d0 <;>
          rcases srcs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> (try cases a) <;>
          simp only [lsemStepCast, hI] <;>
          simp only [mapI, List.map, mapReg_reg, mapReg_imm, mapReg_arr, mapReg_arrIdx,
            castStruct?] at hM ⊢ <;>
          first
            | rfl
            | (rw [hM]; split_ifs <;> cases cd <;> simp only [readReg_map hg])
            | rw [hM]
      · rcases srcs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;>
          simp only [lsemStepCast, hI] <;>
          simp only [mapI, List.map, castStruct?] at hM ⊢ <;> rw [hM]
  | _ => rfl

end Operand

/-! ## 2. The recognizers of the memory and flag layers -/

section Recognizers

variable (g : String → String)

theorem loadStruct?_mapI (i : LinstrR) : loadStruct? (mapI g i) = loadStruct? i := by
  cases i with
  | Lopn d o srcs =>
      rcases srcs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> (try cases a) <;>
        first | rfl | simp [mapI, loadStruct?]
  | _ => rfl

theorem loadCStruct?_mapI (i : LinstrR) : loadCStruct? (mapI g i) = loadCStruct? i := by
  cases i with
  | Lopn d o srcs =>
      rcases srcs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> (try cases a) <;>
        first | rfl | simp [mapI, loadCStruct?]
  | _ => rfl

theorem storeStruct?_mapI (i : LinstrR) :
    storeStruct? (mapI g i) = (storeStruct? i).map (fun p => (p.1, p.2.1, p.2.2.1, g p.2.2.2)) := by
  cases i with
  | Lopn d o srcs =>
      rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        first
          | rfl
          | (simp [mapI, storeStruct?]; done)
          | (rcases d with _ | ⟨d0, _ | ⟨d1, dr⟩⟩ <;> (try cases d0) <;>
              simp only [mapI, List.map, mapReg_reg, mapReg_arrIdx, storeStruct?] <;>
              first | rfl | (split_ifs <;> rfl))
  | _ => rfl

theorem storeCStruct?_mapI (i : LinstrR) :
    storeCStruct? (mapI g i) = (storeCStruct? i).map (fun p => (p.1, p.2.1, g p.2.2)) := by
  cases i with
  | Lopn d o srcs =>
      rcases srcs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> (try cases a) <;>
        first
          | rfl
          | (simp [mapI, storeCStruct?]; done)
          | (rcases d with _ | ⟨d0, _ | ⟨d1, dr⟩⟩ <;> (try cases d0) <;>
              simp only [mapI, List.map, mapReg_reg, storeCStruct?] <;>
              first | rfl | (split_ifs <;> rfl))
  | _ => rfl

theorem aluFlagOp?_mapI (i : LinstrR) (tg : MemTag) :
    aluFlagOp? (mapI g i, tg)
      = (aluFlagOp? (i, tg)).map (fun p => (p.1, mapReg g p.2.1, mapReg g p.2.2)) := by
  cases i with
  | Lopn d o srcs =>
      rcases d with _ | ⟨d0, _ | ⟨d1, dr⟩⟩ <;> (try cases d0) <;>
        rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
        simp only [mapI, List.map, aluFlagOp?] <;>
        first | rfl | (split_ifs <;> rfl)
  | _ => rfl

theorem carryArgs?_mapI (i : LinstrR) (tg : MemTag) :
    carryArgs? (mapI g i, tg)
      = (carryArgs? (i, tg)).map (fun p => (p.1, p.2.1, mapReg g p.2.2.1, mapReg g p.2.2.2)) := by
  cases i with
  | Lopn d o srcs =>
      rcases d with _ | ⟨d0, _ | ⟨d1, dr⟩⟩ <;> (try cases d0) <;>
        rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
        simp only [mapI, List.map, carryArgs?] <;>
        first | rfl | (split_ifs <;> rfl)
  | _ => rfl

/-- A flag-quiet lift operation with its register source renamed. -/
def mapWide : WideOp → WideOp
  | .mov d b => .mov d (mapReg g b)
  | .mulx lo hi b => .mulx lo hi (mapReg g b)

theorem wideArgs?_mapI (i : LinstrR) (tg : MemTag) :
    wideArgs? (mapI g i, tg) = (wideArgs? (i, tg)).map (mapWide g) := by
  cases i with
  | Lopn d o srcs =>
      rcases d with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, dr⟩⟩⟩ <;> (try cases d0) <;> (try cases d1) <;>
        rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
        simp only [mapI, List.map, wideArgs?] <;>
        first | rfl | (split_ifs <;> rfl)
  | _ => rfl

theorem cmpArgs?_mapI (i : LinstrR) (tg : MemTag) :
    cmpArgs? (mapI g i, tg)
      = (cmpArgs? (i, tg)).map (fun p => (mapReg g p.1, mapReg g p.2)) := by
  cases i with
  | Lopn d o srcs =>
      rcases d with _ | ⟨d0, _ | ⟨d1, dr⟩⟩ <;>
        rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;>
        simp only [mapI, List.map, cmpArgs?] <;>
        first | rfl | (split_ifs <;> rfl)
  | _ => rfl

theorem movRegArgs?_mapI (i : LinstrR) (tg : MemTag) :
    movRegArgs? (mapI g i, tg) = (movRegArgs? (i, tg)).map (fun p => (p.1, g p.2)) := by
  cases i with
  | Lopn d o srcs =>
      rcases d with _ | ⟨d0, _ | ⟨d1, dr⟩⟩ <;> (try cases d0) <;>
        rcases srcs with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> (try cases a) <;>
        simp only [mapI, List.map, mapReg_reg, mapReg_imm, mapReg_arr, mapReg_arrIdx,
          movRegArgs?] <;>
        first | rfl | (split_ifs <;> rfl)
  | _ => rfl

end Recognizers

/-! ## 3. The memory step, the flag step and the extended straight step -/

section Mem

variable {g : String → String} {s : LstateM} (hg : ∀ n, s.reg.lvm (g n) = s.reg.lvm n)
include hg

/-- The memory step under a renaming of register sources. -/
theorem lsemStepMem_mapI (i : LinstrR) (tg : MemTag) :
    lsemStepMem (mapI g i, tg) s = lsemStepMem (i, tg) s := by
  have hC := fun cd => lsemStepCast_mapI hg i cd
  cases tg with
  | load w n => simp only [lsemStepMem, loadStruct?_mapI, hC]
  | store w n =>
      simp only [lsemStepMem, storeStruct?_mapI, hC]
      cases storeStruct? i with
      | none => rfl
      | some p => simp only [Option.map_some, getW_map hg]
  | loadC => simp only [lsemStepMem, loadCStruct?_mapI]
  | storeC =>
      simp only [lsemStepMem, storeCStruct?_mapI]
      cases storeCStruct? i with
      | none => rfl
      | some p => simp only [Option.map_some, getW_map hg]
  | reg cd => simp only [lsemStepMem, hC]

theorem carryStep_mapReg (op : CarryOp) (d : String) (a b : LOperand) :
    carryStep op d (mapReg g a) (mapReg g b) s = carryStep op d a b s := by
  unfold carryStep
  rw [evalOperandN_mapReg hg, evalOperandN_mapReg hg]

theorem wideStep_mapWide (w : WideOp) : wideStep (mapWide g w) s = wideStep w s := by
  cases w with
  | mov d b => simp only [mapWide, wideStep, evalOperandN_mapReg hg]
  | mulx lo hi b => simp only [mapWide, wideStep, evalOperandN_mapReg hg]

theorem withALUFlags_mapI (i : LinstrR) (tg : MemTag) (b : LstateM) :
    withALUFlags (mapI g i, tg) s b = withALUFlags (i, tg) s b := by
  unfold withALUFlags
  rw [aluFlagOp?_mapI]
  cases aluFlagOp? (i, tg) with
  | none => rfl
  | some p => simp only [Option.map_some, evalOperandN_mapReg hg]

/-- The straight-line step of the flag machine under a renaming of register sources. -/
theorem stepMemF_mapI (i : LinstrR) (tg : MemTag) :
    stepMemF (mapI g i, tg) s = stepMemF (i, tg) s := by
  unfold stepMemF
  rw [lsemStepMem_mapI hg, carryArgs?_mapI, wideArgs?_mapI]
  cases lsemStepMem (i, tg) s with
  | some b => simp only [withALUFlags_mapI hg]
  | none =>
      simp only
      cases carryArgs? (i, tg) with
      | some p => simp only [Option.map_some, carryStep_mapReg hg]
      | none =>
          simp only [Option.map_none]
          cases wideArgs? (i, tg) with
          | some w => simp only [Option.map_some, wideStep_mapWide hg]
          | none => rfl

/-- **The extended straight step under a renaming of register sources.** When every
    register `g n` holds the cell of `n`, the step of the instruction with its register
    sources renamed by `g` is the step of the instruction, under the same tag. -/
theorem fstepF_mapI (i : LinstrR) (tg : MemTag) (zf : Bool) :
    fstepF (mapI g i, tg) s zf = fstepF (i, tg) s zf := by
  unfold fstepF
  rw [cmpArgs?_mapI, movRegArgs?_mapI, stepMemF_mapI hg]
  cases cmpArgs? (i, tg) with
  | some p => simp only [Option.map_some, evalOperandN_mapReg hg]
  | none =>
      simp only [Option.map_none]
      cases movRegArgs? (i, tg) with
      | some p => simp only [Option.map_some, readReg_map hg]
      | none => rfl

end Mem

/-! ## 4. Forward propagation of register facts -/

section Propagate

open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad (isMovMnem writtenNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames fstepF_frame_dst)
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg

/-- The invariant of forward propagation on the flag machine, for register facts: every
    fact names a physical register that holds the cell of a physical source register. -/
def FactsOkM (facts : List MoveFact) (s : LstateM) : Prop :=
  ∀ f ∈ facts, isPhysGP f.1 = true ∧
    ∃ r, f.2.1 = LOperand.reg r ∧ isPhysGP r = true ∧ s.reg.lvm f.1 = s.reg.lvm r

/-- Under register facts, a rewritten register operand is the operand or a register the
    facts record for it. -/
theorem rewriteOperand_reg_cases {facts : List MoveFact} {s : LstateM}
    (hok : FactsOkM facts s) (ew : Nat) (ai : Bool) (ds : Option String) (u : String) :
    rewriteOperand facts ew ai ds (.reg u) = .reg u
      ∨ ∃ r, rewriteOperand facts ew ai ds (.reg u) = .reg r ∧ s.reg.lvm u = s.reg.lvm r := by
  simp only [rewriteOperand]
  split
  · cases hl : lookupFact facts u with
    | none => exact Or.inl rfl
    | some p =>
        obtain ⟨v, fw⟩ := p
        obtain ⟨-, r, hv, -, hr⟩ := hok _ (lookupFact_mem hl)
        have hv' : v = LOperand.reg r := hv
        subst hv'
        simp only
        split
        · exact Or.inr ⟨r, rfl, hr⟩
        · exact Or.inl rfl
  · exact Or.inl rfl

/-- **The step of a rewritten instruction, for register facts.** -/
theorem fstepF_rewrite {facts : List MoveFact} {s : LstateM} (hok : FactsOkM facts s)
    (dsts : List LOperand) (opn : String) (srcs : List LOperand) (ew : Nat) (ai : Bool)
    (ds : Option String) (tg : MemTag) (zf : Bool) :
    fstepF (.Lopn dsts opn (srcs.map (rewriteOperand facts ew ai ds)), tg) s zf
      = fstepF (.Lopn dsts opn srcs, tg) s zf := by
  let g : String → String := fun u =>
    match rewriteOperand facts ew ai ds (.reg u) with
    | .reg m => m
    | _ => u
  have hg : ∀ n, s.reg.lvm (g n) = s.reg.lvm n := by
    intro n
    rcases rewriteOperand_reg_cases hok ew ai ds n with h | ⟨r, h, hr⟩
    · simp only [g, h]
    · simp only [g, h]
      exact hr.symm
  have h1 : ∀ o, rewriteOperand facts ew ai ds o = mapReg g o := by
    intro o
    cases o with
    | reg u =>
        rcases rewriteOperand_reg_cases hok ew ai ds u with h | ⟨r, h, -⟩ <;>
          simp only [mapReg_reg, g, h]
    | _ => rfl
  rw [List.map_congr_left (fun o _ => h1 o)]
  exact fstepF_mapI hg (.Lopn dsts opn srcs) tg zf

theorem mem_foldl_killFacts {rs : List String} {facts : List MoveFact} {f : MoveFact}
    (h : f ∈ rs.foldl killFacts facts) :
    f ∈ facts ∧ ∀ r ∈ rs, f.1 ≠ r ∧ factSrcNames f.2.1 r = false := by
  induction rs generalizing facts with
  | nil => exact ⟨h, fun _ hr => by simp at hr⟩
  | cons a rest ih =>
      rw [List.foldl_cons] at h
      obtain ⟨h1, h2⟩ := ih h
      obtain ⟨h3, h4, h5⟩ := mem_killFacts h1
      refine ⟨h3, fun r hr => ?_⟩
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨h4, h5⟩
      · exact h2 r hr

/-- A physical register among the destinations of an instruction with register
    destinations is a register the instruction defines. -/
theorem mem_regDefsOf_of_dstNames {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} (hd : dstsRegB (.Lopn dsts opn srcs) = true) {n : String}
    (hn : n ∈ dstNames (.Lopn dsts opn srcs)) (hp : isPhysGP n = true) :
    n ∈ regDefsOf dsts := by
  have hw := mem_writtenNames_of_dstNames hd hn
  simp only [writtenNames, List.mem_filterMap] at hw
  obtain ⟨x, hx, hxn⟩ := hw
  cases x with
  | reg m =>
      simp only [Option.some.injEq] at hxn
      subst hxn
      simp only [regDefsOf, List.mem_filterMap]
      exact ⟨.reg m, hx, by simp [hp]⟩
  | _ => simp at hxn

/-- **The facts after a step, for register facts.** At an instruction with register
    destinations whose candidate move, if it is one, is a register copy under a move
    mnemonic, the facts forward propagation keeps and records hold after the step. -/
theorem factsOkM_step {facts : List MoveFact} {s s₁ : LstateM} {zf z : Bool}
    (hok : FactsOkM facts s) {i' : Linstr} {dsts : List LOperand} {opn : String}
    {srcs' : List LOperand} (hi' : i'.li_i = .Lopn dsts opn srcs') (tg : MemTag)
    (hd : dstsRegB (.Lopn dsts opn srcs') = true)
    (hmv : ∀ d src ww, moveShape i' = some (d, src, ww) →
      isMovMnem opn = true ∧ ∃ r, src = LOperand.reg r)
    (hstep : fstepF (.Lopn dsts opn srcs', tg) s zf = some (s₁, z)) :
    FactsOkM (match moveShape i' with
              | some (d, src, ww) =>
                  if src == LOperand.reg d then (regDefsOf dsts).foldl killFacts facts
                  else (d, src, ww) :: (regDefsOf dsts).foldl killFacts facts
              | none => (regDefsOf dsts).foldl killFacts facts) s₁ := by
  have hkept : FactsOkM ((regDefsOf dsts).foldl killFacts facts) s₁ := by
    intro f hf
    obtain ⟨hf0, hkill⟩ := mem_foldl_killFacts hf
    obtain ⟨hp, r, hr, hpr, hcell⟩ := hok f hf0
    refine ⟨hp, r, hr, hpr, ?_⟩
    have h1 : f.1 ∉ dstNames (.Lopn dsts opn srcs') := fun hm =>
      (hkill _ (mem_regDefsOf_of_dstNames hd hm hp)).1 rfl
    have h2 : r ∉ dstNames (.Lopn dsts opn srcs') := fun hm => by
      have := (hkill _ (mem_regDefsOf_of_dstNames hd hm hpr)).2
      rw [hr] at this
      simp [factSrcNames] at this
    rw [(fstepF_frame_dst hstep h1).1, (fstepF_frame_dst hstep h2).1]
    exact hcell
  cases hms : moveShape i' with
  | none => exact hkept
  | some q =>
      obtain ⟨d, src, ww⟩ := q
      simp only
      split
      · exact hkept
      · rename_i hne
        obtain ⟨hmm, r, rfl⟩ := hmv d src ww hms
        obtain ⟨opn', hsh, hpd, hfs, -⟩ := moveShape_inv hms
        rw [hi'] at hsh
        simp only [LinstrR.Lopn.injEq] at hsh
        obtain ⟨rfl, rfl, rfl⟩ := hsh
        rw [fstepF_reload hmm, Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨rfl, -⟩ := hstep
        have hrd : r ≠ d := fun e => hne (by rw [e]; exact beq_self_eq_true _)
        intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · refine ⟨hpd, r, rfl, by simpa [isFactSrc] using hfs, ?_⟩
          rw [lvm_setReg_nextPcM, lvm_setReg_nextPcM, if_pos rfl, if_neg hrd]
        · exact hkept f hf

/-- The operand is not an immediate. -/
def notImmB : LOperand → Bool
  | .imm _ => false
  | _ => true

/-- The check of an instruction for forward propagation of register facts: its
    destinations are registers, and if it is a one-source instruction under a `MOV` or
    `MOVQ` mnemonic, the mnemonic is a move mnemonic and the source is not an immediate. -/
def cpRegOKB (i : Linstr) : Bool :=
  dstsRegB i.li_i &&
    (match i.li_i with
     | .Lopn _ opn [x] =>
         !(stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ")
           || (isMovMnem opn && notImmB x)
     | _ => true)

/-- A tagging that depends on the destinations and the mnemonic of an `Lopn` only. -/
def TagShape (tag : LinstrR → MemTag) : Prop :=
  ∀ (d : List LOperand) (o : String) (s s' : List LOperand),
    tag (.Lopn d o s) = tag (.Lopn d o s')

/-- A candidate move among the rewritten instructions of a checked body is a register copy
    under a move mnemonic. -/
theorem moveShape_rewrite_ok {facts : List MoveFact} {s : LstateM} (hok : FactsOkM facts s)
    {i : Linstr} {dsts : List LOperand} {opn : String} {srcs : List LOperand}
    (hi : i.li_i = .Lopn dsts opn srcs) (hc : cpRegOKB i = true) (ew : Nat) (ai : Bool)
    (ds : Option String) {d : String} {src : LOperand} {ww : Nat}
    (h : moveShape { i with li_i := .Lopn dsts opn (srcs.map (rewriteOperand facts ew ai ds)) }
      = some (d, src, ww)) :
    isMovMnem opn = true ∧ ∃ r, src = LOperand.reg r := by
  obtain ⟨opn', hsh, -, hfs, hstrip⟩ := moveShape_inv h
  simp only [LinstrR.Lopn.injEq] at hsh
  obtain ⟨-, rfl, hmap⟩ := hsh
  rcases srcs with _ | ⟨x, _ | ⟨y, r⟩⟩
  · simp at hmap
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
    simp only [cpRegOKB, hi, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq, Bool.or_eq_false_iff] at hc
    have h2 : isMovMnem opn = true ∧ notImmB x = true := by
      rcases hc.2 with hno | hyes
      · rcases hstrip with e | e
        · exact absurd e hno.1
        · exact absurd e hno.2
      · exact hyes
    refine ⟨h2.1, ?_⟩
    cases x with
    | reg u =>
        rcases rewriteOperand_reg_cases hok ew ai ds u with e | ⟨r, e, -⟩
        · exact ⟨u, by rw [← hmap, e]⟩
        · exact ⟨r, by rw [← hmap, e]⟩
    | imm k => exact absurd h2.2 (by simp [notImmB])
    | arr b k =>
        have e : src = LOperand.arr b k := hmap.symm
        rw [e] at hfs
        simp [isFactSrc] at hfs
    | arrIdx b x k =>
        have e : src = LOperand.arrIdx b x k := hmap.symm
        rw [e] at hfs
        simp [isFactSrc] at hfs
  · simp at hmap

/-- **Forward propagation of register facts over the extended straight fold.** For a
    tagging that depends on destinations and mnemonic only, a body that passes `cpRegOKB`,
    and facts that hold in the start state, the propagated body runs to the state and zero
    flag of the input body. -/
theorem propagateAux_runStraightF (tag : LinstrR → MemTag) (hT : TagShape tag)
    (body : Lcmd) :
    ∀ (facts : List MoveFact) (s : LstateM) (zf : Bool), (∀ i ∈ body, cpRegOKB i = true) →
      FactsOkM facts s →
      runStraightF ((propagateAux facts body).map fun i => (i.li_i, tag i.li_i)) s zf
        = runStraightF (body.map fun i => (i.li_i, tag i.li_i)) s zf := by
  have hnil : ∀ (t : LstateM), FactsOkM ([] : List MoveFact) t := by
    intro t f hf
    exact absurd hf (by simp)
  induction body with
  | nil => intro facts s zf _ _; rfl
  | cons i rest ih =>
    intro facts s zf hb hok
    have hci := hb i List.mem_cons_self
    have hrest : ∀ j ∈ rest, cpRegOKB j = true := fun j hj => hb j (List.mem_cons_of_mem _ hj)
    rw [propagateAux]
    split
    · rename_i dsts opn srcs hi
      split
      · simp only [List.map_cons, runStraightF_cons]
        rw [hi, hT dsts opn _ srcs, fstepF_rewrite hok]
        cases hst : fstepF (.Lopn dsts opn srcs, tag (.Lopn dsts opn srcs)) s zf with
        | none => rfl
        | some bz =>
          obtain ⟨s₁, z₁⟩ := bz
          simp only [Option.bind_some]
          refine ih _ s₁ z₁ hrest ?_
          refine factsOkM_step (zf := zf) (z := z₁) hok rfl (tag (.Lopn dsts opn srcs)) ?_
            (fun d src ww h => moveShape_rewrite_ok hok hi hci _ _ _ h) ?_
          · have hd := hci
            simp only [cpRegOKB, hi, Bool.and_eq_true] at hd
            exact hd.1
          · rw [fstepF_rewrite hok]
            exact hst
      · simp only [List.map_cons, runStraightF_cons]
        cases hst : fstepF (i.li_i, tag i.li_i) s zf with
        | none => rfl
        | some bz =>
          simp only [Option.bind_some]
          exact ih [] bz.1 bz.2 hrest (hnil bz.1)
    · simp only [List.map_cons, runStraightF_cons]
      cases hst : fstepF (i.li_i, tag i.li_i) s zf with
      | none => rfl
      | some bz =>
        simp only [Option.bind_some]
        exact ih [] bz.1 bz.2 hrest (hnil bz.1)

/-- The statement of dead-move elimination on one body over the extended straight fold: a
    run of the body is matched by a run of the body without its dead moves from the same
    state, with the same zero flag and final states equal up to the program counter. -/
def DeadElimSim (tag : LinstrR → MemTag) (body : Lcmd) : Prop :=
  ∀ (s : LstateM) (zf : Bool) (s₂ : LstateM) (z₂ : Bool),
    runStraightF (body.map fun i => (i.li_i, tag i.li_i)) s zf = some (s₂, z₂) →
    ∃ t₂, runStraightF ((deadElimBody body).map fun i => (i.li_i, tag i.li_i)) s zf
        = some (t₂, z₂) ∧ JasminLsemExportLower.EqPc s₂ t₂

/-- **Copy propagation over the extended straight fold, given dead-move elimination.** For
    a tagging that depends on destinations and mnemonic only and a body that passes
    `cpRegOKB`, the statement of dead-move elimination at the propagated body gives the
    statement of copy propagation at the body. -/
theorem copyPropSim_of_deadElimSim (tag : LinstrR → MemTag) (hT : TagShape tag) (body : Lcmd)
    (hb : ∀ i ∈ body, cpRegOKB i = true)
    (hde : DeadElimSim tag (propagateAux [] body)) : CopyPropSim tag body := by
  intro s zf s₂ z₂ hrun
  rw [← propagateAux_runStraightF tag hT body [] s zf hb
    (fun f hf => absurd hf (by simp))] at hrun
  exact hde s zf s₂ z₂ hrun

end Propagate

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyPropCfg
