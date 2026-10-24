/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr

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
* `fstepF_setReg_dst` — the step of an instruction with one register destination that no
  source names, that is neither the flag compare nor an indexed store, does not depend on
  the earlier cell of the destination; with its layers `lsemStepN_setReg_dst`,
  `lsemStepSh_setReg_dst`, `lsemStepMC_setReg_dst`, `lsemStepCast_setReg_dst`,
  `lsemStepMem_setReg_dst`, `stepMemF_setReg_dst`.
* `fstepF_liveStep` — the step from two states, at any two program counters, that agree on
  the names `JasminLsemAddrCongr.readsI` lists.
* `LiveAgreeM`, `deadOKB`, `liveAgreeM_drop`, `liveAgreeM_keep`,
  `deadElim_foldr_runStraightF`, `deadElim_runStraightF` — backward dead-move elimination
  over the extended straight fold is a forward simulation up to the live set, on a body
  that passes `deadOKB`.
* `copyPropSim_of_deadOKB`, `optBlocksRegOKB`, `optBlocksRegOKB_sound` — copy propagation
  for register facts, and the basic-block optimiser on whole bodies of the flag machine
  for a body that passes the check.
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

theorem zeroStruct?_mapI (i : LinstrR) : zeroStruct? (mapI g i) = zeroStruct? i := by
  cases i with
  | Lopn d o srcs => rcases d with _ | ⟨d0, _ | ⟨d1, dr⟩⟩ <;> (try cases d0) <;> rfl
  | _ => rfl

/-- `mapI` keeps an instruction that is no constant-index store one. The copy
    propagation pass never rewrites a `STOREIMM` (`isRecognizedOpn` rejects it), so only
    this direction is needed. -/
theorem storeImmStruct?_mapI_none {i : LinstrR} (h : storeImmStruct? i = none) :
    storeImmStruct? (mapI g i) = none := by
  cases i with
  | Lopn d o srcs =>
      simp only [mapI]
      rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, r⟩⟩⟩⟩
      all_goals first
        | (simp [storeImmStruct?]; done)
        | (cases a <;> cases b <;> cases c <;> rcases d with _ | ⟨d0, _ | ⟨d1, dr⟩⟩ <;>
            (try cases d0) <;> simp_all [storeImmStruct?, mapReg])
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
theorem lsemStepMem_mapI (i : LinstrR) (tg : MemTag) (hnr : storeImmStruct? i = none) :
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
  | zero w n => simp only [lsemStepMem, zeroStruct?_mapI]
  | storeImm w n => simp only [lsemStepMem, storeImmStruct?_mapI_none (g := g) hnr, hnr]
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
theorem stepMemF_mapI (i : LinstrR) (tg : MemTag) (hnr : storeImmStruct? i = none) :
    stepMemF (mapI g i, tg) s = stepMemF (i, tg) s := by
  unfold stepMemF
  rw [lsemStepMem_mapI hg i tg hnr, carryArgs?_mapI, wideArgs?_mapI]
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
theorem fstepF_mapI (i : LinstrR) (tg : MemTag) (zf : Bool) (hnr : storeImmStruct? i = none) :
    fstepF (mapI g i, tg) s zf = fstepF (i, tg) s zf := by
  unfold fstepF
  rw [cmpArgs?_mapI, movRegArgs?_mapI, stepMemF_mapI hg i tg hnr]
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

/-- A mnemonic the copy propagation pass recognizes is no constant-index store. -/
theorem storeImmStruct?_none_of_recognized {ds : List LOperand} {opn : String}
    {ss : List LOperand} (h : isRecognizedOpn opn = true) :
    storeImmStruct? (.Lopn ds opn ss) = none := by
  unfold storeImmStruct?
  split
  · rename_i heq
    simp only [LinstrR.Lopn.injEq] at heq
    obtain ⟨-, rfl, -⟩ := heq
    rw [if_neg]
    rintro rfl
    exact absurd h (by
      simp (config := {decide := true}) [isRecognizedOpn, implicitReads, parseImmShiftMnem,
        X86Backend.LprogAsmPrinter.stripAbiTag])
  · rfl

/-- **The step of a rewritten instruction, for register facts.** -/
theorem fstepF_rewrite {facts : List MoveFact} {s : LstateM} (hok : FactsOkM facts s)
    (dsts : List LOperand) (opn : String) (srcs : List LOperand) (ew : Nat) (ai : Bool)
    (ds : Option String) (tg : MemTag) (zf : Bool)
    (hnr : storeImmStruct? (.Lopn dsts opn srcs) = none) :
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
  exact fstepF_mapI hg (.Lopn dsts opn srcs) tg zf hnr

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
      · rename_i hrec
        have hnr : storeImmStruct? (.Lopn dsts opn srcs) = none :=
          storeImmStruct?_none_of_recognized hrec
        simp only [List.map_cons, runStraightF_cons]
        rw [hi, hT dsts opn _ srcs, fstepF_rewrite hok _ _ _ _ _ _ _ _ hnr]
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
          · rw [fstepF_rewrite hok _ _ _ _ _ _ _ _ hnr]
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

/-! ## 5. A written destination does not depend on its earlier cell -/

section Overwrite

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (srcNames)

variable {d : String} {s : LstateN} {w : Nat} (c : BitVec w)

theorem setReg_setReg_same {w' : Nat} (v : BitVec w') :
    (s.setReg d c).setReg d v = s.setReg d v := by
  simp only [LstateN.setReg]
  congr 1
  funext r
  by_cases h : r = d <;> simp [h]

theorem readReg_setReg_ne {o : LOperand} (h : d ∉ srcNames o) :
    readReg (s.setReg d c) o = readReg s o := by
  cases o with
  | reg r =>
      have hne : r ≠ d := fun e => h (by simp [srcNames, e])
      simp [readReg, hne]
  | _ => rfl

theorem evalOperandN_setReg_ne {o : LOperand} (h : d ∉ srcNames o) (w' : Nat) :
    evalOperandN (s.setReg d c) w' o = evalOperandN s w' o := by
  cases o with
  | reg r =>
      have hne : r ≠ d := fun e => h (by simp [srcNames, e])
      simp [evalOperandN, hne]
  | _ => rfl

theorem getW_operandName_setReg_ne (hd0 : d ≠ "") {o : LOperand} (h : d ∉ srcNames o)
    (w' : Nat) :
    (s.setReg d c).getW (operandName o) w' = s.getW (operandName o) w' := by
  cases o with
  | reg r =>
      have hne : r ≠ d := fun e => h (by simp [srcNames, e])
      simp [operandName, hne]
  | _ => simp [operandName, Ne.symm hd0]

theorem immFirstN_setReg (o : String) (n : Nat) {b : LOperand} (h : d ∉ srcNames b) :
    immFirstN (s.setReg d c) d o n b = immFirstN s d o n b := by
  unfold immFirstN
  rw [evalOperandN_setReg_ne c h]
  cases evalOperandN s (widthFromTag o) b with
  | none => rfl
  | some vb => simp only [setReg_setReg_same]

/-- The width-aware step of an instruction with the one register destination `d` that no
    source names does not depend on the cell of `d`. -/
theorem lsemStepN_setReg_dst (hd0 : d ≠ "") (o : String) (srcs : List LOperand)
    (hs : ∀ x ∈ srcs, d ∉ srcNames x) :
    lsemStepN (.Lopn [.reg d] o srcs) (s.setReg d c) = lsemStepN (.Lopn [.reg d] o srcs) s := by
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨e, _ | ⟨f, r⟩⟩⟩⟩
  · simp [lsemStepN]
  · have ha := hs a (by simp)
    cases a with
    | reg r0 =>
        have hr : readReg (s.setReg d c) (.reg r0) = readReg s (.reg r0) :=
          readReg_setReg_ne c ha
        simp only [lsemStepN, hr, setReg_setReg_same]
    | arrIdx b x k =>
        have hb : b ≠ d := fun e => ha (by simp [srcNames, e])
        have hx : x ≠ d := fun e => ha (by simp [srcNames, e])
        simp only [lsemStepN, LstateN.getW_setReg_other s d b c 64 hb,
          LstateN.getW_setReg_other s d x c 64 hx, setReg_setReg_same]
    | _ => simp [lsemStepN, setReg_setReg_same]
  · have ha := hs a (by simp)
    have hb := hs b (by simp)
    simp only [lsemStepN, readReg_setReg_ne c ha, evalOperandN_setReg_ne c hb,
      setReg_setReg_same]
    cases a <;> simp [immFirstN_setReg c o _ hb]
  · have ha := hs a (by simp)
    have hb := hs b (by simp)
    have he := hs e (by simp)
    simp only [lsemStepN, getW_operandName_setReg_ne c hd0 ha, readReg_setReg_ne c hb,
      evalOperandN_setReg_ne c he, setReg_setReg_same]
  · simp [lsemStepN]

theorem getW_setReg_ne {r : String} (h : d ∉ srcNames (.reg r)) (w' : Nat) :
    (s.setReg d c).getW r w' = s.getW r w' := by
  have hne : r ≠ d := fun e => h (by simp [srcNames, e])
  simp [hne]

theorem lsemStepSh_setReg_dst (hd0 : d ≠ "") (o : String) (srcs : List LOperand)
    (hs : ∀ x ∈ srcs, d ∉ srcNames x) :
    lsemStepSh (.Lopn [.reg d] o srcs) (s.setReg d c) = lsemStepSh (.Lopn [.reg d] o srcs) s := by
  have hN := lsemStepN_setReg_dst (s := s) c hd0 o srcs hs
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨e, r⟩⟩⟩
  · simp only [lsemStepSh, sarStruct?]
    exact hN
  · cases a <;> simp only [lsemStepSh, sarStruct?] <;> exact hN
  · have ha := hs a (by simp)
    cases a <;> cases b <;> simp only [lsemStepSh, sarStruct?] <;>
      first
        | exact hN
        | (split_ifs <;>
            first
              | exact hN
              | simp only [readReg_setReg_ne c ha, setReg_setReg_same])
  · simp only [lsemStepSh, sarStruct?]
    exact hN

theorem lsemStepMC_setReg_dst (hd0 : d ≠ "") (o : String) (srcs : List LOperand)
    (hs : ∀ x ∈ srcs, d ∉ srcNames x) :
    lsemStepMC (.Lopn [.reg d] o srcs) (s.setReg d c) = lsemStepMC (.Lopn [.reg d] o srcs) s := by
  have hS := lsemStepSh_setReg_dst (s := s) c hd0 o srcs hs
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨e, _ | ⟨f, r⟩⟩⟩⟩
  · simp only [lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?, sbbhiStruct?]
    exact hS
  · cases a <;>
      simp only [lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?,
        sbbhiStruct?] <;> exact hS
  · have ha := hs a (by simp)
    have hb := hs b (by simp)
    cases a <;> cases b <;>
      simp only [lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?,
        sbbhiStruct?] <;>
      first
        | exact hS
        | (split_ifs <;>
            first
              | exact hS
              | simp only [readReg_setReg_ne c ha, getW_setReg_ne c hb, setReg_setReg_same])
  · have ha := hs a (by simp)
    have hb := hs b (by simp)
    have he := hs e (by simp)
    cases a <;> cases b <;> cases e <;>
      simp only [lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?,
        sbbhiStruct?] <;>
      first
        | exact hS
        | (split_ifs <;>
            first
              | exact hS
              | simp only [readReg_setReg_ne c ha, getW_setReg_ne c hb, getW_setReg_ne c he,
                  setReg_setReg_same])
  · simp only [lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?, sbbhiStruct?]
    exact hS

omit s in
theorem castStruct?_dst {o : String} {srcs : List LOperand} {dst a : String}
    (h : castStruct? (.Lopn [.reg d] o srcs) = some (dst, a)) :
    dst = d ∧ srcs = [.reg a] := by
  rcases srcs with _ | ⟨x, _ | ⟨y, r⟩⟩
  · simp [castStruct?] at h
  · cases x <;> simp only [castStruct?] at h
    · split_ifs at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, by rw [h.2]⟩
    all_goals cases h
  · simp [castStruct?] at h

omit s in
theorem movImmStruct?_dst {o : String} {srcs : List LOperand} {dst : String} {n : Nat}
    (h : movImmStruct? (.Lopn [.reg d] o srcs) = some (dst, n)) : dst = d := by
  obtain ⟨_, he⟩ := movImmStruct?_spec h
  simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at he
  exact he.1.1.symm

theorem lsemStepCast_setReg_dst (hd0 : d ≠ "") (o : String) (srcs : List LOperand)
    (cd : Option Nat) (hs : ∀ x ∈ srcs, d ∉ srcNames x) :
    lsemStepCast (.Lopn [.reg d] o srcs, cd) (s.setReg d c)
      = lsemStepCast (.Lopn [.reg d] o srcs, cd) s := by
  have hM := lsemStepMC_setReg_dst (s := s) c hd0 o srcs hs
  cases cd with
  | none =>
      rw [lsemStepCast_of_delegate _ _ (Or.inr rfl), lsemStepCast_of_delegate _ _ (Or.inr rfl)]
      exact hM
  | some w' =>
      cases hcs : castStruct? (.Lopn [.reg d] o srcs) with
      | some p =>
          obtain ⟨dst, a⟩ := p
          obtain ⟨rfl, rfl⟩ := castStruct?_dst hcs
          have ha := hs (.reg a) (by simp)
          simp only [lsemStepCast, hcs, readReg_setReg_ne c ha, setReg_setReg_same]
      | none =>
          cases hmi : movImmStruct? (.Lopn [.reg d] o srcs) with
          | some p =>
              obtain ⟨dst, n⟩ := p
              obtain rfl := movImmStruct?_dst hmi
              simp only [lsemStepCast, hcs, hmi, setReg_setReg_same]
          | none =>
              simp only [lsemStepCast, hcs, hmi]
              exact hM

end Overwrite

section OverwriteM

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (srcNames)

variable {d : String}

theorem loadStruct?_dst {o : String} {srcs : List LOperand} {dst base idx : String}
    (h : loadStruct? (.Lopn [.reg d] o srcs) = some (dst, base, idx)) :
    dst = d ∧ ∃ k, srcs = [.arrIdx base idx k] := by
  unfold loadStruct? at h
  split at h
  · next d' opn b' i' k heq =>
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
      split_ifs at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨heq.1.symm, k, heq.2.2⟩
  · cases h

theorem loadCStruct?_dst {o : String} {srcs : List LOperand} {dst base : String} {off : Nat}
    (h : loadCStruct? (.Lopn [.reg d] o srcs) = some (dst, base, off)) : dst = d := by
  unfold loadCStruct? at h
  split at h
  · next d' opn b' k heq =>
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
      split_ifs at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact h.1.symm.trans heq.1.symm
  · cases h

theorem storeCStruct?_reg_dst (o : String) (srcs : List LOperand) :
    storeCStruct? (.Lopn [.reg d] o srcs) = none := by
  unfold storeCStruct?
  split
  · next heq => simp at heq
  · rfl

theorem aluFlagOp?_srcs {o : String} {srcs : List LOperand} {tg : MemTag} {op : AluOp}
    {a b : LOperand} (h : aluFlagOp? (.Lopn [.reg d] o srcs, tg) = some (op, a, b)) :
    srcs = [a, b] := by
  unfold aluFlagOp? at h
  split at h
  · next d' opn a' b' heq =>
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
      split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
        (obtain ⟨-, rfl, rfl⟩ := h; exact heq.2.2)
  · cases h

theorem carryArgs?_dst {o : String} {srcs : List LOperand} {tg : MemTag} {op : CarryOp}
    {dst : String} {a b : LOperand}
    (h : carryArgs? (.Lopn [.reg d] o srcs, tg) = some (op, dst, a, b)) :
    dst = d ∧ srcs = [a, b] := by
  unfold carryArgs? at h
  split at h
  · next d' opn a' b' heq =>
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
      split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
        (obtain ⟨-, rfl, rfl, rfl⟩ := h; exact ⟨heq.1.symm, heq.2.2⟩)
  · cases h

theorem wideArgs?_dst {o : String} {srcs : List LOperand} {tg : MemTag} {wo : WideOp}
    (h : wideArgs? (.Lopn [.reg d] o srcs, tg) = some wo) :
    ∃ x b, wo = .mov d b ∧ srcs = [x, b] := by
  unfold wideArgs? at h
  split at h
  · next d' opn x' b' heq =>
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
      split_ifs at h
      simp only [Option.some.injEq] at h
      exact ⟨x', b', by rw [← h, heq.1], heq.2.2⟩
  · next heq => simp at heq
  · cases h

theorem movRegArgs?_dst {o : String} {srcs : List LOperand} {tg : MemTag} {dst src : String}
    (h : movRegArgs? (.Lopn [.reg d] o srcs, tg) = some (dst, src)) :
    dst = d ∧ srcs = [.reg src] := by
  unfold movRegArgs? at h
  split at h
  · next d' opn s' heq =>
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
      split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
        (obtain ⟨rfl, rfl⟩ := h; exact ⟨heq.1.symm, heq.2.2⟩)
  · cases h

variable {s : LstateM} {w : Nat} (c : BitVec w)

theorem setRegM_setReg_same {w' : Nat} (v : BitVec w') :
    (s.setReg d c).setReg d v = s.setReg d v := by
  simp only [LstateM.setReg, setReg_setReg_same]

/-- The memory step of an instruction with the one register destination `d` that no source
    names and that is neither an indexed store nor an array zeroing does not depend on the
    cell of `d`. -/
theorem lsemStepMem_setReg_dst (hd0 : d ≠ "") (o : String) (srcs : List LOperand)
    (tg : MemTag) (hs : ∀ x ∈ srcs, d ∉ srcNames x)
    (hst : storeStruct? (.Lopn [.reg d] o srcs) = none)
    (hz : zeroStruct? (.Lopn [.reg d] o srcs) = none)
    (hsi : storeImmStruct? (.Lopn [.reg d] o srcs) = none) :
    lsemStepMem (.Lopn [.reg d] o srcs, tg) (s.setReg d c)
      = lsemStepMem (.Lopn [.reg d] o srcs, tg) s := by
  have hC := fun cd => lsemStepCast_setReg_dst (s := s.reg) c hd0 o srcs cd hs
  have hreg : (s.setReg d c).reg = s.reg.setReg d c := rfl
  cases tg with
  | load w' n =>
      cases hl : loadStruct? (.Lopn [.reg d] o srcs) with
      | none =>
          simp only [lsemStepMem, hl, hreg, hC]
          rfl
      | some p =>
          obtain ⟨dst, base, idx⟩ := p
          obtain ⟨rfl, k, rfl⟩ := loadStruct?_dst hl
          have hi : dst ∉ srcNames (.reg idx) := fun hm =>
            hs (.arrIdx base idx k) (by simp) (by
              simp only [srcNames, List.mem_singleton] at hm
              simp [srcNames, hm])
          have ha : (s.setReg dst c).getArr base w' n = s.getArr base w' n := rfl
          simp only [lsemStepMem, hl, hreg, ha, getW_setReg_ne c hi, setRegM_setReg_same]
  | store w' n =>
      simp only [lsemStepMem, hst, hreg, hC]
      rfl
  | loadC =>
      cases hl : loadCStruct? (.Lopn [.reg d] o srcs) with
      | none => simp only [lsemStepMem, hl]
      | some p =>
          obtain ⟨dst, base, off⟩ := p
          obtain rfl := loadCStruct?_dst hl
          simp only [lsemStepMem, hl]
          exact congrArg (fun x => some (LstateM.nextPc x)) (setRegM_setReg_same c _)
  | storeC => simp only [lsemStepMem, storeCStruct?_reg_dst]
  | zero w' n => simp only [lsemStepMem, hz]
  | storeImm w' n => simp only [lsemStepMem, hsi]
  | reg cd =>
      simp only [lsemStepMem, hreg, hC]
      rfl

theorem carryStep_setReg_dst (op : CarryOp) {a b : LOperand} (ha : d ∉ srcNames a)
    (hb : d ∉ srcNames b) :
    carryStep op d a b (s.setReg d c) = carryStep op d a b s := by
  have hreg : (s.setReg d c).reg = s.reg.setReg d c := rfl
  unfold carryStep
  rw [hreg, evalOperandN_setReg_ne c ha, evalOperandN_setReg_ne c hb]
  cases evalOperandN s.reg 64 a <;> cases evalOperandN s.reg 64 b <;>
    first | rfl | (cases op <;> simp only [setRegM_setReg_same] <;> rfl)

/-- The straight-line step of the flag machine of an instruction with the one register
    destination `d` that no source names and that is neither an indexed store nor an array
    zeroing does not depend on the cell of `d`. -/
theorem stepMemF_setReg_dst (hd0 : d ≠ "") (o : String) (srcs : List LOperand)
    (tg : MemTag) (hs : ∀ x ∈ srcs, d ∉ srcNames x)
    (hst : storeStruct? (.Lopn [.reg d] o srcs) = none)
    (hz : zeroStruct? (.Lopn [.reg d] o srcs) = none)
    (hsi : storeImmStruct? (.Lopn [.reg d] o srcs) = none) :
    stepMemF (.Lopn [.reg d] o srcs, tg) (s.setReg d c)
      = stepMemF (.Lopn [.reg d] o srcs, tg) s := by
  have hreg : (s.setReg d c).reg = s.reg.setReg d c := rfl
  unfold stepMemF
  rw [lsemStepMem_setReg_dst c hd0 o srcs tg hs hst hz hsi]
  cases lsemStepMem (.Lopn [.reg d] o srcs, tg) s with
  | some b =>
      simp only [withALUFlags]
      cases ha : aluFlagOp? (.Lopn [.reg d] o srcs, tg) with
      | none => rfl
      | some p =>
          obtain ⟨op, x, y⟩ := p
          obtain rfl := aluFlagOp?_srcs ha
          simp only [hreg, evalOperandN_setReg_ne c (hs x (by simp)),
            evalOperandN_setReg_ne c (hs y (by simp))]
  | none =>
      simp only
      cases hk : carryArgs? (.Lopn [.reg d] o srcs, tg) with
      | some p =>
          obtain ⟨op, dst, x, y⟩ := p
          obtain ⟨rfl, rfl⟩ := carryArgs?_dst hk
          exact carryStep_setReg_dst c op (hs x (by simp)) (hs y (by simp))
      | none =>
          simp only
          cases hw : wideArgs? (.Lopn [.reg d] o srcs, tg) with
          | none => rfl
          | some wo =>
              obtain ⟨x, y, rfl, rfl⟩ := wideArgs?_dst hw
              simp only [wideStep, hreg, evalOperandN_setReg_ne c (hs y (by simp)),
                setRegM_setReg_same]

/-- **A written destination does not depend on its earlier cell.** The extended straight
    step of an instruction with the one register destination `d`, that no source names,
    that is neither the flag compare nor an indexed store nor an array zeroing, is the same
    from a state and from that state with any cell at `d`. -/
theorem fstepF_setReg_dst (hd0 : d ≠ "") (o : String) (srcs : List LOperand) (tg : MemTag)
    (zf : Bool) (hs : ∀ x ∈ srcs, d ∉ srcNames x)
    (hst : storeStruct? (.Lopn [.reg d] o srcs) = none)
    (hz : zeroStruct? (.Lopn [.reg d] o srcs) = none)
    (hsi : storeImmStruct? (.Lopn [.reg d] o srcs) = none)
    (hcmp : cmpArgs? (.Lopn [.reg d] o srcs, tg) = none) :
    fstepF (.Lopn [.reg d] o srcs, tg) (s.setReg d c) zf
      = fstepF (.Lopn [.reg d] o srcs, tg) s zf := by
  have hreg : (s.setReg d c).reg = s.reg.setReg d c := rfl
  unfold fstepF
  rw [hcmp]
  simp only
  cases hm : movRegArgs? (.Lopn [.reg d] o srcs, tg) with
  | some p =>
      obtain ⟨dst, src⟩ := p
      obtain ⟨rfl, rfl⟩ := movRegArgs?_dst hm
      simp only [hreg, readReg_setReg_ne c (hs (.reg src) (by simp)), setRegM_setReg_same]
  | none =>
      simp only
      rw [stepMemF_setReg_dst c hd0 o srcs tg hs hst hz hsi]

end OverwriteM

/-! ## 6. The step from two states that agree on the names read -/

section LiveStep

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower (fstepF_setLpc)

/-- **The step from two states that agree on the names an instruction reads**, at any two
    program counters. If the states agree on the registers `readsI` lists, on the arrays,
    the word memory and the two flags, a step from the first is matched by a step from the
    second with the same zero flag; every register is equal in the two results or, in
    both, the register of the state it came from; the arrays, the word memory and the
    flags of the results are equal. -/
theorem fstepF_liveStep {i : LinstrRM} {s t s₁ : LstateM} {zf z₁ : Bool}
    (hreg : ∀ r, readsI i.1 r → s.reg.lvm r = t.reg.lvm r) (hA : s.larr = t.larr)
    (hM : s.lmem = t.lmem) (hC : s.cf = t.cf) (hO : s.of = t.of)
    (hstep : fstepF i s zf = some (s₁, z₁)) :
    ∃ t₁, fstepF i t zf = some (t₁, z₁)
      ∧ (∀ r, s₁.reg.lvm r = t₁.reg.lvm r
          ∨ (s₁.reg.lvm r = s.reg.lvm r ∧ t₁.reg.lvm r = t.reg.lvm r))
      ∧ s₁.larr = t₁.larr ∧ s₁.lmem = t₁.lmem ∧ s₁.cf = t₁.cf ∧ s₁.of = t₁.of := by
  have hMA : MAgree (readsI i.1) s (t.setLpc s.lpc) := ⟨⟨rfl, hreg⟩, hA, hM, hC, hO⟩
  have h := fstepF_congr i hMA zf
  rw [hstep] at h
  generalize hq : fstepF i (t.setLpc s.lpc) zf = q at h
  cases h with
  | some hf =>
      rename_i b
      obtain ⟨⟨hN, hA', hM', hC', hO'⟩, hz⟩ := hf
      have hz' : b.2 = z₁ := hz.symm
      refine ⟨b.1.setLpc (t.lpc + 1), ?_, fun r => hN.2 r, hA', hM', hC', hO'⟩
      have hstep' := fstepF_setLpc i (t.setLpc s.lpc) zf t.lpc
      rw [hq, Option.map_some, hz'] at hstep'
      exact hstep'

end LiveStep

/-! ## 7. Backward dead-move elimination -/

section DeadElim

open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad (isMovMnem elimReloads)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler (scheduleBody)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower (EqPc)
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.BlocksCfg

/-- Two states of the flag machine agree up to the live set `L`: they hold the same cell in
    every register that is not a physical register or that `L` lists, and they have the
    same arrays, word memory and flags. The program counters are unrelated. -/
def LiveAgreeM (L : List String) (s t : LstateM) : Prop :=
  (∀ r, (isPhysGP r = false ∨ L.contains r = true) → s.reg.lvm r = t.reg.lvm r)
    ∧ s.larr = t.larr ∧ s.lmem = t.lmem ∧ s.cf = t.cf ∧ s.of = t.of

/-- The names of the operands that `readsI` lists for an instruction: the names of its
    sources and the base registers of its cell operands. -/
def readNames : LinstrR → List String
  | .Lopn ds _ ss => ss.flatMap srcNames ++ (ds ++ ss).filterMap cellBase
  | _ => []

theorem readsI_cases {i : LinstrR} {r : String} (h : readsI i r) :
    r = "" ∨ (r = "RDX" ∧ readsRdx i = true) ∨ r ∈ readNames i := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · cases i with
    | Lopn ds o ss => exact Or.inr (Or.inr (List.mem_append.2 h))
    | _ => exact absurd h (by simp)

/-- An instruction that reads `RDX` implicitly is not recognised by the pass. -/
theorem isRecognizedOpn_of_readsRdx {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : readsRdx (.Lopn ds o ss) = true) : isRecognizedOpn o = false := by
  simp only [readsRdx, rdxOp, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  have hu := h.1
  by_cases hc : '^' ∈ o.toList
  · have hT : ∃ rest, o.toList.takeWhile (· != '^') = 'M' :: 'U' :: 'L' :: 'X' :: rest := by
      have hc' : o.toList.contains '^' = true := by simpa using hc
      unfold X86Backend.LprogAsmPrinter.untagCaret stripWidthTag at hu
      simp only [hc', if_true] at hu
      generalize List.takeWhile (fun x => x != '^') o.toList = T at hu ⊢
      split_ifs at hu
      · rcases hu with (hu | hu) | hu <;> have h2 := congrArg String.toList hu <;>
          simp only [String.toList_append, String.toList_ofList] at h2
        · exfalso
          rcases T with _ | ⟨c, _ | ⟨d, T⟩⟩ <;> simp at h2
          have := congrArg List.length h2.2.2
          simp at this
        · rw [toList_withWidthTag_64] at h2
          exact ⟨[], List.append_cancel_right h2⟩
        · rw [toList_withWidthTag_64] at h2
          exact ⟨['M', 'E', 'M'], by simpa using List.append_cancel_right h2⟩
      · rcases hu with (hu | hu) | hu <;> have h2 := congrArg String.toList hu <;>
          simp only [String.toList_ofList] at h2
        · exact ⟨[], by simpa using h2⟩
        · rw [toList_withWidthTag_64] at h2
          exact ⟨[':', '6', '4'], by simpa using h2⟩
        · rw [toList_withWidthTag_64] at h2
          exact ⟨['M', 'E', 'M', ':', '6', '4'], by simpa using h2⟩
    obtain ⟨rest, hT⟩ := hT
    have hL : o.toList = 'M' :: 'U' :: 'L' :: 'X' ::
        (rest ++ o.toList.dropWhile (· != '^')) := by
      grind only [=_ List.cons_append, List.takeWhile_append_dropWhile]
    refine isRecognizedOpn_MULX ?_
    rw [X86Backend.WellFormedX86.isPrefixOf_eq_hasPrefix]
    unfold X86Backend.LprogAsmPrinter.stripAbiTag
    split
    · rw [hL]
      simp [hasPrefix, List.takeWhile]
    · unfold stripWidthTag
      rw [if_pos (by simpa using hc), hT]
      simp [hasPrefix]
  · rw [X86Backend.LprogAsmPrinter.untagCaret_of_caret_free hc] at hu
    rcases hu with (rfl | rfl) | rfl <;>
      exact isRecognizedOpn_MULX (by
        rw [X86Backend.WellFormedX86.isPrefixOf_eq_hasPrefix]
        decide +kernel)

/-- The check of an instruction for dead-move elimination. The instruction passes
    `cpRegOKB`. If it is an `Lopn` with a recognised mnemonic, every physical register
    among its `readNames` is one of its `instrUses`, and if it has a killing definition it
    has one destination and is neither an indexed store nor the flag compare. -/
def deadOKB (i : Linstr) : Bool :=
  cpRegOKB i &&
    (match i.li_i with
     | .Lopn dsts opn srcs =>
         !isRecognizedOpn opn ||
           ((readNames i.li_i).all (fun r => !isPhysGP r || (instrUses dsts opn srcs).contains r)
             && ((fullDefsOf dsts opn).isEmpty
                  || (dsts.length == 1 && opn != "STOREIDX" && opn != withWidthTag 64 "CMP")))
     | _ => true)

/-- **A dropped move keeps the agreement up to the live set.** A candidate move that passes
    `cpRegOKB` and is a self-copy or writes a register outside the live set steps to a
    state that agrees with the state the other run stays in, and keeps the zero flag. -/
theorem liveAgreeM_drop {Lr : List String} {i : Linstr} (hc : cpRegOKB i = true)
    {d : String} {src : LOperand} {ww : Nat} (hcs : moveShape i = some (d, src, ww))
    (hdr : ((ww == 64 && src == LOperand.reg d) || !(Lr.contains d)) = true) (tg : MemTag)
    {s t s₁ : LstateM} {zf z₁ : Bool} (h : LiveAgreeM Lr s t)
    (hstep : fstepF (i.li_i, tg) s zf = some (s₁, z₁)) : z₁ = zf ∧ LiveAgreeM Lr s₁ t := by
  obtain ⟨opn, hi, hpd, hfs, hstrip⟩ := moveShape_inv hcs
  simp only [cpRegOKB, hi, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, Bool.or_eq_false_iff] at hc
  have h2 : isMovMnem opn = true ∧ notImmB src = true := by
    rcases hc.2 with hno | hyes
    · rcases hstrip with e | e
      · exact absurd e hno.1
      · exact absurd e hno.2
    · exact hyes
  obtain ⟨k, rfl⟩ : ∃ k, src = LOperand.reg k := by
    cases src with
    | reg k => exact ⟨k, rfl⟩
    | imm k => exact absurd h2.2 (by simp [notImmB])
    | arr b k => simp [isFactSrc] at hfs
    | arrIdx b x k => simp [isFactSrc] at hfs
  rw [hi, fstepF_reload h2.1, Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  refine ⟨rfl, fun r hr => ?_, h.2⟩
  rw [lvm_setReg_nextPcM]
  by_cases hrd : r = d
  · subst hrd
    rw [if_pos rfl]
    rcases (Bool.or_eq_true _ _).mp hdr with hself | hdead
    · have hk : k = r := by simpa using ((Bool.and_eq_true _ _).mp hself).2
      subst hk
      exact h.1 k hr
    · exfalso
      have hnc : Lr.contains r = false := by simpa using hdead
      rcases hr with hp | hm
      · rw [hp] at hpd
        exact absurd hpd (by simp)
      · rw [hnc] at hm
        exact absurd hm (by simp)
  · rw [if_neg hrd]
    exact h.1 r hr

/-- **A kept recognised instruction keeps the agreement up to the live set.** From two
    states that agree up to the live set before an instruction that passes `deadOKB`, a
    step from the first is matched by a step from the second with the same zero flag, to
    states that agree up to the live set after it. -/
theorem liveAgreeM_keep {Lr : List String} {i : Linstr} {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} (hi : i.li_i = .Lopn dsts opn srcs)
    (hrec : isRecognizedOpn opn = true) (hc : deadOKB i = true) (tg : MemTag)
    {s t s₁ : LstateM} {zf z₁ : Bool}
    (h : LiveAgreeM (addRegs (Lr.filter fun r => !((fullDefsOf dsts opn).contains r))
      (instrUses dsts opn srcs)) s t)
    (hstep : fstepF (.Lopn dsts opn srcs, tg) s zf = some (s₁, z₁)) :
    ∃ t₁, fstepF (.Lopn dsts opn srcs, tg) t zf = some (t₁, z₁) ∧ LiveAgreeM Lr s₁ t₁ := by
  obtain ⟨hR, hA, hM, hC, hO⟩ := h
  simp only [deadOKB, hi, hrec, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
    beq_iff_eq] at hc
  obtain ⟨-, hreads, hfull⟩ := hc
  have hcov : ∀ r, readsI (.Lopn dsts opn srcs) r → isPhysGP r = true →
      (instrUses dsts opn srcs).contains r = true := by
    intro r hr hp
    rcases readsI_cases hr with rfl | ⟨-, hx⟩ | hm
    · exact absurd hp (by simp [isPhysGP, physGPs])
    · rw [isRecognizedOpn_of_readsRdx hx] at hrec
      exact absurd hrec (by simp)
    · rcases hreads r hm with hn | hu
      · rw [hp] at hn
        exact absurd hn (by simp)
      · exact hu
  have huse : ∀ r, (instrUses dsts opn srcs).contains r = true →
      s.reg.lvm r = t.reg.lvm r :=
    fun r hr => hR r (Or.inr (contains_addRegs_right _ _ hr))
  have hreg : ∀ r, readsI (.Lopn dsts opn srcs) r → s.reg.lvm r = t.reg.lvm r := by
    intro r hr
    by_cases hp : isPhysGP r = true
    · exact huse r (hcov r hr hp)
    · exact hR r (Or.inl (by simpa using hp))
  obtain ⟨t₁, ht, hN, hA', hM', hC', hO'⟩ :=
    fstepF_liveStep (i := (.Lopn dsts opn srcs, tg)) hreg hA hM hC hO hstep
  refine ⟨t₁, ht, fun r hr => ?_, hA', hM', hC', hO'⟩
  rcases hN r with e | ⟨e1, e2⟩
  · exact e
  by_cases hu : (instrUses dsts opn srcs).contains r = true
  · rw [e1, e2]
    exact huse r hu
  by_cases hfd : (fullDefsOf dsts opn).contains r = true
  · have hmem : r ∈ fullDefsOf dsts opn := by simpa using hfd
    rcases hfull with he | ⟨⟨hlen, hns⟩, hnc⟩
    · rw [List.isEmpty_iff.1 he] at hmem
      exact absurd hmem (by simp)
    have hrd : r ∈ regDefsOf dsts := by
      unfold fullDefsOf at hmem
      split at hmem
      · exact hmem
      · exact absurd hmem (by simp)
    obtain ⟨x, rfl⟩ : ∃ x, dsts = [x] := List.length_eq_one_iff.1 hlen
    have hx : x = LOperand.reg r ∧ isPhysGP r = true := by
      cases x with
      | reg n =>
          by_cases hn : isPhysGP n = true
          · simp only [regDefsOf, List.filterMap_cons, hn, if_true, List.filterMap_nil,
              List.mem_singleton] at hrd
            exact ⟨by rw [hrd], hrd ▸ hn⟩
          · simp [regDefsOf, hn] at hrd
      | _ => simp [regDefsOf] at hrd
    obtain ⟨rfl, hp⟩ := hx
    have hd0 : r ≠ "" := fun e => by
      rw [e] at hp
      exact absurd hp (by simp [isPhysGP, physGPs])
    have hs : ∀ x ∈ srcs, r ∉ srcNames x := fun x hx hm =>
      hu (hcov r (readsI_src (List.mem_flatMap.2 ⟨x, hx, hm⟩)) hp)
    have hst : storeStruct? (.Lopn [.reg r] opn srcs) = none := by
      unfold storeStruct?
      split
      · rename_i heq
        injection heq with _ ho _
        rw [if_neg (ho ▸ hns)]
      · rfl
    have hcmp : cmpArgs? (.Lopn [.reg r] opn srcs, tg) = none := by
      unfold cmpArgs?
      split
      · rename_i heq
        injection heq with _ ho _
        rw [if_neg (ho ▸ hnc)]
      · rfl
    have hz : zeroStruct? (.Lopn [.reg r] opn srcs) = none := by
      simp only [zeroStruct?]
      split_ifs with ho
      · subst ho
        have hw : isDstWriteOnly "ZEROARR" = false := by decide +kernel
        simp [fullDefsOf, hw] at hmem
      · rfl
    have hsi : storeImmStruct? (.Lopn [.reg r] opn srcs) = none := by
      unfold storeImmStruct?
      split
      · rename_i heq
        simp only [LinstrR.Lopn.injEq] at heq
        obtain ⟨-, rfl, -⟩ := heq
        split_ifs with ho
        · subst ho
          have hw : isDstWriteOnly "STOREIMM" = false := by decide +kernel
          simp [fullDefsOf, hw] at hmem
        · rfl
      · rfl
    have hset :=
      fstepF_setReg_dst (s := t) (s.reg.lvm r).2 hd0 opn srcs tg zf hs hst hz hsi hcmp
    have hreg' : ∀ q, readsI (.Lopn [.reg r] opn srcs) q →
        s.reg.lvm q = (t.setReg r (s.reg.lvm r).2).reg.lvm q := by
      intro q hq
      have hqr : q ≠ r := fun e => hu (e ▸ hcov q hq (e ▸ hp))
      have e : (t.setReg r (s.reg.lvm r).2).reg.lvm q = t.reg.lvm q := by
        simp [LstateM.setReg, LstateN.setReg, hqr]
      rw [e]
      exact hreg q hq
    obtain ⟨t₁', ht', hN', -⟩ :=
      fstepF_liveStep (i := (.Lopn [.reg r] opn srcs, tg)) (t := t.setReg r (s.reg.lvm r).2)
        hreg' hA hM hC hO hstep
    rw [hset, ht, Option.some.injEq, Prod.mk.injEq] at ht'
    obtain ⟨rfl, -⟩ := ht'
    rcases hN' r with e | ⟨e1', e2'⟩
    · exact e
    · rw [e1', e2']
      simp [LstateM.setReg, LstateN.setReg]
  · rw [e1, e2]
    rcases hr with hp | hm
    · exact hR r (Or.inl hp)
    · refine hR r (Or.inr (contains_addRegs_left _ _ ?_))
      have hmem : r ∈ Lr := by simpa using hm
      have hfil : r ∈ Lr.filter (fun x => !((fullDefsOf dsts opn).contains x)) :=
        List.mem_filter.mpr ⟨hmem, by simpa using hfd⟩
      simpa using hfil

/-- **Dead-move elimination is a forward simulation up to the live set, over the extended
    straight fold.** For a body that passes `deadOKB` and two states that agree up to the
    live set the pass computes at the head of the body, a run of the body from the first
    is matched by a run of the swept body from the second, with the same zero flag, to
    states that agree up to the live set at the end. -/
theorem deadElim_foldr_runStraightF (tag : LinstrR → MemTag) (body : Lcmd)
    (hb : ∀ i ∈ body, deadOKB i = true) :
    ∀ (Lend : List String) (s t : LstateM) (zf : Bool),
      LiveAgreeM (body.foldr deadElimStep (Lend, [])).1 s t →
      ∀ (s₂ : LstateM) (z₂ : Bool),
        runStraightF (body.map fun i => (i.li_i, tag i.li_i)) s zf = some (s₂, z₂) →
        ∃ t₂, runStraightF
            ((body.foldr deadElimStep (Lend, [])).2.map fun i => (i.li_i, tag i.li_i)) t zf
              = some (t₂, z₂)
          ∧ LiveAgreeM Lend s₂ t₂ := by
  induction body with
  | nil =>
    intro Lend s t zf h s₂ z₂ hrun
    simp only [List.map_nil, runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨t, rfl, h⟩
  | cons i rest ih =>
    intro Lend s t zf h s₂ z₂ hrun
    have hci := hb i List.mem_cons_self
    have ih' := ih (fun j hj => hb j (List.mem_cons_of_mem _ hj)) Lend
    simp only [List.map_cons, runStraightF_cons] at hrun
    obtain ⟨Lr, outR, hP⟩ : ∃ a b, rest.foldr deadElimStep (Lend, []) = (a, b) := ⟨_, _, rfl⟩
    rw [hP] at ih'
    rw [List.foldr_cons, hP] at h ⊢
    cases hst : fstepF (i.li_i, tag i.li_i) s zf with
    | none => rw [hst] at hrun; exact absurd hrun (by simp)
    | some bz =>
      obtain ⟨s₁, z₁⟩ := bz
      rw [hst, Option.bind_some] at hrun
      have hcases :
          (∃ dsts opn srcs, i.li_i = LinstrR.Lopn dsts opn srcs ∧ isRecognizedOpn opn = true)
          ∨ (∀ (live : List String) (acc : Lcmd),
              deadElimStep i (live, acc) = (physGPs, i :: acc)) := by
        cases hLi : i.li_i with
        | Lopn dsts opn srcs =>
          by_cases hr : isRecognizedOpn opn = true
          · exact Or.inl ⟨dsts, opn, srcs, rfl, hr⟩
          · refine Or.inr (fun live acc => deadElimStep_barrier i live acc ?_)
            intro d o sc he
            rw [hLi] at he
            injection he with _ h2 _
            rw [← h2]
            simpa using hr
        | _ =>
          exact Or.inr (fun live acc => deadElimStep_barrier i live acc (by
            intro d o sc he; rw [hLi] at he; exact absurd he (by simp)))
      rcases hcases with ⟨dsts, opn, srcs, hLi, hrec⟩ | hbar
      · have hkeep : deadElimStep i (Lr, outR)
              = (addRegs (Lr.filter fun r => !((fullDefsOf dsts opn).contains r))
                  (instrUses dsts opn srcs), i :: outR) →
            ∃ t₂, runStraightF
                ((deadElimStep i (Lr, outR)).2.map fun i => (i.li_i, tag i.li_i)) t zf
                  = some (t₂, z₂)
              ∧ LiveAgreeM Lend s₂ t₂ := by
          intro hk
          rw [hk] at h ⊢
          dsimp only at h ⊢
          rw [hLi] at hst
          obtain ⟨t₁, hts, hag⟩ := liveAgreeM_keep hLi hrec hci _ h hst
          simp only [List.map_cons, runStraightF_cons, hLi, hts, Option.bind_some]
          exact ih' s₁ t₁ z₁ hag s₂ z₂ hrun
        cases hcs : moveShape i with
        | none => exact hkeep (deadElimStep_keep_none Lr outR hLi hrec hcs)
        | some q =>
          obtain ⟨d, src, ww⟩ := q
          by_cases hdr : ((ww == 64 && src == LOperand.reg d) || !(Lr.contains d)) = true
          · rw [deadElimStep_drop Lr outR hLi hrec hcs hdr] at h ⊢
            dsimp only at h ⊢
            have hcp : cpRegOKB i = true := by
              simp only [deadOKB, Bool.and_eq_true] at hci
              exact hci.1
            obtain ⟨rfl, hag⟩ := liveAgreeM_drop hcp hcs hdr _ h hst
            exact ih' s₁ t z₁ hag s₂ z₂ hrun
          · exact hkeep (deadElimStep_keep_some Lr outR hLi hrec hcs (by simpa using hdr))
      · rw [hbar Lr outR] at h ⊢
        dsimp only at h ⊢
        obtain ⟨hR, hA, hM, hC, hO⟩ := h
        have hall : ∀ r, s.reg.lvm r = t.reg.lvm r := fun r => hR r (by
          by_cases hp : isPhysGP r = true
          · exact Or.inr hp
          · exact Or.inl (by simpa using hp))
        obtain ⟨t₁, hts, hN, hA', hM', hC', hO'⟩ :=
          fstepF_liveStep (fun r _ => hall r) hA hM hC hO hst
        simp only [List.map_cons, runStraightF_cons, hts, Option.bind_some]
        refine ih' s₁ t₁ z₁ ⟨fun r _ => ?_, hA', hM', hC', hO'⟩ s₂ z₂ hrun
        rcases hN r with e | ⟨e1, e2⟩
        · exact e
        · rw [e1, e2]
          exact hall r

/-- **Dead-move elimination over the extended straight fold.** For a body that passes
    `deadOKB`, a run of the body is matched by a run of the body without its dead moves
    from the same state, with the same zero flag and final states equal up to the program
    counter. -/
theorem deadElim_runStraightF (tag : LinstrR → MemTag) (body : Lcmd)
    (hb : ∀ i ∈ body, deadOKB i = true) : DeadElimSim tag body := by
  intro s zf s₂ z₂ hrun
  obtain ⟨t₂, ht, hR, hA, hM, hC, hO⟩ :=
    deadElim_foldr_runStraightF tag body hb physGPs s s zf
      ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ s₂ z₂ hrun
  refine ⟨t₂, ht, ?_⟩
  have hl : s₂.reg.lvm = t₂.reg.lvm := funext fun r => hR r (by
    by_cases hp : isPhysGP r = true
    · exact Or.inr hp
    · exact Or.inl (by simpa using hp))
  obtain ⟨⟨lvm, lpc⟩, larr, lmem, cf, of⟩ := s₂
  obtain ⟨⟨lvm', lpc'⟩, larr', lmem', cf', of'⟩ := t₂
  simp only at hl hA hM hC hO
  subst hl hA hM hC hO
  rfl

/-- **Copy propagation over the extended straight fold, for register facts.** For a
    tagging that depends on destinations and mnemonic only, a body that passes `cpRegOKB`
    and whose propagated body passes `deadOKB`, a run of the body is matched by a run of
    the copy-propagated body. -/
theorem copyPropSim_of_deadOKB (tag : LinstrR → MemTag) (hT : TagShape tag) (body : Lcmd)
    (hb : ∀ i ∈ body, cpRegOKB i = true)
    (hd : ∀ i ∈ propagateAux [] body, deadOKB i = true) : CopyPropSim tag body :=
  copyPropSim_of_deadElimSim tag hT body hb (deadElim_runStraightF tag _ hd)

/-- **The check of the optimiser on a body, for register facts**: every instruction passes
    `keepOKB` and has register destinations, and on every straight segment the body after
    the first three stages passes `cpRegOKB` and its propagated body passes `deadOKB`. -/
def optBlocksRegOKB (tag : LinstrR → MemTag) (body : List Linstr) : Bool :=
  (body.all fun i => keepOKB (i.li_i, tag i.li_i) && dstsRegB i.li_i) &&
    (splitStraightRuns body).all fun seg =>
      !bodyIsStraightLine seg ||
        ((scheduleBody (reloadElimBody (elimReloads seg))).all cpRegOKB &&
          (propagateAux [] (scheduleBody (reloadElimBody (elimReloads seg)))).all deadOKB)

/-- **Soundness of the check: the basic-block optimiser on whole bodies of the flag
    machine, for register facts.** For a tagging that depends on destinations and mnemonic
    only and a body that passes `optBlocksRegOKB`, every halting run of `lsemFuelMemFk ck`
    on the tagged body from program counter `0` is matched by a halting run of the tagged
    optimised body from the same state with at most the same fuel, to a state with the
    same function name and zero flag and a base equal up to the program counter. -/
theorem optBlocksRegOKB_sound {ck : Bool} {tag : LinstrR → MemTag} (hT : TagShape tag)
    {body : List Linstr} (h : optBlocksRegOKB tag body = true) (fn : String) :
    WholeBodySim ck (fun _ => True) fn (body.map fun i => (i.li_i, tag i.li_i))
      ((optimizeBasicBlocks body).map fun i => (i.li_i, tag i.li_i)) := by
  simp only [optBlocksRegOKB, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  refine optimizeBasicBlocks_wholeBodySim_of_copyPropSim tag body (fun i hi => (h.1 i hi).1)
    (fun i hi => (h.1 i hi).2) (fun seg hs hsl => ?_) fn
  rcases h.2 seg hs with hn | ⟨h1, h2⟩
  · rw [hsl] at hn
    exact absurd hn (by simp)
  · exact copyPropSim_of_deadOKB tag hT _ h1 h2

end DeadElim

end CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CopyPropCfg
