/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin

@[expose] public section

set_option autoImplicit false

/-!
# The names a step writes

`dstNames i` is the list of register names the destinations of an `Lopn` instruction name.
A step of each layer of the flag machine leaves every register and every array outside
`dstNames` of its instruction: `lsemStepN`, `lsemStepSh`, `lsemStepMC`, `lsemStepCast`,
`lsemStepMem`, `stepMemF` and `fstepF`.

## Main results

* `dstNames`, `dstNames_sub`: the destination names, a sublist of the instruction's names.
* `lsemStepN_lvm`, `lsemStepSh_lvm`, `lsemStepMC_lvm`, `lsemStepCast_lvm`,
  `lsemStepMem_frame`, `stepMemF_frame`, `fstepF_frame`: a step leaves every register and
  array its instruction does not name; the `_dst` forms (`fstepF_frame_dst`, ...): a step
  leaves every register and array its instruction does not write (`dstNames`).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM LstateM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (stepMemF withALUFlags
  withALUFlags_reg withALUFlags_larr carryStep wideStep wideArgs? WideOp)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (fstepF)

/-! ## The names an instruction writes -/

/-- The register names an instruction's wire writes: the operand names of the
    destinations of an `Lopn`; no name for any other instruction. -/
def dstNames : LinstrR → List String
  | .Lopn d _ _ => d.flatMap opNames
  | _ => []

theorem dstNames_sub {i : LinstrR} {r : String} (h : r ∈ dstNames i) : r ∈ instrNames i := by
  cases i <;> simp_all [dstNames, instrNames]

set_option hygiene false in
/-- Prove that the first name a recogniser returns is a destination name. -/
local macro "recog_dst" : tactic =>
  `(tactic| (
      split at h
      · split at h
        · cases h; simp [dstNames, opNames]
        · simp at h
      · simp at h))

theorem sarStruct?_dst {i : LinstrR} {p : String × String × Nat}
    (h : JasminLsemShift.sarStruct? i = some p) : p.1 ∈ dstNames i := by
  unfold JasminLsemShift.sarStruct? at h; recog_dst

theorem mulhiStruct?_dst {i : LinstrR} {p : String × String × String}
    (h : JasminLsemMulCarry.mulhiStruct? i = some p) : p.1 ∈ dstNames i := by
  unfold JasminLsemMulCarry.mulhiStruct? at h; recog_dst

theorem adcxStruct?_dst {i : LinstrR} {p : String × String × String × String}
    (h : JasminLsemMulCarry.adcxStruct? i = some p) : p.1 ∈ dstNames i := by
  unfold JasminLsemMulCarry.adcxStruct? at h; recog_dst

theorem adcxhiStruct?_dst {i : LinstrR} {p : String × String × String × String}
    (h : JasminLsemMulCarry.adcxhiStruct? i = some p) : p.1 ∈ dstNames i := by
  unfold JasminLsemMulCarry.adcxhiStruct? at h; recog_dst

theorem sbbStruct?_dst {i : LinstrR} {p : String × String × String × String}
    (h : JasminLsemMulCarry.sbbStruct? i = some p) : p.1 ∈ dstNames i := by
  unfold JasminLsemMulCarry.sbbStruct? at h; recog_dst

theorem sbbhiStruct?_dst {i : LinstrR} {p : String × String × String × String}
    (h : JasminLsemMulCarry.sbbhiStruct? i = some p) : p.1 ∈ dstNames i := by
  unfold JasminLsemMulCarry.sbbhiStruct? at h; recog_dst

theorem castStruct?_dst {i : LinstrR} {p : String × String}
    (h : JasminLsemCast.castStruct? i = some p) : p.1 ∈ dstNames i := by
  unfold JasminLsemCast.castStruct? at h; recog_dst

theorem movImmStruct?_dst {i : LinstrR} {p : String × Nat}
    (h : JasminLsemCast.movImmStruct? i = some p) : p.1 ∈ dstNames i := by
  unfold JasminLsemCast.movImmStruct? at h
  split at h
  · cases h; simp [dstNames, opNames]
  · simp at h

theorem loadStruct?_dst {i : LinstrR} {p : String × String × String}
    (h : JasminLsemMem.loadStruct? i = some p) : p.1 ∈ dstNames i := by
  unfold JasminLsemMem.loadStruct? at h; recog_dst

theorem storeStruct?_dst {i : LinstrR} {p : String × String × String × String}
    (h : JasminLsemMem.storeStruct? i = some p) : p.1 ∈ dstNames i := by
  unfold JasminLsemMem.storeStruct? at h; recog_dst

theorem loadCStruct?_dst {i : LinstrR} {p : String × String × Nat}
    (h : JasminLsemMem.loadCStruct? i = some p) : p.1 ∈ dstNames i := by
  unfold JasminLsemMem.loadCStruct? at h; recog_dst

theorem zeroStruct?_dst {i : LinstrR} {d : String}
    (h : JasminLsemMem.zeroStruct? i = some d) : d ∈ dstNames i := by
  unfold JasminLsemMem.zeroStruct? at h; recog_dst

theorem lsemStepN_lvm_dst {i : LinstrR} {s t : LstateN} (h : lsemStepN i s = some t)
    {r : String} (hr : r ∉ dstNames i) : t.lvm r = s.lvm r := by
  unfold lsemStepN at h
  simp only [immFirstN] at h
  repeat' split at h
  all_goals first
    | (cases h; simp_all [dstNames, opNames, LstateN.setReg, LstateN.nextPc])
    | (obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.1 h
       simp_all [dstNames, opNames, LstateN.setReg, LstateN.nextPc])
    | simp at h

theorem setReg_nextPc_lvm {s : LstateN} {d r : String} {w : Nat} (v : BitVec w)
    (h : r ≠ d) : ((s.setReg d v).nextPc).lvm r = s.lvm r := by
  simp [LstateN.setReg, LstateN.nextPc, h]

theorem lsemStepSh_lvm_dst {i : LinstrR} {s t : LstateN}
    (h : JasminLsemShift.lsemStepSh i s = some t) {r : String}
    (hr : r ∉ dstNames i) : t.lvm r = s.lvm r := by
  unfold JasminLsemShift.lsemStepSh at h
  split at h
  · rename_i p hp
    have hd := sarStruct?_dst hp
    split at h
    · cases h
      exact setReg_nextPc_lvm _ fun he => hr (he ▸ hd)
    · cases h
  · exact lsemStepN_lvm_dst h hr

theorem lsemStepMC_lvm_dst {i : LinstrR} {s t : LstateN}
    (h : JasminLsemMulCarry.lsemStepMC i s = some t) {r : String}
    (hr : r ∉ dstNames i) : t.lvm r = s.lvm r := by
  unfold JasminLsemMulCarry.lsemStepMC at h
  split at h
  · rename_i p hp
    have hd := mulhiStruct?_dst hp
    repeat' split at h
    all_goals first | (cases h; exact setReg_nextPc_lvm _ fun he => hr (he ▸ hd)) | cases h
  split at h
  · rename_i p hp
    have hd := adcxStruct?_dst hp
    repeat' split at h
    all_goals first | (cases h; exact setReg_nextPc_lvm _ fun he => hr (he ▸ hd)) | cases h
  split at h
  · rename_i p hp
    have hd := adcxhiStruct?_dst hp
    repeat' split at h
    all_goals first | (cases h; exact setReg_nextPc_lvm _ fun he => hr (he ▸ hd)) | cases h
  split at h
  · rename_i p hp
    have hd := sbbStruct?_dst hp
    repeat' split at h
    all_goals first | (cases h; exact setReg_nextPc_lvm _ fun he => hr (he ▸ hd)) | cases h
  split at h
  · rename_i p hp
    have hd := sbbhiStruct?_dst hp
    repeat' split at h
    all_goals first | (cases h; exact setReg_nextPc_lvm _ fun he => hr (he ▸ hd)) | cases h
  exact lsemStepSh_lvm_dst h hr

theorem lsemStepCast_lvm_dst {i : LinstrR} {cd : Option Nat} {s t : LstateN}
    (h : JasminLsemCast.lsemStepCast (i, cd) s = some t) {r : String}
    (hr : r ∉ dstNames i) : t.lvm r = s.lvm r := by
  unfold JasminLsemCast.lsemStepCast at h
  split at h
  · rename_i dst a heq _
    have hd := castStruct?_dst heq
    split at h
    · cases h; exact setReg_nextPc_lvm _ fun he => hr (he ▸ hd)
    · cases h
  · split at h
    · rename_i dst n heq _
      have hd := movImmStruct?_dst heq
      cases h; exact setReg_nextPc_lvm _ fun he => hr (he ▸ hd)
    · exact lsemStepMC_lvm_dst h hr

theorem lsemStepN_lvm {i : LinstrR} {s t : LstateN} (h : lsemStepN i s = some t) {r : String}
    (hr : r ∉ instrNames i) : t.lvm r = s.lvm r :=
  lsemStepN_lvm_dst h fun h' => hr (dstNames_sub h')

theorem lsemStepSh_lvm {i : LinstrR} {s t : LstateN}
    (h : JasminLsemShift.lsemStepSh i s = some t) {r : String}
    (hr : r ∉ instrNames i) : t.lvm r = s.lvm r :=
  lsemStepSh_lvm_dst h fun h' => hr (dstNames_sub h')

theorem lsemStepMC_lvm {i : LinstrR} {s t : LstateN}
    (h : JasminLsemMulCarry.lsemStepMC i s = some t) {r : String}
    (hr : r ∉ instrNames i) : t.lvm r = s.lvm r :=
  lsemStepMC_lvm_dst h fun h' => hr (dstNames_sub h')

theorem lsemStepCast_lvm {i : LinstrR} {cd : Option Nat} {s t : LstateN}
    (h : JasminLsemCast.lsemStepCast (i, cd) s = some t) {r : String}
    (hr : r ∉ instrNames i) : t.lvm r = s.lvm r :=
  lsemStepCast_lvm_dst h fun h' => hr (dstNames_sub h')

/-- A step of `lsemStepMem` leaves every register and every array its instruction does
    not write. -/
theorem lsemStepMem_frame_dst {i : JasminLsemMem.LinstrRM} {s t : JasminLsemMem.LstateM}
    (h : JasminLsemMem.lsemStepMem i s = some t) {r : String}
    (hr : r ∉ dstNames i.1) : t.reg.lvm r = s.reg.lvm r ∧ t.larr r = s.larr r := by
  obtain ⟨wire, tag⟩ := i
  have hcast : ∀ cd, (JasminLsemCast.lsemStepCast (wire, cd) s.reg).map
      (fun r => { s with reg := r }) = some t → t.reg.lvm r = s.reg.lvm r ∧ t.larr r = s.larr r := by
    intro cd h
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨lsemStepCast_lvm_dst hq hr, rfl⟩
  unfold JasminLsemMem.lsemStepMem at h
  cases tag with
  | reg cd => exact hcast cd h
  | load w n =>
      simp only at h
      split at h
      · rename_i dst base idx heq
        have hd := loadStruct?_dst heq
        repeat' split at h
        all_goals first
          | (cases h; exact ⟨setReg_nextPc_lvm _ fun he => hr (he ▸ hd), rfl⟩)
          | cases h
      · exact hcast none h
  | store w n =>
      simp only at h
      split at h
      · rename_i dst base idx val heq
        have hd := storeStruct?_dst heq
        repeat' split at h
        all_goals first
          | (cases h
             have hne : r ≠ dst := fun he => hr (he ▸ hd)
             exact ⟨rfl, by simp [JasminLsemMem.LstateM.nextPc, JasminLsemMem.LstateM.setArr,
               hne]⟩)
          | cases h
      · exact hcast none h
  | loadC =>
      simp only at h
      split at h
      · rename_i dst base off heq
        have hd := loadCStruct?_dst heq
        cases h
        exact ⟨setReg_nextPc_lvm _ fun he => hr (he ▸ hd), rfl⟩
      · cases h
  | storeC =>
      simp only at h
      repeat' split at h
      all_goals first | (cases h; exact ⟨rfl, rfl⟩) | cases h
  | zero w n =>
      simp only at h
      split at h
      · rename_i dst heq
        have hd := zeroStruct?_dst heq
        cases h
        have hne : r ≠ dst := fun he => hr (he ▸ hd)
        exact ⟨rfl, by simp [JasminLsemMem.LstateM.nextPc, JasminLsemMem.LstateM.setArr, hne]⟩
      · cases h

/-- A step of `lsemStepMem` leaves every register and every array its instruction does
    not name. -/
theorem lsemStepMem_frame {i : JasminLsemMem.LinstrRM} {s t : JasminLsemMem.LstateM}
    (h : JasminLsemMem.lsemStepMem i s = some t) {r : String}
    (hr : r ∉ instrNames i.1) : t.reg.lvm r = s.reg.lvm r ∧ t.larr r = s.larr r :=
  lsemStepMem_frame_dst h fun h' => hr (dstNames_sub h')

theorem wideArgs?_names_mulx {i : LinstrRM} {lo hi : String} {b : LOperand}
    (h : wideArgs? i = some (.mulx lo hi b)) : lo ∈ instrNames i.1 ∧ hi ∈ instrNames i.1 := by
  obtain ⟨wire, tag⟩ := i
  unfold wideArgs? at h
  dsimp only at h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h; simp [instrNames, opNames]
    · cases h
  · cases h

theorem wideArgs?_dst_mulx {i : LinstrRM} {lo hi : String} {b : LOperand}
    (h : wideArgs? i = some (.mulx lo hi b)) : lo ∈ dstNames i.1 ∧ hi ∈ dstNames i.1 := by
  obtain ⟨wire, tag⟩ := i
  unfold wideArgs? at h
  dsimp only at h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h; simp [dstNames, opNames]
    · cases h
  · cases h

theorem wideArgs?_dst_mov {i : LinstrRM} {d : String} {b : LOperand}
    (h : wideArgs? i = some (.mov d b)) : d ∈ dstNames i.1 := by
  obtain ⟨wire, tag⟩ := i
  unfold wideArgs? at h
  dsimp only at h
  split at h
  · split_ifs at h
    cases h; simp [dstNames, opNames]
  · split_ifs at h
    cases h
  · cases h

theorem carryArgs?_dst {i : LinstrRM} {p : JasminLsemMemFlagGuard.CarryOp × String × LOperand × LOperand}
    (h : JasminLsemMemFlagGuard.carryArgs? i = some p) : p.2.1 ∈ dstNames i.1 := by
  obtain ⟨wire, tag⟩ := i
  unfold JasminLsemMemFlagGuard.carryArgs? at h
  dsimp only at h
  split at h
  · split_ifs at h <;> cases h <;> simp [dstNames, opNames]
  · simp at h

theorem movRegArgs?_dst {i : LinstrRM} {p : String × String}
    (h : JasminLsemMemFlagGuard.movRegArgs? i = some p) : p.1 ∈ dstNames i.1 := by
  obtain ⟨wire, tag⟩ := i
  unfold JasminLsemMemFlagGuard.movRegArgs? at h
  dsimp only at h
  split at h
  · split_ifs at h <;> cases h <;> simp [dstNames, opNames]
  · simp at h

theorem setReg_nextPcM_lvm {s : LstateM} {d r : String} {w : Nat} (v : BitVec w)
    (h : r ≠ d) : ((s.setReg d v).nextPc).reg.lvm r = s.reg.lvm r := by
  simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, h]

/-- A step of `stepMemF` leaves every register and every array its instruction does not
    write. -/
theorem stepMemF_frame_dst {i : LinstrRM} {s t : LstateM} (h : stepMemF i s = some t)
    {r : String} (hr : r ∉ dstNames i.1) : t.reg.lvm r = s.reg.lvm r ∧ t.larr r = s.larr r := by
  unfold stepMemF at h
  cases hm : JasminLsemMem.lsemStepMem i s with
  | some b =>
      rw [hm] at h
      cases h
      rw [withALUFlags_reg, withALUFlags_larr]
      exact lsemStepMem_frame_dst hm hr
  | none =>
  rw [hm] at h
  simp only at h
  cases hc : JasminLsemMemFlagGuard.carryArgs? i with
  | some p =>
      obtain ⟨op, d, a, b⟩ := p
      rw [hc] at h
      have hne : r ≠ d := fun he => hr (he ▸ carryArgs?_dst hc)
      simp only [carryStep] at h
      cases ha : evalOperandN s.reg 64 a <;> cases hb : evalOperandN s.reg 64 b <;>
        simp only [ha, hb] at h <;> try cases h
      all_goals cases op <;> simp only [Option.some.injEq] at h <;> subst h <;>
        exact ⟨setReg_nextPcM_lvm _ hne, rfl⟩
  | none =>
  rw [hc] at h
  simp only at h
  cases hw : wideArgs? i with
  | none => rw [hw] at h; cases h
  | some wo =>
      rw [hw] at h
      simp only at h
      cases wo with
      | mov d b =>
          have hne : r ≠ d := fun he => hr (he ▸ wideArgs?_dst_mov hw)
          simp only [wideStep] at h
          cases hv : evalOperandN s.reg 64 b <;> simp only [hv] at h <;> try cases h
          exact ⟨setReg_nextPcM_lvm _ hne, rfl⟩
      | mulx lo hi b =>
          have hn := wideArgs?_dst_mulx hw
          have hlo : r ≠ lo := fun he => hr (he ▸ hn.1)
          have hhi : r ≠ hi := fun he => hr (he ▸ hn.2)
          simp only [wideStep] at h
          cases hx : evalOperandN s.reg 64 (.reg JasminLsemMemFlagGuard.mulxSrc) <;>
            cases hy : evalOperandN s.reg 64 b <;> simp only [hx, hy] at h <;> try cases h
          refine ⟨?_, rfl⟩
          simp [LstateM.setReg, LstateM.nextPc, LstateN.setReg, LstateN.nextPc, hlo, hhi]

/-- A step of `stepMemF` leaves every register and every array its instruction does not
    name. -/
theorem stepMemF_frame {i : LinstrRM} {s t : LstateM} (h : stepMemF i s = some t) {r : String}
    (hr : r ∉ instrNames i.1) : t.reg.lvm r = s.reg.lvm r ∧ t.larr r = s.larr r :=
  stepMemF_frame_dst h fun h' => hr (dstNames_sub h')

/-- **A flag-machine step leaves every register and every array its instruction does not
    write.** -/
theorem fstepF_frame_dst {i : LinstrRM} {s t : LstateM} {zf z : Bool}
    (h : fstepF i s zf = some (t, z)) {r : String} (hr : r ∉ dstNames i.1) :
    t.reg.lvm r = s.reg.lvm r ∧ t.larr r = s.larr r := by
  unfold fstepF at h
  cases hc : JasminLsemMemFlagGuard.cmpArgs? i with
  | some p =>
      obtain ⟨a, b⟩ := p
      rw [hc] at h
      simp only at h
      cases ha : evalOperandN s.reg 64 a <;> cases hb : evalOperandN s.reg 64 b <;>
        simp only [ha, hb] at h <;> try cases h
      all_goals exact ⟨rfl, rfl⟩
  | none =>
  rw [hc] at h
  simp only at h
  cases hm : JasminLsemMemFlagGuard.movRegArgs? i with
  | some p =>
      obtain ⟨dst, src⟩ := p
      rw [hm] at h
      simp only at h
      have hne : r ≠ dst := fun he => hr (he ▸ movRegArgs?_dst hm)
      cases hv : readReg s.reg (.reg src) with
      | none => simp only [hv] at h; cases h
      | some v =>
          obtain ⟨w, v⟩ := v
          simp only [hv, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact ⟨setReg_nextPcM_lvm _ hne, rfl⟩
  | none =>
      rw [hm] at h
      simp only at h
      obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact stepMemF_frame_dst hb hr

/-- **A flag-machine step leaves every register and every array its instruction does not
    name.** -/
theorem fstepF_frame {i : LinstrRM} {s t : LstateM} {zf z : Bool}
    (h : fstepF i s zf = some (t, z)) {r : String} (hr : r ∉ instrNames i.1) :
    t.reg.lvm r = s.reg.lvm r ∧ t.larr r = s.larr r :=
  fstepF_frame_dst h fun h' => hr (dstNames_sub h')

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame
