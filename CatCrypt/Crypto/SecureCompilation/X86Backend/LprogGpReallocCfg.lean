/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
public import CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
import all Init.Data.String.TakeDrop

/-!
# The register re-allocation on the flag machine

`LprogGpRealloc.reallocLprog` re-allocates every maximal run of fragment instructions of a
function body (`LprogGpRealloc.reallocRun`) and keeps every other instruction.
`LprogGpRealloc.reallocRun_lsemStraight` states its soundness for one run under the
uniform-width straight-line semantics, which has no flags and no control flow. This module
proves the pass on whole bodies of the flag machine `lsemFuelMemF`, so that the owned
pipeline needs no per-body validator call for it.

## Design

* **One step.** `fstepF_val` relates one flag-machine step of a single-destination fragment
  instruction to the step of the instruction with another destination and renamed sources,
  for a renaming that need not be injective (the check coalesces copies, so two source names
  may share one location). `JasminLsemExportRewrites.evalInstrPMemF_ren` requires an
  injective renaming and does not apply.
* **One run.** `goAccF_sound` is `LprogGpRealloc.goAcc_sound` on the flag machine
  `runStraightF`, with the carry, overflow and zero flags; `reallocRunF` is the pass on one
  run from two states that agree off a set of locations the run does not use.
* **Bodies.** The re-allocated body agrees with the source only on the names live at each
  boundary, so the lift `CfgLift.lsemFuelMemFk_blockRel`, which relates the two bodies by
  equality up to the program counter, does not apply. `lsemFuelMemF_QRel` is that lift with a
  relation `Q X` indexed by the source suffix `X` at the program counter. The relation of the
  pass is `QR`: the states agree off `DX X`, the frame cells that are neither named in `X` nor
  live at every label (`LprogGpRealloc.labelLiveFrames`); before a return, off every location;
  at the end of the body, off every location that is no register of `regsOf` and no frame
  cell live at the labels.
* **Kept instructions.** An instruction outside the fragment runs on both sides from states
  that agree off names it does not mention (`fstepF_bar`, through `evalInstrPMemF_ren` at the
  identity renaming, and directly for `MULX`, which reads `RDX`).

## Hypotheses

`reallocBody_lsemFuelMemF` and `reallocLprog_lsemFuelMemF` assume:

* `AbiOK res abi`: no general-purpose register and no register live at a return
  (`retLive res abi`) is a frame cell `k.N`, and the empty name is no location.
  `abiOK_x86` proves it for `x86Abi` when no result register is a frame cell.
* the memory tag `tag` gives the register tag `.reg none` to every fragment mnemonic
  (every recognised mnemonic other than `LOADIDX`, `STOREIDX`);
* the body has a return at most as its last instruction, every instruction is kept by the
  block lift (`CfgLift.keepOKB`), and every flag compare `CMP:64` of the fragment reads its
  destination (`CmpReadsDst`). `reallocCfgOKB` decides the three, `reallocCfgOKB_sound`.

The check `goAcc` reads a fragment instruction as a write of its destination. The flag
compare writes only the zero flag, so a compare `CMP:64 d, a, b` that does not read `d` makes
the earlier value of `d` dead in the check's liveness while the machine keeps it: in
`MOV:64 RAX, 1; CMP:64 RAX, RBX, 0; ADD:64 RCX, RCX, RAX` the move is dropped as dead and
the addition reads the entry value of `RAX`. The pass is wrong on that shape, which the
export does not produce (its compares are `CMP:64 r, r, n`). A result register that is a
frame cell is outside `AbiOK`: such a cell is not live after a run that precedes its last
naming instruction, so a move to it can be dropped.

## Main results

* `fstepF_val`, `goAccF_sound`, `reallocRunF`: one step, the check and one run.
* `lsemFuelMemF_QRel`: the lift of block-local rewrites with a suffix-indexed relation.
* `fstepF_bar`: a kept instruction from states that agree off names it does not mention.
* `core`, `body_sim`: the pass on the pieces of a body followed by a tail.
* `reallocBody_lsemFuelMemF`, `reallocLprog_lsemFuelMemF`: the pass on a function body and
  on every function of a program.
* `abiOK_x86`, `reallocCfgOKB_sound`: the hypotheses at the x86 register file, and their
  decision on a body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renOperand renLinstrR renRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)
open CatCrypt.Crypto.SecureCompilation.VIR.LsemBridgePass.CfgLift
  (CtlKeep keepOKB drop_succ_of_cons drop_add_of_append getElem?_of_drop_append findLabelMem_cons
   evalInstrPMemF_ret_none ctlKeep_of_keepOKB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fstepF_copy renOperand_id renRM_id emptyP)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (lsemFuelMemF_seg_fuel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix (findLabelMem_prefix)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
  (instrNames RenOn RenProg RelF CondOK mulxFree evalInstrPMemF_ren storeStruct?_names
   zeroStruct?_names storeImmStruct?_names)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
  (NoArrWriteAt evalInstrPMemF_larr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower (fstepF_setLpc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (typeBody dropRet)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi stripAbiTag)

/-! ## 1. One step of a renamed fragment instruction -/

theorem lstateM_ext {s t : LstateM} (h1 : s.reg = t.reg) (h2 : s.larr = t.larr)
    (h3 : s.lmem = t.lmem) (h4 : s.cf = t.cf) (h5 : s.of = t.of) : s = t := by
  cases s; cases t; simp_all

/-- The sources of an instruction read the same values after a renaming `σ` of their
    register names: every register source `x` holds in `s'` at `σ x` the cell it holds
    in `s`, and the empty name (the name a non-register condition operand of `CMOV` is read
    at) holds the same cell. The renaming need not be injective. -/
def SrcAgree (σ : String → String) (srcs : List LOperand) (s s' : LstateN) : Prop :=
  (∀ x, LOperand.reg x ∈ srcs → s'.lvm (σ x) = s.lvm x) ∧ s'.lvm "" = s.lvm ""

section Val

variable {σ : String → String} {srcs : List LOperand} {s s' : LstateN}

theorem SrcAgree.readReg (h : SrcAgree σ srcs s s') {o : LOperand} (ho : o ∈ srcs) :
    JasminLsemWidthN.readReg s' (renOperand σ o) = JasminLsemWidthN.readReg s o := by
  cases o <;> simp only [JasminLsemWidthN.readReg, renOperand]
  rw [h.1 _ ho]

theorem SrcAgree.readReg_reg (h : SrcAgree σ srcs s s') {x : String}
    (ho : LOperand.reg x ∈ srcs) :
    JasminLsemWidthN.readReg s' (.reg (σ x)) = JasminLsemWidthN.readReg s (.reg x) := by
  simp only [JasminLsemWidthN.readReg]
  rw [h.1 _ ho]

theorem SrcAgree.evalOperandN (h : SrcAgree σ srcs s s') (w : Nat) {o : LOperand}
    (ho : o ∈ srcs) :
    evalOperandN s' w (renOperand σ o) = evalOperandN s w o := by
  cases o <;> simp only [JasminLsemWidthN.evalOperandN, renOperand, LstateN.getW]
  rw [h.1 _ ho]

theorem SrcAgree.getW (h : SrcAgree σ srcs s s') (w : Nat) {x : String}
    (ho : LOperand.reg x ∈ srcs) : s'.getW (σ x) w = s.getW x w := by
  unfold LstateN.getW
  rw [h.1 _ ho]

theorem SrcAgree.getW_emp (h : SrcAgree σ srcs s s') (w : Nat) :
    s'.getW "" w = s.getW "" w := by
  unfold LstateN.getW
  rw [h.2]

theorem SrcAgree.operandName (h : SrcAgree σ srcs s s') (w : Nat) {o : LOperand}
    (ho : o ∈ srcs) :
    s'.getW (JasminLsemWidthN.operandName (renOperand σ o)) w
      = s.getW (JasminLsemWidthN.operandName o) w := by
  cases o with
  | reg x => exact h.getW w ho
  | _ => exact h.getW_emp w

/-- A register or immediate source of an instruction of the fragment is no element. -/
theorem mem_srcs_cases {srcs : List LOperand} (hwf : ∀ o ∈ srcs, regOrImm o = true)
    {o : LOperand} (ho : o ∈ srcs) : (∃ x, o = .reg x) ∨ ∃ n, o = .imm n := by
  have := hwf o ho
  cases o <;> simp_all [regOrImm]

set_option hygiene false in
/-- Close a value goal: split the hypothesis `h`, discard the failing arms, and close the
    successful arm with the written value. -/
local macro "val_close" : tactic =>
  `(tactic| ((repeat' split at h) <;>
      first
        | (simp at h; done)
        | (cases h; exact ⟨_, _, rfl, by simp [*]⟩)))

/-- **`lsemStepN` on a renamed instruction.** A successful step of a single-destination
    instruction with register and immediate sources writes one value `v` at its
    destination; the instruction with any destination `c` and the sources renamed by `σ`
    writes the same value at `c`, from a state whose renamed sources hold the original
    values. -/
theorem lsemStepN_val (i : LinstrR) {d opn : String} {srcs : List LOperand}
    (hi : i = .Lopn [.reg d] opn srcs) (c : String)
    (hwf : ∀ o ∈ srcs, regOrImm o = true) (hA : SrcAgree σ srcs s s') {t : LstateN}
    (h : lsemStepN i s = some t) :
    ∃ (w : Nat) (v : BitVec w), t = (s.setReg d v).nextPc
      ∧ lsemStepN (.Lopn [.reg c] opn (srcs.map (renOperand σ))) s' = some ((s'.setReg c v).nextPc) := by
  subst hi
  unfold lsemStepN at h
  split at h
  · rename_i dst opn' c0 a b heq
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp only [List.map_cons, List.map_nil, lsemStepN,
      hA.operandName 1 (o := c0) (by simp), hA.readReg (o := a) (by simp),
      fun w => hA.evalOperandN w (o := b) (by simp)]
    val_close
  · rename_i dst opn' a b heq
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp only [List.map_cons, List.map_nil, lsemStepN, hA.readReg (o := a) (by simp),
      fun w => hA.evalOperandN w (o := b) (by simp)]
    cases hra : JasminLsemWidthN.readReg s a with
    | some wv =>
      obtain ⟨w, va⟩ := wv
      simp only [hra] at h ⊢
      val_close
    | none =>
      simp only [hra] at h ⊢
      cases a with
      | imm n =>
        simp only [JasminLsemExportRewrites.renOperand_imm, immFirstN,
          fun w => hA.evalOperandN w (o := b) (by simp)] at h ⊢
        cases hb : evalOperandN s (widthFromTag opn) b with
        | none => simp [hb] at h
        | some vb =>
          simp only [hb] at h ⊢
          obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
          exact ⟨_, _, rfl, by rw [hv]; rfl⟩
      | _ => simp at h
  · rename_i dst opn' n heq
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp only [List.map_cons, List.map_nil, renOperand, lsemStepN]
    val_close
  · rename_i dst opn' a heq
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    have hra : JasminLsemWidthN.readReg s' (.reg (σ a)) = JasminLsemWidthN.readReg s (.reg a) :=
      hA.readReg (o := .reg a) (by simp)
    simp only [List.map_cons, List.map_nil, renOperand, lsemStepN, hra]
    val_close
  · rename_i dst opn' b x sc heq
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp [regOrImm] at hwf
  all_goals first | (rename_i heq; cases heq; done) | exact absurd h (by simp)

/-- The renamed instruction is an `Lopn` with the renamed sources. -/
theorem lopn_ren_eq {c opn : String} {srcs : List LOperand} {ds : List LOperand}
    {o : String} {ss : List LOperand} :
    LinstrR.Lopn [.reg c] opn (srcs.map (renOperand σ)) = .Lopn ds o ss ↔
      ds = [.reg c] ∧ o = opn ∧ ss = srcs.map (renOperand σ) := by
  simp only [LinstrR.Lopn.injEq]
  tauto

set_option hygiene false in
/-- Prove that a structured recogniser of a single-destination instruction commutes with a
    change of destination and a renaming of the sources. -/
local macro "val_recog" : tactic =>
  `(tactic| (
      split
      · next heq =>
          obtain ⟨hd, rfl, hs⟩ := lopn_ren_eq.mp heq
          cases hd
          have hs := hs.symm
          simp only [List.map_eq_cons_iff, List.map_eq_nil_iff,
            JasminLsemExportRewrites.renOperand_eq_reg,
            JasminLsemExportRewrites.renOperand_eq_imm] at hs
          casesm* (∃ _, _), (_ ∧ _)
          subst_vars
          first | (simp; done) | (split_ifs <;> simp_all [wideRen])
      · next hne =>
          split
          · next heq =>
              exfalso
              simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at heq
              obtain ⟨⟨rfl, -⟩, rfl, rfl⟩ := heq
              apply hne <;> rfl
          · rfl))

variable (d c opn : String) (srcs : List LOperand) (σ : String → String)

theorem sarStruct?_val :
    sarStruct? (.Lopn [.reg c] opn (srcs.map (renOperand σ)))
      = (sarStruct? (.Lopn [.reg d] opn srcs)).map (fun p => (c, σ p.2.1, p.2.2)) := by
  unfold sarStruct?; val_recog

theorem mulhiStruct?_val :
    mulhiStruct? (.Lopn [.reg c] opn (srcs.map (renOperand σ)))
      = (mulhiStruct? (.Lopn [.reg d] opn srcs)).map (fun p => (c, σ p.2.1, σ p.2.2)) := by
  unfold mulhiStruct?; val_recog

theorem adcxStruct?_val :
    adcxStruct? (.Lopn [.reg c] opn (srcs.map (renOperand σ)))
      = (adcxStruct? (.Lopn [.reg d] opn srcs)).map
          (fun p => (c, σ p.2.1, σ p.2.2.1, σ p.2.2.2)) := by
  unfold adcxStruct?; val_recog

theorem adcxhiStruct?_val :
    adcxhiStruct? (.Lopn [.reg c] opn (srcs.map (renOperand σ)))
      = (adcxhiStruct? (.Lopn [.reg d] opn srcs)).map
          (fun p => (c, σ p.2.1, σ p.2.2.1, σ p.2.2.2)) := by
  unfold adcxhiStruct?; val_recog

theorem sbbStruct?_val :
    sbbStruct? (.Lopn [.reg c] opn (srcs.map (renOperand σ)))
      = (sbbStruct? (.Lopn [.reg d] opn srcs)).map
          (fun p => (c, σ p.2.1, σ p.2.2.1, σ p.2.2.2)) := by
  unfold sbbStruct?; val_recog

theorem sbbhiStruct?_val :
    sbbhiStruct? (.Lopn [.reg c] opn (srcs.map (renOperand σ)))
      = (sbbhiStruct? (.Lopn [.reg d] opn srcs)).map
          (fun p => (c, σ p.2.1, σ p.2.2.1, σ p.2.2.2)) := by
  unfold sbbhiStruct?; val_recog

theorem castStruct?_val :
    castStruct? (.Lopn [.reg c] opn (srcs.map (renOperand σ)))
      = (castStruct? (.Lopn [.reg d] opn srcs)).map (fun p => (c, σ p.2)) := by
  unfold castStruct?; val_recog

theorem movImmStruct?_val :
    movImmStruct? (.Lopn [.reg c] opn (srcs.map (renOperand σ)))
      = (movImmStruct? (.Lopn [.reg d] opn srcs)).map (fun p => (c, p.2)) := by
  unfold movImmStruct?; val_recog

set_option hygiene false in
/-- Invert a structured recogniser that fires on a single-destination instruction. -/
local macro "val_shape" : tactic =>
  `(tactic| (
      split at h
      · next heq =>
          simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at heq
          obtain ⟨⟨rfl, -⟩, rfl, rfl⟩ := heq
          split_ifs at h
          cases h
          simp
      · cases h))

variable {d c opn srcs σ}

theorem sarStruct?_shape {p : String × String × Nat}
    (h : sarStruct? (.Lopn [.reg d] opn srcs) = some p) :
    p.1 = d ∧ srcs = [.reg p.2.1, .imm p.2.2] := by
  unfold sarStruct? at h; val_shape

theorem mulhiStruct?_shape {p : String × String × String}
    (h : mulhiStruct? (.Lopn [.reg d] opn srcs) = some p) :
    p.1 = d ∧ srcs = [.reg p.2.1, .reg p.2.2] := by
  unfold mulhiStruct? at h; val_shape

theorem adcxStruct?_shape {p : String × String × String × String}
    (h : adcxStruct? (.Lopn [.reg d] opn srcs) = some p) :
    p.1 = d ∧ srcs = [.reg p.2.1, .reg p.2.2.1, .reg p.2.2.2] := by
  unfold adcxStruct? at h; val_shape

theorem adcxhiStruct?_shape {p : String × String × String × String}
    (h : adcxhiStruct? (.Lopn [.reg d] opn srcs) = some p) :
    p.1 = d ∧ srcs = [.reg p.2.1, .reg p.2.2.1, .reg p.2.2.2] := by
  unfold adcxhiStruct? at h; val_shape

theorem sbbStruct?_shape {p : String × String × String × String}
    (h : sbbStruct? (.Lopn [.reg d] opn srcs) = some p) :
    p.1 = d ∧ srcs = [.reg p.2.1, .reg p.2.2.1, .reg p.2.2.2] := by
  unfold sbbStruct? at h; val_shape

theorem sbbhiStruct?_shape {p : String × String × String × String}
    (h : sbbhiStruct? (.Lopn [.reg d] opn srcs) = some p) :
    p.1 = d ∧ srcs = [.reg p.2.1, .reg p.2.2.1, .reg p.2.2.2] := by
  unfold sbbhiStruct? at h; val_shape

theorem castStruct?_shape {p : String × String}
    (h : castStruct? (.Lopn [.reg d] opn srcs) = some p) :
    p.1 = d ∧ srcs = [.reg p.2] := by
  unfold castStruct? at h; val_shape

theorem movImmStruct?_shape {p : String × Nat}
    (h : movImmStruct? (.Lopn [.reg d] opn srcs) = some p) :
    p.1 = d ∧ srcs = [.imm p.2] := by
  unfold movImmStruct? at h
  split at h
  · next heq =>
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at heq
      obtain ⟨⟨rfl, -⟩, rfl, rfl⟩ := heq
      cases h
      simp
  · cases h

/-- **`lsemStepSh` on a renamed instruction.** -/
theorem lsemStepSh_val (hwf : ∀ o ∈ srcs, regOrImm o = true) (hA : SrcAgree σ srcs s s')
    {t : LstateN} (h : lsemStepSh (.Lopn [.reg d] opn srcs) s = some t) :
    ∃ (w : Nat) (v : BitVec w), t = (s.setReg d v).nextPc
      ∧ lsemStepSh (.Lopn [.reg c] opn (srcs.map (renOperand σ))) s'
          = some ((s'.setReg c v).nextPc) := by
  unfold lsemStepSh at h ⊢
  rw [sarStruct?_val d c opn srcs σ]
  cases hs : sarStruct? (.Lopn [.reg d] opn srcs) with
  | none =>
      simp only [hs, Option.map_none] at h ⊢
      exact lsemStepN_val _ rfl c hwf hA h
  | some p =>
      obtain ⟨d', a, n⟩ := p
      obtain ⟨rfl, rfl⟩ := sarStruct?_shape hs
      simp only [hs, Option.map_some] at h ⊢
      rw [hA.readReg_reg (x := a) (by simp)]
      val_close

/-- **`lsemStepMC` on a renamed instruction.** -/
theorem lsemStepMC_val (hwf : ∀ o ∈ srcs, regOrImm o = true) (hA : SrcAgree σ srcs s s')
    {t : LstateN} (h : lsemStepMC (.Lopn [.reg d] opn srcs) s = some t) :
    ∃ (w : Nat) (v : BitVec w), t = (s.setReg d v).nextPc
      ∧ lsemStepMC (.Lopn [.reg c] opn (srcs.map (renOperand σ))) s'
          = some ((s'.setReg c v).nextPc) := by
  unfold lsemStepMC at h ⊢
  rw [mulhiStruct?_val d c opn srcs σ, adcxStruct?_val d c opn srcs σ,
    adcxhiStruct?_val d c opn srcs σ, sbbStruct?_val d c opn srcs σ,
    sbbhiStruct?_val d c opn srcs σ]
  cases h1 : mulhiStruct? (.Lopn [.reg d] opn srcs) with
  | some p =>
      obtain ⟨d', a, b⟩ := p
      obtain ⟨rfl, rfl⟩ := mulhiStruct?_shape h1
      simp only [h1, Option.map_some] at h ⊢
      rw [hA.readReg_reg (x := a) (by simp)]
      simp only [fun w => hA.getW w (x := b) (by simp)]
      val_close
  | none =>
  simp only [h1, Option.map_none] at h ⊢
  cases h2 : adcxStruct? (.Lopn [.reg d] opn srcs) with
  | some p =>
      obtain ⟨d', a, b, e⟩ := p
      obtain ⟨rfl, rfl⟩ := adcxStruct?_shape h2
      simp only [h2, Option.map_some] at h ⊢
      rw [hA.readReg_reg (x := a) (by simp)]
      simp only [fun w => hA.getW w (x := b) (by simp), hA.getW 1 (x := e) (by simp)]
      val_close
  | none =>
  simp only [h2, Option.map_none] at h ⊢
  cases h3 : adcxhiStruct? (.Lopn [.reg d] opn srcs) with
  | some p =>
      obtain ⟨d', a, b, e⟩ := p
      obtain ⟨rfl, rfl⟩ := adcxhiStruct?_shape h3
      simp only [h3, Option.map_some] at h ⊢
      rw [hA.readReg_reg (x := a) (by simp)]
      simp only [fun w => hA.getW w (x := b) (by simp), hA.getW 1 (x := e) (by simp)]
      val_close
  | none =>
  simp only [h3, Option.map_none] at h ⊢
  cases h4 : sbbStruct? (.Lopn [.reg d] opn srcs) with
  | some p =>
      obtain ⟨d', a, b, e⟩ := p
      obtain ⟨rfl, rfl⟩ := sbbStruct?_shape h4
      simp only [h4, Option.map_some] at h ⊢
      rw [hA.readReg_reg (x := a) (by simp)]
      simp only [fun w => hA.getW w (x := b) (by simp), hA.getW 1 (x := e) (by simp)]
      val_close
  | none =>
  simp only [h4, Option.map_none] at h ⊢
  cases h5 : sbbhiStruct? (.Lopn [.reg d] opn srcs) with
  | some p =>
      obtain ⟨d', a, b, e⟩ := p
      obtain ⟨rfl, rfl⟩ := sbbhiStruct?_shape h5
      simp only [h5, Option.map_some] at h ⊢
      rw [hA.readReg_reg (x := a) (by simp)]
      simp only [fun w => hA.getW w (x := b) (by simp), hA.getW 1 (x := e) (by simp)]
      val_close
  | none =>
  simp only [h5, Option.map_none] at h ⊢
  exact lsemStepSh_val hwf hA h

/-- **`lsemStepCast` on a renamed instruction**, at every cast descriptor. -/
theorem lsemStepCast_val (cd : Option Nat) (hwf : ∀ o ∈ srcs, regOrImm o = true)
    (hA : SrcAgree σ srcs s s') {t : LstateN}
    (h : lsemStepCast (.Lopn [.reg d] opn srcs, cd) s = some t) :
    ∃ (w : Nat) (v : BitVec w), t = (s.setReg d v).nextPc
      ∧ lsemStepCast (.Lopn [.reg c] opn (srcs.map (renOperand σ)), cd) s'
          = some ((s'.setReg c v).nextPc) := by
  cases cd with
  | none =>
      rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)] at h
      rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
      exact lsemStepMC_val hwf hA h
  | some w' =>
      unfold lsemStepCast at h ⊢
      dsimp only at h ⊢
      rw [castStruct?_val d c opn srcs σ, movImmStruct?_val d c opn srcs σ]
      cases h1 : castStruct? (.Lopn [.reg d] opn srcs) with
      | none =>
          cases h2 : movImmStruct? (.Lopn [.reg d] opn srcs) with
          | none =>
              simp only [h1, h2, Option.map_none] at h ⊢
              exact lsemStepMC_val hwf hA h
          | some p =>
              obtain ⟨d', n⟩ := p
              obtain ⟨rfl, rfl⟩ := movImmStruct?_shape h2
              simp only [h1, h2, Option.map_none, Option.map_some] at h ⊢
              cases h
              exact ⟨_, _, rfl, rfl⟩
      | some p =>
          obtain ⟨d', a⟩ := p
          obtain ⟨rfl, rfl⟩ := castStruct?_shape h1
          simp only [h1, Option.map_some] at h ⊢
          rw [hA.readReg_reg (x := a) (by simp)]
          val_close

/-- The renamed wide-instruction description: a two-source copy writes the new destination
    from the renamed source. -/
def wideRen (c : String) (σ : String → String) : WideOp → WideOp
  | .mov _ b => .mov c (renOperand σ b)
  | .mulx lo hi b => .mulx lo hi b

variable (d c opn srcs σ)
variable (tg : MemTag)

theorem cmpArgs?_val :
    cmpArgs? (.Lopn [.reg c] opn (srcs.map (renOperand σ)), tg)
      = (cmpArgs? (.Lopn [.reg d] opn srcs, tg)).map
          (fun p => (renOperand σ p.1, renOperand σ p.2)) := by
  unfold cmpArgs?; dsimp only; val_recog

theorem movRegArgs?_val :
    movRegArgs? (.Lopn [.reg c] opn (srcs.map (renOperand σ)), tg)
      = (movRegArgs? (.Lopn [.reg d] opn srcs, tg)).map (fun p => (c, σ p.2)) := by
  unfold movRegArgs?; dsimp only; val_recog

theorem aluFlagOp?_val :
    aluFlagOp? (.Lopn [.reg c] opn (srcs.map (renOperand σ)), tg)
      = (aluFlagOp? (.Lopn [.reg d] opn srcs, tg)).map
          (fun p => (p.1, renOperand σ p.2.1, renOperand σ p.2.2)) := by
  unfold aluFlagOp?; dsimp only; val_recog

theorem carryArgs?_val :
    carryArgs? (.Lopn [.reg c] opn (srcs.map (renOperand σ)), tg)
      = (carryArgs? (.Lopn [.reg d] opn srcs, tg)).map
          (fun p => (p.1, c, renOperand σ p.2.2.1, renOperand σ p.2.2.2)) := by
  unfold carryArgs?; dsimp only; val_recog

theorem wideArgs?_val :
    wideArgs? (.Lopn [.reg c] opn (srcs.map (renOperand σ)), tg)
      = (wideArgs? (.Lopn [.reg d] opn srcs, tg)).map (wideRen c σ) := by
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨e, rest⟩⟩⟩ <;>
    simp only [wideArgs?, List.map_cons, List.map_nil, Option.map_none]
  all_goals split_ifs <;> simp [wideRen]

variable {d c opn srcs σ tg}

theorem cmpArgs?_shape {p : LOperand × LOperand}
    (h : cmpArgs? (.Lopn [.reg d] opn srcs, tg) = some p) :
    opn = withWidthTag 64 "CMP" ∧ srcs = [p.1, p.2] := by
  unfold cmpArgs? at h
  dsimp only at h
  split at h
  · next heq =>
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, rfl⟩ := heq
      split_ifs at h with h1
      cases h
      exact ⟨h1, rfl⟩
  · cases h

theorem movRegArgs?_shape {p : String × String}
    (h : movRegArgs? (.Lopn [.reg d] opn srcs, tg) = some p) :
    p.1 = d ∧ srcs = [.reg p.2] := by
  unfold movRegArgs? at h
  dsimp only at h
  split at h
  · next heq =>
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at heq
      obtain ⟨⟨rfl, -⟩, rfl, rfl⟩ := heq
      split_ifs at h <;> cases h <;> simp
  · cases h

theorem carryArgs?_shape {p : CarryOp × String × LOperand × LOperand}
    (h : carryArgs? (.Lopn [.reg d] opn srcs, tg) = some p) :
    p.2.1 = d ∧ srcs = [p.2.2.1, p.2.2.2] := by
  unfold carryArgs? at h
  dsimp only at h
  split at h
  · next heq =>
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at heq
      obtain ⟨⟨rfl, -⟩, rfl, rfl⟩ := heq
      split_ifs at h <;> cases h <;> simp
  · cases h

theorem wideArgs?_shape {w : WideOp}
    (h : wideArgs? (.Lopn [.reg d] opn srcs, tg) = some w) :
    ∃ a b, w = .mov d b ∧ srcs = [a, b] := by
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨e, rest⟩⟩⟩ <;> simp [wideArgs?] at h
  exact ⟨a, b, h.2.symm, rfl⟩

/-- The state after a step that writes the cell `wr` (when present) at `d`, advances the
    program counter and sets the carry and overflow flags to `cf` and `of`. -/
def writeDstF (s : LstateM) (d : String) (wr : Option (Σ w, BitVec w)) (cf of : Bool) : LstateM :=
  { (match wr with
      | some v => s.setReg d v.2
      | none => s).nextPc with cf := cf, of := of }

theorem aluFlagOp?_shape {p : AluOp × LOperand × LOperand}
    (h : aluFlagOp? (.Lopn [.reg d] opn srcs, tg) = some p) : srcs = [p.2.1, p.2.2] := by
  unfold aluFlagOp? at h
  dsimp only at h
  split at h
  · next heq =>
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, rfl⟩ := heq
      split_ifs at h <;> cases h <;> rfl
  · cases h

/-- The flags `withALUFlags` writes for the renamed instruction are those it writes for
    the original, from states whose renamed sources hold the original values. -/
theorem withALUFlags_val {s s' b b' : LstateM} (hA : SrcAgree σ srcs s.reg s'.reg)
    (hcf : b'.cf = b.cf) (hof : b'.of = b.of) :
    (withALUFlags (.Lopn [.reg c] opn (srcs.map (renOperand σ)), tg) s' b').cf
        = (withALUFlags (.Lopn [.reg d] opn srcs, tg) s b).cf
      ∧ (withALUFlags (.Lopn [.reg c] opn (srcs.map (renOperand σ)), tg) s' b').of
        = (withALUFlags (.Lopn [.reg d] opn srcs, tg) s b).of := by
  unfold withALUFlags
  rw [aluFlagOp?_val d c opn srcs σ tg]
  cases h1 : aluFlagOp? (.Lopn [.reg d] opn srcs, tg) with
  | none => exact ⟨hcf, hof⟩
  | some p =>
      obtain ⟨op, a, e⟩ := p
      have hs := aluFlagOp?_shape h1
      simp only [Option.map_some]
      rw [hA.evalOperandN 64 (o := a) (by simp [hs]), hA.evalOperandN 64 (o := e) (by simp [hs])]
      split <;> simp [hcf, hof]

/-- **One flag-machine step of a renamed fragment instruction.** A successful step of a
    single-destination instruction with register and immediate sources and the register
    tag writes at most one cell at its destination, advances the program counter and sets
    the carry and overflow flags; it writes no cell only when it is the flag compare. The
    instruction with destination `c` and the sources renamed by `σ`, from a state whose
    renamed sources hold the original values and whose flags are equal, writes the same
    cell at `c`, sets the same flags and the same zero flag. -/
theorem fstepF_val {s s' : LstateM} (hwf : ∀ o ∈ srcs, regOrImm o = true)
    (hA : SrcAgree σ srcs s.reg s'.reg) (hcf : s'.cf = s.cf) (hof : s'.of = s.of)
    {zf zt : Bool} {t : LstateM}
    (h : fstepF (.Lopn [.reg d] opn srcs, .reg none) s zf = some (t, zt)) :
    ∃ wr cf of, t = writeDstF s d wr cf of ∧ (wr = none → opn = withWidthTag 64 "CMP")
      ∧ fstepF (.Lopn [.reg c] opn (srcs.map (renOperand σ)), .reg none) s' zf
          = some (writeDstF s' c wr cf of, zt) := by
  unfold fstepF at h ⊢
  rw [cmpArgs?_val d c opn srcs σ, movRegArgs?_val d c opn srcs σ]
  cases h1 : cmpArgs? (LinstrR.Lopn [.reg d] opn srcs, MemTag.reg none) with
  | some p =>
      obtain ⟨a, e⟩ := p
      obtain ⟨hop, rfl⟩ := cmpArgs?_shape h1
      simp only [h1, Option.map_some] at h ⊢
      rw [hA.evalOperandN 64 (o := a) (by simp), hA.evalOperandN 64 (o := e) (by simp)]
      cases hva : evalOperandN s.reg 64 a <;> cases hvb : evalOperandN s.reg 64 e <;>
        simp only [hva, hvb, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨none, s.cf, s.of, rfl, fun _ => hop, ?_⟩
      simp only [writeDstF, ← hcf, ← hof]
      exact ⟨rfl, trivial⟩
  | none =>
  simp only [h1, Option.map_none] at h ⊢
  cases h2 : movRegArgs? (LinstrR.Lopn [.reg d] opn srcs, MemTag.reg none) with
  | some p =>
      obtain ⟨d', a⟩ := p
      obtain ⟨rfl, rfl⟩ := movRegArgs?_shape h2
      simp only [h2, Option.map_some] at h ⊢
      rw [hA.readReg_reg (x := a) (by simp)]
      cases hr : JasminLsemWidthN.readReg s.reg (.reg a) with
      | none => simp [hr] at h
      | some wv =>
          obtain ⟨w, v⟩ := wv
          simp only [hr, Option.some.injEq, Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨some ⟨w, v⟩, s.cf, s.of, rfl, by simp, ?_⟩
          simp only [writeDstF, ← hcf, ← hof]
          exact ⟨rfl, trivial⟩
  | none =>
  simp only [h2, Option.map_none] at h ⊢
  unfold stepMemF at h ⊢
  rw [lsemStepMem_reg] at h
  cases hm : lsemStepCast (LinstrR.Lopn [.reg d] opn srcs, none) s.reg with
  | some r =>
      rw [lsemStepMem_reg]
      obtain ⟨w, v, rfl, hm'⟩ := lsemStepCast_val (c := c) none hwf hA hm
      simp only [hm, hm', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      have hf := withALUFlags_val (d := d) (c := c) (opn := opn) (tg := .reg none) (s := s)
        (s' := s')
        (b := { reg := (s.reg.setReg d v).nextPc, larr := s.larr, lmem := s.lmem, cf := s.cf,
                of := s.of })
        (b' := { reg := (s'.reg.setReg c v).nextPc, larr := s'.larr, lmem := s'.lmem,
                 cf := s'.cf, of := s'.of }) hA hcf hof
      refine ⟨some ⟨w, v⟩, (withALUFlags (LinstrR.Lopn [.reg d] opn srcs, MemTag.reg none) s
        { reg := (s.reg.setReg d v).nextPc, larr := s.larr, lmem := s.lmem, cf := s.cf,
          of := s.of }).cf, (withALUFlags (LinstrR.Lopn [.reg d] opn srcs, MemTag.reg none) s
        { reg := (s.reg.setReg d v).nextPc, larr := s.larr, lmem := s.lmem, cf := s.cf,
          of := s.of }).of, ?_, by simp, ?_, rfl⟩
      · apply lstateM_ext <;> simp [writeDstF, LstateM.setReg, LstateM.nextPc]
      · apply lstateM_ext <;> simp [writeDstF, LstateM.setReg, LstateM.nextPc, hf.1, hf.2]
  | none =>
  simp only [hm, Option.map_none] at h
  rw [carryArgs?_val d c opn srcs σ]
  cases h3 : carryArgs? (LinstrR.Lopn [.reg d] opn srcs, MemTag.reg none) with
  | some p =>
      obtain ⟨op, d', a, e⟩ := p
      obtain ⟨rfl, rfl⟩ := carryArgs?_shape h3
      have h3' := carryArgs?_val d' c opn [a, e] σ (.reg none)
      rw [h3, Option.map_some] at h3'
      rw [JasminLsemExportRewrites.lsemStepMem_of_carryArgs h3' s']
      simp only [h3, Option.map_some, Option.map_eq_some_iff, Prod.mk.injEq] at h ⊢
      obtain ⟨t0, ht0, rfl, rfl⟩ := h
      unfold carryStep at ht0 ⊢
      rw [hA.evalOperandN 64 (o := a) (by simp), hA.evalOperandN 64 (o := e) (by simp), hcf, hof]
      split at ht0
      · cases op <;> cases ht0 <;>
          refine ⟨some ⟨64, _⟩, _, _, rfl, by simp, _, rfl, ?_, rfl⟩ <;>
          apply lstateM_ext <;> simp [writeDstF, LstateM.setReg, LstateM.nextPc, hcf, hof]
      · cases ht0
  | none =>
  simp only [h3] at h
  rw [wideArgs?_val d c opn srcs σ]
  cases h4 : wideArgs? (LinstrR.Lopn [.reg d] opn srcs, MemTag.reg none) with
  | some w =>
      obtain ⟨a, e, rfl, rfl⟩ := wideArgs?_shape h4
      have h4' := wideArgs?_val d c opn [a, e] σ (.reg none)
      rw [h4, Option.map_some] at h4'
      rw [JasminLsemExportRewrites.lsemStepMem_of_wideArgs h4' s']
      simp only [h4, Option.map_some, Option.map_eq_some_iff, Prod.mk.injEq] at h ⊢
      obtain ⟨t0, ht0, rfl, rfl⟩ := h
      simp only [wideStep] at ht0
      simp only [wideRen, wideStep]
      rw [hA.evalOperandN 64 (o := e) (by simp)]
      cases hv : evalOperandN s.reg 64 e with
      | none => simp [hv] at ht0
      | some v =>
        simp only [hv, Option.some.injEq] at ht0
        subst ht0
        refine ⟨some ⟨64, v⟩, s.cf, s.of, rfl, by simp, _, rfl, ?_, trivial⟩
        apply lstateM_ext <;> simp [writeDstF, LstateM.setReg, LstateM.nextPc, hcf, hof]
  | none =>
  simp [h4] at h

/-- A step whose instruction is no flag compare, no flag-writing arithmetic and no carry
    instruction keeps the zero, carry and overflow flags. -/
theorem fstepF_flags {i : LinstrRM} (hc : cmpArgs? i = none) (ha : aluFlagOp? i = none)
    (hk : carryArgs? i = none) {s t : LstateM} {zf zt : Bool}
    (h : fstepF i s zf = some (t, zt)) : zt = zf ∧ t.cf = s.cf ∧ t.of = s.of := by
  unfold fstepF at h
  rw [hc] at h
  simp only at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl⟩
    · cases h
  · obtain ⟨b, hb, hbt⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hbt
    obtain ⟨rfl, rfl⟩ := hbt
    refine ⟨rfl, ?_⟩
    unfold stepMemF at hb
    cases hm : lsemStepMem i s with
    | some b' =>
        rw [hm] at hb
        cases hb
        rw [withALUFlags_of_none ha]
        exact JasminLsemExportRewrites.lsemStepMem_flags hm
    | none =>
        rw [hm, hk] at hb
        simp only at hb
        split at hb
        · rename_i w _
          cases w <;> simp only [wideStep] at hb <;> split at hb <;> cases hb <;> exact ⟨rfl, rfl⟩
        · cases hb

theorem withWidthTag_64 (m : String) : withWidthTag 64 m = m ++ ":64" := by
  simp [withWidthTag]

/-- A move mnemonic is no flag compare, no flag-writing arithmetic and no carry mnemonic. -/
theorem movClass_recog {opn : String} (hm : movClass opn = true) (ds ss : List LOperand)
    (tg : MemTag) :
    cmpArgs? (.Lopn ds opn ss, tg) = none ∧ aluFlagOp? (.Lopn ds opn ss, tg) = none
      ∧ carryArgs? (.Lopn ds opn ss, tg) = none := by
  have hne : ∀ x ∈ ["CMP", "ADD", "SUB", "AND", "OR", "XOR", "ADC", "SBB", "ADCX", "ADOX"],
      opn ≠ withWidthTag 64 x := by
    intro x hx he
    subst he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      revert hm <;> decide +kernel
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hne
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hne
  refine ⟨?_, ?_, ?_⟩
  · unfold cmpArgs?; dsimp only; split
    · rename_i heq
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, -⟩ := heq
      simp [h1]
    · rfl
  · unfold aluFlagOp?; dsimp only; split
    · rename_i heq
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, -⟩ := heq
      simp [h2, h3, h4, h5, h6]
    · rfl
  · unfold carryArgs?; dsimp only; split
    · rename_i heq
      simp only [LinstrR.Lopn.injEq] at heq
      obtain ⟨-, rfl, -⟩ := heq
      simp [h7, h8, h9, h10]
    · rfl

end Val

/-! ## 2. The check of a run on the flag machine -/

section Check

variable {abi : IsaAbi}

/-- A fragment instruction on the flag machine, with the register tag. -/
def tyF (i : FI) : LinstrRM := (i.toR, .reg none)

/-- The relation between a source state `s` and a renamed state `s'` on the flag machine:
    equal arrays, word memory and carry and overflow flags, equal registers at every name
    that is not a location, and every live location name `n` holding its source cell at its
    location `look m n`. -/
def FRel (m : Cur) (L : List String) (abi : IsaAbi) (s s' : LstateM) : Prop :=
  s'.larr = s.larr ∧ s'.lmem = s.lmem ∧ s'.cf = s.cf ∧ s'.of = s.of
    ∧ (∀ x, isLoc x abi = false → s'.reg.lvm x = s.reg.lvm x)
    ∧ ∀ n ∈ L, isLoc n abi = true →
        isLoc (look m n) abi = true ∧ s'.reg.lvm (look m n) = s.reg.lvm n

/-- Agreement at the end of a run on the flag machine: equal arrays, word memory and carry
    and overflow flags, and equal registers at every name that is not a location or is live
    out. -/
def FFinal (lend : List String) (abi : IsaAbi) (s s' : LstateM) : Prop :=
  s'.larr = s.larr ∧ s'.lmem = s.lmem ∧ s'.cf = s.cf ∧ s'.of = s.of
    ∧ ∀ x, (isLoc x abi = false ∨ x ∈ lend) → s'.reg.lvm x = s.reg.lvm x

/-- The renaming of `renOp m`: a location to its current location, any other name to
    itself. -/
def renOf (m : Cur) (abi : IsaAbi) (n : String) : String := if isLoc n abi then look m n else n

theorem renOp_eq (m : Cur) {o : LOperand} (h : regOrImm o = true) :
    renOp m o abi = renOperand (renOf m abi) o := by
  cases o with
  | reg n => by_cases hn : isLoc n abi = true <;> simp [renOp, renOf, renOperand, hn]
  | imm _ => rfl
  | _ => simp [regOrImm] at h

theorem map_renOp_eq (m : Cur) {srcs : List LOperand} (h : srcs.all regOrImm = true) :
    srcs.map (fun o => renOp m o abi) = srcs.map (renOperand (renOf m abi)) :=
  List.map_congr_left (fun o ho => renOp_eq m (List.all_eq_true.1 h o ho))

@[simp] theorem applyW_larr (s : LstateM) (d : String) (wr : Option (Σ w, BitVec w))
    (cf of : Bool) : (writeDstF s d wr cf of).larr = s.larr := by
  unfold writeDstF; cases wr <;> rfl

@[simp] theorem applyW_lmem (s : LstateM) (d : String) (wr : Option (Σ w, BitVec w))
    (cf of : Bool) : (writeDstF s d wr cf of).lmem = s.lmem := by
  unfold writeDstF; cases wr <;> rfl

@[simp] theorem applyW_cf (s : LstateM) (d : String) (wr : Option (Σ w, BitVec w))
    (cf of : Bool) : (writeDstF s d wr cf of).cf = cf := rfl

@[simp] theorem applyW_of (s : LstateM) (d : String) (wr : Option (Σ w, BitVec w))
    (cf of : Bool) : (writeDstF s d wr cf of).of = of := rfl

theorem applyW_lvm (s : LstateM) (d : String) (wr : Option (Σ w, BitVec w)) (cf of : Bool)
    (y : String) :
    (writeDstF s d wr cf of).reg.lvm y
      = match wr with
        | some v => if y = d then v else s.reg.lvm y
        | none => s.reg.lvm y := by
  unfold writeDstF
  cases wr <;> simp [LstateM.setReg, LstateM.nextPc]

theorem applyW_lvm_some (s : LstateM) (d : String) (v : Σ w, BitVec w) (cf of : Bool) :
    (writeDstF s d (some v) cf of).reg.lvm d = v := by
  simp [writeDstF, LstateM.setReg, LstateM.nextPc]

theorem applyW_lvm_none (s : LstateM) (d : String) (cf of : Bool) (y : String) :
    (writeDstF s d none cf of).reg.lvm y = s.reg.lvm y := rfl

theorem applyW_lvm_ne (s : LstateM) {d y : String} (wr : Option (Σ w, BitVec w))
    (cf of : Bool) (h : y ≠ d) : (writeDstF s d wr cf of).reg.lvm y = s.reg.lvm y := by
  rw [applyW_lvm]; cases wr <;> simp [h]

theorem SrcAgree_of_FRel {m : Cur} {L : List String} {s s' : LstateM} {i : FI}
    (habi : isLoc "" abi = false) (hR : FRel m L abi s s') (hL : ∀ n ∈ i.reads abi, n ∈ L) :
    SrcAgree (renOf m abi) i.srcs s.reg s'.reg := by
  refine ⟨fun x hx => ?_, hR.2.2.2.2.1 "" habi⟩
  by_cases hl : isLoc x abi = true
  · have hr : x ∈ i.reads abi := by
      simp only [FI.reads, List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨.reg x, hx, by simp [opReads, hl]⟩
    simp only [renOf, hl, if_true]
    exact (hR.2.2.2.2.2 x (hL x hr) hl).2
  · simp only [Bool.not_eq_true] at hl
    simp only [renOf, hl]
    exact hR.2.2.2.2.1 x hl

/-- The flag compare has the fixed printer shape. -/
theorem shapeOf_cmp {i : FI} (h : i.opn = withWidthTag 64 "CMP") : shapeOf i = .fixed := by
  have h1 : freeUnary i.opn = false := by rw [h]; decide +kernel
  have h2 : (stripAbiTag i.opn == "ANDN") = false := by rw [h]; decide +kernel
  have h3 : tiedOpn i.opn = false := by rw [h]; decide +kernel
  simp [shapeOf, h1, h2, h3]

/-- The relation after a write of a location destination `i.d` at the location `c`. -/
theorem FRel.loc {m : Cur} {la : List String} {i : FI} {c : String} {s s' s1 s1' : LstateM}
    (hR : FRel m (liveBefore i la abi) abi s s') (hd : isLoc i.d abi = true)
    (hc : isLoc c abi = true) (harr : s1'.larr = s1.larr) (hmem : s1'.lmem = s1.lmem)
    (hcf : s1'.cf = s1.cf) (hof : s1'.of = s1.of)
    (hs1 : ∀ y, y ≠ i.d → s1.reg.lvm y = s.reg.lvm y)
    (hs1' : ∀ x, isLoc x abi = false → s1'.reg.lvm x = s'.reg.lvm x)
    (hkeep : ∀ n ∈ la, isLoc n abi = true → n ≠ i.d →
      s1'.reg.lvm (look m n) = s'.reg.lvm (look m n))
    (hw : s1'.reg.lvm c = s1.reg.lvm i.d) :
    FRel (m.insert i.d c) la abi s1 s1' := by
  refine ⟨harr, hmem, hcf, hof, fun x hx => ?_, fun n hn hnl => ?_⟩
  · have hxd : x ≠ i.d := fun h => by rw [h, hd] at hx; exact absurd hx (by simp)
    rw [hs1' x hx, hR.2.2.2.2.1 x hx, hs1 x hxd]
  · rw [look_insert]
    by_cases hnd : n = i.d
    · subst hnd
      simp only [if_true]
      exact ⟨hc, hw⟩
    · rw [if_neg (Ne.symm hnd)]
      have h := hR.2.2.2.2.2 n (mem_liveBefore hn hnd) hnl
      exact ⟨h.1, by rw [hkeep n hn hnl hnd, h.2, hs1 n hnd]⟩

/-- The relation after a write of a destination `i.d` that is no location, at itself. -/
theorem FRel.nonloc {m : Cur} {la : List String} {i : FI} {s s' s1 s1' : LstateM}
    (hR : FRel m (liveBefore i la abi) abi s s') (hd : isLoc i.d abi = false)
    (harr : s1'.larr = s1.larr) (hmem : s1'.lmem = s1.lmem)
    (hcf : s1'.cf = s1.cf) (hof : s1'.of = s1.of)
    (hs1 : ∀ y, y ≠ i.d → s1.reg.lvm y = s.reg.lvm y)
    (hs1' : ∀ y, y ≠ i.d → s1'.reg.lvm y = s'.reg.lvm y)
    (hw : s1'.reg.lvm i.d = s1.reg.lvm i.d) :
    FRel m la abi s1 s1' := by
  refine ⟨harr, hmem, hcf, hof, fun x hx => ?_, fun n hn hnl => ?_⟩
  · by_cases hxd : x = i.d
    · subst hxd; exact hw
    · rw [hs1' x hxd, hR.2.2.2.2.1 x hx, hs1 x hxd]
  · have hnd : n ≠ i.d := fun h => by rw [h, hd] at hnl; exact absurd hnl (by simp)
    have h := hR.2.2.2.2.2 n (mem_liveBefore hn hnd) hnl
    have hne : look m n ≠ i.d := fun e => by rw [e, hd] at h; exact absurd h.1 (by simp)
    exact ⟨h.1, by rw [hs1' _ hne, h.2, hs1 n hnd]⟩

/-- The relation after a source write of a location destination that is dead after it,
    with no target step. -/
theorem FRel.dead {m : Cur} {la : List String} {i : FI} {s s' s1 : LstateM}
    (hR : FRel m (liveBefore i la abi) abi s s') (hd : isLoc i.d abi = true)
    (hdead : i.d ∉ la) (harr : s1.larr = s.larr) (hmem : s1.lmem = s.lmem)
    (hcf : s1.cf = s.cf) (hof : s1.of = s.of)
    (hs1 : ∀ y, y ≠ i.d → s1.reg.lvm y = s.reg.lvm y) :
    FRel m la abi s1 s' := by
  refine ⟨by rw [harr]; exact hR.1, by rw [hmem]; exact hR.2.1, by rw [hcf]; exact hR.2.2.1,
    by rw [hof]; exact hR.2.2.2.1, fun x hx => ?_, fun n hn hnl => ?_⟩
  · have hxd : x ≠ i.d := fun h => by rw [h, hd] at hx; exact absurd hx (by simp)
    rw [hR.2.2.2.2.1 x hx, hs1 x hxd]
  · have hnd : n ≠ i.d := fun h => hdead (h ▸ hn)
    have h := hR.2.2.2.2.2 n (mem_liveBefore hn hnd) hnl
    exact ⟨h.1, by rw [h.2, hs1 n hnd]⟩

/-- A step of the flag machine as `writeDstF` changes at most its destination. -/
theorem applyW_other (s : LstateM) {d : String} (wr : Option (Σ w, BitVec w)) (cf of : Bool) :
    ∀ y, y ≠ d → (writeDstF s d wr cf of).reg.lvm y = s.reg.lvm y :=
  fun _ h => applyW_lvm_ne s wr cf of h

/-- The flag compare of the fragment reads its destination. -/
def CmpReadsDst (i : FI) : Prop := i.opn = withWidthTag 64 "CMP" → LOperand.reg i.d ∈ i.srcs

theorem runStraightF_cons_some {i : LinstrRM} {is : List LinstrRM} {s t : LstateM}
    {zf zt : Bool} (h : runStraightF (i :: is) s zf = some (t, zt)) :
    ∃ s1 z1, fstepF i s zf = some (s1, z1) ∧ runStraightF is s1 z1 = some (t, zt) := by
  rw [runStraightF_cons] at h
  cases hs : fstepF i s zf with
  | none => rw [hs] at h; cases h
  | some p => rw [hs, Option.bind_some] at h; exact ⟨p.1, p.2, rfl, h⟩

/-- **Soundness of the check on the flag machine.** When `goAcc` accepts decisions `cs` for
    the annotated run of `is`, and the source run of `is` on the flag machine from `s` ends in
    `t`, the materialized run from any `s'` related to `s` on the names live at the start
    ends with the same zero flag in a state that agrees with `t` on the arrays, the word
    memory, the carry and overflow flags, every non-location name and every live-out name. -/
theorem goAccF_sound (habi : isLoc "" abi = false) (lend : List String) :
    ∀ (is : List FI) (m : Cur) (cs : List String) (acc out : List FI) (s t s' : LstateM)
      (zf zt : Bool),
      (∀ i ∈ is, i.wf = true) → (∀ i ∈ is, CmpReadsDst i) →
      goAcc lend m (annotate lend is abi).1 cs acc abi = some out →
      FRel m (annotate lend is abi).2 abi s s' →
      runStraightF (is.map tyF) s zf = some (t, zt) →
      ∃ rest t', out = acc.reverse ++ rest
        ∧ runStraightF (rest.map tyF) s' zf = some (t', zt) ∧ FFinal lend abi t t' := by
  intro is
  induction is with
  | nil =>
    intro m cs acc out s t s' zf zt _ _ hgo hR hrun
    cases cs with
    | cons _ _ => simp [annotate, goAcc] at hgo
    | nil =>
      simp only [annotate, List.foldr_nil, goAcc] at hgo hR
      split at hgo
      · rename_i hall
        simp only [Option.some.injEq] at hgo
        simp only [List.map_nil, runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        subst hgo
        refine ⟨[], s', by simp, rfl, hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1, fun x hx => ?_⟩
        by_cases hl : isLoc x abi = true
        · have hxl : x ∈ lend := by
            rcases hx with h | h
            · simp [hl] at h
            · exact h
          have h1 := (hR.2.2.2.2.2 x hxl hl).2
          have h2 : look m x = x := by simpa using List.all_eq_true.1 hall x hxl
          rw [h2] at h1
          exact h1
        · exact hR.2.2.2.2.1 x (by simpa using hl)
      · exact absurd hgo (by simp)
  | cons i is ih =>
    intro m cs acc out s t s' zf zt hwf hcmp hgo hR hrun
    have hwfi : i.wf = true := hwf i (by simp)
    have hwfs : ∀ j ∈ is, j.wf = true := fun j hj => hwf j (by simp [hj])
    have hcmps : ∀ j ∈ is, CmpReadsDst j := fun j hj => hcmp j (by simp [hj])
    have hsrc := wf_of_srcs hwfi
    have hwfl : ∀ o ∈ i.srcs, regOrImm o = true := fun o ho => List.all_eq_true.1 hsrc o ho
    rw [annotate_cons] at hgo hR
    set la := (annotate lend is abi).2 with hla
    simp only [List.map_cons] at hrun
    obtain ⟨s1, z1, hst, hrest⟩ := runStraightF_cons_some hrun
    have hreads : ∀ n ∈ i.reads abi, n ∈ liveBefore i la abi :=
      fun n hn => reads_mem_liveBefore hn
    change FRel m (liveBefore i la abi) abi s s' at hR
    have hA := SrcAgree_of_FRel habi hR hreads
    have hst' : fstepF (.Lopn [.reg i.d] i.opn i.srcs, .reg none) s zf = some (s1, z1) := hst
    cases cs with
    | nil => simp [goAcc] at hgo
    | cons c cs =>
    simp only [goAcc] at hgo
    by_cases hb : basesOk m i abi = true
    swap
    · rw [if_neg hb] at hgo; exact absurd hgo (by simp)
    rw [if_pos hb] at hgo
    by_cases hd : isLoc i.d abi = true
    · rw [if_pos hd] at hgo
      by_cases hok : (okLoc i.d c abi && shapeOk m i c abi) = true
      swap
      · rw [if_neg hok] at hgo; exact absurd hgo (by simp)
      rw [if_pos hok] at hgo
      have hc : isLoc c abi = true := by
        simp only [Bool.and_eq_true, okLoc, Bool.or_eq_true, beq_iff_eq] at hok
        rcases hok.1 with h | h
        · exact isLoc_of_isPool h
        · rw [h]; exact hd
      by_cases hcp :
          (isCopy64 i.opn && i.srcs.map (fun o => renOp m o abi) == [.reg c]) = true
      · -- a self-copy: dropped
        rw [if_pos hcp] at hgo
        simp only [Bool.and_eq_true, beq_iff_eq] at hcp
        obtain ⟨hcopyi, hmap⟩ := hcp
        obtain ⟨o, hso, hro⟩ : ∃ o, i.srcs = [o] ∧ renOp m o abi = .reg c := by
          rcases hs : i.srcs with _ | ⟨o, _ | ⟨o2, t⟩⟩ <;> rw [hs] at hmap <;> simp at hmap
          exact ⟨o, rfl, hmap⟩
        rw [renOp_eq m (hwfl o (by simp [hso]))] at hro
        obtain ⟨x, rfl, hxc⟩ := (JasminLsemExportRewrites.renOperand_eq_reg _ _ _).1 hro
        have hcop : i.opn = "MOV:64" ∨ i.opn = "MOVQ" := by
          simpa [isCopy64] using hcopyi
        have hmc : movClass i.opn = true := by
          rcases hcop with h | h <;> rw [h] <;> decide +kernel
        have hcm := (movClass_recog hmc [.reg i.d] [.reg x] (.reg none)).1
        have hmv : movRegArgs? (LinstrR.Lopn [.reg i.d] i.opn [.reg x], MemTag.reg none)
            = some (i.d, x) := by
          unfold movRegArgs?
          rcases hcop with h | h
          · rw [h]; simp only; rw [if_pos (by decide +kernel)]
          · rw [h]; simp
        rw [hso, fstepF_copy hcm hmv] at hst'
        simp only [Option.some.injEq, Prod.mk.injEq] at hst'
        obtain ⟨rfl, rfl⟩ := hst'
        have hxc' : s'.reg.lvm c = s.reg.lvm x := by rw [← hxc]; exact hA.1 x (by simp [hso])
        refine ih (m.insert i.d c) cs acc out _ t s' zf zt hwfs hcmps hgo ?_ hrest
        refine FRel.loc hR hd hc ?_ ?_ ?_ ?_ (fun y hy => ?_) (fun _ _ => rfl)
          (fun _ _ _ _ => rfl) ?_
        all_goals simp_all [LstateM.setReg, LstateM.nextPc, hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1]
      · rw [if_neg hcp] at hgo
        obtain ⟨wr, cf, of, rfl, hcw, htgt⟩ := fstepF_val (c := c) (σ := renOf m abi) hwfl hA
          hR.2.2.1 hR.2.2.2.1 hst'
        by_cases hdead : (movClass i.opn && !la.contains i.d) = true
        · -- a dead move: dropped
          rw [if_pos hdead] at hgo
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
            decide_eq_false_iff_not] at hdead
          have hr := movClass_recog hdead.1 [.reg i.d] i.srcs (.reg none)
          obtain ⟨rfl, hcf1, hof1⟩ := fstepF_flags hr.1 hr.2.1 hr.2.2 hst'
          refine ih m cs acc out _ t s' z1 zt hwfs hcmps hgo ?_ hrest
          exact FRel.dead hR hd hdead.2 (by simp) (by simp) hcf1 hof1 (applyW_other s wr cf of)
        · rw [if_neg hdead] at hgo
          by_cases hnc : noClobber m la i.d c = true
          swap
          · rw [if_neg hnc] at hgo; exact absurd hgo (by simp)
          rw [if_pos hnc] at hgo
          let i' : FI := ⟨i.ii, c, i.opn, i.srcs.map (fun o => renOp m o abi)⟩
          have hstep' : fstepF (tyF i') s' zf = some (writeDstF s' c wr cf of, z1) := by
            show fstepF (.Lopn [.reg c] i.opn (i.srcs.map _), .reg none) s' zf = _
            rw [map_renOp_eq m hsrc]
            exact htgt
          have hR' : FRel (m.insert i.d c) la abi (writeDstF s i.d wr cf of)
              (writeDstF s' c wr cf of) := by
            refine FRel.loc hR hd hc (by simp [hR.1]) (by simp [hR.2.1]) rfl rfl
              (applyW_other s wr cf of) (fun x hx => applyW_lvm_ne s' wr cf of
                (fun e => by rw [e, hc] at hx; exact absurd hx (by simp)))
              (fun n hn _ hnd => applyW_lvm_ne s' wr cf of ?_) ?_
            · have h1 := List.all_eq_true.1 hnc n hn
              simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1
              rcases h1 with h1 | h1
              · exact absurd h1 hnd
              · exact h1
            · cases wr with
              | some v => rw [applyW_lvm_some, applyW_lvm_some]
              | none =>
                have hop := hcw rfl
                have hfix := shapeOf_cmp hop
                have hdin := hcmp i (by simp) hop
                simp only [Bool.and_eq_true] at hok
                have hsh := hok.2
                unfold shapeOk at hsh
                rw [hfix] at hsh
                simp only [Bool.and_eq_true, beq_iff_eq] at hsh
                obtain ⟨hcd, hall⟩ := hsh
                rw [hcd]
                have hdr : i.d ∈ i.reads abi := by
                  simp only [FI.reads, List.mem_append, List.mem_flatMap]
                  exact Or.inl ⟨.reg i.d, hdin, by simp [opReads, hd]⟩
                have h2 := (hR.2.2.2.2.2 i.d (hreads _ hdr) hd).2
                have h3 : look m i.d = i.d := by
                  have := List.all_eq_true.1 hall _ hdr
                  simpa using this
                rw [h3] at h2
                rw [applyW_lvm_none, applyW_lvm_none, h2]
          obtain ⟨rest, t', hout, hr', hfin⟩ :=
            ih (m.insert i.d c) cs (i' :: acc) out _ t _ z1 zt hwfs hcmps hgo hR' hrest
          refine ⟨i' :: rest, t', by simp [hout], ?_, hfin⟩
          simp only [List.map_cons]
          rw [runStraightF_cons, hstep', Option.bind_some]
          exact hr'
    · -- a write to a non-location name
      rw [if_neg hd] at hgo
      simp only [Bool.not_eq_true] at hd
      by_cases hsh : shapeOk m i i.d abi = true
      swap
      · rw [if_neg hsh] at hgo; exact absurd hgo (by simp)
      rw [if_pos hsh] at hgo
      obtain ⟨wr, cf, of, rfl, hcw, htgt⟩ := fstepF_val (c := i.d) (σ := renOf m abi) hwfl hA
        hR.2.2.1 hR.2.2.2.1 hst'
      let i' : FI := ⟨i.ii, i.d, i.opn, i.srcs.map (fun o => renOp m o abi)⟩
      have hstep' : fstepF (tyF i') s' zf = some (writeDstF s' i.d wr cf of, z1) := by
        show fstepF (.Lopn [.reg i.d] i.opn (i.srcs.map _), .reg none) s' zf = _
        rw [map_renOp_eq m hsrc]
        exact htgt
      have hR' : FRel m la abi (writeDstF s i.d wr cf of) (writeDstF s' i.d wr cf of) := by
        refine FRel.nonloc hR hd (by simp [hR.1]) (by simp [hR.2.1]) rfl rfl
          (applyW_other s wr cf of) (applyW_other s' wr cf of) ?_
        cases wr with
        | some v => rw [applyW_lvm_some, applyW_lvm_some]
        | none => rw [applyW_lvm_none, applyW_lvm_none, hR.2.2.2.2.1 i.d hd]
      obtain ⟨rest, t', hout, hr', hfin⟩ :=
        ih m cs (i' :: acc) out _ t _ z1 zt hwfs hcmps hgo hR' hrest
      refine ⟨i' :: rest, t', by simp [hout], ?_, hfin⟩
      simp only [List.map_cons]
      rw [runStraightF_cons, hstep', Option.bind_some]
      exact hr'

/-- Two flag-machine states agree off a name set `D`: equal arrays, word memory and carry
    and overflow flags, and equal registers at every name outside `D`. -/
def AgreeOff (D : String → Prop) (s s' : LstateM) : Prop :=
  s'.larr = s.larr ∧ s'.lmem = s.lmem ∧ s'.cf = s.cf ∧ s'.of = s.of
    ∧ ∀ y, ¬ D y → s'.reg.lvm y = s.reg.lvm y

/-- A fragment instruction names its destination and its register sources. -/
def fiNames (i : FI) : List String := i.d :: i.srcs.flatMap (fun o => match o with
  | .reg x => [x]
  | _ => [])

theorem mem_names_of_src {i : FI} {x : String} (h : LOperand.reg x ∈ i.srcs) : x ∈ fiNames i := by
  simp only [fiNames, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨.reg x, h, by simp⟩

/-- **A run from states that agree off names the run does not use.** -/
theorem runSame {D : String → Prop} (hemp : ¬ D "") :
    ∀ (is : List FI) (s s' t : LstateM) (zf zt : Bool),
      (∀ i ∈ is, i.wf = true) → (∀ i ∈ is, ∀ x ∈ fiNames i, ¬ D x) → AgreeOff D s s' →
      runStraightF (is.map tyF) s zf = some (t, zt) →
      ∃ t', runStraightF (is.map tyF) s' zf = some (t', zt) ∧ AgreeOff D t t' := by
  intro is
  induction is with
  | nil =>
      intro s s' t zf zt _ _ hA h
      simp only [List.map_nil, runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨s', rfl, hA⟩
  | cons i is ih =>
      intro s s' t zf zt hwf hn hA h
      simp only [List.map_cons] at h
      obtain ⟨s1, z1, hst, hrest⟩ := runStraightF_cons_some h
      have hwfl : ∀ o ∈ i.srcs, regOrImm o = true :=
        fun o ho => List.all_eq_true.1 (wf_of_srcs (hwf i (by simp))) o ho
      have hS : SrcAgree id i.srcs s.reg s'.reg :=
        ⟨fun x hx => hA.2.2.2.2 x (hn i (by simp) x (mem_names_of_src hx)), hA.2.2.2.2 "" hemp⟩
      obtain ⟨wr, cf, of, rfl, -, htgt⟩ :=
        fstepF_val (c := i.d) (σ := id) hwfl hS hA.2.2.1 hA.2.2.2.1 hst
      have hid : i.srcs.map (renOperand id) = i.srcs := by
        conv_rhs => rw [← List.map_id i.srcs]
        exact List.map_congr_left (fun o _ => renOperand_id o)
      rw [hid] at htgt
      have hA1 : AgreeOff D (writeDstF s i.d wr cf of) (writeDstF s' i.d wr cf of) := by
        refine ⟨by simp [hA.1], by simp [hA.2.1], rfl, rfl, fun y hy => ?_⟩
        by_cases hyd : y = i.d
        · subst hyd
          cases wr with
          | some v => rw [applyW_lvm_some, applyW_lvm_some]
          | none => rw [applyW_lvm_none, applyW_lvm_none, hA.2.2.2.2 _ hy]
        · rw [applyW_lvm_ne _ _ _ _ hyd, applyW_lvm_ne _ _ _ _ hyd, hA.2.2.2.2 _ hy]
      obtain ⟨t', ht', hAt⟩ := ih _ _ t z1 zt (fun j hj => hwf j (by simp [hj]))
        (fun j hj => hn j (by simp [hj])) hA1 hrest
      refine ⟨t', ?_, hAt⟩
      simp only [List.map_cons]
      rw [runStraightF_cons, show fstepF (tyF i) s' zf = some (writeDstF s' i.d wr cf of, z1) from htgt,
        Option.bind_some]
      exact ht'

/-- A name live at the start of a run is live out or read by an instruction of the run. -/
theorem mem_liveIn (lend : List String) :
    ∀ (is : List FI) (n : String), n ∈ (annotate lend is abi).2 →
      n ∈ lend ∨ ∃ i ∈ is, n ∈ i.reads abi := by
  intro is
  induction is with
  | nil => intro n h; exact Or.inl h
  | cons i is ih =>
      intro n h
      rw [annotate_cons] at h
      rcases (mem_addNew _ _ _).1 h with h | h
      · exact Or.inr ⟨i, by simp, h⟩
      · rcases ih n (List.mem_filter.1 h).1 with h' | ⟨j, hj, h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨j, by simp [hj], h'⟩

/-- **The pass on one run on the flag machine.** From two states that agree off a set `D`
    of locations that no instruction of the run names or reads and that is disjoint from
    the live-out set `lend`, a run of `is` on the flag machine is matched by a run of
    `reallocRun lend is abi` with the same zero flag, into a state that agrees with it on the
    arrays, the word memory, the carry and overflow flags, every non-location name and every
    live-out name. -/
theorem reallocRunF (habi : isLoc "" abi = false) {D : String → Prop}
    (hDloc : ∀ y, D y → isLoc y abi = true) (lend : List String) (is : List FI)
    (hwf : ∀ i ∈ is, i.wf = true) (hcmp : ∀ i ∈ is, CmpReadsDst i)
    (hn : ∀ i ∈ is, ∀ x, (x ∈ fiNames i ∨ x ∈ i.reads abi) → ¬ D x)
    (hlend : ∀ x ∈ lend, ¬ D x) {s s' t : LstateM} {zf zt : Bool} (hA : AgreeOff D s s')
    (h : runStraightF (is.map tyF) s zf = some (t, zt)) :
    ∃ t', runStraightF ((reallocRun lend is abi).map tyF) s' zf = some (t', zt)
      ∧ FFinal lend abi t t' := by
  have hemp : ¬ D "" := fun hd => by rw [hDloc _ hd] at habi; cases habi
  unfold reallocRun reallocWith
  split
  · rename_i out hf
    obtain ⟨cs, _, hcs⟩ := List.exists_of_findSome?_eq_some hf
    have hR : FRel {} (annotate lend is abi).2 abi s s' := by
      refine ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1,
        fun x hx => hA.2.2.2.2 x (fun hd => by rw [hDloc _ hd] at hx; cases hx),
        fun n hn' hnl => ⟨by rw [look_empty]; exact hnl, ?_⟩⟩
      rw [look_empty]
      refine hA.2.2.2.2 n ?_
      rcases mem_liveIn lend is n hn' with h1 | ⟨i, hi, h1⟩
      · exact hlend n h1
      · exact hn i hi n (Or.inr h1)
    obtain ⟨rest, t', hout, hr, hfin⟩ :=
      goAccF_sound habi lend is {} cs [] out s t s' zf zt hwf hcmp hcs hR h
    simp only [List.reverse_nil, List.nil_append] at hout
    subst hout
    exact ⟨t', hr, hfin⟩
  · obtain ⟨t', ht', hAt⟩ := runSame hemp is s s' t zf zt hwf
      (fun i hi x hx => hn i hi x (Or.inl hx)) hA h
    refine ⟨t', ht', hAt.1, hAt.2.1, hAt.2.2.1, hAt.2.2.2.1, fun x hx => hAt.2.2.2.2 x ?_⟩
    rcases hx with hx | hx
    · exact fun hd => by rw [hDloc _ hd] at hx; cases hx
    · exact hlend x hx

end Check

/-! ## 3. Block-local rewrites with a relation indexed by the source suffix

`CfgLift.lsemFuelMemFk_blockRel` relates the two bodies by equality up to the program
counter. The re-allocation leaves dead locations at other values, so the lift here carries a
relation `Q X` between the two bases that depends on the source suffix `X` at the program
counter. -/

section QLift

variable (Q : List LinstrRM → LstateM → LstateM → Prop)

/-- The side conditions of a kept control instruction `i` followed by `R`: a label passes the
    relation on to `R`, and a conditional passes it on and reads the same branch condition in
    related states. -/
def CtlQ (i : LinstrRM) (R : List LinstrRM) : Prop :=
  (∀ kd l, i.1 = LinstrR.Llabel kd l → ∀ a b, Q (i :: R) a b → Q R a b)
    ∧ (∀ c l, i.1 = LinstrR.Lcond c l → ∀ a b, Q (i :: R) a b → Q R a b ∧ condNZ b c = condNZ a c)

/-- The simulation of a rewritten segment `seg` followed by `R`: from states related at
    `seg ++ R`, a run of `seg` is matched by a run of `seg'` with the same zero flag into
    states related at `R`. -/
def QSim (seg seg' R : List LinstrRM) : Prop :=
  ∀ (s s' t : LstateM) (zf zt : Bool), Q (seg ++ R) s s' →
    runStraightF seg s zf = some (t, zt) →
    ∃ t', runStraightF seg' s' zf = some (t', zt) ∧ Q R t t'

/-- The relation between a body and its rewrite: kept control instructions alternate with
    non-empty `Lopn` segments rewritten to `Lopn` segments of at most the same length. -/
inductive QRel : List LinstrRM → List LinstrRM → Prop
  | nil : QRel [] []
  | ctl {i : LinstrRM} {R R' : List LinstrRM} :
      CtlKeep i → CtlQ Q i R → QRel R R' → QRel (i :: R) (i :: R')
  | blk {seg seg' R R' : List LinstrRM} :
      seg ≠ [] → seg'.length ≤ seg.length →
      (∀ i ∈ seg, IsLopn i) → (∀ i ∈ seg', IsLopn i) →
      QSim Q seg seg' R → QRel R R' → QRel (seg ++ R) (seg' ++ R')

variable {Q}

theorem QRel.eq_nil {Y : List LinstrRM} (h : QRel Q [] Y) : Y = [] := by
  generalize hX : ([] : List LinstrRM) = X at h
  cases h with
  | nil => rfl
  | ctl _ _ _ => cases hX
  | blk hne _ _ _ _ _ => exact absurd (List.append_eq_nil_iff.mp hX.symm).1 hne

/-- A label position of the source body has a position in the target body, and the suffixes
    after the two labels are related. -/
theorem QRel.findLabelMem {B B' : List LinstrRM} (h : QRel Q B B') (l : LLabel) :
    ∀ pc, findLabelMem l B = some pc →
      ∃ pc', findLabelMem l B' = some pc' ∧ QRel Q (B.drop (pc + 1)) (B'.drop (pc' + 1)) := by
  induction h with
  | nil =>
      intro pc hpc
      simp [JasminLsemMemLoop.findLabelMem, JasminLsemLabeled.findLabel] at hpc
  | @ctl i R R' _ _ hR ih =>
      intro pc hpc
      rw [findLabelMem_cons] at hpc ⊢
      split at hpc
      · rename_i hl
        cases hpc
        exact ⟨0, if_pos hl, by simpa using hR⟩
      · rename_i hl
        obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hpc
        obtain ⟨k', hk', hd⟩ := ih k hk
        exact ⟨k' + 1, by rw [if_neg hl, hk']; rfl, by simpa using hd⟩
  | @blk seg seg' R R' _ _ hseg hseg' _ _ ih =>
      intro pc hpc
      rw [findLabelMem_prefix l seg R hseg] at hpc
      obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hpc
      obtain ⟨k', hk', hd⟩ := ih k hk
      refine ⟨k' + seg'.length, by rw [findLabelMem_prefix l seg' R' hseg', hk']; rfl, ?_⟩
      have e1 : (seg ++ R).drop (k + seg.length + 1) = R.drop (k + 1) := by
        rw [show k + seg.length + 1 = seg.length + (k + 1) from by omega]
        simp
      have e2 : (seg' ++ R').drop (k' + seg'.length + 1) = R'.drop (k' + 1) := by
        rw [show k' + seg'.length + 1 = seg'.length + (k' + 1) from by omega]
        simp
      rw [e1, e2]
      exact hd

/-- The state relation of the simulation: equal function name and zero flag, bases related
    at the source suffix, and related suffixes at the two program counters. -/
structure QS (Q : List LinstrRM → LstateM → LstateM → Prop) (P P' : LprogM) (s s' : LstateMF) :
    Prop where
  lfn : s'.prog.lfn = s.prog.lfn
  zf : s'.zf = s.zf
  base : Q (P.body.drop s.prog.base.lpc) s.prog.base s'.prog.base
  pc : QRel Q (P.body.drop s.prog.base.lpc) (P'.body.drop s'.prog.base.lpc)

/-- The relation is independent of the program counters. -/
def QPc (Q : List LinstrRM → LstateM → LstateM → Prop) : Prop :=
  ∀ X a b (p q : Nat), Q X a b → Q X (a.setLpc p) (b.setLpc q)

/-- A conditional or a goto at a source suffix passes the relation on to the suffix after
    every label of the body. -/
def QJump (Q : List LinstrRM → LstateM → LstateM → Prop) (B : List LinstrRM) : Prop :=
  ∀ k (i : LinstrRM) R, B.drop k = i :: R →
    ((∃ c l, i.1 = LinstrR.Lcond c l) ∨ ∃ tg, i.1 = LinstrR.Lgoto tg) →
    ∀ l pc, findLabelMem l B = some pc → ∀ a b, Q (i :: R) a b → Q (B.drop (pc + 1)) a b


theorem evalJumpMem_QRel {P P' : LprogM} (hB : QRel Q P.body P'.body) (hpc : QPc Q)
    (l : LLabel) {p p' q : LstatePM} {X : List LinstrRM} (hQ : Q X p.base p'.base)
    (hX : ∀ pc, findLabelMem l P.body = some pc → ∀ a b, Q X a b → Q (P.body.drop (pc + 1)) a b)
    (hfn : p'.lfn = p.lfn) (h : evalJumpMem P l p = some q) :
    ∃ q', evalJumpMem P' l p' = some q' ∧ q'.lfn = q.lfn
      ∧ Q (P.body.drop q.base.lpc) q.base q'.base
      ∧ QRel Q (P.body.drop q.base.lpc) (P'.body.drop q'.base.lpc) := by
  unfold evalJumpMem at h ⊢
  cases hl : JasminLsemMemLoop.findLabelMem l P.body with
  | none => simp [hl] at h
  | some pc =>
      obtain ⟨pc', hpc', hR⟩ := hB.findLabelMem l pc hl
      simp only [hl, Option.some.injEq] at h
      subst h
      rw [hpc']
      exact ⟨_, rfl, hfn, hpc _ _ _ _ _ (hX pc hl _ _ hQ), hR⟩

/-- **One step at a kept control instruction.** -/
theorem evalInstrPMemF_QRel {P P' : LprogM} (hfn : P'.lfn = P.lfn) (hpc : QPc Q)
    (hJ : QJump Q P.body) (hB : QRel Q P.body P'.body) {i : LinstrRM} (hi : CtlKeep i)
    {R R' : List LinstrRM} (hci : CtlQ Q i R) {s s' u : LstateMF} (hS : QS Q P P' s s')
    (hd : P.body.drop s.prog.base.lpc = i :: R)
    (hd' : P'.body.drop s'.prog.base.lpc = i :: R') (hRR : QRel Q R R')
    (he : evalInstrPMemF P i s = some u) :
    ∃ u', evalInstrPMemF P' i s' = some u' ∧ QS Q P P' u u' := by
  have hQ := hS.base
  rw [hd] at hQ
  have hnext : Q R s.prog.base s'.prog.base → QS Q P P'
      { s with prog := { s.prog with base := s.prog.base.nextPc } }
      { s' with prog := { s'.prog with base := s'.prog.base.nextPc } } := fun hq =>
    ⟨hS.lfn, hS.zf, by
      show Q (P.body.drop (s.prog.base.lpc + 1)) _ _
      rw [drop_succ_of_cons hd]
      exact hpc _ _ _ _ _ hq, by
      show QRel Q (P.body.drop (s.prog.base.lpc + 1)) (P'.body.drop (s'.prog.base.lpc + 1))
      rw [drop_succ_of_cons hd, drop_succ_of_cons hd']
      exact hRR⟩
  have hjump : ((∃ c l, i.1 = LinstrR.Lcond c l) ∨ ∃ tg, i.1 = LinstrR.Lgoto tg) →
      ∀ (lbl : LLabel) {q : LstatePM}, evalJumpMem P lbl s.prog = some q →
      ∃ q', evalJumpMem P' lbl s'.prog = some q'
        ∧ QS Q P P' { s with prog := q } { s' with prog := q' } := by
    intro hk lbl q hq
    obtain ⟨q', hq', hfq, hQq, hpq⟩ := evalJumpMem_QRel hB hpc lbl hQ
      (fun pc hl a b hab => hJ _ i R hd hk lbl pc hl a b hab) hS.lfn hq
    exact ⟨q', hq', ⟨hfq, hS.zf, hQq, hpq⟩⟩
  obtain ⟨wire, tag⟩ := i
  rcases hi with ⟨kd, l, hw⟩ | ⟨c, l, hw⟩ | ⟨tgt, hw⟩ | hst
  · obtain rfl : wire = LinstrR.Llabel kd l := hw
    rw [evalInstrPMemF_label] at he
    cases he
    exact ⟨_, evalInstrPMemF_label P' kd l tag s', hnext (hci.1 kd l rfl _ _ hQ)⟩
  · obtain rfl : wire = LinstrR.Lcond c l := hw
    obtain ⟨hQR, hc⟩ := hci.2 c l rfl _ _ hQ
    have hk : (∃ c' l', (LinstrR.Lcond c l, tag).1 = LinstrR.Lcond c' l') ∨
        ∃ tg, (LinstrR.Lcond c l, tag).1 = LinstrR.Lgoto tg := Or.inl ⟨c, l, rfl⟩
    have h1 : cmpArgs? (LinstrR.Lcond c l, tag) = none := rfl
    have h2 : movRegArgs? (LinstrR.Lcond c l, tag) = none := rfl
    cases h3 : flagCondCC? (LinstrR.Lcond c l, tag) with
    | none =>
        have hev : ∀ (Q : LprogM) (x : LstateMF),
            evalInstrPMemF Q (LinstrR.Lcond c l, tag) x
              = (if condNZ x.prog.base c then evalJumpMem Q l x.prog
                  else some { x.prog with base := x.prog.base.nextPc }).map
                  (fun p => { x with prog := p }) := fun Q x => by
          rw [evalInstrPMemF_delegate Q _ x rfl rfl h3 rfl rfl rfl]
          rfl
        rw [hev] at he ⊢
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
        split at hq
        · rename_i hz
          obtain ⟨q', hq', hRq⟩ := hjump hk l hq
          refine ⟨{ s' with prog := q' }, ?_, hRq⟩
          rw [hc, if_pos hz, hq']
          rfl
        · rename_i hz
          cases hq
          refine ⟨_, ?_, hnext hQR⟩
          rw [hc, if_neg hz]
          rfl
    | some pl =>
        obtain ⟨pol, lbl⟩ := pl
        unfold evalInstrPMemF at he ⊢
        simp only [h1, h2, h3] at he ⊢
        split at he
        · rename_i hz
          obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
          obtain ⟨q', hq', hRq⟩ := hjump hk lbl hq
          refine ⟨{ s' with prog := q' }, ?_, hRq⟩
          rw [if_pos (hS.zf.trans hz), hq']
          rfl
        · rename_i hz
          cases he
          refine ⟨_, ?_, hnext hQR⟩
          rw [if_neg (fun h => hz (hS.zf.symm.trans h))]
  · obtain rfl : wire = LinstrR.Lgoto tgt := hw
    obtain ⟨fn, l⟩ := tgt
    have hk : (∃ c' l', (LinstrR.Lgoto (fn, l), tag).1 = LinstrR.Lcond c' l') ∨
        ∃ tg, (LinstrR.Lgoto (fn, l), tag).1 = LinstrR.Lgoto tg := Or.inr ⟨_, rfl⟩
    have hev : ∀ (Q : LprogM) (x : LstateMF),
        evalInstrPMemF Q (LinstrR.Lgoto (fn, l), tag) x
          = (if fn = Q.lfn then evalJumpMem Q l x.prog else none).map
              (fun p => { x with prog := p }) := fun Q x => by
      rw [evalInstrPMemF_delegate Q _ x rfl rfl rfl rfl rfl rfl]
      rfl
    rw [hev] at he ⊢
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
    split at hq
    · rename_i hf
      obtain ⟨q', hq', hRq⟩ := hjump hk l hq
      refine ⟨{ s' with prog := q' }, ?_, hRq⟩
      rw [hfn, if_pos hf, hq']
      rfl
    · exact absurd hq (by simp)
  · rw [hst P s] at he
    cases he

/-- **The flag machine under a rewrite related by `QRel`.** Every halting run of `P` from a
    state related to a state of `P'` is matched by a halting run of `P'` with at most the same
    fuel, into a related state. -/
theorem lsemFuelMemF_QRel {P P' : LprogM} (hfn : P'.lfn = P.lfn) (hpc : QPc Q)
    (hJ : QJump Q P.body) (hB : QRel Q P.body P'.body) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, QS Q P P' s s' → lsemFuelMemF P fuel s = some t →
      ∃ fuel' t', fuel' ≤ fuel ∧ lsemFuelMemF P' fuel' s' = some t' ∧ QS Q P P' t t' := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro s s' t hS h
  cases hf : findInstrMem P s.prog with
  | none =>
      rw [lsemFuelMemF_halt P fuel s hf] at h
      cases h
      refine ⟨0, s', Nat.zero_le _, lsemFuelMemF_halt P' 0 s' ?_, hS⟩
      unfold findInstrMem at hf ⊢
      rw [hS.lfn, hfn]
      split
      · rename_i hl
        rw [if_pos hl] at hf
        have hd : P.body.drop s.prog.base.lpc = [] :=
          List.drop_eq_nil_iff.mpr (List.getElem?_eq_none_iff.mp hf)
        have hp := hS.pc
        rw [hd] at hp
        exact List.getElem?_eq_none_iff.mpr (List.drop_eq_nil_iff.mp hp.eq_nil)
      · rfl
  | some i =>
      have hfg : s.prog.lfn = P.lfn ∧ P.body[s.prog.base.lpc]? = some i := by
        unfold findInstrMem at hf
        split at hf
        · exact ⟨by assumption, hf⟩
        · simp at hf
      have hfl' : s'.prog.lfn = P'.lfn := hS.lfn.trans (hfg.1.trans hfn.symm)
      have hp := hS.pc
      have hQ := hS.base
      generalize hX : P.body.drop s.prog.base.lpc = X at hp hQ
      generalize hY : P'.body.drop s'.prog.base.lpc = Y at hp
      have hhead : X[0]? = some i := by
        rw [← hX, List.getElem?_drop]
        exact hfg.2
      cases hp with
      | nil => simp at hhead
      | @ctl i0 R R' hi hci hRR =>
          obtain rfl : i0 = i := by simpa using hhead
          have hfetch' : findInstrMem P' s'.prog = some i0 := by
            unfold findInstrMem
            rw [if_pos hfl']
            have := congrArg (·[0]?) hY
            simpa [List.getElem?_drop] using this
          cases fuel with
          | zero =>
              unfold lsemFuelMemF at h
              simp [hf] at h
          | succ n =>
              unfold lsemFuelMemF at h
              simp only [hf] at h
              cases he : evalInstrPMemF P i0 s with
              | none => simp [he] at h
              | some u =>
                  simp only [he] at h
                  obtain ⟨u', hu', hSu⟩ :=
                    evalInstrPMemF_QRel hfn hpc hJ hB hi hci hS hX hY hRR he
                  obtain ⟨f', t', hle, hrun, hSt⟩ := ih n (Nat.lt_succ_self n) hSu h
                  refine ⟨f' + 1, t', Nat.succ_le_succ hle, ?_, hSt⟩
                  rw [lsemFuelMemF_step P' f' i0 s' u' hfetch' hu']
                  exact hrun
      | @blk seg seg' R R' hne hlen hseg hseg' hsim hRR =>
          have hpos := getElem?_of_drop_append hX
          have hpos' := getElem?_of_drop_append hY
          have hge : seg.length ≤ fuel :=
            lsemFuelMemF_seg_fuel P s.prog.lfn hfg.1 seg s.prog.base s.zf fuel t hseg hpos h
          obtain ⟨f, rfl⟩ : ∃ f, fuel = seg.length + f := ⟨fuel - seg.length, by omega⟩
          have h2 := (lsemFuelMemF_segF P s.prog.lfn hfg.1 seg s.prog.base s.zf f hseg
            hpos).symm.trans h
          cases hr : runStraightF seg s.prog.base s.zf with
          | none => rw [hr] at h2; simp at h2
          | some bz =>
              obtain ⟨u, zu⟩ := bz
              rw [hr, Option.bind_some] at h2
              obtain ⟨u', hu', hQu⟩ := hsim _ _ _ _ _ hQ hr
              have h1 := runStraightF_lpc _ _ _ _ _ hr
              have h1' := runStraightF_lpc _ _ _ _ _ hu'
              have hSu : QS Q P P'
                  { prog := { base := u, lfn := s.prog.lfn }, zf := zu }
                  { prog := { base := u', lfn := s'.prog.lfn }, zf := zu } :=
                ⟨hS.lfn, rfl, by
                  show Q (P.body.drop u.lpc) u u'
                  rw [h1, drop_add_of_append hX]
                  exact hQu, by
                  show QRel Q (P.body.drop u.lpc) (P'.body.drop u'.lpc)
                  rw [h1, h1', drop_add_of_append hX, drop_add_of_append hY]
                  exact hRR⟩
              have hlt : f < seg.length + f := by
                have := List.length_pos_iff.mpr hne
                omega
              obtain ⟨f', t', hle, hrun, hSt⟩ := ih f hlt hSu h2
              have hsegF' := lsemFuelMemF_segF P' s'.prog.lfn hfl' seg' s'.prog.base s'.zf f'
                hseg' hpos'
              rw [← hS.zf] at hu'
              rw [hu', Option.bind_some] at hsegF'
              exact ⟨seg'.length + f', t', by omega, hsegF'.trans hrun, hSt⟩

end QLift

/-! ## 4. An instruction kept between the runs -/

section Bar

variable {D : String → Prop}

/-- An instruction writes no array at a name it does not mention. -/
theorem noArrWriteAt_of_not_mem {i : LinstrRM} {r : String} (h : r ∉ instrNames i.1) :
    NoArrWriteAt r i := by
  refine ⟨fun dst base idx val hs => ?_, fun dst hs => ?_, fun dst base val k hs => ?_⟩
  · rintro rfl; exact h (storeStruct?_names hs).1
  · rintro rfl; exact h (zeroStruct?_names hs)
  · rintro rfl; exact h (storeImmStruct?_names hs).1

/-- **An instruction from states that agree off names it does not mention.** A step of an
    `Lopn` that is no `MULX` is matched by its step from a state that agrees with the source
    state off a set `D` of names the instruction does not mention and that excludes the empty
    name, into states that agree off `D`, with the same zero flag. -/
theorem fstepF_bar_of_mulxFree {i : LinstrRM} (hl : IsLopn i) (hm : mulxFree i = true)
    (hD : ∀ n ∈ instrNames i.1, ¬ D n) (hemp : ¬ D "") {a b t : LstateM} {zf zt : Bool}
    (hA : AgreeOff D a b) (h : fstepF i a zf = some (t, zt)) :
    ∃ t', fstepF i b zf = some (t', zt) ∧ AgreeOff D t t' := by
  let N : String → Prop := fun n => ¬ D n
  have hσ : RenOn id N := ⟨fun _ _ _ _ h => h, hemp, rfl⟩
  have hP : RenProg id N 0 emptyP emptyP :=
    ⟨rfl, fun _ => rfl, fun k _ => by simp [emptyP], fun k i _ h => by simp [emptyP] at h,
      fun k i _ h => by simp [emptyP] at h, fun l pc h => by simp⟩
  let S : LstateMF := { prog := { base := a, lfn := "" }, zf := zf }
  let S' : LstateMF := { prog := { base := b.setLpc a.lpc, lfn := "" }, zf := zf }
  have hR : RelF id N S S' :=
    ⟨⟨⟨rfl, fun r hr => hA.2.2.2.2 r hr⟩, fun r _ => congrFun hA.1 r, hA.2.1⟩, rfl, rfl,
      hA.2.2.1, hA.2.2.2.1⟩
  have hc : CondOK i := ⟨fun c l he => (by
    obtain ⟨d, o, s0, hd⟩ := hl; rw [hd] at he; cases he), hm⟩
  have he : evalInstrPMemF emptyP i S
      = some { prog := { base := t, lfn := "" }, zf := zt } := by
    rw [evalInstrPMemF_isLopn _ i S hl]
    show (fstepF i a zf).map _ = _
    rw [h]; rfl
  obtain ⟨T', hT', hRT, -⟩ := evalInstrPMemF_ren hσ hP i hD hc hR (Nat.zero_le _) he
  rw [renRM_id, evalInstrPMemF_isLopn _ i S' hl] at hT'
  obtain ⟨bz, hb, rfl⟩ := Option.map_eq_some_iff.mp hT'
  have hb' : fstepF i (b.setLpc a.lpc) zf = some bz := hb
  rw [fstepF_setLpc] at hb'
  obtain ⟨⟨t'', z''⟩, h'', hbz⟩ := Option.map_eq_some_iff.mp hb'
  subst hbz
  obtain ⟨⟨⟨-, hreg⟩, harr, hmem⟩, -, hzf, hcf, hof⟩ := hRT
  have hzz : z'' = zt := hzf
  subst hzz
  refine ⟨t'', h'', funext fun r => ?_, hmem, hcf, hof, fun r hr => hreg r hr⟩
  by_cases hr : D r
  · have hna : r ∉ instrNames i.1 := fun hm => hD r hm hr
    have h1 := evalInstrPMemF_larr r emptyP i S _ (noArrWriteAt_of_not_mem hna) he
    have h2 : evalInstrPMemF emptyP i { prog := { base := b, lfn := "" }, zf := zf }
        = some { prog := { base := t'', lfn := "" }, zf := z'' } := by
      rw [evalInstrPMemF_isLopn _ i _ hl]
      show (fstepF i b zf).map _ = _
      rw [h'']; rfl
    have h3 := evalInstrPMemF_larr r emptyP i _ _ (noArrWriteAt_of_not_mem hna) h2
    simp only at h1 h3
    rw [h3, h1, congrFun hA.1 r]
  · exact harr r hr

theorem wideArgs?_mulx_shape {i : LinstrRM} {lo hi : String} {bo : LOperand}
    (h : wideArgs? i = some (.mulx lo hi bo)) : ∃ opn, i.1 = .Lopn [.reg lo, .reg hi] opn [bo] := by
  obtain ⟨w, tg⟩ := i
  unfold wideArgs? at h
  dsimp only at h
  split at h
  · split_ifs at h; cases h
  · split_ifs at h
    cases h
    exact ⟨_, rfl⟩
  · cases h

/-- A widening multiply steps as `wideStep`. -/
theorem fstepF_mulx {i : LinstrRM} {lo hi : String} {bo : LOperand}
    (h : wideArgs? i = some (.mulx lo hi bo)) (x : LstateM) (zf : Bool) :
    fstepF i x zf = (wideStep (.mulx lo hi bo) x).map (fun b => (b, zf)) := by
  obtain ⟨opn, he⟩ := wideArgs?_mulx_shape h
  have h1 : cmpArgs? i = none := by unfold cmpArgs?; rw [he]
  have h2 : movRegArgs? i = none := by unfold movRegArgs?; rw [he]
  have h3 : carryArgs? i = none := by unfold carryArgs?; rw [he]
  unfold fstepF stepMemF
  rw [h1, h2, JasminLsemExportRewrites.lsemStepMem_of_wideArgs h x, h3, h]

/-- **The widening multiply from states that agree off names it does not use.** -/
theorem fstepF_bar_mulx {i : LinstrRM} {lo hi : String} {bo : LOperand}
    (hw : wideArgs? i = some (.mulx lo hi bo)) (hD : ∀ n ∈ instrNames i.1, ¬ D n)
    (hrdx : ¬ D "RDX") {a b t : LstateM} {zf zt : Bool} (hA : AgreeOff D a b)
    (h : fstepF i a zf = some (t, zt)) :
    ∃ t', fstepF i b zf = some (t', zt) ∧ AgreeOff D t t' := by
  obtain ⟨opn, he⟩ := wideArgs?_mulx_shape hw
  have hn : ∀ n, n ∈ instrNames i.1 → ¬ D n := hD
  rw [he] at hn
  have hbo : ∀ w, evalOperandN b.reg w bo = evalOperandN a.reg w bo := by
    intro w
    cases bo with
    | reg r =>
        simp only [JasminLsemWidthN.evalOperandN, LstateN.getW]
        rw [hA.2.2.2.2 r (hn r (by simp [instrNames, JasminLsemExportRewrites.opNames]))]
    | arrIdx bb ii k =>
        rfl
    | _ => rfl
  have hrd : ∀ w, evalOperandN b.reg w (.reg mulxSrc) = evalOperandN a.reg w (.reg mulxSrc) := by
    intro w
    have : b.reg.lvm mulxSrc = a.reg.lvm mulxSrc := hA.2.2.2.2 _ hrdx
    simp only [JasminLsemWidthN.evalOperandN, LstateN.getW]
    rw [this]
  rw [fstepF_mulx hw] at h ⊢
  simp only [wideStep, hbo, hrd] at h ⊢
  split at h
  · rename_i x y hx hy
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨_, rfl, ?_⟩
    refine ⟨by simp [LstateM.setReg, LstateM.nextPc, hA.1], by simp [LstateM.setReg,
      LstateM.nextPc, hA.2.1], hA.2.2.1, hA.2.2.2.1, fun y hy => ?_⟩
    simp only [LstateM.setReg, LstateM.nextPc, LstateN.lvm_nextPc, LstateN.lvm_setReg]
    split_ifs <;> first | rfl | exact hA.2.2.2.2 y hy
  · simp at h

/-- **An `Lopn` from states that agree off names it does not use**, `RDX` and the empty name
    outside `D`. -/
theorem fstepF_bar {i : LinstrRM} (hl : IsLopn i) (hD : ∀ n ∈ instrNames i.1, ¬ D n)
    (hemp : ¬ D "") (hrdx : ¬ D "RDX") {a b t : LstateM} {zf zt : Bool} (hA : AgreeOff D a b)
    (h : fstepF i a zf = some (t, zt)) :
    ∃ t', fstepF i b zf = some (t', zt) ∧ AgreeOff D t t' := by
  cases hw : wideArgs? i with
  | some w =>
      cases w with
      | mulx lo hi bo => exact fstepF_bar_mulx hw hD hrdx hA h
      | mov _ _ => exact fstepF_bar_of_mulxFree hl (by simp [mulxFree, hw]) hD hemp hA h
  | none => exact fstepF_bar_of_mulxFree hl (by simp [mulxFree, hw]) hD hemp hA h

end Bar

/-! ## 5. The pieces of a body -/

section Pieces

variable {recog : String → Bool}

/-- The instructions of a piece. -/
def pieceSrc : Piece → Lcmd
  | .run is => is.map FI.toL
  | .bar li => [li]

theorem fragOf?_toL {li : Linstr} {i : FI} (h : fragOf? li recog = some i) : i.toL = li := by
  obtain ⟨ii, w⟩ := li
  unfold fragOf? at h
  dsimp only at h
  split at h
  · next d opn srcs heq =>
    split_ifs at h
    cases h
    simp only [FI.toL, FI.toR]
  · cases h

theorem fragOf?_props {li : Linstr} {i : FI} (h : fragOf? li recog = some i) :
    recog i.opn = true ∧ i.wf = true := by
  obtain ⟨ii, w⟩ := li
  unfold fragOf? at h
  dsimp only at h
  split at h
  · split_ifs at h with hc
    cases h
    simpa using hc
  · cases h

/-- A piece list whose runs are non-empty and never adjacent. -/
def PiecesOK : List Piece → Prop
  | [] => True
  | .run is :: rest => is ≠ [] ∧ (∀ is', rest.head? ≠ some (.run is')) ∧ PiecesOK rest
  | .bar _ :: rest => PiecesOK rest

theorem pieces_cons (li : Linstr) (body : Lcmd) :
    pieces (li :: body) recog =
      match fragOf? li recog with
      | some i =>
          match pieces body recog with
          | Piece.run is :: rest => Piece.run (i :: is) :: rest
          | _ => Piece.run [i] :: pieces body recog
      | none => Piece.bar li :: pieces body recog := rfl

/-- The pieces of a body list its instructions, with non-empty, non-adjacent runs of fragment
    instructions and every other instruction a bar. -/
theorem pieces_spec : ∀ (body : Lcmd),
    (pieces body recog).flatMap pieceSrc = body ∧ PiecesOK (pieces body recog)
      ∧ (∀ is, Piece.run is ∈ pieces body recog → ∀ i ∈ is, ∃ li ∈ body, fragOf? li recog = some i)
      ∧ (∀ li, Piece.bar li ∈ pieces body recog → li ∈ body ∧ fragOf? li recog = none) := by
  intro body
  induction body with
  | nil => exact ⟨rfl, trivial, by simp [pieces], by simp [pieces]⟩
  | cons li body ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      rw [pieces_cons]
      cases hf : fragOf? li recog with
      | none =>
          refine ⟨?_, h2, ?_, ?_⟩
          · simp [pieceSrc, h1]
          · intro is hm i hi
            simp only [List.mem_cons, reduceCtorEq, false_or] at hm
            obtain ⟨l, hl, hl'⟩ := h3 is hm i hi
            exact ⟨l, List.mem_cons_of_mem _ hl, hl'⟩
          · intro l hm
            simp only [List.mem_cons, Piece.bar.injEq] at hm
            rcases hm with rfl | hm
            · exact ⟨List.mem_cons_self, hf⟩
            · exact ⟨List.mem_cons_of_mem _ (h4 l hm).1, (h4 l hm).2⟩
      | some i =>
          have hli := fragOf?_toL hf
          simp only
          split
          · rename_i is rest heq
            rw [heq] at h1 h2 h3 h4
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [List.flatMap_cons, pieceSrc, List.map_cons] at h1 ⊢
              rw [hli, List.cons_append, h1]
            · exact ⟨by simp, h2.2.1, h2.2.2⟩
            · intro is' hm j hj
              simp only [List.mem_cons, Piece.run.injEq] at hm
              rcases hm with rfl | hm
              · simp only [List.mem_cons] at hj
                rcases hj with rfl | hj
                · exact ⟨li, List.mem_cons_self, hf⟩
                · obtain ⟨l, hl, hl'⟩ := h3 is (by simp) j hj
                  exact ⟨l, List.mem_cons_of_mem _ hl, hl'⟩
              · obtain ⟨l, hl, hl'⟩ := h3 is' (by simp [hm]) j hj
                exact ⟨l, List.mem_cons_of_mem _ hl, hl'⟩
            · intro l hm
              simp only [List.mem_cons, reduceCtorEq, false_or] at hm
              exact ⟨List.mem_cons_of_mem _ (h4 l (by simp [hm])).1, (h4 l (by simp [hm])).2⟩
          · rename_i hne
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [List.flatMap_cons, pieceSrc, List.map_cons, List.map_nil,
                List.singleton_append]
              rw [hli, h1]
            · refine ⟨by simp, fun is' he => ?_, h2⟩
              cases hp : pieces body recog with
              | nil => rw [hp] at he; cases he
              | cons q qs =>
                  rw [hp] at he
                  simp only [List.head?_cons, Option.some.injEq] at he
                  subst he
                  exact hne is' qs hp
            · intro is' hm j hj
              simp only [List.mem_cons, Piece.run.injEq] at hm
              rcases hm with rfl | hm
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                subst hj
                exact ⟨li, List.mem_cons_self, hf⟩
              · obtain ⟨l, hl, hl'⟩ := h3 is' hm j hj
                exact ⟨l, List.mem_cons_of_mem _ hl, hl'⟩
            · intro l hm
              simp only [List.mem_cons, reduceCtorEq, false_or] at hm
              exact ⟨List.mem_cons_of_mem _ (h4 l hm).1, (h4 l hm).2⟩

end Pieces

/-! ## 6. The output of the pass on a run -/

section Out

variable {abi : IsaAbi}

/-- The output of the check is at most as long as its input, and each output instruction is
    accumulated or has the mnemonic of an input instruction and is in the fragment when it
    is. -/
theorem goAcc_out (lend : List String) :
    ∀ (ann : List (FI × List String)) (m : Cur) (cs : List String) (acc out : List FI),
      goAcc lend m ann cs acc abi = some out →
      out.length ≤ acc.length + ann.length
        ∧ ∀ j ∈ out, j ∈ acc ∨ ∃ p ∈ ann, j.opn = p.1.opn ∧ (p.1.wf = true → j.wf = true) := by
  intro ann
  induction ann with
  | nil =>
      intro m cs acc out h
      cases cs with
      | cons _ _ => simp [goAcc] at h
      | nil =>
          simp only [goAcc] at h
          split at h
          · cases h
            exact ⟨by simp, fun j hj => Or.inl (by simpa using hj)⟩
          · cases h
  | cons p ann ih =>
      intro m cs acc out h
      obtain ⟨i, la⟩ := p
      cases cs with
      | nil => simp [goAcc] at h
      | cons c cs =>
          have keep : ∀ (m' : Cur), goAcc lend m' ann cs acc abi = some out →
              out.length ≤ acc.length + (ann.length + 1)
                ∧ ∀ j ∈ out, j ∈ acc ∨ ∃ p ∈ (i, la) :: ann, j.opn = p.1.opn
                    ∧ (p.1.wf = true → j.wf = true) := by
            intro m' h'
            obtain ⟨h1, h2⟩ := ih m' cs acc out h'
            refine ⟨by omega, fun j hj => ?_⟩
            rcases h2 j hj with h | ⟨q, hq, hq'⟩
            · exact Or.inl h
            · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hq'⟩
          have push : ∀ (m' : Cur) (c' : String),
              goAcc lend m' ann cs (⟨i.ii, c', i.opn, i.srcs.map (fun o => renOp m o abi)⟩ :: acc)
                abi = some out →
              out.length ≤ acc.length + (ann.length + 1)
                ∧ ∀ j ∈ out, j ∈ acc ∨ ∃ p ∈ (i, la) :: ann, j.opn = p.1.opn
                    ∧ (p.1.wf = true → j.wf = true) := by
            intro m' c' h'
            obtain ⟨h1, h2⟩ := ih m' cs _ out h'
            refine ⟨by simp at h1; omega, fun j hj => ?_⟩
            rcases h2 j hj with h | ⟨q, hq, hq'⟩
            · simp only [List.mem_cons] at h
              rcases h with rfl | h
              · exact Or.inr ⟨(i, la), List.mem_cons_self, rfl, fun hw => wf_rename m i c' hw⟩
              · exact Or.inl h
            · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hq'⟩
          simp only [goAcc] at h
          simp only [List.length_cons]
          split_ifs at h
          all_goals first
            | exact absurd h (by simp)
            | exact keep _ h
            | exact push _ _ h

theorem annotate_length (lend : List String) :
    ∀ is : List FI, (annotate lend is abi).1.length = is.length := by
  intro is
  induction is with
  | nil => rfl
  | cons i is ih => rw [annotate_cons]; simp [ih]

theorem annotate_fst (lend : List String) :
    ∀ is : List FI, ∀ p ∈ (annotate lend is abi).1, p.1 ∈ is := by
  intro is
  induction is with
  | nil => simp [annotate]
  | cons i is ih =>
      intro p hp
      rw [annotate_cons] at hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp
      · exact List.mem_cons_of_mem _ (ih p hp)

/-- The output of the pass on a run is at most as long as the run, and each of its
    instructions has the mnemonic of an instruction of the run and is in the fragment when the
    run is. -/
theorem reallocRun_out (lend : List String) (is : List FI) (hwf : ∀ i ∈ is, i.wf = true) :
    (reallocRun lend is abi).length ≤ is.length
      ∧ ∀ j ∈ reallocRun lend is abi, (∃ i ∈ is, j.opn = i.opn) ∧ j.wf = true := by
  unfold reallocRun reallocWith
  split
  · rename_i out hf
    obtain ⟨cs, _, hcs⟩ := List.exists_of_findSome?_eq_some hf
    obtain ⟨h1, h2⟩ := goAcc_out lend _ {} cs [] out hcs
    have hlen := annotate_length (abi := abi) lend is
    have hfst := annotate_fst (abi := abi) lend is
    refine ⟨by simpa [hlen] using h1, fun j hj => ?_⟩
    rcases h2 j hj with h | ⟨p, hp, hop, hw⟩
    · simp at h
    · exact ⟨⟨p.1, hfst p hp, hop⟩, hw (hwf _ (hfst p hp))⟩
  · exact ⟨le_refl _, fun j hj => ⟨⟨j, hj, rfl⟩, hwf j hj⟩⟩

end Out

/-! ## 7. The relation of the pass on a body -/

section Main

variable {abi : IsaAbi}

/-- One step of the fold of `reallocBody` over the pieces. -/
def rstep (res : List String) (abi : IsaAbi) (p : Piece) (acc : Lcmd × Std.HashSet String) :
    Lcmd × Std.HashSet String :=
  let out : Lcmd :=
    match p with
    | .run is =>
        let regs := match acc.1 with
          | ⟨_, .Lret⟩ :: _ => retLive res abi
          | _ => gpRegs abi
        (reallocRun (regs ++ acc.2.toList) is abi).map FI.toL ++ acc.1
    | .bar li => li :: acc.1
  (out, acc.2.insertMany p.frames)

theorem reallocBody_eq (res : List String) (body : Lcmd) (recog : String → Bool) :
    reallocBody res body abi recog
      = ((pieces body recog).foldr (rstep res abi) ([], labelLiveFrames body)).1 := rfl

/-- The frame cells a typed suffix names. -/
def sufFrames (X : List LinstrRM) : List String := X.flatMap (fun i => instrFrames i.1)

/-- The return instruction. -/
def isRetRM (i : LinstrRM) : Bool :=
  match i.1 with
  | .Lret => true
  | _ => false

/-- The names at which the states of the two bodies may differ after a source suffix: at
    the end of the body, every location that is neither a register of `E` nor a frame cell of
    `Lbl`; before a return, every location; elsewhere, every frame cell that is not in `Lbl`
    and not named in the suffix. -/
def DX (abi : IsaAbi) (Lbl : Std.HashSet String) (E : List String) :
    List LinstrRM → String → Prop
  | [] => fun y => isLoc y abi = true ∧ ¬ (isGP y abi = true ∧ y ∈ E)
      ∧ ¬ (isFrame y = true ∧ y ∈ Lbl)
  | i :: R => fun y => if isRetRM i = true then isLoc y abi = true
      else isFrame y = true ∧ y ∉ Lbl ∧ y ∉ sufFrames (i :: R)

/-- The relation of the pass on a body: the states agree off `DX`. -/
def QR (abi : IsaAbi) (Lbl : Std.HashSet String) (E : List String) (X : List LinstrRM)
    (a b : LstateM) : Prop :=
  AgreeOff (DX abi Lbl E X) a b

theorem AgreeOff.mono {D D' : String → Prop} (h : ∀ y, D y → D' y) {a b : LstateM}
    (hA : AgreeOff D a b) : AgreeOff D' a b :=
  ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, fun y hy => hA.2.2.2.2 y (fun hd => hy (h y hd))⟩

theorem isLoc_of_isFrame {y : String} (h : isFrame y = true) : isLoc y abi = true := by
  simp only [isLoc, Bool.or_eq_true]
  exact Or.inr h

/-- Past an instruction that is not a return, the set of differing names grows. -/
theorem DX_mono (hgf : ∀ y, isGP y abi = true → isFrame y = false) {Lbl : Std.HashSet String}
    {E : List String} {i : LinstrRM} {R : List LinstrRM} (hi : isRetRM i = false) :
    ∀ y, DX abi Lbl E (i :: R) y → DX abi Lbl E R y := by
  intro y hy
  simp only [DX, hi, Bool.false_eq_true, if_false] at hy
  obtain ⟨hf, hl, hs⟩ := hy
  cases R with
  | nil =>
      refine ⟨isLoc_of_isFrame hf, fun h => ?_, fun h => hl h.2⟩
      rw [hgf y h.1] at hf; cases hf
  | cons j R =>
      simp only [DX]
      split
      · exact isLoc_of_isFrame hf
      · refine ⟨hf, hl, fun h => hs ?_⟩
        simp only [sufFrames, List.flatMap_cons, List.mem_append] at h ⊢
        exact Or.inr (by simpa [List.flatMap_cons] using h)

theorem QR_pc {Lbl : Std.HashSet String} {E : List String} : QPc (QR abi Lbl E) := by
  intro X a b p q h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun y hy => h.2.2.2.2 y hy⟩

/-- A frame cell an operand names. -/
theorem mem_opFrames_of_opNames {o : LOperand} {y : String}
    (h : y ∈ JasminLsemExportRewrites.opNames o) (hy : isFrame y = true) : y ∈ opFrames o := by
  cases o with
  | reg n =>
      simp only [JasminLsemExportRewrites.opNames, List.mem_singleton] at h
      subst h
      simp [opFrames, hy]
  | arrIdx b x k =>
      simp only [JasminLsemExportRewrites.opNames, List.mem_cons, List.not_mem_nil,
        or_false] at h
      simp only [opFrames, List.mem_filter]
      rcases h with rfl | rfl <;> simp [hy]
  | _ => simp [JasminLsemExportRewrites.opNames] at h

/-- A frame cell an instruction names is among its frame cells. -/
theorem mem_instrFrames_of_instrNames {w : LinstrR} {y : String} (h : y ∈ instrNames w)
    (hy : isFrame y = true) : y ∈ instrFrames w := by
  cases w with
  | Lopn d o srcs =>
      simp only [instrNames, List.mem_flatMap, List.mem_append] at h
      obtain ⟨op, hop, hy'⟩ := h
      simp only [instrFrames, List.mem_append, List.mem_flatMap]
      rcases hop with hop | hop
      · exact Or.inl ⟨op, hop, mem_opFrames_of_opNames hy' hy⟩
      · exact Or.inr ⟨op, hop, mem_opFrames_of_opNames hy' hy⟩
  | _ => simp [instrNames] at h

/-- A frame cell a fragment instruction names or reads is among its frame cells, when no
    general-purpose register is a frame cell. -/
theorem mem_instrFrames_of_fi (hgf : ∀ y, isGP y abi = true → isFrame y = false) {i : FI}
    {y : String} (h : y ∈ fiNames i ∨ y ∈ i.reads abi) (hy : isFrame y = true) :
    y ∈ instrFrames i.toR := by
  have hgp : ∀ n, y ∈ nameReadsAt n abi → isGP y abi = true := by
    intro n hb
    unfold nameReadsAt at hb
    split_ifs at hb with h1 h2
    · simp only [List.mem_singleton] at hb; subst hb; exact h1
    · split at hb
      · split_ifs at hb with h4
        · simp only [List.mem_singleton] at hb; subst hb; exact h4
        · simp at hb
      · simp at hb
    · simp at hb
  have hbase : ∀ n, y ∈ baseRegs n abi → False := by
    intro n hb
    unfold baseRegs at hb
    split_ifs at hb
    · rw [hgf _ (hgp n hb)] at hy; cases hy
    · simp at hb
  simp only [instrFrames, FI.toR, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append, List.mem_flatMap]
  rcases h with h | h
  · simp only [fiNames, List.mem_cons, List.mem_flatMap] at h
    rcases h with rfl | ⟨o, ho, hyo⟩
    · exact Or.inl (by simp [opFrames, hy])
    · cases o with
      | reg x =>
          simp only [List.mem_singleton] at hyo
          subst hyo
          exact Or.inr ⟨.reg y, ho, by simp [opFrames, hy]⟩
      | _ => simp at hyo
  · simp only [FI.reads, List.mem_append, List.mem_flatMap] at h
    rcases h with ⟨o, ho, hyo⟩ | h
    · cases o with
      | reg x =>
          simp only [opReads] at hyo
          split_ifs at hyo
          · simp only [List.mem_singleton] at hyo
            subst hyo
            exact Or.inr ⟨.reg y, ho, by simp [opFrames, hy]⟩
          · exact (hbase x hyo).elim
      | _ => simp [opReads] at hyo
    · exact (hbase _ h).elim

/-- The registers live out of the last run before the tail `T`: the registers live at a
    return when `T` starts with a return, all general-purpose registers otherwise. -/
def regsOf (res : List String) (abi : IsaAbi) (T : Lcmd) : List String :=
  match T with
  | ⟨_, .Lret⟩ :: _ => retLive res abi
  | _ => gpRegs abi

theorem sufFrames_typeBody (tag : LinstrR → MemTag) (X : Lcmd) :
    sufFrames (typeBody tag X) = X.flatMap (fun li => instrFrames li.li_i) := by
  simp [sufFrames, typeBody, List.flatMap_map]

theorem piece_frames (p : Piece) :
    p.frames = (pieceSrc p).flatMap (fun li => instrFrames li.li_i) := by
  cases p with
  | run is => simp [Piece.frames, pieceSrc, List.flatMap_map, FI.toL]
  | bar li => simp [Piece.frames, pieceSrc]

theorem typeBody_append (tag : LinstrR → MemTag) (A B : Lcmd) :
    typeBody tag (A ++ B) = typeBody tag A ++ typeBody tag B := by
  simp [typeBody]

/-- The typed form of a list of fragment instructions with the register tag. -/
theorem typeBody_map_toL {tag : LinstrR → MemTag} {recog : String → Bool}
    (htag : ∀ d opn srcs, recog opn = true → opn ≠ "LOADIDX" → opn ≠ "STOREIDX" →
      tag (.Lopn [.reg d] opn srcs) = .reg none)
    (is : List FI) (h : ∀ i ∈ is, recog i.opn = true ∧ i.wf = true) :
    typeBody tag (is.map FI.toL) = is.map tyF := by
  simp only [typeBody, List.map_map]
  refine List.map_congr_left (fun i hi => ?_)
  obtain ⟨hr, hw⟩ := h i hi
  simp only [FI.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
  simp only [Function.comp, FI.toL, tyF, FI.toR, htag i.d i.opn i.srcs hr hw.1.2 hw.2]

/-- `String.isPrefixOf` is the list prefix test on the characters. -/
theorem isPrefixOf_list (p s : String) : p.isPrefixOf s = p.toList.isPrefixOf s.toList := by
  rw [String.isPrefixOf, Bool.eq_iff_iff, String.startsWith_string_iff,
    List.isPrefixOf_iff_prefix]

theorem not_isFrame_emp : isFrame "" = false := by rw [isFrame, isPrefixOf_list]; decide
theorem not_isFrame_rdx : isFrame "RDX" = false := by rw [isFrame, isPrefixOf_list]; decide

section Core

variable (res : List String) (abi : IsaAbi) (recog : String → Bool) (tag : LinstrR → MemTag)
  (T : Lcmd) (Lbl : Std.HashSet String)

/-- The hypotheses of the core induction. -/
structure CoreHyp : Prop where
  gf : ∀ y, isGP y abi = true → isFrame y = false
  emp : isLoc "" abi = false
  ret : ∀ y ∈ retLive res abi, isFrame y = false
  tag : ∀ d opn srcs, recog opn = true → opn ≠ "LOADIDX" → opn ≠ "STOREIDX" →
    tag (.Lopn [.reg d] opn srcs) = .reg none
  tail : T = [] ∨ ∃ ii, T = [⟨ii, .Lret⟩]

/-- The pieces of the induction: runs of fragment instructions that read the destination of
    a flag compare, and kept instructions. -/
def PieceHyp (ps : List Piece) : Prop :=
  (∀ is, Piece.run is ∈ ps → ∀ i ∈ is, recog i.opn = true ∧ i.wf = true ∧ CmpReadsDst i)
    ∧ (∀ li, Piece.bar li ∈ ps → keepOKB (li.li_i, tag li.li_i) = true)
    ∧ PiecesOK ps

theorem DX_cons_nonret {Lbl : Std.HashSet String} {E : List String} {i : LinstrRM}
    {R : List LinstrRM} (hi : isRetRM i = false) (y : String) :
    DX abi Lbl E (i :: R) y ↔ isFrame y = true ∧ y ∉ Lbl ∧ y ∉ sufFrames (i :: R) := by
  simp [DX, hi]

theorem regs_cons (li : Linstr) (rest : Lcmd) (A B : List String) :
    (match (li :: rest : Lcmd) with
      | ⟨_, .Lret⟩ :: _ => A
      | _ => B) = if li.li_i = .Lret then A else B := by
  obtain ⟨ii, w⟩ := li
  cases w <;> rfl

theorem isRetRM_eq (w : LinstrR) (t : MemTag) : isRetRM (w, t) = true ↔ w = .Lret := by
  cases w <;> simp [isRetRM]

theorem isRetRM_tyF (i : FI) : isRetRM (tyF i) = false := rfl

/-- **The core induction over the pieces.** For pieces of a body followed by the tail `T`,
    the fold of `reallocBody` from `(T, Lbl)` collects the frame cells `Lbl` and those the
    pieces name, and its output is `Y ++ T` with `Y` related to the instructions of the
    pieces by `QRel` at the relation `QR`. -/
theorem core (H : CoreHyp res abi recog tag T) :
    ∀ ps : List Piece, PieceHyp recog tag ps →
      (∀ x, x ∈ (ps.foldr (rstep res abi) (T, Lbl)).2 ↔
        x ∈ Lbl ∨ x ∈ (ps.flatMap pieceSrc).flatMap (fun li => instrFrames li.li_i))
      ∧ ∃ Y, (ps.foldr (rstep res abi) (T, Lbl)).1 = Y ++ T ∧ (ps = [] → Y = [])
        ∧ (∀ li ps', ps = .bar li :: ps' → Y.head? = some li)
        ∧ QRel (QR abi Lbl (regsOf res abi T)) (typeBody tag (ps.flatMap pieceSrc))
            (typeBody tag Y) := by
  intro ps
  induction ps with
  | nil =>
      intro _
      refine ⟨fun x => ?_, [], ?_, fun _ => rfl, fun _ _ h => ?_, ?_⟩
      · simp
      · simp
      · cases h
      · exact QRel.nil
  | cons p ps ih =>
      intro hP
      have hP' : PieceHyp recog tag ps := by
        refine ⟨fun is h => hP.1 is (List.mem_cons_of_mem _ h),
          fun li h => hP.2.1 li (List.mem_cons_of_mem _ h), ?_⟩
        have h3 := hP.2.2
        cases p with
        | run is => exact h3.2.2
        | bar li => exact h3
      obtain ⟨hmem, Y', hY', hnil, hbar, hQ⟩ := ih hP'
      refine ⟨fun x => ?_, ?_⟩
      · simp only [List.foldr_cons, rstep, Std.HashSet.mem_insertMany_list, hmem x,
          piece_frames, List.flatMap_cons, List.flatMap_append, List.mem_append,
          List.contains_eq_mem, decide_eq_true_eq]
        tauto
      · cases p with
        | bar li =>
          refine ⟨li :: Y', by simp [rstep, hY'], fun h => (by cases h), fun l ps' h => ?_, ?_⟩
          · simp only [List.cons.injEq, Piece.bar.injEq] at h
            obtain ⟨rfl, -⟩ := h
            rfl
          · have hk := hP.2.1 li List.mem_cons_self
            set x : LinstrRM := (li.li_i, tag li.li_i) with hx
            have hsrc : typeBody tag ((Piece.bar li :: ps).flatMap pieceSrc)
                = x :: typeBody tag (ps.flatMap pieceSrc) := by
              simp [pieceSrc, typeBody, hx]
            have htgt : typeBody tag (li :: Y') = x :: typeBody tag Y' := by
              simp [typeBody, hx]
            rw [hsrc, htgt]
            set R := typeBody tag (ps.flatMap pieceSrc)
            by_cases hl : ∃ d o srcs, li.li_i = LinstrR.Lopn d o srcs
            · obtain ⟨d, o, srcs, hdo⟩ := hl
              have hlx : IsLopn x := ⟨d, o, srcs, hdo⟩
              have hnr : isRetRM x = false := by simp [isRetRM, hx, hdo]
              have hsim : QSim (QR abi Lbl (regsOf res abi T)) [x] [x] R := by
                intro a b t zf zt hq hrun
                obtain ⟨s1, z1, hst, hrest⟩ := runStraightF_cons_some hrun
                simp only [runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at hrest
                obtain ⟨rfl, rfl⟩ := hrest
                have hD : ∀ n ∈ instrNames x.1, ¬ DX abi Lbl (regsOf res abi T) (x :: R) n := by
                  intro n hn hdn
                  rw [DX_cons_nonret abi hnr] at hdn
                  refine hdn.2.2 ?_
                  simp only [sufFrames, List.flatMap_cons, List.mem_append]
                  exact Or.inl (mem_instrFrames_of_instrNames hn hdn.1)
                have hemp : ¬ DX abi Lbl (regsOf res abi T) (x :: R) "" := by
                  rw [DX_cons_nonret abi hnr]; simp [not_isFrame_emp]
                have hrdx : ¬ DX abi Lbl (regsOf res abi T) (x :: R) "RDX" := by
                  rw [DX_cons_nonret abi hnr]; simp [not_isFrame_rdx]
                obtain ⟨t', ht', hA⟩ := fstepF_bar hlx hD hemp hrdx hq hst
                refine ⟨t', ?_, AgreeOff.mono (DX_mono H.gf hnr) hA⟩
                rw [runStraightF_cons, ht', Option.bind_some, runStraightF_nil]
              exact QRel.blk (seg := [x]) (seg' := [x]) (by simp) (le_refl _)
                (fun i hi => by simp at hi; subst hi; exact hlx)
                (fun i hi => by simp at hi; subst hi; exact hlx) hsim hQ
            · have hkeep : CtlKeep x := ctlKeep_of_keepOKB hk
                (fun d o srcs he => hl ⟨d, o, srcs, he⟩)
              have hnr : ∀ w, x.1 = w → (w matches .Llabel _ _ ∨ w matches .Lcond _ _) →
                  isRetRM x = false := by
                intro w hw hm
                rcases hm with hm | hm <;> (cases w <;> simp_all [isRetRM])
              refine QRel.ctl hkeep ⟨fun kd l he a b hab => ?_, fun c l he a b hab => ?_⟩ hQ
              · exact AgreeOff.mono (DX_mono H.gf (hnr _ he (by simp))) hab
              · have hn := hnr _ he (by simp)
                refine ⟨AgreeOff.mono (DX_mono H.gf hn) hab, ?_⟩
                unfold condNZ
                cases c with
                | reg r =>
                    have hr : ¬ DX abi Lbl (regsOf res abi T) (x :: R) r := by
                      rw [DX_cons_nonret abi hn]
                      intro hd
                      refine hd.2.2 ?_
                      simp only [sufFrames, List.flatMap_cons, List.mem_append]
                      exact Or.inl (by rw [he]; simp [instrFrames, opFrames, hd.1])
                    simp only [JasminLsemWidthN.evalOperandN, LstateN.getW]
                    rw [hab.2.2.2.2 r hr]
                | _ => rfl
        | run is =>
          obtain ⟨hne, hnadj, -⟩ := hP.2.2
          have hprops := hP.1 is List.mem_cons_self
          have hwf : ∀ i ∈ is, i.wf = true := fun i hi => (hprops i hi).2.1
          have hcmp : ∀ i ∈ is, CmpReadsDst i := fun i hi => (hprops i hi).2.2
          set r' := ps.foldr (rstep res abi) (T, Lbl) with hr'
          set regs : List String := match r'.1 with
            | ⟨_, .Lret⟩ :: _ => retLive res abi
            | _ => gpRegs abi with hregs
          set lend := regs ++ r'.2.toList with hlend
          set out := reallocRun lend is abi with hout
          obtain ⟨hlen, hout'⟩ := reallocRun_out (abi := abi) lend is hwf
          refine ⟨out.map FI.toL ++ Y', ?_, fun h => (by cases h), fun l ps' h => (by cases h), ?_⟩
          · show (out.map FI.toL ++ r'.1) = _
            rw [hY', List.append_assoc]
          have hsrc : typeBody tag ((Piece.run is :: ps).flatMap pieceSrc)
              = is.map tyF ++ typeBody tag (ps.flatMap pieceSrc) := by
            rw [List.flatMap_cons, typeBody_append, pieceSrc,
              typeBody_map_toL H.tag is (fun i hi => ⟨(hprops i hi).1, (hprops i hi).2.1⟩)]
          have htgt : typeBody tag (out.map FI.toL ++ Y') = out.map tyF ++ typeBody tag Y' := by
            rw [typeBody_append, typeBody_map_toL H.tag out (fun j hj => by
              obtain ⟨⟨i, hi, hop⟩, hw⟩ := hout' j hj
              exact ⟨hop ▸ (hprops i hi).1, hw⟩)]
          rw [hsrc, htgt]
          set R := typeBody tag (ps.flatMap pieceSrc) with hR
          obtain ⟨i0, is', rfl⟩ : ∃ i0 is', is = i0 :: is' := by
            cases is with
            | nil => exact absurd rfl hne
            | cons i0 is' => exact ⟨i0, is', rfl⟩
          have hnr : isRetRM (tyF i0) = false := rfl
          have hsim : QSim (QR abi Lbl (regsOf res abi T)) ((i0 :: is').map tyF) (out.map tyF) R := by
            intro a b t zf zt hq hrun
            have hDf : ∀ y, DX abi Lbl (regsOf res abi T) ((i0 :: is').map tyF ++ R) y →
                isFrame y = true ∧ y ∉ Lbl
                  ∧ y ∉ sufFrames ((i0 :: is').map tyF ++ R) := by
              intro y hy
              simpa [List.map_cons, List.cons_append, DX_cons_nonret abi hnr] using hy
            obtain ⟨t', ht', hfin⟩ := reallocRunF H.emp (D := DX abi Lbl (regsOf res abi T)
                ((i0 :: is').map tyF ++ R)) (fun y hy => isLoc_of_isFrame (hDf y hy).1)
              lend (i0 :: is') hwf hcmp
              (fun i hi y hy hd => (hDf y hd).2.2 (by
                simp only [sufFrames, List.flatMap_append, List.mem_append, List.mem_flatMap]
                exact Or.inl ⟨tyF i, List.mem_map_of_mem hi,
                  mem_instrFrames_of_fi H.gf hy (hDf y hd).1⟩))
              (fun x hx hd => by
                have hd' := hDf x hd
                simp only [hlend, List.mem_append, Std.HashSet.mem_toList] at hx
                rcases hx with hx | hx
                · have hnf : isFrame x = false := by
                    simp only [hregs] at hx
                    split at hx
                    · exact H.ret x hx
                    · exact H.gf x (by simp [isGP, hx])
                  rw [hnf] at hd'; exact absurd hd'.1 (by simp)
                · rcases (hmem x).1 hx with h1 | h1
                  · exact hd'.2.1 h1
                  · refine hd'.2.2 ?_
                    rw [← sufFrames_typeBody tag] at h1
                    simp only [sufFrames, List.flatMap_append, List.mem_append] at h1 ⊢
                    exact Or.inr h1)
              hq hrun
            refine ⟨t', ht', hfin.1, hfin.2.1, hfin.2.2.1, hfin.2.2.2.1, fun y hy => ?_⟩
            apply hfin.2.2.2.2 y
            by_cases hl : isLoc y abi = true
            swap
            · exact Or.inl (by simpa using hl)
            right
            have hinr2 : ∀ z, z ∈ Lbl ∨ z ∈ sufFrames R → z ∈ lend := by
              intro z hz
              simp only [hlend, List.mem_append, Std.HashSet.mem_toList]
              refine Or.inr ((hmem z).2 ?_)
              rcases hz with hz | hz
              · exact Or.inl hz
              · rw [hR, sufFrames_typeBody] at hz; exact Or.inr hz
            cases hps : ps with
            | nil =>
                subst hps
                have hY0 := hnil rfl
                subst hY0
                have hreg : regs = regsOf res abi T := by
                  simp only [hregs, hY', List.nil_append]
                  rfl
                simp only [hR, List.flatMap_nil, typeBody, List.map_nil, DX] at hy
                simp only [hl, true_and, not_and] at hy
                by_cases hg : isGP y abi = true ∧ y ∈ regsOf res abi T
                · simp only [hlend, List.mem_append]
                  exact Or.inl (hreg ▸ hg.2)
                · have h2 := hy (fun h1 h2 => hg ⟨h1, h2⟩)
                  refine hinr2 y (Or.inl ?_)
                  by_contra hn
                  exact h2 (fun _ => hn)
            | cons q qs =>
                subst hps
                cases q with
                | run js => exact absurd rfl (hnadj js)
                | bar li =>
                  have hh := hbar li qs rfl
                  obtain ⟨Y'', rfl⟩ : ∃ Y'', Y' = li :: Y'' := by
                    cases Y' with
                    | nil => cases hh
                    | cons z zs =>
                        simp only [List.head?_cons, Option.some.injEq] at hh
                        exact ⟨zs, by rw [hh]⟩
                  have hreg : regs = if li.li_i = .Lret then retLive res abi else gpRegs abi := by
                    simp only [hregs, hY', List.cons_append]
                    exact regs_cons li _ _ _
                  have hRe : R = (li.li_i, tag li.li_i) :: typeBody tag (qs.flatMap pieceSrc) := by
                    simp [hR, pieceSrc, typeBody]
                  rw [hRe] at hy hinr2
                  by_cases hret : li.li_i = .Lret
                  · have : isRetRM (li.li_i, tag li.li_i) = true := (isRetRM_eq _ _).2 hret
                    simp only [DX, this, if_true] at hy
                    exact absurd hl hy
                  · have hnr' : isRetRM (li.li_i, tag li.li_i) = false := by
                      cases h : isRetRM (li.li_i, tag li.li_i)
                      · rfl
                      · exact absurd ((isRetRM_eq _ _).1 h) hret
                    rw [DX_cons_nonret abi hnr'] at hy
                    by_cases hfr : isFrame y = true
                    · refine hinr2 y ?_
                      by_contra hn
                      push Not at hn
                      exact hy ⟨hfr, hn.1, hn.2⟩
                    · have hgp : isGP y abi = true := by
                        simp only [isLoc, Bool.or_eq_true] at hl
                        rcases hl with h | h
                        · exact h
                        · exact absurd h hfr
                      simp only [hlend, List.mem_append, hreg, if_neg hret]
                      exact Or.inl (by simpa [isGP] using hgp)
          exact QRel.blk (by simp) (by simpa using hlen) (fun i hi => by
              obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi; exact ⟨_, _, _, rfl⟩)
            (fun i hi => by obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi; exact ⟨_, _, _, rfl⟩)
            hsim hQ

end Core

end Main

/-! ## 8. Whole bodies -/

section Body

theorem evalJumpMem_lfn {P : LprogM} {l : LLabel} {p q : LstatePM}
    (h : evalJumpMem P l p = some q) : q.lfn = p.lfn := by
  unfold evalJumpMem at h
  split at h
  · cases h; rfl
  · cases h

theorem evalInstrPMemL_lfn {P : LprogM} {i : LinstrRM} {p q : LstatePM}
    (h : evalInstrPMemL P i p = some q) : q.lfn = p.lfn := by
  unfold evalInstrPMemL at h
  split at h
  · cases h; rfl
  · split at h
    · exact evalJumpMem_lfn h
    · cases h; rfl
  · split at h
    · exact evalJumpMem_lfn h
    · cases h
  · obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl

/-- A step of the flag machine keeps the function name. -/
theorem evalInstrPMemF_lfn {P : LprogM} {i : LinstrRM} {s u : LstateMF}
    (h : evalInstrPMemF P i s = some u) : u.prog.lfn = s.prog.lfn := by
  unfold evalInstrPMemF at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · split at h
    · split at h
      · cases h; rfl
      · cases h
    · split at h
      · split at h
        · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
          exact evalJumpMem_lfn hp
        · cases h; rfl
      · split at h
        · rename_i p hp
          cases h
          exact (evalInstrPMemL_lfn hp : _)
        · split at h
          · obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
          · split at h
            · obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
            · cases h

/-- A halting run keeps the function name and ends where no instruction is fetched. -/
theorem lsemFuelMemF_end {P : LprogM} :
    ∀ (fuel : Nat) {s t : LstateMF}, lsemFuelMemF P fuel s = some t →
      t.prog.lfn = s.prog.lfn ∧ findInstrMem P t.prog = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t h
      unfold lsemFuelMemF at h
      split at h
      · rename_i hf; cases h; exact ⟨rfl, hf⟩
      · cases h
  | succ n ih =>
      intro s t h
      unfold lsemFuelMemF at h
      split at h
      · rename_i hf; cases h; exact ⟨rfl, hf⟩
      · split at h
        · rename_i u hu
          obtain ⟨h1, h2⟩ := ih h
          exact ⟨h1.trans (evalInstrPMemF_lfn hu), h2⟩
        · cases h

theorem mem_labelLiveFrames {body : Lcmd} (hl : ∃ li ∈ body, ∃ k l, li.li_i = .Llabel k l)
    {x : String} (hx : x ∈ body.flatMap (fun li => instrFrames li.li_i)) :
    x ∈ labelLiveFrames body := by
  obtain ⟨li, hli, k, l, he⟩ := hl
  unfold labelLiveFrames
  rw [if_pos (List.any_eq_true.2 ⟨li, hli, by simp [he]⟩), Std.HashSet.mem_insertMany_list]
  exact Or.inr (by simpa using hx)

theorem label_of_findLabelMem {tag : LinstrR → MemTag} {b : Lcmd} {l : LLabel} {pc : Nat}
    (h : findLabelMem l (typeBody tag b) = some pc) :
    ∃ li ∈ b, ∃ k l', li.li_i = .Llabel k l' := by
  obtain ⟨w, hw, hl⟩ := JasminLsemLabeled.findLabel_sound l _ pc h
  simp only [typeBody, List.map_map, List.getElem?_map] at hw
  obtain ⟨li, hli, rfl⟩ := Option.map_eq_some_iff.mp hw
  refine ⟨li, List.mem_of_getElem? hli, ?_⟩
  simp only [Function.comp] at hl
  unfold JasminLsemLabeled.isLabel at hl
  split at hl
  · rename_i k l' he; exact ⟨k, l', he⟩
  · cases hl

theorem sufFrames_drop {X : List LinstrRM} {n : Nat} {z : String}
    (h : z ∈ sufFrames (X.drop n)) : z ∈ sufFrames X := by
  simp only [sufFrames, List.mem_flatMap] at h ⊢
  obtain ⟨i, hi, hz⟩ := h
  exact ⟨i, List.mem_of_mem_drop hi, hz⟩

/-- A frame cell outside `L0` that no instruction of a suffix names may differ after it. -/
theorem DX_of_frame {abi : IsaAbi} (hgf : ∀ y, isGP y abi = true → isFrame y = false)
    {L0 : Std.HashSet String} {E : List String} {X : List LinstrRM} {y : String}
    (hf : isFrame y = true) (hy : y ∉ L0) (hsuf : ∀ z ∈ sufFrames X, z ∈ L0) :
    DX abi L0 E X y := by
  cases X with
  | nil =>
      refine ⟨isLoc_of_isFrame hf, fun h => ?_, fun h => hy h.2⟩
      rw [hgf y h.1] at hf; cases hf
  | cons j R =>
      simp only [DX]
      split
      · exact isLoc_of_isFrame hf
      · exact ⟨hf, hy, fun h => hy (hsuf y h)⟩

/-- **The pass on a body followed by the tail `T`.** -/
theorem body_sim (res : List String) (abi : IsaAbi) (recog : String → Bool)
    (tag : LinstrR → MemTag) (T : Lcmd) (H : CoreHyp res abi recog tag T) (body0 : Lcmd)
    (L0 : Std.HashSet String) (hL0 : ∀ x, x ∈ L0 ↔ x ∈ labelLiveFrames (body0 ++ T))
    (hkeep : ∀ li ∈ body0, keepOKB (li.li_i, tag li.li_i) = true)
    (hcmp : ∀ li ∈ body0, ∀ i, fragOf? li recog = some i → CmpReadsDst i) (fn : String) :
    ∃ Y, ((pieces body0 recog).foldr (rstep res abi) (T, L0)).1 = Y ++ T
      ∧ ∀ {fuel : Nat} {s t : LstateMF}, s.prog.base.lpc = 0 →
        lsemFuelMemF (singletonProgM fn (typeBody tag body0)) fuel s = some t →
        ∃ fuel' t', fuel' ≤ fuel
          ∧ lsemFuelMemF (singletonProgM fn (typeBody tag Y)) fuel' s = some t'
          ∧ t'.prog.lfn = t.prog.lfn ∧ t'.zf = t.zf
          ∧ AgreeOff (DX abi L0 (regsOf res abi T) []) t.prog.base t'.prog.base := by
  obtain ⟨hflat, hok, hruns, hbars⟩ := pieces_spec (recog := recog) body0
  have hP : PieceHyp recog tag (pieces body0 recog) := by
    refine ⟨fun is h i hi => ?_, fun li h => hkeep li (hbars li h).1, hok⟩
    obtain ⟨li, hli, hfi⟩ := hruns is h i hi
    exact ⟨(fragOf?_props hfi).1, (fragOf?_props hfi).2, hcmp li hli i hfi⟩
  obtain ⟨-, Y, hY, -, -, hQ⟩ := core res abi recog tag T L0 H (pieces body0 recog) hP
  rw [hflat] at hQ
  refine ⟨Y, hY, fun {fuel s t} h0 h => ?_⟩
  set B := typeBody tag body0
  set Q := QR abi L0 (regsOf res abi T)
  have hJ : QJump Q (singletonProgM fn B).body := by
    intro k i R hd hk l pc hpc a b hab
    have hnr : isRetRM i = false := by
      rcases hk with ⟨c, l', he⟩ | ⟨tg, he⟩ <;> simp [isRetRM, he]
    obtain ⟨li, hli, kk, ll, he⟩ := label_of_findLabelMem hpc
    have hsuf : ∀ z ∈ sufFrames (B.drop (pc + 1)), z ∈ L0 := by
      intro z hz
      have hz' := sufFrames_drop hz
      rw [sufFrames_typeBody] at hz'
      refine (hL0 z).2 (mem_labelLiveFrames ⟨li, by simp [hli], kk, ll, he⟩ ?_)
      simp only [List.flatMap_append, List.mem_append]
      exact Or.inl hz'
    refine AgreeOff.mono (fun y hy => ?_) hab
    rw [DX_cons_nonret abi hnr] at hy
    exact DX_of_frame H.gf hy.1 hy.2.1 hsuf
  by_cases hfn : s.prog.lfn = fn
  · have hS : QS Q (singletonProgM fn B) (singletonProgM fn (typeBody tag Y)) s s :=
      ⟨rfl, rfl, by
        show Q (B.drop s.prog.base.lpc) s.prog.base s.prog.base
        exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩, by
        show QRel Q (B.drop s.prog.base.lpc) ((typeBody tag Y).drop s.prog.base.lpc)
        rw [h0]; exact hQ⟩
    obtain ⟨f', t', hle, hrun, hSt⟩ :=
      lsemFuelMemF_QRel (P := singletonProgM fn B) (P' := singletonProgM fn (typeBody tag Y))
        rfl QR_pc hJ hQ fuel hS h
    obtain ⟨hlfn, hend⟩ := lsemFuelMemF_end fuel h
    have hdrop : B.drop t.prog.base.lpc = [] := by
      unfold findInstrMem at hend
      split at hend
      · exact List.drop_eq_nil_iff.mpr (List.getElem?_eq_none_iff.mp hend)
      · rename_i hne; exact absurd (hlfn.trans hfn) hne
    have hb : Q (B.drop t.prog.base.lpc) t.prog.base t'.prog.base := hSt.base
    rw [hdrop] at hb
    exact ⟨f', t', hle, hrun, hSt.lfn, hSt.zf, hb⟩
  · have hnone : ∀ (P : LprogM), P.lfn = fn → findInstrMem P s.prog = none := by
      intro P hP
      unfold findInstrMem
      rw [if_neg (by rw [hP]; exact hfn)]
    rw [lsemFuelMemF_halt _ fuel s (hnone _ rfl)] at h
    cases h
    exact ⟨0, s, Nat.zero_le _, lsemFuelMemF_halt _ 0 s (hnone _ rfl), rfl, rfl,
      ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩⟩

end Body

/-! ## 9. The pass on a function body and on a program -/

section Final

/-- The pieces of a body followed by an instruction outside the fragment. -/
theorem pieces_append_bar {recog : String → Bool} (li : Linstr) (hli : fragOf? li recog = none) :
    ∀ body : Lcmd, pieces (body ++ [li]) recog = pieces body recog ++ [Piece.bar li] := by
  intro body
  induction body with
  | nil => simp [hli, pieces]
  | cons x body ih =>
      rw [List.cons_append, pieces_cons, pieces_cons, ih]
      cases fragOf? x recog with
      | none => rfl
      | some i =>
          simp only
          cases hp : pieces body recog with
          | nil => rfl
          | cons q qs => cases q <;> rfl

/-- The output of the fold lists the tail after instructions of the pieces and fragment
    instructions. -/
theorem fold_out (res : List String) (abi : IsaAbi) (T : Lcmd) (L : Std.HashSet String) :
    ∀ ps : List Piece, ∃ Y, (ps.foldr (rstep res abi) (T, L)).1 = Y ++ T
      ∧ ∀ li ∈ Y, li ∈ ps.flatMap pieceSrc ∨ ∃ j : FI, li = j.toL := by
  intro ps
  induction ps with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons p ps ih =>
      obtain ⟨Y, hY, hmem⟩ := ih
      cases p with
      | bar li =>
          refine ⟨li :: Y, by simp [rstep, hY], fun l hl => ?_⟩
          simp only [List.mem_cons] at hl
          rcases hl with rfl | hl
          · exact Or.inl (by simp [pieceSrc])
          · rcases hmem l hl with h | h
            · exact Or.inl (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr h)
            · exact Or.inr h
      | run is =>
          refine ⟨_ ++ Y, by simp only [List.foldr_cons, rstep]; rw [hY, List.append_assoc],
            fun l hl => ?_⟩
          rcases List.mem_append.1 hl with hl | hl
          · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hl
            exact Or.inr ⟨j, rfl⟩
          · rcases hmem l hl with h | h
            · exact Or.inl (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr h)
            · exact Or.inr h

theorem dropRet_typeBody_of_noRet (tag : LinstrR → MemTag) (Y : Lcmd)
    (h : ∀ li ∈ Y, li.li_i ≠ .Lret) : dropRet (typeBody tag Y) = typeBody tag Y := by
  unfold dropRet
  split
  · rename_i t hl
    exfalso
    rcases List.eq_nil_or_concat Y with rfl | ⟨Y0, l, rfl⟩
    · simp [typeBody] at hl
    · simp [typeBody] at hl
      exact h l (by simp) hl.1
  · rfl

theorem dropRet_typeBody_ret (tag : LinstrR → MemTag) (Y : Lcmd) (ii : Nat) :
    dropRet (typeBody tag (Y ++ [⟨ii, .Lret⟩])) = typeBody tag Y := by
  simp [dropRet, typeBody]

/-- The conditions on the register file: no general-purpose register and no register live
    at a return is a frame cell, and the empty name is no location. -/
structure AbiOK (res : List String) (abi : IsaAbi) : Prop where
  gf : ∀ y, isGP y abi = true → isFrame y = false
  emp : isLoc "" abi = false
  ret : ∀ y ∈ retLive res abi, isFrame y = false

/-- The registers the pass keeps at the end of a body: the registers live at a return when
    the body ends with a return, every general-purpose register otherwise. -/
def endRegs (res : List String) (abi : IsaAbi) (body : Lcmd) : List String :=
  match body.getLast? with
  | some ⟨_, .Lret⟩ => retLive res abi
  | _ => gpRegs abi

/-- **The register re-allocation of a function body on the flag machine.** Let the register
    file satisfy `AbiOK`, let `tag` give the register tag to every fragment instruction, and
    let the body `body` have a return at most as its last instruction, have every
    instruction a kept instruction (`keepOKB`), and every flag compare of the fragment read
    its destination. Every halting run of the typed body without its trailing return, from
    program counter `0`, is matched by a halting run of the re-allocated body, typed the same
    way, from the same state with at most the same fuel. The final states have the same
    function name, zero flag, arrays, word memory, carry and overflow flags, and the same
    value at every name that is not a location and at every general-purpose register of
    `endRegs res abi body`. -/
theorem reallocBody_lsemFuelMemF (res : List String) (abi : IsaAbi) (recog : String → Bool)
    (tag : LinstrR → MemTag) (hA : AbiOK res abi)
    (htag : ∀ d opn srcs, recog opn = true → opn ≠ "LOADIDX" → opn ≠ "STOREIDX" →
      tag (.Lopn [.reg d] opn srcs) = .reg none)
    (body : Lcmd)
    (hret : ∀ k li, body[k]? = some li → li.li_i = .Lret → k + 1 = body.length)
    (hkeep : ∀ li ∈ body, keepOKB (li.li_i, tag li.li_i) = true)
    (hcmp : ∀ li ∈ body, ∀ i, fragOf? li recog = some i → CmpReadsDst i)
    (fn : String) {fuel : Nat} {s t : LstateMF} (h0 : s.prog.base.lpc = 0)
    (h : lsemFuelMemF (singletonProgM fn (dropRet (typeBody tag body))) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel
      ∧ lsemFuelMemF (singletonProgM fn
          (dropRet (typeBody tag (reallocBody res body abi recog)))) fuel' s = some t'
      ∧ t'.prog.lfn = t.prog.lfn ∧ t'.zf = t.zf
      ∧ t'.prog.base.larr = t.prog.base.larr ∧ t'.prog.base.lmem = t.prog.base.lmem
      ∧ t'.prog.base.cf = t.prog.base.cf ∧ t'.prog.base.of = t.prog.base.of
      ∧ ∀ x, (isLoc x abi = false ∨ (isGP x abi = true ∧ x ∈ endRegs res abi body)) →
          t'.prog.base.reg.lvm x = t.prog.base.reg.lvm x := by
  -- the final agreement from `AgreeOff` at the end of the body
  have hfinal : ∀ (T : Lcmd) (L0 : Std.HashSet String) (a b : LstateM),
      regsOf res abi T = endRegs res abi body →
      AgreeOff (DX abi L0 (regsOf res abi T) []) a b →
      b.larr = a.larr ∧ b.lmem = a.lmem ∧ b.cf = a.cf ∧ b.of = a.of
        ∧ ∀ x, (isLoc x abi = false ∨ (isGP x abi = true ∧ x ∈ endRegs res abi body)) →
          b.reg.lvm x = a.reg.lvm x := by
    intro T L0 a b hE hAg
    refine ⟨hAg.1, hAg.2.1, hAg.2.2.1, hAg.2.2.2.1, fun x hx => hAg.2.2.2.2 x ?_⟩
    rintro ⟨h1, h2, -⟩
    rcases hx with hx | hx
    · rw [hx] at h1; cases h1
    · exact h2 ⟨hx.1, hE ▸ hx.2⟩
  by_cases hr : ∃ body0 ii, body = body0 ++ [⟨ii, .Lret⟩]
  · obtain ⟨body0, ii, rfl⟩ := hr
    set T : Lcmd := [⟨ii, .Lret⟩]
    have H : CoreHyp res abi recog tag T := ⟨hA.gf, hA.emp, hA.ret, htag, Or.inr ⟨ii, rfl⟩⟩
    have hno : ∀ li ∈ body0, li.li_i ≠ .Lret := by
      intro li hli he
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hli
      have hlt := (List.getElem?_eq_some_iff.1 hk).1
      have := hret k li (by rw [List.getElem?_append_left hlt, hk]) he
      rw [List.length_append, List.length_singleton] at this
      omega
    set L0 := (labelLiveFrames (body0 ++ T)).insertMany (Piece.bar ⟨ii, .Lret⟩).frames
    have hL0 : ∀ x, x ∈ L0 ↔ x ∈ labelLiveFrames (body0 ++ T) := by
      intro x
      simp [L0, Piece.frames, instrFrames]
    obtain ⟨Y, hY, hsim⟩ := body_sim res abi recog tag T H body0 L0 hL0
      (fun li hli => hkeep li (by simp [hli])) (fun li hli => hcmp li (by simp [hli])) fn
    have hrb : reallocBody res (body0 ++ T) abi recog
        = ((pieces body0 recog).foldr (rstep res abi) (T, L0)).1 := by
      rw [reallocBody_eq, pieces_append_bar _ rfl, List.foldr_append]
      rfl
    obtain ⟨Y2, hY2, hmem2⟩ := fold_out res abi T L0 (pieces body0 recog)
    have hYY : Y2 = Y := List.append_cancel_right (hY2.symm.trans hY)
    subst hYY
    have hnoY : ∀ li ∈ Y2, li.li_i ≠ .Lret := by
      intro li hli
      rcases hmem2 li hli with h1 | ⟨j, rfl⟩
      · rw [(pieces_spec (recog := recog) body0).1] at h1
        exact hno li h1
      · simp [FI.toL, FI.toR]
    rw [dropRet_typeBody_ret] at h
    obtain ⟨f', t', hle, hrun, hlfn, hzf, hAg⟩ := hsim h0 h
    refine ⟨f', t', hle, ?_, hlfn, hzf,
      hfinal T L0 _ _ (by simp [regsOf, endRegs, T]) hAg⟩
    rw [hrb, hY, dropRet_typeBody_ret]
    exact hrun
  · have hno : ∀ li ∈ body, li.li_i ≠ .Lret := by
      intro li hli he
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hli
      have hk1 := hret k li hk he
      apply hr
      refine ⟨body.take k, li.li_ii, ?_⟩
      have hlt := (List.getElem?_eq_some_iff.1 hk).1
      conv_lhs => rw [← List.take_append_drop k body]
      congr 1
      rw [List.drop_eq_getElem_cons hlt, List.drop_eq_nil_of_le (by omega)]
      obtain ⟨ii', w⟩ := li
      simp only at he
      subst he
      rw [List.getElem?_eq_some_iff] at hk
      rw [hk.2]
    set T : Lcmd := []
    have H : CoreHyp res abi recog tag T := ⟨hA.gf, hA.emp, hA.ret, htag, Or.inl rfl⟩
    have hL0 : ∀ x, x ∈ labelLiveFrames body ↔ x ∈ labelLiveFrames (body ++ T) := by
      simp [T]
    obtain ⟨Y, hY, hsim⟩ := body_sim res abi recog tag T H body (labelLiveFrames body) hL0
      hkeep hcmp fn
    obtain ⟨Y2, hY2, hmem2⟩ := fold_out res abi T (labelLiveFrames body) (pieces body recog)
    have hYY : Y2 = Y := List.append_cancel_right (hY2.symm.trans hY)
    subst hYY
    have hnoY : ∀ li ∈ Y2, li.li_i ≠ .Lret := by
      intro li hli
      rcases hmem2 li hli with h1 | ⟨j, rfl⟩
      · rw [(pieces_spec (recog := recog) body).1] at h1
        exact hno li h1
      · simp [FI.toL, FI.toR]
    rw [dropRet_typeBody_of_noRet tag body hno] at h
    obtain ⟨f', t', hle, hrun, hlfn, hzf, hAg⟩ := hsim h0 h
    have hE : regsOf res abi T = endRegs res abi body := by
      simp only [regsOf, T, endRegs]
      split
      · rename_i ii hl
        exfalso
        exact hno _ (List.mem_of_getLast? hl) rfl
      · rfl
    refine ⟨f', t', hle, ?_, hlfn, hzf, hfinal T _ _ _ hE hAg⟩
    rw [reallocBody_eq, hY, List.append_nil, dropRet_typeBody_of_noRet tag _ hnoY]
    simpa [T] using hrun

/-- **`reallocLprog_lsemFuelMemF`: the register re-allocation of a program on the flag
    machine.** For every function `(fn, fd)` of `p` whose body satisfies the conditions of
    `reallocBody_lsemFuelMemF`, the program `reallocLprog p abi recog` has the function
    `(fn, fd')` with the same result registers and the re-allocated body, and every halting
    run of the typed body of `fd` without its trailing return, from program counter `0`, is
    matched by a halting run of the typed body of `fd'` from the same state with at most the
    same fuel, into a state with the same function name, zero flag, arrays, word memory, carry
    and overflow flags, and the same value at every name that is not a location and at every
    general-purpose register of `endRegs fd.lfd_res abi fd.lfd_body` (the callee-saved, return
    and result registers when the body ends with a return). -/
theorem reallocLprog_lsemFuelMemF (p : Lprog) (abi : IsaAbi) (recog : String → Bool)
    (tag : LinstrR → MemTag)
    (htag : ∀ d opn srcs, recog opn = true → opn ≠ "LOADIDX" → opn ≠ "STOREIDX" →
      tag (.Lopn [.reg d] opn srcs) = .reg none)
    {fn : String} {fd : Lfundef} (hf : (fn, fd) ∈ p.lp_funcs) (hA : AbiOK fd.lfd_res abi)
    (hret : ∀ k li, fd.lfd_body[k]? = some li → li.li_i = .Lret → k + 1 = fd.lfd_body.length)
    (hkeep : ∀ li ∈ fd.lfd_body, keepOKB (li.li_i, tag li.li_i) = true)
    (hcmp : ∀ li ∈ fd.lfd_body, ∀ i, fragOf? li recog = some i → CmpReadsDst i) :
    ∃ fd', (fn, fd') ∈ (reallocLprog p abi recog).lp_funcs ∧ fd'.lfd_res = fd.lfd_res
      ∧ fd'.lfd_body = reallocBody fd.lfd_res fd.lfd_body abi recog
      ∧ ∀ {fuel : Nat} {s t : LstateMF}, s.prog.base.lpc = 0 →
        lsemFuelMemF (singletonProgM fn (dropRet (typeBody tag fd.lfd_body))) fuel s = some t →
        ∃ fuel' t', fuel' ≤ fuel
          ∧ lsemFuelMemF (singletonProgM fn (dropRet (typeBody tag fd'.lfd_body))) fuel' s
              = some t'
          ∧ t'.prog.lfn = t.prog.lfn ∧ t'.zf = t.zf
          ∧ t'.prog.base.larr = t.prog.base.larr ∧ t'.prog.base.lmem = t.prog.base.lmem
          ∧ t'.prog.base.cf = t.prog.base.cf ∧ t'.prog.base.of = t.prog.base.of
          ∧ ∀ x, (isLoc x abi = false
              ∨ (isGP x abi = true ∧ x ∈ endRegs fd.lfd_res abi fd.lfd_body)) →
              t'.prog.base.reg.lvm x = t.prog.base.reg.lvm x := by
  refine ⟨{ fd with lfd_body := reallocBody fd.lfd_res fd.lfd_body abi recog }, ?_, rfl, rfl,
    fun h0 h => reallocBody_lsemFuelMemF fd.lfd_res abi recog tag hA htag fd.lfd_body hret
      hkeep hcmp fn h0 h⟩
  simp only [reallocLprog, List.mem_map]
  exact ⟨(fn, fd), hf, rfl⟩

/-- A name is a frame cell exactly when its characters start with `k.`. -/
theorem isFrame_eq_list (y : String) : isFrame y = "k.".toList.isPrefixOf y.toList := by
  rw [isFrame, isPrefixOf_list]

/-- **The x86 register file satisfies `AbiOK`** for result registers that are no frame
    cells. -/
theorem abiOK_x86 (res : List String) (hres : ∀ y ∈ res, isFrame y = false) :
    AbiOK res x86Abi := by
  have hgp : ∀ y ∈ LcmdCopyPropagate.physGPs, isFrame y = false := by
    intro y hy
    rw [isFrame_eq_list]
    revert y
    decide
  refine ⟨fun y hy => hgp y (by simpa [isGP_x86, LcmdCopyPropagate.isPhysGP] using hy), ?_, fun y hy => ?_⟩
  · rw [isLoc_x86, Bool.or_eq_false_iff]
    exact ⟨by decide, not_isFrame_emp⟩
  · rw [retLive_x86] at hy
    simp only [List.mem_append, List.mem_filter] at hy
    rcases hy with hy | hy
    · rw [isFrame_eq_list]
      revert y
      decide
    · exact hres y hy.1

/-- A flag compare reads its destination, as a Boolean check. -/
def cmpReadsDstB (i : FI) : Bool :=
  !(decide (i.opn = withWidthTag 64 "CMP")) || decide (LOperand.reg i.d ∈ i.srcs)

theorem cmpReadsDstB_sound {i : FI} (h : cmpReadsDstB i = true) : CmpReadsDst i := by
  intro ho
  simp only [cmpReadsDstB, ho, decide_true, Bool.not_true, Bool.false_or,
    decide_eq_true_eq] at h
  exact h

/-- The conditions of `reallocBody_lsemFuelMemF` on a body as one Boolean check: a return
    only as the last instruction, every instruction a kept instruction, and every flag
    compare of the fragment reading its destination. -/
def reallocCfgOKB (tag : LinstrR → MemTag) (recog : String → Bool) (body : Lcmd) : Bool :=
  body.dropLast.all (fun li => match li.li_i with | .Lret => false | _ => true)
    && body.all (fun li => keepOKB (li.li_i, tag li.li_i))
    && body.all (fun li => match fragOf? li recog with
        | some i => cmpReadsDstB i
        | none => true)

theorem reallocCfgOKB_sound {tag : LinstrR → MemTag} {recog : String → Bool} {body : Lcmd}
    (h : reallocCfgOKB tag recog body = true) :
    (∀ k li, body[k]? = some li → li.li_i = .Lret → k + 1 = body.length)
      ∧ (∀ li ∈ body, keepOKB (li.li_i, tag li.li_i) = true)
      ∧ (∀ li ∈ body, ∀ i, fragOf? li recog = some i → CmpReadsDst i) := by
  simp only [reallocCfgOKB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun k li hk he => ?_, h2, fun li hli i hi => ?_⟩
  · have hlt := (List.getElem?_eq_some_iff.1 hk).1
    by_contra hne
    have hk' : k < body.dropLast.length := by simp; omega
    have hm : li ∈ body.dropLast := by
      rw [List.mem_iff_getElem?]
      exact ⟨k, by rw [List.getElem?_dropLast, if_pos (by simpa using hk'), hk]⟩
    have := h1 li hm
    rw [he] at this
    cases this
  · have := h3 li hli
    rw [hi] at this
    exact cmpReadsDstB_sound this

end Final

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg
