/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa

@[expose] public section

set_option autoImplicit false

/-!
# The symbolic step of the RV64 instruction set

The symbolic companion `rvSym : IsaSym rvIsa` of the RV64 instruction set `RvIsa.rvIsa`, over
the term language of `OwnedLprogTV`. The step of `rvIsa` is the flagless subset step
`subsetStep rvBases rvCond`: the shared control step on a control instruction, the core step
(a register copy, otherwise the memref step `lsemStepMem`) on an instruction of the alphabet
`rvBases`, a no-op on a keep marker, and no step otherwise. `rvSymStep` follows the same
cases: a label is the identity, a branch and a jump are outside the fragment, a register
copy sets the destination to the symbolic word of the source, any other instruction of the
alphabet is described by the memref layer `OwnedLprogTV.symMem`, a keep marker is the
identity, and an instruction outside the alphabet always fails. No instruction writes a
symbolic flag. The branch condition `rvSymDec` is the non-zero test of a register.

`rvSym` is lawful (`IsaSym.Lawful`), so the soundness of the checker
`OwnedLprogTV.ownedCheckM` at `rvSymStep` and `rvSymDec` is the instance of
`IsaSym.ownedCheckM_sound`.

## Main definitions

* `rvSymStep`, `rvSymDec`, `rvSym`: the symbolic step, the symbolic branch condition and the
  symbolic companion of `rvIsa`.

## Main results

* `rvSymStep_sound`, `rvSymDec_sound`: the symbolic step and branch condition describe
  `rvIsa.step` and `rvIsa.condEval`.
* `rvSym_lawful`: the remaining laws of the checker soundness.
* `rvSym_ownedCheckM_sound`: soundness of the checker on runs of `rvIsa`.
-/

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvSym

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (lsemStepMem_flags)
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (IsaSym)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
  (isTermR evalInstrPMemL_next nextPc_plain)

/-- **The RV64 symbolic step.** A label is the identity; a branch and a jump are outside the
    fragment; on an instruction of the alphabet `rvBases`, a register copy sets the
    destination to the symbolic word of the source and any other instruction is described by
    the memref layer `symMem`; a keep marker is the identity; any other instruction always
    fails. -/
def rvSymStep (i : LinstrRM) (ss : SSt) : SOut :=
  if isCtl i.fst then (if isLbl i then .ok ss [] else .unk)
  else if mnemOk rvBases i.fst then
    match movRegArgs? i with
    | some (dst, src) => .ok (ss.setR dst (ss.regs src)) []
    | none => symMem i ss
  else if isKeep i.fst then .ok ss [] else .fail

/-- **The RV64 symbolic branch condition**: a register tested for non-zero at width `64`, or
    a constant. -/
def rvSymDec (ss : SSt) : LOperand → SDec
  | .reg r => .nz (ss.regs r)
  | .imm n => .const (decide (BitVec.ofNat 64 n ≠ 0#64))
  | _ => .const false

/-- The memref loop step of an instruction that is no control instruction is the memref
    step. -/
theorem evalInstrPMemL_of_not_ctl (P : LprogM) (i : LinstrRM) (p : LstatePM)
    (h : isCtl i.fst = false) :
    evalInstrPMemL P i p = (lsemStepMem i p.base).map (fun b => { p with base := b }) := by
  obtain ⟨x, tag⟩ := i
  cases x <;> simp_all [isCtl, evalInstrPMemL]

/-- The lift of a register-file description keeps the symbolic flags. -/
theorem liftR_flags (ss : SSt) (o : ROut) : ∀ ss' gs, liftR ss o = .ok ss' gs →
    ss'.zf = ss.zf ∧ ss'.cf = ss.cf ∧ ss'.of = ss.of := by
  intro ss' gs h
  cases o <;> simp only [liftR, SOut.ok.injEq, reduceCtorEq] at h
  · rw [← h.1]; exact ⟨rfl, rfl, rfl⟩
  · rw [← h.1]; exact ⟨rfl, rfl, rfl⟩

/-- The memref layer keeps the symbolic flags. -/
theorem symMem_flags (i : LinstrRM) (ss : SSt) :
    ∀ ss' gs, symMem i ss = .ok ss' gs → ss'.zf = ss.zf ∧ ss'.cf = ss.cf ∧ ss'.of = ss.of := by
  intro ss' gs h
  obtain ⟨x, tag⟩ := i
  unfold symMem at h
  cases tag with
  | load w n =>
      dsimp only at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact ⟨rfl, rfl, rfl⟩
      · exact liftR_flags ss _ ss' gs h
  | store w n =>
      dsimp only at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact ⟨rfl, rfl, rfl⟩
      · exact liftR_flags ss _ ss' gs h
  | loadC => cases h
  | storeC => cases h
  | reg cd => exact liftR_flags ss _ ss' gs h

/-- A description of a memref step that keeps the symbolic flags describes the step on the
    flag-extended state, when the memref step keeps the carry and overflow flags. -/
theorem descM_lift {res : Option LstateM} {V : String → Σ w, BitVec w} {A : String → ArrCell}
    {C O Z : Bool} {ss : SSt} {s : LstateMF} {o : SOut}
    (hz : ∀ ss' gs, o = .ok ss' gs → ss'.zf = ss.zf ∧ ss'.cf = ss.cf ∧ ss'.of = ss.of)
    (hs : Holds V A C O Z ss s) (h : o.DescM res V A C O s.prog.base)
    (hfl : ∀ b, res = some b → b.cf = s.prog.base.cf ∧ b.of = s.prog.base.of) :
    o.Desc (res.map (fun b => { s with prog := { s.prog with base := b } })) V A C O Z s := by
  cases o with
  | ok ss' gs =>
      obtain ⟨ez, ec, eo⟩ := hz ss' gs rfl
      refine ⟨fun t ht => ?_, fun hg => by simpa using h.2 hg⟩
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp ht
      obtain ⟨hg, hH, hpc, hmem⟩ := h.1 b hb
      refine ⟨hg, ⟨hH.1, hH.2, ?_, ?_, ?_⟩, rfl, hpc, hmem⟩
      · show s.zf = _
        rw [ez]; exact hs.2.2.1
      · show b.cf = _
        rw [(hfl b hb).1, ec]; exact hs.2.2.2.1
      · show b.of = _
        rw [(hfl b hb).2, eo]; exact hs.2.2.2.2
  | fail =>
      simp only [SOut.DescM] at h
      simp [SOut.Desc, h]
  | unk => trivial

/-- **The RV64 symbolic step describes the RV64 step exactly.** -/
theorem rvSymStep_sound (P : LprogM) (i : LinstrRM) (ss : SSt) :
    StepSound (rvIsa.step P i) ss (rvSymStep i ss) := by
  intro V A C O Z s hs
  rw [rvIsa_step]
  unfold rvSymStep subsetStep
  by_cases hc : isCtl i.fst = true
  · rw [if_pos hc, if_pos hc]
    by_cases hl : isLbl i = true
    · rw [if_pos hl]
      obtain ⟨x, tag⟩ := i
      cases x <;> simp only [isLbl, Bool.false_eq_true] at hl
      refine ⟨fun t ht => ?_, fun _ => rfl⟩
      cases ht
      exact ⟨allG_nil V A C O, ⟨hs.1, hs.2.1, hs.2.2⟩, rfl, rfl, rfl⟩
    · rw [if_neg hl]; trivial
  · rw [if_neg hc, if_neg hc]
    by_cases hm : mnemOk rvBases i.fst = true
    · rw [if_pos hm, if_pos hm]
      simp only []
      unfold coreStep
      cases hmv : movRegArgs? i with
      | some p =>
          obtain ⟨dst, src⟩ := p
          simp only [readReg]
          refine ⟨fun t ht => ?_, fun _ => rfl⟩
          cases ht
          refine ⟨allG_nil V A C O, ⟨fun q => ?_, hs.2.1, hs.2.2⟩, rfl, rfl, rfl⟩
          simp only [SSt.setR, LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.lvm_nextPc,
            LstateN.lvm_setReg]
          split_ifs
          · exact hs.1 src
          · exact hs.1 q
      | none =>
          simp only []
          rw [evalInstrPMemL_of_not_ctl P i s.prog (by simpa using hc), Option.map_map]
          exact descM_lift (symMem_flags i ss) hs
            (symMem_sound i ss V A C O s.prog.base ⟨hs.1, hs.2.1⟩)
            (fun b hb => lsemStepMem_flags hb)
    · rw [if_neg hm, if_neg hm]
      by_cases hk : isKeep i.fst = true
      · rw [if_pos hk, if_pos hk]
        refine ⟨fun t ht => ?_, fun _ => rfl⟩
        cases ht
        exact ⟨allG_nil V A C O, ⟨hs.1, hs.2.1, hs.2.2⟩, rfl, rfl, rfl⟩
      · rw [if_neg hk, if_neg hk]
        rfl

/-- **The RV64 symbolic branch condition evaluates to the RV64 branch condition.** -/
theorem rvSymDec_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O Z : Bool}
    {ss : SSt} {s : LstateMF} (hs : Holds V A C O Z ss s) (c : LOperand) :
    rvIsa.condEval s c = (rvSymDec ss c).ev V A C O Z := by
  rw [rvIsa_condEval]
  unfold rvCond rvSymDec
  cases c with
  | reg r =>
      simp only [SDec.ev, condNZ, evalOperandN, getW_eq, hs.1 r]
      split_ifs <;> rfl
  | imm n => rfl
  | arr _ _ => rfl
  | arrIdx _ _ _ => rfl

/-- **The RV64 symbolic companion**: `rvSymStep` and `rvSymDec`, with `rvSymStep_sound` and
    `rvSymDec_sound`. -/
def rvSym : IsaSym rvIsa where
  symStep := rvSymStep
  symDec := rvSymDec
  symStep_sound := rvSymStep_sound
  symDec_sound := fun hs c => rvSymDec_sound hs c

/-- The RV64 symbolic companion is lawful. -/
theorem rvSym_lawful : rvSym.Lawful where
  good := by
    intro i ss hg ss' gs h
    change rvSymStep i ss = _ at h
    unfold rvSymStep at h
    split_ifs at h
    · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact hg
    · cases hmv : movRegArgs? i with
      | some p =>
          rw [hmv] at h
          simp only [SOut.ok.injEq] at h; rw [← h.1]; exact hg.setR _ _
      | none => rw [hmv] at h; exact symMem_good i hg h
    · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact hg
  label := by
    intro i hl ss
    change rvSymStep i ss = _
    have hc : isCtl i.fst = true := by
      obtain ⟨x, tag⟩ := i
      cases x <;> simp_all [isLbl, isCtl]
    unfold rvSymStep
    rw [if_pos hc, if_pos hl]
  plain := by
    intro P x hx s t h
    rw [rvIsa_step] at h
    unfold subsetStep at h
    split_ifs at h with hc hm hk
    · obtain ⟨xi, tag⟩ := x
      cases xi <;> simp_all [isCtl, isTermR, ctlStep]
      subst h
      exact ⟨rfl, rfl⟩
    · simp only [] at h
      unfold coreStep at h
      cases hmv : movRegArgs? x with
      | some p =>
          obtain ⟨dst, src⟩ := p
          rw [hmv] at h
          simp only [readReg, Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl⟩
      | none =>
          rw [hmv] at h
          simp only [] at h
          obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨h1, h2⟩ := evalInstrPMemL_next P x s.prog p hp
          exact ⟨h1, nextPc_plain hx h2⟩
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
  ret := by
    intro P tag s
    rw [rvIsa_step]
    simp [subsetStep, isCtl, mnemOk, isKeep]
  step_subst := by
    intro σ i ss
    change rvSymStep i (ss.subst σ) = (rvSymStep i ss).subst σ
    unfold rvSymStep
    split_ifs
    · rfl
    · rfl
    · cases movRegArgs? i with
      | some p => simp only [SOut.subst, SSt.subst_setR, List.map_nil]; rfl
      | none => exact symMem_subst σ i ss
    · rfl
    · rfl
  dec_subst := by
    intro σ ss c
    cases c <;> rfl

/-- **Soundness of the checker on RV64 runs.** If `ownedCheckM outs B B'` accepts under the
    RV64 symbolic step `rvSymStep` and branch condition `rvSymDec`, every halting run of
    `rvIsa` on the singleton program over `B` from a state at pc `0` of that function is
    matched by a halting run on the singleton program over `B'` from the same state, and the
    end states agree on the registers `outs`, on the arrays and on the word memory. -/
theorem rvSym_ownedCheckM_sound {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckM outs B B' rvSymStep rvSymDec = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : rvIsa.lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', rvIsa.lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' :=
  rvSym.ownedCheckM_sound rvSym_lawful h fn s t hfn hpc fuel hrun

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvSym
