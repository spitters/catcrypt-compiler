/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW
public import CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck

@[expose] public section

set_option autoImplicit false

/-!
# The bounds-checked x86 instruction set with procedure summaries

`x86IsaK` is the x86 instruction set whose step is the bounds-checked step
`JasminLsemMemChecked.evalInstrPMemFk true`. With the summaries of a procedure table `T`,
its runs are the checked runs of `x86Isa.withProcs T`. This module discharges, for
`x86IsaK`, the two instruction-set hypotheses of `ImageAddrCallW.haltsC_of_linkedChecksOne`:
every step is a checked step, and the steps of a body that passes `deadSegB` keep the
agreement of the dead table.

The bounds check `idxInvCheckPB` is the check `IdxInvCheck.idxInvCheckB` with calls: the
symbolic walk of a block (`segWalk`) steps over the shadow instruction of a call of a
procedure of `T` by starting a new symbolic segment at the state after the call. The facts
at the start of the new segment are the facts of the annotation that do not name the
destination of the call and that follow from the facts before the call, read through the
symbolic registers before the call (`callFacts`). The call writes its destination, a word
to the register or an array to the array carrier, on which no fact is kept, and keeps every
other register and the flags, as `LprogIsa.retRes` does.

## Main definitions

* `x86IsaK`: the x86 instruction set with the bounds-checked step.
* `segWalk`, `blockInvOkP`, `idxInvCheckPB`: the bounds check with calls.
* `idxAnnotP`: an annotation for `idxInvCheckPB`, by restriction of masks over the
  candidates to a fixed point (`annPassP`, `annFixP`).

## Main results

* `x86IsaK_checked`, `x86IsaK_pcFree`, `x86IsaK_refusesProcs`, `fnStable_x86IsaK`.
* `cutCheck_soundK`: `LprogCallCut.cutCheck_soundI` at `x86IsaK`.
* `x86IsaK_withProcs_lsemFuelMemF`: the runs of `x86IsaK.withProcs T` are the checked runs
  of `x86Isa.withProcs T`.
* `deadSteps_x86K`: a body that passes `deadSegB` has `DeadSteps` at `x86IsaK`.
* `refRun_checked`: a halting run of `x86Isa.withProcs T` on a body accepted by
  `idxInvCheckPB` from pc `0` and a state satisfying the entry facts is a run of
  `x86IsaK.withProcs T`.
* `haltsC_of_linkedChecksKW`: `ImageAddrCallW.haltsC_of_linkedChecksOne` at `x86IsaK`, at the
  class `ImageAddrCallW.printedAddrCWB`, from the Boolean check `deadSegB`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa ProcTable procCall? shadowCall?
  procStep retWord retArr retRes CallRes lfn_retRes lpc_retRes isCtl ctlStep)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_step)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (idxOkB_of_none)

/-! ## 1. The bounds-checked x86 instruction set -/

/-- A control instruction is in bounds. -/
theorem idxOkB_of_isCtl {i : LinstrRM} (h : isCtl i.fst = true) (s : LstateMF) :
    JasminLsemMemChecked.idxOkB i s = true := by
  obtain ⟨x, tag⟩ := i
  refine idxOkB_of_none ?_ ?_ <;> cases x <;> simp_all [isCtl, loadStruct?, storeStruct?]

/-- A shadow instruction of a call is in bounds. -/
theorem idxOkB_of_shadowCall {i : LinstrRM} (h : shadowCall? i.fst ≠ none) (s : LstateMF) :
    JasminLsemMemChecked.idxOkB i s = true := by
  obtain ⟨x, tag⟩ := i
  obtain ⟨dst, opn, srcs, rfl, hm⟩ := LprogIsaProcs.shadowCall?_wire h
  refine idxOkB_of_none ?_ ?_
  · show loadStruct? (.Lopn [.reg dst] opn srcs) = none
    unfold loadStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (hm.ne _ (by decide)))
  · show storeStruct? (.Lopn [.reg dst] opn srcs) = none
    unfold storeStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (hm.ne _ (by decide)))

/-- **The x86 instruction set with the bounds-checked step**: the step is
    `JasminLsemMemChecked.evalInstrPMemFk true`, the data and the branch condition are those
    of `x86Isa`. -/
def x86IsaK : Isa :=
  { x86Isa with
    step := JasminLsemMemChecked.evalInstrPMemFk true
    step_ctl := fun P i s h => by
      rw [JasminLsemMemChecked.evalInstrPMemFk_true, ite_eq_left (idxOkB_of_isCtl h s)]
      exact x86Isa.step_ctl P i s h }

theorem x86IsaK_step : x86IsaK.step = JasminLsemMemChecked.evalInstrPMemFk true := rfl

theorem x86IsaK_condEval : x86IsaK.condEval = decC := rfl

/-- Every step of `x86IsaK` is a bounds-checked step: the hypothesis `hI` of
    `ImageAddrCallW.haltsC_of_linkedChecksOne`. -/
theorem x86IsaK_checked : ∀ (P : LprogM) (i : LinstrRM) (s t : LstateMF),
    x86IsaK.step P i s = some t → JasminLsemMemChecked.evalInstrPMemFk true P i s = some t :=
  fun _ _ _ _ h => h

/-- The steps of `x86IsaK` do not read the counter. -/
theorem x86IsaK_pcFree : LprogCallCut.PcFree x86IsaK := by
  refine ⟨fun _ _ _ => rfl, fun P P' i hi s q => ?_⟩
  have hk : JasminLsemMemChecked.idxOkB i (Ascent.IsaCfg.goto s q)
      = JasminLsemMemChecked.idxOkB i s := rfl
  rw [x86IsaK_step, JasminLsemMemChecked.evalInstrPMemFk_true,
    JasminLsemMemChecked.evalInstrPMemFk_true, hk]
  split
  · exact LprogCallCut.x86Isa_pcFree.step P P' i hi s q
  · rfl

/-- `x86IsaK` has no step on a shadow instruction of a call of a procedure of `T`. -/
theorem x86IsaK_refusesProcs (T : ProcTable) : x86IsaK.RefusesProcs T := by
  intro P i s h
  rw [x86IsaK_step, JasminLsemMemChecked.evalInstrPMemFk_true]
  split
  · exact LprogIsaProcs.x86Isa_refusesProcs T P i s h
  · rfl

/-- A step of `x86IsaK` stays in the function of its state. -/
theorem fnStable_x86IsaK : LprogCallCut.FnStable x86IsaK := fun P i s u h =>
  (AllocCheck.LcmdCFG.evalInstrPMemF_next P i s u
    (JasminLsemMemChecked.evalInstrPMemF_of_k h)).1

open LprogCallCut (IsSite IsCut IsCutRev CutCheckSoundI) in
/-- **Soundness of a validation by segments on the bounds-checked x86 instruction set.**
    `LprogCallCut.cutCheck_soundI` at `x86IsaK`: for cut programs of `B` that are cuts and
    cut programs of `B'` that are cuts halting only at their exits, under a simulation
    `CutSimI x86IsaK`, every halting run of `x86IsaK.withProcs T` on `B` from a state of
    `fn` at the counter `0` is matched by a halting run on `B'` from the same state, the
    end states agreeing on the registers `outs`, the arrays and the word memory. -/
theorem cutCheck_soundK {T : ProcTable} {outs : List String} {fn : String}
    {B B' : List LinstrRM} {cut cut' : Option Nat → Option Nat → List LinstrRM}
    {pos pos' : Option Nat → Option Nat → Nat → Nat}
    (hcut : ∀ e x, IsSite T B e → IsSite T B x → IsCut T fn B e x (cut e x) (pos e x))
    (hcut' : ∀ e x, IsSite T B' e → IsSite T B' x →
      IsCut T fn B' e x (cut' e x) (pos' e x) ∧ IsCutRev T B' x (cut' e x) (pos' e x)) :
    CutCheckSoundI x86IsaK T outs fn B B' cut cut' :=
  LprogCallCut.cutCheck_soundI x86IsaK_pcFree (x86IsaK_refusesProcs T) fnStable_x86IsaK
    hcut hcut'

/-- The step of `x86IsaK.withProcs T` is the checked step of `x86Isa.withProcs T`. -/
theorem x86IsaK_withProcs_step (T : ProcTable) (P : LprogM) (i : LinstrRM) (s : LstateMF) :
    (x86IsaK.withProcs T).step P i s = (x86Isa.withProcs T).evalInstrPMemFk true P i s := by
  rw [Isa.evalInstrPMemFk_true]
  cases hq : procCall? T i.fst with
  | none =>
      rw [Isa.withProcs_step_of_none _ T P i s hq, Isa.withProcs_step_of_none _ T P i s hq,
        x86IsaK_step, JasminLsemMemChecked.evalInstrPMemFk_true]
      rfl
  | some q =>
      have hs : shadowCall? i.fst ≠ none := by
        intro hn
        simp [procCall?, hn] at hq
      rw [ite_eq_left (idxOkB_of_shadowCall hs s)]
      simp only [Isa.withProcs, hq]

/-- **The runs of `x86IsaK.withProcs T` are the checked runs of `x86Isa.withProcs T`.** -/
theorem x86IsaK_withProcs_lsemFuelMemF (T : ProcTable) :
    (x86IsaK.withProcs T).lsemFuelMemF = (x86Isa.withProcs T).lsemFuelMemFk true := by
  funext P fuel
  induction fuel with
  | zero => funext s; rfl
  | succ n ih =>
      funext s
      simp only [Isa.lsemFuelMemF, Isa.lsemFuelMemFk, x86IsaK_withProcs_step, ih]

/-! ## 2. The steps of a body that passes `deadSegB` at `x86IsaK` -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (DeadTab AgreeOffD descReadsA
  deadStepB step_deadStepB deadCtlB ctl_deadStep DeadAgree deadSegB DeadSteps)

theorem mem_descReadsA_load {x : LinstrR} {w n : Nat} {ss : SSt} {gs : List SG}
    (h : symStep (x, .load w n) SSt.start = .ok ss gs) {d b idx : String}
    (hl : loadStruct? x = some (d, b, idx)) : idx ∈ descReadsA ss gs := by
  unfold loadStruct? at hl
  split at hl
  · split_ifs at hl with ho
    cases hl
    subst ho
    simp only [symStep, cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?, aluFl,
      symMem, loadStruct?, ite_true, SOut.ok.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [descReadsA, ImageAddrSim.descReads, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      ⟨SG.wid (STerm.reg idx) 64, by simp [SSt.start], List.mem_singleton_self idx⟩))))
  · cases hl

theorem mem_descReadsA_store {x : LinstrR} {w n : Nat} {ss : SSt} {gs : List SG}
    (h : symStep (x, .store w n) SSt.start = .ok ss gs) {d b idx v : String}
    (hl : storeStruct? x = some (d, b, idx, v)) : idx ∈ descReadsA ss gs := by
  unfold storeStruct? at hl
  split at hl
  · split_ifs at hl with ho
    cases hl
    subst ho
    simp only [symStep, cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?, aluFl,
      symMem, storeStruct?, ite_true] at h
    obtain ⟨-, rfl⟩ := h
    simp only [descReadsA, ImageAddrSim.descReads, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      ⟨SG.wid (STerm.reg idx) 64, by simp [SSt.start], List.mem_singleton_self idx⟩))))
  · cases hl

/-- **The bounds condition of a checked step is the same at two states that agree up to
    the dead names of the table**: the index register of an indexed access is read by its
    symbolic step, so it is not dead. -/
theorem idxOkB_congrD {D : DeadTab} {k : Nat} {i : LinstrRM} (hk : deadStepB D k i = true)
    {s s' : LstateMF} (hag : AgreeOffD (D.dead k) (D.z k) (D.c k) s s') :
    JasminLsemMemChecked.idxOkB i s = JasminLsemMemChecked.idxOkB i s' := by
  unfold deadStepB at hk
  split at hk
  · rename_i ss gs heq
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hk
    have hrd : ∀ r ∈ descReadsA ss gs, s.prog.base.reg.lvm r = s'.prog.base.reg.lvm r :=
      fun r hr => hag.off.regs r (by simpa using hk.1.1.1.1 r hr)
    obtain ⟨x, tag⟩ := i
    cases tag with
    | load w n =>
        cases hl : loadStruct? x with
        | none => simp [JasminLsemMemChecked.idxOkB, hl]
        | some p =>
            obtain ⟨d, b, idx⟩ := p
            have e := hrd idx (mem_descReadsA_load heq hl)
            simp only [JasminLsemMemChecked.idxOkB, hl, JasminLsemMemChecked.idxBelowB, getW_eq,
              e]
    | store w n =>
        cases hl : storeStruct? x with
        | none => simp [JasminLsemMemChecked.idxOkB, hl]
        | some p =>
            obtain ⟨d, b, idx, v⟩ := p
            have e := hrd idx (mem_descReadsA_store heq hl)
            simp only [JasminLsemMemChecked.idxOkB, hl, JasminLsemMemChecked.idxBelowB, getW_eq,
              e]
    | _ => rfl
  · cases hk

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (Steps) in
/-- **A run of steps of `x86IsaK` on a checked body keeps the agreement of the table**:
    `ImageAddrCall.steps_deadSeg` at the bounds-checked step. -/
theorem steps_deadSegK {D : DeadTab} {fn : String} {B : List LinstrRM}
    (hD : deadSegB D B = true) :
    ∀ (n : Nat) (s s' u : LstateMF), DeadAgree D s s' →
      Steps x86IsaK (singletonProgM fn B) n s u →
      ∃ u', Steps x86IsaK (singletonProgM fn B) n s' u' ∧ DeadAgree D u u'
  | 0, s, s', u, hag, h => by
      have hsu : s = u := Option.some.inj h
      subst hsu
      exact ⟨s', rfl, hag⟩
  | n + 1, s, s', u, hag, h => by
      simp only [Steps, Ascent.CutPoint.iter, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨c, hc, h⟩ := h
      unfold LprogIsa.Isa.lsemStepPMemF at hc ⊢
      have hfe : findInstrMem (singletonProgM fn B) s'.prog
          = findInstrMem (singletonProgM fn B) s.prog := by
        unfold findInstrMem
        rw [← hag.off.fn]
        exact congrArg (fun q => if s.prog.lfn = fn then B[q]? else none) hag.off.pc.symm
      rw [hfe]
      cases hf : findInstrMem (singletonProgM fn B) s.prog with
      | none => rw [hf] at hc; cases hc
      | some i =>
          rw [hf] at hc
          dsimp only at hc
          have hBi : B[s.prog.base.reg.lpc]? = some i := by
            unfold findInstrMem at hf
            split at hf
            · exact hf
            · cases hf
          have hchk := List.all_eq_true.mp hD s.prog.base.reg.lpc
            (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hBi).1)
          rw [hBi] at hchk
          simp only [Option.all_some] at hchk
          have hstep : ∃ c', x86IsaK.step (singletonProgM fn B) i s' = some c'
              ∧ DeadAgree D c c' := by
            by_cases hctl : LprogIsa.isCtl i.fst = true
            · rw [ite_eq_left hctl] at hchk
              rw [x86IsaK.step_ctl _ _ _ hctl] at hc ⊢
              exact ctl_deadStep hchk hag hc
            · rw [ite_eq_right hctl] at hchk
              have hctl' : LprogIsa.isCtl i.fst = false := by simpa using hctl
              cases hsh : LprogIsa.shadowCall? i.fst with
              | some q =>
                  rw [x86IsaK_step, JasminLsemMemChecked.evalInstrPMemFk_true,
                    LprogIsaProcs.evalInstrPMemF_shadowCall _ i s (by rw [hsh]; simp)] at hc
                  simp at hc
              | none =>
                  rw [hsh] at hchk
                  have hk : deadStepB D s.prog.base.reg.lpc i = true := by simpa using hchk
                  have hok := JasminLsemMemChecked.idxOkB_of_checked hc
                  have hc0 := JasminLsemMemChecked.evalInstrPMemF_of_k hc
                  obtain ⟨c', hc', hag'⟩ := step_deadStepB (singletonProgM fn B)
                    (singletonProgM fn B) hk hag hc0
                  refine ⟨c', ?_, ?_⟩
                  · rw [x86IsaK_step, JasminLsemMemChecked.evalInstrPMemFk_true,
                      ← idxOkB_congrD hk hag, hok, ite_eq_left rfl]
                    exact hc'
                  · have e : c.prog.base.reg.lpc = s.prog.base.reg.lpc + 1 := by
                      have := x86IsaK_pcFree.lpc_succ (singletonProgM fn B) hctl' hc
                      rw [this]
                      rfl
                    unfold DeadAgree
                    rw [e]
                    exact hag'
          obtain ⟨c', hc', hag'⟩ := hstep
          obtain ⟨u', hu', hagu⟩ := steps_deadSegK hD n c c' u hag' h
          exact ⟨u', ⟨c', hc', hu'⟩, hagu⟩

/-- **At `x86IsaK`, the steps of a body that passes `deadSegB` keep the agreement of the
    table**: the hypothesis `hD` of `ImageAddrCallW.haltsC_of_linkedChecksOne`. -/
theorem deadSteps_x86K {D : DeadTab} {fn : String} {B : List LinstrRM}
    (hD : deadSegB D B = true) : DeadSteps D x86IsaK (singletonProgM fn B) :=
  steps_deadSegK hD

/-! ## 3. The steps of a procedure summary -/

/-- A step of a procedure summary writes a result, a word or a word array, to its
    destination and advances the counter. -/
theorem procStep_retRes {pr : LprogIsa.ProcSummary} {dst : String} {srcs : List LOperand}
    {s s1 : LstateMF} (h : procStep pr dst srcs s = some s1) : ∃ x, s1 = retRes dst x s := by
  unfold procStep at h
  split_ifs at h
  obtain ⟨vs, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨x, rfl⟩

/-- A step of a procedure summary without a word-array result writes a word to its
    destination and advances the counter. -/
theorem procStep_retWord {pr : LprogIsa.ProcSummary} (hrw : pr.RetWord) {dst : String}
    {srcs : List LOperand} {s s1 : LstateMF} (h : procStep pr dst srcs s = some s1) :
    ∃ r, s1 = retWord dst r s := by
  rw [LprogIsa.procStep_of_retWord hrw] at h
  split_ifs at h
  obtain ⟨vs, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨r, rfl⟩

theorem retWord_lvm_ne {dst q : String} (r : BitVec 64) (s : LstateMF) (h : q ≠ dst) :
    (retWord dst r s).prog.base.reg.lvm q = s.prog.base.reg.lvm q := by
  simp [retWord, h]

/-- The result of a call keeps every register other than the destination. -/
theorem retRes_lvm_ne {dst q : String} (x : CallRes) (s : LstateMF) (h : q ≠ dst) :
    (retRes dst x s).prog.base.reg.lvm q = s.prog.base.reg.lvm q := by
  cases x <;> simp [retWord, retArr, h]

/-- A step of `x86Isa.withProcs T` at an instruction that is no terminator stays in the
    function and advances the pc by one. -/
theorem stepPlain_withProcs (T : ProcTable) : StepPlain (x86Isa.withProcs T) := by
  intro P x hx s t h
  cases hq : procCall? T x.fst with
  | none =>
      rw [Isa.withProcs_step_of_none _ T P x s hq] at h
      exact stepPlain_x86 P hx h
  | some q =>
      simp only [Isa.withProcs, hq] at h
      obtain ⟨x, rfl⟩ := procStep_retRes h
      exact ⟨lfn_retRes _ x s, lpc_retRes _ x s⟩

/-- `x86Isa.withProcs T` takes no step at `Lret`. -/
theorem withProcs_ret (T : ProcTable) (P : LprogM) (tag : MemTag) (s : LstateMF) :
    (x86Isa.withProcs T).step P (.Lret, tag) s = none := by
  rw [Isa.withProcs_step_of_none _ T P _ s rfl]
  exact evalInstrPMemF_ret P tag s

/-! ## 4. The bounds check with calls -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (IdxFact SFact entails startF
  annAt oblsOk guardW64 termInvOk startF_holds succOk_sound oblsOk_sound entails_sound
  edgeFacts edgeFacts_sound guardW64_holds)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (oblOf oblOf_iff RunLOk
  runIdxOk_of_runL_at runIdxOk_halt_at runIdxOk_step_at idxOkB_goto idxOkB_cond)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel)

/-- The registers a fact names. -/
def factRegs : IdxFact → List String
  | .le rs _ => rs
  | .ge r _ => [r]
  | .ale _ _ => []
  | .w64 r => [r]

/-- A fact names only registers: it is not an element bound of an array. -/
def regFact : IdxFact → Bool
  | .ale _ _ => false
  | .le _ _ | .ge _ _ | .w64 _ => true

/-- A register fact holds at two register files that agree on the registers it names, at
    any arrays. -/
theorem idxFact_holds_congr {V V' : String → Σ w, BitVec w} {A A' : String → ArrCell}
    {f : IdxFact} (hr : regFact f = true) (h : ∀ r ∈ factRegs f, V r = V' r)
    (hf : f.holds V A) : f.holds V' A' := by
  cases f with
  | le rs b =>
      simp only [IdxFact.holds, factRegs] at hf h ⊢
      rwa [List.map_congr_left (fun r hr => congrArg IdxInvCheck.wval (h r hr))] at hf
  | ge r k =>
      simp only [IdxFact.holds] at hf ⊢
      rwa [← h r (by simp [factRegs])]
  | ale _ _ => simp [regFact] at hr
  | w64 r =>
      simp only [IdxFact.holds] at hf ⊢
      rwa [← h r (by simp [factRegs])]

/-- **The facts after a call** with destination `dst`, from the candidates `cs`: the register
    facts (`regFact`; the callee may write the arrays) that do not name `dst` and follow from
    the facts `F`, read through the symbolic state `ss` before the call. -/
def callFacts (cs : List IdxFact) (F : List SFact) (ss : SSt) (dst : String) :
    List IdxFact :=
  cs.filter fun f =>
    regFact f && !(factRegs f).contains dst && entails F (f.toS ss.regs ss.arrs)

/-- The facts after a call hold at every state that keeps the registers other than the
    destination of a state described by `ss`. -/
theorem callFacts_sound {cs : List IdxFact} {F : List SFact} {ss : SSt} {dst : String}
    {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O Z : Bool} {s s1 : LstateMF}
    (hF : ∀ g ∈ F, g.holds V A C O) (hs : Holds V A C O Z ss s)
    (h1 : ∀ q, q ≠ dst → s1.prog.base.reg.lvm q = s.prog.base.reg.lvm q) :
    ∀ f ∈ callFacts cs F ss dst, f.holds s1.prog.base.reg.lvm s1.prog.base.larr := by
  intro f hf
  simp only [callFacts, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hf
  obtain ⟨-, ⟨hr, hd⟩, he⟩ := hf
  have hd' : dst ∉ factRegs f := by simpa using hd
  have h2 := (IdxFact.toS_holds (V := V) (A := A) (C := C) (O := O) ss.regs ss.arrs f).mp
    (entails_sound hF _ he)
  have e : (fun r => (ss.regs r).ev V A C O) = s.prog.base.reg.lvm :=
    funext fun q => (hs.1 q).symm
  rw [e] at h2
  exact idxFact_holds_congr hr (fun r hr => (h1 r fun hrd => hd' (hrd ▸ hr)).symm) h2

/-- The result of a segmented symbolic walk: the facts at the start of the last segment with
    the symbolic state from that start; a walk through a step that always fails; or a walk
    the check rejects. -/
inductive SegOut where
  | ok (F : List SFact) (ss : SSt)
  | fail
  | bad

/-- **The segmented symbolic walk** of a stretch under the procedure table `T` and the
    candidates `cs`, from the facts `F` at the start of the current segment and the symbolic
    state `ss` from that start. The shadow instruction of a call of a procedure of `T`
    starts a new segment at `SSt.start` with the facts `callFacts`. Every other instruction
    takes the symbolic step `symStep`; its index obligations follow from the facts and the
    width facts of the guards of the step, which join the facts. -/
def segWalk (T : ProcTable) (cs : List IdxFact) : List SFact → SSt → List LinstrRM → SegOut
  | F, ss, [] => .ok F ss
  | F, ss, i :: is =>
      match procCall? T i.fst with
      | some q => segWalk T cs (startF (callFacts cs F ss q.2.1)) SSt.start is
      | none =>
          match symStep i ss with
          | .ok ss1 g1 =>
              if oblsOk (F ++ g1.flatMap guardW64) (oblOf i ss) then
                segWalk T cs (F ++ g1.flatMap guardW64) ss1 is
              else .bad
          | .fail => .fail
          | .unk => .bad

/-- **The segmented walk is sound.** From a state `ss` describes, at which the facts `F`
    hold, a successful run of `x86Isa.withProcs T` of a stretch that the walk does not
    reject is in bounds, and the walk ends in a segment whose facts hold and whose symbolic
    state describes the end state. -/
theorem segWalk_sound (T : ProcTable) (cs : List IdxFact) (P : LprogM) :
    ∀ (is : List LinstrRM) (F : List SFact) (ss : SSt) (V : String → Σ w, BitVec w)
      (A : String → ArrCell) (C O Z : Bool) (s u : LstateMF),
      Holds V A C O Z ss s → (∀ g ∈ F, g.holds V A C O) →
      (x86Isa.withProcs T).runL P is s = some u → segWalk T cs F ss is ≠ .bad →
      RunLOk P is s (x86Isa.withProcs T) ∧
        ∃ (F' : List SFact) (ss' : SSt) (V' : String → Σ w, BitVec w) (A' : String → ArrCell)
          (C' O' Z' : Bool), segWalk T cs F ss is = .ok F' ss' ∧
          Holds V' A' C' O' Z' ss' u ∧ ∀ g ∈ F', g.holds V' A' C' O'
  | [], F, ss, V, A, C, O, Z, s, u, hs, hF, hu, _ => by
      cases hu
      exact ⟨trivial, F, ss, V, A, C, O, Z, rfl, hs, hF⟩
  | i :: is, F, ss, V, A, C, O, Z, s, u, hs, hF, hu, hb => by
      simp only [Isa.runL] at hu
      obtain ⟨s1, e1, e2⟩ := Option.bind_eq_some_iff.mp hu
      cases hq : procCall? T i.fst with
      | some q =>
          have hw : segWalk T cs F ss (i :: is)
              = segWalk T cs (startF (callFacts cs F ss q.2.1)) SSt.start is := by
            simp only [segWalk, hq]
          have e1' : procStep q.1 q.2.1 q.2.2 s = some s1 := by
            simpa only [Isa.withProcs, hq] using e1
          obtain ⟨r, hr⟩ := procStep_retRes e1'
          have hsh : shadowCall? i.fst ≠ none := by
            intro hn
            simp [procCall?, hn] at hq
          have hF1 : ∀ g ∈ startF (callFacts cs F ss q.2.1),
              g.holds s1.prog.base.reg.lvm s1.prog.base.larr s1.prog.base.cf s1.prog.base.of :=
            startF_holds (callFacts_sound hF hs fun q' hq' => by
              rw [hr]; exact retRes_lvm_ne r s hq')
          rw [hw] at hb ⊢
          obtain ⟨ih1, ih2⟩ := segWalk_sound T cs P is _ _ _ _ _ _ _ _ u (holds_start s1) hF1 e2 hb
          refine ⟨⟨idxOkB_of_shadowCall hsh s, fun s1' e1'' => ?_⟩, ih2⟩
          rw [e1] at e1''
          cases e1''
          exact ih1
      | none =>
          have e1' : evalInstrPMemF P i s = some s1 := by
            rwa [Isa.withProcs_step_of_none _ T P i s hq] at e1
          have hstep := symStep_sound P i ss V A C O Z s hs
          cases h1 : symStep i ss with
          | ok ss1 g1 =>
              rw [h1] at hstep
              obtain ⟨hg1, hH1, -⟩ := hstep.1 s1 e1'
              have hF1 : ∀ g ∈ F ++ g1.flatMap guardW64, g.holds V A C O := by
                intro g hg
                rcases List.mem_append.mp hg with hg | hg
                · exact hF g hg
                · exact guardW64_holds hg1 g hg
              by_cases hob : oblsOk (F ++ g1.flatMap guardW64) (oblOf i ss) = true
              · have hw : segWalk T cs F ss (i :: is)
                    = segWalk T cs (F ++ g1.flatMap guardW64) ss1 is := by
                  simp only [segWalk, hq, h1, ite_eq_left hob]
                rw [hw] at hb ⊢
                obtain ⟨ih1, ih2⟩ := segWalk_sound T cs P is _ ss1 V A C O Z s1 u hH1 hF1 e2 hb
                refine ⟨⟨(oblOf_iff hs.1 i).mpr (oblsOk_sound hob hF1), fun s1' e1'' => ?_⟩, ih2⟩
                rw [e1] at e1''
                cases e1''
                exact ih1
              · exact absurd (by simp only [segWalk, hq, h1, ite_eq_right hob]) hb
          | fail =>
              rw [h1] at hstep
              simp only [SOut.Desc] at hstep
              rw [hstep] at e1'
              cases e1'
          | unk => exact absurd (by simp only [segWalk, hq, h1]) hb

/-- A label at the head of a stretch is skipped by the segmented walk. -/
theorem segWalk_label {T : ProcTable} {cs : List IdxFact} {F : List SFact} {ss : SSt}
    {i : LinstrRM} (h : isLbl i = true) (is : List LinstrRM) :
    segWalk T cs F ss (i :: is) = segWalk T cs F ss is := by
  obtain ⟨x, tag⟩ := i
  have hx : loadStruct? x = none ∧ storeStruct? x = none := by
    cases x <;> simp_all [isLbl, loadStruct?, storeStruct?]
  have ho : oblOf (x, tag) ss = [] := by
    cases tag <;> simp [oblOf, hx.1, hx.2]
  have hq : procCall? T x = none := by
    cases x <;> simp_all [isLbl, procCall?, shadowCall?]
  simp only [segWalk, hq, symStep_label h, ho, oblsOk, List.all_nil, ite_true, List.flatMap_nil,
    List.append_nil]

theorem segWalk_entry {T : ProcTable} {cs : List IdxFact} {F : List SFact} {B : List LinstrRM}
    {b : Block} {Tm : Term} {p : Nat} (hp : EntryAt B b p) (hle : p ≤ bstopOf Tm b) :
    segWalk T cs F SSt.start ((B.drop p).take (bstopOf Tm b - p)) =
      segWalk T cs F SSt.start (bodyAt B b Tm) := by
  rcases hp with rfl | ⟨rfl, x, hx, hl⟩
  · rfl
  · unfold bodyAt
    rw [take_cons B (by omega) hx, segWalk_label hl]

/-- **The check of block `k` with calls**: a block ending in `Lret`, or whose segmented walk
    goes through a step that always fails, is accepted; otherwise the walk is not rejected
    and the facts of the successors follow from the facts of the last segment. The
    candidates after a call are the facts of the annotation. -/
def blockInvOkP (T : ProcTable) (ann : List (List IdxFact)) (B : List LinstrRM) (G : CFG)
    (k : Nat) : Bool :=
  match (G.blk k).term with
  | .ret => true
  | Tm =>
      match segWalk T ann.flatten (startF (annAt ann k)) SSt.start (bodyAt B (G.blk k) Tm) with
      | .fail => true
      | .bad => false
      | .ok F ss => termInvOk ann F ss Tm B[(G.blk k).stop - 1]?

/-- **The bounds-invariant check with calls** of the body `B` under the procedure table `T`
    and the annotation `ann`, from the entry facts `entry`: the body has a control-flow
    graph, every block passes `blockInvOkP`, and the entry facts give the facts of block
    `0`. -/
def idxInvCheckPB (T : ProcTable) (entry : List IdxFact) (ann : List (List IdxFact))
    (B : List LinstrRM) : Bool :=
  match cfgOf (B.map Prod.fst) with
  | some G =>
      (List.range G.blocks.size).all (blockInvOkP T ann B G) &&
        (annAt ann 0).all fun f => entails (startF entry) (f.toS STerm.reg SArr.cell)
  | none => false

section Sound

variable {T : ProcTable} {ann : List (List IdxFact)} {B : List LinstrRM} {G : CFG}
  {fn : String}

/-- The invariant up to the measure `N` for runs of `x86Isa.withProcs T`: a halting run
    from a block entry at which the facts of the block hold is in bounds. -/
def InvAtP (T : ProcTable) (ann : List (List IdxFact)) (B : List LinstrRM) (G : CFG)
    (fn : String) (N : Nat) : Prop :=
  ∀ (fuel k : Nat) (s t : LstateMF),
    fuel * (G.blocks.size + 1) + (G.blocks.size - k) < N → k < G.blocks.size →
    EntryAt B (G.blk k) s.prog.base.reg.lpc → s.prog.lfn = fn →
    (∀ f ∈ annAt ann k, f.holds s.prog.base.reg.lvm s.prog.base.larr) →
    (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B) fuel s = some t →
    (x86Isa.withProcs T).RunIdxOk (singletonProgM fn B) fuel s

theorem inv_stepP (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOkP T ann B G k = true) {N : Nat}
    (ih : InvAtP T ann B G fn N) : InvAtP T ann B G fn (N + 1) := by
  intro fuel k s t hN hk hE hfn hinv hrun
  have F := blockFacts hG hk
  have hpl := stepPlain_withProcs T
  obtain ⟨hs1, hle⟩ := entry_le hG hk hE
  have hplain := body_plain hG hk hs1
  obtain ⟨u, f, hf, hu, hru⟩ :=
    fuel_runL_at hpl _ _ s t fuel hfn (drop_split B hle) hplain hrun
  obtain ⟨hul, hup⟩ := runL_frame_at hpl _ s u hplain hu
  have hbstop : bstopOf (G.blk k).term (G.blk k) ≤ B.length := by
    unfold bstopOf; split <;> have := F.le <;> simp at this <;> omega
  simp only [List.length_take, List.length_drop] at hup hf
  have hupc : u.prog.base.reg.lpc = bstopOf (G.blk k).term (G.blk k) := by
    rw [hup]; omega
  have hul' : u.prog.lfn = fn := hul.trans hfn
  have hlt : (G.blk k).stop - 1 < B.length := by have := F.le; have := F.lt; simp at *; omega
  obtain ⟨z, hz⟩ : ∃ z, B[(G.blk k).stop - 1]? = some z :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have hterm := F.term
  rw [List.getElem?_map, hz, Option.map_some] at hterm
  -- a block ending in `Lret` is never left by a halting run
  by_cases hret : (G.blk k).term = .ret
  · rcases termOk_spec hterm with ⟨_, hT, _⟩ | ⟨_, _, _, hT, _⟩ | ⟨_, _, _, _, hT, _⟩ | ⟨_, hzr⟩
    all_goals try (rw [hret] at hT; cases hT)
    have hupc2 : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by
      rw [hupc]; simp [bstopOf, hret]
    obtain ⟨_, _, _, he, _⟩ :=
      run_inv_at hru (by rw [findInstrMem_single hul', hupc2, hz])
    obtain ⟨zi, zt⟩ := z
    simp only at hzr
    subst hzr
    rw [withProcs_ret] at he
    cases he
  -- the segmented walk of the block body
  have hbk := hb k hk
  unfold blockInvOkP at hbk
  have hbk' : (match segWalk T ann.flatten (startF (annAt ann k)) SSt.start
      (bodyAt B (G.blk k) (G.blk k).term) with
      | .fail => true
      | .bad => false
      | .ok F ss => termInvOk ann F ss (G.blk k).term B[(G.blk k).stop - 1]?) = true := by
    revert hbk
    cases hT : (G.blk k).term with
    | ret => exact absurd hT hret
    | _ => exact id
  have hF0 := startF_holds (A := s.prog.base.larr) (C := s.prog.base.cf) (O := s.prog.base.of)
    hinv
  have hnb : segWalk T ann.flatten (startF (annAt ann k)) SSt.start
      ((B.drop s.prog.base.reg.lpc).take
        (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) ≠ .bad := by
    rw [segWalk_entry hE hle]
    intro hS
    rw [hS] at hbk'
    cases hbk'
  obtain ⟨hlS, F', ss, V', A', C', O', Z', hS, hH, hF'⟩ :=
    segWalk_sound T ann.flatten (singletonProgM fn B) _ _ SSt.start _ _ _ _ _ s u
      (holds_start s) hF0 hu hnb
  rw [segWalk_entry hE hle] at hS
  rw [hS] at hbk'
  have hti : termInvOk ann F' ss (G.blk k).term B[(G.blk k).stop - 1]? = true := hbk'
  have hokJ : ∀ f0, (x86Isa.withProcs T).RunIdxOk (singletonProgM fn B) f0 u →
      (x86Isa.withProcs T).RunIdxOk (singletonProgM fn B) (((B.drop s.prog.base.reg.lpc).take
        (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)).length + f0) s :=
    fun f0 h0 => runIdxOk_of_runL_at hpl _ _ s u f0 hfn (drop_split B hle) hplain hu hlS h0
  simp only [List.length_take, List.length_drop] at hokJ
  rw [hf]
  have hlen : min (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)
      (B.length - s.prog.base.reg.lpc) = bstopOf (G.blk k).term (G.blk k)
        - s.prog.base.reg.lpc := by omega
  rw [hlen] at hokJ
  rw [hlen]
  apply hokJ
  have hfle : f ≤ fuel := by omega
  obtain ⟨zi, zt⟩ := z
  rw [hz] at hti
  simp only at hterm
  rcases termOk_spec hterm with ⟨nx, hT, _, hnx⟩ | ⟨tg, x, l, hT, hzi, htg, hl⟩ |
      ⟨tg, nx, c, l, hT, hzi, htg, hl, hnx⟩ | ⟨hT, _⟩
  · -- fall through
    have hw : u.prog.base.reg.lpc = (G.blk k).stop := by rw [hupc, hT]; rfl
    rw [hT] at hti
    cases nx with
    | none =>
        have e1 := (stop_next hG hk).1 hnx.symm
        exact runIdxOk_halt_at _ (by rw [findInstrMem_single hul', hw, e1]; simp) f
    | some j =>
        obtain ⟨hj, hjlt, e1⟩ := (stop_next hG hk).2 j hnx.symm
        subst hj
        exact ih f (k + 1) u t (measure_le hN hfle hk) hjlt (Or.inl (hw.trans e1)) hul'
          (succOk_sound hti hF' hH) hru
  · -- jump
    subst hzi
    rw [hT] at hti
    have hw : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [hupc, hT]; rfl
    have hfetch : findInstrMem (singletonProgM fn B) u.prog = some (.Lgoto (x, l), zt) := by
      rw [findInstrMem_single hul', hw, hz]
    obtain ⟨f1, u1, hf1, he, hr1⟩ := run_inv_at hru hfetch
    have he0 := he
    rw [Isa.step_goto] at he
    by_cases hx : x = (singletonProgM fn B).lfn
    · rw [ite_eq_left hx, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      subst hf1
      exact runIdxOk_step_at hfetch (idxOkB_goto _ _ _ _) he0
        (ih f1 tg _ t (measure_lt hN (show f1 + 1 ≤ fuel by omega)) htg
          (Or.inr ⟨rfl, label_at hl⟩) hul' (succOk_sound hti hF' hH) hr1)
    · rw [ite_eq_right hx] at he
      cases he
  · -- branch
    subst hzi
    rw [hT] at hti
    simp only [termInvOk, Bool.and_eq_true] at hti
    obtain ⟨htk, hnt⟩ := hti
    have hw : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [hupc, hT]; rfl
    have hfetch : findInstrMem (singletonProgM fn B) u.prog = some (.Lcond c l, zt) := by
      rw [findInstrMem_single hul', hw, hz]
    obtain ⟨f1, u1, hf1, he, hr1⟩ := run_inv_at hru hfetch
    have he0 := he
    subst hf1
    have hdec := decC_eq hH c
    have hce : (x86Isa.withProcs T).condEval u c = decC u c := rfl
    rw [Isa.step_cond, hce] at he
    have hstop : 0 < (G.blk k).stop := by have := F.lt; omega
    by_cases hd : decC u c = true
    · rw [ite_eq_left hd, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have hE' : ∀ g ∈ F' ++ edgeFacts (symDec ss c) true, g.holds V' A' C' O' := by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hF' g hg
        · exact edgeFacts_sound (hdec.symm.trans hd) g hg
      exact runIdxOk_step_at hfetch (idxOkB_cond _ _ _ _) he0
        (ih f1 tg _ t (measure_lt hN (show f1 + 1 ≤ fuel by omega)) htg
          (Or.inr ⟨rfl, label_at hl⟩) hul' (succOk_sound htk hE' hH) hr1)
    · rw [ite_eq_right hd] at he
      simp only [Option.some.injEq] at he
      subst he
      have hE' : ∀ g ∈ F' ++ edgeFacts (symDec ss c) false, g.holds V' A' C' O' := by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hF' g hg
        · exact edgeFacts_sound (by rw [← hdec]; simpa using hd) g hg
      refine runIdxOk_step_at hfetch (idxOkB_cond _ _ _ _) he0 ?_
      have hw1 : u.prog.base.reg.lpc + 1 = (G.blk k).stop := by omega
      cases nx with
      | none =>
          have e1 := (stop_next hG hk).1 hnx.symm
          exact runIdxOk_halt_at _ (by
            rw [findInstrMem_single (s := ⟨⟨u.prog.base.nextPc, u.prog.lfn⟩, u.zf⟩) hul']
            show B[u.prog.base.reg.lpc + 1]? = none
            rw [hw1, e1]; simp) f1
      | some j =>
          obtain ⟨hj, hjlt, e1⟩ := (stop_next hG hk).2 j hnx.symm
          subst hj
          exact ih f1 (k + 1) _ t (measure_le hN (show f1 ≤ fuel by omega) hk) hjlt
            (Or.inl (hw1.trans e1)) hul' (succOk_sound hnt hE' hH) hr1
  · exact absurd hT hret

theorem invAt_allP (hG : cfgOf (B.map Prod.fst) = some G)
    (hb : ∀ k < G.blocks.size, blockInvOkP T ann B G k = true) : ∀ N, InvAtP T ann B G fn N
  | 0 => fun _ _ _ _ hN => absurd hN (Nat.not_lt_zero _)
  | N + 1 => inv_stepP hG hb (invAt_allP hG hb N)

end Sound

/-- **Soundness of the bounds check with calls.** If `idxInvCheckPB T entry ann B` accepts,
    every halting run of `x86Isa.withProcs T` on the singleton program over `B` from a
    state at pc `0` of that function whose registers satisfy the entry facts is in
    bounds. -/
theorem runIdxOk_of_idxInvCheckPB {T : ProcTable} {entry : List IdxFact}
    {ann : List (List IdxFact)} {B : List LinstrRM} (h : idxInvCheckPB T entry ann B = true)
    (fn : String) (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    (x86Isa.withProcs T).RunIdxOk (singletonProgM fn B) fuel s := by
  unfold idxInvCheckPB at h
  split at h
  · rename_i G hG
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
    obtain ⟨hb, h0⟩ := h
    by_cases hB : B.map Prod.fst = []
    · have hBn : B = [] := by simpa using hB
      subst hBn
      exact runIdxOk_halt_at _ (by rw [findInstrMem_single hfn]; simp) fuel
    obtain ⟨hpos, hs0⟩ := cfgOf_start_zero hG hB
    have hF := startF_holds (A := s.prog.base.larr) (C := s.prog.base.cf)
      (O := s.prog.base.of) hent
    have hinv : ∀ f ∈ annAt ann 0, f.holds s.prog.base.reg.lvm s.prog.base.larr :=
      fun f hf => (IdxFact.toS_holds STerm.reg SArr.cell f).mp (entails_sound hF _ (h0 f hf))
    exact invAt_allP hG hb _ fuel 0 s t (Nat.lt_succ_self _) hpos
      (Or.inl (hpc.trans hs0.symm)) hfn hinv hrun
  · cases h

/-- **A halting run of the reference body is a run of the bounds-checked instruction set.**
    If `idxInvCheckPB T entry ann B` accepts, a halting run of `x86Isa.withProcs T` on the
    singleton program over `B` from a state at pc `0` of that function whose registers
    satisfy the entry facts is a halting run of `x86IsaK.withProcs T`, to the same state. -/
theorem refRun_checked {T : ProcTable} {entry : List IdxFact} {ann : List (List IdxFact)}
    {B : List LinstrRM} (h : idxInvCheckPB T entry ann B = true) (fn : String)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    (x86IsaK.withProcs T).lsemFuelMemF (singletonProgM fn B) fuel s = some t := by
  rw [x86IsaK_withProcs_lsemFuelMemF]
  exact (x86Isa.withProcs T).lsemFuelMemFk_of_runIdxOk true _ fuel s t hrun
    (runIdxOk_of_idxInvCheckPB h fn s t hfn hpc hent fuel hrun)

/-! ## 5. Annotation by restriction to a fixed point -/

/-- The segments of a stretch under the procedure table `T` for the annotation: the index
    obligations, the symbolic states at the end of every segment (before each call and at
    the end) and the final symbolic state, `none` when a step fails or is outside the
    fragment. -/
def segScan (T : ProcTable) : SSt → List LinstrRM →
    List OwnedLprogTVChecked.SObl × List SSt × Option SSt
  | ss, [] => ([], [ss], some ss)
  | ss, i :: is =>
      match procCall? T i.fst with
      | some _ =>
          let r := segScan T SSt.start is
          (r.1, ss :: r.2.1, r.2.2)
      | none =>
          match symStep i ss with
          | .ok ss1 _ =>
              let r := segScan T ss1 is
              (oblOf i ss ++ r.1, r.2.1, r.2.2)
          | _ => (oblOf i ss, [], none)

/-- The registers an index obligation, a branch condition or an entry fact of `B` reads,
    over the segments of its blocks: the candidates of the annotation. -/
def annRegsP (T : ProcTable) (entry : List IdxFact) (B : List LinstrRM) (G : CFG) :
    List String :=
  let fromEntry := entry.flatMap factRegs
  let fromBlocks := (List.range G.blocks.size).flatMap fun k =>
    let r := segScan T SSt.start (bodyAt B (G.blk k) (G.blk k).term)
    r.1.flatMap (·.1.vars) ++
      match r.2.2, B[(G.blk k).stop - 1]? with
      | some ss, some (.Lcond c _, _) => (symDec ss c).vars
      | _, _ => []
  (fromEntry ++ fromBlocks).eraseDups

/-- The array lengths of the index obligations of the blocks of `B`, over their
    segments. -/
def oblLensP (T : ProcTable) (B : List LinstrRM) (G : CFG) : List Nat :=
  (List.range G.blocks.size).flatMap fun k =>
    (segScan T SSt.start (bodyAt B (G.blk k) (G.blk k).term)).1.map (·.2)

/-- The immediates at width `64` that a segment of a block of `B` leaves in a register of
    `rs`. -/
def seedImmsP (T : ProcTable) (B : List LinstrRM) (G : CFG) (rs : List String) : List Nat :=
  (List.range G.blocks.size).flatMap fun k =>
    (segScan T SSt.start (bodyAt B (G.blk k) (G.blk k).term)).2.1.flatMap fun ss =>
      rs.filterMap fun r =>
        match ss.regs r with
        | .immW w n => if w = 64 then some n else none
        | _ => none

/-- The candidates of `cs` at which the mask `m` is `true`, in the order of `cs`. -/
def maskFacts (cs : Array IdxFact) (m : Array Bool) : List IdxFact :=
  ((Array.range cs.size).filterMap fun i => if m.getD i false then cs[i]? else none).toList

/-- The candidates of `cs` at which some mask of `ms` is `true`, each once, in the order of
    `cs`. -/
def maskUnion (cs : Array IdxFact) (ms : Array (Array Bool)) : List IdxFact :=
  ((Array.range cs.size).filterMap fun i =>
    if ms.any (fun m => m.getD i false) then cs[i]? else none).toList

/-- One restriction pass with calls, on masks over the candidates `cs`, one mask per block:
    for every block in order, the candidates of the mask of each successor that do not
    follow from the facts of the last segment of the block (with the condition of the edge)
    are dropped. The facts of a block are the candidates of its mask (`maskFacts`), and the
    candidates after a call are those of some mask (`maskUnion`). -/
def annPassP (T : ProcTable) (B : List LinstrRM) (G : CFG) (cs : Array IdxFact)
    (ms : Array (Array Bool)) : Array (Array Bool) :=
  (List.range G.blocks.size).foldl (fun ms k =>
    match segWalk T (maskUnion cs ms) (startF (maskFacts cs (ms.getD k #[]))) SSt.start
        (bodyAt B (G.blk k) (G.blk k).term) with
    | .ok F ss =>
        let keep (F' : List SFact) (ms : Array (Array Bool)) (j : Nat) :=
          ms.modify j fun m => (Array.range m.size).map fun i =>
            m.getD i false && entails F' ((cs.getD i default).toS ss.regs ss.arrs)
        match (G.blk k).term with
        | .fall (some j) => keep F ms j
        | .goto tg => keep F ms tg
        | .cond tg nx =>
            match B[(G.blk k).stop - 1]? with
            | some (.Lcond c _, _) =>
                let ms := keep (F ++ edgeFacts (symDec ss c) true) ms tg
                match nx with
                | some j => keep (F ++ edgeFacts (symDec ss c) false) ms j
                | none => ms
            | _ => ms
        | _ => ms
    | _ => ms) ms

/-- Restriction passes `annPassP` until a pass changes no mask, at most `fuel` of them. A pass
    only drops candidates, so the masks reach a fixed point within one pass per candidate
    and block. -/
def annFixP (T : ProcTable) (B : List LinstrRM) (G : CFG) (cs : Array IdxFact) :
    Nat → Array (Array Bool) → Array (Array Bool)
  | 0, ms => ms
  | fuel + 1, ms =>
      let ms' := annPassP T B G cs ms
      if ms' == ms then ms else annFixP T B G cs fuel ms'

/-- **The annotation by restriction with calls**: `IdxInvCheck.idxAnnot` with the candidate
    registers, bounds and passes taken over the segments of the blocks (`segScan`,
    `segWalk`), the facts of each block held as a mask over the candidates and the passes
    stopped at a fixed point (`annFixP`). `idxInvCheckPB` checks the result. -/
def idxAnnotP (T : ProcTable) (entry : List IdxFact) (B : List LinstrRM) :
    List (List IdxFact) :=
  match cfgOf (B.map Prod.fst) with
  | some G =>
      let rs := annRegsP T entry B G
      let bs := ((entry.filterMap fun | .le _ b => some b | _ => none)
        ++ oblLensP T B G ++ seedImmsP T B G rs).eraseDups
      let cs := (IdxInvCheck.annCands rs bs).toArray
      let m0 := (Array.range G.blocks.size).map fun k =>
        if k = 0 then cs.map fun f => entails (startF entry) (f.toS STerm.reg SArr.cell)
        else Array.replicate cs.size true
      ((annFixP T B G cs (G.blocks.size * cs.size + 1) m0).map (maskFacts cs)).toList
  | none => []

/-! ## 6. The linked image theorem at the bounds-checked instruction set -/

section Linked

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr Params Shape)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeSig CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW
  (printedAddrCWB imgGateCBW bitsDeadB liveW) in
/-- **The linked image theorem at the bounds-checked instruction set**: a halting run of the
    image of a calling body
    of the wide class `printedAddrCWB`, under the gate `imgGateCBW`, with the width analysis dead
    at its calls and its return (`bitsDeadB`), from a position where `liveW` is false, is a run
    through calls of the program its linked bytes decode to, at the bounds-checked instruction
    set. -/
theorem haltsC_of_linkedChecksKW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    (r : CatCrypt.Crypto.SecureCompilation.CT.DoitRegime) {q : List RInstr} {c : CalleeSig}
    (hX : CalleeSpec (Callee.runOf r q) c) (hq : ∀ tg, RInstr.call tg ∉ q) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    (hroom : ∀ ret sA, sA.regs "%rsp" = rsp → room (entryOf ret sA))
    {ds : List PhysAbiShape.DShape} (hcls : printedAddrCWB G body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body
      = some ds)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (symBase : String → Option Int) {cb : List (BitVec 8)} {prog : List RInstr}
    (hcb : LprogBytesDecode.decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : LprogBytesLinkReloc.branchOKReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length 0
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = true)
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {D : DeadTab} (hbits : bitsDeadB frame D body = true)
    (hdead : callDeadB c (fun _ => (res, c.args)) D.dead body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : ProcTable} {f fn : String} (hT : T f = some pr)
    (hshape : siteShapeB f (fun _ => (res, c.args))
      (callImg slotArr (fun _ => (res, c.args)) body) = true)
    (hseg : deadSegB D (callImg slotArr (fun _ => (res, c.args)) body) = true)
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (n : Nat) {s t : LstateMF}
    (hrun : (x86IsaK.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr (fun _ => (res, c.args)) body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    LprogBytesDecode.decodeLprog (LprogBytes.encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ LprogBytesLink.shiftProg prog.length q)
      ∧ ∃ sA', RInstrSemantics.HaltsC aMachine (prog ++ LprogBytesLink.shiftProg prog.length q)
          (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
        ∧ Fin t sA' :=
  ImageAddrCallW.haltsC_of_linkedChecksOne hsep hphys hgate hsites r hX hq hcls hshapes hfr
    symBase hcb hne hbr hP hbits hflags hcond x86IsaK_checked (deadSteps_x86K hseg) hfin hFin
    (fun _ _ _ hg _ hb => siteStep_word hsep hphys hX hw hS hF hroom hdead hb
      (glue_regArgs (sitesOf_of_siteShapeB hshape hT) hw.wordOnly hw.wordRet hg))
    n hrun hfn hlen hL hI0 hA

end Linked

end CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall
