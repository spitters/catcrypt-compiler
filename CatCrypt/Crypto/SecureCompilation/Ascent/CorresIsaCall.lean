/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCfg

/-!
# The procedure-specification rule for calls over an instruction set

`Isa.withCalls` of `VIR.LprogIsa` gives `Lcall` and `Lret` a step: a call through the stack
pushes the return address below the stack pointer and jumps to the label of the callee, and
a return pops it into the program counter. A callee is a labelled region of the body of the
program `P` that ends in an `Lret`.

A procedure specification `ProcSpec isa P l kret SR Pre f Frame B` is the statement about
the callee alone: from every state at the label `l` related by `SR` to an abstract state `a`
satisfying `Pre`, a run of at most `B` steps of `P` reaches the counter `kret` in a state
related to `f a`, with the frame relation `Frame` between the two states and the return
address contract `RetFrame` (the stack pointer and the memory cell it addresses hold their
entry values).

The rule `steps_call` uses a specification at a call site. At a counter `k` holding
`Lcall none (P.lfn, l)`, when the state after the call step (`callEntry`) satisfies the
relation and the precondition of the callee, the call step, the run of the callee and the
return step form one segment `IsaCfg.Steps` of at most `B + 2` steps. It ends at the counter
`k + 1` in the state `retState` of a callee exit state `m₂`: the state `m₂`, related to `f a`
and framed against the callee entry, with the stack pointer and the counter of the caller
restored. The segment is in the form the verification conditions of
`IsaCfg.corresIsa_of_labels_floyd` take, and composes with other segments by `Steps.trans`.

## Main results

* `RetFrame`, `ProcSpec`: the return address contract and the procedure specification.
* `callEntry`, `retState`: the states after the call step and after the return step.
* `steps_call_entry`, `steps_ret`: the call step and the return step as segments.
* `steps_call`: the procedure-specification rule.
* `steps_one_of_not_call`: a step of the underlying instruction set as a segment of the
  instruction set with calls.
* `procSpec_mono`: a specification holds at every larger step bound.
* `isCall_of_isLopn`, `corresIsa_withCalls_iff`, `corresIsaRun_withCalls_iff`: an `Lopn` is
  no call, and on a program without calls the correspondence at `isa.withCalls` is the
  correspondence at `isa`.
* `steps_of_lsemFuelMemF`: a run of the interpreter with fuel `k` is a segment of at most
  `k` steps to a halted state.
* `steps_append_withCalls`: a segment of a body without calls is a segment of
  `isa.withCalls` on every extension of the body on which the steps agree.
* `findLabelMem_snoc_ret`, `step_snoc_ret_of_isCtl`: a return appended to a body changes no
  label search and no step of a control instruction.
* `steps_snoc_ret_prefix`, `steps_snoc_ret`: a run of a body without calls that ends at the
  counter after its last instruction is, on the body followed by a return, a segment to the
  return and, with the return step, a segment to the return address.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

namespace IsaCall

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LLabel LabelKind LOperand
  LinstrR)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (LstateN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag LstateM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM findInstrMem
  findLabelMem evalJumpMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa isCall retAddr pushRet popRet)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (isCtl ctlStep)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (IsLopn singletonProgM)

/-! ## States at the two ends of a call -/

/-- The state after the step of a call through the stack from `m`, whose stack pointer
    register `sp` holds `v`, to a label declared at index `q`: the return address is pushed
    and the counter is `q + 1`. -/
def callEntry (sp : String) (v : BitVec 64) (q : Nat) (m : LstateMF) : LstateMF :=
  goto (pushRet sp v m) (q + 1)

/-- The state after the return step from the callee exit state `m₂` to the counter `k` of
    the caller: `m₂` with the stack pointer register `sp` holding `v` and the counter `k`. -/
def retState (sp : String) (v : BitVec 64) (k : Nat) (m₂ : LstateMF) : LstateMF :=
  { m₂ with prog := { m₂.prog with base := (m₂.prog.base.setReg sp v).setLpc k } }

@[simp] theorem callEntry_lfn (sp : String) (v : BitVec 64) (q : Nat) (m : LstateMF) :
    (callEntry sp v q m).prog.lfn = m.prog.lfn := rfl

@[simp] theorem callEntry_lpc (sp : String) (v : BitVec 64) (q : Nat) (m : LstateMF) :
    (callEntry sp v q m).prog.base.lpc = q + 1 := rfl

/-- The call step changes no register other than the stack pointer. -/
theorem callEntry_lvm_of_ne (sp : String) (v : BitVec 64) (q : Nat) (m : LstateMF)
    {r : String} (hr : r ≠ sp) :
    (callEntry sp v q m).prog.base.reg.lvm r = m.prog.base.reg.lvm r := by
  simp [callEntry, goto, pushRet, LstateM.setLpc, LstateM.setReg, LstateN.setReg, hr]

/-- After the call step the stack pointer holds `v - 8`. -/
theorem callEntry_lvm_sp (sp : String) (v : BitVec 64) (q : Nat) (m : LstateMF) :
    (callEntry sp v q m).prog.base.reg.lvm sp = ⟨64, v - 8⟩ := by
  simp [callEntry, goto, pushRet, LstateM.setLpc, LstateM.setReg, LstateN.setReg]

theorem callEntry_getW_sp (sp : String) (v : BitVec 64) (q : Nat) (m : LstateMF) :
    (callEntry sp v q m).prog.base.reg.getW sp 64 = some (v - 8) := by
  unfold LstateN.getW
  rw [callEntry_lvm_sp]
  simp

/-- After the call step the memory cell the stack pointer addresses holds the return
    address. -/
theorem callEntry_lmem_sp (sp : String) (v : BitVec 64) (q : Nat) (m : LstateMF) :
    (callEntry sp v q m).prog.base.lmem sp (v - 8).toInt = retAddr m := by
  simp [callEntry, goto, pushRet, LstateM.setLpc, LstateM.setReg, LstateM.storeMemC]

@[simp] theorem retState_lfn (sp : String) (v : BitVec 64) (k : Nat) (m₂ : LstateMF) :
    (retState sp v k m₂).prog.lfn = m₂.prog.lfn := rfl

@[simp] theorem retState_lpc (sp : String) (v : BitVec 64) (k : Nat) (m₂ : LstateMF) :
    (retState sp v k m₂).prog.base.lpc = k := rfl

/-- The return step changes no register other than the stack pointer. -/
theorem retState_lvm_of_ne (sp : String) (v : BitVec 64) (k : Nat) (m₂ : LstateMF)
    {r : String} (hr : r ≠ sp) :
    (retState sp v k m₂).prog.base.reg.lvm r = m₂.prog.base.reg.lvm r := by
  simp [retState, LstateM.setLpc, LstateM.setReg, LstateN.setReg, hr]

/-- After the return step the stack pointer holds `v`. -/
theorem retState_lvm_sp (sp : String) (v : BitVec 64) (k : Nat) (m₂ : LstateMF) :
    (retState sp v k m₂).prog.base.reg.lvm sp = ⟨64, v⟩ := by
  simp [retState, LstateM.setLpc, LstateM.setReg, LstateN.setReg]

/-! ## The procedure specification -/

/-- **The return address contract** of a callee between its entry state `m` and its exit
    state `m'`: the stack pointer register `sp` holds at the exit the word `v` it holds at
    the entry, and the memory cell of `sp` at `v`, which holds the return address, is
    unchanged. -/
def RetFrame (sp : String) (m m' : LstateMF) : Prop :=
  ∀ v : BitVec 64, m.prog.base.reg.getW sp 64 = some v →
    m'.prog.base.reg.getW sp 64 = some v ∧
      m'.prog.base.lmem sp v.toInt = m.prog.base.lmem sp v.toInt

/-- **A procedure specification.** From every state at the label `l` of `P` related by `SR`
    to an abstract state `a` satisfying `Pre`, a run of at most `B` steps of `P` reaches the
    counter `kret` in a state related to `f a`; the entry and exit states are related by
    `Frame` and satisfy the return address contract `RetFrame` at the stack pointer of
    `isa`. -/
def ProcSpec {AState : Type} (isa : Isa) (P : LprogM) (l : LLabel) (kret : Nat)
    (SR : LstateMF → AState → Prop) (Pre : AState → Prop) (f : AState → AState)
    (Frame : LstateMF → LstateMF → Prop) (B : Nat) : Prop :=
  ∀ m a, atLabel P l m → SR m a → Pre a →
    ∃ n m', n ≤ B ∧ Steps isa P n m m' ∧ atPc P kret m' ∧ SR m' (f a) ∧ Frame m m' ∧
      RetFrame isa.sp m m'

/-- A procedure specification holds at every larger step bound. -/
theorem procSpec_mono {AState : Type} {isa : Isa} {P : LprogM} {l : LLabel} {kret : Nat}
    {SR : LstateMF → AState → Prop} {Pre : AState → Prop} {f : AState → AState}
    {Frame : LstateMF → LstateMF → Prop} {B B' : Nat}
    (h : ProcSpec isa P l kret SR Pre f Frame B) (hle : B ≤ B') :
    ProcSpec isa P l kret SR Pre f Frame B' := by
  intro m a hat hSR hPre
  obtain ⟨n, m', hn, hrest⟩ := h m a hat hSR hPre
  exact ⟨n, m', Nat.le_trans hn hle, hrest⟩

/-! ## The call step, the return step and the rule -/

/-- A step of `isa` on an instruction other than a call or a return is one step of the
    program under `isa.withCalls`. -/
theorem steps_one_of_not_call (isa : Isa) {P : LprogM} {k : Nat} {s t : LstateMF}
    {i : LinstrRM} (hat : atPc P k s) (hi : P.body[k]? = some i)
    (hc : isCall i.fst = false) (h : isa.step P i s = some t) :
    Steps isa.withCalls P 1 s t :=
  Steps.one (by
    rw [lsemStepPMemF_of_atPc isa.withCalls hat hi, isa.withCalls_step_of_not_call P i s hc, h])

/-- **The call step.** At counter `k` holding a call through the stack to the label `l`
    declared at index `q`, with the stack pointer holding `v`, one step reaches the state
    `callEntry`, which is at the label `l`. -/
theorem steps_call_entry (isa : Isa) {P : LprogM} {k q : Nat} {m : LstateMF} {l : LLabel}
    {tag : MemTag} {v : BitVec 64} (hat : atPc P k m)
    (hi : P.body[k]? = some (.Lcall none (P.lfn, l), tag))
    (hl : findLabelMem l P.body = some q)
    (hsp : m.prog.base.reg.getW isa.sp 64 = some v) :
    Steps isa.withCalls P 1 m (callEntry isa.sp v q m) ∧
      atLabel P l (callEntry isa.sp v q m) := by
  refine ⟨Steps.one ?_, q, hl, hat.1, rfl⟩
  rw [lsemStepPMemF_of_atPc isa.withCalls hat hi, isa.step_call, if_pos rfl]
  show ((m.prog.base.reg.getW isa.sp 64).bind _) = _
  rw [hsp, Option.bind_some]
  exact evalJumpMem_of_findLabelMem hl (pushRet isa.sp v m)

/-- **The return step.** At counter `kret` holding `Lret`, with the stack pointer holding
    `v - 8` and the memory cell it addresses holding the word of a counter `k` below
    `2 ^ 64`, one step reaches the state `retState` at counter `k` with the stack pointer
    holding `v`. -/
theorem steps_ret (isa : Isa) {P : LprogM} {kret k : Nat} {m₂ : LstateMF} {tag : MemTag}
    {v : BitVec 64} (hat : atPc P kret m₂) (hi : P.body[kret]? = some (.Lret, tag))
    (hsp : m₂.prog.base.reg.getW isa.sp 64 = some (v - 8))
    (hra : m₂.prog.base.lmem isa.sp (v - 8).toInt = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    Steps isa.withCalls P 1 m₂ (retState isa.sp v k m₂) ∧
      atPc P k (retState isa.sp v k m₂) := by
  refine ⟨Steps.one ?_, hat.1, rfl⟩
  rw [lsemStepPMemF_of_atPc isa.withCalls hat hi, isa.step_ret]
  show ((m₂.prog.base.reg.getW isa.sp 64).map _) = _
  rw [hsp, Option.map_some]
  simp only [popRet, retState, hra, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
    BitVec.sub_add_cancel]

/-- **The procedure-specification rule.** Let the callee at the label `l` of `P`, declared
    at index `q` and returning at the counter `kret`, satisfy the specification
    `ProcSpec isa.withCalls P l kret SR Pre f Frame B`. At a counter `k` holding
    `Lcall none (P.lfn, l)`, from a state `m` whose stack pointer holds `v` and whose state
    after the call step is related by `SR` to an abstract state `a` satisfying `Pre`, a run
    of at most `B + 2` steps (the call step, the run of the callee and the return step)
    reaches the counter `k + 1` in the state `retState isa.sp v (k + 1) m₂` of a callee exit
    state `m₂` that is related to `f a` and framed against the callee entry state. -/
theorem steps_call {AState : Type} (isa : Isa) {P : LprogM} {k q kret : Nat} {l : LLabel}
    {tag tagr : MemTag} {v : BitVec 64} {m : LstateMF} {a : AState}
    {SR : LstateMF → AState → Prop} {Pre : AState → Prop} {f : AState → AState}
    {Frame : LstateMF → LstateMF → Prop} {B : Nat}
    (hspec : ProcSpec isa.withCalls P l kret SR Pre f Frame B)
    (hret : P.body[kret]? = some (.Lret, tagr))
    (hat : atPc P k m) (hi : P.body[k]? = some (.Lcall none (P.lfn, l), tag))
    (hl : findLabelMem l P.body = some q)
    (hsp : m.prog.base.reg.getW isa.sp 64 = some v) (hk : k + 1 < 2 ^ 64)
    (hSR : SR (callEntry isa.sp v q m) a) (hPre : Pre a) :
    ∃ n m₂, n ≤ B + 2 ∧ Steps isa.withCalls P n m (retState isa.sp v (k + 1) m₂) ∧
      atPc P (k + 1) (retState isa.sp v (k + 1) m₂) ∧ SR m₂ (f a) ∧
      Frame (callEntry isa.sp v q m) m₂ := by
  obtain ⟨h1, hlab⟩ := steps_call_entry isa hat hi hl hsp
  obtain ⟨n, m₂, hn, h2, hat2, hSR2, hF, hRF⟩ := hspec _ a hlab hSR hPre
  have hRF' : RetFrame isa.sp (callEntry isa.sp v q m) m₂ := hRF
  obtain ⟨hsp2, hmem2⟩ := hRF' (v - 8) (callEntry_getW_sp isa.sp v q m)
  have hra : m₂.prog.base.lmem isa.sp (v - 8).toInt = BitVec.ofNat 64 (k + 1) := by
    rw [hmem2, callEntry_lmem_sp, retAddr, hat.2]
  obtain ⟨h3, hat3⟩ := steps_ret isa hat2 hret hsp2 hra hk
  refine ⟨1 + n + 1, m₂, by omega, (h1.trans h2).trans h3, hat3, hSR2, hF⟩

/-! ## Programs without calls -/

/-- An `Lopn` is neither a call nor a return. -/
theorem isCall_of_isLopn {i : LinstrRM} (h : IsLopn i) : isCall i.fst = false := by
  obtain ⟨d, o, s, hi⟩ := h
  rw [hi]
  rfl

section Generic

variable {A : Type}

/-- **The correspondence at the instruction set with calls.** On a program `P` in which no
    instruction is a call or a return, `CorresIsa` at `isa.withCalls` is `CorresIsa` at
    `isa`. -/
theorem corresIsa_withCalls_iff (isa : Isa) (P : LprogM)
    (hP : ∀ i ∈ P.body, isCall i.fst = false) (SR : LstateMF → A → Prop) (Pre : A → Prop)
    (fa : A → A) (fuel : Nat) :
    CorresIsa isa.withCalls P SR Pre fa fuel ↔ CorresIsa isa P SR Pre fa fuel := by
  simp only [CorresIsa, CorresM, Hax.Ascent.RefinesP, isa.withCalls_lsemFuelMemF P hP]

/-- **The per-state-fuel correspondence at the instruction set with calls.** On a program
    `P` in which no instruction is a call or a return, `CorresIsaRun` at `isa.withCalls` is
    `CorresIsaRun` at `isa`. -/
theorem corresIsaRun_withCalls_iff (isa : Isa) (P : LprogM)
    (hP : ∀ i ∈ P.body, isCall i.fst = false) (SR : LstateMF → A → Prop) (Pre : A → Prop)
    (fa : A → A) :
    CorresIsaRun isa.withCalls P SR Pre fa ↔ CorresIsaRun isa P SR Pre fa := by
  simp only [CorresIsaRun, isa.withCalls_lsemFuelMemF P hP]

end Generic

/-! ## A return appended to a body -/

/-- **A run of the interpreter as a segment.** A run with fuel `k` from `m` that returns
    `m'` is a segment of `n ≤ k` steps from `m` to `m'`, and `m'` is halted: the interpreter
    spends one unit of fuel on each step and none on finding the state halted. -/
theorem steps_of_lsemFuelMemF (isa : Isa) (P : LprogM) :
    ∀ (k : Nat) (m m' : LstateMF), isa.lsemFuelMemF P k m = some m' →
      ∃ n, n ≤ k ∧ Steps isa P n m m' ∧ Halted P m'
  | 0, m, m', h => by
      cases hf : findInstrMem P m.prog with
      | none =>
          rw [isa.lsemFuelMemF_halt P 0 m hf] at h
          cases h
          exact ⟨0, Nat.le_refl _, Steps.refl isa P m, hf⟩
      | some i => simp [Isa.lsemFuelMemF, hf] at h
  | k + 1, m, m', h => by
      cases hf : findInstrMem P m.prog with
      | none =>
          rw [isa.lsemFuelMemF_halt P _ m hf] at h
          cases h
          exact ⟨0, Nat.zero_le _, Steps.refl isa P m, hf⟩
      | some i =>
          cases hs : isa.step P i m with
          | none => simp [Isa.lsemFuelMemF, hf, hs] at h
          | some u =>
              rw [isa.lsemFuelMemF_step P k i m u hf hs] at h
              obtain ⟨n, hn, hsteps, hhalt⟩ := steps_of_lsemFuelMemF isa P k u m' h
              have h1 : Steps isa P 1 m u :=
                Steps.one (by simp only [Isa.lsemStepPMemF, hf, hs])
              exact ⟨1 + n, by omega, h1.trans hsteps, hhalt⟩

/-- A segment of `isa` on `P` is a segment of `isa'` on `P'` when every step of the first
    is a step of the second. -/
theorem steps_of_step_imp (isa isa' : Isa) {P P' : LprogM}
    (hstep : ∀ s u, isa.lsemStepPMemF P s = some u → isa'.lsemStepPMemF P' s = some u) :
    ∀ (n : Nat) (s t : LstateMF), Steps isa P n s t → Steps isa' P' n s t
  | 0, _, _, h => h
  | n + 1, s, t, h => by
      simp only [Steps, CutPoint.iter, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨u, hu, h⟩ := h
      exact ⟨u, hstep s u hu, steps_of_step_imp isa isa' hstep n u t h⟩

/-- **A segment of a body without calls under an extension of the body.** Let the body of
    `P'` be the body of `P`, in which no instruction is a call or a return, followed by
    `X`, and let the step of `isa` on every instruction of `P` be the same at `P'` and at
    `P`. A segment of `isa` on `P` is a segment of `isa.withCalls` on `P'` with the same
    number of steps. -/
theorem steps_append_withCalls (isa : Isa) {P P' : LprogM} {X : List LinstrRM}
    (hfn : P'.lfn = P.lfn) (hbody : P'.body = P.body ++ X)
    (hP : ∀ i ∈ P.body, isCall i.fst = false)
    (hstep : ∀ i ∈ P.body, ∀ s, isa.step P' i s = isa.step P i s)
    {n : Nat} {s t : LstateMF} (h : Steps isa P n s t) : Steps isa.withCalls P' n s t := by
  refine steps_of_step_imp isa isa.withCalls ?_ n s t h
  intro s u hu
  unfold Isa.lsemStepPMemF at hu ⊢
  cases hf : findInstrMem P s.prog with
  | none => rw [hf] at hu; cases hu
  | some i =>
      rw [hf] at hu
      unfold findInstrMem at hf
      split at hf
      · next hl =>
          obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hf
          have hi : i ∈ P.body := List.mem_of_getElem? hf
          have hf' : findInstrMem P' s.prog = some i := by
            unfold findInstrMem
            rw [if_pos (hl.trans hfn.symm), hbody, List.getElem?_append_left hlt]
            exact hf
          rw [hf']
          show isa.withCalls.step P' i s = some u
          rw [isa.withCalls_step_of_not_call P' i s (hP i hi), hstep i hi s]
          exact hu
      · cases hf

/-- A label search in a body followed by a return is the search in the body. -/
theorem findLabelMem_snoc_ret (l : LLabel) (B : List LinstrRM) (tag : MemTag) :
    findLabelMem l (B ++ [(.Lret, tag)]) = findLabelMem l B := by
  unfold findLabelMem VIR.JasminLsemLabeled.findLabel
  rw [List.map_append, List.findIdx?_append]
  simp [VIR.JasminLsemLabeled.isLabel]

/-- The step of a control instruction is the same on a body and on the body followed by a
    return. -/
theorem step_snoc_ret_of_isCtl (isa : Isa) (fn : String) (B : List LinstrRM) (tag : MemTag)
    (i : LinstrRM) (s : LstateMF) (h : isCtl i.fst = true) :
    isa.step (singletonProgM fn (B ++ [(.Lret, tag)])) i s =
      isa.step (singletonProgM fn B) i s := by
  rw [isa.step_ctl _ i s h, isa.step_ctl _ i s h]
  obtain ⟨w, t⟩ := i
  cases w <;> simp only [ctlStep, evalJumpMem, singletonProgM, findLabelMem_snoc_ret]
  rfl

/-- **The body of a procedure followed by its return, up to the return.** Let `B` contain
    no call and no return, let the step of `isa` on every instruction of `B` be the same on
    `B ++ [Lret]` and on `B`, and let the run of `isa` on `B` with fuel `k` from `m` return
    `m'` at the counter `B.length`. On `B ++ [Lret]` the instruction set with calls makes a
    segment of `n ≤ k` steps from `m` to `m'`, which is at the counter `B.length` of the
    return; `n` is the number of steps of the run on `B`. -/
theorem steps_snoc_ret_prefix (isa : Isa) {fn : String} {B : List LinstrRM} {tag : MemTag}
    {k : Nat} {m m' : LstateMF} (hB : ∀ i ∈ B, isCall i.fst = false)
    (hstep : ∀ i ∈ B, ∀ s, isa.step (singletonProgM fn (B ++ [(.Lret, tag)])) i s =
      isa.step (singletonProgM fn B) i s)
    (hrun : isa.lsemFuelMemF (singletonProgM fn B) k m = some m')
    (hend : atPc (singletonProgM fn B) B.length m') :
    ∃ n, n ≤ k ∧ Steps isa.withCalls (singletonProgM fn (B ++ [(.Lret, tag)])) n m m' ∧
      atPc (singletonProgM fn (B ++ [(.Lret, tag)])) B.length m' := by
  obtain ⟨n, hn, hsteps, _⟩ := steps_of_lsemFuelMemF isa _ k m m' hrun
  exact ⟨n, hn, steps_append_withCalls isa (P := singletonProgM fn B)
    (P' := singletonProgM fn (B ++ [(LinstrR.Lret, tag)])) (X := [(LinstrR.Lret, tag)]) rfl rfl
    hB hstep
    hsteps, hend⟩

/-- **The body of a procedure followed by its return.** Under the hypotheses of
    `steps_snoc_ret_prefix`, when the stack pointer of `m'` holds `v - 8` and the memory
    cell it addresses holds the word of a counter `r` below `2 ^ 64`, the instruction set
    with calls makes on `B ++ [Lret]` a segment of `n + 1` steps with `n ≤ k` (the steps of
    the run on `B` and the return step) from `m` to `retState isa.sp v r m'`, at the counter
    `r` with the stack pointer holding `v`. -/
theorem steps_snoc_ret (isa : Isa) {fn : String} {B : List LinstrRM} {tag : MemTag}
    {k r : Nat} {v : BitVec 64} {m m' : LstateMF} (hB : ∀ i ∈ B, isCall i.fst = false)
    (hstep : ∀ i ∈ B, ∀ s, isa.step (singletonProgM fn (B ++ [(.Lret, tag)])) i s =
      isa.step (singletonProgM fn B) i s)
    (hrun : isa.lsemFuelMemF (singletonProgM fn B) k m = some m')
    (hend : atPc (singletonProgM fn B) B.length m')
    (hsp : m'.prog.base.reg.getW isa.sp 64 = some (v - 8))
    (hra : m'.prog.base.lmem isa.sp (v - 8).toInt = BitVec.ofNat 64 r) (hr : r < 2 ^ 64) :
    ∃ n, n ≤ k ∧
      Steps isa.withCalls (singletonProgM fn (B ++ [(.Lret, tag)])) (n + 1) m
        (retState isa.sp v r m') ∧
      atPc (singletonProgM fn (B ++ [(.Lret, tag)])) r (retState isa.sp v r m') := by
  obtain ⟨n, hn, hsteps, hat⟩ := steps_snoc_ret_prefix isa (tag := tag) hB hstep hrun hend
  have hi : (singletonProgM fn (B ++ [(.Lret, tag)])).body[B.length]? = some (.Lret, tag) := by
    simp [singletonProgM]
  obtain ⟨h1, hat'⟩ := steps_ret isa hat hi hsp hra hr
  exact ⟨n, hn, hsteps.trans h1, hat'⟩

end IsaCall

end CatCrypt.Crypto.SecureCompilation.Ascent
