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

end IsaCall

end CatCrypt.Crypto.SecureCompilation.Ascent
