/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-!
# The System V red-zone leaf frame as a `JInstr 64` block

A System V AMD64 leaf function may use the 128 bytes below `%rsp` (the red zone) without
moving `%rsp`. `framePrologue` stores the six callee-saved registers
`AsmPrinter.calleeSavedRegs` (`%rbx`, `%rbp`, `%r12`, `%r13`, `%r14`, `%r15`) at the
red-zone slots `AsmPrinter.redZoneSlotOff 0, …, 5` (`-8(%rsp)`, …, `-48(%rsp)`), and
`frameEpilogue` loads them back from the same slots. The two blocks are the `JInstr`
forms of the text sequences `AsmPrinter.abiSave` and `AsmPrinter.abiRestore` for the full
callee-saved set. The `ret` (and an `endbr64`) are outside `JInstr` and outside this
module.

`JasminModel` keys memory by the base register's name, so the slots live in the bank
named `"%rsp"`. A body that neither reads nor writes that bank (`bankFree "%rsp"`) runs
from the post-prologue state exactly as from the entry state with that bank replaced
(`runBlock_withBank`). This gives the exact equation `runBlock_framed` for the framed
block, under the decidable body condition `frameSafe` (the body does not touch the
`"%rsp"` bank and does not write the register `%rsp`).

## Main definitions

* `withBank`: a state with one memory bank replaced.
* `bankFree`: the instruction neither reads nor writes a given memory bank.
* `framePrologue`, `frameEpilogue`: the red-zone save and restore blocks.
* `frameSafe`: the decidable condition on a framed body.
* `saveBank`: the contents of the `"%rsp"` bank after the prologue.
* `FrameAgree`: two states agree off the callee-saved registers and the `"%rsp"` bank.
* `FrameRel`: a state relation extended by the values of `%rsp` and the six callee-saved
  registers.

## Main results

* `evalInstr_withBank`, `runBlock_withBank`: a bank-free instruction or block commutes
  with replacing that bank.
* `runBlock_regs_of_not_written`: a block preserves every register none of its
  instructions writes.
* `runBlock_framed`: the framed block's final state is the body's final state with the
  `"%rsp"` bank replaced by `saveBank st` and the six callee-saved registers reset to their
  entry values.
* `runBlock_framed_calleeSaved`, `runBlock_framed_rsp`, `runBlock_framed_regs_other`,
  `runBlock_framed_flags`, `runBlock_framed_mem_other`, `runBlock_framed_mem_rsp`: the
  components of that equation.
* `corresJ_framed`: a `CorresJ` for the body, whose relation at the abstract result does
  not depend on the callee-saved registers or the `"%rsp"` bank, holds for the framed block
  at `FrameRel`, which also records that `%rsp` and the callee-saved registers end at
  their entry values.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFrame

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (calleeSavedRegs redZoneSlotOff)
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc (writtenNames)

/-! ## 1. Replacing one memory bank -/

/-- The state `s` with the memory bank named `b` replaced by `m`. -/
def withBank {w : Nat} (s : JState w) (b : String) (m : Int → BitVec w) :
    JState w :=
  { s with mem := fun b' o => if b' = b then m o else s.mem b' o }

@[simp] theorem withBank_regs {w : Nat} (s : JState w) (b : String)
    (m : Int → BitVec w) : (withBank s b m).regs = s.regs := rfl

@[simp] theorem withBank_flags {w : Nat} (s : JState w) (b : String)
    (m : Int → BitVec w) : (withBank s b m).flags = s.flags := rfl

/-- The instruction neither reads nor writes the memory bank named `b`: no memory operand
    has base `b`, and a `loadSym` neither aliases nor reads bank `b`. -/
def bankFree {w : Nat} (b : String) : JInstr w → Bool
  | .mulxMem _ _ _ base _ => base != b
  | .loadMem _ base _ => base != b
  | .storeMem base _ _ => base != b
  | .loadMemIdx _ base _ _ => base != b
  | .storeMemIdx base _ _ _ => base != b
  | .loadSym dst sym => dst != b && sym != b
  | .addMem _ base _ => base != b
  | .addToMem base _ _ => base != b
  | .adcxMem _ base _ => base != b
  | .adoxMem _ base _ => base != b
  | .imulMem _ base _ => base != b
  | .imulriMem _ base _ _ => base != b
  | .cmpMem _ base _ => base != b
  | _ => true

/-- A bank-free instruction commutes with replacing that bank. -/
theorem evalInstr_withBank {w : Nat} (s : JState w) (b : String) (m : Int → BitVec w)
    (i : JInstr w) (h : bankFree b i = true) :
    evalInstr (withBank s b m) i = withBank (evalInstr s i) b m := by
  obtain ⟨regs, flags, mem⟩ := s
  cases i <;>
    simp_all [bankFree, evalInstr, withBank, JState.setReg, JState.store,
      JState.storeIdx, JState.loadIdx, JState.writeB5W, JState.writeB5, JState.writeB2W,
      JState.writeB4W, JState.writeB5W2, JState.writeB5N, JState.writeCFW,
      JState.writeB5Mem, JState.setRegMerge, JState.flagB, JState.condB] <;>
    (try rfl) <;>
    funext b' o <;> by_cases hb : b' = b <;> grind

/-- A block of bank-free instructions commutes with replacing that bank. -/
theorem runBlock_withBank {w : Nat} (s : JState w) (b : String) (m : Int → BitVec w)
    (body : List (JInstr w)) (h : ∀ i ∈ body, bankFree b i = true) :
    runBlock (withBank s b m) body = withBank (runBlock s body) b m := by
  induction body generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [runBlock_cons]
    rw [evalInstr_withBank s b m i (h i List.mem_cons_self)]
    exact ih _ fun j hj => h j (List.mem_cons_of_mem _ hj)

/-! ## 2. Registers no instruction writes -/

/-- An instruction preserves every register it does not write. -/
theorem evalInstr_regs_of_not_written (s : JState 64) (i : JInstr 64) (r : String)
    (h : r ∉ writtenNames i) : (evalInstr s i).regs r = s.regs r := by
  cases i <;>
    simp_all [writtenNames, evalInstr, JState.setReg, JState.store, JState.storeIdx,
      JState.writeB5W, JState.writeB5, JState.writeB2W, JState.writeB4W, JState.writeB5W2,
      JState.writeB5N, JState.writeCFW, JState.writeB5Mem, JState.setRegMerge]

/-- A block preserves every register none of its instructions writes. -/
theorem runBlock_regs_of_not_written (s : JState 64) (body : List (JInstr 64)) (r : String)
    (h : ∀ i ∈ body, r ∉ writtenNames i) : (runBlock s body).regs r = s.regs r := by
  induction body generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [runBlock_cons]
    rw [ih _ fun j hj => h j (List.mem_cons_of_mem _ hj)]
    exact evalInstr_regs_of_not_written s i r (h i List.mem_cons_self)

/-! ## 3. The frame blocks -/

/-- The red-zone prologue: `movq %r, -8·(k+1)(%rsp)` for the `k`-th callee-saved
    register `r` of `calleeSavedRegs`. -/
def framePrologue : List (JInstr 64) :=
  [ .storeMem "%rsp" (-8) (.reg "%rbx"), .storeMem "%rsp" (-16) (.reg "%rbp"),
    .storeMem "%rsp" (-24) (.reg "%r12"), .storeMem "%rsp" (-32) (.reg "%r13"),
    .storeMem "%rsp" (-40) (.reg "%r14"), .storeMem "%rsp" (-48) (.reg "%r15") ]

/-- The red-zone epilogue: `movq -8·(k+1)(%rsp), %r` for the `k`-th callee-saved
    register `r` of `calleeSavedRegs`. -/
def frameEpilogue : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" (-8), .loadMem "%rbp" "%rsp" (-16),
    .loadMem "%r12" "%rsp" (-24), .loadMem "%r13" "%rsp" (-32),
    .loadMem "%r14" "%rsp" (-40), .loadMem "%r15" "%rsp" (-48) ]

/-- `framePrologue` stores each register of `calleeSavedRegs` at its slot
    `redZoneSlotOff`, in the order `AsmPrinter.abiSave` prints. -/
theorem framePrologue_eq_zipIdx :
    framePrologue = calleeSavedRegs.zipIdx.map
      (fun p => .storeMem "%rsp" (redZoneSlotOff p.2) (.reg p.1)) := rfl

/-- `frameEpilogue` loads each register of `calleeSavedRegs` from its slot
    `redZoneSlotOff`, in the order `AsmPrinter.abiRestore` prints. -/
theorem frameEpilogue_eq_zipIdx :
    frameEpilogue = calleeSavedRegs.zipIdx.map
      (fun p => .loadMem p.1 "%rsp" (redZoneSlotOff p.2)) := rfl

/-- The condition on a framed body: the instruction neither reads nor writes the
    `"%rsp"` memory bank and does not write the register `%rsp`. -/
def frameSafe (i : JInstr 64) : Bool :=
  bankFree "%rsp" i && decide ("%rsp" ∉ writtenNames i)

/-- The `"%rsp"` bank after the prologue from `s`: the six slots hold the callee-saved
    registers of `s`, and every other offset holds what `s` held there. -/
def saveBank (s : JState 64) (o : Int) : BitVec 64 :=
  if o = -48 then s.regs "%r15" else if o = -40 then s.regs "%r14"
  else if o = -32 then s.regs "%r13" else if o = -24 then s.regs "%r12"
  else if o = -16 then s.regs "%rbp" else if o = -8 then s.regs "%rbx"
  else s.mem "%rsp" o

/-- The state `s` with the six callee-saved registers set to their values in `src`. -/
def restoreSaved (s : JState 64) (src : String → BitVec 64) : JState 64 :=
  { s with regs := fun r => if r ∈ calleeSavedRegs then src r else s.regs r }

/-- The prologue replaces the `"%rsp"` bank by `saveBank`. -/
theorem runBlock_framePrologue (s : JState 64) :
    runBlock s framePrologue = withBank s "%rsp" (saveBank s) := by
  obtain ⟨regs, flags, mem⟩ := s
  simp only [framePrologue, runBlock_cons, runBlock_nil, evalInstr, JState.store,
    withBank, JOperand.eval, JState.get, x86_MOV, JState.mk.injEq, true_and]
  funext b o
  by_cases hb : b = "%rsp"
  · subst hb; simp only [saveBank, true_and, if_true]
  · simp [hb]

/-- The epilogue, run from a state whose `"%rsp"` bank is `saveBank s`, resets the six
    callee-saved registers to their values in `s`. -/
theorem runBlock_frameEpilogue (s u : JState 64) :
    runBlock (withBank u "%rsp" (saveBank s)) frameEpilogue
      = restoreSaved (withBank u "%rsp" (saveBank s)) s.regs := by
  obtain ⟨regs, flags, mem⟩ := u
  simp only [frameEpilogue, runBlock_cons, runBlock_nil, evalInstr, JState.setReg,
    JState.load, withBank, restoreSaved, x86_MOV, if_true, saveBank,
    JState.mk.injEq, and_true]
  funext r
  simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false]
  by_cases h1 : r = "%r15"
  · simp [h1]
  by_cases h2 : r = "%r14"
  · simp [h2]
  by_cases h3 : r = "%r13"
  · simp [h3]
  by_cases h4 : r = "%r12"
  · simp [h4]
  by_cases h5 : r = "%rbp"
  · simp [h5]
  by_cases h6 : r = "%rbx"
  · simp [h6]
  simp [h1, h2, h3, h4, h5, h6]

/-! ## 4. The framed block -/

/-- **The framed block, exactly.** For a body of `frameSafe` instructions, running
    `framePrologue ++ body ++ frameEpilogue` from `st` gives the body's final state from
    `st` with the `"%rsp"` bank replaced by `saveBank st` and the six callee-saved
    registers reset to their values in `st`. -/
theorem runBlock_framed (st : JState 64) (body : List (JInstr 64))
    (hb : ∀ i ∈ body, frameSafe i = true) :
    runBlock st (framePrologue ++ body ++ frameEpilogue)
      = restoreSaved (withBank (runBlock st body) "%rsp" (saveBank st)) st.regs := by
  have hbf : ∀ i ∈ body, bankFree "%rsp" i = true := fun i hi => by
    have := hb i hi
    simp only [frameSafe, Bool.and_eq_true] at this
    exact this.1
  rw [Ascent.runBlock_append, Ascent.runBlock_append, runBlock_framePrologue,
    runBlock_withBank _ _ _ _ hbf, runBlock_frameEpilogue]

/-- The body of a `frameSafe` block preserves the register `%rsp`. -/
theorem runBlock_rsp_of_frameSafe (st : JState 64) (body : List (JInstr 64))
    (hb : ∀ i ∈ body, frameSafe i = true) :
    (runBlock st body).regs "%rsp" = st.regs "%rsp" :=
  runBlock_regs_of_not_written st body "%rsp" fun i hi => by
    have := hb i hi
    simp only [frameSafe, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2

/-- The framed block ends with each callee-saved register at its entry value. -/
theorem runBlock_framed_calleeSaved (st : JState 64) (body : List (JInstr 64))
    (hb : ∀ i ∈ body, frameSafe i = true) (r : String) (hr : r ∈ calleeSavedRegs) :
    (runBlock st (framePrologue ++ body ++ frameEpilogue)).regs r = st.regs r := by
  rw [runBlock_framed st body hb]
  simp [restoreSaved, hr]

/-- The framed block ends with `%rsp` at its entry value. -/
theorem runBlock_framed_rsp (st : JState 64) (body : List (JInstr 64))
    (hb : ∀ i ∈ body, frameSafe i = true) :
    (runBlock st (framePrologue ++ body ++ frameEpilogue)).regs "%rsp" = st.regs "%rsp" := by
  rw [runBlock_framed st body hb]
  have hn : "%rsp" ∉ calleeSavedRegs := by decide
  simp only [restoreSaved, if_neg hn, withBank_regs]
  exact runBlock_rsp_of_frameSafe st body hb

/-- Off the callee-saved registers, the framed block ends with the registers of the
    body run from `st`. -/
theorem runBlock_framed_regs_other (st : JState 64) (body : List (JInstr 64))
    (hb : ∀ i ∈ body, frameSafe i = true) (r : String) (hr : r ∉ calleeSavedRegs) :
    (runBlock st (framePrologue ++ body ++ frameEpilogue)).regs r
      = (runBlock st body).regs r := by
  rw [runBlock_framed st body hb]
  simp [restoreSaved, hr]

/-- The framed block ends with the flags of the body run from `st`. -/
theorem runBlock_framed_flags (st : JState 64) (body : List (JInstr 64))
    (hb : ∀ i ∈ body, frameSafe i = true) :
    (runBlock st (framePrologue ++ body ++ frameEpilogue)).flags
      = (runBlock st body).flags := by
  rw [runBlock_framed st body hb]
  rfl

/-- Off the `"%rsp"` bank, the framed block ends with the memory of the body run from
    `st`. -/
theorem runBlock_framed_mem_other (st : JState 64) (body : List (JInstr 64))
    (hb : ∀ i ∈ body, frameSafe i = true) (b : String) (hbn : b ≠ "%rsp") :
    (runBlock st (framePrologue ++ body ++ frameEpilogue)).mem b
      = (runBlock st body).mem b := by
  rw [runBlock_framed st body hb]
  simp [restoreSaved, withBank, hbn]

/-- The framed block ends with `saveBank st` in the `"%rsp"` bank: the six red-zone
    slots hold the entry values of the callee-saved registers, and every other offset
    holds its entry value. -/
theorem runBlock_framed_mem_rsp (st : JState 64) (body : List (JInstr 64))
    (hb : ∀ i ∈ body, frameSafe i = true) :
    (runBlock st (framePrologue ++ body ++ frameEpilogue)).mem "%rsp" = saveBank st := by
  rw [runBlock_framed st body hb]
  funext o
  simp [restoreSaved, withBank]

/-! ## 5. Transporting `CorresJ` through the frame -/

/-- The states `s` and `t` agree on every register other than the six callee-saved
    ones, on the flags, and on every memory bank other than `"%rsp"`. -/
structure FrameAgree (s t : JState 64) : Prop where
  regs : ∀ r, r ∉ calleeSavedRegs → s.regs r = t.regs r
  flags : s.flags = t.flags
  mem : ∀ b, b ≠ "%rsp" → s.mem b = t.mem b

/-- `SR` extended by saved register values: `SR st p.1` holds, and `%rsp` and each
    callee-saved register hold the value `p.2` records for it. -/
def FrameRel {AState : Type} (SR : JState 64 → AState → Prop) (st : JState 64)
    (p : AState × (String → BitVec 64)) : Prop :=
  SR st p.1 ∧ ∀ r ∈ "%rsp" :: calleeSavedRegs, st.regs r = p.2 r

/-- The framed block's final state agrees with the body's final state off the frame. -/
theorem frameAgree_framed (st : JState 64) (body : List (JInstr 64))
    (hb : ∀ i ∈ body, frameSafe i = true) :
    FrameAgree (runBlock st body) (runBlock st (framePrologue ++ body ++ frameEpilogue)) :=
  ⟨fun r hr => (runBlock_framed_regs_other st body hb r hr).symm,
    (runBlock_framed_flags st body hb).symm,
    fun b hbn => (runBlock_framed_mem_other st body hb b hbn).symm⟩

/-- **`CorresJ` through the frame.** Let `body` consist of `frameSafe` instructions and
    satisfy `CorresJ SR P fa body`, where `SR` at each abstract result `fa a` is invariant
    under `FrameAgree`. Then the framed block satisfies `CorresJ` at `FrameRel SR`: the
    abstract component follows `fa`, and the recorded values of `%rsp` and the six
    callee-saved registers are the ones they end with. -/
theorem corresJ_framed {AState : Type} {SR : JState 64 → AState → Prop}
    {P : AState → Prop} {fa : AState → AState} {body : List (JInstr 64)}
    (hb : ∀ i ∈ body, frameSafe i = true) (h : CorresJ SR P fa body)
    (hinv : ∀ a, P a → ∀ s t : JState 64, FrameAgree s t → SR s (fa a) → SR t (fa a)) :
    CorresJ (FrameRel SR) (fun p => P p.1) (fun p => (fa p.1, p.2))
      (framePrologue ++ body ++ frameEpilogue) := by
  intro st p hSR hP
  refine ⟨hinv p.1 hP _ _ (frameAgree_framed st body hb) (h st p.1 hSR.1 hP), ?_⟩
  intro r hr
  rw [← hSR.2 r hr]
  rcases List.mem_cons.mp hr with rfl | hr'
  · exact runBlock_framed_rsp st body hb
  · exact runBlock_framed_calleeSaved st body hb r hr'

end CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFrame
