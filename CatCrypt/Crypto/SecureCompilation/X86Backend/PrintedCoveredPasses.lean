/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCompleteLegal
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend

/-!
# Covered instructions under the frame-preserving passes

`PrintedCompleteLegal.Covered body i` reads the body `body` only through its parameters
`Params.ofBody body` (the frame size, the spill width and the save block), at the frame-slot
arms `movStore`, `movLoad`, `movImmSlot` and `adcxhi` of `GateOfLegal.GateForm`, and through
the labels the body defines, at the conditional branch. Two bodies agree on their frame
(`FrameAgree`) when the three parameters coincide; a covered instruction of one body is then
covered in the other, provided the other defines every label of the first.

A filter of a body agrees with it on its frame when the body issues no call, every removed
instruction is a move between names that are no spill slot, vector spill slot or frame array
(`FrameNeutral`), and the filter keeps the width of the body (`bodyIsU64`). The frame trim
`Haxc.frameTrim` removes only saves and restores of callee-saved registers and pointer
arguments, which are such moves, so it keeps every covered instruction it keeps.

The dead-write elimination `Haxc.deadWriteRet` of the fusion post-pass removes pure register
writes only, so it keeps every label; on a body whose eliminated form agrees with it on its
frame, it keeps every covered instruction it keeps.

## Main definitions

* `FrameAgree b b'`: the bodies `b` and `b'` have the same frame size, spill width and save
  block.
* `FrameNeutral x`: `x` is a one-to-one move between names that are no spill slot, vector
  spill slot or frame array.

## Main results

* `gateForm_of_frameAgree`, `covered_of_frameAgree`: a covered instruction of `b` is covered in
  every body `b'` that agrees with `b` on its frame and defines the labels of `b`.
* `frameSize_filter`, `frameAgree_filter`: a filter that removes only frame-neutral
  instructions of a call-free body and keeps its width agrees with it on its frame.
* `frameNeutral_of_frameTrim`: every instruction the frame trim removes is frame-neutral.
* `covered_frameTrim`: the frame trim keeps every covered instruction it keeps.
* `mem_dropDeadWriteBody`, `labelAt_deadWriteRet`: the dead-write elimination keeps every
  instruction that is no pure register write, hence every label.
* `covered_deadWriteRet`: the dead-write elimination keeps covered instructions at an agreeing
  frame.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredPasses

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (labelAt isLabelB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (spillQsaveOff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (slotOff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (kOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GateOfLegal (GateForm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCompleteLegal (Covered)

/-! ## 1. Frame agreement -/

/-- **Two bodies agree on their frame**: the body parameters of `b'` have the frame size, the
    spill width and the save block of those of `b`. -/
def FrameAgree (b b' : Lcmd) : Prop :=
  (Params.ofBody b').frame = (Params.ofBody b).frame ∧
    (Params.ofBody b').spillW = (Params.ofBody b).spillW ∧
    (Params.ofBody b').qsaveB = (Params.ofBody b).qsaveB

/-- Bodies that agree on their frame give every frame-slot name the same offset. -/
theorem spillQsaveOff_frameAgree {b b' : Lcmd} (h : FrameAgree b b') (q : String) :
    spillQsaveOff (Params.ofBody b').frame (Params.ofBody b').spillW q (Params.ofBody b').qsaveB
      = spillQsaveOff (Params.ofBody b).frame (Params.ofBody b).spillW q
          (Params.ofBody b).qsaveB := by
  rw [h.1, h.2.1, h.2.2]

/-- Bodies that agree on their frame have the same `slotOff`. -/
theorem slotOff_frameAgree {b b' : Lcmd} (h : FrameAgree b b') (q : String) :
    slotOff (Params.ofBody b') q = slotOff (Params.ofBody b) q := by
  simp only [slotOff, spillQsaveOff_frameAgree h]

/-- Bodies that agree on their frame have the same carry-operand test `kOk`. -/
theorem kOk_frameAgree {b b' : Lcmd} (h : FrameAgree b b') (x : String) :
    kOk (Params.ofBody b') x = kOk (Params.ofBody b) x := by
  simp only [kOk, spillQsaveOff_frameAgree h]

/-- **A gate form of `b` is a gate form of every body that agrees with `b` on its frame** and
    defines every label `b` defines. -/
theorem gateForm_of_frameAgree {b b' : Lcmd} {i : LinstrR} (h : GateForm b i)
    (hf : FrameAgree b b') (hl : ∀ l, (labelAt b l).isSome = true → (labelAt b' l).isSome = true) :
    GateForm b' i := by
  cases h with
  | movStore m q s hm hq ho hd hs =>
    exact .movStore m q s hm hq (by rw [spillQsaveOff_frameAgree hf]; exact ho)
      (by rw [slotOff_frameAgree hf]; exact hd) hs
  | movLoad m d q hm hd hq hk =>
    exact .movLoad m d q hm hd hq (by rw [kOk_frameAgree hf]; exact hk)
  | movImmSlot q v hq ho hd hv hr =>
    exact .movImmSlot q v hq (by rw [spillQsaveOff_frameAgree hf]; exact ho)
      (by rw [slotOff_frameAgree hf]; exact hd) hv (by rw [slotOff_frameAgree hf]; exact hr)
  | adcxhi o a s c ho ha hs hc hac hsc =>
    exact .adcxhi o a s c ho (by rw [kOk_frameAgree hf]; exact ha)
      (by rw [kOk_frameAgree hf]; exact hs) (by rw [kOk_frameAgree hf]; exact hc) hac hsc
  | cond cc l hc hl' => exact .cond cc l hc (hl l hl')
  | movRR m d s h1 h2 h3 => exact .movRR m d s h1 h2 h3
  | movImm32 d n h1 h2 => exact .movImm32 d n h1 h2
  | movImm64 d v h1 h2 => exact .movImm64 d v h1 h2
  | select d c a b' h1 h2 h3 h4 h5 h6 h7 => exact .select d c a b' h1 h2 h3 h4 h5 h6 h7
  | setcc m d a b' h1 h2 h3 h4 => exact .setcc m d a b' h1 h2 h3 h4
  | setccImm m d a v h1 h2 h3 h4 => exact .setccImm m d a v h1 h2 h3 h4
  | alu m d s h1 h2 h3 => exact .alu m d s h1 h2 h3
  | aluImm m d v h1 h2 h3 h4 => exact .aluImm m d v h1 h2 h3 h4
  | cmpImm d v h1 h2 => exact .cmpImm d v h1 h2
  | shiftImm m d k h1 h2 h3 h4 => exact .shiftImm m d k h1 h2 h3 h4
  | sarImm d k h1 h2 h3 => exact .sarImm d k h1 h2 h3
  | shiftReg m d a b' h1 h2 h3 h4 => exact .shiftReg m d a b' h1 h2 h3 h4
  | cast o d a h1 h2 h3 => exact .cast o d a h1 h2 h3
  | tagShift b' k d s h1 h2 h3 h4 h5 => exact .tagShift b' k d s h1 h2 h3 h4 h5
  | shl0 d s h1 h2 => exact .shl0 d s h1 h2
  | load d n b' off h1 h2 h3 h4 => exact .load d n b' off h1 h2 h3 h4
  | store n b' off s h1 h2 h3 h4 => exact .store n b' off s h1 h2 h3 h4
  | storeMov n b' off s h1 h2 h3 h4 => exact .storeMov n b' off s h1 h2 h3 h4
  | loadMov d n b' off h1 h2 h3 h4 => exact .loadMov d n b' off h1 h2 h3 h4
  | leaIdx d b' x sc h1 h2 h3 h4 => exact .leaIdx d b' x sc h1 h2 h3 h4
  | loadIdx d b' x h1 h2 h3 => exact .loadIdx d b' x h1 h2 h3
  | storeIdx a b' x v h1 h2 h3 => exact .storeIdx a b' x v h1 h2 h3
  | zeroArr b' n h1 h2 h3 => exact .zeroArr b' n h1 h2 h3
  | storeImm d b' v k h1 h2 h3 h4 => exact .storeImm d b' v k h1 h2 h3 h4
  | leaFa d q h1 h2 h3 => exact .leaFa d q h1 h2 h3
  | adcx d a s c h1 h2 h3 h4 h5 h6 h7 => exact .adcx d a s c h1 h2 h3 h4 h5 h6 h7
  | mulx l h s h1 h2 h3 => exact .mulx l h s h1 h2 h3
  | label k l => exact .label k l

/-- **A covered instruction of `b` is covered in every body that agrees with `b` on its frame**
    and defines every label `b` defines. -/
theorem covered_of_frameAgree {b b' : Lcmd} {i : LinstrR} (h : Covered b i)
    (hf : FrameAgree b b') (hl : ∀ l, (labelAt b l).isSome = true → (labelAt b' l).isSome = true) :
    Covered b' i := by
  rcases h with h | h | h
  · exact Or.inl (gateForm_of_frameAgree h hf hl)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- A label `b` defines is defined by every filter of `b` that keeps the labels. -/
theorem labelAt_filter {b : Lcmd} {p : Linstr → Bool}
    (hp : ∀ x ∈ b, (∀ k l, x.li_i ≠ .Llabel k l) ∨ p x = true) (l : LLabel)
    (h : (labelAt b l).isSome = true) : (labelAt (b.filter p) l).isSome = true := by
  simp only [labelAt, List.findIdx?_isSome, List.any_eq_true, List.mem_filter] at h ⊢
  obtain ⟨x, hx, hl⟩ := h
  refine ⟨x, ⟨hx, ?_⟩, hl⟩
  rcases hp x hx with hn | hp
  · unfold isLabelB at hl
    split at hl
    · exact absurd ‹_› (hn _ _)
    · cases hl
  · exact hp

/-! ## 2. Filters that keep the frame -/

/-- **A frame-neutral instruction**: a move `Lopn [D] o [S]` between register names `D`, `S`
    that are no spill slot `k.N`, no vector spill slot `kv.N` and no frame array. -/
def FrameNeutral (x : LinstrR) : Prop :=
  ∃ (d o s : String), x = .Lopn [.reg d] o [.reg s] ∧
    hasPrefix d "k." = false ∧ hasPrefix s "k." = false ∧
    hasPrefix d "kv." = false ∧ hasPrefix s "kv." = false ∧ faB d = false ∧ faB s = false

/-- A left fold over a filter is the fold over the list when every removed element leaves the
    accumulator unchanged. -/
theorem foldl_filter_of_neutral {α β : Type} (f : β → α → β) (p : α → Bool) :
    ∀ (l : List α) (a : β), (∀ x ∈ l, p x = false → ∀ a, f a x = a) →
      (l.filter p).foldl f a = l.foldl f a := by
  intro l
  induction l with
  | nil => intro a _; rfl
  | cons x l ih =>
    intro a h
    grind

section Filter

variable {b : Lcmd} {p : Linstr → Bool}

/-- A name that is no frame array has no frame-array parts. -/
theorem faParts?_of_faB {q : String} (h : faB q = false) : faParts? q = none := by
  simpa [faB] using h

/-- A filter removing frame-neutral instructions keeps the `FRAME` directive. -/
theorem frameDirective_filter (hn : ∀ x ∈ b, p x = false → FrameNeutral x.li_i) :
    frameDirective (b.filter p) = frameDirective b := by
  unfold frameDirective
  apply foldl_filter_of_neutral
  intro x hx hp a
  obtain ⟨d, o, s, he, -⟩ := hn x hx hp
  cases a <;> simp [he]

/-- A filter removing frame-neutral instructions keeps the `FRAMEADD` total. -/
theorem frameAddDirective_filter (hn : ∀ x ∈ b, p x = false → FrameNeutral x.li_i) :
    frameAddDirective (b.filter p) = frameAddDirective b := by
  unfold frameAddDirective
  apply foldl_filter_of_neutral
  intro x hx hp a
  obtain ⟨d, o, s, he, -⟩ := hn x hx hp
  simp [he]

/-- A filter removing frame-neutral instructions keeps the frame-array region. -/
theorem faBytes_filter (hn : ∀ x ∈ b, p x = false → FrameNeutral x.li_i) :
    faBytes (b.filter p) = faBytes b := by
  unfold faBytes
  apply foldl_filter_of_neutral
  intro x hx hp a
  obtain ⟨d, o, s, he, -, -, -, -, hfd, hfs⟩ := hn x hx hp
  simp [he, faOpBytes, faParts?_of_faB hfd, faParts?_of_faB hfs]

/-- A filter removing frame-neutral instructions keeps the largest spill index. -/
theorem maxSpillIdx_filter (hn : ∀ x ∈ b, p x = false → FrameNeutral x.li_i) :
    maxSpillIdx (b.filter p) = maxSpillIdx b := by
  unfold maxSpillIdx
  apply foldl_filter_of_neutral
  intro x hx hp a
  obtain ⟨d, o, s, he, hkd, hks, -⟩ := hn x hx hp
  simp [he, hkd, hks]

/-- A filter removing frame-neutral instructions keeps the largest vector-spill index. -/
theorem maxVecSpillIdx_filter (hn : ∀ x ∈ b, p x = false → FrameNeutral x.li_i) :
    maxVecSpillIdx (b.filter p) = maxVecSpillIdx b := by
  unfold maxVecSpillIdx
  apply foldl_filter_of_neutral
  intro x hx hp a
  obtain ⟨d, o, s, he, -, -, hvd, hvs, -⟩ := hn x hx hp
  simp [he, hvd, hvs]

/-- A filter of a call-free body is call-free. -/
theorem bodyHasCall_filter (hc : bodyHasCall b = false) : bodyHasCall (b.filter p) = false := by
  grind [bodyHasCall, List.any_eq_false]

end Filter

/-- **The frame size of a filter**: a filter of a call-free body that removes only
    frame-neutral instructions and keeps the width of the body has the frame size of the
    body. -/
theorem frameSize_filter {b : Lcmd} {p : Linstr → Bool} (hc : bodyHasCall b = false)
    (hn : ∀ x ∈ b, p x = false → FrameNeutral x.li_i)
    (hu : bodyIsU64 (b.filter p) = bodyIsU64 b) :
    frameSize (b.filter p) = frameSize b := by
  simp only [frameSize, qsaveBytesFor, vecSpillBytes, frameDirective_filter hn,
    frameAddDirective_filter hn, faBytes_filter hn, maxSpillIdx_filter hn,
    maxVecSpillIdx_filter hn, bodyHasCall_filter hc, hc, hu, Bool.false_and]

/-- **A filter keeps the frame**: a filter of a call-free body that removes only frame-neutral
    instructions and keeps the width of the body agrees with it on its frame. -/
theorem frameAgree_filter {b : Lcmd} {p : Linstr → Bool} (hc : bodyHasCall b = false)
    (hn : ∀ x ∈ b, p x = false → FrameNeutral x.li_i)
    (hu : bodyIsU64 (b.filter p) = bodyIsU64 b) :
    FrameAgree b (b.filter p) := by
  refine ⟨frameSize_filter hc hn hu, ?_, ?_⟩
  · simp only [Params.ofBody, hu]
  · simp only [Params.ofBody, qsaveBytesFor, bodyHasCall_filter hc, hc]

/-! ## 3. The frame trim -/

/-- A move between a register `X` of the frame trim and its save slot `qsave.X`, in either
    direction, is frame-neutral. -/
theorem frameNeutral_saveMov {x : LinstrR} {X : String}
    (hX : X ∈ ["RBX", "RBP", "R12", "R13", "R14", "R15", "RDI", "RSI"])
    (h : slotMov? x = some (slotOfReg X, X) ∨ slotMov? x = some (X, slotOfReg X)) :
    FrameNeutral x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases h with h | h <;> obtain ⟨o, rfl, -⟩ := Haxc.slotMov?_lopn h <;>
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, o, _, rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The unwritten callee-saved registers of a body are callee-saved registers. -/
theorem mem_of_unwrittenSaved {b : Lcmd} {X : String} (h : X ∈ Haxc.unwrittenSaved b) :
    X ∈ ["RBX", "RBP", "R12", "R13", "R14", "R15", "RDI", "RSI"] := by
  unfold Haxc.unwrittenSaved at h
  split at h
  · have := (List.mem_filter.1 h).1
    simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    tauto
  · simp at h

/-- The pointer arguments with a dead save are `RDI` or `RSI`. -/
theorem mem_of_deadArgSaves {b : Lcmd} {X : String} (h : X ∈ Haxc.deadArgSaves b) :
    X ∈ ["RBX", "RBP", "R12", "R13", "R14", "R15", "RDI", "RSI"] := by
  have := (List.mem_filter.1 h).1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  tauto

/-- Every instruction the frame trim removes is frame-neutral. -/
theorem frameNeutral_of_frameTrim (b : Lcmd) (x : Linstr)
    (h : (!((Haxc.unwrittenSaved b).any
        (fun X => Haxc.saveOfB X x.li_i || Haxc.restoreOfB X x.li_i)
      || (Haxc.deadArgSaves b).any (fun R => Haxc.saveOfB R x.li_i))) = false) :
    FrameNeutral x.li_i := by
  simp only [Bool.not_eq_false', Bool.or_eq_true, List.any_eq_true, Haxc.saveOfB,
    Haxc.restoreOfB, beq_iff_eq] at h
  rcases h with ⟨X, hX, hs | hs⟩ | ⟨X, hX, hs⟩
  · exact frameNeutral_saveMov (mem_of_unwrittenSaved hX) (Or.inl hs)
  · exact frameNeutral_saveMov (mem_of_unwrittenSaved hX) (Or.inr hs)
  · exact frameNeutral_saveMov (mem_of_deadArgSaves hX) (Or.inl hs)

/-- **The frame trim keeps covered instructions**: on a call-free body whose trim keeps its
    width, an instruction the trim keeps that is covered in the body is covered in the trimmed
    body. -/
theorem covered_frameTrim {b : Lcmd} (hc : bodyHasCall b = false)
    (hu : bodyIsU64 (Haxc.frameTrim b) = bodyIsU64 b) {i : LinstrR} (h : Covered b i) :
    Covered (Haxc.frameTrim b) i := by
  unfold Haxc.frameTrim at hu ⊢
  refine covered_of_frameAgree h
    (frameAgree_filter hc (fun x _ hp => frameNeutral_of_frameTrim b x hp) hu)
    (labelAt_filter (fun x _ => ?_))
  cases hx : x.li_i with
  | Llabel k l =>
    right
    simp [Haxc.saveOfB, Haxc.restoreOfB, slotMov?]
  | _ => left; intro k l h; cases h

/-! ## 4. The dead-write elimination of the fusion post-pass -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (deadWriteMarks keptL
  dropDeadWriteBody pureWrDst?)

/-- The dead-write elimination keeps every instruction that is no pure register write. -/
theorem mem_dropDeadWriteBody {x : Linstr} (hp : pureWrDst? x.li_i = none) :
    ∀ {l : Lcmd}, x ∈ l → x ∈ dropDeadWriteBody l := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons i is ih =>
    intro h
    simp only [dropDeadWriteBody, deadWriteMarks, keptL, List.filter_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h
    · simp [hp]
    · split <;> simp_all
      grind

/-- A label of `b` is a label of its dead-write elimination `Haxc.deadWriteRet b`. -/
theorem labelAt_deadWriteRet {b : Lcmd} (l : LLabel) (h : (labelAt b l).isSome = true) :
    (labelAt (Haxc.deadWriteRet b) l).isSome = true := by
  simp only [labelAt, List.findIdx?_isSome, List.any_eq_true] at h ⊢
  obtain ⟨x, hx, hl⟩ := h
  have hp : pureWrDst? x.li_i = none := by
    unfold isLabelB at hl
    split at hl
    · next hx' => rw [hx']; rfl
    · cases hl
  unfold Haxc.deadWriteRet
  split
  · next r hr =>
    split_ifs
    · refine ⟨x, ?_, hl⟩
      obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hr
      rw [List.dropLast_concat]
      rcases List.mem_append.1 hx with hx | hx
      · exact List.mem_append_left _ (mem_dropDeadWriteBody hp hx)
      · exact List.mem_append_right _ hx
    · exact ⟨x, hx, hl⟩
  · exact ⟨x, hx, hl⟩

/-- **The dead-write elimination keeps covered instructions**: when the eliminated body
    `Haxc.deadWriteRet b` agrees with `b` on its frame, every instruction covered in `b` is
    covered in it. -/
theorem covered_deadWriteRet {b : Lcmd} (hf : FrameAgree b (Haxc.deadWriteRet b))
    {i : LinstrR} (h : Covered b i) : Covered (Haxc.deadWriteRet b) i :=
  covered_of_frameAgree h hf (labelAt_deadWriteRet)

end CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredPasses
