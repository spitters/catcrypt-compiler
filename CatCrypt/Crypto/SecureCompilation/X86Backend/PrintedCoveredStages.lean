/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredPasses

/-!
# Covered instructions under register renaming and the full two-address legaliser

An instruction of a printed body is covered (`PrintedCompleteLegal.Covered`), a three-address
operation the two-address legaliser rewrites, or an unfused high-word binding. This module
proves that covered instructions, unfused high-word bindings and two three-address forms are
kept by a renaming of general-purpose names that is injective and fixes every other name
(`GpRenaming`), and therefore by a register re-allocation each of whose instructions is an
instruction of its input or such a renaming of one. The two three-address forms are the
subtraction `SUB:64 D, [A, D]`, which the legaliser routes through the scratch register `R15`
and its save slot, and the three-address compare `CMP:64 D, [A, S]`, which the legaliser
rewrites into `CMP:64 A, [A, S]`; both rewrites consist of gate forms.

## Main definitions

* `GpRenaming ρ`: `ρ` maps general-purpose names injectively to general-purpose names and
  fixes every other name.
* `renameR ρ i`: the operation `i` with every register name renamed by `ρ`.
* `ThreeAddrSubSelf i`, `ThreeAddrCmp i`: the subtraction from the destination and the
  three-address compare.

## Main results

* `gateForm_renameR`, `printedShape_renameR`, `arrShape_renameR`, `covered_renameR`: a
  renaming keeps a covered instruction covered.
* `covered_of_renamed`: a body each of whose instructions is an instruction of a body of
  covered instructions and unfused high-word bindings, or a renaming of one, is of that class,
  when it agrees with the input on its frame and keeps its labels.
* `labelAt_reallocBody`, `covered_reallocBody`: the register re-allocation keeps the labels,
  and keeps the class when it writes renamings of its input instructions.
* `legalizeInstr_subSelf`, `scratchRoute_subSelf_gateForm`: the legaliser routes the
  subtraction from the destination through gate forms.
* `legalizeInstr_cmp`: the legaliser rewrites the three-address compare into a gate form.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredStages

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (labelAt isLabelB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (cellParts?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (spillQsaveOff isSpillOrQsave)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk slotOff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (kOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GateOfLegal (GateForm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (PrintedShape)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCompleteLegal (Covered UnfusedMulHi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredPasses (FrameAgree
  covered_of_frameAgree)

/-! ## 1. Renamings of general-purpose names -/

/-- **A renaming of general-purpose names**: `ρ` maps every general-purpose name of the gate to
    a general-purpose name, injectively, and fixes every other name. -/
structure GpRenaming (ρ : String → String) : Prop where
  /-- The image of a general-purpose name is a general-purpose name. -/
  gp : ∀ n, gpOk n = true → gpOk (ρ n) = true
  /-- Every other name is fixed. -/
  fix : ∀ n, gpOk n = false → ρ n = n
  /-- Distinct general-purpose names have distinct images. -/
  inj : ∀ m n, gpOk m = true → gpOk n = true → ρ m = ρ n → m = n

/-- A renaming keeps the general-purpose names and only them. -/
theorem GpRenaming.gpOk_iff {ρ : String → String} (h : GpRenaming ρ) (n : String) :
    gpOk (ρ n) = gpOk n := by
  cases hn : gpOk n
  · rw [h.fix n hn, hn]
  · exact h.gp n hn

/-- A renaming is injective. -/
theorem GpRenaming.injective {ρ : String → String} (h : GpRenaming ρ) :
    Function.Injective ρ := by
  intro m n he
  cases hm : gpOk m <;> cases hn : gpOk n
  · rwa [h.fix m hm, h.fix n hn] at he
  · have := h.gpOk_iff m
    rw [he, h.gpOk_iff n, hm, hn] at this
    cases this
  · have := h.gpOk_iff m
    rw [he, h.gpOk_iff n, hm, hn] at this
    cases this
  · exact h.inj m n hm hn he

/-- The renaming of an operand: its register names, and the base and index of a
    register-indexed element. -/
def renOpd (ρ : String → String) : LOperand → LOperand
  | .reg n => .reg (ρ n)
  | .arrIdx b x sc => .arrIdx (ρ b) (ρ x) sc
  | o => o

/-- **The renaming of an operation**: every operand of an operation renamed; every other
    instruction kept. -/
def renameR (ρ : String → String) : LinstrR → LinstrR
  | .Lopn ds o ss => .Lopn (ds.map (renOpd ρ)) o (ss.map (renOpd ρ))
  | i => i

/-- A frame slot is fixed by a renaming. -/
theorem GpRenaming.fix_slot {ρ : String → String} (h : GpRenaming ρ) {q : String}
    (hq : isSpillOrQsave q = true) : ρ q = q :=
  h.fix q (GateOfLegal.not_gpOk_of_slot hq)

/-- The image of a name of `kOk` is a name of `kOk`. -/
theorem GpRenaming.kOk_image {ρ : String → String} (h : GpRenaming ρ) {P : Params}
    {n : String} (hk : kOk P n = true) : kOk P (ρ n) = true := by
  cases hn : gpOk n
  · rwa [h.fix n hn]
  · simp [kOk, h.gp n hn]

/-- A memory cell `mem.B.off` is no general-purpose name. -/
theorem gpOk_of_cellParts {n b : String} {off : Nat}
    (h : cellParts? n = some (b, off)) : gpOk n = false := by
  cases hn : gpOk n
  · rfl
  · simp only [gpOk, DecodePrinted.gpList, List.contains_eq_mem, List.mem_cons,
      List.not_mem_nil, decide_eq_true_eq, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp [cellParts?] at h

/-- A frame-array name is no general-purpose name. -/
theorem gpOk_of_faB {q : String} (h : faB q = true) : gpOk q = false := by
  cases hn : gpOk q
  · rfl
  · simp only [gpOk, DecodePrinted.gpList, List.contains_eq_mem, List.mem_cons,
      List.not_mem_nil, decide_eq_true_eq, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> revert h <;> decide

/-- **A renaming keeps a gate form.** -/
theorem gateForm_renameR {ρ : String → String} (h : GpRenaming ρ) {b : Lcmd} {i : LinstrR}
    (hi : GateForm b i) : GateForm b (renameR ρ i) := by
  have ne : ∀ {x y : String}, x ≠ y → ρ x ≠ ρ y := fun hxy => h.injective.ne hxy
  cases hi with
  | movRR m d s hm hd hs => exact .movRR m _ _ hm (h.gp d hd) (h.gp s hs)
  | movStore m q s hm hq h1 h2 hs =>
    change GateForm b (.Lopn [.reg (ρ q)] m [.reg (ρ s)])
    rw [h.fix_slot hq]
    exact .movStore m q _ hm hq h1 h2 (h.gp s hs)
  | movLoad m d q hm hd hq hk =>
    change GateForm b (.Lopn [.reg (ρ d)] m [.reg (ρ q)])
    rw [h.fix_slot hq]
    exact .movLoad m _ q hm (h.gp d hd) hq hk
  | movImm32 d n hd hn => exact .movImm32 _ n (h.gp d hd) hn
  | movImm64 d v hd hv => exact .movImm64 _ v (h.gp d hd) hv
  | movImmSlot q v hq h1 h2 h3 h4 =>
    change GateForm b (.Lopn [.reg (ρ q)] "MOV:64" [.imm v])
    rw [h.fix_slot hq]
    exact .movImmSlot q v hq h1 h2 h3 h4
  | select d c a x hd hc ha hx h1 h2 h3 =>
    exact .select _ _ _ _ (h.gp d hd) (h.gp c hc) (h.gp a ha) (h.gp x hx) (ne h1) (ne h2) (ne h3)
  | setcc m d a x hm hd ha hx => exact .setcc m _ _ _ hm (h.gp d hd) (h.gp a ha) (h.gp x hx)
  | setccImm m d a v hm hd ha hv => exact .setccImm m _ _ v hm (h.gp d hd) (h.gp a ha) hv
  | alu m d s hm hd hs => exact .alu m _ _ hm (h.gp d hd) (h.gp s hs)
  | aluImm m d v hm hd hv hf => exact .aluImm m _ v hm (h.gp d hd) hv hf
  | cmpImm d v hd hf => exact .cmpImm _ v (h.gp d hd) hf
  | shiftImm m d k hm hd hk h0 => exact .shiftImm m _ k hm (h.gp d hd) hk h0
  | sarImm d k hd h0 hk => exact .sarImm _ k (h.gp d hd) h0 hk
  | shiftReg m d a x hm hd ha hx => exact .shiftReg m _ _ _ hm (h.gp d hd) (h.gp a ha) (h.gp x hx)
  | cast o d a ho hd ha => exact .cast o _ _ ho (h.gp d hd) (h.gp a ha)
  | tagShift c k d s hc h0 hk hd hs => exact .tagShift c k _ _ hc h0 hk (h.gp d hd) (h.gp s hs)
  | shl0 d s hd hs => exact .shl0 _ _ (h.gp d hd) (h.gp s hs)
  | load d n c off hn hd hc ho =>
    change GateForm b (.Lopn [.reg (ρ d)] "LOAD:64" [.reg (ρ n)])
    rw [h.fix n (gpOk_of_cellParts hn)]
    exact .load _ n c off hn (h.gp d hd) hc ho
  | store n c off s hn hs hc ho =>
    change GateForm b (.Lopn [.reg (ρ n)] "STORE:64" [.reg (ρ s)])
    rw [h.fix n (gpOk_of_cellParts hn)]
    exact .store n c off _ hn (h.gp s hs) hc ho
  | storeMov n c off s hn hs hc ho =>
    change GateForm b (.Lopn [.reg (ρ n)] "MOV:64" [.reg (ρ s)])
    rw [h.fix n (gpOk_of_cellParts hn)]
    exact .storeMov n c off _ hn (h.gp s hs) hc ho
  | loadMov d n c off hn hd hc ho =>
    change GateForm b (.Lopn [.reg (ρ d)] "MOV:64" [.reg (ρ n)])
    rw [h.fix n (gpOk_of_cellParts hn)]
    exact .loadMov _ n c off hn (h.gp d hd) hc ho
  | leaIdx d c x sc hd hc hx hsc => exact .leaIdx _ _ _ sc (h.gp d hd) (h.gp c hc) (h.gp x hx) hsc
  | loadIdx d c x hd hc hx => exact .loadIdx _ _ _ (h.gp d hd) (h.gp c hc) (h.gp x hx)
  | storeIdx a c x v hc hx hv => exact .storeIdx _ _ _ _ (h.gp c hc) (h.gp x hx) (h.gp v hv)
  | zeroArr c n hc hn hk => exact .zeroArr _ n (h.gp c hc) hn hk
  | storeImm d c v k hd hc hv hk =>
    exact .storeImm _ _ _ k (h.gp d hd) (h.gp c hc) (h.gp v hv) hk
  | leaFa d q hd hq ho =>
    change GateForm b (.Lopn [.reg (ρ d)] "LEA:64" [.reg (ρ q)])
    rw [h.fix q (gpOk_of_faB hq)]
    exact .leaFa _ q (h.gp d hd) hq ho
  | adcx d a s c hd ha hs hc h1 h2 h3 =>
    refine .adcx _ _ _ _ (h.gp d hd) (h.gp a ha) (h.gp s hs) (h.gp c hc) (ne h1) (ne h2) ?_
    rcases h3 with rfl | ⟨h4, h5⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨ne h4, ne h5⟩
  | adcxhi o a s c ho ha hs hc h1 h2 =>
    exact .adcxhi _ _ _ _ (h.gp o ho) (h.kOk_image ha) (h.kOk_image hs) (h.kOk_image hc)
      (ne h1) (ne h2)
  | mulx l x s hl hx hs => exact .mulx _ _ _ (h.gp l hl) (h.gp x hx) (h.gp s hs)
  | label k l => exact .label k l
  | cond cc l h1 h2 => exact .cond cc l h1 h2

/-- The image of a general-purpose register of `x86Abi` is one. -/
theorem GpRenaming.isGp {ρ : String → String} (h : GpRenaming ρ) {n : String}
    (hn : x86Abi.IsGp n) : x86Abi.IsGp (ρ n) :=
  (PrintedCompleteX86.gpOk_iff_isGp _).1 (h.gp n ((PrintedCompleteX86.gpOk_iff_isGp n).2 hn))

/-- **A renaming keeps a printed shape.** -/
theorem printedShape_renameR {ρ : String → String} (h : GpRenaming ρ) {i : LinstrR}
    (hi : PrintedShape x86Abi i) : PrintedShape x86Abi (renameR ρ i) := by
  rcases hi with ⟨n, R, A, B, hR, hA, hB, rfl⟩ | ⟨n, R, A, v, hR, hA, hv, rfl⟩ |
      ⟨l, R, A, B, hR, hA, hB, rfl⟩ | ⟨R, hR, rfl⟩
  · exact Or.inl ⟨n, ρ R, ρ A, ρ B, h.isGp hR, h.isGp hA, h.isGp hB, rfl⟩
  · exact Or.inr (Or.inl ⟨n, ρ R, ρ A, v, h.isGp hR, h.isGp hA, hv, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨l, ρ R, ρ A, ρ B, h.isGp hR, h.isGp hA, h.isGp hB, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ρ R, h.isGp hR, rfl⟩))

/-- **A renaming keeps a stack-array shape.** -/
theorem arrShape_renameR {ρ : String → String} (h : GpRenaming ρ) {i : LinstrR}
    (hi : PrintedCompleteX86.ArrShape i) : PrintedCompleteX86.ArrShape (renameR ρ i) := by
  rcases hi with ⟨B, n, hB, hn, hk, rfl⟩ | ⟨D, B, V, k, hD, hB, hV, hk, rfl⟩
  · exact Or.inl ⟨ρ B, n, h.isGp hB, hn, hk, rfl⟩
  · exact Or.inr ⟨ρ D, ρ B, ρ V, k, h.isGp hD, h.isGp hB, h.isGp hV, hk, rfl⟩

/-- **A renaming keeps a covered instruction covered.** -/
theorem covered_renameR {ρ : String → String} (h : GpRenaming ρ) {b : Lcmd} {i : LinstrR}
    (hi : Covered b i) : Covered b (renameR ρ i) := by
  rcases hi with hi | hi | hi
  · exact Or.inl (gateForm_renameR h hi)
  · exact Or.inr (Or.inl (printedShape_renameR h hi))
  · exact Or.inr (Or.inr (arrShape_renameR h hi))

/-- A renaming keeps an unfused high-word binding. -/
theorem unfusedMulHi_renameR (ρ : String → String) {i : LinstrR} (hi : UnfusedMulHi i) :
    UnfusedMulHi (renameR ρ i) := by
  obtain ⟨ds, ss, rfl⟩ := hi
  exact ⟨_, _, rfl⟩

/-! ## 2. Bodies of renamed instructions -/

/-- **A body of renamed instructions**: on a body `b` whose instructions are covered in it or
    unfused high-word bindings, every instruction of a body `b'` each of whose instructions is
    an instruction of `b` or a renaming of one is covered in `b'` or an unfused high-word
    binding, when `b'` agrees with `b` on its frame and keeps the labels of `b`. -/
theorem covered_of_renamed {b b' : Lcmd}
    (hcov : ∀ x ∈ b, Covered b x.li_i ∨ UnfusedMulHi x.li_i)
    (hren : ∀ y ∈ b', y ∈ b ∨ ∃ x ∈ b, ∃ ρ, GpRenaming ρ ∧ y.li_i = renameR ρ x.li_i)
    (hf : FrameAgree b b')
    (hl : ∀ l, (labelAt b l).isSome = true → (labelAt b' l).isSome = true) :
    ∀ y ∈ b', Covered b' y.li_i ∨ UnfusedMulHi y.li_i := by
  intro y hy
  rcases hren y hy with hy | ⟨x, hx, ρ, hρ, he⟩
  · exact (hcov y hy).imp (fun h => covered_of_frameAgree h hf hl) id
  · rw [he]
    exact (hcov x hx).imp (fun h => covered_of_frameAgree (covered_renameR hρ h) hf hl)
      (unfusedMulHi_renameR ρ)

/-! ## 3. The register re-allocation -/

section Realloc

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc

/-- An instruction of a body outside the fragment is a piece of its own. -/
theorem bar_mem_pieces {li : Linstr} (hf : fragOf? li = none) :
    ∀ {b : Lcmd}, li ∈ b → Piece.bar li ∈ pieces b := by
  intro b
  induction b with
  | nil => intro h; cases h
  | cons x b ih =>
    intro h
    unfold pieces
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · rw [hf]; exact List.mem_cons_self
    · have hb := ih h
      unfold pieces at hb
      split
      · split
        · rename_i heq
          rw [heq] at hb
          rcases List.mem_cons.1 hb with hb | hb
          · cases hb
          · exact List.mem_cons_of_mem _ hb
        · exact List.mem_cons_of_mem _ hb
      · exact List.mem_cons_of_mem _ hb

/-- The re-allocation keeps every instruction of a body that is a piece of its own. -/
theorem mem_reallocBody_of_bar (res : List String) (b : Lcmd) {li : Linstr}
    (h : Piece.bar li ∈ pieces b) : li ∈ reallocBody res b := by
  unfold reallocBody
  dsimp only
  generalize pieces b = ps at h
  induction ps with
  | nil => cases h
  | cons p ps ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · have := ih h
      split
      · exact List.mem_append_right _ this
      · exact List.mem_cons_of_mem _ this

/-- **The re-allocation keeps the labels of a body.** -/
theorem labelAt_reallocBody (res : List String) (b : Lcmd) (l : LLabel)
    (h : (labelAt b l).isSome = true) : (labelAt (reallocBody res b) l).isSome = true := by
  simp only [labelAt, List.findIdx?_isSome, List.any_eq_true] at h ⊢
  obtain ⟨x, hx, hxl⟩ := h
  refine ⟨x, mem_reallocBody_of_bar res b (bar_mem_pieces ?_ hx), hxl⟩
  unfold fragOf?
  split
  · next heq => rw [heq] at hxl; simp [isLabelB] at hxl
  · rfl

/-- **Covered instructions under the register re-allocation**: on a body `b` whose
    instructions are covered in it or unfused high-word bindings, every instruction of the
    re-allocated body is covered in it or an unfused high-word binding, when each instruction
    the re-allocation writes is an instruction of `b` or a renaming of one and the re-allocated
    body agrees with `b` on its frame. -/
theorem covered_reallocBody (res : List String) {b : Lcmd}
    (hcov : ∀ x ∈ b, Covered b x.li_i ∨ UnfusedMulHi x.li_i)
    (hren : ∀ y ∈ reallocBody res b, y ∈ b ∨
      ∃ x ∈ b, ∃ ρ, GpRenaming ρ ∧ y.li_i = renameR ρ x.li_i)
    (hf : FrameAgree b (reallocBody res b)) :
    ∀ y ∈ reallocBody res b, Covered (reallocBody res b) y.li_i ∨ UnfusedMulHi y.li_i :=
  covered_of_renamed hcov hren hf (labelAt_reallocBody res b)

end Realloc

/-! ## 4. The subtraction from the destination and the three-address compare -/

section TwoAddr

open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize

/-- **The subtraction from the destination**: `SUB:64 D, [A, D]` over general-purpose names
    with `A ≠ D`, which no copy into `D` legalises. -/
def ThreeAddrSubSelf (i : LinstrR) : Prop :=
  ∃ (d a : String), gpOk d = true ∧ gpOk a = true ∧ a ≠ d ∧
    i = .Lopn [.reg d] "SUB:64" [.reg a, .reg d]

/-- **The three-address compare** `CMP:64 D, [A, S]` over general-purpose sources, which sets
    the flags of `A - S` and writes no register. -/
def ThreeAddrCmp (i : LinstrR) : Prop :=
  ∃ (d a s : String), gpOk a = true ∧ gpOk s = true ∧
    i = .Lopn [.reg d] "CMP:64" [.reg a, .reg s]

/-- A renaming keeps the subtraction from the destination. -/
theorem threeAddrSubSelf_renameR {ρ : String → String} (h : GpRenaming ρ) {i : LinstrR}
    (hi : ThreeAddrSubSelf i) : ThreeAddrSubSelf (renameR ρ i) := by
  obtain ⟨d, a, hd, ha, had, rfl⟩ := hi
  exact ⟨ρ d, ρ a, h.gp d hd, h.gp a ha, h.injective.ne had, rfl⟩

/-- A renaming keeps the three-address compare. -/
theorem threeAddrCmp_renameR {ρ : String → String} (h : GpRenaming ρ) {i : LinstrR}
    (hi : ThreeAddrCmp i) : ThreeAddrCmp (renameR ρ i) := by
  obtain ⟨d, a, s, ha, hs, rfl⟩ := hi
  exact ⟨ρ d, ρ a, ρ s, h.gp a ha, h.gp s hs, rfl⟩

/-- The save slot of the scratch register is a frame-slot name. -/
theorem isSpillOrQsave_scratchSave : isSpillOrQsave (scratchSave x86Data) = true := by decide

/-- **The legaliser routes the subtraction from the destination through the scratch
    register**: with the route enabled, `SUB:64 D, [A, D]` becomes the save of `R15`, the copy
    `MOV:64 R15, A`, the subtraction `SUB:64 R15, [R15, D]`, the copy `MOV:64 D, R15` and the
    restore of `R15`. -/
theorem legalizeInstr_subSelf (x : Linstr) {d a : String} (had : a ≠ d)
    (hx : x.li_i = .Lopn [.reg d] "SUB:64" [.reg a, .reg d]) :
    legalizeInstr true x =
      scratchRoute x.li_ii "SUB:64" "MOV:64" d (.reg a) (.reg d) := by
  have h1 : needsTie "SUB:64" (LOperand.reg d) = true := by
    unfold needsTie
    rw [show tiedBases.contains (tieBase "SUB:64") = true by decide]
    rfl
  have h2 : (LOperand.reg a != LOperand.reg d) = true := by simp [had]
  have h3 : movFor "SUB:64" = some "MOV:64" := by decide
  have h4 : (tieBase "SUB:64" == "CMP" || tieBase "SUB:64" == "TEST") = false := by decide
  have h7 : commBases.contains (tieBase "SUB:64") = false := by decide
  unfold legalizeInstr
  rw [hx]
  have h6 : (LprogLeak.opNames (LOperand.reg d)).contains d = true := by
    simp [LprogLeak.opNames]
  simp only [h1, h2, h3, h4, h7, h6, isRegOrImm, Bool.and_self, Bool.false_and,
    Bool.not_true, Bool.false_eq_true, ite_true, ite_false]

/-- **The scratch route of the subtraction consists of gate forms** of every body whose frame
    resolves the save slot of the scratch register for a 64-bit load. -/
theorem scratchRoute_subSelf_gateForm (b : Lcmd) (ii : Nat) {d a : String}
    (hd : gpOk d = true) (ha : gpOk a = true)
    (hk : kOk (Params.ofBody b) (scratchSave x86Data) = true) :
    ∀ y ∈ scratchRoute ii "SUB:64" "MOV:64" d (.reg a) (.reg d), GateForm b y.li_i := by
  have hq := isSpillOrQsave_scratchSave
  obtain ⟨h1, h2, -⟩ := GateOfLegal.kOk_slot hk hq
  have h15 : gpOk x86Data.tieScratch = true := by decide
  intro y hy
  simp only [scratchRoute, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · exact .movStore _ _ _ (by simp) hq h1 h2 h15
  · exact .movRR _ _ _ (by simp) h15 ha
  · exact .alu _ _ _ (by simp) h15 hd
  · exact .movRR _ _ _ (by simp) hd h15
  · exact .movLoad _ _ _ (by simp) h15 hq hk

/-- **The legaliser rewrites the three-address compare into a gate form**: `CMP:64 D, [A, S]`
    becomes `CMP:64 A, [A, S]`, or stays when `A = D`. -/
theorem legalizeInstr_cmp (b : Lcmd) (ok : Bool) (x : Linstr) (h : ThreeAddrCmp x.li_i) :
    ∀ y ∈ legalizeInstr ok x, GateForm b y.li_i := by
  obtain ⟨d, a, s, ha, hs, hx⟩ := h
  have hcmp : GateForm b (.Lopn [.reg a] "CMP:64" [.reg a, .reg s]) := .alu _ _ _ (by simp) ha hs
  intro y hy
  by_cases had : a = d
  · subst had
    rw [legalizeInstr_of_tiedOk ok x (by rw [hx]; simp [tiedOk]), List.mem_singleton] at hy
    rw [hy, hx]
    exact hcmp
  · have h1 : needsTie "CMP:64" (LOperand.reg s) = true := by
      unfold needsTie
      rw [show tiedBases.contains (tieBase "CMP:64") = true by decide]
      rfl
    have h2 : (LOperand.reg a != LOperand.reg d) = true := by simp [had]
    have h3 : movFor "CMP:64" = some "MOV:64" := by decide
    have h4 : (tieBase "CMP:64" == "CMP" || tieBase "CMP:64" == "TEST") = true := by decide
    unfold legalizeInstr at hy
    rw [hx] at hy
    simp only [h1, h2, h3, h4, Bool.and_self, ite_true, List.mem_singleton] at hy
    rw [hy]
    exact hcmp

end TwoAddr

end CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredStages
