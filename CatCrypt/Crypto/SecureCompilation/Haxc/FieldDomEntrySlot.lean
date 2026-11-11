/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomInputAcc
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomEntry

/-!
# The save slots of the parameters in the printed field body

The entry check `entryB` asks that the save slot `qsave.R` of the register `R` of each
parameter has a frame word in the printed body, that is, that `qsave.R` is a name of the
trimmed body. The frame trim `frameTrim` drops the save of `RDI` and of `RSI` when no other
instruction names its slot (`deadArgSaves`), and the saves and restores of the callee-saved
registers the body does not write; it keeps every move that reads the slot of a parameter
register into another name (`SlotReader`), since such a move is no save and no restore of a
callee-saved register. A name `qsave.R` of a register with a save slot has a frame word. So the
slot half of the prologue facts holds as soon as the body before the trim reads the slot of
each parameter register.

## Main definitions

* `SlotReader`: a 64-bit move that reads the save slot of a register into another name.
* `ArgReaders`: the printed body of the allocated function of a member reads the save slot of
  the register of each parameter.

## Main results

* `mem_frameTrim_of_slotReader`: the frame trim keeps a reader of the slot of `RDI`, `RSI` or
  `RDX`.
* `slot_mem_frameNames`: the slot of such a register read by the body before the trim is a
  frame name of the trimmed body.
* `entryPrologue_of_argReaders`: the prologue facts of the printed body of a member of
  `fieldDomB'` from `ArgReaders`.
* `fieldDom_entryB_of_argReaders`: the stage `G19` on `fieldDomB'` from `ArgReaders`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameNames bodyNamesI)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (fieldAbi)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate (printedBody)

/-! ## 1. Readers of a save slot through the frame trim -/

/-- **A reader of the save slot of `R`**: a 64-bit move `MOVQ` or `MOV:64` of `qsave.R` into a
    name other than `qsave.R`. -/
def SlotReader (R : String) (x : LinstrR) : Prop :=
  ∃ d o, x = .Lopn [.reg d] o [.reg (slotOfReg R)] ∧ (o = "MOVQ" ∨ o = "MOV:64") ∧
    d ≠ slotOfReg R

/-- The registers whose saves a frame trim may drop are no parameter registers of the field
    layout. -/
theorem slot_ne_of_param {R X : String} (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX")
    (hX : X ∈ X86Backend.LprogAsmPrinter.calleeSavedRegs) : slotOfReg R ≠ X ∧ R ≠ X := by
  rcases hR with rfl | rfl | rfl <;>
    simp only [X86Backend.LprogAsmPrinter.calleeSavedRegs, List.mem_cons, List.not_mem_nil,
      or_false] at hX <;>
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The move of a reader is the move from the slot, or no move of `slotMov?`. -/
theorem slotMov?_of_slotReader {R : String} {x : LinstrR} (h : SlotReader R x) :
    ∃ d, d ≠ slotOfReg R ∧ (slotMov? x = none ∨ slotMov? x = some (d, slotOfReg R)) := by
  obtain ⟨d, o, rfl, ho, hd⟩ := h
  refine ⟨d, hd, ?_⟩
  unfold slotMov?
  dsimp only
  split_ifs <;> simp

/-- A reader of the slot of `R` is no save of a register other than `qsave.R`. -/
theorem saveOfB_of_slotReader {R X : String} {x : LinstrR} (h : SlotReader R x)
    (hX : X ≠ slotOfReg R) : saveOfB X x = false := by
  obtain ⟨d, -, hs | hs⟩ := slotMov?_of_slotReader h <;> simp [saveOfB, hs]
  intro _ h2
  exact hX h2.symm

/-- A reader of the slot of `R` is no restore of a register other than `R`. -/
theorem restoreOfB_of_slotReader {R X : String} {x : LinstrR} (h : SlotReader R x)
    (hX : R ≠ X) : restoreOfB X x = false := by
  obtain ⟨d, -, hs | hs⟩ := slotMov?_of_slotReader h <;> simp [restoreOfB, hs]
  intro _ h2
  exact hX (by simpa [slotOfReg] using h2)

/-- **The frame trim keeps a reader of the slot of a parameter register.** -/
theorem mem_frameTrim_of_slotReader {B : Lcmd} {R : String}
    (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX") {i : Linstr} (hi : i ∈ B)
    (h : SlotReader R i.li_i) : i ∈ frameTrim B := by
  unfold frameTrim
  refine List.mem_filter.mpr ⟨hi, ?_⟩
  have hD : ∀ X ∈ unwrittenSaved B, X ∈ X86Backend.LprogAsmPrinter.calleeSavedRegs := by
    intro X hX
    unfold unwrittenSaved at hX
    split at hX
    · exact (List.mem_filter.mp hX).1
    · cases hX
  have hA : ∀ R' ∈ deadArgSaves B, R' = "RDI" ∨ R' = "RSI" := by
    intro R' hR'
    have := (List.mem_filter.mp hR').1
    simpa using this
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true]
  refine ⟨fun X hX => ?_, fun R' hR' => ?_⟩
  · obtain ⟨h1, h2⟩ := slot_ne_of_param hR (hD X hX)
    simp [saveOfB_of_slotReader h fun e => h1 e.symm, restoreOfB_of_slotReader h h2]
  · refine saveOfB_of_slotReader h ?_
    rcases hA R' hR' with rfl | rfl <;> rcases hR with rfl | rfl | rfl <;> decide

/-- **The slot of a parameter register read before the trim is a frame name of the trimmed
    body.** -/
theorem slot_mem_frameNames {B : Lcmd} {R : String} (hR : R = "RDI" ∨ R = "RSI" ∨ R = "RDX")
    (h : ∃ i ∈ B, SlotReader R i.li_i) : slotOfReg R ∈ frameNames (frameTrim B) := by
  obtain ⟨i, hi, hr⟩ := h
  have hT := mem_frameTrim_of_slotReader hR hi hr
  unfold frameNames
  refine List.mem_filter.mpr ⟨?_, ?_⟩
  · rw [List.mem_eraseDups]
    refine List.mem_flatMap.mpr ⟨i, hT, ?_⟩
    obtain ⟨d, o, he, -, -⟩ := hr
    rw [he]
    simp [JasminLsemExportRewrites.instrNames, JasminLsemExportRewrites.opNames]
  · generalize X86Backend.LprogAsmPrinter.frameSize (frameTrim B) = F
    generalize X86Backend.LprogAsmPrinter.qsaveBytesFor (frameTrim B) = Q
    have k0 : hasPrefix "qsave.RDI" "k." = false := by decide
    have k1 : hasPrefix "qsave.RSI" "k." = false := by decide
    have k2 : hasPrefix "qsave.RDX" "k." = false := by decide
    have q0 : hasPrefix "qsave.RDI" "qsave." = true := by decide
    have q1 : hasPrefix "qsave.RSI" "qsave." = true := by decide
    have q2 : hasPrefix "qsave.RDX" "qsave." = true := by decide
    have s0 : (X86Backend.LprogAsmPrinter.qsaveSlot "RDI").isSome = true := by decide
    have s1 : (X86Backend.LprogAsmPrinter.qsaveSlot "RSI").isSome = true := by decide
    have s2 : (X86Backend.LprogAsmPrinter.qsaveSlot "RDX").isSome = true := by decide
    rcases hR with rfl | rfl | rfl <;>
      simp [X86Backend.LprogBytes.spillQsaveOff, X86Backend.LprogAsmPrinter.qsaveFrameOff,
        slotOfReg, k0, k1, k2, q0, q1, q2, s0, s1, s2]


/-! ## 2. The prologue facts of the printed body -/

/-- The export registers of the parameters of the field layout are `RDI`, `RSI` and `RDX`. -/
theorem exportReg_fieldAbi {k n : Nat} (hk : k = 1 ∨ k = 2) {a : AbiArg}
    (ha : a ∈ (fieldAbi k n).args) :
    exportReg a.reg = "RDI" ∨ exportReg a.reg = "RSI" ∨ exportReg a.reg = "RDX" := by
  have x0 : exportReg "%rdi" = "RDI" := by decide
  have x1 : exportReg "%rsi" = "RSI" := by decide
  have x2 : exportReg "%rdx" = "RDX" := by decide
  simp only [fieldAbi, List.mem_map, List.mem_range] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  have hj3 : j < 3 := by omega
  interval_cases j <;> simp [FieldRoute.fieldArgReg, x0, x1, x2]

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The printed body of the allocated function of a member reads the save slot of the
    register of each parameter**, before the frame trim. -/
def ArgReaders (e : _root_.Hax.TExpr) (σ : AbiLayout) (fname : String) : Prop :=
  ∀ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
    (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0])
    (P0 : Lprog) (c : List (String × String)) (f : Lfundef),
    haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩ →
    NarrowWords.narrowPrep q = some q' →
    regionAllocC (nfAbiNames fname σ) (legalizeRegion q') none (regionWebsEx σ exportReg)
      = some (P0, c) →
    P0.lp_funcs = [(fname, f)] →
    ∀ a ∈ σ.args, ∃ i ∈ printedBody f.lfd_res f.lfd_body, SlotReader (exportReg a.reg) i.li_i

/-- **The prologue facts of the printed body of a member of `fieldDomB'`** from `ArgReaders`:
    the stack half holds on every member (`stackReadFreeB_fieldDom`). -/
theorem entryPrologue_of_argReaders (h : fieldDomB' e σ = true)
    (hB : FieldBody e σ fname b t r cert) (hA : ArgReaders e σ fname) : EntryPrologue σ b := by
  refine ⟨fun a ha => ?_, stackReadFreeB_fieldDom h hB⟩
  obtain ⟨t0, q, q', P0, f, hq, hq', hx, hf, hb⟩ := fieldBody_printedBody hB
  obtain ⟨k, n, hk, rfl, -⟩ := fieldDomB'_layout h
  rw [hb]
  exact slot_mem_frameNames (exportReg_fieldAbi (fieldDomE_k hk) ha)
    (hA t0 q q' P0 cert f hq hq' hx hf a ha)

/-- **Stage `G19` on `fieldDomB'`** from `ArgReaders`. -/
theorem fieldDom_entryB_of_argReaders (h : fieldDomB' e σ = true)
    (hB : FieldBody e σ fname b t r cert) (hA : ArgReaders e σ fname) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "entryB" :=
  fieldDom_entryB h hB (entryPrologue_of_argReaders h hB hA)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
