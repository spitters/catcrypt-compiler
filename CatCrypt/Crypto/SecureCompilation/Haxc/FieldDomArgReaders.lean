/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomEntrySlot

/-!
# Readers of a save slot through the last printer passes

A reader of the save slot of a register is a 64-bit move from the slot with one source. The
reload of spilled compare operands rewrites only a compare with two sources, and the
two-address legalisation rewrites only an operation with two sources, so both keep a reader
as it is. A reader of the body after the re-allocation is therefore a reader of the printed
body.

## Main results

* `spillCmp?_of_slotReader`, `slotReader_cmpReload`: the reload of spilled compare operands
  keeps a reader.
* `legalizeInstr_of_slotReader`, `slotReader_twoAddrBody`: the two-address legalisation keeps a
  reader.
* `slotReader_printedBody`: a reader of the body after the re-allocation is a reader of the
  printed body.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data twoAddrBody
  legalizeInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload (cmpReload cmpReloadI spillCmp?
  cmpReloadI_of_none)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate (printedBody reallocStage)

/-- **A reader of a save slot is no compare on a spilled operand**: it has one source. -/
theorem spillCmp?_of_slotReader {R : String} {x : LinstrR} (h : SlotReader R x)
    (abi : LprogIsa.IsaAbi) : spillCmp? x abi = none := by
  obtain ⟨d, o, rfl, -, -⟩ := h
  rfl

/-- **The reload of spilled compare operands keeps a reader of a save slot.** -/
theorem slotReader_cmpReload {B : Lcmd} {R : String} (abi : LprogIsa.IsaAbi)
    (h : ∃ i ∈ B, SlotReader R i.li_i) : ∃ i ∈ cmpReload B abi, SlotReader R i.li_i := by
  obtain ⟨i, hi, hr⟩ := h
  refine ⟨i, List.mem_flatMap.mpr ⟨i, hi, ?_⟩, hr⟩
  simp [cmpReloadI, spillCmp?_of_slotReader hr abi]

/-- **The two-address legalisation keeps a reader of a save slot**: it has one source. -/
theorem legalizeInstr_of_slotReader {R : String} {i : Linstr} (h : SlotReader R i.li_i)
    (ok : Bool) (I : LprogIsa.IsaData) : legalizeInstr ok i I = [i] := by
  obtain ⟨d, o, he, -, -⟩ := h
  unfold legalizeInstr
  rw [he]

/-- **The two-address legalisation keeps a reader of a save slot.** -/
theorem slotReader_twoAddrBody {B : Lcmd} {R : String} (I : LprogIsa.IsaData)
    (h : ∃ i ∈ B, SlotReader R i.li_i) : ∃ i ∈ twoAddrBody B I, SlotReader R i.li_i := by
  obtain ⟨i, hi, hr⟩ := h
  refine ⟨i, List.mem_flatMap.mpr ⟨i, hi, ?_⟩, hr⟩
  rw [legalizeInstr_of_slotReader hr]
  exact List.mem_singleton_self i

/-- **A reader of a save slot in the body after the re-allocation is a reader of the printed
    body.** -/
theorem slotReader_printedBody {res : List String} {b0 : Lcmd} {R : String}
    (h : ∃ i ∈ reallocStage res b0, SlotReader R i.li_i) :
    ∃ i ∈ printedBody res b0, SlotReader R i.li_i :=
  slotReader_cmpReload _ (slotReader_twoAddrBody _ h)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
