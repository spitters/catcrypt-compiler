/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhysAbi

@[expose] public section

set_option autoImplicit false

/-!
# The spill legalisations over a register file

The spill legalisations of the physical-ABI allocation route an instruction with too many
memory operands through the reload scratch registers. This module states them over a
register file `I : IsaAbi`, with the primary scratch `I.reload` and the secondary scratch
`I.reloadSnd` in place of the x86 names `reloadScratch` and `reloadScratch2`. At the x86
register file each is the x86 legalisation, by `rfl`.

## Main definitions

* `IsaAbi.IsReg`: a register of the register file: an allocatable register, a scratch
  register or the stack pointer.
* `legalizeMovI`, `legalizeOneSrcI`: the register copy, routed through `I.reload` when both
  operands are spill slots, and the one-source arm of the allocation.
* `cmovSpillSeqI`, `cmovSpillDstI?`: the select with its spilled destination and condition
  routed through `I.reload` and `I.reloadSnd`.
* `setccSpillI?`: the materialised comparison with spilled operands routed through the two
  scratch registers.
* `legalizeSpillDstI`: the scratch select, the scratch comparison, or the single
  instruction.

## Main results

* `legalizeMovI_x86`, `legalizeOneSrcI_x86`, `cmovSpillSeqI_x86`, `cmovSpillDstI?_x86`,
  `setccSpillI?_x86`, `legalizeSpillDstI_x86`: at the x86 register file the legalisations
  are the x86 ones.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

namespace IsaAbi

variable (abi : IsaAbi)

/-- **A register of the register file**: an allocatable register, a scratch register or the
    stack pointer. -/
def IsReg (n : String) : Prop := n ∈ abi.allocPool ∨ n ∈ abi.scratch ∨ n = abi.sp

instance (n : String) : Decidable (abi.IsReg n) := by
  unfold IsReg
  infer_instance

/-- An allocatable register is a register. -/
theorem isReg_of_mem_allocPool {n : String} (h : n ∈ abi.allocPool) : abi.IsReg n :=
  Or.inl h

/-- The primary reload scratch is a register when there is a scratch register. -/
theorem isReg_reload (h : abi.scratch ≠ []) : abi.IsReg abi.reload := by
  refine Or.inr (Or.inl ?_)
  cases hs : abi.scratch with
  | nil => exact absurd hs h
  | cons r rs => simp [reload, hs]

/-- The secondary reload scratch is a register when there are two scratch registers. -/
theorem isReg_reloadSnd (h : 2 ≤ abi.scratch.length) : abi.IsReg abi.reloadSnd := by
  refine Or.inr (Or.inl ?_)
  unfold reloadSnd
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

end IsaAbi

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

variable (I : IsaAbi)

/-- **The register copy over a register file**: a copy between two spill slots is routed
    through the primary scratch `I.reload`; every other copy is the single move. -/
def legalizeMovI (dst src : LOperand) (mov : String := "MOV") : List LinstrR :=
  if dst.isSpill && src.isSpill then
    [.Lopn [.reg I.reload] mov [src],
     .Lopn [dst] mov [.reg I.reload]]
  else
    [.Lopn [dst] mov [src]]

/-- **The one-source arm of the allocation over a register file**: for a register copy
    (`MOV` or `MOVQ` after the width tag is stripped) the copy `legalizeMovI` under the move
    selection `spillImmMovMnem u64`; the single instruction otherwise. -/
def legalizeOneSrcI (u64 : Bool) (opn : String) (d s : LOperand) : List LinstrR :=
  if stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ" then
    legalizeMovI I d s (spillImmMovMnem u64 opn d s)
  else [.Lopn [d] (spillImmMovMnem u64 opn d s) [s]]

/-- **The select over a register file** `opn d, [c, t, f]` with its spill slots routed
    through the scratch registers: a condition `c` in a spill slot is loaded by
    `MOV:64 I.reloadSnd, c` and the select reads `I.reloadSnd`; a destination `d` in a spill
    slot is replaced by `I.reload`, followed by the store `MOV:64 d, I.reload`. -/
def cmovSpillSeqI (opn : String) (d c t f : LOperand) : List LinstrR :=
  (if c.isSpill then [.Lopn [.reg I.reloadSnd] "MOV:64" [c]] else [])
    ++ (if d.isSpill then
          [.Lopn [.reg I.reload] opn
              [if c.isSpill then .reg I.reloadSnd else c, t, f],
           .Lopn [d] "MOV:64" [.reg I.reload]]
        else [.Lopn [d] opn [if c.isSpill then .reg I.reloadSnd else c, t, f]])

/-- **The select with spilled operands over a register file**: for a single destination
    `d`, the mnemonic `CMOV:64` and three sources `c`, `t`, `f`, where the destination or
    the condition is a spill slot, `cmovSpillSeqI I opn d c t f`; `none` in every other
    case. -/
def cmovSpillDstI? (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    Option (List LinstrR) :=
  match dsts, srcs with
  | [d], [c, t, f] =>
      if (d.isSpill || c.isSpill) && opn == "CMOV:64" then
        some (cmovSpillSeqI I opn d c t f)
      else none
  | _, _ => none

/-- **The materialised comparison with spilled operands over a register file**: for a
    single destination `d`, a comparison mnemonic `opn` (`isSetccMnem`) and two register
    sources `a`, `b`, one of the three a spill slot, the comparison
    `MOV I.reload, a; MOV I.reloadSnd, b; opn I.reload, [I.reload, I.reloadSnd];
    MOV d, I.reload`, the moves at the width of the comparison (`setccMov`); `none` in
    every other case. -/
def setccSpillI? (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    Option (List LinstrR) :=
  match dsts, srcs with
  | [d], [.reg a, .reg b] =>
      if (d.isSpill || (LOperand.reg a).isSpill || (LOperand.reg b).isSpill)
          && isSetccMnem opn then
        some [.Lopn [.reg I.reload] (setccMov opn) [.reg a],
              .Lopn [.reg I.reloadSnd] (setccMov opn) [.reg b],
              .Lopn [.reg I.reload] opn [.reg I.reload, .reg I.reloadSnd],
              .Lopn [d] (setccMov opn) [.reg I.reload]]
      else none
  | _, _ => none

/-- **The spill legalisation of an instruction over a register file**: the scratch select
    `cmovSpillDstI?` or the scratch comparison `setccSpillI?` when one is defined, and the
    single instruction `Lopn dsts opn srcs` otherwise. -/
def legalizeSpillDstI (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    List LinstrR :=
  match cmovSpillDstI? I dsts opn srcs with
  | some l => l
  | none =>
      match setccSpillI? I dsts opn srcs with
      | some l => l
      | none => [.Lopn dsts opn srcs]

/-! ## The x86 register file -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)

theorem legalizeMovI_x86 (dst src : LOperand) (mov : String) :
    legalizeMovI x86Data.toIsaAbi dst src mov = legalizeMov dst src mov := rfl

theorem legalizeOneSrcI_x86 (u64 : Bool) (opn : String) (d s : LOperand) :
    legalizeOneSrcI x86Data.toIsaAbi u64 opn d s = legalizeOneSrc u64 opn d s := rfl

theorem cmovSpillSeqI_x86 (opn : String) (d c t f : LOperand) :
    cmovSpillSeqI x86Data.toIsaAbi opn d c t f = cmovSpillSeq opn d c t f := rfl

theorem cmovSpillDstI?_x86 (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    cmovSpillDstI? x86Data.toIsaAbi dsts opn srcs = cmovSpillDst? dsts opn srcs := rfl

theorem setccSpillI?_x86 (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    setccSpillI? x86Data.toIsaAbi dsts opn srcs = setccSpill? dsts opn srcs := rfl

theorem legalizeSpillDstI_x86 (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    legalizeSpillDstI x86Data.toIsaAbi dsts opn srcs = legalizeSpillDst dsts opn srcs := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
