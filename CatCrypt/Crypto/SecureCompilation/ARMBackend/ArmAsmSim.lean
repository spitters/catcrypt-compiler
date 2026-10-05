/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMach
public import CatCrypt.Crypto.SecureCompilation.VIR.IsaAsmSim

@[expose] public section

set_option autoImplicit false

/-!
# The assembly simulation of AArch64

`armAsmSim` is the `LprogIsa.AsmSim` of the straight-line AArch64 fragment at the machine
`armMach r`: the gate accepts the instruction lists the selection `armSelX arrs sz cells`
maps, the encoder emits the bytes of the selected block followed by the bytes of `RET`, the
entry relation is the correspondence of `ArmMach.arm_mach_x` with the layouts and the index
bounds of the block, and the exit relation is the same correspondence with the frame of the
source run. The simulation is `ArmMach.arm_mach_x`.

## Main definitions

* `armGate`, `armEncode`: the gate and the encoder of the fragment.
* `armAsmSim`: the assembly simulation at `armMach r`, for every regime `r`.

## Main results

* `armAsmSim_halts`: an `armIsa` run of a gated block from a related state gives a halting
  run of the decoded bytes at `armMach r`.
-/

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmAsmSim

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmIsa
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMach

variable (arrs : List String) (sz : String → Nat) (cells : List (String × Nat))

/-- The gate of the AArch64 fragment: the selection maps every instruction of the block. -/
def armGate (is : List LinstrRM) : Bool := (is.mapM (armSelX arrs sz cells)).isSome

/-- The encoder of the AArch64 fragment: the bytes of the selected block followed by the
    bytes of `RET`, and no byte for a block outside the gate. -/
def armEncode (is : List LinstrRM) : List (BitVec 8) :=
  match is.mapM (armSelX arrs sz cells) with
  | some bs => encodeBMBlock armAlloc bs ++ ArmAbiEncoder.encRet
  | none => []

/-- **The assembly simulation of AArch64** at the machine `armMach r`, for the straight-line
    blocks of `armIsa` in a program `P` that `armSelX arrs sz cells` maps. At entry the
    states are related on `armRegs`, on the arrays, on the word cells and on the flags, the
    arrays and the cells are laid out separately and the indices of the block are in range;
    at the end the states are related in the same four relations, and the source run kept
    the function and the overflow flag and advanced the program counter by the length of the
    block (`FrameX`). -/
def armAsmSim (r : ArmRegime) (P : LprogM) : AsmSim (armIsa.straightSem P) (armMach r) where
  gate := armGate arrs sz cells
  encode := armEncode arrs sz cells
  Pre := fun is s b => RegRel armRegs s b.regs.get ∧ ArmMemRel arrs sz s b
    ∧ ArmWordRel cells s b ∧ ArmFlagRel s b ∧ ArmArrsSep arrs sz b.regs.get
    ∧ ArmCellsSep arrs sz cells b.regs.get ∧ BoundsOKX arrs sz cells is b
  Post := fun is s _ s' b' => RegRel armRegs s' b'.regs.get ∧ ArmMemRel arrs sz s' b'
    ∧ ArmWordRel cells s' b' ∧ ArmFlagRel s' b' ∧ FrameX is.length s s'
  sim := by
    intro is hg s b s' ⟨hrel, hmem, hword, hflag, hsep, hcs, hbd⟩ hrun
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hg
    obtain ⟨hdec, t, b', ht, hh, -, h1, h2, h3, h4, h5⟩ :=
      arm_mach_x r P arrs sz cells is bs hbs s b hrel hmem hword hflag hsep hcs hbd
    have hst : t = s' := Option.some.inj (ht.symm.trans hrun)
    subst hst
    refine ⟨bs.map .op ++ [.ret], b', ?_, hh, h1, h2, h3, h4, h5⟩
    simp only [armEncode, hbs]
    exact hdec

/-- **An `armIsa` run of a gated block gives a halting run of its bytes at `armMach r`.** -/
theorem armAsmSim_halts (r : ArmRegime) (P : LprogM) {is : List LinstrRM}
    (hg : armGate arrs sz cells is = true) {s s' : LstateMF} {b : BMState}
    (hpre : (armAsmSim arrs sz cells r P).Pre is s b) (hrun : armIsa.runL P is s = some s') :
    ∃ prog b', (armMach r).decode (armEncode arrs sz cells is) = some prog
      ∧ (armMach r).Halts prog 0 b b' :=
  (armAsmSim arrs sz cells r P).halts hg hpre hrun

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmAsmSim
