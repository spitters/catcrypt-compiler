/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.CT.Leakage
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Machine constant time and the basic-block optimizer

`LprogOptPipeline.optimizeBasicBlocks` rewrites the straight-line runs of an `Lcmd`
body with five passes whose soundness is stated for `JasminLsem.lsemStraight`, where
`Lopn [.reg d] op [.reg a, .reg b]` denotes `d := a op b` for every choice of names.
The machine model of the body is `Jasmin.runBlock` over the block
`ConstIndexFold.gatherPrinted` produces, and the leakage model is `CT.blockLeakCT`.
The gather lowers the three-address form to `mov d, a; op d, b`, which denotes
`d := a op b` only when `d ≠ b` or `d = a`.

Copy propagation replaces a source by the name it was copied from. On the body
`cpSubBody` it rewrites `SUB RAX ← RBX, RCX` (with `RCX` a copy of `RAX`) to
`SUB RAX ← RBX, RAX`, which the gather lowers to `mov RAX, RBX; sub RAX, RAX`.
The gathered input block is constant time for the public register `RBX`; the
gathered optimized block loads from a table at an index equal to the secret `RAX`.

## Main results

* `gatherPrinted_cpSubBody`, `gatherPrinted_optimizeBasicBlocks_cpSubBody`: the two
  gathered blocks.
* `cpSubBody_machineCT`: the input block is constant time under `DoitRegime.doitm`.
* `cpSubBody_optimized_not_machineCT`: the optimized block is not.
* `optimizeBasicBlocks_not_machineCT_preserving`: there is a body with a
  register-indexed load whose gathered block is constant time while the gathered
  block of its optimization is not.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizeBasicBlocksCT

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (PubPred agreePub instrLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold (gatherPrinted)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (optimizeBasicBlocks)
open CatCrypt.Crypto.SecureCompilation.CT

/-- A body in which `RDX` receives `(RBX - RAX) + RAX`, the value of `RBX`, and indexes
    the table `T`. -/
def cpSubBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "RCX"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "SUB:64" [.reg "RBX", .reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "RDX"] "ADD:64" [.reg "RAX", .reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "R8"] "LOADIDX" [.arrIdx "T" "RDX" 8]⟩ ]

/-- The gathered block of `cpSubBody`. -/
def cpSubBlock : List (JInstr 64) :=
  [ .mov "RCX" (.reg "RAX"), .mov "RAX" (.reg "RBX"), .sub "RAX" (.reg "RCX"),
    .mov "RDX" (.reg "RAX"), .add "RDX" (.reg "RCX"), .loadMemIdx "R8" "T" "RDX" 8 ]

/-- The gathered block of the optimized `cpSubBody`: the source `RCX` of the `sub` is
    replaced by `RAX`. -/
def cpSubOptBlock : List (JInstr 64) :=
  [ .mov "RCX" (.reg "RAX"), .mov "RAX" (.reg "RBX"), .sub "RAX" (.reg "RAX"),
    .mov "RDX" (.reg "RAX"), .add "RDX" (.reg "RCX"), .loadMemIdx "R8" "T" "RDX" 8 ]

theorem gatherPrinted_cpSubBody : gatherPrinted cpSubBody = some cpSubBlock := by
  rfl

theorem gatherPrinted_optimizeBasicBlocks_cpSubBody :
    gatherPrinted (optimizeBasicBlocks cpSubBody) = some cpSubOptBlock := by
  native_decide

/-- The split in which only `RBX` is public. -/
def rbxPub : PubPred := fun r => r == "RBX"

/-- The gathered block of `cpSubBody` is constant time: its one address event is at
    offset `8 · RBX` of `T`. -/
theorem cpSubBody_machineCT : MachineCT .doitm rbxPub cpSubBlock := by
  intro s₁ s₂ hag
  have h : s₁.get "RBX" = s₂.get "RBX" := hag "RBX" rfl
  simp [cpSubBlock, blockLeakCT, instrLeakCT, instrLeak, evalInstr, JInstr.mnem,
    DoitRegime.leaksOperands, X86Mnem.timing, JState.setReg, JState.writeB5W, JOperand.eval,
    x86_MOV, x86_SUB, x86_ADD, rflags_of_aluop] at h ⊢
  simp [h]

/-- The all-zero register state. -/
def zeroSt : JState 64 := { regs := fun _ => 0 }

/-- The state with `RAX = 1` and every other register `0`. -/
def raxOneSt : JState 64 := { regs := fun r => if r = "RAX" then 1 else 0 }

/-- The gathered block of the optimized body is not constant time: the two states
    differ only in the secret `RAX` and access `T` at offsets `0` and `8`. -/
theorem cpSubBody_optimized_not_machineCT : ¬ MachineCT .doitm rbxPub cpSubOptBlock := by
  intro h
  have hag : agreePub rbxPub zeroSt raxOneSt := by
    intro r hr
    simp only [rbxPub, beq_iff_eq] at hr
    subst hr
    rfl
  have := h zeroSt raxOneSt hag
  simp [cpSubOptBlock, blockLeakCT, instrLeakCT, instrLeak, evalInstr, JInstr.mnem,
    DoitRegime.leaksOperands, X86Mnem.timing, JState.setReg, JState.writeB5W, JOperand.eval,
    x86_MOV, x86_SUB, x86_ADD, rflags_of_aluop, mleakToCT, zeroSt,
    raxOneSt] at this

/-- **`optimizeBasicBlocks` does not preserve machine constant time of the gathered
    block.** -/
theorem optimizeBasicBlocks_not_machineCT_preserving :
    ∃ (body : Lcmd) (g g' : List (JInstr 64)),
      gatherPrinted body = some g ∧ gatherPrinted (optimizeBasicBlocks body) = some g' ∧
      MachineCT .doitm rbxPub g ∧ ¬ MachineCT .doitm rbxPub g' :=
  ⟨cpSubBody, cpSubBlock, cpSubOptBlock, gatherPrinted_cpSubBody,
    gatherPrinted_optimizeBasicBlocks_cpSubBody, cpSubBody_machineCT,
    cpSubBody_optimized_not_machineCT⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizeBasicBlocksCT
