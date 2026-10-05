/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvMach
public import CatCrypt.Crypto.SecureCompilation.VIR.IsaAsmSim

@[expose] public section

set_option autoImplicit false

/-!
# The assembly simulation of RV64

`rvAsmSim` is the `LprogIsa.AsmSim` of the straight-line RV64 memory fragment at the machine
`rvMach r`: the gate accepts the instruction lists the selection `rvSelM arrs sz` maps, the
encoder emits the bytes of the selected instructions followed by the bytes of `ret`, the
entry relation is the correspondence of `RvMach.rv_mach_mem` with the array layout and the
index bounds of the block, and the exit relation is the same correspondence with the frame
of the source run. The simulation is `RvMach.rv_mach_mem`.

## Main definitions

* `rvGate`, `rvEncode`: the gate and the encoder of the fragment.
* `rvAsmSim`: the assembly simulation at `rvMach r`, for every regime `r`.

## Main results

* `rvAsmSim_halts`: an `rvIsa` run of a gated block from a related state gives a halting
  run of the decoded bytes at `rvMach r`.
-/

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvAsmSim

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvMach

variable (arrs : List String) (sz : String → Nat)

/-- The gate of the RV64 fragment: the selection maps every instruction of the block. -/
def rvGate (is : List LinstrRM) : Bool := (is.mapM (rvSelM arrs sz)).isSome

/-- The encoder of the RV64 fragment: the bytes of the selected instructions followed by the
    bytes of `ret`, and no byte for a block outside the gate. -/
def rvEncode (is : List LinstrRM) : List (BitVec 8) :=
  match is.mapM (rvSelM arrs sz) with
  | some rss => encodeRMBlock64 rss.flatten ++ wordLE RiscvElfObject.encRet
  | none => []

/-- **The assembly simulation of RV64** at the machine `rvMach r`, for the straight-line
    blocks of `rvIsa` in a program `P` that `rvSelM arrs sz` maps. At entry the states are
    related on `rvMemRegs` and on the arrays, the arrays are laid out separately and the
    indices of the block are in range; at the end the states are related in the same two
    relations, and the source run kept the zero flag, the function, the word memory and the
    carry and overflow flags and advanced the program counter by the length of the block
    (`FrameM`). -/
def rvAsmSim (r : RvRegime) (P : LprogM) : AsmSim (rvIsa.straightSem P) (rvMach r) where
  gate := rvGate arrs sz
  encode := rvEncode arrs sz
  Pre := fun is s b => RegRel rvMemRegs s b.regs.get ∧ RvMemRel arrs sz s b
    ∧ RvArrsSep arrs sz b.regs.get ∧ MemBounds arrs sz is b
  Post := fun is s _ s' b' => RegRel rvMemRegs s' b'.regs.get ∧ RvMemRel arrs sz s' b'
    ∧ FrameM is.length s s'
  sim := by
    intro is hg s b s' ⟨hrel, hmem, hsep, hbd⟩ hrun
    obtain ⟨rss, hrss⟩ := Option.isSome_iff_exists.mp hg
    obtain ⟨hdec, t, b', ht, hh, -, h1, h2, h3⟩ :=
      rv_mach_mem r P arrs sz is rss hrss s b hrel hmem hsep hbd
    have hst : t = s' := Option.some.inj (ht.symm.trans hrun)
    subst hst
    refine ⟨rss.flatten.map .op ++ [.ret], b', ?_, hh, h1, h2, h3⟩
    simp only [rvEncode, hrss]
    exact hdec

/-- **An `rvIsa` run of a gated block gives a halting run of its bytes at `rvMach r`.** -/
theorem rvAsmSim_halts (r : RvRegime) (P : LprogM) {is : List LinstrRM}
    (hg : rvGate arrs sz is = true) {s s' : LstateMF} {b : RMState64}
    (hpre : (rvAsmSim arrs sz r P).Pre is s b) (hrun : rvIsa.runL P is s = some s') :
    ∃ prog b', (rvMach r).decode (rvEncode arrs sz is) = some prog
      ∧ (rvMach r).Halts prog 0 b b' :=
  (rvAsmSim arrs sz r P).halts hg hpre hrun

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvAsmSim
