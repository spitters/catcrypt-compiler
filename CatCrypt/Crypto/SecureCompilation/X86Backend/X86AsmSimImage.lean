/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells
public import CatCrypt.Crypto.SecureCompilation.VIR.IsaAsmSim

@[expose] public section

set_option autoImplicit false

/-!
# The assembly simulation of x86-64 for runs of `x86Isa`

`x86ImageAsmSim` is the `LprogIsa.AsmSim` at the machine `x86Mach r` whose source run is the
in-bounds fuel run of `x86Isa` (`Isa.checkedSem`). A body is a pair of a virtual body `B`
over `x86Isa` and a printed straight body; the gate is the conjunction of the register
allocation checker `ownedCheckMC` of `B` against the image of the cell body, the class
`printedAddrWB` of the printed body and the image gates; the encoder emits the function
bytes of the printed body. The simulation is `ImageAddrCells.virt_bytesC_noCall`, which
composes the image simulation with `DecodePrintedAddrW.printedAddr_simW_noCall`. The printed
body has no
conditional branch.

## Main definitions

* `x86ImageGate`: the gate on pairs of a virtual body and a printed body.
* `X86ImageEntry`: the entry relation.
* `x86ImageAsmSim`: the assembly simulation, for every regime `r`.

## Main results

* `x86ImageAsmSim_halts`: an in-bounds halting run of `x86Isa` on a gated virtual body gives
  a halting run of the decoded function bytes on the address machine.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X86AsmSimImage

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (imgGateBW)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP redW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64 Disjoint8)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

variable (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
  (base : String → BitVec 64) (outs : List String) (fn : String)

/-- **The gate of the image route** on a virtual body `p.1` and a printed body `p.2`: the
    register allocation checker accepts the virtual body against the image of the cell body
    with the observed names `outs`, the printed body is in the class `printedAddrWB`, the
    cell body is in the class `physImgB`, and it passes the gate `imgGateB`, or the gate
    with carry chains `imgGateBW` with no observed name in the width analysis at the
    return; and no observed name is a frame-array name (`faB`). -/
def x86ImageGate (p : List LinstrRM × Lcmd) : Bool :=
  ownedCheckMC outs p.1 (JasminLsemAddrImage.virtImg slotArr (cellBody slotArr p.2))
    && printedAddrWB p.2
    && JasminLsemAddrImage.physImgB slotArr (cellBody slotArr p.2)
    && (imgGateB frame slotArr (cellBody slotArr p.2)
      || (imgGateBW frame slotArr (cellBody slotArr p.2)
        && ImageAddrSimW.retOutsB frame (cellBody slotArr p.2) outs))
    && outs.all (fun r => !faB r)

/-- **The entry relation of the image route.** The printed body has no slot move at a cell
    and no conditional branch; at the stack base of the machine state the frame map is
    separated, gives the cells their words and agrees with the stack frame on the names of
    the body; the source state is at program counter `0` of the function `fn`; and an
    address state at program counter `0` is related to the source state on the cell body,
    holds every general-purpose name at the value of its machine register and has the
    memory of the machine. -/
def X86ImageEntry (p : List LinstrRM × Lcmd) (b : LstateMF) (sa : AState) : Prop :=
  CellNoSlot slotArr p.2
    ∧ (∀ (k : Nat) (bi : Linstr), p.2[k]? = some bi → ∀ cc l, bi.li_i ≠ .Lcond cc l)
    ∧ ImgSep frame slotArr base (frameRsp p.2 sa)
    ∧ CellFrames frame slotArr base (frameRsp p.2 sa) p.2
    ∧ (∀ q ∈ ImageAddrFrame.bodyNamesI p.2,
        frame q = frameP (Params.ofBody p.2) (frameRsp p.2 sa) q)
    ∧ b.prog.lfn = fn ∧ b.prog.base.reg.lpc = 0
    ∧ ∃ (s : LstateA) (zf : Bool), ImgRel frame slotArr base (cellBody slotArr p.2) b s zf
        ∧ s.reg.lpc = 0
        ∧ (∀ R, DecodePrinted.gpOk R = true →
            s.reg.getW R 64 = some (sa.regs (DecodePrinted.phys R)))
        ∧ s.mem = sa.mem

variable (r : CT.DoitRegime)

/-- **The assembly simulation of x86-64 for runs of `x86Isa`** at the machine `x86Mach r`.
    The source run is the in-bounds fuel run of `x86Isa` on the singleton program of the
    virtual body; the bytes are the function bytes of the printed body; at the end every
    observed name with a frame word outside the red-zone word holds the machine word at
    that frame word. -/
def x86ImageAsmSim :
    AsmSim (x86Isa.checkedSem fun p : List LinstrRM × Lcmd => singletonProgM fn p.1)
      (x86Mach r) where
  gate := x86ImageGate frame slotArr outs
  encode := fun p => encodeLfundefBytes p.2
  Pre := X86ImageEntry frame slotArr base fn
  Post := fun p _ sa t sa' => ∀ q a, q ∈ outs → frame q = some a →
    Disjoint8 (redW (frameRsp p.2 sa)) a → t.prog.base.reg.lvm q = ⟨64, read64 sa'.mem a⟩
  sim := by
    rintro ⟨B, body⟩ hg b sa t
      ⟨hN, hnc, hsep, hF, hfr, hfn, hbpc, s, zf, hrel, hpc, hent, hmem⟩ ⟨fuel, hrun, hok⟩
    simp only [x86ImageGate, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨hck, hpr⟩, hphys⟩, hgate⟩, hof⟩ := hg
    have hofa : ∀ r ∈ outs, faB r = false := by simpa using hof
    rw [x86Isa_lsemFuelMemF] at hrun
    rw [x86Isa_RunIdxOk] at hok
    obtain ⟨prog, sa', hdec, hh, hobs⟩ :=
      virt_bytesC_noCall hck hpr hphys hgate hsep hN hF hnc hfr fn b t hfn hbpc s zf hrel hpc hent
        hmem fuel hrun hok hofa
    exact ⟨prog, sa', hdec, (x86Mach_halts_iff r).mpr hh, hobs⟩

/-- **An in-bounds halting run of `x86Isa` on a gated virtual body gives a halting run of
    the function bytes of its printed body** on the address machine. -/
theorem x86ImageAsmSim_halts {p : List LinstrRM × Lcmd}
    (hg : x86ImageGate frame slotArr outs p = true) {b t : LstateMF} {sa : AState}
    (hpre : X86ImageEntry frame slotArr base fn p b sa) {fuel : Nat}
    (hrun : x86Isa.lsemFuelMemF (singletonProgM fn p.1) fuel b = some t)
    (hok : x86Isa.RunIdxOk (singletonProgM fn p.1) fuel b) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes p.2) = some prog
      ∧ RInstrSemantics.Halts aMachine prog 0 sa sa' := by
  obtain ⟨prog, sa', hd, hh⟩ :=
    (x86ImageAsmSim frame slotArr base outs fn .doitm).halts hg hpre ⟨fuel, hrun, hok⟩
  exact ⟨prog, sa', hd, RInstrSemantics.halts_of_haltsNoCall ((x86Mach_halts_iff .doitm).mp hh)⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.X86AsmSimImage
