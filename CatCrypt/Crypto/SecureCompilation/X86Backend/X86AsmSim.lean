/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
public import CatCrypt.Crypto.SecureCompilation.VIR.IsaAsmSim

@[expose] public section

set_option autoImplicit false

/-!
# The assembly simulation of x86-64

The `LprogIsa.AsmSim` records of the printed bodies at the machine `x86Mach r`. The source
semantics is the address semantics of the linear language (`runA`), whose frame words sit at
addresses fixed by a stack base: a source configuration is the stack base, the address state
and the zero flag, and a run is a terminating run that is safe along its steps for a
predicate `Q` (`x86AddrSem Q`). The entry relation fixes the stack base as the entry stack
register lowered by the frame of the body (`frameRsp`).

* `x86AsmSim` is the record of the class `printedAddrWB`, bodies with loops, carry chains,
  casts and immediate moves, with the safety predicate `SafeW`; its simulation is
  `DecodePrintedAddrW.printedAddr_simW_noCall`.
* `x86AsmSimB` is the record of the class `printedAddrB` with the safety predicate
  `LoadSafeAt`; its simulation is `DecodePrintedCFG.printedAddr_sim_noCall`. Its exit relation is
  the stronger one: every general-purpose name holds its machine register at width `64`.

## Main definitions

* `x86AddrSem`: the address semantics of printed bodies as a source semantics.
* `X86Entry`: the entry relation of both records.
* `x86AsmSim`, `x86AsmSimB`: the assembly simulations at `x86Mach r`, for every regime `r`.

## Main results

* `x86AsmSim_halts`, `x86AsmSimB_halts`: a safe terminating run of a gated body from a
  related configuration gives a halting run of the decoded function bytes on the address
  machine.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X86AsmSim

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP redW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (printedAddrB
  printedAddr_sim_noCall frameRsp RunSafe LoadSafeAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB
  printedAddr_simW_noCall SafeW NarrowCell)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState InRange8)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

/-- **The address semantics of printed bodies** with the safety predicate `Q`. A
    configuration is a stack base, an address state and a zero flag; a run of a body keeps
    the stack base and is a terminating run of `runA`, with the frame words of the body at
    their addresses from the stack base, that satisfies `Q` at the stack base along its
    steps (`RunSafe`). -/
def x86AddrSem (Q : BitVec 64 → Lcmd → LstateA → Prop) : SrcSem where
  Body := Lcmd
  State := BitVec 64 × LstateA × Bool
  Run := fun body c c' => c'.1 = c.1 ∧ ∃ fuel,
    runA (frameP (Params.ofBody body) c.1) body fuel c.2.1 c.2.2 = some c'.2
      ∧ RunSafe (frameP (Params.ofBody body) c.1) body (Q c.1 body) fuel c.2.1 c.2.2

/-- **The entry relation of a printed body.** The stack base is the entry stack register
    lowered by the frame of the body, the address state is at program counter `0`, every
    general-purpose name holds the value of its machine register at width `64` or a bit the
    machine register zero-extends, and the memories are equal. -/
def X86Entry (body : Lcmd) (c : BitVec 64 × LstateA × Bool) (sa : AState) : Prop :=
  c.1 = frameRsp body sa ∧ c.2.1.reg.lpc = 0
    ∧ (∀ R, gpOk R = true → c.2.1.reg.getW R 64 = some (sa.regs (phys R))
        ∨ ∃ b : BitVec 1, c.2.1.reg.lvm R = ⟨1, b⟩ ∧ sa.regs (phys R) = b.setWidth 64)
    ∧ c.2.1.mem = sa.mem

variable (r : CT.DoitRegime)

/-- **The assembly simulation of x86-64 on the class `printedAddrWB`** at the machine
    `x86Mach r`: the encoder is `encodeLfundefBytes`, the entry relation is `X86Entry`, and
    at the end the stack register is restored, every general-purpose name holds the value of
    its machine register, a bit the machine register zero-extends or a 32- or 16-bit cell of
    it (`NarrowCell`), and the memories agree outside the red-zone word. -/
def x86AsmSim : AsmSim (x86AddrSem SafeW) (x86Mach r) where
  gate := printedAddrWB
  encode := encodeLfundefBytes
  Pre := X86Entry
  Post := fun body _ sa c' sa' => sa'.regs "%rsp" = sa.regs "%rsp"
    ∧ (∀ R, gpOk R = true → c'.2.1.reg.getW R 64 = some (sa'.regs (phys R))
        ∨ (∃ b : BitVec 1, c'.2.1.reg.lvm R = ⟨1, b⟩ ∧ sa'.regs (phys R) = b.setWidth 64)
        ∨ NarrowCell (c'.2.1.reg.lvm R) (sa'.regs (phys R)))
    ∧ (∀ x, ¬ InRange8 (redW (frameRsp body sa)) x → c'.2.1.mem x = sa'.mem x)
  sim := by
    rintro body hg ⟨rsp, s, zf⟩ sa ⟨rsp', t⟩ ⟨hrsp, hpc, hent, hmem⟩
      ⟨-, fuel, hrun, hsafe⟩
    simp only at hrsp hpc hent hmem hrun hsafe
    subst hrsp
    obtain ⟨prog, sa', hdec, hh, h1, h2, h3⟩ :=
      printedAddr_simW_noCall body hg sa s zf hpc hent hmem fuel t hrun hsafe
    exact ⟨prog, sa', hdec, (x86Mach_halts_iff r).mpr hh, h1, h2, h3⟩

/-- **The assembly simulation of x86-64 on the class `printedAddrB`** at the machine
    `x86Mach r`: the encoder is `encodeLfundefBytes`, at entry every general-purpose name
    holds the value of its machine register at width `64`, and at the end the stack register
    is restored, every general-purpose name holds the value of its machine register at width
    `64`, and the memories agree outside the red-zone word. -/
def x86AsmSimB : AsmSim (x86AddrSem fun rsp body => LoadSafeAt rsp body) (x86Mach r) where
  gate := printedAddrB
  encode := encodeLfundefBytes
  Pre := fun body c sa => c.1 = frameRsp body sa ∧ c.2.1.reg.lpc = 0
    ∧ (∀ R, gpOk R = true → c.2.1.reg.getW R 64 = some (sa.regs (phys R)))
    ∧ c.2.1.mem = sa.mem
  Post := fun body _ sa c' sa' => sa'.regs "%rsp" = sa.regs "%rsp"
    ∧ (∀ R, gpOk R = true → c'.2.1.reg.getW R 64 = some (sa'.regs (phys R)))
    ∧ (∀ x, ¬ InRange8 (redW (frameRsp body sa)) x → c'.2.1.mem x = sa'.mem x)
  sim := by
    rintro body hg ⟨rsp, s, zf⟩ sa ⟨rsp', t⟩ ⟨hrsp, hpc, hent, hmem⟩
      ⟨-, fuel, hrun, hsafe⟩
    simp only at hrsp hpc hent hmem hrun hsafe
    subst hrsp
    obtain ⟨prog, sa', hdec, hh, h1, h2, h3⟩ :=
      printedAddr_sim_noCall body hg sa s zf hpc hent hmem fuel t hrun hsafe
    exact ⟨prog, sa', hdec, (x86Mach_halts_iff r).mpr hh, h1, h2, h3⟩

/-- **A safe terminating run of a body in `printedAddrWB` gives a halting run of its
    function bytes** on the address machine. -/
theorem x86AsmSim_halts {body : Lcmd} (hg : printedAddrWB body = true)
    {c c' : BitVec 64 × LstateA × Bool} {sa : AState} (hpre : X86Entry body c sa)
    (hrun : (x86AddrSem SafeW).Run body c c') :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ RInstrSemantics.Halts aMachine prog 0 sa sa' := by
  obtain ⟨prog, sa', hd, hh⟩ := (x86AsmSim .doitm).halts hg hpre hrun
  exact ⟨prog, sa', hd, RInstrSemantics.halts_of_haltsNoCall ((x86Mach_halts_iff .doitm).mp hh)⟩

/-- **A safe terminating run of a body in `printedAddrB` gives a halting run of its function
    bytes** on the address machine. -/
theorem x86AsmSimB_halts {body : Lcmd} (hg : printedAddrB body = true)
    {c c' : BitVec 64 × LstateA × Bool} {sa : AState} (hpre : (x86AsmSimB r).Pre body c sa)
    (hrun : (x86AddrSem fun rsp body => LoadSafeAt rsp body).Run body c c') :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ RInstrSemantics.Halts aMachine prog 0 sa sa' := by
  obtain ⟨prog, sa', hd, hh⟩ := (x86AsmSimB r).halts hg hpre hrun
  exact ⟨prog, sa', hd, RInstrSemantics.halts_of_haltsNoCall ((x86Mach_halts_iff r).mp hh)⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.X86AsmSim
