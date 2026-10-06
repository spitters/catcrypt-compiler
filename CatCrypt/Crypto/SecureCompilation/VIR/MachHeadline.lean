/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMachLoop
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvMachLoop
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvSym
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86AsmSim
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86AsmSimImage

@[expose] public section

set_option autoImplicit false

/-!
# The `mpn_and_n` body at the machines of three instruction sets

`mach_and_n_three_isas` collects the statements about the `mpn_and_n` loop body at the
machine level (`IsaMachine`) of AArch64, RV64 and x86-64, and the soundness of the register
allocation checker over an arbitrary instruction set. Every field is a theorem of another
module; this module proves the conjunction.

## What is stated

* AArch64 (`ArmAndN`). For every regime, the bytes of the body followed by `RET` decode at
  `armMach` and their run from a related state halts in a state related to the result of the
  `armIsa` run (`ArmMach.arm_and_mach`). Under `ArmRegime.dit` the bytes are constant time
  for the array bases `x0`, `x1`, `x3` and the index `x4`
  (`ArmMach.mpn_and_n_armMach_ct`). Under `ArmRegime.unguaranteed` they are not.
* RV64 (`RvAndN`). The same value statement at `rvMach` (`RvMach.rv_and_mach`). Under
  `RvRegime.zktMemData` the bytes are constant time for the array bases `a0`, `a1`, `a3` and
  the index `a4` (`RvMach.mpn_and_n_rvMach_ct`). Under `RvRegime.zkt` and under
  `RvRegime.unguaranteed` they are not.
* x86-64 (`X86Sim`). For every regime and every body in the class `printedAddrWB`, a safe
  terminating run of the address semantics from a related configuration gives a run of the
  decoded function bytes at `x86Mach` with a leakage trace and the exit relation
  (`X86AsmSim.x86AsmSim`); and the same for an in-bounds halting run of `x86Isa` on a
  virtual body that passes the gate of the image route (`X86AsmSimImage.x86ImageAsmSim`).
  Both statements are over all gated bodies. This module holds no x86 statement for the
  `mpn_and_n` body: its robust compilation and constant time are the theorem
  `mpn_and_n_rc_proved` of the module `Haxc.ComposeCTProved`, which this module cannot
  import.
* The checker (`CheckerOverIsa`). For an instruction set `I` with a lawful symbolic companion
  `T`, acceptance by `T.ownedCheckM` gives the simulation of halting runs of `I`
  (`X86Isa.IsaSym.ownedCheckM_sound`), with the instances `x86Sym` and `rvSym`.

## Hardware assumptions

* AArch64 constant time: the regime constructor `ArmRegime.dit`, a core that runs with
  `PSTATE.DIT = 1` and meets the table `CT.ArmMnem.leaksOperands`. Under it the data of a
  load or store is no event. The table classes `MOVZ` as data-independent although the
  FEAT_DIT list names `MOVK` only; the code holds no `MOVZ` (`ArmAndN.no_movz`).
* RV64 constant time: the regime constructor `RvRegime.zktMemData`, an implementation of Zkt
  on which the latency of a load or store is independent of the value transferred. The
  ratified Zkt text excludes loads and stores, so this assumption is beyond it;
  `RvAndN.not_ct_zkt` is the statement under the ratified text alone.
* The address of a load or store is an event under every regime of both machines.
* The machine semantics: the AArch64 and RV64 decoders and steps of `armMach` and `rvMach`,
  and the x86-64 address machine `aMachine` with the decoder `decodeLprog`.
* x86-64: the two statements of `X86Sim` are value statements and hold for every
  `CT.DoitRegime`; they assume no timing regime.

## The loop

The fields `loop` and `loop_ct` of `ArmAndN` and `RvAndN` state the kernel as a loop over its
limb count `n`, on the decoded programs `ArmMach.armAndLoopProg` and `RvMach.rvAndLoopProg`:
the run to the `RET` in `2 + 7 * n` and `2 + 13 * n` steps, the limb-wise conjunction in the
output array of the final memory, and constant time for the array bases and the count under
`ArmRegime.dit` and `RvRegime.zktMemData` (`ArmMach.arm_and_loop`,
`ArmMach.mpn_and_n_loop_armMach_ct`, `RvMach.rv_and_loop`, `RvMach.mpn_and_n_loop_rvMach_ct`).
The fields `mach` and `ct` are for the straight-line body of one iteration.

## Not covered

* The bytes of the loop: `loop` and `loop_ct` are over the decoded programs, and no statement
  relates them to an encoder output.
* Constant time of the x86-64 bytes of the body (the theorem `mpn_and_n_rc_proved`), and the
  checker on traced runs (`OwnedTVLeak.memFCT_of_ownedCheckML_at`).
* An AArch64 symbolic companion: there is no `IsaSym armIsa`, so the checker has no AArch64
  instance.

## Main definitions

* `ArmAndN`, `RvAndN`: the value, constant-time and non-constant-time statements of the body
  at `armMach` and `rvMach`.
* `X86Sim`: the assembly simulations of x86-64 with a leakage trace.
* `CheckerSound`, `CheckerOverIsa`: the soundness of the checker of a symbolic companion, and
  its statement over every lawful companion with the x86-64 and RV64 instances.
* `MachAndN`: the four records together.

## Main results

* `armAndN`, `rvAndN`, `x86Sim`, `checkerOverIsa`: the four records.
* `mach_and_n_three_isas`: `MachAndN`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.MachHeadline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## AArch64 -/

section Arm

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder
open CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmIsa
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMach

/-- **The `mpn_and_n` body at the AArch64 machine.** -/
structure ArmAndN : Prop where
  /-- Value correctness under every regime: the bytes of the body followed by `RET` decode,
      and from a related state the `armIsa` run of the body succeeds and the decoded program
      halts with the leakage of the block in a related state. -/
  mach : ∀ (r : ArmRegime) (P : LprogM) (n : Nat) (s : LstateMF) (b : BMState),
    RegRel armRegs s b.regs.get → ArmMemRel armAndArrs (fun _ => n) s b →
    ArmArrsSep armAndArrs (fun _ => n) b.regs.get → (b.regs.get "x4").toNat < n →
    (armMach r).decode (encodeBMBlock armAlloc armAndCode ++ ArmAbiEncoder.encRet)
        = some (armAndCode.map .op ++ [.ret]) ∧
    ∃ s' b', armIsa.runL P (armAndBody n) s = some s'
      ∧ (armMach r).Halts (armAndCode.map .op ++ [.ret]) 0 b b'
      ∧ (armMach r).RunL (fun _ _ => True) (armAndCode.map .op ++ [.ret]) 0 b
          ((armMach r).blockLeak b armAndCode) b'
      ∧ RegRel armRegs s' b'.regs.get ∧ ArmMemRel armAndArrs (fun _ => n) s' b'
      ∧ FrameM 6 s s'
  /-- Constant time of the bytes under `PSTATE.DIT = 1`. -/
  ct : ConstantTimeRel ArmAndPub (ArmBytesRun .dit armAndBytes)
  /-- The code holds no `MOVZ`. -/
  no_movz : ∀ bi ∈ armAndCode, bmMnem bi ≠ .movz
  /-- Without a timing guarantee the bytes are not constant time. -/
  not_ct_unguaranteed : ¬ ConstantTimeRel ArmAndPub (ArmBytesRun .unguaranteed armAndBytes)
  /-- The loop over `n` limbs under every regime: from a state that satisfies
      `ArmAndLoopEntry n`, with the inputs `A` at `x1` and `B` at `x0`, the decoded program
      `armAndLoopProg` reaches its `RET` in `armAndLoopFuel n` steps and halts there with the
      trace `armAndLoopLeak`; the output array at `x3` holds the limb-wise conjunction and
      the inputs are in place. -/
  loop : ∀ (r : ArmRegime) (n : Nat) (A B : Fin n → BitVec 64) (b : BMState),
    ArmAndLoopEntry n b → MachineMem64.ArrAt b.mem (b.regs.get "x1") n A →
    MachineMem64.ArrAt b.mem (b.regs.get "x0") n B →
    ∃ b', (armMach r).ReachesIn armAndLoopProg (armAndLoopFuel n) 0 b (armAndLoopLeak r n b)
        (if n = 0 then 2 else 10) b'
      ∧ (armMach r).Halts armAndLoopProg 0 b b'
      ∧ (armMach r).RunL (fun _ _ => True) armAndLoopProg 0 b (armAndLoopLeak r n b) b'
      ∧ MachineMem64.ArrAt b'.mem (b.regs.get "x3") n (fun k => opAnd64 (A k) (B k))
      ∧ MachineMem64.ArrAt b'.mem (b.regs.get "x1") n A
      ∧ MachineMem64.ArrAt b'.mem (b.regs.get "x0") n B
  /-- Constant time of the loop under `PSTATE.DIT = 1`, for the array bases and the count. -/
  loop_ct : ∀ n : Nat,
    ConstantTimeRel (fun b₁ b₂ => ArmAndLoopPub b₁ b₂ ∧ ArmAndLoopEntry n b₁)
      (fun b t => ∃ b', (armMach .dit).RunL (fun _ _ => True) armAndLoopProg 0 b t b')

/-- The statements of `ArmAndN` hold. -/
theorem armAndN : ArmAndN where
  mach := fun r P n s b hrel hmem hsep hidx => arm_and_mach r P n s b hrel hmem hsep hidx
  ct := mpn_and_n_armMach_ct
  no_movz := armAndCode_no_movz
  not_ct_unguaranteed := mpn_and_n_armMach_not_ct_unguaranteed
  loop := fun r n A B b he ha hb => arm_and_loop r n A B b he ha hb
  loop_ct := mpn_and_n_loop_armMach_ct

end Arm

/-! ## RV64 -/

section Rv

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvMach

/-- **The `mpn_and_n` body at the RV64 machine.** -/
structure RvAndN : Prop where
  /-- Value correctness under every regime: the bytes of the body followed by `ret` decode,
      and from a related state the `rvIsa` run of the body succeeds and the decoded program
      halts with the leakage of the block in a related state. -/
  mach : ∀ (r : RvRegime) (P : LprogM) (n : Nat) (s : LstateMF) (b : RMState64),
    RegRel rvMemRegs s b.regs.get → RvMemRel rvAndArrs (fun _ => n) s b →
    RvArrsSep rvAndArrs (fun _ => n) b.regs.get → (b.regs.get "a4").toNat < n →
    (rvMach r).decode (encodeRMBlock64 rvAndCode.flatten ++ wordLE RiscvElfObject.encRet)
        = some (rvAndCode.flatten.map .op ++ [.ret]) ∧
    ∃ s' b', rvIsa.runL P (rvAndBody n) s = some s'
      ∧ (rvMach r).Halts (rvAndCode.flatten.map .op ++ [.ret]) 0 b b'
      ∧ (rvMach r).RunL (fun _ _ => True) (rvAndCode.flatten.map .op ++ [.ret]) 0 b
          ((rvMach r).blockLeak b rvAndCode.flatten) b'
      ∧ RegRel rvMemRegs s' b'.regs.get ∧ RvMemRel rvAndArrs (fun _ => n) s' b'
      ∧ FrameM 6 s s'
  /-- Constant time of the bytes under Zkt with value-independent loads and stores. -/
  ct : ConstantTimeRel RvAndPub (RvBytesRun .zktMemData rvAndBytes)
  /-- Under the ratified Zkt text the bytes are not constant time. -/
  not_ct_zkt : ¬ ConstantTimeRel RvAndPub (RvBytesRun .zkt rvAndBytes)
  /-- Without a timing guarantee the bytes are not constant time. -/
  not_ct_unguaranteed : ¬ ConstantTimeRel RvAndPub (RvBytesRun .unguaranteed rvAndBytes)
  /-- The loop over `n` limbs under every regime: from a state that satisfies
      `RvAndLoopEntry n`, with the inputs `A` at `a1` and `B` at `a0`, the decoded program
      `rvAndLoopProg` reaches its `ret` in `rvAndLoopFuel n` steps and halts there with the
      trace `rvAndLoopLeak`; the output array at `a3` holds the limb-wise conjunction and the
      inputs are in place. -/
  loop : ∀ (r : RvRegime) (n : Nat) (A B : Fin n → BitVec 64) (b : RMState64),
    RvAndLoopEntry n b → MachineMem64.ArrAt b.mem (b.regs.get "a1") n A →
    MachineMem64.ArrAt b.mem (b.regs.get "a0") n B →
    ∃ b', (rvMach r).ReachesIn rvAndLoopProg (rvAndLoopFuel n) 0 b (rvAndLoopLeak r n b)
        (if n = 0 then 2 else 16) b'
      ∧ (rvMach r).Halts rvAndLoopProg 0 b b'
      ∧ (rvMach r).RunL (fun _ _ => True) rvAndLoopProg 0 b (rvAndLoopLeak r n b) b'
      ∧ MachineMem64.ArrAt b'.mem (b.regs.get "a3") n (fun k => A k &&& B k)
      ∧ MachineMem64.ArrAt b'.mem (b.regs.get "a1") n A
      ∧ MachineMem64.ArrAt b'.mem (b.regs.get "a0") n B
  /-- Constant time of the loop under Zkt with value-independent loads and stores, for the
      array bases and the count. -/
  loop_ct : ∀ n : Nat,
    ConstantTimeRel (fun b₁ b₂ => RvAndLoopPub b₁ b₂ ∧ RvAndLoopEntry n b₁)
      (fun b t => ∃ b', (rvMach .zktMemData).RunL (fun _ _ => True) rvAndLoopProg 0 b t b')

/-- The statements of `RvAndN` hold. -/
theorem rvAndN : RvAndN where
  mach := fun r P n s b hrel hmem hsep hidx => rv_and_mach r P n s b hrel hmem hsep hidx
  ct := mpn_and_n_rvMach_ct
  not_ct_zkt := mpn_and_n_rvMach_not_ct_zkt
  not_ct_unguaranteed := mpn_and_n_rvMach_not_ct_unguaranteed
  loop := fun r n A B b he ha hb => rv_and_loop r n A B b he ha hb
  loop_ct := mpn_and_n_loop_rvMach_ct

end Rv

/-! ## x86-64 -/

section X86

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86AsmSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86AsmSimImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB SafeW)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-- **The assembly simulations of x86-64 with a leakage trace**, for every gated body and
    every regime. -/
structure X86Sim : Prop where
  /-- A safe terminating run of the address semantics on a body in `printedAddrWB`, from a
      configuration related at entry, gives a run of the decoded function bytes at `x86Mach`
      with a leakage trace, the exit relation of `x86AsmSim` holding at its end. -/
  printed : ∀ (r : DoitRegime) (body : Lcmd), printedAddrWB body = true →
    ∀ (c c' : BitVec 64 × LstateA × Bool) (sa : AState), X86Entry body c sa →
    (x86AddrSem SafeW).Run body c c' →
    ∃ prog sa' t, (x86Mach r).decode (encodeLfundefBytes body) = some prog
      ∧ (x86Mach r).RunL (fun _ _ => True) prog 0 sa t sa'
      ∧ (x86AsmSim r).Post body c sa c' sa'
  /-- An in-bounds halting run of `x86Isa` on a virtual body that passes the gate of the
      image route, from a state related at entry, gives a run of the decoded function bytes
      of the printed body at `x86Mach` with a leakage trace, the exit relation of
      `x86ImageAsmSim` holding at its end. -/
  image : ∀ (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (outs : List String) (fn : String) (r : DoitRegime)
    (p : List LinstrRM × Lcmd), x86ImageGate frame slotArr outs p = true →
    ∀ (b t : LstateMF) (sa : AState), X86ImageEntry frame slotArr base fn p b sa →
    ∀ fuel : Nat, x86Isa.lsemFuelMemF (singletonProgM fn p.1) fuel b = some t →
    x86Isa.RunIdxOk (singletonProgM fn p.1) fuel b →
    ∃ prog sa' tr, (x86Mach r).decode (encodeLfundefBytes p.2) = some prog
      ∧ (x86Mach r).RunL (fun _ _ => True) prog 0 sa tr sa'
      ∧ (x86ImageAsmSim frame slotArr base outs fn r).Post p b sa t sa'

/-- The statements of `X86Sim` hold. -/
theorem x86Sim : X86Sim where
  printed := fun r _ hg _ _ _ hpre hrun => (x86AsmSim r).runL hg hpre hrun
  image := fun frame slotArr base outs fn r _ hg _ _ _ hpre fuel hrun hok =>
    (x86ImageAsmSim frame slotArr base outs fn r).runL hg hpre ⟨fuel, hrun, hok⟩

end X86

/-! ## The checker over an instruction set -/

section Checker

open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvSym

/-- **Soundness of the checker of a symbolic companion** `T` of an instruction set `I`: if
    `T.ownedCheckM outs B B'` accepts, every halting run of `I` on the singleton program over
    `B` from a state at pc `0` of that function is matched by a halting run on the singleton
    program over `B'` from the same state, and the end states agree on the registers `outs`,
    on the arrays and on the word memory. -/
def CheckerSound {I : Isa} (T : IsaSym I) : Prop :=
  ∀ (outs : List String) (B B' : List LinstrRM), T.ownedCheckM outs B B' = true →
    ∀ (fn : String) (s t : LstateMF), s.prog.lfn = fn → s.prog.base.reg.lpc = 0 →
    ∀ fuel : Nat, I.lsemFuelMemF (singletonProgM fn B) fuel s = some t →
    ∃ fuel' t', I.lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t'

/-- The checker of a lawful symbolic companion is sound. -/
theorem checkerSound_of_lawful {I : Isa} (T : IsaSym I) (h : T.Lawful) : CheckerSound T :=
  fun _ _ _ hc fn s t hfn hpc fuel hrun => T.ownedCheckM_sound h hc fn s t hfn hpc fuel hrun

/-- The checker of the x86-64 symbolic companion is sound. -/
theorem checkerSound_x86 : CheckerSound x86Sym :=
  checkerSound_of_lawful x86Sym x86Sym_lawful

/-- The checker of the RV64 symbolic companion is sound. -/
theorem checkerSound_rv : CheckerSound rvSym :=
  checkerSound_of_lawful rvSym rvSym_lawful

/-- **The checker over an instruction set**: soundness for every lawful symbolic companion,
    and at the x86-64 and RV64 companions. -/
structure CheckerOverIsa : Prop where
  /-- The checker of a lawful symbolic companion of any instruction set is sound. -/
  lawful : ∀ (I : Isa) (T : IsaSym I), T.Lawful → CheckerSound T
  /-- The x86-64 instance. -/
  x86 : CheckerSound x86Sym
  /-- The RV64 instance. -/
  rv : CheckerSound rvSym

/-- The statements of `CheckerOverIsa` hold. -/
theorem checkerOverIsa : CheckerOverIsa where
  lawful := fun _ T h => checkerSound_of_lawful T h
  x86 := checkerSound_x86
  rv := checkerSound_rv

end Checker

/-! ## The closing statement -/

/-- **The `mpn_and_n` body at three instruction sets**: the AArch64 and RV64 machine
    statements, the x86-64 assembly simulations and the checker over an instruction set. -/
structure MachAndN : Prop where
  /-- The body at the AArch64 machine. -/
  arm : ArmAndN
  /-- The body at the RV64 machine. -/
  rv : RvAndN
  /-- The assembly simulations of x86-64, over all gated bodies. -/
  x86 : X86Sim
  /-- The checker over an instruction set. -/
  checker : CheckerOverIsa

/-- **The closing statement of the machine programme for the `mpn_and_n` body.**

    AArch64 and RV64: under every regime the bytes of the body decode at the machine and
    their run from a related state halts in a state related to the result of the run of the
    instruction set; the bytes are constant time under `ArmRegime.dit` (a core with
    `PSTATE.DIT = 1` that meets the table `CT.ArmMnem.leaksOperands`) and under
    `RvRegime.zktMemData` (Zkt, with the assumption beyond the ratified text that the latency
    of a load or store is independent of the value transferred); they are not constant time
    under `ArmRegime.unguaranteed`, `RvRegime.zkt` and `RvRegime.unguaranteed`.

    x86-64: the assembly simulations of all gated bodies, under every `CT.DoitRegime`. The
    constant time of the x86-64 bytes of the `mpn_and_n` body is not a field; it is the
    theorem `mpn_and_n_rc_proved` of the module `Haxc.ComposeCTProved`.

    The checker: soundness for every lawful symbolic companion of an instruction set, with
    the x86-64 and RV64 instances. There is no AArch64 companion.

    The fields `mach` and `ct` at the AArch64 and RV64 machines are for the straight-line
    body of one iteration; the fields `loop` and `loop_ct` are for the loop over the limb
    count, on the decoded programs. -/
theorem mach_and_n_three_isas : MachAndN :=
  ⟨armAndN, rvAndN, x86Sim, checkerOverIsa⟩

end CatCrypt.Crypto.SecureCompilation.VIR.MachHeadline
