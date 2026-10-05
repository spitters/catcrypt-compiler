/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

@[expose] public section

set_option autoImplicit false

/-!
# The x86 instruction-set record whose invariant touch is the keep marker

`x86DataKeep` is the x86 instruction-set data `x86Data` with the invariant touch of a loop
replaced by the keep marker `LprogIsa.keepTouch`; every other field is the field of
`x86Data`. `x86IsaKeep` is the instruction set `x86Isa.withKeep` with the same replacement in
its data: its step on a keep marker is the no-op `keepStep`, its step on every other
instruction is the flag machine `evalInstrPMemF`, and its own invariant touch is an
instruction it steps as a no-op. The records `x86Data` and `x86Isa` are not changed, and no
definition that reads them mentions the records of this module.

The data of `x86IsaKeep` carries the leakage regime of `x86Isa`, so it is not `x86DataKeep`;
the two records have the same loop guards and the same invariant touch, which are the fields
a loop frame reads (`JasminLprogExport.regsLoopFrameI_congr` of
`VIR.JasminLprogExport.ExportLoopsJIsa`, which this module does not import).

The keep marker reaches the byte stream of the checked encoder without bytes: with one
destination and two sources it passes `encodableLinstrR` at every operand. With one
register destination and one register source, `LprogBytes.carriesNoBytes` reads an `Lopn`
through its self-shift arm, which does not accept the mnemonic `KEEP`.

## Main definitions

* `x86DataKeep`: the x86 data with the keep marker as invariant touch.
* `x86IsaKeep`: the x86 instruction set that steps the keep marker as a no-op, with the
  keep marker as invariant touch.

## Main results

* `x86DataKeep_invTouch`, `x86DataKeep_loopGuard`, `x86DataKeep_zeroTripGuard`,
  `x86DataKeep_toIsaAbi` and the other data equations.
* `x86IsaKeep_step_keep`, `x86IsaKeep_step_of_not_keep`, `x86IsaKeep_step_invTouch`: the
  step of `x86IsaKeep`.
* `Isa.withKeep_lsemFuelMemF`, `x86IsaKeep_lsemFuelMemF`: on a program without keep markers
  the run is the run of the underlying instruction set.
* `encodableLinstrR_keep`, `encodableLinstrR_keepTouch`: the checked encoder accepts a keep
  marker.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.Isa

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

variable (I : Isa)

/-- On a program without keep markers the run of `I.withKeep` is the run of `I`. -/
theorem withKeep_lsemFuelMemF (P : LprogM) (hP : ∀ i ∈ P.body, isKeep i.fst = false) :
    ∀ (fuel : Nat) (s : LstateMF),
      I.withKeep.lsemFuelMemF P fuel s = I.lsemFuelMemF P fuel s
  | 0, s => by
      cases hf : findInstrMem P s.prog <;> simp only [lsemFuelMemF, hf]
  | fuel + 1, s => by
      cases hf : findInstrMem P s.prog with
      | none => simp only [lsemFuelMemF, hf]
      | some i =>
          have hi : i ∈ P.body := by
            unfold findInstrMem at hf
            split at hf
            · exact List.mem_of_getElem? hf
            · cases hf
          simp only [lsemFuelMemF, hf, I.withKeep_step_of_not_keep P i s (hP i hi)]
          cases I.step P i s with
          | none => rfl
          | some s' => exact withKeep_lsemFuelMemF P hP fuel s'

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.Isa

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)

/-! ## The data record -/

/-- **The x86 instruction-set data with the keep marker as invariant touch**: `x86Data`
    with `invTouch := keepTouch`. -/
@[reducible] def x86DataKeep : IsaData := { x86Data with invTouch := keepTouch }

/-- The invariant touch of `x86DataKeep` is the keep marker. -/
theorem x86DataKeep_invTouch (ctr r : String) :
    x86DataKeep.invTouch ctr r = keepTouch ctr r := rfl

theorem x86DataKeep_toIsaAbi : x86DataKeep.toIsaAbi = x86Data.toIsaAbi := rfl

theorem x86DataKeep_loopGuard : x86DataKeep.loopGuard = x86Data.loopGuard := rfl

theorem x86DataKeep_zeroTripGuard : x86DataKeep.zeroTripGuard = x86Data.zeroTripGuard := rfl

theorem x86DataKeep_tied : x86DataKeep.tied = x86Data.tied := rfl

theorem x86DataKeep_commutes : x86DataKeep.commutes = x86Data.commutes := rfl

theorem x86DataKeep_tieScratch : x86DataKeep.tieScratch = x86Data.tieScratch := rfl

theorem x86DataKeep_copyMnemonic : x86DataKeep.copyMnemonic = x86Data.copyMnemonic := rfl

theorem x86DataKeep_leaksOperands : x86DataKeep.leaksOperands = x86Data.leaksOperands := rfl

theorem x86DataKeep_supports : x86DataKeep.supports = x86Data.supports := rfl

theorem x86DataKeep_implicitReads : x86DataKeep.implicitReads = x86Data.implicitReads := rfl

/-! ## The instruction set -/

/-- **The x86 instruction set with the keep marker**: `x86Isa.withKeep`, which steps a keep
    marker as the no-op `keepStep` and every other instruction as `evalInstrPMemF`, with
    the keep marker as the invariant touch of its data. -/
def x86IsaKeep : Isa := { x86Isa.withKeep with invTouch := keepTouch }

theorem x86IsaKeep_step : x86IsaKeep.step = x86Isa.withKeep.step := rfl

theorem x86IsaKeep_condEval : x86IsaKeep.condEval = decC := rfl

/-- The invariant touch of `x86IsaKeep` is the keep marker. -/
theorem x86IsaKeep_invTouch (ctr r : String) :
    x86IsaKeep.invTouch ctr r = keepTouch ctr r := rfl

theorem x86IsaKeep_invTouch_eq : x86IsaKeep.invTouch = x86DataKeep.invTouch := rfl

theorem x86IsaKeep_loopGuard : x86IsaKeep.loopGuard = x86DataKeep.loopGuard := rfl

theorem x86IsaKeep_zeroTripGuard : x86IsaKeep.zeroTripGuard = x86DataKeep.zeroTripGuard := rfl

theorem x86IsaKeep_toIsaAbi : x86IsaKeep.toIsaAbi = x86Isa.toIsaAbi := rfl

theorem x86IsaKeep_leaksOperands : x86IsaKeep.leaksOperands = x86Isa.leaksOperands := rfl

/-- **The keep marker is a no-op of `x86IsaKeep`**: the step advances the program counter
    and changes nothing else. -/
theorem x86IsaKeep_step_keep (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (h : isKeep i.fst = true) : x86IsaKeep.step P i s = some (keepStep s) :=
  x86Isa.withKeep_step_keep P i s h

/-- On an instruction other than a keep marker the step of `x86IsaKeep` is the flag machine
    `evalInstrPMemF`. -/
theorem x86IsaKeep_step_of_not_keep (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (h : isKeep i.fst = false) : x86IsaKeep.step P i s = evalInstrPMemF P i s :=
  x86Isa.withKeep_step_of_not_keep P i s h

/-- The invariant touch of `x86IsaKeep` is an instruction it steps as a no-op. -/
theorem x86IsaKeep_step_invTouch (P : LprogM) (ctr r : String) (tag : MemTag)
    (s : LstateMF) :
    x86IsaKeep.step P (x86IsaKeep.invTouch ctr r, tag) s = some (keepStep s) :=
  x86IsaKeep_step_keep P _ s rfl

/-- The run of `x86IsaKeep` is the run of `x86Isa.withKeep`. -/
theorem x86IsaKeep_lsemFuelMemF_withKeep (P : LprogM) :
    ∀ (fuel : Nat) (s : LstateMF),
      x86IsaKeep.lsemFuelMemF P fuel s = x86Isa.withKeep.lsemFuelMemF P fuel s
  | 0, _ => rfl
  | fuel + 1, s => by
      cases hf : findInstrMem P s.prog with
      | none => simp only [Isa.lsemFuelMemF, hf]
      | some i =>
          simp only [Isa.lsemFuelMemF, hf, x86IsaKeep_step]
          cases x86Isa.withKeep.step P i s with
          | none => rfl
          | some s' => exact x86IsaKeep_lsemFuelMemF_withKeep P fuel s'

/-- **On a program without keep markers the run of `x86IsaKeep` is the x86 run**
    `lsemFuelMemF`. -/
theorem x86IsaKeep_lsemFuelMemF (P : LprogM) (hP : ∀ i ∈ P.body, isKeep i.fst = false)
    (fuel : Nat) (s : LstateMF) :
    x86IsaKeep.lsemFuelMemF P fuel s = lsemFuelMemF P fuel s := by
  rw [x86IsaKeep_lsemFuelMemF_withKeep, x86Isa.withKeep_lsemFuelMemF P hP,
    x86Isa_lsemFuelMemF]

/-! ## The checked encoder -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes in
/-- **The checked encoder accepts a keep marker** with one destination and two sources, at
    every operand: it carries no bytes by construction. The operands of a keep marker on
    registers, on a register and a spill slot and on two spill slots have this shape. -/
theorem encodableLinstrR_keep (frame spillW qsaveB : Nat) (d a b : LOperand) :
    encodableLinstrR frame spillW (.Lopn [d] "KEEP" [a, b]) qsaveB = true := by
  have h : carriesNoBytes (.Lopn [d] "KEEP" [a, b]) = true := by
    simp [carriesNoBytes]
  simp [encodableLinstrR, h]

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes in
/-- The checked encoder accepts the keep marker `keepTouch ctr r`. -/
theorem encodableLinstrR_keepTouch (frame spillW qsaveB : Nat) (ctr r : String) :
    encodableLinstrR frame spillW (keepTouch ctr r) qsaveB = true :=
  encodableLinstrR_keep frame spillW qsaveB _ _ _

end CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
