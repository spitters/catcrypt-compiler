/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
public import CatCrypt.Crypto.SecureCompilation.VIR.X86IsaData
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.CT.Leakage

@[expose] public section

set_option autoImplicit false

/-!
# The x86 instruction set

The x86 instance `X86Isa.x86Isa` of the instruction-set record `LprogIsa.Isa`: its data is
`TwoAddrLegalize.x86Data` with the leakage regime `x86LeaksOperands`, its step is the flag
machine `evalInstrPMemF` and its branch condition is `decC`.

## Main results

* `OwnedLprogTV.decC`: the branch a conditional takes from a flag-machine state.
* `X86Isa.evalInstrPMemF_ctl`: the flag-machine step of a control instruction is the shared
  control step under `decC`.
* `X86Isa.x86LeaksOperands`: the operand leakage of an `Lprog` mnemonic base under DOITM.
* `X86Isa.x86Isa`: the x86 instruction set.
* `X86Isa.x86Isa_lsemFuelMemF`, `X86Isa.x86Isa_evalInstrPMemFk`,
  `X86Isa.x86Isa_lsemFuelMemFk`, `X86Isa.x86Isa_RunIdxOk`: the generic run, checked step,
  checked run and in-bounds run predicate at `x86Isa` are those of the flag machine.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa isCtl ctlStep)

/-- The polarity of a condition-code operand: `Z` jumps on a set zero flag, `NZ` on a
    clear one; any other operand is read as a register. -/
def ccPol : LOperand → Option Bool
  | .reg "Z" => some true
  | .reg "NZ" => some false
  | _ => none

theorem flagCondCC?_cond (c : LOperand) (l : LLabel) (tag : MemTag) :
    flagCondCC? (.Lcond c l, tag) = (ccPol c).map (fun p => (p, l)) := by
  unfold flagCondCC? ccPol
  split <;> simp_all

/-- The branch a conditional takes from state `s`. -/
def decC (s : LstateMF) (c : LOperand) : Bool :=
  match ccPol c with
  | some pol => s.zf == pol
  | none => condNZ s.prog.base c

theorem evalInstrPMemF_cond (P : LprogM) (c : LOperand) (l : LLabel) (tag : MemTag)
    (s : LstateMF) :
    evalInstrPMemF P (.Lcond c l, tag) s =
      if decC s c = true then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else some { s with prog := { s.prog with base := s.prog.base.nextPc } } := by
  unfold decC
  cases hcc : ccPol c with
  | some pol =>
      unfold evalInstrPMemF
      simp only [cmpArgs?, movRegArgs?, flagCondCC?_cond, hcc]
      simp [beq_iff_eq]
  | none =>
      have hf : flagCondCC? (LinstrR.Lcond c l, tag) = none := by
        rw [flagCondCC?_cond, hcc]; rfl
      rw [evalInstrPMemF_delegate P _ s rfl rfl hf rfl rfl rfl]
      simp only [evalInstrPMemL]
      split <;> simp

theorem evalInstrPMemF_goto (P : LprogM) (x : String) (l : LLabel) (tag : MemTag)
    (s : LstateMF) :
    evalInstrPMemF P (.Lgoto (x, l), tag) s =
      if x = P.lfn then (evalJumpMem P l s.prog).map (fun p => { s with prog := p })
      else none := by
  rw [evalInstrPMemF_delegate P _ s rfl rfl rfl rfl rfl rfl]
  simp only [evalInstrPMemL]
  split <;> simp

/-- The x86 step of a control instruction is the shared control step under `decC`. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa.evalInstrPMemF_ctl
    (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (h : isCtl i.fst = true) : evalInstrPMemF P i s = ctlStep decC P i s := by
  obtain ⟨x, tag⟩ := i
  cases x with
  | Llabel k l =>
      rw [evalInstrPMemF_delegate P _ s rfl rfl rfl rfl rfl rfl]
      rfl
  | Lcond c l => rw [evalInstrPMemF_cond]; rfl
  | Lgoto t =>
      obtain ⟨x, l⟩ := t
      rw [evalInstrPMemF_goto]; rfl
  | _ => simp [isCtl] at h

/-- The table mnemonic of an AT&T base mnemonic of `LprogAsmPrinter.attBase`, `none` for one
    outside that table. -/
def _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa.attMnem? :
    String → Option CT.X86Mnem
  | "add" => some .add
  | "sub" => some .sub
  | "adc" => some .adc
  | "sbb" => some .sbb
  | "and" => some .and
  | "or" => some .or
  | "xor" => some .xor
  | "andn" => some .andn
  | "shl" => some .shl
  | "shr" => some .shr
  | "imul" => some .imul
  | "mov" => some .mov
  | "cmp" => some .cmp
  | "test" => some .test
  | "adcx" => some .adcx
  | "adox" => some .adox
  | "cmove" | "cmovne" | "cmovb" | "cmovae" | "cmovl" | "cmovge" => some .cmovcc
  | "lea" => some .lea
  | _ => none

/-- The table mnemonic of an `Lprog` mnemonic base: the AT&T mnemonic the printer emits for
    it (`LprogAsmPrinter.attBase`), read in the table. -/
def _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa.x86MnemOfBase (base : String) :
    Option CT.X86Mnem :=
  (LprogAsmPrinter.attBase base).bind X86Isa.attMnem?

/-- The x86 leakage regime under DOITM: `CT.DoitRegime.leaksOperands .doitm` at the table
    mnemonic of the base, every operand observable for a base the printer does not name. -/
def _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa.x86LeaksOperands
    (base : String) : Bool :=
  ((X86Isa.x86MnemOfBase base).map (CT.DoitRegime.leaksOperands .doitm)).getD true

/-- **The x86 instruction set**: the data `TwoAddrLegalize.x86Data` with the leakage regime
    `x86LeaksOperands`, the flag machine `evalInstrPMemF` with the branch condition `decC`. -/
def _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa.x86Isa : Isa where
  toIsaData := { TwoAddrLegalize.x86Data with leaksOperands := X86Isa.x86LeaksOperands }
  step := evalInstrPMemF
  condEval := decC
  step_ctl := X86Isa.evalInstrPMemF_ctl

open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)

/-- The generic run at `x86Isa` is `lsemFuelMemF`, by unfolding both definitions. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa.x86Isa_lsemFuelMemF :
    x86Isa.lsemFuelMemF = lsemFuelMemF := by
  delta Isa.lsemFuelMemF lsemFuelMemF; rfl

/-- The generic checked step at `x86Isa` is `evalInstrPMemFk`. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa.x86Isa_evalInstrPMemFk :
    x86Isa.evalInstrPMemFk = JasminLsemMemChecked.evalInstrPMemFk := rfl

/-- The generic checked run at `x86Isa` is `lsemFuelMemFk`, by unfolding both
    definitions. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa.x86Isa_lsemFuelMemFk :
    x86Isa.lsemFuelMemFk = JasminLsemMemChecked.lsemFuelMemFk := by
  delta Isa.lsemFuelMemFk JasminLsemMemChecked.lsemFuelMemFk; rfl

/-- The generic in-bounds run predicate at `x86Isa` is `RunIdxOk`, by unfolding both
    definitions. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa.x86Isa_RunIdxOk :
    x86Isa.RunIdxOk = JasminLsemMemChecked.RunIdxOk := by
  delta Isa.RunIdxOk JasminLsemMemChecked.RunIdxOk; rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
