/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmModel

@[expose] public section

set_option autoImplicit false

/-!
# The AArch64 timing table of the owned backends

The vendor allowlist for instruction timing on AArch64. An instruction is data independent
(`ArmMnem.isDIT`) when it is on the FEAT_DIT list of the Arm A-profile architecture: the DIT
register description (AArch64 system register `DIT`, Arm A-profile architecture registers,
release 2026.06, https://developer.arm.com/documentation/ddi0601/latest/, retrieved
2026-09-28 through the mirror https://arm.jonpalmisc.com/latest_sysreg/AArch64-dit).

With `PSTATE.DIT = 1` (set by `MSR DIT, #1`; FEAT_DIT is mandatory from Armv8.4-A) the
architecture requires that "the execution time of a data-independent-time sequence of code
must be independent of all data-independent-time values" (release 2026.06). The release
2021-06 wording (ddi0595/2021-06) states the two clauses: load and store timing is
insensitive to the value of the data loaded or stored, and listed data-processing
instructions take a time independent of their register data and of the `NZCV` flags.
Addresses are not covered; the leakage model records them as address events.

Every instruction not on the list is variable time: its data operands are observable. The
divisions `UDIV` and `SDIV` are absent from the list. Branches are absent from the list and
are control transfers, whose outcome is observable as a branch event.

## Main definitions

* `ArmMnem` is one constructor per scalar A64 mnemonic the owned Arm backends emit (the
  `AInst`, `BInst` and `ABranch` alphabets, the loads and stores of the frame and of arrays),
  plus `udiv` and `sdiv`, which no owned path emits.
* `ArmMnem.isDIT`, `ArmMnem.isControl` and `ArmMnem.leaksOperands` are the table and the
  regime with `PSTATE.DIT = 1`.
* `AInst.mnem`, `BInst.mnem` and `ABranch.mnem` project the backend's instruction types onto
  the table; `BInst.mnem_leaksOperands` and `AInst.mnem_leaksOperands` state that no
  straight-line instruction the backend emits leaks its operands.
-/

namespace CatCrypt.Crypto.SecureCompilation.CT

open CatCrypt.Crypto.SecureCompilation.ARMBackend

/-- The scalar A64 mnemonics of the owned Arm backends, with the divisions. -/
inductive ArmMnem where
  | add | sub | adds | subs | adc | adcs | sbc | sbcs
  | mul | umulh
  | and | orr | eor | mov
  | lsl | lsr | ror
  | csel | movz | movk
  | ldr | str | ldp | stp
  | udiv | sdiv
  | b | bcond | cbz | cbnz | ret
  deriving DecidableEq, Repr

/-- **The FEAT_DIT table** (DIT register description, release 2026.06). An entry is `true`
    when the mnemonic is on the list:

    * `ADD`, `SUB`, `ADDS`, `SUBS`: add/subtract (shifted and extended register, immediate);
    * `ADC`, `ADCS`, `SBC`, `SBCS`: add/subtract with carry;
    * `MUL` (alias of `MADD`), `UMULH`: data processing, 3 source;
    * `AND`, `ORR`, `EOR`, and `MOV` (alias of `ORR`): logical (shifted register, immediate);
    * `LSL`, `LSR` by immediate (aliases of `UBFM`): bitfield; `ROR` by immediate (alias of
      `EXTR`): extract;
    * `CSEL`: conditional select;
    * `MOVK`: move wide; `MOVZ`: move wide, listed in the 2026.06 search summary and
      without a register data operand;
    * `LDR`, `STR`, `LDP`, `STP`: load/store register and pair, for the data loaded or
      stored.

    `UDIV`, `SDIV` and every branch are absent. -/
def ArmMnem.isDIT : ArmMnem → Bool
  | .add | .sub | .adds | .subs | .adc | .adcs | .sbc | .sbcs => true
  | .mul | .umulh => true
  | .and | .orr | .eor | .mov => true
  | .lsl | .lsr | .ror => true
  | .csel | .movz | .movk => true
  | .ldr | .str | .ldp | .stp => true
  | .udiv | .sdiv => false
  | .b | .bcond | .cbz | .cbnz | .ret => false

/-- The control transfers `B`, `B.cond`, `CBZ`, `CBNZ`, `RET`. -/
def ArmMnem.isControl : ArmMnem → Bool
  | .b | .bcond | .cbz | .cbnz | .ret => true
  | _ => false

/-- **The regime with `PSTATE.DIT = 1`**: an instruction makes its data operands observable
    when it is neither on the FEAT_DIT list nor a control transfer. -/
def ArmMnem.leaksOperands (m : ArmMnem) : Bool := !m.isDIT && !m.isControl

theorem ArmMnem.leaksOperands_iff (m : ArmMnem) :
    m.leaksOperands = true ↔ m = .udiv ∨ m = .sdiv := by
  cases m <;> decide

/-- The mnemonic of a 32-bit straight-line instruction. -/
def _root_.CatCrypt.Crypto.SecureCompilation.ARMBackend.AInst.mnem : AInst → ArmMnem
  | .add .. => .add
  | .sub .. => .sub
  | .and .. => .and
  | .orr .. => .orr
  | .eor .. => .eor
  | .lsl .. => .lsl
  | .lsr .. => .lsr
  | .ror .. => .ror
  | .mov .. => .mov

/-- The mnemonic of a 64-bit straight-line instruction. -/
def _root_.CatCrypt.Crypto.SecureCompilation.ARMBackend.BInst.mnem : BInst → ArmMnem
  | .add .. => .add
  | .sub .. => .sub
  | .adds .. => .adds
  | .adcs .. => .adcs
  | .adc .. => .adc
  | .subs .. => .subs
  | .sbcs .. => .sbcs
  | .sbc .. => .sbc
  | .mul .. => .mul
  | .umulh .. => .umulh
  | .and .. => .and
  | .orr .. => .orr
  | .eor .. => .eor
  | .csel .. => .csel
  | .movz .. => .movz
  | .movk .. => .movk
  | .mov .. => .mov
  | .lsr .. => .lsr
  | .lsl .. => .lsl

/-- The mnemonic of a control instruction, `none` for a label definition. -/
def _root_.CatCrypt.Crypto.SecureCompilation.ARMBackend.ABranch.mnem : ABranch → Option ArmMnem
  | .label _ => none
  | .b _ => some .b
  | .bcond .. => some .bcond
  | .cbnz .. => some .cbnz
  | .cbz .. => some .cbz

/-- No 32-bit straight-line instruction leaks its data operands under `PSTATE.DIT = 1`. -/
theorem AInst.mnem_leaksOperands (i : AInst) : i.mnem.leaksOperands = false := by
  cases i <;> rfl

/-- No 64-bit straight-line instruction leaks its data operands under `PSTATE.DIT = 1`. -/
theorem BInst.mnem_leaksOperands (i : BInst) : i.mnem.leaksOperands = false := by
  cases i <;> rfl

end CatCrypt.Crypto.SecureCompilation.CT
