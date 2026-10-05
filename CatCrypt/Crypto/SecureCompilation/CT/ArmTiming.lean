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
must be independent of all data-independent-time values" (release 2026.06), and gives "the
list of data-independent-time instructions" by encoding group. The earlier wording (DIT
register description dated 2024-03-26, mirror https://df.lth.se/~getz/ARM/SysReg/AArch64-dit.html,
retrieved 2026-10-05) states two clauses: "the timing of every load and store instruction is
insensitive to the value of the data being loaded or stored", and certain data-processing
instructions take "a time which is independent of the values of the data supplied in any of
its registers" and of "the values of the NZCV flags". Neither wording covers the address of
a load or store; the leakage model records it as an address event.

Every instruction not on the list is variable time: its data operands are observable. The
divisions `UDIV` and `SDIV` are absent from the list. Branches are absent from the list and
are control transfers, whose outcome is observable as a branch event. `MOVZ` is absent from
the list, whose group "Move wide (immediate)" names `MOVK` alone; it reads no register and
no flag, and the table `ArmMnem.isDIT` holds it on that ground (`ArmMnem.readsNoData`),
separately from the list `ArmMnem.isDITListed`.

## Main definitions

* `ArmMnem` is one constructor per scalar A64 mnemonic the owned Arm backends emit (the
  `AInst`, `BInst` and `ABranch` alphabets, the loads and stores of the frame and of arrays),
  plus `udiv` and `sdiv`, which no owned path emits.
* `ArmMnem.isDITListed` is the FEAT_DIT list and `ArmMnem.readsNoData` the mnemonics without
  a data operand; `ArmMnem.isDIT`, `ArmMnem.isControl` and `ArmMnem.leaksOperands` are the
  table and the regime with `PSTATE.DIT = 1`; `ArmMnem.isMem` is the mnemonics with a memory
  access.
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

/-- **The FEAT_DIT list** (DIT register description, release 2026.06, "The list of
    data-independent-time instructions is"). An entry is `true` when the mnemonic is on the
    list, under the group named:

    * `ADD`, `SUB`, `ADDS`, `SUBS`: "Add/subtract (immediate)", "Add/subtract (shifted
      register)", "Add/subtract (extended register)";
    * `ADC`, `ADCS`, `SBC`, `SBCS`: "Add/subtract (with carry)";
    * `MUL` (alias of `MADD`), `UMULH`: "Data-processing (3 source)";
    * `AND`, `ORR`, `EOR`, and `MOV` (alias of `ORR`): "Logical (shifted register)",
      "Logical (immediate)";
    * `LSL`, `LSR` by immediate (aliases of `UBFM`): "Bitfield"; `ROR` by immediate (alias of
      `EXTR`): "Extract";
    * `CSEL`: "Conditional select";
    * `MOVK`: "Move wide (immediate)", whose only entry it is;
    * `LDR`, `STR`: "Load/store register (unsigned immediate)", "Load/store register
      (register offset)"; `LDP`, `STP`: "Load/store register pair (offset)". The guarantee is
      for the data loaded or stored.

    `MOVZ`, `UDIV`, `SDIV` and every branch are absent. -/
def ArmMnem.isDITListed : ArmMnem → Bool
  | .add | .sub | .adds | .subs | .adc | .adcs | .sbc | .sbcs => true
  | .mul | .umulh => true
  | .and | .orr | .eor | .mov => true
  | .lsl | .lsr | .ror => true
  | .csel | .movk => true
  | .movz => false
  | .ldr | .str | .ldp | .stp => true
  | .udiv | .sdiv => false
  | .b | .bcond | .cbz | .cbnz | .ret => false

/-- The mnemonics that read no register and no flag: `MOVZ Xd, #imm16` writes a constant of
    the instruction encoding. Such an instruction has no data operand to make observable. -/
def ArmMnem.readsNoData : ArmMnem → Bool
  | .movz => true
  | _ => false

/-- **The FEAT_DIT table**: a mnemonic of the FEAT_DIT list `ArmMnem.isDITListed`, or one
    that reads no data (`ArmMnem.readsNoData`). `MOVZ` is in the table by the second clause
    only: the list of release 2026.06 does not name it. -/
def ArmMnem.isDIT : ArmMnem → Bool
  | .add | .sub | .adds | .subs | .adc | .adcs | .sbc | .sbcs => true
  | .mul | .umulh => true
  | .and | .orr | .eor | .mov => true
  | .lsl | .lsr | .ror => true
  | .csel | .movz | .movk => true
  | .ldr | .str | .ldp | .stp => true
  | .udiv | .sdiv => false
  | .b | .bcond | .cbz | .cbnz | .ret => false

/-- The table is the FEAT_DIT list with the mnemonics that read no data. -/
theorem ArmMnem.isDIT_eq (m : ArmMnem) : m.isDIT = (m.isDITListed || m.readsNoData) := by
  cases m <;> rfl

/-- `MOVZ` is the only mnemonic of the table outside the FEAT_DIT list. -/
theorem ArmMnem.isDIT_not_listed_iff (m : ArmMnem) :
    (m.isDIT = true ∧ m.isDITListed = false) ↔ m = .movz := by
  cases m <;> decide

/-- The mnemonics with a memory access: `LDR`, `STR`, `LDP`, `STP`. The address of the access
    is outside the FEAT_DIT guarantee and is an address event of the leakage model. -/
def ArmMnem.isMem : ArmMnem → Bool
  | .ldr | .str | .ldp | .stp => true
  | _ => false

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
