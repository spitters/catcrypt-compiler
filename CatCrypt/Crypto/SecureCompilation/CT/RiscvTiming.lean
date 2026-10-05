/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvModel64

@[expose] public section

set_option autoImplicit false

/-!
# The RV64 timing table of the owned backends

The vendor allowlist for instruction timing on RV64. An instruction is data independent
(`RvMnem.isZkt`) when it is in the Zkt subset, "Data Independent Execution Latency Subset:
Zkt", of the RISC-V Cryptography Extensions, Volume I: Scalar & Entropy Source Instructions,
version 1.0.1 (https://github.com/riscv/riscv-crypto, `doc/scalar/riscv-crypto-scalar-zkt.adoc`,
retrieved 2026-10-05). On an implementation of Zkt, the listed instructions "do not leak
information about processed secret data ... through differences in execution latency".

The Zkt list excludes loads, stores and conditional branches, and division ("Cryptographers
typically assume division to be variable-time"). The table therefore classes the loads and
stores as variable time; the branches are control transfers, whose outcome is observable as
a branch event.

## Main definitions

* `RvMnem` is one constructor per RV64 mnemonic of the owned RISC-V backends (the `RInst64`
  alphabet, its pseudo-instructions `LI` and `MV`, the loads, stores and branches), plus
  `div` and `divu`, which no owned path emits.
* `RvMnem.isZkt`, `RvMnem.isControl` and `RvMnem.leaksOperands` are the table and the regime
  of an implementation of Zkt.
* `RInst64.mnem` projects the backend's instruction type onto the table;
  `RInst64.mnem_leaksOperands` states that no instruction of `RInst64` leaks its operands.
-/

namespace CatCrypt.Crypto.SecureCompilation.CT

open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-- The RV64 mnemonics of the owned RISC-V backends, with the divisions. `li` and `mv` are
    the assembler pseudo-instructions of `RInst64`. -/
inductive RvMnem where
  | add | sub | sltu | and | or | xor | mul | mulhu
  | li | mv | srli | slli
  | ld | sd
  | div | divu
  | beq | bne | jal | jalr
  deriving DecidableEq, Repr

/-- **The Zkt table** (RISC-V Cryptography Extensions 1.0.1, Zkt). An entry is `true` when
    the mnemonic is in the subset:

    * `ADD`, `SUB`, `SLTU`, `AND`, `OR`, `XOR`, `SRLI`, `SLLI`: RVI base;
    * `MUL`, `MULHU`: RVM;
    * `LI`: expands to `LUI` and `ADDI` (with `SLLI` for a 64-bit constant), all RVI base
      entries; `MV`: expands to `ADDI rd, rs, 0`, an RVI base entry (`C.MV` in RVC).

    The loads and stores `LD`, `SD`, the divisions `DIV`, `DIVU` and the control transfers are
    not in the subset. -/
def RvMnem.isZkt : RvMnem → Bool
  | .add | .sub | .sltu | .and | .or | .xor | .srli | .slli => true
  | .mul | .mulhu => true
  | .li | .mv => true
  | .ld | .sd => false
  | .div | .divu => false
  | .beq | .bne | .jal | .jalr => false

/-- The control transfers `BEQ`, `BNE`, `JAL`, `JALR`. -/
def RvMnem.isControl : RvMnem → Bool
  | .beq | .bne | .jal | .jalr => true
  | _ => false

/-- **The regime of an implementation of Zkt**: an instruction makes its data operands
    observable when it is neither in Zkt nor a control transfer. -/
def RvMnem.leaksOperands (m : RvMnem) : Bool := !m.isZkt && !m.isControl

theorem RvMnem.leaksOperands_iff (m : RvMnem) :
    m.leaksOperands = true ↔ m = .ld ∨ m = .sd ∨ m = .div ∨ m = .divu := by
  cases m <;> decide

/-- The mnemonic of an RV64 instruction of the straight-line alphabet. -/
def _root_.CatCrypt.Crypto.SecureCompilation.RISCVBackend.RInst64.mnem : RInst64 → RvMnem
  | .add .. => .add
  | .sub .. => .sub
  | .sltu .. => .sltu
  | .and .. => .and
  | .or .. => .or
  | .xor .. => .xor
  | .mul .. => .mul
  | .mulhu .. => .mulhu
  | .li .. => .li
  | .mv .. => .mv
  | .srli .. => .srli
  | .slli .. => .slli

/-- No instruction of `RInst64` leaks its data operands under Zkt. -/
theorem RInst64.mnem_leaksOperands (i : RInst64) : i.mnem.leaksOperands = false := by
  cases i <;> rfl

end CatCrypt.Crypto.SecureCompilation.CT
