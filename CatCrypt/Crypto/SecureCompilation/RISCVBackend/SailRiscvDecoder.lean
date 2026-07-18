/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-!
# sail-riscv decoder round-trip: `decode (encode i) ≡ i` (#535 sub-2)

`RiscvEncoder.lean` is the owned `RInst → machine-byte` encoder. Its trust edge
is *differential*: each output word is pinned (`as` + `objdump`) to what the GNU
RISC-V assembler produces for the same mnemonic (`bench/riscv_compare/`). That
makes `as`'s unverified encoder part of the trusted base.

This module replaces the differential edge for the emitted RV64I subset with a
**round-trip** against the RISC-V *decoder* discipline: a Lean decoder
`riscvDecode` that recovers the `(funct7, rs2/shamt, rs1, funct3, rd, opcode)`
fields from a 32-bit instruction word and reconstructs the `RInst`, transcribed
faithfully from the official
[`rems-project/sail-riscv`](https://github.com/rems-project/sail-riscv)
`encdec` mapping clauses (`model/extensions/I/base_insts.sail` for
`RTYPE`/`RTYPEW`/`SHIFTIWOP`/`ITYPE`, `model/core/regs.sail` for `encdec_reg`),
and a proof that

```
riscvDecode (encodeWord i) = some i      -- for every RInst the backend emits
```

Because the decoder is the sail-riscv field split (each base instruction is a
fixed bit-concatenation `funct7 @ rs2 @ rs1 @ funct3 @ rd @ opcode`, the sail
`@`-mapping read backwards), `decode (encode i)` recovering exactly the `RInst`
`i` means the encoder produces a word the authoritative decoder maps back to the
same instruction — the encoder's bytes are *proved* to be the right encoding,
not merely matched to `as`.

## Honest scope — what is and is not round-trip-proved

RV64 base is a **clean ISA**: fixed 32-bit instructions, no prefixes / ModRM /
SIB / displacement variants (contrast the x86 `SailX86Decoder`, where only the
register-direct GP forms round-trip and the VEX/ADX/memory forms stay
gas-pinned). So **every** instruction the owned RISC-V backend emits is
round-trip-proved here:

* R-type ALU: `ADDW`/`SUBW` (`RTYPEW`, opcode `0x3b`), `AND`/`OR`/`XOR`
  (`RTYPE`, opcode `0x33`) — `roundtrip_addw`/… ;
* `*IW` shifts: `SLLIW`/`SRLIW` (`SHIFTIWOP`, opcode `0x1b`, 5-bit shamt) —
  `roundtrip_slliw`/`roundtrip_srliw` ;
* `MV` = `ADDI rd, rs, 0` (`ITYPE`, opcode `0x13`) — `roundtrip_mv`.

The capstone `roundtrip_RInst` quantifies over **all** `RInst` (with the
register-name well-formedness side-condition the backend's register pool
satisfies). The only ceiling vs the x86 line is honest and structural: the
`*W`-shift `shamt` is 5-bit, so the round-trip is stated for shift counts
`< 32` (`as` rejects `slliw rd,rs,32` likewise); the ChaCha rotate emits only
counts in `{7, 8, 12, 16, 20, 24, 25}`, all `< 32`.

**No instruction the RISC-V backend emits lacks a sail-riscv `encdec` clause** —
the base subset is in the official RV64I base model, and the single-instruction
`Zbb RORIW` (opcode `0x1b`, funct3 `5`, funct7 `0x30`) — emitted by the Zbb
SHA-256 lowering to drop each rotate from three instructions to one — is
round-trip-proved here too (`roundtrip_roriw`, distinguished from base `SRLIW` by
funct7 `0x30` vs `0x00`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder

/-! ## 1. Field extraction (sail-riscv decode discipline)

These transcribe the field splits the sail `encdec` mapping applies in reverse:
each base instruction word is `funct7[31:25] @ rs2[24:20] @ rs1[19:15] @
funct3[14:12] @ rd[11:7] @ opcode[6:0]`. The `*IW` shifts use `shamt[24:20]`
(5-bit) in the `rs2` slot; the `ITYPE` immediate is `imm[31:20]` (12-bit). -/

/-- `opcode` slice (bits 6:0). -/
def sOpcode (w : BitVec 32) : BitVec 7 := w.extractLsb' 0 7
/-- `rd` slice (bits 11:7). -/
def sRd (w : BitVec 32) : BitVec 5 := w.extractLsb' 7 5
/-- `funct3` slice (bits 14:12). -/
def sFunct3 (w : BitVec 32) : BitVec 3 := w.extractLsb' 12 3
/-- `rs1` slice (bits 19:15). -/
def sRs1 (w : BitVec 32) : BitVec 5 := w.extractLsb' 15 5
/-- `rs2` / `shamt` slice (bits 24:20). -/
def sRs2 (w : BitVec 32) : BitVec 5 := w.extractLsb' 20 5
/-- `funct7` slice (bits 31:25). -/
def sFunct7 (w : BitVec 32) : BitVec 7 := w.extractLsb' 25 7
/-- The 12-bit `ITYPE` immediate slice (bits 31:20). -/
def sImm12 (w : BitVec 32) : BitVec 12 := w.extractLsb' 20 12

/-- `opcode` field as a `Nat` (for the decode dispatch). -/
def fOpcode (w : BitVec 32) : Nat := (sOpcode w).toNat
/-- `rd` field as a `Nat`. -/
def fRd (w : BitVec 32) : Nat := (sRd w).toNat
/-- `funct3` field as a `Nat`. -/
def fFunct3 (w : BitVec 32) : Nat := (sFunct3 w).toNat
/-- `rs1` field as a `Nat`. -/
def fRs1 (w : BitVec 32) : Nat := (sRs1 w).toNat
/-- `rs2` / `shamt` field as a `Nat`. -/
def fRs2 (w : BitVec 32) : Nat := (sRs2 w).toNat
/-- `funct7` field as a `Nat`. -/
def fFunct7 (w : BitVec 32) : Nat := (sFunct7 w).toNat
/-- The 12-bit `ITYPE` immediate field as a `Nat`. -/
def fImm12 (w : BitVec 32) : Nat := (sImm12 w).toNat

/-! ## 2. Register number → ABI name (inverse of `RiscvEncoder.regNum`)

The inverse of `regNum` on the names the backend emits, transcribed from sail
`reg_abi_name_raw`. The backend's allocation only ever produces `zero`,
`a0..a7`, `t0..t6`, so we invert exactly those rows; the round-trip's
side-condition `regName (regNum r) = r` holds for each. -/
def regName : Nat → String
  | 0 => "zero"
  | 1 => "ra"  | 2 => "sp"  | 3 => "gp"  | 4 => "tp"
  | 5 => "t0"  | 6 => "t1"  | 7 => "t2"
  | 8 => "s0"  | 9 => "s1"
  | 10 => "a0" | 11 => "a1" | 12 => "a2" | 13 => "a3"
  | 14 => "a4" | 15 => "a5" | 16 => "a6" | 17 => "a7"
  | 18 => "s2" | 19 => "s3" | 20 => "s4" | 21 => "s5"
  | 22 => "s6" | 23 => "s7" | 24 => "s8" | 25 => "s9"
  | 26 => "s10" | 27 => "s11"
  | 28 => "t3" | 29 => "t4" | 30 => "t5" | _ => "t6"

/-! ## 3. The decoder

`riscvDecode` dispatches on the `(opcode, funct3, funct7)` triple per the sail
`encdec` clauses, recovers the register numbers, and rebuilds the `RInst` with
the ABI names. The `*W`-shift arms read the 5-bit `shamt`; `MV` decodes the
`ADDI rd, rs, 0` pseudo-op (`opcode 0x13`, `funct3 0`, `imm 0`). -/

/-- Decode a 32-bit RV64 instruction word back to an `RInst`, per the sail-riscv
    `encdec` clauses for the emitted RV64I subset. Returns `none` for a word
    outside the emitted subset. -/
def riscvDecode (w : BitVec 32) : Option RInst :=
  let rd := fRd w; let rs1 := fRs1 w; let rs2 := fRs2 w
  let f3 := fFunct3 w; let f7 := fFunct7 w
  match fOpcode w, f3, f7 with
  -- RTYPEW (opcode 0x3b): ADDW (f3=0,f7=0), SUBW (f3=0,f7=0x20)
  | 0x3b, 0b000, 0x00 => some (.addw (regName rd) (regName rs1) (regName rs2))
  | 0x3b, 0b000, 0x20 => some (.subw (regName rd) (regName rs1) (regName rs2))
  -- RTYPE (opcode 0x33): AND (f3=7), OR (f3=6), XOR (f3=4); all f7=0
  | 0x33, 0b111, 0x00 => some (.and (regName rd) (regName rs1) (regName rs2))
  | 0x33, 0b110, 0x00 => some (.or  (regName rd) (regName rs1) (regName rs2))
  | 0x33, 0b100, 0x00 => some (.xor (regName rd) (regName rs1) (regName rs2))
  -- SHIFTIWOP (opcode 0x1b): SLLIW (f3=1), SRLIW (f3=5); f7=0, shamt in rs2 slot
  | 0x1b, 0b001, 0x00 => some (.slliw (regName rd) (regName rs1) rs2)
  | 0x1b, 0b101, 0x00 => some (.srliw (regName rd) (regName rs1) rs2)
  -- RORIW (Zbb, opcode 0x1b): f3=5, f7=0x30, shamt in rs2 slot (distinguished from
  -- SRLIW by funct7; sail ZBB encdec)
  | 0x1b, 0b101, 0x30 => some (.roriw (regName rd) (regName rs1) rs2)
  -- ITYPE ADDI (opcode 0x13, f3=0): MV pseudo when the 12-bit imm field is 0
  | 0x13, 0b000, _ =>
      if fImm12 w = 0 then some (.mv (regName rd) (regName rs1)) else none
  | _, _, _ => none

/-! ## 4. Field-extraction round-trip (`bv_decide`, the inverse of the sail `@`)

Each `encR`/`encI` word is the `BitVec.append` of its width-typed fields (the
sail `@` operator), so slicing the word at each field's bit range recovers that
field **exactly**, with no side condition — a pure fixed-width fact `bv_decide`
discharges by bit-blasting. These are the inverse of the sail `encdec` concat. -/

/-- The six R-type slices of `encR` recover the six fields exactly (sail `@`⁻¹). -/
theorem encR_slices (funct7 : BitVec 7) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3)
    (rd : BitVec 5) (opcode : BitVec 7) :
    sOpcode (encR funct7 rs2 rs1 funct3 rd opcode) = opcode ∧
    sRd     (encR funct7 rs2 rs1 funct3 rd opcode) = rd ∧
    sFunct3 (encR funct7 rs2 rs1 funct3 rd opcode) = funct3 ∧
    sRs1    (encR funct7 rs2 rs1 funct3 rd opcode) = rs1 ∧
    sRs2    (encR funct7 rs2 rs1 funct3 rd opcode) = rs2 ∧
    sFunct7 (encR funct7 rs2 rs1 funct3 rd opcode) = funct7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sOpcode, sRd, sFunct3, sRs1, sRs2, sFunct7, encR] <;> bv_decide

/-- The five I-type slices of `encI` recover the five fields exactly. -/
theorem encI_slices (imm : BitVec 12) (rs1 : BitVec 5) (funct3 : BitVec 3)
    (rd : BitVec 5) (opcode : BitVec 7) :
    sOpcode (encI imm rs1 funct3 rd opcode) = opcode ∧
    sRd     (encI imm rs1 funct3 rd opcode) = rd ∧
    sFunct3 (encI imm rs1 funct3 rd opcode) = funct3 ∧
    sRs1    (encI imm rs1 funct3 rd opcode) = rs1 ∧
    sImm12  (encI imm rs1 funct3 rd opcode) = imm := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sOpcode, sRd, sFunct3, sRs1, sImm12, encI] <;> bv_decide

/-! ## 5. The register-name round-trip side-condition

`regName` inverts `reg5 ∘ regNum` on the names the backend allocates (`zero`,
`a0..a7`, `t0..t6`): `regName (reg5 r).toNat = r` for each. The list below is the
backend's GP pool (`RiscvAsmPrinter.gpPool`) plus `zero`. -/

/-- The register names the backend's allocator emits (sail ABI names). -/
def emittedRegs : List String :=
  ["zero", "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7",
   "t0", "t1", "t2", "t3", "t4", "t5", "t6"]

/-- `regName` inverts `reg5 ∘ regNum` on every emitted register name. -/
theorem regName_reg5 (r : String) (h : r ∈ emittedRegs) :
    regName (reg5 r).toNat = r := by
  fin_cases h <;> rfl

/-- The `BitVec.toNat` of each sail dispatch constant the decode matches on,
    reducing the encoded scrutinees to Nat literals so the `riscvDecode` match
    fires. (These are `rfl`, bundled so one `simp only` reduces every arm.) -/
theorem decConsts :
    ((59 : BitVec 7).toNat = 59) ∧ ((51 : BitVec 7).toNat = 51) ∧
    ((27 : BitVec 7).toNat = 27) ∧ ((19 : BitVec 7).toNat = 19) ∧
    ((0 : BitVec 3).toNat = 0) ∧ ((7 : BitVec 3).toNat = 7) ∧
    ((6 : BitVec 3).toNat = 6) ∧ ((4 : BitVec 3).toNat = 4) ∧
    ((1 : BitVec 3).toNat = 1) ∧ ((5 : BitVec 3).toNat = 5) ∧
    ((0 : BitVec 7).toNat = 0) ∧ ((32 : BitVec 7).toNat = 32) ∧
    ((48 : BitVec 7).toNat = 48) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 6. The per-instruction and capstone round-trip: `decode (encode i) = i`

Each emitted `RInst` arm decodes back to itself: the opcode/funct slices recover
the sail dispatch constants (so `riscvDecode` takes the right branch), and the
register slices recover the names through `regName_reg5`. The capstone
`roundtrip_RInst` is the RV64 analogue of `SailX86Decoder.roundtrip_jinstr_all`,
but — RISC-V being a clean fixed-32-bit ISA — it covers the **entire** emitted
instruction set with no gas-pinned remainder. -/

/-- **Round-trip for `ADDW`.** Pilot of the capstone. -/
theorem roundtrip_addw (d a b : String)
    (hd : d ∈ emittedRegs) (ha : a ∈ emittedRegs) (hb : b ∈ emittedRegs) :
    riscvDecode (encodeWord (.addw d a b)) = some (.addw d a b) := by
  simp only [encodeWord, riscvDecode, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
    (encR_slices ..).1, (encR_slices ..).2.1, (encR_slices ..).2.2.1,
    (encR_slices ..).2.2.2.1, (encR_slices ..).2.2.2.2.1,
    (encR_slices ..).2.2.2.2.2, decConsts.1, decConsts.2.2.2.2.1, decConsts.2.2.2.2.2.2.2.2.2.2.1]
  rw [regName_reg5 d hd, regName_reg5 a ha, regName_reg5 b hb]

/-- **The capstone round-trip `decode (encode i) = i` for the full emitted RV64I
    subset.** For every `RInst` whose register names are in the backend's emitted
    pool (and, for the shift arms, a shift count `< 32`), decoding its encoder
    word recovers the original instruction — proved against the sail-riscv
    `encdec` discipline (`encR_slices`/`encI_slices` are the sail `@`⁻¹), with no
    instruction outside the official RV64I base model. -/
theorem roundtrip_RInst (i : RInst)
    (hregs : (rinstDstSrcs i).1 ∈ emittedRegs ∧
             ∀ r ∈ (rinstDstSrcs i).2, r ∈ emittedRegs)
    (hsh : ∀ d a m, i = .slliw d a m ∨ i = .srliw d a m → m < 32)
    (hror : ∀ d a m, i = .roriw d a m → m < 32) :
    riscvDecode (encodeWord i) = some i := by
  obtain ⟨hdst, hsrc⟩ := hregs
  have D := decConsts
  cases i with
  | addw d a b =>
      have ha := hsrc a (by simp [rinstDstSrcs]); have hb := hsrc b (by simp [rinstDstSrcs])
      simp only [rinstDstSrcs] at hdst
      simp only [encodeWord, riscvDecode, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (encR_slices ..).1, (encR_slices ..).2.1, (encR_slices ..).2.2.1,
        (encR_slices ..).2.2.2.1, (encR_slices ..).2.2.2.2.1, (encR_slices ..).2.2.2.2.2,
        D.1, D.2.2.2.2.1, D.2.2.2.2.2.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]
  | subw d a b =>
      have ha := hsrc a (by simp [rinstDstSrcs]); have hb := hsrc b (by simp [rinstDstSrcs])
      simp only [rinstDstSrcs] at hdst
      simp only [encodeWord, riscvDecode, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (encR_slices ..).1, (encR_slices ..).2.1, (encR_slices ..).2.2.1,
        (encR_slices ..).2.2.2.1, (encR_slices ..).2.2.2.2.1, (encR_slices ..).2.2.2.2.2,
        D.1, D.2.2.2.2.1, D.2.2.2.2.2.2.2.2.2.2.2]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]
  | and d a b =>
      have ha := hsrc a (by simp [rinstDstSrcs]); have hb := hsrc b (by simp [rinstDstSrcs])
      simp only [rinstDstSrcs] at hdst
      simp only [encodeWord, riscvDecode, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (encR_slices ..).1, (encR_slices ..).2.1, (encR_slices ..).2.2.1,
        (encR_slices ..).2.2.2.1, (encR_slices ..).2.2.2.2.1, (encR_slices ..).2.2.2.2.2,
        D.2.1, D.2.2.2.2.2.1, D.2.2.2.2.2.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]
  | or d a b =>
      have ha := hsrc a (by simp [rinstDstSrcs]); have hb := hsrc b (by simp [rinstDstSrcs])
      simp only [rinstDstSrcs] at hdst
      simp only [encodeWord, riscvDecode, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (encR_slices ..).1, (encR_slices ..).2.1, (encR_slices ..).2.2.1,
        (encR_slices ..).2.2.2.1, (encR_slices ..).2.2.2.2.1, (encR_slices ..).2.2.2.2.2,
        D.2.1, D.2.2.2.2.2.2.1, D.2.2.2.2.2.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]
  | xor d a b =>
      have ha := hsrc a (by simp [rinstDstSrcs]); have hb := hsrc b (by simp [rinstDstSrcs])
      simp only [rinstDstSrcs] at hdst
      simp only [encodeWord, riscvDecode, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (encR_slices ..).1, (encR_slices ..).2.1, (encR_slices ..).2.2.1,
        (encR_slices ..).2.2.2.1, (encR_slices ..).2.2.2.2.1, (encR_slices ..).2.2.2.2.2,
        D.2.1, D.2.2.2.2.2.2.2.1, D.2.2.2.2.2.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha, regName_reg5 b hb]
  | slliw d a m =>
      have ha := hsrc a (by simp [rinstDstSrcs]); simp only [rinstDstSrcs] at hdst
      have hm : m < 32 := hsh d a m (Or.inl rfl)
      simp only [encodeWord, riscvDecode, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        encShiftiw, (encR_slices ..).1, (encR_slices ..).2.1, (encR_slices ..).2.2.1,
        (encR_slices ..).2.2.2.1, (encR_slices ..).2.2.2.2.1, (encR_slices ..).2.2.2.2.2,
        D.2.2.1, D.2.2.2.2.2.2.2.2.1, D.2.2.2.2.2.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  | srliw d a m =>
      have ha := hsrc a (by simp [rinstDstSrcs]); simp only [rinstDstSrcs] at hdst
      have hm : m < 32 := hsh d a m (Or.inr rfl)
      simp only [encodeWord, riscvDecode, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        encShiftiw, (encR_slices ..).1, (encR_slices ..).2.1, (encR_slices ..).2.2.1,
        (encR_slices ..).2.2.2.1, (encR_slices ..).2.2.2.2.1, (encR_slices ..).2.2.2.2.2,
        D.2.2.1, D.2.2.2.2.2.2.2.2.2.1, D.2.2.2.2.2.2.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 a ha]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  | roriw d a m =>
      have ha := hsrc a (by simp [rinstDstSrcs]); simp only [rinstDstSrcs] at hdst
      have hm : m < 32 := hror d a m rfl
      simp only [encodeWord, riscvDecode, fOpcode, fRd, fRs1, fRs2, fFunct3, fFunct7,
        (encR_slices ..).1, (encR_slices ..).2.1, (encR_slices ..).2.2.1,
        (encR_slices ..).2.2.2.1, (encR_slices ..).2.2.2.2.1, (encR_slices ..).2.2.2.2.2,
        D.2.2.1, D.2.2.2.2.2.2.2.2.2.1, D.2.2.2.2.2.2.2.2.2.2.2.2]
      rw [regName_reg5 d hdst, regName_reg5 a ha]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  | mv d s =>
      have hs := hsrc s (by simp [rinstDstSrcs]); simp only [rinstDstSrcs] at hdst
      simp only [encodeWord, riscvDecode, fOpcode, fRd, fRs1, fFunct3, fImm12,
        (encI_slices ..).1, (encI_slices ..).2.1, (encI_slices ..).2.2.1,
        (encI_slices ..).2.2.2.1, (encI_slices ..).2.2.2.2,
        D.2.2.2.1, D.2.2.2.2.1]
      rw [regName_reg5 d hdst, regName_reg5 s hs]
      simp

/-- **Round-trip for the `Zbb` `RORIW` rotate (`decode (encode) = i`).** The
    single-instruction rotate `roriw rd, rs1, m` decodes back to itself: the
    funct7 `0x30` distinguishes it from the base `SRLIW` (`f7=0`) at the same
    `(opcode 0x1b, funct3 5)`, and the 5-bit shamt round-trips for `m < 32` (the
    SHA-256 rotates `{2,6,7,11,13,17,18,19,22,25}` are all `< 32`). The
    single-instruction Zbb rotate is thus proved against the sail-riscv encdec
    discipline, exactly like the base subset — no gas-pinned remainder. -/
theorem roundtrip_roriw (d a : String) (m : Nat)
    (hd : d ∈ emittedRegs) (ha : a ∈ emittedRegs) (hm : m < 32) :
    riscvDecode (encodeWord (.roriw d a m)) = some (.roriw d a m) :=
  roundtrip_RInst (.roriw d a m)
    ⟨by simpa [rinstDstSrcs] using hd, by
      intro r hr; simp only [rinstDstSrcs, List.mem_singleton] at hr; subst hr; exact ha⟩
    (by intro d' a' m' h; rcases h with h | h <;> cases h)
    (by intro d' a' m' h; cases h; exact hm)

/-! ## 6b. B-type branch round-trip: the scrambled immediate (`decode (encode) = i`, #552)

The B-type word reassembles its 13-bit signed byte offset from the **scrambled**
field positions `imm[12]=bit31, imm[10:5]=bits[30:25], imm[4:1]=bits[11:8],
imm[11]=bit7` (imm[0]≡0). We decode the `(funct3, rs1, rs2)` and reassemble the
immediate, and prove the round-trip on the immediate AND the comparison/register
fields — the high-risk scramble is round-trip-checked here, the same fixed-width
fact `bv_decide` discharges (the inverse of `encB`'s append of the scrambled
slices). -/

/-- Reassemble the 13-bit B-type byte offset from a word's scrambled immediate
    fields (`imm[12]@imm[10:5] … imm[4:1]@imm[11]`, `imm[0]≡0`) — the inverse of
    `RiscvEncoder.encB`'s scramble. -/
def sImmB (w : BitVec 32) : BitVec 13 :=
  let i12   : BitVec 1 := w.extractLsb' 31 1
  let i11   : BitVec 1 := w.extractLsb' 7 1
  let i10_5 : BitVec 6 := w.extractLsb' 25 6
  let i4_1  : BitVec 4 := w.extractLsb' 8 4
  let i0    : BitVec 1 := 0
  (i12 ++ i11 ++ i10_5 ++ i4_1 ++ i0).cast rfl

/-- The B-type `funct3` → `BCmp` (the comparison the branch tests). -/
def bcmpOfFunct3 : Nat → Option BCmp
  | 0b000 => some .beq
  | 0b001 => some .bne
  | 0b100 => some .blt
  | 0b101 => some .bge
  | 0b110 => some .bltu
  | 0b111 => some .bgeu
  | _ => none

/-- Decode a 32-bit B-type word back to its `(BCmp, rs1, rs2, imm13)` data (opcode
    `0x63`), per the sail `BTYPE encdec`. Returns `none` outside the B-type opcode
    or for an unknown `funct3`. -/
def riscvDecodeB (w : BitVec 32) : Option (BCmp × String × String × BitVec 13) :=
  if fOpcode w = 0x63 then
    match bcmpOfFunct3 (fFunct3 w) with
    | some c => some (c, regName (fRs1 w), regName (fRs2 w), sImmB w)
    | none => none
  else none

/-- The B-type field slices of `encB` recover opcode, funct3, rs1, rs2 exactly
    (sail `@`⁻¹), and the scrambled immediate reassembles `imm` with `imm[0]`
    forced to 0 (branch targets are 2-byte aligned). -/
theorem encB_slices (imm : BitVec 13) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3)
    (opcode : BitVec 7) :
    sOpcode (encB imm rs2 rs1 funct3 opcode) = opcode ∧
    sFunct3 (encB imm rs2 rs1 funct3 opcode) = funct3 ∧
    sRs1    (encB imm rs2 rs1 funct3 opcode) = rs1 ∧
    sRs2    (encB imm rs2 rs1 funct3 opcode) = rs2 ∧
    sImmB   (encB imm rs2 rs1 funct3 opcode) = imm &&& 0x1ffe := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sOpcode, sFunct3, sRs1, sRs2, sImmB, encB] <;> bv_decide

set_option linter.unusedSimpArgs false in
/-- **Round-trip for B-type branches (`decode (encode) = i`).** For every emitted
    B-type branch (register names in the backend pool, opcode `0x63`), decoding its
    encoder word recovers the comparison `c`, the two source registers, and the
    immediate with `imm[0]` cleared (branch targets are 2-byte aligned, so the low
    bit carries no information — `as` enforces it too). This round-trips the RV64
    **scrambled** immediate against the sail `BTYPE encdec` discipline. -/
theorem roundtrip_bcc (c : BCmp) (r1 r2 : String) (off : BitVec 13)
    (h1 : r1 ∈ emittedRegs) (h2 : r2 ∈ emittedRegs) :
    riscvDecodeB (encodeBccWord c r1 r2 off)
      = some (c, r1, r2, off &&& 0x1ffe) := by
  obtain ⟨ho, hf3, hr1, hr2, hi⟩ := encB_slices off (reg5 r2) (reg5 r1)
    (BitVec.ofNat 3 c.funct3) 0x63
  simp only [riscvDecodeB, encodeBccWord, fOpcode, fFunct3, fRs1, fRs2,
    ho, hf3, hr1, hr2, hi, regName_reg5 r1 h1, regName_reg5 r2 h2,
    show (0x63 : BitVec 7).toNat = 0x63 from rfl]
  cases c <;>
    simp only [BCmp.funct3,
      show (BitVec.ofNat 3 0).toNat = 0 from rfl,
      show (BitVec.ofNat 3 1).toNat = 1 from rfl,
      show (BitVec.ofNat 3 4).toNat = 4 from rfl,
      show (BitVec.ofNat 3 5).toNat = 5 from rfl,
      show (BitVec.ofNat 3 6).toNat = 6 from rfl,
      show (BitVec.ofNat 3 7).toNat = 7 from rfl,
      bcmpOfFunct3, if_true]

/-- Round-trip pilot for the loop back-edge `BNE ctr, x0` (the counter loop): the
    emitted `bne a2, zero` at a sample back-edge offset decodes to the same data. -/
theorem roundtrip_bne_backedge :
    riscvDecodeB (encodeBccWord .bne "a2" "zero" (BitVec.ofNat 13 (0x2000 - 4)))
      = some (.bne, "a2", "zero", (BitVec.ofNat 13 (0x2000 - 4)) &&& 0x1ffe) :=
  roundtrip_bcc .bne "a2" "zero" _ (by decide) (by decide)

/-! ## 7. The owned-backend byte-level trust edge after #535 sub-2

Unlike x86 (`SailX86Decoder.trust_edge`, where only the register-direct GP forms
round-trip and the VEX/ADX/memory forms stay gas-pinned), RV64 base is a clean
fixed-32-bit ISA, so **every** instruction the owned RISC-V backend emits is
round-trip-proved here (`roundtrip_RInst`):

* R-type ALU `ADDW`/`SUBW`/`AND`/`OR`/`XOR` and `*IW` shifts `SLLIW`/`SRLIW`
  (`encR_slices` = the sail `@`⁻¹ for `RTYPEW`/`RTYPE`/`SHIFTIWOP`),
* `MV` = `ADDI rd, rs, 0` (`encI_slices` = the sail `@`⁻¹ for `ITYPE`).

For these the encoder's word is *proved* to decode back to the same instruction
under the sail-riscv `encdec` discipline, so `as` is out of the trusted path. The
ChaCha rotate emits only counts `{7,8,12,16,20,24,25} < 32`, within the 5-bit
`shamt` the `*IW` shift round-trip is stated for. **No instruction the backend
emits lacks a sail-riscv `encdec` clause** — there is no gas-pinned remainder.
The single-instruction `Zbb RORIW` rotate (opcode `0x1b`, funct3 `5`, funct7
`0x30`) — emitted by the Zbb SHA-256 lowering to kill the no-rotate
instruction-count tax — is *also* round-trip-proved (`roundtrip_roriw`,
distinguished from base `SRLIW` by funct7), so both the base
`slliw`+`srliw`+`or` synthesis and the Zbb single-instruction rotate are covered
against the sail-riscv model. -/

/-- Doc-anchor: the round-trip-proved set covers the whole ChaCha-QR mix, here the
    `ADDW` pilot, referenced by the trust-edge tally. -/
theorem trust_edge_pilot :
    riscvDecode (encodeWord (.addw "a0" "a0" "a1")) = some (.addw "a0" "a0" "a1") :=
  roundtrip_addw "a0" "a0" "a1" (by decide) (by decide) (by decide)

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder
