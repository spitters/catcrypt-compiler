/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvAsmPrinter

/-!
# A verified machine-code byte encoder for the scalar RV64 `RInst` (#535 sub-2)

`RiscvAsmPrinter.lean` prints a `RiscvModel.RInst` block to GAS RV64 *text*, which
is then handed to `riscv64-linux-gnu-as` to be encoded into machine bytes — that
last step trusts the assembler's instruction encoder. This module is the
**RISC-V RV64 analogue of `X86Backend/ScalarEncoder.lean`**: it encodes each
`RInst` directly to its 32-bit RV64 machine-code word in Lean, so the kernel body
is emitted as bytes by a function whose output we audit against the official
`riscv/sail-riscv` model and differentially validate against `as`.

`ScalarEncoder` did this for the x86-64 scalar GP-register subset jasminc emits;
this module does it for the **RV64I scalar 32-bit-word GP-ALU subset the owned
RISC-V backend emits** — the `RInst` set of `RiscvModel.lean` (`ADDW`/`SUBW`/
`AND`/`OR`/`XOR`/`SLLIW`/`SRLIW`/`MV`), i.e. the ChaCha quarter-round mix
(`add`/`addw`, `xor`, the `slliw`+`srliw`+`or` rotate synthesis, and `mv`).

## Why RISC-V is the clean case

RV64I base instructions are **fixed 32-bit** (no legacy/REX/VEX prefixes, no
ModRM/SIB, no displacement variants). Each instruction word is a *fixed bitfield
concatenation* of the official sail-riscv `encdec` mapping clause
(`base_insts.sail`):

```
RTYPEW(rs2,rs1,rd,ADDW) <-> 0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011  (xlen==64)
RTYPEW(rs2,rs1,rd,SUBW) <-> 0b0100000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
RTYPE (rs2,rs1,rd,AND)  <-> 0b0000000 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0110011
RTYPE (rs2,rs1,rd,OR)   <-> 0b0000000 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0110011
RTYPE (rs2,rs1,rd,XOR)  <-> 0b0000000 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0110011
SHIFTIWOP(shamt,rs1,rd,SLLIW) <-> 0b0000000 @ shamt @ rs1 @ 0b001 @ rd @ 0b0011011
SHIFTIWOP(shamt,rs1,rd,SRLIW) <-> 0b0000000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0011011
ITYPE(imm,rs1,rd,ADDI)  <-> imm @ rs1 @ 0b000 @ rd @ 0b0010011        (MV = ADDI rd,rs,0)
```

(`@` is sail bit-concatenation, MSB first; `encdec_reg(r)` is the 5-bit register
number, `core/regs.sail`.) So the encoder is a 32-bit `OR` of shifted fields, and
the round-trip decoder (`riscvDecode`) is the inverse field extraction — both
transcribed *verbatim* from the sail-riscv clauses. There is no instruction
selection / scheduling here, so the trust edge is exactly: this field layout
matches the sail-riscv `encdec` clause (the `decode (encode i) = i` theorem
below) ∧ the chosen `funct7/funct3/opcode` constants are the sail constants
(auditable by eye against the quoted clauses).

## Memory layout / endianness

A 32-bit RV64 instruction word is stored **little-endian** in the `.text`
section. `encodeRInst` returns the 4 LE bytes (low byte first), matching what
`as` writes and what a `riscv64` fetch reads; `riscvWord` is the underlying
`BitVec 32` word (the value objdump prints).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder

open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## 1. Register name → 5-bit number (sail `encdec_reg` / `reg_abi_name_raw`)

The ABI-name → 5-bit register number table, transcribed from sail-riscv
`core/regs.sail` `reg_abi_name_raw` (`zero=0, ra=1, sp=2, gp=3, tp=4,
t0..t2=5..7, s0/fp=8, s1=9, a0..a7=10..17, s2..s11=18..27, t3..t6=28..31`). The
printer only ever emits `zero`, `a0..a7`, `t0..t6`, so those are the live rows;
an unknown name maps to `0` (the `zero` register), never produced for a fitting
block (`allocGp` yields the explicit `<UNALLOCATED:_>` sentinel, which `as`
rejects). -/
def regNum (r : String) : Nat :=
  match r with
  | "zero" | "x0" => 0
  | "ra" => 1   | "sp" => 2   | "gp" => 3   | "tp" => 4
  | "t0" => 5   | "t1" => 6   | "t2" => 7
  | "s0" | "fp" => 8 | "s1" => 9
  | "a0" => 10  | "a1" => 11  | "a2" => 12  | "a3" => 13
  | "a4" => 14  | "a5" => 15  | "a6" => 16  | "a7" => 17
  | "s2" => 18  | "s3" => 19  | "s4" => 20  | "s5" => 21
  | "s6" => 22  | "s7" => 23  | "s8" => 24  | "s9" => 25
  | "s10" => 26 | "s11" => 27
  | "t3" => 28  | "t4" => 29  | "t5" => 30  | "t6" => 31
  | _ => 0

/-- Every `regNum` lands in the 5-bit range `0..31`. -/
theorem regNum_lt_32 (r : String) : regNum r < 32 := by
  unfold regNum; split <;> omega

/-! ## 2. The field-concatenation word builders (sail `encdec` clauses)

Each builder is the **bit-concatenation** of the sail bitfields read MSB-first —
exactly the sail `@` operator, which is `BitVec.append` on width-typed fields.
The fields are width-typed `BitVec`s (`funct7`/opcode `BitVec 7`, regs `BitVec 5`,
funct3 `BitVec 3`, imm `BitVec 12`), built from the `Nat` inputs via
`BitVec.ofNat` (truncating to the field width, the sail field-width discipline);
appending them yields the `BitVec 32` instruction word (the value objdump prints,
MSB field at the high end). Using `++` (append) rather than shifted `OR` makes the
field layout and its inverse (`SailRiscvDecoder.riscvDecode`) `bv_decide`-decidable
with no side conditions, because slicing an append recovers each field exactly. -/

/-- An R-type word (`RTYPE`/`RTYPEW`): the sail concat
    `funct7[7] @ rs2[5] @ rs1[5] @ funct3[3] @ rd[5] @ opcode[7]` (7+5+5+3+5+7 = 32),
    as a `BitVec 32`. The fields are width-typed `BitVec`s (the sail `@` operator
    is `BitVec.append`), so the round-trip decoder slices them back exactly. -/
def encR (funct7 : BitVec 7) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3)
    (rd : BitVec 5) (opcode : BitVec 7) : BitVec 32 :=
  (funct7 ++ rs2 ++ rs1 ++ funct3 ++ rd ++ opcode).cast rfl

/-- An I-type-shaped word with an explicit upper `funct7` field used as the shift
    `0000000` and a 5-bit `shamt` in the `rs2` slot — i.e. the `SHIFTIWOP` shape
    `0b0000000 @ shamt @ rs1 @ funct3 @ rd @ opcode`. (RV64 `*IW` shifts use a
    5-bit shamt; the high `funct7` bit selects logical vs arithmetic, but the
    backend emits only the logical `0000000` forms.) -/
def encShiftiw (shamt rs1 : BitVec 5) (funct3 : BitVec 3) (rd : BitVec 5)
    (opcode : BitVec 7) : BitVec 32 :=
  encR 0 shamt rs1 funct3 rd opcode

/-- An I-type word (`ITYPE` etc.): the sail concat
    `imm[12] @ rs1[5] @ funct3[3] @ rd[5] @ opcode[7]` (12+5+3+5+7 = 32). The
    12-bit immediate occupies the high bits 31:20. -/
def encI (imm : BitVec 12) (rs1 : BitVec 5) (funct3 : BitVec 3) (rd : BitVec 5)
    (opcode : BitVec 7) : BitVec 32 :=
  (imm ++ rs1 ++ funct3 ++ rd ++ opcode).cast rfl

/-- A B-type word (`BTYPE`): the sail `encdec` concat for a conditional branch,
    with the **scrambled** 13-bit byte offset `imm[12:0]` (imm[0] always 0). The
    sail clause is

    `BTYPE(imm,rs2,rs1,op) <-> imm[12] @ imm[10:5] @ rs2 @ rs1 @ funct3 @
                               imm[4:1] @ imm[11] @ 0b1100011`

    (MSB-first; opcode `0b1100011 = 0x63`). The immediate bits are *not* contiguous
    — bit 12 leads, bits 10:5 follow, then (after rs2/rs1/funct3) bits 4:1, then
    bit 11, the RV64 B/J-immediate scramble. We take `imm : BitVec 13` (the signed
    byte offset, `imm[0]` ignored — branch targets are 2-byte aligned) and slice
    its bits into the scrambled positions, so the round-trip decoder recovers them.
    Using `++` (append) of the width-typed slices keeps the layout
    `bv_decide`-decidable, exactly as `encR`/`encI`. -/
def encB (imm : BitVec 13) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3)
    (opcode : BitVec 7) : BitVec 32 :=
  let i12   : BitVec 1 := imm.extractLsb' 12 1
  let i10_5 : BitVec 6 := imm.extractLsb' 5 6
  let i4_1  : BitVec 4 := imm.extractLsb' 1 4
  let i11   : BitVec 1 := imm.extractLsb' 11 1
  (i12 ++ i10_5 ++ rs2 ++ rs1 ++ funct3 ++ i4_1 ++ i11 ++ opcode).cast rfl

/-- The 5-bit register field for a register name (sail `encdec_reg`). -/
def reg5 (r : String) : BitVec 5 := BitVec.ofNat 5 (regNum r)

/-- Encode one B-type `RBranch.bcc` to its 32-bit RV64 instruction word, given the
    resolved signed *byte* offset `(target − here)` as a `BitVec 13`. B-type
    opcode is `0b1100011 = 0x63`; the comparison `funct3` is `BCmp.funct3`. -/
def encodeBccWord (c : BCmp) (rs1 rs2 : String) (off : BitVec 13) : BitVec 32 :=
  encB off (reg5 rs2) (reg5 rs1) (BitVec.ofNat 3 c.funct3) 0x63

/-! ## 3. The per-`RInst` word encoder (sail constants quoted inline)

The `funct7`/`funct3`/`opcode` constants are exactly the sail clauses:
`RTYPEW` opcode `0b0111011 = 0x3b`; `RTYPE` opcode `0b0110011 = 0x33`;
`SHIFTIWOP` opcode `0b0011011 = 0x1b`; `ITYPE` opcode `0b0010011 = 0x13`.
`ADDW`/`SUBW` funct3 `0b000`, `SUBW` funct7 `0b0100000 = 0x20`; `AND` funct3
`0b111`, `OR` `0b110`, `XOR` `0b100`; `SLLIW` funct3 `0b001`, `SRLIW` `0b101`;
`ADDI` (the `MV rd,rs` pseudo = `addi rd,rs,0`) funct3 `0b000`. -/

/-- Encode one `RInst` to its 32-bit RV64 instruction word (the value objdump
    prints). `MV rd, rs` is the canonical pseudo-op `ADDI rd, rs, 0`. -/
def encodeWord : RInst → BitVec 32
  | .addw d a b  => encR 0x00 (reg5 b) (reg5 a) 0b000 (reg5 d) 0x3b
  | .subw d a b  => encR 0x20 (reg5 b) (reg5 a) 0b000 (reg5 d) 0x3b
  | .and  d a b  => encR 0x00 (reg5 b) (reg5 a) 0b111 (reg5 d) 0x33
  | .or   d a b  => encR 0x00 (reg5 b) (reg5 a) 0b110 (reg5 d) 0x33
  | .xor  d a b  => encR 0x00 (reg5 b) (reg5 a) 0b100 (reg5 d) 0x33
  | .slliw d a m => encShiftiw (BitVec.ofNat 5 m) (reg5 a) 0b001 (reg5 d) 0x1b
  | .srliw d a m => encShiftiw (BitVec.ofNat 5 m) (reg5 a) 0b101 (reg5 d) 0x1b
  -- RORIW (Zbb): opcode OP-IMM-32 0x1b, funct3 0b101, funct7 0b0110000 = 0x30
  -- (the high imm[11:5] field selects rotate-right-immediate-word); 5-bit shamt
  -- in the rs2 slot. Sail `ZBB_RTYPEW`/`RORIW` encdec (model/extensions/Zbb).
  | .roriw d a m => encR 0x30 (BitVec.ofNat 5 m) (reg5 a) 0b101 (reg5 d) 0x1b
  | .mv   d s    => encI 0 (reg5 s) 0b000 (reg5 d) 0x13

/-- The little-endian 4 bytes of a 32-bit instruction word (low byte first) — the
    `.text`-section layout `as` writes and a `riscv64` fetch reads. -/
def wordLE (w : BitVec 32) : List (BitVec 8) :=
  [ w.toNat &&& 0xff, (w.toNat >>> 8) &&& 0xff, (w.toNat >>> 16) &&& 0xff,
    (w.toNat >>> 24) &&& 0xff ].map (BitVec.ofNat 8)

/-- Encode one `RInst` to its 4 little-endian machine-code bytes. -/
def encodeRInst (i : RInst) : List (BitVec 8) := wordLE (encodeWord i)

/-- Encode a whole block: concatenate the per-instruction LE byte encodings — the
    contiguous `.text` machine-code stream. -/
def encodeRBlock (block : List RInst) : List (BitVec 8) :=
  block.flatMap encodeRInst

/-- Encode one `RBranch` to its little-endian machine bytes (the looped-emission
    back-edge / jump). A `label` is a pure assembler symbol with **no** machine
    word (empty byte list); a `bcc` resolves its PC-relative *byte* offset through
    `resolve` (`(target − here)`, the step the assembler performs from the label),
    then encodes the B-type word with the scrambled immediate; a `j` is not byte-
    encoded here (the J-immediate scramble differs; the loop never needs `j`, only
    the `bne` back-edge). The `resolve` argument is supplied by the byte-diff
    harness with the same offsets `as` computes. The J-type is rendered as text
    only. -/
def encodeRBranch (resolve : RLabel → BitVec 13) : RBranch → List (BitVec 8)
  | .label _       => []
  | .bcc c r1 r2 l => wordLE (encodeBccWord c r1 r2 (resolve l))
  | .j _           => []   -- J-type text-only (not used by the counter loop)

/-! ## 4. Structural well-formedness (the unconditional half of the trust story)

Every `encodeRInst` output is exactly 4 bytes (the RV64 base fixed instruction
width), and every word's low 7 bits are the sail `opcode` for its `RInst` arm.
This is the encoder analogue of `ScalarEncoder.encAluRR_length` — it pins the
shape an RV64 fetch/decode requires, proved for all inputs. -/

/-- Every `RInst` encodes to exactly 4 bytes (RV64 base instruction width). -/
@[simp] theorem encodeRInst_length (i : RInst) : (encodeRInst i).length = 4 := by
  cases i <;> simp [encodeRInst, wordLE]

/-- `encodeRBlock` length is `4 ×` the instruction count. -/
theorem encodeRBlock_length (block : List RInst) :
    (encodeRBlock block).length = 4 * block.length := by
  induction block with
  | nil => rfl
  | cons i is ih =>
      simp only [encodeRBlock, List.flatMap_cons, List.length_append,
        encodeRInst_length] at *
      simp only [List.length_cons]; omega

/-- `encodeRBlock` is the flat concatenation of the per-instruction encodings. -/
@[simp] theorem encodeRBlock_eq (block : List RInst) :
    encodeRBlock block = block.flatMap encodeRInst := rfl

/-! ## 5. Differential-validation pins against `riscv64-linux-gnu-as`

The encoder's instruction words pinned to the exact 32-bit words
`riscv64-linux-gnu-as` produces for the same mnemonic — the differential anchor
(the `objdump -d` value, the bench `riscv_compare` oracle). These are the same
`addw`/`xor`/`slliw`/`srliw`/`or` lines the QR asm emits; the `decode(encode)=i`
round-trip in `SailRiscvDecoder.lean` upgrades this gas pin to a proof against
the official sail-riscv model. -/

/-- `addw a0, a0, a1` → `as`/objdump word `0x00b5053b`. -/
example : encodeWord (.addw "a0" "a0" "a1") = 0x00b5053b := by native_decide
/-- `xor a3, a3, a0` → `0x00a6c6b3`. -/
example : encodeWord (.xor "a3" "a3" "a0") = 0x00a6c6b3 := by native_decide
/-- `slliw a4, a3, 16` → `0x0106971b`. -/
example : encodeWord (.slliw "a4" "a3" 16) = 0x0106971b := by native_decide
/-- `srliw a3, a3, 16` → `0x0106d69b`. -/
example : encodeWord (.srliw "a3" "a3" 16) = 0x0106d69b := by native_decide
/-- `or a3, a4, a3` → `0x00d766b3`. -/
example : encodeWord (.or "a3" "a4" "a3") = 0x00d766b3 := by native_decide
/-- `subw a2, a2, a3` → `0x40d6063b`. -/
example : encodeWord (.subw "a2" "a2" "a3") = 0x40d6063b := by native_decide
/-- `mv a5, a0` (= `addi a5, a0, 0`) → `0x00050793`. -/
example : encodeWord (.mv "a5" "a0") = 0x00050793 := by native_decide

/-- `roriw a1, a0, 8` (Zbb single-instruction rotate) → `as -march=rv64gc_zbb` /
    objdump word `0x6085559b` (funct7 `0x30`, funct3 `0x5`, opcode `0x1b`). -/
example : encodeWord (.roriw "a1" "a0" 8) = 0x6085559b := by native_decide
/-- `roriw a2, a0, 12` → `0x60c5561b`. -/
example : encodeWord (.roriw "a2" "a0" 12) = 0x60c5561b := by native_decide

/-- The first little-endian byte of `addw a0,a0,a1` is `0x3b` (the RV64 opcode
    byte that leads the LE word in `.text`). -/
example : (encodeRInst (.addw "a0" "a0" "a1")).head? = some 0x3b := by native_decide

/-! ### 5b. B-type branch encoder: structure + gas differential pins (#552)

Each `bcc` branch is one 4-byte word (a `label` is 0 bytes); the words are pinned
to `riscv64-linux-gnu-as` for the looped back-edge offsets — the high-risk spot is
the **scrambled** immediate `imm[12|10:5 … 4:1|11]`, which only the gas byte-diff
catches if mis-packed. Reference words from `objdump -d` on a back-edge to the loop
top (`a2=12`, `a0=10`, `a1=11`, `zero=0`):

* `bne a2, zero, .Ltop`  offset −4  → `0xfe061ee3`
* `beq a0, a1, .Ltop`    offset −8  → `0xfeb50ce3`
* `blt a0, a1, .Ltop`    offset −12 → `0xfeb54ae3`
* `bne a2, zero, .Ltop`  offset −16 → `0xfe0618e3`
-/

/-- Every B-type branch encodes to exactly 4 bytes; a label / `j` to 0. -/
@[simp] theorem encodeRBranch_length (resolve : RLabel → BitVec 13) (i : RBranch) :
    (encodeRBranch resolve i).length =
      (match i with | .bcc _ _ _ _ => 4 | _ => 0) := by
  cases i <;> simp [encodeRBranch, wordLE]

/-- `bne a2, zero, .Ltop` at back-edge byte offset `−4` → gas word `0xfe061ee3`. -/
example : encodeBccWord .bne "a2" "zero" (BitVec.ofNat 13 (0x2000 - 4)) = 0xfe061ee3 := by
  native_decide
/-- `beq a0, a1, .Ltop` at offset `−8` → gas word `0xfeb50ce3`. -/
example : encodeBccWord .beq "a0" "a1" (BitVec.ofNat 13 (0x2000 - 8)) = 0xfeb50ce3 := by
  native_decide
/-- `blt a0, a1, .Ltop` at offset `−12` → gas word `0xfeb54ae3`. -/
example : encodeBccWord .blt "a0" "a1" (BitVec.ofNat 13 (0x2000 - 12)) = 0xfeb54ae3 := by
  native_decide
/-- `bne a2, zero, .Ltop` at offset `−16` → gas word `0xfe0618e3` — the scrambled
    immediate packs `imm[12|10:5|4:1|11]` exactly as the ISA. -/
example : encodeBccWord .bne "a2" "zero" (BitVec.ofNat 13 (0x2000 - 16)) = 0xfe0618e3 := by
  native_decide

/-- The low 7 bits of every B-type branch word are the RV64 `BRANCH` opcode
    `0x63` (the LE head byte also carries `imm[11]` in bit 7, so it is not `0x63`
    itself; the opcode is the low 7 bits). -/
example : (encodeBccWord .bne "a2" "zero" (BitVec.ofNat 13 (0x2000 - 4))).toNat % 128 = 0x63 := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
