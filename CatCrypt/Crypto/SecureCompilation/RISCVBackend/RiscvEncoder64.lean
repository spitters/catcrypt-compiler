/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvAsmPrinter64
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvAsmPrinter64

/-!
# A verified machine-code byte encoder for the 64-bit bignum `RInst64`

`RiscvEncoder.lean` encodes the scalar 32-bit-word `RInst` subset; this module is
its **64-bit bignum** counterpart, encoding the M-extension carry-chain subset the
owned RV64 bignum backend emits — `ADD`/`SUB`/`SLTU`/`AND`/`OR`/`XOR` (RTYPE,
opcode `0x33`), `MUL`/`MULHU` (M-extension RTYPE, funct7 `0x01`, opcode `0x33`),
and `MV` = `ADDI rd,rs,0` (ITYPE, opcode `0x13`).

The `funct7`/`funct3`/`opcode` constants are exactly the sail-riscv `encdec`
clauses (`model/extensions/I/base_insts.sail`, `model/extensions/M/mext_insts.sail`):

```
RTYPE(rs2,rs1,rd,ADD)  <-> 0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011
RTYPE(rs2,rs1,rd,SUB)  <-> 0b0100000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011
RTYPE(rs2,rs1,rd,SLTU) <-> 0b0000000 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0110011
RTYPE(rs2,rs1,rd,AND)  <-> 0b0000000 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0110011
RTYPE(rs2,rs1,rd,OR)   <-> 0b0000000 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0110011
RTYPE(rs2,rs1,rd,XOR)  <-> 0b0000000 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0110011
MUL(rs2,rs1,rd,low)    <-> 0b0000001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011
MULHU(rs2,rs1,rd)      <-> 0b0000001 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0110011
ITYPE(0,rs1,rd,ADDI)   <-> 0...0 @ rs1 @ 0b000 @ rd @ 0b0010011        (MV)
```

## The one pseudo-op left to the assembler: `LI`

`LI rd, #imm` is **not** a fixed-width instruction — `as` expands it to a
*variable-length* `lui`+`addi`(+shift/addi…) sequence whose length depends on the
constant (1–8 instructions for a 64-bit value). It is therefore *not*
byte-encoded here; it is the RV64 analogue of the trusted prologue scaffolding
(the bignum kernel materialises the three `p_256` constant limbs with `li`). The
byte-diff (`addp256-bytes-diff`, checked by hand against `as`/`objdump`; the
comparison harness itself is not vendored in this tree) is run on the
**register-to-register body** (the carry chain + trial subtraction +
mask-select reduce, with the `li`s factored out), exactly the verified-encoded
subset; the `li` constant loads are assembled by `as` as trusted scaffolding.
`encodeWord64` returns `none` for `li` to make that boundary explicit and
machine-checked.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder

/-! ## 1. The per-`RInst64` word encoder (sail constants quoted inline)

Reuses `RiscvEncoder.encR`/`encI`/`reg5` (the sail `@` field-concatenation
builders) and the `regNum` table. `MUL` funct7 is `0b0000001 = 0x01`. -/

/-- Encode one `RInst64` to its 32-bit RV64 instruction word, or `none` for the
    `LI` pseudo-op (which `as` expands to a variable-length sequence).

    The shift amount `sh : Fin 64` of `.srli`/`.slli` is the RV64 6-bit `shamt`; it
    is packed into the 12-bit `ITYPE` immediate, whose upper six bits `imm[11:6]`
    are the `SRLI`/`SRAI` selector and stay `0b000000` because `sh < 64`. -/
def encodeWord64 : RInst64 → Option (BitVec 32)
  | .add  d a b => some (encR 0x00 (reg5 b) (reg5 a) 0b000 (reg5 d) 0x33)
  | .sub  d a b => some (encR 0x20 (reg5 b) (reg5 a) 0b000 (reg5 d) 0x33)
  | .sltu d a b => some (encR 0x00 (reg5 b) (reg5 a) 0b011 (reg5 d) 0x33)
  | .and  d a b => some (encR 0x00 (reg5 b) (reg5 a) 0b111 (reg5 d) 0x33)
  | .or   d a b => some (encR 0x00 (reg5 b) (reg5 a) 0b110 (reg5 d) 0x33)
  | .xor  d a b => some (encR 0x00 (reg5 b) (reg5 a) 0b100 (reg5 d) 0x33)
  | .mul  d a b => some (encR 0x01 (reg5 b) (reg5 a) 0b000 (reg5 d) 0x33)
  | .mulhu d a b => some (encR 0x01 (reg5 b) (reg5 a) 0b011 (reg5 d) 0x33)
  | .mv   d s   => some (encI 0 (reg5 s) 0b000 (reg5 d) 0x13)
  | .srli d a sh => some (encI (BitVec.ofNat 12 sh.val) (reg5 a) 0b101 (reg5 d) 0x13)
  | .slli d a sh => some (encI (BitVec.ofNat 12 sh.val) (reg5 a) 0b001 (reg5 d) 0x13)
  | .li   _ _   => none

/-- Encode one `RInst64` to its little-endian machine-code bytes (`[]` for `LI`,
    the trusted pseudo-op). -/
def encodeRInst64 (i : RInst64) : List (BitVec 8) :=
  match encodeWord64 i with
  | some w => wordLE w
  | none => []

/-- Encode a whole block: concatenate the per-instruction LE byte encodings
    (the `LI` pseudo-ops contribute nothing — they are factored out for the
    byte-diff). -/
def encodeRBlock64 (block : List RInst64) : List (BitVec 8) :=
  block.flatMap encodeRInst64

/-- Every non-`LI` `RInst64` encodes to exactly 4 bytes (RV64 base width). -/
@[simp] theorem encodeRInst64_length (i : RInst64) (h : (∀ d imm, i ≠ .li d imm)) :
    (encodeRInst64 i).length = 4 := by
  cases i <;> simp_all [encodeRInst64, encodeWord64, wordLE]

/-! ## 1a. The memory-and-branch fragment `RMInst64`

The sail-riscv `encdec` clauses of the added instructions (`model/extensions/I/base_insts.sail`):

```
ITYPE(imm,rs1,rd,ADDI) <-> imm @ rs1 @ 0b000 @ rd @ 0b0010011
LOAD(imm,rs1,rd,DOUBLE) <-> imm @ rs1 @ 0b011 @ rd @ 0b0000011
STORE(imm,rs2,rs1,DOUBLE) <-> imm[11:5] @ rs2 @ rs1 @ 0b011 @ imm[4:0] @ 0b0100011
BTYPE(imm,rs2,rs1,BNE) <-> imm[12] @ imm[10:5] @ rs2 @ rs1 @ 0b001 @ imm[4:1] @ imm[11] @ 0b1100011
```
-/

/-- An S-type word (`STORE`): the sail concat
    `imm[11:5] @ rs2 @ rs1 @ funct3 @ imm[4:0] @ opcode` (7+5+5+3+5+7 = 32). -/
def encStype (imm : BitVec 12) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3)
    (opcode : BitVec 7) : BitVec 32 :=
  let i11_5 : BitVec 7 := imm.extractLsb' 5 7
  let i4_0  : BitVec 5 := imm.extractLsb' 0 5
  (i11_5 ++ rs2 ++ rs1 ++ funct3 ++ i4_0 ++ opcode).cast rfl

/-- Encode one `RMInst64` to its 32-bit RV64 word: a register instruction by
    `encodeWord64`, `ADDI` and `LD` as I-type, `SD` as S-type, `BNE` as B-type. The
    immediates are truncated to their fields (12 bits; 13 bits for `BNE`); the round trip
    `SailRiscvDecoder64.roundtrip_RMInst64` is stated for immediates within the fields. -/
def encodeMWord64 : RMInst64 → Option (BitVec 32)
  | .alu i => encodeWord64 i
  | .addi d a imm => some (encI (BitVec.ofInt 12 imm) (reg5 a) 0b000 (reg5 d) 0x13)
  | .ld d base off => some (encI (BitVec.ofInt 12 off) (reg5 base) 0b011 (reg5 d) 0x03)
  | .sd src base off => some (encStype (BitVec.ofInt 12 off) (reg5 src) (reg5 base) 0b011 0x23)
  | .bne a b off => some (encB (BitVec.ofInt 13 off) (reg5 b) (reg5 a) 0b001 0x63)

/-- Encode one `RMInst64` to its little-endian bytes (`[]` for `LI`). -/
def encodeRMInst64 (i : RMInst64) : List (BitVec 8) :=
  match encodeMWord64 i with
  | some w => wordLE w
  | none => []

/-- Encode a block of `RMInst64`: the concatenation of the instruction bytes. -/
def encodeRMBlock64 (block : List RMInst64) : List (BitVec 8) :=
  block.flatMap encodeRMInst64

/-! ## 2. Differential-validation pins against `riscv64-linux-gnu-as`

The encoder's words pinned to the exact 32-bit words `riscv64-linux-gnu-as`
produces for the same mnemonic (the `objdump -d` value, checked by hand against
`as`). These pins cover `add`/`sub`/`sltu`/`mul`/`mulhu`/`and`/`or`/`xor`/`mv`/
`li`; **`srli`/`slli` have no differential pin below** — their only
machine-checked coverage is the sail-riscv round-trip in
`SailRiscvDecoder64.roundtrip_RInst64`, not a gas-pinned example here. -/

-- `add a0, a0, a1` → `0x00b50533`
#guard encodeWord64 (.add "a0" "a0" "a1") == some 0x00b50533
-- `sub a2, a2, a3` → `0x40d60633`
#guard encodeWord64 (.sub "a2" "a2" "a3") == some 0x40d60633
-- `sltu a3, a0, a1` → `0x00b536b3`
#guard encodeWord64 (.sltu "a3" "a0" "a1") == some 0x00b536b3
-- `mul a4, a0, a1` → `0x02b50733`
#guard encodeWord64 (.mul "a4" "a0" "a1") == some 0x02b50733
-- `mulhu a5, a0, a1` → `0x02b537b3`
#guard encodeWord64 (.mulhu "a5" "a0" "a1") == some 0x02b537b3
-- `and a0, a1, a2` → `0x00c5f533`
#guard encodeWord64 (.and "a0" "a1" "a2") == some 0x00c5f533
-- `or a0, a1, a2` → `0x00c5e533`
#guard encodeWord64 (.or "a0" "a1" "a2") == some 0x00c5e533
-- `xor a0, a1, a2` → `0x00c5c533`
#guard encodeWord64 (.xor "a0" "a1" "a2") == some 0x00c5c533
-- `mv a5, a0` (= `addi a5, a0, 0`) → `0x00050793`
#guard encodeWord64 (.mv "a5" "a0") == some 0x00050793

-- `LI` is the one pseudo-op left to `as` (no fixed encoding).
#guard encodeWord64 (.li "a0" 0xffffffffffffffff) == none

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64
