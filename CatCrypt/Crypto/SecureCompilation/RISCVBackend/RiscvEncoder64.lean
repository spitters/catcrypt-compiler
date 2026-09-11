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
# A verified machine-code byte encoder for the 64-bit bignum `RInst64` (#549)

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

    **Precondition:** `.srli`/`.slli`'s shift amount `sh` is packed directly into
    the 12-bit `ITYPE` immediate with `BitVec.ofNat 12 sh`, with **no range
    check**. `SailRiscvDecoder64.roundtrip_RInst64` is stated only for `sh < 64`
    (the RV64 6-bit `shamt`); outside that range the encoding is not just
    "wrong", it can silently name a *different instruction*: on RV64,
    `imm[11:6]` doubles as the `SRLI`/`SRAI` selector (`0b000000` vs
    `0b010000`), so e.g. `sh = 1024` (`0b010000000000`) packs `shamt = 0` with
    the `SRAI` selector bits set — `encodeWord64 (.srli d a 1024)` assembles to
    `srai d, a, 0`, not `srli`. The backend must only ever call this with
    `sh < 64`. -/
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
  | .srli d a sh => some (encI (BitVec.ofNat 12 sh) (reg5 a) 0b101 (reg5 d) 0x13)
  | .slli d a sh => some (encI (BitVec.ofNat 12 sh) (reg5 a) 0b001 (reg5 d) 0x13)
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
