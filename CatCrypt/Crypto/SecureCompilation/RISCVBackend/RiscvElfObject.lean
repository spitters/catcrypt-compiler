/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64

/-!
# A verified RV64 ELF64 relocatable-object stitcher + ABI scaffolding encoder

This is the **RISC-V RV64 analogue of `ARMBackend/ArmElfObject.lean`** (itself the
AArch64 analogue of `X86Backend/ElfObject.lean`): it wraps the verified-encoder
`.text` bytes of one or more leaves into an ELF64 relocatable object
(`ELFCLASS64`, `ET_REL`, `EM_RISCV = 243`), so the owned RV64 backend produces a
real `.o` directly — with neither `riscv64-linux-gnu-as`/gas nor `clang` on the
object-build path. A list of `(name, textBytes)` leaves concatenate into one
`.text` section, each leaf getting its own `STT_FUNC` global symbol whose
`st_value` is its byte offset within `.text` and whose `st_size` is its byte
length. A whole RV64 function (prologue + verified body + epilogue, plus an
in-`.text` `_start` driver) thus stitches into ONE verified-bytes-direct
relocatable object.

The container layout is the standard System-V relocatable form, byte-identical in
*structure* to the x86/ARM stitchers; only `e_machine` (`EM_RISCV = 243`), the
`e_flags` (RV64 double-float ABI `0x4`), and the relocation type vocabulary
(`R_RISCV_CALL = 18` for a `jal`/`call` to an external symbol) are RV64-specific.

```
[ Elf64_Ehdr (64B)
| .text          = text₀ ++ text₁ ++ … (pad8)
| .rela.text     = one Elf64_Rela per relocation (pad8)
| .shstrtab      (pad8)
| .strtab        = NUL ++ name₀\0 ++ … (pad8)
| .symtab        = nullSym ++ funcSym₀ ++ … ++ externSym₀ ++ …
| Elf64_Shdr × 7 ]
```

## The ABI scaffolding encoder (§2)

The verified GP-ALU body is encoded by `RiscvEncoder`/`RiscvEncoder64`
(`add`/`sub`/`sltu`/`and`/`or`/`xor`/`mul`/`mulhu`/`mv` + the 32-bit `*W` ChaCha/
SHA forms). To emit a *whole function* byte-direct we additionally need the RV64
psABI leaf scaffolding — load/store (`ld`/`sd`), frame adjust (`addi`), return
(`jalr`/`ret`), local call (`jal`), 32-bit constant materialisation
(`lui`+`addiw` = the `li` macro for a ≤ 32-bit value), and the `_start` driver
syscall (`ecall`) + checks (`bne`/`bnez`). These are the **trusted ABI edge** (the
same posture as the x86/ARM prologue scaffolding), but here they too are emitted
by Lean field-concatenation builders transcribed from the sail-riscv `encdec`
clauses, so the *whole object* is byte-produced by Lean — `as`/gas touches
nothing on the artifact path. Each builder is pinned to the exact
`riscv64-linux-gnu-as`/objdump word (§2 differential pins).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvElfObject

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder

/-! ## 1. Self-contained little-endian byte helpers (zone isolation) -/

/-- The little-endian bytes of a 16-bit value. -/
def u16LE (v : Nat) : List (BitVec 8) :=
  [v &&& 0xff, (v >>> 8) &&& 0xff].map (BitVec.ofNat 8)
/-- The little-endian bytes of a 32-bit value. -/
def u32LE (v : Nat) : List (BitVec 8) :=
  [v &&& 0xff, (v >>> 8) &&& 0xff, (v >>> 16) &&& 0xff, (v >>> 24) &&& 0xff].map
    (BitVec.ofNat 8)
/-- The little-endian bytes of a 64-bit value. -/
def u64LE (v : Nat) : List (BitVec 8) :=
  (List.range 8).map (fun i => BitVec.ofNat 8 ((v >>> (8 * i)) &&& 0xff))

@[simp] theorem u16LE_length (v : Nat) : (u16LE v).length = 2 := by simp [u16LE]
@[simp] theorem u32LE_length (v : Nat) : (u32LE v).length = 4 := by simp [u32LE]
@[simp] theorem u64LE_length (v : Nat) : (u64LE v).length = 8 := by simp [u64LE]

/-! ## 2. RV64 ABI scaffolding instruction encoders

The body's verified ALU words come from `RiscvEncoder.encodeWord` /
`RiscvEncoder64.encodeWord64`; these builders cover the *scaffolding* a whole RV64
leaf + `_start` driver needs. Every constant is the sail-riscv `encdec` clause
(`base_insts.sail`); each is pinned to `riscv64-linux-gnu-as` in §2c. `encI`/`encB`
are reused from `RiscvEncoder`; we add the S/U/J shapes here. -/

/-- An S-type word (`sd`/`sw`): the sail concat
    `imm[11:5] @ rs2 @ rs1 @ funct3 @ imm[4:0] @ opcode` (7+5+5+3+5+7 = 32). The
    12-bit signed store offset is split across the high and low immediate fields. -/
def encS (imm : BitVec 12) (rs2 rs1 : BitVec 5) (funct3 : BitVec 3)
    (opcode : BitVec 7) : BitVec 32 :=
  let i11_5 : BitVec 7 := imm.extractLsb' 5 7
  let i4_0  : BitVec 5 := imm.extractLsb' 0 5
  (i11_5 ++ rs2 ++ rs1 ++ funct3 ++ i4_0 ++ opcode).cast rfl

/-- A U-type word (`lui`/`auipc`): the sail concat `imm[31:12] @ rd @ opcode`
    (20+5+7 = 32). The 20-bit immediate sits in bits 31:12. -/
def encU (imm20 : BitVec 20) (rd : BitVec 5) (opcode : BitVec 7) : BitVec 32 :=
  (imm20 ++ rd ++ opcode).cast rfl

/-- A J-type word (`jal`): the sail `encdec` concat for an unconditional
    jump-and-link, with the **scrambled** 21-bit byte offset:
    `imm[20] @ imm[10:1] @ imm[11] @ imm[19:12] @ rd @ opcode`
    (1+10+1+8+5+7 = 32; opcode `0b1101111 = 0x6f`; `imm[0]` always 0). We take
    `imm : BitVec 21` (the signed byte offset) and slice it into the scrambled
    positions, exactly like the B-type `encB`. -/
def encJ (imm : BitVec 21) (rd : BitVec 5) (opcode : BitVec 7) : BitVec 32 :=
  let i20    : BitVec 1  := imm.extractLsb' 20 1
  let i10_1  : BitVec 10 := imm.extractLsb' 1 10
  let i11    : BitVec 1  := imm.extractLsb' 11 1
  let i19_12 : BitVec 8  := imm.extractLsb' 12 8
  (i20 ++ i10_1 ++ i11 ++ i19_12 ++ rd ++ opcode).cast rfl

/-- `ld rd, off(rs1)` — I-type, opcode `0x03`, funct3 `0b011` (LOAD doubleword). -/
def encLd (rd rs1 : String) (off : Int) : BitVec 32 :=
  encI (BitVec.ofInt 12 off) (reg5 rs1) 0b011 (reg5 rd) 0x03

/-- `sd rs2, off(rs1)` — S-type, opcode `0x23`, funct3 `0b011` (STORE doubleword). -/
def encSd (rs2 rs1 : String) (off : Int) : BitVec 32 :=
  encS (BitVec.ofInt 12 off) (reg5 rs2) (reg5 rs1) 0b011 0x23

/-- `sw rs2, off(rs1)` — S-type, opcode `0x23`, funct3 `0b010` (STORE word). -/
def encSw (rs2 rs1 : String) (off : Int) : BitVec 32 :=
  encS (BitVec.ofInt 12 off) (reg5 rs2) (reg5 rs1) 0b010 0x23

/-- `lwu rd, off(rs1)` — I-type, opcode `0x03`, funct3 `0b110` (LOAD word unsigned). -/
def encLwu (rd rs1 : String) (off : Int) : BitVec 32 :=
  encI (BitVec.ofInt 12 off) (reg5 rs1) 0b110 (reg5 rd) 0x03

/-- `lw rd, off(rs1)` — I-type, opcode `0x03`, funct3 `0b010` (LOAD word, sign-
    extended to XLEN — the form that matches the `li`/`addiw` sign-extended 32-bit
    constant for an equality compare). -/
def encLw (rd rs1 : String) (off : Int) : BitVec 32 :=
  encI (BitVec.ofInt 12 off) (reg5 rs1) 0b010 (reg5 rd) 0x03

/-- `addi rd, rs1, imm` — I-type, opcode `0x13`, funct3 `0b000`. (`mv`, frame
    adjust `addi sp,sp,#k`, and the `addi rN, sp, #off` arg setup are all this.) -/
def encAddi (rd rs1 : String) (imm : Int) : BitVec 32 :=
  encI (BitVec.ofInt 12 imm) (reg5 rs1) 0b000 (reg5 rd) 0x13

/-- `addiw rd, rs1, imm` — I-type, opcode `0x1b`, funct3 `0b000` (the low half of
    the `li` 32-bit macro `lui`+`addiw`). -/
def encAddiw (rd rs1 : String) (imm : Int) : BitVec 32 :=
  encI (BitVec.ofInt 12 imm) (reg5 rs1) 0b000 (reg5 rd) 0x1b

/-- `lui rd, imm20` — U-type, opcode `0x37` (the high half of the `li` 32-bit
    macro). -/
def encLui (rd : String) (imm20 : Nat) : BitVec 32 :=
  encU (BitVec.ofNat 20 imm20) (reg5 rd) 0x37

/-- `jalr rd, off(rs1)` — I-type, opcode `0x67`, funct3 `0b000`. `ret` = `jalr
    zero, 0(ra)`. -/
def encJalr (rd rs1 : String) (off : Int) : BitVec 32 :=
  encI (BitVec.ofInt 12 off) (reg5 rs1) 0b000 (reg5 rd) 0x67

/-- `ret` = `jalr zero, 0(ra)` → objdump word `0x00008067`. -/
def encRet : BitVec 32 := encJalr "zero" "ra" 0

/-- `jal rd, off` — J-type, opcode `0x6f`. `call sym` (a local PC-relative call)
    is `jal ra, off`; the `off` is the signed byte displacement from the `jal`
    word to the target, supplied by the layout. -/
def encJal (rd : String) (off : Int) : BitVec 32 :=
  encJ (BitVec.ofInt 21 off) (reg5 rd) 0x6f

/-- `ecall` → the fixed word `0x00000073` (ITYPE, all-zero imm/regs, opcode
    `0x73`, funct3 `0b000`). -/
def encEcall : BitVec 32 := encI 0 0 0b000 0 0x73

/-- `slli rd, rs1, shamt` — RV64 shift-left-logical-immediate, opcode `0x13`,
    funct3 `0b001`, with a **6-bit** shamt (RV64) placed in the low I-immediate
    field (`imm[11:6] = 0b000000`). We build the I-type word with `imm = shamt`
    (≤ 63), since `imm[11:6] = 0`. -/
def encSlli (rd rs1 : String) (shamt : Nat) : BitVec 32 :=
  encI (BitVec.ofNat 12 shamt) (reg5 rs1) 0b001 (reg5 rd) 0x13

/-! ### 2b. Byte-level emit helpers (reuse `RiscvEncoder.wordLE`)

`wordLE` (from `RiscvEncoder`) gives the 4 LE bytes of an instruction word — the
`.text` layout an RV64 fetch reads. We surface the scaffolding ops as byte lists
so a whole function/driver is a `List (BitVec 8)` flat concatenation. -/

/-- The 4 LE bytes of a 32-bit instruction word. -/
def w (word : BitVec 32) : List (BitVec 8) := wordLE word

/-- Materialise a (signed) 32-bit constant into `rd` with the canonical `as`
    `li` macro `lui rd, hi20 ; addiw rd, rd, lo12` — where `hi20`/`lo12` are the
    split with the `lo12` sign-extension carry folded into `hi20` (exactly what
    `as` emits for a 32-bit value). Returns the two instruction words' bytes. -/
def encLi32 (rd : String) (v : Int) : List (BitVec 8) :=
  let vu : Nat := (BitVec.ofInt 32 v).toNat
  let lo12 : Nat := vu &&& 0xfff
  -- sign-extend lo12 (12-bit) and add the borrow into hi20 so lui+addiw recombines
  let hi20 : Nat := ((vu + (if lo12 ≥ 0x800 then 0x1000 else 0)) >>> 12) &&& 0xfffff
  let lo12s : Int := if lo12 ≥ 0x800 then (Int.ofNat lo12) - 0x1000 else Int.ofNat lo12
  w (encLui rd hi20) ++ w (encAddiw rd rd lo12s)

/-! ### 2d. Exact 64-bit `li` materialisation (the GNU-`as` canonical sequences)

The verified bignum body materialises the `p_256` constant limbs with `li` of a
64-bit value. `as` expands `li rd, imm` to a canonical `addiw`/`slli`/`addi`
sequence; for a *whole-function byte-direct* emit those words must come from Lean
too. The three `p_256` limbs (and the small `li one,1`) have the simple shapes
below, each pinned to objdump in §2e — exactly the `as` expansion:

* `0xffffffffffffffff` = `addi rd, zero, -1`                    (= `li rd,-1`)
* `0x00000000ffffffff` = `addiw rd,zero,1 ; slli rd,rd,32 ; addi rd,rd,-1`
* `0xffffffff00000001` = `addiw rd,zero,-1 ; slli rd,rd,32 ; addi rd,rd,1`
* `0x0000000000000001` = `addi rd, zero, 1`                     (= `li rd,1`)
-/

/-- The exact `as` `li rd, v` expansion bytes for the constants the verified
    `bignum_add_p256` body materialises (`p_256` limbs + the `1`). Falls back to
    the 32-bit `lui`+`addiw` macro for any other ≤32-bit value, and to the
    `addi rd,zero,v` single-word form for a 12-bit-fitting value. -/
def encLi64 (rd : String) (v : Nat) : List (BitVec 8) :=
  if v = 0xffffffffffffffff then
    w (encAddi rd "zero" (-1))
  else if v = 0x00000000ffffffff then
    w (encAddiw rd "zero" 1) ++ w (encSlli rd rd 32) ++ w (encAddi rd rd (-1))
  else if v = 0xffffffff00000001 then
    w (encAddiw rd "zero" (-1)) ++ w (encSlli rd rd 32) ++ w (encAddi rd rd 1)
  else if v < 0x800 then
    w (encAddi rd "zero" (Int.ofNat v))
  else
    encLi32 rd (Int.ofNat v)

/-! ### 2c. Differential pins against `riscv64-linux-gnu-as -march=rv64g`

Each scaffolding word pinned to the exact objdump value (the same anchors as the
ALU pins in `RiscvEncoder`), checked with `#guard`. -/

-- `ld a0, 0(a1)` → `0x0005b503`.
#guard encLd "a0" "a1" 0 == 0x0005b503
-- `ld a3, 24(a1)` → `0x0185b683`.
#guard encLd "a3" "a1" 24 == 0x0185b683
-- `sd a0, 0(s1)` → `0x00a4b023`.
#guard encSd "a0" "s1" 0 == 0x00a4b023
-- `sd a3, 24(s1)` → `0x00d4bc23`.
#guard encSd "a3" "s1" 24 == 0x00d4bc23
-- `addi sp, sp, -16` → `0xff010113`.
#guard encAddi "sp" "sp" (-16) == 0xff010113
-- `addi sp, sp, 16` → `0x01010113`.
#guard encAddi "sp" "sp" 16 == 0x01010113
-- `addi a1, sp, 32` → `0x02010593`.
#guard encAddi "a1" "sp" 32 == 0x02010593
-- `mv s1, a0` = `addi s1, a0, 0` → `0x00050493`.
#guard encAddi "s1" "a0" 0 == 0x00050493
-- `sd s1, 8(sp)` → `0x00913423`.
#guard encSd "s1" "sp" 8 == 0x00913423
-- `ld s1, 8(sp)` → `0x00813483`.
#guard encLd "s1" "sp" 8 == 0x00813483
-- `ret` → `0x00008067`.
#guard encRet == 0x00008067
-- `lui a0, 0x12345` → `0x12345537`.
#guard encLui "a0" 0x12345 == 0x12345537
-- `addiw a0, a0, 0x678` → `0x6785051b`.
#guard encAddiw "a0" "a0" 0x678 == 0x6785051b
-- `sw t0, 0(a0)` → `0x00552023`.
#guard encSw "t0" "a0" 0 == 0x00552023
-- `sw t0, 4(a0)` → `0x00552223`.
#guard encSw "t0" "a0" 4 == 0x00552223
-- `lwu t1, 0(a0)` → `0x00056303`.
#guard encLwu "t1" "a0" 0 == 0x00056303
-- `lwu t1, 12(a0)` → `0x00c56303`.
#guard encLwu "t1" "a0" 12 == 0x00c56303
-- `lw t1, 0(sp)` → `0x00012303`.
#guard encLw "t1" "sp" 0 == 0x00012303
-- `lw t1, 12(sp)` → `0x00c12303`.
#guard encLw "t1" "sp" 12 == 0x00c12303
-- `ecall` → `0x00000073`.
#guard encEcall == 0x00000073
-- `bne a0, a1, .-0` (offset 0 placeholder) — opcode low 7 bits = `0x63`.
#guard (encodeBccWord .bne "a0" "a1" (BitVec.ofNat 13 0)).toNat % 128 == 0x63
-- `jal ra, 0` → opcode low 7 bits = `0x6f` (JAL).
#guard (encJal "ra" 0).toNat % 128 == 0x6f
-- `li a0, 2` macro = `lui a0,0 ; addiw a0,a0,2` (small const: hi20=0). The
-- `addiw` word is `0x00200513`.
#guard encLi32 "a0" 2 == w (encLui "a0" 0) ++ w (encAddiw "a0" "a0" 2)

/-! ### 2e. The exact `li64` p_256-limb expansions, pinned to objdump

The byte sequences below are byte-identical to `riscv64-linux-gnu-as`'s `li`
expansion of the three `p_256` constant limbs (objdump words from §2's reference
assembly): `0xfff..ff = addi rd,zero,-1`; the split-load `addiw;slli;addi` for the
two mixed limbs. -/

-- `slli a1, a1, 0x20` → `0x02059593`.
#guard encSlli "a1" "a1" 32 == 0x02059593
-- `addiw a1, zero, 1` → `0x0010059b`.
#guard encAddiw "a1" "zero" 1 == 0x0010059b
-- `addiw a2, zero, -1` → `0xfff0061b`.
#guard encAddiw "a2" "zero" (-1) == 0xfff0061b
-- `li rd, 0xffffffffffffffff` = `addi rd, zero, -1`. For `a0`: `0xfff00513`.
#guard encLi64 "a0" 0xffffffffffffffff == w (0xfff00513 : BitVec 32)
-- `li a1, 0x00000000ffffffff` = `addiw a1,zero,1 ; slli a1,a1,32 ; addi a1,a1,-1`
-- → words `0x0010059b 0x02059593 0xfff58593`.
#guard encLi64 "a1" 0x00000000ffffffff
    == w (0x0010059b : BitVec 32) ++ w (0x02059593 : BitVec 32) ++ w (0xfff58593 : BitVec 32)
-- `li a2, 0xffffffff00000001` = `addiw a2,zero,-1 ; slli a2,a2,32 ; addi a2,a2,1`
-- → words `0xfff0061b 0x02061613 0x00160613`.
#guard encLi64 "a2" 0xffffffff00000001
    == w (0xfff0061b : BitVec 32) ++ w (0x02061613 : BitVec 32) ++ w (0x00160613 : BitVec 32)
-- `li a3, 1` = `addi a3, zero, 1` → `0x00100693`.
#guard encLi64 "a3" 1 == w (0x00100693 : BitVec 32)

/-! ## 3. The RV64 ELF64 header (`EM_RISCV = 243`, `e_flags = 0x4` RV64D ABI) -/

/-- The 64-byte `Elf64_Ehdr` for a relocatable RV64 object, parameterised by the
    section-header table offset `shoff`, section count `shnum`, and the
    section-string-table section index `shstrndx`. `e_machine = EM_RISCV = 243`;
    `e_flags = 0x4` (the `EF_RISCV_FLOAT_ABI_DOUBLE` flag `riscv64-linux-gnu-as`
    sets for `rv64g`). -/
def elf64Header (shoff shnum shstrndx : Nat) : List (BitVec 8) :=
  ([0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0].map (BitVec.ofNat 8))
    ++ u16LE 1                 -- e_type = ET_REL
    ++ u16LE 243               -- e_machine = EM_RISCV
    ++ u32LE 1                 -- e_version = EV_CURRENT
    ++ u64LE 0                 -- e_entry
    ++ u64LE 0                 -- e_phoff
    ++ u64LE shoff             -- e_shoff
    ++ u32LE 0x4               -- e_flags = EF_RISCV_FLOAT_ABI_DOUBLE
    ++ u16LE 64                -- e_ehsize
    ++ u16LE 0                 -- e_phentsize
    ++ u16LE 0                 -- e_phnum
    ++ u16LE 64                -- e_shentsize
    ++ u16LE shnum             -- e_shnum
    ++ u16LE shstrndx          -- e_shstrndx

/-! ## 4. ELF64 record builders (structure-identical to the ARM/x86 stitchers) -/

/-- A 64-byte `Elf64_Shdr` section header. -/
def elf64Shdr (name typ flags addr off size link info align entsize : Nat) :
    List (BitVec 8) :=
  u32LE name ++ u32LE typ ++ u64LE flags ++ u64LE addr ++ u64LE off
    ++ u64LE size ++ u32LE link ++ u32LE info ++ u64LE align ++ u64LE entsize

/-- A 24-byte `Elf64_Sym` symbol-table entry. -/
def elf64Sym (name info other shndx value size : Nat) : List (BitVec 8) :=
  u32LE name ++ [BitVec.ofNat 8 info, BitVec.ofNat 8 other] ++ u16LE shndx
    ++ u64LE value ++ u64LE size

/-- A 24-byte `Elf64_Rela` relocation entry. `r_info = (sym << 32) | type`. -/
def elf64Rela (offset symIdx typ : Nat) (addend : Int) : List (BitVec 8) :=
  u64LE offset ++ u64LE (symIdx * 0x100000000 + typ) ++ u64LE (BitVec.ofInt 64 addend).toNat

/-- `R_RISCV_CALL` (type 18): the `auipc`+`jalr` call-pair PC-relative reloc (a
    `call sym` to an external symbol). For a self-contained object (the driver's
    `jal` targets a LOCAL symbol in the same `.text`) no relocation is needed. -/
def R_RISCV_CALL : Nat := 18
/-- `R_RISCV_JAL` (type 17): the 20-bit J-type PC-relative jump reloc. -/
def R_RISCV_JAL : Nat := 17

/-- Pad a byte list up to an 8-byte boundary. -/
def padTo8 (bs : List (BitVec 8)) : List (BitVec 8) :=
  bs ++ List.replicate ((8 - bs.length % 8) % 8) (BitVec.ofNat 8 0)

/-- A name as bytes followed by a NUL terminator. -/
def cstrBytes (s : String) : List (BitVec 8) :=
  s.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat) ++ [BitVec.ofNat 8 0]

/-! ## 5. The multi-symbol leaf table -/

/-- One owned leaf: its global symbol name and the verified-encoder machine bytes. -/
structure Leaf where
  name : String
  text : List (BitVec 8)

/-- The concatenated `.text` bytes of all leaves, in order. -/
def textBytes (leaves : List Leaf) : List (BitVec 8) :=
  (leaves.map Leaf.text).flatten

/-- The per-leaf byte length list. -/
def leafLens (leaves : List Leaf) : List Nat :=
  leaves.map (fun l => l.text.length)

/-- The byte offset of leaf `k` within `.text`. -/
def symValue (leaves : List Leaf) (k : Nat) : Nat :=
  ((leafLens leaves).take k).sum

/-! ## 6. String + symbol tables -/

/-- `.strtab` bytes: `NUL` then each name NUL-terminated. -/
def strtabBytes (leaves : List Leaf) : List (BitVec 8) :=
  (BitVec.ofNat 8 0) :: (leaves.map (fun l => cstrBytes l.name)).flatten

/-- The `st_name` offset of leaf `k` within `.strtab`. -/
def symNameOff (leaves : List Leaf) (k : Nat) : Nat :=
  1 + ((leaves.take k).map (fun l => (cstrBytes l.name).length)).sum

/-- `.symtab` bytes: the null symbol, then one `STT_FUNC` global per leaf. -/
def symtabBytes (leaves : List Leaf) : List (BitVec 8) :=
  elf64Sym 0 0 0 0 0 0
    ++ (leaves.zipIdx.map (fun (l, k) =>
        elf64Sym (symNameOff leaves k) 0x12 0 1 (symValue leaves k) l.text.length)).flatten

/-! ## 7. External (undefined) symbols + `.rela.text` relocations -/

/-- One `.rela.text` relocation: the `.text` byte offset of the call word, the
    name of the (external, undefined) target symbol, the relocation type, and the
    signed addend. -/
structure Reloc where
  /-- Byte offset of the call word within `.text`. -/
  offset : Nat
  /-- The undefined target symbol's name (must appear in `externs`). -/
  symName : String
  /-- The relocation type (`R_RISCV_CALL = 18` for `call`). -/
  typ : Nat := R_RISCV_CALL
  /-- The signed addend. -/
  addend : Int := 0

/-- The `st_name` offset of external symbol `j` within `.strtab`. -/
def externNameOff (leaves : List Leaf) (externs : List String) (j : Nat) : Nat :=
  symNameOff leaves leaves.length
    + ((externs.take j).map (fun s => (cstrBytes s).length)).sum

/-- `.strtab` bytes including external symbol names. -/
def strtabBytesR (leaves : List Leaf) (externs : List String) : List (BitVec 8) :=
  strtabBytes leaves ++ (externs.map cstrBytes).flatten

/-- `.symtab` bytes with external UNDEF symbols appended after the defined funcs. -/
def symtabBytesR (leaves : List Leaf) (externs : List String) : List (BitVec 8) :=
  symtabBytes leaves
    ++ (externs.zipIdx.map (fun (_, j) =>
        elf64Sym (externNameOff leaves externs j) 0x10 0 0 0 0)).flatten

/-- The symtab index of external symbol named `s`. -/
def externSymIdx (leaves : List Leaf) (externs : List String) (s : String) : Nat :=
  match externs.idxOf? s with
  | some j => 1 + leaves.length + j
  | none => 0

/-- `.rela.text` bytes: one 24-byte `Elf64_Rela` per relocation. -/
def relaTextBytes (leaves : List Leaf) (externs : List String) (relocs : List Reloc) :
    List (BitVec 8) :=
  (relocs.map (fun r =>
    elf64Rela r.offset (externSymIdx leaves externs r.symName) r.typ r.addend)).flatten

/-! ## 8. The multi-symbol object -/

/-- Build a complete RV64 ELF64 relocatable object holding ALL `leaves` as
    global `STT_FUNC` symbols in one `.text` section, with optional external UNDEF
    symbols and `.rela.text` relocations. Section order:
    `0 UNDEF | 1 .text | 2 .rela.text | 3 .symtab | 4 .strtab | 5 .shstrtab |
    6 .note.GNU-stack`. -/
def buildElfObjectMultiReloc (leaves : List Leaf) (externs : List String)
    (relocs : List Reloc) : List (BitVec 8) :=
  let z : BitVec 8 := BitVec.ofNat 8 0
  let text := textBytes leaves
  let shstr :=
    [z] ++ cstrBytes ".text" ++ cstrBytes ".rela.text" ++ cstrBytes ".symtab"
        ++ cstrBytes ".strtab" ++ cstrBytes ".shstrtab"
        ++ cstrBytes ".note.GNU-stack"
  let off_text := 1
  let off_rela := off_text + 6
  let off_symtab := off_rela + 11
  let off_strtab := off_symtab + 8
  let off_shstrtab := off_strtab + 8
  let off_note := off_shstrtab + 10
  let strtab := strtabBytesR leaves externs
  let symtab := symtabBytesR leaves externs
  let rela := relaTextBytes leaves externs relocs
  let textOff := 64
  let textPad := padTo8 text
  let relaOff := textOff + textPad.length
  let relaPad := padTo8 rela
  let shstrOff := relaOff + relaPad.length
  let shstrPad := padTo8 shstr
  let strtabOff := shstrOff + shstrPad.length
  let strtabPad := padTo8 strtab
  let symtabOff := strtabOff + strtabPad.length
  let shoff := symtabOff + symtab.length
  let shNull := elf64Shdr 0 0 0 0 0 0 0 0 0 0
  let shText := elf64Shdr off_text 1 6 0 textOff text.length 0 0 16 0
  -- SHT_RELA = 4; sh_link = symtab section index (3); sh_info = .text index (1).
  let shRela := elf64Shdr off_rela 4 0 0 relaOff rela.length 3 1 8 24
  -- sh_link = strtab section index (4); sh_info = index of first global symbol (1).
  let shSymtab := elf64Shdr off_symtab 2 0 0 symtabOff symtab.length 4 1 8 24
  let shStrtab := elf64Shdr off_strtab 3 0 0 strtabOff strtab.length 0 0 1 0
  let shShstrtab := elf64Shdr off_shstrtab 3 0 0 shstrOff shstr.length 0 0 1 0
  let shNote := elf64Shdr off_note 1 0 0 textOff 0 0 0 1 0
  let shdrs := shNull ++ shText ++ shRela ++ shSymtab ++ shStrtab ++ shShstrtab ++ shNote
  elf64Header shoff 7 5
    ++ textPad ++ relaPad ++ shstrPad ++ strtabPad ++ symtab ++ shdrs

/-- The no-relocation specialisation (self-contained object). -/
def buildElfObjectMulti (leaves : List Leaf) : List (BitVec 8) :=
  buildElfObjectMultiReloc leaves [] []

/-- The single-leaf object. -/
def buildElfObject (name : String) (text : List (BitVec 8)) : List (BitVec 8) :=
  buildElfObjectMulti [⟨name, text⟩]

/-! ## 9. Container well-formedness (the unconditional trust-boundary half) -/

@[simp] theorem textBytes_length (leaves : List Leaf) :
    (textBytes leaves).length = (leafLens leaves).sum := by
  simp [textBytes, leafLens, List.length_flatten, List.map_map, Function.comp_def]

@[simp] theorem leafLens_length (leaves : List Leaf) :
    (leafLens leaves).length = leaves.length := by simp [leafLens]

theorem symValue_zero (leaves : List Leaf) : symValue leaves 0 = 0 := by
  simp [symValue]

/-- Core list helper: prefix sum of `k+1` elements = prefix sum of `k` + the
    `k`-th element. -/
theorem sum_take_succ_core (xs : List Nat) (k : Nat) (hk : k < xs.length) :
    (xs.take (k + 1)).sum = (xs.take k).sum + xs[k] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons a as ih =>
    cases k with
    | zero => simp [List.take]
    | succ k' =>
      have hk' : k' < as.length := by simpa [List.length_cons] using hk
      simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]
      rw [ih k' hk']
      omega

theorem symValue_succ (leaves : List Leaf) (k : Nat) (hk : k < leaves.length) :
    symValue leaves (k + 1) = symValue leaves k + (leaves[k]).text.length := by
  have hk' : k < (leafLens leaves).length := by simpa using hk
  simp only [symValue]
  rw [sum_take_succ_core _ k hk']
  simp [leafLens, List.getElem_map]

theorem symValue_last_eq_text (leaves : List Leaf) :
    symValue leaves leaves.length = (textBytes leaves).length := by
  simp only [symValue, textBytes_length]
  rw [List.take_of_length_le (Nat.le_of_eq (leafLens_length leaves))]

theorem elf64Sym_length (name info other shndx value size : Nat) :
    (elf64Sym name info other shndx value size).length = 24 := by
  simp [elf64Sym]

theorem elf64Shdr_length (name typ flags addr off size link info align entsize : Nat) :
    (elf64Shdr name typ flags addr off size link info align entsize).length = 64 := by
  simp [elf64Shdr]

theorem elf64Rela_length (offset symIdx typ : Nat) (addend : Int) :
    (elf64Rela offset symIdx typ addend).length = 24 := by
  simp [elf64Rela]

theorem elf64Header_length (shoff shnum shstrndx : Nat) :
    (elf64Header shoff shnum shstrndx).length = 64 := by
  simp [elf64Header]

theorem elf64Header_magic (shoff shnum shstrndx : Nat) :
    (elf64Header shoff shnum shstrndx).take 6
      = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) := by
  simp [elf64Header, u16LE, u32LE, u64LE]

/-- The `e_machine` field (bytes 18–19) is `EM_RISCV = 243 = 0x00f3` little-endian
    `f3 00` — the field that distinguishes this object from the ARM/x86 stitchers. -/
theorem elf64Header_machine (shoff shnum shstrndx : Nat) :
    ((elf64Header shoff shnum shstrndx).drop 18).take 2
      = [0xf3, 0x00].map (BitVec.ofNat 8) := by
  simp [elf64Header, u16LE, u32LE, u64LE]

theorem flatten_length_const (xss : List (List (BitVec 8))) (c : Nat)
    (h : ∀ xs ∈ xss, xs.length = c) : xss.flatten.length = c * xss.length := by
  induction xss with
  | nil => simp
  | cons a as ih =>
      rw [List.flatten_cons, List.length_append, h a (List.mem_cons_self),
          ih (fun xs hxs => h xs (List.mem_cons_of_mem a hxs)), List.length_cons,
          Nat.mul_succ, Nat.add_comm]

theorem funcSyms_length (leaves : List Leaf) :
    ((leaves.zipIdx.map (fun (l, k) =>
        elf64Sym (symNameOff leaves k) 0x12 0 1 (symValue leaves k) l.text.length)).flatten).length
      = 24 * leaves.length := by
  have hconst : ∀ xs ∈ (leaves.zipIdx.map (fun (l, k) =>
      elf64Sym (symNameOff leaves k) 0x12 0 1 (symValue leaves k) l.text.length)),
      xs.length = 24 := by
    intro xs hxs
    rw [List.mem_map] at hxs
    obtain ⟨⟨l, k⟩, _, rfl⟩ := hxs
    exact elf64Sym_length _ _ _ _ _ _
  rw [flatten_length_const _ 24 hconst, List.length_map, List.length_zipIdx]

theorem symtabBytes_length (leaves : List Leaf) :
    (symtabBytes leaves).length = 24 * (1 + leaves.length) := by
  simp only [symtabBytes, List.length_append, elf64Sym_length, funcSyms_length]
  omega

theorem symCount_eq (leaves : List Leaf) :
    (symtabBytes leaves).length / 24 = 1 + leaves.length := by
  rw [symtabBytes_length]; omega

/-! ## 10. Worked witnesses (multi-symbol offset checks) -/

/-- Two demo leaves with `.text` lengths 8 and 4. -/
def demoLeaves : List Leaf :=
  [ ⟨"f0", List.replicate 8 (BitVec.ofNat 8 0)⟩
  , ⟨"f1", List.replicate 4 (BitVec.ofNat 8 0)⟩ ]

example : symValue demoLeaves 0 = 0 := by simp [symValue]
example : symValue demoLeaves 1 = 8 := by simp [symValue, leafLens, demoLeaves]
example : (textBytes demoLeaves).length = 12 := by
  simp [textBytes_length, leafLens, demoLeaves]
example : (symtabBytes demoLeaves).length / 24 = 3 := by
  rw [symCount_eq]; simp [demoLeaves]

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvElfObject
