/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayVsimdEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayVsimdEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes

/-!
# The ChaCha20 4-way quarter-round core as an owned-emitted ELF object

`chacha20_qr_4way` is the register-resident RFC 8439 §2.1 quarter-round over four
128-bit SoA state words: the packed-ALU core (`VPADDD` / `VPXOR` / `VPSLLD` /
`VPSRLD` / `VPOR`, the 16/12/8/7 rotates), taken on its own rather than inside a
whole block.

## ABI

`void chacha20_qr_4way(uint32_t *abcd)` — SysV, so `abcd = %rdi`. The buffer holds
the four state words `a,b,c,d`, each a 128-bit group of four lanes
(`abcd[4*k + lane]`, i.e. word `k` at byte offset `16·k`), updated **in place**.
The function returns nothing, so the epilogue is the bare `ret`
(`LeafBytes.encRet`) — not the `mov %rdi,%rax ; ret` form
(`VsimdChachaByteEncoder.encRetOutPtrU`) that a pointer-returning kernel such as
`Chacha4WayVsimdEmit`'s whole-block `chacha20_4way_block` uses.

This is a different symbol and a different ABI from `chacha20_4way_block`; the two
objects are siblings, not substitutes.

## Composition

```
  chacha20_qr_4way (abcd=%rdi)
    Chacha4WayVsimdEmit.encodeQR 0 1 2 3
      vmovdqu 0/16/32/48(%rdi) -> xmm0..3
      VsimdChachaByteEncoder.cbQRBytesU        (register-resident quarter-round)
      vmovdqu xmm0..3 -> 0/16/32/48(%rdi)
    ++ LeafBytes.encRet                         (ret)
    = emit : List (BitVec 8)
    --ElfObject.buildElfObject-->  chacha20_qr_4way.o
```

No `gas` and no `jasminc` on the artifact path.

## Trust posture

The same residual as the rest of the SIMD byte path: the quarter-round body bytes
and the `vmovdqu` ABI glue are gas-pinned in `VsimdChachaByteEncoder`
(`cbQRBytesU_eq_gas` and the per-encoder pins), and the VEX SIMD opcodes have no
ACL2 x86isa decode tables, so this stays at the gas-pinned validation tier. The
value-level RFC 8439 §2.1.1 check runs in the bench harness
(`bench/chacha_compare/chacha_4way_owned_kat.c`), which broadcasts the §2.1.1
input across all four lanes.

## Main definitions

* `emit`: the kernel bytes, `Chacha4WayVsimdEmit.encodeQR 0 1 2 3` followed by
  `LeafBytes.encRet` — a bare `ret`, since the harness declares `void`
* `chacha20_qr_4wayObject`: those bytes wrapped as a relocatable ELF object
* `writeObject`, `writeByteListing`, `emitMain`: the writers

## Main results

* `encodeQR_0_1_2_3_offsets`: the loads and stores address words 0..3 at byte
  offsets 0/16/32/48 of `%rdi`, matching the in-place `uint32_t *` ABI
* `encVmovdquBaseU_length_zero`, `encVmovdquBaseU_length_disp8`,
  `encVexShiftLaneU_length_low`: the per-encoder byte counts, parametric in the
  register and displacement operands
* `cbQRBytesU_length`, `encodeQR_0_1_2_3_length`, `emit_length_eq`,
  `emit_length`: the kernel is 127 bytes, as a sum of the per-encoder lengths
* `emit_epilogue`: the trailing byte is `ret`
* `chacha20_qr_4wayObject_header`: the object opens with the ELF magic, as an
  instance of the parametric `ElfObject.buildElfObject_magic`, so no text byte is
  evaluated
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayQrObjectEmit

open CatCrypt.Crypto.SecureCompilation.VIR.VsimdChachaByteEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayVsimdEmit (encodeQR)

/-! ## 1. The kernel and its object -/

/-- The quarter-round kernel's `.text` bytes: `encodeQR 0 1 2 3` (the four
    `vmovdqu` loads from `0/16/32/48(%rdi)`, the `cbQRBytesU` body, the four
    `vmovdqu` stores back to the same addresses) followed by the void-return
    epilogue `ret`. -/
def emit : List (BitVec 8) := encodeQR 0 1 2 3 ++ LeafBytes.encRet

/-- The kernel wrapped as a single-symbol ELF64 relocatable object — symbol
    `chacha20_qr_4way`, the C harness's `extern`. -/
def chacha20_qr_4wayObject : List (BitVec 8) :=
  ElfObject.buildElfObject "chacha20_qr_4way" emit

/-! ## 2. Structural pins -/

/-- The four SoA state words sit at `0/16/32/48(%rdi)`, addressed identically on
    the load and the store side, with the quarter-round body between them. -/
theorem encodeQR_0_1_2_3_offsets :
    encodeQR 0 1 2 3 =
      encVmovdquLoadU 0 0 ++ encVmovdquLoadU 1 16 ++ encVmovdquLoadU 2 32
        ++ encVmovdquLoadU 3 48
        ++ cbQRBytesU
        ++ encVmovdquStoreU 0 0 ++ encVmovdquStoreU 1 16 ++ encVmovdquStoreU 2 32
        ++ encVmovdquStoreU 3 48 := rfl

/-- A `vmovdqu` at `disp = 0` is four bytes: the 2-byte VEX prefix, the opcode, and
    a `mod = 00` ModRM with no displacement. -/
theorem encVmovdquBaseU_length_zero (op d rm : Nat) :
    (encVmovdquBaseU op d rm 0).length = 4 := by
  simp [encVmovdquBaseU]

/-- A `vmovdqu` at a nonzero `disp ≤ 127` is five bytes: the `mod = 01` ModRM and
    its single displacement byte. -/
theorem encVmovdquBaseU_length_disp8 (op d rm disp : Nat) (hne : disp ≠ 0)
    (hle : disp ≤ 127) : (encVmovdquBaseU op d rm disp).length = 5 := by
  simp [encVmovdquBaseU, hne, hle]

/-- A VEX lane imm-shift on a low `src` register is five bytes: the 2-byte VEX
    prefix, the `0F 72` opcode, the `/digit` ModRM, and the `imm8`. -/
theorem encVexShiftLaneU_length_low (ext l dst src imm : Nat)
    (hsrc : CryptoExt.bit src 3 = 0) :
    (encVexShiftLaneU ext l dst src imm).length = 5 := by
  rw [encVexShiftLaneU, if_pos hsrc]
  simp

/-- The quarter-round body is 88 bytes: eight 4-byte `encAvx2Alu` ops and four
    14-byte rotate idioms (`VPSLLD` and `VPSRLD` at five bytes each, `VPOR` at
    four). -/
theorem cbQRBytesU_length : cbQRBytesU.length = 88 := by
  simp [cbQRBytesU, cbRotlBytesU, encVpslldU, encVpsrldU, cbA, cbB, cbC, cbD, cbT,
    CryptoExt.encAvx2Alu_length, encVexShiftLaneU_length_low]

/-- The quarter-round encoding is 126 bytes: four `vmovdqu` loads (four bytes at
    `disp = 0`, five each at the `disp8` offsets 16/32/48), the 88-byte
    quarter-round body, and the four matching stores. Every summand is one
    encoder's length, so no byte of the concatenation is enumerated. -/
theorem encodeQR_0_1_2_3_length : (encodeQR 0 1 2 3).length = 126 := by
  rw [encodeQR_0_1_2_3_offsets]
  simp [List.length_append, encVmovdquLoadU, encVmovdquStoreU,
    encVmovdquBaseU_length_zero, encVmovdquBaseU_length_disp8, cbQRBytesU_length]

/-- The kernel is one byte longer than the quarter-round encoding: the `ret`
    epilogue. -/
theorem emit_length_eq : emit.length = (encodeQR 0 1 2 3).length + 1 := by
  rw [emit, List.length_append]
  simp [LeafBytes.encRet]

/-- The kernel is 127 bytes: the 126-byte quarter-round encoding and the one-byte
    `ret`. -/
theorem emit_length : emit.length = 127 := by
  rw [emit_length_eq, encodeQR_0_1_2_3_length]

/-- Everything after the quarter-round body is the single-byte `ret` epilogue. -/
theorem emit_epilogue : emit.drop (encodeQR 0 1 2 3).length = LeafBytes.encRet := by
  rw [emit, List.drop_left]

/-- The object begins with the `Elf64_Ehdr` magic and the 64-bit little-endian
    class bytes (`ElfObject.buildElfObject_magic` at this kernel). -/
theorem chacha20_qr_4wayObject_header :
    chacha20_qr_4wayObject.take 6 = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) :=
  ElfObject.buildElfObject_magic _ _

/-! ## 3. Artifact writers

The bench Makefile links two artifact shapes for this kernel: the relocatable
object `gen_owned_simd/chacha_4way_owned_bytes.o` (target
`chacha-4way-owned-bytes-kat`) and the assembler listing
`gen_owned_simd/chacha_4way_owned.s` (target `chacha-4way-owned-kat`, which hands
the path to `$(CC)`). Both carry the same `.text` bytes; the listing wraps them in
`.byte` directives under the `chacha20_qr_4way` symbol.

These are `IO` actions rather than elaboration-time writes: the paths are bench
artifacts, so a `#eval` here would rewrite them on every library build. The bench
drivers invoke them. -/

/-- Pack a `List (BitVec 8)` into a `ByteArray` for binary output. -/
def toByteArray (bs : List (BitVec 8)) : ByteArray :=
  bs.foldl (fun acc b => acc.push (UInt8.ofNat b.toNat)) ByteArray.empty

/-- The kernel `.text` as a comma-separated list of hex byte literals. -/
def bytesLine : String :=
  String.intercalate ", " (emit.map (fun b => "0x" ++ String.ofList (Nat.toDigits 16 b.toNat)))

/-- The `.byte`-directive assembler listing of the kernel, defining the global
    `chacha20_qr_4way` symbol over the emitted bytes. -/
def byteListing : String :=
  "# ChaCha20 quarter-round 4-way (xmm, 4x u32 SoA) — OWNED x86(+SIMD) byte-direct emit,\n"
  ++ "# no gas and no jasminc on the artifact path.\n"
  ++ "# ABI: void chacha20_qr_4way(uint32_t *abcd), abcd=%rdi, word k at 16*k, in place.\n"
  ++ "# Bytes: Chacha4WayVsimdEmit.encodeQR 0 1 2 3 ++ LeafBytes.encRet\n"
  ++ "#   (quarter-round body gas-pinned by VsimdChachaByteEncoder.cbQRBytesU_eq_gas).\n"
  ++ "\t.text\n\t.globl chacha20_qr_4way\n\t.type chacha20_qr_4way, @function\n"
  ++ "chacha20_qr_4way:\n\t.byte " ++ bytesLine ++ "\n"
  ++ "\t.size chacha20_qr_4way, .-chacha20_qr_4way\n"
  ++ ".section .note.GNU-stack,\"\",@progbits\n"

/-- The bench object directory, relative to the repository root. -/
def genDir : String := "bench/chacha_compare/gen_owned_simd"

/-- Write the relocatable object to `gen_owned_simd/chacha_4way_owned_bytes.o`. -/
def writeObject : IO Unit := do
  IO.FS.createDirAll genDir
  let path := genDir ++ "/chacha_4way_owned_bytes.o"
  IO.FS.writeBinFile path (toByteArray chacha20_qr_4wayObject)
  IO.println s!"WROTE {path}  ({chacha20_qr_4wayObject.length} bytes ELF64 .o, no assembler)"
  IO.println s!"  .text = {emit.length} bytes; symbol chacha20_qr_4way"

/-- Write the `.byte` listing to `gen_owned_simd/chacha_4way_owned.s`. -/
def writeByteListing : IO Unit := do
  IO.FS.createDirAll genDir
  let path := genDir ++ "/chacha_4way_owned.s"
  IO.FS.writeFile path byteListing
  IO.println s!"WROTE {path}  (.byte listing of the {emit.length}-byte owned .text)"

/-- Write both artifact shapes. -/
def emitMain : IO Unit := do
  writeObject
  writeByteListing

end CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayQrObjectEmit
