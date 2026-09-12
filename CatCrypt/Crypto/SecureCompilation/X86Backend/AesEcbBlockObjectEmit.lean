/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder
public import CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject

/-!
# The AES-128 ECB single-block encrypt kernel as an owned-emitted ELF object

`aes128_ecb_block` is the AES-128 single-block encryption core: the `vmovdqu`
round-key and plaintext loads, the `VAESENC`/`VAESENCLAST` round chain, and the
ciphertext store. The bytes come from the unified `SimdOp` encoder
(`VIR.VsimdByteEncoder.encodeVsimdAesEcbBlock`) and are stitched into a
single-symbol relocatable object by `ElfObject.buildElfObject`; there is no
assembler on the artifact path.

## ABI

`void aes128_ecb_block(uint8_t *buf)` — SysV, so `buf = %rdi`. The buffer is a
208-byte struct: eleven 16-byte round keys, then the 16-byte plaintext, then the
16-byte ciphertext output.

## Trust posture

The 134 kernel bytes are pinned byte-identical to what `gas` assembles for the
same body (`VsimdByteEncoder.encodeVsimdAesEcbBlock_eq_gas`). The value-level
FIPS-197 Appendix B / C.1 check runs in the bench harnesses
(`bench/aes_compare/aes128_ecb_block_owned_kat.c`, and composed into AES-XTS by
`bench/aes_xts_compare/aes_xts_kat.c`).

`X86Backend.SimdBytesVsimd` renders the same symbol and the same 208-byte ABI as
AT&T `.s` text from `Com jasminDialect`.

## Main definitions

* `aesEcbBlockObject`: the kernel bytes wrapped as a relocatable ELF object
* `emitMain`: the writer, run at elaboration

## Main results

* `aesEcbBlockObject_header`: the object opens with the ELF magic, as an instance
  of the parametric `ElfObject.buildElfObject_magic`, so no text byte is
  evaluated
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.AesEcbBlockObjectEmit

open CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder (encodeVsimdAesEcbBlock)

/-! ## 1. The object -/

/-- The kernel wrapped as a single-symbol ELF64 relocatable object — symbol
    `aes128_ecb_block`, the C harnesses' `extern`. -/
def aesEcbBlockObject : List (BitVec 8) :=
  ElfObject.buildElfObject "aes128_ecb_block" encodeVsimdAesEcbBlock

/-! ## 2. Structural pin -/

/-- The object begins with the `Elf64_Ehdr` magic and the 64-bit little-endian
    class bytes (`ElfObject.buildElfObject_magic` at this kernel). -/
theorem aesEcbBlockObject_header :
    aesEcbBlockObject.take 6 = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) :=
  ElfObject.buildElfObject_magic _ _

/-! ## 3. Artifact writer -/

/-- Pack a `List (BitVec 8)` into a `ByteArray` for binary output. -/
def toByteArray (bs : List (BitVec 8)) : ByteArray :=
  bs.foldl (fun acc b => acc.push (UInt8.ofNat b.toNat)) ByteArray.empty

/-- The bench object directory, relative to the repository root. -/
def genDir : String := "bench/aes_compare/gen_owned_simd"

/-- Write the relocatable object to
    `gen_owned_simd/aes128_ecb_block_owned_bytes.o`. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll genDir
  let path := genDir ++ "/aes128_ecb_block_owned_bytes.o"
  IO.FS.writeBinFile path (toByteArray aesEcbBlockObject)
  IO.println s!"WROTE {path}  ({aesEcbBlockObject.length} bytes ELF64 .o, no assembler)"

/-! ## 4. Artifact generation at elaboration

The object is written while this module elaborates, so `lake` owns the dependency
between the encoder and the bench artifact. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.AesEcbBlockObjectEmit
