/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayVsimdEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject

/-!
# The ChaCha20 4-way AoS→SoA transpose as a standalone ELF object

The marshalling half of the ChaCha20 4-way block, wrapped on its own as a
single-symbol ELF64 relocatable object. The `.text` is Phase A of
`Chacha4WayVsimdEmit` — the four `_MM_TRANSPOSE4` word-group transposes reading
AoS rows from `%rsi` and writing SoA words to `%rdi` — followed by the
two-pointer return-value epilogue `mov %rdi,%rax ; ret`.

```
  chacha_transpose_4way (out=%rdi, inp=%rsi)
    for g in 0..3: vmovdqu loads (%rsi) ; transpose4BytesU ; stores (%rdi)
    mov %rdi,%rax ; ret
    = encodeTranspose4way : List (BitVec 8)
    --buildElfObject-->  chacha_transpose_4way.o     (no gas, no jasminc)
```

## ABI

`uint32_t *chacha_transpose_4way(uint32_t *out, const uint32_t *inp)`

* `inp` (SysV `%rsi`): four AoS blocks of sixteen `u32`, word `j` of block `b`
  at `inp[16*b + j]`.
* `out` (SysV `%rdi`): sixteen SoA words of four lanes,
  `out[4*k + lane] = inp[16*lane + k]`.
* Returns `out` in `%rax`.

The byte addresses realise that index formula: word-group `g` loads block `b`'s
four words from `%rsi + 64*b + 16*g` and stores transpose column `j` to
`%rdi + 16*(4*g + j)`, so the word at SoA index `k = 4*g + j`, lane `l`, is the
AoS word `inp[16*l + k]`.

## Relation to the whole-block object

`Chacha4WayVsimdEmit.chacha20_4way_blockObject` contains the same Phase A
composed with the rounds and the inverse Phase C transpose. Phase A and Phase C
share the `transpose4BytesU` body, so a lane-permutation error in that body
cancels between them: the lane-parallel rounds commute with a permutation of the
four lanes, and Phase C undoes what Phase A applied. This object exposes Phase A
alone, where the lane assignment is observable at the ABI boundary.

## Trust posture

The transpose body bytes and the ABI glue are gas-pinned in
`VIR.VsimdChachaByteEncoder`; the VEX SIMD opcodes have no ACL2 x86isa decode
tables, so this sits at the gas-pinned validation tier, as with the rest of the
SIMD byte path. The value-level check is the C harness
`bench/chacha_compare/chacha_transpose_4way_kat.c`, which compares against a
scalar reference transpose of the RFC 8439 §2.3.2 state.

That standalone check is not redundant with the whole-block KAT: Phase A and
Phase C share an encoder body and the rounds are lane-parallel, so a lane
permutation in the transpose cancels end to end and only a check at the ABI
boundary observes it.

## Main definitions

* `encodeTranspose4way`: `Chacha4WayVsimdEmit.encodePhaseA` followed by
  `encRetOutPtrU`, the `mov %rdi,%rax ; ret` epilogue this harness expects
* `transpose4wayObject`: those bytes as a relocatable ELF object
* `objectPath`, `emitObject`: the writer

## Main results

* `transpose4wayObject_header`: the object opens with the ELF magic, as an instance
  of the parametric `ElfObject.buildElfObject_magic`
* `encodeTranspose4way_tail`, `encodeTranspose4way_length`: the epilogue and size
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayTransposeObjectEmit

open CatCrypt.Crypto.SecureCompilation.VIR.VsimdChachaByteEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject

/-! ## 1. The kernel bytes -/

/-- The AoS→SoA transpose kernel as machine bytes: the four Phase-A word-group
    transposes (`Chacha4WayVsimdEmit.encodePhaseA`) followed by the two-pointer
    return-value epilogue `mov %rdi,%rax ; ret`. -/
def encodeTranspose4way : List (BitVec 8) :=
  Chacha4WayVsimdEmit.encodePhaseA ++ encRetOutPtrU

/-- The kernel wrapped as a single-symbol ELF64 relocatable object — symbol
    `chacha_transpose_4way`, the C harness's `extern`. -/
def transpose4wayObject : List (BitVec 8) :=
  buildElfObject "chacha_transpose_4way" encodeTranspose4way

/-! ## 2. Structural pins -/

/-- The kernel ends with the two-pointer return-value epilogue `mov %rdi,%rax ; ret`. -/
theorem encodeTranspose4way_tail :
    encodeTranspose4way.drop (encodeTranspose4way.length - 4)
      = [0x48, 0x89, 0xf8, 0xc3].map (BitVec.ofNat 8) := by
  have h : encRetOutPtrU.length = 4 := by simp [encRetOutPtrU]
  rw [encodeTranspose4way, List.length_append, h, Nat.add_sub_cancel, List.drop_left,
    encRetOutPtrU]

/-- The kernel `.text` is exactly Phase A plus the four epilogue bytes. -/
theorem encodeTranspose4way_length :
    encodeTranspose4way.length = Chacha4WayVsimdEmit.encodePhaseA.length + 4 := by
  have h : encRetOutPtrU.length = 4 := by simp [encRetOutPtrU]
  rw [encodeTranspose4way, List.length_append, h]

/-- The object begins with the `Elf64_Ehdr` magic and the 64-bit/little-endian
    class bytes (`ElfObject.buildElfObject_magic` at this kernel). -/
theorem transpose4wayObject_header :
    transpose4wayObject.take 6 = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) :=
  buildElfObject_magic _ _

/-! ## 3. Object file emission -/

/-- The repository-root-relative path of the emitted object, the path the C
    harness's link step names. -/
def objectPath : System.FilePath :=
  "bench/chacha_compare/gen_owned_simd/chacha_transpose_4way.o"

/-- `List (BitVec 8)` to `ByteArray`, the form `IO.FS.writeBinFile` consumes. -/
def bytesToByteArray (bs : List (BitVec 8)) : ByteArray :=
  ⟨(bs.map (fun b => UInt8.ofNat b.toNat)).toArray⟩

/-- Write `transpose4wayObject` to `objectPath`, creating the output directory.
    Run from the repository root. -/
def emitObject : IO Unit := do
  IO.FS.createDirAll "bench/chacha_compare/gen_owned_simd"
  IO.FS.writeBinFile objectPath (bytesToByteArray transpose4wayObject)
  IO.println s!"WROTE {objectPath}  ({transpose4wayObject.length} bytes ELF64 .o)"
  IO.println s!"  .text = {encodeTranspose4way.length} bytes (Phase A + `mov %rdi,%rax ; ret`)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Chacha4WayTransposeObjectEmit
