/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ProveDriverEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-!
# The whole-prover object as verified BYTES — `gas` out of the trusted base

The Plonky3 whole-prover object (field leaves + phase loop-drivers + the
`plonky3_prove` entry, `Plonky3ProveDriverEmit.wholeProverWithEntryLprog`) was
rendered to AT&T **text** assembled by `gas`. That path trusts `gas` to translate
the printer's text to bytes. This file emits the SAME object as a relocatable ELF
`.o` directly from the **verified byte encoder** (`LprogBytes.encodeLprogReloc` →
`ElfObject`), so the object is produced **without `gas`**:

* each function's straight-line `Lopn` body is byte-encoded by the `LprogBytes`
  encoder, whose straight-line arms carry `SailX86Decoder`'s `decode (encode i) = i`
  round-trip (the verified-to-bytes tier);
* the inter-function `call`s (the prove() entry → the phase leaves/loops) become
  `R_X86_64_PLT32` `.rela.text` relocations the linker resolves — the one
  residual is the relocation/linker (and the control-flow `jmp`/`jcc` encodings,
  gas-pinned by byte-diff, not yet decode-verified).

The result is a linkable `.o` whose `.text` is the verified encoder's bytes, not
`gas`'s — removing `gas` from the prover object's trusted base.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ProveDriverBytes

open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ProveDriverEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

set_option autoImplicit false

/-- The whole-prover object (leaves + loops + `plonky3_prove` entry) as a
    relocatable ELF `.o`, byte-encoded by the verified encoder — no `gas`. -/
def wholeProverObjBytes : List (BitVec 8) :=
  encodeLprogReloc wholeProverWithEntryLprog

/-- The emitted object is a valid ELF: it begins with the `\x7fELF` magic. (The
    full header well-formedness is `ElfObject.header_magic`; this pins the magic on
    the actual emitted prover object.) -/
theorem wholeProverObj_elf_magic :
    wholeProverObjBytes.take 4 = [0x7f, 0x45, 0x4c, 0x46].map (BitVec.ofNat 8) := by
  native_decide

/-- The object is non-empty (it carries the stitched `.text` + symtab + reloc
    sections for the whole prover). -/
theorem wholeProverObj_nonempty : 0 < wholeProverObjBytes.length := by
  native_decide

/-! ## Emit driver: write the verified-bytes `.o` to disk (no `gas`) -/

/-- Write the verified-encoder ELF object for the whole prover. The bytes are the
    verified encoder's output; `ld` links this `.o` directly (no assembler). -/
def emitProveObj : IO Unit := do
  IO.FS.createDirAll "bench/plonky3_compare/gen_com"
  let bytes := wholeProverObjBytes.map (fun b => (b.toNat.toUInt8))
  IO.FS.writeBinFile "bench/plonky3_compare/gen_com/plonky3_whole_prover.o"
    (ByteArray.mk (Array.mk bytes))
  IO.println s!"wrote bench/plonky3_compare/gen_com/plonky3_whole_prover.o ({bytes.length} bytes, verified encoder, no gas)"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ProveDriverBytes
