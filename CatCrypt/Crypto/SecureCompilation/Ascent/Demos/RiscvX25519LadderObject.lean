/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderBytesProof
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvElfObject

/-!
# The RV64 Curve25519 ladder as an ELF object

`ladderObject` wraps the encoded bytes of `RiscvX25519LadderBytesProof.ladderProg` into an
ELF64 relocatable object with `RiscvElfObject.buildElfObject`: one `.text` section, one
global function symbol `catcrypt_x25519_ladder` at offset 0, and no relocations, since every
jump in the program is relative to the program counter. `lake exe riscv-x25519-emit` writes
it to `bench/riscv_x25519/gen/x25519_ladder.o`, and `bench/riscv_x25519/run.sh` links it into
a C driver and checks the RFC 7748 vectors under qemu.

## Main results

* `buildElfObject_text`: the `.text` of a single-leaf object is its bytes, from offset 64.
* `x25519LadderObject_correct`: the `.text` of `ladderObject` decodes to a program whose
  function meets `FnSpec` with `LadderPre` and `LadderPost`.

## Scope

`x25519LadderObject_correct` is a statement about the bytes of `ladderObject` from offset 64,
of the length of the encoded program: it does not parse the ELF header, the section table
or the symbol table, and nothing is proved about the linker. That the linker places
`.text` at a word-aligned address (its `sh_addralign` is 16) and that a C caller meets
`LadderPre` are read off the object and the driver, not proved. No constant-time or
leakage theorem is proved for the ladder program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderObject

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvElfObject
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderLoopProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderBytesProof

/-- The `.text` of a single-leaf object is its bytes, from offset 64. -/
theorem buildElfObject_text (name : String) (text : List (BitVec 8)) :
    ((buildElfObject name text).drop 64).take text.length = text := by
  simp only [buildElfObject, buildElfObjectMulti, buildElfObjectMultiReloc, textBytes,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    padTo8, List.append_assoc]
  rw [List.drop_append_of_le_length (by simp [elf64Header_length]),
    List.drop_eq_nil_of_le (by simp [elf64Header_length]), List.nil_append]
  simp

/-- The symbol of the ladder function. -/
def ladderSym : String := "catcrypt_x25519_ladder"

/-- The ELF64 relocatable object holding the ladder program as one function. -/
def ladderObject : List (BitVec 8) := buildElfObject ladderSym (encodePBlock64 ladderProg)

theorem ladderObject_text :
    ((ladderObject.drop 64).take (encodePBlock64 ladderProg).length) = encodePBlock64 ladderProg :=
  buildElfObject_text _ _

theorem ladderProg_bytes_length : (encodePBlock64 ladderProg).length = 12392 := by
  decide +kernel

/-- **The X25519 ladder object.** The 12392 bytes of `.text` in `ladderObject`, from offset
    64, decode as 3098 instructions `prog` such that, loaded at any word-aligned `base`, the
    function at `base` (the symbol `catcrypt_x25519_ladder`, at offset 0) meets `FnSpec`
    with `LadderPre` and `LadderPost`. -/
theorem x25519LadderObject_correct :
    ∃ prog, decodePStream64 3098 ((ladderObject.drop 64).take 12392) = some prog ∧
      ∀ base : BitVec 64, base &&& 3 = 0 → FnSpec prog base base LadderPre LadderPost := by
  rw [← ladderProg_bytes_length, ladderObject_text]
  exact x25519LadderBytes_correct

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderObject.x25519LadderObject_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x25519LadderObject_correct

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderObject
