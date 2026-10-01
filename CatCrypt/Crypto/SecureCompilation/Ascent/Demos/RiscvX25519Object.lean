/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Proof
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderObject

/-!
# The RV64 X25519 function as an ELF object

`x25519Object` wraps the encoded bytes of `RiscvX25519Proof.x25519Prog` into an ELF64
relocatable object with `RiscvElfObject.buildElfObjectMulti`: one `.text` section holding the
ladder program, the X25519 block function and the C function, with the global function
symbols `catcrypt_x25519_ladder` at offset 0, `catcrypt_x25519_block` at offset 12392
(instruction 3098) and `catcrypt_x25519` at offset 16852 (instruction 4213), and no
relocations. The C entry point is `void catcrypt_x25519(uint8_t out[32], const uint8_t
scalar[32], const uint8_t u[32])`; the other two symbols are internal entry points with their
own register conventions. `lake exe riscv-x25519-emit` writes the object to
`bench/riscv_x25519/gen/x25519.o`, and `bench/riscv_x25519/run.sh` links it into a C driver
and compares its output bytes with RFC 7748 under qemu.

## Main results

* `buildElfObjectMulti_text`: the `.text` of an object is the bytes of its leaves, from
  offset 64.
* `x25519Object_correct`: the `.text` of `x25519Object` decodes to a program whose function
  at offset 16852 maps the 32 bytes at `scalar` and at `u` to `x25519Bytes` of them at `out`.

## Scope

`x25519Object_correct` is a statement about the bytes of `x25519Object` from offset 64, of
the length of the encoded program: it does not parse the ELF header, the section table or the
symbol table (`x25519CSym_offset` computes the symbol value from the leaves), and nothing is
proved about the linker. That the linker places `.text` at a word-aligned address and that a
C caller meets `X25519CPre` (a 16-byte aligned `sp` and 8-byte aligned buffers) are read off
the object and the driver, not proved. No constant-time or leakage theorem is proved.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Object

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvElfObject
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderBytesProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderObject (ladderSym)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Proof
open CatCrypt.Util (x25519Bytes)

/-- The `.text` of an object is the bytes of its leaves, from offset 64. -/
theorem buildElfObjectMulti_text (leaves : List Leaf) :
    ((buildElfObjectMulti leaves).drop 64).take (textBytes leaves).length = textBytes leaves := by
  simp only [buildElfObjectMulti, buildElfObjectMultiReloc, List.append_assoc]
  rw [List.drop_append_of_le_length (by simp [elf64Header_length]),
    List.drop_eq_nil_of_le (by simp [elf64Header_length]), List.nil_append]
  simp only [padTo8, List.append_assoc]
  exact List.take_left' rfl

/-- The symbol of the X25519 block function. -/
def x25519BlockSym : String := "catcrypt_x25519_block"

/-- The symbol of the C function. -/
def x25519CSym : String := "catcrypt_x25519"

/-- The three leaves: the ladder program, the X25519 block function, the C function. -/
def x25519Leaves : List Leaf :=
  [⟨ladderSym, encodePBlock64 ladderProg⟩, ⟨x25519BlockSym, encodePBlock64 (x25519Code 3098)⟩,
    ⟨x25519CSym, encodePBlock64 (wrapCode 3098 4213)⟩]

/-- The ELF64 relocatable object holding the X25519 program. -/
def x25519Object : List (BitVec 8) := buildElfObjectMulti x25519Leaves

theorem x25519Leaves_text : textBytes x25519Leaves = encodePBlock64 x25519Prog := by
  simp [textBytes, x25519Leaves, x25519Prog, encodePBlock64, List.flatMap_append]

theorem x25519BlockSym_offset : symValue x25519Leaves 1 = 4 * 3098 := by
  simp only [symValue, leafLens, x25519Leaves, List.map_cons, List.map_nil, List.take_succ_cons,
    List.take_zero, List.sum_cons, List.sum_nil, Nat.add_zero]
  decide +kernel

theorem x25519CSym_offset : symValue x25519Leaves 2 = 4 * 4213 := by
  simp only [symValue, leafLens, x25519Leaves, List.map_cons, List.map_nil, List.take_succ_cons,
    List.take_zero, List.sum_cons, List.sum_nil, Nat.add_zero]
  decide +kernel

theorem x25519Prog_bytes_length : (encodePBlock64 x25519Prog).length = 16984 := by
  rw [← x25519Leaves_text, textBytes_length]
  simp only [leafLens, x25519Leaves, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  decide +kernel

/-- **The X25519 object.** The 16984 bytes of `.text` in `x25519Object`, from offset 64,
    decode as 4246 instructions `prog` such that, loaded at any word-aligned `base`, the
    function at `base + 16852` (the symbol `catcrypt_x25519`, `x25519CSym_offset`) meets
    `FnSpec` with `X25519CPre`: it returns to `ra` with the 32 bytes at `out` (`a0`) equal to
    `x25519Bytes` of the 32 bytes at `scalar` (`a1`) and at `u` (`a2`), and `X25519CPost`. -/
theorem x25519Object_correct :
    ∃ prog, decodePStream64 4246 ((x25519Object.drop 64).take 16984) = some prog ∧
      ∀ base : BitVec 64, base &&& 3 = 0 →
        FnSpec prog base (addrOf base 4213) X25519CPre fun st st' =>
          bytesAt st'.mem (st.regs.get "a0") 32
              = x25519Bytes (bytesAt st.mem (st.regs.get "a1") 32)
                  (bytesAt st.mem (st.regs.get "a2") 32) ∧
            X25519CPost st st' := by
  rw [← x25519Prog_bytes_length, ← x25519Leaves_text, x25519Object,
    buildElfObjectMulti_text, x25519Leaves_text]
  exact x25519CBytes_correct

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Object.x25519Object_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x25519Object_correct

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Object
