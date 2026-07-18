/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmAbiEncoder

/-!
# A verified AArch64 ELF64 relocatable-object stitcher (the ARM `gas -o foo.o` analogue)

This is the **AArch64 analogue of `X86Backend/ElfObject.lean`**: it wraps the
verified-encoder `.text` bytes of one or more leaves into a genuine ELF64
relocatable object (`ELFCLASS64`, `ET_REL`, `EM_AARCH64`), so the owned ARM
backend produces a real `.o` directly — with neither `as`/gas nor `clang` on the
object-build path. A list of `(name, textBytes)` leaves concatenate into one
`.text` section, each leaf getting its own `STT_FUNC` global symbol whose
`st_value` is its byte offset within `.text` and whose `st_size` is its byte
length. A whole AArch64 function (prologue + verified body + epilogue, optionally
plus an in-`.text` `_start` driver) thus stitches into ONE verified-bytes-direct
relocatable object.

The container layout is the standard System-V relocatable form, byte-identical in
*structure* to the x86 stitcher; only `e_machine` (`EM_AARCH64 = 183`) and the
relocation type vocabulary (`R_AARCH64_CALL26 = 283` for `BL`) are AArch64-specific:

```
[ Elf64_Ehdr (64B)
| .text          = text₀ ++ text₁ ++ … (pad8)
| .rela.text     = one Elf64_Rela per relocation (pad8)
| .shstrtab      (pad8)
| .strtab        = NUL ++ name₀\0 ++ … (pad8)
| .symtab        = nullSym ++ funcSym₀ ++ … ++ externSym₀ ++ …
| Elf64_Shdr × 7 ]
```

The encoder side is proved correct by `SailArmDecoder` (decode∘encode = id for the
GP-ALU / bignum subset); this module proves the *container* well-formedness — the
unconditional half of the trust story — exactly mirroring the x86 stitcher's
`symValue_*` / `textBytes_length` / `symCount_eq` / header lemmas.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmElfObject

open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder

/-! ## 0. Self-contained little-endian byte helpers

These do not depend on the x86 backend (zone isolation); they are the same
field-width LE splitters the ELF records need. -/

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

/-! ## 1. The AArch64 ELF64 header -/

/-- The 64-byte `Elf64_Ehdr` for a relocatable AArch64 object, parameterised by
    the section-header table offset `shoff`, the section count `shnum`, and the
    section-string-table section index `shstrndx`. `e_machine = EM_AARCH64 = 183`. -/
def elf64Header (shoff shnum shstrndx : Nat) : List (BitVec 8) :=
  ([0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0].map (BitVec.ofNat 8))
    ++ u16LE 1                 -- e_type = ET_REL
    ++ u16LE 183               -- e_machine = EM_AARCH64
    ++ u32LE 1                 -- e_version = EV_CURRENT
    ++ u64LE 0                 -- e_entry
    ++ u64LE 0                 -- e_phoff
    ++ u64LE shoff             -- e_shoff
    ++ u32LE 0                 -- e_flags
    ++ u16LE 64                -- e_ehsize
    ++ u16LE 0                 -- e_phentsize
    ++ u16LE 0                 -- e_phnum
    ++ u16LE 64                -- e_shentsize
    ++ u16LE shnum             -- e_shnum
    ++ u16LE shstrndx          -- e_shstrndx

/-! ## 2. ELF64 record builders -/

/-- A 64-byte `Elf64_Shdr` section header. -/
def elf64Shdr (name typ flags addr off size link info align entsize : Nat) :
    List (BitVec 8) :=
  u32LE name ++ u32LE typ ++ u64LE flags ++ u64LE addr ++ u64LE off
    ++ u64LE size ++ u32LE link ++ u32LE info ++ u64LE align ++ u64LE entsize

/-- A 24-byte `Elf64_Sym` symbol-table entry. -/
def elf64Sym (name info other shndx value size : Nat) : List (BitVec 8) :=
  u32LE name ++ [BitVec.ofNat 8 info, BitVec.ofNat 8 other] ++ u16LE shndx
    ++ u64LE value ++ u64LE size

/-- A 24-byte `Elf64_Rela` relocation entry. `r_info = (sym << 32) | type`. For
    AArch64 `BL`/`B` the addend is `0` (the `imm26` is relative to the branch PC
    itself, no `−4` field-end compensation as in x86 `rel32`). -/
def elf64Rela (offset symIdx typ : Nat) (addend : Int) : List (BitVec 8) :=
  u64LE offset ++ u64LE (symIdx * 0x100000000 + typ) ++ u64LE (BitVec.ofInt 64 addend).toNat

/-- `R_AARCH64_CALL26` (type 283): the 26-bit PC-relative branch-and-link reloc
    (the `BL` form; the linker resolves it to a direct displacement when the target
    is local to the link). -/
def R_AARCH64_CALL26 : Nat := 283
/-- `R_AARCH64_JUMP26` (type 282): the 26-bit PC-relative unconditional-branch reloc. -/
def R_AARCH64_JUMP26 : Nat := 282

/-- Pad a byte list up to an 8-byte boundary. -/
def padTo8 (bs : List (BitVec 8)) : List (BitVec 8) :=
  bs ++ List.replicate ((8 - bs.length % 8) % 8) (BitVec.ofNat 8 0)

/-- A name as bytes followed by a NUL terminator. -/
def cstrBytes (s : String) : List (BitVec 8) :=
  s.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat) ++ [BitVec.ofNat 8 0]

/-! ## 3. The multi-symbol leaf table -/

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

/-! ## 4. String + symbol tables -/

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

/-! ## 5. External (undefined) symbols + `.rela.text` relocations -/

/-- One `.rela.text` relocation: the `.text` byte offset of the branch word, the
    name of the (external, undefined) target symbol, the relocation type, and the
    signed addend (`0` for the AArch64 PC-relative branch forms). -/
structure Reloc where
  /-- Byte offset of the 4-byte branch word within `.text`. -/
  offset : Nat
  /-- The undefined target symbol's name (must appear in `externs`). -/
  symName : String
  /-- The relocation type (`R_AARCH64_CALL26 = 283` for `BL`). -/
  typ : Nat := R_AARCH64_CALL26
  /-- The signed addend (`0` for the AArch64 branch forms). -/
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

/-! ## 6. The multi-symbol object -/

/-- Build a complete AArch64 ELF64 relocatable object holding ALL `leaves` as
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

/-- The no-relocation specialisation. -/
def buildElfObjectMulti (leaves : List Leaf) : List (BitVec 8) :=
  buildElfObjectMultiReloc leaves [] []

/-- The single-leaf object. -/
def buildElfObject (name : String) (text : List (BitVec 8)) : List (BitVec 8) :=
  buildElfObjectMulti [⟨name, text⟩]

/-! ## 7. Symbol-table well-formedness (the unconditional trust-boundary half) -/

@[simp] theorem textBytes_length (leaves : List Leaf) :
    (textBytes leaves).length = (leafLens leaves).sum := by
  simp [textBytes, leafLens, List.length_flatten, List.map_map, Function.comp_def]

@[simp] theorem leafLens_length (leaves : List Leaf) :
    (leafLens leaves).length = leaves.length := by simp [leafLens]

theorem symValue_zero (leaves : List Leaf) : symValue leaves 0 = 0 := by
  simp [symValue]

/-- Core list helper: the prefix sum of the first `k+1` elements is the prefix sum
    of the first `k` plus the `k`-th element (no Mathlib `sum_take_succ`). -/
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

/-- Core list helper: the sum of a prefix is `≤` the sum of a longer prefix. -/
theorem sum_take_mono_core (xs : List Nat) {j k : Nat} (h : j ≤ k) :
    (xs.take j).sum ≤ (xs.take k).sum := by
  induction xs generalizing j k with
  | nil => simp
  | cons a as ih =>
    cases j with
    | zero => simp
    | succ j' =>
      cases k with
      | zero => omega
      | succ k' =>
        simp only [List.take_succ_cons, List.sum_cons]
        exact Nat.add_le_add_left (ih (Nat.le_of_succ_le_succ h)) a

theorem symValue_succ (leaves : List Leaf) (k : Nat) (hk : k < leaves.length) :
    symValue leaves (k + 1) = symValue leaves k + (leaves[k]).text.length := by
  have hk' : k < (leafLens leaves).length := by simpa using hk
  simp only [symValue]
  rw [sum_take_succ_core _ k hk']
  simp [leafLens, List.getElem_map]

theorem symValue_mono (leaves : List Leaf) {j k : Nat} (h : j ≤ k) :
    symValue leaves j ≤ symValue leaves k := by
  simp only [symValue]
  exact sum_take_mono_core (leafLens leaves) h

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

/-- The `e_machine` field (bytes 18–19) is `EM_AARCH64 = 183 = 0x00b7` little-endian
    `b7 00` — the field that distinguishes this object from the x86 stitcher. -/
theorem elf64Header_machine (shoff shnum shstrndx : Nat) :
    ((elf64Header shoff shnum shstrndx).drop 18).take 2
      = [0xb7, 0x00].map (BitVec.ofNat 8) := by
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

theorem relaTextBytes_length (leaves : List Leaf) (externs : List String)
    (relocs : List Reloc) :
    (relaTextBytes leaves externs relocs).length = 24 * relocs.length := by
  have hconst : ∀ xs ∈ (relocs.map (fun r =>
      elf64Rela r.offset (externSymIdx leaves externs r.symName) r.typ r.addend)),
      xs.length = 24 := by
    intro xs hxs
    rw [List.mem_map] at hxs
    obtain ⟨r, _, rfl⟩ := hxs
    exact elf64Rela_length _ _ _ _
  rw [relaTextBytes, flatten_length_const _ 24 hconst, List.length_map]

theorem symtabBytes_length (leaves : List Leaf) :
    (symtabBytes leaves).length = 24 * (1 + leaves.length) := by
  simp only [symtabBytes, List.length_append, elf64Sym_length, funcSyms_length]
  omega

theorem symCount_eq (leaves : List Leaf) :
    (symtabBytes leaves).length / 24 = 1 + leaves.length := by
  rw [symtabBytes_length]; omega

/-! ## 8. Worked witnesses (the multi-symbol offset + reloc checks) -/

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

/-- A `BL` to an external `bignum_add_p256_a64` at `.text` offset 4: the reloc is
    `(offset=4, name, CALL26, 0)`, the extern's symtab index is `1+1+0=2`. -/
def demoRela : List Reloc := [{ offset := 4, symName := "bignum_add_p256_a64" }]

example : (relaTextBytes [⟨"_start", []⟩] ["bignum_add_p256_a64"] demoRela).length = 24 := by
  rw [relaTextBytes_length]; rfl
example : externSymIdx [⟨"_start", []⟩] ["bignum_add_p256_a64"] "bignum_add_p256_a64" = 2 := by
  simp [externSymIdx]

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmElfObject
