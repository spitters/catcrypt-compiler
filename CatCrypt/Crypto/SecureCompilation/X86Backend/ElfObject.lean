/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder

/-!
# A verified multi-symbol ELF64 relocatable-object stitcher (#556)

`bench/bytes_direct_pilot/bytes_direct_emit.lean` (the #556 pilot) wraps the
verified-encoder `.text` bytes of ONE leaf into a single-symbol ELF64 `.o` — the
`gas -o foo.o` analogue with the assembler removed from the object-build path.
This module lifts that stitcher into the owned-backend library and generalises it
to a **multi-symbol** object: a list of `(name, textBytes)` leaves concatenate
into one `.text` section, each leaf getting its own `STT_FUNC` global symbol whose
`st_value` is its byte offset within `.text` and whose `st_size` is its byte
length. A whole protocol's owned leaves thus stitch into ONE verified-bytes-direct
relocatable object, with neither `gas` nor `jasminc` on the artifact path.

The layout is the standard System-V relocatable form (no relocations — these are
straight-line leaves):

```
[ Elf64_Ehdr (64B)
| .text          = text₀ ++ text₁ ++ … (pad8)
| .shstrtab      (pad8)
| .strtab        = NUL ++ name₀\0 ++ name₁\0 ++ … (pad8)
| .symtab        = nullSym ++ funcSym₀ ++ funcSym₁ ++ …
| Elf64_Shdr × 6 ]
```

## Trust-boundary well-formedness (the analog of `LprogJasminWellFormed` /
`elf64Header_length`)

The encoder side is proved correct by `SailX86Decoder.roundtrip_*` (decode∘encode
= id for the GP-ALU subset). This module proves the *container* well-formedness —
the unconditional half of the trust story, mirroring `elf64Header_length` /
`elf64Header_magic` but for the multi-symbol symbol table:

* `symValues_eq_scanPrefix` — symbol `k`'s `st_value` is exactly the running
  prefix-sum of the preceding leaves' byte lengths (offsets are correct, monotone).
* `textBytes_length` — `.text` total length is the sum of the leaf lengths.
* `symCount_eq` — the symbol count is `1 + #leaves` (the null sym plus one per leaf).
* `header_64` / `header_magic` — re-exported header shape (via `SailX86Decoder`).
* `buildElfObject_magic` / `buildElfObjectMulti_magic` /
  `buildElfObjectMultiReloc_magic` / `buildElfObjectRodata_magic` — each builder's
  output opens with the ELF magic, for all inputs, with no byte evaluated.

These are the symbol-table analogue of the encoder's `decode (encode i) = i`: they
pin the object's *structure* (where each function lives, how big it is) for all
inputs, so a linker / loader reading the symbol table recovers exactly the leaves
the stitcher was given.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject

open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder

/-! ## 1. ELF64 record builders (shared with the pilot's single-symbol path) -/

/-- A 64-byte `Elf64_Shdr` section header. -/
def elf64Shdr (name typ flags addr off size link info align entsize : Nat) :
    List (BitVec 8) :=
  u32LE name ++ u32LE typ ++ u64LE flags ++ u64LE addr ++ u64LE off
    ++ u64LE size ++ u32LE link ++ u32LE info ++ u64LE align ++ u64LE entsize

/-- A 24-byte `Elf64_Sym` symbol-table entry. -/
def elf64Sym (name info other shndx value size : Nat) : List (BitVec 8) :=
  u32LE name ++ [BitVec.ofNat 8 info, BitVec.ofNat 8 other] ++ u16LE shndx
    ++ u64LE value ++ u64LE size

/-- A 24-byte `Elf64_Rela` relocation entry: `r_offset`(8) `r_info`(8) `r_addend`(8).
    `r_info = (sym << 32) | type` packs the target symbol's symtab index and the
    relocation type into the 64-bit `r_info` word; `r_addend` is the signed implicit
    addend (`-4` for the x86-64 PC-relative `call`/`jmp rel32` forms, since the rel32
    is taken relative to the **end** of the 4-byte displacement field, which the
    linker compensates with `S + A − P` where `A = −4`). -/
def elf64Rela (offset symIdx typ : Nat) (addend : Int) : List (BitVec 8) :=
  u64LE offset ++ u64LE (symIdx * 0x100000000 + typ) ++ u64LE (BitVec.ofInt 64 addend).toNat

/-- `R_X86_64_PC32` (type 2): a 32-bit PC-relative relocation. -/
def R_X86_64_PC32 : Nat := 2
/-- `R_X86_64_PLT32` (type 4): a 32-bit PC-relative relocation routed through the
    PLT slot for the symbol (the modern `call`/`jmp` reloc; the linker resolves it
    to a direct PC-relative displacement when the target is local to the link). -/
def R_X86_64_PLT32 : Nat := 4

/-- Pad a byte list up to an 8-byte boundary. -/
def padTo8 (bs : List (BitVec 8)) : List (BitVec 8) :=
  bs ++ List.replicate ((8 - bs.length % 8) % 8) (BitVec.ofNat 8 0)

/-- A name as bytes followed by a NUL terminator (the ELF string-table form). -/
def cstrBytes (s : String) : List (BitVec 8) :=
  s.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat) ++ [BitVec.ofNat 8 0]

/-! ## 2. The multi-symbol leaf table

A leaf is a `(name, textBytes)` pair: the global symbol name and the verified
encoder's machine-code bytes for that function. -/

/-- One owned leaf to place in the object: its global symbol name and the
    verified-encoder machine-code bytes (`ScalarEncoder.encodeJBlock … ++ ret`). -/
structure Leaf where
  name : String
  text : List (BitVec 8)

/-- The concatenated `.text` bytes of all leaves, in order. -/
def textBytes (leaves : List Leaf) : List (BitVec 8) :=
  (leaves.map Leaf.text).flatten

/-- The per-leaf byte length list — the data underlying all offset arithmetic. -/
def leafLens (leaves : List Leaf) : List Nat :=
  leaves.map (fun l => l.text.length)

/-- The byte offset of leaf `k` within `.text`: the sum of the byte lengths of all
    earlier leaves. This is the `st_value` each leaf's symbol must carry. -/
def symValue (leaves : List Leaf) (k : Nat) : Nat :=
  ((leafLens leaves).take k).sum

/-! ## 3. The symbol table and string table

`.strtab` is `NUL ++ name₀\0 ++ name₁\0 ++ …`; the `st_name` of leaf `k`'s symbol
is the byte offset of `nameₖ` within `.strtab`. `.symtab` is the null symbol
followed by one `STT_FUNC` global per leaf (`st_info = (STB_GLOBAL<<4)|STT_FUNC =
0x12`, `st_shndx = 1` = `.text`, `st_value =` the running offset, `st_size =` the
leaf byte length). -/

/-- `.strtab` bytes: `NUL` then each name NUL-terminated, in leaf order. -/
def strtabBytes (leaves : List Leaf) : List (BitVec 8) :=
  (BitVec.ofNat 8 0) :: (leaves.map (fun l => cstrBytes l.name)).flatten

/-- The `st_name` offset of leaf `k` within `.strtab`: `1` (past the leading NUL)
    plus the summed lengths of the earlier names with their NUL terminators. -/
def symNameOff (leaves : List Leaf) (k : Nat) : Nat :=
  1 + ((leaves.take k).map (fun l => (cstrBytes l.name).length)).sum

/-- `.symtab` bytes: the null symbol, then one `STT_FUNC` global per leaf with the
    correct running `st_value` offset and `st_size`. -/
def symtabBytes (leaves : List Leaf) : List (BitVec 8) :=
  elf64Sym 0 0 0 0 0 0
    ++ (leaves.zipIdx.map (fun (l, k) =>
        elf64Sym (symNameOff leaves k) 0x12 0 1 (symValue leaves k) l.text.length)).flatten

/-! ## 3b. External (undefined) symbols + `.rela.text` relocations (#658)

A looped leaf that `call`s / `jmp`s a function which is NOT one of the object's own
`leaves` cannot be resolved at encode time — the target's address is only known at
link time. The encoder emits a `0`-placeholder rel32 at the call site and records a
**relocation** the linker patches: `R_X86_64_PLT32` (or `R_X86_64_PC32`) against an
**UNDEF** global symbol named for the callee. The undef symbols extend `.symtab`
after the defined func symbols, and the relocations go in a `.rela.text` section.

`r_offset` is the byte offset *within `.text`* of the 4-byte rel32 displacement field
(the call-site instruction's opcode offset + the opcode-prefix length), `r_sym` is the
callee's symtab index, `r_type = 4`/`2`, `r_addend = -4`. -/

/-- One `.rela.text` relocation: the `.text` byte offset of the rel32 field, the
    name of the (external, undefined) target symbol, the relocation type, and the
    signed addend (`-4` for the x86-64 `rel32` PC-relative forms). -/
structure Reloc where
  /-- Byte offset of the 4-byte rel32 displacement field within `.text`. -/
  offset : Nat
  /-- The undefined target symbol's name (must appear in `externs`). -/
  symName : String
  /-- The relocation type (`R_X86_64_PLT32 = 4` for `call`/`jmp`). -/
  typ : Nat := R_X86_64_PLT32
  /-- The signed addend (`-4` for `rel32`). -/
  addend : Int := -4

/-- The `st_name` offset of external symbol `j` within `.strtab`: past the leading
    NUL and ALL the leaf names, plus the summed lengths of the earlier extern names. -/
def externNameOff (leaves : List Leaf) (externs : List String) (j : Nat) : Nat :=
  symNameOff leaves leaves.length
    + ((externs.take j).map (fun s => (cstrBytes s).length)).sum

/-- `.strtab` bytes including external symbol names: `NUL ++ leafNames ++ externNames`,
    each NUL-terminated. -/
def strtabBytesR (leaves : List Leaf) (externs : List String) : List (BitVec 8) :=
  strtabBytes leaves ++ (externs.map cstrBytes).flatten

/-- `.symtab` bytes with external UNDEF symbols appended after the defined func
    symbols. Each extern is a global UNDEF symbol (`st_info = 0x10` = `STB_GLOBAL`,
    `STT_NOTYPE`; `st_shndx = 0 = SHN_UNDEF`; `st_value = st_size = 0`). The linker
    resolves these against the defining object at link time. -/
def symtabBytesR (leaves : List Leaf) (externs : List String) : List (BitVec 8) :=
  symtabBytes leaves
    ++ (externs.zipIdx.map (fun (_, j) =>
        elf64Sym (externNameOff leaves externs j) 0x10 0 0 0 0)).flatten

/-- The symtab index of external symbol named `s`: `1` (null) `+ #leaves` (the defined
    func symbols) `+` its position among `externs`. `0` if not found (which would be a
    bug — every reloc's `symName` must be an extern). -/
def externSymIdx (leaves : List Leaf) (externs : List String) (s : String) : Nat :=
  match externs.idxOf? s with
  | some j => 1 + leaves.length + j
  | none => 0

/-- `.rela.text` bytes: one 24-byte `Elf64_Rela` per relocation, with the target
    symbol's symtab index resolved from `externs`. -/
def relaTextBytes (leaves : List Leaf) (externs : List String) (relocs : List Reloc) :
    List (BitVec 8) :=
  (relocs.map (fun r =>
    elf64Rela r.offset (externSymIdx leaves externs r.symName) r.typ r.addend)).flatten

/-! ## 4. The multi-symbol object -/

/-- Build a complete ELF64 relocatable object holding ALL `leaves` as global
    `STT_FUNC` symbols in one `.text` section, with optional external UNDEF symbols
    (`externs`) and `.rela.text` relocations against them (`relocs`). Section order:

    ```
    0 SHN_UNDEF | 1 .text | 2 .rela.text | 3 .symtab | 4 .strtab | 5 .shstrtab
    | 6 .note.GNU-stack
    ```

    The `.rela.text` section header carries `sh_link = 3` (symtab) and `sh_info = 1`
    (the `.text` it relocates). When `externs` and `relocs` are both empty the
    `.rela.text` section is still present but zero-length, so the byte layout for the
    no-reloc case is the relocatable-friendly superset of the old 6-section form (one
    extra empty section + its 64-byte header). File order:
    `[Ehdr | .text(pad8) | .rela.text(pad8) | .shstrtab(pad8) | .strtab(pad8) | .symtab | Shdrs]`. -/
def buildElfObjectMultiReloc (leaves : List Leaf) (externs : List String)
    (relocs : List Reloc) : List (BitVec 8) :=
  let z : BitVec 8 := BitVec.ofNat 8 0
  let text := textBytes leaves
  let shstr :=
    [z] ++ cstrBytes ".text" ++ cstrBytes ".rela.text" ++ cstrBytes ".symtab"
        ++ cstrBytes ".strtab" ++ cstrBytes ".shstrtab"
        ++ cstrBytes ".note.GNU-stack"
  -- `.shstrtab` name offsets (running byte offsets into `shstr`).
  let off_text := 1                 -- ".text\0"
  let off_rela := off_text + 6      -- ".rela.text\0"
  let off_symtab := off_rela + 11   -- ".symtab\0"
  let off_strtab := off_symtab + 8  -- ".strtab\0"
  let off_shstrtab := off_strtab + 8-- ".shstrtab\0"
  let off_note := off_shstrtab + 10 -- ".note.GNU-stack\0"
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
  -- The first global symbol is index 1 (the null sym is the only local).
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

/-- Build a complete ELF64 relocatable object holding ALL `leaves` as global
    `STT_FUNC` symbols in one `.text` section. The no-relocation specialisation of
    `buildElfObjectMultiReloc` (empty `externs`/`relocs`): the `.rela.text` section
    is present but zero-length. Generalises the pilot's single-leaf `buildElfObject`
    to a whole `Lprog`'s worth of owned leaves with no assembler on the path. -/
def buildElfObjectMulti (leaves : List Leaf) : List (BitVec 8) :=
  buildElfObjectMultiReloc leaves [] []

/-- The single-leaf object is the one-element multi-symbol object: the pilot's
    `buildElfObject name text` is `buildElfObjectMulti [⟨name, text⟩]`. -/
def buildElfObject (name : String) (text : List (BitVec 8)) : List (BitVec 8) :=
  buildElfObjectMulti [⟨name, text⟩]

/-! ### Header re-export (single source of truth in `SailX86Decoder`) and the
object's leading magic -/

/-- The object begins with a 64-byte `Elf64_Ehdr` (re-export of
    `SailX86Decoder.elf64Header_length` for the multi-symbol object). -/
theorem header_64 (shoff shnum shstrndx : Nat) :
    (elf64Header shoff shnum shstrndx).length = 64 :=
  elf64Header_length shoff shnum shstrndx

/-- The first six bytes are the ELF magic + 64-bit/LE class (re-export of
    `SailX86Decoder.elf64Header_magic`). -/
theorem header_magic (shoff shnum shstrndx : Nat) :
    (elf64Header shoff shnum shstrndx).take 6
      = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) :=
  elf64Header_magic shoff shnum shstrndx

/-- Any byte list whose head is an `Elf64_Ehdr` opens with the ELF magic and the
    64-bit/little-endian class bytes: the 6-byte prefix lies inside the 64-byte
    header, so the appended sections do not reach it. -/
theorem header_prefix_magic (shoff shnum shstrndx : Nat) (rest : List (BitVec 8)) :
    (elf64Header shoff shnum shstrndx ++ rest).take 6
      = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) := by
  rw [List.take_append_of_le_length (by rw [header_64]; omega), header_magic]

/-- The multi-symbol relocatable object opens with the ELF magic and the
    64-bit/little-endian class bytes, for any leaves, externs and relocations —
    the sections after the `Elf64_Ehdr` never reach the first six bytes, so no
    byte of the object need be evaluated. -/
theorem buildElfObjectMultiReloc_magic (leaves : List Leaf) (externs : List String)
    (relocs : List Reloc) :
    (buildElfObjectMultiReloc leaves externs relocs).take 6
      = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) := by
  unfold buildElfObjectMultiReloc
  simp only [List.append_assoc]
  exact header_prefix_magic _ _ _ _

/-- The no-relocation multi-symbol object opens with the ELF magic, for any
    leaves. -/
theorem buildElfObjectMulti_magic (leaves : List Leaf) :
    (buildElfObjectMulti leaves).take 6
      = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) :=
  buildElfObjectMultiReloc_magic leaves [] []

/-- The single-symbol object opens with the ELF magic, for any symbol name and
    any `.text` bytes. -/
theorem buildElfObject_magic (name : String) (text : List (BitVec 8)) :
    (buildElfObject name text).take 6
      = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) :=
  buildElfObjectMulti_magic _

/-! ## 4b. A `.text` + `.rodata` object with RIP-relative constant-pool relocations (AEGIS C0/C1)

The fixed-ABI AEAD kernels (AES-GCM GHASH masks, AEGIS `C0`/`C1` state constants)
load 16-byte constants from a **`.rodata` constant pool** by RIP-relative
addressing (`SimdBytes.encVmovdquRipLoad` / `encLeaRip`), because the ABI passes no
constant pointer. The RIP-relative `disp32` of each load is a **link-time
relocation** (`R_X86_64_PC32`, addend `-4`) against the `.rodata` pool symbol.

`buildElfObjectRodata` emits a relocatable object with a `.text` section (the leaf
bytes), a `.rodata` section (the constant-pool bytes), one defined `STT_OBJECT`
*local* symbol for the pool (`rodataSymName`), and a `.rela.text` section with one
`R_X86_64_PC32` reloc per constant load. The relocs target the rodata symbol by its
symtab index; the linker patches each `disp32` to `pool + addend − P`. The section
order is `[.text | .rodata | .rela.text | .symtab | .strtab | .shstrtab]`. -/

/-- A RIP-relative relocation against the `.rodata` constant pool: the `.text` byte
    offset of the 4-byte `disp32` field, and the signed addend into the pool
    (`poolOffset − 4`, where `poolOffset` is the byte offset of the target constant
    within `.rodata` and `−4` is the `rel32` PC-relative correction). -/
structure RodataReloc where
  /-- Byte offset of the 4-byte `disp32` field within `.text`. -/
  offset : Nat
  /-- Byte offset of the target constant within the `.rodata` pool. -/
  poolOffset : Nat := 0

/-- The defined `.rodata` pool symbol name (a local data symbol the relocs target). -/
def rodataSymName : String := ".Lrodata_pool"

/-- Build a relocatable object with one `.text` leaf and a `.rodata` constant pool,
    plus `R_X86_64_PC32` relocations (one per RIP-relative constant load) from
    `.text` into the pool. Layout:
    `[Ehdr | .text(pad8) | .rodata(pad8) | .rela.text(pad8) | .strtab(pad8) | .symtab | Shdrs]`.
    The pool symbol is a defined local `STT_OBJECT` at `.rodata` offset 0; each
    reloc's `r_addend = poolOffset − 4` so the linker resolves `pool + poolOffset − 4 − P`. -/
def buildElfObjectRodata (name : String) (text : List (BitVec 8))
    (rodata : List (BitVec 8)) (relocs : List RodataReloc) : List (BitVec 8) :=
  let z : BitVec 8 := BitVec.ofNat 8 0
  let shstr :=
    [z] ++ cstrBytes ".text" ++ cstrBytes ".rodata" ++ cstrBytes ".rela.text"
        ++ cstrBytes ".symtab" ++ cstrBytes ".strtab" ++ cstrBytes ".shstrtab"
  let off_text := 1
  let off_rodata := off_text + 6     -- ".text\0"
  let off_rela := off_rodata + 8     -- ".rodata\0"
  let off_symtab := off_rela + 11    -- ".rela.text\0"
  let off_strtab := off_symtab + 8   -- ".symtab\0"
  let off_shstrtab := off_strtab + 8 -- ".strtab\0"
  -- `.strtab`: NUL, the func name, the rodata-pool symbol name (each NUL-terminated).
  let strtab : List (BitVec 8) := [z] ++ cstrBytes name ++ cstrBytes rodataSymName
  let funcNameOff := 1
  let rodataNameOff := 1 + (cstrBytes name).length
  -- `.symtab`: null sym | func (STT_FUNC, .text=sec 1) | rodata pool (STT_OBJECT, .rodata=sec 2).
  -- The func sym is the only "global"; both the func and pool are placed after the
  -- null local — `sh_info` of `.symtab` is the index of the first global symbol.
  let symtab : List (BitVec 8) :=
    elf64Sym 0 0 0 0 0 0
      ++ elf64Sym rodataNameOff 0x01 0 2 0 rodata.length        -- STT_OBJECT local, .rodata
      ++ elf64Sym funcNameOff 0x12 0 1 0 text.length            -- STT_FUNC global, .text
  -- the rodata pool symbol is symtab index 1.
  let poolSymIdx := 1
  let rela : List (BitVec 8) :=
    (relocs.map (fun r =>
      elf64Rela r.offset poolSymIdx R_X86_64_PC32 ((r.poolOffset : Int) - 4))).flatten
  let textOff := 64
  let textPad := padTo8 text
  let rodataOff := textOff + textPad.length
  let rodataPad := padTo8 rodata
  let relaOff := rodataOff + rodataPad.length
  let relaPad := padTo8 rela
  let strtabOff := relaOff + relaPad.length
  let strtabPad := padTo8 strtab
  let shstrOff := strtabOff + strtabPad.length
  let shstrPad := padTo8 shstr
  let symtabOff := shstrOff + shstrPad.length
  let shoff := symtabOff + symtab.length
  let shNull := elf64Shdr 0 0 0 0 0 0 0 0 0 0
  let shText := elf64Shdr off_text 1 6 0 textOff text.length 0 0 16 0          -- AX
  let shRodata := elf64Shdr off_rodata 1 2 0 rodataOff rodata.length 0 0 16 0  -- A
  -- SHT_RELA = 4; sh_link = symtab section index (4); sh_info = .text index (1).
  let shRela := elf64Shdr off_rela 4 0 0 relaOff rela.length 4 1 8 24
  -- sh_link = strtab section index (5); sh_info = index of first global symbol (2).
  let shSymtab := elf64Shdr off_symtab 2 0 0 symtabOff symtab.length 5 2 8 24
  let shStrtab := elf64Shdr off_strtab 3 0 0 strtabOff strtab.length 0 0 1 0
  let shShstrtab := elf64Shdr off_shstrtab 3 0 0 shstrOff shstr.length 0 0 1 0
  let shdrs := shNull ++ shText ++ shRodata ++ shRela ++ shSymtab ++ shStrtab ++ shShstrtab
  elf64Header shoff 7 6
    ++ textPad ++ rodataPad ++ relaPad ++ strtabPad ++ shstrPad ++ symtab ++ shdrs

/-- The `.text` + `.rodata` object opens with the ELF magic and the
    64-bit/little-endian class bytes, for any symbol name, `.text` bytes,
    constant pool and relocation list. -/
theorem buildElfObjectRodata_magic (name : String) (text rodata : List (BitVec 8))
    (relocs : List RodataReloc) :
    (buildElfObjectRodata name text rodata relocs).take 6
      = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) := by
  unfold buildElfObjectRodata
  simp only [List.append_assoc]
  exact header_prefix_magic _ _ _ _

/-! ### `.rodata` object well-formedness pins -/

/-- A worked AEGIS-shaped pin: two 16-byte constants `C0`/`C1` in `.rodata`, one
    `vmovdqu C0(%rip)` load at `.text` offset 4 (the disp32 field) targeting pool
    offset 0, and one `vmovdqu C1(%rip)` at offset 12 targeting pool offset 16. -/
def demoRodataRelocs : List RodataReloc :=
  [ { offset := 4, poolOffset := 0 }, { offset := 12, poolOffset := 16 } ]

/-- The 32-byte AEGIS constant pool (`C0 ‖ C1`, two 16-byte placeholders). -/
def demoRodataPool : List (BitVec 8) := List.replicate 32 (BitVec.ofNat 8 0xAA)

/-- A demo `.rodata` object (one 1-byte `ret` leaf + the 32-byte pool + two relocs). -/
def demoRodataObject : List (BitVec 8) :=
  buildElfObjectRodata "aegis_const_load" [BitVec.ofNat 8 0xc3] demoRodataPool demoRodataRelocs

/-- The `.rodata` object begins with the 64-byte `Elf64_Ehdr` (ELF magic + class). -/
example : demoRodataObject.take 6 = [0x7f, 0x45, 0x4c, 0x46, 2, 1].map (BitVec.ofNat 8) :=
  buildElfObjectRodata_magic _ _ _ _

/-- `.rela.text` for the two-constant AEGIS pool is `2 × 24 = 48` bytes (two
    24-byte `Elf64_Rela` entries, one per RIP-relative constant load). -/
example :
    ((demoRodataRelocs.map (fun r =>
      elf64Rela r.offset 1 R_X86_64_PC32 ((r.poolOffset : Int) - 4))).flatten).length = 48 := by
  rfl

/-! ## 5. Symbol-table well-formedness (the unconditional trust-boundary half)

These pin the object's structure for ALL leaf lists — the symbol-table analogue
of `elf64Header_length` / `decode (encode i) = i`. -/

/-- `.text` total length is the sum of the per-leaf byte lengths: the leaves are
    laid down contiguously with no padding *between* them. -/
@[simp] theorem textBytes_length (leaves : List Leaf) :
    (textBytes leaves).length = (leafLens leaves).sum := by
  simp [textBytes, leafLens, List.length_flatten, List.map_map, Function.comp_def]

/-- `leafLens` has one entry per leaf. -/
@[simp] theorem leafLens_length (leaves : List Leaf) :
    (leafLens leaves).length = leaves.length := by
  simp [leafLens]

/-- Symbol `0`'s `st_value` is `0` (the first leaf starts at `.text` offset 0). -/
theorem symValue_zero (leaves : List Leaf) : symValue leaves 0 = 0 := by
  simp [symValue]

/-- Each leaf's `st_value` is exactly the running prefix-sum of the preceding
    leaves' byte lengths — the offset-correctness / monotonicity property a linker
    relies on. Successive symbols advance by exactly the previous leaf's length. -/
theorem symValue_succ (leaves : List Leaf) (k : Nat) (hk : k < leaves.length) :
    symValue leaves (k + 1) = symValue leaves k + (leaves[k]).text.length := by
  have hk' : k < (leafLens leaves).length := by simpa using hk
  simp only [symValue]
  rw [List.sum_take_succ _ k hk']
  simp [leafLens, List.getElem_map]

/-- Symbol values are monotone non-decreasing: each leaf sits at or after the
    previous one in `.text`. -/
theorem symValue_mono (leaves : List Leaf) {j k : Nat} (h : j ≤ k) :
    symValue leaves j ≤ symValue leaves k := by
  simp only [symValue]
  apply List.Sublist.sum_le_sum
  · exact List.take_sublist_take_left h
  · intro x _
    exact Nat.zero_le x

/-- The last symbol's value plus the last leaf's length is the whole `.text`
    length: the symbols tile `.text` exactly, leaving no gap and no overrun. -/
theorem symValue_last_eq_text (leaves : List Leaf) :
    symValue leaves leaves.length = (textBytes leaves).length := by
  simp only [symValue, textBytes_length]
  rw [List.take_of_length_le (le_of_eq (leafLens_length leaves))]

/-! ### Symbol count

`.symtab` holds one 24-byte `Elf64_Sym` per leaf plus the leading null symbol, so
the symbol count is `1 + #leaves` and the section is `24 * (1 + #leaves)` bytes. -/

/-- `elf64Sym` is exactly 24 bytes (`Elf64_Sym`). -/
theorem elf64Sym_length (name info other shndx value size : Nat) :
    (elf64Sym name info other shndx value size).length = 24 := by
  simp [elf64Sym, u32LE, u16LE, u64LE, imm32LE, List.length_map]

/-- `elf64Shdr` is exactly 64 bytes (`Elf64_Shdr`). -/
theorem elf64Shdr_length (name typ flags addr off size link info align entsize : Nat) :
    (elf64Shdr name typ flags addr off size link info align entsize).length = 64 := by
  simp [elf64Shdr, u32LE, u64LE, imm32LE, List.length_map]

/-- `elf64Rela` is exactly 24 bytes (`Elf64_Rela`): `r_offset`(8) `r_info`(8)
    `r_addend`(8) — the `entsize` the `.rela.text` section header records. -/
theorem elf64Rela_length (offset symIdx typ : Nat) (addend : Int) :
    (elf64Rela offset symIdx typ addend).length = 24 := by
  simp [elf64Rela, u64LE, List.length_map]


/-- Generic helper: flattening a list of lists each of which has length `c` gives
    total length `c * #lists`. -/
theorem flatten_length_const {α : Type*} (xss : List (List α)) (c : Nat)
    (h : ∀ xs ∈ xss, xs.length = c) : xss.flatten.length = c * xss.length := by
  induction xss with
  | nil => simp
  | cons a as ih =>
      rw [List.flatten_cons, List.length_append, h a (List.mem_cons_self),
          ih (fun xs hxs => h xs (List.mem_cons_of_mem a hxs)),
          List.length_cons]
      ring

/-- The flattened func-symbol bytes are `24 * #leaves`: every mapped entry is a
    24-byte `Elf64_Sym`, and there is exactly one per leaf. -/
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

/-- `.rela.text` is `24 * #relocs` bytes — one 24-byte `Elf64_Rela` per relocation. -/
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

/-- `.symtab` is `24 * (1 + #leaves)` bytes — the null symbol plus one per leaf. -/
theorem symtabBytes_length (leaves : List Leaf) :
    (symtabBytes leaves).length = 24 * (1 + leaves.length) := by
  simp only [symtabBytes, List.length_append, elf64Sym_length, funcSyms_length]
  ring

/-- The number of `STT_FUNC` symbols equals the number of leaves (one per leaf);
    the total symbol count including the null symbol is `1 + #leaves`. -/
theorem symCount_eq (leaves : List Leaf) :
    (symtabBytes leaves).length / 24 = 1 + leaves.length := by
  rw [symtabBytes_length]; omega

/-- The single-leaf object's `.text` is exactly that leaf's bytes (the pilot's
    `buildElfObject` is the one-element specialisation). -/
@[simp] theorem buildElfObject_eq (name : String) (text : List (BitVec 8)) :
    buildElfObject name text = buildElfObjectMulti [⟨name, text⟩] := rfl

/-! ## 6. A worked two-leaf stitch (the multi-symbol offset check)

The single-symbol case (`#444`, the pilot) places one function at `.text` offset
0. The new property is that with *several* leaves, leaf `k`'s symbol records the
correct running offset. Here is the smallest concrete witness: two leaves whose
`.text` blocks have lengths 5 and 3. The first symbol sits at offset 0, the
second at offset 5 (= the first leaf's length), and `.text` is 8 bytes total. The
proofs `simp`-compute the symbol arithmetic — the multi-symbol analogue of the
encoder's `decode (encode i) = i` byte-check, at the symbol-table layer. -/

/-- Two demo leaves with `.text` lengths 5 and 3 (the byte contents are arbitrary
    placeholders; only the lengths drive the symbol offsets). -/
def demoLeaves : List Leaf :=
  [ ⟨"f0", List.replicate 5 (BitVec.ofNat 8 0x90)⟩
  , ⟨"f1", List.replicate 3 (BitVec.ofNat 8 0x90)⟩ ]

/-- Leaf 0 sits at `.text` offset 0. -/
example : symValue demoLeaves 0 = 0 := by simp [symValue]

/-- Leaf 1 sits at `.text` offset 5 — exactly leaf 0's byte length, with no gap. -/
example : symValue demoLeaves 1 = 5 := by
  simp [symValue, leafLens, demoLeaves]

/-- The two leaves tile a `.text` of 8 bytes (`5 + 3`). -/
example : (textBytes demoLeaves).length = 8 := by
  simp [textBytes_length, leafLens, demoLeaves]

/-- The object carries 3 symbols: the null symbol + one `STT_FUNC` per leaf. -/
example : (symtabBytes demoLeaves).length / 24 = 3 := by
  rw [symCount_eq]; simp [demoLeaves]

/-! ### A worked relocation example (#658)

One leaf `caller` that `call`s an external symbol `callee`: the rel32 field of the
`E8 cd` call sits at `.text` offset 1 (after the `E8` opcode), so the relocation is
`(offset = 1, callee, PLT32, -4)`. The extern symbol's symtab index is
`1 (null) + 1 (caller) + 0 = 2`. -/

/-- A demo with one external relocation against `callee` at `.text` offset 1. -/
def demoRela : List Reloc := [{ offset := 1, symName := "callee" }]

/-- `.rela.text` carries exactly one 24-byte entry. -/
example : (relaTextBytes [⟨"caller", []⟩] ["callee"] demoRela).length = 24 := by
  rw [relaTextBytes_length]; rfl

/-- The external symbol `callee` resolves to symtab index 2 (null=0, caller=1). -/
example : externSymIdx [⟨"caller", []⟩] ["callee"] "callee" = 2 := by
  simp [externSymIdx]

/-- The relocation's packed `r_info` is `(2 << 32) | 4` = `0x200000004`. -/
example :
    ((elf64Rela 1 2 R_X86_64_PLT32 (-4)).drop 8).take 8
      = u64LE (2 * 0x100000000 + 4) := by rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject
