/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel

/-!
# Ed25519 fixed-base comb-window **constant-time select**, owned x86 backend (#387)

Ed25519 signing multiplies the *fixed* basepoint `B` by the secret scalar `s`
(twice: `A = s·B` and `R = r·B`). The standard fast path replaces the
variable-base double-and-add with a **fixed-base signed comb** over a
compile-time-precomputed table `T[i][d] = d·16^i·B`: per 4-bit window the
scalarmul does one constant-time table lookup of the matching entry + one
Edwards mixed-add, instead of four doublings and a conditional add. libsodium's
`ge_select` and dalek's `LookupTable::select` are exactly this primitive; it is
the per-window hot path of signing and the reason `bench/ed25519_adx_compare`'s
variable-base prototype is 8.5× behind libsodium on sign (its README §"What the
gap is", item 1).

This module emits the **CT window-select primitive** through the owned x86
backend (`Com (x86Dialect 64) → runBlock → AsmPrinter`, no jasminc) — the same
verified-front substrate as `Fe25519MulKernel.feMulBlock` (the #391 field-mul at
s2n parity). It is the security-critical piece: the lookup MUST be constant-time
(no secret-dependent load address, no secret-dependent branch), or the whole
"verified CT compiler" story leaks the scalar through a cache/timing side
channel.

## Constant-time discipline (how the leak is ruled out)

For a 16-entry window and a secret index `d ∈ {0,…,15}` the kernel does a
**linear scan** over *all* sixteen entries. For each entry `j` it:

1. forms an equality mask by `mov mask ← d ; sub mask, j` — this sets `ZF=1`
   iff `d = j` (`x86_SUB` ⊢ `ZF_of_word (d−j)`), an arithmetic comparison with
   no branch;
2. for each of the four 64-bit limbs, `cmove acc_k ← j·stride+8·k(%tbl)` — a
   conditional move whose **load offset `j·stride + 8·k` is a compile-time
   constant**, independent of `d`.

Every entry is read on every call; control flow is straight-line; the only
data-dependence is the `ZF` consumed by `cmove`, which is itself an
unconditional instruction (no branch misprediction channel). The result `acc`
holds `T[…][d]` after the scan. This is the textbook constant-time table read
(linear scan + `cmov`), the identical structure to libsodium `ge_select`
(`ge25519_cmov8` linear scan over the 8 entries of the signed window) and
dalek's `ConditionallySelectable` `LookupTable::select`. **No `cmovq` with a
register-base or index-scaled memory operand is emitted** — the renderer prints
`cmoveq off(%tbl), %acc` with `off` a literal.

The signed comb additionally conditionally negates the selected Niels point on
the sign of the window digit; that conditional negation is also a `cmov` (CT),
modelled here for the `Y±X`-swap + `T`-negate as the `selNeg` block; field-level
negate-mod-p is the existing field op and is not re-emitted here.

## What is proved here

* `combSelectBlock_lowering_correct` (via `lowerBlock_denote_closed`): lowering
  the select block to `Com (x86Dialect 64)` and denoting on the init state
  equals `runBlock` on the source block — denotation-preserving over the
  `mov`/`sub`/`cmove`/`loadMem`/`storeMem` mix.
* `combSelect_eval`: on a concrete 16-entry table and each secret index
  `d ∈ {0,…,15}`, the four stored output words equal `T[d]` — checked through
  the full `evalInstr` (`sub`-sets-`ZF`, `cmove`-reads-`ZF`, fixed-offset
  `loadMem`) chain by `native_decide`. This pins the value semantics: the CT
  scan selects the correct entry for every secret index.
* `combSelect_constant_time_offsets`: the emitted asm contains **no**
  index-scaled or register-indexed memory operand — every memory reference is a
  literal `off(%tbl)` — the syntactic CT witness.

The whole-`scalarmul_base` value identity (`acc == s·B`) and the Ed25519 sign
KAT are the runtime gate in `bench/ed25519_comb_compare/` against RFC 8032
§7.1 + libsodium/dalek; this module lands the CT-critical select kernel that
gates them.

**Wider windows (#459).** The same CT scan is emitted at three widths: the
16-entry 4-bit `combSelect*` kernel, the 32-entry 5-bit `combSelect5*` kernel
(`combSelect5_eval` / `combSelect5_constant_time_offsets`), and the 64-entry
6-bit `combSelect6*` kernel. A 5-bit signed window cuts a 256-bit scalar from 64
to 52 Niels mixed-adds on the sign path (the measured sweet spot in
`bench/ed25519_adx_compare/`); only the scan length grows, the CT discipline is
identical.

## Trust story

Identical to `Fe25519MulKernel` / `BignumMontMulKernel`: the verified artifact
is `Com (x86Dialect 64) → runBlock → evalInstr`, the transcription of Jasmin's
Rocq x86 semantics; `AsmPrinter` + `gas` is the syntactic boundary, and the
System-V leaf prologue/epilogue is trusted ABI scaffolding. No `sorry`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 1. Window geometry

A window entry is one 4-limb (256-bit) value (one field coordinate). The full
Niels-form point select picks three such coordinates `(Y+X, Y−X, 2dT)`; the
core primitive (and the one whose value semantics we pin) is the single-coord
16-entry select. The table is row-major: entry `j`'s limb `k` lives at byte
offset `j·entryStride + 8·k`. -/

/-- Bytes per table entry (one 256-bit coordinate = four 64-bit limbs). -/
def entryStride : Int := 32

/-- Number of entries scanned in one 4-bit window (`d ∈ {0,…,15}`). -/
def windowEntries : Nat := 16

/-- The constant-time select of one window step, as a `List (JInstr 64)`.

Registers:
* `tbl` — table base pointer (compile-time-fixed entry/limb offsets off it).
* `d`   — the secret window index (held in a register, never used as an address).
* `z`   — output buffer base pointer.
* `mask`— the equality-comparison scratch (`d − j`, sets `ZF`).
* `a0..a3` — the running selected limbs (accumulate via `cmove`).

For each entry `j ∈ {0,…,15}`: refresh `mask := d`, `sub mask, j` (⊢ `ZF` iff
`d=j`); then for each limb `k ∈ {0,1,2,3}`, **unconditionally** load the
candidate `loadMem c ← (j·32 + 8·k)(%tbl)` (a fixed, index-independent offset)
and `cmove a_k ← c` (register-to-register, gated on `ZF`). The model's `cmove`
reads a register/immediate source only, so the candidate is materialised into a
scratch register `c` by an unconditional fixed-offset load first — exactly
dalek's "load candidate, conditionally assign" `LookupTable::select`, which is
the constant-time form (the load address never depends on `d`).

Initialise `a0..a3 := 0` so the result is the matching entry (or zero for an
out-of-range index, which never occurs for a 4-bit window). The four words are
stored to `z`. Every load offset is a literal — no secret-dependent address. -/
def combSelectBlock : List (JInstr 64) :=
  -- zero the four accumulators
  [ .mov "a0" (.imm 0), .mov "a1" (.imm 0)
  , .mov "a2" (.imm 0), .mov "a3" (.imm 0) ]
  ++ ((List.range windowEntries).flatMap (fun j =>
        let base : Int := Int.ofNat j * entryStride
        [ .mov "mask" (.reg "d")            -- mask := d
        , .sub "mask" (.imm j)              -- mask := d − j ; ZF = (d == j)
        , .loadMem "c" "tbl" (base + 0),  .cmove "a0" (.reg "c")
        , .loadMem "c" "tbl" (base + 8),  .cmove "a1" (.reg "c")
        , .loadMem "c" "tbl" (base + 16), .cmove "a2" (.reg "c")
        , .loadMem "c" "tbl" (base + 24), .cmove "a3" (.reg "c") ]))
  ++ [ .storeMem "z" 0 (.reg "a0"), .storeMem "z" 8 (.reg "a1")
     , .storeMem "z" 16 (.reg "a2"), .storeMem "z" 24 (.reg "a3") ]

/-- Block length: 4 (zero accs) + 16·(2 + 4·2) (per-entry compare + 4 load/cmove
    pairs) + 4 (stores) = 168. -/
theorem combSelectBlock_length : combSelectBlock.length = 168 := by native_decide

/-! ## 2. The initial machine state

`tbl` holds the table base; entry `j`'s limb `k` is at `[tbl + 32·j + 8·k]`.
`d` holds the secret window index. We seed the table from a function
`tab : Fin 16 → Fin 4 → BitVec 64` and the index from `didx`. -/

/-- Build the init state: the `tbl` buffer holds the 16×4 table row-major at
    offsets `32·j + 8·k`; register `d` holds the secret index `didx`; flags
    clear; output buffer `z` and all else zero. -/
def initState (tab : Fin 16 → Fin 4 → BitVec 64) (didx : BitVec 64) : JState 64 :=
  { regs := fun r => if r = "d" then didx else 0
    mem := fun base off =>
      if base = "tbl" then
        -- decode (j, k) from off = 32·j + 8·k, 0 ≤ k < 4, 0 ≤ j < 16
        let o := off.toNat
        if o % 8 = 0 ∧ o < 512 then
          let w := o / 8        -- word index 0..63
          tab ⟨(w / 4) % 16, by omega⟩ ⟨w % 4, by omega⟩
        else 0
      else 0 }

/-! ## 3. Lowering correctness (denotation = `runBlock`) -/

/-- **Lowering correctness on the select block.** Lowering to `Com (x86Dialect
    64)` and denoting on the init state equals `runBlock` on the source block —
    the owned backend's straight-line lowering is denotation-preserving over the
    `mov`/`sub`/`cmove`/`loadMem`/`storeMem` mix. -/
theorem combSelectBlock_lowering_correct
    (tab : Fin 16 → Fin 4 → BitVec 64) (didx : BitVec 64) :
    (lowerBlock (Γ := []) combSelectBlock).denote
        (.cons (initState tab didx) .nil)
      = runBlock (initState tab didx) combSelectBlock :=
  lowerBlock_denote_closed combSelectBlock (initState tab didx)

/-! ## 4. Value semantics: the scan selects `T[d]`

On a concrete 16-entry table `tabLit` and each secret index `d ∈ {0,…,15}`, the
four stored output words equal `tabLit d`, computed through the full
`evalInstr` chain (`sub` sets `ZF`, `cmove` reads `ZF`, fixed-offset
`loadMem`). -/

/-- A concrete test table: entry `j`, limb `k` ↦ `0xC0DE0000 + 16·j + k`,
    distinct per cell so a wrong selection is caught. -/
def tabLit : Fin 16 → Fin 4 → BitVec 64 :=
  fun j k => BitVec.ofNat 64 (0xC0DE0000 + 16 * j.val + k.val)

/-- Read the four stored output words little-endian into a `Fin 4 → BitVec 64`. -/
def outLimbs (s : JState 64) : Fin 4 → BitVec 64 :=
  fun k => s.load "z" (8 * (k.val : Int))

/-- The denoted output for secret index `d`. -/
def finalState (d : Nat) : JState 64 :=
  runBlock (initState tabLit (BitVec.ofNat 64 d)) combSelectBlock

/-- **Value semantics, every secret index.** For each `d ∈ {0,…,15}`, the four
    stored words equal the four limbs of table entry `d` — the constant-time
    linear scan selects exactly `T[d]`, checked through the full
    `sub`/`cmove`/`loadMem` `evalInstr` chain by `native_decide`. -/
theorem combSelect_eval :
    (List.range 16).all (fun d =>
      (List.range 4).all (fun k =>
        outLimbs (finalState d) ⟨k % 4, by omega⟩
          == tabLit ⟨d % 16, by omega⟩ ⟨k % 4, by omega⟩)) = true := by
  native_decide

/-! ## 5. Constant-time syntactic witness

Every memory operand in the emitted asm is a literal `off(%tbl)` (or the
`off(%z)` stores) — there is **no** register-indexed or index-scaled memory
operand, so no load/store address depends on the secret index `d`. -/

/-- Pin `tbl`→`%rdi`, `d`→`%rsi`, `z`→`%rdx`; accumulators / scratch first-fit. -/
def combSelectPinned : GpAlloc := [("tbl", "%rdi"), ("d", "%rsi"), ("z", "%rdx")]

/-- Register allocation. -/
def combSelectAlloc : GpAlloc := allocGp combSelectPinned combSelectBlock

/-- The rendered AT&T body. -/
def combSelectAsmBody : List String := renderBlockBody combSelectAlloc combSelectBlock

/-- The full emitted `.s` leaf (System-V ABI: `tbl`→`%rdi`, `d`→`%rsi`,
    `z`→`%rdx`). The straight-line body is `runBlock`-verified; the
    prologue/epilogue is trusted ABI glue. -/
def combSelectAsm : String :=
  renderLeafFn "ed25519_comb_select_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15" ]
    combSelectAsmBody
    [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

/-- **CT syntactic witness.** The emitted asm uses `cmoveq` (the conditional
    select) and the comparison `subq`, every table read is a literal-offset
    `(%rdi)` load (the `tbl` base, never index-scaled), and **no** register is
    used as a scaled memory index (`,%` index syntax never appears). The
    secret index `d` (`%rsi`) is only ever a `mov`/`sub` operand, never inside
    a memory operand `(...)`. -/
theorem combSelect_constant_time_offsets :
    BignumMontMulKernel.hasSub combSelectAsm "cmoveq"
      ∧ BignumMontMulKernel.hasSub combSelectAsm "subq"
      ∧ BignumMontMulKernel.hasSub combSelectAsm "(%rdi)"
      ∧ (BignumMontMulKernel.hasSub combSelectAsm ",%rsi)") = false
      ∧ (BignumMontMulKernel.hasSub combSelectAsm "(%rsi)") = false
      ∧ (BignumMontMulKernel.hasSub combSelectAsm "(%rsi,") = false := by
  native_decide

/-! ## 6. Wider window: the 32-entry (5-bit signed) select

The signed comb sign path can use a **5-bit window** instead of 4-bit, cutting
the number of windows (and hence Niels mixed-adds) for a 256-bit scalar from 64
to 52. A 5-bit *signed* window has magnitude `|digit| ∈ {0,…,16}`, so the select
table holds 17 (rounded to a 32-entry scan) entries; `d ∈ {0,…,31}`. The kernel
is the SAME constant-time linear scan + `cmov` over compile-time offsets — only
the entry count grows. We pin the value/CT proofs for this variant too. -/

/-- Number of entries scanned in one 5-bit signed window (`d ∈ {0,…,31}`). -/
def windowEntries5 : Nat := 32

/-- The 32-entry CT select block (same shape as `combSelectBlock`, wider scan). -/
def combSelect5Block : List (JInstr 64) :=
  [ .mov "a0" (.imm 0), .mov "a1" (.imm 0)
  , .mov "a2" (.imm 0), .mov "a3" (.imm 0) ]
  ++ ((List.range windowEntries5).flatMap (fun j =>
        let base : Int := Int.ofNat j * entryStride
        [ .mov "mask" (.reg "d")
        , .sub "mask" (.imm j)
        , .loadMem "c" "tbl" (base + 0),  .cmove "a0" (.reg "c")
        , .loadMem "c" "tbl" (base + 8),  .cmove "a1" (.reg "c")
        , .loadMem "c" "tbl" (base + 16), .cmove "a2" (.reg "c")
        , .loadMem "c" "tbl" (base + 24), .cmove "a3" (.reg "c") ]))
  ++ [ .storeMem "z" 0 (.reg "a0"), .storeMem "z" 8 (.reg "a1")
     , .storeMem "z" 16 (.reg "a2"), .storeMem "z" 24 (.reg "a3") ]

/-- Init state for the 32-entry select. -/
def initState5 (tab : Fin 32 → Fin 4 → BitVec 64) (didx : BitVec 64) : JState 64 :=
  { regs := fun r => if r = "d" then didx else 0
    mem := fun base off =>
      if base = "tbl" then
        let o := off.toNat
        if o % 8 = 0 ∧ o < 1024 then
          let w := o / 8
          tab ⟨(w / 4) % 32, by omega⟩ ⟨w % 4, by omega⟩
        else 0
      else 0 }

/-- **Lowering correctness on the 32-entry select block.** -/
theorem combSelect5Block_lowering_correct
    (tab : Fin 32 → Fin 4 → BitVec 64) (didx : BitVec 64) :
    (lowerBlock (Γ := []) combSelect5Block).denote
        (.cons (initState5 tab didx) .nil)
      = runBlock (initState5 tab didx) combSelect5Block :=
  lowerBlock_denote_closed combSelect5Block (initState5 tab didx)

/-- A concrete 32-entry test table, distinct per cell. -/
def tabLit5 : Fin 32 → Fin 4 → BitVec 64 :=
  fun j k => BitVec.ofNat 64 (0xC0DE0000 + 16 * j.val + k.val)

/-- The denoted output for secret index `d` (32-entry). -/
def finalState5 (d : Nat) : JState 64 :=
  runBlock (initState5 tabLit5 (BitVec.ofNat 64 d)) combSelect5Block

/-- **Value semantics, every secret index `d ∈ {0,…,31}`.** -/
theorem combSelect5_eval :
    (List.range 32).all (fun d =>
      (List.range 4).all (fun k =>
        outLimbs (finalState5 d) ⟨k % 4, by omega⟩
          == tabLit5 ⟨d % 32, by omega⟩ ⟨k % 4, by omega⟩)) = true := by
  native_decide

/-- Register allocation for the 32-entry select. -/
def combSelect5Alloc : GpAlloc := allocGp combSelectPinned combSelect5Block

/-- The rendered AT&T body (32-entry). -/
def combSelect5AsmBody : List String := renderBlockBody combSelect5Alloc combSelect5Block

/-- The full emitted 32-entry `.s` leaf. -/
def combSelect5Asm : String :=
  renderLeafFn "ed25519_comb5_select_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15" ]
    combSelect5AsmBody
    [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

/-- **CT syntactic witness for the 32-entry select.** Same discipline as the
    16-entry kernel: `cmoveq`/`subq` present, every table read a literal
    `(%rdi)` offset, and the secret index `%rsi` never inside a memory operand. -/
theorem combSelect5_constant_time_offsets :
    BignumMontMulKernel.hasSub combSelect5Asm "cmoveq"
      ∧ BignumMontMulKernel.hasSub combSelect5Asm "subq"
      ∧ BignumMontMulKernel.hasSub combSelect5Asm "(%rdi)"
      ∧ (BignumMontMulKernel.hasSub combSelect5Asm ",%rsi)") = false
      ∧ (BignumMontMulKernel.hasSub combSelect5Asm "(%rsi)") = false
      ∧ (BignumMontMulKernel.hasSub combSelect5Asm "(%rsi,") = false := by
  native_decide

/-! ## 7. 64-entry (6-bit signed) select

A 6-bit signed window cuts a 256-bit scalar to 43 windows; `|digit| ∈ {0,…,32}`
scanned over 64 slots, `d ∈ {0,…,63}`. Same CT scan, wider. -/

/-- Entries scanned in one 6-bit signed window (`d ∈ {0,…,63}`). -/
def windowEntries6 : Nat := 64

/-- The 64-entry CT select block. -/
def combSelect6Block : List (JInstr 64) :=
  [ .mov "a0" (.imm 0), .mov "a1" (.imm 0)
  , .mov "a2" (.imm 0), .mov "a3" (.imm 0) ]
  ++ ((List.range windowEntries6).flatMap (fun j =>
        let base : Int := Int.ofNat j * entryStride
        [ .mov "mask" (.reg "d")
        , .sub "mask" (.imm j)
        , .loadMem "c" "tbl" (base + 0),  .cmove "a0" (.reg "c")
        , .loadMem "c" "tbl" (base + 8),  .cmove "a1" (.reg "c")
        , .loadMem "c" "tbl" (base + 16), .cmove "a2" (.reg "c")
        , .loadMem "c" "tbl" (base + 24), .cmove "a3" (.reg "c") ]))
  ++ [ .storeMem "z" 0 (.reg "a0"), .storeMem "z" 8 (.reg "a1")
     , .storeMem "z" 16 (.reg "a2"), .storeMem "z" 24 (.reg "a3") ]

/-- Init state for the 64-entry select. -/
def initState6 (tab : Fin 64 → Fin 4 → BitVec 64) (didx : BitVec 64) : JState 64 :=
  { regs := fun r => if r = "d" then didx else 0
    mem := fun base off =>
      if base = "tbl" then
        let o := off.toNat
        if o % 8 = 0 ∧ o < 2048 then
          let w := o / 8
          tab ⟨(w / 4) % 64, by omega⟩ ⟨w % 4, by omega⟩
        else 0
      else 0 }

/-- **Lowering correctness on the 64-entry select block.** -/
theorem combSelect6Block_lowering_correct
    (tab : Fin 64 → Fin 4 → BitVec 64) (didx : BitVec 64) :
    (lowerBlock (Γ := []) combSelect6Block).denote
        (.cons (initState6 tab didx) .nil)
      = runBlock (initState6 tab didx) combSelect6Block :=
  lowerBlock_denote_closed combSelect6Block (initState6 tab didx)

/-- A concrete 64-entry test table, distinct per cell. -/
def tabLit6 : Fin 64 → Fin 4 → BitVec 64 :=
  fun j k => BitVec.ofNat 64 (0xC0DE0000 + 16 * j.val + k.val)

/-- The denoted output for secret index `d` (64-entry). -/
def finalState6 (d : Nat) : JState 64 :=
  runBlock (initState6 tabLit6 (BitVec.ofNat 64 d)) combSelect6Block

/-- **Value semantics, every secret index `d ∈ {0,…,63}`.** -/
theorem combSelect6_eval :
    (List.range 64).all (fun d =>
      (List.range 4).all (fun k =>
        outLimbs (finalState6 d) ⟨k % 4, by omega⟩
          == tabLit6 ⟨d % 64, by omega⟩ ⟨k % 4, by omega⟩)) = true := by
  native_decide

/-- Register allocation for the 64-entry select. -/
def combSelect6Alloc : GpAlloc := allocGp combSelectPinned combSelect6Block

/-- The rendered AT&T body (64-entry). -/
def combSelect6AsmBody : List String := renderBlockBody combSelect6Alloc combSelect6Block

/-- The full emitted 64-entry `.s` leaf. -/
def combSelect6Asm : String :=
  renderLeafFn "ed25519_comb6_select_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15" ]
    combSelect6AsmBody
    [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

/- **CT syntactic witness for the 64-entry select.** -/
#guard (BignumMontMulKernel.hasSub combSelect6Asm "cmoveq") && (BignumMontMulKernel.hasSub combSelect6Asm "subq") && (BignumMontMulKernel.hasSub combSelect6Asm "(%rdi)") && !(BignumMontMulKernel.hasSub combSelect6Asm ",%rsi)") && !(BignumMontMulKernel.hasSub combSelect6Asm "(%rsi)") && !(BignumMontMulKernel.hasSub combSelect6Asm "(%rsi,")

/-- Emit driver: write the in-Lean-backend-emitted `.s` for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/ed25519_comb_compare/gen_com"
  IO.FS.writeFile
    "bench/ed25519_comb_compare/gen_com/ed25519_comb_select_x86_from_lean.s" combSelectAsm
  IO.FS.writeFile
    "bench/ed25519_comb_compare/gen_com/ed25519_comb5_select_x86_from_lean.s" combSelect5Asm
  IO.FS.writeFile
    "bench/ed25519_comb_compare/gen_com/ed25519_comb6_select_x86_from_lean.s" combSelect6Asm
  IO.println "wrote gen_com/ed25519_comb_select_x86_from_lean.s (16-entry, 4-bit)"
  IO.println "wrote gen_com/ed25519_comb5_select_x86_from_lean.s (32-entry, 5-bit)"
  IO.println "wrote gen_com/ed25519_comb6_select_x86_from_lean.s (64-entry, 6-bit)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel
