/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# `fe25519_sub_x86_from_lean` from the owned backend's output as a `JInstr 64` block

`fe25519SubShippedBlock` is the body of the function `fe25519_sub_x86_from_lean` in
an x86-64 AT&T file printed by CatCrypt's owned backend, translated instruction by
instruction. The file's producer is recorded in `PROVENANCE.md` next to it, where
one exists.

## Provenance

* Source: `crates/catcrypt-ed25519/asm/fe25519_sub_x86_from_lean.s` in the
  `SSProve-lean` repository at commit `5a765fbc8aff83bff9eab87c81af0df5d9ae9944`
  (tracked and unchanged at that commit), file SHA-256
  `6c1c5f48c7a52de97743b2a72ff721561dc9ccf81418c27e84284a5229c437dc`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 11 frame instructions,
  each checked by the importer: `pushq` of `%rbx`, `%r12`, `%r13`, `%r14`, `%r15`
  on entry and the `popq` sequence in reverse order on exit; `ret`.
* Every other instruction is kept, `%rsp`-relative moves included, as `storeMem
  "%rsp" off` and `loadMem r "%rsp" off`. `%rsp` is constant in the body.
* Registers keep their physical names (`"%rax"`, …, `"%r15"`, `"%rsp"`); no
  register allocation is involved.
* `JasminModel` keys memory by the name of the base register and a byte offset, at
  word granularity. A proof over this block is a statement about that model; it
  agrees with the processor where each base register holds one address throughout
  the block and distinct names address disjoint words.

The block has 27 instructions. Source instructions by mnemonic: `movq` 16, `sbbq`
7, `andq` 2, `subq` 2.

## Main definitions

* `fe25519SubShippedSeg01`: the block as one segment, a literal `List (JInstr 64)`.
* `fe25519SubShippedBlock`: the block, equal to its one segment.

## Main results

* `fe25519SubShippedBlock_length`: the block has 27 instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519SubShipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 27 instructions from source lines 10–36. -/
def fe25519SubShippedSeg01 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%rdx"),  -- l.10 `movq %rdx, %rdx`
    .loadMem "%rcx" "%rsi" 0,  -- l.11 `movq 0(%rsi), %rcx`
    .loadMem "%r8" "%rdx" 0,  -- l.12 `movq 0(%rdx), %r8`
    .sub "%rcx" (.reg "%r8"),  -- l.13 `subq %r8, %rcx`
    .loadMem "%r9" "%rsi" 8,  -- l.14 `movq 8(%rsi), %r9`
    .loadMem "%r8" "%rdx" 8,  -- l.15 `movq 8(%rdx), %r8`
    .sbb "%r9" (.reg "%r8"),  -- l.16 `sbbq %r8, %r9`
    .loadMem "%r10" "%rsi" 16,  -- l.17 `movq 16(%rsi), %r10`
    .loadMem "%r8" "%rdx" 16,  -- l.18 `movq 16(%rdx), %r8`
    .sbb "%r10" (.reg "%r8"),  -- l.19 `sbbq %r8, %r10`
    .loadMem "%r11" "%rsi" 24,  -- l.20 `movq 24(%rsi), %r11`
    .loadMem "%r8" "%rdx" 24,  -- l.21 `movq 24(%rdx), %r8`
    .sbb "%r11" (.reg "%r8"),  -- l.22 `sbbq %r8, %r11`
    .mov "%rax" (.imm 0),  -- l.23 `movq $0, %rax`
    .sbb "%rax" (.imm 0),  -- l.24 `sbbq $0, %rax`
    .and_ "%rax" (.imm 19),  -- l.25 `andq $19, %rax`
    .mov "%rbx" (.imm 0),  -- l.26 `movq $0, %rbx`
    .sub "%rcx" (.reg "%rax"),  -- l.27 `subq %rax, %rcx`
    .sbb "%r9" (.reg "%rbx"),  -- l.28 `sbbq %rbx, %r9`
    .sbb "%r10" (.reg "%rbx"),  -- l.29 `sbbq %rbx, %r10`
    .sbb "%r11" (.reg "%rbx"),  -- l.30 `sbbq %rbx, %r11`
    .mov "%r8" (.imm 9223372036854775807),  -- l.31 `movq $9223372036854775807, %r8`
    .and_ "%r11" (.reg "%r8"),  -- l.32 `andq %r8, %r11`
    .storeMem "%rdi" 0 (.reg "%rcx"),  -- l.33 `movq %rcx, 0(%rdi)`
    .storeMem "%rdi" 8 (.reg "%r9"),  -- l.34 `movq %r9, 8(%rdi)`
    .storeMem "%rdi" 16 (.reg "%r10"),  -- l.35 `movq %r10, 16(%rdi)`
    .storeMem "%rdi" 24 (.reg "%r11") ]  -- l.36 `movq %r11, 24(%rdi)`

/-- The body of `fe25519_sub_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: its one segment. -/
def fe25519SubShippedBlock : List (JInstr 64) :=
  fe25519SubShippedSeg01

/-- The block has 27 instructions; its count is computed by `rfl`. -/
theorem fe25519SubShippedBlock_length :
    fe25519SubShippedBlock.length = 27 := by
  unfold fe25519SubShippedBlock
  rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519SubShipped
