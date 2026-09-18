/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# `fe25519_add_x86_from_lean` from the owned backend's output as a `JInstr 64` block

`fe25519AddShippedBlock` is the body of the function `fe25519_add_x86_from_lean` in
an x86-64 AT&T file printed by CatCrypt's owned backend, translated instruction by
instruction. The file's producer is recorded in `PROVENANCE.md` next to it, where
one exists.

## Provenance

* Source: `crates/catcrypt-ed25519/asm/fe25519_add_x86_from_lean.s` in the
  `SSProve-lean` repository at commit `5a765fbc8aff83bff9eab87c81af0df5d9ae9944`
  (tracked and unchanged at that commit), file SHA-256
  `ddb97509ab46d713f72ec1cbd664ce2acd69c35982e257dd597d8475042ef92a`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 11 frame instructions,
  each checked by the importer: `pushq` of `%rbx`, `%r12`, `%r13`, `%r14`, `%r15`
  on entry and the `popq` sequence in reverse order on exit; `ret`.
* `fe25519AddShippedPrologue` and `fe25519AddShippedEpilogue` are the frame
  instructions before and after the block, `ret` excluded: each `pushq r` as `lea
  "%rsp" "%rsp" "%rsp" 0 (-8)` followed by `storeMem "%rsp" 0 (.reg r)`, each `popq
  r` as `loadMem r "%rsp" 0` followed by `lea "%rsp" "%rsp" "%rsp" 0 8`, and the
  stack allocation and its release as the instruction the text contains. `lea`
  writes no flag, as `pushq` and `popq` write none.
* Every other instruction is kept, `%rsp`-relative moves included, as `storeMem
  "%rsp" off` and `loadMem r "%rsp" off`. `%rsp` is constant in the body.
* Registers keep their physical names (`"%rax"`, …, `"%r15"`, `"%rsp"`); no
  register allocation is involved.
* `JasminModel` keys memory by the name of the base register and a byte offset, at
  word granularity. A proof over this block is a statement about that model; it
  agrees with the processor where each base register holds one address throughout
  the block and distinct names address disjoint words.

The block has 46 instructions. Source instructions by mnemonic: `movq` 23, `xorq`
8, `adcq` 6, `andq` 5, `addq` 2, `negq` 1, `shrq` 1.

## Main definitions

* `fe25519AddShippedSeg01` … `fe25519AddShippedSeg02`: the block in 2 segments,
  each a literal `List (JInstr 64)`. A segment ends after a call, after the entry
  run of `%rsp` stores, before the exit run of `%rsp` loads, and after 32
  instructions.
* `fe25519AddShippedBlock`: the block, the concatenation of the segments.
* `fe25519AddShippedPrologue`, `fe25519AddShippedEpilogue`: the frame instructions
  before and after the block.

## Main results

* `fe25519AddShippedBlock_length`: the block has 46 instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519AddShipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 32 instructions from source lines 10–41. -/
def fe25519AddShippedSeg01 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%rdx"),  -- l.10 `movq %rdx, %rdx`
    .loadMem "%rcx" "%rsi" 0,  -- l.11 `movq 0(%rsi), %rcx`
    .loadMem "%r8" "%rdx" 0,  -- l.12 `movq 0(%rdx), %r8`
    .add "%rcx" (.reg "%r8"),  -- l.13 `addq %r8, %rcx`
    .loadMem "%r9" "%rsi" 8,  -- l.14 `movq 8(%rsi), %r9`
    .loadMem "%r8" "%rdx" 8,  -- l.15 `movq 8(%rdx), %r8`
    .adc "%r9" (.reg "%r8"),  -- l.16 `adcq %r8, %r9`
    .loadMem "%r10" "%rsi" 16,  -- l.17 `movq 16(%rsi), %r10`
    .loadMem "%r8" "%rdx" 16,  -- l.18 `movq 16(%rdx), %r8`
    .adc "%r10" (.reg "%r8"),  -- l.19 `adcq %r8, %r10`
    .loadMem "%r11" "%rsi" 24,  -- l.20 `movq 24(%rsi), %r11`
    .loadMem "%r8" "%rdx" 24,  -- l.21 `movq 24(%rdx), %r8`
    .adc "%r11" (.reg "%r8"),  -- l.22 `adcq %r8, %r11`
    .mov "%rax" (.reg "%rcx"),  -- l.23 `movq %rcx, %rax`
    .add "%rax" (.imm 19),  -- l.24 `addq $19, %rax`
    .mov "%rbx" (.reg "%r9"),  -- l.25 `movq %r9, %rbx`
    .adc "%rbx" (.imm 0),  -- l.26 `adcq $0, %rbx`
    .mov "%r12" (.reg "%r10"),  -- l.27 `movq %r10, %r12`
    .adc "%r12" (.imm 0),  -- l.28 `adcq $0, %r12`
    .mov "%r13" (.reg "%r11"),  -- l.29 `movq %r11, %r13`
    .adc "%r13" (.imm 0),  -- l.30 `adcq $0, %r13`
    .mov "%r14" (.reg "%r13"),  -- l.31 `movq %r13, %r14`
    .shr "%r14" (.imm 63),  -- l.32 `shrq $63, %r14`
    .neg "%r14",  -- l.33 `negq %r14`
    .mov "%r8" (.imm 9223372036854775807),  -- l.34 `movq $9223372036854775807, %r8`
    .and_ "%r13" (.reg "%r8"),  -- l.35 `andq %r8, %r13`
    .mov "%r8" (.reg "%rax"),  -- l.36 `movq %rax, %r8`
    .xor_ "%r8" (.reg "%rcx"),  -- l.37 `xorq %rcx, %r8`
    .and_ "%r8" (.reg "%r14"),  -- l.38 `andq %r14, %r8`
    .xor_ "%rcx" (.reg "%r8"),  -- l.39 `xorq %r8, %rcx`
    .mov "%r8" (.reg "%rbx"),  -- l.40 `movq %rbx, %r8`
    .xor_ "%r8" (.reg "%r9") ]  -- l.41 `xorq %r9, %r8`

/-- Segment 2 of the body: the 14 instructions from source lines 42–55. -/
def fe25519AddShippedSeg02 : List (JInstr 64) :=
  [ .and_ "%r8" (.reg "%r14"),  -- l.42 `andq %r14, %r8`
    .xor_ "%r9" (.reg "%r8"),  -- l.43 `xorq %r8, %r9`
    .mov "%r8" (.reg "%r12"),  -- l.44 `movq %r12, %r8`
    .xor_ "%r8" (.reg "%r10"),  -- l.45 `xorq %r10, %r8`
    .and_ "%r8" (.reg "%r14"),  -- l.46 `andq %r14, %r8`
    .xor_ "%r10" (.reg "%r8"),  -- l.47 `xorq %r8, %r10`
    .mov "%r8" (.reg "%r13"),  -- l.48 `movq %r13, %r8`
    .xor_ "%r8" (.reg "%r11"),  -- l.49 `xorq %r11, %r8`
    .and_ "%r8" (.reg "%r14"),  -- l.50 `andq %r14, %r8`
    .xor_ "%r11" (.reg "%r8"),  -- l.51 `xorq %r8, %r11`
    .storeMem "%rdi" 0 (.reg "%rcx"),  -- l.52 `movq %rcx, 0(%rdi)`
    .storeMem "%rdi" 8 (.reg "%r9"),  -- l.53 `movq %r9, 8(%rdi)`
    .storeMem "%rdi" 16 (.reg "%r10"),  -- l.54 `movq %r10, 16(%rdi)`
    .storeMem "%rdi" 24 (.reg "%r11") ]  -- l.55 `movq %r11, 24(%rdi)`

/-- The body of `fe25519_add_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 2 segments. -/
def fe25519AddShippedBlock : List (JInstr 64) :=
  fe25519AddShippedSeg01 ++ fe25519AddShippedSeg02

/-- The frame instructions of `fe25519_add_x86_from_lean` before the body,
    which the block omits: each `pushq r` as `leaq -8(%rsp), %rsp` followed by the
    store of `r` at `0(%rsp)`, and the stack allocation as the instruction the text
    contains. -/
def fe25519AddShippedPrologue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.5 `pushq %rbx`
    .storeMem "%rsp" 0 (.reg "%rbx"),  -- l.5 `pushq %rbx`
    .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.6 `pushq %r12`
    .storeMem "%rsp" 0 (.reg "%r12"),  -- l.6 `pushq %r12`
    .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.7 `pushq %r13`
    .storeMem "%rsp" 0 (.reg "%r13"),  -- l.7 `pushq %r13`
    .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.8 `pushq %r14`
    .storeMem "%rsp" 0 (.reg "%r14"),  -- l.8 `pushq %r14`
    .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.9 `pushq %r15`
    .storeMem "%rsp" 0 (.reg "%r15") ]  -- l.9 `pushq %r15`

/-- The frame instructions of `fe25519_add_x86_from_lean` after the body,
    which the block omits, `ret` excluded: the stack release as the instruction the
    text contains, and each `popq r` as the load of `r` from `0(%rsp)` followed by
    `leaq 8(%rsp), %rsp`. -/
def fe25519AddShippedEpilogue : List (JInstr 64) :=
  [ .loadMem "%r15" "%rsp" 0,  -- l.56 `popq %r15`
    .lea "%rsp" "%rsp" "%rsp" 0 8,  -- l.56 `popq %r15`
    .loadMem "%r14" "%rsp" 0,  -- l.57 `popq %r14`
    .lea "%rsp" "%rsp" "%rsp" 0 8,  -- l.57 `popq %r14`
    .loadMem "%r13" "%rsp" 0,  -- l.58 `popq %r13`
    .lea "%rsp" "%rsp" "%rsp" 0 8,  -- l.58 `popq %r13`
    .loadMem "%r12" "%rsp" 0,  -- l.59 `popq %r12`
    .lea "%rsp" "%rsp" "%rsp" 0 8,  -- l.59 `popq %r12`
    .loadMem "%rbx" "%rsp" 0,  -- l.60 `popq %rbx`
    .lea "%rsp" "%rsp" "%rsp" 0 8 ]  -- l.60 `popq %rbx`

/-- The block has 46 instructions; the count of each segment is computed by `rfl`. -/
theorem fe25519AddShippedBlock_length :
    fe25519AddShippedBlock.length = 46 := by
  unfold fe25519AddShippedBlock
  simp only [List.length_append]
  rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519AddShipped
