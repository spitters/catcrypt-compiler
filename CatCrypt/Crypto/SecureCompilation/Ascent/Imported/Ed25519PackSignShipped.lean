/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# `ed25519_pack_sign_x86_from_lean` from the owned backend's output as a `JInstr 64` block

`ed25519PackSignShippedBlock` is the body of the function
`ed25519_pack_sign_x86_from_lean` in an x86-64 AT&T file printed by CatCrypt's
owned backend, translated instruction by instruction. The file's producer is
recorded in `PROVENANCE.md` next to it, where one exists.

## Provenance

* Source: `crates/catcrypt-ed25519/asm/ed25519_compress_x86_from_lean.s` in the
  `SSProve-lean` repository at commit `b294647590404f72dd82b5404e326511f3c055eb`
  (tracked and unchanged at that commit), file SHA-256
  `d5c8ce6b913faf2c354aa7a768acd78c7cac6441cfeafcbae736926402c80d32`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 3 frame instructions,
  each checked by the importer: the stack allocation `leaq -64(%rsp), %rsp` and its
  release `leaq 64(%rsp), %rsp`; `ret`.
* `ed25519PackSignShippedPrologue` and `ed25519PackSignShippedEpilogue` are the
  frame instructions before and after the block, `ret` excluded: each `pushq r` as
  `lea "%rsp" "%rsp" "%rsp" 0 (-8)` followed by `storeMem "%rsp" 0 (.reg r)`, each
  `popq r` as `loadMem r "%rsp" 0` followed by `lea "%rsp" "%rsp" "%rsp" 0 8`, and
  the stack allocation and its release as the instruction the text contains. `lea`
  writes no flag, as `pushq` and `popq` write none.
* Every other instruction is kept, `%rsp`-relative moves included, as `storeMem
  "%rsp" off` and `loadMem r "%rsp" off`. Their offsets are relative to `%rsp`
  after the omitted allocation, and `%rsp` is constant in the body.
* The first 9 instructions store registers into `%rsp` slots and form segment 1.
* Registers keep their physical names (`"%rax"`, …, `"%r15"`, `"%rsp"`); no
  register allocation is involved.
* `JasminModel` keys memory by the name of the base register and a byte offset, at
  word granularity. A proof over this block is a statement about that model; it
  agrees with the processor where each base register holds one address throughout
  the block and distinct names address disjoint words.
* The block writes `%r14` between memory accesses through it, so the accesses
  through that register before and after the write share one memory bank in the
  model.

The block has 60 instructions. Source instructions by mnemonic: `movq` 57, `addq`
1, `andq` 1, `shlq` 1.

## Main definitions

* `ed25519PackSignShippedSeg01` … `ed25519PackSignShippedSeg03`: the block in 3
  segments, each a literal `List (JInstr 64)`. A segment ends after a call, after
  the entry run of `%rsp` stores, before the exit run of `%rsp` loads, and after 32
  instructions.
* `ed25519PackSignShippedBlock`: the block, the concatenation of the segments.
* `ed25519PackSignShippedPrologue`, `ed25519PackSignShippedEpilogue`: the frame
  instructions before and after the block.

## Main results

* `ed25519PackSignShippedBlock_length`: the block has 60 instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PackSignShipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 9 instructions from source lines 40–48. -/
def ed25519PackSignShippedSeg01 : List (JInstr 64) :=
  [ .storeMem "%rsp" 56 (.reg "%rdi"),  -- l.40 `movq %rdi, 56(%rsp)`
    .storeMem "%rsp" 48 (.reg "%rsi"),  -- l.41 `movq %rsi, 48(%rsp)`
    .storeMem "%rsp" 40 (.reg "%rbx"),  -- l.42 `movq %rbx, 40(%rsp)`
    .storeMem "%rsp" 32 (.reg "%rbp"),  -- l.43 `movq %rbp, 32(%rsp)`
    .storeMem "%rsp" 24 (.reg "%r12"),  -- l.44 `movq %r12, 24(%rsp)`
    .storeMem "%rsp" 16 (.reg "%r13"),  -- l.45 `movq %r13, 16(%rsp)`
    .storeMem "%rsp" 8 (.reg "%r14"),  -- l.46 `movq %r14, 8(%rsp)`
    .storeMem "%rsp" 0 (.reg "%r15"),  -- l.47 `movq %r15, 0(%rsp)`
    .storeMem "%rsp" (-8) (.reg "%rdx") ]  -- l.48 `movq %rdx, -8(%rsp)`

/-- Segment 2 of the body: the 32 instructions from source lines 49–80. -/
def ed25519PackSignShippedSeg02 : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 56,  -- l.49 `movq 56(%rsp), %rbx`
    .loadMem "%rcx" "%rsp" 48,  -- l.50 `movq 48(%rsp), %rcx`
    .mov "%rax" (.imm 0),  -- l.51 `movq $0, %rax`
    .mov "%r14" (.reg "%rcx"),  -- l.52 `movq %rcx, %r14`
    .loadMemIdx "%rsi" "%r14" "%rax" 8,  -- l.53 `movq (%r14, %rax, 8), %rsi`
    .mov "%rax" (.imm 0),  -- l.54 `movq $0, %rax`
    .mov "%r14" (.reg "%rbx"),  -- l.55 `movq %rbx, %r14`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%rsi"),  -- l.56 `movq %rsi, (%r14, %rax, 8)`
    .mov "%rax" (.imm 1),  -- l.57 `movq $1, %rax`
    .loadMem "%r14" "%rsp" 48,  -- l.58 `movq 48(%rsp), %r14`
    .loadMemIdx "%rsi" "%r14" "%rax" 8,  -- l.59 `movq (%r14, %rax, 8), %rsi`
    .mov "%rax" (.imm 1),  -- l.60 `movq $1, %rax`
    .loadMem "%r14" "%rsp" 56,  -- l.61 `movq 56(%rsp), %r14`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%rsi"),  -- l.62 `movq %rsi, (%r14, %rax, 8)`
    .mov "%rax" (.imm 2),  -- l.63 `movq $2, %rax`
    .loadMem "%r14" "%rsp" 48,  -- l.64 `movq 48(%rsp), %r14`
    .loadMemIdx "%rsi" "%r14" "%rax" 8,  -- l.65 `movq (%r14, %rax, 8), %rsi`
    .mov "%rax" (.imm 2),  -- l.66 `movq $2, %rax`
    .loadMem "%r14" "%rsp" 56,  -- l.67 `movq 56(%rsp), %r14`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%rsi"),  -- l.68 `movq %rsi, (%r14, %rax, 8)`
    .mov "%rax" (.imm 3),  -- l.69 `movq $3, %rax`
    .loadMem "%r14" "%rsp" 48,  -- l.70 `movq 48(%rsp), %r14`
    .loadMemIdx "%rsi" "%r14" "%rax" 8,  -- l.71 `movq (%r14, %rax, 8), %rsi`
    .mov "%rax" (.imm 0),  -- l.72 `movq $0, %rax`
    .loadMem "%r14" "%rsp" (-8),  -- l.73 `movq -8(%rsp), %r14`
    .loadMemIdx "%rcx" "%r14" "%rax" 8,  -- l.74 `movq (%r14, %rax, 8), %rcx`
    .mov "%rdx" (.reg "%rcx"),  -- l.75 `movq %rcx, %rdx`
    .and_ "%rdx" (.imm 1),  -- l.76 `andq $1, %rdx`
    .mov "%rax" (.reg "%rdx"),  -- l.77 `movq %rdx, %rax`
    .shl "%rax" (.imm 63),  -- l.78 `shlq $63, %rax`
    .mov "%rcx" (.reg "%rsi"),  -- l.79 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rax") ]  -- l.80 `addq %rax, %rcx`

/-- Segment 3 of the body: the 19 instructions from source lines 81–99. -/
def ed25519PackSignShippedSeg03 : List (JInstr 64) :=
  [ .mov "%rax" (.reg "%rcx"),  -- l.81 `movq %rcx, %rax`
    .mov "%rcx" (.imm 3),  -- l.82 `movq $3, %rcx`
    .loadMem "%r14" "%rsp" 56,  -- l.83 `movq 56(%rsp), %r14`
    .storeMemIdx "%r14" "%rcx" 8 (.reg "%rax"),  -- l.84 `movq %rax, (%r14, %rcx, 8)`
    .loadMem "%rbx" "%rsp" 40,  -- l.85 `movq 40(%rsp), %rbx`
    .loadMem "%rbp" "%rsp" 32,  -- l.86 `movq 32(%rsp), %rbp`
    .loadMem "%r12" "%rsp" 24,  -- l.87 `movq 24(%rsp), %r12`
    .loadMem "%r13" "%rsp" 16,  -- l.88 `movq 16(%rsp), %r13`
    .loadMem "%r14" "%rsp" 8,  -- l.89 `movq 8(%rsp), %r14`
    .loadMem "%r15" "%rsp" 0,  -- l.90 `movq 0(%rsp), %r15`
    .storeMem "%rsp" 56 (.imm 0),  -- l.91 `movq $0, 56(%rsp)`
    .storeMem "%rsp" 48 (.imm 0),  -- l.92 `movq $0, 48(%rsp)`
    .storeMem "%rsp" 40 (.imm 0),  -- l.93 `movq $0, 40(%rsp)`
    .storeMem "%rsp" 32 (.imm 0),  -- l.94 `movq $0, 32(%rsp)`
    .storeMem "%rsp" 24 (.imm 0),  -- l.95 `movq $0, 24(%rsp)`
    .storeMem "%rsp" 16 (.imm 0),  -- l.96 `movq $0, 16(%rsp)`
    .storeMem "%rsp" 8 (.imm 0),  -- l.97 `movq $0, 8(%rsp)`
    .storeMem "%rsp" 0 (.imm 0),  -- l.98 `movq $0, 0(%rsp)`
    .storeMem "%rsp" (-8) (.imm 0) ]  -- l.99 `movq $0, -8(%rsp)`

/-- The body of `ed25519_pack_sign_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 3 segments. -/
def ed25519PackSignShippedBlock : List (JInstr 64) :=
  ed25519PackSignShippedSeg01 ++ ed25519PackSignShippedSeg02 ++
  ed25519PackSignShippedSeg03

/-- The frame instructions of `ed25519_pack_sign_x86_from_lean` before the body,
    which the block omits: each `pushq r` as `leaq -8(%rsp), %rsp` followed by the
    store of `r` at `0(%rsp)`, and the stack allocation as the instruction the text
    contains. -/
def ed25519PackSignShippedPrologue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-64) ]  -- l.39 `leaq -64(%rsp), %rsp`

/-- The frame instructions of `ed25519_pack_sign_x86_from_lean` after the body,
    which the block omits, `ret` excluded: the stack release as the instruction the
    text contains, and each `popq r` as the load of `r` from `0(%rsp)` followed by
    `leaq 8(%rsp), %rsp`. -/
def ed25519PackSignShippedEpilogue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 64 ]  -- l.100 `leaq 64(%rsp), %rsp`

/-- The block has 60 instructions; the count of each segment is computed by `rfl`. -/
theorem ed25519PackSignShippedBlock_length :
    ed25519PackSignShippedBlock.length = 60 := by
  unfold ed25519PackSignShippedBlock
  simp only [List.length_append]
  rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PackSignShipped
