/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.CallSeg

/-!
# `ed25519_compress_x86_from_lean` from the owned backend's output as a `JInstr 64` block

`ed25519CompressShippedBlock` is the body of the function
`ed25519_compress_x86_from_lean` in an x86-64 AT&T file printed by CatCrypt's owned
backend, translated instruction by instruction. The file's producer is recorded in
`PROVENANCE.md` next to it, where one exists.

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
* Omitted from the list: the assembler directives and the 9 frame instructions,
  each checked by the importer: `pushq` of `%rbx`, `%r12`, `%r13` on entry and the
  `popq` sequence in reverse order on exit; the stack allocation `leaq -144(%rsp),
  %rsp` and its release `leaq 144(%rsp), %rsp`; `ret`.
* `ed25519CompressShippedPrologue` and `ed25519CompressShippedEpilogue` are the
  frame instructions before and after the block, `ret` excluded: each `pushq r` as
  `lea "%rsp" "%rsp" "%rsp" 0 (-8)` followed by `storeMem "%rsp" 0 (.reg r)`, each
  `popq r` as `loadMem r "%rsp" 0` followed by `lea "%rsp" "%rsp" "%rsp" 0 8`, and
  the stack allocation and its release as the instruction the text contains. `lea`
  writes no flag, as `pushq` and `popq` write none.
* Every other instruction is kept, `%rsp`-relative moves included, as `storeMem
  "%rsp" off` and `loadMem r "%rsp" off`. Their offsets are relative to `%rsp`
  after the omitted allocation, and `%rsp` is constant in the body.
* Registers keep their physical names (`"%rax"`, …, `"%r15"`, `"%rsp"`); no
  register allocation is involved.
* `JasminModel` keys memory by the name of the base register and a byte offset, at
  word granularity. A proof over this block is a statement about that model; it
  agrees with the processor where each base register holds one address throughout
  the block and distinct names address disjoint words.
* An index-free `leaq off(%b), %d` is `lea d b b 0 off`, whose value `b + b * 0 +
  off` is `b + off`; `JInstr.lea` has no index-free form (7 instructions).
* The function makes 4 calls: `fe25519_mul_x86_from_lean` 2,
  `ed25519_invert_x86_from_lean` 1, `ed25519_pack_sign_x86_from_lean` 1. `JInstr`
  has no call instruction, so the block is a `List CallSeg`
  (`Ascent.Imported.CallSeg`): runs of instructions, each followed by the call that
  ends it, if any. The effect of a call is outside `JasminModel`.

The block has 16 instructions. Source instructions by mnemonic: `movq` 9, `leaq` 7,
`call` 4.

## Main definitions

* `ed25519CompressShippedSeg01` … `ed25519CompressShippedSeg05`: the block in 5
  segments, each a literal `List CallSeg`. A segment ends after a call, after the
  entry run of `%rsp` stores, before the exit run of `%rsp` loads, and after 32
  instructions.
* `ed25519CompressShippedBlock`: the block, the concatenation of the segments.
* `ed25519CompressShippedPrologue`, `ed25519CompressShippedEpilogue`: the frame
  instructions before and after the block.

## Main results

* `ed25519CompressShippedBlock_instrs`: the block has 16 instructions.
* `ed25519CompressShippedBlock_calls`: the block makes 4 calls.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519CompressShipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 6 instructions from source lines 9–14,
    then `call ed25519_invert_x86_from_lean`. -/
def ed25519CompressShippedSeg01 : List CallSeg :=
  [ { body :=
        [ .mov "%rbx" (.reg "%rsi"),  -- l.9 `movq %rsi, %rbx`
          .mov "%r12" (.reg "%rdx"),  -- l.10 `movq %rdx, %r12`
          .mov "%r13" (.reg "%rcx"),  -- l.11 `movq %rcx, %r13`
          .storeMem "%rsp" 96 (.reg "%rdi"),  -- l.12 `movq %rdi, 96(%rsp)`
          .lea "%rdi" "%rsp" "%rsp" 0 0,  -- l.13 `leaq (%rsp), %rdi`
          .mov "%rsi" (.reg "%r13") ]  -- l.14 `movq %r13, %rsi`
      callee := some "ed25519_invert_x86_from_lean" } ]  -- l.15 `call ed25519_invert_x86_from_lean`

/-- Segment 2 of the body: the 3 instructions from source lines 16–18,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519CompressShippedSeg02 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.16 `leaq 32(%rsp), %rdi`
          .mov "%rsi" (.reg "%rbx"),  -- l.17 `movq %rbx, %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 0 ]  -- l.18 `leaq (%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.19 `call fe25519_mul_x86_from_lean`

/-- Segment 3 of the body: the 3 instructions from source lines 20–22,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519CompressShippedSeg03 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.20 `leaq 64(%rsp), %rdi`
          .mov "%rsi" (.reg "%r12"),  -- l.21 `movq %r12, %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 0 ]  -- l.22 `leaq (%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.23 `call fe25519_mul_x86_from_lean`

/-- Segment 4 of the body: the 3 instructions from source lines 24–26,
    then `call ed25519_pack_sign_x86_from_lean`. -/
def ed25519CompressShippedSeg04 : List CallSeg :=
  [ { body :=
        [ .loadMem "%rdi" "%rsp" 96,  -- l.24 `movq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64,  -- l.25 `leaq 64(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 32 ]  -- l.26 `leaq 32(%rsp), %rdx`
      callee := some "ed25519_pack_sign_x86_from_lean" } ]  -- l.27 `call ed25519_pack_sign_x86_from_lean`

/-- Segment 5 of the body: the 1 instruction from source line 28. -/
def ed25519CompressShippedSeg05 : List CallSeg :=
  [ { body :=
        [ .storeMem "%rsp" 96 (.imm 0) ]  -- l.28 `movq $0, 96(%rsp)`
      callee := none } ]

/-- The body of `ed25519_compress_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 5 segments.
    Each segment is a run of instructions followed by the `call` that ends it, if any. -/
def ed25519CompressShippedBlock : List CallSeg :=
  ed25519CompressShippedSeg01 ++ ed25519CompressShippedSeg02 ++
  ed25519CompressShippedSeg03 ++ ed25519CompressShippedSeg04 ++
  ed25519CompressShippedSeg05

/-- The frame instructions of `ed25519_compress_x86_from_lean` before the body,
    which the block omits: each `pushq r` as `leaq -8(%rsp), %rsp` followed by the
    store of `r` at `0(%rsp)`, and the stack allocation as the instruction the text
    contains. -/
def ed25519CompressShippedPrologue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.5 `pushq %rbx`
    .storeMem "%rsp" 0 (.reg "%rbx"),  -- l.5 `pushq %rbx`
    .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.6 `pushq %r12`
    .storeMem "%rsp" 0 (.reg "%r12"),  -- l.6 `pushq %r12`
    .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.7 `pushq %r13`
    .storeMem "%rsp" 0 (.reg "%r13"),  -- l.7 `pushq %r13`
    .lea "%rsp" "%rsp" "%rsp" 0 (-144) ]  -- l.8 `leaq -144(%rsp), %rsp`

/-- The frame instructions of `ed25519_compress_x86_from_lean` after the body,
    which the block omits, `ret` excluded: the stack release as the instruction the
    text contains, and each `popq r` as the load of `r` from `0(%rsp)` followed by
    `leaq 8(%rsp), %rsp`. -/
def ed25519CompressShippedEpilogue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 144,  -- l.29 `leaq 144(%rsp), %rsp`
    .loadMem "%r13" "%rsp" 0,  -- l.30 `popq %r13`
    .lea "%rsp" "%rsp" "%rsp" 0 8,  -- l.30 `popq %r13`
    .loadMem "%r12" "%rsp" 0,  -- l.31 `popq %r12`
    .lea "%rsp" "%rsp" "%rsp" 0 8,  -- l.31 `popq %r12`
    .loadMem "%rbx" "%rsp" 0,  -- l.32 `popq %rbx`
    .lea "%rsp" "%rsp" "%rsp" 0 8 ]  -- l.32 `popq %rbx`

/-- The block has 16 instructions; the count of each segment is computed by `rfl`. -/
theorem ed25519CompressShippedBlock_instrs :
    (CallSeg.instrs ed25519CompressShippedBlock).length = 16 := by
  unfold ed25519CompressShippedBlock
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- The block makes 4 calls; the count of each segment is computed by `rfl`. -/
theorem ed25519CompressShippedBlock_calls :
    (CallSeg.callees ed25519CompressShippedBlock).length = 4 := by
  unfold ed25519CompressShippedBlock
  simp only [CallSeg.callees_append, List.length_append]
  rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519CompressShipped
