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
  `SSProve-lean` repository at commit `5a765fbc8aff83bff9eab87c81af0df5d9ae9944`
  (tracked and unchanged at that commit), file SHA-256
  `36a0fbf6138d0ee54f04de691b1c4674cd9594a4fdb5ba19ee0c73da3dd5e14f`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 9 frame instructions,
  each checked by the importer: `pushq` of `%rbx`, `%r12`, `%r13` on entry and the
  `popq` sequence in reverse order on exit; the stack allocation `leaq -144(%rsp),
  %rsp` and its release `leaq 144(%rsp), %rsp`; `ret`.
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

The block has 15 instructions. Source instructions by mnemonic: `movq` 8, `leaq` 7,
`call` 4.

## Main definitions

* `ed25519CompressShippedSeg01` … `ed25519CompressShippedSeg04`: the block in 4
  segments, each a literal `List CallSeg`. A segment ends after a call, after the
  entry run of `%rsp` stores, before the exit run of `%rsp` loads, and after 32
  instructions.
* `ed25519CompressShippedBlock`: the block, the concatenation of the segments.

## Main results

* `ed25519CompressShippedBlock_instrs`: the block has 15 instructions.
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

/-- The body of `ed25519_compress_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 4 segments.
    Each segment is a run of instructions followed by the `call` that ends it, if any. -/
def ed25519CompressShippedBlock : List CallSeg :=
  ed25519CompressShippedSeg01 ++ ed25519CompressShippedSeg02 ++
  ed25519CompressShippedSeg03 ++ ed25519CompressShippedSeg04

/-- The block has 15 instructions; the count of each segment is computed by `rfl`. -/
theorem ed25519CompressShippedBlock_instrs :
    (CallSeg.instrs ed25519CompressShippedBlock).length = 15 := by
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
