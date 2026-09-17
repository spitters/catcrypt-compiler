/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.CallSeg

/-!
# `ed25519_madd_x86_from_lean` from the owned backend's output as a `JInstr 64` block

`ed25519MaddShippedBlock` is the body of the function `ed25519_madd_x86_from_lean`
in an x86-64 AT&T file printed by CatCrypt's owned backend, translated instruction
by instruction. The file's producer is recorded in `PROVENANCE.md` next to it,
where one exists.

## Provenance

* Source: `crates/catcrypt-ed25519/asm/ed25519_madd_x86_from_lean.s` in the
  `SSProve-lean` repository at commit `5a765fbc8aff83bff9eab87c81af0df5d9ae9944`
  (tracked and unchanged at that commit), file SHA-256
  `19ab9911fbfec304ba74f70ae895c9efd76a3eae860b8c027664776745a3fb3e`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 3 frame instructions,
  each checked by the importer: the stack allocation `leaq -632(%rsp), %rsp` and
  its release `leaq 632(%rsp), %rsp`; `ret`.
* Every other instruction is kept, `%rsp`-relative moves included, as `storeMem
  "%rsp" off` and `loadMem r "%rsp" off`. Their offsets are relative to `%rsp`
  after the omitted allocation, and `%rsp` is constant in the body.
* The first 2 instructions store registers into `%rsp` slots and form segment 1.
* Registers keep their physical names (`"%rax"`, …, `"%r15"`, `"%rsp"`); no
  register allocation is involved.
* `JasminModel` keys memory by the name of the base register and a byte offset, at
  word granularity. A proof over this block is a statement about that model; it
  agrees with the processor where each base register holds one address throughout
  the block and distinct names address disjoint words.
* The block accesses memory through registers that a `leaq` set to an address
  computed from another register: `%r9` (from `%rsp`). In the model those accesses
  use the bank of the register's own name, which is unrelated to the bank of the
  register the address was computed from.
* An index-free `leaq off(%b), %d` is `lea d b b 0 off`, whose value `b + b * 0 +
  off` is `b + off`; `JInstr.lea` has no index-free form (48 instructions).
* The function makes 15 calls: `fe25519_mul_x86_from_lean` 7,
  `fe25519_add_x86_from_lean` 4, `fe25519_sub_x86_from_lean` 3,
  `ed25519_join16_x86_from_lean` 1. `JInstr` has no call instruction, so the block
  is a `List CallSeg` (`Ascent.Imported.CallSeg`): runs of instructions, each
  followed by the call that ends it, if any. The effect of a call is outside
  `JasminModel`.

The block has 98 instructions. Source instructions by mnemonic: `movq` 50, `leaq`
48, `call` 15.

## Main definitions

* `ed25519MaddShippedSeg01` … `ed25519MaddShippedSeg18`: the block in 18
  segments, each a literal `List CallSeg`. A segment ends after a call, after the
  entry run of `%rsp` stores, before the exit run of `%rsp` loads, and after 32
  instructions.
* `ed25519MaddShippedPart01` … `ed25519MaddShippedPart02`: the segments in 2
  parts of at most 16 consecutive segments, each with lemmas giving its instruction
  count and its call count.
* `ed25519MaddShippedBlock`: the block, the concatenation of the parts.

## Main results

* `ed25519MaddShippedBlock_instrs`: the block has 98 instructions.
* `ed25519MaddShippedBlock_calls`: the block makes 15 calls.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519MaddShipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 2 instructions from source lines 6–7. -/
def ed25519MaddShippedSeg01 : List CallSeg :=
  [ { body :=
        [ .storeMem "%rsp" 576 (.reg "%rsi"),  -- l.6 `movq %rsi, 576(%rsp)`
          .storeMem "%rsp" 584 (.reg "%rdi") ]  -- l.7 `movq %rdi, 584(%rsp)`
      callee := none } ]

/-- Segment 2 of the body: the 4 instructions from source lines 8–11,
    then `call fe25519_add_x86_from_lean`. -/
def ed25519MaddShippedSeg02 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.8 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 0,  -- l.9 `leaq (%rsp), %rdi`
          .lea "%rsi" "%r10" "%r10" 0 32,  -- l.10 `leaq 32(%r10), %rsi`
          .lea "%rdx" "%r10" "%r10" 0 0 ]  -- l.11 `leaq (%r10), %rdx`
      callee := some "fe25519_add_x86_from_lean" } ]  -- l.12 `call fe25519_add_x86_from_lean`

/-- Segment 3 of the body: the 4 instructions from source lines 13–16,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519MaddShippedSeg03 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.13 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.14 `leaq 32(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 0,  -- l.15 `leaq (%rsp), %rsi`
          .lea "%rdx" "%r10" "%r10" 0 128 ]  -- l.16 `leaq 128(%r10), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.17 `call fe25519_mul_x86_from_lean`

/-- Segment 4 of the body: the 4 instructions from source lines 18–21,
    then `call fe25519_sub_x86_from_lean`. -/
def ed25519MaddShippedSeg04 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.18 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.19 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%r10" "%r10" 0 32,  -- l.20 `leaq 32(%r10), %rsi`
          .lea "%rdx" "%r10" "%r10" 0 0 ]  -- l.21 `leaq (%r10), %rdx`
      callee := some "fe25519_sub_x86_from_lean" } ]  -- l.22 `call fe25519_sub_x86_from_lean`

/-- Segment 5 of the body: the 4 instructions from source lines 23–26,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519MaddShippedSeg05 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.23 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.24 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64,  -- l.25 `leaq 64(%rsp), %rsi`
          .lea "%rdx" "%r10" "%r10" 0 160 ]  -- l.26 `leaq 160(%r10), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.27 `call fe25519_mul_x86_from_lean`

/-- Segment 6 of the body: the 4 instructions from source lines 28–31,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519MaddShippedSeg06 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.28 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 128,  -- l.29 `leaq 128(%rsp), %rdi`
          .lea "%rsi" "%r10" "%r10" 0 96,  -- l.30 `leaq 96(%r10), %rsi`
          .lea "%rdx" "%r10" "%r10" 0 192 ]  -- l.31 `leaq 192(%r10), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.32 `call fe25519_mul_x86_from_lean`

/-- Segment 7 of the body: the 4 instructions from source lines 33–36,
    then `call fe25519_add_x86_from_lean`. -/
def ed25519MaddShippedSeg07 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.33 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 160,  -- l.34 `leaq 160(%rsp), %rdi`
          .lea "%rsi" "%r10" "%r10" 0 64,  -- l.35 `leaq 64(%r10), %rsi`
          .lea "%rdx" "%r10" "%r10" 0 64 ]  -- l.36 `leaq 64(%r10), %rdx`
      callee := some "fe25519_add_x86_from_lean" } ]  -- l.37 `call fe25519_add_x86_from_lean`

/-- Segment 8 of the body: the 4 instructions from source lines 38–41,
    then `call fe25519_sub_x86_from_lean`. -/
def ed25519MaddShippedSeg08 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.38 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 192,  -- l.39 `leaq 192(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32,  -- l.40 `leaq 32(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 96 ]  -- l.41 `leaq 96(%rsp), %rdx`
      callee := some "fe25519_sub_x86_from_lean" } ]  -- l.42 `call fe25519_sub_x86_from_lean`

/-- Segment 9 of the body: the 4 instructions from source lines 43–46,
    then `call fe25519_add_x86_from_lean`. -/
def ed25519MaddShippedSeg09 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.43 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 224,  -- l.44 `leaq 224(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32,  -- l.45 `leaq 32(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 96 ]  -- l.46 `leaq 96(%rsp), %rdx`
      callee := some "fe25519_add_x86_from_lean" } ]  -- l.47 `call fe25519_add_x86_from_lean`

/-- Segment 10 of the body: the 4 instructions from source lines 48–51,
    then `call fe25519_add_x86_from_lean`. -/
def ed25519MaddShippedSeg10 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.48 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 256,  -- l.49 `leaq 256(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 160,  -- l.50 `leaq 160(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 128 ]  -- l.51 `leaq 128(%rsp), %rdx`
      callee := some "fe25519_add_x86_from_lean" } ]  -- l.52 `call fe25519_add_x86_from_lean`

/-- Segment 11 of the body: the 4 instructions from source lines 53–56,
    then `call fe25519_sub_x86_from_lean`. -/
def ed25519MaddShippedSeg11 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.53 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 288,  -- l.54 `leaq 288(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 160,  -- l.55 `leaq 160(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 128 ]  -- l.56 `leaq 128(%rsp), %rdx`
      callee := some "fe25519_sub_x86_from_lean" } ]  -- l.57 `call fe25519_sub_x86_from_lean`

/-- Segment 12 of the body: the 4 instructions from source lines 58–61,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519MaddShippedSeg12 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.58 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 320,  -- l.59 `leaq 320(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 192,  -- l.60 `leaq 192(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 288 ]  -- l.61 `leaq 288(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.62 `call fe25519_mul_x86_from_lean`

/-- Segment 13 of the body: the 4 instructions from source lines 63–66,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519MaddShippedSeg13 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.63 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 352,  -- l.64 `leaq 352(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 224,  -- l.65 `leaq 224(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 256 ]  -- l.66 `leaq 256(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.67 `call fe25519_mul_x86_from_lean`

/-- Segment 14 of the body: the 4 instructions from source lines 68–71,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519MaddShippedSeg14 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.68 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 384,  -- l.69 `leaq 384(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 256,  -- l.70 `leaq 256(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 288 ]  -- l.71 `leaq 288(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.72 `call fe25519_mul_x86_from_lean`

/-- Segment 15 of the body: the 4 instructions from source lines 73–76,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519MaddShippedSeg15 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.73 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 416,  -- l.74 `leaq 416(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 192,  -- l.75 `leaq 192(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 224 ]  -- l.76 `leaq 224(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.77 `call fe25519_mul_x86_from_lean`

/-- Segment 16 of the body: the 6 instructions from source lines 78–83,
    then `call ed25519_join16_x86_from_lean`. -/
def ed25519MaddShippedSeg16 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 576,  -- l.78 `movq 576(%rsp), %r10`
          .lea "%rdi" "%rsp" "%rsp" 0 448,  -- l.79 `leaq 448(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 320,  -- l.80 `leaq 320(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 352,  -- l.81 `leaq 352(%rsp), %rdx`
          .lea "%rcx" "%rsp" "%rsp" 0 384,  -- l.82 `leaq 384(%rsp), %rcx`
          .lea "%r8" "%rsp" "%rsp" 0 416 ]  -- l.83 `leaq 416(%rsp), %r8`
      callee := some "ed25519_join16_x86_from_lean" } ]  -- l.84 `call ed25519_join16_x86_from_lean`

/-- Segment 17 of the body: the 32 instructions from source lines 85–116. -/
def ed25519MaddShippedSeg17 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r10" "%rsp" 584,  -- l.85 `movq 584(%rsp), %r10`
          .lea "%r9" "%rsp" "%rsp" 0 448,  -- l.86 `leaq 448(%rsp), %r9`
          .loadMem "%r11" "%r9" 0,  -- l.87 `movq (%r9), %r11`
          .storeMem "%r10" 0 (.reg "%r11"),  -- l.88 `movq %r11, (%r10)`
          .loadMem "%r11" "%r9" 8,  -- l.89 `movq 8(%r9), %r11`
          .storeMem "%r10" 8 (.reg "%r11"),  -- l.90 `movq %r11, 8(%r10)`
          .loadMem "%r11" "%r9" 16,  -- l.91 `movq 16(%r9), %r11`
          .storeMem "%r10" 16 (.reg "%r11"),  -- l.92 `movq %r11, 16(%r10)`
          .loadMem "%r11" "%r9" 24,  -- l.93 `movq 24(%r9), %r11`
          .storeMem "%r10" 24 (.reg "%r11"),  -- l.94 `movq %r11, 24(%r10)`
          .loadMem "%r11" "%r9" 32,  -- l.95 `movq 32(%r9), %r11`
          .storeMem "%r10" 32 (.reg "%r11"),  -- l.96 `movq %r11, 32(%r10)`
          .loadMem "%r11" "%r9" 40,  -- l.97 `movq 40(%r9), %r11`
          .storeMem "%r10" 40 (.reg "%r11"),  -- l.98 `movq %r11, 40(%r10)`
          .loadMem "%r11" "%r9" 48,  -- l.99 `movq 48(%r9), %r11`
          .storeMem "%r10" 48 (.reg "%r11"),  -- l.100 `movq %r11, 48(%r10)`
          .loadMem "%r11" "%r9" 56,  -- l.101 `movq 56(%r9), %r11`
          .storeMem "%r10" 56 (.reg "%r11"),  -- l.102 `movq %r11, 56(%r10)`
          .loadMem "%r11" "%r9" 64,  -- l.103 `movq 64(%r9), %r11`
          .storeMem "%r10" 64 (.reg "%r11"),  -- l.104 `movq %r11, 64(%r10)`
          .loadMem "%r11" "%r9" 72,  -- l.105 `movq 72(%r9), %r11`
          .storeMem "%r10" 72 (.reg "%r11"),  -- l.106 `movq %r11, 72(%r10)`
          .loadMem "%r11" "%r9" 80,  -- l.107 `movq 80(%r9), %r11`
          .storeMem "%r10" 80 (.reg "%r11"),  -- l.108 `movq %r11, 80(%r10)`
          .loadMem "%r11" "%r9" 88,  -- l.109 `movq 88(%r9), %r11`
          .storeMem "%r10" 88 (.reg "%r11"),  -- l.110 `movq %r11, 88(%r10)`
          .loadMem "%r11" "%r9" 96,  -- l.111 `movq 96(%r9), %r11`
          .storeMem "%r10" 96 (.reg "%r11"),  -- l.112 `movq %r11, 96(%r10)`
          .loadMem "%r11" "%r9" 104,  -- l.113 `movq 104(%r9), %r11`
          .storeMem "%r10" 104 (.reg "%r11"),  -- l.114 `movq %r11, 104(%r10)`
          .loadMem "%r11" "%r9" 112,  -- l.115 `movq 112(%r9), %r11`
          .storeMem "%r10" 112 (.reg "%r11") ]  -- l.116 `movq %r11, 112(%r10)`
      callee := none } ]

/-- Segment 18 of the body: the 2 instructions from source lines 117–118. -/
def ed25519MaddShippedSeg18 : List CallSeg :=
  [ { body :=
        [ .loadMem "%r11" "%r9" 120,  -- l.117 `movq 120(%r9), %r11`
          .storeMem "%r10" 120 (.reg "%r11") ]  -- l.118 `movq %r11, 120(%r10)`
      callee := none } ]

/-- Part 1 of the body: segments 1–16. -/
def ed25519MaddShippedPart01 : List CallSeg :=
  ed25519MaddShippedSeg01 ++ ed25519MaddShippedSeg02 ++ ed25519MaddShippedSeg03 ++
  ed25519MaddShippedSeg04 ++ ed25519MaddShippedSeg05 ++ ed25519MaddShippedSeg06 ++
  ed25519MaddShippedSeg07 ++ ed25519MaddShippedSeg08 ++ ed25519MaddShippedSeg09 ++
  ed25519MaddShippedSeg10 ++ ed25519MaddShippedSeg11 ++ ed25519MaddShippedSeg12 ++
  ed25519MaddShippedSeg13 ++ ed25519MaddShippedSeg14 ++ ed25519MaddShippedSeg15 ++
  ed25519MaddShippedSeg16

/-- Part 1 has 64 instructions. -/
theorem ed25519MaddShippedPart01_instrs :
    (CallSeg.instrs ed25519MaddShippedPart01).length = 64 := by
  unfold ed25519MaddShippedPart01
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 1 makes 15 calls. -/
theorem ed25519MaddShippedPart01_calls :
    (CallSeg.callees ed25519MaddShippedPart01).length = 15 := by
  unfold ed25519MaddShippedPart01
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 2 of the body: segments 17–18. -/
def ed25519MaddShippedPart02 : List CallSeg :=
  ed25519MaddShippedSeg17 ++ ed25519MaddShippedSeg18

/-- Part 2 has 34 instructions. -/
theorem ed25519MaddShippedPart02_instrs :
    (CallSeg.instrs ed25519MaddShippedPart02).length = 34 := by
  unfold ed25519MaddShippedPart02
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 2 makes 0 calls. -/
theorem ed25519MaddShippedPart02_calls :
    (CallSeg.callees ed25519MaddShippedPart02).length = 0 := by
  unfold ed25519MaddShippedPart02
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- The body of `ed25519_madd_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 18 segments,
    grouped in 2 parts.
    Each segment is a run of instructions followed by the `call` that ends it, if any. -/
def ed25519MaddShippedBlock : List CallSeg :=
  ed25519MaddShippedPart01 ++ ed25519MaddShippedPart02

/-- The block has 98 instructions; the count of each part is a lemma above. -/
theorem ed25519MaddShippedBlock_instrs :
    (CallSeg.instrs ed25519MaddShippedBlock).length = 98 := by
  unfold ed25519MaddShippedBlock
  simp only [CallSeg.instrs_append, List.length_append, ed25519MaddShippedPart01_instrs,
    ed25519MaddShippedPart02_instrs]

/-- The block makes 15 calls; the count of each part is a lemma above. -/
theorem ed25519MaddShippedBlock_calls :
    (CallSeg.callees ed25519MaddShippedBlock).length = 15 := by
  unfold ed25519MaddShippedBlock
  simp only [CallSeg.callees_append, List.length_append, ed25519MaddShippedPart01_calls,
    ed25519MaddShippedPart02_calls]

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519MaddShipped
