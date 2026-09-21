/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.CallSeg

/-!
# `ed25519_invert_x86_from_lean` from the owned backend's output as a `JInstr 64` block

`ed25519InvertShippedBlock` is the body of the function
`ed25519_invert_x86_from_lean` in an x86-64 AT&T file printed by CatCrypt's owned
backend, translated instruction by instruction. The file's producer is recorded in
`PROVENANCE.md` next to it, where one exists.

## Provenance

* Source: `crates/catcrypt-ed25519/asm/ed25519_invert_x86_from_lean.s` in the
  `SSProve-lean` repository at commit `b294647590404f72dd82b5404e326511f3c055eb`
  (tracked and unchanged at that commit), file SHA-256
  `41f039989b89ed43973e5eeb0255708889484d659e2f7aa47e72a0cc912c5999`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 5 frame instructions,
  each checked by the importer: `pushq` of `%rbx` on entry and the `popq` sequence
  in reverse order on exit; the stack allocation `leaq -176(%rsp), %rsp` and its
  release `leaq 176(%rsp), %rsp`; `ret`.
* `ed25519InvertShippedPrologue` and `ed25519InvertShippedEpilogue` are the frame
  instructions before and after the block, `ret` excluded: each `pushq r` as `lea
  "%rsp" "%rsp" "%rsp" 0 (-8)` followed by `storeMem "%rsp" 0 (.reg r)`, each `popq
  r` as `loadMem r "%rsp" 0` followed by `lea "%rsp" "%rsp" "%rsp" 0 8`, and the
  stack allocation and its release as the instruction the text contains. `lea`
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
  off` is `b + off`; `JInstr.lea` has no index-free form (538 instructions).
* The function makes 265 calls: `fe25519_sqr_x86_from_lean` 254,
  `fe25519_mul_x86_from_lean` 11. `JInstr` has no call instruction, so the block is
  a `List CallSeg` (`Ascent.Imported.CallSeg`): runs of instructions, each followed
  by the call that ends it, if any. The effect of a call is outside `JasminModel`.

The block has 544 instructions. Source instructions by mnemonic: `leaq` 538, `call`
265, `movq` 6.

## Main definitions

* `ed25519InvertShippedSeg001` … `ed25519InvertShippedSeg266`: the block in 266
  segments, each a literal `List CallSeg`. A segment ends after a call, after the
  entry run of `%rsp` stores, before the exit run of `%rsp` loads, and after 32
  instructions.
* `ed25519InvertShippedPart01` … `ed25519InvertShippedPart17`: the segments in 17
  parts of at most 16 consecutive segments, each with lemmas giving its instruction
  count and its call count.
* `ed25519InvertShippedBlock`: the block, the concatenation of the parts.
* `ed25519InvertShippedPrologue`, `ed25519InvertShippedEpilogue`: the frame
  instructions before and after the block.

## Main results

* `ed25519InvertShippedBlock_instrs`: the block has 544 instructions.
* `ed25519InvertShippedBlock_calls`: the block makes 265 calls.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519InvertShipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 4 instructions from source lines 7–10,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg001 : List CallSeg :=
  [ { body :=
        [ .mov "%rbx" (.reg "%rsi"),  -- l.7 `movq %rsi, %rbx`
          .storeMem "%rsp" 128 (.reg "%rdi"),  -- l.8 `movq %rdi, 128(%rsp)`
          .lea "%rdi" "%rsp" "%rsp" 0 0,  -- l.9 `leaq (%rsp), %rdi`
          .mov "%rsi" (.reg "%rbx") ]  -- l.10 `movq %rbx, %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.11 `call fe25519_sqr_x86_from_lean`

/-- Segment 2 of the body: the 2 instructions from source lines 12–13,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg002 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.12 `leaq 32(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 0 ]  -- l.13 `leaq (%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.14 `call fe25519_sqr_x86_from_lean`

/-- Segment 3 of the body: the 2 instructions from source lines 15–16,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg003 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.15 `leaq 32(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32 ]  -- l.16 `leaq 32(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.17 `call fe25519_sqr_x86_from_lean`

/-- Segment 4 of the body: the 3 instructions from source lines 18–20,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519InvertShippedSeg004 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.18 `leaq 32(%rsp), %rdi`
          .mov "%rsi" (.reg "%rbx"),  -- l.19 `movq %rbx, %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 32 ]  -- l.20 `leaq 32(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.21 `call fe25519_mul_x86_from_lean`

/-- Segment 5 of the body: the 3 instructions from source lines 22–24,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519InvertShippedSeg005 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 0,  -- l.22 `leaq (%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 0,  -- l.23 `leaq (%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 32 ]  -- l.24 `leaq 32(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.25 `call fe25519_mul_x86_from_lean`

/-- Segment 6 of the body: the 2 instructions from source lines 26–27,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg006 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.26 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 0 ]  -- l.27 `leaq (%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.28 `call fe25519_sqr_x86_from_lean`

/-- Segment 7 of the body: the 3 instructions from source lines 29–31,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519InvertShippedSeg007 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.29 `leaq 32(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32,  -- l.30 `leaq 32(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 64 ]  -- l.31 `leaq 64(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.32 `call fe25519_mul_x86_from_lean`

/-- Segment 8 of the body: the 2 instructions from source lines 33–34,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg008 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.33 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32 ]  -- l.34 `leaq 32(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.35 `call fe25519_sqr_x86_from_lean`

/-- Segment 9 of the body: the 2 instructions from source lines 36–37,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg009 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.36 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.37 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.38 `call fe25519_sqr_x86_from_lean`

/-- Segment 10 of the body: the 2 instructions from source lines 39–40,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg010 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.39 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.40 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.41 `call fe25519_sqr_x86_from_lean`

/-- Segment 11 of the body: the 2 instructions from source lines 42–43,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg011 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.42 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.43 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.44 `call fe25519_sqr_x86_from_lean`

/-- Segment 12 of the body: the 2 instructions from source lines 45–46,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg012 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.45 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.46 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.47 `call fe25519_sqr_x86_from_lean`

/-- Segment 13 of the body: the 3 instructions from source lines 48–50,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519InvertShippedSeg013 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.48 `leaq 32(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64,  -- l.49 `leaq 64(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 32 ]  -- l.50 `leaq 32(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.51 `call fe25519_mul_x86_from_lean`

/-- Segment 14 of the body: the 2 instructions from source lines 52–53,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg014 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.52 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32 ]  -- l.53 `leaq 32(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.54 `call fe25519_sqr_x86_from_lean`

/-- Segment 15 of the body: the 2 instructions from source lines 55–56,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg015 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.55 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.56 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.57 `call fe25519_sqr_x86_from_lean`

/-- Segment 16 of the body: the 2 instructions from source lines 58–59,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg016 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.58 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.59 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.60 `call fe25519_sqr_x86_from_lean`

/-- Segment 17 of the body: the 2 instructions from source lines 61–62,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg017 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.61 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.62 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.63 `call fe25519_sqr_x86_from_lean`

/-- Segment 18 of the body: the 2 instructions from source lines 64–65,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg018 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.64 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.65 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.66 `call fe25519_sqr_x86_from_lean`

/-- Segment 19 of the body: the 2 instructions from source lines 67–68,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg019 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.67 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.68 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.69 `call fe25519_sqr_x86_from_lean`

/-- Segment 20 of the body: the 2 instructions from source lines 70–71,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg020 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.70 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.71 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.72 `call fe25519_sqr_x86_from_lean`

/-- Segment 21 of the body: the 2 instructions from source lines 73–74,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg021 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.73 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.74 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.75 `call fe25519_sqr_x86_from_lean`

/-- Segment 22 of the body: the 2 instructions from source lines 76–77,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg022 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.76 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.77 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.78 `call fe25519_sqr_x86_from_lean`

/-- Segment 23 of the body: the 2 instructions from source lines 79–80,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg023 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.79 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.80 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.81 `call fe25519_sqr_x86_from_lean`

/-- Segment 24 of the body: the 3 instructions from source lines 82–84,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519InvertShippedSeg024 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.82 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64,  -- l.83 `leaq 64(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 32 ]  -- l.84 `leaq 32(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.85 `call fe25519_mul_x86_from_lean`

/-- Segment 25 of the body: the 2 instructions from source lines 86–87,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg025 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.86 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.87 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.88 `call fe25519_sqr_x86_from_lean`

/-- Segment 26 of the body: the 2 instructions from source lines 89–90,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg026 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.89 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.90 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.91 `call fe25519_sqr_x86_from_lean`

/-- Segment 27 of the body: the 2 instructions from source lines 92–93,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg027 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.92 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.93 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.94 `call fe25519_sqr_x86_from_lean`

/-- Segment 28 of the body: the 2 instructions from source lines 95–96,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg028 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.95 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.96 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.97 `call fe25519_sqr_x86_from_lean`

/-- Segment 29 of the body: the 2 instructions from source lines 98–99,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg029 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.98 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.99 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.100 `call fe25519_sqr_x86_from_lean`

/-- Segment 30 of the body: the 2 instructions from source lines 101–102,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg030 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.101 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.102 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.103 `call fe25519_sqr_x86_from_lean`

/-- Segment 31 of the body: the 2 instructions from source lines 104–105,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg031 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.104 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.105 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.106 `call fe25519_sqr_x86_from_lean`

/-- Segment 32 of the body: the 2 instructions from source lines 107–108,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg032 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.107 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.108 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.109 `call fe25519_sqr_x86_from_lean`

/-- Segment 33 of the body: the 2 instructions from source lines 110–111,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg033 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.110 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.111 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.112 `call fe25519_sqr_x86_from_lean`

/-- Segment 34 of the body: the 2 instructions from source lines 113–114,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg034 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.113 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.114 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.115 `call fe25519_sqr_x86_from_lean`

/-- Segment 35 of the body: the 2 instructions from source lines 116–117,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg035 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.116 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.117 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.118 `call fe25519_sqr_x86_from_lean`

/-- Segment 36 of the body: the 2 instructions from source lines 119–120,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg036 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.119 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.120 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.121 `call fe25519_sqr_x86_from_lean`

/-- Segment 37 of the body: the 2 instructions from source lines 122–123,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg037 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.122 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.123 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.124 `call fe25519_sqr_x86_from_lean`

/-- Segment 38 of the body: the 2 instructions from source lines 125–126,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg038 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.125 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.126 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.127 `call fe25519_sqr_x86_from_lean`

/-- Segment 39 of the body: the 2 instructions from source lines 128–129,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg039 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.128 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.129 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.130 `call fe25519_sqr_x86_from_lean`

/-- Segment 40 of the body: the 2 instructions from source lines 131–132,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg040 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.131 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.132 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.133 `call fe25519_sqr_x86_from_lean`

/-- Segment 41 of the body: the 2 instructions from source lines 134–135,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg041 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.134 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.135 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.136 `call fe25519_sqr_x86_from_lean`

/-- Segment 42 of the body: the 2 instructions from source lines 137–138,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg042 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.137 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.138 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.139 `call fe25519_sqr_x86_from_lean`

/-- Segment 43 of the body: the 2 instructions from source lines 140–141,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg043 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.140 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.141 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.142 `call fe25519_sqr_x86_from_lean`

/-- Segment 44 of the body: the 2 instructions from source lines 143–144,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg044 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.143 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.144 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.145 `call fe25519_sqr_x86_from_lean`

/-- Segment 45 of the body: the 3 instructions from source lines 146–148,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519InvertShippedSeg045 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.146 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96,  -- l.147 `leaq 96(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 64 ]  -- l.148 `leaq 64(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.149 `call fe25519_mul_x86_from_lean`

/-- Segment 46 of the body: the 2 instructions from source lines 150–151,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg046 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.150 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.151 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.152 `call fe25519_sqr_x86_from_lean`

/-- Segment 47 of the body: the 2 instructions from source lines 153–154,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg047 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.153 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.154 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.155 `call fe25519_sqr_x86_from_lean`

/-- Segment 48 of the body: the 2 instructions from source lines 156–157,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg048 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.156 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.157 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.158 `call fe25519_sqr_x86_from_lean`

/-- Segment 49 of the body: the 2 instructions from source lines 159–160,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg049 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.159 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.160 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.161 `call fe25519_sqr_x86_from_lean`

/-- Segment 50 of the body: the 2 instructions from source lines 162–163,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg050 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.162 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.163 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.164 `call fe25519_sqr_x86_from_lean`

/-- Segment 51 of the body: the 2 instructions from source lines 165–166,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg051 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.165 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.166 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.167 `call fe25519_sqr_x86_from_lean`

/-- Segment 52 of the body: the 2 instructions from source lines 168–169,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg052 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.168 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.169 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.170 `call fe25519_sqr_x86_from_lean`

/-- Segment 53 of the body: the 2 instructions from source lines 171–172,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg053 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.171 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.172 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.173 `call fe25519_sqr_x86_from_lean`

/-- Segment 54 of the body: the 2 instructions from source lines 174–175,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg054 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.174 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.175 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.176 `call fe25519_sqr_x86_from_lean`

/-- Segment 55 of the body: the 2 instructions from source lines 177–178,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg055 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.177 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.178 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.179 `call fe25519_sqr_x86_from_lean`

/-- Segment 56 of the body: the 3 instructions from source lines 180–182,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519InvertShippedSeg056 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.180 `leaq 32(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64,  -- l.181 `leaq 64(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 32 ]  -- l.182 `leaq 32(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.183 `call fe25519_mul_x86_from_lean`

/-- Segment 57 of the body: the 2 instructions from source lines 184–185,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg057 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.184 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32 ]  -- l.185 `leaq 32(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.186 `call fe25519_sqr_x86_from_lean`

/-- Segment 58 of the body: the 2 instructions from source lines 187–188,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg058 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.187 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.188 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.189 `call fe25519_sqr_x86_from_lean`

/-- Segment 59 of the body: the 2 instructions from source lines 190–191,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg059 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.190 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.191 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.192 `call fe25519_sqr_x86_from_lean`

/-- Segment 60 of the body: the 2 instructions from source lines 193–194,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg060 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.193 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.194 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.195 `call fe25519_sqr_x86_from_lean`

/-- Segment 61 of the body: the 2 instructions from source lines 196–197,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg061 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.196 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.197 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.198 `call fe25519_sqr_x86_from_lean`

/-- Segment 62 of the body: the 2 instructions from source lines 199–200,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg062 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.199 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.200 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.201 `call fe25519_sqr_x86_from_lean`

/-- Segment 63 of the body: the 2 instructions from source lines 202–203,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg063 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.202 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.203 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.204 `call fe25519_sqr_x86_from_lean`

/-- Segment 64 of the body: the 2 instructions from source lines 205–206,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg064 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.205 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.206 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.207 `call fe25519_sqr_x86_from_lean`

/-- Segment 65 of the body: the 2 instructions from source lines 208–209,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg065 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.208 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.209 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.210 `call fe25519_sqr_x86_from_lean`

/-- Segment 66 of the body: the 2 instructions from source lines 211–212,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg066 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.211 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.212 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.213 `call fe25519_sqr_x86_from_lean`

/-- Segment 67 of the body: the 2 instructions from source lines 214–215,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg067 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.214 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.215 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.216 `call fe25519_sqr_x86_from_lean`

/-- Segment 68 of the body: the 2 instructions from source lines 217–218,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg068 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.217 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.218 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.219 `call fe25519_sqr_x86_from_lean`

/-- Segment 69 of the body: the 2 instructions from source lines 220–221,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg069 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.220 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.221 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.222 `call fe25519_sqr_x86_from_lean`

/-- Segment 70 of the body: the 2 instructions from source lines 223–224,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg070 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.223 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.224 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.225 `call fe25519_sqr_x86_from_lean`

/-- Segment 71 of the body: the 2 instructions from source lines 226–227,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg071 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.226 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.227 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.228 `call fe25519_sqr_x86_from_lean`

/-- Segment 72 of the body: the 2 instructions from source lines 229–230,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg072 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.229 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.230 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.231 `call fe25519_sqr_x86_from_lean`

/-- Segment 73 of the body: the 2 instructions from source lines 232–233,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg073 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.232 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.233 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.234 `call fe25519_sqr_x86_from_lean`

/-- Segment 74 of the body: the 2 instructions from source lines 235–236,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg074 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.235 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.236 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.237 `call fe25519_sqr_x86_from_lean`

/-- Segment 75 of the body: the 2 instructions from source lines 238–239,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg075 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.238 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.239 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.240 `call fe25519_sqr_x86_from_lean`

/-- Segment 76 of the body: the 2 instructions from source lines 241–242,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg076 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.241 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.242 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.243 `call fe25519_sqr_x86_from_lean`

/-- Segment 77 of the body: the 2 instructions from source lines 244–245,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg077 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.244 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.245 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.246 `call fe25519_sqr_x86_from_lean`

/-- Segment 78 of the body: the 2 instructions from source lines 247–248,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg078 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.247 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.248 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.249 `call fe25519_sqr_x86_from_lean`

/-- Segment 79 of the body: the 2 instructions from source lines 250–251,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg079 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.250 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.251 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.252 `call fe25519_sqr_x86_from_lean`

/-- Segment 80 of the body: the 2 instructions from source lines 253–254,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg080 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.253 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.254 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.255 `call fe25519_sqr_x86_from_lean`

/-- Segment 81 of the body: the 2 instructions from source lines 256–257,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg081 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.256 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.257 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.258 `call fe25519_sqr_x86_from_lean`

/-- Segment 82 of the body: the 2 instructions from source lines 259–260,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg082 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.259 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.260 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.261 `call fe25519_sqr_x86_from_lean`

/-- Segment 83 of the body: the 2 instructions from source lines 262–263,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg083 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.262 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.263 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.264 `call fe25519_sqr_x86_from_lean`

/-- Segment 84 of the body: the 2 instructions from source lines 265–266,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg084 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.265 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.266 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.267 `call fe25519_sqr_x86_from_lean`

/-- Segment 85 of the body: the 2 instructions from source lines 268–269,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg085 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.268 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.269 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.270 `call fe25519_sqr_x86_from_lean`

/-- Segment 86 of the body: the 2 instructions from source lines 271–272,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg086 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.271 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.272 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.273 `call fe25519_sqr_x86_from_lean`

/-- Segment 87 of the body: the 2 instructions from source lines 274–275,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg087 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.274 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.275 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.276 `call fe25519_sqr_x86_from_lean`

/-- Segment 88 of the body: the 2 instructions from source lines 277–278,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg088 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.277 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.278 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.279 `call fe25519_sqr_x86_from_lean`

/-- Segment 89 of the body: the 2 instructions from source lines 280–281,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg089 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.280 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.281 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.282 `call fe25519_sqr_x86_from_lean`

/-- Segment 90 of the body: the 2 instructions from source lines 283–284,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg090 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.283 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.284 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.285 `call fe25519_sqr_x86_from_lean`

/-- Segment 91 of the body: the 2 instructions from source lines 286–287,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg091 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.286 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.287 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.288 `call fe25519_sqr_x86_from_lean`

/-- Segment 92 of the body: the 2 instructions from source lines 289–290,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg092 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.289 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.290 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.291 `call fe25519_sqr_x86_from_lean`

/-- Segment 93 of the body: the 2 instructions from source lines 292–293,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg093 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.292 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.293 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.294 `call fe25519_sqr_x86_from_lean`

/-- Segment 94 of the body: the 2 instructions from source lines 295–296,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg094 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.295 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.296 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.297 `call fe25519_sqr_x86_from_lean`

/-- Segment 95 of the body: the 2 instructions from source lines 298–299,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg095 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.298 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.299 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.300 `call fe25519_sqr_x86_from_lean`

/-- Segment 96 of the body: the 2 instructions from source lines 301–302,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg096 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.301 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.302 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.303 `call fe25519_sqr_x86_from_lean`

/-- Segment 97 of the body: the 2 instructions from source lines 304–305,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg097 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.304 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.305 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.306 `call fe25519_sqr_x86_from_lean`

/-- Segment 98 of the body: the 2 instructions from source lines 307–308,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg098 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.307 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.308 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.309 `call fe25519_sqr_x86_from_lean`

/-- Segment 99 of the body: the 2 instructions from source lines 310–311,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg099 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.310 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.311 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.312 `call fe25519_sqr_x86_from_lean`

/-- Segment 100 of the body: the 2 instructions from source lines 313–314,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg100 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.313 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.314 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.315 `call fe25519_sqr_x86_from_lean`

/-- Segment 101 of the body: the 2 instructions from source lines 316–317,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg101 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.316 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.317 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.318 `call fe25519_sqr_x86_from_lean`

/-- Segment 102 of the body: the 2 instructions from source lines 319–320,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg102 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.319 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.320 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.321 `call fe25519_sqr_x86_from_lean`

/-- Segment 103 of the body: the 2 instructions from source lines 322–323,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg103 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.322 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.323 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.324 `call fe25519_sqr_x86_from_lean`

/-- Segment 104 of the body: the 2 instructions from source lines 325–326,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg104 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.325 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.326 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.327 `call fe25519_sqr_x86_from_lean`

/-- Segment 105 of the body: the 2 instructions from source lines 328–329,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg105 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.328 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.329 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.330 `call fe25519_sqr_x86_from_lean`

/-- Segment 106 of the body: the 2 instructions from source lines 331–332,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg106 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.331 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.332 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.333 `call fe25519_sqr_x86_from_lean`

/-- Segment 107 of the body: the 3 instructions from source lines 334–336,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519InvertShippedSeg107 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.334 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64,  -- l.335 `leaq 64(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 32 ]  -- l.336 `leaq 32(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.337 `call fe25519_mul_x86_from_lean`

/-- Segment 108 of the body: the 2 instructions from source lines 338–339,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg108 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.338 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.339 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.340 `call fe25519_sqr_x86_from_lean`

/-- Segment 109 of the body: the 2 instructions from source lines 341–342,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg109 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.341 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.342 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.343 `call fe25519_sqr_x86_from_lean`

/-- Segment 110 of the body: the 2 instructions from source lines 344–345,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg110 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.344 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.345 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.346 `call fe25519_sqr_x86_from_lean`

/-- Segment 111 of the body: the 2 instructions from source lines 347–348,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg111 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.347 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.348 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.349 `call fe25519_sqr_x86_from_lean`

/-- Segment 112 of the body: the 2 instructions from source lines 350–351,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg112 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.350 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.351 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.352 `call fe25519_sqr_x86_from_lean`

/-- Segment 113 of the body: the 2 instructions from source lines 353–354,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg113 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.353 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.354 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.355 `call fe25519_sqr_x86_from_lean`

/-- Segment 114 of the body: the 2 instructions from source lines 356–357,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg114 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.356 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.357 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.358 `call fe25519_sqr_x86_from_lean`

/-- Segment 115 of the body: the 2 instructions from source lines 359–360,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg115 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.359 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.360 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.361 `call fe25519_sqr_x86_from_lean`

/-- Segment 116 of the body: the 2 instructions from source lines 362–363,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg116 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.362 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.363 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.364 `call fe25519_sqr_x86_from_lean`

/-- Segment 117 of the body: the 2 instructions from source lines 365–366,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg117 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.365 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.366 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.367 `call fe25519_sqr_x86_from_lean`

/-- Segment 118 of the body: the 2 instructions from source lines 368–369,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg118 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.368 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.369 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.370 `call fe25519_sqr_x86_from_lean`

/-- Segment 119 of the body: the 2 instructions from source lines 371–372,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg119 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.371 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.372 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.373 `call fe25519_sqr_x86_from_lean`

/-- Segment 120 of the body: the 2 instructions from source lines 374–375,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg120 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.374 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.375 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.376 `call fe25519_sqr_x86_from_lean`

/-- Segment 121 of the body: the 2 instructions from source lines 377–378,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg121 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.377 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.378 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.379 `call fe25519_sqr_x86_from_lean`

/-- Segment 122 of the body: the 2 instructions from source lines 380–381,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg122 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.380 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.381 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.382 `call fe25519_sqr_x86_from_lean`

/-- Segment 123 of the body: the 2 instructions from source lines 383–384,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg123 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.383 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.384 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.385 `call fe25519_sqr_x86_from_lean`

/-- Segment 124 of the body: the 2 instructions from source lines 386–387,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg124 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.386 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.387 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.388 `call fe25519_sqr_x86_from_lean`

/-- Segment 125 of the body: the 2 instructions from source lines 389–390,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg125 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.389 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.390 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.391 `call fe25519_sqr_x86_from_lean`

/-- Segment 126 of the body: the 2 instructions from source lines 392–393,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg126 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.392 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.393 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.394 `call fe25519_sqr_x86_from_lean`

/-- Segment 127 of the body: the 2 instructions from source lines 395–396,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg127 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.395 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.396 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.397 `call fe25519_sqr_x86_from_lean`

/-- Segment 128 of the body: the 2 instructions from source lines 398–399,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg128 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.398 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.399 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.400 `call fe25519_sqr_x86_from_lean`

/-- Segment 129 of the body: the 2 instructions from source lines 401–402,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg129 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.401 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.402 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.403 `call fe25519_sqr_x86_from_lean`

/-- Segment 130 of the body: the 2 instructions from source lines 404–405,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg130 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.404 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.405 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.406 `call fe25519_sqr_x86_from_lean`

/-- Segment 131 of the body: the 2 instructions from source lines 407–408,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg131 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.407 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.408 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.409 `call fe25519_sqr_x86_from_lean`

/-- Segment 132 of the body: the 2 instructions from source lines 410–411,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg132 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.410 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.411 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.412 `call fe25519_sqr_x86_from_lean`

/-- Segment 133 of the body: the 2 instructions from source lines 413–414,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg133 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.413 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.414 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.415 `call fe25519_sqr_x86_from_lean`

/-- Segment 134 of the body: the 2 instructions from source lines 416–417,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg134 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.416 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.417 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.418 `call fe25519_sqr_x86_from_lean`

/-- Segment 135 of the body: the 2 instructions from source lines 419–420,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg135 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.419 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.420 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.421 `call fe25519_sqr_x86_from_lean`

/-- Segment 136 of the body: the 2 instructions from source lines 422–423,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg136 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.422 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.423 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.424 `call fe25519_sqr_x86_from_lean`

/-- Segment 137 of the body: the 2 instructions from source lines 425–426,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg137 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.425 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.426 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.427 `call fe25519_sqr_x86_from_lean`

/-- Segment 138 of the body: the 2 instructions from source lines 428–429,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg138 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.428 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.429 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.430 `call fe25519_sqr_x86_from_lean`

/-- Segment 139 of the body: the 2 instructions from source lines 431–432,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg139 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.431 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.432 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.433 `call fe25519_sqr_x86_from_lean`

/-- Segment 140 of the body: the 2 instructions from source lines 434–435,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg140 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.434 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.435 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.436 `call fe25519_sqr_x86_from_lean`

/-- Segment 141 of the body: the 2 instructions from source lines 437–438,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg141 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.437 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.438 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.439 `call fe25519_sqr_x86_from_lean`

/-- Segment 142 of the body: the 2 instructions from source lines 440–441,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg142 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.440 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.441 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.442 `call fe25519_sqr_x86_from_lean`

/-- Segment 143 of the body: the 2 instructions from source lines 443–444,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg143 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.443 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.444 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.445 `call fe25519_sqr_x86_from_lean`

/-- Segment 144 of the body: the 2 instructions from source lines 446–447,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg144 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.446 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.447 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.448 `call fe25519_sqr_x86_from_lean`

/-- Segment 145 of the body: the 2 instructions from source lines 449–450,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg145 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.449 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.450 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.451 `call fe25519_sqr_x86_from_lean`

/-- Segment 146 of the body: the 2 instructions from source lines 452–453,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg146 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.452 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.453 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.454 `call fe25519_sqr_x86_from_lean`

/-- Segment 147 of the body: the 2 instructions from source lines 455–456,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg147 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.455 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.456 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.457 `call fe25519_sqr_x86_from_lean`

/-- Segment 148 of the body: the 2 instructions from source lines 458–459,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg148 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.458 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.459 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.460 `call fe25519_sqr_x86_from_lean`

/-- Segment 149 of the body: the 2 instructions from source lines 461–462,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg149 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.461 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.462 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.463 `call fe25519_sqr_x86_from_lean`

/-- Segment 150 of the body: the 2 instructions from source lines 464–465,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg150 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.464 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.465 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.466 `call fe25519_sqr_x86_from_lean`

/-- Segment 151 of the body: the 2 instructions from source lines 467–468,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg151 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.467 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.468 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.469 `call fe25519_sqr_x86_from_lean`

/-- Segment 152 of the body: the 2 instructions from source lines 470–471,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg152 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.470 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.471 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.472 `call fe25519_sqr_x86_from_lean`

/-- Segment 153 of the body: the 2 instructions from source lines 473–474,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg153 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.473 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.474 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.475 `call fe25519_sqr_x86_from_lean`

/-- Segment 154 of the body: the 2 instructions from source lines 476–477,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg154 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.476 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.477 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.478 `call fe25519_sqr_x86_from_lean`

/-- Segment 155 of the body: the 2 instructions from source lines 479–480,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg155 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.479 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.480 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.481 `call fe25519_sqr_x86_from_lean`

/-- Segment 156 of the body: the 2 instructions from source lines 482–483,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg156 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.482 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.483 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.484 `call fe25519_sqr_x86_from_lean`

/-- Segment 157 of the body: the 2 instructions from source lines 485–486,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg157 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.485 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.486 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.487 `call fe25519_sqr_x86_from_lean`

/-- Segment 158 of the body: the 2 instructions from source lines 488–489,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg158 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.488 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.489 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.490 `call fe25519_sqr_x86_from_lean`

/-- Segment 159 of the body: the 2 instructions from source lines 491–492,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg159 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.491 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.492 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.493 `call fe25519_sqr_x86_from_lean`

/-- Segment 160 of the body: the 2 instructions from source lines 494–495,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg160 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.494 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.495 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.496 `call fe25519_sqr_x86_from_lean`

/-- Segment 161 of the body: the 2 instructions from source lines 497–498,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg161 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.497 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.498 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.499 `call fe25519_sqr_x86_from_lean`

/-- Segment 162 of the body: the 2 instructions from source lines 500–501,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg162 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.500 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.501 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.502 `call fe25519_sqr_x86_from_lean`

/-- Segment 163 of the body: the 2 instructions from source lines 503–504,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg163 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.503 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.504 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.505 `call fe25519_sqr_x86_from_lean`

/-- Segment 164 of the body: the 2 instructions from source lines 506–507,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg164 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.506 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.507 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.508 `call fe25519_sqr_x86_from_lean`

/-- Segment 165 of the body: the 2 instructions from source lines 509–510,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg165 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.509 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.510 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.511 `call fe25519_sqr_x86_from_lean`

/-- Segment 166 of the body: the 2 instructions from source lines 512–513,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg166 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.512 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.513 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.514 `call fe25519_sqr_x86_from_lean`

/-- Segment 167 of the body: the 2 instructions from source lines 515–516,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg167 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.515 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.516 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.517 `call fe25519_sqr_x86_from_lean`

/-- Segment 168 of the body: the 2 instructions from source lines 518–519,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg168 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.518 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.519 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.520 `call fe25519_sqr_x86_from_lean`

/-- Segment 169 of the body: the 2 instructions from source lines 521–522,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg169 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.521 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.522 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.523 `call fe25519_sqr_x86_from_lean`

/-- Segment 170 of the body: the 2 instructions from source lines 524–525,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg170 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.524 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.525 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.526 `call fe25519_sqr_x86_from_lean`

/-- Segment 171 of the body: the 2 instructions from source lines 527–528,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg171 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.527 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.528 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.529 `call fe25519_sqr_x86_from_lean`

/-- Segment 172 of the body: the 2 instructions from source lines 530–531,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg172 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.530 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.531 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.532 `call fe25519_sqr_x86_from_lean`

/-- Segment 173 of the body: the 2 instructions from source lines 533–534,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg173 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.533 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.534 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.535 `call fe25519_sqr_x86_from_lean`

/-- Segment 174 of the body: the 2 instructions from source lines 536–537,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg174 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.536 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.537 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.538 `call fe25519_sqr_x86_from_lean`

/-- Segment 175 of the body: the 2 instructions from source lines 539–540,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg175 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.539 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.540 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.541 `call fe25519_sqr_x86_from_lean`

/-- Segment 176 of the body: the 2 instructions from source lines 542–543,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg176 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.542 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.543 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.544 `call fe25519_sqr_x86_from_lean`

/-- Segment 177 of the body: the 2 instructions from source lines 545–546,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg177 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.545 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.546 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.547 `call fe25519_sqr_x86_from_lean`

/-- Segment 178 of the body: the 2 instructions from source lines 548–549,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg178 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.548 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.549 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.550 `call fe25519_sqr_x86_from_lean`

/-- Segment 179 of the body: the 2 instructions from source lines 551–552,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg179 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.551 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.552 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.553 `call fe25519_sqr_x86_from_lean`

/-- Segment 180 of the body: the 2 instructions from source lines 554–555,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg180 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.554 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.555 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.556 `call fe25519_sqr_x86_from_lean`

/-- Segment 181 of the body: the 2 instructions from source lines 557–558,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg181 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.557 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.558 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.559 `call fe25519_sqr_x86_from_lean`

/-- Segment 182 of the body: the 2 instructions from source lines 560–561,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg182 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.560 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.561 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.562 `call fe25519_sqr_x86_from_lean`

/-- Segment 183 of the body: the 2 instructions from source lines 563–564,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg183 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.563 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.564 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.565 `call fe25519_sqr_x86_from_lean`

/-- Segment 184 of the body: the 2 instructions from source lines 566–567,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg184 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.566 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.567 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.568 `call fe25519_sqr_x86_from_lean`

/-- Segment 185 of the body: the 2 instructions from source lines 569–570,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg185 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.569 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.570 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.571 `call fe25519_sqr_x86_from_lean`

/-- Segment 186 of the body: the 2 instructions from source lines 572–573,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg186 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.572 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.573 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.574 `call fe25519_sqr_x86_from_lean`

/-- Segment 187 of the body: the 2 instructions from source lines 575–576,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg187 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.575 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.576 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.577 `call fe25519_sqr_x86_from_lean`

/-- Segment 188 of the body: the 2 instructions from source lines 578–579,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg188 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.578 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.579 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.580 `call fe25519_sqr_x86_from_lean`

/-- Segment 189 of the body: the 2 instructions from source lines 581–582,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg189 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.581 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.582 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.583 `call fe25519_sqr_x86_from_lean`

/-- Segment 190 of the body: the 2 instructions from source lines 584–585,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg190 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.584 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.585 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.586 `call fe25519_sqr_x86_from_lean`

/-- Segment 191 of the body: the 2 instructions from source lines 587–588,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg191 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.587 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.588 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.589 `call fe25519_sqr_x86_from_lean`

/-- Segment 192 of the body: the 2 instructions from source lines 590–591,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg192 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.590 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.591 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.592 `call fe25519_sqr_x86_from_lean`

/-- Segment 193 of the body: the 2 instructions from source lines 593–594,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg193 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.593 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.594 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.595 `call fe25519_sqr_x86_from_lean`

/-- Segment 194 of the body: the 2 instructions from source lines 596–597,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg194 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.596 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.597 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.598 `call fe25519_sqr_x86_from_lean`

/-- Segment 195 of the body: the 2 instructions from source lines 599–600,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg195 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.599 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.600 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.601 `call fe25519_sqr_x86_from_lean`

/-- Segment 196 of the body: the 2 instructions from source lines 602–603,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg196 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.602 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.603 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.604 `call fe25519_sqr_x86_from_lean`

/-- Segment 197 of the body: the 2 instructions from source lines 605–606,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg197 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.605 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.606 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.607 `call fe25519_sqr_x86_from_lean`

/-- Segment 198 of the body: the 2 instructions from source lines 608–609,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg198 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.608 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.609 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.610 `call fe25519_sqr_x86_from_lean`

/-- Segment 199 of the body: the 2 instructions from source lines 611–612,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg199 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.611 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.612 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.613 `call fe25519_sqr_x86_from_lean`

/-- Segment 200 of the body: the 2 instructions from source lines 614–615,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg200 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.614 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.615 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.616 `call fe25519_sqr_x86_from_lean`

/-- Segment 201 of the body: the 2 instructions from source lines 617–618,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg201 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.617 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.618 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.619 `call fe25519_sqr_x86_from_lean`

/-- Segment 202 of the body: the 2 instructions from source lines 620–621,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg202 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.620 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.621 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.622 `call fe25519_sqr_x86_from_lean`

/-- Segment 203 of the body: the 2 instructions from source lines 623–624,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg203 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.623 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.624 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.625 `call fe25519_sqr_x86_from_lean`

/-- Segment 204 of the body: the 2 instructions from source lines 626–627,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg204 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.626 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.627 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.628 `call fe25519_sqr_x86_from_lean`

/-- Segment 205 of the body: the 2 instructions from source lines 629–630,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg205 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.629 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.630 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.631 `call fe25519_sqr_x86_from_lean`

/-- Segment 206 of the body: the 2 instructions from source lines 632–633,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg206 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.632 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.633 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.634 `call fe25519_sqr_x86_from_lean`

/-- Segment 207 of the body: the 2 instructions from source lines 635–636,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg207 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 96,  -- l.635 `leaq 96(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96 ]  -- l.636 `leaq 96(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.637 `call fe25519_sqr_x86_from_lean`

/-- Segment 208 of the body: the 3 instructions from source lines 638–640,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519InvertShippedSeg208 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.638 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 96,  -- l.639 `leaq 96(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 64 ]  -- l.640 `leaq 64(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.641 `call fe25519_mul_x86_from_lean`

/-- Segment 209 of the body: the 2 instructions from source lines 642–643,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg209 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.642 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.643 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.644 `call fe25519_sqr_x86_from_lean`

/-- Segment 210 of the body: the 2 instructions from source lines 645–646,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg210 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.645 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.646 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.647 `call fe25519_sqr_x86_from_lean`

/-- Segment 211 of the body: the 2 instructions from source lines 648–649,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg211 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.648 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.649 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.650 `call fe25519_sqr_x86_from_lean`

/-- Segment 212 of the body: the 2 instructions from source lines 651–652,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg212 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.651 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.652 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.653 `call fe25519_sqr_x86_from_lean`

/-- Segment 213 of the body: the 2 instructions from source lines 654–655,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg213 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.654 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.655 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.656 `call fe25519_sqr_x86_from_lean`

/-- Segment 214 of the body: the 2 instructions from source lines 657–658,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg214 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.657 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.658 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.659 `call fe25519_sqr_x86_from_lean`

/-- Segment 215 of the body: the 2 instructions from source lines 660–661,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg215 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.660 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.661 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.662 `call fe25519_sqr_x86_from_lean`

/-- Segment 216 of the body: the 2 instructions from source lines 663–664,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg216 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.663 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.664 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.665 `call fe25519_sqr_x86_from_lean`

/-- Segment 217 of the body: the 2 instructions from source lines 666–667,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg217 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.666 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.667 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.668 `call fe25519_sqr_x86_from_lean`

/-- Segment 218 of the body: the 2 instructions from source lines 669–670,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg218 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.669 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.670 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.671 `call fe25519_sqr_x86_from_lean`

/-- Segment 219 of the body: the 2 instructions from source lines 672–673,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg219 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.672 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.673 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.674 `call fe25519_sqr_x86_from_lean`

/-- Segment 220 of the body: the 2 instructions from source lines 675–676,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg220 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.675 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.676 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.677 `call fe25519_sqr_x86_from_lean`

/-- Segment 221 of the body: the 2 instructions from source lines 678–679,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg221 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.678 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.679 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.680 `call fe25519_sqr_x86_from_lean`

/-- Segment 222 of the body: the 2 instructions from source lines 681–682,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg222 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.681 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.682 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.683 `call fe25519_sqr_x86_from_lean`

/-- Segment 223 of the body: the 2 instructions from source lines 684–685,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg223 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.684 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.685 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.686 `call fe25519_sqr_x86_from_lean`

/-- Segment 224 of the body: the 2 instructions from source lines 687–688,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg224 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.687 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.688 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.689 `call fe25519_sqr_x86_from_lean`

/-- Segment 225 of the body: the 2 instructions from source lines 690–691,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg225 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.690 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.691 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.692 `call fe25519_sqr_x86_from_lean`

/-- Segment 226 of the body: the 2 instructions from source lines 693–694,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg226 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.693 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.694 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.695 `call fe25519_sqr_x86_from_lean`

/-- Segment 227 of the body: the 2 instructions from source lines 696–697,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg227 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.696 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.697 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.698 `call fe25519_sqr_x86_from_lean`

/-- Segment 228 of the body: the 2 instructions from source lines 699–700,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg228 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.699 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.700 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.701 `call fe25519_sqr_x86_from_lean`

/-- Segment 229 of the body: the 2 instructions from source lines 702–703,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg229 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.702 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.703 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.704 `call fe25519_sqr_x86_from_lean`

/-- Segment 230 of the body: the 2 instructions from source lines 705–706,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg230 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.705 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.706 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.707 `call fe25519_sqr_x86_from_lean`

/-- Segment 231 of the body: the 2 instructions from source lines 708–709,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg231 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.708 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.709 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.710 `call fe25519_sqr_x86_from_lean`

/-- Segment 232 of the body: the 2 instructions from source lines 711–712,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg232 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.711 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.712 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.713 `call fe25519_sqr_x86_from_lean`

/-- Segment 233 of the body: the 2 instructions from source lines 714–715,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg233 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.714 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.715 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.716 `call fe25519_sqr_x86_from_lean`

/-- Segment 234 of the body: the 2 instructions from source lines 717–718,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg234 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.717 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.718 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.719 `call fe25519_sqr_x86_from_lean`

/-- Segment 235 of the body: the 2 instructions from source lines 720–721,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg235 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.720 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.721 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.722 `call fe25519_sqr_x86_from_lean`

/-- Segment 236 of the body: the 2 instructions from source lines 723–724,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg236 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.723 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.724 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.725 `call fe25519_sqr_x86_from_lean`

/-- Segment 237 of the body: the 2 instructions from source lines 726–727,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg237 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.726 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.727 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.728 `call fe25519_sqr_x86_from_lean`

/-- Segment 238 of the body: the 2 instructions from source lines 729–730,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg238 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.729 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.730 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.731 `call fe25519_sqr_x86_from_lean`

/-- Segment 239 of the body: the 2 instructions from source lines 732–733,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg239 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.732 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.733 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.734 `call fe25519_sqr_x86_from_lean`

/-- Segment 240 of the body: the 2 instructions from source lines 735–736,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg240 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.735 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.736 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.737 `call fe25519_sqr_x86_from_lean`

/-- Segment 241 of the body: the 2 instructions from source lines 738–739,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg241 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.738 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.739 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.740 `call fe25519_sqr_x86_from_lean`

/-- Segment 242 of the body: the 2 instructions from source lines 741–742,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg242 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.741 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.742 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.743 `call fe25519_sqr_x86_from_lean`

/-- Segment 243 of the body: the 2 instructions from source lines 744–745,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg243 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.744 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.745 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.746 `call fe25519_sqr_x86_from_lean`

/-- Segment 244 of the body: the 2 instructions from source lines 747–748,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg244 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.747 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.748 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.749 `call fe25519_sqr_x86_from_lean`

/-- Segment 245 of the body: the 2 instructions from source lines 750–751,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg245 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.750 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.751 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.752 `call fe25519_sqr_x86_from_lean`

/-- Segment 246 of the body: the 2 instructions from source lines 753–754,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg246 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.753 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.754 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.755 `call fe25519_sqr_x86_from_lean`

/-- Segment 247 of the body: the 2 instructions from source lines 756–757,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg247 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.756 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.757 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.758 `call fe25519_sqr_x86_from_lean`

/-- Segment 248 of the body: the 2 instructions from source lines 759–760,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg248 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.759 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.760 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.761 `call fe25519_sqr_x86_from_lean`

/-- Segment 249 of the body: the 2 instructions from source lines 762–763,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg249 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.762 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.763 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.764 `call fe25519_sqr_x86_from_lean`

/-- Segment 250 of the body: the 2 instructions from source lines 765–766,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg250 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.765 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.766 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.767 `call fe25519_sqr_x86_from_lean`

/-- Segment 251 of the body: the 2 instructions from source lines 768–769,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg251 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.768 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.769 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.770 `call fe25519_sqr_x86_from_lean`

/-- Segment 252 of the body: the 2 instructions from source lines 771–772,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg252 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.771 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.772 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.773 `call fe25519_sqr_x86_from_lean`

/-- Segment 253 of the body: the 2 instructions from source lines 774–775,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg253 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.774 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.775 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.776 `call fe25519_sqr_x86_from_lean`

/-- Segment 254 of the body: the 2 instructions from source lines 777–778,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg254 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.777 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.778 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.779 `call fe25519_sqr_x86_from_lean`

/-- Segment 255 of the body: the 2 instructions from source lines 780–781,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg255 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.780 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.781 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.782 `call fe25519_sqr_x86_from_lean`

/-- Segment 256 of the body: the 2 instructions from source lines 783–784,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg256 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.783 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.784 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.785 `call fe25519_sqr_x86_from_lean`

/-- Segment 257 of the body: the 2 instructions from source lines 786–787,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg257 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.786 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.787 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.788 `call fe25519_sqr_x86_from_lean`

/-- Segment 258 of the body: the 2 instructions from source lines 789–790,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg258 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 64,  -- l.789 `leaq 64(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64 ]  -- l.790 `leaq 64(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.791 `call fe25519_sqr_x86_from_lean`

/-- Segment 259 of the body: the 3 instructions from source lines 792–794,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519InvertShippedSeg259 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.792 `leaq 32(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 64,  -- l.793 `leaq 64(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 32 ]  -- l.794 `leaq 32(%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.795 `call fe25519_mul_x86_from_lean`

/-- Segment 260 of the body: the 2 instructions from source lines 796–797,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg260 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.796 `leaq 32(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32 ]  -- l.797 `leaq 32(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.798 `call fe25519_sqr_x86_from_lean`

/-- Segment 261 of the body: the 2 instructions from source lines 799–800,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg261 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.799 `leaq 32(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32 ]  -- l.800 `leaq 32(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.801 `call fe25519_sqr_x86_from_lean`

/-- Segment 262 of the body: the 2 instructions from source lines 802–803,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg262 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.802 `leaq 32(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32 ]  -- l.803 `leaq 32(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.804 `call fe25519_sqr_x86_from_lean`

/-- Segment 263 of the body: the 2 instructions from source lines 805–806,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg263 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.805 `leaq 32(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32 ]  -- l.806 `leaq 32(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.807 `call fe25519_sqr_x86_from_lean`

/-- Segment 264 of the body: the 2 instructions from source lines 808–809,
    then `call fe25519_sqr_x86_from_lean`. -/
def ed25519InvertShippedSeg264 : List CallSeg :=
  [ { body :=
        [ .lea "%rdi" "%rsp" "%rsp" 0 32,  -- l.808 `leaq 32(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32 ]  -- l.809 `leaq 32(%rsp), %rsi`
      callee := some "fe25519_sqr_x86_from_lean" } ]  -- l.810 `call fe25519_sqr_x86_from_lean`

/-- Segment 265 of the body: the 3 instructions from source lines 811–813,
    then `call fe25519_mul_x86_from_lean`. -/
def ed25519InvertShippedSeg265 : List CallSeg :=
  [ { body :=
        [ .loadMem "%rdi" "%rsp" 128,  -- l.811 `movq 128(%rsp), %rdi`
          .lea "%rsi" "%rsp" "%rsp" 0 32,  -- l.812 `leaq 32(%rsp), %rsi`
          .lea "%rdx" "%rsp" "%rsp" 0 0 ]  -- l.813 `leaq (%rsp), %rdx`
      callee := some "fe25519_mul_x86_from_lean" } ]  -- l.814 `call fe25519_mul_x86_from_lean`

/-- Segment 266 of the body: the 1 instruction from source line 815. -/
def ed25519InvertShippedSeg266 : List CallSeg :=
  [ { body :=
        [ .storeMem "%rsp" 128 (.imm 0) ]  -- l.815 `movq $0, 128(%rsp)`
      callee := none } ]

/-- Part 1 of the body: segments 1–16. -/
def ed25519InvertShippedPart01 : List CallSeg :=
  ed25519InvertShippedSeg001 ++ ed25519InvertShippedSeg002 ++
  ed25519InvertShippedSeg003 ++ ed25519InvertShippedSeg004 ++
  ed25519InvertShippedSeg005 ++ ed25519InvertShippedSeg006 ++
  ed25519InvertShippedSeg007 ++ ed25519InvertShippedSeg008 ++
  ed25519InvertShippedSeg009 ++ ed25519InvertShippedSeg010 ++
  ed25519InvertShippedSeg011 ++ ed25519InvertShippedSeg012 ++
  ed25519InvertShippedSeg013 ++ ed25519InvertShippedSeg014 ++
  ed25519InvertShippedSeg015 ++ ed25519InvertShippedSeg016

/-- Part 1 has 38 instructions. -/
theorem ed25519InvertShippedPart01_instrs :
    (CallSeg.instrs ed25519InvertShippedPart01).length = 38 := by
  unfold ed25519InvertShippedPart01
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 1 makes 16 calls. -/
theorem ed25519InvertShippedPart01_calls :
    (CallSeg.callees ed25519InvertShippedPart01).length = 16 := by
  unfold ed25519InvertShippedPart01
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 2 of the body: segments 17–32. -/
def ed25519InvertShippedPart02 : List CallSeg :=
  ed25519InvertShippedSeg017 ++ ed25519InvertShippedSeg018 ++
  ed25519InvertShippedSeg019 ++ ed25519InvertShippedSeg020 ++
  ed25519InvertShippedSeg021 ++ ed25519InvertShippedSeg022 ++
  ed25519InvertShippedSeg023 ++ ed25519InvertShippedSeg024 ++
  ed25519InvertShippedSeg025 ++ ed25519InvertShippedSeg026 ++
  ed25519InvertShippedSeg027 ++ ed25519InvertShippedSeg028 ++
  ed25519InvertShippedSeg029 ++ ed25519InvertShippedSeg030 ++
  ed25519InvertShippedSeg031 ++ ed25519InvertShippedSeg032

/-- Part 2 has 33 instructions. -/
theorem ed25519InvertShippedPart02_instrs :
    (CallSeg.instrs ed25519InvertShippedPart02).length = 33 := by
  unfold ed25519InvertShippedPart02
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 2 makes 16 calls. -/
theorem ed25519InvertShippedPart02_calls :
    (CallSeg.callees ed25519InvertShippedPart02).length = 16 := by
  unfold ed25519InvertShippedPart02
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 3 of the body: segments 33–48. -/
def ed25519InvertShippedPart03 : List CallSeg :=
  ed25519InvertShippedSeg033 ++ ed25519InvertShippedSeg034 ++
  ed25519InvertShippedSeg035 ++ ed25519InvertShippedSeg036 ++
  ed25519InvertShippedSeg037 ++ ed25519InvertShippedSeg038 ++
  ed25519InvertShippedSeg039 ++ ed25519InvertShippedSeg040 ++
  ed25519InvertShippedSeg041 ++ ed25519InvertShippedSeg042 ++
  ed25519InvertShippedSeg043 ++ ed25519InvertShippedSeg044 ++
  ed25519InvertShippedSeg045 ++ ed25519InvertShippedSeg046 ++
  ed25519InvertShippedSeg047 ++ ed25519InvertShippedSeg048

/-- Part 3 has 33 instructions. -/
theorem ed25519InvertShippedPart03_instrs :
    (CallSeg.instrs ed25519InvertShippedPart03).length = 33 := by
  unfold ed25519InvertShippedPart03
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 3 makes 16 calls. -/
theorem ed25519InvertShippedPart03_calls :
    (CallSeg.callees ed25519InvertShippedPart03).length = 16 := by
  unfold ed25519InvertShippedPart03
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 4 of the body: segments 49–64. -/
def ed25519InvertShippedPart04 : List CallSeg :=
  ed25519InvertShippedSeg049 ++ ed25519InvertShippedSeg050 ++
  ed25519InvertShippedSeg051 ++ ed25519InvertShippedSeg052 ++
  ed25519InvertShippedSeg053 ++ ed25519InvertShippedSeg054 ++
  ed25519InvertShippedSeg055 ++ ed25519InvertShippedSeg056 ++
  ed25519InvertShippedSeg057 ++ ed25519InvertShippedSeg058 ++
  ed25519InvertShippedSeg059 ++ ed25519InvertShippedSeg060 ++
  ed25519InvertShippedSeg061 ++ ed25519InvertShippedSeg062 ++
  ed25519InvertShippedSeg063 ++ ed25519InvertShippedSeg064

/-- Part 4 has 33 instructions. -/
theorem ed25519InvertShippedPart04_instrs :
    (CallSeg.instrs ed25519InvertShippedPart04).length = 33 := by
  unfold ed25519InvertShippedPart04
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 4 makes 16 calls. -/
theorem ed25519InvertShippedPart04_calls :
    (CallSeg.callees ed25519InvertShippedPart04).length = 16 := by
  unfold ed25519InvertShippedPart04
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 5 of the body: segments 65–80. -/
def ed25519InvertShippedPart05 : List CallSeg :=
  ed25519InvertShippedSeg065 ++ ed25519InvertShippedSeg066 ++
  ed25519InvertShippedSeg067 ++ ed25519InvertShippedSeg068 ++
  ed25519InvertShippedSeg069 ++ ed25519InvertShippedSeg070 ++
  ed25519InvertShippedSeg071 ++ ed25519InvertShippedSeg072 ++
  ed25519InvertShippedSeg073 ++ ed25519InvertShippedSeg074 ++
  ed25519InvertShippedSeg075 ++ ed25519InvertShippedSeg076 ++
  ed25519InvertShippedSeg077 ++ ed25519InvertShippedSeg078 ++
  ed25519InvertShippedSeg079 ++ ed25519InvertShippedSeg080

/-- Part 5 has 32 instructions. -/
theorem ed25519InvertShippedPart05_instrs :
    (CallSeg.instrs ed25519InvertShippedPart05).length = 32 := by
  unfold ed25519InvertShippedPart05
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 5 makes 16 calls. -/
theorem ed25519InvertShippedPart05_calls :
    (CallSeg.callees ed25519InvertShippedPart05).length = 16 := by
  unfold ed25519InvertShippedPart05
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 6 of the body: segments 81–96. -/
def ed25519InvertShippedPart06 : List CallSeg :=
  ed25519InvertShippedSeg081 ++ ed25519InvertShippedSeg082 ++
  ed25519InvertShippedSeg083 ++ ed25519InvertShippedSeg084 ++
  ed25519InvertShippedSeg085 ++ ed25519InvertShippedSeg086 ++
  ed25519InvertShippedSeg087 ++ ed25519InvertShippedSeg088 ++
  ed25519InvertShippedSeg089 ++ ed25519InvertShippedSeg090 ++
  ed25519InvertShippedSeg091 ++ ed25519InvertShippedSeg092 ++
  ed25519InvertShippedSeg093 ++ ed25519InvertShippedSeg094 ++
  ed25519InvertShippedSeg095 ++ ed25519InvertShippedSeg096

/-- Part 6 has 32 instructions. -/
theorem ed25519InvertShippedPart06_instrs :
    (CallSeg.instrs ed25519InvertShippedPart06).length = 32 := by
  unfold ed25519InvertShippedPart06
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 6 makes 16 calls. -/
theorem ed25519InvertShippedPart06_calls :
    (CallSeg.callees ed25519InvertShippedPart06).length = 16 := by
  unfold ed25519InvertShippedPart06
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 7 of the body: segments 97–112. -/
def ed25519InvertShippedPart07 : List CallSeg :=
  ed25519InvertShippedSeg097 ++ ed25519InvertShippedSeg098 ++
  ed25519InvertShippedSeg099 ++ ed25519InvertShippedSeg100 ++
  ed25519InvertShippedSeg101 ++ ed25519InvertShippedSeg102 ++
  ed25519InvertShippedSeg103 ++ ed25519InvertShippedSeg104 ++
  ed25519InvertShippedSeg105 ++ ed25519InvertShippedSeg106 ++
  ed25519InvertShippedSeg107 ++ ed25519InvertShippedSeg108 ++
  ed25519InvertShippedSeg109 ++ ed25519InvertShippedSeg110 ++
  ed25519InvertShippedSeg111 ++ ed25519InvertShippedSeg112

/-- Part 7 has 33 instructions. -/
theorem ed25519InvertShippedPart07_instrs :
    (CallSeg.instrs ed25519InvertShippedPart07).length = 33 := by
  unfold ed25519InvertShippedPart07
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 7 makes 16 calls. -/
theorem ed25519InvertShippedPart07_calls :
    (CallSeg.callees ed25519InvertShippedPart07).length = 16 := by
  unfold ed25519InvertShippedPart07
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 8 of the body: segments 113–128. -/
def ed25519InvertShippedPart08 : List CallSeg :=
  ed25519InvertShippedSeg113 ++ ed25519InvertShippedSeg114 ++
  ed25519InvertShippedSeg115 ++ ed25519InvertShippedSeg116 ++
  ed25519InvertShippedSeg117 ++ ed25519InvertShippedSeg118 ++
  ed25519InvertShippedSeg119 ++ ed25519InvertShippedSeg120 ++
  ed25519InvertShippedSeg121 ++ ed25519InvertShippedSeg122 ++
  ed25519InvertShippedSeg123 ++ ed25519InvertShippedSeg124 ++
  ed25519InvertShippedSeg125 ++ ed25519InvertShippedSeg126 ++
  ed25519InvertShippedSeg127 ++ ed25519InvertShippedSeg128

/-- Part 8 has 32 instructions. -/
theorem ed25519InvertShippedPart08_instrs :
    (CallSeg.instrs ed25519InvertShippedPart08).length = 32 := by
  unfold ed25519InvertShippedPart08
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 8 makes 16 calls. -/
theorem ed25519InvertShippedPart08_calls :
    (CallSeg.callees ed25519InvertShippedPart08).length = 16 := by
  unfold ed25519InvertShippedPart08
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 9 of the body: segments 129–144. -/
def ed25519InvertShippedPart09 : List CallSeg :=
  ed25519InvertShippedSeg129 ++ ed25519InvertShippedSeg130 ++
  ed25519InvertShippedSeg131 ++ ed25519InvertShippedSeg132 ++
  ed25519InvertShippedSeg133 ++ ed25519InvertShippedSeg134 ++
  ed25519InvertShippedSeg135 ++ ed25519InvertShippedSeg136 ++
  ed25519InvertShippedSeg137 ++ ed25519InvertShippedSeg138 ++
  ed25519InvertShippedSeg139 ++ ed25519InvertShippedSeg140 ++
  ed25519InvertShippedSeg141 ++ ed25519InvertShippedSeg142 ++
  ed25519InvertShippedSeg143 ++ ed25519InvertShippedSeg144

/-- Part 9 has 32 instructions. -/
theorem ed25519InvertShippedPart09_instrs :
    (CallSeg.instrs ed25519InvertShippedPart09).length = 32 := by
  unfold ed25519InvertShippedPart09
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 9 makes 16 calls. -/
theorem ed25519InvertShippedPart09_calls :
    (CallSeg.callees ed25519InvertShippedPart09).length = 16 := by
  unfold ed25519InvertShippedPart09
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 10 of the body: segments 145–160. -/
def ed25519InvertShippedPart10 : List CallSeg :=
  ed25519InvertShippedSeg145 ++ ed25519InvertShippedSeg146 ++
  ed25519InvertShippedSeg147 ++ ed25519InvertShippedSeg148 ++
  ed25519InvertShippedSeg149 ++ ed25519InvertShippedSeg150 ++
  ed25519InvertShippedSeg151 ++ ed25519InvertShippedSeg152 ++
  ed25519InvertShippedSeg153 ++ ed25519InvertShippedSeg154 ++
  ed25519InvertShippedSeg155 ++ ed25519InvertShippedSeg156 ++
  ed25519InvertShippedSeg157 ++ ed25519InvertShippedSeg158 ++
  ed25519InvertShippedSeg159 ++ ed25519InvertShippedSeg160

/-- Part 10 has 32 instructions. -/
theorem ed25519InvertShippedPart10_instrs :
    (CallSeg.instrs ed25519InvertShippedPart10).length = 32 := by
  unfold ed25519InvertShippedPart10
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 10 makes 16 calls. -/
theorem ed25519InvertShippedPart10_calls :
    (CallSeg.callees ed25519InvertShippedPart10).length = 16 := by
  unfold ed25519InvertShippedPart10
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 11 of the body: segments 161–176. -/
def ed25519InvertShippedPart11 : List CallSeg :=
  ed25519InvertShippedSeg161 ++ ed25519InvertShippedSeg162 ++
  ed25519InvertShippedSeg163 ++ ed25519InvertShippedSeg164 ++
  ed25519InvertShippedSeg165 ++ ed25519InvertShippedSeg166 ++
  ed25519InvertShippedSeg167 ++ ed25519InvertShippedSeg168 ++
  ed25519InvertShippedSeg169 ++ ed25519InvertShippedSeg170 ++
  ed25519InvertShippedSeg171 ++ ed25519InvertShippedSeg172 ++
  ed25519InvertShippedSeg173 ++ ed25519InvertShippedSeg174 ++
  ed25519InvertShippedSeg175 ++ ed25519InvertShippedSeg176

/-- Part 11 has 32 instructions. -/
theorem ed25519InvertShippedPart11_instrs :
    (CallSeg.instrs ed25519InvertShippedPart11).length = 32 := by
  unfold ed25519InvertShippedPart11
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 11 makes 16 calls. -/
theorem ed25519InvertShippedPart11_calls :
    (CallSeg.callees ed25519InvertShippedPart11).length = 16 := by
  unfold ed25519InvertShippedPart11
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 12 of the body: segments 177–192. -/
def ed25519InvertShippedPart12 : List CallSeg :=
  ed25519InvertShippedSeg177 ++ ed25519InvertShippedSeg178 ++
  ed25519InvertShippedSeg179 ++ ed25519InvertShippedSeg180 ++
  ed25519InvertShippedSeg181 ++ ed25519InvertShippedSeg182 ++
  ed25519InvertShippedSeg183 ++ ed25519InvertShippedSeg184 ++
  ed25519InvertShippedSeg185 ++ ed25519InvertShippedSeg186 ++
  ed25519InvertShippedSeg187 ++ ed25519InvertShippedSeg188 ++
  ed25519InvertShippedSeg189 ++ ed25519InvertShippedSeg190 ++
  ed25519InvertShippedSeg191 ++ ed25519InvertShippedSeg192

/-- Part 12 has 32 instructions. -/
theorem ed25519InvertShippedPart12_instrs :
    (CallSeg.instrs ed25519InvertShippedPart12).length = 32 := by
  unfold ed25519InvertShippedPart12
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 12 makes 16 calls. -/
theorem ed25519InvertShippedPart12_calls :
    (CallSeg.callees ed25519InvertShippedPart12).length = 16 := by
  unfold ed25519InvertShippedPart12
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 13 of the body: segments 193–208. -/
def ed25519InvertShippedPart13 : List CallSeg :=
  ed25519InvertShippedSeg193 ++ ed25519InvertShippedSeg194 ++
  ed25519InvertShippedSeg195 ++ ed25519InvertShippedSeg196 ++
  ed25519InvertShippedSeg197 ++ ed25519InvertShippedSeg198 ++
  ed25519InvertShippedSeg199 ++ ed25519InvertShippedSeg200 ++
  ed25519InvertShippedSeg201 ++ ed25519InvertShippedSeg202 ++
  ed25519InvertShippedSeg203 ++ ed25519InvertShippedSeg204 ++
  ed25519InvertShippedSeg205 ++ ed25519InvertShippedSeg206 ++
  ed25519InvertShippedSeg207 ++ ed25519InvertShippedSeg208

/-- Part 13 has 33 instructions. -/
theorem ed25519InvertShippedPart13_instrs :
    (CallSeg.instrs ed25519InvertShippedPart13).length = 33 := by
  unfold ed25519InvertShippedPart13
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 13 makes 16 calls. -/
theorem ed25519InvertShippedPart13_calls :
    (CallSeg.callees ed25519InvertShippedPart13).length = 16 := by
  unfold ed25519InvertShippedPart13
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 14 of the body: segments 209–224. -/
def ed25519InvertShippedPart14 : List CallSeg :=
  ed25519InvertShippedSeg209 ++ ed25519InvertShippedSeg210 ++
  ed25519InvertShippedSeg211 ++ ed25519InvertShippedSeg212 ++
  ed25519InvertShippedSeg213 ++ ed25519InvertShippedSeg214 ++
  ed25519InvertShippedSeg215 ++ ed25519InvertShippedSeg216 ++
  ed25519InvertShippedSeg217 ++ ed25519InvertShippedSeg218 ++
  ed25519InvertShippedSeg219 ++ ed25519InvertShippedSeg220 ++
  ed25519InvertShippedSeg221 ++ ed25519InvertShippedSeg222 ++
  ed25519InvertShippedSeg223 ++ ed25519InvertShippedSeg224

/-- Part 14 has 32 instructions. -/
theorem ed25519InvertShippedPart14_instrs :
    (CallSeg.instrs ed25519InvertShippedPart14).length = 32 := by
  unfold ed25519InvertShippedPart14
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 14 makes 16 calls. -/
theorem ed25519InvertShippedPart14_calls :
    (CallSeg.callees ed25519InvertShippedPart14).length = 16 := by
  unfold ed25519InvertShippedPart14
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 15 of the body: segments 225–240. -/
def ed25519InvertShippedPart15 : List CallSeg :=
  ed25519InvertShippedSeg225 ++ ed25519InvertShippedSeg226 ++
  ed25519InvertShippedSeg227 ++ ed25519InvertShippedSeg228 ++
  ed25519InvertShippedSeg229 ++ ed25519InvertShippedSeg230 ++
  ed25519InvertShippedSeg231 ++ ed25519InvertShippedSeg232 ++
  ed25519InvertShippedSeg233 ++ ed25519InvertShippedSeg234 ++
  ed25519InvertShippedSeg235 ++ ed25519InvertShippedSeg236 ++
  ed25519InvertShippedSeg237 ++ ed25519InvertShippedSeg238 ++
  ed25519InvertShippedSeg239 ++ ed25519InvertShippedSeg240

/-- Part 15 has 32 instructions. -/
theorem ed25519InvertShippedPart15_instrs :
    (CallSeg.instrs ed25519InvertShippedPart15).length = 32 := by
  unfold ed25519InvertShippedPart15
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 15 makes 16 calls. -/
theorem ed25519InvertShippedPart15_calls :
    (CallSeg.callees ed25519InvertShippedPart15).length = 16 := by
  unfold ed25519InvertShippedPart15
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 16 of the body: segments 241–256. -/
def ed25519InvertShippedPart16 : List CallSeg :=
  ed25519InvertShippedSeg241 ++ ed25519InvertShippedSeg242 ++
  ed25519InvertShippedSeg243 ++ ed25519InvertShippedSeg244 ++
  ed25519InvertShippedSeg245 ++ ed25519InvertShippedSeg246 ++
  ed25519InvertShippedSeg247 ++ ed25519InvertShippedSeg248 ++
  ed25519InvertShippedSeg249 ++ ed25519InvertShippedSeg250 ++
  ed25519InvertShippedSeg251 ++ ed25519InvertShippedSeg252 ++
  ed25519InvertShippedSeg253 ++ ed25519InvertShippedSeg254 ++
  ed25519InvertShippedSeg255 ++ ed25519InvertShippedSeg256

/-- Part 16 has 32 instructions. -/
theorem ed25519InvertShippedPart16_instrs :
    (CallSeg.instrs ed25519InvertShippedPart16).length = 32 := by
  unfold ed25519InvertShippedPart16
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 16 makes 16 calls. -/
theorem ed25519InvertShippedPart16_calls :
    (CallSeg.callees ed25519InvertShippedPart16).length = 16 := by
  unfold ed25519InvertShippedPart16
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- Part 17 of the body: segments 257–266. -/
def ed25519InvertShippedPart17 : List CallSeg :=
  ed25519InvertShippedSeg257 ++ ed25519InvertShippedSeg258 ++
  ed25519InvertShippedSeg259 ++ ed25519InvertShippedSeg260 ++
  ed25519InvertShippedSeg261 ++ ed25519InvertShippedSeg262 ++
  ed25519InvertShippedSeg263 ++ ed25519InvertShippedSeg264 ++
  ed25519InvertShippedSeg265 ++ ed25519InvertShippedSeg266

/-- Part 17 has 21 instructions. -/
theorem ed25519InvertShippedPart17_instrs :
    (CallSeg.instrs ed25519InvertShippedPart17).length = 21 := by
  unfold ed25519InvertShippedPart17
  simp only [CallSeg.instrs_append, List.length_append]
  rfl

/-- Part 17 makes 9 calls. -/
theorem ed25519InvertShippedPart17_calls :
    (CallSeg.callees ed25519InvertShippedPart17).length = 9 := by
  unfold ed25519InvertShippedPart17
  simp only [CallSeg.callees_append, List.length_append]
  rfl

/-- The body of `ed25519_invert_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 266 segments,
    grouped in 17 parts.
    Each segment is a run of instructions followed by the `call` that ends it, if any. -/
def ed25519InvertShippedBlock : List CallSeg :=
  ed25519InvertShippedPart01 ++ ed25519InvertShippedPart02 ++
  ed25519InvertShippedPart03 ++ ed25519InvertShippedPart04 ++
  ed25519InvertShippedPart05 ++ ed25519InvertShippedPart06 ++
  ed25519InvertShippedPart07 ++ ed25519InvertShippedPart08 ++
  ed25519InvertShippedPart09 ++ ed25519InvertShippedPart10 ++
  ed25519InvertShippedPart11 ++ ed25519InvertShippedPart12 ++
  ed25519InvertShippedPart13 ++ ed25519InvertShippedPart14 ++
  ed25519InvertShippedPart15 ++ ed25519InvertShippedPart16 ++ ed25519InvertShippedPart17

/-- The frame instructions of `ed25519_invert_x86_from_lean` before the body,
    which the block omits: each `pushq r` as `leaq -8(%rsp), %rsp` followed by the
    store of `r` at `0(%rsp)`, and the stack allocation as the instruction the text
    contains. -/
def ed25519InvertShippedPrologue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.5 `pushq %rbx`
    .storeMem "%rsp" 0 (.reg "%rbx"),  -- l.5 `pushq %rbx`
    .lea "%rsp" "%rsp" "%rsp" 0 (-176) ]  -- l.6 `leaq -176(%rsp), %rsp`

/-- The frame instructions of `ed25519_invert_x86_from_lean` after the body,
    which the block omits, `ret` excluded: the stack release as the instruction the
    text contains, and each `popq r` as the load of `r` from `0(%rsp)` followed by
    `leaq 8(%rsp), %rsp`. -/
def ed25519InvertShippedEpilogue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 176,  -- l.816 `leaq 176(%rsp), %rsp`
    .loadMem "%rbx" "%rsp" 0,  -- l.817 `popq %rbx`
    .lea "%rsp" "%rsp" "%rsp" 0 8 ]  -- l.817 `popq %rbx`

/-- The block has 544 instructions; the count of each part is a lemma above. -/
theorem ed25519InvertShippedBlock_instrs :
    (CallSeg.instrs ed25519InvertShippedBlock).length = 544 := by
  unfold ed25519InvertShippedBlock
  simp only [CallSeg.instrs_append, List.length_append, ed25519InvertShippedPart01_instrs,
    ed25519InvertShippedPart02_instrs, ed25519InvertShippedPart03_instrs,
    ed25519InvertShippedPart04_instrs, ed25519InvertShippedPart05_instrs,
    ed25519InvertShippedPart06_instrs, ed25519InvertShippedPart07_instrs,
    ed25519InvertShippedPart08_instrs, ed25519InvertShippedPart09_instrs,
    ed25519InvertShippedPart10_instrs, ed25519InvertShippedPart11_instrs,
    ed25519InvertShippedPart12_instrs, ed25519InvertShippedPart13_instrs,
    ed25519InvertShippedPart14_instrs, ed25519InvertShippedPart15_instrs,
    ed25519InvertShippedPart16_instrs, ed25519InvertShippedPart17_instrs]

/-- The block makes 265 calls; the count of each part is a lemma above. -/
theorem ed25519InvertShippedBlock_calls :
    (CallSeg.callees ed25519InvertShippedBlock).length = 265 := by
  unfold ed25519InvertShippedBlock
  simp only [CallSeg.callees_append, List.length_append, ed25519InvertShippedPart01_calls,
    ed25519InvertShippedPart02_calls, ed25519InvertShippedPart03_calls,
    ed25519InvertShippedPart04_calls, ed25519InvertShippedPart05_calls,
    ed25519InvertShippedPart06_calls, ed25519InvertShippedPart07_calls,
    ed25519InvertShippedPart08_calls, ed25519InvertShippedPart09_calls,
    ed25519InvertShippedPart10_calls, ed25519InvertShippedPart11_calls,
    ed25519InvertShippedPart12_calls, ed25519InvertShippedPart13_calls,
    ed25519InvertShippedPart14_calls, ed25519InvertShippedPart15_calls,
    ed25519InvertShippedPart16_calls, ed25519InvertShippedPart17_calls]

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519InvertShipped
