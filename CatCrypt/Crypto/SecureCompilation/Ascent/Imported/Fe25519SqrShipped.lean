/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# `fe25519_sqr_x86_from_lean` from the owned backend's output as a `JInstr 64` block

`fe25519SqrShippedBlock` is the body of the function `fe25519_sqr_x86_from_lean` in
an x86-64 AT&T file printed by CatCrypt's owned backend, translated instruction by
instruction. The file's producer is recorded in `PROVENANCE.md` next to it, where
one exists.

## Provenance

* Source: `crates/catcrypt-ed25519/asm/fe25519_sqr_x86_from_lean.s` in the
  `SSProve-lean` repository at commit `5a765fbc8aff83bff9eab87c81af0df5d9ae9944`
  (tracked and unchanged at that commit), file SHA-256
  `5f9d15f5b3e71213e005ba82e8618d284729ff730332d3b73576ed45471747ac`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 13 frame instructions,
  each checked by the importer: `pushq` of `%rbx`, `%r12`, `%r13`, `%r14`, `%r15`,
  `%rbp` on entry and the `popq` sequence in reverse order on exit; `ret`.
* `fe25519SqrShippedPrologue` and `fe25519SqrShippedEpilogue` are the frame
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

The block has 95 instructions. Source instructions by mnemonic: `adcx` 22, `adox`
16, `mulxq` 16, `movq` 14, `mulx` 5, `xorq` 5, `addq` 3, `sbbq` 3, `adcq` 2,
`imulq` 2, `shlq` 2, `shrq` 2, `subq` 2, `andq` 1.

## Main definitions

* `fe25519SqrShippedSeg01` … `fe25519SqrShippedSeg03`: the block in 3 segments,
  each a literal `List (JInstr 64)`. A segment ends after a call, after the entry
  run of `%rsp` stores, before the exit run of `%rsp` loads, and after 32
  instructions.
* `fe25519SqrShippedBlock`: the block, the concatenation of the segments.
* `fe25519SqrShippedPrologue`, `fe25519SqrShippedEpilogue`: the frame instructions
  before and after the block.

## Main results

* `fe25519SqrShippedBlock_length`: the block has 95 instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519SqrShipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 32 instructions from source lines 11–42. -/
def fe25519SqrShippedSeg01 : List (JInstr 64) :=
  [ .mov "%rbp" (.imm 0),  -- l.11 `movq $0, %rbp`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.12 `xorq %rbp, %rbp`
    .loadMem "%rdx" "%rsi" 0,  -- l.13 `movq 0(%rsi), %rdx`
    .mulxMem "%rcx" "%r8" (.reg "%rdx") "%rsi" 0,  -- l.14 `mulxq 0(%rsi), %r8, %rcx`
    .mulxMem "%r9" "%r10" (.reg "%rdx") "%rsi" 8,  -- l.15 `mulxq 8(%rsi), %r10, %r9`
    .adcx "%rcx" (.reg "%r10"),  -- l.16 `adcx %r10, %rcx`
    .mulxMem "%r11" "%r10" (.reg "%rdx") "%rsi" 16,  -- l.17 `mulxq 16(%rsi), %r10, %r11`
    .adcx "%r9" (.reg "%r10"),  -- l.18 `adcx %r10, %r9`
    .mulxMem "%rax" "%r10" (.reg "%rdx") "%rsi" 24,  -- l.19 `mulxq 24(%rsi), %r10, %rax`
    .adcx "%r11" (.reg "%r10"),  -- l.20 `adcx %r10, %r11`
    .adcx "%rax" (.reg "%rbp"),  -- l.21 `adcx %rbp, %rax`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.22 `xorq %rbp, %rbp`
    .loadMem "%rdx" "%rsi" 8,  -- l.23 `movq 8(%rsi), %rdx`
    .mulxMem "%rbx" "%r10" (.reg "%rdx") "%rsi" 0,  -- l.24 `mulxq 0(%rsi), %r10, %rbx`
    .adcx "%rcx" (.reg "%r10"),  -- l.25 `adcx %r10, %rcx`
    .adox "%r9" (.reg "%rbx"),  -- l.26 `adox %rbx, %r9`
    .mulxMem "%rbx" "%r10" (.reg "%rdx") "%rsi" 8,  -- l.27 `mulxq 8(%rsi), %r10, %rbx`
    .adcx "%r9" (.reg "%r10"),  -- l.28 `adcx %r10, %r9`
    .adox "%r11" (.reg "%rbx"),  -- l.29 `adox %rbx, %r11`
    .mulxMem "%rbx" "%r10" (.reg "%rdx") "%rsi" 16,  -- l.30 `mulxq 16(%rsi), %r10, %rbx`
    .adcx "%r11" (.reg "%r10"),  -- l.31 `adcx %r10, %r11`
    .adox "%rax" (.reg "%rbx"),  -- l.32 `adox %rbx, %rax`
    .mulxMem "%r12" "%r10" (.reg "%rdx") "%rsi" 24,  -- l.33 `mulxq 24(%rsi), %r10, %r12`
    .adcx "%rax" (.reg "%r10"),  -- l.34 `adcx %r10, %rax`
    .adox "%r12" (.reg "%rbp"),  -- l.35 `adox %rbp, %r12`
    .adcx "%r12" (.reg "%rbp"),  -- l.36 `adcx %rbp, %r12`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.37 `xorq %rbp, %rbp`
    .loadMem "%rdx" "%rsi" 16,  -- l.38 `movq 16(%rsi), %rdx`
    .mulxMem "%rbx" "%r10" (.reg "%rdx") "%rsi" 0,  -- l.39 `mulxq 0(%rsi), %r10, %rbx`
    .adcx "%r9" (.reg "%r10"),  -- l.40 `adcx %r10, %r9`
    .adox "%r11" (.reg "%rbx"),  -- l.41 `adox %rbx, %r11`
    .mulxMem "%rbx" "%r10" (.reg "%rdx") "%rsi" 8 ]  -- l.42 `mulxq 8(%rsi), %r10, %rbx`

/-- Segment 2 of the body: the 32 instructions from source lines 43–74. -/
def fe25519SqrShippedSeg02 : List (JInstr 64) :=
  [ .adcx "%r11" (.reg "%r10"),  -- l.43 `adcx %r10, %r11`
    .adox "%rax" (.reg "%rbx"),  -- l.44 `adox %rbx, %rax`
    .mulxMem "%rbx" "%r10" (.reg "%rdx") "%rsi" 16,  -- l.45 `mulxq 16(%rsi), %r10, %rbx`
    .adcx "%rax" (.reg "%r10"),  -- l.46 `adcx %r10, %rax`
    .adox "%r12" (.reg "%rbx"),  -- l.47 `adox %rbx, %r12`
    .mulxMem "%r13" "%r10" (.reg "%rdx") "%rsi" 24,  -- l.48 `mulxq 24(%rsi), %r10, %r13`
    .adcx "%r12" (.reg "%r10"),  -- l.49 `adcx %r10, %r12`
    .adox "%r13" (.reg "%rbp"),  -- l.50 `adox %rbp, %r13`
    .adcx "%r13" (.reg "%rbp"),  -- l.51 `adcx %rbp, %r13`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.52 `xorq %rbp, %rbp`
    .loadMem "%rdx" "%rsi" 24,  -- l.53 `movq 24(%rsi), %rdx`
    .mulxMem "%rbx" "%r10" (.reg "%rdx") "%rsi" 0,  -- l.54 `mulxq 0(%rsi), %r10, %rbx`
    .adcx "%r11" (.reg "%r10"),  -- l.55 `adcx %r10, %r11`
    .adox "%rax" (.reg "%rbx"),  -- l.56 `adox %rbx, %rax`
    .mulxMem "%rbx" "%r10" (.reg "%rdx") "%rsi" 8,  -- l.57 `mulxq 8(%rsi), %r10, %rbx`
    .adcx "%rax" (.reg "%r10"),  -- l.58 `adcx %r10, %rax`
    .adox "%r12" (.reg "%rbx"),  -- l.59 `adox %rbx, %r12`
    .mulxMem "%rbx" "%r10" (.reg "%rdx") "%rsi" 16,  -- l.60 `mulxq 16(%rsi), %r10, %rbx`
    .adcx "%r12" (.reg "%r10"),  -- l.61 `adcx %r10, %r12`
    .adox "%r13" (.reg "%rbx"),  -- l.62 `adox %rbx, %r13`
    .mulxMem "%r14" "%r10" (.reg "%rdx") "%rsi" 24,  -- l.63 `mulxq 24(%rsi), %r10, %r14`
    .adcx "%r13" (.reg "%r10"),  -- l.64 `adcx %r10, %r13`
    .adox "%r14" (.reg "%rbp"),  -- l.65 `adox %rbp, %r14`
    .adcx "%r14" (.reg "%rbp"),  -- l.66 `adcx %rbp, %r14`
    .mov "%rdx" (.imm 38),  -- l.67 `movq $38, %rdx`
    .mulx "%rbx" "%r10" (.reg "%rdx") (.reg "%r14"),  -- l.68 `mulx %r14, %r10, %rbx`
    .add "%r10" (.reg "%r11"),  -- l.69 `addq %r11, %r10`
    .adc "%rbx" (.reg "%rbp"),  -- l.70 `adcq %rbp, %rbx`
    .mov "%r15" (.reg "%r10"),  -- l.71 `movq %r10, %r15`
    .shr "%r15" (.imm 63),  -- l.72 `shrq $63, %r15`
    .shl "%rbx" (.imm 1),  -- l.73 `shlq $1, %rbx`
    .add "%rbx" (.reg "%r15") ]  -- l.74 `addq %r15, %rbx`

/-- Segment 3 of the body: the 31 instructions from source lines 75–105. -/
def fe25519SqrShippedSeg03 : List (JInstr 64) :=
  [ .add "%rbx" (.imm 1),  -- l.75 `addq $1, %rbx`
    .mov "%r15" (.reg "%rbx"),  -- l.76 `movq %rbx, %r15`
    .imulri "%rbx" "%rbx" 19,  -- l.77 `imulq $19, %rbx, %rbx`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.78 `xorq %rbp, %rbp`
    .adox "%r8" (.reg "%rbx"),  -- l.79 `adox %rbx, %r8`
    .mulx "%rbx" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.80 `mulx %rax, %r10, %rbx`
    .adcx "%r8" (.reg "%r10"),  -- l.81 `adcx %r10, %r8`
    .adox "%rcx" (.reg "%rbx"),  -- l.82 `adox %rbx, %rcx`
    .mulx "%rbx" "%r10" (.reg "%rdx") (.reg "%r12"),  -- l.83 `mulx %r12, %r10, %rbx`
    .adcx "%rcx" (.reg "%r10"),  -- l.84 `adcx %r10, %rcx`
    .adox "%r9" (.reg "%rbx"),  -- l.85 `adox %rbx, %r9`
    .mulx "%rbx" "%r10" (.reg "%rdx") (.reg "%r13"),  -- l.86 `mulx %r13, %r10, %rbx`
    .adcx "%r9" (.reg "%r10"),  -- l.87 `adcx %r10, %r9`
    .adox "%r11" (.reg "%rbx"),  -- l.88 `adox %rbx, %r11`
    .mulx "%rbx" "%r10" (.reg "%rdx") (.reg "%r14"),  -- l.89 `mulx %r14, %r10, %rbx`
    .adc "%r11" (.reg "%r10"),  -- l.90 `adcq %r10, %r11`
    .shl "%r15" (.imm 63),  -- l.91 `shlq $63, %r15`
    .mov "%r10" (.reg "%r11"),  -- l.92 `movq %r11, %r10`
    .sub "%r10" (.reg "%r15"),  -- l.93 `subq %r15, %r10`
    .shr "%r10" (.imm 63),  -- l.94 `shrq $63, %r10`
    .imulri "%r10" "%r10" 19,  -- l.95 `imulq $19, %r10, %r10`
    .sub "%r8" (.reg "%r10"),  -- l.96 `subq %r10, %r8`
    .sbb "%rcx" (.reg "%rbp"),  -- l.97 `sbbq %rbp, %rcx`
    .sbb "%r9" (.reg "%rbp"),  -- l.98 `sbbq %rbp, %r9`
    .sbb "%r11" (.reg "%rbp"),  -- l.99 `sbbq %rbp, %r11`
    .mov "%rbx" (.imm 9223372036854775807),  -- l.100 `movq $9223372036854775807, %rbx`
    .and_ "%r11" (.reg "%rbx"),  -- l.101 `andq %rbx, %r11`
    .storeMem "%rdi" 0 (.reg "%r8"),  -- l.102 `movq %r8, 0(%rdi)`
    .storeMem "%rdi" 8 (.reg "%rcx"),  -- l.103 `movq %rcx, 8(%rdi)`
    .storeMem "%rdi" 16 (.reg "%r9"),  -- l.104 `movq %r9, 16(%rdi)`
    .storeMem "%rdi" 24 (.reg "%r11") ]  -- l.105 `movq %r11, 24(%rdi)`

/-- The body of `fe25519_sqr_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 3 segments. -/
def fe25519SqrShippedBlock : List (JInstr 64) :=
  fe25519SqrShippedSeg01 ++ fe25519SqrShippedSeg02 ++ fe25519SqrShippedSeg03

/-- The frame instructions of `fe25519_sqr_x86_from_lean` before the body,
    which the block omits: each `pushq r` as `leaq -8(%rsp), %rsp` followed by the
    store of `r` at `0(%rsp)`, and the stack allocation as the instruction the text
    contains. -/
def fe25519SqrShippedPrologue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.5 `pushq %rbx`
    .storeMem "%rsp" 0 (.reg "%rbx"),  -- l.5 `pushq %rbx`
    .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.6 `pushq %r12`
    .storeMem "%rsp" 0 (.reg "%r12"),  -- l.6 `pushq %r12`
    .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.7 `pushq %r13`
    .storeMem "%rsp" 0 (.reg "%r13"),  -- l.7 `pushq %r13`
    .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.8 `pushq %r14`
    .storeMem "%rsp" 0 (.reg "%r14"),  -- l.8 `pushq %r14`
    .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.9 `pushq %r15`
    .storeMem "%rsp" 0 (.reg "%r15"),  -- l.9 `pushq %r15`
    .lea "%rsp" "%rsp" "%rsp" 0 (-8),  -- l.10 `pushq %rbp`
    .storeMem "%rsp" 0 (.reg "%rbp") ]  -- l.10 `pushq %rbp`

/-- The frame instructions of `fe25519_sqr_x86_from_lean` after the body,
    which the block omits, `ret` excluded: the stack release as the instruction the
    text contains, and each `popq r` as the load of `r` from `0(%rsp)` followed by
    `leaq 8(%rsp), %rsp`. -/
def fe25519SqrShippedEpilogue : List (JInstr 64) :=
  [ .loadMem "%rbp" "%rsp" 0,  -- l.106 `popq %rbp`
    .lea "%rsp" "%rsp" "%rsp" 0 8,  -- l.106 `popq %rbp`
    .loadMem "%r15" "%rsp" 0,  -- l.107 `popq %r15`
    .lea "%rsp" "%rsp" "%rsp" 0 8,  -- l.107 `popq %r15`
    .loadMem "%r14" "%rsp" 0,  -- l.108 `popq %r14`
    .lea "%rsp" "%rsp" "%rsp" 0 8,  -- l.108 `popq %r14`
    .loadMem "%r13" "%rsp" 0,  -- l.109 `popq %r13`
    .lea "%rsp" "%rsp" "%rsp" 0 8,  -- l.109 `popq %r13`
    .loadMem "%r12" "%rsp" 0,  -- l.110 `popq %r12`
    .lea "%rsp" "%rsp" "%rsp" 0 8,  -- l.110 `popq %r12`
    .loadMem "%rbx" "%rsp" 0,  -- l.111 `popq %rbx`
    .lea "%rsp" "%rsp" "%rsp" 0 8 ]  -- l.111 `popq %rbx`

/-- The block has 95 instructions; the count of each segment is computed by `rfl`. -/
theorem fe25519SqrShippedBlock_length :
    fe25519SqrShippedBlock.length = 95 := by
  unfold fe25519SqrShippedBlock
  simp only [List.length_append]
  rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519SqrShipped
