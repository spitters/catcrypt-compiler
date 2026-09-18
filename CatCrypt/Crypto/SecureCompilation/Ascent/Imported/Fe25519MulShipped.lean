/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# `fe25519_mul_x86_from_lean` from the owned backend's output as a `JInstr 64` block

`fe25519MulShippedBlock` is the body of the function `fe25519_mul_x86_from_lean` in
an x86-64 AT&T file printed by CatCrypt's owned backend, translated instruction by
instruction. The file's producer is recorded in `PROVENANCE.md` next to it, where
one exists.

## Provenance

* Source: `crates/catcrypt-ed25519/asm/fe25519_mul_x86_from_lean.s` in the
  `SSProve-lean` repository at commit `5a765fbc8aff83bff9eab87c81af0df5d9ae9944`
  (tracked and unchanged at that commit), file SHA-256
  `d09faf65ef74b1327260cc837b9884915c36ceb3bacbc4c21d4a8b75e90ba75a`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 1 frame instruction, each
  checked by the importer: `ret`.
* `fe25519MulShippedPrologue` and `fe25519MulShippedEpilogue` are the frame
  instructions before and after the block, `ret` excluded: each `pushq r` as `lea
  "%rsp" "%rsp" "%rsp" 0 (-8)` followed by `storeMem "%rsp" 0 (.reg r)`, each `popq
  r` as `loadMem r "%rsp" 0` followed by `lea "%rsp" "%rsp" "%rsp" 0 8`, and the
  stack allocation and its release as the instruction the text contains. `lea`
  writes no flag, as `pushq` and `popq` write none.
* Every other instruction is kept, `%rsp`-relative moves included, as `storeMem
  "%rsp" off` and `loadMem r "%rsp" off`. `%rsp` is constant in the body.
* The first 6 instructions store registers into `%rsp` slots and form segment 1.
  The last 6 instructions load callee-saved registers back from the slots segment 1
  stored them to, and form the last segment.
* Registers keep their physical names (`"%rax"`, …, `"%r15"`, `"%rsp"`); no
  register allocation is involved.
* `JasminModel` keys memory by the name of the base register and a byte offset, at
  word granularity. A proof over this block is a statement about that model; it
  agrees with the processor where each base register holds one address throughout
  the block and distinct names address disjoint words.

The block has 108 instructions. Source instructions by mnemonic: `movq` 27, `adcx`
22, `adox` 16, `mulxq` 16, `mulx` 5, `xorq` 5, `addq` 3, `sbbq` 3, `adcq` 2,
`imulq` 2, `shlq` 2, `shrq` 2, `subq` 2, `andq` 1.

## Main definitions

* `fe25519MulShippedSeg01` … `fe25519MulShippedSeg05`: the block in 5 segments,
  each a literal `List (JInstr 64)`. A segment ends after a call, after the entry
  run of `%rsp` stores, before the exit run of `%rsp` loads, and after 32
  instructions.
* `fe25519MulShippedBlock`: the block, the concatenation of the segments.
* `fe25519MulShippedPrologue`, `fe25519MulShippedEpilogue`: the frame instructions
  before and after the block.

## Main results

* `fe25519MulShippedBlock_length`: the block has 108 instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519MulShipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 6 instructions from source lines 5–10. -/
def fe25519MulShippedSeg01 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-8) (.reg "%rbx"),  -- l.5 `movq %rbx, -8(%rsp)`
    .storeMem "%rsp" (-16) (.reg "%rbp"),  -- l.6 `movq %rbp, -16(%rsp)`
    .storeMem "%rsp" (-24) (.reg "%r12"),  -- l.7 `movq %r12, -24(%rsp)`
    .storeMem "%rsp" (-32) (.reg "%r13"),  -- l.8 `movq %r13, -32(%rsp)`
    .storeMem "%rsp" (-40) (.reg "%r14"),  -- l.9 `movq %r14, -40(%rsp)`
    .storeMem "%rsp" (-48) (.reg "%r15") ]  -- l.10 `movq %r15, -48(%rsp)`

/-- Segment 2 of the body: the 32 instructions from source lines 11–42. -/
def fe25519MulShippedSeg02 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rdx"),  -- l.11 `movq %rdx, %rcx`
    .mov "%rbp" (.imm 0),  -- l.12 `movq $0, %rbp`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.13 `xorq %rbp, %rbp`
    .loadMem "%rdx" "%rcx" 0,  -- l.14 `movq 0(%rcx), %rdx`
    .mulxMem "%r8" "%r9" (.reg "%rdx") "%rsi" 0,  -- l.15 `mulxq 0(%rsi), %r9, %r8`
    .mulxMem "%r10" "%r11" (.reg "%rdx") "%rsi" 8,  -- l.16 `mulxq 8(%rsi), %r11, %r10`
    .adcx "%r8" (.reg "%r11"),  -- l.17 `adcx %r11, %r8`
    .mulxMem "%rax" "%r11" (.reg "%rdx") "%rsi" 16,  -- l.18 `mulxq 16(%rsi), %r11, %rax`
    .adcx "%r10" (.reg "%r11"),  -- l.19 `adcx %r11, %r10`
    .mulxMem "%rbx" "%r11" (.reg "%rdx") "%rsi" 24,  -- l.20 `mulxq 24(%rsi), %r11, %rbx`
    .adcx "%rax" (.reg "%r11"),  -- l.21 `adcx %r11, %rax`
    .adcx "%rbx" (.reg "%rbp"),  -- l.22 `adcx %rbp, %rbx`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.23 `xorq %rbp, %rbp`
    .loadMem "%rdx" "%rcx" 8,  -- l.24 `movq 8(%rcx), %rdx`
    .mulxMem "%r12" "%r11" (.reg "%rdx") "%rsi" 0,  -- l.25 `mulxq 0(%rsi), %r11, %r12`
    .adcx "%r8" (.reg "%r11"),  -- l.26 `adcx %r11, %r8`
    .adox "%r10" (.reg "%r12"),  -- l.27 `adox %r12, %r10`
    .mulxMem "%r12" "%r11" (.reg "%rdx") "%rsi" 8,  -- l.28 `mulxq 8(%rsi), %r11, %r12`
    .adcx "%r10" (.reg "%r11"),  -- l.29 `adcx %r11, %r10`
    .adox "%rax" (.reg "%r12"),  -- l.30 `adox %r12, %rax`
    .mulxMem "%r12" "%r11" (.reg "%rdx") "%rsi" 16,  -- l.31 `mulxq 16(%rsi), %r11, %r12`
    .adcx "%rax" (.reg "%r11"),  -- l.32 `adcx %r11, %rax`
    .adox "%rbx" (.reg "%r12"),  -- l.33 `adox %r12, %rbx`
    .mulxMem "%r13" "%r11" (.reg "%rdx") "%rsi" 24,  -- l.34 `mulxq 24(%rsi), %r11, %r13`
    .adcx "%rbx" (.reg "%r11"),  -- l.35 `adcx %r11, %rbx`
    .adox "%r13" (.reg "%rbp"),  -- l.36 `adox %rbp, %r13`
    .adcx "%r13" (.reg "%rbp"),  -- l.37 `adcx %rbp, %r13`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.38 `xorq %rbp, %rbp`
    .loadMem "%rdx" "%rcx" 16,  -- l.39 `movq 16(%rcx), %rdx`
    .mulxMem "%r12" "%r11" (.reg "%rdx") "%rsi" 0,  -- l.40 `mulxq 0(%rsi), %r11, %r12`
    .adcx "%r10" (.reg "%r11"),  -- l.41 `adcx %r11, %r10`
    .adox "%rax" (.reg "%r12") ]  -- l.42 `adox %r12, %rax`

/-- Segment 3 of the body: the 32 instructions from source lines 43–74. -/
def fe25519MulShippedSeg03 : List (JInstr 64) :=
  [ .mulxMem "%r12" "%r11" (.reg "%rdx") "%rsi" 8,  -- l.43 `mulxq 8(%rsi), %r11, %r12`
    .adcx "%rax" (.reg "%r11"),  -- l.44 `adcx %r11, %rax`
    .adox "%rbx" (.reg "%r12"),  -- l.45 `adox %r12, %rbx`
    .mulxMem "%r12" "%r11" (.reg "%rdx") "%rsi" 16,  -- l.46 `mulxq 16(%rsi), %r11, %r12`
    .adcx "%rbx" (.reg "%r11"),  -- l.47 `adcx %r11, %rbx`
    .adox "%r13" (.reg "%r12"),  -- l.48 `adox %r12, %r13`
    .mulxMem "%r14" "%r11" (.reg "%rdx") "%rsi" 24,  -- l.49 `mulxq 24(%rsi), %r11, %r14`
    .adcx "%r13" (.reg "%r11"),  -- l.50 `adcx %r11, %r13`
    .adox "%r14" (.reg "%rbp"),  -- l.51 `adox %rbp, %r14`
    .adcx "%r14" (.reg "%rbp"),  -- l.52 `adcx %rbp, %r14`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.53 `xorq %rbp, %rbp`
    .loadMem "%rdx" "%rcx" 24,  -- l.54 `movq 24(%rcx), %rdx`
    .mulxMem "%r12" "%r11" (.reg "%rdx") "%rsi" 0,  -- l.55 `mulxq 0(%rsi), %r11, %r12`
    .adcx "%rax" (.reg "%r11"),  -- l.56 `adcx %r11, %rax`
    .adox "%rbx" (.reg "%r12"),  -- l.57 `adox %r12, %rbx`
    .mulxMem "%r12" "%r11" (.reg "%rdx") "%rsi" 8,  -- l.58 `mulxq 8(%rsi), %r11, %r12`
    .adcx "%rbx" (.reg "%r11"),  -- l.59 `adcx %r11, %rbx`
    .adox "%r13" (.reg "%r12"),  -- l.60 `adox %r12, %r13`
    .mulxMem "%r12" "%r11" (.reg "%rdx") "%rsi" 16,  -- l.61 `mulxq 16(%rsi), %r11, %r12`
    .adcx "%r13" (.reg "%r11"),  -- l.62 `adcx %r11, %r13`
    .adox "%r14" (.reg "%r12"),  -- l.63 `adox %r12, %r14`
    .mulxMem "%r15" "%r11" (.reg "%rdx") "%rsi" 24,  -- l.64 `mulxq 24(%rsi), %r11, %r15`
    .adcx "%r14" (.reg "%r11"),  -- l.65 `adcx %r11, %r14`
    .adox "%r15" (.reg "%rbp"),  -- l.66 `adox %rbp, %r15`
    .adcx "%r15" (.reg "%rbp"),  -- l.67 `adcx %rbp, %r15`
    .mov "%rdx" (.imm 38),  -- l.68 `movq $38, %rdx`
    .mulx "%r12" "%r11" (.reg "%rdx") (.reg "%r15"),  -- l.69 `mulx %r15, %r11, %r12`
    .add "%r11" (.reg "%rax"),  -- l.70 `addq %rax, %r11`
    .adc "%r12" (.reg "%rbp"),  -- l.71 `adcq %rbp, %r12`
    .mov "%rcx" (.reg "%r11"),  -- l.72 `movq %r11, %rcx`
    .shr "%rcx" (.imm 63),  -- l.73 `shrq $63, %rcx`
    .shl "%r12" (.imm 1) ]  -- l.74 `shlq $1, %r12`

/-- Segment 4 of the body: the 32 instructions from source lines 75–106. -/
def fe25519MulShippedSeg04 : List (JInstr 64) :=
  [ .add "%r12" (.reg "%rcx"),  -- l.75 `addq %rcx, %r12`
    .add "%r12" (.imm 1),  -- l.76 `addq $1, %r12`
    .mov "%rcx" (.reg "%r12"),  -- l.77 `movq %r12, %rcx`
    .imulri "%r12" "%r12" 19,  -- l.78 `imulq $19, %r12, %r12`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.79 `xorq %rbp, %rbp`
    .adox "%r9" (.reg "%r12"),  -- l.80 `adox %r12, %r9`
    .mulx "%r12" "%r11" (.reg "%rdx") (.reg "%rbx"),  -- l.81 `mulx %rbx, %r11, %r12`
    .adcx "%r9" (.reg "%r11"),  -- l.82 `adcx %r11, %r9`
    .adox "%r8" (.reg "%r12"),  -- l.83 `adox %r12, %r8`
    .mulx "%r12" "%r11" (.reg "%rdx") (.reg "%r13"),  -- l.84 `mulx %r13, %r11, %r12`
    .adcx "%r8" (.reg "%r11"),  -- l.85 `adcx %r11, %r8`
    .adox "%r10" (.reg "%r12"),  -- l.86 `adox %r12, %r10`
    .mulx "%r12" "%r11" (.reg "%rdx") (.reg "%r14"),  -- l.87 `mulx %r14, %r11, %r12`
    .adcx "%r10" (.reg "%r11"),  -- l.88 `adcx %r11, %r10`
    .adox "%rax" (.reg "%r12"),  -- l.89 `adox %r12, %rax`
    .mulx "%r12" "%r11" (.reg "%rdx") (.reg "%r15"),  -- l.90 `mulx %r15, %r11, %r12`
    .adc "%rax" (.reg "%r11"),  -- l.91 `adcq %r11, %rax`
    .shl "%rcx" (.imm 63),  -- l.92 `shlq $63, %rcx`
    .mov "%r11" (.reg "%rax"),  -- l.93 `movq %rax, %r11`
    .sub "%r11" (.reg "%rcx"),  -- l.94 `subq %rcx, %r11`
    .shr "%r11" (.imm 63),  -- l.95 `shrq $63, %r11`
    .imulri "%r11" "%r11" 19,  -- l.96 `imulq $19, %r11, %r11`
    .sub "%r9" (.reg "%r11"),  -- l.97 `subq %r11, %r9`
    .sbb "%r8" (.reg "%rbp"),  -- l.98 `sbbq %rbp, %r8`
    .sbb "%r10" (.reg "%rbp"),  -- l.99 `sbbq %rbp, %r10`
    .sbb "%rax" (.reg "%rbp"),  -- l.100 `sbbq %rbp, %rax`
    .mov "%r12" (.imm 9223372036854775807),  -- l.101 `movq $9223372036854775807, %r12`
    .and_ "%rax" (.reg "%r12"),  -- l.102 `andq %r12, %rax`
    .storeMem "%rdi" 0 (.reg "%r9"),  -- l.103 `movq %r9, 0(%rdi)`
    .storeMem "%rdi" 8 (.reg "%r8"),  -- l.104 `movq %r8, 8(%rdi)`
    .storeMem "%rdi" 16 (.reg "%r10"),  -- l.105 `movq %r10, 16(%rdi)`
    .storeMem "%rdi" 24 (.reg "%rax") ]  -- l.106 `movq %rax, 24(%rdi)`

/-- Segment 5 of the body: the 6 instructions from source lines 107–112. -/
def fe25519MulShippedSeg05 : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" (-8),  -- l.107 `movq -8(%rsp), %rbx`
    .loadMem "%rbp" "%rsp" (-16),  -- l.108 `movq -16(%rsp), %rbp`
    .loadMem "%r12" "%rsp" (-24),  -- l.109 `movq -24(%rsp), %r12`
    .loadMem "%r13" "%rsp" (-32),  -- l.110 `movq -32(%rsp), %r13`
    .loadMem "%r14" "%rsp" (-40),  -- l.111 `movq -40(%rsp), %r14`
    .loadMem "%r15" "%rsp" (-48) ]  -- l.112 `movq -48(%rsp), %r15`

/-- The body of `fe25519_mul_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 5 segments. -/
def fe25519MulShippedBlock : List (JInstr 64) :=
  fe25519MulShippedSeg01 ++ fe25519MulShippedSeg02 ++ fe25519MulShippedSeg03 ++
  fe25519MulShippedSeg04 ++ fe25519MulShippedSeg05

/-- The frame instructions of `fe25519_mul_x86_from_lean` before the body,
    which the block omits: each `pushq r` as `leaq -8(%rsp), %rsp` followed by the
    store of `r` at `0(%rsp)`, and the stack allocation as the instruction the text
    contains. -/
def fe25519MulShippedPrologue : List (JInstr 64) :=
  []

/-- The frame instructions of `fe25519_mul_x86_from_lean` after the body,
    which the block omits, `ret` excluded: the stack release as the instruction the
    text contains, and each `popq r` as the load of `r` from `0(%rsp)` followed by
    `leaq 8(%rsp), %rsp`. -/
def fe25519MulShippedEpilogue : List (JInstr 64) :=
  []

/-- The block has 108 instructions; the count of each segment is computed by `rfl`. -/
theorem fe25519MulShippedBlock_length :
    fe25519MulShippedBlock.length = 108 := by
  unfold fe25519MulShippedBlock
  simp only [List.length_append]
  rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519MulShipped
