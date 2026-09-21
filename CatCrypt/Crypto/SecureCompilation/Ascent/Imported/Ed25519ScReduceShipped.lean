/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# `ed25519_sc_reduce_x86_from_lean` from the owned backend's output as a `JInstr 64` block

`ed25519ScReduceShippedBlock` is the body of the function
`ed25519_sc_reduce_x86_from_lean` in an x86-64 AT&T file printed by CatCrypt's
owned backend, translated instruction by instruction. The file's producer is
recorded in `PROVENANCE.md` next to it, where one exists.

## Provenance

* Source: `crates/catcrypt-ed25519/asm/ed25519_sc_reduce_x86_from_lean.s` in the
  `SSProve-lean` repository at commit `b294647590404f72dd82b5404e326511f3c055eb`
  (tracked and unchanged at that commit), file SHA-256
  `2da152df4996484a453efe2f8830e222f93278212d14c8a9dfb1b152a2362ed5`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 3 frame instructions,
  each checked by the importer: the stack allocation `leaq -240(%rsp), %rsp` and
  its release `leaq 240(%rsp), %rsp`; `ret`.
* `ed25519ScReduceShippedPrologue` and `ed25519ScReduceShippedEpilogue` are the
  frame instructions before and after the block, `ret` excluded: each `pushq r` as
  `lea "%rsp" "%rsp" "%rsp" 0 (-8)` followed by `storeMem "%rsp" 0 (.reg r)`, each
  `popq r` as `loadMem r "%rsp" 0` followed by `lea "%rsp" "%rsp" "%rsp" 0 8`, and
  the stack allocation and its release as the instruction the text contains. `lea`
  writes no flag, as `pushq` and `popq` write none.
* Every other instruction is kept, `%rsp`-relative moves included, as `storeMem
  "%rsp" off` and `loadMem r "%rsp" off`. Their offsets are relative to `%rsp`
  after the omitted allocation, and `%rsp` is constant in the body.
* The first 8 instructions store registers into `%rsp` slots and form segment 1.
* Registers keep their physical names (`"%rax"`, …, `"%r15"`, `"%rsp"`); no
  register allocation is involved.
* `JasminModel` keys memory by the name of the base register and a byte offset, at
  word granularity. A proof over this block is a statement about that model; it
  agrees with the processor where each base register holds one address throughout
  the block and distinct names address disjoint words.
* The block writes `%r14` between memory accesses through it, so the accesses
  through that register before and after the write share one memory bank in the
  model.

The block has 3570 instructions. Source instructions by mnemonic: `movq` 2329,
`xorq` 440, `andq` 280, `addq` 264, `shrq` 136, `imulq` 60, `mulx` 60, `subq` 1.

## Main definitions

* `ed25519ScReduceShippedSeg001` … `ed25519ScReduceShippedSeg113`: the block in
  113 segments, each a literal `List (JInstr 64)`. A segment ends after a call,
  after the entry run of `%rsp` stores, before the exit run of `%rsp` loads, and
  after 32 instructions.
* `ed25519ScReduceShippedPart01` … `ed25519ScReduceShippedPart08`: the segments
  in 8 parts of at most 16 consecutive segments, each with lemmas giving its
  instruction count.
* `ed25519ScReduceShippedBlock`: the block, the concatenation of the parts.
* `ed25519ScReduceShippedPrologue`, `ed25519ScReduceShippedEpilogue`: the frame
  instructions before and after the block.

## Main results

* `ed25519ScReduceShippedBlock_length`: the block has 3570 instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 8 instructions from source lines 6–13. -/
def ed25519ScReduceShippedSeg001 : List (JInstr 64) :=
  [ .storeMem "%rsp" 232 (.reg "%rdi"),  -- l.6 `movq %rdi, 232(%rsp)`
    .storeMem "%rsp" 224 (.reg "%rsi"),  -- l.7 `movq %rsi, 224(%rsp)`
    .storeMem "%rsp" 216 (.reg "%rbx"),  -- l.8 `movq %rbx, 216(%rsp)`
    .storeMem "%rsp" 208 (.reg "%rbp"),  -- l.9 `movq %rbp, 208(%rsp)`
    .storeMem "%rsp" 200 (.reg "%r12"),  -- l.10 `movq %r12, 200(%rsp)`
    .storeMem "%rsp" 192 (.reg "%r13"),  -- l.11 `movq %r13, 192(%rsp)`
    .storeMem "%rsp" 184 (.reg "%r14"),  -- l.12 `movq %r14, 184(%rsp)`
    .storeMem "%rsp" 176 (.reg "%r15") ]  -- l.13 `movq %r15, 176(%rsp)`

/-- Segment 2 of the body: the 32 instructions from source lines 14–45. -/
def ed25519ScReduceShippedSeg002 : List (JInstr 64) :=
  [ .mov "%r14" (.reg "%rsi"),  -- l.14 `movq %rsi, %r14`
    .loadMem "%r15" "%rsp" 232,  -- l.15 `movq 232(%rsp), %r15`
    .storeMem "%rsp" 136 (.reg "%r15"),  -- l.16 `movq %r15, 136(%rsp)`
    .loadMem "%rcx" "%rsp" 224,  -- l.17 `movq 224(%rsp), %rcx`
    .mov "%rax" (.imm 0),  -- l.18 `movq $0, %rax`
    .mov "%r15" (.reg "%rax"),  -- l.19 `movq %rax, %r15`
    .storeMem "%rsp" 144 (.reg "%r15"),  -- l.20 `movq %r15, 144(%rsp)`
    .mov "%rax" (.imm 1),  -- l.21 `movq $1, %rax`
    .mov "%r15" (.reg "%rax"),  -- l.22 `movq %rax, %r15`
    .storeMem "%rsp" 152 (.reg "%r15"),  -- l.23 `movq %r15, 152(%rsp)`
    .mov "%rax" (.imm 2),  -- l.24 `movq $2, %rax`
    .mov "%r15" (.reg "%rax"),  -- l.25 `movq %rax, %r15`
    .storeMem "%rsp" 160 (.reg "%r15"),  -- l.26 `movq %r15, 160(%rsp)`
    .mov "%rax" (.imm 3),  -- l.27 `movq $3, %rax`
    .mov "%r15" (.reg "%rax"),  -- l.28 `movq %rax, %r15`
    .storeMem "%rsp" 168 (.reg "%r15"),  -- l.29 `movq %r15, 168(%rsp)`
    .mov "%rax" (.imm 4),  -- l.30 `movq $4, %rax`
    .mov "%r9" (.reg "%rax"),  -- l.31 `movq %rax, %r9`
    .mov "%rax" (.imm 5),  -- l.32 `movq $5, %rax`
    .mov "%r10" (.reg "%rax"),  -- l.33 `movq %rax, %r10`
    .mov "%rax" (.imm 6),  -- l.34 `movq $6, %rax`
    .mov "%r11" (.reg "%rax"),  -- l.35 `movq %rax, %r11`
    .mov "%rax" (.imm 7),  -- l.36 `movq $7, %rax`
    .mov "%r12" (.reg "%rax"),  -- l.37 `movq %rax, %r12`
    .loadMem "%r14" "%rsp" 224,  -- l.38 `movq 224(%rsp), %r14`
    .loadMem "%r15" "%rsp" 144,  -- l.39 `movq 144(%rsp), %r15`
    .loadMemIdx "%r15" "%r14" "%r15" 8,  -- l.40 `movq (%r14, %r15, 8), %r15`
    .storeMem "%rsp" 72 (.reg "%r15"),  -- l.41 `movq %r15, 72(%rsp)`
    .loadMem "%r14" "%rsp" 224,  -- l.42 `movq 224(%rsp), %r14`
    .loadMem "%r15" "%rsp" 152,  -- l.43 `movq 152(%rsp), %r15`
    .loadMemIdx "%r15" "%r14" "%r15" 8,  -- l.44 `movq (%r14, %r15, 8), %r15`
    .storeMem "%rsp" 80 (.reg "%r15") ]  -- l.45 `movq %r15, 80(%rsp)`

/-- Segment 3 of the body: the 32 instructions from source lines 46–77. -/
def ed25519ScReduceShippedSeg003 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 224,  -- l.46 `movq 224(%rsp), %r14`
    .loadMem "%r15" "%rsp" 160,  -- l.47 `movq 160(%rsp), %r15`
    .loadMemIdx "%r15" "%r14" "%r15" 8,  -- l.48 `movq (%r14, %r15, 8), %r15`
    .storeMem "%rsp" 120 (.reg "%r15"),  -- l.49 `movq %r15, 120(%rsp)`
    .loadMem "%r14" "%rsp" 224,  -- l.50 `movq 224(%rsp), %r14`
    .loadMem "%r15" "%rsp" 168,  -- l.51 `movq 168(%rsp), %r15`
    .loadMemIdx "%r15" "%r14" "%r15" 8,  -- l.52 `movq (%r14, %r15, 8), %r15`
    .storeMem "%rsp" 128 (.reg "%r15"),  -- l.53 `movq %r15, 128(%rsp)`
    .loadMem "%r14" "%rsp" 224,  -- l.54 `movq 224(%rsp), %r14`
    .loadMemIdx "%r15" "%r14" "%r9" 8,  -- l.55 `movq (%r14, %r9, 8), %r15`
    .storeMem "%rsp" 0 (.reg "%r15"),  -- l.56 `movq %r15, 0(%rsp)`
    .loadMem "%r14" "%rsp" 224,  -- l.57 `movq 224(%rsp), %r14`
    .loadMemIdx "%r15" "%r14" "%r10" 8,  -- l.58 `movq (%r14, %r10, 8), %r15`
    .storeMem "%rsp" 48 (.reg "%r15"),  -- l.59 `movq %r15, 48(%rsp)`
    .loadMem "%r14" "%rsp" 224,  -- l.60 `movq 224(%rsp), %r14`
    .loadMemIdx "%r15" "%r14" "%r11" 8,  -- l.61 `movq (%r14, %r11, 8), %r15`
    .storeMem "%rsp" 56 (.reg "%r15"),  -- l.62 `movq %r15, 56(%rsp)`
    .loadMem "%r14" "%rsp" 224,  -- l.63 `movq 224(%rsp), %r14`
    .loadMemIdx "%r15" "%r14" "%r12" 8,  -- l.64 `movq (%r14, %r12, 8), %r15`
    .storeMem "%rsp" 64 (.reg "%r15"),  -- l.65 `movq %r15, 64(%rsp)`
    .mov "%rcx" (.imm 17121812371768873755),  -- l.66 `movq $17121812371768873755, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.67 `movq %rcx, %r15`
    .storeMem "%rsp" 8 (.reg "%r15"),  -- l.68 `movq %r15, 8(%rsp)`
    .mov "%rcx" (.imm 2379626136568277415),  -- l.69 `movq $2379626136568277415, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.70 `movq %rcx, %r15`
    .storeMem "%rsp" 16 (.reg "%r15"),  -- l.71 `movq %r15, 16(%rsp)`
    .mov "%rcx" (.imm 18446744073709551595),  -- l.72 `movq $18446744073709551595, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.73 `movq %rcx, %r15`
    .storeMem "%rsp" 24 (.reg "%r15"),  -- l.74 `movq %r15, 24(%rsp)`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.75 `movq $18446744073709551615, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.76 `movq %rcx, %r15`
    .storeMem "%rsp" 32 (.reg "%r15") ]  -- l.77 `movq %r15, 32(%rsp)`

/-- Segment 4 of the body: the 32 instructions from source lines 78–109. -/
def ed25519ScReduceShippedSeg004 : List (JInstr 64) :=
  [ .mov "%rcx" (.imm 15),  -- l.78 `movq $15, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.79 `movq %rcx, %r15`
    .storeMem "%rsp" 40 (.reg "%r15"),  -- l.80 `movq %r15, 40(%rsp)`
    .mov "%rcx" (.imm 6346243789798364141),  -- l.81 `movq $6346243789798364141, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.82 `movq %rcx, %r15`
    .storeMem "%rsp" 112 (.reg "%r15"),  -- l.83 `movq %r15, 112(%rsp)`
    .mov "%rcx" (.imm 1503914060200516822),  -- l.84 `movq $1503914060200516822, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.85 `movq %rcx, %r15`
    .storeMem "%rsp" 104 (.reg "%r15"),  -- l.86 `movq %r15, 104(%rsp)`
    .mov "%rcx" (.imm 0),  -- l.87 `movq $0, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.88 `movq %rcx, %r15`
    .storeMem "%rsp" 96 (.reg "%r15"),  -- l.89 `movq %r15, 96(%rsp)`
    .mov "%rcx" (.imm 1152921504606846976),  -- l.90 `movq $1152921504606846976, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.91 `movq %rcx, %r15`
    .storeMem "%rsp" 88 (.reg "%r15"),  -- l.92 `movq %r15, 88(%rsp)`
    .loadMem "%rcx" "%rsp" 72,  -- l.93 `movq 72(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 8,  -- l.94 `movq 8(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.95 `imulq %r15, %rcx`
    .mov "%r13" (.reg "%rcx"),  -- l.96 `movq %rcx, %r13`
    .loadMem "%rdx" "%rsp" 72,  -- l.97 `movq 72(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.98 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.99 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.100 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.101 `movq -128(%rsp), %rsi`
    .mov "%rax" (.reg "%rcx"),  -- l.102 `movq %rcx, %rax`
    .mov "%rcx" (.imm 0),  -- l.103 `movq $0, %rcx`
    .mov "%r11" (.reg "%r13"),  -- l.104 `movq %r13, %r11`
    .add "%r11" (.reg "%rcx"),  -- l.105 `addq %rcx, %r11`
    .mov "%rcx" (.reg "%r11"),  -- l.106 `movq %r11, %rcx`
    .mov "%r11" (.imm 0),  -- l.107 `movq $0, %r11`
    .mov "%r10" (.reg "%rcx"),  -- l.108 `movq %rcx, %r10`
    .add "%r10" (.reg "%r11") ]  -- l.109 `addq %r11, %r10`

/-- Segment 5 of the body: the 32 instructions from source lines 110–141. -/
def ed25519ScReduceShippedSeg005 : List (JInstr 64) :=
  [ .mov "%r11" (.reg "%r10"),  -- l.110 `movq %r10, %r11`
    .mov "%r10" (.imm 0),  -- l.111 `movq $0, %r10`
    .mov "%r9" (.reg "%r13"),  -- l.112 `movq %r13, %r9`
    .and_ "%r9" (.reg "%r10"),  -- l.113 `andq %r10, %r9`
    .mov "%r10" (.imm 0),  -- l.114 `movq $0, %r10`
    .mov "%r8" (.reg "%r13"),  -- l.115 `movq %r13, %r8`
    .xor_ "%r8" (.reg "%r10"),  -- l.116 `xorq %r10, %r8`
    .mov "%r10" (.imm 18446744073709551615),  -- l.117 `movq $18446744073709551615, %r10`
    .mov "%r13" (.reg "%rcx"),  -- l.118 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%r10"),  -- l.119 `xorq %r10, %r13`
    .mov "%r10" (.reg "%r8"),  -- l.120 `movq %r8, %r10`
    .and_ "%r10" (.reg "%r13"),  -- l.121 `andq %r13, %r10`
    .mov "%r8" (.reg "%r9"),  -- l.122 `movq %r9, %r8`
    .xor_ "%r8" (.reg "%r10"),  -- l.123 `xorq %r10, %r8`
    .mov "%r9" (.imm 63),  -- l.124 `movq $63, %r9`
    .mov "%r9" (.reg "%r8"),  -- l.125 `movq %r8, %r9`
    .shr "%r9" (.imm 63),  -- l.126 `shrq $63, %r9`
    .mov "%r8" (.reg "%rax"),  -- l.127 `movq %rax, %r8`
    .add "%r8" (.reg "%r9"),  -- l.128 `addq %r9, %r8`
    .mov "%rax" (.imm 0),  -- l.129 `movq $0, %rax`
    .mov "%r9" (.reg "%rcx"),  -- l.130 `movq %rcx, %r9`
    .and_ "%r9" (.reg "%rax"),  -- l.131 `andq %rax, %r9`
    .mov "%rax" (.imm 0),  -- l.132 `movq $0, %rax`
    .mov "%r10" (.reg "%rcx"),  -- l.133 `movq %rcx, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.134 `xorq %rax, %r10`
    .mov "%rax" (.imm 18446744073709551615),  -- l.135 `movq $18446744073709551615, %rax`
    .mov "%rcx" (.reg "%r11"),  -- l.136 `movq %r11, %rcx`
    .xor_ "%rcx" (.reg "%rax"),  -- l.137 `xorq %rax, %rcx`
    .mov "%rax" (.reg "%r10"),  -- l.138 `movq %r10, %rax`
    .and_ "%rax" (.reg "%rcx"),  -- l.139 `andq %rcx, %rax`
    .mov "%rcx" (.reg "%r9"),  -- l.140 `movq %r9, %rcx`
    .xor_ "%rcx" (.reg "%rax") ]  -- l.141 `xorq %rax, %rcx`

/-- Segment 6 of the body: the 32 instructions from source lines 142–173. -/
def ed25519ScReduceShippedSeg006 : List (JInstr 64) :=
  [ .mov "%rax" (.imm 63),  -- l.142 `movq $63, %rax`
    .mov "%rax" (.reg "%rcx"),  -- l.143 `movq %rcx, %rax`
    .shr "%rax" (.imm 63),  -- l.144 `shrq $63, %rax`
    .mov "%rcx" (.reg "%r8"),  -- l.145 `movq %r8, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.146 `addq %rax, %rcx`
    .mov "%rax" (.reg "%rcx"),  -- l.147 `movq %rcx, %rax`
    .loadMem "%rcx" "%rsp" 72,  -- l.148 `movq 72(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.149 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.150 `imulq %r15, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.151 `movq %rcx, %r8`
    .loadMem "%rdx" "%rsp" 72,  -- l.152 `movq 72(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.153 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.154 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.155 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.156 `movq -128(%rsp), %rsi`
    .mov "%r9" (.reg "%rcx"),  -- l.157 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%r8"),  -- l.158 `movq %r8, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.159 `addq %rax, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.160 `movq %rcx, %r10`
    .mov "%rcx" (.imm 0),  -- l.161 `movq $0, %rcx`
    .mov "%r11" (.reg "%r10"),  -- l.162 `movq %r10, %r11`
    .add "%r11" (.reg "%rcx"),  -- l.163 `addq %rcx, %r11`
    .mov "%rcx" (.reg "%r11"),  -- l.164 `movq %r11, %rcx`
    .mov "%r11" (.reg "%r8"),  -- l.165 `movq %r8, %r11`
    .and_ "%r11" (.reg "%rax"),  -- l.166 `andq %rax, %r11`
    .mov "%r13" (.reg "%r8"),  -- l.167 `movq %r8, %r13`
    .xor_ "%r13" (.reg "%rax"),  -- l.168 `xorq %rax, %r13`
    .mov "%rax" (.imm 18446744073709551615),  -- l.169 `movq $18446744073709551615, %rax`
    .mov "%r8" (.reg "%r10"),  -- l.170 `movq %r10, %r8`
    .xor_ "%r8" (.reg "%rax"),  -- l.171 `xorq %rax, %r8`
    .mov "%rax" (.reg "%r13"),  -- l.172 `movq %r13, %rax`
    .and_ "%rax" (.reg "%r8") ]  -- l.173 `andq %r8, %rax`

/-- Segment 7 of the body: the 32 instructions from source lines 174–205. -/
def ed25519ScReduceShippedSeg007 : List (JInstr 64) :=
  [ .mov "%r8" (.reg "%r11"),  -- l.174 `movq %r11, %r8`
    .xor_ "%r8" (.reg "%rax"),  -- l.175 `xorq %rax, %r8`
    .mov "%rax" (.imm 63),  -- l.176 `movq $63, %rax`
    .mov "%rax" (.reg "%r8"),  -- l.177 `movq %r8, %rax`
    .shr "%rax" (.imm 63),  -- l.178 `shrq $63, %rax`
    .mov "%r8" (.reg "%r9"),  -- l.179 `movq %r9, %r8`
    .add "%r8" (.reg "%rax"),  -- l.180 `addq %rax, %r8`
    .mov "%rax" (.imm 0),  -- l.181 `movq $0, %rax`
    .mov "%r9" (.reg "%r10"),  -- l.182 `movq %r10, %r9`
    .and_ "%r9" (.reg "%rax"),  -- l.183 `andq %rax, %r9`
    .mov "%rax" (.imm 0),  -- l.184 `movq $0, %rax`
    .mov "%r11" (.reg "%r10"),  -- l.185 `movq %r10, %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.186 `xorq %rax, %r11`
    .mov "%rax" (.imm 18446744073709551615),  -- l.187 `movq $18446744073709551615, %rax`
    .mov "%r10" (.reg "%rcx"),  -- l.188 `movq %rcx, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.189 `xorq %rax, %r10`
    .mov "%rax" (.reg "%r11"),  -- l.190 `movq %r11, %rax`
    .and_ "%rax" (.reg "%r10"),  -- l.191 `andq %r10, %rax`
    .mov "%r10" (.reg "%r9"),  -- l.192 `movq %r9, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.193 `xorq %rax, %r10`
    .mov "%rax" (.imm 63),  -- l.194 `movq $63, %rax`
    .mov "%rax" (.reg "%r10"),  -- l.195 `movq %r10, %rax`
    .shr "%rax" (.imm 63),  -- l.196 `shrq $63, %rax`
    .mov "%r9" (.reg "%r8"),  -- l.197 `movq %r8, %r9`
    .add "%r9" (.reg "%rax"),  -- l.198 `addq %rax, %r9`
    .mov "%rax" (.reg "%r9"),  -- l.199 `movq %r9, %rax`
    .loadMem "%r8" "%rsp" 72,  -- l.200 `movq 72(%rsp), %r8`
    .loadMem "%r15" "%rsp" 24,  -- l.201 `movq 24(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.202 `imulq %r15, %r8`
    .mov "%r9" (.reg "%r8"),  -- l.203 `movq %r8, %r9`
    .loadMem "%rdx" "%rsp" 72,  -- l.204 `movq 72(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24 ]  -- l.205 `movq 24(%rsp), %r14`

/-- Segment 8 of the body: the 32 instructions from source lines 206–237. -/
def ed25519ScReduceShippedSeg008 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.206 `movq %rcx, -128(%rsp)`
    .mulx "%r8" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.207 `mulx %r14, %rcx, %r8`
    .loadMem "%rcx" "%rsp" (-128),  -- l.208 `movq -128(%rsp), %rcx`
    .mov "%r10" (.reg "%r8"),  -- l.209 `movq %r8, %r10`
    .mov "%r8" (.reg "%r9"),  -- l.210 `movq %r9, %r8`
    .add "%r8" (.reg "%rax"),  -- l.211 `addq %rax, %r8`
    .mov "%r11" (.reg "%r8"),  -- l.212 `movq %r8, %r11`
    .mov "%r8" (.imm 0),  -- l.213 `movq $0, %r8`
    .mov "%r13" (.reg "%r11"),  -- l.214 `movq %r11, %r13`
    .add "%r13" (.reg "%r8"),  -- l.215 `addq %r8, %r13`
    .mov "%r8" (.reg "%r13"),  -- l.216 `movq %r13, %r8`
    .mov "%r13" (.reg "%r9"),  -- l.217 `movq %r9, %r13`
    .and_ "%r13" (.reg "%rax"),  -- l.218 `andq %rax, %r13`
    .mov "%rbp" (.reg "%r9"),  -- l.219 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rax"),  -- l.220 `xorq %rax, %rbp`
    .mov "%rax" (.imm 18446744073709551615),  -- l.221 `movq $18446744073709551615, %rax`
    .mov "%r9" (.reg "%r11"),  -- l.222 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rax"),  -- l.223 `xorq %rax, %r9`
    .mov "%rax" (.reg "%rbp"),  -- l.224 `movq %rbp, %rax`
    .and_ "%rax" (.reg "%r9"),  -- l.225 `andq %r9, %rax`
    .mov "%rbp" (.reg "%r13"),  -- l.226 `movq %r13, %rbp`
    .xor_ "%rbp" (.reg "%rax"),  -- l.227 `xorq %rax, %rbp`
    .mov "%rax" (.imm 63),  -- l.228 `movq $63, %rax`
    .mov "%rax" (.reg "%rbp"),  -- l.229 `movq %rbp, %rax`
    .shr "%rax" (.imm 63),  -- l.230 `shrq $63, %rax`
    .mov "%rbp" (.reg "%r10"),  -- l.231 `movq %r10, %rbp`
    .add "%rbp" (.reg "%rax"),  -- l.232 `addq %rax, %rbp`
    .mov "%rax" (.imm 0),  -- l.233 `movq $0, %rax`
    .mov "%r9" (.reg "%r11"),  -- l.234 `movq %r11, %r9`
    .and_ "%r9" (.reg "%rax"),  -- l.235 `andq %rax, %r9`
    .mov "%rax" (.imm 0),  -- l.236 `movq $0, %rax`
    .mov "%r10" (.reg "%r11") ]  -- l.237 `movq %r11, %r10`

/-- Segment 9 of the body: the 32 instructions from source lines 238–269. -/
def ed25519ScReduceShippedSeg009 : List (JInstr 64) :=
  [ .xor_ "%r10" (.reg "%rax"),  -- l.238 `xorq %rax, %r10`
    .mov "%rax" (.imm 18446744073709551615),  -- l.239 `movq $18446744073709551615, %rax`
    .mov "%r11" (.reg "%r8"),  -- l.240 `movq %r8, %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.241 `xorq %rax, %r11`
    .mov "%rax" (.reg "%r10"),  -- l.242 `movq %r10, %rax`
    .and_ "%rax" (.reg "%r11"),  -- l.243 `andq %r11, %rax`
    .mov "%r10" (.reg "%r9"),  -- l.244 `movq %r9, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.245 `xorq %rax, %r10`
    .mov "%rax" (.imm 63),  -- l.246 `movq $63, %rax`
    .mov "%rax" (.reg "%r10"),  -- l.247 `movq %r10, %rax`
    .shr "%rax" (.imm 63),  -- l.248 `shrq $63, %rax`
    .mov "%r9" (.reg "%rbp"),  -- l.249 `movq %rbp, %r9`
    .add "%r9" (.reg "%rax"),  -- l.250 `addq %rax, %r9`
    .mov "%rax" (.reg "%r9"),  -- l.251 `movq %r9, %rax`
    .loadMem "%rbp" "%rsp" 72,  -- l.252 `movq 72(%rsp), %rbp`
    .loadMem "%r15" "%rsp" 32,  -- l.253 `movq 32(%rsp), %r15`
    .imul "%rbp" (.reg "%r15"),  -- l.254 `imulq %r15, %rbp`
    .mov "%r9" (.reg "%rbp"),  -- l.255 `movq %rbp, %r9`
    .loadMem "%rdx" "%rsp" 72,  -- l.256 `movq 72(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.257 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.258 `movq %rcx, -128(%rsp)`
    .mulx "%rbp" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.259 `mulx %r14, %rcx, %rbp`
    .loadMem "%rcx" "%rsp" (-128),  -- l.260 `movq -128(%rsp), %rcx`
    .mov "%r10" (.reg "%rbp"),  -- l.261 `movq %rbp, %r10`
    .mov "%rbp" (.reg "%r9"),  -- l.262 `movq %r9, %rbp`
    .add "%rbp" (.reg "%rax"),  -- l.263 `addq %rax, %rbp`
    .mov "%r11" (.reg "%rbp"),  -- l.264 `movq %rbp, %r11`
    .mov "%rbp" (.imm 0),  -- l.265 `movq $0, %rbp`
    .mov "%r13" (.reg "%r11"),  -- l.266 `movq %r11, %r13`
    .add "%r13" (.reg "%rbp"),  -- l.267 `addq %rbp, %r13`
    .mov "%rbp" (.reg "%r13"),  -- l.268 `movq %r13, %rbp`
    .mov "%r13" (.reg "%r9") ]  -- l.269 `movq %r9, %r13`

/-- Segment 10 of the body: the 32 instructions from source lines 270–301. -/
def ed25519ScReduceShippedSeg010 : List (JInstr 64) :=
  [ .and_ "%r13" (.reg "%rax"),  -- l.270 `andq %rax, %r13`
    .mov "%rbx" (.reg "%r9"),  -- l.271 `movq %r9, %rbx`
    .xor_ "%rbx" (.reg "%rax"),  -- l.272 `xorq %rax, %rbx`
    .mov "%rax" (.imm 18446744073709551615),  -- l.273 `movq $18446744073709551615, %rax`
    .mov "%r9" (.reg "%r11"),  -- l.274 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rax"),  -- l.275 `xorq %rax, %r9`
    .mov "%rax" (.reg "%rbx"),  -- l.276 `movq %rbx, %rax`
    .and_ "%rax" (.reg "%r9"),  -- l.277 `andq %r9, %rax`
    .mov "%rbx" (.reg "%r13"),  -- l.278 `movq %r13, %rbx`
    .xor_ "%rbx" (.reg "%rax"),  -- l.279 `xorq %rax, %rbx`
    .mov "%rax" (.imm 63),  -- l.280 `movq $63, %rax`
    .mov "%rax" (.reg "%rbx"),  -- l.281 `movq %rbx, %rax`
    .shr "%rax" (.imm 63),  -- l.282 `shrq $63, %rax`
    .mov "%rbx" (.reg "%r10"),  -- l.283 `movq %r10, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.284 `addq %rax, %rbx`
    .mov "%rax" (.imm 0),  -- l.285 `movq $0, %rax`
    .mov "%r9" (.reg "%r11"),  -- l.286 `movq %r11, %r9`
    .and_ "%r9" (.reg "%rax"),  -- l.287 `andq %rax, %r9`
    .mov "%rax" (.imm 0),  -- l.288 `movq $0, %rax`
    .mov "%r10" (.reg "%r11"),  -- l.289 `movq %r11, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.290 `xorq %rax, %r10`
    .mov "%rax" (.imm 18446744073709551615),  -- l.291 `movq $18446744073709551615, %rax`
    .mov "%r11" (.reg "%rbp"),  -- l.292 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.293 `xorq %rax, %r11`
    .mov "%rax" (.reg "%r10"),  -- l.294 `movq %r10, %rax`
    .and_ "%rax" (.reg "%r11"),  -- l.295 `andq %r11, %rax`
    .mov "%r10" (.reg "%r9"),  -- l.296 `movq %r9, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.297 `xorq %rax, %r10`
    .mov "%rax" (.imm 63),  -- l.298 `movq $63, %rax`
    .mov "%rax" (.reg "%r10"),  -- l.299 `movq %r10, %rax`
    .shr "%rax" (.imm 63),  -- l.300 `shrq $63, %rax`
    .mov "%r9" (.reg "%rbx") ]  -- l.301 `movq %rbx, %r9`

/-- Segment 11 of the body: the 32 instructions from source lines 302–333. -/
def ed25519ScReduceShippedSeg011 : List (JInstr 64) :=
  [ .add "%r9" (.reg "%rax"),  -- l.302 `addq %rax, %r9`
    .mov "%rax" (.reg "%r9"),  -- l.303 `movq %r9, %rax`
    .loadMem "%rbx" "%rsp" 72,  -- l.304 `movq 72(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 40,  -- l.305 `movq 40(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.306 `imulq %r15, %rbx`
    .mov "%r9" (.reg "%rbx"),  -- l.307 `movq %rbx, %r9`
    .loadMem "%rdx" "%rsp" 72,  -- l.308 `movq 72(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.309 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.310 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.311 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.312 `movq -128(%rsp), %rcx`
    .mov "%r10" (.reg "%rbx"),  -- l.313 `movq %rbx, %r10`
    .mov "%rbx" (.reg "%r9"),  -- l.314 `movq %r9, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.315 `addq %rax, %rbx`
    .mov "%r11" (.reg "%rbx"),  -- l.316 `movq %rbx, %r11`
    .mov "%rbx" (.imm 0),  -- l.317 `movq $0, %rbx`
    .mov "%r13" (.reg "%r11"),  -- l.318 `movq %r11, %r13`
    .add "%r13" (.reg "%rbx"),  -- l.319 `addq %rbx, %r13`
    .mov "%rbx" (.reg "%r13"),  -- l.320 `movq %r13, %rbx`
    .mov "%r13" (.reg "%r9"),  -- l.321 `movq %r9, %r13`
    .and_ "%r13" (.reg "%rax"),  -- l.322 `andq %rax, %r13`
    .mov "%rsi" (.reg "%r9"),  -- l.323 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.324 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.325 `movq $18446744073709551615, %rax`
    .mov "%r9" (.reg "%r11"),  -- l.326 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rax"),  -- l.327 `xorq %rax, %r9`
    .mov "%rax" (.reg "%rsi"),  -- l.328 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%r9"),  -- l.329 `andq %r9, %rax`
    .mov "%rsi" (.reg "%r13"),  -- l.330 `movq %r13, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.331 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.332 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi") ]  -- l.333 `movq %rsi, %rax`

/-- Segment 12 of the body: the 32 instructions from source lines 334–365. -/
def ed25519ScReduceShippedSeg012 : List (JInstr 64) :=
  [ .shr "%rax" (.imm 63),  -- l.334 `shrq $63, %rax`
    .mov "%rsi" (.reg "%r10"),  -- l.335 `movq %r10, %rsi`
    .add "%rsi" (.reg "%rax"),  -- l.336 `addq %rax, %rsi`
    .mov "%rax" (.imm 0),  -- l.337 `movq $0, %rax`
    .mov "%r9" (.reg "%r11"),  -- l.338 `movq %r11, %r9`
    .and_ "%r9" (.reg "%rax"),  -- l.339 `andq %rax, %r9`
    .mov "%rax" (.imm 0),  -- l.340 `movq $0, %rax`
    .mov "%r10" (.reg "%r11"),  -- l.341 `movq %r11, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.342 `xorq %rax, %r10`
    .mov "%rax" (.imm 18446744073709551615),  -- l.343 `movq $18446744073709551615, %rax`
    .mov "%r11" (.reg "%rbx"),  -- l.344 `movq %rbx, %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.345 `xorq %rax, %r11`
    .mov "%rax" (.reg "%r10"),  -- l.346 `movq %r10, %rax`
    .and_ "%rax" (.reg "%r11"),  -- l.347 `andq %r11, %rax`
    .mov "%r10" (.reg "%r9"),  -- l.348 `movq %r9, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.349 `xorq %rax, %r10`
    .mov "%rax" (.imm 63),  -- l.350 `movq $63, %rax`
    .mov "%rax" (.reg "%r10"),  -- l.351 `movq %r10, %rax`
    .shr "%rax" (.imm 63),  -- l.352 `shrq $63, %rax`
    .mov "%r9" (.reg "%rsi"),  -- l.353 `movq %rsi, %r9`
    .add "%r9" (.reg "%rax"),  -- l.354 `addq %rax, %r9`
    .mov "%rax" (.reg "%r9"),  -- l.355 `movq %r9, %rax`
    .loadMem "%rsi" "%rsp" 80,  -- l.356 `movq 80(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 8,  -- l.357 `movq 8(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.358 `imulq %r15, %rsi`
    .mov "%r9" (.reg "%rsi"),  -- l.359 `movq %rsi, %r9`
    .loadMem "%rdx" "%rsp" 80,  -- l.360 `movq 80(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.361 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.362 `movq %rcx, -128(%rsp)`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.363 `mulx %r14, %rcx, %rsi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.364 `movq -128(%rsp), %rcx`
    .mov "%r10" (.reg "%rsi") ]  -- l.365 `movq %rsi, %r10`

/-- Segment 13 of the body: the 32 instructions from source lines 366–397. -/
def ed25519ScReduceShippedSeg013 : List (JInstr 64) :=
  [ .mov "%rsi" (.imm 0),  -- l.366 `movq $0, %rsi`
    .mov "%r11" (.reg "%r9"),  -- l.367 `movq %r9, %r11`
    .add "%r11" (.reg "%rsi"),  -- l.368 `addq %rsi, %r11`
    .mov "%rsi" (.reg "%r11"),  -- l.369 `movq %r11, %rsi`
    .mov "%r11" (.reg "%rsi"),  -- l.370 `movq %rsi, %r11`
    .add "%r11" (.reg "%rcx"),  -- l.371 `addq %rcx, %r11`
    .mov "%r13" (.reg "%r11"),  -- l.372 `movq %r11, %r13`
    .mov "%r11" (.imm 0),  -- l.373 `movq $0, %r11`
    .mov "%r12" (.reg "%r9"),  -- l.374 `movq %r9, %r12`
    .and_ "%r12" (.reg "%r11"),  -- l.375 `andq %r11, %r12`
    .mov "%r11" (.imm 0),  -- l.376 `movq $0, %r11`
    .mov "%rdi" (.reg "%r9"),  -- l.377 `movq %r9, %rdi`
    .xor_ "%rdi" (.reg "%r11"),  -- l.378 `xorq %r11, %rdi`
    .mov "%r9" (.imm 18446744073709551615),  -- l.379 `movq $18446744073709551615, %r9`
    .mov "%r11" (.reg "%rsi"),  -- l.380 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%r9"),  -- l.381 `xorq %r9, %r11`
    .mov "%r9" (.reg "%rdi"),  -- l.382 `movq %rdi, %r9`
    .and_ "%r9" (.reg "%r11"),  -- l.383 `andq %r11, %r9`
    .mov "%rdi" (.reg "%r12"),  -- l.384 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%r9"),  -- l.385 `xorq %r9, %rdi`
    .mov "%r9" (.imm 63),  -- l.386 `movq $63, %r9`
    .mov "%r9" (.reg "%rdi"),  -- l.387 `movq %rdi, %r9`
    .shr "%r9" (.imm 63),  -- l.388 `shrq $63, %r9`
    .mov "%rdi" (.reg "%r10"),  -- l.389 `movq %r10, %rdi`
    .add "%rdi" (.reg "%r9"),  -- l.390 `addq %r9, %rdi`
    .mov "%r9" (.reg "%rsi"),  -- l.391 `movq %rsi, %r9`
    .and_ "%r9" (.reg "%rcx"),  -- l.392 `andq %rcx, %r9`
    .mov "%r10" (.reg "%rsi"),  -- l.393 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%rcx"),  -- l.394 `xorq %rcx, %r10`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.395 `movq $18446744073709551615, %rcx`
    .mov "%rsi" (.reg "%r13"),  -- l.396 `movq %r13, %rsi`
    .xor_ "%rsi" (.reg "%rcx") ]  -- l.397 `xorq %rcx, %rsi`

/-- Segment 14 of the body: the 32 instructions from source lines 398–429. -/
def ed25519ScReduceShippedSeg014 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%r10"),  -- l.398 `movq %r10, %rcx`
    .and_ "%rcx" (.reg "%rsi"),  -- l.399 `andq %rsi, %rcx`
    .mov "%rsi" (.reg "%r9"),  -- l.400 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rcx"),  -- l.401 `xorq %rcx, %rsi`
    .mov "%rcx" (.imm 63),  -- l.402 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rsi"),  -- l.403 `movq %rsi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.404 `shrq $63, %rcx`
    .mov "%rsi" (.reg "%rdi"),  -- l.405 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.406 `addq %rcx, %rsi`
    .mov "%rcx" (.reg "%rsi"),  -- l.407 `movq %rsi, %rcx`
    .loadMem "%rsi" "%rsp" 80,  -- l.408 `movq 80(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 16,  -- l.409 `movq 16(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.410 `imulq %r15, %rsi`
    .mov "%rdi" (.reg "%rsi"),  -- l.411 `movq %rsi, %rdi`
    .loadMem "%rdx" "%rsp" 80,  -- l.412 `movq 80(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.413 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.414 `movq %rcx, -128(%rsp)`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.415 `mulx %r14, %rcx, %rsi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.416 `movq -128(%rsp), %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.417 `movq %rsi, %r9`
    .mov "%rsi" (.reg "%rdi"),  -- l.418 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.419 `addq %rcx, %rsi`
    .mov "%r10" (.reg "%rsi"),  -- l.420 `movq %rsi, %r10`
    .mov "%rsi" (.reg "%r10"),  -- l.421 `movq %r10, %rsi`
    .add "%rsi" (.reg "%r8"),  -- l.422 `addq %r8, %rsi`
    .mov "%r11" (.reg "%rsi"),  -- l.423 `movq %rsi, %r11`
    .mov "%rsi" (.reg "%rdi"),  -- l.424 `movq %rdi, %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.425 `andq %rcx, %rsi`
    .mov "%r12" (.reg "%rdi"),  -- l.426 `movq %rdi, %r12`
    .xor_ "%r12" (.reg "%rcx"),  -- l.427 `xorq %rcx, %r12`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.428 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%r10") ]  -- l.429 `movq %r10, %rdi`

/-- Segment 15 of the body: the 32 instructions from source lines 430–461. -/
def ed25519ScReduceShippedSeg015 : List (JInstr 64) :=
  [ .xor_ "%rdi" (.reg "%rcx"),  -- l.430 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r12"),  -- l.431 `movq %r12, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.432 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.433 `movq %rsi, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.434 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.435 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.436 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.437 `shrq $63, %rcx`
    .mov "%rsi" (.reg "%r9"),  -- l.438 `movq %r9, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.439 `addq %rcx, %rsi`
    .mov "%rcx" (.reg "%r10"),  -- l.440 `movq %r10, %rcx`
    .and_ "%rcx" (.reg "%r8"),  -- l.441 `andq %r8, %rcx`
    .mov "%rdi" (.reg "%r10"),  -- l.442 `movq %r10, %rdi`
    .xor_ "%rdi" (.reg "%r8"),  -- l.443 `xorq %r8, %rdi`
    .mov "%r8" (.imm 18446744073709551615),  -- l.444 `movq $18446744073709551615, %r8`
    .mov "%r9" (.reg "%r11"),  -- l.445 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%r8"),  -- l.446 `xorq %r8, %r9`
    .mov "%r8" (.reg "%rdi"),  -- l.447 `movq %rdi, %r8`
    .and_ "%r8" (.reg "%r9"),  -- l.448 `andq %r9, %r8`
    .mov "%rdi" (.reg "%rcx"),  -- l.449 `movq %rcx, %rdi`
    .xor_ "%rdi" (.reg "%r8"),  -- l.450 `xorq %r8, %rdi`
    .mov "%rcx" (.imm 63),  -- l.451 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.452 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.453 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.454 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.455 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rdi"),  -- l.456 `movq %rdi, %rcx`
    .loadMem "%rsi" "%rsp" 80,  -- l.457 `movq 80(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 24,  -- l.458 `movq 24(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.459 `imulq %r15, %rsi`
    .mov "%rdi" (.reg "%rsi"),  -- l.460 `movq %rsi, %rdi`
    .loadMem "%rdx" "%rsp" 80 ]  -- l.461 `movq 80(%rsp), %rdx`

/-- Segment 16 of the body: the 32 instructions from source lines 462–493. -/
def ed25519ScReduceShippedSeg016 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 24,  -- l.462 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.463 `movq %rcx, -128(%rsp)`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.464 `mulx %r14, %rcx, %rsi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.465 `movq -128(%rsp), %rcx`
    .mov "%r8" (.reg "%rsi"),  -- l.466 `movq %rsi, %r8`
    .mov "%rsi" (.reg "%rdi"),  -- l.467 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.468 `addq %rcx, %rsi`
    .mov "%r9" (.reg "%rsi"),  -- l.469 `movq %rsi, %r9`
    .mov "%rsi" (.reg "%r9"),  -- l.470 `movq %r9, %rsi`
    .add "%rsi" (.reg "%rbp"),  -- l.471 `addq %rbp, %rsi`
    .mov "%r10" (.reg "%rsi"),  -- l.472 `movq %rsi, %r10`
    .mov "%rsi" (.reg "%rdi"),  -- l.473 `movq %rdi, %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.474 `andq %rcx, %rsi`
    .mov "%r12" (.reg "%rdi"),  -- l.475 `movq %rdi, %r12`
    .xor_ "%r12" (.reg "%rcx"),  -- l.476 `xorq %rcx, %r12`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.477 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%r9"),  -- l.478 `movq %r9, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.479 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r12"),  -- l.480 `movq %r12, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.481 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.482 `movq %rsi, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.483 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.484 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.485 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.486 `shrq $63, %rcx`
    .mov "%rsi" (.reg "%r8"),  -- l.487 `movq %r8, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.488 `addq %rcx, %rsi`
    .mov "%rcx" (.reg "%r9"),  -- l.489 `movq %r9, %rcx`
    .and_ "%rcx" (.reg "%rbp"),  -- l.490 `andq %rbp, %rcx`
    .mov "%rdi" (.reg "%r9"),  -- l.491 `movq %r9, %rdi`
    .xor_ "%rdi" (.reg "%rbp"),  -- l.492 `xorq %rbp, %rdi`
    .mov "%rbp" (.imm 18446744073709551615) ]  -- l.493 `movq $18446744073709551615, %rbp`

/-- Segment 17 of the body: the 32 instructions from source lines 494–525. -/
def ed25519ScReduceShippedSeg017 : List (JInstr 64) :=
  [ .mov "%r8" (.reg "%r10"),  -- l.494 `movq %r10, %r8`
    .xor_ "%r8" (.reg "%rbp"),  -- l.495 `xorq %rbp, %r8`
    .mov "%rbp" (.reg "%rdi"),  -- l.496 `movq %rdi, %rbp`
    .and_ "%rbp" (.reg "%r8"),  -- l.497 `andq %r8, %rbp`
    .mov "%rdi" (.reg "%rcx"),  -- l.498 `movq %rcx, %rdi`
    .xor_ "%rdi" (.reg "%rbp"),  -- l.499 `xorq %rbp, %rdi`
    .mov "%rcx" (.imm 63),  -- l.500 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.501 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.502 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.503 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.504 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rdi"),  -- l.505 `movq %rdi, %rcx`
    .loadMem "%rsi" "%rsp" 80,  -- l.506 `movq 80(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 32,  -- l.507 `movq 32(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.508 `imulq %r15, %rsi`
    .mov "%rdi" (.reg "%rsi"),  -- l.509 `movq %rsi, %rdi`
    .loadMem "%rdx" "%rsp" 80,  -- l.510 `movq 80(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.511 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.512 `movq %rcx, -128(%rsp)`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.513 `mulx %r14, %rcx, %rsi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.514 `movq -128(%rsp), %rcx`
    .mov "%rbp" (.reg "%rsi"),  -- l.515 `movq %rsi, %rbp`
    .mov "%rsi" (.reg "%rdi"),  -- l.516 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.517 `addq %rcx, %rsi`
    .mov "%r8" (.reg "%rsi"),  -- l.518 `movq %rsi, %r8`
    .mov "%rsi" (.reg "%r8"),  -- l.519 `movq %r8, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.520 `addq %rbx, %rsi`
    .mov "%r9" (.reg "%rsi"),  -- l.521 `movq %rsi, %r9`
    .mov "%rsi" (.reg "%rdi"),  -- l.522 `movq %rdi, %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.523 `andq %rcx, %rsi`
    .mov "%r12" (.reg "%rdi"),  -- l.524 `movq %rdi, %r12`
    .xor_ "%r12" (.reg "%rcx") ]  -- l.525 `xorq %rcx, %r12`

/-- Segment 18 of the body: the 32 instructions from source lines 526–557. -/
def ed25519ScReduceShippedSeg018 : List (JInstr 64) :=
  [ .mov "%rcx" (.imm 18446744073709551615),  -- l.526 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%r8"),  -- l.527 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.528 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r12"),  -- l.529 `movq %r12, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.530 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.531 `movq %rsi, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.532 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.533 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.534 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.535 `shrq $63, %rcx`
    .mov "%rsi" (.reg "%rbp"),  -- l.536 `movq %rbp, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.537 `addq %rcx, %rsi`
    .mov "%rcx" (.reg "%r8"),  -- l.538 `movq %r8, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.539 `andq %rbx, %rcx`
    .mov "%rdi" (.reg "%r8"),  -- l.540 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.541 `xorq %rbx, %rdi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.542 `movq $18446744073709551615, %rbx`
    .mov "%rbp" (.reg "%r9"),  -- l.543 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rbx"),  -- l.544 `xorq %rbx, %rbp`
    .mov "%rbx" (.reg "%rdi"),  -- l.545 `movq %rdi, %rbx`
    .and_ "%rbx" (.reg "%rbp"),  -- l.546 `andq %rbp, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.547 `movq %rcx, %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.548 `xorq %rbx, %rdi`
    .mov "%rbx" (.imm 63),  -- l.549 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rdi"),  -- l.550 `movq %rdi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.551 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rsi"),  -- l.552 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.553 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.554 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 80,  -- l.555 `movq 80(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.556 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15") ]  -- l.557 `imulq %r15, %rcx`

/-- Segment 19 of the body: the 32 instructions from source lines 558–589. -/
def ed25519ScReduceShippedSeg019 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rcx"),  -- l.558 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 80,  -- l.559 `movq 80(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.560 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.561 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.562 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.563 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.564 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.565 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.566 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.567 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.568 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.569 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.570 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.571 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.572 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.573 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.574 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.575 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.576 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.577 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.578 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.579 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.580 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.581 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.582 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.583 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.584 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.585 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.586 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.587 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.588 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp") ]  -- l.589 `movq %rbp, %rsi`

/-- Segment 20 of the body: the 32 instructions from source lines 590–621. -/
def ed25519ScReduceShippedSeg020 : List (JInstr 64) :=
  [ .xor_ "%rsi" (.reg "%rax"),  -- l.590 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.591 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.592 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.593 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.594 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.595 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.596 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.597 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.598 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.599 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.600 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.601 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.602 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.603 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 120,  -- l.604 `movq 120(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8,  -- l.605 `movq 8(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.606 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.607 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 120,  -- l.608 `movq 120(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.609 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.610 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.611 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.612 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.613 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.614 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.615 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.616 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.617 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.618 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r11"),  -- l.619 `addq %r11, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.620 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0) ]  -- l.621 `movq $0, %rdi`

/-- Segment 21 of the body: the 32 instructions from source lines 622–653. -/
def ed25519ScReduceShippedSeg021 : List (JInstr 64) :=
  [ .mov "%r12" (.reg "%rcx"),  -- l.622 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rdi"),  -- l.623 `andq %rdi, %r12`
    .mov "%rdi" (.imm 0),  -- l.624 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.625 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.626 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.627 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.628 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.629 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.630 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.631 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r12"),  -- l.632 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.633 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.634 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.635 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.636 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.637 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.638 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.639 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r11"),  -- l.640 `andq %r11, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.641 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.642 `xorq %r11, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.643 `movq $18446744073709551615, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.644 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.645 `xorq %rbx, %r11`
    .mov "%rbx" (.reg "%rsi"),  -- l.646 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.647 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.648 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.649 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.650 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.651 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.652 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi") ]  -- l.653 `movq %rdi, %rcx`

/-- Segment 22 of the body: the 32 instructions from source lines 654–685. -/
def ed25519ScReduceShippedSeg022 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%rbx"),  -- l.654 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.655 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 120,  -- l.656 `movq 120(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.657 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.658 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.659 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 120,  -- l.660 `movq 120(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.661 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.662 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.663 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.664 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.665 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.666 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.667 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.668 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.669 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.670 `addq %r10, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.671 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.672 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.673 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.674 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.675 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.676 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.677 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.678 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.679 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.680 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.681 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.682 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.683 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.684 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63) ]  -- l.685 `shrq $63, %rbx`

/-- Segment 23 of the body: the 32 instructions from source lines 686–717. -/
def ed25519ScReduceShippedSeg023 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rdi"),  -- l.686 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.687 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.688 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.689 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.690 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.691 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.692 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r11"),  -- l.693 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.694 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.695 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.696 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.697 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.698 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.699 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.700 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.701 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.702 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.703 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.704 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 120,  -- l.705 `movq 120(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.706 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.707 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.708 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 120,  -- l.709 `movq 120(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.710 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.711 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.712 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.713 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.714 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.715 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.716 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx") ]  -- l.717 `movq %rcx, %rbp`

/-- Segment 24 of the body: the 32 instructions from source lines 718–749. -/
def ed25519ScReduceShippedSeg024 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rbp"),  -- l.718 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.719 `addq %r9, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.720 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.721 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.722 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.723 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.724 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.725 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.726 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.727 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.728 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.729 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.730 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.731 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.732 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.733 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.734 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.735 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.736 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.737 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.738 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.739 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.740 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.741 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.742 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.743 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.744 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.745 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.746 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.747 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.748 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi") ]  -- l.749 `movq %rsi, %rbx`

/-- Segment 25 of the body: the 32 instructions from source lines 750–781. -/
def ed25519ScReduceShippedSeg025 : List (JInstr 64) :=
  [ .shr "%rbx" (.imm 63),  -- l.750 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.751 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.752 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.753 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 120,  -- l.754 `movq 120(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.755 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.756 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.757 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 120,  -- l.758 `movq 120(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.759 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.760 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.761 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.762 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.763 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.764 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.765 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.766 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.767 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.768 `addq %r8, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.769 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.770 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.771 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.772 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.773 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.774 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.775 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.776 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.777 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.778 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.779 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.780 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63) ]  -- l.781 `movq $63, %rbx`

/-- Segment 26 of the body: the 32 instructions from source lines 782–813. -/
def ed25519ScReduceShippedSeg026 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%rsi"),  -- l.782 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.783 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.784 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.785 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.786 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.787 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.788 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.789 `xorq %r8, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.790 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9"),  -- l.791 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.792 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.793 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.794 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.795 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.796 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.797 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.798 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.799 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.800 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.801 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.802 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 120,  -- l.803 `movq 120(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.804 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.805 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.806 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 120,  -- l.807 `movq 120(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.808 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.809 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.810 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.811 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.812 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi") ]  -- l.813 `movq %rsi, %rcx`

/-- Segment 27 of the body: the 32 instructions from source lines 814–845. -/
def ed25519ScReduceShippedSeg027 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%rbx"),  -- l.814 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.815 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.816 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.817 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.818 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.819 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.820 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.821 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.822 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.823 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.824 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.825 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.826 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.827 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.828 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.829 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.830 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.831 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.832 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.833 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.834 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.835 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.836 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.837 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.838 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.839 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.840 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.841 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.842 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.843 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.844 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax") ]  -- l.845 `xorq %rax, %rsi`

/-- Segment 28 of the body: the 32 instructions from source lines 846–877. -/
def ed25519ScReduceShippedSeg028 : List (JInstr 64) :=
  [ .mov "%rax" (.imm 63),  -- l.846 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.847 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.848 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.849 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.850 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.851 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 128,  -- l.852 `movq 128(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8,  -- l.853 `movq 8(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.854 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.855 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 128,  -- l.856 `movq 128(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.857 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.858 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.859 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.860 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.861 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.862 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.863 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.864 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.865 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.866 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r11"),  -- l.867 `addq %r11, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.868 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0),  -- l.869 `movq $0, %rdi`
    .mov "%r12" (.reg "%rcx"),  -- l.870 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rdi"),  -- l.871 `andq %rdi, %r12`
    .mov "%rdi" (.imm 0),  -- l.872 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.873 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.874 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.875 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.876 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx") ]  -- l.877 `xorq %rcx, %rdi`

/-- Segment 29 of the body: the 32 instructions from source lines 878–909. -/
def ed25519ScReduceShippedSeg029 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%r13"),  -- l.878 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.879 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r12"),  -- l.880 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.881 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.882 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.883 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.884 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.885 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.886 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.887 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r11"),  -- l.888 `andq %r11, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.889 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.890 `xorq %r11, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.891 `movq $18446744073709551615, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.892 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.893 `xorq %rbx, %r11`
    .mov "%rbx" (.reg "%rsi"),  -- l.894 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.895 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.896 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.897 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.898 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.899 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.900 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.901 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.902 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.903 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 128,  -- l.904 `movq 128(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.905 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.906 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.907 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 128,  -- l.908 `movq 128(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16 ]  -- l.909 `movq 16(%rsp), %r14`

/-- Segment 30 of the body: the 32 instructions from source lines 910–941. -/
def ed25519ScReduceShippedSeg030 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.910 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.911 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.912 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.913 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.914 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.915 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.916 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.917 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.918 `addq %r10, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.919 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.920 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.921 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.922 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.923 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.924 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.925 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.926 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.927 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.928 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.929 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.930 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.931 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.932 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.933 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.934 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.935 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.936 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.937 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.938 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.939 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.940 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r11") ]  -- l.941 `movq %r11, %rbp`

/-- Segment 31 of the body: the 32 instructions from source lines 942–973. -/
def ed25519ScReduceShippedSeg031 : List (JInstr 64) :=
  [ .xor_ "%rbp" (.reg "%rdi"),  -- l.942 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.943 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.944 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.945 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.946 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.947 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.948 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.949 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.950 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.951 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.952 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 128,  -- l.953 `movq 128(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.954 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.955 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.956 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 128,  -- l.957 `movq 128(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.958 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.959 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.960 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.961 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.962 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.963 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.964 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.965 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.966 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.967 `addq %r9, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.968 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.969 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.970 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.971 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.972 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615) ]  -- l.973 `movq $18446744073709551615, %rbx`

/-- Segment 32 of the body: the 32 instructions from source lines 974–1005. -/
def ed25519ScReduceShippedSeg032 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rbp"),  -- l.974 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.975 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.976 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.977 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.978 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.979 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.980 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.981 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.982 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.983 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.984 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.985 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.986 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.987 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.988 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.989 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.990 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.991 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.992 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.993 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.994 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.995 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.996 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.997 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.998 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.999 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1000 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1001 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 128,  -- l.1002 `movq 128(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.1003 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1004 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx") ]  -- l.1005 `movq %rcx, %rsi`

/-- Segment 33 of the body: the 32 instructions from source lines 1006–1037. -/
def ed25519ScReduceShippedSeg033 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsp" 128,  -- l.1006 `movq 128(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.1007 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1008 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1009 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1010 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1011 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1012 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1013 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1014 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1015 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.1016 `addq %r8, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.1017 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.1018 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1019 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1020 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1021 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1022 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1023 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1024 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1025 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1026 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1027 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1028 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1029 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1030 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1031 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1032 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1033 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1034 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.1035 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1036 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r8") ]  -- l.1037 `xorq %r8, %rsi`

/-- Segment 34 of the body: the 32 instructions from source lines 1038–1069. -/
def ed25519ScReduceShippedSeg034 : List (JInstr 64) :=
  [ .mov "%rdi" (.imm 18446744073709551615),  -- l.1038 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9"),  -- l.1039 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1040 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1041 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1042 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1043 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1044 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1045 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1046 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1047 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1048 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1049 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1050 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 128,  -- l.1051 `movq 128(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.1052 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1053 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1054 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 128,  -- l.1055 `movq 128(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.1056 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1057 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1058 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1059 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1060 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1061 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1062 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1063 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1064 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.1065 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.1066 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.1067 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1068 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi") ]  -- l.1069 `movq %rsi, %r12`

/-- Segment 35 of the body: the 32 instructions from source lines 1070–1101. -/
def ed25519ScReduceShippedSeg035 : List (JInstr 64) :=
  [ .xor_ "%r12" (.reg "%rbx"),  -- l.1070 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1071 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1072 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1073 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1074 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1075 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1076 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1077 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1078 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1079 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1080 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1081 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1082 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1083 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.1084 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1085 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1086 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1087 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.1088 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.1089 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.1090 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.1091 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.1092 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1093 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.1094 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.1095 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.1096 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.1097 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.1098 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.1099 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 0,  -- l.1100 `movq 0(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8 ]  -- l.1101 `movq 8(%rsp), %r15`

/-- Segment 36 of the body: the 32 instructions from source lines 1102–1133. -/
def ed25519ScReduceShippedSeg036 : List (JInstr 64) :=
  [ .imul "%rbx" (.reg "%r15"),  -- l.1102 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.1103 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 0,  -- l.1104 `movq 0(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.1105 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.1106 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1107 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.1108 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1109 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.1110 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.1111 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.1112 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.1113 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1114 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r11"),  -- l.1115 `addq %r11, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.1116 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0),  -- l.1117 `movq $0, %rdi`
    .mov "%r12" (.reg "%rcx"),  -- l.1118 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rdi"),  -- l.1119 `andq %rdi, %r12`
    .mov "%rdi" (.imm 0),  -- l.1120 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.1121 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.1122 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.1123 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1124 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1125 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.1126 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.1127 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r12"),  -- l.1128 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1129 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.1130 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1131 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.1132 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi") ]  -- l.1133 `movq %rsi, %rdi`

/-- Segment 37 of the body: the 32 instructions from source lines 1134–1165. -/
def ed25519ScReduceShippedSeg037 : List (JInstr 64) :=
  [ .add "%rdi" (.reg "%rcx"),  -- l.1134 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.1135 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r11"),  -- l.1136 `andq %r11, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1137 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.1138 `xorq %r11, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1139 `movq $18446744073709551615, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.1140 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.1141 `xorq %rbx, %r11`
    .mov "%rbx" (.reg "%rsi"),  -- l.1142 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.1143 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1144 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1145 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1146 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1147 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1148 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1149 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1150 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.1151 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 0,  -- l.1152 `movq 0(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.1153 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1154 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1155 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 0,  -- l.1156 `movq 0(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.1157 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1158 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1159 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1160 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1161 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1162 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1163 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1164 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp") ]  -- l.1165 `movq %rbp, %rcx`

/-- Segment 38 of the body: the 32 instructions from source lines 1166–1197. -/
def ed25519ScReduceShippedSeg038 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%r10"),  -- l.1166 `addq %r10, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.1167 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.1168 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1169 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1170 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1171 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1172 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1173 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1174 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1175 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1176 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1177 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1178 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1179 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1180 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1181 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1182 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1183 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1184 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.1185 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1186 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.1187 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1188 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r11"),  -- l.1189 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1190 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1191 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1192 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1193 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1194 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1195 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1196 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63) ]  -- l.1197 `shrq $63, %rbx`

/-- Segment 39 of the body: the 32 instructions from source lines 1198–1229. -/
def ed25519ScReduceShippedSeg039 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rcx"),  -- l.1198 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1199 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1200 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 0,  -- l.1201 `movq 0(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.1202 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1203 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1204 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 0,  -- l.1205 `movq 0(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.1206 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1207 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1208 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1209 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1210 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1211 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1212 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1213 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1214 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.1215 `addq %r9, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.1216 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.1217 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1218 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1219 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1220 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1221 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1222 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1223 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1224 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1225 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1226 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1227 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1228 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi") ]  -- l.1229 `movq %rsi, %rbx`

/-- Segment 40 of the body: the 32 instructions from source lines 1230–1261. -/
def ed25519ScReduceShippedSeg040 : List (JInstr 64) :=
  [ .shr "%rbx" (.imm 63),  -- l.1230 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1231 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1232 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1233 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.1234 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1235 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.1236 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1237 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.1238 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1239 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1240 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1241 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1242 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1243 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1244 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1245 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1246 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1247 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1248 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1249 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 0,  -- l.1250 `movq 0(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.1251 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1252 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1253 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 0,  -- l.1254 `movq 0(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.1255 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1256 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1257 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1258 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1259 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1260 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx") ]  -- l.1261 `addq %rbx, %rcx`

/-- Segment 41 of the body: the 32 instructions from source lines 1262–1293. -/
def ed25519ScReduceShippedSeg041 : List (JInstr 64) :=
  [ .mov "%rbp" (.reg "%rcx"),  -- l.1262 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1263 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.1264 `addq %r8, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.1265 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.1266 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1267 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1268 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1269 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1270 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1271 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1272 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1273 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1274 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1275 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1276 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1277 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1278 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1279 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1280 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1281 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1282 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.1283 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1284 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.1285 `xorq %r8, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1286 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9"),  -- l.1287 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1288 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1289 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1290 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1291 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1292 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63) ]  -- l.1293 `movq $63, %rbx`

/-- Segment 42 of the body: the 32 instructions from source lines 1294–1325. -/
def ed25519ScReduceShippedSeg042 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%rsi"),  -- l.1294 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1295 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1296 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1297 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1298 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 0,  -- l.1299 `movq 0(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.1300 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1301 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1302 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 0,  -- l.1303 `movq 0(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.1304 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1305 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1306 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1307 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1308 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1309 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1310 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1311 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1312 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.1313 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.1314 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.1315 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1316 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1317 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1318 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1319 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1320 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1321 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1322 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1323 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1324 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx") ]  -- l.1325 `xorq %rbx, %rsi`

/-- Segment 43 of the body: the 32 instructions from source lines 1326–1357. -/
def ed25519ScReduceShippedSeg043 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 63),  -- l.1326 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1327 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1328 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1329 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1330 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1331 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.1332 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1333 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1334 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1335 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.1336 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.1337 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.1338 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.1339 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.1340 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1341 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.1342 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.1343 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.1344 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.1345 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.1346 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.1347 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 48,  -- l.1348 `movq 48(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8,  -- l.1349 `movq 8(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.1350 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.1351 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 48,  -- l.1352 `movq 48(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.1353 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.1354 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1355 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.1356 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx") ]  -- l.1357 `movq %rbx, %rsi`

/-- Segment 44 of the body: the 32 instructions from source lines 1358–1389. -/
def ed25519ScReduceShippedSeg044 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 0),  -- l.1358 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.1359 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.1360 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.1361 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1362 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r11"),  -- l.1363 `addq %r11, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.1364 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0),  -- l.1365 `movq $0, %rdi`
    .mov "%r12" (.reg "%rcx"),  -- l.1366 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rdi"),  -- l.1367 `andq %rdi, %r12`
    .mov "%rdi" (.imm 0),  -- l.1368 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.1369 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.1370 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.1371 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1372 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1373 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.1374 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.1375 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r12"),  -- l.1376 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1377 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.1378 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1379 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.1380 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.1381 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.1382 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.1383 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r11"),  -- l.1384 `andq %r11, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1385 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.1386 `xorq %r11, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1387 `movq $18446744073709551615, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.1388 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rbx") ]  -- l.1389 `xorq %rbx, %r11`

/-- Segment 45 of the body: the 32 instructions from source lines 1390–1421. -/
def ed25519ScReduceShippedSeg045 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%rsi"),  -- l.1390 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.1391 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1392 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1393 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1394 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1395 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1396 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1397 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1398 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.1399 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 48,  -- l.1400 `movq 48(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.1401 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1402 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1403 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 48,  -- l.1404 `movq 48(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.1405 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1406 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1407 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1408 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1409 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1410 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1411 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1412 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1413 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.1414 `addq %r10, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.1415 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.1416 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1417 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1418 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1419 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1420 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp") ]  -- l.1421 `movq %rbp, %rsi`

/-- Segment 46 of the body: the 32 instructions from source lines 1422–1453. -/
def ed25519ScReduceShippedSeg046 : List (JInstr 64) :=
  [ .xor_ "%rsi" (.reg "%rbx"),  -- l.1422 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1423 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1424 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1425 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1426 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1427 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1428 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1429 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1430 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1431 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1432 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.1433 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1434 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.1435 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1436 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r11"),  -- l.1437 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1438 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1439 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1440 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1441 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1442 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1443 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1444 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1445 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1446 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1447 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1448 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 48,  -- l.1449 `movq 48(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.1450 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1451 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1452 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 48 ]  -- l.1453 `movq 48(%rsp), %rdx`

/-- Segment 47 of the body: the 32 instructions from source lines 1454–1485. -/
def ed25519ScReduceShippedSeg047 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 24,  -- l.1454 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1455 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1456 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1457 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1458 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1459 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1460 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1461 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1462 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.1463 `addq %r9, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.1464 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.1465 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1466 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1467 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1468 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1469 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1470 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1471 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1472 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1473 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1474 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1475 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1476 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1477 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1478 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1479 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1480 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1481 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.1482 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1483 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.1484 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615) ]  -- l.1485 `movq $18446744073709551615, %rdi`

/-- Segment 48 of the body: the 32 instructions from source lines 1486–1517. -/
def ed25519ScReduceShippedSeg048 : List (JInstr 64) :=
  [ .mov "%rbp" (.reg "%r10"),  -- l.1486 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1487 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1488 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1489 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1490 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1491 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1492 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1493 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1494 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1495 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1496 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1497 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 48,  -- l.1498 `movq 48(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.1499 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1500 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1501 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 48,  -- l.1502 `movq 48(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.1503 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1504 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1505 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1506 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1507 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1508 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1509 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1510 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1511 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.1512 `addq %r8, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.1513 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.1514 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1515 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1516 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx") ]  -- l.1517 `xorq %rbx, %r12`

/-- Segment 49 of the body: the 32 instructions from source lines 1518–1549. -/
def ed25519ScReduceShippedSeg049 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 18446744073709551615),  -- l.1518 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1519 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1520 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1521 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1522 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1523 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1524 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1525 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1526 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1527 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1528 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1529 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1530 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.1531 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1532 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.1533 `xorq %r8, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1534 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9"),  -- l.1535 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1536 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1537 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1538 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1539 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1540 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1541 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1542 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1543 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1544 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1545 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1546 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 48,  -- l.1547 `movq 48(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.1548 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15") ]  -- l.1549 `imulq %r15, %rcx`

/-- Segment 50 of the body: the 32 instructions from source lines 1550–1581. -/
def ed25519ScReduceShippedSeg050 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rcx"),  -- l.1550 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 48,  -- l.1551 `movq 48(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.1552 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1553 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1554 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1555 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1556 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1557 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1558 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1559 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1560 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.1561 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.1562 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.1563 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1564 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1565 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1566 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1567 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1568 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1569 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1570 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1571 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1572 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1573 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1574 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1575 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1576 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1577 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1578 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1579 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.1580 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp") ]  -- l.1581 `movq %rbp, %rsi`

/-- Segment 51 of the body: the 32 instructions from source lines 1582–1613. -/
def ed25519ScReduceShippedSeg051 : List (JInstr 64) :=
  [ .xor_ "%rsi" (.reg "%rax"),  -- l.1582 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1583 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.1584 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.1585 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.1586 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.1587 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.1588 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1589 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.1590 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.1591 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.1592 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.1593 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.1594 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.1595 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 56,  -- l.1596 `movq 56(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8,  -- l.1597 `movq 8(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.1598 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.1599 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 56,  -- l.1600 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.1601 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.1602 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1603 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.1604 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1605 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.1606 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.1607 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.1608 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.1609 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1610 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r11"),  -- l.1611 `addq %r11, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.1612 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0) ]  -- l.1613 `movq $0, %rdi`

/-- Segment 52 of the body: the 32 instructions from source lines 1614–1645. -/
def ed25519ScReduceShippedSeg052 : List (JInstr 64) :=
  [ .mov "%r12" (.reg "%rcx"),  -- l.1614 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rdi"),  -- l.1615 `andq %rdi, %r12`
    .mov "%rdi" (.imm 0),  -- l.1616 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.1617 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.1618 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.1619 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1620 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1621 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.1622 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.1623 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r12"),  -- l.1624 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1625 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.1626 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1627 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.1628 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.1629 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.1630 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.1631 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r11"),  -- l.1632 `andq %r11, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1633 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.1634 `xorq %r11, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1635 `movq $18446744073709551615, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.1636 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.1637 `xorq %rbx, %r11`
    .mov "%rbx" (.reg "%rsi"),  -- l.1638 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.1639 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1640 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1641 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1642 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1643 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1644 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi") ]  -- l.1645 `movq %rdi, %rcx`

/-- Segment 53 of the body: the 32 instructions from source lines 1646–1677. -/
def ed25519ScReduceShippedSeg053 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%rbx"),  -- l.1646 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.1647 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.1648 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.1649 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1650 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1651 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.1652 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.1653 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1654 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1655 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1656 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1657 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1658 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1659 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1660 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1661 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.1662 `addq %r10, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.1663 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.1664 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1665 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1666 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1667 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1668 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1669 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1670 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1671 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1672 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1673 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1674 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1675 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1676 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63) ]  -- l.1677 `shrq $63, %rbx`

/-- Segment 54 of the body: the 32 instructions from source lines 1678–1709. -/
def ed25519ScReduceShippedSeg054 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rdi"),  -- l.1678 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1679 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1680 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.1681 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1682 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.1683 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1684 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r11"),  -- l.1685 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1686 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1687 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1688 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1689 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1690 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1691 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1692 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1693 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1694 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1695 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1696 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.1697 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.1698 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1699 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1700 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.1701 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.1702 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1703 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1704 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1705 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1706 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1707 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1708 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx") ]  -- l.1709 `movq %rcx, %rbp`

/-- Segment 55 of the body: the 32 instructions from source lines 1710–1741. -/
def ed25519ScReduceShippedSeg055 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rbp"),  -- l.1710 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.1711 `addq %r9, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.1712 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.1713 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1714 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1715 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1716 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1717 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1718 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1719 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1720 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1721 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1722 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1723 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1724 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1725 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1726 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1727 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1728 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1729 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.1730 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1731 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.1732 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1733 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.1734 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1735 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1736 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1737 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1738 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1739 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1740 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi") ]  -- l.1741 `movq %rsi, %rbx`

/-- Segment 56 of the body: the 32 instructions from source lines 1742–1773. -/
def ed25519ScReduceShippedSeg056 : List (JInstr 64) :=
  [ .shr "%rbx" (.imm 63),  -- l.1742 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1743 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1744 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1745 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.1746 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.1747 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1748 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1749 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.1750 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.1751 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1752 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1753 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1754 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1755 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1756 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1757 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1758 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1759 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.1760 `addq %r8, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.1761 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.1762 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1763 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1764 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1765 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1766 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1767 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1768 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1769 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1770 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1771 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1772 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63) ]  -- l.1773 `movq $63, %rbx`

/-- Segment 57 of the body: the 32 instructions from source lines 1774–1805. -/
def ed25519ScReduceShippedSeg057 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%rsi"),  -- l.1774 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1775 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1776 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1777 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1778 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.1779 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1780 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.1781 `xorq %r8, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1782 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9"),  -- l.1783 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1784 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1785 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1786 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1787 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1788 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1789 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1790 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1791 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1792 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1793 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1794 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.1795 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.1796 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1797 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1798 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.1799 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.1800 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1801 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1802 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1803 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1804 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi") ]  -- l.1805 `movq %rsi, %rcx`

/-- Segment 58 of the body: the 32 instructions from source lines 1806–1837. -/
def ed25519ScReduceShippedSeg058 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%rbx"),  -- l.1806 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1807 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1808 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.1809 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.1810 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.1811 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1812 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1813 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1814 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1815 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1816 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1817 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1818 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1819 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1820 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1821 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1822 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1823 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1824 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1825 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1826 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1827 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.1828 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1829 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1830 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1831 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.1832 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.1833 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.1834 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.1835 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.1836 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax") ]  -- l.1837 `xorq %rax, %rsi`

/-- Segment 59 of the body: the 32 instructions from source lines 1838–1869. -/
def ed25519ScReduceShippedSeg059 : List (JInstr 64) :=
  [ .mov "%rax" (.imm 63),  -- l.1838 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.1839 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.1840 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.1841 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.1842 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.1843 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 64,  -- l.1844 `movq 64(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8,  -- l.1845 `movq 8(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.1846 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.1847 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 64,  -- l.1848 `movq 64(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.1849 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.1850 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1851 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.1852 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1853 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.1854 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.1855 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.1856 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.1857 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1858 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r11"),  -- l.1859 `addq %r11, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.1860 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0),  -- l.1861 `movq $0, %rdi`
    .mov "%r12" (.reg "%rcx"),  -- l.1862 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rdi"),  -- l.1863 `andq %rdi, %r12`
    .mov "%rdi" (.imm 0),  -- l.1864 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.1865 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.1866 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.1867 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1868 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx") ]  -- l.1869 `xorq %rcx, %rdi`

/-- Segment 60 of the body: the 32 instructions from source lines 1870–1901. -/
def ed25519ScReduceShippedSeg060 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%r13"),  -- l.1870 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.1871 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r12"),  -- l.1872 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1873 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.1874 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1875 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.1876 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.1877 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.1878 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.1879 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r11"),  -- l.1880 `andq %r11, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1881 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.1882 `xorq %r11, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1883 `movq $18446744073709551615, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.1884 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.1885 `xorq %rbx, %r11`
    .mov "%rbx" (.reg "%rsi"),  -- l.1886 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.1887 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1888 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1889 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1890 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1891 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1892 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1893 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1894 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.1895 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 64,  -- l.1896 `movq 64(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.1897 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1898 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1899 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 64,  -- l.1900 `movq 64(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16 ]  -- l.1901 `movq 16(%rsp), %r14`

/-- Segment 61 of the body: the 32 instructions from source lines 1902–1933. -/
def ed25519ScReduceShippedSeg061 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1902 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1903 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1904 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1905 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1906 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1907 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1908 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1909 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.1910 `addq %r10, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.1911 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.1912 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1913 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1914 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1915 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1916 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1917 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1918 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1919 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1920 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1921 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1922 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1923 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1924 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1925 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1926 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1927 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1928 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.1929 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1930 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.1931 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1932 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r11") ]  -- l.1933 `movq %r11, %rbp`

/-- Segment 62 of the body: the 32 instructions from source lines 1934–1965. -/
def ed25519ScReduceShippedSeg062 : List (JInstr 64) :=
  [ .xor_ "%rbp" (.reg "%rdi"),  -- l.1934 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1935 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1936 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1937 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1938 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1939 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1940 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1941 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1942 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1943 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1944 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 64,  -- l.1945 `movq 64(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.1946 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1947 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1948 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 64,  -- l.1949 `movq 64(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.1950 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1951 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1952 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1953 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1954 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1955 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1956 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1957 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1958 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.1959 `addq %r9, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.1960 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.1961 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1962 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1963 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1964 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615) ]  -- l.1965 `movq $18446744073709551615, %rbx`

/-- Segment 63 of the body: the 32 instructions from source lines 1966–1997. -/
def ed25519ScReduceShippedSeg063 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rbp"),  -- l.1966 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1967 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1968 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1969 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1970 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1971 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1972 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1973 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1974 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1975 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1976 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1977 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.1978 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1979 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.1980 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1981 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.1982 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1983 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1984 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1985 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1986 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1987 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1988 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1989 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1990 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1991 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1992 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1993 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 64,  -- l.1994 `movq 64(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.1995 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1996 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx") ]  -- l.1997 `movq %rcx, %rsi`

/-- Segment 64 of the body: the 32 instructions from source lines 1998–2029. -/
def ed25519ScReduceShippedSeg064 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsp" 64,  -- l.1998 `movq 64(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.1999 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2000 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2001 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2002 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2003 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2004 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2005 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2006 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2007 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.2008 `addq %r8, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.2009 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.2010 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2011 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2012 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2013 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2014 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2015 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2016 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2017 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2018 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2019 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2020 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2021 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2022 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2023 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2024 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2025 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2026 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.2027 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2028 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r8") ]  -- l.2029 `xorq %r8, %rsi`

/-- Segment 65 of the body: the 32 instructions from source lines 2030–2061. -/
def ed25519ScReduceShippedSeg065 : List (JInstr 64) :=
  [ .mov "%rdi" (.imm 18446744073709551615),  -- l.2030 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9"),  -- l.2031 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.2032 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.2033 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.2034 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2035 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2036 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2037 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2038 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2039 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2040 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2041 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2042 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 64,  -- l.2043 `movq 64(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.2044 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2045 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2046 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 64,  -- l.2047 `movq 64(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.2048 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2049 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2050 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2051 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2052 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2053 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2054 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2055 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2056 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.2057 `addq %rax, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.2058 `movq %rcx, %r15`
    .storeMem "%rsp" 40 (.reg "%r15"),  -- l.2059 `movq %r15, 40(%rsp)`
    .mov "%rcx" (.reg "%rsi"),  -- l.2060 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx") ]  -- l.2061 `andq %rbx, %rcx`

/-- Segment 66 of the body: the 32 instructions from source lines 2062–2093. -/
def ed25519ScReduceShippedSeg066 : List (JInstr 64) :=
  [ .mov "%r12" (.reg "%rsi"),  -- l.2062 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2063 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2064 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2065 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2066 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2067 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2068 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2069 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2070 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2071 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2072 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2073 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2074 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2075 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2076 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.2077 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2078 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2079 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.2080 `movq $18446744073709551615, %rax`
    .loadMem "%rdi" "%rsp" 40,  -- l.2081 `movq 40(%rsp), %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.2082 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.2083 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.2084 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.2085 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2086 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.2087 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.2088 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.2089 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.2090 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.2091 `addq %rax, %rbx`
    .mov "%r15" (.reg "%rbx"),  -- l.2092 `movq %rbx, %r15`
    .storeMem "%rsp" 56 (.reg "%r15") ]  -- l.2093 `movq %r15, 56(%rsp)`

/-- Segment 67 of the body: the 32 instructions from source lines 2094–2125. -/
def ed25519ScReduceShippedSeg067 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%r11"),  -- l.2094 `movq %r11, %rbx`
    .loadMem "%r15" "%rsp" 112,  -- l.2095 `movq 112(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2096 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.2097 `movq %rbx, %rcx`
    .mov "%rdx" (.reg "%r11"),  -- l.2098 `movq %r11, %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.2099 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2100 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2101 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2102 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2103 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.2104 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.2105 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.2106 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.2107 `movq %rdi, %rbx`
    .mov "%rdi" (.imm 0),  -- l.2108 `movq $0, %rdi`
    .mov "%rbp" (.reg "%rbx"),  -- l.2109 `movq %rbx, %rbp`
    .add "%rbp" (.reg "%rdi"),  -- l.2110 `addq %rdi, %rbp`
    .mov "%r15" (.reg "%rbp"),  -- l.2111 `movq %rbp, %r15`
    .storeMem "%rsp" 64 (.reg "%r15"),  -- l.2112 `movq %r15, 64(%rsp)`
    .mov "%rbp" (.imm 0),  -- l.2113 `movq $0, %rbp`
    .mov "%r12" (.reg "%rcx"),  -- l.2114 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rbp"),  -- l.2115 `andq %rbp, %r12`
    .mov "%rbp" (.imm 0),  -- l.2116 `movq $0, %rbp`
    .mov "%r13" (.reg "%rcx"),  -- l.2117 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rbp"),  -- l.2118 `xorq %rbp, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.2119 `movq $18446744073709551615, %rcx`
    .mov "%rbp" (.reg "%rbx"),  -- l.2120 `movq %rbx, %rbp`
    .xor_ "%rbp" (.reg "%rcx"),  -- l.2121 `xorq %rcx, %rbp`
    .mov "%rcx" (.reg "%r13"),  -- l.2122 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rbp"),  -- l.2123 `andq %rbp, %rcx`
    .mov "%rbp" (.reg "%r12"),  -- l.2124 `movq %r12, %rbp`
    .xor_ "%rbp" (.reg "%rcx") ]  -- l.2125 `xorq %rcx, %rbp`

/-- Segment 68 of the body: the 32 instructions from source lines 2126–2157. -/
def ed25519ScReduceShippedSeg068 : List (JInstr 64) :=
  [ .mov "%rcx" (.imm 63),  -- l.2126 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rbp"),  -- l.2127 `movq %rbp, %rcx`
    .shr "%rcx" (.imm 63),  -- l.2128 `shrq $63, %rcx`
    .mov "%rbp" (.reg "%rsi"),  -- l.2129 `movq %rsi, %rbp`
    .add "%rbp" (.reg "%rcx"),  -- l.2130 `addq %rcx, %rbp`
    .mov "%rcx" (.imm 0),  -- l.2131 `movq $0, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2132 `movq %rbx, %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.2133 `andq %rcx, %rsi`
    .mov "%rcx" (.imm 0),  -- l.2134 `movq $0, %rcx`
    .mov "%r12" (.reg "%rbx"),  -- l.2135 `movq %rbx, %r12`
    .xor_ "%r12" (.reg "%rcx"),  -- l.2136 `xorq %rcx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2137 `movq $18446744073709551615, %rbx`
    .loadMem "%rcx" "%rsp" 64,  -- l.2138 `movq 64(%rsp), %rcx`
    .xor_ "%rcx" (.reg "%rbx"),  -- l.2139 `xorq %rbx, %rcx`
    .mov "%rbx" (.reg "%r12"),  -- l.2140 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rcx"),  -- l.2141 `andq %rcx, %rbx`
    .mov "%rcx" (.reg "%rsi"),  -- l.2142 `movq %rsi, %rcx`
    .xor_ "%rcx" (.reg "%rbx"),  -- l.2143 `xorq %rbx, %rcx`
    .mov "%rbx" (.imm 63),  -- l.2144 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rcx"),  -- l.2145 `movq %rcx, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2146 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rbp"),  -- l.2147 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2148 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.2149 `movq %rcx, %rbx`
    .mov "%rcx" (.reg "%r11"),  -- l.2150 `movq %r11, %rcx`
    .loadMem "%r15" "%rsp" 104,  -- l.2151 `movq 104(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2152 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2153 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r11"),  -- l.2154 `movq %r11, %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.2155 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2156 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14") ]  -- l.2157 `mulx %r14, %rsi, %rcx`

/-- Segment 69 of the body: the 32 instructions from source lines 2158–2189. -/
def ed25519ScReduceShippedSeg069 : List (JInstr 64) :=
  [ .loadMem "%rsi" "%rsp" (-128),  -- l.2158 `movq -128(%rsp), %rsi`
    .mov "%rbp" (.reg "%rcx"),  -- l.2159 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rsi"),  -- l.2160 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2161 `addq %rbx, %rcx`
    .mov "%r12" (.reg "%rcx"),  -- l.2162 `movq %rcx, %r12`
    .mov "%rcx" (.imm 0),  -- l.2163 `movq $0, %rcx`
    .mov "%r13" (.reg "%r12"),  -- l.2164 `movq %r12, %r13`
    .add "%r13" (.reg "%rcx"),  -- l.2165 `addq %rcx, %r13`
    .mov "%rcx" (.reg "%r13"),  -- l.2166 `movq %r13, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.2167 `movq %rsi, %r13`
    .and_ "%r13" (.reg "%rbx"),  -- l.2168 `andq %rbx, %r13`
    .mov "%rdi" (.reg "%rsi"),  -- l.2169 `movq %rsi, %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.2170 `xorq %rbx, %rdi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2171 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r12"),  -- l.2172 `movq %r12, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2173 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%rdi"),  -- l.2174 `movq %rdi, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2175 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%r13"),  -- l.2176 `movq %r13, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2177 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2178 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2179 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2180 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2181 `movq %rbp, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2182 `addq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.2183 `movq $0, %rbx`
    .mov "%rdi" (.reg "%r12"),  -- l.2184 `movq %r12, %rdi`
    .and_ "%rdi" (.reg "%rbx"),  -- l.2185 `andq %rbx, %rdi`
    .mov "%rbx" (.imm 0),  -- l.2186 `movq $0, %rbx`
    .mov "%rbp" (.reg "%r12"),  -- l.2187 `movq %r12, %rbp`
    .xor_ "%rbp" (.reg "%rbx"),  -- l.2188 `xorq %rbx, %rbp`
    .mov "%rbx" (.imm 18446744073709551615) ]  -- l.2189 `movq $18446744073709551615, %rbx`

/-- Segment 70 of the body: the 32 instructions from source lines 2190–2221. -/
def ed25519ScReduceShippedSeg070 : List (JInstr 64) :=
  [ .mov "%r12" (.reg "%rcx"),  -- l.2190 `movq %rcx, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2191 `xorq %rbx, %r12`
    .mov "%rbx" (.reg "%rbp"),  -- l.2192 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r12"),  -- l.2193 `andq %r12, %rbx`
    .mov "%rbp" (.reg "%rdi"),  -- l.2194 `movq %rdi, %rbp`
    .xor_ "%rbp" (.reg "%rbx"),  -- l.2195 `xorq %rbx, %rbp`
    .mov "%rbx" (.imm 63),  -- l.2196 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2197 `movq %rbp, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2198 `shrq $63, %rbx`
    .mov "%rdi" (.reg "%rsi"),  -- l.2199 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.2200 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.2201 `movq %rdi, %rbx`
    .mov "%rsi" (.reg "%r11"),  -- l.2202 `movq %r11, %rsi`
    .loadMem "%r15" "%rsp" 96,  -- l.2203 `movq 96(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.2204 `imulq %r15, %rsi`
    .mov "%rdi" (.reg "%rsi"),  -- l.2205 `movq %rsi, %rdi`
    .mov "%rdx" (.reg "%r11"),  -- l.2206 `movq %r11, %rdx`
    .loadMem "%r14" "%rsp" 96,  -- l.2207 `movq 96(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2208 `movq %rcx, -128(%rsp)`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2209 `mulx %r14, %rcx, %rsi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2210 `movq -128(%rsp), %rcx`
    .mov "%rbp" (.reg "%rsi"),  -- l.2211 `movq %rsi, %rbp`
    .mov "%rsi" (.reg "%rdi"),  -- l.2212 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2213 `addq %rbx, %rsi`
    .mov "%r12" (.reg "%rsi"),  -- l.2214 `movq %rsi, %r12`
    .mov "%rsi" (.imm 0),  -- l.2215 `movq $0, %rsi`
    .mov "%r13" (.reg "%r12"),  -- l.2216 `movq %r12, %r13`
    .add "%r13" (.reg "%rsi"),  -- l.2217 `addq %rsi, %r13`
    .mov "%rsi" (.reg "%r13"),  -- l.2218 `movq %r13, %rsi`
    .mov "%r13" (.reg "%rdi"),  -- l.2219 `movq %rdi, %r13`
    .and_ "%r13" (.reg "%rbx"),  -- l.2220 `andq %rbx, %r13`
    .mov "%rax" (.reg "%rdi") ]  -- l.2221 `movq %rdi, %rax`

/-- Segment 71 of the body: the 32 instructions from source lines 2222–2253. -/
def ed25519ScReduceShippedSeg071 : List (JInstr 64) :=
  [ .xor_ "%rax" (.reg "%rbx"),  -- l.2222 `xorq %rbx, %rax`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2223 `movq $18446744073709551615, %rbx`
    .mov "%rdi" (.reg "%r12"),  -- l.2224 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.2225 `xorq %rbx, %rdi`
    .mov "%rbx" (.reg "%rax"),  -- l.2226 `movq %rax, %rbx`
    .and_ "%rbx" (.reg "%rdi"),  -- l.2227 `andq %rdi, %rbx`
    .mov "%rax" (.reg "%r13"),  -- l.2228 `movq %r13, %rax`
    .xor_ "%rax" (.reg "%rbx"),  -- l.2229 `xorq %rbx, %rax`
    .mov "%rbx" (.imm 63),  -- l.2230 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rax"),  -- l.2231 `movq %rax, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2232 `shrq $63, %rbx`
    .mov "%rax" (.reg "%rbp"),  -- l.2233 `movq %rbp, %rax`
    .add "%rax" (.reg "%rbx"),  -- l.2234 `addq %rbx, %rax`
    .mov "%rbx" (.imm 0),  -- l.2235 `movq $0, %rbx`
    .mov "%rdi" (.reg "%r12"),  -- l.2236 `movq %r12, %rdi`
    .and_ "%rdi" (.reg "%rbx"),  -- l.2237 `andq %rbx, %rdi`
    .mov "%rbx" (.imm 0),  -- l.2238 `movq $0, %rbx`
    .mov "%rbp" (.reg "%r12"),  -- l.2239 `movq %r12, %rbp`
    .xor_ "%rbp" (.reg "%rbx"),  -- l.2240 `xorq %rbx, %rbp`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2241 `movq $18446744073709551615, %rbx`
    .mov "%r12" (.reg "%rsi"),  -- l.2242 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2243 `xorq %rbx, %r12`
    .mov "%rbx" (.reg "%rbp"),  -- l.2244 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r12"),  -- l.2245 `andq %r12, %rbx`
    .mov "%rbp" (.reg "%rdi"),  -- l.2246 `movq %rdi, %rbp`
    .xor_ "%rbp" (.reg "%rbx"),  -- l.2247 `xorq %rbx, %rbp`
    .mov "%rbx" (.imm 63),  -- l.2248 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2249 `movq %rbp, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2250 `shrq $63, %rbx`
    .mov "%rdi" (.reg "%rax"),  -- l.2251 `movq %rax, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.2252 `addq %rbx, %rdi`
    .mov "%rax" (.reg "%rdi") ]  -- l.2253 `movq %rdi, %rax`

/-- Segment 72 of the body: the 32 instructions from source lines 2254–2285. -/
def ed25519ScReduceShippedSeg072 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%r11"),  -- l.2254 `movq %r11, %rbx`
    .loadMem "%r15" "%rsp" 88,  -- l.2255 `movq 88(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2256 `imulq %r15, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2257 `movq %rbx, %rdi`
    .mov "%rdx" (.reg "%r11"),  -- l.2258 `movq %r11, %rdx`
    .loadMem "%r14" "%rsp" 88,  -- l.2259 `movq 88(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2260 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2261 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2262 `movq -128(%rsp), %rcx`
    .mov "%rbp" (.reg "%rbx"),  -- l.2263 `movq %rbx, %rbp`
    .mov "%rbx" (.reg "%rdi"),  -- l.2264 `movq %rdi, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.2265 `addq %rax, %rbx`
    .mov "%r11" (.reg "%rbx"),  -- l.2266 `movq %rbx, %r11`
    .mov "%rbx" (.imm 0),  -- l.2267 `movq $0, %rbx`
    .mov "%r12" (.reg "%r11"),  -- l.2268 `movq %r11, %r12`
    .add "%r12" (.reg "%rbx"),  -- l.2269 `addq %rbx, %r12`
    .mov "%rbx" (.reg "%r12"),  -- l.2270 `movq %r12, %rbx`
    .mov "%r12" (.reg "%rdi"),  -- l.2271 `movq %rdi, %r12`
    .and_ "%r12" (.reg "%rax"),  -- l.2272 `andq %rax, %r12`
    .mov "%r13" (.reg "%rdi"),  -- l.2273 `movq %rdi, %r13`
    .xor_ "%r13" (.reg "%rax"),  -- l.2274 `xorq %rax, %r13`
    .mov "%rax" (.imm 18446744073709551615),  -- l.2275 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r11"),  -- l.2276 `movq %r11, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.2277 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%r13"),  -- l.2278 `movq %r13, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.2279 `andq %rdi, %rax`
    .mov "%rdi" (.reg "%r12"),  -- l.2280 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.2281 `xorq %rax, %rdi`
    .mov "%rax" (.imm 63),  -- l.2282 `movq $63, %rax`
    .mov "%rax" (.reg "%rdi"),  -- l.2283 `movq %rdi, %rax`
    .shr "%rax" (.imm 63),  -- l.2284 `shrq $63, %rax`
    .mov "%rdi" (.reg "%rbp") ]  -- l.2285 `movq %rbp, %rdi`

/-- Segment 73 of the body: the 32 instructions from source lines 2286–2317. -/
def ed25519ScReduceShippedSeg073 : List (JInstr 64) :=
  [ .add "%rdi" (.reg "%rax"),  -- l.2286 `addq %rax, %rdi`
    .mov "%rax" (.imm 0),  -- l.2287 `movq $0, %rax`
    .mov "%rbp" (.reg "%r11"),  -- l.2288 `movq %r11, %rbp`
    .and_ "%rbp" (.reg "%rax"),  -- l.2289 `andq %rax, %rbp`
    .mov "%rax" (.imm 0),  -- l.2290 `movq $0, %rax`
    .mov "%r12" (.reg "%r11"),  -- l.2291 `movq %r11, %r12`
    .xor_ "%r12" (.reg "%rax"),  -- l.2292 `xorq %rax, %r12`
    .mov "%rax" (.imm 18446744073709551615),  -- l.2293 `movq $18446744073709551615, %rax`
    .mov "%r11" (.reg "%rbx"),  -- l.2294 `movq %rbx, %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.2295 `xorq %rax, %r11`
    .mov "%rax" (.reg "%r12"),  -- l.2296 `movq %r12, %rax`
    .and_ "%rax" (.reg "%r11"),  -- l.2297 `andq %r11, %rax`
    .mov "%r11" (.reg "%rbp"),  -- l.2298 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.2299 `xorq %rax, %r11`
    .mov "%rax" (.imm 63),  -- l.2300 `movq $63, %rax`
    .mov "%rax" (.reg "%r11"),  -- l.2301 `movq %r11, %rax`
    .shr "%rax" (.imm 63),  -- l.2302 `shrq $63, %rax`
    .mov "%rbp" (.reg "%rdi"),  -- l.2303 `movq %rdi, %rbp`
    .add "%rbp" (.reg "%rax"),  -- l.2304 `addq %rax, %rbp`
    .mov "%rax" (.reg "%rbp"),  -- l.2305 `movq %rbp, %rax`
    .mov "%rdi" (.reg "%r10"),  -- l.2306 `movq %r10, %rdi`
    .loadMem "%r15" "%rsp" 112,  -- l.2307 `movq 112(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.2308 `imulq %r15, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.2309 `movq %rdi, %rbp`
    .mov "%rdx" (.reg "%r10"),  -- l.2310 `movq %r10, %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.2311 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2312 `movq %rcx, -128(%rsp)`
    .mulx "%rdi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2313 `mulx %r14, %rcx, %rdi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2314 `movq -128(%rsp), %rcx`
    .mov "%r11" (.reg "%rdi"),  -- l.2315 `movq %rdi, %r11`
    .mov "%rdi" (.imm 0),  -- l.2316 `movq $0, %rdi`
    .mov "%r12" (.reg "%rbp") ]  -- l.2317 `movq %rbp, %r12`

/-- Segment 74 of the body: the 32 instructions from source lines 2318–2349. -/
def ed25519ScReduceShippedSeg074 : List (JInstr 64) :=
  [ .add "%r12" (.reg "%rdi"),  -- l.2318 `addq %rdi, %r12`
    .mov "%rdi" (.reg "%r12"),  -- l.2319 `movq %r12, %rdi`
    .mov "%r12" (.reg "%rdi"),  -- l.2320 `movq %rdi, %r12`
    .add "%r12" (.reg "%rcx"),  -- l.2321 `addq %rcx, %r12`
    .mov "%r15" (.reg "%r12"),  -- l.2322 `movq %r12, %r15`
    .storeMem "%rsp" 48 (.reg "%r15"),  -- l.2323 `movq %r15, 48(%rsp)`
    .mov "%r12" (.imm 0),  -- l.2324 `movq $0, %r12`
    .mov "%r13" (.reg "%rbp"),  -- l.2325 `movq %rbp, %r13`
    .and_ "%r13" (.reg "%r12"),  -- l.2326 `andq %r12, %r13`
    .mov "%r12" (.imm 0),  -- l.2327 `movq $0, %r12`
    .mov "%r8" (.reg "%rbp"),  -- l.2328 `movq %rbp, %r8`
    .xor_ "%r8" (.reg "%r12"),  -- l.2329 `xorq %r12, %r8`
    .mov "%rbp" (.imm 18446744073709551615),  -- l.2330 `movq $18446744073709551615, %rbp`
    .mov "%r12" (.reg "%rdi"),  -- l.2331 `movq %rdi, %r12`
    .xor_ "%r12" (.reg "%rbp"),  -- l.2332 `xorq %rbp, %r12`
    .mov "%rbp" (.reg "%r8"),  -- l.2333 `movq %r8, %rbp`
    .and_ "%rbp" (.reg "%r12"),  -- l.2334 `andq %r12, %rbp`
    .mov "%r8" (.reg "%r13"),  -- l.2335 `movq %r13, %r8`
    .xor_ "%r8" (.reg "%rbp"),  -- l.2336 `xorq %rbp, %r8`
    .mov "%rbp" (.imm 63),  -- l.2337 `movq $63, %rbp`
    .mov "%rbp" (.reg "%r8"),  -- l.2338 `movq %r8, %rbp`
    .shr "%rbp" (.imm 63),  -- l.2339 `shrq $63, %rbp`
    .mov "%r8" (.reg "%r11"),  -- l.2340 `movq %r11, %r8`
    .add "%r8" (.reg "%rbp"),  -- l.2341 `addq %rbp, %r8`
    .mov "%rbp" (.reg "%rdi"),  -- l.2342 `movq %rdi, %rbp`
    .and_ "%rbp" (.reg "%rcx"),  -- l.2343 `andq %rcx, %rbp`
    .mov "%r11" (.reg "%rdi"),  -- l.2344 `movq %rdi, %r11`
    .xor_ "%r11" (.reg "%rcx"),  -- l.2345 `xorq %rcx, %r11`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.2346 `movq $18446744073709551615, %rcx`
    .loadMem "%rdi" "%rsp" 48,  -- l.2347 `movq 48(%rsp), %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2348 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r11") ]  -- l.2349 `movq %r11, %rcx`

/-- Segment 75 of the body: the 32 instructions from source lines 2350–2381. -/
def ed25519ScReduceShippedSeg075 : List (JInstr 64) :=
  [ .and_ "%rcx" (.reg "%rdi"),  -- l.2350 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%rbp"),  -- l.2351 `movq %rbp, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2352 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.2353 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2354 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.2355 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%r8"),  -- l.2356 `movq %r8, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.2357 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rdi"),  -- l.2358 `movq %rdi, %rcx`
    .mov "%rdi" (.reg "%r10"),  -- l.2359 `movq %r10, %rdi`
    .loadMem "%r15" "%rsp" 104,  -- l.2360 `movq 104(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.2361 `imulq %r15, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.2362 `movq %rdi, %rbp`
    .mov "%rdx" (.reg "%r10"),  -- l.2363 `movq %r10, %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.2364 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2365 `movq %rcx, -128(%rsp)`
    .mulx "%rdi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2366 `mulx %r14, %rcx, %rdi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2367 `movq -128(%rsp), %rcx`
    .mov "%r8" (.reg "%rdi"),  -- l.2368 `movq %rdi, %r8`
    .mov "%rdi" (.reg "%rbp"),  -- l.2369 `movq %rbp, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.2370 `addq %rcx, %rdi`
    .mov "%r11" (.reg "%rdi"),  -- l.2371 `movq %rdi, %r11`
    .mov "%rdi" (.reg "%r11"),  -- l.2372 `movq %r11, %rdi`
    .add "%rdi" (.reg "%rsi"),  -- l.2373 `addq %rsi, %rdi`
    .mov "%r12" (.reg "%rdi"),  -- l.2374 `movq %rdi, %r12`
    .mov "%rdi" (.reg "%rbp"),  -- l.2375 `movq %rbp, %rdi`
    .and_ "%rdi" (.reg "%rcx"),  -- l.2376 `andq %rcx, %rdi`
    .mov "%r13" (.reg "%rbp"),  -- l.2377 `movq %rbp, %r13`
    .xor_ "%r13" (.reg "%rcx"),  -- l.2378 `xorq %rcx, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.2379 `movq $18446744073709551615, %rcx`
    .mov "%rbp" (.reg "%r11"),  -- l.2380 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rcx") ]  -- l.2381 `xorq %rcx, %rbp`

/-- Segment 76 of the body: the 32 instructions from source lines 2382–2413. -/
def ed25519ScReduceShippedSeg076 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%r13"),  -- l.2382 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rbp"),  -- l.2383 `andq %rbp, %rcx`
    .mov "%rbp" (.reg "%rdi"),  -- l.2384 `movq %rdi, %rbp`
    .xor_ "%rbp" (.reg "%rcx"),  -- l.2385 `xorq %rcx, %rbp`
    .mov "%rcx" (.imm 63),  -- l.2386 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rbp"),  -- l.2387 `movq %rbp, %rcx`
    .shr "%rcx" (.imm 63),  -- l.2388 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%r8"),  -- l.2389 `movq %r8, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.2390 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%r11"),  -- l.2391 `movq %r11, %rcx`
    .and_ "%rcx" (.reg "%rsi"),  -- l.2392 `andq %rsi, %rcx`
    .mov "%rbp" (.reg "%r11"),  -- l.2393 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rsi"),  -- l.2394 `xorq %rsi, %rbp`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.2395 `movq $18446744073709551615, %rsi`
    .mov "%r8" (.reg "%r12"),  -- l.2396 `movq %r12, %r8`
    .xor_ "%r8" (.reg "%rsi"),  -- l.2397 `xorq %rsi, %r8`
    .mov "%rsi" (.reg "%rbp"),  -- l.2398 `movq %rbp, %rsi`
    .and_ "%rsi" (.reg "%r8"),  -- l.2399 `andq %r8, %rsi`
    .mov "%rbp" (.reg "%rcx"),  -- l.2400 `movq %rcx, %rbp`
    .xor_ "%rbp" (.reg "%rsi"),  -- l.2401 `xorq %rsi, %rbp`
    .mov "%rcx" (.imm 63),  -- l.2402 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rbp"),  -- l.2403 `movq %rbp, %rcx`
    .shr "%rcx" (.imm 63),  -- l.2404 `shrq $63, %rcx`
    .mov "%rsi" (.reg "%rdi"),  -- l.2405 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.2406 `addq %rcx, %rsi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2407 `movq %rsi, %rcx`
    .mov "%rsi" (.reg "%r10"),  -- l.2408 `movq %r10, %rsi`
    .loadMem "%r15" "%rsp" 96,  -- l.2409 `movq 96(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.2410 `imulq %r15, %rsi`
    .mov "%rdi" (.reg "%rsi"),  -- l.2411 `movq %rsi, %rdi`
    .mov "%rdx" (.reg "%r10"),  -- l.2412 `movq %r10, %rdx`
    .loadMem "%r14" "%rsp" 96 ]  -- l.2413 `movq 96(%rsp), %r14`

/-- Segment 77 of the body: the 32 instructions from source lines 2414–2445. -/
def ed25519ScReduceShippedSeg077 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2414 `movq %rcx, -128(%rsp)`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2415 `mulx %r14, %rcx, %rsi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2416 `movq -128(%rsp), %rcx`
    .mov "%rbp" (.reg "%rsi"),  -- l.2417 `movq %rsi, %rbp`
    .mov "%rsi" (.reg "%rdi"),  -- l.2418 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.2419 `addq %rcx, %rsi`
    .mov "%r8" (.reg "%rsi"),  -- l.2420 `movq %rsi, %r8`
    .mov "%rsi" (.reg "%r8"),  -- l.2421 `movq %r8, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2422 `addq %rbx, %rsi`
    .mov "%r11" (.reg "%rsi"),  -- l.2423 `movq %rsi, %r11`
    .mov "%rsi" (.reg "%rdi"),  -- l.2424 `movq %rdi, %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.2425 `andq %rcx, %rsi`
    .mov "%r13" (.reg "%rdi"),  -- l.2426 `movq %rdi, %r13`
    .xor_ "%r13" (.reg "%rcx"),  -- l.2427 `xorq %rcx, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.2428 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%r8"),  -- l.2429 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2430 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.2431 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.2432 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.2433 `movq %rsi, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2434 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.2435 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2436 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.2437 `shrq $63, %rcx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2438 `movq %rbp, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.2439 `addq %rcx, %rsi`
    .mov "%rcx" (.reg "%r8"),  -- l.2440 `movq %r8, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2441 `andq %rbx, %rcx`
    .mov "%rdi" (.reg "%r8"),  -- l.2442 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.2443 `xorq %rbx, %rdi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2444 `movq $18446744073709551615, %rbx`
    .mov "%rbp" (.reg "%r11") ]  -- l.2445 `movq %r11, %rbp`

/-- Segment 78 of the body: the 32 instructions from source lines 2446–2477. -/
def ed25519ScReduceShippedSeg078 : List (JInstr 64) :=
  [ .xor_ "%rbp" (.reg "%rbx"),  -- l.2446 `xorq %rbx, %rbp`
    .mov "%rbx" (.reg "%rdi"),  -- l.2447 `movq %rdi, %rbx`
    .and_ "%rbx" (.reg "%rbp"),  -- l.2448 `andq %rbp, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.2449 `movq %rcx, %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.2450 `xorq %rbx, %rdi`
    .mov "%rbx" (.imm 63),  -- l.2451 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rdi"),  -- l.2452 `movq %rdi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2453 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rsi"),  -- l.2454 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2455 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.2456 `movq %rcx, %rbx`
    .mov "%rcx" (.reg "%r10"),  -- l.2457 `movq %r10, %rcx`
    .loadMem "%r15" "%rsp" 88,  -- l.2458 `movq 88(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2459 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2460 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r10"),  -- l.2461 `movq %r10, %rdx`
    .loadMem "%r14" "%rsp" 88,  -- l.2462 `movq 88(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2463 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2464 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2465 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2466 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2467 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2468 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2469 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2470 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.2471 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.2472 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.2473 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2474 `andq %rbx, %rcx`
    .mov "%r10" (.reg "%rsi"),  -- l.2475 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.2476 `xorq %rbx, %r10`
    .mov "%rbx" (.imm 18446744073709551615) ]  -- l.2477 `movq $18446744073709551615, %rbx`

/-- Segment 79 of the body: the 32 instructions from source lines 2478–2509. -/
def ed25519ScReduceShippedSeg079 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rbp"),  -- l.2478 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2479 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r10"),  -- l.2480 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2481 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2482 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2483 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2484 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2485 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2486 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2487 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2488 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2489 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.2490 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2491 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2492 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.2493 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.2494 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.2495 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.2496 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.2497 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.2498 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2499 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.2500 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.2501 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.2502 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.2503 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.2504 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.2505 `movq %rbx, %rax`
    .mov "%rbx" (.reg "%r9"),  -- l.2506 `movq %r9, %rbx`
    .loadMem "%r15" "%rsp" 112,  -- l.2507 `movq 112(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2508 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx") ]  -- l.2509 `movq %rbx, %rcx`

/-- Segment 80 of the body: the 32 instructions from source lines 2510–2541. -/
def ed25519ScReduceShippedSeg080 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r9"),  -- l.2510 `movq %r9, %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.2511 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2512 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2513 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2514 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2515 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.2516 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.2517 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.2518 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.2519 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2520 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r12"),  -- l.2521 `addq %r12, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.2522 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0),  -- l.2523 `movq $0, %rdi`
    .mov "%r10" (.reg "%rcx"),  -- l.2524 `movq %rcx, %r10`
    .and_ "%r10" (.reg "%rdi"),  -- l.2525 `andq %rdi, %r10`
    .mov "%rdi" (.imm 0),  -- l.2526 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.2527 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.2528 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.2529 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2530 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2531 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.2532 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.2533 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r10"),  -- l.2534 `movq %r10, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2535 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.2536 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2537 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.2538 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.2539 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.2540 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx") ]  -- l.2541 `movq %rbx, %rcx`

/-- Segment 81 of the body: the 32 instructions from source lines 2542–2573. -/
def ed25519ScReduceShippedSeg081 : List (JInstr 64) :=
  [ .and_ "%rcx" (.reg "%r12"),  -- l.2542 `andq %r12, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2543 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r12"),  -- l.2544 `xorq %r12, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2545 `movq $18446744073709551615, %rbx`
    .mov "%r10" (.reg "%rbp"),  -- l.2546 `movq %rbp, %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.2547 `xorq %rbx, %r10`
    .mov "%rbx" (.reg "%rsi"),  -- l.2548 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.2549 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2550 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2551 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2552 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2553 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2554 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2555 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2556 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.2557 `movq %rcx, %rbx`
    .mov "%rcx" (.reg "%r9"),  -- l.2558 `movq %r9, %rcx`
    .loadMem "%r15" "%rsp" 104,  -- l.2559 `movq 104(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2560 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2561 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r9"),  -- l.2562 `movq %r9, %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.2563 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2564 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2565 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2566 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2567 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2568 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2569 `addq %rbx, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.2570 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%r10"),  -- l.2571 `movq %r10, %rcx`
    .add "%rcx" (.reg "%r11"),  -- l.2572 `addq %r11, %rcx`
    .mov "%r12" (.reg "%rcx") ]  -- l.2573 `movq %rcx, %r12`

/-- Segment 82 of the body: the 32 instructions from source lines 2574–2605. -/
def ed25519ScReduceShippedSeg082 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rsi"),  -- l.2574 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2575 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.2576 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.2577 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2578 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.2579 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2580 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.2581 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2582 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2583 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2584 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2585 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2586 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2587 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2588 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2589 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r10"),  -- l.2590 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.2591 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.2592 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.2593 `xorq %r11, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2594 `movq $18446744073709551615, %rdi`
    .mov "%r10" (.reg "%r12"),  -- l.2595 `movq %r12, %r10`
    .xor_ "%r10" (.reg "%rdi"),  -- l.2596 `xorq %rdi, %r10`
    .mov "%rdi" (.reg "%rsi"),  -- l.2597 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r10"),  -- l.2598 `andq %r10, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2599 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2600 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2601 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2602 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2603 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2604 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx") ]  -- l.2605 `addq %rbx, %rsi`

/-- Segment 83 of the body: the 32 instructions from source lines 2606–2637. -/
def ed25519ScReduceShippedSeg083 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%rsi"),  -- l.2606 `movq %rsi, %rbx`
    .mov "%rcx" (.reg "%r9"),  -- l.2607 `movq %r9, %rcx`
    .loadMem "%r15" "%rsp" 96,  -- l.2608 `movq 96(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2609 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2610 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r9"),  -- l.2611 `movq %r9, %rdx`
    .loadMem "%r14" "%rsp" 96,  -- l.2612 `movq 96(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2613 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2614 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2615 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2616 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2617 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2618 `addq %rbx, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.2619 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%r10"),  -- l.2620 `movq %r10, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.2621 `addq %r8, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.2622 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.2623 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2624 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.2625 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.2626 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2627 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.2628 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2629 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.2630 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2631 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2632 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2633 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2634 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2635 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2636 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi") ]  -- l.2637 `movq %rdi, %rcx`

/-- Segment 84 of the body: the 32 instructions from source lines 2638–2669. -/
def ed25519ScReduceShippedSeg084 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%rbx"),  -- l.2638 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r10"),  -- l.2639 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.2640 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.2641 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.2642 `xorq %r8, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2643 `movq $18446744073709551615, %rdi`
    .mov "%r8" (.reg "%r11"),  -- l.2644 `movq %r11, %r8`
    .xor_ "%r8" (.reg "%rdi"),  -- l.2645 `xorq %rdi, %r8`
    .mov "%rdi" (.reg "%rsi"),  -- l.2646 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r8"),  -- l.2647 `andq %r8, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2648 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2649 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2650 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2651 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2652 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2653 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2654 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2655 `movq %rsi, %rbx`
    .mov "%rcx" (.reg "%r9"),  -- l.2656 `movq %r9, %rcx`
    .loadMem "%r15" "%rsp" 88,  -- l.2657 `movq 88(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2658 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2659 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r9"),  -- l.2660 `movq %r9, %rdx`
    .loadMem "%r14" "%rsp" 88,  -- l.2661 `movq 88(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2662 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2663 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2664 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2665 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2666 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2667 `addq %rbx, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.2668 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%r8") ]  -- l.2669 `movq %r8, %rcx`

/-- Segment 85 of the body: the 32 instructions from source lines 2670–2701. -/
def ed25519ScReduceShippedSeg085 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%rax"),  -- l.2670 `addq %rax, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.2671 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.2672 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2673 `andq %rbx, %rcx`
    .mov "%r10" (.reg "%rsi"),  -- l.2674 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.2675 `xorq %rbx, %r10`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2676 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.2677 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2678 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r10"),  -- l.2679 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2680 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2681 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2682 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2683 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2684 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2685 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2686 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2687 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r8"),  -- l.2688 `movq %r8, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.2689 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.2690 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2691 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.2692 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r9"),  -- l.2693 `movq %r9, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.2694 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.2695 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.2696 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.2697 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2698 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.2699 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.2700 `movq %rsi, %rax`
    .shr "%rax" (.imm 63) ]  -- l.2701 `shrq $63, %rax`

/-- Segment 86 of the body: the 32 instructions from source lines 2702–2733. -/
def ed25519ScReduceShippedSeg086 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%rcx"),  -- l.2702 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.2703 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.2704 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 40,  -- l.2705 `movq 40(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 112,  -- l.2706 `movq 112(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2707 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.2708 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 40,  -- l.2709 `movq 40(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.2710 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2711 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2712 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2713 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2714 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.2715 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.2716 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.2717 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.2718 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2719 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r12"),  -- l.2720 `addq %r12, %rdi`
    .mov "%r15" (.reg "%rdi"),  -- l.2721 `movq %rdi, %r15`
    .storeMem "%rsp" 32 (.reg "%r15"),  -- l.2722 `movq %r15, 32(%rsp)`
    .mov "%rdi" (.imm 0),  -- l.2723 `movq $0, %rdi`
    .mov "%r10" (.reg "%rcx"),  -- l.2724 `movq %rcx, %r10`
    .and_ "%r10" (.reg "%rdi"),  -- l.2725 `andq %rdi, %r10`
    .mov "%rdi" (.imm 0),  -- l.2726 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.2727 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.2728 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.2729 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2730 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2731 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.2732 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi") ]  -- l.2733 `andq %rdi, %rcx`

/-- Segment 87 of the body: the 32 instructions from source lines 2734–2765. -/
def ed25519ScReduceShippedSeg087 : List (JInstr 64) :=
  [ .mov "%rdi" (.reg "%r10"),  -- l.2734 `movq %r10, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2735 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.2736 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2737 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.2738 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.2739 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.2740 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.2741 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r12"),  -- l.2742 `andq %r12, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2743 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r12"),  -- l.2744 `xorq %r12, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2745 `movq $18446744073709551615, %rbx`
    .loadMem "%r10" "%rsp" 32,  -- l.2746 `movq 32(%rsp), %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.2747 `xorq %rbx, %r10`
    .mov "%rbx" (.reg "%rsi"),  -- l.2748 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.2749 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2750 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2751 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2752 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2753 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2754 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2755 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2756 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.2757 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 40,  -- l.2758 `movq 40(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 104,  -- l.2759 `movq 104(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2760 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2761 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 40,  -- l.2762 `movq 40(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.2763 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2764 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14") ]  -- l.2765 `mulx %r14, %rsi, %rcx`

/-- Segment 88 of the body: the 32 instructions from source lines 2766–2797. -/
def ed25519ScReduceShippedSeg088 : List (JInstr 64) :=
  [ .loadMem "%rsi" "%rsp" (-128),  -- l.2766 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2767 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2768 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2769 `addq %rbx, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.2770 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%r10"),  -- l.2771 `movq %r10, %rcx`
    .add "%rcx" (.reg "%r11"),  -- l.2772 `addq %r11, %rcx`
    .mov "%r12" (.reg "%rcx"),  -- l.2773 `movq %rcx, %r12`
    .mov "%rcx" (.reg "%rsi"),  -- l.2774 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2775 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.2776 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.2777 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2778 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.2779 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2780 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.2781 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2782 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2783 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2784 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2785 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2786 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2787 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2788 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2789 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r10"),  -- l.2790 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.2791 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.2792 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.2793 `xorq %r11, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2794 `movq $18446744073709551615, %rdi`
    .mov "%r10" (.reg "%r12"),  -- l.2795 `movq %r12, %r10`
    .xor_ "%r10" (.reg "%rdi"),  -- l.2796 `xorq %rdi, %r10`
    .mov "%rdi" (.reg "%rsi") ]  -- l.2797 `movq %rsi, %rdi`

/-- Segment 89 of the body: the 32 instructions from source lines 2798–2829. -/
def ed25519ScReduceShippedSeg089 : List (JInstr 64) :=
  [ .and_ "%rdi" (.reg "%r10"),  -- l.2798 `andq %r10, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2799 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2800 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2801 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2802 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2803 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2804 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2805 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2806 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 40,  -- l.2807 `movq 40(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 96,  -- l.2808 `movq 96(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2809 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2810 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 40,  -- l.2811 `movq 40(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 96,  -- l.2812 `movq 96(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2813 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2814 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2815 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2816 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2817 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2818 `addq %rbx, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.2819 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%r10"),  -- l.2820 `movq %r10, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.2821 `addq %r9, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.2822 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.2823 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2824 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.2825 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.2826 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2827 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.2828 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%rbx") ]  -- l.2829 `xorq %rbx, %rsi`

/-- Segment 90 of the body: the 32 instructions from source lines 2830–2861. -/
def ed25519ScReduceShippedSeg090 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%r13"),  -- l.2830 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2831 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2832 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2833 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2834 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2835 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2836 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2837 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2838 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r10"),  -- l.2839 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.2840 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.2841 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.2842 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2843 `movq $18446744073709551615, %rdi`
    .mov "%r9" (.reg "%r11"),  -- l.2844 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rdi"),  -- l.2845 `xorq %rdi, %r9`
    .mov "%rdi" (.reg "%rsi"),  -- l.2846 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r9"),  -- l.2847 `andq %r9, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2848 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2849 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2850 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2851 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2852 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2853 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2854 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2855 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 40,  -- l.2856 `movq 40(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 88,  -- l.2857 `movq 88(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2858 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2859 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 40,  -- l.2860 `movq 40(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 88 ]  -- l.2861 `movq 88(%rsp), %r14`

/-- Segment 91 of the body: the 32 instructions from source lines 2862–2893. -/
def ed25519ScReduceShippedSeg091 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2862 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2863 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2864 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2865 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2866 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2867 `addq %rbx, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.2868 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.2869 `movq %r9, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.2870 `addq %rax, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.2871 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.2872 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2873 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.2874 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.2875 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2876 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.2877 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2878 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.2879 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2880 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2881 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2882 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2883 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2884 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2885 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2886 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2887 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r9"),  -- l.2888 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.2889 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.2890 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2891 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.2892 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r10") ]  -- l.2893 `movq %r10, %rdi`

/-- Segment 92 of the body: the 32 instructions from source lines 2894–2925. -/
def ed25519ScReduceShippedSeg092 : List (JInstr 64) :=
  [ .xor_ "%rdi" (.reg "%rax"),  -- l.2894 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.2895 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.2896 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.2897 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2898 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.2899 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.2900 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.2901 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.2902 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.2903 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.2904 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 56,  -- l.2905 `movq 56(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 112,  -- l.2906 `movq 112(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2907 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.2908 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 56,  -- l.2909 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.2910 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2911 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2912 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2913 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2914 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.2915 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.2916 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.2917 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.2918 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2919 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r12"),  -- l.2920 `addq %r12, %rdi`
    .mov "%r9" (.reg "%rdi"),  -- l.2921 `movq %rdi, %r9`
    .mov "%rdi" (.imm 0),  -- l.2922 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.2923 `movq %rcx, %r13`
    .and_ "%r13" (.reg "%rdi"),  -- l.2924 `andq %rdi, %r13`
    .mov "%rdi" (.imm 0) ]  -- l.2925 `movq $0, %rdi`

/-- Segment 93 of the body: the 32 instructions from source lines 2926–2957. -/
def ed25519ScReduceShippedSeg093 : List (JInstr 64) :=
  [ .mov "%r8" (.reg "%rcx"),  -- l.2926 `movq %rcx, %r8`
    .xor_ "%r8" (.reg "%rdi"),  -- l.2927 `xorq %rdi, %r8`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.2928 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2929 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2930 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r8"),  -- l.2931 `movq %r8, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.2932 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r13"),  -- l.2933 `movq %r13, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2934 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.2935 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2936 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.2937 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.2938 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.2939 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.2940 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r12"),  -- l.2941 `andq %r12, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2942 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r12"),  -- l.2943 `xorq %r12, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2944 `movq $18446744073709551615, %rbx`
    .mov "%r8" (.reg "%r9"),  -- l.2945 `movq %r9, %r8`
    .xor_ "%r8" (.reg "%rbx"),  -- l.2946 `xorq %rbx, %r8`
    .mov "%rbx" (.reg "%rsi"),  -- l.2947 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.2948 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2949 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2950 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2951 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2952 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2953 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2954 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2955 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.2956 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 56 ]  -- l.2957 `movq 56(%rsp), %rcx`

/-- Segment 94 of the body: the 32 instructions from source lines 2958–2989. -/
def ed25519ScReduceShippedSeg094 : List (JInstr 64) :=
  [ .loadMem "%r15" "%rsp" 104,  -- l.2958 `movq 104(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2959 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2960 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.2961 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.2962 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2963 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2964 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2965 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2966 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2967 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2968 `addq %rbx, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.2969 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%r8"),  -- l.2970 `movq %r8, %rcx`
    .add "%rcx" (.reg "%r11"),  -- l.2971 `addq %r11, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.2972 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.2973 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2974 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2975 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2976 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2977 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.2978 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2979 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2980 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2981 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2982 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2983 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2984 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2985 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2986 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2987 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2988 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r8") ]  -- l.2989 `movq %r8, %rbx`

/-- Segment 95 of the body: the 32 instructions from source lines 2990–3021. -/
def ed25519ScReduceShippedSeg095 : List (JInstr 64) :=
  [ .and_ "%rbx" (.reg "%r11"),  -- l.2990 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.2991 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.2992 `xorq %r11, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2993 `movq $18446744073709551615, %rdi`
    .mov "%r8" (.reg "%r9"),  -- l.2994 `movq %r9, %r8`
    .xor_ "%r8" (.reg "%rdi"),  -- l.2995 `xorq %rdi, %r8`
    .mov "%rdi" (.reg "%rsi"),  -- l.2996 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r8"),  -- l.2997 `andq %r8, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2998 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2999 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3000 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3001 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3002 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3003 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3004 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.3005 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.3006 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 96,  -- l.3007 `movq 96(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3008 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3009 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.3010 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 96,  -- l.3011 `movq 96(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.3012 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3013 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.3014 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.3015 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3016 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3017 `addq %rbx, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.3018 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%r8"),  -- l.3019 `movq %r8, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.3020 `addq %r10, %rcx`
    .mov "%r9" (.reg "%rcx") ]  -- l.3021 `movq %rcx, %r9`

/-- Segment 96 of the body: the 32 instructions from source lines 3022–3053. -/
def ed25519ScReduceShippedSeg096 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rsi"),  -- l.3022 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.3023 `andq %rbx, %rcx`
    .mov "%r11" (.reg "%rsi"),  -- l.3024 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.3025 `xorq %rbx, %r11`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3026 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3027 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3028 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r11"),  -- l.3029 `movq %r11, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3030 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3031 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3032 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3033 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3034 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3035 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3036 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3037 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r8"),  -- l.3038 `movq %r8, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.3039 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3040 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.3041 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.3042 `movq $18446744073709551615, %rdi`
    .mov "%r8" (.reg "%r9"),  -- l.3043 `movq %r9, %r8`
    .xor_ "%r8" (.reg "%rdi"),  -- l.3044 `xorq %rdi, %r8`
    .mov "%rdi" (.reg "%rsi"),  -- l.3045 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r8"),  -- l.3046 `andq %r8, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.3047 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.3048 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3049 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3050 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3051 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3052 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx") ]  -- l.3053 `addq %rbx, %rsi`

/-- Segment 97 of the body: the 32 instructions from source lines 3054–3085. -/
def ed25519ScReduceShippedSeg097 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%rsi"),  -- l.3054 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.3055 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 88,  -- l.3056 `movq 88(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3057 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3058 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.3059 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 88,  -- l.3060 `movq 88(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.3061 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3062 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.3063 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.3064 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3065 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3066 `addq %rbx, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.3067 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%r8"),  -- l.3068 `movq %r8, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.3069 `addq %rax, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.3070 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.3071 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.3072 `andq %rbx, %rcx`
    .mov "%r10" (.reg "%rsi"),  -- l.3073 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.3074 `xorq %rbx, %r10`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3075 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3076 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3077 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r10"),  -- l.3078 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3079 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3080 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3081 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3082 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3083 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3084 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi") ]  -- l.3085 `movq %rdi, %rcx`

/-- Segment 98 of the body: the 32 instructions from source lines 3086–3117. -/
def ed25519ScReduceShippedSeg098 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%rbx"),  -- l.3086 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r8"),  -- l.3087 `movq %r8, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.3088 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3089 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.3090 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.3091 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r9"),  -- l.3092 `movq %r9, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.3093 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.3094 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.3095 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.3096 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.3097 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.3098 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.3099 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.3100 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.3101 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.3102 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.3103 `movq %rbx, %rax`
    .mov "%rax" (.imm 18446744073709551615),  -- l.3104 `movq $18446744073709551615, %rax`
    .loadMem "%rbx" "%rsp" 64,  -- l.3105 `movq 64(%rsp), %rbx`
    .xor_ "%rbx" (.reg "%rax"),  -- l.3106 `xorq %rax, %rbx`
    .loadMem "%rax" "%rsp" 72,  -- l.3107 `movq 72(%rsp), %rax`
    .add "%rax" (.reg "%rbx"),  -- l.3108 `addq %rbx, %rax`
    .mov "%rbx" (.reg "%rax"),  -- l.3109 `movq %rax, %rbx`
    .mov "%rax" (.imm 1),  -- l.3110 `movq $1, %rax`
    .mov "%rcx" (.reg "%rbx"),  -- l.3111 `movq %rbx, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.3112 `addq %rax, %rcx`
    .mov "%rax" (.reg "%rcx"),  -- l.3113 `movq %rcx, %rax`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3114 `movq $18446744073709551615, %rcx`
    .loadMem "%rsi" "%rsp" 64,  -- l.3115 `movq 64(%rsp), %rsi`
    .xor_ "%rsi" (.reg "%rcx"),  -- l.3116 `xorq %rcx, %rsi`
    .loadMem "%rcx" "%rsp" 72 ]  -- l.3117 `movq 72(%rsp), %rcx`

/-- Segment 99 of the body: the 32 instructions from source lines 3118–3149. -/
def ed25519ScReduceShippedSeg099 : List (JInstr 64) :=
  [ .and_ "%rcx" (.reg "%rsi"),  -- l.3118 `andq %rsi, %rcx`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.3119 `movq $18446744073709551615, %rsi`
    .loadMem "%rdi" "%rsp" 64,  -- l.3120 `movq 64(%rsp), %rdi`
    .xor_ "%rdi" (.reg "%rsi"),  -- l.3121 `xorq %rsi, %rdi`
    .loadMem "%rsi" "%rsp" 72,  -- l.3122 `movq 72(%rsp), %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.3123 `xorq %rdi, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.3124 `movq $18446744073709551615, %rdi`
    .mov "%r8" (.reg "%rbx"),  -- l.3125 `movq %rbx, %r8`
    .xor_ "%r8" (.reg "%rdi"),  -- l.3126 `xorq %rdi, %r8`
    .mov "%rdi" (.reg "%rsi"),  -- l.3127 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r8"),  -- l.3128 `andq %r8, %rdi`
    .mov "%rsi" (.reg "%rcx"),  -- l.3129 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.3130 `xorq %rdi, %rsi`
    .mov "%rcx" (.imm 63),  -- l.3131 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rsi"),  -- l.3132 `movq %rsi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3133 `shrq $63, %rcx`
    .mov "%rsi" (.imm 1),  -- l.3134 `movq $1, %rsi`
    .mov "%rdi" (.reg "%rbx"),  -- l.3135 `movq %rbx, %rdi`
    .and_ "%rdi" (.reg "%rsi"),  -- l.3136 `andq %rsi, %rdi`
    .mov "%rsi" (.imm 1),  -- l.3137 `movq $1, %rsi`
    .mov "%r8" (.reg "%rbx"),  -- l.3138 `movq %rbx, %r8`
    .xor_ "%r8" (.reg "%rsi"),  -- l.3139 `xorq %rsi, %r8`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3140 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rax"),  -- l.3141 `movq %rax, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3142 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r8"),  -- l.3143 `movq %r8, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3144 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rdi"),  -- l.3145 `movq %rdi, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3146 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3147 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3148 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63) ]  -- l.3149 `shrq $63, %rbx`

/-- Segment 100 of the body: the 32 instructions from source lines 3150–3181. -/
def ed25519ScReduceShippedSeg100 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rcx"),  -- l.3150 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3151 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.3152 `movq %rsi, %rbx`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3153 `movq $18446744073709551615, %rcx`
    .loadMem "%rsi" "%rsp" 48,  -- l.3154 `movq 48(%rsp), %rsi`
    .xor_ "%rsi" (.reg "%rcx"),  -- l.3155 `xorq %rcx, %rsi`
    .loadMem "%rcx" "%rsp" 80,  -- l.3156 `movq 80(%rsp), %rcx`
    .add "%rcx" (.reg "%rsi"),  -- l.3157 `addq %rsi, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3158 `movq %rcx, %rsi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3159 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3160 `addq %rbx, %rcx`
    .mov "%rdi" (.reg "%rcx"),  -- l.3161 `movq %rcx, %rdi`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3162 `movq $18446744073709551615, %rcx`
    .loadMem "%r8" "%rsp" 48,  -- l.3163 `movq 48(%rsp), %r8`
    .xor_ "%r8" (.reg "%rcx"),  -- l.3164 `xorq %rcx, %r8`
    .loadMem "%rcx" "%rsp" 80,  -- l.3165 `movq 80(%rsp), %rcx`
    .and_ "%rcx" (.reg "%r8"),  -- l.3166 `andq %r8, %rcx`
    .mov "%r8" (.imm 18446744073709551615),  -- l.3167 `movq $18446744073709551615, %r8`
    .loadMem "%r9" "%rsp" 48,  -- l.3168 `movq 48(%rsp), %r9`
    .xor_ "%r9" (.reg "%r8"),  -- l.3169 `xorq %r8, %r9`
    .loadMem "%r8" "%rsp" 80,  -- l.3170 `movq 80(%rsp), %r8`
    .xor_ "%r8" (.reg "%r9"),  -- l.3171 `xorq %r9, %r8`
    .mov "%r9" (.imm 18446744073709551615),  -- l.3172 `movq $18446744073709551615, %r9`
    .mov "%r10" (.reg "%rsi"),  -- l.3173 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%r9"),  -- l.3174 `xorq %r9, %r10`
    .mov "%r9" (.reg "%r8"),  -- l.3175 `movq %r8, %r9`
    .and_ "%r9" (.reg "%r10"),  -- l.3176 `andq %r10, %r9`
    .mov "%r8" (.reg "%rcx"),  -- l.3177 `movq %rcx, %r8`
    .xor_ "%r8" (.reg "%r9"),  -- l.3178 `xorq %r9, %r8`
    .mov "%rcx" (.imm 63),  -- l.3179 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r8"),  -- l.3180 `movq %r8, %rcx`
    .shr "%rcx" (.imm 63) ]  -- l.3181 `shrq $63, %rcx`

/-- Segment 101 of the body: the 32 instructions from source lines 3182–3213. -/
def ed25519ScReduceShippedSeg101 : List (JInstr 64) :=
  [ .mov "%r8" (.reg "%rsi"),  -- l.3182 `movq %rsi, %r8`
    .and_ "%r8" (.reg "%rbx"),  -- l.3183 `andq %rbx, %r8`
    .mov "%r9" (.reg "%rsi"),  -- l.3184 `movq %rsi, %r9`
    .xor_ "%r9" (.reg "%rbx"),  -- l.3185 `xorq %rbx, %r9`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3186 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rdi"),  -- l.3187 `movq %rdi, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3188 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r9"),  -- l.3189 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3190 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3191 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3192 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3193 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3194 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3195 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3196 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3197 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.3198 `movq %rsi, %rbx`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3199 `movq $18446744073709551615, %rcx`
    .mov "%rsi" (.reg "%rbp"),  -- l.3200 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rcx"),  -- l.3201 `xorq %rcx, %rsi`
    .loadMem "%rcx" "%rsp" 120,  -- l.3202 `movq 120(%rsp), %rcx`
    .add "%rcx" (.reg "%rsi"),  -- l.3203 `addq %rsi, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3204 `movq %rcx, %rsi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3205 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3206 `addq %rbx, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.3207 `movq %rcx, %r8`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3208 `movq $18446744073709551615, %rcx`
    .mov "%r9" (.reg "%rbp"),  -- l.3209 `movq %rbp, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.3210 `xorq %rcx, %r9`
    .loadMem "%rcx" "%rsp" 120,  -- l.3211 `movq 120(%rsp), %rcx`
    .and_ "%rcx" (.reg "%r9"),  -- l.3212 `andq %r9, %rcx`
    .mov "%r9" (.imm 18446744073709551615) ]  -- l.3213 `movq $18446744073709551615, %r9`

/-- Segment 102 of the body: the 32 instructions from source lines 3214–3245. -/
def ed25519ScReduceShippedSeg102 : List (JInstr 64) :=
  [ .mov "%r10" (.reg "%rbp"),  -- l.3214 `movq %rbp, %r10`
    .xor_ "%r10" (.reg "%r9"),  -- l.3215 `xorq %r9, %r10`
    .loadMem "%rbp" "%rsp" 120,  -- l.3216 `movq 120(%rsp), %rbp`
    .xor_ "%rbp" (.reg "%r10"),  -- l.3217 `xorq %r10, %rbp`
    .mov "%r9" (.imm 18446744073709551615),  -- l.3218 `movq $18446744073709551615, %r9`
    .mov "%r10" (.reg "%rsi"),  -- l.3219 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%r9"),  -- l.3220 `xorq %r9, %r10`
    .mov "%r9" (.reg "%rbp"),  -- l.3221 `movq %rbp, %r9`
    .and_ "%r9" (.reg "%r10"),  -- l.3222 `andq %r10, %r9`
    .mov "%rbp" (.reg "%rcx"),  -- l.3223 `movq %rcx, %rbp`
    .xor_ "%rbp" (.reg "%r9"),  -- l.3224 `xorq %r9, %rbp`
    .mov "%rcx" (.imm 63),  -- l.3225 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rbp"),  -- l.3226 `movq %rbp, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3227 `shrq $63, %rcx`
    .mov "%rbp" (.reg "%rsi"),  -- l.3228 `movq %rsi, %rbp`
    .and_ "%rbp" (.reg "%rbx"),  -- l.3229 `andq %rbx, %rbp`
    .mov "%r9" (.reg "%rsi"),  -- l.3230 `movq %rsi, %r9`
    .xor_ "%r9" (.reg "%rbx"),  -- l.3231 `xorq %rbx, %r9`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3232 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3233 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3234 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r9"),  -- l.3235 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3236 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.3237 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3238 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3239 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3240 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3241 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3242 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3243 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.3244 `movq %rsi, %rbx`
    .mov "%rcx" (.imm 18446744073709551615) ]  -- l.3245 `movq $18446744073709551615, %rcx`

/-- Segment 103 of the body: the 32 instructions from source lines 3246–3277. -/
def ed25519ScReduceShippedSeg103 : List (JInstr 64) :=
  [ .loadMem "%rsi" "%rsp" 32,  -- l.3246 `movq 32(%rsp), %rsi`
    .xor_ "%rsi" (.reg "%rcx"),  -- l.3247 `xorq %rcx, %rsi`
    .loadMem "%rcx" "%rsp" 128,  -- l.3248 `movq 128(%rsp), %rcx`
    .add "%rcx" (.reg "%rsi"),  -- l.3249 `addq %rsi, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3250 `movq %rcx, %rsi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3251 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3252 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.3253 `movq %rcx, %rbp`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3254 `movq $18446744073709551615, %rcx`
    .loadMem "%r9" "%rsp" 32,  -- l.3255 `movq 32(%rsp), %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.3256 `xorq %rcx, %r9`
    .loadMem "%rcx" "%rsp" 128,  -- l.3257 `movq 128(%rsp), %rcx`
    .and_ "%rcx" (.reg "%r9"),  -- l.3258 `andq %r9, %rcx`
    .mov "%r9" (.imm 18446744073709551615),  -- l.3259 `movq $18446744073709551615, %r9`
    .loadMem "%r10" "%rsp" 32,  -- l.3260 `movq 32(%rsp), %r10`
    .xor_ "%r10" (.reg "%r9"),  -- l.3261 `xorq %r9, %r10`
    .loadMem "%r9" "%rsp" 128,  -- l.3262 `movq 128(%rsp), %r9`
    .xor_ "%r9" (.reg "%r10"),  -- l.3263 `xorq %r10, %r9`
    .mov "%r10" (.imm 18446744073709551615),  -- l.3264 `movq $18446744073709551615, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.3265 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%r10"),  -- l.3266 `xorq %r10, %r11`
    .mov "%r10" (.reg "%r9"),  -- l.3267 `movq %r9, %r10`
    .and_ "%r10" (.reg "%r11"),  -- l.3268 `andq %r11, %r10`
    .mov "%r9" (.reg "%rcx"),  -- l.3269 `movq %rcx, %r9`
    .xor_ "%r9" (.reg "%r10"),  -- l.3270 `xorq %r10, %r9`
    .mov "%rcx" (.imm 63),  -- l.3271 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r9"),  -- l.3272 `movq %r9, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3273 `shrq $63, %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.3274 `movq %rsi, %r9`
    .and_ "%r9" (.reg "%rbx"),  -- l.3275 `andq %rbx, %r9`
    .mov "%r10" (.reg "%rsi"),  -- l.3276 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%rbx") ]  -- l.3277 `xorq %rbx, %r10`

/-- Segment 104 of the body: the 32 instructions from source lines 3278–3309. -/
def ed25519ScReduceShippedSeg104 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 18446744073709551615),  -- l.3278 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.3279 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3280 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r10"),  -- l.3281 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3282 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.3283 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3284 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3285 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3286 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3287 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3288 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3289 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.3290 `movq %rsi, %rbx`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3291 `movq $18446744073709551615, %rbx`
    .loadMem "%rcx" "%rsp" 112,  -- l.3292 `movq 112(%rsp), %rcx`
    .xor_ "%rcx" (.reg "%rbx"),  -- l.3293 `xorq %rbx, %rcx`
    .mov "%rbx" (.reg "%rax"),  -- l.3294 `movq %rax, %rbx`
    .add "%rbx" (.reg "%rcx"),  -- l.3295 `addq %rcx, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.3296 `movq %rbx, %rcx`
    .mov "%rbx" (.imm 1),  -- l.3297 `movq $1, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3298 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3299 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.3300 `movq %rsi, %rbx`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.3301 `movq $18446744073709551615, %rsi`
    .loadMem "%r9" "%rsp" 112,  -- l.3302 `movq 112(%rsp), %r9`
    .xor_ "%r9" (.reg "%rsi"),  -- l.3303 `xorq %rsi, %r9`
    .mov "%rsi" (.reg "%rax"),  -- l.3304 `movq %rax, %rsi`
    .and_ "%rsi" (.reg "%r9"),  -- l.3305 `andq %r9, %rsi`
    .mov "%r9" (.imm 18446744073709551615),  -- l.3306 `movq $18446744073709551615, %r9`
    .loadMem "%r10" "%rsp" 112,  -- l.3307 `movq 112(%rsp), %r10`
    .xor_ "%r10" (.reg "%r9"),  -- l.3308 `xorq %r9, %r10`
    .mov "%r9" (.reg "%rax") ]  -- l.3309 `movq %rax, %r9`

/-- Segment 105 of the body: the 32 instructions from source lines 3310–3341. -/
def ed25519ScReduceShippedSeg105 : List (JInstr 64) :=
  [ .xor_ "%r9" (.reg "%r10"),  -- l.3310 `xorq %r10, %r9`
    .mov "%r10" (.imm 18446744073709551615),  -- l.3311 `movq $18446744073709551615, %r10`
    .mov "%r11" (.reg "%rcx"),  -- l.3312 `movq %rcx, %r11`
    .xor_ "%r11" (.reg "%r10"),  -- l.3313 `xorq %r10, %r11`
    .mov "%r10" (.reg "%r9"),  -- l.3314 `movq %r9, %r10`
    .and_ "%r10" (.reg "%r11"),  -- l.3315 `andq %r11, %r10`
    .mov "%r9" (.reg "%rsi"),  -- l.3316 `movq %rsi, %r9`
    .xor_ "%r9" (.reg "%r10"),  -- l.3317 `xorq %r10, %r9`
    .mov "%rsi" (.imm 63),  -- l.3318 `movq $63, %rsi`
    .mov "%rsi" (.reg "%r9"),  -- l.3319 `movq %r9, %rsi`
    .shr "%rsi" (.imm 63),  -- l.3320 `shrq $63, %rsi`
    .mov "%r9" (.imm 1),  -- l.3321 `movq $1, %r9`
    .mov "%r10" (.reg "%rcx"),  -- l.3322 `movq %rcx, %r10`
    .and_ "%r10" (.reg "%r9"),  -- l.3323 `andq %r9, %r10`
    .mov "%r9" (.imm 1),  -- l.3324 `movq $1, %r9`
    .mov "%r11" (.reg "%rcx"),  -- l.3325 `movq %rcx, %r11`
    .xor_ "%r11" (.reg "%r9"),  -- l.3326 `xorq %r9, %r11`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3327 `movq $18446744073709551615, %rcx`
    .mov "%r9" (.reg "%rbx"),  -- l.3328 `movq %rbx, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.3329 `xorq %rcx, %r9`
    .mov "%rcx" (.reg "%r11"),  -- l.3330 `movq %r11, %rcx`
    .and_ "%rcx" (.reg "%r9"),  -- l.3331 `andq %r9, %rcx`
    .mov "%r9" (.reg "%r10"),  -- l.3332 `movq %r10, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.3333 `xorq %rcx, %r9`
    .mov "%rcx" (.imm 63),  -- l.3334 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r9"),  -- l.3335 `movq %r9, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3336 `shrq $63, %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.3337 `movq %rsi, %r9`
    .add "%r9" (.reg "%rcx"),  -- l.3338 `addq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.3339 `movq %r9, %rcx`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.3340 `movq $18446744073709551615, %rsi`
    .loadMem "%r9" "%rsp" 104 ]  -- l.3341 `movq 104(%rsp), %r9`

/-- Segment 106 of the body: the 32 instructions from source lines 3342–3373. -/
def ed25519ScReduceShippedSeg106 : List (JInstr 64) :=
  [ .xor_ "%r9" (.reg "%rsi"),  -- l.3342 `xorq %rsi, %r9`
    .mov "%rsi" (.reg "%rdi"),  -- l.3343 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%r9"),  -- l.3344 `addq %r9, %rsi`
    .mov "%r9" (.reg "%rsi"),  -- l.3345 `movq %rsi, %r9`
    .mov "%rsi" (.reg "%r9"),  -- l.3346 `movq %r9, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.3347 `addq %rcx, %rsi`
    .mov "%r10" (.reg "%rsi"),  -- l.3348 `movq %rsi, %r10`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.3349 `movq $18446744073709551615, %rsi`
    .loadMem "%r11" "%rsp" 104,  -- l.3350 `movq 104(%rsp), %r11`
    .xor_ "%r11" (.reg "%rsi"),  -- l.3351 `xorq %rsi, %r11`
    .mov "%rsi" (.reg "%rdi"),  -- l.3352 `movq %rdi, %rsi`
    .and_ "%rsi" (.reg "%r11"),  -- l.3353 `andq %r11, %rsi`
    .mov "%r11" (.imm 18446744073709551615),  -- l.3354 `movq $18446744073709551615, %r11`
    .loadMem "%r12" "%rsp" 104,  -- l.3355 `movq 104(%rsp), %r12`
    .xor_ "%r12" (.reg "%r11"),  -- l.3356 `xorq %r11, %r12`
    .mov "%r11" (.reg "%rdi"),  -- l.3357 `movq %rdi, %r11`
    .xor_ "%r11" (.reg "%r12"),  -- l.3358 `xorq %r12, %r11`
    .mov "%r12" (.imm 18446744073709551615),  -- l.3359 `movq $18446744073709551615, %r12`
    .mov "%r13" (.reg "%r9"),  -- l.3360 `movq %r9, %r13`
    .xor_ "%r13" (.reg "%r12"),  -- l.3361 `xorq %r12, %r13`
    .mov "%r12" (.reg "%r11"),  -- l.3362 `movq %r11, %r12`
    .and_ "%r12" (.reg "%r13"),  -- l.3363 `andq %r13, %r12`
    .mov "%r11" (.reg "%rsi"),  -- l.3364 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%r12"),  -- l.3365 `xorq %r12, %r11`
    .mov "%rsi" (.imm 63),  -- l.3366 `movq $63, %rsi`
    .mov "%rsi" (.reg "%r11"),  -- l.3367 `movq %r11, %rsi`
    .shr "%rsi" (.imm 63),  -- l.3368 `shrq $63, %rsi`
    .mov "%r11" (.reg "%r9"),  -- l.3369 `movq %r9, %r11`
    .and_ "%r11" (.reg "%rcx"),  -- l.3370 `andq %rcx, %r11`
    .mov "%r12" (.reg "%r9"),  -- l.3371 `movq %r9, %r12`
    .xor_ "%r12" (.reg "%rcx"),  -- l.3372 `xorq %rcx, %r12`
    .mov "%rcx" (.imm 18446744073709551615) ]  -- l.3373 `movq $18446744073709551615, %rcx`

/-- Segment 107 of the body: the 32 instructions from source lines 3374–3405. -/
def ed25519ScReduceShippedSeg107 : List (JInstr 64) :=
  [ .mov "%r9" (.reg "%r10"),  -- l.3374 `movq %r10, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.3375 `xorq %rcx, %r9`
    .mov "%rcx" (.reg "%r12"),  -- l.3376 `movq %r12, %rcx`
    .and_ "%rcx" (.reg "%r9"),  -- l.3377 `andq %r9, %rcx`
    .mov "%r9" (.reg "%r11"),  -- l.3378 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.3379 `xorq %rcx, %r9`
    .mov "%rcx" (.imm 63),  -- l.3380 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r9"),  -- l.3381 `movq %r9, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3382 `shrq $63, %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.3383 `movq %rsi, %r9`
    .add "%r9" (.reg "%rcx"),  -- l.3384 `addq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.3385 `movq %r9, %rcx`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.3386 `movq $18446744073709551615, %rsi`
    .loadMem "%r9" "%rsp" 96,  -- l.3387 `movq 96(%rsp), %r9`
    .xor_ "%r9" (.reg "%rsi"),  -- l.3388 `xorq %rsi, %r9`
    .mov "%rsi" (.reg "%r8"),  -- l.3389 `movq %r8, %rsi`
    .add "%rsi" (.reg "%r9"),  -- l.3390 `addq %r9, %rsi`
    .mov "%r9" (.reg "%rsi"),  -- l.3391 `movq %rsi, %r9`
    .mov "%rsi" (.reg "%r9"),  -- l.3392 `movq %r9, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.3393 `addq %rcx, %rsi`
    .mov "%r15" (.reg "%rsi"),  -- l.3394 `movq %rsi, %r15`
    .storeMem "%rsp" 128 (.reg "%r15"),  -- l.3395 `movq %r15, 128(%rsp)`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.3396 `movq $18446744073709551615, %rsi`
    .loadMem "%r12" "%rsp" 96,  -- l.3397 `movq 96(%rsp), %r12`
    .xor_ "%r12" (.reg "%rsi"),  -- l.3398 `xorq %rsi, %r12`
    .mov "%rsi" (.reg "%r8"),  -- l.3399 `movq %r8, %rsi`
    .and_ "%rsi" (.reg "%r12"),  -- l.3400 `andq %r12, %rsi`
    .mov "%r12" (.imm 18446744073709551615),  -- l.3401 `movq $18446744073709551615, %r12`
    .loadMem "%r13" "%rsp" 96,  -- l.3402 `movq 96(%rsp), %r13`
    .xor_ "%r13" (.reg "%r12"),  -- l.3403 `xorq %r12, %r13`
    .mov "%r12" (.reg "%r8"),  -- l.3404 `movq %r8, %r12`
    .xor_ "%r12" (.reg "%r13") ]  -- l.3405 `xorq %r13, %r12`

/-- Segment 108 of the body: the 32 instructions from source lines 3406–3437. -/
def ed25519ScReduceShippedSeg108 : List (JInstr 64) :=
  [ .mov "%r13" (.imm 18446744073709551615),  -- l.3406 `movq $18446744073709551615, %r13`
    .mov "%r11" (.reg "%r9"),  -- l.3407 `movq %r9, %r11`
    .xor_ "%r11" (.reg "%r13"),  -- l.3408 `xorq %r13, %r11`
    .mov "%r13" (.reg "%r12"),  -- l.3409 `movq %r12, %r13`
    .and_ "%r13" (.reg "%r11"),  -- l.3410 `andq %r11, %r13`
    .mov "%r11" (.reg "%rsi"),  -- l.3411 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%r13"),  -- l.3412 `xorq %r13, %r11`
    .mov "%rsi" (.imm 63),  -- l.3413 `movq $63, %rsi`
    .mov "%rsi" (.reg "%r11"),  -- l.3414 `movq %r11, %rsi`
    .shr "%rsi" (.imm 63),  -- l.3415 `shrq $63, %rsi`
    .mov "%r11" (.reg "%r9"),  -- l.3416 `movq %r9, %r11`
    .and_ "%r11" (.reg "%rcx"),  -- l.3417 `andq %rcx, %r11`
    .mov "%r12" (.reg "%r9"),  -- l.3418 `movq %r9, %r12`
    .xor_ "%r12" (.reg "%rcx"),  -- l.3419 `xorq %rcx, %r12`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3420 `movq $18446744073709551615, %rcx`
    .loadMem "%r9" "%rsp" 128,  -- l.3421 `movq 128(%rsp), %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.3422 `xorq %rcx, %r9`
    .mov "%rcx" (.reg "%r12"),  -- l.3423 `movq %r12, %rcx`
    .and_ "%rcx" (.reg "%r9"),  -- l.3424 `andq %r9, %rcx`
    .mov "%r9" (.reg "%r11"),  -- l.3425 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.3426 `xorq %rcx, %r9`
    .mov "%rcx" (.imm 63),  -- l.3427 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r9"),  -- l.3428 `movq %r9, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3429 `shrq $63, %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.3430 `movq %rsi, %r9`
    .add "%r9" (.reg "%rcx"),  -- l.3431 `addq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.3432 `movq %r9, %rcx`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.3433 `movq $18446744073709551615, %rsi`
    .loadMem "%r9" "%rsp" 88,  -- l.3434 `movq 88(%rsp), %r9`
    .xor_ "%r9" (.reg "%rsi"),  -- l.3435 `xorq %rsi, %r9`
    .mov "%rsi" (.reg "%rbp"),  -- l.3436 `movq %rbp, %rsi`
    .add "%rsi" (.reg "%r9") ]  -- l.3437 `addq %r9, %rsi`

/-- Segment 109 of the body: the 32 instructions from source lines 3438–3469. -/
def ed25519ScReduceShippedSeg109 : List (JInstr 64) :=
  [ .mov "%r9" (.reg "%rsi"),  -- l.3438 `movq %rsi, %r9`
    .mov "%rsi" (.reg "%r9"),  -- l.3439 `movq %r9, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.3440 `addq %rcx, %rsi`
    .mov "%r15" (.reg "%rsi"),  -- l.3441 `movq %rsi, %r15`
    .storeMem "%rsp" 120 (.reg "%r15"),  -- l.3442 `movq %r15, 120(%rsp)`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.3443 `movq $18446744073709551615, %rsi`
    .loadMem "%r12" "%rsp" 88,  -- l.3444 `movq 88(%rsp), %r12`
    .xor_ "%r12" (.reg "%rsi"),  -- l.3445 `xorq %rsi, %r12`
    .mov "%rsi" (.reg "%rbp"),  -- l.3446 `movq %rbp, %rsi`
    .and_ "%rsi" (.reg "%r12"),  -- l.3447 `andq %r12, %rsi`
    .mov "%r12" (.imm 18446744073709551615),  -- l.3448 `movq $18446744073709551615, %r12`
    .loadMem "%r13" "%rsp" 88,  -- l.3449 `movq 88(%rsp), %r13`
    .xor_ "%r13" (.reg "%r12"),  -- l.3450 `xorq %r12, %r13`
    .mov "%r12" (.reg "%rbp"),  -- l.3451 `movq %rbp, %r12`
    .xor_ "%r12" (.reg "%r13"),  -- l.3452 `xorq %r13, %r12`
    .mov "%r13" (.imm 18446744073709551615),  -- l.3453 `movq $18446744073709551615, %r13`
    .mov "%r11" (.reg "%r9"),  -- l.3454 `movq %r9, %r11`
    .xor_ "%r11" (.reg "%r13"),  -- l.3455 `xorq %r13, %r11`
    .mov "%r13" (.reg "%r12"),  -- l.3456 `movq %r12, %r13`
    .and_ "%r13" (.reg "%r11"),  -- l.3457 `andq %r11, %r13`
    .mov "%r11" (.reg "%rsi"),  -- l.3458 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%r13"),  -- l.3459 `xorq %r13, %r11`
    .mov "%rsi" (.imm 63),  -- l.3460 `movq $63, %rsi`
    .mov "%rsi" (.reg "%r11"),  -- l.3461 `movq %r11, %rsi`
    .shr "%rsi" (.imm 63),  -- l.3462 `shrq $63, %rsi`
    .mov "%r11" (.reg "%r9"),  -- l.3463 `movq %r9, %r11`
    .and_ "%r11" (.reg "%rcx"),  -- l.3464 `andq %rcx, %r11`
    .mov "%r12" (.reg "%r9"),  -- l.3465 `movq %r9, %r12`
    .xor_ "%r12" (.reg "%rcx"),  -- l.3466 `xorq %rcx, %r12`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3467 `movq $18446744073709551615, %rcx`
    .loadMem "%r9" "%rsp" 120,  -- l.3468 `movq 120(%rsp), %r9`
    .xor_ "%r9" (.reg "%rcx") ]  -- l.3469 `xorq %rcx, %r9`

/-- Segment 110 of the body: the 32 instructions from source lines 3470–3501. -/
def ed25519ScReduceShippedSeg110 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%r12"),  -- l.3470 `movq %r12, %rcx`
    .and_ "%rcx" (.reg "%r9"),  -- l.3471 `andq %r9, %rcx`
    .mov "%r9" (.reg "%r11"),  -- l.3472 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.3473 `xorq %rcx, %r9`
    .mov "%rcx" (.imm 63),  -- l.3474 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r9"),  -- l.3475 `movq %r9, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3476 `shrq $63, %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.3477 `movq %rsi, %r9`
    .add "%r9" (.reg "%rcx"),  -- l.3478 `addq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.3479 `movq %r9, %rcx`
    .mov "%rsi" (.imm 0),  -- l.3480 `movq $0, %rsi`
    .mov "%r9" (.reg "%rsi"),  -- l.3481 `movq %rsi, %r9`
    .sub "%r9" (.reg "%rcx"),  -- l.3482 `subq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.3483 `movq %r9, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.3484 `movq %rbx, %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.3485 `andq %rcx, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3486 `movq $18446744073709551615, %rbx`
    .mov "%r9" (.reg "%rcx"),  -- l.3487 `movq %rcx, %r9`
    .xor_ "%r9" (.reg "%rbx"),  -- l.3488 `xorq %rbx, %r9`
    .mov "%rbx" (.reg "%rax"),  -- l.3489 `movq %rax, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.3490 `andq %r9, %rbx`
    .mov "%rax" (.reg "%rsi"),  -- l.3491 `movq %rsi, %rax`
    .xor_ "%rax" (.reg "%rbx"),  -- l.3492 `xorq %rbx, %rax`
    .mov "%rbx" (.reg "%rax"),  -- l.3493 `movq %rax, %rbx`
    .mov "%rax" (.reg "%r10"),  -- l.3494 `movq %r10, %rax`
    .and_ "%rax" (.reg "%rcx"),  -- l.3495 `andq %rcx, %rax`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.3496 `movq $18446744073709551615, %rsi`
    .mov "%r9" (.reg "%rcx"),  -- l.3497 `movq %rcx, %r9`
    .xor_ "%r9" (.reg "%rsi"),  -- l.3498 `xorq %rsi, %r9`
    .mov "%rsi" (.reg "%rdi"),  -- l.3499 `movq %rdi, %rsi`
    .and_ "%rsi" (.reg "%r9"),  -- l.3500 `andq %r9, %rsi`
    .mov "%rdi" (.reg "%rax") ]  -- l.3501 `movq %rax, %rdi`

/-- Segment 111 of the body: the 32 instructions from source lines 3502–3533. -/
def ed25519ScReduceShippedSeg111 : List (JInstr 64) :=
  [ .xor_ "%rdi" (.reg "%rsi"),  -- l.3502 `xorq %rsi, %rdi`
    .mov "%rax" (.reg "%rdi"),  -- l.3503 `movq %rdi, %rax`
    .loadMem "%rsi" "%rsp" 128,  -- l.3504 `movq 128(%rsp), %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.3505 `andq %rcx, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.3506 `movq $18446744073709551615, %rdi`
    .mov "%r9" (.reg "%rcx"),  -- l.3507 `movq %rcx, %r9`
    .xor_ "%r9" (.reg "%rdi"),  -- l.3508 `xorq %rdi, %r9`
    .mov "%rdi" (.reg "%r8"),  -- l.3509 `movq %r8, %rdi`
    .and_ "%rdi" (.reg "%r9"),  -- l.3510 `andq %r9, %rdi`
    .mov "%r8" (.reg "%rsi"),  -- l.3511 `movq %rsi, %r8`
    .xor_ "%r8" (.reg "%rdi"),  -- l.3512 `xorq %rdi, %r8`
    .mov "%rsi" (.reg "%r8"),  -- l.3513 `movq %r8, %rsi`
    .loadMem "%rdi" "%rsp" 120,  -- l.3514 `movq 120(%rsp), %rdi`
    .and_ "%rdi" (.reg "%rcx"),  -- l.3515 `andq %rcx, %rdi`
    .mov "%r8" (.imm 18446744073709551615),  -- l.3516 `movq $18446744073709551615, %r8`
    .mov "%r9" (.reg "%rcx"),  -- l.3517 `movq %rcx, %r9`
    .xor_ "%r9" (.reg "%r8"),  -- l.3518 `xorq %r8, %r9`
    .mov "%rcx" (.reg "%rbp"),  -- l.3519 `movq %rbp, %rcx`
    .and_ "%rcx" (.reg "%r9"),  -- l.3520 `andq %r9, %rcx`
    .mov "%rbp" (.reg "%rdi"),  -- l.3521 `movq %rdi, %rbp`
    .xor_ "%rbp" (.reg "%rcx"),  -- l.3522 `xorq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.3523 `movq %rbp, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.3524 `movq %rbx, %rdi`
    .mov "%rbx" (.reg "%rax"),  -- l.3525 `movq %rax, %rbx`
    .mov "%rax" (.reg "%rsi"),  -- l.3526 `movq %rsi, %rax`
    .mov "%rsi" (.reg "%rcx"),  -- l.3527 `movq %rcx, %rsi`
    .loadMem "%r14" "%rsp" 232,  -- l.3528 `movq 232(%rsp), %r14`
    .loadMem "%r15" "%rsp" 144,  -- l.3529 `movq 144(%rsp), %r15`
    .storeMemIdx "%r14" "%r15" 8 (.reg "%rdi"),  -- l.3530 `movq %rdi, (%r14, %r15, 8)`
    .loadMem "%r14" "%rsp" 232,  -- l.3531 `movq 232(%rsp), %r14`
    .loadMem "%r15" "%rsp" 152,  -- l.3532 `movq 152(%rsp), %r15`
    .storeMemIdx "%r14" "%r15" 8 (.reg "%rbx") ]  -- l.3533 `movq %rbx, (%r14, %r15, 8)`

/-- Segment 112 of the body: the 32 instructions from source lines 3534–3565. -/
def ed25519ScReduceShippedSeg112 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 232,  -- l.3534 `movq 232(%rsp), %r14`
    .loadMem "%r15" "%rsp" 160,  -- l.3535 `movq 160(%rsp), %r15`
    .storeMemIdx "%r14" "%r15" 8 (.reg "%rax"),  -- l.3536 `movq %rax, (%r14, %r15, 8)`
    .loadMem "%r14" "%rsp" 232,  -- l.3537 `movq 232(%rsp), %r14`
    .loadMem "%r15" "%rsp" 168,  -- l.3538 `movq 168(%rsp), %r15`
    .storeMemIdx "%r14" "%r15" 8 (.reg "%rsi"),  -- l.3539 `movq %rsi, (%r14, %r15, 8)`
    .loadMem "%rbx" "%rsp" 216,  -- l.3540 `movq 216(%rsp), %rbx`
    .loadMem "%rbp" "%rsp" 208,  -- l.3541 `movq 208(%rsp), %rbp`
    .loadMem "%r12" "%rsp" 200,  -- l.3542 `movq 200(%rsp), %r12`
    .loadMem "%r13" "%rsp" 192,  -- l.3543 `movq 192(%rsp), %r13`
    .loadMem "%r14" "%rsp" 184,  -- l.3544 `movq 184(%rsp), %r14`
    .loadMem "%r15" "%rsp" 176,  -- l.3545 `movq 176(%rsp), %r15`
    .storeMem "%rsp" 232 (.imm 0),  -- l.3546 `movq $0, 232(%rsp)`
    .storeMem "%rsp" 224 (.imm 0),  -- l.3547 `movq $0, 224(%rsp)`
    .storeMem "%rsp" 216 (.imm 0),  -- l.3548 `movq $0, 216(%rsp)`
    .storeMem "%rsp" 208 (.imm 0),  -- l.3549 `movq $0, 208(%rsp)`
    .storeMem "%rsp" 200 (.imm 0),  -- l.3550 `movq $0, 200(%rsp)`
    .storeMem "%rsp" 192 (.imm 0),  -- l.3551 `movq $0, 192(%rsp)`
    .storeMem "%rsp" 184 (.imm 0),  -- l.3552 `movq $0, 184(%rsp)`
    .storeMem "%rsp" 176 (.imm 0),  -- l.3553 `movq $0, 176(%rsp)`
    .storeMem "%rsp" 136 (.imm 0),  -- l.3554 `movq $0, 136(%rsp)`
    .storeMem "%rsp" 144 (.imm 0),  -- l.3555 `movq $0, 144(%rsp)`
    .storeMem "%rsp" 152 (.imm 0),  -- l.3556 `movq $0, 152(%rsp)`
    .storeMem "%rsp" 160 (.imm 0),  -- l.3557 `movq $0, 160(%rsp)`
    .storeMem "%rsp" 168 (.imm 0),  -- l.3558 `movq $0, 168(%rsp)`
    .storeMem "%rsp" 72 (.imm 0),  -- l.3559 `movq $0, 72(%rsp)`
    .storeMem "%rsp" 80 (.imm 0),  -- l.3560 `movq $0, 80(%rsp)`
    .storeMem "%rsp" 120 (.imm 0),  -- l.3561 `movq $0, 120(%rsp)`
    .storeMem "%rsp" 128 (.imm 0),  -- l.3562 `movq $0, 128(%rsp)`
    .storeMem "%rsp" 0 (.imm 0),  -- l.3563 `movq $0, 0(%rsp)`
    .storeMem "%rsp" 48 (.imm 0),  -- l.3564 `movq $0, 48(%rsp)`
    .storeMem "%rsp" 56 (.imm 0) ]  -- l.3565 `movq $0, 56(%rsp)`

/-- Segment 113 of the body: the 10 instructions from source lines 3566–3575. -/
def ed25519ScReduceShippedSeg113 : List (JInstr 64) :=
  [ .storeMem "%rsp" 64 (.imm 0),  -- l.3566 `movq $0, 64(%rsp)`
    .storeMem "%rsp" 8 (.imm 0),  -- l.3567 `movq $0, 8(%rsp)`
    .storeMem "%rsp" 16 (.imm 0),  -- l.3568 `movq $0, 16(%rsp)`
    .storeMem "%rsp" 24 (.imm 0),  -- l.3569 `movq $0, 24(%rsp)`
    .storeMem "%rsp" 32 (.imm 0),  -- l.3570 `movq $0, 32(%rsp)`
    .storeMem "%rsp" 40 (.imm 0),  -- l.3571 `movq $0, 40(%rsp)`
    .storeMem "%rsp" 112 (.imm 0),  -- l.3572 `movq $0, 112(%rsp)`
    .storeMem "%rsp" 104 (.imm 0),  -- l.3573 `movq $0, 104(%rsp)`
    .storeMem "%rsp" 96 (.imm 0),  -- l.3574 `movq $0, 96(%rsp)`
    .storeMem "%rsp" 88 (.imm 0) ]  -- l.3575 `movq $0, 88(%rsp)`

/-- Part 1 of the body: segments 1–16. -/
def ed25519ScReduceShippedPart01 : List (JInstr 64) :=
  ed25519ScReduceShippedSeg001 ++ ed25519ScReduceShippedSeg002 ++
  ed25519ScReduceShippedSeg003 ++ ed25519ScReduceShippedSeg004 ++
  ed25519ScReduceShippedSeg005 ++ ed25519ScReduceShippedSeg006 ++
  ed25519ScReduceShippedSeg007 ++ ed25519ScReduceShippedSeg008 ++
  ed25519ScReduceShippedSeg009 ++ ed25519ScReduceShippedSeg010 ++
  ed25519ScReduceShippedSeg011 ++ ed25519ScReduceShippedSeg012 ++
  ed25519ScReduceShippedSeg013 ++ ed25519ScReduceShippedSeg014 ++
  ed25519ScReduceShippedSeg015 ++ ed25519ScReduceShippedSeg016

/-- Part 1 has 488 instructions. -/
theorem ed25519ScReduceShippedPart01_length :
    ed25519ScReduceShippedPart01.length = 488 := by
  unfold ed25519ScReduceShippedPart01
  simp only [List.length_append]
  rfl

/-- Part 2 of the body: segments 17–32. -/
def ed25519ScReduceShippedPart02 : List (JInstr 64) :=
  ed25519ScReduceShippedSeg017 ++ ed25519ScReduceShippedSeg018 ++
  ed25519ScReduceShippedSeg019 ++ ed25519ScReduceShippedSeg020 ++
  ed25519ScReduceShippedSeg021 ++ ed25519ScReduceShippedSeg022 ++
  ed25519ScReduceShippedSeg023 ++ ed25519ScReduceShippedSeg024 ++
  ed25519ScReduceShippedSeg025 ++ ed25519ScReduceShippedSeg026 ++
  ed25519ScReduceShippedSeg027 ++ ed25519ScReduceShippedSeg028 ++
  ed25519ScReduceShippedSeg029 ++ ed25519ScReduceShippedSeg030 ++
  ed25519ScReduceShippedSeg031 ++ ed25519ScReduceShippedSeg032

/-- Part 2 has 512 instructions. -/
theorem ed25519ScReduceShippedPart02_length :
    ed25519ScReduceShippedPart02.length = 512 := by
  unfold ed25519ScReduceShippedPart02
  simp only [List.length_append]
  rfl

/-- Part 3 of the body: segments 33–48. -/
def ed25519ScReduceShippedPart03 : List (JInstr 64) :=
  ed25519ScReduceShippedSeg033 ++ ed25519ScReduceShippedSeg034 ++
  ed25519ScReduceShippedSeg035 ++ ed25519ScReduceShippedSeg036 ++
  ed25519ScReduceShippedSeg037 ++ ed25519ScReduceShippedSeg038 ++
  ed25519ScReduceShippedSeg039 ++ ed25519ScReduceShippedSeg040 ++
  ed25519ScReduceShippedSeg041 ++ ed25519ScReduceShippedSeg042 ++
  ed25519ScReduceShippedSeg043 ++ ed25519ScReduceShippedSeg044 ++
  ed25519ScReduceShippedSeg045 ++ ed25519ScReduceShippedSeg046 ++
  ed25519ScReduceShippedSeg047 ++ ed25519ScReduceShippedSeg048

/-- Part 3 has 512 instructions. -/
theorem ed25519ScReduceShippedPart03_length :
    ed25519ScReduceShippedPart03.length = 512 := by
  unfold ed25519ScReduceShippedPart03
  simp only [List.length_append]
  rfl

/-- Part 4 of the body: segments 49–64. -/
def ed25519ScReduceShippedPart04 : List (JInstr 64) :=
  ed25519ScReduceShippedSeg049 ++ ed25519ScReduceShippedSeg050 ++
  ed25519ScReduceShippedSeg051 ++ ed25519ScReduceShippedSeg052 ++
  ed25519ScReduceShippedSeg053 ++ ed25519ScReduceShippedSeg054 ++
  ed25519ScReduceShippedSeg055 ++ ed25519ScReduceShippedSeg056 ++
  ed25519ScReduceShippedSeg057 ++ ed25519ScReduceShippedSeg058 ++
  ed25519ScReduceShippedSeg059 ++ ed25519ScReduceShippedSeg060 ++
  ed25519ScReduceShippedSeg061 ++ ed25519ScReduceShippedSeg062 ++
  ed25519ScReduceShippedSeg063 ++ ed25519ScReduceShippedSeg064

/-- Part 4 has 512 instructions. -/
theorem ed25519ScReduceShippedPart04_length :
    ed25519ScReduceShippedPart04.length = 512 := by
  unfold ed25519ScReduceShippedPart04
  simp only [List.length_append]
  rfl

/-- Part 5 of the body: segments 65–80. -/
def ed25519ScReduceShippedPart05 : List (JInstr 64) :=
  ed25519ScReduceShippedSeg065 ++ ed25519ScReduceShippedSeg066 ++
  ed25519ScReduceShippedSeg067 ++ ed25519ScReduceShippedSeg068 ++
  ed25519ScReduceShippedSeg069 ++ ed25519ScReduceShippedSeg070 ++
  ed25519ScReduceShippedSeg071 ++ ed25519ScReduceShippedSeg072 ++
  ed25519ScReduceShippedSeg073 ++ ed25519ScReduceShippedSeg074 ++
  ed25519ScReduceShippedSeg075 ++ ed25519ScReduceShippedSeg076 ++
  ed25519ScReduceShippedSeg077 ++ ed25519ScReduceShippedSeg078 ++
  ed25519ScReduceShippedSeg079 ++ ed25519ScReduceShippedSeg080

/-- Part 5 has 512 instructions. -/
theorem ed25519ScReduceShippedPart05_length :
    ed25519ScReduceShippedPart05.length = 512 := by
  unfold ed25519ScReduceShippedPart05
  simp only [List.length_append]
  rfl

/-- Part 6 of the body: segments 81–96. -/
def ed25519ScReduceShippedPart06 : List (JInstr 64) :=
  ed25519ScReduceShippedSeg081 ++ ed25519ScReduceShippedSeg082 ++
  ed25519ScReduceShippedSeg083 ++ ed25519ScReduceShippedSeg084 ++
  ed25519ScReduceShippedSeg085 ++ ed25519ScReduceShippedSeg086 ++
  ed25519ScReduceShippedSeg087 ++ ed25519ScReduceShippedSeg088 ++
  ed25519ScReduceShippedSeg089 ++ ed25519ScReduceShippedSeg090 ++
  ed25519ScReduceShippedSeg091 ++ ed25519ScReduceShippedSeg092 ++
  ed25519ScReduceShippedSeg093 ++ ed25519ScReduceShippedSeg094 ++
  ed25519ScReduceShippedSeg095 ++ ed25519ScReduceShippedSeg096

/-- Part 6 has 512 instructions. -/
theorem ed25519ScReduceShippedPart06_length :
    ed25519ScReduceShippedPart06.length = 512 := by
  unfold ed25519ScReduceShippedPart06
  simp only [List.length_append]
  rfl

/-- Part 7 of the body: segments 97–112. -/
def ed25519ScReduceShippedPart07 : List (JInstr 64) :=
  ed25519ScReduceShippedSeg097 ++ ed25519ScReduceShippedSeg098 ++
  ed25519ScReduceShippedSeg099 ++ ed25519ScReduceShippedSeg100 ++
  ed25519ScReduceShippedSeg101 ++ ed25519ScReduceShippedSeg102 ++
  ed25519ScReduceShippedSeg103 ++ ed25519ScReduceShippedSeg104 ++
  ed25519ScReduceShippedSeg105 ++ ed25519ScReduceShippedSeg106 ++
  ed25519ScReduceShippedSeg107 ++ ed25519ScReduceShippedSeg108 ++
  ed25519ScReduceShippedSeg109 ++ ed25519ScReduceShippedSeg110 ++
  ed25519ScReduceShippedSeg111 ++ ed25519ScReduceShippedSeg112

/-- Part 7 has 512 instructions. -/
theorem ed25519ScReduceShippedPart07_length :
    ed25519ScReduceShippedPart07.length = 512 := by
  unfold ed25519ScReduceShippedPart07
  simp only [List.length_append]
  rfl

/-- Part 8 of the body: segments 113–113. -/
def ed25519ScReduceShippedPart08 : List (JInstr 64) :=
  ed25519ScReduceShippedSeg113

/-- Part 8 has 10 instructions. -/
theorem ed25519ScReduceShippedPart08_length :
    ed25519ScReduceShippedPart08.length = 10 := by
  unfold ed25519ScReduceShippedPart08
  rfl

/-- The body of `ed25519_sc_reduce_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 113 segments,
    grouped in 8 parts. -/
def ed25519ScReduceShippedBlock : List (JInstr 64) :=
  ed25519ScReduceShippedPart01 ++ ed25519ScReduceShippedPart02 ++
  ed25519ScReduceShippedPart03 ++ ed25519ScReduceShippedPart04 ++
  ed25519ScReduceShippedPart05 ++ ed25519ScReduceShippedPart06 ++
  ed25519ScReduceShippedPart07 ++ ed25519ScReduceShippedPart08

/-- The frame instructions of `ed25519_sc_reduce_x86_from_lean` before the body,
    which the block omits: each `pushq r` as `leaq -8(%rsp), %rsp` followed by the
    store of `r` at `0(%rsp)`, and the stack allocation as the instruction the text
    contains. -/
def ed25519ScReduceShippedPrologue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-240) ]  -- l.5 `leaq -240(%rsp), %rsp`

/-- The frame instructions of `ed25519_sc_reduce_x86_from_lean` after the body,
    which the block omits, `ret` excluded: the stack release as the instruction the
    text contains, and each `popq r` as the load of `r` from `0(%rsp)` followed by
    `leaq 8(%rsp), %rsp`. -/
def ed25519ScReduceShippedEpilogue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 240 ]  -- l.3576 `leaq 240(%rsp), %rsp`

/-- The block has 3570 instructions; the count of each part is a lemma above. -/
theorem ed25519ScReduceShippedBlock_length :
    ed25519ScReduceShippedBlock.length = 3570 := by
  unfold ed25519ScReduceShippedBlock
  simp only [List.length_append, ed25519ScReduceShippedPart01_length,
    ed25519ScReduceShippedPart02_length, ed25519ScReduceShippedPart03_length,
    ed25519ScReduceShippedPart04_length, ed25519ScReduceShippedPart05_length,
    ed25519ScReduceShippedPart06_length, ed25519ScReduceShippedPart07_length,
    ed25519ScReduceShippedPart08_length]

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped
