/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# `ed25519_sc_muladd_x86_from_lean` from the owned backend's output as a `JInstr 64` block

`ed25519ScMuladdShippedBlock` is the body of the function
`ed25519_sc_muladd_x86_from_lean` in an x86-64 AT&T file printed by CatCrypt's
owned backend, translated instruction by instruction. The file's producer is
recorded in `PROVENANCE.md` next to it, where one exists.

## Provenance

* Source: `crates/catcrypt-ed25519/asm/ed25519_sc_muladd_x86_from_lean.s` in the
  `SSProve-lean` repository at commit `5a765fbc8aff83bff9eab87c81af0df5d9ae9944`
  (tracked and unchanged at that commit), file SHA-256
  `dae1d49335af3ce0609fa0a11d89659faabffb7420ceef370fafc5fd3e5607f6`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 3 frame instructions,
  each checked by the importer: the stack allocation `leaq -240(%rsp), %rsp` and
  its release `leaq 240(%rsp), %rsp`; `ret`.
* Every other instruction is kept, `%rsp`-relative moves included, as `storeMem
  "%rsp" off` and `loadMem r "%rsp" off`. Their offsets are relative to `%rsp`
  after the omitted allocation, and `%rsp` is constant in the body.
* The first 8 instructions store registers into `%rsp` slots and form segment 1.
  The last 6 instructions load callee-saved registers back from the slots segment 1
  stored them to, and form the last segment.
* Registers keep their physical names (`"%rax"`, …, `"%r15"`, `"%rsp"`); no
  register allocation is involved.
* `JasminModel` keys memory by the name of the base register and a byte offset, at
  word granularity. A proof over this block is a statement about that model; it
  agrees with the processor where each base register holds one address throughout
  the block and distinct names address disjoint words.
* The block writes `%r14` between memory accesses through it, so the accesses
  through that register before and after the write share one memory bank in the
  model.

The block has 4354 instructions. Source instructions by mnemonic: `movq` 2825,
`xorq` 536, `andq` 344, `addq` 328, `shrq` 168, `imulq` 76, `mulx` 76, `subq` 1.

## Main definitions

* `ed25519ScMuladdShippedSeg001` … `ed25519ScMuladdShippedSeg138`: the block in
  138 segments, each a literal `List (JInstr 64)`. A segment ends after a call,
  after the entry run of `%rsp` stores, before the exit run of `%rsp` loads, and
  after 32 instructions.
* `ed25519ScMuladdShippedPart01` … `ed25519ScMuladdShippedPart09`: the segments
  in 9 parts of at most 16 consecutive segments, each with lemmas giving its
  instruction count.
* `ed25519ScMuladdShippedBlock`: the block, the concatenation of the parts.

## Main results

* `ed25519ScMuladdShippedBlock_length`: the block has 4354 instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScMuladdShipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 8 instructions from source lines 6–13. -/
def ed25519ScMuladdShippedSeg001 : List (JInstr 64) :=
  [ .storeMem "%rsp" 232 (.reg "%rdi"),  -- l.6 `movq %rdi, 232(%rsp)`
    .storeMem "%rsp" 224 (.reg "%rsi"),  -- l.7 `movq %rsi, 224(%rsp)`
    .storeMem "%rsp" 216 (.reg "%rbx"),  -- l.8 `movq %rbx, 216(%rsp)`
    .storeMem "%rsp" 208 (.reg "%rbp"),  -- l.9 `movq %rbp, 208(%rsp)`
    .storeMem "%rsp" 200 (.reg "%r12"),  -- l.10 `movq %r12, 200(%rsp)`
    .storeMem "%rsp" 192 (.reg "%r13"),  -- l.11 `movq %r13, 192(%rsp)`
    .storeMem "%rsp" 184 (.reg "%r14"),  -- l.12 `movq %r14, 184(%rsp)`
    .storeMem "%rsp" 176 (.reg "%r15") ]  -- l.13 `movq %r15, 176(%rsp)`

/-- Segment 2 of the body: the 32 instructions from source lines 14–45. -/
def ed25519ScMuladdShippedSeg002 : List (JInstr 64) :=
  [ .mov "%r14" (.reg "%rsi"),  -- l.14 `movq %rsi, %r14`
    .storeMem "%rsp" (-8) (.reg "%rdx"),  -- l.15 `movq %rdx, -8(%rsp)`
    .storeMem "%rsp" (-16) (.reg "%rcx"),  -- l.16 `movq %rcx, -16(%rsp)`
    .loadMem "%r15" "%rsp" 232,  -- l.17 `movq 232(%rsp), %r15`
    .storeMem "%rsp" 136 (.reg "%r15"),  -- l.18 `movq %r15, 136(%rsp)`
    .loadMem "%rcx" "%rsp" 224,  -- l.19 `movq 224(%rsp), %rcx`
    .loadMem "%rsi" "%rsp" (-8),  -- l.20 `movq -8(%rsp), %rsi`
    .loadMem "%rdi" "%rsp" (-16),  -- l.21 `movq -16(%rsp), %rdi`
    .mov "%rax" (.imm 0),  -- l.22 `movq $0, %rax`
    .mov "%r15" (.reg "%rax"),  -- l.23 `movq %rax, %r15`
    .storeMem "%rsp" 144 (.reg "%r15"),  -- l.24 `movq %r15, 144(%rsp)`
    .mov "%rax" (.imm 1),  -- l.25 `movq $1, %rax`
    .mov "%r15" (.reg "%rax"),  -- l.26 `movq %rax, %r15`
    .storeMem "%rsp" 152 (.reg "%r15"),  -- l.27 `movq %r15, 152(%rsp)`
    .mov "%rax" (.imm 2),  -- l.28 `movq $2, %rax`
    .mov "%r15" (.reg "%rax"),  -- l.29 `movq %rax, %r15`
    .storeMem "%rsp" 160 (.reg "%r15"),  -- l.30 `movq %r15, 160(%rsp)`
    .mov "%rax" (.imm 3),  -- l.31 `movq $3, %rax`
    .mov "%r15" (.reg "%rax"),  -- l.32 `movq %rax, %r15`
    .storeMem "%rsp" 168 (.reg "%r15"),  -- l.33 `movq %r15, 168(%rsp)`
    .loadMem "%r14" "%rsp" 224,  -- l.34 `movq 224(%rsp), %r14`
    .loadMem "%r15" "%rsp" 144,  -- l.35 `movq 144(%rsp), %r15`
    .loadMemIdx "%rax" "%r14" "%r15" 8,  -- l.36 `movq (%r14, %r15, 8), %rax`
    .loadMem "%r14" "%rsp" 224,  -- l.37 `movq 224(%rsp), %r14`
    .loadMem "%r15" "%rsp" 152,  -- l.38 `movq 152(%rsp), %r15`
    .loadMemIdx "%r11" "%r14" "%r15" 8,  -- l.39 `movq (%r14, %r15, 8), %r11`
    .loadMem "%r14" "%rsp" 224,  -- l.40 `movq 224(%rsp), %r14`
    .loadMem "%r15" "%rsp" 160,  -- l.41 `movq 160(%rsp), %r15`
    .loadMemIdx "%r15" "%r14" "%r15" 8,  -- l.42 `movq (%r14, %r15, 8), %r15`
    .storeMem "%rsp" 80 (.reg "%r15"),  -- l.43 `movq %r15, 80(%rsp)`
    .loadMem "%r14" "%rsp" 224,  -- l.44 `movq 224(%rsp), %r14`
    .loadMem "%r15" "%rsp" 168 ]  -- l.45 `movq 168(%rsp), %r15`

/-- Segment 3 of the body: the 32 instructions from source lines 46–77. -/
def ed25519ScMuladdShippedSeg003 : List (JInstr 64) :=
  [ .loadMemIdx "%r15" "%r14" "%r15" 8,  -- l.46 `movq (%r14, %r15, 8), %r15`
    .storeMem "%rsp" 120 (.reg "%r15"),  -- l.47 `movq %r15, 120(%rsp)`
    .loadMem "%r14" "%rsp" (-8),  -- l.48 `movq -8(%rsp), %r14`
    .loadMem "%r15" "%rsp" 144,  -- l.49 `movq 144(%rsp), %r15`
    .loadMemIdx "%r15" "%r14" "%r15" 8,  -- l.50 `movq (%r14, %r15, 8), %r15`
    .storeMem "%rsp" 88 (.reg "%r15"),  -- l.51 `movq %r15, 88(%rsp)`
    .loadMem "%r14" "%rsp" (-8),  -- l.52 `movq -8(%rsp), %r14`
    .loadMem "%r15" "%rsp" 152,  -- l.53 `movq 152(%rsp), %r15`
    .loadMemIdx "%r15" "%r14" "%r15" 8,  -- l.54 `movq (%r14, %r15, 8), %r15`
    .storeMem "%rsp" 104 (.reg "%r15"),  -- l.55 `movq %r15, 104(%rsp)`
    .loadMem "%r14" "%rsp" (-8),  -- l.56 `movq -8(%rsp), %r14`
    .loadMem "%r15" "%rsp" 160,  -- l.57 `movq 160(%rsp), %r15`
    .loadMemIdx "%r15" "%r14" "%r15" 8,  -- l.58 `movq (%r14, %r15, 8), %r15`
    .storeMem "%rsp" 112 (.reg "%r15"),  -- l.59 `movq %r15, 112(%rsp)`
    .loadMem "%r14" "%rsp" (-8),  -- l.60 `movq -8(%rsp), %r14`
    .loadMem "%r15" "%rsp" 168,  -- l.61 `movq 168(%rsp), %r15`
    .loadMemIdx "%r15" "%r14" "%r15" 8,  -- l.62 `movq (%r14, %r15, 8), %r15`
    .storeMem "%rsp" 128 (.reg "%r15"),  -- l.63 `movq %r15, 128(%rsp)`
    .loadMem "%r14" "%rsp" (-16),  -- l.64 `movq -16(%rsp), %r14`
    .loadMem "%r15" "%rsp" 144,  -- l.65 `movq 144(%rsp), %r15`
    .loadMemIdx "%rsi" "%r14" "%r15" 8,  -- l.66 `movq (%r14, %r15, 8), %rsi`
    .loadMem "%r14" "%rsp" (-16),  -- l.67 `movq -16(%rsp), %r14`
    .loadMem "%r15" "%rsp" 152,  -- l.68 `movq 152(%rsp), %r15`
    .loadMemIdx "%rbp" "%r14" "%r15" 8,  -- l.69 `movq (%r14, %r15, 8), %rbp`
    .loadMem "%r14" "%rsp" (-16),  -- l.70 `movq -16(%rsp), %r14`
    .loadMem "%r15" "%rsp" 160,  -- l.71 `movq 160(%rsp), %r15`
    .loadMemIdx "%rbx" "%r14" "%r15" 8,  -- l.72 `movq (%r14, %r15, 8), %rbx`
    .loadMem "%r14" "%rsp" (-16),  -- l.73 `movq -16(%rsp), %r14`
    .loadMem "%r15" "%rsp" 168,  -- l.74 `movq 168(%rsp), %r15`
    .loadMemIdx "%r8" "%r14" "%r15" 8,  -- l.75 `movq (%r14, %r15, 8), %r8`
    .mov "%rdi" (.reg "%rax"),  -- l.76 `movq %rax, %rdi`
    .loadMem "%r15" "%rsp" 88 ]  -- l.77 `movq 88(%rsp), %r15`

/-- Segment 4 of the body: the 32 instructions from source lines 78–109. -/
def ed25519ScMuladdShippedSeg004 : List (JInstr 64) :=
  [ .imul "%rdi" (.reg "%r15"),  -- l.78 `imulq %r15, %rdi`
    .mov "%r13" (.reg "%rdi"),  -- l.79 `movq %rdi, %r13`
    .mov "%rdx" (.reg "%rax"),  -- l.80 `movq %rax, %rdx`
    .loadMem "%r14" "%rsp" 88,  -- l.81 `movq 88(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.82 `movq %rcx, -128(%rsp)`
    .mulx "%rdi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.83 `mulx %r14, %rcx, %rdi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.84 `movq -128(%rsp), %rcx`
    .mov "%r9" (.reg "%rdi"),  -- l.85 `movq %rdi, %r9`
    .mov "%rdi" (.imm 0),  -- l.86 `movq $0, %rdi`
    .mov "%r10" (.reg "%r13"),  -- l.87 `movq %r13, %r10`
    .add "%r10" (.reg "%rdi"),  -- l.88 `addq %rdi, %r10`
    .mov "%rdi" (.reg "%r10"),  -- l.89 `movq %r10, %rdi`
    .mov "%r10" (.reg "%rdi"),  -- l.90 `movq %rdi, %r10`
    .add "%r10" (.reg "%rsi"),  -- l.91 `addq %rsi, %r10`
    .mov "%r15" (.reg "%r10"),  -- l.92 `movq %r10, %r15`
    .storeMem "%rsp" 96 (.reg "%r15"),  -- l.93 `movq %r15, 96(%rsp)`
    .mov "%r10" (.imm 0),  -- l.94 `movq $0, %r10`
    .mov "%rcx" (.reg "%r13"),  -- l.95 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%r10"),  -- l.96 `andq %r10, %rcx`
    .mov "%r10" (.imm 0),  -- l.97 `movq $0, %r10`
    .mov "%r12" (.reg "%r13"),  -- l.98 `movq %r13, %r12`
    .xor_ "%r12" (.reg "%r10"),  -- l.99 `xorq %r10, %r12`
    .mov "%r10" (.imm 18446744073709551615),  -- l.100 `movq $18446744073709551615, %r10`
    .mov "%r13" (.reg "%rdi"),  -- l.101 `movq %rdi, %r13`
    .xor_ "%r13" (.reg "%r10"),  -- l.102 `xorq %r10, %r13`
    .mov "%r10" (.reg "%r12"),  -- l.103 `movq %r12, %r10`
    .and_ "%r10" (.reg "%r13"),  -- l.104 `andq %r13, %r10`
    .mov "%r12" (.reg "%rcx"),  -- l.105 `movq %rcx, %r12`
    .xor_ "%r12" (.reg "%r10"),  -- l.106 `xorq %r10, %r12`
    .mov "%rcx" (.imm 63),  -- l.107 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r12"),  -- l.108 `movq %r12, %rcx`
    .shr "%rcx" (.imm 63) ]  -- l.109 `shrq $63, %rcx`

/-- Segment 5 of the body: the 32 instructions from source lines 110–141. -/
def ed25519ScMuladdShippedSeg005 : List (JInstr 64) :=
  [ .mov "%r10" (.reg "%r9"),  -- l.110 `movq %r9, %r10`
    .add "%r10" (.reg "%rcx"),  -- l.111 `addq %rcx, %r10`
    .mov "%rcx" (.reg "%rdi"),  -- l.112 `movq %rdi, %rcx`
    .and_ "%rcx" (.reg "%rsi"),  -- l.113 `andq %rsi, %rcx`
    .mov "%r9" (.reg "%rdi"),  -- l.114 `movq %rdi, %r9`
    .xor_ "%r9" (.reg "%rsi"),  -- l.115 `xorq %rsi, %r9`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.116 `movq $18446744073709551615, %rsi`
    .loadMem "%rdi" "%rsp" 96,  -- l.117 `movq 96(%rsp), %rdi`
    .xor_ "%rdi" (.reg "%rsi"),  -- l.118 `xorq %rsi, %rdi`
    .mov "%rsi" (.reg "%r9"),  -- l.119 `movq %r9, %rsi`
    .and_ "%rsi" (.reg "%rdi"),  -- l.120 `andq %rdi, %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.121 `movq %rcx, %rdi`
    .xor_ "%rdi" (.reg "%rsi"),  -- l.122 `xorq %rsi, %rdi`
    .mov "%rcx" (.imm 63),  -- l.123 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.124 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.125 `shrq $63, %rcx`
    .mov "%rsi" (.reg "%r10"),  -- l.126 `movq %r10, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.127 `addq %rcx, %rsi`
    .mov "%rcx" (.reg "%rsi"),  -- l.128 `movq %rsi, %rcx`
    .mov "%rsi" (.reg "%rax"),  -- l.129 `movq %rax, %rsi`
    .loadMem "%r15" "%rsp" 104,  -- l.130 `movq 104(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.131 `imulq %r15, %rsi`
    .mov "%rdi" (.reg "%rsi"),  -- l.132 `movq %rsi, %rdi`
    .mov "%rdx" (.reg "%rax"),  -- l.133 `movq %rax, %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.134 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.135 `movq %rcx, -128(%rsp)`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.136 `mulx %r14, %rcx, %rsi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.137 `movq -128(%rsp), %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.138 `movq %rsi, %r9`
    .mov "%rsi" (.reg "%rdi"),  -- l.139 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.140 `addq %rcx, %rsi`
    .mov "%r10" (.reg "%rsi") ]  -- l.141 `movq %rsi, %r10`

/-- Segment 6 of the body: the 32 instructions from source lines 142–173. -/
def ed25519ScMuladdShippedSeg006 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%r10"),  -- l.142 `movq %r10, %rsi`
    .add "%rsi" (.reg "%rbp"),  -- l.143 `addq %rbp, %rsi`
    .mov "%r12" (.reg "%rsi"),  -- l.144 `movq %rsi, %r12`
    .mov "%rsi" (.reg "%rdi"),  -- l.145 `movq %rdi, %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.146 `andq %rcx, %rsi`
    .mov "%r13" (.reg "%rdi"),  -- l.147 `movq %rdi, %r13`
    .xor_ "%r13" (.reg "%rcx"),  -- l.148 `xorq %rcx, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.149 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%r10"),  -- l.150 `movq %r10, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.151 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.152 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.153 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.154 `movq %rsi, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.155 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.156 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.157 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.158 `shrq $63, %rcx`
    .mov "%rsi" (.reg "%r9"),  -- l.159 `movq %r9, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.160 `addq %rcx, %rsi`
    .mov "%rcx" (.reg "%r10"),  -- l.161 `movq %r10, %rcx`
    .and_ "%rcx" (.reg "%rbp"),  -- l.162 `andq %rbp, %rcx`
    .mov "%rdi" (.reg "%r10"),  -- l.163 `movq %r10, %rdi`
    .xor_ "%rdi" (.reg "%rbp"),  -- l.164 `xorq %rbp, %rdi`
    .mov "%rbp" (.imm 18446744073709551615),  -- l.165 `movq $18446744073709551615, %rbp`
    .mov "%r9" (.reg "%r12"),  -- l.166 `movq %r12, %r9`
    .xor_ "%r9" (.reg "%rbp"),  -- l.167 `xorq %rbp, %r9`
    .mov "%rbp" (.reg "%rdi"),  -- l.168 `movq %rdi, %rbp`
    .and_ "%rbp" (.reg "%r9"),  -- l.169 `andq %r9, %rbp`
    .mov "%rdi" (.reg "%rcx"),  -- l.170 `movq %rcx, %rdi`
    .xor_ "%rdi" (.reg "%rbp"),  -- l.171 `xorq %rbp, %rdi`
    .mov "%rcx" (.imm 63),  -- l.172 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi") ]  -- l.173 `movq %rdi, %rcx`

/-- Segment 7 of the body: the 32 instructions from source lines 174–205. -/
def ed25519ScMuladdShippedSeg007 : List (JInstr 64) :=
  [ .shr "%rcx" (.imm 63),  -- l.174 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.175 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.176 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rdi"),  -- l.177 `movq %rdi, %rcx`
    .mov "%rsi" (.reg "%rax"),  -- l.178 `movq %rax, %rsi`
    .loadMem "%r15" "%rsp" 112,  -- l.179 `movq 112(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.180 `imulq %r15, %rsi`
    .mov "%rdi" (.reg "%rsi"),  -- l.181 `movq %rsi, %rdi`
    .mov "%rdx" (.reg "%rax"),  -- l.182 `movq %rax, %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.183 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.184 `movq %rcx, -128(%rsp)`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.185 `mulx %r14, %rcx, %rsi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.186 `movq -128(%rsp), %rcx`
    .mov "%rbp" (.reg "%rsi"),  -- l.187 `movq %rsi, %rbp`
    .mov "%rsi" (.reg "%rdi"),  -- l.188 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.189 `addq %rcx, %rsi`
    .mov "%r9" (.reg "%rsi"),  -- l.190 `movq %rsi, %r9`
    .mov "%rsi" (.reg "%r9"),  -- l.191 `movq %r9, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.192 `addq %rbx, %rsi`
    .mov "%r10" (.reg "%rsi"),  -- l.193 `movq %rsi, %r10`
    .mov "%rsi" (.reg "%rdi"),  -- l.194 `movq %rdi, %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.195 `andq %rcx, %rsi`
    .mov "%r13" (.reg "%rdi"),  -- l.196 `movq %rdi, %r13`
    .xor_ "%r13" (.reg "%rcx"),  -- l.197 `xorq %rcx, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.198 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%r9"),  -- l.199 `movq %r9, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.200 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.201 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.202 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.203 `movq %rsi, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.204 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63) ]  -- l.205 `movq $63, %rcx`

/-- Segment 8 of the body: the 32 instructions from source lines 206–237. -/
def ed25519ScMuladdShippedSeg008 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rdi"),  -- l.206 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.207 `shrq $63, %rcx`
    .mov "%rsi" (.reg "%rbp"),  -- l.208 `movq %rbp, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.209 `addq %rcx, %rsi`
    .mov "%rcx" (.reg "%r9"),  -- l.210 `movq %r9, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.211 `andq %rbx, %rcx`
    .mov "%rdi" (.reg "%r9"),  -- l.212 `movq %r9, %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.213 `xorq %rbx, %rdi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.214 `movq $18446744073709551615, %rbx`
    .mov "%rbp" (.reg "%r10"),  -- l.215 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rbx"),  -- l.216 `xorq %rbx, %rbp`
    .mov "%rbx" (.reg "%rdi"),  -- l.217 `movq %rdi, %rbx`
    .and_ "%rbx" (.reg "%rbp"),  -- l.218 `andq %rbp, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.219 `movq %rcx, %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.220 `xorq %rbx, %rdi`
    .mov "%rbx" (.imm 63),  -- l.221 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rdi"),  -- l.222 `movq %rdi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.223 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rsi"),  -- l.224 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.225 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.226 `movq %rcx, %rbx`
    .mov "%rcx" (.reg "%rax"),  -- l.227 `movq %rax, %rcx`
    .loadMem "%r15" "%rsp" 128,  -- l.228 `movq 128(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.229 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.230 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%rax"),  -- l.231 `movq %rax, %rdx`
    .loadMem "%r14" "%rsp" 128,  -- l.232 `movq 128(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.233 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.234 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.235 `movq -128(%rsp), %rsi`
    .mov "%rax" (.reg "%rcx"),  -- l.236 `movq %rcx, %rax`
    .mov "%rcx" (.reg "%rsi") ]  -- l.237 `movq %rsi, %rcx`

/-- Segment 9 of the body: the 32 instructions from source lines 238–269. -/
def ed25519ScMuladdShippedSeg009 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%rbx"),  -- l.238 `addq %rbx, %rcx`
    .mov "%rdi" (.reg "%rcx"),  -- l.239 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rdi"),  -- l.240 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.241 `addq %r8, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.242 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rsi"),  -- l.243 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.244 `andq %rbx, %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.245 `movq %rsi, %r9`
    .xor_ "%r9" (.reg "%rbx"),  -- l.246 `xorq %rbx, %r9`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.247 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rdi"),  -- l.248 `movq %rdi, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.249 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r9"),  -- l.250 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.251 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.252 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.253 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.254 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.255 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.256 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rax"),  -- l.257 `movq %rax, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.258 `addq %rbx, %rcx`
    .mov "%rax" (.reg "%rdi"),  -- l.259 `movq %rdi, %rax`
    .and_ "%rax" (.reg "%r8"),  -- l.260 `andq %r8, %rax`
    .mov "%rbx" (.reg "%rdi"),  -- l.261 `movq %rdi, %rbx`
    .xor_ "%rbx" (.reg "%r8"),  -- l.262 `xorq %r8, %rbx`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.263 `movq $18446744073709551615, %rsi`
    .mov "%rdi" (.reg "%rbp"),  -- l.264 `movq %rbp, %rdi`
    .xor_ "%rdi" (.reg "%rsi"),  -- l.265 `xorq %rsi, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.266 `movq %rbx, %rsi`
    .and_ "%rsi" (.reg "%rdi"),  -- l.267 `andq %rdi, %rsi`
    .mov "%rbx" (.reg "%rax"),  -- l.268 `movq %rax, %rbx`
    .xor_ "%rbx" (.reg "%rsi") ]  -- l.269 `xorq %rsi, %rbx`

/-- Segment 10 of the body: the 32 instructions from source lines 270–301. -/
def ed25519ScMuladdShippedSeg010 : List (JInstr 64) :=
  [ .mov "%rax" (.imm 63),  -- l.270 `movq $63, %rax`
    .mov "%rax" (.reg "%rbx"),  -- l.271 `movq %rbx, %rax`
    .shr "%rax" (.imm 63),  -- l.272 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.273 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.274 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.275 `movq %rbx, %rax`
    .mov "%rbx" (.reg "%r11"),  -- l.276 `movq %r11, %rbx`
    .loadMem "%r15" "%rsp" 88,  -- l.277 `movq 88(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.278 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.279 `movq %rbx, %rcx`
    .mov "%rdx" (.reg "%r11"),  -- l.280 `movq %r11, %rdx`
    .loadMem "%r14" "%rsp" 88,  -- l.281 `movq 88(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.282 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.283 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.284 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.285 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.286 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.287 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.288 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.289 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.290 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r12"),  -- l.291 `addq %r12, %rdi`
    .mov "%r15" (.reg "%rdi"),  -- l.292 `movq %rdi, %r15`
    .storeMem "%rsp" 64 (.reg "%r15"),  -- l.293 `movq %r15, 64(%rsp)`
    .mov "%rdi" (.imm 0),  -- l.294 `movq $0, %rdi`
    .mov "%r9" (.reg "%rcx"),  -- l.295 `movq %rcx, %r9`
    .and_ "%r9" (.reg "%rdi"),  -- l.296 `andq %rdi, %r9`
    .mov "%rdi" (.imm 0),  -- l.297 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.298 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.299 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.300 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx") ]  -- l.301 `movq %rbx, %rdi`

/-- Segment 11 of the body: the 32 instructions from source lines 302–333. -/
def ed25519ScMuladdShippedSeg011 : List (JInstr 64) :=
  [ .xor_ "%rdi" (.reg "%rcx"),  -- l.302 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.303 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.304 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r9"),  -- l.305 `movq %r9, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.306 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.307 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.308 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.309 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.310 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.311 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.312 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r12"),  -- l.313 `andq %r12, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.314 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r12"),  -- l.315 `xorq %r12, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.316 `movq $18446744073709551615, %rbx`
    .loadMem "%r9" "%rsp" 64,  -- l.317 `movq 64(%rsp), %r9`
    .xor_ "%r9" (.reg "%rbx"),  -- l.318 `xorq %rbx, %r9`
    .mov "%rbx" (.reg "%rsi"),  -- l.319 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.320 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.321 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.322 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.323 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.324 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.325 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.326 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.327 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.328 `movq %rcx, %rbx`
    .mov "%rcx" (.reg "%r11"),  -- l.329 `movq %r11, %rcx`
    .loadMem "%r15" "%rsp" 104,  -- l.330 `movq 104(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.331 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.332 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r11") ]  -- l.333 `movq %r11, %rdx`

/-- Segment 12 of the body: the 32 instructions from source lines 334–365. -/
def ed25519ScMuladdShippedSeg012 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 104,  -- l.334 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.335 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.336 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.337 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.338 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.339 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.340 `addq %rbx, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.341 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.342 `movq %r9, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.343 `addq %r10, %rcx`
    .mov "%r12" (.reg "%rcx"),  -- l.344 `movq %rcx, %r12`
    .mov "%rcx" (.reg "%rsi"),  -- l.345 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.346 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.347 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.348 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.349 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.350 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.351 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.352 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.353 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.354 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.355 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.356 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.357 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.358 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.359 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.360 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r9"),  -- l.361 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.362 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.363 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.364 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615) ]  -- l.365 `movq $18446744073709551615, %rdi`

/-- Segment 13 of the body: the 32 instructions from source lines 366–397. -/
def ed25519ScMuladdShippedSeg013 : List (JInstr 64) :=
  [ .mov "%r9" (.reg "%r12"),  -- l.366 `movq %r12, %r9`
    .xor_ "%r9" (.reg "%rdi"),  -- l.367 `xorq %rdi, %r9`
    .mov "%rdi" (.reg "%rsi"),  -- l.368 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r9"),  -- l.369 `andq %r9, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.370 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.371 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.372 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.373 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.374 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.375 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.376 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.377 `movq %rsi, %rbx`
    .mov "%rcx" (.reg "%r11"),  -- l.378 `movq %r11, %rcx`
    .loadMem "%r15" "%rsp" 112,  -- l.379 `movq 112(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.380 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.381 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r11"),  -- l.382 `movq %r11, %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.383 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.384 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.385 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.386 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.387 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.388 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.389 `addq %rbx, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.390 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.391 `movq %r9, %rcx`
    .add "%rcx" (.reg "%rbp"),  -- l.392 `addq %rbp, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.393 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.394 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.395 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.396 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx") ]  -- l.397 `xorq %rbx, %r13`

/-- Segment 14 of the body: the 32 instructions from source lines 398–429. -/
def ed25519ScMuladdShippedSeg014 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 18446744073709551615),  -- l.398 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.399 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.400 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.401 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.402 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.403 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.404 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.405 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.406 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.407 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.408 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.409 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r9"),  -- l.410 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%rbp"),  -- l.411 `andq %rbp, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.412 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rbp"),  -- l.413 `xorq %rbp, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.414 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.415 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.416 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.417 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.418 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.419 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.420 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.421 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.422 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.423 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.424 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.425 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.426 `movq %rsi, %rbx`
    .mov "%rcx" (.reg "%r11"),  -- l.427 `movq %r11, %rcx`
    .loadMem "%r15" "%rsp" 128,  -- l.428 `movq 128(%rsp), %r15`
    .imul "%rcx" (.reg "%r15") ]  -- l.429 `imulq %r15, %rcx`

/-- Segment 15 of the body: the 32 instructions from source lines 430–461. -/
def ed25519ScMuladdShippedSeg015 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rcx"),  -- l.430 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r11"),  -- l.431 `movq %r11, %rdx`
    .loadMem "%r14" "%rsp" 128,  -- l.432 `movq 128(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.433 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.434 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.435 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.436 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.437 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.438 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.439 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.440 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.441 `addq %rax, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.442 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.443 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.444 `andq %rbx, %rcx`
    .mov "%r11" (.reg "%rsi"),  -- l.445 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.446 `xorq %rbx, %r11`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.447 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.448 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.449 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r11"),  -- l.450 `movq %r11, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.451 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.452 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.453 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.454 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.455 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.456 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.457 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.458 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.459 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.460 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp") ]  -- l.461 `movq %rbp, %rsi`

/-- Segment 16 of the body: the 32 instructions from source lines 462–493. -/
def ed25519ScMuladdShippedSeg016 : List (JInstr 64) :=
  [ .xor_ "%rsi" (.reg "%rax"),  -- l.462 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.463 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r9"),  -- l.464 `movq %r9, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.465 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.466 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.467 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.468 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.469 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.470 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.471 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.472 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.473 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.474 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.475 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 80,  -- l.476 `movq 80(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 88,  -- l.477 `movq 88(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.478 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.479 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 80,  -- l.480 `movq 80(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 88,  -- l.481 `movq 88(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.482 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.483 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.484 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.485 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.486 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.487 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.488 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.489 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.490 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r12"),  -- l.491 `addq %r12, %rdi`
    .mov "%r15" (.reg "%rdi"),  -- l.492 `movq %rdi, %r15`
    .storeMem "%rsp" 72 (.reg "%r15") ]  -- l.493 `movq %r15, 72(%rsp)`

/-- Segment 17 of the body: the 32 instructions from source lines 494–525. -/
def ed25519ScMuladdShippedSeg017 : List (JInstr 64) :=
  [ .mov "%rdi" (.imm 0),  -- l.494 `movq $0, %rdi`
    .mov "%r11" (.reg "%rcx"),  -- l.495 `movq %rcx, %r11`
    .and_ "%r11" (.reg "%rdi"),  -- l.496 `andq %rdi, %r11`
    .mov "%rdi" (.imm 0),  -- l.497 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.498 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.499 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.500 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.501 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.502 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.503 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.504 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r11"),  -- l.505 `movq %r11, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.506 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.507 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.508 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.509 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.510 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.511 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.512 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r12"),  -- l.513 `andq %r12, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.514 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r12"),  -- l.515 `xorq %r12, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.516 `movq $18446744073709551615, %rbx`
    .loadMem "%r11" "%rsp" 72,  -- l.517 `movq 72(%rsp), %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.518 `xorq %rbx, %r11`
    .mov "%rbx" (.reg "%rsi"),  -- l.519 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.520 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.521 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.522 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.523 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.524 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63) ]  -- l.525 `shrq $63, %rbx`

/-- Segment 18 of the body: the 32 instructions from source lines 526–557. -/
def ed25519ScMuladdShippedSeg018 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rdi"),  -- l.526 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.527 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.528 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 80,  -- l.529 `movq 80(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 104,  -- l.530 `movq 104(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.531 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.532 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 80,  -- l.533 `movq 80(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.534 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.535 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.536 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.537 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.538 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.539 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.540 `addq %rbx, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.541 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%r11"),  -- l.542 `movq %r11, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.543 `addq %r10, %rcx`
    .mov "%r12" (.reg "%rcx"),  -- l.544 `movq %rcx, %r12`
    .mov "%rcx" (.reg "%rsi"),  -- l.545 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.546 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.547 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.548 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.549 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r11"),  -- l.550 `movq %r11, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.551 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.552 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.553 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.554 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.555 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.556 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi") ]  -- l.557 `movq %rsi, %rbx`

/-- Segment 19 of the body: the 32 instructions from source lines 558–589. -/
def ed25519ScMuladdShippedSeg019 : List (JInstr 64) :=
  [ .shr "%rbx" (.imm 63),  -- l.558 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.559 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.560 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r11"),  -- l.561 `movq %r11, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.562 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%r11"),  -- l.563 `movq %r11, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.564 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.565 `movq $18446744073709551615, %rdi`
    .mov "%r10" (.reg "%r12"),  -- l.566 `movq %r12, %r10`
    .xor_ "%r10" (.reg "%rdi"),  -- l.567 `xorq %rdi, %r10`
    .mov "%rdi" (.reg "%rsi"),  -- l.568 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r10"),  -- l.569 `andq %r10, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.570 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.571 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.572 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.573 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.574 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.575 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.576 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.577 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 80,  -- l.578 `movq 80(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 112,  -- l.579 `movq 112(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.580 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.581 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 80,  -- l.582 `movq 80(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.583 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.584 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.585 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.586 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.587 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.588 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx") ]  -- l.589 `addq %rbx, %rcx`

/-- Segment 20 of the body: the 32 instructions from source lines 590–621. -/
def ed25519ScMuladdShippedSeg020 : List (JInstr 64) :=
  [ .mov "%r10" (.reg "%rcx"),  -- l.590 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%r10"),  -- l.591 `movq %r10, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.592 `addq %r9, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.593 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.594 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.595 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.596 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.597 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.598 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.599 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.600 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.601 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.602 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.603 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.604 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.605 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.606 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.607 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.608 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.609 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r10"),  -- l.610 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.611 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.612 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.613 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.614 `movq $18446744073709551615, %rdi`
    .mov "%r9" (.reg "%r11"),  -- l.615 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rdi"),  -- l.616 `xorq %rdi, %r9`
    .mov "%rdi" (.reg "%rsi"),  -- l.617 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r9"),  -- l.618 `andq %r9, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.619 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.620 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63) ]  -- l.621 `movq $63, %rbx`

/-- Segment 21 of the body: the 32 instructions from source lines 622–653. -/
def ed25519ScMuladdShippedSeg021 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%rsi"),  -- l.622 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.623 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.624 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.625 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.626 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 80,  -- l.627 `movq 80(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 128,  -- l.628 `movq 128(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.629 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.630 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 80,  -- l.631 `movq 80(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 128,  -- l.632 `movq 128(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.633 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.634 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.635 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.636 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.637 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.638 `addq %rbx, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.639 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.640 `movq %r9, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.641 `addq %rax, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.642 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.643 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.644 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.645 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.646 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.647 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.648 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.649 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.650 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.651 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.652 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx") ]  -- l.653 `xorq %rbx, %rsi`

/-- Segment 22 of the body: the 32 instructions from source lines 654–685. -/
def ed25519ScMuladdShippedSeg022 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 63),  -- l.654 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.655 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.656 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.657 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.658 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r9"),  -- l.659 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.660 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.661 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.662 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.663 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r10"),  -- l.664 `movq %r10, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.665 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.666 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.667 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.668 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.669 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.670 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.671 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.672 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.673 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.674 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.675 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 120,  -- l.676 `movq 120(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 88,  -- l.677 `movq 88(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.678 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.679 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 120,  -- l.680 `movq 120(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 88,  -- l.681 `movq 88(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.682 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.683 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.684 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx") ]  -- l.685 `movq %rbx, %rsi`

/-- Segment 23 of the body: the 32 instructions from source lines 686–717. -/
def ed25519ScMuladdShippedSeg023 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 0),  -- l.686 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.687 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.688 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.689 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.690 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r12"),  -- l.691 `addq %r12, %rdi`
    .mov "%r15" (.reg "%rdi"),  -- l.692 `movq %rdi, %r15`
    .storeMem "%rsp" 88 (.reg "%r15"),  -- l.693 `movq %r15, 88(%rsp)`
    .mov "%rdi" (.imm 0),  -- l.694 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.695 `movq %rcx, %r13`
    .and_ "%r13" (.reg "%rdi"),  -- l.696 `andq %rdi, %r13`
    .mov "%rdi" (.imm 0),  -- l.697 `movq $0, %rdi`
    .mov "%r9" (.reg "%rcx"),  -- l.698 `movq %rcx, %r9`
    .xor_ "%r9" (.reg "%rdi"),  -- l.699 `xorq %rdi, %r9`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.700 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.701 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.702 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r9"),  -- l.703 `movq %r9, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.704 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r13"),  -- l.705 `movq %r13, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.706 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.707 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.708 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.709 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.710 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.711 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.712 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r12"),  -- l.713 `andq %r12, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.714 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r12"),  -- l.715 `xorq %r12, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.716 `movq $18446744073709551615, %rbx`
    .loadMem "%r9" "%rsp" 88 ]  -- l.717 `movq 88(%rsp), %r9`

/-- Segment 24 of the body: the 32 instructions from source lines 718–749. -/
def ed25519ScMuladdShippedSeg024 : List (JInstr 64) :=
  [ .xor_ "%r9" (.reg "%rbx"),  -- l.718 `xorq %rbx, %r9`
    .mov "%rbx" (.reg "%rsi"),  -- l.719 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.720 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.721 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.722 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.723 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.724 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.725 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.726 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.727 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.728 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 120,  -- l.729 `movq 120(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 104,  -- l.730 `movq 104(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.731 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.732 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 120,  -- l.733 `movq 120(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.734 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.735 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.736 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.737 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.738 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.739 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.740 `addq %rbx, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.741 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.742 `movq %r9, %rcx`
    .add "%rcx" (.reg "%r11"),  -- l.743 `addq %r11, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.744 `movq %rcx, %r15`
    .storeMem "%rsp" 0 (.reg "%r15"),  -- l.745 `movq %r15, 0(%rsp)`
    .mov "%rcx" (.reg "%rsi"),  -- l.746 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.747 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.748 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx") ]  -- l.749 `xorq %rbx, %r13`

/-- Segment 25 of the body: the 32 instructions from source lines 750–781. -/
def ed25519ScMuladdShippedSeg025 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 18446744073709551615),  -- l.750 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.751 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.752 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.753 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.754 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.755 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.756 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.757 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.758 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.759 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.760 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.761 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r9"),  -- l.762 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.763 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.764 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.765 `xorq %r11, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.766 `movq $18446744073709551615, %rdi`
    .loadMem "%r9" "%rsp" 0,  -- l.767 `movq 0(%rsp), %r9`
    .xor_ "%r9" (.reg "%rdi"),  -- l.768 `xorq %rdi, %r9`
    .mov "%rdi" (.reg "%rsi"),  -- l.769 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r9"),  -- l.770 `andq %r9, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.771 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.772 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.773 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.774 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.775 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.776 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.777 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.778 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 120,  -- l.779 `movq 120(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 112,  -- l.780 `movq 112(%rsp), %r15`
    .imul "%rcx" (.reg "%r15") ]  -- l.781 `imulq %r15, %rcx`

/-- Segment 26 of the body: the 32 instructions from source lines 782–813. -/
def ed25519ScMuladdShippedSeg026 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rcx"),  -- l.782 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 120,  -- l.783 `movq 120(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.784 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.785 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.786 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.787 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.788 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.789 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.790 `addq %rbx, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.791 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.792 `movq %r9, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.793 `addq %r10, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.794 `movq %rcx, %r15`
    .storeMem "%rsp" 48 (.reg "%r15"),  -- l.795 `movq %r15, 48(%rsp)`
    .mov "%rcx" (.reg "%rsi"),  -- l.796 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.797 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.798 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.799 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.800 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.801 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.802 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.803 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.804 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.805 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.806 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.807 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.808 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.809 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.810 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.811 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r9"),  -- l.812 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%r10") ]  -- l.813 `andq %r10, %rbx`

/-- Segment 27 of the body: the 32 instructions from source lines 814–845. -/
def ed25519ScMuladdShippedSeg027 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%r9"),  -- l.814 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.815 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.816 `movq $18446744073709551615, %rdi`
    .loadMem "%r9" "%rsp" 48,  -- l.817 `movq 48(%rsp), %r9`
    .xor_ "%r9" (.reg "%rdi"),  -- l.818 `xorq %rdi, %r9`
    .mov "%rdi" (.reg "%rsi"),  -- l.819 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r9"),  -- l.820 `andq %r9, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.821 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.822 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.823 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.824 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.825 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.826 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.827 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.828 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 120,  -- l.829 `movq 120(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 128,  -- l.830 `movq 128(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.831 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.832 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 120,  -- l.833 `movq 120(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 128,  -- l.834 `movq 128(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.835 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.836 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.837 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.838 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.839 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.840 `addq %rbx, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.841 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.842 `movq %r9, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.843 `addq %rax, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.844 `movq %rcx, %r15`
    .storeMem "%rsp" 56 (.reg "%r15") ]  -- l.845 `movq %r15, 56(%rsp)`

/-- Segment 28 of the body: the 32 instructions from source lines 846–877. -/
def ed25519ScMuladdShippedSeg028 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rsi"),  -- l.846 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.847 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.848 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.849 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.850 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.851 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.852 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.853 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.854 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.855 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.856 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.857 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.858 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.859 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.860 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.861 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r9"),  -- l.862 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.863 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.864 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.865 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.866 `movq $18446744073709551615, %rax`
    .loadMem "%rdi" "%rsp" 56,  -- l.867 `movq 56(%rsp), %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.868 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.869 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.870 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.871 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.872 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.873 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.874 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.875 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.876 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax") ]  -- l.877 `addq %rax, %rbx`

/-- Segment 29 of the body: the 32 instructions from source lines 878–909. -/
def ed25519ScMuladdShippedSeg029 : List (JInstr 64) :=
  [ .mov "%r15" (.reg "%rbx"),  -- l.878 `movq %rbx, %r15`
    .storeMem "%rsp" 80 (.reg "%r15"),  -- l.879 `movq %r15, 80(%rsp)`
    .mov "%rbx" (.imm 17121812371768873755),  -- l.880 `movq $17121812371768873755, %rbx`
    .mov "%r15" (.reg "%rbx"),  -- l.881 `movq %rbx, %r15`
    .storeMem "%rsp" 8 (.reg "%r15"),  -- l.882 `movq %r15, 8(%rsp)`
    .mov "%rbx" (.imm 2379626136568277415),  -- l.883 `movq $2379626136568277415, %rbx`
    .mov "%r15" (.reg "%rbx"),  -- l.884 `movq %rbx, %r15`
    .storeMem "%rsp" 16 (.reg "%r15"),  -- l.885 `movq %r15, 16(%rsp)`
    .mov "%rbx" (.imm 18446744073709551595),  -- l.886 `movq $18446744073709551595, %rbx`
    .mov "%r15" (.reg "%rbx"),  -- l.887 `movq %rbx, %r15`
    .storeMem "%rsp" 24 (.reg "%r15"),  -- l.888 `movq %r15, 24(%rsp)`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.889 `movq $18446744073709551615, %rbx`
    .mov "%r15" (.reg "%rbx"),  -- l.890 `movq %rbx, %r15`
    .storeMem "%rsp" 32 (.reg "%r15"),  -- l.891 `movq %r15, 32(%rsp)`
    .mov "%rbx" (.imm 15),  -- l.892 `movq $15, %rbx`
    .mov "%r15" (.reg "%rbx"),  -- l.893 `movq %rbx, %r15`
    .storeMem "%rsp" 40 (.reg "%r15"),  -- l.894 `movq %r15, 40(%rsp)`
    .mov "%rbx" (.imm 6346243789798364141),  -- l.895 `movq $6346243789798364141, %rbx`
    .mov "%r15" (.reg "%rbx"),  -- l.896 `movq %rbx, %r15`
    .storeMem "%rsp" 128 (.reg "%r15"),  -- l.897 `movq %r15, 128(%rsp)`
    .mov "%rbx" (.imm 1503914060200516822),  -- l.898 `movq $1503914060200516822, %rbx`
    .mov "%r15" (.reg "%rbx"),  -- l.899 `movq %rbx, %r15`
    .storeMem "%rsp" 120 (.reg "%r15"),  -- l.900 `movq %r15, 120(%rsp)`
    .mov "%rbx" (.imm 0),  -- l.901 `movq $0, %rbx`
    .mov "%r15" (.reg "%rbx"),  -- l.902 `movq %rbx, %r15`
    .storeMem "%rsp" 112 (.reg "%r15"),  -- l.903 `movq %r15, 112(%rsp)`
    .mov "%rbx" (.imm 1152921504606846976),  -- l.904 `movq $1152921504606846976, %rbx`
    .mov "%r15" (.reg "%rbx"),  -- l.905 `movq %rbx, %r15`
    .storeMem "%rsp" 104 (.reg "%r15"),  -- l.906 `movq %r15, 104(%rsp)`
    .loadMem "%rbx" "%rsp" 96,  -- l.907 `movq 96(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8,  -- l.908 `movq 8(%rsp), %r15`
    .imul "%rbx" (.reg "%r15") ]  -- l.909 `imulq %r15, %rbx`

/-- Segment 30 of the body: the 32 instructions from source lines 910–941. -/
def ed25519ScMuladdShippedSeg030 : List (JInstr 64) :=
  [ .mov "%rbp" (.reg "%rbx"),  -- l.910 `movq %rbx, %rbp`
    .loadMem "%rdx" "%rsp" 96,  -- l.911 `movq 96(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.912 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.913 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.914 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.915 `movq -128(%rsp), %rcx`
    .mov "%r8" (.reg "%rbx"),  -- l.916 `movq %rbx, %r8`
    .mov "%rbx" (.imm 0),  -- l.917 `movq $0, %rbx`
    .mov "%rax" (.reg "%rbp"),  -- l.918 `movq %rbp, %rax`
    .add "%rax" (.reg "%rbx"),  -- l.919 `addq %rbx, %rax`
    .mov "%rbx" (.reg "%rax"),  -- l.920 `movq %rax, %rbx`
    .mov "%rax" (.imm 0),  -- l.921 `movq $0, %rax`
    .mov "%r10" (.reg "%rbx"),  -- l.922 `movq %rbx, %r10`
    .add "%r10" (.reg "%rax"),  -- l.923 `addq %rax, %r10`
    .mov "%rax" (.reg "%r10"),  -- l.924 `movq %r10, %rax`
    .mov "%r10" (.imm 0),  -- l.925 `movq $0, %r10`
    .mov "%r11" (.reg "%rbp"),  -- l.926 `movq %rbp, %r11`
    .and_ "%r11" (.reg "%r10"),  -- l.927 `andq %r10, %r11`
    .mov "%r10" (.imm 0),  -- l.928 `movq $0, %r10`
    .mov "%r13" (.reg "%rbp"),  -- l.929 `movq %rbp, %r13`
    .xor_ "%r13" (.reg "%r10"),  -- l.930 `xorq %r10, %r13`
    .mov "%rbp" (.imm 18446744073709551615),  -- l.931 `movq $18446744073709551615, %rbp`
    .mov "%r10" (.reg "%rbx"),  -- l.932 `movq %rbx, %r10`
    .xor_ "%r10" (.reg "%rbp"),  -- l.933 `xorq %rbp, %r10`
    .mov "%rbp" (.reg "%r13"),  -- l.934 `movq %r13, %rbp`
    .and_ "%rbp" (.reg "%r10"),  -- l.935 `andq %r10, %rbp`
    .mov "%r10" (.reg "%r11"),  -- l.936 `movq %r11, %r10`
    .xor_ "%r10" (.reg "%rbp"),  -- l.937 `xorq %rbp, %r10`
    .mov "%rbp" (.imm 63),  -- l.938 `movq $63, %rbp`
    .mov "%rbp" (.reg "%r10"),  -- l.939 `movq %r10, %rbp`
    .shr "%rbp" (.imm 63),  -- l.940 `shrq $63, %rbp`
    .mov "%r10" (.reg "%r8") ]  -- l.941 `movq %r8, %r10`

/-- Segment 31 of the body: the 32 instructions from source lines 942–973. -/
def ed25519ScMuladdShippedSeg031 : List (JInstr 64) :=
  [ .add "%r10" (.reg "%rbp"),  -- l.942 `addq %rbp, %r10`
    .mov "%rbp" (.imm 0),  -- l.943 `movq $0, %rbp`
    .mov "%r8" (.reg "%rbx"),  -- l.944 `movq %rbx, %r8`
    .and_ "%r8" (.reg "%rbp"),  -- l.945 `andq %rbp, %r8`
    .mov "%rbp" (.imm 0),  -- l.946 `movq $0, %rbp`
    .mov "%r11" (.reg "%rbx"),  -- l.947 `movq %rbx, %r11`
    .xor_ "%r11" (.reg "%rbp"),  -- l.948 `xorq %rbp, %r11`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.949 `movq $18446744073709551615, %rbx`
    .mov "%rbp" (.reg "%rax"),  -- l.950 `movq %rax, %rbp`
    .xor_ "%rbp" (.reg "%rbx"),  -- l.951 `xorq %rbx, %rbp`
    .mov "%rax" (.reg "%r11"),  -- l.952 `movq %r11, %rax`
    .and_ "%rax" (.reg "%rbp"),  -- l.953 `andq %rbp, %rax`
    .mov "%rbx" (.reg "%r8"),  -- l.954 `movq %r8, %rbx`
    .xor_ "%rbx" (.reg "%rax"),  -- l.955 `xorq %rax, %rbx`
    .mov "%rax" (.imm 63),  -- l.956 `movq $63, %rax`
    .mov "%rax" (.reg "%rbx"),  -- l.957 `movq %rbx, %rax`
    .shr "%rax" (.imm 63),  -- l.958 `shrq $63, %rax`
    .mov "%rbx" (.reg "%r10"),  -- l.959 `movq %r10, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.960 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.961 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 96,  -- l.962 `movq 96(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 16,  -- l.963 `movq 16(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.964 `imulq %r15, %rbx`
    .mov "%rbp" (.reg "%rbx"),  -- l.965 `movq %rbx, %rbp`
    .loadMem "%rdx" "%rsp" 96,  -- l.966 `movq 96(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.967 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.968 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.969 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.970 `movq -128(%rsp), %rcx`
    .mov "%r8" (.reg "%rbx"),  -- l.971 `movq %rbx, %r8`
    .mov "%rbx" (.reg "%rbp"),  -- l.972 `movq %rbp, %rbx`
    .add "%rbx" (.reg "%rax") ]  -- l.973 `addq %rax, %rbx`

/-- Segment 32 of the body: the 32 instructions from source lines 974–1005. -/
def ed25519ScMuladdShippedSeg032 : List (JInstr 64) :=
  [ .mov "%r10" (.reg "%rbx"),  -- l.974 `movq %rbx, %r10`
    .mov "%rbx" (.imm 0),  -- l.975 `movq $0, %rbx`
    .mov "%r11" (.reg "%r10"),  -- l.976 `movq %r10, %r11`
    .add "%r11" (.reg "%rbx"),  -- l.977 `addq %rbx, %r11`
    .mov "%rbx" (.reg "%r11"),  -- l.978 `movq %r11, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.979 `movq %rbp, %r11`
    .and_ "%r11" (.reg "%rax"),  -- l.980 `andq %rax, %r11`
    .mov "%r13" (.reg "%rbp"),  -- l.981 `movq %rbp, %r13`
    .xor_ "%r13" (.reg "%rax"),  -- l.982 `xorq %rax, %r13`
    .mov "%rax" (.imm 18446744073709551615),  -- l.983 `movq $18446744073709551615, %rax`
    .mov "%rbp" (.reg "%r10"),  -- l.984 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rax"),  -- l.985 `xorq %rax, %rbp`
    .mov "%rax" (.reg "%r13"),  -- l.986 `movq %r13, %rax`
    .and_ "%rax" (.reg "%rbp"),  -- l.987 `andq %rbp, %rax`
    .mov "%rbp" (.reg "%r11"),  -- l.988 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rax"),  -- l.989 `xorq %rax, %rbp`
    .mov "%rax" (.imm 63),  -- l.990 `movq $63, %rax`
    .mov "%rax" (.reg "%rbp"),  -- l.991 `movq %rbp, %rax`
    .shr "%rax" (.imm 63),  -- l.992 `shrq $63, %rax`
    .mov "%rbp" (.reg "%r8"),  -- l.993 `movq %r8, %rbp`
    .add "%rbp" (.reg "%rax"),  -- l.994 `addq %rax, %rbp`
    .mov "%rax" (.imm 0),  -- l.995 `movq $0, %rax`
    .mov "%r8" (.reg "%r10"),  -- l.996 `movq %r10, %r8`
    .and_ "%r8" (.reg "%rax"),  -- l.997 `andq %rax, %r8`
    .mov "%rax" (.imm 0),  -- l.998 `movq $0, %rax`
    .mov "%r11" (.reg "%r10"),  -- l.999 `movq %r10, %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.1000 `xorq %rax, %r11`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1001 `movq $18446744073709551615, %rax`
    .mov "%r10" (.reg "%rbx"),  -- l.1002 `movq %rbx, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.1003 `xorq %rax, %r10`
    .mov "%rax" (.reg "%r11"),  -- l.1004 `movq %r11, %rax`
    .and_ "%rax" (.reg "%r10") ]  -- l.1005 `andq %r10, %rax`

/-- Segment 33 of the body: the 32 instructions from source lines 1006–1037. -/
def ed25519ScMuladdShippedSeg033 : List (JInstr 64) :=
  [ .mov "%r10" (.reg "%r8"),  -- l.1006 `movq %r8, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.1007 `xorq %rax, %r10`
    .mov "%rax" (.imm 63),  -- l.1008 `movq $63, %rax`
    .mov "%rax" (.reg "%r10"),  -- l.1009 `movq %r10, %rax`
    .shr "%rax" (.imm 63),  -- l.1010 `shrq $63, %rax`
    .mov "%r8" (.reg "%rbp"),  -- l.1011 `movq %rbp, %r8`
    .add "%r8" (.reg "%rax"),  -- l.1012 `addq %rax, %r8`
    .mov "%rax" (.reg "%r8"),  -- l.1013 `movq %r8, %rax`
    .loadMem "%rbp" "%rsp" 96,  -- l.1014 `movq 96(%rsp), %rbp`
    .loadMem "%r15" "%rsp" 24,  -- l.1015 `movq 24(%rsp), %r15`
    .imul "%rbp" (.reg "%r15"),  -- l.1016 `imulq %r15, %rbp`
    .mov "%r8" (.reg "%rbp"),  -- l.1017 `movq %rbp, %r8`
    .loadMem "%rdx" "%rsp" 96,  -- l.1018 `movq 96(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.1019 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.1020 `movq %rcx, -128(%rsp)`
    .mulx "%rbp" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1021 `mulx %r14, %rcx, %rbp`
    .loadMem "%rcx" "%rsp" (-128),  -- l.1022 `movq -128(%rsp), %rcx`
    .mov "%r10" (.reg "%rbp"),  -- l.1023 `movq %rbp, %r10`
    .mov "%rbp" (.reg "%r8"),  -- l.1024 `movq %r8, %rbp`
    .add "%rbp" (.reg "%rax"),  -- l.1025 `addq %rax, %rbp`
    .mov "%r11" (.reg "%rbp"),  -- l.1026 `movq %rbp, %r11`
    .mov "%rbp" (.imm 0),  -- l.1027 `movq $0, %rbp`
    .mov "%r13" (.reg "%r11"),  -- l.1028 `movq %r11, %r13`
    .add "%r13" (.reg "%rbp"),  -- l.1029 `addq %rbp, %r13`
    .mov "%rbp" (.reg "%r13"),  -- l.1030 `movq %r13, %rbp`
    .mov "%r13" (.reg "%r8"),  -- l.1031 `movq %r8, %r13`
    .and_ "%r13" (.reg "%rax"),  -- l.1032 `andq %rax, %r13`
    .mov "%r9" (.reg "%r8"),  -- l.1033 `movq %r8, %r9`
    .xor_ "%r9" (.reg "%rax"),  -- l.1034 `xorq %rax, %r9`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1035 `movq $18446744073709551615, %rax`
    .mov "%r8" (.reg "%r11"),  -- l.1036 `movq %r11, %r8`
    .xor_ "%r8" (.reg "%rax") ]  -- l.1037 `xorq %rax, %r8`

/-- Segment 34 of the body: the 32 instructions from source lines 1038–1069. -/
def ed25519ScMuladdShippedSeg034 : List (JInstr 64) :=
  [ .mov "%rax" (.reg "%r9"),  -- l.1038 `movq %r9, %rax`
    .and_ "%rax" (.reg "%r8"),  -- l.1039 `andq %r8, %rax`
    .mov "%r8" (.reg "%r13"),  -- l.1040 `movq %r13, %r8`
    .xor_ "%r8" (.reg "%rax"),  -- l.1041 `xorq %rax, %r8`
    .mov "%rax" (.imm 63),  -- l.1042 `movq $63, %rax`
    .mov "%rax" (.reg "%r8"),  -- l.1043 `movq %r8, %rax`
    .shr "%rax" (.imm 63),  -- l.1044 `shrq $63, %rax`
    .mov "%r8" (.reg "%r10"),  -- l.1045 `movq %r10, %r8`
    .add "%r8" (.reg "%rax"),  -- l.1046 `addq %rax, %r8`
    .mov "%rax" (.imm 0),  -- l.1047 `movq $0, %rax`
    .mov "%r9" (.reg "%r11"),  -- l.1048 `movq %r11, %r9`
    .and_ "%r9" (.reg "%rax"),  -- l.1049 `andq %rax, %r9`
    .mov "%rax" (.imm 0),  -- l.1050 `movq $0, %rax`
    .mov "%r10" (.reg "%r11"),  -- l.1051 `movq %r11, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.1052 `xorq %rax, %r10`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1053 `movq $18446744073709551615, %rax`
    .mov "%r11" (.reg "%rbp"),  -- l.1054 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.1055 `xorq %rax, %r11`
    .mov "%rax" (.reg "%r10"),  -- l.1056 `movq %r10, %rax`
    .and_ "%rax" (.reg "%r11"),  -- l.1057 `andq %r11, %rax`
    .mov "%r10" (.reg "%r9"),  -- l.1058 `movq %r9, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.1059 `xorq %rax, %r10`
    .mov "%rax" (.imm 63),  -- l.1060 `movq $63, %rax`
    .mov "%rax" (.reg "%r10"),  -- l.1061 `movq %r10, %rax`
    .shr "%rax" (.imm 63),  -- l.1062 `shrq $63, %rax`
    .mov "%r9" (.reg "%r8"),  -- l.1063 `movq %r8, %r9`
    .add "%r9" (.reg "%rax"),  -- l.1064 `addq %rax, %r9`
    .mov "%rax" (.reg "%r9"),  -- l.1065 `movq %r9, %rax`
    .loadMem "%r8" "%rsp" 96,  -- l.1066 `movq 96(%rsp), %r8`
    .loadMem "%r15" "%rsp" 32,  -- l.1067 `movq 32(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.1068 `imulq %r15, %r8`
    .mov "%r9" (.reg "%r8") ]  -- l.1069 `movq %r8, %r9`

/-- Segment 35 of the body: the 32 instructions from source lines 1070–1101. -/
def ed25519ScMuladdShippedSeg035 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsp" 96,  -- l.1070 `movq 96(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.1071 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.1072 `movq %rcx, -128(%rsp)`
    .mulx "%r8" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1073 `mulx %r14, %rcx, %r8`
    .loadMem "%rcx" "%rsp" (-128),  -- l.1074 `movq -128(%rsp), %rcx`
    .mov "%r10" (.reg "%r8"),  -- l.1075 `movq %r8, %r10`
    .mov "%r8" (.reg "%r9"),  -- l.1076 `movq %r9, %r8`
    .add "%r8" (.reg "%rax"),  -- l.1077 `addq %rax, %r8`
    .mov "%r11" (.reg "%r8"),  -- l.1078 `movq %r8, %r11`
    .mov "%r8" (.imm 0),  -- l.1079 `movq $0, %r8`
    .mov "%r13" (.reg "%r11"),  -- l.1080 `movq %r11, %r13`
    .add "%r13" (.reg "%r8"),  -- l.1081 `addq %r8, %r13`
    .mov "%r8" (.reg "%r13"),  -- l.1082 `movq %r13, %r8`
    .mov "%r13" (.reg "%r9"),  -- l.1083 `movq %r9, %r13`
    .and_ "%r13" (.reg "%rax"),  -- l.1084 `andq %rax, %r13`
    .mov "%rdi" (.reg "%r9"),  -- l.1085 `movq %r9, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.1086 `xorq %rax, %rdi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1087 `movq $18446744073709551615, %rax`
    .mov "%r9" (.reg "%r11"),  -- l.1088 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rax"),  -- l.1089 `xorq %rax, %r9`
    .mov "%rax" (.reg "%rdi"),  -- l.1090 `movq %rdi, %rax`
    .and_ "%rax" (.reg "%r9"),  -- l.1091 `andq %r9, %rax`
    .mov "%rdi" (.reg "%r13"),  -- l.1092 `movq %r13, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.1093 `xorq %rax, %rdi`
    .mov "%rax" (.imm 63),  -- l.1094 `movq $63, %rax`
    .mov "%rax" (.reg "%rdi"),  -- l.1095 `movq %rdi, %rax`
    .shr "%rax" (.imm 63),  -- l.1096 `shrq $63, %rax`
    .mov "%rdi" (.reg "%r10"),  -- l.1097 `movq %r10, %rdi`
    .add "%rdi" (.reg "%rax"),  -- l.1098 `addq %rax, %rdi`
    .mov "%rax" (.imm 0),  -- l.1099 `movq $0, %rax`
    .mov "%r9" (.reg "%r11"),  -- l.1100 `movq %r11, %r9`
    .and_ "%r9" (.reg "%rax") ]  -- l.1101 `andq %rax, %r9`

/-- Segment 36 of the body: the 32 instructions from source lines 1102–1133. -/
def ed25519ScMuladdShippedSeg036 : List (JInstr 64) :=
  [ .mov "%rax" (.imm 0),  -- l.1102 `movq $0, %rax`
    .mov "%r10" (.reg "%r11"),  -- l.1103 `movq %r11, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.1104 `xorq %rax, %r10`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1105 `movq $18446744073709551615, %rax`
    .mov "%r11" (.reg "%r8"),  -- l.1106 `movq %r8, %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.1107 `xorq %rax, %r11`
    .mov "%rax" (.reg "%r10"),  -- l.1108 `movq %r10, %rax`
    .and_ "%rax" (.reg "%r11"),  -- l.1109 `andq %r11, %rax`
    .mov "%r10" (.reg "%r9"),  -- l.1110 `movq %r9, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.1111 `xorq %rax, %r10`
    .mov "%rax" (.imm 63),  -- l.1112 `movq $63, %rax`
    .mov "%rax" (.reg "%r10"),  -- l.1113 `movq %r10, %rax`
    .shr "%rax" (.imm 63),  -- l.1114 `shrq $63, %rax`
    .mov "%r9" (.reg "%rdi"),  -- l.1115 `movq %rdi, %r9`
    .add "%r9" (.reg "%rax"),  -- l.1116 `addq %rax, %r9`
    .mov "%rax" (.reg "%r9"),  -- l.1117 `movq %r9, %rax`
    .loadMem "%rdi" "%rsp" 96,  -- l.1118 `movq 96(%rsp), %rdi`
    .loadMem "%r15" "%rsp" 40,  -- l.1119 `movq 40(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.1120 `imulq %r15, %rdi`
    .mov "%r9" (.reg "%rdi"),  -- l.1121 `movq %rdi, %r9`
    .loadMem "%rdx" "%rsp" 96,  -- l.1122 `movq 96(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.1123 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.1124 `movq %rcx, -128(%rsp)`
    .mulx "%rdi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1125 `mulx %r14, %rcx, %rdi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.1126 `movq -128(%rsp), %rcx`
    .mov "%r10" (.reg "%rdi"),  -- l.1127 `movq %rdi, %r10`
    .mov "%rdi" (.reg "%r9"),  -- l.1128 `movq %r9, %rdi`
    .add "%rdi" (.reg "%rax"),  -- l.1129 `addq %rax, %rdi`
    .mov "%r11" (.reg "%rdi"),  -- l.1130 `movq %rdi, %r11`
    .mov "%rdi" (.imm 0),  -- l.1131 `movq $0, %rdi`
    .mov "%r13" (.reg "%r11"),  -- l.1132 `movq %r11, %r13`
    .add "%r13" (.reg "%rdi") ]  -- l.1133 `addq %rdi, %r13`

/-- Segment 37 of the body: the 32 instructions from source lines 1134–1165. -/
def ed25519ScMuladdShippedSeg037 : List (JInstr 64) :=
  [ .mov "%rdi" (.reg "%r13"),  -- l.1134 `movq %r13, %rdi`
    .mov "%r13" (.reg "%r9"),  -- l.1135 `movq %r9, %r13`
    .and_ "%r13" (.reg "%rax"),  -- l.1136 `andq %rax, %r13`
    .mov "%rsi" (.reg "%r9"),  -- l.1137 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1138 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1139 `movq $18446744073709551615, %rax`
    .mov "%r9" (.reg "%r11"),  -- l.1140 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rax"),  -- l.1141 `xorq %rax, %r9`
    .mov "%rax" (.reg "%rsi"),  -- l.1142 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%r9"),  -- l.1143 `andq %r9, %rax`
    .mov "%rsi" (.reg "%r13"),  -- l.1144 `movq %r13, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1145 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.1146 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.1147 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.1148 `shrq $63, %rax`
    .mov "%rsi" (.reg "%r10"),  -- l.1149 `movq %r10, %rsi`
    .add "%rsi" (.reg "%rax"),  -- l.1150 `addq %rax, %rsi`
    .mov "%rax" (.imm 0),  -- l.1151 `movq $0, %rax`
    .mov "%r9" (.reg "%r11"),  -- l.1152 `movq %r11, %r9`
    .and_ "%r9" (.reg "%rax"),  -- l.1153 `andq %rax, %r9`
    .mov "%rax" (.imm 0),  -- l.1154 `movq $0, %rax`
    .mov "%r10" (.reg "%r11"),  -- l.1155 `movq %r11, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.1156 `xorq %rax, %r10`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1157 `movq $18446744073709551615, %rax`
    .mov "%r11" (.reg "%rdi"),  -- l.1158 `movq %rdi, %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.1159 `xorq %rax, %r11`
    .mov "%rax" (.reg "%r10"),  -- l.1160 `movq %r10, %rax`
    .and_ "%rax" (.reg "%r11"),  -- l.1161 `andq %r11, %rax`
    .mov "%r10" (.reg "%r9"),  -- l.1162 `movq %r9, %r10`
    .xor_ "%r10" (.reg "%rax"),  -- l.1163 `xorq %rax, %r10`
    .mov "%rax" (.imm 63),  -- l.1164 `movq $63, %rax`
    .mov "%rax" (.reg "%r10") ]  -- l.1165 `movq %r10, %rax`

/-- Segment 38 of the body: the 32 instructions from source lines 1166–1197. -/
def ed25519ScMuladdShippedSeg038 : List (JInstr 64) :=
  [ .shr "%rax" (.imm 63),  -- l.1166 `shrq $63, %rax`
    .mov "%r9" (.reg "%rsi"),  -- l.1167 `movq %rsi, %r9`
    .add "%r9" (.reg "%rax"),  -- l.1168 `addq %rax, %r9`
    .mov "%rax" (.reg "%r9"),  -- l.1169 `movq %r9, %rax`
    .loadMem "%rsi" "%rsp" 64,  -- l.1170 `movq 64(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 8,  -- l.1171 `movq 8(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.1172 `imulq %r15, %rsi`
    .mov "%r9" (.reg "%rsi"),  -- l.1173 `movq %rsi, %r9`
    .loadMem "%rdx" "%rsp" 64,  -- l.1174 `movq 64(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.1175 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.1176 `movq %rcx, -128(%rsp)`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1177 `mulx %r14, %rcx, %rsi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.1178 `movq -128(%rsp), %rcx`
    .mov "%r10" (.reg "%rsi"),  -- l.1179 `movq %rsi, %r10`
    .mov "%rsi" (.imm 0),  -- l.1180 `movq $0, %rsi`
    .mov "%r11" (.reg "%r9"),  -- l.1181 `movq %r9, %r11`
    .add "%r11" (.reg "%rsi"),  -- l.1182 `addq %rsi, %r11`
    .mov "%rsi" (.reg "%r11"),  -- l.1183 `movq %r11, %rsi`
    .mov "%r11" (.reg "%rsi"),  -- l.1184 `movq %rsi, %r11`
    .add "%r11" (.reg "%rbx"),  -- l.1185 `addq %rbx, %r11`
    .mov "%r13" (.reg "%r11"),  -- l.1186 `movq %r11, %r13`
    .mov "%r11" (.imm 0),  -- l.1187 `movq $0, %r11`
    .mov "%rcx" (.reg "%r9"),  -- l.1188 `movq %r9, %rcx`
    .and_ "%rcx" (.reg "%r11"),  -- l.1189 `andq %r11, %rcx`
    .mov "%r11" (.imm 0),  -- l.1190 `movq $0, %r11`
    .mov "%r12" (.reg "%r9"),  -- l.1191 `movq %r9, %r12`
    .xor_ "%r12" (.reg "%r11"),  -- l.1192 `xorq %r11, %r12`
    .mov "%r9" (.imm 18446744073709551615),  -- l.1193 `movq $18446744073709551615, %r9`
    .mov "%r11" (.reg "%rsi"),  -- l.1194 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%r9"),  -- l.1195 `xorq %r9, %r11`
    .mov "%r9" (.reg "%r12"),  -- l.1196 `movq %r12, %r9`
    .and_ "%r9" (.reg "%r11") ]  -- l.1197 `andq %r11, %r9`

/-- Segment 39 of the body: the 32 instructions from source lines 1198–1229. -/
def ed25519ScMuladdShippedSeg039 : List (JInstr 64) :=
  [ .mov "%r11" (.reg "%rcx"),  -- l.1198 `movq %rcx, %r11`
    .xor_ "%r11" (.reg "%r9"),  -- l.1199 `xorq %r9, %r11`
    .mov "%rcx" (.imm 63),  -- l.1200 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r11"),  -- l.1201 `movq %r11, %rcx`
    .shr "%rcx" (.imm 63),  -- l.1202 `shrq $63, %rcx`
    .mov "%r9" (.reg "%r10"),  -- l.1203 `movq %r10, %r9`
    .add "%r9" (.reg "%rcx"),  -- l.1204 `addq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.1205 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1206 `andq %rbx, %rcx`
    .mov "%r10" (.reg "%rsi"),  -- l.1207 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.1208 `xorq %rbx, %r10`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1209 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r13"),  -- l.1210 `movq %r13, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1211 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r10"),  -- l.1212 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1213 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1214 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1215 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1216 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1217 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1218 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%r9"),  -- l.1219 `movq %r9, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1220 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.1221 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 64,  -- l.1222 `movq 64(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.1223 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1224 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1225 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 64,  -- l.1226 `movq 64(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.1227 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1228 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14") ]  -- l.1229 `mulx %r14, %rsi, %rcx`

/-- Segment 40 of the body: the 32 instructions from source lines 1230–1261. -/
def ed25519ScMuladdShippedSeg040 : List (JInstr 64) :=
  [ .loadMem "%rsi" "%rsp" (-128),  -- l.1230 `movq -128(%rsp), %rsi`
    .mov "%r9" (.reg "%rcx"),  -- l.1231 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.1232 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1233 `addq %rbx, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.1234 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%r10"),  -- l.1235 `movq %r10, %rcx`
    .add "%rcx" (.reg "%rbp"),  -- l.1236 `addq %rbp, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.1237 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.1238 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1239 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1240 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1241 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1242 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.1243 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1244 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1245 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1246 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1247 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1248 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1249 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1250 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1251 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%r9"),  -- l.1252 `movq %r9, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1253 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r10"),  -- l.1254 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%rbp"),  -- l.1255 `andq %rbp, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.1256 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%rbp"),  -- l.1257 `xorq %rbp, %rsi`
    .mov "%rbp" (.imm 18446744073709551615),  -- l.1258 `movq $18446744073709551615, %rbp`
    .mov "%r9" (.reg "%r11"),  -- l.1259 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rbp"),  -- l.1260 `xorq %rbp, %r9`
    .mov "%rbp" (.reg "%rsi") ]  -- l.1261 `movq %rsi, %rbp`

/-- Segment 41 of the body: the 32 instructions from source lines 1262–1293. -/
def ed25519ScMuladdShippedSeg041 : List (JInstr 64) :=
  [ .and_ "%rbp" (.reg "%r9"),  -- l.1262 `andq %r9, %rbp`
    .mov "%rsi" (.reg "%rbx"),  -- l.1263 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rbp"),  -- l.1264 `xorq %rbp, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1265 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1266 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1267 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1268 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1269 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1270 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 64,  -- l.1271 `movq 64(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.1272 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1273 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1274 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 64,  -- l.1275 `movq 64(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.1276 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1277 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1278 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1279 `movq -128(%rsp), %rsi`
    .mov "%rbp" (.reg "%rcx"),  -- l.1280 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rsi"),  -- l.1281 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1282 `addq %rbx, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.1283 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.1284 `movq %r9, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.1285 `addq %r8, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.1286 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.1287 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1288 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1289 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1290 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1291 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.1292 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rbx") ]  -- l.1293 `xorq %rbx, %rsi`

/-- Segment 42 of the body: the 32 instructions from source lines 1294–1325. -/
def ed25519ScMuladdShippedSeg042 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%r12"),  -- l.1294 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1295 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1296 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1297 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1298 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1299 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1300 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rbp"),  -- l.1301 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1302 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r9"),  -- l.1303 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.1304 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.1305 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.1306 `xorq %r8, %rsi`
    .mov "%rbp" (.imm 18446744073709551615),  -- l.1307 `movq $18446744073709551615, %rbp`
    .mov "%r8" (.reg "%r10"),  -- l.1308 `movq %r10, %r8`
    .xor_ "%r8" (.reg "%rbp"),  -- l.1309 `xorq %rbp, %r8`
    .mov "%rbp" (.reg "%rsi"),  -- l.1310 `movq %rsi, %rbp`
    .and_ "%rbp" (.reg "%r8"),  -- l.1311 `andq %r8, %rbp`
    .mov "%rsi" (.reg "%rbx"),  -- l.1312 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rbp"),  -- l.1313 `xorq %rbp, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1314 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1315 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1316 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1317 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1318 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1319 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 64,  -- l.1320 `movq 64(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.1321 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1322 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1323 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 64,  -- l.1324 `movq 64(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32 ]  -- l.1325 `movq 32(%rsp), %r14`

/-- Segment 43 of the body: the 32 instructions from source lines 1326–1357. -/
def ed25519ScMuladdShippedSeg043 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1326 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1327 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1328 `movq -128(%rsp), %rsi`
    .mov "%rbp" (.reg "%rcx"),  -- l.1329 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rsi"),  -- l.1330 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1331 `addq %rbx, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.1332 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%r8"),  -- l.1333 `movq %r8, %rcx`
    .add "%rcx" (.reg "%rdi"),  -- l.1334 `addq %rdi, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.1335 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.1336 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1337 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1338 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1339 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1340 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.1341 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1342 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1343 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1344 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1345 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1346 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1347 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1348 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1349 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rbp"),  -- l.1350 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1351 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r8"),  -- l.1352 `movq %r8, %rbx`
    .and_ "%rbx" (.reg "%rdi"),  -- l.1353 `andq %rdi, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.1354 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1355 `xorq %rdi, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1356 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9") ]  -- l.1357 `movq %r9, %rbp`

/-- Segment 44 of the body: the 32 instructions from source lines 1358–1389. -/
def ed25519ScMuladdShippedSeg044 : List (JInstr 64) :=
  [ .xor_ "%rbp" (.reg "%rdi"),  -- l.1358 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1359 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1360 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1361 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1362 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1363 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1364 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1365 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1366 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1367 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1368 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 64,  -- l.1369 `movq 64(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.1370 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1371 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1372 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 64,  -- l.1373 `movq 64(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.1374 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1375 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1376 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1377 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1378 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1379 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1380 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1381 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1382 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.1383 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.1384 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.1385 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1386 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1387 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1388 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615) ]  -- l.1389 `movq $18446744073709551615, %rbx`

/-- Segment 45 of the body: the 32 instructions from source lines 1390–1421. -/
def ed25519ScMuladdShippedSeg045 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rbp"),  -- l.1390 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1391 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1392 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1393 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1394 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1395 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1396 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1397 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1398 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1399 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1400 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1401 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.1402 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1403 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1404 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1405 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.1406 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.1407 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.1408 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.1409 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.1410 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1411 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.1412 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.1413 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.1414 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.1415 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.1416 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.1417 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 72,  -- l.1418 `movq 72(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8,  -- l.1419 `movq 8(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.1420 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx") ]  -- l.1421 `movq %rbx, %rcx`

/-- Segment 46 of the body: the 32 instructions from source lines 1422–1453. -/
def ed25519ScMuladdShippedSeg046 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsp" 72,  -- l.1422 `movq 72(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.1423 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.1424 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1425 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.1426 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1427 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.1428 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.1429 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.1430 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.1431 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1432 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r11"),  -- l.1433 `addq %r11, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.1434 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0),  -- l.1435 `movq $0, %rdi`
    .mov "%r12" (.reg "%rcx"),  -- l.1436 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rdi"),  -- l.1437 `andq %rdi, %r12`
    .mov "%rdi" (.imm 0),  -- l.1438 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.1439 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.1440 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.1441 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1442 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1443 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.1444 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.1445 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r12"),  -- l.1446 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1447 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.1448 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1449 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.1450 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.1451 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.1452 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx") ]  -- l.1453 `movq %rbx, %rcx`

/-- Segment 47 of the body: the 32 instructions from source lines 1454–1485. -/
def ed25519ScMuladdShippedSeg047 : List (JInstr 64) :=
  [ .and_ "%rcx" (.reg "%r11"),  -- l.1454 `andq %r11, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1455 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.1456 `xorq %r11, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1457 `movq $18446744073709551615, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.1458 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.1459 `xorq %rbx, %r11`
    .mov "%rbx" (.reg "%rsi"),  -- l.1460 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.1461 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1462 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1463 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1464 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1465 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1466 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1467 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1468 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.1469 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 72,  -- l.1470 `movq 72(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.1471 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1472 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1473 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 72,  -- l.1474 `movq 72(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.1475 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1476 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1477 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1478 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1479 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1480 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1481 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1482 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1483 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.1484 `addq %r10, %rcx`
    .mov "%r11" (.reg "%rcx") ]  -- l.1485 `movq %rcx, %r11`

/-- Segment 48 of the body: the 32 instructions from source lines 1486–1517. -/
def ed25519ScMuladdShippedSeg048 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rsi"),  -- l.1486 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1487 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1488 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1489 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1490 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1491 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1492 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1493 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1494 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1495 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1496 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1497 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1498 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1499 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1500 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1501 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1502 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.1503 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1504 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.1505 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1506 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r11"),  -- l.1507 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1508 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1509 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1510 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1511 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1512 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1513 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1514 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1515 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1516 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx") ]  -- l.1517 `addq %rbx, %rsi`

/-- Segment 49 of the body: the 32 instructions from source lines 1518–1549. -/
def ed25519ScMuladdShippedSeg049 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%rsi"),  -- l.1518 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 72,  -- l.1519 `movq 72(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.1520 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1521 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1522 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 72,  -- l.1523 `movq 72(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.1524 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1525 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1526 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1527 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1528 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1529 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1530 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1531 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1532 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.1533 `addq %r9, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.1534 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.1535 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1536 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1537 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1538 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1539 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1540 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1541 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1542 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1543 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1544 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1545 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1546 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1547 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1548 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi") ]  -- l.1549 `movq %rdi, %rcx`

/-- Segment 50 of the body: the 32 instructions from source lines 1550–1581. -/
def ed25519ScMuladdShippedSeg050 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%rbx"),  -- l.1550 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1551 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.1552 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1553 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.1554 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1555 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.1556 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1557 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1558 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1559 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1560 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1561 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1562 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1563 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1564 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1565 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1566 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1567 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 72,  -- l.1568 `movq 72(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.1569 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1570 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1571 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 72,  -- l.1572 `movq 72(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.1573 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1574 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1575 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1576 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1577 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1578 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1579 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1580 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp") ]  -- l.1581 `movq %rbp, %rcx`

/-- Segment 51 of the body: the 32 instructions from source lines 1582–1613. -/
def ed25519ScMuladdShippedSeg051 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%r8"),  -- l.1582 `addq %r8, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.1583 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.1584 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1585 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1586 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1587 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1588 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1589 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1590 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1591 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1592 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1593 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1594 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1595 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1596 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1597 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1598 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1599 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1600 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.1601 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1602 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.1603 `xorq %r8, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1604 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9"),  -- l.1605 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1606 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1607 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1608 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1609 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1610 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1611 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1612 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63) ]  -- l.1613 `shrq $63, %rbx`

/-- Segment 52 of the body: the 32 instructions from source lines 1614–1645. -/
def ed25519ScMuladdShippedSeg052 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rcx"),  -- l.1614 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1615 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1616 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 72,  -- l.1617 `movq 72(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.1618 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1619 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1620 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 72,  -- l.1621 `movq 72(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.1622 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1623 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1624 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1625 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1626 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1627 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1628 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1629 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1630 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.1631 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.1632 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.1633 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1634 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1635 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1636 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1637 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1638 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1639 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1640 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1641 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1642 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1643 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1644 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi") ]  -- l.1645 `movq %rsi, %rbx`

/-- Segment 53 of the body: the 32 instructions from source lines 1646–1677. -/
def ed25519ScMuladdShippedSeg053 : List (JInstr 64) :=
  [ .shr "%rbx" (.imm 63),  -- l.1646 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1647 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1648 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1649 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.1650 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1651 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1652 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.1653 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.1654 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.1655 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.1656 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.1657 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.1658 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1659 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.1660 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.1661 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.1662 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.1663 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.1664 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.1665 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 88,  -- l.1666 `movq 88(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8,  -- l.1667 `movq 8(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.1668 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.1669 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 88,  -- l.1670 `movq 88(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.1671 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.1672 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1673 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.1674 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1675 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.1676 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx") ]  -- l.1677 `movq %rcx, %rdi`

/-- Segment 54 of the body: the 32 instructions from source lines 1678–1709. -/
def ed25519ScMuladdShippedSeg054 : List (JInstr 64) :=
  [ .add "%rdi" (.reg "%rbx"),  -- l.1678 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.1679 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1680 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r11"),  -- l.1681 `addq %r11, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.1682 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0),  -- l.1683 `movq $0, %rdi`
    .mov "%r12" (.reg "%rcx"),  -- l.1684 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rdi"),  -- l.1685 `andq %rdi, %r12`
    .mov "%rdi" (.imm 0),  -- l.1686 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.1687 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.1688 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.1689 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1690 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1691 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.1692 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.1693 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r12"),  -- l.1694 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1695 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.1696 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1697 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.1698 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.1699 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.1700 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.1701 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r11"),  -- l.1702 `andq %r11, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1703 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.1704 `xorq %r11, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1705 `movq $18446744073709551615, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.1706 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.1707 `xorq %rbx, %r11`
    .mov "%rbx" (.reg "%rsi"),  -- l.1708 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11") ]  -- l.1709 `andq %r11, %rbx`

/-- Segment 55 of the body: the 32 instructions from source lines 1710–1741. -/
def ed25519ScMuladdShippedSeg055 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rcx"),  -- l.1710 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1711 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1712 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1713 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1714 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1715 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1716 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.1717 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 88,  -- l.1718 `movq 88(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.1719 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1720 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1721 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 88,  -- l.1722 `movq 88(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.1723 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1724 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1725 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1726 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1727 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1728 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1729 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1730 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1731 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.1732 `addq %r10, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.1733 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.1734 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1735 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1736 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1737 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1738 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1739 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1740 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12") ]  -- l.1741 `movq %r12, %rbx`

/-- Segment 56 of the body: the 32 instructions from source lines 1742–1773. -/
def ed25519ScMuladdShippedSeg056 : List (JInstr 64) :=
  [ .and_ "%rbx" (.reg "%rsi"),  -- l.1742 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1743 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1744 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1745 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1746 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1747 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1748 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1749 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1750 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.1751 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1752 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.1753 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1754 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r11"),  -- l.1755 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1756 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1757 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1758 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1759 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1760 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1761 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1762 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1763 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1764 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1765 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1766 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 88,  -- l.1767 `movq 88(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.1768 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1769 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1770 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 88,  -- l.1771 `movq 88(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.1772 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi") ]  -- l.1773 `movq %rsi, -128(%rsp)`

/-- Segment 57 of the body: the 32 instructions from source lines 1774–1805. -/
def ed25519ScMuladdShippedSeg057 : List (JInstr 64) :=
  [ .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1774 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1775 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1776 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1777 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1778 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1779 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1780 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.1781 `addq %r9, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.1782 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.1783 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1784 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1785 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1786 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1787 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1788 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1789 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1790 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1791 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1792 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1793 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1794 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1795 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1796 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1797 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1798 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1799 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.1800 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1801 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.1802 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1803 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.1804 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi") ]  -- l.1805 `xorq %rdi, %rbp`

/-- Segment 58 of the body: the 32 instructions from source lines 1806–1837. -/
def ed25519ScMuladdShippedSeg058 : List (JInstr 64) :=
  [ .mov "%rdi" (.reg "%rsi"),  -- l.1806 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1807 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1808 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1809 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1810 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1811 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1812 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1813 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1814 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1815 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 88,  -- l.1816 `movq 88(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.1817 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1818 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1819 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 88,  -- l.1820 `movq 88(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.1821 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1822 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1823 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1824 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1825 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1826 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1827 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1828 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1829 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.1830 `addq %r8, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.1831 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.1832 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1833 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1834 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1835 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1836 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp") ]  -- l.1837 `movq %rbp, %rsi`

/-- Segment 59 of the body: the 32 instructions from source lines 1838–1869. -/
def ed25519ScMuladdShippedSeg059 : List (JInstr 64) :=
  [ .xor_ "%rsi" (.reg "%rbx"),  -- l.1838 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1839 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1840 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1841 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1842 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1843 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1844 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1845 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1846 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1847 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1848 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.1849 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1850 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.1851 `xorq %r8, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.1852 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9"),  -- l.1853 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.1854 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.1855 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.1856 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.1857 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.1858 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1859 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1860 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1861 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1862 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.1863 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.1864 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 88,  -- l.1865 `movq 88(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.1866 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1867 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1868 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 88 ]  -- l.1869 `movq 88(%rsp), %rdx`

/-- Segment 60 of the body: the 32 instructions from source lines 1870–1901. -/
def ed25519ScMuladdShippedSeg060 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 40,  -- l.1870 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1871 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1872 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1873 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1874 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1875 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1876 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1877 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1878 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.1879 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.1880 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.1881 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1882 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1883 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1884 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1885 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1886 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1887 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1888 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1889 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1890 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1891 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1892 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1893 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1894 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1895 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1896 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.1897 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.1898 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1899 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1900 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615) ]  -- l.1901 `movq $18446744073709551615, %rax`

/-- Segment 61 of the body: the 32 instructions from source lines 1902–1933. -/
def ed25519ScMuladdShippedSeg061 : List (JInstr 64) :=
  [ .mov "%rdi" (.reg "%r8"),  -- l.1902 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.1903 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.1904 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.1905 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.1906 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.1907 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.1908 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.1909 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.1910 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.1911 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.1912 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.1913 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 0,  -- l.1914 `movq 0(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8,  -- l.1915 `movq 8(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.1916 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.1917 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 0,  -- l.1918 `movq 0(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.1919 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.1920 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1921 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.1922 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1923 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.1924 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.1925 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.1926 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.1927 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1928 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r11"),  -- l.1929 `addq %r11, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.1930 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0),  -- l.1931 `movq $0, %rdi`
    .mov "%r12" (.reg "%rcx"),  -- l.1932 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rdi") ]  -- l.1933 `andq %rdi, %r12`

/-- Segment 62 of the body: the 32 instructions from source lines 1934–1965. -/
def ed25519ScMuladdShippedSeg062 : List (JInstr 64) :=
  [ .mov "%rdi" (.imm 0),  -- l.1934 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.1935 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.1936 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.1937 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.1938 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1939 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.1940 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.1941 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r12"),  -- l.1942 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.1943 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.1944 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1945 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.1946 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.1947 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.1948 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.1949 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r11"),  -- l.1950 `andq %r11, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.1951 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.1952 `xorq %r11, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1953 `movq $18446744073709551615, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.1954 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.1955 `xorq %rbx, %r11`
    .mov "%rbx" (.reg "%rsi"),  -- l.1956 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.1957 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1958 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1959 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1960 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1961 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1962 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1963 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1964 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx") ]  -- l.1965 `movq %rcx, %rbx`

/-- Segment 63 of the body: the 32 instructions from source lines 1966–1997. -/
def ed25519ScMuladdShippedSeg063 : List (JInstr 64) :=
  [ .loadMem "%rcx" "%rsp" 0,  -- l.1966 `movq 0(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.1967 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1968 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1969 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 0,  -- l.1970 `movq 0(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.1971 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.1972 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1973 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.1974 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1975 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.1976 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.1977 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.1978 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.1979 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.1980 `addq %r10, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.1981 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.1982 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.1983 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.1984 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.1985 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.1986 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.1987 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1988 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.1989 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.1990 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.1991 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.1992 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.1993 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.1994 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.1995 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.1996 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx") ]  -- l.1997 `addq %rbx, %rcx`

/-- Segment 64 of the body: the 32 instructions from source lines 1998–2029. -/
def ed25519ScMuladdShippedSeg064 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%rbp"),  -- l.1998 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.1999 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2000 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.2001 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2002 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r11"),  -- l.2003 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.2004 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.2005 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.2006 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2007 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2008 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2009 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2010 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2011 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2012 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2013 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2014 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 0,  -- l.2015 `movq 0(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.2016 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2017 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2018 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 0,  -- l.2019 `movq 0(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.2020 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2021 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2022 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2023 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2024 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2025 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2026 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2027 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2028 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r9") ]  -- l.2029 `addq %r9, %rcx`

/-- Segment 65 of the body: the 32 instructions from source lines 2030–2061. -/
def ed25519ScMuladdShippedSeg065 : List (JInstr 64) :=
  [ .mov "%r10" (.reg "%rcx"),  -- l.2030 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.2031 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2032 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2033 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2034 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2035 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2036 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2037 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2038 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2039 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2040 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2041 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2042 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2043 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2044 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2045 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2046 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2047 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.2048 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2049 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.2050 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2051 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.2052 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.2053 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.2054 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.2055 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2056 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2057 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2058 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2059 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2060 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx") ]  -- l.2061 `movq %rcx, %rsi`

/-- Segment 66 of the body: the 32 instructions from source lines 2062–2093. -/
def ed25519ScMuladdShippedSeg066 : List (JInstr 64) :=
  [ .add "%rsi" (.reg "%rbx"),  -- l.2062 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2063 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 0,  -- l.2064 `movq 0(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.2065 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2066 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2067 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 0,  -- l.2068 `movq 0(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.2069 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2070 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2071 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2072 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2073 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2074 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2075 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2076 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2077 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.2078 `addq %r8, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.2079 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.2080 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2081 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2082 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2083 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2084 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2085 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2086 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2087 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2088 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2089 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2090 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2091 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2092 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63) ]  -- l.2093 `shrq $63, %rbx`

/-- Segment 67 of the body: the 32 instructions from source lines 2094–2125. -/
def ed25519ScMuladdShippedSeg067 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rdi"),  -- l.2094 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2095 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2096 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.2097 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2098 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.2099 `xorq %r8, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2100 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9"),  -- l.2101 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.2102 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.2103 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.2104 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2105 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2106 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2107 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2108 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2109 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2110 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2111 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2112 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 0,  -- l.2113 `movq 0(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.2114 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2115 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2116 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 0,  -- l.2117 `movq 0(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.2118 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2119 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2120 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2121 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2122 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2123 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2124 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx") ]  -- l.2125 `movq %rcx, %rbp`

/-- Segment 68 of the body: the 32 instructions from source lines 2126–2157. -/
def ed25519ScMuladdShippedSeg068 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rbp"),  -- l.2126 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.2127 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.2128 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.2129 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2130 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2131 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2132 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2133 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2134 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2135 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2136 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2137 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2138 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2139 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2140 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2141 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2142 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2143 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2144 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2145 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.2146 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2147 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2148 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.2149 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.2150 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.2151 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.2152 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.2153 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.2154 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2155 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.2156 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi") ]  -- l.2157 `movq %rsi, %rax`

/-- Segment 69 of the body: the 32 instructions from source lines 2158–2189. -/
def ed25519ScMuladdShippedSeg069 : List (JInstr 64) :=
  [ .shr "%rax" (.imm 63),  -- l.2158 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.2159 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.2160 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.2161 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 48,  -- l.2162 `movq 48(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8,  -- l.2163 `movq 8(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2164 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.2165 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 48,  -- l.2166 `movq 48(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.2167 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2168 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2169 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2170 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2171 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.2172 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.2173 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.2174 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.2175 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2176 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r11"),  -- l.2177 `addq %r11, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.2178 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0),  -- l.2179 `movq $0, %rdi`
    .mov "%r12" (.reg "%rcx"),  -- l.2180 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rdi"),  -- l.2181 `andq %rdi, %r12`
    .mov "%rdi" (.imm 0),  -- l.2182 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.2183 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.2184 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.2185 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2186 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2187 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.2188 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi") ]  -- l.2189 `andq %rdi, %rcx`

/-- Segment 70 of the body: the 32 instructions from source lines 2190–2221. -/
def ed25519ScMuladdShippedSeg070 : List (JInstr 64) :=
  [ .mov "%rdi" (.reg "%r12"),  -- l.2190 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2191 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.2192 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2193 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.2194 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.2195 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.2196 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.2197 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r11"),  -- l.2198 `andq %r11, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2199 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.2200 `xorq %r11, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2201 `movq $18446744073709551615, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.2202 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.2203 `xorq %rbx, %r11`
    .mov "%rbx" (.reg "%rsi"),  -- l.2204 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.2205 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2206 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2207 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2208 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2209 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2210 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2211 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2212 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.2213 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 48,  -- l.2214 `movq 48(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.2215 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2216 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2217 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 48,  -- l.2218 `movq 48(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.2219 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2220 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14") ]  -- l.2221 `mulx %r14, %rsi, %rcx`

/-- Segment 71 of the body: the 32 instructions from source lines 2222–2253. -/
def ed25519ScMuladdShippedSeg071 : List (JInstr 64) :=
  [ .loadMem "%rsi" "%rsp" (-128),  -- l.2222 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2223 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2224 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2225 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2226 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2227 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.2228 `addq %r10, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.2229 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.2230 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2231 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2232 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2233 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2234 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2235 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2236 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2237 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2238 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2239 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2240 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2241 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2242 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2243 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2244 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2245 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2246 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.2247 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2248 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.2249 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2250 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r11"),  -- l.2251 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.2252 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi") ]  -- l.2253 `movq %rsi, %rdi`

/-- Segment 72 of the body: the 32 instructions from source lines 2254–2285. -/
def ed25519ScMuladdShippedSeg072 : List (JInstr 64) :=
  [ .and_ "%rdi" (.reg "%rbp"),  -- l.2254 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2255 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2256 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2257 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2258 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2259 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2260 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2261 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2262 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 48,  -- l.2263 `movq 48(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.2264 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2265 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2266 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 48,  -- l.2267 `movq 48(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.2268 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2269 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2270 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2271 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2272 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2273 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2274 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2275 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2276 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.2277 `addq %r9, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.2278 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.2279 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2280 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2281 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2282 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2283 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2284 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx") ]  -- l.2285 `xorq %rbx, %rsi`

/-- Segment 73 of the body: the 32 instructions from source lines 2286–2317. -/
def ed25519ScMuladdShippedSeg073 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%r12"),  -- l.2286 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2287 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2288 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2289 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2290 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2291 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2292 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2293 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2294 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2295 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.2296 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2297 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.2298 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2299 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.2300 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.2301 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.2302 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.2303 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2304 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2305 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2306 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2307 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2308 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2309 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2310 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2311 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 48,  -- l.2312 `movq 48(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.2313 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2314 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2315 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 48,  -- l.2316 `movq 48(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32 ]  -- l.2317 `movq 32(%rsp), %r14`

/-- Segment 74 of the body: the 32 instructions from source lines 2318–2349. -/
def ed25519ScMuladdShippedSeg074 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2318 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2319 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2320 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2321 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2322 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2323 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2324 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2325 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.2326 `addq %r8, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.2327 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.2328 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2329 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2330 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2331 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2332 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2333 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2334 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2335 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2336 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2337 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2338 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2339 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2340 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2341 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2342 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2343 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2344 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.2345 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2346 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.2347 `xorq %r8, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2348 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9") ]  -- l.2349 `movq %r9, %rbp`

/-- Segment 75 of the body: the 32 instructions from source lines 2350–2381. -/
def ed25519ScMuladdShippedSeg075 : List (JInstr 64) :=
  [ .xor_ "%rbp" (.reg "%rdi"),  -- l.2350 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.2351 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.2352 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2353 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2354 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2355 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2356 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2357 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2358 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2359 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2360 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 48,  -- l.2361 `movq 48(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.2362 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2363 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2364 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 48,  -- l.2365 `movq 48(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.2366 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2367 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2368 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2369 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2370 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2371 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2372 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2373 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2374 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.2375 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.2376 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.2377 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2378 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2379 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2380 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615) ]  -- l.2381 `movq $18446744073709551615, %rbx`

/-- Segment 76 of the body: the 32 instructions from source lines 2382–2413. -/
def ed25519ScMuladdShippedSeg076 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rbp"),  -- l.2382 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2383 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2384 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2385 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2386 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2387 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2388 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2389 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2390 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2391 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2392 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2393 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.2394 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2395 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2396 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.2397 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.2398 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.2399 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.2400 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.2401 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.2402 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2403 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.2404 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.2405 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.2406 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.2407 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.2408 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.2409 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 56,  -- l.2410 `movq 56(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8,  -- l.2411 `movq 8(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2412 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx") ]  -- l.2413 `movq %rbx, %rcx`

/-- Segment 77 of the body: the 32 instructions from source lines 2414–2445. -/
def ed25519ScMuladdShippedSeg077 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsp" 56,  -- l.2414 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.2415 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2416 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2417 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2418 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2419 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.2420 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.2421 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.2422 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.2423 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2424 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r11"),  -- l.2425 `addq %r11, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.2426 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0),  -- l.2427 `movq $0, %rdi`
    .mov "%r12" (.reg "%rcx"),  -- l.2428 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rdi"),  -- l.2429 `andq %rdi, %r12`
    .mov "%rdi" (.imm 0),  -- l.2430 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.2431 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.2432 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.2433 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2434 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2435 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.2436 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.2437 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r12"),  -- l.2438 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2439 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.2440 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2441 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.2442 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.2443 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.2444 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx") ]  -- l.2445 `movq %rbx, %rcx`

/-- Segment 78 of the body: the 32 instructions from source lines 2446–2477. -/
def ed25519ScMuladdShippedSeg078 : List (JInstr 64) :=
  [ .and_ "%rcx" (.reg "%r11"),  -- l.2446 `andq %r11, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2447 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.2448 `xorq %r11, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2449 `movq $18446744073709551615, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.2450 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.2451 `xorq %rbx, %r11`
    .mov "%rbx" (.reg "%rsi"),  -- l.2452 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.2453 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2454 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2455 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2456 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2457 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2458 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2459 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2460 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.2461 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.2462 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.2463 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2464 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2465 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.2466 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.2467 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2468 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2469 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2470 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2471 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2472 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2473 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2474 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2475 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.2476 `addq %r10, %rcx`
    .mov "%r11" (.reg "%rcx") ]  -- l.2477 `movq %rcx, %r11`

/-- Segment 79 of the body: the 32 instructions from source lines 2478–2509. -/
def ed25519ScMuladdShippedSeg079 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rsi"),  -- l.2478 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2479 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2480 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2481 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2482 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2483 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2484 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2485 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2486 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2487 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2488 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2489 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2490 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2491 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2492 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2493 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2494 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.2495 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2496 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.2497 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2498 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r11"),  -- l.2499 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.2500 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.2501 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.2502 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2503 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2504 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2505 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2506 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2507 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2508 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx") ]  -- l.2509 `addq %rbx, %rsi`

/-- Segment 80 of the body: the 32 instructions from source lines 2510–2541. -/
def ed25519ScMuladdShippedSeg080 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%rsi"),  -- l.2510 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.2511 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.2512 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2513 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2514 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.2515 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.2516 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2517 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2518 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2519 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2520 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2521 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2522 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2523 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2524 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.2525 `addq %r9, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.2526 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.2527 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2528 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2529 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2530 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2531 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2532 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2533 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2534 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2535 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2536 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2537 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2538 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2539 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2540 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi") ]  -- l.2541 `movq %rdi, %rcx`

/-- Segment 81 of the body: the 32 instructions from source lines 2542–2573. -/
def ed25519ScMuladdShippedSeg081 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%rbx"),  -- l.2542 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2543 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.2544 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2545 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.2546 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2547 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.2548 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.2549 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.2550 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.2551 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2552 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2553 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2554 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2555 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2556 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2557 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2558 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2559 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.2560 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.2561 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2562 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2563 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.2564 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.2565 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2566 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2567 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2568 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2569 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2570 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2571 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2572 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp") ]  -- l.2573 `movq %rbp, %rcx`

/-- Segment 82 of the body: the 32 instructions from source lines 2574–2605. -/
def ed25519ScMuladdShippedSeg082 : List (JInstr 64) :=
  [ .add "%rcx" (.reg "%r8"),  -- l.2574 `addq %r8, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.2575 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.2576 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2577 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2578 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2579 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2580 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2581 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2582 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2583 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2584 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2585 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2586 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2587 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2588 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2589 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2590 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2591 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2592 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.2593 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2594 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.2595 `xorq %r8, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2596 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9"),  -- l.2597 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.2598 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.2599 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.2600 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2601 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2602 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2603 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2604 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63) ]  -- l.2605 `shrq $63, %rbx`

/-- Segment 83 of the body: the 32 instructions from source lines 2606–2637. -/
def ed25519ScMuladdShippedSeg083 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rcx"),  -- l.2606 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2607 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2608 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.2609 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.2610 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2611 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2612 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.2613 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 40,  -- l.2614 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2615 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2616 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2617 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2618 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2619 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2620 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2621 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2622 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.2623 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.2624 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.2625 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2626 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2627 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2628 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2629 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2630 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2631 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2632 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2633 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2634 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2635 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2636 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi") ]  -- l.2637 `movq %rsi, %rbx`

/-- Segment 84 of the body: the 32 instructions from source lines 2638–2669. -/
def ed25519ScMuladdShippedSeg084 : List (JInstr 64) :=
  [ .shr "%rbx" (.imm 63),  -- l.2638 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2639 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2640 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2641 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.2642 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2643 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2644 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.2645 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.2646 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.2647 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.2648 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.2649 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.2650 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2651 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.2652 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.2653 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.2654 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.2655 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.2656 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.2657 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 80,  -- l.2658 `movq 80(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 8,  -- l.2659 `movq 8(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2660 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.2661 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 80,  -- l.2662 `movq 80(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 8,  -- l.2663 `movq 8(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2664 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2665 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2666 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2667 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.2668 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx") ]  -- l.2669 `movq %rcx, %rdi`

/-- Segment 85 of the body: the 32 instructions from source lines 2670–2701. -/
def ed25519ScMuladdShippedSeg085 : List (JInstr 64) :=
  [ .add "%rdi" (.reg "%rbx"),  -- l.2670 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.2671 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2672 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r11"),  -- l.2673 `addq %r11, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.2674 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0),  -- l.2675 `movq $0, %rdi`
    .mov "%r12" (.reg "%rcx"),  -- l.2676 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rdi"),  -- l.2677 `andq %rdi, %r12`
    .mov "%rdi" (.imm 0),  -- l.2678 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.2679 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.2680 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.2681 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.2682 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2683 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.2684 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.2685 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r12"),  -- l.2686 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.2687 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.2688 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2689 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.2690 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.2691 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.2692 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.2693 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r11"),  -- l.2694 `andq %r11, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2695 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.2696 `xorq %r11, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2697 `movq $18446744073709551615, %rbx`
    .mov "%r11" (.reg "%rbp"),  -- l.2698 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.2699 `xorq %rbx, %r11`
    .mov "%rbx" (.reg "%rsi"),  -- l.2700 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r11") ]  -- l.2701 `andq %r11, %rbx`

/-- Segment 86 of the body: the 32 instructions from source lines 2702–2733. -/
def ed25519ScMuladdShippedSeg086 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rcx"),  -- l.2702 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2703 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2704 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2705 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2706 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2707 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2708 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.2709 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 80,  -- l.2710 `movq 80(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 16,  -- l.2711 `movq 16(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2712 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2713 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 80,  -- l.2714 `movq 80(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 16,  -- l.2715 `movq 16(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2716 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2717 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2718 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2719 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2720 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2721 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2722 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2723 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.2724 `addq %r10, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.2725 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.2726 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2727 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2728 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2729 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2730 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2731 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2732 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12") ]  -- l.2733 `movq %r12, %rbx`

/-- Segment 87 of the body: the 32 instructions from source lines 2734–2765. -/
def ed25519ScMuladdShippedSeg087 : List (JInstr 64) :=
  [ .and_ "%rbx" (.reg "%rsi"),  -- l.2734 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2735 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2736 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2737 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2738 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2739 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2740 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2741 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2742 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.2743 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2744 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.2745 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2746 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r11"),  -- l.2747 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.2748 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.2749 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.2750 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2751 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2752 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2753 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2754 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2755 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2756 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2757 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2758 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 80,  -- l.2759 `movq 80(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 24,  -- l.2760 `movq 24(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2761 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2762 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 80,  -- l.2763 `movq 80(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 24,  -- l.2764 `movq 24(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi") ]  -- l.2765 `movq %rsi, -128(%rsp)`

/-- Segment 88 of the body: the 32 instructions from source lines 2766–2797. -/
def ed25519ScMuladdShippedSeg088 : List (JInstr 64) :=
  [ .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2766 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2767 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2768 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2769 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2770 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2771 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2772 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.2773 `addq %r9, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.2774 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.2775 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2776 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2777 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2778 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2779 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2780 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2781 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2782 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2783 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2784 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2785 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2786 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2787 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2788 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2789 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2790 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2791 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.2792 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2793 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.2794 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2795 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.2796 `movq %r10, %rbp`
    .xor_ "%rbp" (.reg "%rdi") ]  -- l.2797 `xorq %rdi, %rbp`

/-- Segment 89 of the body: the 32 instructions from source lines 2798–2829. -/
def ed25519ScMuladdShippedSeg089 : List (JInstr 64) :=
  [ .mov "%rdi" (.reg "%rsi"),  -- l.2798 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.2799 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2800 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2801 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2802 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2803 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2804 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2805 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2806 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2807 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 80,  -- l.2808 `movq 80(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.2809 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2810 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2811 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 80,  -- l.2812 `movq 80(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.2813 `movq 32(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2814 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2815 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2816 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2817 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2818 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2819 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2820 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2821 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.2822 `addq %r8, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.2823 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.2824 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2825 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2826 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2827 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2828 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp") ]  -- l.2829 `movq %rbp, %rsi`

/-- Segment 90 of the body: the 32 instructions from source lines 2830–2861. -/
def ed25519ScMuladdShippedSeg090 : List (JInstr 64) :=
  [ .xor_ "%rsi" (.reg "%rbx"),  -- l.2830 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2831 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2832 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2833 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2834 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2835 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2836 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2837 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2838 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2839 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2840 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.2841 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2842 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.2843 `xorq %r8, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.2844 `movq $18446744073709551615, %rdi`
    .mov "%rbp" (.reg "%r9"),  -- l.2845 `movq %r9, %rbp`
    .xor_ "%rbp" (.reg "%rdi"),  -- l.2846 `xorq %rdi, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.2847 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%rbp"),  -- l.2848 `andq %rbp, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.2849 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.2850 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2851 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2852 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2853 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2854 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2855 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.2856 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 80,  -- l.2857 `movq 80(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 40,  -- l.2858 `movq 40(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2859 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2860 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 80 ]  -- l.2861 `movq 80(%rsp), %rdx`

/-- Segment 91 of the body: the 32 instructions from source lines 2862–2893. -/
def ed25519ScMuladdShippedSeg091 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 40,  -- l.2862 `movq 40(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2863 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2864 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2865 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.2866 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.2867 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2868 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.2869 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.2870 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.2871 `addq %rax, %rcx`
    .mov "%r15" (.reg "%rcx"),  -- l.2872 `movq %rcx, %r15`
    .storeMem "%rsp" 40 (.reg "%r15"),  -- l.2873 `movq %r15, 40(%rsp)`
    .mov "%rcx" (.reg "%rsi"),  -- l.2874 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.2875 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi"),  -- l.2876 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.2877 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2878 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2879 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2880 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.2881 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.2882 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2883 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2884 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2885 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2886 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2887 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.2888 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2889 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.2890 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.2891 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2892 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax") ]  -- l.2893 `xorq %rax, %rsi`

/-- Segment 92 of the body: the 32 instructions from source lines 2894–2925. -/
def ed25519ScMuladdShippedSeg092 : List (JInstr 64) :=
  [ .mov "%rax" (.imm 18446744073709551615),  -- l.2894 `movq $18446744073709551615, %rax`
    .loadMem "%rdi" "%rsp" 40,  -- l.2895 `movq 40(%rsp), %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.2896 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.2897 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.2898 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.2899 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.2900 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.2901 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.2902 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.2903 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.2904 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.2905 `addq %rax, %rbx`
    .mov "%r15" (.reg "%rbx"),  -- l.2906 `movq %rbx, %r15`
    .storeMem "%rsp" 56 (.reg "%r15"),  -- l.2907 `movq %r15, 56(%rsp)`
    .mov "%rbx" (.reg "%r11"),  -- l.2908 `movq %r11, %rbx`
    .loadMem "%r15" "%rsp" 128,  -- l.2909 `movq 128(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2910 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.2911 `movq %rbx, %rcx`
    .mov "%rdx" (.reg "%r11"),  -- l.2912 `movq %r11, %rdx`
    .loadMem "%r14" "%rsp" 128,  -- l.2913 `movq 128(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2914 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2915 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2916 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2917 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.2918 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.2919 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.2920 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.2921 `movq %rdi, %rbx`
    .mov "%rdi" (.imm 0),  -- l.2922 `movq $0, %rdi`
    .mov "%rbp" (.reg "%rbx"),  -- l.2923 `movq %rbx, %rbp`
    .add "%rbp" (.reg "%rdi"),  -- l.2924 `addq %rdi, %rbp`
    .mov "%r15" (.reg "%rbp") ]  -- l.2925 `movq %rbp, %r15`

/-- Segment 93 of the body: the 32 instructions from source lines 2926–2957. -/
def ed25519ScMuladdShippedSeg093 : List (JInstr 64) :=
  [ .storeMem "%rsp" 80 (.reg "%r15"),  -- l.2926 `movq %r15, 80(%rsp)`
    .mov "%rbp" (.imm 0),  -- l.2927 `movq $0, %rbp`
    .mov "%r12" (.reg "%rcx"),  -- l.2928 `movq %rcx, %r12`
    .and_ "%r12" (.reg "%rbp"),  -- l.2929 `andq %rbp, %r12`
    .mov "%rbp" (.imm 0),  -- l.2930 `movq $0, %rbp`
    .mov "%r13" (.reg "%rcx"),  -- l.2931 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rbp"),  -- l.2932 `xorq %rbp, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.2933 `movq $18446744073709551615, %rcx`
    .mov "%rbp" (.reg "%rbx"),  -- l.2934 `movq %rbx, %rbp`
    .xor_ "%rbp" (.reg "%rcx"),  -- l.2935 `xorq %rcx, %rbp`
    .mov "%rcx" (.reg "%r13"),  -- l.2936 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rbp"),  -- l.2937 `andq %rbp, %rcx`
    .mov "%rbp" (.reg "%r12"),  -- l.2938 `movq %r12, %rbp`
    .xor_ "%rbp" (.reg "%rcx"),  -- l.2939 `xorq %rcx, %rbp`
    .mov "%rcx" (.imm 63),  -- l.2940 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rbp"),  -- l.2941 `movq %rbp, %rcx`
    .shr "%rcx" (.imm 63),  -- l.2942 `shrq $63, %rcx`
    .mov "%rbp" (.reg "%rsi"),  -- l.2943 `movq %rsi, %rbp`
    .add "%rbp" (.reg "%rcx"),  -- l.2944 `addq %rcx, %rbp`
    .mov "%rcx" (.imm 0),  -- l.2945 `movq $0, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.2946 `movq %rbx, %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.2947 `andq %rcx, %rsi`
    .mov "%rcx" (.imm 0),  -- l.2948 `movq $0, %rcx`
    .mov "%r12" (.reg "%rbx"),  -- l.2949 `movq %rbx, %r12`
    .xor_ "%r12" (.reg "%rcx"),  -- l.2950 `xorq %rcx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2951 `movq $18446744073709551615, %rbx`
    .loadMem "%rcx" "%rsp" 80,  -- l.2952 `movq 80(%rsp), %rcx`
    .xor_ "%rcx" (.reg "%rbx"),  -- l.2953 `xorq %rbx, %rcx`
    .mov "%rbx" (.reg "%r12"),  -- l.2954 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rcx"),  -- l.2955 `andq %rcx, %rbx`
    .mov "%rcx" (.reg "%rsi"),  -- l.2956 `movq %rsi, %rcx`
    .xor_ "%rcx" (.reg "%rbx") ]  -- l.2957 `xorq %rbx, %rcx`

/-- Segment 94 of the body: the 32 instructions from source lines 2958–2989. -/
def ed25519ScMuladdShippedSeg094 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 63),  -- l.2958 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rcx"),  -- l.2959 `movq %rcx, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2960 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rbp"),  -- l.2961 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2962 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.2963 `movq %rcx, %rbx`
    .mov "%rcx" (.reg "%r11"),  -- l.2964 `movq %r11, %rcx`
    .loadMem "%r15" "%rsp" 120,  -- l.2965 `movq 120(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2966 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.2967 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r11"),  -- l.2968 `movq %r11, %rdx`
    .loadMem "%r14" "%rsp" 120,  -- l.2969 `movq 120(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.2970 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.2971 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.2972 `movq -128(%rsp), %rsi`
    .mov "%rbp" (.reg "%rcx"),  -- l.2973 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rsi"),  -- l.2974 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.2975 `addq %rbx, %rcx`
    .mov "%r12" (.reg "%rcx"),  -- l.2976 `movq %rcx, %r12`
    .mov "%rcx" (.imm 0),  -- l.2977 `movq $0, %rcx`
    .mov "%r13" (.reg "%r12"),  -- l.2978 `movq %r12, %r13`
    .add "%r13" (.reg "%rcx"),  -- l.2979 `addq %rcx, %r13`
    .mov "%rcx" (.reg "%r13"),  -- l.2980 `movq %r13, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.2981 `movq %rsi, %r13`
    .and_ "%r13" (.reg "%rbx"),  -- l.2982 `andq %rbx, %r13`
    .mov "%rdi" (.reg "%rsi"),  -- l.2983 `movq %rsi, %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.2984 `xorq %rbx, %rdi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.2985 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r12"),  -- l.2986 `movq %r12, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2987 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%rdi"),  -- l.2988 `movq %rdi, %rbx`
    .and_ "%rbx" (.reg "%rsi") ]  -- l.2989 `andq %rsi, %rbx`

/-- Segment 95 of the body: the 32 instructions from source lines 2990–3021. -/
def ed25519ScMuladdShippedSeg095 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%r13"),  -- l.2990 `movq %r13, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2991 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.2992 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.2993 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.2994 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.2995 `movq %rbp, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.2996 `addq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.2997 `movq $0, %rbx`
    .mov "%rdi" (.reg "%r12"),  -- l.2998 `movq %r12, %rdi`
    .and_ "%rdi" (.reg "%rbx"),  -- l.2999 `andq %rbx, %rdi`
    .mov "%rbx" (.imm 0),  -- l.3000 `movq $0, %rbx`
    .mov "%rbp" (.reg "%r12"),  -- l.3001 `movq %r12, %rbp`
    .xor_ "%rbp" (.reg "%rbx"),  -- l.3002 `xorq %rbx, %rbp`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3003 `movq $18446744073709551615, %rbx`
    .mov "%r12" (.reg "%rcx"),  -- l.3004 `movq %rcx, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.3005 `xorq %rbx, %r12`
    .mov "%rbx" (.reg "%rbp"),  -- l.3006 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r12"),  -- l.3007 `andq %r12, %rbx`
    .mov "%rbp" (.reg "%rdi"),  -- l.3008 `movq %rdi, %rbp`
    .xor_ "%rbp" (.reg "%rbx"),  -- l.3009 `xorq %rbx, %rbp`
    .mov "%rbx" (.imm 63),  -- l.3010 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rbp"),  -- l.3011 `movq %rbp, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3012 `shrq $63, %rbx`
    .mov "%rdi" (.reg "%rsi"),  -- l.3013 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.3014 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.3015 `movq %rdi, %rbx`
    .mov "%rsi" (.reg "%r11"),  -- l.3016 `movq %r11, %rsi`
    .loadMem "%r15" "%rsp" 112,  -- l.3017 `movq 112(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.3018 `imulq %r15, %rsi`
    .mov "%rdi" (.reg "%rsi"),  -- l.3019 `movq %rsi, %rdi`
    .mov "%rdx" (.reg "%r11"),  -- l.3020 `movq %r11, %rdx`
    .loadMem "%r14" "%rsp" 112 ]  -- l.3021 `movq 112(%rsp), %r14`

/-- Segment 96 of the body: the 32 instructions from source lines 3022–3053. -/
def ed25519ScMuladdShippedSeg096 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.3022 `movq %rcx, -128(%rsp)`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3023 `mulx %r14, %rcx, %rsi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.3024 `movq -128(%rsp), %rcx`
    .mov "%rbp" (.reg "%rsi"),  -- l.3025 `movq %rsi, %rbp`
    .mov "%rsi" (.reg "%rdi"),  -- l.3026 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3027 `addq %rbx, %rsi`
    .mov "%r12" (.reg "%rsi"),  -- l.3028 `movq %rsi, %r12`
    .mov "%rsi" (.imm 0),  -- l.3029 `movq $0, %rsi`
    .mov "%r13" (.reg "%r12"),  -- l.3030 `movq %r12, %r13`
    .add "%r13" (.reg "%rsi"),  -- l.3031 `addq %rsi, %r13`
    .mov "%rsi" (.reg "%r13"),  -- l.3032 `movq %r13, %rsi`
    .mov "%r13" (.reg "%rdi"),  -- l.3033 `movq %rdi, %r13`
    .and_ "%r13" (.reg "%rbx"),  -- l.3034 `andq %rbx, %r13`
    .mov "%rax" (.reg "%rdi"),  -- l.3035 `movq %rdi, %rax`
    .xor_ "%rax" (.reg "%rbx"),  -- l.3036 `xorq %rbx, %rax`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3037 `movq $18446744073709551615, %rbx`
    .mov "%rdi" (.reg "%r12"),  -- l.3038 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.3039 `xorq %rbx, %rdi`
    .mov "%rbx" (.reg "%rax"),  -- l.3040 `movq %rax, %rbx`
    .and_ "%rbx" (.reg "%rdi"),  -- l.3041 `andq %rdi, %rbx`
    .mov "%rax" (.reg "%r13"),  -- l.3042 `movq %r13, %rax`
    .xor_ "%rax" (.reg "%rbx"),  -- l.3043 `xorq %rbx, %rax`
    .mov "%rbx" (.imm 63),  -- l.3044 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rax"),  -- l.3045 `movq %rax, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3046 `shrq $63, %rbx`
    .mov "%rax" (.reg "%rbp"),  -- l.3047 `movq %rbp, %rax`
    .add "%rax" (.reg "%rbx"),  -- l.3048 `addq %rbx, %rax`
    .mov "%rbx" (.imm 0),  -- l.3049 `movq $0, %rbx`
    .mov "%rdi" (.reg "%r12"),  -- l.3050 `movq %r12, %rdi`
    .and_ "%rdi" (.reg "%rbx"),  -- l.3051 `andq %rbx, %rdi`
    .mov "%rbx" (.imm 0),  -- l.3052 `movq $0, %rbx`
    .mov "%rbp" (.reg "%r12") ]  -- l.3053 `movq %r12, %rbp`

/-- Segment 97 of the body: the 32 instructions from source lines 3054–3085. -/
def ed25519ScMuladdShippedSeg097 : List (JInstr 64) :=
  [ .xor_ "%rbp" (.reg "%rbx"),  -- l.3054 `xorq %rbx, %rbp`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3055 `movq $18446744073709551615, %rbx`
    .mov "%r12" (.reg "%rsi"),  -- l.3056 `movq %rsi, %r12`
    .xor_ "%r12" (.reg "%rbx"),  -- l.3057 `xorq %rbx, %r12`
    .mov "%rbx" (.reg "%rbp"),  -- l.3058 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%r12"),  -- l.3059 `andq %r12, %rbx`
    .mov "%rbp" (.reg "%rdi"),  -- l.3060 `movq %rdi, %rbp`
    .xor_ "%rbp" (.reg "%rbx"),  -- l.3061 `xorq %rbx, %rbp`
    .mov "%rbx" (.imm 63),  -- l.3062 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rbp"),  -- l.3063 `movq %rbp, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3064 `shrq $63, %rbx`
    .mov "%rdi" (.reg "%rax"),  -- l.3065 `movq %rax, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.3066 `addq %rbx, %rdi`
    .mov "%rax" (.reg "%rdi"),  -- l.3067 `movq %rdi, %rax`
    .mov "%rbx" (.reg "%r11"),  -- l.3068 `movq %r11, %rbx`
    .loadMem "%r15" "%rsp" 104,  -- l.3069 `movq 104(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.3070 `imulq %r15, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.3071 `movq %rbx, %rdi`
    .mov "%rdx" (.reg "%r11"),  -- l.3072 `movq %r11, %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.3073 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.3074 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3075 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.3076 `movq -128(%rsp), %rcx`
    .mov "%rbp" (.reg "%rbx"),  -- l.3077 `movq %rbx, %rbp`
    .mov "%rbx" (.reg "%rdi"),  -- l.3078 `movq %rdi, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.3079 `addq %rax, %rbx`
    .mov "%r11" (.reg "%rbx"),  -- l.3080 `movq %rbx, %r11`
    .mov "%rbx" (.imm 0),  -- l.3081 `movq $0, %rbx`
    .mov "%r12" (.reg "%r11"),  -- l.3082 `movq %r11, %r12`
    .add "%r12" (.reg "%rbx"),  -- l.3083 `addq %rbx, %r12`
    .mov "%rbx" (.reg "%r12"),  -- l.3084 `movq %r12, %rbx`
    .mov "%r12" (.reg "%rdi") ]  -- l.3085 `movq %rdi, %r12`

/-- Segment 98 of the body: the 32 instructions from source lines 3086–3117. -/
def ed25519ScMuladdShippedSeg098 : List (JInstr 64) :=
  [ .and_ "%r12" (.reg "%rax"),  -- l.3086 `andq %rax, %r12`
    .mov "%r13" (.reg "%rdi"),  -- l.3087 `movq %rdi, %r13`
    .xor_ "%r13" (.reg "%rax"),  -- l.3088 `xorq %rax, %r13`
    .mov "%rax" (.imm 18446744073709551615),  -- l.3089 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r11"),  -- l.3090 `movq %r11, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.3091 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%r13"),  -- l.3092 `movq %r13, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.3093 `andq %rdi, %rax`
    .mov "%rdi" (.reg "%r12"),  -- l.3094 `movq %r12, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.3095 `xorq %rax, %rdi`
    .mov "%rax" (.imm 63),  -- l.3096 `movq $63, %rax`
    .mov "%rax" (.reg "%rdi"),  -- l.3097 `movq %rdi, %rax`
    .shr "%rax" (.imm 63),  -- l.3098 `shrq $63, %rax`
    .mov "%rdi" (.reg "%rbp"),  -- l.3099 `movq %rbp, %rdi`
    .add "%rdi" (.reg "%rax"),  -- l.3100 `addq %rax, %rdi`
    .mov "%rax" (.imm 0),  -- l.3101 `movq $0, %rax`
    .mov "%rbp" (.reg "%r11"),  -- l.3102 `movq %r11, %rbp`
    .and_ "%rbp" (.reg "%rax"),  -- l.3103 `andq %rax, %rbp`
    .mov "%rax" (.imm 0),  -- l.3104 `movq $0, %rax`
    .mov "%r12" (.reg "%r11"),  -- l.3105 `movq %r11, %r12`
    .xor_ "%r12" (.reg "%rax"),  -- l.3106 `xorq %rax, %r12`
    .mov "%rax" (.imm 18446744073709551615),  -- l.3107 `movq $18446744073709551615, %rax`
    .mov "%r11" (.reg "%rbx"),  -- l.3108 `movq %rbx, %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.3109 `xorq %rax, %r11`
    .mov "%rax" (.reg "%r12"),  -- l.3110 `movq %r12, %rax`
    .and_ "%rax" (.reg "%r11"),  -- l.3111 `andq %r11, %rax`
    .mov "%r11" (.reg "%rbp"),  -- l.3112 `movq %rbp, %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.3113 `xorq %rax, %r11`
    .mov "%rax" (.imm 63),  -- l.3114 `movq $63, %rax`
    .mov "%rax" (.reg "%r11"),  -- l.3115 `movq %r11, %rax`
    .shr "%rax" (.imm 63),  -- l.3116 `shrq $63, %rax`
    .mov "%rbp" (.reg "%rdi") ]  -- l.3117 `movq %rdi, %rbp`

/-- Segment 99 of the body: the 32 instructions from source lines 3118–3149. -/
def ed25519ScMuladdShippedSeg099 : List (JInstr 64) :=
  [ .add "%rbp" (.reg "%rax"),  -- l.3118 `addq %rax, %rbp`
    .mov "%rax" (.reg "%rbp"),  -- l.3119 `movq %rbp, %rax`
    .mov "%rdi" (.reg "%r10"),  -- l.3120 `movq %r10, %rdi`
    .loadMem "%r15" "%rsp" 128,  -- l.3121 `movq 128(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.3122 `imulq %r15, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.3123 `movq %rdi, %rbp`
    .mov "%rdx" (.reg "%r10"),  -- l.3124 `movq %r10, %rdx`
    .loadMem "%r14" "%rsp" 128,  -- l.3125 `movq 128(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.3126 `movq %rcx, -128(%rsp)`
    .mulx "%rdi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3127 `mulx %r14, %rcx, %rdi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.3128 `movq -128(%rsp), %rcx`
    .mov "%r11" (.reg "%rdi"),  -- l.3129 `movq %rdi, %r11`
    .mov "%rdi" (.imm 0),  -- l.3130 `movq $0, %rdi`
    .mov "%r12" (.reg "%rbp"),  -- l.3131 `movq %rbp, %r12`
    .add "%r12" (.reg "%rdi"),  -- l.3132 `addq %rdi, %r12`
    .mov "%rdi" (.reg "%r12"),  -- l.3133 `movq %r12, %rdi`
    .mov "%r12" (.reg "%rdi"),  -- l.3134 `movq %rdi, %r12`
    .add "%r12" (.reg "%rcx"),  -- l.3135 `addq %rcx, %r12`
    .mov "%r15" (.reg "%r12"),  -- l.3136 `movq %r12, %r15`
    .storeMem "%rsp" 48 (.reg "%r15"),  -- l.3137 `movq %r15, 48(%rsp)`
    .mov "%r12" (.imm 0),  -- l.3138 `movq $0, %r12`
    .mov "%r13" (.reg "%rbp"),  -- l.3139 `movq %rbp, %r13`
    .and_ "%r13" (.reg "%r12"),  -- l.3140 `andq %r12, %r13`
    .mov "%r12" (.imm 0),  -- l.3141 `movq $0, %r12`
    .mov "%r8" (.reg "%rbp"),  -- l.3142 `movq %rbp, %r8`
    .xor_ "%r8" (.reg "%r12"),  -- l.3143 `xorq %r12, %r8`
    .mov "%rbp" (.imm 18446744073709551615),  -- l.3144 `movq $18446744073709551615, %rbp`
    .mov "%r12" (.reg "%rdi"),  -- l.3145 `movq %rdi, %r12`
    .xor_ "%r12" (.reg "%rbp"),  -- l.3146 `xorq %rbp, %r12`
    .mov "%rbp" (.reg "%r8"),  -- l.3147 `movq %r8, %rbp`
    .and_ "%rbp" (.reg "%r12"),  -- l.3148 `andq %r12, %rbp`
    .mov "%r8" (.reg "%r13") ]  -- l.3149 `movq %r13, %r8`

/-- Segment 100 of the body: the 32 instructions from source lines 3150–3181. -/
def ed25519ScMuladdShippedSeg100 : List (JInstr 64) :=
  [ .xor_ "%r8" (.reg "%rbp"),  -- l.3150 `xorq %rbp, %r8`
    .mov "%rbp" (.imm 63),  -- l.3151 `movq $63, %rbp`
    .mov "%rbp" (.reg "%r8"),  -- l.3152 `movq %r8, %rbp`
    .shr "%rbp" (.imm 63),  -- l.3153 `shrq $63, %rbp`
    .mov "%r8" (.reg "%r11"),  -- l.3154 `movq %r11, %r8`
    .add "%r8" (.reg "%rbp"),  -- l.3155 `addq %rbp, %r8`
    .mov "%rbp" (.reg "%rdi"),  -- l.3156 `movq %rdi, %rbp`
    .and_ "%rbp" (.reg "%rcx"),  -- l.3157 `andq %rcx, %rbp`
    .mov "%r11" (.reg "%rdi"),  -- l.3158 `movq %rdi, %r11`
    .xor_ "%r11" (.reg "%rcx"),  -- l.3159 `xorq %rcx, %r11`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3160 `movq $18446744073709551615, %rcx`
    .loadMem "%rdi" "%rsp" 48,  -- l.3161 `movq 48(%rsp), %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.3162 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r11"),  -- l.3163 `movq %r11, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.3164 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%rbp"),  -- l.3165 `movq %rbp, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.3166 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.3167 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3168 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3169 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%r8"),  -- l.3170 `movq %r8, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.3171 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rdi"),  -- l.3172 `movq %rdi, %rcx`
    .mov "%rdi" (.reg "%r10"),  -- l.3173 `movq %r10, %rdi`
    .loadMem "%r15" "%rsp" 120,  -- l.3174 `movq 120(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.3175 `imulq %r15, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.3176 `movq %rdi, %rbp`
    .mov "%rdx" (.reg "%r10"),  -- l.3177 `movq %r10, %rdx`
    .loadMem "%r14" "%rsp" 120,  -- l.3178 `movq 120(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.3179 `movq %rcx, -128(%rsp)`
    .mulx "%rdi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3180 `mulx %r14, %rcx, %rdi`
    .loadMem "%rcx" "%rsp" (-128) ]  -- l.3181 `movq -128(%rsp), %rcx`

/-- Segment 101 of the body: the 32 instructions from source lines 3182–3213. -/
def ed25519ScMuladdShippedSeg101 : List (JInstr 64) :=
  [ .mov "%r8" (.reg "%rdi"),  -- l.3182 `movq %rdi, %r8`
    .mov "%rdi" (.reg "%rbp"),  -- l.3183 `movq %rbp, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.3184 `addq %rcx, %rdi`
    .mov "%r11" (.reg "%rdi"),  -- l.3185 `movq %rdi, %r11`
    .mov "%rdi" (.reg "%r11"),  -- l.3186 `movq %r11, %rdi`
    .add "%rdi" (.reg "%rsi"),  -- l.3187 `addq %rsi, %rdi`
    .mov "%r12" (.reg "%rdi"),  -- l.3188 `movq %rdi, %r12`
    .mov "%rdi" (.reg "%rbp"),  -- l.3189 `movq %rbp, %rdi`
    .and_ "%rdi" (.reg "%rcx"),  -- l.3190 `andq %rcx, %rdi`
    .mov "%r13" (.reg "%rbp"),  -- l.3191 `movq %rbp, %r13`
    .xor_ "%r13" (.reg "%rcx"),  -- l.3192 `xorq %rcx, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3193 `movq $18446744073709551615, %rcx`
    .mov "%rbp" (.reg "%r11"),  -- l.3194 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rcx"),  -- l.3195 `xorq %rcx, %rbp`
    .mov "%rcx" (.reg "%r13"),  -- l.3196 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rbp"),  -- l.3197 `andq %rbp, %rcx`
    .mov "%rbp" (.reg "%rdi"),  -- l.3198 `movq %rdi, %rbp`
    .xor_ "%rbp" (.reg "%rcx"),  -- l.3199 `xorq %rcx, %rbp`
    .mov "%rcx" (.imm 63),  -- l.3200 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rbp"),  -- l.3201 `movq %rbp, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3202 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%r8"),  -- l.3203 `movq %r8, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.3204 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%r11"),  -- l.3205 `movq %r11, %rcx`
    .and_ "%rcx" (.reg "%rsi"),  -- l.3206 `andq %rsi, %rcx`
    .mov "%rbp" (.reg "%r11"),  -- l.3207 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rsi"),  -- l.3208 `xorq %rsi, %rbp`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.3209 `movq $18446744073709551615, %rsi`
    .mov "%r8" (.reg "%r12"),  -- l.3210 `movq %r12, %r8`
    .xor_ "%r8" (.reg "%rsi"),  -- l.3211 `xorq %rsi, %r8`
    .mov "%rsi" (.reg "%rbp"),  -- l.3212 `movq %rbp, %rsi`
    .and_ "%rsi" (.reg "%r8") ]  -- l.3213 `andq %r8, %rsi`

/-- Segment 102 of the body: the 32 instructions from source lines 3214–3245. -/
def ed25519ScMuladdShippedSeg102 : List (JInstr 64) :=
  [ .mov "%rbp" (.reg "%rcx"),  -- l.3214 `movq %rcx, %rbp`
    .xor_ "%rbp" (.reg "%rsi"),  -- l.3215 `xorq %rsi, %rbp`
    .mov "%rcx" (.imm 63),  -- l.3216 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rbp"),  -- l.3217 `movq %rbp, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3218 `shrq $63, %rcx`
    .mov "%rsi" (.reg "%rdi"),  -- l.3219 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.3220 `addq %rcx, %rsi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3221 `movq %rsi, %rcx`
    .mov "%rsi" (.reg "%r10"),  -- l.3222 `movq %r10, %rsi`
    .loadMem "%r15" "%rsp" 112,  -- l.3223 `movq 112(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.3224 `imulq %r15, %rsi`
    .mov "%rdi" (.reg "%rsi"),  -- l.3225 `movq %rsi, %rdi`
    .mov "%rdx" (.reg "%r10"),  -- l.3226 `movq %r10, %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.3227 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.3228 `movq %rcx, -128(%rsp)`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3229 `mulx %r14, %rcx, %rsi`
    .loadMem "%rcx" "%rsp" (-128),  -- l.3230 `movq -128(%rsp), %rcx`
    .mov "%rbp" (.reg "%rsi"),  -- l.3231 `movq %rsi, %rbp`
    .mov "%rsi" (.reg "%rdi"),  -- l.3232 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.3233 `addq %rcx, %rsi`
    .mov "%r8" (.reg "%rsi"),  -- l.3234 `movq %rsi, %r8`
    .mov "%rsi" (.reg "%r8"),  -- l.3235 `movq %r8, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3236 `addq %rbx, %rsi`
    .mov "%r11" (.reg "%rsi"),  -- l.3237 `movq %rsi, %r11`
    .mov "%rsi" (.reg "%rdi"),  -- l.3238 `movq %rdi, %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.3239 `andq %rcx, %rsi`
    .mov "%r13" (.reg "%rdi"),  -- l.3240 `movq %rdi, %r13`
    .xor_ "%r13" (.reg "%rcx"),  -- l.3241 `xorq %rcx, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3242 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%r8"),  -- l.3243 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.3244 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13") ]  -- l.3245 `movq %r13, %rcx`

/-- Segment 103 of the body: the 32 instructions from source lines 3246–3277. -/
def ed25519ScMuladdShippedSeg103 : List (JInstr 64) :=
  [ .and_ "%rcx" (.reg "%rdi"),  -- l.3246 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.3247 `movq %rsi, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.3248 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.3249 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3250 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3251 `shrq $63, %rcx`
    .mov "%rsi" (.reg "%rbp"),  -- l.3252 `movq %rbp, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.3253 `addq %rcx, %rsi`
    .mov "%rcx" (.reg "%r8"),  -- l.3254 `movq %r8, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.3255 `andq %rbx, %rcx`
    .mov "%rdi" (.reg "%r8"),  -- l.3256 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.3257 `xorq %rbx, %rdi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3258 `movq $18446744073709551615, %rbx`
    .mov "%rbp" (.reg "%r11"),  -- l.3259 `movq %r11, %rbp`
    .xor_ "%rbp" (.reg "%rbx"),  -- l.3260 `xorq %rbx, %rbp`
    .mov "%rbx" (.reg "%rdi"),  -- l.3261 `movq %rdi, %rbx`
    .and_ "%rbx" (.reg "%rbp"),  -- l.3262 `andq %rbp, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.3263 `movq %rcx, %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.3264 `xorq %rbx, %rdi`
    .mov "%rbx" (.imm 63),  -- l.3265 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rdi"),  -- l.3266 `movq %rdi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3267 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rsi"),  -- l.3268 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3269 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.3270 `movq %rcx, %rbx`
    .mov "%rcx" (.reg "%r10"),  -- l.3271 `movq %r10, %rcx`
    .loadMem "%r15" "%rsp" 104,  -- l.3272 `movq 104(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3273 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3274 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r10"),  -- l.3275 `movq %r10, %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.3276 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi") ]  -- l.3277 `movq %rsi, -128(%rsp)`

/-- Segment 104 of the body: the 32 instructions from source lines 3278–3309. -/
def ed25519ScMuladdShippedSeg104 : List (JInstr 64) :=
  [ .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3278 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.3279 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.3280 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3281 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3282 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.3283 `movq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.3284 `movq %rbp, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.3285 `addq %rax, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.3286 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.3287 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.3288 `andq %rbx, %rcx`
    .mov "%r10" (.reg "%rsi"),  -- l.3289 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.3290 `xorq %rbx, %r10`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3291 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.3292 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3293 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r10"),  -- l.3294 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3295 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3296 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3297 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3298 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3299 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3300 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3301 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3302 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rbp"),  -- l.3303 `movq %rbp, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.3304 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.3305 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.3306 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.3307 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r8"),  -- l.3308 `movq %r8, %rdi`
    .xor_ "%rdi" (.reg "%rax") ]  -- l.3309 `xorq %rax, %rdi`

/-- Segment 105 of the body: the 32 instructions from source lines 3310–3341. -/
def ed25519ScMuladdShippedSeg105 : List (JInstr 64) :=
  [ .mov "%rax" (.reg "%rsi"),  -- l.3310 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.3311 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.3312 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.3313 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.3314 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.3315 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.3316 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.3317 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.3318 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.3319 `movq %rbx, %rax`
    .mov "%rbx" (.reg "%r9"),  -- l.3320 `movq %r9, %rbx`
    .loadMem "%r15" "%rsp" 128,  -- l.3321 `movq 128(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.3322 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.3323 `movq %rbx, %rcx`
    .mov "%rdx" (.reg "%r9"),  -- l.3324 `movq %r9, %rdx`
    .loadMem "%r14" "%rsp" 128,  -- l.3325 `movq 128(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.3326 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3327 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.3328 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.3329 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.3330 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.3331 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.3332 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.3333 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.3334 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r12"),  -- l.3335 `addq %r12, %rdi`
    .mov "%rbp" (.reg "%rdi"),  -- l.3336 `movq %rdi, %rbp`
    .mov "%rdi" (.imm 0),  -- l.3337 `movq $0, %rdi`
    .mov "%r10" (.reg "%rcx"),  -- l.3338 `movq %rcx, %r10`
    .and_ "%r10" (.reg "%rdi"),  -- l.3339 `andq %rdi, %r10`
    .mov "%rdi" (.imm 0),  -- l.3340 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx") ]  -- l.3341 `movq %rcx, %r13`

/-- Segment 106 of the body: the 32 instructions from source lines 3342–3373. -/
def ed25519ScMuladdShippedSeg106 : List (JInstr 64) :=
  [ .xor_ "%r13" (.reg "%rdi"),  -- l.3342 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3343 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.3344 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.3345 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.3346 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.3347 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r10"),  -- l.3348 `movq %r10, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.3349 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.3350 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3351 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3352 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.3353 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.3354 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.3355 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r12"),  -- l.3356 `andq %r12, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.3357 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r12"),  -- l.3358 `xorq %r12, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3359 `movq $18446744073709551615, %rbx`
    .mov "%r10" (.reg "%rbp"),  -- l.3360 `movq %rbp, %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.3361 `xorq %rbx, %r10`
    .mov "%rbx" (.reg "%rsi"),  -- l.3362 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.3363 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3364 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3365 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3366 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3367 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3368 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3369 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3370 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.3371 `movq %rcx, %rbx`
    .mov "%rcx" (.reg "%r9"),  -- l.3372 `movq %r9, %rcx`
    .loadMem "%r15" "%rsp" 120 ]  -- l.3373 `movq 120(%rsp), %r15`

/-- Segment 107 of the body: the 32 instructions from source lines 3374–3405. -/
def ed25519ScMuladdShippedSeg107 : List (JInstr 64) :=
  [ .imul "%rcx" (.reg "%r15"),  -- l.3374 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3375 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r9"),  -- l.3376 `movq %r9, %rdx`
    .loadMem "%r14" "%rsp" 120,  -- l.3377 `movq 120(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.3378 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3379 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.3380 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.3381 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3382 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3383 `addq %rbx, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.3384 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%r10"),  -- l.3385 `movq %r10, %rcx`
    .add "%rcx" (.reg "%r11"),  -- l.3386 `addq %r11, %rcx`
    .mov "%r12" (.reg "%rcx"),  -- l.3387 `movq %rcx, %r12`
    .mov "%rcx" (.reg "%rsi"),  -- l.3388 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.3389 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.3390 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.3391 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3392 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.3393 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3394 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.3395 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3396 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3397 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3398 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3399 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3400 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3401 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3402 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3403 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r10"),  -- l.3404 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%r11") ]  -- l.3405 `andq %r11, %rbx`

/-- Segment 108 of the body: the 32 instructions from source lines 3406–3437. -/
def ed25519ScMuladdShippedSeg108 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%r10"),  -- l.3406 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.3407 `xorq %r11, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.3408 `movq $18446744073709551615, %rdi`
    .mov "%r10" (.reg "%r12"),  -- l.3409 `movq %r12, %r10`
    .xor_ "%r10" (.reg "%rdi"),  -- l.3410 `xorq %rdi, %r10`
    .mov "%rdi" (.reg "%rsi"),  -- l.3411 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r10"),  -- l.3412 `andq %r10, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.3413 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.3414 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3415 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3416 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3417 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3418 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3419 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.3420 `movq %rsi, %rbx`
    .mov "%rcx" (.reg "%r9"),  -- l.3421 `movq %r9, %rcx`
    .loadMem "%r15" "%rsp" 112,  -- l.3422 `movq 112(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3423 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3424 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r9"),  -- l.3425 `movq %r9, %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.3426 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.3427 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3428 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.3429 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.3430 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3431 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3432 `addq %rbx, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.3433 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%r10"),  -- l.3434 `movq %r10, %rcx`
    .add "%rcx" (.reg "%r8"),  -- l.3435 `addq %r8, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.3436 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi") ]  -- l.3437 `movq %rsi, %rcx`

/-- Segment 109 of the body: the 32 instructions from source lines 3438–3469. -/
def ed25519ScMuladdShippedSeg109 : List (JInstr 64) :=
  [ .and_ "%rcx" (.reg "%rbx"),  -- l.3438 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.3439 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.3440 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3441 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.3442 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3443 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.3444 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3445 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3446 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3447 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3448 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3449 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3450 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3451 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3452 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r10"),  -- l.3453 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.3454 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.3455 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%r8"),  -- l.3456 `xorq %r8, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.3457 `movq $18446744073709551615, %rdi`
    .mov "%r8" (.reg "%r11"),  -- l.3458 `movq %r11, %r8`
    .xor_ "%r8" (.reg "%rdi"),  -- l.3459 `xorq %rdi, %r8`
    .mov "%rdi" (.reg "%rsi"),  -- l.3460 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r8"),  -- l.3461 `andq %r8, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.3462 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.3463 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3464 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3465 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3466 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3467 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3468 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi") ]  -- l.3469 `movq %rsi, %rbx`

/-- Segment 110 of the body: the 32 instructions from source lines 3470–3501. -/
def ed25519ScMuladdShippedSeg110 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%r9"),  -- l.3470 `movq %r9, %rcx`
    .loadMem "%r15" "%rsp" 104,  -- l.3471 `movq 104(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3472 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3473 `movq %rcx, %rsi`
    .mov "%rdx" (.reg "%r9"),  -- l.3474 `movq %r9, %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.3475 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.3476 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3477 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.3478 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.3479 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3480 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3481 `addq %rbx, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.3482 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%r8"),  -- l.3483 `movq %r8, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.3484 `addq %rax, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.3485 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.3486 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.3487 `andq %rbx, %rcx`
    .mov "%r10" (.reg "%rsi"),  -- l.3488 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.3489 `xorq %rbx, %r10`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3490 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3491 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3492 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r10"),  -- l.3493 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3494 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3495 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3496 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3497 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3498 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3499 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3500 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx") ]  -- l.3501 `addq %rbx, %rcx`

/-- Segment 111 of the body: the 32 instructions from source lines 3502–3533. -/
def ed25519ScMuladdShippedSeg111 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%r8"),  -- l.3502 `movq %r8, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.3503 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3504 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.3505 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.3506 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r9"),  -- l.3507 `movq %r9, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.3508 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.3509 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.3510 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.3511 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.3512 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.3513 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.3514 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.3515 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.3516 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.3517 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.3518 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 40,  -- l.3519 `movq 40(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 128,  -- l.3520 `movq 128(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.3521 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.3522 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 40,  -- l.3523 `movq 40(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 128,  -- l.3524 `movq 128(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.3525 `movq %rcx, -128(%rsp)`
    .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3526 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.3527 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.3528 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.3529 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.3530 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.3531 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.3532 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx") ]  -- l.3533 `movq %rbx, %rdi`

/-- Segment 112 of the body: the 32 instructions from source lines 3534–3565. -/
def ed25519ScMuladdShippedSeg112 : List (JInstr 64) :=
  [ .add "%rdi" (.reg "%r12"),  -- l.3534 `addq %r12, %rdi`
    .mov "%r15" (.reg "%rdi"),  -- l.3535 `movq %rdi, %r15`
    .storeMem "%rsp" 32 (.reg "%r15"),  -- l.3536 `movq %r15, 32(%rsp)`
    .mov "%rdi" (.imm 0),  -- l.3537 `movq $0, %rdi`
    .mov "%r10" (.reg "%rcx"),  -- l.3538 `movq %rcx, %r10`
    .and_ "%r10" (.reg "%rdi"),  -- l.3539 `andq %rdi, %r10`
    .mov "%rdi" (.imm 0),  -- l.3540 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.3541 `movq %rcx, %r13`
    .xor_ "%r13" (.reg "%rdi"),  -- l.3542 `xorq %rdi, %r13`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3543 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.3544 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.3545 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r13"),  -- l.3546 `movq %r13, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.3547 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r10"),  -- l.3548 `movq %r10, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.3549 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.3550 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3551 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3552 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.3553 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.3554 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.3555 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r12"),  -- l.3556 `andq %r12, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.3557 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r12"),  -- l.3558 `xorq %r12, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3559 `movq $18446744073709551615, %rbx`
    .loadMem "%r10" "%rsp" 32,  -- l.3560 `movq 32(%rsp), %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.3561 `xorq %rbx, %r10`
    .mov "%rbx" (.reg "%rsi"),  -- l.3562 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r10"),  -- l.3563 `andq %r10, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3564 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx") ]  -- l.3565 `xorq %rbx, %rsi`

/-- Segment 113 of the body: the 32 instructions from source lines 3566–3597. -/
def ed25519ScMuladdShippedSeg113 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 63),  -- l.3566 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3567 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3568 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3569 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3570 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.3571 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 40,  -- l.3572 `movq 40(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 120,  -- l.3573 `movq 120(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3574 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3575 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 40,  -- l.3576 `movq 40(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 120,  -- l.3577 `movq 120(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.3578 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3579 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.3580 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.3581 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3582 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3583 `addq %rbx, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.3584 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%r10"),  -- l.3585 `movq %r10, %rcx`
    .add "%rcx" (.reg "%r11"),  -- l.3586 `addq %r11, %rcx`
    .mov "%r12" (.reg "%rcx"),  -- l.3587 `movq %rcx, %r12`
    .mov "%rcx" (.reg "%rsi"),  -- l.3588 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.3589 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.3590 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.3591 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3592 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.3593 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3594 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.3595 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3596 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx") ]  -- l.3597 `movq %rcx, %rsi`

/-- Segment 114 of the body: the 32 instructions from source lines 3598–3629. -/
def ed25519ScMuladdShippedSeg114 : List (JInstr 64) :=
  [ .xor_ "%rsi" (.reg "%rbx"),  -- l.3598 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3599 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3600 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3601 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3602 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3603 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r10"),  -- l.3604 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.3605 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.3606 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.3607 `xorq %r11, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.3608 `movq $18446744073709551615, %rdi`
    .mov "%r10" (.reg "%r12"),  -- l.3609 `movq %r12, %r10`
    .xor_ "%r10" (.reg "%rdi"),  -- l.3610 `xorq %rdi, %r10`
    .mov "%rdi" (.reg "%rsi"),  -- l.3611 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r10"),  -- l.3612 `andq %r10, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.3613 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.3614 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3615 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3616 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3617 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3618 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3619 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.3620 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 40,  -- l.3621 `movq 40(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 112,  -- l.3622 `movq 112(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3623 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3624 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 40,  -- l.3625 `movq 40(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.3626 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.3627 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3628 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128) ]  -- l.3629 `movq -128(%rsp), %rsi`

/-- Segment 115 of the body: the 32 instructions from source lines 3630–3661. -/
def ed25519ScMuladdShippedSeg115 : List (JInstr 64) :=
  [ .mov "%rdi" (.reg "%rcx"),  -- l.3630 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3631 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3632 `addq %rbx, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.3633 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%r10"),  -- l.3634 `movq %r10, %rcx`
    .add "%rcx" (.reg "%r9"),  -- l.3635 `addq %r9, %rcx`
    .mov "%r11" (.reg "%rcx"),  -- l.3636 `movq %rcx, %r11`
    .mov "%rcx" (.reg "%rsi"),  -- l.3637 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.3638 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.3639 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.3640 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3641 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.3642 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3643 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13"),  -- l.3644 `movq %r13, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3645 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3646 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3647 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3648 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3649 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3650 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3651 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3652 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r10"),  -- l.3653 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.3654 `andq %r9, %rbx`
    .mov "%rsi" (.reg "%r10"),  -- l.3655 `movq %r10, %rsi`
    .xor_ "%rsi" (.reg "%r9"),  -- l.3656 `xorq %r9, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.3657 `movq $18446744073709551615, %rdi`
    .mov "%r9" (.reg "%r11"),  -- l.3658 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rdi"),  -- l.3659 `xorq %rdi, %r9`
    .mov "%rdi" (.reg "%rsi"),  -- l.3660 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r9") ]  -- l.3661 `andq %r9, %rdi`

/-- Segment 116 of the body: the 32 instructions from source lines 3662–3693. -/
def ed25519ScMuladdShippedSeg116 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rbx"),  -- l.3662 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.3663 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3664 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3665 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3666 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3667 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3668 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.3669 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 40,  -- l.3670 `movq 40(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 104,  -- l.3671 `movq 104(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3672 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3673 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 40,  -- l.3674 `movq 40(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.3675 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.3676 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3677 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.3678 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.3679 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3680 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3681 `addq %rbx, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.3682 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.3683 `movq %r9, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.3684 `addq %rax, %rcx`
    .mov "%r10" (.reg "%rcx"),  -- l.3685 `movq %rcx, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.3686 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.3687 `andq %rbx, %rcx`
    .mov "%r13" (.reg "%rsi"),  -- l.3688 `movq %rsi, %r13`
    .xor_ "%r13" (.reg "%rbx"),  -- l.3689 `xorq %rbx, %r13`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3690 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.3691 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3692 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r13") ]  -- l.3693 `movq %r13, %rbx`

/-- Segment 117 of the body: the 32 instructions from source lines 3694–3725. -/
def ed25519ScMuladdShippedSeg117 : List (JInstr 64) :=
  [ .and_ "%rbx" (.reg "%rsi"),  -- l.3694 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3695 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3696 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3697 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3698 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3699 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3700 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3701 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r9"),  -- l.3702 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.3703 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.3704 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.3705 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.3706 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r10"),  -- l.3707 `movq %r10, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.3708 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.3709 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.3710 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.3711 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.3712 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.3713 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.3714 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.3715 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.3716 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.3717 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx"),  -- l.3718 `movq %rbx, %rax`
    .loadMem "%rbx" "%rsp" 56,  -- l.3719 `movq 56(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 128,  -- l.3720 `movq 128(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.3721 `imulq %r15, %rbx`
    .mov "%rcx" (.reg "%rbx"),  -- l.3722 `movq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 56,  -- l.3723 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 128,  -- l.3724 `movq 128(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rcx") ]  -- l.3725 `movq %rcx, -128(%rsp)`

/-- Segment 118 of the body: the 32 instructions from source lines 3726–3757. -/
def ed25519ScMuladdShippedSeg118 : List (JInstr 64) :=
  [ .mulx "%rbx" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3726 `mulx %r14, %rcx, %rbx`
    .loadMem "%rcx" "%rsp" (-128),  -- l.3727 `movq -128(%rsp), %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.3728 `movq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.3729 `movq $0, %rbx`
    .mov "%rdi" (.reg "%rcx"),  -- l.3730 `movq %rcx, %rdi`
    .add "%rdi" (.reg "%rbx"),  -- l.3731 `addq %rbx, %rdi`
    .mov "%rbx" (.reg "%rdi"),  -- l.3732 `movq %rdi, %rbx`
    .mov "%rdi" (.reg "%rbx"),  -- l.3733 `movq %rbx, %rdi`
    .add "%rdi" (.reg "%r12"),  -- l.3734 `addq %r12, %rdi`
    .mov "%r9" (.reg "%rdi"),  -- l.3735 `movq %rdi, %r9`
    .mov "%rdi" (.imm 0),  -- l.3736 `movq $0, %rdi`
    .mov "%r13" (.reg "%rcx"),  -- l.3737 `movq %rcx, %r13`
    .and_ "%r13" (.reg "%rdi"),  -- l.3738 `andq %rdi, %r13`
    .mov "%rdi" (.imm 0),  -- l.3739 `movq $0, %rdi`
    .mov "%r8" (.reg "%rcx"),  -- l.3740 `movq %rcx, %r8`
    .xor_ "%r8" (.reg "%rdi"),  -- l.3741 `xorq %rdi, %r8`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3742 `movq $18446744073709551615, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.3743 `movq %rbx, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.3744 `xorq %rcx, %rdi`
    .mov "%rcx" (.reg "%r8"),  -- l.3745 `movq %r8, %rcx`
    .and_ "%rcx" (.reg "%rdi"),  -- l.3746 `andq %rdi, %rcx`
    .mov "%rdi" (.reg "%r13"),  -- l.3747 `movq %r13, %rdi`
    .xor_ "%rdi" (.reg "%rcx"),  -- l.3748 `xorq %rcx, %rdi`
    .mov "%rcx" (.imm 63),  -- l.3749 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3750 `movq %rdi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3751 `shrq $63, %rcx`
    .mov "%rdi" (.reg "%rsi"),  -- l.3752 `movq %rsi, %rdi`
    .add "%rdi" (.reg "%rcx"),  -- l.3753 `addq %rcx, %rdi`
    .mov "%rcx" (.reg "%rbx"),  -- l.3754 `movq %rbx, %rcx`
    .and_ "%rcx" (.reg "%r12"),  -- l.3755 `andq %r12, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.3756 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%r12") ]  -- l.3757 `xorq %r12, %rsi`

/-- Segment 119 of the body: the 32 instructions from source lines 3758–3789. -/
def ed25519ScMuladdShippedSeg119 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 18446744073709551615),  -- l.3758 `movq $18446744073709551615, %rbx`
    .mov "%r8" (.reg "%r9"),  -- l.3759 `movq %r9, %r8`
    .xor_ "%r8" (.reg "%rbx"),  -- l.3760 `xorq %rbx, %r8`
    .mov "%rbx" (.reg "%rsi"),  -- l.3761 `movq %rsi, %rbx`
    .and_ "%rbx" (.reg "%r8"),  -- l.3762 `andq %r8, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3763 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3764 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3765 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3766 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3767 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3768 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3769 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%rcx"),  -- l.3770 `movq %rcx, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.3771 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 120,  -- l.3772 `movq 120(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3773 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3774 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.3775 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 120,  -- l.3776 `movq 120(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.3777 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3778 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.3779 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.3780 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3781 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3782 `addq %rbx, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.3783 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%r8"),  -- l.3784 `movq %r8, %rcx`
    .add "%rcx" (.reg "%r11"),  -- l.3785 `addq %r11, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.3786 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.3787 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.3788 `andq %rbx, %rcx`
    .mov "%r12" (.reg "%rsi") ]  -- l.3789 `movq %rsi, %r12`

/-- Segment 120 of the body: the 32 instructions from source lines 3790–3821. -/
def ed25519ScMuladdShippedSeg120 : List (JInstr 64) :=
  [ .xor_ "%r12" (.reg "%rbx"),  -- l.3790 `xorq %rbx, %r12`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3791 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3792 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3793 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r12"),  -- l.3794 `movq %r12, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3795 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3796 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3797 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3798 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3799 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3800 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3801 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3802 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r8"),  -- l.3803 `movq %r8, %rbx`
    .and_ "%rbx" (.reg "%r11"),  -- l.3804 `andq %r11, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3805 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%r11"),  -- l.3806 `xorq %r11, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.3807 `movq $18446744073709551615, %rdi`
    .mov "%r8" (.reg "%r9"),  -- l.3808 `movq %r9, %r8`
    .xor_ "%r8" (.reg "%rdi"),  -- l.3809 `xorq %rdi, %r8`
    .mov "%rdi" (.reg "%rsi"),  -- l.3810 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r8"),  -- l.3811 `andq %r8, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.3812 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.3813 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3814 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3815 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3816 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3817 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3818 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.3819 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.3820 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 112 ]  -- l.3821 `movq 112(%rsp), %r15`

/-- Segment 121 of the body: the 32 instructions from source lines 3822–3853. -/
def ed25519ScMuladdShippedSeg121 : List (JInstr 64) :=
  [ .imul "%rcx" (.reg "%r15"),  -- l.3822 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3823 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.3824 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 112,  -- l.3825 `movq 112(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.3826 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3827 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.3828 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.3829 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3830 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3831 `addq %rbx, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.3832 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%r8"),  -- l.3833 `movq %r8, %rcx`
    .add "%rcx" (.reg "%r10"),  -- l.3834 `addq %r10, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.3835 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.3836 `movq %rsi, %rcx`
    .and_ "%rcx" (.reg "%rbx"),  -- l.3837 `andq %rbx, %rcx`
    .mov "%r11" (.reg "%rsi"),  -- l.3838 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%rbx"),  -- l.3839 `xorq %rbx, %r11`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3840 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3841 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3842 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r11"),  -- l.3843 `movq %r11, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3844 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3845 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3846 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3847 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3848 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3849 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3850 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3851 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r8"),  -- l.3852 `movq %r8, %rbx`
    .and_ "%rbx" (.reg "%r10") ]  -- l.3853 `andq %r10, %rbx`

/-- Segment 122 of the body: the 32 instructions from source lines 3854–3885. -/
def ed25519ScMuladdShippedSeg122 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%r8"),  -- l.3854 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%r10"),  -- l.3855 `xorq %r10, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.3856 `movq $18446744073709551615, %rdi`
    .mov "%r8" (.reg "%r9"),  -- l.3857 `movq %r9, %r8`
    .xor_ "%r8" (.reg "%rdi"),  -- l.3858 `xorq %rdi, %r8`
    .mov "%rdi" (.reg "%rsi"),  -- l.3859 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r8"),  -- l.3860 `andq %r8, %rdi`
    .mov "%rsi" (.reg "%rbx"),  -- l.3861 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.3862 `xorq %rdi, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3863 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3864 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3865 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3866 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3867 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.3868 `movq %rsi, %rbx`
    .loadMem "%rcx" "%rsp" 56,  -- l.3869 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 104,  -- l.3870 `movq 104(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3871 `imulq %r15, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3872 `movq %rcx, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.3873 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 104,  -- l.3874 `movq 104(%rsp), %r14`
    .storeMem "%rsp" (-128) (.reg "%rsi"),  -- l.3875 `movq %rsi, -128(%rsp)`
    .mulx "%rcx" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3876 `mulx %r14, %rsi, %rcx`
    .loadMem "%rsi" "%rsp" (-128),  -- l.3877 `movq -128(%rsp), %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.3878 `movq %rcx, %rdi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3879 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3880 `addq %rbx, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.3881 `movq %rcx, %r8`
    .mov "%rcx" (.reg "%r8"),  -- l.3882 `movq %r8, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.3883 `addq %rax, %rcx`
    .mov "%r9" (.reg "%rcx"),  -- l.3884 `movq %rcx, %r9`
    .mov "%rcx" (.reg "%rsi") ]  -- l.3885 `movq %rsi, %rcx`

/-- Segment 123 of the body: the 32 instructions from source lines 3886–3917. -/
def ed25519ScMuladdShippedSeg123 : List (JInstr 64) :=
  [ .and_ "%rcx" (.reg "%rbx"),  -- l.3886 `andq %rbx, %rcx`
    .mov "%r10" (.reg "%rsi"),  -- l.3887 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.3888 `xorq %rbx, %r10`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3889 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3890 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3891 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r10"),  -- l.3892 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3893 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3894 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3895 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3896 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3897 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3898 `shrq $63, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3899 `movq %rdi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3900 `addq %rbx, %rcx`
    .mov "%rbx" (.reg "%r8"),  -- l.3901 `movq %r8, %rbx`
    .and_ "%rbx" (.reg "%rax"),  -- l.3902 `andq %rax, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.3903 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.3904 `xorq %rax, %rsi`
    .mov "%rax" (.imm 18446744073709551615),  -- l.3905 `movq $18446744073709551615, %rax`
    .mov "%rdi" (.reg "%r9"),  -- l.3906 `movq %r9, %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.3907 `xorq %rax, %rdi`
    .mov "%rax" (.reg "%rsi"),  -- l.3908 `movq %rsi, %rax`
    .and_ "%rax" (.reg "%rdi"),  -- l.3909 `andq %rdi, %rax`
    .mov "%rsi" (.reg "%rbx"),  -- l.3910 `movq %rbx, %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.3911 `xorq %rax, %rsi`
    .mov "%rax" (.imm 63),  -- l.3912 `movq $63, %rax`
    .mov "%rax" (.reg "%rsi"),  -- l.3913 `movq %rsi, %rax`
    .shr "%rax" (.imm 63),  -- l.3914 `shrq $63, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.3915 `movq %rcx, %rbx`
    .add "%rbx" (.reg "%rax"),  -- l.3916 `addq %rax, %rbx`
    .mov "%rax" (.reg "%rbx") ]  -- l.3917 `movq %rbx, %rax`

/-- Segment 124 of the body: the 32 instructions from source lines 3918–3949. -/
def ed25519ScMuladdShippedSeg124 : List (JInstr 64) :=
  [ .mov "%rax" (.imm 18446744073709551615),  -- l.3918 `movq $18446744073709551615, %rax`
    .loadMem "%rbx" "%rsp" 80,  -- l.3919 `movq 80(%rsp), %rbx`
    .xor_ "%rbx" (.reg "%rax"),  -- l.3920 `xorq %rax, %rbx`
    .loadMem "%rax" "%rsp" 96,  -- l.3921 `movq 96(%rsp), %rax`
    .add "%rax" (.reg "%rbx"),  -- l.3922 `addq %rbx, %rax`
    .mov "%rbx" (.reg "%rax"),  -- l.3923 `movq %rax, %rbx`
    .mov "%rax" (.imm 1),  -- l.3924 `movq $1, %rax`
    .mov "%rcx" (.reg "%rbx"),  -- l.3925 `movq %rbx, %rcx`
    .add "%rcx" (.reg "%rax"),  -- l.3926 `addq %rax, %rcx`
    .mov "%rax" (.reg "%rcx"),  -- l.3927 `movq %rcx, %rax`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3928 `movq $18446744073709551615, %rcx`
    .loadMem "%rsi" "%rsp" 80,  -- l.3929 `movq 80(%rsp), %rsi`
    .xor_ "%rsi" (.reg "%rcx"),  -- l.3930 `xorq %rcx, %rsi`
    .loadMem "%rcx" "%rsp" 96,  -- l.3931 `movq 96(%rsp), %rcx`
    .and_ "%rcx" (.reg "%rsi"),  -- l.3932 `andq %rsi, %rcx`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.3933 `movq $18446744073709551615, %rsi`
    .loadMem "%rdi" "%rsp" 80,  -- l.3934 `movq 80(%rsp), %rdi`
    .xor_ "%rdi" (.reg "%rsi"),  -- l.3935 `xorq %rsi, %rdi`
    .loadMem "%rsi" "%rsp" 96,  -- l.3936 `movq 96(%rsp), %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.3937 `xorq %rdi, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.3938 `movq $18446744073709551615, %rdi`
    .mov "%r8" (.reg "%rbx"),  -- l.3939 `movq %rbx, %r8`
    .xor_ "%r8" (.reg "%rdi"),  -- l.3940 `xorq %rdi, %r8`
    .mov "%rdi" (.reg "%rsi"),  -- l.3941 `movq %rsi, %rdi`
    .and_ "%rdi" (.reg "%r8"),  -- l.3942 `andq %r8, %rdi`
    .mov "%rsi" (.reg "%rcx"),  -- l.3943 `movq %rcx, %rsi`
    .xor_ "%rsi" (.reg "%rdi"),  -- l.3944 `xorq %rdi, %rsi`
    .mov "%rcx" (.imm 63),  -- l.3945 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rsi"),  -- l.3946 `movq %rsi, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3947 `shrq $63, %rcx`
    .mov "%rsi" (.imm 1),  -- l.3948 `movq $1, %rsi`
    .mov "%rdi" (.reg "%rbx") ]  -- l.3949 `movq %rbx, %rdi`

/-- Segment 125 of the body: the 32 instructions from source lines 3950–3981. -/
def ed25519ScMuladdShippedSeg125 : List (JInstr 64) :=
  [ .and_ "%rdi" (.reg "%rsi"),  -- l.3950 `andq %rsi, %rdi`
    .mov "%rsi" (.imm 1),  -- l.3951 `movq $1, %rsi`
    .mov "%r8" (.reg "%rbx"),  -- l.3952 `movq %rbx, %r8`
    .xor_ "%r8" (.reg "%rsi"),  -- l.3953 `xorq %rsi, %r8`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.3954 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rax"),  -- l.3955 `movq %rax, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3956 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r8"),  -- l.3957 `movq %r8, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.3958 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rdi"),  -- l.3959 `movq %rdi, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.3960 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.3961 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.3962 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.3963 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3964 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.3965 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.3966 `movq %rsi, %rbx`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3967 `movq $18446744073709551615, %rcx`
    .loadMem "%rsi" "%rsp" 48,  -- l.3968 `movq 48(%rsp), %rsi`
    .xor_ "%rsi" (.reg "%rcx"),  -- l.3969 `xorq %rcx, %rsi`
    .loadMem "%rcx" "%rsp" 64,  -- l.3970 `movq 64(%rsp), %rcx`
    .add "%rcx" (.reg "%rsi"),  -- l.3971 `addq %rsi, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.3972 `movq %rcx, %rsi`
    .mov "%rcx" (.reg "%rsi"),  -- l.3973 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.3974 `addq %rbx, %rcx`
    .mov "%rdi" (.reg "%rcx"),  -- l.3975 `movq %rcx, %rdi`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.3976 `movq $18446744073709551615, %rcx`
    .loadMem "%r8" "%rsp" 48,  -- l.3977 `movq 48(%rsp), %r8`
    .xor_ "%r8" (.reg "%rcx"),  -- l.3978 `xorq %rcx, %r8`
    .loadMem "%rcx" "%rsp" 64,  -- l.3979 `movq 64(%rsp), %rcx`
    .and_ "%rcx" (.reg "%r8"),  -- l.3980 `andq %r8, %rcx`
    .mov "%r8" (.imm 18446744073709551615) ]  -- l.3981 `movq $18446744073709551615, %r8`

/-- Segment 126 of the body: the 32 instructions from source lines 3982–4013. -/
def ed25519ScMuladdShippedSeg126 : List (JInstr 64) :=
  [ .loadMem "%r9" "%rsp" 48,  -- l.3982 `movq 48(%rsp), %r9`
    .xor_ "%r9" (.reg "%r8"),  -- l.3983 `xorq %r8, %r9`
    .loadMem "%r8" "%rsp" 64,  -- l.3984 `movq 64(%rsp), %r8`
    .xor_ "%r8" (.reg "%r9"),  -- l.3985 `xorq %r9, %r8`
    .mov "%r9" (.imm 18446744073709551615),  -- l.3986 `movq $18446744073709551615, %r9`
    .mov "%r10" (.reg "%rsi"),  -- l.3987 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%r9"),  -- l.3988 `xorq %r9, %r10`
    .mov "%r9" (.reg "%r8"),  -- l.3989 `movq %r8, %r9`
    .and_ "%r9" (.reg "%r10"),  -- l.3990 `andq %r10, %r9`
    .mov "%r8" (.reg "%rcx"),  -- l.3991 `movq %rcx, %r8`
    .xor_ "%r8" (.reg "%r9"),  -- l.3992 `xorq %r9, %r8`
    .mov "%rcx" (.imm 63),  -- l.3993 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r8"),  -- l.3994 `movq %r8, %rcx`
    .shr "%rcx" (.imm 63),  -- l.3995 `shrq $63, %rcx`
    .mov "%r8" (.reg "%rsi"),  -- l.3996 `movq %rsi, %r8`
    .and_ "%r8" (.reg "%rbx"),  -- l.3997 `andq %rbx, %r8`
    .mov "%r9" (.reg "%rsi"),  -- l.3998 `movq %rsi, %r9`
    .xor_ "%r9" (.reg "%rbx"),  -- l.3999 `xorq %rbx, %r9`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.4000 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rdi"),  -- l.4001 `movq %rdi, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.4002 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r9"),  -- l.4003 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.4004 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.4005 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.4006 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.4007 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.4008 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.4009 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.4010 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.4011 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.4012 `movq %rsi, %rbx`
    .mov "%rcx" (.imm 18446744073709551615) ]  -- l.4013 `movq $18446744073709551615, %rcx`

/-- Segment 127 of the body: the 32 instructions from source lines 4014–4045. -/
def ed25519ScMuladdShippedSeg127 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rbp"),  -- l.4014 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rcx"),  -- l.4015 `xorq %rcx, %rsi`
    .loadMem "%rcx" "%rsp" 72,  -- l.4016 `movq 72(%rsp), %rcx`
    .add "%rcx" (.reg "%rsi"),  -- l.4017 `addq %rsi, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.4018 `movq %rcx, %rsi`
    .mov "%rcx" (.reg "%rsi"),  -- l.4019 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.4020 `addq %rbx, %rcx`
    .mov "%r8" (.reg "%rcx"),  -- l.4021 `movq %rcx, %r8`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.4022 `movq $18446744073709551615, %rcx`
    .mov "%r9" (.reg "%rbp"),  -- l.4023 `movq %rbp, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.4024 `xorq %rcx, %r9`
    .loadMem "%rcx" "%rsp" 72,  -- l.4025 `movq 72(%rsp), %rcx`
    .and_ "%rcx" (.reg "%r9"),  -- l.4026 `andq %r9, %rcx`
    .mov "%r9" (.imm 18446744073709551615),  -- l.4027 `movq $18446744073709551615, %r9`
    .mov "%r10" (.reg "%rbp"),  -- l.4028 `movq %rbp, %r10`
    .xor_ "%r10" (.reg "%r9"),  -- l.4029 `xorq %r9, %r10`
    .loadMem "%rbp" "%rsp" 72,  -- l.4030 `movq 72(%rsp), %rbp`
    .xor_ "%rbp" (.reg "%r10"),  -- l.4031 `xorq %r10, %rbp`
    .mov "%r9" (.imm 18446744073709551615),  -- l.4032 `movq $18446744073709551615, %r9`
    .mov "%r10" (.reg "%rsi"),  -- l.4033 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%r9"),  -- l.4034 `xorq %r9, %r10`
    .mov "%r9" (.reg "%rbp"),  -- l.4035 `movq %rbp, %r9`
    .and_ "%r9" (.reg "%r10"),  -- l.4036 `andq %r10, %r9`
    .mov "%rbp" (.reg "%rcx"),  -- l.4037 `movq %rcx, %rbp`
    .xor_ "%rbp" (.reg "%r9"),  -- l.4038 `xorq %r9, %rbp`
    .mov "%rcx" (.imm 63),  -- l.4039 `movq $63, %rcx`
    .mov "%rcx" (.reg "%rbp"),  -- l.4040 `movq %rbp, %rcx`
    .shr "%rcx" (.imm 63),  -- l.4041 `shrq $63, %rcx`
    .mov "%rbp" (.reg "%rsi"),  -- l.4042 `movq %rsi, %rbp`
    .and_ "%rbp" (.reg "%rbx"),  -- l.4043 `andq %rbx, %rbp`
    .mov "%r9" (.reg "%rsi"),  -- l.4044 `movq %rsi, %r9`
    .xor_ "%r9" (.reg "%rbx") ]  -- l.4045 `xorq %rbx, %r9`

/-- Segment 128 of the body: the 32 instructions from source lines 4046–4077. -/
def ed25519ScMuladdShippedSeg128 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 18446744073709551615),  -- l.4046 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%r8"),  -- l.4047 `movq %r8, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.4048 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r9"),  -- l.4049 `movq %r9, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.4050 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.4051 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.4052 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.4053 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.4054 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.4055 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.4056 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.4057 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.4058 `movq %rsi, %rbx`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.4059 `movq $18446744073709551615, %rcx`
    .loadMem "%rsi" "%rsp" 32,  -- l.4060 `movq 32(%rsp), %rsi`
    .xor_ "%rsi" (.reg "%rcx"),  -- l.4061 `xorq %rcx, %rsi`
    .loadMem "%rcx" "%rsp" 88,  -- l.4062 `movq 88(%rsp), %rcx`
    .add "%rcx" (.reg "%rsi"),  -- l.4063 `addq %rsi, %rcx`
    .mov "%rsi" (.reg "%rcx"),  -- l.4064 `movq %rcx, %rsi`
    .mov "%rcx" (.reg "%rsi"),  -- l.4065 `movq %rsi, %rcx`
    .add "%rcx" (.reg "%rbx"),  -- l.4066 `addq %rbx, %rcx`
    .mov "%rbp" (.reg "%rcx"),  -- l.4067 `movq %rcx, %rbp`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.4068 `movq $18446744073709551615, %rcx`
    .loadMem "%r9" "%rsp" 32,  -- l.4069 `movq 32(%rsp), %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.4070 `xorq %rcx, %r9`
    .loadMem "%rcx" "%rsp" 88,  -- l.4071 `movq 88(%rsp), %rcx`
    .and_ "%rcx" (.reg "%r9"),  -- l.4072 `andq %r9, %rcx`
    .mov "%r9" (.imm 18446744073709551615),  -- l.4073 `movq $18446744073709551615, %r9`
    .loadMem "%r10" "%rsp" 32,  -- l.4074 `movq 32(%rsp), %r10`
    .xor_ "%r10" (.reg "%r9"),  -- l.4075 `xorq %r9, %r10`
    .loadMem "%r9" "%rsp" 88,  -- l.4076 `movq 88(%rsp), %r9`
    .xor_ "%r9" (.reg "%r10") ]  -- l.4077 `xorq %r10, %r9`

/-- Segment 129 of the body: the 32 instructions from source lines 4078–4109. -/
def ed25519ScMuladdShippedSeg129 : List (JInstr 64) :=
  [ .mov "%r10" (.imm 18446744073709551615),  -- l.4078 `movq $18446744073709551615, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.4079 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%r10"),  -- l.4080 `xorq %r10, %r11`
    .mov "%r10" (.reg "%r9"),  -- l.4081 `movq %r9, %r10`
    .and_ "%r10" (.reg "%r11"),  -- l.4082 `andq %r11, %r10`
    .mov "%r9" (.reg "%rcx"),  -- l.4083 `movq %rcx, %r9`
    .xor_ "%r9" (.reg "%r10"),  -- l.4084 `xorq %r10, %r9`
    .mov "%rcx" (.imm 63),  -- l.4085 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r9"),  -- l.4086 `movq %r9, %rcx`
    .shr "%rcx" (.imm 63),  -- l.4087 `shrq $63, %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.4088 `movq %rsi, %r9`
    .and_ "%r9" (.reg "%rbx"),  -- l.4089 `andq %rbx, %r9`
    .mov "%r10" (.reg "%rsi"),  -- l.4090 `movq %rsi, %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.4091 `xorq %rbx, %r10`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.4092 `movq $18446744073709551615, %rbx`
    .mov "%rsi" (.reg "%rbp"),  -- l.4093 `movq %rbp, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.4094 `xorq %rbx, %rsi`
    .mov "%rbx" (.reg "%r10"),  -- l.4095 `movq %r10, %rbx`
    .and_ "%rbx" (.reg "%rsi"),  -- l.4096 `andq %rsi, %rbx`
    .mov "%rsi" (.reg "%r9"),  -- l.4097 `movq %r9, %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.4098 `xorq %rbx, %rsi`
    .mov "%rbx" (.imm 63),  -- l.4099 `movq $63, %rbx`
    .mov "%rbx" (.reg "%rsi"),  -- l.4100 `movq %rsi, %rbx`
    .shr "%rbx" (.imm 63),  -- l.4101 `shrq $63, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.4102 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.4103 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.4104 `movq %rsi, %rbx`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.4105 `movq $18446744073709551615, %rbx`
    .loadMem "%rcx" "%rsp" 128,  -- l.4106 `movq 128(%rsp), %rcx`
    .xor_ "%rcx" (.reg "%rbx"),  -- l.4107 `xorq %rbx, %rcx`
    .mov "%rbx" (.reg "%rax"),  -- l.4108 `movq %rax, %rbx`
    .add "%rbx" (.reg "%rcx") ]  -- l.4109 `addq %rcx, %rbx`

/-- Segment 130 of the body: the 32 instructions from source lines 4110–4141. -/
def ed25519ScMuladdShippedSeg130 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rbx"),  -- l.4110 `movq %rbx, %rcx`
    .mov "%rbx" (.imm 1),  -- l.4111 `movq $1, %rbx`
    .mov "%rsi" (.reg "%rcx"),  -- l.4112 `movq %rcx, %rsi`
    .add "%rsi" (.reg "%rbx"),  -- l.4113 `addq %rbx, %rsi`
    .mov "%rbx" (.reg "%rsi"),  -- l.4114 `movq %rsi, %rbx`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.4115 `movq $18446744073709551615, %rsi`
    .loadMem "%r9" "%rsp" 128,  -- l.4116 `movq 128(%rsp), %r9`
    .xor_ "%r9" (.reg "%rsi"),  -- l.4117 `xorq %rsi, %r9`
    .mov "%rsi" (.reg "%rax"),  -- l.4118 `movq %rax, %rsi`
    .and_ "%rsi" (.reg "%r9"),  -- l.4119 `andq %r9, %rsi`
    .mov "%r9" (.imm 18446744073709551615),  -- l.4120 `movq $18446744073709551615, %r9`
    .loadMem "%r10" "%rsp" 128,  -- l.4121 `movq 128(%rsp), %r10`
    .xor_ "%r10" (.reg "%r9"),  -- l.4122 `xorq %r9, %r10`
    .mov "%r9" (.reg "%rax"),  -- l.4123 `movq %rax, %r9`
    .xor_ "%r9" (.reg "%r10"),  -- l.4124 `xorq %r10, %r9`
    .mov "%r10" (.imm 18446744073709551615),  -- l.4125 `movq $18446744073709551615, %r10`
    .mov "%r11" (.reg "%rcx"),  -- l.4126 `movq %rcx, %r11`
    .xor_ "%r11" (.reg "%r10"),  -- l.4127 `xorq %r10, %r11`
    .mov "%r10" (.reg "%r9"),  -- l.4128 `movq %r9, %r10`
    .and_ "%r10" (.reg "%r11"),  -- l.4129 `andq %r11, %r10`
    .mov "%r9" (.reg "%rsi"),  -- l.4130 `movq %rsi, %r9`
    .xor_ "%r9" (.reg "%r10"),  -- l.4131 `xorq %r10, %r9`
    .mov "%rsi" (.imm 63),  -- l.4132 `movq $63, %rsi`
    .mov "%rsi" (.reg "%r9"),  -- l.4133 `movq %r9, %rsi`
    .shr "%rsi" (.imm 63),  -- l.4134 `shrq $63, %rsi`
    .mov "%r9" (.imm 1),  -- l.4135 `movq $1, %r9`
    .mov "%r10" (.reg "%rcx"),  -- l.4136 `movq %rcx, %r10`
    .and_ "%r10" (.reg "%r9"),  -- l.4137 `andq %r9, %r10`
    .mov "%r9" (.imm 1),  -- l.4138 `movq $1, %r9`
    .mov "%r11" (.reg "%rcx"),  -- l.4139 `movq %rcx, %r11`
    .xor_ "%r11" (.reg "%r9"),  -- l.4140 `xorq %r9, %r11`
    .mov "%rcx" (.imm 18446744073709551615) ]  -- l.4141 `movq $18446744073709551615, %rcx`

/-- Segment 131 of the body: the 32 instructions from source lines 4142–4173. -/
def ed25519ScMuladdShippedSeg131 : List (JInstr 64) :=
  [ .mov "%r9" (.reg "%rbx"),  -- l.4142 `movq %rbx, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.4143 `xorq %rcx, %r9`
    .mov "%rcx" (.reg "%r11"),  -- l.4144 `movq %r11, %rcx`
    .and_ "%rcx" (.reg "%r9"),  -- l.4145 `andq %r9, %rcx`
    .mov "%r9" (.reg "%r10"),  -- l.4146 `movq %r10, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.4147 `xorq %rcx, %r9`
    .mov "%rcx" (.imm 63),  -- l.4148 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r9"),  -- l.4149 `movq %r9, %rcx`
    .shr "%rcx" (.imm 63),  -- l.4150 `shrq $63, %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.4151 `movq %rsi, %r9`
    .add "%r9" (.reg "%rcx"),  -- l.4152 `addq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.4153 `movq %r9, %rcx`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.4154 `movq $18446744073709551615, %rsi`
    .loadMem "%r9" "%rsp" 120,  -- l.4155 `movq 120(%rsp), %r9`
    .xor_ "%r9" (.reg "%rsi"),  -- l.4156 `xorq %rsi, %r9`
    .mov "%rsi" (.reg "%rdi"),  -- l.4157 `movq %rdi, %rsi`
    .add "%rsi" (.reg "%r9"),  -- l.4158 `addq %r9, %rsi`
    .mov "%r9" (.reg "%rsi"),  -- l.4159 `movq %rsi, %r9`
    .mov "%rsi" (.reg "%r9"),  -- l.4160 `movq %r9, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.4161 `addq %rcx, %rsi`
    .mov "%r10" (.reg "%rsi"),  -- l.4162 `movq %rsi, %r10`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.4163 `movq $18446744073709551615, %rsi`
    .loadMem "%r11" "%rsp" 120,  -- l.4164 `movq 120(%rsp), %r11`
    .xor_ "%r11" (.reg "%rsi"),  -- l.4165 `xorq %rsi, %r11`
    .mov "%rsi" (.reg "%rdi"),  -- l.4166 `movq %rdi, %rsi`
    .and_ "%rsi" (.reg "%r11"),  -- l.4167 `andq %r11, %rsi`
    .mov "%r11" (.imm 18446744073709551615),  -- l.4168 `movq $18446744073709551615, %r11`
    .loadMem "%r12" "%rsp" 120,  -- l.4169 `movq 120(%rsp), %r12`
    .xor_ "%r12" (.reg "%r11"),  -- l.4170 `xorq %r11, %r12`
    .mov "%r11" (.reg "%rdi"),  -- l.4171 `movq %rdi, %r11`
    .xor_ "%r11" (.reg "%r12"),  -- l.4172 `xorq %r12, %r11`
    .mov "%r12" (.imm 18446744073709551615) ]  -- l.4173 `movq $18446744073709551615, %r12`

/-- Segment 132 of the body: the 32 instructions from source lines 4174–4205. -/
def ed25519ScMuladdShippedSeg132 : List (JInstr 64) :=
  [ .mov "%r13" (.reg "%r9"),  -- l.4174 `movq %r9, %r13`
    .xor_ "%r13" (.reg "%r12"),  -- l.4175 `xorq %r12, %r13`
    .mov "%r12" (.reg "%r11"),  -- l.4176 `movq %r11, %r12`
    .and_ "%r12" (.reg "%r13"),  -- l.4177 `andq %r13, %r12`
    .mov "%r11" (.reg "%rsi"),  -- l.4178 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%r12"),  -- l.4179 `xorq %r12, %r11`
    .mov "%rsi" (.imm 63),  -- l.4180 `movq $63, %rsi`
    .mov "%rsi" (.reg "%r11"),  -- l.4181 `movq %r11, %rsi`
    .shr "%rsi" (.imm 63),  -- l.4182 `shrq $63, %rsi`
    .mov "%r11" (.reg "%r9"),  -- l.4183 `movq %r9, %r11`
    .and_ "%r11" (.reg "%rcx"),  -- l.4184 `andq %rcx, %r11`
    .mov "%r12" (.reg "%r9"),  -- l.4185 `movq %r9, %r12`
    .xor_ "%r12" (.reg "%rcx"),  -- l.4186 `xorq %rcx, %r12`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.4187 `movq $18446744073709551615, %rcx`
    .mov "%r9" (.reg "%r10"),  -- l.4188 `movq %r10, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.4189 `xorq %rcx, %r9`
    .mov "%rcx" (.reg "%r12"),  -- l.4190 `movq %r12, %rcx`
    .and_ "%rcx" (.reg "%r9"),  -- l.4191 `andq %r9, %rcx`
    .mov "%r9" (.reg "%r11"),  -- l.4192 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.4193 `xorq %rcx, %r9`
    .mov "%rcx" (.imm 63),  -- l.4194 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r9"),  -- l.4195 `movq %r9, %rcx`
    .shr "%rcx" (.imm 63),  -- l.4196 `shrq $63, %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.4197 `movq %rsi, %r9`
    .add "%r9" (.reg "%rcx"),  -- l.4198 `addq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.4199 `movq %r9, %rcx`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.4200 `movq $18446744073709551615, %rsi`
    .loadMem "%r9" "%rsp" 112,  -- l.4201 `movq 112(%rsp), %r9`
    .xor_ "%r9" (.reg "%rsi"),  -- l.4202 `xorq %rsi, %r9`
    .mov "%rsi" (.reg "%r8"),  -- l.4203 `movq %r8, %rsi`
    .add "%rsi" (.reg "%r9"),  -- l.4204 `addq %r9, %rsi`
    .mov "%r9" (.reg "%rsi") ]  -- l.4205 `movq %rsi, %r9`

/-- Segment 133 of the body: the 32 instructions from source lines 4206–4237. -/
def ed25519ScMuladdShippedSeg133 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%r9"),  -- l.4206 `movq %r9, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.4207 `addq %rcx, %rsi`
    .mov "%r15" (.reg "%rsi"),  -- l.4208 `movq %rsi, %r15`
    .storeMem "%rsp" 128 (.reg "%r15"),  -- l.4209 `movq %r15, 128(%rsp)`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.4210 `movq $18446744073709551615, %rsi`
    .loadMem "%r12" "%rsp" 112,  -- l.4211 `movq 112(%rsp), %r12`
    .xor_ "%r12" (.reg "%rsi"),  -- l.4212 `xorq %rsi, %r12`
    .mov "%rsi" (.reg "%r8"),  -- l.4213 `movq %r8, %rsi`
    .and_ "%rsi" (.reg "%r12"),  -- l.4214 `andq %r12, %rsi`
    .mov "%r12" (.imm 18446744073709551615),  -- l.4215 `movq $18446744073709551615, %r12`
    .loadMem "%r13" "%rsp" 112,  -- l.4216 `movq 112(%rsp), %r13`
    .xor_ "%r13" (.reg "%r12"),  -- l.4217 `xorq %r12, %r13`
    .mov "%r12" (.reg "%r8"),  -- l.4218 `movq %r8, %r12`
    .xor_ "%r12" (.reg "%r13"),  -- l.4219 `xorq %r13, %r12`
    .mov "%r13" (.imm 18446744073709551615),  -- l.4220 `movq $18446744073709551615, %r13`
    .mov "%r11" (.reg "%r9"),  -- l.4221 `movq %r9, %r11`
    .xor_ "%r11" (.reg "%r13"),  -- l.4222 `xorq %r13, %r11`
    .mov "%r13" (.reg "%r12"),  -- l.4223 `movq %r12, %r13`
    .and_ "%r13" (.reg "%r11"),  -- l.4224 `andq %r11, %r13`
    .mov "%r11" (.reg "%rsi"),  -- l.4225 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%r13"),  -- l.4226 `xorq %r13, %r11`
    .mov "%rsi" (.imm 63),  -- l.4227 `movq $63, %rsi`
    .mov "%rsi" (.reg "%r11"),  -- l.4228 `movq %r11, %rsi`
    .shr "%rsi" (.imm 63),  -- l.4229 `shrq $63, %rsi`
    .mov "%r11" (.reg "%r9"),  -- l.4230 `movq %r9, %r11`
    .and_ "%r11" (.reg "%rcx"),  -- l.4231 `andq %rcx, %r11`
    .mov "%r12" (.reg "%r9"),  -- l.4232 `movq %r9, %r12`
    .xor_ "%r12" (.reg "%rcx"),  -- l.4233 `xorq %rcx, %r12`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.4234 `movq $18446744073709551615, %rcx`
    .loadMem "%r9" "%rsp" 128,  -- l.4235 `movq 128(%rsp), %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.4236 `xorq %rcx, %r9`
    .mov "%rcx" (.reg "%r12") ]  -- l.4237 `movq %r12, %rcx`

/-- Segment 134 of the body: the 32 instructions from source lines 4238–4269. -/
def ed25519ScMuladdShippedSeg134 : List (JInstr 64) :=
  [ .and_ "%rcx" (.reg "%r9"),  -- l.4238 `andq %r9, %rcx`
    .mov "%r9" (.reg "%r11"),  -- l.4239 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.4240 `xorq %rcx, %r9`
    .mov "%rcx" (.imm 63),  -- l.4241 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r9"),  -- l.4242 `movq %r9, %rcx`
    .shr "%rcx" (.imm 63),  -- l.4243 `shrq $63, %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.4244 `movq %rsi, %r9`
    .add "%r9" (.reg "%rcx"),  -- l.4245 `addq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.4246 `movq %r9, %rcx`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.4247 `movq $18446744073709551615, %rsi`
    .loadMem "%r9" "%rsp" 104,  -- l.4248 `movq 104(%rsp), %r9`
    .xor_ "%r9" (.reg "%rsi"),  -- l.4249 `xorq %rsi, %r9`
    .mov "%rsi" (.reg "%rbp"),  -- l.4250 `movq %rbp, %rsi`
    .add "%rsi" (.reg "%r9"),  -- l.4251 `addq %r9, %rsi`
    .mov "%r9" (.reg "%rsi"),  -- l.4252 `movq %rsi, %r9`
    .mov "%rsi" (.reg "%r9"),  -- l.4253 `movq %r9, %rsi`
    .add "%rsi" (.reg "%rcx"),  -- l.4254 `addq %rcx, %rsi`
    .mov "%r15" (.reg "%rsi"),  -- l.4255 `movq %rsi, %r15`
    .storeMem "%rsp" 120 (.reg "%r15"),  -- l.4256 `movq %r15, 120(%rsp)`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.4257 `movq $18446744073709551615, %rsi`
    .loadMem "%r12" "%rsp" 104,  -- l.4258 `movq 104(%rsp), %r12`
    .xor_ "%r12" (.reg "%rsi"),  -- l.4259 `xorq %rsi, %r12`
    .mov "%rsi" (.reg "%rbp"),  -- l.4260 `movq %rbp, %rsi`
    .and_ "%rsi" (.reg "%r12"),  -- l.4261 `andq %r12, %rsi`
    .mov "%r12" (.imm 18446744073709551615),  -- l.4262 `movq $18446744073709551615, %r12`
    .loadMem "%r13" "%rsp" 104,  -- l.4263 `movq 104(%rsp), %r13`
    .xor_ "%r13" (.reg "%r12"),  -- l.4264 `xorq %r12, %r13`
    .mov "%r12" (.reg "%rbp"),  -- l.4265 `movq %rbp, %r12`
    .xor_ "%r12" (.reg "%r13"),  -- l.4266 `xorq %r13, %r12`
    .mov "%r13" (.imm 18446744073709551615),  -- l.4267 `movq $18446744073709551615, %r13`
    .mov "%r11" (.reg "%r9"),  -- l.4268 `movq %r9, %r11`
    .xor_ "%r11" (.reg "%r13") ]  -- l.4269 `xorq %r13, %r11`

/-- Segment 135 of the body: the 32 instructions from source lines 4270–4301. -/
def ed25519ScMuladdShippedSeg135 : List (JInstr 64) :=
  [ .mov "%r13" (.reg "%r12"),  -- l.4270 `movq %r12, %r13`
    .and_ "%r13" (.reg "%r11"),  -- l.4271 `andq %r11, %r13`
    .mov "%r11" (.reg "%rsi"),  -- l.4272 `movq %rsi, %r11`
    .xor_ "%r11" (.reg "%r13"),  -- l.4273 `xorq %r13, %r11`
    .mov "%rsi" (.imm 63),  -- l.4274 `movq $63, %rsi`
    .mov "%rsi" (.reg "%r11"),  -- l.4275 `movq %r11, %rsi`
    .shr "%rsi" (.imm 63),  -- l.4276 `shrq $63, %rsi`
    .mov "%r11" (.reg "%r9"),  -- l.4277 `movq %r9, %r11`
    .and_ "%r11" (.reg "%rcx"),  -- l.4278 `andq %rcx, %r11`
    .mov "%r12" (.reg "%r9"),  -- l.4279 `movq %r9, %r12`
    .xor_ "%r12" (.reg "%rcx"),  -- l.4280 `xorq %rcx, %r12`
    .mov "%rcx" (.imm 18446744073709551615),  -- l.4281 `movq $18446744073709551615, %rcx`
    .loadMem "%r9" "%rsp" 120,  -- l.4282 `movq 120(%rsp), %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.4283 `xorq %rcx, %r9`
    .mov "%rcx" (.reg "%r12"),  -- l.4284 `movq %r12, %rcx`
    .and_ "%rcx" (.reg "%r9"),  -- l.4285 `andq %r9, %rcx`
    .mov "%r9" (.reg "%r11"),  -- l.4286 `movq %r11, %r9`
    .xor_ "%r9" (.reg "%rcx"),  -- l.4287 `xorq %rcx, %r9`
    .mov "%rcx" (.imm 63),  -- l.4288 `movq $63, %rcx`
    .mov "%rcx" (.reg "%r9"),  -- l.4289 `movq %r9, %rcx`
    .shr "%rcx" (.imm 63),  -- l.4290 `shrq $63, %rcx`
    .mov "%r9" (.reg "%rsi"),  -- l.4291 `movq %rsi, %r9`
    .add "%r9" (.reg "%rcx"),  -- l.4292 `addq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.4293 `movq %r9, %rcx`
    .mov "%rsi" (.imm 0),  -- l.4294 `movq $0, %rsi`
    .mov "%r9" (.reg "%rsi"),  -- l.4295 `movq %rsi, %r9`
    .sub "%r9" (.reg "%rcx"),  -- l.4296 `subq %rcx, %r9`
    .mov "%rcx" (.reg "%r9"),  -- l.4297 `movq %r9, %rcx`
    .mov "%rsi" (.reg "%rbx"),  -- l.4298 `movq %rbx, %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.4299 `andq %rcx, %rsi`
    .mov "%rbx" (.imm 18446744073709551615),  -- l.4300 `movq $18446744073709551615, %rbx`
    .mov "%r9" (.reg "%rcx") ]  -- l.4301 `movq %rcx, %r9`

/-- Segment 136 of the body: the 32 instructions from source lines 4302–4333. -/
def ed25519ScMuladdShippedSeg136 : List (JInstr 64) :=
  [ .xor_ "%r9" (.reg "%rbx"),  -- l.4302 `xorq %rbx, %r9`
    .mov "%rbx" (.reg "%rax"),  -- l.4303 `movq %rax, %rbx`
    .and_ "%rbx" (.reg "%r9"),  -- l.4304 `andq %r9, %rbx`
    .mov "%rax" (.reg "%rsi"),  -- l.4305 `movq %rsi, %rax`
    .xor_ "%rax" (.reg "%rbx"),  -- l.4306 `xorq %rbx, %rax`
    .mov "%rbx" (.reg "%rax"),  -- l.4307 `movq %rax, %rbx`
    .mov "%rax" (.reg "%r10"),  -- l.4308 `movq %r10, %rax`
    .and_ "%rax" (.reg "%rcx"),  -- l.4309 `andq %rcx, %rax`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.4310 `movq $18446744073709551615, %rsi`
    .mov "%r9" (.reg "%rcx"),  -- l.4311 `movq %rcx, %r9`
    .xor_ "%r9" (.reg "%rsi"),  -- l.4312 `xorq %rsi, %r9`
    .mov "%rsi" (.reg "%rdi"),  -- l.4313 `movq %rdi, %rsi`
    .and_ "%rsi" (.reg "%r9"),  -- l.4314 `andq %r9, %rsi`
    .mov "%rdi" (.reg "%rax"),  -- l.4315 `movq %rax, %rdi`
    .xor_ "%rdi" (.reg "%rsi"),  -- l.4316 `xorq %rsi, %rdi`
    .mov "%rax" (.reg "%rdi"),  -- l.4317 `movq %rdi, %rax`
    .loadMem "%rsi" "%rsp" 128,  -- l.4318 `movq 128(%rsp), %rsi`
    .and_ "%rsi" (.reg "%rcx"),  -- l.4319 `andq %rcx, %rsi`
    .mov "%rdi" (.imm 18446744073709551615),  -- l.4320 `movq $18446744073709551615, %rdi`
    .mov "%r9" (.reg "%rcx"),  -- l.4321 `movq %rcx, %r9`
    .xor_ "%r9" (.reg "%rdi"),  -- l.4322 `xorq %rdi, %r9`
    .mov "%rdi" (.reg "%r8"),  -- l.4323 `movq %r8, %rdi`
    .and_ "%rdi" (.reg "%r9"),  -- l.4324 `andq %r9, %rdi`
    .mov "%r8" (.reg "%rsi"),  -- l.4325 `movq %rsi, %r8`
    .xor_ "%r8" (.reg "%rdi"),  -- l.4326 `xorq %rdi, %r8`
    .mov "%rsi" (.reg "%r8"),  -- l.4327 `movq %r8, %rsi`
    .loadMem "%rdi" "%rsp" 120,  -- l.4328 `movq 120(%rsp), %rdi`
    .and_ "%rdi" (.reg "%rcx"),  -- l.4329 `andq %rcx, %rdi`
    .mov "%r8" (.imm 18446744073709551615),  -- l.4330 `movq $18446744073709551615, %r8`
    .mov "%r9" (.reg "%rcx"),  -- l.4331 `movq %rcx, %r9`
    .xor_ "%r9" (.reg "%r8"),  -- l.4332 `xorq %r8, %r9`
    .mov "%rcx" (.reg "%rbp") ]  -- l.4333 `movq %rbp, %rcx`

/-- Segment 137 of the body: the 20 instructions from source lines 4334–4353. -/
def ed25519ScMuladdShippedSeg137 : List (JInstr 64) :=
  [ .and_ "%rcx" (.reg "%r9"),  -- l.4334 `andq %r9, %rcx`
    .mov "%rbp" (.reg "%rdi"),  -- l.4335 `movq %rdi, %rbp`
    .xor_ "%rbp" (.reg "%rcx"),  -- l.4336 `xorq %rcx, %rbp`
    .mov "%rcx" (.reg "%rbp"),  -- l.4337 `movq %rbp, %rcx`
    .mov "%rdi" (.reg "%rbx"),  -- l.4338 `movq %rbx, %rdi`
    .mov "%rbx" (.reg "%rax"),  -- l.4339 `movq %rax, %rbx`
    .mov "%rax" (.reg "%rsi"),  -- l.4340 `movq %rsi, %rax`
    .mov "%rsi" (.reg "%rcx"),  -- l.4341 `movq %rcx, %rsi`
    .loadMem "%r14" "%rsp" 232,  -- l.4342 `movq 232(%rsp), %r14`
    .loadMem "%r15" "%rsp" 144,  -- l.4343 `movq 144(%rsp), %r15`
    .storeMemIdx "%r14" "%r15" 8 (.reg "%rdi"),  -- l.4344 `movq %rdi, (%r14, %r15, 8)`
    .loadMem "%r14" "%rsp" 232,  -- l.4345 `movq 232(%rsp), %r14`
    .loadMem "%r15" "%rsp" 152,  -- l.4346 `movq 152(%rsp), %r15`
    .storeMemIdx "%r14" "%r15" 8 (.reg "%rbx"),  -- l.4347 `movq %rbx, (%r14, %r15, 8)`
    .loadMem "%r14" "%rsp" 232,  -- l.4348 `movq 232(%rsp), %r14`
    .loadMem "%r15" "%rsp" 160,  -- l.4349 `movq 160(%rsp), %r15`
    .storeMemIdx "%r14" "%r15" 8 (.reg "%rax"),  -- l.4350 `movq %rax, (%r14, %r15, 8)`
    .loadMem "%r14" "%rsp" 232,  -- l.4351 `movq 232(%rsp), %r14`
    .loadMem "%r15" "%rsp" 168,  -- l.4352 `movq 168(%rsp), %r15`
    .storeMemIdx "%r14" "%r15" 8 (.reg "%rsi") ]  -- l.4353 `movq %rsi, (%r14, %r15, 8)`

/-- Segment 138 of the body: the 6 instructions from source lines 4354–4359. -/
def ed25519ScMuladdShippedSeg138 : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 216,  -- l.4354 `movq 216(%rsp), %rbx`
    .loadMem "%rbp" "%rsp" 208,  -- l.4355 `movq 208(%rsp), %rbp`
    .loadMem "%r12" "%rsp" 200,  -- l.4356 `movq 200(%rsp), %r12`
    .loadMem "%r13" "%rsp" 192,  -- l.4357 `movq 192(%rsp), %r13`
    .loadMem "%r14" "%rsp" 184,  -- l.4358 `movq 184(%rsp), %r14`
    .loadMem "%r15" "%rsp" 176 ]  -- l.4359 `movq 176(%rsp), %r15`

/-- Part 1 of the body: segments 1–16. -/
def ed25519ScMuladdShippedPart01 : List (JInstr 64) :=
  ed25519ScMuladdShippedSeg001 ++ ed25519ScMuladdShippedSeg002 ++
  ed25519ScMuladdShippedSeg003 ++ ed25519ScMuladdShippedSeg004 ++
  ed25519ScMuladdShippedSeg005 ++ ed25519ScMuladdShippedSeg006 ++
  ed25519ScMuladdShippedSeg007 ++ ed25519ScMuladdShippedSeg008 ++
  ed25519ScMuladdShippedSeg009 ++ ed25519ScMuladdShippedSeg010 ++
  ed25519ScMuladdShippedSeg011 ++ ed25519ScMuladdShippedSeg012 ++
  ed25519ScMuladdShippedSeg013 ++ ed25519ScMuladdShippedSeg014 ++
  ed25519ScMuladdShippedSeg015 ++ ed25519ScMuladdShippedSeg016

/-- Part 1 has 488 instructions. -/
theorem ed25519ScMuladdShippedPart01_length :
    ed25519ScMuladdShippedPart01.length = 488 := by
  unfold ed25519ScMuladdShippedPart01
  simp only [List.length_append]
  rfl

/-- Part 2 of the body: segments 17–32. -/
def ed25519ScMuladdShippedPart02 : List (JInstr 64) :=
  ed25519ScMuladdShippedSeg017 ++ ed25519ScMuladdShippedSeg018 ++
  ed25519ScMuladdShippedSeg019 ++ ed25519ScMuladdShippedSeg020 ++
  ed25519ScMuladdShippedSeg021 ++ ed25519ScMuladdShippedSeg022 ++
  ed25519ScMuladdShippedSeg023 ++ ed25519ScMuladdShippedSeg024 ++
  ed25519ScMuladdShippedSeg025 ++ ed25519ScMuladdShippedSeg026 ++
  ed25519ScMuladdShippedSeg027 ++ ed25519ScMuladdShippedSeg028 ++
  ed25519ScMuladdShippedSeg029 ++ ed25519ScMuladdShippedSeg030 ++
  ed25519ScMuladdShippedSeg031 ++ ed25519ScMuladdShippedSeg032

/-- Part 2 has 512 instructions. -/
theorem ed25519ScMuladdShippedPart02_length :
    ed25519ScMuladdShippedPart02.length = 512 := by
  unfold ed25519ScMuladdShippedPart02
  simp only [List.length_append]
  rfl

/-- Part 3 of the body: segments 33–48. -/
def ed25519ScMuladdShippedPart03 : List (JInstr 64) :=
  ed25519ScMuladdShippedSeg033 ++ ed25519ScMuladdShippedSeg034 ++
  ed25519ScMuladdShippedSeg035 ++ ed25519ScMuladdShippedSeg036 ++
  ed25519ScMuladdShippedSeg037 ++ ed25519ScMuladdShippedSeg038 ++
  ed25519ScMuladdShippedSeg039 ++ ed25519ScMuladdShippedSeg040 ++
  ed25519ScMuladdShippedSeg041 ++ ed25519ScMuladdShippedSeg042 ++
  ed25519ScMuladdShippedSeg043 ++ ed25519ScMuladdShippedSeg044 ++
  ed25519ScMuladdShippedSeg045 ++ ed25519ScMuladdShippedSeg046 ++
  ed25519ScMuladdShippedSeg047 ++ ed25519ScMuladdShippedSeg048

/-- Part 3 has 512 instructions. -/
theorem ed25519ScMuladdShippedPart03_length :
    ed25519ScMuladdShippedPart03.length = 512 := by
  unfold ed25519ScMuladdShippedPart03
  simp only [List.length_append]
  rfl

/-- Part 4 of the body: segments 49–64. -/
def ed25519ScMuladdShippedPart04 : List (JInstr 64) :=
  ed25519ScMuladdShippedSeg049 ++ ed25519ScMuladdShippedSeg050 ++
  ed25519ScMuladdShippedSeg051 ++ ed25519ScMuladdShippedSeg052 ++
  ed25519ScMuladdShippedSeg053 ++ ed25519ScMuladdShippedSeg054 ++
  ed25519ScMuladdShippedSeg055 ++ ed25519ScMuladdShippedSeg056 ++
  ed25519ScMuladdShippedSeg057 ++ ed25519ScMuladdShippedSeg058 ++
  ed25519ScMuladdShippedSeg059 ++ ed25519ScMuladdShippedSeg060 ++
  ed25519ScMuladdShippedSeg061 ++ ed25519ScMuladdShippedSeg062 ++
  ed25519ScMuladdShippedSeg063 ++ ed25519ScMuladdShippedSeg064

/-- Part 4 has 512 instructions. -/
theorem ed25519ScMuladdShippedPart04_length :
    ed25519ScMuladdShippedPart04.length = 512 := by
  unfold ed25519ScMuladdShippedPart04
  simp only [List.length_append]
  rfl

/-- Part 5 of the body: segments 65–80. -/
def ed25519ScMuladdShippedPart05 : List (JInstr 64) :=
  ed25519ScMuladdShippedSeg065 ++ ed25519ScMuladdShippedSeg066 ++
  ed25519ScMuladdShippedSeg067 ++ ed25519ScMuladdShippedSeg068 ++
  ed25519ScMuladdShippedSeg069 ++ ed25519ScMuladdShippedSeg070 ++
  ed25519ScMuladdShippedSeg071 ++ ed25519ScMuladdShippedSeg072 ++
  ed25519ScMuladdShippedSeg073 ++ ed25519ScMuladdShippedSeg074 ++
  ed25519ScMuladdShippedSeg075 ++ ed25519ScMuladdShippedSeg076 ++
  ed25519ScMuladdShippedSeg077 ++ ed25519ScMuladdShippedSeg078 ++
  ed25519ScMuladdShippedSeg079 ++ ed25519ScMuladdShippedSeg080

/-- Part 5 has 512 instructions. -/
theorem ed25519ScMuladdShippedPart05_length :
    ed25519ScMuladdShippedPart05.length = 512 := by
  unfold ed25519ScMuladdShippedPart05
  simp only [List.length_append]
  rfl

/-- Part 6 of the body: segments 81–96. -/
def ed25519ScMuladdShippedPart06 : List (JInstr 64) :=
  ed25519ScMuladdShippedSeg081 ++ ed25519ScMuladdShippedSeg082 ++
  ed25519ScMuladdShippedSeg083 ++ ed25519ScMuladdShippedSeg084 ++
  ed25519ScMuladdShippedSeg085 ++ ed25519ScMuladdShippedSeg086 ++
  ed25519ScMuladdShippedSeg087 ++ ed25519ScMuladdShippedSeg088 ++
  ed25519ScMuladdShippedSeg089 ++ ed25519ScMuladdShippedSeg090 ++
  ed25519ScMuladdShippedSeg091 ++ ed25519ScMuladdShippedSeg092 ++
  ed25519ScMuladdShippedSeg093 ++ ed25519ScMuladdShippedSeg094 ++
  ed25519ScMuladdShippedSeg095 ++ ed25519ScMuladdShippedSeg096

/-- Part 6 has 512 instructions. -/
theorem ed25519ScMuladdShippedPart06_length :
    ed25519ScMuladdShippedPart06.length = 512 := by
  unfold ed25519ScMuladdShippedPart06
  simp only [List.length_append]
  rfl

/-- Part 7 of the body: segments 97–112. -/
def ed25519ScMuladdShippedPart07 : List (JInstr 64) :=
  ed25519ScMuladdShippedSeg097 ++ ed25519ScMuladdShippedSeg098 ++
  ed25519ScMuladdShippedSeg099 ++ ed25519ScMuladdShippedSeg100 ++
  ed25519ScMuladdShippedSeg101 ++ ed25519ScMuladdShippedSeg102 ++
  ed25519ScMuladdShippedSeg103 ++ ed25519ScMuladdShippedSeg104 ++
  ed25519ScMuladdShippedSeg105 ++ ed25519ScMuladdShippedSeg106 ++
  ed25519ScMuladdShippedSeg107 ++ ed25519ScMuladdShippedSeg108 ++
  ed25519ScMuladdShippedSeg109 ++ ed25519ScMuladdShippedSeg110 ++
  ed25519ScMuladdShippedSeg111 ++ ed25519ScMuladdShippedSeg112

/-- Part 7 has 512 instructions. -/
theorem ed25519ScMuladdShippedPart07_length :
    ed25519ScMuladdShippedPart07.length = 512 := by
  unfold ed25519ScMuladdShippedPart07
  simp only [List.length_append]
  rfl

/-- Part 8 of the body: segments 113–128. -/
def ed25519ScMuladdShippedPart08 : List (JInstr 64) :=
  ed25519ScMuladdShippedSeg113 ++ ed25519ScMuladdShippedSeg114 ++
  ed25519ScMuladdShippedSeg115 ++ ed25519ScMuladdShippedSeg116 ++
  ed25519ScMuladdShippedSeg117 ++ ed25519ScMuladdShippedSeg118 ++
  ed25519ScMuladdShippedSeg119 ++ ed25519ScMuladdShippedSeg120 ++
  ed25519ScMuladdShippedSeg121 ++ ed25519ScMuladdShippedSeg122 ++
  ed25519ScMuladdShippedSeg123 ++ ed25519ScMuladdShippedSeg124 ++
  ed25519ScMuladdShippedSeg125 ++ ed25519ScMuladdShippedSeg126 ++
  ed25519ScMuladdShippedSeg127 ++ ed25519ScMuladdShippedSeg128

/-- Part 8 has 512 instructions. -/
theorem ed25519ScMuladdShippedPart08_length :
    ed25519ScMuladdShippedPart08.length = 512 := by
  unfold ed25519ScMuladdShippedPart08
  simp only [List.length_append]
  rfl

/-- Part 9 of the body: segments 129–138. -/
def ed25519ScMuladdShippedPart09 : List (JInstr 64) :=
  ed25519ScMuladdShippedSeg129 ++ ed25519ScMuladdShippedSeg130 ++
  ed25519ScMuladdShippedSeg131 ++ ed25519ScMuladdShippedSeg132 ++
  ed25519ScMuladdShippedSeg133 ++ ed25519ScMuladdShippedSeg134 ++
  ed25519ScMuladdShippedSeg135 ++ ed25519ScMuladdShippedSeg136 ++
  ed25519ScMuladdShippedSeg137 ++ ed25519ScMuladdShippedSeg138

/-- Part 9 has 282 instructions. -/
theorem ed25519ScMuladdShippedPart09_length :
    ed25519ScMuladdShippedPart09.length = 282 := by
  unfold ed25519ScMuladdShippedPart09
  simp only [List.length_append]
  rfl

/-- The body of `ed25519_sc_muladd_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 138 segments,
    grouped in 9 parts. -/
def ed25519ScMuladdShippedBlock : List (JInstr 64) :=
  ed25519ScMuladdShippedPart01 ++ ed25519ScMuladdShippedPart02 ++
  ed25519ScMuladdShippedPart03 ++ ed25519ScMuladdShippedPart04 ++
  ed25519ScMuladdShippedPart05 ++ ed25519ScMuladdShippedPart06 ++
  ed25519ScMuladdShippedPart07 ++ ed25519ScMuladdShippedPart08 ++
  ed25519ScMuladdShippedPart09

/-- The block has 4354 instructions; the count of each part is a lemma above. -/
theorem ed25519ScMuladdShippedBlock_length :
    ed25519ScMuladdShippedBlock.length = 4354 := by
  unfold ed25519ScMuladdShippedBlock
  simp only [List.length_append, ed25519ScMuladdShippedPart01_length,
    ed25519ScMuladdShippedPart02_length, ed25519ScMuladdShippedPart03_length,
    ed25519ScMuladdShippedPart04_length, ed25519ScMuladdShippedPart05_length,
    ed25519ScMuladdShippedPart06_length, ed25519ScMuladdShippedPart07_length,
    ed25519ScMuladdShippedPart08_length, ed25519ScMuladdShippedPart09_length]

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScMuladdShipped
