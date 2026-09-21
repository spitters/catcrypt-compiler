/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# `ed25519_point_add` from the owned backend's output as a `JInstr 64` block

`ed25519PointAddShippedBlock` is the body of the function `ed25519_point_add` in an
x86-64 AT&T file printed by CatCrypt's owned backend, translated instruction by
instruction. The file's producer is recorded in `PROVENANCE.md` next to it, where
one exists.

## Provenance

* Source: `crates/catcrypt-ed25519/asm/ed25519_point_add_x86_from_lean.s` in the
  `SSProve-lean` repository at commit `b294647590404f72dd82b5404e326511f3c055eb`
  (tracked and unchanged at that commit), file SHA-256
  `5b3cf92957bab88e115f700584ec50bd14a37bbe9e26f815076d2b95b856e022`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 3 frame instructions,
  each checked by the importer: the stack allocation `leaq -400(%rsp), %rsp` and
  its release `leaq 400(%rsp), %rsp`; `ret`.
* `ed25519PointAddShippedPrologue` and `ed25519PointAddShippedEpilogue` are the
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
* Each of the 585 pairs `setc %r8; movzbq %r8, %r64` on one register is the single
  element `setc r64` (`JasminModel.evalInstr_setc_eq_setcc_movzx`); its comment
  gives both source instructions.
* The 144 instructions `movl $imm, %r32` are `mov r64 (.imm imm)`: both write the
  zero-extended immediate and no flag.
* The 639 instructions `btq $k, %r` are `bt`, which writes `CF` only. The Intel SDM
  leaves `OF`, `SF` and `PF` undefined after `BT`; the importer checks that no
  `adox` reads `OF` before a later instruction writes it.

The block has 4909 instructions. Source instructions by mnemonic: `movq` 2258,
`adcxq` 639, `btq` 639, `movzbq` 585, `setc` 585, `imulq` 189, `mulx` 189, `movl`
144, `cmovneq` 117, `testq` 117, `orq` 16, `xorq` 16.

## Main definitions

* `ed25519PointAddShippedSeg001` … `ed25519PointAddShippedSeg155`: the block in
  155 segments, each a literal `List (JInstr 64)`. A segment ends after a call,
  after the entry run of `%rsp` stores, before the exit run of `%rsp` loads, and
  after 32 instructions.
* `ed25519PointAddShippedPart01` … `ed25519PointAddShippedPart10`: the segments
  in 10 parts of at most 16 consecutive segments, each with lemmas giving its
  instruction count.
* `ed25519PointAddShippedBlock`: the block, the concatenation of the parts.
* `ed25519PointAddShippedPrologue`, `ed25519PointAddShippedEpilogue`: the frame
  instructions before and after the block.

## Main results

* `ed25519PointAddShippedBlock_length`: the block has 4909 instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 8 instructions from source lines 6–13. -/
def ed25519PointAddShippedSeg001 : List (JInstr 64) :=
  [ .storeMem "%rsp" 392 (.reg "%rdi"),  -- l.6 `movq %rdi, 392(%rsp)`
    .storeMem "%rsp" 384 (.reg "%rsi"),  -- l.7 `movq %rsi, 384(%rsp)`
    .storeMem "%rsp" 376 (.reg "%rbx"),  -- l.8 `movq %rbx, 376(%rsp)`
    .storeMem "%rsp" 368 (.reg "%rbp"),  -- l.9 `movq %rbp, 368(%rsp)`
    .storeMem "%rsp" 360 (.reg "%r12"),  -- l.10 `movq %r12, 360(%rsp)`
    .storeMem "%rsp" 352 (.reg "%r13"),  -- l.11 `movq %r13, 352(%rsp)`
    .storeMem "%rsp" 344 (.reg "%r14"),  -- l.12 `movq %r14, 344(%rsp)`
    .storeMem "%rsp" 336 (.reg "%r15") ]  -- l.13 `movq %r15, 336(%rsp)`

/-- Segment 2 of the body: the 32 instructions from source lines 14–45. -/
def ed25519PointAddShippedSeg002 : List (JInstr 64) :=
  [ .mov "%r14" (.reg "%rsi"),  -- l.14 `movq %rsi, %r14`
    .loadMem "%r14" "%rsp" 384,  -- l.15 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 248,  -- l.16 `movq 248(%r14), %r15`
    .storeMem "%rsp" 296 (.reg "%r15"),  -- l.17 `movq %r15, 296(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.18 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 240,  -- l.19 `movq 240(%r14), %r15`
    .storeMem "%rsp" 288 (.reg "%r15"),  -- l.20 `movq %r15, 288(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.21 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 232,  -- l.22 `movq 232(%r14), %r15`
    .storeMem "%rsp" 280 (.reg "%r15"),  -- l.23 `movq %r15, 280(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.24 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 224,  -- l.25 `movq 224(%r14), %r15`
    .storeMem "%rsp" 272 (.reg "%r15"),  -- l.26 `movq %r15, 272(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.27 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 216,  -- l.28 `movq 216(%r14), %r15`
    .storeMem "%rsp" 328 (.reg "%r15"),  -- l.29 `movq %r15, 328(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.30 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 208,  -- l.31 `movq 208(%r14), %r15`
    .storeMem "%rsp" 320 (.reg "%r15"),  -- l.32 `movq %r15, 320(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.33 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 200,  -- l.34 `movq 200(%r14), %r15`
    .storeMem "%rsp" 312 (.reg "%r15"),  -- l.35 `movq %r15, 312(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.36 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 192,  -- l.37 `movq 192(%r14), %r15`
    .storeMem "%rsp" 304 (.reg "%r15"),  -- l.38 `movq %r15, 304(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.39 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 184,  -- l.40 `movq 184(%r14), %r15`
    .storeMem "%rsp" 136 (.reg "%r15"),  -- l.41 `movq %r15, 136(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.42 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 176,  -- l.43 `movq 176(%r14), %r15`
    .storeMem "%rsp" 128 (.reg "%r15"),  -- l.44 `movq %r15, 128(%rsp)`
    .loadMem "%r14" "%rsp" 384 ]  -- l.45 `movq 384(%rsp), %r14`

/-- Segment 3 of the body: the 32 instructions from source lines 46–77. -/
def ed25519PointAddShippedSeg003 : List (JInstr 64) :=
  [ .loadMem "%r15" "%r14" 168,  -- l.46 `movq 168(%r14), %r15`
    .storeMem "%rsp" 120 (.reg "%r15"),  -- l.47 `movq %r15, 120(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.48 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 160,  -- l.49 `movq 160(%r14), %r15`
    .storeMem "%rsp" 112 (.reg "%r15"),  -- l.50 `movq %r15, 112(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.51 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 152,  -- l.52 `movq 152(%r14), %r15`
    .storeMem "%rsp" 264 (.reg "%r15"),  -- l.53 `movq %r15, 264(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.54 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 144,  -- l.55 `movq 144(%r14), %r15`
    .storeMem "%rsp" 224 (.reg "%r15"),  -- l.56 `movq %r15, 224(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.57 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 136,  -- l.58 `movq 136(%r14), %r15`
    .storeMem "%rsp" 216 (.reg "%r15"),  -- l.59 `movq %r15, 216(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.60 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 128,  -- l.61 `movq 128(%r14), %r15`
    .storeMem "%rsp" 208 (.reg "%r15"),  -- l.62 `movq %r15, 208(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.63 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 120,  -- l.64 `movq 120(%r14), %r15`
    .storeMem "%rsp" 200 (.reg "%r15"),  -- l.65 `movq %r15, 200(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.66 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 112,  -- l.67 `movq 112(%r14), %r15`
    .storeMem "%rsp" 192 (.reg "%r15"),  -- l.68 `movq %r15, 192(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.69 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 104,  -- l.70 `movq 104(%r14), %r15`
    .storeMem "%rsp" 176 (.reg "%r15"),  -- l.71 `movq %r15, 176(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.72 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 96,  -- l.73 `movq 96(%r14), %r15`
    .storeMem "%rsp" 160 (.reg "%r15"),  -- l.74 `movq %r15, 160(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.75 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 88,  -- l.76 `movq 88(%r14), %r15`
    .storeMem "%rsp" 256 (.reg "%r15") ]  -- l.77 `movq %r15, 256(%rsp)`

/-- Segment 4 of the body: the 32 instructions from source lines 78–109. -/
def ed25519PointAddShippedSeg004 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 384,  -- l.78 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 80,  -- l.79 `movq 80(%r14), %r15`
    .storeMem "%rsp" 248 (.reg "%r15"),  -- l.80 `movq %r15, 248(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.81 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 72,  -- l.82 `movq 72(%r14), %r15`
    .storeMem "%rsp" 240 (.reg "%r15"),  -- l.83 `movq %r15, 240(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.84 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 64,  -- l.85 `movq 64(%r14), %r15`
    .storeMem "%rsp" 232 (.reg "%r15"),  -- l.86 `movq %r15, 232(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.87 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 56,  -- l.88 `movq 56(%r14), %r15`
    .storeMem "%rsp" 104 (.reg "%r15"),  -- l.89 `movq %r15, 104(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.90 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 48,  -- l.91 `movq 48(%r14), %r15`
    .storeMem "%rsp" 96 (.reg "%r15"),  -- l.92 `movq %r15, 96(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.93 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 40,  -- l.94 `movq 40(%r14), %r15`
    .storeMem "%rsp" 88 (.reg "%r15"),  -- l.95 `movq %r15, 88(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.96 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 32,  -- l.97 `movq 32(%r14), %r15`
    .storeMem "%rsp" 80 (.reg "%r15"),  -- l.98 `movq %r15, 80(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.99 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 24,  -- l.100 `movq 24(%r14), %r15`
    .storeMem "%rsp" 184 (.reg "%r15"),  -- l.101 `movq %r15, 184(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.102 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 16,  -- l.103 `movq 16(%r14), %r15`
    .storeMem "%rsp" 168 (.reg "%r15"),  -- l.104 `movq %r15, 168(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.105 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 8,  -- l.106 `movq 8(%r14), %r15`
    .storeMem "%rsp" 152 (.reg "%r15"),  -- l.107 `movq %r15, 152(%rsp)`
    .loadMem "%r14" "%rsp" 384,  -- l.108 `movq 384(%rsp), %r14`
    .loadMem "%r15" "%r14" 0 ]  -- l.109 `movq (%r14), %r15`

/-- Segment 5 of the body: the 32 instructions from source lines 110–145. -/
def ed25519PointAddShippedSeg005 : List (JInstr 64) :=
  [ .storeMem "%rsp" 144 (.reg "%r15"),  -- l.110 `movq %r15, 144(%rsp)`
    .mov "%rax" (.imm 18446744073709551615),  -- l.111 `movq $18446744073709551615, %rax`
    .loadMem "%r8" "%rsp" 144,  -- l.112 `movq 144(%rsp), %r8`
    .xor_ "%r8" (.reg "%rax"),  -- l.113 `xorq %rax, %r8`
    .loadMem "%rdi" "%rsp" 152,  -- l.114 `movq 152(%rsp), %rdi`
    .xor_ "%rdi" (.reg "%rax"),  -- l.115 `xorq %rax, %rdi`
    .loadMem "%rsi" "%rsp" 168,  -- l.116 `movq 168(%rsp), %rsi`
    .xor_ "%rsi" (.reg "%rax"),  -- l.117 `xorq %rax, %rsi`
    .loadMem "%r11" "%rsp" 184,  -- l.118 `movq 184(%rsp), %r11`
    .xor_ "%r11" (.reg "%rax"),  -- l.119 `xorq %rax, %r11`
    .mov "%rax" (.imm 1),  -- l.120 `movl $1, %eax`
    .loadMem "%r12" "%rsp" 80,  -- l.121 `movq 80(%rsp), %r12`
    .bt "%rax" (.imm 0),  -- l.122 `btq $0, %rax`
    .adcx "%r12" (.reg "%r8"),  -- l.123 `adcxq %r8, %r12`
    .setc "%r13",  -- l.124 `setc %r13b; movzbq %r13b, %r13`
    .loadMem "%rax" "%rsp" 88,  -- l.126 `movq 88(%rsp), %rax`
    .bt "%r13" (.imm 0),  -- l.127 `btq $0, %r13`
    .adcx "%rax" (.reg "%rdi"),  -- l.128 `adcxq %rdi, %rax`
    .setc "%r8",  -- l.129 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rdi" "%rsp" 96,  -- l.131 `movq 96(%rsp), %rdi`
    .bt "%r8" (.imm 0),  -- l.132 `btq $0, %r8`
    .adcx "%rdi" (.reg "%rsi"),  -- l.133 `adcxq %rsi, %rdi`
    .setc "%r13",  -- l.134 `setc %r13b; movzbq %r13b, %r13`
    .loadMem "%rsi" "%rsp" 104,  -- l.136 `movq 104(%rsp), %rsi`
    .bt "%r13" (.imm 0),  -- l.137 `btq $0, %r13`
    .adcx "%rsi" (.reg "%r11"),  -- l.138 `adcxq %r11, %rsi`
    .setc "%r8",  -- l.139 `setc %r8b; movzbq %r8b, %r8`
    .mov "%r11" (.imm 18446744073709551597),  -- l.141 `movq $18446744073709551597, %r11`
    .mov "%r13" (.imm 18446744073709551615),  -- l.142 `movq $18446744073709551615, %r13`
    .mov "%rbp" (.imm 18446744073709551615),  -- l.143 `movq $18446744073709551615, %rbp`
    .mov "%r9" (.imm 9223372036854775807),  -- l.144 `movq $9223372036854775807, %r9`
    .mov "%r10" (.imm 0) ]  -- l.145 `movl $0, %r10d`

/-- Segment 6 of the body: the 32 instructions from source lines 146–181. -/
def ed25519PointAddShippedSeg006 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%r12"),  -- l.146 `movq %r12, %rbx`
    .bt "%r10" (.imm 0),  -- l.147 `btq $0, %r10`
    .adcx "%rbx" (.reg "%r11"),  -- l.148 `adcxq %r11, %rbx`
    .setc "%rcx",  -- l.149 `setc %cl; movzbq %cl, %rcx`
    .mov "%r10" (.reg "%rax"),  -- l.151 `movq %rax, %r10`
    .bt "%rcx" (.imm 0),  -- l.152 `btq $0, %rcx`
    .adcx "%r10" (.reg "%r13"),  -- l.153 `adcxq %r13, %r10`
    .setc "%r11",  -- l.154 `setc %r11b; movzbq %r11b, %r11`
    .mov "%rcx" (.reg "%rdi"),  -- l.156 `movq %rdi, %rcx`
    .bt "%r11" (.imm 0),  -- l.157 `btq $0, %r11`
    .adcx "%rcx" (.reg "%rbp"),  -- l.158 `adcxq %rbp, %rcx`
    .setc "%r13",  -- l.159 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%rsi"),  -- l.161 `movq %rsi, %rbp`
    .bt "%r13" (.imm 0),  -- l.162 `btq $0, %r13`
    .adcx "%rbp" (.reg "%r9"),  -- l.163 `adcxq %r9, %rbp`
    .setc "%r11",  -- l.164 `setc %r11b; movzbq %r11b, %r11`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.166 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.167 `movq %rbx, %rax`
    .test "%r8" (.reg "%r8"),  -- l.168 `testq %r8, %r8`
    .cmovne "%rax" (.reg "%r12"),  -- l.169 `cmovneq %r12, %rax`
    .storeMem "%rsp" 48 (.reg "%rax"),  -- l.170 `movq %rax, 48(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.171 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.172 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%r10"),  -- l.173 `movq %r10, %rbx`
    .test "%r8" (.reg "%r8"),  -- l.174 `testq %r8, %r8`
    .cmovne "%rbx" (.reg "%rax"),  -- l.175 `cmovneq %rax, %rbx`
    .storeMem "%rsp" 56 (.reg "%rbx"),  -- l.176 `movq %rbx, 56(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.177 `movq -128(%rsp), %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.178 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.179 `movq %rcx, %rax`
    .test "%r8" (.reg "%r8"),  -- l.180 `testq %r8, %r8`
    .cmovne "%rax" (.reg "%rdi") ]  -- l.181 `cmovneq %rdi, %rax`

/-- Segment 7 of the body: the 32 instructions from source lines 182–216. -/
def ed25519PointAddShippedSeg007 : List (JInstr 64) :=
  [ .storeMem "%rsp" 64 (.reg "%rax"),  -- l.182 `movq %rax, 64(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.183 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.184 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbp"),  -- l.185 `movq %rbp, %rax`
    .test "%r8" (.reg "%r8"),  -- l.186 `testq %r8, %r8`
    .cmovne "%rax" (.reg "%rsi"),  -- l.187 `cmovneq %rsi, %rax`
    .storeMem "%rsp" 72 (.reg "%rax"),  -- l.188 `movq %rax, 72(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.189 `movq -128(%rsp), %rax`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.190 `movq $18446744073709551615, %rsi`
    .loadMem "%rdi" "%rsp" 208,  -- l.191 `movq 208(%rsp), %rdi`
    .xor_ "%rdi" (.reg "%rsi"),  -- l.192 `xorq %rsi, %rdi`
    .loadMem "%rbp" "%rsp" 216,  -- l.193 `movq 216(%rsp), %rbp`
    .xor_ "%rbp" (.reg "%rsi"),  -- l.194 `xorq %rsi, %rbp`
    .loadMem "%r8" "%rsp" 224,  -- l.195 `movq 224(%rsp), %r8`
    .xor_ "%r8" (.reg "%rsi"),  -- l.196 `xorq %rsi, %r8`
    .loadMem "%r10" "%rsp" 264,  -- l.197 `movq 264(%rsp), %r10`
    .xor_ "%r10" (.reg "%rsi"),  -- l.198 `xorq %rsi, %r10`
    .mov "%rsi" (.imm 1),  -- l.199 `movl $1, %esi`
    .loadMem "%r11" "%rsp" 112,  -- l.200 `movq 112(%rsp), %r11`
    .bt "%rsi" (.imm 0),  -- l.201 `btq $0, %rsi`
    .adcx "%r11" (.reg "%rdi"),  -- l.202 `adcxq %rdi, %r11`
    .setc "%r12",  -- l.203 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rsi" "%rsp" 120,  -- l.205 `movq 120(%rsp), %rsi`
    .bt "%r12" (.imm 0),  -- l.206 `btq $0, %r12`
    .adcx "%rsi" (.reg "%rbp"),  -- l.207 `adcxq %rbp, %rsi`
    .setc "%rdi",  -- l.208 `setc %dil; movzbq %dil, %rdi`
    .loadMem "%rbp" "%rsp" 128,  -- l.210 `movq 128(%rsp), %rbp`
    .bt "%rdi" (.imm 0),  -- l.211 `btq $0, %rdi`
    .adcx "%rbp" (.reg "%r8"),  -- l.212 `adcxq %r8, %rbp`
    .setc "%r12",  -- l.213 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rdi" "%rsp" 136,  -- l.215 `movq 136(%rsp), %rdi`
    .bt "%r12" (.imm 0) ]  -- l.216 `btq $0, %r12`

/-- Segment 8 of the body: the 32 instructions from source lines 217–253. -/
def ed25519PointAddShippedSeg008 : List (JInstr 64) :=
  [ .adcx "%rdi" (.reg "%r10"),  -- l.217 `adcxq %r10, %rdi`
    .setc "%r8",  -- l.218 `setc %r8b; movzbq %r8b, %r8`
    .mov "%r10" (.imm 18446744073709551597),  -- l.220 `movq $18446744073709551597, %r10`
    .mov "%r12" (.imm 18446744073709551615),  -- l.221 `movq $18446744073709551615, %r12`
    .mov "%r13" (.imm 18446744073709551615),  -- l.222 `movq $18446744073709551615, %r13`
    .mov "%rcx" (.imm 9223372036854775807),  -- l.223 `movq $9223372036854775807, %rcx`
    .mov "%rax" (.imm 0),  -- l.224 `movl $0, %eax`
    .mov "%rbx" (.reg "%r11"),  -- l.225 `movq %r11, %rbx`
    .bt "%rax" (.imm 0),  -- l.226 `btq $0, %rax`
    .adcx "%rbx" (.reg "%r10"),  -- l.227 `adcxq %r10, %rbx`
    .setc "%r9",  -- l.228 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rsi"),  -- l.230 `movq %rsi, %rax`
    .bt "%r9" (.imm 0),  -- l.231 `btq $0, %r9`
    .adcx "%rax" (.reg "%r12"),  -- l.232 `adcxq %r12, %rax`
    .setc "%r10",  -- l.233 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%rbp"),  -- l.235 `movq %rbp, %r9`
    .bt "%r10" (.imm 0),  -- l.236 `btq $0, %r10`
    .adcx "%r9" (.reg "%r13"),  -- l.237 `adcxq %r13, %r9`
    .setc "%r12",  -- l.238 `setc %r12b; movzbq %r12b, %r12`
    .mov "%r10" (.reg "%rdi"),  -- l.240 `movq %rdi, %r10`
    .bt "%r12" (.imm 0),  -- l.241 `btq $0, %r12`
    .adcx "%r10" (.reg "%rcx"),  -- l.242 `adcxq %rcx, %r10`
    .setc "%r13",  -- l.243 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rcx" (.reg "%rbx"),  -- l.245 `movq %rbx, %rcx`
    .test "%r8" (.reg "%r8"),  -- l.246 `testq %r8, %r8`
    .cmovne "%rcx" (.reg "%r11"),  -- l.247 `cmovneq %r11, %rcx`
    .mov "%rbx" (.reg "%rax"),  -- l.248 `movq %rax, %rbx`
    .test "%r8" (.reg "%r8"),  -- l.249 `testq %r8, %r8`
    .cmovne "%rbx" (.reg "%rsi"),  -- l.250 `cmovneq %rsi, %rbx`
    .mov "%rax" (.reg "%r9"),  -- l.251 `movq %r9, %rax`
    .test "%r8" (.reg "%r8"),  -- l.252 `testq %r8, %r8`
    .cmovne "%rax" (.reg "%rbp") ]  -- l.253 `cmovneq %rbp, %rax`

/-- Segment 9 of the body: the 32 instructions from source lines 254–287. -/
def ed25519PointAddShippedSeg009 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.254 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r10"),  -- l.255 `movq %r10, %rax`
    .test "%r8" (.reg "%r8"),  -- l.256 `testq %r8, %r8`
    .cmovne "%rax" (.reg "%rdi"),  -- l.257 `cmovneq %rdi, %rax`
    .storeMem "%rsp" 32 (.reg "%rax"),  -- l.258 `movq %rax, 32(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.259 `movq -128(%rsp), %rax`
    .mov "%rdi" (.imm 0),  -- l.260 `movq $0, %rdi`
    .mov "%rbp" (.imm 0),  -- l.261 `movl $0, %ebp`
    .loadMem "%r8" "%rsp" 48,  -- l.262 `movq 48(%rsp), %r8`
    .imul "%r8" (.reg "%rcx"),  -- l.263 `imulq %rcx, %r8`
    .loadMem "%rdx" "%rsp" 48,  -- l.264 `movq 48(%rsp), %rdx`
    .mulx "%r9" "%r8" (.reg "%rdx") (.reg "%rcx"),  -- l.265 `mulx %rcx, %r8, %r9`
    .bt "%rbp" (.imm 0),  -- l.266 `btq $0, %rbp`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.267 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.268 `movq %r8, %rax`
    .adcx "%rax" (.reg "%rdi"),  -- l.269 `adcxq %rdi, %rax`
    .storeMem "%rsp" 40 (.reg "%rax"),  -- l.270 `movq %rax, 40(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.271 `movq -128(%rsp), %rax`
    .setc "%r11",  -- l.272 `setc %r11b; movzbq %r11b, %r11`
    .loadMem "%rbp" "%rsp" 56,  -- l.274 `movq 56(%rsp), %rbp`
    .imul "%rbp" (.reg "%rcx"),  -- l.275 `imulq %rcx, %rbp`
    .loadMem "%rdx" "%rsp" 56,  -- l.276 `movq 56(%rsp), %rdx`
    .mulx "%r8" "%rbp" (.reg "%rdx") (.reg "%rcx"),  -- l.277 `mulx %rcx, %rbp, %r8`
    .mov "%r12" (.reg "%rbp"),  -- l.278 `movq %rbp, %r12`
    .bt "%r11" (.imm 0),  -- l.279 `btq $0, %r11`
    .adcx "%r12" (.reg "%r9"),  -- l.280 `adcxq %r9, %r12`
    .setc "%r13",  -- l.281 `setc %r13b; movzbq %r13b, %r13`
    .loadMem "%rbp" "%rsp" 64,  -- l.283 `movq 64(%rsp), %rbp`
    .imul "%rbp" (.reg "%rcx"),  -- l.284 `imulq %rcx, %rbp`
    .loadMem "%rdx" "%rsp" 64,  -- l.285 `movq 64(%rsp), %rdx`
    .mulx "%r9" "%rbp" (.reg "%rdx") (.reg "%rcx"),  -- l.286 `mulx %rcx, %rbp, %r9`
    .mov "%r11" (.reg "%rbp") ]  -- l.287 `movq %rbp, %r11`

/-- Segment 10 of the body: the 32 instructions from source lines 288–322. -/
def ed25519PointAddShippedSeg010 : List (JInstr 64) :=
  [ .bt "%r13" (.imm 0),  -- l.288 `btq $0, %r13`
    .adcx "%r11" (.reg "%r8"),  -- l.289 `adcxq %r8, %r11`
    .setc "%r10",  -- l.290 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rbp" "%rsp" 72,  -- l.292 `movq 72(%rsp), %rbp`
    .imul "%rbp" (.reg "%rcx"),  -- l.293 `imulq %rcx, %rbp`
    .loadMem "%rdx" "%rsp" 72,  -- l.294 `movq 72(%rsp), %rdx`
    .mulx "%r8" "%rbp" (.reg "%rdx") (.reg "%rcx"),  -- l.295 `mulx %rcx, %rbp, %r8`
    .bt "%r10" (.imm 0),  -- l.296 `btq $0, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.297 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbp"),  -- l.298 `movq %rbp, %rax`
    .adcx "%rax" (.reg "%r9"),  -- l.299 `adcxq %r9, %rax`
    .storeMem "%rsp" 16 (.reg "%rax"),  -- l.300 `movq %rax, 16(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.301 `movq -128(%rsp), %rax`
    .setc "%r13",  -- l.302 `setc %r13b; movzbq %r13b, %r13`
    .bt "%r13" (.imm 0),  -- l.304 `btq $0, %r13`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.305 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.306 `movq %r8, %rax`
    .adcx "%rax" (.reg "%rdi"),  -- l.307 `adcxq %rdi, %rax`
    .storeMem "%rsp" 24 (.reg "%rax"),  -- l.308 `movq %rax, 24(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.309 `movq -128(%rsp), %rax`
    .mov "%rdi" (.imm 0),  -- l.310 `movq $0, %rdi`
    .mov "%r8" (.imm 0),  -- l.311 `movl $0, %r8d`
    .loadMem "%r9" "%rsp" 48,  -- l.312 `movq 48(%rsp), %r9`
    .imul "%r9" (.reg "%rbx"),  -- l.313 `imulq %rbx, %r9`
    .loadMem "%rdx" "%rsp" 48,  -- l.314 `movq 48(%rsp), %rdx`
    .mulx "%r10" "%r9" (.reg "%rdx") (.reg "%rbx"),  -- l.315 `mulx %rbx, %r9, %r10`
    .mov "%r13" (.reg "%r9"),  -- l.316 `movq %r9, %r13`
    .bt "%r8" (.imm 0),  -- l.317 `btq $0, %r8`
    .adcx "%r13" (.reg "%rdi"),  -- l.318 `adcxq %rdi, %r13`
    .setc "%rsi",  -- l.319 `setc %sil; movzbq %sil, %rsi`
    .loadMem "%r8" "%rsp" 56,  -- l.321 `movq 56(%rsp), %r8`
    .imul "%r8" (.reg "%rbx") ]  -- l.322 `imulq %rbx, %r8`

/-- Segment 11 of the body: the 32 instructions from source lines 323–357. -/
def ed25519PointAddShippedSeg011 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsp" 56,  -- l.323 `movq 56(%rsp), %rdx`
    .mulx "%r9" "%r8" (.reg "%rdx") (.reg "%rbx"),  -- l.324 `mulx %rbx, %r8, %r9`
    .mov "%rbp" (.reg "%r8"),  -- l.325 `movq %r8, %rbp`
    .bt "%rsi" (.imm 0),  -- l.326 `btq $0, %rsi`
    .adcx "%rbp" (.reg "%r10"),  -- l.327 `adcxq %r10, %rbp`
    .setc "%rcx",  -- l.328 `setc %cl; movzbq %cl, %rcx`
    .loadMem "%rsi" "%rsp" 64,  -- l.330 `movq 64(%rsp), %rsi`
    .imul "%rsi" (.reg "%rbx"),  -- l.331 `imulq %rbx, %rsi`
    .loadMem "%rdx" "%rsp" 64,  -- l.332 `movq 64(%rsp), %rdx`
    .mulx "%r8" "%rsi" (.reg "%rdx") (.reg "%rbx"),  -- l.333 `mulx %rbx, %rsi, %r8`
    .bt "%rcx" (.imm 0),  -- l.334 `btq $0, %rcx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.335 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rsi"),  -- l.336 `movq %rsi, %rax`
    .adcx "%rax" (.reg "%r9"),  -- l.337 `adcxq %r9, %rax`
    .storeMem "%rsp" 8 (.reg "%rax"),  -- l.338 `movq %rax, 8(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.339 `movq -128(%rsp), %rax`
    .setc "%r10",  -- l.340 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rcx" "%rsp" 72,  -- l.342 `movq 72(%rsp), %rcx`
    .imul "%rcx" (.reg "%rbx"),  -- l.343 `imulq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 72,  -- l.344 `movq 72(%rsp), %rdx`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%rbx"),  -- l.345 `mulx %rbx, %rcx, %rsi`
    .mov "%rbx" (.reg "%rcx"),  -- l.346 `movq %rcx, %rbx`
    .bt "%r10" (.imm 0),  -- l.347 `btq $0, %r10`
    .adcx "%rbx" (.reg "%r8"),  -- l.348 `adcxq %r8, %rbx`
    .setc "%r9",  -- l.349 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rsi"),  -- l.351 `movq %rsi, %rcx`
    .bt "%r9" (.imm 0),  -- l.352 `btq $0, %r9`
    .adcx "%rcx" (.reg "%rdi"),  -- l.353 `adcxq %rdi, %rcx`
    .mov "%rsi" (.imm 0),  -- l.354 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.355 `movl $0, %edi`
    .bt "%rdi" (.imm 0),  -- l.356 `btq $0, %rdi`
    .storeMem "%rsp" (-128) (.reg "%rax") ]  -- l.357 `movq %rax, -128(%rsp)`

/-- Segment 12 of the body: the 32 instructions from source lines 358–394. -/
def ed25519PointAddShippedSeg012 : List (JInstr 64) :=
  [ .mov "%rax" (.reg "%r12"),  -- l.358 `movq %r12, %rax`
    .adcx "%rax" (.reg "%r13"),  -- l.359 `adcxq %r13, %rax`
    .storeMem "%rsp" 0 (.reg "%rax"),  -- l.360 `movq %rax, 0(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.361 `movq -128(%rsp), %rax`
    .setc "%r9",  -- l.362 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rdi" (.reg "%r11"),  -- l.364 `movq %r11, %rdi`
    .bt "%r9" (.imm 0),  -- l.365 `btq $0, %r9`
    .adcx "%rdi" (.reg "%rbp"),  -- l.366 `adcxq %rbp, %rdi`
    .setc "%r10",  -- l.367 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rbp" "%rsp" 16,  -- l.369 `movq 16(%rsp), %rbp`
    .bt "%r10" (.imm 0),  -- l.370 `btq $0, %r10`
    .adcxMem "%rbp" "%rsp" 8,  -- l.371 `adcxq 8(%rsp), %rbp`
    .setc "%r9",  -- l.372 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%r10" "%rsp" 24,  -- l.374 `movq 24(%rsp), %r10`
    .bt "%r9" (.imm 0),  -- l.375 `btq $0, %r9`
    .adcx "%r10" (.reg "%rbx"),  -- l.376 `adcxq %rbx, %r10`
    .setc "%r11",  -- l.377 `setc %r11b; movzbq %r11b, %r11`
    .bt "%r11" (.imm 0),  -- l.379 `btq $0, %r11`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.380 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rsi"),  -- l.381 `movq %rsi, %rax`
    .adcx "%rax" (.reg "%rcx"),  -- l.382 `adcxq %rcx, %rax`
    .storeMem "%rsp" 24 (.reg "%rax"),  -- l.383 `movq %rax, 24(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.384 `movq -128(%rsp), %rax`
    .setc "%r9",  -- l.385 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.imm 0),  -- l.387 `movq $0, %rcx`
    .mov "%rsi" (.imm 0),  -- l.388 `movl $0, %esi`
    .loadMem "%r9" "%rsp" 48,  -- l.389 `movq 48(%rsp), %r9`
    .imul "%r9" (.reg "%rax"),  -- l.390 `imulq %rax, %r9`
    .loadMem "%rdx" "%rsp" 48,  -- l.391 `movq 48(%rsp), %rdx`
    .mulx "%r11" "%r9" (.reg "%rdx") (.reg "%rax"),  -- l.392 `mulx %rax, %r9, %r11`
    .mov "%r12" (.reg "%r9"),  -- l.393 `movq %r9, %r12`
    .bt "%rsi" (.imm 0) ]  -- l.394 `btq $0, %rsi`

/-- Segment 13 of the body: the 32 instructions from source lines 395–430. -/
def ed25519PointAddShippedSeg013 : List (JInstr 64) :=
  [ .adcx "%r12" (.reg "%rcx"),  -- l.395 `adcxq %rcx, %r12`
    .setc "%r13",  -- l.396 `setc %r13b; movzbq %r13b, %r13`
    .loadMem "%rsi" "%rsp" 56,  -- l.398 `movq 56(%rsp), %rsi`
    .imul "%rsi" (.reg "%rax"),  -- l.399 `imulq %rax, %rsi`
    .loadMem "%rdx" "%rsp" 56,  -- l.400 `movq 56(%rsp), %rdx`
    .mulx "%r9" "%rsi" (.reg "%rdx") (.reg "%rax"),  -- l.401 `mulx %rax, %rsi, %r9`
    .mov "%r8" (.reg "%rsi"),  -- l.402 `movq %rsi, %r8`
    .bt "%r13" (.imm 0),  -- l.403 `btq $0, %r13`
    .adcx "%r8" (.reg "%r11"),  -- l.404 `adcxq %r11, %r8`
    .setc "%rbx",  -- l.405 `setc %bl; movzbq %bl, %rbx`
    .loadMem "%rsi" "%rsp" 64,  -- l.407 `movq 64(%rsp), %rsi`
    .imul "%rsi" (.reg "%rax"),  -- l.408 `imulq %rax, %rsi`
    .loadMem "%rdx" "%rsp" 64,  -- l.409 `movq 64(%rsp), %rdx`
    .mulx "%r11" "%rsi" (.reg "%rdx") (.reg "%rax"),  -- l.410 `mulx %rax, %rsi, %r11`
    .bt "%rbx" (.imm 0),  -- l.411 `btq $0, %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.412 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rsi"),  -- l.413 `movq %rsi, %rax`
    .adcx "%rax" (.reg "%r9"),  -- l.414 `adcxq %r9, %rax`
    .storeMem "%rsp" 16 (.reg "%rax"),  -- l.415 `movq %rax, 16(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.416 `movq -128(%rsp), %rax`
    .setc "%r13",  -- l.417 `setc %r13b; movzbq %r13b, %r13`
    .loadMem "%rbx" "%rsp" 72,  -- l.419 `movq 72(%rsp), %rbx`
    .imul "%rbx" (.reg "%rax"),  -- l.420 `imulq %rax, %rbx`
    .loadMem "%rdx" "%rsp" 72,  -- l.421 `movq 72(%rsp), %rdx`
    .mulx "%rsi" "%rbx" (.reg "%rdx") (.reg "%rax"),  -- l.422 `mulx %rax, %rbx, %rsi`
    .mov "%rax" (.reg "%rbx"),  -- l.423 `movq %rbx, %rax`
    .bt "%r13" (.imm 0),  -- l.424 `btq $0, %r13`
    .adcx "%rax" (.reg "%r11"),  -- l.425 `adcxq %r11, %rax`
    .setc "%r9",  -- l.426 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbx" (.reg "%rsi"),  -- l.428 `movq %rsi, %rbx`
    .bt "%r9" (.imm 0),  -- l.429 `btq $0, %r9`
    .adcx "%rbx" (.reg "%rcx") ]  -- l.430 `adcxq %rcx, %rbx`

/-- Segment 14 of the body: the 32 instructions from source lines 431–467. -/
def ed25519PointAddShippedSeg014 : List (JInstr 64) :=
  [ .mov "%rcx" (.imm 0),  -- l.431 `movq $0, %rcx`
    .mov "%rsi" (.imm 0),  -- l.432 `movl $0, %esi`
    .bt "%rsi" (.imm 0),  -- l.433 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.434 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.435 `movq %rdi, %rax`
    .adcx "%rax" (.reg "%r12"),  -- l.436 `adcxq %r12, %rax`
    .storeMem "%rsp" 8 (.reg "%rax"),  -- l.437 `movq %rax, 8(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.438 `movq -128(%rsp), %rax`
    .setc "%r11",  -- l.439 `setc %r11b; movzbq %r11b, %r11`
    .mov "%rsi" (.reg "%rbp"),  -- l.441 `movq %rbp, %rsi`
    .bt "%r11" (.imm 0),  -- l.442 `btq $0, %r11`
    .adcx "%rsi" (.reg "%r8"),  -- l.443 `adcxq %r8, %rsi`
    .setc "%rdi",  -- l.444 `setc %dil; movzbq %dil, %rdi`
    .mov "%rbp" (.reg "%r10"),  -- l.446 `movq %r10, %rbp`
    .bt "%rdi" (.imm 0),  -- l.447 `btq $0, %rdi`
    .adcxMem "%rbp" "%rsp" 16,  -- l.448 `adcxq 16(%rsp), %rbp`
    .setc "%r8",  -- l.449 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rdi" "%rsp" 24,  -- l.451 `movq 24(%rsp), %rdi`
    .bt "%r8" (.imm 0),  -- l.452 `btq $0, %r8`
    .adcx "%rdi" (.reg "%rax"),  -- l.453 `adcxq %rax, %rdi`
    .setc "%r10",  -- l.454 `setc %r10b; movzbq %r10b, %r10`
    .bt "%r10" (.imm 0),  -- l.456 `btq $0, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.457 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.458 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%rbx"),  -- l.459 `adcxq %rbx, %rax`
    .storeMem "%rsp" 24 (.reg "%rax"),  -- l.460 `movq %rax, 24(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.461 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.462 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rbx" (.imm 0),  -- l.464 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.465 `movl $0, %ecx`
    .loadMem "%r8" "%rsp" 48,  -- l.466 `movq 48(%rsp), %r8`
    .loadMem "%r15" "%rsp" 32 ]  -- l.467 `movq 32(%rsp), %r15`

/-- Segment 15 of the body: the 32 instructions from source lines 468–502. -/
def ed25519PointAddShippedSeg015 : List (JInstr 64) :=
  [ .imul "%r8" (.reg "%r15"),  -- l.468 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 48,  -- l.469 `movq 48(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.470 `movq 32(%rsp), %r14`
    .mulx "%r10" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.471 `mulx %r14, %r8, %r10`
    .mov "%r11" (.reg "%r8"),  -- l.472 `movq %r8, %r11`
    .bt "%rcx" (.imm 0),  -- l.473 `btq $0, %rcx`
    .adcx "%r11" (.reg "%rbx"),  -- l.474 `adcxq %rbx, %r11`
    .setc "%r12",  -- l.475 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rcx" "%rsp" 56,  -- l.477 `movq 56(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.478 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.479 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 56,  -- l.480 `movq 56(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.481 `movq 32(%rsp), %r14`
    .mulx "%r8" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.482 `mulx %r14, %rcx, %r8`
    .mov "%r13" (.reg "%rcx"),  -- l.483 `movq %rcx, %r13`
    .bt "%r12" (.imm 0),  -- l.484 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.485 `adcxq %r10, %r13`
    .setc "%r9",  -- l.486 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rcx" "%rsp" 64,  -- l.488 `movq 64(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.489 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.490 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 64,  -- l.491 `movq 64(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 32,  -- l.492 `movq 32(%rsp), %r14`
    .mulx "%r10" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.493 `mulx %r14, %rcx, %r10`
    .mov "%r12" (.reg "%rcx"),  -- l.494 `movq %rcx, %r12`
    .bt "%r9" (.imm 0),  -- l.495 `btq $0, %r9`
    .adcx "%r12" (.reg "%r8"),  -- l.496 `adcxq %r8, %r12`
    .setc "%rax",  -- l.497 `setc %al; movzbq %al, %rax`
    .loadMem "%rcx" "%rsp" 72,  -- l.499 `movq 72(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 32,  -- l.500 `movq 32(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.501 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 72 ]  -- l.502 `movq 72(%rsp), %rdx`

/-- Segment 16 of the body: the 32 instructions from source lines 503–539. -/
def ed25519PointAddShippedSeg016 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 32,  -- l.503 `movq 32(%rsp), %r14`
    .mulx "%r8" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.504 `mulx %r14, %rcx, %r8`
    .bt "%rax" (.imm 0),  -- l.505 `btq $0, %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.506 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rcx"),  -- l.507 `movq %rcx, %rbx`
    .adcx "%rbx" (.reg "%r10"),  -- l.508 `adcxq %r10, %rbx`
    .storeMem "%rsp" 72 (.reg "%rbx"),  -- l.509 `movq %rbx, 72(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.510 `movq -128(%rsp), %rbx`
    .setc "%r9",  -- l.511 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%r8"),  -- l.513 `movq %r8, %rax`
    .bt "%r9" (.imm 0),  -- l.514 `btq $0, %r9`
    .adcx "%rax" (.reg "%rbx"),  -- l.515 `adcxq %rbx, %rax`
    .mov "%rbx" (.imm 0),  -- l.516 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.517 `movl $0, %ecx`
    .mov "%r8" (.reg "%rsi"),  -- l.518 `movq %rsi, %r8`
    .bt "%rcx" (.imm 0),  -- l.519 `btq $0, %rcx`
    .adcx "%r8" (.reg "%r11"),  -- l.520 `adcxq %r11, %r8`
    .setc "%r9",  -- l.521 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rbp"),  -- l.523 `movq %rbp, %rcx`
    .bt "%r9" (.imm 0),  -- l.524 `btq $0, %r9`
    .adcx "%rcx" (.reg "%r13"),  -- l.525 `adcxq %r13, %rcx`
    .setc "%rsi",  -- l.526 `setc %sil; movzbq %sil, %rsi`
    .mov "%rbp" (.reg "%rdi"),  -- l.528 `movq %rdi, %rbp`
    .bt "%rsi" (.imm 0),  -- l.529 `btq $0, %rsi`
    .adcx "%rbp" (.reg "%r12"),  -- l.530 `adcxq %r12, %rbp`
    .setc "%r9",  -- l.531 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rsi" "%rsp" 24,  -- l.533 `movq 24(%rsp), %rsi`
    .bt "%r9" (.imm 0),  -- l.534 `btq $0, %r9`
    .adcxMem "%rsi" "%rsp" 72,  -- l.535 `adcxq 72(%rsp), %rsi`
    .setc "%rdi",  -- l.536 `setc %dil; movzbq %dil, %rdi`
    .mov "%r9" (.reg "%rbx"),  -- l.538 `movq %rbx, %r9`
    .bt "%rdi" (.imm 0) ]  -- l.539 `btq $0, %rdi`

/-- Segment 17 of the body: the 32 instructions from source lines 540–575. -/
def ed25519PointAddShippedSeg017 : List (JInstr 64) :=
  [ .adcx "%r9" (.reg "%rax"),  -- l.540 `adcxq %rax, %r9`
    .setc "%r10",  -- l.541 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 38),  -- l.543 `movq $38, %rax`
    .mov "%rbx" (.imm 0),  -- l.544 `movq $0, %rbx`
    .mov "%rdi" (.imm 0),  -- l.545 `movl $0, %edi`
    .mov "%r10" (.reg "%rcx"),  -- l.546 `movq %rcx, %r10`
    .imul "%r10" (.reg "%rax"),  -- l.547 `imulq %rax, %r10`
    .mov "%rdx" (.reg "%rcx"),  -- l.548 `movq %rcx, %rdx`
    .mulx "%r11" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.549 `mulx %rax, %r10, %r11`
    .mov "%rcx" (.reg "%r10"),  -- l.550 `movq %r10, %rcx`
    .bt "%rdi" (.imm 0),  -- l.551 `btq $0, %rdi`
    .adcx "%rcx" (.reg "%rbx"),  -- l.552 `adcxq %rbx, %rcx`
    .setc "%r12",  -- l.553 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rbp"),  -- l.555 `movq %rbp, %rdi`
    .imul "%rdi" (.reg "%rax"),  -- l.556 `imulq %rax, %rdi`
    .mov "%rdx" (.reg "%rbp"),  -- l.557 `movq %rbp, %rdx`
    .mulx "%r10" "%rdi" (.reg "%rdx") (.reg "%rax"),  -- l.558 `mulx %rax, %rdi, %r10`
    .mov "%rbp" (.reg "%rdi"),  -- l.559 `movq %rdi, %rbp`
    .bt "%r12" (.imm 0),  -- l.560 `btq $0, %r12`
    .adcx "%rbp" (.reg "%r11"),  -- l.561 `adcxq %r11, %rbp`
    .setc "%r13",  -- l.562 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rdi" (.reg "%rsi"),  -- l.564 `movq %rsi, %rdi`
    .imul "%rdi" (.reg "%rax"),  -- l.565 `imulq %rax, %rdi`
    .mov "%rdx" (.reg "%rsi"),  -- l.566 `movq %rsi, %rdx`
    .mulx "%r11" "%rdi" (.reg "%rdx") (.reg "%rax"),  -- l.567 `mulx %rax, %rdi, %r11`
    .mov "%rsi" (.reg "%rdi"),  -- l.568 `movq %rdi, %rsi`
    .bt "%r13" (.imm 0),  -- l.569 `btq $0, %r13`
    .adcx "%rsi" (.reg "%r10"),  -- l.570 `adcxq %r10, %rsi`
    .setc "%r12",  -- l.571 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%r9"),  -- l.573 `movq %r9, %rdi`
    .imul "%rdi" (.reg "%rax"),  -- l.574 `imulq %rax, %rdi`
    .mov "%rdx" (.reg "%r9") ]  -- l.575 `movq %r9, %rdx`

/-- Segment 18 of the body: the 32 instructions from source lines 576–613. -/
def ed25519PointAddShippedSeg018 : List (JInstr 64) :=
  [ .mulx "%r10" "%rdi" (.reg "%rdx") (.reg "%rax"),  -- l.576 `mulx %rax, %rdi, %r10`
    .mov "%r9" (.reg "%rdi"),  -- l.577 `movq %rdi, %r9`
    .bt "%r12" (.imm 0),  -- l.578 `btq $0, %r12`
    .adcx "%r9" (.reg "%r11"),  -- l.579 `adcxq %r11, %r9`
    .setc "%r13",  -- l.580 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rdi" (.reg "%r10"),  -- l.582 `movq %r10, %rdi`
    .bt "%r13" (.imm 0),  -- l.583 `btq $0, %r13`
    .adcx "%rdi" (.reg "%rbx"),  -- l.584 `adcxq %rbx, %rdi`
    .mov "%rbx" (.imm 0),  -- l.585 `movq $0, %rbx`
    .mov "%r10" (.imm 0),  -- l.586 `movl $0, %r10d`
    .loadMem "%r11" "%rsp" 40,  -- l.587 `movq 40(%rsp), %r11`
    .bt "%r10" (.imm 0),  -- l.588 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.589 `adcxq %rcx, %r11`
    .setc "%r12",  -- l.590 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rcx" "%rsp" 0,  -- l.592 `movq 0(%rsp), %rcx`
    .bt "%r12" (.imm 0),  -- l.593 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rbp"),  -- l.594 `adcxq %rbp, %rcx`
    .setc "%r10",  -- l.595 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rbp" "%rsp" 8,  -- l.597 `movq 8(%rsp), %rbp`
    .bt "%r10" (.imm 0),  -- l.598 `btq $0, %r10`
    .adcx "%rbp" (.reg "%rsi"),  -- l.599 `adcxq %rsi, %rbp`
    .setc "%r12",  -- l.600 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rsi" (.reg "%r8"),  -- l.602 `movq %r8, %rsi`
    .bt "%r12" (.imm 0),  -- l.603 `btq $0, %r12`
    .adcx "%rsi" (.reg "%r9"),  -- l.604 `adcxq %r9, %rsi`
    .setc "%r10",  -- l.605 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r8" (.reg "%rbx"),  -- l.607 `movq %rbx, %r8`
    .bt "%r10" (.imm 0),  -- l.608 `btq $0, %r10`
    .adcx "%r8" (.reg "%rdi"),  -- l.609 `adcxq %rdi, %r8`
    .setc "%r9",  -- l.610 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rdi" (.imm 0),  -- l.612 `movq $0, %rdi`
    .mov "%r9" (.imm 0) ]  -- l.613 `movl $0, %r9d`

/-- Segment 19 of the body: the 32 instructions from source lines 614–650. -/
def ed25519PointAddShippedSeg019 : List (JInstr 64) :=
  [ .mov "%r10" (.reg "%r8"),  -- l.614 `movq %r8, %r10`
    .imul "%r10" (.reg "%rax"),  -- l.615 `imulq %rax, %r10`
    .mov "%rdx" (.reg "%r8"),  -- l.616 `movq %r8, %rdx`
    .mulx "%r12" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.617 `mulx %rax, %r10, %r12`
    .mov "%r8" (.reg "%r10"),  -- l.618 `movq %r10, %r8`
    .bt "%r9" (.imm 0),  -- l.619 `btq $0, %r9`
    .adcx "%r8" (.reg "%rdi"),  -- l.620 `adcxq %rdi, %r8`
    .setc "%r13",  -- l.621 `setc %r13b; movzbq %r13b, %r13`
    .mov "%r9" (.reg "%r12"),  -- l.623 `movq %r12, %r9`
    .bt "%r13" (.imm 0),  -- l.624 `btq $0, %r13`
    .adcx "%r9" (.reg "%rdi"),  -- l.625 `adcxq %rdi, %r9`
    .mov "%rdi" (.imm 0),  -- l.626 `movl $0, %edi`
    .mov "%r10" (.reg "%r11"),  -- l.627 `movq %r11, %r10`
    .bt "%rdi" (.imm 0),  -- l.628 `btq $0, %rdi`
    .adcx "%r10" (.reg "%r8"),  -- l.629 `adcxq %r8, %r10`
    .setc "%r12",  -- l.630 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rcx"),  -- l.632 `movq %rcx, %rdi`
    .bt "%r12" (.imm 0),  -- l.633 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.634 `adcxq %r9, %rdi`
    .setc "%r8",  -- l.635 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rcx" (.reg "%rbp"),  -- l.637 `movq %rbp, %rcx`
    .bt "%r8" (.imm 0),  -- l.638 `btq $0, %r8`
    .adcx "%rcx" (.reg "%rbx"),  -- l.639 `adcxq %rbx, %rcx`
    .setc "%r9",  -- l.640 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbp" (.reg "%rsi"),  -- l.642 `movq %rsi, %rbp`
    .bt "%r9" (.imm 0),  -- l.643 `btq $0, %r9`
    .adcx "%rbp" (.reg "%rbx"),  -- l.644 `adcxq %rbx, %rbp`
    .setc "%r8",  -- l.645 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rsi" (.reg "%rbx"),  -- l.647 `movq %rbx, %rsi`
    .test "%r8" (.reg "%r8"),  -- l.648 `testq %r8, %r8`
    .cmovne "%rsi" (.reg "%rax"),  -- l.649 `cmovneq %rax, %rsi`
    .mov "%rax" (.imm 0) ]  -- l.650 `movl $0, %eax`

/-- Segment 20 of the body: the 32 instructions from source lines 651–688. -/
def ed25519PointAddShippedSeg020 : List (JInstr 64) :=
  [ .mov "%r8" (.reg "%r10"),  -- l.651 `movq %r10, %r8`
    .bt "%rax" (.imm 0),  -- l.652 `btq $0, %rax`
    .adcx "%r8" (.reg "%rsi"),  -- l.653 `adcxq %rsi, %r8`
    .setc "%r9",  -- l.654 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rdi"),  -- l.656 `movq %rdi, %rax`
    .bt "%r9" (.imm 0),  -- l.657 `btq $0, %r9`
    .adcx "%rax" (.reg "%rbx"),  -- l.658 `adcxq %rbx, %rax`
    .setc "%rsi",  -- l.659 `setc %sil; movzbq %sil, %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.661 `movq %rcx, %rdi`
    .bt "%rsi" (.imm 0),  -- l.662 `btq $0, %rsi`
    .adcx "%rdi" (.reg "%rbx"),  -- l.663 `adcxq %rbx, %rdi`
    .setc "%r9",  -- l.664 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rbp"),  -- l.666 `movq %rbp, %rcx`
    .bt "%r9" (.imm 0),  -- l.667 `btq $0, %r9`
    .adcx "%rcx" (.reg "%rbx"),  -- l.668 `adcxq %rbx, %rcx`
    .setc "%rsi",  -- l.669 `setc %sil; movzbq %sil, %rsi`
    .mov "%rbx" (.imm 19),  -- l.671 `movq $19, %rbx`
    .mov "%rsi" (.imm 0),  -- l.672 `movq $0, %rsi`
    .mov "%rbp" (.imm 0),  -- l.673 `movq $0, %rbp`
    .mov "%r9" (.imm 9223372036854775808),  -- l.674 `movq $9223372036854775808, %r9`
    .mov "%r10" (.imm 0),  -- l.675 `movl $0, %r10d`
    .mov "%r11" (.reg "%r8"),  -- l.676 `movq %r8, %r11`
    .bt "%r10" (.imm 0),  -- l.677 `btq $0, %r10`
    .adcx "%r11" (.reg "%rbx"),  -- l.678 `adcxq %rbx, %r11`
    .setc "%r12",  -- l.679 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbx" (.reg "%rax"),  -- l.681 `movq %rax, %rbx`
    .bt "%r12" (.imm 0),  -- l.682 `btq $0, %r12`
    .adcx "%rbx" (.reg "%rsi"),  -- l.683 `adcxq %rsi, %rbx`
    .setc "%r10",  -- l.684 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rdi"),  -- l.686 `movq %rdi, %rsi`
    .bt "%r10" (.imm 0),  -- l.687 `btq $0, %r10`
    .adcx "%rsi" (.reg "%rbp") ]  -- l.688 `adcxq %rbp, %rsi`

/-- Segment 21 of the body: the 32 instructions from source lines 689–724. -/
def ed25519PointAddShippedSeg021 : List (JInstr 64) :=
  [ .setc "%r12",  -- l.689 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rcx"),  -- l.691 `movq %rcx, %rbp`
    .bt "%r12" (.imm 0),  -- l.692 `btq $0, %r12`
    .adcx "%rbp" (.reg "%r9"),  -- l.693 `adcxq %r9, %rbp`
    .setc "%r10",  -- l.694 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%r8"),  -- l.696 `movq %r8, %r9`
    .test "%r10" (.reg "%r10"),  -- l.697 `testq %r10, %r10`
    .cmovne "%r9" (.reg "%r11"),  -- l.698 `cmovneq %r11, %r9`
    .mov "%r8" (.reg "%rax"),  -- l.699 `movq %rax, %r8`
    .test "%r10" (.reg "%r10"),  -- l.700 `testq %r10, %r10`
    .cmovne "%r8" (.reg "%rbx"),  -- l.701 `cmovneq %rbx, %r8`
    .mov "%rax" (.reg "%rdi"),  -- l.702 `movq %rdi, %rax`
    .test "%r10" (.reg "%r10"),  -- l.703 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rsi"),  -- l.704 `cmovneq %rsi, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.705 `movq %rcx, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.706 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rbp"),  -- l.707 `cmovneq %rbp, %rbx`
    .mov "%rcx" (.imm 19),  -- l.708 `movq $19, %rcx`
    .mov "%rsi" (.imm 0),  -- l.709 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.710 `movq $0, %rdi`
    .mov "%rbp" (.imm 9223372036854775808),  -- l.711 `movq $9223372036854775808, %rbp`
    .mov "%r10" (.imm 0),  -- l.712 `movl $0, %r10d`
    .mov "%r11" (.reg "%r9"),  -- l.713 `movq %r9, %r11`
    .bt "%r10" (.imm 0),  -- l.714 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.715 `adcxq %rcx, %r11`
    .setc "%r12",  -- l.716 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rcx" (.reg "%r8"),  -- l.718 `movq %r8, %rcx`
    .bt "%r12" (.imm 0),  -- l.719 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rsi"),  -- l.720 `adcxq %rsi, %rcx`
    .setc "%r10",  -- l.721 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rax"),  -- l.723 `movq %rax, %rsi`
    .bt "%r10" (.imm 0) ]  -- l.724 `btq $0, %r10`

/-- Segment 22 of the body: the 32 instructions from source lines 725–758. -/
def ed25519PointAddShippedSeg022 : List (JInstr 64) :=
  [ .adcx "%rsi" (.reg "%rdi"),  -- l.725 `adcxq %rdi, %rsi`
    .setc "%r12",  -- l.726 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rbx"),  -- l.728 `movq %rbx, %rdi`
    .bt "%r12" (.imm 0),  -- l.729 `btq $0, %r12`
    .adcx "%rdi" (.reg "%rbp"),  -- l.730 `adcxq %rbp, %rdi`
    .setc "%r10",  -- l.731 `setc %r10b; movzbq %r10b, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.733 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r9"),  -- l.734 `movq %r9, %rax`
    .test "%r10" (.reg "%r10"),  -- l.735 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%r11"),  -- l.736 `cmovneq %r11, %rax`
    .storeMem "%rsp" 48 (.reg "%rax"),  -- l.737 `movq %rax, 48(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.738 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.739 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.740 `movq %r8, %rax`
    .test "%r10" (.reg "%r10"),  -- l.741 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rcx"),  -- l.742 `cmovneq %rcx, %rax`
    .storeMem "%rsp" 56 (.reg "%rax"),  -- l.743 `movq %rax, 56(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.744 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.745 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rax"),  -- l.746 `movq %rax, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.747 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rsi"),  -- l.748 `cmovneq %rsi, %rbx`
    .storeMem "%rsp" 64 (.reg "%rbx"),  -- l.749 `movq %rbx, 64(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.750 `movq -128(%rsp), %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.751 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.752 `movq %rbx, %rax`
    .test "%r10" (.reg "%r10"),  -- l.753 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rdi"),  -- l.754 `cmovneq %rdi, %rax`
    .storeMem "%rsp" 72 (.reg "%rax"),  -- l.755 `movq %rax, 72(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.756 `movq -128(%rsp), %rax`
    .mov "%rbx" (.imm 0),  -- l.757 `movl $0, %ebx`
    .loadMem "%rsi" "%rsp" 80 ]  -- l.758 `movq 80(%rsp), %rsi`

/-- Segment 23 of the body: the 32 instructions from source lines 759–796. -/
def ed25519PointAddShippedSeg023 : List (JInstr 64) :=
  [ .bt "%rbx" (.imm 0),  -- l.759 `btq $0, %rbx`
    .adcxMem "%rsi" "%rsp" 144,  -- l.760 `adcxq 144(%rsp), %rsi`
    .setc "%rdi",  -- l.761 `setc %dil; movzbq %dil, %rdi`
    .loadMem "%rbx" "%rsp" 88,  -- l.763 `movq 88(%rsp), %rbx`
    .bt "%rdi" (.imm 0),  -- l.764 `btq $0, %rdi`
    .adcxMem "%rbx" "%rsp" 152,  -- l.765 `adcxq 152(%rsp), %rbx`
    .setc "%r8",  -- l.766 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rdi" "%rsp" 96,  -- l.768 `movq 96(%rsp), %rdi`
    .bt "%r8" (.imm 0),  -- l.769 `btq $0, %r8`
    .adcxMem "%rdi" "%rsp" 168,  -- l.770 `adcxq 168(%rsp), %rdi`
    .setc "%r10",  -- l.771 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%r8" "%rsp" 104,  -- l.773 `movq 104(%rsp), %r8`
    .bt "%r10" (.imm 0),  -- l.774 `btq $0, %r10`
    .adcxMem "%r8" "%rsp" 184,  -- l.775 `adcxq 184(%rsp), %r8`
    .setc "%r11",  -- l.776 `setc %r11b; movzbq %r11b, %r11`
    .mov "%r10" (.imm 19),  -- l.778 `movq $19, %r10`
    .mov "%r11" (.imm 0),  -- l.779 `movq $0, %r11`
    .mov "%r12" (.imm 0),  -- l.780 `movq $0, %r12`
    .mov "%r13" (.imm 9223372036854775808),  -- l.781 `movq $9223372036854775808, %r13`
    .mov "%rax" (.imm 0),  -- l.782 `movl $0, %eax`
    .mov "%rcx" (.reg "%rsi"),  -- l.783 `movq %rsi, %rcx`
    .bt "%rax" (.imm 0),  -- l.784 `btq $0, %rax`
    .adcx "%rcx" (.reg "%r10"),  -- l.785 `adcxq %r10, %rcx`
    .setc "%r9",  -- l.786 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rbx"),  -- l.788 `movq %rbx, %rax`
    .bt "%r9" (.imm 0),  -- l.789 `btq $0, %r9`
    .adcx "%rax" (.reg "%r11"),  -- l.790 `adcxq %r11, %rax`
    .setc "%r10",  -- l.791 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%rdi"),  -- l.793 `movq %rdi, %r9`
    .bt "%r10" (.imm 0),  -- l.794 `btq $0, %r10`
    .adcx "%r9" (.reg "%r12"),  -- l.795 `adcxq %r12, %r9`
    .setc "%r11" ]  -- l.796 `setc %r11b; movzbq %r11b, %r11`

/-- Segment 24 of the body: the 32 instructions from source lines 798–830. -/
def ed25519PointAddShippedSeg024 : List (JInstr 64) :=
  [ .mov "%r10" (.reg "%r8"),  -- l.798 `movq %r8, %r10`
    .bt "%r11" (.imm 0),  -- l.799 `btq $0, %r11`
    .adcx "%r10" (.reg "%r13"),  -- l.800 `adcxq %r13, %r10`
    .setc "%r12",  -- l.801 `setc %r12b; movzbq %r12b, %r12`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.803 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rsi"),  -- l.804 `movq %rsi, %rax`
    .test "%r12" (.reg "%r12"),  -- l.805 `testq %r12, %r12`
    .cmovne "%rax" (.reg "%rcx"),  -- l.806 `cmovneq %rcx, %rax`
    .storeMem "%rsp" 144 (.reg "%rax"),  -- l.807 `movq %rax, 144(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.808 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.809 `movq %rcx, -128(%rsp)`
    .mov "%rcx" (.reg "%rbx"),  -- l.810 `movq %rbx, %rcx`
    .test "%r12" (.reg "%r12"),  -- l.811 `testq %r12, %r12`
    .cmovne "%rcx" (.reg "%rax"),  -- l.812 `cmovneq %rax, %rcx`
    .storeMem "%rsp" 152 (.reg "%rcx"),  -- l.813 `movq %rcx, 152(%rsp)`
    .loadMem "%rcx" "%rsp" (-128),  -- l.814 `movq -128(%rsp), %rcx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.815 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.816 `movq %rdi, %rax`
    .test "%r12" (.reg "%r12"),  -- l.817 `testq %r12, %r12`
    .cmovne "%rax" (.reg "%r9"),  -- l.818 `cmovneq %r9, %rax`
    .storeMem "%rsp" 168 (.reg "%rax"),  -- l.819 `movq %rax, 168(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.820 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.821 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.822 `movq %r8, %rax`
    .test "%r12" (.reg "%r12"),  -- l.823 `testq %r12, %r12`
    .cmovne "%rax" (.reg "%r10"),  -- l.824 `cmovneq %r10, %rax`
    .storeMem "%rsp" 184 (.reg "%rax"),  -- l.825 `movq %rax, 184(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.826 `movq -128(%rsp), %rax`
    .mov "%rsi" (.imm 0),  -- l.827 `movl $0, %esi`
    .loadMem "%rdi" "%rsp" 112,  -- l.828 `movq 112(%rsp), %rdi`
    .bt "%rsi" (.imm 0),  -- l.829 `btq $0, %rsi`
    .adcxMem "%rdi" "%rsp" 208 ]  -- l.830 `adcxq 208(%rsp), %rdi`

/-- Segment 25 of the body: the 32 instructions from source lines 831–869. -/
def ed25519PointAddShippedSeg025 : List (JInstr 64) :=
  [ .setc "%r8",  -- l.831 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rsi" "%rsp" 120,  -- l.833 `movq 120(%rsp), %rsi`
    .bt "%r8" (.imm 0),  -- l.834 `btq $0, %r8`
    .adcxMem "%rsi" "%rsp" 216,  -- l.835 `adcxq 216(%rsp), %rsi`
    .setc "%r9",  -- l.836 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%r8" "%rsp" 128,  -- l.838 `movq 128(%rsp), %r8`
    .bt "%r9" (.imm 0),  -- l.839 `btq $0, %r9`
    .adcxMem "%r8" "%rsp" 224,  -- l.840 `adcxq 224(%rsp), %r8`
    .setc "%r10",  -- l.841 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%r9" "%rsp" 136,  -- l.843 `movq 136(%rsp), %r9`
    .bt "%r10" (.imm 0),  -- l.844 `btq $0, %r10`
    .adcxMem "%r9" "%rsp" 264,  -- l.845 `adcxq 264(%rsp), %r9`
    .setc "%r12",  -- l.846 `setc %r12b; movzbq %r12b, %r12`
    .mov "%r10" (.imm 19),  -- l.848 `movq $19, %r10`
    .mov "%r12" (.imm 0),  -- l.849 `movq $0, %r12`
    .mov "%r13" (.imm 0),  -- l.850 `movq $0, %r13`
    .mov "%rbp" (.imm 9223372036854775808),  -- l.851 `movq $9223372036854775808, %rbp`
    .mov "%rbx" (.imm 0),  -- l.852 `movl $0, %ebx`
    .mov "%rax" (.reg "%rdi"),  -- l.853 `movq %rdi, %rax`
    .bt "%rbx" (.imm 0),  -- l.854 `btq $0, %rbx`
    .adcx "%rax" (.reg "%r10"),  -- l.855 `adcxq %r10, %rax`
    .setc "%rcx",  -- l.856 `setc %cl; movzbq %cl, %rcx`
    .mov "%rbx" (.reg "%rsi"),  -- l.858 `movq %rsi, %rbx`
    .bt "%rcx" (.imm 0),  -- l.859 `btq $0, %rcx`
    .adcx "%rbx" (.reg "%r12"),  -- l.860 `adcxq %r12, %rbx`
    .setc "%r10",  -- l.861 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rcx" (.reg "%r8"),  -- l.863 `movq %r8, %rcx`
    .bt "%r10" (.imm 0),  -- l.864 `btq $0, %r10`
    .adcx "%rcx" (.reg "%r13"),  -- l.865 `adcxq %r13, %rcx`
    .setc "%r12",  -- l.866 `setc %r12b; movzbq %r12b, %r12`
    .mov "%r10" (.reg "%r9"),  -- l.868 `movq %r9, %r10`
    .bt "%r12" (.imm 0) ]  -- l.869 `btq $0, %r12`

/-- Segment 26 of the body: the 32 instructions from source lines 870–903. -/
def ed25519PointAddShippedSeg026 : List (JInstr 64) :=
  [ .adcx "%r10" (.reg "%rbp"),  -- l.870 `adcxq %rbp, %r10`
    .setc "%r13",  -- l.871 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%rdi"),  -- l.873 `movq %rdi, %rbp`
    .test "%r13" (.reg "%r13"),  -- l.874 `testq %r13, %r13`
    .cmovne "%rbp" (.reg "%rax"),  -- l.875 `cmovneq %rax, %rbp`
    .mov "%rax" (.reg "%rsi"),  -- l.876 `movq %rsi, %rax`
    .test "%r13" (.reg "%r13"),  -- l.877 `testq %r13, %r13`
    .cmovne "%rax" (.reg "%rbx"),  -- l.878 `cmovneq %rbx, %rax`
    .mov "%rbx" (.reg "%r8"),  -- l.879 `movq %r8, %rbx`
    .test "%r13" (.reg "%r13"),  -- l.880 `testq %r13, %r13`
    .cmovne "%rbx" (.reg "%rcx"),  -- l.881 `cmovneq %rcx, %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.882 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r9"),  -- l.883 `movq %r9, %rax`
    .test "%r13" (.reg "%r13"),  -- l.884 `testq %r13, %r13`
    .cmovne "%rax" (.reg "%r10"),  -- l.885 `cmovneq %r10, %rax`
    .storeMem "%rsp" 216 (.reg "%rax"),  -- l.886 `movq %rax, 216(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.887 `movq -128(%rsp), %rax`
    .mov "%rsi" (.imm 0),  -- l.888 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.889 `movl $0, %edi`
    .loadMem "%r8" "%rsp" 144,  -- l.890 `movq 144(%rsp), %r8`
    .imul "%r8" (.reg "%rbp"),  -- l.891 `imulq %rbp, %r8`
    .loadMem "%rdx" "%rsp" 144,  -- l.892 `movq 144(%rsp), %rdx`
    .mulx "%r9" "%r8" (.reg "%rdx") (.reg "%rbp"),  -- l.893 `mulx %rbp, %r8, %r9`
    .bt "%rdi" (.imm 0),  -- l.894 `btq $0, %rdi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.895 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.896 `movq %r8, %rax`
    .adcx "%rax" (.reg "%rsi"),  -- l.897 `adcxq %rsi, %rax`
    .storeMem "%rsp" 264 (.reg "%rax"),  -- l.898 `movq %rax, 264(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.899 `movq -128(%rsp), %rax`
    .setc "%r12",  -- l.900 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rdi" "%rsp" 152,  -- l.902 `movq 152(%rsp), %rdi`
    .imul "%rdi" (.reg "%rbp") ]  -- l.903 `imulq %rbp, %rdi`

/-- Segment 27 of the body: the 32 instructions from source lines 904–938. -/
def ed25519PointAddShippedSeg027 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsp" 152,  -- l.904 `movq 152(%rsp), %rdx`
    .mulx "%r8" "%rdi" (.reg "%rdx") (.reg "%rbp"),  -- l.905 `mulx %rbp, %rdi, %r8`
    .mov "%r13" (.reg "%rdi"),  -- l.906 `movq %rdi, %r13`
    .bt "%r12" (.imm 0),  -- l.907 `btq $0, %r12`
    .adcx "%r13" (.reg "%r9"),  -- l.908 `adcxq %r9, %r13`
    .setc "%r10",  -- l.909 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rdi" "%rsp" 168,  -- l.911 `movq 168(%rsp), %rdi`
    .imul "%rdi" (.reg "%rbp"),  -- l.912 `imulq %rbp, %rdi`
    .loadMem "%rdx" "%rsp" 168,  -- l.913 `movq 168(%rsp), %rdx`
    .mulx "%r9" "%rdi" (.reg "%rdx") (.reg "%rbp"),  -- l.914 `mulx %rbp, %rdi, %r9`
    .bt "%r10" (.imm 0),  -- l.915 `btq $0, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.916 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.917 `movq %rdi, %rax`
    .adcx "%rax" (.reg "%r8"),  -- l.918 `adcxq %r8, %rax`
    .storeMem "%rsp" 224 (.reg "%rax"),  -- l.919 `movq %rax, 224(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.920 `movq -128(%rsp), %rax`
    .setc "%r12",  -- l.921 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rdi" "%rsp" 184,  -- l.923 `movq 184(%rsp), %rdi`
    .imul "%rdi" (.reg "%rbp"),  -- l.924 `imulq %rbp, %rdi`
    .loadMem "%rdx" "%rsp" 184,  -- l.925 `movq 184(%rsp), %rdx`
    .mulx "%r8" "%rdi" (.reg "%rdx") (.reg "%rbp"),  -- l.926 `mulx %rbp, %rdi, %r8`
    .mov "%rbp" (.reg "%rdi"),  -- l.927 `movq %rdi, %rbp`
    .bt "%r12" (.imm 0),  -- l.928 `btq $0, %r12`
    .adcx "%rbp" (.reg "%r9"),  -- l.929 `adcxq %r9, %rbp`
    .setc "%r10",  -- l.930 `setc %r10b; movzbq %r10b, %r10`
    .bt "%r10" (.imm 0),  -- l.932 `btq $0, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.933 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.934 `movq %r8, %rax`
    .adcx "%rax" (.reg "%rsi"),  -- l.935 `adcxq %rsi, %rax`
    .storeMem "%rsp" 208 (.reg "%rax"),  -- l.936 `movq %rax, 208(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.937 `movq -128(%rsp), %rax`
    .mov "%rsi" (.imm 0) ]  -- l.938 `movq $0, %rsi`

/-- Segment 28 of the body: the 32 instructions from source lines 939–973. -/
def ed25519PointAddShippedSeg028 : List (JInstr 64) :=
  [ .mov "%r8" (.imm 0),  -- l.939 `movl $0, %r8d`
    .loadMem "%r9" "%rsp" 144,  -- l.940 `movq 144(%rsp), %r9`
    .imul "%r9" (.reg "%rax"),  -- l.941 `imulq %rax, %r9`
    .loadMem "%rdx" "%rsp" 144,  -- l.942 `movq 144(%rsp), %rdx`
    .mulx "%r10" "%r9" (.reg "%rdx") (.reg "%rax"),  -- l.943 `mulx %rax, %r9, %r10`
    .mov "%r12" (.reg "%r9"),  -- l.944 `movq %r9, %r12`
    .bt "%r8" (.imm 0),  -- l.945 `btq $0, %r8`
    .adcx "%r12" (.reg "%rsi"),  -- l.946 `adcxq %rsi, %r12`
    .setc "%rcx",  -- l.947 `setc %cl; movzbq %cl, %rcx`
    .loadMem "%r8" "%rsp" 152,  -- l.949 `movq 152(%rsp), %r8`
    .imul "%r8" (.reg "%rax"),  -- l.950 `imulq %rax, %r8`
    .loadMem "%rdx" "%rsp" 152,  -- l.951 `movq 152(%rsp), %rdx`
    .mulx "%r9" "%r8" (.reg "%rdx") (.reg "%rax"),  -- l.952 `mulx %rax, %r8, %r9`
    .mov "%rdi" (.reg "%r8"),  -- l.953 `movq %r8, %rdi`
    .bt "%rcx" (.imm 0),  -- l.954 `btq $0, %rcx`
    .adcx "%rdi" (.reg "%r10"),  -- l.955 `adcxq %r10, %rdi`
    .setc "%r11",  -- l.956 `setc %r11b; movzbq %r11b, %r11`
    .loadMem "%rcx" "%rsp" 168,  -- l.958 `movq 168(%rsp), %rcx`
    .imul "%rcx" (.reg "%rax"),  -- l.959 `imulq %rax, %rcx`
    .loadMem "%rdx" "%rsp" 168,  -- l.960 `movq 168(%rsp), %rdx`
    .mulx "%r8" "%rcx" (.reg "%rdx") (.reg "%rax"),  -- l.961 `mulx %rax, %rcx, %r8`
    .bt "%r11" (.imm 0),  -- l.962 `btq $0, %r11`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.963 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.964 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%r9"),  -- l.965 `adcxq %r9, %rax`
    .storeMem "%rsp" 136 (.reg "%rax"),  -- l.966 `movq %rax, 136(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.967 `movq -128(%rsp), %rax`
    .setc "%r10",  -- l.968 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rcx" "%rsp" 184,  -- l.970 `movq 184(%rsp), %rcx`
    .imul "%rcx" (.reg "%rax"),  -- l.971 `imulq %rax, %rcx`
    .loadMem "%rdx" "%rsp" 184,  -- l.972 `movq 184(%rsp), %rdx`
    .mulx "%r9" "%rcx" (.reg "%rdx") (.reg "%rax") ]  -- l.973 `mulx %rax, %rcx, %r9`

/-- Segment 29 of the body: the 32 instructions from source lines 974–1010. -/
def ed25519PointAddShippedSeg029 : List (JInstr 64) :=
  [ .mov "%rax" (.reg "%rcx"),  -- l.974 `movq %rcx, %rax`
    .bt "%r10" (.imm 0),  -- l.975 `btq $0, %r10`
    .adcx "%rax" (.reg "%r8"),  -- l.976 `adcxq %r8, %rax`
    .setc "%r11",  -- l.977 `setc %r11b; movzbq %r11b, %r11`
    .mov "%rcx" (.reg "%r9"),  -- l.979 `movq %r9, %rcx`
    .bt "%r11" (.imm 0),  -- l.980 `btq $0, %r11`
    .adcx "%rcx" (.reg "%rsi"),  -- l.981 `adcxq %rsi, %rcx`
    .mov "%rsi" (.imm 0),  -- l.982 `movq $0, %rsi`
    .mov "%r8" (.imm 0),  -- l.983 `movl $0, %r8d`
    .bt "%r8" (.imm 0),  -- l.984 `btq $0, %r8`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.985 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r13"),  -- l.986 `movq %r13, %rax`
    .adcx "%rax" (.reg "%r12"),  -- l.987 `adcxq %r12, %rax`
    .storeMem "%rsp" 128 (.reg "%rax"),  -- l.988 `movq %rax, 128(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.989 `movq -128(%rsp), %rax`
    .setc "%r10",  -- l.990 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%r8" "%rsp" 224,  -- l.992 `movq 224(%rsp), %r8`
    .bt "%r10" (.imm 0),  -- l.993 `btq $0, %r10`
    .adcx "%r8" (.reg "%rdi"),  -- l.994 `adcxq %rdi, %r8`
    .setc "%r11",  -- l.995 `setc %r11b; movzbq %r11b, %r11`
    .mov "%rdi" (.reg "%rbp"),  -- l.997 `movq %rbp, %rdi`
    .bt "%r11" (.imm 0),  -- l.998 `btq $0, %r11`
    .adcxMem "%rdi" "%rsp" 136,  -- l.999 `adcxq 136(%rsp), %rdi`
    .setc "%r10",  -- l.1000 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rbp" "%rsp" 208,  -- l.1002 `movq 208(%rsp), %rbp`
    .bt "%r10" (.imm 0),  -- l.1003 `btq $0, %r10`
    .adcx "%rbp" (.reg "%rax"),  -- l.1004 `adcxq %rax, %rbp`
    .setc "%r11",  -- l.1005 `setc %r11b; movzbq %r11b, %r11`
    .bt "%r11" (.imm 0),  -- l.1007 `btq $0, %r11`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1008 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rsi"),  -- l.1009 `movq %rsi, %rax`
    .adcx "%rax" (.reg "%rcx") ]  -- l.1010 `adcxq %rcx, %rax`

/-- Segment 30 of the body: the 32 instructions from source lines 1011–1045. -/
def ed25519PointAddShippedSeg030 : List (JInstr 64) :=
  [ .storeMem "%rsp" 224 (.reg "%rax"),  -- l.1011 `movq %rax, 224(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1012 `movq -128(%rsp), %rax`
    .setc "%r10",  -- l.1013 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rcx" (.imm 0),  -- l.1015 `movq $0, %rcx`
    .mov "%rsi" (.imm 0),  -- l.1016 `movl $0, %esi`
    .loadMem "%r10" "%rsp" 144,  -- l.1017 `movq 144(%rsp), %r10`
    .imul "%r10" (.reg "%rbx"),  -- l.1018 `imulq %rbx, %r10`
    .loadMem "%rdx" "%rsp" 144,  -- l.1019 `movq 144(%rsp), %rdx`
    .mulx "%r11" "%r10" (.reg "%rdx") (.reg "%rbx"),  -- l.1020 `mulx %rbx, %r10, %r11`
    .mov "%r12" (.reg "%r10"),  -- l.1021 `movq %r10, %r12`
    .bt "%rsi" (.imm 0),  -- l.1022 `btq $0, %rsi`
    .adcx "%r12" (.reg "%rcx"),  -- l.1023 `adcxq %rcx, %r12`
    .setc "%r13",  -- l.1024 `setc %r13b; movzbq %r13b, %r13`
    .loadMem "%rsi" "%rsp" 152,  -- l.1026 `movq 152(%rsp), %rsi`
    .imul "%rsi" (.reg "%rbx"),  -- l.1027 `imulq %rbx, %rsi`
    .loadMem "%rdx" "%rsp" 152,  -- l.1028 `movq 152(%rsp), %rdx`
    .mulx "%r10" "%rsi" (.reg "%rdx") (.reg "%rbx"),  -- l.1029 `mulx %rbx, %rsi, %r10`
    .mov "%r9" (.reg "%rsi"),  -- l.1030 `movq %rsi, %r9`
    .bt "%r13" (.imm 0),  -- l.1031 `btq $0, %r13`
    .adcx "%r9" (.reg "%r11"),  -- l.1032 `adcxq %r11, %r9`
    .setc "%rax",  -- l.1033 `setc %al; movzbq %al, %rax`
    .loadMem "%rsi" "%rsp" 168,  -- l.1035 `movq 168(%rsp), %rsi`
    .imul "%rsi" (.reg "%rbx"),  -- l.1036 `imulq %rbx, %rsi`
    .loadMem "%rdx" "%rsp" 168,  -- l.1037 `movq 168(%rsp), %rdx`
    .mulx "%r11" "%rsi" (.reg "%rdx") (.reg "%rbx"),  -- l.1038 `mulx %rbx, %rsi, %r11`
    .bt "%rax" (.imm 0),  -- l.1039 `btq $0, %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.1040 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rsi"),  -- l.1041 `movq %rsi, %rbx`
    .adcx "%rbx" (.reg "%r10"),  -- l.1042 `adcxq %r10, %rbx`
    .storeMem "%rsp" 208 (.reg "%rbx"),  -- l.1043 `movq %rbx, 208(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.1044 `movq -128(%rsp), %rbx`
    .setc "%r13" ]  -- l.1045 `setc %r13b; movzbq %r13b, %r13`

/-- Segment 31 of the body: the 32 instructions from source lines 1047–1082. -/
def ed25519PointAddShippedSeg031 : List (JInstr 64) :=
  [ .loadMem "%rax" "%rsp" 184,  -- l.1047 `movq 184(%rsp), %rax`
    .imul "%rax" (.reg "%rbx"),  -- l.1048 `imulq %rbx, %rax`
    .loadMem "%rdx" "%rsp" 184,  -- l.1049 `movq 184(%rsp), %rdx`
    .mulx "%rsi" "%rax" (.reg "%rdx") (.reg "%rbx"),  -- l.1050 `mulx %rbx, %rax, %rsi`
    .mov "%rbx" (.reg "%rax"),  -- l.1051 `movq %rax, %rbx`
    .bt "%r13" (.imm 0),  -- l.1052 `btq $0, %r13`
    .adcx "%rbx" (.reg "%r11"),  -- l.1053 `adcxq %r11, %rbx`
    .setc "%r10",  -- l.1054 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.reg "%rsi"),  -- l.1056 `movq %rsi, %rax`
    .bt "%r10" (.imm 0),  -- l.1057 `btq $0, %r10`
    .adcx "%rax" (.reg "%rcx"),  -- l.1058 `adcxq %rcx, %rax`
    .mov "%rcx" (.imm 0),  -- l.1059 `movq $0, %rcx`
    .mov "%rsi" (.imm 0),  -- l.1060 `movl $0, %esi`
    .bt "%rsi" (.imm 0),  -- l.1061 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1062 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.1063 `movq %r8, %rax`
    .adcx "%rax" (.reg "%r12"),  -- l.1064 `adcxq %r12, %rax`
    .storeMem "%rsp" 136 (.reg "%rax"),  -- l.1065 `movq %rax, 136(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1066 `movq -128(%rsp), %rax`
    .setc "%r11",  -- l.1067 `setc %r11b; movzbq %r11b, %r11`
    .mov "%rsi" (.reg "%rdi"),  -- l.1069 `movq %rdi, %rsi`
    .bt "%r11" (.imm 0),  -- l.1070 `btq $0, %r11`
    .adcx "%rsi" (.reg "%r9"),  -- l.1071 `adcxq %r9, %rsi`
    .setc "%r8",  -- l.1072 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rdi" (.reg "%rbp"),  -- l.1074 `movq %rbp, %rdi`
    .bt "%r8" (.imm 0),  -- l.1075 `btq $0, %r8`
    .adcxMem "%rdi" "%rsp" 208,  -- l.1076 `adcxq 208(%rsp), %rdi`
    .setc "%r9",  -- l.1077 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rbp" "%rsp" 224,  -- l.1079 `movq 224(%rsp), %rbp`
    .bt "%r9" (.imm 0),  -- l.1080 `btq $0, %r9`
    .adcx "%rbp" (.reg "%rbx"),  -- l.1081 `adcxq %rbx, %rbp`
    .setc "%r8" ]  -- l.1082 `setc %r8b; movzbq %r8b, %r8`

/-- Segment 32 of the body: the 32 instructions from source lines 1084–1118. -/
def ed25519PointAddShippedSeg032 : List (JInstr 64) :=
  [ .bt "%r8" (.imm 0),  -- l.1084 `btq $0, %r8`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.1085 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rcx"),  -- l.1086 `movq %rcx, %rbx`
    .adcx "%rbx" (.reg "%rax"),  -- l.1087 `adcxq %rax, %rbx`
    .storeMem "%rsp" 224 (.reg "%rbx"),  -- l.1088 `movq %rbx, 224(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.1089 `movq -128(%rsp), %rbx`
    .setc "%r9",  -- l.1090 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.imm 0),  -- l.1092 `movq $0, %rax`
    .mov "%rcx" (.imm 0),  -- l.1093 `movl $0, %ecx`
    .loadMem "%r8" "%rsp" 144,  -- l.1094 `movq 144(%rsp), %r8`
    .loadMem "%r15" "%rsp" 216,  -- l.1095 `movq 216(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.1096 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 144,  -- l.1097 `movq 144(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 216,  -- l.1098 `movq 216(%rsp), %r14`
    .mulx "%r9" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.1099 `mulx %r14, %r8, %r9`
    .mov "%r11" (.reg "%r8"),  -- l.1100 `movq %r8, %r11`
    .bt "%rcx" (.imm 0),  -- l.1101 `btq $0, %rcx`
    .adcx "%r11" (.reg "%rax"),  -- l.1102 `adcxq %rax, %r11`
    .setc "%r12",  -- l.1103 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rcx" "%rsp" 152,  -- l.1105 `movq 152(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 216,  -- l.1106 `movq 216(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1107 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 152,  -- l.1108 `movq 152(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 216,  -- l.1109 `movq 216(%rsp), %r14`
    .mulx "%r8" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1110 `mulx %r14, %rcx, %r8`
    .mov "%r13" (.reg "%rcx"),  -- l.1111 `movq %rcx, %r13`
    .bt "%r12" (.imm 0),  -- l.1112 `btq $0, %r12`
    .adcx "%r13" (.reg "%r9"),  -- l.1113 `adcxq %r9, %r13`
    .setc "%r10",  -- l.1114 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rcx" "%rsp" 168,  -- l.1116 `movq 168(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 216,  -- l.1117 `movq 216(%rsp), %r15`
    .imul "%rcx" (.reg "%r15") ]  -- l.1118 `imulq %r15, %rcx`

/-- Segment 33 of the body: the 32 instructions from source lines 1119–1153. -/
def ed25519PointAddShippedSeg033 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsp" 168,  -- l.1119 `movq 168(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 216,  -- l.1120 `movq 216(%rsp), %r14`
    .mulx "%r9" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1121 `mulx %r14, %rcx, %r9`
    .mov "%r12" (.reg "%rcx"),  -- l.1122 `movq %rcx, %r12`
    .bt "%r10" (.imm 0),  -- l.1123 `btq $0, %r10`
    .adcx "%r12" (.reg "%r8"),  -- l.1124 `adcxq %r8, %r12`
    .setc "%rbx",  -- l.1125 `setc %bl; movzbq %bl, %rbx`
    .loadMem "%rcx" "%rsp" 184,  -- l.1127 `movq 184(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 216,  -- l.1128 `movq 216(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1129 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 184,  -- l.1130 `movq 184(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 216,  -- l.1131 `movq 216(%rsp), %r14`
    .mulx "%r8" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1132 `mulx %r14, %rcx, %r8`
    .bt "%rbx" (.imm 0),  -- l.1133 `btq $0, %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1134 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.1135 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%r9"),  -- l.1136 `adcxq %r9, %rax`
    .storeMem "%rsp" 216 (.reg "%rax"),  -- l.1137 `movq %rax, 216(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1138 `movq -128(%rsp), %rax`
    .setc "%r10",  -- l.1139 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbx" (.reg "%r8"),  -- l.1141 `movq %r8, %rbx`
    .bt "%r10" (.imm 0),  -- l.1142 `btq $0, %r10`
    .adcx "%rbx" (.reg "%rax"),  -- l.1143 `adcxq %rax, %rbx`
    .mov "%rax" (.imm 0),  -- l.1144 `movq $0, %rax`
    .mov "%rcx" (.imm 0),  -- l.1145 `movl $0, %ecx`
    .mov "%r8" (.reg "%rsi"),  -- l.1146 `movq %rsi, %r8`
    .bt "%rcx" (.imm 0),  -- l.1147 `btq $0, %rcx`
    .adcx "%r8" (.reg "%r11"),  -- l.1148 `adcxq %r11, %r8`
    .setc "%r9",  -- l.1149 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi"),  -- l.1151 `movq %rdi, %rcx`
    .bt "%r9" (.imm 0),  -- l.1152 `btq $0, %r9`
    .adcx "%rcx" (.reg "%r13") ]  -- l.1153 `adcxq %r13, %rcx`

/-- Segment 34 of the body: the 32 instructions from source lines 1154–1190. -/
def ed25519PointAddShippedSeg034 : List (JInstr 64) :=
  [ .setc "%rsi",  -- l.1154 `setc %sil; movzbq %sil, %rsi`
    .mov "%rdi" (.reg "%rbp"),  -- l.1156 `movq %rbp, %rdi`
    .bt "%rsi" (.imm 0),  -- l.1157 `btq $0, %rsi`
    .adcx "%rdi" (.reg "%r12"),  -- l.1158 `adcxq %r12, %rdi`
    .setc "%r9",  -- l.1159 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rsi" "%rsp" 224,  -- l.1161 `movq 224(%rsp), %rsi`
    .bt "%r9" (.imm 0),  -- l.1162 `btq $0, %r9`
    .adcxMem "%rsi" "%rsp" 216,  -- l.1163 `adcxq 216(%rsp), %rsi`
    .setc "%rbp",  -- l.1164 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%r9" (.reg "%rax"),  -- l.1166 `movq %rax, %r9`
    .bt "%rbp" (.imm 0),  -- l.1167 `btq $0, %rbp`
    .adcx "%r9" (.reg "%rbx"),  -- l.1168 `adcxq %rbx, %r9`
    .setc "%r10",  -- l.1169 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 38),  -- l.1171 `movq $38, %rax`
    .mov "%rbx" (.imm 0),  -- l.1172 `movq $0, %rbx`
    .mov "%rbp" (.imm 0),  -- l.1173 `movl $0, %ebp`
    .mov "%r10" (.reg "%rcx"),  -- l.1174 `movq %rcx, %r10`
    .imul "%r10" (.reg "%rax"),  -- l.1175 `imulq %rax, %r10`
    .mov "%rdx" (.reg "%rcx"),  -- l.1176 `movq %rcx, %rdx`
    .mulx "%r11" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.1177 `mulx %rax, %r10, %r11`
    .mov "%rcx" (.reg "%r10"),  -- l.1178 `movq %r10, %rcx`
    .bt "%rbp" (.imm 0),  -- l.1179 `btq $0, %rbp`
    .adcx "%rcx" (.reg "%rbx"),  -- l.1180 `adcxq %rbx, %rcx`
    .setc "%r12",  -- l.1181 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rdi"),  -- l.1183 `movq %rdi, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.1184 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%rdi"),  -- l.1185 `movq %rdi, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.1186 `mulx %rax, %rbp, %r10`
    .mov "%rdi" (.reg "%rbp"),  -- l.1187 `movq %rbp, %rdi`
    .bt "%r12" (.imm 0),  -- l.1188 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r11"),  -- l.1189 `adcxq %r11, %rdi`
    .setc "%r13" ]  -- l.1190 `setc %r13b; movzbq %r13b, %r13`

/-- Segment 35 of the body: the 32 instructions from source lines 1192–1227. -/
def ed25519PointAddShippedSeg035 : List (JInstr 64) :=
  [ .mov "%rbp" (.reg "%rsi"),  -- l.1192 `movq %rsi, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.1193 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%rsi"),  -- l.1194 `movq %rsi, %rdx`
    .mulx "%r11" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.1195 `mulx %rax, %rbp, %r11`
    .mov "%rsi" (.reg "%rbp"),  -- l.1196 `movq %rbp, %rsi`
    .bt "%r13" (.imm 0),  -- l.1197 `btq $0, %r13`
    .adcx "%rsi" (.reg "%r10"),  -- l.1198 `adcxq %r10, %rsi`
    .setc "%r12",  -- l.1199 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%r9"),  -- l.1201 `movq %r9, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.1202 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%r9"),  -- l.1203 `movq %r9, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.1204 `mulx %rax, %rbp, %r10`
    .mov "%r9" (.reg "%rbp"),  -- l.1205 `movq %rbp, %r9`
    .bt "%r12" (.imm 0),  -- l.1206 `btq $0, %r12`
    .adcx "%r9" (.reg "%r11"),  -- l.1207 `adcxq %r11, %r9`
    .setc "%r13",  -- l.1208 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%r10"),  -- l.1210 `movq %r10, %rbp`
    .bt "%r13" (.imm 0),  -- l.1211 `btq $0, %r13`
    .adcx "%rbp" (.reg "%rbx"),  -- l.1212 `adcxq %rbx, %rbp`
    .mov "%rbx" (.imm 0),  -- l.1213 `movq $0, %rbx`
    .mov "%r10" (.imm 0),  -- l.1214 `movl $0, %r10d`
    .loadMem "%r11" "%rsp" 264,  -- l.1215 `movq 264(%rsp), %r11`
    .bt "%r10" (.imm 0),  -- l.1216 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.1217 `adcxq %rcx, %r11`
    .setc "%r12",  -- l.1218 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rcx" "%rsp" 128,  -- l.1220 `movq 128(%rsp), %rcx`
    .bt "%r12" (.imm 0),  -- l.1221 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rdi"),  -- l.1222 `adcxq %rdi, %rcx`
    .setc "%r10",  -- l.1223 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rdi" "%rsp" 136,  -- l.1225 `movq 136(%rsp), %rdi`
    .bt "%r10" (.imm 0),  -- l.1226 `btq $0, %r10`
    .adcx "%rdi" (.reg "%rsi") ]  -- l.1227 `adcxq %rsi, %rdi`

/-- Segment 36 of the body: the 32 instructions from source lines 1228–1265. -/
def ed25519PointAddShippedSeg036 : List (JInstr 64) :=
  [ .setc "%r12",  -- l.1228 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rsi" (.reg "%r8"),  -- l.1230 `movq %r8, %rsi`
    .bt "%r12" (.imm 0),  -- l.1231 `btq $0, %r12`
    .adcx "%rsi" (.reg "%r9"),  -- l.1232 `adcxq %r9, %rsi`
    .setc "%r10",  -- l.1233 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r8" (.reg "%rbx"),  -- l.1235 `movq %rbx, %r8`
    .bt "%r10" (.imm 0),  -- l.1236 `btq $0, %r10`
    .adcx "%r8" (.reg "%rbp"),  -- l.1237 `adcxq %rbp, %r8`
    .setc "%r9",  -- l.1238 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbp" (.imm 0),  -- l.1240 `movq $0, %rbp`
    .mov "%r9" (.imm 0),  -- l.1241 `movl $0, %r9d`
    .mov "%r10" (.reg "%r8"),  -- l.1242 `movq %r8, %r10`
    .imul "%r10" (.reg "%rax"),  -- l.1243 `imulq %rax, %r10`
    .mov "%rdx" (.reg "%r8"),  -- l.1244 `movq %r8, %rdx`
    .mulx "%r12" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.1245 `mulx %rax, %r10, %r12`
    .mov "%r8" (.reg "%r10"),  -- l.1246 `movq %r10, %r8`
    .bt "%r9" (.imm 0),  -- l.1247 `btq $0, %r9`
    .adcx "%r8" (.reg "%rbp"),  -- l.1248 `adcxq %rbp, %r8`
    .setc "%r13",  -- l.1249 `setc %r13b; movzbq %r13b, %r13`
    .mov "%r9" (.reg "%r12"),  -- l.1251 `movq %r12, %r9`
    .bt "%r13" (.imm 0),  -- l.1252 `btq $0, %r13`
    .adcx "%r9" (.reg "%rbp"),  -- l.1253 `adcxq %rbp, %r9`
    .mov "%rbp" (.imm 0),  -- l.1254 `movl $0, %ebp`
    .mov "%r10" (.reg "%r11"),  -- l.1255 `movq %r11, %r10`
    .bt "%rbp" (.imm 0),  -- l.1256 `btq $0, %rbp`
    .adcx "%r10" (.reg "%r8"),  -- l.1257 `adcxq %r8, %r10`
    .setc "%r12",  -- l.1258 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rcx"),  -- l.1260 `movq %rcx, %rbp`
    .bt "%r12" (.imm 0),  -- l.1261 `btq $0, %r12`
    .adcx "%rbp" (.reg "%r9"),  -- l.1262 `adcxq %r9, %rbp`
    .setc "%r8",  -- l.1263 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rcx" (.reg "%rdi") ]  -- l.1265 `movq %rdi, %rcx`

/-- Segment 37 of the body: the 32 instructions from source lines 1266–1303. -/
def ed25519PointAddShippedSeg037 : List (JInstr 64) :=
  [ .bt "%r8" (.imm 0),  -- l.1266 `btq $0, %r8`
    .adcx "%rcx" (.reg "%rbx"),  -- l.1267 `adcxq %rbx, %rcx`
    .setc "%r9",  -- l.1268 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rdi" (.reg "%rsi"),  -- l.1270 `movq %rsi, %rdi`
    .bt "%r9" (.imm 0),  -- l.1271 `btq $0, %r9`
    .adcx "%rdi" (.reg "%rbx"),  -- l.1272 `adcxq %rbx, %rdi`
    .setc "%r8",  -- l.1273 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rsi" (.reg "%rbx"),  -- l.1275 `movq %rbx, %rsi`
    .test "%r8" (.reg "%r8"),  -- l.1276 `testq %r8, %r8`
    .cmovne "%rsi" (.reg "%rax"),  -- l.1277 `cmovneq %rax, %rsi`
    .mov "%rax" (.imm 0),  -- l.1278 `movl $0, %eax`
    .mov "%r8" (.reg "%r10"),  -- l.1279 `movq %r10, %r8`
    .bt "%rax" (.imm 0),  -- l.1280 `btq $0, %rax`
    .adcx "%r8" (.reg "%rsi"),  -- l.1281 `adcxq %rsi, %r8`
    .setc "%r9",  -- l.1282 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rbp"),  -- l.1284 `movq %rbp, %rax`
    .bt "%r9" (.imm 0),  -- l.1285 `btq $0, %r9`
    .adcx "%rax" (.reg "%rbx"),  -- l.1286 `adcxq %rbx, %rax`
    .setc "%rsi",  -- l.1287 `setc %sil; movzbq %sil, %rsi`
    .mov "%rbp" (.reg "%rcx"),  -- l.1289 `movq %rcx, %rbp`
    .bt "%rsi" (.imm 0),  -- l.1290 `btq $0, %rsi`
    .adcx "%rbp" (.reg "%rbx"),  -- l.1291 `adcxq %rbx, %rbp`
    .setc "%r9",  -- l.1292 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi"),  -- l.1294 `movq %rdi, %rcx`
    .bt "%r9" (.imm 0),  -- l.1295 `btq $0, %r9`
    .adcx "%rcx" (.reg "%rbx"),  -- l.1296 `adcxq %rbx, %rcx`
    .setc "%rsi",  -- l.1297 `setc %sil; movzbq %sil, %rsi`
    .mov "%rbx" (.imm 19),  -- l.1299 `movq $19, %rbx`
    .mov "%rsi" (.imm 0),  -- l.1300 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.1301 `movq $0, %rdi`
    .mov "%r9" (.imm 9223372036854775808),  -- l.1302 `movq $9223372036854775808, %r9`
    .mov "%r10" (.imm 0) ]  -- l.1303 `movl $0, %r10d`

/-- Segment 38 of the body: the 32 instructions from source lines 1304–1339. -/
def ed25519PointAddShippedSeg038 : List (JInstr 64) :=
  [ .mov "%r11" (.reg "%r8"),  -- l.1304 `movq %r8, %r11`
    .bt "%r10" (.imm 0),  -- l.1305 `btq $0, %r10`
    .adcx "%r11" (.reg "%rbx"),  -- l.1306 `adcxq %rbx, %r11`
    .setc "%r12",  -- l.1307 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbx" (.reg "%rax"),  -- l.1309 `movq %rax, %rbx`
    .bt "%r12" (.imm 0),  -- l.1310 `btq $0, %r12`
    .adcx "%rbx" (.reg "%rsi"),  -- l.1311 `adcxq %rsi, %rbx`
    .setc "%r10",  -- l.1312 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rbp"),  -- l.1314 `movq %rbp, %rsi`
    .bt "%r10" (.imm 0),  -- l.1315 `btq $0, %r10`
    .adcx "%rsi" (.reg "%rdi"),  -- l.1316 `adcxq %rdi, %rsi`
    .setc "%r12",  -- l.1317 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rcx"),  -- l.1319 `movq %rcx, %rdi`
    .bt "%r12" (.imm 0),  -- l.1320 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.1321 `adcxq %r9, %rdi`
    .setc "%r10",  -- l.1322 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%r8"),  -- l.1324 `movq %r8, %r9`
    .test "%r10" (.reg "%r10"),  -- l.1325 `testq %r10, %r10`
    .cmovne "%r9" (.reg "%r11"),  -- l.1326 `cmovneq %r11, %r9`
    .mov "%r8" (.reg "%rax"),  -- l.1327 `movq %rax, %r8`
    .test "%r10" (.reg "%r10"),  -- l.1328 `testq %r10, %r10`
    .cmovne "%r8" (.reg "%rbx"),  -- l.1329 `cmovneq %rbx, %r8`
    .mov "%rax" (.reg "%rbp"),  -- l.1330 `movq %rbp, %rax`
    .test "%r10" (.reg "%r10"),  -- l.1331 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rsi"),  -- l.1332 `cmovneq %rsi, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.1333 `movq %rcx, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.1334 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rdi"),  -- l.1335 `cmovneq %rdi, %rbx`
    .mov "%rcx" (.imm 19),  -- l.1336 `movq $19, %rcx`
    .mov "%rsi" (.imm 0),  -- l.1337 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.1338 `movq $0, %rdi`
    .mov "%rbp" (.imm 9223372036854775808) ]  -- l.1339 `movq $9223372036854775808, %rbp`

/-- Segment 39 of the body: the 32 instructions from source lines 1340–1375. -/
def ed25519PointAddShippedSeg039 : List (JInstr 64) :=
  [ .mov "%r10" (.imm 0),  -- l.1340 `movl $0, %r10d`
    .mov "%r11" (.reg "%r9"),  -- l.1341 `movq %r9, %r11`
    .bt "%r10" (.imm 0),  -- l.1342 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.1343 `adcxq %rcx, %r11`
    .setc "%r12",  -- l.1344 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rcx" (.reg "%r8"),  -- l.1346 `movq %r8, %rcx`
    .bt "%r12" (.imm 0),  -- l.1347 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rsi"),  -- l.1348 `adcxq %rsi, %rcx`
    .setc "%r10",  -- l.1349 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rax"),  -- l.1351 `movq %rax, %rsi`
    .bt "%r10" (.imm 0),  -- l.1352 `btq $0, %r10`
    .adcx "%rsi" (.reg "%rdi"),  -- l.1353 `adcxq %rdi, %rsi`
    .setc "%r12",  -- l.1354 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rbx"),  -- l.1356 `movq %rbx, %rdi`
    .bt "%r12" (.imm 0),  -- l.1357 `btq $0, %r12`
    .adcx "%rdi" (.reg "%rbp"),  -- l.1358 `adcxq %rbp, %rdi`
    .setc "%r10",  -- l.1359 `setc %r10b; movzbq %r10b, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1361 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r9"),  -- l.1362 `movq %r9, %rax`
    .test "%r10" (.reg "%r10"),  -- l.1363 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%r11"),  -- l.1364 `cmovneq %r11, %rax`
    .storeMem "%rsp" 208 (.reg "%rax"),  -- l.1365 `movq %rax, 208(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1366 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1367 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.1368 `movq %r8, %rax`
    .test "%r10" (.reg "%r10"),  -- l.1369 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rcx"),  -- l.1370 `cmovneq %rcx, %rax`
    .storeMem "%rsp" 216 (.reg "%rax"),  -- l.1371 `movq %rax, 216(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1372 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.1373 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rax"),  -- l.1374 `movq %rax, %rbx`
    .test "%r10" (.reg "%r10") ]  -- l.1375 `testq %r10, %r10`

/-- Segment 40 of the body: the 32 instructions from source lines 1376–1408. -/
def ed25519PointAddShippedSeg040 : List (JInstr 64) :=
  [ .cmovne "%rbx" (.reg "%rsi"),  -- l.1376 `cmovneq %rsi, %rbx`
    .storeMem "%rsp" 224 (.reg "%rbx"),  -- l.1377 `movq %rbx, 224(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.1378 `movq -128(%rsp), %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1379 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.1380 `movq %rbx, %rax`
    .test "%r10" (.reg "%r10"),  -- l.1381 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rdi"),  -- l.1382 `cmovneq %rdi, %rax`
    .storeMem "%rsp" 264 (.reg "%rax"),  -- l.1383 `movq %rax, 264(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1384 `movq -128(%rsp), %rax`
    .mov "%rbx" (.imm 16993941304535871833),  -- l.1385 `movq $16993941304535871833, %rbx`
    .mov "%rsi" (.imm 63073048630374742),  -- l.1386 `movq $63073048630374742, %rsi`
    .mov "%rdi" (.imm 1841551078520508720),  -- l.1387 `movq $1841551078520508720, %rdi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1388 `movq %rax, -128(%rsp)`
    .mov "%rax" (.imm 2596001775599221991),  -- l.1389 `movq $2596001775599221991, %rax`
    .storeMem "%rsp" 168 (.reg "%rax"),  -- l.1390 `movq %rax, 168(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1391 `movq -128(%rsp), %rax`
    .mov "%r10" (.imm 0),  -- l.1392 `movq $0, %r10`
    .mov "%r11" (.imm 0),  -- l.1393 `movl $0, %r11d`
    .loadMem "%r12" "%rsp" 160,  -- l.1394 `movq 160(%rsp), %r12`
    .imul "%r12" (.reg "%rbx"),  -- l.1395 `imulq %rbx, %r12`
    .loadMem "%rdx" "%rsp" 160,  -- l.1396 `movq 160(%rsp), %rdx`
    .mulx "%r13" "%r12" (.reg "%rdx") (.reg "%rbx"),  -- l.1397 `mulx %rbx, %r12, %r13`
    .bt "%r11" (.imm 0),  -- l.1398 `btq $0, %r11`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1399 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r12"),  -- l.1400 `movq %r12, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.1401 `adcxq %r10, %rax`
    .storeMem "%rsp" 184 (.reg "%rax"),  -- l.1402 `movq %rax, 184(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1403 `movq -128(%rsp), %rax`
    .setc "%rcx",  -- l.1404 `setc %cl; movzbq %cl, %rcx`
    .loadMem "%r11" "%rsp" 176,  -- l.1406 `movq 176(%rsp), %r11`
    .imul "%r11" (.reg "%rbx"),  -- l.1407 `imulq %rbx, %r11`
    .loadMem "%rdx" "%rsp" 176 ]  -- l.1408 `movq 176(%rsp), %rdx`

/-- Segment 41 of the body: the 32 instructions from source lines 1409–1443. -/
def ed25519PointAddShippedSeg041 : List (JInstr 64) :=
  [ .mulx "%r12" "%r11" (.reg "%rdx") (.reg "%rbx"),  -- l.1409 `mulx %rbx, %r11, %r12`
    .mov "%r9" (.reg "%r11"),  -- l.1410 `movq %r11, %r9`
    .bt "%rcx" (.imm 0),  -- l.1411 `btq $0, %rcx`
    .adcx "%r9" (.reg "%r13"),  -- l.1412 `adcxq %r13, %r9`
    .setc "%rbp",  -- l.1413 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rcx" "%rsp" 192,  -- l.1415 `movq 192(%rsp), %rcx`
    .imul "%rcx" (.reg "%rbx"),  -- l.1416 `imulq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 192,  -- l.1417 `movq 192(%rsp), %rdx`
    .mulx "%r11" "%rcx" (.reg "%rdx") (.reg "%rbx"),  -- l.1418 `mulx %rbx, %rcx, %r11`
    .mov "%r13" (.reg "%rcx"),  -- l.1419 `movq %rcx, %r13`
    .bt "%rbp" (.imm 0),  -- l.1420 `btq $0, %rbp`
    .adcx "%r13" (.reg "%r12"),  -- l.1421 `adcxq %r12, %r13`
    .setc "%rax",  -- l.1422 `setc %al; movzbq %al, %rax`
    .loadMem "%rcx" "%rsp" 200,  -- l.1424 `movq 200(%rsp), %rcx`
    .imul "%rcx" (.reg "%rbx"),  -- l.1425 `imulq %rbx, %rcx`
    .loadMem "%rdx" "%rsp" 200,  -- l.1426 `movq 200(%rsp), %rdx`
    .mulx "%rbp" "%rcx" (.reg "%rdx") (.reg "%rbx"),  -- l.1427 `mulx %rbx, %rcx, %rbp`
    .bt "%rax" (.imm 0),  -- l.1428 `btq $0, %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.1429 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rcx"),  -- l.1430 `movq %rcx, %rbx`
    .adcx "%rbx" (.reg "%r11"),  -- l.1431 `adcxq %r11, %rbx`
    .storeMem "%rsp" 144 (.reg "%rbx"),  -- l.1432 `movq %rbx, 144(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.1433 `movq -128(%rsp), %rbx`
    .setc "%r12",  -- l.1434 `setc %r12b; movzbq %r12b, %r12`
    .bt "%r12" (.imm 0),  -- l.1436 `btq $0, %r12`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1437 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbp"),  -- l.1438 `movq %rbp, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.1439 `adcxq %r10, %rax`
    .storeMem "%rsp" 152 (.reg "%rax"),  -- l.1440 `movq %rax, 152(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1441 `movq -128(%rsp), %rax`
    .mov "%rcx" (.imm 0),  -- l.1442 `movq $0, %rcx`
    .mov "%rbp" (.imm 0) ]  -- l.1443 `movl $0, %ebp`

/-- Segment 42 of the body: the 32 instructions from source lines 1444–1478. -/
def ed25519PointAddShippedSeg042 : List (JInstr 64) :=
  [ .loadMem "%r10" "%rsp" 160,  -- l.1444 `movq 160(%rsp), %r10`
    .imul "%r10" (.reg "%rsi"),  -- l.1445 `imulq %rsi, %r10`
    .loadMem "%rdx" "%rsp" 160,  -- l.1446 `movq 160(%rsp), %rdx`
    .mulx "%r11" "%r10" (.reg "%rdx") (.reg "%rsi"),  -- l.1447 `mulx %rsi, %r10, %r11`
    .mov "%r12" (.reg "%r10"),  -- l.1448 `movq %r10, %r12`
    .bt "%rbp" (.imm 0),  -- l.1449 `btq $0, %rbp`
    .adcx "%r12" (.reg "%rcx"),  -- l.1450 `adcxq %rcx, %r12`
    .setc "%r8",  -- l.1451 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rbp" "%rsp" 176,  -- l.1453 `movq 176(%rsp), %rbp`
    .imul "%rbp" (.reg "%rsi"),  -- l.1454 `imulq %rsi, %rbp`
    .loadMem "%rdx" "%rsp" 176,  -- l.1455 `movq 176(%rsp), %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rsi"),  -- l.1456 `mulx %rsi, %rbp, %r10`
    .mov "%rax" (.reg "%rbp"),  -- l.1457 `movq %rbp, %rax`
    .bt "%r8" (.imm 0),  -- l.1458 `btq $0, %r8`
    .adcx "%rax" (.reg "%r11"),  -- l.1459 `adcxq %r11, %rax`
    .setc "%rbx",  -- l.1460 `setc %bl; movzbq %bl, %rbx`
    .loadMem "%rbp" "%rsp" 192,  -- l.1462 `movq 192(%rsp), %rbp`
    .imul "%rbp" (.reg "%rsi"),  -- l.1463 `imulq %rsi, %rbp`
    .loadMem "%rdx" "%rsp" 192,  -- l.1464 `movq 192(%rsp), %rdx`
    .mulx "%r8" "%rbp" (.reg "%rdx") (.reg "%rsi"),  -- l.1465 `mulx %rsi, %rbp, %r8`
    .bt "%rbx" (.imm 0),  -- l.1466 `btq $0, %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1467 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbp"),  -- l.1468 `movq %rbp, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.1469 `adcxq %r10, %rax`
    .storeMem "%rsp" 136 (.reg "%rax"),  -- l.1470 `movq %rax, 136(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1471 `movq -128(%rsp), %rax`
    .setc "%r11",  -- l.1472 `setc %r11b; movzbq %r11b, %r11`
    .loadMem "%rbx" "%rsp" 200,  -- l.1474 `movq 200(%rsp), %rbx`
    .imul "%rbx" (.reg "%rsi"),  -- l.1475 `imulq %rsi, %rbx`
    .loadMem "%rdx" "%rsp" 200,  -- l.1476 `movq 200(%rsp), %rdx`
    .mulx "%rbp" "%rbx" (.reg "%rdx") (.reg "%rsi"),  -- l.1477 `mulx %rsi, %rbx, %rbp`
    .mov "%rsi" (.reg "%rbx") ]  -- l.1478 `movq %rbx, %rsi`

/-- Segment 43 of the body: the 32 instructions from source lines 1479–1515. -/
def ed25519PointAddShippedSeg043 : List (JInstr 64) :=
  [ .bt "%r11" (.imm 0),  -- l.1479 `btq $0, %r11`
    .adcx "%rsi" (.reg "%r8"),  -- l.1480 `adcxq %r8, %rsi`
    .setc "%r10",  -- l.1481 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbx" (.reg "%rbp"),  -- l.1483 `movq %rbp, %rbx`
    .bt "%r10" (.imm 0),  -- l.1484 `btq $0, %r10`
    .adcx "%rbx" (.reg "%rcx"),  -- l.1485 `adcxq %rcx, %rbx`
    .mov "%rcx" (.imm 0),  -- l.1486 `movq $0, %rcx`
    .mov "%rbp" (.imm 0),  -- l.1487 `movl $0, %ebp`
    .bt "%rbp" (.imm 0),  -- l.1488 `btq $0, %rbp`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1489 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r9"),  -- l.1490 `movq %r9, %rax`
    .adcx "%rax" (.reg "%r12"),  -- l.1491 `adcxq %r12, %rax`
    .storeMem "%rsp" 128 (.reg "%rax"),  -- l.1492 `movq %rax, 128(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1493 `movq -128(%rsp), %rax`
    .setc "%r10",  -- l.1494 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbp" (.reg "%r13"),  -- l.1496 `movq %r13, %rbp`
    .bt "%r10" (.imm 0),  -- l.1497 `btq $0, %r10`
    .adcx "%rbp" (.reg "%rax"),  -- l.1498 `adcxq %rax, %rbp`
    .setc "%r9",  -- l.1499 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rax" "%rsp" 144,  -- l.1501 `movq 144(%rsp), %rax`
    .bt "%r9" (.imm 0),  -- l.1502 `btq $0, %r9`
    .adcxMem "%rax" "%rsp" 136,  -- l.1503 `adcxq 136(%rsp), %rax`
    .setc "%r10",  -- l.1504 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%r9" "%rsp" 152,  -- l.1506 `movq 152(%rsp), %r9`
    .bt "%r10" (.imm 0),  -- l.1507 `btq $0, %r10`
    .adcx "%r9" (.reg "%rsi"),  -- l.1508 `adcxq %rsi, %r9`
    .setc "%r11",  -- l.1509 `setc %r11b; movzbq %r11b, %r11`
    .bt "%r11" (.imm 0),  -- l.1511 `btq $0, %r11`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1512 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.1513 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%rbx"),  -- l.1514 `adcxq %rbx, %rax`
    .storeMem "%rsp" 152 (.reg "%rax") ]  -- l.1515 `movq %rax, 152(%rsp)`

/-- Segment 44 of the body: the 32 instructions from source lines 1516–1551. -/
def ed25519PointAddShippedSeg044 : List (JInstr 64) :=
  [ .loadMem "%rax" "%rsp" (-128),  -- l.1516 `movq -128(%rsp), %rax`
    .setc "%r10",  -- l.1517 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbx" (.imm 0),  -- l.1519 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.1520 `movl $0, %ecx`
    .loadMem "%r10" "%rsp" 160,  -- l.1521 `movq 160(%rsp), %r10`
    .imul "%r10" (.reg "%rdi"),  -- l.1522 `imulq %rdi, %r10`
    .loadMem "%rdx" "%rsp" 160,  -- l.1523 `movq 160(%rsp), %rdx`
    .mulx "%r11" "%r10" (.reg "%rdx") (.reg "%rdi"),  -- l.1524 `mulx %rdi, %r10, %r11`
    .mov "%r12" (.reg "%r10"),  -- l.1525 `movq %r10, %r12`
    .bt "%rcx" (.imm 0),  -- l.1526 `btq $0, %rcx`
    .adcx "%r12" (.reg "%rbx"),  -- l.1527 `adcxq %rbx, %r12`
    .setc "%r13",  -- l.1528 `setc %r13b; movzbq %r13b, %r13`
    .loadMem "%rcx" "%rsp" 176,  -- l.1530 `movq 176(%rsp), %rcx`
    .imul "%rcx" (.reg "%rdi"),  -- l.1531 `imulq %rdi, %rcx`
    .loadMem "%rdx" "%rsp" 176,  -- l.1532 `movq 176(%rsp), %rdx`
    .mulx "%r10" "%rcx" (.reg "%rdx") (.reg "%rdi"),  -- l.1533 `mulx %rdi, %rcx, %r10`
    .mov "%r8" (.reg "%rcx"),  -- l.1534 `movq %rcx, %r8`
    .bt "%r13" (.imm 0),  -- l.1535 `btq $0, %r13`
    .adcx "%r8" (.reg "%r11"),  -- l.1536 `adcxq %r11, %r8`
    .setc "%rsi",  -- l.1537 `setc %sil; movzbq %sil, %rsi`
    .loadMem "%rcx" "%rsp" 192,  -- l.1539 `movq 192(%rsp), %rcx`
    .imul "%rcx" (.reg "%rdi"),  -- l.1540 `imulq %rdi, %rcx`
    .loadMem "%rdx" "%rsp" 192,  -- l.1541 `movq 192(%rsp), %rdx`
    .mulx "%r11" "%rcx" (.reg "%rdx") (.reg "%rdi"),  -- l.1542 `mulx %rdi, %rcx, %r11`
    .bt "%rsi" (.imm 0),  -- l.1543 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1544 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.1545 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.1546 `adcxq %r10, %rax`
    .storeMem "%rsp" 144 (.reg "%rax"),  -- l.1547 `movq %rax, 144(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1548 `movq -128(%rsp), %rax`
    .setc "%r13",  -- l.1549 `setc %r13b; movzbq %r13b, %r13`
    .loadMem "%rcx" "%rsp" 200 ]  -- l.1551 `movq 200(%rsp), %rcx`

/-- Segment 45 of the body: the 32 instructions from source lines 1552–1588. -/
def ed25519PointAddShippedSeg045 : List (JInstr 64) :=
  [ .imul "%rcx" (.reg "%rdi"),  -- l.1552 `imulq %rdi, %rcx`
    .loadMem "%rdx" "%rsp" 200,  -- l.1553 `movq 200(%rsp), %rdx`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%rdi"),  -- l.1554 `mulx %rdi, %rcx, %rsi`
    .mov "%rdi" (.reg "%rcx"),  -- l.1555 `movq %rcx, %rdi`
    .bt "%r13" (.imm 0),  -- l.1556 `btq $0, %r13`
    .adcx "%rdi" (.reg "%r11"),  -- l.1557 `adcxq %r11, %rdi`
    .setc "%r10",  -- l.1558 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rcx" (.reg "%rsi"),  -- l.1560 `movq %rsi, %rcx`
    .bt "%r10" (.imm 0),  -- l.1561 `btq $0, %r10`
    .adcx "%rcx" (.reg "%rbx"),  -- l.1562 `adcxq %rbx, %rcx`
    .mov "%rbx" (.imm 0),  -- l.1563 `movq $0, %rbx`
    .mov "%rsi" (.imm 0),  -- l.1564 `movl $0, %esi`
    .bt "%rsi" (.imm 0),  -- l.1565 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1566 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbp"),  -- l.1567 `movq %rbp, %rax`
    .adcx "%rax" (.reg "%r12"),  -- l.1568 `adcxq %r12, %rax`
    .storeMem "%rsp" 136 (.reg "%rax"),  -- l.1569 `movq %rax, 136(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1570 `movq -128(%rsp), %rax`
    .setc "%r11",  -- l.1571 `setc %r11b; movzbq %r11b, %r11`
    .mov "%rsi" (.reg "%rax"),  -- l.1573 `movq %rax, %rsi`
    .bt "%r11" (.imm 0),  -- l.1574 `btq $0, %r11`
    .adcx "%rsi" (.reg "%r8"),  -- l.1575 `adcxq %r8, %rsi`
    .setc "%rbp",  -- l.1576 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%rax" (.reg "%r9"),  -- l.1578 `movq %r9, %rax`
    .bt "%rbp" (.imm 0),  -- l.1579 `btq $0, %rbp`
    .adcxMem "%rax" "%rsp" 144,  -- l.1580 `adcxq 144(%rsp), %rax`
    .setc "%r8",  -- l.1581 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rbp" "%rsp" 152,  -- l.1583 `movq 152(%rsp), %rbp`
    .bt "%r8" (.imm 0),  -- l.1584 `btq $0, %r8`
    .adcx "%rbp" (.reg "%rdi"),  -- l.1585 `adcxq %rdi, %rbp`
    .setc "%r9",  -- l.1586 `setc %r9b; movzbq %r9b, %r9`
    .bt "%r9" (.imm 0) ]  -- l.1588 `btq $0, %r9`

/-- Segment 46 of the body: the 32 instructions from source lines 1589–1623. -/
def ed25519PointAddShippedSeg046 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1589 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.1590 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%rcx"),  -- l.1591 `adcxq %rcx, %rax`
    .storeMem "%rsp" 152 (.reg "%rax"),  -- l.1592 `movq %rax, 152(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1593 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.1594 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rbx" (.imm 0),  -- l.1596 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.1597 `movl $0, %ecx`
    .loadMem "%r8" "%rsp" 160,  -- l.1598 `movq 160(%rsp), %r8`
    .loadMem "%r15" "%rsp" 168,  -- l.1599 `movq 168(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.1600 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 160,  -- l.1601 `movq 160(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 168,  -- l.1602 `movq 168(%rsp), %r14`
    .mulx "%r9" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.1603 `mulx %r14, %r8, %r9`
    .mov "%r11" (.reg "%r8"),  -- l.1604 `movq %r8, %r11`
    .bt "%rcx" (.imm 0),  -- l.1605 `btq $0, %rcx`
    .adcx "%r11" (.reg "%rbx"),  -- l.1606 `adcxq %rbx, %r11`
    .setc "%r12",  -- l.1607 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rcx" "%rsp" 176,  -- l.1609 `movq 176(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 168,  -- l.1610 `movq 168(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1611 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 176,  -- l.1612 `movq 176(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 168,  -- l.1613 `movq 168(%rsp), %r14`
    .mulx "%r8" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1614 `mulx %r14, %rcx, %r8`
    .mov "%r13" (.reg "%rcx"),  -- l.1615 `movq %rcx, %r13`
    .bt "%r12" (.imm 0),  -- l.1616 `btq $0, %r12`
    .adcx "%r13" (.reg "%r9"),  -- l.1617 `adcxq %r9, %r13`
    .setc "%r10",  -- l.1618 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rcx" "%rsp" 192,  -- l.1620 `movq 192(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 168,  -- l.1621 `movq 168(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1622 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 192 ]  -- l.1623 `movq 192(%rsp), %rdx`

/-- Segment 47 of the body: the 32 instructions from source lines 1624–1658. -/
def ed25519PointAddShippedSeg047 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 168,  -- l.1624 `movq 168(%rsp), %r14`
    .mulx "%r9" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1625 `mulx %r14, %rcx, %r9`
    .mov "%r12" (.reg "%rcx"),  -- l.1626 `movq %rcx, %r12`
    .bt "%r10" (.imm 0),  -- l.1627 `btq $0, %r10`
    .adcx "%r12" (.reg "%r8"),  -- l.1628 `adcxq %r8, %r12`
    .setc "%rdi",  -- l.1629 `setc %dil; movzbq %dil, %rdi`
    .loadMem "%rcx" "%rsp" 200,  -- l.1631 `movq 200(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 168,  -- l.1632 `movq 168(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.1633 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 200,  -- l.1634 `movq 200(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 168,  -- l.1635 `movq 168(%rsp), %r14`
    .mulx "%r8" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.1636 `mulx %r14, %rcx, %r8`
    .bt "%rdi" (.imm 0),  -- l.1637 `btq $0, %rdi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1638 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.1639 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%r9"),  -- l.1640 `adcxq %r9, %rax`
    .storeMem "%rsp" 200 (.reg "%rax"),  -- l.1641 `movq %rax, 200(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1642 `movq -128(%rsp), %rax`
    .setc "%r10",  -- l.1643 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rcx" (.reg "%r8"),  -- l.1645 `movq %r8, %rcx`
    .bt "%r10" (.imm 0),  -- l.1646 `btq $0, %r10`
    .adcx "%rcx" (.reg "%rbx"),  -- l.1647 `adcxq %rbx, %rcx`
    .mov "%rbx" (.imm 0),  -- l.1648 `movq $0, %rbx`
    .mov "%rdi" (.imm 0),  -- l.1649 `movl $0, %edi`
    .mov "%r8" (.reg "%rsi"),  -- l.1650 `movq %rsi, %r8`
    .bt "%rdi" (.imm 0),  -- l.1651 `btq $0, %rdi`
    .adcx "%r8" (.reg "%r11"),  -- l.1652 `adcxq %r11, %r8`
    .setc "%r9",  -- l.1653 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rsi" (.reg "%rax"),  -- l.1655 `movq %rax, %rsi`
    .bt "%r9" (.imm 0),  -- l.1656 `btq $0, %r9`
    .adcx "%rsi" (.reg "%r13"),  -- l.1657 `adcxq %r13, %rsi`
    .setc "%rdi" ]  -- l.1658 `setc %dil; movzbq %dil, %rdi`

/-- Segment 48 of the body: the 32 instructions from source lines 1660–1696. -/
def ed25519PointAddShippedSeg048 : List (JInstr 64) :=
  [ .mov "%rax" (.reg "%rbp"),  -- l.1660 `movq %rbp, %rax`
    .bt "%rdi" (.imm 0),  -- l.1661 `btq $0, %rdi`
    .adcx "%rax" (.reg "%r12"),  -- l.1662 `adcxq %r12, %rax`
    .setc "%r9",  -- l.1663 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rdi" "%rsp" 152,  -- l.1665 `movq 152(%rsp), %rdi`
    .bt "%r9" (.imm 0),  -- l.1666 `btq $0, %r9`
    .adcxMem "%rdi" "%rsp" 200,  -- l.1667 `adcxq 200(%rsp), %rdi`
    .setc "%rbp",  -- l.1668 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%r9" (.reg "%rbx"),  -- l.1670 `movq %rbx, %r9`
    .bt "%rbp" (.imm 0),  -- l.1671 `btq $0, %rbp`
    .adcx "%r9" (.reg "%rcx"),  -- l.1672 `adcxq %rcx, %r9`
    .setc "%r10",  -- l.1673 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbx" (.imm 38),  -- l.1675 `movq $38, %rbx`
    .mov "%rcx" (.imm 0),  -- l.1676 `movq $0, %rcx`
    .mov "%rbp" (.imm 0),  -- l.1677 `movl $0, %ebp`
    .mov "%r10" (.reg "%rsi"),  -- l.1678 `movq %rsi, %r10`
    .imul "%r10" (.reg "%rbx"),  -- l.1679 `imulq %rbx, %r10`
    .mov "%rdx" (.reg "%rsi"),  -- l.1680 `movq %rsi, %rdx`
    .mulx "%r11" "%r10" (.reg "%rdx") (.reg "%rbx"),  -- l.1681 `mulx %rbx, %r10, %r11`
    .mov "%rsi" (.reg "%r10"),  -- l.1682 `movq %r10, %rsi`
    .bt "%rbp" (.imm 0),  -- l.1683 `btq $0, %rbp`
    .adcx "%rsi" (.reg "%rcx"),  -- l.1684 `adcxq %rcx, %rsi`
    .setc "%r12",  -- l.1685 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rax"),  -- l.1687 `movq %rax, %rbp`
    .imul "%rbp" (.reg "%rbx"),  -- l.1688 `imulq %rbx, %rbp`
    .mov "%rdx" (.reg "%rax"),  -- l.1689 `movq %rax, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rbx"),  -- l.1690 `mulx %rbx, %rbp, %r10`
    .mov "%rax" (.reg "%rbp"),  -- l.1691 `movq %rbp, %rax`
    .bt "%r12" (.imm 0),  -- l.1692 `btq $0, %r12`
    .adcx "%rax" (.reg "%r11"),  -- l.1693 `adcxq %r11, %rax`
    .setc "%r13",  -- l.1694 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%rdi") ]  -- l.1696 `movq %rdi, %rbp`

/-- Segment 49 of the body: the 32 instructions from source lines 1697–1732. -/
def ed25519PointAddShippedSeg049 : List (JInstr 64) :=
  [ .imul "%rbp" (.reg "%rbx"),  -- l.1697 `imulq %rbx, %rbp`
    .mov "%rdx" (.reg "%rdi"),  -- l.1698 `movq %rdi, %rdx`
    .mulx "%r11" "%rbp" (.reg "%rdx") (.reg "%rbx"),  -- l.1699 `mulx %rbx, %rbp, %r11`
    .mov "%rdi" (.reg "%rbp"),  -- l.1700 `movq %rbp, %rdi`
    .bt "%r13" (.imm 0),  -- l.1701 `btq $0, %r13`
    .adcx "%rdi" (.reg "%r10"),  -- l.1702 `adcxq %r10, %rdi`
    .setc "%r12",  -- l.1703 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%r9"),  -- l.1705 `movq %r9, %rbp`
    .imul "%rbp" (.reg "%rbx"),  -- l.1706 `imulq %rbx, %rbp`
    .mov "%rdx" (.reg "%r9"),  -- l.1707 `movq %r9, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rbx"),  -- l.1708 `mulx %rbx, %rbp, %r10`
    .mov "%r9" (.reg "%rbp"),  -- l.1709 `movq %rbp, %r9`
    .bt "%r12" (.imm 0),  -- l.1710 `btq $0, %r12`
    .adcx "%r9" (.reg "%r11"),  -- l.1711 `adcxq %r11, %r9`
    .setc "%r13",  -- l.1712 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%r10"),  -- l.1714 `movq %r10, %rbp`
    .bt "%r13" (.imm 0),  -- l.1715 `btq $0, %r13`
    .adcx "%rbp" (.reg "%rcx"),  -- l.1716 `adcxq %rcx, %rbp`
    .mov "%rcx" (.imm 0),  -- l.1717 `movq $0, %rcx`
    .mov "%r10" (.imm 0),  -- l.1718 `movl $0, %r10d`
    .loadMem "%r11" "%rsp" 184,  -- l.1719 `movq 184(%rsp), %r11`
    .bt "%r10" (.imm 0),  -- l.1720 `btq $0, %r10`
    .adcx "%r11" (.reg "%rsi"),  -- l.1721 `adcxq %rsi, %r11`
    .setc "%r12",  -- l.1722 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rsi" "%rsp" 128,  -- l.1724 `movq 128(%rsp), %rsi`
    .bt "%r12" (.imm 0),  -- l.1725 `btq $0, %r12`
    .adcx "%rsi" (.reg "%rax"),  -- l.1726 `adcxq %rax, %rsi`
    .setc "%r10",  -- l.1727 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rax" "%rsp" 136,  -- l.1729 `movq 136(%rsp), %rax`
    .bt "%r10" (.imm 0),  -- l.1730 `btq $0, %r10`
    .adcx "%rax" (.reg "%rdi"),  -- l.1731 `adcxq %rdi, %rax`
    .setc "%r12" ]  -- l.1732 `setc %r12b; movzbq %r12b, %r12`

/-- Segment 50 of the body: the 32 instructions from source lines 1734–1770. -/
def ed25519PointAddShippedSeg050 : List (JInstr 64) :=
  [ .mov "%rdi" (.reg "%r8"),  -- l.1734 `movq %r8, %rdi`
    .bt "%r12" (.imm 0),  -- l.1735 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.1736 `adcxq %r9, %rdi`
    .setc "%r10",  -- l.1737 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r8" (.reg "%rcx"),  -- l.1739 `movq %rcx, %r8`
    .bt "%r10" (.imm 0),  -- l.1740 `btq $0, %r10`
    .adcx "%r8" (.reg "%rbp"),  -- l.1741 `adcxq %rbp, %r8`
    .setc "%r9",  -- l.1742 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbp" (.imm 0),  -- l.1744 `movq $0, %rbp`
    .mov "%r9" (.imm 0),  -- l.1745 `movl $0, %r9d`
    .mov "%r10" (.reg "%r8"),  -- l.1746 `movq %r8, %r10`
    .imul "%r10" (.reg "%rbx"),  -- l.1747 `imulq %rbx, %r10`
    .mov "%rdx" (.reg "%r8"),  -- l.1748 `movq %r8, %rdx`
    .mulx "%r12" "%r10" (.reg "%rdx") (.reg "%rbx"),  -- l.1749 `mulx %rbx, %r10, %r12`
    .mov "%r8" (.reg "%r10"),  -- l.1750 `movq %r10, %r8`
    .bt "%r9" (.imm 0),  -- l.1751 `btq $0, %r9`
    .adcx "%r8" (.reg "%rbp"),  -- l.1752 `adcxq %rbp, %r8`
    .setc "%r13",  -- l.1753 `setc %r13b; movzbq %r13b, %r13`
    .mov "%r9" (.reg "%r12"),  -- l.1755 `movq %r12, %r9`
    .bt "%r13" (.imm 0),  -- l.1756 `btq $0, %r13`
    .adcx "%r9" (.reg "%rbp"),  -- l.1757 `adcxq %rbp, %r9`
    .mov "%rbp" (.imm 0),  -- l.1758 `movl $0, %ebp`
    .mov "%r10" (.reg "%r11"),  -- l.1759 `movq %r11, %r10`
    .bt "%rbp" (.imm 0),  -- l.1760 `btq $0, %rbp`
    .adcx "%r10" (.reg "%r8"),  -- l.1761 `adcxq %r8, %r10`
    .setc "%r12",  -- l.1762 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rsi"),  -- l.1764 `movq %rsi, %rbp`
    .bt "%r12" (.imm 0),  -- l.1765 `btq $0, %r12`
    .adcx "%rbp" (.reg "%r9"),  -- l.1766 `adcxq %r9, %rbp`
    .setc "%r8",  -- l.1767 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rsi" (.reg "%rax"),  -- l.1769 `movq %rax, %rsi`
    .bt "%r8" (.imm 0) ]  -- l.1770 `btq $0, %r8`

/-- Segment 51 of the body: the 32 instructions from source lines 1771–1808. -/
def ed25519PointAddShippedSeg051 : List (JInstr 64) :=
  [ .adcx "%rsi" (.reg "%rcx"),  -- l.1771 `adcxq %rcx, %rsi`
    .setc "%r9",  -- l.1772 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rdi"),  -- l.1774 `movq %rdi, %rax`
    .bt "%r9" (.imm 0),  -- l.1775 `btq $0, %r9`
    .adcx "%rax" (.reg "%rcx"),  -- l.1776 `adcxq %rcx, %rax`
    .setc "%r8",  -- l.1777 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rdi" (.reg "%rcx"),  -- l.1779 `movq %rcx, %rdi`
    .test "%r8" (.reg "%r8"),  -- l.1780 `testq %r8, %r8`
    .cmovne "%rdi" (.reg "%rbx"),  -- l.1781 `cmovneq %rbx, %rdi`
    .mov "%rbx" (.imm 0),  -- l.1782 `movl $0, %ebx`
    .mov "%r8" (.reg "%r10"),  -- l.1783 `movq %r10, %r8`
    .bt "%rbx" (.imm 0),  -- l.1784 `btq $0, %rbx`
    .adcx "%r8" (.reg "%rdi"),  -- l.1785 `adcxq %rdi, %r8`
    .setc "%r9",  -- l.1786 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbx" (.reg "%rbp"),  -- l.1788 `movq %rbp, %rbx`
    .bt "%r9" (.imm 0),  -- l.1789 `btq $0, %r9`
    .adcx "%rbx" (.reg "%rcx"),  -- l.1790 `adcxq %rcx, %rbx`
    .setc "%rdi",  -- l.1791 `setc %dil; movzbq %dil, %rdi`
    .mov "%rbp" (.reg "%rsi"),  -- l.1793 `movq %rsi, %rbp`
    .bt "%rdi" (.imm 0),  -- l.1794 `btq $0, %rdi`
    .adcx "%rbp" (.reg "%rcx"),  -- l.1795 `adcxq %rcx, %rbp`
    .setc "%r9",  -- l.1796 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rsi" (.reg "%rax"),  -- l.1798 `movq %rax, %rsi`
    .bt "%r9" (.imm 0),  -- l.1799 `btq $0, %r9`
    .adcx "%rsi" (.reg "%rcx"),  -- l.1800 `adcxq %rcx, %rsi`
    .setc "%rdi",  -- l.1801 `setc %dil; movzbq %dil, %rdi`
    .mov "%rax" (.imm 19),  -- l.1803 `movq $19, %rax`
    .mov "%rcx" (.imm 0),  -- l.1804 `movq $0, %rcx`
    .mov "%rdi" (.imm 0),  -- l.1805 `movq $0, %rdi`
    .mov "%r9" (.imm 9223372036854775808),  -- l.1806 `movq $9223372036854775808, %r9`
    .mov "%r10" (.imm 0),  -- l.1807 `movl $0, %r10d`
    .mov "%r11" (.reg "%r8") ]  -- l.1808 `movq %r8, %r11`

/-- Segment 52 of the body: the 32 instructions from source lines 1809–1844. -/
def ed25519PointAddShippedSeg052 : List (JInstr 64) :=
  [ .bt "%r10" (.imm 0),  -- l.1809 `btq $0, %r10`
    .adcx "%r11" (.reg "%rax"),  -- l.1810 `adcxq %rax, %r11`
    .setc "%r12",  -- l.1811 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rax" (.reg "%rbx"),  -- l.1813 `movq %rbx, %rax`
    .bt "%r12" (.imm 0),  -- l.1814 `btq $0, %r12`
    .adcx "%rax" (.reg "%rcx"),  -- l.1815 `adcxq %rcx, %rax`
    .setc "%r10",  -- l.1816 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rcx" (.reg "%rbp"),  -- l.1818 `movq %rbp, %rcx`
    .bt "%r10" (.imm 0),  -- l.1819 `btq $0, %r10`
    .adcx "%rcx" (.reg "%rdi"),  -- l.1820 `adcxq %rdi, %rcx`
    .setc "%r12",  -- l.1821 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rsi"),  -- l.1823 `movq %rsi, %rdi`
    .bt "%r12" (.imm 0),  -- l.1824 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.1825 `adcxq %r9, %rdi`
    .setc "%r10",  -- l.1826 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%r8"),  -- l.1828 `movq %r8, %r9`
    .test "%r10" (.reg "%r10"),  -- l.1829 `testq %r10, %r10`
    .cmovne "%r9" (.reg "%r11"),  -- l.1830 `cmovneq %r11, %r9`
    .mov "%r8" (.reg "%rbx"),  -- l.1831 `movq %rbx, %r8`
    .test "%r10" (.reg "%r10"),  -- l.1832 `testq %r10, %r10`
    .cmovne "%r8" (.reg "%rax"),  -- l.1833 `cmovneq %rax, %r8`
    .mov "%rax" (.reg "%rbp"),  -- l.1834 `movq %rbp, %rax`
    .test "%r10" (.reg "%r10"),  -- l.1835 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rcx"),  -- l.1836 `cmovneq %rcx, %rax`
    .mov "%rbx" (.reg "%rsi"),  -- l.1837 `movq %rsi, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.1838 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rdi"),  -- l.1839 `cmovneq %rdi, %rbx`
    .mov "%rcx" (.imm 19),  -- l.1840 `movq $19, %rcx`
    .mov "%rsi" (.imm 0),  -- l.1841 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.1842 `movq $0, %rdi`
    .mov "%rbp" (.imm 9223372036854775808),  -- l.1843 `movq $9223372036854775808, %rbp`
    .mov "%r10" (.imm 0) ]  -- l.1844 `movl $0, %r10d`

/-- Segment 53 of the body: the 32 instructions from source lines 1845–1880. -/
def ed25519PointAddShippedSeg053 : List (JInstr 64) :=
  [ .mov "%r11" (.reg "%r9"),  -- l.1845 `movq %r9, %r11`
    .bt "%r10" (.imm 0),  -- l.1846 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.1847 `adcxq %rcx, %r11`
    .setc "%r12",  -- l.1848 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rcx" (.reg "%r8"),  -- l.1850 `movq %r8, %rcx`
    .bt "%r12" (.imm 0),  -- l.1851 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rsi"),  -- l.1852 `adcxq %rsi, %rcx`
    .setc "%r10",  -- l.1853 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rax"),  -- l.1855 `movq %rax, %rsi`
    .bt "%r10" (.imm 0),  -- l.1856 `btq $0, %r10`
    .adcx "%rsi" (.reg "%rdi"),  -- l.1857 `adcxq %rdi, %rsi`
    .setc "%r12",  -- l.1858 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rbx"),  -- l.1860 `movq %rbx, %rdi`
    .bt "%r12" (.imm 0),  -- l.1861 `btq $0, %r12`
    .adcx "%rdi" (.reg "%rbp"),  -- l.1862 `adcxq %rbp, %rdi`
    .setc "%r10",  -- l.1863 `setc %r10b; movzbq %r10b, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1865 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r9"),  -- l.1866 `movq %r9, %rax`
    .test "%r10" (.reg "%r10"),  -- l.1867 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%r11"),  -- l.1868 `cmovneq %r11, %rax`
    .storeMem "%rsp" 168 (.reg "%rax"),  -- l.1869 `movq %rax, 168(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1870 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1871 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.1872 `movq %r8, %rax`
    .test "%r10" (.reg "%r10"),  -- l.1873 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rcx"),  -- l.1874 `cmovneq %rcx, %rax`
    .storeMem "%rsp" 176 (.reg "%rax"),  -- l.1875 `movq %rax, 176(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1876 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.1877 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rax"),  -- l.1878 `movq %rax, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.1879 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rsi") ]  -- l.1880 `cmovneq %rsi, %rbx`

/-- Segment 54 of the body: the 32 instructions from source lines 1881–1913. -/
def ed25519PointAddShippedSeg054 : List (JInstr 64) :=
  [ .storeMem "%rsp" 184 (.reg "%rbx"),  -- l.1881 `movq %rbx, 184(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.1882 `movq -128(%rsp), %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1883 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.1884 `movq %rbx, %rax`
    .test "%r10" (.reg "%r10"),  -- l.1885 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rdi"),  -- l.1886 `cmovneq %rdi, %rax`
    .storeMem "%rsp" 192 (.reg "%rax"),  -- l.1887 `movq %rax, 192(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1888 `movq -128(%rsp), %rax`
    .mov "%rbx" (.imm 0),  -- l.1889 `movq $0, %rbx`
    .mov "%rsi" (.imm 0),  -- l.1890 `movl $0, %esi`
    .loadMem "%rdi" "%rsp" 168,  -- l.1891 `movq 168(%rsp), %rdi`
    .loadMem "%r15" "%rsp" 272,  -- l.1892 `movq 272(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.1893 `imulq %r15, %rdi`
    .loadMem "%rdx" "%rsp" 168,  -- l.1894 `movq 168(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 272,  -- l.1895 `movq 272(%rsp), %r14`
    .mulx "%r8" "%rdi" (.reg "%rdx") (.reg "%r14"),  -- l.1896 `mulx %r14, %rdi, %r8`
    .bt "%rsi" (.imm 0),  -- l.1897 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1898 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.1899 `movq %rdi, %rax`
    .adcx "%rax" (.reg "%rbx"),  -- l.1900 `adcxq %rbx, %rax`
    .storeMem "%rsp" 200 (.reg "%rax"),  -- l.1901 `movq %rax, 200(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1902 `movq -128(%rsp), %rax`
    .setc "%r11",  -- l.1903 `setc %r11b; movzbq %r11b, %r11`
    .loadMem "%rsi" "%rsp" 176,  -- l.1905 `movq 176(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 272,  -- l.1906 `movq 272(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.1907 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 176,  -- l.1908 `movq 176(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 272,  -- l.1909 `movq 272(%rsp), %r14`
    .mulx "%rdi" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1910 `mulx %r14, %rsi, %rdi`
    .mov "%r12" (.reg "%rsi"),  -- l.1911 `movq %rsi, %r12`
    .bt "%r11" (.imm 0),  -- l.1912 `btq $0, %r11`
    .adcx "%r12" (.reg "%r8") ]  -- l.1913 `adcxq %r8, %r12`

/-- Segment 55 of the body: the 32 instructions from source lines 1914–1948. -/
def ed25519PointAddShippedSeg055 : List (JInstr 64) :=
  [ .setc "%r13",  -- l.1914 `setc %r13b; movzbq %r13b, %r13`
    .loadMem "%rsi" "%rsp" 184,  -- l.1916 `movq 184(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 272,  -- l.1917 `movq 272(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.1918 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 184,  -- l.1919 `movq 184(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 272,  -- l.1920 `movq 272(%rsp), %r14`
    .mulx "%r8" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1921 `mulx %r14, %rsi, %r8`
    .mov "%r11" (.reg "%rsi"),  -- l.1922 `movq %rsi, %r11`
    .bt "%r13" (.imm 0),  -- l.1923 `btq $0, %r13`
    .adcx "%r11" (.reg "%rdi"),  -- l.1924 `adcxq %rdi, %r11`
    .setc "%r10",  -- l.1925 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rsi" "%rsp" 192,  -- l.1927 `movq 192(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 272,  -- l.1928 `movq 272(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.1929 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 192,  -- l.1930 `movq 192(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 272,  -- l.1931 `movq 272(%rsp), %r14`
    .mulx "%rdi" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.1932 `mulx %r14, %rsi, %rdi`
    .bt "%r10" (.imm 0),  -- l.1933 `btq $0, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1934 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rsi"),  -- l.1935 `movq %rsi, %rax`
    .adcx "%rax" (.reg "%r8"),  -- l.1936 `adcxq %r8, %rax`
    .storeMem "%rsp" 272 (.reg "%rax"),  -- l.1937 `movq %rax, 272(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.1938 `movq -128(%rsp), %rax`
    .setc "%r13",  -- l.1939 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rsi" (.reg "%rdi"),  -- l.1941 `movq %rdi, %rsi`
    .bt "%r13" (.imm 0),  -- l.1942 `btq $0, %r13`
    .adcx "%rsi" (.reg "%rbx"),  -- l.1943 `adcxq %rbx, %rsi`
    .mov "%rbx" (.imm 0),  -- l.1944 `movq $0, %rbx`
    .mov "%rdi" (.imm 0),  -- l.1945 `movl $0, %edi`
    .loadMem "%r8" "%rsp" 168,  -- l.1946 `movq 168(%rsp), %r8`
    .loadMem "%r15" "%rsp" 280,  -- l.1947 `movq 280(%rsp), %r15`
    .imul "%r8" (.reg "%r15") ]  -- l.1948 `imulq %r15, %r8`

/-- Segment 56 of the body: the 32 instructions from source lines 1949–1983. -/
def ed25519PointAddShippedSeg056 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsp" 168,  -- l.1949 `movq 168(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 280,  -- l.1950 `movq 280(%rsp), %r14`
    .mulx "%r10" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.1951 `mulx %r14, %r8, %r10`
    .mov "%r13" (.reg "%r8"),  -- l.1952 `movq %r8, %r13`
    .bt "%rdi" (.imm 0),  -- l.1953 `btq $0, %rdi`
    .adcx "%r13" (.reg "%rbx"),  -- l.1954 `adcxq %rbx, %r13`
    .setc "%rax",  -- l.1955 `setc %al; movzbq %al, %rax`
    .loadMem "%rdi" "%rsp" 176,  -- l.1957 `movq 176(%rsp), %rdi`
    .loadMem "%r15" "%rsp" 280,  -- l.1958 `movq 280(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.1959 `imulq %r15, %rdi`
    .loadMem "%rdx" "%rsp" 176,  -- l.1960 `movq 176(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 280,  -- l.1961 `movq 280(%rsp), %r14`
    .mulx "%r8" "%rdi" (.reg "%rdx") (.reg "%r14"),  -- l.1962 `mulx %r14, %rdi, %r8`
    .mov "%rcx" (.reg "%rdi"),  -- l.1963 `movq %rdi, %rcx`
    .bt "%rax" (.imm 0),  -- l.1964 `btq $0, %rax`
    .adcx "%rcx" (.reg "%r10"),  -- l.1965 `adcxq %r10, %rcx`
    .setc "%r9",  -- l.1966 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rax" "%rsp" 184,  -- l.1968 `movq 184(%rsp), %rax`
    .loadMem "%r15" "%rsp" 280,  -- l.1969 `movq 280(%rsp), %r15`
    .imul "%rax" (.reg "%r15"),  -- l.1970 `imulq %r15, %rax`
    .loadMem "%rdx" "%rsp" 184,  -- l.1971 `movq 184(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 280,  -- l.1972 `movq 280(%rsp), %r14`
    .mulx "%rdi" "%rax" (.reg "%rdx") (.reg "%r14"),  -- l.1973 `mulx %r14, %rax, %rdi`
    .mov "%r10" (.reg "%rax"),  -- l.1974 `movq %rax, %r10`
    .bt "%r9" (.imm 0),  -- l.1975 `btq $0, %r9`
    .adcx "%r10" (.reg "%r8"),  -- l.1976 `adcxq %r8, %r10`
    .setc "%rbp",  -- l.1977 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rax" "%rsp" 192,  -- l.1979 `movq 192(%rsp), %rax`
    .loadMem "%r15" "%rsp" 280,  -- l.1980 `movq 280(%rsp), %r15`
    .imul "%rax" (.reg "%r15"),  -- l.1981 `imulq %r15, %rax`
    .loadMem "%rdx" "%rsp" 192,  -- l.1982 `movq 192(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 280 ]  -- l.1983 `movq 280(%rsp), %r14`

/-- Segment 57 of the body: the 32 instructions from source lines 1984–2019. -/
def ed25519PointAddShippedSeg057 : List (JInstr 64) :=
  [ .mulx "%r8" "%rax" (.reg "%rdx") (.reg "%r14"),  -- l.1984 `mulx %r14, %rax, %r8`
    .bt "%rbp" (.imm 0),  -- l.1985 `btq $0, %rbp`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.1986 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rax"),  -- l.1987 `movq %rax, %rbx`
    .adcx "%rbx" (.reg "%rdi"),  -- l.1988 `adcxq %rdi, %rbx`
    .storeMem "%rsp" 280 (.reg "%rbx"),  -- l.1989 `movq %rbx, 280(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.1990 `movq -128(%rsp), %rbx`
    .setc "%r9",  -- l.1991 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%r8"),  -- l.1993 `movq %r8, %rax`
    .bt "%r9" (.imm 0),  -- l.1994 `btq $0, %r9`
    .adcx "%rax" (.reg "%rbx"),  -- l.1995 `adcxq %rbx, %rax`
    .mov "%rbx" (.imm 0),  -- l.1996 `movq $0, %rbx`
    .mov "%rdi" (.imm 0),  -- l.1997 `movl $0, %edi`
    .bt "%rdi" (.imm 0),  -- l.1998 `btq $0, %rdi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.1999 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r12"),  -- l.2000 `movq %r12, %rax`
    .adcx "%rax" (.reg "%r13"),  -- l.2001 `adcxq %r13, %rax`
    .storeMem "%rsp" 160 (.reg "%rax"),  -- l.2002 `movq %rax, 160(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2003 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.2004 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rdi" (.reg "%r11"),  -- l.2006 `movq %r11, %rdi`
    .bt "%r8" (.imm 0),  -- l.2007 `btq $0, %r8`
    .adcx "%rdi" (.reg "%rcx"),  -- l.2008 `adcxq %rcx, %rdi`
    .setc "%r9",  -- l.2009 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rcx" "%rsp" 272,  -- l.2011 `movq 272(%rsp), %rcx`
    .bt "%r9" (.imm 0),  -- l.2012 `btq $0, %r9`
    .adcx "%rcx" (.reg "%r10"),  -- l.2013 `adcxq %r10, %rcx`
    .setc "%r8",  -- l.2014 `setc %r8b; movzbq %r8b, %r8`
    .mov "%r9" (.reg "%rsi"),  -- l.2016 `movq %rsi, %r9`
    .bt "%r8" (.imm 0),  -- l.2017 `btq $0, %r8`
    .adcxMem "%r9" "%rsp" 280,  -- l.2018 `adcxq 280(%rsp), %r9`
    .setc "%r10" ]  -- l.2019 `setc %r10b; movzbq %r10b, %r10`

/-- Segment 58 of the body: the 32 instructions from source lines 2021–2055. -/
def ed25519PointAddShippedSeg058 : List (JInstr 64) :=
  [ .bt "%r10" (.imm 0),  -- l.2021 `btq $0, %r10`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2022 `movq %rcx, -128(%rsp)`
    .mov "%rcx" (.reg "%rbx"),  -- l.2023 `movq %rbx, %rcx`
    .adcx "%rcx" (.reg "%rax"),  -- l.2024 `adcxq %rax, %rcx`
    .storeMem "%rsp" 280 (.reg "%rcx"),  -- l.2025 `movq %rcx, 280(%rsp)`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2026 `movq -128(%rsp), %rcx`
    .setc "%r8",  -- l.2027 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rax" (.imm 0),  -- l.2029 `movq $0, %rax`
    .mov "%rbx" (.imm 0),  -- l.2030 `movl $0, %ebx`
    .loadMem "%r8" "%rsp" 168,  -- l.2031 `movq 168(%rsp), %r8`
    .loadMem "%r15" "%rsp" 288,  -- l.2032 `movq 288(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.2033 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 168,  -- l.2034 `movq 168(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 288,  -- l.2035 `movq 288(%rsp), %r14`
    .mulx "%r10" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.2036 `mulx %r14, %r8, %r10`
    .mov "%r11" (.reg "%r8"),  -- l.2037 `movq %r8, %r11`
    .bt "%rbx" (.imm 0),  -- l.2038 `btq $0, %rbx`
    .adcx "%r11" (.reg "%rax"),  -- l.2039 `adcxq %rax, %r11`
    .setc "%r12",  -- l.2040 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rbx" "%rsp" 176,  -- l.2042 `movq 176(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 288,  -- l.2043 `movq 288(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2044 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 176,  -- l.2045 `movq 176(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 288,  -- l.2046 `movq 288(%rsp), %r14`
    .mulx "%r8" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.2047 `mulx %r14, %rbx, %r8`
    .mov "%r13" (.reg "%rbx"),  -- l.2048 `movq %rbx, %r13`
    .bt "%r12" (.imm 0),  -- l.2049 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.2050 `adcxq %r10, %r13`
    .setc "%rbp",  -- l.2051 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rbx" "%rsp" 184,  -- l.2053 `movq 184(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 288,  -- l.2054 `movq 288(%rsp), %r15`
    .imul "%rbx" (.reg "%r15") ]  -- l.2055 `imulq %r15, %rbx`

/-- Segment 59 of the body: the 32 instructions from source lines 2056–2089. -/
def ed25519PointAddShippedSeg059 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsp" 184,  -- l.2056 `movq 184(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 288,  -- l.2057 `movq 288(%rsp), %r14`
    .mulx "%r10" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.2058 `mulx %r14, %rbx, %r10`
    .mov "%r12" (.reg "%rbx"),  -- l.2059 `movq %rbx, %r12`
    .bt "%rbp" (.imm 0),  -- l.2060 `btq $0, %rbp`
    .adcx "%r12" (.reg "%r8"),  -- l.2061 `adcxq %r8, %r12`
    .setc "%rsi",  -- l.2062 `setc %sil; movzbq %sil, %rsi`
    .loadMem "%rbx" "%rsp" 192,  -- l.2064 `movq 192(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 288,  -- l.2065 `movq 288(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2066 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 192,  -- l.2067 `movq 192(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 288,  -- l.2068 `movq 288(%rsp), %r14`
    .mulx "%rbp" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.2069 `mulx %r14, %rbx, %rbp`
    .bt "%rsi" (.imm 0),  -- l.2070 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2071 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.2072 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.2073 `adcxq %r10, %rax`
    .storeMem "%rsp" 288 (.reg "%rax"),  -- l.2074 `movq %rax, 288(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2075 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.2076 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rbx" (.reg "%rbp"),  -- l.2078 `movq %rbp, %rbx`
    .bt "%r8" (.imm 0),  -- l.2079 `btq $0, %r8`
    .adcx "%rbx" (.reg "%rax"),  -- l.2080 `adcxq %rax, %rbx`
    .mov "%rax" (.imm 0),  -- l.2081 `movq $0, %rax`
    .mov "%rsi" (.imm 0),  -- l.2082 `movl $0, %esi`
    .bt "%rsi" (.imm 0),  -- l.2083 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2084 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.2085 `movq %rdi, %rax`
    .adcx "%rax" (.reg "%r11"),  -- l.2086 `adcxq %r11, %rax`
    .storeMem "%rsp" 272 (.reg "%rax"),  -- l.2087 `movq %rax, 272(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2088 `movq -128(%rsp), %rax`
    .setc "%r8" ]  -- l.2089 `setc %r8b; movzbq %r8b, %r8`

/-- Segment 60 of the body: the 32 instructions from source lines 2091–2127. -/
def ed25519PointAddShippedSeg060 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rcx"),  -- l.2091 `movq %rcx, %rsi`
    .bt "%r8" (.imm 0),  -- l.2092 `btq $0, %r8`
    .adcx "%rsi" (.reg "%r13"),  -- l.2093 `adcxq %r13, %rsi`
    .setc "%rdi",  -- l.2094 `setc %dil; movzbq %dil, %rdi`
    .mov "%rcx" (.reg "%r9"),  -- l.2096 `movq %r9, %rcx`
    .bt "%rdi" (.imm 0),  -- l.2097 `btq $0, %rdi`
    .adcx "%rcx" (.reg "%r12"),  -- l.2098 `adcxq %r12, %rcx`
    .setc "%r8",  -- l.2099 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rdi" "%rsp" 280,  -- l.2101 `movq 280(%rsp), %rdi`
    .bt "%r8" (.imm 0),  -- l.2102 `btq $0, %r8`
    .adcxMem "%rdi" "%rsp" 288,  -- l.2103 `adcxq 288(%rsp), %rdi`
    .setc "%r9",  -- l.2104 `setc %r9b; movzbq %r9b, %r9`
    .bt "%r9" (.imm 0),  -- l.2106 `btq $0, %r9`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2107 `movq %rcx, -128(%rsp)`
    .mov "%rcx" (.reg "%rax"),  -- l.2108 `movq %rax, %rcx`
    .adcx "%rcx" (.reg "%rbx"),  -- l.2109 `adcxq %rbx, %rcx`
    .storeMem "%rsp" 288 (.reg "%rcx"),  -- l.2110 `movq %rcx, 288(%rsp)`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2111 `movq -128(%rsp), %rcx`
    .setc "%r10",  -- l.2112 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 0),  -- l.2114 `movq $0, %rax`
    .mov "%rbx" (.imm 0),  -- l.2115 `movl $0, %ebx`
    .loadMem "%r9" "%rsp" 168,  -- l.2116 `movq 168(%rsp), %r9`
    .loadMem "%r15" "%rsp" 296,  -- l.2117 `movq 296(%rsp), %r15`
    .imul "%r9" (.reg "%r15"),  -- l.2118 `imulq %r15, %r9`
    .loadMem "%rdx" "%rsp" 168,  -- l.2119 `movq 168(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 296,  -- l.2120 `movq 296(%rsp), %r14`
    .mulx "%r10" "%r9" (.reg "%rdx") (.reg "%r14"),  -- l.2121 `mulx %r14, %r9, %r10`
    .mov "%r11" (.reg "%r9"),  -- l.2122 `movq %r9, %r11`
    .bt "%rbx" (.imm 0),  -- l.2123 `btq $0, %rbx`
    .adcx "%r11" (.reg "%rax"),  -- l.2124 `adcxq %rax, %r11`
    .setc "%r12",  -- l.2125 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rbx" "%rsp" 176 ]  -- l.2127 `movq 176(%rsp), %rbx`

/-- Segment 61 of the body: the 32 instructions from source lines 2128–2161. -/
def ed25519PointAddShippedSeg061 : List (JInstr 64) :=
  [ .loadMem "%r15" "%rsp" 296,  -- l.2128 `movq 296(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2129 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 176,  -- l.2130 `movq 176(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 296,  -- l.2131 `movq 296(%rsp), %r14`
    .mulx "%r9" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.2132 `mulx %r14, %rbx, %r9`
    .mov "%r13" (.reg "%rbx"),  -- l.2133 `movq %rbx, %r13`
    .bt "%r12" (.imm 0),  -- l.2134 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.2135 `adcxq %r10, %r13`
    .setc "%rbp",  -- l.2136 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rbx" "%rsp" 184,  -- l.2138 `movq 184(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 296,  -- l.2139 `movq 296(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2140 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 184,  -- l.2141 `movq 184(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 296,  -- l.2142 `movq 296(%rsp), %r14`
    .mulx "%r10" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.2143 `mulx %r14, %rbx, %r10`
    .mov "%r12" (.reg "%rbx"),  -- l.2144 `movq %rbx, %r12`
    .bt "%rbp" (.imm 0),  -- l.2145 `btq $0, %rbp`
    .adcx "%r12" (.reg "%r9"),  -- l.2146 `adcxq %r9, %r12`
    .setc "%r8",  -- l.2147 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rbx" "%rsp" 192,  -- l.2149 `movq 192(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 296,  -- l.2150 `movq 296(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2151 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 192,  -- l.2152 `movq 192(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 296,  -- l.2153 `movq 296(%rsp), %r14`
    .mulx "%rbp" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.2154 `mulx %r14, %rbx, %rbp`
    .bt "%r8" (.imm 0),  -- l.2155 `btq $0, %r8`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2156 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.2157 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.2158 `adcxq %r10, %rax`
    .storeMem "%rsp" 296 (.reg "%rax"),  -- l.2159 `movq %rax, 296(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2160 `movq -128(%rsp), %rax`
    .setc "%r9" ]  -- l.2161 `setc %r9b; movzbq %r9b, %r9`

/-- Segment 62 of the body: the 32 instructions from source lines 2163–2199. -/
def ed25519PointAddShippedSeg062 : List (JInstr 64) :=
  [ .mov "%rbx" (.reg "%rbp"),  -- l.2163 `movq %rbp, %rbx`
    .bt "%r9" (.imm 0),  -- l.2164 `btq $0, %r9`
    .adcx "%rbx" (.reg "%rax"),  -- l.2165 `adcxq %rax, %rbx`
    .mov "%rax" (.imm 0),  -- l.2166 `movq $0, %rax`
    .mov "%rbp" (.imm 0),  -- l.2167 `movl $0, %ebp`
    .mov "%r8" (.reg "%rsi"),  -- l.2168 `movq %rsi, %r8`
    .bt "%rbp" (.imm 0),  -- l.2169 `btq $0, %rbp`
    .adcx "%r8" (.reg "%r11"),  -- l.2170 `adcxq %r11, %r8`
    .setc "%r9",  -- l.2171 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rsi" (.reg "%rcx"),  -- l.2173 `movq %rcx, %rsi`
    .bt "%r9" (.imm 0),  -- l.2174 `btq $0, %r9`
    .adcx "%rsi" (.reg "%r13"),  -- l.2175 `adcxq %r13, %rsi`
    .setc "%rbp",  -- l.2176 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%rcx" (.reg "%rdi"),  -- l.2178 `movq %rdi, %rcx`
    .bt "%rbp" (.imm 0),  -- l.2179 `btq $0, %rbp`
    .adcx "%rcx" (.reg "%r12"),  -- l.2180 `adcxq %r12, %rcx`
    .setc "%r9",  -- l.2181 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rdi" "%rsp" 288,  -- l.2183 `movq 288(%rsp), %rdi`
    .bt "%r9" (.imm 0),  -- l.2184 `btq $0, %r9`
    .adcxMem "%rdi" "%rsp" 296,  -- l.2185 `adcxq 296(%rsp), %rdi`
    .setc "%rbp",  -- l.2186 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%r9" (.reg "%rax"),  -- l.2188 `movq %rax, %r9`
    .bt "%rbp" (.imm 0),  -- l.2189 `btq $0, %rbp`
    .adcx "%r9" (.reg "%rbx"),  -- l.2190 `adcxq %rbx, %r9`
    .setc "%r10",  -- l.2191 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 38),  -- l.2193 `movq $38, %rax`
    .mov "%rbx" (.imm 0),  -- l.2194 `movq $0, %rbx`
    .mov "%rbp" (.imm 0),  -- l.2195 `movl $0, %ebp`
    .mov "%r10" (.reg "%rsi"),  -- l.2196 `movq %rsi, %r10`
    .imul "%r10" (.reg "%rax"),  -- l.2197 `imulq %rax, %r10`
    .mov "%rdx" (.reg "%rsi"),  -- l.2198 `movq %rsi, %rdx`
    .mulx "%r11" "%r10" (.reg "%rdx") (.reg "%rax") ]  -- l.2199 `mulx %rax, %r10, %r11`

/-- Segment 63 of the body: the 32 instructions from source lines 2200–2235. -/
def ed25519PointAddShippedSeg063 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%r10"),  -- l.2200 `movq %r10, %rsi`
    .bt "%rbp" (.imm 0),  -- l.2201 `btq $0, %rbp`
    .adcx "%rsi" (.reg "%rbx"),  -- l.2202 `adcxq %rbx, %rsi`
    .setc "%r12",  -- l.2203 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rcx"),  -- l.2205 `movq %rcx, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.2206 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%rcx"),  -- l.2207 `movq %rcx, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.2208 `mulx %rax, %rbp, %r10`
    .mov "%rcx" (.reg "%rbp"),  -- l.2209 `movq %rbp, %rcx`
    .bt "%r12" (.imm 0),  -- l.2210 `btq $0, %r12`
    .adcx "%rcx" (.reg "%r11"),  -- l.2211 `adcxq %r11, %rcx`
    .setc "%r13",  -- l.2212 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%rdi"),  -- l.2214 `movq %rdi, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.2215 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%rdi"),  -- l.2216 `movq %rdi, %rdx`
    .mulx "%r11" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.2217 `mulx %rax, %rbp, %r11`
    .mov "%rdi" (.reg "%rbp"),  -- l.2218 `movq %rbp, %rdi`
    .bt "%r13" (.imm 0),  -- l.2219 `btq $0, %r13`
    .adcx "%rdi" (.reg "%r10"),  -- l.2220 `adcxq %r10, %rdi`
    .setc "%r12",  -- l.2221 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%r9"),  -- l.2223 `movq %r9, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.2224 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%r9"),  -- l.2225 `movq %r9, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.2226 `mulx %rax, %rbp, %r10`
    .mov "%r9" (.reg "%rbp"),  -- l.2227 `movq %rbp, %r9`
    .bt "%r12" (.imm 0),  -- l.2228 `btq $0, %r12`
    .adcx "%r9" (.reg "%r11"),  -- l.2229 `adcxq %r11, %r9`
    .setc "%r13",  -- l.2230 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%r10"),  -- l.2232 `movq %r10, %rbp`
    .bt "%r13" (.imm 0),  -- l.2233 `btq $0, %r13`
    .adcx "%rbp" (.reg "%rbx"),  -- l.2234 `adcxq %rbx, %rbp`
    .mov "%rbx" (.imm 0) ]  -- l.2235 `movq $0, %rbx`

/-- Segment 64 of the body: the 32 instructions from source lines 2236–2273. -/
def ed25519PointAddShippedSeg064 : List (JInstr 64) :=
  [ .mov "%r10" (.imm 0),  -- l.2236 `movl $0, %r10d`
    .loadMem "%r11" "%rsp" 200,  -- l.2237 `movq 200(%rsp), %r11`
    .bt "%r10" (.imm 0),  -- l.2238 `btq $0, %r10`
    .adcx "%r11" (.reg "%rsi"),  -- l.2239 `adcxq %rsi, %r11`
    .setc "%r12",  -- l.2240 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rsi" "%rsp" 160,  -- l.2242 `movq 160(%rsp), %rsi`
    .bt "%r12" (.imm 0),  -- l.2243 `btq $0, %r12`
    .adcx "%rsi" (.reg "%rcx"),  -- l.2244 `adcxq %rcx, %rsi`
    .setc "%r10",  -- l.2245 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rcx" "%rsp" 272,  -- l.2247 `movq 272(%rsp), %rcx`
    .bt "%r10" (.imm 0),  -- l.2248 `btq $0, %r10`
    .adcx "%rcx" (.reg "%rdi"),  -- l.2249 `adcxq %rdi, %rcx`
    .setc "%r12",  -- l.2250 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%r8"),  -- l.2252 `movq %r8, %rdi`
    .bt "%r12" (.imm 0),  -- l.2253 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.2254 `adcxq %r9, %rdi`
    .setc "%r10",  -- l.2255 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r8" (.reg "%rbx"),  -- l.2257 `movq %rbx, %r8`
    .bt "%r10" (.imm 0),  -- l.2258 `btq $0, %r10`
    .adcx "%r8" (.reg "%rbp"),  -- l.2259 `adcxq %rbp, %r8`
    .setc "%r9",  -- l.2260 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbp" (.imm 0),  -- l.2262 `movq $0, %rbp`
    .mov "%r9" (.imm 0),  -- l.2263 `movl $0, %r9d`
    .mov "%r10" (.reg "%r8"),  -- l.2264 `movq %r8, %r10`
    .imul "%r10" (.reg "%rax"),  -- l.2265 `imulq %rax, %r10`
    .mov "%rdx" (.reg "%r8"),  -- l.2266 `movq %r8, %rdx`
    .mulx "%r12" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.2267 `mulx %rax, %r10, %r12`
    .mov "%r8" (.reg "%r10"),  -- l.2268 `movq %r10, %r8`
    .bt "%r9" (.imm 0),  -- l.2269 `btq $0, %r9`
    .adcx "%r8" (.reg "%rbp"),  -- l.2270 `adcxq %rbp, %r8`
    .setc "%r13",  -- l.2271 `setc %r13b; movzbq %r13b, %r13`
    .mov "%r9" (.reg "%r12") ]  -- l.2273 `movq %r12, %r9`

/-- Segment 65 of the body: the 32 instructions from source lines 2274–2311. -/
def ed25519PointAddShippedSeg065 : List (JInstr 64) :=
  [ .bt "%r13" (.imm 0),  -- l.2274 `btq $0, %r13`
    .adcx "%r9" (.reg "%rbp"),  -- l.2275 `adcxq %rbp, %r9`
    .mov "%rbp" (.imm 0),  -- l.2276 `movl $0, %ebp`
    .mov "%r10" (.reg "%r11"),  -- l.2277 `movq %r11, %r10`
    .bt "%rbp" (.imm 0),  -- l.2278 `btq $0, %rbp`
    .adcx "%r10" (.reg "%r8"),  -- l.2279 `adcxq %r8, %r10`
    .setc "%r12",  -- l.2280 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rsi"),  -- l.2282 `movq %rsi, %rbp`
    .bt "%r12" (.imm 0),  -- l.2283 `btq $0, %r12`
    .adcx "%rbp" (.reg "%r9"),  -- l.2284 `adcxq %r9, %rbp`
    .setc "%r8",  -- l.2285 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rsi" (.reg "%rcx"),  -- l.2287 `movq %rcx, %rsi`
    .bt "%r8" (.imm 0),  -- l.2288 `btq $0, %r8`
    .adcx "%rsi" (.reg "%rbx"),  -- l.2289 `adcxq %rbx, %rsi`
    .setc "%r9",  -- l.2290 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi"),  -- l.2292 `movq %rdi, %rcx`
    .bt "%r9" (.imm 0),  -- l.2293 `btq $0, %r9`
    .adcx "%rcx" (.reg "%rbx"),  -- l.2294 `adcxq %rbx, %rcx`
    .setc "%r8",  -- l.2295 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rdi" (.reg "%rbx"),  -- l.2297 `movq %rbx, %rdi`
    .test "%r8" (.reg "%r8"),  -- l.2298 `testq %r8, %r8`
    .cmovne "%rdi" (.reg "%rax"),  -- l.2299 `cmovneq %rax, %rdi`
    .mov "%rax" (.imm 0),  -- l.2300 `movl $0, %eax`
    .mov "%r8" (.reg "%r10"),  -- l.2301 `movq %r10, %r8`
    .bt "%rax" (.imm 0),  -- l.2302 `btq $0, %rax`
    .adcx "%r8" (.reg "%rdi"),  -- l.2303 `adcxq %rdi, %r8`
    .setc "%r9",  -- l.2304 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rbp"),  -- l.2306 `movq %rbp, %rax`
    .bt "%r9" (.imm 0),  -- l.2307 `btq $0, %r9`
    .adcx "%rax" (.reg "%rbx"),  -- l.2308 `adcxq %rbx, %rax`
    .setc "%rdi",  -- l.2309 `setc %dil; movzbq %dil, %rdi`
    .mov "%rbp" (.reg "%rsi") ]  -- l.2311 `movq %rsi, %rbp`

/-- Segment 66 of the body: the 32 instructions from source lines 2312–2349. -/
def ed25519PointAddShippedSeg066 : List (JInstr 64) :=
  [ .bt "%rdi" (.imm 0),  -- l.2312 `btq $0, %rdi`
    .adcx "%rbp" (.reg "%rbx"),  -- l.2313 `adcxq %rbx, %rbp`
    .setc "%r9",  -- l.2314 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rsi" (.reg "%rcx"),  -- l.2316 `movq %rcx, %rsi`
    .bt "%r9" (.imm 0),  -- l.2317 `btq $0, %r9`
    .adcx "%rsi" (.reg "%rbx"),  -- l.2318 `adcxq %rbx, %rsi`
    .setc "%rdi",  -- l.2319 `setc %dil; movzbq %dil, %rdi`
    .mov "%rbx" (.imm 19),  -- l.2321 `movq $19, %rbx`
    .mov "%rcx" (.imm 0),  -- l.2322 `movq $0, %rcx`
    .mov "%rdi" (.imm 0),  -- l.2323 `movq $0, %rdi`
    .mov "%r9" (.imm 9223372036854775808),  -- l.2324 `movq $9223372036854775808, %r9`
    .mov "%r10" (.imm 0),  -- l.2325 `movl $0, %r10d`
    .mov "%r11" (.reg "%r8"),  -- l.2326 `movq %r8, %r11`
    .bt "%r10" (.imm 0),  -- l.2327 `btq $0, %r10`
    .adcx "%r11" (.reg "%rbx"),  -- l.2328 `adcxq %rbx, %r11`
    .setc "%r12",  -- l.2329 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbx" (.reg "%rax"),  -- l.2331 `movq %rax, %rbx`
    .bt "%r12" (.imm 0),  -- l.2332 `btq $0, %r12`
    .adcx "%rbx" (.reg "%rcx"),  -- l.2333 `adcxq %rcx, %rbx`
    .setc "%r10",  -- l.2334 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rcx" (.reg "%rbp"),  -- l.2336 `movq %rbp, %rcx`
    .bt "%r10" (.imm 0),  -- l.2337 `btq $0, %r10`
    .adcx "%rcx" (.reg "%rdi"),  -- l.2338 `adcxq %rdi, %rcx`
    .setc "%r12",  -- l.2339 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rsi"),  -- l.2341 `movq %rsi, %rdi`
    .bt "%r12" (.imm 0),  -- l.2342 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.2343 `adcxq %r9, %rdi`
    .setc "%r10",  -- l.2344 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%r8"),  -- l.2346 `movq %r8, %r9`
    .test "%r10" (.reg "%r10"),  -- l.2347 `testq %r10, %r10`
    .cmovne "%r9" (.reg "%r11"),  -- l.2348 `cmovneq %r11, %r9`
    .mov "%r8" (.reg "%rax") ]  -- l.2349 `movq %rax, %r8`

/-- Segment 67 of the body: the 32 instructions from source lines 2350–2385. -/
def ed25519PointAddShippedSeg067 : List (JInstr 64) :=
  [ .test "%r10" (.reg "%r10"),  -- l.2350 `testq %r10, %r10`
    .cmovne "%r8" (.reg "%rbx"),  -- l.2351 `cmovneq %rbx, %r8`
    .mov "%rax" (.reg "%rbp"),  -- l.2352 `movq %rbp, %rax`
    .test "%r10" (.reg "%r10"),  -- l.2353 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rcx"),  -- l.2354 `cmovneq %rcx, %rax`
    .mov "%rbx" (.reg "%rsi"),  -- l.2355 `movq %rsi, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.2356 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rdi"),  -- l.2357 `cmovneq %rdi, %rbx`
    .mov "%rcx" (.imm 19),  -- l.2358 `movq $19, %rcx`
    .mov "%rsi" (.imm 0),  -- l.2359 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.2360 `movq $0, %rdi`
    .mov "%rbp" (.imm 9223372036854775808),  -- l.2361 `movq $9223372036854775808, %rbp`
    .mov "%r10" (.imm 0),  -- l.2362 `movl $0, %r10d`
    .mov "%r11" (.reg "%r9"),  -- l.2363 `movq %r9, %r11`
    .bt "%r10" (.imm 0),  -- l.2364 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.2365 `adcxq %rcx, %r11`
    .setc "%r12",  -- l.2366 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rcx" (.reg "%r8"),  -- l.2368 `movq %r8, %rcx`
    .bt "%r12" (.imm 0),  -- l.2369 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rsi"),  -- l.2370 `adcxq %rsi, %rcx`
    .setc "%r10",  -- l.2371 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rax"),  -- l.2373 `movq %rax, %rsi`
    .bt "%r10" (.imm 0),  -- l.2374 `btq $0, %r10`
    .adcx "%rsi" (.reg "%rdi"),  -- l.2375 `adcxq %rdi, %rsi`
    .setc "%r12",  -- l.2376 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rbx"),  -- l.2378 `movq %rbx, %rdi`
    .bt "%r12" (.imm 0),  -- l.2379 `btq $0, %r12`
    .adcx "%rdi" (.reg "%rbp"),  -- l.2380 `adcxq %rbp, %rdi`
    .setc "%r10",  -- l.2381 `setc %r10b; movzbq %r10b, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2383 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r9"),  -- l.2384 `movq %r9, %rax`
    .test "%r10" (.reg "%r10") ]  -- l.2385 `testq %r10, %r10`

/-- Segment 68 of the body: the 32 instructions from source lines 2386–2419. -/
def ed25519PointAddShippedSeg068 : List (JInstr 64) :=
  [ .cmovne "%rax" (.reg "%r11"),  -- l.2386 `cmovneq %r11, %rax`
    .storeMem "%rsp" 272 (.reg "%rax"),  -- l.2387 `movq %rax, 272(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2388 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2389 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.2390 `movq %r8, %rax`
    .test "%r10" (.reg "%r10"),  -- l.2391 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rcx"),  -- l.2392 `cmovneq %rcx, %rax`
    .storeMem "%rsp" 280 (.reg "%rax"),  -- l.2393 `movq %rax, 280(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2394 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.2395 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rax"),  -- l.2396 `movq %rax, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.2397 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rsi"),  -- l.2398 `cmovneq %rsi, %rbx`
    .storeMem "%rsp" 288 (.reg "%rbx"),  -- l.2399 `movq %rbx, 288(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.2400 `movq -128(%rsp), %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2401 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.2402 `movq %rbx, %rax`
    .test "%r10" (.reg "%r10"),  -- l.2403 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rdi"),  -- l.2404 `cmovneq %rdi, %rax`
    .storeMem "%rsp" 296 (.reg "%rax"),  -- l.2405 `movq %rax, 296(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2406 `movq -128(%rsp), %rax`
    .mov "%rbx" (.imm 0),  -- l.2407 `movl $0, %ebx`
    .loadMem "%rsi" "%rsp" 232,  -- l.2408 `movq 232(%rsp), %rsi`
    .bt "%rbx" (.imm 0),  -- l.2409 `btq $0, %rbx`
    .adcxMem "%rsi" "%rsp" 232,  -- l.2410 `adcxq 232(%rsp), %rsi`
    .setc "%rdi",  -- l.2411 `setc %dil; movzbq %dil, %rdi`
    .loadMem "%rbx" "%rsp" 240,  -- l.2413 `movq 240(%rsp), %rbx`
    .bt "%rdi" (.imm 0),  -- l.2414 `btq $0, %rdi`
    .adcxMem "%rbx" "%rsp" 240,  -- l.2415 `adcxq 240(%rsp), %rbx`
    .setc "%r8",  -- l.2416 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rdi" "%rsp" 248,  -- l.2418 `movq 248(%rsp), %rdi`
    .bt "%r8" (.imm 0) ]  -- l.2419 `btq $0, %r8`

/-- Segment 69 of the body: the 32 instructions from source lines 2420–2457. -/
def ed25519PointAddShippedSeg069 : List (JInstr 64) :=
  [ .adcxMem "%rdi" "%rsp" 248,  -- l.2420 `adcxq 248(%rsp), %rdi`
    .setc "%r10",  -- l.2421 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%r8" "%rsp" 256,  -- l.2423 `movq 256(%rsp), %r8`
    .bt "%r10" (.imm 0),  -- l.2424 `btq $0, %r10`
    .adcxMem "%r8" "%rsp" 256,  -- l.2425 `adcxq 256(%rsp), %r8`
    .setc "%r11",  -- l.2426 `setc %r11b; movzbq %r11b, %r11`
    .mov "%r10" (.imm 19),  -- l.2428 `movq $19, %r10`
    .mov "%r11" (.imm 0),  -- l.2429 `movq $0, %r11`
    .mov "%r12" (.imm 0),  -- l.2430 `movq $0, %r12`
    .mov "%r13" (.imm 9223372036854775808),  -- l.2431 `movq $9223372036854775808, %r13`
    .mov "%rax" (.imm 0),  -- l.2432 `movl $0, %eax`
    .mov "%rcx" (.reg "%rsi"),  -- l.2433 `movq %rsi, %rcx`
    .bt "%rax" (.imm 0),  -- l.2434 `btq $0, %rax`
    .adcx "%rcx" (.reg "%r10"),  -- l.2435 `adcxq %r10, %rcx`
    .setc "%r9",  -- l.2436 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rbx"),  -- l.2438 `movq %rbx, %rax`
    .bt "%r9" (.imm 0),  -- l.2439 `btq $0, %r9`
    .adcx "%rax" (.reg "%r11"),  -- l.2440 `adcxq %r11, %rax`
    .setc "%r10",  -- l.2441 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%rdi"),  -- l.2443 `movq %rdi, %r9`
    .bt "%r10" (.imm 0),  -- l.2444 `btq $0, %r10`
    .adcx "%r9" (.reg "%r12"),  -- l.2445 `adcxq %r12, %r9`
    .setc "%r11",  -- l.2446 `setc %r11b; movzbq %r11b, %r11`
    .mov "%r10" (.reg "%r8"),  -- l.2448 `movq %r8, %r10`
    .bt "%r11" (.imm 0),  -- l.2449 `btq $0, %r11`
    .adcx "%r10" (.reg "%r13"),  -- l.2450 `adcxq %r13, %r10`
    .setc "%r12",  -- l.2451 `setc %r12b; movzbq %r12b, %r12`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2453 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rsi"),  -- l.2454 `movq %rsi, %rax`
    .test "%r12" (.reg "%r12"),  -- l.2455 `testq %r12, %r12`
    .cmovne "%rax" (.reg "%rcx"),  -- l.2456 `cmovneq %rcx, %rax`
    .storeMem "%rsp" 200 (.reg "%rax") ]  -- l.2457 `movq %rax, 200(%rsp)`

/-- Segment 70 of the body: the 32 instructions from source lines 2458–2489. -/
def ed25519PointAddShippedSeg070 : List (JInstr 64) :=
  [ .loadMem "%rax" "%rsp" (-128),  -- l.2458 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.2459 `movq %rcx, -128(%rsp)`
    .mov "%rcx" (.reg "%rbx"),  -- l.2460 `movq %rbx, %rcx`
    .test "%r12" (.reg "%r12"),  -- l.2461 `testq %r12, %r12`
    .cmovne "%rcx" (.reg "%rax"),  -- l.2462 `cmovneq %rax, %rcx`
    .storeMem "%rsp" 232 (.reg "%rcx"),  -- l.2463 `movq %rcx, 232(%rsp)`
    .loadMem "%rcx" "%rsp" (-128),  -- l.2464 `movq -128(%rsp), %rcx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2465 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.2466 `movq %rdi, %rax`
    .test "%r12" (.reg "%r12"),  -- l.2467 `testq %r12, %r12`
    .cmovne "%rax" (.reg "%r9"),  -- l.2468 `cmovneq %r9, %rax`
    .storeMem "%rsp" 240 (.reg "%rax"),  -- l.2469 `movq %rax, 240(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2470 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2471 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.2472 `movq %r8, %rax`
    .test "%r12" (.reg "%r12"),  -- l.2473 `testq %r12, %r12`
    .cmovne "%rax" (.reg "%r10"),  -- l.2474 `cmovneq %r10, %rax`
    .storeMem "%rsp" 248 (.reg "%rax"),  -- l.2475 `movq %rax, 248(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2476 `movq -128(%rsp), %rax`
    .mov "%rsi" (.imm 0),  -- l.2477 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.2478 `movl $0, %edi`
    .loadMem "%r8" "%rsp" 200,  -- l.2479 `movq 200(%rsp), %r8`
    .loadMem "%r15" "%rsp" 304,  -- l.2480 `movq 304(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.2481 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 200,  -- l.2482 `movq 200(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 304,  -- l.2483 `movq 304(%rsp), %r14`
    .mulx "%r9" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.2484 `mulx %r14, %r8, %r9`
    .bt "%rdi" (.imm 0),  -- l.2485 `btq $0, %rdi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2486 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.2487 `movq %r8, %rax`
    .adcx "%rax" (.reg "%rsi"),  -- l.2488 `adcxq %rsi, %rax`
    .storeMem "%rsp" 256 (.reg "%rax") ]  -- l.2489 `movq %rax, 256(%rsp)`

/-- Segment 71 of the body: the 32 instructions from source lines 2490–2524. -/
def ed25519PointAddShippedSeg071 : List (JInstr 64) :=
  [ .loadMem "%rax" "%rsp" (-128),  -- l.2490 `movq -128(%rsp), %rax`
    .setc "%r12",  -- l.2491 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rdi" "%rsp" 232,  -- l.2493 `movq 232(%rsp), %rdi`
    .loadMem "%r15" "%rsp" 304,  -- l.2494 `movq 304(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.2495 `imulq %r15, %rdi`
    .loadMem "%rdx" "%rsp" 232,  -- l.2496 `movq 232(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 304,  -- l.2497 `movq 304(%rsp), %r14`
    .mulx "%r8" "%rdi" (.reg "%rdx") (.reg "%r14"),  -- l.2498 `mulx %r14, %rdi, %r8`
    .mov "%r13" (.reg "%rdi"),  -- l.2499 `movq %rdi, %r13`
    .bt "%r12" (.imm 0),  -- l.2500 `btq $0, %r12`
    .adcx "%r13" (.reg "%r9"),  -- l.2501 `adcxq %r9, %r13`
    .setc "%rbp",  -- l.2502 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rdi" "%rsp" 240,  -- l.2504 `movq 240(%rsp), %rdi`
    .loadMem "%r15" "%rsp" 304,  -- l.2505 `movq 304(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.2506 `imulq %r15, %rdi`
    .loadMem "%rdx" "%rsp" 240,  -- l.2507 `movq 240(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 304,  -- l.2508 `movq 304(%rsp), %r14`
    .mulx "%r9" "%rdi" (.reg "%rdx") (.reg "%r14"),  -- l.2509 `mulx %r14, %rdi, %r9`
    .mov "%r12" (.reg "%rdi"),  -- l.2510 `movq %rdi, %r12`
    .bt "%rbp" (.imm 0),  -- l.2511 `btq $0, %rbp`
    .adcx "%r12" (.reg "%r8"),  -- l.2512 `adcxq %r8, %r12`
    .setc "%r10",  -- l.2513 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rdi" "%rsp" 248,  -- l.2515 `movq 248(%rsp), %rdi`
    .loadMem "%r15" "%rsp" 304,  -- l.2516 `movq 304(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.2517 `imulq %r15, %rdi`
    .loadMem "%rdx" "%rsp" 248,  -- l.2518 `movq 248(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 304,  -- l.2519 `movq 304(%rsp), %r14`
    .mulx "%rbp" "%rdi" (.reg "%rdx") (.reg "%r14"),  -- l.2520 `mulx %r14, %rdi, %rbp`
    .bt "%r10" (.imm 0),  -- l.2521 `btq $0, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2522 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.2523 `movq %rdi, %rax`
    .adcx "%rax" (.reg "%r9") ]  -- l.2524 `adcxq %r9, %rax`

/-- Segment 72 of the body: the 32 instructions from source lines 2525–2559. -/
def ed25519PointAddShippedSeg072 : List (JInstr 64) :=
  [ .storeMem "%rsp" 304 (.reg "%rax"),  -- l.2525 `movq %rax, 304(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2526 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.2527 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rdi" (.reg "%rbp"),  -- l.2529 `movq %rbp, %rdi`
    .bt "%r8" (.imm 0),  -- l.2530 `btq $0, %r8`
    .adcx "%rdi" (.reg "%rsi"),  -- l.2531 `adcxq %rsi, %rdi`
    .mov "%rsi" (.imm 0),  -- l.2532 `movq $0, %rsi`
    .mov "%rbp" (.imm 0),  -- l.2533 `movl $0, %ebp`
    .loadMem "%r8" "%rsp" 200,  -- l.2534 `movq 200(%rsp), %r8`
    .loadMem "%r15" "%rsp" 312,  -- l.2535 `movq 312(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.2536 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 200,  -- l.2537 `movq 200(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 312,  -- l.2538 `movq 312(%rsp), %r14`
    .mulx "%r9" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.2539 `mulx %r14, %r8, %r9`
    .mov "%r10" (.reg "%r8"),  -- l.2540 `movq %r8, %r10`
    .bt "%rbp" (.imm 0),  -- l.2541 `btq $0, %rbp`
    .adcx "%r10" (.reg "%rsi"),  -- l.2542 `adcxq %rsi, %r10`
    .setc "%rbx",  -- l.2543 `setc %bl; movzbq %bl, %rbx`
    .loadMem "%rbp" "%rsp" 232,  -- l.2545 `movq 232(%rsp), %rbp`
    .loadMem "%r15" "%rsp" 312,  -- l.2546 `movq 312(%rsp), %r15`
    .imul "%rbp" (.reg "%r15"),  -- l.2547 `imulq %r15, %rbp`
    .loadMem "%rdx" "%rsp" 232,  -- l.2548 `movq 232(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 312,  -- l.2549 `movq 312(%rsp), %r14`
    .mulx "%r8" "%rbp" (.reg "%rdx") (.reg "%r14"),  -- l.2550 `mulx %r14, %rbp, %r8`
    .mov "%rax" (.reg "%rbp"),  -- l.2551 `movq %rbp, %rax`
    .bt "%rbx" (.imm 0),  -- l.2552 `btq $0, %rbx`
    .adcx "%rax" (.reg "%r9"),  -- l.2553 `adcxq %r9, %rax`
    .setc "%rcx",  -- l.2554 `setc %cl; movzbq %cl, %rcx`
    .loadMem "%rbx" "%rsp" 240,  -- l.2556 `movq 240(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 312,  -- l.2557 `movq 312(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2558 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 240 ]  -- l.2559 `movq 240(%rsp), %rdx`

/-- Segment 73 of the body: the 32 instructions from source lines 2560–2594. -/
def ed25519PointAddShippedSeg073 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 312,  -- l.2560 `movq 312(%rsp), %r14`
    .mulx "%rbp" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.2561 `mulx %r14, %rbx, %rbp`
    .mov "%r9" (.reg "%rbx"),  -- l.2562 `movq %rbx, %r9`
    .bt "%rcx" (.imm 0),  -- l.2563 `btq $0, %rcx`
    .adcx "%r9" (.reg "%r8"),  -- l.2564 `adcxq %r8, %r9`
    .setc "%r11",  -- l.2565 `setc %r11b; movzbq %r11b, %r11`
    .loadMem "%rbx" "%rsp" 248,  -- l.2567 `movq 248(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 312,  -- l.2568 `movq 312(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.2569 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 248,  -- l.2570 `movq 248(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 312,  -- l.2571 `movq 312(%rsp), %r14`
    .mulx "%rcx" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.2572 `mulx %r14, %rbx, %rcx`
    .bt "%r11" (.imm 0),  -- l.2573 `btq $0, %r11`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2574 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.2575 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%rbp"),  -- l.2576 `adcxq %rbp, %rax`
    .storeMem "%rsp" 312 (.reg "%rax"),  -- l.2577 `movq %rax, 312(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2578 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.2579 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rbx" (.reg "%rcx"),  -- l.2581 `movq %rcx, %rbx`
    .bt "%r8" (.imm 0),  -- l.2582 `btq $0, %r8`
    .adcx "%rbx" (.reg "%rsi"),  -- l.2583 `adcxq %rsi, %rbx`
    .mov "%rcx" (.imm 0),  -- l.2584 `movq $0, %rcx`
    .mov "%rsi" (.imm 0),  -- l.2585 `movl $0, %esi`
    .bt "%rsi" (.imm 0),  -- l.2586 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2587 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r13"),  -- l.2588 `movq %r13, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.2589 `adcxq %r10, %rax`
    .storeMem "%rsp" 192 (.reg "%rax"),  -- l.2590 `movq %rax, 192(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2591 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.2592 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rsi" (.reg "%r12") ]  -- l.2594 `movq %r12, %rsi`

/-- Segment 74 of the body: the 32 instructions from source lines 2595–2631. -/
def ed25519PointAddShippedSeg074 : List (JInstr 64) :=
  [ .bt "%r8" (.imm 0),  -- l.2595 `btq $0, %r8`
    .adcx "%rsi" (.reg "%rax"),  -- l.2596 `adcxq %rax, %rsi`
    .setc "%r10",  -- l.2597 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rax" "%rsp" 304,  -- l.2599 `movq 304(%rsp), %rax`
    .bt "%r10" (.imm 0),  -- l.2600 `btq $0, %r10`
    .adcx "%rax" (.reg "%r9"),  -- l.2601 `adcxq %r9, %rax`
    .setc "%r8",  -- l.2602 `setc %r8b; movzbq %r8b, %r8`
    .mov "%r9" (.reg "%rdi"),  -- l.2604 `movq %rdi, %r9`
    .bt "%r8" (.imm 0),  -- l.2605 `btq $0, %r8`
    .adcxMem "%r9" "%rsp" 312,  -- l.2606 `adcxq 312(%rsp), %r9`
    .setc "%r10",  -- l.2607 `setc %r10b; movzbq %r10b, %r10`
    .bt "%r10" (.imm 0),  -- l.2609 `btq $0, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2610 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.2611 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%rbx"),  -- l.2612 `adcxq %rbx, %rax`
    .storeMem "%rsp" 312 (.reg "%rax"),  -- l.2613 `movq %rax, 312(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2614 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.2615 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rbx" (.imm 0),  -- l.2617 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.2618 `movl $0, %ecx`
    .loadMem "%r8" "%rsp" 200,  -- l.2619 `movq 200(%rsp), %r8`
    .loadMem "%r15" "%rsp" 320,  -- l.2620 `movq 320(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.2621 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 200,  -- l.2622 `movq 200(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 320,  -- l.2623 `movq 320(%rsp), %r14`
    .mulx "%r10" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.2624 `mulx %r14, %r8, %r10`
    .mov "%r11" (.reg "%r8"),  -- l.2625 `movq %r8, %r11`
    .bt "%rcx" (.imm 0),  -- l.2626 `btq $0, %rcx`
    .adcx "%r11" (.reg "%rbx"),  -- l.2627 `adcxq %rbx, %r11`
    .setc "%r12",  -- l.2628 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rcx" "%rsp" 232,  -- l.2630 `movq 232(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 320 ]  -- l.2631 `movq 320(%rsp), %r15`

/-- Segment 75 of the body: the 32 instructions from source lines 2632–2666. -/
def ed25519PointAddShippedSeg075 : List (JInstr 64) :=
  [ .imul "%rcx" (.reg "%r15"),  -- l.2632 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 232,  -- l.2633 `movq 232(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 320,  -- l.2634 `movq 320(%rsp), %r14`
    .mulx "%r8" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2635 `mulx %r14, %rcx, %r8`
    .mov "%r13" (.reg "%rcx"),  -- l.2636 `movq %rcx, %r13`
    .bt "%r12" (.imm 0),  -- l.2637 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.2638 `adcxq %r10, %r13`
    .setc "%rbp",  -- l.2639 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rcx" "%rsp" 240,  -- l.2641 `movq 240(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 320,  -- l.2642 `movq 320(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2643 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 240,  -- l.2644 `movq 240(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 320,  -- l.2645 `movq 320(%rsp), %r14`
    .mulx "%r10" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2646 `mulx %r14, %rcx, %r10`
    .mov "%r12" (.reg "%rcx"),  -- l.2647 `movq %rcx, %r12`
    .bt "%rbp" (.imm 0),  -- l.2648 `btq $0, %rbp`
    .adcx "%r12" (.reg "%r8"),  -- l.2649 `adcxq %r8, %r12`
    .setc "%rdi",  -- l.2650 `setc %dil; movzbq %dil, %rdi`
    .loadMem "%rcx" "%rsp" 248,  -- l.2652 `movq 248(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 320,  -- l.2653 `movq 320(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2654 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 248,  -- l.2655 `movq 248(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 320,  -- l.2656 `movq 320(%rsp), %r14`
    .mulx "%rbp" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2657 `mulx %r14, %rcx, %rbp`
    .bt "%rdi" (.imm 0),  -- l.2658 `btq $0, %rdi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2659 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.2660 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.2661 `adcxq %r10, %rax`
    .storeMem "%rsp" 320 (.reg "%rax"),  -- l.2662 `movq %rax, 320(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2663 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.2664 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rcx" (.reg "%rbp") ]  -- l.2666 `movq %rbp, %rcx`

/-- Segment 76 of the body: the 32 instructions from source lines 2667–2703. -/
def ed25519PointAddShippedSeg076 : List (JInstr 64) :=
  [ .bt "%r8" (.imm 0),  -- l.2667 `btq $0, %r8`
    .adcx "%rcx" (.reg "%rbx"),  -- l.2668 `adcxq %rbx, %rcx`
    .mov "%rbx" (.imm 0),  -- l.2669 `movq $0, %rbx`
    .mov "%rdi" (.imm 0),  -- l.2670 `movl $0, %edi`
    .bt "%rdi" (.imm 0),  -- l.2671 `btq $0, %rdi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2672 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rsi"),  -- l.2673 `movq %rsi, %rax`
    .adcx "%rax" (.reg "%r11"),  -- l.2674 `adcxq %r11, %rax`
    .storeMem "%rsp" 304 (.reg "%rax"),  -- l.2675 `movq %rax, 304(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2676 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.2677 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rsi" (.reg "%rax"),  -- l.2679 `movq %rax, %rsi`
    .bt "%r8" (.imm 0),  -- l.2680 `btq $0, %r8`
    .adcx "%rsi" (.reg "%r13"),  -- l.2681 `adcxq %r13, %rsi`
    .setc "%rdi",  -- l.2682 `setc %dil; movzbq %dil, %rdi`
    .mov "%rax" (.reg "%r9"),  -- l.2684 `movq %r9, %rax`
    .bt "%rdi" (.imm 0),  -- l.2685 `btq $0, %rdi`
    .adcx "%rax" (.reg "%r12"),  -- l.2686 `adcxq %r12, %rax`
    .setc "%r8",  -- l.2687 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rdi" "%rsp" 312,  -- l.2689 `movq 312(%rsp), %rdi`
    .bt "%r8" (.imm 0),  -- l.2690 `btq $0, %r8`
    .adcxMem "%rdi" "%rsp" 320,  -- l.2691 `adcxq 320(%rsp), %rdi`
    .setc "%r9",  -- l.2692 `setc %r9b; movzbq %r9b, %r9`
    .bt "%r9" (.imm 0),  -- l.2694 `btq $0, %r9`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2695 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.2696 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%rcx"),  -- l.2697 `adcxq %rcx, %rax`
    .storeMem "%rsp" 320 (.reg "%rax"),  -- l.2698 `movq %rax, 320(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2699 `movq -128(%rsp), %rax`
    .setc "%r10",  -- l.2700 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbx" (.imm 0),  -- l.2702 `movq $0, %rbx`
    .mov "%rcx" (.imm 0) ]  -- l.2703 `movl $0, %ecx`

/-- Segment 77 of the body: the 32 instructions from source lines 2704–2738. -/
def ed25519PointAddShippedSeg077 : List (JInstr 64) :=
  [ .loadMem "%r9" "%rsp" 200,  -- l.2704 `movq 200(%rsp), %r9`
    .loadMem "%r15" "%rsp" 328,  -- l.2705 `movq 328(%rsp), %r15`
    .imul "%r9" (.reg "%r15"),  -- l.2706 `imulq %r15, %r9`
    .loadMem "%rdx" "%rsp" 200,  -- l.2707 `movq 200(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 328,  -- l.2708 `movq 328(%rsp), %r14`
    .mulx "%r10" "%r9" (.reg "%rdx") (.reg "%r14"),  -- l.2709 `mulx %r14, %r9, %r10`
    .mov "%r11" (.reg "%r9"),  -- l.2710 `movq %r9, %r11`
    .bt "%rcx" (.imm 0),  -- l.2711 `btq $0, %rcx`
    .adcx "%r11" (.reg "%rbx"),  -- l.2712 `adcxq %rbx, %r11`
    .setc "%r12",  -- l.2713 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rcx" "%rsp" 232,  -- l.2715 `movq 232(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 328,  -- l.2716 `movq 328(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2717 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 232,  -- l.2718 `movq 232(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 328,  -- l.2719 `movq 328(%rsp), %r14`
    .mulx "%r9" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2720 `mulx %r14, %rcx, %r9`
    .mov "%r13" (.reg "%rcx"),  -- l.2721 `movq %rcx, %r13`
    .bt "%r12" (.imm 0),  -- l.2722 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.2723 `adcxq %r10, %r13`
    .setc "%rbp",  -- l.2724 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rcx" "%rsp" 240,  -- l.2726 `movq 240(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 328,  -- l.2727 `movq 328(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.2728 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 240,  -- l.2729 `movq 240(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 328,  -- l.2730 `movq 328(%rsp), %r14`
    .mulx "%r10" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2731 `mulx %r14, %rcx, %r10`
    .mov "%r12" (.reg "%rcx"),  -- l.2732 `movq %rcx, %r12`
    .bt "%rbp" (.imm 0),  -- l.2733 `btq $0, %rbp`
    .adcx "%r12" (.reg "%r9"),  -- l.2734 `adcxq %r9, %r12`
    .setc "%r8",  -- l.2735 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rcx" "%rsp" 248,  -- l.2737 `movq 248(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 328 ]  -- l.2738 `movq 328(%rsp), %r15`

/-- Segment 78 of the body: the 32 instructions from source lines 2739–2774. -/
def ed25519PointAddShippedSeg078 : List (JInstr 64) :=
  [ .imul "%rcx" (.reg "%r15"),  -- l.2739 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 248,  -- l.2740 `movq 248(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 328,  -- l.2741 `movq 328(%rsp), %r14`
    .mulx "%rbp" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.2742 `mulx %r14, %rcx, %rbp`
    .bt "%r8" (.imm 0),  -- l.2743 `btq $0, %r8`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2744 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.2745 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.2746 `adcxq %r10, %rax`
    .storeMem "%rsp" 328 (.reg "%rax"),  -- l.2747 `movq %rax, 328(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2748 `movq -128(%rsp), %rax`
    .setc "%r9",  -- l.2749 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rbp"),  -- l.2751 `movq %rbp, %rcx`
    .bt "%r9" (.imm 0),  -- l.2752 `btq $0, %r9`
    .adcx "%rcx" (.reg "%rbx"),  -- l.2753 `adcxq %rbx, %rcx`
    .mov "%rbx" (.imm 0),  -- l.2754 `movq $0, %rbx`
    .mov "%rbp" (.imm 0),  -- l.2755 `movl $0, %ebp`
    .mov "%r8" (.reg "%rsi"),  -- l.2756 `movq %rsi, %r8`
    .bt "%rbp" (.imm 0),  -- l.2757 `btq $0, %rbp`
    .adcx "%r8" (.reg "%r11"),  -- l.2758 `adcxq %r11, %r8`
    .setc "%r9",  -- l.2759 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rsi" (.reg "%rax"),  -- l.2761 `movq %rax, %rsi`
    .bt "%r9" (.imm 0),  -- l.2762 `btq $0, %r9`
    .adcx "%rsi" (.reg "%r13"),  -- l.2763 `adcxq %r13, %rsi`
    .setc "%rbp",  -- l.2764 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%rax" (.reg "%rdi"),  -- l.2766 `movq %rdi, %rax`
    .bt "%rbp" (.imm 0),  -- l.2767 `btq $0, %rbp`
    .adcx "%rax" (.reg "%r12"),  -- l.2768 `adcxq %r12, %rax`
    .setc "%r9",  -- l.2769 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rdi" "%rsp" 320,  -- l.2771 `movq 320(%rsp), %rdi`
    .bt "%r9" (.imm 0),  -- l.2772 `btq $0, %r9`
    .adcxMem "%rdi" "%rsp" 328,  -- l.2773 `adcxq 328(%rsp), %rdi`
    .setc "%rbp" ]  -- l.2774 `setc %bpl; movzbq %bpl, %rbp`

/-- Segment 79 of the body: the 32 instructions from source lines 2776–2811. -/
def ed25519PointAddShippedSeg079 : List (JInstr 64) :=
  [ .mov "%r9" (.reg "%rbx"),  -- l.2776 `movq %rbx, %r9`
    .bt "%rbp" (.imm 0),  -- l.2777 `btq $0, %rbp`
    .adcx "%r9" (.reg "%rcx"),  -- l.2778 `adcxq %rcx, %r9`
    .setc "%r10",  -- l.2779 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbx" (.imm 38),  -- l.2781 `movq $38, %rbx`
    .mov "%rcx" (.imm 0),  -- l.2782 `movq $0, %rcx`
    .mov "%rbp" (.imm 0),  -- l.2783 `movl $0, %ebp`
    .mov "%r10" (.reg "%rsi"),  -- l.2784 `movq %rsi, %r10`
    .imul "%r10" (.reg "%rbx"),  -- l.2785 `imulq %rbx, %r10`
    .mov "%rdx" (.reg "%rsi"),  -- l.2786 `movq %rsi, %rdx`
    .mulx "%r11" "%r10" (.reg "%rdx") (.reg "%rbx"),  -- l.2787 `mulx %rbx, %r10, %r11`
    .mov "%rsi" (.reg "%r10"),  -- l.2788 `movq %r10, %rsi`
    .bt "%rbp" (.imm 0),  -- l.2789 `btq $0, %rbp`
    .adcx "%rsi" (.reg "%rcx"),  -- l.2790 `adcxq %rcx, %rsi`
    .setc "%r12",  -- l.2791 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rax"),  -- l.2793 `movq %rax, %rbp`
    .imul "%rbp" (.reg "%rbx"),  -- l.2794 `imulq %rbx, %rbp`
    .mov "%rdx" (.reg "%rax"),  -- l.2795 `movq %rax, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rbx"),  -- l.2796 `mulx %rbx, %rbp, %r10`
    .mov "%rax" (.reg "%rbp"),  -- l.2797 `movq %rbp, %rax`
    .bt "%r12" (.imm 0),  -- l.2798 `btq $0, %r12`
    .adcx "%rax" (.reg "%r11"),  -- l.2799 `adcxq %r11, %rax`
    .setc "%r13",  -- l.2800 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%rdi"),  -- l.2802 `movq %rdi, %rbp`
    .imul "%rbp" (.reg "%rbx"),  -- l.2803 `imulq %rbx, %rbp`
    .mov "%rdx" (.reg "%rdi"),  -- l.2804 `movq %rdi, %rdx`
    .mulx "%r11" "%rbp" (.reg "%rdx") (.reg "%rbx"),  -- l.2805 `mulx %rbx, %rbp, %r11`
    .mov "%rdi" (.reg "%rbp"),  -- l.2806 `movq %rbp, %rdi`
    .bt "%r13" (.imm 0),  -- l.2807 `btq $0, %r13`
    .adcx "%rdi" (.reg "%r10"),  -- l.2808 `adcxq %r10, %rdi`
    .setc "%r12",  -- l.2809 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%r9") ]  -- l.2811 `movq %r9, %rbp`

/-- Segment 80 of the body: the 32 instructions from source lines 2812–2848. -/
def ed25519PointAddShippedSeg080 : List (JInstr 64) :=
  [ .imul "%rbp" (.reg "%rbx"),  -- l.2812 `imulq %rbx, %rbp`
    .mov "%rdx" (.reg "%r9"),  -- l.2813 `movq %r9, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rbx"),  -- l.2814 `mulx %rbx, %rbp, %r10`
    .mov "%r9" (.reg "%rbp"),  -- l.2815 `movq %rbp, %r9`
    .bt "%r12" (.imm 0),  -- l.2816 `btq $0, %r12`
    .adcx "%r9" (.reg "%r11"),  -- l.2817 `adcxq %r11, %r9`
    .setc "%r13",  -- l.2818 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%r10"),  -- l.2820 `movq %r10, %rbp`
    .bt "%r13" (.imm 0),  -- l.2821 `btq $0, %r13`
    .adcx "%rbp" (.reg "%rcx"),  -- l.2822 `adcxq %rcx, %rbp`
    .mov "%rcx" (.imm 0),  -- l.2823 `movq $0, %rcx`
    .mov "%r10" (.imm 0),  -- l.2824 `movl $0, %r10d`
    .loadMem "%r11" "%rsp" 256,  -- l.2825 `movq 256(%rsp), %r11`
    .bt "%r10" (.imm 0),  -- l.2826 `btq $0, %r10`
    .adcx "%r11" (.reg "%rsi"),  -- l.2827 `adcxq %rsi, %r11`
    .setc "%r12",  -- l.2828 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rsi" "%rsp" 192,  -- l.2830 `movq 192(%rsp), %rsi`
    .bt "%r12" (.imm 0),  -- l.2831 `btq $0, %r12`
    .adcx "%rsi" (.reg "%rax"),  -- l.2832 `adcxq %rax, %rsi`
    .setc "%r10",  -- l.2833 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rax" "%rsp" 304,  -- l.2835 `movq 304(%rsp), %rax`
    .bt "%r10" (.imm 0),  -- l.2836 `btq $0, %r10`
    .adcx "%rax" (.reg "%rdi"),  -- l.2837 `adcxq %rdi, %rax`
    .setc "%r12",  -- l.2838 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%r8"),  -- l.2840 `movq %r8, %rdi`
    .bt "%r12" (.imm 0),  -- l.2841 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.2842 `adcxq %r9, %rdi`
    .setc "%r10",  -- l.2843 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r8" (.reg "%rcx"),  -- l.2845 `movq %rcx, %r8`
    .bt "%r10" (.imm 0),  -- l.2846 `btq $0, %r10`
    .adcx "%r8" (.reg "%rbp"),  -- l.2847 `adcxq %rbp, %r8`
    .setc "%r9" ]  -- l.2848 `setc %r9b; movzbq %r9b, %r9`

/-- Segment 81 of the body: the 32 instructions from source lines 2850–2886. -/
def ed25519PointAddShippedSeg081 : List (JInstr 64) :=
  [ .mov "%rbp" (.imm 0),  -- l.2850 `movq $0, %rbp`
    .mov "%r9" (.imm 0),  -- l.2851 `movl $0, %r9d`
    .mov "%r10" (.reg "%r8"),  -- l.2852 `movq %r8, %r10`
    .imul "%r10" (.reg "%rbx"),  -- l.2853 `imulq %rbx, %r10`
    .mov "%rdx" (.reg "%r8"),  -- l.2854 `movq %r8, %rdx`
    .mulx "%r12" "%r10" (.reg "%rdx") (.reg "%rbx"),  -- l.2855 `mulx %rbx, %r10, %r12`
    .mov "%r8" (.reg "%r10"),  -- l.2856 `movq %r10, %r8`
    .bt "%r9" (.imm 0),  -- l.2857 `btq $0, %r9`
    .adcx "%r8" (.reg "%rbp"),  -- l.2858 `adcxq %rbp, %r8`
    .setc "%r13",  -- l.2859 `setc %r13b; movzbq %r13b, %r13`
    .mov "%r9" (.reg "%r12"),  -- l.2861 `movq %r12, %r9`
    .bt "%r13" (.imm 0),  -- l.2862 `btq $0, %r13`
    .adcx "%r9" (.reg "%rbp"),  -- l.2863 `adcxq %rbp, %r9`
    .mov "%rbp" (.imm 0),  -- l.2864 `movl $0, %ebp`
    .mov "%r10" (.reg "%r11"),  -- l.2865 `movq %r11, %r10`
    .bt "%rbp" (.imm 0),  -- l.2866 `btq $0, %rbp`
    .adcx "%r10" (.reg "%r8"),  -- l.2867 `adcxq %r8, %r10`
    .setc "%r12",  -- l.2868 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rsi"),  -- l.2870 `movq %rsi, %rbp`
    .bt "%r12" (.imm 0),  -- l.2871 `btq $0, %r12`
    .adcx "%rbp" (.reg "%r9"),  -- l.2872 `adcxq %r9, %rbp`
    .setc "%r8",  -- l.2873 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rsi" (.reg "%rax"),  -- l.2875 `movq %rax, %rsi`
    .bt "%r8" (.imm 0),  -- l.2876 `btq $0, %r8`
    .adcx "%rsi" (.reg "%rcx"),  -- l.2877 `adcxq %rcx, %rsi`
    .setc "%r9",  -- l.2878 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rdi"),  -- l.2880 `movq %rdi, %rax`
    .bt "%r9" (.imm 0),  -- l.2881 `btq $0, %r9`
    .adcx "%rax" (.reg "%rcx"),  -- l.2882 `adcxq %rcx, %rax`
    .setc "%r8",  -- l.2883 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rdi" (.reg "%rcx"),  -- l.2885 `movq %rcx, %rdi`
    .test "%r8" (.reg "%r8") ]  -- l.2886 `testq %r8, %r8`

/-- Segment 82 of the body: the 32 instructions from source lines 2887–2924. -/
def ed25519PointAddShippedSeg082 : List (JInstr 64) :=
  [ .cmovne "%rdi" (.reg "%rbx"),  -- l.2887 `cmovneq %rbx, %rdi`
    .mov "%rbx" (.imm 0),  -- l.2888 `movl $0, %ebx`
    .mov "%r8" (.reg "%r10"),  -- l.2889 `movq %r10, %r8`
    .bt "%rbx" (.imm 0),  -- l.2890 `btq $0, %rbx`
    .adcx "%r8" (.reg "%rdi"),  -- l.2891 `adcxq %rdi, %r8`
    .setc "%r9",  -- l.2892 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbx" (.reg "%rbp"),  -- l.2894 `movq %rbp, %rbx`
    .bt "%r9" (.imm 0),  -- l.2895 `btq $0, %r9`
    .adcx "%rbx" (.reg "%rcx"),  -- l.2896 `adcxq %rcx, %rbx`
    .setc "%rdi",  -- l.2897 `setc %dil; movzbq %dil, %rdi`
    .mov "%rbp" (.reg "%rsi"),  -- l.2899 `movq %rsi, %rbp`
    .bt "%rdi" (.imm 0),  -- l.2900 `btq $0, %rdi`
    .adcx "%rbp" (.reg "%rcx"),  -- l.2901 `adcxq %rcx, %rbp`
    .setc "%r9",  -- l.2902 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rsi" (.reg "%rax"),  -- l.2904 `movq %rax, %rsi`
    .bt "%r9" (.imm 0),  -- l.2905 `btq $0, %r9`
    .adcx "%rsi" (.reg "%rcx"),  -- l.2906 `adcxq %rcx, %rsi`
    .setc "%rdi",  -- l.2907 `setc %dil; movzbq %dil, %rdi`
    .mov "%rax" (.imm 19),  -- l.2909 `movq $19, %rax`
    .mov "%rcx" (.imm 0),  -- l.2910 `movq $0, %rcx`
    .mov "%rdi" (.imm 0),  -- l.2911 `movq $0, %rdi`
    .mov "%r9" (.imm 9223372036854775808),  -- l.2912 `movq $9223372036854775808, %r9`
    .mov "%r10" (.imm 0),  -- l.2913 `movl $0, %r10d`
    .mov "%r11" (.reg "%r8"),  -- l.2914 `movq %r8, %r11`
    .bt "%r10" (.imm 0),  -- l.2915 `btq $0, %r10`
    .adcx "%r11" (.reg "%rax"),  -- l.2916 `adcxq %rax, %r11`
    .setc "%r12",  -- l.2917 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rax" (.reg "%rbx"),  -- l.2919 `movq %rbx, %rax`
    .bt "%r12" (.imm 0),  -- l.2920 `btq $0, %r12`
    .adcx "%rax" (.reg "%rcx"),  -- l.2921 `adcxq %rcx, %rax`
    .setc "%r10",  -- l.2922 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rcx" (.reg "%rbp") ]  -- l.2924 `movq %rbp, %rcx`

/-- Segment 83 of the body: the 32 instructions from source lines 2925–2959. -/
def ed25519PointAddShippedSeg083 : List (JInstr 64) :=
  [ .bt "%r10" (.imm 0),  -- l.2925 `btq $0, %r10`
    .adcx "%rcx" (.reg "%rdi"),  -- l.2926 `adcxq %rdi, %rcx`
    .setc "%r12",  -- l.2927 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rsi"),  -- l.2929 `movq %rsi, %rdi`
    .bt "%r12" (.imm 0),  -- l.2930 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.2931 `adcxq %r9, %rdi`
    .setc "%r10",  -- l.2932 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%r8"),  -- l.2934 `movq %r8, %r9`
    .test "%r10" (.reg "%r10"),  -- l.2935 `testq %r10, %r10`
    .cmovne "%r9" (.reg "%r11"),  -- l.2936 `cmovneq %r11, %r9`
    .mov "%r8" (.reg "%rbx"),  -- l.2937 `movq %rbx, %r8`
    .test "%r10" (.reg "%r10"),  -- l.2938 `testq %r10, %r10`
    .cmovne "%r8" (.reg "%rax"),  -- l.2939 `cmovneq %rax, %r8`
    .mov "%rax" (.reg "%rbp"),  -- l.2940 `movq %rbp, %rax`
    .test "%r10" (.reg "%r10"),  -- l.2941 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rcx"),  -- l.2942 `cmovneq %rcx, %rax`
    .mov "%rbx" (.reg "%rsi"),  -- l.2943 `movq %rsi, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.2944 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rdi"),  -- l.2945 `cmovneq %rdi, %rbx`
    .mov "%rcx" (.imm 19),  -- l.2946 `movq $19, %rcx`
    .mov "%rsi" (.imm 0),  -- l.2947 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.2948 `movq $0, %rdi`
    .mov "%rbp" (.imm 9223372036854775808),  -- l.2949 `movq $9223372036854775808, %rbp`
    .mov "%r10" (.imm 0),  -- l.2950 `movl $0, %r10d`
    .mov "%r11" (.reg "%r9"),  -- l.2951 `movq %r9, %r11`
    .bt "%r10" (.imm 0),  -- l.2952 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.2953 `adcxq %rcx, %r11`
    .setc "%r12",  -- l.2954 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rcx" (.reg "%r8"),  -- l.2956 `movq %r8, %rcx`
    .bt "%r12" (.imm 0),  -- l.2957 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rsi"),  -- l.2958 `adcxq %rsi, %rcx`
    .setc "%r10" ]  -- l.2959 `setc %r10b; movzbq %r10b, %r10`

/-- Segment 84 of the body: the 32 instructions from source lines 2961–2994. -/
def ed25519PointAddShippedSeg084 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rax"),  -- l.2961 `movq %rax, %rsi`
    .bt "%r10" (.imm 0),  -- l.2962 `btq $0, %r10`
    .adcx "%rsi" (.reg "%rdi"),  -- l.2963 `adcxq %rdi, %rsi`
    .setc "%r12",  -- l.2964 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rbx"),  -- l.2966 `movq %rbx, %rdi`
    .bt "%r12" (.imm 0),  -- l.2967 `btq $0, %r12`
    .adcx "%rdi" (.reg "%rbp"),  -- l.2968 `adcxq %rbp, %rdi`
    .setc "%r10",  -- l.2969 `setc %r10b; movzbq %r10b, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2971 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r9"),  -- l.2972 `movq %r9, %rax`
    .test "%r10" (.reg "%r10"),  -- l.2973 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%r11"),  -- l.2974 `cmovneq %r11, %rax`
    .storeMem "%rsp" 304 (.reg "%rax"),  -- l.2975 `movq %rax, 304(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2976 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2977 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.2978 `movq %r8, %rax`
    .test "%r10" (.reg "%r10"),  -- l.2979 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rcx"),  -- l.2980 `cmovneq %rcx, %rax`
    .storeMem "%rsp" 312 (.reg "%rax"),  -- l.2981 `movq %rax, 312(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.2982 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.2983 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rax"),  -- l.2984 `movq %rax, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.2985 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rsi"),  -- l.2986 `cmovneq %rsi, %rbx`
    .storeMem "%rsp" 320 (.reg "%rbx"),  -- l.2987 `movq %rbx, 320(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.2988 `movq -128(%rsp), %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.2989 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.2990 `movq %rbx, %rax`
    .test "%r10" (.reg "%r10"),  -- l.2991 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rdi"),  -- l.2992 `cmovneq %rdi, %rax`
    .storeMem "%rsp" 328 (.reg "%rax"),  -- l.2993 `movq %rax, 328(%rsp)`
    .loadMem "%rax" "%rsp" (-128) ]  -- l.2994 `movq -128(%rsp), %rax`

/-- Segment 85 of the body: the 32 instructions from source lines 2995–3030. -/
def ed25519PointAddShippedSeg085 : List (JInstr 64) :=
  [ .mov "%rbx" (.imm 18446744073709551615),  -- l.2995 `movq $18446744073709551615, %rbx`
    .loadMem "%rsi" "%rsp" 48,  -- l.2996 `movq 48(%rsp), %rsi`
    .xor_ "%rsi" (.reg "%rbx"),  -- l.2997 `xorq %rbx, %rsi`
    .loadMem "%rdi" "%rsp" 56,  -- l.2998 `movq 56(%rsp), %rdi`
    .xor_ "%rdi" (.reg "%rbx"),  -- l.2999 `xorq %rbx, %rdi`
    .loadMem "%r8" "%rsp" 64,  -- l.3000 `movq 64(%rsp), %r8`
    .xor_ "%r8" (.reg "%rbx"),  -- l.3001 `xorq %rbx, %r8`
    .loadMem "%r10" "%rsp" 72,  -- l.3002 `movq 72(%rsp), %r10`
    .xor_ "%r10" (.reg "%rbx"),  -- l.3003 `xorq %rbx, %r10`
    .mov "%rbx" (.imm 1),  -- l.3004 `movl $1, %ebx`
    .loadMem "%r11" "%rsp" 208,  -- l.3005 `movq 208(%rsp), %r11`
    .bt "%rbx" (.imm 0),  -- l.3006 `btq $0, %rbx`
    .adcx "%r11" (.reg "%rsi"),  -- l.3007 `adcxq %rsi, %r11`
    .setc "%r12",  -- l.3008 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rbx" "%rsp" 216,  -- l.3010 `movq 216(%rsp), %rbx`
    .bt "%r12" (.imm 0),  -- l.3011 `btq $0, %r12`
    .adcx "%rbx" (.reg "%rdi"),  -- l.3012 `adcxq %rdi, %rbx`
    .setc "%rsi",  -- l.3013 `setc %sil; movzbq %sil, %rsi`
    .loadMem "%rdi" "%rsp" 224,  -- l.3015 `movq 224(%rsp), %rdi`
    .bt "%rsi" (.imm 0),  -- l.3016 `btq $0, %rsi`
    .adcx "%rdi" (.reg "%r8"),  -- l.3017 `adcxq %r8, %rdi`
    .setc "%r12",  -- l.3018 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rsi" "%rsp" 264,  -- l.3020 `movq 264(%rsp), %rsi`
    .bt "%r12" (.imm 0),  -- l.3021 `btq $0, %r12`
    .adcx "%rsi" (.reg "%r10"),  -- l.3022 `adcxq %r10, %rsi`
    .setc "%r8",  -- l.3023 `setc %r8b; movzbq %r8b, %r8`
    .mov "%r10" (.imm 18446744073709551597),  -- l.3025 `movq $18446744073709551597, %r10`
    .mov "%r12" (.imm 18446744073709551615),  -- l.3026 `movq $18446744073709551615, %r12`
    .mov "%r13" (.imm 18446744073709551615),  -- l.3027 `movq $18446744073709551615, %r13`
    .mov "%rax" (.imm 9223372036854775807),  -- l.3028 `movq $9223372036854775807, %rax`
    .mov "%rcx" (.imm 0),  -- l.3029 `movl $0, %ecx`
    .mov "%r9" (.reg "%r11") ]  -- l.3030 `movq %r11, %r9`

/-- Segment 86 of the body: the 32 instructions from source lines 3031–3066. -/
def ed25519PointAddShippedSeg086 : List (JInstr 64) :=
  [ .bt "%rcx" (.imm 0),  -- l.3031 `btq $0, %rcx`
    .adcx "%r9" (.reg "%r10"),  -- l.3032 `adcxq %r10, %r9`
    .setc "%rbp",  -- l.3033 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%rcx" (.reg "%rbx"),  -- l.3035 `movq %rbx, %rcx`
    .bt "%rbp" (.imm 0),  -- l.3036 `btq $0, %rbp`
    .adcx "%rcx" (.reg "%r12"),  -- l.3037 `adcxq %r12, %rcx`
    .setc "%r10",  -- l.3038 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbp" (.reg "%rdi"),  -- l.3040 `movq %rdi, %rbp`
    .bt "%r10" (.imm 0),  -- l.3041 `btq $0, %r10`
    .adcx "%rbp" (.reg "%r13"),  -- l.3042 `adcxq %r13, %rbp`
    .setc "%r12",  -- l.3043 `setc %r12b; movzbq %r12b, %r12`
    .mov "%r10" (.reg "%rsi"),  -- l.3045 `movq %rsi, %r10`
    .bt "%r12" (.imm 0),  -- l.3046 `btq $0, %r12`
    .adcx "%r10" (.reg "%rax"),  -- l.3047 `adcxq %rax, %r10`
    .setc "%r13",  -- l.3048 `setc %r13b; movzbq %r13b, %r13`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3050 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r9"),  -- l.3051 `movq %r9, %rax`
    .test "%r8" (.reg "%r8"),  -- l.3052 `testq %r8, %r8`
    .cmovne "%rax" (.reg "%r11"),  -- l.3053 `cmovneq %r11, %rax`
    .storeMem "%rsp" 232 (.reg "%rax"),  -- l.3054 `movq %rax, 232(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3055 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3056 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.3057 `movq %rcx, %rax`
    .test "%r8" (.reg "%r8"),  -- l.3058 `testq %r8, %r8`
    .cmovne "%rax" (.reg "%rbx"),  -- l.3059 `cmovneq %rbx, %rax`
    .storeMem "%rsp" 240 (.reg "%rax"),  -- l.3060 `movq %rax, 240(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3061 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3062 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbp"),  -- l.3063 `movq %rbp, %rax`
    .test "%r8" (.reg "%r8"),  -- l.3064 `testq %r8, %r8`
    .cmovne "%rax" (.reg "%rdi"),  -- l.3065 `cmovneq %rdi, %rax`
    .storeMem "%rsp" 248 (.reg "%rax") ]  -- l.3066 `movq %rax, 248(%rsp)`

/-- Segment 87 of the body: the 32 instructions from source lines 3067–3101. -/
def ed25519PointAddShippedSeg087 : List (JInstr 64) :=
  [ .loadMem "%rax" "%rsp" (-128),  -- l.3067 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3068 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r10"),  -- l.3069 `movq %r10, %rax`
    .test "%r8" (.reg "%r8"),  -- l.3070 `testq %r8, %r8`
    .cmovne "%rax" (.reg "%rsi"),  -- l.3071 `cmovneq %rsi, %rax`
    .storeMem "%rsp" 256 (.reg "%rax"),  -- l.3072 `movq %rax, 256(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3073 `movq -128(%rsp), %rax`
    .mov "%rsi" (.imm 18446744073709551615),  -- l.3074 `movq $18446744073709551615, %rsi`
    .loadMem "%rdi" "%rsp" 272,  -- l.3075 `movq 272(%rsp), %rdi`
    .xor_ "%rdi" (.reg "%rsi"),  -- l.3076 `xorq %rsi, %rdi`
    .loadMem "%rbp" "%rsp" 280,  -- l.3077 `movq 280(%rsp), %rbp`
    .xor_ "%rbp" (.reg "%rsi"),  -- l.3078 `xorq %rsi, %rbp`
    .loadMem "%r8" "%rsp" 288,  -- l.3079 `movq 288(%rsp), %r8`
    .xor_ "%r8" (.reg "%rsi"),  -- l.3080 `xorq %rsi, %r8`
    .loadMem "%r10" "%rsp" 296,  -- l.3081 `movq 296(%rsp), %r10`
    .xor_ "%r10" (.reg "%rsi"),  -- l.3082 `xorq %rsi, %r10`
    .mov "%rsi" (.imm 1),  -- l.3083 `movl $1, %esi`
    .loadMem "%r11" "%rsp" 304,  -- l.3084 `movq 304(%rsp), %r11`
    .bt "%rsi" (.imm 0),  -- l.3085 `btq $0, %rsi`
    .adcx "%r11" (.reg "%rdi"),  -- l.3086 `adcxq %rdi, %r11`
    .setc "%r12",  -- l.3087 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rsi" "%rsp" 312,  -- l.3089 `movq 312(%rsp), %rsi`
    .bt "%r12" (.imm 0),  -- l.3090 `btq $0, %r12`
    .adcx "%rsi" (.reg "%rbp"),  -- l.3091 `adcxq %rbp, %rsi`
    .setc "%rdi",  -- l.3092 `setc %dil; movzbq %dil, %rdi`
    .loadMem "%rbp" "%rsp" 320,  -- l.3094 `movq 320(%rsp), %rbp`
    .bt "%rdi" (.imm 0),  -- l.3095 `btq $0, %rdi`
    .adcx "%rbp" (.reg "%r8"),  -- l.3096 `adcxq %r8, %rbp`
    .setc "%r12",  -- l.3097 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rdi" "%rsp" 328,  -- l.3099 `movq 328(%rsp), %rdi`
    .bt "%r12" (.imm 0),  -- l.3100 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r10") ]  -- l.3101 `adcxq %r10, %rdi`

/-- Segment 88 of the body: the 32 instructions from source lines 3102–3138. -/
def ed25519PointAddShippedSeg088 : List (JInstr 64) :=
  [ .setc "%r8",  -- l.3102 `setc %r8b; movzbq %r8b, %r8`
    .mov "%r10" (.imm 18446744073709551597),  -- l.3104 `movq $18446744073709551597, %r10`
    .mov "%r12" (.imm 18446744073709551615),  -- l.3105 `movq $18446744073709551615, %r12`
    .mov "%r13" (.imm 18446744073709551615),  -- l.3106 `movq $18446744073709551615, %r13`
    .mov "%rcx" (.imm 9223372036854775807),  -- l.3107 `movq $9223372036854775807, %rcx`
    .mov "%rbx" (.imm 0),  -- l.3108 `movl $0, %ebx`
    .mov "%r9" (.reg "%r11"),  -- l.3109 `movq %r11, %r9`
    .bt "%rbx" (.imm 0),  -- l.3110 `btq $0, %rbx`
    .adcx "%r9" (.reg "%r10"),  -- l.3111 `adcxq %r10, %r9`
    .setc "%rax",  -- l.3112 `setc %al; movzbq %al, %rax`
    .mov "%rbx" (.reg "%rsi"),  -- l.3114 `movq %rsi, %rbx`
    .bt "%rax" (.imm 0),  -- l.3115 `btq $0, %rax`
    .adcx "%rbx" (.reg "%r12"),  -- l.3116 `adcxq %r12, %rbx`
    .setc "%r10",  -- l.3117 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.reg "%rbp"),  -- l.3119 `movq %rbp, %rax`
    .bt "%r10" (.imm 0),  -- l.3120 `btq $0, %r10`
    .adcx "%rax" (.reg "%r13"),  -- l.3121 `adcxq %r13, %rax`
    .setc "%r12",  -- l.3122 `setc %r12b; movzbq %r12b, %r12`
    .mov "%r10" (.reg "%rdi"),  -- l.3124 `movq %rdi, %r10`
    .bt "%r12" (.imm 0),  -- l.3125 `btq $0, %r12`
    .adcx "%r10" (.reg "%rcx"),  -- l.3126 `adcxq %rcx, %r10`
    .setc "%r13",  -- l.3127 `setc %r13b; movzbq %r13b, %r13`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3129 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r9"),  -- l.3130 `movq %r9, %rax`
    .test "%r8" (.reg "%r8"),  -- l.3131 `testq %r8, %r8`
    .cmovne "%rax" (.reg "%r11"),  -- l.3132 `cmovneq %r11, %rax`
    .storeMem "%rsp" 176 (.reg "%rax"),  -- l.3133 `movq %rax, 176(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3134 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3135 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.3136 `movq %rbx, %rax`
    .test "%r8" (.reg "%r8"),  -- l.3137 `testq %r8, %r8`
    .cmovne "%rax" (.reg "%rsi") ]  -- l.3138 `cmovneq %rsi, %rax`

/-- Segment 89 of the body: the 32 instructions from source lines 3139–3174. -/
def ed25519PointAddShippedSeg089 : List (JInstr 64) :=
  [ .storeMem "%rsp" 184 (.reg "%rax"),  -- l.3139 `movq %rax, 184(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3140 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.3141 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rax"),  -- l.3142 `movq %rax, %rbx`
    .test "%r8" (.reg "%r8"),  -- l.3143 `testq %r8, %r8`
    .cmovne "%rbx" (.reg "%rbp"),  -- l.3144 `cmovneq %rbp, %rbx`
    .storeMem "%rsp" 192 (.reg "%rbx"),  -- l.3145 `movq %rbx, 192(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.3146 `movq -128(%rsp), %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3147 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r10"),  -- l.3148 `movq %r10, %rax`
    .test "%r8" (.reg "%r8"),  -- l.3149 `testq %r8, %r8`
    .cmovne "%rax" (.reg "%rdi"),  -- l.3150 `cmovneq %rdi, %rax`
    .storeMem "%rsp" 200 (.reg "%rax"),  -- l.3151 `movq %rax, 200(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3152 `movq -128(%rsp), %rax`
    .mov "%rsi" (.imm 0),  -- l.3153 `movl $0, %esi`
    .loadMem "%rdi" "%rsp" 304,  -- l.3154 `movq 304(%rsp), %rdi`
    .bt "%rsi" (.imm 0),  -- l.3155 `btq $0, %rsi`
    .adcxMem "%rdi" "%rsp" 272,  -- l.3156 `adcxq 272(%rsp), %rdi`
    .setc "%rbp",  -- l.3157 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rsi" "%rsp" 312,  -- l.3159 `movq 312(%rsp), %rsi`
    .bt "%rbp" (.imm 0),  -- l.3160 `btq $0, %rbp`
    .adcxMem "%rsi" "%rsp" 280,  -- l.3161 `adcxq 280(%rsp), %rsi`
    .setc "%r8",  -- l.3162 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rbp" "%rsp" 320,  -- l.3164 `movq 320(%rsp), %rbp`
    .bt "%r8" (.imm 0),  -- l.3165 `btq $0, %r8`
    .adcxMem "%rbp" "%rsp" 288,  -- l.3166 `adcxq 288(%rsp), %rbp`
    .setc "%r10",  -- l.3167 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%r8" "%rsp" 328,  -- l.3169 `movq 328(%rsp), %r8`
    .bt "%r10" (.imm 0),  -- l.3170 `btq $0, %r10`
    .adcxMem "%r8" "%rsp" 296,  -- l.3171 `adcxq 296(%rsp), %r8`
    .setc "%r11",  -- l.3172 `setc %r11b; movzbq %r11b, %r11`
    .mov "%r10" (.imm 19) ]  -- l.3174 `movq $19, %r10`

/-- Segment 90 of the body: the 32 instructions from source lines 3175–3210. -/
def ed25519PointAddShippedSeg090 : List (JInstr 64) :=
  [ .mov "%r11" (.imm 0),  -- l.3175 `movq $0, %r11`
    .mov "%r12" (.imm 0),  -- l.3176 `movq $0, %r12`
    .mov "%r13" (.imm 9223372036854775808),  -- l.3177 `movq $9223372036854775808, %r13`
    .mov "%rax" (.imm 0),  -- l.3178 `movl $0, %eax`
    .mov "%rbx" (.reg "%rdi"),  -- l.3179 `movq %rdi, %rbx`
    .bt "%rax" (.imm 0),  -- l.3180 `btq $0, %rax`
    .adcx "%rbx" (.reg "%r10"),  -- l.3181 `adcxq %r10, %rbx`
    .setc "%r9",  -- l.3182 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rsi"),  -- l.3184 `movq %rsi, %rax`
    .bt "%r9" (.imm 0),  -- l.3185 `btq $0, %r9`
    .adcx "%rax" (.reg "%r11"),  -- l.3186 `adcxq %r11, %rax`
    .setc "%r10",  -- l.3187 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%rbp"),  -- l.3189 `movq %rbp, %r9`
    .bt "%r10" (.imm 0),  -- l.3190 `btq $0, %r10`
    .adcx "%r9" (.reg "%r12"),  -- l.3191 `adcxq %r12, %r9`
    .setc "%r11",  -- l.3192 `setc %r11b; movzbq %r11b, %r11`
    .mov "%r10" (.reg "%r8"),  -- l.3194 `movq %r8, %r10`
    .bt "%r11" (.imm 0),  -- l.3195 `btq $0, %r11`
    .adcx "%r10" (.reg "%r13"),  -- l.3196 `adcxq %r13, %r10`
    .setc "%r12",  -- l.3197 `setc %r12b; movzbq %r12b, %r12`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3199 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.3200 `movq %rdi, %rax`
    .test "%r12" (.reg "%r12"),  -- l.3201 `testq %r12, %r12`
    .cmovne "%rax" (.reg "%rbx"),  -- l.3202 `cmovneq %rbx, %rax`
    .storeMem "%rsp" 296 (.reg "%rax"),  -- l.3203 `movq %rax, 296(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3204 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.3205 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rsi"),  -- l.3206 `movq %rsi, %rbx`
    .test "%r12" (.reg "%r12"),  -- l.3207 `testq %r12, %r12`
    .cmovne "%rbx" (.reg "%rax"),  -- l.3208 `cmovneq %rax, %rbx`
    .storeMem "%rsp" 312 (.reg "%rbx"),  -- l.3209 `movq %rbx, 312(%rsp)`
    .loadMem "%rbx" "%rsp" (-128) ]  -- l.3210 `movq -128(%rsp), %rbx`

/-- Segment 91 of the body: the 32 instructions from source lines 3211–3246. -/
def ed25519PointAddShippedSeg091 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3211 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbp"),  -- l.3212 `movq %rbp, %rax`
    .test "%r12" (.reg "%r12"),  -- l.3213 `testq %r12, %r12`
    .cmovne "%rax" (.reg "%r9"),  -- l.3214 `cmovneq %r9, %rax`
    .storeMem "%rsp" 320 (.reg "%rax"),  -- l.3215 `movq %rax, 320(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3216 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3217 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.3218 `movq %r8, %rax`
    .test "%r12" (.reg "%r12"),  -- l.3219 `testq %r12, %r12`
    .cmovne "%rax" (.reg "%r10"),  -- l.3220 `cmovneq %r10, %rax`
    .storeMem "%rsp" 328 (.reg "%rax"),  -- l.3221 `movq %rax, 328(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3222 `movq -128(%rsp), %rax`
    .mov "%rdi" (.imm 0),  -- l.3223 `movl $0, %edi`
    .loadMem "%rbp" "%rsp" 208,  -- l.3224 `movq 208(%rsp), %rbp`
    .bt "%rdi" (.imm 0),  -- l.3225 `btq $0, %rdi`
    .adcxMem "%rbp" "%rsp" 48,  -- l.3226 `adcxq 48(%rsp), %rbp`
    .setc "%r8",  -- l.3227 `setc %r8b; movzbq %r8b, %r8`
    .loadMem "%rdi" "%rsp" 216,  -- l.3229 `movq 216(%rsp), %rdi`
    .bt "%r8" (.imm 0),  -- l.3230 `btq $0, %r8`
    .adcxMem "%rdi" "%rsp" 56,  -- l.3231 `adcxq 56(%rsp), %rdi`
    .setc "%r9",  -- l.3232 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%r8" "%rsp" 224,  -- l.3234 `movq 224(%rsp), %r8`
    .bt "%r9" (.imm 0),  -- l.3235 `btq $0, %r9`
    .adcxMem "%r8" "%rsp" 64,  -- l.3236 `adcxq 64(%rsp), %r8`
    .setc "%r10",  -- l.3237 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%r9" "%rsp" 264,  -- l.3239 `movq 264(%rsp), %r9`
    .bt "%r10" (.imm 0),  -- l.3240 `btq $0, %r10`
    .adcxMem "%r9" "%rsp" 72,  -- l.3241 `adcxq 72(%rsp), %r9`
    .setc "%r12",  -- l.3242 `setc %r12b; movzbq %r12b, %r12`
    .mov "%r10" (.imm 19),  -- l.3244 `movq $19, %r10`
    .mov "%r12" (.imm 0),  -- l.3245 `movq $0, %r12`
    .mov "%r13" (.imm 0) ]  -- l.3246 `movq $0, %r13`

/-- Segment 92 of the body: the 32 instructions from source lines 3247–3282. -/
def ed25519PointAddShippedSeg092 : List (JInstr 64) :=
  [ .mov "%rsi" (.imm 9223372036854775808),  -- l.3247 `movq $9223372036854775808, %rsi`
    .mov "%rcx" (.imm 0),  -- l.3248 `movl $0, %ecx`
    .mov "%rax" (.reg "%rbp"),  -- l.3249 `movq %rbp, %rax`
    .bt "%rcx" (.imm 0),  -- l.3250 `btq $0, %rcx`
    .adcx "%rax" (.reg "%r10"),  -- l.3251 `adcxq %r10, %rax`
    .setc "%rbx",  -- l.3252 `setc %bl; movzbq %bl, %rbx`
    .mov "%rcx" (.reg "%rdi"),  -- l.3254 `movq %rdi, %rcx`
    .bt "%rbx" (.imm 0),  -- l.3255 `btq $0, %rbx`
    .adcx "%rcx" (.reg "%r12"),  -- l.3256 `adcxq %r12, %rcx`
    .setc "%r10",  -- l.3257 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbx" (.reg "%r8"),  -- l.3259 `movq %r8, %rbx`
    .bt "%r10" (.imm 0),  -- l.3260 `btq $0, %r10`
    .adcx "%rbx" (.reg "%r13"),  -- l.3261 `adcxq %r13, %rbx`
    .setc "%r12",  -- l.3262 `setc %r12b; movzbq %r12b, %r12`
    .mov "%r10" (.reg "%r9"),  -- l.3264 `movq %r9, %r10`
    .bt "%r12" (.imm 0),  -- l.3265 `btq $0, %r12`
    .adcx "%r10" (.reg "%rsi"),  -- l.3266 `adcxq %rsi, %r10`
    .setc "%r13",  -- l.3267 `setc %r13b; movzbq %r13b, %r13`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.3269 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rbp"),  -- l.3270 `movq %rbp, %rbx`
    .test "%r13" (.reg "%r13"),  -- l.3271 `testq %r13, %r13`
    .cmovne "%rbx" (.reg "%rax"),  -- l.3272 `cmovneq %rax, %rbx`
    .storeMem "%rsp" 264 (.reg "%rbx"),  -- l.3273 `movq %rbx, 264(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.3274 `movq -128(%rsp), %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3275 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.3276 `movq %rdi, %rax`
    .test "%r13" (.reg "%r13"),  -- l.3277 `testq %r13, %r13`
    .cmovne "%rax" (.reg "%rcx"),  -- l.3278 `cmovneq %rcx, %rax`
    .storeMem "%rsp" 272 (.reg "%rax"),  -- l.3279 `movq %rax, 272(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3280 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3281 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8") ]  -- l.3282 `movq %r8, %rax`

/-- Segment 93 of the body: the 32 instructions from source lines 3283–3315. -/
def ed25519PointAddShippedSeg093 : List (JInstr 64) :=
  [ .test "%r13" (.reg "%r13"),  -- l.3283 `testq %r13, %r13`
    .cmovne "%rax" (.reg "%rbx"),  -- l.3284 `cmovneq %rbx, %rax`
    .storeMem "%rsp" 280 (.reg "%rax"),  -- l.3285 `movq %rax, 280(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3286 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3287 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r9"),  -- l.3288 `movq %r9, %rax`
    .test "%r13" (.reg "%r13"),  -- l.3289 `testq %r13, %r13`
    .cmovne "%rax" (.reg "%r10"),  -- l.3290 `cmovneq %r10, %rax`
    .storeMem "%rsp" 288 (.reg "%rax"),  -- l.3291 `movq %rax, 288(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3292 `movq -128(%rsp), %rax`
    .mov "%rdi" (.imm 0),  -- l.3293 `movq $0, %rdi`
    .mov "%rbp" (.imm 0),  -- l.3294 `movl $0, %ebp`
    .loadMem "%r8" "%rsp" 232,  -- l.3295 `movq 232(%rsp), %r8`
    .loadMem "%r15" "%rsp" 176,  -- l.3296 `movq 176(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.3297 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 232,  -- l.3298 `movq 232(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 176,  -- l.3299 `movq 176(%rsp), %r14`
    .mulx "%r9" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.3300 `mulx %r14, %r8, %r9`
    .bt "%rbp" (.imm 0),  -- l.3301 `btq $0, %rbp`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3302 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.3303 `movq %r8, %rax`
    .adcx "%rax" (.reg "%rdi"),  -- l.3304 `adcxq %rdi, %rax`
    .storeMem "%rsp" 304 (.reg "%rax"),  -- l.3305 `movq %rax, 304(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3306 `movq -128(%rsp), %rax`
    .setc "%r12",  -- l.3307 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rbp" "%rsp" 240,  -- l.3309 `movq 240(%rsp), %rbp`
    .loadMem "%r15" "%rsp" 176,  -- l.3310 `movq 176(%rsp), %r15`
    .imul "%rbp" (.reg "%r15"),  -- l.3311 `imulq %r15, %rbp`
    .loadMem "%rdx" "%rsp" 240,  -- l.3312 `movq 240(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 176,  -- l.3313 `movq 176(%rsp), %r14`
    .mulx "%r8" "%rbp" (.reg "%rdx") (.reg "%r14"),  -- l.3314 `mulx %r14, %rbp, %r8`
    .mov "%r13" (.reg "%rbp") ]  -- l.3315 `movq %rbp, %r13`

/-- Segment 94 of the body: the 32 instructions from source lines 3316–3350. -/
def ed25519PointAddShippedSeg094 : List (JInstr 64) :=
  [ .bt "%r12" (.imm 0),  -- l.3316 `btq $0, %r12`
    .adcx "%r13" (.reg "%r9"),  -- l.3317 `adcxq %r9, %r13`
    .setc "%r10",  -- l.3318 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rbp" "%rsp" 248,  -- l.3320 `movq 248(%rsp), %rbp`
    .loadMem "%r15" "%rsp" 176,  -- l.3321 `movq 176(%rsp), %r15`
    .imul "%rbp" (.reg "%r15"),  -- l.3322 `imulq %r15, %rbp`
    .loadMem "%rdx" "%rsp" 248,  -- l.3323 `movq 248(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 176,  -- l.3324 `movq 176(%rsp), %r14`
    .mulx "%r9" "%rbp" (.reg "%rdx") (.reg "%r14"),  -- l.3325 `mulx %r14, %rbp, %r9`
    .mov "%r12" (.reg "%rbp"),  -- l.3326 `movq %rbp, %r12`
    .bt "%r10" (.imm 0),  -- l.3327 `btq $0, %r10`
    .adcx "%r12" (.reg "%r8"),  -- l.3328 `adcxq %r8, %r12`
    .setc "%r11",  -- l.3329 `setc %r11b; movzbq %r11b, %r11`
    .loadMem "%rbp" "%rsp" 256,  -- l.3331 `movq 256(%rsp), %rbp`
    .loadMem "%r15" "%rsp" 176,  -- l.3332 `movq 176(%rsp), %r15`
    .imul "%rbp" (.reg "%r15"),  -- l.3333 `imulq %r15, %rbp`
    .loadMem "%rdx" "%rsp" 256,  -- l.3334 `movq 256(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 176,  -- l.3335 `movq 176(%rsp), %r14`
    .mulx "%r8" "%rbp" (.reg "%rdx") (.reg "%r14"),  -- l.3336 `mulx %r14, %rbp, %r8`
    .mov "%r10" (.reg "%rbp"),  -- l.3337 `movq %rbp, %r10`
    .bt "%r11" (.imm 0),  -- l.3338 `btq $0, %r11`
    .adcx "%r10" (.reg "%r9"),  -- l.3339 `adcxq %r9, %r10`
    .setc "%rbx",  -- l.3340 `setc %bl; movzbq %bl, %rbx`
    .bt "%rbx" (.imm 0),  -- l.3342 `btq $0, %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3343 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.3344 `movq %r8, %rax`
    .adcx "%rax" (.reg "%rdi"),  -- l.3345 `adcxq %rdi, %rax`
    .storeMem "%rsp" 224 (.reg "%rax"),  -- l.3346 `movq %rax, 224(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3347 `movq -128(%rsp), %rax`
    .mov "%rbx" (.imm 0),  -- l.3348 `movq $0, %rbx`
    .mov "%rdi" (.imm 0),  -- l.3349 `movl $0, %edi`
    .loadMem "%r8" "%rsp" 232 ]  -- l.3350 `movq 232(%rsp), %r8`

/-- Segment 95 of the body: the 32 instructions from source lines 3351–3385. -/
def ed25519PointAddShippedSeg095 : List (JInstr 64) :=
  [ .loadMem "%r15" "%rsp" 184,  -- l.3351 `movq 184(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.3352 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 232,  -- l.3353 `movq 232(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 184,  -- l.3354 `movq 184(%rsp), %r14`
    .mulx "%r9" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.3355 `mulx %r14, %r8, %r9`
    .mov "%r11" (.reg "%r8"),  -- l.3356 `movq %r8, %r11`
    .bt "%rdi" (.imm 0),  -- l.3357 `btq $0, %rdi`
    .adcx "%r11" (.reg "%rbx"),  -- l.3358 `adcxq %rbx, %r11`
    .setc "%rcx",  -- l.3359 `setc %cl; movzbq %cl, %rcx`
    .loadMem "%rdi" "%rsp" 240,  -- l.3361 `movq 240(%rsp), %rdi`
    .loadMem "%r15" "%rsp" 184,  -- l.3362 `movq 184(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.3363 `imulq %r15, %rdi`
    .loadMem "%rdx" "%rsp" 240,  -- l.3364 `movq 240(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 184,  -- l.3365 `movq 184(%rsp), %r14`
    .mulx "%r8" "%rdi" (.reg "%rdx") (.reg "%r14"),  -- l.3366 `mulx %r14, %rdi, %r8`
    .mov "%rax" (.reg "%rdi"),  -- l.3367 `movq %rdi, %rax`
    .bt "%rcx" (.imm 0),  -- l.3368 `btq $0, %rcx`
    .adcx "%rax" (.reg "%r9"),  -- l.3369 `adcxq %r9, %rax`
    .setc "%rsi",  -- l.3370 `setc %sil; movzbq %sil, %rsi`
    .loadMem "%rcx" "%rsp" 248,  -- l.3372 `movq 248(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 184,  -- l.3373 `movq 184(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3374 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 248,  -- l.3375 `movq 248(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 184,  -- l.3376 `movq 184(%rsp), %r14`
    .mulx "%rdi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3377 `mulx %r14, %rcx, %rdi`
    .mov "%r9" (.reg "%rcx"),  -- l.3378 `movq %rcx, %r9`
    .bt "%rsi" (.imm 0),  -- l.3379 `btq $0, %rsi`
    .adcx "%r9" (.reg "%r8"),  -- l.3380 `adcxq %r8, %r9`
    .setc "%rbp",  -- l.3381 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rcx" "%rsp" 256,  -- l.3383 `movq 256(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 184,  -- l.3384 `movq 184(%rsp), %r15`
    .imul "%rcx" (.reg "%r15") ]  -- l.3385 `imulq %r15, %rcx`

/-- Segment 96 of the body: the 32 instructions from source lines 3386–3421. -/
def ed25519PointAddShippedSeg096 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsp" 256,  -- l.3386 `movq 256(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 184,  -- l.3387 `movq 184(%rsp), %r14`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3388 `mulx %r14, %rcx, %rsi`
    .bt "%rbp" (.imm 0),  -- l.3389 `btq $0, %rbp`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3390 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.3391 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%rdi"),  -- l.3392 `adcxq %rdi, %rax`
    .storeMem "%rsp" 216 (.reg "%rax"),  -- l.3393 `movq %rax, 216(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3394 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.3395 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rcx" (.reg "%rsi"),  -- l.3397 `movq %rsi, %rcx`
    .bt "%r8" (.imm 0),  -- l.3398 `btq $0, %r8`
    .adcx "%rcx" (.reg "%rbx"),  -- l.3399 `adcxq %rbx, %rcx`
    .mov "%rbx" (.imm 0),  -- l.3400 `movq $0, %rbx`
    .mov "%rsi" (.imm 0),  -- l.3401 `movl $0, %esi`
    .bt "%rsi" (.imm 0),  -- l.3402 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3403 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r13"),  -- l.3404 `movq %r13, %rax`
    .adcx "%rax" (.reg "%r11"),  -- l.3405 `adcxq %r11, %rax`
    .storeMem "%rsp" 208 (.reg "%rax"),  -- l.3406 `movq %rax, 208(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3407 `movq -128(%rsp), %rax`
    .setc "%rbp",  -- l.3408 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%rsi" (.reg "%r12"),  -- l.3410 `movq %r12, %rsi`
    .bt "%rbp" (.imm 0),  -- l.3411 `btq $0, %rbp`
    .adcx "%rsi" (.reg "%rax"),  -- l.3412 `adcxq %rax, %rsi`
    .setc "%r8",  -- l.3413 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rax" (.reg "%r10"),  -- l.3415 `movq %r10, %rax`
    .bt "%r8" (.imm 0),  -- l.3416 `btq $0, %r8`
    .adcx "%rax" (.reg "%r9"),  -- l.3417 `adcxq %r9, %rax`
    .setc "%rbp",  -- l.3418 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%r8" "%rsp" 224,  -- l.3420 `movq 224(%rsp), %r8`
    .bt "%rbp" (.imm 0) ]  -- l.3421 `btq $0, %rbp`

/-- Segment 97 of the body: the 32 instructions from source lines 3422–3457. -/
def ed25519PointAddShippedSeg097 : List (JInstr 64) :=
  [ .adcxMem "%r8" "%rsp" 216,  -- l.3422 `adcxq 216(%rsp), %r8`
    .setc "%r9",  -- l.3423 `setc %r9b; movzbq %r9b, %r9`
    .bt "%r9" (.imm 0),  -- l.3425 `btq $0, %r9`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3426 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.3427 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%rcx"),  -- l.3428 `adcxq %rcx, %rax`
    .storeMem "%rsp" 224 (.reg "%rax"),  -- l.3429 `movq %rax, 224(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3430 `movq -128(%rsp), %rax`
    .setc "%r10",  -- l.3431 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbx" (.imm 0),  -- l.3433 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.3434 `movl $0, %ecx`
    .loadMem "%r9" "%rsp" 232,  -- l.3435 `movq 232(%rsp), %r9`
    .loadMem "%r15" "%rsp" 192,  -- l.3436 `movq 192(%rsp), %r15`
    .imul "%r9" (.reg "%r15"),  -- l.3437 `imulq %r15, %r9`
    .loadMem "%rdx" "%rsp" 232,  -- l.3438 `movq 232(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 192,  -- l.3439 `movq 192(%rsp), %r14`
    .mulx "%r10" "%r9" (.reg "%rdx") (.reg "%r14"),  -- l.3440 `mulx %r14, %r9, %r10`
    .mov "%r11" (.reg "%r9"),  -- l.3441 `movq %r9, %r11`
    .bt "%rcx" (.imm 0),  -- l.3442 `btq $0, %rcx`
    .adcx "%r11" (.reg "%rbx"),  -- l.3443 `adcxq %rbx, %r11`
    .setc "%r12",  -- l.3444 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rcx" "%rsp" 240,  -- l.3446 `movq 240(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 192,  -- l.3447 `movq 192(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3448 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 240,  -- l.3449 `movq 240(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 192,  -- l.3450 `movq 192(%rsp), %r14`
    .mulx "%r9" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3451 `mulx %r14, %rcx, %r9`
    .mov "%r13" (.reg "%rcx"),  -- l.3452 `movq %rcx, %r13`
    .bt "%r12" (.imm 0),  -- l.3453 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.3454 `adcxq %r10, %r13`
    .setc "%rdi",  -- l.3455 `setc %dil; movzbq %dil, %rdi`
    .loadMem "%rcx" "%rsp" 248 ]  -- l.3457 `movq 248(%rsp), %rcx`

/-- Segment 98 of the body: the 32 instructions from source lines 3458–3491. -/
def ed25519PointAddShippedSeg098 : List (JInstr 64) :=
  [ .loadMem "%r15" "%rsp" 192,  -- l.3458 `movq 192(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3459 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 248,  -- l.3460 `movq 248(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 192,  -- l.3461 `movq 192(%rsp), %r14`
    .mulx "%r10" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3462 `mulx %r14, %rcx, %r10`
    .mov "%r12" (.reg "%rcx"),  -- l.3463 `movq %rcx, %r12`
    .bt "%rdi" (.imm 0),  -- l.3464 `btq $0, %rdi`
    .adcx "%r12" (.reg "%r9"),  -- l.3465 `adcxq %r9, %r12`
    .setc "%rbp",  -- l.3466 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rcx" "%rsp" 256,  -- l.3468 `movq 256(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 192,  -- l.3469 `movq 192(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3470 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 256,  -- l.3471 `movq 256(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 192,  -- l.3472 `movq 192(%rsp), %r14`
    .mulx "%rdi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3473 `mulx %r14, %rcx, %rdi`
    .bt "%rbp" (.imm 0),  -- l.3474 `btq $0, %rbp`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3475 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.3476 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.3477 `adcxq %r10, %rax`
    .storeMem "%rsp" 216 (.reg "%rax"),  -- l.3478 `movq %rax, 216(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3479 `movq -128(%rsp), %rax`
    .setc "%r9",  -- l.3480 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi"),  -- l.3482 `movq %rdi, %rcx`
    .bt "%r9" (.imm 0),  -- l.3483 `btq $0, %r9`
    .adcx "%rcx" (.reg "%rbx"),  -- l.3484 `adcxq %rbx, %rcx`
    .mov "%rbx" (.imm 0),  -- l.3485 `movq $0, %rbx`
    .mov "%rdi" (.imm 0),  -- l.3486 `movl $0, %edi`
    .bt "%rdi" (.imm 0),  -- l.3487 `btq $0, %rdi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3488 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rsi"),  -- l.3489 `movq %rsi, %rax`
    .adcx "%rax" (.reg "%r11"),  -- l.3490 `adcxq %r11, %rax`
    .storeMem "%rsp" 168 (.reg "%rax") ]  -- l.3491 `movq %rax, 168(%rsp)`

/-- Segment 99 of the body: the 32 instructions from source lines 3492–3528. -/
def ed25519PointAddShippedSeg099 : List (JInstr 64) :=
  [ .loadMem "%rax" "%rsp" (-128),  -- l.3492 `movq -128(%rsp), %rax`
    .setc "%r9",  -- l.3493 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rsi" (.reg "%rax"),  -- l.3495 `movq %rax, %rsi`
    .bt "%r9" (.imm 0),  -- l.3496 `btq $0, %r9`
    .adcx "%rsi" (.reg "%r13"),  -- l.3497 `adcxq %r13, %rsi`
    .setc "%rdi",  -- l.3498 `setc %dil; movzbq %dil, %rdi`
    .mov "%rax" (.reg "%r8"),  -- l.3500 `movq %r8, %rax`
    .bt "%rdi" (.imm 0),  -- l.3501 `btq $0, %rdi`
    .adcx "%rax" (.reg "%r12"),  -- l.3502 `adcxq %r12, %rax`
    .setc "%r9",  -- l.3503 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rdi" "%rsp" 224,  -- l.3505 `movq 224(%rsp), %rdi`
    .bt "%r9" (.imm 0),  -- l.3506 `btq $0, %r9`
    .adcxMem "%rdi" "%rsp" 216,  -- l.3507 `adcxq 216(%rsp), %rdi`
    .setc "%r8",  -- l.3508 `setc %r8b; movzbq %r8b, %r8`
    .bt "%r8" (.imm 0),  -- l.3510 `btq $0, %r8`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3511 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.3512 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%rcx"),  -- l.3513 `adcxq %rcx, %rax`
    .storeMem "%rsp" 224 (.reg "%rax"),  -- l.3514 `movq %rax, 224(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3515 `movq -128(%rsp), %rax`
    .setc "%r10",  -- l.3516 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbx" (.imm 0),  -- l.3518 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.3519 `movl $0, %ecx`
    .loadMem "%r8" "%rsp" 232,  -- l.3520 `movq 232(%rsp), %r8`
    .loadMem "%r15" "%rsp" 200,  -- l.3521 `movq 200(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.3522 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 232,  -- l.3523 `movq 232(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 200,  -- l.3524 `movq 200(%rsp), %r14`
    .mulx "%r10" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.3525 `mulx %r14, %r8, %r10`
    .mov "%r11" (.reg "%r8"),  -- l.3526 `movq %r8, %r11`
    .bt "%rcx" (.imm 0),  -- l.3527 `btq $0, %rcx`
    .adcx "%r11" (.reg "%rbx") ]  -- l.3528 `adcxq %rbx, %r11`

/-- Segment 100 of the body: the 32 instructions from source lines 3529–3563. -/
def ed25519PointAddShippedSeg100 : List (JInstr 64) :=
  [ .setc "%r12",  -- l.3529 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rcx" "%rsp" 240,  -- l.3531 `movq 240(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 200,  -- l.3532 `movq 200(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3533 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 240,  -- l.3534 `movq 240(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 200,  -- l.3535 `movq 200(%rsp), %r14`
    .mulx "%r8" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3536 `mulx %r14, %rcx, %r8`
    .mov "%r13" (.reg "%rcx"),  -- l.3537 `movq %rcx, %r13`
    .bt "%r12" (.imm 0),  -- l.3538 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.3539 `adcxq %r10, %r13`
    .setc "%rbp",  -- l.3540 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rcx" "%rsp" 248,  -- l.3542 `movq 248(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 200,  -- l.3543 `movq 200(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3544 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 248,  -- l.3545 `movq 248(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 200,  -- l.3546 `movq 200(%rsp), %r14`
    .mulx "%r10" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3547 `mulx %r14, %rcx, %r10`
    .mov "%r12" (.reg "%rcx"),  -- l.3548 `movq %rcx, %r12`
    .bt "%rbp" (.imm 0),  -- l.3549 `btq $0, %rbp`
    .adcx "%r12" (.reg "%r8"),  -- l.3550 `adcxq %r8, %r12`
    .setc "%r9",  -- l.3551 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rcx" "%rsp" 256,  -- l.3553 `movq 256(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 200,  -- l.3554 `movq 200(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3555 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 256,  -- l.3556 `movq 256(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 200,  -- l.3557 `movq 200(%rsp), %r14`
    .mulx "%rbp" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3558 `mulx %r14, %rcx, %rbp`
    .bt "%r9" (.imm 0),  -- l.3559 `btq $0, %r9`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3560 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.3561 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.3562 `adcxq %r10, %rax`
    .storeMem "%rsp" 216 (.reg "%rax") ]  -- l.3563 `movq %rax, 216(%rsp)`

/-- Segment 101 of the body: the 32 instructions from source lines 3564–3601. -/
def ed25519PointAddShippedSeg101 : List (JInstr 64) :=
  [ .loadMem "%rax" "%rsp" (-128),  -- l.3564 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.3565 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rcx" (.reg "%rbp"),  -- l.3567 `movq %rbp, %rcx`
    .bt "%r8" (.imm 0),  -- l.3568 `btq $0, %r8`
    .adcx "%rcx" (.reg "%rbx"),  -- l.3569 `adcxq %rbx, %rcx`
    .mov "%rbx" (.imm 0),  -- l.3570 `movq $0, %rbx`
    .mov "%rbp" (.imm 0),  -- l.3571 `movl $0, %ebp`
    .mov "%r8" (.reg "%rsi"),  -- l.3572 `movq %rsi, %r8`
    .bt "%rbp" (.imm 0),  -- l.3573 `btq $0, %rbp`
    .adcx "%r8" (.reg "%r11"),  -- l.3574 `adcxq %r11, %r8`
    .setc "%r9",  -- l.3575 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rsi" (.reg "%rax"),  -- l.3577 `movq %rax, %rsi`
    .bt "%r9" (.imm 0),  -- l.3578 `btq $0, %r9`
    .adcx "%rsi" (.reg "%r13"),  -- l.3579 `adcxq %r13, %rsi`
    .setc "%rbp",  -- l.3580 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%rax" (.reg "%rdi"),  -- l.3582 `movq %rdi, %rax`
    .bt "%rbp" (.imm 0),  -- l.3583 `btq $0, %rbp`
    .adcx "%rax" (.reg "%r12"),  -- l.3584 `adcxq %r12, %rax`
    .setc "%r9",  -- l.3585 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rdi" "%rsp" 224,  -- l.3587 `movq 224(%rsp), %rdi`
    .bt "%r9" (.imm 0),  -- l.3588 `btq $0, %r9`
    .adcxMem "%rdi" "%rsp" 216,  -- l.3589 `adcxq 216(%rsp), %rdi`
    .setc "%rbp",  -- l.3590 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%r9" (.reg "%rbx"),  -- l.3592 `movq %rbx, %r9`
    .bt "%rbp" (.imm 0),  -- l.3593 `btq $0, %rbp`
    .adcx "%r9" (.reg "%rcx"),  -- l.3594 `adcxq %rcx, %r9`
    .setc "%r10",  -- l.3595 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbx" (.imm 38),  -- l.3597 `movq $38, %rbx`
    .mov "%rcx" (.imm 0),  -- l.3598 `movq $0, %rcx`
    .mov "%rbp" (.imm 0),  -- l.3599 `movl $0, %ebp`
    .mov "%r10" (.reg "%rsi"),  -- l.3600 `movq %rsi, %r10`
    .imul "%r10" (.reg "%rbx") ]  -- l.3601 `imulq %rbx, %r10`

/-- Segment 102 of the body: the 32 instructions from source lines 3602–3637. -/
def ed25519PointAddShippedSeg102 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%rsi"),  -- l.3602 `movq %rsi, %rdx`
    .mulx "%r11" "%r10" (.reg "%rdx") (.reg "%rbx"),  -- l.3603 `mulx %rbx, %r10, %r11`
    .mov "%rsi" (.reg "%r10"),  -- l.3604 `movq %r10, %rsi`
    .bt "%rbp" (.imm 0),  -- l.3605 `btq $0, %rbp`
    .adcx "%rsi" (.reg "%rcx"),  -- l.3606 `adcxq %rcx, %rsi`
    .setc "%r12",  -- l.3607 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rax"),  -- l.3609 `movq %rax, %rbp`
    .imul "%rbp" (.reg "%rbx"),  -- l.3610 `imulq %rbx, %rbp`
    .mov "%rdx" (.reg "%rax"),  -- l.3611 `movq %rax, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rbx"),  -- l.3612 `mulx %rbx, %rbp, %r10`
    .mov "%rax" (.reg "%rbp"),  -- l.3613 `movq %rbp, %rax`
    .bt "%r12" (.imm 0),  -- l.3614 `btq $0, %r12`
    .adcx "%rax" (.reg "%r11"),  -- l.3615 `adcxq %r11, %rax`
    .setc "%r13",  -- l.3616 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%rdi"),  -- l.3618 `movq %rdi, %rbp`
    .imul "%rbp" (.reg "%rbx"),  -- l.3619 `imulq %rbx, %rbp`
    .mov "%rdx" (.reg "%rdi"),  -- l.3620 `movq %rdi, %rdx`
    .mulx "%r11" "%rbp" (.reg "%rdx") (.reg "%rbx"),  -- l.3621 `mulx %rbx, %rbp, %r11`
    .mov "%rdi" (.reg "%rbp"),  -- l.3622 `movq %rbp, %rdi`
    .bt "%r13" (.imm 0),  -- l.3623 `btq $0, %r13`
    .adcx "%rdi" (.reg "%r10"),  -- l.3624 `adcxq %r10, %rdi`
    .setc "%r12",  -- l.3625 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%r9"),  -- l.3627 `movq %r9, %rbp`
    .imul "%rbp" (.reg "%rbx"),  -- l.3628 `imulq %rbx, %rbp`
    .mov "%rdx" (.reg "%r9"),  -- l.3629 `movq %r9, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rbx"),  -- l.3630 `mulx %rbx, %rbp, %r10`
    .mov "%r9" (.reg "%rbp"),  -- l.3631 `movq %rbp, %r9`
    .bt "%r12" (.imm 0),  -- l.3632 `btq $0, %r12`
    .adcx "%r9" (.reg "%r11"),  -- l.3633 `adcxq %r11, %r9`
    .setc "%r13",  -- l.3634 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%r10"),  -- l.3636 `movq %r10, %rbp`
    .bt "%r13" (.imm 0) ]  -- l.3637 `btq $0, %r13`

/-- Segment 103 of the body: the 32 instructions from source lines 3638–3674. -/
def ed25519PointAddShippedSeg103 : List (JInstr 64) :=
  [ .adcx "%rbp" (.reg "%rcx"),  -- l.3638 `adcxq %rcx, %rbp`
    .mov "%rcx" (.imm 0),  -- l.3639 `movq $0, %rcx`
    .mov "%r10" (.imm 0),  -- l.3640 `movl $0, %r10d`
    .loadMem "%r11" "%rsp" 304,  -- l.3641 `movq 304(%rsp), %r11`
    .bt "%r10" (.imm 0),  -- l.3642 `btq $0, %r10`
    .adcx "%r11" (.reg "%rsi"),  -- l.3643 `adcxq %rsi, %r11`
    .setc "%r12",  -- l.3644 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rsi" "%rsp" 208,  -- l.3646 `movq 208(%rsp), %rsi`
    .bt "%r12" (.imm 0),  -- l.3647 `btq $0, %r12`
    .adcx "%rsi" (.reg "%rax"),  -- l.3648 `adcxq %rax, %rsi`
    .setc "%r10",  -- l.3649 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rax" "%rsp" 168,  -- l.3651 `movq 168(%rsp), %rax`
    .bt "%r10" (.imm 0),  -- l.3652 `btq $0, %r10`
    .adcx "%rax" (.reg "%rdi"),  -- l.3653 `adcxq %rdi, %rax`
    .setc "%r12",  -- l.3654 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%r8"),  -- l.3656 `movq %r8, %rdi`
    .bt "%r12" (.imm 0),  -- l.3657 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.3658 `adcxq %r9, %rdi`
    .setc "%r10",  -- l.3659 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r8" (.reg "%rcx"),  -- l.3661 `movq %rcx, %r8`
    .bt "%r10" (.imm 0),  -- l.3662 `btq $0, %r10`
    .adcx "%r8" (.reg "%rbp"),  -- l.3663 `adcxq %rbp, %r8`
    .setc "%r9",  -- l.3664 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbp" (.imm 0),  -- l.3666 `movq $0, %rbp`
    .mov "%r9" (.imm 0),  -- l.3667 `movl $0, %r9d`
    .mov "%r10" (.reg "%r8"),  -- l.3668 `movq %r8, %r10`
    .imul "%r10" (.reg "%rbx"),  -- l.3669 `imulq %rbx, %r10`
    .mov "%rdx" (.reg "%r8"),  -- l.3670 `movq %r8, %rdx`
    .mulx "%r12" "%r10" (.reg "%rdx") (.reg "%rbx"),  -- l.3671 `mulx %rbx, %r10, %r12`
    .mov "%r8" (.reg "%r10"),  -- l.3672 `movq %r10, %r8`
    .bt "%r9" (.imm 0),  -- l.3673 `btq $0, %r9`
    .adcx "%r8" (.reg "%rbp") ]  -- l.3674 `adcxq %rbp, %r8`

/-- Segment 104 of the body: the 32 instructions from source lines 3675–3712. -/
def ed25519PointAddShippedSeg104 : List (JInstr 64) :=
  [ .setc "%r13",  -- l.3675 `setc %r13b; movzbq %r13b, %r13`
    .mov "%r9" (.reg "%r12"),  -- l.3677 `movq %r12, %r9`
    .bt "%r13" (.imm 0),  -- l.3678 `btq $0, %r13`
    .adcx "%r9" (.reg "%rbp"),  -- l.3679 `adcxq %rbp, %r9`
    .mov "%rbp" (.imm 0),  -- l.3680 `movl $0, %ebp`
    .mov "%r10" (.reg "%r11"),  -- l.3681 `movq %r11, %r10`
    .bt "%rbp" (.imm 0),  -- l.3682 `btq $0, %rbp`
    .adcx "%r10" (.reg "%r8"),  -- l.3683 `adcxq %r8, %r10`
    .setc "%r12",  -- l.3684 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rsi"),  -- l.3686 `movq %rsi, %rbp`
    .bt "%r12" (.imm 0),  -- l.3687 `btq $0, %r12`
    .adcx "%rbp" (.reg "%r9"),  -- l.3688 `adcxq %r9, %rbp`
    .setc "%r8",  -- l.3689 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rsi" (.reg "%rax"),  -- l.3691 `movq %rax, %rsi`
    .bt "%r8" (.imm 0),  -- l.3692 `btq $0, %r8`
    .adcx "%rsi" (.reg "%rcx"),  -- l.3693 `adcxq %rcx, %rsi`
    .setc "%r9",  -- l.3694 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rdi"),  -- l.3696 `movq %rdi, %rax`
    .bt "%r9" (.imm 0),  -- l.3697 `btq $0, %r9`
    .adcx "%rax" (.reg "%rcx"),  -- l.3698 `adcxq %rcx, %rax`
    .setc "%r8",  -- l.3699 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rdi" (.reg "%rcx"),  -- l.3701 `movq %rcx, %rdi`
    .test "%r8" (.reg "%r8"),  -- l.3702 `testq %r8, %r8`
    .cmovne "%rdi" (.reg "%rbx"),  -- l.3703 `cmovneq %rbx, %rdi`
    .mov "%rbx" (.imm 0),  -- l.3704 `movl $0, %ebx`
    .mov "%r8" (.reg "%r10"),  -- l.3705 `movq %r10, %r8`
    .bt "%rbx" (.imm 0),  -- l.3706 `btq $0, %rbx`
    .adcx "%r8" (.reg "%rdi"),  -- l.3707 `adcxq %rdi, %r8`
    .setc "%r9",  -- l.3708 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbx" (.reg "%rbp"),  -- l.3710 `movq %rbp, %rbx`
    .bt "%r9" (.imm 0),  -- l.3711 `btq $0, %r9`
    .adcx "%rbx" (.reg "%rcx") ]  -- l.3712 `adcxq %rcx, %rbx`

/-- Segment 105 of the body: the 32 instructions from source lines 3713–3751. -/
def ed25519PointAddShippedSeg105 : List (JInstr 64) :=
  [ .setc "%rdi",  -- l.3713 `setc %dil; movzbq %dil, %rdi`
    .mov "%rbp" (.reg "%rsi"),  -- l.3715 `movq %rsi, %rbp`
    .bt "%rdi" (.imm 0),  -- l.3716 `btq $0, %rdi`
    .adcx "%rbp" (.reg "%rcx"),  -- l.3717 `adcxq %rcx, %rbp`
    .setc "%r9",  -- l.3718 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rsi" (.reg "%rax"),  -- l.3720 `movq %rax, %rsi`
    .bt "%r9" (.imm 0),  -- l.3721 `btq $0, %r9`
    .adcx "%rsi" (.reg "%rcx"),  -- l.3722 `adcxq %rcx, %rsi`
    .setc "%rdi",  -- l.3723 `setc %dil; movzbq %dil, %rdi`
    .mov "%rax" (.imm 19),  -- l.3725 `movq $19, %rax`
    .mov "%rcx" (.imm 0),  -- l.3726 `movq $0, %rcx`
    .mov "%rdi" (.imm 0),  -- l.3727 `movq $0, %rdi`
    .mov "%r9" (.imm 9223372036854775808),  -- l.3728 `movq $9223372036854775808, %r9`
    .mov "%r10" (.imm 0),  -- l.3729 `movl $0, %r10d`
    .mov "%r11" (.reg "%r8"),  -- l.3730 `movq %r8, %r11`
    .bt "%r10" (.imm 0),  -- l.3731 `btq $0, %r10`
    .adcx "%r11" (.reg "%rax"),  -- l.3732 `adcxq %rax, %r11`
    .setc "%r12",  -- l.3733 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rax" (.reg "%rbx"),  -- l.3735 `movq %rbx, %rax`
    .bt "%r12" (.imm 0),  -- l.3736 `btq $0, %r12`
    .adcx "%rax" (.reg "%rcx"),  -- l.3737 `adcxq %rcx, %rax`
    .setc "%r10",  -- l.3738 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rcx" (.reg "%rbp"),  -- l.3740 `movq %rbp, %rcx`
    .bt "%r10" (.imm 0),  -- l.3741 `btq $0, %r10`
    .adcx "%rcx" (.reg "%rdi"),  -- l.3742 `adcxq %rdi, %rcx`
    .setc "%r12",  -- l.3743 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rsi"),  -- l.3745 `movq %rsi, %rdi`
    .bt "%r12" (.imm 0),  -- l.3746 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.3747 `adcxq %r9, %rdi`
    .setc "%r10",  -- l.3748 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%r8"),  -- l.3750 `movq %r8, %r9`
    .test "%r10" (.reg "%r10") ]  -- l.3751 `testq %r10, %r10`

/-- Segment 106 of the body: the 32 instructions from source lines 3752–3787. -/
def ed25519PointAddShippedSeg106 : List (JInstr 64) :=
  [ .cmovne "%r9" (.reg "%r11"),  -- l.3752 `cmovneq %r11, %r9`
    .mov "%r8" (.reg "%rbx"),  -- l.3753 `movq %rbx, %r8`
    .test "%r10" (.reg "%r10"),  -- l.3754 `testq %r10, %r10`
    .cmovne "%r8" (.reg "%rax"),  -- l.3755 `cmovneq %rax, %r8`
    .mov "%rax" (.reg "%rbp"),  -- l.3756 `movq %rbp, %rax`
    .test "%r10" (.reg "%r10"),  -- l.3757 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rcx"),  -- l.3758 `cmovneq %rcx, %rax`
    .mov "%rbx" (.reg "%rsi"),  -- l.3759 `movq %rsi, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.3760 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rdi"),  -- l.3761 `cmovneq %rdi, %rbx`
    .mov "%rcx" (.imm 19),  -- l.3762 `movq $19, %rcx`
    .mov "%rsi" (.imm 0),  -- l.3763 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.3764 `movq $0, %rdi`
    .mov "%rbp" (.imm 9223372036854775808),  -- l.3765 `movq $9223372036854775808, %rbp`
    .mov "%r10" (.imm 0),  -- l.3766 `movl $0, %r10d`
    .mov "%r11" (.reg "%r9"),  -- l.3767 `movq %r9, %r11`
    .bt "%r10" (.imm 0),  -- l.3768 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.3769 `adcxq %rcx, %r11`
    .setc "%r12",  -- l.3770 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rcx" (.reg "%r8"),  -- l.3772 `movq %r8, %rcx`
    .bt "%r12" (.imm 0),  -- l.3773 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rsi"),  -- l.3774 `adcxq %rsi, %rcx`
    .setc "%r10",  -- l.3775 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rax"),  -- l.3777 `movq %rax, %rsi`
    .bt "%r10" (.imm 0),  -- l.3778 `btq $0, %r10`
    .adcx "%rsi" (.reg "%rdi"),  -- l.3779 `adcxq %rdi, %rsi`
    .setc "%r12",  -- l.3780 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rbx"),  -- l.3782 `movq %rbx, %rdi`
    .bt "%r12" (.imm 0),  -- l.3783 `btq $0, %r12`
    .adcx "%rdi" (.reg "%rbp"),  -- l.3784 `adcxq %rbp, %rdi`
    .setc "%r10",  -- l.3785 `setc %r10b; movzbq %r10b, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax") ]  -- l.3787 `movq %rax, -128(%rsp)`

/-- Segment 107 of the body: the 32 instructions from source lines 3788–3819. -/
def ed25519PointAddShippedSeg107 : List (JInstr 64) :=
  [ .mov "%rax" (.reg "%r9"),  -- l.3788 `movq %r9, %rax`
    .test "%r10" (.reg "%r10"),  -- l.3789 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%r11"),  -- l.3790 `cmovneq %r11, %rax`
    .storeMem "%rsp" 208 (.reg "%rax"),  -- l.3791 `movq %rax, 208(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3792 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3793 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.3794 `movq %r8, %rax`
    .test "%r10" (.reg "%r10"),  -- l.3795 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rcx"),  -- l.3796 `cmovneq %rcx, %rax`
    .storeMem "%rsp" 216 (.reg "%rax"),  -- l.3797 `movq %rax, 216(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3798 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.3799 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rax"),  -- l.3800 `movq %rax, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.3801 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rsi"),  -- l.3802 `cmovneq %rsi, %rbx`
    .storeMem "%rsp" 224 (.reg "%rbx"),  -- l.3803 `movq %rbx, 224(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.3804 `movq -128(%rsp), %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3805 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.3806 `movq %rbx, %rax`
    .test "%r10" (.reg "%r10"),  -- l.3807 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rdi"),  -- l.3808 `cmovneq %rdi, %rax`
    .storeMem "%rsp" 304 (.reg "%rax"),  -- l.3809 `movq %rax, 304(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3810 `movq -128(%rsp), %rax`
    .mov "%rbx" (.imm 0),  -- l.3811 `movq $0, %rbx`
    .mov "%rsi" (.imm 0),  -- l.3812 `movl $0, %esi`
    .loadMem "%rdi" "%rsp" 296,  -- l.3813 `movq 296(%rsp), %rdi`
    .loadMem "%r15" "%rsp" 264,  -- l.3814 `movq 264(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.3815 `imulq %r15, %rdi`
    .loadMem "%rdx" "%rsp" 296,  -- l.3816 `movq 296(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 264,  -- l.3817 `movq 264(%rsp), %r14`
    .mulx "%r8" "%rdi" (.reg "%rdx") (.reg "%r14"),  -- l.3818 `mulx %r14, %rdi, %r8`
    .bt "%rsi" (.imm 0) ]  -- l.3819 `btq $0, %rsi`

/-- Segment 108 of the body: the 32 instructions from source lines 3820–3854. -/
def ed25519PointAddShippedSeg108 : List (JInstr 64) :=
  [ .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3820 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.3821 `movq %rdi, %rax`
    .adcx "%rax" (.reg "%rbx"),  -- l.3822 `adcxq %rbx, %rax`
    .storeMem "%rsp" 168 (.reg "%rax"),  -- l.3823 `movq %rax, 168(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3824 `movq -128(%rsp), %rax`
    .setc "%r11",  -- l.3825 `setc %r11b; movzbq %r11b, %r11`
    .loadMem "%rsi" "%rsp" 312,  -- l.3827 `movq 312(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 264,  -- l.3828 `movq 264(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.3829 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 312,  -- l.3830 `movq 312(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 264,  -- l.3831 `movq 264(%rsp), %r14`
    .mulx "%rdi" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3832 `mulx %r14, %rsi, %rdi`
    .mov "%r12" (.reg "%rsi"),  -- l.3833 `movq %rsi, %r12`
    .bt "%r11" (.imm 0),  -- l.3834 `btq $0, %r11`
    .adcx "%r12" (.reg "%r8"),  -- l.3835 `adcxq %r8, %r12`
    .setc "%r13",  -- l.3836 `setc %r13b; movzbq %r13b, %r13`
    .loadMem "%rsi" "%rsp" 320,  -- l.3838 `movq 320(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 264,  -- l.3839 `movq 264(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.3840 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 320,  -- l.3841 `movq 320(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 264,  -- l.3842 `movq 264(%rsp), %r14`
    .mulx "%r8" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3843 `mulx %r14, %rsi, %r8`
    .mov "%r11" (.reg "%rsi"),  -- l.3844 `movq %rsi, %r11`
    .bt "%r13" (.imm 0),  -- l.3845 `btq $0, %r13`
    .adcx "%r11" (.reg "%rdi"),  -- l.3846 `adcxq %rdi, %r11`
    .setc "%rax",  -- l.3847 `setc %al; movzbq %al, %rax`
    .loadMem "%rsi" "%rsp" 328,  -- l.3849 `movq 328(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 264,  -- l.3850 `movq 264(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.3851 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 328,  -- l.3852 `movq 328(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 264,  -- l.3853 `movq 264(%rsp), %r14`
    .mulx "%rdi" "%rsi" (.reg "%rdx") (.reg "%r14") ]  -- l.3854 `mulx %r14, %rsi, %rdi`

/-- Segment 109 of the body: the 32 instructions from source lines 3855–3888. -/
def ed25519PointAddShippedSeg109 : List (JInstr 64) :=
  [ .mov "%r13" (.reg "%rsi"),  -- l.3855 `movq %rsi, %r13`
    .bt "%rax" (.imm 0),  -- l.3856 `btq $0, %rax`
    .adcx "%r13" (.reg "%r8"),  -- l.3857 `adcxq %r8, %r13`
    .setc "%rcx",  -- l.3858 `setc %cl; movzbq %cl, %rcx`
    .bt "%rcx" (.imm 0),  -- l.3860 `btq $0, %rcx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3861 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.3862 `movq %rdi, %rax`
    .adcx "%rax" (.reg "%rbx"),  -- l.3863 `adcxq %rbx, %rax`
    .storeMem "%rsp" 160 (.reg "%rax"),  -- l.3864 `movq %rax, 160(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3865 `movq -128(%rsp), %rax`
    .mov "%rbx" (.imm 0),  -- l.3866 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.3867 `movl $0, %ecx`
    .loadMem "%rsi" "%rsp" 296,  -- l.3868 `movq 296(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 272,  -- l.3869 `movq 272(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.3870 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 296,  -- l.3871 `movq 296(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 272,  -- l.3872 `movq 272(%rsp), %r14`
    .mulx "%rdi" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.3873 `mulx %r14, %rsi, %rdi`
    .mov "%r8" (.reg "%rsi"),  -- l.3874 `movq %rsi, %r8`
    .bt "%rcx" (.imm 0),  -- l.3875 `btq $0, %rcx`
    .adcx "%r8" (.reg "%rbx"),  -- l.3876 `adcxq %rbx, %r8`
    .setc "%r9",  -- l.3877 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rcx" "%rsp" 312,  -- l.3879 `movq 312(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 272,  -- l.3880 `movq 272(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3881 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 312,  -- l.3882 `movq 312(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 272,  -- l.3883 `movq 272(%rsp), %r14`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3884 `mulx %r14, %rcx, %rsi`
    .mov "%rbp" (.reg "%rcx"),  -- l.3885 `movq %rcx, %rbp`
    .bt "%r9" (.imm 0),  -- l.3886 `btq $0, %r9`
    .adcx "%rbp" (.reg "%rdi"),  -- l.3887 `adcxq %rdi, %rbp`
    .setc "%r10" ]  -- l.3888 `setc %r10b; movzbq %r10b, %r10`

/-- Segment 110 of the body: the 32 instructions from source lines 3890–3923. -/
def ed25519PointAddShippedSeg110 : List (JInstr 64) :=
  [ .loadMem "%rcx" "%rsp" 320,  -- l.3890 `movq 320(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 272,  -- l.3891 `movq 272(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3892 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 320,  -- l.3893 `movq 320(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 272,  -- l.3894 `movq 272(%rsp), %r14`
    .mulx "%rdi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3895 `mulx %r14, %rcx, %rdi`
    .mov "%r9" (.reg "%rcx"),  -- l.3896 `movq %rcx, %r9`
    .bt "%r10" (.imm 0),  -- l.3897 `btq $0, %r10`
    .adcx "%r9" (.reg "%rsi"),  -- l.3898 `adcxq %rsi, %r9`
    .setc "%rax",  -- l.3899 `setc %al; movzbq %al, %rax`
    .loadMem "%rcx" "%rsp" 328,  -- l.3901 `movq 328(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 272,  -- l.3902 `movq 272(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.3903 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 328,  -- l.3904 `movq 328(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 272,  -- l.3905 `movq 272(%rsp), %r14`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.3906 `mulx %r14, %rcx, %rsi`
    .bt "%rax" (.imm 0),  -- l.3907 `btq $0, %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.3908 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rcx"),  -- l.3909 `movq %rcx, %rbx`
    .adcx "%rbx" (.reg "%rdi"),  -- l.3910 `adcxq %rdi, %rbx`
    .storeMem "%rsp" 152 (.reg "%rbx"),  -- l.3911 `movq %rbx, 152(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.3912 `movq -128(%rsp), %rbx`
    .setc "%r10",  -- l.3913 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.reg "%rsi"),  -- l.3915 `movq %rsi, %rax`
    .bt "%r10" (.imm 0),  -- l.3916 `btq $0, %r10`
    .adcx "%rax" (.reg "%rbx"),  -- l.3917 `adcxq %rbx, %rax`
    .mov "%rbx" (.imm 0),  -- l.3918 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.3919 `movl $0, %ecx`
    .bt "%rcx" (.imm 0),  -- l.3920 `btq $0, %rcx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3921 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r12"),  -- l.3922 `movq %r12, %rax`
    .adcx "%rax" (.reg "%r8") ]  -- l.3923 `adcxq %r8, %rax`

/-- Segment 111 of the body: the 32 instructions from source lines 3924–3960. -/
def ed25519PointAddShippedSeg111 : List (JInstr 64) :=
  [ .storeMem "%rsp" 144 (.reg "%rax"),  -- l.3924 `movq %rax, 144(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3925 `movq -128(%rsp), %rax`
    .setc "%rdi",  -- l.3926 `setc %dil; movzbq %dil, %rdi`
    .mov "%rcx" (.reg "%r11"),  -- l.3928 `movq %r11, %rcx`
    .bt "%rdi" (.imm 0),  -- l.3929 `btq $0, %rdi`
    .adcx "%rcx" (.reg "%rbp"),  -- l.3930 `adcxq %rbp, %rcx`
    .setc "%r8",  -- l.3931 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rdi" (.reg "%r13"),  -- l.3933 `movq %r13, %rdi`
    .bt "%r8" (.imm 0),  -- l.3934 `btq $0, %r8`
    .adcx "%rdi" (.reg "%r9"),  -- l.3935 `adcxq %r9, %rdi`
    .setc "%rbp",  -- l.3936 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%r8" "%rsp" 160,  -- l.3938 `movq 160(%rsp), %r8`
    .bt "%rbp" (.imm 0),  -- l.3939 `btq $0, %rbp`
    .adcxMem "%r8" "%rsp" 152,  -- l.3940 `adcxq 152(%rsp), %r8`
    .setc "%r9",  -- l.3941 `setc %r9b; movzbq %r9b, %r9`
    .bt "%r9" (.imm 0),  -- l.3943 `btq $0, %r9`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.3944 `movq %rcx, -128(%rsp)`
    .mov "%rcx" (.reg "%rbx"),  -- l.3945 `movq %rbx, %rcx`
    .adcx "%rcx" (.reg "%rax"),  -- l.3946 `adcxq %rax, %rcx`
    .storeMem "%rsp" 160 (.reg "%rcx"),  -- l.3947 `movq %rcx, 160(%rsp)`
    .loadMem "%rcx" "%rsp" (-128),  -- l.3948 `movq -128(%rsp), %rcx`
    .setc "%r10",  -- l.3949 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 0),  -- l.3951 `movq $0, %rax`
    .mov "%rbx" (.imm 0),  -- l.3952 `movl $0, %ebx`
    .loadMem "%r9" "%rsp" 296,  -- l.3953 `movq 296(%rsp), %r9`
    .loadMem "%r15" "%rsp" 280,  -- l.3954 `movq 280(%rsp), %r15`
    .imul "%r9" (.reg "%r15"),  -- l.3955 `imulq %r15, %r9`
    .loadMem "%rdx" "%rsp" 296,  -- l.3956 `movq 296(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 280,  -- l.3957 `movq 280(%rsp), %r14`
    .mulx "%r10" "%r9" (.reg "%rdx") (.reg "%r14"),  -- l.3958 `mulx %r14, %r9, %r10`
    .mov "%r11" (.reg "%r9"),  -- l.3959 `movq %r9, %r11`
    .bt "%rbx" (.imm 0) ]  -- l.3960 `btq $0, %rbx`

/-- Segment 112 of the body: the 32 instructions from source lines 3961–3995. -/
def ed25519PointAddShippedSeg112 : List (JInstr 64) :=
  [ .adcx "%r11" (.reg "%rax"),  -- l.3961 `adcxq %rax, %r11`
    .setc "%r12",  -- l.3962 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rbx" "%rsp" 312,  -- l.3964 `movq 312(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 280,  -- l.3965 `movq 280(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.3966 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 312,  -- l.3967 `movq 312(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 280,  -- l.3968 `movq 280(%rsp), %r14`
    .mulx "%r9" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.3969 `mulx %r14, %rbx, %r9`
    .mov "%r13" (.reg "%rbx"),  -- l.3970 `movq %rbx, %r13`
    .bt "%r12" (.imm 0),  -- l.3971 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.3972 `adcxq %r10, %r13`
    .setc "%rsi",  -- l.3973 `setc %sil; movzbq %sil, %rsi`
    .loadMem "%rbx" "%rsp" 320,  -- l.3975 `movq 320(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 280,  -- l.3976 `movq 280(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.3977 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 320,  -- l.3978 `movq 320(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 280,  -- l.3979 `movq 280(%rsp), %r14`
    .mulx "%r10" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.3980 `mulx %r14, %rbx, %r10`
    .mov "%r12" (.reg "%rbx"),  -- l.3981 `movq %rbx, %r12`
    .bt "%rsi" (.imm 0),  -- l.3982 `btq $0, %rsi`
    .adcx "%r12" (.reg "%r9"),  -- l.3983 `adcxq %r9, %r12`
    .setc "%rbp",  -- l.3984 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rbx" "%rsp" 328,  -- l.3986 `movq 328(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 280,  -- l.3987 `movq 280(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.3988 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 328,  -- l.3989 `movq 328(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 280,  -- l.3990 `movq 280(%rsp), %r14`
    .mulx "%rsi" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.3991 `mulx %r14, %rbx, %rsi`
    .bt "%rbp" (.imm 0),  -- l.3992 `btq $0, %rbp`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.3993 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.3994 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%r10") ]  -- l.3995 `adcxq %r10, %rax`

/-- Segment 113 of the body: the 32 instructions from source lines 3996–4032. -/
def ed25519PointAddShippedSeg113 : List (JInstr 64) :=
  [ .storeMem "%rsp" 152 (.reg "%rax"),  -- l.3996 `movq %rax, 152(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.3997 `movq -128(%rsp), %rax`
    .setc "%r9",  -- l.3998 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbx" (.reg "%rsi"),  -- l.4000 `movq %rsi, %rbx`
    .bt "%r9" (.imm 0),  -- l.4001 `btq $0, %r9`
    .adcx "%rbx" (.reg "%rax"),  -- l.4002 `adcxq %rax, %rbx`
    .mov "%rax" (.imm 0),  -- l.4003 `movq $0, %rax`
    .mov "%rsi" (.imm 0),  -- l.4004 `movl $0, %esi`
    .bt "%rsi" (.imm 0),  -- l.4005 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4006 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.4007 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%r11"),  -- l.4008 `adcxq %r11, %rax`
    .storeMem "%rsp" 136 (.reg "%rax"),  -- l.4009 `movq %rax, 136(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4010 `movq -128(%rsp), %rax`
    .setc "%r9",  -- l.4011 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi"),  -- l.4013 `movq %rdi, %rcx`
    .bt "%r9" (.imm 0),  -- l.4014 `btq $0, %r9`
    .adcx "%rcx" (.reg "%r13"),  -- l.4015 `adcxq %r13, %rcx`
    .setc "%rsi",  -- l.4016 `setc %sil; movzbq %sil, %rsi`
    .mov "%rdi" (.reg "%r8"),  -- l.4018 `movq %r8, %rdi`
    .bt "%rsi" (.imm 0),  -- l.4019 `btq $0, %rsi`
    .adcx "%rdi" (.reg "%r12"),  -- l.4020 `adcxq %r12, %rdi`
    .setc "%r9",  -- l.4021 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rsi" "%rsp" 160,  -- l.4023 `movq 160(%rsp), %rsi`
    .bt "%r9" (.imm 0),  -- l.4024 `btq $0, %r9`
    .adcxMem "%rsi" "%rsp" 152,  -- l.4025 `adcxq 152(%rsp), %rsi`
    .setc "%r8",  -- l.4026 `setc %r8b; movzbq %r8b, %r8`
    .bt "%r8" (.imm 0),  -- l.4028 `btq $0, %r8`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.4029 `movq %rcx, -128(%rsp)`
    .mov "%rcx" (.reg "%rax"),  -- l.4030 `movq %rax, %rcx`
    .adcx "%rcx" (.reg "%rbx"),  -- l.4031 `adcxq %rbx, %rcx`
    .storeMem "%rsp" 160 (.reg "%rcx") ]  -- l.4032 `movq %rcx, 160(%rsp)`

/-- Segment 114 of the body: the 32 instructions from source lines 4033–4067. -/
def ed25519PointAddShippedSeg114 : List (JInstr 64) :=
  [ .loadMem "%rcx" "%rsp" (-128),  -- l.4033 `movq -128(%rsp), %rcx`
    .setc "%r10",  -- l.4034 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 0),  -- l.4036 `movq $0, %rax`
    .mov "%rbx" (.imm 0),  -- l.4037 `movl $0, %ebx`
    .loadMem "%r8" "%rsp" 296,  -- l.4038 `movq 296(%rsp), %r8`
    .loadMem "%r15" "%rsp" 288,  -- l.4039 `movq 288(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.4040 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 296,  -- l.4041 `movq 296(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 288,  -- l.4042 `movq 288(%rsp), %r14`
    .mulx "%r10" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.4043 `mulx %r14, %r8, %r10`
    .mov "%r11" (.reg "%r8"),  -- l.4044 `movq %r8, %r11`
    .bt "%rbx" (.imm 0),  -- l.4045 `btq $0, %rbx`
    .adcx "%r11" (.reg "%rax"),  -- l.4046 `adcxq %rax, %r11`
    .setc "%r12",  -- l.4047 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rbx" "%rsp" 312,  -- l.4049 `movq 312(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 288,  -- l.4050 `movq 288(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.4051 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 312,  -- l.4052 `movq 312(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 288,  -- l.4053 `movq 288(%rsp), %r14`
    .mulx "%r8" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.4054 `mulx %r14, %rbx, %r8`
    .mov "%r13" (.reg "%rbx"),  -- l.4055 `movq %rbx, %r13`
    .bt "%r12" (.imm 0),  -- l.4056 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.4057 `adcxq %r10, %r13`
    .setc "%rbp",  -- l.4058 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rbx" "%rsp" 320,  -- l.4060 `movq 320(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 288,  -- l.4061 `movq 288(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.4062 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 320,  -- l.4063 `movq 320(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 288,  -- l.4064 `movq 288(%rsp), %r14`
    .mulx "%r10" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.4065 `mulx %r14, %rbx, %r10`
    .mov "%r12" (.reg "%rbx"),  -- l.4066 `movq %rbx, %r12`
    .bt "%rbp" (.imm 0) ]  -- l.4067 `btq $0, %rbp`

/-- Segment 115 of the body: the 32 instructions from source lines 4068–4103. -/
def ed25519PointAddShippedSeg115 : List (JInstr 64) :=
  [ .adcx "%r12" (.reg "%r8"),  -- l.4068 `adcxq %r8, %r12`
    .setc "%r9",  -- l.4069 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rbx" "%rsp" 328,  -- l.4071 `movq 328(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 288,  -- l.4072 `movq 288(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.4073 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 328,  -- l.4074 `movq 328(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 288,  -- l.4075 `movq 288(%rsp), %r14`
    .mulx "%rbp" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.4076 `mulx %r14, %rbx, %rbp`
    .bt "%r9" (.imm 0),  -- l.4077 `btq $0, %r9`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4078 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.4079 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.4080 `adcxq %r10, %rax`
    .storeMem "%rsp" 152 (.reg "%rax"),  -- l.4081 `movq %rax, 152(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4082 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.4083 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rbx" (.reg "%rbp"),  -- l.4085 `movq %rbp, %rbx`
    .bt "%r8" (.imm 0),  -- l.4086 `btq $0, %r8`
    .adcx "%rbx" (.reg "%rax"),  -- l.4087 `adcxq %rax, %rbx`
    .mov "%rax" (.imm 0),  -- l.4088 `movq $0, %rax`
    .mov "%rbp" (.imm 0),  -- l.4089 `movl $0, %ebp`
    .mov "%r8" (.reg "%rcx"),  -- l.4090 `movq %rcx, %r8`
    .bt "%rbp" (.imm 0),  -- l.4091 `btq $0, %rbp`
    .adcx "%r8" (.reg "%r11"),  -- l.4092 `adcxq %r11, %r8`
    .setc "%r9",  -- l.4093 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi"),  -- l.4095 `movq %rdi, %rcx`
    .bt "%r9" (.imm 0),  -- l.4096 `btq $0, %r9`
    .adcx "%rcx" (.reg "%r13"),  -- l.4097 `adcxq %r13, %rcx`
    .setc "%rbp",  -- l.4098 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.4100 `movq %rsi, %rdi`
    .bt "%rbp" (.imm 0),  -- l.4101 `btq $0, %rbp`
    .adcx "%rdi" (.reg "%r12"),  -- l.4102 `adcxq %r12, %rdi`
    .setc "%r9" ]  -- l.4103 `setc %r9b; movzbq %r9b, %r9`

/-- Segment 116 of the body: the 32 instructions from source lines 4105–4140. -/
def ed25519PointAddShippedSeg116 : List (JInstr 64) :=
  [ .loadMem "%rsi" "%rsp" 160,  -- l.4105 `movq 160(%rsp), %rsi`
    .bt "%r9" (.imm 0),  -- l.4106 `btq $0, %r9`
    .adcxMem "%rsi" "%rsp" 152,  -- l.4107 `adcxq 152(%rsp), %rsi`
    .setc "%rbp",  -- l.4108 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%r9" (.reg "%rax"),  -- l.4110 `movq %rax, %r9`
    .bt "%rbp" (.imm 0),  -- l.4111 `btq $0, %rbp`
    .adcx "%r9" (.reg "%rbx"),  -- l.4112 `adcxq %rbx, %r9`
    .setc "%r10",  -- l.4113 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 38),  -- l.4115 `movq $38, %rax`
    .mov "%rbx" (.imm 0),  -- l.4116 `movq $0, %rbx`
    .mov "%rbp" (.imm 0),  -- l.4117 `movl $0, %ebp`
    .mov "%r10" (.reg "%rcx"),  -- l.4118 `movq %rcx, %r10`
    .imul "%r10" (.reg "%rax"),  -- l.4119 `imulq %rax, %r10`
    .mov "%rdx" (.reg "%rcx"),  -- l.4120 `movq %rcx, %rdx`
    .mulx "%r11" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.4121 `mulx %rax, %r10, %r11`
    .mov "%rcx" (.reg "%r10"),  -- l.4122 `movq %r10, %rcx`
    .bt "%rbp" (.imm 0),  -- l.4123 `btq $0, %rbp`
    .adcx "%rcx" (.reg "%rbx"),  -- l.4124 `adcxq %rbx, %rcx`
    .setc "%r12",  -- l.4125 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rdi"),  -- l.4127 `movq %rdi, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.4128 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%rdi"),  -- l.4129 `movq %rdi, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.4130 `mulx %rax, %rbp, %r10`
    .mov "%rdi" (.reg "%rbp"),  -- l.4131 `movq %rbp, %rdi`
    .bt "%r12" (.imm 0),  -- l.4132 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r11"),  -- l.4133 `adcxq %r11, %rdi`
    .setc "%r13",  -- l.4134 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%rsi"),  -- l.4136 `movq %rsi, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.4137 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%rsi"),  -- l.4138 `movq %rsi, %rdx`
    .mulx "%r11" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.4139 `mulx %rax, %rbp, %r11`
    .mov "%rsi" (.reg "%rbp") ]  -- l.4140 `movq %rbp, %rsi`

/-- Segment 117 of the body: the 32 instructions from source lines 4141–4177. -/
def ed25519PointAddShippedSeg117 : List (JInstr 64) :=
  [ .bt "%r13" (.imm 0),  -- l.4141 `btq $0, %r13`
    .adcx "%rsi" (.reg "%r10"),  -- l.4142 `adcxq %r10, %rsi`
    .setc "%r12",  -- l.4143 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%r9"),  -- l.4145 `movq %r9, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.4146 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%r9"),  -- l.4147 `movq %r9, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.4148 `mulx %rax, %rbp, %r10`
    .mov "%r9" (.reg "%rbp"),  -- l.4149 `movq %rbp, %r9`
    .bt "%r12" (.imm 0),  -- l.4150 `btq $0, %r12`
    .adcx "%r9" (.reg "%r11"),  -- l.4151 `adcxq %r11, %r9`
    .setc "%r13",  -- l.4152 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%r10"),  -- l.4154 `movq %r10, %rbp`
    .bt "%r13" (.imm 0),  -- l.4155 `btq $0, %r13`
    .adcx "%rbp" (.reg "%rbx"),  -- l.4156 `adcxq %rbx, %rbp`
    .mov "%rbx" (.imm 0),  -- l.4157 `movq $0, %rbx`
    .mov "%r10" (.imm 0),  -- l.4158 `movl $0, %r10d`
    .loadMem "%r11" "%rsp" 168,  -- l.4159 `movq 168(%rsp), %r11`
    .bt "%r10" (.imm 0),  -- l.4160 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.4161 `adcxq %rcx, %r11`
    .setc "%r12",  -- l.4162 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rcx" "%rsp" 144,  -- l.4164 `movq 144(%rsp), %rcx`
    .bt "%r12" (.imm 0),  -- l.4165 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rdi"),  -- l.4166 `adcxq %rdi, %rcx`
    .setc "%r10",  -- l.4167 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rdi" "%rsp" 136,  -- l.4169 `movq 136(%rsp), %rdi`
    .bt "%r10" (.imm 0),  -- l.4170 `btq $0, %r10`
    .adcx "%rdi" (.reg "%rsi"),  -- l.4171 `adcxq %rsi, %rdi`
    .setc "%r12",  -- l.4172 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rsi" (.reg "%r8"),  -- l.4174 `movq %r8, %rsi`
    .bt "%r12" (.imm 0),  -- l.4175 `btq $0, %r12`
    .adcx "%rsi" (.reg "%r9"),  -- l.4176 `adcxq %r9, %rsi`
    .setc "%r10" ]  -- l.4177 `setc %r10b; movzbq %r10b, %r10`

/-- Segment 118 of the body: the 32 instructions from source lines 4179–4215. -/
def ed25519PointAddShippedSeg118 : List (JInstr 64) :=
  [ .mov "%r8" (.reg "%rbx"),  -- l.4179 `movq %rbx, %r8`
    .bt "%r10" (.imm 0),  -- l.4180 `btq $0, %r10`
    .adcx "%r8" (.reg "%rbp"),  -- l.4181 `adcxq %rbp, %r8`
    .setc "%r9",  -- l.4182 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbp" (.imm 0),  -- l.4184 `movq $0, %rbp`
    .mov "%r9" (.imm 0),  -- l.4185 `movl $0, %r9d`
    .mov "%r10" (.reg "%r8"),  -- l.4186 `movq %r8, %r10`
    .imul "%r10" (.reg "%rax"),  -- l.4187 `imulq %rax, %r10`
    .mov "%rdx" (.reg "%r8"),  -- l.4188 `movq %r8, %rdx`
    .mulx "%r12" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.4189 `mulx %rax, %r10, %r12`
    .mov "%r8" (.reg "%r10"),  -- l.4190 `movq %r10, %r8`
    .bt "%r9" (.imm 0),  -- l.4191 `btq $0, %r9`
    .adcx "%r8" (.reg "%rbp"),  -- l.4192 `adcxq %rbp, %r8`
    .setc "%r13",  -- l.4193 `setc %r13b; movzbq %r13b, %r13`
    .mov "%r9" (.reg "%r12"),  -- l.4195 `movq %r12, %r9`
    .bt "%r13" (.imm 0),  -- l.4196 `btq $0, %r13`
    .adcx "%r9" (.reg "%rbp"),  -- l.4197 `adcxq %rbp, %r9`
    .mov "%rbp" (.imm 0),  -- l.4198 `movl $0, %ebp`
    .mov "%r10" (.reg "%r11"),  -- l.4199 `movq %r11, %r10`
    .bt "%rbp" (.imm 0),  -- l.4200 `btq $0, %rbp`
    .adcx "%r10" (.reg "%r8"),  -- l.4201 `adcxq %r8, %r10`
    .setc "%r12",  -- l.4202 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rcx"),  -- l.4204 `movq %rcx, %rbp`
    .bt "%r12" (.imm 0),  -- l.4205 `btq $0, %r12`
    .adcx "%rbp" (.reg "%r9"),  -- l.4206 `adcxq %r9, %rbp`
    .setc "%r8",  -- l.4207 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rcx" (.reg "%rdi"),  -- l.4209 `movq %rdi, %rcx`
    .bt "%r8" (.imm 0),  -- l.4210 `btq $0, %r8`
    .adcx "%rcx" (.reg "%rbx"),  -- l.4211 `adcxq %rbx, %rcx`
    .setc "%r9",  -- l.4212 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rdi" (.reg "%rsi"),  -- l.4214 `movq %rsi, %rdi`
    .bt "%r9" (.imm 0) ]  -- l.4215 `btq $0, %r9`

/-- Segment 119 of the body: the 32 instructions from source lines 4216–4253. -/
def ed25519PointAddShippedSeg119 : List (JInstr 64) :=
  [ .adcx "%rdi" (.reg "%rbx"),  -- l.4216 `adcxq %rbx, %rdi`
    .setc "%r8",  -- l.4217 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rsi" (.reg "%rbx"),  -- l.4219 `movq %rbx, %rsi`
    .test "%r8" (.reg "%r8"),  -- l.4220 `testq %r8, %r8`
    .cmovne "%rsi" (.reg "%rax"),  -- l.4221 `cmovneq %rax, %rsi`
    .mov "%rax" (.imm 0),  -- l.4222 `movl $0, %eax`
    .mov "%r8" (.reg "%r10"),  -- l.4223 `movq %r10, %r8`
    .bt "%rax" (.imm 0),  -- l.4224 `btq $0, %rax`
    .adcx "%r8" (.reg "%rsi"),  -- l.4225 `adcxq %rsi, %r8`
    .setc "%r9",  -- l.4226 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rbp"),  -- l.4228 `movq %rbp, %rax`
    .bt "%r9" (.imm 0),  -- l.4229 `btq $0, %r9`
    .adcx "%rax" (.reg "%rbx"),  -- l.4230 `adcxq %rbx, %rax`
    .setc "%rsi",  -- l.4231 `setc %sil; movzbq %sil, %rsi`
    .mov "%rbp" (.reg "%rcx"),  -- l.4233 `movq %rcx, %rbp`
    .bt "%rsi" (.imm 0),  -- l.4234 `btq $0, %rsi`
    .adcx "%rbp" (.reg "%rbx"),  -- l.4235 `adcxq %rbx, %rbp`
    .setc "%r9",  -- l.4236 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi"),  -- l.4238 `movq %rdi, %rcx`
    .bt "%r9" (.imm 0),  -- l.4239 `btq $0, %r9`
    .adcx "%rcx" (.reg "%rbx"),  -- l.4240 `adcxq %rbx, %rcx`
    .setc "%rsi",  -- l.4241 `setc %sil; movzbq %sil, %rsi`
    .mov "%rbx" (.imm 19),  -- l.4243 `movq $19, %rbx`
    .mov "%rsi" (.imm 0),  -- l.4244 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.4245 `movq $0, %rdi`
    .mov "%r9" (.imm 9223372036854775808),  -- l.4246 `movq $9223372036854775808, %r9`
    .mov "%r10" (.imm 0),  -- l.4247 `movl $0, %r10d`
    .mov "%r11" (.reg "%r8"),  -- l.4248 `movq %r8, %r11`
    .bt "%r10" (.imm 0),  -- l.4249 `btq $0, %r10`
    .adcx "%r11" (.reg "%rbx"),  -- l.4250 `adcxq %rbx, %r11`
    .setc "%r12",  -- l.4251 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbx" (.reg "%rax") ]  -- l.4253 `movq %rax, %rbx`

/-- Segment 120 of the body: the 32 instructions from source lines 4254–4288. -/
def ed25519PointAddShippedSeg120 : List (JInstr 64) :=
  [ .bt "%r12" (.imm 0),  -- l.4254 `btq $0, %r12`
    .adcx "%rbx" (.reg "%rsi"),  -- l.4255 `adcxq %rsi, %rbx`
    .setc "%r10",  -- l.4256 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rbp"),  -- l.4258 `movq %rbp, %rsi`
    .bt "%r10" (.imm 0),  -- l.4259 `btq $0, %r10`
    .adcx "%rsi" (.reg "%rdi"),  -- l.4260 `adcxq %rdi, %rsi`
    .setc "%r12",  -- l.4261 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rcx"),  -- l.4263 `movq %rcx, %rdi`
    .bt "%r12" (.imm 0),  -- l.4264 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.4265 `adcxq %r9, %rdi`
    .setc "%r10",  -- l.4266 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%r8"),  -- l.4268 `movq %r8, %r9`
    .test "%r10" (.reg "%r10"),  -- l.4269 `testq %r10, %r10`
    .cmovne "%r9" (.reg "%r11"),  -- l.4270 `cmovneq %r11, %r9`
    .mov "%r8" (.reg "%rax"),  -- l.4271 `movq %rax, %r8`
    .test "%r10" (.reg "%r10"),  -- l.4272 `testq %r10, %r10`
    .cmovne "%r8" (.reg "%rbx"),  -- l.4273 `cmovneq %rbx, %r8`
    .mov "%rax" (.reg "%rbp"),  -- l.4274 `movq %rbp, %rax`
    .test "%r10" (.reg "%r10"),  -- l.4275 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rsi"),  -- l.4276 `cmovneq %rsi, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.4277 `movq %rcx, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.4278 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rdi"),  -- l.4279 `cmovneq %rdi, %rbx`
    .mov "%rcx" (.imm 19),  -- l.4280 `movq $19, %rcx`
    .mov "%rsi" (.imm 0),  -- l.4281 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.4282 `movq $0, %rdi`
    .mov "%rbp" (.imm 9223372036854775808),  -- l.4283 `movq $9223372036854775808, %rbp`
    .mov "%r10" (.imm 0),  -- l.4284 `movl $0, %r10d`
    .mov "%r11" (.reg "%r9"),  -- l.4285 `movq %r9, %r11`
    .bt "%r10" (.imm 0),  -- l.4286 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.4287 `adcxq %rcx, %r11`
    .setc "%r12" ]  -- l.4288 `setc %r12b; movzbq %r12b, %r12`

/-- Segment 121 of the body: the 32 instructions from source lines 4290–4324. -/
def ed25519PointAddShippedSeg121 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%r8"),  -- l.4290 `movq %r8, %rcx`
    .bt "%r12" (.imm 0),  -- l.4291 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rsi"),  -- l.4292 `adcxq %rsi, %rcx`
    .setc "%r10",  -- l.4293 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rax"),  -- l.4295 `movq %rax, %rsi`
    .bt "%r10" (.imm 0),  -- l.4296 `btq $0, %r10`
    .adcx "%rsi" (.reg "%rdi"),  -- l.4297 `adcxq %rdi, %rsi`
    .setc "%r12",  -- l.4298 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rbx"),  -- l.4300 `movq %rbx, %rdi`
    .bt "%r12" (.imm 0),  -- l.4301 `btq $0, %r12`
    .adcx "%rdi" (.reg "%rbp"),  -- l.4302 `adcxq %rbp, %rdi`
    .setc "%r10",  -- l.4303 `setc %r10b; movzbq %r10b, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4305 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r9"),  -- l.4306 `movq %r9, %rax`
    .test "%r10" (.reg "%r10"),  -- l.4307 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%r11"),  -- l.4308 `cmovneq %r11, %rax`
    .storeMem "%rsp" 144 (.reg "%rax"),  -- l.4309 `movq %rax, 144(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4310 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4311 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r8"),  -- l.4312 `movq %r8, %rax`
    .test "%r10" (.reg "%r10"),  -- l.4313 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rcx"),  -- l.4314 `cmovneq %rcx, %rax`
    .storeMem "%rsp" 152 (.reg "%rax"),  -- l.4315 `movq %rax, 152(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4316 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.4317 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rax"),  -- l.4318 `movq %rax, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.4319 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rsi"),  -- l.4320 `cmovneq %rsi, %rbx`
    .storeMem "%rsp" 160 (.reg "%rbx"),  -- l.4321 `movq %rbx, 160(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.4322 `movq -128(%rsp), %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4323 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx") ]  -- l.4324 `movq %rbx, %rax`

/-- Segment 122 of the body: the 32 instructions from source lines 4325–4358. -/
def ed25519PointAddShippedSeg122 : List (JInstr 64) :=
  [ .test "%r10" (.reg "%r10"),  -- l.4325 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rdi"),  -- l.4326 `cmovneq %rdi, %rax`
    .storeMem "%rsp" 168 (.reg "%rax"),  -- l.4327 `movq %rax, 168(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4328 `movq -128(%rsp), %rax`
    .mov "%rbx" (.imm 0),  -- l.4329 `movq $0, %rbx`
    .mov "%rsi" (.imm 0),  -- l.4330 `movl $0, %esi`
    .loadMem "%rdi" "%rsp" 232,  -- l.4331 `movq 232(%rsp), %rdi`
    .loadMem "%r15" "%rsp" 264,  -- l.4332 `movq 264(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.4333 `imulq %r15, %rdi`
    .loadMem "%rdx" "%rsp" 232,  -- l.4334 `movq 232(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 264,  -- l.4335 `movq 264(%rsp), %r14`
    .mulx "%r8" "%rdi" (.reg "%rdx") (.reg "%r14"),  -- l.4336 `mulx %r14, %rdi, %r8`
    .bt "%rsi" (.imm 0),  -- l.4337 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4338 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.4339 `movq %rdi, %rax`
    .adcx "%rax" (.reg "%rbx"),  -- l.4340 `adcxq %rbx, %rax`
    .storeMem "%rsp" 136 (.reg "%rax"),  -- l.4341 `movq %rax, 136(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4342 `movq -128(%rsp), %rax`
    .setc "%r11",  -- l.4343 `setc %r11b; movzbq %r11b, %r11`
    .loadMem "%rsi" "%rsp" 240,  -- l.4345 `movq 240(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 264,  -- l.4346 `movq 264(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.4347 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 240,  -- l.4348 `movq 240(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 264,  -- l.4349 `movq 264(%rsp), %r14`
    .mulx "%rdi" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.4350 `mulx %r14, %rsi, %rdi`
    .mov "%r12" (.reg "%rsi"),  -- l.4351 `movq %rsi, %r12`
    .bt "%r11" (.imm 0),  -- l.4352 `btq $0, %r11`
    .adcx "%r12" (.reg "%r8"),  -- l.4353 `adcxq %r8, %r12`
    .setc "%r13",  -- l.4354 `setc %r13b; movzbq %r13b, %r13`
    .loadMem "%rsi" "%rsp" 248,  -- l.4356 `movq 248(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 264,  -- l.4357 `movq 264(%rsp), %r15`
    .imul "%rsi" (.reg "%r15") ]  -- l.4358 `imulq %r15, %rsi`

/-- Segment 123 of the body: the 32 instructions from source lines 4359–4392. -/
def ed25519PointAddShippedSeg123 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsp" 248,  -- l.4359 `movq 248(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 264,  -- l.4360 `movq 264(%rsp), %r14`
    .mulx "%r8" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.4361 `mulx %r14, %rsi, %r8`
    .mov "%r11" (.reg "%rsi"),  -- l.4362 `movq %rsi, %r11`
    .bt "%r13" (.imm 0),  -- l.4363 `btq $0, %r13`
    .adcx "%r11" (.reg "%rdi"),  -- l.4364 `adcxq %rdi, %r11`
    .setc "%rax",  -- l.4365 `setc %al; movzbq %al, %rax`
    .loadMem "%rsi" "%rsp" 256,  -- l.4367 `movq 256(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 264,  -- l.4368 `movq 264(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.4369 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 256,  -- l.4370 `movq 256(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 264,  -- l.4371 `movq 264(%rsp), %r14`
    .mulx "%rdi" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.4372 `mulx %r14, %rsi, %rdi`
    .mov "%r13" (.reg "%rsi"),  -- l.4373 `movq %rsi, %r13`
    .bt "%rax" (.imm 0),  -- l.4374 `btq $0, %rax`
    .adcx "%r13" (.reg "%r8"),  -- l.4375 `adcxq %r8, %r13`
    .setc "%rcx",  -- l.4376 `setc %cl; movzbq %cl, %rcx`
    .bt "%rcx" (.imm 0),  -- l.4378 `btq $0, %rcx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4379 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.4380 `movq %rdi, %rax`
    .adcx "%rax" (.reg "%rbx"),  -- l.4381 `adcxq %rbx, %rax`
    .storeMem "%rsp" 264 (.reg "%rax"),  -- l.4382 `movq %rax, 264(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4383 `movq -128(%rsp), %rax`
    .mov "%rbx" (.imm 0),  -- l.4384 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.4385 `movl $0, %ecx`
    .loadMem "%rsi" "%rsp" 232,  -- l.4386 `movq 232(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 272,  -- l.4387 `movq 272(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.4388 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 232,  -- l.4389 `movq 232(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 272,  -- l.4390 `movq 272(%rsp), %r14`
    .mulx "%rdi" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.4391 `mulx %r14, %rsi, %rdi`
    .mov "%r8" (.reg "%rsi") ]  -- l.4392 `movq %rsi, %r8`

/-- Segment 124 of the body: the 32 instructions from source lines 4393–4427. -/
def ed25519PointAddShippedSeg124 : List (JInstr 64) :=
  [ .bt "%rcx" (.imm 0),  -- l.4393 `btq $0, %rcx`
    .adcx "%r8" (.reg "%rbx"),  -- l.4394 `adcxq %rbx, %r8`
    .setc "%r9",  -- l.4395 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rcx" "%rsp" 240,  -- l.4397 `movq 240(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 272,  -- l.4398 `movq 272(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.4399 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 240,  -- l.4400 `movq 240(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 272,  -- l.4401 `movq 272(%rsp), %r14`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.4402 `mulx %r14, %rcx, %rsi`
    .mov "%rbp" (.reg "%rcx"),  -- l.4403 `movq %rcx, %rbp`
    .bt "%r9" (.imm 0),  -- l.4404 `btq $0, %r9`
    .adcx "%rbp" (.reg "%rdi"),  -- l.4405 `adcxq %rdi, %rbp`
    .setc "%r10",  -- l.4406 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rcx" "%rsp" 248,  -- l.4408 `movq 248(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 272,  -- l.4409 `movq 272(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.4410 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 248,  -- l.4411 `movq 248(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 272,  -- l.4412 `movq 272(%rsp), %r14`
    .mulx "%rdi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.4413 `mulx %r14, %rcx, %rdi`
    .mov "%r9" (.reg "%rcx"),  -- l.4414 `movq %rcx, %r9`
    .bt "%r10" (.imm 0),  -- l.4415 `btq $0, %r10`
    .adcx "%r9" (.reg "%rsi"),  -- l.4416 `adcxq %rsi, %r9`
    .setc "%rax",  -- l.4417 `setc %al; movzbq %al, %rax`
    .loadMem "%rcx" "%rsp" 256,  -- l.4419 `movq 256(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 272,  -- l.4420 `movq 272(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.4421 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 256,  -- l.4422 `movq 256(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 272,  -- l.4423 `movq 272(%rsp), %r14`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.4424 `mulx %r14, %rcx, %rsi`
    .bt "%rax" (.imm 0),  -- l.4425 `btq $0, %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.4426 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rcx") ]  -- l.4427 `movq %rcx, %rbx`

/-- Segment 125 of the body: the 32 instructions from source lines 4428–4464. -/
def ed25519PointAddShippedSeg125 : List (JInstr 64) :=
  [ .adcx "%rbx" (.reg "%rdi"),  -- l.4428 `adcxq %rdi, %rbx`
    .storeMem "%rsp" 272 (.reg "%rbx"),  -- l.4429 `movq %rbx, 272(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.4430 `movq -128(%rsp), %rbx`
    .setc "%r10",  -- l.4431 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.reg "%rsi"),  -- l.4433 `movq %rsi, %rax`
    .bt "%r10" (.imm 0),  -- l.4434 `btq $0, %r10`
    .adcx "%rax" (.reg "%rbx"),  -- l.4435 `adcxq %rbx, %rax`
    .mov "%rbx" (.imm 0),  -- l.4436 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.4437 `movl $0, %ecx`
    .bt "%rcx" (.imm 0),  -- l.4438 `btq $0, %rcx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4439 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r12"),  -- l.4440 `movq %r12, %rax`
    .adcx "%rax" (.reg "%r8"),  -- l.4441 `adcxq %r8, %rax`
    .storeMem "%rsp" 128 (.reg "%rax"),  -- l.4442 `movq %rax, 128(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4443 `movq -128(%rsp), %rax`
    .setc "%rdi",  -- l.4444 `setc %dil; movzbq %dil, %rdi`
    .mov "%rcx" (.reg "%r11"),  -- l.4446 `movq %r11, %rcx`
    .bt "%rdi" (.imm 0),  -- l.4447 `btq $0, %rdi`
    .adcx "%rcx" (.reg "%rbp"),  -- l.4448 `adcxq %rbp, %rcx`
    .setc "%r8",  -- l.4449 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rdi" (.reg "%r13"),  -- l.4451 `movq %r13, %rdi`
    .bt "%r8" (.imm 0),  -- l.4452 `btq $0, %r8`
    .adcx "%rdi" (.reg "%r9"),  -- l.4453 `adcxq %r9, %rdi`
    .setc "%rbp",  -- l.4454 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%r8" "%rsp" 264,  -- l.4456 `movq 264(%rsp), %r8`
    .bt "%rbp" (.imm 0),  -- l.4457 `btq $0, %rbp`
    .adcxMem "%r8" "%rsp" 272,  -- l.4458 `adcxq 272(%rsp), %r8`
    .setc "%r9",  -- l.4459 `setc %r9b; movzbq %r9b, %r9`
    .bt "%r9" (.imm 0),  -- l.4461 `btq $0, %r9`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.4462 `movq %rcx, -128(%rsp)`
    .mov "%rcx" (.reg "%rbx"),  -- l.4463 `movq %rbx, %rcx`
    .adcx "%rcx" (.reg "%rax") ]  -- l.4464 `adcxq %rax, %rcx`

/-- Segment 126 of the body: the 32 instructions from source lines 4465–4499. -/
def ed25519PointAddShippedSeg126 : List (JInstr 64) :=
  [ .storeMem "%rsp" 272 (.reg "%rcx"),  -- l.4465 `movq %rcx, 272(%rsp)`
    .loadMem "%rcx" "%rsp" (-128),  -- l.4466 `movq -128(%rsp), %rcx`
    .setc "%r10",  -- l.4467 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 0),  -- l.4469 `movq $0, %rax`
    .mov "%rbx" (.imm 0),  -- l.4470 `movl $0, %ebx`
    .loadMem "%r9" "%rsp" 232,  -- l.4471 `movq 232(%rsp), %r9`
    .loadMem "%r15" "%rsp" 280,  -- l.4472 `movq 280(%rsp), %r15`
    .imul "%r9" (.reg "%r15"),  -- l.4473 `imulq %r15, %r9`
    .loadMem "%rdx" "%rsp" 232,  -- l.4474 `movq 232(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 280,  -- l.4475 `movq 280(%rsp), %r14`
    .mulx "%r10" "%r9" (.reg "%rdx") (.reg "%r14"),  -- l.4476 `mulx %r14, %r9, %r10`
    .mov "%r11" (.reg "%r9"),  -- l.4477 `movq %r9, %r11`
    .bt "%rbx" (.imm 0),  -- l.4478 `btq $0, %rbx`
    .adcx "%r11" (.reg "%rax"),  -- l.4479 `adcxq %rax, %r11`
    .setc "%r12",  -- l.4480 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rbx" "%rsp" 240,  -- l.4482 `movq 240(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 280,  -- l.4483 `movq 280(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.4484 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 240,  -- l.4485 `movq 240(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 280,  -- l.4486 `movq 280(%rsp), %r14`
    .mulx "%r9" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.4487 `mulx %r14, %rbx, %r9`
    .mov "%r13" (.reg "%rbx"),  -- l.4488 `movq %rbx, %r13`
    .bt "%r12" (.imm 0),  -- l.4489 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.4490 `adcxq %r10, %r13`
    .setc "%rsi",  -- l.4491 `setc %sil; movzbq %sil, %rsi`
    .loadMem "%rbx" "%rsp" 248,  -- l.4493 `movq 248(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 280,  -- l.4494 `movq 280(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.4495 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 248,  -- l.4496 `movq 248(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 280,  -- l.4497 `movq 280(%rsp), %r14`
    .mulx "%r10" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.4498 `mulx %r14, %rbx, %r10`
    .mov "%r12" (.reg "%rbx") ]  -- l.4499 `movq %rbx, %r12`

/-- Segment 127 of the body: the 32 instructions from source lines 4500–4534. -/
def ed25519PointAddShippedSeg127 : List (JInstr 64) :=
  [ .bt "%rsi" (.imm 0),  -- l.4500 `btq $0, %rsi`
    .adcx "%r12" (.reg "%r9"),  -- l.4501 `adcxq %r9, %r12`
    .setc "%rbp",  -- l.4502 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rbx" "%rsp" 256,  -- l.4504 `movq 256(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 280,  -- l.4505 `movq 280(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.4506 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 256,  -- l.4507 `movq 256(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 280,  -- l.4508 `movq 280(%rsp), %r14`
    .mulx "%rsi" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.4509 `mulx %r14, %rbx, %rsi`
    .bt "%rbp" (.imm 0),  -- l.4510 `btq $0, %rbp`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4511 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.4512 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.4513 `adcxq %r10, %rax`
    .storeMem "%rsp" 280 (.reg "%rax"),  -- l.4514 `movq %rax, 280(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4515 `movq -128(%rsp), %rax`
    .setc "%r9",  -- l.4516 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbx" (.reg "%rsi"),  -- l.4518 `movq %rsi, %rbx`
    .bt "%r9" (.imm 0),  -- l.4519 `btq $0, %r9`
    .adcx "%rbx" (.reg "%rax"),  -- l.4520 `adcxq %rax, %rbx`
    .mov "%rax" (.imm 0),  -- l.4521 `movq $0, %rax`
    .mov "%rsi" (.imm 0),  -- l.4522 `movl $0, %esi`
    .bt "%rsi" (.imm 0),  -- l.4523 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4524 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.4525 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%r11"),  -- l.4526 `adcxq %r11, %rax`
    .storeMem "%rsp" 264 (.reg "%rax"),  -- l.4527 `movq %rax, 264(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4528 `movq -128(%rsp), %rax`
    .setc "%r9",  -- l.4529 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi"),  -- l.4531 `movq %rdi, %rcx`
    .bt "%r9" (.imm 0),  -- l.4532 `btq $0, %r9`
    .adcx "%rcx" (.reg "%r13"),  -- l.4533 `adcxq %r13, %rcx`
    .setc "%rsi" ]  -- l.4534 `setc %sil; movzbq %sil, %rsi`

/-- Segment 128 of the body: the 32 instructions from source lines 4536–4571. -/
def ed25519PointAddShippedSeg128 : List (JInstr 64) :=
  [ .mov "%rdi" (.reg "%r8"),  -- l.4536 `movq %r8, %rdi`
    .bt "%rsi" (.imm 0),  -- l.4537 `btq $0, %rsi`
    .adcx "%rdi" (.reg "%r12"),  -- l.4538 `adcxq %r12, %rdi`
    .setc "%r9",  -- l.4539 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rsi" "%rsp" 272,  -- l.4541 `movq 272(%rsp), %rsi`
    .bt "%r9" (.imm 0),  -- l.4542 `btq $0, %r9`
    .adcxMem "%rsi" "%rsp" 280,  -- l.4543 `adcxq 280(%rsp), %rsi`
    .setc "%r8",  -- l.4544 `setc %r8b; movzbq %r8b, %r8`
    .bt "%r8" (.imm 0),  -- l.4546 `btq $0, %r8`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.4547 `movq %rcx, -128(%rsp)`
    .mov "%rcx" (.reg "%rax"),  -- l.4548 `movq %rax, %rcx`
    .adcx "%rcx" (.reg "%rbx"),  -- l.4549 `adcxq %rbx, %rcx`
    .storeMem "%rsp" 280 (.reg "%rcx"),  -- l.4550 `movq %rcx, 280(%rsp)`
    .loadMem "%rcx" "%rsp" (-128),  -- l.4551 `movq -128(%rsp), %rcx`
    .setc "%r10",  -- l.4552 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 0),  -- l.4554 `movq $0, %rax`
    .mov "%rbx" (.imm 0),  -- l.4555 `movl $0, %ebx`
    .loadMem "%r8" "%rsp" 232,  -- l.4556 `movq 232(%rsp), %r8`
    .loadMem "%r15" "%rsp" 288,  -- l.4557 `movq 288(%rsp), %r15`
    .imul "%r8" (.reg "%r15"),  -- l.4558 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 232,  -- l.4559 `movq 232(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 288,  -- l.4560 `movq 288(%rsp), %r14`
    .mulx "%r10" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.4561 `mulx %r14, %r8, %r10`
    .mov "%r11" (.reg "%r8"),  -- l.4562 `movq %r8, %r11`
    .bt "%rbx" (.imm 0),  -- l.4563 `btq $0, %rbx`
    .adcx "%r11" (.reg "%rax"),  -- l.4564 `adcxq %rax, %r11`
    .setc "%r12",  -- l.4565 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rbx" "%rsp" 240,  -- l.4567 `movq 240(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 288,  -- l.4568 `movq 288(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.4569 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 240,  -- l.4570 `movq 240(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 288 ]  -- l.4571 `movq 288(%rsp), %r14`

/-- Segment 129 of the body: the 32 instructions from source lines 4572–4606. -/
def ed25519PointAddShippedSeg129 : List (JInstr 64) :=
  [ .mulx "%r8" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.4572 `mulx %r14, %rbx, %r8`
    .mov "%r13" (.reg "%rbx"),  -- l.4573 `movq %rbx, %r13`
    .bt "%r12" (.imm 0),  -- l.4574 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.4575 `adcxq %r10, %r13`
    .setc "%rbp",  -- l.4576 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rbx" "%rsp" 248,  -- l.4578 `movq 248(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 288,  -- l.4579 `movq 288(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.4580 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 248,  -- l.4581 `movq 248(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 288,  -- l.4582 `movq 288(%rsp), %r14`
    .mulx "%r10" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.4583 `mulx %r14, %rbx, %r10`
    .mov "%r12" (.reg "%rbx"),  -- l.4584 `movq %rbx, %r12`
    .bt "%rbp" (.imm 0),  -- l.4585 `btq $0, %rbp`
    .adcx "%r12" (.reg "%r8"),  -- l.4586 `adcxq %r8, %r12`
    .setc "%r9",  -- l.4587 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rbx" "%rsp" 256,  -- l.4589 `movq 256(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 288,  -- l.4590 `movq 288(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.4591 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 256,  -- l.4592 `movq 256(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 288,  -- l.4593 `movq 288(%rsp), %r14`
    .mulx "%rbp" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.4594 `mulx %r14, %rbx, %rbp`
    .bt "%r9" (.imm 0),  -- l.4595 `btq $0, %r9`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4596 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.4597 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.4598 `adcxq %r10, %rax`
    .storeMem "%rsp" 288 (.reg "%rax"),  -- l.4599 `movq %rax, 288(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4600 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.4601 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rbx" (.reg "%rbp"),  -- l.4603 `movq %rbp, %rbx`
    .bt "%r8" (.imm 0),  -- l.4604 `btq $0, %r8`
    .adcx "%rbx" (.reg "%rax"),  -- l.4605 `adcxq %rax, %rbx`
    .mov "%rax" (.imm 0) ]  -- l.4606 `movq $0, %rax`

/-- Segment 130 of the body: the 32 instructions from source lines 4607–4643. -/
def ed25519PointAddShippedSeg130 : List (JInstr 64) :=
  [ .mov "%rbp" (.imm 0),  -- l.4607 `movl $0, %ebp`
    .mov "%r8" (.reg "%rcx"),  -- l.4608 `movq %rcx, %r8`
    .bt "%rbp" (.imm 0),  -- l.4609 `btq $0, %rbp`
    .adcx "%r8" (.reg "%r11"),  -- l.4610 `adcxq %r11, %r8`
    .setc "%r9",  -- l.4611 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi"),  -- l.4613 `movq %rdi, %rcx`
    .bt "%r9" (.imm 0),  -- l.4614 `btq $0, %r9`
    .adcx "%rcx" (.reg "%r13"),  -- l.4615 `adcxq %r13, %rcx`
    .setc "%rbp",  -- l.4616 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.4618 `movq %rsi, %rdi`
    .bt "%rbp" (.imm 0),  -- l.4619 `btq $0, %rbp`
    .adcx "%rdi" (.reg "%r12"),  -- l.4620 `adcxq %r12, %rdi`
    .setc "%r9",  -- l.4621 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rsi" "%rsp" 280,  -- l.4623 `movq 280(%rsp), %rsi`
    .bt "%r9" (.imm 0),  -- l.4624 `btq $0, %r9`
    .adcxMem "%rsi" "%rsp" 288,  -- l.4625 `adcxq 288(%rsp), %rsi`
    .setc "%rbp",  -- l.4626 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%r9" (.reg "%rax"),  -- l.4628 `movq %rax, %r9`
    .bt "%rbp" (.imm 0),  -- l.4629 `btq $0, %rbp`
    .adcx "%r9" (.reg "%rbx"),  -- l.4630 `adcxq %rbx, %r9`
    .setc "%r10",  -- l.4631 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 38),  -- l.4633 `movq $38, %rax`
    .mov "%rbx" (.imm 0),  -- l.4634 `movq $0, %rbx`
    .mov "%rbp" (.imm 0),  -- l.4635 `movl $0, %ebp`
    .mov "%r10" (.reg "%rcx"),  -- l.4636 `movq %rcx, %r10`
    .imul "%r10" (.reg "%rax"),  -- l.4637 `imulq %rax, %r10`
    .mov "%rdx" (.reg "%rcx"),  -- l.4638 `movq %rcx, %rdx`
    .mulx "%r11" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.4639 `mulx %rax, %r10, %r11`
    .mov "%rcx" (.reg "%r10"),  -- l.4640 `movq %r10, %rcx`
    .bt "%rbp" (.imm 0),  -- l.4641 `btq $0, %rbp`
    .adcx "%rcx" (.reg "%rbx"),  -- l.4642 `adcxq %rbx, %rcx`
    .setc "%r12" ]  -- l.4643 `setc %r12b; movzbq %r12b, %r12`

/-- Segment 131 of the body: the 32 instructions from source lines 4645–4679. -/
def ed25519PointAddShippedSeg131 : List (JInstr 64) :=
  [ .mov "%rbp" (.reg "%rdi"),  -- l.4645 `movq %rdi, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.4646 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%rdi"),  -- l.4647 `movq %rdi, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.4648 `mulx %rax, %rbp, %r10`
    .mov "%rdi" (.reg "%rbp"),  -- l.4649 `movq %rbp, %rdi`
    .bt "%r12" (.imm 0),  -- l.4650 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r11"),  -- l.4651 `adcxq %r11, %rdi`
    .setc "%r13",  -- l.4652 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%rsi"),  -- l.4654 `movq %rsi, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.4655 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%rsi"),  -- l.4656 `movq %rsi, %rdx`
    .mulx "%r11" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.4657 `mulx %rax, %rbp, %r11`
    .mov "%rsi" (.reg "%rbp"),  -- l.4658 `movq %rbp, %rsi`
    .bt "%r13" (.imm 0),  -- l.4659 `btq $0, %r13`
    .adcx "%rsi" (.reg "%r10"),  -- l.4660 `adcxq %r10, %rsi`
    .setc "%r12",  -- l.4661 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%r9"),  -- l.4663 `movq %r9, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.4664 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%r9"),  -- l.4665 `movq %r9, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.4666 `mulx %rax, %rbp, %r10`
    .mov "%r9" (.reg "%rbp"),  -- l.4667 `movq %rbp, %r9`
    .bt "%r12" (.imm 0),  -- l.4668 `btq $0, %r12`
    .adcx "%r9" (.reg "%r11"),  -- l.4669 `adcxq %r11, %r9`
    .setc "%r13",  -- l.4670 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%r10"),  -- l.4672 `movq %r10, %rbp`
    .bt "%r13" (.imm 0),  -- l.4673 `btq $0, %r13`
    .adcx "%rbp" (.reg "%rbx"),  -- l.4674 `adcxq %rbx, %rbp`
    .mov "%rbx" (.imm 0),  -- l.4675 `movq $0, %rbx`
    .mov "%r10" (.imm 0),  -- l.4676 `movl $0, %r10d`
    .loadMem "%r11" "%rsp" 136,  -- l.4677 `movq 136(%rsp), %r11`
    .bt "%r10" (.imm 0),  -- l.4678 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx") ]  -- l.4679 `adcxq %rcx, %r11`

/-- Segment 132 of the body: the 32 instructions from source lines 4680–4717. -/
def ed25519PointAddShippedSeg132 : List (JInstr 64) :=
  [ .setc "%r12",  -- l.4680 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rcx" "%rsp" 128,  -- l.4682 `movq 128(%rsp), %rcx`
    .bt "%r12" (.imm 0),  -- l.4683 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rdi"),  -- l.4684 `adcxq %rdi, %rcx`
    .setc "%r10",  -- l.4685 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rdi" "%rsp" 264,  -- l.4687 `movq 264(%rsp), %rdi`
    .bt "%r10" (.imm 0),  -- l.4688 `btq $0, %r10`
    .adcx "%rdi" (.reg "%rsi"),  -- l.4689 `adcxq %rsi, %rdi`
    .setc "%r12",  -- l.4690 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rsi" (.reg "%r8"),  -- l.4692 `movq %r8, %rsi`
    .bt "%r12" (.imm 0),  -- l.4693 `btq $0, %r12`
    .adcx "%rsi" (.reg "%r9"),  -- l.4694 `adcxq %r9, %rsi`
    .setc "%r10",  -- l.4695 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r8" (.reg "%rbx"),  -- l.4697 `movq %rbx, %r8`
    .bt "%r10" (.imm 0),  -- l.4698 `btq $0, %r10`
    .adcx "%r8" (.reg "%rbp"),  -- l.4699 `adcxq %rbp, %r8`
    .setc "%r9",  -- l.4700 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbp" (.imm 0),  -- l.4702 `movq $0, %rbp`
    .mov "%r9" (.imm 0),  -- l.4703 `movl $0, %r9d`
    .mov "%r10" (.reg "%r8"),  -- l.4704 `movq %r8, %r10`
    .imul "%r10" (.reg "%rax"),  -- l.4705 `imulq %rax, %r10`
    .mov "%rdx" (.reg "%r8"),  -- l.4706 `movq %r8, %rdx`
    .mulx "%r12" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.4707 `mulx %rax, %r10, %r12`
    .mov "%r8" (.reg "%r10"),  -- l.4708 `movq %r10, %r8`
    .bt "%r9" (.imm 0),  -- l.4709 `btq $0, %r9`
    .adcx "%r8" (.reg "%rbp"),  -- l.4710 `adcxq %rbp, %r8`
    .setc "%r13",  -- l.4711 `setc %r13b; movzbq %r13b, %r13`
    .mov "%r9" (.reg "%r12"),  -- l.4713 `movq %r12, %r9`
    .bt "%r13" (.imm 0),  -- l.4714 `btq $0, %r13`
    .adcx "%r9" (.reg "%rbp"),  -- l.4715 `adcxq %rbp, %r9`
    .mov "%rbp" (.imm 0),  -- l.4716 `movl $0, %ebp`
    .mov "%r10" (.reg "%r11") ]  -- l.4717 `movq %r11, %r10`

/-- Segment 133 of the body: the 32 instructions from source lines 4718–4756. -/
def ed25519PointAddShippedSeg133 : List (JInstr 64) :=
  [ .bt "%rbp" (.imm 0),  -- l.4718 `btq $0, %rbp`
    .adcx "%r10" (.reg "%r8"),  -- l.4719 `adcxq %r8, %r10`
    .setc "%r12",  -- l.4720 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rcx"),  -- l.4722 `movq %rcx, %rbp`
    .bt "%r12" (.imm 0),  -- l.4723 `btq $0, %r12`
    .adcx "%rbp" (.reg "%r9"),  -- l.4724 `adcxq %r9, %rbp`
    .setc "%r8",  -- l.4725 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rcx" (.reg "%rdi"),  -- l.4727 `movq %rdi, %rcx`
    .bt "%r8" (.imm 0),  -- l.4728 `btq $0, %r8`
    .adcx "%rcx" (.reg "%rbx"),  -- l.4729 `adcxq %rbx, %rcx`
    .setc "%r9",  -- l.4730 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rdi" (.reg "%rsi"),  -- l.4732 `movq %rsi, %rdi`
    .bt "%r9" (.imm 0),  -- l.4733 `btq $0, %r9`
    .adcx "%rdi" (.reg "%rbx"),  -- l.4734 `adcxq %rbx, %rdi`
    .setc "%r8",  -- l.4735 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rsi" (.reg "%rbx"),  -- l.4737 `movq %rbx, %rsi`
    .test "%r8" (.reg "%r8"),  -- l.4738 `testq %r8, %r8`
    .cmovne "%rsi" (.reg "%rax"),  -- l.4739 `cmovneq %rax, %rsi`
    .mov "%rax" (.imm 0),  -- l.4740 `movl $0, %eax`
    .mov "%r8" (.reg "%r10"),  -- l.4741 `movq %r10, %r8`
    .bt "%rax" (.imm 0),  -- l.4742 `btq $0, %rax`
    .adcx "%r8" (.reg "%rsi"),  -- l.4743 `adcxq %rsi, %r8`
    .setc "%r9",  -- l.4744 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rbp"),  -- l.4746 `movq %rbp, %rax`
    .bt "%r9" (.imm 0),  -- l.4747 `btq $0, %r9`
    .adcx "%rax" (.reg "%rbx"),  -- l.4748 `adcxq %rbx, %rax`
    .setc "%rsi",  -- l.4749 `setc %sil; movzbq %sil, %rsi`
    .mov "%rbp" (.reg "%rcx"),  -- l.4751 `movq %rcx, %rbp`
    .bt "%rsi" (.imm 0),  -- l.4752 `btq $0, %rsi`
    .adcx "%rbp" (.reg "%rbx"),  -- l.4753 `adcxq %rbx, %rbp`
    .setc "%r9",  -- l.4754 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi") ]  -- l.4756 `movq %rdi, %rcx`

/-- Segment 134 of the body: the 32 instructions from source lines 4757–4793. -/
def ed25519PointAddShippedSeg134 : List (JInstr 64) :=
  [ .bt "%r9" (.imm 0),  -- l.4757 `btq $0, %r9`
    .adcx "%rcx" (.reg "%rbx"),  -- l.4758 `adcxq %rbx, %rcx`
    .setc "%rsi",  -- l.4759 `setc %sil; movzbq %sil, %rsi`
    .mov "%rbx" (.imm 19),  -- l.4761 `movq $19, %rbx`
    .mov "%rsi" (.imm 0),  -- l.4762 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.4763 `movq $0, %rdi`
    .mov "%r9" (.imm 9223372036854775808),  -- l.4764 `movq $9223372036854775808, %r9`
    .mov "%r10" (.imm 0),  -- l.4765 `movl $0, %r10d`
    .mov "%r11" (.reg "%r8"),  -- l.4766 `movq %r8, %r11`
    .bt "%r10" (.imm 0),  -- l.4767 `btq $0, %r10`
    .adcx "%r11" (.reg "%rbx"),  -- l.4768 `adcxq %rbx, %r11`
    .setc "%r12",  -- l.4769 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbx" (.reg "%rax"),  -- l.4771 `movq %rax, %rbx`
    .bt "%r12" (.imm 0),  -- l.4772 `btq $0, %r12`
    .adcx "%rbx" (.reg "%rsi"),  -- l.4773 `adcxq %rsi, %rbx`
    .setc "%r10",  -- l.4774 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rbp"),  -- l.4776 `movq %rbp, %rsi`
    .bt "%r10" (.imm 0),  -- l.4777 `btq $0, %r10`
    .adcx "%rsi" (.reg "%rdi"),  -- l.4778 `adcxq %rdi, %rsi`
    .setc "%r12",  -- l.4779 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rcx"),  -- l.4781 `movq %rcx, %rdi`
    .bt "%r12" (.imm 0),  -- l.4782 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.4783 `adcxq %r9, %rdi`
    .setc "%r10",  -- l.4784 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%r8"),  -- l.4786 `movq %r8, %r9`
    .test "%r10" (.reg "%r10"),  -- l.4787 `testq %r10, %r10`
    .cmovne "%r9" (.reg "%r11"),  -- l.4788 `cmovneq %r11, %r9`
    .mov "%r8" (.reg "%rax"),  -- l.4789 `movq %rax, %r8`
    .test "%r10" (.reg "%r10"),  -- l.4790 `testq %r10, %r10`
    .cmovne "%r8" (.reg "%rbx"),  -- l.4791 `cmovneq %rbx, %r8`
    .mov "%rax" (.reg "%rbp"),  -- l.4792 `movq %rbp, %rax`
    .test "%r10" (.reg "%r10") ]  -- l.4793 `testq %r10, %r10`

/-- Segment 135 of the body: the 32 instructions from source lines 4794–4829. -/
def ed25519PointAddShippedSeg135 : List (JInstr 64) :=
  [ .cmovne "%rax" (.reg "%rsi"),  -- l.4794 `cmovneq %rsi, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.4795 `movq %rcx, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.4796 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rdi"),  -- l.4797 `cmovneq %rdi, %rbx`
    .mov "%rcx" (.imm 19),  -- l.4798 `movq $19, %rcx`
    .mov "%rsi" (.imm 0),  -- l.4799 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.4800 `movq $0, %rdi`
    .mov "%rbp" (.imm 9223372036854775808),  -- l.4801 `movq $9223372036854775808, %rbp`
    .mov "%r10" (.imm 0),  -- l.4802 `movl $0, %r10d`
    .mov "%r11" (.reg "%r9"),  -- l.4803 `movq %r9, %r11`
    .bt "%r10" (.imm 0),  -- l.4804 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.4805 `adcxq %rcx, %r11`
    .setc "%r12",  -- l.4806 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rcx" (.reg "%r8"),  -- l.4808 `movq %r8, %rcx`
    .bt "%r12" (.imm 0),  -- l.4809 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rsi"),  -- l.4810 `adcxq %rsi, %rcx`
    .setc "%r10",  -- l.4811 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rax"),  -- l.4813 `movq %rax, %rsi`
    .bt "%r10" (.imm 0),  -- l.4814 `btq $0, %r10`
    .adcx "%rsi" (.reg "%rdi"),  -- l.4815 `adcxq %rdi, %rsi`
    .setc "%r12",  -- l.4816 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rbx"),  -- l.4818 `movq %rbx, %rdi`
    .bt "%r12" (.imm 0),  -- l.4819 `btq $0, %r12`
    .adcx "%rdi" (.reg "%rbp"),  -- l.4820 `adcxq %rbp, %rdi`
    .setc "%r10",  -- l.4821 `setc %r10b; movzbq %r10b, %r10`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4823 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r9"),  -- l.4824 `movq %r9, %rax`
    .test "%r10" (.reg "%r10"),  -- l.4825 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%r11"),  -- l.4826 `cmovneq %r11, %rax`
    .storeMem "%rsp" 264 (.reg "%rax"),  -- l.4827 `movq %rax, 264(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4828 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rax") ]  -- l.4829 `movq %rax, -128(%rsp)`

/-- Segment 136 of the body: the 32 instructions from source lines 4830–4861. -/
def ed25519PointAddShippedSeg136 : List (JInstr 64) :=
  [ .mov "%rax" (.reg "%r8"),  -- l.4830 `movq %r8, %rax`
    .test "%r10" (.reg "%r10"),  -- l.4831 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rcx"),  -- l.4832 `cmovneq %rcx, %rax`
    .storeMem "%rsp" 272 (.reg "%rax"),  -- l.4833 `movq %rax, 272(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4834 `movq -128(%rsp), %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.4835 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rax"),  -- l.4836 `movq %rax, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.4837 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rsi"),  -- l.4838 `cmovneq %rsi, %rbx`
    .storeMem "%rsp" 280 (.reg "%rbx"),  -- l.4839 `movq %rbx, 280(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.4840 `movq -128(%rsp), %rbx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4841 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.4842 `movq %rbx, %rax`
    .test "%r10" (.reg "%r10"),  -- l.4843 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rdi"),  -- l.4844 `cmovneq %rdi, %rax`
    .storeMem "%rsp" 288 (.reg "%rax"),  -- l.4845 `movq %rax, 288(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4846 `movq -128(%rsp), %rax`
    .mov "%rbx" (.imm 0),  -- l.4847 `movq $0, %rbx`
    .mov "%rsi" (.imm 0),  -- l.4848 `movl $0, %esi`
    .loadMem "%rdi" "%rsp" 176,  -- l.4849 `movq 176(%rsp), %rdi`
    .loadMem "%r15" "%rsp" 296,  -- l.4850 `movq 296(%rsp), %r15`
    .imul "%rdi" (.reg "%r15"),  -- l.4851 `imulq %r15, %rdi`
    .loadMem "%rdx" "%rsp" 176,  -- l.4852 `movq 176(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 296,  -- l.4853 `movq 296(%rsp), %r14`
    .mulx "%r8" "%rdi" (.reg "%rdx") (.reg "%r14"),  -- l.4854 `mulx %r14, %rdi, %r8`
    .bt "%rsi" (.imm 0),  -- l.4855 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4856 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rdi"),  -- l.4857 `movq %rdi, %rax`
    .adcx "%rax" (.reg "%rbx"),  -- l.4858 `adcxq %rbx, %rax`
    .storeMem "%rsp" 256 (.reg "%rax"),  -- l.4859 `movq %rax, 256(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4860 `movq -128(%rsp), %rax`
    .setc "%r11" ]  -- l.4861 `setc %r11b; movzbq %r11b, %r11`

/-- Segment 137 of the body: the 32 instructions from source lines 4863–4897. -/
def ed25519PointAddShippedSeg137 : List (JInstr 64) :=
  [ .loadMem "%rsi" "%rsp" 184,  -- l.4863 `movq 184(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 296,  -- l.4864 `movq 296(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.4865 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 184,  -- l.4866 `movq 184(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 296,  -- l.4867 `movq 296(%rsp), %r14`
    .mulx "%rdi" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.4868 `mulx %r14, %rsi, %rdi`
    .mov "%r12" (.reg "%rsi"),  -- l.4869 `movq %rsi, %r12`
    .bt "%r11" (.imm 0),  -- l.4870 `btq $0, %r11`
    .adcx "%r12" (.reg "%r8"),  -- l.4871 `adcxq %r8, %r12`
    .setc "%r13",  -- l.4872 `setc %r13b; movzbq %r13b, %r13`
    .loadMem "%rsi" "%rsp" 192,  -- l.4874 `movq 192(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 296,  -- l.4875 `movq 296(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.4876 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 192,  -- l.4877 `movq 192(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 296,  -- l.4878 `movq 296(%rsp), %r14`
    .mulx "%r8" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.4879 `mulx %r14, %rsi, %r8`
    .mov "%r11" (.reg "%rsi"),  -- l.4880 `movq %rsi, %r11`
    .bt "%r13" (.imm 0),  -- l.4881 `btq $0, %r13`
    .adcx "%r11" (.reg "%rdi"),  -- l.4882 `adcxq %rdi, %r11`
    .setc "%rax",  -- l.4883 `setc %al; movzbq %al, %rax`
    .loadMem "%rsi" "%rsp" 200,  -- l.4885 `movq 200(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 296,  -- l.4886 `movq 296(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.4887 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 200,  -- l.4888 `movq 200(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 296,  -- l.4889 `movq 296(%rsp), %r14`
    .mulx "%rdi" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.4890 `mulx %r14, %rsi, %rdi`
    .mov "%r13" (.reg "%rsi"),  -- l.4891 `movq %rsi, %r13`
    .bt "%rax" (.imm 0),  -- l.4892 `btq $0, %rax`
    .adcx "%r13" (.reg "%r8"),  -- l.4893 `adcxq %r8, %r13`
    .setc "%rcx",  -- l.4894 `setc %cl; movzbq %cl, %rcx`
    .bt "%rcx" (.imm 0),  -- l.4896 `btq $0, %rcx`
    .storeMem "%rsp" (-128) (.reg "%rax") ]  -- l.4897 `movq %rax, -128(%rsp)`

/-- Segment 138 of the body: the 32 instructions from source lines 4898–4931. -/
def ed25519PointAddShippedSeg138 : List (JInstr 64) :=
  [ .mov "%rax" (.reg "%rdi"),  -- l.4898 `movq %rdi, %rax`
    .adcx "%rax" (.reg "%rbx"),  -- l.4899 `adcxq %rbx, %rax`
    .storeMem "%rsp" 296 (.reg "%rax"),  -- l.4900 `movq %rax, 296(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4901 `movq -128(%rsp), %rax`
    .mov "%rbx" (.imm 0),  -- l.4902 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.4903 `movl $0, %ecx`
    .loadMem "%rsi" "%rsp" 176,  -- l.4904 `movq 176(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 312,  -- l.4905 `movq 312(%rsp), %r15`
    .imul "%rsi" (.reg "%r15"),  -- l.4906 `imulq %r15, %rsi`
    .loadMem "%rdx" "%rsp" 176,  -- l.4907 `movq 176(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 312,  -- l.4908 `movq 312(%rsp), %r14`
    .mulx "%rdi" "%rsi" (.reg "%rdx") (.reg "%r14"),  -- l.4909 `mulx %r14, %rsi, %rdi`
    .mov "%r8" (.reg "%rsi"),  -- l.4910 `movq %rsi, %r8`
    .bt "%rcx" (.imm 0),  -- l.4911 `btq $0, %rcx`
    .adcx "%r8" (.reg "%rbx"),  -- l.4912 `adcxq %rbx, %r8`
    .setc "%r9",  -- l.4913 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rcx" "%rsp" 184,  -- l.4915 `movq 184(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 312,  -- l.4916 `movq 312(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.4917 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 184,  -- l.4918 `movq 184(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 312,  -- l.4919 `movq 312(%rsp), %r14`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.4920 `mulx %r14, %rcx, %rsi`
    .mov "%rbp" (.reg "%rcx"),  -- l.4921 `movq %rcx, %rbp`
    .bt "%r9" (.imm 0),  -- l.4922 `btq $0, %r9`
    .adcx "%rbp" (.reg "%rdi"),  -- l.4923 `adcxq %rdi, %rbp`
    .setc "%r10",  -- l.4924 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rcx" "%rsp" 192,  -- l.4926 `movq 192(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 312,  -- l.4927 `movq 312(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.4928 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 192,  -- l.4929 `movq 192(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 312,  -- l.4930 `movq 312(%rsp), %r14`
    .mulx "%rdi" "%rcx" (.reg "%rdx") (.reg "%r14") ]  -- l.4931 `mulx %r14, %rcx, %rdi`

/-- Segment 139 of the body: the 32 instructions from source lines 4932–4966. -/
def ed25519PointAddShippedSeg139 : List (JInstr 64) :=
  [ .mov "%r9" (.reg "%rcx"),  -- l.4932 `movq %rcx, %r9`
    .bt "%r10" (.imm 0),  -- l.4933 `btq $0, %r10`
    .adcx "%r9" (.reg "%rsi"),  -- l.4934 `adcxq %rsi, %r9`
    .setc "%rax",  -- l.4935 `setc %al; movzbq %al, %rax`
    .loadMem "%rcx" "%rsp" 200,  -- l.4937 `movq 200(%rsp), %rcx`
    .loadMem "%r15" "%rsp" 312,  -- l.4938 `movq 312(%rsp), %r15`
    .imul "%rcx" (.reg "%r15"),  -- l.4939 `imulq %r15, %rcx`
    .loadMem "%rdx" "%rsp" 200,  -- l.4940 `movq 200(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 312,  -- l.4941 `movq 312(%rsp), %r14`
    .mulx "%rsi" "%rcx" (.reg "%rdx") (.reg "%r14"),  -- l.4942 `mulx %r14, %rcx, %rsi`
    .bt "%rax" (.imm 0),  -- l.4943 `btq $0, %rax`
    .storeMem "%rsp" (-128) (.reg "%rbx"),  -- l.4944 `movq %rbx, -128(%rsp)`
    .mov "%rbx" (.reg "%rcx"),  -- l.4945 `movq %rcx, %rbx`
    .adcx "%rbx" (.reg "%rdi"),  -- l.4946 `adcxq %rdi, %rbx`
    .storeMem "%rsp" 312 (.reg "%rbx"),  -- l.4947 `movq %rbx, 312(%rsp)`
    .loadMem "%rbx" "%rsp" (-128),  -- l.4948 `movq -128(%rsp), %rbx`
    .setc "%r10",  -- l.4949 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.reg "%rsi"),  -- l.4951 `movq %rsi, %rax`
    .bt "%r10" (.imm 0),  -- l.4952 `btq $0, %r10`
    .adcx "%rax" (.reg "%rbx"),  -- l.4953 `adcxq %rbx, %rax`
    .mov "%rbx" (.imm 0),  -- l.4954 `movq $0, %rbx`
    .mov "%rcx" (.imm 0),  -- l.4955 `movl $0, %ecx`
    .bt "%rcx" (.imm 0),  -- l.4956 `btq $0, %rcx`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.4957 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%r12"),  -- l.4958 `movq %r12, %rax`
    .adcx "%rax" (.reg "%r8"),  -- l.4959 `adcxq %r8, %rax`
    .storeMem "%rsp" 248 (.reg "%rax"),  -- l.4960 `movq %rax, 248(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.4961 `movq -128(%rsp), %rax`
    .setc "%rdi",  -- l.4962 `setc %dil; movzbq %dil, %rdi`
    .mov "%rcx" (.reg "%r11"),  -- l.4964 `movq %r11, %rcx`
    .bt "%rdi" (.imm 0),  -- l.4965 `btq $0, %rdi`
    .adcx "%rcx" (.reg "%rbp") ]  -- l.4966 `adcxq %rbp, %rcx`

/-- Segment 140 of the body: the 32 instructions from source lines 4967–5003. -/
def ed25519PointAddShippedSeg140 : List (JInstr 64) :=
  [ .setc "%r8",  -- l.4967 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rdi" (.reg "%r13"),  -- l.4969 `movq %r13, %rdi`
    .bt "%r8" (.imm 0),  -- l.4970 `btq $0, %r8`
    .adcx "%rdi" (.reg "%r9"),  -- l.4971 `adcxq %r9, %rdi`
    .setc "%rbp",  -- l.4972 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%r8" "%rsp" 296,  -- l.4974 `movq 296(%rsp), %r8`
    .bt "%rbp" (.imm 0),  -- l.4975 `btq $0, %rbp`
    .adcxMem "%r8" "%rsp" 312,  -- l.4976 `adcxq 312(%rsp), %r8`
    .setc "%r9",  -- l.4977 `setc %r9b; movzbq %r9b, %r9`
    .bt "%r9" (.imm 0),  -- l.4979 `btq $0, %r9`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.4980 `movq %rcx, -128(%rsp)`
    .mov "%rcx" (.reg "%rbx"),  -- l.4981 `movq %rbx, %rcx`
    .adcx "%rcx" (.reg "%rax"),  -- l.4982 `adcxq %rax, %rcx`
    .storeMem "%rsp" 312 (.reg "%rcx"),  -- l.4983 `movq %rcx, 312(%rsp)`
    .loadMem "%rcx" "%rsp" (-128),  -- l.4984 `movq -128(%rsp), %rcx`
    .setc "%r10",  -- l.4985 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 0),  -- l.4987 `movq $0, %rax`
    .mov "%rbx" (.imm 0),  -- l.4988 `movl $0, %ebx`
    .loadMem "%r9" "%rsp" 176,  -- l.4989 `movq 176(%rsp), %r9`
    .loadMem "%r15" "%rsp" 320,  -- l.4990 `movq 320(%rsp), %r15`
    .imul "%r9" (.reg "%r15"),  -- l.4991 `imulq %r15, %r9`
    .loadMem "%rdx" "%rsp" 176,  -- l.4992 `movq 176(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 320,  -- l.4993 `movq 320(%rsp), %r14`
    .mulx "%r10" "%r9" (.reg "%rdx") (.reg "%r14"),  -- l.4994 `mulx %r14, %r9, %r10`
    .mov "%r11" (.reg "%r9"),  -- l.4995 `movq %r9, %r11`
    .bt "%rbx" (.imm 0),  -- l.4996 `btq $0, %rbx`
    .adcx "%r11" (.reg "%rax"),  -- l.4997 `adcxq %rax, %r11`
    .setc "%r12",  -- l.4998 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rbx" "%rsp" 184,  -- l.5000 `movq 184(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 320,  -- l.5001 `movq 320(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.5002 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 184 ]  -- l.5003 `movq 184(%rsp), %rdx`

/-- Segment 141 of the body: the 32 instructions from source lines 5004–5038. -/
def ed25519PointAddShippedSeg141 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 320,  -- l.5004 `movq 320(%rsp), %r14`
    .mulx "%r9" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.5005 `mulx %r14, %rbx, %r9`
    .mov "%r13" (.reg "%rbx"),  -- l.5006 `movq %rbx, %r13`
    .bt "%r12" (.imm 0),  -- l.5007 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.5008 `adcxq %r10, %r13`
    .setc "%rsi",  -- l.5009 `setc %sil; movzbq %sil, %rsi`
    .loadMem "%rbx" "%rsp" 192,  -- l.5011 `movq 192(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 320,  -- l.5012 `movq 320(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.5013 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 192,  -- l.5014 `movq 192(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 320,  -- l.5015 `movq 320(%rsp), %r14`
    .mulx "%r10" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.5016 `mulx %r14, %rbx, %r10`
    .mov "%r12" (.reg "%rbx"),  -- l.5017 `movq %rbx, %r12`
    .bt "%rsi" (.imm 0),  -- l.5018 `btq $0, %rsi`
    .adcx "%r12" (.reg "%r9"),  -- l.5019 `adcxq %r9, %r12`
    .setc "%rbp",  -- l.5020 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rbx" "%rsp" 200,  -- l.5022 `movq 200(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 320,  -- l.5023 `movq 320(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.5024 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 200,  -- l.5025 `movq 200(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 320,  -- l.5026 `movq 320(%rsp), %r14`
    .mulx "%rsi" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.5027 `mulx %r14, %rbx, %rsi`
    .bt "%rbp" (.imm 0),  -- l.5028 `btq $0, %rbp`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.5029 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.5030 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.5031 `adcxq %r10, %rax`
    .storeMem "%rsp" 320 (.reg "%rax"),  -- l.5032 `movq %rax, 320(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.5033 `movq -128(%rsp), %rax`
    .setc "%r9",  -- l.5034 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbx" (.reg "%rsi"),  -- l.5036 `movq %rsi, %rbx`
    .bt "%r9" (.imm 0),  -- l.5037 `btq $0, %r9`
    .adcx "%rbx" (.reg "%rax") ]  -- l.5038 `adcxq %rax, %rbx`

/-- Segment 142 of the body: the 32 instructions from source lines 5039–5075. -/
def ed25519PointAddShippedSeg142 : List (JInstr 64) :=
  [ .mov "%rax" (.imm 0),  -- l.5039 `movq $0, %rax`
    .mov "%rsi" (.imm 0),  -- l.5040 `movl $0, %esi`
    .bt "%rsi" (.imm 0),  -- l.5041 `btq $0, %rsi`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.5042 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rcx"),  -- l.5043 `movq %rcx, %rax`
    .adcx "%rax" (.reg "%r11"),  -- l.5044 `adcxq %r11, %rax`
    .storeMem "%rsp" 296 (.reg "%rax"),  -- l.5045 `movq %rax, 296(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.5046 `movq -128(%rsp), %rax`
    .setc "%r9",  -- l.5047 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi"),  -- l.5049 `movq %rdi, %rcx`
    .bt "%r9" (.imm 0),  -- l.5050 `btq $0, %r9`
    .adcx "%rcx" (.reg "%r13"),  -- l.5051 `adcxq %r13, %rcx`
    .setc "%rsi",  -- l.5052 `setc %sil; movzbq %sil, %rsi`
    .mov "%rdi" (.reg "%r8"),  -- l.5054 `movq %r8, %rdi`
    .bt "%rsi" (.imm 0),  -- l.5055 `btq $0, %rsi`
    .adcx "%rdi" (.reg "%r12"),  -- l.5056 `adcxq %r12, %rdi`
    .setc "%r9",  -- l.5057 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rsi" "%rsp" 312,  -- l.5059 `movq 312(%rsp), %rsi`
    .bt "%r9" (.imm 0),  -- l.5060 `btq $0, %r9`
    .adcxMem "%rsi" "%rsp" 320,  -- l.5061 `adcxq 320(%rsp), %rsi`
    .setc "%r8",  -- l.5062 `setc %r8b; movzbq %r8b, %r8`
    .bt "%r8" (.imm 0),  -- l.5064 `btq $0, %r8`
    .storeMem "%rsp" (-128) (.reg "%rcx"),  -- l.5065 `movq %rcx, -128(%rsp)`
    .mov "%rcx" (.reg "%rax"),  -- l.5066 `movq %rax, %rcx`
    .adcx "%rcx" (.reg "%rbx"),  -- l.5067 `adcxq %rbx, %rcx`
    .storeMem "%rsp" 320 (.reg "%rcx"),  -- l.5068 `movq %rcx, 320(%rsp)`
    .loadMem "%rcx" "%rsp" (-128),  -- l.5069 `movq -128(%rsp), %rcx`
    .setc "%r10",  -- l.5070 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 0),  -- l.5072 `movq $0, %rax`
    .mov "%rbx" (.imm 0),  -- l.5073 `movl $0, %ebx`
    .loadMem "%r8" "%rsp" 176,  -- l.5074 `movq 176(%rsp), %r8`
    .loadMem "%r15" "%rsp" 328 ]  -- l.5075 `movq 328(%rsp), %r15`

/-- Segment 143 of the body: the 32 instructions from source lines 5076–5110. -/
def ed25519PointAddShippedSeg143 : List (JInstr 64) :=
  [ .imul "%r8" (.reg "%r15"),  -- l.5076 `imulq %r15, %r8`
    .loadMem "%rdx" "%rsp" 176,  -- l.5077 `movq 176(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 328,  -- l.5078 `movq 328(%rsp), %r14`
    .mulx "%r10" "%r8" (.reg "%rdx") (.reg "%r14"),  -- l.5079 `mulx %r14, %r8, %r10`
    .mov "%r11" (.reg "%r8"),  -- l.5080 `movq %r8, %r11`
    .bt "%rbx" (.imm 0),  -- l.5081 `btq $0, %rbx`
    .adcx "%r11" (.reg "%rax"),  -- l.5082 `adcxq %rax, %r11`
    .setc "%r12",  -- l.5083 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rbx" "%rsp" 184,  -- l.5085 `movq 184(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 328,  -- l.5086 `movq 328(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.5087 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 184,  -- l.5088 `movq 184(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 328,  -- l.5089 `movq 328(%rsp), %r14`
    .mulx "%r8" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.5090 `mulx %r14, %rbx, %r8`
    .mov "%r13" (.reg "%rbx"),  -- l.5091 `movq %rbx, %r13`
    .bt "%r12" (.imm 0),  -- l.5092 `btq $0, %r12`
    .adcx "%r13" (.reg "%r10"),  -- l.5093 `adcxq %r10, %r13`
    .setc "%rbp",  -- l.5094 `setc %bpl; movzbq %bpl, %rbp`
    .loadMem "%rbx" "%rsp" 192,  -- l.5096 `movq 192(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 328,  -- l.5097 `movq 328(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.5098 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 192,  -- l.5099 `movq 192(%rsp), %rdx`
    .loadMem "%r14" "%rsp" 328,  -- l.5100 `movq 328(%rsp), %r14`
    .mulx "%r10" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.5101 `mulx %r14, %rbx, %r10`
    .mov "%r12" (.reg "%rbx"),  -- l.5102 `movq %rbx, %r12`
    .bt "%rbp" (.imm 0),  -- l.5103 `btq $0, %rbp`
    .adcx "%r12" (.reg "%r8"),  -- l.5104 `adcxq %r8, %r12`
    .setc "%r9",  -- l.5105 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rbx" "%rsp" 200,  -- l.5107 `movq 200(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 328,  -- l.5108 `movq 328(%rsp), %r15`
    .imul "%rbx" (.reg "%r15"),  -- l.5109 `imulq %r15, %rbx`
    .loadMem "%rdx" "%rsp" 200 ]  -- l.5110 `movq 200(%rsp), %rdx`

/-- Segment 144 of the body: the 32 instructions from source lines 5111–5147. -/
def ed25519PointAddShippedSeg144 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 328,  -- l.5111 `movq 328(%rsp), %r14`
    .mulx "%rbp" "%rbx" (.reg "%rdx") (.reg "%r14"),  -- l.5112 `mulx %r14, %rbx, %rbp`
    .bt "%r9" (.imm 0),  -- l.5113 `btq $0, %r9`
    .storeMem "%rsp" (-128) (.reg "%rax"),  -- l.5114 `movq %rax, -128(%rsp)`
    .mov "%rax" (.reg "%rbx"),  -- l.5115 `movq %rbx, %rax`
    .adcx "%rax" (.reg "%r10"),  -- l.5116 `adcxq %r10, %rax`
    .storeMem "%rsp" 328 (.reg "%rax"),  -- l.5117 `movq %rax, 328(%rsp)`
    .loadMem "%rax" "%rsp" (-128),  -- l.5118 `movq -128(%rsp), %rax`
    .setc "%r8",  -- l.5119 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rbx" (.reg "%rbp"),  -- l.5121 `movq %rbp, %rbx`
    .bt "%r8" (.imm 0),  -- l.5122 `btq $0, %r8`
    .adcx "%rbx" (.reg "%rax"),  -- l.5123 `adcxq %rax, %rbx`
    .mov "%rax" (.imm 0),  -- l.5124 `movq $0, %rax`
    .mov "%rbp" (.imm 0),  -- l.5125 `movl $0, %ebp`
    .mov "%r8" (.reg "%rcx"),  -- l.5126 `movq %rcx, %r8`
    .bt "%rbp" (.imm 0),  -- l.5127 `btq $0, %rbp`
    .adcx "%r8" (.reg "%r11"),  -- l.5128 `adcxq %r11, %r8`
    .setc "%r9",  -- l.5129 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi"),  -- l.5131 `movq %rdi, %rcx`
    .bt "%r9" (.imm 0),  -- l.5132 `btq $0, %r9`
    .adcx "%rcx" (.reg "%r13"),  -- l.5133 `adcxq %r13, %rcx`
    .setc "%rbp",  -- l.5134 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%rdi" (.reg "%rsi"),  -- l.5136 `movq %rsi, %rdi`
    .bt "%rbp" (.imm 0),  -- l.5137 `btq $0, %rbp`
    .adcx "%rdi" (.reg "%r12"),  -- l.5138 `adcxq %r12, %rdi`
    .setc "%r9",  -- l.5139 `setc %r9b; movzbq %r9b, %r9`
    .loadMem "%rsi" "%rsp" 320,  -- l.5141 `movq 320(%rsp), %rsi`
    .bt "%r9" (.imm 0),  -- l.5142 `btq $0, %r9`
    .adcxMem "%rsi" "%rsp" 328,  -- l.5143 `adcxq 328(%rsp), %rsi`
    .setc "%rbp",  -- l.5144 `setc %bpl; movzbq %bpl, %rbp`
    .mov "%r9" (.reg "%rax"),  -- l.5146 `movq %rax, %r9`
    .bt "%rbp" (.imm 0) ]  -- l.5147 `btq $0, %rbp`

/-- Segment 145 of the body: the 32 instructions from source lines 5148–5183. -/
def ed25519PointAddShippedSeg145 : List (JInstr 64) :=
  [ .adcx "%r9" (.reg "%rbx"),  -- l.5148 `adcxq %rbx, %r9`
    .setc "%r10",  -- l.5149 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rax" (.imm 38),  -- l.5151 `movq $38, %rax`
    .mov "%rbx" (.imm 0),  -- l.5152 `movq $0, %rbx`
    .mov "%rbp" (.imm 0),  -- l.5153 `movl $0, %ebp`
    .mov "%r10" (.reg "%rcx"),  -- l.5154 `movq %rcx, %r10`
    .imul "%r10" (.reg "%rax"),  -- l.5155 `imulq %rax, %r10`
    .mov "%rdx" (.reg "%rcx"),  -- l.5156 `movq %rcx, %rdx`
    .mulx "%r11" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.5157 `mulx %rax, %r10, %r11`
    .mov "%rcx" (.reg "%r10"),  -- l.5158 `movq %r10, %rcx`
    .bt "%rbp" (.imm 0),  -- l.5159 `btq $0, %rbp`
    .adcx "%rcx" (.reg "%rbx"),  -- l.5160 `adcxq %rbx, %rcx`
    .setc "%r12",  -- l.5161 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rdi"),  -- l.5163 `movq %rdi, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.5164 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%rdi"),  -- l.5165 `movq %rdi, %rdx`
    .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.5166 `mulx %rax, %rbp, %r10`
    .mov "%rdi" (.reg "%rbp"),  -- l.5167 `movq %rbp, %rdi`
    .bt "%r12" (.imm 0),  -- l.5168 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r11"),  -- l.5169 `adcxq %r11, %rdi`
    .setc "%r13",  -- l.5170 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%rsi"),  -- l.5172 `movq %rsi, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.5173 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%rsi"),  -- l.5174 `movq %rsi, %rdx`
    .mulx "%r11" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.5175 `mulx %rax, %rbp, %r11`
    .mov "%rsi" (.reg "%rbp"),  -- l.5176 `movq %rbp, %rsi`
    .bt "%r13" (.imm 0),  -- l.5177 `btq $0, %r13`
    .adcx "%rsi" (.reg "%r10"),  -- l.5178 `adcxq %r10, %rsi`
    .setc "%r12",  -- l.5179 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%r9"),  -- l.5181 `movq %r9, %rbp`
    .imul "%rbp" (.reg "%rax"),  -- l.5182 `imulq %rax, %rbp`
    .mov "%rdx" (.reg "%r9") ]  -- l.5183 `movq %r9, %rdx`

/-- Segment 146 of the body: the 32 instructions from source lines 5184–5221. -/
def ed25519PointAddShippedSeg146 : List (JInstr 64) :=
  [ .mulx "%r10" "%rbp" (.reg "%rdx") (.reg "%rax"),  -- l.5184 `mulx %rax, %rbp, %r10`
    .mov "%r9" (.reg "%rbp"),  -- l.5185 `movq %rbp, %r9`
    .bt "%r12" (.imm 0),  -- l.5186 `btq $0, %r12`
    .adcx "%r9" (.reg "%r11"),  -- l.5187 `adcxq %r11, %r9`
    .setc "%r13",  -- l.5188 `setc %r13b; movzbq %r13b, %r13`
    .mov "%rbp" (.reg "%r10"),  -- l.5190 `movq %r10, %rbp`
    .bt "%r13" (.imm 0),  -- l.5191 `btq $0, %r13`
    .adcx "%rbp" (.reg "%rbx"),  -- l.5192 `adcxq %rbx, %rbp`
    .mov "%rbx" (.imm 0),  -- l.5193 `movq $0, %rbx`
    .mov "%r10" (.imm 0),  -- l.5194 `movl $0, %r10d`
    .loadMem "%r11" "%rsp" 256,  -- l.5195 `movq 256(%rsp), %r11`
    .bt "%r10" (.imm 0),  -- l.5196 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.5197 `adcxq %rcx, %r11`
    .setc "%r12",  -- l.5198 `setc %r12b; movzbq %r12b, %r12`
    .loadMem "%rcx" "%rsp" 248,  -- l.5200 `movq 248(%rsp), %rcx`
    .bt "%r12" (.imm 0),  -- l.5201 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rdi"),  -- l.5202 `adcxq %rdi, %rcx`
    .setc "%r10",  -- l.5203 `setc %r10b; movzbq %r10b, %r10`
    .loadMem "%rdi" "%rsp" 296,  -- l.5205 `movq 296(%rsp), %rdi`
    .bt "%r10" (.imm 0),  -- l.5206 `btq $0, %r10`
    .adcx "%rdi" (.reg "%rsi"),  -- l.5207 `adcxq %rsi, %rdi`
    .setc "%r12",  -- l.5208 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rsi" (.reg "%r8"),  -- l.5210 `movq %r8, %rsi`
    .bt "%r12" (.imm 0),  -- l.5211 `btq $0, %r12`
    .adcx "%rsi" (.reg "%r9"),  -- l.5212 `adcxq %r9, %rsi`
    .setc "%r10",  -- l.5213 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r8" (.reg "%rbx"),  -- l.5215 `movq %rbx, %r8`
    .bt "%r10" (.imm 0),  -- l.5216 `btq $0, %r10`
    .adcx "%r8" (.reg "%rbp"),  -- l.5217 `adcxq %rbp, %r8`
    .setc "%r9",  -- l.5218 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rbp" (.imm 0),  -- l.5220 `movq $0, %rbp`
    .mov "%r9" (.imm 0) ]  -- l.5221 `movl $0, %r9d`

/-- Segment 147 of the body: the 32 instructions from source lines 5222–5258. -/
def ed25519PointAddShippedSeg147 : List (JInstr 64) :=
  [ .mov "%r10" (.reg "%r8"),  -- l.5222 `movq %r8, %r10`
    .imul "%r10" (.reg "%rax"),  -- l.5223 `imulq %rax, %r10`
    .mov "%rdx" (.reg "%r8"),  -- l.5224 `movq %r8, %rdx`
    .mulx "%r12" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.5225 `mulx %rax, %r10, %r12`
    .mov "%r8" (.reg "%r10"),  -- l.5226 `movq %r10, %r8`
    .bt "%r9" (.imm 0),  -- l.5227 `btq $0, %r9`
    .adcx "%r8" (.reg "%rbp"),  -- l.5228 `adcxq %rbp, %r8`
    .setc "%r13",  -- l.5229 `setc %r13b; movzbq %r13b, %r13`
    .mov "%r9" (.reg "%r12"),  -- l.5231 `movq %r12, %r9`
    .bt "%r13" (.imm 0),  -- l.5232 `btq $0, %r13`
    .adcx "%r9" (.reg "%rbp"),  -- l.5233 `adcxq %rbp, %r9`
    .mov "%rbp" (.imm 0),  -- l.5234 `movl $0, %ebp`
    .mov "%r10" (.reg "%r11"),  -- l.5235 `movq %r11, %r10`
    .bt "%rbp" (.imm 0),  -- l.5236 `btq $0, %rbp`
    .adcx "%r10" (.reg "%r8"),  -- l.5237 `adcxq %r8, %r10`
    .setc "%r12",  -- l.5238 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbp" (.reg "%rcx"),  -- l.5240 `movq %rcx, %rbp`
    .bt "%r12" (.imm 0),  -- l.5241 `btq $0, %r12`
    .adcx "%rbp" (.reg "%r9"),  -- l.5242 `adcxq %r9, %rbp`
    .setc "%r8",  -- l.5243 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rcx" (.reg "%rdi"),  -- l.5245 `movq %rdi, %rcx`
    .bt "%r8" (.imm 0),  -- l.5246 `btq $0, %r8`
    .adcx "%rcx" (.reg "%rbx"),  -- l.5247 `adcxq %rbx, %rcx`
    .setc "%r9",  -- l.5248 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rdi" (.reg "%rsi"),  -- l.5250 `movq %rsi, %rdi`
    .bt "%r9" (.imm 0),  -- l.5251 `btq $0, %r9`
    .adcx "%rdi" (.reg "%rbx"),  -- l.5252 `adcxq %rbx, %rdi`
    .setc "%r8",  -- l.5253 `setc %r8b; movzbq %r8b, %r8`
    .mov "%rsi" (.reg "%rbx"),  -- l.5255 `movq %rbx, %rsi`
    .test "%r8" (.reg "%r8"),  -- l.5256 `testq %r8, %r8`
    .cmovne "%rsi" (.reg "%rax"),  -- l.5257 `cmovneq %rax, %rsi`
    .mov "%rax" (.imm 0) ]  -- l.5258 `movl $0, %eax`

/-- Segment 148 of the body: the 32 instructions from source lines 5259–5296. -/
def ed25519PointAddShippedSeg148 : List (JInstr 64) :=
  [ .mov "%r8" (.reg "%r10"),  -- l.5259 `movq %r10, %r8`
    .bt "%rax" (.imm 0),  -- l.5260 `btq $0, %rax`
    .adcx "%r8" (.reg "%rsi"),  -- l.5261 `adcxq %rsi, %r8`
    .setc "%r9",  -- l.5262 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rax" (.reg "%rbp"),  -- l.5264 `movq %rbp, %rax`
    .bt "%r9" (.imm 0),  -- l.5265 `btq $0, %r9`
    .adcx "%rax" (.reg "%rbx"),  -- l.5266 `adcxq %rbx, %rax`
    .setc "%rsi",  -- l.5267 `setc %sil; movzbq %sil, %rsi`
    .mov "%rbp" (.reg "%rcx"),  -- l.5269 `movq %rcx, %rbp`
    .bt "%rsi" (.imm 0),  -- l.5270 `btq $0, %rsi`
    .adcx "%rbp" (.reg "%rbx"),  -- l.5271 `adcxq %rbx, %rbp`
    .setc "%r9",  -- l.5272 `setc %r9b; movzbq %r9b, %r9`
    .mov "%rcx" (.reg "%rdi"),  -- l.5274 `movq %rdi, %rcx`
    .bt "%r9" (.imm 0),  -- l.5275 `btq $0, %r9`
    .adcx "%rcx" (.reg "%rbx"),  -- l.5276 `adcxq %rbx, %rcx`
    .setc "%rsi",  -- l.5277 `setc %sil; movzbq %sil, %rsi`
    .mov "%rbx" (.imm 19),  -- l.5279 `movq $19, %rbx`
    .mov "%rsi" (.imm 0),  -- l.5280 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.5281 `movq $0, %rdi`
    .mov "%r9" (.imm 9223372036854775808),  -- l.5282 `movq $9223372036854775808, %r9`
    .mov "%r10" (.imm 0),  -- l.5283 `movl $0, %r10d`
    .mov "%r11" (.reg "%r8"),  -- l.5284 `movq %r8, %r11`
    .bt "%r10" (.imm 0),  -- l.5285 `btq $0, %r10`
    .adcx "%r11" (.reg "%rbx"),  -- l.5286 `adcxq %rbx, %r11`
    .setc "%r12",  -- l.5287 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rbx" (.reg "%rax"),  -- l.5289 `movq %rax, %rbx`
    .bt "%r12" (.imm 0),  -- l.5290 `btq $0, %r12`
    .adcx "%rbx" (.reg "%rsi"),  -- l.5291 `adcxq %rsi, %rbx`
    .setc "%r10",  -- l.5292 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rbp"),  -- l.5294 `movq %rbp, %rsi`
    .bt "%r10" (.imm 0),  -- l.5295 `btq $0, %r10`
    .adcx "%rsi" (.reg "%rdi") ]  -- l.5296 `adcxq %rdi, %rsi`

/-- Segment 149 of the body: the 32 instructions from source lines 5297–5332. -/
def ed25519PointAddShippedSeg149 : List (JInstr 64) :=
  [ .setc "%r12",  -- l.5297 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rcx"),  -- l.5299 `movq %rcx, %rdi`
    .bt "%r12" (.imm 0),  -- l.5300 `btq $0, %r12`
    .adcx "%rdi" (.reg "%r9"),  -- l.5301 `adcxq %r9, %rdi`
    .setc "%r10",  -- l.5302 `setc %r10b; movzbq %r10b, %r10`
    .mov "%r9" (.reg "%r8"),  -- l.5304 `movq %r8, %r9`
    .test "%r10" (.reg "%r10"),  -- l.5305 `testq %r10, %r10`
    .cmovne "%r9" (.reg "%r11"),  -- l.5306 `cmovneq %r11, %r9`
    .mov "%r8" (.reg "%rax"),  -- l.5307 `movq %rax, %r8`
    .test "%r10" (.reg "%r10"),  -- l.5308 `testq %r10, %r10`
    .cmovne "%r8" (.reg "%rbx"),  -- l.5309 `cmovneq %rbx, %r8`
    .mov "%rax" (.reg "%rbp"),  -- l.5310 `movq %rbp, %rax`
    .test "%r10" (.reg "%r10"),  -- l.5311 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rsi"),  -- l.5312 `cmovneq %rsi, %rax`
    .mov "%rbx" (.reg "%rcx"),  -- l.5313 `movq %rcx, %rbx`
    .test "%r10" (.reg "%r10"),  -- l.5314 `testq %r10, %r10`
    .cmovne "%rbx" (.reg "%rdi"),  -- l.5315 `cmovneq %rdi, %rbx`
    .mov "%rcx" (.imm 19),  -- l.5316 `movq $19, %rcx`
    .mov "%rsi" (.imm 0),  -- l.5317 `movq $0, %rsi`
    .mov "%rdi" (.imm 0),  -- l.5318 `movq $0, %rdi`
    .mov "%rbp" (.imm 9223372036854775808),  -- l.5319 `movq $9223372036854775808, %rbp`
    .mov "%r10" (.imm 0),  -- l.5320 `movl $0, %r10d`
    .mov "%r11" (.reg "%r9"),  -- l.5321 `movq %r9, %r11`
    .bt "%r10" (.imm 0),  -- l.5322 `btq $0, %r10`
    .adcx "%r11" (.reg "%rcx"),  -- l.5323 `adcxq %rcx, %r11`
    .setc "%r12",  -- l.5324 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rcx" (.reg "%r8"),  -- l.5326 `movq %r8, %rcx`
    .bt "%r12" (.imm 0),  -- l.5327 `btq $0, %r12`
    .adcx "%rcx" (.reg "%rsi"),  -- l.5328 `adcxq %rsi, %rcx`
    .setc "%r10",  -- l.5329 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rsi" (.reg "%rax"),  -- l.5331 `movq %rax, %rsi`
    .bt "%r10" (.imm 0) ]  -- l.5332 `btq $0, %r10`

/-- Segment 150 of the body: the 32 instructions from source lines 5333–5366. -/
def ed25519PointAddShippedSeg150 : List (JInstr 64) :=
  [ .adcx "%rsi" (.reg "%rdi"),  -- l.5333 `adcxq %rdi, %rsi`
    .setc "%r12",  -- l.5334 `setc %r12b; movzbq %r12b, %r12`
    .mov "%rdi" (.reg "%rbx"),  -- l.5336 `movq %rbx, %rdi`
    .bt "%r12" (.imm 0),  -- l.5337 `btq $0, %r12`
    .adcx "%rdi" (.reg "%rbp"),  -- l.5338 `adcxq %rbp, %rdi`
    .setc "%r10",  -- l.5339 `setc %r10b; movzbq %r10b, %r10`
    .mov "%rbp" (.reg "%r9"),  -- l.5341 `movq %r9, %rbp`
    .test "%r10" (.reg "%r10"),  -- l.5342 `testq %r10, %r10`
    .cmovne "%rbp" (.reg "%r11"),  -- l.5343 `cmovneq %r11, %rbp`
    .mov "%r9" (.reg "%r8"),  -- l.5344 `movq %r8, %r9`
    .test "%r10" (.reg "%r10"),  -- l.5345 `testq %r10, %r10`
    .cmovne "%r9" (.reg "%rcx"),  -- l.5346 `cmovneq %rcx, %r9`
    .mov "%rcx" (.reg "%rax"),  -- l.5347 `movq %rax, %rcx`
    .test "%r10" (.reg "%r10"),  -- l.5348 `testq %r10, %r10`
    .cmovne "%rcx" (.reg "%rsi"),  -- l.5349 `cmovneq %rsi, %rcx`
    .mov "%rax" (.reg "%rbx"),  -- l.5350 `movq %rbx, %rax`
    .test "%r10" (.reg "%r10"),  -- l.5351 `testq %r10, %r10`
    .cmovne "%rax" (.reg "%rdi"),  -- l.5352 `cmovneq %rdi, %rax`
    .loadMem "%rbx" "%rsp" 208,  -- l.5353 `movq 208(%rsp), %rbx`
    .loadMem "%r15" "%rsp" 208,  -- l.5354 `movq 208(%rsp), %r15`
    .or_ "%rbx" (.reg "%r15"),  -- l.5355 `orq %r15, %rbx`
    .loadMem "%r14" "%rsp" 392,  -- l.5356 `movq 392(%rsp), %r14`
    .storeMem "%r14" 0 (.reg "%rbx"),  -- l.5357 `movq %rbx, (%r14)`
    .loadMem "%rsi" "%rsp" 216,  -- l.5358 `movq 216(%rsp), %rsi`
    .loadMem "%r15" "%rsp" 216,  -- l.5359 `movq 216(%rsp), %r15`
    .or_ "%rsi" (.reg "%r15"),  -- l.5360 `orq %r15, %rsi`
    .loadMem "%r14" "%rsp" 392,  -- l.5361 `movq 392(%rsp), %r14`
    .storeMem "%r14" 8 (.reg "%rsi"),  -- l.5362 `movq %rsi, 8(%r14)`
    .loadMem "%rdi" "%rsp" 224,  -- l.5363 `movq 224(%rsp), %rdi`
    .loadMem "%r15" "%rsp" 224,  -- l.5364 `movq 224(%rsp), %r15`
    .or_ "%rdi" (.reg "%r15"),  -- l.5365 `orq %r15, %rdi`
    .loadMem "%r14" "%rsp" 392 ]  -- l.5366 `movq 392(%rsp), %r14`

/-- Segment 151 of the body: the 32 instructions from source lines 5367–5398. -/
def ed25519PointAddShippedSeg151 : List (JInstr 64) :=
  [ .storeMem "%r14" 16 (.reg "%rdi"),  -- l.5367 `movq %rdi, 16(%r14)`
    .loadMem "%r8" "%rsp" 304,  -- l.5368 `movq 304(%rsp), %r8`
    .loadMem "%r15" "%rsp" 304,  -- l.5369 `movq 304(%rsp), %r15`
    .or_ "%r8" (.reg "%r15"),  -- l.5370 `orq %r15, %r8`
    .loadMem "%r14" "%rsp" 392,  -- l.5371 `movq 392(%rsp), %r14`
    .storeMem "%r14" 24 (.reg "%r8"),  -- l.5372 `movq %r8, 24(%r14)`
    .loadMem "%r10" "%rsp" 144,  -- l.5373 `movq 144(%rsp), %r10`
    .loadMem "%r15" "%rsp" 144,  -- l.5374 `movq 144(%rsp), %r15`
    .or_ "%r10" (.reg "%r15"),  -- l.5375 `orq %r15, %r10`
    .loadMem "%r14" "%rsp" 392,  -- l.5376 `movq 392(%rsp), %r14`
    .storeMem "%r14" 32 (.reg "%r10"),  -- l.5377 `movq %r10, 32(%r14)`
    .loadMem "%r11" "%rsp" 152,  -- l.5378 `movq 152(%rsp), %r11`
    .loadMem "%r15" "%rsp" 152,  -- l.5379 `movq 152(%rsp), %r15`
    .or_ "%r11" (.reg "%r15"),  -- l.5380 `orq %r15, %r11`
    .loadMem "%r14" "%rsp" 392,  -- l.5381 `movq 392(%rsp), %r14`
    .storeMem "%r14" 40 (.reg "%r11"),  -- l.5382 `movq %r11, 40(%r14)`
    .loadMem "%r12" "%rsp" 160,  -- l.5383 `movq 160(%rsp), %r12`
    .loadMem "%r15" "%rsp" 160,  -- l.5384 `movq 160(%rsp), %r15`
    .or_ "%r12" (.reg "%r15"),  -- l.5385 `orq %r15, %r12`
    .loadMem "%r14" "%rsp" 392,  -- l.5386 `movq 392(%rsp), %r14`
    .storeMem "%r14" 48 (.reg "%r12"),  -- l.5387 `movq %r12, 48(%r14)`
    .loadMem "%r13" "%rsp" 168,  -- l.5388 `movq 168(%rsp), %r13`
    .loadMem "%r15" "%rsp" 168,  -- l.5389 `movq 168(%rsp), %r15`
    .or_ "%r13" (.reg "%r15"),  -- l.5390 `orq %r15, %r13`
    .loadMem "%r14" "%rsp" 392,  -- l.5391 `movq 392(%rsp), %r14`
    .storeMem "%r14" 56 (.reg "%r13"),  -- l.5392 `movq %r13, 56(%r14)`
    .storeMem "%rsp" 328 (.reg "%rbp"),  -- l.5393 `movq %rbp, 328(%rsp)`
    .loadMem "%r15" "%rsp" 328,  -- l.5394 `movq 328(%rsp), %r15`
    .or_ "%r15" (.reg "%rbp"),  -- l.5395 `orq %rbp, %r15`
    .storeMem "%rsp" 328 (.reg "%r15"),  -- l.5396 `movq %r15, 328(%rsp)`
    .loadMem "%r15" "%rsp" 328,  -- l.5397 `movq 328(%rsp), %r15`
    .loadMem "%r14" "%rsp" 392 ]  -- l.5398 `movq 392(%rsp), %r14`

/-- Segment 152 of the body: the 32 instructions from source lines 5399–5430. -/
def ed25519PointAddShippedSeg152 : List (JInstr 64) :=
  [ .storeMem "%r14" 64 (.reg "%r15"),  -- l.5399 `movq %r15, 64(%r14)`
    .mov "%rbp" (.reg "%r9"),  -- l.5400 `movq %r9, %rbp`
    .or_ "%rbp" (.reg "%r9"),  -- l.5401 `orq %r9, %rbp`
    .loadMem "%r14" "%rsp" 392,  -- l.5402 `movq 392(%rsp), %r14`
    .storeMem "%r14" 72 (.reg "%rbp"),  -- l.5403 `movq %rbp, 72(%r14)`
    .mov "%r9" (.reg "%rcx"),  -- l.5404 `movq %rcx, %r9`
    .or_ "%r9" (.reg "%rcx"),  -- l.5405 `orq %rcx, %r9`
    .loadMem "%r14" "%rsp" 392,  -- l.5406 `movq 392(%rsp), %r14`
    .storeMem "%r14" 80 (.reg "%r9"),  -- l.5407 `movq %r9, 80(%r14)`
    .mov "%rcx" (.reg "%rax"),  -- l.5408 `movq %rax, %rcx`
    .or_ "%rcx" (.reg "%rax"),  -- l.5409 `orq %rax, %rcx`
    .loadMem "%r14" "%rsp" 392,  -- l.5410 `movq 392(%rsp), %r14`
    .storeMem "%r14" 88 (.reg "%rcx"),  -- l.5411 `movq %rcx, 88(%r14)`
    .loadMem "%rax" "%rsp" 264,  -- l.5412 `movq 264(%rsp), %rax`
    .loadMem "%r15" "%rsp" 264,  -- l.5413 `movq 264(%rsp), %r15`
    .or_ "%rax" (.reg "%r15"),  -- l.5414 `orq %r15, %rax`
    .loadMem "%r14" "%rsp" 392,  -- l.5415 `movq 392(%rsp), %r14`
    .storeMem "%r14" 96 (.reg "%rax"),  -- l.5416 `movq %rax, 96(%r14)`
    .loadMem "%r15" "%rsp" 272,  -- l.5417 `movq 272(%rsp), %r15`
    .storeMem "%rsp" 320 (.reg "%r15"),  -- l.5418 `movq %r15, 320(%rsp)`
    .loadMem "%r15" "%rsp" 320,  -- l.5419 `movq 320(%rsp), %r15`
    .loadMem "%r14" "%rsp" 272,  -- l.5420 `movq 272(%rsp), %r14`
    .or_ "%r15" (.reg "%r14"),  -- l.5421 `orq %r14, %r15`
    .storeMem "%rsp" 320 (.reg "%r15"),  -- l.5422 `movq %r15, 320(%rsp)`
    .loadMem "%r15" "%rsp" 320,  -- l.5423 `movq 320(%rsp), %r15`
    .loadMem "%r14" "%rsp" 392,  -- l.5424 `movq 392(%rsp), %r14`
    .storeMem "%r14" 104 (.reg "%r15"),  -- l.5425 `movq %r15, 104(%r14)`
    .loadMem "%r15" "%rsp" 280,  -- l.5426 `movq 280(%rsp), %r15`
    .storeMem "%rsp" 312 (.reg "%r15"),  -- l.5427 `movq %r15, 312(%rsp)`
    .loadMem "%r15" "%rsp" 312,  -- l.5428 `movq 312(%rsp), %r15`
    .loadMem "%r14" "%rsp" 280,  -- l.5429 `movq 280(%rsp), %r14`
    .or_ "%r15" (.reg "%r14") ]  -- l.5430 `orq %r14, %r15`

/-- Segment 153 of the body: the 32 instructions from source lines 5431–5462. -/
def ed25519PointAddShippedSeg153 : List (JInstr 64) :=
  [ .storeMem "%rsp" 312 (.reg "%r15"),  -- l.5431 `movq %r15, 312(%rsp)`
    .loadMem "%r15" "%rsp" 312,  -- l.5432 `movq 312(%rsp), %r15`
    .loadMem "%r14" "%rsp" 392,  -- l.5433 `movq 392(%rsp), %r14`
    .storeMem "%r14" 112 (.reg "%r15"),  -- l.5434 `movq %r15, 112(%r14)`
    .loadMem "%r15" "%rsp" 288,  -- l.5435 `movq 288(%rsp), %r15`
    .storeMem "%rsp" 304 (.reg "%r15"),  -- l.5436 `movq %r15, 304(%rsp)`
    .loadMem "%r15" "%rsp" 304,  -- l.5437 `movq 304(%rsp), %r15`
    .loadMem "%r14" "%rsp" 288,  -- l.5438 `movq 288(%rsp), %r14`
    .or_ "%r15" (.reg "%r14"),  -- l.5439 `orq %r14, %r15`
    .storeMem "%rsp" 304 (.reg "%r15"),  -- l.5440 `movq %r15, 304(%rsp)`
    .loadMem "%r15" "%rsp" 304,  -- l.5441 `movq 304(%rsp), %r15`
    .loadMem "%r14" "%rsp" 392,  -- l.5442 `movq 392(%rsp), %r14`
    .storeMem "%r14" 120 (.reg "%r15"),  -- l.5443 `movq %r15, 120(%r14)`
    .loadMem "%rbx" "%rsp" 376,  -- l.5444 `movq 376(%rsp), %rbx`
    .loadMem "%rbp" "%rsp" 368,  -- l.5445 `movq 368(%rsp), %rbp`
    .loadMem "%r12" "%rsp" 360,  -- l.5446 `movq 360(%rsp), %r12`
    .loadMem "%r13" "%rsp" 352,  -- l.5447 `movq 352(%rsp), %r13`
    .loadMem "%r14" "%rsp" 344,  -- l.5448 `movq 344(%rsp), %r14`
    .loadMem "%r15" "%rsp" 336,  -- l.5449 `movq 336(%rsp), %r15`
    .storeMem "%rsp" 392 (.imm 0),  -- l.5450 `movq $0, 392(%rsp)`
    .storeMem "%rsp" 384 (.imm 0),  -- l.5451 `movq $0, 384(%rsp)`
    .storeMem "%rsp" 376 (.imm 0),  -- l.5452 `movq $0, 376(%rsp)`
    .storeMem "%rsp" 368 (.imm 0),  -- l.5453 `movq $0, 368(%rsp)`
    .storeMem "%rsp" 360 (.imm 0),  -- l.5454 `movq $0, 360(%rsp)`
    .storeMem "%rsp" 352 (.imm 0),  -- l.5455 `movq $0, 352(%rsp)`
    .storeMem "%rsp" 344 (.imm 0),  -- l.5456 `movq $0, 344(%rsp)`
    .storeMem "%rsp" 336 (.imm 0),  -- l.5457 `movq $0, 336(%rsp)`
    .storeMem "%rsp" 296 (.imm 0),  -- l.5458 `movq $0, 296(%rsp)`
    .storeMem "%rsp" 288 (.imm 0),  -- l.5459 `movq $0, 288(%rsp)`
    .storeMem "%rsp" 280 (.imm 0),  -- l.5460 `movq $0, 280(%rsp)`
    .storeMem "%rsp" 272 (.imm 0),  -- l.5461 `movq $0, 272(%rsp)`
    .storeMem "%rsp" 328 (.imm 0) ]  -- l.5462 `movq $0, 328(%rsp)`

/-- Segment 154 of the body: the 32 instructions from source lines 5463–5494. -/
def ed25519PointAddShippedSeg154 : List (JInstr 64) :=
  [ .storeMem "%rsp" 320 (.imm 0),  -- l.5463 `movq $0, 320(%rsp)`
    .storeMem "%rsp" 312 (.imm 0),  -- l.5464 `movq $0, 312(%rsp)`
    .storeMem "%rsp" 304 (.imm 0),  -- l.5465 `movq $0, 304(%rsp)`
    .storeMem "%rsp" 136 (.imm 0),  -- l.5466 `movq $0, 136(%rsp)`
    .storeMem "%rsp" 128 (.imm 0),  -- l.5467 `movq $0, 128(%rsp)`
    .storeMem "%rsp" 120 (.imm 0),  -- l.5468 `movq $0, 120(%rsp)`
    .storeMem "%rsp" 112 (.imm 0),  -- l.5469 `movq $0, 112(%rsp)`
    .storeMem "%rsp" 264 (.imm 0),  -- l.5470 `movq $0, 264(%rsp)`
    .storeMem "%rsp" 224 (.imm 0),  -- l.5471 `movq $0, 224(%rsp)`
    .storeMem "%rsp" 216 (.imm 0),  -- l.5472 `movq $0, 216(%rsp)`
    .storeMem "%rsp" 208 (.imm 0),  -- l.5473 `movq $0, 208(%rsp)`
    .storeMem "%rsp" 200 (.imm 0),  -- l.5474 `movq $0, 200(%rsp)`
    .storeMem "%rsp" 192 (.imm 0),  -- l.5475 `movq $0, 192(%rsp)`
    .storeMem "%rsp" 176 (.imm 0),  -- l.5476 `movq $0, 176(%rsp)`
    .storeMem "%rsp" 160 (.imm 0),  -- l.5477 `movq $0, 160(%rsp)`
    .storeMem "%rsp" 256 (.imm 0),  -- l.5478 `movq $0, 256(%rsp)`
    .storeMem "%rsp" 248 (.imm 0),  -- l.5479 `movq $0, 248(%rsp)`
    .storeMem "%rsp" 240 (.imm 0),  -- l.5480 `movq $0, 240(%rsp)`
    .storeMem "%rsp" 232 (.imm 0),  -- l.5481 `movq $0, 232(%rsp)`
    .storeMem "%rsp" 104 (.imm 0),  -- l.5482 `movq $0, 104(%rsp)`
    .storeMem "%rsp" 96 (.imm 0),  -- l.5483 `movq $0, 96(%rsp)`
    .storeMem "%rsp" 88 (.imm 0),  -- l.5484 `movq $0, 88(%rsp)`
    .storeMem "%rsp" 80 (.imm 0),  -- l.5485 `movq $0, 80(%rsp)`
    .storeMem "%rsp" 184 (.imm 0),  -- l.5486 `movq $0, 184(%rsp)`
    .storeMem "%rsp" 168 (.imm 0),  -- l.5487 `movq $0, 168(%rsp)`
    .storeMem "%rsp" 152 (.imm 0),  -- l.5488 `movq $0, 152(%rsp)`
    .storeMem "%rsp" 144 (.imm 0),  -- l.5489 `movq $0, 144(%rsp)`
    .storeMem "%rsp" 48 (.imm 0),  -- l.5490 `movq $0, 48(%rsp)`
    .storeMem "%rsp" 56 (.imm 0),  -- l.5491 `movq $0, 56(%rsp)`
    .storeMem "%rsp" 64 (.imm 0),  -- l.5492 `movq $0, 64(%rsp)`
    .storeMem "%rsp" 72 (.imm 0),  -- l.5493 `movq $0, 72(%rsp)`
    .storeMem "%rsp" 32 (.imm 0) ]  -- l.5494 `movq $0, 32(%rsp)`

/-- Segment 155 of the body: the 5 instructions from source lines 5495–5499. -/
def ed25519PointAddShippedSeg155 : List (JInstr 64) :=
  [ .storeMem "%rsp" 40 (.imm 0),  -- l.5495 `movq $0, 40(%rsp)`
    .storeMem "%rsp" 16 (.imm 0),  -- l.5496 `movq $0, 16(%rsp)`
    .storeMem "%rsp" 24 (.imm 0),  -- l.5497 `movq $0, 24(%rsp)`
    .storeMem "%rsp" 8 (.imm 0),  -- l.5498 `movq $0, 8(%rsp)`
    .storeMem "%rsp" 0 (.imm 0) ]  -- l.5499 `movq $0, 0(%rsp)`

/-- Part 1 of the body: segments 1–16. -/
def ed25519PointAddShippedPart01 : List (JInstr 64) :=
  ed25519PointAddShippedSeg001 ++ ed25519PointAddShippedSeg002 ++
  ed25519PointAddShippedSeg003 ++ ed25519PointAddShippedSeg004 ++
  ed25519PointAddShippedSeg005 ++ ed25519PointAddShippedSeg006 ++
  ed25519PointAddShippedSeg007 ++ ed25519PointAddShippedSeg008 ++
  ed25519PointAddShippedSeg009 ++ ed25519PointAddShippedSeg010 ++
  ed25519PointAddShippedSeg011 ++ ed25519PointAddShippedSeg012 ++
  ed25519PointAddShippedSeg013 ++ ed25519PointAddShippedSeg014 ++
  ed25519PointAddShippedSeg015 ++ ed25519PointAddShippedSeg016

/-- Part 1 has 488 instructions. -/
theorem ed25519PointAddShippedPart01_length :
    ed25519PointAddShippedPart01.length = 488 := by
  unfold ed25519PointAddShippedPart01
  simp only [List.length_append]
  rfl

/-- Part 2 of the body: segments 17–32. -/
def ed25519PointAddShippedPart02 : List (JInstr 64) :=
  ed25519PointAddShippedSeg017 ++ ed25519PointAddShippedSeg018 ++
  ed25519PointAddShippedSeg019 ++ ed25519PointAddShippedSeg020 ++
  ed25519PointAddShippedSeg021 ++ ed25519PointAddShippedSeg022 ++
  ed25519PointAddShippedSeg023 ++ ed25519PointAddShippedSeg024 ++
  ed25519PointAddShippedSeg025 ++ ed25519PointAddShippedSeg026 ++
  ed25519PointAddShippedSeg027 ++ ed25519PointAddShippedSeg028 ++
  ed25519PointAddShippedSeg029 ++ ed25519PointAddShippedSeg030 ++
  ed25519PointAddShippedSeg031 ++ ed25519PointAddShippedSeg032

/-- Part 2 has 512 instructions. -/
theorem ed25519PointAddShippedPart02_length :
    ed25519PointAddShippedPart02.length = 512 := by
  unfold ed25519PointAddShippedPart02
  simp only [List.length_append]
  rfl

/-- Part 3 of the body: segments 33–48. -/
def ed25519PointAddShippedPart03 : List (JInstr 64) :=
  ed25519PointAddShippedSeg033 ++ ed25519PointAddShippedSeg034 ++
  ed25519PointAddShippedSeg035 ++ ed25519PointAddShippedSeg036 ++
  ed25519PointAddShippedSeg037 ++ ed25519PointAddShippedSeg038 ++
  ed25519PointAddShippedSeg039 ++ ed25519PointAddShippedSeg040 ++
  ed25519PointAddShippedSeg041 ++ ed25519PointAddShippedSeg042 ++
  ed25519PointAddShippedSeg043 ++ ed25519PointAddShippedSeg044 ++
  ed25519PointAddShippedSeg045 ++ ed25519PointAddShippedSeg046 ++
  ed25519PointAddShippedSeg047 ++ ed25519PointAddShippedSeg048

/-- Part 3 has 512 instructions. -/
theorem ed25519PointAddShippedPart03_length :
    ed25519PointAddShippedPart03.length = 512 := by
  unfold ed25519PointAddShippedPart03
  simp only [List.length_append]
  rfl

/-- Part 4 of the body: segments 49–64. -/
def ed25519PointAddShippedPart04 : List (JInstr 64) :=
  ed25519PointAddShippedSeg049 ++ ed25519PointAddShippedSeg050 ++
  ed25519PointAddShippedSeg051 ++ ed25519PointAddShippedSeg052 ++
  ed25519PointAddShippedSeg053 ++ ed25519PointAddShippedSeg054 ++
  ed25519PointAddShippedSeg055 ++ ed25519PointAddShippedSeg056 ++
  ed25519PointAddShippedSeg057 ++ ed25519PointAddShippedSeg058 ++
  ed25519PointAddShippedSeg059 ++ ed25519PointAddShippedSeg060 ++
  ed25519PointAddShippedSeg061 ++ ed25519PointAddShippedSeg062 ++
  ed25519PointAddShippedSeg063 ++ ed25519PointAddShippedSeg064

/-- Part 4 has 512 instructions. -/
theorem ed25519PointAddShippedPart04_length :
    ed25519PointAddShippedPart04.length = 512 := by
  unfold ed25519PointAddShippedPart04
  simp only [List.length_append]
  rfl

/-- Part 5 of the body: segments 65–80. -/
def ed25519PointAddShippedPart05 : List (JInstr 64) :=
  ed25519PointAddShippedSeg065 ++ ed25519PointAddShippedSeg066 ++
  ed25519PointAddShippedSeg067 ++ ed25519PointAddShippedSeg068 ++
  ed25519PointAddShippedSeg069 ++ ed25519PointAddShippedSeg070 ++
  ed25519PointAddShippedSeg071 ++ ed25519PointAddShippedSeg072 ++
  ed25519PointAddShippedSeg073 ++ ed25519PointAddShippedSeg074 ++
  ed25519PointAddShippedSeg075 ++ ed25519PointAddShippedSeg076 ++
  ed25519PointAddShippedSeg077 ++ ed25519PointAddShippedSeg078 ++
  ed25519PointAddShippedSeg079 ++ ed25519PointAddShippedSeg080

/-- Part 5 has 512 instructions. -/
theorem ed25519PointAddShippedPart05_length :
    ed25519PointAddShippedPart05.length = 512 := by
  unfold ed25519PointAddShippedPart05
  simp only [List.length_append]
  rfl

/-- Part 6 of the body: segments 81–96. -/
def ed25519PointAddShippedPart06 : List (JInstr 64) :=
  ed25519PointAddShippedSeg081 ++ ed25519PointAddShippedSeg082 ++
  ed25519PointAddShippedSeg083 ++ ed25519PointAddShippedSeg084 ++
  ed25519PointAddShippedSeg085 ++ ed25519PointAddShippedSeg086 ++
  ed25519PointAddShippedSeg087 ++ ed25519PointAddShippedSeg088 ++
  ed25519PointAddShippedSeg089 ++ ed25519PointAddShippedSeg090 ++
  ed25519PointAddShippedSeg091 ++ ed25519PointAddShippedSeg092 ++
  ed25519PointAddShippedSeg093 ++ ed25519PointAddShippedSeg094 ++
  ed25519PointAddShippedSeg095 ++ ed25519PointAddShippedSeg096

/-- Part 6 has 512 instructions. -/
theorem ed25519PointAddShippedPart06_length :
    ed25519PointAddShippedPart06.length = 512 := by
  unfold ed25519PointAddShippedPart06
  simp only [List.length_append]
  rfl

/-- Part 7 of the body: segments 97–112. -/
def ed25519PointAddShippedPart07 : List (JInstr 64) :=
  ed25519PointAddShippedSeg097 ++ ed25519PointAddShippedSeg098 ++
  ed25519PointAddShippedSeg099 ++ ed25519PointAddShippedSeg100 ++
  ed25519PointAddShippedSeg101 ++ ed25519PointAddShippedSeg102 ++
  ed25519PointAddShippedSeg103 ++ ed25519PointAddShippedSeg104 ++
  ed25519PointAddShippedSeg105 ++ ed25519PointAddShippedSeg106 ++
  ed25519PointAddShippedSeg107 ++ ed25519PointAddShippedSeg108 ++
  ed25519PointAddShippedSeg109 ++ ed25519PointAddShippedSeg110 ++
  ed25519PointAddShippedSeg111 ++ ed25519PointAddShippedSeg112

/-- Part 7 has 512 instructions. -/
theorem ed25519PointAddShippedPart07_length :
    ed25519PointAddShippedPart07.length = 512 := by
  unfold ed25519PointAddShippedPart07
  simp only [List.length_append]
  rfl

/-- Part 8 of the body: segments 113–128. -/
def ed25519PointAddShippedPart08 : List (JInstr 64) :=
  ed25519PointAddShippedSeg113 ++ ed25519PointAddShippedSeg114 ++
  ed25519PointAddShippedSeg115 ++ ed25519PointAddShippedSeg116 ++
  ed25519PointAddShippedSeg117 ++ ed25519PointAddShippedSeg118 ++
  ed25519PointAddShippedSeg119 ++ ed25519PointAddShippedSeg120 ++
  ed25519PointAddShippedSeg121 ++ ed25519PointAddShippedSeg122 ++
  ed25519PointAddShippedSeg123 ++ ed25519PointAddShippedSeg124 ++
  ed25519PointAddShippedSeg125 ++ ed25519PointAddShippedSeg126 ++
  ed25519PointAddShippedSeg127 ++ ed25519PointAddShippedSeg128

/-- Part 8 has 512 instructions. -/
theorem ed25519PointAddShippedPart08_length :
    ed25519PointAddShippedPart08.length = 512 := by
  unfold ed25519PointAddShippedPart08
  simp only [List.length_append]
  rfl

/-- Part 9 of the body: segments 129–144. -/
def ed25519PointAddShippedPart09 : List (JInstr 64) :=
  ed25519PointAddShippedSeg129 ++ ed25519PointAddShippedSeg130 ++
  ed25519PointAddShippedSeg131 ++ ed25519PointAddShippedSeg132 ++
  ed25519PointAddShippedSeg133 ++ ed25519PointAddShippedSeg134 ++
  ed25519PointAddShippedSeg135 ++ ed25519PointAddShippedSeg136 ++
  ed25519PointAddShippedSeg137 ++ ed25519PointAddShippedSeg138 ++
  ed25519PointAddShippedSeg139 ++ ed25519PointAddShippedSeg140 ++
  ed25519PointAddShippedSeg141 ++ ed25519PointAddShippedSeg142 ++
  ed25519PointAddShippedSeg143 ++ ed25519PointAddShippedSeg144

/-- Part 9 has 512 instructions. -/
theorem ed25519PointAddShippedPart09_length :
    ed25519PointAddShippedPart09.length = 512 := by
  unfold ed25519PointAddShippedPart09
  simp only [List.length_append]
  rfl

/-- Part 10 of the body: segments 145–155. -/
def ed25519PointAddShippedPart10 : List (JInstr 64) :=
  ed25519PointAddShippedSeg145 ++ ed25519PointAddShippedSeg146 ++
  ed25519PointAddShippedSeg147 ++ ed25519PointAddShippedSeg148 ++
  ed25519PointAddShippedSeg149 ++ ed25519PointAddShippedSeg150 ++
  ed25519PointAddShippedSeg151 ++ ed25519PointAddShippedSeg152 ++
  ed25519PointAddShippedSeg153 ++ ed25519PointAddShippedSeg154 ++
  ed25519PointAddShippedSeg155

/-- Part 10 has 325 instructions. -/
theorem ed25519PointAddShippedPart10_length :
    ed25519PointAddShippedPart10.length = 325 := by
  unfold ed25519PointAddShippedPart10
  simp only [List.length_append]
  rfl

/-- The body of `ed25519_point_add`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 155 segments,
    grouped in 10 parts. -/
def ed25519PointAddShippedBlock : List (JInstr 64) :=
  ed25519PointAddShippedPart01 ++ ed25519PointAddShippedPart02 ++
  ed25519PointAddShippedPart03 ++ ed25519PointAddShippedPart04 ++
  ed25519PointAddShippedPart05 ++ ed25519PointAddShippedPart06 ++
  ed25519PointAddShippedPart07 ++ ed25519PointAddShippedPart08 ++
  ed25519PointAddShippedPart09 ++ ed25519PointAddShippedPart10

/-- The frame instructions of `ed25519_point_add` before the body,
    which the block omits: each `pushq r` as `leaq -8(%rsp), %rsp` followed by the
    store of `r` at `0(%rsp)`, and the stack allocation as the instruction the text
    contains. -/
def ed25519PointAddShippedPrologue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-400) ]  -- l.5 `leaq -400(%rsp), %rsp`

/-- The frame instructions of `ed25519_point_add` after the body,
    which the block omits, `ret` excluded: the stack release as the instruction the
    text contains, and each `popq r` as the load of `r` from `0(%rsp)` followed by
    `leaq 8(%rsp), %rsp`. -/
def ed25519PointAddShippedEpilogue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 400 ]  -- l.5500 `leaq 400(%rsp), %rsp`

/-- The block has 4909 instructions; the count of each part is a lemma above. -/
theorem ed25519PointAddShippedBlock_length :
    ed25519PointAddShippedBlock.length = 4909 := by
  unfold ed25519PointAddShippedBlock
  simp only [List.length_append, ed25519PointAddShippedPart01_length,
    ed25519PointAddShippedPart02_length, ed25519PointAddShippedPart03_length,
    ed25519PointAddShippedPart04_length, ed25519PointAddShippedPart05_length,
    ed25519PointAddShippedPart06_length, ed25519PointAddShippedPart07_length,
    ed25519PointAddShippedPart08_length, ed25519PointAddShippedPart09_length,
    ed25519PointAddShippedPart10_length]

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
