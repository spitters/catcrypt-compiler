/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# `ed25519_comb_select_x86_from_lean` from the owned backend's output as a `JInstr 64` block

`ed25519CombSelectShippedBlock` is the body of the function
`ed25519_comb_select_x86_from_lean` in an x86-64 AT&T file printed by CatCrypt's
owned backend, translated instruction by instruction. The file's producer is
recorded in `PROVENANCE.md` next to it, where one exists.

## Provenance

* Source: `crates/catcrypt-ed25519/asm/ed25519_comb_select_x86_from_lean.s` in the
  `SSProve-lean` repository at commit `5a765fbc8aff83bff9eab87c81af0df5d9ae9944`
  (tracked and unchanged at that commit), file SHA-256
  `d78f511b133690bd60a1ba31a20429ff078b44bb71a55b3f87945b2ecf29f3c2`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 11 frame instructions,
  each checked by the importer: `pushq` of `%rbx`, `%r12`, `%r13`, `%r14`, `%r15`
  on entry and the `popq` sequence in reverse order on exit; `ret`.
* Every other instruction is kept, `%rsp`-relative moves included, as `storeMem
  "%rsp" off` and `loadMem r "%rsp" off`. `%rsp` is constant in the body.
* Registers keep their physical names (`"%rax"`, …, `"%r15"`, `"%rsp"`); no
  register allocation is involved.
* `JasminModel` keys memory by the name of the base register and a byte offset, at
  word granularity. A proof over this block is a statement about that model; it
  agrees with the processor where each base register holds one address throughout
  the block and distinct names address disjoint words.

The block has 168 instructions. Source instructions by mnemonic: `movq` 88,
`cmoveq` 64, `subq` 16.

## Main definitions

* `ed25519CombSelectShippedSeg01` … `ed25519CombSelectShippedSeg06`: the block in
  6 segments, each a literal `List (JInstr 64)`. A segment ends after a call, after
  the entry run of `%rsp` stores, before the exit run of `%rsp` loads, and after 32
  instructions.
* `ed25519CombSelectShippedBlock`: the block, the concatenation of the segments.

## Main results

* `ed25519CombSelectShippedBlock_length`: the block has 168 instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519CombSelectShipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 32 instructions from source lines 10–41. -/
def ed25519CombSelectShippedSeg01 : List (JInstr 64) :=
  [ .mov "%rcx" (.imm 0),  -- l.10 `movq $0, %rcx`
    .mov "%r8" (.imm 0),  -- l.11 `movq $0, %r8`
    .mov "%r9" (.imm 0),  -- l.12 `movq $0, %r9`
    .mov "%r10" (.imm 0),  -- l.13 `movq $0, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.14 `movq %rsi, %r11`
    .sub "%r11" (.imm 0),  -- l.15 `subq $0, %r11`
    .loadMem "%rax" "%rdi" 0,  -- l.16 `movq 0(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.17 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 8,  -- l.18 `movq 8(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.19 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 16,  -- l.20 `movq 16(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.21 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 24,  -- l.22 `movq 24(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.23 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.24 `movq %rsi, %r11`
    .sub "%r11" (.imm 1),  -- l.25 `subq $1, %r11`
    .loadMem "%rax" "%rdi" 32,  -- l.26 `movq 32(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.27 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 40,  -- l.28 `movq 40(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.29 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 48,  -- l.30 `movq 48(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.31 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 56,  -- l.32 `movq 56(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.33 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.34 `movq %rsi, %r11`
    .sub "%r11" (.imm 2),  -- l.35 `subq $2, %r11`
    .loadMem "%rax" "%rdi" 64,  -- l.36 `movq 64(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.37 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 72,  -- l.38 `movq 72(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.39 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 80,  -- l.40 `movq 80(%rdi), %rax`
    .cmove "%r9" (.reg "%rax") ]  -- l.41 `cmoveq %rax, %r9`

/-- Segment 2 of the body: the 32 instructions from source lines 42–73. -/
def ed25519CombSelectShippedSeg02 : List (JInstr 64) :=
  [ .loadMem "%rax" "%rdi" 88,  -- l.42 `movq 88(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.43 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.44 `movq %rsi, %r11`
    .sub "%r11" (.imm 3),  -- l.45 `subq $3, %r11`
    .loadMem "%rax" "%rdi" 96,  -- l.46 `movq 96(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.47 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 104,  -- l.48 `movq 104(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.49 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 112,  -- l.50 `movq 112(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.51 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 120,  -- l.52 `movq 120(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.53 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.54 `movq %rsi, %r11`
    .sub "%r11" (.imm 4),  -- l.55 `subq $4, %r11`
    .loadMem "%rax" "%rdi" 128,  -- l.56 `movq 128(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.57 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 136,  -- l.58 `movq 136(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.59 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 144,  -- l.60 `movq 144(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.61 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 152,  -- l.62 `movq 152(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.63 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.64 `movq %rsi, %r11`
    .sub "%r11" (.imm 5),  -- l.65 `subq $5, %r11`
    .loadMem "%rax" "%rdi" 160,  -- l.66 `movq 160(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.67 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 168,  -- l.68 `movq 168(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.69 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 176,  -- l.70 `movq 176(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.71 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 184,  -- l.72 `movq 184(%rdi), %rax`
    .cmove "%r10" (.reg "%rax") ]  -- l.73 `cmoveq %rax, %r10`

/-- Segment 3 of the body: the 32 instructions from source lines 74–105. -/
def ed25519CombSelectShippedSeg03 : List (JInstr 64) :=
  [ .mov "%r11" (.reg "%rsi"),  -- l.74 `movq %rsi, %r11`
    .sub "%r11" (.imm 6),  -- l.75 `subq $6, %r11`
    .loadMem "%rax" "%rdi" 192,  -- l.76 `movq 192(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.77 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 200,  -- l.78 `movq 200(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.79 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 208,  -- l.80 `movq 208(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.81 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 216,  -- l.82 `movq 216(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.83 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.84 `movq %rsi, %r11`
    .sub "%r11" (.imm 7),  -- l.85 `subq $7, %r11`
    .loadMem "%rax" "%rdi" 224,  -- l.86 `movq 224(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.87 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 232,  -- l.88 `movq 232(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.89 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 240,  -- l.90 `movq 240(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.91 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 248,  -- l.92 `movq 248(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.93 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.94 `movq %rsi, %r11`
    .sub "%r11" (.imm 8),  -- l.95 `subq $8, %r11`
    .loadMem "%rax" "%rdi" 256,  -- l.96 `movq 256(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.97 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 264,  -- l.98 `movq 264(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.99 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 272,  -- l.100 `movq 272(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.101 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 280,  -- l.102 `movq 280(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.103 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.104 `movq %rsi, %r11`
    .sub "%r11" (.imm 9) ]  -- l.105 `subq $9, %r11`

/-- Segment 4 of the body: the 32 instructions from source lines 106–137. -/
def ed25519CombSelectShippedSeg04 : List (JInstr 64) :=
  [ .loadMem "%rax" "%rdi" 288,  -- l.106 `movq 288(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.107 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 296,  -- l.108 `movq 296(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.109 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 304,  -- l.110 `movq 304(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.111 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 312,  -- l.112 `movq 312(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.113 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.114 `movq %rsi, %r11`
    .sub "%r11" (.imm 10),  -- l.115 `subq $10, %r11`
    .loadMem "%rax" "%rdi" 320,  -- l.116 `movq 320(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.117 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 328,  -- l.118 `movq 328(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.119 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 336,  -- l.120 `movq 336(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.121 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 344,  -- l.122 `movq 344(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.123 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.124 `movq %rsi, %r11`
    .sub "%r11" (.imm 11),  -- l.125 `subq $11, %r11`
    .loadMem "%rax" "%rdi" 352,  -- l.126 `movq 352(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.127 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 360,  -- l.128 `movq 360(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.129 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 368,  -- l.130 `movq 368(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.131 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 376,  -- l.132 `movq 376(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.133 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.134 `movq %rsi, %r11`
    .sub "%r11" (.imm 12),  -- l.135 `subq $12, %r11`
    .loadMem "%rax" "%rdi" 384,  -- l.136 `movq 384(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax") ]  -- l.137 `cmoveq %rax, %rcx`

/-- Segment 5 of the body: the 32 instructions from source lines 138–169. -/
def ed25519CombSelectShippedSeg05 : List (JInstr 64) :=
  [ .loadMem "%rax" "%rdi" 392,  -- l.138 `movq 392(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.139 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 400,  -- l.140 `movq 400(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.141 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 408,  -- l.142 `movq 408(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.143 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.144 `movq %rsi, %r11`
    .sub "%r11" (.imm 13),  -- l.145 `subq $13, %r11`
    .loadMem "%rax" "%rdi" 416,  -- l.146 `movq 416(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.147 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 424,  -- l.148 `movq 424(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.149 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 432,  -- l.150 `movq 432(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.151 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 440,  -- l.152 `movq 440(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.153 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.154 `movq %rsi, %r11`
    .sub "%r11" (.imm 14),  -- l.155 `subq $14, %r11`
    .loadMem "%rax" "%rdi" 448,  -- l.156 `movq 448(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.157 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 456,  -- l.158 `movq 456(%rdi), %rax`
    .cmove "%r8" (.reg "%rax"),  -- l.159 `cmoveq %rax, %r8`
    .loadMem "%rax" "%rdi" 464,  -- l.160 `movq 464(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.161 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 472,  -- l.162 `movq 472(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.163 `cmoveq %rax, %r10`
    .mov "%r11" (.reg "%rsi"),  -- l.164 `movq %rsi, %r11`
    .sub "%r11" (.imm 15),  -- l.165 `subq $15, %r11`
    .loadMem "%rax" "%rdi" 480,  -- l.166 `movq 480(%rdi), %rax`
    .cmove "%rcx" (.reg "%rax"),  -- l.167 `cmoveq %rax, %rcx`
    .loadMem "%rax" "%rdi" 488,  -- l.168 `movq 488(%rdi), %rax`
    .cmove "%r8" (.reg "%rax") ]  -- l.169 `cmoveq %rax, %r8`

/-- Segment 6 of the body: the 8 instructions from source lines 170–177. -/
def ed25519CombSelectShippedSeg06 : List (JInstr 64) :=
  [ .loadMem "%rax" "%rdi" 496,  -- l.170 `movq 496(%rdi), %rax`
    .cmove "%r9" (.reg "%rax"),  -- l.171 `cmoveq %rax, %r9`
    .loadMem "%rax" "%rdi" 504,  -- l.172 `movq 504(%rdi), %rax`
    .cmove "%r10" (.reg "%rax"),  -- l.173 `cmoveq %rax, %r10`
    .storeMem "%rdx" 0 (.reg "%rcx"),  -- l.174 `movq %rcx, 0(%rdx)`
    .storeMem "%rdx" 8 (.reg "%r8"),  -- l.175 `movq %r8, 8(%rdx)`
    .storeMem "%rdx" 16 (.reg "%r9"),  -- l.176 `movq %r9, 16(%rdx)`
    .storeMem "%rdx" 24 (.reg "%r10") ]  -- l.177 `movq %r10, 24(%rdx)`

/-- The body of `ed25519_comb_select_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 6 segments. -/
def ed25519CombSelectShippedBlock : List (JInstr 64) :=
  ed25519CombSelectShippedSeg01 ++ ed25519CombSelectShippedSeg02 ++
  ed25519CombSelectShippedSeg03 ++ ed25519CombSelectShippedSeg04 ++
  ed25519CombSelectShippedSeg05 ++ ed25519CombSelectShippedSeg06

/-- The block has 168 instructions; the count of each segment is computed by `rfl`. -/
theorem ed25519CombSelectShippedBlock_length :
    ed25519CombSelectShippedBlock.length = 168 := by
  unfold ed25519CombSelectShippedBlock
  simp only [List.length_append]
  rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519CombSelectShipped
