/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
/-
The instruction list in this file is a translation of `x86_att/p384/bignum_montmul_p384.S` from
s2n-bignum (https://github.com/awslabs/s2n-bignum), which carries the notice:

  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
  SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# s2n-bignum's `bignum_montmul_p384` as a `JInstr 64` block

`s2nMontmulP384Block` is the body of s2n-bignum's hand-written x86-64 Montgomery
multiplication modulo `p_384 = 2^384 - 2^128 - 2^96 + 2^32 - 1`: for six-limb inputs
`x`, `y` it writes `z = x * y * 2^(-384) mod p_384`, under the precondition
`x * y <= 2^384 * p_384` stated in the source (it holds when `x, y < p_384`).

## Provenance

* Source: `x86_att/p384/bignum_montmul_p384.S` in s2n-bignum at commit
  `7bd7c8ca1f3316fbc705d464e23f31358aff9e8a`, file SHA-256
  `d9521c0e0c8308a3b7426a6ebc84aa987e79dbaca075876f083565adcf425b4f`.
  s2n-bignum is licensed Apache-2.0 OR ISC OR MIT-0; its copyright notice is
  reproduced in the comment at the top of this file.
* Produced by `bench/s2n_import/import_s2n.sh`, which runs the C preprocessor over
  the source and translates each instruction to one `JInstr 64` constructor. The
  comment after each element gives the source line of the instruction (a macro
  invocation, for the instructions of `mulpadd` and `montredc`) and its text.
  The importer is not trusted: whether this list computes the Montgomery product is
  the subject of the correctness proof over it in a sibling module.
* Omitted from the list: the assembler directives and the frame, which is
  `endbr64`, `pushq` of `%rbx`, `%rbp`, `%r12`, `%r13`, `%r14`, `%r15` on entry, and the
  matching `popq` sequence and `retq` on exit (14 instructions).
* Registers keep their physical names (`"%rax"`, …, `"%r15"`); no register
  allocation is involved.
* The source uses 32-bit instruction forms in three positions, each translated to
  the 64-bit form with equal register value and flags: 15 `xorl %r, %r` zeroing
  idioms to `xor_`, 8 `movl $imm, %r` zero-extending moves to `mov`, and 6
  `adcl %ebp, %ebp` to `adc`, the last accepted only where the preceding instruction
  that touches `%rbp` is `xorl %ebp, %ebp` in the same macro expansion.

The block has 264 instructions: `mulxq` 48, `adcq` 44, `adoxq` 30, `sbbq` 30,
`movq` 26, `adcxq` 25, `xorl` 15, `addq` 14, `movl` 8, `adcl` 6, `cmovnzq` 6,
`shlq` 6, `subq` 6.

## Calling convention

System V AMD64, as in s2n-bignum's header: `%rdi` points to the six output limbs
`z`, `%rsi` to the input limbs `x`, `%rdx` to the input limbs `y`, each
little-endian at offsets `0, 8, …, 40`. The block copies `%rdx` to `%rcx` and reads
`y` through `%rcx`, reads `x` through `%rsi`, and writes `z` through `%rdi`. The
omitted frame saves and restores `%rbx`, `%rbp`, `%r12`, `%r13`, `%r14`, `%r15`.

## Main results

* `s2nMontmulP384Seg01` … `s2nMontmulP384Seg17`: the block in 17 segments, one per
  paragraph of the source (a run of instructions with no blank or comment line between
  them), each a literal `List (JInstr 64)`.
* `s2nMontmulP384Block`: the block, the concatenation of the segments.
* `s2nMontmulP384Block_length`: the block has 264 instructions.

Provenance class: `@imported theorems: s2nMontmulP384_correct`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 1 instruction from source line 113. -/
def s2nMontmulP384Seg01 : List (JInstr 64) :=
  [ .mov "%rcx" (.reg "%rdx") ]  -- l.113 `movq %rdx, %rcx`

/-- Segment 2 of the body: the 14 instructions from source lines 119–132. -/
def s2nMontmulP384Seg02 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rcx" 0,  -- l.119 `movq (%rcx), %rdx`
    .xor_ "%r15" (.reg "%r15"),  -- l.120 `xorl %r15d, %r15d`
    .mulxMem "%r9" "%r8" (.reg "%rdx") "%rsi" 0,  -- l.121 `mulxq (%rsi), %r8, %r9`
    .mulxMem "%r10" "%rbx" (.reg "%rdx") "%rsi" 8,  -- l.122 `mulxq 8(%rsi), %rbx, %r10`
    .add "%r9" (.reg "%rbx"),  -- l.123 `addq %rbx, %r9`
    .mulxMem "%r11" "%rbx" (.reg "%rdx") "%rsi" 16,  -- l.124 `mulxq 16(%rsi), %rbx, %r11`
    .adc "%r10" (.reg "%rbx"),  -- l.125 `adcq %rbx, %r10`
    .mulxMem "%r12" "%rbx" (.reg "%rdx") "%rsi" 24,  -- l.126 `mulxq 24(%rsi), %rbx, %r12`
    .adc "%r11" (.reg "%rbx"),  -- l.127 `adcq %rbx, %r11`
    .mulxMem "%r13" "%rbx" (.reg "%rdx") "%rsi" 32,  -- l.128 `mulxq 32(%rsi), %rbx, %r13`
    .adc "%r12" (.reg "%rbx"),  -- l.129 `adcq %rbx, %r12`
    .mulxMem "%r14" "%rbx" (.reg "%rdx") "%rsi" 40,  -- l.130 `mulxq 40(%rsi), %rbx, %r14`
    .adc "%r13" (.reg "%rbx"),  -- l.131 `adcq %rbx, %r13`
    .adc "%r14" (.reg "%r15") ]  -- l.132 `adcq %r15, %r14`

/-- Segment 3 of the body: the 19 instructions from source line 136. -/
def s2nMontmulP384Seg03 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r8"),  -- l.136 `movq %r8, %rdx`
    .shl "%rdx" (.imm 32),  -- l.136 `shlq $32, %rdx`
    .add "%rdx" (.reg "%r8"),  -- l.136 `addq %r8, %rdx`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.136 `xorl %ebp, %ebp`
    .mov "%rax" (.imm 18446744069414584321),  -- l.136 `movq $0xffffffff00000001, %rax`
    .mulx "%rax" "%rbx" (.reg "%rdx") (.reg "%rax"),  -- l.136 `mulxq %rax, %rbx, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.136 `movl $0x00000000ffffffff, %ebx`
    .mulx "%rbx" "%r8" (.reg "%rdx") (.reg "%rbx"),  -- l.136 `mulxq %rbx, %r8, %rbx`
    .adc "%rax" (.reg "%r8"),  -- l.136 `adcq %r8, %rax`
    .adc "%rbx" (.reg "%rdx"),  -- l.136 `adcq %rdx, %rbx`
    .adc "%rbp" (.reg "%rbp"),  -- l.136 `adcl %ebp, %ebp`
    .sub "%r9" (.reg "%rax"),  -- l.136 `subq %rax, %r9`
    .sbb "%r10" (.reg "%rbx"),  -- l.136 `sbbq %rbx, %r10`
    .sbb "%r11" (.reg "%rbp"),  -- l.136 `sbbq %rbp, %r11`
    .sbb "%r12" (.imm 0),  -- l.136 `sbbq $0, %r12`
    .sbb "%r13" (.imm 0),  -- l.136 `sbbq $0, %r13`
    .sbb "%rdx" (.imm 0),  -- l.136 `sbbq $0, %rdx`
    .add "%r14" (.reg "%rdx"),  -- l.136 `addq %rdx, %r14`
    .adc "%r15" (.imm 0) ]  -- l.136 `adcq $0, %r15`

/-- Segment 4 of the body: the 22 instructions from source lines 140–151. -/
def s2nMontmulP384Seg04 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rcx" 8,  -- l.140 `movq 8(%rcx), %rdx`
    .xor_ "%r8" (.reg "%r8"),  -- l.141 `xorl %r8d, %r8d`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 0,  -- l.142 `mulxq (%rsi), %rax, %rbx`
    .adcx "%r9" (.reg "%rax"),  -- l.142 `adcxq %rax, %r9`
    .adox "%r10" (.reg "%rbx"),  -- l.142 `adoxq %rbx, %r10`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 8,  -- l.143 `mulxq 8(%rsi), %rax, %rbx`
    .adcx "%r10" (.reg "%rax"),  -- l.143 `adcxq %rax, %r10`
    .adox "%r11" (.reg "%rbx"),  -- l.143 `adoxq %rbx, %r11`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 16,  -- l.144 `mulxq 16(%rsi), %rax, %rbx`
    .adcx "%r11" (.reg "%rax"),  -- l.144 `adcxq %rax, %r11`
    .adox "%r12" (.reg "%rbx"),  -- l.144 `adoxq %rbx, %r12`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 24,  -- l.145 `mulxq 24(%rsi), %rax, %rbx`
    .adcx "%r12" (.reg "%rax"),  -- l.145 `adcxq %rax, %r12`
    .adox "%r13" (.reg "%rbx"),  -- l.145 `adoxq %rbx, %r13`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 32,  -- l.146 `mulxq 32(%rsi), %rax, %rbx`
    .adcx "%r13" (.reg "%rax"),  -- l.146 `adcxq %rax, %r13`
    .adox "%r14" (.reg "%rbx"),  -- l.146 `adoxq %rbx, %r14`
    .adox "%r15" (.reg "%r8"),  -- l.147 `adoxq %r8, %r15`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 40,  -- l.148 `mulxq 40(%rsi), %rax, %rbx`
    .adc "%r14" (.reg "%rax"),  -- l.149 `adcq %rax, %r14`
    .adc "%r15" (.reg "%rbx"),  -- l.150 `adcq %rbx, %r15`
    .adc "%r8" (.reg "%r8") ]  -- l.151 `adcq %r8, %r8`

/-- Segment 5 of the body: the 19 instructions from source line 155. -/
def s2nMontmulP384Seg05 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r9"),  -- l.155 `movq %r9, %rdx`
    .shl "%rdx" (.imm 32),  -- l.155 `shlq $32, %rdx`
    .add "%rdx" (.reg "%r9"),  -- l.155 `addq %r9, %rdx`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.155 `xorl %ebp, %ebp`
    .mov "%rax" (.imm 18446744069414584321),  -- l.155 `movq $0xffffffff00000001, %rax`
    .mulx "%rax" "%rbx" (.reg "%rdx") (.reg "%rax"),  -- l.155 `mulxq %rax, %rbx, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.155 `movl $0x00000000ffffffff, %ebx`
    .mulx "%rbx" "%r9" (.reg "%rdx") (.reg "%rbx"),  -- l.155 `mulxq %rbx, %r9, %rbx`
    .adc "%rax" (.reg "%r9"),  -- l.155 `adcq %r9, %rax`
    .adc "%rbx" (.reg "%rdx"),  -- l.155 `adcq %rdx, %rbx`
    .adc "%rbp" (.reg "%rbp"),  -- l.155 `adcl %ebp, %ebp`
    .sub "%r10" (.reg "%rax"),  -- l.155 `subq %rax, %r10`
    .sbb "%r11" (.reg "%rbx"),  -- l.155 `sbbq %rbx, %r11`
    .sbb "%r12" (.reg "%rbp"),  -- l.155 `sbbq %rbp, %r12`
    .sbb "%r13" (.imm 0),  -- l.155 `sbbq $0, %r13`
    .sbb "%r14" (.imm 0),  -- l.155 `sbbq $0, %r14`
    .sbb "%rdx" (.imm 0),  -- l.155 `sbbq $0, %rdx`
    .add "%r15" (.reg "%rdx"),  -- l.155 `addq %rdx, %r15`
    .adc "%r8" (.imm 0) ]  -- l.155 `adcq $0, %r8`

/-- Segment 6 of the body: the 22 instructions from source lines 159–170. -/
def s2nMontmulP384Seg06 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rcx" 16,  -- l.159 `movq 16(%rcx), %rdx`
    .xor_ "%r9" (.reg "%r9"),  -- l.160 `xorl %r9d, %r9d`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 0,  -- l.161 `mulxq (%rsi), %rax, %rbx`
    .adcx "%r10" (.reg "%rax"),  -- l.161 `adcxq %rax, %r10`
    .adox "%r11" (.reg "%rbx"),  -- l.161 `adoxq %rbx, %r11`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 8,  -- l.162 `mulxq 8(%rsi), %rax, %rbx`
    .adcx "%r11" (.reg "%rax"),  -- l.162 `adcxq %rax, %r11`
    .adox "%r12" (.reg "%rbx"),  -- l.162 `adoxq %rbx, %r12`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 16,  -- l.163 `mulxq 16(%rsi), %rax, %rbx`
    .adcx "%r12" (.reg "%rax"),  -- l.163 `adcxq %rax, %r12`
    .adox "%r13" (.reg "%rbx"),  -- l.163 `adoxq %rbx, %r13`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 24,  -- l.164 `mulxq 24(%rsi), %rax, %rbx`
    .adcx "%r13" (.reg "%rax"),  -- l.164 `adcxq %rax, %r13`
    .adox "%r14" (.reg "%rbx"),  -- l.164 `adoxq %rbx, %r14`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 32,  -- l.165 `mulxq 32(%rsi), %rax, %rbx`
    .adcx "%r14" (.reg "%rax"),  -- l.165 `adcxq %rax, %r14`
    .adox "%r15" (.reg "%rbx"),  -- l.165 `adoxq %rbx, %r15`
    .adox "%r8" (.reg "%r9"),  -- l.166 `adoxq %r9, %r8`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 40,  -- l.167 `mulxq 40(%rsi), %rax, %rbx`
    .adc "%r15" (.reg "%rax"),  -- l.168 `adcq %rax, %r15`
    .adc "%r8" (.reg "%rbx"),  -- l.169 `adcq %rbx, %r8`
    .adc "%r9" (.reg "%r9") ]  -- l.170 `adcq %r9, %r9`

/-- Segment 7 of the body: the 19 instructions from source line 174. -/
def s2nMontmulP384Seg07 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r10"),  -- l.174 `movq %r10, %rdx`
    .shl "%rdx" (.imm 32),  -- l.174 `shlq $32, %rdx`
    .add "%rdx" (.reg "%r10"),  -- l.174 `addq %r10, %rdx`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.174 `xorl %ebp, %ebp`
    .mov "%rax" (.imm 18446744069414584321),  -- l.174 `movq $0xffffffff00000001, %rax`
    .mulx "%rax" "%rbx" (.reg "%rdx") (.reg "%rax"),  -- l.174 `mulxq %rax, %rbx, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.174 `movl $0x00000000ffffffff, %ebx`
    .mulx "%rbx" "%r10" (.reg "%rdx") (.reg "%rbx"),  -- l.174 `mulxq %rbx, %r10, %rbx`
    .adc "%rax" (.reg "%r10"),  -- l.174 `adcq %r10, %rax`
    .adc "%rbx" (.reg "%rdx"),  -- l.174 `adcq %rdx, %rbx`
    .adc "%rbp" (.reg "%rbp"),  -- l.174 `adcl %ebp, %ebp`
    .sub "%r11" (.reg "%rax"),  -- l.174 `subq %rax, %r11`
    .sbb "%r12" (.reg "%rbx"),  -- l.174 `sbbq %rbx, %r12`
    .sbb "%r13" (.reg "%rbp"),  -- l.174 `sbbq %rbp, %r13`
    .sbb "%r14" (.imm 0),  -- l.174 `sbbq $0, %r14`
    .sbb "%r15" (.imm 0),  -- l.174 `sbbq $0, %r15`
    .sbb "%rdx" (.imm 0),  -- l.174 `sbbq $0, %rdx`
    .add "%r8" (.reg "%rdx"),  -- l.174 `addq %rdx, %r8`
    .adc "%r9" (.imm 0) ]  -- l.174 `adcq $0, %r9`

/-- Segment 8 of the body: the 22 instructions from source lines 178–189. -/
def s2nMontmulP384Seg08 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rcx" 24,  -- l.178 `movq 24(%rcx), %rdx`
    .xor_ "%r10" (.reg "%r10"),  -- l.179 `xorl %r10d, %r10d`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 0,  -- l.180 `mulxq (%rsi), %rax, %rbx`
    .adcx "%r11" (.reg "%rax"),  -- l.180 `adcxq %rax, %r11`
    .adox "%r12" (.reg "%rbx"),  -- l.180 `adoxq %rbx, %r12`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 8,  -- l.181 `mulxq 8(%rsi), %rax, %rbx`
    .adcx "%r12" (.reg "%rax"),  -- l.181 `adcxq %rax, %r12`
    .adox "%r13" (.reg "%rbx"),  -- l.181 `adoxq %rbx, %r13`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 16,  -- l.182 `mulxq 16(%rsi), %rax, %rbx`
    .adcx "%r13" (.reg "%rax"),  -- l.182 `adcxq %rax, %r13`
    .adox "%r14" (.reg "%rbx"),  -- l.182 `adoxq %rbx, %r14`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 24,  -- l.183 `mulxq 24(%rsi), %rax, %rbx`
    .adcx "%r14" (.reg "%rax"),  -- l.183 `adcxq %rax, %r14`
    .adox "%r15" (.reg "%rbx"),  -- l.183 `adoxq %rbx, %r15`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 32,  -- l.184 `mulxq 32(%rsi), %rax, %rbx`
    .adcx "%r15" (.reg "%rax"),  -- l.184 `adcxq %rax, %r15`
    .adox "%r8" (.reg "%rbx"),  -- l.184 `adoxq %rbx, %r8`
    .adox "%r9" (.reg "%r10"),  -- l.185 `adoxq %r10, %r9`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 40,  -- l.186 `mulxq 40(%rsi), %rax, %rbx`
    .adc "%r8" (.reg "%rax"),  -- l.187 `adcq %rax, %r8`
    .adc "%r9" (.reg "%rbx"),  -- l.188 `adcq %rbx, %r9`
    .adc "%r10" (.reg "%r10") ]  -- l.189 `adcq %r10, %r10`

/-- Segment 9 of the body: the 19 instructions from source line 193. -/
def s2nMontmulP384Seg09 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r11"),  -- l.193 `movq %r11, %rdx`
    .shl "%rdx" (.imm 32),  -- l.193 `shlq $32, %rdx`
    .add "%rdx" (.reg "%r11"),  -- l.193 `addq %r11, %rdx`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.193 `xorl %ebp, %ebp`
    .mov "%rax" (.imm 18446744069414584321),  -- l.193 `movq $0xffffffff00000001, %rax`
    .mulx "%rax" "%rbx" (.reg "%rdx") (.reg "%rax"),  -- l.193 `mulxq %rax, %rbx, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.193 `movl $0x00000000ffffffff, %ebx`
    .mulx "%rbx" "%r11" (.reg "%rdx") (.reg "%rbx"),  -- l.193 `mulxq %rbx, %r11, %rbx`
    .adc "%rax" (.reg "%r11"),  -- l.193 `adcq %r11, %rax`
    .adc "%rbx" (.reg "%rdx"),  -- l.193 `adcq %rdx, %rbx`
    .adc "%rbp" (.reg "%rbp"),  -- l.193 `adcl %ebp, %ebp`
    .sub "%r12" (.reg "%rax"),  -- l.193 `subq %rax, %r12`
    .sbb "%r13" (.reg "%rbx"),  -- l.193 `sbbq %rbx, %r13`
    .sbb "%r14" (.reg "%rbp"),  -- l.193 `sbbq %rbp, %r14`
    .sbb "%r15" (.imm 0),  -- l.193 `sbbq $0, %r15`
    .sbb "%r8" (.imm 0),  -- l.193 `sbbq $0, %r8`
    .sbb "%rdx" (.imm 0),  -- l.193 `sbbq $0, %rdx`
    .add "%r9" (.reg "%rdx"),  -- l.193 `addq %rdx, %r9`
    .adc "%r10" (.imm 0) ]  -- l.193 `adcq $0, %r10`

/-- Segment 10 of the body: the 22 instructions from source lines 197–208. -/
def s2nMontmulP384Seg10 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rcx" 32,  -- l.197 `movq 32(%rcx), %rdx`
    .xor_ "%r11" (.reg "%r11"),  -- l.198 `xorl %r11d, %r11d`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 0,  -- l.199 `mulxq (%rsi), %rax, %rbx`
    .adcx "%r12" (.reg "%rax"),  -- l.199 `adcxq %rax, %r12`
    .adox "%r13" (.reg "%rbx"),  -- l.199 `adoxq %rbx, %r13`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 8,  -- l.200 `mulxq 8(%rsi), %rax, %rbx`
    .adcx "%r13" (.reg "%rax"),  -- l.200 `adcxq %rax, %r13`
    .adox "%r14" (.reg "%rbx"),  -- l.200 `adoxq %rbx, %r14`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 16,  -- l.201 `mulxq 16(%rsi), %rax, %rbx`
    .adcx "%r14" (.reg "%rax"),  -- l.201 `adcxq %rax, %r14`
    .adox "%r15" (.reg "%rbx"),  -- l.201 `adoxq %rbx, %r15`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 24,  -- l.202 `mulxq 24(%rsi), %rax, %rbx`
    .adcx "%r15" (.reg "%rax"),  -- l.202 `adcxq %rax, %r15`
    .adox "%r8" (.reg "%rbx"),  -- l.202 `adoxq %rbx, %r8`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 32,  -- l.203 `mulxq 32(%rsi), %rax, %rbx`
    .adcx "%r8" (.reg "%rax"),  -- l.203 `adcxq %rax, %r8`
    .adox "%r9" (.reg "%rbx"),  -- l.203 `adoxq %rbx, %r9`
    .adox "%r10" (.reg "%r11"),  -- l.204 `adoxq %r11, %r10`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 40,  -- l.205 `mulxq 40(%rsi), %rax, %rbx`
    .adc "%r9" (.reg "%rax"),  -- l.206 `adcq %rax, %r9`
    .adc "%r10" (.reg "%rbx"),  -- l.207 `adcq %rbx, %r10`
    .adc "%r11" (.reg "%r11") ]  -- l.208 `adcq %r11, %r11`

/-- Segment 11 of the body: the 19 instructions from source line 212. -/
def s2nMontmulP384Seg11 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r12"),  -- l.212 `movq %r12, %rdx`
    .shl "%rdx" (.imm 32),  -- l.212 `shlq $32, %rdx`
    .add "%rdx" (.reg "%r12"),  -- l.212 `addq %r12, %rdx`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.212 `xorl %ebp, %ebp`
    .mov "%rax" (.imm 18446744069414584321),  -- l.212 `movq $0xffffffff00000001, %rax`
    .mulx "%rax" "%rbx" (.reg "%rdx") (.reg "%rax"),  -- l.212 `mulxq %rax, %rbx, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.212 `movl $0x00000000ffffffff, %ebx`
    .mulx "%rbx" "%r12" (.reg "%rdx") (.reg "%rbx"),  -- l.212 `mulxq %rbx, %r12, %rbx`
    .adc "%rax" (.reg "%r12"),  -- l.212 `adcq %r12, %rax`
    .adc "%rbx" (.reg "%rdx"),  -- l.212 `adcq %rdx, %rbx`
    .adc "%rbp" (.reg "%rbp"),  -- l.212 `adcl %ebp, %ebp`
    .sub "%r13" (.reg "%rax"),  -- l.212 `subq %rax, %r13`
    .sbb "%r14" (.reg "%rbx"),  -- l.212 `sbbq %rbx, %r14`
    .sbb "%r15" (.reg "%rbp"),  -- l.212 `sbbq %rbp, %r15`
    .sbb "%r8" (.imm 0),  -- l.212 `sbbq $0, %r8`
    .sbb "%r9" (.imm 0),  -- l.212 `sbbq $0, %r9`
    .sbb "%rdx" (.imm 0),  -- l.212 `sbbq $0, %rdx`
    .add "%r10" (.reg "%rdx"),  -- l.212 `addq %rdx, %r10`
    .adc "%r11" (.imm 0) ]  -- l.212 `adcq $0, %r11`

/-- Segment 12 of the body: the 22 instructions from source lines 216–227. -/
def s2nMontmulP384Seg12 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rcx" 40,  -- l.216 `movq 40(%rcx), %rdx`
    .xor_ "%r12" (.reg "%r12"),  -- l.217 `xorl %r12d, %r12d`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 0,  -- l.218 `mulxq (%rsi), %rax, %rbx`
    .adcx "%r13" (.reg "%rax"),  -- l.218 `adcxq %rax, %r13`
    .adox "%r14" (.reg "%rbx"),  -- l.218 `adoxq %rbx, %r14`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 8,  -- l.219 `mulxq 8(%rsi), %rax, %rbx`
    .adcx "%r14" (.reg "%rax"),  -- l.219 `adcxq %rax, %r14`
    .adox "%r15" (.reg "%rbx"),  -- l.219 `adoxq %rbx, %r15`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 16,  -- l.220 `mulxq 16(%rsi), %rax, %rbx`
    .adcx "%r15" (.reg "%rax"),  -- l.220 `adcxq %rax, %r15`
    .adox "%r8" (.reg "%rbx"),  -- l.220 `adoxq %rbx, %r8`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 24,  -- l.221 `mulxq 24(%rsi), %rax, %rbx`
    .adcx "%r8" (.reg "%rax"),  -- l.221 `adcxq %rax, %r8`
    .adox "%r9" (.reg "%rbx"),  -- l.221 `adoxq %rbx, %r9`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 32,  -- l.222 `mulxq 32(%rsi), %rax, %rbx`
    .adcx "%r9" (.reg "%rax"),  -- l.222 `adcxq %rax, %r9`
    .adox "%r10" (.reg "%rbx"),  -- l.222 `adoxq %rbx, %r10`
    .adox "%r11" (.reg "%r12"),  -- l.223 `adoxq %r12, %r11`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 40,  -- l.224 `mulxq 40(%rsi), %rax, %rbx`
    .adc "%r10" (.reg "%rax"),  -- l.225 `adcq %rax, %r10`
    .adc "%r11" (.reg "%rbx"),  -- l.226 `adcq %rbx, %r11`
    .adc "%r12" (.reg "%r12") ]  -- l.227 `adcq %r12, %r12`

/-- Segment 13 of the body: the 19 instructions from source line 231. -/
def s2nMontmulP384Seg13 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r13"),  -- l.231 `movq %r13, %rdx`
    .shl "%rdx" (.imm 32),  -- l.231 `shlq $32, %rdx`
    .add "%rdx" (.reg "%r13"),  -- l.231 `addq %r13, %rdx`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.231 `xorl %ebp, %ebp`
    .mov "%rax" (.imm 18446744069414584321),  -- l.231 `movq $0xffffffff00000001, %rax`
    .mulx "%rax" "%rbx" (.reg "%rdx") (.reg "%rax"),  -- l.231 `mulxq %rax, %rbx, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.231 `movl $0x00000000ffffffff, %ebx`
    .mulx "%rbx" "%r13" (.reg "%rdx") (.reg "%rbx"),  -- l.231 `mulxq %rbx, %r13, %rbx`
    .adc "%rax" (.reg "%r13"),  -- l.231 `adcq %r13, %rax`
    .adc "%rbx" (.reg "%rdx"),  -- l.231 `adcq %rdx, %rbx`
    .adc "%rbp" (.reg "%rbp"),  -- l.231 `adcl %ebp, %ebp`
    .sub "%r14" (.reg "%rax"),  -- l.231 `subq %rax, %r14`
    .sbb "%r15" (.reg "%rbx"),  -- l.231 `sbbq %rbx, %r15`
    .sbb "%r8" (.reg "%rbp"),  -- l.231 `sbbq %rbp, %r8`
    .sbb "%r9" (.imm 0),  -- l.231 `sbbq $0, %r9`
    .sbb "%r10" (.imm 0),  -- l.231 `sbbq $0, %r10`
    .sbb "%rdx" (.imm 0),  -- l.231 `sbbq $0, %rdx`
    .add "%r11" (.reg "%rdx"),  -- l.231 `addq %rdx, %r11`
    .adc "%r12" (.imm 0) ]  -- l.231 `adcq $0, %r12`

/-- Segment 14 of the body: the 3 instructions from source lines 238–240. -/
def s2nMontmulP384Seg14 : List (JInstr 64) :=
  [ .xor_ "%rdx" (.reg "%rdx"),  -- l.238 `xorl %edx, %edx`
    .xor_ "%rbp" (.reg "%rbp"),  -- l.239 `xorl %ebp, %ebp`
    .xor_ "%r13" (.reg "%r13") ]  -- l.240 `xorl %r13d, %r13d`

/-- Segment 15 of the body: the 10 instructions from source lines 242–251. -/
def s2nMontmulP384Seg15 : List (JInstr 64) :=
  [ .mov "%rax" (.imm 18446744069414584321),  -- l.242 `movq $0xffffffff00000001, %rax`
    .add "%rax" (.reg "%r14"),  -- l.243 `addq %r14, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.244 `movl $0x00000000ffffffff, %ebx`
    .adc "%rbx" (.reg "%r15"),  -- l.245 `adcq %r15, %rbx`
    .mov "%rcx" (.imm 1),  -- l.246 `movl $0x0000000000000001, %ecx`
    .adc "%rcx" (.reg "%r8"),  -- l.247 `adcq %r8, %rcx`
    .adc "%rdx" (.reg "%r9"),  -- l.248 `adcq %r9, %rdx`
    .adc "%rbp" (.reg "%r10"),  -- l.249 `adcq %r10, %rbp`
    .adc "%r13" (.reg "%r11"),  -- l.250 `adcq %r11, %r13`
    .adc "%r12" (.imm 0) ]  -- l.251 `adcq $0, %r12`

/-- Segment 16 of the body: the 6 instructions from source lines 256–261. -/
def s2nMontmulP384Seg16 : List (JInstr 64) :=
  [ .cmovne "%r14" (.reg "%rax"),  -- l.256 `cmovnzq %rax, %r14`
    .cmovne "%r15" (.reg "%rbx"),  -- l.257 `cmovnzq %rbx, %r15`
    .cmovne "%r8" (.reg "%rcx"),  -- l.258 `cmovnzq %rcx, %r8`
    .cmovne "%r9" (.reg "%rdx"),  -- l.259 `cmovnzq %rdx, %r9`
    .cmovne "%r10" (.reg "%rbp"),  -- l.260 `cmovnzq %rbp, %r10`
    .cmovne "%r11" (.reg "%r13") ]  -- l.261 `cmovnzq %r13, %r11`

/-- Segment 17 of the body: the 6 instructions from source lines 265–270. -/
def s2nMontmulP384Seg17 : List (JInstr 64) :=
  [ .storeMem "%rdi" 0 (.reg "%r14"),  -- l.265 `movq %r14, (%rdi)`
    .storeMem "%rdi" 8 (.reg "%r15"),  -- l.266 `movq %r15, 8(%rdi)`
    .storeMem "%rdi" 16 (.reg "%r8"),  -- l.267 `movq %r8, 16(%rdi)`
    .storeMem "%rdi" 24 (.reg "%r9"),  -- l.268 `movq %r9, 24(%rdi)`
    .storeMem "%rdi" 32 (.reg "%r10"),  -- l.269 `movq %r10, 32(%rdi)`
    .storeMem "%rdi" 40 (.reg "%r11") ]  -- l.270 `movq %r11, 40(%rdi)`

/-- The body of s2n-bignum's `bignum_montmul_p384`, translated instruction by instruction
    by `bench/s2n_import/import_s2n.sh`: the concatenation of its 17 segments. -/
def s2nMontmulP384Block : List (JInstr 64) :=
  s2nMontmulP384Seg01 ++ s2nMontmulP384Seg02 ++ s2nMontmulP384Seg03 ++
  s2nMontmulP384Seg04 ++ s2nMontmulP384Seg05 ++ s2nMontmulP384Seg06 ++
  s2nMontmulP384Seg07 ++ s2nMontmulP384Seg08 ++ s2nMontmulP384Seg09 ++
  s2nMontmulP384Seg10 ++ s2nMontmulP384Seg11 ++ s2nMontmulP384Seg12 ++
  s2nMontmulP384Seg13 ++ s2nMontmulP384Seg14 ++ s2nMontmulP384Seg15 ++
  s2nMontmulP384Seg16 ++ s2nMontmulP384Seg17

/-- The block has 264 instructions. The length of each segment is computed by `rfl`;
    the whole list at once exceeds the default recursion depth. -/
theorem s2nMontmulP384Block_length : s2nMontmulP384Block.length = 264 := by
  simp only [s2nMontmulP384Block, List.length_append]; rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
