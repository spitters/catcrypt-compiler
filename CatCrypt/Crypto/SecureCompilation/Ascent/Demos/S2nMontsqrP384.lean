/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
/-
The instruction list in this file is a translation of `x86_att/p384/bignum_montsqr_p384.S` from
s2n-bignum (https://github.com/awslabs/s2n-bignum), which carries the notice:

  Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
  SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# s2n-bignum's `bignum_montsqr_p384` as a `JInstr 64` block

`s2nMontsqrP384Block` is the body of s2n-bignum's hand-written x86-64 Montgomery
squaring modulo `p_384 = 2^384 - 2^128 - 2^96 + 2^32 - 1`: for a six-limb input `x`
it writes `z = x^2 * 2^(-384) mod p_384`, under the precondition
`x^2 <= 2^384 * p_384` stated in the source (it holds when `x < p_384`).

## Provenance

* Source: `x86_att/p384/bignum_montsqr_p384.S` in s2n-bignum at commit
  `7bd7c8ca1f3316fbc705d464e23f31358aff9e8a`, file SHA-256
  `5e2b95a1592b11aed7d3a14d8d02f5b8a0669614b7fe7e8ac5bc89959918b01b`.
  s2n-bignum is licensed Apache-2.0 OR ISC OR MIT-0; its copyright notice is
  reproduced in the comment at the top of this file.
* Produced by `bench/s2n_import/import_s2n.sh`, which runs the C preprocessor over
  the source and translates each instruction to one `JInstr 64` constructor. The
  comment after each element gives the source line of the instruction (a macro
  invocation, for the instructions of `mulpadd` and `montreds`) and its text.
  The importer is not trusted: whether this list computes the Montgomery square is
  the subject of the correctness proof over it in a sibling module.
* Omitted from the list: the assembler directives and the frame, which is
  `endbr64`, `pushq` of `%rbx`, `%rbp`, `%r12`, `%r13`, `%r14`, `%r15` on entry, and the
  matching `popq` sequence and `retq` on exit (14 instructions).
* Registers keep their physical names (`"%rax"`, …, `"%r15"`); no register
  allocation is involved.
* The source uses two 32-bit instruction forms, each translated to the 64-bit form
  with equal register value and flags: 2 `xorl %r, %r` zeroing idioms to `xor_` and
  17 `movl $imm, %r` zero-extending moves to `mov`.

The block has 230 instructions: `movq` 40, `mulxq` 33, `sbbq` 30, `adcq` 26,
`adcxq` 23, `adoxq` 23, `movl` 17, `addq` 14, `cmovnzq` 6, `shlq` 6, `subq` 6,
`xorq` 4, `xorl` 2.

## Calling convention

System V AMD64, as in s2n-bignum's header: `%rdi` points to the six output limbs
`z` and `%rsi` to the six input limbs `x`, each little-endian at offsets
`0, 8, …, 40`. The block reads `x` through `%rsi` until the last squaring term
overwrites `%rsi`, uses the output limb `z[0]` to hold `%rbx` during the
reduction, and writes `z` through `%rdi`. The omitted frame saves and restores
`%rbx`, `%rbp`, `%r12`, `%r13`, `%r14`, `%r15`.

## Main results

* `s2nMontsqrP384Seg01` … `s2nMontsqrP384Seg21`: the block in 21 segments, each a
  literal `List (JInstr 64)`. A segment is a paragraph of the source (a run of
  instructions with no blank or comment line between them); a paragraph of more than
  22 instructions is divided into near-equal parts at source lines, so no macro
  expansion is divided.
* `s2nMontsqrP384Block`: the block, the concatenation of the segments.
* `s2nMontsqrP384Block_length`: the block has 230 instructions.

Provenance class: `@imported`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontsqrP384

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 6 instructions from source lines 109–114. -/
def s2nMontsqrP384Seg01 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsi" 0,  -- l.109 `movq (%rsi), %rdx`
    .mulxMem "%r10" "%r9" (.reg "%rdx") "%rsi" 8,  -- l.110 `mulxq 8(%rsi), %r9, %r10`
    .mulxMem "%r12" "%r11" (.reg "%rdx") "%rsi" 24,  -- l.111 `mulxq 24(%rsi), %r11, %r12`
    .mulxMem "%r14" "%r13" (.reg "%rdx") "%rsi" 40,  -- l.112 `mulxq 40(%rsi), %r13, %r14`
    .loadMem "%rdx" "%rsi" 24,  -- l.113 `movq 24(%rsi), %rdx`
    .mulxMem "%rcx" "%r15" (.reg "%rdx") "%rsi" 32 ]  -- l.114 `mulxq 32(%rsi), %r15, %rcx`

/-- Segment 2 of the body: the 1 instruction from source line 118. -/
def s2nMontsqrP384Seg02 : List (JInstr 64) :=
  [ .xor_ "%rbp" (.reg "%rbp") ]  -- l.118 `xorl %ebp, %ebp`

/-- Segment 3 of the body: the 20 instructions from source lines 123–132. -/
def s2nMontsqrP384Seg03 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsi" 16,  -- l.123 `movq 16(%rsi), %rdx`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 0,  -- l.124 `mulxq (%rsi), %rax, %rbx`
    .adcx "%r10" (.reg "%rax"),  -- l.124 `adcxq %rax, %r10`
    .adox "%r11" (.reg "%rbx"),  -- l.124 `adoxq %rbx, %r11`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 8,  -- l.125 `mulxq 8(%rsi), %rax, %rbx`
    .adcx "%r11" (.reg "%rax"),  -- l.125 `adcxq %rax, %r11`
    .adox "%r12" (.reg "%rbx"),  -- l.125 `adoxq %rbx, %r12`
    .loadMem "%rdx" "%rsi" 8,  -- l.126 `movq 8(%rsi), %rdx`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 24,  -- l.127 `mulxq 24(%rsi), %rax, %rbx`
    .adcx "%r12" (.reg "%rax"),  -- l.127 `adcxq %rax, %r12`
    .adox "%r13" (.reg "%rbx"),  -- l.127 `adoxq %rbx, %r13`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 32,  -- l.128 `mulxq 32(%rsi), %rax, %rbx`
    .adcx "%r13" (.reg "%rax"),  -- l.128 `adcxq %rax, %r13`
    .adox "%r14" (.reg "%rbx"),  -- l.128 `adoxq %rbx, %r14`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 40,  -- l.129 `mulxq 40(%rsi), %rax, %rbx`
    .adcx "%r14" (.reg "%rax"),  -- l.129 `adcxq %rax, %r14`
    .adox "%r15" (.reg "%rbx"),  -- l.129 `adoxq %rbx, %r15`
    .adcx "%r15" (.reg "%rbp"),  -- l.130 `adcxq %rbp, %r15`
    .adox "%rcx" (.reg "%rbp"),  -- l.131 `adoxq %rbp, %rcx`
    .adc "%rcx" (.reg "%rbp") ]  -- l.132 `adcq %rbp, %rcx`

/-- Segment 4 of the body: the 1 instruction from source line 137. -/
def s2nMontsqrP384Seg04 : List (JInstr 64) :=
  [ .xor_ "%rbp" (.reg "%rbp") ]  -- l.137 `xorl %ebp, %ebp`

/-- Segment 5 of the body: the 14 instructions from source lines 144–151. -/
def s2nMontsqrP384Seg05 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsi" 32,  -- l.144 `movq 32(%rsi), %rdx`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 0,  -- l.145 `mulxq (%rsi), %rax, %rbx`
    .adcx "%r12" (.reg "%rax"),  -- l.145 `adcxq %rax, %r12`
    .adox "%r13" (.reg "%rbx"),  -- l.145 `adoxq %rbx, %r13`
    .loadMem "%rdx" "%rsi" 16,  -- l.146 `movq 16(%rsi), %rdx`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 24,  -- l.147 `mulxq 24(%rsi), %rax, %rbx`
    .adcx "%r13" (.reg "%rax"),  -- l.147 `adcxq %rax, %r13`
    .adox "%r14" (.reg "%rbx"),  -- l.147 `adoxq %rbx, %r14`
    .mulxMem "%rbx" "%rax" (.reg "%rdx") "%rsi" 32,  -- l.148 `mulxq 32(%rsi), %rax, %rbx`
    .adcx "%r14" (.reg "%rax"),  -- l.148 `adcxq %rax, %r14`
    .adox "%r15" (.reg "%rbx"),  -- l.148 `adoxq %rbx, %r15`
    .mulxMem "%rdx" "%rax" (.reg "%rdx") "%rsi" 40,  -- l.149 `mulxq 40(%rsi), %rax, %rdx`
    .adcx "%r15" (.reg "%rax"),  -- l.150 `adcxq %rax, %r15`
    .adox "%rcx" (.reg "%rdx") ]  -- l.151 `adoxq %rdx, %rcx`

/-- Segment 6 of the body: the 9 instructions from source lines 156–164. -/
def s2nMontsqrP384Seg06 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsi" 40,  -- l.156 `movq 40(%rsi), %rdx`
    .mulxMem "%rbp" "%rbx" (.reg "%rdx") "%rsi" 32,  -- l.157 `mulxq 32(%rsi), %rbx, %rbp`
    .mulxMem "%rdx" "%rax" (.reg "%rdx") "%rsi" 24,  -- l.158 `mulxq 24(%rsi), %rax, %rdx`
    .adcx "%rcx" (.reg "%rax"),  -- l.159 `adcxq %rax, %rcx`
    .adox "%rbx" (.reg "%rdx"),  -- l.160 `adoxq %rdx, %rbx`
    .mov "%rax" (.imm 0),  -- l.161 `movl $0, %eax`
    .adcx "%rbx" (.reg "%rax"),  -- l.162 `adcxq %rax, %rbx`
    .adox "%rbp" (.reg "%rax"),  -- l.163 `adoxq %rax, %rbp`
    .adc "%rbp" (.reg "%rax") ]  -- l.164 `adcq %rax, %rbp`

/-- Segment 7 of the body: the 1 instruction from source line 168. -/
def s2nMontsqrP384Seg07 : List (JInstr 64) :=
  [ .xor_ "%rax" (.reg "%rax") ]  -- l.168 `xorq %rax, %rax`

/-- Segment 8 of the body: the 18 instructions from source lines 175–192. -/
def s2nMontsqrP384Seg08 : List (JInstr 64) :=
  [ .loadMem "%rdx" "%rsi" 0,  -- l.175 `movq (%rsi), %rdx`
    .mulxMem "%rax" "%r8" (.reg "%rdx") "%rsi" 0,  -- l.176 `mulxq (%rsi), %r8, %rax`
    .adcx "%r9" (.reg "%r9"),  -- l.177 `adcxq %r9, %r9`
    .adox "%r9" (.reg "%rax"),  -- l.178 `adoxq %rax, %r9`
    .loadMem "%rdx" "%rsi" 8,  -- l.179 `movq 8(%rsi), %rdx`
    .mulx "%rdx" "%rax" (.reg "%rdx") (.reg "%rdx"),  -- l.180 `mulxq %rdx, %rax, %rdx`
    .adcx "%r10" (.reg "%r10"),  -- l.181 `adcxq %r10, %r10`
    .adox "%r10" (.reg "%rax"),  -- l.182 `adoxq %rax, %r10`
    .adcx "%r11" (.reg "%r11"),  -- l.183 `adcxq %r11, %r11`
    .adox "%r11" (.reg "%rdx"),  -- l.184 `adoxq %rdx, %r11`
    .loadMem "%rdx" "%rsi" 16,  -- l.185 `movq 16(%rsi), %rdx`
    .mulx "%rdx" "%rax" (.reg "%rdx") (.reg "%rdx"),  -- l.186 `mulxq %rdx, %rax, %rdx`
    .adcx "%r12" (.reg "%r12"),  -- l.187 `adcxq %r12, %r12`
    .adox "%r12" (.reg "%rax"),  -- l.188 `adoxq %rax, %r12`
    .adcx "%r13" (.reg "%r13"),  -- l.189 `adcxq %r13, %r13`
    .adox "%r13" (.reg "%rdx"),  -- l.190 `adoxq %rdx, %r13`
    .loadMem "%rdx" "%rsi" 24,  -- l.191 `movq 24(%rsi), %rdx`
    .mulx "%rdx" "%rax" (.reg "%rdx") (.reg "%rdx") ]  -- l.192 `mulxq %rdx, %rax, %rdx`

/-- Segment 9 of the body: the 17 instructions from source lines 193–209. -/
def s2nMontsqrP384Seg09 : List (JInstr 64) :=
  [ .adcx "%r14" (.reg "%r14"),  -- l.193 `adcxq %r14, %r14`
    .adox "%r14" (.reg "%rax"),  -- l.194 `adoxq %rax, %r14`
    .adcx "%r15" (.reg "%r15"),  -- l.195 `adcxq %r15, %r15`
    .adox "%r15" (.reg "%rdx"),  -- l.196 `adoxq %rdx, %r15`
    .loadMem "%rdx" "%rsi" 32,  -- l.197 `movq 32(%rsi), %rdx`
    .mulx "%rdx" "%rax" (.reg "%rdx") (.reg "%rdx"),  -- l.198 `mulxq %rdx, %rax, %rdx`
    .adcx "%rcx" (.reg "%rcx"),  -- l.199 `adcxq %rcx, %rcx`
    .adox "%rcx" (.reg "%rax"),  -- l.200 `adoxq %rax, %rcx`
    .adcx "%rbx" (.reg "%rbx"),  -- l.201 `adcxq %rbx, %rbx`
    .adox "%rbx" (.reg "%rdx"),  -- l.202 `adoxq %rdx, %rbx`
    .loadMem "%rdx" "%rsi" 40,  -- l.203 `movq 40(%rsi), %rdx`
    .mulx "%rsi" "%rax" (.reg "%rdx") (.reg "%rdx"),  -- l.204 `mulxq %rdx, %rax, %rsi`
    .adcx "%rbp" (.reg "%rbp"),  -- l.205 `adcxq %rbp, %rbp`
    .adox "%rbp" (.reg "%rax"),  -- l.206 `adoxq %rax, %rbp`
    .mov "%rax" (.imm 0),  -- l.207 `movl $0, %eax`
    .adcx "%rsi" (.reg "%rax"),  -- l.208 `adcxq %rax, %rsi`
    .adox "%rsi" (.reg "%rax") ]  -- l.209 `adoxq %rax, %rsi`

/-- Segment 10 of the body: the 1 instruction from source line 214. -/
def s2nMontsqrP384Seg10 : List (JInstr 64) :=
  [ .storeMem "%rdi" 0 (.reg "%rbx") ]  -- l.214 `movq %rbx, (%rdi)`

/-- Segment 11 of the body: the 18 instructions from source line 218. -/
def s2nMontsqrP384Seg11 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r8"),  -- l.218 `movq %r8, %rdx`
    .shl "%rdx" (.imm 32),  -- l.218 `shlq $32, %rdx`
    .add "%rdx" (.reg "%r8"),  -- l.218 `addq %r8, %rdx`
    .mov "%rax" (.imm 18446744069414584321),  -- l.218 `movq $0xffffffff00000001, %rax`
    .mulx "%rax" "%r8" (.reg "%rdx") (.reg "%rax"),  -- l.218 `mulxq %rax, %r8, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.218 `movl $0x00000000ffffffff, %ebx`
    .mulx "%r8" "%rbx" (.reg "%rdx") (.reg "%rbx"),  -- l.218 `mulxq %rbx, %rbx, %r8`
    .add "%rax" (.reg "%rbx"),  -- l.218 `addq %rbx, %rax`
    .adc "%r8" (.reg "%rdx"),  -- l.218 `adcq %rdx, %r8`
    .mov "%rbx" (.imm 0),  -- l.218 `movl $0, %ebx`
    .adc "%rbx" (.reg "%rbx"),  -- l.218 `adcq %rbx, %rbx`
    .sub "%r9" (.reg "%rax"),  -- l.218 `subq %rax, %r9`
    .sbb "%r10" (.reg "%r8"),  -- l.218 `sbbq %r8, %r10`
    .sbb "%r11" (.reg "%rbx"),  -- l.218 `sbbq %rbx, %r11`
    .sbb "%r12" (.imm 0),  -- l.218 `sbbq $0, %r12`
    .sbb "%r13" (.imm 0),  -- l.218 `sbbq $0, %r13`
    .mov "%r8" (.reg "%rdx"),  -- l.218 `movq %rdx, %r8`
    .sbb "%r8" (.imm 0) ]  -- l.218 `sbbq $0, %r8`

/-- Segment 12 of the body: the 18 instructions from source line 219. -/
def s2nMontsqrP384Seg12 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r9"),  -- l.219 `movq %r9, %rdx`
    .shl "%rdx" (.imm 32),  -- l.219 `shlq $32, %rdx`
    .add "%rdx" (.reg "%r9"),  -- l.219 `addq %r9, %rdx`
    .mov "%rax" (.imm 18446744069414584321),  -- l.219 `movq $0xffffffff00000001, %rax`
    .mulx "%rax" "%r9" (.reg "%rdx") (.reg "%rax"),  -- l.219 `mulxq %rax, %r9, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.219 `movl $0x00000000ffffffff, %ebx`
    .mulx "%r9" "%rbx" (.reg "%rdx") (.reg "%rbx"),  -- l.219 `mulxq %rbx, %rbx, %r9`
    .add "%rax" (.reg "%rbx"),  -- l.219 `addq %rbx, %rax`
    .adc "%r9" (.reg "%rdx"),  -- l.219 `adcq %rdx, %r9`
    .mov "%rbx" (.imm 0),  -- l.219 `movl $0, %ebx`
    .adc "%rbx" (.reg "%rbx"),  -- l.219 `adcq %rbx, %rbx`
    .sub "%r10" (.reg "%rax"),  -- l.219 `subq %rax, %r10`
    .sbb "%r11" (.reg "%r9"),  -- l.219 `sbbq %r9, %r11`
    .sbb "%r12" (.reg "%rbx"),  -- l.219 `sbbq %rbx, %r12`
    .sbb "%r13" (.imm 0),  -- l.219 `sbbq $0, %r13`
    .sbb "%r8" (.imm 0),  -- l.219 `sbbq $0, %r8`
    .mov "%r9" (.reg "%rdx"),  -- l.219 `movq %rdx, %r9`
    .sbb "%r9" (.imm 0) ]  -- l.219 `sbbq $0, %r9`

/-- Segment 13 of the body: the 18 instructions from source line 220. -/
def s2nMontsqrP384Seg13 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r10"),  -- l.220 `movq %r10, %rdx`
    .shl "%rdx" (.imm 32),  -- l.220 `shlq $32, %rdx`
    .add "%rdx" (.reg "%r10"),  -- l.220 `addq %r10, %rdx`
    .mov "%rax" (.imm 18446744069414584321),  -- l.220 `movq $0xffffffff00000001, %rax`
    .mulx "%rax" "%r10" (.reg "%rdx") (.reg "%rax"),  -- l.220 `mulxq %rax, %r10, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.220 `movl $0x00000000ffffffff, %ebx`
    .mulx "%r10" "%rbx" (.reg "%rdx") (.reg "%rbx"),  -- l.220 `mulxq %rbx, %rbx, %r10`
    .add "%rax" (.reg "%rbx"),  -- l.220 `addq %rbx, %rax`
    .adc "%r10" (.reg "%rdx"),  -- l.220 `adcq %rdx, %r10`
    .mov "%rbx" (.imm 0),  -- l.220 `movl $0, %ebx`
    .adc "%rbx" (.reg "%rbx"),  -- l.220 `adcq %rbx, %rbx`
    .sub "%r11" (.reg "%rax"),  -- l.220 `subq %rax, %r11`
    .sbb "%r12" (.reg "%r10"),  -- l.220 `sbbq %r10, %r12`
    .sbb "%r13" (.reg "%rbx"),  -- l.220 `sbbq %rbx, %r13`
    .sbb "%r8" (.imm 0),  -- l.220 `sbbq $0, %r8`
    .sbb "%r9" (.imm 0),  -- l.220 `sbbq $0, %r9`
    .mov "%r10" (.reg "%rdx"),  -- l.220 `movq %rdx, %r10`
    .sbb "%r10" (.imm 0) ]  -- l.220 `sbbq $0, %r10`

/-- Segment 14 of the body: the 18 instructions from source line 221. -/
def s2nMontsqrP384Seg14 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r11"),  -- l.221 `movq %r11, %rdx`
    .shl "%rdx" (.imm 32),  -- l.221 `shlq $32, %rdx`
    .add "%rdx" (.reg "%r11"),  -- l.221 `addq %r11, %rdx`
    .mov "%rax" (.imm 18446744069414584321),  -- l.221 `movq $0xffffffff00000001, %rax`
    .mulx "%rax" "%r11" (.reg "%rdx") (.reg "%rax"),  -- l.221 `mulxq %rax, %r11, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.221 `movl $0x00000000ffffffff, %ebx`
    .mulx "%r11" "%rbx" (.reg "%rdx") (.reg "%rbx"),  -- l.221 `mulxq %rbx, %rbx, %r11`
    .add "%rax" (.reg "%rbx"),  -- l.221 `addq %rbx, %rax`
    .adc "%r11" (.reg "%rdx"),  -- l.221 `adcq %rdx, %r11`
    .mov "%rbx" (.imm 0),  -- l.221 `movl $0, %ebx`
    .adc "%rbx" (.reg "%rbx"),  -- l.221 `adcq %rbx, %rbx`
    .sub "%r12" (.reg "%rax"),  -- l.221 `subq %rax, %r12`
    .sbb "%r13" (.reg "%r11"),  -- l.221 `sbbq %r11, %r13`
    .sbb "%r8" (.reg "%rbx"),  -- l.221 `sbbq %rbx, %r8`
    .sbb "%r9" (.imm 0),  -- l.221 `sbbq $0, %r9`
    .sbb "%r10" (.imm 0),  -- l.221 `sbbq $0, %r10`
    .mov "%r11" (.reg "%rdx"),  -- l.221 `movq %rdx, %r11`
    .sbb "%r11" (.imm 0) ]  -- l.221 `sbbq $0, %r11`

/-- Segment 15 of the body: the 18 instructions from source line 222. -/
def s2nMontsqrP384Seg15 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r12"),  -- l.222 `movq %r12, %rdx`
    .shl "%rdx" (.imm 32),  -- l.222 `shlq $32, %rdx`
    .add "%rdx" (.reg "%r12"),  -- l.222 `addq %r12, %rdx`
    .mov "%rax" (.imm 18446744069414584321),  -- l.222 `movq $0xffffffff00000001, %rax`
    .mulx "%rax" "%r12" (.reg "%rdx") (.reg "%rax"),  -- l.222 `mulxq %rax, %r12, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.222 `movl $0x00000000ffffffff, %ebx`
    .mulx "%r12" "%rbx" (.reg "%rdx") (.reg "%rbx"),  -- l.222 `mulxq %rbx, %rbx, %r12`
    .add "%rax" (.reg "%rbx"),  -- l.222 `addq %rbx, %rax`
    .adc "%r12" (.reg "%rdx"),  -- l.222 `adcq %rdx, %r12`
    .mov "%rbx" (.imm 0),  -- l.222 `movl $0, %ebx`
    .adc "%rbx" (.reg "%rbx"),  -- l.222 `adcq %rbx, %rbx`
    .sub "%r13" (.reg "%rax"),  -- l.222 `subq %rax, %r13`
    .sbb "%r8" (.reg "%r12"),  -- l.222 `sbbq %r12, %r8`
    .sbb "%r9" (.reg "%rbx"),  -- l.222 `sbbq %rbx, %r9`
    .sbb "%r10" (.imm 0),  -- l.222 `sbbq $0, %r10`
    .sbb "%r11" (.imm 0),  -- l.222 `sbbq $0, %r11`
    .mov "%r12" (.reg "%rdx"),  -- l.222 `movq %rdx, %r12`
    .sbb "%r12" (.imm 0) ]  -- l.222 `sbbq $0, %r12`

/-- Segment 16 of the body: the 18 instructions from source line 223. -/
def s2nMontsqrP384Seg16 : List (JInstr 64) :=
  [ .mov "%rdx" (.reg "%r13"),  -- l.223 `movq %r13, %rdx`
    .shl "%rdx" (.imm 32),  -- l.223 `shlq $32, %rdx`
    .add "%rdx" (.reg "%r13"),  -- l.223 `addq %r13, %rdx`
    .mov "%rax" (.imm 18446744069414584321),  -- l.223 `movq $0xffffffff00000001, %rax`
    .mulx "%rax" "%r13" (.reg "%rdx") (.reg "%rax"),  -- l.223 `mulxq %rax, %r13, %rax`
    .mov "%rbx" (.imm 4294967295),  -- l.223 `movl $0x00000000ffffffff, %ebx`
    .mulx "%r13" "%rbx" (.reg "%rdx") (.reg "%rbx"),  -- l.223 `mulxq %rbx, %rbx, %r13`
    .add "%rax" (.reg "%rbx"),  -- l.223 `addq %rbx, %rax`
    .adc "%r13" (.reg "%rdx"),  -- l.223 `adcq %rdx, %r13`
    .mov "%rbx" (.imm 0),  -- l.223 `movl $0, %ebx`
    .adc "%rbx" (.reg "%rbx"),  -- l.223 `adcq %rbx, %rbx`
    .sub "%r8" (.reg "%rax"),  -- l.223 `subq %rax, %r8`
    .sbb "%r9" (.reg "%r13"),  -- l.223 `sbbq %r13, %r9`
    .sbb "%r10" (.reg "%rbx"),  -- l.223 `sbbq %rbx, %r10`
    .sbb "%r11" (.imm 0),  -- l.223 `sbbq $0, %r11`
    .sbb "%r12" (.imm 0),  -- l.223 `sbbq $0, %r12`
    .mov "%r13" (.reg "%rdx"),  -- l.223 `movq %rdx, %r13`
    .sbb "%r13" (.imm 0) ]  -- l.223 `sbbq $0, %r13`

/-- Segment 17 of the body: the 1 instruction from source line 227. -/
def s2nMontsqrP384Seg17 : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rdi" 0 ]  -- l.227 `movq (%rdi), %rbx`

/-- Segment 18 of the body: the 8 instructions from source lines 229–236. -/
def s2nMontsqrP384Seg18 : List (JInstr 64) :=
  [ .add "%r14" (.reg "%r8"),  -- l.229 `addq %r8, %r14`
    .adc "%r15" (.reg "%r9"),  -- l.230 `adcq %r9, %r15`
    .adc "%rcx" (.reg "%r10"),  -- l.231 `adcq %r10, %rcx`
    .adc "%rbx" (.reg "%r11"),  -- l.232 `adcq %r11, %rbx`
    .adc "%rbp" (.reg "%r12"),  -- l.233 `adcq %r12, %rbp`
    .adc "%rsi" (.reg "%r13"),  -- l.234 `adcq %r13, %rsi`
    .mov "%r8" (.imm 0),  -- l.235 `movl $0, %r8d`
    .adc "%r8" (.reg "%r8") ]  -- l.236 `adcq %r8, %r8`

/-- Segment 19 of the body: the 13 instructions from source lines 243–255. -/
def s2nMontsqrP384Seg19 : List (JInstr 64) :=
  [ .xor_ "%r11" (.reg "%r11"),  -- l.243 `xorq %r11, %r11`
    .xor_ "%r12" (.reg "%r12"),  -- l.244 `xorq %r12, %r12`
    .xor_ "%r13" (.reg "%r13"),  -- l.245 `xorq %r13, %r13`
    .mov "%rax" (.imm 18446744069414584321),  -- l.246 `movq $0xffffffff00000001, %rax`
    .add "%rax" (.reg "%r14"),  -- l.247 `addq %r14, %rax`
    .mov "%r9" (.imm 4294967295),  -- l.248 `movl $0x00000000ffffffff, %r9d`
    .adc "%r9" (.reg "%r15"),  -- l.249 `adcq %r15, %r9`
    .mov "%r10" (.imm 1),  -- l.250 `movl $0x0000000000000001, %r10d`
    .adc "%r10" (.reg "%rcx"),  -- l.251 `adcq %rcx, %r10`
    .adc "%r11" (.reg "%rbx"),  -- l.252 `adcq %rbx, %r11`
    .adc "%r12" (.reg "%rbp"),  -- l.253 `adcq %rbp, %r12`
    .adc "%r13" (.reg "%rsi"),  -- l.254 `adcq %rsi, %r13`
    .adc "%r8" (.imm 0) ]  -- l.255 `adcq $0, %r8`

/-- Segment 20 of the body: the 6 instructions from source lines 260–265. -/
def s2nMontsqrP384Seg20 : List (JInstr 64) :=
  [ .cmovne "%r14" (.reg "%rax"),  -- l.260 `cmovnzq %rax, %r14`
    .cmovne "%r15" (.reg "%r9"),  -- l.261 `cmovnzq %r9, %r15`
    .cmovne "%rcx" (.reg "%r10"),  -- l.262 `cmovnzq %r10, %rcx`
    .cmovne "%rbx" (.reg "%r11"),  -- l.263 `cmovnzq %r11, %rbx`
    .cmovne "%rbp" (.reg "%r12"),  -- l.264 `cmovnzq %r12, %rbp`
    .cmovne "%rsi" (.reg "%r13") ]  -- l.265 `cmovnzq %r13, %rsi`

/-- Segment 21 of the body: the 6 instructions from source lines 269–274. -/
def s2nMontsqrP384Seg21 : List (JInstr 64) :=
  [ .storeMem "%rdi" 0 (.reg "%r14"),  -- l.269 `movq %r14, (%rdi)`
    .storeMem "%rdi" 8 (.reg "%r15"),  -- l.270 `movq %r15, 8(%rdi)`
    .storeMem "%rdi" 16 (.reg "%rcx"),  -- l.271 `movq %rcx, 16(%rdi)`
    .storeMem "%rdi" 24 (.reg "%rbx"),  -- l.272 `movq %rbx, 24(%rdi)`
    .storeMem "%rdi" 32 (.reg "%rbp"),  -- l.273 `movq %rbp, 32(%rdi)`
    .storeMem "%rdi" 40 (.reg "%rsi") ]  -- l.274 `movq %rsi, 40(%rdi)`

/-- The body of s2n-bignum's `bignum_montsqr_p384`, translated instruction by instruction
    by `bench/s2n_import/import_s2n.sh`: the concatenation of its 21 segments. -/
def s2nMontsqrP384Block : List (JInstr 64) :=
  s2nMontsqrP384Seg01 ++ s2nMontsqrP384Seg02 ++ s2nMontsqrP384Seg03 ++
  s2nMontsqrP384Seg04 ++ s2nMontsqrP384Seg05 ++ s2nMontsqrP384Seg06 ++
  s2nMontsqrP384Seg07 ++ s2nMontsqrP384Seg08 ++ s2nMontsqrP384Seg09 ++
  s2nMontsqrP384Seg10 ++ s2nMontsqrP384Seg11 ++ s2nMontsqrP384Seg12 ++
  s2nMontsqrP384Seg13 ++ s2nMontsqrP384Seg14 ++ s2nMontsqrP384Seg15 ++
  s2nMontsqrP384Seg16 ++ s2nMontsqrP384Seg17 ++ s2nMontsqrP384Seg18 ++
  s2nMontsqrP384Seg19 ++ s2nMontsqrP384Seg20 ++ s2nMontsqrP384Seg21

/-- The block has 230 instructions. The length of each segment is computed by `rfl`;
    the whole list at once exceeds the default recursion depth. -/
theorem s2nMontsqrP384Block_length : s2nMontsqrP384Block.length = 230 := by
  unfold s2nMontsqrP384Block; simp only [List.length_append]; rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontsqrP384
