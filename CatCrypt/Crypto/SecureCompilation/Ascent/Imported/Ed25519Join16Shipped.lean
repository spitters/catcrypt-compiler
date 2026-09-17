/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# `ed25519_join16_x86_from_lean` from the owned backend's output as a `JInstr 64` block

`ed25519Join16ShippedBlock` is the body of the function
`ed25519_join16_x86_from_lean` in an x86-64 AT&T file printed by CatCrypt's owned
backend, translated instruction by instruction. The file's producer is recorded in
`PROVENANCE.md` next to it, where one exists.

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
  each checked by the importer: the stack allocation `leaq -112(%rsp), %rsp` and
  its release `leaq 112(%rsp), %rsp`; `ret`.
* Every other instruction is kept, `%rsp`-relative moves included, as `storeMem
  "%rsp" off` and `loadMem r "%rsp" off`. Their offsets are relative to `%rsp`
  after the omitted allocation, and `%rsp` is constant in the body.
* The first 11 instructions store registers into `%rsp` slots and form segment 1.
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

The block has 102 instructions. Source instructions by mnemonic: `movq` 102.

## Main definitions

* `ed25519Join16ShippedSeg01` … `ed25519Join16ShippedSeg05`: the block in 5
  segments, each a literal `List (JInstr 64)`. A segment ends after a call, after
  the entry run of `%rsp` stores, before the exit run of `%rsp` loads, and after 32
  instructions.
* `ed25519Join16ShippedBlock`: the block, the concatenation of the segments.

## Main results

* `ed25519Join16ShippedBlock_length`: the block has 102 instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519Join16Shipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 11 instructions from source lines 128–138. -/
def ed25519Join16ShippedSeg01 : List (JInstr 64) :=
  [ .storeMem "%rsp" 104 (.reg "%rdi"),  -- l.128 `movq %rdi, 104(%rsp)`
    .storeMem "%rsp" 96 (.reg "%rsi"),  -- l.129 `movq %rsi, 96(%rsp)`
    .storeMem "%rsp" 88 (.reg "%rbx"),  -- l.130 `movq %rbx, 88(%rsp)`
    .storeMem "%rsp" 80 (.reg "%rbp"),  -- l.131 `movq %rbp, 80(%rsp)`
    .storeMem "%rsp" 72 (.reg "%r12"),  -- l.132 `movq %r12, 72(%rsp)`
    .storeMem "%rsp" 64 (.reg "%r13"),  -- l.133 `movq %r13, 64(%rsp)`
    .storeMem "%rsp" 56 (.reg "%r14"),  -- l.134 `movq %r14, 56(%rsp)`
    .storeMem "%rsp" 48 (.reg "%r15"),  -- l.135 `movq %r15, 48(%rsp)`
    .storeMem "%rsp" (-8) (.reg "%rdx"),  -- l.136 `movq %rdx, -8(%rsp)`
    .storeMem "%rsp" (-16) (.reg "%rcx"),  -- l.137 `movq %rcx, -16(%rsp)`
    .storeMem "%rsp" (-24) (.reg "%r8") ]  -- l.138 `movq %r8, -24(%rsp)`

/-- Segment 2 of the body: the 32 instructions from source lines 139–170. -/
def ed25519Join16ShippedSeg02 : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 104,  -- l.139 `movq 104(%rsp), %rbx`
    .loadMem "%rcx" "%rsp" 96,  -- l.140 `movq 96(%rsp), %rcx`
    .loadMem "%rsi" "%rsp" (-16),  -- l.141 `movq -16(%rsp), %rsi`
    .loadMem "%rdi" "%rsp" (-24),  -- l.142 `movq -24(%rsp), %rdi`
    .mov "%rax" (.imm 0),  -- l.143 `movq $0, %rax`
    .mov "%r14" (.reg "%rcx"),  -- l.144 `movq %rcx, %r14`
    .loadMemIdx "%rbp" "%r14" "%rax" 8,  -- l.145 `movq (%r14, %rax, 8), %rbp`
    .mov "%rax" (.imm 1),  -- l.146 `movq $1, %rax`
    .loadMemIdx "%r8" "%r14" "%rax" 8,  -- l.147 `movq (%r14, %rax, 8), %r8`
    .mov "%rax" (.imm 2),  -- l.148 `movq $2, %rax`
    .loadMemIdx "%r9" "%r14" "%rax" 8,  -- l.149 `movq (%r14, %rax, 8), %r9`
    .mov "%rax" (.imm 3),  -- l.150 `movq $3, %rax`
    .loadMemIdx "%r10" "%r14" "%rax" 8,  -- l.151 `movq (%r14, %rax, 8), %r10`
    .mov "%rax" (.imm 0),  -- l.152 `movq $0, %rax`
    .loadMem "%r14" "%rsp" (-8),  -- l.153 `movq -8(%rsp), %r14`
    .loadMemIdx "%rcx" "%r14" "%rax" 8,  -- l.154 `movq (%r14, %rax, 8), %rcx`
    .mov "%rax" (.imm 1),  -- l.155 `movq $1, %rax`
    .loadMemIdx "%r11" "%r14" "%rax" 8,  -- l.156 `movq (%r14, %rax, 8), %r11`
    .mov "%rax" (.imm 2),  -- l.157 `movq $2, %rax`
    .loadMemIdx "%r12" "%r14" "%rax" 8,  -- l.158 `movq (%r14, %rax, 8), %r12`
    .mov "%rax" (.imm 3),  -- l.159 `movq $3, %rax`
    .loadMemIdx "%r13" "%r14" "%rax" 8,  -- l.160 `movq (%r14, %rax, 8), %r13`
    .mov "%rax" (.imm 0),  -- l.161 `movq $0, %rax`
    .mov "%r14" (.reg "%rsi"),  -- l.162 `movq %rsi, %r14`
    .loadMemIdx "%rdx" "%r14" "%rax" 8,  -- l.163 `movq (%r14, %rax, 8), %rdx`
    .mov "%rax" (.imm 1),  -- l.164 `movq $1, %rax`
    .loadMemIdx "%r15" "%r14" "%rax" 8,  -- l.165 `movq (%r14, %rax, 8), %r15`
    .storeMem "%rsp" 40 (.reg "%r15"),  -- l.166 `movq %r15, 40(%rsp)`
    .mov "%rax" (.imm 2),  -- l.167 `movq $2, %rax`
    .loadMemIdx "%r15" "%r14" "%rax" 8,  -- l.168 `movq (%r14, %rax, 8), %r15`
    .storeMem "%rsp" 32 (.reg "%r15"),  -- l.169 `movq %r15, 32(%rsp)`
    .mov "%rax" (.imm 3) ]  -- l.170 `movq $3, %rax`

/-- Segment 3 of the body: the 32 instructions from source lines 171–202. -/
def ed25519Join16ShippedSeg03 : List (JInstr 64) :=
  [ .loadMemIdx "%r15" "%r14" "%rax" 8,  -- l.171 `movq (%r14, %rax, 8), %r15`
    .storeMem "%rsp" 24 (.reg "%r15"),  -- l.172 `movq %r15, 24(%rsp)`
    .mov "%rax" (.imm 0),  -- l.173 `movq $0, %rax`
    .mov "%r14" (.reg "%rdi"),  -- l.174 `movq %rdi, %r14`
    .loadMemIdx "%rsi" "%r14" "%rax" 8,  -- l.175 `movq (%r14, %rax, 8), %rsi`
    .mov "%rax" (.imm 1),  -- l.176 `movq $1, %rax`
    .loadMemIdx "%r15" "%r14" "%rax" 8,  -- l.177 `movq (%r14, %rax, 8), %r15`
    .storeMem "%rsp" 16 (.reg "%r15"),  -- l.178 `movq %r15, 16(%rsp)`
    .mov "%rax" (.imm 2),  -- l.179 `movq $2, %rax`
    .loadMemIdx "%r15" "%r14" "%rax" 8,  -- l.180 `movq (%r14, %rax, 8), %r15`
    .storeMem "%rsp" 8 (.reg "%r15"),  -- l.181 `movq %r15, 8(%rsp)`
    .mov "%rax" (.imm 3),  -- l.182 `movq $3, %rax`
    .loadMemIdx "%r15" "%r14" "%rax" 8,  -- l.183 `movq (%r14, %rax, 8), %r15`
    .storeMem "%rsp" 0 (.reg "%r15"),  -- l.184 `movq %r15, 0(%rsp)`
    .mov "%rax" (.imm 0),  -- l.185 `movq $0, %rax`
    .mov "%r14" (.reg "%rbx"),  -- l.186 `movq %rbx, %r14`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%rbp"),  -- l.187 `movq %rbp, (%r14, %rax, 8)`
    .mov "%rax" (.imm 1),  -- l.188 `movq $1, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r8"),  -- l.189 `movq %r8, (%r14, %rax, 8)`
    .mov "%rax" (.imm 2),  -- l.190 `movq $2, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r9"),  -- l.191 `movq %r9, (%r14, %rax, 8)`
    .mov "%rax" (.imm 3),  -- l.192 `movq $3, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r10"),  -- l.193 `movq %r10, (%r14, %rax, 8)`
    .mov "%rax" (.imm 4),  -- l.194 `movq $4, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%rcx"),  -- l.195 `movq %rcx, (%r14, %rax, 8)`
    .mov "%rax" (.imm 5),  -- l.196 `movq $5, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r11"),  -- l.197 `movq %r11, (%r14, %rax, 8)`
    .mov "%rax" (.imm 6),  -- l.198 `movq $6, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r12"),  -- l.199 `movq %r12, (%r14, %rax, 8)`
    .mov "%rax" (.imm 7),  -- l.200 `movq $7, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r13"),  -- l.201 `movq %r13, (%r14, %rax, 8)`
    .mov "%rax" (.imm 8) ]  -- l.202 `movq $8, %rax`

/-- Segment 4 of the body: the 21 instructions from source lines 203–223. -/
def ed25519Join16ShippedSeg04 : List (JInstr 64) :=
  [ .storeMemIdx "%r14" "%rax" 8 (.reg "%rdx"),  -- l.203 `movq %rdx, (%r14, %rax, 8)`
    .mov "%rax" (.imm 9),  -- l.204 `movq $9, %rax`
    .loadMem "%r15" "%rsp" 40,  -- l.205 `movq 40(%rsp), %r15`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r15"),  -- l.206 `movq %r15, (%r14, %rax, 8)`
    .mov "%rax" (.imm 10),  -- l.207 `movq $10, %rax`
    .loadMem "%r15" "%rsp" 32,  -- l.208 `movq 32(%rsp), %r15`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r15"),  -- l.209 `movq %r15, (%r14, %rax, 8)`
    .mov "%rax" (.imm 11),  -- l.210 `movq $11, %rax`
    .loadMem "%r15" "%rsp" 24,  -- l.211 `movq 24(%rsp), %r15`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r15"),  -- l.212 `movq %r15, (%r14, %rax, 8)`
    .mov "%rax" (.imm 12),  -- l.213 `movq $12, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%rsi"),  -- l.214 `movq %rsi, (%r14, %rax, 8)`
    .mov "%rax" (.imm 13),  -- l.215 `movq $13, %rax`
    .loadMem "%r15" "%rsp" 16,  -- l.216 `movq 16(%rsp), %r15`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r15"),  -- l.217 `movq %r15, (%r14, %rax, 8)`
    .mov "%rax" (.imm 14),  -- l.218 `movq $14, %rax`
    .loadMem "%r15" "%rsp" 8,  -- l.219 `movq 8(%rsp), %r15`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r15"),  -- l.220 `movq %r15, (%r14, %rax, 8)`
    .mov "%rax" (.imm 15),  -- l.221 `movq $15, %rax`
    .loadMem "%r15" "%rsp" 0,  -- l.222 `movq 0(%rsp), %r15`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r15") ]  -- l.223 `movq %r15, (%r14, %rax, 8)`

/-- Segment 5 of the body: the 6 instructions from source lines 224–229. -/
def ed25519Join16ShippedSeg05 : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 88,  -- l.224 `movq 88(%rsp), %rbx`
    .loadMem "%rbp" "%rsp" 80,  -- l.225 `movq 80(%rsp), %rbp`
    .loadMem "%r12" "%rsp" 72,  -- l.226 `movq 72(%rsp), %r12`
    .loadMem "%r13" "%rsp" 64,  -- l.227 `movq 64(%rsp), %r13`
    .loadMem "%r14" "%rsp" 56,  -- l.228 `movq 56(%rsp), %r14`
    .loadMem "%r15" "%rsp" 48 ]  -- l.229 `movq 48(%rsp), %r15`

/-- The body of `ed25519_join16_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 5 segments. -/
def ed25519Join16ShippedBlock : List (JInstr 64) :=
  ed25519Join16ShippedSeg01 ++ ed25519Join16ShippedSeg02 ++ ed25519Join16ShippedSeg03 ++
  ed25519Join16ShippedSeg04 ++ ed25519Join16ShippedSeg05

/-- The block has 102 instructions; the count of each segment is computed by `rfl`. -/
theorem ed25519Join16ShippedBlock_length :
    ed25519Join16ShippedBlock.length = 102 := by
  unfold ed25519Join16ShippedBlock
  simp only [List.length_append]
  rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519Join16Shipped
