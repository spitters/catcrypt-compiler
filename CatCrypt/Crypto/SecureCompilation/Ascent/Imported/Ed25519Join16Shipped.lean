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
  `SSProve-lean` repository at commit `b294647590404f72dd82b5404e326511f3c055eb`
  (tracked and unchanged at that commit), file SHA-256
  `b16afc9f5f03c810d65863a4f4ae7028861acf8054a07cb3311b83b829d866fd`.
* Produced by `bench/s2n_import/import_owned.sh`, which translates each instruction
  to one `JInstr 64` constructor. The comment after each element gives the source
  line and text. The importer is not trusted: a correctness proof is stated over
  this list, and `bench/s2n_import/compare_owned.sh` checks that the list, printed
  back by `AsmPrinter.renderBlockBody`, is the source's instruction sequence.
* Omitted from the list: the assembler directives and the 3 frame instructions,
  each checked by the importer: the stack allocation `leaq -112(%rsp), %rsp` and
  its release `leaq 112(%rsp), %rsp`; `ret`.
* `ed25519Join16ShippedPrologue` and `ed25519Join16ShippedEpilogue` are the frame
  instructions before and after the block, `ret` excluded: each `pushq r` as `lea
  "%rsp" "%rsp" "%rsp" 0 (-8)` followed by `storeMem "%rsp" 0 (.reg r)`, each `popq
  r` as `loadMem r "%rsp" 0` followed by `lea "%rsp" "%rsp" "%rsp" 0 8`, and the
  stack allocation and its release as the instruction the text contains. `lea`
  writes no flag, as `pushq` and `popq` write none.
* Every other instruction is kept, `%rsp`-relative moves included, as `storeMem
  "%rsp" off` and `loadMem r "%rsp" off`. Their offsets are relative to `%rsp`
  after the omitted allocation, and `%rsp` is constant in the body.
* The first 11 instructions store registers into `%rsp` slots and form segment 1.
* Registers keep their physical names (`"%rax"`, …, `"%r15"`, `"%rsp"`); no
  register allocation is involved.
* `JasminModel` keys memory by the name of the base register and a byte offset, at
  word granularity. A proof over this block is a statement about that model; it
  agrees with the processor where each base register holds one address throughout
  the block and distinct names address disjoint words.
* The block writes `%r14` between memory accesses through it, so the accesses
  through that register before and after the write share one memory bank in the
  model.

The block has 119 instructions. Source instructions by mnemonic: `movq` 119.

## Main definitions

* `ed25519Join16ShippedSeg01` … `ed25519Join16ShippedSeg05`: the block in 5
  segments, each a literal `List (JInstr 64)`. A segment ends after a call, after
  the entry run of `%rsp` stores, before the exit run of `%rsp` loads, and after 32
  instructions.
* `ed25519Join16ShippedBlock`: the block, the concatenation of the segments.
* `ed25519Join16ShippedPrologue`, `ed25519Join16ShippedEpilogue`: the frame
  instructions before and after the block.

## Main results

* `ed25519Join16ShippedBlock_length`: the block has 119 instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519Join16Shipped

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- Segment 1 of the body: the 11 instructions from source lines 130–140. -/
def ed25519Join16ShippedSeg01 : List (JInstr 64) :=
  [ .storeMem "%rsp" 104 (.reg "%rdi"),  -- l.130 `movq %rdi, 104(%rsp)`
    .storeMem "%rsp" 96 (.reg "%rsi"),  -- l.131 `movq %rsi, 96(%rsp)`
    .storeMem "%rsp" 88 (.reg "%rbx"),  -- l.132 `movq %rbx, 88(%rsp)`
    .storeMem "%rsp" 80 (.reg "%rbp"),  -- l.133 `movq %rbp, 80(%rsp)`
    .storeMem "%rsp" 72 (.reg "%r12"),  -- l.134 `movq %r12, 72(%rsp)`
    .storeMem "%rsp" 64 (.reg "%r13"),  -- l.135 `movq %r13, 64(%rsp)`
    .storeMem "%rsp" 56 (.reg "%r14"),  -- l.136 `movq %r14, 56(%rsp)`
    .storeMem "%rsp" 48 (.reg "%r15"),  -- l.137 `movq %r15, 48(%rsp)`
    .storeMem "%rsp" (-8) (.reg "%rdx"),  -- l.138 `movq %rdx, -8(%rsp)`
    .storeMem "%rsp" (-16) (.reg "%rcx"),  -- l.139 `movq %rcx, -16(%rsp)`
    .storeMem "%rsp" (-24) (.reg "%r8") ]  -- l.140 `movq %r8, -24(%rsp)`

/-- Segment 2 of the body: the 32 instructions from source lines 141–172. -/
def ed25519Join16ShippedSeg02 : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 104,  -- l.141 `movq 104(%rsp), %rbx`
    .loadMem "%rcx" "%rsp" 96,  -- l.142 `movq 96(%rsp), %rcx`
    .loadMem "%rsi" "%rsp" (-16),  -- l.143 `movq -16(%rsp), %rsi`
    .loadMem "%rdi" "%rsp" (-24),  -- l.144 `movq -24(%rsp), %rdi`
    .mov "%rax" (.imm 0),  -- l.145 `movq $0, %rax`
    .mov "%r14" (.reg "%rcx"),  -- l.146 `movq %rcx, %r14`
    .loadMemIdx "%rbp" "%r14" "%rax" 8,  -- l.147 `movq (%r14, %rax, 8), %rbp`
    .mov "%rax" (.imm 1),  -- l.148 `movq $1, %rax`
    .loadMemIdx "%r8" "%r14" "%rax" 8,  -- l.149 `movq (%r14, %rax, 8), %r8`
    .mov "%rax" (.imm 2),  -- l.150 `movq $2, %rax`
    .loadMemIdx "%r9" "%r14" "%rax" 8,  -- l.151 `movq (%r14, %rax, 8), %r9`
    .mov "%rax" (.imm 3),  -- l.152 `movq $3, %rax`
    .loadMemIdx "%r10" "%r14" "%rax" 8,  -- l.153 `movq (%r14, %rax, 8), %r10`
    .mov "%rax" (.imm 0),  -- l.154 `movq $0, %rax`
    .loadMem "%r14" "%rsp" (-8),  -- l.155 `movq -8(%rsp), %r14`
    .loadMemIdx "%rcx" "%r14" "%rax" 8,  -- l.156 `movq (%r14, %rax, 8), %rcx`
    .mov "%rax" (.imm 1),  -- l.157 `movq $1, %rax`
    .loadMemIdx "%r11" "%r14" "%rax" 8,  -- l.158 `movq (%r14, %rax, 8), %r11`
    .mov "%rax" (.imm 2),  -- l.159 `movq $2, %rax`
    .loadMemIdx "%r12" "%r14" "%rax" 8,  -- l.160 `movq (%r14, %rax, 8), %r12`
    .mov "%rax" (.imm 3),  -- l.161 `movq $3, %rax`
    .loadMemIdx "%r13" "%r14" "%rax" 8,  -- l.162 `movq (%r14, %rax, 8), %r13`
    .mov "%rax" (.imm 0),  -- l.163 `movq $0, %rax`
    .mov "%r14" (.reg "%rsi"),  -- l.164 `movq %rsi, %r14`
    .loadMemIdx "%rdx" "%r14" "%rax" 8,  -- l.165 `movq (%r14, %rax, 8), %rdx`
    .mov "%rax" (.imm 1),  -- l.166 `movq $1, %rax`
    .loadMemIdx "%r15" "%r14" "%rax" 8,  -- l.167 `movq (%r14, %rax, 8), %r15`
    .storeMem "%rsp" 40 (.reg "%r15"),  -- l.168 `movq %r15, 40(%rsp)`
    .mov "%rax" (.imm 2),  -- l.169 `movq $2, %rax`
    .loadMemIdx "%r15" "%r14" "%rax" 8,  -- l.170 `movq (%r14, %rax, 8), %r15`
    .storeMem "%rsp" 32 (.reg "%r15"),  -- l.171 `movq %r15, 32(%rsp)`
    .mov "%rax" (.imm 3) ]  -- l.172 `movq $3, %rax`

/-- Segment 3 of the body: the 32 instructions from source lines 173–204. -/
def ed25519Join16ShippedSeg03 : List (JInstr 64) :=
  [ .loadMemIdx "%r15" "%r14" "%rax" 8,  -- l.173 `movq (%r14, %rax, 8), %r15`
    .storeMem "%rsp" 24 (.reg "%r15"),  -- l.174 `movq %r15, 24(%rsp)`
    .mov "%rax" (.imm 0),  -- l.175 `movq $0, %rax`
    .mov "%r14" (.reg "%rdi"),  -- l.176 `movq %rdi, %r14`
    .loadMemIdx "%rsi" "%r14" "%rax" 8,  -- l.177 `movq (%r14, %rax, 8), %rsi`
    .mov "%rax" (.imm 1),  -- l.178 `movq $1, %rax`
    .loadMemIdx "%r15" "%r14" "%rax" 8,  -- l.179 `movq (%r14, %rax, 8), %r15`
    .storeMem "%rsp" 16 (.reg "%r15"),  -- l.180 `movq %r15, 16(%rsp)`
    .mov "%rax" (.imm 2),  -- l.181 `movq $2, %rax`
    .loadMemIdx "%r15" "%r14" "%rax" 8,  -- l.182 `movq (%r14, %rax, 8), %r15`
    .storeMem "%rsp" 8 (.reg "%r15"),  -- l.183 `movq %r15, 8(%rsp)`
    .mov "%rax" (.imm 3),  -- l.184 `movq $3, %rax`
    .loadMemIdx "%r15" "%r14" "%rax" 8,  -- l.185 `movq (%r14, %rax, 8), %r15`
    .storeMem "%rsp" 0 (.reg "%r15"),  -- l.186 `movq %r15, 0(%rsp)`
    .mov "%rax" (.imm 0),  -- l.187 `movq $0, %rax`
    .mov "%r14" (.reg "%rbx"),  -- l.188 `movq %rbx, %r14`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%rbp"),  -- l.189 `movq %rbp, (%r14, %rax, 8)`
    .mov "%rax" (.imm 1),  -- l.190 `movq $1, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r8"),  -- l.191 `movq %r8, (%r14, %rax, 8)`
    .mov "%rax" (.imm 2),  -- l.192 `movq $2, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r9"),  -- l.193 `movq %r9, (%r14, %rax, 8)`
    .mov "%rax" (.imm 3),  -- l.194 `movq $3, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r10"),  -- l.195 `movq %r10, (%r14, %rax, 8)`
    .mov "%rax" (.imm 4),  -- l.196 `movq $4, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%rcx"),  -- l.197 `movq %rcx, (%r14, %rax, 8)`
    .mov "%rax" (.imm 5),  -- l.198 `movq $5, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r11"),  -- l.199 `movq %r11, (%r14, %rax, 8)`
    .mov "%rax" (.imm 6),  -- l.200 `movq $6, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r12"),  -- l.201 `movq %r12, (%r14, %rax, 8)`
    .mov "%rax" (.imm 7),  -- l.202 `movq $7, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r13"),  -- l.203 `movq %r13, (%r14, %rax, 8)`
    .mov "%rax" (.imm 8) ]  -- l.204 `movq $8, %rax`

/-- Segment 4 of the body: the 32 instructions from source lines 205–236. -/
def ed25519Join16ShippedSeg04 : List (JInstr 64) :=
  [ .storeMemIdx "%r14" "%rax" 8 (.reg "%rdx"),  -- l.205 `movq %rdx, (%r14, %rax, 8)`
    .mov "%rax" (.imm 9),  -- l.206 `movq $9, %rax`
    .loadMem "%r15" "%rsp" 40,  -- l.207 `movq 40(%rsp), %r15`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r15"),  -- l.208 `movq %r15, (%r14, %rax, 8)`
    .mov "%rax" (.imm 10),  -- l.209 `movq $10, %rax`
    .loadMem "%r15" "%rsp" 32,  -- l.210 `movq 32(%rsp), %r15`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r15"),  -- l.211 `movq %r15, (%r14, %rax, 8)`
    .mov "%rax" (.imm 11),  -- l.212 `movq $11, %rax`
    .loadMem "%r15" "%rsp" 24,  -- l.213 `movq 24(%rsp), %r15`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r15"),  -- l.214 `movq %r15, (%r14, %rax, 8)`
    .mov "%rax" (.imm 12),  -- l.215 `movq $12, %rax`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%rsi"),  -- l.216 `movq %rsi, (%r14, %rax, 8)`
    .mov "%rax" (.imm 13),  -- l.217 `movq $13, %rax`
    .loadMem "%r15" "%rsp" 16,  -- l.218 `movq 16(%rsp), %r15`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r15"),  -- l.219 `movq %r15, (%r14, %rax, 8)`
    .mov "%rax" (.imm 14),  -- l.220 `movq $14, %rax`
    .loadMem "%r15" "%rsp" 8,  -- l.221 `movq 8(%rsp), %r15`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r15"),  -- l.222 `movq %r15, (%r14, %rax, 8)`
    .mov "%rax" (.imm 15),  -- l.223 `movq $15, %rax`
    .loadMem "%r15" "%rsp" 0,  -- l.224 `movq 0(%rsp), %r15`
    .storeMemIdx "%r14" "%rax" 8 (.reg "%r15"),  -- l.225 `movq %r15, (%r14, %rax, 8)`
    .loadMem "%rbx" "%rsp" 88,  -- l.226 `movq 88(%rsp), %rbx`
    .loadMem "%rbp" "%rsp" 80,  -- l.227 `movq 80(%rsp), %rbp`
    .loadMem "%r12" "%rsp" 72,  -- l.228 `movq 72(%rsp), %r12`
    .loadMem "%r13" "%rsp" 64,  -- l.229 `movq 64(%rsp), %r13`
    .loadMem "%r14" "%rsp" 56,  -- l.230 `movq 56(%rsp), %r14`
    .loadMem "%r15" "%rsp" 48,  -- l.231 `movq 48(%rsp), %r15`
    .storeMem "%rsp" 104 (.imm 0),  -- l.232 `movq $0, 104(%rsp)`
    .storeMem "%rsp" 96 (.imm 0),  -- l.233 `movq $0, 96(%rsp)`
    .storeMem "%rsp" 88 (.imm 0),  -- l.234 `movq $0, 88(%rsp)`
    .storeMem "%rsp" 80 (.imm 0),  -- l.235 `movq $0, 80(%rsp)`
    .storeMem "%rsp" 72 (.imm 0) ]  -- l.236 `movq $0, 72(%rsp)`

/-- Segment 5 of the body: the 12 instructions from source lines 237–248. -/
def ed25519Join16ShippedSeg05 : List (JInstr 64) :=
  [ .storeMem "%rsp" 64 (.imm 0),  -- l.237 `movq $0, 64(%rsp)`
    .storeMem "%rsp" 56 (.imm 0),  -- l.238 `movq $0, 56(%rsp)`
    .storeMem "%rsp" 48 (.imm 0),  -- l.239 `movq $0, 48(%rsp)`
    .storeMem "%rsp" (-8) (.imm 0),  -- l.240 `movq $0, -8(%rsp)`
    .storeMem "%rsp" (-16) (.imm 0),  -- l.241 `movq $0, -16(%rsp)`
    .storeMem "%rsp" (-24) (.imm 0),  -- l.242 `movq $0, -24(%rsp)`
    .storeMem "%rsp" 40 (.imm 0),  -- l.243 `movq $0, 40(%rsp)`
    .storeMem "%rsp" 32 (.imm 0),  -- l.244 `movq $0, 32(%rsp)`
    .storeMem "%rsp" 24 (.imm 0),  -- l.245 `movq $0, 24(%rsp)`
    .storeMem "%rsp" 16 (.imm 0),  -- l.246 `movq $0, 16(%rsp)`
    .storeMem "%rsp" 8 (.imm 0),  -- l.247 `movq $0, 8(%rsp)`
    .storeMem "%rsp" 0 (.imm 0) ]  -- l.248 `movq $0, 0(%rsp)`

/-- The body of `ed25519_join16_x86_from_lean`, translated instruction by instruction by
    `bench/s2n_import/import_owned.sh`: the concatenation of its 5 segments. -/
def ed25519Join16ShippedBlock : List (JInstr 64) :=
  ed25519Join16ShippedSeg01 ++ ed25519Join16ShippedSeg02 ++ ed25519Join16ShippedSeg03 ++
  ed25519Join16ShippedSeg04 ++ ed25519Join16ShippedSeg05

/-- The frame instructions of `ed25519_join16_x86_from_lean` before the body,
    which the block omits: each `pushq r` as `leaq -8(%rsp), %rsp` followed by the
    store of `r` at `0(%rsp)`, and the stack allocation as the instruction the text
    contains. -/
def ed25519Join16ShippedPrologue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-112) ]  -- l.129 `leaq -112(%rsp), %rsp`

/-- The frame instructions of `ed25519_join16_x86_from_lean` after the body,
    which the block omits, `ret` excluded: the stack release as the instruction the
    text contains, and each `popq r` as the load of `r` from `0(%rsp)` followed by
    `leaq 8(%rsp), %rsp`. -/
def ed25519Join16ShippedEpilogue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 112 ]  -- l.249 `leaq 112(%rsp), %rsp`

/-- The block has 119 instructions; the count of each segment is computed by `rfl`. -/
theorem ed25519Join16ShippedBlock_length :
    ed25519Join16ShippedBlock.length = 119 := by
  unfold ed25519Join16ShippedBlock
  simp only [List.length_append]
  rfl

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519Join16Shipped
