/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Framed
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddSubSelectProof
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect

/-!
# The Curve25519 field kernels, carried to their encoded bytes

The functional results `Fe25519MulSqrProof.feMulBlock_correct`,
`Fe25519MulSqrProof.feSqrBlock_correct`, `Fe25519AddSubSelectProof.feAddBlock_correct` and
`Fe25519AddSubSelectProof.feSubBlock_correct` are stated over blocks with symbolic register
names (`"x"`, `"y"`, `"z"`, scratch names). This module
states them over the byte strings that the owned scalar encoder `encodeJBlock` produces,
in the form of `S2nMontmulP384.s2nMontmulP384FramedBytes_correct`.

## Construction, per kernel `K`

* `KAlloc` is the allocation `allocGp` computes for `K` under the kernel module's pins,
  written out as a literal list; `KAlloc_eq` checks it against the kernel module's
  allocation. The physical block `KPhys` is `renameBlock (nameOf KAlloc) K`: every
  symbolic name, including the memory bank names, replaced by its `%rN` register.
* `KFramed` places `KPhys` between `LeafFrame.framePrologue` and
  `LeafFrame.frameEpilogue`; each of the four allocations uses a callee-saved register.
  For `feMul` the body starts with `movq %rdx, %rcx`, which moves the third argument out
  of `%rdx`, the implicit `MULX` source.
* The encoded bytes are `encodeJBlock s2nAlloc KFramed`, under the identity allocation on
  the sixteen `%rN` names. `decode_phys` shows that they decode to `KFramed` itself.
* `runBlock_renameBlock_mem` transports the functional result from `K` to `KPhys` through
  `JInstrRegAllocScoped.runBlock_renameBlock_rel_on`, with the renamed state
  `pullState`; injectivity of `nameOf KAlloc` on the names of `K` is checked by
  `decide +kernel`.

## ABI

| kernel | symbol | arguments | output bank |
|---|---|---|---|
| `feMul` | `fe25519_mul_x86_from_lean` | `z = %rdi`, `x = %rsi`, `y = %rdx` (moved to `%rcx`) | `%rdi` |
| `feSqr` | `fe25519_sqr_x86_from_lean` | `z = %rdi`, `x = %rsi` | `%rdi` |
| `feAdd` | `fe25519_add_x86_from_lean` | `z = %rdi`, `x = %rsi`, `y = %rdx` | `%rdi` |
| `feSub` | `fe25519_sub_x86_from_lean` | `z = %rdi`, `x = %rsi`, `y = %rdx` | `%rdi` |

## Trust points

* That `decodeJStream` and `JasminModel.evalInstr` agree with an x86-64 processor on these
  instructions is not proved here.
* `JasminModel` keys memory by the base register's name. The input and output buffers
  are the banks `"%rsi"`, `"%rcx"` (the `feMul` multiplicand, passed in `%rdx`), `"%rdx"`
  (the `feAdd`/`feSub` second input) and `"%rdi"`; that the output does not alias an
  input is assumed. The red-zone slots
  are the bank `"%rsp"`; that they do not overlap the caller's buffers is the System V
  red-zone convention.
* The artifact lines `endbr64`, `retq` and the assembler directives are literal text and
  are not described; `ret` is outside `JInstr`.
* The `*_correct`/`*Bytes_correct` results are `∃ c, decode = some c ∧ ∀ st, …`: universally
  quantified over every machine state, with no `CorresJ`/`BytesCorresJ` guard. They carry no
  guard-satisfiability obligation (`scripts/ascent-nonvacuity-ratchet.sh`'s guard pass), because
  there is no guard to be vacuous over.

## Main results

* `pullState`, `runBlock_renameBlock_mem`, `runBlock_renameBlock_regs`: the functional
  transport along the allocation.
* `decode_phys`: a block of `s2nInstrOk` instructions decodes from its identity-allocated
  encoding to itself.
* `allDirect_map_renameJ`, `allDirect_decoded`, `decoded_constant_time`: the decoded
  instructions of a covered direct-addressing block are direct-addressing, so their
  leakage trace does not depend on the state.
* `feMulFramedBytes_correct`, `feSqrFramedBytes_correct`, `feAddFramedBytes_correct`,
  `feSubFramedBytes_correct`: the byte theorems.
* `feMulFramedBytes_constant_time`, `feSqrFramedBytes_constant_time`,
  `feAddFramedBytes_constant_time`, `feSubFramedBytes_constant_time`: the leakage trace of
  the decoded instructions is the same from any two states.

Provenance class: `@proved-hand-kernel theorems: feMulFramedBytes_correct, feSqrFramedBytes_correct, feAddFramedBytes_correct, feSubFramedBytes_correct`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFrame
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
  (s2nAlloc s2nInstrOk nameOf_s2nAlloc renameInstr_eq_self_of_fix)
open CatCrypt.Crypto.Optimizer.GenericRegAlloc (RenInjOn)
open CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (p25519)

/-! ## 1. Transport along the allocation -/

/-- The machine state `st` read through the renaming `ρ`: register `n` and bank `b` of the
    result are register `ρ n` and bank `ρ b` of `st`. -/
def pullState (ρ : String → String) (st : JState 64) : JState 64 :=
  { regs := fun n => st.regs (ρ n), flags := st.flags, mem := fun b => st.mem (ρ b) }

theorem stateRelOn_pullState (ns : List String) (ρ : String → String) (st : JState 64) :
    StateRelOn ns ρ st (pullState ρ st) :=
  ⟨fun _ _ => rfl, rfl, fun _ _ _ => rfl⟩

/-- Bank `ρ b` after the renamed block is bank `b` after the block run from the pulled
    state. -/
theorem runBlock_renameBlock_mem (ρ : String → String) (K : List (JInstr 64))
    (hinj : RenInjOn (blockNamesXsym K) ρ) (st : JState 64) (b : String)
    (hb : b ∈ blockNamesXsym K) :
    (runBlock st (Optimizer.RandomizedRegAlloc.renameBlock ρ K)).mem (ρ b)
      = (runBlock (pullState ρ st) K).mem b := by
  funext o
  exact (runBlock_renameBlock_rel_on hinj (stateRelOn_pullState _ ρ st) K
    (fun _ h => h)).memOn b hb o

/-- Register `ρ n` after the renamed block is register `n` after the block run from the
    pulled state. -/
theorem runBlock_renameBlock_regs (ρ : String → String) (K : List (JInstr 64))
    (hinj : RenInjOn (blockNamesXsym K) ρ) (st : JState 64) (n : String)
    (hn : n ∈ blockNamesXsym K) :
    (runBlock st (Optimizer.RandomizedRegAlloc.renameBlock ρ K)).regs (ρ n)
      = (runBlock (pullState ρ st) K).regs n :=
  (runBlock_renameBlock_rel_on hinj (stateRelOn_pullState _ ρ st) K
    (fun _ h => h)).regsOn n hn

/-- In a framed block whose body is `pre ++ renameBlock ρ K`, bank `ρ b ≠ "%rsp"` ends as
    bank `b` of `K` run from the pulled state after `pre`. -/
theorem framed_mem (st : JState 64) (pre : List (JInstr 64)) (ρ : String → String)
    (K : List (JInstr 64))
    (hsafe : ∀ i ∈ pre ++ Optimizer.RandomizedRegAlloc.renameBlock ρ K, frameSafe i = true)
    (hinj : RenInjOn (blockNamesXsym K) ρ) (b : String) (hb : b ∈ blockNamesXsym K)
    (hbr : ρ b ≠ "%rsp") :
    (runBlock st (framePrologue ++ (pre ++ Optimizer.RandomizedRegAlloc.renameBlock ρ K)
        ++ frameEpilogue)).mem (ρ b)
      = (runBlock (pullState ρ (runBlock st pre)) K).mem b := by
  rw [runBlock_framed_mem_other st _ hsafe _ hbr, Ascent.runBlock_append,
    runBlock_renameBlock_mem ρ K hinj _ b hb]

/-- `framed_mem` with an empty `pre`. -/
theorem framed_mem_nil (st : JState 64) (ρ : String → String) (K : List (JInstr 64))
    (hsafe : ∀ i ∈ Optimizer.RandomizedRegAlloc.renameBlock ρ K, frameSafe i = true)
    (hinj : RenInjOn (blockNamesXsym K) ρ) (b : String) (hb : b ∈ blockNamesXsym K)
    (hbr : ρ b ≠ "%rsp") :
    (runBlock st (framePrologue ++ Optimizer.RandomizedRegAlloc.renameBlock ρ K
        ++ frameEpilogue)).mem (ρ b)
      = (runBlock (pullState ρ st) K).mem b :=
  framed_mem st [] ρ K hsafe hinj b hb hbr

/-! ## 2. Decoding the identity-allocated encoding -/

/-- A block of `s2nInstrOk` instructions (covered, `MULX` from `%rdx`, canonical names)
    decodes from `encodeJBlock s2nAlloc` to itself. -/
theorem decode_phys (B : List (JInstr 64)) (h : B.all s2nInstrOk = true) :
    decodeJStream B.length (encodeJBlock s2nAlloc B) = some B := by
  have hok := List.all_eq_true.mp h
  have hc : ∀ i ∈ B, blockCovered i = true := fun i hi => by
    have := hok i hi
    simp only [s2nInstrOk, Bool.and_eq_true] at this
    exact this.1.1
  have hr : ∀ i ∈ B, mulxRdxOk s2nAlloc i = true := fun i hi => by
    have := hok i hi
    simp only [s2nInstrOk, Bool.and_eq_true] at this
    exact this.1.2
  rw [roundtrip_block _ _ hc hr]
  refine congrArg some ((List.map_congr_left fun i hi => ?_).trans (List.map_id _))
  rw [renameJ_eq_renameInstr _ _ (loadSymFree_of_blockCovered _ (hc i hi))]
  refine renameInstr_eq_self_of_fix _ _ fun n hn => nameOf_s2nAlloc n ?_
  have := hok i hi
  simp only [s2nInstrOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact this.2 n hn

/-! ## 3. Constant time over the decoded instructions -/

/-- Resolving names through an allocation keeps an instruction direct-addressing. -/
theorem isDirect_renameJ (alloc : GpAlloc) (i : JInstr 64) :
    IsDirect (renameJ alloc i) ↔ IsDirect i := by
  cases i <;> simp [renameJ, IsDirect]

/-- Resolving names through an allocation preserves `allDirect`. -/
theorem allDirect_map_renameJ (alloc : GpAlloc) (block : List (JInstr 64)) :
    allDirect (block.map (renameJ alloc)) = allDirect block := by
  unfold allDirect
  induction block with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.all_cons, ih]
    rw [decide_eq_decide.mpr (isDirect_renameJ alloc i)]

/-- **The decoded instructions of a covered direct-addressing block are
    direct-addressing.** -/
theorem allDirect_decoded (alloc : GpAlloc) (block : List (JInstr 64))
    (hc : ∀ i ∈ block, blockCovered i = true) (hr : ∀ i ∈ block, mulxRdxOk alloc i = true)
    (hd : allDirect block = true) (c : List (JInstr 64))
    (hdec : decodeJStream block.length (encodeJBlock alloc block) = some c) :
    allDirect c = true := by
  rw [roundtrip_block alloc block hc hr, Option.some.injEq] at hdec
  rw [← hdec, allDirect_map_renameJ]
  exact hd

/-- **Constant time over the bytes.** The instructions that the encoding of a covered
    direct-addressing block decodes to have the same leakage trace from any two
    states. -/
theorem decoded_constant_time (alloc : GpAlloc) (block : List (JInstr 64))
    (hc : ∀ i ∈ block, blockCovered i = true) (hr : ∀ i ∈ block, mulxRdxOk alloc i = true)
    (hd : allDirect block = true) (c : List (JInstr 64))
    (hdec : decodeJStream block.length (encodeJBlock alloc block) = some c)
    (s₁ s₂ : JState 64) : blockLeak s₁ c = blockLeak s₂ c :=
  allDirect_constant_time c (allDirect_decoded alloc block hc hr hd c hdec) s₁ s₂

/-- `decoded_constant_time` for a block of `s2nInstrOk` instructions. -/
theorem phys_constant_time (B : List (JInstr 64)) (h : B.all s2nInstrOk = true)
    (hd : allDirect B = true) (c : List (JInstr 64))
    (hdec : decodeJStream B.length (encodeJBlock s2nAlloc B) = some c)
    (s₁ s₂ : JState 64) : blockLeak s₁ c = blockLeak s₂ c := by
  rw [decode_phys B h, Option.some.injEq] at hdec
  subst hdec
  exact allDirect_constant_time _ hd s₁ s₂

/-- `allDirect` of a framed block from `allDirect` of the renamed body. -/
theorem allDirect_framed (pre K : List (JInstr 64)) (ρ : String → String)
    (hpre : allDirect pre = true) (hK : allDirect K = true) :
    allDirect (framePrologue ++ (pre ++ Optimizer.RandomizedRegAlloc.renameBlock ρ K)
      ++ frameEpilogue) = true := by
  simp only [allDirect_append, hpre, ScalarCompileCorrect.allDirect_renameBlock, hK]
  decide

/-- The registers `%rsp` and the callee-saved registers, unwritten by a block, end at
    their entry values. -/
theorem frameRegs_of_not_written (st : JState 64) (B : List (JInstr 64))
    (h : B.all (fun i => ("%rsp" :: calleeSavedRegs).all
      (fun r => decide (r ∉ Optimizer.SpillingRegAlloc.writtenNames i))) = true)
    (r : String) (hr : r ∈ "%rsp" :: calleeSavedRegs) :
    (runBlock st B).regs r = st.regs r :=
  runBlock_regs_of_not_written st B r fun i hi => by
    have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
    simpa using this

/-- The framed block ends with `%rsp` and the callee-saved registers at their entry
    values. -/
theorem framed_frameRegs (st : JState 64) (body : List (JInstr 64))
    (hb : ∀ i ∈ body, frameSafe i = true) (r : String)
    (hr : r ∈ "%rsp" :: calleeSavedRegs) :
    (runBlock st (framePrologue ++ body ++ frameEpilogue)).regs r = st.regs r := by
  rcases List.mem_cons.mp hr with rfl | hr'
  · exact runBlock_framed_rsp st body hb
  · exact runBlock_framed_calleeSaved st body hb r hr'

/-! ## 4. The field multiply `feMul` -/

section FeMul

open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (feMulBlock feMulAlloc)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof (mem4)

/-- The allocation of `feMulBlock`: `z = %rdi`, `x = %rsi`, the `MULX` multiplier
    `yd = %rdx`, the zero register `zr = %rbp`, the multiplicand pointer `y = %rcx`, and the
    working registers first-fit. -/
def feMulAllocL : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("zr", "%rbp"), ("y", "%rcx"),
    ("t1", "%r8"), ("t0", "%r9"), ("t2", "%r10"), ("lo", "%r11"), ("t3", "%rax"),
    ("t4", "%rbx"), ("hi", "%r12"), ("t5", "%r13"), ("t6", "%r14"), ("t7", "%r15")]

/-- `feMulAllocL` is the allocation `Fe25519MulKernel.feMulAlloc` computes. -/
theorem feMulAllocL_eq : feMulAlloc = feMulAllocL := by decide +kernel

/-- `feMulBlock` with every name replaced by its register under `feMulAllocL`. -/
def feMulPhys : List (JInstr 64) :=
  Optimizer.RandomizedRegAlloc.renameBlock (nameOf feMulAllocL) feMulBlock

/-- `movq %rdx, %rcx`: the multiplicand pointer, passed in `%rdx`, moved to `%rcx`. -/
def feMulPre : List (JInstr 64) := [.mov "%rcx" (.reg "%rdx")]

/-- The framed field multiply. -/
def feMulFramed : List (JInstr 64) := framePrologue ++ (feMulPre ++ feMulPhys) ++ frameEpilogue

theorem feMulFramed_length : feMulFramed.length = 108 := by decide +kernel

theorem feMulFramed_instrOk : feMulFramed.all s2nInstrOk = true := by decide +kernel

theorem feMul_body_frameSafe : ∀ i ∈ feMulPre ++ feMulPhys, frameSafe i = true :=
  List.all_eq_true.mp (by decide +kernel)

theorem feMul_renInjOn : RenInjOn (blockNamesXsym feMulBlock) (nameOf feMulAllocL) := by
  decide +kernel

/-- **The framed field multiply computes the product modulo `p25519` and restores the
    frame.** For every machine state, with `x` the four words at `%rsi` and `y` the four
    words at `%rcx`, running `feMulFramed` stores at `[%rdi + 0], …, [%rdi + 24]` a value
    `z < p25519` with `z = x · y` in `ZMod p25519`, and ends with `%rsp` and each
    callee-saved register at its entry value. -/
theorem feMulFramed_correct (st : JState 64) :
    mem4 (runBlock st feMulFramed).mem "%rdi" < p25519 ∧
      ((mem4 (runBlock st feMulFramed).mem "%rdi" : Nat) : ZMod p25519)
        = (mem4 st.mem "%rsi" : ZMod p25519) * (mem4 st.mem "%rcx" : ZMod p25519) ∧
      ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st feMulFramed).regs r = st.regs r := by
  have hz : nameOf feMulAllocL "z" = "%rdi" := by decide
  have hm := framed_mem st feMulPre _ feMulBlock feMul_body_frameSafe feMul_renInjOn "z"
    (by decide +kernel) (by rw [hz]; decide)
  rw [hz] at hm
  have hx : (pullState (nameOf feMulAllocL) (runBlock st feMulPre)).mem "x" = st.mem "%rsi" := by
    have : nameOf feMulAllocL "x" = "%rsi" := by decide
    simp only [pullState, this]
    rfl
  have hy : (pullState (nameOf feMulAllocL) (runBlock st feMulPre)).mem "y" = st.mem "%rcx" := by
    have : nameOf feMulAllocL "y" = "%rcx" := by decide
    simp only [pullState, this]
    rfl
  obtain ⟨h1, h2⟩ :=
    Fe25519MulSqrProof.feMulBlock_correct (pullState (nameOf feMulAllocL) (runBlock st feMulPre))
  have e : mem4 (runBlock st feMulFramed).mem "%rdi"
      = mem4 (runBlock (pullState (nameOf feMulAllocL) (runBlock st feMulPre)) feMulBlock).mem
          "z" := by
    simp only [mem4, feMulFramed, feMulPhys, hm]
  simp only [mem4, hx, hy] at h2
  have hr : ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st feMulFramed).regs r = st.regs r := by
    unfold feMulFramed
    exact framed_frameRegs st _ feMul_body_frameSafe
  rw [e]
  refine ⟨h1, ?_, hr⟩
  simpa only [mem4] using h2

/-- **The encoded framed field multiply.** The byte string
    `encodeJBlock s2nAlloc feMulFramed` decodes as 108 instructions `c` such that, for
    every machine state, with `x` the four words at `%rsi` and `y` the four words at
    `%rcx`, running `c` stores at `[%rdi + 0], …, [%rdi + 24]` a value `z < p25519` with
    `z = x · y` in `ZMod p25519`, and ends with `%rsp` and each callee-saved register at
    its entry value. -/
theorem feMulFramedBytes_correct :
    ∃ c, decodeJStream 108 (encodeJBlock s2nAlloc feMulFramed) = some c ∧
      ∀ st : JState 64,
        mem4 (runBlock st c).mem "%rdi" < p25519 ∧
          ((mem4 (runBlock st c).mem "%rdi" : Nat) : ZMod p25519)
            = (mem4 st.mem "%rsi" : ZMod p25519) * (mem4 st.mem "%rcx" : ZMod p25519) ∧
          ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st c).regs r = st.regs r :=
  ⟨feMulFramed, feMulFramed_length ▸ decode_phys _ feMulFramed_instrOk, feMulFramed_correct⟩

/-- **Constant time over the encoded framed field multiply.** -/
theorem feMulFramedBytes_constant_time (c : List (JInstr 64))
    (hdec : decodeJStream 108 (encodeJBlock s2nAlloc feMulFramed) = some c)
    (s₁ s₂ : JState 64) : blockLeak s₁ c = blockLeak s₂ c :=
  phys_constant_time _ feMulFramed_instrOk
    (allDirect_framed _ _ _ (by decide) Fe25519MulKernel.feMulBlock_allDirect) c
    (feMulFramed_length ▸ hdec) s₁ s₂

end FeMul

/-! ## 5. The field square `feSqr` -/

section FeSqr

open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel (feSqrBlock feSqrAlloc)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof (mem4)

/-- The allocation of `feSqrBlock`: `z = %rdi`, `x = %rsi`, the `MULX` multiplier
    `yd = %rdx`, the zero register `zr = %rbp`, and the working registers first-fit. -/
def feSqrAllocL : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("zr", "%rbp"), ("t1", "%rcx"),
    ("t0", "%r8"), ("t2", "%r9"), ("lo", "%r10"), ("t3", "%r11"), ("t4", "%rax"),
    ("hi", "%rbx"), ("t5", "%r12"), ("t6", "%r13"), ("t7", "%r14"), ("y", "%r15")]

/-- `feSqrAllocL` is the allocation `Fe25519OpsKernel.feSqrAlloc` computes. -/
theorem feSqrAllocL_eq : feSqrAlloc = feSqrAllocL := by decide +kernel

/-- `feSqrBlock` with every name replaced by its register under `feSqrAllocL`. -/
def feSqrPhys : List (JInstr 64) :=
  Optimizer.RandomizedRegAlloc.renameBlock (nameOf feSqrAllocL) feSqrBlock

/-- The framed field square. -/
def feSqrFramed : List (JInstr 64) := framePrologue ++ feSqrPhys ++ frameEpilogue

theorem feSqrFramed_length : feSqrFramed.length = 107 := by decide +kernel

theorem feSqrFramed_instrOk : feSqrFramed.all s2nInstrOk = true := by decide +kernel

theorem feSqr_body_frameSafe : ∀ i ∈ feSqrPhys, frameSafe i = true :=
  List.all_eq_true.mp (by decide +kernel)

theorem feSqr_renInjOn : RenInjOn (blockNamesXsym feSqrBlock) (nameOf feSqrAllocL) := by
  decide +kernel

/-- **The framed field square computes the square modulo `p25519` and restores the
    frame.** For every machine state, with `x` the four words at `%rsi`, running
    `feSqrFramed` stores at `[%rdi + 0], …, [%rdi + 24]` a value `z < p25519` with
    `z = x²` in `ZMod p25519`, and ends with `%rsp` and each callee-saved register at its
    entry value. -/
theorem feSqrFramed_correct (st : JState 64) :
    mem4 (runBlock st feSqrFramed).mem "%rdi" < p25519 ∧
      ((mem4 (runBlock st feSqrFramed).mem "%rdi" : Nat) : ZMod p25519)
        = (mem4 st.mem "%rsi" : ZMod p25519) ^ 2 ∧
      ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st feSqrFramed).regs r = st.regs r := by
  have hz : nameOf feSqrAllocL "z" = "%rdi" := by decide
  have hm := framed_mem_nil st _ feSqrBlock feSqr_body_frameSafe feSqr_renInjOn "z"
    (by decide +kernel) (by rw [hz]; decide)
  rw [hz] at hm
  have hx : (pullState (nameOf feSqrAllocL) st).mem "x" = st.mem "%rsi" := by
    have : nameOf feSqrAllocL "x" = "%rsi" := by decide
    simp only [pullState, this]
  obtain ⟨h1, h2⟩ := Fe25519MulSqrProof.feSqrBlock_correct (pullState (nameOf feSqrAllocL) st)
  have e : mem4 (runBlock st feSqrFramed).mem "%rdi"
      = mem4 (runBlock (pullState (nameOf feSqrAllocL) st) feSqrBlock).mem "z" := by
    simp only [mem4, feSqrFramed, feSqrPhys, hm]
  simp only [mem4, hx] at h2
  have hr : ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st feSqrFramed).regs r = st.regs r := by
    unfold feSqrFramed
    exact framed_frameRegs st _ feSqr_body_frameSafe
  rw [e]
  refine ⟨h1, ?_, hr⟩
  simpa only [mem4] using h2

/-- **The encoded framed field square.** The byte string
    `encodeJBlock s2nAlloc feSqrFramed` decodes as 107 instructions `c` such that, for every
    machine state, with `x` the four words at `%rsi`, running `c` stores at
    `[%rdi + 0], …, [%rdi + 24]` a value `z < p25519` with `z = x²` in `ZMod p25519`, and
    ends with `%rsp` and each callee-saved register at its entry value. -/
theorem feSqrFramedBytes_correct :
    ∃ c, decodeJStream 107 (encodeJBlock s2nAlloc feSqrFramed) = some c ∧
      ∀ st : JState 64,
        mem4 (runBlock st c).mem "%rdi" < p25519 ∧
          ((mem4 (runBlock st c).mem "%rdi" : Nat) : ZMod p25519)
            = (mem4 st.mem "%rsi" : ZMod p25519) ^ 2 ∧
          ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st c).regs r = st.regs r :=
  ⟨feSqrFramed, feSqrFramed_length ▸ decode_phys _ feSqrFramed_instrOk, feSqrFramed_correct⟩

/-- **Constant time over the encoded framed field square.** -/
theorem feSqrFramedBytes_constant_time (c : List (JInstr 64))
    (hdec : decodeJStream 107 (encodeJBlock s2nAlloc feSqrFramed) = some c)
    (s₁ s₂ : JState 64) : blockLeak s₁ c = blockLeak s₂ c :=
  phys_constant_time _ feSqrFramed_instrOk
    (allDirect_framed [] _ _ rfl Fe25519OpsKernel.feSqrBlock_allDirect) c
    (feSqrFramed_length ▸ hdec) s₁ s₂

end FeSqr

/-! ## 6. The field add `feAdd` and subtract `feSub` -/

section FeAddSub

open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel
  (feAddBlock feSubBlock feAddAlloc feSubAlloc)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddSubSelectProof (mem4)

/-- The allocation of `feAddBlock`: `z = %rdi`, `x = %rsi`, `y = %rdx`, and the working
    registers first-fit. -/
def feAddAllocL : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("y", "%rdx"), ("d0", "%rcx"), ("lo", "%r8"),
    ("d1", "%r9"), ("d2", "%r10"), ("d3", "%r11"), ("c0", "%rax"), ("c1", "%rbx"),
    ("c2", "%r12"), ("c3", "%r13"), ("m", "%r14")]

/-- The allocation of `feSubBlock`: `z = %rdi`, `x = %rsi`, `y = %rdx`, and the working
    registers first-fit. -/
def feSubAllocL : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("y", "%rdx"), ("d0", "%rcx"), ("lo", "%r8"),
    ("d1", "%r9"), ("d2", "%r10"), ("d3", "%r11"), ("c", "%rax"), ("zr", "%rbx")]

/-- `feAddAllocL` is the allocation `Fe25519OpsKernel.feAddAlloc` computes. -/
theorem feAddAllocL_eq : feAddAlloc = feAddAllocL := by decide +kernel

/-- `feSubAllocL` is the allocation `Fe25519OpsKernel.feSubAlloc` computes. -/
theorem feSubAllocL_eq : feSubAlloc = feSubAllocL := by decide +kernel

/-- `feAddBlock` with every name replaced by its register under `feAddAllocL`. -/
def feAddPhys : List (JInstr 64) :=
  Optimizer.RandomizedRegAlloc.renameBlock (nameOf feAddAllocL) feAddBlock

/-- `feSubBlock` with every name replaced by its register under `feSubAllocL`. -/
def feSubPhys : List (JInstr 64) :=
  Optimizer.RandomizedRegAlloc.renameBlock (nameOf feSubAllocL) feSubBlock

/-- The framed field add. -/
def feAddFramed : List (JInstr 64) := framePrologue ++ feAddPhys ++ frameEpilogue

/-- The framed field subtract. -/
def feSubFramed : List (JInstr 64) := framePrologue ++ feSubPhys ++ frameEpilogue

theorem feAddFramed_length : feAddFramed.length = 57 := by decide +kernel
theorem feSubFramed_length : feSubFramed.length = 38 := by decide +kernel

theorem feAddFramed_instrOk : feAddFramed.all s2nInstrOk = true := by decide +kernel
theorem feSubFramed_instrOk : feSubFramed.all s2nInstrOk = true := by decide +kernel

theorem feAdd_body_frameSafe : ∀ i ∈ feAddPhys, frameSafe i = true :=
  List.all_eq_true.mp (by decide +kernel)
theorem feSub_body_frameSafe : ∀ i ∈ feSubPhys, frameSafe i = true :=
  List.all_eq_true.mp (by decide +kernel)

theorem feAdd_renInjOn : RenInjOn (blockNamesXsym feAddBlock) (nameOf feAddAllocL) := by
  decide +kernel
theorem feSub_renInjOn : RenInjOn (blockNamesXsym feSubBlock) (nameOf feSubAllocL) := by
  decide +kernel

/-- **The framed field add computes the sum modulo `p25519` and restores the frame.** For
    every machine state whose four words `x` at `%rsi` and `y` at `%rdx` satisfy
    `x + y < 2 · p25519`, running `feAddFramed` stores at `[%rdi + 0], …, [%rdi + 24]` the
    value `(x + y) mod p25519`, which is below `p25519` and equals `x + y` in
    `ZMod p25519`, and ends with `%rsp` and each callee-saved register at its entry
    value. -/
theorem feAddFramed_correct (st : JState 64)
    (h : mem4 st.mem "%rsi" + mem4 st.mem "%rdx" < 2 * p25519) :
    mem4 (runBlock st feAddFramed).mem "%rdi" = (mem4 st.mem "%rsi" + mem4 st.mem "%rdx") % p25519 ∧
      mem4 (runBlock st feAddFramed).mem "%rdi" < p25519 ∧
      ((mem4 (runBlock st feAddFramed).mem "%rdi" : Nat) : ZMod p25519)
        = (mem4 st.mem "%rsi" : ZMod p25519) + (mem4 st.mem "%rdx" : Nat) ∧
      ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st feAddFramed).regs r = st.regs r := by
  have hz : nameOf feAddAllocL "z" = "%rdi" := by decide
  have hm := framed_mem_nil st _ feAddBlock feAdd_body_frameSafe feAdd_renInjOn "z"
    (by decide +kernel) (by rw [hz]; decide)
  rw [hz] at hm
  have hx : (pullState (nameOf feAddAllocL) st).mem "x" = st.mem "%rsi" := by
    have : nameOf feAddAllocL "x" = "%rsi" := by decide
    simp only [pullState, this]
  have hy : (pullState (nameOf feAddAllocL) st).mem "y" = st.mem "%rdx" := by
    have : nameOf feAddAllocL "y" = "%rdx" := by decide
    simp only [pullState, this]
  have h' : mem4 (pullState (nameOf feAddAllocL) st).mem "x"
      + mem4 (pullState (nameOf feAddAllocL) st).mem "y" < 2 * p25519 := by
    simpa only [mem4, hx, hy] using h
  obtain ⟨h0, h1, h2, -⟩ :=
    Fe25519AddSubSelectProof.feAddBlock_correct (pullState (nameOf feAddAllocL) st) h'
  have e : mem4 (runBlock st feAddFramed).mem "%rdi"
      = mem4 (runBlock (pullState (nameOf feAddAllocL) st) feAddBlock).mem "z" := by
    simp only [mem4, feAddFramed, feAddPhys, hm]
  simp only [mem4, hx, hy] at h0 h2
  have hr : ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st feAddFramed).regs r = st.regs r := by
    unfold feAddFramed
    exact framed_frameRegs st _ feAdd_body_frameSafe
  rw [e]
  refine ⟨?_, h1, ?_, hr⟩
  · simpa only [mem4] using h0
  · simpa only [mem4] using h2

/-- **The framed field subtract computes the difference modulo `p25519` and restores the
    frame.** For every machine state whose four words `x` at `%rsi` and `y` at `%rdx`
    satisfy `x < y + p25519` and `y ≤ x + p25519`, running `feSubFramed` stores at
    `[%rdi + 0], …, [%rdi + 24]` the value `(x + p25519 - y) mod p25519`, which is below
    `p25519` and equals `x - y` in `ZMod p25519`, and ends with `%rsp` and each
    callee-saved register at its entry value. -/
theorem feSubFramed_correct (st : JState 64)
    (h1 : mem4 st.mem "%rsi" < mem4 st.mem "%rdx" + p25519)
    (h2 : mem4 st.mem "%rdx" ≤ mem4 st.mem "%rsi" + p25519) :
    mem4 (runBlock st feSubFramed).mem "%rdi"
        = (mem4 st.mem "%rsi" + p25519 - mem4 st.mem "%rdx") % p25519 ∧
      mem4 (runBlock st feSubFramed).mem "%rdi" < p25519 ∧
      ((mem4 (runBlock st feSubFramed).mem "%rdi" : Nat) : ZMod p25519)
        = (mem4 st.mem "%rsi" : ZMod p25519) - (mem4 st.mem "%rdx" : Nat) ∧
      ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st feSubFramed).regs r = st.regs r := by
  have hz : nameOf feSubAllocL "z" = "%rdi" := by decide
  have hm := framed_mem_nil st _ feSubBlock feSub_body_frameSafe feSub_renInjOn "z"
    (by decide +kernel) (by rw [hz]; decide)
  rw [hz] at hm
  have hx : (pullState (nameOf feSubAllocL) st).mem "x" = st.mem "%rsi" := by
    have : nameOf feSubAllocL "x" = "%rsi" := by decide
    simp only [pullState, this]
  have hy : (pullState (nameOf feSubAllocL) st).mem "y" = st.mem "%rdx" := by
    have : nameOf feSubAllocL "y" = "%rdx" := by decide
    simp only [pullState, this]
  have h1' : mem4 (pullState (nameOf feSubAllocL) st).mem "x"
      < mem4 (pullState (nameOf feSubAllocL) st).mem "y" + p25519 := by
    simpa only [mem4, hx, hy] using h1
  have h2' : mem4 (pullState (nameOf feSubAllocL) st).mem "y"
      ≤ mem4 (pullState (nameOf feSubAllocL) st).mem "x" + p25519 := by
    simpa only [mem4, hx, hy] using h2
  obtain ⟨g0, g1, g2, -⟩ :=
    Fe25519AddSubSelectProof.feSubBlock_correct (pullState (nameOf feSubAllocL) st) h1' h2'
  have e : mem4 (runBlock st feSubFramed).mem "%rdi"
      = mem4 (runBlock (pullState (nameOf feSubAllocL) st) feSubBlock).mem "z" := by
    simp only [mem4, feSubFramed, feSubPhys, hm]
  simp only [mem4, hx, hy] at g0 g2
  have hr : ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st feSubFramed).regs r = st.regs r := by
    unfold feSubFramed
    exact framed_frameRegs st _ feSub_body_frameSafe
  rw [e]
  refine ⟨?_, g1, ?_, hr⟩
  · simpa only [mem4] using g0
  · simpa only [mem4] using g2

/-- **The encoded framed field add.** The byte string `encodeJBlock s2nAlloc feAddFramed`
    decodes as 57 instructions `c` such that, for every machine state whose four words
    `x` at `%rsi` and `y` at `%rdx` satisfy `x + y < 2 · p25519`, running `c` stores at
    `[%rdi + 0], …, [%rdi + 24]` the value `(x + y) mod p25519`, below `p25519` and equal
    to `x + y` in `ZMod p25519`, and ends with `%rsp` and each callee-saved register at its
    entry value. -/
theorem feAddFramedBytes_correct :
    ∃ c, decodeJStream 57 (encodeJBlock s2nAlloc feAddFramed) = some c ∧
      ∀ st : JState 64, mem4 st.mem "%rsi" + mem4 st.mem "%rdx" < 2 * p25519 →
        mem4 (runBlock st c).mem "%rdi" = (mem4 st.mem "%rsi" + mem4 st.mem "%rdx") % p25519 ∧
          mem4 (runBlock st c).mem "%rdi" < p25519 ∧
          ((mem4 (runBlock st c).mem "%rdi" : Nat) : ZMod p25519)
            = (mem4 st.mem "%rsi" : ZMod p25519) + (mem4 st.mem "%rdx" : Nat) ∧
          ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st c).regs r = st.regs r :=
  ⟨feAddFramed, feAddFramed_length ▸ decode_phys _ feAddFramed_instrOk, feAddFramed_correct⟩

/-- **The encoded framed field subtract.** The byte string
    `encodeJBlock s2nAlloc feSubFramed` decodes as 38 instructions `c` such that, for every
    machine state whose four words `x` at `%rsi` and `y` at `%rdx` satisfy
    `x < y + p25519` and `y ≤ x + p25519`, running `c` stores at
    `[%rdi + 0], …, [%rdi + 24]` the value `(x + p25519 - y) mod p25519`, below `p25519`
    and equal to `x - y` in `ZMod p25519`, and ends with `%rsp` and each callee-saved
    register at its entry value. -/
theorem feSubFramedBytes_correct :
    ∃ c, decodeJStream 38 (encodeJBlock s2nAlloc feSubFramed) = some c ∧
      ∀ st : JState 64, mem4 st.mem "%rsi" < mem4 st.mem "%rdx" + p25519 →
        mem4 st.mem "%rdx" ≤ mem4 st.mem "%rsi" + p25519 →
        mem4 (runBlock st c).mem "%rdi"
            = (mem4 st.mem "%rsi" + p25519 - mem4 st.mem "%rdx") % p25519 ∧
          mem4 (runBlock st c).mem "%rdi" < p25519 ∧
          ((mem4 (runBlock st c).mem "%rdi" : Nat) : ZMod p25519)
            = (mem4 st.mem "%rsi" : ZMod p25519) - (mem4 st.mem "%rdx" : Nat) ∧
          ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st c).regs r = st.regs r :=
  ⟨feSubFramed, feSubFramed_length ▸ decode_phys _ feSubFramed_instrOk, feSubFramed_correct⟩

/-- **Constant time over the encoded framed field add.** -/
theorem feAddFramedBytes_constant_time (c : List (JInstr 64))
    (hdec : decodeJStream 57 (encodeJBlock s2nAlloc feAddFramed) = some c)
    (s₁ s₂ : JState 64) : blockLeak s₁ c = blockLeak s₂ c :=
  phys_constant_time _ feAddFramed_instrOk
    (allDirect_framed [] _ _ rfl Fe25519OpsKernel.feAddBlock_allDirect) c
    (feAddFramed_length ▸ hdec) s₁ s₂

/-- **Constant time over the encoded framed field subtract.** -/
theorem feSubFramedBytes_constant_time (c : List (JInstr 64))
    (hdec : decodeJStream 38 (encodeJBlock s2nAlloc feSubFramed) = some c)
    (s₁ s₂ : JState 64) : blockLeak s₁ c = blockLeak s₂ c :=
  phys_constant_time _ feSubFramed_instrOk
    (allDirect_framed [] _ _ rfl Fe25519OpsKernel.feSubBlock_allDirect) c
    (feSubFramed_length ▸ hdec) s₁ s₂

end FeAddSub

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes
