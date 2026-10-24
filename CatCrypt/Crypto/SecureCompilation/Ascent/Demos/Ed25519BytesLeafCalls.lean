/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519FramedCalls

/-!
# The shipped Ed25519 call sequences over the byte-encoded field leaves

The crate `catcrypt-ed25519` ships `fe25519_{mul,sqr,add,sub}_x86_from_lean.s` as the
bytes `encodeJBlock s2nAlloc feXFramed`. These decode to
`Fe25519KernelsBytes.feMulFramed`, `feSqrFramed`, `feAddFramed` and `feSubFramed`
(`feXFramed_decode`): the kernel body over physical registers, between
`LeafFrame.framePrologue` (six stores of the callee-saved registers into the red zone
below `%rsp`) and `LeafFrame.frameEpilogue` (six loads back). This module states the four
blocks over `AddrMem.runBlockA`, in the form the Ed25519 call models read: the four-limb
value at the output pointer `%rdi`, no byte changed outside the output and the 48 bytes
below `%rsp`, and `%rsp` and the callee-saved registers at their entry values. It then
states the shipped `ed25519_madd`, `ed25519_invert` and `ed25519_compress` over call
models in which every field-leaf call runs those decoded blocks.

## The leaves

Each body `c` is, up to the two-operand form of `imul` by an immediate (`deImulri`) or a
leading self-move, the body of the imported `fe25519_*` text, whose address-machine
statement `Ed25519LeafCallees.{mulCore, sqrShipped, addShipped, subShipped}_correct_addr`
comes from the name-keyed kernel theorem through `AddrMemDerived`. The body statement
holds at every state and allows the output to coincide with an input. The red-zone
prologue and epilogue are handled by `redFramed_frame`, `redFramed_rsp` and
`redFramed_saved`, for any body that changes only the four words at `%rdi` and keeps
`%rsp`; the inputs are read after the prologue, so they are required to lie outside the
red-zone slots, and the callee-saved registers are reloaded from those slots, so the
output is required to lie outside them too.

## The calls

A byte-decoded leaf pushes nothing and allocates no stack, so a call to one is
`Ed25519FramedCalls.leafCall` with the empty frame `CallFrame.framePro [] 0` and
`CallFrame.frameEpi [] 0`. Its red zone at the callee's `%rsp` lies among the eighteen
words below the caller's `%rsp`, so the hypotheses at each call are those of
`Ed25519FramedCalls` (`CallSep`, `SqrSep`), and the call models meet the callee
specifications `MaddCalleesF`, `InvertCallees` (through `invertCallModelPB`) and
`CompressCalleesF` with no further hypothesis. `ed25519_join16`, `ed25519_invert` and
`ed25519_pack_sign` are not field leaves and run their shipped `pushq`-framed text as in
`Ed25519FramedCalls`.

Each body `c` is, up to the two-operand form of `imul` by an immediate (`deImulri`) or a
leading self-move, the body of the imported `fe25519_*` text, whose address-machine
statement `Ed25519LeafCallees.{mulCore, sqrShipped, addShipped, subShipped}_correct_addr`
comes from the name-keyed kernel theorem through `AddrMemDerived`. The body statement
holds at every state and allows the output to coincide with an input. The red-zone
prologue and epilogue are handled by `redFramed_frame`, `redFramed_rsp` and
`redFramed_saved`, for any body that changes only the four words at `%rdi` and keeps
`%rsp`; the inputs are read after the prologue, so they are required to lie outside the
red-zone slots, and the callee-saved registers are reloaded from those slots, so the
output is required to lie outside them too.

## Main definitions

* `CoreOK`: a body that changes only the four words at `%rdi` and keeps `%rsp`.
* `redFramed`: a body between the red-zone prologue and epilogue.
* `bytesLeafCall`, `mulCallB`, `sqrCallB`, `addCallB`, `subCallB`: the calls of the
  byte-decoded leaves.
* `maddCallModelB`, `invertCallModelB`, `compressCallModelB`: the call models; `invertCallB`
  the call of the inversion over `invertCallModelB`.

## Main results

* `feMulFramed_decode`, `feSqrFramed_decode`, `feAddFramed_decode`, `feSubFramed_decode`:
  the encoded bytes decode to the framed blocks.
* `redFramed_frame`, `redFramed_rsp`, `redFramed_saved`: the frame of a red-zone framed
  body.
* `feMulFramed_correct_addr`, `feSqrFramed_correct_addr`, `feAddFramed_correct_addr`,
  `feSubFramed_correct_addr`: the four byte-decoded leaves on the address machine.
* `mulCallB_spec`, `sqrCallB_spec`, `addCallB_spec`, `subCallB_spec`: their calls.
* `maddShippedBytes_correct`, `maddShippedBytes_correct_cross`,
  `invertShippedBytes_correct`, `compressShippedBytes_correct`: the three shipped call
  sequences over the byte-decoded leaves.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519BytesLeaves

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFrame (framePrologue frameEpilogue)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (decodeJStream)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder (encodeJBlock)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384 (s2nAlloc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (calleeSavedRegs)

/-! ## 1. The encoded bytes decode to the framed blocks -/

/-- The encoded field multiply decodes to `feMulFramed`. -/
theorem feMulFramed_decode :
    decodeJStream 108 (encodeJBlock s2nAlloc feMulFramed) = some feMulFramed :=
  feMulFramed_length ▸ decode_phys _ feMulFramed_instrOk

/-- The encoded field square decodes to `feSqrFramed`. -/
theorem feSqrFramed_decode :
    decodeJStream 107 (encodeJBlock s2nAlloc feSqrFramed) = some feSqrFramed :=
  feSqrFramed_length ▸ decode_phys _ feSqrFramed_instrOk

/-- The encoded field add decodes to `feAddFramed`. -/
theorem feAddFramed_decode :
    decodeJStream 57 (encodeJBlock s2nAlloc feAddFramed) = some feAddFramed :=
  feAddFramed_length ▸ decode_phys _ feAddFramed_instrOk

/-- The encoded field subtract decodes to `feSubFramed`. -/
theorem feSubFramed_decode :
    decodeJStream 38 (encodeJBlock s2nAlloc feSubFramed) = some feSubFramed :=
  feSubFramed_length ▸ decode_phys _ feSubFramed_instrOk

/-! ## 2. Instruction identities on the address machine -/

theorem writeAddr_deImulri (sa : AState) (i : JInstr 64) :
    writeAddr sa (deImulri i) = writeAddr sa i := by
  unfold deImulri
  split
  · split <;> rfl
  · rfl

theorem writeVal_deImulri (s : JState 64) (i : JInstr 64) :
    writeVal s (deImulri i) = writeVal s i := by
  unfold deImulri
  split
  · split <;> rfl
  · rfl

/-- The two-operand form of a multiply by an immediate steps the address machine as the
    three-operand form. -/
theorem evalInstrA_deImulri (sa : AState) (i : JInstr 64) :
    evalInstrA sa (deImulri i) = evalInstrA sa i := by
  simp only [evalInstrA, evalInstr_deImulri, writeAddr_deImulri, writeVal_deImulri]

theorem runBlockA_map_deImulri (sa : AState) (blk : List (JInstr 64)) :
    runBlockA sa (blk.map deImulri) = runBlockA sa blk := by
  induction blk generalizing sa with
  | nil => rfl
  | cons i is ih => rw [List.map_cons, runBlockA_cons, runBlockA_cons, evalInstrA_deImulri, ih]

/-- A self-move leaves the address state unchanged. -/
theorem evalInstrA_mov_self (sa : AState) (d : String) :
    evalInstrA sa (.mov d (.reg d)) = sa := by
  simp only [evalInstrA, evalInstr_mov_self]
  rfl

/-! ## 3. The four bodies on the address machine -/

/-- A body that changes no byte outside the 32 bytes at `%rdi` and keeps `%rsp`, at every
    state. -/
def CoreOK (c : List (JInstr 64)) : Prop :=
  ∀ s : AState, FrameC s.mem (runBlockA s c).mem (s.regs "%rdi") 4
    ∧ (runBlockA s c).regs "%rsp" = s.regs "%rsp"

theorem runBlockA_mulBody (sa : AState) :
    runBlockA sa (feMulPre ++ feMulPhys) = runBlockA sa mulCore := by
  rw [← mulCore_deImulri, runBlockA_map_deImulri]

theorem runBlockA_sqrBody (sa : AState) :
    runBlockA sa feSqrPhys = runBlockA sa Fe25519SqrShipped.fe25519SqrShippedBlock := by
  rw [← sqr_deImulri, runBlockA_map_deImulri]

theorem runBlockA_addBody (sa : AState) :
    runBlockA sa feAddPhys = runBlockA sa Fe25519AddShipped.fe25519AddShippedBlock := by
  rw [add_split, runBlockA_cons, evalInstrA_mov_self]

theorem runBlockA_subBody (sa : AState) :
    runBlockA sa feSubPhys = runBlockA sa Fe25519SubShipped.fe25519SubShippedBlock := by
  rw [sub_split, runBlockA_cons, evalInstrA_mov_self]

/-- The body of the field multiply leaves the product modulo `2 ^ 255 - 19` at `%rdi`;
    an argument may coincide with the output. -/
theorem mulBody_correct_addr (sa : AState) :
    feO (runBlockA sa (feMulPre ++ feMulPhys)).mem (sa.regs "%rdi") 0
      = feO sa.mem (sa.regs "%rsi") 0 * feO sa.mem (sa.regs "%rdx") 0 % pM := by
  rw [runBlockA_mulBody]; exact (mulCore_correct_addr sa).1

theorem mulBody_ok : CoreOK (feMulPre ++ feMulPhys) := fun s => by
  rw [runBlockA_mulBody]; exact (mulCore_correct_addr s).2

/-- The body of the field square leaves the square modulo `2 ^ 255 - 19` at `%rdi`; the
    argument may coincide with the output. -/
theorem sqrBody_correct_addr (sa : AState) :
    feO (runBlockA sa feSqrPhys).mem (sa.regs "%rdi") 0
      = feO sa.mem (sa.regs "%rsi") 0 ^ 2 % pM := by
  rw [runBlockA_sqrBody]; exact (sqrShipped_correct_addr sa).1

theorem sqrBody_ok : CoreOK feSqrPhys := fun s => by
  rw [runBlockA_sqrBody]; exact (sqrShipped_correct_addr s).2

/-- The body of the field add leaves the sum modulo `2 ^ 255 - 19` at `%rdi`, for
    arguments below that prime. -/
theorem addBody_correct_addr (sa : AState) (h1 : feO sa.mem (sa.regs "%rsi") 0 < pM)
    (h2 : feO sa.mem (sa.regs "%rdx") 0 < pM) :
    feO (runBlockA sa feAddPhys).mem (sa.regs "%rdi") 0
      = (feO sa.mem (sa.regs "%rsi") 0 + feO sa.mem (sa.regs "%rdx") 0) % pM := by
  rw [runBlockA_addBody]; exact (addShipped_correct_addr sa).1 h1 h2

theorem addBody_ok : CoreOK feAddPhys := fun s => by
  rw [runBlockA_addBody]; exact (addShipped_correct_addr s).2

/-- The body of the field subtract leaves the difference modulo `2 ^ 255 - 19` at `%rdi`,
    for arguments below that prime. -/
theorem subBody_correct_addr (sa : AState) (h1 : feO sa.mem (sa.regs "%rsi") 0 < pM)
    (h2 : feO sa.mem (sa.regs "%rdx") 0 < pM) :
    feO (runBlockA sa feSubPhys).mem (sa.regs "%rdi") 0
      = (feO sa.mem (sa.regs "%rsi") 0 + (pM - feO sa.mem (sa.regs "%rdx") 0)) % pM := by
  rw [runBlockA_subBody]; exact (subShipped_correct_addr sa).1 h1 h2

theorem subBody_ok : CoreOK feSubPhys := fun s => by
  rw [runBlockA_subBody]; exact (subShipped_correct_addr s).2

/-! ## 4. The red-zone frame -/

/-- The body `c` between the red-zone prologue and epilogue. -/
def redFramed (c : List (JInstr 64)) : List (JInstr 64) := framePrologue ++ c ++ frameEpilogue

theorem redFramed_run (c : List (JInstr 64)) (s : AState) :
    runBlockA s (redFramed c)
      = runBlockA (runBlockA (runBlockA s framePrologue) c) frameEpilogue := by
  rw [redFramed, runBlockA_append, runBlockA_append]

/-- The memory after a framed body is the memory the body leaves after the prologue. -/
theorem redFramed_mem (c : List (JInstr 64)) (s : AState) :
    (runBlockA s (redFramed c)).mem = (runBlockA (runBlockA s framePrologue) c).mem := by
  rw [redFramed_run, frameEpilogue_mem]

/-- A four-limb value outside the 48 bytes below `%rsp` reads after the prologue as at
    entry. -/
theorem feO_prologue (s : AState) {p : BitVec 64}
    (hd : RangeDisj p 0 24 (s.regs "%rsp") (-48) (-8)) :
    feO (runBlockA s framePrologue).mem p 0 = feO s.mem p 0 :=
  feO_redFrame (framePrologue_frameC s) hd

/-- **The memory frame of a framed body.** No byte outside the 32 bytes at `%rdi` and the
    48 bytes below `%rsp` changes. -/
theorem redFramed_frame {c : List (JInstr 64)} (hc : CoreOK c) (s : AState) :
    FrameCRed s.mem (runBlockA s (redFramed c)).mem (s.regs "%rdi") 4 (s.regs "%rsp") 6 := by
  intro x hx hy
  have hfr := (hc (runBlockA s framePrologue)).1
  rw [framePrologue_regs] at hfr
  rw [redFramed_mem, hfr x hx]
  refine framePrologue_frameC s x fun k hk => ?_
  rw [addI, show (-48 : Int) + ((8 * k : Nat) : Int)
    = (-(8 * ((5 - k) + 1) : Nat) : Int) from by omega]
  exact hy (5 - k) (by omega)

/-- **A framed body keeps `%rsp`.** -/
theorem redFramed_rsp {c : List (JInstr 64)} (hc : CoreOK c) (s : AState) :
    (runBlockA s (redFramed c)).regs "%rsp" = s.regs "%rsp" := by
  rw [redFramed_run,
    runBlockA_regs_of_not_dsts _ frameEpilogue "%rsp" (rsp_not_dst_of_all (by decide +kernel)),
    (hc _).2, framePrologue_regs]

/-- **A framed body restores the callee-saved registers.** When the output buffer lies
    outside the 48 bytes below `%rsp`, the prologue stores each callee-saved register in
    its red-zone slot, the body leaves those slots unchanged, and the epilogue loads each
    register back. -/
theorem redFramed_saved {c : List (JInstr 64)} (hc : CoreOK c) (s : AState)
    (ho : RangeDisj (s.regs "%rdi") 0 24 (s.regs "%rsp") (-48) (-8)) :
    ∀ r ∈ calleeSavedRegs, (runBlockA s (redFramed c)).regs r = s.regs r := by
  rw [redFramed_run]
  set s1 := runBlockA s framePrologue with hs1
  set s2 := runBlockA s1 c with hs2
  have r1 : ∀ r, s1.regs r = s.regs r := framePrologue_regs s
  obtain ⟨hfr, hsp⟩ := hc s1
  rw [r1] at hfr hsp
  have m1 : s1.mem = write64 (write64 (write64 (write64 (write64 (write64 s.mem
      (s.regs "%rsp" + BitVec.ofInt 64 (-8)) (s.regs "%rbx"))
      (s.regs "%rsp" + BitVec.ofInt 64 (-16)) (s.regs "%rbp"))
      (s.regs "%rsp" + BitVec.ofInt 64 (-24)) (s.regs "%r12"))
      (s.regs "%rsp" + BitVec.ofInt 64 (-32)) (s.regs "%r13"))
      (s.regs "%rsp" + BitVec.ofInt 64 (-40)) (s.regs "%r14"))
      (s.regs "%rsp" + BitVec.ofInt 64 (-48)) (s.regs "%r15") := by
    rw [hs1]
    simp only [framePrologue, runBlockA_cons, runBlockA_nil, CallFrame.evalInstrA_storeMem]
    rfl
  have m2 : ∀ o : Int, -48 ≤ o → o ≤ -8 → o % 8 = 0 →
      read64 s2.mem (s.regs "%rsp" + BitVec.ofInt 64 o)
        = read64 s1.mem (s.regs "%rsp" + BitVec.ofInt 64 o) := fun o a1 a2 a3 =>
    read64_frameC hfr _ fun k hk => ho _ _ (by omega) (by omega) (by omega) a1 a2 a3
  have w : ∀ (m : AMem) (v : BitVec 64) (a b : Int), 8 ≤ (a - b).natAbs →
      (a - b).natAbs ≤ 2 ^ 64 - 8 →
      read64 (write64 m (s.regs "%rsp" + BitVec.ofInt 64 a) v)
          (s.regs "%rsp" + BitVec.ofInt 64 b)
        = read64 m (s.regs "%rsp" + BitVec.ofInt 64 b) :=
    fun m v a b h h' => read64_write64_of_disjoint _ _ _ _ (djSS _ _ _ h h')
  intro r hr
  simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [frameEpilogue, runBlockA_cons, runBlockA_nil,
      CallFrame.evalInstrA_loadMem, ite_true, ite_false] <;>
    rw [← hs2] at hsp <;>
    rw [hsp] <;>
    (first
      | rw [m2 (-8) (by omega) (by omega) (by omega)]
      | rw [m2 (-16) (by omega) (by omega) (by omega)]
      | rw [m2 (-24) (by omega) (by omega) (by omega)]
      | rw [m2 (-32) (by omega) (by omega) (by omega)]
      | rw [m2 (-40) (by omega) (by omega) (by omega)]
      | rw [m2 (-48) (by omega) (by omega) (by omega)]) <;>
    rw [m1] <;>
    repeat (first | rw [read64_write64_same] | (rw [w] <;> try decide))

/-- **A framed body on the address machine.** For a body meeting `CoreOK` and an output
    buffer outside the 48 bytes below `%rsp`: the four-limb value at `%rdi` is the one the
    body leaves after the prologue, no byte outside the output and those 48 bytes changes,
    and `%rsp` and the callee-saved registers end at their entry values. -/
theorem redFramed_spec {c : List (JInstr 64)} (hc : CoreOK c) (s : AState)
    (ho : RangeDisj (s.regs "%rdi") 0 24 (s.regs "%rsp") (-48) (-8)) :
    feO (runBlockA s (redFramed c)).mem (s.regs "%rdi") 0
        = feO (runBlockA (runBlockA s framePrologue) c).mem
            ((runBlockA s framePrologue).regs "%rdi") 0
      ∧ FrameCRed s.mem (runBlockA s (redFramed c)).mem (s.regs "%rdi") 4 (s.regs "%rsp") 6
      ∧ (runBlockA s (redFramed c)).regs "%rsp" = s.regs "%rsp"
      ∧ ∀ r ∈ calleeSavedRegs, (runBlockA s (redFramed c)).regs r = s.regs r := by
  refine ⟨?_, redFramed_frame hc s, redFramed_rsp hc s, redFramed_saved hc s ho⟩
  rw [redFramed_mem, framePrologue_regs]

/-! ## 5. The four byte-decoded leaves -/

theorem feMulFramed_eq : feMulFramed = redFramed (feMulPre ++ feMulPhys) := rfl
theorem feSqrFramed_eq : feSqrFramed = redFramed feSqrPhys := rfl
theorem feAddFramed_eq : feAddFramed = redFramed feAddPhys := rfl
theorem feSubFramed_eq : feSubFramed = redFramed feSubPhys := rfl

/-- **The byte-decoded `fe25519_mul` on the address machine.** `feMulFramed` is the block
    the shipped bytes `fe25519_mul_x86_from_lean` decode to (`feMulFramed_decode`). When the
    two argument buffers and the output buffer lie outside the 48 bytes below `%rsp`, it
    leaves the product of the four-limb values at `%rsi` and at `%rdx`, reduced modulo
    `2 ^ 255 - 19`, at `%rdi`, changes no byte outside the 32 bytes at `%rdi` and the 48
    bytes below `%rsp`, and ends with `%rsp` and the callee-saved registers at their entry
    values. The output buffer may coincide with an argument buffer. -/
theorem feMulFramed_correct_addr (sa : AState)
    (hi : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-48) (-8))
    (hj : RangeDisj (sa.regs "%rdx") 0 24 (sa.regs "%rsp") (-48) (-8))
    (ho : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-48) (-8)) :
    feO (runBlockA sa feMulFramed).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 * feO sa.mem (sa.regs "%rdx") 0 % pM
      ∧ FrameCRed sa.mem (runBlockA sa feMulFramed).mem (sa.regs "%rdi") 4 (sa.regs "%rsp") 6
      ∧ (runBlockA sa feMulFramed).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ calleeSavedRegs, (runBlockA sa feMulFramed).regs r = sa.regs r := by
  obtain ⟨hv, hf, hr, hs⟩ := redFramed_spec mulBody_ok sa ho
  refine ⟨?_, hf, hr, hs⟩
  rw [feMulFramed_eq, hv, mulBody_correct_addr, framePrologue_regs, framePrologue_regs,
    feO_prologue sa hi, feO_prologue sa hj]

/-- **The byte-decoded `fe25519_sqr` on the address machine.** `feSqrFramed` is the block
    the shipped bytes `fe25519_sqr_x86_from_lean` decode to (`feSqrFramed_decode`). When the
    argument buffer and the output buffer lie outside the 48 bytes below `%rsp`, it leaves
    the square of the four-limb value at `%rsi`, reduced modulo `2 ^ 255 - 19`, at `%rdi`,
    changes no byte outside the 32 bytes at `%rdi` and the 48 bytes below `%rsp`, and ends
    with `%rsp` and the callee-saved registers at their entry values. The output buffer
    may coincide with the argument buffer. -/
theorem feSqrFramed_correct_addr (sa : AState)
    (hi : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-48) (-8))
    (ho : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-48) (-8)) :
    feO (runBlockA sa feSqrFramed).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 ^ 2 % pM
      ∧ FrameCRed sa.mem (runBlockA sa feSqrFramed).mem (sa.regs "%rdi") 4 (sa.regs "%rsp") 6
      ∧ (runBlockA sa feSqrFramed).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ calleeSavedRegs, (runBlockA sa feSqrFramed).regs r = sa.regs r := by
  obtain ⟨hv, hf, hr, hs⟩ := redFramed_spec sqrBody_ok sa ho
  refine ⟨?_, hf, hr, hs⟩
  rw [feSqrFramed_eq, hv, sqrBody_correct_addr, framePrologue_regs, feO_prologue sa hi]

/-- **The byte-decoded `fe25519_add` on the address machine.** `feAddFramed` is the block
    the shipped bytes `fe25519_add_x86_from_lean` decode to (`feAddFramed_decode`). When the
    two argument buffers and the output buffer lie outside the 48 bytes below `%rsp`, and
    both arguments are below `2 ^ 255 - 19`, it leaves their sum modulo that prime at
    `%rdi`; it changes no byte outside the 32 bytes at `%rdi` and the 48 bytes below
    `%rsp`, and ends with `%rsp` and the callee-saved registers at their entry values. -/
theorem feAddFramed_correct_addr (sa : AState)
    (hi : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-48) (-8))
    (hj : RangeDisj (sa.regs "%rdx") 0 24 (sa.regs "%rsp") (-48) (-8))
    (ho : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-48) (-8)) :
    (feO sa.mem (sa.regs "%rsi") 0 < pM → feO sa.mem (sa.regs "%rdx") 0 < pM →
        feO (runBlockA sa feAddFramed).mem (sa.regs "%rdi") 0
          = (feO sa.mem (sa.regs "%rsi") 0 + feO sa.mem (sa.regs "%rdx") 0) % pM)
      ∧ FrameCRed sa.mem (runBlockA sa feAddFramed).mem (sa.regs "%rdi") 4 (sa.regs "%rsp") 6
      ∧ (runBlockA sa feAddFramed).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ calleeSavedRegs, (runBlockA sa feAddFramed).regs r = sa.regs r := by
  obtain ⟨hv, hf, hr, hs⟩ := redFramed_spec addBody_ok sa ho
  refine ⟨fun h1 h2 => ?_, hf, hr, hs⟩
  have e1 := feO_prologue sa hi
  have e2 := feO_prologue sa hj
  rw [feAddFramed_eq, hv, addBody_correct_addr _ (by rw [framePrologue_regs, e1]; exact h1)
    (by rw [framePrologue_regs, e2]; exact h2), framePrologue_regs, framePrologue_regs, e1, e2]

/-- **The byte-decoded `fe25519_sub` on the address machine.** `feSubFramed` is the block
    the shipped bytes `fe25519_sub_x86_from_lean` decode to (`feSubFramed_decode`). When the
    two argument buffers and the output buffer lie outside the 48 bytes below `%rsp`, and
    both arguments are below `2 ^ 255 - 19`, it leaves their difference modulo that prime at
    `%rdi`; it changes no byte outside the 32 bytes at `%rdi` and the 48 bytes below
    `%rsp`, and ends with `%rsp` and the callee-saved registers at their entry values. -/
theorem feSubFramed_correct_addr (sa : AState)
    (hi : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-48) (-8))
    (hj : RangeDisj (sa.regs "%rdx") 0 24 (sa.regs "%rsp") (-48) (-8))
    (ho : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-48) (-8)) :
    (feO sa.mem (sa.regs "%rsi") 0 < pM → feO sa.mem (sa.regs "%rdx") 0 < pM →
        feO (runBlockA sa feSubFramed).mem (sa.regs "%rdi") 0
          = (feO sa.mem (sa.regs "%rsi") 0 + (pM - feO sa.mem (sa.regs "%rdx") 0)) % pM)
      ∧ FrameCRed sa.mem (runBlockA sa feSubFramed).mem (sa.regs "%rdi") 4 (sa.regs "%rsp") 6
      ∧ (runBlockA sa feSubFramed).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ calleeSavedRegs, (runBlockA sa feSubFramed).regs r = sa.regs r := by
  obtain ⟨hv, hf, hr, hs⟩ := redFramed_spec subBody_ok sa ho
  refine ⟨fun h1 h2 => ?_, hf, hr, hs⟩
  have e1 := feO_prologue sa hi
  have e2 := feO_prologue sa hj
  rw [feSubFramed_eq, hv, subBody_correct_addr _ (by rw [framePrologue_regs, e1]; exact h1)
    (by rw [framePrologue_regs, e2]; exact h2), framePrologue_regs, framePrologue_regs, e1, e2]

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519BytesLeaves

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519BytesCalls

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFrame (framePrologue frameEpilogue)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.CallFrame
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519FramedCalls
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519BytesLeaves
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (calleeSavedRegs)

/-! ## 1. Calls of the byte-decoded leaves -/

/-- A call to a byte-decoded field leaf: the return address pushed, the block `blk`, and
    the return; the leaf pushes nothing and allocates no stack. -/
def bytesLeafCall (blk : List (JInstr 64)) (ra : BitVec 64) : AState → AState :=
  leafCall (framePro [] 0) blk (frameEpi [] 0) ra

/-- A call to the byte-decoded `fe25519_mul` (`feMulFramed`). -/
def mulCallB (ra : BitVec 64) : AState → AState := bytesLeafCall feMulFramed ra

/-- A call to the byte-decoded `fe25519_sqr` (`feSqrFramed`). -/
def sqrCallB (ra : BitVec 64) : AState → AState := bytesLeafCall feSqrFramed ra

/-- A call to the byte-decoded `fe25519_add` (`feAddFramed`). -/
def addCallB (ra : BitVec 64) : AState → AState := bytesLeafCall feAddFramed ra

/-- A call to the byte-decoded `fe25519_sub` (`feSubFramed`). -/
def subCallB (ra : BitVec 64) : AState → AState := bytesLeafCall feSubFramed ra

theorem entry_rsp (ra : BitVec 64) (sa : AState) :
    (entryState (framePro [] 0) ra sa).regs "%rsp" = sa.regs "%rsp" + BitVec.ofInt 64 (-8) := by
  rw [(entered [] 0 ra sa (by simp) (by simp)).rsp]; congr 2

theorem entry_regs (ra : BitVec 64) (sa : AState) (r : String) (hr : r ≠ "%rsp") :
    (entryState (framePro [] 0) ra sa).regs r = sa.regs r :=
  (entered [] 0 ra sa (by simp) (by simp)).regs r hr

/-- A buffer outside the eighteen words below the caller's `%rsp` lies outside the 48 bytes
    below the leaf's `%rsp`. -/
theorem entry_red (ra : BitVec 64) (sa : AState) {p : BitVec 64}
    (h : RangeDisj p 0 24 (sa.regs "%rsp") (-144) (-8)) :
    RangeDisj p 0 24 ((entryState (framePro [] 0) ra sa).regs "%rsp") (-48) (-8) := by
  rw [entry_rsp]
  exact rangeDisj_frame (-8) h fun o a1 a2 a3 => ⟨by omega, by omega, by omega⟩

/-- A four-limb value outside the eighteen words below the caller's `%rsp` reads at the
    leaf's entry as at the call. -/
theorem entry_feO (ra : BitVec 64) (sa : AState) {p : BitVec 64}
    (h : RangeDisj p 0 24 (sa.regs "%rsp") (-144) (-8)) :
    feO (entryState (framePro [] 0) ra sa).mem p 0 = feO sa.mem p 0 :=
  entered_feO (entered [] 0 ra sa (by simp) (by simp)) (by simp) h

/-- **A call to a red-zone framed body.** For a body meeting `CoreOK` and an output buffer
    outside the eighteen words below `%rsp`, the call leaves the memory the block leaves
    from the entry state, changes no byte outside the output and those eighteen words, and
    returns `%rsp` and the callee-saved registers at their values at the call. -/
theorem bytesLeafCall_spec {c : List (JInstr 64)} (hc : CoreOK c) (ra : BitVec 64)
    (sa : AState) (ho : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-144) (-8)) :
    (bytesLeafCall (redFramed c) ra sa).mem
        = (runBlockA (entryState (framePro [] 0) ra sa) (redFramed c)).mem
      ∧ FrameCS sa.mem (bytesLeafCall (redFramed c) ra sa).mem (sa.regs "%rdi") 4
          (sa.regs "%rsp")
      ∧ (bytesLeafCall (redFramed c) ra sa).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ calleeSavedRegs, (bytesLeafCall (redFramed c) ra sa).regs r = sa.regs r := by
  have ent := entered [] 0 ra sa (by simp) (by simp)
  have hoE : RangeDisj ((entryState (framePro [] 0) ra sa).regs "%rdi") 0 24
      ((entryState (framePro [] 0) ra sa).regs "%rsp") (-48) (-8) := by
    rw [entry_regs ra sa "%rdi" (by decide)]; exact entry_red ra sa ho
  obtain ⟨-, hf, hsp, hsaved⟩ := redFramed_spec hc _ hoE
  rw [entry_regs ra sa "%rdi" (by decide), entry_rsp] at hf
  have P := framedCall_popped [] 0 (fun s => runBlockA s (redFramed c))
    ra sa (by simp) (by simp) (by simp) hsp (fun k hk => absurd hk (by simp))
  unfold bytesLeafCall leafCall
  refine ⟨P.mem, fun x hx hy => ?_, P.rsp, fun r hr => ?_⟩
  · rw [P.mem, hf x hx fun i hi => ?_]
    · exact entered_mem_red ent (by decide) x hy
    · have h2 := hy (16 - i) (by omega)
      rw [redBase, addI, show (-144 : Int) + ((8 * (16 - i) : Nat) : Int)
        = -8 + (-(8 * (i + 1) : Nat) : Int) from by omega, ← addI] at h2
      exact h2
  · have hr0 : r ≠ "%rsp" := by
      simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [P.other r (by simp) hr0, hsaved r hr, ent.regs r hr0]

/-- **A call to the byte-decoded `fe25519_mul`** (`feMulFramed`, the block the shipped
    bytes `fe25519_mul_x86_from_lean` decode to). When its arguments and output lie outside
    the eighteen words below `%rsp`, the call leaves the product of the arguments modulo
    `2 ^ 255 - 19` at the output, changes no byte outside the output and those words, and
    returns `%rsp` and the callee-saved registers at their values at the call. An argument
    may coincide with the output. -/
theorem mulCallB_spec (ra : BitVec 64) (sa : AState) (h : CallSep sa) :
    feO (mulCallB ra sa).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 * feO sa.mem (sa.regs "%rdx") 0 % pM
      ∧ FrameCS sa.mem (mulCallB ra sa).mem (sa.regs "%rdi") 4 (sa.regs "%rsp")
      ∧ (mulCallB ra sa).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ calleeSavedRegs, (mulCallB ra sa).regs r = sa.regs r := by
  obtain ⟨hm, hF, hr, hs⟩ := bytesLeafCall_spec mulBody_ok ra sa h.os
  have hv := (feMulFramed_correct_addr (entryState (framePro [] 0) ra sa)
    (by rw [entry_regs ra sa "%rsi" (by decide)]; exact entry_red ra sa h.is)
    (by rw [entry_regs ra sa "%rdx" (by decide)]; exact entry_red ra sa h.js)
    (by rw [entry_regs ra sa "%rdi" (by decide)]; exact entry_red ra sa h.os)).1
  rw [entry_regs ra sa "%rdi" (by decide), entry_regs ra sa "%rsi" (by decide),
    entry_regs ra sa "%rdx" (by decide), entry_feO ra sa h.is, entry_feO ra sa h.js] at hv
  exact ⟨by rw [mulCallB, feMulFramed_eq, hm]; exact hv, hF, hr, hs⟩

/-- **A call to the byte-decoded `fe25519_sqr`** (`feSqrFramed`, the block the shipped
    bytes `fe25519_sqr_x86_from_lean` decode to). When its argument and output lie outside
    the eighteen words below `%rsp`, the call leaves the square of the argument modulo
    `2 ^ 255 - 19` at the output, changes no byte outside the output and those words, and
    returns `%rsp` and the callee-saved registers at their values at the call. The argument
    may coincide with the output. -/
theorem sqrCallB_spec (ra : BitVec 64) (sa : AState) (h : SqrSep sa) :
    feO (sqrCallB ra sa).mem (sa.regs "%rdi") 0 = feO sa.mem (sa.regs "%rsi") 0 ^ 2 % pM
      ∧ FrameCS sa.mem (sqrCallB ra sa).mem (sa.regs "%rdi") 4 (sa.regs "%rsp")
      ∧ (sqrCallB ra sa).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ calleeSavedRegs, (sqrCallB ra sa).regs r = sa.regs r := by
  obtain ⟨hm, hF, hr, hs⟩ := bytesLeafCall_spec sqrBody_ok ra sa h.os
  have hv := (feSqrFramed_correct_addr (entryState (framePro [] 0) ra sa)
    (by rw [entry_regs ra sa "%rsi" (by decide)]; exact entry_red ra sa h.is)
    (by rw [entry_regs ra sa "%rdi" (by decide)]; exact entry_red ra sa h.os)).1
  rw [entry_regs ra sa "%rdi" (by decide), entry_regs ra sa "%rsi" (by decide),
    entry_feO ra sa h.is] at hv
  exact ⟨by rw [sqrCallB, feSqrFramed_eq, hm]; exact hv, hF, hr, hs⟩

/-- **A call to the byte-decoded `fe25519_add`** (`feAddFramed`, the block the shipped
    bytes `fe25519_add_x86_from_lean` decode to). When its arguments and output lie outside
    the eighteen words below `%rsp` and both arguments are below `2 ^ 255 - 19`, the call
    leaves their sum modulo that prime at the output; it changes no byte outside the output
    and those words, and returns `%rsp` and the callee-saved registers at their values at
    the call. -/
theorem addCallB_spec (ra : BitVec 64) (sa : AState) (h : CallSep sa) :
    (feO sa.mem (sa.regs "%rsi") 0 < pM → feO sa.mem (sa.regs "%rdx") 0 < pM →
        feO (addCallB ra sa).mem (sa.regs "%rdi") 0
          = (feO sa.mem (sa.regs "%rsi") 0 + feO sa.mem (sa.regs "%rdx") 0) % pM)
      ∧ FrameCS sa.mem (addCallB ra sa).mem (sa.regs "%rdi") 4 (sa.regs "%rsp")
      ∧ (addCallB ra sa).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ calleeSavedRegs, (addCallB ra sa).regs r = sa.regs r := by
  obtain ⟨hm, hF, hr, hs⟩ := bytesLeafCall_spec addBody_ok ra sa h.os
  have hv := (feAddFramed_correct_addr (entryState (framePro [] 0) ra sa)
    (by rw [entry_regs ra sa "%rsi" (by decide)]; exact entry_red ra sa h.is)
    (by rw [entry_regs ra sa "%rdx" (by decide)]; exact entry_red ra sa h.js)
    (by rw [entry_regs ra sa "%rdi" (by decide)]; exact entry_red ra sa h.os)).1
  rw [entry_regs ra sa "%rdi" (by decide), entry_regs ra sa "%rsi" (by decide),
    entry_regs ra sa "%rdx" (by decide), entry_feO ra sa h.is, entry_feO ra sa h.js] at hv
  exact ⟨fun h1 h2 => by rw [addCallB, feAddFramed_eq, hm]; exact hv h1 h2, hF, hr, hs⟩

/-- **A call to the byte-decoded `fe25519_sub`** (`feSubFramed`, the block the shipped
    bytes `fe25519_sub_x86_from_lean` decode to). When its arguments and output lie outside
    the eighteen words below `%rsp` and both arguments are below `2 ^ 255 - 19`, the call
    leaves their difference modulo that prime at the output; it changes no byte outside the
    output and those words, and returns `%rsp` and the callee-saved registers at their
    values at the call. -/
theorem subCallB_spec (ra : BitVec 64) (sa : AState) (h : CallSep sa) :
    (feO sa.mem (sa.regs "%rsi") 0 < pM → feO sa.mem (sa.regs "%rdx") 0 < pM →
        feO (subCallB ra sa).mem (sa.regs "%rdi") 0
          = (feO sa.mem (sa.regs "%rsi") 0 + (pM - feO sa.mem (sa.regs "%rdx") 0)) % pM)
      ∧ FrameCS sa.mem (subCallB ra sa).mem (sa.regs "%rdi") 4 (sa.regs "%rsp")
      ∧ (subCallB ra sa).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ calleeSavedRegs, (subCallB ra sa).regs r = sa.regs r := by
  obtain ⟨hm, hF, hr, hs⟩ := bytesLeafCall_spec subBody_ok ra sa h.os
  have hv := (feSubFramed_correct_addr (entryState (framePro [] 0) ra sa)
    (by rw [entry_regs ra sa "%rsi" (by decide)]; exact entry_red ra sa h.is)
    (by rw [entry_regs ra sa "%rdx" (by decide)]; exact entry_red ra sa h.js)
    (by rw [entry_regs ra sa "%rdi" (by decide)]; exact entry_red ra sa h.os)).1
  rw [entry_regs ra sa "%rdi" (by decide), entry_regs ra sa "%rsi" (by decide),
    entry_regs ra sa "%rdx" (by decide), entry_feO ra sa h.is, entry_feO ra sa h.js] at hv
  exact ⟨fun h1 h2 => by rw [subCallB, feSubFramed_eq, hm]; exact hv h1 h2, hF, hr, hs⟩

/-! ## 2. The mixed addition over the byte-decoded leaves -/

open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519MaddShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT
  (mulSym addSym subSym join16Sym)

/-- The call model of the shipped mixed addition over the byte-decoded field leaves: each
    of `fe25519_add`, `fe25519_sub` and `fe25519_mul` runs the block its shipped bytes
    decode to after the return address `ra` is pushed, and returns; `ed25519_join16` runs
    its shipped prologue, block and epilogue (`Ed25519FramedCalls.joinCall`). -/
def maddCallModelB (ra : BitVec 64) : ACallModel := fun f sa =>
  if f = addSym then addCallB ra sa
  else if f = subSym then subCallB ra sa
  else if f = mulSym then mulCallB ra sa
  else if f = join16Sym then joinCall ra sa
  else sa

theorem maddCallModelB_addSym (ra : BitVec 64) (sa : AState) :
    maddCallModelB ra addSym sa = addCallB ra sa := by simp [maddCallModelB]

theorem maddCallModelB_subSym (ra : BitVec 64) (sa : AState) :
    maddCallModelB ra subSym sa = subCallB ra sa := by
  simp [maddCallModelB, addSym, subSym]

theorem maddCallModelB_mulSym (ra : BitVec 64) (sa : AState) :
    maddCallModelB ra mulSym sa = mulCallB ra sa := by
  simp [maddCallModelB, addSym, subSym, mulSym]

theorem maddCallModelB_joinSym (ra : BitVec 64) (sa : AState) :
    maddCallModelB ra join16Sym sa = joinCall ra sa := by
  simp [maddCallModelB, addSym, subSym, mulSym, join16Sym]

/-- **The byte-decoded field leaves and the framed concatenation meet the callee
    specifications of the mixed addition.** -/
theorem maddCalleesF_maddCallModelB (ra : BitVec 64) : MaddCalleesF (maddCallModelB ra) := by
  refine ⟨fun sa h => ?_, fun sa h => ?_, fun sa h => ?_, fun sa h => ?_⟩
  · obtain ⟨hv, hf, hr, -⟩ := addCallB_spec ra sa h
    unfold FieldEffect
    rw [maddCallModelB_addSym]
    exact ⟨hv, hf, hr⟩
  · obtain ⟨hv, hf, hr, -⟩ := subCallB_spec ra sa h
    unfold FieldEffect
    rw [maddCallModelB_subSym]
    exact ⟨hv, hf, hr⟩
  · obtain ⟨hv, hf, hr, -⟩ := mulCallB_spec ra sa ⟨h.is, h.js, h.os⟩
    unfold FieldEffect
    rw [maddCallModelB_mulSym]
    exact ⟨fun _ _ => hv, hf, hr⟩
  · obtain ⟨hv, hf, hr⟩ := joinCall_spec ra sa h
    unfold JoinEffect
    rw [maddCallModelB_joinSym]
    exact ⟨hv, hf, hr⟩

/-- **The shipped `ed25519_madd` over the byte-decoded field leaves, output aliasing
    allowed.** Each of `fe25519_add`, `fe25519_sub` and `fe25519_mul` runs
    `feAddFramed`, `feSubFramed`, `feMulFramed`, the blocks the crate's shipped bytes
    decode to; `ed25519_join16` runs its shipped prologue, block and epilogue. For a state
    whose stack words are disjoint from the input point (`CrossIn`) and from the output
    words (`CrossOut`) and whose seven input coordinates are below `2 ^ 255 - 19`, the four
    field elements at the output pointer are the four coordinates of `maddSpecN`. -/
theorem maddShippedBytes_correct_cross (ra : BitVec 64) (sa : AState)
    (hX : CrossIn (sa.regs "%rsp") (sa.regs "%rsi"))
    (hO : CrossOut (sa.regs "%rsp") (sa.regs "%rdi"))
    (hb : ∀ j, j < 7 → maddIn sa j < pM) :
    feO (segsRunA (maddCallModelB ra) sa ed25519MaddShippedBlock).mem (sa.regs "%rdi")
        (slotOff 0)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).1
      ∧ feO (segsRunA (maddCallModelB ra) sa ed25519MaddShippedBlock).mem (sa.regs "%rdi")
          (slotOff 1)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.1
      ∧ feO (segsRunA (maddCallModelB ra) sa ed25519MaddShippedBlock).mem (sa.regs "%rdi")
          (slotOff 2)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.1
      ∧ feO (segsRunA (maddCallModelB ra) sa ed25519MaddShippedBlock).mem (sa.regs "%rdi")
          (slotOff 3)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.2 :=
  maddOut_of_calls sa hO (maddCallsRunF (maddCalleesF_maddCallModelB ra) sa hX hb)

/-- **The shipped `ed25519_madd` over the byte-decoded field leaves.** Each of
    `fe25519_add`, `fe25519_sub` and `fe25519_mul` runs `feAddFramed`, `feSubFramed`,
    `feMulFramed`, the blocks the crate's shipped bytes decode to; `ed25519_join16` runs its
    shipped prologue, block and epilogue. For pairwise separated cells and input
    coordinates below `2 ^ 255 - 19`, the four field elements at the output pointer are the
    four coordinates of `maddSpecN`. -/
theorem maddShippedBytes_correct (ra : BitVec 64) (sa : AState)
    (hsep : Separated shippedBank sa.regs maddCells)
    (hb : ∀ j, j < 7 → maddIn sa j < pM) :
    feO (segsRunA (maddCallModelB ra) sa ed25519MaddShippedBlock).mem (sa.regs "%rdi")
        (slotOff 0)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).1
      ∧ feO (segsRunA (maddCallModelB ra) sa ed25519MaddShippedBlock).mem (sa.regs "%rdi")
          (slotOff 1)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.1
      ∧ feO (segsRunA (maddCallModelB ra) sa ed25519MaddShippedBlock).mem (sa.regs "%rdi")
          (slotOff 2)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.1
      ∧ feO (segsRunA (maddCallModelB ra) sa ed25519MaddShippedBlock).mem (sa.regs "%rdi")
          (slotOff 3)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.2 :=
  maddShippedF_correct_addr (maddCalleesF_maddCallModelB ra) sa hsep hb

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519BytesCalls

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519BytesCalls

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.CallFrame
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519FramedCalls
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT (mulSym sqrSym)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (calleeSavedRegs)

/-! ## 3. The inversion over the byte-decoded leaves -/

/-- The call model of the shipped inversion over the byte-decoded field leaves:
    `fe25519_sqr` and `fe25519_mul` run the blocks their shipped bytes decode to
    (`feSqrFramed`, `feMulFramed`) after the return address `ra` is pushed, and return. -/
def invertCallModelB (ra : BitVec 64) : ACallModel := fun f sa =>
  if f = sqrSym then sqrCallB ra sa
  else if f = mulSym then mulCallB ra sa
  else sa

theorem invertCallModelB_sqrSym (ra : BitVec 64) (sa : AState) :
    invertCallModelB ra sqrSym sa = sqrCallB ra sa := by simp [invertCallModelB]

theorem invertCallModelB_mulSym (ra : BitVec 64) (sa : AState) :
    invertCallModelB ra mulSym sa = mulCallB ra sa := by
  simp [invertCallModelB, sqrSym, mulSym]

open Classical in
/-- The model that is `invertCallModelB ra` at every square call satisfying `SqrSep` and
    every multiply call satisfying `CallSep`, and `Ed25519InvertShippedProof.invertCallModel`
    at every other call. It meets `InvertCallees`, and on the inversion block, whose calls
    all satisfy those conditions, it runs as `invertCallModelB ra`. -/
noncomputable def invertCallModelPB (ra : BitVec 64) : ACallModel := fun f sa =>
  if f = sqrSym then (if SqrSep sa then sqrCallB ra sa else invertCallModel sqrSym sa)
  else if f = mulSym then (if CallSep sa then mulCallB ra sa else invertCallModel mulSym sa)
  else sa

theorem invertCallModelPB_sqr {ra : BitVec 64} {sa : AState} (h : SqrSep sa) :
    invertCallModelPB ra sqrSym sa = invertCallModelB ra sqrSym sa := by
  simp [invertCallModelPB, invertCallModelB, h]

theorem invertCallModelPB_mul {ra : BitVec 64} {sa : AState} (h : CallSep sa) :
    invertCallModelPB ra mulSym sa = invertCallModelB ra mulSym sa := by
  simp [invertCallModelPB, invertCallModelB, h, sqrSym, mulSym]

theorem invertCallees_invertCallModelPB (ra : BitVec 64) :
    InvertCallees (invertCallModelPB ra) := by
  refine ⟨fun sa => ?_, fun sa hsp => ?_⟩
  · unfold SqrEffect
    by_cases h : SqrSep sa
    · rw [invertCallModelPB_sqr h, invertCallModelB_sqrSym]
      obtain ⟨hv, hf, hr, hs⟩ := sqrCallB_spec ra sa h
      exact ⟨hv, hf, hr, hs "%rbx" (by decide)⟩
    · have e : invertCallModelPB ra sqrSym sa = invertCallModel sqrSym sa := by
        simp [invertCallModelPB, h]
      rw [e]
      exact invertCallModel_sqr sa
  · unfold MulEffect
    by_cases h : CallSep sa
    · rw [invertCallModelPB_mul h, invertCallModelB_mulSym]
      obtain ⟨hv, hf, hr, hs⟩ := mulCallB_spec ra sa h
      exact ⟨hv, hf, hr, hs "%rbx" (by decide)⟩
    · have e : invertCallModelPB ra mulSym sa = invertCallModel mulSym sa := by
        simp [invertCallModelPB, h, sqrSym, mulSym]
      rw [e]
      exact invertCallModel_mul sa hsp

/-- A byte-decoded square call at a state satisfying `SqrSep` keeps the registers of
    `keptRegs`. -/
theorem sqrCallB_kept (ra : BitVec 64) (sa : AState) (h : SqrSep sa) (r : String)
    (hr : r ∈ keptRegs) : (invertCallModelB ra sqrSym sa).regs r = sa.regs r := by
  obtain ⟨-, -, hsp, hs⟩ := sqrCallB_spec ra sa h
  rw [invertCallModelB_sqrSym]
  by_cases h0 : r = "%rsp"
  · subst h0; exact hsp
  · exact hs r (keptRegs_calleeSaved r hr h0)

/-- A byte-decoded multiply call at a state satisfying `CallSep` keeps the registers of
    `keptRegs`. -/
theorem mulCallB_kept (ra : BitVec 64) (sa : AState) (h : CallSep sa) (r : String)
    (hr : r ∈ keptRegs) : (invertCallModelB ra mulSym sa).regs r = sa.regs r := by
  obtain ⟨-, -, hsp, hs⟩ := mulCallB_spec ra sa h
  rw [invertCallModelB_mulSym]
  by_cases h0 : r = "%rsp"
  · subst h0; exact hsp
  · exact hs r (keptRegs_calleeSaved r hr h0)

/-- One step of the chain runs as under `invertCallModelPB ra` and keeps the registers of
    `keptRegs`. -/
theorem stepB {ra : BitVec 64} {SP IP OP : BitVec 64} {z : Nat} {E : Env} {sa : AState}
    (hsep : ChainSep SP IP) (hinv : ChainInv SP IP OP z E sa) (s : Step) :
    segsRunA (invertCallModelPB ra) sa [segOfStep s]
        = segsRunA (invertCallModelB ra) sa [segOfStep s]
      ∧ ∀ r ∈ keptRegs, (segsRunA (invertCallModelB ra) sa [segOfStep s]).regs r
          = sa.regs r := by
  have hS := stepSep hsep hinv s
  cases s with
  | sqr d a =>
    refine ⟨invertCallModelPB_sqr hS, fun r hr => ?_⟩
    show (invertCallModelB ra sqrSym (runBlockA sa (segOfStep (.sqr d a)).body)).regs r = _
    rw [sqrCallB_kept ra _ hS r hr, segBody_kept _ _ r hr]
  | mul d a b =>
    refine ⟨invertCallModelPB_mul hS, fun r hr => ?_⟩
    show (invertCallModelB ra mulSym (runBlockA sa (segOfStep (.mul d a b)).body)).regs r = _
    rw [mulCallB_kept ra _ hS r hr, segBody_kept _ _ r hr]

/-- The chain over a list of steps runs as under `invertCallModelPB ra` and keeps the
    registers of `keptRegs`. -/
theorem chainRunB (ra : BitVec 64) {SP IP OP : BitVec 64} {z : Nat} (hz : z < pM)
    (hsep : ChainSep SP IP) :
    ∀ (steps : List Step) (E : Env) (sa : AState), ChainInv SP IP OP z E sa →
      segsRunA (invertCallModelPB ra) sa (steps.map segOfStep)
          = segsRunA (invertCallModelB ra) sa (steps.map segOfStep)
        ∧ ∀ r ∈ keptRegs,
          (segsRunA (invertCallModelB ra) sa (steps.map segOfStep)).regs r = sa.regs r := by
  intro steps
  induction steps with
  | nil => intro E sa _; exact ⟨rfl, fun _ _ => rfl⟩
  | cons s rest ih =>
    intro E sa h
    have e : ∀ C : ACallModel, segsRunA C sa ((s :: rest).map segOfStep)
        = segsRunA C (segsRunA C sa [segOfStep s]) (rest.map segOfStep) := fun C => by
      rw [List.map_cons, show (segOfStep s :: rest.map segOfStep)
        = [segOfStep s] ++ rest.map segOfStep from rfl, segsRunA_append]
    obtain ⟨e1, k1⟩ := stepB (ra := ra) hsep h s
    have h1 := chainStep (invertCallees_invertCallModelPB ra) hz hsep h s
    obtain ⟨e2, k2⟩ := ih _ _ h1
    rw [e, e, e2, e1]
    refine ⟨rfl, fun r hr => ?_⟩
    rw [← e1, k2 r hr, e1, k1 r hr]

/-- **The inversion block under the byte-decoded model.** For a state whose input buffer is
    disjoint from the inversion frame, whose input is below `2 ^ 255 - 19`, and whose output
    buffer lies outside the eighteen words below `%rsp`, the block runs as under
    `invertCallModelPB ra` and keeps the registers of `keptRegs`. -/
theorem invertB_run (ra : BitVec 64) (sa : AState)
    (hsep : ChainSep (sa.regs "%rsp") (sa.regs "%rsi"))
    (hz : feO sa.mem (sa.regs "%rsi") 0 < pM)
    (ho : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-144) (-8)) :
    segsRunA (invertCallModelPB ra) sa Ed25519InvertShipped.ed25519InvertShippedBlock
        = segsRunA (invertCallModelB ra) sa Ed25519InvertShipped.ed25519InvertShippedBlock
      ∧ ∀ r ∈ keptRegs, (segsRunA (invertCallModelB ra) sa
          Ed25519InvertShipped.ed25519InvertShippedBlock).regs r = sa.regs r := by
  simp only [invertBlock_eq, segsRunA_append, segsRunA_clear]
  -- the first segment
  obtain ⟨-, hrsp, -, hrdi, hrsi⟩ := runEntryBody sa
  have hS1 : SqrSep (runBlockA sa
      [.mov "%rbx" (.reg "%rsi"), .storeMem "%rsp" 128 (.reg "%rdi"),
       .lea "%rdi" "%rsp" "%rsp" 0 0, .mov "%rsi" (.reg "%rbx")]) :=
    ⟨by rw [hrsi, hrsp]; exact srcBelowSep hsep .inp,
      by rw [hrdi, hrsp]; exact srcBelowSep hsep (.buf .b0)⟩
  have eS : ∀ C : ACallModel, segsRunA C sa Ed25519InvertShipped.ed25519InvertShippedSeg001
      = C sqrSym (runBlockA sa
        [.mov "%rbx" (.reg "%rsi"), .storeMem "%rsp" 128 (.reg "%rdi"),
         .lea "%rdi" "%rsp" "%rsp" 0 0, .mov "%rsi" (.reg "%rbx")]) := fun C => rfl
  have e1 : segsRunA (invertCallModelPB ra) sa Ed25519InvertShipped.ed25519InvertShippedSeg001
      = segsRunA (invertCallModelB ra) sa Ed25519InvertShipped.ed25519InvertShippedSeg001 := by
    rw [eS, eS]; exact invertCallModelPB_sqr hS1
  have k1 : ∀ r ∈ keptRegs, (segsRunA (invertCallModelB ra) sa
      Ed25519InvertShipped.ed25519InvertShippedSeg001).regs r = sa.regs r := by
    intro r hr
    rw [eS, sqrCallB_kept ra _ hS1 r hr]
    refine runBlockA_regs_of_all _ _ _ ?_
    simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dsts]
  have i1 := invertEntry (invertCallees_invertCallModelPB ra) sa hsep
  -- the chain
  obtain ⟨e2, k2⟩ := chainRunB ra hz hsep invertSteps invertEnv1 _ i1
  have i2 := chainRun (invertCallees_invertCallModelPB ra) hz hsep invertSteps invertEnv1 _ i1
  rw [invertEnv_final] at i2
  obtain ⟨s2, hs2⟩ : ∃ s, segsRunA (invertCallModelPB ra)
      (segsRunA (invertCallModelPB ra) sa Ed25519InvertShipped.ed25519InvertShippedSeg001)
      (invertSteps.map segOfStep) = s := ⟨_, rfl⟩
  have i2' : ChainInv _ _ _ _ _ s2 := hs2 ▸ i2
  -- the last segment
  obtain ⟨-, hrsp3, hrdi3, hrsi3, hrdx3⟩ := runExitBody s2
  rw [i2'.rsp] at hrsp3 hrdi3 hrsi3 hrdx3
  rw [i2'.outp] at hrdi3
  have hS3 : CallSep (runBlockA s2 [.loadMem "%rdi" "%rsp" 128,
      .lea "%rsi" "%rsp" "%rsp" 0 32, .lea "%rdx" "%rsp" "%rsp" 0 0]) :=
    ⟨by rw [hrsi3, hrsp3]; exact srcBelowSep hsep (.buf .b1),
      by rw [hrdx3, hrsp3]; exact srcBelowSep hsep (.buf .b0),
      by rw [hrdi3, hrsp3]; exact ho⟩
  have e3 : segsRunA (invertCallModelPB ra) s2 Ed25519InvertShipped.ed25519InvertShippedSeg265
      = segsRunA (invertCallModelB ra) s2 Ed25519InvertShipped.ed25519InvertShippedSeg265 := by
    rw [segsRunA_exit, segsRunA_exit]
    exact invertCallModelPB_mul hS3
  have k3 : ∀ r ∈ keptRegs, (segsRunA (invertCallModelB ra) s2
      Ed25519InvertShipped.ed25519InvertShippedSeg265).regs r = s2.regs r := by
    intro r hr
    rw [segsRunA_exit, mulCallB_kept ra _ hS3 r hr]
    refine runBlockA_regs_of_all _ _ _ ?_
    simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dsts]
  have e21 : segsRunA (invertCallModelB ra)
      (segsRunA (invertCallModelB ra) sa Ed25519InvertShipped.ed25519InvertShippedSeg001)
      (invertSteps.map segOfStep) = s2 :=
    (congrArg (fun x => segsRunA (invertCallModelB ra) x (invertSteps.map segOfStep))
      e1).symm.trans (e2.symm.trans hs2)
  refine ⟨congrArg (fun x => runBlockA x [.storeMem "%rsp" 128 (.imm 0)]) ?_, fun r hr => ?_⟩
  · exact (congrArg (fun x => segsRunA (invertCallModelPB ra) x
      Ed25519InvertShipped.ed25519InvertShippedSeg265) hs2).trans
      (e3.trans (congrArg (fun x => segsRunA (invertCallModelB ra) x
        Ed25519InvertShipped.ed25519InvertShippedSeg265) e21.symm))
  · refine (runBlockA_regs_of_all _ _ _ (by simp [dsts])).trans ?_
    refine (congrArg (fun x => (segsRunA (invertCallModelB ra) x
      Ed25519InvertShipped.ed25519InvertShippedSeg265).regs r) e21).trans ?_
    refine (k3 r hr).trans ?_
    refine (congrArg (fun x => x.regs r) (hs2.symm.trans e2)).trans ?_
    refine (k2 r hr).trans ?_
    exact (congrArg (fun x => x.regs r) e1).trans (k1 r hr)

/-- **The shipped `ed25519_invert` over the byte-decoded field leaves.** Each call to
    `fe25519_sqr` and `fe25519_mul` runs `feSqrFramed`, resp. `feMulFramed`, the blocks the
    crate's shipped bytes decode to, after the return address `ra` is pushed. For a state
    whose input buffer is disjoint from the inversion frame, whose input is below
    `2 ^ 255 - 19` and whose output buffer lies outside the eighteen words below `%rsp` and
    the word at `128(%rsp)`, the four-limb value at the output pointer after the block is
    the input raised to
    `2 ^ 255 - 21` modulo `2 ^ 255 - 19`; the block changes no byte outside the inversion
    frame and the output, and keeps `%rsp`, `%rbp` and `%r12` to `%r15`. -/
theorem invertShippedBytes_correct (ra : BitVec 64) (sa : AState)
    (hsep : ChainSep (sa.regs "%rsp") (sa.regs "%rsi"))
    (hz : feO sa.mem (sa.regs "%rsi") 0 < pM)
    (ho : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-144) (-8))
    (hout : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") 128 128) :
    feO (segsRunA (invertCallModelB ra) sa
        Ed25519InvertShipped.ed25519InvertShippedBlock).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 ^ (pM - 2) % pM
      ∧ InvertFrame sa.mem (segsRunA (invertCallModelB ra) sa
          Ed25519InvertShipped.ed25519InvertShippedBlock).mem (sa.regs "%rsp") (sa.regs "%rdi")
      ∧ ∀ r ∈ keptRegs, (segsRunA (invertCallModelB ra) sa
          Ed25519InvertShipped.ed25519InvertShippedBlock).regs r = sa.regs r := by
  obtain ⟨e, k⟩ := invertB_run ra sa hsep hz ho
  rw [← e]
  exact ⟨invertShipped_correct_addr (invertCallees_invertCallModelPB ra) sa hsep hz hout,
    invertShipped_frame (invertCallees_invertCallModelPB ra) sa hsep hz, by rw [e]; exact k⟩

/-! ## 4. The compression over the byte-decoded leaves -/

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519CompressShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT (invertSym packSignSym)

/-- A call to the shipped `ed25519_invert`: its prologue, its block over the byte-decoded
    model `invertCallModelB ra` of its own callees, and its epilogue. -/
def invertCallB (ra : BitVec 64) : AState → AState :=
  framedCall Ed25519InvertShipped.ed25519InvertShippedPrologue
    Ed25519InvertShipped.ed25519InvertShippedEpilogue
    (fun s => segsRunA (invertCallModelB ra) s Ed25519InvertShipped.ed25519InvertShippedBlock)
    ra

/-- **A call to the shipped `ed25519_invert` over the byte-decoded field leaves.** For an
    input below `2 ^ 255 - 19` and buffers satisfying `InvSep`, the call leaves the input
    raised to `2 ^ 255 - 21` modulo `2 ^ 255 - 19` at the output, changes no byte outside
    the forty-two words below `%rsp` and the output, and returns `%rsp`, `%rbx` and `%r12`
    at their values at the call. -/
theorem invertCallB_spec (ra : BitVec 64) (sa : AState) (h : InvSep sa)
    (hz : feO sa.mem (sa.regs "%rsi") 0 < pM) :
    feO (invertCallB ra sa).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 ^ (pM - 2) % pM
      ∧ InvertFrameF sa.mem (invertCallB ra sa).mem (sa.regs "%rsp") (sa.regs "%rdi")
      ∧ (invertCallB ra sa).regs "%rsp" = sa.regs "%rsp"
      ∧ (invertCallB ra sa).regs "%rbx" = sa.regs "%rbx"
      ∧ (invertCallB ra sa).regs "%r12" = sa.regs "%r12" := by
  have ent := entered ["%rbx"] 176 ra sa (by decide) (by simp)
  have hEsp : (entryState (framePro ["%rbx"] 176) ra sa).regs "%rsp"
      = sa.regs "%rsp" + BitVec.ofInt 64 (-192) := by
    rw [ent.rsp]; congr 2
  have er : ∀ r : String, r ≠ "%rsp" →
      (entryState (framePro ["%rbx"] 176) ra sa).regs r = sa.regs r := ent.regs
  have hin : feO (entryState (framePro ["%rbx"] 176) ra sa).mem (sa.regs "%rsi") 0
      = feO sa.mem (sa.regs "%rsi") 0 := by
    simp only [feO]
    refine congrArg _ (List.map_congr_left fun j hj => ent.read64_eq _ fun k hk => ?_)
    simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
    simp only [List.length_cons, List.length_nil] at hk
    exact (h.is (0 + j) (-(8 * ((k : Int) + 1)))
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega) (by omega) (by omega)
      (by omega)).symm
  have hsepE : ChainSep ((entryState (framePro ["%rbx"] 176) ra sa).regs "%rsp")
      ((entryState (framePro ["%rbx"] 176) ra sa).regs "%rsi") := by
    rw [hEsp, er _ (by decide)]; exact h.chain
  have hzE : feO (entryState (framePro ["%rbx"] 176) ra sa).mem
      ((entryState (framePro ["%rbx"] 176) ra sa).regs "%rsi") 0 < pM := by
    rw [er _ (by decide), hin]; exact hz
  have hoE : RangeDisj ((entryState (framePro ["%rbx"] 176) ra sa).regs "%rdi") 0 24
      ((entryState (framePro ["%rbx"] 176) ra sa).regs "%rsp") (-144) (-8) := by
    rw [hEsp, er _ (by decide)]
    exact rangeDisj_shift (-192) (by decide)
      (rangeDisj_narrow h.os (le_refl _) (le_refl _) (by omega) (by omega))
  have hqE : RangeDisj ((entryState (framePro ["%rbx"] 176) ra sa).regs "%rdi") 0 24
      ((entryState (framePro ["%rbx"] 176) ra sa).regs "%rsp") 128 128 := by
    rw [hEsp, er _ (by decide)]
    exact rangeDisj_shift (-192) (by decide)
      (rangeDisj_narrow h.os (le_refl _) (le_refl _) (by omega) (by omega))
  obtain ⟨hv, hf, hk⟩ := invertShippedBytes_correct ra _ hsepE hzE hoE hqE
  rw [er "%rdi" (by decide), er "%rsi" (by decide), hin] at hv
  rw [er "%rdi" (by decide), hEsp] at hf
  have hs : ∀ k, k < ["%rbx"].length →
      read64 (segsRunA (invertCallModelB ra) (entryState (framePro ["%rbx"] 176) ra sa)
          Ed25519InvertShipped.ed25519InvertShippedBlock).mem
          (slotAddr (sa.regs "%rsp") (k + 1))
        = read64 (entryState (framePro ["%rbx"] 176) ra sa).mem
          (slotAddr (sa.regs "%rsp") (k + 1)) := by
    intro k hk
    obtain rfl : k = 0 := by simp at hk; omega
    refine read64_invertFrame hf _ (fun j hj => ?_) (fun j hj => ?_)
    · rw [redBase, addI, addI, slotAddr]
      exact djSS _ _ _ (by omega) (by omega)
    · rw [slotAddr]
      exact h.os _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have P := framedCall_popped ["%rbx"] 176
    (fun s => segsRunA (invertCallModelB ra) s Ed25519InvertShipped.ed25519InvertShippedBlock)
    ra sa (by decide) (by simp) (by simp) (hk "%rsp" (by decide)) hs
  rw [invertCallB, invertFrame.1, invertFrame.2]
  refine ⟨by rw [P.mem]; exact hv, fun x hx hy => ?_, P.rsp, P.saved "%rbx" (by simp), ?_⟩
  · rw [P.mem, hf x (fun k hk => ?_) hy]
    · refine ent.mem x fun k hk => ?_
      simp only [List.length_cons, List.length_nil] at hk
      have h2 := hx (41 - k) (by omega)
      rwa [slotAddr, show -(8 * ((k : Int) + 1)) = (-336 : Int) + ((8 * (41 - k) : Nat) : Int)
        from by omega]
    · rw [redBase, addI, addI]
      have h2 := hx k (by omega)
      rwa [show (-192 : Int) + (-144 + ((8 * k : Nat) : Int)) = -336 + ((8 * k : Nat) : Int)
        from by omega]
  · rw [P.other "%r12" (by simp) (by decide), hk "%r12" (by decide), er _ (by decide)]

/-- The call model of the shipped compression over the byte-decoded field leaves:
    `ed25519_invert` runs its shipped prologue, its block over `invertCallModelB ra` and its
    epilogue; `fe25519_mul` runs `feMulFramed`, the block its shipped bytes decode to; and
    `ed25519_pack_sign` runs its shipped prologue, block and epilogue; each after the
    return address `ra` is pushed, and returns. -/
def compressCallModelB (ra : BitVec 64) : ACallModel := fun f sa =>
  if f = invertSym then invertCallB ra sa
  else if f = mulSym then mulCallB ra sa
  else if f = packSignSym then packCall ra sa
  else sa

theorem compressCallModelB_invertSym (ra : BitVec 64) (sa : AState) :
    compressCallModelB ra invertSym sa = invertCallB ra sa := by simp [compressCallModelB]

theorem compressCallModelB_mulSym (ra : BitVec 64) (sa : AState) :
    compressCallModelB ra mulSym sa = mulCallB ra sa := by
  simp [compressCallModelB, invertSym, mulSym]

theorem compressCallModelB_packSignSym (ra : BitVec 64) (sa : AState) :
    compressCallModelB ra packSignSym sa = packCall ra sa := by
  simp [compressCallModelB, invertSym, mulSym, packSignSym]

/-- **The callees of the compression over the byte-decoded field leaves meet
    `CompressCalleesF`.** -/
theorem compressCalleesF_compressCallModelB (ra : BitVec 64) :
    CompressCalleesF (compressCallModelB ra) := by
  refine ⟨fun sa h hz => ?_, fun sa h => ?_, fun sa h => ?_⟩
  · obtain ⟨hv, hf, h1, h2, h3⟩ := invertCallB_spec ra sa h hz
    unfold InvEffectF KeepsRegs
    rw [compressCallModelB_invertSym]
    exact ⟨hv, hf, h1, h2, h3⟩
  · obtain ⟨hv, hf, h1, hs⟩ := mulCallB_spec ra sa h
    unfold MulEffect
    rw [compressCallModelB_mulSym]
    exact ⟨⟨hv, hf, h1, hs "%rbx" (by decide)⟩, hs "%r12" (by decide)⟩
  · unfold PackEffect
    rw [compressCallModelB_packSignSym]
    exact packCall_spec ra sa h

/-- **The shipped `ed25519_compress` over the byte-decoded field leaves.** Every call to
    `fe25519_mul` and `fe25519_sqr`, including those inside `ed25519_invert`, runs
    `feMulFramed`, resp. `feSqrFramed`, the blocks the crate's shipped bytes decode to;
    `ed25519_invert` and `ed25519_pack_sign` run their shipped prologue, block and epilogue.
    For a state whose output and coordinate buffers are disjoint from the stack words the
    compression and its callees use, and whose third coordinate `Z` is below
    `2 ^ 255 - 19`, the four-limb value at the output pointer after the block is
    `y + 2 ^ 255 * (x % 2)`, where `x` and `y` are the first and second coordinates times
    `Z ^ (2 ^ 255 - 21)`, reduced modulo `2 ^ 255 - 19`. -/
theorem compressShippedBytes_correct (ra : BitVec 64) (sa : AState) (hsep : CompressSep sa)
    (hz : feO sa.mem (sa.regs "%rcx") 0 < pM) :
    feO (segsRunA (compressCallModelB ra) sa
        Ed25519CompressShipped.ed25519CompressShippedBlock).mem (sa.regs "%rdi") 0
      = feO sa.mem (sa.regs "%rdx") 0 * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM) % pM
        + 2 ^ 255 * (feO sa.mem (sa.regs "%rsi") 0
            * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM) % pM % 2) :=
  compressShippedF_correct_addr (compressCalleesF_compressCallModelB ra) sa hsep hz

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519BytesCalls
