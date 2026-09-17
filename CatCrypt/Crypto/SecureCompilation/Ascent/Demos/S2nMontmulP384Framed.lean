/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Bytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFrame

/-!
# The imported `bignum_montmul_p384` block inside the red-zone leaf frame

`s2nMontmulP384FramedBlock` is the imported s2n-bignum body `s2nMontmulP384Block` between
`LeafFrame.framePrologue` and `LeafFrame.frameEpilogue`: six stores of the callee-saved
registers `%rbx`, `%rbp`, `%r12`, `%r13`, `%r14`, `%r15` into the red-zone slots
`-8(%rsp)`, …, `-48(%rsp)`, the body, and six loads from the same slots. The frame of the
s2n-bignum source (`pushq`/`popq`) is replaced by this block; `endbr64` and `retq` are not
`JInstr` instructions and stay outside it.

The body satisfies `LeafFrame.frameSafe` (it does not address memory through `%rsp` and
does not write `%rsp`), checked per segment by `decide`. `LeafFrame.runBlock_framed` then
gives the machine-level result, and `LeafFrame.corresJ_framed` the refinement that
`encodeJBlock_bytesCorresJ` carries to the encoded bytes.

## What the results do not give

* That `decodeJStream` and `JasminModel.evalInstr` agree with an x86-64 processor on these
  instructions is not proved here, as for `S2nMontmulP384Bytes`.
* `JasminModel` keys memory by the base register's name, so the red-zone slots are the
  bank named `"%rsp"`, which the model keeps apart from the banks `"%rdi"`, `"%rsi"` and
  `"%rcx"`. That the red zone does not overlap the caller's buffers is the System V
  convention, not a theorem here. The assumptions of `S2nMontmulP384Proof` (no aliasing
  between the output and the inputs; the bank `"%rcx"` holds the buffer passed in `%rdx`)
  carry over.
* `endbr64` and `retq` are not described.

## Main results

* `s2nMontmulP384FramedBlock`: the framed block.
* `s2nMontmulP384Block_frameSafe`: every body instruction satisfies `frameSafe`.
* `s2nMontmulP384Framed_correct`: the framed block computes the Montgomery product modulo
  `p384` at `%rdi` and ends with `%rsp` and the six callee-saved registers at their entry
  values.
* `s2nMontmulP384Framed_corresJ`: the framed block refines `montAbs` at
  `LeafFrame.FrameRel SRm`.
* `s2nMontmulP384Framed_decode`: the encoded framed block decodes to itself.
* `s2nMontmulP384FramedBytes_correct`: the instructions the encoded framed block decodes
  to compute the Montgomery product and restore `%rsp` and the callee-saved registers.
-/

@[expose] public section

set_option autoImplicit false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFrame
open CatCrypt.Crypto.Optimizer.GenericRegAlloc
open CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped
open CatCrypt.Crypto.Optimizer.JInstrRegAllocValidated

/-- The imported body between the red-zone prologue and epilogue. -/
def s2nMontmulP384FramedBlock : List (JInstr 64) :=
  framePrologue ++ s2nMontmulP384Block ++ frameEpilogue

/-- The framed block has 276 instructions. -/
theorem s2nMontmulP384FramedBlock_length : s2nMontmulP384FramedBlock.length = 276 := by
  simp only [s2nMontmulP384FramedBlock, List.length_append, s2nMontmulP384Block_length]
  rfl

/-! ## The body condition, per segment -/

theorem seg01_frameSafe : s2nMontmulP384Seg01.all frameSafe = true := by decide
theorem seg02_frameSafe : s2nMontmulP384Seg02.all frameSafe = true := by decide
theorem seg03_frameSafe : s2nMontmulP384Seg03.all frameSafe = true := by decide
theorem seg04_frameSafe : s2nMontmulP384Seg04.all frameSafe = true := by decide
theorem seg05_frameSafe : s2nMontmulP384Seg05.all frameSafe = true := by decide
theorem seg06_frameSafe : s2nMontmulP384Seg06.all frameSafe = true := by decide
theorem seg07_frameSafe : s2nMontmulP384Seg07.all frameSafe = true := by decide
theorem seg08_frameSafe : s2nMontmulP384Seg08.all frameSafe = true := by decide
theorem seg09_frameSafe : s2nMontmulP384Seg09.all frameSafe = true := by decide
theorem seg10_frameSafe : s2nMontmulP384Seg10.all frameSafe = true := by decide
theorem seg11_frameSafe : s2nMontmulP384Seg11.all frameSafe = true := by decide
theorem seg12_frameSafe : s2nMontmulP384Seg12.all frameSafe = true := by decide
theorem seg13_frameSafe : s2nMontmulP384Seg13.all frameSafe = true := by decide
theorem seg14_frameSafe : s2nMontmulP384Seg14.all frameSafe = true := by decide
theorem seg15_frameSafe : s2nMontmulP384Seg15.all frameSafe = true := by decide
theorem seg16_frameSafe : s2nMontmulP384Seg16.all frameSafe = true := by decide
theorem seg17_frameSafe : s2nMontmulP384Seg17.all frameSafe = true := by decide

/-- Every instruction of `s2nMontmulP384Block` satisfies `frameSafe`: the segment checks
    combined over the concatenation. -/
theorem s2nMontmulP384Block_frameSafe :
    ∀ i ∈ s2nMontmulP384Block, frameSafe i = true := by
  have h : s2nMontmulP384Block.all frameSafe = true := by
    simp only [s2nMontmulP384Block, List.all_append, seg01_frameSafe, seg02_frameSafe,
      seg03_frameSafe, seg04_frameSafe, seg05_frameSafe, seg06_frameSafe, seg07_frameSafe,
      seg08_frameSafe, seg09_frameSafe, seg10_frameSafe, seg11_frameSafe, seg12_frameSafe,
      seg13_frameSafe, seg14_frameSafe, seg15_frameSafe, seg16_frameSafe, seg17_frameSafe,
      Bool.and_self]
  exact List.all_eq_true.mp h

/-! ## The machine-level result -/

/-- **The framed block computes the Montgomery product and restores the frame.** Under the
    hypotheses of `s2nMontmulP384_correct`, running `s2nMontmulP384FramedBlock` stores at
    `[%rdi + 0], …, [%rdi + 40]` a value `z < p384` with `z = x · y · (2^384)⁻¹` in
    `ZMod p384`, and ends with `%rsp` and each of the six callee-saved registers at its
    entry value. -/
theorem s2nMontmulP384Framed_correct (st : JState 64)
    (hxy : mem6 st.mem "%rsi" * mem6 st.mem "%rcx" ≤ 2 ^ 384 * p384) :
    mem6 (runBlock st s2nMontmulP384FramedBlock).mem "%rdi" < p384 ∧
      ((mem6 (runBlock st s2nMontmulP384FramedBlock).mem "%rdi" : Nat) : ZMod p384)
        = (mem6 st.mem "%rsi" : ZMod p384) * (mem6 st.mem "%rcx" : Nat)
          * ((2 ^ 384 : Nat) : ZMod p384)⁻¹ ∧
      (∀ r ∈ calleeSavedRegs, (runBlock st s2nMontmulP384FramedBlock).regs r = st.regs r) ∧
      (runBlock st s2nMontmulP384FramedBlock).regs "%rsp" = st.regs "%rsp" := by
  unfold s2nMontmulP384FramedBlock
  have hm : (runBlock st (framePrologue ++ s2nMontmulP384Block ++ frameEpilogue)).mem "%rdi"
      = (runBlock st s2nMontmulP384Block).mem "%rdi" :=
    runBlock_framed_mem_other st _ s2nMontmulP384Block_frameSafe "%rdi" (by decide)
  have hm6 : mem6 (runBlock st (framePrologue ++ s2nMontmulP384Block ++ frameEpilogue)).mem "%rdi"
      = mem6 (runBlock st s2nMontmulP384Block).mem "%rdi" := by
    simp only [mem6, hm]
  rw [hm6]
  exact ⟨(s2nMontmulP384_correct st hxy).1, (s2nMontmulP384_correct st hxy).2,
    runBlock_framed_calleeSaved st _ s2nMontmulP384Block_frameSafe,
    runBlock_framed_rsp st _ s2nMontmulP384Block_frameSafe⟩

/-! ## The refinement through the frame -/

/-- At stage `17`, `SRm` reads only the banks `"%rsi"`, `"%rcx"` and `"%rdi"`, so it is
    invariant under `FrameAgree`. -/
theorem srm_stage17_frameAgree (s t : JState 64) (hA : FrameAgree s t) (x y acc : Nat)
    (h : SRm s ⟨17, x, y, acc⟩) : SRm t ⟨17, x, y, acc⟩ := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := hA.mem "%rsi" (by decide)
  have e2 := hA.mem "%rcx" (by decide)
  have e3 := hA.mem "%rdi" (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1]; simp only [mem6, e1]
  · rw [← h2]; simp only [mem6, e2]
  · show mem6 t.mem "%rdi" = acc
    have h3' : mem6 s.mem "%rdi" = acc := h3
    rw [← h3']; simp only [mem6, e3]

/-- **The framed block refines the abstract Montgomery multiplication.** At
    `FrameRel SRm`, the abstract component goes from stage `0` to stage `17` with
    accumulator `montAbs x y`, and the recorded values of `%rsp` and the callee-saved
    registers are the ones the framed block ends with. -/
theorem s2nMontmulP384Framed_corresJ :
    CorresJ (FrameRel SRm) (fun p => p.1.stage = 0 ∧ p.1.x < 2 ^ 384)
      (fun p => ({ stage := 17, x := p.1.x, y := p.1.y, acc := montAbs p.1.x p.1.y }, p.2))
      s2nMontmulP384FramedBlock :=
  corresJ_framed s2nMontmulP384Block_frameSafe s2nMontmulP384_corresJ
    fun _ _ s t hA h => srm_stage17_frameAgree s t hA _ _ _ h

/-! ## The byte-level results -/

theorem framePrologue_instrOk : framePrologue.all s2nInstrOk = true := by decide
theorem frameEpilogue_instrOk : frameEpilogue.all s2nInstrOk = true := by decide

/-- Every instruction of the framed block satisfies `s2nInstrOk`. -/
theorem s2nMontmulP384FramedBlock_instrOk :
    ∀ i ∈ s2nMontmulP384FramedBlock, s2nInstrOk i = true := by
  intro i hi
  simp only [s2nMontmulP384FramedBlock, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact List.all_eq_true.mp framePrologue_instrOk i hi
  · exact s2nMontmulP384Block_instrOk i hi
  · exact List.all_eq_true.mp frameEpilogue_instrOk i hi

theorem s2nMontmulP384FramedBlock_covered :
    ∀ i ∈ s2nMontmulP384FramedBlock, blockCovered i = true := fun i hi => by
  have := s2nMontmulP384FramedBlock_instrOk i hi
  simp only [s2nInstrOk, Bool.and_eq_true] at this
  exact this.1.1

theorem s2nMontmulP384FramedBlock_mulxRdxOk :
    ∀ i ∈ s2nMontmulP384FramedBlock, mulxRdxOk s2nAlloc i = true := fun i hi => by
  have := s2nMontmulP384FramedBlock_instrOk i hi
  simp only [s2nInstrOk, Bool.and_eq_true] at this
  exact this.1.2

/-- `nameOf s2nAlloc` is the identity on the framed block's names. -/
theorem nameOf_s2nAlloc_framed (n : String)
    (hn : n ∈ blockNamesXsym s2nMontmulP384FramedBlock) : nameOf s2nAlloc n = n := by
  obtain ⟨i, hi, hni⟩ := List.mem_flatMap.mp hn
  have := s2nMontmulP384FramedBlock_instrOk i hi
  simp only [s2nInstrOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact nameOf_s2nAlloc n (this.2 n hni)

/-- `nameOf s2nAlloc` is injective on the framed block's names. -/
theorem s2nMontmulP384FramedBlock_renInjOn :
    RenInjOn (blockNamesXsym s2nMontmulP384FramedBlock) (nameOf s2nAlloc) := by
  intro a ha b hb hab
  rwa [nameOf_s2nAlloc_framed a ha, nameOf_s2nAlloc_framed b hb] at hab

/-- `%rsp` and the six callee-saved registers are names of the prologue. -/
theorem frameRegs_mem_prologue :
    ∀ r ∈ "%rsp" :: calleeSavedRegs, r ∈ blockNamesXsym framePrologue := by decide

/-- `%rsp` and the six callee-saved registers are names of the framed block. -/
theorem frameRegs_mem_framed (r : String) (hr : r ∈ "%rsp" :: calleeSavedRegs) :
    r ∈ blockNamesXsym s2nMontmulP384FramedBlock := by
  have h := frameRegs_mem_prologue r hr
  simp only [blockNamesXsym, s2nMontmulP384FramedBlock, List.flatMap_append,
    List.mem_append] at h ⊢
  exact Or.inl (Or.inl h)

/-- `%rdi`, the output base register, is a name of the framed block. -/
theorem rdi_mem_framed : "%rdi" ∈ blockNamesXsym s2nMontmulP384FramedBlock := by
  have h := rdi_mem_blockNamesXsym
  simp only [blockNamesXsym, s2nMontmulP384FramedBlock, List.flatMap_append,
    List.mem_append] at h ⊢
  exact Or.inl (Or.inr h)

/-- **The encoded framed block refines the abstract Montgomery multiplication.** -/
theorem s2nMontmulP384Framed_bytesCorresJ :
    BytesCorresJ
      (SRalloc (blockNamesXsym s2nMontmulP384FramedBlock) (nameOf s2nAlloc) (FrameRel SRm))
      (fun p => p.1.stage = 0 ∧ p.1.x < 2 ^ 384)
      (fun p => ({ stage := 17, x := p.1.x, y := p.1.y, acc := montAbs p.1.x p.1.y }, p.2))
      s2nMontmulP384FramedBlock.length (encodeJBlock s2nAlloc s2nMontmulP384FramedBlock) :=
  encodeJBlock_bytesCorresJ s2nAlloc s2nMontmulP384FramedBlock
    s2nMontmulP384FramedBlock_covered s2nMontmulP384FramedBlock_mulxRdxOk
    s2nMontmulP384FramedBlock_renInjOn s2nMontmulP384Framed_corresJ

/-- **The encoded framed block decodes to itself.** -/
theorem s2nMontmulP384Framed_decode :
    decodeJStream 276 (encodeJBlock s2nAlloc s2nMontmulP384FramedBlock)
      = some s2nMontmulP384FramedBlock := by
  rw [← s2nMontmulP384FramedBlock_length, roundtrip_block _ _
    s2nMontmulP384FramedBlock_covered s2nMontmulP384FramedBlock_mulxRdxOk]
  refine congrArg some ((List.map_congr_left fun i hi => ?_).trans (List.map_id _))
  rw [renameJ_eq_renameInstr _ _ (loadSymFree_of_blockCovered _
    (s2nMontmulP384FramedBlock_covered i hi))]
  exact renameInstr_eq_self_of_fix _ _ fun n hn =>
    nameOf_s2nAlloc_framed n (List.mem_flatMap.mpr ⟨i, hi, hn⟩)

/-- **The encoded framed block computes the Montgomery product and restores the frame.**
    The byte string `encodeJBlock s2nAlloc s2nMontmulP384FramedBlock` decodes as 276
    instructions `c` such that, for every machine state whose six words at `%rsi` hold `x`
    and whose six words at `%rcx` hold `y` with `x · y ≤ 2^384 · p384`, running `c` under
    `runBlock` stores at `[%rdi + 0], …, [%rdi + 40]` a value `z < p384` with
    `z = x · y · (2^384)⁻¹` in `ZMod p384`, and ends with `%rsp` and each callee-saved
    register at its entry value. -/
theorem s2nMontmulP384FramedBytes_correct :
    ∃ c, decodeJStream 276 (encodeJBlock s2nAlloc s2nMontmulP384FramedBlock) = some c ∧
      ∀ st : JState 64, mem6 st.mem "%rsi" * mem6 st.mem "%rcx" ≤ 2 ^ 384 * p384 →
        mem6 (runBlock st c).mem "%rdi" < p384 ∧
          ((mem6 (runBlock st c).mem "%rdi" : Nat) : ZMod p384)
            = (mem6 st.mem "%rsi" : ZMod p384) * (mem6 st.mem "%rcx" : Nat)
              * ((2 ^ 384 : Nat) : ZMod p384)⁻¹ ∧
          ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st c).regs r = st.regs r := by
  obtain ⟨c, hdec, hcor⟩ := s2nMontmulP384Framed_bytesCorresJ
  rw [s2nMontmulP384FramedBlock_length] at hdec
  refine ⟨c, hdec, fun st hxy => ?_⟩
  have hrel0 :
      StateRelOn (blockNamesXsym s2nMontmulP384FramedBlock) (nameOf s2nAlloc) st st :=
    ⟨fun n hn => by rw [nameOf_s2nAlloc_framed n hn], rfl,
      fun b hb o => by rw [nameOf_s2nAlloc_framed b hb]⟩
  obtain ⟨st₀, hrel, ⟨-, -, hz⟩, hsv⟩ := hcor st
    (⟨0, mem6 st.mem "%rsi", mem6 st.mem "%rcx", 0⟩, st.regs)
    ⟨st, hrel0, ⟨rfl, rfl, trivial⟩, fun _ _ => rfl⟩ ⟨rfl, mem6_lt _ _⟩
  have hm : mem6 (runBlock st c).mem "%rdi" = mem6 st₀.mem "%rdi" := by
    have h := hrel.memOn "%rdi" rdi_mem_framed
    rw [nameOf_s2nAlloc_framed _ rdi_mem_framed] at h
    simp only [mem6, h]
  have hz' : mem6 st₀.mem "%rdi" = montAbs (mem6 st.mem "%rsi") (mem6 st.mem "%rcx") := hz
  rw [hm, hz']
  refine ⟨(montAbs_spec _ _ (mem6_lt _ _) hxy).1, (montAbs_spec _ _ (mem6_lt _ _) hxy).2,
    fun r hr => ?_⟩
  have h := hrel.regsOn r (frameRegs_mem_framed r hr)
  rw [nameOf_s2nAlloc_framed _ (frameRegs_mem_framed r hr)] at h
  exact h.trans (hsv r hr)

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
