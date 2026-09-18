/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCalleesField

/-!
# The shipped `fe25519_mul` on the address machine with an aliased output

`Ed25519LeafCallees.mulShipped_correct_addr` states the shipped multiply for pairwise
disjoint argument and output buffers. The inversion chain calls the multiply with the
output buffer equal to one of the argument buffers, so this module states it again with
only the disjointness the block needs: its red-zone slots apart from the three buffers.

## The route

`Fe25519MulShipped.fe25519MulShippedBlock` is `LeafFrame.framePrologue ++ mulCore ++
LeafFrame.frameEpilogue`. The prologue writes the six red-zone slots and the epilogue
reads them back, which is why the whole block needs its argument cells separated: a read
after a write must lie in the separated cell set. `mulCore` writes only the four cells at
`%rdi`, each after every cell it reads, so on it `AddrMemDerived.runBlockA_simD_from`
needs no separation beyond the output cells, which are separated at every pointer. The
prologue's writes and the epilogue's reads are then handled directly.

## Main definitions

* `mulCore`: the body of the shipped multiply between its red-zone prologue and epilogue.
* `redCells`: the six red-zone cells of the prologue.

## Main results

* `mulCore_nameKeyed`, `mulCore_correct_addr`: the body computes the product modulo
  `2 ^ 255 - 19` at `%rdi` and changes no byte outside the 32 bytes there, at every state.
* `mulShipped_alias_addr`: the shipped block leaves the product of the four-limb values at
  `%rsi` and at `%rdx`, reduced modulo `2 ^ 255 - 19`, at `%rdi`, changes no byte outside
  the 32 bytes at `%rdi` and the 48 bytes below `%rsp`, and keeps `%rsp`, whenever the two
  argument buffers and the output buffer are disjoint from the red-zone slots.

Provenance class: `@reimported`.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFrame
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (p25519 feMulBlock)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddSubSelectProof (mem4)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (nameOf)

/-! ## 1. The body between the red-zone prologue and epilogue -/

/-- The body of the shipped multiply between its red-zone prologue and epilogue. -/
def mulCore : List (JInstr 64) :=
  Fe25519MulShipped.fe25519MulShippedSeg02 ++ Fe25519MulShipped.fe25519MulShippedSeg03 ++
    Fe25519MulShipped.fe25519MulShippedSeg04

theorem mulShipped_split :
    Fe25519MulShipped.fe25519MulShippedBlock = framePrologue ++ mulCore ++ frameEpilogue := by
  decide +kernel

theorem mulCore_deImulri : mulCore.map deImulri = feMulPre ++ feMulPhys := by decide +kernel

theorem runBlock_mulCore (st : JState 64) :
    runBlock st mulCore = runBlock st (feMulPre ++ feMulPhys) := by
  rw [← mulCore_deImulri, runBlock_map_deImulri]

/-- The body, over the name-keyed memory, stores the product modulo `p25519` at `%rdi`. -/
theorem mulCore_nameKeyed (st : JState 64) :
    mem4 (runBlock st mulCore).mem "%rdi" = mem4 st.mem "%rsi" * mem4 st.mem "%rcx" % p25519 := by
  rw [runBlock_mulCore]
  have hz : nameOf feMulAllocL "z" = "%rdi" := by decide
  have hm := runBlock_renameBlock_mem (nameOf feMulAllocL) feMulBlock feMul_renInjOn
    (runBlock st feMulPre) "z" (by decide +kernel)
  rw [hz] at hm
  have hx : (pullState (nameOf feMulAllocL) (runBlock st feMulPre)).mem "x" = st.mem "%rsi" := by
    have h : nameOf feMulAllocL "x" = "%rsi" := by decide
    simp only [pullState, h]
    rfl
  have hy : (pullState (nameOf feMulAllocL) (runBlock st feMulPre)).mem "y" = st.mem "%rcx" := by
    have h : nameOf feMulAllocL "y" = "%rcx" := by decide
    simp only [pullState, h]
    rfl
  have h0 := CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof.feMulBlock_mod
    (pullState (nameOf feMulAllocL) (runBlock st feMulPre))
  simp only [CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof.mem4,
    hx, hy] at h0
  rw [Ascent.runBlock_append]
  simp only [mem4, feMulPhys, hm]
  simpa only [mem4, CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.limbsNat]
    using h0

/-! ## 2. The body on the address machine -/

theorem mulCore_disciplinedFromD :
    disciplinedFromD shippedBank mulEntryD mulCore = true := by decide +kernel

theorem canonFromD_mulCore :
    canonFromD shippedBank mulEntryD mulCore = mulCore := by decide +kernel

theorem mulCore_rbw :
    readsBeforeWritesFromB outCells false (canonFromD shippedBank mulEntryD mulCore)
      = true := by decide +kernel

theorem mulCore_wk :
    writeKeys (canonFromD shippedBank mulEntryD mulCore) = outCells := by decide +kernel

/-- **The body of the shipped multiply on the address machine.** At every state it leaves
    the product of the four-limb values at `%rsi` and at `%rdx`, reduced modulo
    `2 ^ 255 - 19`, at `%rdi`, changes no byte outside the 32 bytes at `%rdi`, and keeps
    `%rsp`. An argument buffer may coincide with the output buffer. -/
theorem mulCore_correct_addr (sa : AState) :
    feO (runBlockA sa mulCore).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 * feO sa.mem (sa.regs "%rdx") 0 % pM
      ∧ FrameC sa.mem (runBlockA sa mulCore).mem (sa.regs "%rdi") 4
      ∧ (runBlockA sa mulCore).regs "%rsp" = sa.regs "%rsp" := by
  have hP : ∀ b : String, b ≠ "%rcx" → mulP sa b = sa.regs b := by
    intro b hb; simp [mulP, hb]
  have hsep : Separated shippedBank (mulP sa) outCells := separated_outCells _
  obtain ⟨-, -, hK, -, -⟩ := runBlockA_simD_from shippedBank (mulP sa) mulEntryD mulCore
    outCells mulCore_disciplinedFromD mulCore_rbw (fun k hk => by rwa [mulCore_wk] at hk)
    (by simp [mulEntryD, DState.cellKeys]) sa hsep (mulRegInv sa) (mulCellInv sa)
  refine ⟨?_, ?_, runBlockA_regs_of_not_dsts _ _ _ (rsp_not_dst_of_all (by decide +kernel))⟩
  · have hout : ∀ o : Int, ("%rdi", o) ∈ outCells →
        read64 (runBlockA sa mulCore).mem (sa.regs "%rdi" + BitVec.ofInt 64 o)
          = (runBlock (jOfD shippedBank (mulP sa) sa) mulCore).mem "%rdi" o := by
      intro o ho
      have := hK ("%rdi", o) ho
      rw [absMem_shipped _ _ _ _ shippedBank_rdi, hP _ (by decide), canonFromD_mulCore] at this
      exact this
    have hin : ∀ (b c : String), shippedBank b = some b → mulP sa b = sa.regs c →
        mem4 (jOfD shippedBank (mulP sa) sa).mem b = feO sa.mem (sa.regs c) 0 := by
      intro b c hb hbc
      simp only [mem4, jOfD, absMem_shipped _ _ _ _ hb, hbc, feO_eq_limbsNat]
    rw [feO_eq_limbsNat, hout 0 (by simp [outCells]), hout 8 (by simp [outCells]),
      hout 16 (by simp [outCells]), hout 24 (by simp [outCells])]
    show mem4 (runBlock (jOfD shippedBank (mulP sa) sa) mulCore).mem "%rdi" = _
    rw [mulCore_nameKeyed, hin "%rsi" "%rsi" shippedBank_rsi (hP _ (by decide)),
      hin "%rcx" "%rdx" (by decide) (by simp [mulP]), pM_eq]
  · intro x hx
    refine runBlockA_mem_frameD_from shippedBank (mulP sa) x mulCore mulEntryD sa
      mulCore_disciplinedFromD (mulRegInv sa) (mulCellInv sa) ?_ ?_
    · intro k hk
      rw [mulCore_wk] at hk
      have hrdi : mulP sa "%rdi" = sa.regs "%rdi" := by simp [mulP]
      have hk' : k = ("%rdi", 0) ∨ k = ("%rdi", 8) ∨ k = ("%rdi", 16) ∨ k = ("%rdi", 24) := by
        simpa [outCells] using hk
      rcases hk' with rfl | rfl | rfl | rfl
      · simpa [keyAddr_shipped _ _ _ shippedBank_rdi, hrdi] using hx 0 (by omega)
      · simpa [keyAddr_shipped _ _ _ shippedBank_rdi, hrdi] using hx 1 (by omega)
      · simpa [keyAddr_shipped _ _ _ shippedBank_rdi, hrdi] using hx 2 (by omega)
      · simpa [keyAddr_shipped _ _ _ shippedBank_rdi, hrdi] using hx 3 (by omega)
    · intro k hk c hc hne
      have hc' : c ∈ writeKeys (canonFromD shippedBank mulEntryD mulCore) := by
        simpa [mulEntryD, DState.cellKeys] using hc
      exact hsep k (by rwa [mulCore_wk] at hk) c (by rwa [mulCore_wk] at hc') (Ne.symm hne)

/-! ## 3. The red-zone prologue and epilogue -/

/-- The six red-zone cells the prologue writes. -/
def redCells : List (String × Int) :=
  [("%rsp", -8), ("%rsp", -16), ("%rsp", -24), ("%rsp", -32), ("%rsp", -40), ("%rsp", -48)]

theorem framePrologue_disciplinedD : disciplinedD shippedBank framePrologue = true := by
  decide +kernel

theorem framePrologue_wk : writeKeys (canonD shippedBank framePrologue) = redCells := by
  decide +kernel

theorem separated_redCells (R : String → BitVec 64) : Separated shippedBank R redCells := by
  intro k hk k' hk' hne
  simp only [redCells, List.mem_cons, List.not_mem_nil, or_false] at hk hk'
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [keyAddr_shipped _ _ _ shippedBank_rsp] <;>
    first
      | exact absurd rfl hne
      | exact djSS _ _ _ (by norm_num) (by norm_num)

theorem framePrologue_regs (sa : AState) (r : String) :
    (runBlockA sa framePrologue).regs r = sa.regs r := by
  refine runBlockA_regs_of_not_dsts _ _ _ fun i hi => ?_
  simp only [framePrologue, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dsts]

/-- The prologue changes no byte outside the 48 bytes below `%rsp`. -/
theorem framePrologue_frameC (sa : AState) :
    FrameC sa.mem (runBlockA sa framePrologue).mem
      (sa.regs "%rsp" + BitVec.ofInt 64 (-48)) 6 := by
  intro x hx
  refine runBlockA_mem_frameD shippedBank framePrologue framePrologue_disciplinedD sa x
    (by rw [framePrologue_wk]; exact separated_redCells _) ?_
  intro k hk
  rw [framePrologue_wk] at hk
  have hk' : k = ("%rsp", -8) ∨ k = ("%rsp", -16) ∨ k = ("%rsp", -24) ∨ k = ("%rsp", -32) ∨
      k = ("%rsp", -40) ∨ k = ("%rsp", -48) := by simpa [redCells] using hk
  have key : ∀ (o : Int) (m : Nat), m < 6 → (-48 : Int) + ((8 * m : Nat) : Int) = o →
      ¬ InRange8 (keyAddr shippedBank sa.regs ("%rsp", o)) x := by
    intro o m hm he
    rw [keyAddr_shipped _ _ _ shippedBank_rsp, ← he, ← addI]
    exact hx m hm
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact key _ 5 (by omega) (by omega)
  · exact key _ 4 (by omega) (by omega)
  · exact key _ 3 (by omega) (by omega)
  · exact key _ 2 (by omega) (by omega)
  · exact key _ 1 (by omega) (by omega)
  · exact key _ 0 (by omega) (by omega)

/-- A four-limb value disjoint from the 48 bytes below `%rsp` survives the prologue. -/
theorem feO_redFrame {m m' : AMem} {sp p : BitVec 64}
    (hf : FrameC m m' (sp + BitVec.ofInt 64 (-48)) 6)
    (hd : RangeDisj p 0 24 sp (-48) (-8)) : feO m' p 0 = feO m p 0 := by
  refine feO_frame hf fun k hk j hj => ?_
  simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
  rw [addI]
  exact (hd (0 + j) (-48 + ((8 * k : Nat) : Int)) (by omega) (by omega)
    (by rcases hj with rfl | rfl | rfl | rfl <;> omega) (by omega) (by omega) (by omega)).symm

theorem frameEpilogue_mem (sa : AState) : (runBlockA sa frameEpilogue).mem = sa.mem := rfl

/-! ## 4. The shipped multiply with an aliased output -/

/-- **The shipped `fe25519_mul` block on the address machine, output aliasing allowed.**
    When the two argument buffers are disjoint from the 48 bytes below `%rsp`, the block
    leaves the product of the four-limb values at `%rsi` and at `%rdx`, reduced modulo
    `2 ^ 255 - 19`, at `%rdi`; it changes no byte outside the 32 bytes at `%rdi` and the
    48 bytes below `%rsp`, and keeps `%rsp`. The output buffer may coincide with an
    argument buffer. -/
theorem mulShipped_alias_addr (sa : AState)
    (hi : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-48) (-8))
    (hj : RangeDisj (sa.regs "%rdx") 0 24 (sa.regs "%rsp") (-48) (-8)) :
    feO (runBlockA sa Fe25519MulShipped.fe25519MulShippedBlock).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 * feO sa.mem (sa.regs "%rdx") 0 % pM
      ∧ FrameCRed sa.mem (runBlockA sa Fe25519MulShipped.fe25519MulShippedBlock).mem
          (sa.regs "%rdi") 4 (sa.regs "%rsp") 6
      ∧ (runBlockA sa Fe25519MulShipped.fe25519MulShippedBlock).regs "%rsp"
          = sa.regs "%rsp" := by
  have hrun : runBlockA sa Fe25519MulShipped.fe25519MulShippedBlock
      = runBlockA (runBlockA (runBlockA sa framePrologue) mulCore) frameEpilogue := by
    rw [mulShipped_split, runBlockA_append, runBlockA_append]
  set sb := runBlockA sa framePrologue with hsb
  have hbr : ∀ r : String, sb.regs r = sa.regs r := framePrologue_regs sa
  obtain ⟨hval, hfr, -⟩ := mulCore_correct_addr sb
  rw [hbr, hbr, hbr] at hval
  rw [hbr] at hfr
  rw [feO_redFrame (framePrologue_frameC sa) hi, feO_redFrame (framePrologue_frameC sa) hj]
    at hval
  refine ⟨?_, ?_, runBlockA_regs_of_not_dsts _ _ _ (rsp_not_dst_of_all (by decide +kernel))⟩
  · rw [hrun, frameEpilogue_mem]
    exact hval
  · intro x hx hy
    rw [hrun, frameEpilogue_mem]
    rw [hfr x hx]
    refine framePrologue_frameC sa x fun k hk => ?_
    rw [addI, show (-48 : Int) + ((8 * k : Nat) : Int)
      = (-(8 * ((5 - k) + 1) : Nat) : Int) from by omega]
    exact hy (5 - k) (by omega)

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
