/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCalleesField

/-!
# The shipped `fe25519_sqr` on the address machine

`Fe25519SqrShipped.fe25519SqrShippedBlock` is the body of `fe25519_sqr` as printed by the
owned backend. This module carries its correctness to `AddrMem.runBlockA`, in the form the
callee specification of the inversion chain reads: the four-limb value at the block's own
`%rdi`, the memory outside that output, and `%rsp`.

## The route

The block is `canonD shippedBank` of itself and writes only the four cells at `%rdi`, each
after every cell it reads, so `AddrMemDerived.runBlockA_simD_readsBeforeWrites` carries a
name-keyed statement about it to the address machine with no separation hypothesis: the
input buffer may coincide with the output buffer. The name-keyed statement is
`Fe25519MulSqrProof.feSqrBlock_mod`, transported along the register allocation by
`Fe25519KernelsBytes.runBlock_renameBlock_mem`.

## Main results

* `sqrShipped_nameKeyed`: over the name-keyed memory the block stores the square modulo
  `p25519` at `%rdi`.
* `sqrShipped_correct_addr`: on the address machine the block leaves the square of the
  four-limb value at `%rsi`, reduced modulo `2 ^ 255 - 19`, at `%rdi`, changes no byte
  outside the 32 bytes at `%rdi`, and keeps `%rsp`. No hypothesis on the pointers.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (p25519)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddSubSelectProof (mem4)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel (feSqrBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (nameOf)

/-- The shipped square block with each three-operand multiply by an immediate whose
    source and destination agree put in two-operand form. -/
theorem sqr_deImulri :
    Fe25519SqrShipped.fe25519SqrShippedBlock.map deImulri = feSqrPhys := by decide +kernel

theorem runBlock_sqrShipped (st : JState 64) :
    runBlock st Fe25519SqrShipped.fe25519SqrShippedBlock = runBlock st feSqrPhys := by
  rw [← sqr_deImulri, runBlock_map_deImulri]

/-- The shipped square block, over the name-keyed memory, stores the square modulo
    `p25519` at `%rdi`. -/
theorem sqrShipped_nameKeyed (st : JState 64) :
    mem4 (runBlock st Fe25519SqrShipped.fe25519SqrShippedBlock).mem "%rdi"
      = mem4 st.mem "%rsi" ^ 2 % p25519 := by
  rw [runBlock_sqrShipped]
  have hz : nameOf feSqrAllocL "z" = "%rdi" := by decide
  have hm := runBlock_renameBlock_mem (nameOf feSqrAllocL) feSqrBlock feSqr_renInjOn st "z"
    (by decide +kernel)
  rw [hz] at hm
  have hx : (pullState (nameOf feSqrAllocL) st).mem "x" = st.mem "%rsi" := by
    have h : nameOf feSqrAllocL "x" = "%rsi" := by decide
    simp only [pullState, h]
  have h0 := CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof.feSqrBlock_mod
    (pullState (nameOf feSqrAllocL) st)
  simp only [CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519MulSqrProof.mem4,
    hx] at h0
  simp only [mem4, feSqrPhys, hm]
  simpa only [mem4, CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel.limbsNat]
    using h0

theorem canonD_sqr :
    canonD shippedBank Fe25519SqrShipped.fe25519SqrShippedBlock
      = Fe25519SqrShipped.fe25519SqrShippedBlock := by decide +kernel

theorem sqr_rbw :
    readsBeforeWritesB (canonD shippedBank Fe25519SqrShipped.fe25519SqrShippedBlock)
      = true := by decide +kernel

theorem sqr_wk :
    writeKeys (canonD shippedBank Fe25519SqrShipped.fe25519SqrShippedBlock)
      = outCells := by decide +kernel

/-- **The shipped `fe25519_sqr` block on the address machine.** The block leaves the
    square of the four-limb value at `%rsi`, reduced modulo `2 ^ 255 - 19`, at `%rdi`,
    changes no byte outside the 32 bytes at `%rdi`, and keeps `%rsp`. The input buffer
    may coincide with the output buffer. -/
theorem sqrShipped_correct_addr (sa : AState) :
    feO (runBlockA sa Fe25519SqrShipped.fe25519SqrShippedBlock).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 ^ 2 % pM
      ∧ FrameC sa.mem (runBlockA sa Fe25519SqrShipped.fe25519SqrShippedBlock).mem
          (sa.regs "%rdi") 4
      ∧ (runBlockA sa Fe25519SqrShipped.fe25519SqrShippedBlock).regs "%rsp"
          = sa.regs "%rsp" := by
  obtain ⟨hout, hfr⟩ := leafOut _ fe25519Sqr_disciplinedD sqr_rbw sqr_wk sa
  refine ⟨?_, hfr, runBlockA_regs_of_not_dsts _ _ _ (rsp_not_dst_of_all (by decide +kernel))⟩
  rw [feO_eq_limbsNat, hout 0 (by simp [outCells]), hout 8 (by simp [outCells]),
    hout 16 (by simp [outCells]), hout 24 (by simp [outCells]), canonD_sqr]
  show mem4 (runBlock (jOf shippedBank sa) Fe25519SqrShipped.fe25519SqrShippedBlock).mem "%rdi"
    = _
  rw [sqrShipped_nameKeyed, mem4_jOf _ _ shippedBank_rsi, pM_eq]

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
