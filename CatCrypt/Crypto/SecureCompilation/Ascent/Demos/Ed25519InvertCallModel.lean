/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertChain
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertLeafSqr
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertLeafMul
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees

/-!
# The call model of the shipped `ed25519_invert`

`invertCallModel` sends `fe25519_sqr` and `fe25519_mul` to the shipped block of that
function, run on the callee's frame eight bytes below the caller's `%rsp`, the return
address of the call, and with `%rsp` and the callee-saved registers at their values at the
call. The shipped `fe25519_sqr` saves and restores those registers with the `pushq`/`popq`
pair the import omits, and the shipped `fe25519_mul` with the red-zone stores and loads its
own block carries; the inversion keeps its input pointer in `%rbx` across the calls.

## Main definitions

* `callBlockSaved`: the state a call leaves.
* `invertCallModel`: the call model.

## Main results

* `invertCallModel_sqr`, `invertCallModel_mul`, `invertCallees_invertCallModel`: the two
  shipped callees meet the specifications `Ed25519InvertChain` states.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT (mulSym sqrSym)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (calleeSavedRegs)

/-- The state a call leaves: the callee's block run on the callee's frame, with `%rsp` and
    the callee-saved registers at their values at the call. The shipped `fe25519_sqr`
    saves and restores them with the `pushq`/`popq` pair the import omits; the shipped
    `fe25519_mul` saves and restores them in its own red zone. -/
def callBlockSaved (blk : List (JInstr 64)) (d : Int) (sa : AState) : AState :=
  { regs := fun r => if r ∈ "%rsp" :: calleeSavedRegs then sa.regs r
      else (runBlockA (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d)) blk).regs r
    flags := (runBlockA (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d)) blk).flags
    mem := (runBlockA (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d)) blk).mem }

theorem callBlockSaved_mem (blk : List (JInstr 64)) (d : Int) (sa : AState) :
    (callBlockSaved blk d sa).mem
      = (runBlockA (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d)) blk).mem := rfl

theorem callBlockSaved_rsp (blk : List (JInstr 64)) (d : Int) (sa : AState) :
    (callBlockSaved blk d sa).regs "%rsp" = sa.regs "%rsp" := by
  simp [callBlockSaved]

theorem callBlockSaved_rbx (blk : List (JInstr 64)) (d : Int) (sa : AState) :
    (callBlockSaved blk d sa).regs "%rbx" = sa.regs "%rbx" := by
  simp [callBlockSaved, calleeSavedRegs]

/-- The call model of the shipped inversion: each callee symbol at the shipped block of
    that function, run on the callee's frame eight bytes below the caller's `%rsp`, the
    return address of the call. -/
def invertCallModel : ACallModel := fun f sa =>
  if f = sqrSym then callBlockSaved Fe25519SqrShipped.fe25519SqrShippedBlock (-8) sa
  else if f = mulSym then callBlockSaved Fe25519MulShipped.fe25519MulShippedBlock (-8) sa
  else sa

theorem invertCallModel_sqrSym (sa : AState) :
    invertCallModel sqrSym sa
      = callBlockSaved Fe25519SqrShipped.fe25519SqrShippedBlock (-8) sa := by
  simp [invertCallModel]

theorem invertCallModel_mulSym (sa : AState) :
    invertCallModel mulSym sa
      = callBlockSaved Fe25519MulShipped.fe25519MulShippedBlock (-8) sa := by
  simp [invertCallModel, sqrSym, mulSym]

/-- **The shipped `fe25519_sqr` meets the square specification of the chain.** -/
theorem invertCallModel_sqr (sa : AState) : SqrEffect invertCallModel sqrSym sa := by
  have h := sqrShipped_correct_addr (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8)))
  rw [atRsp_mem] at h
  rw [atRsp_regs _ _ "%rdi" (by decide), atRsp_regs _ _ "%rsi" (by decide)] at h
  obtain ⟨hv, hf, -⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [invertCallModel_sqrSym, callBlockSaved_mem]; exact hv
  · rw [invertCallModel_sqrSym, callBlockSaved_mem]; exact frameCS_of_frameC _ hf
  · rw [invertCallModel_sqrSym]; exact callBlockSaved_rsp _ _ _
  · rw [invertCallModel_sqrSym]; exact callBlockSaved_rbx _ _ _

/-- **The shipped `fe25519_mul` meets the multiply specification of the chain.** -/
theorem invertCallModel_mul (sa : AState) (hsp : ArgsBelowSep sa) :
    MulEffect invertCallModel mulSym sa := by
  have hred : ∀ o : Int, (-48 : Int) ≤ o → o ≤ -8 → o % 8 = 0 →
      (-144 : Int) ≤ -8 + o ∧ -8 + o ≤ -8 ∧ (-8 + o) % 8 = 0 :=
    fun o a1 a2 a3 => ⟨by omega, by omega, by omega⟩
  have e_rsi : (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8))).regs "%rsi"
      = sa.regs "%rsi" := atRsp_regs _ _ _ (by decide)
  have e_rdx : (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8))).regs "%rdx"
      = sa.regs "%rdx" := atRsp_regs _ _ _ (by decide)
  have h := mulShipped_alias_addr (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8)))
    (by rw [e_rsi, atRsp_rsp]; exact rangeDisj_frame (-8) hsp.is hred)
    (by rw [e_rdx, atRsp_rsp]; exact rangeDisj_frame (-8) hsp.js hred)
  rw [atRsp_mem] at h
  rw [atRsp_regs _ _ "%rdi" (by decide), e_rsi, e_rdx, atRsp_rsp] at h
  obtain ⟨hv, hf, -⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [invertCallModel_mulSym, callBlockSaved_mem]; exact hv
  · rw [invertCallModel_mulSym, callBlockSaved_mem]
    intro x hx hy
    refine hf x hx fun i hi => ?_
    have h2 := hy (16 - i) (by omega)
    rw [redBase, addI, show (-144 : Int) + ((8 * (16 - i) : Nat) : Int)
      = -8 + (-(8 * (i + 1) : Nat) : Int) from by omega, ← addI] at h2
    exact h2
  · rw [invertCallModel_mulSym]; exact callBlockSaved_rsp _ _ _
  · rw [invertCallModel_mulSym]; exact callBlockSaved_rbx _ _ _

/-- **The two shipped callees of the inversion chain meet their specifications.** -/
theorem invertCallees_invertCallModel : InvertCallees invertCallModel :=
  ⟨invertCallModel_sqr, invertCallModel_mul⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof
