/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCalleesJoin

/-!
# The call model of the shipped `ed25519_madd`

`maddCallModel` sends each callee symbol of the shipped mixed addition to the shipped
block of that function, run on the callee's own frame: the field leaves eight bytes below
the caller's `%rsp`, the return address of the call, and the concatenation another 112
bytes below, the stack its body allocates. The `%rsp` the caller sees is restored on
return.

## What the model meets

`Ed25519MaddShippedParts.FieldCallee` holds of the model at `fe25519_add` and
`fe25519_sub`: both blocks write only the four words at their `%rdi`, and both read every
cell before writing it, so neither statement carries a hypothesis.

`fe25519_mul` writes six red-zone slots below its `%rsp` and `ed25519_join16` seventeen
slots in its own frame, so their frames are `FrameCRed` and `FrameCJoin`, over the output
and those slots, rather than `FieldCallee`'s and `JoinCallee`'s frame over the output
alone. Both also need their cells pairwise separated: `fe25519_mul` reads its red-zone
slots after writing them, and `ed25519_join16` reads its stack slots after writing them,
so neither is covered by the reads-before-writes rule that makes the add and sub
statements hypothesis-free.

## Main definitions

* `atRsp`, `callBlock`: the state with `%rsp` set to a value, and the state a call leaves.
* `maddCallModel`: the call model.

## Main results

* `maddCallModel_add`, `maddCallModel_sub`: the two `FieldCallee` instances.
* `maddCallModel_mul`, `maddCallModel_join`: the value, frame and `%rsp` statements of the
  other two callees, under the separation of their cells.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof

open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT
  (mulSym addSym subSym join16Sym)

/-- The state with `%rsp` set to `v`. -/
def atRsp (sa : AState) (v : BitVec 64) : AState :=
  { sa with regs := fun r => if r = "%rsp" then v else sa.regs r }

@[simp] theorem atRsp_mem (sa : AState) (v : BitVec 64) : (atRsp sa v).mem = sa.mem := rfl

theorem atRsp_regs (sa : AState) (v : BitVec 64) (r : String) (hr : r ≠ "%rsp") :
    (atRsp sa v).regs r = sa.regs r := by simp [atRsp, hr]

@[simp] theorem atRsp_rsp (sa : AState) (v : BitVec 64) : (atRsp sa v).regs "%rsp" = v := by
  simp [atRsp]

/-- The state a call leaves: the callee's block run with `%rsp` at the callee's own frame,
    `sa.regs "%rsp" + d`, and `%rsp` restored on return. -/
def callBlock (blk : List (JInstr 64)) (d : Int) (sa : AState) : AState :=
  atRsp (runBlockA (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d)) blk) (sa.regs "%rsp")

theorem callBlock_mem (blk : List (JInstr 64)) (d : Int) (sa : AState) :
    (callBlock blk d sa).mem
      = (runBlockA (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d)) blk).mem := rfl

theorem callBlock_rsp (blk : List (JInstr 64)) (d : Int) (sa : AState) :
    (callBlock blk d sa).regs "%rsp" = sa.regs "%rsp" := by simp [callBlock]

/-- The call model of the shipped mixed addition: each callee symbol at the shipped block
    of that function, run on the callee's frame. The field leaves run eight bytes below the
    caller's `%rsp`, the return address of the call; the concatenation runs another 112
    bytes below, the stack its body allocates. -/
def maddCallModel : ACallModel := fun f sa =>
  if f = addSym then callBlock Fe25519AddShipped.fe25519AddShippedBlock (-8) sa
  else if f = subSym then callBlock Fe25519SubShipped.fe25519SubShippedBlock (-8) sa
  else if f = mulSym then callBlock Fe25519MulShipped.fe25519MulShippedBlock (-8) sa
  else if f = join16Sym then
    callBlock Ed25519Join16Shipped.ed25519Join16ShippedBlock (-120) sa
  else sa

theorem maddCallModel_addSym (sa : AState) :
    maddCallModel addSym sa = callBlock Fe25519AddShipped.fe25519AddShippedBlock (-8) sa := by
  simp [maddCallModel]

theorem maddCallModel_subSym (sa : AState) :
    maddCallModel subSym sa = callBlock Fe25519SubShipped.fe25519SubShippedBlock (-8) sa := by
  simp [maddCallModel, addSym, subSym]

theorem maddCallModel_mulSym (sa : AState) :
    maddCallModel mulSym sa = callBlock Fe25519MulShipped.fe25519MulShippedBlock (-8) sa := by
  simp [maddCallModel, addSym, subSym, mulSym]

theorem maddCallModel_joinSym (sa : AState) :
    maddCallModel join16Sym sa
      = callBlock Ed25519Join16Shipped.ed25519Join16ShippedBlock (-120) sa := by
  simp [maddCallModel, addSym, subSym, mulSym, join16Sym]

/-- **The shipped `fe25519_add` meets the callee specification of the mixed addition.** -/
theorem maddCallModel_add : FieldCallee maddCallModel addSym (fun x y => x + y) := by
  intro sa
  have h := addShipped_correct_addr (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8)))
  rw [atRsp_mem] at h
  rw [atRsp_regs _ _ "%rdi" (by decide), atRsp_regs _ _ "%rsi" (by decide),
    atRsp_regs _ _ "%rdx" (by decide)] at h
  obtain ⟨hv, hf, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [maddCallModel_addSym, callBlock_mem]; exact hv
  · rw [maddCallModel_addSym, callBlock_mem]; exact hf
  · rw [maddCallModel_addSym]; exact callBlock_rsp _ _ _

/-- **The shipped `fe25519_sub` meets the callee specification of the mixed addition.** -/
theorem maddCallModel_sub : FieldCallee maddCallModel subSym (fun x y => x + (pM - y)) := by
  intro sa
  have h := subShipped_correct_addr (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8)))
  rw [atRsp_mem] at h
  rw [atRsp_regs _ _ "%rdi" (by decide), atRsp_regs _ _ "%rsi" (by decide),
    atRsp_regs _ _ "%rdx" (by decide)] at h
  obtain ⟨hv, hf, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [maddCallModel_subSym, callBlock_mem]; exact hv
  · rw [maddCallModel_subSym, callBlock_mem]; exact hf
  · rw [maddCallModel_subSym]; exact callBlock_rsp _ _ _

/-- **The shipped `fe25519_mul` at the call model.** With the argument buffers and the
    callee's red-zone slots pairwise disjoint, the call leaves the product modulo
    `2 ^ 255 - 19` at `%rdi`, changes no byte outside those 32 bytes and the 48 bytes below
    the callee's `%rsp`, and keeps `%rsp`. -/
theorem maddCallModel_mul (sa : AState)
    (hsep : Separated shippedBank
      (mulP (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8)))) mulCells) :
    feO (maddCallModel mulSym sa).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 * feO sa.mem (sa.regs "%rdx") 0 % pM
      ∧ FrameCRed sa.mem (maddCallModel mulSym sa).mem (sa.regs "%rdi") 4
          (sa.regs "%rsp" + BitVec.ofInt 64 (-8)) 6
      ∧ (maddCallModel mulSym sa).regs "%rsp" = sa.regs "%rsp" := by
  have h := mulShipped_correct_addr (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8))) hsep
  rw [atRsp_mem] at h
  rw [atRsp_regs _ _ "%rdi" (by decide), atRsp_regs _ _ "%rsi" (by decide),
    atRsp_regs _ _ "%rdx" (by decide), atRsp_rsp] at h
  obtain ⟨hv, hf, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [maddCallModel_mulSym, callBlock_mem]; exact hv
  · rw [maddCallModel_mulSym, callBlock_mem]; exact hf
  · rw [maddCallModel_mulSym]; exact callBlock_rsp _ _ _

/-- **The shipped `ed25519_join16` at the call model.** With the argument buffers, the
    output block and the callee's stack slots pairwise disjoint, the call leaves the four
    input field elements in the four consecutive field slots at `%rdi`, changes no byte
    outside those 128 bytes and its own stack slots, and keeps `%rsp`. -/
theorem maddCallModel_join (sa : AState)
    (hsep : Separated shippedBank
      (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-120))).regs joinCells) :
    (feO (maddCallModel join16Sym sa).mem (sa.regs "%rdi") 0 = feO sa.mem (sa.regs "%rsi") 0
      ∧ feO (maddCallModel join16Sym sa).mem (sa.regs "%rdi") 32
          = feO sa.mem (sa.regs "%rdx") 0
      ∧ feO (maddCallModel join16Sym sa).mem (sa.regs "%rdi") 64
          = feO sa.mem (sa.regs "%rcx") 0
      ∧ feO (maddCallModel join16Sym sa).mem (sa.regs "%rdi") 96
          = feO sa.mem (sa.regs "%r8") 0)
      ∧ FrameCJoin sa.mem (maddCallModel join16Sym sa).mem (sa.regs "%rdi")
          (sa.regs "%rsp" + BitVec.ofInt 64 (-120))
      ∧ (maddCallModel join16Sym sa).regs "%rsp" = sa.regs "%rsp" := by
  have h := joinShipped_correct_addr (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-120))) hsep
  rw [atRsp_mem] at h
  rw [atRsp_regs _ _ "%rdi" (by decide), atRsp_regs _ _ "%rsi" (by decide),
    atRsp_regs _ _ "%rdx" (by decide), atRsp_regs _ _ "%rcx" (by decide),
    atRsp_regs _ _ "%r8" (by decide), atRsp_rsp] at h
  obtain ⟨hv, hf, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [maddCallModel_joinSym, callBlock_mem]; exact hv
  · rw [maddCallModel_joinSym, callBlock_mem]; exact hf
  · rw [maddCallModel_joinSym]; exact callBlock_rsp _ _ _

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
