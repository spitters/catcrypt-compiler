/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedFrame
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PackSignLeaf

/-!
# The call model of the shipped `ed25519_compress`

`Imported.Ed25519CompressShipped.ed25519CompressShippedBlock` calls `ed25519_invert`,
`fe25519_mul` twice, and `ed25519_pack_sign`. `compressCallModel` sends each callee symbol
to the shipped block of that function, run on the callee's frame below the caller's `%rsp`
with `%rsp` and the callee-saved registers at their values at the call; the inversion runs
its own segments over `Ed25519InvertShippedProof.invertCallModel`.

## Main definitions

* `callSegsSaved`: the state a call to a function with calls leaves.
* `compressCallModel`: the call model.
* `InvEffect`, `PackSep`, `PackEffect`, `CompressCallees`: the callee specifications.

## Main results

* `compressCallModel_inv`, `compressCallModel_mul`, `compressCallModel_pack`,
  `compressCallees_compressCallModel`: the three shipped callees meet their
  specifications.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519CompressShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT
  (mulSym sqrSym invertSym packSignSym)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PackSignLeaf

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (calleeSavedRegs)

/-! ## The call model -/

/-- The state a call to a function with calls leaves: the callee's segments run over `C`
    on the callee's frame, with `%rsp` and the callee-saved registers at their values at
    the call. -/
def callSegsSaved (C : ACallModel) (blk : List CallSeg) (d : Int) (sa : AState) : AState :=
  { regs := fun r => if r ∈ "%rsp" :: calleeSavedRegs then sa.regs r
      else (segsRunA C (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d)) blk).regs r
    flags := (segsRunA C (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d)) blk).flags
    mem := (segsRunA C (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d)) blk).mem }

/-- The call model of the shipped compression: `ed25519_invert` at its shipped block over
    the call model of the inversion, on the frame 192 bytes below the caller's `%rsp` (the
    return address, the saved `%rbx` and the 176 bytes the inversion allocates);
    `fe25519_mul` at its shipped block eight bytes below; `ed25519_pack_sign` at its shipped
    block 72 bytes below (the return address and the 64 bytes it allocates). -/
def compressCallModel : ACallModel := fun f sa =>
  if f = invertSym then
    callSegsSaved invertCallModel Ed25519InvertShipped.ed25519InvertShippedBlock (-192) sa
  else if f = mulSym then callBlockSaved Fe25519MulShipped.fe25519MulShippedBlock (-8) sa
  else if f = packSignSym then
    callBlockSaved Ed25519PackSignShipped.ed25519PackSignShippedBlock (-72) sa
  else sa

theorem compressCallModel_invertSym (sa : AState) :
    compressCallModel invertSym sa = callSegsSaved invertCallModel
      Ed25519InvertShipped.ed25519InvertShippedBlock (-192) sa := by
  simp [compressCallModel]

theorem compressCallModel_mulSym (sa : AState) :
    compressCallModel mulSym sa = invertCallModel mulSym sa := by
  simp [compressCallModel, invertCallModel, invertSym, mulSym, sqrSym]

theorem compressCallModel_packSignSym (sa : AState) :
    compressCallModel packSignSym sa
      = callBlockSaved Ed25519PackSignShipped.ed25519PackSignShippedBlock (-72) sa := by
  simp [compressCallModel, invertSym, mulSym, packSignSym]

/-! ## The callee specifications -/

/-- A call keeps `%rsp`, `%rbx` and `%r12`. -/
def KeepsRegs (C : ACallModel) (f : String) (sa : AState) : Prop :=
  (C f sa).regs "%rsp" = sa.regs "%rsp" ∧ (C f sa).regs "%rbx" = sa.regs "%rbx"
    ∧ (C f sa).regs "%r12" = sa.regs "%r12"

/-- The effect of an inversion call at one state: the input at `%rsi` raised to
    `2 ^ 255 - 21` modulo `2 ^ 255 - 19` at `%rdi`, no memory outside the inversion frame
    192 bytes below `%rsp` and the 32 bytes at `%rdi`, and the saved registers kept. -/
def InvEffect (C : ACallModel) (f : String) (sa : AState) : Prop :=
  feO (C f sa).mem (sa.regs "%rdi") 0 = feO sa.mem (sa.regs "%rsi") 0 ^ (pM - 2) % pM
    ∧ InvertFrame sa.mem (C f sa).mem (sa.regs "%rsp" + BitVec.ofInt 64 (-192))
        (sa.regs "%rdi")
    ∧ KeepsRegs C f sa

/-- The buffers of a pack call: the output at `%rdi`, the four words at `%rsi`, the word
    at `%rdx`, and the stack slots from `%rsp - 80` to `%rsp - 16` are pairwise disjoint. -/
structure PackSep (sa : AState) : Prop where
  /-- The output and the first input. -/
  oi : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsi") 0 24
  /-- The output and the second input. -/
  od : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rdx") 0 0
  /-- The two inputs. -/
  id : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rdx") 0 0
  /-- The output and the stack slots. -/
  os : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-80) (-16)
  /-- The first input and the stack slots. -/
  is : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-80) (-16)
  /-- The second input and the stack slots. -/
  ds : RangeDisj (sa.regs "%rdx") 0 0 (sa.regs "%rsp") (-80) (-16)

/-- The effect of a pack call at one state: the four words at `%rsi` at `%rdi`, with the
    low bit of the word at `%rdx` added into the top bit of the fourth. -/
def PackEffect (C : ACallModel) (f : String) (sa : AState) : Prop :=
  (∀ j ∈ [(0 : Int), 8, 16],
      read64 (C f sa).mem (sa.regs "%rdi" + BitVec.ofInt 64 j)
        = read64 sa.mem (sa.regs "%rsi" + BitVec.ofInt 64 j))
    ∧ read64 (C f sa).mem (sa.regs "%rdi" + BitVec.ofInt 64 24)
      = read64 sa.mem (sa.regs "%rsi" + BitVec.ofInt 64 24)
        + (read64 sa.mem (sa.regs "%rdx" + BitVec.ofInt 64 0) &&& 1) <<< 63

/-- The three callees of the compression at their specifications. -/
structure CompressCallees (C : ACallModel) : Prop where
  /-- `ed25519_invert` inverts, at every state whose input is reduced and disjoint from
      the inversion frame. -/
  inv : ∀ sa, ChainSep (sa.regs "%rsp" + BitVec.ofInt 64 (-192)) (sa.regs "%rsi") →
    feO sa.mem (sa.regs "%rsi") 0 < pM → InvEffect C invertSym sa
  /-- `fe25519_mul` multiplies modulo `pM`, at every state whose arguments lie outside
      the words below `%rsp`, and keeps `%r12`. -/
  mul : ∀ sa, ArgsBelowSep sa →
    MulEffect C mulSym sa ∧ (C mulSym sa).regs "%r12" = sa.regs "%r12"
  /-- `ed25519_pack_sign` packs, at every state whose buffers are disjoint. -/
  pack : ∀ sa, PackSep sa → PackEffect C packSignSym sa

theorem callSegsSaved_mem (C : ACallModel) (blk : List CallSeg) (d : Int) (sa : AState) :
    (callSegsSaved C blk d sa).mem
      = (segsRunA C (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d)) blk).mem := rfl

theorem callSegsSaved_saved (C : ACallModel) (blk : List CallSeg) (d : Int) (sa : AState)
    (r : String) (hr : r ∈ "%rsp" :: calleeSavedRegs) :
    (callSegsSaved C blk d sa).regs r = sa.regs r := by
  simp only [callSegsSaved, if_pos hr]

theorem callBlockSaved_saved (blk : List (JInstr 64)) (d : Int) (sa : AState)
    (r : String) (hr : r ∈ "%rsp" :: calleeSavedRegs) :
    (callBlockSaved blk d sa).regs r = sa.regs r := by
  simp only [callBlockSaved, if_pos hr]

/-- **The shipped `ed25519_invert` meets the inversion specification of the compression.** -/
theorem compressCallModel_inv (sa : AState)
    (hsep : ChainSep (sa.regs "%rsp" + BitVec.ofInt 64 (-192)) (sa.regs "%rsi"))
    (hz : feO sa.mem (sa.regs "%rsi") 0 < pM) : InvEffect compressCallModel invertSym sa := by
  set sb := atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-192)) with hsb
  have e_rsi : sb.regs "%rsi" = sa.regs "%rsi" := atRsp_regs _ _ _ (by decide)
  have e_rdi : sb.regs "%rdi" = sa.regs "%rdi" := atRsp_regs _ _ _ (by decide)
  have hsep' : ChainSep (sb.regs "%rsp") (sb.regs "%rsi") := by
    rw [e_rsi, hsb, atRsp_rsp]; exact hsep
  have hz' : feO sb.mem (sb.regs "%rsi") 0 < pM := by rw [e_rsi, hsb, atRsp_mem]; exact hz
  have hv := invertShipped_correct sb hsep' hz'
  have hf := invertShipped_frame invertCallees_invertCallModel sb hsep' hz'
  rw [e_rsi, e_rdi, hsb, atRsp_mem] at hv
  rw [e_rdi, hsb, atRsp_mem, atRsp_rsp] at hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [compressCallModel_invertSym, callSegsSaved_mem]; exact hv
  · rw [compressCallModel_invertSym, callSegsSaved_mem]; exact hf
  · rw [compressCallModel_invertSym]; exact callSegsSaved_saved _ _ _ _ _ (by decide)
  · rw [compressCallModel_invertSym]; exact callSegsSaved_saved _ _ _ _ _ (by decide)
  · rw [compressCallModel_invertSym]; exact callSegsSaved_saved _ _ _ _ _ (by decide)

/-- **The shipped `fe25519_mul` meets the multiply specification of the compression.** -/
theorem compressCallModel_mul (sa : AState) (hsp : ArgsBelowSep sa) :
    MulEffect compressCallModel mulSym sa
      ∧ (compressCallModel mulSym sa).regs "%r12" = sa.regs "%r12" := by
  have h := invertCallModel_mul sa hsp
  unfold MulEffect at h ⊢
  rw [compressCallModel_mulSym]
  refine ⟨h, ?_⟩
  rw [invertCallModel_mulSym]
  exact callBlockSaved_saved _ _ _ _ (by decide)

/-- A range of cells at a displacement `d` of a base, read as a range at the base. -/
theorem rangeDisj_shift {a sp : BitVec 64} {lo hi u v : Int} (d : Int) (hd : d % 8 = 0)
    (h : RangeDisj a lo hi sp (d + u) (d + v)) :
    RangeDisj a lo hi (sp + BitVec.ofInt 64 d) u v := by
  intro o o' a1 a2 a3 b1 b2 b3
  rw [addI]
  exact h o (d + o') a1 a2 a3 (by omega) (by omega) (by omega)

/-- **The shipped `ed25519_pack_sign` meets the pack specification of the compression.** -/
theorem compressCallModel_pack (sa : AState) (hsep : PackSep sa) :
    PackEffect compressCallModel packSignSym sa := by
  set sb := atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-72)) with hsb
  have e_rsi : sb.regs "%rsi" = sa.regs "%rsi" := atRsp_regs _ _ _ (by decide)
  have e_rdi : sb.regs "%rdi" = sa.regs "%rdi" := atRsp_regs _ _ _ (by decide)
  have e_rdx : sb.regs "%rdx" = sa.regs "%rdx" := atRsp_regs _ _ _ (by decide)
  have e_rsp : sb.regs "%rsp" = sa.regs "%rsp" + BitVec.ofInt 64 (-72) := atRsp_rsp _ _
  have hs : Separated shippedBank sb.regs packCells := by
    refine separated_packCells ?_ ?_ ?_ ?_ ?_ ?_
    · rw [e_rdi, e_rsi]; exact hsep.oi
    · rw [e_rdi, e_rdx]; exact hsep.od
    · rw [e_rsi, e_rdx]; exact hsep.id
    · rw [e_rdi, e_rsp]; exact rangeDisj_shift (-72) (by decide) hsep.os
    · rw [e_rsi, e_rsp]; exact rangeDisj_shift (-72) (by decide) hsep.is
    · rw [e_rdx, e_rsp]; exact rangeDisj_shift (-72) (by decide) hsep.ds
  obtain ⟨h0, h24, -, -⟩ := packSignShipped_correct_addr sb hs
  rw [e_rdi, e_rsi, hsb, atRsp_mem] at h0
  rw [e_rdi, e_rsi, e_rdx, hsb, atRsp_mem] at h24
  refine ⟨?_, ?_⟩
  · rw [compressCallModel_packSignSym, callBlockSaved_mem]; exact h0
  · rw [compressCallModel_packSignSym, callBlockSaved_mem]; exact h24

/-- **The three shipped callees of the compression meet their specifications.** -/
theorem compressCallees_compressCallModel : CompressCallees compressCallModel :=
  ⟨compressCallModel_inv, compressCallModel_mul, compressCallModel_pack⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519CompressShippedProof
