/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OneBitConstImage

/-!
# The image of a spilled carry constant at its carry-in

A one-bit carry constant `MOV^1 r, #n` of the reference whose name the allocation spills is
stored into its frame word as `MOV:64 k, #n` and read back before a later carry-in by the copy
`MOV:64 R, k`, which the next instruction reads as the carry-in of `ADCX:64` or `ADCXHI:64`.
The constant-index fold keeps that copy a copy (`ConstIndexFold.carryCopyB`,
`ConstIndexFold.foldEnv`). The image of the printed body (`virtImg`) reads the store as a
stored carry constant (`JasminLsemAddrImage.bitStore?`), the move of the one-bit immediate
`immW 1 n` into `k`; the copy gives `R` that one-bit immediate with no guard; and the width
guard of the carry-in on `R` adds no obligation to the guard check `guardsT` of
`ownedCheckMC`.

This module states the completeness of the check at this construct: on the printed body the
fold produces, the guards of the image at a carry-in of a spilled carry constant pass
`guardsT` whenever the guards without the carry-in guard do.

## Main results

* `foldCore_carryCopy`: the fold keeps a carry-in reload.
* `symStep_img_bitStore`: the image of a stored carry constant steps to the one-bit immediate
  with no guard.
* `symStep_copy`: a 64-bit copy steps to the value of its source with no guard, at every tag.
* `guardsT_img_carryIn`: completeness of `guardsT` at a carry-in reload of a stored carry
  constant.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OneBitCarryInImage

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold

/-- **The fold keeps a carry-in reload**: at a copy `MOV:64 d, x` whose next instruction reads
    `d` as a carry-in, `foldCore` leaves the instruction unchanged. -/
theorem foldCore_carryCopy (p : Nat × Nat × Nat) (ex : List String) (env : KEnv) {i : Linstr}
    {is : Lcmd} (h : carryCopyB i.li_i is = true) :
    foldCore p ex env (i :: is) = i :: foldCore p ex (nextEnv p env i) is := by
  simp [foldCore, foldInstr_foldEnv_of_carryCopy _ _ h]

/-- **The image of a stored carry constant** `MOV:64 d, #n` steps to the one-bit immediate
    `immW 1 n` in `d` with no guard. -/
theorem symStep_img_bitStore (slotArr : String → Option (String × Nat)) {body : Lcmd}
    {k : Nat} {i : LinstrR} {d : String} {n : Nat} (h : bitStore? body k i = some (d, n))
    (ss : SSt) : symStep (imgInstr slotArr body k i) ss = .ok (ss.setR d (.immW 1 n)) [] := by
  rw [imgInstr_bitStore slotArr h]
  exact OneBitConstImage.symStep_oneBit (by decide) ss

/-- **The step of a 64-bit copy** `MOV:64 R, x`, at every tag, sets `R` to the value of `x`
    with no guard. -/
theorem symStep_copy (R x : String) (t : MemTag) (ss : SSt) :
    symStep (.Lopn [.reg R] "MOV:64" [.reg x], t) ss = .ok (ss.setR R (ss.regs x)) [] := by
  have hw : stripWidthTag "MOV:64" = "MOV" := by decide
  simp [symStep, cmpArgs?, movRegArgs?, hw]

/-- **Completeness of `guardsT` at a carry-in reload of a stored carry constant.** If the
    symbolic state of the allocated block holds the one-bit immediate `immW 1 n` in the frame
    word `x`, the value the image of the stored carry constant gives it
    (`symStep_img_bitStore`), then the copy `MOV:64 R, x` that the fold keeps
    (`foldCore_carryCopy`) gives `R` that immediate with no guard, and the block passes
    `guardsT` against the reference guards `gs` with the width guard of the carry-in on `R`
    exactly when it passes without it. -/
theorem guardsT_img_carryIn (E : Array TEnt) (L : List String × Bool) (gs gs₁ gs₂ : List SG)
    {R x : String} {n : Nat} (t : MemTag) (ss : SSt) (hx : ss.regs x = .immW 1 n)
    (hg : guardsT E L gs (gs₁ ++ gs₂) = true) :
    symStep (.Lopn [.reg R] "MOV:64" [.reg x], t) ss = .ok (ss.setR R (.immW 1 n)) [] ∧
      guardsT E L gs (gs₁ ++ .wid ((ss.setR R (.immW 1 n)).regs R) 1 :: gs₂) = true := by
  refine ⟨by rw [symStep_copy, hx], ?_⟩
  simpa [SSt.setR, OneBitConstImage.guardsT_oneBit] using hg

end CatCrypt.Crypto.SecureCompilation.X86Backend.OneBitCarryInImage
