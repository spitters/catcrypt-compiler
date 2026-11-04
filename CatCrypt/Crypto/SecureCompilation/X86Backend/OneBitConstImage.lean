/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold

@[expose] public section

set_option autoImplicit false

/-!
# The image of a one-bit constant and the guards of a select on it

A branch on a condition known at compile time, and a length guard on an array whose length the
types fix, reach the export code as a one-bit immediate move `MOV^1 r, #n` (tagged with the
one-bit descriptor `cast 1`) followed by a select `CMOV x, [r, a, b]` on it. The register
allocation keeps the move as `MOV^1 R, #n` in the printed body. The check `ownedCheckMC` of
`compileRegion` compares the export code with the image of the printed body (`virtImg`), and
the symbolic step of the select guards its condition with the width `1`
(`OwnedLprogTV.symN`). The image tags an immediate move of `0` or `1` with the one-bit
descriptor exactly when it is a one-bit constant (`JasminLsemAddrRun.bitMovB`): its next use
reads its destination only as a one-bit value, as a carry-in or as the condition of a select.

When the one-bit name is spilled, the allocation stores it into its frame word with
`MOV^1 k, #n` and reads it back into a scratch register with the copy `MOV:64 R, k` before the
select. The constant-index fold (`ConstIndexFold.foldTarget?`) does not record the
destination of an immediate move with a narrow width in its mnemonic
(`ConstIndexFold.narrowImmDsts`), so it leaves this copy a copy instead of writing
`MOV:64 R, #n`, a 64-bit move of the bit; and the image reads a move written `MOV^1` at the
one-bit tag whatever its next use (`JasminLsemAddrRun.oneBitMnemB`).

This module states the completeness of the check at this construct, for every body: the image
of a one-bit constant is its move at the one-bit tag; the move at the one-bit tag, on either
side, steps to the one-bit immediate with no guard; and the width guard of a select on a
one-bit immediate adds no obligation to the guard check `guardsT` of `ownedCheckMC`. Before
`bitMovB` admitted the select condition, the image read such a move at the width `32` of an
untagged move, and the guard of the select normalised to the false guard, which no reference
guard matches.

## Main results

* `bitInNext_of_cond`: a move into `d` followed by a select reading `d` only as its condition
  has a one-bit next use.
* `bitMovB_of_cond`: an immediate move of `0` or `1` into a name that is no cell name, followed
  by such a select, is a one-bit constant.
* `bitMovB_of_oneBitMnem`: a move of `0` or `1` written `MOV^1` into a name that is no cell
  name is a one-bit constant.
* `nextEnv_find_narrow`, `foldTarget?_copy_of_narrow`: after a narrow immediate move into `d`
  the fold knows no value of `d`, and a following 64-bit copy of `d` stays a copy.
* `imgInstr_oneBit`: the image of a one-bit constant is its move at the one-bit tag.
* `symStep_oneBit`: an immediate move at the one-bit tag steps to the one-bit immediate with no
  guard; the reference move and the image move have one term.
* `guardsT_oneBit`: the width guard of a select on a one-bit immediate adds no obligation to
  `guardsT`.
* `guardsT_img_oneBit`: the guards of the image of a one-bit constant followed by a select on
  it pass `guardsT` whenever the guards of the values of the select do.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OneBitConstImage

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (isMovImmMnem movImmStruct?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-- A move into `d` at position `k`, followed at `k + 1` by a select `CMOV x, [d, a, b]` that
    reads `d` only as its condition, has a one-bit next use. -/
theorem bitInNext_of_cond {body : Lcmd} {k : Nat} {d : String} {l : Linstr}
    (hl : body[k + 1]? = some l) (hc : condUseB d l.li_i = true) :
    bitInNext body k d = true := by
  have hlt : k + 1 < body.length := (List.getElem?_eq_some_iff.mp hl).1
  have e : body[k + 1] = l := (List.getElem?_eq_some_iff.mp hl).2
  simp [bitInNext, List.drop_eq_getElem_cons hlt, e, useFirst, bitUseB, hc]

/-- An immediate move `o d, #n` (`o` an immediate-move mnemonic other than the 64-bit one) of
    `0` or `1` into a name that is no cell name, followed by a select reading `d` only as its
    condition, is a one-bit constant. -/
theorem bitMovB_of_cond {body : Lcmd} {k : Nat} {d o : String} {n : Nat} {l : Linstr}
    (ho : isMovImmMnem o = true) (hn : n < 2) (hd : hasPrefix d "mem." = false)
    (hl : body[k + 1]? = some l) (hc : condUseB d l.li_i = true) :
    bitMovB body k (.Lopn [.reg d] o [.imm n]) = true := by
  simp [bitMovB, movImmStruct?, ho, hn, hd, bitInNext_of_cond hl hc]

/-- A move of `0` or `1` written with the one-bit mnemonic `MOV^1` into a name that is no cell
    name is a one-bit constant, whatever its next use. -/
theorem bitMovB_of_oneBitMnem {body : Lcmd} {k : Nat} {d : String} {n : Nat} (hn : n < 2)
    (hd : hasPrefix d "mem." = false) :
    bitMovB body k (.Lopn [.reg d] (withWidthTag 1 "MOV") [.imm n]) = true := by
  have ho : isMovImmMnem (withWidthTag 1 "MOV") = true :=
    JasminLsemCast.isMovImmMnem_iff.mpr (Or.inr ⟨1, by decide, rfl⟩)
  simp [bitMovB, movImmStruct?, ho, hn, hd, oneBitMnemB]

open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold in
/-- **The fold forgets a narrow constant**: after an immediate move `o d, #n` whose mnemonic
    carries a width (`MOV^w`), the environment of the constant-index fold has no value of `d`.
-/
theorem nextEnv_find_narrow (p : Nat × Nat × Nat) (env : KEnv) {i : Linstr} {d o : String}
    {n : Nat} (hi : i.li_i = .Lopn [.reg d] o [.imm n])
    (ho : List.isPrefixOf "MOV^".toList o.toList = true) : (nextEnv p env i).find d = none := by
  have hr : JInstrGatherExtended.isLret i = false := by
    simp [JInstrGatherExtended.isLret, hi]
  have hk : ∀ (e : KEnv) (ds : List String), d ∈ ds → (e.killAll ds).find d = none := by
    intro e ds hd
    cases hf : (e.killAll ds).find d with
    | none => rfl
    | some v => exact absurd hd (KEnv.find_killAll hf).2
  unfold nextEnv
  rw [hr]
  simp only [Bool.false_eq_true, ite_false]
  split
  · exact hk _ _ (by rw [hi]; simp only [narrowImmDsts, ho, ite_true, List.mem_singleton])
  · rw [hi]
    exact hk _ _ (by simp [dstOpNames])

open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold in
/-- **A copy of a narrow constant stays a copy**: the 64-bit copy `MOV:64 R, d` right after a
    narrow immediate move into `d` is not rewritten by the fold, so it reads the value of `d` at
    the width of that move. -/
theorem foldTarget?_copy_of_narrow (p : Nat × Nat × Nat) (env : KEnv) {i : Linstr}
    {d o R : String} {n : Nat} (hi : i.li_i = .Lopn [.reg d] o [.imm n])
    (ho : List.isPrefixOf "MOV^".toList o.toList = true) :
    foldTarget? (nextEnv p env i) (.Lopn [.reg R] "MOV:64" [.reg d]) = none := by
  simp [foldTarget?, nextEnv_find_narrow p env hi ho]

/-- **The image of a one-bit constant** is its move at the one-bit tag. -/
theorem imgInstr_oneBit (slotArr : String → Option (String × Nat)) {body : Lcmd} {k : Nat}
    {d o : String} {n : Nat} (ho : isMovImmMnem o = true)
    (hb : bitMovB body k (.Lopn [.reg d] o [.imm n]) = true) :
    imgInstr slotArr body k (.Lopn [.reg d] o [.imm n])
      = (normA (.Lopn [.reg d] o [.imm n]), .reg (some 1)) := by
  have h64 : o ≠ "MOV:64" := by
    rintro rfl
    exact absurd ho (by decide)
  have hs : bitStore? body k (.Lopn [.reg d] o [.imm n]) = none := by
    simp [bitStore?, h64]
  simp [imgInstr, hs, cellIdxStore?, arrImmImg, baseReload?, tagAt, hb]

/-- **The step of an immediate move at the one-bit tag**: the move `o d, #n` of an
    immediate-move mnemonic `o`, at the one-bit descriptor `.reg (some 1)`, sets `d` to the
    one-bit immediate `immW 1 n` with no guard, from every state. The reference move
    `MOV^1 r, #n` tagged `cast 1` and the image of a one-bit constant have this step. -/
theorem symStep_oneBit {d o : String} {n : Nat} (ho : isMovImmMnem o = true) (ss : SSt) :
    symStep (.Lopn [.reg d] o [.imm n], .reg (some 1)) ss = .ok (ss.setR d (.immW 1 n)) [] := by
  have hc : ∀ R, symCast (.Lopn [.reg d] o [.imm n], some 1) R = .set d (.immW 1 n) [] :=
    fun R => by
      simp only [symCast, JasminLsemCast.castStruct?, movImmStruct?, ite_eq_left ho]
  simp [symStep, cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?, symMem, hc, liftR,
    aluFl, aluFlT, aluFlagOp?, SSt.setR]

/-- **The width guard of a select on a one-bit immediate adds no obligation**: inserted
    anywhere among the guards of the allocated block, the guard that the one-bit immediate
    `immW 1 b` has width `1` leaves `guardsT` unchanged. -/
theorem guardsT_oneBit (E : Array TEnt) (L : List String × Bool) (gs gs₁ gs₂ : List SG)
    (b : Nat) :
    guardsT E L gs (gs₁ ++ .wid (.immW 1 b) 1 :: gs₂) = guardsT E L gs (gs₁ ++ gs₂) := by
  simp [guardsT, normGT, List.flatMap_append, SG.normT, STerm.wbkT, SG.refsLt, STerm.refsLt,
    List.all_append]

/-- **Completeness of `guardsT` at a select on a one-bit constant.** If an allocated block
    holds the image of a one-bit constant into `c` and then a select `CMOV x, [c, a, b]`, so
    that its guards are those `gs₁` before the select, the width guard of the condition, which
    is the one-bit immediate (`symStep_oneBit`), and the guards `gs₂` after it, then the block
    passes `guardsT` against the reference guards `gs` exactly when its guards without the
    condition guard do. -/
theorem guardsT_img_oneBit (E : Array TEnt) (L : List String × Bool) (gs gs₁ gs₂ : List SG)
    {d o : String} {n : Nat} (ho : isMovImmMnem o = true) (ss : SSt)
    (hg : guardsT E L gs (gs₁ ++ gs₂) = true) :
    symStep (.Lopn [.reg d] o [.imm n], .reg (some 1)) ss = .ok (ss.setR d (.immW 1 n)) [] ∧
      guardsT E L gs (gs₁ ++ .wid ((ss.setR d (.immW 1 n)).regs d) 1 :: gs₂) = true := by
  refine ⟨symStep_oneBit ho ss, ?_⟩
  simpa [SSt.setR, guardsT_oneBit] using hg

end CatCrypt.Crypto.SecureCompilation.X86Backend.OneBitConstImage
