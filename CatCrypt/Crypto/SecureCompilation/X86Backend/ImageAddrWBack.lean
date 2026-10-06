/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCellsLoop

@[expose] public section

set_option autoImplicit false

/-!
# The image simulation with carry chains at a branch with one-bit names

The relation `ImageAddrSimW.ImgRelW` is monotone in the width analysis
`ImageAddrSimW.oneBitAt`: a larger analysis constrains fewer widths. A taken branch from
position `k` to the label at position `p` therefore keeps `ImgRelW` when every name of the
analysis at `k` is a name of the analysis one past the label, `p + 1`.
`ImageAddrSimW.gateAtW` checks that inclusion at a branch. This module states the inclusion
as the property `BranchW` of a body and as the gate `imgGateBW'`, which reads the branch
form directly, and gives the step of the image at a branch from each.

## Main definitions

* `BranchW`: the branches of a body before its last position are on a condition code with a
  polarity, to a label of the body, and the width analysis at the branch is included in the
  analysis one past the label.
* `gateAtW'`, `instrGateBW'`, `imgGateBW'`: the gate `ImageAddrSimW.imgGateBW` with the
  inclusion at a branch read off the branch instruction.

## Main results

* `rel_fallW`, `rel_jumpW`: a branch not taken, and a branch taken under the inclusion, keep
  `ImgRelW` (`ImageAddrSimW.rel_condFallW`, `ImageAddrSimW.rel_condJumpW`).
* `condStep_of_branchW`: `ImageAddrCellsLoop.ImgStepWCond` from `BranchW`.
* `imgGateBW'_of`: `imgGateBW` gives `imgGateBW'`.
* `branchW_of_gate'`, `imgStepWCond_of_gate'`: `imgGateBW'` gives `BranchW` and
  `ImgStepWCond`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrWBack

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel isLabel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (isRetB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCellsLoop (CondStep ImgStepWCond)

/-! ## 1. A branch keeps the relation -/

/-- **A branch not taken keeps `ImgRelW`.** -/
theorem rel_fallW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {cc : String} {l : LLabel}
    (hx : bi.li_i = .Lcond (.reg cc) l) :
    ImgRelW frame slotArr base body
      { s with prog := { s.prog with base := s.prog.base.nextPc } }
      (sa.setLpc (sa.reg.lpc + 1)) zf :=
  rel_condFallW hphys hrel hb hx

/-- **A branch taken keeps `ImgRelW`** where the width analysis at the branch is included in
    the analysis one past the label: the image jumps one past the label, the address machine
    to the label and then over it. -/
theorem rel_jumpW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (hphys : physImgB slotArr body = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hnm : slotMov? bi.li_i = none) {p : Nat}
    {bp : Linstr} (hbp : body[p]? = some bp) (hpl : slotMov? bp.li_i = none)
    (hpx : ∀ ds o ss, bp.li_i ≠ .Lopn ds o ss)
    (hW : ∀ r, r ∈ oneBitAt frame body sa.reg.lpc → r ∈ oneBitAt frame body (p + 1)) :
    ImgRelW frame slotArr base body
      { s with prog := { s.prog with base := s.prog.base.setLpc (p + 1) } }
      (sa.setLpc (p + 1)) zf :=
  rel_condJumpW hphys hrel hb hnm hbp hpl hpx hW

/-! ## 2. The step at a branch -/

/-- **The branches of a body under the width analysis**: every conditional branch before the
    last position is on a condition code with a polarity, to a label of the body, and every
    name of the width analysis at the branch is a name of the analysis one past the label. -/
def BranchW (frame : String → Option (BitVec 64)) (c : Lcmd) : Prop :=
  ∀ (k : Nat) (bi : Linstr) (cnd : _) (l : LLabel), c[k]? = some bi → k < c.length - 1 →
    bi.li_i = .Lcond cnd l →
    ∃ cc pol p, cnd = .reg cc ∧ condPol cc = some pol ∧ labelAt c l = some p
      ∧ ∀ r, r ∈ oneBitAt frame c k → r ∈ oneBitAt frame c (p + 1)

/-- **The step of the image with carry chains at a conditional branch, from `BranchW`**, for
    a body that ends in the return. -/
theorem condStep_of_branchW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} (rsp : BitVec 64)
    {c : Lcmd} (hphys : physImgB slotArr c = true)
    (hlast : ∃ r, c.getLast? = some r ∧ r.li_i = .Lret) (hbr : BranchW frame c)
    (fn : String) : ImgStepWCond frame slotArr base rsp c fn := by
  intro s t sa bi cnd l hrel hb hlt hc hstep
  obtain ⟨cc, pol, p, rfl, hpol, hp, hW⟩ := hbr _ bi cnd l hb hlt hc
  exact (img_stepW_cond' (rsp := rsp) hphys hlast fn hrel hb hc hpol hp hW hstep).2

/-! ## 3. The gate -/

/-- **The gate of instruction `k` at the analysis `W`, with one-bit names at a branch**:
    `gateAtW`, except that a branch on a condition code is accepted where the code has a
    polarity and every name of `W` is in the width analysis one past its label. -/
def gateAtW' (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) (W : List String) : LinstrR → Bool
  | .Lcond (.reg cc) l =>
      (condPol cc).isSome && (labelAt body l).any fun p =>
        W.all fun r => (oneBitAt frame body (p + 1)).contains r
  | x => gateAtW frame slotArr body k W x

/-- The gate `gateAtW'` of instruction `k` of a body at its width analysis. -/
def instrGateBW' (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) (x : LinstrR) : Bool :=
  gateAtW' frame slotArr body k (oneBitAt frame body k) x

/-- **The gate of the image simulation with carry chains and one-bit names at a branch**:
    `imgGateBW` with `instrGateBW'` at every instruction but the last. -/
def imgGateBW' (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) : Bool :=
  (List.range (body.length - 1)).all (fun k =>
      (body[k]?).all fun i => instrGateBW' frame slotArr body k i.li_i)
    && body.getLast?.any (fun r => isRetB r.li_i)
    && reloadSavedB slotArr body

/-- The facts of `gateAtW'` at a branch. -/
theorem gateAtW'_cond {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {c : Lcmd} {k : Nat} {W : List String}
    {cnd : _} {l : LLabel} (hg : gateAtW' frame slotArr c k W (.Lcond cnd l) = true) :
    ∃ cc pol p, cnd = .reg cc ∧ condPol cc = some pol ∧ labelAt c l = some p
      ∧ ∀ r, r ∈ W → r ∈ oneBitAt frame c (p + 1) := by
  cases cnd with
  | reg cc =>
      simp only [gateAtW', Bool.and_eq_true, Option.isSome_iff_exists, Option.any_eq_true,
        List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hg
      obtain ⟨⟨pol, hpol⟩, p, hp, hW⟩ := hg
      exact ⟨cc, pol, p, rfl, hpol, hp, hW⟩
  | _ =>
      obtain ⟨cc, pol, p, hcc, -, -, -⟩ := gateAtW_cond (slotArr := slotArr) (c := c) (k := k)
        (W := W) rfl (show gateAtW frame slotArr c k W _ = true from hg)
      cases hcc

/-- `gateAtW` gives `gateAtW'`. -/
theorem gateAtW'_of {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {x : LinstrR} (h : gateAtW frame slotArr body k W x = true) :
    gateAtW' frame slotArr body k W x = true := by
  unfold gateAtW'
  split
  · rename_i cc l
    obtain ⟨cc', pol, p, hcc, hpol, hp, hW⟩ := gateAtW_cond rfl h
    cases hcc
    simpa [hpol, hp] using hW
  · exact h

/-- **`imgGateBW` gives `imgGateBW'`.** -/
theorem imgGateBW'_of {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateBW frame slotArr body = true) : imgGateBW' frame slotArr body = true := by
  simp only [imgGateBW, imgGateBW', Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨⟨fun k hk => ?_, h.1.2⟩, h.2⟩
  have := h.1.1 k hk
  cases hb : body[k]? with
  | none => rfl
  | some i =>
      rw [hb] at this
      exact gateAtW'_of (by simpa [instrGateBW] using this)

/-- A body passing `imgGateBW'` ends in the return. -/
theorem imgGateBW'_last {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateBW' frame slotArr body = true) :
    ∃ r, body.getLast? = some r ∧ r.li_i = .Lret := by
  simp only [imgGateBW', Bool.and_eq_true] at h
  obtain ⟨⟨-, h2⟩, -⟩ := h
  cases hl : body.getLast? with
  | none => rw [hl] at h2; cases h2
  | some r =>
      rw [hl] at h2
      simp only [Option.any_some] at h2
      refine ⟨r, rfl, ?_⟩
      revert h2
      cases r.li_i <;> simp [isRetB]

/-- **`imgGateBW'` gives `BranchW`.** -/
theorem branchW_of_gate' {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {c : Lcmd}
    (hgate : imgGateBW' frame slotArr c = true) : BranchW frame c := by
  intro k bi cnd l hb hlt hc
  simp only [imgGateBW', Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
  have hg := hgate.1.1 k hlt
  rw [hb] at hg
  simp only [Option.all_some, instrGateBW', hc] at hg
  exact gateAtW'_cond hg

/-- **The step of the image with carry chains at a conditional branch, from `imgGateBW'`.** -/
theorem imgStepWCond_of_gate' {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} (rsp : BitVec 64)
    {c : Lcmd} (hphys : physImgB slotArr c = true)
    (hgate : imgGateBW' frame slotArr c = true) (fn : String) :
    ImgStepWCond frame slotArr base rsp c fn :=
  condStep_of_branchW rsp hphys (imgGateBW'_last hgate) (branchW_of_gate' hgate) fn

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrWBack
