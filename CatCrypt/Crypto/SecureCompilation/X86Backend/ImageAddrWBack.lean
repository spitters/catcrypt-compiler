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

`ImageAddrSimW.gateAtW` accepts a conditional branch where the width analysis
`ImageAddrSimW.oneBitAt` is empty. The relation `ImageAddrSimW.ImgRelW` is monotone in the
width analysis: a larger analysis constrains fewer widths. A taken branch from position `k` to
the label at position `p` therefore keeps `ImgRelW` when every name of the analysis at `k` is a
name of the analysis one past the label, `p + 1`. This module states the gate with that
inclusion at a branch and proves the step of the image at such a branch.

## Main definitions

* `BranchW`: the branches of a body before its last position are on a condition code with a
  polarity, to a label of the body, and the width analysis at the branch is included in the
  analysis one past the label.
* `gateAtW'`, `instrGateBW'`, `imgGateBW'`: the gate `ImageAddrSimW.imgGateBW` with the
  inclusion in place of the empty analysis at a branch.

## Main results

* `rel_fallW`, `rel_jumpW`: a branch not taken, and a branch taken under the inclusion, keep
  `ImgRelW`.
* `img_stepW_cond'`: the step of `ImgRelW` at a branch under the inclusion.
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
      (sa.setLpc (sa.reg.lpc + 1)) zf := by
  have hnm : slotMov? bi.li_i = none := by rw [hx]; rfl
  have hW1 := oneBitAt_succ (frame := frame) hb (bitStore?_of_eq hx (by simp))
  rw [oneBitStep_noCarry (by rw [hx]; rfl), hx] at hW1
  obtain ⟨hsv, hrl⟩ := saved_reload_nextW (sa' := sa.setLpc (sa.reg.lpc + 1)) hphys hrel hb
    hnm rfl (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  refine ⟨by simp [LstateA.setLpc, LstateM.nextPc, hrel.pc], fun r hr => hrel.regs r hr,
    fun q a ha => (hrel.slots q a ha).of_eq (by simp [LstateM.nextPc]) rfl fun h => by
      simp only [LstateA.setLpc]; rw [hW1]; simpa [icase] using h,
    hrel.zf, hrel.cf, hrel.of, fun r hr hW => ?_,
    fun q A n hq => hrel.cells q A n hq, hsv, hrl⟩
  simp only [LstateA.setLpc] at hW ⊢
  rw [hW1] at hW
  exact hrel.wid r hr (by simpa [icase] using hW)

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
      (sa.setLpc (p + 1)) zf := by
  refine ⟨rfl, fun r hr => hrel.regs r hr,
    fun q a ha => (hrel.slots q a ha).of_eq rfl rfl (hW q), hrel.zf, hrel.cf, hrel.of,
    fun r hr hn => hrel.wid r hr (fun h => hn (hW r h)), fun q A n hq => hrel.cells q A n hq,
    fun k R A n a hS hA ha => ⟨fun hk => ?_, fun hk => ?_⟩, fun b q a A n hbi _ _ _ => ?_⟩
  · have hk' : k < sa.reg.lpc := by
      by_contra hc
      obtain ⟨i', hi', hm'⟩ := hS
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hc) with hlt | heq
      · have hent := (physImgB_slotStore hphys hi' hm' (by rw [hA]; rfl)).2
        obtain ⟨d, src, hm2, -⟩ := entryRegB_spec hent hlt hb
        rw [hnm] at hm2; cases hm2
      · rw [← heq, hb] at hi'
        cases hi'
        rw [hnm] at hm'; cases hm'
    exact (hrel.saved k R A n a hS hA ha).1 hk'
  · show sa.reg.getW R 64 = some (base A)
    by_cases hk' : sa.reg.lpc ≤ k
    · exact (hrel.saved k R A n a hS hA ha).2 hk'
    · exfalso
      obtain ⟨i', hi', hm'⟩ := hS
      have hent := (physImgB_slotStore hphys hi' hm' (by rw [hA]; rfl)).2
      have hpk : p < k := by
        simp only [LstateA.setLpc] at hk
        omega
      obtain ⟨d, src, hm2, -⟩ := entryRegB_spec hent hpk hbp
      rw [hpl] at hm2; cases hm2
  · simp only [LstateA.setLpc] at hbi
    rw [reloadOf_succ_other hbp hpl hpx] at hbi
    cases hbi

/-! ## 2. The step at a branch -/

/-- **One step of the image at a branch with one-bit names.** From states related by
    `ImgRelW`, a checked step of the image at a branch on a condition code with a polarity,
    to a label of the body one past which the width analysis includes the analysis at the
    branch, keeps the zero flag and is matched by one step of the address machine when the
    branch falls through, and by two when it is taken: to the label and over it. -/
theorem img_stepW_cond' {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hphys : physImgB slotArr c = true)
    (hlast : ∃ r, c.getLast? = some r ∧ r.li_i = .Lret) (fn : String) {s t : LstateMF}
    {sa : LstateA} (hrel : ImgRelW frame slotArr base c s sa s.zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) {cc : String} {l : LLabel}
    (hx : bi.li_i = .Lcond (.reg cc) l) {pol : Bool} (hpol : condPol cc = some pol) {p : Nat}
    (hp : labelAt c l = some p)
    (hW : ∀ r, r ∈ oneBitAt frame c sa.reg.lpc → r ∈ oneBitAt frame c (p + 1))
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr c))
      (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t) :
    t.zf = s.zf ∧ StepOut frame rsp c (ImgRelW frame slotArr base c) s.zf sa t := by
  have hi : imgInstr slotArr c sa.reg.lpc bi.li_i = (bi.li_i, .reg none) := by
    rw [hx]; rfl
  obtain ⟨r, hr, hret⟩ := hlast
  have hfl := findLabel_virtImg slotArr c l (fun r' hr' => by
    rw [hr] at hr'
    cases hr'
    rw [hret]; rfl)
  rw [hp] at hfl
  rw [hi, evalInstrPMemFk_reg, hx, eval_cond fn _ cc l _ hpol hfl] at hstep
  have hnm : slotMov? bi.li_i = none := by rw [hx]; rfl
  obtain ⟨hpl, hlab, -⟩ := labelAt_spec hp
  have hbp : c[p]? = some c[p] := List.getElem?_eq_getElem hpl
  have hlabp : ∃ ii', c[p].li_i = .Llabel ii' l := by
    revert hlab
    cases c[p].li_i <;> simp [isLabelB]
  obtain ⟨ii', hli⟩ := hlabp
  have hstepA : stepA frame c sa s.zf = if s.zf = pol then some (sa.setLpc p, s.zf)
      else some (sa.setLpc (sa.reg.lpc + 1), s.zf) := by
    obtain ⟨ii0, li⟩ := bi
    simp only at hx
    subst hx
    simp only [stepA, hb, hpol, hp, Option.map_some]
  by_cases hzp : s.zf = pol
  · rw [if_pos hzp] at hstep hstepA
    cases hstep
    refine ⟨rfl, haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp), _, hstepA,
      Or.inr ⟨⟨c[p], ii', l, by simp [LstateA.setLpc], hli⟩,
        haltedA_of (bi := c[p]) (by simp [LstateA.setLpc]) (by rw [hli]; simp),
        loadSafe_of (bi := c[p]) (by simp [LstateA.setLpc]) (by rw [hli]; simp),
        sa.setLpc (p + 1), ?_,
        rel_jumpW hphys hrel hb hnm hbp (by rw [hli]; rfl)
          (fun ds o ss h => by rw [hli] at h; cases h) hW⟩⟩
    have hb' : c[p]? = some c[p] := hbp
    generalize c[p] = bp at hli hb'
    obtain ⟨ii1, li1⟩ := bp
    simp only at hli
    subst hli
    simp [stepA, LstateA.setLpc, hb']
  · rw [if_neg hzp] at hstep hstepA
    cases hstep
    exact ⟨rfl, haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp), _, hstepA,
      Or.inl (rel_fallW hphys hrel hb hx)⟩

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
      obtain ⟨hW, cc, pol, p, hcc, -, -⟩ := gateAtW_cond (slotArr := slotArr) (c := c) (k := k)
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
    obtain ⟨hW, cc', pol, p, hcc, hpol, hp⟩ := gateAtW_cond rfl h
    cases hcc
    simp [hW, hpol, hp]
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
