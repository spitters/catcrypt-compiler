/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW

@[expose] public section

set_option autoImplicit false

/-!
# The image simulation with carry chains at a branch

`ImageAddrSimW.img_stepW` is the step of the image simulation with carry chains at an
instruction other than a branch. The gate `ImageAddrSimW.gateAtW` accepts a branch on a
condition code where the width analysis `ImageAddrSimW.oneBitAt` is empty. There `ImgRelW` is
`ImgRel` (`imgRel_of_W`), the branch is the branch of `ImageAddrSim.img_step`, and `ImgRel` at
the target gives `ImgRelW` there (`imgRelW_of`), whatever the width analysis of the straight
prefix up to the target is.

## Main definitions

* `StepOut`: the conclusion of a step of the image, over a relation: one step of the address
  machine into the relation, or two when the image takes a branch, the first to the label and
  the second over it.

## Main results

* `img_step_cond`: the step of `ImageAddrSim.ImgRel` at a branch, from the facts of the gate
  at that instruction.
* `gateAtW_cond`: the gate of a branch gives an empty width analysis, the polarity of the
  condition code and the position of the label.
* `img_stepW_cond`: the step of `ImgRelW` at a branch.
* `img_stepW'`: the step of `ImgRelW` at every instruction.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW

/-- **The conclusion of a step of the image** from the address state `sa` to the image state
    `t`, over a relation `R` between image states, address states and zero flags: the address
    machine does not halt at `sa`, reads outside the red-zone word there, and steps to a
    state `sa1` that is related to `t`, or that stands at a label, from where a second step
    reaches a state related to `t`. The zero flag after each step is the zero flag of `t`. -/
def StepOut (frame : String → Option (BitVec 64)) (rsp : BitVec 64) (c : Lcmd)
    (R : LstateMF → LstateA → Bool → Prop) (zf : Bool) (sa : LstateA) (t : LstateMF) : Prop :=
  haltedA c sa = false ∧ LoadSafeAt rsp c sa
    ∧ ∃ sa1, stepA frame c sa zf = some (sa1, t.zf)
      ∧ (R t sa1 t.zf
        ∨ ((∃ bp ii l, c[sa1.reg.lpc]? = some bp ∧ bp.li_i = .Llabel ii l)
          ∧ haltedA c sa1 = false ∧ LoadSafeAt rsp c sa1
          ∧ ∃ sa2, stepA frame c sa1 t.zf = some (sa2, t.zf) ∧ R t sa2 t.zf))

/-- `StepOut` is monotone in the relation. -/
theorem StepOut.mono {frame : String → Option (BitVec 64)} {rsp : BitVec 64} {c : Lcmd}
    {R R' : LstateMF → LstateA → Bool → Prop} {zf : Bool} {sa : LstateA} {t : LstateMF}
    (h : StepOut frame rsp c R zf sa t) (hR : ∀ sa' z, R t sa' z → R' t sa' z) :
    StepOut frame rsp c R' zf sa t := by
  obtain ⟨hh, hs, sa1, hst, hcase⟩ := h
  refine ⟨hh, hs, sa1, hst, ?_⟩
  rcases hcase with h1 | ⟨hl, hh1, hs1, sa2, hst2, h2⟩
  · exact Or.inl (hR _ _ h1)
  · exact Or.inr ⟨hl, hh1, hs1, sa2, hst2, hR _ _ h2⟩

/-- **The step of the image at a branch.** From states related by `ImgRel`, a checked step of
    the image at a branch on a condition code with a polarity, to a label of the body, keeps
    the zero flag and is matched by one step of the address machine when the branch falls
    through, and by two when it is taken: to the label and over it. -/
theorem img_step_cond {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hphys : physImgB slotArr c = true)
    (hlast : ∃ r, c.getLast? = some r ∧ r.li_i = .Lret) (fn : String) {s t : LstateMF}
    {sa : LstateA} (hrel : ImgRel frame slotArr base c s sa s.zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) {cc : String} {l : LLabel}
    (hx : bi.li_i = .Lcond (.reg cc) l) {pol : Bool} (hpol : condPol cc = some pol) {p : Nat}
    (hp : labelAt c l = some p)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr c))
      (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t) :
    t.zf = s.zf ∧ StepOut frame rsp c (ImgRel frame slotArr base c) s.zf sa t := by
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
        rel_jump hphys hrel hb hnm hbp (by rw [hli]; rfl)
          (fun ds o ss h => by rw [hli] at h; cases h)⟩⟩
    have hb' : c[p]? = some c[p] := hbp
    generalize c[p] = bp at hli hb'
    obtain ⟨ii1, li1⟩ := bp
    simp only at hli
    subst hli
    simp [stepA, LstateA.setLpc, hb']
  · rw [if_neg hzp] at hstep hstepA
    cases hstep
    exact ⟨rfl, haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp), _, hstepA,
      Or.inl (rel_label hphys hrel hb hnm)⟩

/-- **The gate of a branch**: the width analysis is empty, the branch is on a condition code
    with a polarity, and its label is a label of the body. -/
theorem gateAtW_cond {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {c : Lcmd} {k : Nat} {W : List String}
    {x : LinstrR} {cnd : _} {l : LLabel} (hx : x = .Lcond cnd l)
    (hg : gateAtW frame slotArr c k W x = true) :
    W = [] ∧ ∃ cc pol p, cnd = .reg cc ∧ condPol cc = some pol ∧ labelAt c l = some p := by
  subst hx
  simp only [gateAtW, Bool.and_eq_true] at hg
  obtain ⟨-, hg⟩ := hg
  have hci : carryI? (.Lcond cnd l) = none := rfl
  rw [hci] at hg
  cases hc : icase frame (.Lcond cnd l) with
  | cond cc l' =>
      rw [hc] at hg
      have hx := icase_cond hc
      simp only [LinstrR.Lcond.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.isEmpty_iff] at hg
      obtain ⟨⟨hW, pol, hpol⟩, p, hp⟩ := hg
      exact ⟨hW, cc, pol, p, rfl, hpol, hp⟩
  | other =>
      rw [hc] at hg
      simp [castGateB, DecodePrintedAddrW.classifyK] at hg
  | label => exact absurd (icase_label hc) (by simp)
  | ldx d b idx => exact absurd (icase_ldx hc) (by simp)
  | stx d b idx v => exact absurd (icase_stx hc) (by simp)
  | sload d q => exact absurd (icase_sload hc).1 (by simp [slotMov?])
  | sstore q S => exact absurd (icase_sstore hc).1 (by simp [slotMov?])
  | scmp d y q => exact absurd (icase_scmp hc).1 (by simp [slotCmp?])
  | reg =>
      obtain ⟨ds, o, ss, hx, -⟩ := icase_reg hc
      cases hx

/-- **One step of the image at a branch.** From states related by `ImgRelW`, a checked step
    of the image of a body that passes `imgGateBW` at a branch keeps the zero flag and is
    matched by one step of the address machine when the branch falls through, and by two when
    it is taken: to the label and over it. -/
theorem img_stepW_cond {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hphys : physImgB slotArr c = true)
    (hgate : imgGateBW frame slotArr c = true) (fn : String) {s t : LstateMF} {sa : LstateA}
    (hrel : ImgRelW frame slotArr base c s sa s.zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1)
    {cnd : _} {l : LLabel} (hc : bi.li_i = .Lcond cnd l)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr c))
      (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t) :
    t.zf = s.zf ∧ StepOut frame rsp c (ImgRelW frame slotArr base c) s.zf sa t := by
  have hg : instrGateBW frame slotArr c sa.reg.lpc bi.li_i = true := by
    simp only [imgGateBW, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
    have := hgate.1.1 sa.reg.lpc hlt
    rw [hb] at this
    simpa using this
  obtain ⟨hW, cc, pol, p, rfl, hpol, hp⟩ := gateAtW_cond hc hg
  obtain ⟨hz, hout⟩ := img_step_cond (rsp := rsp) hphys (imgGateBW_last hgate) fn
    (imgRel_of_W hrel hW) hb hc hpol hp hstep
  exact ⟨hz, hout.mono fun _ _ h => imgRelW_of h⟩

/-- **One step of the image.** From states related by `ImgRelW`, a checked step of the image
    of a body that passes `imgGateBW` is matched by one step of the address machine, or by
    two when the image takes a branch (the address machine stops at the label); the address
    machine does not halt and reads outside the red-zone word at each state it steps from. -/
theorem img_stepW' {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr c = true)
    (hgate : imgGateBW frame slotArr c = true) (fn : String) {s t : LstateMF} {sa : LstateA}
    (hrel : ImgRelW frame slotArr base c s sa s.zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr c))
      (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t) :
    StepOut frame rsp c (ImgRelW frame slotArr base c) s.zf sa t := by
  by_cases hc : ∃ cnd l, bi.li_i = .Lcond cnd l
  · obtain ⟨cnd, l, hc⟩ := hc
    exact (img_stepW_cond hphys hgate fn hrel hb hlt hc hstep).2
  · obtain ⟨hh, hs, sa1, hst, hr⟩ := img_stepW hsep hphys hgate _ hrel hb hlt
      (fun cc l h => hc ⟨cc, l, h⟩) hstep
    exact ⟨hh, hs, sa1, hst, Or.inl hr⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond
