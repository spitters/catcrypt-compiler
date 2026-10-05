/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaX86
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMovReg

/-!
# `CorresJ` at the x86 instruction set for blocks with register-to-register moves

`corresIsa_x86_of_corresJ` transports a `runBlock` correspondence `CorresJ SR P fa c` to
`CorresIsa x86Isa` for blocks of `InSubsetM`, whose lowering is a plain `Lopn` body. A
register-to-register `mov` lowers to the wire `Lopn [.reg dst] "MOV:64" [.reg src]`, which
the flag machine steps through its register-copy arm (`movRegArgs?`), so a block containing
one is not a plain `Lopn` body. This module transports `CorresJ` for the subset
`RunBlockLsemAgreeMovReg.InMovRegSubset` (the register arithmetic, the compile-time-offset
loads and stores, the immediate shifts, the negate and the register-to-register `mov`) and
its lowering `List.map jToRMMov`.

The transport is stated once over the extended straight fold `runStraightF` of the flag
machine (`corresIsa_x86_of_runStraightF`): a body of `Lopn`s whose fold from every state
agreeing with a `JState` on the registers and the memory reaches a state agreeing with the
`runBlock` result. For the move-extended subset the fold agreement is proved per
instruction (`fstepF_jToRMMov`): on a register-to-register `mov` the register-copy arm
writes the word `lsemStepMem` writes (`lsemStepMem_movReg`), and on every other instruction
the step is the plain one, covered by `jToRMNeg_agrees` and
`runStraightF_of_lsemStraightMem`.

## Main results

* `corresIsa_x86_of_runStraightF`: `CorresJ` gives `CorresIsa x86Isa` for a body of `Lopn`s
  whose extended straight fold agrees with `runBlock`.
* `plainLopnBody_jToRMNeg`: the lowering of an `InNegSubset` instruction is a plain `Lopn`.
* `fstepF_jToRMMov`, `runStraightF_map_jToRMMov`: the extended straight step and fold of
  the lowering of the move-extended subset agree with `runBlock`.
* `inMovRegSubsetB`, `inMovRegSubsetB_sound`: a Boolean check of `InMovRegSubset`.
* `corresIsa_x86_of_corresJ_mov`: `CorresJ` over an `InMovRegSubset` block gives
  `CorresIsa x86Isa` for its lowering.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeShift (jToRMSh InShiftSubset)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeNeg (jToRMNeg InNegSubset
  jToRMNeg_agrees)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMovReg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM LstateM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (PlainLopnBody cmpArgs?
  movRegArgs?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (fstepF runStraightF
  runStraightF_cons runStraightF_nil runStraightF_lpc runStraightF_of_lsemStraightMem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)

/-! ## The transport over the extended straight fold -/

/-- **`CorresJ` at the x86 instruction set, over the extended straight fold.** Let `seg` be a
    body of `Lopn`s whose fold `runStraightF`, from every state agreeing with a `JState` `s`
    on the registers and the memory, reaches a state agreeing with `runBlock s c`. Then a
    `runBlock` correspondence `CorresJ SR P fa c` gives the `CorresIsa x86Isa`
    correspondence of `singletonProgM fn seg` with fuel its length, under the lifted
    relation `liftSR fn SR`, from counter `0` to the end of the body. -/
theorem corresIsa_x86_of_runStraightF {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : List (JInstr 64)) (fn : String)
    (seg : List LinstrRM) (hl : ∀ i ∈ seg, IsLopn i)
    (hagree : ∀ (s : JState 64) (b0 : LstateM) (zf : Bool), JLstateCorr s b0 →
      ∃ b z, runStraightF seg b0 zf = some (b, z) ∧ JLstateCorr (runBlock s c) b)
    (h : CorresJ SR P fa c) :
    CorresIsa x86Isa (singletonProgM fn seg) (liftSR fn SR)
      (fun a => P a.1 ∧ a.2 = 0) (fun a => (fa a.1, seg.length)) seg.length := by
  rintro ⟨⟨b0, lfn⟩, zf⟩ ⟨a, k⟩ ⟨hfn, hpc, s, hSR, hcorr⟩ ⟨hP, hk⟩
  simp only at hfn hpc hcorr hP hk
  subst hfn hk
  obtain ⟨b, z, hF, hcorr'⟩ := hagree s b0 zf hcorr
  refine ⟨_, x86Isa_lsemFuelMemF_straight lfn seg hl b0 b zf z hpc hF, rfl, ?_, runBlock s c,
    h s a hSR hP, hcorr'⟩
  have := runStraightF_lpc seg b0 zf b z hF
  rw [hpc, Nat.zero_add] at this
  exact this

/-! ## The extended straight fold on the move-extended subset -/

/-- The lowering of an `InNegSubset` instruction is an `Lopn` that is neither the flag
    compare nor a register copy. -/
theorem plainLopnBody_jToRMNeg (i : JInstr 64) (hi : InNegSubset i) :
    PlainLopnBody [jToRMNeg i] := by
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  cases i
  case mov d s =>
    cases s <;> simp_all [InNegSubset, InShiftSubset, InFieldArithSubset, jToRMNeg, jToRMSh,
      jToRM, IsLopn, cmpArgs?, movRegArgs?]
  case storeMem b o s =>
    cases s <;> simp_all [InNegSubset, InShiftSubset, InFieldArithSubset, jToRMNeg, jToRMSh,
      jToRM, IsLopn, cmpArgs?, movRegArgs?]
  case shl d s =>
    cases s <;> simp_all [InNegSubset, InShiftSubset, InFieldArithSubset, jToRMNeg, jToRMSh,
      IsLopn, cmpArgs?, movRegArgs?, VIR.JasminLsemShift.shiftLinstr, withWidthTag]
  case shr d s =>
    cases s <;> simp_all [InNegSubset, InShiftSubset, InFieldArithSubset, jToRMNeg, jToRMSh,
      IsLopn, cmpArgs?, movRegArgs?, VIR.JasminLsemShift.shiftLinstr, withWidthTag]
  case sar d s =>
    cases s <;> simp_all [InNegSubset, InShiftSubset, InFieldArithSubset, jToRMNeg, jToRMSh,
      IsLopn, cmpArgs?, movRegArgs?, VIR.JasminLsemShift.shiftLinstr, withWidthTag]
  case neg d =>
    simp_all [InNegSubset, jToRMNeg, IsLopn, cmpArgs?, movRegArgs?, withWidthTag,
      VIR.JasminLsemWidthN.negLinstr]
    decide
  all_goals simp_all [InNegSubset, InShiftSubset, InFieldArithSubset, jToRMNeg, jToRMSh,
    jToRM, IsLopn, cmpArgs?, movRegArgs?, withWidthTag]

/-- **The extended straight step on the move-extended subset.** From a state agreeing with
    `s` on the registers and the memory, the step `fstepF` of the lowering of an
    `InMovRegSubset` instruction `i` reaches a state agreeing with `runBlock s [i]`, with
    the zero flag unchanged. -/
theorem fstepF_jToRMMov (i : JInstr 64) (hi : InMovRegSubset i) (s : JState 64)
    (b0 : LstateM) (zf : Bool) (h : JLstateCorr s b0) :
    ∃ b, fstepF (jToRMMov i) b0 zf = some (b, zf) ∧ JLstateCorr (runBlock s [i]) b := by
  rcases jToRMMov_cases i with ⟨dst, src, rfl⟩ | ⟨heq, himp⟩
  · obtain ⟨ls', hrun, hcorr'⟩ := movReg_case s b0 h dst src
    have hw : jToRMMov (.mov dst (.reg src))
        = (.Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg src], .reg none) := rfl
    rw [hw, lsemStraightMem_single,
      lsemStepMem_movReg dst src b0 (s.regs src) (h.regAgree src)] at hrun
    have hc : cmpArgs? (jToRMMov (.mov dst (.reg src))) = none := rfl
    have hm : movRegArgs? (jToRMMov (.mov dst (.reg src))) = some (dst, src) := by
      rw [hw]
      simp only [movRegArgs?,
        VIR.JasminLsemScalar.stripWidthTag_withWidthTag_MOV 64, if_true]
    refine ⟨ls', ?_, hcorr'⟩
    unfold fstepF
    rw [hc, hm]
    simp only [VIR.JasminLsemWidthN.readReg_of_getW (h.regAgree src)]
    rw [← Option.some.inj hrun]
    rfl
  · rw [heq]
    obtain ⟨ls', hrun, hcorr'⟩ := jToRMNeg_agrees i (himp hi) s b0 h
    obtain ⟨cf, of, hF⟩ := runStraightF_of_lsemStraightMem _
      (plainLopnBody_jToRMNeg i (himp hi)) b0 ls' zf hrun
    rw [runStraightF_cons] at hF
    cases hstep : fstepF (jToRMNeg i) b0 zf with
    | none => rw [hstep] at hF; exact absurd hF (by simp)
    | some bz =>
        obtain ⟨b1, z1⟩ := bz
        rw [hstep, Option.bind_some, runStraightF_nil] at hF
        simp only [Option.some.injEq, Prod.mk.injEq] at hF
        obtain ⟨rfl, rfl⟩ := hF
        exact ⟨_, rfl, JLstateCorr_withFlags hcorr' cf of⟩

/-- **The extended straight fold on the move-extended subset.** From a state agreeing with
    `s` on the registers and the memory, the fold `runStraightF` of the lowering of an
    `InMovRegSubset` block `c` reaches a state agreeing with `runBlock s c`, with the zero
    flag unchanged. -/
theorem runStraightF_map_jToRMMov (c : List (JInstr 64)) (hc : ∀ i ∈ c, InMovRegSubset i)
    (s : JState 64) (b0 : LstateM) (zf : Bool) (h : JLstateCorr s b0) :
    ∃ b, runStraightF (c.map jToRMMov) b0 zf = some (b, zf) ∧ JLstateCorr (runBlock s c) b := by
  induction c generalizing s b0 with
  | nil => exact ⟨b0, rfl, h⟩
  | cons i is ih =>
      obtain ⟨b1, hstep, hcorr1⟩ := fstepF_jToRMMov i (hc i (List.mem_cons_self ..)) s b0 zf h
      obtain ⟨b, hrun, hcorr'⟩ :=
        ih (fun j hj => hc j (List.mem_cons_of_mem i hj)) (runBlock s [i]) b1 hcorr1
      refine ⟨b, ?_, ?_⟩
      · rw [List.map_cons, runStraightF_cons, hstep, Option.bind_some]
        exact hrun
      · simpa only [runBlock_cons, runBlock_nil] using hcorr'

/-- The lowering of an `InMovRegSubset` instruction is an `Lopn`. -/
theorem isLopn_jToRMMov (i : JInstr 64) (hi : InMovRegSubset i) : IsLopn (jToRMMov i) := by
  rcases jToRMMov_cases i with ⟨dst, src, rfl⟩ | ⟨heq, himp⟩
  · exact ⟨_, _, _, rfl⟩
  · rw [heq]
    exact (plainLopnBody_jToRMNeg i (himp hi) _ (List.mem_singleton_self _)).1

/-! ## A Boolean check of the move-extended subset -/

/-- A Boolean check of `InMovRegSubset`: the moves, the two-address register arithmetic, the
    negate, the immediate shifts with count below `64`, and the loads and register stores at
    a non-negative offset. -/
def inMovRegSubsetB : JInstr 64 → Bool
  | .mov _ _ => true
  | .add _ _ => true
  | .sub _ _ => true
  | .imul _ _ => true
  | .and_ _ _ => true
  | .or_ _ _ => true
  | .xor_ _ _ => true
  | .neg _ => true
  | .shl _ (.imm n) => decide (n < 64)
  | .shr _ (.imm n) => decide (n < 64)
  | .sar _ (.imm n) => decide (n < 64)
  | .loadMem _ _ off => decide (0 ≤ off)
  | .storeMem _ off (.reg _) => decide (0 ≤ off)
  | _ => false

/-- An instruction accepted by `inMovRegSubsetB` is in `InMovRegSubset`. -/
theorem inMovRegSubsetB_sound (i : JInstr 64) (h : inMovRegSubsetB i = true) :
    InMovRegSubset i := by
  cases i
  case mov d s => cases s <;> simp [InMovRegSubset, InNegSubset, InShiftSubset, InFieldArithSubset]
  case storeMem b o s =>
    cases s <;> simp_all [inMovRegSubsetB, InMovRegSubset, InNegSubset, InShiftSubset,
      InFieldArithSubset]
  case shl d s =>
    cases s <;> simp_all [inMovRegSubsetB, InMovRegSubset, InNegSubset, InShiftSubset]
  case shr d s =>
    cases s <;> simp_all [inMovRegSubsetB, InMovRegSubset, InNegSubset, InShiftSubset]
  case sar d s =>
    cases s <;> simp_all [inMovRegSubsetB, InMovRegSubset, InNegSubset, InShiftSubset]
  all_goals simp_all [inMovRegSubsetB, InMovRegSubset, InNegSubset, InShiftSubset,
    InFieldArithSubset]

/-! ## The transport on the move-extended subset -/

/-- **`CorresJ` at the x86 instruction set, with register-to-register moves.** For a block
    `c` of `InMovRegSubset` instructions, a `runBlock` correspondence `CorresJ SR P fa c`
    gives the `CorresIsa x86Isa` correspondence of the lowered program
    `singletonProgM fn (c.map jToRMMov)` with fuel its length, under the lifted relation
    `liftSR fn SR`, from counter `0` to the end of the body. -/
theorem corresIsa_x86_of_corresJ_mov {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : List (JInstr 64)) (fn : String)
    (hc : ∀ i ∈ c, InMovRegSubset i) (h : CorresJ SR P fa c) :
    CorresIsa x86Isa (singletonProgM fn (c.map jToRMMov)) (liftSR fn SR)
      (fun a => P a.1 ∧ a.2 = 0) (fun a => (fa a.1, (c.map jToRMMov).length))
      (c.map jToRMMov).length :=
  corresIsa_x86_of_runStraightF SR P fa c fn (c.map jToRMMov)
    (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact isLopn_jToRMMov i (hc i hi))
    (fun s b0 zf hcorr => by
      obtain ⟨b, hrun, hcorr'⟩ := runStraightF_map_jToRMMov c hc s b0 zf hcorr
      exact ⟨b, zf, hrun, hcorr'⟩)
    h

end CatCrypt.Crypto.SecureCompilation.Ascent
