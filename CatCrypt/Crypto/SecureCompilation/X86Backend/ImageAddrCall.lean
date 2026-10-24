/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut

@[expose] public section

set_option autoImplicit false

/-!
# The image relation across a call to a callee given by a run relation

`ImageAddrSim.ImgRel` relates a state of the name-keyed machine on the image of a printed
body to a state of the address machine, and `DecodePrintedAddr.ACorr` relates that state to
a state of the byte machine. A callee is a run relation `Callee.CalleeRun` with an
interface `Callee.CalleeSig` and the specification `Callee.CalleeSpec`. This module proves
that both relations hold after a call whose callee meets its specification, for every run
of the callee, and states the class of printed bodies with calls.

## The summary step

A call sets every general-purpose name whose machine register is in the clobber set of the
callee (`clobN`) and the three flags to the values of an oracle
`ImageCallProbe.CallOut`, and advances the program counter: `callSumC` on the image and
`callAC` on the address machine. The result register is in the clobber set, and its value
is constrained by the postcondition of the callee.

## The word reading of a callee

`WordCallee c res pr room` relates an interface `c` to a procedure summary
`LprogIsa.ProcSummary`: the precondition follows from `room` and from the summary being
defined at the words of the argument registers, and the postcondition gives the word of
the summary in the register of `res`. `LprogIsa.retWord res v` is the step of the summary
on the image. After a call the image state `LprogIsa.retWord res v s` and the address state
are related up to the names `exemptC c` and the three flags (`ImgRelF`).

## The frame of a calling body

The return word of a call is the eight bytes below the stack register and the frame of the
callee lies below it. `FrameAbove frame rsp G` states that every frame word is at a
non-negative offset from `rsp`, with `G` bytes and the return word below `rsp`;
`frameNonnegB` decides it on the frame offsets of a printed body. `CallerSep` adds the same
for the array words. A save of an array pointer does not follow a call in a body of the
class `physImgB` (`not_saveAt_after_call`), and no register is a reload of a frame word
after a call (`ImageCallProbe.reloadOf_call`).

## Main definitions

* `clobN`, `callRegsC`, `callSumC`, `callAC`: the summary step of a call.
* `WordCallee`: the reading of an interface as a procedure summary on words.
* `FrameAbove`, `frameNonnegB`, `CallerSep`, `FootBelow`: the frame words and the array
  words above the return word and the frame of the callee.
* `AgreeOffF`, `ImgRelF`, `exemptC`: the image relation up to a list of names and the
  flags.
* `remoteCallB`, `callFreeB`, `instrOKCB`, `relocFrameB`, `printedAddrCB`, `imgGateCB`: the
  class of printed bodies with calls and the gate of the image simulation between calls.
* `AgreeOffD`, `DeadTab`, `deadStepB`: agreement of two image states up to dead names and
  dead flags, a table of dead names and live flags by position, and the check of a
  described instruction against it.
* `DeadTab.le`, `deadCtlB`, `deadSegB`, `DeadAgree`: the comparison of two positions of a
  table, the check of a control instruction and of a body against a table, and agreement
  up to the table of the position of a state.
* `SegSim`: the statement of the simulation of one segment `LprogCallCut.SegTo` of a body
  with shadow instructions, at a table of dead names, from the positions where no flag is
  live.
* `SegExact`, `DeadTab.live`, `callFlagsB`: the statement of the simulation of one segment
  at the relation `ImgRel`, the positions where a flag is live, and the check that no flag
  is live after a call.
* `callImg`: the image of a calling body, `virtImg` with a shadow instruction at each
  call.
* `callDeadB`, `SitesOf`, `siteShapeB`: the dead names at the calls, and the shadow
  instructions as calls of one summary on register operands.

## Main results

* `call_return`: every run of a specified callee, followed by the return.
* `imgRel_callC`, `acorr_callC`: the two relations across the summary step.
* `not_saveAt_after_call`: no save of an array pointer follows a call.
* `frameAbove_of_frameNonnegB`, `footClear_of_callerSep`: the frame check gives
  `ImageCallProbe.FootClear` for a callee whose footprint is its frame.
* `pre_of_image`: the precondition of the callee from the image relation.
* `call_reestablishes`: both relations after every run of the callee.
* `call_reestablishes_word`, `haltsO_call_image`: the relaxed relation after the step of
  the summary, and the continuation of the run under the oracle of the callee.
* `step_congrD`, `step_deadStepB`: the congruence of a described step up to dead names and
  dead flags.
* `haltsO_call_imageF`: a call from the relaxed relation.
* `ResStep`, `SiteStep`, `deadAfter`: the call step of a callee at a result of a call
  (`LprogIsa.CallRes`), the step of a call site at the dead names before and after it, and
  the names dead after a result is written.
* `resStep_word`, `siteStep_word`, `AgreeOffF.retRes`, `haltsO_call_imageS`: the word
  instances from `call_reestablishes_word`, agreement across the write of a result, and a
  call site from the relaxed relation.
* `haltsO_of_runChainS`: a chain `LprogCallCut.RunChain` with `SegSim` at the steps of its
  call sites is a run under the oracle; `haltsO_of_runChain` is its word instance.
* `procStep_regArgs`, `glue_regArgs`: the step `LprogCallCut.Glue` is the step of the
  summary at the argument words.
* `haltsO_of_withProcs_run`: a halting run on the machine with procedures is a run under
  the oracle, from `SegSim`.
* `ctl_deadStep`, `steps_deadSeg`: a control step and a run of steps of a body that passes
  `deadSegB` keep the agreement of the table.
* `DeadSteps`, `deadSteps_x86`, `segSim_of_segExact`: the steps of an instruction set keep
  the agreement of a table, which holds at x86 for a body that passes `deadSegB`, and
  `SegSim` from `SegExact` under it.
* `imgGate_of_imgGateCB`, `callSitesB`, `condLiveB`, `CondFlag`, `ByteSeg`: the positionwise
  gate from the gate of a calling body, the checks of the call sites and of the flags at
  conditional branches, and the statement of the byte simulation of the segments.
* `steps_callImg`, `segExact_callImg`, `haltsO_of_deadChecks`: a run of checked steps of
  the image `callImg` by the decoded program, `SegExact` for the image from `ByteSeg`, and
  the run under the oracle from the Boolean checks and `ByteSeg`.
* `haltsO_of_deadChecksS`, `haltsO_of_linkedChecksS`, `haltsC_of_linkedChecksS`: the runs
  under the oracle and through calls at the steps of the call sites; `haltsO_of_deadChecks`,
  `haltsO_of_linkedChecks` and `haltsC_of_linkedChecks` are their word instances.
* `callImg_length`, `callImg_getElem?_of_ne`, `callImg_getElem?_call`,
  `findLabelMem_callImg`: the image of a calling body has the positions and the labels of
  the image, the instruction of the image off the calls, and the shadow instruction at a
  call.
* `printedAddrCB_of_printedAddrB`, `printedAddrB_iff_of_callFree`, `imgGateCB_of_callFree`:
  on a body without calls the classes are the existing ones.
* `printedAddrCB_reloc`, `printedAddrCB_remote`, `relocShapeOK_of_printedAddrCB`,
  `printedAddrCB_frameAbove`: the facts of the class for the relocating encoder and for the
  frame.
* `keepPoolB_clobN`: a name of a checked allocation pool is not set by the summary step
  and is not exempted after a call.
* `lfundefPhysAbiOfVirtCCert`, `lfundefPhysAbiOfVirtC`: the allocation of a caller of `c`
  at the pool `keepPool c`, with the shadow instructions expanded after the allocation,
  with and without its allocation certificate.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
  (RInstr callOps retOps Params ShapeOK Shape)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (remoteSym)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc (RelocShapeOK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (calleeSavedToSave frameSize)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (dispOk32)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (leaFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
  (gpOk gpList mem_gpList gpFacts phys evalInstrA_leaFrame isRetB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr redW frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
  (printedAddrB instrOKB condPrevB frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout (decodableLcmd)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame
  (frameOffs frameIn frameIn_some offOf bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe
  (retWord entryOf entryOf_regs entryOf_mem retOps_eq CallOut argWord argWord_congr
    read64_congr_range reloadOf_call outOf memAfter FootClear)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
  (CalleeRun CalleeSig CalleeSpec HaltsO oracleAt InFrame)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

/-! ## 1. Every run of a specified callee, followed by the return -/

/-- **The byte machine across a run of a specified callee.** For every run of the callee
    from the entry state of a call, after the stack operation of the return: the stack
    register holds its value before the call; every other register holds its value at the
    return of the callee; a register outside the clobber set holds its value before the
    call; every byte outside the footprint and the return word is kept; and the
    postcondition relates the entry state to the return state of the callee. -/
theorem call_return {X : CalleeRun} {c : CalleeSig} (h : CalleeSpec X c) (ret : Nat)
    (s : AState) (hpre : c.pre (entryOf ret s)) {t : List CTLeak} {sc : AState}
    (hX : X (entryOf ret s) t sc) :
    (retOps.foldl aMachine.exec sc).regs "%rsp" = s.regs "%rsp"
      ∧ (∀ r, r ≠ "%rsp" → (retOps.foldl aMachine.exec sc).regs r = sc.regs r)
      ∧ (∀ r, r ≠ "%rsp" → c.clob r = false →
          (retOps.foldl aMachine.exec sc).regs r = s.regs r)
      ∧ (∀ x, ¬ c.foot (entryOf ret s) x → ¬ InRange8 (retWord s) x →
          (retOps.foldl aMachine.exec sc).mem x = s.mem x)
      ∧ c.post (entryOf ret s) sc := by
  obtain ⟨hl, hlm⟩ := evalInstrA_leaFrame sc 8
  refine ⟨?_, fun r hr => ?_, fun r hr hcl => ?_, fun x hx hx' => ?_, h.post _ t sc hpre hX⟩
  · rw [retOps_eq, hl, ite_eq_left rfl, h.rsp _ t sc hpre hX, entryOf_regs, ite_eq_left rfl, retWord,
      BitVec.add_assoc]
    simp
  · rw [retOps_eq, hl, ite_eq_right hr]
  · rw [retOps_eq, hl, ite_eq_right hr, h.keep _ t sc hpre hX r hcl, entryOf_regs, ite_eq_right hr]
  · rw [retOps_eq, hlm, h.frame _ t sc hpre hX x hx, entryOf_mem ret s x hx']

/-! ## 2. The summary step of a call -/

/-- The name `r` is a general-purpose name whose machine register the callee may change. -/
def clobN (c : CalleeSig) (r : String) : Bool := gpOk r && c.clob (phys r)

/-- The register file after a call: a name of `clobN` holds the oracle's word, every other
    name is kept, and the program counter advances. -/
def callRegsC (c : CalleeSig) (ω : CallOut) (R : LstateN) : LstateN where
  lvm := fun r => if clobN c r then ⟨64, ω.reg r⟩ else R.lvm r
  lpc := R.lpc + 1

/-- **The summary step of a call on the image**, a function of the oracle `ω`: the register
    file of `callRegsC`, the three flags of `ω`, the arrays kept. -/
def callSumC (c : CalleeSig) (ω : CallOut) (s : LstateMF) : LstateMF :=
  { prog := { s.prog with
      base := { s.prog.base with reg := callRegsC c ω s.prog.base.reg, cf := ω.cf, of := ω.of } }
    zf := ω.zf }

/-- **The summary step of a call on the address machine**: the register file of
    `callRegsC`, the memory `m`, the carry and overflow flags of `ω`. -/
def callAC (c : CalleeSig) (ω : CallOut) (m : AMem) (sa : LstateA) : LstateA :=
  { reg := callRegsC c ω sa.reg, mem := m, cf := ω.cf, of := ω.of }

@[simp] theorem callAC_lpc (c : CalleeSig) (ω : CallOut) (m : AMem) (sa : LstateA) :
    (callAC c ω m sa).reg.lpc = sa.reg.lpc + 1 := rfl

/-! ## 3. The image relation across the summary step -/

/-- **No save of an array pointer follows a call.** In a body of the class `physImgB`, the
    save of a register into the frame word of an array pointer is not at a position after a
    call instruction. -/
theorem not_saveAt_after_call {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hphys : physImgB slotArr body = true) {p : Nat} {bi : Linstr} (hb : body[p]? = some bi)
    {ra : Option String} {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt) {k : Nat}
    {R A : String} {n : Nat} (hS : SaveAt body k R) (hA : slotArr (slotOfReg R) = some (A, n)) :
    ¬ p < k := by
  intro hpk
  obtain ⟨i, hi, hm⟩ := hS
  obtain ⟨-, hent⟩ := physImgB_slotStore hphys hi hm (by rw [hA]; rfl)
  obtain ⟨d, src, hmv, -⟩ := entryRegB_spec hent hpk hb
  rw [hbi] at hmv
  simp [slotMov?] at hmv

/-- **The image relation across the summary step of a call**, for one oracle on both
    levels. Let the instruction at the program counter be a call in a body of the class
    `physImgB`. If the memory `m` after the call holds the bytes of every frame word and of
    every array word of the memory before it, the relation holds between `callSumC c ω s`
    and `callAC c ω m sa`. -/
theorem imgRel_callC {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (c : CalleeSig) (ω : CallOut) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {ra : Option String} {tgt : String × LLabel}
    (hbi : bi.li_i = .Lcall ra tgt) {m : AMem}
    (hfr : ∀ q a, frame q = some a → ∀ x, InRange8 a x → m x = sa.mem x)
    (hce : ∀ q A n j, slotArr q = some (A, n) → j < n →
      ∀ x, InRange8 (cellAt (base A) j) x → m x = sa.mem x) :
    ImgRel frame slotArr base body (callSumC c ω s) (callAC c ω m sa) ω.zf := by
  have hlvm : ∀ r, gpOk r = false → ∀ R : LstateN, (callRegsC c ω R).lvm r = R.lvm r := by
    intro r hr R
    simp [callRegsC, clobN, hr]
  refine ⟨congrArg (· + 1) hrel.pc, fun r hr => ?_, fun q a ha => ?_, rfl, rfl, rfl,
    fun r hr => ?_, fun q A n hq => ?_, fun k R A n a hS hA ha => ⟨fun hk => ?_, fun hk => ?_⟩,
    fun b q a A n hr => ?_, fun R A n a hR hA ha => ?_⟩
  · show (callRegsC c ω s.prog.base.reg).lvm r = (callRegsC c ω sa.reg).lvm r
    simp only [callRegsC, hrel.regs r hr]
  · have hq : gpOk q = false := by
      cases hg : gpOk q
      · rfl
      · rw [hsep.gp q hg] at ha; cases ha
    show (callRegsC c ω s.prog.base.reg).lvm q = ⟨64, read64 m a⟩
    rw [hlvm q hq, hrel.slots q a ha, read64_congr_range (hfr q a ha)]
  · show ((callRegsC c ω sa.reg).lvm r).1 = 64
    simp only [callRegsC]
    split_ifs
    · rfl
    · exact hrel.wid r hr
  · obtain ⟨arr, h1, h2⟩ := hrel.cells q A n hq
    exact ⟨arr, h1, fun j hj => by
      show read64 m _ = _
      rw [read64_congr_range (hce q A n j hq hj)]; exact h2 j hj⟩
  · have hk' : k < sa.reg.lpc := by
      have hk0 : k < sa.reg.lpc + 1 := hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk0 with h | rfl
      · exact h
      · obtain ⟨i, hi, hm⟩ := hS
        rw [hb] at hi
        cases hi
        rw [hbi] at hm
        cases hm
    show read64 m a = base A
    rw [read64_congr_range (hfr _ a ha)]
    exact (hrel.saved k R A n a hS hA ha).1 hk'
  · have hk0 : sa.reg.lpc + 1 ≤ k := hk
    exact absurd (show sa.reg.lpc < k by omega) (not_saveAt_after_call hphys hb hbi hS hA)
  · have e : reloadOf slotArr body (sa.reg.lpc + 1) b = some q := hr
    rw [reloadOf_call hb hbi] at e
    cases e
  · show read64 m a = base A
    rw [read64_congr_range (hfr _ a ha)]
    exact hrel.held R A n a hR hA ha

/-- **The byte correspondence across the summary step.** If after the return the stack
    register and the registers outside the clobber set hold their values before the call,
    `ACorr` holds between the byte state after the return and `callAC` with the oracle
    `outOf` and the memory `memAfter`. -/
theorem acorr_callC {rsp : BitVec 64} {sA sA' : AState} {sa : LstateA} (c : CalleeSig)
    (ω : CallOut) (hc : ACorr rsp sA sa) (hsp : sA'.regs "%rsp" = sA.regs "%rsp")
    (hk : ∀ r, gpOk r = true → c.clob (phys r) = false →
      sA'.regs (phys r) = sA.regs (phys r)) :
    ACorr rsp sA' (callAC c (outOf sA' ω) (memAfter rsp sa.mem sA'.mem) sa) := by
  refine ⟨fun r hg => ?_, hsp.trans hc.sp, fun x hx => ?_⟩
  · show (callRegsC c (outOf sA' ω) sa.reg).getW r 64 = some (sA'.regs (phys r))
    rw [getW_eq_some_iff]
    simp only [callRegsC]
    split_ifs with h1
    · rfl
    · have hcl : c.clob (phys r) = false := by simpa [clobN, hg] using h1
      rw [hk r hg hcl]
      exact getW_eq_some_iff.mp (hc.regs r hg)
  · show memAfter rsp sa.mem sA'.mem x = sA'.mem x
    simp [memAfter, hx]

/-- **A call to a specified callee re-establishes the relations.** Let the image state `s`,
    the address state `sa` and the byte state `sA` be related by `ImgRel` and `ACorr`, the
    instruction at the program counter be a call in a body of the class `physImgB`, the
    entry state satisfy the precondition of a callee with `CalleeSpec`, and the frame words
    and the array words lie outside the footprint and the return word. Then for every run
    of the callee and every oracle `ω`, after the return: `ACorr` holds for the address
    state `callAC` with the oracle `outOf`; `ImgRel` holds for the summary step with that
    oracle; and the postcondition relates the entry state to the return state. -/
theorem call_reestablishes {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {s : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf) {sA : AState}
    (hc : ACorr rsp sA sa) {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi)
    {ra : Option String} {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt) (ret : Nat)
    (hpre : c.pre (entryOf ret sA))
    (hfoot : FootClear frame slotArr base
      fun x => c.foot (entryOf ret sA) x ∨ InRange8 (retWord sA) x)
    {t : List CTLeak} {sc : AState} (hrun : X (entryOf ret sA) t sc) (ω : CallOut) :
    ACorr rsp (retOps.foldl aMachine.exec sc)
        (callAC c (outOf (retOps.foldl aMachine.exec sc) ω)
          (memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem) sa)
      ∧ ImgRel frame slotArr base body
          (callSumC c (outOf (retOps.foldl aMachine.exec sc) ω) s)
          (callAC c (outOf (retOps.foldl aMachine.exec sc) ω)
            (memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem) sa) ω.zf
      ∧ c.post (entryOf ret sA) sc := by
  obtain ⟨hsp, -, hk, hm, hpost⟩ := call_return hX ret sA hpre hrun
  have hmem : ∀ x, ¬ (c.foot (entryOf ret sA) x ∨ InRange8 (retWord sA) x) →
      memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem x = sa.mem x := by
    intro x hx
    unfold memAfter
    split_ifs with hred
    · rfl
    · rw [hm x (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h))]
      exact (hc.mem x hred).symm
  exact ⟨acorr_callC c ω hc hsp fun r hg hcl => hk _ (gpFacts hg).physNe hcl,
    imgRel_callC hsep hphys c (outOf _ ω) hrel hb hbi
      (fun q a ha x hx => hmem x (hfoot.1 q a ha x hx))
      (fun q A n j hq hj x hx => hmem x (hfoot.2 q A n j hq hj x hx)), hpost⟩

/-! ## 4. The frame words and the array words above the return word -/

/-- Every frame word is at an offset `o` above `rsp`, with `o + 16 + G` at most
    `2 ^ 64`: the eight bytes of the word do not reach the `G + 8` bytes below `rsp`. -/
def FrameAbove (frame : String → Option (BitVec 64)) (rsp : BitVec 64) (G : Nat) : Prop :=
  ∀ q a, frame q = some a →
    ∃ o : Nat, o + 16 + G ≤ 2 ^ 64 ∧ a = rsp + BitVec.ofNat 64 o

/-- The sum of a word below `8` and a number `k` with `k + 8 ≤ 2 ^ 64` does not wrap. -/
theorem toNat_add_ofNat_of_lt (d : BitVec 64) (k : Nat) (hd : d.toNat < 8)
    (hk : k + 8 ≤ 2 ^ 64) : (d + BitVec.ofNat 64 k).toNat = d.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show d.toNat + k < 2 ^ 64 by omega)]

/-- A byte of a word at a non-negative offset from `r` is not a byte of the return word
    below `r`. -/
theorem above_not_retWord (r x : BitVec 64) (o : Nat) (h1 : o + 16 ≤ 2 ^ 64)
    (hx : InRange8 (r + BitVec.ofNat 64 o) x) : ¬ InRange8 (r + BitVec.ofInt 64 (-8)) x := by
  intro hr
  unfold InRange8 at hx hr
  have key : x - (r + BitVec.ofInt 64 (-8))
      = (x - (r + BitVec.ofNat 64 o)) + BitVec.ofNat 64 (o + 8) := by
    have e8 : BitVec.ofInt 64 (-8) = -(BitVec.ofNat 64 8) := rfl
    rw [e8, BitVec.ofNat_add]
    ring
  rw [key, toNat_add_ofNat_of_lt _ _ hx (by omega)] at hr
  omega

/-- A byte of a word at a non-negative offset from `r` is not among the `G` bytes below
    the return word. -/
theorem above_not_inFrame (r x : BitVec 64) (o G : Nat) (h1 : o + 16 + G ≤ 2 ^ 64)
    (hx : InRange8 (r + BitVec.ofNat 64 o) x) : ¬ InFrame (r + BitVec.ofInt 64 (-8)) G x := by
  intro hr
  unfold InRange8 at hx
  unfold InFrame at hr
  have key : x - (r + BitVec.ofInt 64 (-8) + BitVec.ofInt 64 (-(G : Int)))
      = (x - (r + BitVec.ofNat 64 o)) + BitVec.ofNat 64 (o + 8 + G) := by
    have e8 : BitVec.ofInt 64 (-8) = -(BitVec.ofNat 64 8) := rfl
    rw [e8, BitVec.ofInt_neg, BitVec.ofInt_natCast, BitVec.ofNat_add, BitVec.ofNat_add]
    ring
  rw [key, toNat_add_ofNat_of_lt _ _ hx (by omega)] at hr
  omega

/-- **The frame check of a calling body**: every frame offset `o` of the body, from the
    stack register after the prologue, is non-negative with `o + 16 + G` at most
    `2 ^ 64`. -/
def frameNonnegB (body : Lcmd) (G : Nat) : Bool :=
  (frameOffs body).all fun o => decide (0 ≤ o ∧ o.toNat + 16 + G ≤ 2 ^ 64)

/-- **Soundness of the frame check.** The restricted frame of a body accepted by
    `frameNonnegB` lies above the stack register after the prologue. -/
theorem frameAbove_of_frameNonnegB {body : Lcmd} {G : Nat} (h : frameNonnegB body G = true)
    (sa0 : AState) :
    FrameAbove (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0)))
      (frameRsp body sa0) G := by
  intro q a ha
  obtain ⟨hq, o, ho, rfl⟩ := frameIn_some ha
  have hm : o ∈ frameOffs body :=
    List.mem_filterMap.mpr ⟨q, List.mem_eraseDups.mpr hq, ho⟩
  have hb := List.all_eq_true.mp h o hm
  simp only [decide_eq_true_eq] at hb
  refine ⟨o.toNat, hb.2, ?_⟩
  rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg hb.1]
  simp only [frameRsp, BitVec.add_assoc, ← BitVec.ofInt_add]
  congr 2
  simp only [Int.ofNat_eq_natCast]
  omega

/-- **The separation of a caller at a call.** The frame words lie above the stack register
    (`FrameAbove`), and no byte of an array word is a byte of the return word or among the
    `G` bytes below it. -/
structure CallerSep (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) (rsp : BitVec 64)
    (G : Nat) : Prop where
  /-- The frame words lie above the stack register. -/
  frames : FrameAbove frame rsp G
  /-- The array words do not meet the return word and the `G` bytes below it. -/
  cells : ∀ q A n j, slotArr q = some (A, n) → j < n →
    ∀ x, InRange8 (cellAt (base A) j) x →
      ¬ InRange8 (rsp + BitVec.ofInt 64 (-8)) x ∧ ¬ InFrame (rsp + BitVec.ofInt 64 (-8)) G x

/-- The footprint of the callee is among the `G` bytes below its entry stack register. -/
def FootBelow (c : CalleeSig) (G : Nat) : Prop :=
  ∀ s x, c.foot s x → InFrame (s.regs "%rsp") G x

/-- **The footprint and the return word are clear of the caller.** Under `CallerSep` at the
    stack register of the byte state, for a callee whose footprint is among the `G` bytes
    below its entry stack register, the frame words and the array words lie outside the
    footprint and the return word. -/
theorem footClear_of_callerSep {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) {c : CalleeSig} (hF : FootBelow c G)
    {sA : AState} (hsp : sA.regs "%rsp" = rsp) (ret : Nat) :
    FootClear frame slotArr base
      fun x => c.foot (entryOf ret sA) x ∨ InRange8 (retWord sA) x := by
  have he : (entryOf ret sA).regs "%rsp" = rsp + BitVec.ofInt 64 (-8) := by
    rw [entryOf_regs, ite_eq_left rfl, retWord, hsp]
  have hr : retWord sA = rsp + BitVec.ofInt 64 (-8) := by rw [retWord, hsp]
  refine ⟨fun q a ha x hx hT => ?_, fun q A n j hq hj x hx hT => ?_⟩
  · obtain ⟨o, h1, rfl⟩ := hS.frames q a ha
    rcases hT with hT | hT
    · exact above_not_inFrame rsp x o G h1 hx (he ▸ hF _ x hT)
    · exact above_not_retWord rsp x o (by omega) hx (hr ▸ hT)
  · obtain ⟨n1, n2⟩ := hS.cells q A n j hq hj x hx
    rcases hT with hT | hT
    · exact n2 (he ▸ hF _ x hT)
    · exact n1 (hr ▸ hT)

/-! ## 5. The word reading of a callee -/

/-- **The reading of an interface as a procedure summary on words.** The argument names and
    the result name `res` are general-purpose names and the register of `res` is in the
    clobber set; the precondition holds at an entry state that satisfies `room` and at
    whose argument registers the summary is defined; the postcondition gives the word of
    the summary in the register of `res` at the return; and every argument of the summary
    is a word. -/
structure WordCallee (c : CalleeSig) (res : String) (pr : LprogIsa.ProcSummary)
    (room : AState → Prop) : Prop where
  /-- The argument names are general-purpose names. -/
  args_gp : ∀ a ∈ c.args, gpOk a = true
  /-- The result register of the interface is that of `res`. -/
  res_eq : c.res = some res
  /-- The result name is a general-purpose name. -/
  res_gp : gpOk res = true
  /-- The register of the result name is in the clobber set. -/
  res_clob : c.clob (phys res) = true
  /-- The precondition, from `room` and a defined summary. -/
  pre : ∀ s, room s → (pr.run (c.args.map fun a => s.regs (phys a))).isSome = true → c.pre s
  /-- The result register at the return holds the word of the summary. -/
  post : ∀ s s', c.pre s → c.post s s' →
    pr.run (c.args.map fun a => s.regs (phys a)) = some (s'.regs (phys res))
  /-- Every argument of the summary is a word. -/
  wordOnly : pr.WordOnly := by exact rfl
  /-- The summary has no word-array result. -/
  wordRet : pr.RetWord := by exact rfl

/-- **The argument registers at the entry of a call hold the argument words of the image.**
    Under `ImgRel` and `ACorr`, the words of the general-purpose argument names in the image
    state are the values of their machine registers in the entry state of the call. -/
theorem args_entry {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) {args : List String}
    (hargs : ∀ a ∈ args, gpOk a = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {sA : AState} (hc : ACorr rsp sA sa)
    (ret : Nat) :
    args.map (fun a => (entryOf ret sA).regs (phys a)) = args.map (argWord s.prog.base.reg) := by
  refine List.map_congr_left fun a ha => ?_
  have hg := hargs a ha
  rw [entryOf_regs, ite_eq_right (gpFacts hg).physNe, argWord_congr (hrel.regs a (hsep.gp a hg))]
  simp [argWord, hc.regs a hg]

/-- **The precondition of the callee from the image relation.** Under `ImgRel` and `ACorr`,
    if the entry state of the call satisfies `room` and the summary is defined at the
    argument words of the image state, the entry state satisfies the precondition. -/
theorem pre_of_image {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) {c : CalleeSig} {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {s : LstateMF} {sa : LstateA} {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf)
    {sA : AState} (hc : ACorr rsp sA sa) (ret : Nat) (hroom : room (entryOf ret sA))
    {v : BitVec 64} (hv : pr.run (c.args.map (argWord s.prog.base.reg)) = some v) :
    c.pre (entryOf ret sA) := by
  refine hw.pre _ hroom ?_
  rw [args_entry hsep hw.args_gp hrel hc ret, hv]
  rfl

/-! ## 6. The relation up to names and flags -/

/-- Two image states agree off the names of `X` and the three flags: on the other names,
    the program counter, the arrays and the function name. -/
structure AgreeOffF (X : List String) (s s' : LstateMF) : Prop where
  regs : ∀ r, r ∉ X → s.prog.base.reg.lvm r = s'.prog.base.reg.lvm r
  pc : s.prog.base.reg.lpc = s'.prog.base.reg.lpc
  arr : s.prog.base.larr = s'.prog.base.larr
  fn : s.prog.lfn = s'.prog.lfn

/-- **The relaxed relation**: `ImgRel` up to the values of the names in `X` and of the
    three flags. The image state agrees off `X` and the flags with a state related to the
    address state at some zero flag. -/
def ImgRelF (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (body : Lcmd) (X : List String) (s : LstateMF)
    (sa : LstateA) : Prop :=
  ∃ s' zf, AgreeOffF X s s' ∧ ImgRel frame slotArr base body s' sa zf

/-- The relation gives the relaxed relation at every list of names. -/
theorem imgRelF_of_imgRel {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (X : List String) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (h : ImgRel frame slotArr base body s sa zf) : ImgRelF frame slotArr base body X s sa :=
  ⟨s, zf, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, h⟩

/-- The relaxed relation gives the program counter of the address state. -/
theorem ImgRelF.pc {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {X : List String} {s : LstateMF} {sa : LstateA}
    (h : ImgRelF frame slotArr base body X s sa) : sa.reg.lpc = s.prog.base.reg.lpc := by
  obtain ⟨s', zf, hag, hrel⟩ := h
  exact hrel.pc.trans hag.pc.symm

/-- The names exempted after a call: the general-purpose names whose machine register is
    in the clobber set, other than the result name. -/
def exemptC (c : CalleeSig) : List String :=
  gpList.filter fun r => c.clob (phys r) && (c.res != some r)

/-- The step of a procedure summary with the result word `v` agrees with the summary step
    of the call off the exempted names and the flags, when the oracle holds `v` at the
    result name. -/
theorem agreeOffF_retWord (c : CalleeSig) (ω : CallOut) (s : LstateMF) {res : String}
    {v : BitVec 64} (hres : c.res = some res) (hcl : clobN c res = true)
    (hv : ω.reg res = v) :
    AgreeOffF (exemptC c) (LprogIsa.retWord res v s) (callSumC c ω s) := by
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  show (if r = res then (⟨64, v⟩ : Σ w, BitVec w) else s.prog.base.reg.lvm r)
    = (if clobN c r then ⟨64, ω.reg r⟩ else s.prog.base.reg.lvm r)
  by_cases h1 : r = res
  · subst h1
    rw [ite_eq_left rfl, ite_eq_left hcl, hv]
  · rw [ite_eq_right h1]
    split_ifs with h2
    · exfalso
      apply hr
      simp only [clobN, Bool.and_eq_true] at h2
      simp only [exemptC, List.mem_filter, Bool.and_eq_true, bne_iff_ne, hres]
      exact ⟨mem_gpList h2.1, h2.2, fun e => h1 (Option.some.inj e).symm⟩
    · rfl

/-- Agreement off `X` gives agreement off every list that contains `X`. -/
theorem AgreeOffF.mono {X Y : List String} {s s' : LstateMF} (h : AgreeOffF X s s')
    (hs : ∀ r ∈ X, r ∈ Y) : AgreeOffF Y s s' :=
  ⟨fun r hr => h.regs r fun hx => hr (hs r hx), h.pc, h.arr, h.fn⟩

/-- Agreement off `X` followed by agreement off `Y` is agreement off `X ++ Y`. -/
theorem AgreeOffF.trans {X Y : List String} {s s' s'' : LstateMF} (h : AgreeOffF X s s')
    (h' : AgreeOffF Y s' s'') : AgreeOffF (X ++ Y) s s'' :=
  ⟨fun r hr => (h.regs r fun hx => hr (List.mem_append_left _ hx)).trans
      (h'.regs r fun hx => hr (List.mem_append_right _ hx)),
    h.pc.trans h'.pc, h.arr.trans h'.arr, h.fn.trans h'.fn⟩

/-- The step of a procedure summary with one result word, from two states that agree off
    `X`, gives states that agree off the names of `X` other than the result name. -/
theorem AgreeOffF.retWord {X : List String} {s s' : LstateMF} (h : AgreeOffF X s s')
    (res : String) (v : BitVec 64) :
    AgreeOffF (X.filter fun r => r != res) (LprogIsa.retWord res v s)
      (LprogIsa.retWord res v s') := by
  refine ⟨fun r hr => ?_, congrArg (· + 1) h.pc, h.arr, h.fn⟩
  show (if r = res then (⟨64, v⟩ : Σ w, BitVec w) else s.prog.base.reg.lvm r)
    = (if r = res then ⟨64, v⟩ else s'.prog.base.reg.lvm r)
  by_cases h1 : r = res
  · rw [ite_eq_left h1, ite_eq_left h1]
  · rw [ite_eq_right h1, ite_eq_right h1]
    exact h.regs r fun hx => hr (List.mem_filter.mpr ⟨hx, by simpa using h1⟩)

/-- The relaxed relation at `X` gives the relaxed relation at every list that contains
    `X`. -/
theorem ImgRelF.mono {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {X Y : List String} {s : LstateMF} {sa : LstateA}
    (h : ImgRelF frame slotArr base body X s sa) (hs : ∀ r ∈ X, r ∈ Y) :
    ImgRelF frame slotArr base body Y s sa := by
  obtain ⟨s', zf, hag, hrel⟩ := h
  exact ⟨s', zf, hag.mono hs, hrel⟩

/-! ## 6a. The congruence of a described step up to dead names and dead flags -/

section Dead

open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-- **Agreement up to dead names and dead flags.** Two image states agree off the names of
    `X`; they have the same zero flag when `z` holds, and the same carry and overflow flags
    when `c` holds. -/
structure AgreeOffD (X : List String) (z c : Bool) (s s' : LstateMF) : Prop where
  /-- Agreement off the names of `X`. -/
  off : AgreeOffF X s s'
  /-- The zero flags, when `z` holds. -/
  zf : z = true → s.zf = s'.zf
  /-- The carry and overflow flags, when `c` holds. -/
  cf : c = true → s.prog.base.cf = s'.prog.base.cf ∧ s.prog.base.of = s'.prog.base.of

/-- Agreement off `X` is agreement up to `X` with every flag dead. -/
theorem agreeOffD_of_agreeOffF {X : List String} {s s' : LstateMF} (h : AgreeOffF X s s') :
    AgreeOffD X false false s s' :=
  ⟨h, fun e => Bool.noConfusion e, fun e => Bool.noConfusion e⟩

/-- Agreement up to dead names and flags gives agreement at a larger list of names and at
    weaker flag conditions. -/
theorem AgreeOffD.mono {X Y : List String} {z c z' c' : Bool} {s s' : LstateMF}
    (h : AgreeOffD X z c s s') (hs : ∀ r ∈ X, r ∈ Y) (hz : z' = true → z = true)
    (hc : c' = true → c = true) : AgreeOffD Y z' c' s s' :=
  ⟨h.off.mono hs, fun e => h.zf (hz e), fun e => h.cf (hc e)⟩

/-- The start registers a one-step description reads: those of `ImageAddrSim.descReads` and
    those in its written arrays. -/
def descReadsA (ss : SSt) (gs : List SG) : List String :=
  descReads ss gs ++ ss.awr.flatMap fun a => (ss.arrs a).vars

/-- A guard, a written register or a written array of the description reads the carry or
    the overflow flag of the start. -/
def descReadsF (ss : SSt) (gs : List SG) : Bool :=
  gs.any SG.readsF || ss.wr.any (fun r => (ss.regs r).readsF)
    || ss.awr.any (fun a => (ss.arrs a).readsF)

/-- The zero flags agree after a step with the symbolic zero flag `f`, from states whose
    zero flags agree when `z` holds and whose carry and overflow flags agree when `c`
    holds: an unchanged flag keeps `z`, and the flag of a compare agrees when `c` holds or
    its operands read no flag. -/
def zNext (z c : Bool) : SFlag → Bool
  | .init => z
  | .cmp x y => c || !(x.readsF || y.readsF)

/-- The carry and overflow flags agree after a step with the description `ss`, from states
    whose carry and overflow flags agree when `c` holds. -/
def cNext (c : Bool) (ss : SSt) : Bool := c || (!ss.cf.readsF && !ss.of.readsF)

theorem descReadsF_guard {ss : SSt} {gs : List SG} (h : descReadsF ss gs = false) {g : SG}
    (hg : g ∈ gs) : g.readsF = false := by
  simp only [descReadsF, Bool.or_eq_false_iff, List.any_eq_false] at h
  simpa using h.1.1 g hg

theorem descReadsF_reg {ss : SSt} {gs : List SG} (h : descReadsF ss gs = false) {r : String}
    (hr : r ∈ ss.wr) : (ss.regs r).readsF = false := by
  simp only [descReadsF, Bool.or_eq_false_iff, List.any_eq_false] at h
  simpa using h.1.2 r hr

theorem descReadsF_arr {ss : SSt} {gs : List SG} (h : descReadsF ss gs = false) {a : String}
    (ha : a ∈ ss.awr) : (ss.arrs a).readsF = false := by
  simp only [descReadsF, Bool.or_eq_false_iff, List.any_eq_false] at h
  simpa using h.2 a ha

/-- A symbolic zero flag has one value at two starts that agree on the registers it reads,
    under the flag conditions of `zNext`. -/
theorem sflag_ev_congrD {V V' : String → Σ w, BitVec w} (A : String → ArrCell)
    {C O C' O' Z Z' : Bool} {z c : Bool} (f : SFlag) (h : ∀ r ∈ f.vars, V r = V' r)
    (hz : z = true → Z = Z') (hc : c = true → C = C' ∧ O = O')
    (hn : zNext z c f = true) : f.ev V A C O Z = f.ev V' A C' O' Z' := by
  cases f with
  | init => exact hz hn
  | cmp x y =>
      simp only [zNext, Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at hn
      have hf : ∀ b : Bool, (c = true ∨ b = false) → b = true → C = C' ∧ O = O' :=
        fun b hb e => hb.elim hc fun hn' => by rw [hn'] at e; cases e
      simp only [SFlag.ev,
        STerm.ev_congr A x (fun r hr => h r (by simp [SFlag.vars, hr]))
          (hf _ (hn.imp id fun q => q.1)),
        STerm.ev_congr A y (fun r hr => h r (by simp [SFlag.vars, hr]))
          (hf _ (hn.imp id fun q => q.2))]

/-- **The congruence of a described step up to dead names and dead flags.** Let the
    symbolic step of `i` from the start state be `ok ss gs`. Let `s` and `s'` agree off the
    names of `X`, on the zero flag when `z` holds and on the carry and overflow flags when
    `c` holds; let the description read no name of `X`, and read the carry and overflow
    flags only when `c` holds. Then a successful step from `s` is matched by a successful
    step from `s'`, and the results agree off the names of `X` that the step does not
    write, on the zero flag when `zNext z c ss.zf` holds, and on the carry and overflow
    flags when `cNext c ss` holds. -/
theorem step_congrD (P P' : LprogM) (i : LinstrRM) {ss : SSt} {gs : List SG}
    (h : symStep i SSt.start = .ok ss gs) {X : List String} {z c : Bool} {s s' t : LstateMF}
    (hag : AgreeOffD X z c s s') (hrd : ∀ r ∈ descReadsA ss gs, r ∉ X)
    (hfl : c = true ∨ descReadsF ss gs = false) (hs : evalInstrPMemF P i s = some t) :
    ∃ t', evalInstrPMemF P' i s' = some t'
      ∧ AgreeOffD (X.filter fun r => !ss.wr.contains r) (zNext z c ss.zf) (cNext c ss) t t' := by
  have hg := symStep_good i SSt.good_start h
  have hA : s'.prog.base.larr = s.prog.base.larr := hag.off.arr.symm
  have hD := symStep_sound P i SSt.start s.prog.base.reg.lvm s.prog.base.larr s.prog.base.cf
    s.prog.base.of s.zf s (holds_start s)
  have hD' := symStep_sound P' i SSt.start s'.prog.base.reg.lvm s.prog.base.larr
    s'.prog.base.cf s'.prog.base.of s'.zf s' (by rw [← hA]; exact holds_start s')
  rw [h] at hD hD'
  obtain ⟨hG, hH, hF⟩ := hD.1 t hs
  have hv : ∀ r ∈ descReadsA ss gs, s.prog.base.reg.lvm r = s'.prog.base.reg.lvm r :=
    fun r hr => hag.off.regs r (hrd r hr)
  have hfc : ∀ b : Bool, (c = true ∨ b = false) → b = true →
      s.prog.base.cf = s'.prog.base.cf ∧ s.prog.base.of = s'.prog.base.of :=
    fun b hb e => hb.elim hag.cf fun hn => by rw [hn] at e; cases e
  have hG' : AllG s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of gs := by
    intro g hgm
    refine (SG.holds_congr _ g (fun r hr => hv r ?_)
      (hfc _ (hfl.imp id fun hn => descReadsF_guard hn hgm))).mp (hG g hgm)
    simp only [descReadsA, descReads, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨g, hgm, hr⟩))))
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (hD'.2 hG')
  obtain ⟨-, hH', hF'⟩ := hD'.1 t' ht'
  have hnw : ∀ r, r ∉ ss.wr → t.prog.base.reg.lvm r = s.prog.base.reg.lvm r := fun r hr => by
    rw [hH.1 r, hg.1 r hr]; rfl
  have hnw' : ∀ r, r ∉ ss.wr → t'.prog.base.reg.lvm r = s'.prog.base.reg.lvm r := fun r hr => by
    rw [hH'.1 r, hg.1 r hr]; rfl
  refine ⟨t', ht', ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, fun hz => ?_, fun hc => ?_⟩⟩
  · by_cases hw : r ∈ ss.wr
    · rw [hH.1 r, hH'.1 r]
      refine STerm.ev_congr _ _ (fun q hq => hv q ?_)
        (hfc _ (hfl.imp id fun hn => descReadsF_reg hn hw))
      simp only [descReadsA, descReads, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨r, hw, hq⟩))))
    · rw [hnw r hw, hnw' r hw]
      exact hag.off.regs r fun hx => hr (List.mem_filter.mpr ⟨hx, by simpa using hw⟩)
  · rw [hF.2.1, hF'.2.1, hag.off.pc]
  · funext q
    rw [hH.2.1 q, hH'.2.1 q]
    by_cases hw : q ∈ ss.awr
    · refine SArr.ev_congr _ _ (fun r hr => hv r ?_)
        (hfc _ (hfl.imp id fun hn => descReadsF_arr hn hw))
      simp only [descReadsA, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨q, hw, hr⟩
    · rw [hg.2 q hw]
      rfl
  · rw [hF.1, hF'.1, hag.off.fn]
  · rw [hH.2.2.1, hH'.2.2.1]
    refine sflag_ev_congrD _ ss.zf (fun r hr => hv r ?_) hag.zf hag.cf hz
    simp only [descReadsA, descReads, List.mem_append]
    exact Or.inl (Or.inr hr)
  · simp only [cNext, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
    constructor
    · rw [hH.2.2.2.1, hH'.2.2.2.1]
      congr 1
      refine STerm.ev_congr _ _ (fun r hr => hv r ?_) (hfc _ (hc.imp id fun q => q.1))
      simp only [descReadsA, descReads, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inr hr)))
    · rw [hH.2.2.2.2, hH'.2.2.2.2]
      congr 1
      refine STerm.ev_congr _ _ (fun r hr => hv r ?_) (hfc _ (hc.imp id fun q => q.2))
      simp only [descReadsA, descReads, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hr))

/-- **A table of dead names and dead flags**: at each position of a body, the names whose
    values are not read before they are written, whether the zero flag is live, and whether
    the carry and overflow flags are live. -/
structure DeadTab where
  /-- The dead names at a position. -/
  dead : Nat → List String
  /-- The zero flag is live at a position. -/
  z : Nat → Bool
  /-- The carry and overflow flags are live at a position. -/
  c : Nat → Bool

/-- **The check of a described instruction `i` at position `k` against a table**: the
    symbolic step is `ok ss gs`; the description reads no dead name; it reads the carry and
    overflow flags only where they are live; a dead name the step does not write is dead at
    `k + 1`; and a flag live at `k + 1` is live after the step (`zNext`, `cNext`). -/
def deadStepB (D : DeadTab) (k : Nat) (i : LinstrRM) : Bool :=
  match symStep i SSt.start with
  | .ok ss gs =>
      (descReadsA ss gs).all (fun r => !(D.dead k).contains r)
        && (D.c k || !descReadsF ss gs)
        && ((D.dead k).filter fun r => !ss.wr.contains r).all
            (fun r => (D.dead (k + 1)).contains r)
        && (!D.z (k + 1) || zNext (D.z k) (D.c k) ss.zf)
        && (!D.c (k + 1) || cNext (D.c k) ss)
  | _ => false

/-- **A checked step keeps the agreement of the table.** For an instruction that passes
    `deadStepB` at position `k`, from two states that agree up to the dead names and the
    dead flags of position `k`, a successful step from the first is matched by a successful
    step from the second, and the results agree up to the dead names and the dead flags of
    position `k + 1`. -/
theorem step_deadStepB (P P' : LprogM) {D : DeadTab} {k : Nat} {i : LinstrRM}
    (hk : deadStepB D k i = true) {s s' t : LstateMF}
    (hag : AgreeOffD (D.dead k) (D.z k) (D.c k) s s') (hs : evalInstrPMemF P i s = some t) :
    ∃ t', evalInstrPMemF P' i s' = some t'
      ∧ AgreeOffD (D.dead (k + 1)) (D.z (k + 1)) (D.c (k + 1)) t t' := by
  unfold deadStepB at hk
  split at hk
  · rename_i ss gs heq
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hk
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hk
    obtain ⟨t', ht', hag'⟩ := step_congrD P P' i heq hag
      (fun r hr => by simpa using h1 r hr) h2 hs
    exact ⟨t', ht', hag'.mono (fun r hr => by simpa using h3 r hr)
      (fun e => h4.resolve_left (by rw [e]; exact Bool.noConfusion))
      (fun e => h5.resolve_left (by rw [e]; exact Bool.noConfusion))⟩
  · cases hk

/-- **The table at `j` is no stronger than the table at `k`**: a name dead at `k` is dead at
    `j`, and a flag live at `j` is live at `k`. -/
def DeadTab.le (D : DeadTab) (k j : Nat) : Bool :=
  (D.dead k).all (fun r => (D.dead j).contains r) && (!D.z j || D.z k) && (!D.c j || D.c k)

/-- Agreement at the table of `k` gives agreement at a table that is no stronger. -/
theorem AgreeOffD.of_le {D : DeadTab} {k j : Nat} (h : D.le k j = true) {s s' : LstateMF}
    (hag : AgreeOffD (D.dead k) (D.z k) (D.c k) s s') :
    AgreeOffD (D.dead j) (D.z j) (D.c j) s s' := by
  simp only [DeadTab.le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact hag.mono (fun r hr => by simpa using h1 r hr)
    (fun e => h2.resolve_left (by rw [e]; exact Bool.noConfusion))
    (fun e => h3.resolve_left (by rw [e]; exact Bool.noConfusion))

/-- **The check of a control instruction at position `k` of the body `B` against a table.**
    A label: the table at `k + 1` is no stronger. A conditional jump: its condition is a
    condition code, the zero flag is live at `k`, and the tables at `k + 1` and after the
    target label are no stronger. A jump: the table after the target label is no
    stronger. -/
def deadCtlB (D : DeadTab) (B : List LinstrRM) (k : Nat) : LinstrR → Bool
  | .Llabel _ _ => D.le k (k + 1)
  | .Lcond c l => (ccPol c).isSome && D.z k && D.le k (k + 1)
      && (findLabelMem l B).all fun q => D.le k (q + 1)
  | .Lgoto (_, l) => (findLabelMem l B).all fun q => D.le k (q + 1)
  | _ => false

/-- Two states agree up to the dead names and the dead flags of the table at their
    position. -/
def DeadAgree (D : DeadTab) (s s' : LstateMF) : Prop :=
  AgreeOffD (D.dead s.prog.base.reg.lpc) (D.z s.prog.base.reg.lpc) (D.c s.prog.base.reg.lpc)
    s s'

/-- **A checked control step keeps the agreement of the table.** -/
theorem ctl_deadStep {D : DeadTab} {fn : String} {B : List LinstrRM} {i : LinstrRM}
    {s s' t : LstateMF} (hk : deadCtlB D B s.prog.base.reg.lpc i.fst = true)
    (hag : DeadAgree D s s')
    (hs : LprogIsa.ctlStep decC (singletonProgM fn B) i s = some t) :
    ∃ t', LprogIsa.ctlStep decC (singletonProgM fn B) i s' = some t' ∧ DeadAgree D t t' := by
  obtain ⟨x, tag⟩ := i
  have hjump : ∀ (l : LLabel) (t : LstateMF),
      ((findLabelMem l B).all fun q => D.le s.prog.base.reg.lpc (q + 1)) = true →
      (evalJumpMem (singletonProgM fn B) l s.prog).map (fun p => { s with prog := p }) = some t →
      ∃ t', (evalJumpMem (singletonProgM fn B) l s'.prog).map (fun p => { s' with prog := p })
          = some t' ∧ DeadAgree D t t' := by
    intro l t hl ht
    have hbody : (singletonProgM fn B).body = B := rfl
    unfold evalJumpMem at ht ⊢
    rw [hbody] at ht ⊢
    cases hf : findLabelMem l B with
    | none => rw [hf] at ht; cases ht
    | some q =>
        rw [hf] at ht hl
        simp only [Option.map_some, Option.some.injEq] at ht
        subst ht
        have h2 := AgreeOffD.of_le (by simpa using hl) hag
        exact ⟨_, rfl, ⟨fun r hr => h2.off.regs r hr, rfl, h2.off.arr, h2.off.fn⟩, h2.zf, h2.cf⟩
  cases x with
  | Llabel kd l =>
      cases hs
      have h2 := AgreeOffD.of_le hk hag
      exact ⟨_, rfl, ⟨fun r hr => h2.off.regs r hr, congrArg (· + 1) hag.off.pc, h2.off.arr,
        h2.off.fn⟩, h2.zf, h2.cf⟩
  | Lcond c l =>
      simp only [deadCtlB, Bool.and_eq_true] at hk
      obtain ⟨⟨⟨hcc, hz⟩, hnext⟩, htgt⟩ := hk
      have hd : decC s' c = decC s c := by
        unfold decC
        cases hp : ccPol c with
        | none => rw [hp] at hcc; cases hcc
        | some pol => simp only [hag.zf hz]
      simp only [LprogIsa.ctlStep] at hs ⊢
      rw [hd]
      split at hs
      · rename_i hc
        rw [ite_eq_left hc]
        exact hjump l t htgt hs
      · rename_i hc
        rw [ite_eq_right hc]
        cases hs
        have h2 := AgreeOffD.of_le hnext hag
        exact ⟨_, rfl, ⟨fun r hr => h2.off.regs r hr, congrArg (· + 1) hag.off.pc, h2.off.arr,
          h2.off.fn⟩, h2.zf, h2.cf⟩
  | Lgoto tg =>
      obtain ⟨g, l⟩ := tg
      simp only [LprogIsa.ctlStep] at hs ⊢
      split at hs
      · rename_i hc
        rw [ite_eq_left hc]
        exact hjump l t hk hs
      · cases hs
  | _ => cases hk

/-- **The check of a body against a table**: every control instruction passes `deadCtlB`,
    and every other instruction is a shadow instruction of a call or passes `deadStepB`. -/
def deadSegB (D : DeadTab) (B : List LinstrRM) : Bool :=
  (List.range B.length).all fun k => (B[k]?).all fun i =>
    if LprogIsa.isCtl i.fst then deadCtlB D B k i.fst
    else (LprogIsa.shadowCall? i.fst).isSome || deadStepB D k i

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (Steps Halted atPc) in
/-- **A run of steps of a checked body keeps the agreement of the table.** From two states
    that agree up to the dead names and the dead flags of their position, a run of steps of
    the x86 instruction set on a body that passes `deadSegB` is matched by a run of the same
    number of steps, to states that agree up to the dead names and the dead flags of their
    position. -/
theorem steps_deadSeg {D : DeadTab} {fn : String} {B : List LinstrRM}
    (hD : deadSegB D B = true) :
    ∀ (n : Nat) (s s' u : LstateMF), DeadAgree D s s' →
      Steps X86Isa.x86Isa (singletonProgM fn B) n s u →
      ∃ u', Steps X86Isa.x86Isa (singletonProgM fn B) n s' u' ∧ DeadAgree D u u'
  | 0, s, s', u, hag, h => by
      have hsu : s = u := Option.some.inj h
      subst hsu
      exact ⟨s', rfl, hag⟩
  | n + 1, s, s', u, hag, h => by
      simp only [Steps, Ascent.CutPoint.iter, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨c, hc, h⟩ := h
      unfold LprogIsa.Isa.lsemStepPMemF at hc ⊢
      have hfe : findInstrMem (singletonProgM fn B) s'.prog
          = findInstrMem (singletonProgM fn B) s.prog := by
        unfold findInstrMem
        rw [← hag.off.fn]
        exact congrArg (fun q => if s.prog.lfn = fn then B[q]? else none) hag.off.pc.symm
      rw [hfe]
      cases hf : findInstrMem (singletonProgM fn B) s.prog with
      | none => rw [hf] at hc; cases hc
      | some i =>
          rw [hf] at hc
          dsimp only at hc
          have hBi : B[s.prog.base.reg.lpc]? = some i := by
            unfold findInstrMem at hf
            split at hf
            · exact hf
            · cases hf
          have hchk := List.all_eq_true.mp hD s.prog.base.reg.lpc
            (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hBi).1)
          rw [hBi] at hchk
          simp only [Option.all_some] at hchk
          have hstep : ∃ c', X86Isa.x86Isa.step (singletonProgM fn B) i s' = some c'
              ∧ DeadAgree D c c' := by
            by_cases hctl : LprogIsa.isCtl i.fst = true
            · rw [ite_eq_left hctl] at hchk
              rw [X86Isa.x86Isa.step_ctl _ _ _ hctl] at hc ⊢
              exact ctl_deadStep hchk hag hc
            · rw [ite_eq_right hctl] at hchk
              have hctl' : LprogIsa.isCtl i.fst = false := by simpa using hctl
              rw [X86Isa.x86Isa_step] at hc ⊢
              cases hsh : LprogIsa.shadowCall? i.fst with
              | some q =>
                  rw [LprogIsaProcs.evalInstrPMemF_shadowCall _ i s (by rw [hsh]; simp)] at hc
                  cases hc
              | none =>
                  rw [hsh] at hchk
                  obtain ⟨c', hc', hag'⟩ := step_deadStepB (singletonProgM fn B)
                    (singletonProgM fn B) (by simpa using hchk) hag hc
                  refine ⟨c', hc', ?_⟩
                  have e : c.prog.base.reg.lpc = s.prog.base.reg.lpc + 1 := by
                    have := LprogCallCut.x86Isa_pcFree.lpc_succ (singletonProgM fn B) hctl'
                      (by rw [X86Isa.x86Isa_step]; exact hc)
                    rw [this]
                    rfl
                  unfold DeadAgree
                  rw [e]
                  exact hag'
          obtain ⟨c', hc', hag'⟩ := hstep
          obtain ⟨u', hu', hagu⟩ := steps_deadSeg hD n c c' u hag' h
          exact ⟨u', ⟨c', hc', hu'⟩, hagu⟩

end Dead

/-! ## 7. A call re-establishes the relaxed relation, and the run continues -/

/-- **A call to a word callee re-establishes the relaxed relation.** Let `ImgRel` and
    `ACorr` hold at a call instruction of a body of the class `physImgB`, the callee meet
    its specification and have the word reading `pr`, the caller be separated (`CallerSep`)
    for a callee whose footprint is among the `G` bytes below its entry stack register, the
    entry state satisfy `room`, and the summary give the word `v` at the argument words of
    the image state. Then the entry state satisfies the precondition, and for every run of
    the callee, after the return: the result register holds `v`, and there is an address
    state at the next position that corresponds to the byte state and is related, up to the
    names `exemptC c` and the flags, to the image state after the step of the summary. -/
theorem call_reestablishes_word {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    {s : LstateMF} {sa : LstateA} {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf)
    {sA : AState} (hc : ACorr rsp sA sa) {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi)
    {ra : Option String} {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt) (ret : Nat)
    (hroom : room (entryOf ret sA)) {v : BitVec 64}
    (hv : pr.run (c.args.map (argWord s.prog.base.reg)) = some v) :
    c.pre (entryOf ret sA) ∧ ∀ t sc, X (entryOf ret sA) t sc →
      (retOps.foldl aMachine.exec sc).regs (phys res) = v
        ∧ ∃ sa', sa'.reg.lpc = sa.reg.lpc + 1
          ∧ ACorr rsp (retOps.foldl aMachine.exec sc) sa'
          ∧ ImgRelF frame slotArr base body (exemptC c) (LprogIsa.retWord res v s) sa' := by
  have hpre := pre_of_image hsep hw hrel hc ret hroom hv
  refine ⟨hpre, fun t sc hrun => ?_⟩
  obtain ⟨hA, hI, hpost⟩ := call_reestablishes hsep hphys hX hrel hc hb hbi ret hpre
    (footClear_of_callerSep hS hF hc.sp ret) hrun ⟨fun _ => 0, false, false, false⟩
  have hres : (retOps.foldl aMachine.exec sc).regs (phys res) = v := by
    have h1 := hw.post _ _ hpre hpost
    rw [args_entry hsep hw.args_gp hrel hc ret, hv] at h1
    rw [(call_return hX ret sA hpre hrun).2.1 _ (gpFacts hw.res_gp).physNe]
    exact (Option.some.inj h1).symm
  exact ⟨hres, _, rfl, hA, _, _,
    agreeOffF_retWord c (outOf (retOps.foldl aMachine.exec sc) _) s hw.res_eq
      (by simp [clobN, hw.res_gp, hw.res_clob]) hres,
    hI⟩

/-- **A call under the oracle of its callee, on the image.** Under the hypotheses of
    `call_reestablishes_word`, with index `pc` of `prog` a call to `tgt`: there are a byte
    state and an address state at the next position, corresponding by `ACorr`, with the
    result register holding `v` and the address state related up to the names `exemptC c`
    and the flags to the image state after the step of the summary, such that every run
    under the oracle from `pc + 1` on that byte state extends to a run from `pc`. -/
theorem haltsO_call_image {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    {s : LstateMF} {sa : LstateA} {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf)
    {sA : AState} (hc : ACorr rsp sA sa) {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi)
    {ra : Option String} {tgt' : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt')
    {prog : List RInstr} {pc tgt : Nat} (hcall : prog[pc]? = some (.call tgt))
    (hroom : room (entryOf (pc + 1) sA)) {v : BitVec 64}
    (hv : pr.run (c.args.map (argWord s.prog.base.reg)) = some v) :
    ∃ sA' sa', sA'.regs (phys res) = v ∧ sa'.reg.lpc = sa.reg.lpc + 1 ∧ ACorr rsp sA' sa'
      ∧ ImgRelF frame slotArr base body (exemptC c) (LprogIsa.retWord res v s) sa'
      ∧ ∀ s'', HaltsO aMachine (oracleAt tgt X) prog (pc + 1) sA' s'' →
          HaltsO aMachine (oracleAt tgt X) prog pc sA s'' := by
  obtain ⟨hpre, hall⟩ := call_reestablishes_word hsep hphys hX hw hS hF hrel hc hb hbi
    (pc + 1) hroom hv
  obtain ⟨t, sc, hrun⟩ := hX.halts _ hpre
  obtain ⟨hres, sa', hpc, hA, hI⟩ := hall t sc hrun
  exact ⟨_, sa', hres, hpc, hA, hI, fun s'' hr => .call hcall ⟨rfl, t, hrun⟩ hr⟩

/-- **A call under the oracle of its callee, from the relaxed relation.** As
    `haltsO_call_image`, from an image state related to the address state up to the names
    `E` and the flags, when no argument name of the callee is in `E`: the image state after
    the step of the summary is related to the address state at the next position up to the
    names of `E` other than the result name, the names `exemptC c`, and the flags. -/
theorem haltsO_call_imageF {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    {E : List String} {s : LstateMF} {sa : LstateA}
    (hI : ImgRelF frame slotArr base body E s sa) (hargs : ∀ a ∈ c.args, a ∉ E)
    {sA : AState} (hc : ACorr rsp sA sa) {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi)
    {ra : Option String} {tgt' : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt')
    {prog : List RInstr} {pc tgt : Nat} (hcall : prog[pc]? = some (.call tgt))
    (hroom : room (entryOf (pc + 1) sA)) {v : BitVec 64}
    (hv : pr.run (c.args.map (argWord s.prog.base.reg)) = some v) :
    ∃ sA' sa', sA'.regs (phys res) = v ∧ sa'.reg.lpc = sa.reg.lpc + 1 ∧ ACorr rsp sA' sa'
      ∧ ImgRelF frame slotArr base body ((E.filter fun r => r != res) ++ exemptC c)
          (LprogIsa.retWord res v s) sa'
      ∧ ∀ s'', HaltsO aMachine (oracleAt tgt X) prog (pc + 1) sA' s'' →
          HaltsO aMachine (oracleAt tgt X) prog pc sA s'' := by
  obtain ⟨s', zf, hag, hrel⟩ := hI
  have hv' : pr.run (c.args.map (argWord s'.prog.base.reg)) = some v := by
    rw [← hv]
    congr 1
    exact List.map_congr_left fun a ha => (argWord_congr (hag.regs a (hargs a ha))).symm
  obtain ⟨sA', sa', hres, hpc, hA, ⟨w, zf', hag2, hrel2⟩, hcont⟩ :=
    haltsO_call_image hsep hphys hX hw hS hF hrel hc hb hbi hcall hroom hv'
  exact ⟨sA', sa', hres, hpc, hA, ⟨w, zf', (hag.retWord res v).trans hag2, hrel2⟩, hcont⟩

/-! ## 7a. The call step at a result of a call -/

/-- **The call step of a callee at the result `x` written to `dst`.** From an image state `u`
    related by `ImgRel` to an address state at a call instruction that corresponds to a byte
    state, at every return index: the entry state of the call satisfies the precondition of
    `c`, and for every run of the callee there is an address state at the next position that
    corresponds to the byte state after the return and is related, up to the names
    `exemptC c` and the flags, to `LprogIsa.retRes dst x u`. -/
def ResStep (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (rsp : BitVec 64) (body : Lcmd) (X : CalleeRun)
    (c : CalleeSig) (dst : String) (x : LprogIsa.CallRes) (u : LstateMF) : Prop :=
  ∀ sa zf sA, ImgRel frame slotArr base body u sa zf → ACorr rsp sA sa →
    (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) → ∀ ret,
    c.pre (entryOf ret sA) ∧ ∀ t sc, X (entryOf ret sA) t sc →
      ∃ sa', sa'.reg.lpc = sa.reg.lpc + 1 ∧ ACorr rsp (retOps.foldl aMachine.exec sc) sa'
        ∧ ImgRelF frame slotArr base body (exemptC c) (LprogIsa.retRes dst x u) sa'

/-- **The call step of a word callee** at the word `v` of the summary at the argument words
    of the image state, from `call_reestablishes_word`. -/
theorem resStep_word {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    (hroom : ∀ ret sA, sA.regs "%rsp" = rsp → room (entryOf ret sA)) {u : LstateMF}
    {v : BitVec 64} (hv : pr.run (c.args.map (argWord u.prog.base.reg)) = some v) :
    ResStep frame slotArr base rsp body X c res (.word v) u := by
  intro sa zf sA hrel hc hcall ret
  obtain ⟨bi, ra, t, hb, hbi⟩ := hcall
  obtain ⟨hpre, hall⟩ := call_reestablishes_word hsep hphys hX hw hS hF hrel hc hb hbi ret
    (hroom ret sA hc.sp) hv
  exact ⟨hpre, fun t sc hrun => (hall t sc hrun).2⟩

/-- The names dead after the result `x` is written to `dst`, from the names `E` dead before:
    for a word, the names of `E` other than `dst`; for an array, the names of `E`. -/
def deadAfter (dst : String) : LprogIsa.CallRes → List String → List String
  | .word _, E => E.filter fun r => r != dst
  | .arr _, E => E

/-- The write of a result of a call, from two states that agree off `X`, gives states that
    agree off the names `deadAfter dst x X`. -/
theorem AgreeOffF.retRes {X : List String} {s s' : LstateMF} (h : AgreeOffF X s s')
    (dst : String) (x : LprogIsa.CallRes) :
    AgreeOffF (deadAfter dst x X) (LprogIsa.retRes dst x s) (LprogIsa.retRes dst x s') := by
  cases x with
  | word v => exact h.retWord dst v
  | arr a =>
    refine ⟨fun r hr => h.regs r hr, congrArg (· + 1) h.pc, ?_, h.fn⟩
    show (s.prog.base.setArr dst a).larr = (s'.prog.base.setArr dst a).larr
    unfold LstateM.setArr
    rw [h.arr]

/-- **The step of a call site** from the image state `u` to `v`, at the names `E` dead before
    the call and `E'` dead after it: `v` is the write of a result `x` to a destination `dst`,
    the callee has the call step at `x` from every state that agrees with `u` off `E`, and the
    names `deadAfter dst x E` and `exemptC c` are among `E'`. -/
def SiteStep (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (rsp : BitVec 64) (body : Lcmd) (X : CalleeRun)
    (c : CalleeSig) (E E' : List String) (u v : LstateMF) : Prop :=
  ∃ dst x, v = LprogIsa.retRes dst x u
    ∧ (∀ u', AgreeOffF E u u' → ResStep frame slotArr base rsp body X c dst x u')
    ∧ ∀ r ∈ deadAfter dst x E ++ exemptC c, r ∈ E'

/-- **A call site under the oracle of its callee, from the relaxed relation.** From an image
    state `u` related up to the names `E` and the flags to an address state at a call that
    corresponds to a byte state, with the step of the site from `u` to `v` at `E` and `E'`
    and index `pc` of `prog` a call to `tgt`: there are a byte state and an address state at
    the next position, corresponding by `ACorr`, with the address state related up to `E'`
    and the flags to `v`, such that every run under the oracle from `pc + 1` on that byte
    state extends to a run from `pc`. -/
theorem haltsO_call_imageS {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {E E' : List String} {u v : LstateMF} {sa : LstateA}
    (hI : ImgRelF frame slotArr base body E u sa)
    (hst : SiteStep frame slotArr base rsp body X c E E' u v)
    {sA : AState} (hc : ACorr rsp sA sa)
    (hcall' : ∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t)
    {prog : List RInstr} {pc tgt : Nat} (hcall : prog[pc]? = some (.call tgt)) :
    ∃ sA' sa', sa'.reg.lpc = sa.reg.lpc + 1 ∧ ACorr rsp sA' sa'
      ∧ ImgRelF frame slotArr base body E' v sa'
      ∧ ∀ s'', HaltsO aMachine (oracleAt tgt X) prog (pc + 1) sA' s'' →
          HaltsO aMachine (oracleAt tgt X) prog pc sA s'' := by
  obtain ⟨dst, x, rfl, hres, hsub⟩ := hst
  obtain ⟨u', zf, hag, hrel⟩ := hI
  obtain ⟨hpre, hall⟩ := hres u' hag sa zf sA hrel hc hcall' (pc + 1)
  obtain ⟨t, sc, hrun⟩ := hX.halts _ hpre
  obtain ⟨sa', hpc, hA, w, zf', hag2, hrel2⟩ := hall t sc hrun
  exact ⟨_, sa', hpc, hA, ⟨w, zf', ((hag.retRes dst x).trans hag2).mono hsub, hrel2⟩,
    fun s'' hr => .call hcall ⟨rfl, t, hrun⟩ hr⟩

/-! ## 8. Chains of segments -/

open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (RunChain SegTo Glue runChain_of_run)

/-- **The statement of the simulation of one segment** of the image of a calling body by
    the decoded program `prog` under the oracle `O`, with `pos` the index in `prog` of a
    position of the body, `E` the dead names at each position and `L` the positions at
    which a flag is live. From an image state in the function `fn` related, up to the dead
    names of its position and the flags, to an address state that corresponds to a byte
    state, at a position of the body where no flag is live:

    * a segment to the call at position `p` reaches an image state related, up to the dead
      names of `p` and the flags, to an address state at `p` that corresponds to a byte
      state; position `p` of the body is a call, index `pos p` of `prog` is a call to
      `tgt`, and every run under `O` from `pos p` on that byte state extends to a run from
      the index of the start;
    * a segment to an end state gives a run under `O` to a byte state that satisfies `Fin`
      with the end state.

    The index of the position after a call is the index after the call. -/
structure SegSim (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) (rsp : BitVec 64)
    (body : Lcmd) (fn : String) (E : Nat → List String) (L : Nat → Bool)
    (O : Nat → AState → AState → Prop)
    (prog : List RInstr) (pos : Nat → Nat) (tgt : Nat)
    (Seg : LstateMF → Option Nat → LstateMF → Prop) (Fin : LstateMF → AState → Prop) :
    Prop where
  /-- A segment to a call. -/
  toCall : ∀ s sa sA p u, s.prog.lfn = fn → sa.reg.lpc < body.length →
    L sa.reg.lpc = false →
    ImgRelF frame slotArr base body (E sa.reg.lpc) s sa →
    ACorr rsp sA sa → Seg s (some p) u →
    ∃ sa' sA', ImgRelF frame slotArr base body (E p) u sa' ∧ ACorr rsp sA' sa'
      ∧ sa'.reg.lpc = p
      ∧ (∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t)
      ∧ prog[pos p]? = some (.call tgt)
      ∧ ∀ s'', HaltsO aMachine O prog (pos p) sA' s'' →
          HaltsO aMachine O prog (pos sa.reg.lpc) sA s''
  /-- A segment to an end state. -/
  toEnd : ∀ s sa sA t, s.prog.lfn = fn → sa.reg.lpc < body.length →
    L sa.reg.lpc = false →
    ImgRelF frame slotArr base body (E sa.reg.lpc) s sa →
    ACorr rsp sA sa → Seg s none t →
    ∃ sA', HaltsO aMachine O prog (pos sa.reg.lpc) sA sA' ∧ Fin t sA'
  /-- The index after a call. -/
  pos_call : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
    pos (p + 1) = pos p + 1

/-- The instruction is a call. -/
def isCallB : LinstrR → Bool
  | .Lcall _ _ => true
  | _ => false

/-- **The check of the dead names at the calls of a body**: at each call instruction, at
    position `p`, no argument name of the callee is dead, and the names dead at `p` other
    than the result name and the names `exemptC c` are dead at `p + 1`. -/
def callDeadB (c : CalleeSig) (res : String) (E : Nat → List String) (body : Lcmd) : Bool :=
  (List.range body.length).all fun p => (body[p]?).all fun bi =>
    !isCallB bi.li_i ||
      (c.args.all (fun a => !(E p).contains a)
        && (((E p).filter fun r => r != res) ++ exemptC c).all
            (fun r => (E (p + 1)).contains r))

/-- **Soundness of `callDeadB`** at a call instruction. -/
theorem callDeadB_spec {c : CalleeSig} {res : String} {E : Nat → List String} {body : Lcmd}
    (h : callDeadB c res E body = true) {p : Nat} {bi : Linstr} (hb : body[p]? = some bi)
    {ra : Option String} {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt) :
    (∀ a ∈ c.args, a ∉ E p)
      ∧ ∀ r ∈ ((E p).filter fun r => r != res) ++ exemptC c, r ∈ E (p + 1) := by
  simp only [callDeadB, List.all_eq_true, List.mem_range] at h
  have hp := h p (List.getElem?_eq_some_iff.mp hb).1
  rw [hb] at hp
  simp only [Option.all_some, hbi, isCallB, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    List.all_eq_true] at hp
  exact ⟨fun a ha => by simpa using hp.1 a ha, fun r hr => by simpa using hp.2 r hr⟩

/-- **A chain of segments at the steps of its call sites is a run under the oracle of the
    callee.** Let the segments `SegTo I T P` of a calling body have the simulation `SegSim`
    at the dead names `E` and the oracle of a callee `X` at `tgt`, with `CalleeSpec X c`, no
    flag be live after a call, and each step `Glue T P` at a call position `p` be a step of
    the site (`SiteStep`) at the names `E p` and `E (p + 1)`. Then every chain
    `RunChain I T P` from an image state at a position where no flag is live, related, up to
    the dead names of its position and the flags, to an address state that corresponds to a
    byte state is matched by a run of `prog` under the oracle to a byte state that satisfies
    `Fin` with the end state of the chain. -/
theorem haltsO_of_runChainS {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {prog : List RInstr} {pos : Nat → Nat} {tgt : Nat} {E : Nat → List String} {L : Nat → Bool}
    (hLc : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → L (p + 1) = false)
    (hcl : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → p + 1 < body.length)
    {I : LprogIsa.Isa} {T : LprogIsa.ProcTable} {P : LprogM}
    {Fin : LstateMF → AState → Prop}
    (hsim : SegSim frame slotArr base rsp body P.lfn E L (oracleAt tgt X) prog pos tgt
      (SegTo I T P) Fin)
    (hStep : ∀ p u v, Glue T P p u v →
      (∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t) →
      SiteStep frame slotArr base rsp body X c (E p) (E (p + 1)) u v)
    {s t : LstateMF} (hch : RunChain I T P s t) :
    ∀ sa sA, s.prog.lfn = P.lfn → sa.reg.lpc < body.length → L sa.reg.lpc = false →
      ImgRelF frame slotArr base body (E sa.reg.lpc) s sa → ACorr rsp sA sa →
      ∃ sA', HaltsO aMachine (oracleAt tgt X) prog (pos sa.reg.lpc) sA sA' ∧ Fin t sA' := by
  induction hch with
  | done hseg =>
    exact fun sa sA hfn hlen hL hI hA => hsim.toEnd _ sa sA _ hfn hlen hL hI hA hseg
  | @call s u v t p hseg hcall _ ih =>
    intro sa sA hfn hlen hL hI hA
    obtain ⟨sa1, sA1, hI1, hc1, hpc1, ⟨bi, ra, tg, hb, hbi⟩, hprog, hk⟩ :=
      hsim.toCall _ sa sA p _ hfn hlen hL hI hA hseg
    have hfu : u.prog.lfn = P.lfn := by
      obtain ⟨_, _, hat, _⟩ := hseg
      exact hat.1
    have hst := hStep _ _ _ hcall ⟨bi, ra, tg, hb, hbi⟩
    have hfv : v.prog.lfn = P.lfn := by
      obtain ⟨dst, x, rfl, -⟩ := hst
      exact (LprogIsa.lfn_retRes dst x u).trans hfu
    subst hpc1
    obtain ⟨sA2, sa2, hpc2, hc2, hI2, hcont⟩ :=
      haltsO_call_imageS hX hI1 hst hc1 ⟨bi, ra, tg, hb, hbi⟩ hprog
    obtain ⟨sA', hrun, hfin⟩ := ih sa2 sA2 hfv
      (by rw [hpc2]; exact hcl _ bi ra tg hb hbi)
      (by rw [hpc2]; exact hLc _ bi ra tg hb hbi)
      (by rw [hpc2]; exact hI2) hc2
    rw [hpc2, hsim.pos_call _ bi ra tg hb hbi] at hrun
    exact ⟨sA', hk _ (hcont _ hrun), hfin⟩

/-- **The step of a call site of a word callee**: under `callDeadB` at a call position `p`,
    a step to the image state after the word of the summary at the argument words is a step
    of the site (`SiteStep`) at the dead names of `p` and `p + 1`. -/
theorem siteStep_word {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    (hroom : ∀ ret sA, sA.regs "%rsp" = rsp → room (entryOf ret sA))
    {E : Nat → List String} (hdead : callDeadB c res E body = true) {p : Nat}
    (hb : ∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t) {u v : LstateMF}
    (hv : ∃ w, pr.run (c.args.map (argWord u.prog.base.reg)) = some w
      ∧ v = LprogIsa.retWord res w u) :
    SiteStep frame slotArr base rsp body X c (E p) (E (p + 1)) u v := by
  obtain ⟨bi, ra, t, hb, hbi⟩ := hb
  obtain ⟨w, hw', rfl⟩ := hv
  obtain ⟨hargs, hsub⟩ := callDeadB_spec hdead hb hbi
  refine ⟨res, .word w, rfl, fun u' hag => ?_, hsub⟩
  have hv' : pr.run (c.args.map (argWord u'.prog.base.reg)) = some w := by
    rw [← hw']
    congr 1
    exact List.map_congr_left fun a ha => (argWord_congr (hag.regs a (hargs a ha))).symm
  exact resStep_word hsep hphys hX hw hS hF hroom hv'

/-- **A chain of segments is a run under the oracle of the callee.** Let the segments
    `SegTo I T P` of a calling body of the class `physImgB` have the simulation `SegSim` at
    the dead names `E` and the oracle of a callee `X` at `tgt`, with `CalleeSpec X c`, the
    word reading `pr` and the separation `CallerSep`; let `callDeadB` accept `E`, no flag be
    live after a call, each step `Glue T P` be the step of the summary `pr` at the argument
    words, and `room` hold at the entry state of every call from a byte state with the
    stack register `rsp`. Then every chain `RunChain I T P` from an image state at a
    position where no flag is live, related, up to the dead names of its position and the
    flags, to an address state that corresponds to a byte state is matched by a run of
    `prog` under the oracle to a byte state that satisfies `Fin` with the end state of the
    chain. -/
theorem haltsO_of_runChain {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    (hroom : ∀ ret sA, sA.regs "%rsp" = rsp → room (entryOf ret sA))
    {prog : List RInstr} {pos : Nat → Nat} {tgt : Nat} {E : Nat → List String}
    (hdead : callDeadB c res E body = true) {L : Nat → Bool}
    (hLc : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → L (p + 1) = false)
    (hcl : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → p + 1 < body.length)
    {I : LprogIsa.Isa} {T : LprogIsa.ProcTable} {P : LprogM}
    {Fin : LstateMF → AState → Prop}
    (hsim : SegSim frame slotArr base rsp body P.lfn E L (oracleAt tgt X) prog pos tgt
      (SegTo I T P) Fin)
    (hCall : ∀ p u v, Glue T P p u v → ∃ w,
      pr.run (c.args.map (argWord u.prog.base.reg)) = some w ∧ v = LprogIsa.retWord res w u)
    {s t : LstateMF} (hch : RunChain I T P s t) :
    ∀ sa sA, s.prog.lfn = P.lfn → sa.reg.lpc < body.length → L sa.reg.lpc = false →
      ImgRelF frame slotArr base body (E sa.reg.lpc) s sa → ACorr rsp sA sa →
      ∃ sA', HaltsO aMachine (oracleAt tgt X) prog (pos sa.reg.lpc) sA sA' ∧ Fin t sA' :=
  haltsO_of_runChainS hX hLc hcl hsim
    (fun p u v hg hb => siteStep_word hsep hphys hX hw hS hF hroom hdead hb (hCall p u v hg))
    hch

/-! ## 8a. The step of the summary at a shadow instruction -/

/-- The words of register operands read at width `64` are the argument words. -/
theorem mapM_reg_argWord (R : LstateN) :
    ∀ (args : List String) (vs : List (BitVec 64)),
      (args.map LOperand.reg).mapM (evalOperandN R 64) = some vs → vs = args.map (argWord R)
  | [], vs, h => by
      simp only [List.map_nil, List.mapM_nil] at h
      exact (Option.some.inj h).symm
  | a :: as, vs, h => by
      simp only [List.map_cons, List.mapM_cons, evalOperandN, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, ws, hws, h⟩ := h
      cases h
      rw [List.map_cons, ← mapM_reg_argWord R as ws hws]
      simp [argWord, hx]

/-- **The step of a summary on register operands**: the result word of the summary at the
    argument words, written to the destination. -/
theorem procStep_regArgs {pr : LprogIsa.ProcSummary} (hwo : pr.WordOnly) (hrw : pr.RetWord)
    {res : String} {args : List String} {u v : LstateMF}
    (h : LprogIsa.procStep pr res (args.map LOperand.reg) u = some v) :
    ∃ w, pr.run (args.map (argWord u.prog.base.reg)) = some w
      ∧ v = LprogIsa.retWord res w u := by
  rw [LprogIsa.procStep_of_wordOnly hwo hrw] at h
  split at h
  · obtain ⟨vs, hvs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨w, by rw [← mapM_reg_argWord _ _ _ hvs]; exact hw, rfl⟩
  · cases h

/-- **The shadow instructions of the body `B` are calls of one summary on register
    operands**: every shadow instruction of a call of a symbol of `T` has the summary `pr`,
    the destination `res` and the operands `args` as registers. -/
def SitesOf (T : LprogIsa.ProcTable) (B : List LinstrRM) (pr : LprogIsa.ProcSummary)
    (res : String) (args : List String) : Prop :=
  ∀ (p : Nat) (i : LinstrRM) (pr' : LprogIsa.ProcSummary) (dst : String)
    (srcs : List LOperand), B[p]? = some i →
    LprogIsa.procCall? T i.fst = some (pr', dst, srcs) →
    pr' = pr ∧ dst = res ∧ srcs = args.map LOperand.reg

/-- **The check of the shadow instructions of a body**: every shadow instruction of a call
    has the destination `res`, the symbol `f` and the operands `args` as registers. -/
def siteShapeB (f res : String) (args : List String) (B : List LinstrRM) : Bool :=
  B.all fun i =>
    match LprogIsa.shadowCall? i.fst with
    | none => true
    | some q => decide (q = (res, f, args.map LOperand.reg))

/-- **Soundness of `siteShapeB`** at a table that gives `f` the summary `pr`. -/
theorem sitesOf_of_siteShapeB {T : LprogIsa.ProcTable} {B : List LinstrRM}
    {pr : LprogIsa.ProcSummary} {f res : String} {args : List String}
    (h : siteShapeB f res args B = true) (hT : T f = some pr) : SitesOf T B pr res args := by
  intro p i pr' dst srcs hi hq
  have hm := List.all_eq_true.mp h i (List.mem_of_getElem? hi)
  unfold LprogIsa.procCall? at hq
  cases hs : LprogIsa.shadowCall? i.fst with
  | none => rw [hs] at hq; cases hq
  | some q =>
      rw [hs] at hm hq
      simp only [decide_eq_true_eq] at hm
      subst hm
      simp only [Option.bind_some, hT, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
      exact ⟨hq.1.symm, hq.2.1.symm, hq.2.2.symm⟩

/-- **The step `Glue` at a shadow instruction is the step of the summary at the argument
    words**, for a body whose shadow instructions are calls of `pr` on the registers
    `args` with the destination `res`. -/
theorem glue_regArgs {T : LprogIsa.ProcTable} {fn : String} {B : List LinstrRM}
    {pr : LprogIsa.ProcSummary} (hwo : pr.WordOnly) (hrw : pr.RetWord) {res : String}
    {args : List String} (hsite : SitesOf T B pr res args) {p : Nat} {u v : LstateMF}
    (hg : Glue T (singletonProgM fn B) p u v) :
    ∃ w, pr.run (args.map (argWord u.prog.base.reg)) = some w
      ∧ v = LprogIsa.retWord res w u := by
  obtain ⟨i, pr', dst, srcs, hi, hq, hstep⟩ := hg
  obtain ⟨rfl, rfl, rfl⟩ := hsite p i pr' dst srcs hi hq
  exact procStep_regArgs hwo hrw hstep

/-- **A run of a body with shadow instructions on the machine with procedures is a run of
    the decoded program under the oracle of the callee.** Let `B` be a body whose shadow
    instructions are calls of the summary `pr` on the argument registers of `c` with the
    destination `res`, and let the segments of `B` on the x86 instruction set have the
    simulation `SegSim` under the hypotheses of `haltsO_of_runChain`. Then every halting
    run of `x86Isa.withProcs T` on `B`, from an image state at a position where no flag is
    live, related, up to the dead names of its position and the flags, to an address state
    that corresponds to a byte state, is matched by a run of `prog` under the oracle to a
    byte state that satisfies `Fin` with the end state. -/
theorem haltsO_of_withProcs_run {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    (hroom : ∀ ret sA, sA.regs "%rsp" = rsp → room (entryOf ret sA))
    {prog : List RInstr} {pos : Nat → Nat} {tgt : Nat} {E : Nat → List String}
    (hdead : callDeadB c res E body = true) {L : Nat → Bool}
    (hLc : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → L (p + 1) = false)
    (hcl : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t → p + 1 < body.length)
    {I : LprogIsa.Isa} {T : LprogIsa.ProcTable} {fn : String} {B : List LinstrRM}
    {Fin : LstateMF → AState → Prop} (hsite : SitesOf T B pr res c.args)
    (hsim : SegSim frame slotArr base rsp body fn E L (oracleAt tgt X) prog pos tgt
      (SegTo I T (singletonProgM fn B)) Fin)
    (n : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF (singletonProgM fn B) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : L sa.reg.lpc = false)
    (hI : ImgRelF frame slotArr base body (E sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    ∃ sA', HaltsO aMachine (oracleAt tgt X) prog (pos sa.reg.lpc) sA sA' ∧ Fin t sA' :=
  haltsO_of_runChain hsep hphys hX hw hS hF hroom hdead hLc hcl hsim
    (fun _ _ _ hg => glue_regArgs hw.wordOnly hw.wordRet hsite hg) (runChain_of_run _ T _ n s t hrun) sa sA
    hfn hlen hL hI hA

/-! ## 8b. The simulation of a segment up to dead names, from the simulation at the relation -/

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (Steps Halted atPc)

/-- **The statement of the simulation of one segment at the relation `ImgRel`**: the
    statement `SegSim` with the image state related to the address state by `ImgRel`, at
    a start position where no flag is live. -/
structure SegExact (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) (rsp : BitVec 64)
    (body : Lcmd) (fn : String) (L : Nat → Bool) (O : Nat → AState → AState → Prop)
    (prog : List RInstr) (pos : Nat → Nat) (tgt : Nat)
    (Seg : LstateMF → Option Nat → LstateMF → Prop) (Fin : LstateMF → AState → Prop) :
    Prop where
  /-- A segment to a call. -/
  toCall : ∀ s sa zf sA p u, s.prog.lfn = fn → sa.reg.lpc < body.length →
    L sa.reg.lpc = false →
    ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa → Seg s (some p) u →
    ∃ sa' zf' sA', ImgRel frame slotArr base body u sa' zf' ∧ ACorr rsp sA' sa'
      ∧ (∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t)
      ∧ prog[pos p]? = some (.call tgt)
      ∧ ∀ s'', HaltsO aMachine O prog (pos p) sA' s'' →
          HaltsO aMachine O prog (pos sa.reg.lpc) sA s''
  /-- A segment to an end state. -/
  toEnd : ∀ s sa zf sA t, s.prog.lfn = fn → sa.reg.lpc < body.length →
    L sa.reg.lpc = false →
    ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa → Seg s none t →
    ∃ sA', HaltsO aMachine O prog (pos sa.reg.lpc) sA sA' ∧ Fin t sA'
  /-- The index after a call. -/
  pos_call : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
    pos (p + 1) = pos p + 1

/-- The positions of a table at which a flag is live. -/
def DeadTab.live (D : DeadTab) (k : Nat) : Bool := D.z k || D.c k

/-- **The check of the flags at the calls of a body**: no flag is live at the position
    after a call. -/
def callFlagsB (D : DeadTab) (body : Lcmd) : Bool :=
  (List.range body.length).all fun p => (body[p]?).all fun bi =>
    !isCallB bi.li_i || !D.live (p + 1)

/-- **Soundness of `callFlagsB`** at a call instruction. -/
theorem callFlagsB_spec {D : DeadTab} {body : Lcmd} (h : callFlagsB D body = true) (p : Nat)
    (bi : Linstr) (ra : Option String) (tgt : String × LLabel) (hb : body[p]? = some bi)
    (hbi : bi.li_i = .Lcall ra tgt) : D.live (p + 1) = false := by
  simp only [callFlagsB, List.all_eq_true, List.mem_range] at h
  have hp := h p (List.getElem?_eq_some_iff.mp hb).1
  rw [hb] at hp
  simpa [hbi, isCallB] using hp

/-- The relaxed relation at a position where no flag is live gives a related state that
    agrees with the image state up to the table of the position. -/
theorem deadAgree_of_imgRelF {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {D : DeadTab} {s : LstateMF} {sa : LstateA} (hL : D.live sa.reg.lpc = false)
    (hI : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) :
    ∃ s' zf, DeadAgree D s s' ∧ ImgRel frame slotArr base body s' sa zf := by
  obtain ⟨s', zf, hag, hrel⟩ := hI
  have hpc : s.prog.base.reg.lpc = sa.reg.lpc := hag.pc.trans hrel.pc.symm
  simp only [DeadTab.live, Bool.or_eq_false_iff] at hL
  refine ⟨s', zf, ?_, hrel⟩
  unfold DeadAgree
  rw [hpc]
  exact ⟨hag, fun e => (by rw [hL.1] at e; cases e), fun e => (by rw [hL.2] at e; cases e)⟩

/-- **A run of steps of the instruction set `I` on `P` keeps the agreement of the table
    `D`**: from two states that agree up to the dead names and the dead flags of their
    position, a run of steps is matched by a run of the same number of steps, to states
    that agree up to the dead names and the dead flags of their position. At the x86
    instruction set this is `steps_deadSeg`. -/
def DeadSteps (D : DeadTab) (I : LprogIsa.Isa) (P : LprogM) : Prop :=
  ∀ (n : Nat) (s s' u : LstateMF), DeadAgree D s s' → Steps I P n s u →
    ∃ u', Steps I P n s' u' ∧ DeadAgree D u u'

/-- **The simulation of a segment up to dead names, from the simulation at the relation.**
    Let the steps of the instruction set `I` on the body `B` keep the agreement of the table
    `D` (`DeadSteps`), the segments of `B` on `I` have the simulation `SegExact` at the
    positions where no flag of `D` is live, and `Fin` be kept by a change of the dead names
    of the position of the end state. Then the segments have the simulation `SegSim` at the
    dead names of `D`. -/
theorem segSim_of_segExact {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} {D : DeadTab} {O : Nat → AState → AState → Prop} {prog : List RInstr}
    {pos : Nat → Nat} {tgt : Nat} {I : LprogIsa.Isa} {T : LprogIsa.ProcTable} {fn : String}
    {B : List LinstrRM}
    {Fin : LstateMF → AState → Prop} (hD : DeadSteps D I (singletonProgM fn B))
    (hX : SegExact frame slotArr base rsp body fn D.live O prog pos tgt
      (SegTo I T (singletonProgM fn B)) Fin)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA) :
    SegSim frame slotArr base rsp body fn D.dead D.live O prog pos tgt
      (SegTo I T (singletonProgM fn B)) Fin := by
  refine ⟨fun s sa sA p u hfn hlen hL hI hA hseg => ?_,
    fun s sa sA t hfn hlen hL hI hA hseg => ?_, hX.pos_call⟩
  · obtain ⟨s', zf, hag, hrel⟩ := deadAgree_of_imgRelF hL hI
    obtain ⟨n, hn, hat, i, hi, hproc⟩ := hseg
    obtain ⟨u', hn', hagu⟩ := hD n s s' u hag hn
    have hat' : atPc (singletonProgM fn B) p u' :=
      ⟨hagu.off.fn.symm.trans hat.1, hagu.off.pc.symm.trans hat.2⟩
    obtain ⟨sa', zf', sA', hrel', hA', hcall, hprog, hk⟩ :=
      hX.toCall s' sa zf sA p u' (hag.off.fn.symm.trans hfn) hlen hL hrel hA
        ⟨n, hn', hat', i, hi, hproc⟩
    have hpu : u.prog.base.reg.lpc = p := hat.2
    refine ⟨sa', sA', ⟨u', zf', ?_, hrel'⟩, hA', ?_, hcall, hprog, hk⟩
    · have := hagu.off
      rwa [hpu] at this
    · exact hrel'.pc.trans (hagu.off.pc.symm.trans hpu)
  · obtain ⟨s', zf, hag, hrel⟩ := deadAgree_of_imgRelF hL hI
    obtain ⟨n, hn, hhalt⟩ := hseg
    obtain ⟨t', hn', hagt⟩ := hD n s s' t hag hn
    have hhalt' : Halted (singletonProgM fn B) t' := by
      unfold Halted findInstrMem at hhalt ⊢
      rw [← hagt.off.fn]
      exact (congrArg (fun q => if t.prog.lfn = fn then B[q]? else none) hagt.off.pc.symm).trans
        hhalt
    obtain ⟨sA', hrun, hfin⟩ := hX.toEnd s' sa zf sA t' (hag.off.fn.symm.trans hfn) hlen hL
      hrel hA ⟨n, hn', hhalt'⟩
    exact ⟨sA', hrun, hFin t t' sA' hagt.off hfin⟩

/-- At the x86 instruction set, the steps of a body that passes `deadSegB` keep the
    agreement of the table. -/
theorem deadSteps_x86 {D : DeadTab} {fn : String} {B : List LinstrRM}
    (hD : deadSegB D B = true) : DeadSteps D X86Isa.x86Isa (singletonProgM fn B) :=
  steps_deadSeg hD

/-! ## 8c. The image of a calling body -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel isLabel)

/-- **The image of a calling body**: the image `virtImg`, with the instruction at each
    position of a call `Lcall none (f, _)` of the body replaced by the shadow instruction
    `callShadow res f args`. -/
def callImg (slotArr : String → Option (String × Nat)) (res : String) (args : List LOperand)
    (body : Lcmd) : List LinstrRM :=
  (virtImg slotArr body).mapIdx fun k i =>
    match body[k]? with
    | some ⟨_, .Lcall none (f, _)⟩ => (LprogIsa.callShadow res f args, .reg none)
    | _ => i

/-- The image of a calling body has the length of the image. -/
theorem callImg_length (slotArr : String → Option (String × Nat)) (res : String)
    (args : List LOperand) (body : Lcmd) :
    (callImg slotArr res args body).length = body.length - 1 := by
  simp [callImg, virtImg_length]

/-- At a position that holds no call, the image of a calling body is the image. -/
theorem callImg_getElem?_of_ne (slotArr : String → Option (String × Nat)) (res : String)
    (args : List LOperand) {body : Lcmd} {k : Nat} {bi : Linstr} (hb : body[k]? = some bi)
    (hn : ∀ f l, bi.li_i ≠ .Lcall none (f, l)) :
    (callImg slotArr res args body)[k]? = (virtImg slotArr body)[k]? := by
  simp only [callImg, List.getElem?_mapIdx, hb]
  cases hv : (virtImg slotArr body)[k]? with
  | none => rfl
  | some i =>
      simp only [Option.map_some, Option.some.injEq]
      split
      · rename_i ii f l heq
        cases Option.some.inj heq
        exact absurd rfl (hn f l)
      · rfl

/-- At the position of a call, the image of a calling body holds the shadow instruction of
    the call. -/
theorem callImg_getElem?_call (slotArr : String → Option (String × Nat)) (res : String)
    (args : List LOperand) {body : Lcmd} {k : Nat} {bi : Linstr} (hb : body[k]? = some bi)
    (hk : k + 1 < body.length) {f : String} {l : LLabel} (hbi : bi.li_i = .Lcall none (f, l)) :
    (callImg slotArr res args body)[k]? = some (LprogIsa.callShadow res f args, .reg none) := by
  obtain ⟨ii, li⟩ := bi
  simp only at hbi
  subst hbi
  have hlt : k < (virtImg slotArr body).length := by rw [virtImg_length]; omega
  simp only [callImg, List.getElem?_mapIdx, hb, List.getElem?_eq_getElem hlt, Option.map_some]

/-- **The labels of the image of a calling body are the labels of the image.** -/
theorem findLabelMem_callImg (slotArr : String → Option (String × Nat)) (res : String)
    (args : List LOperand) (body : Lcmd) (l : LLabel) :
    findLabelMem l (callImg slotArr res args body) = findLabelMem l (virtImg slotArr body) := by
  have hmap : ((callImg slotArr res args body).map Prod.fst).map (isLabel l)
      = ((virtImg slotArr body).map Prod.fst).map (isLabel l) := by
    apply List.ext_getElem
    · simp [callImg]
    · intro n h1 h2
      simp only [callImg, List.getElem_map, List.getElem_mapIdx]
      split
      · rename_i ii f l' heq
        have hlt : n < body.dropLast.length := by
          simpa [virtImg] using h2
        have hv : (virtImg slotArr body)[n]'(by simpa using h2)
            = imgInstr slotArr body n (.Lcall none (f, l')) := by
          have hd : body.dropLast[n]? = some ⟨ii, .Lcall none (f, l')⟩ := by
            rw [List.getElem?_dropLast, ite_eq_left (by simpa using hlt)]
            exact heq
          have := virtImg_getElem? slotArr body n
          rw [hd, List.getElem?_eq_getElem (by simpa using h2)] at this
          exact Option.some.inj this
        rw [hv, ImageAddrSim.isLabel_imgInstr]
        rfl
      · rfl
  have e : ∀ xs : List LinstrR,
      List.findIdx? (isLabel l) xs = (xs.map (isLabel l)).findIdx? id := fun xs => by
    rw [List.findIdx?_map]; rfl
  unfold findLabelMem findLabel
  rw [e, e, hmap]

/-! ## 9. The class of printed bodies with calls -/

/-- The instruction is a call of a named symbol. -/
def remoteCallB : LinstrR → Bool
  | .Lcall _ (f, _) => !f.isEmpty
  | _ => false

/-- No instruction of the body is a call. -/
def callFreeB (body : Lcmd) : Bool := body.all fun i => !isCallB i.li_i

/-- An instruction of a calling body other than its closing return: a call of a named
    symbol, or an instruction of the covered fragment `DecodePrintedCFG.instrOKB`. -/
def instrOKCB (body : Lcmd) (P : Params) (i : LinstrR) : Bool :=
  remoteCallB i || instrOKB body P i

/-- The conditions of the relocating encoder on the frame of a body: no register is saved
    by `push`, and the frame is non-zero and below `2 ^ 31`. -/
def relocFrameB (body : Lcmd) : Bool :=
  (calleeSavedToSave body).isEmpty && frameSize body != 0 && decide (frameSize body < 2 ^ 31)

/-- **The printed bodies with calls**: the frame conditions of the relocating encoder; the
    closing return; every other instruction a call of a named symbol or in the covered
    fragment; every conditional branch directly after a compare; and, for a body with a
    call, the frame check `frameNonnegB` at `G` bytes below the return word. -/
def printedAddrCB (G : Nat) (body : Lcmd) : Bool :=
  relocFrameB body && body.getLast?.any (fun r => isRetB r.li_i)
    && body.dropLast.all (fun i => instrOKCB body (Params.ofBody body) i.li_i)
    && (List.range body.length).all (condPrevB body)
    && (callFreeB body || frameNonnegB body G)

/-- **The gate of the image simulation of a calling body**: every instruction but the last
    is a call of a named symbol or passes `ImageAddrSim.instrGateB`, the last is the
    return, and every array-pointer reload follows a save. -/
def imgGateCB (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) : Bool :=
  (List.range (body.length - 1)).all (fun k =>
      (body[k]?).all fun i => remoteCallB i.li_i || instrGateB frame slotArr body k i.li_i)
    && body.getLast?.any (fun r => isRetB r.li_i)
    && reloadSavedB slotArr body

theorem remoteCallB_of_callFree {body : Lcmd} (h : callFreeB body = true) {i : Linstr}
    (hi : i ∈ body) : remoteCallB i.li_i = false := by
  have := List.all_eq_true.mp h i hi
  cases hc : i.li_i <;> simp_all [isCallB, remoteCallB]

/-- **On a body without calls the gate is the existing gate.** -/
theorem imgGateCB_of_callFree {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} (h : callFreeB body = true) :
    imgGateCB frame slotArr body = imgGateB frame slotArr body := by
  unfold imgGateCB imgGateB
  congr 2
  refine List.all_congr rfl fun k => ?_
  cases hk : body[k]? with
  | none => rfl
  | some i =>
    simp only [Option.all_some]
    rw [remoteCallB_of_callFree h (List.mem_of_getElem? hk), Bool.false_or]

/-- A body of the existing class has no call. -/
theorem callFreeB_of_printedAddrB {body : Lcmd} (h : printedAddrB body = true) :
    callFreeB body = true := by
  simp only [printedAddrB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, hlast⟩, hall⟩, -⟩ := h
  rcases List.eq_nil_or_concat body with rfl | ⟨L, b, rfl⟩
  · rfl
  · simp only [List.concat_eq_append, List.dropLast_concat, List.getLast?_concat,
      Option.any_some, List.all_eq_true] at hlast hall
    simp only [callFreeB, List.concat_eq_append, List.all_append, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
    refine ⟨fun i hi => ?_, ?_⟩
    · have := hall i hi
      cases hc : i.li_i <;> simp_all [isCallB, instrOKB]
    · cases hc : b.li_i <;> simp_all [isCallB, isRetB]

/-- **The existing class is in the class with calls.** -/
theorem printedAddrCB_of_printedAddrB (G : Nat) {body : Lcmd} (h : printedAddrB body = true) :
    printedAddrCB G body = true := by
  have hcf := callFreeB_of_printedAddrB h
  simp only [printedAddrB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hdec, hlast⟩, hall⟩, hcond⟩ := h
  simp only [decodableLcmd, Bool.and_eq_true, bne_iff_ne, ne_eq] at hdec
  obtain ⟨⟨⟨⟨⟨-, hsaves⟩, hF0⟩, hF⟩, -⟩, -⟩ := hdec
  have hF' : frameSize body < 2 ^ 31 := by
    have h1 : (Int.ofNat (Params.ofBody body).frame) < 2 ^ 31 := by
      simp only [dispOk32, decide_eq_true_eq] at hF
      exact hF.2
    have h2 : ((frameSize body : Nat) : Int) < 2 ^ 31 := h1
    exact_mod_cast h2
  simp only [printedAddrCB, relocFrameB, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨hsaves, hF0⟩, hF'⟩, hlast⟩, ?_⟩, hcond⟩, Or.inl hcf⟩
  rw [List.all_eq_true] at hall ⊢
  intro i hi
  simp [instrOKCB, hall i hi]

/-- **On a body without calls the class is the existing class** together with
    decodability. -/
theorem printedAddrB_iff_of_callFree (G : Nat) {body : Lcmd} (h : callFreeB body = true) :
    printedAddrB body = true ↔ decodableLcmd body = true ∧ printedAddrCB G body = true := by
  constructor
  · intro hp
    refine ⟨?_, printedAddrCB_of_printedAddrB G hp⟩
    simp only [printedAddrB, Bool.and_eq_true] at hp
    exact hp.1.1.1
  · rintro ⟨hdec, hc⟩
    simp only [printedAddrCB, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨-, hlast⟩, hall⟩, hcond⟩, -⟩ := hc
    simp only [printedAddrB, Bool.and_eq_true]
    refine ⟨⟨⟨hdec, hlast⟩, ?_⟩, hcond⟩
    rw [List.all_eq_true] at hall ⊢
    intro i hi
    have := hall i hi
    rwa [instrOKCB, remoteCallB_of_callFree h (List.mem_of_mem_dropLast hi),
      Bool.false_or] at this

/-- **The frame facts of the class for the relocating encoder**: no register is saved by
    `push`, and the frame is non-zero and below `2 ^ 31`. -/
theorem printedAddrCB_reloc {G : Nat} {body : Lcmd} (h : printedAddrCB G body = true) :
    calleeSavedToSave body = [] ∧ frameSize body ≠ 0 ∧ frameSize body < 2 ^ 31 := by
  simp only [printedAddrCB, relocFrameB, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, List.isEmpty_iff] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2⟩

/-- **A remote transfer of a body of the class is a call.** -/
theorem printedAddrCB_remote {G : Nat} {body : Lcmd} (h : printedAddrCB G body = true)
    {i : Linstr} (hi : i ∈ body) {f : String} (hf : remoteSym i.li_i = some f) :
    ∃ ra l, i.li_i = .Lcall ra (f, l) := by
  simp only [printedAddrCB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, hlast⟩, hall⟩, -⟩, -⟩ := h
  rcases List.eq_nil_or_concat body with rfl | ⟨L, b, rfl⟩
  · cases hi
  · simp only [List.concat_eq_append, List.dropLast_concat, List.getLast?_concat,
      Option.any_some, List.all_eq_true] at hlast hall
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · have := hall i hi
      cases hc : i.li_i with
      | Lcall ra tg =>
        obtain ⟨f', l⟩ := tg
        rw [hc] at hf
        simp only [remoteSym] at hf
        split at hf
        · cases hf
        · cases hf
          exact ⟨ra, l, rfl⟩
      | _ => simp_all [remoteSym, instrOKCB, remoteCallB, instrOKB]
    · cases hc : i.li_i <;> simp_all [remoteSym, isRetB]

/-- **The shape condition of the relocating encoder from the class.** An instruction of a
    body of the class meets `RelocShapeOK` at a shape `sh` when, being no remote transfer,
    it has the shape `sh`. -/
theorem relocShapeOK_of_printedAddrCB {G : Nat} {body : Lcmd}
    (h : printedAddrCB G body = true) {i : Linstr} (hi : i ∈ body) (P : Params) (sh : Shape)
    (hsh : remoteSym i.li_i = none → ShapeOK P i.li_i sh) : RelocShapeOK P i.li_i sh := by
  unfold RelocShapeOK
  cases hr : remoteSym i.li_i with
  | none => exact hsh hr
  | some f => exact printedAddrCB_remote h hi hr

/-- **The frame of a body of the class with a call lies above the stack register.** -/
theorem printedAddrCB_frameAbove {G : Nat} {body : Lcmd} (h : printedAddrCB G body = true)
    (hcall : callFreeB body = false) (sa0 : AState) :
    FrameAbove (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0)))
      (frameRsp body sa0) G := by
  simp only [printedAddrCB, Bool.and_eq_true, hcall, Bool.false_or] at h
  exact frameAbove_of_frameNonnegB h.2 sa0

/-! ## 9a. The segments of the image of a calling body -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (isCondB LoadSafeAt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (stepA)

/-- A body that passes `imgGateCB` passes the positionwise gate of the image simulation. -/
theorem imgGate_of_imgGateCB {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateCB frame slotArr body = true) : ImgGate frame slotArr body := by
  simp only [imgGateCB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun k i hi hk hnc => ?_, ?_, h3⟩
  · have := h1 k (by omega)
    rw [hi] at this
    simp only [Option.all_some, Bool.or_eq_true] at this
    rcases this with hr | hg
    · cases hx : i.li_i with
      | Lcall ra t => exact absurd hx (hnc ra t)
      | _ => rw [hx] at hr; simp [remoteCallB] at hr
    · exact hg
  · cases hl : body.getLast? with
    | none => rw [hl] at h2; cases h2
    | some r =>
        rw [hl] at h2
        simp only [Option.any_some] at h2
        refine ⟨r, rfl, ?_⟩
        revert h2
        cases r.li_i <;> simp [isRetB]

/-- **The check of the call sites of a body**: before the last position, every call has no
    return-address name, and the image of every other instruction is no shadow instruction
    of a call. -/
def callSitesB (slotArr : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  (List.range (body.length - 1)).all fun k => (body[k]?).all fun bi =>
    match bi.li_i with
    | .Lcall ra _ => ra.isNone
    | x => (LprogIsa.shadowCall? (imgInstr slotArr body k x).1).isNone

/-- **Soundness of `callSitesB`** at a call. -/
theorem callSitesB_call {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : callSitesB slotArr body = true) {k : Nat} {bi : Linstr} (hb : body[k]? = some bi)
    (hk : k < body.length - 1) {ra : Option String} {t : String × LLabel}
    (hbi : bi.li_i = .Lcall ra t) : ra = none := by
  simp only [callSitesB, List.all_eq_true, List.mem_range] at h
  have := h k hk
  rw [hb] at this
  simpa [hbi] using this

/-- **Soundness of `callSitesB`** at an instruction that is no call. -/
theorem callSitesB_other {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : callSitesB slotArr body = true) {k : Nat} {bi : Linstr} (hb : body[k]? = some bi)
    (hk : k < body.length - 1) (hnc : ∀ ra t, bi.li_i ≠ .Lcall ra t) :
    LprogIsa.shadowCall? (imgInstr slotArr body k bi.li_i).1 = none := by
  simp only [callSitesB, List.all_eq_true, List.mem_range] at h
  have := h k hk
  rw [hb] at this
  simp only [Option.all_some] at this
  cases hx : bi.li_i with
  | Lcall ra t => exact absurd hx (hnc ra t)
  | _ => rw [hx] at this; simpa using this

/-- **The check of the flags at the conditional branches of a body**: a flag is live at
    every conditional branch. -/
def condLiveB (D : DeadTab) (body : Lcmd) : Bool :=
  (List.range body.length).all fun k => (body[k]?).all fun bi =>
    !isCondB bi.li_i || D.live k

/-- **Soundness of `condLiveB`.** -/
theorem condLiveB_spec {D : DeadTab} {body : Lcmd} (h : condLiveB D body = true) (k : Nat)
    (bi : Linstr) (hb : body[k]? = some bi) (hc : isCondB bi.li_i = true) :
    D.live k = true := by
  simp only [condLiveB, List.all_eq_true, List.mem_range] at h
  have := h k (List.getElem?_eq_some_iff.mp hb).1
  rw [hb] at this
  simpa [hc] using this

/-- The zero flag of the byte state is the zero flag `zf` of the address machine when the
    position of the address state holds a conditional branch. -/
def CondFlag (body : Lcmd) (sA : AState) (sa : LstateA) (zf : Bool) : Prop :=
  ∀ bi, body[sa.reg.lpc]? = some bi → isCondB bi.li_i = true → sA.flags.zf.getD false = zf

/-- **The statement of the byte simulation of the segments of a calling body** by the
    decoded program `prog` under the oracle `O`, with `pos` the index in `prog` of a
    position of the body:

    * a step of the address machine on the body, from an address state that corresponds to
      a byte state with the zero flag of a conditional branch (`CondFlag`) and whose indexed
      load reads outside the red-zone word, reaches an address state at a position of the
      body that corresponds to a byte state with `CondFlag`, and every run under `O` from
      the index of the reached position on that byte state extends to a run from the index
      of the start;
    * at the closing return, there is a run under `O` to a byte state that satisfies `FinA`
      with the address state;
    * the index of a call of the body holds a call to `tgt`, and the index of the position
      after a call is the index after the call. -/
structure ByteSeg (frame : String → Option (BitVec 64)) (rsp : BitVec 64) (body : Lcmd)
    (O : Nat → AState → AState → Prop) (prog : List RInstr) (pos : Nat → Nat) (tgt : Nat)
    (FinA : LstateA → AState → Prop) : Prop where
  /-- A step of the address machine. -/
  step : ∀ sa zf sa' zf' sA, LoadSafeAt rsp body sa →
    stepA frame body sa zf = some (sa', zf') → ACorr rsp sA sa → CondFlag body sA sa zf →
    ∃ sA', ACorr rsp sA' sa' ∧ sa'.reg.lpc < body.length ∧ CondFlag body sA' sa' zf'
      ∧ ∀ s'', HaltsO aMachine O prog (pos sa'.reg.lpc) sA' s'' →
          HaltsO aMachine O prog (pos sa.reg.lpc) sA s''
  /-- The closing return. -/
  halt : ∀ sa sA, sa.reg.lpc + 1 = body.length → ACorr rsp sA sa →
    ∃ sA', HaltsO aMachine O prog (pos sa.reg.lpc) sA sA' ∧ FinA sa sA'
  /-- The index of a call. -/
  call : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
    prog[pos p]? = some (.call tgt)
  /-- The index after a call. -/
  pos_call : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
    pos (p + 1) = pos p + 1

/-- **A run of checked steps of the image of a calling body, by the decoded program.** Let
    the body pass the positionwise gate `ImgGate`, the class `physImgB` and `callSitesB`,
    the byte simulation `ByteSeg` hold, and every step of the instruction set `I` be a
    checked step of the x86 instruction set. From an image state in the function `fn`
    related by `ImgRel` to an address state at a position of the body that corresponds to
    a byte state with `CondFlag`, a run of steps of `I` on the image `callImg` reaches an
    image state related to an address state at a position of the body that corresponds to
    a byte state, and every run under `O` from the index of the reached position on that
    byte state extends to a run from the index of the start. -/
theorem steps_callImg {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : ImgGate frame slotArr body) (hsites : callSitesB slotArr body = true)
    {O : Nat → AState → AState → Prop} {prog : List RInstr} {pos : Nat → Nat} {tgt : Nat}
    {FinA : LstateA → AState → Prop} (hbytes : ByteSeg frame rsp body O prog pos tgt FinA)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (res : String) (args : List LOperand) (fn : String) :
    ∀ (n : Nat) (s u : LstateMF) (sa : LstateA) (zf : Bool) (sA : AState),
      s.prog.lfn = fn → ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      CondFlag body sA sa zf →
      Steps I (singletonProgM fn (callImg slotArr res args body)) n s u →
      ∃ sa' zf' sA', ImgRel frame slotArr base body u sa' zf' ∧ ACorr rsp sA' sa'
        ∧ u.prog.lfn = fn ∧ (0 < n → sa'.reg.lpc < body.length)
        ∧ ∀ s'', HaltsO aMachine O prog (pos sa'.reg.lpc) sA' s'' →
            HaltsO aMachine O prog (pos sa.reg.lpc) sA s''
  | 0, s, u, sa, zf, sA, hfn, hrel, hA, _, h => by
      have hsu : s = u := Option.some.inj h
      subst hsu
      exact ⟨sa, zf, sA, hrel, hA, hfn, fun h0 => absurd h0 (Nat.lt_irrefl 0), fun _ hr => hr⟩
  | n + 1, s, u, sa, zf, sA, hfn, hrel, hA, hz, h => by
      simp only [Steps, Ascent.CutPoint.iter, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, h⟩ := h
      unfold LprogIsa.Isa.lsemStepPMemF at hc
      cases hf : findInstrMem (singletonProgM fn (callImg slotArr res args body)) s.prog with
      | none => rw [hf] at hc; cases hc
      | some i =>
        rw [hf] at hc
        dsimp only at hc
        have hck := hI _ _ _ _ hc
        rw [OwnedLprogTV.findInstrMem_single hfn, ← hrel.pc] at hf
        have hlt : sa.reg.lpc < body.length - 1 := by
          have := (List.getElem?_eq_some_iff.mp hf).1
          rwa [callImg_length] at this
        obtain ⟨bi, hb⟩ : ∃ bi, body[sa.reg.lpc]? = some bi :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hnc : ∀ ra tg, bi.li_i ≠ .Lcall ra tg := by
          intro ra tg e
          obtain rfl := callSitesB_call hsites hb hlt e
          obtain ⟨f, l⟩ := tg
          rw [callImg_getElem?_call slotArr res args hb (by omega) e] at hf
          obtain rfl := Option.some.inj hf
          have hn := LprogIsaProcs.evalInstrPMemF_shadowCall
            (singletonProgM fn (callImg slotArr res args body))
            (LprogIsa.callShadow res f args, .reg none) s
            (by rw [LprogIsa.shadowCall?_callShadow]; exact Option.some_ne_none _)
          rw [JasminLsemMemChecked.evalInstrPMemF_of_k hck] at hn
          cases hn
        rw [callImg_getElem?_of_ne slotArr res args hb (fun f l => hnc none (f, l)),
          virtImg_getElem?, List.getElem?_dropLast, ite_eq_left hlt, hb, Option.map_some] at hf
        obtain rfl := Option.some.inj hf
        obtain ⟨-, hsafe, hfn1, sa1, z1, hst1, hcase⟩ :=
          gate_step hsep hphys hgate fn
            (fun l => findLabelMem_callImg slotArr res args body l) hfn hrel hb hlt hnc hck
        obtain ⟨sA1, hA1, hlen1, hz1, hk1⟩ := hbytes.step sa zf sa1 z1 sA hsafe hst1 hA hz
        rcases hcase with hrel1 | ⟨-, hsafe1, sa2, z2, hst2, hrel2⟩
        · obtain ⟨sa', zf', sA', hrel', hA', hfn', hlen', hk⟩ :=
            steps_callImg hsep hphys hgate hsites hbytes hI res args fn n c u sa1 z1 sA1
              hfn1 hrel1 hA1 hz1 h
          refine ⟨sa', zf', sA', hrel', hA', hfn', fun _ => ?_, fun s'' hr => hk1 _ (hk _ hr)⟩
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · have hcu : c = u := Option.some.inj h
            subst hcu
            rw [hrel'.pc, ← hrel1.pc]
            exact hlen1
          · exact hlen' hn
        · obtain ⟨sA2, hA2, hlen2, hz2, hk2⟩ :=
            hbytes.step sa1 z1 sa2 z2 sA1 hsafe1 hst2 hA1 hz1
          obtain ⟨sa', zf', sA', hrel', hA', hfn', hlen', hk⟩ :=
            steps_callImg hsep hphys hgate hsites hbytes hI res args fn n c u sa2 z2 sA2
              hfn1 hrel2 hA2 hz2 h
          refine ⟨sa', zf', sA', hrel', hA', hfn', fun _ => ?_,
            fun s'' hr => hk1 _ (hk2 _ (hk _ hr))⟩
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · have hcu : c = u := Option.some.inj h
            subst hcu
            rw [hrel'.pc, ← hrel2.pc]
            exact hlen2
          · exact hlen' hn

/-- **The simulation `SegExact` of the segments of the image of a calling body**, from the
    byte simulation `ByteSeg`. Let the body pass the positionwise gate `ImgGate`, the class
    `physImgB` and `callSitesB`, a flag of `L` be live at every conditional branch, every
    step of the instruction set `I` be a checked step of the x86 instruction set, and `Fin`
    hold of an image state related by `ImgRel` to an address state that satisfies `FinA`.
    Then the segments of the image `callImg` on `I` have the simulation `SegExact`. -/
theorem segExact_callImg {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : ImgGate frame slotArr body) (hsites : callSitesB slotArr body = true)
    {L : Nat → Bool}
    (hLc : ∀ k bi, body[k]? = some bi → isCondB bi.li_i = true → L k = true)
    {O : Nat → AState → AState → Prop} {prog : List RInstr} {pos : Nat → Nat} {tgt : Nat}
    {FinA : LstateA → AState → Prop} (hbytes : ByteSeg frame rsp body O prog pos tgt FinA)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf → FinA sa sA → Fin t sA)
    (res : String) (args : List LOperand) (T : LprogIsa.ProcTable) (fn : String) :
    SegExact frame slotArr base rsp body fn L O prog pos tgt
      (SegTo I T (singletonProgM fn (callImg slotArr res args body))) Fin := by
  have hz0 : ∀ (sa : LstateA) (sA : AState) (zf : Bool), L sa.reg.lpc = false →
      CondFlag body sA sa zf := fun sa sA zf hL bi hb hc => by
    rw [hLc _ bi hb hc] at hL
    cases hL
  refine ⟨fun s sa zf sA p u hfn hlen hL hrel hA hseg => ?_,
    fun s sa zf sA t hfn hlen hL hrel hA hseg => ?_, hbytes.pos_call⟩
  · obtain ⟨n, hn, hat, i, hi, hproc⟩ := hseg
    obtain ⟨sa', zf', sA', hrel', hA', -, -, hk⟩ :=
      steps_callImg hsep hphys hgate hsites hbytes hI res args fn n s u sa zf sA hfn hrel hA
        (hz0 sa sA zf hL) hn
    have hpc : sa'.reg.lpc = p := hrel'.pc.trans hat.2
    have hi' : (callImg slotArr res args body)[p]? = some i := hi
    have hp : p < body.length - 1 := by
      have := (List.getElem?_eq_some_iff.mp hi').1
      rwa [callImg_length] at this
    obtain ⟨bi, hb⟩ : ∃ bi, body[p]? = some bi := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hcallp : ∃ ra t, bi.li_i = .Lcall ra t := by
      by_contra hne
      have hnc : ∀ ra t, bi.li_i ≠ .Lcall ra t := fun ra t e => hne ⟨ra, t, e⟩
      rw [callImg_getElem?_of_ne slotArr res args hb (fun f l => hnc none (f, l)),
        virtImg_getElem?, List.getElem?_dropLast, ite_eq_left hp, hb, Option.map_some] at hi'
      obtain rfl := Option.some.inj hi'
      have hsh := callSitesB_other hsites hb hp hnc
      simp [LprogCallCut.isProcB, LprogIsa.procCall?, hsh] at hproc
    obtain ⟨ra, t, hbi⟩ := hcallp
    subst hpc
    exact ⟨sa', zf', sA', hrel', hA', ⟨bi, ra, t, hb, hbi⟩, hbytes.call _ bi ra t hb hbi, hk⟩
  · obtain ⟨n, hn, hhalt⟩ := hseg
    obtain ⟨sa', zf', sA', hrel', hA', hfn', hlen', hk⟩ :=
      steps_callImg hsep hphys hgate hsites hbytes hI res args fn n s t sa zf sA hfn hrel hA
        (hz0 sa sA zf hL) hn
    have hlenE : sa'.reg.lpc < body.length := by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · have hst : s = t := Option.some.inj hn
        subst hst
        rw [hrel'.pc, ← hrel.pc]
        exact hlen
      · exact hlen' hn0
    have hend : sa'.reg.lpc + 1 = body.length := by
      have hh : findInstrMem (singletonProgM fn (callImg slotArr res args body)) t.prog
          = none := hhalt
      rw [OwnedLprogTV.findInstrMem_single hfn', List.getElem?_eq_none_iff, callImg_length,
        ← hrel'.pc] at hh
      omega
    obtain ⟨sA'', hrun, hfa⟩ := hbytes.halt sa' sA' hend hA'
    exact ⟨sA'', hk _ hrun, hfin _ _ _ _ hrel' hfa⟩

/-- **A halting run of the image of a calling body at the steps of its call sites is a run
    of the decoded program under the oracle of the callee**, from Boolean checks and the
    byte simulation `ByteSeg` of the segments. Let the body pass `physImgB`, `imgGateCB` and
    `callSitesB`; let `callFlagsB` and `condLiveB` accept the table `D`; let the callee meet
    its specification; let every step of the instruction set `I` be a checked step of the
    x86 instruction set and the steps of `I` on the image `callImg` at the destination `res`
    and the operands `args` keep the agreement of `D` (`DeadSteps`); and let each step
    `Glue` of the image at a call position `p` be a step of the site (`SiteStep`) at the dead
    names of `p` and `p + 1`. Then every halting run of `I.withProcs T` on the image, from an
    image state in `fn` at a position of the body where no flag is live, related up to the
    dead names of its position to an address state that corresponds to a byte state, is
    matched by a run of `prog` under the oracle to a byte state that satisfies `Fin` with the
    end state. -/
theorem haltsO_of_deadChecksS {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCB frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {prog : List RInstr} {pos : Nat → Nat} {tgt : Nat} {D : DeadTab}
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {fn res : String} {args : List LOperand} {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr res args body)))
    {FinA : LstateA → AState → Prop}
    (hbytes : ByteSeg frame rsp body (oracleAt tgt X) prog pos tgt FinA)
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf → FinA sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (hStep : ∀ p u v, Glue T (singletonProgM fn (callImg slotArr res args body)) p u v →
      (∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t) →
      SiteStep frame slotArr base rsp body X c (D.dead p) (D.dead (p + 1)) u v)
    (n : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr res args body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : D.live sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    ∃ sA', HaltsO aMachine (oracleAt tgt X) prog (pos sa.reg.lpc) sA sA' ∧ Fin t sA' := by
  have hG := imgGate_of_imgGateCB hgate
  have hcl : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
      p + 1 < body.length := fun p bi ra t hb hbi => by
    have hk : p < body.length := (List.getElem?_eq_some_iff.mp hb).1
    by_contra hcn
    have he : p = body.length - 1 := by omega
    obtain ⟨r, hr, hret⟩ := hG.last
    rw [List.getLast?_eq_getElem?, ← he, hb] at hr
    cases hr
    rw [hbi] at hret
    cases hret
  exact haltsO_of_runChainS hX (callFlagsB_spec hflags) hcl
    (segSim_of_segExact hD
      (segExact_callImg hsep hphys hG hsites (condLiveB_spec hcond) hbytes hI hfin res args T
        fn) hFin)
    hStep (runChain_of_run _ T _ n s t hrun) sa sA hfn hlen hL hI0 hA

/-- **A halting run of the image of a calling body on an instruction set with procedures is
    a run of the decoded program under the oracle of the callee**, from Boolean checks and
    the byte simulation `ByteSeg` of the segments. Let the body pass `physImgB`, `imgGateCB`
    and `callSitesB`; let `callDeadB`, `callFlagsB` and `condLiveB` accept the table `D`;
    let the image `callImg` at the result name and the argument names of `c` pass
    `siteShapeB` at the symbol `f`, `T` give `f` the word reading `pr` of the callee, and
    the callee meet its specification; let every step of the instruction set `I` be a
    checked step of the x86 instruction set and the steps of `I` on the image keep the
    agreement of `D` (`DeadSteps`). Then, under the separation `CallerSep` and the byte
    simulation `ByteSeg`, every halting run of `I.withProcs T` on the image, from an image
    state in `fn` at a position of the body where no flag is live, related up to the dead
    names of its position to an address state that corresponds to a byte state, is matched
    by a run of `prog` under the oracle to a byte state that satisfies `Fin` with the end
    state. -/
theorem haltsO_of_deadChecks {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCB frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    (hroom : ∀ ret sA, sA.regs "%rsp" = rsp → room (entryOf ret sA))
    {prog : List RInstr} {pos : Nat → Nat} {tgt : Nat} {D : DeadTab}
    (hdead : callDeadB c res D.dead body = true) (hflags : callFlagsB D body = true)
    (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {f fn : String} (hT : T f = some pr)
    (hshape : siteShapeB f res c.args
      (callImg slotArr res (c.args.map LOperand.reg) body) = true)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I
      (singletonProgM fn (callImg slotArr res (c.args.map LOperand.reg) body)))
    {FinA : LstateA → AState → Prop}
    (hbytes : ByteSeg frame rsp body (oracleAt tgt X) prog pos tgt FinA)
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf → FinA sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (n : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr res (c.args.map LOperand.reg) body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : D.live sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    ∃ sA', HaltsO aMachine (oracleAt tgt X) prog (pos sa.reg.lpc) sA sA' ∧ Fin t sA' :=
  haltsO_of_deadChecksS hsep hphys hgate hsites hX hflags hcond hI hD hbytes hfin hFin
    (fun _ _ _ hg hb => siteStep_word hsep hphys hX hw hS hF hroom hdead hb
      (glue_regArgs hw.wordOnly hw.wordRet (sitesOf_of_siteShapeB hshape hT) hg))
    n hrun hfn hlen hL hI0 hA

/-! ## 9b. The byte simulation from the checks of the relocated layout -/

/-- A call of a named symbol is a remote transfer. -/
theorem remoteSym_of_remoteCallB {i : LinstrR} (h : remoteCallB i = true) :
    remoteSym i ≠ none := by
  cases i with
  | Lcall ra tg =>
    obtain ⟨f, l⟩ := tg
    have hf : f.isEmpty = false := by simpa [remoteCallB] using h
    simp [remoteSym, hf]
  | _ => simp [remoteCallB] at h

/-- **The facts of a body of the class with calls** whose shapes are `ds`. -/
theorem callFacts_of_printedAddrCB {G : Nat} {body : Lcmd} {ds : List PhysAbiShape.DShape}
    (h : printedAddrCB G body = true)
    (hs : DecodeGen.shapesOf (Params.ofBody body) body
      = some ds) :
    LprogBytesLinkReloc.CallFacts body ds := by
  simp only [printedAddrCB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, hlast⟩, hall⟩, hcond⟩, -⟩ := h
  refine LprogBytesLinkReloc.callFacts_of_checks hs hlast (fun i hi => ?_) hcond
  have hi' := List.all_eq_true.mp hall i hi
  simp only [instrOKCB, Bool.or_eq_true] at hi'
  exact hi'.imp remoteSym_of_remoteCallB id

/-- **The byte simulation `ByteSeg` of a relocated body.** For a body with the facts
    `CallFacts`, a program `prog` that satisfies `LinkedProg` at the index `K`, and a frame
    that agrees with the frame of the body parameters at the names of the body, `ByteSeg`
    holds under every oracle at the index `DecodePrintedCFG.posOf` and the target `K`,
    with the end `LprogBytesLinkReloc.FinLea`. -/
theorem byteSeg_of_linked {body : Lcmd} {ds : List PhysAbiShape.DShape}
    (hF : LprogBytesLinkReloc.CallFacts body ds) {K : Nat} {prog : List RInstr}
    (hL : LprogBytesLinkReloc.LinkedProg body ds K
      (Params.ofBody body).frame prog)
    (rsp : BitVec 64) {frame : String → Option (BitVec 64)}
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (O : Nat → AState → AState → Prop) :
    ByteSeg frame rsp body O prog
      (DecodePrintedCFG.posOf ds) K
      (LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame) := by
  obtain ⟨h1, h2, h3, h4⟩ := LprogBytesLinkReloc.linked_seg hF hL rsp hfr O
  exact ⟨h1, h2, h3, h4⟩

/-- **A halting run of the image of a calling body at the steps of its call sites is a run
    of the program of its relocated item list under the oracle of the callee**, from Boolean
    checks. The hypotheses are those of `haltsO_of_deadChecksS` with the byte simulation
    replaced by: the class `printedAddrCB`, the shapes `ds` of the body, the program
    `prog` of the relocated item list in front of a callee block at the index `tgt`, and the
    agreement of `frame` with the frame of the body parameters at the names of the body.
    The run starts at the index `DecodePrintedCFG.posOf` of the position of the address
    state, and the end is `LprogBytesLinkReloc.FinLea`. -/
theorem haltsO_of_linkedChecksS {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCB frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {G : Nat} {ds : List PhysAbiShape.DShape} (hcls : printedAddrCB G body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body
      = some ds)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (symBase : String → Option Int) {prog : List RInstr} {tgt L : Nat}
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) tgt L
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {D : DeadTab} (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {fn res : String} {args : List LOperand} {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr res args body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (hStep : ∀ p u v, Glue T (singletonProgM fn (callImg slotArr res args body)) p u v →
      (∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t) →
      SiteStep frame slotArr base rsp body X c (D.dead p) (D.dead (p + 1)) u v)
    (n : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr res args body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : D.live sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    ∃ sA', HaltsO aMachine (oracleAt tgt X) prog
        (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
      ∧ Fin t sA' := by
  have hCF := callFacts_of_printedAddrCB hcls hshapes
  exact haltsO_of_deadChecksS hsep hphys hgate hsites hX hflags hcond hI hD
    (byteSeg_of_linked hCF
      (LprogBytesLinkReloc.linkedProg_of_items symBase hCF tgt L prog hP) rsp hfr _)
    hfin hFin hStep n hrun hfn hlen hL hI0 hA

/-- **A halting run of the image of a calling body is a run of the program of its
    relocated item list under the oracle of the callee**, from Boolean checks. The
    hypotheses are those of `haltsO_of_deadChecks` with the byte simulation replaced by:
    the class `printedAddrCB`, the shapes `ds` of the body, the program `prog` of
    the relocated item list in front of a callee block at the index `tgt`, and the
    agreement of `frame` with the frame of the body parameters at the names of the body.
    The run starts at the index `DecodePrintedCFG.posOf` of the position of the address
    state, and the end is `LprogBytesLinkReloc.FinLea`. -/
theorem haltsO_of_linkedChecks {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCB frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    (hroom : ∀ ret sA, sA.regs "%rsp" = rsp → room (entryOf ret sA))
    {ds : List PhysAbiShape.DShape} (hcls : printedAddrCB G body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body
      = some ds)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (symBase : String → Option Int) {prog : List RInstr} {tgt L : Nat}
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) tgt L
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {D : DeadTab}
    (hdead : callDeadB c res D.dead body = true) (hflags : callFlagsB D body = true)
    (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {f fn : String} (hT : T f = some pr)
    (hshape : siteShapeB f res c.args
      (callImg slotArr res (c.args.map LOperand.reg) body) = true)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I
      (singletonProgM fn (callImg slotArr res (c.args.map LOperand.reg) body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (n : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr res (c.args.map LOperand.reg) body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : D.live sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    ∃ sA', HaltsO aMachine (oracleAt tgt X) prog
        (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
      ∧ Fin t sA' :=
  haltsO_of_linkedChecksS hsep hphys hgate hsites hX hcls hshapes hfr symBase hP hflags hcond
    hI hD hfin hFin
    (fun _ _ _ hg hb => siteStep_word hsep hphys hX hw hS hF hroom hdead hb
      (glue_regArgs hw.wordOnly hw.wordRet (sitesOf_of_siteShapeB hshape hT) hg))
    n hrun hfn hlen hL hI0 hA

/-- **A halting run of the image of a calling body at the steps of its call sites is a run
    through calls of the program its linked bytes decode to**, from Boolean checks. Let the
    callee block `cb` decode to a block `q` without `call` whose leaky runs meet the
    specification of `c`, and let the relocated item list of the body satisfy
    `branchOKReloc` and denote `prog` at its own instruction count and byte length. Under the
    other hypotheses of `haltsO_of_linkedChecksS`, the bytes of the relocated body followed
    by `cb` decode to `prog` followed by `q` with its targets raised, and this program has a
    run through calls from the index of the position of the address state to a byte state
    that satisfies `Fin` with the end state. -/
theorem haltsC_of_linkedChecksS {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCB frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    (r : CatCrypt.Crypto.SecureCompilation.CT.DoitRegime) {q : List RInstr} {c : CalleeSig}
    (hX : CalleeSpec (Callee.runOf r q) c) (hq : ∀ tg, RInstr.call tg ∉ q)
    {G : Nat} {ds : List PhysAbiShape.DShape} (hcls : printedAddrCB G body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body
      = some ds)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (symBase : String → Option Int) {cb : List (BitVec 8)} {prog : List RInstr}
    (hcb : LprogBytesDecode.decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : LprogBytesLinkReloc.branchOKReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length 0
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = true)
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {D : DeadTab} (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {fn res : String} {args : List LOperand} {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr res args body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (hStep : ∀ p u v, Glue T (singletonProgM fn (callImg slotArr res args body)) p u v →
      (∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t) →
      SiteStep frame slotArr base rsp body (Callee.runOf r q) c (D.dead p) (D.dead (p + 1)) u v)
    (n : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr res args body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : D.live sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    LprogBytesDecode.decodeLprog (LprogBytes.encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ LprogBytesLink.shiftProg prog.length q)
      ∧ ∃ sA', RInstrSemantics.HaltsC aMachine (prog ++ LprogBytesLink.shiftProg prog.length q)
          (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
        ∧ Fin t sA' := by
  have hCF := callFacts_of_printedAddrCB hcls hshapes
  obtain ⟨hsaves, hF0, hFr⟩ := printedAddrCB_reloc hcls
  obtain ⟨hdec, hLk⟩ := LprogBytesLinkReloc.linkedProg_of_bytes symBase hCF cb q prog hsaves
    hF0 hFr hcb hne hbr hP
  obtain ⟨sA', hrun', hfin'⟩ := haltsO_of_deadChecksS hsep hphys hgate hsites hX hflags hcond
    hI hD (byteSeg_of_linked hCF hLk rsp hfr _) hfin hFin hStep n hrun hfn hlen hL hI0 hA
  exact ⟨hdec, sA', Callee.haltsC_append_of_haltsO_runOf r prog q hq hrun', hfin'⟩

/-- **A halting run of the image of a calling body is a run through calls of the program
    its linked bytes decode to**, from Boolean checks. Let the callee block `cb` decode to
    a block `q` without `call` whose leaky runs meet the specification of `c`, and let the
    relocated item list of the body satisfy `branchOKReloc` and denote `prog` at its own
    instruction count and byte length. Under the other hypotheses of
    `haltsO_of_linkedChecks`, the bytes of the relocated body followed by `cb` decode to
    `prog` followed by `q` with its targets raised, and this program has a run through
    calls from the index of the position of the address state to a byte state that
    satisfies `Fin` with the end state. -/
theorem haltsC_of_linkedChecks {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCB frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    (r : CatCrypt.Crypto.SecureCompilation.CT.DoitRegime) {q : List RInstr} {c : CalleeSig}
    (hX : CalleeSpec (Callee.runOf r q) c) (hq : ∀ tg, RInstr.call tg ∉ q) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    (hroom : ∀ ret sA, sA.regs "%rsp" = rsp → room (entryOf ret sA))
    {ds : List PhysAbiShape.DShape} (hcls : printedAddrCB G body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body
      = some ds)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (symBase : String → Option Int) {cb : List (BitVec 8)} {prog : List RInstr}
    (hcb : LprogBytesDecode.decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : LprogBytesLinkReloc.branchOKReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length 0
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = true)
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {D : DeadTab}
    (hdead : callDeadB c res D.dead body = true) (hflags : callFlagsB D body = true)
    (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {f fn : String} (hT : T f = some pr)
    (hshape : siteShapeB f res c.args
      (callImg slotArr res (c.args.map LOperand.reg) body) = true)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t →
      JasminLsemMemChecked.evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I
      (singletonProgM fn (callImg slotArr res (c.args.map LOperand.reg) body)))
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel frame slotArr base body t sa zf →
      LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame sa sA → Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (n : Nat) {s t : LstateMF}
    (hrun : (I.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr res (c.args.map LOperand.reg) body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : D.live sa.reg.lpc = false)
    (hI0 : ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa) (hA : ACorr rsp sA sa) :
    LprogBytesDecode.decodeLprog (LprogBytes.encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ LprogBytesLink.shiftProg prog.length q)
      ∧ ∃ sA', RInstrSemantics.HaltsC aMachine (prog ++ LprogBytesLink.shiftProg prog.length q)
          (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
        ∧ Fin t sA' :=
  haltsC_of_linkedChecksS hsep hphys hgate hsites r hX hq hcls hshapes hfr symBase hcb hne hbr
    hP hflags hcond hI hD hfin hFin
    (fun _ _ _ hg hb => siteStep_word hsep hphys hX hw hS hF hroom hdead hb
      (glue_regArgs hw.wordOnly hw.wordRet (sitesOf_of_siteShapeB hshape hT) hg))
    n hrun hfn hlen hL hI0 hA

/-! ## 10. The allocation pool and the common names of a callee -/

open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (lfundefPhysAbiOfVirtAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (keepPool keepPoolB keepPoolB_spec)

/-- **A name of a checked allocation pool is kept by the summary step of a call**: it is
    not set by `callSumC` and is not among the names `exemptC c`. -/
theorem keepPoolB_clobN {c : CalleeSig} {pool : List String} (h : keepPoolB c pool = true)
    {r : String} (hr : r ∈ pool) : clobN c r = false ∧ r ∉ exemptC c := by
  have hk := ((keepPoolB_spec h).1 r hr).2.1
  refine ⟨by simp [clobN, hk], fun hm => ?_⟩
  simp [exemptC, hk] at hm

/-- **The allocation of a virtual function that calls `c`, with its allocation
    certificate**: the allocation `lfundefPhysAbiOfVirtCert` at the register file
    `poolAbi (keepPool c)` of the names kept across a call of `c`, with the shadow
    instructions expanded on the allocated body at the out symbols `outs`, whose calls copy
    no result register, and the certificate of that allocation. -/
def lfundefPhysAbiOfVirtCCert (c : CalleeSig) (virt0 : Lfundef) (outArg' : String)
    (inArgs' accRegs abiArgs : List String) (abiTyin : List Nat) (posBind : Bool)
    (outs : List String := []) : Lfundef × List (String × String) :=
  let fc := lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs (abiArgs := abiArgs)
    (abiTyin := abiTyin) (abi := VIR.LprogCallCut.poolAbi (keepPool c)) (posBind := posBind)
  ({ fc.1 with lfd_body := expandCallShadows fc.1.lfd_body outs }, fc.2)

/-- **The allocation of a virtual function that calls `c`**: the function of
    `lfundefPhysAbiOfVirtCCert`, which is `lfundefPhysAbiOfVirtAt` at the pool `keepPool c`
    (`lfundefPhysAbiOfVirtC_eq_at`). -/
def lfundefPhysAbiOfVirtC (c : CalleeSig) (virt0 : Lfundef) (outArg' : String)
    (inArgs' accRegs abiArgs : List String) (abiTyin : List Nat) (posBind : Bool)
    (outs : List String := []) : Lfundef :=
  (lfundefPhysAbiOfVirtCCert c virt0 outArg' inArgs' accRegs abiArgs abiTyin posBind outs).1

/-- The function of `lfundefPhysAbiOfVirtCCert` is `lfundefPhysAbiOfVirtC`. -/
theorem lfundefPhysAbiOfVirtCCert_fst (c : CalleeSig) (virt0 : Lfundef) (outArg' : String)
    (inArgs' accRegs abiArgs : List String) (abiTyin : List Nat) (posBind : Bool)
    (outs : List String) :
    (lfundefPhysAbiOfVirtCCert c virt0 outArg' inArgs' accRegs abiArgs abiTyin posBind outs).1
      = lfundefPhysAbiOfVirtC c virt0 outArg' inArgs' accRegs abiArgs abiTyin posBind outs :=
  rfl

/-- The allocation of a caller of `c` is `lfundefPhysAbiOfVirtAt` at the pool
    `keepPool c`. -/
theorem lfundefPhysAbiOfVirtC_eq_at (c : CalleeSig) (virt0 : Lfundef) (outArg' : String)
    (inArgs' accRegs abiArgs : List String) (abiTyin : List Nat) (posBind : Bool)
    (outs : List String) :
    lfundefPhysAbiOfVirtC c virt0 outArg' inArgs' accRegs abiArgs abiTyin posBind outs
      = lfundefPhysAbiOfVirtAt (keepPool c) virt0 outArg' inArgs' accRegs abiArgs abiTyin
        posBind outs := rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
