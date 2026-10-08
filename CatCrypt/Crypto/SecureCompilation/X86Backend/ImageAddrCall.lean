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
* `SegSim`: the statement of the simulation of one segment `LprogCallCut.SegTo` of a body
  with shadow instructions, at a table of dead names.
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
* `haltsO_of_runChain`: a chain `LprogCallCut.RunChain` with `SegSim` is a run under the
  oracle.
* `procStep_regArgs`, `glue_regArgs`: the step `LprogCallCut.Glue` is the step of the
  summary at the argument words.
* `haltsO_of_withProcs_run`: a halting run on the machine with procedures is a run under
  the oracle, from `SegSim`.
* `printedAddrCB_of_printedAddrB`, `printedAddrB_iff_of_callFree`, `imgGateCB_of_callFree`:
  on a body without calls the classes are the existing ones.
* `printedAddrCB_reloc`, `printedAddrCB_remote`, `relocShapeOK_of_printedAddrCB`,
  `printedAddrCB_frameAbove`: the facts of the class for the relocating encoder and for the
  frame.
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
  · rw [retOps_eq, hl, if_pos rfl, h.rsp _ t sc hpre hX, entryOf_regs, if_pos rfl, retWord,
      BitVec.add_assoc]
    simp
  · rw [retOps_eq, hl, if_neg hr]
  · rw [retOps_eq, hl, if_neg hr, h.keep _ t sc hpre hX r hcl, entryOf_regs, if_neg hr]
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
    fun b q a A n hr => ?_⟩
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
    rw [entryOf_regs, if_pos rfl, retWord, hsp]
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
    whose argument registers the summary is defined; and the postcondition gives the word
    of the summary in the register of `res` at the return. -/
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
  rw [entryOf_regs, if_neg (gpFacts hg).physNe, argWord_congr (hrel.regs a (hsep.gp a hg))]
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
    rw [if_pos rfl, if_pos hcl, hv]
  · rw [if_neg h1]
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
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
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

/-! ## 8. Chains of segments -/

open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (RunChain SegTo Glue runChain_of_run)

/-- **The statement of the simulation of one segment** of the image of a calling body by
    the decoded program `prog` under the oracle `O`, with `pos` the index in `prog` of a
    position of the body and `E` the dead names at each position. From an image state
    related, up to the dead names of its position and the flags, to an address state that
    corresponds to a byte state:

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
    (body : Lcmd) (E : Nat → List String) (O : Nat → AState → AState → Prop)
    (prog : List RInstr) (pos : Nat → Nat) (tgt : Nat)
    (Seg : LstateMF → Option Nat → LstateMF → Prop) (Fin : LstateMF → AState → Prop) :
    Prop where
  /-- A segment to a call. -/
  toCall : ∀ s sa sA p u, ImgRelF frame slotArr base body (E sa.reg.lpc) s sa →
    ACorr rsp sA sa → Seg s (some p) u →
    ∃ sa' sA', ImgRelF frame slotArr base body (E p) u sa' ∧ ACorr rsp sA' sa'
      ∧ sa'.reg.lpc = p
      ∧ (∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t)
      ∧ prog[pos p]? = some (.call tgt)
      ∧ ∀ s'', HaltsO aMachine O prog (pos p) sA' s'' →
          HaltsO aMachine O prog (pos sa.reg.lpc) sA s''
  /-- A segment to an end state. -/
  toEnd : ∀ s sa sA t, ImgRelF frame slotArr base body (E sa.reg.lpc) s sa →
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

/-- **A chain of segments is a run under the oracle of the callee.** Let the segments
    `SegTo I T P` of a calling body of the class `physImgB` have the simulation `SegSim` at
    the dead names `E` and the oracle of a callee `X` at `tgt`, with `CalleeSpec X c`, the
    word reading `pr` and the separation `CallerSep`; let `callDeadB` accept `E`, each step
    `Glue T P` be the step of the summary `pr` at the argument words, and `room` hold at the
    entry state of every call from a byte state with the stack register `rsp`. Then every
    chain `RunChain I T P` from an image state related, up to the dead names of its position
    and the flags, to an address state that corresponds to a byte state is matched by a run
    of `prog` under the oracle to a byte state that satisfies `Fin` with the end state of
    the chain. -/
theorem haltsO_of_runChain {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    (hroom : ∀ ret sA, sA.regs "%rsp" = rsp → room (entryOf ret sA))
    {prog : List RInstr} {pos : Nat → Nat} {tgt : Nat} {E : Nat → List String}
    (hdead : callDeadB c res E body = true)
    {I : LprogIsa.Isa} {T : LprogIsa.ProcTable} {P : LprogM}
    {Fin : LstateMF → AState → Prop}
    (hsim : SegSim frame slotArr base rsp body E (oracleAt tgt X) prog pos tgt (SegTo I T P)
      Fin)
    (hCall : ∀ p u v, Glue T P p u v → ∃ w,
      pr.run (c.args.map (argWord u.prog.base.reg)) = some w ∧ v = LprogIsa.retWord res w u)
    {s t : LstateMF} (hch : RunChain I T P s t) :
    ∀ sa sA, ImgRelF frame slotArr base body (E sa.reg.lpc) s sa → ACorr rsp sA sa →
      ∃ sA', HaltsO aMachine (oracleAt tgt X) prog (pos sa.reg.lpc) sA sA' ∧ Fin t sA' := by
  induction hch with
  | done hseg => exact fun sa sA hI hA => hsim.toEnd _ sa sA _ hI hA hseg
  | call p hseg hcall _ ih =>
    intro sa sA hI hA
    obtain ⟨sa1, sA1, hI1, hc1, hpc1, ⟨bi, ra, tg, hb, hbi⟩, hprog, hk⟩ :=
      hsim.toCall _ sa sA p _ hI hA hseg
    obtain ⟨w, hw', rfl⟩ := hCall _ _ _ hcall
    subst hpc1
    obtain ⟨hargs, hsub⟩ := callDeadB_spec hdead hb hbi
    obtain ⟨sA2, sa2, -, hpc2, hc2, hI2, hcont⟩ :=
      haltsO_call_imageF hsep hphys hX hw hS hF hI1 hargs hc1 hb hbi hprog
        (hroom _ sA1 hc1.sp) hw'
    obtain ⟨sA', hrun, hfin⟩ := ih sa2 sA2 (by rw [hpc2]; exact hI2.mono hsub) hc2
    rw [hpc2, hsim.pos_call _ bi ra tg hb hbi] at hrun
    exact ⟨sA', hk _ (hcont _ hrun), hfin⟩

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
theorem procStep_regArgs {pr : LprogIsa.ProcSummary} {res : String} {args : List String}
    {u v : LstateMF} (h : LprogIsa.procStep pr res (args.map LOperand.reg) u = some v) :
    ∃ w, pr.run (args.map (argWord u.prog.base.reg)) = some w
      ∧ v = LprogIsa.retWord res w u := by
  unfold LprogIsa.procStep at h
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
    {pr : LprogIsa.ProcSummary} {res : String} {args : List String}
    (hsite : SitesOf T B pr res args) {p : Nat} {u v : LstateMF}
    (hg : Glue T (singletonProgM fn B) p u v) :
    ∃ w, pr.run (args.map (argWord u.prog.base.reg)) = some w
      ∧ v = LprogIsa.retWord res w u := by
  obtain ⟨i, pr', dst, srcs, hi, hq, hstep⟩ := hg
  obtain ⟨rfl, rfl, rfl⟩ := hsite p i pr' dst srcs hi hq
  exact procStep_regArgs hstep

/-- **A run of a body with shadow instructions on the machine with procedures is a run of
    the decoded program under the oracle of the callee.** Let `B` be a body whose shadow
    instructions are calls of the summary `pr` on the argument registers of `c` with the
    destination `res`, and let the segments of `B` on the x86 instruction set have the
    simulation `SegSim` under the hypotheses of `haltsO_of_runChain`. Then every halting
    run of `x86Isa.withProcs T` on `B`, from an image state related, up to the dead names
    of its position and the flags, to an address state that corresponds to a byte state, is
    matched by a run of `prog` under the oracle to a byte state that satisfies `Fin` with
    the end state. -/
theorem haltsO_of_withProcs_run {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {res : String}
    {pr : LprogIsa.ProcSummary} {room : AState → Prop} (hw : WordCallee c res pr room)
    {G : Nat} (hS : CallerSep frame slotArr base rsp G) (hF : FootBelow c G)
    (hroom : ∀ ret sA, sA.regs "%rsp" = rsp → room (entryOf ret sA))
    {prog : List RInstr} {pos : Nat → Nat} {tgt : Nat} {E : Nat → List String}
    (hdead : callDeadB c res E body = true)
    {T : LprogIsa.ProcTable} {fn : String} {B : List LinstrRM}
    {Fin : LstateMF → AState → Prop} (hsite : SitesOf T B pr res c.args)
    (hsim : SegSim frame slotArr base rsp body E (oracleAt tgt X) prog pos tgt
      (SegTo X86Isa.x86Isa T (singletonProgM fn B)) Fin)
    (n : Nat) {s t : LstateMF}
    (hrun : (X86Isa.x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B) n s = some t)
    {sa : LstateA} {sA : AState} (hI : ImgRelF frame slotArr base body (E sa.reg.lpc) s sa)
    (hA : ACorr rsp sA sa) :
    ∃ sA', HaltsO aMachine (oracleAt tgt X) prog (pos sa.reg.lpc) sA sA' ∧ Fin t sA' :=
  haltsO_of_runChain hsep hphys hX hw hS hF hroom hdead hsim
    (fun _ _ _ hg => glue_regArgs hsite hg) (runChain_of_run _ T _ n s t hrun) sa sA hI hA

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

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
