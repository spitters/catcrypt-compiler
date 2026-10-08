/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallX

@[expose] public section

set_option autoImplicit false

/-!
# The image call step with a read-only word-array argument

`ImageAddrCall.call_reestablishes_word` is the step of the image relation across a call to
a callee read as a procedure summary on the words of its argument registers. This module
states the same step for a callee whose last argument register holds the address of a word
array of the caller that the callee only reads. The summary input is the argument words
followed by the `n` words of the array read from memory at the pointer (`readArgs`). On the
image the pointer register holds the base of the array, which follows from its reload out
of the saved frame word (`ptrW_of_reload`), and the summary input is the argument words
followed by the array of the image state (`imgArgs`). The footprint of the callee stays
its frame, so `ImageAddrCall.FootBelow`, `ImageAddrCall.call_reestablishes` and
`ImageAddrCall.callSumC` are used unchanged.

## Main definitions

* `arrLen`: the length of the array of a frame slot of a body.
* `arrWords`, `readArgs`: the `n` words at an address, and the summary input at an entry
  state: the argument words followed by the array words at the pointer register.
* `imgArgs`: the summary input on the image: the argument words followed by an array.
* `ArrCallee`: the reading of an interface as a procedure summary on the argument words and
  the contents of one array argument.

## Main results

* `ptrW_of_reload`: after the reload of an array pointer from its saved frame word, the
  reloaded register holds the base of the array.
* `readArgs_entry`: at the entry of a call, the summary input read from the byte state is
  the summary input on the image.
* `pre_of_imageArr`: the precondition of the callee from the image relation.
* `call_reestablishes_arr`: after every run of the callee, the result register holds the
  word of the summary and the relaxed relation holds at the step of the summary.
* `call_reestablishes_arr_reload`: the same, with the pointer register reloaded from the
  saved frame word of the array.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArr

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (retOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk gpFacts phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr redW read64_eq_of_agree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe
  (retWord entryOf entryOf_regs entryOf_mem outOf argWord read64_congr_range)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSig CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

/-! ## 1. The summary input with an array argument -/

/-- The length of the array of the frame slot `q`, `0` when `q` is not an array slot. -/
def arrLen (slotArr : String → Option (String × Nat)) (q : String) : Nat :=
  ((slotArr q).map Prod.snd).getD 0

theorem arrLen_of_slot {slotArr : String → Option (String × Nat)} {q A : String} {n : Nat}
    (h : slotArr q = some (A, n)) : arrLen slotArr q = n := by
  simp [arrLen, h]

/-- The `n` words of the memory `m` at the address `p`. -/
def arrWords (m : AMem) (p : BitVec 64) (n : Nat) : List (BitVec 64) :=
  (List.range n).map fun j => read64 m (cellAt p j)

/-- **The summary input at an entry state**: the words of the argument registers of `ws`,
    followed by the `n` words of memory at the address in the register of `pa`. -/
def readArgs (ws : List String) (pa : String) (n : Nat) (s : AState) : List (BitVec 64) :=
  ws.map (fun a => s.regs (phys a)) ++ arrWords s.mem (s.regs (phys pa)) n

/-- **The summary input on the image**: the argument words of `ws` in the register file `R`,
    followed by the words of the array `arr`. -/
def imgArgs (R : LstateN) (ws : List String) {n : Nat} (arr : Fin n → BitVec 64) :
    List (BitVec 64) :=
  ws.map (argWord R) ++ List.ofFn arr

/-- **The reading of an interface as a procedure summary on words and one array.** The
    argument registers are those of the word names `ws` followed by the pointer name `pa`;
    these and the result name `res` are general-purpose names and the register of `res` is
    in the clobber set; the precondition holds at an entry state that satisfies `room` and
    at whose `readArgs` the summary is defined; and the postcondition gives the word of the
    summary at `readArgs` in the register of `res` at the return. -/
structure ArrCallee (c : CalleeSig) (ws : List String) (pa : String) (n : Nat) (res : String)
    (pr : LprogIsa.ProcSummary) (room : AState → Prop) : Prop where
  /-- The argument registers: the words, then the pointer. -/
  args_eq : c.args = ws ++ [pa]
  /-- The word argument names are general-purpose names. -/
  ws_gp : ∀ a ∈ ws, gpOk a = true
  /-- The pointer name is a general-purpose name. -/
  pa_gp : gpOk pa = true
  /-- The result register of the interface is that of `res`. -/
  res_eq : c.res = some res
  /-- The result name is a general-purpose name. -/
  res_gp : gpOk res = true
  /-- The register of the result name is in the clobber set. -/
  res_clob : c.clob (phys res) = true
  /-- The precondition, from `room` and a defined summary. -/
  pre : ∀ s, room s → (pr.run (readArgs ws pa n s)).isSome = true → c.pre s
  /-- The result register at the return holds the word of the summary. -/
  post : ∀ s s', c.pre s → c.post s s' → pr.run (readArgs ws pa n s) = some (s'.regs (phys res))

/-! ## 2. The pointer and the array at the entry of a call -/

/-- **The reloaded pointer holds the base.** Under `ImgRel`, if the register `b` without a
    frame word is the reload at the position of the address state of the frame slot of the
    saved register `R`, which is the slot of the array `A`, and the save of `R` is before
    that position, then `b` holds the base of `A`. -/
theorem ptrW_of_reload {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {s : LstateMF} {sa : LstateA} {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf)
    {b R A : String} {n k : Nat} {a : BitVec 64}
    (hre : reloadOf slotArr body sa.reg.lpc b = some (slotOfReg R))
    (hA : slotArr (slotOfReg R) = some (A, n)) (ha : frame (slotOfReg R) = some a)
    (hb : frame b = none) (hS : SaveAt body k R) (hk : k < sa.reg.lpc) :
    sa.reg.getW b 64 = some (base A) := by
  rw [getW_eq_some_iff, hrel.reload b _ a A n hre hA ha hb, (hrel.saved k R A n a hS hA ha).1 hk]

/-- **The summary input at the entry of a call.** Under `ImgSep`, `ImgRel`, `ACorr` and
    `CallerSep`, with the pointer name `pa` holding the base of the array `A` of a frame
    slot, the summary input read from the entry state of the call is the summary input on
    the image with the array of `A`. -/
theorem readArgs_entry {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) {G : Nat}
    (hS : CallerSep frame slotArr base rsp G) {ws : List String} (hws : ∀ a ∈ ws, gpOk a = true)
    {pa : String} (hpa : gpOk pa = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {sA : AState} (hc : ACorr rsp sA sa)
    {q A : String} {n : Nat} (hq : slotArr q = some (A, n))
    (hptr : sa.reg.getW pa 64 = some (base A)) {arr : Fin n → BitVec 64}
    (harr : s.prog.base.getArr A 64 n = some arr) (ret : Nat) :
    readArgs ws pa n (entryOf ret sA) = imgArgs s.prog.base.reg ws arr := by
  unfold readArgs imgArgs
  congr 1
  · exact args_entry hsep hws hrel hc ret
  · have hp : (entryOf ret sA).regs (phys pa) = base A := by
      rw [entryOf_regs, if_neg (gpFacts hpa).physNe]
      exact Option.some.inj ((hc.regs pa hpa).symm.trans hptr)
    obtain ⟨arr', harr', hcell⟩ := hrel.cells q A n hq
    rw [harr] at harr'
    cases harr'
    rw [hp]
    refine List.ext_getElem (by simp [arrWords]) fun j h1 h2 => ?_
    have hj : j < n := by simpa [arrWords] using h1
    simp only [arrWords, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [← hcell j hj, read64_eq_of_agree (fun x hx => hc.mem x hx) (hsep.red q A n j hq hj)]
    refine read64_congr_range fun x hx => entryOf_mem ret sA x ?_
    rw [retWord, hc.sp]
    exact (hS.cells q A n j hq hj x hx).1

/-- **The precondition of the callee from the image relation.** Under the hypotheses of
    `readArgs_entry`, if the entry state of the call satisfies `room` and the summary is
    defined at the summary input on the image, the entry state satisfies the
    precondition. -/
theorem pre_of_imageArr {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) {G : Nat}
    (hS : CallerSep frame slotArr base rsp G) {c : CalleeSig} {ws : List String} {pa : String}
    {n : Nat} {res : String} {pr : LprogIsa.ProcSummary} {room : AState → Prop}
    (hw : ArrCallee c ws pa n res pr room) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {sA : AState} (hc : ACorr rsp sA sa)
    {q A : String} (hq : slotArr q = some (A, n)) (hptr : sa.reg.getW pa 64 = some (base A))
    {arr : Fin n → BitVec 64} (harr : s.prog.base.getArr A 64 n = some arr) (ret : Nat)
    (hroom : room (entryOf ret sA)) {v : BitVec 64}
    (hv : pr.run (imgArgs s.prog.base.reg ws arr) = some v) :
    c.pre (entryOf ret sA) := by
  refine hw.pre _ hroom ?_
  rw [readArgs_entry hsep hS hw.ws_gp hw.pa_gp hrel hc hq hptr harr ret, hv]
  rfl

/-! ## 3. The call step -/

/-- **A call with a read-only array argument re-establishes the relaxed relation.** Let
    `ImgRel` and `ACorr` hold at a call instruction of a body of the class `physImgB`, the
    callee meet its specification and have the reading `pr` on the words `ws` and the `n`
    words at the pointer `pa`, the caller be separated (`CallerSep`) for a callee whose
    footprint is among the `G` bytes below its entry stack register, the pointer name hold
    the base of the array `A` of a frame slot, the entry state satisfy `room`, and the
    summary give the word `v` at the argument words and the array of the image state. Then
    the entry state satisfies the precondition, and for every run of the callee, after the
    return: the result register holds `v`, and there is an address state at the next
    position that corresponds to the byte state and is related, up to the names `exemptC c`
    and the flags, to the image state after the step of the summary. -/
theorem call_reestablishes_arr {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {ws : List String} {pa : String}
    {n : Nat} {res : String} {pr : LprogIsa.ProcSummary} {room : AState → Prop}
    (hw : ArrCallee c ws pa n res pr room) {G : Nat} (hS : CallerSep frame slotArr base rsp G)
    (hF : FootBelow c G) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {sA : AState} (hc : ACorr rsp sA sa)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {ra : Option String}
    {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt)
    {q A : String} (hq : slotArr q = some (A, n)) (hptr : sa.reg.getW pa 64 = some (base A))
    {arr : Fin n → BitVec 64} (harr : s.prog.base.getArr A 64 n = some arr) (ret : Nat)
    (hroom : room (entryOf ret sA)) {v : BitVec 64}
    (hv : pr.run (imgArgs s.prog.base.reg ws arr) = some v) :
    c.pre (entryOf ret sA) ∧ ∀ t sc, X (entryOf ret sA) t sc →
      (retOps.foldl aMachine.exec sc).regs (phys res) = v
        ∧ ∃ sa', sa'.reg.lpc = sa.reg.lpc + 1
          ∧ ACorr rsp (retOps.foldl aMachine.exec sc) sa'
          ∧ ImgRelF frame slotArr base body (exemptC c) (LprogIsa.retWord res v s) sa' := by
  have hpre := pre_of_imageArr hsep hS hw hrel hc hq hptr harr ret hroom hv
  refine ⟨hpre, fun t sc hrun => ?_⟩
  obtain ⟨hA, hI, hpost⟩ := call_reestablishes hsep hphys hX hrel hc hb hbi ret hpre
    (footClear_of_callerSep hS hF hc.sp ret) hrun ⟨fun _ => 0, false, false, false⟩
  have hres : (retOps.foldl aMachine.exec sc).regs (phys res) = v := by
    have h1 := hw.post _ _ hpre hpost
    rw [readArgs_entry hsep hS hw.ws_gp hw.pa_gp hrel hc hq hptr harr ret, hv] at h1
    rw [(call_return hX ret sA hpre hrun).2.1 _ (gpFacts hw.res_gp).physNe]
    exact (Option.some.inj h1).symm
  exact ⟨hres, _, rfl, hA, _, _,
    agreeOffF_retWord c (outOf (retOps.foldl aMachine.exec sc) _) s hw.res_eq
      (by simp [clobN, hw.res_gp, hw.res_clob]) hres,
    hI⟩

/-- **The call step with the pointer reloaded from its saved frame word.** As
    `call_reestablishes_arr`, where the pointer name `pa` is the reload, at the position of
    the call, of the frame slot of the saved register `R`, which is the slot of the array
    `A`, and the save of `R` is before the call. -/
theorem call_reestablishes_arr_reload {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {ws : List String} {pa : String}
    {n : Nat} {res : String} {pr : LprogIsa.ProcSummary} {room : AState → Prop}
    (hw : ArrCallee c ws pa n res pr room) {G : Nat} (hS : CallerSep frame slotArr base rsp G)
    (hF : FootBelow c G) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {sA : AState} (hc : ACorr rsp sA sa)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {ra : Option String}
    {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt)
    {R A : String} {k : Nat} {a : BitVec 64}
    (hre : reloadOf slotArr body sa.reg.lpc pa = some (slotOfReg R))
    (hA : slotArr (slotOfReg R) = some (A, n)) (ha : frame (slotOfReg R) = some a)
    (hS0 : SaveAt body k R) (hk : k < sa.reg.lpc)
    {arr : Fin n → BitVec 64} (harr : s.prog.base.getArr A 64 n = some arr) (ret : Nat)
    (hroom : room (entryOf ret sA)) {v : BitVec 64}
    (hv : pr.run (imgArgs s.prog.base.reg ws arr) = some v) :
    c.pre (entryOf ret sA) ∧ ∀ t sc, X (entryOf ret sA) t sc →
      (retOps.foldl aMachine.exec sc).regs (phys res) = v
        ∧ ∃ sa', sa'.reg.lpc = sa.reg.lpc + 1
          ∧ ACorr rsp (retOps.foldl aMachine.exec sc) sa'
          ∧ ImgRelF frame slotArr base body (exemptC c) (LprogIsa.retWord res v s) sa' :=
  call_reestablishes_arr hsep hphys hX hw hS hF hrel hc hb hbi hA
    (ptrW_of_reload hrel hre hA ha (hsep.gp pa hw.pa_gp) hS0 hk) harr ret hroom hv

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArr
