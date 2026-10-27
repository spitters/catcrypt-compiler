/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArr

@[expose] public section

set_option autoImplicit false

/-!
# The image call step with a word-array result written by the callee

`ImageAddrCallArr.call_reestablishes_arr` is the step of the image relation across a call
whose callee reads one array of the caller. This module states the step for a callee that
writes a word array of the caller: the pointer register `po` holds the base of the array `A`
of length `n`, the footprint of the callee is its frame together with the `n` words at that
pointer (`FootBelowOut`), and the postcondition gives the words written there as the array of
the summary (`ProcSummary.runOut`). After the call the image state holds that array in the
carrier of `A` (`LprogIsa.retArr`). The frame words and the words of the other arrays stay
outside the footprint (`FootClearExcept`), which follows from `CallerSep` and `ImgSep`.

## Main definitions

* `FootBelowOut`: the footprint of the callee is among the `G` bytes below its entry stack
  register and the `n` words at the pointer register.
* `FootClearExcept`: the frame words and the words of the arrays other than `A` lie outside
  a set of addresses.
* `outState`: the image state with an array in the carrier of `A`.
* `OutCallee`: the reading of an interface as a summary whose result is the array the callee
  writes at the pointer register.

## Main results

* `footBelowOut_of_footBelow`: a footprint among the frame bytes is a footprint of
  `FootBelowOut`.
* `footClearExcept_of_callerSep`: under `CallerSep` and `ImgSep`, with the pointer register
  holding the base of `A`, the frame words and the other arrays are clear of the footprint
  and the return word.
* `imgRel_callC_out`: the image relation across the summary step of a call that writes `A`.
* `agreeOffF_retArr`: the step of the summary with the array result agrees with the summary
  step of the call off the exempted names and the flags.
* `call_reestablishes_out`: after every run of the callee, the words at the base of `A` are
  the array of the summary and the relaxed relation holds at `LprogIsa.retArr`.
* `call_reestablishes_out_reload`: the same, with the pointer register reloaded from the
  saved frame word of the array.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallOut

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
  (gpOk gpFacts phys evalInstrA_leaFrame mem_gpList)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr redW read64_eq_of_agree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe
  (retWord entryOf entryOf_regs entryOf_mem outOf memAfter retOps_eq CallOut read64_congr_range
    reloadOf_call)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSig CalleeSpec InFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArr (ptrW_of_reload)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

/-! ## 1. The footprint of a callee that writes an array -/

/-- The footprint of the callee is among the `G` bytes below its entry stack register and
    the `n` words at the address in the register of the pointer name `po`. -/
def FootBelowOut (c : CalleeSig) (G : Nat) (po : String) (n : Nat) : Prop :=
  ∀ s x, c.foot s x →
    InFrame (s.regs "%rsp") G x ∨ ∃ j < n, InRange8 (cellAt (s.regs (phys po)) j) x

/-- A footprint among the `G` bytes below the entry stack register is a footprint of
    `FootBelowOut`. -/
theorem footBelowOut_of_footBelow {c : CalleeSig} {G : Nat} (hF : FootBelow c G) (po : String)
    (n : Nat) : FootBelowOut c G po n :=
  fun s x h => Or.inl (hF s x h)

/-- The frame words of the names that are no frame-array names (`faB`) and the words of every
    array other than `A` lie outside the set `T` of addresses. -/
def FootClearExcept (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) (A : String)
    (T : BitVec 64 → Prop) : Prop :=
  (∀ q a, frame q = some a → faB q = false → ∀ x, InRange8 a x → ¬ T x)
    ∧ ∀ q A' n j, slotArr q = some (A', n) → A' ≠ A → j < n →
        ∀ x, InRange8 (cellAt (base A') j) x → ¬ T x

/-- **The footprint and the return word are clear of the caller off the written array.**
    Under `ImgSep` and `CallerSep` at the stack register of the byte state, for a callee of
    `FootBelowOut` whose pointer register holds the base of the array `A` of a frame slot,
    the frame words and the words of the arrays other than `A` lie outside the footprint and
    the return word. -/
theorem footClearExcept_of_callerSep {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    (hsep : ImgSep frame slotArr base rsp) {G : Nat} (hS : CallerSep frame slotArr base rsp G)
    {c : CalleeSig} {po : String} {n : Nat} (hF : FootBelowOut c G po n) (hpo : gpOk po = true)
    {sA : AState} (hsp : sA.regs "%rsp" = rsp) {qA A : String} (hqA : slotArr qA = some (A, n))
    (hptr : sA.regs (phys po) = base A) (ret : Nat) :
    FootClearExcept frame slotArr base A
      fun x => c.foot (entryOf ret sA) x ∨ InRange8 (retWord sA) x := by
  have hdis : ∀ {a w x : BitVec 64}, Disjoint8 a w → InRange8 w x → ¬ InRange8 a x := by
    intro a w x hd hx ha
    obtain ⟨h1, h2⟩ := hd
    unfold InRange8 at hx ha
    simp only [BitVec.toNat_sub] at h1 h2 hx ha
    have := a.isLt
    have := w.isLt
    have := x.isLt
    omega
  have he : (entryOf ret sA).regs "%rsp" = rsp + BitVec.ofInt 64 (-8) := by
    rw [entryOf_regs, ite_eq_left rfl, retWord, hsp]
  have hp : (entryOf ret sA).regs (phys po) = base A := by
    rw [entryOf_regs, ite_eq_right (gpFacts hpo).physNe, hptr]
  have hr : retWord sA = rsp + BitVec.ofInt 64 (-8) := by rw [retWord, hsp]
  refine ⟨fun q a ha hf x hx hT => ?_, fun q A' n' j hq hA' hj x hx hT => ?_⟩
  · obtain ⟨o, h1, rfl⟩ := hS.frames q a ha
    rcases hT with hT | hT
    · rcases hF _ x hT with hT | ⟨i, hi, hT⟩
      · exact above_not_inFrame rsp x o G h1 hx (he ▸ hT)
      · rw [hp] at hT
        exact hdis (hsep.cellFrame qA A n i hqA hi q _ ha hf) hx hT
    · exact above_not_retWord rsp x o (by omega) hx (hr ▸ hT)
  · obtain ⟨n1, n2⟩ := hS.cells q A' n' j hq hj x hx
    rcases hT with hT | hT
    · rcases hF _ x hT with hT | ⟨i, hi, hT⟩
      · exact n2 (he ▸ hT)
      · rw [hp] at hT
        exact hdis (hsep.cells qA A n q A' n' i j hqA hq hi hj (Or.inl (Ne.symm hA'))) hx hT
    · exact n1 (hr ▸ hT)

/-! ## 2. The image relation across a call that writes an array -/

/-- The image state `s` with the array `arr` in the carrier of `A`. -/
def outState (A : String) {n : Nat} (arr : Fin n → BitVec 64) (s : LstateMF) : LstateMF :=
  { s with prog := { s.prog with base := s.prog.base.setArr A arr } }

/-- **The image relation across the summary step of a call that writes the array `A`.** Let
    the instruction at the program counter be a call in a body of the class `physImgB`, and
    `A` be the array of a frame slot with length `n`. If the memory `m` after the call holds
    the bytes of every frame word and of every word of an array other than `A` of the memory
    before it, and the words of `m` at the base of `A` are `arr`, the relation holds between
    the summary step from the image state with `arr` in the carrier of `A` and `callAC c ω m sa`. -/
theorem imgRel_callC_out {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (c : CalleeSig) (ω : CallOut) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {ra : Option String} {tgt : String × LLabel}
    (hbi : bi.li_i = .Lcall ra tgt) {m : AMem}
    (hfr : ∀ q a, frame q = some a → faB q = false → ∀ x, InRange8 a x → m x = sa.mem x)
    {qA A : String} {n : Nat} (hqA : slotArr qA = some (A, n))
    (hce : ∀ q A' n' j, slotArr q = some (A', n') → A' ≠ A → j < n' →
      ∀ x, InRange8 (cellAt (base A') j) x → m x = sa.mem x)
    {arr : Fin n → BitVec 64} (harr : ∀ j (hj : j < n), read64 m (cellAt (base A) j) = arr ⟨j, hj⟩) :
    ImgRel frame slotArr base body (callSumC c ω (outState A arr s)) (callAC c ω m sa) ω.zf := by
  have hlvm : ∀ r, gpOk r = false → ∀ R : LstateN, (callRegsC c ω R).lvm r = R.lvm r := by
    intro r hr R
    simp [callRegsC, clobN, hr]
  refine ⟨congrArg (· + 1) hrel.pc, fun r hr => ?_, fun q a ha => ?_, rfl, rfl, rfl,
    fun r hr => ?_, fun q A' n' hq => ?_, fun k R A' n' a hS hA ha => ⟨fun hk => ?_, fun hk => ?_⟩,
    fun b q a A' n' hr => ?_, fun R A' n' a hR hA ha => by
      show read64 m a = base A'
      rw [read64_congr_range (hfr _ a ha (faB_slotOfReg R))]
      exact hrel.held R A' n' a hR hA ha⟩
  · show (callRegsC c ω s.prog.base.reg).lvm r = (callRegsC c ω sa.reg).lvm r
    simp only [callRegsC, hrel.regs r hr]
  · have hq : gpOk q = false := by
      cases hg : gpOk q
      · rfl
      · rw [hsep.gp q hg] at ha; cases ha
    show (callRegsC c ω s.prog.base.reg).lvm q = ⟨64, frameVal m q a⟩
    rw [hlvm q hq, hrel.slots q a ha,
      frameVal_congr fun hf => read64_congr_range (hfr q a ha hf)]
  · show ((callRegsC c ω sa.reg).lvm r).1 = 64
    simp only [callRegsC]
    split_ifs
    · rfl
    · exact hrel.wid r hr
  · show ∃ arr', (s.prog.base.setArr A arr).getArr A' 64 n' = some arr' ∧
      ∀ j (hj : j < n'), read64 m (cellAt (base A') j) = arr' ⟨j, hj⟩
    by_cases hA' : A' = A
    · subst hA'
      obtain rfl := hsep.len qA q A' n n' hqA hq
      refine ⟨arr, ?_, harr⟩
      have hl : (s.prog.base.setArr A' arr).larr A' = ⟨64, n, arr⟩ := ite_eq_left rfl
      unfold LstateM.getArr
      rw [hl]
      simp
    · obtain ⟨arr', h1, h2⟩ := hrel.cells q A' n' hq
      have hl : (s.prog.base.setArr A arr).larr A' = s.prog.base.larr A' := ite_eq_right hA'
      refine ⟨arr', ?_, fun j hj => ?_⟩
      · rw [← h1]
        unfold LstateM.getArr
        rw [hl]
      · rw [read64_congr_range (hce q A' n' j hq hA' hj)]; exact h2 j hj
  · have hk' : k < sa.reg.lpc := by
      have hk0 : k < sa.reg.lpc + 1 := hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk0 with h | rfl
      · exact h
      · obtain ⟨i, hi, hm⟩ := hS
        rw [hb] at hi
        cases hi
        rw [hbi] at hm
        cases hm
    show read64 m a = base A'
    rw [read64_congr_range (hfr _ a ha (faB_slotOfReg R))]
    exact (hrel.saved k R A' n' a hS hA ha).1 hk'
  · have hk0 : sa.reg.lpc + 1 ≤ k := hk
    exact absurd (show sa.reg.lpc < k by omega) (not_saveAt_after_call hphys hb hbi hS hA)
  · have e : reloadOf slotArr body (sa.reg.lpc + 1) b = some q := hr
    rw [reloadOf_call hb hbi] at e
    cases e

/-- The step of a procedure summary with the array result `arr` at `A` agrees with the
    summary step of the call from `outState A arr s` off the exempted names and the flags,
    for an interface without a result register. -/
theorem agreeOffF_retArr (c : CalleeSig) (ω : CallOut) (s : LstateMF) (A : String) {n : Nat}
    (arr : Fin n → BitVec 64) (hres : c.res = none) :
    AgreeOffF (exemptC c) (LprogIsa.retArr A arr s) (callSumC c ω (outState A arr s)) := by
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  show s.prog.base.reg.nextPc.lvm r
    = (if clobN c r then ⟨64, ω.reg r⟩ else s.prog.base.reg.lvm r)
  split_ifs with h2
  · exfalso
    apply hr
    simp only [clobN, Bool.and_eq_true] at h2
    simp only [exemptC, List.mem_filter, Bool.and_eq_true, bne_iff_ne, hres]
    exact ⟨mem_gpList h2.1, h2.2, nofun⟩
  · rfl

/-! ## 3. The reading of an interface with an array result -/

/-- **The reading of an interface as a procedure summary whose result is an array the callee
    writes.** The summary input at an entry state is `rd`; the pointer name `po` is a
    general-purpose name; the interface has no result register; the summary has a
    word-array result of length `n`; the precondition holds at an entry state that satisfies
    `room` and at whose summary input the array result is defined; and the postcondition
    gives the `n` words of the return state at the pointer of the entry state as the array of
    the summary. -/
structure OutCallee (c : CalleeSig) (rd : AState → List (BitVec 64)) (po : String) (n : Nat)
    (pr : LprogIsa.ProcSummary) (room : AState → Prop) : Prop where
  /-- The pointer name is a general-purpose name. -/
  po_gp : gpOk po = true
  /-- The interface has no result register. -/
  res_none : c.res = none
  /-- The summary has a word-array result of length `n`. -/
  len : pr.out = some n
  /-- The precondition, from `room` and a defined array result. -/
  pre : ∀ s, room s → (pr.runOut n (rd s)).isSome = true → c.pre s
  /-- The words at the pointer at the return are the array of the summary. -/
  post : ∀ s s', c.pre s → c.post s s' →
    pr.runOut n (rd s) = some fun j : Fin n => read64 s'.mem (cellAt (s.regs (phys po)) j.val)

/-! ## 4. The call step -/

/-- **A call that writes an array re-establishes the relaxed relation.** Let `ImgRel` and
    `ACorr` hold at a call instruction of a body of the class `physImgB`, the callee meet its
    specification and have the reading `pr` whose array result is written at the pointer
    `po`, the caller be separated (`CallerSep`) for a callee whose footprint is among the `G`
    bytes below its entry stack register and the `n` words at the pointer, the pointer name
    hold the base of the array `A` of a frame slot, the summary input of the entry state be
    `vs`, the entry state satisfy `room`, and the summary give the array `arr` at `vs`. Then
    the entry state satisfies the precondition, and for every run of the callee, after the
    return: the words at the base of `A` are `arr`, and there is an address state at the next
    position that corresponds to the byte state and is related, up to the names `exemptC c`
    and the flags, to the image state with `arr` in the carrier of `A` (`LprogIsa.retArr`). -/
theorem call_reestablishes_out {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {rd : AState → List (BitVec 64)}
    {po : String} {n : Nat} {pr : LprogIsa.ProcSummary} {room : AState → Prop}
    (hw : OutCallee c rd po n pr room) {G : Nat} (hS : CallerSep frame slotArr base rsp G)
    (hF : FootBelowOut c G po n) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {sA : AState} (hc : ACorr rsp sA sa)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {ra : Option String}
    {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt)
    {q A : String} (hq : slotArr q = some (A, n)) (hptr : sa.reg.getW po 64 = some (base A))
    (ret : Nat) {vs : List (BitVec 64)} (hrd : rd (entryOf ret sA) = vs)
    (hroom : room (entryOf ret sA)) {arr : Fin n → BitVec 64} (hv : pr.runOut n vs = some arr) :
    c.pre (entryOf ret sA) ∧ ∀ t sc, X (entryOf ret sA) t sc →
      (∀ j (hj : j < n),
          read64 (retOps.foldl aMachine.exec sc).mem (cellAt (base A) j) = arr ⟨j, hj⟩)
        ∧ ∃ sa', sa'.reg.lpc = sa.reg.lpc + 1
          ∧ ACorr rsp (retOps.foldl aMachine.exec sc) sa'
          ∧ ImgRelF frame slotArr base body (exemptC c) (LprogIsa.retArr A arr s) sa' := by
  have hpo : sA.regs (phys po) = base A :=
    Option.some.inj ((hc.regs po hw.po_gp).symm.trans hptr)
  have hpre : c.pre (entryOf ret sA) := hw.pre _ hroom (by rw [hrd, hv]; rfl)
  refine ⟨hpre, fun t sc hrun => ?_⟩
  obtain ⟨hsp, -, hk, hm, hpost⟩ := call_return hX ret sA hpre hrun
  have hmR : (retOps.foldl aMachine.exec sc).mem = sc.mem := by
    rw [retOps_eq, (evalInstrA_leaFrame sc 8).2]
  have hwr : ∀ j (hj : j < n),
      read64 (retOps.foldl aMachine.exec sc).mem (cellAt (base A) j) = arr ⟨j, hj⟩ := by
    intro j hj
    have h1 := hw.post _ _ hpre hpost
    rw [hrd, hv, entryOf_regs, ite_eq_right (gpFacts hw.po_gp).physNe, hpo] at h1
    rw [hmR, Option.some.inj h1]
  have hfoot := footClearExcept_of_callerSep hsep hS hF hw.po_gp hc.sp hq hpo ret
  have hmem : ∀ x, ¬ (c.foot (entryOf ret sA) x ∨ InRange8 (retWord sA) x) →
      memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem x = sa.mem x := by
    intro x hx
    unfold memAfter
    split_ifs with hred
    · rfl
    · rw [hm x (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h))]
      exact (hc.mem x hred).symm
  have harr : ∀ j (hj : j < n),
      read64 (memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem) (cellAt (base A) j)
        = arr ⟨j, hj⟩ := by
    intro j hj
    rw [read64_eq_of_agree (m' := (retOps.foldl aMachine.exec sc).mem)
      (fun x hx => by simp [memAfter, hx]) (hsep.red q A n j hq hj)]
    exact hwr j hj
  let ω : CallOut := ⟨fun _ => 0, false, false, false⟩
  exact ⟨hwr, _, rfl, acorr_callC c ω hc hsp fun r hg hcl => hk _ (gpFacts hg).physNe hcl,
    _, _, agreeOffF_retArr c (outOf _ ω) s A arr hw.res_none,
    imgRel_callC_out hsep hphys c (outOf _ ω) hrel hb hbi
      (fun q a ha hf x hx => hmem x (hfoot.1 q a ha hf x hx)) hq
      (fun q A' n' j hq' hA' hj x hx => hmem x (hfoot.2 q A' n' j hq' hA' hj x hx)) harr⟩

/-- **The call step with the pointer reloaded from its saved frame word.** As
    `call_reestablishes_out`, where the pointer name `po` is the reload, at the position of
    the call, of the frame slot of the saved register `R`, which is the slot of the array
    `A`, and the save of `R` is before the call. -/
theorem call_reestablishes_out_reload {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c) {rd : AState → List (BitVec 64)}
    {po : String} {n : Nat} {pr : LprogIsa.ProcSummary} {room : AState → Prop}
    (hw : OutCallee c rd po n pr room) {G : Nat} (hS : CallerSep frame slotArr base rsp G)
    (hF : FootBelowOut c G po n) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {sA : AState} (hc : ACorr rsp sA sa)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {ra : Option String}
    {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt)
    {R A : String} {k : Nat} {a : BitVec 64}
    (hre : reloadOf slotArr body sa.reg.lpc po = some (slotOfReg R))
    (hA : slotArr (slotOfReg R) = some (A, n)) (ha : frame (slotOfReg R) = some a)
    (hS0 : SaveAt body k R) (hk : k < sa.reg.lpc)
    (ret : Nat) {vs : List (BitVec 64)} (hrd : rd (entryOf ret sA) = vs)
    (hroom : room (entryOf ret sA)) {arr : Fin n → BitVec 64} (hv : pr.runOut n vs = some arr) :
    c.pre (entryOf ret sA) ∧ ∀ t sc, X (entryOf ret sA) t sc →
      (∀ j (hj : j < n),
          read64 (retOps.foldl aMachine.exec sc).mem (cellAt (base A) j) = arr ⟨j, hj⟩)
        ∧ ∃ sa', sa'.reg.lpc = sa.reg.lpc + 1
          ∧ ACorr rsp (retOps.foldl aMachine.exec sc) sa'
          ∧ ImgRelF frame slotArr base body (exemptC c) (LprogIsa.retArr A arr s) sa' :=
  call_reestablishes_out hsep hphys hX hw hS hF hrel hc hb hbi hA
    (ptrW_of_reload hrel hre hA ha (hsep.gp po hw.po_gp) hS0 hk) ret hrd hroom hv

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallOut
