/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW

/-!
# Segments of the image of a calling body as paths of the decoded program

The image of a calling body of the wide class is simulated by its decoded program segment by
segment, a segment running from the start of the body or from the position after a call to the
next call or to the closing return. The step of the byte simulation is a path of steps of the
machine (`LprogBytesLinkW.linked_stepW`); this module keeps the paths. A segment of the image to
a call is matched by a path of steps from the index of its start to the index of the call, and a
segment to the end by a path to the index of the closing return followed by a halting path
without call. Composed with the steps of the call sites, which relate the image after a call to
every return state of the callee that its interface admits (`ImageAddrCall.ResStep`), these
paths cut the run of the decoded program at its calls.

## Main definitions

* `ByteSegR`: the byte simulation of the steps of a calling body by paths of the decoded
  program.
* `SegExactR`: the simulation of a segment of the image by a path of the decoded program.

## Main results

* `byteSegR_of_linked`: the byte simulation of a relocated body.
* `steps_callImgR`: a run of checked steps of the image is matched by a path.
* `segExactR_callImg`: the simulation of the segments of the image by paths.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsImg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport hiding regName
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (stepA)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (evalInstrPMemFk)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (RunChain SegTo Glue runChain_of_run)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (Steps Halted atPc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
  (RInstr Params ShapeOK Shape)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (remoteSym)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc (RelocShapeOK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (calleeSavedToSave frameSize)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys isRetB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
  (instrOKB condPrevB frameRsp isCondB LoadSafeAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
  (ACorrW widenS widenCell lvm_of_getW instrOKWB carryPrevB castPosB SafeWN WideSafeAt CellSafeAt
    NarrowInv CarryReq narrowIn narrowIn_zero narrowIn_succ narrowStep narrowInv_step classifyK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameIn bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkW
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
  (CalleeRun CalleeSig CalleeSpec HaltsO)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW

/-! ## The byte simulation by paths -/

/-- **The byte simulation of the steps of a calling body of the wide class by paths of the
    decoded program `prog`**, with `pos` the index in `prog` of a position of the body: from a
    safe state, a step of the address machine at the correspondence `ACorrW`, the zero flag
    `CondFlag` and the carry flag `CarryReq` is matched by a path of steps of `prog`, and the
    closing return, at `ACorr`, by a halting path without call. -/
structure ByteSegR (frame : String → Option (BitVec 64)) (rsp : BitVec 64) (body : Lcmd)
    (prog : List RInstr) (pos : Nat → Nat) (tgt : String → Nat)
    (FinA : LstateA → AState → Prop) : Prop where
  /-- A step of the address machine. -/
  step : ∀ sa zf sa' zf' sA, SafeWN rsp body sa →
    stepA frame body sa zf = some (sa', zf') → ACorrW rsp sA sa → CondFlag body sA sa zf →
    CarryReq frame body sa.reg.lpc sA sa →
    ∃ sA', ACorrW rsp sA' sa' ∧ sa'.reg.lpc < body.length ∧ CondFlag body sA' sa' zf'
      ∧ CarryReq frame body sa'.reg.lpc sA' sa'
      ∧ Reaches aMachine prog (pos sa.reg.lpc) sA (pos sa'.reg.lpc) sA'
  /-- The closing return. -/
  halt : ∀ sa sA, sa.reg.lpc + 1 = body.length → ACorr rsp sA sa →
    ∃ sA', HaltsNoCall aMachine prog (pos sa.reg.lpc) sA sA' ∧ FinA sa sA'
  /-- The index of a call. -/
  call : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
    prog[pos p]? = some (.call (tgt t.1))
  /-- The index after a call. -/
  pos_call : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
    pos (p + 1) = pos p + 1

/-- **The byte simulation `ByteSegR` of a relocated body.** For a body with the facts
    `CallFactsW`, a program `prog` that satisfies `LinkedProgMap` at the target map `K`, and
    a frame that agrees with the frame of the body parameters at the names of the body,
    `ByteSegR` holds at the index `DecodePrintedCFG.posOf` and the target map `K`, with the end
    `LprogBytesLinkReloc.FinLea`. -/
theorem byteSegR_of_linked {body : Lcmd} {ds : List X86Backend.PhysAbiShape.DShape}
    (hF : CallFactsW body ds) {K : String → Nat} {prog : List RInstr}
    (hL : X86Backend.LprogBytesLinkReloc.LinkedProgMap body ds K (Params.ofBody body).frame prog)
    (rsp : BitVec 64) {frame : String → Option (BitVec 64)}
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q) :
    ByteSegR frame rsp body prog (X86Backend.DecodePrintedCFG.posOf ds) K
      (X86Backend.LprogBytesLinkReloc.FinLea rsp (Params.ofBody body).frame) := by
  refine ⟨fun sa zf sa' zf' sA hsafe hst hc hz hcy => ?_, fun sa sA hend hc => ?_,
    fun p bi ra t hb hbi => (linked_callW hF hL p bi ra t hb hbi).1,
    fun p bi ra t hb hbi => (linked_callW hF hL p bi ra t hb hbi).2⟩
  · exact linked_stepW hF hL rsp hfr sa zf sa' zf' sA hsafe hst hc hz hcy
  · have e : sa.reg.lpc = body.length - 1 := by omega
    refine ⟨_, ?_, sA, hc, rfl⟩
    rw [e]
    exact ⟨_, .single (X86Backend.DecodedLsemStep.aMachine_step_op prog _ sA _ hL.fin.1), hL.fin.2⟩

/-! ## The run of a segment -/

theorem steps_callImgR {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {prog : List RInstr} {pos : Nat → Nat}
    {tgt : String → Nat} {FinA : LstateA → AState → Prop}
    (hbytes : ByteSegR frame rsp body prog pos tgt FinA)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (site : Nat → String × List String) (fn : String) :
    ∀ (n : Nat) (s u : LstateMF) (sa : LstateA) (zf : Bool) (sA : AState),
      SegStW frame slotArr base rsp body fn s sa zf sA →
      Steps I (singletonProgM fn (callImg slotArr site body)) n s u →
      ∃ sa' zf' sA', SegStW frame slotArr base rsp body fn u sa' zf' sA'
        ∧ (0 < n → sa'.reg.lpc < body.length)
        ∧ Reaches aMachine prog (pos sa.reg.lpc) sA (pos sa'.reg.lpc) sA'
  | 0, s, u, sa, zf, sA, hst, h => by
      have hsu : s = u := Option.some.inj h
      subst hsu
      exact ⟨sa, zf, sA, hst, fun h0 => absurd h0 (Nat.lt_irrefl 0), .refl _ _⟩
  | n + 1, s, u, sa, zf, sA, hst, h => by
      simp only [Steps, Ascent.CutPoint.iter, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, h⟩ := h
      unfold LprogIsa.Isa.lsemStepPMemF at hc
      cases hf : findInstrMem (singletonProgM fn (callImg slotArr site body)) s.prog with
      | none => rw [hf] at hc; cases hc
      | some i =>
        rw [hf] at hc
        dsimp only at hc
        have hck := hI _ _ _ _ hc
        have hrel := hst.rel
        have hz := hrel.zf
        subst hz
        rw [X86Backend.OwnedLprogTV.findInstrMem_single hst.lfn, ← hrel.pc] at hf
        have hlt : sa.reg.lpc < body.length - 1 := by
          have := (List.getElem?_eq_some_iff.mp hf).1
          rwa [callImg_length] at this
        obtain ⟨bi, hb⟩ : ∃ bi, body[sa.reg.lpc]? = some bi :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hnc : ∀ ra tg, bi.li_i ≠ .Lcall ra tg := by
          intro ra tg e
          obtain rfl := callSitesB_call hsites hb hlt e
          obtain ⟨f, l⟩ := tg
          rw [callImg_getElem?_call slotArr site hb (by omega) e] at hf
          obtain rfl := Option.some.inj hf
          have hn := LprogIsaProcs.evalInstrPMemF_shadowCall
            (singletonProgM fn (callImg slotArr site body))
            (LprogIsa.callShadow (site sa.reg.lpc).1 f
              ((site sa.reg.lpc).2.map LOperand.reg), .reg none) s
            (by rw [LprogIsa.shadowCall?_callShadow]; exact Option.some_ne_none _)
          rw [JasminLsemMemChecked.evalInstrPMemF_of_k hck] at hn
          cases hn
        rw [callImg_getElem?_of_ne slotArr site hb (fun f l => hnc none (f, l)),
          virtImg_getElem?, List.getElem?_dropLast, ite_eq_left hlt, hb, Option.map_some] at hf
        obtain rfl := Option.some.inj hf
        have hfn1 : c.prog.lfn = fn :=
          (X86Backend.AllocCheck.LcmdCFG.evalInstrPMemF_next _ _ s c
            (JasminLsemMemChecked.evalInstrPMemF_of_k hck)).1.trans hst.lfn
        obtain ⟨-, hsl, sa1, hst1, hcase⟩ :=
          stepOut_callImgW hsep hphys hgate site fn hrel hst.inv hb hlt hnc hck
        obtain ⟨hw, hcs⟩ := safeAt_of_imgGateCBW (rsp := rsp) hgate hrel hb hlt hnc
        have hn1 : NarrowInv body sa1 := narrowInv_step hst.narrow hst1
        obtain ⟨sA1, hA1, hlen1, hz1, hcy1, hk1⟩ :=
          hbytes.step sa s.zf sa1 c.zf sA ⟨hsl, hw, hcs, hst.narrow⟩ hst1 hst.corr hst.cond
            hst.carry
        rcases hcase with ⟨hrel1, hinv1⟩ | ⟨⟨bp, ii, l, hbp, hlb⟩, -, hsl1, sa2, hst2, hrel2, hinv2⟩
        · obtain ⟨sa', zf', sA', hst', hlen', hk⟩ :=
            steps_callImgR hsep hphys hgate hsites hbytes hI site fn n c u sa1 c.zf sA1
              ⟨hfn1, hrel1, hinv1, hA1, hz1, hcy1, hn1⟩ h
          refine ⟨sa', zf', sA', hst', fun _ => ?_, hk1.trans hk⟩
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · have hcu : c = u := Option.some.inj h
            subst hcu
            rw [hst'.rel.pc, ← hrel1.pc]
            exact hlen1
          · exact hlen' hn
        · obtain ⟨hw1, hcs1⟩ := safeAt_label (rsp := rsp) hbp hlb
          obtain ⟨sA2, hA2, hlen2, hz2, hcy2, hk2⟩ :=
            hbytes.step sa1 c.zf sa2 c.zf sA1 ⟨hsl1, hw1, hcs1, hn1⟩ hst2 hA1 hz1 hcy1
          obtain ⟨sa', zf', sA', hst', hlen', hk⟩ :=
            steps_callImgR hsep hphys hgate hsites hbytes hI site fn n c u sa2 c.zf sA2
              ⟨hfn1, hrel2, hinv2, hA2, hz2, hcy2, narrowInv_step hn1 hst2⟩ h
          refine ⟨sa', zf', sA', hst', fun _ => ?_, (hk1.trans hk2).trans hk⟩
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · have hcu : c = u := Option.some.inj h
            subst hcu
            rw [hst'.rel.pc, ← hrel2.pc]
            exact hlen2
          · exact hlen' hn

/-! ## The simulation of a segment -/

structure SegExactR (frame : String → Option (BitVec 64))
    (slotArr : String → Option (String × Nat)) (base : String → BitVec 64) (rsp : BitVec 64)
    (body : Lcmd) (fn : String) (L : Nat → Bool) (prog : List RInstr) (pos : Nat → Nat) (tgt : String → Nat)
    (Seg : LstateMF → Option Nat → LstateMF → Prop) : Prop where
  /-- A segment to a call. -/
  toCall : ∀ s sa zf sA p u, s.prog.lfn = fn → sa.reg.lpc < body.length →
    L sa.reg.lpc = false →
    ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa → Seg s (some p) u →
    ∃ sa' zf' sA', ImgRelW frame slotArr base body u sa' zf' ∧ ACorrW rsp sA' sa'
      ∧ (∃ bi ra t, body[p]? = some bi ∧ bi.li_i = .Lcall ra t
          ∧ prog[pos p]? = some (.call (tgt t.1)))
      ∧ Reaches aMachine prog (pos sa.reg.lpc) sA (pos p) sA'
  /-- A segment to an end state. -/
  toEnd : ∀ s sa zf sA t, s.prog.lfn = fn → sa.reg.lpc < body.length →
    L sa.reg.lpc = false →
    ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa → Seg s none t →
    ∃ sa' zf' sA', ImgRelW frame slotArr base body t sa' zf' ∧ ACorrW rsp sA' sa'
      ∧ sa'.reg.lpc + 1 = body.length
      ∧ Reaches aMachine prog (pos sa.reg.lpc) sA (pos sa'.reg.lpc) sA'
  /-- The index after a call. -/
  pos_call : ∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
    pos (p + 1) = pos p + 1

theorem segExactR_callImg {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {D : DeadTab} (hcond : condLiveB D body = true)
    {prog : List RInstr} {pos : Nat → Nat}
    {tgt : String → Nat} {FinA : LstateA → AState → Prop}
    (hbytes : ByteSegR frame rsp body prog pos tgt FinA)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (site : Nat → String × List String) (T : LprogIsa.ProcTable) (fn : String) :
    SegExactR frame slotArr base rsp body fn (liveW D slotArr body) prog pos tgt
      (SegTo I T (singletonProgM fn (callImg slotArr site body))) := by
  refine ⟨fun s sa zf sA p u hfn hlen hL hrel hA hseg => ?_,
    fun s sa zf sA t hfn hlen hL hrel hA hseg => ?_, hbytes.pos_call⟩
  · obtain ⟨n, hn, hat, i, hi, hproc⟩ := hseg
    obtain ⟨sa', zf', sA', hst', -, hk⟩ :=
      steps_callImgR hsep hphys hgate hsites hbytes hI site fn n s u sa zf sA
        (segStW_start hcond hfn hL hrel hA) hn
    have hrel' := hst'.rel
    have hpc : sa'.reg.lpc = p := hrel'.pc.trans hat.2
    have hi' : (callImg slotArr site body)[p]? = some i := hi
    have hp : p < body.length - 1 := by
      have := (List.getElem?_eq_some_iff.mp hi').1
      rwa [callImg_length] at this
    obtain ⟨bi, hb⟩ : ∃ bi, body[p]? = some bi := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hcallp : ∃ ra t, bi.li_i = .Lcall ra t := by
      by_contra hne
      have hnc : ∀ ra t, bi.li_i ≠ .Lcall ra t := fun ra t e => hne ⟨ra, t, e⟩
      rw [callImg_getElem?_of_ne slotArr site hb (fun f l => hnc none (f, l)),
        virtImg_getElem?, List.getElem?_dropLast, ite_eq_left hp, hb, Option.map_some] at hi'
      obtain rfl := Option.some.inj hi'
      have hsh := callSitesB_other hsites hb hp hnc
      simp [LprogCallCut.isProcB, LprogIsa.procCall?, hsh] at hproc
    obtain ⟨ra, t, hbi⟩ := hcallp
    subst hpc
    exact ⟨sa', zf', sA', hrel', hst'.corr, ⟨bi, ra, t, hb, hbi, hbytes.call _ bi ra t hb hbi⟩, hk⟩
  · obtain ⟨n, hn, hhalt⟩ := hseg
    obtain ⟨sa', zf', sA', hst', hlen', hk⟩ :=
      steps_callImgR hsep hphys hgate hsites hbytes hI site fn n s t sa zf sA
        (segStW_start hcond hfn hL hrel hA) hn
    have hrel' := hst'.rel
    have hlenE : sa'.reg.lpc < body.length := by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · have hst : s = t := Option.some.inj hn
        subst hst
        rw [hrel'.pc, ← hrel.pc]
        exact hlen
      · exact hlen' hn0
    have hend : sa'.reg.lpc + 1 = body.length := by
      have hh : findInstrMem (singletonProgM fn (callImg slotArr site body)) t.prog
          = none := hhalt
      rw [X86Backend.OwnedLprogTV.findInstrMem_single hst'.lfn, List.getElem?_eq_none_iff, callImg_length,
        ← hrel'.pc] at hh
      omega
    exact ⟨sa', zf', sA', hrel', hst'.corr, hend, hk⟩


end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsImg
