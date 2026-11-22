/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall

/-!
# The memory and the stack register through linked calls

A halting run through calls of the bytes of the compiler on a program with calls of linked
kernels restores the stack register and changes the memory only in the stack words
`%rsp + o`, `frameLo ≤ o ≤ frameHi`, and in the words of the pointer regions of the layout.

A step of the calling body stores in a frame word or in an array word of the image simulation
(`ImageAddrStore.imgStores`). A linked call changes the return word and the footprint of the
interface of the callee, which is among the bytes of its frame below the return word and, at
an out result, the words of the destination array (`footBelow_contractSig`,
`footBelowOut_contractSig`). The check `CalleeStackRoom.stackRoomB` of the gate places the
return word and the frames of the callees in the stack words of the layout, so the stack area
of the calls adds no byte to the set `layoutMem σ sa`.

## Main results

* `storeIn_callImgW`, `steps_callImgW_keep`: the stores of one step of the image of a calling
  body, and the memory kept through the steps of a segment.
* `haltsO_call_keep`, `haltsO_of_runChain_keep`: the memory kept through a call, and through a
  chain of segments and calls, with the stack register at the return.
* `ok_foot_mem`, `callStack_mem_layoutMem`: the footprint of a callee at a call site, by its
  kind, and the stack area of the calls in the stack words of the layout.
* `regionBack_linked_keep`: the halting run of the linked bytes of a calling body restores
  the stack register and keeps the memory outside `layoutMem σ sa`.
* `NFEntry.linked_keep`, `NFEntry.halts_keep`, `haxc_halts_keep`: the same for every halting
  run of the bytes of an entry and of `compileA`.
* `haxc_correct_auto_keep`: the halting runs and the read-back of `haxc_correct_auto`, with
  both facts at the state that reads back the result, also through the linked calls.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.LinkKeep

/-! ## 1. The image simulation -/

section Image

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
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (RunChain Glue)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (Steps Halted atPc)
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc (FinLea)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
  (gpOk phys gpFacts evalInstrA_leaFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr redW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
  (ACorrW widenS NarrowInv narrowInv_step)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind CallAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrStore (imgStores)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe
  (retWord entryOf entryOf_regs entryOf_mem retOps_eq)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
  (CalleeRun CalleeSig CalleeSpec HaltsO InFrame)
open CatCrypt.Crypto.SecureCompilation.SepLogic.Addr (StoreIn)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState InRange8)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

variable {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
  {base : String → BitVec 64} {rsp : BitVec 64} {body : Lcmd}

/-- An instruction that passes `gateAtW` is no cell store. -/
theorem cellSt_of_gateAtW {k : Nat} {W : List String} {x : LinstrR}
    (hg : gateAtW frame slotArr body k W x = true) (B : String) (off : Nat) (S : String) :
    cellA? x ≠ some (.st B off S) := by
  intro hc
  obtain ⟨d, o, n, rfl⟩ : ∃ d o n, x = .Lopn [.reg d] o [.reg n] := by
    unfold cellA? at hc
    split at hc
    · exact ⟨_, _, _, rfl⟩
    · cases hc
  obtain ⟨hu, hd⟩ : (LprogAsmPrinter.untagCaret o = "STORE:64"
      ∨ LprogAsmPrinter.untagCaret o = "MOV:64") ∧ (cellParts? d).isSome = true := by
    simp only [cellA?] at hc
    grind [Option.map_eq_some_iff]
  have hs : slotMov? (.Lopn [.reg d] o [.reg n]) = none := by
    by_cases ho : o = "MOVQ"
    · subst ho
      simp_all
    by_cases ho2 : o = "MOV:64"
    · simp [slotMov?, ho2, hd]
    · simp [slotMov?, ho, ho2]
  have hic : icase frame (.Lopn [.reg d] o [.reg n]) = .reg := by
    unfold icase
    rcases hu with hu | hu <;>
      simp (config := { decide := true }) [hu, hs, JasminLsemAddrRun.normA, slotCmp?,
        JasminLsemAddrRun.castTagW]
  simp only [gateAtW, carryI?, hic, Bool.and_eq_true] at hg
  have h2 := hg.2
  have hnorm : cellA? (JasminLsemAddrRun.normA (.Lopn [.reg d] o [.reg n]))
      = some (.st B off S) := by
    rw [← hc, ← cellA?_untagCaret]
    rcases hu with hu | hu <;>
      simp (config := { decide := true }) [JasminLsemAddrRun.normA, hu]
  simp [JasminLsemCast.movImmStruct?, bitStore?, sImmB, sCmovB, regGateBW, regOkB, hnorm,
    copyInB_of_slotMov_none (frame := frame) (body := body) (W := W) hs] at h2

/-- **The stores of one step of the image of a calling body, off the calls**, lie in the
    frame words and the array words `imgStores`. -/
theorem storeIn_callImgW (hsep : ImgSep frame slotArr base rsp)
    (hgate : imgGateCBW frame slotArr body = true) (P : LprogM) {s t : LstateMF} {sa : LstateA}
    {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf)
    (hinv : CidxInv slotArr base body s) {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi)
    (hlt : sa.reg.lpc < body.length - 1) (hnc : ∀ ra tg, bi.li_i ≠ .Lcall ra tg)
    (hstep : evalInstrPMemFk true P (imgInstr slotArr body sa.reg.lpc bi.li_i) s = some t) :
    StoreIn (imgStores frame slotArr base) frame body sa := by
  have hG := imgGateW_of_imgGateCBW hgate
  by_cases hX : exemptCW frame slotArr body sa.reg.lpc
  · simp only [exemptCW, hb, Option.any_some, Bool.or_eq_true] at hX
    rcases hX with hr | harm
    · cases hx : bi.li_i with
      | Lcall ra t => exact absurd hx (hnc ra t)
      | _ => rw [hx] at hr; simp [remoteCallB] at hr
    -- An indexed store through a cell writes a word of the array of the access.
    simp only [cidxArmCW, Bool.and_eq_true] at harm
    obtain ⟨A, n, idx, v, -, -, hst, -⟩ := cidxArmB_spec harm.1
    have he := hstep
    rw [imgInstr_cellIdxStore slotArr hst] at he
    obtain ⟨c, D, w, hx, hcp, hw, -, hD⟩ := cidxStore_addr P hrel hinv hb harm.1 hst he
    have hcl : cellA? bi.li_i = some (.st D 0 v) := by
      rw [hx]
      simp [cellA?, hcp, LprogAsmPrinter.untagCaret_of_caret_free
        (by decide : '^' ∉ "MOV:64".toList)]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hac, _⟩ :=
      cellIdxStore?_spec hst
    obtain ⟨q, -, hq, -⟩ := ImageAddrSim.accArr_spec hac
    refine (ImageAddrStore.accessIn_of_cases hb ImageAddrStore.frame_mem_imgStores
      (fun b i sc p vi h => ?_) (fun b off p h hp => ?_) (fun b m z p h => ?_)
      (fun d b u j p h => ?_)).1
    · rcases h with ⟨_, _, _, -, h⟩ | ⟨_, _, -, h⟩ <;> rw [hx] at h <;> simp at h
    · rcases h with ⟨u, h⟩ | ⟨u, h⟩ <;> rw [hcl] at h <;> cases h
      rw [hD] at hp
      cases hp
      simpa [cellAt] using
        ImageAddrStore.cell_mem_imgStores (frame := frame) (base := base) hq hw
    · obtain ⟨_, -, h⟩ := h
      rw [hx] at h
      simp at h
    · obtain ⟨_, -, h⟩ := h
      rw [hx] at h
      simp at h
  · have hg := hG.instr _ _ hb (by omega) hX
    refine (ImageAddrStore.accessIn_of_cases hb ImageAddrStore.frame_mem_imgStores
      (fun b i sc p vi h hp hv => ?_) (fun b off p h _ => ?_) (fun b m z p h hp => ?_)
      (fun d b u j p h hp => ?_)).1
    · exact ImageAddrStore.idx_mem_of_imgStepWG hsep hG P hrel hb hlt hX hstep h hp hv
    · rcases h with ⟨u, h⟩ | ⟨u, h⟩
      · exact absurd h (cellSt_of_gateAtW hg b off u)
      · exact absurd h (cellLd_of_gateAtW hg u b off)
    · exact ImageAddrStore.zarr_mem_of_imgStepWG hsep hG hrel hb hlt hX h hp
    · exact ImageAddrStore.simm_mem_of_imgStepWG hsep hG hrel hb hlt hX h hp

/-- **A step that stores in `M` keeps the bytes of the machine outside `M`**, when `M` holds
    the red-zone word, at which the machine and the address state may differ. -/
theorem keep_of_stepA {M : Set (BitVec 64)} (hred : ∀ x, InRange8 (redW rsp) x → x ∈ M)
    {M' : Set (BitVec 64)} (hM : M' ⊆ M) {sa sa1 : LstateA} {zf z1 : Bool}
    (hsto : StoreIn M' frame body sa) (hst : stepA frame body sa zf = some (sa1, z1))
    {sA sA1 : AState} (hA : ACorrW rsp sA sa) (hA1 : ACorrW rsp sA1 sa1) :
    ∀ x, x ∉ M → sA1.mem x = sA.mem x := fun x hx => by
  have h : sa.mem x = sa1.mem x :=
    SepLogic.Addr.stepA_writesIn frame body hst (SepLogic.Addr.Loc.mem x)
      fun hw => hx (hM (hsto x hw))
  exact (hA1.mem x fun hr => hx (hred x hr)).symm.trans
    (h.symm.trans (hA.mem x fun hr => hx (hred x hr)))

/-- **A linked call keeps the bytes outside `M`**, when `M` holds the return word and the
    footprint of the interface of the callee at the entry of the call, with the call step of
    `ImageAddrCall.haltsO_call_imageS`. -/
theorem haltsO_call_keep {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {E E' : List String} {u v : LstateMF} {sa : LstateA}
    (hI : ImgRelF frame slotArr base body E u sa)
    (hst : SiteStep frame slotArr base rsp body X c E E' u v)
    {sA : AState} (hc : ACorr rsp sA sa)
    (hcall' : ∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t)
    {prog : List RInstr} {pc tgt : Nat} (hcall : prog[pc]? = some (.call tgt))
    {O : Nat → AState → AState → Prop} (hO : ∀ s tr s', X s tr s' → O tgt s s')
    {M : Set (BitVec 64)} (hret : ∀ x, InRange8 (retWord sA) x → x ∈ M)
    (hfoot : ∀ u' zf, ImgRel frame slotArr base body u' sa zf → ∀ ret x,
      c.foot (entryOf ret sA) x → x ∈ M) :
    ∃ sA' sa', sa'.reg.lpc = sa.reg.lpc + 1 ∧ ACorr rsp sA' sa'
      ∧ ImgRelF frame slotArr base body E' v sa'
      ∧ (∀ x, x ∉ M → sA'.mem x = sA.mem x)
      ∧ ∀ s'', HaltsO aMachine O prog (pc + 1) sA' s'' →
          HaltsO aMachine O prog pc sA s'' := by
  obtain ⟨dst, r, rfl, hres, hsub⟩ := hst
  obtain ⟨u', zf, hag, hrel⟩ := hI
  obtain ⟨hpre, hall⟩ := hres u' hag sa zf sA hrel hc hcall' (pc + 1)
  obtain ⟨t, sc, hrun⟩ := hX.halts _ hpre
  obtain ⟨sa', hpc, hA, w, zf', hag2, hrel2⟩ := hall t sc hrun
  refine ⟨_, sa', hpc, hA, ⟨w, zf', ((hag.retRes dst r).trans hag2).mono hsub, hrel2⟩,
    fun x hx => ?_, fun s'' hr => .call hcall (hO _ t _ hrun) hr⟩
  rw [retOps_eq, (evalInstrA_leaFrame sc 8).2,
    hX.frame _ t sc hpre hrun x fun hf => hx (hfoot u' zf hrel _ x hf),
    entryOf_mem _ sA x fun hr => hx (hret x hr)]

/-- **The steps of a segment keep the bytes outside `M`**: `ImageAddrCallW.steps_callImgW`
    with the machine states at the two ends equal at every byte outside a set `M` that holds
    the red-zone word and `imgStores`. -/
theorem steps_callImgW_keep (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    {O : Nat → AState → AState → Prop} {prog : List RInstr} {pos : Nat → Nat}
    {tgt : String → Nat} {FinA : LstateA → AState → Prop}
    (hbytes : ByteSegW frame rsp body O prog pos tgt FinA)
    {M : Set (BitVec 64)} (hred : ∀ x, InRange8 (redW rsp) x → x ∈ M)
    (hM : imgStores frame slotArr base ⊆ M)
    {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (site : Nat → String × List String) (fn : String) :
    ∀ (n : Nat) (s u : LstateMF) (sa : LstateA) (zf : Bool) (sA : AState),
      SegStW frame slotArr base rsp body fn s sa zf sA →
      Steps I (singletonProgM fn (callImg slotArr site body)) n s u →
      ∃ sa' zf' sA', SegStW frame slotArr base rsp body fn u sa' zf' sA'
        ∧ (∀ x, x ∉ M → sA'.mem x = sA.mem x)
        ∧ ∀ s'', HaltsO aMachine O prog (pos sa'.reg.lpc) sA' s'' →
            HaltsO aMachine O prog (pos sa.reg.lpc) sA s''
  | 0, s, u, sa, zf, sA, hst, h => by
      have hsu : s = u := Option.some.inj h
      subst hsu
      exact ⟨sa, zf, sA, hst, fun _ _ => rfl, fun _ hr => hr⟩
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
        obtain ⟨sA1, hA1, -, hz1, hcy1, hk1⟩ :=
          hbytes.step sa s.zf sa1 c.zf sA ⟨hsl, hw, hcs, hst.narrow⟩ hst1 hst.corr hst.cond
            hst.carry
        have hm1 := keep_of_stepA hred hM
          (storeIn_callImgW hsep hgate _ hrel hst.inv hb hlt hnc hck) hst1 hst.corr hA1
        rcases hcase with ⟨hrel1, hinv1⟩
          | ⟨⟨bp, ii, l, hbp, hlb⟩, -, hsl1, sa2, hst2, hrel2, hinv2⟩
        · obtain ⟨sa', zf', sA', hst', hm, hk⟩ :=
            steps_callImgW_keep hsep hphys hgate hsites hbytes hred hM hI site fn n c u sa1
              c.zf sA1 ⟨hfn1, hrel1, hinv1, hA1, hz1, hcy1, hn1⟩ h
          exact ⟨sa', zf', sA', hst', fun x hx => (hm x hx).trans (hm1 x hx),
            fun s'' hr => hk1 _ (hk _ hr)⟩
        · obtain ⟨hw1, hcs1⟩ := safeAt_label (rsp := rsp) hbp hlb
          obtain ⟨sA2, hA2, -, hz2, hcy2, hk2⟩ :=
            hbytes.step sa1 c.zf sa2 c.zf sA1 ⟨hsl1, hw1, hcs1, hn1⟩ hst2 hA1 hz1 hcy1
          have hm2 := keep_of_stepA hred hM
            (ImageAddrStore.accessIn_of_label hbp hlb).1 hst2 hA1 hA2
          obtain ⟨sa', zf', sA', hst', hm, hk⟩ :=
            steps_callImgW_keep hsep hphys hgate hsites hbytes hred hM hI site fn n c u sa2
              c.zf sA2 ⟨hfn1, hrel2, hinv2, hA2, hz2, hcy2, narrowInv_step hn1 hst2⟩ h
          exact ⟨sa', zf', sA', hst',
            fun x hx => ((hm x hx).trans (hm2 x hx)).trans (hm1 x hx),
            fun s'' hr => hk1 _ (hk2 _ (hk _ hr))⟩

/-- **A chain of segments and calls keeps the bytes outside `M` and restores the frame.**
    Under the hypotheses of `ImageAddrCallW.haltsO_of_deadChecksS` at the end `FinLea` of the
    closing return, let `M` hold the red-zone word, the return word of a call, `imgStores`,
    and the footprint of the interface of each callee at each of its call sites. The program
    halts under the oracle in a state whose stack register is `rsp` raised by the frame `F`
    and whose memory is that of the start at every byte outside `M`. -/
theorem haltsO_of_runChain_keep (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW frame slotArr body = true) (hsites : callSitesB slotArr body = true)
    (hcarry : ∀ k, k < body.length → X86Backend.DecodePrintedAddrW.carryPrevB body k = true)
    {X : String → CalleeRun} {c : String → CalleeSig}
    (hX : ∀ f, CalledIn body f → CalleeSpec (X f) (c f))
    {prog : List RInstr} {pos : Nat → Nat} {tgt : String → Nat}
    {O : Nat → AState → AState → Prop}
    (hCall : ∀ f, CalledIn body f → ∀ s tr s', X f s tr s' → O (tgt f) s s') {D : DeadTab}
    (hbits : bitsDeadB frame D body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {fn : String} {site : Nat → String × List String} {I : LprogIsa.Isa}
    (hI : ∀ P i s t, I.step P i s = some t → evalInstrPMemFk true P i s = some t)
    (hD : DeadSteps D I (singletonProgM fn (callImg slotArr site body))) {F : Nat}
    (hbytes : ByteSegW frame rsp body O prog pos tgt (FinLea rsp F))
    (hStep : ∀ p u v, Glue T (singletonProgM fn (callImg slotArr site body)) p u v →
      u.prog.base.reg.lpc = p → ∀ bi ra f l, body[p]? = some bi → bi.li_i = .Lcall ra (f, l) →
      SiteStep frame slotArr base rsp body (X f) (c f) (D.dead p) (D.dead (p + 1)) u v)
    {M : Set (BitVec 64)} (hred : ∀ x, InRange8 (redW rsp) x → x ∈ M)
    (hret : ∀ x, InRange8 (rsp + BitVec.ofInt 64 (-8)) x → x ∈ M)
    (hM : imgStores frame slotArr base ⊆ M)
    (hfoot : ∀ f, CalledIn body f → ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf →
      ACorr rsp sA sa → CallAt body f sa.reg.lpc → ∀ ret x,
      (c f).foot (entryOf ret sA) x → x ∈ M)
    {s t : LstateMF}
    (hch : RunChain I T (singletonProgM fn (callImg slotArr site body)) s t) :
    ∀ sa sA, s.prog.lfn = fn → sa.reg.lpc < body.length →
      liveW D slotArr body sa.reg.lpc = false →
      ImgRelF frame slotArr base body (D.dead sa.reg.lpc) s sa → ACorr rsp sA sa →
      ∃ sA', HaltsO aMachine O prog (pos sa.reg.lpc) sA sA'
        ∧ sA'.regs "%rsp" = rsp + BitVec.ofInt 64 (Int.ofNat F)
        ∧ ∀ x, x ∉ M → sA'.mem x = sA.mem x := by
  have hSeg := segExactW_callImg hsep hphys hgate hsites hcond hbytes hI site T fn
  induction hch with
  | @done s t hseg =>
    intro sa sA hfn hlen hL hI0 hA
    obtain ⟨s', zf, hag, hrel⟩ := deadAgree_of_imgRelF (liveW_false_spec hL).1 hI0
    obtain ⟨n, hn, hhalt0⟩ := hseg
    obtain ⟨t', hn', hagt⟩ := hD n s s' t hag hn
    have hfn' : s'.prog.lfn = fn := hag.off.fn.symm.trans hfn
    have hhalt' : Halted (singletonProgM fn (callImg slotArr site body)) t' := by
      unfold Halted findInstrMem at hhalt0 ⊢
      rw [← hagt.off.fn]
      exact (congrArg (fun q => if t.prog.lfn = fn then (callImg slotArr site body)[q]? else none)
        hagt.off.pc.symm).trans hhalt0
    obtain ⟨sa', zf', sA', hst', hm, hk⟩ := steps_callImgW_keep hsep hphys hgate hsites hbytes
      hred hM hI site fn n s' t' sa zf sA (segStW_start hcond hfn' hL hrel hA) hn'
    obtain ⟨saE, zfE, sAE, hrelE, -, hendE, -⟩ :=
      hSeg.toEnd s' sa zf sA t' hfn' hlen hL hrel hA ⟨n, hn', hhalt'⟩
    have hend : sa'.reg.lpc + 1 = body.length := by
      rw [hst'.rel.pc, ← hrelE.pc]
      exact hendE
    have hpe : sa'.reg.lpc = body.length - 1 := by omega
    obtain ⟨-, hA2⟩ := imgRelF_of_imgRelW
      (E := D.dead (body.length - 1)) hst'.rel hst'.corr (by rw [hpe]; exact bitsDeadB_last hbits)
    obtain ⟨sA'', hrun, sB, hB, rfl⟩ := hbytes.halt (widenS sA' sa') sA' hend hA2
    refine ⟨_, hk _ hrun, ?_, fun x hx => ?_⟩
    · rw [(evalInstrA_leaFrame sB _).1, ite_eq_left rfl, hB.sp]
    · rw [(evalInstrA_leaFrame sB _).2]
      have hr : ¬ InRange8 (redW rsp) x := fun h => hx (hred x h)
      exact (hB.mem x hr).symm.trans ((hA2.mem x hr).trans (hm x hx))
  | @call s u v t p hseg hcall _ ih =>
    intro sa sA hfn hlen hL hI0 hA
    obtain ⟨s', zf, hag, hrel⟩ := deadAgree_of_imgRelF (liveW_false_spec hL).1 hI0
    obtain ⟨n, hn, hat, i, hi, hproc⟩ := hseg
    obtain ⟨u', hn', hagu⟩ := hD n s s' u hag hn
    have hfn' : s'.prog.lfn = fn := hag.off.fn.symm.trans hfn
    have hat' : atPc (singletonProgM fn (callImg slotArr site body)) p u' :=
      ⟨hagu.off.fn.symm.trans hat.1, hagu.off.pc.symm.trans hat.2⟩
    obtain ⟨sa', zf', sA', hst', hm, hk⟩ := steps_callImgW_keep hsep hphys hgate hsites hbytes
      hred hM hI site fn n s' u' sa zf sA (segStW_start hcond hfn' hL hrel hA) hn'
    obtain ⟨-, -, -, -, -, ⟨bi, ra, ⟨f, l⟩, hb, hbi, hprog⟩, -⟩ :=
      hSeg.toCall s' sa zf sA p u' hfn' hlen hL hrel hA ⟨n, hn', hat', i, hi, hproc⟩
    have hpu : u.prog.base.reg.lpc = p := hat.2
    have hpa : sa'.reg.lpc = p := hst'.rel.pc.trans (hagu.off.pc.symm.trans hpu)
    obtain ⟨⟨u'', zf'', hag2, hrel2⟩, hA2⟩ := imgRelF_of_imgRelW (E := D.dead p) hst'.rel
      hst'.corr (by rw [hpa]; exact bitsDeadB_call hbits hb hbi)
    have hI1 : ImgRelF frame slotArr base body (D.dead p) u (widenS sA' sa') := by
      refine ⟨u'', zf'', ?_, hrel2⟩
      have := hagu.off
      rw [hpu] at this
      exact (this.trans hag2).mono fun r hr => by simpa using hr
    have hst := hStep _ _ _ hcall hpu bi ra f l hb hbi
    have hfv : v.prog.lfn = fn := by
      obtain ⟨dst, x, rfl, -⟩ := hst
      exact (LprogIsa.lfn_retRes dst x u).trans hat.1
    have hin : CalledIn body f := ⟨p, bi, ra, l, hb, hbi⟩
    subst hpa
    obtain ⟨sA2, sa2, hpc2, hc2, hI2, hm2, hcont⟩ :=
      haltsO_call_keep (hX f hin) hI1 hst hA2 ⟨bi, ra, (f, l), hb, hbi⟩ hprog (hCall f hin)
        (M := M) (fun x hx => hret x (by rwa [retWord, hA2.sp] at hx))
        (fun u' zf hr => hfoot f hin u' _ zf _ hr hA2 ⟨bi, ra, l, hb, hbi⟩)
    have hpc2' : sa2.reg.lpc = sa'.reg.lpc + 1 := hpc2
    obtain ⟨sAF, hrun, hspF, hmF⟩ := ih sa2 sA2 hfv
      (by rw [hpc2']; exact lt_of_call_imgGateCBW hgate _ _ _ _ hb hbi)
      (by rw [hpc2']; exact liveW_succ_call hflags hcarry hb hbi)
      (by rw [hpc2']; exact hI2) hc2
    rw [hpc2', hbytes.pos_call _ bi ra _ hb hbi] at hrun
    exact ⟨sAF, hk _ (hcont _ hrun), hspF,
      fun x hx => ((hmF x hx).trans (hm2 x hx)).trans (hm x hx)⟩

/-- **The footprint of a callee at a call site**, at every kind: it is among the `G` bytes
    below the return word or, at an out result, in the words of the array the site passes as
    destination, so it lies in a set with both. -/
theorem ok_foot_mem {k : CalleeKind} {site : Nat → String × List String} {f : String} {G : Nat}
    (hk : k.Ok frame slotArr base rsp body site f G) {M : Set (BitVec 64)}
    (hM : imgStores frame slotArr base ⊆ M)
    (hG : ∀ x, InFrame (rsp + BitVec.ofInt 64 (-8)) G x → x ∈ M)
    {s : LstateMF} {sa : LstateA} {zf : Bool} {sA : AState}
    (hrel : ImgRel frame slotArr base body s sa zf) (hc : ACorr rsp sA sa)
    (hcall : CallAt body f sa.reg.lpc) (ret : Nat) (x : BitVec 64)
    (hx : k.sig.foot (entryOf ret sA) x) : x ∈ M := by
  have he : (entryOf ret sA).regs "%rsp" = rsp + BitVec.ofInt 64 (-8) := by
    rw [entryOf_regs, ite_eq_left rfl, retWord, hc.sp]
  -- The footprint at an out result, at the pointer of the destination.
  have hout : ∀ {F n : Nat} {po q A : String}, F ≤ G → gpOk po = true →
      sa.reg.getW po 64 = some (base A) → slotArr q = some (A, n) →
      (InFrame ((entryOf ret sA).regs "%rsp") F x
        ∨ ∃ j < n, InRange8 (cellAt ((entryOf ret sA).regs (phys po)) j) x) → x ∈ M := by
    intro F n po q A hF hgp hptr hq h
    rcases h with h | ⟨j, hj, h⟩
    · exact hG x (he ▸ inFrame_mono_of_le hF h)
    · rw [entryOf_regs, ite_eq_right (gpFacts hgp).physNe,
        Option.some.inj ((hc.regs po hgp).symm.trans hptr)] at h
      exact hM (ImageAddrStore.cell_mem_imgStores hq hj x h)
  cases k with
  | word c res pr room =>
    obtain ⟨-, hF, -, -⟩ := hk
    exact hG x (he ▸ hF _ x hx)
  | outO l ps po n =>
    obtain ⟨hL, hle, -, hentry, hqA⟩ := hk
    obtain ⟨q, hq⟩ := hqA _ hcall
    exact hout hle hL.po_gp (hentry s sa zf sA hrel hc hcall).1 hq
      (LinkedFnCallee.footBelowOut_outSig hL _ x hx)
  | ins l ps res =>
    obtain ⟨hL, -, -, hle, -, -⟩ := hk
    exact hG x (he ▸ inFrame_mono_of_le hle
      (LinkedFnContract.footBelow_contractSig hL.result _ _ _ x hx))
  | outC l ps po n =>
    obtain ⟨hL, -, -, hle, hqA, hA, hpar, -⟩ := hk
    obtain ⟨q, hq⟩ := hqA _ hcall
    exact hout hle hL.po_gp
      ((List.forall₂_iff_zip.1 (hpar s sa zf sA hrel hc hcall)).2 (hA _ hcall)).2.2 hq
      (LinkedFnContract.footBelowOut_contractSig hL _ _ _ x hx)

end Image

/-! ## 2. The back half -/

section Back

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (ProcTable)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (runOf InFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (HaltsC)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState InRange8)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall

/-- **The return word and the frames of the callees lie in the stack words of the layout**:
    under the stack room check, every byte of the stack word at the offset `-(F + 8)` from the
    entry stack register, `F` the frame of the body, and every one of the `G` bytes below it is
    a byte of `layoutMem σ sa`. -/
theorem callStack_mem_layoutMem {σ : AbiLayout} {body : Lcmd} {G : Nat}
    (hr : X86Backend.CalleeStackRoom.stackRoomB σ body G = true) (sa : AState) {x : BitVec 64}
    (hx : InRange8 (X86Backend.DecodePrintedCFG.frameRsp body sa + BitVec.ofInt 64 (-8)) x
      ∨ InFrame (X86Backend.DecodePrintedCFG.frameRsp body sa + BitVec.ofInt 64 (-8)) G x) :
    x ∈ layoutMem σ sa := by
  simp only [X86Backend.CalleeStackRoom.stackRoomB, decide_eq_true_eq] at hr
  set H : Int := -(((X86Backend.LprogBytesDecode.Params.ofBody body).frame : Int) + 8) with hH
  have hret : X86Backend.DecodePrintedCFG.frameRsp body sa + BitVec.ofInt 64 (-8)
      = sa.regs "%rsp" + BitVec.ofInt 64 H := by
    simp only [X86Backend.DecodePrintedCFG.frameRsp, BitVec.add_assoc, ← BitVec.ofInt_add]
    congr 2
    simp only [hH, Int.ofNat_eq_natCast]
    omega
  rw [hret] at hx
  rcases hx with hx | hx
  · exact Or.inl (mem_wordsLocs ⟨H, by omega, hr.2, rfl⟩ hx)
  · unfold InFrame at hx
    set d := (x - (sa.regs "%rsp" + BitVec.ofInt 64 H + BitVec.ofInt 64 (-(G : Int)))).toNat
      with hdd
    have hxe : sa.regs "%rsp" + BitVec.ofInt 64 (H - G + d) = x := by
      rw [BitVec.ofInt_add, sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_natCast, hdd,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
      ring
    refine Or.inl (mem_wordsLocs ⟨H - G + d, by omega, by omega, rfl⟩ ?_)
    change InRange8 _ x
    unfold InRange8
    rw [hxe, BitVec.sub_self]
    decide

/-- **The linked bytes of a calling body restore the stack register and keep the memory
    outside the layout.** Under the hypotheses of `regionBack_correct_linked_multi` at the
    leaky runs of the decoded blocks `q` of the table `T` that `regionCallee` finds, the bytes
    decode to a program that halts through the calls from `sa` with the stack register of `sa`
    and with the memory of `sa` outside `layoutMem σ sa`. -/
theorem regionBack_linked_keep {σ : AbiLayout} {a : AbiNames}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    {linked : List CalleeData} {P : Lprog} {bytes : List (BitVec 8)}
    (h : regionBack σ a p linked = some (P, bytes)) (hcf : p.callFree = false) {T : CalleeTab}
    (hT0 : ∃ r0, exportR Γ.length a.fname (legalizeRegion p) Γ.length 0 = some r0
      ∧ regionCallee linked (legalizeRegion p) r0.code = some (some T))
    {kind : String → CalleeKind} {q : CalleeData → List RInstr}
    (hdecq : ∀ c ∈ T.fns, decodeLprog c.bytes = some (q c))
    (hK : ∀ c ∈ T.fns, (kind c.name).Top c ∧ (kind c.name).Spec (runOf ctRegime (q c)))
    {Ec : CallEnv jasminDialect} {PT : ProcTable} (hT : ProcsAgree Ec PT)
    (hwo : ∀ f pr, f ∉ T.names → PT f = some pr → pr.WordOnly ∧ pr.RetWord)
    (hTc : ∀ c ∈ T.fns, PT c.name = some (kind c.name).summary)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denoteAt Ec fuel V = some v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ HaltsC aMachine prog 0 sa sa'
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ x, x ∉ layoutMem σ sa → sa'.mem x = sa.mem x := by
  obtain ⟨T', r0, hr0, hcT, hst, hB, r, b, cert, hwb, hbs, hg, -, -⟩ := regionBack_spec_tab h hcf
  obtain ⟨r0', hr0', hcT'⟩ := hT0
  rw [hr0, Option.some.injEq] at hr0'
  subst hr0'
  rw [hcT, Option.some.injEq, Option.some.injEq] at hcT'
  subst hcT'
  have hnoc := fun c hc => (regionCoB_callee hg).2 c hc (q c) (hdecq c hc)
  obtain ⟨w, m, rfl⟩ := hst
  generalize hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCodeT (some T') r.code) r.res
    cert (some T') = d
  -- The summaries of the procedure table at the symbols of the table and elsewhere.
  have hTf : ∀ f c, T'.lookup f = some c → PT f = some (kind f).summary := by
    intro f c hc
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    exact hTc c hcm
  have hnames : ∀ f, T'.lookup f = none → f ∉ T'.names := by
    intro f hf hmem
    obtain ⟨c, hc⟩ := T'.lookup_of_mem hmem
    rw [hf] at hc
    cases hc
  have haa : LprogIsa.Isa.procArrArgs PT = calleeAAT (some T') := by
    funext f
    cases hl : T'.lookup f with
    | some c =>
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hl
      have hF := (hK c hcm).1.facts
      simp [LprogIsa.Isa.procArrArgs, calleeAAT, hl, hTc c hcm, hF.2.1]
    | none =>
      cases hPf : PT f with
      | none => simp [LprogIsa.Isa.procArrArgs, calleeAAT, hl, hPf]
      | some pr =>
        have hw : pr.arrArgs = fun _ => none := (hwo f pr (hnames f hl) hPf).1
        simp [LprogIsa.Isa.procArrArgs, calleeAAT, hl, hPf, hw]
  have hao : LprogIsa.Isa.procOut PT = calleeAOT (some T') := by
    funext f
    cases hl : T'.lookup f with
    | some c =>
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hl
      have hF := (hK c hcm).1.facts
      simp only [LprogIsa.Isa.procOut, calleeAOT, hl, hTc c hcm, hF.2.2.1, Option.bind_some]
      cases c.res <;> rfl
    | none =>
      cases hPf : PT f with
      | none => simp [LprogIsa.Isa.procOut, calleeAOT, hl, hPf]
      | some pr =>
        have hw : pr.out = none := (hwo f pr (hnames f hl) hPf).2
        simp [LprogIsa.Isa.procOut, calleeAOT, hl, hPf, hw]
  have hkd : ∀ f pr, PT f = some pr → pr.Kinded := by
    intro f pr hf
    cases hl : T'.lookup f with
    | some c =>
      rw [hTf f c hl] at hf
      cases hf
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hl
      exact (hK c hcm).1.facts.2.2.2.1
    | none => exact LprogIsa.ProcSummary.kinded_of_retWord (hwo f pr (hnames f hl) hf).2
  obtain ⟨k, u, hu, hcb, hsep, hrelF, hacorr, hpc0, hbnd, -⟩ :=
    RegionLinkCompose.regionCo_bytes_tab (regionExportableB_sound hB) hr0 ⟨w, m, rfl⟩ hwb hg hd
      hT hkd haa hao (fun f c hc => by rw [hTf f c hc]; rfl) sa V hV hreg fuel
      ((legalizeRegion_denoteAt Ec fuel p V).trans hv)
  -- The conjuncts of the gate.
  have hg' := hg
  simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hce⟩, hren⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, himg⟩⟩ := hg'
  have hcells : d.cells = [] := List.isEmpty_iff.mp hce
  rw [hcells] at himg
  simp only [renImageB, X86Backend.ImageAddrRouteW.slotArrC_nil, Bool.and_eq_true] at himg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hphys⟩, himgT⟩, hfrok⟩, hent⟩, -⟩, -⟩ := himg
  obtain ⟨-, -, hcls, hgate⟩ := calleeImgBT_some himgT
  have hcellsE : d.cells = regionCells σ exportReg d.ps b (d.fused.drop d.pre.length) := by
    rw [← hd]; rfl
  have hcb0 : X86Backend.ImageAddrCells.cellBody
      (X86Backend.ImageAddrRoute.slotRen (X86Backend.ImageAddrRoute.slotArrOf σ exportReg)
        (VIR.JasminLsemRenameLoop.renOf d.ps)) b = b :=
    RegionLinkCall.cellBody_of_cellArrsOf_nil _
      (RegionLinkCall.cellArrsOf_nil_of_regionCells_nil (hcellsE ▸ hcells))
  rw [hcb0] at hphys hrelF
  have hfm : X86Backend.ImageStraightCells.frameMarkC [] b
      = X86Backend.ImageAddrFrame.frameMark (X86Backend.ImageAddrFrame.frameNames b) := rfl
  rw [hcb0, hfm] at hgate
  generalize hsl : X86Backend.ImageAddrRoute.slotRen
    (X86Backend.ImageAddrRoute.slotArrOf σ exportReg)
    (VIR.JasminLsemRenameLoop.renOf d.ps) = sl at hcb hphys hgate hsep hrelF
  generalize hrsp : X86Backend.DecodePrintedCFG.frameRsp b sa = rsp at hsep hacorr
  -- The checks of the calling body.
  have hok := calleeBodyBT_spec.mp hcb
  have hdead := hok.dead
  simp only [calleeDeadBT, Bool.and_eq_true] at hdead
  obtain ⟨hdo, hparB⟩ := hdead
  have hl : b.getLast?.any (fun r => X86Backend.DecodePrinted.isRetB r.li_i) = true := by
    have h1 := hcls
    simp only [X86Backend.ImageAddrCallW.printedAddrCWB, Bool.and_eq_true] at h1
    exact h1.1.1.1.2
  have hcall : ∀ {p : Nat} {bi : Linstr} {ra : Option String} {f : String} {l : LLabel},
      b[p]? = some bi → bi.li_i = .Lcall ra (f, l) → ∃ c, T'.lookup f = some c :=
    fun hb hbi => lookup_of_call hok.decode hl hb hbi
  -- The dead names at the interfaces and the result kinds of the kinds.
  generalize hDt : deadTab (X86Backend.ImageAddrCall.callImg sl (siteFn T'.lookup sl b) b)
    d.outs = D at hdo
  have hdead' : X86Backend.ImageAddrCall.callDeadSymB (fun f => (kind f).sig)
      (fun f => (kind f).isOut) (siteFn T'.lookup sl b) D.dead b = true := by
    refine (callDeadSymB_congr_exempt fun p bi ra f l hb hbi => ?_).trans hdo
    obtain ⟨c, hc⟩ := hcall hb hbi
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    obtain ⟨-, -, -, -, hout, hclob, hres, -⟩ := (hK c hcm).1.facts
    refine ⟨?_, ?_, rfl⟩
    · simp only [CalleeTab.sigOf, hc]
      unfold X86Backend.ImageAddrCall.exemptC
      rw [hclob, hres]
    · simp only [CalleeTab.outOf, hc, Option.any_some, hout]
      cases c.res <;> rfl
  -- The summaries at the call sites of the image.
  have hsit : X86Backend.ImageAddrCall.SitesOf PT
      (X86Backend.ImageAddrCall.callImg sl (siteFn T'.lookup sl b) b)
      (fun p => (kind ((callSymAt b p).getD "")).summary) (siteFn T'.lookup sl b) :=
    X86Backend.ImageAddrCall.sitesOf_callImg _ hok.callSites fun p bi ra f l hb hbi => by
      obtain ⟨c, hc⟩ := hcall hb hbi
      simp only [callSymAt_eq_some.mpr ⟨bi, ra, l, hb, hbi⟩, Option.getD_some]
      exact hTf f c hc
  -- The image run at the table.
  obtain ⟨fuel', t', himgrun, -⟩ := RegionLinkCompose.calleeBody_imgRun_tab hcb
    (fun f c hc => by
      obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
      obtain ⟨har, -, -, -, -, -, -, hrw⟩ := (hK c hcm).1.facts
      exact ⟨_, hTc c hcm, har, hrw.imp id fun hall p _ => hall _ _ p⟩)
    ⟨⟨X86Backend.ImageAddrRoute.entryV σ (X86Backend.ImageAddrRoute.frameE b sa) sa
      (X86Backend.ImageAddrRoute.unren d.ps), a.fname⟩, false⟩
    u rfl rfl hbnd k hu
  -- The separation of the caller at the renamed slot map.
  have RF := X86Backend.ImageAddrRoute.renB_spec hren
  have E := X86Backend.ImageAddrRoute.entryB_spec hent sa
  have hU : ∀ j, j < σ.args.length → X86Backend.ImageAddrRoute.unren d.ps
      (VIR.JasminLsemRenameLoop.renOf d.ps (argName j)) = argName j :=
    fun j hj => (RF.unr j hj).2
  have hS0 := X86Backend.CalleeStackRoom.callerSep_of_regions E.rs hreg hok.stackRoom
    hok.frameNonneg (slotArr := X86Backend.ImageAddrRoute.slotArrOf σ exportReg) E.len
  have hS : X86Backend.ImageAddrCall.CallerSep (X86Backend.ImageAddrRoute.frameE b sa) sl
      (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) rsp T'.frame := by
    subst hrsp hsl
    refine ⟨hS0.frames, fun q' A' n j hq hj x hx => ?_⟩
    obtain ⟨A, hA, rfl⟩ := X86Backend.ImageAddrRoute.slotRen_some hq
    obtain ⟨i, ai, hi, -, rfl, -⟩ := X86Backend.ImageAddrRoute.slotArrOf_some hA
    simp only [X86Backend.ImageAddrRouteW.baseR,
      hU i (List.getElem?_eq_some_iff.mp hi).1] at hx
    exact hS0.cells q' _ n j hA hj x hx
  have hgateW :=
    (RegionLinkCall.imgGateCBW_frameMark b rsp _).trans hgate
  subst hrsp
  have hgateI := X86Backend.ImageAddrCallW.imgGateW_of_imgGateCBW hgateW
  have hOk : ∀ f, X86Backend.ImageAddrCall.CalledIn b f →
      (kind f).Ok (X86Backend.ImageAddrRoute.frameE b sa) sl
        (X86Backend.ImageAddrRouteW.baseR σ sa d.ps)
        (X86Backend.DecodePrintedCFG.frameRsp b sa) b (siteFn T'.lookup sl b) f T'.frame := by
    rintro f ⟨p, bi, ra, l, hb, hbi⟩
    obtain ⟨c, hc⟩ := hcall hb hbi
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    subst hsl
    exact (hK c hcm).1.ok hsep hgateI hS hparB hok.code hc (CalleeTab.frame_le hcm)
  -- The bytes the simulation writes are bytes of the layout.
  have hMi : X86Backend.ImageAddrStore.imgStores (X86Backend.ImageAddrRoute.frameE b sa) sl
      (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) ⊆ layoutMem σ sa := by
    have h1 := imgStores_export (R := []) (ps := d.ps) hfrok E
      (fun _ h => absurd h List.not_mem_nil) hU
    have hf0 : X86Backend.ImageStraightCells.frameC (X86Backend.ImageAddrRouteW.baseR σ sa d.ps)
        [] (X86Backend.ImageAddrRoute.frameE b sa) = X86Backend.ImageAddrRoute.frameE b sa := rfl
    rw [hf0, X86Backend.ImageAddrRouteW.slotArrC_nil, hsl] at h1
    exact h1
  -- The program of the linked bytes.
  obtain ⟨hbytes, hne, ds, prog, hss, hbr, hP, hprog, hp0⟩ := RegionLinkCall.calleeBytes_tab hbs
  have hbne : b ≠ [] := by
    intro hb
    simp [X86Backend.ImageAddrCallW.printedAddrCWB, hb] at hcls
  have hLv : X86Backend.ImageAddrCallW.liveW D sl b
      (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc = false := by
    subst hDt
    rw [hpc0]
    exact X86Backend.ImageAddrCallW.liveW_zero (by simpa using hok.live0)
      (X86Backend.ImageAddrCallW.callFacts_of_printedAddrCWB hcls hss).carry
  have hbits : X86Backend.ImageAddrCallW.bitsDeadB (X86Backend.ImageAddrRoute.frameE b sa) D b
      = true := by
    subst hDt
    exact (RegionLinkCall.bitsDeadB_frameMark b _ _).trans hok.bitsDead
  have hRB := T'.regionBlocks (regionCallee_fns_ne_nil hcT) q hdecq hne hnoc T'.names
    (fun _ hf => hf)
  have hag := symTgt_linkMap_regionTgt T' (calleeSym T' b)
    (X86Backend.LprogBytesDecode.Params.ofBody b) b ds hss
    (RegionLinkCall.remoteSym_mem_names hcls hok.decode)
  rw [X86Backend.LprogBytesLinkReloc.branchOKRelocMap_congr _ _ (hag _ _)] at hbr
  rw [X86Backend.LprogBytesLinkReloc.expectedRelocMap_congr _ _ (hag _ _)] at hP
  have hCF := X86Backend.ImageAddrCallW.callFacts_of_printedAddrCWB hcls hss
  obtain ⟨hsaves, hF0, hFr⟩ := X86Backend.ImageAddrCallW.printedAddrCWB_reloc hcls
  obtain ⟨hdec, hLk⟩ := X86Backend.LprogBytesLinkReloc.linkedProg_of_bytesSymL (calleeSym T' b)
    hCF.toLinkFacts T'.bytes T'.names _ _ _ prog hsaves hF0 hFr hRB.decode hbr hP
  have hmem : ∀ f, X86Backend.ImageAddrCall.CalledIn b f → f ∈ T'.names := by
    rintro f ⟨p, bi, ra, l, hb, hbi⟩
    obtain ⟨c, hc⟩ := hcall hb hbi
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    exact List.mem_map_of_mem hcm
  have hspec : ∀ f, X86Backend.ImageAddrCall.CalledIn b f → (kind f).Spec (runOf ctRegime
      (X86Backend.LprogBytesLinkReloc.regionCode (T'.regionEntries q) f)) := by
    rintro f ⟨p, bi, ra, l, hb, hbi⟩
    obtain ⟨c, hc⟩ := hcall hb hbi
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    rw [CalleeTab.regionCode_lookup T' q hc]
    exact (hK c hcm).2
  obtain ⟨sA', hhalt, hsp, hkeep⟩ := haltsO_of_runChain_keep hsep hphys hgateW hok.callSites
    hCF.carry (fun f hf => CalleeKind.calleeSpec_of_spec (hspec f hf))
    (O := X86Backend.Callee.oracleOf T'.names (fun f => prog.length + T'.entryIdx (T'.symPos f))
      (fun f => runOf ctRegime
        (X86Backend.LprogBytesLinkReloc.regionCode (T'.regionEntries q) f)))
    (fun f hf _ tr _ hx => ⟨f, hmem f hf, rfl, tr, hx⟩)
    hbits (hDt ▸ hok.flags) (hDt ▸ hok.condLive) X86Backend.CheckedIsaCall.x86IsaK_checked
    (hDt ▸ X86Backend.CheckedIsaCall.deadSteps_x86K hok.deadSeg)
    (X86Backend.ImageAddrCallW.byteSegW_of_linked hCF hLk _
      (fun q hq => X86Backend.ImageAddrFrame.frameIn_eq q hq) _)
    (fun p _ _ hglue hpc bi ra f l hb hbi =>
      CalleeKind.siteStep hsep hphys (hspec f ⟨p, bi, ra, l, hb, hbi⟩) hS
        (hOk f ⟨p, bi, ra, l, hb, hbi⟩) ⟨bi, ra, l, hb, hbi⟩
        (X86Backend.ImageAddrCall.callDeadSymB_spec hdead' hb hbi).1
        (X86Backend.ImageAddrCall.callDeadSymB_spec hdead' hb hbi).2 hsit
        (by simp only [callSymAt_eq_some.mpr ⟨bi, ra, l, hb, hbi⟩, Option.getD_some])
        hpc hglue)
    (M := layoutMem σ sa)
    (fun x hx => Or.inl (mem_wordsLocs (redW_mem_frameWords hfrok sa) hx))
    (fun x hx => callStack_mem_layoutMem hok.stackRoom sa (.inl hx)) hMi
    (fun f hf _ _ _ _ hrel hc hat => ok_foot_mem (hOk f hf) hMi
      (fun x hx => callStack_mem_layoutMem hok.stackRoom sa (.inr hx)) hrel hc hat)
    (VIR.LprogCallCut.runChain_of_run _ PT _ fuel' _ t' himgrun)
    (X86Backend.ImageAddrRoute.entryA σ sa) _ rfl
    (by rw [hpc0]; exact List.length_pos_iff.mpr hbne) hLv (hrelF _) hacorr
  have hpos : X86Backend.DecodePrintedCFG.posOf ds 0 = 0 + 1 := by
    simp [X86Backend.DecodePrintedCFG.posOf]
  rw [hpc0, hpos] at hhalt
  have hlen0 : 0 < prog.length := by
    rcases hq : prog with _ | ⟨x, xs⟩
    · rw [hq] at hp0; cases hp0
    · simp
  refine ⟨_, sA', hbytes ▸ hdec, .go ?_ (X86Backend.Callee.haltsC_of_haltsO_blocks aMachine prog
    _ (fun t s sc ho => ?_) hhalt), ?_, fun x hx => ?_⟩
  · simp only [X86Backend.RInstrSemantics.step, List.getElem?_append_left hlen0, hp0]
    rfl
  · obtain ⟨f, hf, rfl, tr, hrunf⟩ := ho
    obtain ⟨A, B, hQ, hA⟩ := hRB.block f hf
    exact ⟨A, _, B, hQ, by rw [hA], hRB.callFree f hf, X86Backend.DecodedCT.RunL.halts hrunf⟩
  · rw [hsp]
    simp only [X86Backend.DecodePrintedCFG.frameRsp, BitVec.add_assoc, ← BitVec.ofInt_add]
    simp
  · rw [hkeep x hx, (X86Backend.DecodePrinted.evalInstrA_leaFrame sa _).2]

end Back

/-! ## 3. The compiler -/

section Top

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts HaltsC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (HaltsO runOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)

/-- **Every halting run of the bytes of an entry with linked calls restores the stack register
    and keeps the memory outside the layout.** Under the hypotheses of
    `NFEntry.call_halts_multi`, a run through calls of a decoding of the bytes from an entry
    state `sa` with a source run ends with the stack register of `sa` and with the memory of
    `sa` outside `layoutMem σ sa`. It is `regionBack_linked_keep` at the kinds `kernelKind` of
    the linked kernels of the table, and the determinism `halts_det` of the decoded machine. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.NFEntry.linked_keep (E : NFEntry)
    {s : E.Src} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hnd : ((E.linked s).map (·.name)).Nodup)
    (hk : ∀ l ∈ E.linked s, LinkedKernel l)
    {q0 : Σ t : NFDialect.NfTy,
      NFProg NFDialect.nfDialect (CatCrypt.Crypto.Hax.ImpToNF.entryCtx (NFToRoute.abiEntry σ))
        [t]}
    (hq0 : E.toNF σ s = some q0)
    {p : NFProg jasminDialect (nfCtx σ)
      [CryptoToJasminCom.mapTy (CatCrypt.Crypto.Hax.NFToCat.catTy q0.1)]}
    (hp : (extChain (E.decls s) _ q0.1).run q0.2 = some p) (hcf : p.callFree = false)
    (h1 : compileRegion σ (E.names fname σ) p ((E.linked s).filterMap LinkedFn.calleeData)
      = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : E.Runs σ s sa v)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog)
    {sa' : AState} (hh : HaltsC aMachine prog 0 sa sa') :
    sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ x, x ∉ layoutMem σ sa → sa'.mem x = sa.mem x := by
  obtain ⟨-, w, -, h1, hcfw, hden⟩ := compileRegion_ctx (nfCtx_wide σ) h1
  have hcf' := hcfw.trans hcf
  obtain ⟨T, hpin, hsub, hne, -, hcalls, -, -⟩ := regionBack_correct_linked_multi h1 hcf'
  obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨l0, -, -⟩ := List.mem_filterMap.mp (hsub.subset hc0)
  -- The linked kernel of each function of the table, at its kind and its decoded block.
  have hkind : ∀ c ∈ T.fns, ∃ l ∈ E.linked s, l.calleeData = some c ∧ c.name = l.name
      ∧ moduleKind (E.linked s) (.ins l0 [] "") c.name = kernelKind l c
      ∧ decodeLprog c.bytes = some (moduleBlock (E.linked s) c.name)
      ∧ SepLogic.SContract (runOf ctRegime (moduleBlock (E.linked s) c.name)) l.contract := by
    intro c hc
    obtain ⟨l, hl, hlc⟩ := List.mem_filterMap.mp (hsub.subset hc)
    obtain ⟨-, hn, -, -, -, hb, -⟩ := CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc
    have hf := find?_name_of_nodup hnd hl
    obtain ⟨q, hq, hm⟩ := (hk l hl).contract_code hlc
    have hbl : moduleBlock (E.linked s) c.name = q := by
      rw [hb] at hq
      simp [moduleBlock, hn, hf, hq]
    exact ⟨l, hl, hlc, hn, by simp [moduleKind, hn, hf, hlc], by rw [hbl]; exact hq,
      by rw [hbl]; exact hm⟩
  -- The source run and the summaries at the functions of the table alone.
  let ls := (E.linked s).filter fun l => T.names.contains l.name
  have hmemls : ∀ g, g ∈ ls.map (·.name) ↔ g ∈ T.names := by
    intro g
    constructor
    · intro hg
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
      simpa [CalleeTab.names] using (List.mem_filter.mp hl).2
    · intro hg
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
      obtain ⟨l, hl, -, hn, -⟩ := hkind c hc
      refine List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨hl, ?_⟩, hn.symm⟩
      simpa [← hn, CalleeTab.names] using List.mem_map_of_mem (f := (·.name)) hc
  have henv : linkedEnvOn (E.linked s) (ls.map (·.name)) = linkedEnvOn (E.linked s) T.names := by
    unfold linkedEnvOn
    congr 1
    funext g vals
    by_cases hg : g ∈ T.names
    · simp [hg, (hmemls g).mpr hg]
    · have hg' : g ∉ ls.map (·.name) := fun h => hg ((hmemls g).mp h)
      simp [hg, hg']
  have hT : ProcsAgree (linkedEnvOn (E.linked s) T.names) (summaryTableL ls) := by
    rw [← henv]
    exact procsAgree_summaryTableL hnd (fun l hl => (List.mem_filter.mp hl).1)
      (fun l hl => (hk l (List.mem_filter.mp hl).1).sem_kinds)
      (fun l hl => (hk l (List.mem_filter.mp hl).1).res_slice)
  have hwo : ∀ f pr, f ∉ T.names → summaryTableL ls f = some pr → pr.WordOnly ∧ pr.RetWord := by
    intro f pr hf ht
    obtain ⟨l, hl, -⟩ := Option.map_eq_some_iff.mp ht
    have hlf : l.name = f := by simpa using List.find?_some hl
    exact absurd ((hmemls f).mp (List.mem_map.mpr ⟨l, List.mem_of_find?_eq_some hl, hlf⟩)) hf
  have hTc : ∀ c ∈ T.fns, summaryTableL ls c.name
      = some (moduleKind (E.linked s) (.ins l0 [] "") c.name).summary := by
    intro c hc
    obtain ⟨l, hl, hlc, hn, hkk, -⟩ := hkind c hc
    obtain ⟨-, -, hsum, -⟩ := (hk l hl).kind_facts hlc
    have hlT : l ∈ ls := List.mem_filter.mpr ⟨hl, by
      simpa [← hn, CalleeTab.names] using List.mem_map_of_mem (f := (·.name)) hc⟩
    have hfind := find?_name_of_nodup (hnd.sublist (List.filter_sublist.map _)) hlT
    rw [hkk, hsum, hn, summaryTableL, hfind]
    rfl
  obtain ⟨k, V, x, hV, -, hx⟩ := E.run_linkedEnv hq0 hp hsep hrun
  have hx' : (VIR.NarrowWords.castProg (nfCtx_wide σ) rfl w).denoteAt
      (linkedEnvOn (E.linked s) T.names) k V =
        some (HVector.cons (VIR.NarrowWords.transTy x) .nil) := by
    rw [denoteAt_linkedEnvOn hcalls, hden, hx]
    rfl
  obtain ⟨prog', sa1, hd', hh', hsp, hkeep⟩ := regionBack_linked_keep h1 hcf' hpin
    (kind := moduleKind (E.linked s) (.ins l0 [] ""))
    (q := fun c => moduleBlock (E.linked s) c.name)
    (fun c hc => by
      obtain ⟨l, -, -, -, -, hq, -⟩ := hkind c hc
      exact hq)
    (fun c hc => by
      obtain ⟨l, hl, hlc, -, hkk, -, hm⟩ := hkind c hc
      obtain ⟨htop, hspec, -, -⟩ := (hk l hl).kind_facts hlc
      rw [hkk]
      exact ⟨htop, hspec _ hm⟩)
    hT hwo hTc sa V hV hsep k hx'
  obtain rfl : prog' = prog := Option.some.inj (hd'.symm.trans hd)
  obtain rfl := halts_det hh hh'
  exact ⟨hsp, hkeep⟩

/-- **Every halting run of the bytes of the compiler at an entry restores the stack register
    and keeps the memory outside the layout**, from an entry state with a source run, when the
    linked functions are linked kernels with distinct names: `NFEntry.linked_keep` at a program
    with a `call`, `NFEntry.compileR_correct_saved` and `halts_det` at a program without. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.NFEntry.halts_keep (E : NFEntry)
    (s : E.Src) (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : E.compileR s σ fname ((E.linked s).filterMap LinkedFn.calleeData) = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : E.Runs σ s sa v)
    (hnd : ((E.linked s).map (·.name)).Nodup) (hk : ∀ l ∈ E.linked s, LinkedKernel l)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog)
    {sa' : AState} (hh : HaltsC aMachine prog 0 sa sa') :
    sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ x, x ∉ layoutMem σ sa → sa'.mem x = sa.mem x := by
  rw [NFEntry.compileR_eq_bind] at hc
  obtain ⟨q0, hq0, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨p, hp, hc⟩ := Option.bind_eq_some_iff.mp hc
  cases hcf : p.callFree with
  | true =>
    rw [compileRegion_of_callFree _ _ hcf] at hc
    have hc' : E.compileR s σ fname = some (P, bytes) := by
      simp only [NFEntry.compileR, NFEntry.chainNF, hq0, Option.bind_some, hp, Option.map_some]
      exact hc
    obtain ⟨prog', sa1, hd', hh', -, hsp, -, hkeep, -⟩ :=
      E.compileR_correct_saved s σ fname P bytes hc' sa hsep v hrun
    obtain rfl : prog' = prog := Option.some.inj (hd'.symm.trans hd)
    obtain rfl := halts_det hh hh'
    exact ⟨hsp, fun x hx => hkeep x (fun h => hx (.inl h)) fun r hr h => hx (.inr ⟨r, hr, h⟩)⟩
  | false => exact E.linked_keep hnd hk hq0 hp hcf hc sa hsep v hrun hd hh

/-- **Every halting run of the bytes of `compileA` restores the stack register and keeps the
    memory outside the stack words and the pointer regions.** Under the hypotheses of
    `haxc_correct_auto`, for every decoding `prog` of the bytes and every state `sa'` at which
    `prog` halts from `sa`, through calls or without, `sa'` has the stack register of `sa`,
    and its memory is that of `sa` at every byte outside the stack words `%rsp + o`,
    `frameLo ≤ o ≤ frameHi`, and outside the words of each pointer region of `σ`, at the
    registers of `sa`. It is `NFEntry.halts_keep` at the pair stage. -/
theorem haxc_halts_keep (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v)
    {prog : List RInstr} (hd : decodeLprog bytes = some prog)
    {sa' : AState} (hh : HaltsC aMachine prog 0 sa sa')
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x := by
  obtain ⟨x, hrun', -⟩ := haxRuns_pairStage hrun
  have hl : haxEntry.linked (pairStage m σ).1 = m.linked := pairStage_linked m σ
  obtain ⟨hsp, hkeep⟩ := haxEntry.halts_keep _ _ fname P bytes hc sa
    ((pairStage_regions m σ sa).2 hsep) x hrun' (hl ▸ hnd) (hl ▸ hk) hd hh
  rw [layoutMem_pairStage] at hkeep
  exact ⟨hsp, fun y hf hr => hkeep y fun hy => hy.elim hf fun ⟨p, hp, h⟩ => hr p hp h⟩

/-- **The compiler theorem on a module, with the memory through linked calls.** Under the
    hypotheses of `haxc_correct_auto`, the bytes decode to a program `prog` with one of the two
    cases of that theorem, and in both the state `sa'` at which `prog` halts from `sa` and from
    which `σ` reads back the source value `v` has the stack register of `sa` and, at every
    byte outside the stack words `%rsp + o`, `frameLo ≤ o ≤ frameHi`, and outside the words of
    each pointer region of `σ`, the memory of `sa`. In the case with linked calls these stack
    words hold the return word of each call and the frames of the callees
    (`callStack_mem_layoutMem`), and the bytes a callee writes for its caller are those of a
    pointer region (`ok_foot_mem`). The runs and the read-back are those of
    `haxc_correct_auto_saved`, the two facts those of `haxc_halts_keep`. -/
theorem haxc_correct_auto_keep (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ ∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions,
            SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
      ∨ ∃ cs : List CalleeData, cs.Sublist (m.linked.filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B,
                Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
              ∧ sa'.regs "%rsp" = sa.regs "%rsp"
              ∧ ∀ x, SepLogic.X86.Loc.mem x
                  ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
                (∀ p ∈ σ.regions,
                  SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
                sa'.mem x = sa.mem x)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) := by
  obtain ⟨prog, hd, h⟩ := haxc_correct_auto_saved m σ fname P bytes hc sa hsep v hrun hnd hk
  refine ⟨prog, hd, ?_⟩
  rcases h with ⟨sa', hh, hR, hsp, -, hkeep, -⟩
    | ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hp, ⟨sa', hh, hR⟩, hO⟩
  · exact .inl ⟨sa', hh, hR, hsp, hkeep⟩
  · exact .inr ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hp,
      ⟨sa', hh, hR, haxc_halts_keep m σ fname P bytes hc sa hsep v hrun hd hh hnd hk⟩, hO⟩

end Top

end CatCrypt.Crypto.SecureCompilation.Haxc.LinkKeep
