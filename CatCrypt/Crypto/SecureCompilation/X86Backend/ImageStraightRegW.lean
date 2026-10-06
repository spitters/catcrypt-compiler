/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells

@[expose] public section

set_option autoImplicit false

/-!
# A register-returning straight-line program over the printed class with carry chains

The gate `ImageStraightRoute.straightRegB` of a register-returning straight-line program
asks the printed body to lie in the class `DecodePrintedCFG.printedAddrB` and to pass the
image gate `ImageAddrSim.imgGateB`. This module states the gate over the class
`DecodePrintedAddrW.printedAddrWB` and the image gate with carry chains
`ImageAddrSimW.imgGateBW`, through the cell route `ImageStraightCells.cellRouteB` with the
result register observed: a register select `CMOV:64`, a 64-bit immediate, a carry constant
and a carry chain are in that class.

The observed register is read at the end of the run. The relation `ImageAddrSimW.ImgRelW`
gives a general-purpose name outside the width analysis `ImageAddrSimW.oneBitAt` a 64-bit
value; `ImageAddrSimW.retOutsB` places the observed register outside the analysis at the
return, and `DecodePrintedAddrW.printedAddr_simW` gives a 64-bit value of a general-purpose
name as the value of its machine register.

## Main definitions

* `straightRegWB`: the gate of a register-returning straight-line program over the printed
  class with carry chains, at a fusion flag.

## Main results

* `virt_bytesC_reg`: `ImageAddrCells.virt_bytesC` with the observed general-purpose names
  without a frame word read from the machine registers.
* `cell_route_reg_bytes`: `ImageStraightCells.cell_route_bytes` with the observed
  general-purpose names without a frame word read from the machine registers.
* `straightRegW_bytes`: a program accepted by `straightRegWB` at the bytes, its result read
  back by the layout; the conclusion of `ImageStraightRoute.straight_reg_bytes`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRegW

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots isArrB isCellB
  cellsDistinctB cellsDistinct CellRel slotsOkB cellFold runStraightF_cellFold)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep cellAt ImgRel imgGateB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (Region regLen regK regLay)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (rsOK abiBase abiReg
  cells_disjoint frameSep_of_regions)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState Disjoint8 read64)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (LstateA)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (physImgB virtImg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody CellNoSlot
  CellFrames image_addr_simB image_addr_simBW haltedA_cellBody)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LstateM LinstrRM straightOpsMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (IsLopn singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF isLopnB
  isLopnB_isLopn runStraightF_of_lsemStraightMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (RunIdxOk
  lsemFuelMemFk_of_runIdxOk)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseMulHiRM fuseOKL fuseLoPre
  fuseMulHi_lsemFuelMemF_pre)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (entryV entryA rsOf frameE
  argBind slotArrOf slotRen slotRen_some imgSep_slotRen imgRel_entryV boundFacts_entryV entryB
  entryB_spec fuseRegs entryV_abiEntry frameE_none)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (afterArgs
  lsemFuelMemF_of_runStraightF getW_congr movesState_single_lvm storeAgreesM_lpc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI frameIn frameNames
  frameMark frameOkB runA_congr runSafe_congr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW (imgGateBW imgGateBW_congr
  retOutsB retOutsB_congr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC
  ownedCheckMC_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (idxInvCheckB idxAnnot boundFacts
  runIdxOk_of_idxInvCheckB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB
  printedAddr_simW NarrowCell SafeW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp RunSafe)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP redW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes cmovRedZone)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi (e64_of_abiEntryM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (scalarMemNB
  scalarMemNB_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf storeAgreesM_of_abi)

/-! ## 1. A virtual body on the decoded bytes, at a register -/

/-- **A virtual body on the decoded bytes of a straight body with cells, at the observed
    registers.** Under the hypotheses of `ImageAddrCells.virt_bytesC`, at the end of the
    halting run of the decoded bytes every observed general-purpose name without a frame
    word holds on the virtual body the value of its machine register. -/
theorem virt_bytesC_reg {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {sa : AState} {outs : List String} {B : List LinstrRM}
    (hck : ownedCheckMC outs B (virtImg slotArr (cellBody slotArr body)) = true)
    (hpr : printedAddrWB body = true)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : (imgGateB frame slotArr (cellBody slotArr body)
      || (imgGateBW frame slotArr (cellBody slotArr body)
        && retOutsB frame (cellBody slotArr body) outs)) = true)
    (hsep : ImgSep frame slotArr base (frameRsp body sa))
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base (frameRsp body sa) body)
    (hnc : ∀ (k : Nat) (bi : Linstr), body[k]? = some bi → ∀ cc l, bi.li_i ≠ .Lcond cc l)
    (hfr : ∀ q ∈ bodyNamesI body,
      frame q = frameP (Params.ofBody body) (frameRsp body sa) q)
    (fn : String) (b t : LstateMF) (hfn : b.prog.lfn = fn) (hbpc : b.prog.base.reg.lpc = 0)
    (s : LstateA) (zf : Bool)
    (hrel : ImgRel frame slotArr base (cellBody slotArr body) b s zf)
    (hpc : s.reg.lpc = 0)
    (hent : ∀ R, gpOk R = true → s.reg.getW R 64 = some (sa.regs (phys R)))
    (hmem : s.mem = sa.mem) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel b = some t)
    (hok : RunIdxOk (singletonProgM fn B) fuel b) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∀ r, r ∈ outs → gpOk r = true → frame r = none →
        t.prog.base.reg.getW r 64 = some (sa'.regs (phys r)) := by
  have hck' := lsemFuelMemFk_of_runIdxOk true _ fuel b t hrun hok
  obtain ⟨f', t', hr', hobs⟩ := ownedCheckMC_sound hck fn b t hfn hbpc fuel hck'
  have hsim : ∃ fA sA zA, runA frame body fA s zf = some (sA, zA)
      ∧ (∀ q, q ∈ outs → gpOk q = true → frame q = none →
        t'.prog.base.reg.lvm q = sA.reg.lvm q ∧ (sA.reg.lvm q).1 = 64)
      ∧ RunSafe frame body (SafeW (frameRsp body sa) body) fA s zf := by
    rcases Bool.or_eq_true_iff.mp hgate with hg | hg
    · obtain ⟨fA, sA, zA, h1, h2, h3⟩ :=
        image_addr_simB hsep hphys hg hN hF hnc fn f' b t' s zf hfn hrel hr'
      exact ⟨fA, sA, zA, h1, fun q _ hq hf => ⟨h2.regs q hf, h2.wid q hq⟩, h3⟩
    · obtain ⟨hg, hro⟩ := Bool.and_eq_true_iff.mp hg
      obtain ⟨fA, sA, zA, h1, h2, h3⟩ :=
        image_addr_simBW hsep hphys hg hN hF hnc fn f' b t' s zf hfn
          (ImageAddrSimW.imgRelW_of hrel) hr'
      have hh : haltedA (cellBody slotArr body) sA = true := by
        rw [haltedA_cellBody]
        exact JasminLsemAddrRun.haltedA_of_runA frame body fA s zf (sA, zA) h1
      exact ⟨fA, sA, zA, h1, fun q hq hgp hf => ⟨h2.regs q hf, h2.wid q hgp
        (ImageAddrSimW.not_mem_oneBitAt_of_halted hg hh
          (ImageAddrSimW.not_mem_of_retOutsB hro hq))⟩, h3⟩
  obtain ⟨fA, sA, zA, hrA, hregs, hsafe⟩ := hsim
  rw [runA_congr hfr] at hrA
  rw [runSafe_congr hfr] at hsafe
  obtain ⟨prog, sa', hdec, hh, -, hR, -⟩ :=
    printedAddr_simW body hpr sa s zf hpc (fun R hR => Or.inl (hent R hR)) hmem fA (sA, zA) hrA
      hsafe
  refine ⟨prog, sa', hdec, hh, fun r hr hgp hf => ?_⟩
  obtain ⟨hl, hw⟩ := hregs r hr hgp hf
  have hlv : t.prog.base.reg.lvm r = sA.reg.lvm r := (hobs.1 r hr).symm.trans hl
  rw [getW_congr 64 hlv]
  rcases hR r hgp with h | ⟨b1, hb, -⟩ | hn
  · exact h
  · rw [hb] at hw
    cases hw
  · rcases hn.width with h | h <;> rw [hw] at h <;> cases h

/-! ## 2. The cell route on the decoded bytes, at a register -/

/-- **The cell route on the decoded bytes, at the observed registers.** Under the hypotheses
    of `ImageStraightCells.cell_route_bytes`, at the end of the halting run of the decoded
    bytes every observed general-purpose name without a frame mark holds at the end of the
    run of the folded chain the value of its machine register. -/
theorem cell_route_reg_bytes {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {outs : List String} {C2 : List LinstrRM} {fuse : Bool}
    (hg : cellRouteB σ nm body outs C2 fuse = true)
    (hN : cellNamesOkB σ body = true) (sa : AState) (hreg : σ.Regions sa) (b : LstateM)
    (z : Bool) (hrun : runStraightF C2 (afterArgsC σ body sa (cellArrs σ)) false = some (b, z)) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∀ r, r ∈ outs → gpOk r = true → (frameMark (frameNames body) r).isNone = true →
        b.reg.getW r 64 = some (sa'.regs (phys r)) := by
  simp only [cellRouteB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, hidx⟩, hpr⟩, hphys⟩, hgate⟩, hfr⟩, hent⟩, hacc⟩, hnc⟩, hns⟩, hlop⟩,
    hfuse⟩ := hg
  have N := cellNamesOkB_spec hN
  have E := entryB_spec hent sa
  have hgpN : ∀ r, gpOk r = true → cellIdx (cellArrs σ) r = none := by
    intro r hr
    cases hc : cellIdx (cellArrs σ) r with
    | none => rfl
    | some _ =>
        have := N.gp r (by rw [hc]; rfl)
        rw [hr] at this
        cases this
  have hfrA : ∀ j, j < σ.args.length →
      frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa) (argName j) = none := by
    intro j hj
    simp only [frameC, N.arg j hj]
    exact E.argF j hj
  have hfrR : ∀ a ∈ σ.args, gpOk (nm a.reg) = true ∧ DecodePrinted.phys (nm a.reg) = a.reg
      ∧ frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa) (nm a.reg) = none := by
    intro a ha
    obtain ⟨h1, h2, h3⟩ := E.regs a ha
    refine ⟨h1, h2, ?_⟩
    simp only [frameC, hgpN _ h1]
    exact h3
  have hpr0 := ImageAddrRoute.argBind_entryV (nm := nm) (sa := sa) (un := fun x => x) hfrA E.argG
    hfrR false
  have hB : runStraightF (argBind σ nm ++ C2) (emptyArrs (cellArrs σ)
      (entryV σ (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) sa fun x => x))
      false = some (b, z) := by
    rw [JasminLsemAddrMem.runStraightF_append, runStraightF_argBind_empty hpr0, Option.bind_some]
    exact hrun
  have hl : ∀ i ∈ argBind σ nm ++ C2, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact JasminLsemRenameLoop.movesOf_isLopn _ i hi
    · exact isLopnB_isLopn (List.all_eq_true.mp hlop i hi)
  have hrun' := lsemFuelMemF_of_runStraightF "" _ hl _ b false z rfl hB
  obtain ⟨fuelB, tB, hrunB, hagB⟩ : ∃ fuelB tB, JasminLsemMemFlagGuard.lsemFuelMemF
      (JasminLsemMemLoop.singletonProgM ""
      (cellVirt σ nm C2 fuse)) fuelB
      { prog := { base := emptyArrs (cellArrs σ) (entryV σ (frameC (abiBase (abiReg σ) sa)
        (cellArrs σ) (frameE body sa)) sa fun x => x), lfn := "" }, zf := false } = some tB
      ∧ ∀ r ∈ outs, tB.prog.base.reg.lvm r = b.reg.lvm r := by
    cases fuse with
    | false => exact ⟨_, _, hrun', fun _ _ => rfl⟩
    | true =>
        simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
          bne_iff_ne, ne_eq] at hfuse
        have habiC := ImageAddrRoute.entryV_abiEntry (un := fun x => x) (sa := sa) hfrA E.argG
          fun _ _ => rfl
        have hE : JasminLsemFuseMulHi.E64 (fuseRegs σ nm ++ cellNames (cellArrs σ))
            (emptyArrs (cellArrs σ)
            (entryV σ (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) sa
              fun x => x)) := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · rcases List.mem_append.mp hx with hx | hx
            · exact e64_of_abiEntryM habiC x hx
            · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
              obtain ⟨h1, -, h3⟩ := hfrR a ha
              simp only [emptyArrs, entryV, h3, ImageAddrRoute.entryA, h1, if_true]
          · obtain ⟨⟨A, j⟩, hc⟩ := Option.isSome_iff_exists.mp (cellIdx_isSome.mpr hx)
            simp only [emptyArrs, entryV, frameC, hc]
        obtain ⟨f2, t2, -, ht2, hag, -, -⟩ :=
          fuseMulHi_lsemFuelMemF_pre hfuse.1 "" _ _ rfl hE _ hrun'
        exact ⟨f2, t2, ht2, fun r hr => hag.reg r (hfuse.2 r hr)⟩
  have hents := boundFacts_entryV (nm := nm)
    (fr := frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) (un := fun x => x) hreg
    fun b hb => by
      obtain ⟨h1, h2, h3⟩ := E.bnds b hb
      refine ⟨h1, h2, ?_⟩
      simp only [frameC, hgpN _ h1]
      exact h3
  have hok := runIdxOk_of_idxInvCheckB hidx "" _ _ rfl rfl hents _ hrunB
  have hS0 := imgSep_slotRen (ren := fun x => x) (un := fun x => x)
    (ImageAddrFrame.imgSep_of_regions E.rs hreg hfr E.len E.slot) fun _ _ _ _ => rfl
  have hword : ∀ q a, frameE body sa q = some a →
      ∃ o : Int, σ.frameLo ≤ o ∧ o ≤ σ.frameHi ∧ a = sa.regs "%rsp" + BitVec.ofInt 64 o := by
    intro q a ha
    obtain ⟨hq, o, ho, rfl⟩ := ImageAddrFrame.frameIn_some ha
    have := ImageAddrFrame.frameOkB_range hfr hq ho
    exact ⟨_, this.1, this.2, rfl⟩
  have hsl : ∀ q A n, slotRen (slotArrOf σ nm) (fun x => x) q = some (A, n) →
      regLen (rsOf σ) A = n := by
    intro q A n hq
    obtain ⟨A0, hq0, hA⟩ := slotRen_some hq
    rw [hA]
    exact E.len q A0 n hq0
  have hslC : ∀ q A n, slotRen (slotArrOf σ nm) (fun x => x) q = some (A, n) →
      cellIdx (cellArrs σ) q = none := by
    intro q A n hq
    obtain ⟨A0, hq0, -⟩ := slotRen_some hq
    obtain ⟨a, ha⟩ := E.slot q A0 n hq0
    exact N.body q (ImageAddrFrame.frameIn_some ha).1
  have hsep := imgSep_cells E.rs hreg hS0 hword hsl N.len N.gp hslC
  have hred : ∀ A j, cellIdx (cellArrs σ) (memName A (8 * j)) = some (A, j) →
      Disjoint8 (redW (frameRsp body sa)) (cellAt (abiBase (abiReg σ) sa A) j) := by
    intro A j hc
    obtain ⟨n, hn, hj, -⟩ := cellIdx_spec hc
    have hk : regK (rsOf σ) A j := by
      unfold regK
      rw [N.len _ hn]
      exact hj
    have hr : redW (frameRsp body sa)
        = sa.regs "%rsp" + BitVec.ofInt 64 (cmovRedZone - (Params.ofBody body).frame) := by
      simp only [redW, frameRsp, BitVec.add_assoc, ← BitVec.ofInt_add]
      congr 2
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hr]
    have h2 := ImageAddrFrame.frameOkB_red hfr
    exact frameSep_of_regions E.rs hreg A j hk _ h2.1 h2.2
  have hF := cellFrames_of (base := abiBase (abiReg σ) sa) (rsp := frameRsp body sa) hacc N.gp
    (fun r hr => hS0.gp r hr) hred
  have hgate' : (imgGateB (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
      (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x))
      (cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body)
      || (imgGateBW (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
      (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x))
      (cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body)
      && retOutsB (frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa))
      (cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body) outs))
      = true := by
    rw [ImageAddrFrame.imgGateB_congr (frame' := frameMarkC (cellArrs σ) body)
      (frameC_isSome _ _ body sa), imgGateBW_congr (frame' := frameMarkC (cellArrs σ) body)
      (frameC_isSome _ _ body sa), retOutsB_congr (frame' := frameMarkC (cellArrs σ) body)
      (frameC_isSome _ _ body sa)]
    exact hgate
  have hfr' : ∀ q ∈ bodyNamesI body,
      frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa) q
        = frameP (Params.ofBody body) (frameRsp body sa) q := by
    intro q hq
    simp only [frameC, N.body q hq]
    show frameIn body _ q = _
    unfold frameIn
    rw [if_pos hq]
  have hrel0 := imgRel_entryV (nm := nm)
    (fr := frameC (abiBase (abiReg σ) sa) (cellArrs σ) (frameE body sa)) (sa := sa)
    (body := cellBody (slotArrC (cellArrs σ) (slotRen (slotArrOf σ nm) fun x => x)) body)
    (fn := "") (ren := fun x => x) (un := fun x => x)
    (fun a ha => ⟨(E.regs a ha).1, (E.regs a ha).2.1⟩) fun _ _ => rfl
  have hrel := imgRel_cellArrs (R := cellArrs σ) hrel0
  obtain ⟨prog, sa', hdec, hh, hobs⟩ := virt_bytesC_reg
    (base := abiBase (abiReg σ) sa) hck hpr hphys hgate' hsep (cellNoSlotB_spec hns) hF
    (noCondB_spec hnc) hfr' "" _ _ rfl rfl (ImageAddrRoute.entryA σ sa) false hrel rfl
    (fun R' hR => by
      have hl : (ImageAddrRoute.entryA σ sa).reg.lvm R'
          = ⟨64, sa.regs (DecodePrinted.phys R')⟩ := by
        simp only [ImageAddrRoute.entryA, hR, if_true]
      unfold JasminLsemWidthN.LstateN.getW
      rw [hl]
      simp) rfl _ hrunB hok
  refine ⟨prog, sa', hdec, hh, fun r hr hgp hfm => ?_⟩
  rw [← getW_congr 64 (hagB r hr)]
  exact hobs r hr hgp (by simp only [frameC, hgpN r hgp]; exact frameE_none sa hfm)

/-! ## 3. A register-returning program through the cell route -/

/-- **The gate of a register-returning straight-line program over the printed class with
    carry chains.** For a program returning a `64`-bit register: the stack-memory fragment
    `scalarMemNB`; the result of `σ` the register `RA`, whose export name `nm RA` is a
    general-purpose register with machine register `RA` and no frame mark; the cell names
    of `σ` checked against `body`; and the cell fold, from the empty constant environment,
    of the chain `straightOpsMem` followed by the copy of its return name into `nm RA`,
    some chain `C2` that passes the cell route `cellRouteB` against `body` with `nm RA`
    observed, at the fusion flag `fuse`. -/
def straightRegWB (σ : AbiLayout) (nm : String → String) (body : Lcmd) (fuse : Bool) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | Γ, .reg w, com =>
      let ch := straightOpsMem Γ.length com Γ.length
      let ret := comRetReg Γ.length argName com Γ.length
      scalarMemNB com && w == 64
        && (match σ.result with
          | .reg RA => gpOk (nm RA) && phys (nm RA) == RA
              && (frameMark (frameNames body) (nm RA)).isNone
              && cellNamesOkB σ body
              && (match cellFold (cellArrs σ) []
                  (ch ++ JasminLsemRenameLoop.movesOf [(ret, nm RA)]) with
                | some C2 => cellRouteB σ nm body [nm RA] C2 fuse
                | none => false)
          | _ => false)
  | _, _, _ => false

/-- A program accepted by `straightRegWB` returns a `64`-bit register. -/
theorem straightRegWB_ty {σ : AbiLayout} {nm : String → String} {body : Lcmd} {fuse : Bool}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {c : Com jasminDialect Γ t}
    (h : straightRegWB σ nm body fuse c = true) : t = .reg 64 := by
  unfold straightRegWB at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.2]
  · cases h

/-- **A register-returning straight-line program at the bytes, over the printed class with
    carry chains.** For a program returning a `64`-bit register that passes `straightRegWB`
    against the printed body `body`: from every entry state `sa` satisfying `σ.Regions`, at
    every valuation `V` the layout reads off `sa` (`AbiValOf`), the decoded bytes of `body`
    halt in a state from which `σ` reads back the program's denotation. -/
theorem straightRegW_bytes {σ : AbiLayout} {nm : String → String} {body : Lcmd} {fuse : Bool}
    {Γ : Ctxt jasminDialect} (com : Com jasminDialect Γ (.reg 64))
    (hg : straightRegWB σ nm body fuse com = true) (sa : AState) (V : Ctxt.Valuation Γ)
    (hV : AbiValOf σ sa V) (hreg : σ.Regions sa) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (.int (com.denote V).toNat) := by
  simp only [straightRegWB, Bool.and_eq_true] at hg
  obtain ⟨⟨hmem, -⟩, hres⟩ := hg
  split at hres
  · rename_i RA hσ
    simp only [Bool.and_eq_true, beq_iff_eq] at hres
    obtain ⟨⟨⟨⟨hgp, hph⟩, hfr⟩, hN⟩, hroute⟩ := hres
    have N := cellNamesOkB_spec hN
    split at hroute
    · rename_i C2 hfold
      have E := entryB_spec (cellRouteB_entryB hroute) sa
      have habi := entryV_abiEntry (un := fun x => x) (sa := sa) E.argF E.argG fun _ _ => rfl
      have hagr := storeAgreesM_lpc σ.args.length (storeAgreesM_of_abi hV habi)
      have hm := scalarMemNB_sound com hmem
      obtain ⟨b, hrun, -, -, hval⟩ :=
        JasminLsemMem.lsemStraightMem_straightOps_full hm rfl rfl le_rfl hagr
      have hpl := JasminLsemMemFlagArrLoop.straightOpsMem_plain Γ.length com
        (JasminLsemMemFlagArrLoop.scalarMemN_comOpsPlain hm) Γ.length
      obtain ⟨c, o, hF⟩ := runStraightF_of_lsemStraightMem _ hpl _ b false hrun
      set ret := comRetReg Γ.length argName com Γ.length with hret
      have hF2 : runStraightF (straightOpsMem Γ.length com Γ.length
            ++ JasminLsemRenameLoop.movesOf [(ret, nm RA)]) (afterArgs σ body sa) false
          = some (JasminLsemRenameLoop.movesState [(ret, nm RA)] { b with cf := c, of := o },
            false) := by
        have hF' : runStraightF (straightOpsMem Γ.length com Γ.length) (afterArgs σ body sa)
            false = some ({ b with cf := c, of := o }, false) := hF
        rw [JasminLsemAddrMem.runStraightF_append, hF', Option.bind_some]
        exact JasminLsemRenameLoop.runStraightF_movesOf _ _ _
      obtain ⟨env', b2, hF3, hCR⟩ :=
        runStraightF_cellFold N.slots N.dist _ [] C2 hfold (cellRel_entry N.dist) hF2
      obtain ⟨prog, sa', hdec, hh, hR⟩ := cell_route_reg_bytes hroute hN sa hreg b2 false hF3
      refine ⟨prog, sa', hdec, hh, ?_⟩
      have hcell : isCellB (cellArrs σ) (nm RA) = false := by
        rw [isCellB_eq]
        cases hc : cellIdx (cellArrs σ) (nm RA) with
        | none => rfl
        | some _ =>
            have := N.gp (nm RA) (by rw [hc]; rfl)
            rw [hgp] at this
            cases this
      have h0 : b.reg.getW ret 64 = some (com.denote V) := by
        simpa only [JasminLsemWidthN.evalOperandN] using hval
      have hv : b2.reg.getW (nm RA) 64 = some (com.denote V) := by
        rw [getW_congr 64 (hCR.reg (nm RA) hcell), ← h0]
        unfold JasminLsemWidthN.LstateN.getW
        rw [movesState_single_lvm]
      have hR' := hR (nm RA) (List.mem_singleton_self _) hgp hfr
      rw [hv, hph] at hR'
      have hx := Option.some.inj hR'
      unfold AbiLayout.ResultOf
      rw [hσ]
      simp only [Haxc.ResultKind.read, hx]
    · cases hroute
  · cases hres

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRegW
