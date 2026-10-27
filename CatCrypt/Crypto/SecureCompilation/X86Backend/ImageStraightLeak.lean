/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageRouteCT

@[expose] public section

set_option autoImplicit false

/-!
# Constant time of the decoded bytes of the straight register route from the source

The straight image routes of `ImageStraightRoute` compile a straight-line program through the
virtual body `argBind σ nm ++ C`: the copies of the parameter registers followed by a chain
`C` of `Lopn`s. The register allocation checker compares the virtual body with the image
`virtImg` of the printed body. This module follows the events `instrLeakF` of the traced flag
machine along that chain of comparisons, for the route of a program returning a register
(`straightRegB`), in which `C` is the chain `straightOpsMem` of the program followed by the
copy of its return name into the export register of the result.

The copies emit no event, so the trace of the virtual body is the trace `straightLeakFF` of
`C` from the state behind the copies. For the register route this is `straightT` of the
source events `Com.ctLeak` of the program at the valuation the layout reads off the entry
state. Constant time of the source gives constant time of the virtual body, the checker on
traced runs `ownedCheckML` gives constant time of the image, and
`DecodePrintedAddrLeak.image_bytes_ct` gives constant time of the decoded bytes of a printed
body without a conditional branch.

Sections 1 to 3 hold for every chain `C` and every list of observed registers, and so for
the array route `straightArrB`, whose check `straightRouteB` is `straightRouteOutB` at no
observed register.

## Main definitions

* `StraightPub`: two entry machine states of a straight route under a layout `σ` and labels
  `L`: the valuations `σ` reads off them agree on the positions `L` marks public, both
  satisfy `σ.Regions`, the stack registers are equal and the registers of the array
  parameters are equal. The contents of the arrays are unconstrained.
* `StraightEntryPub`: two flag-machine states that are the entries `ent sa₁` and `ent sa₂`
  of machine states related by `StraightPub`, for an entry map `ent` of the route.
* `straightEntry`: the entry map of the routes whose virtual body runs from `entryV` at the
  frame of the printed body.
* `regChain`: the chain of a register-returning program followed by the copy of its return
  name into a register.
* `straightRegLB`: the check on traced runs of the register route, `ownedCheckML` on the
  pair that `straightRegB` compares with `ownedCheckMC`.

## Main results

* `fRun_of_runStraightF`: a chain of `Lopn`s has a terminating traced run with trace
  `straightLeakFF`.
* `straightVirt_leak`, `straightVirt_checked_run`: the trace, and a halting checked run, of
  the virtual body of a chain that runs from the state behind the copies.
* `straight_imgBytePub`: machine states related by `StraightPub` are related by `ImgBytePub`
  at the frame address and the array bases of the first, through the entries of the virtual
  body.
* `straight_bytes_ct`: constant time of the decoded bytes of a printed body without a
  conditional branch from constant time of the virtual body, for every chain.
* `straightReg_leak`, `straightReg_memFCT`: the trace of the virtual body of the register
  route from the source events, and its constant time from the source.
* `straightReg_image_memFCT`: constant time of the image of the printed body of the register
  route.
* `straightReg_bytes_ct`: constant time of the decoded bytes of the register route between
  entry states related by `StraightPub`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF lsemFuelMemF
  PlainLopnBody)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (lsemFuelMemFk
  lsemFuelMemFk_of_runIdxOk)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF
  runStraightF_lpc runStraightF_of_lsemStraightMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop (straightOpsMem_plain
  scalarMemN_comOpsPlain)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (movesOf movesOf_isLopn
  movesState runStraightF_movesOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop (straightLeakFF
  straightLeakFF_append straightLeakFF_quiet straightLeakFF_plain lsemFuelMemFLeak_segF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (physImgB virtImg)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (scalarMemNB
  scalarMemNB_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf AbiEntryM
  storeAgreesM_of_abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (argBind slotArrOf slotRen
  entryA entryV entryB entryB_spec argBind_entryV boundFacts_entryV imgRel_entryV entryB_save
  imgSep_slotRen frameE entryV_abiEntry slotArrOf_some slotRen_some abiBase_argName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (movesOf_quiet)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameIn imgGateB_frameMark
  imgSep_of_regions)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (ImgSep ImgRel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (NoCond)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (afterArgs
  straightRouteOutB straightRegB straightRegB_ty storeAgreesM_lpc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (idxInvCheckB idxAnnot boundFacts
  runIdxOk_of_idxInvCheckB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMC
  ownedCheckMC_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak (ownedCheckML TVPub
  memFCT_of_ownedCheckML ownedCheckMC_of_ownedCheckML)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (ImgBytePub Entry
  image_bytes_ct)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiBase abiReg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime ConstantTimeRel)

/-! ## 1. The entry relation of a straight route -/

/-- **Public-equal entry machine states of a straight route** under the layout `σ` and the
    labels `L`: the valuations `σ` reads off the two states agree on the positions `L` marks
    public; both states satisfy `σ.Regions`; the stack registers are equal; the register of
    every array parameter, its base address, is equal. The words of the arrays and the
    scalar parameters `L` marks secret are unconstrained. -/
def StraightPub (σ : AbiLayout) {Γ : Ctxt jasminDialect} (L : Labels Γ) (sa₁ sa₂ : AState) :
    Prop :=
  ∃ V₁ V₂ : Ctxt.Valuation Γ, AbiValOf σ sa₁ V₁ ∧ AbiValOf σ sa₂ V₂ ∧ PubEqV L V₁ V₂
    ∧ σ.Regions sa₁ ∧ σ.Regions sa₂ ∧ sa₁.regs "%rsp" = sa₂.regs "%rsp"
    ∧ ∀ a ∈ σ.args, ∀ n, a.kind = .words n → sa₁.regs a.reg = sa₂.regs a.reg

/-- **Public-equal entry states of the virtual body of a straight route**: the entries
    `ent sa₁` and `ent sa₂` of two machine states related by `StraightPub`. The entry map
    `ent` is the one of the route: `straightEntry` for the routes whose virtual body runs
    from `entryV` at the frame of the printed body. -/
def StraightEntryPub (σ : AbiLayout) {Γ : Ctxt jasminDialect} (L : Labels Γ)
    (ent : AState → LstateMF) (s₁ s₂ : LstateMF) : Prop :=
  ∃ sa₁ sa₂ : AState, StraightPub σ L sa₁ sa₂ ∧ s₁ = ent sa₁ ∧ s₂ = ent sa₂

/-- `StraightPub` from agreement on the public data of the layout: valuations that agree on
    the public labels, the separation of both states, and equal stack and array-parameter
    registers. -/
theorem StraightPub.intro {σ : AbiLayout} {Γ : Ctxt jasminDialect} {L : Labels Γ}
    {sa₁ sa₂ : AState} {V₁ V₂ : Ctxt.Valuation Γ} (h₁ : AbiValOf σ sa₁ V₁)
    (h₂ : AbiValOf σ sa₂ V₂) (hp : PubEqV L V₁ V₂) (hr₁ : σ.Regions sa₁) (hr₂ : σ.Regions sa₂)
    (hrsp : sa₁.regs "%rsp" = sa₂.regs "%rsp")
    (harr : ∀ a ∈ σ.args, ∀ n, a.kind = .words n → sa₁.regs a.reg = sa₂.regs a.reg) :
    StraightPub σ L sa₁ sa₂ :=
  ⟨V₁, V₂, h₁, h₂, hp, hr₁, hr₂, hrsp, harr⟩

/-- The entries of two machine states related by `StraightPub` are related by
    `StraightEntryPub`. -/
theorem straightEntryPub_of_pub {σ : AbiLayout} {Γ : Ctxt jasminDialect} {L : Labels Γ}
    (ent : AState → LstateMF) {sa₁ sa₂ : AState} (h : StraightPub σ L sa₁ sa₂) :
    StraightEntryPub σ L ent (ent sa₁) (ent sa₂) :=
  ⟨sa₁, sa₂, h, rfl, rfl⟩

/-- The flag-machine entry state of the virtual body of a straight route at the machine
    state `sa`: the base `entryV` at the frame of the printed body `body` and the identity
    name map, the function `fn`, the zero flag clear. -/
abbrev straightEntry (σ : AbiLayout) (body : Lcmd) (fn : String) (sa : AState) : LstateMF :=
  { prog := { base := entryV σ (frameE body sa) sa fun x => x, lfn := fn }, zf := false }

/-! ## 2. The virtual body of a chain -/

/-- **A chain of `Lopn`s on the traced flag machine.** A chain that the extended fold
    `runStraightF` runs from program counter `0` has a terminating traced run in its
    singleton program with trace `straightLeakFF`. -/
theorem fRun_of_runStraightF (fn : String) (seg : List LinstrRM) (hl : ∀ i ∈ seg, IsLopn i)
    (b0 : LstateM) (zf : Bool) (bz : LstateM × Bool) (hpc : b0.lpc = 0)
    (hrun : runStraightF seg b0 zf = some bz) :
    FRun (singletonProgM fn seg) { prog := { base := b0, lfn := fn }, zf := zf }
      (straightLeakFF seg b0 zf) := by
  have h := lsemFuelMemFLeak_segF (singletonProgM fn seg) fn rfl seg b0 zf 0 bz hl
    (fun k _ => by rw [hpc, Nat.zero_add]; rfl) hrun
  have hlpc : bz.1.lpc = seg.length := by
    rw [runStraightF_lpc seg b0 zf bz.1 bz.2 hrun, hpc, Nat.zero_add]
  have hhalt : JasminLsemMemLoop.findInstrMem (singletonProgM fn seg)
      { base := bz.1, lfn := fn } = none := by
    show (if fn = fn then seg[bz.1.lpc]? else none) = none
    rw [ite_eq_left rfl, hlpc]
    exact List.getElem?_eq_none (le_refl _)
  rw [lsemFuelMemFLeak_halt _ 0 { prog := { base := bz.1, lfn := fn }, zf := bz.2 } hhalt] at h
  refine ⟨seg.length + 0, { prog := { base := bz.1, lfn := fn }, zf := bz.2 }, ?_⟩
  rw [h]
  simp

/-- **The trace of the virtual body of a chain.** Let the printed body pass the entry check
    and the chain `C` of `Lopn`s run from the state `afterArgs` behind the copies of the
    parameter registers. At a machine state with the stack parameters at entry, every
    terminating traced run of the virtual body `argBind σ nm ++ C` from `straightEntry` emits
    the events `straightLeakFF` of `C` from `afterArgs`. -/
theorem straightVirt_leak {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    (hent : entryB σ nm body = true) {C : List LinstrRM} (hC : ∀ i ∈ C, IsLopn i)
    (sa : AState) (hst : σ.StackIn sa) (fn : String) {bz : LstateM × Bool}
    (hrun : runStraightF C (afterArgs σ body sa) false = some bz) {ℓ : List CTLeak}
    (hr : FRun (singletonProgM fn (argBind σ nm ++ C)) (straightEntry σ body fn sa) ℓ) :
    ℓ = straightLeakFF C (afterArgs σ body sa) false := by
  have E := entryB_spec hent sa
  have hpr0 := argBind_entryV (nm := nm) (sa := sa) (fr := frameE body sa)
    (un := fun x => x) E.argF E.argG (E.argSrc hst) false
  have hB : runStraightF (argBind σ nm ++ C) (entryV σ (frameE body sa) sa fun x => x) false
      = some bz := by
    rw [JasminLsemAddrMem.runStraightF_append, hpr0, Option.bind_some]
    exact hrun
  have hl : ∀ i ∈ argBind σ nm ++ C, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact movesOf_isLopn _ i hi
    · exact hC i hi
  have hq : ∀ i ∈ argBind σ nm, ∀ r, instrLeakB r i = [] := movesOf_quiet _
  rw [fRun_unique hr (fRun_of_runStraightF fn _ hl _ false bz rfl hB),
    straightLeakFF_append _ _ _ _ _ hpr0, straightLeakFF_quiet _ hq, List.nil_append]
  rfl

/-- **The virtual body of a chain halts on checked runs.** Let the virtual body
    `argBind σ nm ++ C` pass the bounds invariant, the printed body pass the entry check, and
    the chain `C` of `Lopn`s run from the state `afterArgs`. From the entry of every machine
    state that satisfies `σ.Regions`, the virtual body has a halting checked run. -/
theorem straightVirt_checked_run {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {C : List LinstrRM}
    (hidx : idxInvCheckB (boundFacts σ nm) (idxAnnot (boundFacts σ nm) (argBind σ nm ++ C))
      (argBind σ nm ++ C) = true)
    (hent : entryB σ nm body = true) (hC : ∀ i ∈ C, IsLopn i) (sa : AState)
    (hreg : σ.Regions sa) (fn : String) {bz : LstateM × Bool}
    (hrun : runStraightF C (afterArgs σ body sa) false = some bz) :
    ∃ f t, lsemFuelMemFk true (singletonProgM fn (argBind σ nm ++ C)) f
      (straightEntry σ body fn sa) = some t := by
  have E := entryB_spec hent sa
  have hpr0 := argBind_entryV (nm := nm) (sa := sa) (fr := frameE body sa)
    (un := fun x => x) E.argF E.argG (E.argSrc hreg.stackIn) false
  have hB : runStraightF (argBind σ nm ++ C) (entryV σ (frameE body sa) sa fun x => x) false
      = some (bz.1, bz.2) := by
    rw [JasminLsemAddrMem.runStraightF_append, hpr0, Option.bind_some]
    exact hrun
  have hl : ∀ i ∈ argBind σ nm ++ C, IsLopn i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact movesOf_isLopn _ i hi
    · exact hC i hi
  have hrun' := ImageStraightRoute.lsemFuelMemF_of_runStraightF fn _ hl _ bz.1 false bz.2
    rfl hB
  have hents := boundFacts_entryV (nm := nm) (fr := frameE body sa) (un := fun x => x)
    hreg E.bnds
  have hok := runIdxOk_of_idxInvCheckB hidx fn _ _ rfl rfl (hents _) _ hrun'
  exact ⟨_, _, lsemFuelMemFk_of_runIdxOk true _ _ _ _ hrun' hok⟩

/-! ## 3. From the virtual body to the decoded bytes -/

/-- The relation of the image simulation at array bases that agree on the arrays of the slot
    map. -/
theorem imgRel_of_base_eq {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base base' : String → BitVec 64} {body : Lcmd}
    {s : LstateMF} {sa : JasminLsemAddrMem.LstateA} {zf : Bool}
    (h : ∀ q A n, slotArr q = some (A, n) → base A = base' A)
    (hr : ImgRel frame slotArr base body s sa zf) : ImgRel frame slotArr base' body s sa zf :=
  ⟨hr.pc, hr.regs, hr.slots, hr.zf, hr.cf, hr.of, hr.wid,
    fun q A n hq => by rw [← h q A n hq]; exact hr.cells q A n hq,
    fun k R A n a hs hq hf => by rw [← h _ A n hq]; exact hr.saved k R A n a hs hq hf,
    hr.reload, fun R A n a hR hq hf => by rw [← h _ A n hq]; exact hr.held R A n a hR hq hf⟩

/-- **The entry bridge of a straight route.** Let the printed body `body` and the chain `C`
    pass `straightRouteOutB` with the observed registers `outs`, and let the virtual body
    have a halting checked run from the entry of every machine state that satisfies
    `σ.Regions` and has a valuation. Two machine states related by `StraightPub` are then
    related by `ImgBytePub`, at the frame address and the array bases of the first state,
    through the entries `straightEntry` of the virtual body (`TVPub` over
    `StraightEntryPub`), and the slot map is separated at that frame. -/
theorem straight_imgBytePub {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {outs : List String} {C : List LinstrRM} {Γ : Ctxt jasminDialect} {L : Labels Γ}
    (hroute : straightRouteOutB σ nm body outs C = true) (fn : String)
    (hck : ∀ (sa : AState) (V : Ctxt.Valuation Γ), σ.Regions sa → AbiValOf σ sa V →
      ∃ f t, lsemFuelMemFk true (singletonProgM fn (argBind σ nm ++ C)) f
        (straightEntry σ body fn sa) = some t)
    {sa₁ sa₂ : AState} (hpub : StraightPub σ L sa₁ sa₂) :
    ImgSep (frameIn body (frameP (Params.ofBody body) (frameRsp body sa₁)))
        (slotRen (slotArrOf σ nm) fun x => x) (fun A => abiBase (abiReg σ) sa₁ A)
        (frameRsp body sa₁)
      ∧ ImgBytePub (frameRsp body sa₁) (slotRen (slotArrOf σ nm) fun x => x)
        (fun A => abiBase (abiReg σ) sa₁ A) body fn
        (TVPub fn (argBind σ nm ++ C) (StraightEntryPub σ L (straightEntry σ body fn)))
        sa₁ sa₂ := by
  have hg' := hroute
  simp only [straightRouteOutB, Bool.and_eq_true] at hg'
  obtain ⟨⟨⟨⟨⟨⟨hck0, -⟩, -⟩, -⟩, -⟩, hfr⟩, hent⟩ := hg'
  have hpub' := hpub
  obtain ⟨V₁, V₂, hV₁, hV₂, -, hreg₁, hreg₂, hrspE, hbases⟩ := hpub'
  have E₁ := entryB_spec hent sa₁
  have E₂ := entryB_spec hent sa₂
  have hrsp : frameRsp body sa₂ = frameRsp body sa₁ := by
    unfold frameRsp
    rw [hrspE]
  have hfrE : frameE body sa₂ = frameE body sa₁ := by
    unfold frameE
    rw [hrsp]
  have hsep := imgSep_slotRen (ren := fun x => x) (un := fun x => x)
    (imgSep_of_regions E₁.rs hreg₁ hfr E₁.len E₁.slot ImageAddrRoute.slotArrOf_not_fa)
      fun _ _ _ _ => rfl
  have hk₁ := hck sa₁ V₁ hreg₁ hV₁
  have hk₂ := hck sa₂ V₂ hreg₂ hV₂
  have himg : ∀ sa, (∃ f t, lsemFuelMemFk true (singletonProgM fn (argBind σ nm ++ C)) f
        (straightEntry σ body fn sa) = some t) →
      ∃ f t, lsemFuelMemFk true (singletonProgM fn
        (virtImg (slotRen (slotArrOf σ nm) fun x => x) body)) f
        (straightEntry σ body fn sa) = some t := by
    rintro sa ⟨f, t, hk⟩
    obtain ⟨f', t', hr', -⟩ := ownedCheckMC_sound hck0 fn _ t rfl rfl f hk
    exact ⟨f', t', hr'⟩
  have hentA : ∀ sa : AState, Entry sa (entryA σ sa) := fun sa =>
    ⟨rfl, fun R hR => by
      have hl : (entryA σ sa).reg.lvm R = ⟨64, sa.regs (phys R)⟩ := by
        simp only [entryA, hR, ite_true]
      unfold JasminLsemWidthN.LstateN.getW
      rw [hl]
      simp, rfl⟩
  have hrel₁ := imgRel_entryV (σ := σ) (nm := nm) (fr := frameE body sa₁)
    (sa := sa₁) (body := body) (fn := fn) (ren := fun x => x) (un := fun x => x)
    (E₁.argSrc hreg₁.stackIn) (fun _ _ hs => entryB_save hent hs) (fun _ _ => rfl)
  have hrel₂ := imgRel_entryV (σ := σ) (nm := nm) (fr := frameE body sa₂)
    (sa := sa₂) (body := body) (fn := fn) (ren := fun x => x) (un := fun x => x)
    (E₂.argSrc hreg₂.stackIn) (fun _ _ hs => entryB_save hent hs) (fun _ _ => rfl)
  have hbase : ∀ q A n, slotRen (slotArrOf σ nm) (fun x => x) q = some (A, n) →
      abiBase (abiReg σ) sa₂ A = abiBase (abiReg σ) sa₁ A := by
    intro q A n hq
    obtain ⟨A0, hA0, rfl⟩ := slotRen_some hq
    obtain ⟨j, a0, hj, hkind, rfl, -⟩ := slotArrOf_some hA0
    rw [abiBase_argName hj, abiBase_argName hj]
    exact (hbases a0 (List.mem_of_getElem? hj) n hkind).symm
  have hrel₂' := imgRel_of_base_eq hbase hrel₂
  refine ⟨hsep, rfl, hrsp, (entryA σ sa₁, false), (entryA σ sa₂, false),
    ⟨straightEntry σ body fn sa₁, straightEntry σ body fn sa₂, ?_, rfl, rfl, rfl, hrel₁, ?_,
      himg sa₁ hk₁, himg sa₂ hk₂⟩, hentA sa₁, hentA sa₂⟩
  · exact ⟨straightEntryPub_of_pub _ hpub, rfl, rfl, rfl, rfl, hk₁, hk₂⟩
  · have key : ∀ fr : String → Option (BitVec 64), fr = frameE body sa₁ →
        ImgRel fr (slotRen (slotArrOf σ nm) fun x => x)
          (fun A => abiBase (abiReg σ) sa₁ A) body
          (straightEntry σ body fn sa₂) (entryA σ sa₂) false →
        ImgRel (frameE body sa₁) (slotRen (slotArrOf σ nm) fun x => x)
          (fun A => abiBase (abiReg σ) sa₁ A) body
          (straightEntry σ body fn sa₂) (entryA σ sa₂) false := by
      rintro _ rfl h
      exact h
    exact key _ hfrE hrel₂'

/-- **Constant time of the decoded bytes of a straight route from its virtual body.** Let the
    printed body `body`, without a conditional branch, and the chain `C` pass
    `straightRouteOutB` with the observed registers `outs`, and let the checker on traced
    runs `ownedCheckML` accept the virtual body against the image of `body`. If the virtual
    body is constant time on the flag machine between the entries of machine states related
    by `StraightPub`, and has a halting checked run from the entry of every machine state
    that satisfies `σ.Regions` and has a valuation, then every decoding of the function
    bytes of `body` is constant time under the regime `doitm` and any side condition between
    machine states related by `StraightPub`. -/
theorem straight_bytes_ct {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {outs : List String} {C : List LinstrRM} {Γ : Ctxt jasminDialect} {L : Labels Γ}
    (hroute : straightRouteOutB σ nm body outs C = true)
    (hlk : ownedCheckML outs (argBind σ nm ++ C)
      (virtImg (slotRen (slotArrOf σ nm) fun x => x) body) = true)
    (hnc : NoCond body) (fn : String)
    (hct : MemFCT (singletonProgM fn (argBind σ nm ++ C))
      (StraightEntryPub σ L (straightEntry σ body fn)))
    (hck : ∀ (sa : AState) (V : Ctxt.Valuation Γ), σ.Regions sa → AbiValOf σ sa V →
      ∃ f t, lsemFuelMemFk true (singletonProgM fn (argBind σ nm ++ C)) f
        (straightEntry σ body fn sa) = some t)
    (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (StraightPub σ L) (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  have hg' := hroute
  simp only [straightRouteOutB, Bool.and_eq_true] at hg'
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hpr⟩, hphys⟩, hgate⟩, -⟩, -⟩ := hg'
  rintro sa₁ sa₂ u₁ u₂ hpub hb₁ hb₂
  obtain ⟨hsep, hbp⟩ := straight_imgBytePub hroute fn hck hpub
  have hgate' : ImageAddrSim.imgGateB
      (frameIn body (frameP (Params.ofBody body) (frameRsp body sa₁)))
      (slotRen (slotArrOf σ nm) fun x => x) body = true := by
    rw [imgGateB_frameMark]
    exact hgate
  exact image_bytes_ct hpr hphys hgate' hsep hnc fn (memFCT_of_ownedCheckML hlk fn hct) ok hdec
    sa₁ sa₂ u₁ u₂ hbp hb₁ hb₂

/-! ## 4. The register route -/

/-- The chain of a register-returning program followed by the copy of its return name into
    the register `R`: the chain of the virtual body of `straightRegB` at `R` the export name
    of the result register. -/
def regChain (R : String) {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t) :
    List LinstrRM :=
  straightOpsMem Γ.length com Γ.length
    ++ movesOf [(comRetReg Γ.length argName com Γ.length, R)]

/-- The conjuncts of `straightRegB` at a layout whose result is the register `RA`: the
    stack-memory fragment and the route check of `regChain`. -/
theorem straightRegB_spec {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {com : Com jasminDialect Γ t}
    (hg : straightRegB σ nm body com = true) {RA : String} (hσ : σ.result = .reg RA) :
    scalarMemNB com = true
      ∧ straightRouteOutB σ nm body [nm RA] (regChain (nm RA) com) = true := by
  obtain rfl := straightRegB_ty hg
  simp only [straightRegB, Bool.and_eq_true, hσ] at hg
  exact ⟨hg.1.1, hg.2.2⟩

/-- **The chain of the register route from the state behind the copies.** For a program in
    the stack-memory fragment and a printed body that passes the entry check, at every
    valuation `V` the layout reads off the machine state `sa`: the chain `regChain` is a
    chain of `Lopn`s, runs from `afterArgs`, and emits `straightT` of the source events of
    the program at `V`. -/
theorem regChain_run (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {Γ : Ctxt jasminDialect} {w : Nat} (com : Com jasminDialect Γ (.reg w))
    (hmem : scalarMemNB com = true) (hent : entryB σ nm body = true) (R : String)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) :
    (∀ i ∈ regChain R com, IsLopn i)
      ∧ (∃ bz, runStraightF (regChain R com) (afterArgs σ body sa) false = some bz)
      ∧ straightLeakFF (regChain R com) (afterArgs σ body sa) false
        = straightT Pj Γ.length com Γ.length (Com.ctLeak (jLeakModel Pj) com V) := by
  have E := entryB_spec hent sa
  have habi := entryV_abiEntry (un := fun x => x) (sa := sa) E.argF E.argG fun _ _ => rfl
  have hagr : StoreAgreesM Γ.length Γ.length (afterArgs σ body sa) V :=
    storeAgreesM_lpc σ.args.length (storeAgreesM_of_abi hV habi)
  have hm := scalarMemNB_sound com hmem
  obtain ⟨b, hrun, -⟩ := lsemStraightMem_straightOps_full hm rfl rfl le_rfl hagr
  have hpl := straightOpsMem_plain Γ.length com (scalarMemN_comOpsPlain hm) Γ.length
  obtain ⟨c, o, hF⟩ := runStraightF_of_lsemStraightMem _ hpl _ b false hrun
  have hlk : straightLeakFF (straightOpsMem Γ.length com Γ.length) (afterArgs σ body sa) false
      = straightLeakF (straightOpsMem Γ.length com Γ.length) (afterArgs σ body sa) :=
    straightLeakFF_plain _ hpl (afterArgs σ body sa) b (afterArgs σ body sa).cf
      (afterArgs σ body sa).of false hrun
  refine ⟨fun i hi => ?_, ⟨(movesState [(comRetReg Γ.length argName com Γ.length, R)]
    { b with cf := c, of := o }, false), ?_⟩, ?_⟩
  · rcases List.mem_append.mp hi with hi | hi
    · exact (hpl i hi).1
    · exact movesOf_isLopn _ i hi
  · unfold regChain
    rw [JasminLsemAddrMem.runStraightF_append, hF, Option.bind_some]
    exact runStraightF_movesOf _ _ _
  · unfold regChain
    rw [straightLeakFF_append _ _ _ _ _ hF, straightLeakFF_quiet _ (movesOf_quiet _),
      List.append_nil, hlk]
    exact straightLeakF_straightOps Pj hm rfl le_rfl hagr

/-- **The trace of the virtual body of the register route from the source events.** For a
    program that passes `straightRegB` against the printed body `body`, at a layout whose
    result is the register `RA`: every terminating traced run of the virtual body from
    `straightEntry` at a machine state `sa` with the stack parameters at entry emits
    `straightT` of the source events of the program at the valuation `σ` reads off `sa`. -/
theorem straightReg_leak (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hg : straightRegB σ nm body com = true) {RA : String} (hσ : σ.result = .reg RA)
    (sa : AState) (hst : σ.StackIn sa) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V)
    (fn : String) {ℓ : List CTLeak}
    (hr : FRun (singletonProgM fn (argBind σ nm ++ regChain (nm RA) com))
      (straightEntry σ body fn sa) ℓ) :
    ℓ = straightT Pj Γ.length com Γ.length (Com.ctLeak (jLeakModel Pj) com V) := by
  obtain ⟨hmem, hroute⟩ := straightRegB_spec hg hσ
  obtain rfl := straightRegB_ty hg
  simp only [straightRouteOutB, Bool.and_eq_true] at hroute
  obtain ⟨hC, ⟨bz, hrun⟩, hT⟩ := regChain_run Pj com hmem hroute.2 (nm RA) sa V hV
  rw [straightVirt_leak hroute.2 hC sa hst fn hrun hr, hT]

/-- **Constant time of the virtual body of the register route from the source.** For a
    program that passes `straightRegB` against the printed body `body`, at a layout whose
    result is the register `RA`: if the source events of the program are constant time for
    the labels `L`, the virtual body is constant time on the flag machine between the
    entries `straightEntry` of machine states related by `StraightPub`. -/
theorem straightReg_memFCT (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hg : straightRegB σ nm body com = true) {RA : String} (hσ : σ.result = .reg RA)
    (L : Labels Γ) (fn : String)
    (hct : ConstantTime (PubEqV L) (Com.ctLeak (jLeakModel Pj) com)) :
    MemFCT (singletonProgM fn (argBind σ nm ++ regChain (nm RA) com))
      (StraightEntryPub σ L (straightEntry σ body fn)) := by
  rintro s₁ s₂ ℓ₁ ℓ₂ ⟨sa₁, sa₂, ⟨V₁, V₂, hV₁, hV₂, hp, hr₁, hr₂, -⟩, rfl, rfl⟩ r₁ r₂
  rw [straightReg_leak Pj com hg hσ sa₁ hr₁.stackIn V₁ hV₁ fn r₁,
    straightReg_leak Pj com hg hσ sa₂ hr₂.stackIn V₂ hV₂ fn r₂, hct V₁ V₂ hp]

/-- **The virtual body of the register route halts on checked runs** from the entry of every
    machine state that satisfies `σ.Regions` and has a valuation. -/
theorem straightReg_checked_run {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hg : straightRegB σ nm body com = true) {RA : String} (hσ : σ.result = .reg RA)
    (fn : String) (sa : AState) (V : Ctxt.Valuation Γ) (hreg : σ.Regions sa)
    (hV : AbiValOf σ sa V) :
    ∃ f t, lsemFuelMemFk true (singletonProgM fn (argBind σ nm ++ regChain (nm RA) com)) f
      (straightEntry σ body fn sa) = some t := by
  obtain ⟨hmem, hroute⟩ := straightRegB_spec hg hσ
  obtain rfl := straightRegB_ty hg
  simp only [straightRouteOutB, Bool.and_eq_true] at hroute
  obtain ⟨hC, ⟨bz, hrun⟩, -⟩ :=
    regChain_run JLeakParams.owned com hmem hroute.2 (nm RA) sa V hV
  exact straightVirt_checked_run hroute.1.1.1.1.1.2 hroute.2 hC sa hreg fn hrun

/-- **The check on traced runs of the register route**: on a program returning a register,
    at a layout whose result is a register `RA`, `ownedCheckML` observing `nm RA` on the
    virtual body and the image of the printed body `body` that `straightRegB` compares with
    `ownedCheckMC`; `false` otherwise. -/
def straightRegLB (σ : AbiLayout) (nm : String → String) (body : Lcmd) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | _, .reg _, com =>
      match σ.result with
      | .reg RA => ownedCheckML [nm RA] (argBind σ nm ++ regChain (nm RA) com)
          (virtImg (slotRen (slotArrOf σ nm) fun x => x) body)
      | _ => false
  | _, _, _ => false

/-- A program accepted by `straightRegLB` at a layout whose result is the register `RA`
    passes `ownedCheckML` observing `nm RA`. -/
theorem straightRegLB_spec {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {Γ : Ctxt jasminDialect} {w : Nat} {com : Com jasminDialect Γ (.reg w)}
    (h : straightRegLB σ nm body com = true) {RA : String} (hσ : σ.result = .reg RA) :
    ownedCheckML [nm RA] (argBind σ nm ++ regChain (nm RA) com)
      (virtImg (slotRen (slotArrOf σ nm) fun x => x) body) = true := by
  simpa only [straightRegLB, hσ] using h

/-- **Constant time of the image of the printed body of the register route.** For a program
    that passes `straightRegB` and the check on traced runs `straightRegLB` against the
    printed body `body`, with source events constant time for the labels `L`: the image of
    `body` is constant time on the flag machine between entries of the virtual body,
    public-equal by `StraightEntryPub`, at pc `0` and with halting checked runs (`TVPub`). -/
theorem straightReg_image_memFCT (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hg : straightRegB σ nm body com = true) (hlk : straightRegLB σ nm body com = true)
    {RA : String} (hσ : σ.result = .reg RA) (L : Labels Γ) (fn : String)
    (hct : ConstantTime (PubEqV L) (Com.ctLeak (jLeakModel Pj) com)) :
    MemFCT (singletonProgM fn (virtImg (slotRen (slotArrOf σ nm) fun x => x) body))
      (TVPub fn (argBind σ nm ++ regChain (nm RA) com)
        (StraightEntryPub σ L (straightEntry σ body fn))) := by
  have hm := straightReg_memFCT Pj com hg hσ L fn hct
  obtain rfl := straightRegB_ty hg
  exact memFCT_of_ownedCheckML (straightRegLB_spec hlk hσ) fn hm

/-- **Constant time of the decoded bytes of the register route from the source.** Let the
    register-returning program `com` pass the gate `straightRegB` and the check on traced
    runs `straightRegLB` against the printed body `body`, which has no conditional branch,
    at a layout whose result is the register `RA`. If the source events of `com` are constant
    time for the labels `L`, every decoding of the function bytes of `body` is constant time
    under the regime `doitm` and any side condition between entry machine states related by
    `StraightPub`: valuations that agree on the public labels, both states separated, equal
    stack registers and equal array-parameter registers. -/
theorem straightReg_bytes_ct (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hg : straightRegB σ nm body com = true) (hlk : straightRegLB σ nm body com = true)
    {RA : String} (hσ : σ.result = .reg RA) (L : Labels Γ)
    (hct : ConstantTime (PubEqV L) (Com.ctLeak (jLeakModel Pj) com))
    (hnc : NoCond body) (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (StraightPub σ L) (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  have hm := straightReg_memFCT Pj com hg hσ L "" hct
  have hk := straightReg_checked_run com hg hσ ""
  obtain ⟨-, hroute⟩ := straightRegB_spec hg hσ
  obtain rfl := straightRegB_ty hg
  exact straight_bytes_ct hroute (straightRegLB_spec hlk hσ) hnc "" hm
    (fun sa V hreg hV => hk sa V hreg hV) ok hdec

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightLeak
