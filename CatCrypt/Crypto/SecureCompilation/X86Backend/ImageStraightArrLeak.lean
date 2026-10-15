/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightLeak

@[expose] public section

set_option autoImplicit false

/-!
# Constant time of the decoded bytes of the straight array route from the source

The gate `straightArrB` of `ImageStraightRoute` compiles a straight-line program returning a
word array through the virtual body `argBind σ nm ++ C`, in which `C` is the coalesced chain
`ch.map (renRM ρ)` of the chain `ch = straightOpsMem` of the program under the alias map
`ρ = chainAlias ch`. The result is written in place to the output parameter: no copy follows
the chain and the route check observes no register.

An address event `CTLeak.addr b k` of the traced flag machine carries the name `b` of the
array and the index value `k`. The coalescing check fixes the index name of every
runtime-indexed access and every name of every other instruction, so the coalesced chain
emits, from a state with the same registers, the events of the chain with array names
renamed by `ρ` (`renEv ρ`). The trace of the virtual body is therefore the image under
`renEv ρ` of `straightT` of the source events `Com.ctLeak` of the program, and constant time
of the source gives constant time of the virtual body. The image and the decoded bytes follow
from the lemmas of `ImageStraightLeak` for an arbitrary chain.

## Main definitions

* `arrChain`: the coalesced chain of an array-returning program, the chain of the virtual
  body of `straightArrB`.
* `straightArrLB`: the check on traced runs of the array route, `ownedCheckML` on the pair
  that `straightArrB` compares with `ownedCheckMC`.

## Main results

* `instrLeakB_coStep`, `straightLeakF_coalesce`: the events of a coalesced instruction and
  of a coalesced chain are the events of the original with renamed array names.
* `straightArr_leak`, `straightArr_memFCT`: the trace of the virtual body of the array route
  from the source events, and its constant time from the source.
* `straightArr_image_memFCT`: constant time of the image of the printed body of the array
  route.
* `straightArr_bytes_ct`: constant time of the decoded bytes of the array route between
  entry states related by `StraightPub`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightArrLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (LstateN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (lsemFuelMemFk)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF
  runStraightF_of_lsemStraightMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop (arrMemN_comOpsPlain
  arrMemN_straightOpsMem_plain)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renOperand renLinstrR renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop (straightLeakFF
  straightLeakFF_plain straightLeakF_straightOps_arr renEv ArrOK instrLeakB_renRM
  straightOpsMem_arrOK)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (virtImg)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (arrMemNB arrMemNB_sound)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf storeAgreesM_of_abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (argBind slotArrOf slotRen
  entryB_spec entryV_abiEntry)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (NoCond)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak (ownedCheckML TVPub
  memFCT_of_ownedCheckML)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime ConstantTimeRel)

/-! ## 1. The events of a coalesced chain -/

/-- The wire of a runtime-indexed load. -/
theorem loadStruct?_wire {w : LinstrR} {p : String × String × String}
    (h : loadStruct? w = some p) :
    ∃ sc, w = .Lopn [.reg p.1] "LOADIDX" [.arrIdx p.2.1 p.2.2 sc] := by
  unfold loadStruct? at h
  split at h
  · split_ifs at h with ho
    cases h
    subst ho
    exact ⟨_, rfl⟩
  · cases h

/-- The wire of a runtime-indexed store. -/
theorem storeStruct?_wire {w : LinstrR} {p : String × String × String × String}
    (h : storeStruct? w = some p) :
    ∃ sc, w = .Lopn [.reg p.1] "STOREIDX" [.arrIdx p.2.1 p.2.2.1 sc, .reg p.2.2.2] := by
  unfold storeStruct? at h
  split at h
  · split_ifs at h with ho
    cases h
    subst ho
    exact ⟨_, rfl⟩
  · cases h

/-- **The events of a coalesced instruction.** An `ArrOK` `Lopn` accepted by `coStepB σ`
    emits, after renaming by `σ` and at the same registers, its events with array names
    renamed by `σ`. -/
theorem instrLeakB_coStep {σ : String → String} {i : LinstrRM} {after : List String}
    (hc : coStepB σ i after = true) (hl : IsLopn i) (hok : ArrOK i.1) (r : LstateN) :
    instrLeakB r (renRM σ i) = (instrLeakB r i).map (renEv σ) := by
  obtain ⟨wire, tag⟩ := i
  have hfix : fixB σ wire = true →
      instrLeakB r (renRM σ (wire, tag)) = (instrLeakB r (wire, tag)).map (renEv σ) := by
    intro hf
    refine instrLeakB_renRM σ r r _ hl hok fun x hx => ?_
    have hx' : x ∈ instrNames wire := by
      obtain ⟨ds, o, ss, hd⟩ := hl
      simp only at hd
      subst hd
      simp only [instrNames, useNames, List.flatMap_append, List.mem_append] at hx ⊢
      exact Or.inr hx
    have h := List.all_eq_true.mp hf x hx'
    rw [show σ x = x from by simpa using h]
  cases tag with
  | reg cd => exact hfix hc
  | load w n =>
      simp only [coStepB] at hc
      cases hls : loadStruct? wire with
      | none =>
          rw [hls] at hc
          exact hfix hc
      | some p =>
          obtain ⟨d, b, x⟩ := p
          rw [hls] at hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨sc, rfl⟩ := loadStruct?_wire hls
          simp [instrLeakB, renRM, renLinstrR, renOperand, opLeakF, renEv, hc.2]
  | store w n =>
      simp only [coStepB] at hc
      cases hls : storeStruct? wire with
      | none =>
          rw [hls] at hc
          exact hfix hc
      | some p =>
          obtain ⟨d, b, x, v⟩ := p
          rw [hls] at hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨sc, rfl⟩ := storeStruct?_wire hls
          simp [instrLeakB, renRM, renLinstrR, renOperand, opLeakF, renEv, hc.1.1]
  | loadC => simp [coStepB] at hc
  | storeC => simp [coStepB] at hc
  | zero _ _ => simp [coStepB] at hc
  | storeImm _ _ => simp [coStepB] at hc

/-- **The events of a coalesced chain.** For a chain `is` of `ArrOK` `Lopn`s accepted by
    `coalesceB σ is obs` that runs from `s`, the coalesced chain `is.map (renRM σ)` emits,
    from a state related to `s` on the array names `liveArr is obs`, the events of `is` from
    `s` with array names renamed by `σ`. -/
theorem straightLeakF_coalesce {σ : String → String} :
    ∀ (is : List LinstrRM) (obs : List String), coalesceB σ is obs = true →
      (∀ i ∈ is, IsLopn i ∧ ArrOK i.1) →
      ∀ {s s' t : LstateM}, CoRel σ (liveArr is obs) s s' → lsemStraightMem is s = some t →
        straightLeakF (is.map (renRM σ)) s' = (straightLeakF is s).map (renEv σ)
  | [], _, _, _, _, _, _, _, _ => rfl
  | i :: is, obs, hc, hok, s, s', t, hR, h => by
      simp only [coalesceB, Bool.and_eq_true] at hc
      rw [lsemStraightMem_cons] at h
      cases hs : lsemStepMem i s with
      | none => simp [hs] at h
      | some s₁ =>
          rw [hs] at h
          obtain ⟨s₁', h₁, hR₁⟩ := lsemStepMem_coalesce hc.1 hR hs
          rw [List.map_cons, straightLeakF_cons_of_step h₁, straightLeakF_cons_of_step hs,
            List.map_append, hR.reg,
            instrLeakB_coStep hc.1 (hok i (by simp)).1 (hok i (by simp)).2,
            straightLeakF_coalesce is obs hc.2 (fun j hj => hok j (by simp [hj])) hR₁ h]

/-! ## 2. The array route -/

/-- The coalesced chain of a program: its chain `straightOpsMem` renamed by the alias map
    `chainAlias` of that chain. For an array-returning program it is the chain of the
    virtual body of `straightArrB`. -/
def arrChain {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t) :
    List LinstrRM :=
  (straightOpsMem Γ.length com Γ.length).map
    (renRM (chainAlias (straightOpsMem Γ.length com Γ.length)))

/-- A program accepted by `straightArrB` passes the route check of `arrChain` with no
    observed register. -/
theorem straightArrB_spec {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {Γ : Ctxt jasminDialect} {m : Nat} {com : Com jasminDialect Γ (.stackArr 64 m)}
    (hg : straightArrB σ nm body com = true) :
    straightRouteOutB σ nm body [] (arrChain com) = true := by
  simp only [straightArrB, Bool.and_eq_true] at hg
  exact hg.2

/-- **The coalesced chain from the state behind the copies.** For an array-returning program
    in the fragment `arrMemNB` whose chain passes the coalescing check under its alias map,
    the map fixing every array name live at the entry, with the coalesced chain plain, and a
    printed body `body` that passes the entry check `entryB`: at every valuation `V` the
    layout reads off the machine state `sa`, the chain `arrChain` is a chain of `Lopn`s, runs
    from `afterArgs`, and emits `straightT` of the source events of the program at `V` with
    array names renamed by the alias map. -/
theorem arrChain_run_of (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {Γ : Ctxt jasminDialect} {m : Nat}
    (com : Com jasminDialect Γ (.stackArr 64 m)) (hmem : arrMemNB com = true)
    (hco : coalesceB (chainAlias (straightOpsMem Γ.length com Γ.length))
      (straightOpsMem Γ.length com Γ.length) [comRetReg Γ.length argName com Γ.length] = true)
    (hfix : (liveArr (straightOpsMem Γ.length com Γ.length)
      [comRetReg Γ.length argName com Γ.length]).all
        (fun r => chainAlias (straightOpsMem Γ.length com Γ.length) r == r) = true)
    (hpl : plainB (arrChain com) = true) (hent : ImageAddrRoute.entryB σ nm body = true)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) :
    (∀ i ∈ arrChain com, IsLopn i)
      ∧ (∃ bz, runStraightF (arrChain com) (afterArgs σ body sa) false = some bz)
      ∧ straightLeakFF (arrChain com) (afterArgs σ body sa) false
        = (straightT Pj Γ.length com Γ.length (Com.ctLeak (jLeakModel Pj) com V)).map
          (renEv (chainAlias (straightOpsMem Γ.length com Γ.length))) := by
  have E := entryB_spec hent sa
  have habi := entryV_abiEntry (un := fun x => x) (sa := sa) E.argF E.argG fun _ _ => rfl
  have hagr : StoreAgreesM Γ.length Γ.length (afterArgs σ body sa) V :=
    storeAgreesM_lpc σ.args.length (storeAgreesM_of_abi hV habi)
  have hm := arrMemNB_sound com hmem
  obtain ⟨b, hrun, -⟩ := hm.straightOps_full rfl le_rfl hagr
  have hR0 : CoRel (chainAlias (straightOpsMem Γ.length com Γ.length))
      (liveArr (straightOpsMem Γ.length com Γ.length)
        [comRetReg Γ.length argName com Γ.length])
      (afterArgs σ body sa) (afterArgs σ body sa) :=
    ⟨rfl, rfl, rfl, rfl, fun r hr => by
      rw [show chainAlias (straightOpsMem Γ.length com Γ.length) r = r from by
        simpa using (List.all_eq_true.mp hfix) r hr]⟩
  obtain ⟨b', hrun', -⟩ := lsemStraightMem_coalesce _ _ hco hR0 hrun
  have hplain := plainB_sound hpl
  obtain ⟨c, o, hF⟩ := runStraightF_of_lsemStraightMem _ hplain _ b' false hrun'
  have hlk : straightLeakFF (arrChain com) (afterArgs σ body sa) false
      = straightLeakF (arrChain com) (afterArgs σ body sa) :=
    straightLeakFF_plain _ hplain (afterArgs σ body sa) b' (afterArgs σ body sa).cf
      (afterArgs σ body sa).of false hrun'
  have hok : ∀ i ∈ straightOpsMem Γ.length com Γ.length, IsLopn i ∧ ArrOK i.1 := fun i hi =>
    ⟨(arrMemN_straightOpsMem_plain hm _ _ i hi).1,
      straightOpsMem_arrOK _ com (arrMemN_comOpsPlain hm) _ i hi⟩
  refine ⟨fun i hi => (hplain i hi).1, ⟨_, hF⟩, ?_⟩
  rw [hlk]
  unfold arrChain
  rw [straightLeakF_coalesce _ _ hco hok hR0 hrun,
    straightLeakF_straightOps_arr Pj hm rfl le_rfl hagr]

/-- **The chain of the array route from the state behind the copies.** For an
    array-returning program that passes `straightArrB` against the printed body `body`, at
    every valuation `V` the layout reads off the machine state `sa`: the chain `arrChain` is
    a chain of `Lopn`s, runs from `afterArgs`, and emits `straightT` of the source events of
    the program at `V` with array names renamed by the alias map. -/
theorem arrChain_run (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {Γ : Ctxt jasminDialect} {m : Nat} (com : Com jasminDialect Γ (.stackArr 64 m))
    (hg : straightArrB σ nm body com = true) (sa : AState) (V : Ctxt.Valuation Γ)
    (hV : AbiValOf σ sa V) :
    (∀ i ∈ arrChain com, IsLopn i)
      ∧ (∃ bz, runStraightF (arrChain com) (afterArgs σ body sa) false = some bz)
      ∧ straightLeakFF (arrChain com) (afterArgs σ body sa) false
        = (straightT Pj Γ.length com Γ.length (Com.ctLeak (jLeakModel Pj) com V)).map
          (renEv (chainAlias (straightOpsMem Γ.length com Γ.length))) := by
  simp only [straightArrB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨hmem, hco⟩, hfix⟩, hpl⟩, -⟩, hroute⟩ := hg
  simp only [straightRouteB, Bool.and_eq_true] at hroute
  exact arrChain_run_of Pj com hmem hco hfix hpl hroute.2 sa V hV

/-- **The trace of the virtual body of the array route from the source events.** For a
    program that passes `straightArrB` against the printed body `body`: every terminating
    traced run of the virtual body from `straightEntry` at a machine state `sa` with the
    stack parameters at entry emits `straightT` of the source events of the program at the
    valuation `σ` reads off `sa`, with array names renamed by the alias map of the chain. -/
theorem straightArr_leak (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hg : straightArrB σ nm body com = true) (sa : AState) (hst : σ.StackIn sa)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (fn : String) {ℓ : List CTLeak}
    (hr : FRun (singletonProgM fn (argBind σ nm ++ arrChain com))
      (straightEntry σ body fn sa) ℓ) :
    ℓ = (straightT Pj Γ.length com Γ.length (Com.ctLeak (jLeakModel Pj) com V)).map
      (renEv (chainAlias (straightOpsMem Γ.length com Γ.length))) := by
  obtain ⟨m, rfl⟩ := straightArrB_ty hg
  have hroute := straightArrB_spec hg
  simp only [straightRouteOutB, Bool.and_eq_true] at hroute
  obtain ⟨hC, ⟨bz, hrun⟩, hT⟩ := arrChain_run Pj com hg sa V hV
  rw [straightVirt_leak hroute.2 hC sa hst fn hrun hr, hT]

/-- **Constant time of the virtual body of the array route from the source.** For a program
    that passes `straightArrB` against the printed body `body`: if the source events of the
    program are constant time for the labels `L`, the virtual body is constant time on the
    flag machine between the entries `straightEntry` of machine states related by
    `StraightPub`. -/
theorem straightArr_memFCT (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hg : straightArrB σ nm body com = true) (L : Labels Γ) (fn : String)
    (hct : ConstantTime (PubEqV L) (Com.ctLeak (jLeakModel Pj) com)) :
    MemFCT (singletonProgM fn (argBind σ nm ++ arrChain com))
      (StraightEntryPub σ L (straightEntry σ body fn)) := by
  rintro s₁ s₂ ℓ₁ ℓ₂ ⟨sa₁, sa₂, ⟨V₁, V₂, hV₁, hV₂, hp, hr₁, hr₂, -⟩, rfl, rfl⟩ r₁ r₂
  rw [straightArr_leak Pj com hg sa₁ hr₁.stackIn V₁ hV₁ fn r₁,
    straightArr_leak Pj com hg sa₂ hr₂.stackIn V₂ hV₂ fn r₂, hct V₁ V₂ hp]

/-- **The virtual body of the array route halts on checked runs** from the entry of every
    machine state that satisfies `σ.Regions` and has a valuation. -/
theorem straightArr_checked_run {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hg : straightArrB σ nm body com = true) (fn : String) (sa : AState)
    (V : Ctxt.Valuation Γ) (hreg : σ.Regions sa) (hV : AbiValOf σ sa V) :
    ∃ f t, lsemFuelMemFk true (singletonProgM fn (argBind σ nm ++ arrChain com)) f
      (straightEntry σ body fn sa) = some t := by
  obtain ⟨m, rfl⟩ := straightArrB_ty hg
  have hroute := straightArrB_spec hg
  simp only [straightRouteOutB, Bool.and_eq_true] at hroute
  obtain ⟨hC, ⟨bz, hrun⟩, -⟩ := arrChain_run JLeakParams.owned com hg sa V hV
  exact straightVirt_checked_run hroute.1.1.1.1.1.2 hroute.2 hC sa hreg fn hrun

/-- **The check on traced runs of the array route**: on a program returning an array of
    `64`-bit words, `ownedCheckML` observing no register on the virtual body and the image
    of the printed body `body` that `straightArrB` compares with `ownedCheckMC`; `false`
    otherwise. -/
def straightArrLB (σ : AbiLayout) (nm : String → String) (body : Lcmd) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | _, .stackArr 64 _, com =>
      ownedCheckML [] (argBind σ nm ++ arrChain com)
        (virtImg (slotRen (slotArrOf σ nm) fun x => x) body)
  | _, _, _ => false

/-- An array-returning program accepted by `straightArrLB` passes `ownedCheckML` observing
    no register. -/
theorem straightArrLB_spec {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {Γ : Ctxt jasminDialect} {m : Nat} {com : Com jasminDialect Γ (.stackArr 64 m)}
    (h : straightArrLB σ nm body com = true) :
    ownedCheckML [] (argBind σ nm ++ arrChain com)
      (virtImg (slotRen (slotArrOf σ nm) fun x => x) body) = true := by
  simpa only [straightArrLB] using h

/-- **Constant time of the image of the printed body of the array route.** For a program
    that passes `straightArrB` and the check on traced runs `straightArrLB` against the
    printed body `body`, with source events constant time for the labels `L`: the image of
    `body` is constant time on the flag machine between entries of the virtual body,
    public-equal by `StraightEntryPub`, at pc `0` and with halting checked runs (`TVPub`). -/
theorem straightArr_image_memFCT (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hg : straightArrB σ nm body com = true) (hlk : straightArrLB σ nm body com = true)
    (L : Labels Γ) (fn : String)
    (hct : ConstantTime (PubEqV L) (Com.ctLeak (jLeakModel Pj) com)) :
    MemFCT (singletonProgM fn (virtImg (slotRen (slotArrOf σ nm) fun x => x) body))
      (TVPub fn (argBind σ nm ++ arrChain com)
        (StraightEntryPub σ L (straightEntry σ body fn))) := by
  have hm := straightArr_memFCT Pj com hg L fn hct
  obtain ⟨m, rfl⟩ := straightArrB_ty hg
  exact memFCT_of_ownedCheckML (straightArrLB_spec hlk) fn hm

/-- **Constant time of the decoded bytes of the array route from the source.** Let the
    array-returning program `com` pass the gate `straightArrB` and the check on traced runs
    `straightArrLB` against the printed body `body`, which has no conditional branch. If the
    source events of `com` are constant time for the labels `L`, every decoding of the
    function bytes of `body` is constant time under the regime `doitm` and any side
    condition between entry machine states related by `StraightPub`: valuations that agree
    on the public labels, both states separated, equal stack registers and equal
    array-parameter registers. -/
theorem straightArr_bytes_ct (Pj : JLeakParams) {σ : AbiLayout} {nm : String → String}
    {body : Lcmd} {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hg : straightArrB σ nm body com = true) (hlk : straightArrLB σ nm body com = true)
    (L : Labels Γ) (hct : ConstantTime (PubEqV L) (Com.ctLeak (jLeakModel Pj) com))
    (hnc : NoCond body) (ok : AState → JInstr 64 → Prop) {prog : List RInstr}
    (hdec : decodeLprog (encodeLfundefBytes body) = some prog) :
    ConstantTimeRel (StraightPub σ L) (fun sa t => ∃ sa', RunL .doitm ok prog 0 sa t sa') := by
  have hm := straightArr_memFCT Pj com hg L "" hct
  have hk := straightArr_checked_run com hg ""
  obtain ⟨m, rfl⟩ := straightArrB_ty hg
  exact straight_bytes_ct (straightArrB_spec hg) (straightArrLB_spec hlk) hnc "" hm
    (fun sa V hreg hV => hk sa V hreg hV) ok hdec

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightArrLeak
