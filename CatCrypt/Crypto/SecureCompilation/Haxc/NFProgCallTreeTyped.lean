/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeAnswer

/-!
# The front relation with the call typing of the linked functions

The relation of the front `FrontRE` relates a call of a linked function `l` to a leaf call of the
same name at the result type of `l` whose encoded arguments are the source arguments; it does not
fix the argument types of the leaf call. The passage to the separation contracts
(`NFProgCallTreeEvent.contractREG_of_comp`, `NFProgCallTreeAnswer.compRA_of_contractRAC`) uses the
argument types of the leaf call at every pair of related calls, and a condition on the argument
types of every leaf call `FrontRE` relates to a source call does not hold: a leaf call with
arguments of another type whose encodings are the source arguments is related as well. The front
of the translation types a leaf call of a linked function by its parameters (`linkSig`), so the
front relation `FrontRET` adds the parameter types of the linked function as the argument types
of the leaf call, and the conditions become conditions on the linked functions of the module
(`frontRET_types`).

## Main definitions

* `FrontRET`: the relation `FrontRE` with the argument types of the leaf call the parameter types
  of the linked function.

## Main results

* `frontRET_types`: at linked functions with word and integer parameters and a word result, a leaf
  call related by `FrontRET` has word and integer arguments, as many as the parameters, and a word
  result.
* `contractREG_of_compT`, `compRA_of_contractRACT`: the passage to the separation contracts at
  `FrontRET`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTyped

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (wordsOf arrArgsOf
  resWord)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (enc dec encAll)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn wordVal)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig ExtRE ExtRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt (MapRE MapRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (CompRE CompRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack (BackRE BackRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCompose (FrontRE FrontRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (ChainRE ChainRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeKinds (contractRunOf summaryOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvent (IsCallEv encAll_wordsOf
  ins_scalar_of_arrArgs)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeAnswer (length_encAll arrArgsOf_words)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG
  contractREG_of_backRE)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (contractRAC)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open _root_.Hax

/-- **The front relation with the call typing**: `FrontRE`, with the argument types of the leaf
    call the parameter types of the linked function of its name. -/
def FrontRET (m : HaxModule) (e₀ : linkSig.Event) (e₁ : leafSig.Event) : Prop :=
  FrontRE m e₀ e₁ ∧ ∀ l, m.linked.find? (·.name == LinkCall.name e₀) = some l →
    e₁.argTys = l.params.map (·.2)

/-- **The types of a leaf call related by `FrontRET`.** At linked functions with word and integer
    parameters and a word result, a leaf call related by `FrontRET` has word and integer
    arguments, a word result, and as many arguments as the parameters of the linked function. -/
theorem frontRET_types {m : HaxModule}
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    {e₀ : linkSig.Event} {e₁ : leafSig.Event} (h : FrontRET m e₀ e₁) :
    (∀ a ∈ e₁.argTys, a = .word 64 ∨ a = .int) ∧ e₁.ret = .word 64
      ∧ ∀ l, m.linked.find? (·.name == LinkCall.name e₀) = some l →
        e₁.argTys.length = l.params.length := by
  obtain ⟨⟨-, -, l, hl, hr⟩, ht⟩ := h
  have hlm := List.mem_of_find?_eq_some hl
  refine ⟨fun a ha => ?_, hr.trans (hpar l hlm).2, fun l' hl' => by rw [ht l' hl', List.length_map]⟩
  rw [ht l hl] at ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact (hpar l hlm).1 p hp

/-- **The composed event relation at call events of the linked reader implies `contractREG`.**
    The statement of `NFProgCallTreeEvent.contractREG_of_comp` at the front relation `FrontRET`,
    at linked functions with word and integer parameters and a word result. A
    source call related to a target call event of the linked reader at the entry of a call by the
    composition of the event relations of the front, the chain and the back half is related to it
    by `contractREG`. -/
theorem contractREG_of_compT {m : HaxModule} {T : CalleeTab}
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hsub : T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData))
    (hword : ∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none))
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    {e₀ : linkSig.Event} {e₅ : (kSig AState).Event}
    (h : CompRE (FrontRET m) (CompRE ChainRE
      (fun e₄ e₅ => BackRE T e₄ e₅ ∧ IsCallEv (linkRead m) e₅)) e₀ e₅) :
    contractREG m e₀ e₅ := by
  obtain ⟨e₁, hFT, e₄, ⟨e₃, ⟨e₂, hE, hM⟩, hW⟩, hB, ret, sA, hent, hcall⟩ := h
  have htyF := (frontRET_types hpar hFT).1
  have hF := hFT.1
  obtain ⟨hn1, ha1, l, hl, -⟩ := hF
  obtain ⟨n₂, as₂, rs₂, xs₂⟩ := e₂
  obtain ⟨hn2, hty2, -, hv2⟩ := hE
  dsimp only at hn2 hty2
  subst hty2
  subst hM
  subst hW
  -- The source call at the words of the call event of `jasminDialect`.
  have he₀ : e₀ = ⟨e₁.name, (wordsOf (transArgs NarrowWords.widenP.mapTy
      (fun x => NarrowWords.transTy x)
      (transArgs catToJasmin.mapTy (fun x => ctTransTy x) xs₂))).map wordVal⟩ := by
    obtain ⟨n₀, a₀⟩ := e₀
    dsimp only at hn1 ha1 hl ⊢
    rw [hn1, ha1, encAll_wordsOf _ htyF _ _ hv2]
  generalize hev : (⟨n₂, ((e₁.argTys.map catTy).map catToJasmin.mapTy).map
      NarrowWords.widenP.mapTy, (rs₂.map catToJasmin.mapTy).map NarrowWords.widenP.mapTy,
      transArgs NarrowWords.widenP.mapTy (fun x => NarrowWords.transTy x)
        (transArgs catToJasmin.mapTy (fun x => ctTransTy x) xs₂)⟩ :
      NFProgCallTree.NFCall jasminDialect) = ev at hB
  have hevn : ev.name = e₀.name := by rw [← hev, ← hn1, ← hn2]
  have hevw : (wordsOf (transArgs NarrowWords.widenP.mapTy (fun x => NarrowWords.transTy x)
      (transArgs catToJasmin.mapTy (fun x => ctTransTy x) xs₂))) = wordsOf ev.args := by
    rw [← hev]
  -- The target event at the linked reader.
  obtain ⟨⟨cn, cargs⟩, entry⟩ := e₅
  dsimp only at hent hcall
  subst hent
  obtain ⟨hn5, c, hc, hw5⟩ := id hB
  dsimp only at hn5
  simp only [LinkCall.mk.injEq] at hcall
  obtain ⟨-, rfl⟩ := hcall
  subst hn5
  -- The linked function of the callee.
  have hl' : m.linked.find? (·.name == ev.name) = some l := by rw [hevn]; exact hl
  obtain ⟨hcm, hcn⟩ := CalleeTab.lookup_spec hc
  obtain ⟨l', hl'm, hlc⟩ := List.mem_filterMap.mp (hsub.subset hcm)
  have hn' := (CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1
  have hll : l' = l := by
    have h1 := find?_name_of_nodup hnd hl'm
    rw [← hn', hcn, hl'] at h1
    exact (Option.some.inj h1).symm
  subst hll
  obtain ⟨⟨r, hres⟩, harr⟩ := hword c hcm
  have hkind : kernelKind l' c = .ins l' c.ins c.resReg := by
    simp only [kernelKind, hres]
  have htop := ((hk l' hl'm).kind_facts hlc).1
  rw [hkind] at htop
  obtain ⟨-, hL, -⟩ := htop
  rw [he₀, hevw, show e₁.name = ev.name by rw [hevn, hn1]]
  exact contractREG_of_backRE (hk l' hl'm) hl' hc hL (ins_scalar_of_arrArgs harr) ret sA hB

/-- **The answers of the separation contracts are related by the composed answer relation.** Let
    the linked functions of `m` have distinct names, each be a linked kernel, the functions of the
    table `T` be among their data, each with a register result and no array position, and the
    leaf calls the front relates to source calls have word and integer arguments, as many as the
    parameters of the linked function, and a word result. Answers related by `contractRAC` are
    related by the composition of the answer relations of the front, the chain and the back half,
    at the procedure table of the summaries of the kinds `moduleKind` and the run relations of the
    contracts. -/
theorem compRA_of_contractRACT {m : HaxModule} {T : CalleeTab}
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hsub : T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData))
    (hword : ∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none))
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (d : CalleeKind) (tr₀ : List CTLeak)
    {e₀ : linkSig.Event} {e₅ : (kSig AState).Event} {a₀ : linkSig.Resp e₀}
    {a₅ : (kSig AState).Resp e₅} (hc : contractRAC m e₀ e₅ a₀ a₅) :
    CompRA (FrontRET m) (CompRE ChainRE (fun e₄ e₅ => BackRE T e₄ e₅ ∧ IsCallEv (linkRead m) e₅))
      FrontRA (CompRA ChainRE (fun e₄ e₅ => BackRE T e₄ e₅ ∧ IsCallEv (linkRead m) e₅)
        ChainRA (BackRA (summaryOf m.linked d) (contractRunOf m.linked tr₀))) e₀ e₅ a₀ a₅ := by
  intro e₁ hFT hCB
  obtain ⟨hargTy, hret, hlenT⟩ := frontRET_types hpar hFT
  have hF := hFT.1
  obtain ⟨l, hl, hsem, hall⟩ := id hc
  have hlen₁ := hlenT l hl
  obtain ⟨n₁, as₁, r₁, xs₁⟩ := e₁
  dsimp only at hargTy hret hlen₁
  subst hret
  obtain ⟨hn1, ha1, l', hl', hr1⟩ := hF
  dsimp only at hn1 ha1 hr1
  rw [hl] at hl'
  obtain rfl := Option.some.inj hl'
  refine ⟨(a₀ : Option Value).bind (dec (.word 64)), ?_, ?_⟩
  · -- The source answer is the encoding of the answer of the leaf call.
    show (a₀ : Option Value) = ((a₀ : Option Value).bind (dec (.word 64))).map (enc (.word 64))
    cases ha : (a₀ : Option Value) with
    | none => rfl
    | some v =>
      have hv : l.sem (LinkCall.args e₀) = some v := by rw [← hsem, ha]
      have hs := l.sem_res _ v hv
      rw [← hr1] at hs
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
      rw [Option.bind_some, hy, Option.map_some, ← CatCrypt.Crypto.Hax.ImpToNF.dec_sound _ _ _ hy]
  · intro e₄ hC hB
    obtain ⟨e₃, ⟨e₂, hE, hM⟩, hW⟩ := id hC
    obtain ⟨n₂, as₂, rs₂, xs₂⟩ := e₂
    obtain ⟨hn2, has2, hrs2, hv2⟩ := hE
    dsimp only at hn2 has2 hrs2 hv2
    subst hrs2
    subst has2
    subst hM
    subst hW
    refine ⟨((a₀ : Option Value).bind (dec (.word 64))).map fun y =>
      transArgs NarrowWords.widenP.mapTy (fun x => NarrowWords.transTy x)
        (transArgs catToJasmin.mapTy (fun x => ctTransTy x)
          (HVector.cons y .nil : Ctxt.Valuation (d := catCryptDialect) [catTy (.word 64)])), ?_, ?_⟩
    · -- The answers of the chain: the word, transported.
      generalize (a₀ : Option Value).bind (dec (.word 64)) = a₁
      intro e₃' hA' hW'
      obtain ⟨e₂', hE', hM'⟩ := hA'
      obtain ⟨n₂', as₂', rs₂', xs₂'⟩ := e₂'
      obtain ⟨-, has2', hrs2', -⟩ := hE'
      dsimp only at has2' hrs2'
      subst hrs2'
      subst has2'
      subst hM'
      refine ⟨a₁.map fun y => transArgs catToJasmin.mapTy (fun x => ctTransTy x)
        (HVector.cons y .nil : Ctxt.Valuation (d := catCryptDialect) [catTy (.word 64)]),
        fun e₂'' hE'' hM'' => ?_, fun y hy => ?_⟩
      · obtain ⟨n₂'', as₂'', rs₂'', xs₂''⟩ := e₂''
        obtain ⟨-, has2'', hrs2'', -⟩ := hE''
        dsimp only at has2'' hrs2''
        subst hrs2''
        subst has2''
        refine ⟨a₁.map fun y => (HVector.cons y .nil :
          Ctxt.Valuation (d := catCryptDialect) [catTy (.word 64)]), fun y hy => ?_,
          fun y hy => ?_⟩
        · refine ⟨y, ?_, rfl⟩
          rw [hy]
          rfl
        · cases a₁ with
          | none => cases hy
          | some y₀ =>
            cases hy
            rfl
      · cases a₁ with
        | none => cases hy
        | some y₀ =>
          cases hy
          rfl
    · -- The answer of the back half: the summary computes the word, the target runs the contract.
      obtain ⟨⟨hn5, c, hc5, hw5⟩, -⟩ := hB
      dsimp only at hn5 hc5 hw5 hn2
      have hn₀ : n₂ = LinkCall.name e₀ := hn2.trans hn1
      rw [hn₀] at hc5
      obtain ⟨hcm, hcn⟩ := CalleeTab.lookup_spec hc5
      obtain ⟨l', hl'm, hlc⟩ := List.mem_filterMap.mp (hsub.subset hcm)
      have hll : l' = l := by
        have h1 := find?_name_of_nodup hnd hl'm
        rw [← (CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1, hcn, hl] at h1
        exact (Option.some.inj h1).symm
      subst hll
      obtain ⟨⟨r, hres⟩, harr⟩ := hword c hcm
      obtain ⟨htop, -, hsum, -⟩ := (hk l' hl'm).kind_facts hlc
      have hkind : kernelKind l' c = .ins l' c.ins c.resReg := by
        simp only [kernelKind, hres]
      rw [hkind] at htop
      obtain ⟨-, hL, -⟩ := htop
      have hmk : moduleKind m.linked d n₂ = kernelKind l' c := by
        rw [hn₀]
        simp [moduleKind, hl, hlc]
      -- The kinds of the parameters are scalars.
      have hsc : ∀ k ∈ linkedKinds l', k = .scalar := by
        rw [(hk l' hl'm).kinds c hlc]
        intro k hk'
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk'
        have h1 : (a.reg, a.kind) ∈
            c.ins.map fun p => (X86Backend.DecodePrinted.phys p.1, p.2) := by
          rw [← hL.args]
          exact List.mem_map_of_mem ha
        obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h1
        rw [← (Prod.mk.inj hpe).2]
        exact NFProgCallTreeEvent.ins_scalar_of_arrArgs harr p hp
      have hargs : (wordsOf (transArgs NarrowWords.widenP.mapTy (fun x => NarrowWords.transTy x)
          (transArgs catToJasmin.mapTy (fun x => ctTransTy x) xs₂))).map wordVal
          = LinkCall.args e₀ := by
        rw [ha1, NFProgCallTreeEvent.encAll_wordsOf as₁ hargTy xs₁ xs₂ hv2]
      have hlenK : (linkedKinds l').length = (wordsOf (transArgs NarrowWords.widenP.mapTy
          (fun x => NarrowWords.transTy x)
          (transArgs catToJasmin.mapTy (fun x => ctTransTy x) xs₂))).length := by
        have h1 := congrArg List.length hargs
        rw [List.length_map, ha1, length_encAll] at h1
        rw [h1]
        simp [linkedKinds, hlen₁]
      cases hav : (a₀ : Option Value) with
      | none =>
        left
        rfl
      | some v =>
        right
        have hv : l'.sem (LinkCall.args e₀) = some v := by rw [← hsem, hav]
        have hs := l'.sem_res _ v hv
        rw [← hr1] at hs
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨s', hs', hrun⟩ := NFProgCallTreeKinds.contractRunOf_of_contractRAC hc hav tr₀
        refine ⟨transArgs NarrowWords.widenP.mapTy (fun x => NarrowWords.transTy x)
          (transArgs catToJasmin.mapTy (fun x => ctTransTy x)
            (HVector.cons y .nil : Ctxt.Valuation (d := catCryptDialect) [catTy (.word 64)])),
          ?_, ⟨(kernelKind l' c).summary, .word y, ?_, ?_, ?_, ?_, ?_⟩, s', tr₀, hs', ?_⟩
        · rw [Option.bind_some, hy]
          rfl
        · show some (moduleKind m.linked d n₂).summary = _
          rw [hmk]
        · rw [hsum]
          show l'.params.length = _
          simp [hlen₁]
        · rw [hsum]
          show CatCrypt.Crypto.Hax.insArrArgs (linkedKinds l') = _
          rw [CatCrypt.Crypto.Hax.insArrArgs_of_scalars hsc, arrArgsOf_words as₁ hargTy]
        · rw [hsum]
          simp only [LprogIsa.ProcSummary.result, linkedSummary]
          rw [insVals_scalars _ _ hsc hlenK, hargs, hv, Option.bind_some, hy]
        · intro dst u
          rfl
        · show contractRunOf m.linked tr₀ n₂ _ _ _
          rw [hn₀]
          exact hrun

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTyped
