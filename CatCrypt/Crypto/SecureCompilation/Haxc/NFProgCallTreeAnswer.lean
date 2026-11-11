/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvent

/-!
# The composed answer relation from the separation contracts

`NFProgCallTreeR3.ruttF_front_compileRegion` relates the answers of a source call and of a target
call at the composition of the answer relations of the front (`FrontRA`), of the chain
(`ChainRA`) and of the back half (`BackRA PT X`). The statement `R3StatementF` relates them by
`contractRAC`. Since `RuttF` is antitone in the relation of answers, the passage asks that
`contractRAC` imply the composition, at the procedure table of the summaries of the kinds of the
linked kernels and the run relations of their contracts.

At a linked kernel with scalar parameters and a word result, the source answer of a call is the
meaning `sem` of the kernel at the arguments, which decodes to a word (`LinkedFn.sem_res`); the
leaf call answers that word, the calls of `catCryptDialect` and of `jasminDialect` answer it as a
valuation of one word, and the summary `linkedSummary` of the kernel computes it from the
argument words of the call of `jasminDialect`, which are the arguments of the source call
(`NFProgCallTreeEvent.encAll_wordsOf`). The target answer is a return state of the run relation of
the contract (`NFProgCallTreeKinds.contractRunOf_of_contractRAC`).

## Main results

* `compRA_of_contractRAC`: the answers of the separation contracts are related by the composed
  answer relation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeAnswer

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
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvent (IsCallEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (contractRAC)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open _root_.Hax

/-- The encodings of a vector of values are as many as its types. -/
theorem length_encAll : ∀ (as : List NfTy) (x : HVector NfTy.denote as),
    (encAll as x).length = as.length
  | [], .nil => rfl
  | _ :: as, .cons _ xs => by
    simp only [encAll, List.length_cons, length_encAll as xs]

/-- Word and integer argument types along the chain have no array position. -/
theorem arrArgsOf_words : ∀ (as : List NfTy), (∀ a ∈ as, a = .word 64 ∨ a = .int) →
    arrArgsOf (((as.map catTy).map catToJasmin.mapTy).map NarrowWords.widenP.mapTy)
      = fun _ => none
  | [], _ => by funext i; cases i <;> rfl
  | a :: as, ha => by
    have ih := arrArgsOf_words as fun b hb => ha b (List.mem_cons_of_mem _ hb)
    funext i
    rcases ha a List.mem_cons_self with rfl | rfl
    · cases i with
      | zero => rfl
      | succ i =>
        simp only [List.map_cons]
        rw [JasminLprogExport.ExportRegions.arrArgsOf_cons_succ, ih]
    · cases i with
      | zero => rfl
      | succ i =>
        simp only [List.map_cons]
        rw [JasminLprogExport.ExportRegions.arrArgsOf_cons_succ, ih]

/-- **The answers of the separation contracts are related by the composed answer relation.** Let
    the linked functions of `m` have distinct names, each be a linked kernel, the functions of the
    table `T` be among their data, each with a register result and no array position, and the
    leaf calls the front relates to source calls have word and integer arguments, as many as the
    parameters of the linked function, and a word result. Answers related by `contractRAC` are
    related by the composition of the answer relations of the front, the chain and the back half,
    at the procedure table of the summaries of the kinds `moduleKind` and the run relations of the
    contracts. -/
theorem compRA_of_contractRAC {m : HaxModule} {T : CalleeTab}
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hsub : T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData))
    (hword : ∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none))
    (hty : ∀ e₀ e₁, FrontRE m e₀ e₁ → (∀ a ∈ e₁.argTys, a = .word 64 ∨ a = .int)
      ∧ e₁.ret = .word 64)
    (hlen : ∀ e₀ e₁ l, FrontRE m e₀ e₁ → m.linked.find? (·.name == LinkCall.name e₀) = some l →
      e₁.argTys.length = l.params.length)
    (d : CalleeKind) (tr₀ : List CTLeak)
    {e₀ : linkSig.Event} {e₅ : (kSig AState).Event} {a₀ : linkSig.Resp e₀}
    {a₅ : (kSig AState).Resp e₅} (hc : contractRAC m e₀ e₅ a₀ a₅) :
    CompRA (FrontRE m) (CompRE ChainRE (fun e₄ e₅ => BackRE T e₄ e₅ ∧ IsCallEv (linkRead m) e₅))
      FrontRA (CompRA ChainRE (fun e₄ e₅ => BackRE T e₄ e₅ ∧ IsCallEv (linkRead m) e₅)
        ChainRA (BackRA (summaryOf m.linked d) (contractRunOf m.linked tr₀))) e₀ e₅ a₀ a₅ := by
  intro e₁ hF hCB
  obtain ⟨hargTy, hret⟩ := hty e₀ e₁ hF
  obtain ⟨l, hl, hsem, hall⟩ := id hc
  have hlen₁ := hlen e₀ e₁ l hF hl
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

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeAnswer
