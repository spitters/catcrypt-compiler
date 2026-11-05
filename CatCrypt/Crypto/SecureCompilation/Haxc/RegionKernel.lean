/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeStackRoom
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTProved
public import CatCrypt.Crypto.Hax.Module
public import CatCrypt.Crypto.SecureCompilation.VIR.NFRegionLaws
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntryUniq

@[expose] public section

set_option autoImplicit false

/-!
# A region-compiled program as a linked callee

A result `(P, bytes)` of `regionBack σ a p` whose decoded block `q` passes the keep check
`Callee.keepCheckB` is a callee of a linked call. Its interface `regionSig` has the
precondition `regionPre σ p` (the entry conditions of the layout and a valuation the layout
reads off the entry state at which `p` denotes), the footprint `KeepFoot P F` of a store
policy `P` (at `P := .frame`, the `F` bytes below the entry stack register), the
postcondition `regionPost σ p` (the layout reads back the source value of the result) and the
public relation `σ.PubAgree`.

## Main results

* `regionPre`, `regionPost`, `regionSig`: the interface of a region-compiled callee.
* `regionPre_bytes_ct`: the decoded block is constant time under `ctRegime` between
  publicly related entry states that satisfy `regionPre`, from the source constant time of
  the program and `regionWide_bytes_ct`.
* `calleeSpec_of_regionBack`: the leaky run of the decoded block meets `regionSig`, from
  the keep check, `regionBack_correct` and `regionPre_bytes_ct`.
* `LinkedFn.ofRegion`: the linked function of a region-compiled kernel, with the value-level
  contract `post_sem` as a hypothesis.
* `ofRegion_calleeSpec`, `ofRegion_calleeSpec_of_compile`, `ofRegion_pre_of`, `ofRegion_pub`: the specification of the code of
  `LinkedFn.ofRegion` at the interface of its fields, its precondition from the entry
  conditions and a denoting valuation, and its public relation from the public registers.
* `ofRegion_keepCheckAt`: the code check `calleeCodeB` accepts the data of
  `LinkedFn.ofRegion` whose code passes the keep check with separated out windows
  (`Callee.keepCheckSWB`) at the frame and the store policy of the record.
* `regionPost_sem`: the contract `post_sem` of `LinkedFn.ofRegion` for a meaning whose values
  are values of source runs, from the leg of a front that gives the program, without `call`
  and over a context of registers and stack arrays (`abiValOf_unique`, `denoteAt_fuel_mono`).
* `haltsC_of_regionCallee`: `CheckedIsaCall.haltsC_of_linkedChecksKW` at a region-compiled
  callee, with the callee specification from `calleeSpec_of_regionBack`, the absence of
  `call` in the callee from the keep check, the caller separation from the layout of the
  caller (`CalleeStackRoom.callerSep_of_regions`) and the footprint bound from
  `keepFoot_frame`.
* `regionPre_congr`, `regionPost_congr`, `regionSig_congr`: the interface depends on the
  program only through its denotation.
* `narrowPrep_castCtx_nfct`, `regionSig_castCtx`: over a wide context the program the back half
  compiles is constant time where the source is and has the interface of the source.
* `calleeSpec_of_compileRegion`, `haltsC_of_compileRegionCallee`: the same at a result of
  `compileRegion` over a context of 64-bit words, at a result type that is not an array of
  narrow words, through `compileRegion_ctx`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (NFCT)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)

/-! ## 1. The interface of a region-compiled callee -/

/-- **The precondition of a region-compiled callee** at the entry state `s`: the entry
    conditions `σ.Regions`, and a valuation that `σ` reads off `s` at which `p` denotes at
    some fuel. -/
def regionPre (σ : AbiLayout) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (s : AState) : Prop :=
  σ.Regions s ∧ ∃ (V : Ctxt.Valuation Γ) (fuel : Nat)
    (v : Ctxt.Valuation (d := jasminDialect) [t]), AbiValOf σ s V ∧ p.denote fuel V = some v

/-- **The postcondition of a region-compiled callee** between the entry state `s` and the
    return state `s'`: at a valuation that `σ` reads off `s` and a fuel at which `p` denotes
    `v`, the layout reads back from `s` and `s'` the source value of the result of `v`. -/
def regionPost (σ : AbiLayout) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (s s' : AState) : Prop :=
  ∃ (V : Ctxt.Valuation Γ) (fuel : Nat) (v : Ctxt.Valuation (d := jasminDialect) [t]),
    AbiValOf σ s V ∧ p.denote fuel V = some v
      ∧ σ.ResultOf s s' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))

/-- **The interface of a region-compiled callee**: the argument names `args` and the result
    name `res` at a call site, the clobber set `clob`, the precondition `regionPre σ p`, the
    footprint `KeepFoot P F` of the entry register file under the store policy `P` (the
    frame of `F` bytes below the entry stack register at `P := .frame`), the postcondition
    `regionPost σ p` and the public relation `σ.PubAgree`. -/
def regionSig (σ : AbiLayout) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (args : List String) (res : Option String)
    (clob : String → Bool) (F : Nat) (P : StorePol := .frame) : CalleeSig where
  args := args
  res := res
  clob := clob
  pre := regionPre σ p
  foot := fun s x => KeepFoot P F s.regs x
  post := regionPost σ p
  pub := σ.PubAgree

/-! ## 2. The specification of a region-compiled callee -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
  (regionExportableB_sound) in
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytesChecked_eq) in
/-- **Constant time of a region-compiled callee at its precondition.** Let
    `regionBack σ a p` give the bytes `bytes`, decoding to the block `q`, on a program `p`
    that is constant time at the source events for labels `L` that agree with the public
    data of `σ`, at every fuel. Then the leaky runs of `q` under `ctRegime`, with no side
    condition on the steps, from entry states that agree on the public data of `σ` and
    satisfy `regionPre σ p` have equal traces. The proof is `regionWide_bytes_ct_of_regionExp`
    at the webs of the export and the printed body of `regionBack_spec`, with the valuations of
    both entry
    states from the precondition. -/
theorem regionPre_bytes_ct {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog} {bytes : List (BitVec 8)}
    (h : regionBack σ a p = some (P, bytes)) (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel p) (hL : PubLabelsOK σ L)
    {q : List RInstr} (hq : decodeLprog bytes = some q) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ regionPre σ p s₁ ∧ regionPre σ p s₂)
      (fun s tr => ∃ s', RunL ctRegime (fun _ _ => True) q 0 s tr s') := by
  have hcf := callFree_of_regionBack h
  obtain ⟨hB, r0, r, b, cert, hr, rfl, hb, hco, hck, -⟩ := regionBack_spec h
  obtain ⟨hlk, hprW, hgW⟩ := regionCtB_spec hck
  rw [encodeLfundefBytesChecked_eq hb] at hq
  rintro sa₁ sa₂ u₁ u₂ ⟨hag, ⟨h₁, V₁, fuel, v₁, hV₁, hv₁⟩, ⟨h₂, V₂, -, -, hV₂, -⟩⟩ hb₁ hb₂
  exact regionWide_bytes_ct_of_regionExp JLeakParams.owned a.fname fuel
    (regionExportableB_sound hB) (legalizeRegion_callFree hcf)
    (nfCT_restrict _ σ (fun _ => True) (nfct_legalizeRegion (fun _ => rfl) (hsrc fuel)))
    (regionExp_webs _ hr) (regionWebsLeak_of_regionExp (regionExp_webs _ hr)) hco
    hlk hprW hgW (fun _ _ => True) hq
    sa₁ sa₂ u₁ u₂
    ⟨V₁, V₂, pubEqV_of_pubAgree hL hag hV₁ hV₂, hV₁, hV₂, h₁, h₂, trivial, trivial, hag.1,
      fun x hx n hn => hag.2 x hx (by simp [AbiLayout.argPub, hn]),
      show ((legalizeRegion p).denote fuel V₁).isSome = true by
        rw [legalizeRegion_denote, hv₁]; rfl⟩
    hb₁ hb₂

/-- **The specification of a region-compiled callee.** Let `regionBack σ a p` give the
    bytes `bytes`, decoding to the block `q` that passes `keepCheckWB` at the clobber set
    `clob`, the frame of `F` bytes and the store policy `K`, on a program `p` that is
    constant time at the source events for labels `L` that agree with the public data of
    `σ`, at every fuel. Then the leaky run of `q` under `ctRegime` meets
    `regionSig σ p args res clob F K`; the equal traces are `regionPre_bytes_ct`. -/
theorem calleeSpec_of_regionBack {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog} {bytes : List (BitVec 8)}
    (h : regionBack σ a p = some (P, bytes)) {q : List RInstr}
    (hq : decodeLprog bytes = some q) {args : List String} {res : Option String}
    {clob : String → Bool} {F : Nat} {K : StorePol} (hk : keepCheckWB q clob F K = true)
    (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel p) (hL : PubLabelsOK σ L) :
    CalleeSpec (runOf ctRegime q) (regionSig σ p args res clob F K) :=
  calleeSpec_of_keepCheckW (c := regionSig σ p args res clob F K) (P := K) hk
    (fun _ _ hx => hx)
    (fun s ⟨hreg, V, fuel, v, hV, hv⟩ => by
      obtain ⟨prog, s', hd, hh, hR, -⟩ := regionBack_correct h s V hV hreg fuel hv
      rw [hq, Option.some.injEq] at hd
      subst hd
      exact ⟨s', hh, V, fuel, v, hV, hv, hR⟩)
    (regionPre_bytes_ct h L hsrc hL hq)

/-- The precondition of a region-compiled callee depends on the program only through its
    denotation. -/
theorem regionPre_congr (σ : AbiLayout) {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p p' : NFProg jasminDialect Γ [t]} (h : ∀ fuel V, p'.denote fuel V = p.denote fuel V) :
    regionPre σ p' = regionPre σ p := by
  funext s
  simp only [regionPre, h]

/-- The postcondition of a region-compiled callee depends on the program only through its
    denotation. -/
theorem regionPost_congr (σ : AbiLayout) {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p p' : NFProg jasminDialect Γ [t]} (h : ∀ fuel V, p'.denote fuel V = p.denote fuel V) :
    regionPost σ p' = regionPost σ p := by
  funext s s'
  simp only [regionPost, h]

/-- The interface of a region-compiled callee depends on the program only through its
    denotation. -/
theorem regionSig_congr (σ : AbiLayout) {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p p' : NFProg jasminDialect Γ [t]} (h : ∀ fuel V, p'.denote fuel V = p.denote fuel V)
    (args : List String) (res : Option String) (clob : String → Bool) (F : Nat) (K : StorePol) :
    regionSig σ p' args res clob F K = regionSig σ p args res clob F K := by
  simp only [regionSig, regionPre_congr σ h, regionPost_congr σ h]

/-- **On a wide context the stages keep constant time** of the program carried back to the
    context alone (`castProg hΓ rfl`), at parameters with no variable-time operation. -/
theorem narrowPrep_castCtx_nfct {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (hΓ : Γ.map VIR.NarrowWords.wideTy = Γ)
    {p : NFProg jasminDialect Γ ts}
    {q : NFProg jasminDialect (Γ.map VIR.NarrowWords.wideTy) (ts.map VIR.NarrowWords.wideTy)}
    (hq : VIR.NarrowWords.narrowPrep p = some q) {L : Labels Γ} {fuel : Nat}
    (h : NFCT (jLeakModel Pj) L fuel p) :
    NFCT (jLeakModel Pj) L fuel (VIR.NarrowWords.castProg hΓ rfl q) := by
  intro V₁ V₂ hpub
  have e : ∀ V : Ctxt.Valuation Γ,
      (Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel (VIR.NarrowWords.castProg hΓ rfl q)
          V).map Prod.snd =
        (Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel q
          (VIR.NarrowWords.mapVal V)).map Prod.snd :=
    fun V => VIR.NarrowWords.leakRun_snd_heq _ hΓ.symm rfl
      (VIR.NarrowWords.castProg_heq hΓ rfl q) (VIR.NarrowWords.mapVal_heq_of_wide hΓ V).symm fuel
  rw [e, e]
  exact VIR.NarrowWords.narrowPrep_events hV fuel hq V₁ V₂ (h V₁ V₂ hpub)

/-- **The interface of the program the back half compiles over a wide context is that of the
    source.** Over a context that `wideTy` fixes and at a result type that is not an array of
    narrow words, the widened program carried back to the context denotes the widened values
    of `p`, which the layout reads as the values of `p` (`denVal_wideTy_transTy`). -/
theorem regionSig_castCtx (σ : AbiLayout) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (hΓ : Γ.map VIR.NarrowWords.wideTy = Γ) (ht : narrowArrB t = false)
    {p : NFProg jasminDialect Γ [t]}
    (hB : JasminLprogExport.ExportRegions.regionExportableB p = true)
    {q : NFProg jasminDialect (Γ.map VIR.NarrowWords.wideTy) ([t].map VIR.NarrowWords.wideTy)}
    (hq : VIR.NarrowWords.narrowPrep p = some q)
    (args : List String) (res : Option String) (clob : String → Bool) (F : Nat) (K : StorePol) :
    regionSig σ (VIR.NarrowWords.castProg hΓ rfl q) args res clob F K =
      regionSig σ p args res clob F K := by
  have hd : ∀ fuel V, (VIR.NarrowWords.castProg hΓ rfl q).denote fuel V =
      (p.denote fuel V).map
        (BlockLoweringExtend.transArgs VIR.NarrowWords.wideTy (fun x => VIR.NarrowWords.transTy x)) :=
    fun fuel V => VIR.NarrowWords.narrowPrep_castCtx_denoteAt CallDenote.env hΓ hB hq fuel V
  have hpre : regionPre σ (VIR.NarrowWords.castProg hΓ rfl q) = regionPre σ p := by
    funext s
    simp only [regionPre, hd, Option.map_eq_some_iff]
    apply propext
    constructor
    · rintro ⟨hr, V, fuel, -, hV, v, hv, -⟩
      exact ⟨hr, V, fuel, v, hV, hv⟩
    · rintro ⟨hr, V, fuel, v, hV, hv⟩
      exact ⟨hr, V, fuel, _, hV, v, hv, rfl⟩
  have hpost : regionPost σ (VIR.NarrowWords.castProg hΓ rfl q) = regionPost σ p := by
    funext s s'
    simp only [regionPost, hd, Option.map_eq_some_iff]
    apply propext
    constructor
    · rintro ⟨V, fuel, -, hV, ⟨v, hv, rfl⟩, hR⟩
      refine ⟨V, fuel, v, hV, hv, ?_⟩
      obtain ⟨x, ⟨⟩⟩ := v
      rwa [← denVal_wideTy_transTy ht]
    · rintro ⟨V, fuel, v, hV, hv, hR⟩
      refine ⟨V, fuel, _, hV, ⟨v, hv, rfl⟩, ?_⟩
      obtain ⟨x, ⟨⟩⟩ := v
      rwa [← denVal_wideTy_transTy ht] at hR
  simp only [regionSig, hpre, hpost]

/-- **The specification of a callee compiled by `compileRegion`.** Over a context that
    `wideTy` fixes and at a result type that is not an array of narrow words, let
    `compileRegion σ a p` give the bytes `bytes`, decoding to the block `q` that passes
    `keepCheckWB` at `clob`, `F` and `K`, on a program `p` that is constant time at the source
    events for labels `L` that agree with the public data of `σ`, at every fuel. Then the leaky
    run of `q` under `ctRegime` meets `regionSig σ p args res clob F K`: `regionBack` runs on
    the widened program carried back to the context (`compileRegion_ctx`), whose interface is
    that of `p` (`regionSig_castCtx`) and which is constant time where `p` is. -/
theorem calleeSpec_of_compileRegion {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog} {bytes : List (BitVec 8)}
    (hΓ : Γ.map VIR.NarrowWords.wideTy = Γ) (ht : narrowArrB t = false)
    (h : compileRegion σ a p = some (P, bytes)) {q : List RInstr}
    (hq : decodeLprog bytes = some q) {args : List String} {res : Option String}
    {clob : String → Bool} {F : Nat} {K : StorePol} (hk : keepCheckWB q clob F K = true)
    (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel p) (hL : PubLabelsOK σ L) :
    CalleeSpec (runOf ctRegime q) (regionSig σ p args res clob F K) := by
  obtain ⟨hB, q', hq', hb, -, -⟩ := compileRegion_ctx hΓ h
  rw [← regionSig_castCtx σ hΓ ht hB hq']
  exact calleeSpec_of_regionBack hb hq hk L
    (fun fuel => narrowPrep_castCtx_nfct (fun _ => rfl) hΓ hq' (hsrc fuel)) hL

/-! ## 3. The linked function of a region-compiled kernel -/

/-- **The linked function of a region-compiled kernel**: the name `name`, the typed
    parameters `params`, the result type `res` and the meaning `sem` of the kernel, the layout
    `σ`, the interface of `regionSig σ p` (precondition `regionPre σ p`, the footprint
    `KeepFoot P F` of the entry register file under the store policy `P`, postcondition
    `regionPost σ p`, public relation `σ.PubAgree`), the clobbered registers `clob`, the
    frame size `F` and the machine code `bytes`, the code of a result of
    `regionBack σ a p`. The value-level contract is the hypothesis `hsem`; the layout has
    no public array (`h0`), so agreement on the stack register and the public registers is
    the public relation. At the default `P := .frame` the footprint is the `F` bytes below
    the entry stack register (`keepFoot_frame`). The frame of the record is the larger of
    the code's frame `F + P.red` and the stack bound `-σ.frameLo` of the layout, since
    `AbiLayout.Regions` separates the pointer regions from the whole layout frame. -/
def _root_.CatCrypt.Crypto.Hax.LinkedFn.ofRegion (name : String)
    (params : List (String × NFDialect.NfTy)) (res : NFDialect.NfTy)
    (sem : List _root_.Hax.Value → Option _root_.Hax.Value)
    (sem_res : ∀ vals v, sem vals = some v →
      (CatCrypt.Crypto.Hax.ImpToNF.dec res v).isSome = true)
    (σ : AbiLayout) {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t])
    (clob : List String) (F : Nat) (bytes : List (BitVec 8))
    (hsem : ∀ sa sa' v, regionPre σ p sa → regionPost σ p sa sa' →
      sem (σ.args.map (·.read sa)) = some v → σ.ResultOf sa sa' v)
    (h0 : σ.pubWords = []) (P : StorePol := .frame) :
    CatCrypt.Crypto.Hax.LinkedFn where
  name := name
  params := params
  res := res
  sem := sem
  sem_res := sem_res
  layout := σ
  pre := regionPre σ p
  foot := fun s x => KeepFoot P F s.regs x
  post := regionPost σ p
  pub := σ.PubAgree
  pub_of_regs _ _ hrsp hargs := AbiLayout.PubAgree.of_pubWords_nil h0 hrsp hargs
  post_sem := hsem
  clob := clob
  /- The larger of the code's frame `F + P.red` (the frame and the red zone below the entry
     stack register) and the stack bound `-σ.frameLo` of the layout, the latter because
     `AbiLayout.Regions` separates the pointer regions from the whole layout frame. -/
  frame := max (F + P.red) (-σ.frameLo).toNat
  bytes := bytes
  pol := P

section OfRegion

variable {name : String} {params : List (String × NFDialect.NfTy)} {res : NFDialect.NfTy}
  {sem : List _root_.Hax.Value → Option _root_.Hax.Value}
  {sem_res : ∀ vals v, sem vals = some v →
    (CatCrypt.Crypto.Hax.ImpToNF.dec res v).isSome = true}
  {σ : AbiLayout} {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
  {clob : List String} {F : Nat} {bytes : List (BitVec 8)}
  {hsem : ∀ sa sa' v, regionPre σ p sa → regionPost σ p sa sa' →
    sem (σ.args.map (·.read sa)) = some v → σ.ResultOf sa sa' v} {h0 : σ.pubWords = []}
  {K : StorePol}

/-- **The specification of the code of a region-compiled linked function.** Let
    `regionBack σ a p` give the bytes `bytes` of `LinkedFn.ofRegion`, decoding to the block
    `q` that passes `keepCheckWB` at the clobbered registers, the frame size and the store
    policy `K` of the record,
    on a program `p` that is constant time at the source events for labels `L` that agree
    with the public data of `σ`, at every fuel. Then the leaky run of `q` under `ctRegime`
    meets the interface whose argument names are `args`, whose result name is `cres`, and
    whose clobber set, precondition, footprint, postcondition and public relation are those
    of the record. -/
theorem ofRegion_calleeSpec {a : AbiNames} {P : Lprog}
    (h : regionBack σ a p = some (P, bytes)) {q : List RInstr}
    (hq : decodeLprog bytes = some q) (args : List String) (cres : Option String)
    (hk : keepCheckWB q (fun x => clob.contains x) F K = true) (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel p) (hL : PubLabelsOK σ L) :
    let l := CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p clob F
      bytes hsem h0 K
    CalleeSpec (runOf ctRegime q)
      { args := args, res := cres, clob := fun x => l.clob.contains x, pre := l.pre,
        foot := l.foot, post := l.post, pub := l.pub } :=
  calleeSpec_of_regionBack (args := args) (res := cres) h hq hk L hsrc hL

/-- **The specification of the code of a linked function compiled by `compileRegion`.**
    `ofRegion_calleeSpec` at a result of `compileRegion σ a p` over a context that `wideTy`
    fixes, at a result type that is not an array of narrow words
    (`calleeSpec_of_compileRegion`). -/
theorem ofRegion_calleeSpec_of_compile {a : AbiNames} {P : Lprog}
    (hΓ : Γ.map VIR.NarrowWords.wideTy = Γ) (ht : narrowArrB t = false)
    (h : compileRegion σ a p = some (P, bytes)) {q : List RInstr}
    (hq : decodeLprog bytes = some q) (args : List String) (cres : Option String)
    (hk : keepCheckWB q (fun x => clob.contains x) F K = true) (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel p) (hL : PubLabelsOK σ L) :
    let l := CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p clob F
      bytes hsem h0 K
    CalleeSpec (runOf ctRegime q)
      { args := args, res := cres, clob := fun x => l.clob.contains x, pre := l.pre,
        foot := l.foot, post := l.post, pub := l.pub } :=
  calleeSpec_of_compileRegion (args := args) (res := cres) hΓ ht h hq hk L hsrc hL

/-- **The precondition of a region-compiled linked function from the entry conditions.** At
    an entry state `s` that satisfies `σ.Regions`, a valuation `V` that `σ` reads off `s` and
    at which `p` denotes at some fuel gives the precondition of `LinkedFn.ofRegion`. -/
theorem ofRegion_pre_of {s : AState} (hreg : σ.Regions s) {V : Ctxt.Valuation Γ}
    (hV : AbiValOf σ s V) {fuel : Nat} {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    (CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p clob F bytes
      hsem h0 K).pre s :=
  ⟨hreg, V, fuel, v, hV, hv⟩

/-- **The public relation of a region-compiled linked function from the public registers.**
    Two entry states with equal stack registers and equal registers of every public parameter
    of `σ` are related by the public relation of `LinkedFn.ofRegion`. -/
theorem ofRegion_pub {s₁ s₂ : AState} (hrsp : s₁.regs "%rsp" = s₂.regs "%rsp")
    (hargs : ∀ x ∈ σ.args, σ.argPub x = true → s₁.regs x.reg = s₂.regs x.reg) :
    (CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p clob F bytes
      hsem h0 K).pub s₁ s₂ :=
  AbiLayout.PubAgree.of_pubWords_nil h0 hrsp hargs

/-- The frame words of the layout lie among the frame bytes of a region-compiled linked
    function: `-l.frame ≤ σ.frameLo`. -/
theorem ofRegion_frameLo :
    -((CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p clob F bytes
      hsem h0 K).frame : Int) ≤ σ.frameLo := by
  change -((max (F + K.red) (-σ.frameLo).toNat : Nat) : Int) ≤ σ.frameLo
  omega

/-- **Completeness of the code check at a region-compiled linked function.** The data `c` of
    `LinkedFn.ofRegion` at the clobbered registers `clob`, the frame size `F` and the store
    policy `K`, whose bytes decode to a block `q` that passes `keepCheckSWB` at `clob`, `F` and
    `K`, passes the code check of `calleeCodeB`: `Callee.keepCheckAtB` at the clobber set, the
    frame and the store policy of `c`. -/
theorem ofRegion_keepCheckAt {c : CalleeData}
    (hc : (CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params res sem sem_res σ p clob F bytes
      hsem h0 K).calleeData = some c) {q : List RInstr} (hq : decodeLprog bytes = some q)
    (hk : keepCheckSWB q (fun x => clob.contains x) F K = true) :
    decodeLprog c.bytes = some q ∧ keepCheckAtB q c.sig.clob c.frame c.pol = true := by
  obtain ⟨-, -, -, hcl, hfr, hby, -⟩ := CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hc
  refine ⟨hby ▸ hq, ?_⟩
  have hsig : c.sig.clob = fun x => clob.contains x := by
    funext x
    show c.clob.contains x = clob.contains x
    rw [hcl]
    rfl
  rw [hsig, hfr, CatCrypt.Crypto.Hax.LinkedFn.calleeData_pol hc]
  exact keepCheckAtB_of_keepCheckSWB hk (le_max_left _ _)

end OfRegion

open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (regArrCtxB abiValOf_unique) in
/-- **The value-level contract of a region-compiled callee from its front.** Let the front
    of the leg `L` give the structured program `p` without `call` on the source program `s`,
    over a context of registers and stack arrays, and let every value `v` of `sem` at the
    arguments `σ` reads off an entry state satisfying `regionPre σ p` be a value of a source
    run of `s`. Then `sem` meets the contract `post_sem` of `LinkedFn.ofRegion` at `σ` and
    `p`: at an entry state `sa` and a return state `sa'` satisfying `regionPost σ p`, the
    layout reads back from `sa` and `sa'` the value of `sem`. -/
theorem regionPost_sem (L : FrontLegOfJ) {σ : AbiLayout} {s : L.Src} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hf : L.front σ s = some ⟨Γ, t, .regions p⟩) (hcf : p.callFree = true)
    (hΓ : regArrCtxB Γ = true) {sem : List _root_.Hax.Value → Option _root_.Hax.Value}
    (hrun : ∀ sa v, regionPre σ p sa → sem (σ.args.map (·.read sa)) = some v →
      L.Runs σ s sa v) :
    ∀ sa sa' v, regionPre σ p sa → regionPost σ p sa sa' →
      sem (σ.args.map (·.read sa)) = some v → σ.ResultOf sa sa' v := by
  intro sa sa' v hpre hpost hs
  obtain ⟨V', fuel, w, hV', hw, hR⟩ := hpost
  obtain ⟨V, k, x, hV, hx, rfl⟩ := L.leg σ s _ hf sa v hpre.1 (hrun sa v hpre hs)
  obtain rfl := abiValOf_unique hΓ hV hV'
  rw [RouteProgJ.envDenote_regions_of_callFree _ k p hcf] at hx
  obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp hx
  have e₁ := NFProg.denoteAt_fuel_mono CallEnv.empty (le_max_left k fuel) p V out ho
  have e₂ := NFProg.denoteAt_fuel_mono CallEnv.empty (le_max_right k fuel) p V w hw
  rw [e₁, Option.some.injEq] at e₂
  subst e₂
  exact hR

/-! ## 4. The linked call to a region-compiled callee -/

section Linked

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall (x86IsaK haltsC_of_linkedChecksKW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallW
  (printedAddrCWB imgGateCBW bitsDeadB liveW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeStackRoom
  (stackRoomB callerSep_of_regions footBelow_mono)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr frameP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem (Region regLen)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (rsOK abiBase abiReg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI frameIn frameIn_eq)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf)

/-- **A linked call to a region-compiled callee.** `CheckedIsaCall.haltsC_of_linkedChecksKW`
    over the wide class `ImageAddrCallW.printedAddrCWB` and the gate `ImageAddrCallW.imgGateCBW`
    at the callee given by a result of `regionBack σk ak pk` whose decoded block `q`
    passes `keepCheckB` at `clob` and `F`, under the interface
    `regionSig σk pk args (some res) clob F`, with:

    * the callee specification under `ctRegime` from `calleeSpec_of_regionBack`, with
      the source program constant time at labels `Lk` that agree with the public data of
      `σk`;
    * the absence of `call` in `q` from `not_call_mem_of_keepCheckW`;
    * the caller separation at the restricted frame of the body, the entry bases of the
      layout `σ` of the caller and the stack register after the prologue, from the entry
      conditions `σ.Regions sa0`, the stack room check `stackRoomB` and the frame check
      `frameNonnegB` (`callerSep_of_regions`);
    * the footprint bound at `G ≥ F` from `keepFoot_frame` and `footBelow_mono`.

    The bytes of the relocated calling body followed by the callee bytes decode to the
    caller prefix followed by the shifted block, and that program halts through calls from
    the position of the address state in a byte state that satisfies `Fin`. -/
theorem haltsC_of_regionCallee
    {σ : AbiLayout} {rs : List Region} (hrs : rsOK σ rs = true) {sa0 : AState}
    (hreg0 : σ.Regions sa0) {body : Lcmd} {G : Nat} (hroomB : stackRoomB σ body G = true)
    (hn : frameNonnegB body G = true) {slotArr : String → Option (String × Nat)}
    (hsl : ∀ q A n, slotArr q = some (A, n) → regLen rs A = n)
    (hsep : ImgSep (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0))) slotArr
      (abiBase (abiReg σ) sa0) (frameRsp body sa0))
    (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0)))
      slotArr body = true)
    (hsites : callSitesB slotArr body = true)
    {σk : AbiLayout} {ak : AbiNames} {Γk : Ctxt jasminDialect} {tk : JasminTy}
    {pk : NFProg jasminDialect Γk [tk]} {Pk : Lprog} {cb : List (BitVec 8)}
    (hc : regionBack σk ak pk = some (Pk, cb)) {q : List RInstr}
    (hcb : decodeLprog cb = some q) (hne : cb ≠ []) {args : List String} {res : String}
    {clob : String → Bool} {F : Nat} (hk : keepCheckB q clob F = true) (Lk : Labels Γk)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) Lk fuel pk) (hLk : PubLabelsOK σk Lk)
    (hFG : F ≤ G) (hG : G ≤ 2 ^ 64)
    {pr : LprogIsa.ProcSummary} {room : AState → Prop}
    (hw : WordCallee (regionSig σk pk args (some res) clob F) res pr room)
    (hroom : ∀ ret sA, sA.regs "%rsp" = frameRsp body sa0 → room (entryOf ret sA))
    {ds : List PhysAbiShape.DShape} (hcls : printedAddrCWB G body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body = some ds)
    (symBase : String → Option Int) {prog : List RInstr}
    (hbr : LprogBytesLinkReloc.branchOKReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length 0
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = true)
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {D : DeadTab}
    (hbits : bitsDeadB (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0))) D body
      = true)
    (hdead : callDeadB (regionSig σk pk args (some res) clob F) (fun _ => (res, args)) D.dead
      body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {f fn : String} (hT : T f = some pr)
    (hshape : siteShapeB f (fun _ => (res, args))
      (callImg slotArr (fun _ => (res, args)) body) = true)
    (hseg : deadSegB D (callImg slotArr (fun _ => (res, args)) body) = true)
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0)))
      slotArr (abiBase (abiReg σ) sa0) body t sa zf →
      LprogBytesLinkReloc.FinLea (frameRsp body sa0) (Params.ofBody body).frame sa sA →
      Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (n : Nat) {s t : LstateMF}
    (hrun : (x86IsaK.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr (fun _ => (res, args)) body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hI0 : ImgRelF (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0))) slotArr
      (abiBase (abiReg σ) sa0) body (D.dead sa.reg.lpc) s sa)
    (hA : ACorr (frameRsp body sa0) sA sa) :
    decodeLprog (LprogBytes.encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ LprogBytesLink.shiftProg prog.length q)
      ∧ ∃ sA', RInstrSemantics.HaltsC aMachine (prog ++ LprogBytesLink.shiftProg prog.length q)
          (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
        ∧ Fin t sA' :=
  haltsC_of_linkedChecksKW hsep hphys hgate hsites ctRegime
    (calleeSpec_of_regionBack hc hcb hk Lk hsrc hLk) (not_call_mem_of_keepCheckW hk) hw
    (callerSep_of_regions hrs hreg0 hroomB hn hsl)
    (footBelow_mono (fun _ _ hx => keepFoot_frame.1 hx) hFG hG) hroom hcls hshapes frameIn_eq
    symBase hcb hne hbr hP hbits hdead hflags hcond hT hshape hseg hfin hFin n hrun hfn hlen hL
    hI0 hA

/-- **A linked call to a callee compiled by `compileRegion`.** `haltsC_of_regionCallee` with
    the callee given by a result of `compileRegion σk ak pk` over a context that `wideTy` fixes,
    at a result type that is not an array of narrow words, its specification from
    `calleeSpec_of_compileRegion`. -/
theorem haltsC_of_compileRegionCallee
    {σ : AbiLayout} {rs : List Region} (hrs : rsOK σ rs = true) {sa0 : AState}
    (hreg0 : σ.Regions sa0) {body : Lcmd} {G : Nat} (hroomB : stackRoomB σ body G = true)
    (hn : frameNonnegB body G = true) {slotArr : String → Option (String × Nat)}
    (hsl : ∀ q A n, slotArr q = some (A, n) → regLen rs A = n)
    (hsep : ImgSep (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0))) slotArr
      (abiBase (abiReg σ) sa0) (frameRsp body sa0))
    (hphys : physImgB slotArr body = true)
    (hgate : imgGateCBW (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0)))
      slotArr body = true)
    (hsites : callSitesB slotArr body = true)
    {σk : AbiLayout} {ak : AbiNames} {Γk : Ctxt jasminDialect} {tk : JasminTy}
    {pk : NFProg jasminDialect Γk [tk]} {Pk : Lprog} {cb : List (BitVec 8)}
    (hΓk : Γk.map VIR.NarrowWords.wideTy = Γk) (htk : narrowArrB tk = false) (hc : compileRegion σk ak pk = some (Pk, cb)) {q : List RInstr}
    (hcb : decodeLprog cb = some q) (hne : cb ≠ []) {args : List String} {res : String}
    {clob : String → Bool} {F : Nat} (hk : keepCheckB q clob F = true) (Lk : Labels Γk)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) Lk fuel pk) (hLk : PubLabelsOK σk Lk)
    (hFG : F ≤ G) (hG : G ≤ 2 ^ 64)
    {pr : LprogIsa.ProcSummary} {room : AState → Prop}
    (hw : WordCallee (regionSig σk pk args (some res) clob F) res pr room)
    (hroom : ∀ ret sA, sA.regs "%rsp" = frameRsp body sa0 → room (entryOf ret sA))
    {ds : List PhysAbiShape.DShape} (hcls : printedAddrCWB G body = true)
    (hshapes : DecodeGen.shapesOf (Params.ofBody body) body = some ds)
    (symBase : String → Option Int) {prog : List RInstr}
    (hbr : LprogBytesLinkReloc.branchOKReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length 0
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = true)
    (hP : LprogBytesLinkReloc.expectedReloc
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (LprogBytesDecode.decCount
        (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds))
      (LprogBytes.encodeLfundefBytesReloc symBase body).length
      (LprogBytesLinkReloc.fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog)
    {D : DeadTab}
    (hbits : bitsDeadB (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0))) D body
      = true)
    (hdead : callDeadB (regionSig σk pk args (some res) clob F) (fun _ => (res, args)) D.dead
      body = true)
    (hflags : callFlagsB D body = true) (hcond : condLiveB D body = true)
    {T : LprogIsa.ProcTable} {f fn : String} (hT : T f = some pr)
    (hshape : siteShapeB f (fun _ => (res, args))
      (callImg slotArr (fun _ => (res, args)) body) = true)
    (hseg : deadSegB D (callImg slotArr (fun _ => (res, args)) body) = true)
    {Fin : LstateMF → AState → Prop}
    (hfin : ∀ t sa zf sA, ImgRel (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0)))
      slotArr (abiBase (abiReg σ) sa0) body t sa zf →
      LprogBytesLinkReloc.FinLea (frameRsp body sa0) (Params.ofBody body).frame sa sA →
      Fin t sA)
    (hFin : ∀ t t' sA, AgreeOffF (D.dead t.prog.base.reg.lpc) t t' → Fin t' sA → Fin t sA)
    (n : Nat) {s t : LstateMF}
    (hrun : (x86IsaK.withProcs T).lsemFuelMemF
      (singletonProgM fn (callImg slotArr (fun _ => (res, args)) body)) n s = some t)
    {sa : LstateA} {sA : AState} (hfn : s.prog.lfn = fn) (hlen : sa.reg.lpc < body.length)
    (hL : liveW D slotArr body sa.reg.lpc = false)
    (hI0 : ImgRelF (frameIn body (frameP (Params.ofBody body) (frameRsp body sa0))) slotArr
      (abiBase (abiReg σ) sa0) body (D.dead sa.reg.lpc) s sa)
    (hA : ACorr (frameRsp body sa0) sA sa) :
    decodeLprog (LprogBytes.encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ LprogBytesLink.shiftProg prog.length q)
      ∧ ∃ sA', RInstrSemantics.HaltsC aMachine (prog ++ LprogBytesLink.shiftProg prog.length q)
          (DecodePrintedCFG.posOf ds sa.reg.lpc) sA sA'
        ∧ Fin t sA' :=
  haltsC_of_linkedChecksKW hsep hphys hgate hsites ctRegime
    (calleeSpec_of_compileRegion hΓk htk hc hcb hk Lk hsrc hLk) (not_call_mem_of_keepCheckW hk) hw
    (callerSep_of_regions hrs hreg0 hroomB hn hsl)
    (footBelow_mono (fun _ _ hx => keepFoot_frame.1 hx) hFG hG) hroom hcls hshapes frameIn_eq
    symBase hcb hne hbr hP hbits hdead hflags hcond hT hshape hseg hfin hFin n hrun hfn hlen hL
    hI0 hA

end Linked

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel
