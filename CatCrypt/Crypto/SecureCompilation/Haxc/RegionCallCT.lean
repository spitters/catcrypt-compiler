/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import CatCrypt.Crypto.SecureCompilation.Haxc.CTRegionsCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkRoute

@[expose] public section

set_option autoImplicit false

/-!
# Byte-level constant time of a calling body

The region back half `compileRegion` compiles a program with calls of linked functions to
the bytes of the function followed by the code of the table `T` of the called functions that
`regionCallee` finds, and gates the function with the constant-time decision with calls of
linked callees `AbiLayout.ctCheckRXT` at the interface of the table (`calleeCtB`): the clobber
set `CalleeTab.clobB`, the public argument registers `CalleeTab.ctIfc` and the destinations
`CalleeTab.ctDst` at the call targets, and the frame of the table. This module reads the gate
back: the bytes decode to the program `pr` of the function followed by the region of the
blocks of the functions of `T` with its targets raised by `pr.length`, and two runs of these
bytes from entry states related by the public data of the layout have equal leakage traces
when the leaky runs of each block meet an interface within that of its function.

## Main results

* `regionCoB_remoteSym`: the remote symbols of a calling body that passes the gate are
  symbols of its table.
* `compileRegion_spec_callee`: a result of `compileRegion` on a program with `call` has the
  table `T` that `regionCallee` finds at the export of the legalised program, a nonempty
  sublist of the linked functions with distinct symbols; the program `pr` of the function
  passes `ctCheckRXT` at the interface of `T`; and at the blocks the codes of `T` decode to,
  the code of `T` is their region and the bytes decode to `pr` followed by that region.
* `compileRegion_call_bytes_ct`: for such a result, every two runs with leakage of the
  decoded bytes from entry states satisfying `σ.Regions`, agreeing on the public data of
  `σ`, from which `pr` halts under the guarded oracle of the blocks at the entries of `T`,
  have equal traces.
* `AbiLayout.ctCheckRXO_sound_opt`: the soundness of `ctCheckRXO` at an optional destination.
* `LinkedFn.calleeData_callPub`: the data of a linked function relates by its public
  relation two entry states that agree on `%rsp` and its public argument registers.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.CT
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (exportR)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (remoteSym_mem_names
  compileRegion_spec_tab calleeBytes_tab regionCallee_fns_ne_nil)

/-- The remote symbols of a body that passes `regionCoB` at a table are symbols of the table:
    the decode of the call sites of the gate (`calleeBodyBT_spec`) at the class
    `ImageAddrCallW.printedAddrCWB` (`remoteSym_mem_names`). -/
theorem regionCoB_remoteSym {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {t : JasminTy} {code : List LinstrRM} {res : List LOperand} {cert : List (String × String)}
    {T : CalleeTab} {fn : String} (h : regionCoB σ nm body t code res cert (some T) fn = true) :
    ∀ i ∈ body, ∀ f, X86Backend.LprogBytes.remoteSym i.li_i = some f → f ∈ T.names := by
  have hpr := (regionCoB_callee h).1
  simp only [regionCoB, renImageB, calleeImgBT, Option.all_some, Bool.and_eq_true] at h
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := h
  exact remoteSym_mem_names hpr (calleeBodyBT_spec.mp hb).decode

/-- **The bytes and the gate of a calling body, at its table.** A result `(P, bytes)` of
    `compileRegion σ a p linked` on a program `p` with `call` has the table `T` that
    `regionCallee` finds at the export `r0` of the legalised program: a nonempty sublist of
    `linked` with distinct symbols and nonempty codes. The program `pr` of the function
    passes the constant-time decision with calls of linked callees `σ.ctCheckRXT` at the
    clobber set `T.clobB`, the public argument registers `T.ctIfc`, the frame `T.frame` and the
    destinations `T.ctDst` of the table. For every map `q` such that the code of each
    function `c` of `T` decodes to `q c`, the block `q c` has no `call`, the code of the table
    is the region of these blocks at the entry offsets and indices of the table
    (`CalleeTab.regionBlocks`), and the bytes decode to `pr` followed by the region program
    with its targets raised by `pr.length` (`calleeBytes_decode`). -/
theorem compileRegion_spec_callee {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData} {P : Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p linked = some (P, bytes))
    (hcf : p.callFree = false) :
    ∃ T : CalleeTab, (∃ r0, exportR Γ.length a.fname (legalizeRegion p) Γ.length 0 = some r0
        ∧ regionCallee linked (legalizeRegion p) r0.code = some (some T))
      ∧ T.fns.Sublist linked ∧ T.fns ≠ [] ∧ T.names.Nodup ∧ (∀ c ∈ T.fns, c.bytes ≠ [])
      ∧ ∃ pr : List RInstr,
        σ.ctCheckRXT T.clobB (T.ctIfc pr.length) T.frame (T.ctDst pr.length) pr = true
        ∧ ∀ q : CalleeData → List RInstr, (∀ c ∈ T.fns, decodeLprog c.bytes = some (q c)) →
          (∀ c ∈ T.fns, ∀ tg, RInstr.call tg ∉ q c)
          ∧ X86Backend.LprogBytesLinkReloc.RegionBlocks T.bytes T.names
              (fun g => T.entryOff (T.symPos g)) (fun g => T.entryIdx (T.symPos g))
              (X86Backend.LprogBytesLinkReloc.regionCode (T.regionEntries q))
              (X86Backend.LprogBytesLinkReloc.regionProg (T.regionEntries q))
          ∧ decodeLprog bytes = some (pr ++ shiftProg pr.length
              (X86Backend.LprogBytesLinkReloc.regionProg (T.regionEntries q))) := by
  obtain ⟨T, r0, hr0, hcT, -, -, r, b, cert, -, hbs, hg, hct, -⟩ := compileRegion_spec_tab h hcf
  have hnd : T.names.Nodup := by
    have hg' := hg
    simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
    obtain ⟨⟨⟨⟨⟨⟨hnd0, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg'
    exact of_decide_eq_true hnd0
  obtain ⟨pr, hp, hctp⟩ := calleeCtB_tab hct
  obtain ⟨hpr, hnoc⟩ := regionCoB_callee hg
  have hne := regionCallee_fns_ne_nil hcT
  have hneB := (calleeBytes_tab hbs).2.1
  refine ⟨T, ⟨r0, hr0, hcT⟩, regionCallee_sublist hcT, hne, hnd, hneB, pr, hctp,
    fun q hdecq => ?_⟩
  have hnoq : ∀ c ∈ T.fns, ∀ tg, RInstr.call tg ∉ q c := fun c hc => hnoc c hc _ (hdecq c hc)
  have hR := T.regionBlocks hne q hdecq hneB hnoq T.names (fun _ h => h)
  obtain ⟨pr', hp', hd⟩ := calleeBytes_decode hbs hpr (regionCoB_remoteSym hg) hR.decode
  rw [hp, Option.some.injEq] at hp'
  subst hp'
  exact ⟨hnoq, hR, hd⟩
/-- **Soundness of `ctCheckRXO` at an optional destination.** It is `ctCheckRX_sound` at
    `none` (`ctCheckRXO_none`) and `ctCheckRXO_sound` at `some w`, with the footprint of the
    callee among the `G` bytes below its entry stack register and the destination words
    `RegionSep.destAt w.1 w.2` of a destination `w ∈ dst`. -/
theorem AbiLayout.ctCheckRXO_sound_opt {σ : AbiLayout} {clob : String → Bool}
    {pubRegs : List String} {G : Nat} {dst : Option (String × Nat)} {p q : List RInstr}
    (h : σ.ctCheckRXO clob pubRegs G dst p = true)
    (hq : ∀ tg, RInstr.call tg ∉ q) {c : CalleeSig} (hX : CalleeSpec (runOf ctRegime q) c)
    (hclob : ∀ x, clob x = false → c.clob x = false)
    (hfoot : ∀ s x, c.foot s x →
      InFrame (s.regs "%rsp") G x ∨ ∃ w ∈ dst, RegionSep.destAt w.1 w.2 s x)
    (hpub : ∀ s₁ s₂, c.pre s₁ → c.pre s₂ → (callPub pubRegs).Agree s₁ s₂ → c.pub s₁ s₂)
    {s₁ s₂ s₁' s₂' : AState} (hag : σ.PubAgree s₁ s₂) (hR₁ : σ.Regions s₁)
    (hR₂ : σ.Regions s₂)
    (h₁ : HaltsO aMachine (oracleAt p.length (guarded c (runOf ctRegime q))) p 0 s₁ s₁')
    (h₂ : HaltsO aMachine (oracleAt p.length (guarded c (runOf ctRegime q))) p 0 s₂ s₂')
    {ok₁ ok₂ : AState → JInstr 64 → Prop} {t₁ t₂ : List CTLeak} {e₁ e₂ : AState}
    (hr₁ : RunL ctRegime ok₁ (p ++ shiftProg p.length q) 0 s₁ t₁ e₁)
    (hr₂ : RunL ctRegime ok₂ (p ++ shiftProg p.length q) 0 s₂ t₂ e₂) : t₁ = t₂ := by
  cases dst with
  | none =>
      rw [AbiLayout.ctCheckRXO_none] at h
      exact AbiLayout.ctCheckRX_sound h hq hX hclob
        (fun s x hf => (hfoot s x hf).resolve_right (by simp)) hpub hag hR₁ hR₂ h₁ h₂ hr₁ hr₂
  | some w =>
      refine AbiLayout.ctCheckRXO_sound h hq hX hclob (fun s x hf => ?_) hpub
        hag hR₁ hR₂ h₁ h₂ hr₁ hr₂
      rcases hfoot s x hf with h | ⟨w', hw', hdw⟩
      · exact .inl h
      · rw [Option.mem_def, Option.some.injEq] at hw'
        subst hw'
        exact .inr hdw

/-- **Byte-level constant time of a calling body, at its table.** For a result `(P, bytes)` of
    `compileRegion σ a p linked` on a program `p` with `call`, the table `T` that
    `regionCallee` finds (`compileRegion_spec_callee`) and the program `pr` of the function
    satisfy: for every map `q` such that the code of each function `c` of `T` decodes to
    `q c.name`, the bytes decode to `pr` followed by the region program of the blocks; and for
    interfaces `sg` such that the leaky runs of `q c.name` meet `sg c.name` (`CalleeSpec`),
    with clobber set inside that of `c`, footprint among the `c.frame` bytes below the entry
    stack register and the words of the destination `c.outDst?` (`RegionSep.destAt`), and a
    public relation implied by agreement on `%rsp` and the public argument registers of `c`
    between entry states satisfying the precondition, every two runs with leakage of that
    program from entry states satisfying `σ.Regions`, agreeing on the public data of `σ`, from
    which `pr` halts under the oracle of the blocks guarded by the preconditions of `sg` at
    the entries of the functions of `T`, have equal traces. The proof is
    `AbiLayout.ctCheckRXT_sound` at the blocks of the region (`CalleeTab.regionBlocks`), whose
    entries are distinct (`CalleeTab.entryIdx_inj`) and carry the interface of their function
    (`CalleeTab.ctIfc_entry`, `CalleeTab.ctDst_entry`, `CalleeTab.clob_of_clobB`). -/
theorem compileRegion_call_bytes_ct {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData} {P : Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p linked = some (P, bytes))
    (hcf : p.callFree = false) :
    ∃ T : CalleeTab, (∃ r0, exportR Γ.length a.fname (legalizeRegion p) Γ.length 0 = some r0
        ∧ regionCallee linked (legalizeRegion p) r0.code = some (some T))
      ∧ T.fns.Sublist linked ∧ T.fns ≠ [] ∧ T.names.Nodup
      ∧ ∃ pr : List RInstr, ∀ q : String → List RInstr,
        (∀ c ∈ T.fns, decodeLprog c.bytes = some (q c.name)) →
        decodeLprog bytes = some (pr ++ shiftProg pr.length
          (X86Backend.LprogBytesLinkReloc.regionProg (T.regionEntries fun c => q c.name)))
        ∧ ∀ sg : String → CalleeSig,
          (∀ c ∈ T.fns, CalleeSpec (runOf ctRegime (q c.name)) (sg c.name)
            ∧ (∀ x, c.clob.contains x = false → (sg c.name).clob x = false)
            ∧ (∀ s x, (sg c.name).foot s x → InFrame (s.regs "%rsp") c.frame x
              ∨ ∃ w ∈ c.outDst?, RegionSep.destAt w.1 w.2 s x)
            ∧ ∀ s₁ s₂, (sg c.name).pre s₁ → (sg c.name).pre s₂ →
              (callPub c.pubRegs).Agree s₁ s₂ → (sg c.name).pub s₁ s₂) →
          ∀ {s₁ s₂ s₁' s₂' : AState}, σ.PubAgree s₁ s₂ → σ.Regions s₁ → σ.Regions s₂ →
            HaltsO aMachine (oracleOf T.names (fun f => pr.length + T.entryIdx (T.symPos f))
              (fun f => guarded (sg f) (runOf ctRegime (q f)))) pr 0 s₁ s₁' →
            HaltsO aMachine (oracleOf T.names (fun f => pr.length + T.entryIdx (T.symPos f))
              (fun f => guarded (sg f) (runOf ctRegime (q f)))) pr 0 s₂ s₂' →
            ∀ {ok₁ ok₂ : AState → JInstr 64 → Prop} {t₁ t₂ : List CTLeak} {e₁ e₂ : AState},
              RunL ctRegime ok₁ (pr ++ shiftProg pr.length
                (X86Backend.LprogBytesLinkReloc.regionProg (T.regionEntries fun c => q c.name)))
                0 s₁ t₁ e₁ →
              RunL ctRegime ok₂ (pr ++ shiftProg pr.length
                (X86Backend.LprogBytesLinkReloc.regionProg (T.regionEntries fun c => q c.name)))
                0 s₂ t₂ e₂ → t₁ = t₂ := by
  obtain ⟨T, hpin, hsub, hne, hnd, hneB, pr, hct, hrest⟩ := compileRegion_spec_callee h hcf
  refine ⟨T, hpin, hsub, hne, hnd, pr, fun q hq => ?_⟩
  obtain ⟨hnoc, hR, hd⟩ := hrest (fun c => q c.name) hq
  refine ⟨hd, fun sg hsg s₁ s₂ s₁' s₂' hag hR₁ hR₂ h₁ h₂ ok₁ ok₂ t₁ t₂ e₁ e₂ hr₁ hr₂ => ?_⟩
  have hinjP : ∀ i < T.fns.length, ∀ j < T.fns.length, T.entryIdx i = T.entryIdx j → i = j :=
    fun i hi j hj hij => T.entryIdx_inj hnd hneB hR.decode hi hj hij
  refine AbiLayout.ctCheckRXT_sound (fs := T.names) (k := fun f => T.entryIdx (T.symPos f))
    (q := q) (c := sg) (pub := fun f => ((T.lookup f).map (·.pubRegs)).getD []) hct
    (fun f hf => ?_) (fun f hf => ?_) (fun f hf g hg hfg => ?_) (fun f hf => ?_)
    (fun f hf => ?_) (fun f hf => ?_) (fun f hf => ?_) (fun f hf => ?_)
    hag hR₁ hR₂ h₁ h₂ hr₁ hr₂
  all_goals obtain ⟨c, hc⟩ := T.lookup_of_mem hf
  all_goals obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
  · obtain ⟨A, B, hQ, hA⟩ := hR.block c.name hf
    rw [CalleeTab.regionCode_lookup T _ hc] at hQ
    exact ⟨A, B, hQ, hA⟩
  · exact hnoc c hcm
  · obtain ⟨d, hd⟩ := T.lookup_of_mem hg
    obtain ⟨hdm, rfl⟩ := CalleeTab.lookup_spec hd
    have hc' := CalleeTab.lookup_symPos hc
    have hd' := CalleeTab.lookup_symPos hd
    have hi := (List.getElem?_eq_some_iff.mp hc').1
    have hj := (List.getElem?_eq_some_iff.mp hd').1
    rw [hinjP _ hi _ hj hfg, hd', Option.some.injEq] at hc'
    rw [hc']
  · exact (hsg c hcm).1
  · exact fun x hx => (hsg c hcm).2.1 x (T.clob_of_clobB hcm hx)
  · refine fun s x hx => ((hsg c hcm).2.2.1 s x hx).imp
      (X86Backend.Callee.inFrame_of_le (T.frame_le hcm)) fun ⟨w, hw, hdw⟩ => ⟨w, ?_, hdw⟩
    rw [T.ctDst_entry hinjP _ hc]
    exact hw
  · rw [T.ctIfc_entry hinjP _ hc]
    simp [hc]
  · intro s₁ s₂ hp₁ hp₂ hpa
    simp only [hc, Option.map_some, Option.getD_some] at hpa
    exact (hsg c hcm).2.2.2 s₁ s₂ hp₁ hp₂ hpa

/-- **The public relation of the data of a linked function**: two entry states that agree
    on `%rsp` and on the public argument registers `pubRegs` of the data of a linked
    function `l` are related by its public relation (`LinkedFn.pub_of_regs`). -/
theorem _root_.CatCrypt.Crypto.Hax.LinkedFn.calleeData_callPub
    {l : CatCrypt.Crypto.Hax.LinkedFn} {c : CalleeData} (h : l.calleeData = some c)
    (s₁ s₂ : AState) (hag : (callPub c.pubRegs).Agree s₁ s₂) : c.pub s₁ s₂ := by
  obtain ⟨res, -, rfl⟩ := Option.map_eq_some_iff.mp h
  refine l.pub_of_regs s₁ s₂ (hag.1 _ List.mem_cons_self) fun x hx hp => hag.1 _ ?_
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, hp⟩, rfl⟩)

end CatCrypt.Crypto.SecureCompilation.Haxc
