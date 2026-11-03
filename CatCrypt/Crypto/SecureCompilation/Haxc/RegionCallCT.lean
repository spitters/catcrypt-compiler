/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import CatCrypt.Crypto.SecureCompilation.Haxc.CTRegionsCall

@[expose] public section

set_option autoImplicit false

/-!
# Byte-level constant time of a calling body

The region back half `compileRegion` compiles a program with a `call` of a linked function
`c` to the bytes of the function followed by the code of `c`, and gates the function with
the constant-time decision with a call and an optional destination `AbiLayout.ctCheckRXO`
(`calleeCtB`), at the destination `CalleeData.outDst?` of an out result. This module
reads the gate back: the bytes decode to the program `pr` of the function followed by the
code `q` of `c` with its targets raised by `pr.length`, and two runs of these bytes from
entry states related by the public data of the layout have equal leakage traces when the
callee's leaky runs meet its interface.

## Main results

* `compileRegion_spec_callee`: at linked functions whose code decodes, a result of
  `compileRegion` on a program with `call` has a callee among the linked functions whose
  code decodes to a block `q` without `call`, the
  bytes decode to `pr ++ shiftProg pr.length q`, and `pr` passes `ctCheckRXO` at the clobber
  set, the public argument registers, the frame and the destination of the callee.
* `compileRegion_call_bytes_ct`: for such a result, every two runs with leakage of the
  decoded bytes from entry states satisfying `σ.Regions`, agreeing on the public data of
  `σ`, from which `pr` halts under the guarded oracle of the callee, have equal traces.
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

/-- **The bytes and the gate of a calling body.** When the code of every linked function of
    `linked` decodes, a result `(P, bytes)` of `compileRegion σ a p linked` on a program `p`
    with `call` has a callee `c` among
    `linked` whose code decodes to a block `q` without `call`; the bytes decode to the
    program `pr` of the function followed by `q` with its targets raised by `pr.length`; and
    `pr` passes the constant-time decision with a call and an optional destination
    `σ.ctCheckRXO` at the clobber set, the public argument registers, the frame and the
    destination `c.outDst?` of `c`. -/
theorem compileRegion_spec_callee {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData} {P : Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p linked = some (P, bytes))
    (hcf : p.callFree = false) (hdec : ∀ c ∈ linked, (decodeLprog c.bytes).isSome) :
    ∃ c ∈ linked, ∃ pr q, decodeLprog c.bytes = some q ∧ (∀ tg, RInstr.call tg ∉ q)
      ∧ decodeLprog bytes = some (pr ++ shiftProg pr.length q)
      ∧ σ.ctCheckRXO (fun x => c.clob.contains x) c.pubRegs c.frame c.outDst? pr = true := by
  unfold compileRegion at h
  split at h
  · split at h
    · split at h
      · rename_i callee hc
        cases callee with
        | none => rw [← legalizeRegion_callFree_eq,regionCallee_callFree hc] at hcf; cases hcf
        | some T =>
          split at h
          · obtain ⟨b, hbs, hg⟩ := regionEncode_spec_callee h
            rw [Bool.and_eq_true] at hg
            obtain ⟨c, rfl⟩ := calleeCtB_some hg.2
            have hcm := regionCallee_mem hc c (by simp [CalleeTab.one])
            obtain ⟨hpr, hqc⟩ := regionCoB_callee hg.1
            rw [CalleeTab.frame_one] at hpr
            obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hdec c hcm)
            obtain ⟨pr, hp, hd⟩ := calleeBytes_decode_one hbs hpr hq
            have hct := hg.2
            simp only [calleeCtB_one, hp] at hct
            exact ⟨c, hcm, pr, q, hq, hqc c (by simp [CalleeTab.one]) q hq, hd, hct⟩
          · cases h
      · cases h
    · cases h
  · cases h

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

/-- **Byte-level constant time of a calling body.** Let the code of every linked function of
    `linked` decode, and let every linked function `c` of `linked` whose code decodes to `q`
    meet its interface on the leaky runs of `q`
    (`CalleeSpec`), write only among the `c.frame` bytes below its entry stack register and
    the words of its destination `c.outDst?` (`RegionSep.destAt`), and relate by its public
    relation two entry states satisfying its
    precondition that agree on `%rsp` and its public argument registers. For a result
    `(P, bytes)` of `compileRegion σ a p linked` on a program `p` with `call`, the bytes
    decode to `pr ++ shiftProg pr.length q` for the code `q` of a callee `c` among
    `linked`, and every two runs with leakage of that program from entry states satisfying
    `σ.Regions` and agreeing on the public data of `σ`, from which `pr` halts under the
    oracle of the leaky runs of `q` guarded by the precondition of `c`, have equal
    traces. -/
theorem compileRegion_call_bytes_ct {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {linked : List CalleeData} {P : Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p linked = some (P, bytes))
    (hcf : p.callFree = false) (hdec : ∀ c ∈ linked, (decodeLprog c.bytes).isSome)
    (hlk : ∀ c ∈ linked, ∀ q, decodeLprog c.bytes = some q →
      CalleeSpec (runOf ctRegime q) c.sig
        ∧ (∀ s x, c.foot s x → InFrame (s.regs "%rsp") c.frame x
          ∨ ∃ w ∈ c.outDst?, RegionSep.destAt w.1 w.2 s x)
        ∧ ∀ s₁ s₂, c.pre s₁ → c.pre s₂ → (callPub c.pubRegs).Agree s₁ s₂ → c.pub s₁ s₂) :
    ∃ c ∈ linked, ∃ pr q, decodeLprog c.bytes = some q
      ∧ decodeLprog bytes = some (pr ++ shiftProg pr.length q)
      ∧ ∀ {s₁ s₂ s₁' s₂' : AState}, σ.PubAgree s₁ s₂ → σ.Regions s₁ → σ.Regions s₂ →
        HaltsO aMachine (oracleAt pr.length (guarded c.sig (runOf ctRegime q))) pr 0 s₁ s₁' →
        HaltsO aMachine (oracleAt pr.length (guarded c.sig (runOf ctRegime q))) pr 0 s₂ s₂' →
        ∀ {ok₁ ok₂ : AState → JInstr 64 → Prop} {t₁ t₂ : List CTLeak} {e₁ e₂ : AState},
          RunL ctRegime ok₁ (pr ++ shiftProg pr.length q) 0 s₁ t₁ e₁ →
          RunL ctRegime ok₂ (pr ++ shiftProg pr.length q) 0 s₂ t₂ e₂ → t₁ = t₂ := by
  obtain ⟨c, hc, pr, q, hq, hqc, hd, hct⟩ := compileRegion_spec_callee h hcf hdec
  obtain ⟨hX, hF, hpub⟩ := hlk c hc q hq
  exact ⟨c, hc, pr, q, hq, hd, fun hag hR₁ hR₂ h₁ h₂ _ _ _ _ _ _ hr₁ hr₂ =>
    AbiLayout.ctCheckRXO_sound_opt hct hqc hX (fun _ hx => hx) hF hpub hag hR₁ hR₂ h₁ h₂ hr₁ hr₂⟩

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
