/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCommon
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCoalesce
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeLive
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSelfNop

/-!
# Call trees whose events meet a condition, through the passes of the reference

`NFProgCallTreeExport.CallSite` constrains the symbol, the arity and the argument words of an
event, not its result types, so a hypothesis on every event at every call site of a body with
a call (the hypothesis `hev` of `NFProgCallTreeWebs.tsim_webs`, `tsim_coalesce`, `tsim_live`,
`tsim_selfNop` and `NFProgCallTreeCommon.tsim_common`) also covers events of every result type.
The passes hold with that hypothesis restricted to the events of a condition `G`, when the
relation `TSim` is taken at the call sites of events of `G`. A tree all of whose events meet `G`
(`AllEv`) is related at the call sites alone exactly when it is related at the call sites of
events of `G` (`tsim_and_of_allEv`, `TSim.siteMono`).

## Main definitions

* `AllEv`: every event of a call tree meets a condition.

## Main results

* `TSim.siteMono`: `TSim` is monotone in the predicate of the call sites.
* `tsim_and_of_allEv`: a tree whose events meet `G` is related at the call sites of events of
  `G`.
* `tsim_websOn`, `tsim_coalesceOn`, `tsim_liveOn`, `tsim_selfNopOn`, `tsim_commonOn`: the
  passes of the reference at the call sites of events of `G`, under the condition of the pass
  on the events of `G` only.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim)

/-- **Every event of a call tree meets the condition `G`**, at every answer. -/
def AllEv {E : EventSig} {R : Type} (G : E.Event → Prop) : CallTree E R → Prop
  | .ret _ => True
  | .vis e c => G e ∧ ∀ a, AllEv G (c a)

variable {E : EventSig} {I : Isa} {P : LprogM}

/-- **`TSim` is monotone in the predicate of the call sites.** -/
theorem TSim.siteMono {Site Site' : E.Event → LstateMF → Prop}
    {Q : (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop} {α : Type}
    {Post : α → LstateMF → Prop} (hS : ∀ e u, Site e u → Site' e u) :
    ∀ {t : CallTree E (Option α)} {s : LstateMF}, TSim I P Site Q t s Post →
      TSim I P Site' Q t s Post
  | .ret none, _, _ => trivial
  | .ret (some _), _, h => h
  | .vis e c, _, ⟨k, u, hs, hsi, hc⟩ =>
      ⟨k, u, hs, hS e u hsi, fun a u' hq => TSim.siteMono hS (t := c a) (hc a u' hq)⟩

/-- **A tree whose events meet `G` is related at the call sites of events of `G`.** -/
theorem tsim_and_of_allEv {Site : E.Event → LstateMF → Prop}
    {Q : (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop} {α : Type}
    {Post : α → LstateMF → Prop} {G : E.Event → Prop} :
    ∀ {t : CallTree E (Option α)} {s : LstateMF}, AllEv G t → TSim I P Site Q t s Post →
      TSim I P (fun e u => Site e u ∧ G e) Q t s Post
  | .ret none, _, _, _ => trivial
  | .ret (some _), _, _, h => h
  | .vis _ c, _, ⟨hG, hc'⟩, ⟨k, u, hs, hsi, hc⟩ =>
      ⟨k, u, hs, ⟨hsi, hG⟩, fun a u' hq => tsim_and_of_allEv (t := c a) (hc' a) (hc a u' hq)⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (CoRel)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow retRes CallRes
  shadowCall? shadowCall?_callShadow)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (NextPc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstGuard (GuardInv takenAt_of_guardInv
  guardInv_isaStep guardInv_retRes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall (steps_of_step_rel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (resWord resArr
  arrArgsOf wordsOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallOut CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExportTransfer (TSim.transfer)

section Webs

variable {fn : String} {body : List LinstrRM} {L : Nat → List String} {obs : List String}
  {w : Nat → String → String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}

theorem tsim_websOn {I : Isa} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    (hc : webB w body L obs aa ao = true)
    {G : NFCall jasminDialect → Prop}
    (hev : ∀ e, G e →
      arrArgsOf e.argTys = aa e.name ∧ resLen e.resTys = ao e.name)
    {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', WebsRel fn body L w m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hR : WebsRel fn body L w s s')
    (h : TSim I (singletonProgM fn body)
      (fun e u => NFProgCallTreeExport.CallSite (singletonProgM fn body) e u ∧ G e)
      (CallRet (singletonProgM fn body)) t s Post) :
    TSim I (singletonProgM fn (webRen w ao body))
      (fun e u => NFProgCallTreeExport.CallSite (singletonProgM fn (webRen w ao body)) e u ∧ G e)
      (CallRet (singletonProgM fn (webRen w ao body))) t s' Post' := by
  refine TSim.transfer (WebsRel fn body L w) ?_ ?_ ?_ hpost hR h
  · intro n s t s' hs hR
    obtain ⟨t', ht', hRt⟩ := steps_of_step_rel I I (WebsRel fn body L w)
      (fun s s' u hR hu => webs_step hle hcl hc hR hu) n s s' t hR hs
    exact ⟨n, t', ht', hRt⟩
  · rintro e u u' hR ⟨hsi, hG⟩
    refine And.intro ?_ hG
    obtain ⟨hf, hpc, hg, hR, hfn, hz⟩ := hR
    obtain ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩ := hsi
    obtain ⟨haa, -⟩ := hev e hG
    have hk : u.prog.base.lpc = k := hat.2
    have hb : body[k]? = some (callShadow dst e.name srcs, tag) := hfk
    obtain ⟨hcB, hpre, -⟩ := webB_call hc hb
    have hcB' := hcB
    simp only [callB, Bool.and_eq_true] at hcB'
    obtain ⟨⟨htag, hops⟩, -⟩ := hcB'
    rw [hk] at hR
    have hRσ := coRel_congr hR (fun r hr => (hpre r hr).symm)
    refine ⟨stepRen w ao k (callShadow dst e.name srcs, tag) dst,
      srcs.map (renOpR (stepRen w ao k (callShadow dst e.name srcs, tag))), tag, k,
      ⟨hfn.trans hat.1, by rw [coRel_lpc hR, hk]⟩, ?_, by rw [List.length_map]; exact hlen, ?_⟩
    · show (webRen w ao body)[k]? = _
      rw [webRen_getElem? hb, renArr_callShadow dst e.name srcs htag]
    · rw [haa, argsRead_renOpR hRσ 0 srcs hops, ← haa]
      exact hrd
  · rintro e u u' a v' hR ⟨hsi, hG⟩ hq
    obtain ⟨hf, hpc, hg, hR, hfn, hz⟩ := hR
    obtain ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩ := hsi
    obtain ⟨-, hao⟩ := hev e hG
    have hk : u.prog.base.lpc = k := hat.2
    have hb : body[k]? = some (callShadow dst e.name srcs, tag) := hfk
    have hklt : k < body.length := (List.getElem?_eq_some_iff.mp hb).1
    obtain ⟨hcB, hpre, hsucc⟩ := webB_call hc hb
    have hcB' := hcB
    simp only [callB, Bool.and_eq_true] at hcB'
    obtain ⟨⟨htag, -⟩, -⟩ := hcB'
    rw [hk] at hR
    have hRσ := coRel_congr hR (fun r hr => (hpre r hr).symm)
    obtain ⟨dst', srcs', tag', k', res, hat', hf', rfl, hout⟩ := hq
    have hk' : k' = k := by rw [← hat'.2, coRel_lpc hR, hk]
    subst hk'
    have hf'' : (webRen w ao body)[k']? = some (callShadow dst' e.name srcs', tag') := hf'
    rw [webRen_getElem? hb, renArr_callShadow dst e.name srcs htag] at hf''
    simp only [Option.some.injEq, Prod.mk.injEq, callShadow, LinstrR.Lopn.injEq,
      List.cons.injEq, LOperand.reg.injEq, and_true] at hf''
    obtain ⟨⟨rfl, -⟩, -⟩ := hf''
    obtain ⟨rfl, hxlen, hback⟩ := callOut_retRes hout
    refine ⟨retRes dst (callResOf e.resTys res) u,
      ⟨dst, srcs, tag, k', res, hat, hfk, rfl, hback dst u⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (LprogIsa.lfn_retRes dst _ u).trans hf
    · rw [LprogIsa.lpc_retRes, hk]
      omega
    · exact guardInv_retRes hg (by rw [hk]; exact hb) rfl
    · rw [LprogIsa.lpc_retRes, hk]
      exact coRel_congr (coRel_retRes_of_callB hcB hRσ (hxlen.trans hao)) hsucc
    · rw [LprogIsa.lfn_retRes, LprogIsa.lfn_retRes]
      exact hfn
    · cases callResOf e.resTys res <;> exact hz

end Webs

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCoalesce

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (CoRel)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow retRes CallRes
  shadowCall? shadowCall?_callShadow)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (NextPc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstGuard (GuardInv takenAt_of_guardInv
  guardInv_isaStep guardInv_retRes)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall (steps_of_step_rel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (resWord resArr
  arrArgsOf wordsOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallOut CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExportTransfer (TSim.transfer)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs (callResOf resLen callOut_retRes
  coRel_retRes_of_callB)

section Coalesce

variable {σ : String → String} {fn : String} {body : List LinstrRM} {L : Nat → List String}
  {obs : List String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}

theorem tsim_coalesceOn {I : Isa} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    (hc : coCfgB σ body L obs aa ao = true)
    {G : NFCall jasminDialect → Prop}
    (hev : ∀ e, G e →
      arrArgsOf e.argTys = aa e.name ∧ resLen e.resTys = ao e.name)
    {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', CoalRel σ fn body L m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hR : CoalRel σ fn body L s s')
    (h : TSim I (singletonProgM fn body)
      (fun e u => NFProgCallTreeExport.CallSite (singletonProgM fn body) e u ∧ G e)
      (CallRet (singletonProgM fn body)) t s Post) :
    TSim I (singletonProgM fn (body.map (renArr σ)))
      (fun e u => NFProgCallTreeExport.CallSite (singletonProgM fn (body.map (renArr σ))) e u ∧ G e)
      (CallRet (singletonProgM fn (body.map (renArr σ)))) t s' Post' := by
  refine TSim.transfer (CoalRel σ fn body L) ?_ ?_ ?_ hpost hR h
  · intro n s t s' hs hR
    obtain ⟨t', ht', hRt⟩ := steps_of_step_rel I I (CoalRel σ fn body L)
      (fun s s' u hR hu => coal_step hle hcl hc hR hu) n s s' t hR hs
    exact ⟨n, t', ht', hRt⟩
  · rintro e u u' hR ⟨hsi, hG⟩
    refine And.intro ?_ hG
    obtain ⟨hf, hpc, hg, hR, hfn, hz⟩ := hR
    obtain ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩ := hsi
    obtain ⟨haa, -⟩ := hev e hG
    have hk : u.prog.base.lpc = k := hat.2
    have hb : body[k]? = some (callShadow dst e.name srcs, tag) := hfk
    have hcB := coCfgB_call hc hb
    have hcB' := hcB
    simp only [callB, Bool.and_eq_true] at hcB'
    obtain ⟨⟨htag, hops⟩, -⟩ := hcB'
    rw [hk] at hR
    refine ⟨σ dst, srcs.map (renOpR σ), tag, k,
      ⟨hfn.trans hat.1, by rw [coRel_lpc hR, hk]⟩, ?_, by rw [List.length_map]; exact hlen, ?_⟩
    · show (body.map (renArr σ))[k]? = _
      rw [List.getElem?_map, hb, Option.map_some, renArr_callShadow dst e.name srcs htag]
    · rw [haa, argsRead_renOpR hR 0 srcs hops, ← haa]
      exact hrd
  · rintro e u u' a v' hR ⟨hsi, hG⟩ hq
    obtain ⟨hf, hpc, hg, hR, hfn, hz⟩ := hR
    obtain ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩ := hsi
    obtain ⟨-, hao⟩ := hev e hG
    have hk : u.prog.base.lpc = k := hat.2
    have hb : body[k]? = some (callShadow dst e.name srcs, tag) := hfk
    have hklt : k < body.length := (List.getElem?_eq_some_iff.mp hb).1
    have hcB := coCfgB_call hc hb
    have hcB' := hcB
    simp only [callB, Bool.and_eq_true] at hcB'
    obtain ⟨⟨htag, -⟩, -⟩ := hcB'
    rw [hk] at hR
    obtain ⟨dst', srcs', tag', k', res, hat', hf', rfl, hout⟩ := hq
    have hk' : k' = k := by rw [← hat'.2, coRel_lpc hR, hk]
    subst hk'
    have hf'' : (body.map (renArr σ))[k']? = some (callShadow dst' e.name srcs', tag') := hf'
    rw [List.getElem?_map, hb, Option.map_some, renArr_callShadow dst e.name srcs htag] at hf''
    simp only [Option.some.injEq, Prod.mk.injEq, callShadow, LinstrR.Lopn.injEq,
      List.cons.injEq, LOperand.reg.injEq, and_true] at hf''
    obtain ⟨⟨rfl, -⟩, -⟩ := hf''
    obtain ⟨rfl, hxlen, hback⟩ := callOut_retRes hout
    refine ⟨retRes dst (callResOf e.resTys res) u,
      ⟨dst, srcs, tag, k', res, hat, hfk, rfl, hback dst u⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (LprogIsa.lfn_retRes dst _ u).trans hf
    · rw [LprogIsa.lpc_retRes, hk]
      omega
    · exact guardInv_retRes hg (by rw [hk]; exact hb) rfl
    · rw [LprogIsa.lpc_retRes, hk]
      exact coRel_retRes_of_callB hcB hR (hxlen.trans hao)
    · rw [LprogIsa.lfn_retRes, LprogIsa.lfn_retRes]
      exact hfn
    · cases callResOf e.resTys res <;> exact hz

end Coalesce

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCoalesce

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeLive

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renOperand)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow retRes CallRes lpc_retRes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall (steps_of_step_rel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (arrArgsOf wordsOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallOut CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExportTransfer (TSim.transfer)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs (callResOf resLen callOut_retRes)

section Live

variable {σ : String → String} {k0 : Nat} {P P' : LprogM} {Lr La : Nat → String → Prop}

theorem tsim_liveOn {I : Isa} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao) (hC : LiveCert σ k0 P P' Lr La)
    (hK : LiveCalls σ k0 P Lr La aa ao)
    {G : NFCall jasminDialect → Prop}
    (hev : ∀ e, G e →
      arrArgsOf e.argTys = aa e.name ∧ resLen e.resTys = ao e.name)
    {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', LiveRel σ Lr La k0 m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hR : LiveRel σ Lr La k0 s s')
    (h : TSim I P (fun e u => NFProgCallTreeExport.CallSite P e u ∧ G e) (CallRet P) t s Post) :
    TSim I P' (fun e u => NFProgCallTreeExport.CallSite P' e u ∧ G e) (CallRet P') t s' Post' := by
  refine TSim.transfer (LiveRel σ Lr La k0) ?_ ?_ ?_ hpost hR h
  · intro n s t s' hs hR
    obtain ⟨t', ht', hRt⟩ := steps_of_step_rel I I (LiveRel σ Lr La k0)
      (fun s s' u hR hu => live_step hle hcl hC hK hR hu) n s s' t hR hs
    exact ⟨n, t', ht', hRt⟩
  · rintro e u u' hR ⟨⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩, hG⟩
    refine And.intro ?_ hG
    obtain ⟨haa, -⟩ := hev e hG
    have hk0 : k0 ≤ k := hat.2 ▸ hR.2
    have hu := hC.uses _ _ hk0 hfk
    obtain ⟨hcA, -⟩ := hK _ _ dst e.name srcs hk0 hfk rfl
    obtain ⟨⟨hRn, hRa, hRm⟩, hfn, -⟩ := hR.1
    rw [hat.2] at hRn hRa
    refine ⟨σ dst, srcs.map (renOperand σ), tag, k,
      ⟨hfn.trans (hat.1.trans hC.lfn.symm), by rw [← hat.2]; exact hR.1.1.1.1⟩, ?_,
      by rw [List.length_map]; exact hlen, ?_⟩
    · rw [hC.body k hk0, hfk]
      rfl
    · rw [haa, argsRead_ren ⟨hRn, hRa, hRm⟩ 0 srcs
        (fun o ho n hn => hu n (List.mem_flatMap.mpr ⟨o, ho, hn⟩))
        (fun m n A h1 h2 => hcA m n A (by simpa using h1) h2), ← haa]
      exact hrd
  · rintro e u u' a v' hR ⟨⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩, hG⟩
      ⟨dst', srcs', tag', k', res, hat', hf', rfl, hout⟩
    obtain ⟨-, hao⟩ := hev e hG
    have hk0 : k0 ≤ k := hat.2 ▸ hR.2
    have hk' : k' = k := by rw [← hat'.2, ← hat.2]; exact hR.1.1.1.1
    subst hk'
    have hb' : P'.body[k']? = some (callShadow (σ dst) e.name (srcs.map (renOperand σ)), tag) := by
      rw [hC.body k' hk0, hfk]
      rfl
    rw [hb'] at hf'
    simp only [Option.some.injEq, Prod.mk.injEq, callShadow, LinstrR.Lopn.injEq,
      List.cons.injEq, LOperand.reg.injEq, and_true] at hf'
    obtain ⟨⟨rfl, -⟩, -⟩ := hf'
    obtain ⟨rfl, hxlen, hback⟩ := callOut_retRes hout
    have hKr := hC.fallR _ _ hk0 hfk
    have hKa := hC.fallA _ _ hk0 hfk
    obtain ⟨-, hcO⟩ := hK _ _ dst e.name srcs hk0 hfk rfl
    rw [regDefs_callShadow] at hKr
    rw [arrDefs_callShadow] at hKa
    obtain ⟨⟨hRn, hRa, hRm⟩, hfn, hz, hcf, hof⟩ := hR.1
    rw [hat.2] at hRn hRa
    refine ⟨retRes dst (callResOf e.resTys res) u,
      ⟨dst, srcs, tag, k', res, hat, hfk, rfl, hback dst u⟩, ?_, ?_⟩
    · rw [lpc_retRes, hat.2]
      cases hx : callResOf e.resTys res with
      | word r =>
          exact ⟨⟨relN_setReg_keeps hRn hKr r, fun a ha => hRa a (hKa.sub a ha), hRm⟩, hfn,
            hz, hcf, hof⟩
      | arr a =>
          rw [hx] at hxlen
          obtain ⟨hd, hKa'⟩ := hcO _ (hao.symm.trans hxlen.symm)
          have hsub : ∀ r, Lr (k' + 1) r → Lr k' r := fun r hr => by
            rcases hKr r hr with h1 | h1
            · obtain rfl : dst = r := by simpa using h1
              exact hd
            · exact h1.1
          exact ⟨RelM2.setArr_keeps ⟨hRn, hRa, hRm⟩ hKa' hsub a, hfn, hz, hcf, hof⟩
    · rw [lpc_retRes]
      exact Nat.le_succ_of_le hR.2

end Live

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeLive

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSelfNop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renOperand)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow retRes CallRes lpc_retRes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (NextPc)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall (steps_of_step_rel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (arrArgsOf wordsOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallOut CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExportTransfer (TSim.transfer)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs (callResOf resLen callOut_retRes)

section SelfNop

variable {fn : String} {B : List LinstrRM} {k0 : Nat} {Lr : Nat → List String}
  {AN : List String}

theorem tsim_selfNopOn {I : Isa} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao) {P₁ : LprogM}
    (hC : LiveCert id k0 (singletonProgM fn B) P₁ (fun k r => r ∈ Lr k) (fun _ r => r ∈ AN))
    (hK : LiveCalls id k0 (singletonProgM fn B) (fun k r => r ∈ Lr k) (fun _ r => r ∈ AN) aa ao)
    {G : NFCall jasminDialect → Prop}
    (hev : ∀ e, G e →
      arrArgsOf e.argTys = aa e.name ∧ resLen e.resTys = ao e.name)
    {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', NopRel fn B k0 Lr AN m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hR : NopRel fn B k0 Lr AN s s')
    (h : TSim I (singletonProgM fn B)
      (fun e u => NFProgCallTreeExport.CallSite (singletonProgM fn B) e u ∧ G e)
      (CallRet (singletonProgM fn B)) t s Post) :
    TSim I (singletonProgM fn (selfNop k0 Lr B))
      (fun e u => NFProgCallTreeExport.CallSite (singletonProgM fn (selfNop k0 Lr B)) e u ∧ G e)
      (CallRet (singletonProgM fn (selfNop k0 Lr B))) t s' Post' := by
  -- a call site is a state of `NopNorm`
  have hnorm : ∀ {e u u'}, NopRel fn B k0 Lr AN u u' →
      NFProgCallTreeExport.CallSite (singletonProgM fn B) e u → NopNorm fn B k0 Lr AN u u' := by
    rintro e u u' (hN | ⟨s₀, s₀', t, a, z, sc, w, n, -, -, -, hj, -, -, hld, -⟩)
      ⟨dst, srcs, tag, k, hat, hfk, -, -⟩
    · exact hN
    · exfalso
      have hnx := X86Backend.AllocCheck.LcmdCFG.evalInstrPMemF_next _ _ s₀ u hld
      have hk : k = s₀.prog.base.lpc + 1 := hat.2.symm.trans hnx.2
      have hfk' : B[k]? = some (callShadow dst e.name srcs, tag) := hfk
      rw [hk, hj] at hfk'
      have h1 := congrArg (fun i : LinstrRM => LprogIsa.shadowCall? i.1) (Option.some.inj hfk')
      simp only [LprogIsa.shadowCall?_callShadow] at h1
      exact absurd h1.symm (by simp only [LprogIsa.shadowCall?]; exact nofun)
  refine TSim.transfer (NopRel fn B k0 Lr AN) ?_ ?_ ?_ hpost hR h
  · intro n s t s' hs hR
    obtain ⟨t', ht', hRt⟩ := steps_of_step_rel I I (NopRel fn B k0 Lr AN)
      (fun s s' u hR hu => nop_step hle hcl hC hK hR hu) n s s' t hR hs
    exact ⟨n, t', ht', hRt⟩
  · rintro e u u' hR ⟨hsi, hG⟩
    refine And.intro ?_ hG
    obtain ⟨⟨⟨hRn, hRa, hRm⟩, hfn', -⟩, hk0, hsec, hfn⟩ := hnorm hR hsi
    obtain ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩ := hsi
    obtain ⟨haa, -⟩ := hev e hG
    have hpc' : u'.prog.base.lpc = u.prog.base.lpc := hRn.1
    rw [hat.2] at hRn hk0 hsec
    have hu := hC.uses _ _ hk0 hfk
    obtain ⟨hcA, -⟩ := hK _ _ dst e.name srcs hk0 hfk rfl
    have hid : srcs.map (renOperand id) = srcs := by
      have : renOperand id = fun o => o := by
        funext o
        cases o <;> rfl
      rw [this, List.map_id']
    have hrd' := argsRead_ren (σ := id) ⟨hRn, hRa, hRm⟩ 0 srcs
      (fun o ho n hn => hu n (List.mem_flatMap.mpr ⟨o, ho, hn⟩))
      (fun m n A h1 h2 => hcA m n A (by simpa using h1) h2)
    rw [hid] at hrd'
    refine ⟨dst, srcs, tag, k, ⟨hfn'.trans hat.1, by rw [hpc', hat.2]⟩,
      selfNop_getElem?_callShadow (B := B) hfk hsec, hlen, ?_⟩
    rw [haa, hrd', ← haa]
    exact hrd
  · rintro e u u' a v' hR ⟨hsi, hG⟩ hq
    obtain ⟨⟨⟨hRn, hRa, hRm⟩, hfn', hz, hcf, hof⟩, hk0, hsec, hfn⟩ := hnorm hR hsi
    obtain ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩ := hsi
    obtain ⟨-, hao⟩ := hev e hG
    have hpc' : u'.prog.base.lpc = u.prog.base.lpc := hRn.1
    rw [hat.2] at hRn hk0 hsec
    obtain ⟨dst', srcs', tag', k', res, hat', hf', rfl, hout⟩ := hq
    have hk' : k' = k := by rw [← hat'.2, hpc', hat.2]
    subst hk'
    have hfk' : (selfNop k0 Lr B)[k']? = some (callShadow dst' e.name srcs', tag') := hf'
    rw [selfNop_getElem?_callShadow (B := B) hfk hsec] at hfk'
    simp only [Option.some.injEq, Prod.mk.injEq, callShadow, LinstrR.Lopn.injEq,
      List.cons.injEq, LOperand.reg.injEq, and_true] at hfk'
    obtain ⟨⟨rfl, -⟩, -⟩ := hfk'
    obtain ⟨rfl, hxlen, hback⟩ := callOut_retRes hout
    have hKr := hC.fallR _ _ hk0 hfk
    have hKa := hC.fallA _ _ hk0 hfk
    obtain ⟨-, hcO⟩ := hK _ _ dst e.name srcs hk0 hfk rfl
    rw [regDefs_callShadow] at hKr
    rw [arrDefs_callShadow] at hKa
    refine ⟨retRes dst (callResOf e.resTys res) u,
      ⟨dst, srcs, tag, k', res, hat, hfk, rfl, hback dst u⟩, .inl ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [lpc_retRes, hat.2]
      cases hx : callResOf e.resTys res with
      | word r =>
          exact ⟨⟨relN_setReg_keeps hRn hKr r, fun a ha => hRa a (hKa.sub a ha), hRm⟩,
            (LprogIsa.lfn_retRes _ _ _).trans
              (hfn'.trans (LprogIsa.lfn_retRes _ _ _).symm), hz, hcf, hof⟩
      | arr a =>
          rw [hx] at hxlen
          obtain ⟨hd, hKa'⟩ := hcO _ (hao.symm.trans hxlen.symm)
          have hsub : ∀ r, r ∈ Lr (k' + 1) → r ∈ Lr k' := fun r hr => by
            rcases hKr r hr with h1 | h1
            · obtain rfl : dst = r := by simpa using h1
              exact hd
            · exact h1.1
          exact ⟨RelM2.setArr_keeps ⟨hRn, hRa, hRm⟩ hKa' hsub a,
            (LprogIsa.lfn_retRes _ _ _).trans
              (hfn'.trans (LprogIsa.lfn_retRes _ _ _).symm), hz, hcf, hof⟩
    · rw [lpc_retRes, hat.2]
      omega
    · rw [lpc_retRes, hat.2, show k' + 1 - 1 = k' from rfl, selfPairB_callShadow (B := B) hfk,
        Bool.and_false]
    · exact (LprogIsa.lfn_retRes _ _ _).trans hfn

end SelfNop

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSelfNop

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCommon

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallRet)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (arrArgsOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs (resLen)

/-- **The rewriting onto common names at the call sites of events of `G`.** As `tsim_common`,
    with the shape condition on the events of `G` only. -/
theorem tsim_commonOn {T : ProcTable}
    {tab : String → Option (CallShape × List String × String)}
    {N : List String} {fn : String} {B B' : List LinstrRM} (hB : commonCallsT? tab B = some B')
    (hc : CommonSimT T tab N B) {G : NFCall jasminDialect → Prop}
    (hev : ∀ e, G e → ∀ sh args res, tab e.name = some (sh, args, res) →
        (∀ i, sh.arrArgs i = none → arrArgsOf e.argTys i = none)
        ∧ (sh.out = false → resLen e.resTys = none))
    {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', OffRel N (expPosT tab B) m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hr : OffRel N (expPosT tab B) s s')
    (h : TSim x86Isa (singletonProgM fn B)
      (fun e u => NFProgCallTreeExport.CallSite (singletonProgM fn B) e u ∧ G e)
      (CallRet (singletonProgM fn B)) t s Post) :
    TSim x86Isa (singletonProgM fn B')
      (fun e u => NFProgCallTreeExport.CallSite (singletonProgM fn B') e u ∧ G e)
      (CallRet (singletonProgM fn B')) t s' Post' := by
  refine TSim.transfer' (OffRel N (expPosT tab B)) ?_ (fun e u u' hr hsi => ?_) hpost hr h
  · intro n s t s' hs hr
    obtain ⟨t', ht', hrt⟩ := Ascent.IsaCall.steps_of_step_rel x86Isa x86Isa
      (OffRel N (expPosT tab B)) (fun s s' u hr hu => common_step_x86 hB hc hu hr) n s s' t hr
      hs
    exact ⟨n, t', ht', hrt⟩
  · obtain ⟨k, u'', hs, hsi', hans⟩ := common_site hB hc hr hsi.1 (hev e hsi.2)
    exact ⟨k, u'', hs, ⟨hsi', hsi.2⟩, hans⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCommon
