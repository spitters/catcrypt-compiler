/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs

/-!
# Call trees related to the runs of a coalesced body

The coalescing of the array names of a body by an alias map `σ` (`body.map (renArr σ)`),
accepted by `ImageCoalesceCfg.coCfgB`, is correct for halting runs by
`ImageCoalesceCfg.lsemFuelMemF_coalesce_calls`, through the step simulation
`ImageCoalesceCfg.step_coalesce_calls` under the relation of the states through `σ` at the
live names. The same relation (`CoalRel`) carries a call tree related to the states of the body
by `NFProgCallTreeExport.TSim`, at the call sites and the states after the calls, to the states
of the coalesced body (`tsim_coalesce`), when the array positions of the arguments of each event
and the length of its result are those the check expects.

## Main definitions

* `CoalRel`: the relation of the states of the body and of the coalesced body.

## Main results

* `coal_step`: a step of the body is matched by a step of the coalesced body.
* `tsim_coalesce`: a call tree related to a state of the body is related to every state of the
  coalesced body that `CoalRel` relates to it.
-/

@[expose] public section

set_option autoImplicit false

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

/-- **The relation of a state of the body and a state of the coalesced body**: the state of
    the body is in the function `fn` at a position at most the length of the body and satisfies
    the invariant of the constant guards, and the states agree through `σ` on the names live at
    that position, with the same function name and zero flag. -/
def CoalRel (σ : String → String) (fn : String) (body : List LinstrRM) (L : Nat → List String)
    (s s' : LstateMF) : Prop :=
  s.prog.lfn = fn ∧ s.prog.base.lpc ≤ body.length ∧ GuardInv body s
    ∧ CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base
    ∧ s'.prog.lfn = s.prog.lfn ∧ s'.zf = s.zf

/-- **A step of the body is matched by a step of the coalesced body.** -/
theorem coal_step {I : Isa} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    (hc : coCfgB σ body L obs aa ao = true) {s s' u : LstateMF}
    (hR : CoalRel σ fn body L s s')
    (h : I.lsemStepPMemF (singletonProgM fn body) s = some u) :
    ∃ u', I.lsemStepPMemF (singletonProgM fn (body.map (renArr σ))) s' = some u'
      ∧ CoalRel σ fn body L u u' := by
  obtain ⟨hf, hpc, hg, hR, hfn, hz⟩ := hR
  unfold Isa.lsemStepPMemF at h ⊢
  rw [findInstrMem_singleton fn body s.prog hf] at h
  rw [findInstrMem_singleton fn _ s'.prog (hfn.trans hf), coRel_lpc hR, List.getElem?_map]
  cases hb : body[s.prog.base.lpc]? with
  | none => rw [hb] at h; cases h
  | some i =>
      rw [hb] at h
      obtain ⟨u', hu', hRu, hfu, hfs, hzu, hleu⟩ := step_coalesce_calls hle hcl
        (coCfgB_instr hc hb) (List.getElem?_eq_some_iff.mp hb).1
        (takenAt_of_guardInv hg hb) hR hfn hz h
      exact ⟨u', hu', hfs.trans hf, hleu, guardInv_isaStep hcl hg hb h, hRu, hfu, hzu⟩

/-- The check of a call instruction of an accepted body is `callB`. -/
theorem coCfgB_call (hc : coCfgB σ body L obs aa ao = true) {k : Nat} {dst f : String}
    {srcs : List LOperand} {tag : MemTag}
    (hb : body[k]? = some (callShadow dst f srcs, tag)) :
    callB σ L k aa ao tag dst f srcs = true := by
  have hco := coCfgB_instr hc hb
  unfold coInstrB at hco
  simpa only [shadowCall?_callShadow] using hco

/-- **A call tree related to the states of the body is related to the states of the coalesced
    body.** Let `I` have the steps of `x86Isa` and local calls at `aa` and `ao`, the body pass
    `coCfgB`, and every event at a call site of the body have the array positions `aa` and the
    result length `ao` of its symbol. A tree related by `TSim` to `s` at the call sites and the
    states after the calls of the body is related to every state `s'` that `CoalRel` relates to
    `s`, at the call sites and the states after the calls of the coalesced body, at every end
    condition that `CoalRel` carries `Post` to. -/
theorem tsim_coalesce {I : Isa} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    (hc : coCfgB σ body L obs aa ao = true)
    (hev : ∀ e u, NFProgCallTreeExport.CallSite (singletonProgM fn body) e u →
      arrArgsOf e.argTys = aa e.name ∧ resLen e.resTys = ao e.name)
    {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', CoalRel σ fn body L m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hR : CoalRel σ fn body L s s')
    (h : TSim I (singletonProgM fn body) (NFProgCallTreeExport.CallSite (singletonProgM fn body))
      (CallRet (singletonProgM fn body)) t s Post) :
    TSim I (singletonProgM fn (body.map (renArr σ)))
      (NFProgCallTreeExport.CallSite (singletonProgM fn (body.map (renArr σ))))
      (CallRet (singletonProgM fn (body.map (renArr σ)))) t s' Post' := by
  refine TSim.transfer (CoalRel σ fn body L) ?_ ?_ ?_ hpost hR h
  · intro n s t s' hs hR
    obtain ⟨t', ht', hRt⟩ := steps_of_step_rel I I (CoalRel σ fn body L)
      (fun s s' u hR hu => coal_step hle hcl hc hR hu) n s s' t hR hs
    exact ⟨n, t', ht', hRt⟩
  · intro e u u' hR hsi
    obtain ⟨hf, hpc, hg, hR, hfn, hz⟩ := hR
    obtain ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩ := hsi
    obtain ⟨haa, -⟩ := hev e u ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
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
  · intro e u u' a v' hR hsi hq
    obtain ⟨hf, hpc, hg, hR, hfn, hz⟩ := hR
    obtain ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩ := hsi
    obtain ⟨-, hao⟩ := hev e u ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
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
