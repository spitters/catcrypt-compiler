/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExportTransfer
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs

/-!
# Call trees related to the runs of a body with its array names split into webs

The pass `ArrWebs.arrWebs` renames the array positions of a body by a position map `w`
(`ArrWebs.webRen`), accepted by the check `ArrWebs.webB`. Its correctness for halting runs is
`ArrWebs.lsemFuelMemF_webs`, by the step simulation `ArrWebs.step_webs` under the relation of
the states through `w` at the live names. The same relation (`WebsRel`) carries a call tree
related to the states of the body by `NFProgCallTreeExport.TSim`, at the call sites and the
states after the calls, to the states of the renamed body (`tsim_webs`). A call site of the
body is a call site of the renamed body, whose renamed operands read the same words, when the
array positions of the arguments of the event are those the check expects; and a state after
a call of the renamed body is related to the state after the call of the body at the same
answer, when the length of the answer is the result length the check expects.

## Main definitions

* `callResOf`, `resLen`: the result of a call at a valuation of word or word-array results, and
  its length.
* `WebsRel`: the relation of the states of the body and of the renamed body.

## Main results

* `callOut_retRes`: the state after a call is `LprogIsa.retRes` of the result of the answer.
* `coRel_retRes_of_callB`: the states after a call accepted by `callB` are related at the names
  live after it, at every result of the declared length.
* `webs_step`: a step of the body is matched by a step of the renamed body.
* `tsim_webs`: a call tree related to a state of the body is related to every state of the
  renamed body that `WebsRel` relates to it.
-/

@[expose] public section

set_option autoImplicit false

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

/-! ## The result of a call -/

/-- The result of a call at a valuation of a word result or of a word-array result. -/
def callResOf : (rs : List JasminTy) → Ctxt.Valuation (d := jasminDialect) rs → CallRes
  | [.reg 64], v => .word (resWord v)
  | [.stackArr 64 _], v => .arr (resArr v)
  | _, _ => .word 0

/-- The length of the result of a call of the result types `rs`. -/
def resLen : List JasminTy → Option Nat
  | [.reg 64] => none
  | [.stackArr 64 n] => some n
  | _ => none

/-- **The state after a call is the state after the result of the answer.** The state after a
    call of the answer `v` from `u` is `retRes` of the result of `v`, whose length is that of
    the result types, and at every destination and state that result gives a state after the
    call. -/
theorem callOut_retRes {dst : String} :
    ∀ {rs : List JasminTy} {v : Ctxt.Valuation (d := jasminDialect) rs} {u u' : LstateMF},
      CallOut dst rs v u u' →
      u' = retRes dst (callResOf rs v) u ∧ (callResOf rs v).len = resLen rs
      ∧ ∀ (dst' : String) (u₂ : LstateMF),
        CallOut dst' rs v u₂ (retRes dst' (callResOf rs v) u₂) := by
  intro rs v u u' h
  unfold CallOut at h
  split at h
  · exact ⟨h, rfl, fun _ _ => rfl⟩
  · exact ⟨h, rfl, fun _ _ => rfl⟩
  · exact h.elim

/-! ## The states after an accepted call -/

/-- **The states after a call accepted by `callB` are related**, at every result of the
    declared length, at the names live after the call. -/
theorem coRel_retRes_of_callB {σ : String → String} {L : Nat → List String} {k : Nat}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {tag : MemTag}
    {dst f : String} {srcs : List LOperand} {x : CallRes} {s s' : LstateMF}
    (hc : callB σ L k aa ao tag dst f srcs = true)
    (hR : CoRel σ (L k) s.prog.base s'.prog.base) (hlen : x.len = ao f) :
    CoRel σ (L (k + 1)) (retRes dst x s).prog.base (retRes (σ dst) x s').prog.base := by
  simp only [callB, Bool.and_eq_true] at hc
  obtain ⟨-, hres⟩ := hc
  cases x with
  | word r =>
      rw [← hlen] at hres
      simp only [CallRes.len, Bool.and_eq_true, beq_iff_eq] at hres
      rw [LprogIsa.retRes_word, LprogIsa.retRes_word, hres.1]
      exact coRel_nextPc (coRel_setReg (hR.mono (subB_spec hres.2)) dst r)
  | arr a =>
      rw [← hlen] at hres
      simp only [CallRes.len, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
        bne_iff_ne, ne_eq] at hres
      obtain ⟨hcl, hsub⟩ := hres
      refine ⟨?_, hR.mem, hR.cf, hR.of, fun r hr => ?_⟩
      · simp only [LprogIsa.retRes_arr, LprogIsa.retArr, LstateM.nextPc, LstateM.setArr, hR.reg]
      · simp only [LprogIsa.retRes_arr, LprogIsa.retArr, LstateM.nextPc, LstateM.setArr]
        by_cases hrd : r = dst
        · subst hrd
          simp
        · have hne : σ r ≠ σ dst := by
            rcases hcl r hr with h' | h'
            · exact absurd h' hrd
            · exact h'
          simp only [hne, hrd, ite_false]
          exact hR.arr r (subB_spec hsub r (List.mem_filter.mpr ⟨hr, by simpa using hrd⟩))

/-! ## The relation of the states -/

section Webs

variable {fn : String} {body : List LinstrRM} {L : Nat → List String} {obs : List String}
  {w : Nat → String → String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}

/-- **The relation of a state of the body and a state of the renamed body**: the state of the
    body is in the function `fn` at a position at most the length of the body and satisfies the
    invariant of the constant guards, and the states agree through `w` at that position on the
    names live there, with the same function name and zero flag. -/
def WebsRel (fn : String) (body : List LinstrRM) (L : Nat → List String)
    (w : Nat → String → String) (s s' : LstateMF) : Prop :=
  s.prog.lfn = fn ∧ s.prog.base.lpc ≤ body.length ∧ GuardInv body s
    ∧ CoRel (w s.prog.base.lpc) (L s.prog.base.lpc) s.prog.base s'.prog.base
    ∧ s'.prog.lfn = s.prog.lfn ∧ s'.zf = s.zf

/-- The instruction of the renamed body at a position is the renamed instruction. -/
theorem webRen_getElem? {k : Nat} {i : LinstrRM} (hb : body[k]? = some i) :
    (webRen w ao body)[k]? = some (renArr (stepRen w ao k i) i) := by
  simp only [webRen, List.getElem?_mapIdx, hb, Option.map_some]

/-- **A step of the body is matched by a step of the renamed body.** -/
theorem webs_step {I : Isa} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    (hc : webB w body L obs aa ao = true) {s s' u : LstateMF}
    (hR : WebsRel fn body L w s s')
    (h : I.lsemStepPMemF (singletonProgM fn body) s = some u) :
    ∃ u', I.lsemStepPMemF (singletonProgM fn (webRen w ao body)) s' = some u'
      ∧ WebsRel fn body L w u u' := by
  obtain ⟨hf, hpc, hg, hR, hfn, hz⟩ := hR
  unfold Isa.lsemStepPMemF at h ⊢
  rw [findInstrMem_singleton fn body s.prog hf] at h
  rw [findInstrMem_singleton fn _ s'.prog (hfn.trans hf), coRel_lpc hR]
  cases hb : body[s.prog.base.lpc]? with
  | none => rw [hb] at h; cases h
  | some i =>
      rw [hb] at h
      obtain ⟨u', hu', hRu, hfu, hfs, hzu, hleu⟩ := step_webs hle hcl
        (webB_instr hc hb) (List.getElem?_eq_some_iff.mp hb).1
        (takenAt_of_guardInv hg hb) hR hfn hz h
      refine ⟨u', ?_, hfs.trans hf, hleu, guardInv_isaStep hcl hg hb h, hRu, hfu, hzu⟩
      rw [webRen_getElem? hb]
      exact hu'

/-- The check of a call instruction of an accepted body: the call passes `callB` under its step
    renaming, which agrees with `w k` on the names live at `k` and with `w (k + 1)` on the names
    live at `k + 1`. -/
theorem webB_call (hc : webB w body L obs aa ao = true) {k : Nat} {dst f : String}
    {srcs : List LOperand} {tag : MemTag}
    (hb : body[k]? = some (callShadow dst f srcs, tag)) :
    callB (stepRen w ao k (callShadow dst f srcs, tag)) L k aa ao tag dst f srcs = true
      ∧ (∀ r ∈ L k, stepRen w ao k (callShadow dst f srcs, tag) r = w k r)
      ∧ (∀ r ∈ L (k + 1), stepRen w ao k (callShadow dst f srcs, tag) r = w (k + 1) r) := by
  have hci := webB_instr hc hb
  unfold webInstrB at hci
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hci
  obtain ⟨⟨⟨hco, hpre⟩, hsucc⟩, -⟩ := hci
  refine ⟨?_, hpre, hsucc (k + 1) (mem_webSuccs_of_nextPc (by simp [callShadow, NextPc]))⟩
  unfold coInstrB at hco
  simpa only [shadowCall?_callShadow] using hco

/-- **A call tree related to the states of the body is related to the states of the renamed
    body.** Let `I` have the steps of `x86Isa` and local calls at `aa` and `ao`, the body pass
    `webB`, and every event at a call site of the body have the array positions `aa` and the
    result length `ao` of its symbol. A tree related by `TSim` to `s` at the call sites and the
    states after the calls of the body is related to every state `s'` that `WebsRel` relates to
    `s`, at the call sites and the states after the calls of the renamed body, at every end
    condition that `WebsRel` carries `Post` to. -/
theorem tsim_webs {I : Isa} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    (hc : webB w body L obs aa ao = true)
    (hev : ∀ e u, NFProgCallTreeExport.CallSite (singletonProgM fn body) e u →
      arrArgsOf e.argTys = aa e.name ∧ resLen e.resTys = ao e.name)
    {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', WebsRel fn body L w m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hR : WebsRel fn body L w s s')
    (h : TSim I (singletonProgM fn body) (NFProgCallTreeExport.CallSite (singletonProgM fn body))
      (CallRet (singletonProgM fn body)) t s Post) :
    TSim I (singletonProgM fn (webRen w ao body))
      (NFProgCallTreeExport.CallSite (singletonProgM fn (webRen w ao body)))
      (CallRet (singletonProgM fn (webRen w ao body))) t s' Post' := by
  refine TSim.transfer (WebsRel fn body L w) ?_ ?_ ?_ hpost hR h
  · intro n s t s' hs hR
    obtain ⟨t', ht', hRt⟩ := steps_of_step_rel I I (WebsRel fn body L w)
      (fun s s' u hR hu => webs_step hle hcl hc hR hu) n s s' t hR hs
    exact ⟨n, t', ht', hRt⟩
  · intro e u u' hR hsi
    obtain ⟨hf, hpc, hg, hR, hfn, hz⟩ := hR
    obtain ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩ := hsi
    obtain ⟨haa, -⟩ := hev e u ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
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
  · intro e u u' a v' hR hsi hq
    obtain ⟨hf, hpc, hg, hR, hfn, hz⟩ := hR
    obtain ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩ := hsi
    obtain ⟨-, hao⟩ := hev e u ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
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
