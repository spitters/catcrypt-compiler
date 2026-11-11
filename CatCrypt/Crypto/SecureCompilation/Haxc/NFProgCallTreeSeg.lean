/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs

/-!
# Segments of a body from call trees related to its states

A call tree related by `NFProgCallTreeExport.TSim` to a state of a body gives the segments of
the body that `LprogCallCut` cuts at the shadow instructions of the calls of a procedure table:
at an event whose symbol has a summary in the table, a run of steps to a shadow instruction of
the table (`LprogCallCut.SegTo` to `some p`), and at a leaf whose end condition implies a halted
state, a run to a halted state (`SegTo` to `none`). The step of a summary at the call
(`LprogCallCut.Glue`) is a state after the call of the event (`NFProgCallTreeExport.CallRet`)
at the answer whose result the summary computes on the argument words of the event.

## Main results

* `segTo_of_tsim_vis`, `segTo_of_tsim_ret`: the segments of a body from a related call tree.
* `callRet_of_glue`: the step of a summary that computes the result of an answer on the
  argument words of the event is a state after the call at that answer.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSeg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa ProcTable ProcSummary callShadow retRes
  CallRes procCall? procStep procCall?_callShadow)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (SegTo Glue isProcB)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (arrArgsOf wordsOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallOut CallRet)

variable {I : Isa} {T : ProcTable} {P : LprogM}

/-- **The segment to the call of an event.** If an event `ev`, whose symbol has a summary in
    `T`, is related by `TSim` to `s`, a segment of `P` from `s` reaches a shadow instruction of
    `T` at a state `u` at a call site of `ev`, and every state after the call of `ev` from `u`
    at an answer is related to the continuation at that answer. -/
theorem segTo_of_tsim_vis {α : Type} {ev : NFCall jasminDialect}
    {c : Option (Ctxt.Valuation (d := jasminDialect) ev.resTys) →
      CallTree (nfCallSig jasminDialect) (Option α)}
    {s : LstateMF} {Post : α → LstateMF → Prop} (hT : (T ev.name).isSome = true)
    (h : TSim I P (NFProgCallTreeExport.CallSite P) (CallRet P)
      (CallTree.vis (E := nfCallSig jasminDialect) ev c) s Post) :
    ∃ p u, SegTo I T P s (some p) u ∧ NFProgCallTreeExport.CallSite P ev u
      ∧ ∀ a u', CallRet P ev u a u' →
        TSim I P (NFProgCallTreeExport.CallSite P) (CallRet P) (c a) u' Post := by
  obtain ⟨k, u, hs, hsi, hc⟩ := h
  obtain ⟨dst, srcs, tag, p, hat, hf, hlen, hrd⟩ := hsi
  refine ⟨p, u, ⟨k, hs, hat, _, hf, ?_⟩, ⟨dst, srcs, tag, p, hat, hf, hlen, hrd⟩, hc⟩
  simp only [isProcB, procCall?_callShadow, Option.isSome_map, hT]

/-- **The segment to the end.** If a leaf `some r` is related by `TSim` to `s` at an end
    condition that implies a halted state, a segment of `P` from `s` reaches a halted state at
    which the end condition holds. -/
theorem segTo_of_tsim_ret {α : Type} {r : α} {s : LstateMF} {Post : α → LstateMF → Prop}
    {Site : NFCall jasminDialect → LstateMF → Prop}
    {Q : (e : NFCall jasminDialect) → LstateMF →
      Option (Ctxt.Valuation (d := jasminDialect) e.resTys) → LstateMF → Prop}
    (hpost : ∀ m, Post r m → Halted P m)
    (h : TSim (E := nfCallSig jasminDialect) I P Site Q (.ret (some r)) s Post) :
    ∃ u, SegTo I T P s none u ∧ Post r u := by
  obtain ⟨k, u, hs, hp⟩ := h
  exact ⟨u, ⟨k, hs, hpost u hp⟩, hp⟩

/-- **The step of a summary at a call site is a state after the call.** Let the summary `pr` of
    the symbol of `ev` in `T` take as many arguments as `ev` at the array positions of its
    argument types and compute the result `x` on the argument words of `ev`, and let `x` give a
    state after the call of the answer `r` at every destination and state. The step of the
    summary from a state at a call site of `ev` is a state after the call of `ev` at `some r`. -/
theorem callRet_of_glue {ev : NFCall jasminDialect} {pr : ProcSummary} (hpr : T ev.name = some pr)
    (har : pr.arity = ev.argTys.length) (haa : pr.arrArgs = arrArgsOf ev.argTys)
    {x : CallRes} (hx : pr.result (wordsOf ev.args) = some x)
    {r : Ctxt.Valuation (d := jasminDialect) ev.resTys}
    (hout : ∀ (dst : String) (u : LstateMF), CallOut dst ev.resTys r u (retRes dst x u))
    {p : Nat} {u v : LstateMF} (hsi : NFProgCallTreeExport.CallSite P ev u) (hpu : atPc P p u)
    (hg : Glue T P p u v) : CallRet P ev u (some r) v := by
  obtain ⟨dst, srcs, tag, k, hat, hf, hlen, hrd⟩ := hsi
  obtain rfl : k = p := hat.2.symm.trans hpu.2
  obtain ⟨i, pr', dst', srcs', hi, hq, hstep⟩ := hg
  rw [hf] at hi
  obtain rfl := Option.some.inj hi
  rw [procCall?_callShadow, hpr] at hq
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl, rfl⟩ := hq
  unfold procStep at hstep
  rw [ite_eq_left (hlen.trans har.symm), haa, hrd] at hstep
  simp only [Option.bind_some, hx, Option.map_some, Option.some.injEq] at hstep
  subst hstep
  exact ⟨dst, srcs, tag, k, r, hat, hf, rfl, hout dst u⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSeg
