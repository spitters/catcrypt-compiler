/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs

/-!
# Call trees related to the runs of a program under a liveness certificate

A renaming `σ` of a program with a liveness certificate (`JasminLsemExportRegAlloc.LiveCert`),
which relates the register and array names live at each position, is correct for halting runs
by `JasminLsemExportRegAlloc.lsemFuelMemF_live_calls` under the call condition `LiveCalls`,
through the step simulation `JasminLsemExportRegAlloc.step_live_calls` under the relation
`RelF2` at the live names. The register merge of the region backend and the removal of its
array self-moves are of this kind. The same relation, with the position bound (`LiveRel`),
carries a call tree related to the states of the program by `NFProgCallTreeExport.TSim`, at the
call sites and the states after the calls, to the states of the renamed program (`tsim_live`),
when the array positions of the arguments of each event and the length of its result are those
of the call condition.

## Main definitions

* `LiveRel`: the relation of the states of the program and of the renamed program.

## Main results

* `live_step`: a step of the program is matched by a step of the renamed program.
* `tsim_live`: a call tree related to a state of the program is related to every state of the
  renamed program that `LiveRel` relates to it.
-/

@[expose] public section

set_option autoImplicit false

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

/-- **The relation of a state of the program and a state of the renamed program**: `RelF2 σ` at
    the names live at the position of the state of the program, which is `k0` or later. -/
def LiveRel (σ : String → String) (Lr La : Nat → String → Prop) (k0 : Nat)
    (s s' : LstateMF) : Prop :=
  RelF2 σ (Lr s.prog.base.lpc) (La s.prog.base.lpc) s s' ∧ k0 ≤ s.prog.base.lpc

/-- The instruction fetched in the renamed program is the renamed instruction. -/
theorem live_fetch (hC : LiveCert σ k0 P P' Lr La) {s s' : LstateMF}
    (hR : LiveRel σ Lr La k0 s s') :
    findInstrMem P' s'.prog = (findInstrMem P s.prog).map (renRM σ) := by
  obtain ⟨hR, hk⟩ := hR
  unfold findInstrMem
  rw [hR.2.1, hC.lfn]
  have hpc : s'.prog.base.lpc = s.prog.base.lpc := hR.1.1.1
  split
  · rw [hpc]; exact hC.body _ hk
  · rfl

/-- **A step of the program is matched by a step of the renamed program.** -/
theorem live_step {I : Isa} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao) (hC : LiveCert σ k0 P P' Lr La)
    (hK : LiveCalls σ k0 P Lr La aa ao) {s s' u : LstateMF} (hR : LiveRel σ Lr La k0 s s')
    (h : I.lsemStepPMemF P s = some u) :
    ∃ u', I.lsemStepPMemF P' s' = some u' ∧ LiveRel σ Lr La k0 u u' := by
  unfold Isa.lsemStepPMemF at h ⊢
  rw [live_fetch hC hR]
  cases hf : findInstrMem P s.prog with
  | none => rw [hf] at h; cases h
  | some i =>
      rw [hf] at h
      have hget : P.body[s.prog.base.lpc]? = some i := by
        unfold findInstrMem at hf
        split at hf
        · exact hf
        · simp at hf
      obtain ⟨u', hu', hRu, hku⟩ := step_live_calls hle hcl hC hK i hR.2 hget hR.1 h
      exact ⟨u', hu', hRu, hku⟩

/-- **A call tree related to the states of the program is related to the states of the renamed
    program.** Let `I` have the steps of `x86Isa` and local calls at `aa` and `ao`, the programs
    have a liveness certificate from `k0` on with the call condition `LiveCalls` at `aa` and
    `ao`, and every event at a call site of `P` have the array positions `aa` and the result
    length `ao` of its symbol. A tree related by `TSim` to `s` at the call sites and the states
    after the calls of `P` is related to every state `s'` that `LiveRel` relates to `s`, at the
    call sites and the states after the calls of `P'`, at every end condition that `LiveRel`
    carries `Post` to. -/
theorem tsim_live {I : Isa} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao) (hC : LiveCert σ k0 P P' Lr La)
    (hK : LiveCalls σ k0 P Lr La aa ao)
    (hev : ∀ e u, NFProgCallTreeExport.CallSite P e u →
      arrArgsOf e.argTys = aa e.name ∧ resLen e.resTys = ao e.name)
    {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', LiveRel σ Lr La k0 m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hR : LiveRel σ Lr La k0 s s')
    (h : TSim I P (NFProgCallTreeExport.CallSite P) (CallRet P) t s Post) :
    TSim I P' (NFProgCallTreeExport.CallSite P') (CallRet P') t s' Post' := by
  refine TSim.transfer (LiveRel σ Lr La k0) ?_ ?_ ?_ hpost hR h
  · intro n s t s' hs hR
    obtain ⟨t', ht', hRt⟩ := steps_of_step_rel I I (LiveRel σ Lr La k0)
      (fun s s' u hR hu => live_step hle hcl hC hK hR hu) n s s' t hR hs
    exact ⟨n, t', ht', hRt⟩
  · rintro e u u' hR ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
    obtain ⟨haa, -⟩ := hev e u ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
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
  · rintro e u u' a v' hR ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
      ⟨dst', srcs', tag', k', res, hat', hf', rfl, hout⟩
    obtain ⟨-, hao⟩ := hev e u ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
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
