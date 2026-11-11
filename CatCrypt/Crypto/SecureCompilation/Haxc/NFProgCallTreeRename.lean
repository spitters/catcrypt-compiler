/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs

/-!
# Call trees related to the runs of a renamed program

A renaming `σ` of the register names of a program from a position on
(`JasminLsemExportRewrites.RenProg`) is correct for halting runs by
`JasminLsemExportRewrites.lsemFuelMemF_ren_calls`, through the step simulation
`JasminLsemExportRewrites.step_ren_calls` under the relation `RelF σ N`. The same relation,
with the position bound (`RenRel`), carries a call tree related to the states of the program by
`NFProgCallTreeExport.TSim`, at the call sites and the states after the calls, to the states of
the renamed program (`tsim_ren`): the renamed operands of a call read the same words, and the
answer is written to the renamed destination.

## Main definitions

* `RenRel`: the relation of the states of the program and of the renamed program.

## Main results

* `ren_step`: a step of the program is matched by a step of the renamed program.
* `tsim_ren`: a call tree related to a state of the program is related to every state of the
  renamed program that `RenRel` relates to it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRename

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renOperand
  renLinstrR)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (RelF RelM RenOn RenProg
  step_ren_calls)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow retRes CallRes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall (steps_of_step_rel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (arrArgsOf wordsOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallOut CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExportTransfer (TSim.transfer)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs (callResOf callOut_retRes)

section Rename

variable {σ : String → String} {N : String → Prop} {k0 : Nat} {P P' : LprogM}

/-- **The relation of a state of the program and a state of the renamed program**: `RelF σ N`,
    with the state of the program at the position `k0` or later. -/
def RenRel (σ : String → String) (N : String → Prop) (k0 : Nat) (s s' : LstateMF) : Prop :=
  RelF σ N s s' ∧ k0 ≤ s.prog.base.lpc

/-- The instruction fetched in the renamed program is the renamed instruction. -/
theorem ren_fetch (hP : RenProg σ N k0 P P') {s s' : LstateMF} (hR : RenRel σ N k0 s s') :
    findInstrMem P' s'.prog = (findInstrMem P s.prog).map (renRM σ) := by
  obtain ⟨hR, hk⟩ := hR
  unfold findInstrMem
  rw [hR.2.1, hP.lfn]
  have hpc : s'.prog.base.lpc = s.prog.base.lpc := hR.1.1.1
  split
  · rw [hpc]; exact hP.body _ hk
  · rfl

/-- **A step of the program is matched by a step of the renamed program.** -/
theorem ren_step {I : Isa} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao) (hσ : RenOn σ N)
    (hP : RenProg σ N k0 P P') {s s' u : LstateMF} (hR : RenRel σ N k0 s s')
    (h : I.lsemStepPMemF P s = some u) :
    ∃ u', I.lsemStepPMemF P' s' = some u' ∧ RenRel σ N k0 u u' := by
  unfold Isa.lsemStepPMemF at h ⊢
  rw [ren_fetch hP hR]
  cases hf : findInstrMem P s.prog with
  | none => rw [hf] at h; cases h
  | some i =>
      rw [hf] at h
      have hget : P.body[s.prog.base.lpc]? = some i := by
        unfold findInstrMem at hf
        split at hf
        · exact hf
        · simp at hf
      obtain ⟨u', hu', hRu, hku⟩ := step_ren_calls hle hcl hσ hP i
        (hP.names _ i hR.2 hget) (hP.cond _ i hR.2 hget) hR.1 hR.2 h
      exact ⟨u', hu', hRu, hku⟩

/-- **A call tree related to the states of the program is related to the states of the renamed
    program.** Let `I` have the steps of `x86Isa` and local calls, `σ` be usable on `N`, and the
    programs be related by `RenProg` from `k0` on. A tree related by `TSim` to `s` at the call
    sites and the states after the calls of `P` is related to every state `s'` that `RenRel`
    relates to `s`, at the call sites and the states after the calls of `P'`, at every end
    condition that `RenRel` carries `Post` to. -/
theorem tsim_ren {I : Isa} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao) (hσ : RenOn σ N)
    (hP : RenProg σ N k0 P P') {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', RenRel σ N k0 m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hR : RenRel σ N k0 s s')
    (h : TSim I P (NFProgCallTreeExport.CallSite P) (CallRet P) t s Post) :
    TSim I P' (NFProgCallTreeExport.CallSite P') (CallRet P') t s' Post' := by
  have hsite : ∀ {u u' : LstateMF} {dst f : String} {srcs : List LOperand} {tag : MemTag}
      {k : Nat}, RenRel σ N k0 u u' → atPc P k u →
      P.body[k]? = some (callShadow dst f srcs, tag) →
      P'.body[k]? = some (callShadow (σ dst) f (srcs.map (renOperand σ)), tag)
        ∧ N dst ∧ ∀ o ∈ srcs, ∀ n ∈ JasminLsemExportRewrites.opNames o, N n := by
    intro u u' dst f srcs tag k hR hat hb
    have hk : k0 ≤ k := hat.2 ▸ hR.2
    refine ⟨by rw [hP.body k hk, hb]; rfl, ?_, ?_⟩
    · exact hP.names k _ hk hb dst
        (by simp [callShadow, JasminLsemExportRewrites.instrNames,
          JasminLsemExportRewrites.opNames])
    · intro o ho n hn
      exact hP.names k _ hk hb n (by
        simp only [callShadow, JasminLsemExportRewrites.instrNames, List.flatMap_append,
          List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨o, ho, hn⟩)
  refine TSim.transfer (RenRel σ N k0) ?_ ?_ ?_ hpost hR h
  · intro n s t s' hs hR
    obtain ⟨t', ht', hRt⟩ := steps_of_step_rel I I (RenRel σ N k0)
      (fun s s' u hR hu => ren_step hle hcl hσ hP hR hu) n s s' t hR hs
    exact ⟨n, t', ht', hRt⟩
  · rintro e u u' hR ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
    obtain ⟨hb', -, hs⟩ := hsite hR hat hfk
    refine ⟨σ dst, srcs.map (renOperand σ), tag, k,
      ⟨hR.1.2.1.trans (hat.1.trans hP.lfn.symm), by rw [← hat.2]; exact hR.1.1.1.1⟩, hb',
      by rw [List.length_map]; exact hlen, ?_⟩
    rw [hR.1.1.argsRead_ren _ 0 srcs hs]
    exact hrd
  · rintro e u u' a v' hR ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
      ⟨dst', srcs', tag', k', res, hat', hf', rfl, hout⟩
    obtain ⟨hb', hd, -⟩ := hsite hR hat hfk
    have hk' : k' = k := by rw [← hat'.2, ← hat.2]; exact hR.1.1.1.1
    subst hk'
    rw [hb'] at hf'
    simp only [Option.some.injEq, Prod.mk.injEq, callShadow, LinstrR.Lopn.injEq,
      List.cons.injEq, LOperand.reg.injEq, and_true] at hf'
    obtain ⟨⟨rfl, -⟩, -⟩ := hf'
    obtain ⟨rfl, -, hback⟩ := callOut_retRes hout
    refine ⟨retRes dst (callResOf e.resTys res) u,
      ⟨dst, srcs, tag, k', res, hat, hfk, rfl, hback dst u⟩, ?_, ?_⟩
    · cases callResOf e.resTys res with
      | word r => exact ⟨JasminLsemExportRewrites.RelM.setReg hσ hR.1.1 hd r, hR.1.2.1, hR.1.2.2⟩
      | arr a => exact ⟨JasminLsemExportRewrites.RelM.setArr hσ hR.1.1 hd a, hR.1.2.1, hR.1.2.2⟩
    · rw [LprogIsa.lpc_retRes]
      exact Nat.le_succ_of_le hR.2

end Rename

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRename
