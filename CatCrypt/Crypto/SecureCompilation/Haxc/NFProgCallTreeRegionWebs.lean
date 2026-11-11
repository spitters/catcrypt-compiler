/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend

/-!
# The call tree of a program against the webs of its region export

The first stage of the reference of the region backend is the export `r` of the program with
its array names split into webs (`regionWebs`). The call tree of the program with call events,
`treeAt pureReader eventEnv`, is related by `NFProgCallTreeExport.TSim` on the x86 flag machine
to the entry state of the webs, at their call sites and states after the calls, with the end
condition that some state at the end of the export agrees with the returned operands at the
value, and the end state of the webs has its registers and its arrays at the names read after
the code (`tsim_regionWebs`). This is the tree form of the run of the webs used by
`RegionLinkCompose.regionVirt_run_procs`, with calls as events.

## Main results

* `tsim_regionWebs`: the call tree of a program of `RegionExportable` against the webs of its
  export, from a state at the counter `0` whose store agrees with the arguments.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegionWebs

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig eventEnv treeAt pureReader)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallRet exportT_sim
  tCallsSim_eventEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs (WebsRel tsim_webs resLen)

/-- **The call tree of a program against the webs of its export.** Let `p` be a program of
    `RegionExportable` with the export `r`, and let every event at a call site of the export
    code have the array positions `aa` and the result length `ao` of its symbol. From a state
    `m` of the function `fn` at the counter `0` whose store agrees with the arguments `V`, the
    call tree of `p` with call events is related by `TSim` on the x86 flag machine to `m` on the
    code of the webs `regionWebs ex r aa ao`, at its call sites and states after the calls, with
    the end condition: a state at the end of the export code agrees with the returned operands
    at the value, and the end state of the webs is at the end of the code, in `fn`, with the
    registers of that state and its arrays at the names `regionWebsObs ex r`. -/
theorem tsim_regionWebs {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hp : RegionExportable p) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) (ex : List String)
    {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hev : ∀ e u, NFProgCallTreeExport.CallSite (singletonProgM fn r.code) e u →
      arrArgsOf e.argTys = aa e.name ∧ resLen e.resTys = ao e.name)
    (fuel : Nat) (V : Ctxt.Valuation Γ) (m : LstateMF) (hpc : m.prog.base.lpc = 0)
    (hfn : m.prog.lfn = fn) (hag : StoreAgreesM Γ.length Γ.length m.prog.base V) :
    TSim x86Isa (singletonProgM fn (regionWebs ex r aa ao).code)
      (NFProgCallTreeExport.CallSite (singletonProgM fn (regionWebs ex r aa ao).code))
      (CallRet (singletonProgM fn (regionWebs ex r aa ao).code))
      (treeAt pureReader eventEnv fuel p V) m fun v t =>
        ∃ t₁ : LstateMF, ResAgrees Γ.length r.depth t₁.prog.base r.res v
          ∧ t.prog.base.reg.lvm = t₁.prog.base.reg.lvm
          ∧ (∀ x ∈ regionWebsObs ex r, t.prog.base.larr x = t₁.prog.base.larr x)
          ∧ t.prog.base.lpc = r.code.length ∧ t.prog.lfn = fn := by
  have hT := exportT_sim Γ.length fn (I := x86Isa) (LprogIsa.Isa.StepLe.refl _)
    (tCallsSim_eventEnv x86Isa) hp Γ.length 0 r hr rfl le_rfl (singletonProgM fn r.code) [] []
    rfl (by simp [singletonProgM]) (fun _ _ => rfl) fuel V m ⟨hfn, by rw [hpc]; rfl⟩ hag
  unfold regionWebs
  split
  · rename_i hc
    rw [Bool.and_eq_true] at hc
    have hwb := hc.1
    refine tsim_webs (LprogIsa.Isa.StepLe.refl _) (LprogIsa.Isa.CallLocal.refl x86Isa aa ao) hwb hev
      (fun v t t' hW hP => ?_) ⟨hfn, by rw [hpc]; exact Nat.zero_le _,
        X86Backend.ConstGuard.guardInv_zero _ hpc, ?_, rfl, rfl⟩ hT
    · obtain ⟨hat, hres, -⟩ := hP
      obtain ⟨hft, -, -, hR, hfn', -⟩ := hW
      have hlen : t.prog.base.lpc = r.code.length := by
        rw [hat.2]
        simp
      rw [hlen] at hR
      have hR' := X86Backend.ArrWebs.coRel_congr (hR.mono (X86Backend.ArrWebs.webB_obs hwb))
        (X86Backend.ArrWebs.webB_exit hwb)
      refine ⟨t, hres, ?_, fun x hx => hR'.arr x hx, ?_, hfn'.trans hft⟩
      · rw [hR'.reg]
      · rw [show t'.prog.base.lpc = t.prog.base.lpc from
          X86Backend.ImageCoalesceCfg.coRel_lpc hR, hlen]
    · rw [hpc]
      exact X86Backend.ArrWebs.coRel_congr ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
        (fun x hx => (X86Backend.ArrWebs.webB_entry hwb x hx).symm)
  · refine NFProgCallTreeExport.TSim.mono (fun v t hP => ?_) hT
    obtain ⟨hat, hres, -⟩ := hP
    exact ⟨t, hres, rfl, fun _ _ => rfl, by rw [hat.2]; simp, hat.1⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegionWebs
