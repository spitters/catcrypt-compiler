/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChecked

/-!
# The call tree of a calling body against its reference, on the bounds-checked machine

The cut programs of the reference `d.ref` of a calling body, which the simulation of the cut
programs of its image (`LprogCallCut.CutSimI`) takes, run on the bounds-checked machine
`CheckedIsaCall.x86IsaK`. The call tree of the program is related to the entry state of `d.ref` on
the x86 flag machine (`NFProgCallTreeRefChain.tsim_regionRef`); the bounds check of the gate
carries the relation to the bounds-checked machine (`NFProgCallTreeChecked.tsim_checked`), at the
entry facts of the image entry, since every call of `d.ref` names a symbol of the table of the
callees and `d.ref` has no return.

## Main results

* `ret_renArr`, `ret_renRM`, `ret_selfNopI`, `ret_fuseE`, `mem_expI`: the renamings, the removal
  of a self-move and the fusion of a high multiply make no return of an instruction that is none.
* `ref_noRet`: the reference of a calling body that passes the gate has no return.
* `tab_of_callSymsB`: the calls of a body whose shadow instructions call symbols of a table of
  callees name symbols of its table of procedures.
* `tsim_regionRef_checked`: the call tree of a calling body against its reference, on the
  bounds-checked machine.
-/
@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChecked

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

/-- The renaming of the array positions makes no return. -/
theorem ret_renArr (σ : String → String) {i : LinstrRM}
    (h : (X86Backend.ImageCoalesceCfg.renArr σ i).1 = .Lret) : i.1 = .Lret := by
  obtain ⟨x, tag⟩ := i
  simp only [X86Backend.ImageCoalesceCfg.renArr] at h
  split at h <;>
    simp only [X86Backend.ImageCoalesceCfg.renLoad, X86Backend.ImageCoalesceCfg.renStore,
      X86Backend.ImageCoalesceCfg.renZero, X86Backend.ImageCoalesceCfg.renStoreImm,
      X86Backend.ImageCoalesceCfg.renCallW] at h <;>
    (repeat' split at h) <;> simp_all [LprogIsa.callShadow]


/-- The renaming of the register names makes no return. -/
theorem ret_renRM (σ : String → String) {i : LinstrRM}
    (h : (JasminLsemExportTransfer.renRM σ i).1 = .Lret) : i.1 = .Lret := by
  obtain ⟨x, tag⟩ := i
  cases x <;> simp_all [JasminLsemExportTransfer.renRM, JasminLsemExportTransfer.renLinstrR]

/-- The removal of a self-move makes no return. -/
theorem ret_selfNopI {i : LinstrRM} (h : (selfNopI i).1 = .Lret) :
    i.1 = .Lret := by
  unfold selfNopI at h
  split at h
  · cases h
  · exact h

/-- The expansion of a site of the high-multiply fusion makes no return. -/
theorem ret_fuseE {L : List (Option String)} {k : Nat} {i j : LinstrRM}
    (hj : j ∈ JasminLsemFuseMulHi.fuseE L k i) (h : j.1 = .Lret) : i.1 = .Lret := by
  unfold JasminLsemFuseMulHi.fuseE at hj
  split at hj
  · unfold JasminLsemFuseMulHi.fuseSiteExp at hj
    split at hj
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> cases h
    · simp only [List.mem_singleton] at hj
      subst hj
      exact h
  · simp only [List.mem_singleton] at hj
    subst hj
    exact h

/-- An instruction of an expansion by index is an instruction of the expansion of an instruction
    of the body. -/
theorem mem_expI {e : Nat → LinstrRM → List LinstrRM} :
    ∀ (c : List LinstrRM) (n : Nat) {j : LinstrRM}, j ∈ JasminLsemFuseMulHi.expI e c n →
      ∃ k i, i ∈ c ∧ j ∈ e k i
  | [], _, _, hj => by simp [JasminLsemFuseMulHi.expI] at hj
  | i :: is, n, j, hj => by
      simp only [JasminLsemFuseMulHi.expI, List.mem_append] at hj
      rcases hj with hj | hj
      · exact ⟨n, i, List.mem_cons_self, hj⟩
      · obtain ⟨k, i', hi', hj'⟩ := mem_expI is (n + 1) hj
        exact ⟨k, i', List.mem_cons_of_mem _ hi', hj'⟩


section Ref

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (movesOf renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiReg abiBase)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall eventEnv treeAt
  pureReader)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK tsim_regionRef)

/-- **The reference of a calling body has no return**, on a gate `regionCoB` at a table. -/
theorem ref_noRet {σ : AbiLayout} {nm : String → String} {fn : String} {t : JasminTy}
    {r : Exported} {T : CalleeTab} {body : Lcmd} {cert : List (String × String)}
    (hg : regionCoB σ nm body t r.code r.res cert (some T) fn = true) {d : CoParts}
    (hd : regionCoParts σ nm body t (calleeCodeT (some T) r.code) r.res cert (some T) = d) :
    ∀ i ∈ d.ref, i.1 ≠ LinstrR.Lret := by
  simp only [regionCoB, regionCopy_some_callee, regionOut, Option.all, Bool.and_eq_true] at hg
  rw [hd] at hg
  obtain ⟨⟨⟨⟨⟨⟨-, hcs⟩, -⟩, hcls0⟩, -⟩, -⟩,
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hce⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hsite⟩, -⟩, -⟩⟩ := hg
  obtain ⟨codeC, hcode⟩ := Option.isSome_iff_exists.mp hcs
  have hcc : calleeCodeT (some T) r.code = codeC := by
    simp only [calleeCodeT, hcode, Option.getD_some]
  rw [hcc] at hd hcls0
  have hmv : ∀ (ps : List (String × String)), ∀ i ∈ movesOf ps, i.1 ≠ LinstrR.Lret := by
    intro ps i hi
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
    simp [JasminLsemExportLower.movWire]
  have hpre : d.pre = argBind σ nm ++ movesOf d.ps := by rw [← hd]; rfl
  have hren' : d.ren = (regionCoBody σ nm t codeC r.res (some T)).map
      (JasminLsemExportTransfer.renRM (renOf d.ps)) := by rw [← hd]; rfl
  have hmerged : d.merged = d.ren.map (JasminLsemExportTransfer.renRM (renOf d.tau)) := by
    rw [← hd]; rfl
  have hnopE : d.nop = selfNop d.pre.length
      (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length) (d.pre ++ d.merged) := by
    rw [← hd]; rfl
  have hfusedE : d.fused = if d.sites then d.pre ++
      JasminLsemFuseMulHi.fuseMulHiRM (d.nop.drop d.pre.length) else d.nop := by
    rw [← hd]; rfl
  have hrefF : d.ref = d.fused := by
    have h1 : d.ref = if d.cells.isEmpty then d.fused
        else d.pre ++ (X86Backend.CellFoldLReg.cellFoldLR d.cells []
          (d.fused.drop d.pre.length)).getD (d.fused.drop d.pre.length) := by
      rw [← hd]; rfl
    rw [h1, hce, ite_eq_left rfl]
  have hP : ∀ i ∈ d.pre, i.1 ≠ LinstrR.Lret := by
    rw [hpre]
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hmv _ i hi
    · exact hmv _ i hi
  have hM : ∀ i ∈ d.pre ++ d.merged, i.1 ≠ LinstrR.Lret := by
    intro i hi hr
    rcases List.mem_append.mp hi with hi | hi
    · exact hP i hi hr
    rw [hmerged, hren'] at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hj
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hl
    have hc := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hcls0 o ho)).1
    have hro := ret_renArr _ (ret_renRM _ (ret_renRM _ hr))
    unfold JasminLsemFuseMulHi.clsB at hc
    rw [hro] at hc
    cases hc
  have hN : ∀ i ∈ d.nop, i.1 ≠ LinstrR.Lret := by
    rw [hnopE]
    intro i hi hr
    obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hi
    split at hr
    · exact hM _ (List.getElem_mem hk) (ret_selfNopI hr)
    · exact hM _ (List.getElem_mem hk) hr
  rw [hrefF, hfusedE]
  cases hS : d.sites with
  | false => exact hN
  | true =>
      simp only [regionSitesB, hS, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hsite
      obtain ⟨⟨hfuse, -⟩, -⟩ := hsite
      have hw : ∀ i ∈ d.nop.drop d.pre.length, JasminLsemFuseMulHi.wireOK i.1 = true :=
        fun i hi => JasminLsemFuseMulHi.wireOK_of_fuseOKL hfuse i (List.mem_append_right _ hi)
      intro i hi hr
      rcases List.mem_append.mp hi with hi | hi
      · exact hP i hi hr
      rw [JasminLsemFuseMulHi.fuseMulHiRM_eq _ hw] at hi
      obtain ⟨k, j, hj, hij⟩ := mem_expI _ 0 hi
      exact hN j (List.mem_of_mem_drop hj) (ret_fuseE hij hr)


/-- **The calls of a reference whose shadow instructions call symbols of a table of callees name
    symbols of its table of procedures.** -/
theorem tab_of_callSymsB {T : CalleeTab} {B : List LinstrRM}
    (h : X86Backend.CalleeSegCheck.callSymsB (fun g => T.names.contains g) B = true) :
    ∀ (k : Nat) (dst f : String) (srcs : List LOperand) (tag : MemTag),
      B[k]? = some (LprogIsa.callShadow dst f srcs, tag) → (T.tab f).isSome = true := by
  intro k dst f srcs tag hk
  have h1 := List.all_eq_true.mp h _ (List.mem_of_getElem? hk)
  simp only [LprogIsa.shadowCall?_callShadow, Option.all_some] at h1
  have h2 := congrFun T.lookup_isSome f
  simp only [CalleeTab.tab, Option.isSome_map]
  rw [h2]
  exact h1

/-- **The call tree of a calling body against the reference, on the bounds-checked machine.**
    Under the hypotheses of `NFProgCallTreeRefChain.tsim_regionRef`, the call tree of the program
    is related by `TSim` on `CheckedIsaCall.x86IsaK` to the entry state of `d.ref`, at the same
    end condition: the bounds check of the gate holds of the reference
    (`NFProgCallTreeChecked.tsim_checked`), whose calls name symbols of the table and which has no
    return (`ref_noRet`), at the entry facts of the image entry. -/
theorem tsim_regionRef_checked {σ : AbiLayout} {nm : String → String} {fn : String}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) {r0 r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r0) (ht : ∃ w m, t = .stackArr w m)
    {ex : List String} {T : CalleeTab}
    (hw : regionWebs ex r0 (calleeAAT (some T)) (calleeAOT (some T)) = r) {body : Lcmd}
    {cert : List (String × String)}
    (hg : regionCoB σ nm body t r.code r.res cert (some T) fn = true) {d : CoParts}
    (hd : regionCoParts σ nm body t (calleeCodeT (some T) r.code) r.res cert (some T) = d)
    {G : NFCall jasminDialect → Prop} (hGT : ∀ e, G e → EvOK T e)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) (hG : AllEv G (treeAt pureReader eventEnv fuel p V)) :
    TSim X86Backend.CheckedIsaCall.x86IsaK (singletonProgM fn d.ref)
      (NFProgCallTreeExport.CallSite (singletonProgM fn d.ref))
      (CallRet (singletonProgM fn d.ref)) (treeAt pureReader eventEnv fuel p V)
      { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn }, zf := false }
      fun v u => (∀ sa' : AState,
        (∀ q A n, slotArrOf σ nm q = some (A, n) →
          ∃ arr, u.prog.base.getArr (renOf d.ps A) 64 n = some arr
            ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa A) j) = arr ⟨j, hj⟩) →
        σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
        ∧ u.prog.base.lpc = d.ref.length ∧ u.prog.lfn = fn := by
  have hT0 := tsim_regionRef hp hr ht hw hg hd hGT sa V hV hreg fuel hG
  have hnoRet := ref_noRet hg hd
  simp only [regionCoB, regionCopy_some_callee, regionOut, Option.all, Bool.and_eq_true] at hg
  rw [hd] at hg
  obtain ⟨⟨⟨⟨⟨⟨-, hcs⟩, -⟩, -⟩, -⟩, -⟩,
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, hce⟩, hren⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, himg⟩⟩ := hg
  obtain ⟨codeC, hcode⟩ := Option.isSome_iff_exists.mp hcs
  have hcc : calleeCodeT (some T) r.code = codeC := by
    simp only [calleeCodeT, hcode, Option.getD_some]
  rw [hcc] at hd hren
  have hcells : d.cells = [] := List.isEmpty_iff.mp hce
  have hcellOuts : d.cellOuts = [] := by
    have h1 : d.cellOuts = d.cells.flatMap fun p =>
        if d.obs.contains p.1 then X86Backend.ImageAddrRouteW.outCells p.1 p.2 else [] := by
      rw [← hd]; rfl
    rw [h1, hcells]
    rfl
  rw [hcells, hcellOuts, List.append_nil] at himg
  have RF := renB_spec hren
  have hU : ∀ j, j < σ.args.length → unren d.ps (renOf d.ps (argName j)) = argName j :=
    fun j hj => (RF.unr j hj).2
  obtain ⟨-, -, -, -, hbnd⟩ := renImage_entry_nil himg hU sa hreg fn []
  have hok := calleeBodyBT_spec.mp hcb
  exact NFProgCallTreeChecked.tsim_checked hok.idx hnoRet (tab_of_callSymsB hok.symsRef) rfl rfl
    hbnd hT0

end Ref

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChecked
