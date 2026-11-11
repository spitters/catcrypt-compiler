/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegionWebs
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRename
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExpand
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose

/-!
# The call tree of a calling body against the reference of its region export

The reference `d.ref` of a calling body is built from the export of the program by the webs of
its array names, the rewriting onto the common names of the callees, the coalescing of array
names, the renaming by the pairs of the certificate behind the copies of the parameter
registers, the register merge, the removal of array self-moves and the high-multiply fusion
(`RegionBackend.regionCoParts`). The halting form of this chain is
`RegionLinkCompose.regionCo_bytes_tab`. Here every stage carries a call tree with call events,
related to the entry state by `NFProgCallTreeExport.TSim`, to the next stage, with each
hypothesis from the gate `regionCoB`: the call tree of the program is related on the x86 flag
machine to the entry state of `d.ref`, at its call sites and the states after the calls, with
the end condition that every machine state holding the arrays of the result slots reads back
the source value of the result.

The passes that read the shape of an event at a call site take it from the events of the tree
(`NFProgCallTreeEvents.AllEv`) at the condition `EvOK`: the array positions and result length
of the symbol in the table, and the shape of its common entry.

## Main definitions

* `EndAt`: the end condition at a stage: a state agreeing with the returned operands, whose
  arrays the state holds under a renaming, at a counter in a function.
* `EvOK`: the condition on an event of a symbol of a table of callees.

## Main results

* `tsim_regionWebsOn`: the call tree of a program against the webs of its export, at the call
  sites of events of a condition `G`.
* `tsim_regionRef`: the call tree of a calling body with a word-array result against the
  reference of its region export, from the entry state of the reference.
-/
@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall eventEnv treeAt
  pureReader)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallRet exportT_sim
  tCallsSim_eventEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs (resLen)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv TSim.siteMono
  tsim_and_of_allEv)

/-- **The call tree of a program against the webs of its export, at the call sites of events
    of `G`.** As `NFProgCallTreeRegionWebs.tsim_regionWebs`, for a tree whose events meet `G`,
    with the array positions `aa` and the result lengths `ao` of the symbol of each event of
    `G`. -/
theorem tsim_regionWebsOn {fn : String} {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hp : RegionExportable p) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) (ex : List String)
    {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    {G : NFCall jasminDialect → Prop}
    (hev : ∀ e, G e → arrArgsOf e.argTys = aa e.name ∧ resLen e.resTys = ao e.name)
    (fuel : Nat) (V : Ctxt.Valuation Γ) (hG : AllEv G (treeAt pureReader eventEnv fuel p V))
    (m : LstateMF) (hpc : m.prog.base.lpc = 0)
    (hfn : m.prog.lfn = fn) (hag : StoreAgreesM Γ.length Γ.length m.prog.base V) :
    TSim x86Isa (singletonProgM fn (regionWebs ex r aa ao).code)
      (fun e u => NFProgCallTreeExport.CallSite (singletonProgM fn (regionWebs ex r aa ao).code)
        e u ∧ G e)
      (CallRet (singletonProgM fn (regionWebs ex r aa ao).code))
      (treeAt pureReader eventEnv fuel p V) m fun v t =>
        ∃ t₁ : LstateMF, ResAgrees Γ.length r.depth t₁.prog.base r.res v
          ∧ t.prog.base.reg.lvm = t₁.prog.base.reg.lvm
          ∧ (∀ x ∈ regionWebsObs ex r, t.prog.base.larr x = t₁.prog.base.larr x)
          ∧ t.prog.base.lpc = r.code.length ∧ t.prog.lfn = fn := by
  have hT := tsim_and_of_allEv hG (exportT_sim Γ.length fn (I := x86Isa)
    (LprogIsa.Isa.StepLe.refl _) (tCallsSim_eventEnv x86Isa) hp Γ.length 0 r hr rfl le_rfl
    (singletonProgM fn r.code) [] [] rfl (by simp [singletonProgM]) (fun _ _ => rfl) fuel V m
    ⟨hfn, by rw [hpc]; rfl⟩ hag)
  unfold regionWebs
  split
  · rename_i hc
    rw [Bool.and_eq_true] at hc
    have hwb := hc.1
    refine NFProgCallTreeWebs.tsim_websOn (LprogIsa.Isa.StepLe.refl _)
      (LprogIsa.Isa.CallLocal.refl x86Isa aa ao) hwb hev
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


section Ref

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (movesOf movesOf_isLopn renOf
  movesState movesState_larr movesState_target movesState_other renOf_of_not_mem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseMulHiRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa ProcTable ProcSummary)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (chainAliasO)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf AbiEntryM
  storeAgreesM_of_abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix (CtlOK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiReg abiBase)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut

/-- **The end condition of the reference at a stage**: some state agrees with the returned
    operands `res` at the value `v`, the state `u` holds the array of each returned name `x` of
    that state at `g x`, and `u` is at the counter `len` of the function `fn`. -/
def EndAt (fn : String) (n depth : Nat) (res : List LOperand) (g : String → String) (len : Nat)
    {ts : List JasminTy} (v : Ctxt.Valuation (d := jasminDialect) ts) (u : LstateMF) : Prop :=
  ∃ t₁ : LstateMF, ResAgrees n depth t₁.prog.base res v
    ∧ (∀ x ∈ res.map operandName, u.prog.base.larr (g x) = t₁.prog.base.larr x)
    ∧ u.prog.base.lpc = len ∧ u.prog.lfn = fn

/-- The summary of no arguments that refuses every call: a table of it meets the shape of every
    entry of a table of common names. -/
def refuseSummary : ProcSummary where
  arity := 0
  run := fun _ => none

/-- **The condition on an event at a table of callees `T`**: its array positions and its result
    length are those of its symbol in `T`. -/
def EvOK (T : CalleeTab) (e : NFCall jasminDialect) : Prop :=
  arrArgsOf e.argTys = calleeAAT (some T) e.name ∧ resLen e.resTys = calleeAOT (some T) e.name

/-- **An event of `EvOK` meets the shape of the common entry of its symbol.** -/
theorem evOK_common {T : CalleeTab} {e : NFCall jasminDialect} (h : EvOK T e) :
    ∀ sh args res, T.common e.name = some (sh, args, res) →
      (∀ i, sh.arrArgs i = none → arrArgsOf e.argTys i = none)
      ∧ (sh.out = false → resLen e.resTys = none) := by
  intro sh args res hc
  obtain ⟨c, hc', he⟩ := Option.map_eq_some_iff.mp hc
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -, -⟩ := he
  refine ⟨fun i hi => ?_, fun ho => ?_⟩
  · rw [h.1]
    simpa [calleeAAT, hc', CalleeData.shape] using hi
  · rw [h.2]
    cases hcr : c.res with
    | reg r => simp [calleeAOT, hc', hcr]
    | out n k => simp [CalleeData.shape, hcr] at ho

/-- **The call tree of a calling body against the reference.** Let a program `p` of
    `RegionExportable` with a word-array result have the export `r0`, its webs `r` at the table
    `T`, and pass the gate `regionCoB` with the parts `d`, and let every event of its call tree
    meet a condition `G` under which it has the array positions and the result length of its
    symbol in `T` (`EvOK`). From the entry state of the reference at a machine state `sa` whose
    registers hold the arguments `V` in the layout `σ`, the call tree is related by `TSim` on the
    x86 flag machine to `d.ref`, at its call sites and the states after the calls, with the end
    condition: the state is at the end of `d.ref` in `fn`, and every machine state holding the
    arrays of the result slots reads back the source value of the result. This is the tree form
    of `RegionLinkCompose.regionCo_bytes_tab`. -/
theorem tsim_regionRef {σ : AbiLayout} {nm : String → String} {fn : String}
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
    TSim x86Isa (singletonProgM fn d.ref) (NFProgCallTreeExport.CallSite (singletonProgM fn d.ref))
      (CallRet (singletonProgM fn d.ref)) (treeAt pureReader eventEnv fuel p V)
      { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn }, zf := false }
      fun v u => (∀ sa' : AState,
        (∀ q A n, slotArrOf σ nm q = some (A, n) →
          ∃ arr, u.prog.base.getArr (renOf d.ps A) 64 n = some arr
            ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa A) j) = arr ⟨j, hj⟩) →
        σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
        ∧ u.prog.base.lpc = d.ref.length ∧ u.prog.lfn = fn := by
  obtain ⟨w, m, rfl⟩ := ht
  simp only [regionCoB, regionCopy_some_callee, regionOut, Option.all, Bool.and_eq_true] at hg
  rw [hd] at hg
  obtain ⟨⟨⟨⟨⟨⟨-, hcs⟩, hfresh⟩, hcls0⟩, hco⟩, hfix⟩,
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, hce⟩, hren⟩, hobs⟩, -⟩, hres⟩, hmg⟩, hnop⟩, hsite⟩, -⟩, himg⟩⟩ := hg
  obtain ⟨codeC, hcode⟩ := Option.isSome_iff_exists.mp hcs
  have hcc : calleeCodeT (some T) r.code = codeC := by
    simp only [calleeCodeT, hcode, Option.getD_some]
  rw [hcc] at hd hcls0 hco hfix hren hobs hres
  have hcells : d.cells = [] := List.isEmpty_iff.mp hce
  have hcellOuts : d.cellOuts = [] := by
    have h1 : d.cellOuts = d.cells.flatMap fun p =>
        if d.obs.contains p.1 then X86Backend.ImageAddrRouteW.outCells p.1 p.2 else [] := by
      rw [← hd]; rfl
    rw [h1, hcells]
    rfl
  rw [hcells, hcellOuts, List.append_nil] at himg
  have RF := renB_spec hren
  have E := entryB_spec (renImageB_entryB himg) sa
  have hSrc := E.argSrc hreg.stackIn
  have hU : ∀ j, j < σ.args.length → unren d.ps (renOf d.ps (argName j)) = argName j :=
    fun j hj => (RF.unr j hj).2
  have hdaa : d.aa = calleeAAT (some T) := by rw [← hd]; rfl
  have hdao : d.ao = calleeAOT (some T) := by rw [← hd]; rfl
  have hevA : ∀ e, G e → arrArgsOf e.argTys = calleeAAT (some T) e.name
      ∧ resLen e.resTys = calleeAOT (some T) e.name := hGT
  -- The webs of the export.
  have hres0 : r0.res = r.res := by rw [← hw]; simp
  have hlen0 : r.code.length = r0.code.length := by rw [← hw, regionWebs_length]
  have habi := entryV_abiEntry (sa := sa) (un := unren d.ps) E.argF E.argG
    fun j hj => (RF.unr j hj).1
  have hag0 := storeAgreesM_of_abi hV habi
  have h1 := tsim_regionWebsOn hp hr ex hevA fuel V hG
    { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn }, zf := false }
    habi.pc rfl hag0
  rw [hw] at h1
  have hB0 : regionCoCode σ nm (.stackArr w m) r.code r.res = r.code := by
    simp [regionCoCode, regionRet, movesOf]
  replace h1 := NFProgCallTreeExport.TSim.mono
    (Post' := EndAt fn Γ.length r0.depth r.res id
      (regionCoCode σ nm (.stackArr w m) r.code r.res).length)
    (fun v u hP => by
      obtain ⟨t₁, hres, -, harr, hpc, hfn⟩ := hP
      refine ⟨t₁, hres0 ▸ hres, fun x hx => harr x ?_, by rw [hpc, hB0, hlen0], hfn⟩
      simp only [regionWebsObs, List.mem_append, hres0]
      exact Or.inl hx) h1
  rw [hB0] at h1
  -- The rewriting onto the common names of the callee.
  have hB : commonCallsT? T.common (regionCoCode σ nm (.stackArr w m) r.code r.res)
      = some (regionCoCode σ nm (.stackArr w m) codeC r.res) := by
    simp only [regionCoCode, commonCallsT?_append, hcode, commonCallsT?_movesOf,
      Option.bind_some, Option.map_some]
  have hnames : ∀ g e, T.common g = some e → g ∈ T.names := by
    intro g e hg'
    obtain ⟨c, hc', -⟩ := Option.map_eq_some_iff.mp hg'
    have h1 := congrFun T.lookup_isSome g
    simp only [hc', Option.isSome_some] at h1
    simpa using h1.symm
  have hTc : ∀ g sh args res, T.common g = some (sh, args, res) →
      ∃ pr, (fun _ => some refuseSummary : ProcTable) g = some pr
        ∧ (∀ i, sh.arrArgs i = none → pr.arrArgs i = none) ∧ (sh.out = false → pr.RetWord) :=
    fun _ _ _ _ _ => ⟨refuseSummary, rfl, fun _ _ => rfl, fun _ => rfl⟩
  have hcS := commonSimT_of_commonFreshT hTc hnames hfresh
  rw [← hB0] at h1
  have h2 := NFProgCallTreeCommon.tsim_commonOn hB hcS (fun e he => evOK_common (hGT e he))
    (Post' := EndAt fn Γ.length r0.depth r.res id
      (regionCoCode σ nm (.stackArr w m) codeC r.res).length)
    (fun x u u' hR hP => by
      obtain ⟨L', -, rfl⟩ := hR
      obtain ⟨t₁, hres, harr, hpc, hfn⟩ := hP
      refine ⟨t₁, hres, harr, ?_, hfn⟩
      show expPosT _ _ u.prog.base.reg.lpc = _
      rw [show u.prog.base.reg.lpc = _ from hpc, ← commonCallsT?_length hB])
    (offRel_entryT _ _ _ rfl) h1
  -- The coalescing of the array names.
  have hobsC : ∀ x ∈ r.res.map operandName,
      x ∈ regionCoObs (.stackArr w m) r.res := fun x hx => hx
  have h3 := NFProgCallTreeCoalesce.tsim_coalesceOn (LprogIsa.Isa.StepLe.refl _)
    (LprogIsa.Isa.CallLocal.refl x86Isa _ _) hco hevA
    (Post := EndAt fn Γ.length r0.depth r.res id
      (regionCoCode σ nm (.stackArr w m) codeC r.res).length)
    (Post' := EndAt fn Γ.length r0.depth r.res
      (chainAliasO (calleeOutsT (some T)) (regionCoCode σ nm (.stackArr w m) codeC r.res))
      (regionCoCode σ nm (.stackArr w m) codeC r.res).length)
    (fun x u u' hR hP => by
      obtain ⟨-, -, -, hR, hfn, -⟩ := hR
      obtain ⟨t₁, hres, harr, hpc, hfn1⟩ := hP
      rw [hpc] at hR
      refine ⟨t₁, hres, fun y hy => ?_, ?_, hfn.trans hfn1⟩
      · rw [← harr y hy]
        exact hR.arr y (X86Backend.ImageCoalesceCfg.coCfgB_obs hco y (hobsC y hy))
      · rw [← hpc]
        exact X86Backend.ImageCoalesceCfg.coRel_lpc hR)
    (s := ⟨⟨entryV σ (frameE body sa) sa (unren d.ps), fn⟩, false⟩)
    (s' := ⟨⟨entryV σ (frameE body sa) sa (unren d.ps), fn⟩, false⟩)
    ⟨rfl, Nat.zero_le _, X86Backend.ConstGuard.guardInv_zero _ rfl,
      ⟨rfl, rfl, rfl, rfl, fun x hx => by
        rw [show _ = x from beq_iff_eq.mp (List.all_eq_true.mp hfix x hx)]⟩, rfl, rfl⟩ h2
  -- The renaming by the pairs, from the state after the copies of the parameter registers.
  have hpre : d.pre = argBind σ nm ++ movesOf d.ps := by rw [← hd]; rfl
  have hren' : d.ren = (regionCoBody σ nm (.stackArr w m) codeC r.res (some T)).map
      (renRM (renOf d.ps)) := by rw [← hd]; rfl
  set b1 : LstateM := { entryV σ (frameE body sa) sa (unren d.ps) with
    reg := { (entryV σ (frameE body sa) sa (unren d.ps)).reg with lpc := σ.args.length } }
    with hb1e
  have hb1 : runStraightF (argBind σ nm) (entryV σ (frameE body sa) sa (unren d.ps)) false
      = some (b1, false) := argBind_entryV E.argF E.argG hSrc false
  have hst : (argBind σ nm).all noStoreB = true := by
    have := RF.store
    rwa [List.append_nil] at this
  have hA : ∀ y, y ∈ loopNames (regionCoBody σ nm (.stackArr w m) codeC r.res (some T)) →
      b1.larr (renOf d.ps y) = b1.larr y := by
    intro y _
    rw [runStraightF_larr hst hb1]
    rcases renOf_cases d.ps y with he | ⟨p, hp, rfl, he⟩
    · rw [he]
    · rw [he]
      show (X86Backend.ExportCertEntry.abiEntryM σ sa).larr (unren d.ps p.2)
        = (X86Backend.ExportCertEntry.abiEntryM σ sa).larr (unren d.ps p.1)
      rw [unren_target RF.nd hp, unren_of_not_target fun q hq => RF.ts p hp q hq]
  have hRel : JasminLsemExportRewrites.RelF (renOf d.ps)
      (· ∈ loopNames (regionCoBody σ nm (.stackArr w m) codeC r.res (some T)))
      { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn }, zf := false }
      { prog := { base := (movesState d.ps b1).setLpc 0, lfn := fn }, zf := false } := by
    obtain ⟨hl, hm, hc, ho⟩ := movesState_larr d.ps b1
    refine ⟨⟨⟨rfl, fun y hy => ?_⟩, fun y hy => ?_, hm⟩, rfl, rfl, hc, ho⟩
    · show (movesState d.ps b1).reg.lvm (renOf d.ps y) = b1.reg.lvm y
      by_cases hm' : y ∈ d.ps.map Prod.fst
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hm'
        rw [RF.tgt p hp']
        exact movesState_target d.ps RF.nd RF.ts b1 p hp'
      · rw [renOf_of_not_mem hm']
        refine movesState_other d.ps b1 y fun hmem => ?_
        obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hmem
        exact RF.fresh p hp' hy
    · show (movesState d.ps b1).larr (renOf d.ps y) = b1.larr y
      rw [hl]
      exact hA y hy
  have hNobs : ∀ y ∈ r.res.map operandName,
      chainAliasO (calleeOutsT (some T)) (regionCoCode σ nm (.stackArr w m) codeC r.res) y
        ∈ loopNames (regionCoBody σ nm (.stackArr w m) codeC r.res (some T)) := by
    intro y hy
    have := List.all_eq_true.mp hobs y (hobsC y hy)
    rwa [List.contains_eq_mem, decide_eq_true_eq] at this
  have h4 := NFProgCallTreeRename.tsim_ren (LprogIsa.Isa.StepLe.refl x86Isa)
    (LprogIsa.Isa.CallLocal.refl x86Isa (fun _ _ => none) (fun _ => none)) RF.ren
    (JasminLsemExportRewrites.renProg_map fn _ (Nat.zero_le 1)
      (fun _ i _ hi => RF.names i (List.mem_of_getElem? hi))
      (fun _ i _ hi => RF.cond i (List.mem_of_getElem? hi)))
    (Post := EndAt fn Γ.length r0.depth r.res
      (chainAliasO (calleeOutsT (some T)) (regionCoCode σ nm (.stackArr w m) codeC r.res))
      (regionCoCode σ nm (.stackArr w m) codeC r.res).length)
    (Post' := EndAt fn Γ.length r0.depth r.res (fun y => renOf d.ps
      (chainAliasO (calleeOutsT (some T)) (regionCoCode σ nm (.stackArr w m) codeC r.res) y))
      (regionCoCode σ nm (.stackArr w m) codeC r.res).length)
    (fun x u u' hR hP => by
      obtain ⟨t₁, hres, harr, hpc, hfn⟩ := hP
      refine ⟨t₁, hres, fun y hy => (hR.1.1.2.1 _ (hNobs y hy)).trans (harr y hy), ?_,
        hR.1.2.1.trans hfn⟩
      rw [← hpc]
      exact hR.1.1.1.1)
    ⟨hRel, Nat.zero_le _⟩ (TSim.siteMono (fun _ _ h => h.1) h3)
  -- The copies in front.
  have hlop : ∀ i ∈ argBind σ nm ++ movesOf d.ps, IsLopn i := fun i hi =>
    (List.mem_append.mp hi).elim (movesOf_isLopn _ i) (movesOf_isLopn _ i)
  have h5 := NFProgCallTreeExportTransfer.tsim_relocate
    (Ascent.IsaCall.x86_stepRelocates fn (argBind σ nm ++ movesOf d.ps)
      ((regionCoBody σ nm (.stackArr w m) codeC r.res (some T)).map (renRM (renOf d.ps))) [])
    (Ascent.IsaCall.labelsFresh_of_labelsFreshB (List.all_eq_true.mpr fun i hi => by
      obtain ⟨_, _, _, hd⟩ := hlop i hi
      simp [hd]))
    (Post := EndAt fn Γ.length r0.depth r.res (fun y => renOf d.ps
      (chainAliasO (calleeOutsT (some T)) (regionCoCode σ nm (.stackArr w m) codeC r.res) y))
      (regionCoCode σ nm (.stackArr w m) codeC r.res).length)
    (Post' := EndAt fn Γ.length r0.depth r.res (fun y => renOf d.ps
      (chainAliasO (calleeOutsT (some T)) (regionCoCode σ nm (.stackArr w m) codeC r.res) y))
      (d.pre ++ d.ren).length)
    (fun x u hP => by
      obtain ⟨t₁, hres, harr, hpc, hfn⟩ := hP
      refine ⟨t₁, hres, harr, ?_, hfn⟩
      show (argBind σ nm ++ movesOf d.ps).length + u.prog.base.lpc = _
      rw [hpc, hpre, hren']
      simp [regionCoBody, Nat.add_assoc]) h4
  rw [List.append_nil, ← hpre, ← hren'] at h5
  replace h5 := tsim_and_of_allEv hG h5
  -- The state after the copies in front.
  set X : LstateMF := Ascent.IsaCall.shiftPc d.pre.length
    { prog := { base := (movesState d.ps b1).setLpc 0, lfn := fn }, zf := false } with hX
  have hXpc : X.prog.base.lpc = d.pre.length := rfl
  set g : String → String := fun y => renOf d.ps
    (chainAliasO (calleeOutsT (some T)) (regionCoCode σ nm (.stackArr w m) codeC r.res) y)
    with hgdef
  have hobsE : ∀ y ∈ r.res.map operandName, g y ∈ d.obs := by
    intro y hy
    have h1 : d.obs = (regionCoObs (.stackArr w m) r.res).map g := by
      rw [hgdef, ← hd]
      rfl
    rw [h1]
    exact List.mem_map.mpr ⟨y, hobsC y hy, rfl⟩
  have harrs : ∀ y ∈ r.res.map operandName, g y ∈ d.arrs ∧ g y ∈ d.arrsM := by
    intro y hy
    have h1 : d.arrs = arrNames d.ren ++ callArrNames d.aa d.ao d.ren ++ d.obs := by
      rw [← hd]; rfl
    have h2 : d.arrsM = arrNames d.merged ++ callArrNames d.aa d.ao d.merged ++ d.obs := by
      rw [← hd]; rfl
    rw [h1, h2]
    exact ⟨List.mem_append_right _ (hobsE y hy), List.mem_append_right _ (hobsE y hy)⟩
  have hlopP : ∀ i ∈ d.pre, IsLopn i := hpre ▸ hlop
  have hmerged : d.merged = d.ren.map (renRM (renOf d.tau)) := by rw [← hd]; rfl
  -- The register merge.
  simp only [regionMergeB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hmg
  have h6 : TSim x86Isa (singletonProgM fn (d.pre ++ d.merged))
      (fun e u => NFProgCallTreeExport.CallSite (singletonProgM fn (d.pre ++ d.merged)) e u ∧ G e)
      (CallRet (singletonProgM fn (d.pre ++ d.merged))) (treeAt pureReader eventEnv fuel p V) X
      (EndAt fn Γ.length r0.depth r.res g (d.pre ++ d.merged).length) := by
    rcases hmg with hnil | ⟨hck, -⟩
    · rw [hmerged, hnil, map_renRM_renOf_nil]
      exact h5
    · rw [hdaa, hdao] at hck
      rw [hmerged]
      have hck' := hck
      simp only [regCoB, Bool.and_eq_true, beq_iff_eq] at hck'
      obtain ⟨⟨⟨-, hAN⟩, hent⟩, -⟩ := hck'
      refine NFProgCallTreeLive.tsim_liveOn (LprogIsa.Isa.StepLe.refl x86Isa)
        (LprogIsa.Isa.CallLocal.refl x86Isa _ _) (liveCert_of_regCoB fn hlopP hck)
        (liveCalls_of_regCoB fn hck) hevA (fun x u u' hR hP => ?_) ?_ h5
      · obtain ⟨t₁, hres, harr, hpc, hfn⟩ := hP
        refine ⟨t₁, hres, fun y hy => ?_, ?_, hR.1.2.1.trans hfn⟩
        · have h1 := hR.1.1.2.1 (g y) (harrs y hy).1
          rw [show renOf d.tau (g y) = g y by
            simpa using List.all_eq_true.mp hAN (g y) (harrs y hy).1] at h1
          rw [h1]
          exact harr y hy
        · exact hR.1.1.1.1.trans (hpc.trans (by simp))
      · refine ⟨⟨⟨⟨rfl, fun y hy => ?_⟩, fun y hy => ?_, rfl⟩, rfl, rfl, rfl, rfl⟩, hXpc.ge⟩
        · rw [show renOf d.tau y = y by
            simpa using List.all_eq_true.mp hent y (by rwa [hXpc] at hy)]
        · rw [show renOf d.tau y = y by simpa using List.all_eq_true.mp hAN y hy]
  -- The array self-moves.
  have hnopE : d.nop = selfNop d.pre.length
      (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length) (d.pre ++ d.merged) := by
    rw [← hd]; rfl
  simp only [regionNopB, Bool.and_eq_true] at hnop
  obtain ⟨hck2, -⟩ := hnop
  rw [hdaa, hdao] at hck2
  have hlow : ∀ j, j < d.pre.length → selfPairB d.pre.length
      (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length) (d.pre ++ d.merged) j = false :=
    fun j hj => by simp [selfPairB, Nat.not_le.mpr hj]
  have hsec : (decide (0 < d.pre.length) && selfPairB d.pre.length
      (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length) (d.pre ++ d.merged)
        (d.pre.length - 1)) = false := by
    rcases Nat.eq_zero_or_pos d.pre.length with h0 | h0
    · rw [h0]; rfl
    · rw [hlow (d.pre.length - 1) (by omega), Bool.and_false]
  have h7 := NFProgCallTreeSelfNop.tsim_selfNopOn (LprogIsa.Isa.StepLe.refl x86Isa)
    (LprogIsa.Isa.CallLocal.refl x86Isa _ _) (liveCert_of_regCoB fn hlopP hck2)
    (liveCalls_of_regCoB fn hck2) hevA
    (Post := EndAt fn Γ.length r0.depth r.res g (d.pre ++ d.merged).length)
    (Post' := EndAt fn Γ.length r0.depth r.res g (d.pre ++ d.merged).length)
    (fun x u u' hR hP => by
      obtain ⟨t₁, hres, harr, hpc, hfn⟩ := hP
      rcases hR with ⟨hR, -, -, -⟩ | ⟨s₀, s₀', t', a, z, sc, w', n, -, -, -, hj, -, -, hld, -⟩
      · refine ⟨t₁, hres, fun y hy => (hR.1.2.1 (g y) (harrs y hy).2).trans (harr y hy), ?_,
          hR.2.1.trans hfn⟩
        exact hR.1.1.1.trans hpc
      · exfalso
        have hnx := X86Backend.AllocCheck.LcmdCFG.evalInstrPMemF_next _ _ s₀ u hld
        have hlt := (List.getElem?_eq_some_iff.mp hj).1
        have h2 : u.prog.base.lpc = s₀.prog.base.lpc + 1 := hnx.2
        omega)
    (Or.inl ⟨⟨⟨⟨rfl, fun _ _ => rfl⟩, fun _ _ => rfl, rfl⟩, rfl, rfl, rfl, rfl⟩, hXpc.ge,
      by rw [hXpc]; exact hsec, rfl⟩) h6
  rw [← hnopE] at h7
  -- The steps of the copies in front.
  have hrunPre : runStraightF d.pre (entryV σ (frameE body sa) sa (unren d.ps)) false
      = some (movesState d.ps b1, false) := by
    rw [hpre, JasminLsemAddrMem.runStraightF_append, hb1, Option.bind_some,
      JasminLsemRenameLoop.runStraightF_movesOf]
  have hposN : ∀ j, j < d.pre.length →
      (singletonProgM fn d.nop).body[(entryV σ (frameE body sa) sa (unren d.ps)).lpc + j]?
        = d.pre[j]? := fun j hj => by
    show d.nop[0 + j]? = _
    rw [Nat.zero_add, hnopE, selfNop, List.getElem?_mapIdx, List.getElem?_append_left hj,
      hlow j hj]
    have h1 : (decide (0 < j) && selfPairB d.pre.length
        (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length) (d.pre ++ d.merged) (j - 1))
        = false := by
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rfl
      · rw [hlow (j - 1) (by omega), Bool.and_false]
    rw [h1]
    cases d.pre[j]? <;> rfl
  have hsteps := NFProgCallTreeExpand.steps_of_runStraightF (I := x86Isa)
    (singletonProgM fn d.nop) fn rfl d.pre _ false _ false hlopP (fun _ _ _ _ => rfl) hposN
    hrunPre
  have hXe : X = { prog := { base := movesState d.ps b1, lfn := fn }, zf := false } := by
    have hml : (movesState d.ps b1).lpc = d.pre.length := by
      rw [JasminLsemMemFlagNestJoin.runStraightF_lpc _ _ _ _ _ hrunPre]
      exact Nat.zero_add _
    change goto _ (d.pre.length + 0) = _
    rw [Nat.add_zero, ← hml]
    rfl
  rw [← hXe] at hsteps
  have h8 := NFProgCallTreeExport.TSim.steps hsteps h7
  -- The multiplication fusion.
  have hrefF : d.ref = d.fused := by
    have h1 : d.ref = if d.cells.isEmpty then d.fused
        else d.pre ++ (X86Backend.CellFoldLReg.cellFoldLR d.cells []
          (d.fused.drop d.pre.length)).getD (d.fused.drop d.pre.length) := by
      rw [← hd]; rfl
    rw [h1, hce, ite_eq_left rfl]
  have hfusedE : d.fused
      = if d.sites then d.pre ++ fuseMulHiRM (d.nop.drop d.pre.length) else d.nop := by
    rw [← hd]; rfl
  have hsplit : d.nop = d.pre ++ d.nop.drop d.pre.length := by
    conv_lhs => rw [← List.take_append_drop d.pre.length d.nop]
    rw [hnopE, selfNop_take, List.take_left']
    rfl
  have h9 : TSim x86Isa (singletonProgM fn d.ref)
      (NFProgCallTreeExport.CallSite (singletonProgM fn d.ref))
      (CallRet (singletonProgM fn d.ref)) (treeAt pureReader eventEnv fuel p V)
      { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn }, zf := false }
      (fun v u => (∃ t₁ : LstateMF, ResAgrees Γ.length r0.depth t₁.prog.base r.res v
        ∧ ∀ y ∈ r.res.map operandName, u.prog.base.larr (g y) = t₁.prog.base.larr y)
        ∧ u.prog.base.lpc = d.ref.length ∧ u.prog.lfn = fn) := by
    rw [hrefF, hfusedE]
    replace h8 := TSim.siteMono (fun _ _ h => h.1) h8
    cases hS : d.sites with
    | false =>
        refine NFProgCallTreeExport.TSim.mono
          (fun v u ⟨t₁, hres, harr, hpc, hfn⟩ => ⟨⟨t₁, hres, harr⟩, ?_, hfn⟩) h8
        simp only [Bool.false_eq_true, ite_false]
        rw [hpc, hnopE]
        simp [selfNop]
    | true =>
        simp only [regionSitesB, hS, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hsite
        obtain ⟨⟨hfuse, hk1⟩, -⟩ := hsite
        set loop := d.nop.drop d.pre.length with hloop
        have hw : ∀ i ∈ loop, JasminLsemFuseMulHi.wireOK i.1 = true := fun i hi =>
          JasminLsemFuseMulHi.wireOK_of_fuseOKL hfuse i (List.mem_append_right _ hi)
        have heq : JasminLsemFuseMulHi.expI
            (JasminLsemFuseMulHi.fuseE (JasminLsemFuseMulHi.fuseLoPre d.pre loop))
            (d.pre ++ loop) 0 = d.pre ++ fuseMulHiRM loop := by
          rw [JasminLsemFuseMulHi.expI_append, Nat.zero_add,
            JasminLsemFuseMulHi.fuseMulHiRM_eq loop hw]
          congr 1
          · exact JasminLsemFuseMulHi.expI_fuseE_none d.pre 0 (fun k hk => by
              rw [Nat.zero_add, JasminLsemFuseMulHi.fuseLoPre,
                List.getElem?_append_left (by rw [List.length_replicate]; exact hk)]
              simp [hk])
          · have := JasminLsemFuseMulHi.expI_fuseE_shift
              (L := JasminLsemFuseMulHi.fuseLoPre d.pre loop)
              (L' := JasminLsemFuseMulHi.fuseLo loop) d.pre.length
              (fun k => by simp [JasminLsemFuseMulHi.fuseLoPre, List.getElem?_append_right])
              loop 0
            rwa [Nat.add_zero] at this
        have hL : ∀ (k : Nat) (i : LinstrRM) (dd : String), (d.pre ++ loop)[k]? = some i →
            (JasminLsemFuseMulHi.fuseLoPre d.pre loop)[k]? = some (some dd) →
            LprogIsa.shadowCall? i.1 = none := by
          intro k i dd hk hdd
          by_cases hkp : k < d.pre.length
          · rw [JasminLsemFuseMulHi.fuseLoPre,
              List.getElem?_append_left (by rw [List.length_replicate]; exact hkp)] at hdd
            simp [hkp] at hdd
          · have hkp' : d.pre.length ≤ k := Nat.le_of_not_lt hkp
            rw [JasminLsemFuseMulHi.fuseLoPre,
              List.getElem?_append_right (by rw [List.length_replicate]; exact hkp'),
              List.length_replicate] at hdd
            rw [List.getElem?_append_right hkp'] at hk
            obtain ⟨w', hw', hsw⟩ := JasminLsemFuseMulHi.fuseLoAux_site [] _ _ dd hdd
            rw [List.getElem?_map, hk] at hw'
            obtain rfl := (Option.some.inj hw').symm
            exact hsw
        have hE : JasminLsemFuseMulHi.E64 (fuseRegs σ nm)
            (entryV σ (frameE body sa) sa (unren d.ps)) := fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact X86Backend.FuseMulHiAbi.e64_of_abiEntryM habi x hx
          · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
            exact congrArg (·.1) (entryV_srcOf (un := unren d.ps) hSrc ha)
        rw [hsplit] at h8
        have hlenN : (d.pre ++ d.merged).length = (d.pre ++ loop).length := by
          rw [← hsplit, hnopE]
          simp [selfNop]
        rw [ite_eq_left rfl, ← heq]
        refine NFProgCallTreeExpand.tsim_fuse hfuse hL
          (fun v u u' hR ⟨t₁, hres, harr, hpc, hfn⟩ => ⟨⟨t₁, hres, fun y hy => ?_⟩, ?_,
            hR.lfn.trans hfn⟩)
          ⟨rfl, rfl, rfl, JasminLsemFuseMulHi.Agree.refl _,
            JasminLsemFuseMulHi.finv_start _ _ 0 _ _ (JasminLsemFuseMulHi.blk_zero _) hE⟩ h8
        have hkept : JasminLsemFuseMulHi.KeptN (g y) := by
          simpa [JasminLsemFuseMulHi.KeptN] using List.all_eq_true.mp hk1 _ (hobsE y hy)
        · rw [hR.base.arr _ hkept]
          exact harr y hy
        · rw [hR.pc, hpc, hlenN, JasminLsemFuseMulHi.pcI, List.take_of_length_le (le_refl _)]
  refine NFProgCallTreeExport.TSim.mono
    (fun v u ⟨hP, hpc, hfn⟩ => ⟨fun sa' hcellsB => ?_, hpc, hfn⟩) h9
  obtain ⟨t₁, hagr, harrU⟩ := hP
  obtain ⟨op, hop, harr⟩ := hagr.decodeArrM_single
  have hmem : operandName op ∈ r.res.map operandName := by simp [hop]
  rw [hop] at hres
  simp only [regionResultB, List.map] at hres
  split at hres
  · rename_i RA k' op' hσ hop'
    obtain rfl := (List.cons.inj hop').1
    simp only [Bool.and_eq_true, beq_iff_eq] at hres
    obtain ⟨⟨⟨rfl, hk⟩, hA⟩, hslot⟩ := hres
    obtain ⟨arr, harr', hw⟩ := hcellsB _ _ _ hslot
    have harr2 : u.prog.base.getArr (g (operandName op)) 64 m = some arr := harr'
    rw [getArr_of_larr_eq _ _ (harrU _ hmem)] at harr2
    have h2 : t₁.prog.base.getArr (operandName op) 64 m = some _ := harr
    rw [h2] at harr2
    obtain rfl := Option.some.inj harr2
    have hbase : abiBase (abiReg σ) sa
        (chainAliasO (calleeOutsT (some T))
          (regionCoCode σ nm (.stackArr 64 m) codeC [op]) (operandName op))
          = sa.regs RA := by
      have hA' : abiReg σ (chainAliasO (calleeOutsT (some T))
          (regionCoCode σ nm (.stackArr 64 m) codeC [op]) (operandName op)) = some RA := hA
      simp only [abiBase, hA']
    exact resultOf_words (σ := σ) (sa' := sa') (by rw [hσ, hk])
      fun j hj => by rw [← hbase]; exact hw j hj
  · cases hres

end Ref

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain
