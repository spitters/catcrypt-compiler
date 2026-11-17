/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSiteAns
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack

/-!
# The answers at the calls of a calling body, at the answers of the callees

`NFProgCallTreeRefBack` relates the call tree of the program of a calling body to the target
trees at the answer relation `BackRA`, in which the source answer at a call is the value that
the summary of the procedure table computes on the argument words of the event. This module
states the same relation at the answers of the callees, for callees with a word result: after a
call of the symbol `f` ending in the return state `sc` of a run of the run relation `X f`, the
source answer is the value that the step `LprogCallCutAns.GlueA` writes at the word
`sc.regs (phys (resK f))` of the result register. The relation with the target trees is
`NFProgCallTreeOracle.RuttFA` at an arbitrary skip predicate `Sk`; no summary value enters the
relation of the answers, and no condition on the summaries at the call sites remains, since the
step `GlueA` is defined at every word.

## Main definitions

* `BackRAA`: the relation of the answers of a call event and of a linked call event of the
  image, at a reader `ρ` of the word result of a return state.

## Main results

* `callRet_of_glueA`: the step at a word answer at a call site is a state after the call of a
  source answer that the word writes.
* `answers_of_backRAA`: at `BackRAA`, every pair of answers is the failed answer or a callee
  answer whose source answer the step `GlueA` at the word read off the return state writes.
* `backRAA_iff_backRA`: at a symbol whose summary computes, at every return state of the callee
  run, the word that `ρ` reads off it, `BackRAA` is `BackRA`.
* `refCarriedA_of_tsim`, `refCarriedA_regionRef`: the relation `RefUpT` is carried by the cut
  programs of the reference at the answers of the callees (`RefCarriedA`).
* `ruttF_regionRef_segA`: the call tree of the program of a calling body against the target
  trees, at the simulation `CalleeSegCheckAns.segSimA_of_checks` of the segment check.
* `ruttF_regionRef_backA`: the same at the answer relation `BackRAA`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBackAns

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport hiding regName
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
  (CutRun IsSite SegTo entryPos)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCutAns (GlueA CutSimIA)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (ImgRelF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (Obs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck (segOutsAt siteMap)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheckAns (segSimA_of_checks)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiReg abiBase)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (atPc goto)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall eventEnv treeAt
  pureReader)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (CallOut CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack (callEvent)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBody (imgOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefCarried (RefUpT noneFail_treeAt)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack (BackRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsLinked (FinT entryImg
  cuts_of_calleeCutB)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsSiteAns (RefCarriedA
  glueA_of_isSite ruttF_calleeBody_refA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle (RuttFA)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose
open CatCrypt.Crypto.Hax (LinkedFn)

/-! ## 1. The answers at a call -/

/-- **The step at a word answer at a call site is a state after the call.** If the word `w`
    gives a state after the call of the answer `r` of the event `ev` at every destination and
    state, the step `GlueA` at `w` from a state at a call site of `ev` is a state after the call
    of `ev` at `some r`. Word results only: `GlueA` writes a word. -/
theorem callRet_of_glueA {T : LprogIsa.ProcTable} {P : LprogM} {ev : NFCall jasminDialect}
    {r : Ctxt.Valuation (d := jasminDialect) ev.resTys} {w : BitVec 64}
    (hout : ∀ (dst : String) (u : LstateMF),
      CallOut dst ev.resTys r u (LprogIsa.retWord dst w u))
    {p : Nat} {u v : LstateMF} (hsi : NFProgCallTreeExport.CallSite P ev u) (hpu : atPc P p u)
    (hg : GlueA T P p u w v) : CallRet P ev u (some r) v := by
  obtain ⟨dst, srcs, tag, k, hat, hf, -, -⟩ := hsi
  obtain rfl : k = p := hat.2.symm.trans hpu.2
  obtain ⟨i, pr, dst', srcs', hi, hq, rfl⟩ := hg
  rw [hf] at hi
  obtain rfl := Option.some.inj hi
  simp only [LprogIsa.procCall?_callShadow, Option.map_eq_some_iff, Prod.mk.injEq] at hq
  obtain ⟨-, -, -, rfl, -⟩ := hq
  exact ⟨dst, srcs, tag, k, r, hat, hf, rfl, hout dst u⟩

/-- **The relation of the answers at a call, at the answers of the callees**, at the callee
    runs `X` and a reader `ρ` of the word result of a return state of the callee of a symbol:
    the source answer fails, or it is a result `r`, the target answer is a return state `sc` of
    the callee run of the symbol of the event from the entry state of the linked call, and the
    word `ρ ev.name sc` gives a state after the call of `r` at every destination and state.
    Word results only: an event with a word-array result has no related answer but the failed
    one. -/
def BackRAA (ρ : String → AState → BitVec 64) (X : String → CalleeRun)
    (ev : NFCall jasminDialect) (e₂ : (kSig AState).Event)
    (a₁ : (nfCallSig jasminDialect).Resp ev) (a₂ : (kSig AState).Resp e₂) : Prop :=
  a₁ = none ∨ ∃ r sc tr, a₁ = some r ∧ a₂ = some sc ∧ X ev.name e₂.entry tr sc
    ∧ ∀ (dst : String) (u : LstateMF),
      CallOut dst ev.resTys r u (LprogIsa.retWord dst (ρ ev.name sc) u)

/-- **The answers at `BackRAA`.** Every pair of answers of a call event `ev` at a call site `u`
    of `P` at `p` and of a linked call event that `BackRAA` relates is the failed answer, or a
    return state `sc` of the callee run of the symbol of `ev` whose source answer the step
    `GlueA` at `p` at the word `ρ ev.name sc` writes. -/
theorem answers_of_backRAA {ρ : String → AState → BitVec 64} {X : String → CalleeRun}
    {T : LprogIsa.ProcTable} {P : LprogM} {ev : NFCall jasminDialect} {u : LstateMF} {p : Nat}
    (hsi : NFProgCallTreeExport.CallSite P ev u) (hat : atPc P p u)
    {e₂ : (kSig AState).Event} {a₁ : (nfCallSig jasminDialect).Resp ev}
    {a₂ : (kSig AState).Resp e₂} (h : BackRAA ρ X ev e₂ a₁ a₂) :
    a₁ = none ∨ ∃ sc tr, a₂ = some sc ∧ X ev.name e₂.entry tr sc
      ∧ ∀ v, GlueA T P p u (ρ ev.name sc) v → CallRet P ev u a₁ v := by
  rcases h with h | ⟨r, sc, tr, rfl, hsc, hX, hout⟩
  · exact Or.inl h
  · exact Or.inr ⟨sc, tr, hsc, hX, fun v hg => callRet_of_glueA hout hsi hat hg⟩

/-- **`BackRAA` is `BackRA` at the summary answer.** Let the summary `pr` of the symbol of `ev`
    in `PT` have the arity and the array positions of `ev`, and compute on the argument words of
    `ev`, at every return state `sc` of the callee run of the symbol from the entry state of
    `e₂`, the word `ρ ev.name sc`. Then the answers that `BackRA PT X` relates are those that
    `BackRAA ρ X` relates. -/
theorem backRAA_iff_backRA {PT : LprogIsa.ProcTable} {ρ : String → AState → BitVec 64}
    {X : String → CalleeRun} {ev : NFCall jasminDialect} {e₂ : (kSig AState).Event}
    {pr : LprogIsa.ProcSummary} (hpr : PT ev.name = some pr)
    (har : pr.arity = ev.argTys.length) (haa : pr.arrArgs = arrArgsOf ev.argTys)
    (hρ : ∀ tr sc, X ev.name e₂.entry tr sc →
      pr.result (wordsOf ev.args) = some (.word (ρ ev.name sc)))
    {a₁ : (nfCallSig jasminDialect).Resp ev} {a₂ : (kSig AState).Resp e₂} :
    BackRA PT X ev e₂ a₁ a₂ ↔ BackRAA ρ X ev e₂ a₁ a₂ := by
  constructor
  · rintro (h | ⟨r, rfl, ⟨pr', x, hpr', -, -, hx, hout⟩, sc, tr, hsc, hX⟩)
    · exact Or.inl h
    · rw [hpr] at hpr'
      obtain rfl := Option.some.inj hpr'
      rw [hρ tr sc hX] at hx
      obtain rfl := Option.some.inj hx
      exact Or.inr ⟨r, sc, tr, rfl, hsc, hX, fun dst u => by simpa using hout dst u⟩
  · rintro (h | ⟨r, sc, tr, rfl, hsc, hX, hout⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r, rfl, ⟨pr, _, hpr, har, haa, hρ tr sc hX,
        fun dst u => by simpa using hout dst u⟩, sc, tr, hsc, hX⟩

/-! ## 2. The reference carries the call tree at the answers of the callees -/

/-- **A relation of call trees and states at the entries of the cuts of a body is carried by its
    cut programs at the answers of the callees.** The hypotheses of
    `NFProgCallTreeRefCarried.refCarried_of_tsim` with a simulation `CutSimIA` at the steps
    `GlueA`, without the condition on the summaries at the call sites: at every image call, every
    pair of answers that `RA` relates is the failed answer or a return state `sc` of the callee
    run `X` whose source answer the step `GlueA` at the word `ρ f sc` writes. Then `RefUpT` is
    carried by the cut programs of `B` (`RefCarriedA`) at every skip predicate `Sk`, at the
    failed leaves `none`. Word results only. -/
theorem refCarriedA_of_tsim
    (Sk : (e : (nfCallSig jasminDialect).Event) → (nfCallSig jasminDialect).Resp e → Prop)
    (RE : (nfCallSig jasminDialect).Event → (kSig AState).Event → Prop)
    (RA : (e₁ : (nfCallSig jasminDialect).Event) → (e₂ : (kSig AState).Event) →
      (nfCallSig jasminDialect).Resp e₁ → (kSig AState).Resp e₂ → Prop)
    (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (rsp : BitVec 64) (body : Lcmd) (E : Nat → List String)
    (X : String → CalleeRun) (ρ : String → AState → BitVec 64) (pos : Nat → Nat)
    (tgt : String → Nat) (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value)
    (Fin : LstateMF → AState → Prop)
    {PT : LprogIsa.ProcTable} {outs : List String} {fn : String}
    {A B B' : List LinstrRM} {cut' : Option Nat → Option Nat → List LinstrRM}
    (sim : CutSimIA X86Backend.CheckedIsaCall.x86IsaK PT outs fn B B'
      (LprogCallCut.cutAt fn (freshLabel A) B) cut' (GlueA PT (singletonProgM fn B))
      (GlueA PT (singletonProgM fn B')))
    {α : Type} {RR : Option α → Option AState → Prop} {Post : α → LstateMF → Prop}
    (hcut : calleeCutB PT (freshLabel A) B = true) (hsub : ∀ i ∈ B, i ∈ A)
    (hPT : ∀ (k : Nat) (dst f : String) (srcs : List LOperand) (tag : MemTag),
      B[k]? = some (LprogIsa.callShadow dst f srcs, tag) → (PT f).isSome = true)
    (hleaf : ∀ v u, Post v u → u.prog.lfn = fn ∧ B.length ≤ u.prog.base.reg.lpc
      ∧ ∀ t', Obs outs u t' → ∀ sA, Fin t' sA → RR (some v) (some sA))
    {G : NFCall jasminDialect → Prop}
    (hsite : ∀ (ev : NFCall jasminDialect) (u : LstateMF) (p : Nat), G ev →
      NFProgCallTreeExport.CallSite (singletonProgM fn B) ev u →
      atPc (singletonProgM fn B) p u →
      ∀ u' q, sim.Q (some p) u u' → sim.site (some p) = some q →
      ∀ bi ra f l, body[q]? = some bi → bi.li_i = .Lcall ra (f, l) →
      ∀ sa sA, ImgRelF frame slotArr base body (E q) (goto u' q) sa → ACorr rsp sA sa →
        sa.reg.lpc = q →
        RE ev (callEvent aMachine sym rd (pos q) (tgt f) sA)
        ∧ ∀ a₁ a₂, RA ev (callEvent aMachine sym rd (pos q) (tgt f) sA) a₁ a₂ →
          a₁ = none ∨ ∃ sc tr, a₂ = some sc
            ∧ X f (X86Backend.ImageCallProbe.entryOf (pos q + 1) sA) tr sc
            ∧ ∀ v, GlueA PT (singletonProgM fn B) p u (ρ f sc) v →
              CallRet (singletonProgM fn B) ev u a₁ v) :
    RefCarriedA Sk RE RA RR (fun r => r = none) frame slotArr base rsp body E X ρ pos tgt sym rd
      Fin sim (RefUpT PT fn B G Post) := by
  have hcuts := cuts_of_calleeCutB (fn := fn) hcut hsub
  intro t₁ e s ⟨hfn, hpc, he, hle, hG, hnf, hT⟩
  cases t₁ with
  | ret o =>
      cases o with
      | none => exact Or.inl ⟨none, rfl, Or.inl rfl⟩
      | some v =>
          obtain ⟨k, u, hs, hP⟩ := hT
          obtain ⟨hfu, hlu, hR⟩ := hleaf v u hP
          have hseg : SegTo X86Backend.CheckedIsaCall.x86IsaK PT (singletonProgM fn B) s none u :=
            ⟨k, hs, by
              change (if u.prog.lfn = fn then B[u.prog.base.reg.lpc]? else none) = none
              rw [ite_eq_left hfu]
              exact List.getElem?_eq_none hlu⟩
          exact Or.inl ⟨some v, rfl, Or.inr ⟨u, LprogCallCut.cutRun_of_segTo
            X86Backend.CheckedIsaCall.x86IsaK_pcFree
            (X86Backend.CheckedIsaCall.x86IsaK_refusesProcs PT) (hcuts e none he trivial).1
            ⟨hfn, hpc⟩ hle hseg, hR⟩⟩
  | vis ev c =>
      obtain ⟨k, u, hs, hsi, hc⟩ := hT
      obtain ⟨dst, srcs, tag, p, hat, hf, hlen, hrd⟩ := hsi
      have hPTs := hPT p dst ev.name srcs tag hf
      have hproc : LprogCallCut.isProcB PT (LprogIsa.callShadow dst ev.name srcs, tag) = true := by
        change (LprogIsa.procCall? PT (LprogIsa.callShadow dst ev.name srcs)).isSome = true
        rw [LprogIsa.procCall?_callShadow, Option.isSome_map]
        exact hPTs
      have hsite' : IsSite PT B (some p) := ⟨_, hf, hproc⟩
      have hseg : SegTo X86Backend.CheckedIsaCall.x86IsaK PT (singletonProgM fn B) s (some p) u :=
        ⟨k, hs, hat, _, hf, hproc⟩
      have hplt : p < B.length := (List.getElem?_eq_some_iff.mp hf).1
      refine Or.inr ⟨ev, c, rfl, Or.inl ⟨p, u, hsite',
        LprogCallCut.cutRun_of_segTo X86Backend.CheckedIsaCall.x86IsaK_pcFree
          (X86Backend.CheckedIsaCall.x86IsaK_refusesProcs PT) (hcuts e (some p) he hsite').1
          ⟨hfn, hpc⟩ hle hseg, ?_⟩⟩
      intro u' q hQ hq bi ra f l hbi hcall sa sA hrel hac hpcq
      obtain ⟨hRE, hRA⟩ := hsite ev u p hG.1 ⟨dst, srcs, tag, p, hat, hf, hlen, hrd⟩ hat u' q
        hQ hq bi ra f l hbi hcall sa sA hrel hac hpcq
      refine ⟨hRE, fun a₁ a₂ hra => ?_⟩
      rcases hRA a₁ a₂ hra with rfl | ⟨sc, tr, hsc, hX, hret⟩
      · exact Or.inl ⟨none, hnf.1, rfl⟩
      · obtain ⟨v, hv⟩ := glueA_of_isSite (fn := fn) hsite' u (ρ f sc)
        have hat' := hv.atPc_succ hat
        exact Or.inr ⟨sc, tr, hsc, hX, v, hv, hat'.1, hat'.2, hsite',
          Nat.succ_le_of_lt hplt, hG.2 a₁, hnf.2 a₁, hc a₁ _ (hret v hv)⟩

/-- **The reference of a calling body carries the call tree of its program at the answers of
    the callees.** As `NFProgCallTreeRefBody.refCarried_regionRef`, with a simulation `CutSimIA`
    of the cut programs of `d.ref` by those of its image at the steps `GlueA`, and without the
    condition on the summaries at the call sites: at every image call related to a call state of
    `d.ref`, the source event and the call event of the image are related by `RE`, and every pair
    of answers that `RA` relates is the failed answer or a return state `sc` of the callee run `X`
    whose source answer the step `GlueA` at the word `ρ f sc` writes. Word results only. -/
theorem refCarriedA_regionRef {σ : AbiLayout} {fn : String}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) {r0 r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r0) (ht : ∃ w m, t = .stackArr w m)
    {ex : List String} {T : CalleeTab}
    (hw : regionWebs ex r0 (calleeAAT (some T)) (calleeAOT (some T)) = r) {b : Lcmd}
    {cert : List (String × String)}
    (hg : regionCoB σ exportReg b t r.code r.res cert (some T) fn = true) {d : CoParts}
    (hd : regionCoParts σ exportReg b t (calleeCodeT (some T) r.code) r.res cert (some T) = d)
    {G : NFCall jasminDialect → Prop} (hGT : ∀ e, G e → EvOK T e)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) (hG : AllEv G (treeAt pureReader eventEnv fuel p V))
    {PT : LprogIsa.ProcTable}
    (hT' : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length)
    (Sk : (e : (nfCallSig jasminDialect).Event) → (nfCallSig jasminDialect).Resp e → Prop)
    (RE : (nfCallSig jasminDialect).Event → (kSig AState).Event → Prop)
    (RA : (e₁ : (nfCallSig jasminDialect).Event) → (e₂ : (kSig AState).Event) →
      (nfCallSig jasminDialect).Resp e₁ → (kSig AState).Resp e₂ → Prop)
    (E : Nat → List String) (X : String → CalleeRun) (ρ : String → AState → BitVec 64)
    (pos : Nat → Nat) (tgt : String → Nat)
    (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value)
    {cut' : Option Nat → Option Nat → List LinstrRM}
    (sim : CutSimIA X86Backend.CheckedIsaCall.x86IsaK PT d.outs fn d.ref (imgOf σ T b d.ps)
      (LprogCallCut.cutAt fn (freshLabel (d.ref ++ imgOf σ T b d.ps)) d.ref) cut'
      (GlueA PT (singletonProgM fn d.ref)) (GlueA PT (singletonProgM fn (imgOf σ T b d.ps))))
    (hsite : ∀ (ev : NFCall jasminDialect) (u : LstateMF) (p : Nat), G ev →
      NFProgCallTreeExport.CallSite (singletonProgM fn d.ref) ev u →
      atPc (singletonProgM fn d.ref) p u →
      ∀ u' q, sim.Q (some p) u u' → sim.site (some p) = some q →
      ∀ bi ra f l, b[q]? = some bi → bi.li_i = .Lcall ra (f, l) →
      ∀ sa₁ sA, ImgRelF (frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
          (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b (E q) (goto u' q) sa₁ →
        ACorr (X86Backend.DecodePrintedCFG.frameRsp b sa) sA sa₁ → sa₁.reg.lpc = q →
        RE ev (callEvent aMachine sym rd (pos q) (tgt f) sA)
        ∧ ∀ a₁ a₂, RA ev (callEvent aMachine sym rd (pos q) (tgt f) sA) a₁ a₂ →
          a₁ = none ∨ ∃ sc tr, a₂ = some sc
            ∧ X f (X86Backend.ImageCallProbe.entryOf (pos q + 1) sA) tr sc
            ∧ ∀ v, GlueA PT (singletonProgM fn d.ref) p u (ρ f sc) v →
              CallRet (singletonProgM fn d.ref) ev u a₁ v) :
    let Post : Ctxt.Valuation (d := jasminDialect) [t] → LstateMF → Prop := fun v u =>
      (∀ sa' : AState,
        (∀ q A n, slotArrOf σ exportReg q = some (A, n) →
          ∃ arr, u.prog.base.getArr (renOf d.ps A) 64 n = some arr
            ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa A) j) = arr ⟨j, hj⟩) →
        σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
        ∧ u.prog.base.lpc = d.ref.length ∧ u.prog.lfn = fn
    RefCarriedA Sk RE RA
        (NFProgCallTreeExt.OutRel fun v sA => σ.ResultOf sa sA (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
        (fun r => r = none) (frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) (X86Backend.DecodePrintedCFG.frameRsp b sa) b
        E X ρ pos tgt sym rd (FinT σ sa d.ps) sim (RefUpT PT fn d.ref G Post)
      ∧ RefUpT PT fn d.ref G Post (treeAt pureReader eventEnv fuel p V) none
        (entryImg σ b sa d.ps fn) := by
  intro Post
  have hT0 := NFProgCallTreeRefChecked.tsim_regionRef_checked hp hr ht hw hg hd hGT sa V hV hreg
    fuel hG
  -- The checks of the calling body.
  have hg' := hg
  simp only [regionCoB, regionCopy_some_callee, regionOut, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, -⟩, hren⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := hg'
  have hok := calleeBodyBT_spec.mp hcb
  have RF := renB_spec hren
  have hun : ∀ q A n, slotArrOf σ exportReg q = some (A, n) → unren d.ps (renOf d.ps A) = A := by
    intro q A n h
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some h
    exact (RF.unr j (List.getElem?_eq_some_iff.mp hj).1).2
  have hDr := calleeTab_domEqT hT' hok.symsRef
  have hcut := calleeCutB_of_domEq hok.cutRef hDr
  have hPT : ∀ (k : Nat) (dst f : String) (srcs : List LOperand) (tag : MemTag),
      d.ref[k]? = some (LprogIsa.callShadow dst f srcs, tag) → (PT f).isSome = true := by
    intro k dst f srcs tag hk
    have h1 := NFProgCallTreeRefChecked.tab_of_callSymsB hok.symsRef k dst f srcs tag hk
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (by simpa [CalleeTab.tab] using h1)
    obtain ⟨pr, hpr, -⟩ := hT' f c hc
    rw [hpr]
    rfl
  refine ⟨refCarriedA_of_tsim Sk RE RA _ _ _ _ b E X ρ pos tgt sym rd _ sim hcut
    (fun i hi => List.mem_append_left _ hi) hPT ?_ hsite, rfl, rfl, trivial,
    Nat.zero_le _, hG, noneFail_treeAt fuel p V, hT0⟩
  intro v u ⟨hP, hpc, hfn⟩
  refine ⟨hfn, le_of_eq hpc.symm, fun t' hO sA hF w hw' => ?_⟩
  obtain rfl := Option.some.inj hw'
  refine ⟨sA, rfl, hP sA fun q A n hq => ?_⟩
  have hq' : slotRen (slotArrOf σ exportReg) (renOf d.ps) q = some (renOf d.ps A, n) := by
    simp only [slotRen, hq, Option.map_some]
  obtain ⟨arr, harr, hrd⟩ := hF q _ n hq'
  refine ⟨arr, ?_, fun j hj => ?_⟩
  · rw [← harr]
    exact getArr_of_larr_eq _ _ (by rw [hO.2.1])
  · rw [← hrd j hj]
    change _ = read64 _ (cellAt (abiBase (abiReg σ) sa (unren d.ps (renOf d.ps A))) j)
    rw [hun q A n hq]

/-! ## 3. The calling body against the target trees -/

/-- **The calling body against the target trees, at the simulation of the segment check, at the
    answers of the callees.** As `NFProgCallTreeRefRutt.ruttF_regionRef_seg`, with each function
    `c` of `T` of the kind `CalleeKind.ins (lf c.name) (insK c.name) (resK c.name)` and its run
    relation `X c.name` meeting the interface `LinkedFn.frameSig` of the frame contract (the
    hypotheses of `NFProgCallTreeCallsSiteAns.ruttF_calleeBody_refA`), at the simulation
    `CalleeSegCheckAns.segSimA_of_checks` of the segment check, and at the relation `RuttFA` at
    every skip predicate `Sk`. At an image call, the condition on the answers is that every pair
    the answer relation relates is the failed answer, or a return state `sc` of the callee run
    whose source answer the step `GlueA` at the word of the result register `resK f` of `sc`
    writes. No condition on the summaries at the call sites remains. Word results only. -/
theorem ruttF_regionRef_segA {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
    {bytes : List (BitVec 8)} {w m : Nat} {r : Exported} {cert : List (String × String)}
    (hbs : calleeBytes (some T) b = some bytes)
    (hg : regionCoB σ exportReg b (.stackArr w m) r.code r.res cert (some T) a.fname = true)
    {d : CoParts}
    (hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCodeT (some T) r.code) r.res cert
      (some T) = d)
    (kind : String → CalleeKind) (lf : String → LinkedFn)
    (insK : String → List (String × ArgKind)) (resK : String → String) (X : String → CalleeRun)
    (hK : ∀ c ∈ T.fns, (kind c.name).Top c
      ∧ kind c.name = .ins (lf c.name) (insK c.name) (resK c.name)
      ∧ CalleeSpec (X c.name)
        ((lf c.name).frameSig ((insK c.name).map (·.1)) (some (resK c.name))))
    {PT : LprogIsa.ProcTable} (hTc : ∀ c ∈ T.fns, PT c.name = some (kind c.name).summary)
    (sa : AState) (hreg : σ.Regions sa)
    {Γ : Ctxt jasminDialect} {p : NFProg jasminDialect Γ [.stackArr w m]}
    (hp : RegionExportable p) {r0 : Exported}
    (hr : exportR Γ.length a.fname p Γ.length 0 = some r0) {ex : List String}
    (hw : regionWebs ex r0 (calleeAAT (some T)) (calleeAOT (some T)) = r)
    {G : NFCall jasminDialect → Prop} (hGT : ∀ e, G e → EvOK T e)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (fuel : Nat)
    (hG : AllEv G (treeAt pureReader eventEnv fuel p V)) :
    ∃ (pc : List RInstr) (ds : List X86Backend.PhysAbiShape.DShape),
      calleeProg T b = some pc
      ∧ X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
      ∧ ∀ (Sk : (e : (nfCallSig jasminDialect).Event) → (nfCallSig jasminDialect).Resp e → Prop)
        (RE : (nfCallSig jasminDialect).Event → (kSig AState).Event → Prop)
        (RA : (e₁ : (nfCallSig jasminDialect).Event) → (e₂ : (kSig AState).Event) →
          (nfCallSig jasminDialect).Resp e₁ → (kSig AState).Resp e₂ → Prop)
        (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value),
        (∀ (ev : NFCall jasminDialect) (u : LstateMF) (p : Nat), G ev →
          NFProgCallTreeExport.CallSite (singletonProgM a.fname d.ref) ev u →
          atPc (singletonProgM a.fname d.ref) p u →
          ∀ u' q, Obs (segOutsAt d.ref (insTab d.ref d.outs) d.outs (some p)) u u' →
          u'.prog.lfn = u.prog.lfn → siteMap PT d.ref (imgOf σ T b d.ps) (some p) = some q →
          ∀ bi ra f l, b[q]? = some bi → bi.li_i = .Lcall ra (f, l) →
          ∀ sa₁ sA, ImgRelF (frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
              (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b
              ((deadTab (imgOf σ T b d.ps) d.outs).dead q) (goto u' q) sa₁ →
            ACorr (X86Backend.DecodePrintedCFG.frameRsp b sa) sA sa₁ → sa₁.reg.lpc = q →
            RE ev (callEvent aMachine sym rd (X86Backend.DecodePrintedCFG.posOf ds q)
              (pc.length + T.entryIdx (T.symPos f)) sA)
            ∧ ∀ a₁ a₂, RA ev (callEvent aMachine sym rd (X86Backend.DecodePrintedCFG.posOf ds q)
                (pc.length + T.entryIdx (T.symPos f)) sA) a₁ a₂ →
              a₁ = none ∨ ∃ sc tr, a₂ = some sc
                ∧ X f (X86Backend.ImageCallProbe.entryOf
                  (X86Backend.DecodePrintedCFG.posOf ds q + 1) sA) tr sc
                ∧ ∀ v, GlueA PT (singletonProgM a.fname d.ref) p u (sc.regs (phys (resK f))) v →
                  CallRet (singletonProgM a.fname d.ref) ev u a₁ v) →
        RuttFA Sk RE RA (NFProgCallTreeExt.OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (.stackArr w m)
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m)
                .here v)))
          (fun o => o = none) (treeAt pureReader eventEnv fuel p V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨pc, ds, hpc, hds, hR⟩ :=
    ruttF_calleeBody_refA hbs hg hd kind lf insK resK X hK hTc sa hreg
  refine ⟨pc, ds, hpc, hds, fun Sk RE RA sym rd hsite => ?_⟩
  -- The checks of the calling body.
  have hg' := hg
  simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := hg'
  have hok := calleeBodyBT_spec.mp hcb
  have hT' : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length := by
    intro f c hc
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    obtain ⟨har, -⟩ := (hK c hcm).1.facts
    exact ⟨_, hTc c hcm, har⟩
  have hsymB : X86Backend.ImageAddrCall.bodyCallSymsB (fun g => T.names.contains g) b
      = true := by
    have h1 := bodyCallSymsB_of_decodeSites hok.decode
    rwa [CalleeTab.lookup_isSome] at h1
  have hsi := callSymsB_callImg (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
    hok.callSites hsymB
  have hseg := (X86Backend.CallTableCongr.calleeSegB_congr (calleeTab_domEqT hT' hok.symsRef)
    (calleeTab_domEqT hT' hsi)).symm.trans hok.seg
  obtain ⟨hC, hU⟩ := refCarriedA_regionRef hp hr ⟨w, m, rfl⟩ hw hg hd hGT sa V hV hreg fuel hG
    hT' Sk RE RA _ X (fun f sc => sc.regs (phys (resK f))) _ _ sym rd (segSimA_of_checks hseg)
    fun ev u p hev hsi hat u' q hQ hq => hsite ev u p hev hsi hat u' q hQ.1 hQ.2 hq
  exact hR Sk RE RA _ _ sym rd (segSimA_of_checks hseg) _ hC _ hU

/-- **The calling body against the target trees at the answer relation `BackRAA`.** As
    `ruttF_regionRef_segA` at `RA := BackRAA ρ X` with `ρ f sc` the word of the result register
    `resK f` of `sc`: the answers at the calls are those of `answers_of_backRAA`, and the symbol
    of the image call is that of the event (`NFProgCallTreeRefArgs.callSym_eq`). The condition at
    the image calls of events of `G` is the relation `RE` of the event and the call event of the
    image alone. Word results only. -/
theorem ruttF_regionRef_backA {σ : AbiLayout} {a : AbiNames} {T : CalleeTab} {b : Lcmd}
    {bytes : List (BitVec 8)} {w m : Nat} {r : Exported} {cert : List (String × String)}
    (hbs : calleeBytes (some T) b = some bytes)
    (hg : regionCoB σ exportReg b (.stackArr w m) r.code r.res cert (some T) a.fname = true)
    {d : CoParts}
    (hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCodeT (some T) r.code) r.res cert
      (some T) = d)
    (kind : String → CalleeKind) (lf : String → LinkedFn)
    (insK : String → List (String × ArgKind)) (resK : String → String) (X : String → CalleeRun)
    (hK : ∀ c ∈ T.fns, (kind c.name).Top c
      ∧ kind c.name = .ins (lf c.name) (insK c.name) (resK c.name)
      ∧ CalleeSpec (X c.name)
        ((lf c.name).frameSig ((insK c.name).map (·.1)) (some (resK c.name))))
    {PT : LprogIsa.ProcTable} (hTc : ∀ c ∈ T.fns, PT c.name = some (kind c.name).summary)
    (sa : AState) (hreg : σ.Regions sa)
    {Γ : Ctxt jasminDialect} {p : NFProg jasminDialect Γ [.stackArr w m]}
    (hp : RegionExportable p) {r0 : Exported}
    (hr : exportR Γ.length a.fname p Γ.length 0 = some r0) {ex : List String}
    (hw : regionWebs ex r0 (calleeAAT (some T)) (calleeAOT (some T)) = r)
    {G : NFCall jasminDialect → Prop} (hGT : ∀ e, G e → EvOK T e)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (fuel : Nat)
    (hG : AllEv G (treeAt pureReader eventEnv fuel p V)) :
    ∃ (pc : List RInstr) (ds : List X86Backend.PhysAbiShape.DShape),
      calleeProg T b = some pc
      ∧ X86Backend.DecodeGen.shapesOf (X86Backend.LprogBytesDecode.Params.ofBody b) b = some ds
      ∧ ∀ (Sk : (e : (nfCallSig jasminDialect).Event) → (nfCallSig jasminDialect).Resp e → Prop)
        (RE : (nfCallSig jasminDialect).Event → (kSig AState).Event → Prop)
        (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value),
        (∀ (ev : NFCall jasminDialect) (u : LstateMF) (p : Nat), G ev →
          NFProgCallTreeExport.CallSite (singletonProgM a.fname d.ref) ev u →
          atPc (singletonProgM a.fname d.ref) p u →
          ∀ u' q, Obs (segOutsAt d.ref (insTab d.ref d.outs) d.outs (some p)) u u' →
          u'.prog.lfn = u.prog.lfn → siteMap PT d.ref (imgOf σ T b d.ps) (some p) = some q →
          ∀ bi ra f l, b[q]? = some bi → bi.li_i = .Lcall ra (f, l) →
          ∀ sa₁ sA, ImgRelF (frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
              (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b
              ((deadTab (imgOf σ T b d.ps) d.outs).dead q) (goto u' q) sa₁ →
            ACorr (X86Backend.DecodePrintedCFG.frameRsp b sa) sA sa₁ → sa₁.reg.lpc = q →
            RE ev (callEvent aMachine sym rd (X86Backend.DecodePrintedCFG.posOf ds q)
              (pc.length + T.entryIdx (T.symPos f)) sA)) →
        RuttFA Sk RE (BackRAA (fun f sc => sc.regs (phys (resK f))) X)
          (NFProgCallTreeExt.OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (.stackArr w m)
              (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m)
                .here v)))
          (fun o => o = none) (treeAt pureReader eventEnv fuel p V)
          fun n => targetTree aMachine pc sym rd n 0 sa := by
  obtain ⟨pc, ds, hpc, hds, hR⟩ := ruttF_regionRef_segA hbs hg hd kind lf insK resK X hK hTc sa
    hreg hp hr hw hGT V hV fuel hG
  refine ⟨pc, ds, hpc, hds, fun Sk RE sym rd hRE => ?_⟩
  -- The segment check at `PT` and the call sites of the body.
  have hg' := hg
  simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := hg'
  have hok := calleeBodyBT_spec.mp hcb
  have hT' : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length := by
    intro f c hc
    obtain ⟨hcm, rfl⟩ := CalleeTab.lookup_spec hc
    obtain ⟨har, -⟩ := (hK c hcm).1.facts
    exact ⟨_, hTc c hcm, har⟩
  have hsymB : X86Backend.ImageAddrCall.bodyCallSymsB (fun g => T.names.contains g) b
      = true := by
    have h1 := bodyCallSymsB_of_decodeSites hok.decode
    rwa [CalleeTab.lookup_isSome] at h1
  have hsi := callSymsB_callImg (siteFn T.lookup (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
    hok.callSites hsymB
  have hseg := (X86Backend.CallTableCongr.calleeSegB_congr (calleeTab_domEqT hT' hok.symsRef)
    (calleeTab_domEqT hT' hsi)).symm.trans hok.seg
  refine hR Sk RE (BackRAA _ X) sym rd fun ev u p hev hcs hat u' q hO hfn hq bi ra f l hb hbi
    sa₁ sA hrel hac hpcq => ⟨hRE ev u p hev hcs hat u' q hO hfn hq bi ra f l hb hbi sa₁ sA hrel
      hac hpcq, fun a₁ a₂ hra => ?_⟩
  obtain ⟨dst, srcs, tag, k, hat', hf, hlen, hrd⟩ := hcs
  obtain rfl : k = p := hat'.2.symm.trans hat.2
  obtain rfl := NFProgCallTreeRefArgs.callSym_eq hseg hok.callSites hf hq hb hbi
  exact answers_of_backRAA ⟨dst, srcs, tag, k, hat', hf, hlen, hrd⟩ hat hra

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBackAns
