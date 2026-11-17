/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnFrame

/-!
# The call step at the answer read from the return state of the callee

`ImageAddrCall.ResStep` and `ImageAddrCall.SiteStep` state the call step of a callee at a
result `x` fixed before the call, on the `compileA` path the value of the procedure summary.
This module states the call step at the answer read from the return state of the callee by a
result reader `ρ : AState → BitVec 64`: after every run of the callee from the entry state of
the call, ending in the state `sc`, the image state after the write of the word `ρ sc` to the
destination is related to an address state at the next position. Results are words.

`SiteStepA.toSiteStep` gives the step at a fixed result back: where every run from the
precondition ends in a state at which `ρ` reads `w`, `SiteStepA` gives `SiteStep` at the word
`w`.

For a linked function on scalars and read-only arrays (`ImageAddrCallArrChain.InsLayout`), the
call step holds at the interface `LinkedFn.frameSig` of the frame contract and the reader of
the result register, for every run relation that meets that interface
(`siteStepAt_frame_ins`), with no summary and no meaning; `siteStepA_ins` is the step at the
hypotheses of the kind `ImageAddrCallMeets.CalleeKind.ins`.

## Main definitions

* `ResStepA`: the call step of a callee at the result reader `ρ`.
* `SiteStepA`: the step of a call site with the destination `dst` at the dead names before and
  after it, at the result reader `ρ`.

## Main results

* `ResStepA.toResStep`, `SiteStepA.toSiteStep`: the steps at a fixed word result.
* `haltsO_call_imageSA`: a call site from the relaxed relation, for every run of the callee,
  with the continuation of the run under an oracle that answers the callee.
* `siteStepAt_frame_ins`, `siteStepA_ins`: the step of a call site of a linked function on
  scalars and read-only arrays at the interface of the frame contract.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallAns

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr retOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk gpFacts phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf outOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
  (CalleeRun CalleeSig CalleeSpec HaltsO)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArrChain (InsLayout)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets
  (CalleeKind CallAt entryAt_at_call)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee (ParamAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnFrame (footBelow_frameSig)
open CatCrypt.Crypto.SecureCompilation.Haxc (ArgKind)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax (LinkedFn)

/-! ## 1. The call step at a result reader -/

/-- **The call step of a callee at the result reader `ρ`, written to `dst`.** From an image
    state `u` related by `ImgRel` to an address state at a call instruction that corresponds
    to a byte state, at every return index: the entry state of the call satisfies the
    precondition of `c`, and for every run of the callee, ending in `sc`, there is an address
    state at the next position that corresponds to the byte state after the return and is
    related, up to the names `exemptC c` and the flags, to `LprogIsa.retWord dst (ρ sc) u`. -/
def ResStepA (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (rsp : BitVec 64) (body : Lcmd) (X : CalleeRun)
    (c : CalleeSig) (ρ : AState → BitVec 64) (dst : String) (u : LstateMF) : Prop :=
  ∀ sa zf sA, ImgRel frame slotArr base body u sa zf → ACorr rsp sA sa →
    (∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) → ∀ ret,
    c.pre (entryOf ret sA) ∧ ∀ t sc, X (entryOf ret sA) t sc →
      ∃ sa', sa'.reg.lpc = sa.reg.lpc + 1 ∧ ACorr rsp (retOps.foldl aMachine.exec sc) sa'
        ∧ ImgRelF frame slotArr base body (exemptC c) (LprogIsa.retWord dst (ρ sc) u) sa'

/-- **The step of a call site with the destination `dst` at the result reader `ρ`**, at the
    names `E` dead before the call and `E'` dead after it: the callee has the call step at `ρ`
    from every state that agrees with `u` off `E`, and the names of `E` other than `dst` and
    the names `exemptC c` are among `E'`. -/
def SiteStepA (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (rsp : BitVec 64) (body : Lcmd) (X : CalleeRun)
    (c : CalleeSig) (ρ : AState → BitVec 64) (E E' : List String) (dst : String)
    (u : LstateMF) : Prop :=
  (∀ u', AgreeOffF E u u' → ResStepA frame slotArr base rsp body X c ρ dst u')
    ∧ ∀ r ∈ E.filter (fun r => r != dst) ++ exemptC c, r ∈ E'

section Steps

variable {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
  {base : String → BitVec 64} {rsp : BitVec 64} {body : Lcmd} {X : CalleeRun} {c : CalleeSig}
  {ρ : AState → BitVec 64}

/-- **The call step at a fixed word.** If every run of the callee from its precondition ends
    in a state at which `ρ` reads `w`, the call step at `ρ` is the call step at the word
    `w`. -/
theorem ResStepA.toResStep {dst : String} {u : LstateMF}
    (h : ResStepA frame slotArr base rsp body X c ρ dst u) {w : BitVec 64}
    (hx : ∀ s t sc, c.pre s → X s t sc → ρ sc = w) :
    ResStep frame slotArr base rsp body X c dst (.word w) u := by
  intro sa zf sA hrel hc hcall ret
  obtain ⟨hpre, hall⟩ := h sa zf sA hrel hc hcall ret
  refine ⟨hpre, fun t sc hrun => ?_⟩
  obtain ⟨sa', h1, h2, h3⟩ := hall t sc hrun
  rw [hx _ t sc hpre hrun] at h3
  exact ⟨sa', h1, h2, h3⟩

/-- **The step of a call site at a fixed word.** If every run of the callee from its
    precondition ends in a state at which `ρ` reads `w`, the step of the site at `ρ` with the
    destination `dst` is the step of the site from `u` to `LprogIsa.retWord dst w u`. -/
theorem SiteStepA.toSiteStep {E E' : List String} {dst : String} {u : LstateMF}
    (h : SiteStepA frame slotArr base rsp body X c ρ E E' dst u) {w : BitVec 64}
    (hx : ∀ s t sc, c.pre s → X s t sc → ρ sc = w) :
    SiteStep frame slotArr base rsp body X c E E' u (LprogIsa.retWord dst w u) :=
  ⟨dst, .word w, rfl, fun u' hag => (h.1 u' hag).toResStep hx, h.2⟩

/-- **A call site under an oracle that answers its callee, at the result reader `ρ`.** From an
    image state `u` related up to the names `E` and the flags to an address state at a call
    that corresponds to a byte state, with the step of the site at `ρ`, index `pc` of `prog` a
    call to `tgt`, and an oracle `O` that answers every run of the callee at `tgt`: the entry
    state of the call satisfies the precondition, and for every run of the callee, ending in
    `sc`, there is an address state at the next position, corresponding to the byte state
    after the return and related up to `E'` and the flags to `LprogIsa.retWord dst (ρ sc) u`,
    such that every run under `O` from `pc + 1` on that byte state extends to a run from
    `pc`. -/
theorem haltsO_call_imageSA {E E' : List String} {dst : String} {u : LstateMF}
    {sa : LstateA} (hI : ImgRelF frame slotArr base body E u sa)
    (hst : SiteStepA frame slotArr base rsp body X c ρ E E' dst u)
    {sA : AState} (hc : ACorr rsp sA sa)
    (hcall' : ∃ bi ra t, body[sa.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t)
    {prog : List RInstr} {pc tgt : Nat} (hcall : prog[pc]? = some (.call tgt))
    {O : Nat → AState → AState → Prop} (hO : ∀ s tr s', X s tr s' → O tgt s s') :
    c.pre (entryOf (pc + 1) sA) ∧ ∀ t sc, X (entryOf (pc + 1) sA) t sc →
      ∃ sa', sa'.reg.lpc = sa.reg.lpc + 1 ∧ ACorr rsp (retOps.foldl aMachine.exec sc) sa'
        ∧ ImgRelF frame slotArr base body E' (LprogIsa.retWord dst (ρ sc) u) sa'
        ∧ ∀ s'', HaltsO aMachine O prog (pc + 1) (retOps.foldl aMachine.exec sc) s'' →
            HaltsO aMachine O prog pc sA s'' := by
  obtain ⟨u', zf, hag, hrel⟩ := hI
  obtain ⟨hpre, hall⟩ := hst.1 u' hag sa zf sA hrel hc hcall' (pc + 1)
  refine ⟨hpre, fun t sc hrun => ?_⟩
  obtain ⟨sa', hpc, hA, w, zf', hag2, hrel2⟩ := hall t sc hrun
  exact ⟨sa', hpc, hA, ⟨w, zf', ((hag.retWord dst (ρ sc)).trans hag2).mono hst.2, hrel2⟩,
    fun s'' hr => .call hcall (hO _ t _ hrun) hr⟩

end Steps

/-! ## 2. The call site of a linked function at the frame contract -/

/-- **The step of the call site at position `p` of a linked function on scalars and read-only
    arrays, at the interface of the frame contract.** Let the run relation `X` meet the
    interface `LinkedFn.frameSig` of `l`, the caller be separated (`CallerSep`) at the frame
    size of `l`, and the operands of `site p` pass the parameters `ins` at every image state
    at position `p`. Then the step of the site at `p` with the destination `res` holds at the
    reader of the register of `res`, at every names `E` and `E'` that contain the names dead
    after the result. No summary and no meaning of `l` enter. -/
theorem siteStepAt_frame_ins {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {l : LinkedFn} {ins : List (String × ArgKind)} {res : String}
    (hX : CalleeSpec X (l.frameSig (ins.map (·.1)) (some res))) (hL : InsLayout l ins res)
    (hnd : (l.layout.args.map (·.reg)).Nodup) (hfb : l.frame + 8 ≤ 2 ^ 64)
    (hS : CallerSep frame slotArr base rsp l.frame) {site : Nat → String × List String}
    {p : Nat}
    (hpar : ∀ s sa zf sA, ImgRel frame slotArr base body s sa zf → ACorr rsp sA sa →
      sa.reg.lpc = p → List.Forall₂ (ParamAt slotArr base sa) ins (site p).2)
    {E E' : List String}
    (hsub : ∀ r ∈ E.filter (fun r => r != res)
      ++ exemptC (l.frameSig (ins.map (·.1)) (some res)), r ∈ E')
    {u : LstateMF} (hpc : u.prog.base.reg.lpc = p) :
    SiteStepA frame slotArr base rsp body X (l.frameSig (ins.map (·.1)) (some res))
      (fun sc => sc.regs (phys res)) E E' res u := by
  refine ⟨fun u' hag => ?_, hsub⟩
  intro sa zf sA hrel hc hcall ret
  have hsp : sa.reg.lpc = p := hrel.pc.trans (hag.pc.symm.trans hpc)
  obtain ⟨bi, ra, t, hb, hbi⟩ := hcall
  have hent := entryAt_at_call hsep hL.args hnd hfb hS hc (hpar u' sa zf sA hrel hc hsp)
    (fun r n h => by rw [hL.result] at h; cases h) ret
  have hpre : (l.frameSig (ins.map (·.1)) (some res)).pre (entryOf ret sA) := ⟨_, hent⟩
  refine ⟨hpre, fun t' sc hrun => ?_⟩
  obtain ⟨hA, hI, -⟩ := call_reestablishes hsep hphys hX hrel hc hb hbi ret hpre
    (footClear_of_callerSep hS (footBelow_frameSig hL.result _ _) hc.sp ret) hrun
    ⟨fun _ => 0, false, false, false⟩
  have hres : (outOf (retOps.foldl aMachine.exec sc) ⟨fun _ => 0, false, false, false⟩).reg res
      = sc.regs (phys res) :=
    (call_return hX ret sA hpre hrun).2.1 _ (gpFacts hL.res_gp).physNe
  exact ⟨_, rfl, hA, _, _, agreeOffF_retWord _ _ u' rfl
    (by simpa [clobN, hL.res_gp, LinkedFn.frameSig] using hL.res_clob) hres, hI⟩

/-- **The step of a call site of the symbol `f` at the kind `CalleeKind.ins`, at the interface
    of the frame contract.** Under the hypotheses of the calls of `f` at the kind
    `CalleeKind.ins l ins res`, for a run relation that meets the interface
    `LinkedFn.frameSig` of `l` and a caller separated at the frame bound `G`, the step of the
    site at a call position `p` of `f` holds at the reader of the register of `res`. -/
theorem siteStepA_ins {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {X : CalleeRun} {l : LinkedFn} {ins : List (String × ArgKind)} {res : String}
    (hX : CalleeSpec X (l.frameSig (ins.map (·.1)) (some res))) {G : Nat}
    (hS : CallerSep frame slotArr base rsp G) {site : Nat → String × List String} {f : String}
    (hk : (CalleeKind.ins l ins res).Ok frame slotArr base rsp body site f G) {p : Nat}
    (hcall : CallAt body f p) {E E' : List String}
    (hsub : ∀ r ∈ E.filter (fun r => r != (site p).1)
      ++ exemptC (l.frameSig (ins.map (·.1)) (some res)), r ∈ E')
    {u : LstateMF} (hpc : u.prog.base.reg.lpc = p) :
    SiteStepA frame slotArr base rsp body X (l.frameSig (ins.map (·.1)) (some res))
      (fun sc => sc.regs (phys res)) E E' (site p).1 u := by
  obtain ⟨hL, hnd, hfb, hle, hpar, hres⟩ := hk
  rw [hres p hcall] at hsub ⊢
  exact siteStepAt_frame_ins hsep hphys hX hL hnd hfb (hS.mono hle)
    (fun s sa zf sA hrel hc hp => by
      subst hp
      exact hpar s sa zf sA hrel hc hcall)
    hsub hpc

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallAns
