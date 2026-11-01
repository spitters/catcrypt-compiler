/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkRoute
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets

@[expose] public section

set_option autoImplicit false

/-!
# Correctness of a compiled body with one linked kernel at its contract

A program with a `call` that `compileRegion` compiles at the callee data `c` of one linked
function `l` whose parameters are scalars and read-only word arrays and whose result is a
word in a register runs on its bytes through the call of the code of `l`, when the code of
`l` meets the contract of `l` (`SContract (runOf ctRegime qk) l.contract`). The route is
that of `RegionLinkCall.compileRegion_correct_linked_outO` with a word result: the reference
run of the gate (`RegionLinkCompose.regionCo_bytes_callee`) at the array positions of the
summary, the image run at the call sites `calleeSiteAt`
(`RegionLinkCompose.calleeBody_imgRun_at`),
whose operands at the array parameters are the arrays whose frame slots the argument
registers reload, and the run chain at the interface of the contract
(`ImageAddrCallMeets.haltsC_of_contract_ins`, `ImageAddrCallMeets.haltsO_of_contract_ins`),
with the parameters passed at each call from `callParamsB_forall₂`.

The conclusion is stated at the interface `l.contractSig c.args (some c.resReg)`: the bytes
decode to the caller program `pc` followed by the shifted block `qk`, this program halts
through the call, and `pc` halts with its call answered by the runs of `qk` from entry states
that satisfy the precondition of the contract, each in a state from which the layout reads
back the source value of the result.

## Main results

* `linkedSummary_eq_insSummary`: the summary of a linked function without an array result is
  its summary on parameters `ImageAddrCallArrChain.insSummary`.
* `sContract_guarded`: a run relation that meets the contract of `l` meets it when guarded by
  the precondition of the interface of the contract.
* `compileRegion_correct_contract_ins`: the bytes of a calling body with one such linked
  function halt through the call, and the caller halts under the oracle of the callee
  guarded by the precondition of the contract, in a state from which the layout reads back
  the source value of the result.
* `compileRegion_correct_contract_out`: the same for one linked function whose result is the
  words of a destination array, at the interface `l.contractSig c.args none`; the
  destination operand of the call differs from every other array operand by the conjunct
  `outDestB` of the gate.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkArr

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (slotRen slotArrOf
  slotArrOf_some)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (ProcTable ProcSummary)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (HaltsC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiBase abiReg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArrChain (InsLayout insSummary
  insSummary_retWord)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (compileRegion_spec_linked
  calleeBytes_some cellBody_of_cellArrsOf_nil cellArrsOf_nil_of_regionCells_nil
  imgGateCB_frameMark)
open CatCrypt.Crypto.SecureCompilation.SepLogic (SContract)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun HaltsO oracleAt runOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall (guarded)

/-- **The summary of a linked function without an array result is its summary on
    parameters.** If the parameter kinds `linkedKinds l` of `l` are the kinds of `ins` and
    the result type of `l` is not an array, the summary `linkedSummary l` is
    `ImageAddrCallArrChain.insSummary l ins`. -/
theorem linkedSummary_eq_insSummary {l : CatCrypt.Crypto.Hax.LinkedFn}
    {ins : List (String × ArgKind)} (hk : linkedKinds l = ins.map (·.2))
    (hn : arrLen? l.res = none) : linkedSummary l = insSummary l ins := by
  simp only [linkedSummary, insSummary, hk, hn]

/-- **A run relation that meets the contract of `l` meets it when guarded** by the
    precondition of the interface `l.contractSig args res`: an entry state that satisfies
    the precondition of the contract at some logical variables satisfies that of the
    interface. -/
theorem sContract_guarded {l : CatCrypt.Crypto.Hax.LinkedFn} {X : CalleeRun}
    (h : SContract X l.contract) (args : List String) (res : Option String) :
    SContract (guarded (l.contractSig args res) X) l.contract where
  halts a s hs := let ⟨t, s', hx⟩ := h.halts a s hs; ⟨t, s', ⟨a, hs⟩, hx⟩
  post a s t s' hs hx := h.post a s t s' hs hx.2
  keep a s t s' hs hx := h.keep a s t s' hs hx.2
  ct a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hx₁ hx₂ :=
    h.ct a₁ a₂ s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hx₁.2 hx₂.2

/-- **Correctness of a calling body with one linked kernel on scalars and read-only
    arrays, at the contract.** Let `l` be a linked function whose callee data `c` passes its
    parameters `c.ins` in the registers of their names and returns a word in the register of
    `c.resReg` (`InsLayout l c.ins c.resReg`), whose parameter kinds are those of `c.ins`,
    whose result type is not an array, which has as many parameters as `c` has arguments,
    whose layout has distinct argument registers (`hnd`) and whose frame and return word fit
    below `2 ^ 64` (`hfb`). Let the code of `c` decode to the block `qk` without `call`, whose
    leaky runs under `ctRegime` meet the contract of `l`.

    Let `compileRegion σ a p [c]` give the bytes `bytes` on a program `p` with a `call`, and
    let the table `T` agree with the call environment `Ec`, hold summaries on words with word
    results at every other symbol, and give the symbol of `c` the summary `linkedSummary l`.
    From every entry state `sa` satisfying `σ.Regions`, at every valuation `V` that `σ` reads
    off `sa` at which `p` denotes `v` in `Ec` at some fuel, the bytes decode to the program
    `pc` of the caller followed by the shifted block `qk`, and:

    * the linked program halts through the call (`HaltsC`) from `sa` at index `0` in a state
      from which `σ` reads back the source value of the result;
    * the program `pc` halts from `sa` at index `0`, its call answered by the oracle
      `oracleAt pc.length` of the leaky runs of `qk` under `ctRegime` from entry states that
      satisfy the precondition of `l.contractSig c.args (some c.resReg)`, in a state from
      which `σ` reads back the same value. -/
theorem compileRegion_correct_contract_ins
    {l : CatCrypt.Crypto.Hax.LinkedFn} {c : CalleeData} (hc : l.calleeData = some c)
    (hL : InsLayout l c.ins c.resReg)
    (hk : linkedKinds l = c.ins.map (·.2)) (hn : arrLen? l.res = none)
    (hpar : l.params.length = c.args.length)
    (hnd : (l.layout.args.map (·.reg)).Nodup) (hfb : l.frame + 8 ≤ 2 ^ 64)
    {qk : List RInstr} (hqk : decodeLprog c.bytes = some qk) (hnc : ∀ tg, RInstr.call tg ∉ qk)
    (hm : SContract (runOf ctRegime qk) l.contract)
    {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {P : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion σ a p [c] = some (P, bytes)) (hcf : p.callFree = false)
    {Ec : CallEnv jasminDialect} {T : ProcTable} (hT : ProcsAgree Ec T)
    (hwo : ∀ f pr, f ≠ c.name → T f = some pr → pr.WordOnly)
    (hrw : ∀ f pr, f ≠ c.name → T f = some pr → pr.RetWord)
    (hTc : T c.name = some (linkedSummary l))
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denoteAt Ec fuel V = some v) :
    ∃ pc : List RInstr,
      decodeLprog bytes = some (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length qk)
      ∧ (∃ sa', HaltsC aMachine (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length qk) 0 sa sa'
        ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
      ∧ ∃ sa', HaltsO aMachine
          (oracleAt pc.length
            (guarded (l.contractSig c.args (some c.resReg)) (runOf ctRegime qk)))
          pc 0 sa sa'
        ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)) := by
  rw [linkedSummary_eq_insSummary hk hn] at hTc
  obtain ⟨⟨w, m, rfl⟩, hB, rx0, r, b, cert, hrx, hwb, hbs, hg, -⟩ :=
    compileRegion_spec_linked h hcf
  generalize hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCode (some c) r.code) r.res
    cert (some c) = d
  obtain ⟨hcres, -, -, hcclob, hcframe, -, -, -, -, -, -, hcaa⟩ :=
    CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hc
  -- The word result of `c`.
  obtain ⟨r0, hr0⟩ : ∃ r, c.res = .reg r := by
    cases hcr : c.res with
    | reg r => exact ⟨r, rfl⟩
    | out n =>
        rw [hcr] at hcres
        simp [CatCrypt.Crypto.Hax.LinkedFn.calleeRes, hL.result] at hcres
  have hcsig : c.res.reg? = some c.resReg := by
    simp only [CalleeData.resReg, hr0, CalleeRes.reg?]
  -- The array positions of `c` are those of the kinds of the parameters.
  have hkinds : l.layout.args.map (·.kind) = c.ins.map (·.2) := by
    have h2 := congrArg (List.map Prod.snd) hL.args
    simpa [List.map_map, Function.comp_def] using h2
  have hcaa' : c.arrArgs = CatCrypt.Crypto.Hax.insArrArgs (c.ins.map (·.2)) := by
    rw [hcaa, hkinds]
  have haa : LprogIsa.Isa.procArrArgs T = calleeAA (some c) := by
    funext f
    by_cases hf : f = c.name
    · subst hf
      simp [LprogIsa.Isa.procArrArgs, calleeAA, hTc, insSummary, hcaa']
    · cases hTf : T f with
      | none => simp [LprogIsa.Isa.procArrArgs, calleeAA, hTf, hf]
      | some pr =>
          have hw : pr.arrArgs = fun _ => none := hwo f pr hf hTf
          simp [LprogIsa.Isa.procArrArgs, calleeAA, hTf, hf, hw]
  have hao : LprogIsa.Isa.procOut T = calleeAO (some c) := by
    funext f
    by_cases hf : f = c.name
    · subst hf
      simp [LprogIsa.Isa.procOut, calleeAO, hTc, insSummary, hr0]
    · cases hTf : T f with
      | none => simp [LprogIsa.Isa.procOut, calleeAO, hTf, hf]
      | some pr =>
          have hw : pr.out = none := hrw f pr hf hTf
          simp [LprogIsa.Isa.procOut, calleeAO, hTf, hf, hw]
  have hkd : ∀ f pr, T f = some pr → pr.Kinded := by
    intro f pr hf
    by_cases hfc : f = c.name
    · subst hfc
      rw [hTc] at hf
      cases hf
      exact LprogIsa.ProcSummary.kinded_of_retWord (insSummary_retWord l c.ins)
    · exact LprogIsa.ProcSummary.kinded_of_retWord (hrw f pr hfc hf)
  obtain ⟨k, u, hu, hcb, hsep, hrelF, hacorr, hpc0, hbnd, hread⟩ :=
    RegionLinkCompose.regionCo_bytes_callee (regionExportableB_sound hB) hrx hwb hg hd hT hkd haa
      hao hTc sa V hV hreg fuel ((legalizeRegion_denoteAt Ec fuel p V).trans hv)
  -- The conjuncts of the gate.
  have hg' := hg
  simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hce⟩, hren⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, himg⟩⟩ := hg'
  have hcells : d.cells = [] := List.isEmpty_iff.mp hce
  rw [hcells] at himg
  simp only [renImageB, X86Backend.ImageAddrRouteW.slotArrC_nil, calleeImgB,
    Bool.and_eq_true] at himg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hphys⟩, hcls, hgate⟩, -⟩, hent⟩, -⟩, -⟩ := himg
  have hcellsE : d.cells = regionCells σ exportReg d.ps b (d.fused.drop d.pre.length) := by
    rw [← hd]; rfl
  have hcb0 : cellBody (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b = b :=
    cellBody_of_cellArrsOf_nil _ (cellArrsOf_nil_of_regionCells_nil (hcellsE ▸ hcells))
  rw [hcb0] at hphys hrelF
  -- The destination of every call site is the result register.
  have hs1 : ∀ p, (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b p).1
      = c.resReg := by
    intro p
    simp only [calleeSiteAt, hr0]
  -- The checks of the calling body.
  have hok := calleeBodyB_spec.mp hcb
  have hsi := hok.shapeImg
  have hsites := hok.callSites
  have hdead := hok.dead
  have hflags := hok.flags
  have hcond := hok.condLive
  have hseg := hok.deadSeg
  have hlive := hok.live0
  have hroomB := hok.stackRoom
  have hnn := hok.frameNonneg
  have hdead2 := hdead
  simp only [calleeDeadB, hr0, Bool.and_eq_true] at hdead2
  obtain ⟨hdo, hparB⟩ := hdead2
  have hdead' : X86Backend.ImageAddrCall.callDeadB
      (l.contractSig (c.ins.map (·.1)) (some c.resReg))
      (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
      (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
        b) d.outs).dead b = true := by
    unfold X86Backend.ImageAddrCall.callDeadB X86Backend.ImageAddrCall.exemptC at hdo ⊢
    simpa [CatCrypt.Crypto.Hax.LinkedFn.contractSig, CalleeData.sig, CalleeData.ins_map_fst,
      hcclob, hcsig] using hdo
  -- The bytes of the calling body.
  obtain ⟨rfl, hne, ds, prog, hss, hbr, hP, hp0⟩ := calleeBytes_some hbs
  -- The image run at the table.
  obtain ⟨fuel', t', himgrun, hobs⟩ := RegionLinkCompose.calleeBody_imgRun_at hcb hTc hpar
    ⟨⟨X86Backend.ImageAddrRoute.entryV σ (X86Backend.ImageAddrRoute.frameE b sa) sa
      (X86Backend.ImageAddrRoute.unren d.ps), a.fname⟩, false⟩
    u rfl rfl hbnd k hu (.inl (insSummary_retWord l c.ins))
  -- The caller separation at the renamed slot map.
  have RF := X86Backend.ImageAddrRoute.renB_spec hren
  have E := X86Backend.ImageAddrRoute.entryB_spec hent sa
  have hun : ∀ q A n, slotArrOf σ exportReg q = some (A, n) →
      X86Backend.ImageAddrRoute.unren d.ps (renOf d.ps A) = A := by
    intro q A n hq
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some hq
    exact (RF.unr j (List.getElem?_eq_some_iff.mp hj).1).2
  have hS0 := X86Backend.CalleeStackRoom.callerSep_of_regions E.rs hreg hroomB hnn
    (slotArr := slotArrOf σ exportReg) E.len
  have hS : X86Backend.ImageAddrCall.CallerSep (X86Backend.ImageAddrRoute.frameE b sa)
      (slotRen (slotArrOf σ exportReg) (renOf d.ps)) (X86Backend.ImageAddrRouteW.baseR σ sa d.ps)
      (X86Backend.DecodePrintedCFG.frameRsp b sa) l.frame := by
    rw [← hcframe]
    refine ⟨hS0.frames, fun q A' n j hq hj x hx => ?_⟩
    obtain ⟨A, hA, rfl⟩ := X86Backend.ImageAddrRoute.slotRen_some hq
    have hb : X86Backend.ImageAddrRouteW.baseR σ sa d.ps (renOf d.ps A)
        = abiBase (abiReg σ) sa A := by
      simp only [X86Backend.ImageAddrRouteW.baseR, hun q A n hA]
    rw [hb] at hx
    exact hS0.cells q A n j hA hj x hx
  -- The parameters passed at the entry of a call.
  have hgateI : X86Backend.ImageAddrSim.ImgGate (X86Backend.ImageAddrRoute.frameE b sa)
      (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b :=
    X86Backend.ImageAddrCall.imgGate_of_imgGateCB ((imgGateCB_frameMark b _ _).trans hgate)
  have hparF : ∀ s sa0 zf sA, X86Backend.ImageAddrSim.ImgRel
      (X86Backend.ImageAddrRoute.frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
      (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b s sa0 zf →
      X86Backend.DecodePrintedAddr.ACorr (X86Backend.DecodePrintedCFG.frameRsp b sa) sA sa0 →
      (∃ bi ra t, b[sa0.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      List.Forall₂ (X86Backend.LinkedFnCallee.ParamAt
        (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) sa0) c.ins
        (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b sa0.reg.lpc).2 :=
    fun _ _ _ _ hrel _ hcall => callParamsB_forall₂ hparB hsep hgateI hrel hcall
  -- The end of the run: the words of the arrays of the slot map at their bases.
  let Fin : LstateMF → AState → Prop := fun t sA => ∀ q A n,
    slotRen (slotArrOf σ exportReg) (renOf d.ps) q = some (A, n) →
      ∃ arr, t.prog.base.getArr A 64 n = some arr
        ∧ ∀ j (hj : j < n), read64 sA.mem
          (cellAt (X86Backend.ImageAddrRouteW.baseR σ sa d.ps A) j) = arr ⟨j, hj⟩
  have hfin : ∀ t0 sa0 zf sA, X86Backend.ImageAddrSim.ImgRel
      (X86Backend.ImageAddrRoute.frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
      (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b t0 sa0 zf →
      X86Backend.LprogBytesLinkReloc.FinLea (X86Backend.DecodePrintedCFG.frameRsp b sa)
        (X86Backend.LprogBytesDecode.Params.ofBody b).frame sa0 sA → Fin t0 sA := by
    rintro t0 sa0 zf sA hrel ⟨sB, hcB, rfl⟩ q A n hq
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A n hq
    refine ⟨arr, h1, fun j hj => ?_⟩
    rw [(X86Backend.DecodePrinted.evalInstrA_leaFrame sB _).2,
      ← X86Backend.DecodePrintedAddr.read64_eq_of_agree hcB.mem (hsep.red q A n j hq hj)]
    exact h2 j hj
  have hFin : ∀ t1 t2 sA, X86Backend.ImageAddrCall.AgreeOffF
      ((deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
        b) d.outs).dead t1.prog.base.reg.lpc) t1 t2 →
      Fin t2 sA → Fin t1 sA := by
    intro t1 t2 sA hag hF2 q A n hq
    obtain ⟨arr, h1, h2⟩ := hF2 q A n hq
    exact ⟨arr, by rw [X86Backend.ImageAddrSim.getArr_congr hag.arr]; exact h1, h2⟩
  have hbne : b ≠ [] := by
    intro hb
    simp [X86Backend.ImageAddrCall.printedAddrCB, hb] at hcls
  have hlen : (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc < b.length := by
    rw [hpc0]
    exact List.length_pos_iff.mpr hbne
  have hL0 : (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg)
      (renOf d.ps)) (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
      b) d.outs).live (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc = false := by
    rw [hpc0]
    simpa using hlive
  have hclsL : X86Backend.ImageAddrCall.printedAddrCB l.frame b = true := hcframe ▸ hcls
  -- The run through the call.
  obtain ⟨hdec, sA', hhalt, hfinal⟩ :=
    X86Backend.ImageAddrCallMeets.haltsC_of_contract_ins hsep hphys
      ((imgGateCB_frameMark b _ _).trans hgate) hsites ctRegime hL hm hnc hnd hfb hS hparF
      (fun p _ => hs1 p) hclsL hss (fun q hq => X86Backend.ImageAddrFrame.frameIn_eq q hq)
      (calleeSym c b) hqk hne hbr hP hdead' hflags hcond hTc hsi
      X86Backend.CheckedIsaCall.x86IsaK_checked (X86Backend.CheckedIsaCall.deadSteps_x86K hseg)
      hfin hFin fuel' himgrun rfl hlen hL0 (hrelF _) hacorr
  -- The run under the oracle of the callee guarded by the precondition of the contract.
  obtain ⟨sO, hhaltO, hfinalO⟩ :=
    X86Backend.ImageAddrCallMeets.haltsO_of_contract_ins hsep hphys
      ((imgGateCB_frameMark b _ _).trans hgate) hsites hL
      (sContract_guarded hm c.args (some c.resReg)) hnd hfb hS hparF (fun p _ => hs1 p)
      hclsL hss (fun q hq => X86Backend.ImageAddrFrame.frameIn_eq q hq)
      (calleeSym c b) hP hdead' hflags hcond hTc hsi X86Backend.CheckedIsaCall.x86IsaK_checked
      (X86Backend.CheckedIsaCall.deadSteps_x86K hseg) hfin hFin fuel' himgrun rfl hlen hL0
      (hrelF _) hacorr
  rw [← X86Backend.LprogBytesLinkReloc.expectedReloc_length _ _ _ _ _ hP] at hhaltO
  rw [hpc0] at hhalt hhaltO
  have hpos : X86Backend.DecodePrintedCFG.posOf ds 0
      = 0 + 1 := by
    simp [X86Backend.DecodePrintedCFG.posOf]
  rw [hpos] at hhalt hhaltO
  have hlen0 : 0 < prog.length := by
    rcases hq : prog with _ | ⟨x, xs⟩
    · rw [hq] at hp0; cases hp0
    · simp
  -- The read-back of the result: the arrays of the slot map, no observed register.
  have houts : d.outs = (regionRet σ exportReg (.stackArr w m) r.res).toList.map Prod.snd := by
    rw [← hd]; rfl
  have hR : ∀ sA, Fin t' sA → σ.ResultOf sa sA (denVal (.stackArr w m)
      (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m) .here
        v)) := by
    intro sA hfinal
    refine hread sA (fun q A n hq => ?_) (fun y hy => ?_)
    · have hq' : slotRen (slotArrOf σ exportReg) (renOf d.ps) q = some (renOf d.ps A, n) := by
        simp [slotRen, hq]
      obtain ⟨arr, h1, h2⟩ := hfinal q _ n hq'
      refine ⟨arr, ?_, fun j hj => ?_⟩
      · rw [X86Backend.ImageAddrSim.getArr_congr hobs.2.1.symm]
        exact h1
      · have h2' := h2 j hj
        simp only [X86Backend.ImageAddrRouteW.baseR, hun q A n hq] at h2'
        exact h2'
    · rw [houts] at hy
      simp [regionRet] at hy
  refine ⟨prog, hdec, ⟨sA', .go ?_ hhalt, hR sA' hfinal⟩, sO, .go ?_ hhaltO, hR sO hfinalO⟩
  · simp only [X86Backend.RInstrSemantics.step, List.getElem?_append_left hlen0, hp0]
    rfl
  · simp only [X86Backend.RInstrSemantics.step, hp0]
    rfl

/-- **Correctness of a calling body with one linked out kernel, at the contract.** Let `l` be
    a linked function whose callee data `c` has the parameters `ins` and the destination
    `po`, an array of `n` words, as out layout (`OutLayout l ins po n`), which has as many
    parameters as `c` has arguments, whose layout has distinct argument registers (`hnd`)
    and whose frame and return word fit below `2 ^ 64` (`hfb`). Let the code of `c` decode to
    the block `qk` without `call`, whose leaky runs under `ctRegime` meet the contract of `l`.

    Let `compileRegion σ a p [c]` give the bytes `bytes` on a program `p` with a `call`, and
    let the table `T` agree with the call environment `Ec`, hold summaries on words with word
    results at every other symbol, and give the symbol of `c` the summary `outSummary l ins
    n`. From every entry state `sa` satisfying `σ.Regions`, at every valuation `V` that `σ`
    reads off `sa` at which `p` denotes `v` in `Ec` at some fuel, the bytes decode to the
    program `pc` of the caller followed by the shifted block `qk`, and:

    * the linked program halts through the call (`HaltsC`) from `sa` at index `0` in a state
      from which `σ` reads back the source value of the result;
    * the program `pc` halts from `sa` at index `0`, its call answered by the oracle
      `oracleAt pc.length` of the leaky runs of `qk` under `ctRegime` from entry states that
      satisfy the precondition of `l.contractSig c.args none`, in a state from which `σ`
      reads back the same value.

    The destination operand of the call site differs from every other array operand by the
    conjunct `outDestB` of the gate (`outDestB_iff`). -/
theorem compileRegion_correct_contract_out
    {l : CatCrypt.Crypto.Hax.LinkedFn} {c : CalleeData} (hc : l.calleeData = some c)
    {ins : List (String × ArgKind)} {po : String} {n : Nat}
    (hL : X86Backend.LinkedFnCallee.OutLayout l ins po n) (hins : c.ins = ins)
    (hpar : l.params.length = c.args.length)
    (hnd : (l.layout.args.map (·.reg)).Nodup) (hfb : l.frame + 8 ≤ 2 ^ 64)
    {qk : List RInstr} (hqk : decodeLprog c.bytes = some qk) (hnc : ∀ tg, RInstr.call tg ∉ qk)
    (hm : SContract (runOf ctRegime qk) l.contract)
    {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {P : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion σ a p [c] = some (P, bytes)) (hcf : p.callFree = false)
    {Ec : CallEnv jasminDialect} {T : ProcTable} (hT : ProcsAgree Ec T)
    (hwo : ∀ f pr, f ≠ c.name → T f = some pr → pr.WordOnly)
    (hrw : ∀ f pr, f ≠ c.name → T f = some pr → pr.RetWord)
    (hTc : T c.name = some (X86Backend.LinkedFnCallee.outSummary l ins n))
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denoteAt Ec fuel V = some v) :
    ∃ pc : List RInstr,
      decodeLprog bytes = some (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length qk)
      ∧ (∃ sa', HaltsC aMachine (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length qk) 0 sa sa'
        ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)))
      ∧ ∃ sa', HaltsO aMachine
          (oracleAt pc.length (guarded (l.contractSig c.args none) (runOf ctRegime qk)))
          pc 0 sa sa'
        ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)) := by
  subst hins
  obtain ⟨⟨w, m, rfl⟩, hB, rx0, r, b, cert, hrx, hwb, hbs, hg, -⟩ :=
    compileRegion_spec_linked h hcf
  generalize hd : regionCoParts σ exportReg b (.stackArr w m) (calleeCode (some c) r.code) r.res
    cert (some c) = d
  obtain ⟨hcres, -, -, hcclob, hcframe, -, -, -, -, -, -, hcaa⟩ :=
    CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hc
  -- The out result of `c`, at its destination position `kd`.
  obtain ⟨n0, kd, hcr⟩ : ∃ n0 kd, c.res = .out n0 kd := by
    cases h' : c.res with
    | reg r =>
        rw [h'] at hcres
        simp [CatCrypt.Crypto.Hax.LinkedFn.calleeRes, hL.result] at hcres
    | out n0 kd => exact ⟨n0, kd, rfl⟩
  obtain ⟨r0, a0, hres0, hak, har, hakd⟩ :=
    CatCrypt.Crypto.Hax.LinkedFn.calleeRes_out (hcr ▸ hcres)
  rw [hL.result] at hres0
  cases hres0
  -- The parameter at the destination position is the destination.
  have hdk : c.ins[kd]? = some (po, ArgKind.words n) := by
    have h1 := congrArg (·[kd]?) hL.args
    simp only [List.getElem?_map, hak, Option.map_some] at h1
    cases hik : c.ins[kd]? with
    | none => rw [hik] at h1; cases h1
    | some q =>
        rw [hik] at h1
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
        have hpo : q.1 = po := X86Backend.DecodePrinted.phys_inj
          (hL.ins_gp q (List.mem_of_getElem? hik)) hL.po_gp (h1.1.symm.trans har)
        exact congrArg some (Prod.ext hpo (h1.2.symm.trans hakd))
  -- The array positions of `c` are those of the kinds of the parameters.
  have hkinds : l.layout.args.map (·.kind) = c.ins.map (·.2) := by
    have h2 := congrArg (List.map Prod.snd) hL.args
    simpa [List.map_map, Function.comp_def] using h2
  have hcaa' : c.arrArgs = CatCrypt.Crypto.Hax.insArrArgs (c.ins.map (·.2)) := by
    rw [hcaa, hkinds]
  have haa : LprogIsa.Isa.procArrArgs T = calleeAA (some c) := by
    funext f
    by_cases hf : f = c.name
    · subst hf
      simp [LprogIsa.Isa.procArrArgs, calleeAA, hTc, X86Backend.LinkedFnCallee.outSummary,
        hcaa']
    · cases hTf : T f with
      | none => simp [LprogIsa.Isa.procArrArgs, calleeAA, hTf, hf]
      | some pr =>
          have hw : pr.arrArgs = fun _ => none := hwo f pr hf hTf
          simp [LprogIsa.Isa.procArrArgs, calleeAA, hTf, hf, hw]
  have hao : LprogIsa.Isa.procOut T = calleeAO (some c) := by
    funext f
    by_cases hf : f = c.name
    · subst hf
      simp [LprogIsa.Isa.procOut, calleeAO, hTc, X86Backend.LinkedFnCallee.outSummary, hcr]
    · cases hTf : T f with
      | none => simp [LprogIsa.Isa.procOut, calleeAO, hTf, hf]
      | some pr =>
          have hw : pr.out = none := hrw f pr hf hTf
          simp [LprogIsa.Isa.procOut, calleeAO, hTf, hf, hw]
  have hkd : ∀ f pr, T f = some pr → pr.Kinded := by
    intro f pr hf
    by_cases hfc : f = c.name
    · subst hfc
      rw [hTc] at hf
      cases hf
      intro _ _ _
      rfl
    · exact LprogIsa.ProcSummary.kinded_of_retWord (hrw f pr hfc hf)
  obtain ⟨k, u, hu, hcb, hsep, hrelF, hacorr, hpc0, hbnd, hread⟩ :=
    RegionLinkCompose.regionCo_bytes_callee (regionExportableB_sound hB) hrx hwb hg hd hT hkd haa
      hao hTc sa V hV hreg fuel ((legalizeRegion_denoteAt Ec fuel p V).trans hv)
  -- The conjuncts of the gate.
  have hg' := hg
  simp only [regionCoB, Option.all, Bool.and_eq_true] at hg'
  rw [hd] at hg'
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hce⟩, hren⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, himg⟩⟩ := hg'
  have hcells : d.cells = [] := List.isEmpty_iff.mp hce
  rw [hcells] at himg
  simp only [renImageB, X86Backend.ImageAddrRouteW.slotArrC_nil, calleeImgB,
    Bool.and_eq_true] at himg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hphys⟩, hcls, hgate⟩, -⟩, hent⟩, -⟩, -⟩ := himg
  have hcellsE : d.cells = regionCells σ exportReg d.ps b (d.fused.drop d.pre.length) := by
    rw [← hd]; rfl
  have hcb0 : cellBody (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b = b :=
    cellBody_of_cellArrsOf_nil _ (cellArrsOf_nil_of_regionCells_nil (hcellsE ▸ hcells))
  rw [hcb0] at hphys hrelF
  -- The checks of the calling body.
  have hok := calleeBodyB_spec.mp hcb
  have hsi := hok.shapeImg
  have hsites := hok.callSites
  have hdead := hok.dead
  have hflags := hok.flags
  have hcond := hok.condLive
  have hseg := hok.deadSeg
  have hlive := hok.live0
  have hroomB := hok.stackRoom
  have hnn := hok.frameNonneg
  have hdead2 := hdead
  simp only [calleeDeadB, hcr, Bool.and_eq_true] at hdead2
  obtain ⟨hdo, hparB⟩ := hdead2
  -- The destination array at every call and the dead names at the interface of the contract.
  have hqA : ∀ i, (∃ bi ra t, b[i]? = some bi ∧ bi.li_i = .Lcall ra t) →
      ∃ qA, slotRen (slotArrOf σ exportReg) (renOf d.ps) qA
        = some ((calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b i).1, n) := by
    rintro i ⟨bi, ra, t, hb, hbi⟩
    exact calleeSite_dest hcr hdead hb hbi hdk
  have hdead' : X86Backend.ImageAddrCallOutChain.callDeadOutB
      (l.contractSig (c.ins.map (·.1)) none)
      (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
      (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
        b) d.outs).dead b = true := by
    unfold X86Backend.ImageAddrCallOutChain.callDeadOutB X86Backend.ImageAddrCall.exemptC
      at hdo ⊢
    simpa [CatCrypt.Crypto.Hax.LinkedFn.contractSig, CalleeData.sig, CalleeData.ins_map_fst,
      hcclob, hcr, CalleeRes.reg?] using hdo
  -- The bytes of the calling body.
  obtain ⟨rfl, hne, ds, prog, hss, hbr, hP, hp0⟩ := calleeBytes_some hbs
  -- The destination of every call site is the operand at the destination position.
  obtain ⟨hk, hik⟩ := List.getElem?_eq_some_iff.mp hdk
  have hA : ∀ i, ((po, ArgKind.words n),
      (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b i).1)
      ∈ c.ins.zip (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b i).2 := by
    intro i
    have hsite : calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b i
        = ((calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b i).2.getD kd "",
          (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b i).2) := by
      simp only [calleeSiteAt, hcr]
    have hk2 : kd < (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b i).2.length
        := by
      rw [calleeSiteAt_snd, CalleeData.siteArgs_length]
      exact hk
    rw [List.mem_iff_getElem]
    refine ⟨kd, by simp [hk, hk2], ?_⟩
    simp only [List.getElem_zip, hik]
    conv_rhs => rw [hsite]
    rw [List.getD_eq_getElem _ _ hk2]
  -- The image run at the table, at the call sites, whose destinations are operands.
  obtain ⟨fuel', t', himgrun, hobs⟩ := RegionLinkCompose.calleeBody_imgRun_at hcb hTc hpar
    ⟨⟨X86Backend.ImageAddrRoute.entryV σ (X86Backend.ImageAddrRoute.frameE b sa) sa
      (X86Backend.ImageAddrRoute.unren d.ps), a.fname⟩, false⟩
    u rfl rfl hbnd k hu (.inr fun i => (List.of_mem_zip (hA i)).2)
  -- The destination operand is no other array operand (`outDestB`), at every call.
  have hdst : ∀ i, (∃ bi ra t, b[i]? = some bi ∧ bi.li_i = .Lcall ra t) →
      ∀ r n', l.layout.result = .words r n' → ∀ p x,
      (p, x) ∈ c.ins.zip (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b i).2 →
      p.2 ≠ .scalar → X86Backend.DecodePrinted.phys p.1 ≠ r → ∀ p' x',
      (p', x') ∈ c.ins.zip
        (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b i).2 →
      X86Backend.DecodePrinted.phys p'.1 = r → x ≠ x' := by
    rintro i ⟨bi, ra, tg, hb, hbi⟩ r1 n1 hr1 p x hpx hs hpr p' x' hpx' hp'r
    rw [hL.result] at hr1
    cases hr1
    rw [calleeSiteAt_snd] at hpx hpx'
    have hod := (outDestB_iff hcr hdk).1 (outDestB_of_callParamsB hparB hb hbi)
    exact hod p x hpx hs (fun he => hpr (by rw [he])) p' x' hpx'
      (X86Backend.DecodePrinted.phys_inj (hL.ins_gp p' (List.of_mem_zip hpx').1) hL.po_gp hp'r)
  -- The caller separation at the renamed slot map.
  have RF := X86Backend.ImageAddrRoute.renB_spec hren
  have E := X86Backend.ImageAddrRoute.entryB_spec hent sa
  have hun : ∀ q A n, slotArrOf σ exportReg q = some (A, n) →
      X86Backend.ImageAddrRoute.unren d.ps (renOf d.ps A) = A := by
    intro q A n hq
    obtain ⟨j, a, hj, -, rfl, -⟩ := slotArrOf_some hq
    exact (RF.unr j (List.getElem?_eq_some_iff.mp hj).1).2
  have hS0 := X86Backend.CalleeStackRoom.callerSep_of_regions E.rs hreg hroomB hnn
    (slotArr := slotArrOf σ exportReg) E.len
  have hS : X86Backend.ImageAddrCall.CallerSep (X86Backend.ImageAddrRoute.frameE b sa)
      (slotRen (slotArrOf σ exportReg) (renOf d.ps)) (X86Backend.ImageAddrRouteW.baseR σ sa d.ps)
      (X86Backend.DecodePrintedCFG.frameRsp b sa) l.frame := by
    rw [← hcframe]
    refine ⟨hS0.frames, fun q A' n j hq hj x hx => ?_⟩
    obtain ⟨A, hA, rfl⟩ := X86Backend.ImageAddrRoute.slotRen_some hq
    have hb : X86Backend.ImageAddrRouteW.baseR σ sa d.ps (renOf d.ps A)
        = abiBase (abiReg σ) sa A := by
      simp only [X86Backend.ImageAddrRouteW.baseR, hun q A n hA]
    rw [hb] at hx
    exact hS0.cells q A n j hA hj x hx
  -- The parameters passed at the entry of a call.
  have hgateI : X86Backend.ImageAddrSim.ImgGate (X86Backend.ImageAddrRoute.frameE b sa)
      (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b :=
    X86Backend.ImageAddrCall.imgGate_of_imgGateCB ((imgGateCB_frameMark b _ _).trans hgate)
  have hparF : ∀ s sa0 zf sA, X86Backend.ImageAddrSim.ImgRel
      (X86Backend.ImageAddrRoute.frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
      (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b s sa0 zf →
      X86Backend.DecodePrintedAddr.ACorr (X86Backend.DecodePrintedCFG.frameRsp b sa) sA sa0 →
      (∃ bi ra t, b[sa0.reg.lpc]? = some bi ∧ bi.li_i = .Lcall ra t) →
      List.Forall₂ (X86Backend.LinkedFnCallee.ParamAt
        (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) sa0) c.ins
        (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b sa0.reg.lpc).2 :=
    fun _ _ _ _ hrel _ hcall => callParamsB_forall₂ hparB hsep hgateI hrel hcall
  -- The end of the run: the words of the arrays of the slot map at their bases.
  let Fin : LstateMF → AState → Prop := fun t sA => ∀ q A n,
    slotRen (slotArrOf σ exportReg) (renOf d.ps) q = some (A, n) →
      ∃ arr, t.prog.base.getArr A 64 n = some arr
        ∧ ∀ j (hj : j < n), read64 sA.mem
          (cellAt (X86Backend.ImageAddrRouteW.baseR σ sa d.ps A) j) = arr ⟨j, hj⟩
  have hfin : ∀ t0 sa0 zf sA, X86Backend.ImageAddrSim.ImgRel
      (X86Backend.ImageAddrRoute.frameE b sa) (slotRen (slotArrOf σ exportReg) (renOf d.ps))
      (X86Backend.ImageAddrRouteW.baseR σ sa d.ps) b t0 sa0 zf →
      X86Backend.LprogBytesLinkReloc.FinLea (X86Backend.DecodePrintedCFG.frameRsp b sa)
        (X86Backend.LprogBytesDecode.Params.ofBody b).frame sa0 sA → Fin t0 sA := by
    rintro t0 sa0 zf sA hrel ⟨sB, hcB, rfl⟩ q A n hq
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A n hq
    refine ⟨arr, h1, fun j hj => ?_⟩
    rw [(X86Backend.DecodePrinted.evalInstrA_leaFrame sB _).2,
      ← X86Backend.DecodePrintedAddr.read64_eq_of_agree hcB.mem (hsep.red q A n j hq hj)]
    exact h2 j hj
  have hFin : ∀ t1 t2 sA, X86Backend.ImageAddrCall.AgreeOffF
      ((deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg) (renOf d.ps))
        (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
        b) d.outs).dead t1.prog.base.reg.lpc) t1 t2 →
      Fin t2 sA → Fin t1 sA := by
    intro t1 t2 sA hag hF2 q A n hq
    obtain ⟨arr, h1, h2⟩ := hF2 q A n hq
    exact ⟨arr, by rw [X86Backend.ImageAddrSim.getArr_congr hag.arr]; exact h1, h2⟩
  have hbne : b ≠ [] := by
    intro hb
    simp [X86Backend.ImageAddrCall.printedAddrCB, hb] at hcls
  have hlen : (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc < b.length := by
    rw [hpc0]
    exact List.length_pos_iff.mpr hbne
  have hL0 : (deadTab (X86Backend.ImageAddrCall.callImg (slotRen (slotArrOf σ exportReg)
      (renOf d.ps)) (calleeSiteAt c (slotRen (slotArrOf σ exportReg) (renOf d.ps)) b)
      b) d.outs).live (X86Backend.ImageAddrRoute.entryA σ sa).reg.lpc = false := by
    rw [hpc0]
    simpa using hlive
  have hclsL : X86Backend.ImageAddrCall.printedAddrCB l.frame b = true := hcframe ▸ hcls
  -- The run through the call.
  obtain ⟨hdec, sA', hhalt, hfinal⟩ :=
    X86Backend.ImageAddrCallMeets.haltsC_of_contract_out hsep hphys
      ((imgGateCB_frameMark b _ _).trans hgate) hsites ctRegime hL hm hnc hnd hfb hS hqA
      (fun i _ => hA i) hparF hdst hclsL hss (fun q hq => X86Backend.ImageAddrFrame.frameIn_eq q hq)
      (calleeSym c b) hqk hne hbr hP hdead' hflags hcond hTc hsi
      X86Backend.CheckedIsaCall.x86IsaK_checked (X86Backend.CheckedIsaCall.deadSteps_x86K hseg)
      hfin hFin fuel' himgrun rfl hlen hL0 (hrelF _) hacorr
  -- The run under the oracle of the callee guarded by the precondition of the contract.
  obtain ⟨sO, hhaltO, hfinalO⟩ :=
    X86Backend.ImageAddrCallMeets.haltsO_of_contract_out hsep hphys
      ((imgGateCB_frameMark b _ _).trans hgate) hsites hL
      (sContract_guarded hm c.args none) hnd hfb hS hqA (fun i _ => hA i) hparF hdst
      hclsL hss (fun q hq => X86Backend.ImageAddrFrame.frameIn_eq q hq)
      (calleeSym c b) hP hdead' hflags hcond hTc hsi X86Backend.CheckedIsaCall.x86IsaK_checked
      (X86Backend.CheckedIsaCall.deadSteps_x86K hseg) hfin hFin fuel' himgrun rfl hlen hL0
      (hrelF _) hacorr
  rw [← X86Backend.LprogBytesLinkReloc.expectedReloc_length _ _ _ _ _ hP] at hhaltO
  rw [hpc0] at hhalt hhaltO
  have hpos : X86Backend.DecodePrintedCFG.posOf ds 0
      = 0 + 1 := by
    simp [X86Backend.DecodePrintedCFG.posOf]
  rw [hpos] at hhalt hhaltO
  have hlen0 : 0 < prog.length := by
    rcases hq : prog with _ | ⟨x, xs⟩
    · rw [hq] at hp0; cases hp0
    · simp
  -- The read-back of the result: the arrays of the slot map, no observed register.
  have houts : d.outs = (regionRet σ exportReg (.stackArr w m) r.res).toList.map Prod.snd := by
    rw [← hd]; rfl
  have hR : ∀ sA, Fin t' sA → σ.ResultOf sa sA (denVal (.stackArr w m)
      (Ctxt.Var.lookup (d := jasminDialect) (Γ := [.stackArr w m]) (t := .stackArr w m) .here
        v)) := by
    intro sA hfinal
    refine hread sA (fun q A n hq => ?_) (fun y hy => ?_)
    · have hq' : slotRen (slotArrOf σ exportReg) (renOf d.ps) q = some (renOf d.ps A, n) := by
        simp [slotRen, hq]
      obtain ⟨arr, h1, h2⟩ := hfinal q _ n hq'
      refine ⟨arr, ?_, fun j hj => ?_⟩
      · rw [X86Backend.ImageAddrSim.getArr_congr hobs.2.1.symm]
        exact h1
      · have h2' := h2 j hj
        simp only [X86Backend.ImageAddrRouteW.baseR, hun q A n hq] at h2'
        exact h2'
    · rw [houts] at hy
      simp [regionRet] at hy
  refine ⟨prog, hdec, ⟨sA', .go ?_ hhalt, hR sA' hfinal⟩, sO, .go ?_ hhaltO, hR sO hfinalO⟩
  · simp only [X86Backend.RInstrSemantics.step, List.getElem?_append_left hlen0, hp0]
    rfl
  · simp only [X86Backend.RInstrSemantics.step, hp0]
    rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkArr
