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
`l` meets the contract of `l` (`SContract (runOf ctRegime qk) l.contract`). Both theorems of this
module are instances at `linked = [c]` of `RegionLinkCall.compileRegion_correct_linked_multi`,
at the contract kinds `.ins` and `.outC`. The route is
that of `RegionLinkCall.compileRegion_correct_linked_outO` with a word result: the reference
run of the gate (`RegionLinkCompose.regionCo_bytes_callee`) at the array positions of the
summary, the image run at the call sites `calleeSiteAt`
(`RegionLinkCompose.calleeBody_imgRun_at`),
whose operands at the array parameters are the arrays whose frame slots the argument
registers reload, and the run chain at the interface of the contract
(`ImageAddrCallMeets.haltsC_of_contractW_ins`, `ImageAddrCallMeets.haltsO_of_contractW_ins`)
over the wide class `ImageAddrCallW.printedAddrCWB`, with the parameters passed at each call
from `callParamsB_forall₂W`.

The conclusion is stated at the interface `l.contractSig c.args (some c.resReg)`: the bytes
decode to the caller program `pc` followed by the shifted block `qk`, this program halts
through the call, and `pc` halts with its call answered by the runs of `qk` from entry states
that satisfy the precondition of the contract, each in a state from which the layout reads
back the source value of the result.

## Main results

* `linkedSummary_eq_insSummary`: the summary of a linked function without an array result is
  its summary on parameters `ImageAddrCallArrChain.insSummary`.
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
  imgGateCBW_frameMark bitsDeadB_frameMark callParamsB_forall₂W sContract_guarded)
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
  obtain ⟨T, hsub, hne, -, -, -, hrest⟩ := RegionLinkCall.compileRegion_correct_linked_multi h hcf
  obtain rfl := CalleeTab.eq_one_of_sublist hsub hne
  have hmem : ∀ c' ∈ (CalleeTab.one c).fns, c' = c := fun c' hc' => List.mem_singleton.mp hc'
  rw [linkedSummary_eq_insSummary hk hn] at hTc
  obtain ⟨pc, -, ⟨sO, hO, hRO⟩, hC⟩ :=
    hrest (fun _ => .ins l c.ins c.resReg) (fun _ => runOf ctRegime qk)
      (fun c' hc' => by
        obtain rfl := hmem c' hc'
        exact ⟨⟨hc, hL, rfl, rfl, hpar, hnd, hfb⟩, hm⟩)
      hT (fun f pr' hf hp => by
        have hf' : f ≠ c.name := by simpa using hf
        exact ⟨hwo f pr' hf' hp, hrw f pr' hf' hp⟩)
      (fun c' hc' => by obtain rfl := hmem c' hc'; exact hTc) sa V hV hreg fuel hv
  obtain ⟨hdec, sC, hhC, hRC⟩ := hC (fun _ => qk)
    (fun c' hc' => by obtain rfl := hmem c' hc'; exact hqk)
    (fun c' hc' => by obtain rfl := hmem c' hc'; exact hnc) (by simp [CalleeTab.one])
    (fun _ _ => rfl)
  have hQ : X86Backend.LprogBytesLinkReloc.regionProg
      ((CalleeTab.one c).regionEntries fun _ => qk) = qk := by
    simp [CalleeTab.regionEntries, CalleeTab.one, X86Backend.LprogBytesLinkReloc.regionProg,
      X86Backend.LprogBytesLink.shiftProg]
  rw [hQ] at hdec hhC
  refine ⟨pc, hdec, ⟨sC, hhC, hRC⟩, sO, hO.mono fun t s s' ho => ?_, hRO⟩
  obtain ⟨f, -, ht, tr, hx⟩ := ho
  simp only [CalleeTab.symPos_one, CalleeTab.entryIdx_zero, Nat.add_zero] at ht
  simp only [X86Backend.ImageAddrCallMeets.CalleeKind.sig, CalleeData.ins_map_fst] at hx
  exact ⟨ht.symm, tr, hx⟩

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
  obtain ⟨T, hsub, hne, -, -, -, hrest⟩ := RegionLinkCall.compileRegion_correct_linked_multi h hcf
  obtain rfl := CalleeTab.eq_one_of_sublist hsub hne
  have hmem : ∀ c' ∈ (CalleeTab.one c).fns, c' = c := fun c' hc' => List.mem_singleton.mp hc'
  obtain ⟨pc, -, ⟨sO, hO, hRO⟩, hC⟩ :=
    hrest (fun _ => .outC l c.ins po n) (fun _ => runOf ctRegime qk)
      (fun c' hc' => by
        obtain rfl := hmem c' hc'
        exact ⟨⟨hc, hL, rfl, hpar, hnd, hfb⟩, hm⟩)
      hT (fun f pr' hf hp => by
        have hf' : f ≠ c.name := by simpa using hf
        exact ⟨hwo f pr' hf' hp, hrw f pr' hf' hp⟩)
      (fun c' hc' => by obtain rfl := hmem c' hc'; exact hTc) sa V hV hreg fuel hv
  obtain ⟨hdec, sC, hhC, hRC⟩ := hC (fun _ => qk)
    (fun c' hc' => by obtain rfl := hmem c' hc'; exact hqk)
    (fun c' hc' => by obtain rfl := hmem c' hc'; exact hnc) (by simp [CalleeTab.one])
    (fun _ _ => rfl)
  have hQ : X86Backend.LprogBytesLinkReloc.regionProg
      ((CalleeTab.one c).regionEntries fun _ => qk) = qk := by
    simp [CalleeTab.regionEntries, CalleeTab.one, X86Backend.LprogBytesLinkReloc.regionProg,
      X86Backend.LprogBytesLink.shiftProg]
  rw [hQ] at hdec hhC
  refine ⟨pc, hdec, ⟨sC, hhC, hRC⟩, sO, hO.mono fun t s s' ho => ?_, hRO⟩
  obtain ⟨f, -, ht, tr, hx⟩ := ho
  simp only [CalleeTab.symPos_one, CalleeTab.entryIdx_zero, Nat.add_zero] at ht
  simp only [X86Backend.ImageAddrCallMeets.CalleeKind.sig, CalleeData.ins_map_fst] at hx
  exact ⟨ht.symm, tr, hx⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkArr
