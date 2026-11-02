/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkRoute
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkArr
public import CatCrypt.Crypto.SecureCompilation.Haxc.LinkedKernel

@[expose] public section

set_option autoImplicit false

/-!
# The hax compiler on a module with linked kernels

The bytes of `compileA` on a program with a `call` halt through the call of the code of a
linked function of the module, from every entry state with a source run: the source run
denotes the source value at the environment of the linked functions alone
(`RegionLinkCall.haxEntry_run_linkedEnv`), and the calling body compiled at the data of
the callee runs through its call (`RegionLinkCall.compileRegion_correct_linked`). The
compiler theorems of the region line combine this case with the program without `call`.

## Main results

* `haxEntry_call_halts`, `eq_of_append_shiftProg`: the runs of the bytes of `compileA` on a
  program with a `call` from every entry state with a source run, and the calling body of
  such a program determined by the program.
* `correct_of_compileARegion`: the compiler theorem of the region line on a module whose
  linked functions are linked kernels with distinct names.
* `haxc_correct_auto`: the compiler theorem on a module whose linked functions are linked
  kernels with distinct names; on a module without linked functions its hypotheses
  hold vacuously and the bytes halt.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions

section Linked

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (HaltsC)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (HaltsO oracleAt runOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall (guarded)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)

/-- **The runs of a calling body of `compileA`.** Let the linked functions of `m` have
    distinct names and each be a linked kernel. Let the translation of the hax entry
    return `q0` on `m`, the chain with the declared procedures of `m` return a program `p`
    with a `call`, and `compileRegion` at the data `c` of the linked function `l` of `m`
    alone return `(P, bytes)` on `p`. Then the code of `c` decodes to `qk`, the bytes decode
    to `pc ++ shiftProg pc.length qk`, and from every entry state `sa` satisfying
    `σ.Regions` with a source run of `m` to `v`, the program halts through the call
    (`HaltsC`) in a state from which `σ` reads back `v`, and the calling body `pc` halts
    with its call answered by the oracle of the leaky runs of `qk` guarded by the
    precondition of the interface of the contract `l.contractSig c.args c.res.reg?` in such
    a state. The source run denotes the source value in `linkedEnv m`
    (`haxEntry_run_linkedEnv`), hence in the environment `linkedEnvAt m l.name` of `l` alone,
    since every call of `p` names `l` (`callsTo_of_compileRegion`, `denoteAt_linkedEnvAt`);
    the table `summaryTable l` agrees with it (`procsAgree_summaryTable`), and the runs are
    `compileRegion_correct_contract_ins` or `compileRegion_correct_contract_out` at the
    shape of the code of `l`. -/
theorem haxEntry_call_halts {m : HaxModule} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hnd : (m.linked.map (·.name)).Nodup)
    (hk : ∀ l ∈ m.linked, LinkedKernel l)
    {q0 : Σ t : NFDialect.NfTy,
      NFProg NFDialect.nfDialect (CatCrypt.Crypto.Hax.ImpToNF.entryCtx (NFToRoute.abiEntry σ))
        [t]}
    (hq0 : haxEntry.toNF σ m = some q0)
    {p : NFProg jasminDialect (nfCtx σ)
      [CryptoToJasminCom.mapTy (CatCrypt.Crypto.Hax.NFToCat.catTy q0.1)]}
    (hp : (extChain (haxEntry.decls m) _ q0.1).run q0.2 = some p) (hcf : p.callFree = false)
    {l : LinkedFn} (hl : l ∈ m.linked) {c : CalleeData} (hlc : l.calleeData = some c)
    (h1 : compileRegion σ (haxEntry.names fname σ) p [c] = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v) :
    ∃ pc qk, decodeLprog c.bytes = some qk
      ∧ decodeLprog bytes = some (pc ++ shiftProg pc.length qk)
      ∧ (∃ sa', HaltsC aMachine (pc ++ shiftProg pc.length qk) 0 sa sa' ∧ σ.ResultOf sa sa' v)
      ∧ ∃ sa', HaltsO aMachine
          (oracleAt pc.length (guarded (l.contractSig c.args c.res.reg?) (runOf ctRegime qk)))
          pc 0 sa sa' ∧ σ.ResultOf sa sa' v := by
  have K := hk l hl
  obtain ⟨qk, hqk, hm⟩ := K.contract_code hlc
  obtain ⟨hcres, hname, hcargs, -, -, -, -, -, -, -, -⟩ :=
    CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc
  -- The code of the callee has no `call`.
  obtain ⟨-, -, -, r, b, cert, -, -, -, hg, -⟩ := compileRegion_spec_linked h1 hcf
  have hnc := (regionCoB_callee hg).2 c (by simp [CalleeTab.one]) qk hqk
  -- The source run at the linked function `l` alone.
  obtain ⟨k, V, x, hV, hvx, hx⟩ := haxEntry_run_linkedEnv hq0 hp hsep hrun
  have hx' : p.denoteAt (linkedEnvAt m l.name) k V = some (HVector.cons x .nil) := by
    rw [denoteAt_linkedEnvAt (hname ▸ callsTo_of_compileRegion h1 hcf)]
    exact hx
  -- The table of `l` alone.
  have hT := procsAgree_summaryTable hnd hl K.sem_kinds K.res_slice
  have hcl : ∀ f pr, f ≠ c.name → summaryTable l f = some pr → False := by
    intro f pr hf ht
    by_cases hfl : f = l.name
    · exact hf (hfl.trans hname.symm)
    · simp [summaryTable, hfl] at ht
  have hwo : ∀ f pr, f ≠ c.name → summaryTable l f = some pr → pr.WordOnly :=
    fun f pr hf ht => (hcl f pr hf ht).elim
  have hrw : ∀ f pr, f ≠ c.name → summaryTable l f = some pr → pr.RetWord :=
    fun f pr hf ht => (hcl f pr hf ht).elim
  have hTc : summaryTable l c.name = some (linkedSummary l) := by
    simp [summaryTable, hname]
  have hn : l.params.length = c.args.length := by
    rw [hcargs, List.length_map]
    exact K.arity
  rcases (K.code c hlc).1 with ⟨hL, hres⟩ | ⟨po, n, hL, hres⟩
  · -- Scalars and read-only arrays with a word result.
    have hkinds : linkedKinds l = c.ins.map (·.2) := by
      rw [K.kinds c hlc]
      have h2 := congrArg (List.map Prod.snd) hL.args
      simpa [List.map_map, Function.comp_def] using h2
    have hcsig : c.res.reg? = some c.resReg := by
      cases hcr : c.res with
      | reg r => simp only [CalleeData.resReg, hcr, CalleeRes.reg?]
      | out n' kd =>
          rw [hcr] at hcres
          simp [CatCrypt.Crypto.Hax.LinkedFn.calleeRes, hL.result] at hcres
    obtain ⟨pc, hdec, ⟨sa1, hC, hR1⟩, sa2, hO, hR2⟩ :=
      RegionLinkArr.compileRegion_correct_contract_ins hlc hL hkinds hres hn K.args_nodup
        K.frame_fit hqk hnc hm h1 hcf hT hwo hrw hTc sa V hV hsep k hx'
    rw [hcsig]
    refine ⟨pc, qk, hqk, hdec, ⟨sa1, hC, ?_⟩, sa2, hO, ?_⟩
    · rw [hvx]
      exact hR1
    · rw [hvx]
      exact hR2
  · -- Scalars and word arrays with the words of a destination array as result.
    have hkinds : linkedKinds l = c.ins.map (·.2) := by
      rw [K.kinds c hlc]
      have h2 := congrArg (List.map Prod.snd) hL.args
      simpa [List.map_map, Function.comp_def] using h2
    have hcsig : c.res.reg? = none := by
      cases hcr : c.res with
      | reg r =>
          rw [hcr] at hcres
          simp [CatCrypt.Crypto.Hax.LinkedFn.calleeRes, hL.result] at hcres
      | out n' kd => rfl
    rw [linkedSummary_eq_outSummary hkinds hres] at hTc
    obtain ⟨pc, hdec, ⟨sa1, hC, hR1⟩, sa2, hO, hR2⟩ :=
      RegionLinkArr.compileRegion_correct_contract_out hlc hL rfl hn K.args_nodup
        K.frame_fit hqk hnc hm h1 hcf hT hwo hrw hTc sa V hV hsep k hx'
    rw [hcsig]
    refine ⟨pc, qk, hqk, hdec, ⟨sa1, hC, ?_⟩, sa2, hO, ?_⟩
    · rw [hvx]
      exact hR1
    · rw [hvx]
      exact hR2

/-- **The calling body of a linked program is determined by the program.** Two calling
    bodies `pr` and `pc` followed by the same code `q` with its targets raised by their
    lengths give the same program only when `pr = pc`. -/
theorem eq_of_append_shiftProg {pr pc q : List RInstr}
    (h : pr ++ shiftProg pr.length q = pc ++ shiftProg pc.length q) : pr = pc := by
  have hl : pr.length = pc.length := by
    have := congrArg List.length h
    simp only [List.length_append, shiftProg, List.length_map] at this
    omega
  rw [hl] at h
  exact List.append_cancel_right h

end Linked

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts HaltsC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (HaltsO oracleAt runOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall (guarded)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (entryA)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (RunSafe)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (runA)
open CatCrypt.Crypto.SecureCompilation.SepLogic.Addr (AccessIn)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)

/-- **The compiler theorem of the region line, on a module.** Let the linked functions
    of `m` have distinct names (`hnd`) and each be a linked kernel (`hk`,
    `LinkedKernel`). For the result of `compileARegion` on `m`, the bytes decode to a program
    `prog`, and from every entry state `sa` satisfying `σ.Regions`, every value `v` of a
    source run of `m` from `sa` (`haxRuns σ m sa v`: a run of the source reading of the
    entry, from a hax environment `σ` reads off `sa`, at the table of the module, to a value
    that is not a control-flow value) is read back by `σ`:

    * either from a state `sa'` at which `prog` halts from `sa`, whose stack register holds
      its value in `sa`, and whose memory agrees with that of `sa` at every byte outside the
      stack words `%rsp + o`, `frameLo ≤ o ≤ frameHi`, and outside the words of each pointer
      region of `σ`, at the registers of `sa`; some run of the address machine on a body
      from `entryA σ sa` then halts and stores to and loads from `layoutMem σ sa` only,
    * or the program is `pc ++ shiftProg pc.length q` for the decoded code `q` of the data
      `c` of a linked function of `m`; the program halts through the call (`HaltsC`) from
      `sa` in a state from which `σ` reads back `v`, and `pc` halts from `sa` with its call
      answered by the oracle of the leaky runs of `q` guarded by the precondition of
      `c.sig`, the premise of `compileRegion_call_bytes_ct`, in such a state.

    A call of a function of the module in the source run is the run of the source reading
    of the extraction of the callee under the table of the module. On a module without
    linked functions, such as a single function (`te : HaxModule`), `hnd` and `hk` hold
    vacuously (the default arguments close them when `m.linked` reduces to `[]`) and only
    the first case occurs, since `m.linked.filterMap LinkedFn.calleeData` is empty; on a
    single function the source run is a run of the source reading of `te` at `hax64WExit`
    (`haxRuns_single`). A
    program without `call` is the case of `NFEntry.compileR_correct`; a program with a
    `call` is that of `haxEntry_call_halts` at the callee `compileRegion_singleton` finds. -/
theorem correct_of_compileARegion (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileARegion m σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
          ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false)
      ∨ ∃ c ∈ m.linked.filterMap LinkedFn.calleeData, ∃ pc q,
          decodeLprog c.bytes = some q ∧ prog = pc ++ shiftProg pc.length q
          ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
          ∧ ∃ sa', HaltsO aMachine (oracleAt pc.length (guarded c.sig (runOf ctRegime q)))
              pc 0 sa sa' ∧ σ.ResultOf sa sa' v) := by
  unfold compileARegion at hc
  erw [NFEntry.compileR_eq_bind] at hc
  obtain ⟨q0, hq0, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨p, hp, hc⟩ := Option.bind_eq_some_iff.mp hc
  cases hcf : p.callFree with
  | true =>
      rw [compileRegion_of_callFree _ _ hcf] at hc
      have hc' : haxEntry.compileR m σ fname = some (P, bytes) := by
        simp only [NFEntry.compileR, NFEntry.chainNF, hq0, Option.bind_some, hp, Option.map_some]
        exact hc
      obtain ⟨prog, sa', hd, h⟩ :=
        haxEntry.compileR_correct m σ fname P bytes hc' sa hsep v hrun
      exact ⟨prog, hd, .inl ⟨sa', h⟩⟩
  | false =>
      obtain ⟨c, hcm, h1⟩ := compileRegion_singleton hc hcf
      obtain ⟨l, hl, hlc⟩ := List.mem_filterMap.mp hcm
      obtain ⟨pc, qk, hqk, hdec, hC, sa', hO, hR⟩ :=
        haxEntry_call_halts hnd hk hq0 hp hcf hl hlc h1 sa hsep v hrun
      exact ⟨_, hdec, .inr ⟨c, hcm, pc, qk, hqk, rfl, hC, sa', (hk l hl).haltsO_sig hlc hO, hR⟩⟩

/-- **The general compiler theorem with no witness, on a module.** Let the linked functions
    of `m` have distinct names (`hnd`) and each be a linked kernel (`hk`,
    `LinkedKernel`). For the result of `compileA` on `m`, the bytes decode to a program
    `prog`, and from every entry state `sa` satisfying `σ.Regions`, every value `v` of a
    source run of `m` from `sa` (`haxRuns σ m sa v`) is read back by `σ`, either from a
    state at which `prog` halts from `sa`, with the entry stack register, the entry bytes
    outside the stack words and the pointer regions of `σ`, and a halting run of the address
    machine from `entryA σ sa` whose stores and loads lie in `layoutMem σ sa`, or, for a
    program `pc ++ shiftProg pc.length q`
    calling the decoded code `q` of the data `c` of a linked function of `m`, from a state at
    which the program halts through the call and from a state at which `pc` halts with its
    call answered by the guarded oracle of `q` (`correct_of_compileARegion`).

    The proof is `correct_of_compileARegion` at the module and layout of the pair stage: the
    source run of `m` to `v` gives a source run of the module of the stage to a value `x`
    from whose read-back `σ` reads back `v` (`haxRuns_pairStage`); on a module with a pair
    tail `x` is the array and `v` the pair of the array and one of its words. The stack
    range, the pointer regions and the entry state of the address machine of the stage are
    those of `σ` (`pairStage_frame`, `entryA_pairStage`, `layoutMem_pairStage`). -/
theorem haxc_correct_auto (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
          ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false)
      ∨ ∃ c ∈ m.linked.filterMap LinkedFn.calleeData, ∃ pc q,
          decodeLprog c.bytes = some q ∧ prog = pc ++ shiftProg pc.length q
          ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
          ∧ ∃ sa', HaltsO aMachine (oracleAt pc.length (guarded c.sig (runOf ctRegime q)))
              pc 0 sa sa' ∧ σ.ResultOf sa sa' v) := by
  obtain ⟨x, hrun', hback⟩ := haxRuns_pairStage hrun
  have hl := pairStage_linked m σ
  obtain ⟨hlo, hhi, hrg⟩ := pairStage_frame m σ
  obtain ⟨prog, hd, h⟩ := correct_of_compileARegion _ _ fname P bytes hc sa
    ((pairStage_regions m σ sa).2 hsep) x hrun' (hl ▸ hnd) (hl ▸ hk)
  rw [hl] at h
  refine ⟨prog, hd, ?_⟩
  rcases h with ⟨sa', hh, hR, hsp, hkeep, hA⟩
    | ⟨c, hcm, pc, q, hq, hp, ⟨sa', hC, hR⟩, sa'', hO, hR'⟩
  · rw [hlo, hhi, hrg] at hkeep
    rw [entryA_pairStage, layoutMem_pairStage] at hA
    exact .inl ⟨sa', hh, hback _ hR, hsp, hkeep, hA⟩
  · exact .inr ⟨c, hcm, pc, q, hq, hp, ⟨sa', hC, hback _ hR⟩, sa'', hO, hback _ hR'⟩

end CatCrypt.Crypto.SecureCompilation.Haxc
