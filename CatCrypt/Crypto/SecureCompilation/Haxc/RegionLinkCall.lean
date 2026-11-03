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

The bytes of `compileA` on a program with `call`s halt through the calls of the code of the
linked functions of the module it calls, from every entry state with a source run: the
source run denotes the source value at the environment of these functions alone
(`RegionLinkCall.haxEntry_run_linkedEnv`, `RegionLinkCall.denoteAt_linkedEnvOn`), and the
calling body compiled at the table of these functions runs through its calls
(`RegionLinkCall.compileRegion_correct_linked_multi`). The compiler theorems of the region
line combine this case with the program without `call`.

## Main results

* `haxEntry_call_halts`, `eq_of_append_shiftProg`: the runs of the bytes of `compileA` on a
  program with a `call` of one linked function from every entry state with a source run, and
  the calling body of such a program determined by the program.
* `kernelKind`, `moduleKind`, `moduleBlock`, `LinkedKernel.kind_facts`: the kind of a linked
  kernel at its data and its facts, and the kinds and decoded blocks of the linked kernels of
  a module by symbol.
* `tabOracle`, `tabOracle_one`: the oracle of a table of linked functions, and at one
  function the oracle of its guarded block.
* `haxEntry_call_halts_multi`: the runs of the bytes of `compileA` on a program with calls of
  several linked kernels, through the region of their blocks.
* `correct_of_compileARegion`: the compiler theorem of the region line on a module whose
  linked functions are linked kernels with distinct names.
* `haxc_correct_auto`: the compiler theorem on a module whose linked functions are linked
  kernels with distinct names; on a module without linked functions its hypotheses
  hold vacuously and the bytes halt.
* `haxc_correct_auto_one`: `haxc_correct_auto` on a module with at most one linked function,
  whose second disjunct is the call of that function, answered by the oracle of its guarded
  block.
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
    · have hfl' : (l.name == f) = false := beq_eq_false_iff_ne.mpr fun h => hfl h.symm
      simp [summaryTableL, hfl'] at ht
  have hwo : ∀ f pr, f ≠ c.name → summaryTable l f = some pr → pr.WordOnly :=
    fun f pr hf ht => (hcl f pr hf ht).elim
  have hrw : ∀ f pr, f ≠ c.name → summaryTable l f = some pr → pr.RetWord :=
    fun f pr hf ht => (hcl f pr hf ht).elim
  have hTc : summaryTable l c.name = some (linkedSummary l) := by
    simp [summaryTableL, hname]
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


/-! ## A module whose program calls several linked kernels -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.SepLogic (SContract)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun oracleOf)

/-- **The kind of a linked kernel at its data**: the contract kind of its shape, `.ins` at a
    register result and `.outC` at an out result `.out n kd`, whose destination is the name of
    the parameter at the position `kd`. -/
def kernelKind (l : LinkedFn) (c : CalleeData) : CalleeKind :=
  match c.res with
  | .reg _ => .ins l c.ins c.resReg
  | .out n kd => .outC l c.ins (c.ins.getD kd ("", .scalar)).1 n

/-- **The kinds of the linked kernels of a module, by symbol**: the kind of the first linked
    function with the symbol at its data, and `d` at every other symbol. -/
def moduleKind (m : HaxModule) (d : CalleeKind) (f : String) : CalleeKind :=
  ((m.linked.find? (·.name == f)).bind fun l => l.calleeData.map (kernelKind l)).getD d

/-- **The decoded blocks of the linked kernels of a module, by symbol**: the program the code
    of the first linked function with the symbol decodes to, and the empty program
    elsewhere. -/
def moduleBlock (m : HaxModule) (f : String) : List RInstr :=
  ((m.linked.find? (·.name == f)).bind fun l => decodeLprog l.bytes).getD []

/-- **A linked kernel at its kind.** At the data `c` of a linked kernel `l`, the kind
    `kernelKind l c` meets its top hypotheses, a run relation that meets the contract of `l`
    meets its specification, its summary is `linkedSummary l`, and the precondition of its
    interface gives the precondition of the interface of `c` (`LinkedFnMeets.pre_of_callSite`). -/
theorem LinkedKernel.kind_facts {l : LinkedFn} (K : LinkedKernel l) {c : CalleeData}
    (hc : l.calleeData = some c) :
    (kernelKind l c).Top c ∧ (∀ X : CalleeRun, SContract X l.contract → (kernelKind l c).Spec X)
      ∧ (kernelKind l c).summary = linkedSummary l
      ∧ ∀ s, (kernelKind l c).sig.pre s → c.sig.pre s := by
  obtain ⟨-, -, hcargs, -, -, -, hcpre, -⟩ := CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hc
  have hn : l.params.length = c.args.length := by
    rw [hcargs, List.length_map]
    exact K.arity
  have hpre : ∀ s, (∃ a, (l.contractPre a).holds s) → c.sig.pre s := by
    rintro s ⟨a, ha⟩
    show c.pre s
    rw [hcpre]
    exact LinkedFnMeets.pre_of_callSite K.callSite ha
  rcases (K.code c hc).1 with ⟨hL, hres⟩ | ⟨po, n, hL, hres⟩
  · obtain ⟨⟨r0, hr0⟩, -, -, -, -⟩ := regCallee_facts hc hL.result
    have hkk : kernelKind l c = .ins l c.ins c.resReg := by simp [kernelKind, hr0]
    have hkinds : linkedKinds l = c.ins.map (·.2) := by
      rw [K.kinds c hc]
      have h2 := congrArg (List.map Prod.snd) hL.args
      simpa [List.map_map, Function.comp_def] using h2
    rw [hkk]
    exact ⟨⟨hc, hL, rfl, rfl, hn, K.args_nodup, K.frame_fit⟩, fun _ h => h,
      (RegionLinkArr.linkedSummary_eq_insSummary hkinds hres).symm, hpre⟩
  · obtain ⟨kd, hcr, hdk, -, -, -, -⟩ := outCallee_facts hc hL rfl
    have hkk : kernelKind l c = .outC l c.ins po n := by
      simp [kernelKind, hcr, List.getD_eq_getElem?_getD, hdk]
    have hkinds : linkedKinds l = c.ins.map (·.2) := by
      rw [K.kinds c hc]
      have h2 := congrArg (List.map Prod.snd) hL.args
      simpa [List.map_map, Function.comp_def] using h2
    rw [hkk]
    exact ⟨⟨hc, hL, rfl, hn, K.args_nodup, K.frame_fit⟩, fun _ h => h,
      (linkedSummary_eq_outSummary hkinds hres).symm, hpre⟩

/-- **The oracle of a table of linked functions** behind a caller of `n` instructions: a call
    to the index `n + k f` of the entry of the block of a symbol `f` of `cs` is answered by the
    leaky runs under `ctRegime` of the block `q f`, guarded by the precondition of the interface
    of the function of `f` (`Callee.oracleOf`). -/
def tabOracle (cs : List CalleeData) (n : Nat) (k : String → Nat) (q : String → List RInstr) :
    Nat → AState → AState → Prop :=
  oracleOf (cs.map (·.name)) (fun f => n + k f)
    (fun f => guarded (CalleeTab.sigOf ⟨cs⟩ f) (runOf ctRegime (q f)))

/-- **The oracle of the table of one linked function** is the oracle of its guarded block at
    the index behind the caller. -/
theorem tabOracle_one (c : CalleeData) (n : Nat) (q : List RInstr) :
    tabOracle [c] n (fun _ => 0) (fun _ => q) = oracleAt n (guarded c.sig (runOf ctRegime q)) := by
  have hsig : CalleeTab.sigOf ⟨[c]⟩ c.name = c.sig := by
    simp [CalleeTab.sigOf, CalleeTab.lookup]
  funext t s s'
  apply propext
  simp only [tabOracle, oracleOf, oracleAt, List.map_cons, List.map_nil, List.mem_singleton,
    Nat.add_zero]
  constructor
  · rintro ⟨f, rfl, ht, tr, hx⟩
    exact ⟨ht.symm, tr, hsig ▸ hx⟩
  · rintro ⟨rfl, tr, hx⟩
    exact ⟨c.name, rfl, rfl, tr, hsig.symm ▸ hx⟩

/-- **The runs of the bytes of `compileA` on a program with calls of several linked kernels.**
    Let the linked functions of `m` have distinct names and each be a linked kernel, let the code
    of each but the last be an item stream (`LprogBytesLinkReloc.KernelItems`), let the
    translation of the hax entry return `q0` on `m`, the chain with the declared procedures of
    `m` return a program `p` with a `call`, and `compileRegion` at the data of the linked
    functions of `m` return `(P, bytes)` on `p`. There is a nonempty sublist `cs` of these data
    with distinct names, the table the back half finds, whose code decodes to the region `Q` of
    the blocks `q f` at the entry indices `k f`, such that from every entry state `sa` satisfying
    `σ.Regions` with a source run of `m` to `v` the bytes decode to `pc` followed by `Q` with its
    targets raised by `pc.length`, the program halts through the calls (`HaltsC`) in a state
    from which `σ` reads back `v`, and `pc` halts with its calls answered by the oracle
    `tabOracle cs pc.length k q` in such a state. The source run denotes the source value at the
    environment of the functions of `cs` alone (`denoteAt_linkedEnvOn`), whose table of
    summaries agrees with it (`procsAgree_summaryTableL`), and the runs are
    `compileRegion_correct_linked_multi` at the kinds `kernelKind` of the linked kernels. At
    one linked function this is `haxEntry_call_halts`. -/
theorem haxEntry_call_halts_multi {m : HaxModule} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hnd : (m.linked.map (·.name)).Nodup)
    (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hit : ∀ l ∈ m.linked.dropLast, X86Backend.LprogBytesLinkReloc.KernelItems l.bytes)
    {q0 : Σ t : NFDialect.NfTy,
      NFProg NFDialect.nfDialect (CatCrypt.Crypto.Hax.ImpToNF.entryCtx (NFToRoute.abiEntry σ))
        [t]}
    (hq0 : haxEntry.toNF σ m = some q0)
    {p : NFProg jasminDialect (nfCtx σ)
      [CryptoToJasminCom.mapTy (CatCrypt.Crypto.Hax.NFToCat.catTy q0.1)]}
    (hp : (extChain (haxEntry.decls m) _ q0.1).run q0.2 = some p) (hcf : p.callFree = false)
    (h1 : compileRegion σ (haxEntry.names fname σ) p (m.linked.filterMap LinkedFn.calleeData)
      = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v) :
    ∃ cs : List CalleeData, cs.Sublist (m.linked.filterMap LinkedFn.calleeData) ∧ cs ≠ []
      ∧ (cs.map (·.name)).Nodup
      ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
        (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
        ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
        ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
        ∧ decodeLprog bytes = some (pc ++ shiftProg pc.length Q)
        ∧ (∃ sa', HaltsC aMachine (pc ++ shiftProg pc.length Q) 0 sa sa' ∧ σ.ResultOf sa sa' v)
        ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
          ∧ σ.ResultOf sa sa' v := by
  obtain ⟨T, hsub, hne, hndT, hcalls, hnoc, hrest⟩ := compileRegion_correct_linked_multi h1 hcf
  -- The linked function of each function of the table, the first with its name.
  have hlc : ∀ c ∈ T.fns, ∃ l ∈ m.linked, l.calleeData = some c ∧
      m.linked.find? (·.name == c.name) = some l := by
    intro c hc
    obtain ⟨l, hl, hlc⟩ := List.mem_filterMap.mp (hsub.subset hc)
    refine ⟨l, hl, hlc, ?_⟩
    rw [(CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1]
    exact find?_name_of_nodup hnd hl
  obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨l0, -, -, -⟩ := hlc c0 hc0
  have hkind : ∀ c ∈ T.fns, ∃ l ∈ m.linked, l.calleeData = some c
      ∧ moduleKind m (.ins l0 [] "") c.name = kernelKind l c
      ∧ moduleBlock m c.name = (decodeLprog c.bytes).getD [] := by
    intro c hc
    obtain ⟨l, hl, hlc, hf⟩ := hlc c hc
    refine ⟨l, hl, hlc, by simp [moduleKind, hf, hlc], ?_⟩
    rw [(CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.2.2.2.2.1]
    simp [moduleBlock, hf]
  have hdecq : ∀ c ∈ T.fns, decodeLprog c.bytes = some (moduleBlock m c.name) := by
    intro c hc
    obtain ⟨l, hl, hlc, -, hb⟩ := hkind c hc
    obtain ⟨q, hq, -⟩ := (hk l hl).contract_code hlc
    rw [hb, hq]
    rfl
  -- The source run at the functions of the table alone.
  obtain ⟨k, V, x, hV, hvx, hx⟩ := haxEntry_run_linkedEnv hq0 hp hsep hrun
  let ls := m.linked.filter fun l => T.names.contains l.name
  have hmemls : ∀ g, g ∈ ls.map (·.name) ↔ g ∈ T.names := by
    intro g
    constructor
    · intro hg
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
      simpa [CalleeTab.names] using (List.mem_filter.mp hl).2
    · intro hg
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
      obtain ⟨l, hl, hlc, -⟩ := hlc c hc
      have hn := (CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1
      refine List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨hl, ?_⟩, hn.symm⟩
      simpa [← hn, CalleeTab.names] using List.mem_map_of_mem (f := (·.name)) hc
  have henv : linkedEnvOn m (ls.map (·.name)) = linkedEnvOn m T.names := by
    unfold linkedEnvOn
    congr 1
    funext g vals
    by_cases hg : g ∈ T.names
    · simp [hg, (hmemls g).mpr hg]
    · have hg' : g ∉ ls.map (·.name) := fun h => hg ((hmemls g).mp h)
      simp [hg, hg']
  have hT : ProcsAgree (linkedEnvOn m T.names) (summaryTableL ls) := by
    rw [← henv]
    exact procsAgree_summaryTableL hnd (fun l hl => (List.mem_filter.mp hl).1)
      (fun l hl => (hk l (List.mem_filter.mp hl).1).sem_kinds)
      (fun l hl => (hk l (List.mem_filter.mp hl).1).res_slice)
  have hx' : p.denoteAt (linkedEnvOn m T.names) k V = some (HVector.cons x .nil) := by
    rw [denoteAt_linkedEnvOn hcalls]
    exact hx
  -- The summaries of the table of the functions of `T`.
  have hwo : ∀ f pr, f ∉ T.names → summaryTableL ls f = some pr → pr.WordOnly ∧ pr.RetWord := by
    intro f pr hf ht
    obtain ⟨l, hl, -⟩ := Option.map_eq_some_iff.mp ht
    have hlf : l.name = f := by simpa using List.find?_some hl
    exact absurd ((hmemls f).mp (List.mem_map.mpr ⟨l, List.mem_of_find?_eq_some hl, hlf⟩)) hf
  have hTc : ∀ c ∈ T.fns, summaryTableL ls c.name
      = some (moduleKind m (.ins l0 [] "") c.name).summary := by
    intro c hc
    obtain ⟨l, hl, hlc, hkk, -⟩ := hkind c hc
    obtain ⟨-, -, hsum, -⟩ := (hk l hl).kind_facts hlc
    have hn := (CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1
    have hfind : ls.find? (·.name == c.name) = some l := by
      cases hf : ls.find? (·.name == c.name) with
      | none =>
          refine absurd (List.find?_eq_none.mp hf l (List.mem_filter.mpr ⟨hl, ?_⟩)) (by simp [hn])
          simpa [← hn, CalleeTab.names] using List.mem_map_of_mem (f := (·.name)) hc
      | some l' =>
          have h1 := (List.mem_filter.mp (List.mem_of_find?_eq_some hf)).1
          have h2 : l'.name = l.name := by rw [← hn]; simpa using List.find?_some hf
          rw [List.inj_on_of_nodup_map hnd h1 hl h2]
    rw [hkk, hsum]
    simp [summaryTableL, hfind]
  -- The kinds and the specifications of the functions of the table.
  have hK : ∀ c ∈ T.fns, (moduleKind m (.ins l0 [] "") c.name).Top c
      ∧ (moduleKind m (.ins l0 [] "") c.name).Spec
        (runOf ctRegime (moduleBlock m c.name)) := by
    intro c hc
    obtain ⟨l, hl, hlc, hkk, -⟩ := hkind c hc
    obtain ⟨htop, hspec, -, -⟩ := (hk l hl).kind_facts hlc
    obtain ⟨q, hq, hm⟩ := (hk l hl).contract_code hlc
    rw [hkk]
    refine ⟨htop, hspec _ ?_⟩
    have := hdecq c hc
    rw [hq] at this
    rw [← Option.some.inj this]
    exact hm
  obtain ⟨pc, ⟨b, hbs, -, -⟩, ⟨sO, hO, hRO⟩, hC⟩ :=
    hrest (moduleKind m (.ins l0 [] "")) (fun f => runOf ctRegime (moduleBlock m f)) hK hT hwo hTc
      sa V hV hsep k hx'
  -- The region of the blocks of the table.
  have hit' : ∀ c ∈ T.fns.dropLast, X86Backend.LprogBytesLinkReloc.KernelItems c.bytes := by
    intro c hc
    have hsubD : T.fns.dropLast.Sublist (m.linked.filterMap LinkedFn.calleeData).dropLast := by
      have key : ∀ {l₁ l₂ : List CalleeData}, l₁.Sublist l₂ → l₁.dropLast.Sublist l₂.dropLast := by
        intro l₁ l₂ h
        induction h with
        | slnil => exact List.Sublist.slnil
        | cons a h ih =>
            rename_i l₁' l₂'
            cases l₂' with
            | nil => simp_all
            | cons b l₂'' =>
                rw [List.dropLast_cons_cons]
                exact ih.cons a
        | cons_cons a h ih =>
            rename_i l₁' l₂'
            cases l₁' with
            | nil => simp
            | cons b l₁'' =>
                cases l₂' with
                | nil => simp at h
                | cons e l₂'' =>
                    rw [List.dropLast_cons_cons, List.dropLast_cons_cons]
                    exact ih.cons_cons a
      exact key hsub
    have hfd : ∀ {L : List LinkedFn} {d : CalleeData},
        d ∈ (L.filterMap LinkedFn.calleeData).dropLast →
          ∃ l ∈ L.dropLast, l.calleeData = some d := by
      intro L d h
      rcases List.eq_nil_or_concat L with rfl | ⟨L', a, rfl⟩
      · simp at h
      · rw [List.concat_eq_append, List.filterMap_append] at h
        rw [List.concat_eq_append, List.dropLast_concat]
        apply List.mem_filterMap.mp
        cases hfa : a.calleeData with
        | none =>
            simp only [List.filterMap_cons_none hfa, List.filterMap_nil, List.append_nil] at h
            exact List.dropLast_subset _ h
        | some y =>
            simpa [List.filterMap_cons_some hfa] using h
    obtain ⟨l, hl, hlc⟩ := hfd (hsubD.subset hc)
    rw [(CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.2.2.2.2.1]
    exact hit l hl
  have hneB := (calleeBytes_tab hbs).2.1
  have hR := T.regionBlocks hne (fun c => moduleBlock m c.name) hdecq hneB
    (fun c hc => hnoc c hc _ (hdecq c hc)) hit' T.names (fun _ h => h)
  obtain ⟨hdecB, sC, hhC, hRC⟩ := hC (fun c => moduleBlock m c.name) hdecq
    (fun c hc => hnoc c hc _ (hdecq c hc)) hit' (fun _ _ => rfl)
  obtain ⟨xs₂, hd, hr, -⟩ := hR.decode
  refine ⟨T.fns, hsub, hne, hndT, pc,
    X86Backend.LprogBytesLinkReloc.regionProg (T.regionEntries fun c => moduleBlock m c.name),
    fun f => T.entryIdx (T.symPos f), moduleBlock m, hdecq,
    by show decodeLprog T.bytes = _; simp [decodeLprog, hd, hr], fun c hc => ?_, hdecB,
    ⟨sC, hhC, by rw [hvx]; exact hRC⟩, sO, hO.mono fun t s s' ho => ?_, by rw [hvx]; exact hRO⟩
  · obtain ⟨c', hc'⟩ : ∃ c', T.lookup c.name = some c' := by
      have h1 := congrFun T.lookup_isSome c.name
      exact Option.isSome_iff_exists.mp
        (by rw [h1]; simpa [CalleeTab.names] using List.mem_map_of_mem (f := (·.name)) hc)
    obtain ⟨A, B, hQ, hA⟩ := hR.block c.name (List.mem_map_of_mem hc)
    rw [CalleeTab.regionCode_lookup T _ hc', (CalleeTab.lookup_spec hc').2] at hQ
    exact ⟨A, B, hQ, hA⟩
  · obtain ⟨f, hf, ht, tr, hgx⟩ := ho
    refine ⟨f, hf, ht, tr, ?_, hgx.2⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf
    obtain ⟨l, hl, hlc, hkk, -⟩ := hkind c hc
    obtain ⟨-, -, -, hpre⟩ := (hk l hl).kind_facts hlc
    have hsig : CalleeTab.sigOf ⟨T.fns⟩ c.name = c.sig := by
      obtain ⟨c', hc'⟩ : ∃ c', T.lookup c.name = some c' := by
        have h1 := congrFun T.lookup_isSome c.name
        exact Option.isSome_iff_exists.mp
          (by rw [h1]; simpa [CalleeTab.names] using List.mem_map_of_mem (f := (·.name)) hc)
      obtain ⟨hcm', hn'⟩ := CalleeTab.lookup_spec hc'
      have hcc : c' = c := List.inj_on_of_nodup_map hndT hcm' hc hn'
      subst hcc
      simp [CalleeTab.sigOf, show CalleeTab.lookup ⟨T.fns⟩ c'.name = some c' from hc']
    rw [hsig]
    exact hpre s (hkk ▸ hgx.1)

end Linked

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
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

/-- **The compiler theorem of the region line, on a module.** Let the linked functions of `m`
    have distinct names (`hnd`), each be a linked kernel (`hk`, `LinkedKernel`), and each but
    the last have code that is an item stream (`hit`, `LprogBytesLinkReloc.KernelItems`). For
    the result of `compileARegion` on `m`, the bytes decode to a program `prog`, and from every
    entry state `sa` satisfying `σ.Regions`, every value `v` of a source run of `m` from `sa`
    (`haxRuns σ m sa v`: a run of the source reading of the entry, from a hax environment `σ`
    reads off `sa`, at the table of the module, to a value that is not a control-flow value) is
    read back by `σ`:

    * either from a state `sa'` at which `prog` halts from `sa`, whose stack register holds
      its value in `sa`, and whose memory agrees with that of `sa` at every byte outside the
      stack words `%rsp + o`, `frameLo ≤ o ≤ frameHi`, and outside the words of each pointer
      region of `σ`, at the registers of `sa`; some run of the address machine on a body
      from `entryA σ sa` then halts and stores to and loads from `layoutMem σ sa` only,
    * or, for a nonempty sublist `cs` with distinct names of the data of the linked functions
      of `m` (the table of the functions the program calls), the program is
      `pc ++ shiftProg pc.length Q` for the region `Q` of the code of `cs`, which decodes to
      the blocks `q f` of the functions, the block of each symbol `f` at the index `k f` of
      `Q`; the program halts through the calls (`HaltsC`) from `sa` in a state from which
      `σ` reads back `v`, and `pc` halts from `sa` with its calls answered by the oracle
      `tabOracle cs pc.length k q` of the leaky runs of the blocks guarded by the
      preconditions of the interfaces of their functions, in such a state. At one function
      `c` the oracle is `oracleAt pc.length (guarded c.sig (runOf ctRegime q))`
      (`tabOracle_one`), the premise of `compileRegion_call_bytes_ct`.

    A call of a function of the module in the source run is the run of the source reading
    of the extraction of the callee under the table of the module. On a module without
    linked functions, such as a single function (`te : HaxModule`), `hnd`, `hk` and `hit`
    hold vacuously (the default arguments close them when `m.linked` reduces to `[]`, and
    `hit` also at one linked function) and only the first case occurs, since
    `m.linked.filterMap LinkedFn.calleeData` is empty; on a single function the source run is
    a run of the source reading of `te` at `hax64WExit` (`haxRuns_single`). A program without
    `call` is the case of `NFEntry.compileR_correct`; a program with a `call` is that of
    `haxEntry_call_halts_multi`. -/
theorem correct_of_compileARegion (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileARegion m σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h)
    (hit : ∀ l ∈ m.linked.dropLast, X86Backend.LprogBytesLinkReloc.KernelItems l.bytes := by
      exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
          ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false)
      ∨ ∃ cs : List CalleeData, cs.Sublist (m.linked.filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) := by
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
      obtain ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hdec, hC, hO⟩ :=
        haxEntry_call_halts_multi hnd hk hit hq0 hp hcf hc sa hsep v hrun
      exact ⟨_, hdec, .inr ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, rfl, hC, hO⟩⟩

/-- **The general compiler theorem with no witness, on a module.** Let the linked functions of
    `m` have distinct names (`hnd`), each be a linked kernel (`hk`, `LinkedKernel`), and each
    but the last have code that is an item stream (`hit`). For the result of `compileA` on `m`,
    the bytes decode to a program `prog`, and from every entry state `sa` satisfying
    `σ.Regions`, every value `v` of a source run of `m` from `sa` (`haxRuns σ m sa v`) is read
    back by `σ`, either from a state at which `prog` halts from `sa`, with the entry stack
    register, the entry bytes outside the stack words and the pointer regions of `σ`, and a
    halting run of the address machine from `entryA σ sa` whose stores and loads lie in
    `layoutMem σ sa`, or, for a program `pc ++ shiftProg pc.length Q` calling the region `Q` of
    the decoded blocks of the data `cs` of linked functions of `m`, from a state at which the
    program halts through the calls and from a state at which `pc` halts with its calls answered
    by the oracle `tabOracle` of the guarded blocks (`correct_of_compileARegion`).

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
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h)
    (hit : ∀ l ∈ m.linked.dropLast, X86Backend.LprogBytesLinkReloc.KernelItems l.bytes := by
      exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
          ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false)
      ∨ ∃ cs : List CalleeData, cs.Sublist (m.linked.filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) := by
  obtain ⟨x, hrun', hback⟩ := haxRuns_pairStage hrun
  have hl := pairStage_linked m σ
  obtain ⟨hlo, hhi, hrg⟩ := pairStage_frame m σ
  obtain ⟨prog, hd, h⟩ := correct_of_compileARegion _ _ fname P bytes hc sa
    ((pairStage_regions m σ sa).2 hsep) x hrun' (hl ▸ hnd) (hl ▸ hk) (hl ▸ hit)
  rw [hl] at h
  refine ⟨prog, hd, ?_⟩
  rcases h with ⟨sa', hh, hR, hsp, hkeep, hA⟩
    | ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hp, ⟨sa', hC, hR⟩, sa'', hO, hR'⟩
  · rw [hlo, hhi, hrg] at hkeep
    rw [entryA_pairStage, layoutMem_pairStage] at hA
    exact .inl ⟨sa', hh, hback _ hR, hsp, hkeep, hA⟩
  · exact .inr ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hp, ⟨sa', hC, hback _ hR⟩, sa'',
      hO, hback _ hR'⟩

/-- **The general compiler theorem at one linked function.** On a module `m` with at most one
    linked function, a linked kernel (`hk`), the conclusion of `haxc_correct_auto` holds with
    its second disjunct at the data `c` of that function: the bytes decode to a program
    `pc ++ shiftProg pc.length q` for the decoded code `q` of `c`, which halts through the call
    in a state from which `σ` reads back `v`, and `pc` halts with its call answered by the
    oracle of the block `q` guarded by the precondition of `c`. It is `haxc_correct_auto`,
    whose table is then `[c]` and whose oracle is that of `tabOracle_one`. -/
theorem haxc_correct_auto_one (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v)
    (h1 : m.linked.length ≤ 1)
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
  have hnd : (m.linked.map (·.name)).Nodup := by
    match m.linked, h1 with
    | [], _ => exact List.nodup_nil
    | [_], _ => exact List.nodup_singleton _
  have hit : ∀ l ∈ m.linked.dropLast, X86Backend.LprogBytesLinkReloc.KernelItems l.bytes := by
    intro l hl
    have := List.length_pos_of_mem hl
    simp only [List.length_dropLast] at this
    omega
  obtain ⟨prog, hd, h⟩ := haxc_correct_auto m σ fname P bytes hc sa hsep v hrun hnd hk hit
  refine ⟨prog, hd, ?_⟩
  rcases h with h | ⟨cs, hsub, hne, -, pc, Q, k, q, hq, hQ, hB, hp, hC, sa', hO, hR⟩
  · exact .inl h
  obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := by
    have hlen : cs.length ≤ 1 := hsub.length_le.trans ((List.length_filterMap_le _ _).trans h1)
    match cs, hne, hlen with
    | [c], _, _ => exact ⟨c, rfl⟩
  have hQq : Q = q c.name := by
    have h2 := hq c List.mem_cons_self
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hQ
    rw [hQ] at h2
    exact Option.some.inj h2
  obtain ⟨A, B, hAB, hA⟩ := hB c List.mem_cons_self
  have hk0 : k c.name = 0 := by
    have := congrArg List.length hAB
    simp only [List.length_append, X86Backend.LprogBytesLink.shiftProg_length, hQq] at this
    omega
  have hO' : tabOracle [c] pc.length k q
      = tabOracle [c] pc.length (fun _ => 0) (fun _ => q c.name) := by
    funext t s s'
    simp only [tabOracle, X86Backend.Callee.oracleOf, List.map_cons, List.map_nil,
      List.mem_singleton, exists_eq_left, hk0]
  rw [hO', tabOracle_one] at hO
  exact .inr ⟨c, hsub.subset List.mem_cons_self, pc, q c.name, hq c List.mem_cons_self,
    by rw [hp, hQq], hC, sa', hO, hR⟩

end CatCrypt.Crypto.SecureCompilation.Haxc
