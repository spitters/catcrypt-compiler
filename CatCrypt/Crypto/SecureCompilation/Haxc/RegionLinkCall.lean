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
# The compiler at an entry with linked kernels

The bytes of `NFEntry.compileR` at the data of the linked functions of a source program, on a
program with `call`s, halt through the calls of the code of the linked functions it calls,
from every entry state with a source run: the source run denotes the source value at the
environment of these functions alone (`NFEntry.run_linkedEnv`,
`RegionLinkCall.denoteAt_linkedEnvOn`), and the calling body compiled at the table of these
functions runs through its calls (`RegionLinkCall.regionBack_correct_linked_multi`). The
compiler theorem at an entry combines this case with the program without `call`; the hax
compiler `compileA` is its instance at `haxEntry`.

## Main results

* `NFEntry.call_halts`, `eq_of_append_shiftProg`: the runs of the bytes of the compiler at an
  entry on a program with a `call` of one linked function from every entry state with a
  source run, and the calling body of such a program determined by the program.
* `kernelKind`, `moduleKind`, `moduleBlock`, `LinkedKernel.kind_facts`: the kind of a linked
  kernel at its data and its facts, and the kinds and decoded blocks of a list of linked
  kernels by symbol.
* `tabOracle`, `tabOracle_one`: the oracle of a table of linked functions, and at one
  function the oracle of its guarded block.
* `NFEntry.call_halts_tab`, `NFEntry.call_halts_multi`: the runs of the bytes of the compiler
  at an entry on a program with calls of several linked kernels, through the region of their
  blocks.
* `NFEntry.compileR_correct_linked`: the compiler theorem at an entry whose source program
  has linked functions that are linked kernels with distinct names.
* `haxc_correct_auto`: the compiler theorem on a module whose linked functions are linked
  kernels with distinct names, `NFEntry.compileR_correct_linked` at `haxEntry` and the pair
  stage; on a module without linked functions its hypotheses hold vacuously and the bytes
  halt.
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

/-- **The runs of a calling body at an entry.** Let the linked functions of the source program `s`
    of the entry `E` have distinct names and each be a linked kernel. Let the translation of `E`
    return `q0` on `s`, the chain with the declared procedures of `s` return a program `p` with a
    `call`, and `compileRegion` at the data `c` of the linked function `l` of `s` alone return `(P,
    bytes)` on `p`. Then the code of `c` decodes to `qk`, the bytes decode to `pc ++ shiftProg
    pc.length qk`, and from every entry state `sa` satisfying `σ.Regions` with a source run of `s`
    to `v`, the program halts through the call (`HaltsC`) in a state from which `σ` reads back `v`,
    and the calling body `pc` halts with its call answered by the oracle of the leaky runs of `qk`
    guarded by the precondition of the interface of the contract `l.contractSig c.args c.res.reg?`
    in such a state. The source run denotes the source value in `linkedEnv (E.linked s)`
    (`NFEntry.run_linkedEnv`), hence in the environment `linkedEnvAt (E.linked s) l.name` of `l`
    alone, since every call of `p` names `l` (`callsTo_of_regionBack`, `denoteAt_linkedEnvAt`);
    the table `summaryTable l` agrees with it (`procsAgree_summaryTable`), and the runs are
    `regionBack_correct_contract_ins` or `regionBack_correct_contract_out` at the shape of the
    code of `l`. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.NFEntry.call_halts (E : NFEntry)
    {s : E.Src} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hnd : ((E.linked s).map (·.name)).Nodup)
    (hk : ∀ l ∈ E.linked s, LinkedKernel l)
    {q0 : Σ t : NFDialect.NfTy,
      NFProg NFDialect.nfDialect (CatCrypt.Crypto.Hax.ImpToNF.entryCtx (NFToRoute.abiEntry σ))
        [t]}
    (hq0 : E.toNF σ s = some q0)
    {p : NFProg jasminDialect (nfCtx σ)
      [CryptoToJasminCom.mapTy (CatCrypt.Crypto.Hax.NFToCat.catTy q0.1)]}
    (hp : (extChain (E.decls s) _ q0.1).run q0.2 = some p) (hcf : p.callFree = false)
    {l : LinkedFn} (hl : l ∈ E.linked s) {c : CalleeData} (hlc : l.calleeData = some c)
    (h1 : compileRegion σ (E.names fname σ) p [c] = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : E.Runs σ s sa v) :
    ∃ pc qk, decodeLprog c.bytes = some qk
      ∧ decodeLprog bytes = some (pc ++ shiftProg pc.length qk)
      ∧ (∃ sa', HaltsC aMachine (pc ++ shiftProg pc.length qk) 0 sa sa' ∧ σ.ResultOf sa sa' v)
      ∧ ∃ sa', HaltsO aMachine
          (oracleAt pc.length (guarded (l.contractSig c.args c.res.reg?) (runOf ctRegime qk)))
          pc 0 sa sa' ∧ σ.ResultOf sa sa' v := by
  obtain ⟨-, w, -, h1, hcfw, hden⟩ := compileRegion_ctx (nfCtx_wide σ) h1
  have hcf' := hcfw.trans hcf
  have K := hk l hl
  obtain ⟨qk, hqk, hm⟩ := K.contract_code hlc
  obtain ⟨hcres, hname, hcargs, -, -, -, -, -, -, -, -⟩ :=
    CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc
  -- The code of the callee has no `call`.
  obtain ⟨-, -, -, r, b, cert, -, -, -, hg, -⟩ := regionBack_spec_linked h1 hcf'
  have hnc := (regionCoB_callee hg).2 c (by simp [CalleeTab.one]) qk hqk
  -- The source run at the linked function `l` alone.
  obtain ⟨k, V, x, hV, hvx, hx⟩ := E.run_linkedEnv hq0 hp hsep hrun
  have hx' : (VIR.NarrowWords.castProg (nfCtx_wide σ) rfl w).denoteAt
      (linkedEnvAt (E.linked s) l.name) k V =
        some (HVector.cons (VIR.NarrowWords.transTy x) .nil) := by
    rw [denoteAt_linkedEnvAt (hname ▸ callsTo_of_regionBack h1 hcf'), hden, hx]
    rfl
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
      RegionLinkArr.regionBack_correct_contract_ins hlc hL hkinds hres hn K.args_nodup
        K.frame_fit hqk hnc hm h1 hcf' hT hwo hrw hTc sa V hV hsep k hx'
    rw [hcsig]
    refine ⟨pc, qk, hqk, hdec, ⟨sa1, hC, ?_⟩, sa2, hO, ?_⟩
    · rw [hvx, ← denVal_wideTy_transTy (narrowArrB_mapTy_catTy _)]
      exact hR1
    · rw [hvx, ← denVal_wideTy_transTy (narrowArrB_mapTy_catTy _)]
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
      RegionLinkArr.regionBack_correct_contract_out hlc hL rfl hn K.args_nodup
        K.frame_fit hqk hnc hm h1 hcf' hT hwo hrw hTc sa V hV hsep k hx'
    rw [hcsig]
    refine ⟨pc, qk, hqk, hdec, ⟨sa1, hC, ?_⟩, sa2, hO, ?_⟩
    · rw [hvx, ← denVal_wideTy_transTy (narrowArrB_mapTy_catTy _)]
      exact hR1
    · rw [hvx, ← denVal_wideTy_transTy (narrowArrB_mapTy_catTy _)]
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

/-- **The kinds of linked kernels, by symbol**: the kind of the first linked function of `ls`
    with the symbol at its data, and `d` at every other symbol. -/
def moduleKind (ls : List LinkedFn) (d : CalleeKind) (f : String) : CalleeKind :=
  ((ls.find? (·.name == f)).bind fun l => l.calleeData.map (kernelKind l)).getD d

/-- **The decoded blocks of linked kernels, by symbol**: the program the code of the first
    linked function of `ls` with the symbol decodes to, and the empty program elsewhere. -/
def moduleBlock (ls : List LinkedFn) (f : String) : List RInstr :=
  ((ls.find? (·.name == f)).bind fun l => decodeLprog l.bytes).getD []

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

/-- **The runs of the bytes of a calling body at its table, at an entry.** Let the linked functions
    of the source program `s` of the entry `E` have distinct names and each be a linked kernel, let
    the translation of `E` return `q0` on `s`, the chain with the declared procedures of `s` return
    a program `p` with a `call`, and `compileRegion` at the data of the linked functions of `s`
    return `(P, bytes)` on `p`. The table `T` that `regionCallee` finds at the export `r0` of the
    legalised program is a nonempty sublist of these data with distinct names, whose code is
    nonempty and decodes, at each function `c`, to the block `moduleBlock (E.linked s) c.name`
    without `call`. At the interfaces `sg` of the kinds `kernelKind` of the linked kernels, from
    every entry state `sa` satisfying `σ.Regions` with a source run of `s` to `v`, the bytes decode
    to a caller `pc` followed by the region of the blocks of `T` with its targets raised by
    `pc.length`, the program halts through the calls (`HaltsC`) in a state from which `σ` reads back
    `v`, and `pc` halts in such a state with its calls answered by the oracle of the blocks guarded
    by the preconditions of `sg`, at the entries of the functions of `T`. The source run denotes the
    source value at the environment of the functions of `T` alone (`denoteAt_linkedEnvOn`), whose
    table of summaries agrees with it (`procsAgree_summaryTableL`), and the runs are
    `regionBack_correct_linked_multi` at the kinds `kernelKind` of the linked kernels. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.NFEntry.call_halts_tab (E : NFEntry)
    {s : E.Src} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hnd : ((E.linked s).map (·.name)).Nodup)
    (hk : ∀ l ∈ E.linked s, LinkedKernel l)
    {q0 : Σ t : NFDialect.NfTy,
      NFProg NFDialect.nfDialect (CatCrypt.Crypto.Hax.ImpToNF.entryCtx (NFToRoute.abiEntry σ))
        [t]}
    (hq0 : E.toNF σ s = some q0)
    {p : NFProg jasminDialect (nfCtx σ)
      [CryptoToJasminCom.mapTy (CatCrypt.Crypto.Hax.NFToCat.catTy q0.1)]}
    (hp : (extChain (E.decls s) _ q0.1).run q0.2 = some p) (hcf : p.callFree = false)
    (h1 : compileRegion σ (E.names fname σ) p ((E.linked s).filterMap LinkedFn.calleeData)
      = some (P, bytes)) :
    ∃ T : CalleeTab, (∃ w r0, VIR.NarrowWords.narrowPrep p = some w
        ∧ exportR (nfCtx σ).length (E.names fname σ).fname
          (legalizeRegion (VIR.NarrowWords.castProg (nfCtx_wide σ) rfl w)) (nfCtx σ).length 0
          = some r0
        ∧ regionCallee ((E.linked s).filterMap LinkedFn.calleeData)
          (legalizeRegion (VIR.NarrowWords.castProg (nfCtx_wide σ) rfl w)) r0.code
          = some (some T))
      ∧ T.fns.Sublist ((E.linked s).filterMap LinkedFn.calleeData) ∧ T.fns ≠ [] ∧ T.names.Nodup
      ∧ (∀ c ∈ T.fns, c.bytes ≠ [])
      ∧ (∀ c ∈ T.fns, decodeLprog c.bytes = some (moduleBlock (E.linked s) c.name))
      ∧ (∀ c ∈ T.fns, ∀ tg, RInstr.call tg ∉ moduleBlock (E.linked s) c.name)
      ∧ ∃ sg : String → X86Backend.Callee.CalleeSig,
        (∀ c ∈ T.fns, ∃ l ∈ E.linked s, l.calleeData = some c
          ∧ sg c.name = (kernelKind l c).sig)
        ∧ ∀ (sa : AState), σ.Regions sa → ∀ (v : _root_.Hax.Value), E.Runs σ s sa v →
          ∃ pc : List RInstr,
            decodeLprog bytes = some (pc ++ shiftProg pc.length
              (X86Backend.LprogBytesLinkReloc.regionProg
                (T.regionEntries fun c => moduleBlock (E.linked s) c.name)))
            ∧ (∃ sa', HaltsC aMachine (pc ++ shiftProg pc.length
                (X86Backend.LprogBytesLinkReloc.regionProg
                  (T.regionEntries fun c => moduleBlock (E.linked s) c.name))) 0 sa sa'
              ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (oracleOf T.names
                (fun f => pc.length + T.entryIdx (T.symPos f))
                (fun f => guarded (sg f) (runOf ctRegime (moduleBlock (E.linked s) f)))) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v := by
  obtain ⟨-, w, hw, h1, hcfw, hden⟩ := compileRegion_ctx (nfCtx_wide σ) h1
  have hcf' := hcfw.trans hcf
  obtain ⟨T, hpin, hsub, hne, hndT, hcalls, hnoc, hrest⟩ :=
    regionBack_correct_linked_multi h1 hcf'
  -- The linked function of each function of the table, the first with its name.
  have hlc : ∀ c ∈ T.fns, ∃ l ∈ E.linked s, l.calleeData = some c ∧
      (E.linked s).find? (·.name == c.name) = some l := by
    intro c hc
    obtain ⟨l, hl, hlc⟩ := List.mem_filterMap.mp (hsub.subset hc)
    refine ⟨l, hl, hlc, ?_⟩
    rw [(CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1]
    exact find?_name_of_nodup hnd hl
  obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨l0, -, -, -⟩ := hlc c0 hc0
  have hkind : ∀ c ∈ T.fns, ∃ l ∈ E.linked s, l.calleeData = some c
      ∧ moduleKind (E.linked s) (.ins l0 [] "") c.name = kernelKind l c
      ∧ moduleBlock (E.linked s) c.name = (decodeLprog c.bytes).getD [] := by
    intro c hc
    obtain ⟨l, hl, hlc, hf⟩ := hlc c hc
    refine ⟨l, hl, hlc, by simp [moduleKind, hf, hlc], ?_⟩
    rw [(CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.2.2.2.2.1]
    simp [moduleBlock, hf]
  have hdecq : ∀ c ∈ T.fns, decodeLprog c.bytes = some (moduleBlock (E.linked s) c.name) := by
    intro c hc
    obtain ⟨l, hl, hlc, -, hb⟩ := hkind c hc
    obtain ⟨q, hq, -⟩ := (hk l hl).contract_code hlc
    rw [hb, hq]
    rfl
  -- The source run at the functions of the table alone.
  let ls := (E.linked s).filter fun l => T.names.contains l.name
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
  have henv : linkedEnvOn (E.linked s) (ls.map (·.name)) = linkedEnvOn (E.linked s) T.names := by
    unfold linkedEnvOn
    congr 1
    funext g vals
    by_cases hg : g ∈ T.names
    · simp [hg, (hmemls g).mpr hg]
    · have hg' : g ∉ ls.map (·.name) := fun h => hg ((hmemls g).mp h)
      simp [hg, hg']
  have hT : ProcsAgree (linkedEnvOn (E.linked s) T.names) (summaryTableL ls) := by
    rw [← henv]
    exact procsAgree_summaryTableL hnd (fun l hl => (List.mem_filter.mp hl).1)
      (fun l hl => (hk l (List.mem_filter.mp hl).1).sem_kinds)
      (fun l hl => (hk l (List.mem_filter.mp hl).1).res_slice)
  -- The summaries of the table of the functions of `T`.
  have hwo : ∀ f pr, f ∉ T.names → summaryTableL ls f = some pr → pr.WordOnly ∧ pr.RetWord := by
    intro f pr hf ht
    obtain ⟨l, hl, -⟩ := Option.map_eq_some_iff.mp ht
    have hlf : l.name = f := by simpa using List.find?_some hl
    exact absurd ((hmemls f).mp (List.mem_map.mpr ⟨l, List.mem_of_find?_eq_some hl, hlf⟩)) hf
  have hTc : ∀ c ∈ T.fns, summaryTableL ls c.name
      = some (moduleKind (E.linked s) (.ins l0 [] "") c.name).summary := by
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
  have hK : ∀ c ∈ T.fns, (moduleKind (E.linked s) (.ins l0 [] "") c.name).Top c
      ∧ (moduleKind (E.linked s) (.ins l0 [] "") c.name).Spec
        (runOf ctRegime (moduleBlock (E.linked s) c.name)) := by
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
  have hneB : ∀ c ∈ T.fns, c.bytes ≠ [] := by
    obtain ⟨r0, hr0, hcT⟩ := hpin
    obtain ⟨T', r0', hr0', hcT', -, -, r, b, cert, -, hbs, -⟩ := regionBack_spec_tab h1 hcf'
    rw [hr0, Option.some.injEq] at hr0'
    subst hr0'
    rw [hcT, Option.some.injEq, Option.some.injEq] at hcT'
    subst hcT'
    exact (calleeBytes_tab hbs).2.1
  refine ⟨T, (by obtain ⟨r0, hr0, hcT⟩ := hpin; exact ⟨w, r0, hw, hr0, hcT⟩), hsub, hne, hndT,
    hneB, hdecq, fun c hc => hnoc c hc _ (hdecq c hc),
    fun f => (moduleKind (E.linked s) (.ins l0 [] "") f).sig, fun c hc => ?_,
    fun sa hsep v hrun => ?_⟩
  · obtain ⟨l, hl, hlc, hkk, -⟩ := hkind c hc
    exact ⟨l, hl, hlc, by simp only [hkk]⟩
  obtain ⟨k, V, x, hV, hvx, hx⟩ := E.run_linkedEnv hq0 hp hsep hrun
  have hx' : (VIR.NarrowWords.castProg (nfCtx_wide σ) rfl w).denoteAt
      (linkedEnvOn (E.linked s) T.names) k V =
        some (HVector.cons (VIR.NarrowWords.transTy x) .nil) := by
    rw [denoteAt_linkedEnvOn hcalls, hden, hx]
    rfl
  obtain ⟨pc, -, ⟨sO, hO, hRO⟩, hC⟩ :=
    hrest (moduleKind (E.linked s) (.ins l0 [] ""))
      (fun f => runOf ctRegime (moduleBlock (E.linked s) f)) hK hT hwo hTc
      sa V hV hsep k hx'
  obtain ⟨hdecB, sC, hhC, hRC⟩ := hC (fun c => moduleBlock (E.linked s) c.name) hdecq
    (fun c hc => hnoc c hc _ (hdecq c hc)) (fun _ _ => rfl)
  have hval := denVal_wideTy_transTy (narrowArrB_mapTy_catTy q0.1) x
  exact ⟨pc, hdecB, ⟨sC, hhC, by rw [hvx, ← hval]; exact hRC⟩, sO, hO,
    by rw [hvx, ← hval]; exact hRO⟩

/-- **The runs of the bytes of a program with calls of several linked kernels, at an entry.** Let
    the linked functions of the source program `s` of the entry `E` have distinct names and each be
    a linked kernel, let the translation of `E` return `q0` on `s`, the chain with the declared
    procedures of `s` return a program `p` with a `call`, and `compileRegion` at the data of the
    linked functions of `s` return `(P, bytes)` on `p`. There is a nonempty sublist `cs` of these
    data with distinct names, the table the back half finds, whose code decodes to the region `Q` of
    the blocks `q f` at the entry indices `k f`, such that from every entry state `sa` satisfying
    `σ.Regions` with a source run of `s` to `v` the bytes decode to `pc` followed by `Q` with its
    targets raised by `pc.length`, the program halts through the calls (`HaltsC`) in a state from
    which `σ` reads back `v`, and `pc` halts with its calls answered by the oracle `tabOracle cs
    pc.length k q` in such a state. It is `NFEntry.call_halts_tab`, whose oracle answers within
    `tabOracle` since the precondition of the interface of each kind gives that of the data
    (`LinkedKernel.kind_facts`). At one linked function this is `NFEntry.call_halts`. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.NFEntry.call_halts_multi
    (E : NFEntry) {s : E.Src} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hnd : ((E.linked s).map (·.name)).Nodup)
    (hk : ∀ l ∈ E.linked s, LinkedKernel l)
    {q0 : Σ t : NFDialect.NfTy,
      NFProg NFDialect.nfDialect (CatCrypt.Crypto.Hax.ImpToNF.entryCtx (NFToRoute.abiEntry σ))
        [t]}
    (hq0 : E.toNF σ s = some q0)
    {p : NFProg jasminDialect (nfCtx σ)
      [CryptoToJasminCom.mapTy (CatCrypt.Crypto.Hax.NFToCat.catTy q0.1)]}
    (hp : (extChain (E.decls s) _ q0.1).run q0.2 = some p) (hcf : p.callFree = false)
    (h1 : compileRegion σ (E.names fname σ) p ((E.linked s).filterMap LinkedFn.calleeData)
      = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : E.Runs σ s sa v) :
    ∃ cs : List CalleeData, cs.Sublist ((E.linked s).filterMap LinkedFn.calleeData) ∧ cs ≠ []
      ∧ (cs.map (·.name)).Nodup
      ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
        (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
        ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
        ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
        ∧ decodeLprog bytes = some (pc ++ shiftProg pc.length Q)
        ∧ (∃ sa', HaltsC aMachine (pc ++ shiftProg pc.length Q) 0 sa sa' ∧ σ.ResultOf sa sa' v)
        ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
          ∧ σ.ResultOf sa sa' v := by
  obtain ⟨T, -, hsub, hne, hndT, hneB, hdecq, hnoq, sg, hsg, H⟩ :=
    E.call_halts_tab hnd hk hq0 hp hcf h1
  obtain ⟨pc, hdecB, hCC, sO, hO, hRO⟩ := H sa hsep v hrun
  have hR := T.regionBlocks hne (fun c => moduleBlock (E.linked s) c.name) hdecq hneB hnoq T.names
    (fun _ h => h)
  obtain ⟨xs₂, hd, hr, -⟩ := hR.decode
  refine ⟨T.fns, hsub, hne, hndT, pc,
    X86Backend.LprogBytesLinkReloc.regionProg
      (T.regionEntries fun c => moduleBlock (E.linked s) c.name),
    fun f => T.entryIdx (T.symPos f), moduleBlock (E.linked s), hdecq,
    by show decodeLprog T.bytes = _; simp [decodeLprog, hd, hr], fun c hc => ?_, hdecB,
    hCC, sO, hO.mono fun t s s' ho => ?_, hRO⟩
  · obtain ⟨c', hc'⟩ := T.lookup_of_mem (List.mem_map_of_mem (f := (·.name)) hc)
    obtain ⟨A, B, hQ, hA⟩ := hR.block c.name (List.mem_map_of_mem hc)
    rw [CalleeTab.regionCode_lookup T _ hc', (CalleeTab.lookup_spec hc').2] at hQ
    exact ⟨A, B, hQ, hA⟩
  · obtain ⟨f, hf, ht, tr, hgx⟩ := ho
    refine ⟨f, hf, ht, tr, ?_, hgx.2⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf
    obtain ⟨l, hl, hlc, hsgc⟩ := hsg c hc
    obtain ⟨-, -, -, hpre⟩ := (hk l hl).kind_facts hlc
    have hsig : CalleeTab.sigOf ⟨T.fns⟩ c.name = c.sig := by
      obtain ⟨c', hc'⟩ := T.lookup_of_mem (List.mem_map_of_mem (f := (·.name)) hc)
      obtain ⟨hcm', hn'⟩ := CalleeTab.lookup_spec hc'
      have hcc : c' = c := List.inj_on_of_nodup_map hndT hcm' hc hn'
      subst hcc
      simp [CalleeTab.sigOf, show CalleeTab.lookup ⟨T.fns⟩ c'.name = some c' from hc']
    rw [hsig]
    exact hpre s (hsgc ▸ hgx.1)

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

/-- **The compiler theorem at an entry with linked functions, with the callee-saved
    registers**: the statement of `NFEntry.compileR_correct_linked`, whose first case adds
    that every System V callee-saved register (`DecodedCT.calleeSaved`) holds its value in
    `sa`. The proof is that of `NFEntry.compileR_correct_linked` with
    `NFEntry.compileR_correct_saved` at a program without `call`. -/
theorem NFEntry.compileR_correct_linked_saved (E : NFEntry) (s : E.Src) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : E.compileR s σ fname ((E.linked s).filterMap LinkedFn.calleeData) = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : E.Runs σ s sa v)
    (hnd : ((E.linked s).map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ E.linked s, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x ∈ X86Backend.DecodedCT.calleeSaved, sa'.regs x = sa.regs x)
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
          ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false)
      ∨ ∃ cs : List CalleeData, cs.Sublist ((E.linked s).filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) := by
  rw [NFEntry.compileR_eq_bind] at hc
  obtain ⟨q0, hq0, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨p, hp, hc⟩ := Option.bind_eq_some_iff.mp hc
  cases hcf : p.callFree with
  | true =>
      rw [compileRegion_of_callFree _ _ hcf] at hc
      have hc' : E.compileR s σ fname = some (P, bytes) := by
        simp only [NFEntry.compileR, NFEntry.chainNF, hq0, Option.bind_some, hp, Option.map_some]
        exact hc
      obtain ⟨prog, sa', hd, h⟩ := E.compileR_correct_saved s σ fname P bytes hc' sa hsep v hrun
      exact ⟨prog, hd, .inl ⟨sa', h⟩⟩
  | false =>
      obtain ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hdec, hC, hO⟩ :=
        E.call_halts_multi hnd hk hq0 hp hcf hc sa hsep v hrun
      exact ⟨_, hdec, .inr ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, rfl, hC, hO⟩⟩

/-- **The compiler theorem at an entry with linked functions.** Let the linked functions of the
    source program `s` of the entry `E` have distinct names (`hnd`) and each be a linked kernel
    (`hk`, `LinkedKernel`). For a result of `E.compileR` at the data of these functions, the
    bytes decode to a program `prog`, and from every entry state `sa` satisfying `σ.Regions`,
    every value `v` of a source run of `s` from `sa` (`E.Runs σ s sa v`) is read back by `σ`:

    * either from a state `sa'` at which `prog` halts from `sa`, whose stack register holds
      its value in `sa`, and whose memory agrees with that of `sa` at every byte outside the
      stack words `%rsp + o`, `frameLo ≤ o ≤ frameHi`, and outside the words of each pointer
      region of `σ`, at the registers of `sa`; some run of the address machine on a body
      from `entryA σ sa` then halts and stores to and loads from `layoutMem σ sa` only,
    * or, for a nonempty sublist `cs` with distinct names of the data of the linked functions
      of `s` (the table of the functions the program calls), the program is
      `pc ++ shiftProg pc.length Q` for the region `Q` of the code of `cs`, which decodes to
      the blocks `q f` of the functions, the block of each symbol `f` at the index `k f` of
      `Q`; the program halts through the calls (`HaltsC`) from `sa` in a state from which
      `σ` reads back `v`, and `pc` halts from `sa` with its calls answered by the oracle
      `tabOracle cs pc.length k q` of the leaky runs of the blocks guarded by the
      preconditions of the interfaces of their functions, in such a state. At one function
      `c` the oracle is `oracleAt pc.length (guarded c.sig (runOf ctRegime q))`
      (`tabOracle_one`), the premise of `regionBack_call_bytes_ct`.

    The linked functions enter through the fields `NFEntry.linked` and `NFEntry.linkedAgree`:
    the environment of the linked functions alone implements the declared procedures, and
    each linked function is answered by its meaning `LinkedFn.sem`. On a source program
    without linked functions `hnd` and `hk` hold vacuously (the default arguments close them
    when `E.linked s` reduces to `[]`) and only the first case occurs. A program without
    `call` is the case of `NFEntry.compileR_correct`; a program with a `call` is that of
    `NFEntry.call_halts_multi`. The hax instance is `haxc_correct_auto`; the Aeneas instance
    is stated at `aeneasEntry` with the linked functions of its opaque callees. -/
theorem NFEntry.compileR_correct_linked (E : NFEntry) (s : E.Src) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : E.compileR s σ fname ((E.linked s).filterMap LinkedFn.calleeData) = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : E.Runs σ s sa v)
    (hnd : ((E.linked s).map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ E.linked s, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
          ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false)
      ∨ ∃ cs : List CalleeData, cs.Sublist ((E.linked s).filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) := by
  obtain ⟨prog, hd, h⟩ :=
    E.compileR_correct_linked_saved s σ fname P bytes hc sa hsep v hrun hnd hk
  refine ⟨prog, hd, ?_⟩
  rcases h with ⟨sa', hh, hR, hsp, -, hkeep, hA⟩ | h
  · exact .inl ⟨sa', hh, hR, hsp, hkeep, hA⟩
  · exact .inr h

/-- **The general compiler theorem with no witness, on a module, with the callee-saved
    registers**: the statement of `haxc_correct_auto`, whose first case adds that every
    System V callee-saved register (`DecodedCT.calleeSaved`) holds its value in `sa`. The
    proof is that of `haxc_correct_auto` at `NFEntry.compileR_correct_linked_saved`. -/
theorem haxc_correct_auto_saved (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x ∈ X86Backend.DecodedCT.calleeSaved, sa'.regs x = sa.regs x)
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
  have hl : haxEntry.linked (pairStage m σ).1 = m.linked := pairStage_linked m σ
  obtain ⟨hlo, hhi, hrg⟩ := pairStage_frame m σ
  obtain ⟨prog, hd, h⟩ := haxEntry.compileR_correct_linked_saved _ _ fname P bytes hc sa
    ((pairStage_regions m σ sa).2 hsep) x hrun' (hl ▸ hnd) (hl ▸ hk)
  rw [hl] at h
  refine ⟨prog, hd, ?_⟩
  rcases h with ⟨sa', hh, hR, hsp, hcs, hkeep, hA⟩
    | ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hp, ⟨sa', hC, hR⟩, sa'', hO, hR'⟩
  · rw [hlo, hhi, hrg] at hkeep
    rw [entryA_pairStage, layoutMem_pairStage] at hA
    exact .inl ⟨sa', hh, hback _ hR, hsp, hcs, hkeep, hA⟩
  · exact .inr ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hp, ⟨sa', hC, hback _ hR⟩, sa'',
      hO, hback _ hR'⟩

/-- **The general compiler theorem with no witness, on a module.** Let the linked functions of
    `m` have distinct names (`hnd`) and each be a linked kernel (`hk`, `LinkedKernel`). For the
    result of `compileA` on `m`,
    the bytes decode to a program `prog`, and from every entry state `sa` satisfying
    `σ.Regions`, every value `v` of a source run of `m` from `sa` (`haxRuns σ m sa v`) is read
    back by `σ`, either from a state at which `prog` halts from `sa`, with the entry stack
    register, the entry bytes outside the stack words and the pointer regions of `σ`, and a
    halting run of the address machine from `entryA σ sa` whose stores and loads lie in
    `layoutMem σ sa`, or, for a program `pc ++ shiftProg pc.length Q` calling the region `Q` of
    the decoded blocks of the data `cs` of linked functions of `m`, from a state at which the
    program halts through the calls and from a state at which `pc` halts with its calls answered
    by the oracle `tabOracle` of the guarded blocks (`NFEntry.compileR_correct_linked`).

    The proof is `NFEntry.compileR_correct_linked` at the hax entry `haxEntry`, the module and
    the layout of the pair stage: the
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
  obtain ⟨prog, hd, h⟩ := haxc_correct_auto_saved m σ fname P bytes hc sa hsep v hrun hnd hk
  refine ⟨prog, hd, ?_⟩
  rcases h with ⟨sa', hh, hR, hsp, -, hkeep, hA⟩ | h
  · exact .inl ⟨sa', hh, hR, hsp, hkeep, hA⟩
  · exact .inr h

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
  obtain ⟨prog, hd, h⟩ := haxc_correct_auto m σ fname P bytes hc sa hsep v hrun hnd hk
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
