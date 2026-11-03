/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CallTableCongr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee

@[expose] public section

set_option autoImplicit false

/-!
# The checks of a calling body at the table of the linked functions

The checks `calleeBodyB` of a calling body read the procedure table of the callee
`CalleeData.tab`, which holds the one symbol of the callee with a summary that refuses
every argument list. The checks read the table only through which symbols it holds and at
which arity (`CallTableCongr`), so a body that passes them at this table passes them at
every table that gives the symbol of the callee a summary of the same arity, and the image
run of the calling body (`calleeBody_imgRun`) holds at such a table. A region-compiled
kernel packaged as `LinkedFn.ofRegion` whose layout passes the arguments and the result in
general-purpose registers is a word callee of the image call step
(`ImageAddrCall.WordCallee`), with the specification of its code at the word interface.

## Main results

* `calleeCutB_congr`, `calleeCutB_of_domEq`: the cut checks `calleeCutB` are equal at
  tables that agree on the body, so they transfer to every such table.
* `calleeTab_domEq`: a body whose calls are calls of the symbol of a callee has agreeing
  tables when the tables agree on that symbol.
* `shadowAt_img_of_calleeSegB`: a shadow instruction at a site of `ref` is one of the image
  under the checks of the segments.
* `calleeBody_imgRun_at`: `calleeBody_imgRun` at every table that gives the symbol of the
  callee a summary of its arity; `calleeBody_imgRun_wordSummary` at the summary
  `LinkedFnCallee.wordSummary` of a linked function.
* `wordLayout_ofRegion`: `LinkedFnCallee.WordLayout` of `LinkedFn.ofRegion` from its region
  layout.
* `regionCallee_word`, `regionCallee_wordSpec`: a region-compiled linked function with a
  word layout is a `WordCallee` at `LinkedFnCallee.wordSig`, and its code meets that
  interface; these are the callee hypotheses of `ImageAddrCall.call_reestablishes_word`.
* `outLayout_ofRegion`, `regionCallee_out`: the out layout `LinkedFnCallee.OutLayout` of a
  region-compiled linked function from its region layout, and its code meets the out
  interface `LinkedFnCallee.outSig`; these are the callee hypotheses of
  `ImageAddrCallOutChain.haltsC_of_linkedChecks_out`.
* `commonCalls?_append`, `commonCalls?_movesOf`: the rewriting onto common names of a
  concatenation and of copies.
* `fnStable_withProcs`: the steps of `x86Isa.withProcs T` stay in the function.
* `regionVirt_run_procs`: the run of the webbed exported code and the register copy at
  `x86Isa.withProcs T` for a table that agrees with the call environment.
* `regionCo_bytes_callee`: for a calling body accepted by `regionCoB` at a callee, a
  halting run of the reference at the table, the image entry facts and the read-back of the
  result; stated for bodies without a site of the multiplication fusion.
* `shadowCall?_callImg`, `callSymsB_callImg`, `calleeTab_domEqT`, `calleeBody_imgRun_tab`:
  the shadow instructions of the image of a calling body are the calls of its sites, and the
  image run at a table of callees.
* `commonCallsT?_append`, `commonCallsT?_movesOf`, `regionCo_bytes_tab`: the rewriting onto
  the common names of a table, and the reference of a calling body at a table of callees with
  a word-array result.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (ProcTable ProcSummary)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CallTableCongr
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (boundFacts)

/-! ## 1. The cut checks at agreeing tables -/

/-- **The cut checks are equal at tables that agree on the body.** -/
theorem calleeCutB_congr {T T' : ProcTable} {fin : LLabel} {B : List LinstrRM}
    (h : ProcTable.DomEq T T' B) : calleeCutB T fin B = calleeCutB T' fin B := by
  simp only [calleeCutB, cutOkB_congr h, sites_congr h]
  congr 1
  exact List.all_congr rfl fun e => List.all_congr rfl fun x =>
    isCutRevB_congr h (domEq_cutAt h e x) x _

/-- **The cut checks transfer to an agreeing table.** If `B` passes `calleeCutB` at the
    table `T` and the table `T'` agrees with `T` on `B`, then `B` passes the cut checks at
    `T'`. -/
theorem calleeCutB_of_domEq {T T' : ProcTable} {fin : LLabel} {B : List LinstrRM}
    (h : calleeCutB T fin B = true) (hD : ProcTable.DomEq T T' B) :
    calleeCutB T' fin B = true :=
  (calleeCutB_congr hD).symm.trans h

/-! ## 2. Tables that agree on the symbol of the callee -/

/-- **The table of a callee agrees with every table that gives its symbol a summary of its
    arity**, on a body whose calls are calls of that symbol. -/
theorem calleeTab_domEq {c : CalleeData} {T : ProcTable} {pr : ProcSummary}
    (hT : T c.name = some pr) (ha : pr.arity = c.args.length) {B : List LinstrRM}
    (h : X86Backend.CalleeSegCheck.callSymsB (· == c.name) B = true) :
    ProcTable.DomEq c.tab T B :=
  domEq_of_symsB h fun f hf => by
    obtain rfl := beq_iff_eq.mp hf
    simp [CalleeData.tab, hT, ha]

/-- **A shadow instruction at a site of `ref` is a shadow instruction of the image.** If
    the checks of the segments `calleeSegB T₀` accept `ref` and `img`, every shadow
    instruction of `ref` at a position `p` whose symbol has a summary in `T₀` is the shadow
    instruction of `img` at some position. -/
theorem shadowAt_img_of_calleeSegB {T₀ : ProcTable} {fn : String} {fin : LLabel}
    {ins : Option Nat → List String} {outs : List String} {ref img : List LinstrRM}
    (h : X86Backend.CalleeSegCheck.calleeSegB T₀ fn fin ins outs ref img = true) {p : Nat}
    {x : String × String × List LOperand}
    (hp : X86Backend.CalleeSegCheck.shadowAt ref p = some x) (hx : (T₀ x.2.1).isSome) :
    ∃ q, X86Backend.CalleeSegCheck.shadowAt img q = some x := by
  simp only [X86Backend.CalleeSegCheck.calleeSegB, Bool.and_eq_true, beq_iff_eq] at h
  have hmem : p ∈ LprogCallCut.sites T₀ ref := by
    simp only [LprogCallCut.sites, List.mem_filter, List.mem_range]
    cases hr : ref[p]? with
    | none => simp [X86Backend.CalleeSegCheck.shadowAt, hr] at hp
    | some i =>
      simp only [X86Backend.CalleeSegCheck.shadowAt, hr, Option.bind_some] at hp
      refine ⟨(List.getElem?_eq_some_iff.mp hr).1, ?_⟩
      simp [LprogCallCut.isProcB, LprogIsa.procCall?, hp, hx]
  have hin : some x ∈ (LprogCallCut.sites T₀ img).map
      (X86Backend.CalleeSegCheck.shadowAt img) := by
    rw [← h.1.1]
    exact hp ▸ List.mem_map_of_mem hmem
  obtain ⟨q, -, hq⟩ := List.mem_map.mp hin
  exact ⟨q, hq⟩

/-- **The image run of a calling body at a table of the callee's arity.** If the printed
    body `body` passes the checks `calleeBodyB` against the reference `ref` at the function
    name `fn`, and the table `T` gives the symbol of `c` a summary `pr` of the arity of `c`
    that has no word-array result or at whose call sites `calleeSiteAt` the destination is
    among the operands,
    every halting run of `x86Isa.withProcs T` on `ref`, from a state of `fn` at pc `0` whose
    registers satisfy the entry facts `boundFacts σ nm`, is matched by a halting run of
    `CheckedIsaCall.x86IsaK.withProcs T` on the image `ImageAddrCall.callImg` of `body` at
    those call sites from
    the same state, the end states agreeing on the registers `outs`, the arrays and the word
    memory. -/
theorem calleeBody_imgRun_at {σ : AbiLayout} {nm : String → String} {c : CalleeData}
    {sl : String → Option (String × Nat)} {outs : List String} {body : Lcmd}
    {ref : List LinstrRM} {fn : String} (h : calleeBodyB σ nm c sl outs body ref fn = true)
    {T : ProcTable} {pr : ProcSummary} (hT : T c.name = some pr)
    (ha : pr.arity = c.args.length)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ boundFacts σ nm, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : (X86Backend.X86Isa.x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn ref)
      fuel s = some t)
    (hres : pr.RetWord ∨
      ∀ q, (calleeSiteAt c sl body q).1 ∈ (calleeSiteAt c sl body q).2 := by
      exact Or.inl rfl) :
    ∃ fuel' t', (X86Backend.CheckedIsaCall.x86IsaK.withProcs T).lsemFuelMemF
        (singletonProgM fn
          (X86Backend.ImageAddrCall.callImg sl (calleeSiteAt c sl body) body))
        fuel' s = some t'
      ∧ X86Backend.OwnedLprogTV.Obs outs t t' := by
  have hok := calleeBodyB_spec.mp h
  have hsi : X86Backend.CalleeSegCheck.callSymsB (· == c.name)
      (X86Backend.ImageAddrCall.callImg sl (calleeSiteAt c sl body) body) = true := by
    simp only [X86Backend.CalleeSegCheck.callSymsB, List.all_eq_true]
    intro i hi
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hi
    have hm := List.all_eq_true.mp hok.shapeImg p
      (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hp).1)
    rw [hp, Option.all_some] at hm
    cases hs : LprogIsa.shadowCall? i.fst with
    | none => rfl
    | some q =>
      rw [hs] at hm
      obtain rfl := of_decide_eq_true hm
      simp
  have hDr := calleeTab_domEq hT ha hok.symsRef
  have hDi := calleeTab_domEq hT ha hsi
  have hres' : ∀ (p : Nat) (d f : String) (xs : List String) (pr' : ProcSummary),
      X86Backend.CalleeSegCheck.shadowAt ref p = some (d, f, xs.map LOperand.reg) →
      T f = some pr' → pr'.RetWord ∨ d ∈ xs := by
    intro p d f xs pr' hp hf
    have hfc : f = c.name := by
      unfold X86Backend.CalleeSegCheck.shadowAt at hp
      cases hr : ref[p]? with
      | none => simp [hr] at hp
      | some i =>
        simp only [hr, Option.bind_some] at hp
        have hm := List.all_eq_true.mp hok.symsRef i (List.mem_of_getElem? hr)
        simpa [hp] using hm
    subst hfc
    rw [hT] at hf
    cases hf
    refine hres.imp id fun hall => ?_
    obtain ⟨q, hq⟩ := shadowAt_img_of_calleeSegB hok.seg hp (by simp [CalleeData.tab])
    unfold X86Backend.CalleeSegCheck.shadowAt at hq
    cases hr : (X86Backend.ImageAddrCall.callImg sl (calleeSiteAt c sl body) body)[q]? with
    | none => simp [hr] at hq
    | some i =>
      simp only [hr, Option.bind_some] at hq
      have hm := List.all_eq_true.mp hok.shapeImg q
        (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hr).1)
      rw [hr, Option.all_some] at hm
      simp only [hq, decide_eq_true_eq, Prod.mk.injEq] at hm
      obtain ⟨rfl, -, hxs⟩ := hm
      rw [List.map_injective_iff.mpr (fun _ _ h => LOperand.reg.inj h) hxs]
      exact hall q
  exact calleeSegB_soundK_of_domEq hok.seg hDr hDi
    (calleeCutB_soundK (calleeCutB_of_domEq hok.cutRef hDr)
      (calleeCutB_of_domEq hok.cutImg hDi) outs fn)
    s t hfn hpc fuel (refRun_checked_of_domEq hok.idx hDr fn s t hfn hpc hent fuel hrun) hres'

/-- **The image run of a calling body at the word summary of a linked function.**
    `calleeBody_imgRun_at` at a table that gives the symbol of `c` the summary
    `LinkedFnCallee.wordSummary l` of a linked function `l` with as many parameters as `c`
    has arguments. -/
theorem calleeBody_imgRun_wordSummary {σ : AbiLayout} {nm : String → String}
    {c : CalleeData} {sl : String → Option (String × Nat)} {outs : List String}
    {body : Lcmd} {ref : List LinstrRM} {fn : String}
    (h : calleeBodyB σ nm c sl outs body ref fn = true) {l : CatCrypt.Crypto.Hax.LinkedFn}
    (hl : l.params.length = c.args.length) {T : ProcTable}
    (hT : T c.name = some (X86Backend.LinkedFnCallee.wordSummary l))
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ boundFacts σ nm, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : (X86Backend.X86Isa.x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn ref)
      fuel s = some t) :
    ∃ fuel' t', (X86Backend.CheckedIsaCall.x86IsaK.withProcs T).lsemFuelMemF
        (singletonProgM fn
          (X86Backend.ImageAddrCall.callImg sl (calleeSiteAt c sl body) body))
        fuel' s = some t'
      ∧ X86Backend.OwnedLprogTV.Obs outs t t' :=
  calleeBody_imgRun_at h hT hl s t hfn hpc hent fuel hrun

/-! ## 2b. The image run at a table of callees -/

/-- **A shadow instruction of the image of a calling body is the call of its site.** Under
    `ImageAddrCall.callSitesB`, a shadow instruction `x` of the image `callImg sl site body` at
    the position `q` sits at a call of the symbol `x.2.1` in `body`, and its destination and
    operands are those of `site q`. -/
theorem shadowCall?_callImg {sl : String → Option (String × Nat)} {body : Lcmd}
    (site : Nat → String × List String)
    (hcs : X86Backend.ImageAddrCall.callSitesB sl body = true) {q : Nat} {i : LinstrRM}
    (hi : (X86Backend.ImageAddrCall.callImg sl site body)[q]? = some i)
    {x : String × String × List LOperand} (hx : LprogIsa.shadowCall? i.fst = some x) :
    (∃ bi ra l, body[q]? = some bi ∧ bi.li_i = .Lcall ra (x.2.1, l))
      ∧ x = ((site q).1, x.2.1, (site q).2.map LOperand.reg) := by
  have hq : q < body.length - 1 := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    rwa [X86Backend.ImageAddrCall.callImg_length] at this
  obtain ⟨bi, hb⟩ : ∃ bi, body[q]? = some bi := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  cases hc : X86Backend.ImageAddrCall.isCallB bi.li_i with
  | false =>
      rw [X86Backend.ImageAddrCall.callImg_getElem?_imgInstr sl site hb hq hc] at hi
      obtain rfl := Option.some.inj hi
      rw [X86Backend.ImageAddrCall.callSitesB_other hcs hb hq
        (fun ra t e => by simp [e, X86Backend.ImageAddrCall.isCallB] at hc)] at hx
      cases hx
  | true =>
      obtain ⟨ra, g, l, e⟩ := X86Backend.ImageAddrCall.exists_lcall_of_isCallB hc
      obtain rfl := X86Backend.ImageAddrCall.callSitesB_call hcs hb hq e
      rw [X86Backend.ImageAddrCall.callImg_getElem?_call sl site hb (by omega) e] at hi
      obtain rfl := Option.some.inj hi
      rw [LprogIsa.shadowCall?_callShadow] at hx
      obtain rfl := Option.some.inj hx
      exact ⟨⟨bi, none, l, hb, e⟩, rfl⟩

/-- **The shadow instructions of the image call the symbols of the calls of the body**: under
    `ImageAddrCall.callSitesB`, when every call of `body` names a symbol accepted by `ok`, so
    does every shadow instruction of the image. -/
theorem callSymsB_callImg {sl : String → Option (String × Nat)} {body : Lcmd}
    (site : Nat → String × List String) {ok : String → Bool}
    (hcs : X86Backend.ImageAddrCall.callSitesB sl body = true)
    (hsym : X86Backend.ImageAddrCall.bodyCallSymsB ok body = true) :
    X86Backend.CalleeSegCheck.callSymsB ok
      (X86Backend.ImageAddrCall.callImg sl site body) = true := by
  simp only [X86Backend.CalleeSegCheck.callSymsB, List.all_eq_true]
  intro i hi
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hi
  cases hs : LprogIsa.shadowCall? i.fst with
  | none => rfl
  | some x =>
      obtain ⟨⟨bi, ra, l, hb, hbi⟩, -⟩ := shadowCall?_callImg site hcs hq hs
      have hlt : q < body.length - 1 := by
        have := (List.getElem?_eq_some_iff.mp hq).1
        rwa [X86Backend.ImageAddrCall.callImg_length] at this
      rw [Option.all_some]
      exact X86Backend.ImageAddrCall.bodyCallSymsB_spec hsym hb hlt hbi

/-- **The table of procedures of a table of callees agrees with every table that gives each
    of its symbols a summary of the arity of its function**, on a body whose calls are calls
    of symbols of the table. -/
theorem calleeTab_domEqT {T : CalleeTab} {PT : ProcTable}
    (hT : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length)
    {B : List LinstrRM}
    (h : X86Backend.CalleeSegCheck.callSymsB (fun g => T.names.contains g) B = true) :
    ProcTable.DomEq T.tab PT B :=
  domEq_of_symsB h fun f hf => by
    have hs : (T.lookup f).isSome = true := by
      have h1 := congrFun T.lookup_isSome f
      rw [h1]
      exact hf
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨pr, hpr, ha⟩ := hT f c hc
    simp [CalleeTab.tab, hc, hpr, ha]

/-- **The image run of a calling body at a table of callees.** If the printed body `body`
    passes the checks `calleeBodyBT` at the table `T` against the reference `ref` at the
    function name `fn`, and the procedure table `PT` gives each symbol of `T` a summary of the
    arity of its function that has no word-array result or at whose call sites the
    destination is among the operands, every halting run of `x86Isa.withProcs PT` on `ref`,
    from a state of `fn` at pc `0` whose registers satisfy the entry facts `boundFacts σ nm`,
    is matched by a halting run of `CheckedIsaCall.x86IsaK.withProcs PT` on the image
    `ImageAddrCall.callImg` of `body` at the site function `siteFn T.lookup` from the same
    state, the end states agreeing on the registers `outs`, the arrays and the word memory.
    At the table of one function this is `calleeBody_imgRun_at`. -/
theorem calleeBody_imgRun_tab {σ : AbiLayout} {nm : String → String} {T : CalleeTab}
    {sl : String → Option (String × Nat)} {outs : List String} {body : Lcmd}
    {ref : List LinstrRM} {fn : String} (h : calleeBodyBT σ nm T sl outs body ref fn = true)
    {PT : ProcTable}
    (hT : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length
      ∧ (pr.RetWord ∨ ∀ q, callSymAt body q = some f →
        (calleeSiteAt c sl body q).1 ∈ (calleeSiteAt c sl body q).2))
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ boundFacts σ nm, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : (X86Backend.X86Isa.x86Isa.withProcs PT).lsemFuelMemF (singletonProgM fn ref)
      fuel s = some t) :
    ∃ fuel' t', (X86Backend.CheckedIsaCall.x86IsaK.withProcs PT).lsemFuelMemF
        (singletonProgM fn
          (X86Backend.ImageAddrCall.callImg sl (siteFn T.lookup sl body) body))
        fuel' s = some t'
      ∧ X86Backend.OwnedLprogTV.Obs outs t t' := by
  have hok := calleeBodyBT_spec.mp h
  have hsymB : X86Backend.ImageAddrCall.bodyCallSymsB (fun g => T.names.contains g) body
      = true := by
    have h1 := bodyCallSymsB_of_decodeSites hok.decode
    rwa [CalleeTab.lookup_isSome] at h1
  have hsi := callSymsB_callImg (siteFn T.lookup sl body) hok.callSites hsymB
  have hT' : ∀ f c, T.lookup f = some c → ∃ pr, PT f = some pr ∧ pr.arity = c.args.length :=
    fun f c hc => let ⟨pr, hpr, ha, _⟩ := hT f c hc; ⟨pr, hpr, ha⟩
  have hDr := calleeTab_domEqT hT' hok.symsRef
  have hDi := calleeTab_domEqT hT' hsi
  have hres' : ∀ (p : Nat) (d f : String) (xs : List String) (pr' : ProcSummary),
      X86Backend.CalleeSegCheck.shadowAt ref p = some (d, f, xs.map LOperand.reg) →
      PT f = some pr' → pr'.RetWord ∨ d ∈ xs := by
    intro p d f xs pr' hp hf
    have hfT : T.names.contains f = true := by
      unfold X86Backend.CalleeSegCheck.shadowAt at hp
      cases hr : ref[p]? with
      | none => simp [hr] at hp
      | some i =>
        simp only [hr, Option.bind_some] at hp
        have hm := List.all_eq_true.mp hok.symsRef i (List.mem_of_getElem? hr)
        simpa [hp] using hm
    have hs : (T.lookup f).isSome = true := by
      have h1 := congrFun T.lookup_isSome f
      rw [h1]
      exact hfT
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨pr, hpr, -, hres⟩ := hT f c hc
    rw [hpr] at hf
    cases hf
    refine hres.imp id fun hall => ?_
    obtain ⟨q, hq⟩ := shadowAt_img_of_calleeSegB hok.seg hp (by simp [CalleeTab.tab, hc])
    unfold X86Backend.CalleeSegCheck.shadowAt at hq
    cases hr : (X86Backend.ImageAddrCall.callImg sl (siteFn T.lookup sl body) body)[q]? with
    | none => simp [hr] at hq
    | some i =>
      simp only [hr, Option.bind_some] at hq
      obtain ⟨⟨bi, ra, l, hb, hbi⟩, hx⟩ := shadowCall?_callImg _ hok.callSites hr hq
      have hcs : callSymAt body q = some f := callSymAt_eq_some.mpr ⟨bi, ra, l, hb, hbi⟩
      have hsite : siteFn T.lookup sl body q = calleeSiteAt c sl body q := by
        simp [siteFn, hcs, hc]
      simp only [Prod.mk.injEq, hsite] at hx
      obtain ⟨hd, -, hxs⟩ := hx
      have hxs' : xs = (calleeSiteAt c sl body q).2 :=
        List.map_injective_iff.mpr (fun _ _ h => LOperand.reg.inj h) hxs
      rw [hxs', hd]
      exact hall q hcs
  exact calleeSegB_soundK_of_domEq hok.seg hDr hDi
    (calleeCutB_soundK (calleeCutB_of_domEq hok.cutRef hDr)
      (calleeCutB_of_domEq hok.cutImg hDi) outs fn)
    s t hfn hpc fuel (refRun_checked_of_domEq hok.idx hDr fn s t hfn hpc hent fuel hrun) hres'

/-! ## 3. A region-compiled linked function as a word callee -/

section OfRegion

open CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (NFCT)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)

variable {name : String} {params : List (String × NFDialect.NfTy)} {kres : NFDialect.NfTy}
  {sem : List _root_.Hax.Value → Option _root_.Hax.Value}
  {sem_res : ∀ vals v, sem vals = some v →
    (CatCrypt.Crypto.Hax.ImpToNF.dec kres v).isSome = true}
  {σ : AbiLayout} {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
  {clob : List String} {F : Nat} {bytes : List (BitVec 8)}
  {hsem : ∀ sa sa' v, regionPre σ p sa → regionPost σ p sa sa' →
    sem (σ.args.map (·.read sa)) = some v → σ.ResultOf sa sa' v} {h0 : σ.pubWords = []}
  {K : StorePol}

/-- **The word layout of a region-compiled linked function from its region layout.** If the
    parameters of `σ` are, in order, scalars in the registers of the general-purpose names
    `ws`, the result of `σ` is the register of the general-purpose name `r`, and `clob`
    holds that register, then `LinkedFn.ofRegion` has the word layout at `ws` and `r`. -/
theorem wordLayout_ofRegion {ws : List String} {r : String}
    (hargs : σ.args.map (fun a => (a.reg, a.kind)) = ws.map fun w => (phys w, ArgKind.scalar))
    (hres : σ.result = .reg (phys r)) (hws : ∀ a ∈ ws, gpOk a = true) (hr : gpOk r = true)
    (hclob : clob.contains (phys r) = true) :
    WordLayout (CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params kres sem sem_res σ p clob F
      bytes hsem h0 K) ws r :=
  ⟨hargs, hres, hws, hr, hclob⟩

/-- **A region-compiled linked function with a word layout is a word callee.** Under the
    conditions of `wordLayout_ofRegion`, `LinkedFn.ofRegion` is a `WordCallee` at its word
    interface `wordSig` and the result name `r`, with the summary `wordSummary` on its
    precondition `regionPre σ p` (`wordCallee_of_linkedFn`). -/
theorem regionCallee_word {ws : List String} {r : String}
    (hargs : σ.args.map (fun a => (a.reg, a.kind)) = ws.map fun w => (phys w, ArgKind.scalar))
    (hres : σ.result = .reg (phys r)) (hws : ∀ a ∈ ws, gpOk a = true) (hr : gpOk r = true)
    (hclob : clob.contains (phys r) = true) :
    let l := CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params kres sem sem_res σ p clob F
      bytes hsem h0 K
    X86Backend.ImageAddrCall.WordCallee (wordSig l ws r) r (wordSummary l) l.pre :=
  wordCallee_of_linkedFn (wordLayout_ofRegion hargs hres hws hr hclob)

/-- **The code of a region-compiled linked function meets its word interface.** Let
    `compileRegion σ a p` give the bytes of `LinkedFn.ofRegion`, decoding to the block `q`
    that passes `keepCheckWB` at the clobbered registers, the frame size and the store policy
    `K` of the record, on a program `p` that is constant time at the source events for labels
    `L` that agree with the public data of `σ`, at every fuel. Then the leaky run of `q`
    under `ctRegime` meets the word interface `wordSig` at the names `ws` and `r`
    (`ofRegion_calleeSpec` and `calleeSpec_wordSig`). -/
theorem regionCallee_wordSpec {a : AbiNames} {P : Lprog}
    (h : compileRegion σ a p = some (P, bytes)) {q : List RInstr}
    (hq : decodeLprog bytes = some q) (ws : List String) (r : String)
    (hk : keepCheckWB q (fun x => clob.contains x) F K = true) (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel p) (hL : PubLabelsOK σ L) :
    let l := CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params kres sem sem_res σ p clob F
      bytes hsem h0 K
    CalleeSpec (runOf ctRegime q) (wordSig l ws r) :=
  calleeSpec_wordSig (ofRegion_calleeSpec (hsem := hsem) (h0 := h0) h hq ws (some r) hk L hsrc hL)

/-- **The out layout of a region-compiled linked function from its region layout.** If the
    parameters of `σ` are, in order, the parameters `ins` in the registers of their names,
    each name a general-purpose name, a parameter at any position is an array of `n` words
    at the register of `po`, and the result of `σ` is the `n` words at that register, then
    `LinkedFn.ofRegion` at the store policy `K` has the out layout at `ins`, `po` and `n`
    when its footprint `KeepFoot K F` is among the `F + K.red` bytes below the entry stack
    register and the `n` words at the entry value of the register of `po` (`hK`; at `K := .frame` by
    `keepFoot_frame`). -/
theorem outLayout_ofRegion {ins : List (String × ArgKind)} {po : String} {n : Nat}
    (hargs : σ.args.map (fun a => (a.reg, a.kind)) = ins.map fun q => (phys q.1, q.2))
    (hdest : (po, ArgKind.words n) ∈ ins) (hres : σ.result = .words (phys po) n)
    (hgp : ∀ q ∈ ins, gpOk q.1 = true)
    (hK : ∀ (s : Ascent.AddrMem.AState) x, KeepFoot K F s.regs x →
      InFrame (s.regs "%rsp") (F + K.red) x ∨
        ∃ j < n, Ascent.AddrMem.InRange8 (X86Backend.ImageAddrSim.cellAt (s.regs (phys po)) j) x
      := by exact fun _ _ hx => Or.inl (keepFoot_frame.1 hx)) :
    OutLayout (CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params kres sem sem_res σ p clob F
      bytes hsem h0 K) ins po n :=
  ⟨hargs, hdest, hres, hgp,
    fun s x hx => (hK s x hx).imp_left (inFrame_of_le (le_max_left _ _))⟩

/-- **The code of a region-compiled linked function meets its out interface.** Under the
    hypotheses of `regionCallee_wordSpec`, the leaky run of `q` under `ctRegime` meets the
    out interface `outSig` at the parameters `ins` and the length `n` (`ofRegion_calleeSpec`
    at the names of `ins` and no result register, under the precondition of
    `outSig`). -/
theorem regionCallee_out {a : AbiNames} {P : Lprog}
    (h : compileRegion σ a p = some (P, bytes)) {q : List RInstr}
    (hq : decodeLprog bytes = some q) (ins : List (String × ArgKind)) (n : Nat)
    (hk : keepCheckWB q (fun x => clob.contains x) F K = true) (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel p) (hL : PubLabelsOK σ L) :
    let l := CatCrypt.Crypto.Hax.LinkedFn.ofRegion name params kres sem sem_res σ p clob F
      bytes hsem h0 K
    CalleeSpec (runOf ctRegime q) (outSig l ins n) := by
  intro l
  exact CalleeSpec.restrictPre
    (ofRegion_calleeSpec (name := name) (params := params) (res := kres) (sem_res := sem_res)
      (hsem := hsem) (h0 := h0) h hq (ins.map Prod.fst) none hk L hsrc hL)
    (P := (outSig l ins n).pre) fun _ hs => hs.1

end OfRegion

/-! ## 4. The reference of a calling body at a procedure table -/

section Calling

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (movesOf movesOf_isLopn renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (chainAliasO)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs (x86Isa_refusesProcs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf AbiEntryM
  storeAgreesM_of_abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg

/-- **The rewriting onto common names of a concatenation** is the concatenation of the
    rewritings. -/
theorem commonCalls?_append {sh : LprogCallCut.CallShape} {f : String} {args : List String}
    {res : String} :
    ∀ (A B : List LinstrRM), LprogCallCut.commonCalls? sh f args res (A ++ B)
      = (LprogCallCut.commonCalls? sh f args res A).bind fun A' =>
          (LprogCallCut.commonCalls? sh f args res B).map (A' ++ ·)
  | [], B => by
      simp only [List.nil_append, LprogCallCut.commonCalls?, Option.bind_some]
      cases LprogCallCut.commonCalls? sh f args res B <;> rfl
  | i :: A, B => by
      simp only [List.cons_append, LprogCallCut.commonCalls?, commonCalls?_append A B]
      cases LprogCallCut.commonCall? sh f args res i with
      | none => rfl
      | some is =>
          simp only [Option.bind_some]
          cases LprogCallCut.commonCalls? sh f args res A with
          | none => rfl
          | some A' =>
              cases LprogCallCut.commonCalls? sh f args res B with
              | none => rfl
              | some B' => simp

/-- **The copies of a list of pairs are unchanged by the rewriting onto common names.** -/
theorem commonCalls?_movesOf {sh : LprogCallCut.CallShape} {f : String} {args : List String}
    {res : String} :
    ∀ ps : List (String × String),
      LprogCallCut.commonCalls? sh f args res (movesOf ps) = some (movesOf ps)
  | [] => rfl
  | p :: ps => by
      have h := commonCalls?_movesOf (sh := sh) (f := f) (args := args) (res := res) ps
      simp only [movesOf, List.map_cons] at h ⊢
      simp only [LprogCallCut.commonCalls?, LprogCallCut.commonCall?, h]
      rfl

/-- **The rewriting onto the common names of a table of a concatenation** is the
    concatenation of the rewritings. -/
theorem commonCallsT?_append
    {tab : String → Option (LprogCallCut.CallShape × List String × String)} :
    ∀ (A B : List LinstrRM), LprogCallCut.commonCallsT? tab (A ++ B)
      = (LprogCallCut.commonCallsT? tab A).bind fun A' =>
          (LprogCallCut.commonCallsT? tab B).map (A' ++ ·)
  | [], B => by
      simp only [List.nil_append, LprogCallCut.commonCallsT?, Option.bind_some]
      cases LprogCallCut.commonCallsT? tab B <;> rfl
  | i :: A, B => by
      simp only [List.cons_append, LprogCallCut.commonCallsT?, commonCallsT?_append A B]
      cases LprogCallCut.commonCallT? tab i with
      | none => rfl
      | some is =>
          simp only [Option.bind_some]
          cases LprogCallCut.commonCallsT? tab A with
          | none => rfl
          | some A' =>
              cases LprogCallCut.commonCallsT? tab B with
              | none => rfl
              | some B' => simp

/-- **The copies of a list of pairs are unchanged by the rewriting onto the common names of a
    table.** -/
theorem commonCallsT?_movesOf
    {tab : String → Option (LprogCallCut.CallShape × List String × String)} :
    ∀ ps : List (String × String),
      LprogCallCut.commonCallsT? tab (movesOf ps) = some (movesOf ps)
  | [] => rfl
  | p :: ps => by
      have h := commonCallsT?_movesOf (tab := tab) ps
      simp only [movesOf, List.map_cons] at h ⊢
      simp only [LprogCallCut.commonCallsT?, LprogCallCut.commonCallT?, h]
      rfl

/-- A step of the x86 instruction set with procedure summaries stays in the function of its
    state: a step of `x86Isa`, or the step `procStep` of a summary, which writes its result
    and advances the counter. -/
theorem fnStable_withProcs (T : ProcTable) : LprogCallCut.FnStable (x86Isa.withProcs T) := by
  intro P i s u h
  cases hq : LprogIsa.procCall? T i.fst with
  | none =>
      rw [Isa.withProcs_step_of_none x86Isa T P i s hq] at h
      exact LprogCallCut.fnStable_x86Isa P i s u h
  | some q =>
      obtain ⟨pr, dst, srcs⟩ := q
      simp only [Isa.withProcs, hq, LprogIsa.procStep] at h
      split at h
      · obtain ⟨vs, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp h
        cases x <;> rfl
      · cases h

/-- **The run of the webbed code of a region export at a procedure table.** Let `p` be a
    program of `RegionExportable` with the export `r`, let the frame map `fr` satisfy the
    facts of the entry check, let the table `T` agree with the call environment `Ec`, and let
    the steps of `x86Isa.withProcs T` beyond `x86Isa` be local calls at the array positions
    `aa` and the result lengths `ao`. At a valuation `V` the layout `σ` reads off the machine
    state `sa`, if `p` denotes `v` at `V` in `Ec` then the code of the webs
    `regionWebs ex r aa ao` followed by the register copy `ret`, run by `x86Isa.withProcs T`
    from the entry state `entryV` at a map `un` of array names that fixes the argument
    names, halts in a state `t`. A state `t1` agrees with the returned operands at `v`, and
    the state `t0` before the copy has the variable registers of `t1` and the arrays of `t1`
    at the names `regionWebsObs ex r`; without a copy `t` is `t0`, and after the copy of `x`
    into `y` the cell of `y` in `t` is the cell of `x` in `t0`. -/
theorem regionVirt_run_procs (σ : AbiLayout) (nm : String → String) (fn : String)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    (hp : RegionExportable p) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r) (ex : List String)
    (ret : Option (String × String))
    {fr : String → Option (BitVec 64)} (E : EntryFacts σ nm fr) (un : String → String)
    (hU : ∀ j, j < σ.args.length → un (argName j) = argName j) (sa : AState)
    (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) {Ec : CallEnv jasminDialect}
    {T : ProcTable} (hT : ProcsAgree Ec T) {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hcl : (x86Isa.withProcs T).CallLocal x86Isa aa ao)
    (fuel : Nat)
    (v : Ctxt.Valuation (d := jasminDialect) ts) (hden : p.denoteAt Ec fuel V = some v) :
    ∃ (k : Nat) (t t0 t1 : LstateMF),
      (x86Isa.withProcs T).lsemFuelMemF
          (singletonProgM fn ((regionWebs ex r aa ao).code ++ movesOf ret.toList)) k
        { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } = some t
      ∧ ResAgrees Γ.length r.depth t1.prog.base r.res v
      ∧ t0.prog.base.reg.lvm = t1.prog.base.reg.lvm
      ∧ (∀ x ∈ regionWebsObs ex r, t0.prog.base.larr x = t1.prog.base.larr x)
      ∧ (ret = none → t = t0)
      ∧ (∀ x y, ret = some (x, y) → t.prog.base.reg.lvm y = t0.prog.base.reg.lvm x) := by
  have habi : AbiEntryM σ sa (entryV σ fr sa un) := entryV_abiEntry E.argF E.argG hU
  have hag0 := storeAgreesM_of_abi hV habi
  have hle : x86Isa.StepLe (x86Isa.withProcs T) :=
    x86Isa.withProcs_stepLe (x86Isa_refusesProcs T)
  obtain ⟨k1, t1, hrun1, hat1, hres, -, -⟩ := @exportRSim_run Γ.length fn Γ ts p
    (x86Isa.withProcs T) ⟨Ec⟩ (exportR_sim_procs Γ.length fn hT (x86Isa_refusesProcs T) hp)
    Γ.length 0 r hr rfl le_rfl fuel V v hden (entryV σ fr sa un) false habi.pc hag0
  obtain ⟨t0, hrun2, hlt0, hft0, hlvm, harr⟩ := regionWebs_run hle hcl (fnStable_withProcs T)
    ex r (fn := fn) (k1 + 0) rfl habi.pc (hrun1 0) hat1.2
  obtain ⟨n0, -, hst0, -⟩ := Ascent.IsaCall.steps_of_lsemFuelMemF _ _ _ _ _ hrun2
  have hz : ∀ x : LstateMF, Ascent.IsaCall.shiftPc 0 x = x := fun x => by
    simp only [Ascent.IsaCall.shiftPc, Nat.zero_add]
    rfl
  have hs := Ascent.IsaCall.steps_relocate (x86Isa.withProcs T) fn (pre := [])
    (movesOf ret.toList)
    (X86Backend.ArrWebs.withProcs_stepRelocates T fn [] _ _) (fun _ _ _ => rfl) hst0
  simp only [List.nil_append, List.length_nil, hz] at hs
  have hat : atPc (singletonProgM fn ((regionWebs ex r aa ao).code ++ movesOf ret.toList))
      (regionWebs ex r aa ao).code.length t0 :=
    ⟨hft0, by rw [hlt0, regionWebs_length]⟩
  obtain ⟨n, t, hst, hhalt, h1, h2⟩ : ∃ (n : Nat) (t : LstateMF),
      Steps (x86Isa.withProcs T)
          (singletonProgM fn ((regionWebs ex r aa ao).code ++ movesOf ret.toList)) n
        { prog := { base := entryV σ fr sa un, lfn := fn }, zf := false } t
      ∧ Halted (singletonProgM fn ((regionWebs ex r aa ao).code ++ movesOf ret.toList)) t
      ∧ (ret = none → t = t0)
      ∧ (∀ x y, ret = some (x, y) → t.prog.base.reg.lvm y = t0.prog.base.reg.lvm x) := by
    cases ret with
    | none =>
        exact ⟨n0, t0, hs, halted_of_atPc hat (by simp [singletonProgM, movesOf]),
          fun _ => rfl, fun _ _ h => (by cases h)⟩
    | some q =>
        obtain ⟨x, y⟩ := q
        obtain ⟨t3, hs1, hat3, -, hl⟩ := steps_movReg (dst := y) (src := x) hat (by
          show ((regionWebs ex r aa ao).code ++ movesOf [(x, y)])[_]? = _
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl)
        refine ⟨n0 + 1, t3, hs.trans (steps_of_stepLe hle hs1),
          halted_of_atPc hat3 (by simp [singletonProgM, movesOf]), nofun,
          fun x' y' h => ?_⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        rw [hl, ite_eq_left rfl]
  exact ⟨n + 0, t, t0, t1, lsemFuelMemF_of_steps _ _ hst hhalt 0, hres, hlvm, harr, h1, h2⟩

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix (CtlOK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenNode (abiReg abiBase)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (frameNames frameMark)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW (baseR)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (fuseMulHiRM KeptN
  fuseMulHi_lsemFuelMemF_pre_calls)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHiAbi (e64_of_abiEntryM)

/-- **The reference of a calling body at a procedure table.** Let `p` be a program of
    `RegionExportable` with the export `r0` and its webs
    `r = regionWebs ex r0 (calleeAA (some c)) (calleeAO (some c))`, and let the code and
    returned operands of `r` pass `regionCoB`
    at the callee `c` and the function name `fn` against the printed body `body`, with the
    parts `d` of the reference. Let the table `T` agree with the call environment `Ec`
    (`ProcsAgree`), hold summaries of their declared result kinds (`ProcSummary.Kinded`)
    whose array positions and result lengths are those of `c` (`calleeAA`, `calleeAO`), and
    give the symbol of `c` a summary. From every entry state `sa` satisfying `σ.Regions`, at every valuation
    `V` that `σ` reads off `sa` at which `p` denotes `v` in `Ec` at some fuel:

    * the reference `d.ref` halts at `x86Isa.withProcs T` from the entry state `entryV` at
      the frame map `frameE body sa` and the map `unren d.ps`, in a state `u`;
    * the printed body passes the checks `calleeBodyB` of a calling body against `d.ref`;
    * the entry facts of `renImage_entry_nil` hold: the frame and slot maps are separated,
      the entry state is related by `ImageAddrCall.ImgRelF` to `entryA σ sa` at every list
      of names, the machine state after the prologue is related to `entryA σ sa` by
      `ACorr`, the address state is at position `0`, and the entry registers satisfy the
      bounds `boundFacts σ nm`;
    * every machine state `sa'` whose words at the entry base of each array parameter `A`
      are the array of `renOf d.ps A` in `u`, and whose machine register of each observed
      general-purpose name without a frame word holds the value of that name in `u`, reads
      back the source value of the result through `σ`.

    The run of the exported code at the table (`regionVirt_run_procs`) is carried to the
    exported code on the common names of `c` by `LprogCallCut.run_onCommonNames`, the
    copies of the parameter registers are put in front by
    `JasminLsemMemFlagPrefix.lsemFuelMemF_prepend_calls`, and the stages
    `regionRef_run_calls`, `regCo_run_calls` and `selfNop_run_calls` follow, and, when the
    code has a site of the multiplication fusion, `fuseMulHi_lsemFuelMemF_pre_calls` carries
    the run to the fused reference. These are the
    reference run of `calleeBody_imgRun_at` and the entry hypotheses of
    `CheckedIsaCall.haltsC_of_linkedChecksKW`. -/
theorem regionCo_bytes_callee {σ : AbiLayout} {nm : String → String} {fn : String}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) {r0 r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r0) {ex : List String} {c : CalleeData}
    (hw : regionWebs ex r0 (calleeAA (some c)) (calleeAO (some c)) = r) {body : Lcmd}
    {cert : List (String × String)}
    (hg : regionCoB σ nm body t r.code r.res cert (some (CalleeTab.one c)) fn = true) {d : CoParts}
    (hd : regionCoParts σ nm body t (calleeCode (some c) r.code) r.res cert
      (some (CalleeTab.one c)) = d)
    {Ec : CallEnv jasminDialect} {T : ProcTable} (hT : ProcsAgree Ec T)
    (hk : ∀ f pr, T f = some pr → pr.Kinded)
    (haa : LprogIsa.Isa.procArrArgs T = calleeAA (some c))
    (hao : LprogIsa.Isa.procOut T = calleeAO (some c))
    {pr : ProcSummary} (hc : T c.name = some pr)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denoteAt Ec fuel V = some v) :
    ∃ (k : Nat) (u : LstateMF),
      (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn d.ref) k
        { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn },
          zf := false } = some u
      ∧ calleeBodyB σ nm c (slotRen (slotArrOf σ nm) (renOf d.ps)) d.outs body d.ref fn = true
      ∧ X86Backend.ImageAddrSim.ImgSep (frameE body sa) (slotRen (slotArrOf σ nm) (renOf d.ps))
        (baseR σ sa d.ps) (X86Backend.DecodePrintedCFG.frameRsp body sa)
      ∧ (∀ X : List String, X86Backend.ImageAddrCall.ImgRelF (frameE body sa)
        (slotRen (slotArrOf σ nm) (renOf d.ps)) (baseR σ sa d.ps)
        (cellBody (slotRen (slotArrOf σ nm) (renOf d.ps)) body) X
        { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn }, zf := false }
        (entryA σ sa))
      ∧ X86Backend.DecodePrintedAddr.ACorr (X86Backend.DecodePrintedCFG.frameRsp body sa)
        (Ascent.AddrMem.evalInstrA sa (X86Backend.PhysAbiShape.leaFrame
          (-(Int.ofNat (X86Backend.LprogBytesDecode.Params.ofBody body).frame))))
        (entryA σ sa)
      ∧ (entryA σ sa).reg.lpc = 0
      ∧ (∀ f ∈ boundFacts σ nm, f.holds (entryV σ (frameE body sa) sa (unren d.ps)).reg.lvm
          (entryV σ (frameE body sa) sa (unren d.ps)).larr)
      ∧ ∀ sa' : AState,
        (∀ q A n, slotArrOf σ nm q = some (A, n) →
          ∃ arr, u.prog.base.getArr (renOf d.ps A) 64 n = some arr
            ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa A) j) = arr ⟨j, hj⟩) →
        (∀ y ∈ d.outs, gpOk y = true → (frameMark (frameNames body) y).isNone = true →
          u.prog.base.reg.getW y 64 = some (sa'.regs (phys y))) →
        σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)) := by
  simp only [regionCoB, regionCopy_some_callee, regionOut, Option.all, Bool.and_eq_true,
    CalleeTab.common_one, CalleeTab.names_one, LprogCallCut.commonCallsT?_one,
    LprogCallCut.commonFreshT_one, calleeCodeT_one] at hg
  rw [hd] at hg
  obtain ⟨⟨⟨⟨⟨⟨-, hcs⟩, hfresh⟩, hcls0⟩, hco⟩, hfix⟩,
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcb, hce⟩, hren⟩, hobs⟩, hret⟩, hres⟩, hmg⟩, hnop⟩, hsite⟩, -⟩, himg⟩⟩ := hg
  obtain ⟨codeC, hcode⟩ := Option.isSome_iff_exists.mp hcs
  have hcc : calleeCode (some c) r.code = codeC := by
    simp only [calleeCode, hcode, Option.getD_some]
  rw [hcc] at hd hcls0 hco hfix hren hobs hret hres
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
  have hle : x86Isa.StepLe (x86Isa.withProcs T) :=
    x86Isa.withProcs_stepLe (x86Isa_refusesProcs T)
  have hcl : (x86Isa.withProcs T).CallLocal x86Isa (calleeAA (some c)) (calleeAO (some c)) := by
    rw [← haa, ← hao]
    exact x86Isa.withProcs_callLocal T hk
  have hpra : pr.arrArgs = c.arrArgs := by
    have h1 := congrFun haa c.name
    simp [LprogIsa.Isa.procArrArgs, hc, calleeAA] at h1
    exact h1
  have hpro : c.shape.out = false → pr.RetWord := by
    intro ho
    have h1 := congrFun hao c.name
    cases hcr : c.res with
    | reg r => simpa [LprogIsa.Isa.procOut, hc, calleeAO, hcr, ProcSummary.RetWord] using h1
    | out n => simp [CalleeData.shape, hcr] at ho
  have hdaa : d.aa = calleeAA (some c) := by rw [← hd]; rfl
  have hdao : d.ao = calleeAO (some c) := by rw [← hd]; rfl
  -- The run of the exported code with the result copy.
  have hres0 : r0.res = r.res := by rw [← hw]; simp
  obtain ⟨k0, tv, t0, t1v, hrunV, hag, hlvm, harrO, hnone, hmv⟩ := regionVirt_run_procs σ nm fn
    hp hr ex (regionRet σ nm t r.res) E (unren d.ps) (fun j hj => (RF.unr j hj).1) sa V hV hT
    hcl fuel v hv
  rw [hw] at hrunV
  rw [hres0] at hag
  have h0 : (entryV σ (frameE body sa) sa (unren d.ps)).lpc = 0 := rfl
  -- The rewriting onto the common names of the callee.
  have hB : LprogCallCut.commonCalls? c.shape c.name c.args c.resReg
      (regionCoCode σ nm t r.code r.res) = some (regionCoCode σ nm t codeC r.res) := by
    simp only [regionCoCode, commonCalls?_append, hcode, commonCalls?_movesOf, Option.bind_some,
      Option.map_some]
  obtain ⟨f1, t1, hrun1, hrel1⟩ := LprogCallCut.run_onCommonNames hc
    (fun i hi => by rw [hpra]; exact hi) hpro
    hB hfresh h0 hrunV
  -- The copies of the parameter registers in front.
  have hclsC : ∀ i ∈ regionCoCode σ nm t codeC r.res, CtlOK i := fun i hi =>
    (clsB_ctl_cond (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hcls0 i hi)).1
      (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hcls0 i hi)).2).1
  have hlopA : ∀ i ∈ argBind σ nm, IsLopn i := movesOf_isLopn _
  obtain ⟨t2, hrun2, hsh2⟩ := JasminLsemMemFlagPrefix.lsemFuelMemF_prepend_calls hle
    hcl fn (argBind σ nm) (regionCoCode σ nm t codeC r.res) hlopA hclsC _ _ false
    false h0 (argBind_entryV E.argF E.argG hSrc false) f1 t1 hrun1
  -- The coalesced and renamed reference.
  obtain ⟨k1, s1, hrun3, harrs, hregs'⟩ := regionRef_run_calls hle hcl E sa hSrc hclsC hco
    (fun x hx => by simpa using List.all_eq_true.mp hfix x hx) RF _ t2 hrun2
  have hnopE : d.nop = selfNop d.pre.length
      (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length) (d.pre ++ d.merged) := by
    rw [← hd]; rfl
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
  have hobsE : d.obs = (regionCoObs t r.res).map fun A =>
      renOf d.ps (chainAliasO (calleeOuts (some c))
        (regionCoCode σ nm t codeC r.res) A) := by
    rw [← hd]; rfl
  have hpre : d.pre = argBind σ nm ++ movesOf d.ps := by rw [← hd]; rfl
  have hren' : d.ren
      = (regionCoBody σ nm t codeC r.res (some (CalleeTab.one c))).map (renRM (renOf d.ps)) := by
    rw [← hd]; rfl
  have hmerged : d.merged = d.ren.map (renRM (renOf d.tau)) := by rw [← hd]; rfl
  have houts : d.outs = (regionRet σ nm t r.res).toList.map Prod.snd := by rw [← hd]; rfl
  have harrsM : ∀ A ∈ regionCoObs t r.res,
      renOf d.ps (chainAliasO (calleeOuts (some c)) (regionCoCode σ nm t codeC r.res) A)
          ∈ d.arrs
        ∧ renOf d.ps (chainAliasO (calleeOuts (some c))
          (regionCoCode σ nm t codeC r.res) A) ∈ d.arrsM := by
    intro A hA
    rw [← hd]
    exact ⟨List.mem_append_right _ (List.mem_map.mpr ⟨A, hA, rfl⟩),
      List.mem_append_right _ (List.mem_map.mpr ⟨A, hA, rfl⟩)⟩
  have hlop : ∀ i ∈ d.pre, IsLopn i := fun i hi => by
    rw [hpre] at hi
    exact (List.mem_append.mp hi).elim (movesOf_isLopn _ i) (movesOf_isLopn _ i)
  have hagP : ∀ i ∈ d.pre, ∀ (Q : JasminLsemMemLoop.LprogM) (s : LstateMF),
      (x86Isa.withProcs T).step Q i s = x86Isa.step Q i s := fun i hi => by
    rw [hpre] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact X86Backend.ImageAddrSrcFuel.movesOf_agree hle hcl _ i hi
    · exact X86Backend.ImageAddrSrcFuel.movesOf_agree hle hcl _ i hi
  have h : (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn (d.pre ++ d.ren)) k1
      { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn }, zf := false }
        = some s1 := by
    rw [hpre, hren']
    exact hrun3
  -- The register merge.
  have hrun : ∃ s' : LstateMF,
      (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn (d.pre ++ d.merged)) k1
        { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn },
          zf := false } = some s'
      ∧ (∀ a ∈ d.arrs, s'.prog.base.larr a = s1.prog.base.larr a)
      ∧ ∀ y ∈ d.outs, s'.prog.base.reg.lvm y = s1.prog.base.reg.lvm y := by
    simp only [regionMergeB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hmg
    rcases hmg with hnil | ⟨hck, hout⟩
    · refine ⟨s1, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
      rw [hmerged, hnil, map_renRM_renOf_nil]
      exact h
    · rw [hdaa, hdao] at hck
      obtain ⟨s', hs', hrg, har⟩ := regCo_run_calls hle hcl hlop hagP hck _ rfl false k1 s1 h
      rw [← hmerged] at hs'
      refine ⟨s', hs', har, fun y hy => ?_⟩
      have hy' := List.all_eq_true.mp hout y hy
      simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, beq_iff_eq] at hy'
      have := hrg y hy'.1
      rwa [hy'.2] at this
  obtain ⟨s', hs', har, hrg⟩ := hrun
  -- The array self-moves.
  simp only [regionNopB, Bool.and_eq_true] at hnop
  obtain ⟨hck, hout⟩ := hnop
  rw [hdaa, hdao] at hck
  obtain ⟨u0, hu0, hrg2, har2⟩ := selfNop_run_calls hle hcl hlop hagP hck _ rfl false k1 s' hs'
  rw [← hnopE] at hu0
  have hA0 : ∀ A ∈ regionCoObs t r.res, ∀ w n,
      u0.prog.base.getArr (renOf d.ps (chainAliasO (calleeOuts (some c))
          (regionCoCode σ nm t codeC r.res) A)) w n
        = s1.prog.base.getArr (renOf d.ps (chainAliasO (calleeOuts (some c))
          (regionCoCode σ nm t codeC r.res) A)) w n := by
    intro A hA w n
    unfold LstateM.getArr
    rw [har2 _ (harrsM A hA).2, har _ (harrsM A hA).1]
  have hY0 : ∀ y ∈ d.outs, u0.prog.base.reg.lvm y = s1.prog.base.reg.lvm y := by
    intro y hy
    have hy' := List.all_eq_true.mp hout y hy
    rw [List.contains_eq_mem, decide_eq_true_eq] at hy'
    rw [hrg2 y hy', hrg y hy]
  -- The multiplication fusion.
  obtain ⟨kF, u, hu, hA2, hY2⟩ : ∃ (kF : Nat) (u : LstateMF),
      (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn d.ref) kF
        { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn },
          zf := false } = some u
      ∧ (∀ A ∈ regionCoObs t r.res, ∀ w n,
        u.prog.base.getArr (renOf d.ps (chainAliasO (calleeOuts (some c))
            (regionCoCode σ nm t codeC r.res) A)) w n
          = s1.prog.base.getArr (renOf d.ps (chainAliasO (calleeOuts (some c))
            (regionCoCode σ nm t codeC r.res) A)) w n)
      ∧ ∀ y ∈ d.outs, u.prog.base.reg.lvm y = s1.prog.base.reg.lvm y := by
    rw [hrefF, hfusedE]
    cases hS : d.sites with
    | false => exact ⟨k1, u0, hu0, hA0, hY0⟩
    | true =>
        simp only [regionSitesB, hS, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hsite
        obtain ⟨⟨hfuse, hk1⟩, hk2⟩ := hsite
        rw [hsplit] at hu0
        have habi := entryV_abiEntry (sa := sa) (un := unren d.ps) E.argF E.argG
          fun j hj => (RF.unr j hj).1
        obtain ⟨k', u', -, hrun', hag, -, -⟩ := fuseMulHi_lsemFuelMemF_pre_calls hle
          hcl hfuse fn _ u0 rfl
          (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact e64_of_abiEntryM habi x hx
            · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
              exact congrArg (·.1) (entryV_srcOf (un := unren d.ps) hSrc ha)) k1 hu0
        refine ⟨k', u', hrun', fun A hA w n => ?_, fun y hy => ?_⟩
        · have hkept : KeptN (renOf d.ps (chainAliasO (calleeOuts (some c))
              (regionCoCode σ nm t codeC r.res) A)) := by
            have hm : renOf d.ps (chainAliasO (calleeOuts (some c))
                (regionCoCode σ nm t codeC r.res) A) ∈ d.obs := by
              rw [hobsE]
              exact List.mem_map.mpr ⟨A, hA, rfl⟩
            simpa [KeptN] using List.all_eq_true.mp hk1 _ hm
          rw [← hA0 A hA w n]
          unfold LstateM.getArr
          rw [hag.arr _ hkept]
        · rw [← hY0 y hy]
          exact hag.reg y (by simpa [KeptN] using List.all_eq_true.mp hk2 y hy)
  -- The states before the reference: the copies in front and the common names.
  obtain ⟨L', hL', ht1⟩ := hrel1
  have hArr : ∀ A w n, t2.prog.base.getArr A w n = tv.prog.base.getArr A w n := by
    intro A w n
    unfold LstateM.getArr
    rw [hsh2.base, ht1]
    rfl
  have hLv : ∀ y, y ∉ c.resReg :: c.args → t2.prog.base.reg.lvm y = tv.prog.base.reg.lvm y := by
    intro y hy
    rw [hsh2.base, ht1]
    exact hL' y hy
  obtain ⟨hsep, -, hacorr, hpc0, hbnd⟩ := renImage_entry_nil himg hU sa hreg fn []
  have hl : body.getLast?.any (fun r => X86Backend.DecodePrinted.isRetB r.li_i) = true := by
    simp only [renImageB, calleeImgBT, X86Backend.ImageAddrCallW.printedAddrCWB,
      Bool.and_eq_true] at himg
    grind
  refine ⟨kF, u, hu, calleeBodyB_of_one hcb hl, hsep,
    fun X => (renImage_entry_nil himg hU sa hreg fn X).2.1, hacorr,
    hpc0, hbnd, fun sa' hcellsB hregsB => ?_⟩
  cases t with
  | stackArr w m =>
      obtain rfl : tv = t0 := hnone rfl
      obtain ⟨op, hop, harr⟩ := hag.decodeArrM_single
      replace harr := (getArr_of_larr_eq _ _
        (harrO _ (by simp [regionWebsObs, hres0, hop]))).trans harr
      have hmem : operandName op ∈ regionCoObs (.stackArr w m) r.res := by
        simp [regionCoObs, hop]
      have hN := List.all_eq_true.mp hobs _ hmem
      rw [List.contains_eq_mem, decide_eq_true_eq] at hN
      rw [hop] at hres
      simp only [regionResultB, List.map] at hres
      split at hres
      · rename_i RA k' op' hσ hop'
        obtain rfl := (List.cons.inj hop').1
        simp only [Bool.and_eq_true, beq_iff_eq] at hres
        obtain ⟨⟨⟨rfl, hk⟩, hA⟩, hslot⟩ := hres
        obtain ⟨arr, harr', hw⟩ := hcellsB _ _ _ hslot
        have hgo := (hA2 _ hmem 64 m).trans ((harrs _ hmem hN 64 m).trans (hArr _ 64 m))
        rw [hop] at hgo
        have h2 : tv.prog.base.getArr (operandName op) 64 m = some _ := harr
        have harr2 : u.prog.base.getArr (renOf d.ps (chainAliasO (calleeOuts (some c))
            (regionCoCode σ nm (.stackArr 64 m) codeC [op]) (operandName op))) 64 m = some arr :=
          harr'
        rw [hgo, h2] at harr2
        obtain rfl := Option.some.inj harr2
        have hbase : abiBase (abiReg σ) sa
            (chainAliasO (calleeOuts (some c))
              (regionCoCode σ nm (.stackArr 64 m) codeC [op]) (operandName op))
              = sa.regs RA := by
          have hA' : abiReg σ (chainAliasO (calleeOuts (some c))
              (regionCoCode σ nm (.stackArr 64 m) codeC [op]) (operandName op)) = some RA := hA
          simp [abiBase, hA']
        exact resultOf_words (σ := σ) (sa' := sa') (by rw [hσ, hk])
          fun j hj => by rw [← hbase]; exact hw j hj
      · cases hres
  | reg w =>
      obtain ⟨op, hop, hval⟩ := hag.getW_single
      replace hval := (show t0.prog.base.reg.getW (operandName op) w
          = t1v.prog.base.reg.getW (operandName op) w by
        unfold LstateN.getW
        rw [hlvm]).trans hval
      rw [hop] at hres
      simp only [regionResultB, List.map] at hres
      split at hres
      · rename_i RA op' hσ hop'
        simp only [Bool.and_eq_true, beq_iff_eq] at hres
        obtain ⟨⟨⟨rfl, hgp⟩, hph⟩, hfr⟩ := hres
        have hret' : regionRet σ nm (JasminTy.reg 64) r.res
            = some (operandName op, nm RA) := by
          simp only [regionRet, hσ, hop]
        rw [hret'] at hret
        simp only [Option.toList_some, List.all_cons, List.all_nil, Bool.and_true,
          Bool.and_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hret
        have houtR : nm RA ∈ d.outs := by
          rw [houts, hret']
          simp
        have hfreshRA : nm RA ∉ c.resReg :: c.args := by
          simp only [LprogCallCut.commonFreshB, Bool.and_eq_true, List.all_eq_true] at hfresh
          obtain ⟨i0, hi0, hn0⟩ : ∃ i0 ∈ movesOf [(operandName op, nm RA)],
              nm RA ∈ LprogCallCut.instrNames i0.1 :=
            ⟨_, List.mem_singleton_self _, by
              simp [JasminLsemExportLower.movWire, LprogCallCut.instrNames,
                LprogCallCut.opNames]⟩
          have hi : i0 ∈ regionCoCode σ nm (.reg 64) r.code r.res := by
            simp only [regionCoCode, hret', Option.toList_some]
            exact List.mem_append_right _ hi0
          have := hfresh.1.2 _ hi (nm RA) hn0
          simp only [Bool.not_eq_true', List.contains_eq_mem,
            decide_eq_false_iff_not, bne_iff_ne, ne_eq] at this
          simp only [List.mem_cons, not_or]
          exact ⟨this.2, this.1⟩
        have hlvRA : u.prog.base.reg.lvm (nm RA) = t0.prog.base.reg.lvm (operandName op) := by
          have h3 := hregs' (nm RA) hret.1
          rw [hret.2] at h3
          rw [hY2 _ houtR, h3, hLv _ hfreshRA, hmv _ _ hret']
        have hR := hregsB (nm RA) houtR hgp hfr
        unfold LstateN.getW at hR hval
        rw [hlvRA, hval, hph] at hR
        unfold AbiLayout.ResultOf
        rw [hσ]
        simp only [Haxc.ResultKind.read, ← Option.some.inj hR]
        rfl
      · cases hres
  | _ => simp [regionResultB] at hres


/-- **The reference of a calling body at a table of callees.** `regionCo_bytes_callee` at a
    table `T` of linked functions and a word-array result: let `p` be a program of
    `RegionExportable` with the export `r0` and its webs
    `r = regionWebs ex r0 (calleeAAT (some T)) (calleeAOT (some T))`, and let the code and
    returned operands of `r` pass `regionCoB` at `T` and the function name `fn` against the
    printed body `body`, with the parts `d` of the reference. Let the procedure table `PT`
    agree with the call environment `Ec`, hold summaries of their declared result kinds whose
    array positions and result lengths are those of `T` (`calleeAAT`, `calleeAOT`), and give
    each symbol of `T` a summary. Then the reference halts at `x86Isa.withProcs PT`, the
    printed body passes the checks `calleeBodyBT` at `T`, the entry facts of
    `renImage_entry_nil` hold, and every machine state whose words at the entry base of each
    array parameter `A` are the array of `renOf d.ps A` at the end of the reference reads
    back the source value of the result through `σ`. The rewriting onto common names is
    `LprogCallCut.run_onCommonNamesT` at the common names `CalleeTab.common` of `T`. -/
theorem regionCo_bytes_tab {σ : AbiLayout} {nm : String → String} {fn : String}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : RegionExportable p) {r0 r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 = some r0) (ht : ∃ w m, t = .stackArr w m)
    {ex : List String} {T : CalleeTab}
    (hw : regionWebs ex r0 (calleeAAT (some T)) (calleeAOT (some T)) = r) {body : Lcmd}
    {cert : List (String × String)}
    (hg : regionCoB σ nm body t r.code r.res cert (some T) fn = true) {d : CoParts}
    (hd : regionCoParts σ nm body t (calleeCodeT (some T) r.code) r.res cert (some T) = d)
    {Ec : CallEnv jasminDialect} {PT : ProcTable} (hT : ProcsAgree Ec PT)
    (hk : ∀ f pr, PT f = some pr → pr.Kinded)
    (haa : LprogIsa.Isa.procArrArgs PT = calleeAAT (some T))
    (hao : LprogIsa.Isa.procOut PT = calleeAOT (some T))
    (hc : ∀ f c, T.lookup f = some c → (PT f).isSome)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denoteAt Ec fuel V = some v) :
    ∃ (k : Nat) (u : LstateMF),
      (x86Isa.withProcs PT).lsemFuelMemF (singletonProgM fn d.ref) k
        { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn },
          zf := false } = some u
      ∧ calleeBodyBT σ nm T (slotRen (slotArrOf σ nm) (renOf d.ps)) d.outs body d.ref fn = true
      ∧ X86Backend.ImageAddrSim.ImgSep (frameE body sa) (slotRen (slotArrOf σ nm) (renOf d.ps))
        (baseR σ sa d.ps) (X86Backend.DecodePrintedCFG.frameRsp body sa)
      ∧ (∀ X : List String, X86Backend.ImageAddrCall.ImgRelF (frameE body sa)
        (slotRen (slotArrOf σ nm) (renOf d.ps)) (baseR σ sa d.ps)
        (cellBody (slotRen (slotArrOf σ nm) (renOf d.ps)) body) X
        { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn }, zf := false }
        (entryA σ sa))
      ∧ X86Backend.DecodePrintedAddr.ACorr (X86Backend.DecodePrintedCFG.frameRsp body sa)
        (Ascent.AddrMem.evalInstrA sa (X86Backend.PhysAbiShape.leaFrame
          (-(Int.ofNat (X86Backend.LprogBytesDecode.Params.ofBody body).frame))))
        (entryA σ sa)
      ∧ (entryA σ sa).reg.lpc = 0
      ∧ (∀ f ∈ boundFacts σ nm, f.holds (entryV σ (frameE body sa) sa (unren d.ps)).reg.lvm
          (entryV σ (frameE body sa) sa (unren d.ps)).larr)
      ∧ ∀ sa' : AState,
        (∀ q A n, slotArrOf σ nm q = some (A, n) →
          ∃ arr, u.prog.base.getArr (renOf d.ps A) 64 n = some arr
            ∧ ∀ j (hj : j < n), read64 sa'.mem (cellAt (abiBase (abiReg σ) sa A) j) = arr ⟨j, hj⟩) →
        (∀ y ∈ d.outs, gpOk y = true → (frameMark (frameNames body) y).isNone = true →
          u.prog.base.reg.getW y 64 = some (sa'.regs (phys y))) →
        σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v)) := by
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
  have hle : x86Isa.StepLe (x86Isa.withProcs PT) :=
    x86Isa.withProcs_stepLe (x86Isa_refusesProcs PT)
  have hcl : (x86Isa.withProcs PT).CallLocal x86Isa (calleeAAT (some T)) (calleeAOT (some T)) := by
    rw [← haa, ← hao]
    exact x86Isa.withProcs_callLocal PT hk
  -- The summaries of the symbols of the table meet the shapes of their calls.
  have hTab : ∀ g sh args res, T.common g = some (sh, args, res) → ∃ pr, PT g = some pr ∧
      (∀ i, sh.arrArgs i = none → pr.arrArgs i = none) ∧ (sh.out = false → pr.RetWord) := by
    intro g sh args res hg'
    obtain ⟨c, hc', he⟩ := Option.map_eq_some_iff.mp hg'
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.mp (hc g c hc')
    refine ⟨pr, hpr, fun i hi => ?_, fun ho => ?_⟩
    · have h1 := congrFun haa g
      simp only [LprogIsa.Isa.procArrArgs, hpr, calleeAAT, Option.bind_some, hc'] at h1
      rw [h1]
      exact hi
    · have h1 := congrFun hao g
      cases hcr : c.res with
      | reg r =>
          simpa [LprogIsa.Isa.procOut, hpr, calleeAOT, hc', hcr, ProcSummary.RetWord] using h1
      | out n => simp [CalleeData.shape, hcr] at ho
  have hnames : ∀ g e, T.common g = some e → g ∈ T.names := by
    intro g e hg'
    obtain ⟨c, hc', -⟩ := Option.map_eq_some_iff.mp hg'
    have h1 := congrFun T.lookup_isSome g
    simp only [hc', Option.isSome_some] at h1
    simpa using h1.symm
  have hdaa : d.aa = calleeAAT (some T) := by rw [← hd]; rfl
  have hdao : d.ao = calleeAOT (some T) := by rw [← hd]; rfl
  -- The run of the exported code with the result copy.
  have hres0 : r0.res = r.res := by rw [← hw]; simp
  obtain ⟨k0, tv, t0, _, hrunV, hag, -, harrO, hnone, -⟩ := regionVirt_run_procs σ nm fn
    hp hr ex (regionRet σ nm t r.res) E (unren d.ps) (fun j hj => (RF.unr j hj).1) sa V hV hT
    hcl fuel v hv
  rw [hw] at hrunV
  rw [hres0] at hag
  have h0 : (entryV σ (frameE body sa) sa (unren d.ps)).lpc = 0 := rfl
  -- The rewriting onto the common names of the callee.
  have hB : LprogCallCut.commonCallsT? T.common (regionCoCode σ nm t r.code r.res)
      = some (regionCoCode σ nm t codeC r.res) := by
    simp only [regionCoCode, commonCallsT?_append, hcode, commonCallsT?_movesOf,
      Option.bind_some, Option.map_some]
  obtain ⟨f1, t1, hrun1, hrel1⟩ := LprogCallCut.run_onCommonNamesT hTab hnames hB hfresh h0
    hrunV
  -- The copies of the parameter registers in front.
  have hclsC : ∀ i ∈ regionCoCode σ nm t codeC r.res, CtlOK i := fun i hi =>
    (clsB_ctl_cond (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hcls0 i hi)).1
      (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hcls0 i hi)).2).1
  have hlopA : ∀ i ∈ argBind σ nm, IsLopn i := movesOf_isLopn _
  obtain ⟨t2, hrun2, hsh2⟩ := JasminLsemMemFlagPrefix.lsemFuelMemF_prepend_calls hle
    hcl fn (argBind σ nm) (regionCoCode σ nm t codeC r.res) hlopA hclsC _ _ false
    false h0 (argBind_entryV E.argF E.argG hSrc false) f1 t1 hrun1
  -- The coalesced and renamed reference.
  obtain ⟨k1, s1, hrun3, harrs, -⟩ := regionRef_run_calls hle hcl E sa hSrc hclsC hco
    (fun x hx => by simpa using List.all_eq_true.mp hfix x hx) RF _ t2 hrun2
  have hnopE : d.nop = selfNop d.pre.length
      (liveAt (tabAt d.liveM) (d.pre ++ d.merged).length) (d.pre ++ d.merged) := by
    rw [← hd]; rfl
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
  have hobsE : d.obs = (regionCoObs t r.res).map fun A =>
      renOf d.ps (chainAliasO (calleeOutsT (some T))
        (regionCoCode σ nm t codeC r.res) A) := by
    rw [← hd]; rfl
  have hpre : d.pre = argBind σ nm ++ movesOf d.ps := by rw [← hd]; rfl
  have hren' : d.ren
      = (regionCoBody σ nm t codeC r.res (some T)).map (renRM (renOf d.ps)) := by
    rw [← hd]; rfl
  have hmerged : d.merged = d.ren.map (renRM (renOf d.tau)) := by rw [← hd]; rfl
  have harrsM : ∀ A ∈ regionCoObs t r.res,
      renOf d.ps (chainAliasO (calleeOutsT (some T)) (regionCoCode σ nm t codeC r.res) A)
          ∈ d.arrs
        ∧ renOf d.ps (chainAliasO (calleeOutsT (some T))
          (regionCoCode σ nm t codeC r.res) A) ∈ d.arrsM := by
    intro A hA
    rw [← hd]
    exact ⟨List.mem_append_right _ (List.mem_map.mpr ⟨A, hA, rfl⟩),
      List.mem_append_right _ (List.mem_map.mpr ⟨A, hA, rfl⟩)⟩
  have hlop : ∀ i ∈ d.pre, IsLopn i := fun i hi => by
    rw [hpre] at hi
    exact (List.mem_append.mp hi).elim (movesOf_isLopn _ i) (movesOf_isLopn _ i)
  have hagP : ∀ i ∈ d.pre, ∀ (Q : JasminLsemMemLoop.LprogM) (s : LstateMF),
      (x86Isa.withProcs PT).step Q i s = x86Isa.step Q i s := fun i hi => by
    rw [hpre] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact X86Backend.ImageAddrSrcFuel.movesOf_agree hle hcl _ i hi
    · exact X86Backend.ImageAddrSrcFuel.movesOf_agree hle hcl _ i hi
  have h : (x86Isa.withProcs PT).lsemFuelMemF (singletonProgM fn (d.pre ++ d.ren)) k1
      { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn }, zf := false }
        = some s1 := by
    rw [hpre, hren']
    exact hrun3
  -- The register merge.
  have hrun : ∃ s' : LstateMF,
      (x86Isa.withProcs PT).lsemFuelMemF (singletonProgM fn (d.pre ++ d.merged)) k1
        { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn },
          zf := false } = some s'
      ∧ (∀ a ∈ d.arrs, s'.prog.base.larr a = s1.prog.base.larr a)
      ∧ ∀ y ∈ d.outs, s'.prog.base.reg.lvm y = s1.prog.base.reg.lvm y := by
    simp only [regionMergeB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hmg
    rcases hmg with hnil | ⟨hck, hout⟩
    · refine ⟨s1, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
      rw [hmerged, hnil, map_renRM_renOf_nil]
      exact h
    · rw [hdaa, hdao] at hck
      obtain ⟨s', hs', hrg, har⟩ := regCo_run_calls hle hcl hlop hagP hck _ rfl false k1 s1 h
      rw [← hmerged] at hs'
      refine ⟨s', hs', har, fun y hy => ?_⟩
      have hy' := List.all_eq_true.mp hout y hy
      simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, beq_iff_eq] at hy'
      have := hrg y hy'.1
      rwa [hy'.2] at this
  obtain ⟨s', hs', har, hrg⟩ := hrun
  -- The array self-moves.
  simp only [regionNopB, Bool.and_eq_true] at hnop
  obtain ⟨hck, hout⟩ := hnop
  rw [hdaa, hdao] at hck
  obtain ⟨u0, hu0, hrg2, har2⟩ := selfNop_run_calls hle hcl hlop hagP hck _ rfl false k1 s' hs'
  rw [← hnopE] at hu0
  have hA0 : ∀ A ∈ regionCoObs t r.res, ∀ w n,
      u0.prog.base.getArr (renOf d.ps (chainAliasO (calleeOutsT (some T))
          (regionCoCode σ nm t codeC r.res) A)) w n
        = s1.prog.base.getArr (renOf d.ps (chainAliasO (calleeOutsT (some T))
          (regionCoCode σ nm t codeC r.res) A)) w n := by
    intro A hA w n
    unfold LstateM.getArr
    rw [har2 _ (harrsM A hA).2, har _ (harrsM A hA).1]
  have hY0 : ∀ y ∈ d.outs, u0.prog.base.reg.lvm y = s1.prog.base.reg.lvm y := by
    intro y hy
    have hy' := List.all_eq_true.mp hout y hy
    rw [List.contains_eq_mem, decide_eq_true_eq] at hy'
    rw [hrg2 y hy', hrg y hy]
  -- The multiplication fusion.
  obtain ⟨kF, u, hu, hA2, -⟩ : ∃ (kF : Nat) (u : LstateMF),
      (x86Isa.withProcs PT).lsemFuelMemF (singletonProgM fn d.ref) kF
        { prog := { base := entryV σ (frameE body sa) sa (unren d.ps), lfn := fn },
          zf := false } = some u
      ∧ (∀ A ∈ regionCoObs t r.res, ∀ w n,
        u.prog.base.getArr (renOf d.ps (chainAliasO (calleeOutsT (some T))
            (regionCoCode σ nm t codeC r.res) A)) w n
          = s1.prog.base.getArr (renOf d.ps (chainAliasO (calleeOutsT (some T))
            (regionCoCode σ nm t codeC r.res) A)) w n)
      ∧ ∀ y ∈ d.outs, u.prog.base.reg.lvm y = s1.prog.base.reg.lvm y := by
    rw [hrefF, hfusedE]
    cases hS : d.sites with
    | false => exact ⟨k1, u0, hu0, hA0, hY0⟩
    | true =>
        simp only [regionSitesB, hS, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hsite
        obtain ⟨⟨hfuse, hk1⟩, hk2⟩ := hsite
        rw [hsplit] at hu0
        have habi := entryV_abiEntry (sa := sa) (un := unren d.ps) E.argF E.argG
          fun j hj => (RF.unr j hj).1
        obtain ⟨k', u', -, hrun', hag, -, -⟩ := fuseMulHi_lsemFuelMemF_pre_calls hle
          hcl hfuse fn _ u0 rfl
          (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact e64_of_abiEntryM habi x hx
            · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
              exact congrArg (·.1) (entryV_srcOf (un := unren d.ps) hSrc ha)) k1 hu0
        refine ⟨k', u', hrun', fun A hA w n => ?_, fun y hy => ?_⟩
        · have hkept : KeptN (renOf d.ps (chainAliasO (calleeOutsT (some T))
              (regionCoCode σ nm t codeC r.res) A)) := by
            have hm : renOf d.ps (chainAliasO (calleeOutsT (some T))
                (regionCoCode σ nm t codeC r.res) A) ∈ d.obs := by
              rw [hobsE]
              exact List.mem_map.mpr ⟨A, hA, rfl⟩
            simpa [KeptN] using List.all_eq_true.mp hk1 _ hm
          rw [← hA0 A hA w n]
          unfold LstateM.getArr
          rw [hag.arr _ hkept]
        · rw [← hY0 y hy]
          exact hag.reg y (by simpa [KeptN] using List.all_eq_true.mp hk2 y hy)
  -- The states before the reference: the copies in front and the common names.
  obtain ⟨_, -, ht1⟩ := hrel1
  have hArr : ∀ A w n, t2.prog.base.getArr A w n = tv.prog.base.getArr A w n := by
    intro A w n
    unfold LstateM.getArr
    rw [hsh2.base, ht1]
    rfl
  obtain ⟨hsep, -, hacorr, hpc0, hbnd⟩ := renImage_entry_nil himg hU sa hreg fn []
  refine ⟨kF, u, hu, hcb, hsep,
    fun X => (renImage_entry_nil himg hU sa hreg fn X).2.1, hacorr,
    hpc0, hbnd, fun sa' hcellsB _ => ?_⟩
  obtain ⟨w, m, rfl⟩ := ht
  obtain rfl : tv = t0 := hnone rfl
  obtain ⟨op, hop, harr⟩ := hag.decodeArrM_single
  replace harr := (getArr_of_larr_eq _ _
    (harrO _ (by simp [regionWebsObs, hres0, hop]))).trans harr
  have hmem : operandName op ∈ regionCoObs (.stackArr w m) r.res := by
    simp [regionCoObs, hop]
  have hN := List.all_eq_true.mp hobs _ hmem
  rw [List.contains_eq_mem, decide_eq_true_eq] at hN
  rw [hop] at hres
  simp only [regionResultB, List.map] at hres
  split at hres
  · rename_i RA k' op' hσ hop'
    obtain rfl := (List.cons.inj hop').1
    simp only [Bool.and_eq_true, beq_iff_eq] at hres
    obtain ⟨⟨⟨rfl, hk⟩, hA⟩, hslot⟩ := hres
    obtain ⟨arr, harr', hw⟩ := hcellsB _ _ _ hslot
    have hgo := (hA2 _ hmem 64 m).trans ((harrs _ hmem hN 64 m).trans (hArr _ 64 m))
    rw [hop] at hgo
    have h2 : tv.prog.base.getArr (operandName op) 64 m = some _ := harr
    have harr2 : u.prog.base.getArr (renOf d.ps (chainAliasO (calleeOutsT (some T))
        (regionCoCode σ nm (.stackArr 64 m) codeC [op]) (operandName op))) 64 m = some arr :=
      harr'
    rw [hgo, h2] at harr2
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

end Calling

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCompose
