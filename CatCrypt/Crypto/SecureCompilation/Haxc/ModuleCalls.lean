/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel

@[expose] public section

set_option autoImplicit false

/-!
# Module functions as compiled linked callees

A function of a module that `compileA` compiles alone is called by the entry through the ABI
as a linked callee, in place of its inlining.

## Main results

* `callSitePre_ofRegion`, `callSitePre_ofRegion_one`: the precondition of a region-compiled
  linked function holds under the resources of every call whose arguments have a source
  run, for a layout with at most one read-only pointer region and its frame words in the
  stack room of the call.
* `sameCallees_compileA_eq`: `compileA` reads the linked functions through their callees and
  their data.
* `foldl_linkFn`, `runs_foldl_linkFn`: the module with functions linked in turn, and a run
  of a module as a run of that module under `LinkSteps`.
* `callOrder`, `compileCallee`, `compileModule`: the call order of the functions of a module
  (refusing a cycle), a function compiled alone as a callee, and the driver that compiles
  the entry with the compiled callees linked.
* `compileCallee_compileA`, `compileModule_eq`, `compileModule_correct`: a compiled callee
  is a result of `compileA`, the driver result is `compileA` on the module with linked
  functions of the same callees and data, and its correctness against the source runs of
  the inlining module.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.ModuleCalls

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts HaltsC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (HaltsO oracleAt runOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall (guarded)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel (regionPre regionPost)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)

/-! ## 1. The call-site precondition of a region-compiled callee -/

/-- **The entry conditions of a layout without bounds, pointer regions or stack parameters
    hold at every state.** -/
theorem regions_of_free {σ : AbiLayout} (hb : σ.bounds = []) (hr : σ.regions = [])
    (hc : σ.regCarriedB = true) (s : AState) : σ.Regions s :=
  ⟨by simp [hb], by simp [hr], by simp [hr], AbiLayout.stackIn_of_regCarriedB hc s⟩

/-- **The precondition of a region-compiled linked function at its call sites.** Let the
    front of the leg `L` give the structured program `p` without `call` on the source
    program `src`; let the layout `σ` have no bounded register, distinct pointer regions, at
    most one pointer region other than the region of an out result, and its frame words
    below the return word (`frameHi ≤ -8`); and let every state satisfying
    `σ.Regions` at whose arguments the predicate `D` holds have a source run of `src`. Then
    the precondition `regionPre σ p` of `LinkedFn.ofRegion` holds under the resources of
    every call at whose arguments `D` holds: the resources give `σ.Regions`
    (`regions_of_entryAt`), and the leg gives a valuation `σ` reads off the state at which
    `p` denotes. -/
theorem callSitePre_ofRegion (L : FrontLegOfJ) {σ : AbiLayout} {src : L.Src}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hf : L.front σ src = some ⟨Γ, t, .regions p⟩) (hcf : p.callFree = true)
    {F : Nat} (hb : σ.bounds = []) (hnd : σ.regions.Nodup)
    (hro : (σ.regions.filter fun q =>
      !X86Backend.LinkedFnContract.isResRegion σ q).length ≤ 1)
    (hhi : σ.frameHi ≤ -8) {D : List _root_.Hax.Value → Prop}
    (hrun : ∀ sa, σ.Regions sa → D (σ.args.map (·.read sa)) → ∃ v, L.Runs σ src sa v)
    {name : String} {params : List (String × NFDialect.NfTy)} {res : NFDialect.NfTy}
    {sem : List _root_.Hax.Value → Option _root_.Hax.Value}
    {sem_res : ∀ vals v, sem vals = some v →
      (CatCrypt.Crypto.Hax.ImpToNF.dec res v).isSome = true}
    {clob : List String} {bytes : List (BitVec 8)}
    {hsem : ∀ sa sa' v, regionPre σ p sa → regionPost σ p sa sa' →
      sem (σ.args.map (·.read sa)) = some v → σ.ResultOf sa sa' v} {h0 : σ.pubWords = []} :
    (LinkedFn.ofRegion name params res sem sem_res σ p clob F bytes hsem h0).CallSitePre D := by
  intro a s hs hD
  have hR : σ.Regions s := regions_of_entryAt
    (l := LinkedFn.ofRegion name params res sem sem_res σ p clob F bytes hsem h0)
    hb hnd hro RegionKernel.ofRegion_frameLo hhi hs
  obtain ⟨-, -, hvals, -⟩ := X86Backend.LinkedFnContract.holds_entryAt hs
  have hvals' : σ.args.map (·.read s) = a.vals := hvals
  obtain ⟨v, hv⟩ := hrun s hR (by rw [hvals']; exact hD)
  obtain ⟨V, k, x, hV, hx, -⟩ := L.leg σ src _ hf _ v hR hv
  rw [RouteProgJ.envDenote_regions_of_callFree _ k p hcf] at hx
  obtain ⟨out, ho, -⟩ := Option.map_eq_some_iff.mp hx
  exact ⟨hR, V, k, out, hV, ho⟩

/-- **The call-site precondition of a region-compiled linked function with one pointer
    region.** For a layout without bounded registers whose only pointer region is `q` (one
    array parameter, or one out result) and whose frame words lie below the return word,
    the precondition of `LinkedFn.ofRegion` holds under the
    resources of every call at whose arguments `D` holds (`callSitePre_ofRegion`). -/
theorem callSitePre_ofRegion_one (L : FrontLegOfJ) {σ : AbiLayout} {src : L.Src}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hf : L.front σ src = some ⟨Γ, t, .regions p⟩) (hcf : p.callFree = true)
    {F : Nat} {q : String × Nat} (hb : σ.bounds = []) (hq : σ.regions = [q])
    (hhi : σ.frameHi ≤ -8) {D : List _root_.Hax.Value → Prop}
    (hrun : ∀ sa, σ.Regions sa → D (σ.args.map (·.read sa)) → ∃ v, L.Runs σ src sa v)
    {name : String} {params : List (String × NFDialect.NfTy)} {res : NFDialect.NfTy}
    {sem : List _root_.Hax.Value → Option _root_.Hax.Value}
    {sem_res : ∀ vals v, sem vals = some v →
      (CatCrypt.Crypto.Hax.ImpToNF.dec res v).isSome = true}
    {clob : List String} {bytes : List (BitVec 8)}
    {hsem : ∀ sa sa' v, regionPre σ p sa → regionPost σ p sa sa' →
      sem (σ.args.map (·.read sa)) = some v → σ.ResultOf sa sa' v} {h0 : σ.pubWords = []} :
    (LinkedFn.ofRegion name params res sem sem_res σ p clob F bytes hsem h0).CallSitePre D :=
  callSitePre_ofRegion L hf hcf hb (by simp [hq])
    (by rw [hq]; exact (List.length_filter_le _ _).trans (by simp)) hhi hrun

/-! ## 2. `compileA` reads the linked functions through their callees and data -/

/-- The declared procedures of a module are a function of the callees of its linked
    functions. -/
theorem linkedDecls_eq_of_callees {m₁ m₂ : HaxModule}
    (hl : m₁.linked.map LinkedFn.callee = m₂.linked.map LinkedFn.callee) (bi : _root_.Hax.Builtins) :
    linkedDecls m₁ bi = linkedDecls m₂ bi := by
  let G : List CatCrypt.Crypto.Hax.ImpToNF.CrateFn → List CatCrypt.Crypto.Hax.NFToCat.ExtDecl := fun cs =>
    (cs.filter fun c => linkNameOk c.name && linkResOk c.res).flatMap fun c =>
      ((sigVariants (c.params.map (·.2))).filter (·.all CatCrypt.Crypto.Hax.NFToCat.wordArrTy)).map fun as =>
        ⟨c.name, as, c.res, (CatCrypt.Crypto.Hax.ImpToNF.tableOf bi).call c.name as c.res⟩
  have hG : ∀ m : HaxModule, linkedDecls m bi = G (m.linked.map LinkedFn.callee) := by
    intro m
    simp only [linkedDecls, G, List.filter_map, List.flatMap_map]
    rfl
  rw [hG, hG, hl]

/-- **The region line reads the linked functions of a module through their callees and their
    data.** Two modules with the same entry, functions and depth, whose linked functions
    have the same callees (`LinkedFn.callee`: name, parameters, result type) and the same
    data (`LinkedFn.calleeData`), have the same result of `compileARegion`. -/
theorem sameCallees_compileARegion_eq {m₁ m₂ : HaxModule} (he : m₁.entry = m₂.entry)
    (hf : m₁.fns = m₂.fns) (hd : m₁.depth = m₂.depth)
    (hl : m₁.linked.map LinkedFn.callee = m₂.linked.map LinkedFn.callee)
    (hc : m₁.linked.filterMap LinkedFn.calleeData = m₂.linked.filterMap LinkedFn.calleeData)
    (σ : AbiLayout) (fname : String) :
    compileARegion m₁ σ fname = compileARegion m₂ σ fname := by
  have hall : ∀ (g : CatCrypt.Crypto.Hax.ImpToNF.CrateFn → Bool),
      m₁.linked.all (fun l => g l.callee) = m₂.linked.all (fun l => g l.callee) := by
    intro g
    have := congrArg (fun cs => cs.all g) hl
    simpa [List.all_map, Function.comp_def] using this
  have hN : m₁.linked.all (fun l => linkNameOk l.name)
      = m₂.linked.all (fun l => linkNameOk l.name) := hall fun c => linkNameOk c.name
  have hS : m₁.linked.all linkSigOk = m₂.linked.all linkSigOk :=
    hall fun c => (c.params.all fun p => linkResOk p.2) && linkResOk c.res
  have hT : haxToNF σ m₁ = haxToNF σ m₂ := by
    obtain ⟨e₁, f₁, d₁, l₁⟩ := m₁
    obtain ⟨e₂, f₂, d₂, l₂⟩ := m₂
    simp only at he hf hd hl hN hS
    subst he hf hd
    have hinl : ∀ {Γ : Ctxt NFDialect.nfDialect} {ts : List NFDialect.NfTy}
        (p : NFProg NFDialect.nfDialect Γ ts),
        (⟨e₁, f₁, d₁, l₁⟩ : HaxModule).inline? nfBody p
          = (⟨e₁, f₁, d₁, l₂⟩ : HaxModule).inline? nfBody p := by
      intro Γ ts p
      simp only [HaxModule.inline?, HaxModule.linkSig, HaxModule.linkedFns,
        HaxModule.prepared, hl]
    unfold haxToNF
    split_ifs with h1 h2 h2
    · simp only [HaxModule.linkedFns, HaxModule.prepared] at hl ⊢
      rw [hl]
      simp only [hinl]
    · exact absurd (by simpa [hN, hS, HaxModule.prepared] using h1) h2
    · exact absurd (by simpa [hN, hS, HaxModule.prepared] using h2) h1
    · rfl
  unfold compileARegion
  erw [NFEntry.compileR_eq_bind]
  erw [NFEntry.compileR_eq_bind]
  rw [hc]
  show (haxToNF σ m₁).bind _ = (haxToNF σ m₂).bind _
  rw [hT]
  congr 1
  funext q
  show ((extChain (linkedDecls m₁ _) _ q.1).run q.2).bind _
    = ((extChain (linkedDecls m₂ _) _ q.1).run q.2).bind _
  rw [linkedDecls_eq_of_callees hl]

/-- **`compileA` reads the linked functions of a module through their callees and their
    data.** Two modules with the same entry, functions and depth, whose linked functions
    have the same callees (`LinkedFn.callee`: name, parameters, result type) and the same
    data (`LinkedFn.calleeData`), have the same result of `compileA`: they have the same pair
    tail (`pairTailOf` reads the entry and the names of the functions), and the region line
    gives them the same result (`sameCallees_compileARegion_eq`). -/
theorem sameCallees_compileA_eq {m₁ m₂ : HaxModule} (he : m₁.entry = m₂.entry)
    (hf : m₁.fns = m₂.fns) (hd : m₁.depth = m₂.depth)
    (hl : m₁.linked.map LinkedFn.callee = m₂.linked.map LinkedFn.callee)
    (hc : m₁.linked.filterMap LinkedFn.calleeData = m₂.linked.filterMap LinkedFn.calleeData)
    (σ : AbiLayout) (fname : String) : compileA m₁ σ fname = compileA m₂ σ fname := by
  have hn : m₁.linked.all (fun l => l.name != "index")
      = m₂.linked.all (fun l => l.name != "index") := by
    have := congrArg (fun cs => cs.all fun c => c.name != "index") hl
    simpa [List.all_map, Function.comp_def, LinkedFn.callee] using this
  have hp : pairTailOf m₁ σ = pairTailOf m₂ σ := by
    simp only [pairTailOf, indexFreeB, he, hf, hn]
  cases h : pairTailOf m₂ σ with
  | none =>
      rw [pairTailOf_none_compileA_eq (hp.trans h), pairTailOf_none_compileA_eq h]
      exact sameCallees_compileARegion_eq he hf hd hl hc σ fname
  | some d =>
      rw [pairTailOf_some_compileA_eq (hp.trans h), pairTailOf_some_compileA_eq h]
      exact sameCallees_compileARegion_eq (m₁ := { m₁ with entry := stripArrTailT m₁.entry })
        (m₂ := { m₂ with entry := stripArrTailT m₂.entry }) (congrArg stripArrTailT he) hf hd hl
        hc σ.arrPart fname

/-! ## 3. Linking functions of a module in turn -/

/-- **The module with the functions `ls` linked in turn**: the functions of the module whose
    name is the name of no function of `ls` removed, and the functions of `ls`, last first,
    placed before the linked functions of the module. -/
theorem foldl_linkFn (ls : List LinkedFn) (m : HaxModule) :
    ls.foldl HaxModule.linkFn m =
      { m with fns := m.fns.filter (fun f => ls.all fun l => f.name != l.name)
               linked := ls.reverse ++ m.linked } := by
  induction ls generalizing m with
  | nil => simp
  | cons l ls ih =>
      rw [List.foldl_cons, ih]
      simp only [HaxModule.linkFn, List.filter_filter, List.all_cons, List.reverse_cons,
        List.append_assoc, List.singleton_append, HaxModule.mk.injEq, true_and, and_true]
      congr 1
      funext f
      exact Bool.and_comm _ _

/-- **The functions linked in turn, step by step**: at each step the module has a function
    `f` of the name of the next linked function `l`, and the meaning of `l` returns every
    value the reference meaning of `f` returns at the reference tables of the module of that
    step (the hypothesis of `HaxModule.runs_linkFn`). -/
def LinkSteps (bi : _root_.Hax.Builtins) : HaxModule → List LinkedFn → Prop
  | _, [] => True
  | m, l :: ls => (∃ f, m.fns.find? (·.name == l.name) = some f ∧
      ∀ fuelC n vals v, f.refSem (CatCrypt.Crypto.Hax.refBi m.fns (m.linkTable bi) fuelC n)
        fuelC vals = some v → l.sem vals = some v) ∧ LinkSteps bi (m.linkFn l) ls

/-- **A run of a module is a run of the module with functions linked in turn**, under
    `LinkSteps`: `HaxModule.runs_linkFn` at each step. -/
theorem runs_foldl_linkFn (bi : _root_.Hax.Builtins) (σ : AbiLayout) :
    ∀ (ls : List LinkedFn) (m : HaxModule), LinkSteps bi m ls → ∀ {sa : AState}
      {v : _root_.Hax.Value}, HaxModule.Runs bi σ m sa v →
        HaxModule.Runs bi σ (ls.foldl HaxModule.linkFn m) sa v
  | [], _, _, _, _, h => h
  | l :: ls, m, ⟨⟨_, hf, hsem⟩, hs⟩, _, _, h =>
      runs_foldl_linkFn bi σ ls (m.linkFn l) hs (HaxModule.runs_linkFn bi σ m hf hsem h)

/-! ## 4. The driver -/

/-- The names of the functions of `fs` that the extraction of `f` calls. -/
def calledFns (fs : List CatCrypt.Crypto.Hax.ModFn) (f : CatCrypt.Crypto.Hax.ModFn) :
    List String :=
  ((fs.map (·.name)).filter fun g => !_root_.Hax.Ascent.callsOK (· != g) f.texpr.erase).eraseDups

/-- **The functions of a module ordered by the call graph**, callees first: at each round
    the functions whose called functions of `fs` are all placed are placed; a round that
    places no function, which a cycle of calls causes, refuses. -/
def callOrder (fs : List CatCrypt.Crypto.Hax.ModFn) : Option (List CatCrypt.Crypto.Hax.ModFn) :=
  go fs.length fs []
where
  /-- The rounds: at most `n` more, the functions `rest` not yet placed after `acc`. -/
  go : Nat → List CatCrypt.Crypto.Hax.ModFn → List CatCrypt.Crypto.Hax.ModFn →
      Option (List CatCrypt.Crypto.Hax.ModFn)
    | _, [], acc => some acc
    | 0, _ :: _, _ => none
    | n + 1, rest@(_ :: _), acc =>
        let ready := rest.filter fun f =>
          (calledFns fs f).all fun g => acc.any (·.name == g)
        if ready.isEmpty then none
        else go n (rest.filter fun f => !ready.any (·.name == f.name)) (acc ++ ready)

/-- The plan of a callee: its layout, the registers its code may change and the size in
    bytes of its stack frame. -/
structure CalleePlan where
  /-- The layout of its arguments and result. -/
  layout : AbiLayout
  /-- The registers the code may change. -/
  clob : List String
  /-- The size in bytes of the stack frame. -/
  frame : Nat
  /-- The layout has no public array. -/
  pubWords_nil : layout.pubWords = []

/-- **A compiled callee**: a function of a module, its plan, the program of the chain on its
    extraction under the layout of the plan, and the bytes `compileRegion` gives on that
    program. -/
structure CompiledCallee where
  /-- The function. -/
  fn : CatCrypt.Crypto.Hax.ModFn
  /-- The plan. -/
  plan : CalleePlan
  /-- The result type of the program. -/
  t : JasminTy
  /-- The program of the chain. -/
  prog : NFProg jasminDialect (nfCtx plan.layout) [t]
  /-- The machine code. -/
  bytes : List (BitVec 8)

/-- The layout of a plan has no bound, no pointer region and no stack parameter. -/
def CalleePlan.freeB (pl : CalleePlan) : Bool :=
  pl.layout.bounds.isEmpty && pl.layout.regions.isEmpty && pl.layout.regCarriedB

/-- **The compilation of a callee**: the translation of the hax entry on the module of the
    single function `f` under the layout of the plan, the chain with its declared
    procedures, and `compileRegion` at no linked function (the computation of `compileA`,
    `compileCallee_compileA`); the code is kept when it decodes to a block that passes
    `keepCheckB` at the registers and frame of the plan, the layout passes
    `CalleePlan.freeB`, and the function has no pair tail at the layout (`pairTailOf`), so
    that the pair stage of `compileA` is the identity on it. -/
def compileCallee (pl : CalleePlan) (f : CatCrypt.Crypto.Hax.ModFn) : Option CompiledCallee :=
  let m := HaxModule.single f.texpr
  (haxEntry.toNF pl.layout m).bind fun q0 =>
    ((extChain (haxEntry.decls m) _ q0.1).run q0.2).bind fun p =>
      (compileRegion pl.layout (haxEntry.names f.name pl.layout) p []).bind fun r =>
        match decodeLprog r.2 with
        | some q =>
            if X86Backend.Callee.keepCheckB q (fun x => pl.clob.contains x) pl.frame
                && pl.freeB && (pairTailOf m pl.layout).isNone then
              some ⟨f, pl, _, p, r.2⟩
            else none
        | none => none

/-- **A compiled callee is a result of `compileA`** on the module of the single function,
    at the layout of its plan and the name of the function, on the program of the
    record. -/
theorem compileCallee_compileA {pl : CalleePlan} {f : CatCrypt.Crypto.Hax.ModFn}
    {k : CompiledCallee} (h : compileCallee pl f = some k) :
    k.fn = f ∧ k.plan = pl ∧ (∃ P, compileRegion pl.layout (haxEntry.names f.name pl.layout)
        k.prog [] = some (P, k.bytes) ∧ compileA (HaxModule.single f.texpr) pl.layout f.name
          = some (P, k.bytes))
      ∧ ∃ q, decodeLprog k.bytes = some q
        ∧ X86Backend.Callee.keepCheckB q (fun x => pl.clob.contains x) pl.frame = true
        ∧ pl.freeB = true := by
  unfold compileCallee at h
  obtain ⟨q0, hq0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨P, bs⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i q hq
    split at h
    · rename_i hk
      cases h
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hk
      refine ⟨rfl, rfl, ⟨P, hr, ?_⟩, q, hq, hk.1.1, hk.1.2⟩
      rw [pairTailOf_none_compileA_eq hk.2]
      simp only [compileARegion, NFEntry.compileR, NFEntry.chainNF, hq0, Option.bind_some, hp,
        Option.map_some]
      exact hr
    · cases h
  · cases h

/-- **The linked function of a compiled callee** at the meaning `sem`:
    `LinkedFn.ofRegion` at the name, parameters and result type of the function and the
    layout, program, registers, frame and bytes of the record. -/
def CompiledCallee.linkedWith (k : CompiledCallee)
    (sem : List _root_.Hax.Value → Option _root_.Hax.Value)
    (sem_res : ∀ vals v, sem vals = some v →
      (CatCrypt.Crypto.Hax.ImpToNF.dec k.fn.res v).isSome = true)
    (hsem : ∀ sa sa' v, regionPre k.plan.layout k.prog sa → regionPost k.plan.layout k.prog sa sa' →
      sem (k.plan.layout.args.map (·.read sa)) = some v → k.plan.layout.ResultOf sa sa' v) :
    LinkedFn :=
  LinkedFn.ofRegion k.fn.name k.fn.params k.fn.res sem sem_res k.plan.layout k.prog
    k.plan.clob k.plan.frame k.bytes hsem k.plan.pubWords_nil

/-- **The linked function the driver passes for a compiled callee**: `linkedWith` at the
    meaning defined nowhere. `compileA` reads it through its callee and its data only
    (`sameCallees_compileA_eq`), which `linkedWith` takes from the record whatever the
    meaning. -/
def CompiledCallee.stub (k : CompiledCallee) : LinkedFn :=
  k.linkedWith (fun _ => none) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)

/-- **The driver**: the functions of the module in call order (`callOrder`, refusing a
    cycle), each compiled alone by `compileCallee` at its plan, and `compileA` on the module
    with these callees linked in turn (`HaxModule.linkFn`), which removes them from the
    functions of the module. -/
def compileModule (m : HaxModule) (σ : AbiLayout) (fname : String)
    (plan : String → Option CalleePlan) : Option (Lprog × List (BitVec 8)) :=
  (callOrder m.fns).bind fun order =>
    (order.mapM fun f => (plan f.name).bind fun pl => compileCallee pl f).bind fun ks =>
      compileA ((ks.map CompiledCallee.stub).foldl HaxModule.linkFn m) σ fname

/-- A linked function with the callee and the data of the stub of a compiled callee. -/
def SameData (k : CompiledCallee) (l : LinkedFn) : Prop :=
  l.callee = k.stub.callee ∧ l.calleeData = k.stub.calleeData

/-- The linked function of a compiled callee at any meaning has the callee and the data of
    its stub. -/
theorem sameData_linkedWith (k : CompiledCallee)
    (sem : List _root_.Hax.Value → Option _root_.Hax.Value)
    (sem_res : ∀ vals v, sem vals = some v →
      (CatCrypt.Crypto.Hax.ImpToNF.dec k.fn.res v).isSome = true)
    (hsem : ∀ sa sa' v, regionPre k.plan.layout k.prog sa → regionPost k.plan.layout k.prog sa sa' →
      sem (k.plan.layout.args.map (·.read sa)) = some v → k.plan.layout.ResultOf sa sa' v) :
    SameData k (k.linkedWith sem sem_res hsem) :=
  ⟨rfl, rfl⟩

/-- **The driver result is the result of `compileA` on the module with the linked functions
    `ls` linked in turn**, for every list `ls` of linked functions with the callees and the
    data of the stubs of the compiled callees (`sameCallees_compileA_eq`). -/
theorem compileModule_eq {m : HaxModule} {σ : AbiLayout} {fname : String}
    {plan : String → Option CalleePlan} {r : Lprog × List (BitVec 8)}
    (h : compileModule m σ fname plan = some r) :
    ∃ order ks, callOrder m.fns = some order
      ∧ order.mapM (fun f => (plan f.name).bind fun pl => compileCallee pl f) = some ks
      ∧ ∀ ls : List LinkedFn, List.Forall₂ SameData ks ls →
          compileA (ls.foldl HaxModule.linkFn m) σ fname = some r := by
  unfold compileModule at h
  obtain ⟨order, ho, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ks, hks, h⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨order, ks, ho, hks, fun ls hls => ?_⟩
  clear hks ho
  have hcal : ls.map LinkedFn.callee = (ks.map CompiledCallee.stub).map LinkedFn.callee := by
    clear h
    induction hls with
    | nil => rfl
    | cons hk _ ih => simp only [List.map_cons, hk.1, ih]
  have hdat : ∀ (xs : List LinkedFn), (ls.reverse ++ xs).filterMap LinkedFn.calleeData
      = ((ks.map CompiledCallee.stub).reverse ++ xs).filterMap LinkedFn.calleeData := by
    intro xs
    clear h hcal
    induction hls generalizing xs with
    | nil => rfl
    | @cons k l ks ls hk _ ih =>
        simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
        rw [ih, List.filterMap_append, List.filterMap_append, List.filterMap_cons,
          List.filterMap_cons, hk.2]
  have hnames : ∀ f : CatCrypt.Crypto.Hax.ModFn,
      (ls.all fun l => f.name != l.name)
        = ((ks.map CompiledCallee.stub).all fun l => f.name != l.name) := by
    intro f
    have := congrArg (fun cs : List CatCrypt.Crypto.Hax.ImpToNF.CrateFn =>
      cs.all fun c => f.name != c.name) hcal
    simpa [List.all_map, Function.comp_def, LinkedFn.callee] using this
  rw [← h, foldl_linkFn, foldl_linkFn]
  refine sameCallees_compileA_eq (he := ?_) (hf := ?_) (hd := ?_) (hl := ?_) (hc := ?_) σ fname
  · rfl
  · simp only [hnames]
  · rfl
  · simp only [List.map_append, List.map_reverse, hcal]
  · exact hdat m.linked

/-- **Correctness of the driver against the source runs of the inlining module.** Let
    `compileModule` return `(P, bytes)` on the module `m`. Then the functions of `m` have a
    call order and compiled callees `ks`, and for every list `ls` of linked functions with
    the callees and the data of the stubs of `ks` (for instance `CompiledCallee.linkedWith`
    at the meanings of the functions, `sameData_linkedWith`) such that

    * the linked functions of the module with `ls` linked in turn have distinct names and
      are linked kernels (`LinkedKernel`; a region-compiled callee with a `u64` result is
      one by `LinkedWordKernel.toKernel`, with the call-site precondition
      `callSitePre_ofRegion`), and
    * the meaning of each function of `ls` returns the values of the reference meaning of the
      function it replaces at each step (`LinkSteps`),

    the bytes decode to a program `prog`, and from every entry state `sa` satisfying
    `σ.Regions`, every value `v` of a source run of `m` from `sa`, at the table of `m`, which
    runs the callees by their reference reading, is read back by `σ` as in
    `haxc_correct_auto`. The bytes are those of `compileA` on the module with `ls` linked
    (`compileModule_eq`), the source run of `m` is one of that module
    (`runs_foldl_linkFn`), and the runs are `haxc_correct_auto`. -/
theorem compileModule_correct {m : HaxModule} {σ : AbiLayout} {fname : String}
    {plan : String → Option CalleePlan} {P : Lprog} {bytes : List (BitVec 8)}
    (h : compileModule m σ fname plan = some (P, bytes)) :
    ∃ order ks, callOrder m.fns = some order
      ∧ order.mapM (fun f => (plan f.name).bind fun pl => compileCallee pl f) = some ks
      ∧ ∀ ls : List LinkedFn, List.Forall₂ SameData ks ls →
        ((ls.foldl HaxModule.linkFn m).linked.map (·.name)).Nodup →
        (∀ l ∈ (ls.foldl HaxModule.linkFn m).linked, LinkedKernel l) →
        LinkSteps CatCrypt.Crypto.Hax.hax64WExit m ls →
        ∀ (sa : AState), σ.Regions sa → ∀ v, haxRuns σ m sa v →
          ∃ prog, decodeLprog bytes = some prog ∧
            ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∨ ∃ c ∈ (ls.foldl HaxModule.linkFn m).linked.filterMap LinkedFn.calleeData,
              ∃ pc q, decodeLprog c.bytes = some q ∧ prog = pc ++ shiftProg pc.length q
                ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
                ∧ ∃ sa', HaltsO aMachine (oracleAt pc.length (guarded c.sig (runOf ctRegime q)))
                    pc 0 sa sa' ∧ σ.ResultOf sa sa' v) := by
  obtain ⟨order, ks, ho, hks, hc⟩ := compileModule_eq h
  refine ⟨order, ks, ho, hks, fun ls hls hnd hk hsteps sa hsep v hrun => ?_⟩
  obtain ⟨prog, hd, h⟩ := haxc_correct_auto _ σ fname P bytes (hc ls hls) sa hsep v
    (runs_foldl_linkFn _ σ ls m hsteps hrun) hnd hk
  rcases h with ⟨sa', hh, hR, -⟩ | h
  · exact ⟨prog, hd, .inl ⟨sa', hh, hR⟩⟩
  · exact ⟨prog, hd, .inr h⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.ModuleCalls
