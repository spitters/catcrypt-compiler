/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.WordResult
public import CatCrypt.Crypto.SecureCompilation.Haxc.BackHalf
public import CatCrypt.Crypto.SecureCompilation.Haxc.FrontLegOf
public import CatCrypt.Crypto.SecureCompilation.Haxc.Consts
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChain
public import CatCrypt.Crypto.SecureCompilation.Haxc.ExtChain
public import CatCrypt.Crypto.SecureCompilation.Haxc.TupleTail

@[expose] public section

set_option autoImplicit false

/-!
# The general compiler theorem: the front half and the back half

The unit of compilation is a module `HaxModule`: an entry function, the functions the entry
may call and an inlining depth. A single function is the module with no callee, and a
`TExpr` coerces to it.

`compileA` is `compileARegion`, the compiler `NFEntry.compileR` at the hax entry `haxEntry`:
the typed front, the translation to `NFProg` at the call typing of the functions of the
module, the inlining of their calls, the chain `extChain` at the declared procedures
`linkedDecls` of the module, then the region back half `RegionBackend.compileRegion`. The
front runs on the entry of the module with the constants of the layout bound at its head
(`bindConsts`), whose source reading is that of the entry (`run_bindConsts_of_envOf`). A
program the region back half refuses has no result. A result is a result of
`compileRegion` on the program of the region front `NFEntry.frontR`
(`NFEntry.compileR_spec`). On a module that `nfToCat` translates after `dce` the chain
returns what `nfChainPre` returns (`extChain_run_of_nfToCat`); the field values at a
modulus that passes `mont32Cert` are kept in Montgomery form where the degree analysis places
them (`NFMontify.montifyStep`), and a tagged field call is lowered by the chain's field-dialect
step through the template of its modulus (`fieldDialectStep`).

A module may carry linked functions (`HaxModule.linked`). The front types a call of a linked
function and keeps it as a call. In the source relation `haxRuns` a call of a linked
function is the value of its meaning `LinkedFn.sem`, and the leg of the region front is
stated at the call environment of the hax entry, which answers a linked symbol by that
meaning. The data the region back half reads of a linked function, with its machine
contract, is `LinkedFn.calleeData`, and `compileA` passes the data of the linked functions of
the module to `compileRegion`. A module whose translation keeps a call of a linked word
kernel is compiled when `compileRegion` finds the callee among them; the correctness of such
a result is `RegionLinkCall.compileRegion_correct_linked`, and the theorems of this file are
stated at modules without linked functions.
The theorem `NFEntry.compileR_correct` is the leg of the region front composed with the
correctness of `compileRegion`; at the hax entry it is the case without `call` of the
compiler theorem `haxc_correct_auto` (`RegionLinkCall`). In the source run a call of a
function of the module is the run of the source reading of the extraction of the callee
under the table of the module. A program compiled without linked functions has no `call`
(`callFree_of_compileRegion`), so its denotation does not read the call environment
(`RouteProgJ.envDenote_regions_of_callFree`).

## Main results

* `callFree_of_compileRegion` — a structured program the region back half compiles without
  linked functions has no `call`.
* `NFEntry.compileR`, `NFEntry.frontR_of_compileRegion`, `NFEntry.compileR_spec`,
  `NFEntry.compileR_correct` — the compiler at an entry (its translation, the chain
  `extChain` and `compileRegion`), the program of the region front it compiles, and its
  theorem: the leg of the region front composed with the correctness of `compileRegion`.
* `compileARegion`, `linkedNil_compileARegion_eq` — `NFEntry.compileR` at the hax entry
  `haxEntry` and the linked functions of the module, and its value on a module without them.
* `compileA`, `linkedNil_compileA_eq` — the compiler taking no witness on a module
  (`compileARegion`), and its value on a module without linked functions; its theorem is
  `haxc_correct_auto` (`RegionLinkCall`).
* `LinkedFn.calleeData` — the data of a linked function the region back half reads: its
  argument and result registers and its array positions from its layout, its clobbered
  registers, frame, bytes and machine contract; `LinkedFn.calleeData_shape`, the call
  shape of that data.
* `isControlFlow_false_of_wordResult` — a run of an extraction satisfying `WordArrResult` or
  `WordScalResult` returns a value that is not a control-flow value.
* `pairStage_frame`, `entryA_pairStage`, `layoutMem_pairStage` — the layout of the pair stage
  has the stack range, the pointer regions, the entry state of the address machine and the
  bytes `layoutMem` of the layout.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open _root_.Hax (TExpr Value Env)
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Crypto.Hax (hax64WExit HaxModule)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (entryA)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (RunSafe)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (runA)
open CatCrypt.Crypto.SecureCompilation.SepLogic.Addr (AccessIn)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)

/-! ## 1. The compiler at an entry -/

/-- A structured program the stages `regionBack` compile without linked functions has no
    `call`: `regionCallee` at the empty list returns a result on a program without `call`
    only. -/
theorem callFree_of_regionBack {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {r : Lprog × List (BitVec 8)}
    (h : regionBack σ a p = some r) : p.callFree = true := by
  unfold regionBack at h
  split at h
  · split at h
    · split at h
      · rename_i callee hc
        obtain rfl := regionCallee_nil hc
        rw [← legalizeRegion_callFree_eq]
        exact regionCallee_callFree hc
      · cases h
    · cases h
  · cases h

/-- A structured program the region back half compiles without linked functions has no
    `call`: its widened program has none (`callFree_of_regionBack`), and the narrow-word
    stages keep the calls (`NarrowWords.callFree_narrowPrep`). -/
theorem callFree_of_compileRegion {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {r : Lprog × List (BitVec 8)}
    (h : compileRegion σ a p = some r) : p.callFree = true := by
  obtain ⟨-, q, hq, hb⟩ := compileRegion_eq_some.mp h
  rw [← VIR.NarrowWords.callFree_narrowPrep hq]
  exact callFree_of_regionBack hb

/-- The result type of the region front is not an array of narrow words: the conversion
    `catTy` sends every array to a `memref` of 64-bit words. -/
theorem narrowArrB_mapTy_catTy (x : NFDialect.NfTy) :
    narrowArrB (CryptoToJasminCom.mapTy (CatCrypt.Crypto.Hax.NFToCat.catTy x)) = false := by
  cases x <;> rfl

/-- The context of the region front holds 64-bit words only: the widening fixes it. -/
theorem nfCtx_wide (σ : AbiLayout) : (nfCtx σ).map VIR.NarrowWords.wideTy = nfCtx σ := by
  simp only [nfCtx, CryptoToJasminCom.mapCtx, CatCrypt.Crypto.Hax.ImpToNF.entryCtx,
    NFToRoute.abiEntry, CatCrypt.Crypto.Hax.NFToCat.abiParamsArr, List.map_map,
    List.map_reverse]
  congr 1
  apply List.map_congr_left
  intro a _
  rcases a with ⟨_, _, _ | _⟩ <;> rfl

/-- **The structured program of the compiler at an entry**: the translation `E.toNF` of the
    source program and the chain `extChain` at its declared procedures, ending in the
    `jasminDialect` program that the region back half compiles. `compileR` is this stage
    followed by `compileRegion`; a printer of the same program reads it here. -/
def NFEntry.chainNF (E : NFEntry) (s : E.Src) (σ : AbiLayout) :
    Option (Σ t : JasminTy, NFProg jasminDialect (nfCtx σ) [t]) :=
  (E.toNF σ s).bind fun q =>
    ((extChain (E.decls s) _ q.1).run q.2).map fun p => ⟨_, p⟩

/-- **The compiler at an entry**: the translation `E.toNF` of the source program, the chain
    `extChain` at the declared procedures `E.decls s` of the source program, and the region
    back half `compileRegion` under the export names `E.names fname σ` at the linked
    functions `linked`. `compileRegion` tests `regionExportableB`; a program with a `call`
    is compiled only when its callee is among `linked`, so at no linked function (the
    default) the result is `none` on a source program whose translation keeps a call of a
    declared procedure. -/
def NFEntry.compileR (E : NFEntry) (s : E.Src) (σ : AbiLayout) (fname : String)
    (linked : List CalleeData := []) : Option (Lprog × List (BitVec 8)) :=
  (E.chainNF s σ).bind fun x => compileRegion σ (E.names fname σ) x.2 linked

/-- `compileR` unfolded through its stage `chainNF`: the translation, the chain and the
    region back half as three nested binds. -/
theorem NFEntry.compileR_eq_bind (E : NFEntry) (s : E.Src) (σ : AbiLayout) (fname : String)
    (linked : List CalleeData) :
    E.compileR s σ fname linked =
      (E.toNF σ s).bind fun q =>
        ((extChain (E.decls s) _ q.1).run q.2).bind fun p =>
          compileRegion σ (E.names fname σ) p linked := by
  unfold NFEntry.compileR NFEntry.chainNF
  cases E.toNF σ s with
  | none => rfl
  | some q =>
      simp only [Option.bind_some]
      cases (extChain (E.decls s) _ q.1).run q.2 <;> rfl

/-- **A program of the chain that `compileRegion` compiles is the program of the region
    front.** Let the translation of the entry return `q` on `s`, the chain `extChain` at the
    declared procedures of `s` return `p` on `q`, and `compileRegion` return a result on `p`.
    Then `p` passes `regionExportableB` and has no `call` (`callFree_of_compileRegion`), so
    the region export at the signatures of the declared procedures accepts it and the region
    front returns `p`. -/
theorem NFEntry.frontR_of_compileRegion {E : NFEntry} {s : E.Src} {σ : AbiLayout}
    {q : Σ t : NFDialect.NfTy,
      NFProg NFDialect.nfDialect (CatCrypt.Crypto.Hax.ImpToNF.entryCtx (NFToRoute.abiEntry σ)) [t]}
    {p : NFProg jasminDialect (nfCtx σ)
      [CryptoToJasminCom.mapTy (CatCrypt.Crypto.Hax.NFToCat.catTy q.1)]}
    {a : AbiNames} {r : Lprog × List (BitVec 8)}
    (hq : E.toNF σ s = some q) (hp : (extChain (E.decls s) _ q.1).run q.2 = some p)
    (hc : compileRegion σ a p = some r) :
    E.frontR σ s = some ⟨nfCtx σ, _, .regions p⟩ := by
  have hex : exportRegion (declSigs (E.decls s)) p = some (.regions p) := by
    unfold exportRegion
    rw [show ExportRegions.regionExportableB (legalizeRegion p) = true from (compileRegion_spec hc).1,
      onlyCalls_of_callFree _ p (callFree_of_compileRegion hc)]
    rfl
  unfold NFEntry.frontR
  rw [hq, Option.bind_some, hp, Option.bind_some, hex]
  rfl

/-- **A result of the compiler at an entry is a result of `compileRegion` on the program of
    the region front.** The region front `E.frontR` returns the structured program `q`, and
    `compileRegion` returns the result on `q` (`NFEntry.frontR_of_compileRegion`). -/
theorem NFEntry.compileR_spec {E : NFEntry} {s : E.Src} {σ : AbiLayout} {fname : String}
    {P : Lprog} {bytes : List (BitVec 8)} (hc : E.compileR s σ fname = some (P, bytes)) :
    ∃ (t : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t]),
      E.frontR σ s = some ⟨nfCtx σ, t, .regions q⟩ ∧
        compileRegion σ (E.names fname σ) q = some (P, bytes) := by
  rw [NFEntry.compileR_eq_bind] at hc
  obtain ⟨q0, hq0, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨p, hp, hc⟩ := Option.bind_eq_some_iff.mp hc
  exact ⟨_, p, NFEntry.frontR_of_compileRegion hq0 hp hc, hc⟩

/-- **The compiler theorem at an entry, with the callee-saved registers.** For a result
    `(P, bytes)` of `E.compileR s σ fname`: from every entry state `sa` satisfying
    `σ.Regions`, every value `v` of a source run of `s` from `sa` is matched by a halting run
    of the machine on the decoded bytes in a state from which `σ` reads back `v`, whose stack
    register and System V callee-saved registers (`DecodedCT.calleeSaved`) hold their entry
    values, and whose memory agrees with the entry memory at every byte outside the stack
    words and the pointer regions of `σ`; some run of the address machine on a body from
    `entryA σ sa` halts and stores to and loads from `layoutMem σ sa` only. The proof
    composes the leg of the region front `E.toFrontLegOfR` at the structured program of
    `NFEntry.compileR_spec` with `RegionBackend.compileRegion_correct_saved`: the compiled program has no `call`, so it
    denotes the same value at the environment in which every call refuses
    (`RouteProgJ.envDenote_regions_of_callFree`). -/
theorem NFEntry.compileR_correct_saved (E : NFEntry) (s : E.Src) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8)) (hc : E.compileR s σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : E.Runs σ s sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' v
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x ∈ X86Backend.DecodedCT.calleeSaved, sa'.regs x = sa.regs x)
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false := by
  rw [NFEntry.compileR_eq_bind] at hc
  obtain ⟨q0, hq0, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨q, hp, hJ⟩ := Option.bind_eq_some_iff.mp hc
  have hf := NFEntry.frontR_of_compileRegion hq0 hp hJ
  obtain ⟨V, fuel, x, hV, hx, hv⟩ := E.toFrontLegOfR.leg σ s _ hf sa v hsep hrun
  rw [RouteProgJ.envDenote_regions_of_callFree _ fuel q (callFree_of_compileRegion hJ)] at hx
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨prog', sa', hd, hh, hR, hsp, hcs, hkeep, hA⟩ :=
    compileRegion_correct_wide_saved hJ sa V hV hsep fuel hw (narrowArrB_mapTy_catTy _)
  refine ⟨prog', sa', hd, hh, ?_, hsp, hcs, hkeep, hA⟩
  rw [hv]
  exact hR

/-- **The compiler theorem at an entry.** For a result `(P, bytes)` of `E.compileR s σ fname`:
    from every entry state `sa` satisfying `σ.Regions`, every value `v` of a source run of `s`
    from `sa` is matched by a halting run of the machine on the decoded bytes in a state from
    which `σ` reads back `v`, whose stack register holds its entry value, and whose memory
    agrees with the entry memory at every byte outside the stack words and the pointer
    regions of `σ`; some run of the address machine on a body from `entryA σ sa` halts and
    stores to and loads from `layoutMem σ sa` only. The proof composes the leg of the region
    front `E.toFrontLegOfR` at the structured program of `NFEntry.compileR_spec` with
    `RegionBackend.compileRegion_correct`: the compiled program has no `call`, so it denotes
    the same value at the environment in which every call refuses
    (`RouteProgJ.envDenote_regions_of_callFree`). -/
theorem NFEntry.compileR_correct (E : NFEntry) (s : E.Src) (σ : AbiLayout) (fname : String)
    (P : Lprog) (bytes : List (BitVec 8)) (hc : E.compileR s σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : E.Runs σ s sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' v
      ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ x, SepLogic.X86.Loc.mem x
          ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
        (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
        sa'.mem x = sa.mem x)
      ∧ ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
        ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false := by
  rw [NFEntry.compileR_eq_bind] at hc
  obtain ⟨q0, hq0, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨q, hp, hJ⟩ := Option.bind_eq_some_iff.mp hc
  have hf := NFEntry.frontR_of_compileRegion hq0 hp hJ
  obtain ⟨V, fuel, x, hV, hx, hv⟩ := E.toFrontLegOfR.leg σ s _ hf sa v hsep hrun
  rw [RouteProgJ.envDenote_regions_of_callFree _ fuel q (callFree_of_compileRegion hJ)] at hx
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨prog', sa', hd, hh, hR, hsp, hkeep, hA⟩ := compileRegion_correct_wide hJ sa V hV hsep fuel hw
    (narrowArrB_mapTy_catTy _)
  refine ⟨prog', sa', hd, hh, ?_, hsp, hkeep, hA⟩
  rw [hv]
  exact hR

/-- **The result of a linked function as the region back half reads it**: for a result in
    the register `r`, that register in the upper-case names of the region back half (`%rax`
    becomes `RAX`); for a result of `n` words at the register of a parameter of the layout
    that is an array of `n` words, the out result of length `n` at the position `k` of the
    first such parameter; `none` for every other result. -/
def _root_.CatCrypt.Crypto.Hax.LinkedFn.calleeRes (l : CatCrypt.Crypto.Hax.LinkedFn) :
    Option CalleeRes :=
  match l.layout.result with
  | .reg r => some (.reg ((r.drop 1).toString).toUpper)
  | .words r n =>
      (l.layout.args.findIdx? fun a => decide (a.reg = r ∧ a.kind = .words n)).map (.out n)
  | _ => none

/-- **An out result of a linked function** is read at a parameter of its layout: the result
    of the layout is `n` words at a register `r`, and the parameter at the position `k` is an
    array of `n` words at `r`. -/
theorem _root_.CatCrypt.Crypto.Hax.LinkedFn.calleeRes_out {l : CatCrypt.Crypto.Hax.LinkedFn}
    {n k : Nat} (h : l.calleeRes = some (.out n k)) :
    ∃ r a, l.layout.result = .words r n ∧ l.layout.args[k]? = some a ∧ a.reg = r
      ∧ a.kind = .words n := by
  unfold CatCrypt.Crypto.Hax.LinkedFn.calleeRes at h
  split at h
  · cases h
  · rename_i r m hres
    obtain ⟨j, hj, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    obtain ⟨hk, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
    refine ⟨r, _, hres, List.getElem?_eq_getElem hk, ?_⟩
    simpa using hp
  · cases h

/-- **The data the region back half reads of a linked function**: its symbol; the argument
    registers of its layout, in order, in the upper-case names of the region back half
    (`%rdi` becomes `RDI`); its result (`LinkedFn.calleeRes`); its clobbered registers, its
    frame and its bytes; its machine contract (precondition, footprint, postcondition and
    public relation); the machine registers of the public arguments of its layout
    (`AbiLayout.argPub`); the array positions of its layout, with the length in words of
    each array argument (`insArrArgs` of the argument kinds); and the store policy of its
    code. `none` when the layout of
    the function returns its result neither in a register nor in the array of one of its
    parameters. -/
def _root_.CatCrypt.Crypto.Hax.LinkedFn.calleeData (l : CatCrypt.Crypto.Hax.LinkedFn) :
    Option CalleeData :=
  l.calleeRes.map fun res =>
    { name := l.name
      args := l.layout.args.map fun a => ((a.reg.drop 1).toString).toUpper
      res := res
      clob := l.clob
      frame := l.frame
      bytes := l.bytes
      pre := l.pre
      foot := l.foot
      post := l.post
      pub := l.pub
      pubRegs := (l.layout.args.filter l.layout.argPub).map (·.reg)
      arrArgs := CatCrypt.Crypto.Hax.insArrArgs (l.layout.args.map (·.kind))
      pol := l.pol }

/-- The store policy of the data of a linked function is the store policy of the
    function. -/
theorem _root_.CatCrypt.Crypto.Hax.LinkedFn.calleeData_pol {l : CatCrypt.Crypto.Hax.LinkedFn}
    {c : CalleeData} (h : l.calleeData = some c) : c.pol = l.pol := by
  obtain ⟨res, -, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

/-- **The fields of the data of a linked function**: the symbol, the argument registers,
    the clobbered registers, the frame, the bytes, the machine contract, the public
    argument registers and the array positions of the layout of the linked function, and a
    result of `LinkedFn.calleeRes`. -/
theorem _root_.CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq {l : CatCrypt.Crypto.Hax.LinkedFn}
    {c : CalleeData} (h : l.calleeData = some c) :
    l.calleeRes = some c.res ∧ c.name = l.name
      ∧ c.args = l.layout.args.map (fun a => ((a.reg.drop 1).toString).toUpper)
      ∧ c.clob = l.clob ∧ c.frame = l.frame ∧ c.bytes = l.bytes ∧ c.pre = l.pre
      ∧ c.foot = l.foot ∧ c.post = l.post ∧ c.pub = l.pub
      ∧ c.pubRegs = (l.layout.args.filter l.layout.argPub).map (·.reg)
      ∧ c.arrArgs = CatCrypt.Crypto.Hax.insArrArgs (l.layout.args.map (·.kind)) := by
  obtain ⟨res, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨hr, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The shape of a call of the data of a linked function**: its array positions are those
    of the layout of the linked function, and its result is an out result exactly at a
    word-array result of the layout. -/
theorem _root_.CatCrypt.Crypto.Hax.LinkedFn.calleeData_shape {l : CatCrypt.Crypto.Hax.LinkedFn}
    {c : CalleeData} (h : l.calleeData = some c) :
    c.shape.arrArgs = CatCrypt.Crypto.Hax.insArrArgs (l.layout.args.map (·.kind))
      ∧ (c.shape.out = true ↔ ∃ n k, c.res = .out n k) := by
  refine ⟨(CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq h).2.2.2.2.2.2.2.2.2.2.2, ?_⟩
  cases hr : c.res <;> simp [CalleeData.shape, hr]

/-- The interface of the data of a linked function is its machine contract: the
    precondition, footprint, postcondition and public relation of the linked function. -/
theorem _root_.CatCrypt.Crypto.Hax.LinkedFn.calleeData_sig {l : CatCrypt.Crypto.Hax.LinkedFn}
    {c : CalleeData} (h : l.calleeData = some c) :
    c.sig.pre = l.pre ∧ c.sig.foot = l.foot ∧ c.sig.post = l.post ∧ c.sig.pub = l.pub := by
  obtain ⟨-, -, -, -, -, -, hp, hf, hq, hb, -⟩ :=
    CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq h
  exact ⟨hp, hf, hq, hb⟩

/-- **The hax compiler through the region back half**: the compiler `NFEntry.compileR` at the
    hax entry `haxEntry`, at the data `LinkedFn.calleeData` of the linked functions of the
    module: the translation `haxToNF` of the module, the chain `extChain` at the declared
    procedures `linkedDecls` of the module, and `compileRegion` at those linked functions.
    On a module without linked functions the chain is `nfChainPre` and the result is that of
    `haxEntry.compileR` (`linkedNil_compileARegion_eq`). A module whose translation keeps a
    call of a linked word kernel is compiled when `compileRegion` finds the callee among the
    linked functions; the correctness of such a result is
    `RegionLinkCall.compileRegion_correct_linked`. -/
def compileARegion (m : HaxModule) (σ : AbiLayout) (fname : String) :
    Option (Lprog × List (BitVec 8)) :=
  haxEntry.compileR m σ fname (m.linked.filterMap CatCrypt.Crypto.Hax.LinkedFn.calleeData)

/-- On a module without linked functions, `compileARegion` is `haxEntry.compileR` at no
    linked function. -/
theorem linkedNil_compileARegion_eq {m : HaxModule} (h : m.linked = []) (σ : AbiLayout)
    (fname : String) : compileARegion m σ fname = haxEntry.compileR m σ fname := by
  rw [compileARegion, h]
  rfl

/-- No function and no linked function of the module has the name `index`, so the table of
    the module answers `index` as the base table does. -/
def indexFreeB (m : HaxModule) : Bool :=
  m.fns.all (·.name != "index") && m.linked.all (·.name != "index")

/-- On a module without a function named `index` (`indexFreeB`), the table of the module
    answers `index` as the base table. -/
theorem table_index_of_indexFreeB {m : HaxModule} (h : indexFreeB m = true)
    (bi : _root_.Hax.Builtins) (fuelC : Nat) (vals : List Value) :
    m.table bi fuelC "index" vals = bi "index" vals := by
  simp only [indexFreeB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  rw [HaxModule.table, CatCrypt.Crypto.Hax.refBi_of_find_none, HaxModule.linkTable,
    CatCrypt.Crypto.Hax.linkBi_of_find_none]
  · exact List.find?_eq_none.mpr fun l hl => by simpa using h.2 l hl
  · exact List.find?_eq_none.mpr fun f hf => by simpa using h.1 f hf

/-- **The pair tail of a module at a layout**: the data `arrWordTailOf` of a pair result
    (the register `i` and the scalar parameter `k`) of the entry of the module at the layout,
    when no function of the module has the name `index` (`indexFreeB`); `none` otherwise,
    and `none` at once on a layout whose result is not a tuple. -/
def pairTailOf (m : HaxModule) (σ : AbiLayout) : Option (String × String) :=
  match σ.result with
  | .tuple _ => (arrWordTailOf σ m.entry.erase).filter fun _ => indexFreeB m
  | _ => none

/-- **The pair stage**: on a module and a layout with a pair tail (`pairTailOf`), the module
    whose entry has the tail `let y = a[k]; (a, y)` replaced by `a` (`stripArrTailT`) and the
    array part of the layout (`AbiLayout.arrPart`); the module and the layout otherwise. -/
def pairStage (m : HaxModule) (σ : AbiLayout) : HaxModule × AbiLayout :=
  match pairTailOf m σ with
  | some _ => ({ m with entry := stripArrTailT m.entry }, σ.arrPart)
  | none => (m, σ)

/-- **The hax compiler with no witness**, on a module: the pair stage `pairStage`, then
    `compileARegion`, the region back half on the structured program of the module at the
    linked functions of the module. The calls of the functions of the module are inlined to
    its depth. A module the region route refuses has no result. A single function is the
    module with no callee and no linked function, and a `TExpr` coerces to it. -/
def compileA (m : HaxModule) (σ : AbiLayout) (fname : String) :
    Option (Lprog × List (BitVec 8)) :=
  compileARegion (pairStage m σ).1 (pairStage m σ).2 fname

/-- Without a pair tail, `compileA` is `compileARegion`. -/
theorem pairTailOf_none_compileA_eq {m : HaxModule} {σ : AbiLayout} (h : pairTailOf m σ = none)
    (fname : String) : compileA m σ fname = compileARegion m σ fname := by
  simp only [compileA, pairStage, h]

/-- With a pair tail, `compileA` is `compileARegion` on the stripped entry under the array
    part of the layout. -/
theorem pairTailOf_some_compileA_eq {m : HaxModule} {σ : AbiLayout} {d : String × String}
    (h : pairTailOf m σ = some d) (fname : String) :
    compileA m σ fname = compileARegion { m with entry := stripArrTailT m.entry } σ.arrPart fname
    := by
  simp only [compileA, pairStage, h]

/-- The data of a pair tail: the data `arrWordTailOf` of the entry, and no function of the
    module has the name `index`. -/
theorem pairTailOf_spec {m : HaxModule} {σ : AbiLayout} {d : String × String}
    (h : pairTailOf m σ = some d) : arrWordTailOf σ m.entry.erase = some d ∧ indexFreeB m = true
    := by
  unfold pairTailOf at h
  split at h
  · cases ha : arrWordTailOf σ m.entry.erase with
    | none => simp [ha] at h
    | some d' =>
        rw [ha] at h
        cases hb : indexFreeB m
        · simp [Option.filter, hb] at h
        · simp only [Option.filter, hb, ite_true, Option.some.injEq] at h
          exact ⟨h ▸ rfl, rfl⟩
  · cases h

/-- On a module without linked functions and without a pair tail, `compileA` is
    `haxEntry.compileR` at no linked function. -/
theorem linkedNil_compileA_eq {m : HaxModule} (h : m.linked = []) (σ : AbiLayout)
    (fname : String) (hp : pairTailOf m σ = none := by rfl) :
    compileA m σ fname = haxEntry.compileR m σ fname := by
  rw [pairTailOf_none_compileA_eq hp]
  exact linkedNil_compileARegion_eq h σ fname

/-- The pair stage keeps the linked functions of the module. -/
theorem pairStage_linked (m : HaxModule) (σ : AbiLayout) :
    (pairStage m σ).1.linked = m.linked := by
  unfold pairStage
  split <;> rfl

/-- The layout of the pair stage has the regions of the layout. -/
theorem pairStage_regions (m : HaxModule) (σ : AbiLayout) (sa : AState) :
    (pairStage m σ).2.Regions sa ↔ σ.Regions sa := by
  unfold pairStage
  split
  · exact arrPart_regions σ sa
  · exact Iff.rfl

/-- The layout of the pair stage has the stack range and the pointer regions of the
    layout. -/
theorem pairStage_frame (m : HaxModule) (σ : AbiLayout) :
    (pairStage m σ).2.frameLo = σ.frameLo ∧ (pairStage m σ).2.frameHi = σ.frameHi
      ∧ (pairStage m σ).2.regions = σ.regions := by
  unfold pairStage
  split
  · unfold AbiLayout.arrPart
    split <;> exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- The entry state of the address machine at the layout of the pair stage is that at the
    layout: the pair stage changes only the result of the layout. -/
theorem entryA_pairStage (m : HaxModule) (σ : AbiLayout) (sa : AState) :
    entryA (pairStage m σ).2 sa = entryA σ sa := by
  unfold pairStage
  split
  · unfold AbiLayout.arrPart
    split <;> rfl
  · rfl

/-- The bytes of the stack words and the pointer regions at the layout of the pair stage are
    those at the layout. -/
theorem layoutMem_pairStage (m : HaxModule) (σ : AbiLayout) (sa : AState) :
    layoutMem (pairStage m σ).2 sa = layoutMem σ sa := by
  obtain ⟨hlo, hhi, hrg⟩ := pairStage_frame m σ
  unfold layoutMem
  rw [hlo, hhi, hrg]

/-- The array part of a layout has the public data of the layout: `PubAgree` reads the
    parameters and the bounds, which the array part keeps. -/
theorem arrPart_pubAgree (σ : AbiLayout) (s₁ s₂ : AState) :
    σ.arrPart.PubAgree s₁ s₂ ↔ σ.PubAgree s₁ s₂ := by
  unfold AbiLayout.arrPart
  split <;> exact ⟨fun h => ⟨h.rsp, h.regs, h.words⟩, fun h => ⟨h.rsp, h.regs, h.words⟩⟩

/-- The layout of the pair stage has the public data of the layout. -/
theorem pairStage_pubAgree (m : HaxModule) (σ : AbiLayout) (s₁ s₂ : AState) :
    (pairStage m σ).2.PubAgree s₁ s₂ ↔ σ.PubAgree s₁ s₂ := by
  unfold pairStage
  split
  · exact arrPart_pubAgree σ s₁ s₂
  · exact Iff.rfl

/-- **The source run through the pair stage.** Every source run of `m` from `sa` to `v` under
    `σ` is matched by a source run to a value `x` of the module of the pair stage under its
    layout, and every state from which the layout of the pair stage reads back `x` is one from
    which `σ` reads back `v`. Without a pair tail `x` is `v`. With a pair tail
    `let y = a[k]; (a, y)`, `x` is the array `a` and `v` the pair of `x` and its word at the
    entry value of `k` (`denoteSpine_stripArrTail`): the table of the module answers `index`
    as `hax64WExit` (`table_index_of_indexFreeB`), and the layout reads back the pair
    (`resultOf_arrWordTail`). -/
theorem haxRuns_pairStage {m : HaxModule} {σ : AbiLayout} {sa : AState} {v : Value}
    (hrun : haxRuns σ m sa v) :
    ∃ x, haxRuns (pairStage m σ).2 (pairStage m σ).1 sa x ∧
      ∀ sa', (pairStage m σ).2.ResultOf sa sa' x → σ.ResultOf sa sa' v := by
  cases hpt : pairTailOf m σ with
  | none =>
      have hs : pairStage m σ = (m, σ) := by simp only [pairStage, hpt]
      rw [hs]
      exact ⟨v, hrun, fun _ h => h⟩
  | some d =>
      have hs : pairStage m σ = ({ m with entry := stripArrTailT m.entry }, σ.arrPart) := by
        simp only [pairStage, hpt]
      rw [hs]
      obtain ⟨hdat, hfree⟩ := pairTailOf_spec hpt
      obtain ⟨r, n, a, hσ, htail, hka, hkeep⟩ := arrWordTailOf_spec hdat
      obtain ⟨env, fuel, fuelC, env', henv, hr, hcf⟩ := hrun
      obtain ⟨x, env'', hrs, hdisj⟩ := denoteSpine_stripArrTail _ fuel m.entry.erase htail hkeep
        (envOf_scalarArg hka henv) hr
      rcases hdisj with ⟨hxc, rfl⟩ | ⟨hxc, w, hw, hv⟩
      · rw [hcf] at hxc
        cases hxc
      rcases hv with ⟨hwc, rfl⟩ | rfl
      · rw [hcf] at hwc
        cases hwc
      rw [table_index_of_indexFreeB hfree] at hw
      exact ⟨x, ⟨env, fuel, fuelC, env'', (arrPart_envOf σ sa env).2 henv,
        by rw [erase_stripArrTailT]; exact hrs, hxc⟩,
        fun sa' hR => resultOf_arrWordTail hσ hR hw⟩

/-- A run of the source reading of `te` from an environment `σ` reads off an entry state
    satisfying `σ.Regions` returns a value that is not a control-flow value, when the
    extraction with the constants of `σ` bound satisfies `WordArrResult` or `WordScalResult`:
    an array of words and a word are not control-flow values. -/
theorem isControlFlow_false_of_wordResult {σ : AbiLayout} {te : TExpr}
    (h : WordArrResult σ (bindConsts σ.consts te) ∨ WordScalResult σ (bindConsts σ.consts te))
    {sa : AState} (hsep : σ.Regions sa) {env : Env} (henv : σ.EnvOf sa env)
    {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (denoteSpine hax64WExit fuel te.erase).run env = (.val v, env')) :
    v.isControlFlow = false := by
  have hrunK : (denoteSpine hax64WExit fuel (bindConsts σ.consts te).erase).run env =
      (.val v, env') := by
    rw [run_bindConsts_of_envOf hax64WExit fuel te henv]
    exact hrun
  rcases h with h | h
  · obtain ⟨zs, rfl⟩ := h sa env fuel v env' hsep henv hrunK
    rfl
  · obtain ⟨z, rfl⟩ := h sa env fuel v env' hsep henv hrunK
    rfl

end CatCrypt.Crypto.SecureCompilation.Haxc
