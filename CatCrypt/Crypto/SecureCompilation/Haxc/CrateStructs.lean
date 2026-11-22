/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
public import HaxLean.StructTuple

/-!
# Records of a crate as tuples

The front of `compileA` has tuples and no records. A typed extraction writes a record as calls
of the struct heads of its layout `Hax.StructFieldTys`: a construction, a field read, a field
update. `structFns` rewrites the named extractions of a crate and `structTExpr` a single one,
by `Hax.tStructToTuple` at the reserved name `structVar`, before the functions of a module are
made, so that `modFnTy` reads a record parameter or result as a tuple type. `structModule` is
the same rewrite on a module. At the empty layout all three are the identity.

The source semantics of a program with records, `haxRunsStruct`, is the source relation of
`haxRuns` with the table `Hax.structBi` of the struct heads over the base table `hax64WExit`.
A run of it is a run of `haxRuns` on the rewritten module when `structModuleOk` holds, a check
by evaluation: no function and no linked function has the name of a struct head, and each body
satisfies the premises of `Hax.denoteSpine_tStructToTuple`. The compiler theorem
`haxc_correct_auto` on the rewritten module then reads back every run of the record source.

The module of a crate function binds the constants of the crate in each callee after the
rewrite, and the rewrite changes the type of such a binding. `StructImage` therefore relates
the two modules up to the erasure of the bodies, which is all the source semantics reads.

## Main definitions

* `structTExpr`, `structFns`, `structModule`: the rewrite of an extraction, of the named
  extractions of a crate, and of a module.
* `structModuleOk`: the check of the side conditions.
* `haxRunsStruct`: the source semantics of a module with records.
* `StructImage`: a module whose bodies erase to the rewrite of those of another.
* `recordSource`: the module with records of which a module of a rewritten crate is the image.

## Main results

* `structTExpr_nil`, `structFns_nil`, `structModule_nil`, `haxRunsStruct_nil`: the empty
  layout.
* `haxRuns_of_structImage`, `haxRuns_structModule`: a run of a module with records is a run of
  the rewritten module.
* `structImage_recordSource`: a module made from a rewritten crate is the image of its record
  source.
* `haxc_correct_structImage`, `haxc_correct_structModule`: the compiler theorem on a module
  with records.
* `PairExample.ok`, `PairExample.runs`: a record built and projected in a function on scalars.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.CrateStructs

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts HaltsC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute (entryA)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (RunSafe)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (runA)
open CatCrypt.Crypto.SecureCompilation.SepLogic.Addr (AccessIn)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (HaltsO)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.Hax (HaxModule ModFn LinkedFn refBi refBi_succ refBi_of_find_none linkBi
  linkBi_of_find_none linkBi_of_find_some hax64WExit)
open _root_.Hax (StructFieldTys TExpr Value Env Builtins structHead? structBi tStructToTuple
  spineStructOk noVarRef denoteSpine_tStructToTuple_of_structTab)
open _root_.Hax.StructTuple (StructTab isErr)
open _root_.Hax.InlineLocalClosures (denoteSpine)

/-! ## The rewrite -/

/-- The reserved name that the rewrite of a field update binds. A Rust identifier contains no
    `#`, and `structModuleOk` checks that no body reads the name. -/
def structVar : String := "struct#t"

/-- **The records of an extraction as tuples**: `Hax.tStructToTuple` at the layout `sf` and
    the reserved name `structVar`. -/
def structTExpr (sf : StructFieldTys) (te : TExpr) : TExpr :=
  tStructToTuple sf structVar te

/-- **The records of the named extractions of a crate as tuples.** The names and their order
    are kept. The result is the input of `modFnsE`. -/
def structFns (sf : StructFieldTys) (gs : List (String × TExpr)) : List (String × TExpr) :=
  gs.map fun g => (g.1, structTExpr sf g.2)

/-- **The records of a module as tuples**: the rewrite of the entry and of the body of each
    function. The typed parameters and results of the functions, the depth and the linked
    functions are kept. -/
def structModule (sf : StructFieldTys) (m : HaxModule) : HaxModule :=
  { m with
    entry := structTExpr sf m.entry
    fns := m.fns.map fun f => { f with texpr := structTExpr sf f.texpr } }

/-- At the empty layout no application head has a struct role. -/
theorem structHead?_nil (f : String) : structHead? [] f = none := by
  simp [structHead?, _root_.Hax.structUpdateRole?, _root_.Hax.structFieldRole?]

/-- At the empty layout the table of the struct heads is the base table. -/
theorem structBi_nil (bi : Builtins) : structBi [] bi = bi := by
  funext f args
  simp [structBi, structHead?_nil]

/-- At the empty layout the rewrite of an extraction is the identity. -/
theorem structTExpr_nil (te : TExpr) : structTExpr [] te = te := by
  unfold structTExpr
  have map_fixed : ∀ {α : Type} (f : α → α) (l : List α), (∀ a ∈ l, f a = a) → l.map f = l :=
    fun f l h => (List.map_congr_left (g := id) h).trans (List.map_id l)
  induction te using TExpr.ind with
  | match_ ty s arms ihs iha =>
    simp only [tStructToTuple, tStructToTuple.goKind, _root_.Hax.tStructToTuple_goArms, ihs,
      List.length_nil, _root_.Hax.tyStructToTuple]
    grind
  | _ =>
    simp_all [tStructToTuple, tStructToTuple.goKind, _root_.Hax.structApp, structHead?_nil,
      _root_.Hax.tyStructToTuple]

/-- At the empty layout the rewrite of the extractions of a crate is the identity. -/
theorem structFns_nil (gs : List (String × TExpr)) : structFns [] gs = gs := by
  simp [structFns, structTExpr_nil]

/-- At the empty layout the rewrite of a module is the identity. -/
theorem structModule_nil (m : HaxModule) : structModule [] m = m := by
  simp [structModule, structTExpr_nil]

/-- The extraction of a name in the rewritten crate is the rewrite of its extraction. -/
theorem lookup_structFns (sf : StructFieldTys) (gs : List (String × TExpr)) (g : String) :
    (structFns sf gs).lookup g = (gs.lookup g).map (structTExpr sf) := by
  induction gs <;> grind [structFns, List.lookup]

/-! ## The side conditions -/

/-- The side conditions of the rewrite on a body: it does not read the reserved name and its
    spine satisfies `Hax.spineStructOk`. -/
def structBodyOk (sf : StructFieldTys) (te : TExpr) : Bool :=
  noVarRef structVar te.erase && spineStructOk sf structVar te

/-- **The check of the rewrite on a module with records**: the layout is empty, or no function
    and no linked function has the name of a struct head and the entry and each function body
    satisfy `structBodyOk`. -/
def structModuleOk (sf : StructFieldTys) (m : HaxModule) : Bool :=
  sf.isEmpty ||
    (m.fns.all (fun f => (structHead? sf f.name).isNone && structBodyOk sf f.texpr)
      && m.linked.all (fun l => (structHead? sf l.name).isNone)
      && structBodyOk sf m.entry)

/-! ## Images of the rewrite -/

/-- The function `f'` is an image of the function `f` with records: it has the name, the
    parameters and the result type of `f`, and its body erases to the rewrite of that of
    `f`. -/
structure StructFnImage (sf : StructFieldTys) (f f' : ModFn) : Prop where
  /-- The name is kept. -/
  name : f'.name = f.name
  /-- The typed parameters are kept. -/
  params : f'.params = f.params
  /-- The result type is kept. -/
  res : f'.res = f.res
  /-- The body erases to the rewritten body. -/
  body : f'.texpr.erase = (structTExpr sf f.texpr).erase

/-- **The module `m'` is an image of the module `m` with records**: the entry erases to the
    rewritten entry, the functions are images in their order, and the depth and the linked
    functions are kept. -/
structure StructImage (sf : StructFieldTys) (m m' : HaxModule) : Prop where
  /-- The entry erases to the rewritten entry. -/
  entry : m'.entry.erase = (structTExpr sf m.entry).erase
  /-- The functions are images in their order. -/
  fns : List.Forall₂ (StructFnImage sf) m.fns m'.fns
  /-- The depth is kept. -/
  depth : m'.depth = m.depth
  /-- The linked functions are kept. -/
  linked : m'.linked = m.linked

/-- The rewritten module is an image of the module. -/
theorem structImage_structModule (sf : StructFieldTys) (m : HaxModule) :
    StructImage sf m (structModule sf m) := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  simp only [structModule, List.forall₂_map_right_iff, List.forall₂_same]
  exact fun f _ => ⟨rfl, rfl, rfl, rfl⟩

/-- An image has no function of a name exactly when the source has none, and the first
    function of a name is the image of the first function of the name in the source. -/
theorem find?_image {sf : StructFieldTys} {fs fs' : List ModFn}
    (h : List.Forall₂ (StructFnImage sf) fs fs') (g : String) :
    (fs.find? (·.name == g) = none ∧ fs'.find? (·.name == g) = none) ∨
      ∃ f f', fs.find? (·.name == g) = some f ∧ fs'.find? (·.name == g) = some f' ∧
        StructFnImage sf f f' := by
  induction h with
  | nil => simp
  | cons hf _ ih => grind [StructFnImage]

/-! ## Source runs -/

/-- **The source semantics of a module with records**: the source relation of `haxRuns` with
    the struct heads of `sf`, a record read as the tuple of its fields (`Hax.structBi`), over
    the base table `hax64WExit`. A function or a linked function of the module is called
    before a struct head. -/
def haxRunsStruct (sf : StructFieldTys) (σ : AbiLayout) (m : HaxModule) (sa : AState)
    (v : Value) : Prop :=
  HaxModule.Runs (structBi sf hax64WExit) σ m (narrowEntry m σ sa) v

/-- At the empty layout the source semantics with records is `haxRuns`. -/
theorem haxRunsStruct_nil (σ : AbiLayout) (m : HaxModule) (sa : AState) (v : Value) :
    haxRunsStruct [] σ m sa v ↔ haxRuns σ m sa v := by
  rw [haxRunsStruct, structBi_nil, haxRuns, haxRunsW]

/-- At the empty layout an image has the reference tables of its source. -/
theorem refBi_image_nil {fs fs' : List ModFn} (h : List.Forall₂ (StructFnImage []) fs fs')
    (bi : Builtins) (fuel n : Nat) : refBi fs' bi fuel n = refBi fs bi fuel n := by
  induction n with
  | zero =>
    funext g vals
    rcases find?_image h g with ⟨h₁, h₂⟩ | ⟨f, f', h₁, h₂, -⟩ <;> simp [refBi, h₁, h₂]
  | succ n ih =>
    funext g vals
    rcases find?_image h g with ⟨h₁, h₂⟩ | ⟨f, f', h₁, h₂, hi⟩
    · simp [refBi, h₁, h₂]
    · rw [refBi_succ _ _ _ _ h₁, refBi_succ _ _ _ _ h₂, ih, hi.params, hi.res, hi.body,
        structTExpr_nil]

/-- **The reference tables of an image answer the calls of the source with records.** When no
    function and no linked function has the name of a struct head and each body satisfies the
    side conditions, the reference table of the source over the struct heads is related by
    `StructTab` to that of the image over the base table, at every depth. -/
theorem structTab_refBi {sf : StructFieldTys} {fs fs' : List ModFn} {ls : List LinkedFn}
    (hi : List.Forall₂ (StructFnImage sf) fs fs')
    (hf : ∀ f ∈ fs, structHead? sf f.name = none ∧ structBodyOk sf f.texpr = true)
    (hl : ∀ l ∈ ls, structHead? sf l.name = none) (bi : Builtins) (fuel : Nat) :
    ∀ n, StructTab sf (refBi fs (linkBi ls (structBi sf bi)) fuel n)
      (refBi fs' (linkBi ls bi) fuel n) := by
  intro n
  induction n with
  | zero =>
    intro g vals v _ h
    rcases find?_image hi g with ⟨h₁, h₂⟩ | ⟨f, f', h₁, -, -⟩
    · rw [refBi_of_find_none _ _ _ _ h₁] at h
      grind [structBi, refBi, linkBi]
    · simp [refBi, h₁] at h
  | succ n ih =>
    intro g vals v _ h
    rcases find?_image hi g with ⟨h₁, h₂⟩ | ⟨f, f', h₁, h₂, him⟩
    · rw [refBi_of_find_none _ _ _ _ h₁] at h
      grind [structBi, refBi, linkBi]
    · obtain ⟨hn, hb⟩ := hf f (List.mem_of_find?_eq_some h₁)
      have hg : f.name = g := by simpa using List.find?_some h₁
      subst hg
      simp only [structBi, hn]
      rw [refBi_succ _ _ _ _ h₁] at h
      rw [refBi_succ _ _ _ _ h₂, him.params, him.res, him.body]
      simp only [structBodyOk, Bool.and_eq_true] at hb
      have hr := denoteSpine_tStructToTuple_of_structTab sf structVar fuel f.texpr _ _ ih
        hb.1 hb.2 _ _ (Env.AgreeExcept.rfl' structVar
          (CatCrypt.Crypto.Hax.ImpToNF.paramsEnv (f.params.map (·.1)) vals))
      grind [structTExpr, StateT.run, isErr]

/-- An image is read at the entry state of its source. -/
theorem narrowEntry_image {sf : StructFieldTys} {m m' : HaxModule} (h : StructImage sf m m')
    (σ : AbiLayout) (sa : AState) : narrowEntry m' σ sa = narrowEntry m σ sa := by
  have hn : m'.fns.all (·.name != maskCall) = m.fns.all (·.name != maskCall) := by
    have hfns := h.fns
    generalize m.fns = fs, m'.fns = fs' at hfns ⊢
    induction hfns <;> grind [StructFnImage]
  have hok : narrowOk m' σ = narrowOk m σ := by simp only [narrowOk, hn, h.linked]
  rw [narrowEntry, narrowEntry, hok]

/-- **A run of a module with records is a run of every image of it over the base table**,
    under the check `structModuleOk`. -/
theorem runs_of_structImage {sf : StructFieldTys} {m m' : HaxModule} (hi : StructImage sf m m')
    (hok : structModuleOk sf m = true) (bi : Builtins) (σ : AbiLayout) {sa : AState} {v : Value}
    (hr : HaxModule.Runs (structBi sf bi) σ m sa v) : HaxModule.Runs bi σ m' sa v := by
  obtain ⟨env, fuel, fuelC, env', henv, hrun, hcf⟩ := hr
  simp only [structModuleOk, Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true, List.all_eq_true,
    Option.isNone_iff_eq_none] at hok
  rcases hok with rfl | ⟨⟨hf, hl⟩, he⟩
  · refine ⟨env, fuel, fuelC, env', henv, ?_, hcf⟩
    simpa only [HaxModule.table, HaxModule.linkTable, refBi_image_nil hi.fns, hi.depth, hi.linked,
      hi.entry, structTExpr_nil, structBi_nil] using hrun
  · simp only [structBodyOk, Bool.and_eq_true] at he
    have href := denoteSpine_tStructToTuple_of_structTab sf structVar fuel m.entry _ _
      (structTab_refBi hi.fns hf hl bi fuelC m.depth) he.1 he.2 env env
      (Env.AgreeExcept.rfl' structVar env)
    simp only [HaxModule.table, HaxModule.linkTable] at hrun
    refine ⟨env, fuel, fuelC, _, henv, Prod.ext ?_ rfl, hcf⟩
    simp only [HaxModule.table, HaxModule.linkTable, hi.depth, hi.linked, hi.entry]
    grind [structTExpr, StateT.run, isErr]

/-- **A run of a module with records is a source run of every image of it** (`haxRuns`),
    under the check `structModuleOk`. -/
theorem haxRuns_of_structImage {sf : StructFieldTys} {m m' : HaxModule}
    (hi : StructImage sf m m') (hok : structModuleOk sf m = true) {σ : AbiLayout} {sa : AState}
    {v : Value} (hr : haxRunsStruct sf σ m sa v) : haxRuns σ m' sa v := by
  rw [haxRuns, haxRunsW, narrowEntry_image hi]
  exact runs_of_structImage hi hok hax64WExit σ hr

/-- **A run of a module with records is a source run of the rewritten module**, under the
    check `structModuleOk`. -/
theorem haxRuns_structModule {sf : StructFieldTys} {m : HaxModule}
    (hok : structModuleOk sf m = true) {σ : AbiLayout} {sa : AState} {v : Value}
    (hr : haxRunsStruct sf σ m sa v) : haxRuns σ (structModule sf m) sa v :=
  haxRuns_of_structImage (structImage_structModule sf m) hok hr

/-! ## The module of a crate with records -/

/-- The constants of `cs` that `ModFn.ofTExpr` binds in the extraction `te`: those it reads
    free that are not parameters. -/
def constsRead (cs : List (String × Value)) (te : TExpr) : List (String × Value) :=
  cs.filter fun c => (_root_.Hax.freeVars te.erase).eraseDups.contains c.1 &&
    !(texprPrelude 64 te).any (·.1 == c.1)

/-- The name and the body of a function that `ModFn.ofTExpr` makes. -/
theorem ofTExpr_some {name : String} {te : TExpr} {cs : List (String × Value)} {f : ModFn}
    (h : ModFn.ofTExpr name te cs = some f) :
    f.name = name ∧ f.texpr = bindConsts (constsRead cs te) te := by
  grind [ModFn.ofTExpr, constsRead, Option.bind_eq_some_iff]

/-- The binding of constants commutes with the rewrite up to erasure. -/
theorem erase_bindConsts_structTExpr (sf : StructFieldTys) (te : TExpr) :
    ∀ cs : List (String × Value), (bindConsts cs (structTExpr sf te)).erase =
      (structTExpr sf (bindConsts cs te)).erase := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [bindConsts]
    split <;>
      simp_all [structTExpr, tStructToTuple, tStructToTuple.goKind, TExpr.erase]

/-- **The record source of a module made from a rewritten crate**: the module `m'` with the
    entry `te` and, as body of each function, its extraction in the crate `gs` with the
    constants that the function of `m'` binds. The typed parameters and results are those of
    `m'`, where a record type is a tuple type. -/
def recordSource (sf : StructFieldTys) (cs : List (String × Value))
    (gs : List (String × TExpr)) (te : TExpr) (m' : HaxModule) : HaxModule :=
  { m' with
    entry := te
    fns := m'.fns.map fun f =>
      match gs.lookup f.name with
      | some tg => { f with texpr := bindConsts (constsRead cs (structTExpr sf tg)) tg }
      | none => f }

/-- A function `modFnsE` returns is made by `ModFn.ofTExpr` from an extraction of its list. -/
theorem exists_of_mem_modFnsE {cs : List (String × Value)} {gs : List (String × TExpr)}
    {fs : List ModFn} (h : modFnsE cs gs = .ok fs) {f : ModFn} (hf : f ∈ fs) :
    ∃ g ∈ gs, ModFn.ofTExpr g.1 g.2 cs = some f := by
  induction gs generalizing fs with
  | nil => grind [modFnsE]
  | cons g gs ih =>
    simp only [modFnsE] at h
    rcases he : ModFn.ofTExprE g.1 g.2 cs with r | f₁ <;> rw [he] at h
    · cases h
    rcases hr : modFnsE cs gs with r | fs₁ <;> rw [hr] at h <;> cases h
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨g, List.mem_cons_self, by rw [← ModFn.toOption_ofTExprE, he]; rfl⟩
    · grind

/-- Linking keeps the entry and adds no function. -/
theorem foldl_linkFn_entry_fns (ls : List LinkedFn) (m : HaxModule) :
    (ls.foldl HaxModule.linkFn m).entry = m.entry ∧
      ∀ f ∈ (ls.foldl HaxModule.linkFn m).fns, f ∈ m.fns := by
  induction ls generalizing m <;> grind [HaxModule.linkFn]

/-- **A module made from a rewritten crate is the image of its record source.** Let `sel` be
    extractions of the rewritten crate `structFns sf gs`, each under its name, let `modFnsE`
    make the functions `fs` of them, and link any functions `ls` in the module of the
    rewritten entry and `fs`. The result is an image of `recordSource` at the original crate
    and entry. This is the form of the module of a crate function. -/
theorem structImage_recordSource (sf : StructFieldTys) (cs : List (String × Value))
    (gs sel : List (String × TExpr)) (te : TExpr) (fs : List ModFn) (depth : Nat)
    (ls : List LinkedFn) (hsel : ∀ g ∈ sel, (structFns sf gs).lookup g.1 = some g.2)
    (hfs : modFnsE cs sel = .ok fs) :
    let m' := ls.foldl HaxModule.linkFn { entry := structTExpr sf te, fns := fs, depth := depth }
    StructImage sf (recordSource sf cs gs te m') m' := by
  intro m'
  obtain ⟨he, hsub⟩ := foldl_linkFn_entry_fns ls
    { entry := structTExpr sf te, fns := fs, depth := depth }
  refine ⟨congrArg TExpr.erase he, ?_, rfl, rfl⟩
  simp only [recordSource, List.forall₂_map_left_iff, List.forall₂_same]
  intro f hf
  obtain ⟨g, hg, hfg⟩ := exists_of_mem_modFnsE hfs (hsub f hf)
  obtain ⟨hname, hbody⟩ := ofTExpr_some hfg
  have hlk := hsel g hg
  rw [lookup_structFns, Option.map_eq_some_iff] at hlk
  obtain ⟨tg, htg, hte⟩ := hlk
  rw [hname, htg]
  exact ⟨hname, rfl, rfl, by rw [hbody, ← hte, erase_bindConsts_structTExpr]⟩

/-! ## The compiler theorem -/

/-- **The compiler theorem on a module with records, at an image.** Let `m'` be an image of
    the module `m` with records (`StructImage`) and let the check `structModuleOk` hold of
    `m`. When `compileA` returns bytes on `m'`, every value of a source run of `m` with the
    table of the struct heads is read back as `haxc_correct_auto` states. -/
theorem haxc_correct_structImage {sf : StructFieldTys} {m m' : HaxModule}
    (hi : StructImage sf m m') (hok : structModuleOk sf m = true)
    (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m' σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : haxRunsStruct sf σ m sa v)
    (hnd : (m'.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m'.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ ∃ body frame fuel s zf, runA frame body fuel (entryA σ sa) false = some (s, zf)
          ∧ RunSafe frame body (AccessIn (layoutMem σ sa) frame body) fuel (entryA σ sa) false)
      ∨ ∃ cs : List CalleeData, cs.Sublist (m'.linked.filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) :=
  haxc_correct_auto m' σ fname P bytes hc sa hsep v (haxRuns_of_structImage hi hok hrun) hnd hk

/-- **The compiler theorem on a module with records.** For every module `m`, layout `σ` and
    struct layout `sf` with `structModuleOk sf m`: when `compileA` returns bytes on the
    rewritten module `structModule sf m`, every value of a source run of `m` with the table of
    the struct heads is read back as `haxc_correct_auto` states. -/
theorem haxc_correct_structModule (sf : StructFieldTys) (m : HaxModule)
    (hok : structModuleOk sf m = true) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA (structModule sf m) σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : Value) (hrun : haxRunsStruct sf σ m sa v)
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
              ∧ σ.ResultOf sa sa' v) :=
  haxc_correct_structImage (structImage_structModule sf m) hok σ fname P bytes hc sa hsep v
    hrun hnd hk

/-! ## An instance -/

namespace PairExample

/-- The type of a machine word. -/
def wordTy : _root_.Hax.ImpType := .uint .w64

/-- The layout of a record with two fields. -/
def layout : StructFieldTys := [("Pair", [("x", wordTy), ("y", wordTy)])]

/-- The type of the record. -/
def pairTy : _root_.Hax.ImpType := .adt "Pair" []

/-- A function on two words that builds the record of them and returns its second field. -/
def body : TExpr :=
  .mk (.letBind "p"
    (.mk (.app "Pair" [.mk (.var "a") wordTy, .mk (.var "b") wordTy]) pairTy)
    (.mk (.app "Pair.y" [.mk (.var "p") pairTy]) wordTy)) wordTy

/-- The System V layout of the function: two scalars in registers, the result in `%rax`. -/
def abi : AbiLayout where
  args := [⟨"a", "%rdi", .scalar⟩, ⟨"b", "%rsi", .scalar⟩]
  consts := []
  result := .reg "%rax"
  bounds := []
  frameLo := 0
  frameHi := 0

/-- The check holds of the function. -/
theorem ok : structModuleOk layout (HaxModule.single body) = true := by
  decide

/-- From every entry state the function has a source run with records, to the register of
    its second parameter. -/
theorem runs (sa : AState) :
    haxRunsStruct layout abi (HaxModule.single body) sa (.int (sa.regs "%rsi").toNat) := by
  have hc : structHead? layout "Pair" = some (.ctor 2) := by decide
  have hp : structHead? layout "Pair.y" = some (.field 1 2) := by decide
  rw [haxRunsStruct, narrowEntry_of_widths_nil rfl]
  refine (HaxModule.runs_single _ _ _ _ _).2
    ⟨abi.canonEnv sa, 1, _, AbiLayout.envOf_canonEnv _ (by decide) _, Prod.ext ?_ rfl, rfl⟩
  simp [body, abi, AbiLayout.canonEnv, AbiArg.read, TExpr.erase, denoteSpine, structBi, hc, hp,
    _root_.Hax.denote', _root_.Hax.denoteApp', _root_.Hax.denoteArgs', StateT.run, bind,
    StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, Env.extend]

/-- The run is a source run of the rewritten function, the hypothesis of
    `haxc_correct_auto`. -/
theorem runs_rewritten (sa : AState) :
    haxRuns abi (structModule layout (HaxModule.single body)) sa
      (.int (sa.regs "%rsi").toNat) :=
  haxRuns_structModule ok (runs sa)

end PairExample

end CatCrypt.Crypto.SecureCompilation.Haxc.CrateStructs
