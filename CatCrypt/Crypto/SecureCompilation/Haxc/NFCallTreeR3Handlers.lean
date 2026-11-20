/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3TypedAns
public import CatCrypt.Crypto.SecureCompilation.Haxc.R3UHandlerFacts

/-!
# The handlers of the linked functions of a module, and `R3StatementFA TypedAns` without them

The call environment of `jasminDialect` of a module `m` answers a reduce-multiply head
(`montTag?`) by `MontDeg.redcMulW`, a field head (`fieldHeadB`) by the `u64` builtin table, and
every other name by the table of the linked functions of `m` over `Hax.hax64WExit`:

  `linkedEnvJ m := montEnv (fieldEnv (tableEnv (m.linkTable hax64WExit)))`.

The handler of `jasminDialect` answers a call event by `linkedEnvJ m`; the handler of
`catCryptDialect` answers it by `catEnvOf (linkedEnvJ m)`. At every leaf call of a signature of
the translated calls (`ExtEv`), these handlers answer as the leaf table of the module:

* at a head that is not inner, `linkedEnvJ m` is `tableEnv` of the linked table, and the
  answer is that of `implementedBy_tableEnv`;
* at a field head, no linked function has the name, so the leaf table is `hax64WExit`, a
  sub-table of `hax64Builtins` (`hax64WExit_sub`), which `fieldEnv` reads;
* at a reduce-multiply head the leaf table answers nothing (`hax64WExit_of_montTag?`).

The widening of `narrowPrep` is the identity at the types of these events (`reg 64` and
`stackArr 64 n`), so the relation of the whole chain follows from the two stage relations.

## Main results

* `linkedHandlerJ_inner`, `linkedHandler_mapRA`, `linkedHandler_extRA`,
  `linkedHandler_chainRA`: the four handler hypotheses of `r3FA_of_shape_int`.
* `r3FA_of_shape_linkedHandlers`: the conclusion of `R3StatementFA TypedAns` at a module from
  its shape, at the handlers of its linked functions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Handlers

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (tableOf entryCtx dec encAll hax64NFWordTy)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn linkBi_of_find_none)
open CatCrypt.Crypto.Hax.NFInline (crateOp)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv nfCallSig callHandler)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig leafHandler ExtRE ExtRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt (MapRE MapRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree innerHead
  montEnv_fieldEnv_inner montEnv_fieldEnv_outer)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montEnv montEnv_of_none montTag?
  hax64WExit_of_montTag?)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (ChainRE ChainRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (ExtEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle (RuttFA SkipAns TypedAns
  contractRACA)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open _root_.Hax.FieldTag (fieldHeadB)
open Ctxt (Valuation)

/-! ## The handlers -/

/-- **The call environment of `jasminDialect` of the linked functions of `m`**: a
    reduce-multiply head is answered by `montEnv`, a field head by the `u64` builtin table
    (`fieldEnv`), every other name by `tableEnv` at the table of the linked functions of `m`
    over `Hax.hax64WExit`. -/
def linkedEnvJ (m : HaxModule) : CallEnv jasminDialect :=
  montEnv (fieldEnv (tableEnv (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)))

/-- The handler of the call events of `jasminDialect` at `linkedEnvJ m`. -/
def linkedHandlerJ (m : HaxModule) :
    ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e :=
  callHandler (linkedEnvJ m)

/-- The handler of the call events of `catCryptDialect` at `catEnvOf (linkedEnvJ m)`. -/
def linkedHandlerC (m : HaxModule) :
    ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e :=
  callHandler (catEnvOf (linkedEnvJ m))

/-! ## Inner heads and the lowering to `jasminDialect` -/

/-- **At an inner head the handler of `jasminDialect` is the environment of the inner heads.** -/
theorem linkedHandlerJ_inner (m : HaxModule) (f : String) (as rs : List JasminTy)
    (x : Valuation (d := jasminDialect) as) (hf : innerHead f = true) :
    linkedHandlerJ m ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x :=
  montEnv_fieldEnv_inner hf _ _ as rs x

/-- **The two handlers are related along the lowering `catToJasmin`** at every call event. -/
theorem linkedHandler_mapRA (m : HaxModule) (e₁ : (nfCallSig catCryptDialect).Event)
    (e₂ : (nfCallSig jasminDialect).Event)
    (h : MapRE catToJasmin (fun x => ctTransTy x) e₁ e₂) :
    MapRA catToJasmin (fun x => ctTransTy x) e₁ e₂ (linkedHandlerC m e₁)
      (linkedHandlerJ m e₂) := by
  obtain ⟨f, as, rs, x⟩ := e₁
  subst h
  intro y hy
  have ht := catEnvOf_transports (linkedEnvJ m) f as rs x trivial
  change (catEnvOf (linkedEnvJ m)).call f as rs x = some y at hy
  apply heq_of_eq
  change (linkedEnvJ m).call f (as.map mapTy) (rs.map mapTy)
    (transArgs mapTy (fun x => ctTransTy x) x) = _
  rw [ht, hy]
  rfl

/-! ## The leaf table and the handler of `catCryptDialect` -/

/-- No linked function of `m` has an inner head as its name. -/
theorem find?_eq_none_of_innerHead {m : HaxModule}
    (hin : ∀ l ∈ m.linked, innerHead l.name = false) {f : String} (hf : innerHead f = true) :
    m.linked.find? (·.name == f) = none :=
  List.find?_eq_none.mpr fun l hl h => by
    have := hin l hl
    simp_all

/-- **At a leaf call of a signature of the translated calls, the handler of `catCryptDialect`
    answers as the leaf table of `m`.** -/
theorem linkedHandler_extRA {m : HaxModule} (hin : ∀ l ∈ m.linked, innerHead l.name = false)
    (e₁ : leafSig.Event) (e₂ : (nfCallSig catCryptDialect).Event) (h : ExtRE e₁ e₂)
    (hX : ExtEv e₁) :
    ExtRA e₁ e₂ (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁)
      (linkedHandlerC m e₂) := by
  obtain ⟨f, as, r, xs⟩ := e₁
  obtain ⟨g, bs, rs, ws⟩ := e₂
  obtain ⟨hg, hb, hrs, hrel⟩ := h
  dsimp only at hg hb hrs hrel
  subst hg hb hrs
  have hX' : (as.all wordArrTy && linkResOk r) = true := hX
  simp only [Bool.and_eq_true, List.all_eq_true] at hX'
  obtain ⟨has, hr⟩ := hX'
  intro y hy
  change ((m.linkTable CatCrypt.Crypto.Hax.hax64WExit) g (encAll as xs)).bind (dec r)
    = some y at hy
  suffices hsuf : ∃ bi : _root_.Hax.Builtins,
      (∀ rs' x', (linkedEnvJ m).call g ((as.map catTy).map mapTy) rs' x'
        = (tableEnv bi).call g ((as.map catTy).map mapTy) rs' x') ∧
      (tableOf bi).call g as r xs = some y by
    obtain ⟨bi, hE, hy'⟩ := hsuf
    obtain ⟨y', hy'', hv⟩ := implementedBy_tableEnv bi g as r hr has xs ws y hrel hy'
    refine ⟨y', ?_, hv⟩
    apply heq_of_eq
    change ((linkedEnvJ m).call g ((as.map catTy).map mapTy) ([catTy r].map mapTy)
      (transArgs mapTy (fun x => ctTransTy x) ws)).map backArgs = _
    rw [hE]
    exact hy''
  cases hmt : montTag? g with
  | some q =>
    have hnone := find?_eq_none_of_innerHead hin (f := g) (by simp [innerHead, hmt])
    rw [CatCrypt.Crypto.Hax.HaxModule.linkTable, linkBi_of_find_none _ _ hnone,
      hax64WExit_of_montTag? hmt] at hy
    cases hy
  | none =>
    cases hfh : fieldHeadB g with
    | true =>
      have hnone := find?_eq_none_of_innerHead hin (f := g) (by simp [innerHead, hfh])
      refine ⟨_root_.Hax.hax64Builtins, fun rs' x' =>
        (montEnv_of_none _ hmt _ _ _).trans (fieldEnv_of_fieldHeadB _ hfh _ _ _), ?_⟩
      rw [CatCrypt.Crypto.Hax.HaxModule.linkTable, linkBi_of_find_none _ _ hnone] at hy
      obtain ⟨v, hv, hd⟩ := Option.bind_eq_some_iff.mp hy
      change (_root_.Hax.hax64Builtins g (encAll as xs)).bind (dec r) = some y
      rw [CatCrypt.Crypto.Hax.hax64WExit_sub hv]
      exact hd
    | false =>
      exact ⟨m.linkTable CatCrypt.Crypto.Hax.hax64WExit, fun rs' x' =>
        montEnv_fieldEnv_outer (by simp [innerHead, hmt, hfh]) _ _ _ _, hy⟩

/-! ## Widening at the types of the translated calls -/

/-- A type fixed by the widening: the `64`-bit register or a stack array of `64`-bit words. -/
def WideFix (t : JasminTy) : Prop := t = .reg 64 ∨ ∃ n, t = .stackArr 64 n

/-- Widening fixes a list of types of `WideFix` and transports a valuation at it to itself. -/
theorem wideFix_transArgs {ts : List JasminTy} (h : ∀ t ∈ ts, WideFix t) :
    ts.map NarrowWords.wideTy = ts ∧ ∀ x : Valuation (d := jasminDialect) ts,
      transArgs NarrowWords.wideTy (fun x => NarrowWords.transTy x) x ≍ x := by
  have hm : ts.map NarrowWords.wideTy = ts := by
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      rcases h t List.mem_cons_self with rfl | ⟨n, rfl⟩ <;>
        simp [ih fun s hs => h s (List.mem_cons_of_mem _ hs)]
  exact ⟨hm, NarrowWords.transArgs_heq_of_wide hm⟩

/-- The image under `mapTy ∘ catTy` of a type of words and word arrays is fixed by widening. -/
theorem wideFix_of_wordArrTy {s : NfTy} (h : wordArrTy s = true) :
    WideFix (mapTy (catTy s)) := by
  unfold wordArrTy at h
  split at h
  · exact .inr ⟨_, rfl⟩
  · unfold hax64NFWordTy at h
    split at h <;> first | exact .inl rfl | cases h

/-- The image under `mapTy ∘ catTy` of a result type of `linkResOk` is fixed by widening. -/
theorem wideFix_of_linkResOk {s : NfTy} (h : linkResOk s = true) :
    WideFix (mapTy (catTy s)) := by
  rcases linkResOk_iff.mp h with rfl | ⟨n, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨n, rfl⟩

/-- **The handler of a call environment is related to itself along the widening** at a call
    event whose types are fixed by widening. -/
theorem callHandler_mapRA_widen (E : CallEnv jasminDialect)
    (e₁ e₂ : (nfCallSig jasminDialect).Event)
    (hm : MapRE NarrowWords.widenP (fun x => NarrowWords.transTy x) e₁ e₂)
    (ha : ∀ t ∈ e₁.argTys, WideFix t) (hr : ∀ t ∈ e₁.resTys, WideFix t) :
    MapRA NarrowWords.widenP (fun x => NarrowWords.transTy x) e₁ e₂ (callHandler E e₁)
      (callHandler E e₂) := by
  obtain ⟨f, as, rs, x⟩ := e₁
  subst hm
  obtain ⟨has, hx⟩ := wideFix_transArgs ha
  obtain ⟨hrs, hy⟩ := wideFix_transArgs hr
  intro y hyE
  change E.call f as rs x = some y at hyE
  have key : ∀ (as' rs' : List JasminTy) (x' : Valuation (d := jasminDialect) as')
      (y' : Valuation (d := jasminDialect) rs'), as' = as → rs' = rs → x' ≍ x → y' ≍ y →
      E.call f as' rs' x' ≍ (some y' : Option (Valuation (d := jasminDialect) rs')) := by
    intro as' rs' x' y' h1 h2 h3 h4
    subst h1 h2
    cases h3
    cases h4
    exact heq_of_eq hyE
  exact key _ _ _ _ has hrs (hx x) (hy y)

/-- **At a leaf call of a signature of the translated calls, the handler of `jasminDialect`
    answers as the leaf table of `m` along the chain** `extChain` followed by `narrowPrep`. -/
theorem linkedHandler_chainRA {m : HaxModule} (hin : ∀ l ∈ m.linked, innerHead l.name = false)
    (e₀ : leafSig.Event) (e₂ : (nfCallSig jasminDialect).Event) (_h : ChainRE e₀ e₂)
    (hX : ExtEv e₀) :
    ChainRA e₀ e₂ (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₀)
      (linkedHandlerJ m e₂) := by
  intro e₁' he₁' hw
  refine ⟨linkedHandlerJ m e₁', ?_, ?_⟩
  · intro e₁ he₁ hm
    exact ⟨linkedHandlerC m e₁, linkedHandler_extRA hin e₀ e₁ he₁ hX,
      linkedHandler_mapRA m e₁ e₁' hm⟩
  · obtain ⟨e₁, ⟨-, hb, hrs, -⟩, hm⟩ := he₁'
    have hX' : (e₀.argTys.all wordArrTy && linkResOk e₀.ret) = true := hX
    simp only [Bool.and_eq_true, List.all_eq_true] at hX'
    subst hm
    refine callHandler_mapRA_widen _ _ _ hw ?_ ?_
    · intro t ht
      change t ∈ e₁.argTys.map mapTy at ht
      rw [hb] at ht
      simp only [List.mem_map] at ht
      obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := ht
      exact wideFix_of_wordArrTy (hX'.1 s hs)
    · intro t ht
      change t ∈ e₁.resTys.map mapTy at ht
      rw [hrs] at ht
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at ht
      subst ht
      exact wideFix_of_linkResOk hX'.2

/-! ## The conclusion of `R3StatementFA TypedAns` at the handlers of the linked functions -/

/-- **The conclusion of `R3StatementFA TypedAns` at a module, from its shape, at the handlers of
    its linked functions.** The statement of `NFCallTreeR3TypedAns.r3FA_of_shape_int` with the
    handlers `linkedHandlerC m` and `linkedHandlerJ m` of the call environment `linkedEnvJ m`,
    which discharge its four handler hypotheses. -/
theorem r3FA_of_shape_linkedHandlers {m : HaxModule} {σ : AbiLayout} {fname : String}
    {P : Lprog} {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none)
    (hcf : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (x : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs x = .ret none)
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (hword : ∀ c ∈ m.linked.filterMap LinkedFn.calleeData, (∃ r, c.res = .reg r)
      ∧ c.arrArgs = (fun _ => none) ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true)
    (hin : ∀ l ∈ m.linked, innerHead l.name = false)
    (hev : ∀ (T : CalleeTab), T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData) →
      ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
        (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)])
        (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
          ([mapTy (catTy q.1)].map NarrowWords.wideTy)), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → NarrowWords.narrowPrep p = some q' →
      ∀ (tf : Nat) (V : Ctxt.Valuation (entryCtx (abiEntry σ))),
        AllEv (EvOK T) (mfTree tf q' (NarrowWords.mapVal (ctMapValD (mapVal V)))))
    (hspine : NFCallTreeInlineSpine.spineArgsOk m.entry.erase = true)
    (hfs : ∀ f ∈ m.fns, NFCallTreeInlineSpine.spineArgsOk f.texpr.erase = true)
    (hint : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg nfDialect (entryCtx (abiEntry σ)) [q.1]), haxToNF σ m = some q →
      nfSrcProgC (m.prepared nfBody ++ m.linkedFns) σ (bindConsts σ.consts m.entry)
        = some ⟨q.1, p⟩ → ∀ o, p.HasOp o →
          NFCallTreeFrontModule.OpOk NFCallTreeGoodCall.IntArgFree o)
    (hgood : ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → NFCallTreeFrontModule.OpOk (NFCallTreeFrontModule.GoodCall m) o) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel,
          RuttFA (SkipAns TypedAns m) (contractREG m) (contractRACA TypedAns m) (resRel σ sa)
            srcFail
            (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel
              m.entry.erase env)
            (fun fuelT => targetTree aMachine pc sym (linkRead m) fuelT 0 sa) :=
  NFCallTreeR3TypedAns.r3FA_of_shape_int hc hnd hk hn hpt hcf tE htE
    (linkedHandlerC m) (linkedHandlerJ m)
    (fun e₁ e₂ h hX => linkedHandler_extRA hin e₁ e₂ h hX)
    (fun _ e₁ e₂ _ _ hm => linkedHandler_mapRA m e₁ e₂ hm)
    (fun f as rs x hf => linkedHandlerJ_inner m f as rs x hf)
    (fun e₁ e₂ h hX => linkedHandler_chainRA hin e₁ e₂ h hX)
    hpar hword hin hev hspine hfs hint hgood

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Handlers
