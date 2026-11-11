/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeConsts

/-!
# The front, the chain and the back half of a module composed

The program of `nfDialect` that the translation `haxToNF` returns on a module `m` runs through the
chain `extChain` at the declared procedures of `m` and through `compileRegion` at the data of its
linked functions. `NFProgCallTreeRegion.ruttF_extChain_compileRegion` relates the call tree of
that program at `linkReader` to the target trees of the calling body. A source tree related to
the call tree with the calls of names that are not linked answered by the leaf table of the table
of the linked functions (`answerOut`, at `FrontRE`, `FrontRA`, `FrontRR`) is therefore related to
the target trees at the compositions of the three relations (`ruttF_front_compileRegion`), when
every event the chain relates to a target event is a call of a linked function.

## Main definitions

* `keepL`: the calls of the linked functions of a module.

## Main results

* `RuttF.answerOut`: a relation by `RuttF` whose related source events satisfy the predicate
  holds from the tree with the other events answered.
* `ruttF_front_compileRegion`: a source tree related to the call tree of the program of
  `haxToNF` by the front is related by `RuttF` to the target trees of the calling body of every
  result of `compileRegion` on its chain.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeR3

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (tableOf entryCtx EntryVals)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv nfCallSig NFCall treeAt)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig leafHandler linkReader
  OutRel ExtRE ExtRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt (MapRE MapRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (CompRE CompRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack (BackRE BackRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCompose (answerOut FrontRE FrontRA
  FrontRR)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (ChainRE ChainRA ChainRR)
open _root_.Hax

/-- **A relation with a family from the tree with the other events answered.** When every source
    event that `RE` relates to a target event satisfies `keep`, a relation by `RuttF` at the source
    handler `h₁` holds from the tree whose events outside `keep` are answered by `h₁`. -/
theorem RuttF.answerOut {E₁ E₂ : EventSig} {R₁ R₂ : Type} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} (keep : E₁.Event → Bool)
    (hkeep : ∀ e₁ e₂, RE e₁ e₂ → keep e₁ = true) {t₁ : CallTree E₁ R₁}
    {T : Nat → CallTree E₂ R₂} (h : RuttF h₁ RE RA RR Fail t₁ T) :
    RuttF h₁ RE RA RR Fail (NFProgCallTreeCompose.answerOut keep h₁ t₁) T := by
  induction h with
  | ret n hT h => exact .ret n hT h
  | fail h => exact .fail h
  | @vis e₁ e₂ k₁ T K n hT he _ ih =>
    simp only [NFProgCallTreeCompose.answerOut, hkeep _ _ he, ite_true]
    exact .vis n hT he ih
  | @skip e₁ k₁ T _ ih =>
    by_cases hk : keep e₁ = true
    · simp only [NFProgCallTreeCompose.answerOut, hk, ite_true]
      exact .skip ih
    · simp only [NFProgCallTreeCompose.answerOut, hk, Bool.false_eq_true, ite_false]
      exact ih

/-- The calls of the linked functions of a module: a leaf call whose name is the name of a linked
    function of `m`. -/
def keepL (m : HaxModule) (e : leafSig.Event) : Bool :=
  m.linked.any fun l => l.name == e.name

/-- **The front composed with the chain and the back half.** Let `haxToNF` return `q` on the
    module `m`, the chain `extChain` at the declared procedures of `m` return `p` on `q`, and
    `compileRegion` return a result on `p`, which has a `call`. Under the conditions of
    `NFProgCallTreeRegion.ruttF_extChain_compileRegion` at the table of the linked functions of `m`,
    and when every event the chain relates to a target event is a call of a linked function of `m`,
    every source tree related by the front (`FrontRE`, `FrontRA`, `FrontRR`, the failed source leaf
    `srcFail`) to the call tree of `q` at `linkReader` with the other calls answered by the leaf
    table is related by `RuttF` to the target trees of the calling body, at the compositions of the
    relations of the front, of the chain and of the back half. -/
theorem ruttF_front_compileRegion {m : HaxModule} {σ : AbiLayout}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : haxToNF σ m = some q)
    {p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]}
    (hp : (extChain (linkedDecls m (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) _ q.1).run q.2
      = some p)
    {a : AbiNames} {linked : List CalleeData} {P : Lprog} {bytes : List (BitVec 8)}
    (h1 : compileRegion σ a p linked = some (P, bytes)) (hcf : p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (x : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs x = .ret none)
    (h₂ : ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e)
    (h₃ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hh₂ : ∀ e₁ e₂, ExtRE e₁ e₂ → ExtRA e₁ e₂
      (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁) (h₂ e₂))
    (hh₃ : ∀ e₁ e₂, MapRE catToJasmin (fun x => ctTransTy x) e₁ e₂ →
      MapRA catToJasmin (fun x => ctTransTy x) e₁ e₂ (h₂ e₁) (h₃ e₂))
    (hinner : ∀ (f : String) (as rs : List JasminTy) (x : Ctxt.Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₃ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    (hhC : ∀ e₁ e₂, ChainRE e₁ e₂ → ChainRA e₁ e₂
      (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁) (h₃ e₂)) :
    ∃ (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
        ([mapTy (catTy q.1)].map NarrowWords.wideTy)) (T : CalleeTab) (b : Lcmd)
        (pc : List RInstr),
      NarrowWords.narrowPrep p = some q'
      ∧ T.fns.Sublist linked ∧ calleeBytes (some T) b = some bytes ∧ calleeProg T b = some pc
      ∧ ((∀ e₁ e₂, ChainRE e₁ e₂ → keepL m e₁ = true) →
        ∀ (kind : String → CalleeKind) (X : String → CalleeRun),
        (∀ c ∈ T.fns, (kind c.name).Top c ∧ (kind c.name).Spec (X c.name)) →
        ∀ {PT : LprogIsa.ProcTable}, (∀ c ∈ T.fns, PT c.name = some (kind c.name).summary) →
        (∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none)
          ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true) →
        (∀ f ∈ T.names, innerHead f = false) →
        ∀ (sa : AState), σ.Regions sa → ∀ (env : Env), σ.EnvOf sa env →
        ∀ (V : Ctxt.Valuation (entryCtx (abiEntry σ))), EntryVals env (abiEntry σ) V →
        ∀ (tf : Nat) {G : NFCall jasminDialect → Prop}, (∀ e, G e → EvOK T e) →
        AllEv G (mfTree tf q' (NarrowWords.mapVal (ctMapValD (mapVal V)))) →
        ∀ (sym : Nat → String) (rd : String → AState → List Value),
        (∀ ev, G ev → ∃ pr, PT ev.name = some pr ∧ pr.arity = ev.argTys.length
          ∧ pr.arrArgs = arrArgsOf ev.argTys
          ∧ (pr.result (wordsOf ev.args) = none → h₃ ev = none)) →
        (∀ f ∈ T.names, sym (pc.length + T.entryIdx (T.symPos f)) = f) →
        ∀ (t₀ : CallTree linkSig (Outcome × Env)),
        RuttS (linkHandler m) (FrontRE m) FrontRA (FrontRR q.1) srcFail t₀
          (answerOut (keepL m) (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)))
            (treeAt linkReader tE tf q.2 V)) →
        RuttF (linkHandler m) (CompRE (FrontRE m) (CompRE ChainRE (BackRE T)))
          (CompRA (FrontRE m) (CompRE ChainRE (BackRE T)) FrontRA
            (CompRA ChainRE (BackRE T) ChainRA (BackRA PT X)))
          (Relation.Comp (FrontRR q.1) (Relation.Comp (ChainRR q.1) (OutRel fun v sA =>
            σ.ResultOf sa sA (denVal (NarrowWords.wideTy (mapTy (catTy q.1)))
              (Ctxt.Var.lookup (d := jasminDialect)
                (Γ := [NarrowWords.wideTy (mapTy (catTy q.1))])
                (t := NarrowWords.wideTy (mapTy (catTy q.1))) .here v)))))
          srcFail t₀ fun n => targetTree aMachine pc sym rd n 0 sa) := by
  obtain ⟨hfs, -, hlk, -⟩ := haxToNF_eq_some hq
  have hbi : SubTable (m.linkTable CatCrypt.Crypto.Hax.hax64WExit) :=
    subTable_linkBi _ CatCrypt.Crypto.Hax.hax64WExit_subTable
      fun l hl => not_catName_of_linkNameOk (hlk l hl)
  obtain ⟨q', T, b, pc, hq', hsub, hbs, hpc, hR⟩ :=
    NFProgCallTreeRegion.ruttF_extChain_compileRegion hbi
      (linkedDecls m (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) tE htE h₂ h₃ hh₂ hh₃ hinner
      hhC hp h1 hcf
  refine ⟨q', T, b, pc, hq', hsub, hbs, hpc, fun hkeep kind X hK PT hTc hword hin sa hreg env
    henv V hV tf G hGT hG sym rd hsum hsym t₀ hfront => ?_⟩
  have hback := hR kind X hK hTc hword hin sa hreg env henv V hV tf tf le_rfl hGT hG sym rd hsum
    hsym
  exact NFProgCallTreeCalls.RuttS.trans_ruttF
    (fun e₀ e₁ he => NFProgCallTreeCompose.frontRA_linkHandler m _ he)
    (fun r₀ r₁ hr hf => by subst hf; exact NFProgCallTreeCompose.srcFail_of_frontRR hr)
    hfront (RuttF.answerOut (keepL m) (fun e₁ e₂ he => by
      obtain ⟨e', he', -⟩ := he
      exact hkeep _ _ he') hback)

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeR3
