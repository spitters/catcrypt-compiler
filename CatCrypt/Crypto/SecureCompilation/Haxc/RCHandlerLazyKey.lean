/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed
public import CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerStateful

/-!
# Robust compilation over keyed source oracles with a lazily drawn key

`RCHandlerKeyed` states robust compilation for keyed source oracles whose key is drawn before
the run. This module states it for the same oracles with the key drawn lazily: the handler state
is an optional key, the first call draws the key by `keyDist` and answers at it, and every later
call answers at the key drawn. A run that makes no call draws no key.

When the distribution of the key is discardable (`Discardable`: sequencing it in front of a
computation and discarding the key gives that computation), interpreting a call tree under the
lazy handler from the empty state is drawing the key first and interpreting the tree under the
handler at that key (`interpSt_lazySt_none_bind`). The equation holds at every tree, so it holds
at every tree of a fuel family and passes to the supremum over the fuel by the ω-continuity of
`bind` in the continuation (`interpStω_lazySt_none`). The source and target computations with the
lazily drawn key are then the computations of `RCHandlerKeyed`, and robust compilation transfers.

## Main definitions

* `lazySt`: a keyed handler family as a stateful handler that draws the key at the first call.
* `lazySrc`, `lazyTgt`: the source and target computations of a keyed oracle with a lazily drawn
  key.
* `HandlerRCLazy`: robust compilation over the target handler families coupled with a keyed
  oracle, with the key drawn lazily on both sides.

## Main results

* `interpSt_lazySt_none_bind`, `interpStOpt_lazySt_none`, `interpStω_lazySt_none`: the
  lazy-to-eager equations.
* `lazySrc_eq_keyedSrc`, `lazyTgt_eq_keyedTgt`: the computations with a lazily drawn key are the
  computations with the key drawn first.
* `handlerRCLazy_of_handlerRCKeyed`: `HandlerRCKeyed` implies `HandlerRCLazy`.
* `haxc_rcHLazy`: for a result of `compileA`, `HandlerRCLazy` at every keyed oracle whose key
  distribution is discardable.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerLazyKey

open OmegaCompletePartialOrder
open scoped ENNReal
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle (Discardable)
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerStateful

/-! ## The lazy handler and the lazy-to-eager equations -/

section Lazy

variable {E : EventSig} {K R : Type}

/-- **A keyed handler family as a stateful handler with a lazily drawn key**: the handler state is
    an optional key. At the state `some k` a call is answered by the handler at `k` and the
    state is kept; at the state `none` the key is drawn by `μ` and the call is answered as at
    `some k`. -/
noncomputable def lazySt (μ : SPComp K) (a : K → ∀ e : E.Event, SPComp (E.Resp e)) :
    ∀ e : E.Event, Option K → SPComp (E.Resp e × Option K)
  | e, some k => (a k e).bind fun r => SPComp.pure (r, some k)
  | e, none => μ.bind fun k => (a k e).bind fun r => SPComp.pure (r, some k)

/-- The stateful interpretation under the lazy handler at a drawn key is the interpretation under
    the handler at that key, with that key. -/
theorem interpSt_lazySt_some (μ : SPComp K) (a : K → ∀ e : E.Event, SPComp (E.Resp e))
    (t : CallTree E R) (k : K) :
    interpSt (lazySt μ a) t (some k) =
      (interpSP (a k) t).bind fun r => SPComp.pure (r, some k) := by
  induction t with
  | ret r => simp [SPComp.pure_bind]
  | vis e c ih =>
    simp only [interpSt_vis, interpSP_vis, lazySt, SPComp.bind_assoc, SPComp.pure_bind, ih]

/-- **The lazy-to-eager equation.** For a discardable key distribution `μ`, the stateful
    interpretation under the lazy handler from the empty state, followed by a continuation at the
    leaf, is drawing the key first and interpreting under the handler at that key. -/
theorem interpSt_lazySt_none_bind {β : Type} {μ : SPComp K} (hd : Discardable μ)
    (a : K → ∀ e : E.Event, SPComp (E.Resp e)) (t : CallTree E R) (f : R → SPComp β) :
    (interpSt (lazySt μ a) t none).bind (fun p => f p.1) =
      μ.bind fun k => (interpSP (a k) t).bind f := by
  cases t with
  | ret r =>
    simp only [interpSt_ret, interpSP_ret, SPComp.pure_bind]
    exact (hd β (f r)).symm
  | vis e c =>
    simp only [interpSt_vis, interpSP_vis, lazySt, SPComp.bind_assoc, SPComp.pure_bind,
      interpSt_lazySt_some]

/-- The lazy-to-eager equation at a tree with optional leaves. -/
theorem interpStOpt_lazySt_none {μ : SPComp K} (hd : Discardable μ)
    (a : K → ∀ e : E.Event, SPComp (E.Resp e)) (t : CallTree E (Option R)) :
    interpStOpt (lazySt μ a) t none = μ.bind fun k => interpSPOpt (a k) t :=
  interpSt_lazySt_none_bind hd a t optSP

/-- **The lazy-to-eager equation at an increasing fuel family**: the supremum over the fuel of the
    lazy interpretations from the empty state is drawing the key first and taking the supremum of
    the interpretations under the handler at that key. -/
theorem interpStω_lazySt_none {μ : SPComp K} (hd : Discardable μ)
    (a : K → ∀ e : E.Event, SPComp (E.Resp e)) (T : Nat → CallTree E (Option R))
    (hT : FuelMono T) :
    interpStω (lazySt μ a) T hT none = μ.bind fun k => interpSPω (a k) T hT := by
  let C : Chain (K → SPComp R) :=
    ⟨fun n k => interpSPOpt (a k) (T n), fun _ _ hnm k => (interpChain (a k) T hT).monotone hnm⟩
  have hC : (fun k => interpSPω (a k) T hT) = ωSup C := rfl
  rw [hC, (SPComp.ωScottContinuous_bind_right μ).map_ωSup]
  unfold interpStω
  refine le_antisymm (ωSup_le _ _ fun n => le_ωSup_of_le n ?_)
    (ωSup_le _ _ fun n => le_ωSup_of_le n ?_)
  · exact (interpStOpt_lazySt_none hd a (T n)).le
  · exact (interpStOpt_lazySt_none hd a (T n)).ge

end Lazy

end CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerLazyKey

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerLazyKey

open scoped ENNReal
open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.Haxc
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
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (tableOf entryCtx)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn hax64WExit)
open CatCrypt.Crypto.Hax.NFInline (crateOp crateBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv nfCallSig)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig leafHandler ExtRE ExtRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt (MapRE MapRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (ChainRE ChainRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerStateful
open _root_.Hax

/-! ## Keyed oracles with a lazily drawn key -/

variable {m : HaxModule}

/-- **The source computation of a keyed oracle with a lazily drawn key**: interpret the source
    tree under the lazy handler of the answers of `O` from the empty state, and read back the
    value of the source leaf. -/
noncomputable def lazySrc (O : KeyedOracle m) (t : CallTree linkSig (Outcome × Env)) :
    SPComp Value :=
  readBack (fun p => srcRead p.1)
    (interpSt (lazySt O.keyDist fun k e => SPComp.pure (O.ans k e)) t none)

/-- **The target computation of a keyed oracle with a lazily drawn key**: interpret the target
    trees of the calling body `pc` from `sa` under the lazy handler of the target handler family
    `h₂` from the empty state, and read back the result by `σ`. -/
noncomputable def lazyTgt (σ : AbiLayout) (pc : List RInstr) (sym : Nat → String) (sa : AState)
    (O : KeyedOracle m)
    (h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)) : SPComp Value :=
  readBack (fun s' => some (σ.result.read sa s'))
    (interpTargetStω m pc sym sa (lazySt O.keyDist h₂) none)

/-- At a discardable key distribution, the source computation with a lazily drawn key is the
    source computation with the key drawn first. -/
theorem lazySrc_eq_keyedSrc {O : KeyedOracle m} (hd : Discardable O.keyDist)
    (t : CallTree linkSig (Outcome × Env)) : lazySrc O t = keyedSrc O t := by
  unfold lazySrc keyedSrc readBack
  exact interpSt_lazySt_none_bind hd _ t fun r => optSP (srcRead r)

/-- At a discardable key distribution, the target computation with a lazily drawn key is the
    target computation with the key drawn first. -/
theorem lazyTgt_eq_keyedTgt {O : KeyedOracle m} (hd : Discardable O.keyDist) (σ : AbiLayout)
    (pc : List RInstr) (sym : Nat → String) (sa : AState)
    (h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)) :
    lazyTgt σ pc sym sa O h₂ = keyedTgt σ pc sym sa O h₂ := by
  simp only [lazyTgt, keyedTgt, interpTargetStω, interpStω_lazySt_none hd, interpTargetω,
    readBack, SPComp.bind_assoc]

/-- **Robust compilation over the target handler families coupled with a keyed oracle, with the
    key drawn lazily on both sides.** The hypotheses are those of `HandlerRCKeyed`; the source
    and target computations are `lazySrc` and `lazyTgt`. -/
def HandlerRCLazy (m : HaxModule) (σ : AbiLayout) (pc : List RInstr) (sym : Nat → String)
    (O : KeyedOracle m) : Prop :=
  ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
    ∀ (fuelC fuel : Nat) (ε δ : ℝ≥0∞),
      (∀ k s, readBack srcRead (interpSP (fun e => SPComp.pure (O.ans k e))
        (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)) s none ≤ δ) →
      RobustCompilationH
        (fun h₂ => HandlerCoupledKeyed O h₂ ∧
          ∀ k s, interpTargetω m pc sym sa (h₂ k) s none ≤ ε) (ε + δ)
        (fun h₂ (_ : Unit) => lazyTgt σ pc sym sa O h₂)
        (fun _ (_ : Unit) =>
          lazySrc O (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env))

/-- **`HandlerRCLazy` from `HandlerRCKeyed`** at a keyed oracle whose key distribution is
    discardable. -/
theorem handlerRCLazy_of_handlerRCKeyed {σ : AbiLayout} {pc : List RInstr} {sym : Nat → String}
    {O : KeyedOracle m} (hd : Discardable O.keyDist) (h : HandlerRCKeyed m σ pc sym O) :
    HandlerRCLazy m σ pc sym O := by
  intro sa hsa env henv fC fuel ε δ hδ
  simp only [lazyTgt_eq_keyedTgt hd, lazySrc_eq_keyedSrc hd]
  exact h sa hsa env henv fC fuel ε δ hδ

/-- **Robust compilation over keyed oracles with a lazily drawn key, for the hax compiler.** Let
    `compileA` compile the module `m` to `(P, bytes)` under the hypotheses of
    `NFCallTreeR3Linked.r3FA_of_shape_linked`. The bytes decode to a calling body `pc` followed
    by the shifted linked code `Q`, and `HandlerRCLazy` holds at `pc` for every keyed oracle of `m` whose key
    distribution is discardable. -/
theorem haxc_rcHLazy {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none)
    (hcf : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]), haxToNF σ m = some q →
      (extChain (linkedDecls m hax64WExit) _ q.1).run q.2 = some p → p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (x : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs x = .ret none)
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (hword : ∀ c ∈ m.linked.filterMap LinkedFn.calleeData, (∃ r, c.res = .reg r)
      ∧ c.arrArgs = (fun _ => none) ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true)
    (hin : ∀ l ∈ m.linked, innerHead l.name = false)
    (hspine : NFCallTreeInlineSpine.spineArgsOk m.entry.erase = true)
    (hfs : ∀ f ∈ m.fns, NFCallTreeInlineSpine.spineArgsOk f.texpr.erase = true)
    (hint : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg nfDialect (entryCtx (abiEntry σ)) [q.1]), haxToNF σ m = some q →
      nfSrcProgC (m.prepared nfBody ++ m.linkedFns) σ (bindConsts σ.consts m.entry)
        = some ⟨q.1, p⟩ → ∀ o, p.HasOp o →
          NFCallTreeFrontModule.OpOk NFCallTreeGoodCall.IntArgFree o)
    (hfp : ∀ f ∈ m.fns, ∀ p ∈ f.params, p.2 ≠ .int)
    (hbody : ∀ f ∈ m.fns, (crateBody (m.prepared nfBody) (f.prep nfBody) (entryCtx f.params)
      f.res m.linkSig).isSome = true)
    (hintB : ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → NFCallTreeFrontModule.OpOk NFCallTreeGoodCall.IntArgFree o) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      ∀ O : KeyedOracle m, Discardable O.keyDist → HandlerRCLazy m σ pc sym O := by
  obtain ⟨pc, Q, sym, hdec, hrc⟩ := haxc_rcHKeyed hc hnd hk hn hpt hcf tE htE hpar hword hin
    hspine hfs hint hfp hbody hintB
  exact ⟨pc, Q, sym, hdec, fun O hO => handlerRCLazy_of_handlerRCKeyed hO (hrc O)⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerLazyKey
