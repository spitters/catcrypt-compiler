/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3TypedAns
public import CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerInstance

/-!
# Robust compilation over keyed source oracles

`HandlerRC` fixes the source handler of the linked functions to the point mass at their meanings
`linkHandler m`. This module states robust compilation over source handlers of the keyed-game
form: a key is drawn by a distribution `keyDist`, and at a key `k` each call is answered by
`ans k`, an answer that is typed by the result type of the linked function (`TypedAns`). The
target handler is a family indexed by the key, coupled at each key, at equal heaps, with the
point mass at `ans k` on the separation contracts at the typed answer relation
`contractRACA TypedAns m`. The source and target computations draw the same key and then run the
source tree, respectively the target trees of the calling body, under the handlers at that key.

The relation of the call trees at the skip predicate `SkipAns TypedAns m`
(`NFCallTreeR3TypedAns.r3FA_of_shape_int`) is, at each key, the relation `RuttF` at the pure
handler `ans k`, since its answers satisfy the skip predicate. The statistical distance bound of
`sdist_readBack_ruttF` then holds at each key, and the common draw of the key keeps it
(`sdist_bind_right_dep`).

## Main definitions

* `KeyedOracle`: a source oracle of the keyed-game form with typed answers.
* `keyedSrc`, `keyedTgt`: the source and target computations of a keyed oracle.
* `HandlerCoupledKeyed`: a target handler family coupled at each key with the keyed oracle.
* `HandlerRCKeyed`: robust compilation over the target handler families coupled with a keyed
  oracle whose failure weight is bounded.
* `pointOracle`: the point mass at the meanings of the linked functions as a keyed oracle.

## Main results

* `sdist_keyed_contract`: the statistical distance of the source and target computations.
* `handlerCoupledKeyed_point`: a handler of `HandlerCoupledCG` is coupled with `pointOracle`.
* `handlerRC_of_handlerRCKeyed`: `HandlerRC` from `HandlerRCKeyed` at `pointOracle`.
* `haxc_rcHKeyed`: for a result of `compileA` under the hypotheses of `r3FA_of_shape_int`,
  `HandlerRCKeyed` at every keyed oracle.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed

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
open CatCrypt.Crypto.Hax.NFInline (crateOp)
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
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSP (HandlerCoupled)
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerInstance (HandlerRC)
open _root_.Hax

/-! ## Keyed source oracles -/

/-- **A source oracle of the keyed-game form** for the linked functions of `m`: a key of type
    `Key` drawn by `keyDist`, and at a key `k` the answer `ans k e` to a call `e`. At a call of a
    linked function the answer is typed by the result type of the function, and at a call of
    another name it is `none` (`SkipAns TypedAns m`). -/
structure KeyedOracle (m : HaxModule) where
  /-- The type of the keys. -/
  Key : Type
  /-- The distribution of the key. -/
  keyDist : SPComp Key
  /-- The answer to a call at a key. -/
  ans : Key → ∀ e : linkSig.Event, linkSig.Resp e
  /-- The answers satisfy the skip predicate at the typing predicate. -/
  typed : ∀ k e, SkipAns TypedAns m e (ans k e)

variable {m : HaxModule}

/-- **The source computation of a keyed oracle**: draw the key, interpret the source tree under
    the point mass at the answers at that key, and read back the value of the source leaf. -/
noncomputable def keyedSrc (O : KeyedOracle m) (t : CallTree linkSig (Outcome × Env)) :
    SPComp Value :=
  O.keyDist.bind fun k => readBack srcRead (interpSP (fun e => SPComp.pure (O.ans k e)) t)

/-- **The target computation of a keyed oracle**: draw the key, interpret the target trees of
    the calling body `pc` from `sa` under the target handler at that key, and read back the
    result by `σ` from the return state. -/
noncomputable def keyedTgt (σ : AbiLayout) (pc : List RInstr) (sym : Nat → String) (sa : AState)
    (O : KeyedOracle m)
    (h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)) : SPComp Value :=
  O.keyDist.bind fun k =>
    readBack (fun s' => some (σ.result.read sa s')) (interpTargetω m pc sym sa (h₂ k))

/-- **A target handler family coupled with a keyed oracle**: at each key `k`, the target handler
    at `k` is coupled at equal heaps with the point mass at the answers `O.ans k` on the
    separation contracts at the typed answer relation. -/
def HandlerCoupledKeyed (O : KeyedOracle m)
    (h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)) : Prop :=
  ∀ k, HandlerCoupled eqPre (contractREG m) (contractRACA TypedAns m)
    (fun e => SPComp.pure (O.ans k e)) (h₂ k)

/-- **Statistical distance at a keyed oracle.** Let a source tree be related by `RuttFA` at the
    skip predicate `SkipAns TypedAns m` and the separation contracts at `TypedAns` to the target
    trees of the calling body `pc` from `sa`, and let the target handler family be coupled with
    the keyed oracle `O`. The statistical distance of the source and target computations is at
    most a bound `ε` of the failure weight of the target at every key plus a bound `δ` of the
    failure weight of the source read-back at every key. -/
theorem sdist_keyed_contract {σ : AbiLayout} {sa : AState} {pc : List RInstr}
    {sym : Nat → String} (O : KeyedOracle m)
    {h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hc : HandlerCoupledKeyed O h₂) {t₁ : CallTree linkSig (Outcome × Env)}
    (h : RuttFA (SkipAns TypedAns m) (contractREG m) (contractRACA TypedAns m) (resRel σ sa)
      srcFail t₁ (fun n => targetTree aMachine pc sym (linkRead m) n 0 sa))
    {ε δ : ℝ≥0∞} (hε : ∀ k s, interpTargetω m pc sym sa (h₂ k) s none ≤ ε)
    (hδ : ∀ k s, readBack srcRead (interpSP (fun e => SPComp.pure (O.ans k e)) t₁) s none ≤ δ) :
    sdist (fun _ : Unit => keyedSrc O t₁) (fun _ : Unit => keyedTgt σ pc sym sa O h₂) ≤
      ε + δ := by
  have hk : ∀ k, sdist
      (fun _ : Unit => readBack srcRead (interpSP (fun e => SPComp.pure (O.ans k e)) t₁))
      (fun _ : Unit => readBack (fun s' => some (σ.result.read sa s'))
        (interpTargetω m pc sym sa (h₂ k))) ≤ ε + δ := fun k =>
    sdist_readBack_ruttF (hc k) (fun _ => srcFail_of_resRel_none) _
      (ruttFA_iff_ruttF.mp (h.imp (fun e a ha => by subst ha; exact O.typed k e)
        (fun _ _ he => he) (fun _ _ _ _ _ ha => ha) (fun _ _ hr => hr) (fun _ hf => hf)))
      srcRead _ (fun _ => srcRead_of_srcFail) (fun _ _ _ => read_of_resRel) (hε k) (hδ k)
  have hfun : sdist
      (fun k => readBack srcRead (interpSP (fun e => SPComp.pure (O.ans k e)) t₁))
      (fun k => readBack (fun s' => some (σ.result.read sa s'))
        (interpTargetω m pc sym sa (h₂ k))) ≤ ε + δ :=
    iSup_le fun D => iSup_le fun k => iSup_le fun h₀ => sdist_le_of_forall (hk k) D () h₀
  exact sdist_bind_right_dep (fun _ : Unit => O.keyDist) _ _ fun _ => hfun

/-! ## Robust compilation over keyed oracles -/

/-- **Robust compilation over the target handler families coupled with a keyed oracle.** At
    every entry state `sa` of the domain of `σ`, every source environment `env` of the narrowed
    entry, and every fuel, let `δ` bound the failure weight of the source read-back under the
    keyed oracle `O` at every key. Then replacing the source computation `keyedSrc` by the target
    computation `keyedTgt` is robust compilation at `ε + δ` over the target handler families
    coupled with `O` whose failure weight at every key is at most `ε`. -/
def HandlerRCKeyed (m : HaxModule) (σ : AbiLayout) (pc : List RInstr) (sym : Nat → String)
    (O : KeyedOracle m) : Prop :=
  ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
    ∀ (fuelC fuel : Nat) (ε δ : ℝ≥0∞),
      (∀ k s, readBack srcRead (interpSP (fun e => SPComp.pure (O.ans k e))
        (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env)) s none ≤ δ) →
      RobustCompilationH
        (fun h₂ => HandlerCoupledKeyed O h₂ ∧
          ∀ k s, interpTargetω m pc sym sa (h₂ k) s none ≤ ε) (ε + δ)
        (fun h₂ (_ : Unit) => keyedTgt σ pc sym sa O h₂)
        (fun _ (_ : Unit) =>
          keyedSrc O (nfTree (moduleTreeTable m hax64WExit fuelC) fuel m.entry.erase env))

/-- **The meanings of the linked functions as a keyed oracle**: a single key, and the answers
    of `linkHandler m`. -/
noncomputable def pointOracle (m : HaxModule) : KeyedOracle m where
  Key := Unit
  keyDist := SPComp.pure ()
  ans _ := linkHandler m
  typed _ _ := skipAns_mono (fun _ _ _ => typedAns_of_semAns) (skipAns_sem_iff.mpr rfl)

/-- **A target handler coupled with the meanings on the separation contracts is coupled with
    `pointOracle`**: the answer relation `contractRAC` implies the typed answer relation. -/
theorem handlerCoupledKeyed_point
    {h₂ : ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hc : HandlerCoupledCG m eqPre h₂) : HandlerCoupledKeyed (pointOracle m) fun _ => h₂ :=
  fun _ e₁ e₂ he => rHoare_mono_post (hc e₁ e₂ he) fun _ _ _ _ hp =>
    ⟨contractRACA_mono (fun _ _ _ => typedAns_of_semAns) ((contractRACA_sem_iff he).mpr hp.1),
      hp.2⟩

/-- **`HandlerRC` from robust compilation at the point oracle.** -/
theorem handlerRC_of_handlerRCKeyed {σ : AbiLayout} {pc : List RInstr} {sym : Nat → String}
    (h : HandlerRCKeyed m σ pc sym (pointOracle m)) : HandlerRC m σ pc sym := by
  intro sa hsa env henv fC fuel ε δ hε hδ
  refine (robustCompilationH_iff_sdist _ _ _ _).mpr fun h₂ hh => ?_
  have hk := (robustCompilationH_iff_sdist _ _ _ _).mp
    (h sa hsa env henv fC fuel ε δ (fun _ s => hδ s)) (fun _ => h₂)
    ⟨handlerCoupledKeyed_point hh, fun _ s => hε h₂ hh s⟩
  simpa only [keyedTgt, keyedSrc, pointOracle, SPComp.pure_bind] using hk

/-- **Robust compilation over keyed oracles, for the hax compiler.** Let `compileA` compile the
    module `m` to `(P, bytes)` under the hypotheses of `r3FA_of_shape_int`. The bytes decode to
    a calling body `pc` followed by the shifted linked code `Q`, and `HandlerRCKeyed` holds at
    `pc` for every keyed oracle of `m`. -/
theorem haxc_rcHKeyed {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none)
    (hcf : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]), haxToNF σ m = some q →
      (extChain (linkedDecls m hax64WExit) _ q.1).run q.2 = some p → p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (x : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs x = .ret none)
    (h₂ : ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e)
    (h₃ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hh₂ : ∀ e₁ e₂, ExtRE e₁ e₂ → NFProgCallTreeChain.ExtEv e₁ → ExtRA e₁ e₂
      (leafHandler (tableOf (m.linkTable hax64WExit)) e₁) (h₂ e₂))
    (hh₃ : ∀ e₀ e₁ e₂, ExtRE e₀ e₁ → NFProgCallTreeChain.ExtEv e₀ →
      MapRE catToJasmin (fun x => ctTransTy x) e₁ e₂ →
      MapRA catToJasmin (fun x => ctTransTy x) e₁ e₂ (h₂ e₁) (h₃ e₂))
    (hinner : ∀ (f : String) (as rs : List JasminTy) (x : Ctxt.Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₃ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    (hhC : ∀ e₁ e₂, ChainRE e₁ e₂ → NFProgCallTreeChain.ExtEv e₁ → ChainRA e₁ e₂
      (leafHandler (tableOf (m.linkTable hax64WExit)) e₁) (h₃ e₂))
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (hword : ∀ c ∈ m.linked.filterMap LinkedFn.calleeData, (∃ r, c.res = .reg r)
      ∧ c.arrArgs = (fun _ => none) ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true)
    (hin : ∀ l ∈ m.linked, innerHead l.name = false)
    (hev : ∀ (T : CalleeTab), T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData) →
      ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
        (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)])
        (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
          ([mapTy (catTy q.1)].map NarrowWords.wideTy)), haxToNF σ m = some q →
      (extChain (linkedDecls m hax64WExit) _ q.1).run q.2 = some p →
      NarrowWords.narrowPrep p = some q' →
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
      ∀ O : KeyedOracle m, HandlerRCKeyed m σ pc sym O := by
  obtain ⟨pc, Q, sym, hd, hrel⟩ := NFCallTreeR3TypedAns.r3FA_of_shape_int hc hnd hk hn hpt hcf
    tE htE h₂ h₃ hh₂ hh₃ hinner hhC hpar hword hin hev hspine hfs hint hgood
  refine ⟨pc, Q, sym, hd, fun O sa hsa env henv fC fuel ε δ hδ => ?_⟩
  refine (robustCompilationH_iff_sdist _ _ _ _).mpr fun h hh => ?_
  rw [sdist_sym]
  exact sdist_keyed_contract O hh.1 (hrel sa hsa env henv fC fuel) hh.2 hδ

end CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed
