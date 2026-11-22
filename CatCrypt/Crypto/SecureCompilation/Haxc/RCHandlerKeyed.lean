/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerStateful

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

A keyed oracle is the stateful oracle of `RCHandlerStateful` whose handler state is the key:
drawn by `keyDist`, and kept by every call (`keyedSt`). Its source and target computations and
its couplings are those of that stateful oracle, so the statistical distance bound and robust
compilation over keyed oracles are instances of the theorems over stateful oracles.

## Main definitions

* `KeyedOracle`: a source oracle of the keyed-game form with typed answers.
* `keyedSrc`, `keyedTgt`: the source and target computations of a keyed oracle.
* `HandlerCoupledKeyed`: a target handler family coupled at each key with the keyed oracle.
* `keyedSt`: a keyed oracle as a stateful oracle.
* `HandlerRCKeyed`: robust compilation over the target handler families coupled with a keyed
  oracle whose failure weight is bounded.
* `pointOracle`: the point mass at the meanings of the linked functions as a keyed oracle.

## Main results

* `sdist_keyed_contract`: the statistical distance of the source and target computations, the
  instance of `sdist_st_contract` at `keyedSt`.
* `handlerRCKeyed_of_handlerRCSt`: `HandlerRCKeyed` from `HandlerRCSt` at `keyedSt`.
* `handlerCoupledKeyed_point`: a handler of `HandlerCoupledCG` is coupled with `pointOracle`.
* `handlerRC_of_handlerRCKeyed`: `HandlerRC` from `HandlerRCKeyed` at `pointOracle`.
* `haxc_rcHKeyed`: for a result of `compileA` under the hypotheses of `haxc_rcHSt`,
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
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSP (HandlerCoupled)
open CatCrypt.Crypto.SecureCompilation.Haxc.CallTreeInterpSPFuel
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerInstance (HandlerRC)
open CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerStateful
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

/-! ## The keyed oracle as a stateful oracle -/

/-- **A keyed oracle as a stateful oracle**: the handler state is the key, drawn by `keyDist`
    and kept by every call. -/
noncomputable def keyedSt (O : KeyedOracle m) : StOracle m where
  St := O.Key
  init := O.keyDist
  step := constSt fun k e => SPComp.pure (O.ans k e)
  skips := by
    rintro e k _ rfl
    change RelF _ ((SPComp.pure _).bind _) _ _
    rw [SPComp.pure_bind]
    exact RelF.ret fun _ _ hs => ⟨O.typed k e, rfl, hs⟩

/-- The source computation of a keyed oracle as a stateful oracle is `keyedSrc`. -/
theorem stSrc_keyedSt (O : KeyedOracle m) (t : CallTree linkSig (Outcome × Env)) :
    stSrc (keyedSt O) t = keyedSrc O t := by
  simp only [stSrc, keyedSrc, keyedSt, readBack_interpSt_constSt]

/-- The target computation of a keyed oracle as a stateful oracle, at a target handler family
    indexed by the key, is `keyedTgt`. -/
theorem stTgt_keyedSt (σ : AbiLayout) (pc : List RInstr) (sym : Nat → String) (sa : AState)
    (O : KeyedOracle m)
    (h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)) :
    stTgt σ pc sym sa (keyedSt O) (constSt h₂) = keyedTgt σ pc sym sa O h₂ := by
  simp only [stTgt, keyedTgt, keyedSt, interpTargetStω, interpStω_constSt, interpTargetω]

/-- **A target handler family coupled with a keyed oracle is coupled with it as a stateful
    oracle.** -/
theorem handlerCoupledSt_keyedSt {O : KeyedOracle m}
    {h₂ : O.Key → ∀ e : (kSig AState).Event, SPComp ((kSig AState).Resp e)}
    (hc : HandlerCoupledKeyed O h₂) : HandlerCoupledSt (keyedSt O) (constSt h₂) := by
  rintro e₁ e₂ he k _ rfl
  have hk := hc k e₁ e₂ he
  have hnf : ∀ s, h₂ k e₂ s none = 0 :=
    rHoare_noFail_right (Φ := eqPre) hk (fun s => ⟨s, rfl⟩) fun _ => SDistr.pure_apply_none _
  change RelF eqPre ((SPComp.pure (O.ans k e₁)).bind fun a => SPComp.pure (a, k))
    ((h₂ k e₂).bind fun a => SPComp.pure (a, k)) _
  refine RelF.bind (RelF.of_rHoare (fun _ => SDistr.pure_apply_none _) hnf hk) fun a b => ?_
  exact RelF.ret fun _ _ hp => ⟨hp.1, rfl, hp.2⟩

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
  rw [← stSrc_keyedSt, ← stTgt_keyedSt]
  refine sdist_st_contract (keyedSt O) (handlerCoupledSt_keyedSt hc) h
    (fun (k : O.Key) s => ?_) (fun (k : O.Key) s => ?_)
  · have he := hε k s
    rw [interpTargetω, ← interpStω_constSt] at he
    exact he
  · have he := readBack_interpSt_constSt (S := O.Key) srcRead
      (fun k e => SPComp.pure (O.ans k e)) t₁ k
    exact (congrArg (fun c : SPComp Value => c s none) he).trans_le (hδ k s)

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

/-- **`HandlerRCKeyed` is the instance of `HandlerRCSt` at a keyed oracle**, whose handler state
    is the key. -/
theorem handlerRCKeyed_of_handlerRCSt {σ : AbiLayout} {pc : List RInstr} {sym : Nat → String}
    {O : KeyedOracle m} (h : HandlerRCSt m σ pc sym (keyedSt O)) :
    HandlerRCKeyed m σ pc sym O := by
  intro sa hsa env henv fC fuel ε δ hδ
  refine (robustCompilationH_iff_sdist _ _ _ _).mpr fun h₂ hh => ?_
  have hk := (robustCompilationH_iff_sdist _ _ _ _).mp
    (h sa hsa env henv fC fuel ε δ fun (k : O.Key) s => by
      have he := readBack_interpSt_constSt (S := O.Key) srcRead
        (fun k e => SPComp.pure (O.ans k e))
        (nfTree (moduleTreeTable m hax64WExit fC) fuel m.entry.erase env) k
      exact (congrArg (fun c : SPComp Value => c s none) he).trans_le (hδ k s)) (constSt h₂)
    ⟨handlerCoupledSt_keyedSt hh.1, fun (k : O.Key) s => by
      have hk := hh.2 k s
      rw [interpTargetω, ← interpStω_constSt] at hk
      exact hk⟩
  rwa [stTgt_keyedSt, stSrc_keyedSt] at hk

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
    module `m` to `(P, bytes)` under the hypotheses of `NFCallTreeR3Linked.r3FA_of_shape_linked`.
    The bytes decode to a calling body `pc` followed by the shifted linked code `Q`, and
    `HandlerRCKeyed` holds at `pc` for every keyed oracle of `m`, as the instance of `haxc_rcHSt`
    at the stateful oracles `keyedSt`. -/
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
      ∀ O : KeyedOracle m, HandlerRCKeyed m σ pc sym O := by
  obtain ⟨pc, Q, sym, hd, h⟩ := haxc_rcHSt hc hnd hk hn hpt hcf tE htE hpar hword hin
    hspine hfs hint hfp hbody hintB
  exact ⟨pc, Q, sym, hd, fun O => handlerRCKeyed_of_handlerRCSt (h (keyedSt O))⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.RCHandlerKeyed
