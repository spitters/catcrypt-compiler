/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeModuleAns

/-!
# The conclusion of `R3StatementFA TypedAns` at a module, from the shape of the module

`NFProgCallTreeModuleAns.r3FA_typed` gives the relation of the call trees of a module at the
separation contracts at an answer predicate, at the skip predicate `SkipAns TypedAns m`, from the
relation of the front at that skip predicate. `NFCallTreeFrontModule.front_relTA` gives that
relation from the shape of the module, at every skip predicate whose leaves of the linked tree
table at `repeat` are the answers of the table of `repeat` calls. The linked tree table answers a
call of `repeat` without an event, since no linked name is `repeat` (`linkNameOk`), so every skip
predicate qualifies.

## Main results

* `repeatCallsA_retsA_linkTreeTable_of_linkNameOk`: at linked names that pass `linkNameOk`, every
  skip predicate admits at `repeat` only the answers of the table of `repeat` calls.
* `r3FA_of_shape_int`: the conclusion of `R3StatementFA TypedAns` at a module, from its shape.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3TypedAns

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
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
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
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA (RetsA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle (RuttFA SkipAns TypedAns
  contractRACA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeImpToNF (RepeatCallsA)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open _root_.Hax

/-- **At linked names that pass `linkNameOk`, every skip predicate admits at `repeat` only the
    answers of the table of `repeat` calls**: no linked function is named `repeat`, so the linked
    tree table answers a call of `repeat` by `hax64WExit` without an event. -/
theorem repeatCallsA_retsA_linkTreeTable_of_linkNameOk {m : HaxModule}
    (hlk : ∀ l ∈ m.linked, linkNameOk l.name = true)
    (Sk : (e : linkSig.Event) → linkSig.Resp e → Prop) :
    RepeatCallsA fun e a =>
      RetsA Sk (linkTreeTable m CatCrypt.Crypto.Hax.hax64WExit e.name e.args) a := by
  have hnone : m.linked.find? (·.name == "repeat") = none :=
    List.find?_eq_none.mpr fun l hl h => by
      have hk := hlk l hl
      rw [beq_iff_eq.mp h] at hk
      simp [linkNameOk] at hk
  intro x N v hN hv
  refine NFCallTreeFrontModule.repeatCallsA_retsA_linkTreeTable (linkTable_repeatCalls hlk)
    x N v hN ?_
  have ht : linkTreeTable m CatCrypt.Crypto.Hax.hax64WExit "repeat" [.int x, .int N]
      = .ret (CatCrypt.Crypto.Hax.hax64WExit "repeat" [.int x, .int N]) := by
    unfold linkTreeTable
    rw [hnone]
  change RetsA _ (linkTreeTable m _ "repeat" [.int x, .int N]) (some v) at hv
  change RetsA _ (linkTreeTable m _ "repeat" [.int x, .int N]) (some v)
  rw [ht] at hv ⊢
  generalize CatCrypt.Crypto.Hax.hax64WExit "repeat" [.int x, .int N] = r at hv ⊢
  cases hv
  exact .ret _

/-- **The conclusion of `R3StatementFA TypedAns` at a module, from its shape, with calls without
    an argument of type `int`.** The statement of `NFCallTreeGoodCall.r3FG_of_shape_int` with the
    conclusion at the skip predicate `SkipAns TypedAns m` and the answer relation
    `contractRACA TypedAns m`, and the events of the narrowed program within `EvOK`. -/
theorem r3FA_of_shape_int {m : HaxModule} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none)
    (hcf : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → p.callFree = false)
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
      (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁) (h₃ e₂))
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
  NFProgCallTreeModuleAns.r3FA_typed hc hnd hk hn hpt hcf tE htE h₂ h₃ hh₂ hh₃ hinner hhC hpar
    hword hin hev
    (fun q hq => NFCallTreeFrontModule.front_relTA tE htE hspine hfs
      (fun q p hq hp => NFCallTreeGoodCall.goodCallE hq hp (hint q p hq hp)) hgood _
      (repeatCallsA_retsA_linkTreeTable_of_linkNameOk (haxToNF_eq_some hq).2.2.1 _) q hq)
    TypedAns

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3TypedAns
