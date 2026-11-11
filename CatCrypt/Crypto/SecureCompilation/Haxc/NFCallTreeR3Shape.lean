/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontModule

/-!
# The conclusion of `R3StatementFG` at a module, from the shape of the module

`NFProgCallTreeModule.r3FG_of_front` gives the conclusion of `R3StatementFG` at a module compiled
by `compileA` from the relation of the front; `NFCallTreeFrontModule.front_relT` gives that
relation from the shape of the module. Together they give the conclusion under conditions on the
module only: the shape conditions of `r3FG_of_front` (without narrow parameters read at their
widths, without a pair tail, linked kernels with distinct names, word and integer parameters and a
word result, register results, no array positions, general-purpose argument names, no inner
heads, a chain output with a call), the conditions of the intermediate handlers and of the events
of the narrowed program, call-free arguments at the calls of inlined closures of the entry and of
every function (`spineArgsOk`), and calls of the source programs of the entry and of the callees
typed as their callees declare (`GoodCall`; a linked call at exactly the parameter types of the
linked function).

Without the narrow and pair-tail stages the stages before the front (`pairStage`) leave the module
and the layout as they are (`pairTailOf_none_compileA_eq`).

## Main results

* `r3FG_of_shape`: the conclusion of `R3StatementFG` at a module, from its shape.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Shape

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

open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeR3 (keepL)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeKinds (contractRunOf summaryOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (contractRAC)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (OutTy)
open CatCrypt.Crypto.Hax (LinkedFn)

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc (regionProg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTarget (symOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (eq_none_of_outRel mfTree_castProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (pureReader eventEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContracts (R3StatementFG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTyped (FrontRET)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeModule (GoodEv)
open CatCrypt.Crypto.Hax.NFInline (crateOp)

/-- **The conclusion of `R3StatementFG` at a module, from the shape of the module.** The
    statement of `NFProgCallTreeModule.r3FG_of_front` with its relation of the front replaced by
    call-free arguments at the calls of inlined closures (`spineArgsOk`) and the typing
    `GoodCall` of the calls of the source programs of the entry and of the callees. -/
theorem r3FG_of_shape {m : HaxModule} {σ : AbiLayout} {fname : String} {P : Lprog}
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
    (hin : ∀ l ∈ m.linked, innerHead l.name = false) (d : CalleeKind) (tr₀ : List CTLeak)
    (hev : ∀ (T : CalleeTab), T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData) →
      ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
        (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)])
        (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
          ([mapTy (catTy q.1)].map NarrowWords.wideTy)), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → NarrowWords.narrowPrep p = some q' →
      ∀ (tf : Nat) (V : Ctxt.Valuation (entryCtx (abiEntry σ))),
        AllEv (GoodEv m d T h₃) (mfTree tf q' (NarrowWords.mapVal (ctMapValD (mapVal V)))))
    (hspine : NFCallTreeInlineSpine.spineArgsOk m.entry.erase = true)
    (hfs : ∀ f ∈ m.fns, NFCallTreeInlineSpine.spineArgsOk f.texpr.erase = true)
    (hgoodE : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg nfDialect (entryCtx (abiEntry σ)) [q.1]), haxToNF σ m = some q →
      nfSrcProgC (m.prepared nfBody ++ m.linkedFns) σ (bindConsts σ.consts m.entry)
        = some ⟨q.1, p⟩ → ∀ o, p.HasOp o →
          NFCallTreeFrontModule.OpOk (NFCallTreeFrontModule.GoodCall m) o)
    (hgood : ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → NFCallTreeFrontModule.OpOk (NFCallTreeFrontModule.GoodCall m) o) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel,
          RuttF (linkHandler m) (contractREG m) (contractRAC m) (resRel σ sa) srcFail
            (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel
              m.entry.erase env)
            (fun fuelT => targetTree aMachine pc sym (linkRead m) fuelT 0 sa) :=
  NFProgCallTreeModule.r3FG_of_front hc hnd hk hn hpt hcf tE htE h₂ h₃ hh₂ hh₃ hinner hhC hpar
    hword hin d tr₀ hev
    (NFCallTreeFrontModule.front_relT tE htE hspine hfs hgoodE hgood)

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Shape
