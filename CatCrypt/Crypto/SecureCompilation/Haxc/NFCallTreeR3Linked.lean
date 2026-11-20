/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Ev
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodBody

/-!
# R3 at the linked handlers from shape conditions on the bodies

`NFCallTreeR3Handlers.r3FA_of_shape_linkedHandlers` takes two hypotheses about the programs
of the chain: `hev`, on the events of the narrowed chain program, and `hgood`, on the
operations of the callee bodies. Both follow from conditions on the module:

* `hev` from `hpar` and `hword` (`NFCallTreeR3Ev.allEv_evOK_of_linkedWords`);
* `hgood` from the signatures of the linked functions, which `compileA` checks
  (`linkSigOk_of_compileA`), and three decidable conditions on the functions of the module:
  no parameter of type `int`, each callee body translates (`crateBody`), and no operation of a
  callee body takes an integer argument (`NFCallTreeGoodBody.goodCallB`).

## Main results

* `linkSigOk_of_compileA`: the linked functions of a module `compileA` compiles pass
  `linkSigOk`.
* `goodCall_of_bodies`: the hypothesis `hgood` of `r3FA_of_shape_linkedHandlers` and of
  `NFCallTreeR3TypedAns.r3FG_of_shape_int`.
* `r3FA_of_shape_linked`: the conclusion of `r3FA_of_shape_linkedHandlers` without `hev`, with
  `hgood` replaced by the three conditions on the bodies.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Linked

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (tableOf entryCtx)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
open CatCrypt.Crypto.Hax.NFInline (crateOp crateBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle (RuttFA SkipAns TypedAns
  contractRACA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontModule (OpOk GoodCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodCall (IntArgFree)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open Ctxt (Valuation)

/-- **The linked functions of a compiled module pass `linkSigOk`.** Without narrow parameters
    and a pair tail, `compileA` runs `haxToNF`, which checks the signatures of the linked
    functions (`haxToNF_eq_some_sig`). -/
theorem linkSigOk_of_compileA {m : HaxModule} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none) :
    ∀ l ∈ m.linked, linkSigOk l = true := by
  have hca : compileARegion m σ fname = some (P, bytes) := by
    rw [← pairTailOf_none_compileA_eq hpt fname hn]
    exact hc
  have hca' := (NFEntry.compileR_eq_bind haxEntry m σ fname
    (m.linked.filterMap LinkedFn.calleeData)).symm.trans hca
  obtain ⟨q, hq, -⟩ := Option.bind_eq_some_iff.mp hca'
  exact (haxToNF_eq_some_sig hq).1

/-- **The operations of the callee bodies of a compiled module are good calls** when no
    function of the module has a parameter of type `int`, each callee body translates, and no
    operation of a callee body takes an integer argument. This is the hypothesis `hgood` of
    `NFCallTreeR3TypedAns.r3FG_of_shape_int` and `r3FA_of_shape_linkedHandlers`. -/
theorem goodCall_of_bodies {m : HaxModule} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none)
    (hfp : ∀ f ∈ m.fns, ∀ p ∈ f.params, p.2 ≠ .int)
    (hbody : ∀ f ∈ m.fns, (crateBody (m.prepared nfBody) (f.prep nfBody) (entryCtx f.params)
      f.res m.linkSig).isSome = true)
    (hintB : ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → OpOk IntArgFree o) :
    ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → OpOk (GoodCall m) o :=
  NFCallTreeGoodBody.goodCallB (linkSigOk_of_compileA hc hn hpt) hfp hbody hintB

/-- **The conclusion of `R3StatementFA TypedAns` at a module, from its shape, at the handlers of
    its linked functions.** The statement of
    `NFCallTreeR3Handlers.r3FA_of_shape_linkedHandlers` without the event hypothesis `hev`
    (`NFCallTreeR3Ev.allEv_evOK_of_linkedWords`), and with `hgood` replaced by the conditions
    `hfp`, `hbody` and `hintB` on the functions of the module (`goodCall_of_bodies`). -/
theorem r3FA_of_shape_linked {m : HaxModule} {σ : AbiLayout} {fname : String}
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
    (hspine : NFCallTreeInlineSpine.spineArgsOk m.entry.erase = true)
    (hfs : ∀ f ∈ m.fns, NFCallTreeInlineSpine.spineArgsOk f.texpr.erase = true)
    (hint : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg nfDialect (entryCtx (abiEntry σ)) [q.1]), haxToNF σ m = some q →
      nfSrcProgC (m.prepared nfBody ++ m.linkedFns) σ (bindConsts σ.consts m.entry)
        = some ⟨q.1, p⟩ → ∀ o, p.HasOp o → OpOk IntArgFree o)
    (hfp : ∀ f ∈ m.fns, ∀ p ∈ f.params, p.2 ≠ .int)
    (hbody : ∀ f ∈ m.fns, (crateBody (m.prepared nfBody) (f.prep nfBody) (entryCtx f.params)
      f.res m.linkSig).isSome = true)
    (hintB : ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → OpOk IntArgFree o) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel,
          RuttFA (SkipAns TypedAns m) (contractREG m) (contractRACA TypedAns m) (resRel σ sa)
            srcFail
            (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel
              m.entry.erase env)
            (fun fuelT => targetTree aMachine pc sym (linkRead m) fuelT 0 sa) :=
  NFCallTreeR3Handlers.r3FA_of_shape_linkedHandlers hc hnd hk hn hpt hcf tE htE hpar hword hin
    (NFCallTreeR3Ev.allEv_evOK_of_linkedWords hpar hword) hspine hfs hint
    (goodCall_of_bodies hc hn hpt hfp hbody hintB)

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Linked
