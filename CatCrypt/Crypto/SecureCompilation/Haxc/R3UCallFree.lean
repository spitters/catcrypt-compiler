/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Handlers
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeBack
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.TemplateKernel

/-!
# The conclusion of `R3StatementFA TypedAns` at a module without linked functions

On a module without linked functions, `compileA` (without narrow parameters and without a pair
tail) is the region back half `compileRegion` at no linked function, which compiles only a
program without `call` (`callFree_of_compileRegion`). The decoded bytes then hold no
instruction `call`, and the target tree is the leaf of the fuelled run of the decoded program.

The relation of the call trees is the composition of three relations:

* the front (`NFCallTreeFrontModule.front_relTA`), from the source call tree of the entry to
  the call tree of the program of `haxToNF`;
* the chain `extChain` followed by `narrowPrep` (`NFProgCallTreeModuleAns.chainSA_typed`) at
  the handlers `linkedHandlerC m` and `linkedHandlerJ m` of `NFCallTreeR3Handlers`;
* the back half on a program without `call`: the tree `mfTree` of the narrowed program is the
  leaf of its denotation, and `regionBack_correct` gives a halting run of the decoded bytes
  with the result read back.

No source event is related to a target event: the front relates source events to calls of
linked functions only, and the target trees have no event.

## Main results

* `r3FA_callFree`: the conclusion of `R3StatementFA TypedAns` at a module without linked
  functions, without narrow parameters and without a pair tail.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.R3UCallFree

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
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
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig leafHandler OutRel)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (linkResOk_of_mem_linkedDecls)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle (RuttFA SkipAns TypedAns
  contractRACA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSAComp (RuttSA.trans_ruttFA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeR3 (keepL)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Handlers
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open Ctxt (Valuation)

/-- **The conclusion of `R3StatementFA TypedAns` at a module without linked functions.** Let
    `compileA` return `(P, bytes)` on a module `m` without linked functions, without narrow
    parameters read at their widths and without a pair tail, and let the calls of the source
    program of the entry and of the bodies of the calls of the functions of `m` satisfy the
    conditions of the front (no argument of type `int`; `GoodCall m` in the bodies). Then the
    bytes decode to a program without `call`, and from every entry state the source call tree of
    the entry is related by `RuttFA (SkipAns TypedAns m)` at `contractREG m`,
    `contractRACA TypedAns m`, `resRel σ sa` and `srcFail` to the target trees of the decoded
    program. -/
theorem r3FA_callFree {m : HaxModule} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hl : m.linked = []) (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none)
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
            (fun fuelT => targetTree aMachine pc sym (linkRead m) fuelT 0 sa) := by
  let tE : TreeCallEnv leafSig nfDialect := ⟨fun _ _ _ _ => .ret none⟩
  have htE : ∀ (f : String) (as rs : List NfTy) (x : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs x = .ret none := fun _ _ _ _ => rfl
  have hin : ∀ l ∈ m.linked, innerHead l.name = false := by simp [hl]
  -- The stages of `compileA` at no linked function.
  have hca : haxEntry.compileR m σ fname = some (P, bytes) := by
    rw [← linkedNil_compileA_eq hl σ fname hpt hn]
    exact hc
  have hca' := (NFEntry.compileR_eq_bind haxEntry m σ fname []).symm.trans hca
  obtain ⟨q, hq, hca⟩ := Option.bind_eq_some_iff.mp hca'
  obtain ⟨p, hp, h1⟩ := Option.bind_eq_some_iff.mp hca
  have hcf : p.callFree = true := callFree_of_compileRegion h1
  obtain ⟨hB, q', hq', hb⟩ := compileRegion_eq_some.mp h1
  have hcf' : q'.callFree = true := (NarrowWords.callFree_narrowPrep hq').trans hcf
  obtain ⟨prog, hd⟩ := Option.isSome_iff_exists.mp
    (HashTemplate.decode_isSome_of_compileRegion h1)
  have hnc := NFProgCallTreeCallsBack.noCall_of_regionBack hb hd
  have hout : NFToRoute.OutTy q.1 := outTy_of_outTyB q.1 (haxToNF_eq_some_res hq)
  refine ⟨prog, [], fun _ => "", by simp [hd, shiftProg], fun sa hreg env henv fuelC fuel => ?_⟩
  have hne : narrowEntry m σ sa = sa := by simp [narrowEntry, hn]
  rw [hne] at henv
  -- The front.
  obtain ⟨V, tf, hV, hfr⟩ := NFCallTreeFrontModule.front_relTA tE htE
    (NFCallTreeInlineSpine.spineArgsOk_eq_true _)
    (fun _ _ => NFCallTreeInlineSpine.spineArgsOk_eq_true _)
    (fun q p hq hp => NFCallTreeGoodCall.goodCallE hq hp (hint q p hq hp)) hgood _
    (NFCallTreeR3TypedAns.repeatCallsA_retsA_linkTreeTable_of_linkNameOk (by simp [hl]) _)
    q hq sa hreg env henv fuelC fuel
  -- The chain.
  have hch := NFProgCallTreeModuleAns.chainSA_typed (m := m) (by simp [hl]) (by simp [hl]) hin
    _ tE htE (linkedHandlerC m) (linkedHandlerJ m)
    (fun e₁ e₂ h hX => linkedHandler_extRA hin e₁ e₂ h hX)
    (fun _ e₁ e₂ _ _ hm => linkedHandler_mapRA m e₁ e₂ hm)
    (fun f as rs x hf => linkedHandlerJ_inner m f as rs x hf)
    (fun _ hd => linkResOk_of_mem_linkedDecls hd) hp
  have hchV := hch hB q' hq' V (NFToRoute.inRange_entry henv V hV) tf tf le_rfl
  -- The back half on the narrowed program without `call`.
  have hW : AbiValOf σ sa (NarrowWords.mapVal (ctMapValD (mapVal V))) := by
    have key : ∀ {Γ' : Ctxt jasminDialect} (e : Γ' = nfCtx σ) (W : Valuation Γ'),
        W ≍ ctMapValD (mapVal V) → AbiValOf σ sa W := by
      intro Γ' e W hW'
      subst e
      obtain rfl := eq_of_heq hW'
      exact NFToRoute.abiValOf_mapVal henv V hV
    exact key (nfCtx_wide σ) _ (NarrowWords.mapVal_heq_of_wide (nfCtx_wide σ) _)
  have hback : RuttFA (fun _ _ => True) (fun _ _ => False) (fun _ _ _ _ => True)
      (OutRel fun v sA => σ.ResultOf sa sA (denVal (NarrowWords.wideTy (mapTy (catTy q.1)))
        (Ctxt.Var.lookup (d := jasminDialect) (Γ := [NarrowWords.wideTy (mapTy (catTy q.1))])
          (t := NarrowWords.wideTy (mapTy (catTy q.1))) .here v)))
      (fun o => o = none) (mfTree tf q' (NarrowWords.mapVal (ctMapValD (mapVal V))))
      (fun n => targetTree aMachine prog (fun _ => "") (linkRead m) n 0 sa) := by
    rw [NFProgCallTreeBack.mfTree_eq_ret_denote tf q' hcf']
    cases hv : q'.denote tf (NarrowWords.mapVal (ctMapValD (mapVal V))) with
    | none => exact .fail rfl
    | some v =>
      obtain ⟨prog', sa', hd', hh, hR, -⟩ := regionBack_correct hb sa _ hW hreg tf hv
      rw [hd] at hd'
      cases hd'
      obtain ⟨fuelT, hrun⟩ := NFProgCallTreeBack.run_of_halts_noCall hnc hh
      exact .ret fuelT (NFProgCallTreeBack.targetTree_of_run _ _ hnc hrun)
        fun x hx => by cases hx; exact ⟨sa', rfl, hR⟩
  -- The chain composed with the back half.
  have hcb := RuttSA.trans_ruttFA (fun e₀ e₁ he a₀ ha₀ => by
      rcases ha₀ with ⟨hk, -⟩ | rfl
      · simp [keepL, hl] at hk
      · exact ⟨_, trivial, linkedHandler_chainRA hin e₀ e₁ he.1 he.2⟩)
    (fun r₀ r₁ hr hf => by
      obtain ⟨m₁, ⟨m₀, h1, h2⟩, h3⟩ := hr
      subst hf
      exact NFProgCallTreeRegion.eq_none_of_outRel h1
        (NFProgCallTreeRegion.eq_none_of_outRel h2
          (NFProgCallTreeRegion.eq_none_of_outRel h3 rfl))) hchV hback
  have hacb := NFProgCallTreeModuleAns.RuttFA.answerOut (keepL m)
    (fun _ _ he => by obtain ⟨_, _, h⟩ := he; exact h.elim) (fun _ _ => Or.inr rfl) hcb
  -- The front composed with the rest.
  have hall := RuttSA.trans_ruttFA (fun e₀ e₁ hF _ _ => by
      obtain ⟨⟨-, -, l, hl', -⟩, -⟩ := hF
      simp [hl] at hl')
    (fun r₀ r₁ hr hf => by subst hf; exact NFProgCallTreeCompose.srcFail_of_frontRR hr)
    hfr hacb
  exact NFProgCallTreeOracle.RuttFA.imp (fun _ _ h => h)
    (fun _ _ he => by obtain ⟨_, _, _, _, h⟩ := he; exact h.elim)
    (fun _ _ _ _ he _ => by obtain ⟨_, _, _, _, h⟩ := he; exact h.elim)
    (fun _ _ hr => NFProgCallTreeResult.resRel_of_comp hout hr) (fun _ h => h) hall

end CatCrypt.Crypto.SecureCompilation.Haxc.R3UCallFree
