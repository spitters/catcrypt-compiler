/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeKinds

/-!
# The relation of the leaves of the composed call trees

`NFProgCallTreeR3.ruttF_front_compileRegion` relates the source call tree of a module to the
target trees of the calling body at the composition of the relations of the leaves of the front
(`FrontRR`), of the chain (`ChainRR`) and of the back half (the read-back of the result of the
program of `jasminDialect` by the layout). The statement `R3StatementF` relates the leaves by
`resRel`: a source value that is not a control-flow value is read back by the layout from the
target return state. At a result type the back half reads back (`OutTy`), the composition implies
`resRel`: the front reads the source value as the encoding of the result of the program of
`nfDialect`, the chain relates that result to the transported and widened result of the program
of `jasminDialect`, and the value the layout reads of it is the encoding (`denVal_ctTransTy`,
`denVal_wideTy_transTy`).

## Main results

* `resRel_of_comp`: the composition of the relations of the leaves of the front, the chain and
  the back half implies `resRel`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeResult

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (enc)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree (resRel)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (OutRel)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCompose (FrontRR)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (ChainRR)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (OutTy denVal_ctTransTy)
open _root_.Hax

/-- **The composed relation of the leaves implies `resRel`.** At a result type `t` the back half
    reads back, a source leaf related by `FrontRR t` to a leaf of the program of `nfDialect`,
    related by `ChainRR t` to a leaf of the program of `jasminDialect`, related to a target leaf by
    the read-back of its result by `σ` from `sa`, is related to the target leaf by `resRel σ sa`. -/
theorem resRel_of_comp {σ : AbiLayout} {sa : AState} {t : NfTy} (ht : OutTy t)
    {r₀ : Outcome × Env} {r₄ : Option AState}
    (h : Relation.Comp (FrontRR t) (Relation.Comp (ChainRR t) (OutRel fun v sA =>
      σ.ResultOf sa sA (denVal (NarrowWords.wideTy (mapTy (catTy t)))
        (Ctxt.Var.lookup (d := jasminDialect) (Γ := [NarrowWords.wideTy (mapTy (catTy t))])
          (t := NarrowWords.wideTy (mapTy (catTy t))) .here v)))) r₀ r₄) :
    resRel σ sa r₀ r₄ := by
  intro v hv hcf
  obtain ⟨r₁, hF, r₃, ⟨m₂, ⟨m₁, hA, hB⟩, hW⟩, hR⟩ := h
  obtain ⟨y, rfl, rfl⟩ := hF v hv hcf
  obtain ⟨z, rfl, hz⟩ := hA _ rfl
  obtain ⟨z', rfl, rfl⟩ := hB z rfl
  obtain ⟨z'', rfl, rfl⟩ := hW _ rfl
  obtain ⟨sA, rfl, hres⟩ := hR _ rfl
  refine ⟨sA, rfl, ?_⟩
  cases z with
  | cons z₀ zs =>
    obtain ⟨hz₀, -⟩ := hz
    have hval : denVal (NarrowWords.wideTy (mapTy (catTy t)))
        (NarrowWords.transTy (ctTransTy z₀)) = enc t y :=
      (denVal_wideTy_transTy (narrowArrB_mapTy_catTy t) _).trans (denVal_ctTransTy t ht y z₀ hz₀)
    rw [← hval]
    exact hres

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeResult
