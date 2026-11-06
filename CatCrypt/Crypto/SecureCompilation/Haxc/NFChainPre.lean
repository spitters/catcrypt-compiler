/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChain

/-!
# The linear route up to the structured program of `jasminDialect`

`nfChainPre Γ t` is the chain `nfChain Γ t` without its last step `exportNFJ`: it ends at the
structured program of `jasminDialect` that the export reads. The region front of an entry
(`NFEntry.frontR`, in `Haxc/NFChainCall.lean`) runs the chain `extChain` at the declared
procedures of the entry, which returns what this chain returns on a program that `nfToCat`
translates after `dce` (`extChain_run_of_nfToCat`).

## Main definitions

* `nfChainPre` — the steps `outTy`, `dce`, `nfToCat`, `aegraph`, `map?`, `lowerSelects`,
  `range`, `aegraph` of `nfChain`.

## Main statements

* `nfChain_eq_append` — `nfChain` is `nfChainPre` followed by the export step.
* `nfChain_run_eq_bind` — a run of `nfChain` is a run of `nfChainPre` followed by `exportNFJ`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes)
open CatCrypt.Crypto.Hax.NFToCat (catTy)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute

/-- **The linear route up to the structured program of `jasminDialect`**: the steps of
    `nfChain Γ t` before the export `exportNFJ`. -/
def nfChainPre (Γ : Ctxt nfDialect) (t : NfTy) :
    Chain (NFProg nfDialect Γ [t])
      (NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) :=
  .cons (outTyStep Γ t) <| .cons (dceStep Γ [t]) <| .cons (nfToCatStep Γ [t]) <|
    .cons (aegraphStep catRules (Γ.map catTy) [catTy t]) <|
    .cons (mapStep catToJasmin catToJasmin_regionTypes (Γ.map catTy) [catTy t]) <|
    .cons (lowerSelectsStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (synRangeStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (aegraphStep jasminRules (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <| .nil _

/-- The chain `nfChain` is `nfChainPre` followed by the export step. -/
theorem nfChain_eq_append (Γ : Ctxt nfDialect) (t : NfTy) :
    nfChain Γ t = (nfChainPre Γ t).append
      (.cons (exportStep (mapCtx (Γ.map catTy)) (mapTy (catTy t))) <| .nil _) :=
  rfl

/-- A run of `nfChain` is a run of `nfChainPre` followed by `exportNFJ`. -/
theorem nfChain_run_eq_bind (Γ : Ctxt nfDialect) (t : NfTy) (p : NFProg nfDialect Γ [t]) :
    (nfChain Γ t).run p = ((nfChainPre Γ t).run p).bind exportNFJ := by
  rw [nfChain_eq_append, Chain.run_append]
  congr 1
  funext q
  cases h : exportNFJ q <;> simp [Chain.run, exportStep, h]

end CatCrypt.Crypto.SecureCompilation.Haxc
