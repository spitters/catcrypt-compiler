/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FrontLeak
public import CatCrypt.Crypto.Hax.NFToCatLeak
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFDceLeak

/-!
# The level check of the `nfDialect` source of the direct front

The source of the leakage statements of the direct front relative to source runs is the
program of `NFProg nfDialect` that `ImpToNF.impToNF` builds from the body of `te`
(`nfSrcProg`), with the leakage model `nfLeakModel` and the labels `nfSrcLabels s` of the
parameters in the secrecy record `s`. `nfFrontSrcCT s σ te` is the level check
`NFProg.levelCheck'` on that program. The statements themselves are
`NFChainCT.nfFront_routeCT_src` and `NFChainCT.nfFront_routeCT_src_check`.

The impToNF step from the hax expression to `nfSrcProg` is not covered: the source is the
`nfDialect` program, not the hax expression.

## Main definitions

* `nfSrcLabels`, `nfFrontSrcCT`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open _root_.Hax (TExpr)

/-- The labels of the parameters `ps` from the secrecy record `s`, in the context of
    `nfDialect`. -/
def nfSrcLabels (s : _root_.Hax.FnSecrecy) :
    (ps : List (String × NfTy)) → Labels (d := nfDialect) (entryCtx ps)
  | [] => .nil
  | (x, _) :: ps => .cons (paramLevel s x) (nfSrcLabels s ps)

/-- **The level check of the source of the direct front**: `NFProg.levelCheck'` on
    `nfSrcProg σ te` at the leakage `nfLeakModel` from the labels of the parameters in the
    secrecy record `s`. -/
def nfFrontSrcCT (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr) : Bool :=
  match nfSrcProg σ te with
  | some q => (NFProg.levelCheck' nfLeakModel q.2 (nfSrcLabels s (abiEntry σ))).isSome
  | none => false

end CatCrypt.Crypto.SecureCompilation.Haxc
