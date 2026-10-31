/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldCorrect
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4Instances
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.FieldCorrect
public meta import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4Instances

/-!
# The chain of a function over a prime field

`nfChainF P T σ ρ` is the route from a program of `NFProg nfDialect` with one integer result
to a program `RouteProgJ` whose result is a word array, as a chain of named partial steps
(`PassChain.Chain`):

0. `dce`: dead-code elimination `NFProg.dce`;
1. `nfToSum`: the translation `nfToSum T P.p` to `NFProg nfFieldDialect` from the renaming
   `σ`, with the result carried as a field element (`sumStep`);
2. `fieldLower`: the lowering `lowerF P` of the field operations to the blocks of the
   Montgomery template, from the renaming `ρ` (`fieldLowerStep`);
3. `lowerSelects`: the lowering of branches to selects;
4. `aegraph`: the e-graph pass at the rule set `jasminRules`;
5. `exportNFJ`: the export to a route program, else to a carried-register program.

The steps 3 to 5 are the last three steps of `nfChain`. The chain `nfChainFPre` is the
steps 0 to 4; it ends at the structured program of `jasminDialect` that the region back half
`compileRegion` compiles.

## Main definitions

* `nfChainF`, `nfChainFCert` — the chain and its certificate.
* `nfChainFPre`, `nfChainFPreCert` — the chain without the export, and its certificate.
* `fieldChainFront` — the front `impToNF` at the call typing `fieldSigOf` followed by the
  chain, from parameters carried at given kinds.
* `fieldLoweredFront`, `fieldRegionFront` — the program of `jasminDialect` the chain lowers
  the body to, and that program after `lowerSelects` and the e-graph pass.
* `fieldChainRuns` — the source semantics of a function over the field through the chain.

## Main results

* `nfChainF_denote`, `nfChainFPre_denote` — the program the chain returns denotes an array
  holding the Montgomery limbs of the residue of the source result.
* `fieldChainFront_denote`, `fieldRegionFront_denote` — the same for `fieldChainFront` and
  `fieldRegionFront`, from a run of the body with the builtins `primeirBuiltins P.p`.
* `fieldChain_correct_auto` — the halting run and the read-back of `haxc_correct_auto`
  without linked functions for every result of `compileRegion` on the program of `fieldRegionFront`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.Hax.NFFieldSum (nfFieldDialect Kind KRelV SRen SAgree CallsAgree
  primeirFieldTable)
open CatCrypt.Hax.PrimeirNames (OpTable)
open CatCrypt.Crypto.Hax.ImpToNF (tableOf PDenP impToNF entryCtx entryEnv)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (aegraphOptNF)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldCorrect (fieldSigOf fieldSigOf_typedCalls
  denoteSpine_eq_of_spineLamFree arrVal_eq_of_arrLimbs repeatCalls_primeirBuiltins)
open CatCrypt.Hax (primeirBuiltins)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open Ctxt (Var Valuation)
open _root_.Hax (Builtins ImpExpr)

variable {n : Nat} (P : LimbParams n)

/-- **The chain of a function over the field**: `dce`, the translation `nfToSum T P.p`
    from `σ` with an integer result carried as a field element, the field lowering from `ρ`,
    the select lowering, the e-graph pass at `jasminRules`, and `exportNFJ`. -/
def nfChainF (T : OpTable) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ) :
    Chain (NFProg nfDialect Γ [.int]) (RouteProgJ Θ (arrTy n)) :=
  .cons (dceStep Γ [.int]) <| .cons (sumStep P T σ) <|
    .cons (fieldLowerStep P ρ [.inr (.fp P.p)]) <|
    .cons (lowerSelectsStep Θ [arrTy n]) <| .cons (aegraphStep jasminRules Θ [arrTy n]) <|
    .cons (exportStep Θ (arrTy n)) <| .nil _

/-- **The certificate of `nfChainF`** at the builtin table `bi`, the source fuel `tf` and
    the target fuel `cf`. -/
def nfChainFCert (T : OpTable) (hT : T.ok = true) {bi : Builtins} (hbi : CallsAgree T P.p bi)
    (hn : n < 2 ^ 64) (tf cf : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ) :
    Cert (nfChainF P T σ ρ) (nfSemB bi tf Γ [.int]) (routeSem cf Θ (arrTy n)) :=
  .cons (@dceCert nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ tf Γ [.int]) <|
    .cons (sumCert P T hT hbi tf σ) <|
    .cons (fieldLowerCert P hn bi tf cf ρ [.inr (.fp P.p)]) <|
    .cons (lowerSelectsCert cf Θ [arrTy n]) <|
    .cons (aegraphCert jasminRules cf Θ [arrTy n]) <|
    .cons (exportCert cf Θ (arrTy n)) <| .nil _

/-- **The chain computes the Montgomery limbs of the residue.** For a program `prog` the
    chain takes to `rp`, valuations `V`, `X`, `W` related along `σ` and `ρ`, and a run of
    `prog` at the builtins `bi` to the integer `y`: at every fuel `cf`, `rp` denotes an
    array whose limbs are the Montgomery limbs `enc P` of the residue of `y`. -/
theorem nfChainF_denote (T : OpTable) (hT : T.ok = true) {bi : Builtins}
    (hbi : CallsAgree T P.p bi) (hn : n < 2 ^ 64) (tf cf : Nat) {Γ : Ctxt nfDialect}
    {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy n)}
    (h : (nfChainF P T σ ρ).run prog = some rp) (V : Valuation Γ) (X : Valuation Δ)
    (W : Valuation Θ) (hσ : SAgree σ V X) (hρ : JAgree P ρ X W) {y : Int}
    (hp : PDenP bi tf prog V = some (HVector.cons y .nil)) :
    ∃ a, rp.denoteF cf W = some a ∧
      arrLimbs a n 0 = CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont.enc P
        (y : ZMod P.p) := by
  obtain ⟨o', ho', hrel⟩ := (nfChainFCert P T hT hbi hn tf cf σ ρ).sound (V := V) (W := W) h
    ⟨V, rfl, X, hσ, W, hρ, W, rfl, W, rfl, W, rfl, rfl⟩ hp
  obtain ⟨_, rfl, x2, hx2, x3, hx3, _, rfl, _, rfl, x6, hx6, rfl⟩ := hrel
  rcases x2 with _ | ⟨z, _ | _⟩
  rcases x3 with _ | ⟨a, _ | _⟩
  have hz : ((y : Int) : ZMod P.p) = z := hx2.1
  have ha : arrLimbs a n 0 = encL P (t := .fp P.p) z := hx3.1
  have hx6' : x6 = a := (HVector.cons.inj hx6.symm).1
  refine ⟨x6, ho', ?_⟩
  rw [hx6', ha, encL_fp, hz]

/-- **The chain of a function over the field up to the structured program of
    `jasminDialect`**: the steps of `nfChainF` before the export `exportNFJ`. Its result is
    the program the region back half `compileRegion` compiles. -/
def nfChainFPre (T : OpTable) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ) :
    Chain (NFProg nfDialect Γ [.int]) (NFProg jasminDialect Θ [arrTy n]) :=
  .cons (dceStep Γ [.int]) <| .cons (sumStep P T σ) <|
    .cons (fieldLowerStep P ρ [.inr (.fp P.p)]) <|
    .cons (lowerSelectsStep Θ [arrTy n]) <| .cons (aegraphStep jasminRules Θ [arrTy n]) <|
    .nil _

/-- The chain `nfChainF` is `nfChainFPre` followed by the export step. -/
theorem nfChainF_eq_append (T : OpTable) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ) :
    nfChainF P T σ ρ = (nfChainFPre P T σ ρ).append (.cons (exportStep Θ (arrTy n)) <| .nil _) :=
  rfl

/-- **The certificate of `nfChainFPre`** at the builtin table `bi`, the source fuel `tf` and
    the target fuel `cf`. -/
def nfChainFPreCert (T : OpTable) (hT : T.ok = true) {bi : Builtins}
    (hbi : CallsAgree T P.p bi) (hn : n < 2 ^ 64) (tf cf : Nat) {Γ : Ctxt nfDialect}
    {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ) :
    Cert (nfChainFPre P T σ ρ) (nfSemB bi tf Γ [.int]) (nfSem cf jasminDialect Θ [arrTy n]) :=
  .cons (@dceCert nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ tf Γ [.int]) <|
    .cons (sumCert P T hT hbi tf σ) <|
    .cons (fieldLowerCert P hn bi tf cf ρ [.inr (.fp P.p)]) <|
    .cons (lowerSelectsCert cf Θ [arrTy n]) <|
    .cons (aegraphCert jasminRules cf Θ [arrTy n]) <| .nil _

/-- **The chain up to the structured program computes the Montgomery limbs of the
    residue.** For a program `prog` that `nfChainFPre` takes to `q`, valuations `V`, `X`, `W`
    related along `σ` and `ρ`, and a run of `prog` at the builtins `bi` to the integer `y`:
    at every fuel `cf`, `q` denotes a one-element tuple whose array holds the Montgomery
    limbs `enc P` of the residue of `y`. -/
theorem nfChainFPre_denote (T : OpTable) (hT : T.ok = true) {bi : Builtins}
    (hbi : CallsAgree T P.p bi) (hn : n < 2 ^ 64) (tf cf : Nat) {Γ : Ctxt nfDialect}
    {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {q : NFProg jasminDialect Θ [arrTy n]}
    (h : (nfChainFPre P T σ ρ).run prog = some q) (V : Valuation Γ) (X : Valuation Δ)
    (W : Valuation Θ) (hσ : SAgree σ V X) (hρ : JAgree P ρ X W) {y : Int}
    (hp : PDenP bi tf prog V = some (HVector.cons y .nil)) :
    ∃ a, q.denote cf W = some (.cons a .nil) ∧
      arrLimbs a n 0 = CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont.enc P
        (y : ZMod P.p) := by
  obtain ⟨o', ho', hrel⟩ := (nfChainFPreCert P T hT hbi hn tf cf σ ρ).sound (V := V) (W := W)
    h ⟨V, rfl, X, hσ, W, hρ, W, rfl, W, rfl, rfl⟩ hp
  obtain ⟨_, rfl, x2, hx2, x3, hx3, _, rfl, _, rfl, rfl⟩ := hrel
  rcases x2 with _ | ⟨z, _ | _⟩
  rcases x3 with _ | ⟨a, _ | _⟩
  have hz : ((y : Int) : ZMod P.p) = z := hx2.1
  have ha : arrLimbs a n 0 = encL P (t := .fp P.p) z := hx3.1
  refine ⟨a, ho', ?_⟩
  rw [ha, encL_fp, hz]

/-- **The front of a function over the field through the chain**: the body translated by
    `impToNF` at the call typing `fieldSigOf` from the parameters `ps`, with an integer
    result, followed by `nfChainF` at the table `primeirFieldTable` from the parameters
    carried at the kinds `ks`. -/
def fieldChainFront (ps : List (String × NfTy)) (ks : HVector (Kind P.p) (entryCtx ps))
    (e : ImpExpr) :
    Option (RouteProgJ ((Hax.NFFieldSum.kTys ks).map (jTy n)) (arrTy n)) :=
  (impToNF fieldSigOf none (entryEnv ps) e).bind fun o =>
    if h : o.t = .int then
      (nfChainF P primeirFieldTable (kindRen ks) (idRen n _)).run (h ▸ o.prog)
    else none

open _root_.Hax (Env Value denote')
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Crypto.Hax (spineLamFree)
open CatCrypt.Crypto.Hax.ImpToNF (EntryVals entryEnv_rel impToNF_sound PDenP_plug_ret)
open CatCrypt.Crypto.Hax.NFFieldSum (primeirFieldTable_ok primeirFieldTable_agrees)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

/-- **The front through the chain computes the Montgomery limbs of the result.** For a
    result `rp` of `fieldChainFront` on a body without `whileFold`, an environment holding the
    encodings of `V` at the parameters, valuations `X`, `W` related to `V` along the kinds and the carriers, and a
    run of the body with the builtins `primeirBuiltins P.p` to the integer `r`: at every
    fuel, `rp` denotes an array holding the Montgomery limbs of the residue of `r`. -/
theorem fieldChainFront_denote (hn : n < 2 ^ 64) (ps : List (String × NfTy))
    (ks : HVector (Kind P.p) (entryCtx ps)) (e : ImpExpr)
    {rp : RouteProgJ ((Hax.NFFieldSum.kTys ks).map (jTy n)) (arrTy n)}
    (hf : fieldChainFront P ps ks e = some rp)
    (hw : CatCrypt.Crypto.Hax.ImpToNF.whileFoldFree e = true) (env : Env)
    (V : Valuation (entryCtx ps))
    (hV : EntryVals env ps V) (X : Valuation (Hax.NFFieldSum.kTys ks))
    (W : Valuation (d := jasminDialect) ((Hax.NFFieldSum.kTys ks).map (jTy n)))
    (hX : KRelV ks V X) (hW : JRelV P X W) (fuel : Nat) (r : Int) (env' : Env)
    (hrun : (denote' (primeirBuiltins P.p) fuel e).run env = (.val (.int r), env'))
    (cf : Nat) :
    ∃ a, rp.denoteF cf W = some a ∧
      arrLimbs a n 0 = CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont.enc P
        (r : ZMod P.p) := by
  unfold fieldChainFront at hf
  obtain ⟨o, ho, hf⟩ := Option.bind_eq_some_iff.mp hf
  obtain ⟨Wn, hprog, -, hvW⟩ := CatCrypt.Crypto.Hax.ImpToNF.Sound.all_of_whileFree
    (impToNF_sound (primeirBuiltins P.p) fieldSigOf (fieldSigOf_typedCalls P.p)
      (repeatCalls_primeirBuiltins P.p) e none (entryEnv ps) ho fuel)
    (FrontComplete.whileFree_of_opsNB _ (FrontComplete.impToNF_prog_frontOp _ _ none _ o ho hw))
    (entryEnv_rel hV) hrun
  have hp : PDenP (primeirBuiltins P.p) 0 o.prog V = some (.cons (o.res.lookup Wn) .nil) :=
    hprog 0
  obtain ⟨Δ, t, pre, σ, res⟩ := o
  split at hf
  · rename_i ht
    dsimp only at ht
    subst ht
    have hy : res.lookup Wn = r := (Value.int.inj hvW).symm
    obtain ⟨a, ha, hl⟩ := nfChainF_denote P primeirFieldTable primeirFieldTable_ok
      (primeirFieldTable_agrees P.p) hn 0 cf (kindRen ks) (idRen n _) _ hf V X W
      (kindRen_agree ks V X hX) (idRen_agree P _ X W hW) (y := res.lookup Wn) hp
    exact ⟨a, ha, by rw [hl, hy]⟩
  · cases hf

/-- **The program of `jasminDialect` the chain lowers the body to**: the body translated by
    `impToNF` at the call typing `fieldSigOf` from the parameters `ps`, pruned by
    `NFProg.dce`, translated by `sumStep` at the table `primeirFieldTable` from the kinds
    `ks`, and lowered by `lowerF P`; the input of `lowerSelects` in `fieldChainFront`. -/
def fieldLoweredFront (ps : List (String × NfTy)) (ks : HVector (Kind P.p) (entryCtx ps))
    (e : ImpExpr) :
    Option (NFProg jasminDialect ((Hax.NFFieldSum.kTys ks).map (jTy n)) [arrTy n]) :=
  (impToNF fieldSigOf none (entryEnv ps) e).bind fun o =>
    if h : o.t = .int then
      ((sumStep P primeirFieldTable (kindRen ks)).run (NFProg.dce (h ▸ o.prog))).bind fun q =>
        lowerF P q (idRen n _)
    else none

/-- **The structured program of the chain of a function over the field**: on a body without
    `whileFold` (`ImpToNF.whileFoldFree`), the program `fieldLoweredFront` returns, with its
    selects lowered by `lowerSelects` and optimised by
    the e-graph pass at `jasminRules`; the result of `nfChainFPre` on the translated body,
    the input of the export in `fieldChainFront` and the program the region back half
    `compileRegion` compiles. -/
def fieldRegionFront (ps : List (String × NfTy)) (ks : HVector (Kind P.p) (entryCtx ps))
    (e : ImpExpr) :
    Option (NFProg jasminDialect ((Hax.NFFieldSum.kTys ks).map (jTy n)) [arrTy n]) :=
  if CatCrypt.Crypto.Hax.ImpToNF.whileFoldFree e then
    (fieldLoweredFront P ps ks e).map fun q => aegraphOptNF jasminRules (NFProg.lowerSelects q)
  else none

/-- **The structured program of the chain computes the Montgomery limbs of the result.**
    For a result `p` of `fieldRegionFront`, an environment holding the encodings of `V` at
    the parameters, valuations `X`, `W` related to `V` along the kinds and the carriers, and
    a run of the body with the builtins `primeirBuiltins P.p` to the integer `r`: at every
    fuel, `p` denotes a one-element tuple whose array holds the Montgomery limbs of the
    residue of `r`. The proof is the certificate of `nfChainFPre`. -/
theorem fieldRegionFront_denote (hn : n < 2 ^ 64) (ps : List (String × NfTy))
    (ks : HVector (Kind P.p) (entryCtx ps)) (e : ImpExpr)
    {p : NFProg jasminDialect ((Hax.NFFieldSum.kTys ks).map (jTy n)) [arrTy n]}
    (hp : fieldRegionFront P ps ks e = some p) (env : Env) (V : Valuation (entryCtx ps))
    (hV : EntryVals env ps V) (X : Valuation (Hax.NFFieldSum.kTys ks))
    (W : Valuation (d := jasminDialect) ((Hax.NFFieldSum.kTys ks).map (jTy n)))
    (hX : KRelV ks V X) (hW : JRelV P X W) (fuel : Nat) (r : Int) (env' : Env)
    (hrun : (denote' (primeirBuiltins P.p) fuel e).run env = (.val (.int r), env'))
    (cf : Nat) :
    ∃ a, p.denote cf W = some (.cons a .nil) ∧
      arrLimbs a n 0 = CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont.enc P
        (r : ZMod P.p) := by
  have hw : CatCrypt.Crypto.Hax.ImpToNF.whileFoldFree e = true := by
    by_contra hnw
    simp [fieldRegionFront, hnw] at hp
  simp only [fieldRegionFront, hw, ite_true] at hp
  unfold fieldLoweredFront at hp
  obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨o, ho, hq'⟩ := Option.bind_eq_some_iff.mp hq'
  obtain ⟨Wn, hprog, -, hvW⟩ := CatCrypt.Crypto.Hax.ImpToNF.Sound.all_of_whileFree
    (impToNF_sound (primeirBuiltins P.p) fieldSigOf (fieldSigOf_typedCalls P.p)
      (repeatCalls_primeirBuiltins P.p) e none (entryEnv ps) ho fuel)
    (FrontComplete.whileFree_of_opsNB _ (FrontComplete.impToNF_prog_frontOp _ _ none _ o ho hw))
    (entryEnv_rel hV) hrun
  have hp : PDenP (primeirBuiltins P.p) 0 o.prog V = some (.cons (o.res.lookup Wn) .nil) :=
    hprog 0
  obtain ⟨Δ, t, pre, σ, res⟩ := o
  split at hq'
  · rename_i ht
    dsimp only at ht
    subst ht
    obtain ⟨q, hs, hl⟩ := Option.bind_eq_some_iff.mp hq'
    have hy : res.lookup Wn = r := (Value.int.inj hvW).symm
    obtain ⟨a, ha, hla⟩ := nfChainFPre_denote P primeirFieldTable primeirFieldTable_ok
      (primeirFieldTable_agrees P.p) hn 0 cf (kindRen ks) (idRen n _) _
      (q := aegraphOptNF jasminRules (NFProg.lowerSelects q'))
      (by simp only [nfChainFPre, Chain.run, dceStep, Option.bind_some, hs]
          simp only [fieldLowerStep] at hl ⊢
          simp [hl, lowerSelectsStep, aegraphStep])
      V X W (kindRen_agree ks V X hX) (idRen_agree P _ X W hW) (y := res.lookup Wn) hp
    exact ⟨a, ha, by rw [hla, hy]⟩
  · cases hq'

/-- **The source semantics of a function over the field `ZMod P.p`** through the chain,
    at parameters `ps` carried at the kinds `ks`: an environment `env` holding the encodings
    of `V` at the parameters, valuations `X` and `W` related to `V` along the kinds and the
    carriers, with `W` read off the entry state by the layout; a run of the spine reading of
    the body with the builtins `primeirBuiltins P.p` to the integer `r`; and `v` the source
    value of a word array holding the Montgomery limbs of the residue of `r`. -/
def fieldChainRuns (ps : List (String × NfTy)) (ks : HVector (Kind P.p) (entryCtx ps))
    (σ : AbiLayout) (e : ImpExpr) (sa : AState) (v : Value) : Prop :=
  ∃ (env : Env) (V : Valuation (entryCtx ps)) (X : Valuation (Hax.NFFieldSum.kTys ks))
    (W : Valuation (d := jasminDialect) ((Hax.NFFieldSum.kTys ks).map (jTy n)))
    (fuel : Nat) (r : Int) (env' : Env),
    EntryVals env ps V ∧ KRelV ks V X ∧ JRelV P X W ∧ AbiValOf σ sa W ∧
      (denoteSpine (primeirBuiltins P.p) fuel e).run env = (.val (.int r), env') ∧
      ∃ arr : Fin n → BitVec 64,
        arrLimbs arr n 0 = CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont.enc P
          (r : ZMod P.p) ∧ v = arrVal arr

/-- **The compiler theorem for a function over the field through the chain.** For a body
    `e` whose spine binds no closure, the structured program `p` that `fieldRegionFront`
    returns on it, and a result `(P', bytes)` of the region back half `compileRegion` on `p`
    under the export names `a`: from every entry state `sa` satisfying `σ.Regions`, every
    value `v` of a source run of the body (`fieldChainRuns`) is matched by a halting run of
    the machine on the decoded bytes from which `σ` reads back `v`. The conclusion is the
    halting run and the read-back of `haxc_correct_auto`; the proof composes
    `fieldRegionFront_denote` with `compileRegion_correct`. -/
theorem fieldChain_correct_auto (hn : n < 2 ^ 64) (ps : List (String × NfTy))
    (ks : HVector (Kind P.p) (entryCtx ps)) (e : ImpExpr) (hsp : spineLamFree e = true)
    (σ : AbiLayout) (a : AbiNames)
    {p : NFProg jasminDialect ((Hax.NFFieldSum.kTys ks).map (jTy n)) [arrTy n]}
    (hp : fieldRegionFront P ps ks e = some p) (P' : Lprog) (bytes : List (BitVec 8))
    (hc : compileRegion σ a p = some (P', bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : Value)
    (hrun : fieldChainRuns P ps ks σ e sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' v := by
  obtain ⟨env, V, X, W, fuel, r, env', hV, hX, hW, hA, hrun, arr, harr, rfl⟩ := hrun
  rw [denoteSpine_eq_of_spineLamFree _ _ _ hsp] at hrun
  obtain ⟨x, hx, hl⟩ := fieldRegionFront_denote P hn ps ks e hp env V hV X W hX hW fuel r env'
    hrun 0
  obtain ⟨prog, sa', hd, hh, hR, -⟩ := compileRegion_correct hc sa W hA hsep 0 hx
  exact ⟨prog, sa', hd, hh, by rwa [arrVal_eq_of_arrLimbs (harr.trans hl.symm)]⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower
