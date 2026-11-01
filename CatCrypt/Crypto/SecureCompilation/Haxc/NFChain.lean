/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFToRouteVia
public import CatCrypt.Crypto.SecureCompilation.Haxc.FrontLegOf
public import CatCrypt.Crypto.SecureCompilation.Haxc.Consts
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
public import CatCrypt.Crypto.Hax.NFToCatImages
public import CatCrypt.Crypto.Hax.NFToCatCall
public import CatCrypt.Crypto.Hax.Module
public import CatCrypt.Crypto.Hax.FrontDomain
public import CatCrypt.Crypto.Optimizer.Rewrite.RangeNF
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldLevel

/-!
# The linear route as a certified chain of passes

`nfChain Γ t` is the linear route from a program of `NFProg nfDialect Γ [t]` to a program
`RouteProgJ` (a route program `RouteProg` or a structured program) as a chain
of named partial steps (`PassChain.Chain`):

0. `outTy`: the check `outTyB t` of the result type;
1. `dce`: dead-code elimination `NFProg.dce`;
2. `nfToCat`: the translation `NFToCat.nfToCat` from the readings `TRd.id`;
3. `aegraph`: the e-graph pass at the catCrypt rule set `catRules`;
4. `map?`: the lowering along the partial block lowering `catToJasmin`;
5. `lowerSelects`: the lowering of branches to selects;
6. `range`: the range stage `rangeNF` on structured programs;
7. `aegraph`: the e-graph pass at the jasmin rule set `jasminRules`;
8. `exportNFJ`: the export to a route program, else to a structured program.

`nfChainCert` certifies every step: the steps 1, 3, 4, 5 and 7 by the certificates of
`VIR/NFProgPasses.lean`, step 6 by `rangeNFCert`, the check by the identity
relations, and the translation `nfToCat` and the export by direct certificates from
`nfToCat_sound` and `exportNFJ_denote`, at every fuel of the structured programs.

`nfFront σ te`, the front half of the hax compiler, is the source program `nfSrcProg σ te`
followed by the chain. Its leg `nfFront_leg` is `nfSrcProg_sound` followed by
`nfChain_entry`.

An `NFEntry` is a front that produces a program of `NFProg nfDialect` over the parameters
of a layout, with a builtin table and a call environment for each source program and fuel of
its callees, and a soundness statement relating a source run to a run of that program at
the table of some fuel.
`NFEntry.toFrontLegOf` composes it with `nfChain` into a `FrontLegOfJ`, whose leg follows
from the entry's soundness and `PassChain.Cert.sound`. `haxEntry` is the hax front as an
`NFEntry`, and `nfFrontC` the resulting `FrontLegOfJ`. Its source programs are the modules
`HaxModule`: an entry function, the functions it may call, each with its extraction, and an
inlining depth. The translation `haxToNF` is the source program of the entry at the call
typing of the functions of the module, followed by the inlining of their calls, the body of
each callee prepared by `nfBody`; the source semantics `haxRuns` runs the reference reading of
the entry at the table of the module, where a call of a function of the module is the run of
the reference reading of the extraction of the callee. `ModFn.ofTExpr` makes a function of a
module from a name and an extraction: the parameters are the leading bindings `let x = x` of
the extraction (`texprPrelude`) at the types `modFnTy` reads, and the literal constants the
extraction reads are bound at its head (`bindConsts`). A single function is the module
with no callee (a `TExpr` coerces): its source semantics is the run at `hax64WExit`
(`haxRuns_single`), its translation is `nfSrcProg` at a result type passing `entryResOk`
(`haxToNF_single`), and the compile
function of `nfFrontC` is `nfFront` on the extraction with the constants of the layout bound
(`nfFrontC_front`).

## Main definitions

* `routeSem`, `nfSemB` — the semantics of `RouteProgJ` programs at a fuel and of programs of
  `nfDialect` at a builtin table.
* `outTyStep`, `nfToCatStep`, `exportStep` — the check, the translation and the export as
  chain steps; `nfToCatCert`, `exportCert` their certificates.
* `nfChain`, `nfChainCert` — the chain and its certificate.
* `haxRuns`, `nfFront` — the source semantics of the hax front, and the front half of the
  hax compiler through the chain.
* `nfFrontReport` — the run of `nfFront` that names the refusing step: `nfSrcProg`, or the
  index and name of the first refusing step of `nfChain` (`Chain.runTrace`).
* `NFEntry`, `NFEntry.toFrontLegOf` — an entry into `NFProg nfDialect` and its composite
  front.
* `haxEntry`, `nfFrontC` — the hax front as an entry and as a `FrontLegOfJ`.
* `backArgs`, `catEnvOf` — the section of the transport of argument vectors, and the call
  environment of `catCryptDialect` read off one of `jasminDialect`.
* `denVals`, `tableEnv` — the source values of a vector of values of `jasminDialect`, and
  the call environment of `jasminDialect` read off a builtin table, with word and word-array
  results.
* `linkNameOk`, `linkResOk`, `sigVariants`, `linkedDecls` — the names `hax64WExit` answers
  by no value, the result types of words and word arrays, the argument types that fit a list
  of parameter types, and the declared external procedures of a module at a builtin table:
  its linked functions with a word or word-array result and parameters of words and word
  arrays, each with the call of the table as its function. A call of a linked function is typed from
  the function, is not inlined, and is in the source semantics `haxRuns` the run of the
  source reading of the extraction of the linked function; the table of the linked
  functions and the environment read off it agree on the declarations
  (`extAgree_linkedDecls`). On a module without linked functions the translation reads the
  prepared callees only (`haxToNF_of_linked_nil`, `linkedDecls_of_linked_nil`).
* `linkSigOk`, `intSliceTy`, `modFnIntSlice` — the linked functions whose parameter and
  result types are words and word arrays, the types containing an integer slice, and the
  callees with such a parameter or result type; `haxToNF` refuses a module with a linked
  function failing `linkSigOk` or a callee of `modFnIntSlice` (`haxToNF_eq_some_sig`).
* `entryResOk` — an entry result type, the check `outTyB` of the chain: a word, an integer
  or an array of words; the result type of a program `haxToNF` returns passes it
  (`haxToNF_eq_some_res`).
* `texprPrelude`, `modFnTy`, `ModFn.ofTExpr` — the parameters an extraction binds at its head,
  the type of a parameter or a result of a function of a module, and the function of a module
  made from a name and an extraction.
* `ModFn.ofTExprE`, `modFnsE` — the same construction with the refusal
  `ModuleRefusal.calleeShape` naming the function it does not make and the condition that
  fails; forgetting the refusal gives `ModFn.ofTExpr` (`toOption_ofTExprE`), and `modFnsE`
  leaves no function out (`modFnsE_eq_ok_iff`, `modFnsE_toOption_eq_none_iff`).

## Main results

* `nfChain_run` — the chain runs as the stages of `nfToRouteProgVia` after `NFProg.dce`,
  with the range stage `rangeNF` before the e-graph pass at `jasminRules`, followed by
  `exportNFJ`, under the check `outTyB t`; `nfChain_run_of_exportNF` — a result of `exportNF`
  on the program of the last e-graph pass is a result of the chain as
  `RouteProgJ.straightLoop`.
* `nfChain_denote`, `nfChain_entry` — the statements of `nfToRouteProgVia_denote` and
  `nfToRouteProgVia_entry` for the chain at every fuel, proved from `PassChain.Cert.sound`.
* `nfFrontReport_agrees` — forgetting the refusal report gives `nfFront`.
* `catEnvOf_transports`, `implementedBy_catEnvOf`, `implementedBy_tableEnv` — `catEnvOf E'`
  and `E'` agree along the transport at every call; a declaration is implemented by
  `catEnvOf E'` when `E'` answers its name by a related value; a declaration of words and
  word arrays whose function is the call of a table is implemented by the environment read
  off the table.
* `subTable_linkBi`, `typedCalls_linkBi_of_not_catName`, `arrayOps_linkBi_of_table_none` —
  the table of linked functions whose names the base table does not answer keeps
  `SubTable`, the typing `hax64SigOf` and the array operations of the base table.
* `nfFront_leg` — the leg of the front: a valuation the layout reads off the entry state at
  which the program denotes the value of the source run.
* `haxRuns_single`, `haxToNF_single` — the source semantics and the translation at the
  module of a single function.
* `HaxModule.refusal?_eq_none_iff` — `HaxModule.refusal?`, the first refusal of `haxToNF`
  on a module under a layout, is `none` exactly when `haxToNF` returns a program.
* `nfFrontC_leg` — the leg of `nfFrontC`, at the source semantics `haxRuns`;
  `nfFrontC_front` — at the module of a single function the compile function of `nfFrontC`
  is `nfFront` on the extraction with the constants of the layout bound.
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
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes catToJasmin_varTransports catToJasmin_block
  catToJasmin_mapValExtends catToJasmin_regionTransports)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNF (rangeNF rangeNFStep rangeNFCert)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (enc dec encAll PDenP entryCtx EntryVals entryEnv impToNF
  hax64SigOf hax64NFWordTy TypedCalls entryVals_of_typed impToNF_sound entryEnv_rel
  PDenP_plug_ret tableOf)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower (ctBackTy ctTransTy_ctBackTy)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open Ctxt (Var Valuation)
open _root_.Hax (TExpr Value Env Builtins)
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Crypto.Hax (HaxModule)

/-! ## The semantics along the chain -/

/-- The semantics of programs of `nfDialect` at the builtin table `bi` and the fuel `tf`:
    `nfSem` at the denotation `nfDenote (tableOf bi)`, whose denotation is `PDenP bi tf`. -/
abbrev nfSemB (bi : Builtins) (tf : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    Sem (NFProg nfDialect Γ ts) :=
  @nfSem tf nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ Γ ts

/-- The semantics of `RouteProgJ` programs at the fuel `cf`: valuations of the context as
    inputs, a value of the result type as output, and `RouteProgJ.denoteF cf` as
    denotation. -/
def routeSem (cf : Nat) (Γ : Ctxt jasminDialect) (t : JasminTy) : Sem (RouteProgJ Γ t) where
  In := Valuation Γ
  Out := ⟦t⟧
  den rp W := rp.denoteF cf W

/-! ## The steps without a certificate in `NFProgPasses` -/

/-- The check of the result type `outTyB t` as a chain step: the identity when the check
    holds, a refusal otherwise. -/
def outTyStep (Γ : Ctxt nfDialect) (t : NfTy) :
    Step (NFProg nfDialect Γ [t]) (NFProg nfDialect Γ [t]) :=
  ⟨"outTy", fun p => if outTyB t then some p else none⟩

/-- The certificate of the check of the result type, at equal inputs and outputs. -/
def outTyCert (bi : Builtins) (tf : Nat) (Γ : Ctxt nfDialect) (t : NfTy) :
    StepCert (outTyStep Γ t).run (nfSemB bi tf Γ [t]) (nfSemB bi tf Γ [t]) :=
  StepCert.ofRefines _ fun p q _ _ hf hd => by
    simp only [outTyStep] at hf
    split at hf
    · cases hf
      exact hd
    · cases hf

theorem outTyStep_run_isSome {Γ : Ctxt nfDialect} {t : NfTy} {p q : NFProg nfDialect Γ [t]}
    (h : (outTyStep Γ t).run p = some q) : outTyB t = true := by
  simp only [outTyStep] at h
  split at h
  · assumption
  · cases h

/-- The translation `nfToCat` from the readings `TRd.id` as a chain step. -/
def nfToCatStep (Γ : Ctxt nfDialect) (ts : List NfTy) :
    Step (NFProg nfDialect Γ ts) (NFProg catCryptDialect (Γ.map catTy) (ts.map catTy)) :=
  ⟨"nfToCat", fun p => nfToCat p TRd.id⟩

/-- **The certificate of the translation `nfToCat`**, from `nfToCat_sound`: the input
    relation relates a valuation in range to its mapped valuation `mapVal`, and the output
    relation is `VRelL`. -/
def nfToCatCert {bi : Builtins} (hbi : SubTable bi) (tf cf : Nat) (Γ : Ctxt nfDialect)
    (ts : List NfTy) :
    StepCert (nfToCatStep Γ ts).run (nfSemB bi tf Γ ts)
      (nfSem cf catCryptDialect (Γ.map catTy) (ts.map catTy)) where
  relIn V W := W = mapVal V ∧ ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V)
  relOut o o' := VRelL ts o o'
  sound := by
    rintro p q V W o hf ⟨rfl, hin⟩ hd
    exact nfToCat_sound hbi tf p TRd.id q hf V (mapVal V) o (TRd.agree_id V hin) hd cf

/-- The export `exportNFJ` as a chain step. -/
def exportStep (Γ : Ctxt jasminDialect) (t : JasminTy) :
    Step (NFProg jasminDialect Γ [t]) (RouteProgJ Γ t) :=
  ⟨"exportNFJ", exportNFJ⟩

/-- **The certificate of the export**, from `exportNFJ_denote`: at equal inputs and the same
    fuel, the source result tuple is the one value the exported program denotes. -/
def exportCert (cf : Nat) (Γ : Ctxt jasminDialect) (t : JasminTy) :
    StepCert (exportStep Γ t).run (nfSem cf jasminDialect Γ [t]) (routeSem cf Γ t) where
  relIn := Eq
  relOut o y := o = .cons y .nil
  sound := by
    rintro p rp V W o hf rfl hd
    have he := exportNFJ_denote p hf cf V
    rcases hx : rp.denoteF cf V with _ | x
    · rw [hx, Option.map_none] at he
      exact absurd (hd.symm.trans he) (by simp)
    · rw [hx, Option.map_some] at he
      exact ⟨x, hx, Option.some.inj (hd.symm.trans he)⟩

/-! ## The chain and its certificate -/

/-- **The linear route as a chain**: the check `outTyB t`, `dce`, `nfToCat` from `TRd.id`,
    the e-graph pass at `catRules`, `map?` along `catToJasmin`, the select lowering, the
    range stage `rangeNF`, the e-graph pass at `jasminRules`, and `exportNFJ`. -/
def nfChain (Γ : Ctxt nfDialect) (t : NfTy) :
    Chain (NFProg nfDialect Γ [t]) (RouteProgJ (mapCtx (Γ.map catTy)) (mapTy (catTy t))) :=
  .cons (outTyStep Γ t) <| .cons (dceStep Γ [t]) <| .cons (nfToCatStep Γ [t]) <|
    .cons (aegraphStep catRules (Γ.map catTy) [catTy t]) <|
    .cons (mapStep catToJasmin catToJasmin_regionTypes (Γ.map catTy) [catTy t]) <|
    .cons (lowerSelectsStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (rangeNFStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (aegraphStep jasminRules (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (exportStep (mapCtx (Γ.map catTy)) (mapTy (catTy t))) <| .nil _

/-- **The certificate of the linear route** at the builtin table `bi`, the source fuel `tf`
    and the fuel `cf` of the structured programs of `catCryptDialect` and `jasminDialect`. -/
def nfChainCert {bi : Builtins} (hbi : SubTable bi) (tf cf : Nat) (Γ : Ctxt nfDialect)
    (t : NfTy) :
    Cert (nfChain Γ t) (nfSemB bi tf Γ [t])
      (routeSem cf (mapCtx (Γ.map catTy)) (mapTy (catTy t))) :=
  .cons (outTyCert bi tf Γ t) <|
    .cons (@dceCert nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ tf Γ [t]) <|
    .cons (nfToCatCert hbi tf cf Γ [t]) <|
    .cons (aegraphCert catRules cf (Γ.map catTy) [catTy t]) <|
    .cons (StepCert.ofMap? catToJasmin catToJasmin_regionTypes (fun x => ctTransTy x) ctMapValD
      catToJasmin_varTransports (fun e blk hb V => catToJasmin_block e blk hb V)
      catToJasmin_mapValExtends catToJasmin_regionTransports cf (Γ.map catTy) [catTy t]) <|
    .cons (lowerSelectsCert cf (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (rangeNFCert cf (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (aegraphCert jasminRules cf (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (exportCert cf (mapCtx (Γ.map catTy)) (mapTy (catTy t))) <| .nil _

/-- **The chain runs as the linear route**: after `NFProg.dce`,
    the stages of `nfToRouteProgVia` up to the export, with the range stage `rangeNF` before
    the e-graph pass at `jasminRules`, followed by `exportNFJ`, when the result type passes
    the check `outTyB`. -/
theorem nfChain_run (Γ : Ctxt nfDialect) (t : NfTy) (p : NFProg nfDialect Γ [t]) :
    (nfChain Γ t).run p = if outTyB t then
      (nfToCat (NFProg.dce p) TRd.id).bind fun p' =>
        (NFProg.map? catToJasmin catToJasmin_regionTypes
            (Optimizer.Rewrite.AegraphNF.aegraphOptNF catRules p') (fun v => v)).bind fun q =>
          exportNFJ (Optimizer.Rewrite.AegraphNF.aegraphOptNF jasminRules
            (rangeNF (NFProg.lowerSelects q)))
    else none := by
  cases h : outTyB t <;>
    simp [h, nfChain, Chain.run, outTyStep, dceStep, nfToCatStep, aegraphStep, mapStep,
      lowerSelectsStep, rangeNFStep, exportStep] <;> rfl

/-- **A route program of the export is a result of the chain.** At a result type that passes
    the check `outTyB`, when `nfToCat` returns `p'` on `NFProg.dce p`, the lowering along
    `catToJasmin` returns `q` on the e-graph pass of `p'`, and `exportNF` returns `rp` on the
    e-graph pass at `jasminRules` of the range stage of `NFProg.lowerSelects q`, the chain
    runs `p` to `RouteProgJ.straightLoop rp`. -/
theorem nfChain_run_of_exportNF {Γ : Ctxt nfDialect} {t : NfTy} {p : NFProg nfDialect Γ [t]}
    {rp : RouteProg (mapCtx (Γ.map catTy)) (mapTy (catTy t))} (ht : outTyB t = true)
    {p' : NFProg catCryptDialect (Γ.map catTy) [catTy t]}
    (hp' : nfToCat (NFProg.dce p) TRd.id = some p')
    {q : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]}
    (hq : NFProg.map? catToJasmin catToJasmin_regionTypes
      (Optimizer.Rewrite.AegraphNF.aegraphOptNF catRules p') (fun v => v) = some q)
    (h : exportNF (Optimizer.Rewrite.AegraphNF.aegraphOptNF jasminRules
      (rangeNF (NFProg.lowerSelects q))) = some rp) :
    (nfChain Γ t).run p = some (.straightLoop rp) := by
  rw [nfChain_run, ite_eq_left ht, hp', Option.bind_some, hq]
  exact exportNFJ_of_exportNF h

/-- A program the chain accepts has a result type that passes the check `outTyB`. -/
theorem nfChain_outTyB {Γ : Ctxt nfDialect} {t : NfTy} {p : NFProg nfDialect Γ [t]}
    {rp : RouteProgJ (mapCtx (Γ.map catTy)) (mapTy (catTy t))}
    (h : (nfChain Γ t).run p = some rp) : outTyB t = true := by
  simp only [nfChain, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨q, hq, -⟩ := h
  exact outTyStep_run_isSome hq

/-- **The chain simulates the source program**, in the statement of
    `nfToRouteProgVia_denote` at every fuel `cf`, from `PassChain.Cert.sound`: the program the
    chain returns denotes, at the fuel `cf`, a value whose source value is the encoding of the
    source result; the result type is one the back half reads back by the check the chain
    performs. -/
theorem nfChain_denote {bi : Builtins} (hbi : SubTable bi) (tf cf : Nat) {Γ : Ctxt nfDialect}
    {t : NfTy} (p : NFProg nfDialect Γ [t])
    {rp : RouteProgJ (mapCtx (Γ.map catTy)) (mapTy (catTy t))}
    (h : (nfChain Γ t).run p = some rp) (V : Valuation Γ)
    (hin : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V)) {y : t.denote}
    (hp : PDenP bi tf p V = some (HVector.cons y .nil)) :
    ∃ x, rp.denoteF cf (ctMapValD (mapVal V)) = some x ∧
      denVal (mapTy (catTy t)) x = enc t y := by
  have ht := outTy_of_outTyB t (nfChain_outTyB h)
  obtain ⟨o', ho', hrel⟩ := (nfChainCert hbi tf cf Γ t).sound (V := V)
    (W := ctMapValD (mapVal V)) h
    ⟨V, rfl, V, rfl, mapVal V, ⟨rfl, hin⟩, mapVal V, rfl, ctMapValD (mapVal V), rfl,
      ctMapValD (mapVal V), rfl, ctMapValD (mapVal V), rfl, ctMapValD (mapVal V), rfl,
      ctMapValD (mapVal V), rfl, rfl⟩
    hp
  obtain ⟨_, rfl, _, rfl, x2, hx2, _, rfl, _, rfl, _, rfl, _, rfl, _, rfl, x7, hx7, rfl⟩ :=
    hrel
  rcases x2 with _ | ⟨x, _ | _⟩
  have hx : VRel t y x := hx2.1
  have hx7' : x7 = ctTransTy x := (HVector.cons.inj hx7.symm).1
  refine ⟨x7, ho', ?_⟩
  rw [hx7']
  exact denVal_ctTransTy t ht y x hx

/-- **The input of the back half through the chain**, in the statement of
    `nfToRouteProgVia_entry` at every fuel `cf`. -/
theorem nfChain_entry {bi : Builtins} (hbi : SubTable bi) (tf cf : Nat) {σ : AbiLayout}
    {sa : AState} {env : Env} (hσ : σ.EnvOf sa env) {t : NfTy}
    (p : NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    {rp : RouteProgJ (mapCtx ((entryCtx (abiEntry σ)).map catTy)) (mapTy (catTy t))}
    (h : (nfChain _ t).run p = some rp) (V : Valuation (entryCtx (abiEntry σ)))
    (hV : EntryVals env (abiEntry σ) V) {y : t.denote}
    (hp : PDenP bi tf p V = some (HVector.cons y .nil)) :
    AbiValOf σ sa (ctMapValD (mapVal V)) ∧
      ∃ x, rp.denoteF cf (ctMapValD (mapVal V)) = some x ∧
        denVal (mapTy (catTy t)) x = enc t y :=
  ⟨abiValOf_mapVal hσ V hV, nfChain_denote hbi tf cf p h V (inRange_entry hσ V hV) hp⟩

/-- **The conversion step of the chain does not refuse.** When the translation step
    `nfToCatStep` returns `q` and the e-graph step at `catRules` returns `r` on `q`, the
    step `mapStep catToJasmin` returns a program on `r`: every operation `nfToCat` emits
    has an image in the Jasmin dialect, and the e-graph pass keeps this
    (`NFToCatImages.isSome_map?_aegraphOptNF_nfToCat`). -/
theorem nfChain_mapStep_isSome (Γ : Ctxt nfDialect) (ts : List NfTy)
    (p : NFProg nfDialect Γ ts) (q r : NFProg catCryptDialect (Γ.map catTy) (ts.map catTy))
    (hq : (nfToCatStep Γ ts).run p = some q)
    (hr : (aegraphStep catRules (Γ.map catTy) (ts.map catTy)).run q = some r) :
    ((mapStep catToJasmin catToJasmin_regionTypes (Γ.map catTy) (ts.map catTy)).run
      r).isSome := by
  cases hr
  exact CatCrypt.Crypto.Hax.NFToCatImages.isSome_map?_aegraphOptNF_nfToCat p TRd.id q hq
    (fun v => v)

/-! ## The front half of the hax compiler -/

/-- **The source semantics of the hax front**: the source relation `HaxModule.Runs` of the
    module `m` at the table `hax64WExit`. A hax environment `env` that `σ` reads off the entry
    state `sa`, and a run of the source reading of the entry of `m` from `env`, at the table
    of `m` for some fuel of the callees, to a value `v` that is not a control-flow value. A
    call of a function of `m` is the run of the source reading of the extraction of the
    callee under that table, from the environment binding the names of its parameters to the
    argument values. A call of a linked function of `m` is the value of the meaning `sem` of
    the linked function on the argument values (`HaxModule.linkTable`).

    For a module with linked functions the relation holds of runs that call them. For a
    module whose translation keeps a call of a linked function, `compileA` returns a result
    only when `compileRegion` finds the callee among the linked functions, and
    `haxc_correct_auto` then gives its second disjunct (a run through the call). For a
    module without linked functions the table is the
    reference table of its functions over `hax64WExit` (`HaxModule.table_of_linked_nil`). -/
def haxRuns (σ : AbiLayout) (m : HaxModule) (sa : AState) (v : Value) : Prop :=
  HaxModule.Runs CatCrypt.Crypto.Hax.hax64WExit σ m sa v

/-- **The source semantics of a single function**: at the module of the function `te`,
    `haxRuns` is a hax environment `env` that `σ` reads off the entry state `sa`, and a run
    of the source reading of `te` at `hax64WExit` from `env` to a value `v` that is not a
    control-flow value. -/
theorem haxRuns_single (σ : AbiLayout) (te : TExpr) (sa : AState) (v : Value) :
    haxRuns σ (te : HaxModule) sa v ↔
      ∃ env fuel env', σ.EnvOf sa env ∧
        (denoteSpine CatCrypt.Crypto.Hax.hax64WExit fuel te.erase).run env = (.val v, env') ∧
          v.isControlFlow = false :=
  HaxModule.runs_single _ σ te sa v

open _root_.Hax.FieldTag (fieldArgs fieldHeadB) in
/-- **The table `hax64WExit` at a field head on integer words is the `u64` table**, when the
    head is no wide field head and every value of the `u64` table there is an integer word
    on integer-word arguments: the head is no array constructor or array comparison, and
    `hax64Exit` admits the call as a scalar call (`hax64ScalarAdmit`). -/
theorem hax64WExit_fieldArgs {f : String} {m : _root_.Hax.FieldTag.FieldMethod} {a b : Nat}
    (hF : fieldHeadB f = true) (hpre : ∃ ds, f.toList = m.nameChars ++ '#' :: 'p' :: ds)
    (hwide : ¬ CatCrypt.Crypto.Hax.hax64WideHead f)
    (hv : ∀ v, _root_.Hax.hax64Builtins f (fieldArgs m a b) = some v →
      ∃ n : Nat, v = .int n ∧ n < 2 ^ 64 ∧ a < 2 ^ 64 ∧ (m.binary = true → b < 2 ^ 64)) :
    CatCrypt.Crypto.Hax.hax64WExit f (fieldArgs m a b) =
      _root_.Hax.hax64Builtins f (fieldArgs m a b) := by
  have hne : ∀ s : String, fieldHeadB s = false → f ≠ s := by
    rintro s hs rfl
    rw [hs] at hF
    cases hF
  rw [CatCrypt.Crypto.Hax.hax64WExit_of_ne (hne _ rfl) (hne _ rfl) (hne _ rfl) (hne _ rfl) hwide]
  unfold CatCrypt.Crypto.Hax.hax64Exit
  rcases hb : _root_.Hax.hax64Builtins f (fieldArgs m a b) with _ | v
  · rfl
  · obtain ⟨n, rfl, hn, hab⟩ := hv _ hb
    obtain ⟨ds, hf⟩ := hpre
    obtain ⟨h1, -, h4, hso⟩ := CatCrypt.Crypto.Hax.admit_of_fieldPrefix hf
    have h2 : (f != "len") = true := by simpa using hne "len" rfl
    have h3 : CatCrypt.Crypto.Hax.hax64ArgsShape f (fieldArgs m a b) = true := by
      unfold CatCrypt.Crypto.Hax.hax64ArgsShape
      rw [hso, ite_eq_right (by simp), ite_eq_right (hne "Not" rfl)]
      cases m <;>
        simp [fieldArgs, _root_.Hax.FieldTag.FieldMethod.binary,
          CatCrypt.Crypto.Hax.hax64IntArgs] at hab ⊢ <;> omega
    have h5 : CatCrypt.Crypto.Hax.scalarValNB (.int (n : Nat)) = true := by
      simp only [CatCrypt.Crypto.Hax.scalarValNB, Bool.and_eq_true, decide_eq_true_eq]
      omega
    have hadm : CatCrypt.Crypto.Hax.hax64ScalarAdmit f (fieldArgs m a b)
        (.int (n : Nat)) = true := by
      unfold CatCrypt.Crypto.Hax.hax64ScalarAdmit
      simp only [h1, h2, h3, h4, h5, Bool.and_self]
    simp [hadm, _root_.Hax.Value.isControlFlow]

open _root_.Hax.FieldTag (fieldTag? fieldTagM? fieldArgs fieldArm fieldArmMont fieldVal_lt
  fieldValMont_lt toList_of_fieldTag? toList_of_fieldTagM? fieldHeadB_of_fieldTag?
  fieldHeadB_of_fieldTagM? fieldTag?_of_fieldTagM?) in
/-- **The table `hax64WExit` answers the narrow field heads by their arms**
    (`hax64WExit_fieldArgs`): a narrow tagged head is no wide field head, and a Montgomery head
    is no tagged head. -/
theorem fieldCalls_hax64WExit : FieldLevel.FieldCalls CatCrypt.Crypto.Hax.hax64WExit := by
  refine ⟨fun f m p ht hp a b => ?_, fun f m p k ht hodd hp a b => ?_⟩
  · rw [hax64WExit_fieldArgs (fieldHeadB_of_fieldTag? ht)
      ((toList_of_fieldTag? ht).imp fun _ h => h.1)
      (CatCrypt.Crypto.Hax.not_hax64WideHead_of_lt ht hp) ?_,
      _root_.Hax.hax64Builtins_fieldArgs ht hp a b]
    intro v hv
    rw [_root_.Hax.hax64Builtins_fieldArgs ht hp a b] at hv
    unfold fieldArm at hv
    split at hv
    · rename_i hl
      cases hv
      have := fieldVal_lt m (p := p) (by omega) a b
      exact ⟨_, rfl, by omega, by omega, fun h => by have := hl.2 h; omega⟩
    · cases hv
  · have hwide : ¬ CatCrypt.Crypto.Hax.hax64WideHead f := by
      rintro ⟨_, _, h, _⟩
      rw [fieldTag?_of_fieldTagM? ht] at h
      cases h
    rw [hax64WExit_fieldArgs (fieldHeadB_of_fieldTagM? ht) (toList_of_fieldTagM? ht) hwide ?_,
      _root_.Hax.hax64Builtins_fieldArgsMont ht hodd hp a b]
    intro v hv
    rw [_root_.Hax.hax64Builtins_fieldArgsMont ht hodd hp a b] at hv
    unfold fieldArmMont at hv
    split at hv
    · rename_i hl
      cases hv
      have := fieldValMont_lt m (p := p) (by omega) k a b
      exact ⟨_, rfl, by omega, by omega, fun h => by have := hl.2 h; omega⟩
    · cases hv

open CatCrypt.Crypto.Hax (LinkedFn linkBi linkBi_of_find_none) in
/-- The table of linked functions with no field head as name answers the narrow field heads
    by their arms when the base table does. -/
theorem fieldCalls_linkBi (ls : List LinkedFn) {bi : Builtins} (hF : FieldLevel.FieldCalls bi)
    (hft : ∀ l ∈ ls, _root_.Hax.FieldTag.fieldHeadB l.name = false) :
    FieldLevel.FieldCalls (linkBi ls bi) := by
  have hg : ∀ g, _root_.Hax.FieldTag.fieldHeadB g = true → ls.find? (·.name == g) = none := by
    intro g hg
    rw [List.find?_eq_none]
    intro f hf hfg
    have h := hft f hf
    rw [show f.name = g by simpa using hfg, hg] at h
    cases h
  refine ⟨fun g m p ht hp a b => ?_, fun g m p k ht hodd hp a b => ?_⟩
  · rw [linkBi_of_find_none ls bi (hg g (_root_.Hax.FieldTag.fieldHeadB_of_fieldTag? ht))]
    exact hF.canon g m p ht hp a b
  · rw [linkBi_of_find_none ls bi (hg g (_root_.Hax.FieldTag.fieldHeadB_of_fieldTagM? ht))]
    exact hF.mont g m p k ht hodd hp a b

/-- **The table `hax64WExit` answers the wide tagged heads as the `u64` table**: it is a
    sub-table of `Hax.hax64Builtins` (`hax64WExit_sub`). -/
theorem fieldCallsWide_hax64WExit :
    FieldLevel.FieldCallsWide CatCrypt.Crypto.Hax.hax64WExit :=
  fun _ _ _ _ _ _ _ h => CatCrypt.Crypto.Hax.hax64WExit_sub h

open CatCrypt.Crypto.Hax (LinkedFn linkBi linkBi_of_find_none) in
/-- The table of linked functions with no tagged head as name answers the wide tagged heads as
    the `u64` table when the base table does. -/
theorem fieldCallsWide_linkBi (ls : List LinkedFn) {bi : Builtins}
    (hF : FieldLevel.FieldCallsWide bi)
    (hft : ∀ l ∈ ls, _root_.Hax.FieldTag.fieldTag? l.name = none) :
    FieldLevel.FieldCallsWide (linkBi ls bi) := by
  intro g m p ht hp args v hv
  have hg : ls.find? (·.name == g) = none := by
    rw [List.find?_eq_none]
    intro f hf hfg
    have h := hft f hf
    rw [show f.name = g by simpa using hfg, ht] at h
    cases h
  rw [linkBi_of_find_none ls bi hg] at hv
  exact hF g m p ht hp args v hv

/-- **The table `hax64WExit` is the `u64` table at the wide tagged heads**: a tagged head at a
    modulus `p ≥ 2⁶⁴` is a wide field head, at which `hax64WExit` is `Hax.hax64Builtins`
    (`hax64WExit_wide`). -/
theorem fieldCallsWideEq_hax64WExit :
    FieldLevel.FieldCallsWideEq CatCrypt.Crypto.Hax.hax64WExit :=
  fun _ m p ht hp args => CatCrypt.Crypto.Hax.hax64WExit_wide ⟨m, p, ht, hp⟩ args

open CatCrypt.Crypto.Hax (LinkedFn linkBi linkBi_of_find_none) in
/-- The table of linked functions with no tagged head as name is the `u64` table at the wide
    tagged heads when the base table is. -/
theorem fieldCallsWideEq_linkBi (ls : List LinkedFn) {bi : Builtins}
    (hF : FieldLevel.FieldCallsWideEq bi)
    (hft : ∀ l ∈ ls, _root_.Hax.FieldTag.fieldTag? l.name = none) :
    FieldLevel.FieldCallsWideEq (linkBi ls bi) := by
  intro g m p ht hp args
  have hg : ls.find? (·.name == g) = none := by
    rw [List.find?_eq_none]
    intro f hf hfg
    have h := hft f hf
    rw [show f.name = g by simpa using hfg, ht] at h
    cases h
  rw [linkBi_of_find_none ls bi hg]
  exact hF g m p ht hp args

/-- **The front half of the hax compiler**: the source program `nfSrcProg σ te` (the body
    `nfBody te` accepted by the typed front and translated to `NFProg nfDialect` from the
    parameters `abiEntry σ`), followed by the chain `nfChain`, with the type of its
    result. -/
def nfFront (σ : AbiLayout) (te : TExpr) :
    Option (Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))) :=
  (nfSrcProg σ te).bind fun q => ((nfChain _ q.1).run q.2).map fun rp => ⟨q.1, rp⟩

/-- **The refusal report of the front half**: the run of `nfFront σ te` that, on refusal,
    names the refusing step. A refusal of the source program is reported as `nfSrcProg`; a
    refusal by the chain as `nfChain step i: n`, with the index `i` (from `0`) and the name
    `n` of the first refusing step of `nfChain`, from `Chain.runTrace`. -/
def nfFrontReport (σ : AbiLayout) (te : TExpr) :
    Except String (Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))) :=
  match nfSrcProg σ te with
  | none => .error "nfSrcProg"
  | some q =>
    match (nfChain _ q.1).runTrace q.2 with
    | .error (i, n) => .error s!"nfChain step {i}: {n}"
    | .ok rp => .ok ⟨q.1, rp⟩

/-- **The refusal report agrees with the front half**: forgetting the report gives
    `nfFront`. -/
theorem nfFrontReport_agrees (σ : AbiLayout) (te : TExpr) :
    (nfFrontReport σ te).toOption = nfFront σ te := by
  unfold nfFrontReport nfFront
  cases nfSrcProg σ te with
  | none => rfl
  | some q =>
    simp only [Option.bind_some]
    rw [← Chain.runTrace_eq_run]
    cases (nfChain _ q.1).runTrace q.2 <;> rfl

/-- **The leg of the front.** For a result `⟨t, rp⟩` of `nfFront σ te`, from every
    environment `σ` reads off an entry state `sa`, a run of the source reading of `te` to a
    value `v` that is not a control-flow value gives a valuation of the route program's
    context that `σ` reads off `sa` (`AbiValOf`) at which, at every fuel `cf`, the program
    denotes a value whose source value `denVal` is `v`. The proof is `nfSrcProg_sound`
    followed by `nfChain_entry`. -/
theorem nfFront_leg (σ : AbiLayout) (te : TExpr)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))) (hf : nfFront σ te = some p)
    (sa : AState) (env : Env) (henv : σ.EnvOf sa env)
    (fuel : Nat) (v : Value) (env' : Env)
    (hrun : (denoteSpine CatCrypt.Crypto.Hax.hax64WExit fuel te.erase).run env = (.val v, env'))
    (hcf : v.isControlFlow = false) :
    ∃ V : Valuation (nfCtx σ), AbiValOf σ sa V ∧
      ∀ cf : Nat, ∃ x, p.2.denoteF cf V = some x ∧ v = denVal _ x := by
  obtain ⟨q, hq, hf⟩ := Option.bind_eq_some_iff.mp hf
  obtain ⟨rp, hrp, rfl⟩ := Option.map_eq_some_iff.mp hf
  obtain ⟨V, y, hV, ⟨N, hp⟩, hv⟩ := nfSrcProg_sound hq henv hrun hcf
  refine ⟨_, abiValOf_mapVal henv V hV, fun cf => ?_⟩
  obtain ⟨-, x, hx, hden⟩ := nfChain_entry CatCrypt.Crypto.Hax.hax64WExit_subTable N cf henv
    q.2 hrp V hV (hp N le_rfl)
  exact ⟨x, hx, hv.trans hden.symm⟩

/-! ## Call environments read off a builtin table and off one another -/

/-- The section of the transport of argument vectors: `ctBackTy` at every component. -/
def backArgs : {as : List CryptoTy} → Valuation (d := jasminDialect) (as.map mapTy) →
    Valuation (d := catCryptDialect) as
  | [], _ => .nil
  | t :: _, .cons x W => .cons (ctBackTy t x) (backArgs W)

/-- `backArgs` is a section of the transport of argument vectors. -/
theorem transArgs_backArgs : {as : List CryptoTy} →
    (W : Valuation (d := jasminDialect) (as.map mapTy)) →
    transArgs mapTy (fun x => ctTransTy x) (backArgs W) = W
  | [], .nil => rfl
  | t :: _, .cons x W => by
      change HVector.cons (ctTransTy (ctBackTy t x))
        (transArgs mapTy (fun x => ctTransTy x) (backArgs W)) = _
      rw [ctTransTy_ctBackTy, transArgs_backArgs W]

/-- **The call environment of `catCryptDialect` read off the environment `E'` of
    `jasminDialect`**: the callee of `f` at `as → rs` is the callee of `E'` at the mapped
    signature on the transported arguments, with its results read back by `backArgs`. -/
def catEnvOf (E' : CallEnv jasminDialect) : CallEnv catCryptDialect where
  call f as rs x :=
    (E'.call f (as.map mapTy) (rs.map mapTy) (transArgs mapTy (fun x => ctTransTy x) x)).map
      backArgs

/-- **`catEnvOf E'` and `E'` agree along the transport at every call.** -/
theorem catEnvOf_transports (E' : CallEnv jasminDialect) :
    (catEnvOf E').Transports E' (fun as => as.map mapTy)
      (fun x => transArgs mapTy (fun x => ctTransTy x) x) (fun _ _ _ => True) := by
  intro f as rs x _
  change _ = ((E'.call f (as.map mapTy) (rs.map mapTy) _).map backArgs).map _
  cases E'.call f (as.map mapTy) (rs.map mapTy) (transArgs mapTy (fun x => ctTransTy x) x) with
  | none => rfl
  | some W => exact congrArg some (transArgs_backArgs W).symm

/-- **A declaration is implemented by `catEnvOf E'`** when `E'` answers its name, at the
    mapped signature and on the transport of every vector related to arguments on which the
    function of the declaration returns `y`, by one value whose section is related to
    `y`. -/
theorem implementedBy_catEnvOf (E' : CallEnv jasminDialect) (d : ExtDecl)
    (h : ∀ (xs : Valuation (d := nfDialect) d.args)
      (ws : Valuation (d := catCryptDialect) (d.args.map catTy)) (y : d.ret.denote),
      VRelL d.args xs ws → d.sem xs = some y →
      ∃ v : ⟦mapTy (catTy d.ret)⟧,
        E'.call d.name ((d.args.map catTy).map mapTy) [mapTy (catTy d.ret)]
          (transArgs mapTy (fun x => ctTransTy x) ws) = some (HVector.cons v .nil) ∧
          VRel d.ret y (ctBackTy (catTy d.ret) v)) :
    d.ImplementedBy (catEnvOf E') := by
  intro xs ws y hws hy
  obtain ⟨v, hv, hrel⟩ := h xs ws y hws hy
  refine ⟨ctBackTy (catTy d.ret) v, ?_, hrel⟩
  change (E'.call d.name ((d.args.map catTy).map mapTy) [mapTy (catTy d.ret)] _).map
    (backArgs (as := [catTy d.ret])) = _
  rw [hv]
  rfl

/-- The source values of a vector of values of `jasminDialect`: `denVal` at every
    component. -/
def denVals : {as : List JasminTy} → Valuation (d := jasminDialect) as → List Value
  | [], _ => []
  | t :: _, .cons x W => denVal t x :: denVals W

/-- **The call environment of `jasminDialect` read off the builtin table `bi`**: a call of
    `f` with one result of the type `reg 64` is the call of `bi` at `f` on the source values
    of the arguments, when `dec` decodes its value as a `64`-bit word; a call with one result
    of the type `stackArr 64 n` is that call when `dec` decodes its value as an array of `n`
    `64`-bit words; every other call refuses. -/
def tableEnv (bi : Builtins) : CallEnv jasminDialect where
  call f _ rs x :=
    match rs with
    | [.reg 64] => (bi f (denVals x)).bind fun v =>
        (dec (.word 64) v).map fun y =>
          (HVector.cons y .nil : Valuation (d := jasminDialect) [.reg 64])
    | [.stackArr 64 n] => (bi f (denVals x)).bind fun v =>
        (dec (.arr n (.word 64)) v).map fun y =>
          (HVector.cons y .nil : Valuation (d := jasminDialect) [.stackArr 64 n])
    | _ => none

/-- The result types of the declared procedures: the `64`-bit word and an array of `64`-bit
    words. -/
def linkResOk : NfTy → Bool
  | .word 64 => true
  | .arr _ (.word 64) => true
  | _ => false

/-- A result type of `linkResOk` is the `64`-bit word or an array of `64`-bit words. -/
theorem linkResOk_iff {r : NfTy} :
    linkResOk r = true ↔ r = .word 64 ∨ ∃ n, r = .arr n (.word 64) := by
  unfold linkResOk
  split <;> simp_all

/-- The source values of the transport of a vector related to arguments of types of words
    and word arrays (`wordArrTy`) are the encodings of the arguments. -/
theorem denVals_transArgs : ∀ (as : List NfTy), (∀ t ∈ as, wordArrTy t = true) →
    ∀ (xs : Valuation (d := nfDialect) as)
      (ws : Valuation (d := catCryptDialect) (as.map catTy)), VRelL as xs ws →
      denVals (transArgs mapTy (fun x => ctTransTy x) ws) = encAll as xs
  | [], _, .nil, .nil, _ => rfl
  | t :: as, h, .cons x xs, .cons w ws, hr => by
      have ht : outTyB t = true := by
        have := h t List.mem_cons_self
        cases t with
        | arr n s => cases s <;> simp_all [wordArrTy, hax64NFWordTy, outTyB]
        | _ => simp_all [wordArrTy, hax64NFWordTy, outTyB]
      change denVal (mapTy (catTy t)) (ctTransTy w) ::
        denVals (transArgs mapTy (fun x => ctTransTy x) ws) = enc t x :: encAll as xs
      rw [denVal_ctTransTy t (outTy_of_outTyB t ht) x w hr.1,
        denVals_transArgs as (fun s hs => h s (List.mem_cons_of_mem _ hs)) xs ws hr.2]

/-- **A declaration whose function is the call of a table is implemented by the environment
    read off the table.** For a name `f`, argument types `as` of words and word arrays
    (`wordArrTy`) and a result type `r` of `linkResOk` (the `64`-bit word or an array of
    `64`-bit words), the declaration with the function `(tableOf bi).call f as r` is
    implemented by `catEnvOf (tableEnv bi)`. -/
theorem implementedBy_tableEnv (bi : Builtins) (f : String) (as : List NfTy) (r : NfTy)
    (hr : linkResOk r = true) (has : ∀ t ∈ as, wordArrTy t = true) :
    (ExtDecl.mk f as r ((tableOf bi).call f as r)).ImplementedBy
      (catEnvOf (tableEnv bi)) := by
  refine implementedBy_catEnvOf _ _ fun xs ws y hws hy => ?_
  obtain ⟨v, hv, hd⟩ := Option.bind_eq_some_iff.mp hy
  have hx := denVals_transArgs as has xs ws hws
  rcases linkResOk_iff.mp hr with rfl | ⟨n, rfl⟩
  · refine ⟨y, ?_, rfl⟩
    change ((bi f (denVals (transArgs mapTy (fun x => ctTransTy x) ws))).bind fun v =>
      (dec (.word 64) v).map fun y =>
        (HVector.cons y .nil : Valuation (d := jasminDialect) [.reg 64])) = _
    rw [hx, hv, Option.bind_some, hd]
    rfl
  · refine ⟨y, ?_, fun _ => rfl⟩
    change ((bi f (denVals (transArgs mapTy (fun x => ctTransTy x) ws))).bind fun v =>
      (dec (.arr n (.word 64)) v).map fun y =>
        (HVector.cons y .nil : Valuation (d := jasminDialect) [.stackArr 64 n])) = _
    rw [hx, hv, Option.bind_some, hd]
    rfl

/-! ## Entries into `NFProg nfDialect` -/

/-- **An entry into `NFProg nfDialect`**: source programs `Src` with a source semantics
    `Runs` read off an entry state through a layout, export names, a translation `toNF` of a
    source program under a layout to a program of `NFProg nfDialect` over the parameters
    `abiEntry σ` with its result type, and, for each source program `s` and each fuel `k` of
    its callees, a builtin table `bi s k` and a call environment `env s k` of
    `jasminDialect`, the environment in which every call refuses unless given. An entry also
    gives each source program its declared external procedures `decls s`, none unless given:
    the leaf calls the translation with declarations `nfToCatExt` keeps as calls.

    Soundness: a source run from an entry state satisfying `σ.Regions` to a value `v` gives
    a fuel `k` of the callees, an environment `σ` reads off the entry state, a valuation of
    the parameters whose encodings it holds, and a run of the translated program at that
    valuation and the table `bi s k` to a value `y` whose encoding is `v`. The table
    `bi s k` agrees with the `u64` table (`SubTable`), and it agrees with the environment
    `catEnvOf (env s k)` on a list `D` of declarations that declares the names and
    signatures `decls s` declares (`ExtAgree`): the table answers each declared name by the
    function of its declaration in `D`, and `env s k` implements that function. The
    functions of the declarations of `D` may depend on `k`; the translation reads the names
    and signatures only. At a source program the translation accepts, the table of every
    fuel answers the tagged field heads by their arms (`fieldCalls`) and is the `u64` table at
    the wide tagged heads (`fieldCallsWide`). -/
structure NFEntry where
  /-- The source programs. -/
  Src : Type
  /-- The source semantics read off an entry state through a layout. -/
  Runs : AbiLayout → Src → AState → Value → Prop
  /-- The export names of the back half, from the function symbol and the layout. -/
  names : String → AbiLayout → AbiNames
  /-- The translation to a program of `NFProg nfDialect` over the parameters of the layout,
      with its result type. -/
  toNF : (σ : AbiLayout) → Src →
    Option (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
  /-- The builtin table of the translated program's semantics, for a source program and a
      fuel of its callees. -/
  bi : Src → Nat → Builtins
  /-- The call environment of `jasminDialect` that answers the declared procedures of a
      source program, at a fuel of its callees. -/
  env : Src → Nat → CallEnv jasminDialect := fun _ _ => CallEnv.empty
  /-- The declared external procedures of a source program. -/
  decls : Src → List ExtDecl := fun _ => []
  /-- A source run is matched, at some fuel of the callees, by a run of the translated
      program, at a program fuel at most that fuel, at a valuation of the parameters the
      layout reads off the entry state; the
      table of that fuel agrees with the `u64` table at the calls `nfToCat` admits, and with
      the call environment of that fuel on declarations of the declared names and
      signatures. -/
  sound : ∀ (σ : AbiLayout) (s : Src)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]),
    toNF σ s = some q → ∀ (sa : AState) (v : Value), σ.Regions sa → Runs σ s sa v →
      ∃ (k : Nat) (D : List ExtDecl) (e : Env) (V : Valuation (entryCtx (abiEntry σ)))
        (y : q.1.denote),
        (∀ f as r, declared D f as r = declared (decls s) f as r) ∧ SubTable (bi s k) ∧
          ExtAgree (bi s k) (catEnvOf (env s k)) D ∧
          σ.EnvOf sa e ∧ EntryVals e (abiEntry σ) V ∧
            (∃ tf, tf ≤ k ∧ PDenP (bi s k) tf q.2 V = some (HVector.cons y .nil)) ∧
              v = enc q.1 y
  /-- At a source program the translation accepts, the table of every fuel answers the
      tagged field heads by their arms. -/
  fieldCalls : ∀ (σ : AbiLayout) (s : Src)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]),
    toNF σ s = some q → ∀ k, FieldLevel.FieldCalls (bi s k)
  /-- At a source program the translation accepts, the table of every fuel is the `u64`
      table at the wide tagged heads. -/
  fieldCallsWide : ∀ (σ : AbiLayout) (s : Src)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]),
    toNF σ s = some q → ∀ k, FieldLevel.FieldCallsWideEq (bi s k)

/-- **The front of an entry**: the translation `toNF` followed by the chain `nfChain`. -/
def NFEntry.front (E : NFEntry) (σ : AbiLayout) (s : E.Src) : Option AnyRouteProgJ :=
  (E.toNF σ s).bind fun q => ((nfChain _ q.1).run q.2).map fun rp => ⟨nfCtx σ, _, rp⟩

/-- **An entry composed with the chain is a front**, at the call environment in which every
    call refuses. Its leg is the entry's soundness, then `nfChain_entry` at the source fuel
    the soundness gives and the target fuel `0`,
    which is `PassChain.Cert.sound` with `inRange_entry`, `abiValOf_mapVal` and
    `denVal_ctTransTy`. The chain `nfChain` translates by `nfToCat`, which keeps no call of
    a declared procedure. -/
def NFEntry.toFrontLegOf (E : NFEntry) : FrontLegOfJ where
  Src := E.Src
  Runs := E.Runs
  front := E.front
  names := E.names
  leg σ s p hf sa v hreg hrun := by
    obtain ⟨q, hq, hf⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨rp, hrp, rfl⟩ := Option.map_eq_some_iff.mp hf
    obtain ⟨k, D, env, V, y, -, hsub, -, henv, hV, ⟨tf, -, hp⟩, hv⟩ :=
      E.sound σ s q hq sa v hreg hrun
    obtain ⟨hA, x, hx, hden⟩ := nfChain_entry hsub tf 0 henv q.2 hrp V hV hp
    exact ⟨_, 0, x, hA, hx, hv.trans hden.symm⟩

/-! ## The hax front as an entry -/

open CatCrypt.Crypto.Hax (ModFn refBi refBi_of_find_none find?_prep) in
/-- The array operations of `bi` are those of the reference table of functions whose prepared
    callees have no array-operation name. -/
theorem arrayOps_refBi {P : TExpr → _root_.Hax.ImpExpr} {fs : List ModFn}
    (h : crateArrOk (fs.map (ModFn.prep P)) = true) {bi : Builtins}
    (hbi : _root_.Hax.InlineMap.ArrayOps bi) (fuel n : Nat) :
    _root_.Hax.InlineMap.ArrayOps (refBi fs bi fuel n) := by
  simp only [crateArrOk, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Option.isNone_iff_eq_none, find?_prep, Option.map_eq_none_iff] at h
  obtain ⟨hl, hi, hu, -⟩ := h
  exact ⟨fun vs => (hbi.len vs).imp (refBi_of_find_none fs bi fuel n hl _).trans
      (refBi_of_find_none fs bi fuel n hl _).trans,
    fun vs j hj hcf => (refBi_of_find_none fs bi fuel n hi _).trans (hbi.index vs j hj hcf),
    fun vs j v hj => (refBi_of_find_none fs bi fuel n hu _).trans (hbi.update vs j v hj)⟩

open CatCrypt.Crypto.Hax (LinkedFn linkBi linkBi_of_find_none) in
/-- The table of linked functions with no name of a translated call (`CatName`) agrees with
    the `u64` table when the base table does. -/
theorem subTable_linkBi (fs : List LinkedFn) {bi : Builtins} (hbi : SubTable bi)
    (hfs : ∀ f ∈ fs, ¬ CatName f.name) : SubTable (linkBi fs bi) := by
  intro g vals v hc hv
  have hg : fs.find? (·.name == g) = none := by
    rw [List.find?_eq_none]
    intro f hf hfg
    exact hfs f hf (by rw [show f.name = g by simpa using hfg]; exact hc)
  rw [linkBi_of_find_none fs bi hg] at hv
  exact hbi g vals v hc hv

open CatCrypt.Crypto.Hax (LinkedFn linkBi linkBi_of_find_none) in
/-- The table of linked functions with no name of a translated call (`CatName`) and no
    tagged field head as name is typed by `hax64SigOf` when the base table is: `hax64SigOf`
    types the names of translated calls and the tagged field calls only
    (`ImpToNF.hax64SigOf_name`). -/
theorem typedCalls_linkBi_of_not_catName (fs : List LinkedFn) {bi : Builtins}
    (hT : TypedCalls bi hax64SigOf) (hfs : ∀ f ∈ fs, ¬ CatName f.name)
    (hft : ∀ f ∈ fs, _root_.Hax.FieldTag.fieldTag? f.name = none) :
    TypedCalls (linkBi fs bi) hax64SigOf := by
  intro g as r hsig xs v hb
  have hg : fs.find? (·.name == g) = none := by
    rw [List.find?_eq_none]
    intro f hf hfg
    have hfg' : f.name = g := by simpa using hfg
    rcases CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf_name hsig with h1 | h2 | h3 | h3 | h3 | h3 | h4
    · exact hfs f hf (by rw [hfg']; exact Or.inl h1)
    · exact hfs f hf (by rw [hfg']; exact Or.inr (Or.inl h2))
    · exact hfs f hf (by rw [hfg']; exact Or.inr (Or.inr (Or.inl h3)))
    · exact hfs f hf (by rw [hfg']; exact Or.inr (Or.inr (Or.inr (Or.inl h3))))
    · exact hfs f hf (by rw [hfg']; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3)))))
    · exact hfs f hf (by rw [hfg']; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h3)))))
    · have h := hft f hf
      rw [hfg'] at h
      rw [h] at h4
      cases h4
  rw [linkBi_of_find_none fs bi hg] at hb
  exact hT g as r hsig xs v hb

open CatCrypt.Crypto.Hax (LinkedFn linkBi linkBi_of_find_none) in
/-- The array operations of `bi` are those of the table of linked functions whose names `bi`
    answers by no value. -/
theorem arrayOps_linkBi_of_table_none (fs : List LinkedFn) {bi : Builtins}
    (hbi : _root_.Hax.InlineMap.ArrayOps bi)
    (hfs : ∀ f ∈ fs, ∀ vals, bi f.name vals = none) :
    _root_.Hax.InlineMap.ArrayOps (linkBi fs bi) := by
  have key : ∀ g vals v, bi g vals = some v → linkBi fs bi g vals = some v := by
    intro g vals v hv
    have hg : fs.find? (·.name == g) = none := by
      rw [List.find?_eq_none]
      intro f hf hfg
      have := hfs f hf vals
      rw [show f.name = g by simpa using hfg, hv] at this
      cases this
    rw [linkBi_of_find_none fs bi hg, hv]
  exact ⟨fun vs => (hbi.len vs).imp (key _ _ _) (key _ _ _), fun vs j hj hcf => key _ _ _ (hbi.index vs j hj hcf),
    fun vs j v hj => key _ _ _ (hbi.update vs j v hj)⟩

/-- **A name the table `hax64WExit` answers by no value and the translation `NFToCat.catOp`
    of an operation does not read**: the name of no scalar call (`exitScalarRes`), none of
    `index`, `array_update`, `array_lit`, `repeat`, no name of the scalar table
    `ImpToNF.hax64NFScalar`, and not `declassify`. The translation of a call tries `catOp`
    before the declared procedures, and `catOp` reads a call by `index`, `array_update`,
    `declassify` and the names of that table. -/
def linkNameOk (f : String) : Bool :=
  !(CatCrypt.Crypto.Hax.exitScalarRes f || f == "index" || f == "array_update"
    || f == "array_lit" || f == "repeat")
    && !(CatCrypt.Crypto.Hax.ImpToNF.hax64NFScalar ()).contains f
    && !(f == "declassify")

/-- The table `hax64WExit` answers a name of `linkNameOk` by no value. -/
theorem hax64WExit_of_linkNameOk {f : String} (h : linkNameOk f = true) (vals : List Value) :
    CatCrypt.Crypto.Hax.hax64WExit f vals = none := by
  simp only [linkNameOk, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, -⟩, -⟩ := h
  exact CatCrypt.Crypto.Hax.hax64WExit_none h0 h1 h2 h3 h4 vals

/-- The table of the linked functions over `hax64WExit` satisfies `RepeatCalls` when every
    linked name passes `linkNameOk`, which excludes `repeat`. -/
theorem linkTable_repeatCalls {m : CatCrypt.Crypto.Hax.HaxModule}
    (hlk : ∀ l ∈ m.linked, linkNameOk l.name = true) :
    CatCrypt.Crypto.Hax.ImpToNF.RepeatCalls (m.linkTable CatCrypt.Crypto.Hax.hax64WExit) :=
  CatCrypt.Crypto.Hax.linkBi_repeatCalls _ CatCrypt.Crypto.Hax.repeatCalls_hax64WExit
    (List.find?_eq_none.mpr fun l hl h => by
      have hk := hlk l hl
      rw [beq_iff_eq.mp h] at hk
      simp [linkNameOk] at hk)

/-- A name of `linkNameOk` is no tagged field head: a tagged head contains `#`, so it is the
    name of a scalar call (`exitScalarRes`). -/
theorem fieldTag?_of_linkNameOk {f : String} (h : linkNameOk f = true) :
    _root_.Hax.FieldTag.fieldTag? f = none := by
  cases ht : _root_.Hax.FieldTag.fieldTag? f with
  | none => rfl
  | some mp =>
      exfalso
      simp only [linkNameOk, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨h0, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
      have hm := _root_.Hax.FieldTag.mem_toList_of_fieldTag? (m := mp.1) (p := mp.2) ht
      simp [CatCrypt.Crypto.Hax.exitScalarRes, CatCrypt.Crypto.Hax.exitScalarCall,
        String.contains_char_eq, hm] at h0

/-- A name of `linkNameOk` is no field head: a field head contains `#`, so it is the name of
    a scalar call (`exitScalarRes`). -/
theorem fieldHeadB_of_linkNameOk {f : String} (h : linkNameOk f = true) :
    _root_.Hax.FieldTag.fieldHeadB f = false := by
  cases hb : _root_.Hax.FieldTag.fieldHeadB f with
  | false => rfl
  | true =>
      exfalso
      simp only [linkNameOk, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨h0, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
      have hm := _root_.Hax.FieldTag.mem_hash_of_fieldHeadB hb
      simp [CatCrypt.Crypto.Hax.exitScalarRes, CatCrypt.Crypto.Hax.exitScalarCall,
        String.contains_char_eq, hm] at h0

/-- A name of `linkNameOk` is the name of no translated call. -/
theorem not_catName_of_linkNameOk {f : String} (h : linkNameOk f = true) : ¬ CatName f := by
  simp only [linkNameOk, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, -⟩, h5⟩, h6⟩ := h
  have h5' : f ∉ CatCrypt.Crypto.Hax.ImpToNF.hax64NFScalar () := by simpa using h5
  rintro (hc | hc | hc | hc | hc | hc)
  · exact h5' hc
  · exact h1 hc
  · exact h2 hc
  · subst hc
    simp [CatCrypt.Crypto.Hax.exitScalarRes, CatCrypt.Crypto.Hax.exitScalarCall,
      CatCrypt.Crypto.Hax.exitScalarCalls] at h0
  · exact h3 hc
  · exact h6 hc

/-- The lists of argument types that fit the parameter types `ts` (`ImpToNF.argTysFit`) at
    the types whose values encode as integers: at each position the parameter type, or, for
    a parameter of a `hax64NFWordTy` type, the `64`-bit word or the integer. -/
def sigVariants : List NfTy → List (List NfTy)
  | [] => [[]]
  | t :: ts =>
      (if CatCrypt.Crypto.Hax.ImpToNF.hax64NFWordTy t then [NfTy.word 64, NfTy.int]
        else [t]).flatMap fun a => (sigVariants ts).map (a :: ·)

/-- **The declared external procedures of a module, at a builtin table `bi`**: for each
    linked function whose name passes `linkNameOk` and whose result type passes `linkResOk`
    (a `64`-bit word or an array of `64`-bit words), one declaration at each list of argument
    types `sigVariants` gives its parameter types that all pass `wordArrTy` (types whose
    values encode as integers, and arrays of `64`-bit words), with the result type of the
    function. An array parameter and an array result are passed as memrefs by `nfToCatExt`.
    The function of each declaration is the call of the leaf table of `bi` at the name and
    the signature. The names and the signatures do not depend on `bi`
    (`declared_linkedDecls`). A linked function with another result type, and a list of
    argument types with a type that fails `wordArrTy`, are not signatures of words and word
    arrays, which are the signatures the translation `nfToCatExt` keeps as calls. -/
def linkedDecls (m : HaxModule) (bi : Builtins) : List ExtDecl :=
  (m.linked.filter fun l => linkNameOk l.name && linkResOk l.res).flatMap
    fun l =>
      ((sigVariants (l.params.map (·.2))).filter (·.all wordArrTy)).map fun as =>
        ⟨l.name, as, l.res, (tableOf bi).call l.name as l.res⟩

/-- A module without linked functions declares no external procedure. -/
theorem linkedDecls_of_linked_nil {m : HaxModule} (h : m.linked = []) (bi : Builtins) :
    linkedDecls m bi = [] := by
  rw [linkedDecls, h]
  rfl

/-- The module of a single function declares no external procedure. -/
theorem linkedDecls_single (te : TExpr) (bi : Builtins) :
    linkedDecls (te : HaxModule) bi = [] := rfl

/-- The declared procedures of a module at two tables declare the same names at the same
    signatures. -/
theorem declared_linkedDecls (m : HaxModule) (bi bi' : Builtins) (f : String)
    (as : List NfTy) (r : NfTy) :
    declared (linkedDecls m bi) f as r = declared (linkedDecls m bi') f as r := by
  simp only [declared, linkedDecls, List.any_flatMap, List.any_map]
  rfl

/-- **A table and the call environment read off it agree on the declared procedures of a
    module at the table.** The function of each declaration is the call of the table, and
    the environment `catEnvOf (tableEnv bi)` implements it (`implementedBy_tableEnv`). -/
theorem extAgree_linkedDecls (m : HaxModule) (bi : Builtins) :
    ExtAgree bi (catEnvOf (tableEnv bi)) (linkedDecls m bi) := by
  intro d hd
  obtain ⟨l, hl, hd⟩ := List.mem_flatMap.mp hd
  obtain ⟨as, has, rfl⟩ := List.mem_map.mp hd
  have hr : linkResOk l.res = true := by
    have := (List.mem_filter.mp hl).2
    simp only [Bool.and_eq_true] at this
    exact this.2
  exact ⟨fun _ => rfl, implementedBy_tableEnv bi l.name as l.res hr
    (List.all_eq_true.mp (List.mem_filter.mp has).2)⟩

/-- **A signature of words and word arrays**: the type of every parameter of the linked
    function `l` and its result type pass `linkResOk` (the `64`-bit word or an array of
    `64`-bit words). -/
def linkSigOk (l : CatCrypt.Crypto.Hax.LinkedFn) : Bool :=
  (l.params.all fun p => linkResOk p.2) && linkResOk l.res

/-- A type contains an integer slice `.slice .int`. -/
def intSliceTy : NfTy → Bool
  | .slice .int => true
  | .slice t => intSliceTy t
  | .arr _ t => intSliceTy t
  | .pair a b => intSliceTy a || intSliceTy b
  | .tcons h t => intSliceTy h || intSliceTy t
  | _ => false

/-- The type of a parameter or the result type of the function `f` of a module contains an
    integer slice (`intSliceTy`). -/
def modFnIntSlice (f : CatCrypt.Crypto.Hax.ModFn) : Bool :=
  (f.params.any fun p => intSliceTy p.2) || intSliceTy f.res

/-- **An entry result type of the front**: the result types the chain reads back
    (`outTyB`), a word, an integer or an array of words. -/
def entryResOk (t : NfTy) : Bool := outTyB t

/-- An entry result type of the front is a result type the chain accepts (`outTyB`). -/
theorem entryResOk_iff_outTyB {t : NfTy} : entryResOk t = true ↔ outTyB t = true := Iff.rfl

/-- A result type the chain accepts (`outTyB`) is an entry result type of the front. -/
theorem entryResOk_of_outTyB {t : NfTy} (h : outTyB t = true) : entryResOk t = true := h

/-- **The translation of the hax front** on a module: when no function of the module has the
    name of an array operation (`crateArrOk` on the callees prepared by `nfBody`), the
    extraction of each function passes the side conditions `haxFrontShapeOk` of the front,
    the name of each linked function passes `linkNameOk` and its signature `linkSigOk`, and
    no callee has a parameter or result type containing an integer slice
    (`modFnIntSlice`), the source program `nfSrcProgC`
    of the entry with the constants of the layout bound (`bindConsts`), at the call typing of
    the prepared callees followed by the linked functions, at a result type passing
    `entryResOk` (a word, an integer or an array of words), followed by the inlining
    `HaxModule.inline?` of the calls of the prepared callees. A call of a linked function is
    typed from the parameter and result types of the function and stays a leaf call of the
    result. On a module without linked functions the call typing is that of the prepared
    callees (`haxToNF_of_linked_nil`). -/
def haxToNF (σ : AbiLayout) (m : HaxModule) :
    Option (Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]) :=
  if crateArrOk (m.prepared nfBody) = true ∧
      (m.fns.all fun f => CatCrypt.Crypto.Hax.haxFrontShapeOk f.texpr) = true ∧
      (m.linked.all fun l => linkNameOk l.name) = true ∧
      (m.linked.all linkSigOk) = true ∧
      (m.fns.all fun f => !modFnIntSlice f) = true then
    (nfSrcProgC (m.prepared nfBody ++ m.linkedFns) σ
        (bindConsts σ.consts m.entry)).bind fun q =>
      if entryResOk q.1 then (m.inline? nfBody q.2).map fun p => ⟨q.1, p⟩ else none
  else none

/-- **On a module without linked functions the translation reads the prepared callees
    only**: under `crateArrOk` on them, `haxFrontShapeOk` on the extraction of each
    function and no integer-slice type of a callee (`modFnIntSlice`), the source program
    `nfSrcProgC` at the call typing of the prepared callees, at a result type passing
    `entryResOk`, followed by the inlining of their calls. -/
theorem haxToNF_of_linked_nil (σ : AbiLayout) {m : HaxModule} (h : m.linked = []) :
    haxToNF σ m =
      if crateArrOk (m.prepared nfBody) = true ∧
          (m.fns.all fun f => CatCrypt.Crypto.Hax.haxFrontShapeOk f.texpr) = true ∧
          (m.fns.all fun f => !modFnIntSlice f) = true then
        (nfSrcProgC (m.prepared nfBody) σ (bindConsts σ.consts m.entry)).bind fun q =>
          if entryResOk q.1 then (m.inline? nfBody q.2).map fun p => ⟨q.1, p⟩ else none
      else none := by
  unfold haxToNF
  rw [HaxModule.linkedFns_of_linked_nil h, h]
  simp only [List.all_nil, List.append_nil, true_and]

/-- A result of `haxToNF` is the inlining of a result of `nfSrcProgC` at the prepared callees
    of the module followed by its linked functions; no prepared callee has the name of an
    array operation, the extraction of each function of the module passes
    `haxFrontShapeOk`, and the name of each linked function passes `linkNameOk`. -/
theorem haxToNF_eq_some {σ : AbiLayout} {m : HaxModule}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (h : haxToNF σ m = some q) :
    crateArrOk (m.prepared nfBody) = true ∧
      (∀ f ∈ m.fns, CatCrypt.Crypto.Hax.haxFrontShapeOk f.texpr = true) ∧
      (∀ l ∈ m.linked, linkNameOk l.name = true) ∧
      ∃ p : NFProg nfDialect (entryCtx (abiEntry σ)) [q.1],
        nfSrcProgC (m.prepared nfBody ++ m.linkedFns) σ
            (bindConsts σ.consts m.entry) = some ⟨q.1, p⟩ ∧
          m.inline? nfBody p = some q.2 := by
  unfold haxToNF at h
  split at h
  · rename_i hfs
    obtain ⟨q', hq', h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨hfs.1, List.all_eq_true.mp hfs.2.1, List.all_eq_true.mp hfs.2.2.1, q'.2, hq', hp⟩
    · cases h
  · cases h

/-- The result type of a program `haxToNF` returns passes `entryResOk`: it is a word,
    an integer or an array of words. -/
theorem haxToNF_eq_some_res {σ : AbiLayout} {m : HaxModule}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (h : haxToNF σ m = some q) : entryResOk q.1 = true := by
  unfold haxToNF at h
  split at h
  · obtain ⟨q', -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.mp h
      assumption
    · cases h
  · cases h

/-- At a module `haxToNF` translates, the signature of each linked function passes
    `linkSigOk` (words and word arrays) and no callee has a parameter or result type
    containing an integer slice (`modFnIntSlice`). -/
theorem haxToNF_eq_some_sig {σ : AbiLayout} {m : HaxModule}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (h : haxToNF σ m = some q) :
    (∀ l ∈ m.linked, linkSigOk l = true) ∧ (∀ f ∈ m.fns, modFnIntSlice f = false) := by
  unfold haxToNF at h
  split at h
  · rename_i hfs
    exact ⟨List.all_eq_true.mp hfs.2.2.2.1,
      fun f hf => by simpa using List.all_eq_true.mp hfs.2.2.2.2 f hf⟩
  · cases h

/-- **The translation of a single function** is the source program `nfSrcProg` of the
    extraction with the constants of the layout bound, at a result type passing
    `entryResOk`. -/
theorem haxToNF_single (σ : AbiLayout) (te : TExpr) :
    haxToNF σ (te : HaxModule) =
      (nfSrcProg σ (bindConsts σ.consts te)).filter fun q => entryResOk q.1 := by
  have hC : nfSrcProgC [] σ (bindConsts σ.consts te) = nfSrcProg σ (bindConsts σ.consts te) :=
    rfl
  have hA : crateArrOk ((HaxModule.single te).prepared nfBody) = true ∧
      ((HaxModule.single te).fns.all fun f =>
        CatCrypt.Crypto.Hax.haxFrontShapeOk f.texpr) = true ∧
      ((HaxModule.single te).linked.all fun l => linkNameOk l.name) = true ∧
      ((HaxModule.single te).linked.all linkSigOk) = true ∧
      ((HaxModule.single te).fns.all fun f => !modFnIntSlice f) = true := by
    refine ⟨?_, rfl, rfl, rfl, rfl⟩
    change crateArrOk [] = true
    decide
  unfold haxToNF
  rw [ite_eq_left hA]
  change (nfSrcProgC [] σ (bindConsts σ.consts te)).bind _ = _
  rw [hC]
  rcases nfSrcProg σ (bindConsts σ.consts te) with _ | q
  · rfl
  · rw [Option.bind_some, Option.filter_some]
    split
    · rw [HaxModule.inline?_single]
      rfl
    · rfl

/-! ### The boundary of the translation -/

open CatCrypt.Crypto.Hax.FrontDomain (ModuleRefusal frontOut toOption_frontOut)
open CatCrypt.Crypto.Hax.ImpToNF (crateSigOf)

/-- The conjunct of `haxFrontShapeOk` that fails on an extraction it refuses:
    `aNormTDenoteOk` of the prepared extraction, else the shape test `prepShapeB` of the form
    chosen. -/
def shapeCond (te : TExpr) : String :=
  if CatCrypt.Crypto.Hax.aNormTDenoteOk (CatCrypt.Crypto.Hax.haxFrontPrep te.erase) = false then
    "aNormTDenoteOk"
  else "prepShapeB"

/-- **The refusal of the translation `haxToNF`** of the module `m` under the layout `σ`, in
    the order of the translation: a callee with the name of an array operation
    (`crateArrOk`), a callee whose extraction fails `haxFrontShapeOk`, a linked function
    whose name fails `linkNameOk`, a linked function whose signature fails `linkSigOk`, a
    callee with an integer-slice type (`modFnIntSlice`), the entry failing
    `haxFrontShapeOk`, the first construct of the entry that `impToNF` does not accept at the
    call typing of the module (`FrontDomain.frontOut`), the result type of the entry failing
    `entryResOk` (a type other than a word, an integer and an array of words), and the
    inlining `HaxModule.inline?` refusing;
    `none` when there is none. -/
def _root_.CatCrypt.Crypto.Hax.HaxModule.refusal? (σ : AbiLayout) (m : HaxModule) :
    Option ModuleRefusal :=
  if crateArrOk (m.prepared nfBody) = true then
    if (m.fns.all fun f => CatCrypt.Crypto.Hax.haxFrontShapeOk f.texpr) = true then
      if (m.linked.all fun l => linkNameOk l.name) = true then
        if (m.linked.all linkSigOk) = true then
          if (m.fns.all fun f => !modFnIntSlice f) = true then
            if CatCrypt.Crypto.Hax.haxFrontShapeOk (bindConsts σ.consts m.entry) = true then
              match frontOut (crateSigOf (m.prepared nfBody ++ m.linkedFns) hax64SigOf) none
                  (entryEnv (abiEntry σ)) (nfBody (bindConsts σ.consts m.entry)) with
              | .error r => some (.entry r)
              | .ok o =>
                  if entryResOk o.t then
                    if (m.inline? nfBody o.prog).isSome then none else some (.inline m.depth)
                  else some (.entryResult (CatCrypt.Crypto.Hax.FrontDomain.tyName o.t))
            else some (.entryShape (shapeCond (bindConsts σ.consts m.entry)))
          else some (.intSlice (((m.fns.find? modFnIntSlice).map (·.name)).getD ""))
        else
          some (.linkedSig (((m.linked.find? fun l => !linkSigOk l).map (·.name)).getD ""))
      else
        some (.linkedName
          (((m.linked.find? fun l => !linkNameOk l.name).map (·.name)).getD ""))
    else
      some (((m.fns.find? fun f => !CatCrypt.Crypto.Hax.haxFrontShapeOk f.texpr).map fun f =>
        ModuleRefusal.calleeShape f.name (shapeCond f.texpr)).getD (.calleeShape "" ""))
  else
    some (.arrayOpName
      ((["len", "index", "array_update"].find? fun g =>
        ((m.prepared nfBody).find? (·.name == g)).isSome).getD ""))

/-- **The translation refuses nothing exactly when it returns a program**: `m.refusal? σ` is
    `none` exactly when `haxToNF σ m` returns a program. -/
theorem _root_.CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_iff (σ : AbiLayout)
    (m : HaxModule) : m.refusal? σ = none ↔ (haxToNF σ m).isSome = true := by
  unfold HaxModule.refusal? haxToNF nfSrcProgC
  by_cases hABC : crateArrOk (m.prepared nfBody) = true ∧
      (m.fns.all fun f => CatCrypt.Crypto.Hax.haxFrontShapeOk f.texpr) = true ∧
      (m.linked.all fun l => linkNameOk l.name) = true ∧
      (m.linked.all linkSigOk) = true ∧
      (m.fns.all fun f => !modFnIntSlice f) = true
  · by_cases hS : CatCrypt.Crypto.Hax.haxFrontShapeOk (bindConsts σ.consts m.entry) = true
    · simp only [ite_eq_left hABC.1, ite_eq_left hABC.2.1, ite_eq_left hABC.2.2.1, ite_eq_left hABC.2.2.2.1,
        ite_eq_left hABC.2.2.2.2, ite_eq_left hABC, ite_eq_left hS]
      rw [← toOption_frontOut]
      cases frontOut (crateSigOf (m.prepared nfBody ++ m.linkedFns) hax64SigOf) none
          (entryEnv (abiEntry σ)) (nfBody (bindConsts σ.consts m.entry)) with
      | error r => simp [Except.toOption]
      | ok o =>
          simp only [Except.toOption, Option.map_some, Option.bind_some]
          by_cases hr : entryResOk o.t = true
          · simp only [ite_eq_left hr]
            cases m.inline? nfBody o.prog <;> simp
          · simp [hr]
    · simp only [ite_eq_left hABC.1, ite_eq_left hABC.2.1, ite_eq_left hABC.2.2.1, ite_eq_left hABC.2.2.2.1,
        ite_eq_left hABC.2.2.2.2, ite_eq_left hABC, ite_eq_right hS]
      simp
  · rw [ite_eq_right hABC]
    by_cases hA : crateArrOk (m.prepared nfBody) = true
    · by_cases hB : (m.fns.all fun f => CatCrypt.Crypto.Hax.haxFrontShapeOk f.texpr) = true
      · by_cases hC : (m.linked.all fun l => linkNameOk l.name) = true
        · by_cases hD : (m.linked.all linkSigOk) = true
          · have hE : ¬ (m.fns.all fun f => !modFnIntSlice f) = true :=
              fun h => hABC ⟨hA, hB, hC, hD, h⟩
            simp only [ite_eq_left hA, ite_eq_left hB, ite_eq_left hC, ite_eq_left hD, ite_eq_right hE]
            simp
          · simp only [ite_eq_left hA, ite_eq_left hB, ite_eq_left hC, ite_eq_right hD]
            simp
        · simp only [ite_eq_left hA, ite_eq_left hB, ite_eq_right hC]
          simp
      · simp only [ite_eq_left hA, ite_eq_right hB]
        simp
    · simp only [ite_eq_right hA]
      simp

/-- **The hax front as an entry**: the modules `HaxModule` with the source semantics
    `haxRuns`, the translation `haxToNF` and the export names `nfAbiNames`. At a module `m`
    and every fuel of the callees, the table is the table `m.linkTable hax64WExit` of the
    linked functions, in which a call of a linked function is the value of its meaning `sem`,
    and the call environment is the one read off that table (`tableEnv`).
    The declared procedures are `linkedDecls m hax64WExit`; the soundness gives the
    declarations `linkedDecls` at the table of the linked functions, which declare the same
    names and signatures (`declared_linkedDecls`) and on which the table and the environment
    agree (`extAgree_linkedDecls`).

    Its soundness is `nfSrcProgT_sound` after `run_bindConsts_of_envOf`, at the table of the
    module, which has the array operations (`arrayOps_refBi` over
    `arrayOps_linkBi_of_table_none`) and is typed by the call typing of the module
    (`HaxModule.table_typedCalls`), followed by `HaxModule.denote_inline?`; the preparation
    `nfBody` keeps the runs of each function at each depth of the reference table by
    `nfBody_prepSim`. The table of the linked functions agrees with the `u64` table and is
    typed by `hax64SigOf` because the name of a linked function passes `linkNameOk`
    (`subTable_linkBi`, `typedCalls_linkBi_of_not_catName`, `not_catName_of_linkNameOk`).

    For a module without linked functions the table is `hax64WExit`
    (`HaxModule.linkTable_of_linked_nil`) and there is no declared procedure
    (`linkedDecls_of_linked_nil`). At a module the translation accepts no linked function
    has a tagged head as name, so the table of the linked functions answers the tagged
    heads by their arms (`fieldCalls_linkBi`, `fieldCalls_hax64WExit`) and is the `u64` table
    at the wide tagged heads (`fieldCallsWideEq_linkBi`, `fieldCallsWideEq_hax64WExit`). -/
def haxEntry : NFEntry where
  Src := HaxModule
  Runs := haxRuns
  names := nfAbiNames
  toNF := haxToNF
  bi m _ := m.linkTable CatCrypt.Crypto.Hax.hax64WExit
  env m _ := tableEnv (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)
  decls m := linkedDecls m CatCrypt.Crypto.Hax.hax64WExit
  sound σ m q hq sa v _ hrun := by
    obtain ⟨env, fuel, fuelC, env', henv, hrun, hcf⟩ := hrun
    obtain ⟨hfs, hsh, hlk, p, hp, hinl⟩ := haxToNF_eq_some hq
    have hft : ∀ l ∈ m.linked, _root_.Hax.FieldTag.fieldTag? l.name = none :=
      fun l hl => fieldTag?_of_linkNameOk (hlk l hl)
    have hnc : ∀ l ∈ m.linked, ¬ CatName l.name :=
      fun l hl => not_catName_of_linkNameOk (hlk l hl)
    have hAL : _root_.Hax.InlineMap.ArrayOps (m.linkTable CatCrypt.Crypto.Hax.hax64WExit) :=
      arrayOps_linkBi_of_table_none _ CatCrypt.Crypto.Hax.arrayOps_hax64WExit
        (fun l hl vals => hax64WExit_of_linkNameOk (hlk l hl) vals)
    have hA : ∀ n, _root_.Hax.InlineMap.ArrayOps
        (CatCrypt.Crypto.Hax.refBi m.fns (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)
          fuelC n) := fun n => arrayOps_refBi hfs hAL fuelC n
    have hsim : ∀ n, ∀ f ∈ m.fns, f.PrepSim nfBody
        (CatCrypt.Crypto.Hax.refBi m.fns (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)
          fuelC n) :=
      fun n f hf fuel' e e' w hw hcw => nfBody_prepSim (hsh f hf) (hA n) fuel' e e' w hw hcw
    have hrunK : (denoteSpine (m.table CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel
        (bindConsts σ.consts m.entry).erase).run env = (.val v, env') := by
      rw [run_bindConsts_of_envOf _ fuel m.entry henv]
      exact hrun
    have hRL := linkTable_repeatCalls hlk
    have hfR : m.fns.find? (·.name == "repeat") = none := by
      have h := crateArrOk_find_repeat hfs
      rw [HaxModule.prepared, CatCrypt.Crypto.Hax.find?_prep, Option.map_eq_none_iff] at h
      exact h
    obtain ⟨V, y, hV, ⟨N, hden⟩, hv⟩ := nfSrcProgT_sound
      (T := m.table CatCrypt.Crypto.Hax.hax64WExit fuelC) (hA m.depth)
      (m.table_typedCalls nfBody CatCrypt.Crypto.Hax.hax64WExit_typedCalls fuelC)
      (CatCrypt.Crypto.Hax.refBi_repeatCalls m.fns hRL hfR fuelC m.depth) hp henv
      hrunK hcf
    exact ⟨N, linkedDecls m (m.linkTable CatCrypt.Crypto.Hax.hax64WExit), env, V, y,
      declared_linkedDecls m _ _,
      subTable_linkBi _ CatCrypt.Crypto.Hax.hax64WExit_subTable hnc,
      extAgree_linkedDecls m _, henv, hV,
      ⟨N, le_rfl, m.denote_inline? nfBody
        (typedCalls_linkBi_of_not_catName _ CatCrypt.Crypto.Hax.hax64WExit_typedCalls hnc hft)
        hRL hfR N hsim hinl (hden N le_rfl)⟩, hv⟩
  fieldCalls σ m q hq _ := by
    obtain ⟨-, -, hlk, -⟩ := haxToNF_eq_some hq
    exact fieldCalls_linkBi _ fieldCalls_hax64WExit
      (fun l hl => fieldHeadB_of_linkNameOk (hlk l hl))
  fieldCallsWide σ m q hq _ := by
    obtain ⟨-, -, hlk, -⟩ := haxToNF_eq_some hq
    exact fieldCallsWideEq_linkBi _ fieldCallsWideEq_hax64WExit
      (fun l hl => fieldTag?_of_linkNameOk (hlk l hl))

/-- **The table of the hax entry is the `u64` table at the wide tagged heads**: the field
    `NFEntry.fieldCallsWide` of `haxEntry`. -/
theorem haxEntry_fieldCallsWideEq (σ : AbiLayout) (m : HaxModule)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    (hq : haxEntry.toNF σ m = some q) (k : Nat) :
    FieldLevel.FieldCallsWideEq (haxEntry.bi m k) :=
  haxEntry.fieldCallsWide σ m q hq k

/-! ## The functions of a module from their extractions -/

/-- The parameters of an extraction: its leading bindings `let x = x`, at most `n` of them,
    in the order of the bindings, each with its type. -/
def texprPrelude : Nat → TExpr → List (String × _root_.Hax.ImpType)
  | 0, _ => []
  | n + 1, .mk (.letBind x (.mk (.var y) τ) b) _ =>
      if x == y then (x, τ) :: texprPrelude n b else []
  | _ + 1, _ => []

/-- An element type of a word array of a function of a module: an unsigned integer of at most
    `64` bits, read as one `64`-bit word per element, as the widened entry layout reads an
    array parameter of the entry. The source semantics keeps no element width (a width is a
    tag of an operation), so the reading needs no bound on the elements below `2^64`. -/
def modFnElem : _root_.Hax.ImpType → Bool
  | .uint w => decide (w.bits ≤ 64)
  | _ => false

mutual

/-- The type of a parameter or of the result of a function of a module: the bit type for a
    Boolean, the unit type for the unit value, the unbounded integer for an unbounded
    integer, a `64`-bit word for an unsigned integer of at most `64` bits, the tuple type
    (`tupTy`) of the component types for a tuple, and an array of `n` `64`-bit words for an
    array of `n` unsigned integers of at most `64` bits (`modFnElem`), behind a reference or
    not. -/
def modFnTy : _root_.Hax.ImpType → Option NfTy
  | .bool => some .bit
  | .unit => some .unit
  | .int => some .int
  | .uint w => if w.bits ≤ 64 then some (.word 64) else none
  | .tuple ts => (modFnTys ts).map CatCrypt.Crypto.Hax.ImpToNF.tupTy
  | .array t n => if modFnElem t then some (.arr n (.word 64)) else none
  | .ref (.array t n) _ => if modFnElem t then some (.arr n (.word 64)) else none
  | _ => none

/-- The types `modFnTy` reads off a list of types, in order; `none` when it reads none off
    one of them. -/
def modFnTys : List _root_.Hax.ImpType → Option (List NfTy)
  | [] => some []
  | t :: ts => (modFnTy t).bind fun a => (modFnTys ts).map (a :: ·)

end

/-- **The function of a module named `name` with the extraction `te`**, in a crate with the
    literal constants `consts`. Its parameters are the leading bindings `let x = x` of `te`
    (`texprPrelude`), in their order, each at the type `modFnTy` reads off the type of the
    binding; its result type is `modFnTy` of the type of `te`; its extraction is `te` with
    the constants of `consts` that `te` reads free and that are not parameters bound at its
    head (`bindConsts`). The result is `none` when a parameter or the result has a type
    `modFnTy` does not read, or when the extraction with the constants bound reads a free
    name that is not a parameter. -/
def _root_.CatCrypt.Crypto.Hax.ModFn.ofTExpr (name : String) (te : TExpr)
    (consts : List (String × Value) := []) : Option CatCrypt.Crypto.Hax.ModFn :=
  let ps := texprPrelude 64 te
  let free := (_root_.Hax.freeVars te.erase).eraseDups
  let te' := bindConsts (consts.filter fun c => free.contains c.1 && !ps.any (·.1 == c.1)) te
  (ps.mapM fun p => (modFnTy p.2).map fun t => (p.1, t)).bind fun params =>
    (modFnTy te.ty).bind fun r =>
      if (_root_.Hax.freeVars te'.erase).all fun x => ps.any (·.1 == x) then
        some ⟨name, params, r, te'⟩
      else none

/-- The parameters `ps` at the types `modFnTy` reads, in order, or the name of the first
    parameter whose type `modFnTy` does not read. -/
def modFnParamsE : List (String × _root_.Hax.ImpType) → Except String (List (String × NfTy))
  | [] => .ok []
  | p :: ps =>
      match modFnTy p.2 with
      | some t => (modFnParamsE ps).map ((p.1, t) :: ·)
      | none => .error p.1

/-- Forgetting the name of `modFnParamsE` gives the parameters `ModFn.ofTExpr` reads. -/
theorem toOption_modFnParamsE (ps : List (String × _root_.Hax.ImpType)) :
    (modFnParamsE ps).toOption = ps.mapM fun p => (modFnTy p.2).map fun t => (p.1, t) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rw [List.mapM_cons]
      unfold modFnParamsE
      cases modFnTy p.2 with
      | none => rfl
      | some t =>
          rcases h : modFnParamsE ps with x | qs <;> rw [h] at ih <;>
            simp [Except.toOption, Except.map, ← ih]

/-- **The function of a module named `name` with the extraction `te`, with its refusal**:
    `ModFn.ofTExpr` when it makes the function, and otherwise the refusal
    `ModuleRefusal.calleeShape name c` with the condition `c` the extraction fails: a parameter
    whose type `modFnTy` does not read, the result whose type `modFnTy` does not read, or a
    free name of the extraction with the constants bound that is not a parameter
    (`toOption_ofTExprE`). -/
def _root_.CatCrypt.Crypto.Hax.ModFn.ofTExprE (name : String) (te : TExpr)
    (consts : List (String × Value) := []) : Except ModuleRefusal CatCrypt.Crypto.Hax.ModFn :=
  let ps := texprPrelude 64 te
  let free := (_root_.Hax.freeVars te.erase).eraseDups
  let te' := bindConsts (consts.filter fun c => free.contains c.1 && !ps.any (·.1 == c.1)) te
  match modFnParamsE ps with
  | .error x => .error (.calleeShape name s!"parameter {x} has a type outside the domain")
  | .ok params =>
      match modFnTy te.ty with
      | none => .error (.calleeShape name "the result has a type outside the domain")
      | some r =>
          if (_root_.Hax.freeVars te'.erase).all fun x => ps.any (·.1 == x) then
            .ok ⟨name, params, r, te'⟩
          else
            .error (.calleeShape name s!"free name {(((_root_.Hax.freeVars te'.erase).find?
              fun x => !ps.any (·.1 == x)).getD "")}")

/-- **Forgetting the refusal of `ModFn.ofTExprE` gives `ModFn.ofTExpr`.** -/
theorem _root_.CatCrypt.Crypto.Hax.ModFn.toOption_ofTExprE (name : String) (te : TExpr)
    (consts : List (String × Value)) :
    (CatCrypt.Crypto.Hax.ModFn.ofTExprE name te consts).toOption =
      CatCrypt.Crypto.Hax.ModFn.ofTExpr name te consts := by
  unfold CatCrypt.Crypto.Hax.ModFn.ofTExprE CatCrypt.Crypto.Hax.ModFn.ofTExpr
  dsimp only
  rw [← toOption_modFnParamsE]
  rcases modFnParamsE (texprPrelude 64 te) with x | params
  · rfl
  · simp only [Except.toOption, Option.bind_some]
    cases modFnTy te.ty with
    | none => rfl
    | some r =>
        simp only [Option.bind_some]
        split_ifs <;> rfl

/-- **The functions of a module from the extractions `gs`, with their refusal**: each
    function as `ModFn.ofTExprE` makes it with the constants `consts`, in order, or the
    refusal of the first function of `gs` it does not make. No function is left out:
    `modFnsE_eq_ok_iff` and `modFnsE_toOption_eq_none_iff`. -/
def modFnsE (consts : List (String × Value)) :
    List (String × TExpr) → Except ModuleRefusal (List CatCrypt.Crypto.Hax.ModFn)
  | [] => .ok []
  | g :: gs =>
      match CatCrypt.Crypto.Hax.ModFn.ofTExprE g.1 g.2 consts with
      | .error r => .error r
      | .ok f => (modFnsE consts gs).map (f :: ·)

/-- **`modFnsE` returns the functions exactly when `ModFn.ofTExpr` makes each of them**: the
    result is `fs` exactly when `ModFn.ofTExpr` makes, function by function, the list `fs`. -/
theorem modFnsE_eq_ok_iff (consts : List (String × Value)) (gs : List (String × TExpr))
    (fs : List CatCrypt.Crypto.Hax.ModFn) :
    modFnsE consts gs = .ok fs ↔
      (gs.mapM fun g => CatCrypt.Crypto.Hax.ModFn.ofTExpr g.1 g.2 consts) = some fs := by
  induction gs generalizing fs with
  | nil =>
      simp only [modFnsE, List.mapM_nil]
      constructor <;> intro h <;> cases h <;> rfl
  | cons g gs ih =>
      rw [List.mapM_cons, ← CatCrypt.Crypto.Hax.ModFn.toOption_ofTExprE]
      unfold modFnsE
      rcases CatCrypt.Crypto.Hax.ModFn.ofTExprE g.1 g.2 consts with r | f
      · simp [Except.toOption]
      · simp only [Except.toOption]
        rcases h : modFnsE consts gs with r | fs'
        · have hn : (gs.mapM fun g => CatCrypt.Crypto.Hax.ModFn.ofTExpr g.1 g.2 consts) = none := by
            cases hm : (gs.mapM fun g => CatCrypt.Crypto.Hax.ModFn.ofTExpr g.1 g.2 consts) with
            | none => rfl
            | some fs'' => rw [← ih fs'', h] at hm; cases hm
          simp [Except.map, hn]
        · have hs := (ih fs').mp h
          simp [Except.map, hs, eq_comm]

/-- **`modFnsE` refuses exactly when `ModFn.ofTExpr` does not make a function of `gs`.** -/
theorem modFnsE_toOption_eq_none_iff (consts : List (String × Value))
    (gs : List (String × TExpr)) :
    (modFnsE consts gs).toOption = none ↔
      ∃ g ∈ gs, CatCrypt.Crypto.Hax.ModFn.ofTExpr g.1 g.2 consts = none := by
  have hiff : (modFnsE consts gs).toOption =
      gs.mapM fun g => CatCrypt.Crypto.Hax.ModFn.ofTExpr g.1 g.2 consts := by
    cases h : (gs.mapM fun g => CatCrypt.Crypto.Hax.ModFn.ofTExpr g.1 g.2 consts) with
    | some fs => rw [(modFnsE_eq_ok_iff consts gs fs).mpr h]; rfl
    | none =>
        rcases h' : modFnsE consts gs with r | fs
        · rfl
        · rw [(modFnsE_eq_ok_iff consts gs fs).mp h'] at h; cases h
  rw [hiff]
  clear hiff
  induction gs with
  | nil => simp [List.mapM_nil]
  | cons g gs ih =>
      rw [List.mapM_cons]
      cases hg : CatCrypt.Crypto.Hax.ModFn.ofTExpr g.1 g.2 consts with
      | none => simp [hg]
      | some f =>
          cases hm : (gs.mapM fun g => CatCrypt.Crypto.Hax.ModFn.ofTExpr g.1 g.2 consts) with
          | none =>
              rw [hm] at ih
              obtain ⟨g', hg', hn⟩ := ih.mp rfl
              exact iff_of_true rfl ⟨g', List.mem_cons_of_mem _ hg', hn⟩
          | some fs =>
              rw [hm] at ih
              have hnone : ¬ ∃ g ∈ gs, CatCrypt.Crypto.Hax.ModFn.ofTExpr g.1 g.2 consts = none :=
                fun h => absurd (ih.mpr h) (by simp)
              constructor
              · intro h; simp at h
              · rintro ⟨g', hg', hn⟩
                rcases List.mem_cons.mp hg' with rfl | hg'
                · rw [hg] at hn; cases hn
                · exact absurd ⟨g', hg', hn⟩ hnone

/-- **The hax front through the chain**, as a `FrontLegOfJ`. -/
def nfFrontC : FrontLegOfJ := haxEntry.toFrontLegOf

/-- **The leg of the hax front through the chain**: for a result `p` of the compile
    function, every value `v` of a run of the source reading (`haxRuns`) from an entry state
    satisfying `σ.Regions` is the source value `denVal` of a value the program denotes at
    some fuel, at a valuation `σ` reads off the entry state. -/
theorem nfFrontC_leg (σ : AbiLayout) (m : HaxModule) (p : AnyRouteProgJ)
    (hf : nfFrontC.front σ m = some p) (sa : AState) (v : Value) (hreg : σ.Regions sa)
    (hrun : haxRuns σ m sa v) :
    ∃ (V : Valuation p.1) (fuel : Nat) (x : ⟦p.2.1⟧), AbiValOf σ sa V ∧
      p.2.2.denoteF fuel V = some x ∧ v = denVal p.2.1 x :=
  nfFrontC.leg σ m p hf sa v hreg hrun

/-- **The compile function of the hax front through the chain**, at the module of a single
    function, is `nfFront` on the extraction with the constants of the layout bound. -/
theorem nfFrontC_front (σ : AbiLayout) (te : TExpr) :
    nfFrontC.front σ (te : HaxModule) =
      (nfFront σ (bindConsts σ.consts te)).map fun p => ⟨nfCtx σ, _, p.2⟩ := by
  change (haxToNF σ (te : HaxModule)).bind _ = _
  rw [haxToNF_single, nfFront, Option.map_bind]
  rcases nfSrcProg σ (bindConsts σ.consts te) with _ | q
  · rfl
  · rw [Option.filter_some, Option.bind_some]
    split
    · rw [Option.bind_some]
      simp only [Function.comp_apply, Option.map_map]
      rfl
    · rename_i hr
      have hc : (nfChain (entryCtx (abiEntry σ)) q.1).run q.2 = none := by
        simp only [nfChain, Chain.run, outTyStep]
        rw [ite_eq_right fun h => hr (entryResOk_of_outTyB h)]
        rfl
      simp [hc]

end CatCrypt.Crypto.SecureCompilation.Haxc
