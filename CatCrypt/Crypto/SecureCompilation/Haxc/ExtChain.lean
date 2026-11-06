/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChainCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotalJ
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep
public import CatCrypt.Crypto.SecureCompilation.VIR.NFAbortElim

/-!
# The extended NF chain, its certificates and its completeness

`extChain D Γ t` is the elimination of aborting branches `abortElimStep NfOp.isAbort`, then
the tuple flattening `flatSameStep`, followed by `extChainCore D Γ t`,
the chain `nfChainPre Γ t` with the translation `nfToCatExt` in place of `nfToCat`, the
montify step `montifyStep` and the field dialect step `fieldDialectStep` after the conversion
to `jasminDialect`, and the select lowering, the range stage and the e-graph pass at
`jasminRules` (the steps and their certificates are in `Haxc/NFChainCall.lean`, the field
dialect step in `Haxc/FieldDialectStep.lean`). This module
holds the chain, its value certificate `extChainCert` at an explicit call environment `E'`,
the theorems that the program it returns simulates the source program and runs as exported
code over procedure summaries, the region front `NFEntry.frontR` of an entry with the front
`NFEntry.toFrontLegOfR` it gives, and the completeness of the chain on the programs whose
flattening lies in `ChainTotal.extDomNB` or `ChainTotal.extDomNBD` (the domains are in
`Haxc/ChainTotalJ.lean`).

## Main definitions

* `extChainCore`, `extChain`, `extChainCert` — the steps after flattening, the chain and
  its certificate.
* `nfDenote_isAbort` — an aborting operation of `nfDialect` denotes no value, the hypothesis of
  the certificate `abortElimCert` of the first step.
* `NFEntry.frontR`, `NFEntry.toFrontLegOfR` — the region front of an entry (`toNF`,
  `extChain` at the declared procedures of the source program, the region export
  `exportRegion` at their signatures `declSigs`) and the front `FrontLegOfJ` it gives.

## Main results

* `extChainCore_run_of_nfToCat`, `extChain_run_of_nfToCat` — on a program that `nfToCat`
  translates after `dce`, the steps after flattening return what `nfChainPre` returns: such
  a program has no `call`, and the field dialect step keeps a program without `call`; the chain
  returns what `nfChainPre` returns on the flattened program.
* `extChain_run_of_abortFree` — on a program without aborting operation the chain is the chain
  without its first step (`NFProg.abortElim_of_abortFree`).
* `extChain_congr` — the chain reads the declared names and signatures only.
* `extChain_outTyB` — a program the chain accepts has a result type that passes `outTyB`.
* `extChain_denote`, `extChain_entry` — a run of the source program at the builtin table
  is matched, at every fuel at least the source fuel, by a run at `E'` of the program the
  chain returns, to the
  encoded value.
* `extChain_run_procs` — the code the region exporter gives for the program the chain
  returns, run on the x86 flag machine with the procedure summaries of a table that agrees
  with `E'`, halts in a state that holds the encoded value of the source run.
* `NFEntry.frontR_regions` — a result of the region front is a structured program.
* `NFEntry.frontR_run_procs` — a source run of an entry is matched by a run of the exported
  code of its structured program over procedure summaries that agree with the call
  environment of the entry.
* `ChainTotal.extChainCore_completeOn_NB`, `ChainTotal.extChain_completeOn_NB`,
  `ChainTotal.extChain_isSome_of_NB` — the steps after flattening are complete on
  `extDomNB`, and the chain on the programs whose flattening lies in `extDomNB`.
* `ChainTotal.extChainCore_completeOn_NBD`, `ChainTotal.extChain_completeOn_NBD`,
  `ChainTotal.extChain_isSome_of_NBD` — the steps after flattening are complete on
  `extDomNBD`, and the chain on the programs whose flattening lies in `extDomNBD`.
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
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes catToJasmin_varTransports catToJasmin_block
  catToJasmin_mapValExtends catToJasmin_regionTransports)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower (ctBackTy ctTransTy_ctBackTy)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (aegraphOptNF aegraphOptNF_denote)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric (RuleSet)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (enc PDenP entryCtx EntryVals tableOf dec encAll)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (SingleWordField canonEnc w64
  eq_canonEnc_of_toNat)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteNarrow (narrowField narrowFoldsOf
  narrowCert_of_narrowFoldsOf narrowCert_bounds)
open _root_.Hax.FieldTag (FieldMethod fieldTag? fieldArm fieldVal fieldArgs fieldVal_lt)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa ProcTable)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montifyStep montifyStepCert
  montifyStep_of_callFree)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep (fieldDialectStep fieldDialectCert
  fieldDialectStep_of_callFree)
open Ctxt (Var Valuation)
open _root_.Hax (Env Builtins)

/-! ## The chain and its certificate -/

/-- **The steps of the linear route with the declared procedures `D` after tuple
    flattening, up to the structured program of `jasminDialect`**: the check `outTyB t`,
    `dce`, `nfToCatExt (fieldDeclsFor D p)` from
    `TRd.id`, the e-graph pass at `catRules`, `map?` along `catToJasmin`, the montify pass
    `montifyStep` (Montgomery representatives at each modulus of the tagged calls that passes
    `mont32Cert`), the field dialect step `fieldDialectStep` (the tagged calls raised to the
    field dialect and lowered through `modArith` to limb templates), the select lowering,
    the range stage `synRange` (`loopRange` at the synthesised intervals of the loop-carried
    variables, each checked by the stage), and the e-graph pass at `jasminRules`. -/
def extChainCore (D : List ExtDecl) (Γ : Ctxt nfDialect) (t : NfTy) :
    Chain (NFProg nfDialect Γ [t])
      (NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) :=
  .cons (outTyStep Γ t) <| .cons (dceStep Γ [t]) <| .cons (extCallStep D Γ [t]) <|
    .cons (aegraphStep catRules (Γ.map catTy) [catTy t]) <|
    .cons (mapStep catToJasmin catToJasmin_regionTypes (Γ.map catTy) [catTy t]) <|
    .cons (montifyStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (fieldDialectStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (lowerSelectsStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (synRangeStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (aegraphStep jasminRules (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <| .nil _

/-- **The linear route with the declared procedures `D`, up to the structured program of
    `jasminDialect`**: the elimination of aborting branches `abortElimStep NfOp.isAbort`
    (a branch on a panic guard of the source is replaced by its continuation), tuple
    flattening `flatSameStep`, followed by the steps `extChainCore D Γ t`. -/
def extChain (D : List ExtDecl) (Γ : Ctxt nfDialect) (t : NfTy) :
    Chain (NFProg nfDialect Γ [t])
      (NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) :=
  .cons (abortElimStep NfOp.isAbort Γ [t]) (.cons (flatSameStep Γ [t]) (extChainCore D Γ t))

/-- **An aborting operation of `nfDialect` denotes no value**, at every leaf table: the
    hypothesis of `abortElimCert` at `NfOp.isAbort`. -/
theorem nfDenote_isAbort (T : NfLeafTable) {Γ : Ctxt nfDialect} {t : NfTy}
    (e : Expr nfDialect Γ t) (V : Valuation Γ) (h : e.op.isAbort = true) :
    @Expr.denoteM nfDialect Option _ _ (nfDenote T) Γ t e V = none := by
  obtain ⟨op, rfl, args⟩ := e
  change nfDenoteOp T op (Expr.lookupArgs args V) = none
  exact nfDenoteOp_of_isAbort T h _

/-- **On a program without aborting operation the chain is the chain without its first
    step**: the elimination of aborting branches is the identity on it
    (`NFProg.abortElim_of_abortFree`). -/
theorem extChain_run_of_abortFree (D : List ExtDecl) {Γ : Ctxt nfDialect} {t : NfTy}
    (p : NFProg nfDialect Γ [t]) (h : NFProg.abortFree NfOp.isAbort p = true) :
    (extChain D Γ t).run p = ((flatSameStep Γ [t]).run p).bind (extChainCore D Γ t).run := by
  show ((flatSameStep Γ [t]).run (NFProg.abortElim NfOp.isAbort p)).bind
    (extChainCore D Γ t).run = _
  rw [NFProg.abortElim_of_abortFree _ p h]

/-- **On a program that `nfToCat` translates after `dce`, the steps after flattening return
    what `nfChainPre` returns.** The translation `nfToCat` keeps no `call`
    (`nfToCat_callFree`), so the translation with declarations returns the same program
    (`nfToCatExt_of_nfToCat`), the e-graph pass and the conversion keep the absence of
    `call` (`nfGo_callFree`, `map?_callFree`), and the field dialect step keeps a program
    without `call` (`fieldDialectStep_of_callFree`). -/
theorem extChainCore_run_of_nfToCat (D : List ExtDecl) {Γ : Ctxt nfDialect} {t : NfTy}
    (p : NFProg nfDialect Γ [t]) {p' : NFProg catCryptDialect (Γ.map catTy) [catTy t]}
    (hp' : nfToCat (NFProg.dce p) TRd.id = some p') :
    (extChainCore D Γ t).run p = (nfChainPre Γ t).run p := by
  have hf' := nfToCat_callFree _ _ hp'
  have hx : (extCallStep D Γ [t]).run (NFProg.dce p) = some p' := by
    change nfToCatExt (fieldDeclsFor D (NFProg.dce p)) (NFProg.dce p) TRd.id = some p'
    exact nfToCatExt_of_nfToCat _ (NFProg.dce p) TRd.id p'
      (nfToCatExt_nil (NFProg.dce p) TRd.id p' hp') hf'
  have hy : (nfToCatStep Γ [t]).run (NFProg.dce p) = some p' := hp'
  have hg : (aegraphOptNF catRules p').callFree = true := by
    unfold aegraphOptNF
    exact (nfGo_callFree (d := catCryptDialect) catRules _ _ p').trans hf'
  simp only [extChainCore, nfChainPre, Chain.run]
  cases h0 : (outTyStep Γ t).run p with
  | none => rfl
  | some q0 =>
      have hq0 : q0 = p := by
        simp only [outTyStep] at h0
        split at h0
        · exact (Option.some.inj h0).symm
        · cases h0
      subst hq0
      simp only [Option.bind_some]
      change ((extCallStep D Γ [t]).run (NFProg.dce q0)).bind _ =
        ((nfToCatStep Γ [t]).run (NFProg.dce q0)).bind _
      rw [hx, hy, Option.bind_some, Option.bind_some]
      change ((mapStep catToJasmin catToJasmin_regionTypes (Γ.map catTy) [catTy t]).run
          (aegraphOptNF catRules p')).bind _ =
        ((mapStep catToJasmin catToJasmin_regionTypes (Γ.map catTy) [catTy t]).run
          (aegraphOptNF catRules p')).bind _
      cases hm : (mapStep catToJasmin catToJasmin_regionTypes (Γ.map catTy) [catTy t]).run
          (aegraphOptNF catRules p') with
      | none => rfl
      | some q4 =>
          have h4 : q4.callFree = true :=
            map?_callFree _ _ _ hg _ (q := q4) hm
          have h4' : (montifyStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]).run q4 =
              some q4 := montifyStep_of_callFree q4 h4
          have h5 : (fieldDialectStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]).run q4 =
              some q4 := fieldDialectStep_of_callFree q4 h4
          simp only [Option.bind_some]
          rw [h4']
          exact congrArg (fun o => o.bind fun p =>
            ((lowerSelectsStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]).run p).bind fun p =>
              ((synRangeStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]).run p).bind fun p =>
                ((aegraphStep jasminRules (mapCtx (Γ.map catTy)) [mapTy (catTy t)]).run p).bind
                  some) h5

/-- **On a program whose flattening after the elimination of aborting branches `nfToCat`
    translates after `dce`, the chain returns what `nfChainPre` returns on that program**
    (`extChainCore_run_of_nfToCat`). -/
theorem extChain_run_of_nfToCat (D : List ExtDecl) {Γ : Ctxt nfDialect} {t : NfTy}
    (p q : NFProg nfDialect Γ [t])
    (hq : (flatSameStep Γ [t]).run (NFProg.abortElim NfOp.isAbort p) = some q)
    {p' : NFProg catCryptDialect (Γ.map catTy) [catTy t]}
    (hp' : nfToCat (NFProg.dce q) TRd.id = some p') :
    (extChain D Γ t).run p = (nfChainPre Γ t).run q := by
  show ((flatSameStep Γ [t]).run (NFProg.abortElim NfOp.isAbort p)).bind
    (extChainCore D Γ t).run = _
  rw [hq, Option.bind_some]
  exact extChainCore_run_of_nfToCat D q hp'

/-- **The chain reads the declared names and signatures only**: two lists that declare the
    same names at the same signatures give the same chain. -/
theorem extChain_congr {D D' : List ExtDecl}
    (h : ∀ f as r, declared D f as r = declared D' f as r) (Γ : Ctxt nfDialect) (t : NfTy) :
    extChain D Γ t = extChain D' Γ t := by
  have hs : extCallStep D Γ [t] = extCallStep D' Γ [t] := by
    unfold extCallStep
    congr 1
    funext p
    refine nfToCatExt_congr (fun f as r => ?_) p TRd.id
    simp only [fieldDeclsFor, declared, List.any_append] at h ⊢
    have h1 := declared_filter_fieldTag D f as r
    have h2 := declared_filter_fieldTag D' f as r
    simp only [declared] at h1 h2
    rw [h1, h2, h f as r]
  unfold extChain extChainCore
  rw [hs]

/-- **The certificate of the chain with declarations**, between the source semantics at the
    builtin table `bi` and the fuel `tf` and the semantics of `jasminDialect` at the call
    environment `E'` and a fuel `cf` at least `tf`, under `SubTable bi`,
    `FieldLevel.FieldCalls bi`, `FieldLevel.FieldCallsWideEq bi` and the agreement
    `ExtAgree bi (catEnvOf E') D` of the table, the declarations and the
    environment of `catCryptDialect` read off `E'`. The elimination of aborting branches
    (`abortElimCert` with `nfDenote_isAbort`) and tuple flattening (`flatSameCert`) are
    certified at equal inputs and outputs. The steps up to the montify step are
    certified at `fieldEnv E'`, the field dialect step from `fieldEnv E'` to `E'`, and the later
    steps at `E'`. -/
def extChainCert {bi : Builtins} (hbi : SubTable bi) (hF : FieldLevel.FieldCalls bi)
    (hW : FieldLevel.FieldCallsWideEq bi) (tf cf : Nat) (hle : tf ≤ cf) {D : List ExtDecl}
    (E' : CallEnv jasminDialect)
    (hD : ExtAgree bi (catEnvOf E') D) (Γ : Ctxt nfDialect) (t : NfTy) :
    Cert (extChain D Γ t) (nfSemB bi tf Γ [t])
      (nfSemE E' cf (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) :=
  .cons (@abortElimCert nfDialect _ _ _ _ NfOp.isAbort (nfDenote (tableOf bi)) _
    (fun e V h => nfDenote_isAbort (tableOf bi) e V h) tf Γ [t]) <|
  .cons (flatSameCert bi tf Γ [t]) <|
  .cons (outTyCert bi tf Γ t) <|
    .cons (@dceCert nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ tf Γ [t]) <|
    .cons (extCallCert hbi hF hW tf cf hle hD Γ [t]) <|
    .cons (aegraphEnvCert (catEnvOf (fieldEnv E')) catRules cf (Γ.map catTy) [catTy t]) <|
    .cons (StepCert.ofMapAt? catToJasmin catToJasmin_regionTypes (fun x => ctTransTy x)
      ctMapValD catToJasmin_varTransports (fun e blk hb V => catToJasmin_block e blk hb V)
      catToJasmin_mapValExtends catToJasmin_regionTransports (catEnvOf (fieldEnv E'))
      (fieldEnv E') (catEnvOf_transports (fieldEnv E')) cf (Γ.map catTy) [catTy t]) <|
    .cons (montifyStepCert E' cf (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (fieldDialectCert E' cf (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (lowerSelectsEnvCert E' cf (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (rangeEnvCert E' cf (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .cons (aegraphEnvCert E' jasminRules cf (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) <|
    .nil _

/-- A program the chain accepts has a result type that passes the check `outTyB`. -/
theorem extChain_outTyB {D : List ExtDecl} {Γ : Ctxt nfDialect} {t : NfTy}
    {p : NFProg nfDialect Γ [t]}
    {q : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]}
    (h : (extChain D Γ t).run p = some q) : outTyB t = true := by
  simp only [extChain, extChainCore, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, hq, -⟩ := h
  exact outTyStep_run_isSome hq

/-- **The chain with declarations simulates the source program.** Under `SubTable bi`,
    `FieldLevel.FieldCalls bi`, `FieldLevel.FieldCallsWideEq bi` and
    `ExtAgree bi (catEnvOf E') D`, the program the chain
    returns denotes at the call environment `E'`, at every fuel `cf` at least the source fuel
    `tf` and from the transport of a valuation in range, a value whose source value is the
    encoding of the result of the source program at the builtin table `bi`. -/
theorem extChain_denote {bi : Builtins} (hbi : SubTable bi) (hF : FieldLevel.FieldCalls bi)
    (hW : FieldLevel.FieldCallsWideEq bi) (tf cf : Nat) (hle : tf ≤ cf) {D : List ExtDecl}
    (E' : CallEnv jasminDialect) (hD : ExtAgree bi (catEnvOf E') D) {Γ : Ctxt nfDialect}
    {t : NfTy} (p : NFProg nfDialect Γ [t])
    {q : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]}
    (h : (extChain D Γ t).run p = some q) (V : Valuation Γ)
    (hin : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V)) {y : t.denote}
    (hp : PDenP bi tf p V = some (HVector.cons y .nil)) :
    ∃ x, q.denoteAt E' cf (ctMapValD (mapVal V)) = some (HVector.cons x .nil) ∧
      denVal (mapTy (catTy t)) x = enc t y := by
  have ht := outTy_of_outTyB t (extChain_outTyB h)
  obtain ⟨o', ho', hrel⟩ := (extChainCert hbi hF hW tf cf hle E' hD Γ t).sound (V := V)
    (W := ctMapValD (mapVal V)) h
    ⟨V, rfl, V, rfl, V, rfl, V, rfl, mapVal V, ⟨rfl, hin⟩, mapVal V, rfl,
      ctMapValD (mapVal V), rfl,
      ctMapValD (mapVal V), rfl, ctMapValD (mapVal V), rfl, ctMapValD (mapVal V), rfl,
      ctMapValD (mapVal V), rfl, ctMapValD (mapVal V), rfl, rfl⟩
    hp
  obtain ⟨_, rfl, _, rfl, _, rfl, _, rfl, x2, hx2, _, rfl, _, rfl, _, rfl, _, rfl, _, rfl, _, rfl, _, rfl,
    rfl⟩ := hrel
  rcases x2 with _ | ⟨x, _ | _⟩
  have hx : VRel t y x := hx2.1
  exact ⟨ctTransTy x, ho', denVal_ctTransTy t ht y x hx⟩

/-- **The input of the exporter through the chain with declarations.** From an environment
    the layout `σ` reads off the entry state `sa` and a valuation of the parameters that
    holds its encodings, the transported valuation is one `σ` reads off `sa`, and at it the
    program the chain returns denotes at `E'`, at every fuel `cf` at least the source fuel
    `tf` (`hle`, discharged by `omega` when omitted), a value whose source value is the
    encoding of the result of the source program. -/
theorem extChain_entry {bi : Builtins} (hbi : SubTable bi) (hF : FieldLevel.FieldCalls bi)
    (hW : FieldLevel.FieldCallsWideEq bi) (tf cf : Nat) {D : List ExtDecl}
    (E' : CallEnv jasminDialect) (hD : ExtAgree bi (catEnvOf E') D) {σ : AbiLayout}
    {sa : AState} {env : Env} (hσ : σ.EnvOf sa env) {t : NfTy}
    (p : NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    {q : NFProg jasminDialect (mapCtx ((entryCtx (abiEntry σ)).map catTy)) [mapTy (catTy t)]}
    (h : (extChain D _ t).run p = some q) (V : Valuation (entryCtx (abiEntry σ)))
    (hV : EntryVals env (abiEntry σ) V) {y : t.denote}
    (hp : PDenP bi tf p V = some (HVector.cons y .nil)) (hle : tf ≤ cf := by omega) :
    AbiValOf σ sa (ctMapValD (mapVal V)) ∧
      ∃ x, q.denoteAt E' cf (ctMapValD (mapVal V)) = some (HVector.cons x .nil) ∧
        denVal (mapTy (catTy t)) x = enc t y :=
  ⟨abiValOf_mapVal hσ V hV,
    extChain_denote hbi hF hW tf cf hle E' hD p h V (inRange_entry hσ V hV) hp⟩

/-! ## The exported code over procedure summaries -/

/-- **A source run is matched by a run of the exported code over procedure summaries.**
    Let the chain with the declarations `D` return `q` on `p`, let `q` pass the test
    `regionExportableB` of the region exporter, let the table `T` of procedure summaries
    agree with the call environment `E'` (`ProcsAgree`), and let `SubTable bi`,
    `FieldLevel.FieldCalls bi`, `FieldLevel.FieldCallsWideEq bi` and
    `ExtAgree bi (catEnvOf E') D` hold. For a run of `p` at the builtin table `bi` from a
    valuation `V` in range to `y` at the fuel `tf ≤ cf`, the code `exportR` gives for `q`,
    as the body of a
    one-function program run by the run function of `x86Isa.withProcs T` from a state at
    counter `0` whose store agrees with the transport of `V`, halts at every fuel from some
    bound on in a state that agrees with the returned operands at a value whose source
    value is the encoding of `y`, and that reads as the entry state at every argument
    register.

    The hypothesis `hx : x86Isa.RefusesProcs T` is the open obligation of the exporter's
    call arm (`exportR_sim_procs`): the x86 flag machine has no step on a shadow instruction
    of a call of a symbol of `T`. It is carried here and proved nowhere. -/
theorem extChain_run_procs {bi : Builtins} (hbi : SubTable bi)
    (hF : FieldLevel.FieldCalls bi) (hW : FieldLevel.FieldCallsWideEq bi) (tf cf : Nat)
    (hle : tf ≤ cf) {D : List ExtDecl} (E' : CallEnv jasminDialect)
    (hD : ExtAgree bi (catEnvOf E') D) {T : ProcTable} (hT : ProcsAgree E' T) (hx : x86Isa.RefusesProcs T) (fn : String)
    {Γ : Ctxt nfDialect} {t : NfTy} (p : NFProg nfDialect Γ [t])
    {q : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]}
    (h : (extChain D Γ t).run p = some q) (hB : regionExportableB q = true)
    (V : Valuation Γ) (hin : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V))
    {y : t.denote} (hp : PDenP bi tf p V = some (HVector.cons y .nil))
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hag : StoreAgreesM (mapCtx (Γ.map catTy)).length (mapCtx (Γ.map catTy)).length b0
      (ctMapValD (mapVal V))) :
    ∃ x : ⟦mapTy (catTy t)⟧, denVal (mapTy (catTy t)) x = enc t y ∧
      ∃ r, exportR (mapCtx (Γ.map catTy)).length fn q (mapCtx (Γ.map catTy)).length 0 = some r ∧
        ∃ (k : Nat) (s : LstateMF),
          (∀ j, (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn r.code) (k + j)
            { prog := { base := b0, lfn := fn }, zf := zf } = some s)
          ∧ atPc (singletonProgM fn r.code) r.code.length s
          ∧ ResAgrees (mapCtx (Γ.map catTy)).length r.depth s.prog.base r.res
              (HVector.cons x .nil)
          ∧ RegionFrame (mapCtx (Γ.map catTy)).length 0 b0 s.prog.base := by
  obtain ⟨x, hden, hx'⟩ := extChain_denote hbi hF hW tf cf hle E' hD p h V hin hp
  exact ⟨x, hx', exportR_run_procs fn hT hx (regionExportableB_sound hB) cf _ _ hden b0 zf
    hpc hag⟩

/-! ## The region front of an entry -/

/-- **The region front of an entry**: the translation `toNF`, the chain `extChain` at the
    declared procedures `E.decls s` of the source program, and the region export
    `exportRegion` of the structured program at the signatures of those declarations. A
    call of a declared procedure stays a `call` of the result; `compileRegion` compiles it
    only when the compiler at the entry (`NFEntry.compileR`) passes the callee data of the
    procedure, and refuses it otherwise. A tagged field call is no `call` of the result:
    the field dialect step lowers it to limb templates or the chain refuses. -/
def NFEntry.frontR (E : NFEntry) (σ : AbiLayout) (s : E.Src) : Option AnyRouteProgJ :=
  (E.toNF σ s).bind fun q =>
    (((extChain (E.decls s) _ q.1).run q.2).bind
      (exportRegion (declSigs (E.decls s)))).map fun rp => ⟨nfCtx σ, _, rp⟩

/-- A result of the region front is a structured program. -/
theorem NFEntry.frontR_regions {E : NFEntry} {σ : AbiLayout} {s : E.Src} {p : AnyRouteProgJ}
    (hf : E.frontR σ s = some p) :
    ∃ q : NFProg jasminDialect p.1 [p.2.1], p.2.2 = .regions q := by
  obtain ⟨q, -, hf⟩ := Option.bind_eq_some_iff.mp hf
  obtain ⟨rp, hrp, rfl⟩ := Option.map_eq_some_iff.mp hf
  obtain ⟨p', -, hex⟩ := Option.bind_eq_some_iff.mp hrp
  exact ⟨p', exportRegion_eq_some hex⟩

/-- **An entry composed with the chain with its declared procedures and the region export
    is a front**, at the call environment `E.env` of the entry. The leg is the soundness of
    the entry, which gives a fuel `k` of the callees, followed by `extChain_entry` at the
    table `E.bi s k`, the environment `E.env s k` and the program fuel `k`: the structured
    program denotes at that environment a value whose source value is the value of the
    source run. A call of a declared procedure is answered by `E.env s k`, which implements
    the function the table `E.bi s k` gives the name.

    For an entry with the default environment, and at a source program without declared
    procedures, the leg is the leg at the environment in which every call refuses
    (`RouteProgJ.envDenote_empty`, `RouteProgJ.envDenote_regions_of_callFree`). -/
def NFEntry.toFrontLegOfR (E : NFEntry) : FrontLegOfJ where
  Src := E.Src
  Runs := E.Runs
  front := E.frontR
  names := E.names
  env := E.env
  leg σ s p hf sa v hreg hrun := by
    obtain ⟨q, hq, hf⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨rp, hrp, rfl⟩ := Option.map_eq_some_iff.mp hf
    obtain ⟨p', hp', hex⟩ := Option.bind_eq_some_iff.mp hrp
    obtain rfl := exportRegion_eq_some hex
    obtain ⟨k, D, env, V, y, hD, hsub, hag, henv, hV, ⟨tf, hle, hp⟩, hv⟩ :=
      E.sound σ s q hq sa v hreg hrun
    rw [← extChain_congr hD] at hp'
    obtain ⟨hA, x, hx, hden⟩ :=
      extChain_entry hsub (E.fieldCalls σ s q hq k) (E.fieldCallsWide σ s q hq k) tf k
        (E.env s k) hag henv q.2 hp' V hV hp hle
    refine ⟨_, k, x, hA, ?_, hv.trans hden.symm⟩
    change (p'.denoteAt (E.env s k) k (ctMapValD (mapVal V))).map oneResult = some x
    rw [hx]
    rfl

/-- **A source run is matched by a run of the exported code in which each declared symbol
    is the function of its declaration.** Let the translation of the entry return `q` on the
    source program `s`, the chain with the declared procedures of `s` return the structured
    program `p` on `q`, and `p` pass the test `regionExportableB` of the region exporter.
    For every value `v` of a source run from an entry state `sa` satisfying `σ.Regions`
    there are a fuel `k` of the callees, a valuation `V` that `σ` reads off `sa` and a value
    `x` with source value `v` such that `p` denotes `x` at `V`, at the call environment
    `E.env s k` and the fuel `k`; and for every table `T` of procedure summaries that agrees
    with `E.env s k` (`ProcsAgree`) and whose symbols the x86 flag machine refuses
    (`RefusesProcs`), the code `exportR` gives for `p`, as the body of a one-function program
    run by the run function of `x86Isa.withProcs T` from a state at counter `0` whose store
    agrees with `V`, halts at every fuel from some bound on in a state that agrees with the
    returned operands at `x` and reads as the entry state at every argument register.

    At the hax entry `haxEntry` the environment `E.env s k` answers the symbol of a linked
    function by its meaning `LinkedFn.sem` (`tableEnv` at `HaxModule.linkTable`), so a table
    `T` that agrees with it holds, at each linked symbol, a summary whose function is that
    meaning. The statement is about the exported code over
    procedure summaries; it is not a statement about bytes. The two hypotheses on `T` are
    carried: `ProcsAgree` is the obligation on the summaries of the callees, and
    `RefusesProcs` is the obligation of the exporter's call arm (`exportR_sim_procs`). -/
theorem NFEntry.frontR_run_procs (E : NFEntry) {σ : AbiLayout} {s : E.Src}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]} (hq : E.toNF σ s = some q)
    {p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]}
    (hp : (extChain (E.decls s) _ q.1).run q.2 = some p) (hB : regionExportableB p = true)
    {sa : AState} {v : _root_.Hax.Value} (hreg : σ.Regions sa) (hrun : E.Runs σ s sa v) :
    ∃ (k : Nat) (V : Valuation (nfCtx σ)) (x : ⟦mapTy (catTy q.1)⟧),
      AbiValOf σ sa V ∧ v = denVal (mapTy (catTy q.1)) x ∧
      p.denoteAt (E.env s k) k V = some (HVector.cons x .nil) ∧
      ∀ (T : ProcTable), ProcsAgree (E.env s k) T → x86Isa.RefusesProcs T →
        ∀ (fn : String) (b0 : LstateM) (zf : Bool), b0.lpc = 0 →
          StoreAgreesM (nfCtx σ).length (nfCtx σ).length b0 V →
          ∃ r, exportR (nfCtx σ).length fn p (nfCtx σ).length 0 = some r ∧
            ∃ (j0 : Nat) (st : LstateMF),
              (∀ j, (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn r.code) (j0 + j)
                { prog := { base := b0, lfn := fn }, zf := zf } = some st)
              ∧ atPc (singletonProgM fn r.code) r.code.length st
              ∧ ResAgrees (nfCtx σ).length r.depth st.prog.base r.res (HVector.cons x .nil)
              ∧ RegionFrame (nfCtx σ).length 0 b0 st.prog.base := by
  obtain ⟨k, D, env, V, y, hD, hsub, hag, henv, hV, ⟨tf, hle, hden⟩, hv⟩ :=
    E.sound σ s q hq sa v hreg hrun
  rw [← extChain_congr hD] at hp
  obtain ⟨hA, x, hx, hxv⟩ :=
    extChain_entry hsub (E.fieldCalls σ s q hq k) (E.fieldCallsWide σ s q hq k) tf k
      (E.env s k) hag henv q.2 hp V hV hden hle
  exact ⟨k, _, x, hA, hv.trans hxv.symm, hx, fun T hT hRef fn b0 zf hpc hst =>
    exportR_run_procs fn hT hRef (regionExportableB_sound hB) k _ _ hx b0 zf hpc hst⟩

end CatCrypt.Crypto.SecureCompilation.Haxc

namespace CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montifyStep montifyStep_of_callFree)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep (fieldDialectStep
  fieldDialectStep_completeOn)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (aegraphOptNF)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.NFToCatImages (Convertible OpsHaveImages
  isSome_map?_catToJasmin_iff aegraphOptNF_catRules_opsHaveImages)
open CatCrypt.Crypto.Hax.NFToCatComplete (NB nfToCat_isSome_of_NB NBD nfToCatExt_isSome_of_NBD)
open _root_.Hax.FieldTag (fieldTag?)
open Ctxt (Var Valuation)

/-! ## The chain on the programs of `NB` -/

/-- **The steps of `extChain` after flattening are complete on `extDomNB`.** -/
theorem extChainCore_completeOn_NB (D : List ExtDecl) (Γ : Ctxt nfDialect) (t : NfTy) :
    (extChainCore D Γ t).CompleteOn (fun p => extDomNB t p = true) (fun _ => True) := by
  have h0 : (outTyStep Γ t).CompleteOn (fun p => extDomNB t p = true)
      (fun p => extDomNB t p = true) := by
    intro p hp
    have ht : outTyB t = true := by
      simp only [extDomNB, Bool.and_eq_true] at hp
      exact hp.1
    exact ⟨p, by simp only [outTyStep, ht, ite_true], hp⟩
  have h1 : (dceStep Γ [t]).CompleteOn (fun p => extDomNB t p = true)
      (fun q => NB q = true) := by
    intro p hp
    simp only [extDomNB, Bool.and_eq_true] at hp
    exact ⟨_, rfl, hp.2⟩
  have h3 : (aegraphStep catRules (Γ.map catTy) [catTy t]).CompleteOn
      (fun r => r.callFree = true ∧ OpsHaveImages r)
      (fun r => Convertible r ∧ r.callFree = true) := by
    rintro r ⟨hf, hi⟩
    refine ⟨_, rfl, (aegraphOptNF_catRules_opsHaveImages r hi).convertible, ?_⟩
    unfold aegraphOptNF
    exact (nfGo_callFree (d := catCryptDialect) catRules _ _ r).trans hf
  have h5 : (montifyStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]).CompleteOn
      (fun q => q.callFree = true) (fun q => fieldDomB q = true) :=
    fun q hq => ⟨q, montifyStep_of_callFree q hq, fieldDomB_of_callFree q hq⟩
  have h6 : (fieldDialectStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]).CompleteOn
      (fun q => fieldDomB q = true) (fun _ => True) :=
    fieldDialectStep_completeOn _ _
  have hT : ∀ {P Q : Type} (s : Step P Q) {E : P → Prop},
      (∀ p, (s.run p).isSome = true) → s.CompleteOn E (fun _ => True) := by
    intro P Q s E hs p _
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hs p)
    exact ⟨q, hq, trivial⟩
  exact Chain.completeOn_cons h0 <| Chain.completeOn_cons h1 <|
    Chain.completeOn_cons (extCallStep_completeOn_NB D Γ [t]) <| Chain.completeOn_cons h3 <|
    Chain.completeOn_cons (catToJasmin_completeOn _ _) <| Chain.completeOn_cons h5 <|
    Chain.completeOn_cons h6 <|
    Chain.completeOn_cons (hT _ (lowerSelectsStep_isSome _ _)) <|
    Chain.completeOn_cons (hT _ (synRangeStep_isSome _ _)) <|
    Chain.completeOn_cons (hT _ (aegraphStep_isSome _ _ _)) <| Chain.completeOn_nil _

/-- **`extChain` is complete on the programs whose flattening after the elimination of
    aborting branches lies in `extDomNB`.** -/
theorem extChain_completeOn_NB (D : List ExtDecl) (Γ : Ctxt nfDialect) (t : NfTy) :
    (extChain D Γ t).CompleteOn
      (fun p => ∃ q, (flatSameStep Γ [t]).run (NFProg.abortElim NfOp.isAbort p) = some q ∧
        extDomNB t q = true)
      (fun _ => True) :=
  Chain.completeOn_cons (fun _ hp => ⟨_, rfl, hp⟩) <|
    Chain.completeOn_cons (flatSameStep_completeOn Γ [t] _) (extChainCore_completeOn_NB D Γ t)

/-- **`extChain` runs to `some` on every program at a result type that passes `outTyB` whose
    flattening after the elimination of aborting branches has a dead-code-eliminated form that
    satisfies `NB`**, at every list of
    declarations. -/
theorem extChain_isSome_of_NB (D : List ExtDecl) {Γ : Ctxt nfDialect} {t : NfTy}
    {p q : NFProg nfDialect Γ [t]}
    (hq : (flatSameStep Γ [t]).run (NFProg.abortElim NfOp.isAbort p) = some q)
    (ht : outTyB t = true) (hp : NB (NFProg.dce q) = true) :
    ((extChain D Γ t).run p).isSome = true :=
  Chain.run_isSome (extChain_completeOn_NB D Γ t) ⟨q, hq, by simp only [extDomNB, ht, hp,
    Bool.and_self]⟩

/-! ## The chain on the programs of `NBD` -/

/-- **The steps of `extChain` after flattening are complete on `extDomNBD`.** The calls of
    the translation are transported
    by the e-graph pass (`callsAll_nfGo`), the conversion (`callsAll_map?`) and the montify
    pass (`callsAll_montifyPass`) into the domain `fieldDomB` of the field dialect step. -/
theorem extChainCore_completeOn_NBD (D : List ExtDecl) (Γ : Ctxt nfDialect) (t : NfTy) :
    (extChainCore D Γ t).CompleteOn (fun p => extDomNBD D t p = true) (fun _ => True) := by
  have h0 : (outTyStep Γ t).CompleteOn (fun p => extDomNBD D t p = true)
      (fun p => extDomNBD D t p = true) := by
    intro p hp
    have ht : outTyB t = true := by
      simp only [extDomNBD, Bool.and_eq_true] at hp
      exact hp.1.1
    exact ⟨p, by simp only [outTyStep, ht, ite_true], hp⟩
  have h1 : (dceStep Γ [t]).CompleteOn (fun p => extDomNBD D t p = true)
      (fun q => NBD (fieldDeclsFor D q) q = true ∧ fieldTemplsB q = true) := by
    intro p hp
    simp only [extDomNBD, Bool.and_eq_true] at hp
    exact ⟨_, rfl, hp.1.2, hp.2⟩
  have h3 : (aegraphStep catRules (Γ.map catTy) [catTy t]).CompleteOn
      (fun r => callsAll (fun f as rs => fieldCallB f (as.map mapTy) (rs.map mapTy)) r = true ∧
        OpsHaveImages r)
      (fun r => Convertible r ∧
        callsAll (fun f as rs => fieldCallB f (as.map mapTy) (rs.map mapTy)) r = true) := by
    rintro r ⟨hf, hi⟩
    refine ⟨_, rfl, (aegraphOptNF_catRules_opsHaveImages r hi).convertible, ?_⟩
    unfold aegraphOptNF
    exact (callsAll_nfGo (d := catCryptDialect) _ catRules _ _ r).trans hf
  have h4 : (mapStep catToJasmin catToJasmin_regionTypes (Γ.map catTy) [catTy t]).CompleteOn
      (fun r => Convertible r ∧
        callsAll (fun f as rs => fieldCallB f (as.map mapTy) (rs.map mapTy)) r = true)
      (fun q => fieldDomB q = true) := by
    rintro r ⟨hc, hf⟩
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
      ((isSome_map?_catToJasmin_iff r (fun v => v)).2 hc)
    refine ⟨q, hq, ?_⟩
    show fieldDomB q = true
    rw [fieldDomB_eq_callsAll]
    exact callsAll_map? catToJasmin catToJasmin_regionTypes fieldCallB r hf _ hq
  have h6 : (fieldDialectStep (mapCtx (Γ.map catTy)) [mapTy (catTy t)]).CompleteOn
      (fun q => fieldDomB q = true) (fun _ => True) :=
    fieldDialectStep_completeOn _ _
  have hT : ∀ {P Q : Type} (s : Step P Q) {E : P → Prop},
      (∀ p, (s.run p).isSome = true) → s.CompleteOn E (fun _ => True) := by
    intro P Q s E hs p _
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hs p)
    exact ⟨q, hq, trivial⟩
  exact Chain.completeOn_cons h0 <| Chain.completeOn_cons h1 <|
    Chain.completeOn_cons (extCallStep_completeOn_NBD D Γ [t]) <| Chain.completeOn_cons h3 <|
    Chain.completeOn_cons h4 <| Chain.completeOn_cons (montifyStep_completeOn _ _) <|
    Chain.completeOn_cons h6 <|
    Chain.completeOn_cons (hT _ (lowerSelectsStep_isSome _ _)) <|
    Chain.completeOn_cons (hT _ (synRangeStep_isSome _ _)) <|
    Chain.completeOn_cons (hT _ (aegraphStep_isSome _ _ _)) <| Chain.completeOn_nil _

/-- **`extChain` is complete on the programs whose flattening after the elimination of
    aborting branches lies in `extDomNBD`.** -/
theorem extChain_completeOn_NBD (D : List ExtDecl) (Γ : Ctxt nfDialect) (t : NfTy) :
    (extChain D Γ t).CompleteOn
      (fun p => ∃ q, (flatSameStep Γ [t]).run (NFProg.abortElim NfOp.isAbort p) = some q ∧
        extDomNBD D t q = true)
      (fun _ => True) :=
  Chain.completeOn_cons (fun _ hp => ⟨_, rfl, hp⟩) <|
    Chain.completeOn_cons (flatSameStep_completeOn Γ [t] _) (extChainCore_completeOn_NBD D Γ t)

/-- **`extChain` runs to `some` on every program at a result type that passes `outTyB` whose
    flattening after the elimination of aborting branches has a dead-code-eliminated form that
    satisfies `NBD` at its declarations and
    has a template for every tagged call**, at every list of declarations. -/
theorem extChain_isSome_of_NBD (D : List ExtDecl) {Γ : Ctxt nfDialect} {t : NfTy}
    {p q : NFProg nfDialect Γ [t]}
    (hq : (flatSameStep Γ [t]).run (NFProg.abortElim NfOp.isAbort p) = some q)
    (ht : outTyB t = true)
    (hp : NBD (fieldDeclsFor D (NFProg.dce q)) (NFProg.dce q) = true)
    (hT : fieldTemplsB (NFProg.dce q) = true) :
    ((extChain D Γ t).run p).isSome = true :=
  Chain.run_isSome (extChain_completeOn_NBD D Γ t) ⟨q, hq, by simp only [extDomNBD, ht, hp,
    hT, Bool.and_self]⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal
