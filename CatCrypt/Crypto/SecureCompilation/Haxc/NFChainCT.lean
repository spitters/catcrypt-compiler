/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChain
public import CatCrypt.Crypto.SecureCompilation.Haxc.FrontLeakOpt
public import CatCrypt.Crypto.SecureCompilation.Haxc.ExportNF
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphNFLeak
public import CatCrypt.Crypto.Optimizer.Rewrite.RangeNF
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFMapLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.NFIfToSelectLeak

/-!
# Constant time through the linear route as a chain

`nfChainCTCert` is a constant-time certificate (`PassChain.CTCert`) of the chain `nfChain`,
with one leaf per step, each an existing leakage lemma of the stage:

0. `outTy`: the identity;
1. `dce`: `NFProg.dce_ctRel`;
2. `nfToCat`: `nfToCat_leak_id`, at valuations in range and their mapped valuations; the
   events of the translation are the source events without those of division (`stripDiv`);
3. `aegraph` at `catRules`: `aegraphOptNF_ctRel` under `catRules_indep`;
4. `map?` along `catToJasmin`: `catToJasmin_map?_ctLeak` under `LeakCompat`;
5. `lowerSelects`: `lowerSelects_ctRel`; the lowering speculates only the ops `jasminQuiet`
   lists, whose events do not depend on their argument values at the parameters of the
   certificate (`jasminQuiet_opLeak_indep`), and the selects are quiet (`jasminSel_kind`);
6. `range`: `rangeNF_ctRel`, under quiet register arithmetic of the leakage model;
7. `aegraph` at `jasminRules`: `aegraphOptNF_ctRel` under `jasminRules_indep`, which needs the
   register arithmetic of the leakage model to be quiet;
8. `exportNFJ`: `exportNFJ_ctLeak`, at the same fuel.

`nfToCat` carries a branch of the source to a branch, and every step reads the unrestricted
leakage semantics `leakSemNF`. A branch whose arms pass `NFProg.Lowerable` is lowered to
selects with no event; a branch that stays is refused by `exportNFJ`. `nfChain_ct` is
`PassChain.CTCert.ct` at this certificate.

The statement from the level check, `nfChain_routeCT_cat`, takes the program of
`catCryptDialect` constant time (`NFCT`), which the level check gives
(`NFProg.nfCT_of_levelCheck`); the level check accepts a branch on a public condition, so
the program may branch. Each step keeps `NFCT`; at `lowerSelects` this is
`NFProg.nfCT_lowerSelects`, from `jasminQuiet_opLeak_indep` and `jasminSel_kind`, both
consequences of the compatibility of the leakage parameters and of quiet register
arithmetic; at `range` it is `rangeNF_nfCT`.

The front `nfFront` is the source `nfSrcProg σ te` followed by the chain, and
`nfFrontC.front` is `nfFront` on the extraction with the constants of the layout bound
(`nfFrontC_front`). The constant-time statements hold for `nfFront` and for `nfFrontC`,
with the quiet register arithmetic of the jasmin leakage model as an explicit hypothesis
(the e-graph pass at `jasminRules`):

* from the level check of the intermediate program of `catCryptDialect`
  (`nfFrontLeakCT`): constant time is kept step by step by the suffix of the chain from step 3
  (`nfChain_routeCT_cat`);
* from constant time of the `nfDialect` source relative to its runs (`NFCTRel`): `nfChain_ct`.

## Main definitions

* `stepCertOfLeak` — the constant-time step certificate of a two-run leakage statement.
* `leakSemNF`, `leakSemIfFree`, `srcLeakSem`, `routeLeakSem` — the leakage semantics along
  the chain.
* `nfChainCTCert` — the constant-time certificate of `nfChain`.

## Main results

* `nfChain_ct` — equal source events of two runs at a fuel give two runs of the exported
  program at that fuel with equal events.
* `nfChain_routeCT_cat` — a constant-time intermediate program of `catCryptDialect` at a fuel
  gives an exported program constant time at that fuel (`RouteCTJ`).
* `RouteProgJ.opt_ctLeak_eq`, `RouteProgJ.opt_ctLeak_some`, `RouteCTJ_opt` — the
  optimisation stage keeps equal events and constant time.
* `nfFront_routeCT`, `_owned`, `_src`, `_src_check`, `_opt`, `_opt_owned`, `_src_opt` and
  the same seven for `nfFrontC` — the constant-time statements of the front through the chain;
  on a route program `RouteProgJ.straightLoop rp` they give the statements on `RouteCT` and
  `RouteProg.ctLeak` through `routeCTJ_straightLoop_iff` and `RouteProgJ.ctLeak_straightLoop`
  (`nfFront_routeCT_straight`).
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
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes catToJasmin_map?_ctLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak (CatLeakParams catLeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric (RuleSet RulesIndep)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (aegraphOptNF aegraphOptNF_ctRel
  aegraphOptNF_catRules_nfCT aegraphOptNF_jasminRules_nfCT ifFree_aegraphOptNF)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules catRules_indep)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules jasminRules_indep)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNF (rangeNF rangeNFStep rangeNF_ctRel rangeNF_nfCT)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnv impToNF hax64SigOf tableOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open Ctxt (Var Valuation)
open _root_.Hax (TExpr)

/-! ## A constant-time step certificate from a two-run statement -/

/-- **The constant-time step certificate of a two-run leakage statement.** For a relation
    `R` on inputs: two successful source runs at inputs related to `W₁`, `W₂` give two
    successful target runs at `W₁`, `W₂`, with equal events when the source events are equal.
    The input relation of the two-run semantics is `R` on both components and the output
    relation is `ctRel`. -/
def stepCertOfLeak {P Q : Type} {f : P → Option Q} (L : LeakSem P) (L' : LeakSem Q)
    (R : L.In → L'.In → Prop)
    (h : ∀ {p q V₁ V₂ W₁ W₂ l₁ l₂}, f p = some q → R V₁ W₁ → R V₂ W₂ →
      L.leak p V₁ = some l₁ → L.leak p V₂ = some l₂ →
      ∃ m₁ m₂, L'.leak q W₁ = some m₁ ∧ L'.leak q W₂ = some m₂ ∧ (l₁ = l₂ → m₁ = m₂)) :
    StepCert f L.twoRun L'.twoRun where
  relIn V W := R V.1 W.1 ∧ R V.2 W.2
  relOut := ctRel
  sound := by
    rintro p q ⟨V₁, V₂⟩ ⟨W₁, W₂⟩ o hf ⟨h1, h2⟩ hd
    obtain ⟨hl₁, hl₂⟩ := L.twoRun_den_eq_some hd
    obtain ⟨m₁, m₂, hm₁, hm₂, he⟩ := h hf h1 h2 hl₁ hl₂
    exact ⟨(m₁, m₂), L'.twoRun_den q W₁ W₂ m₁ m₂ hm₁ hm₂, he⟩

/-! ## The leakage semantics along the chain -/

section Sems

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenote d]

/-- The leakage semantics of structured programs at the leakage model `M` and the fuel
    `fuel`: the events of `NFProg.leakRun`. -/
def leakSemNF (M : LeakModel d) (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    LeakSem (NFProg d Γ ts) where
  In := Valuation Γ
  Ev := CTLeak
  leak p V := (NFProg.leakRun M fuel p V).map Prod.snd

/-- The leakage semantics of branch-free structured programs: the events of
    `NFProg.leakRun` of a program without `ifThenElse`, and no run otherwise. -/
def leakSemIfFree (M : LeakModel d) (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    LeakSem (NFProg d Γ ts) where
  In := Valuation Γ
  Ev := CTLeak
  leak p V := if NFProg.ifFree p then (NFProg.leakRun M fuel p V).map Prod.snd else none

theorem leakSemIfFree_leak_eq_some {M : LeakModel d} {fuel : Nat} {Γ : Ctxt d}
    {ts : List d.Ty} {p : NFProg d Γ ts} {V : Valuation Γ} {l : List CTLeak}
    (h : (leakSemIfFree M fuel Γ ts).leak p V = some l) :
    NFProg.ifFree p = true ∧ (NFProg.leakRun M fuel p V).map Prod.snd = some l := by
  simp only [leakSemIfFree] at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

variable [DecidableEq d.Ty] [DecidableEq d.Op]

/-- **The e-graph pass at two runs.** Under `RulesIndep`, two successful runs of `p` give two
    successful runs of `aegraphOptNF R p`, with equal events when those of `p` are equal. -/
theorem aegraphOptNF_leak2 {M : LeakModel d} (R : RuleSet d) (hI : RulesIndep M R)
    (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (V₁ V₂ : Valuation Γ)
    {l₁ l₂ : List CTLeak} (h₁ : (NFProg.leakRun M fuel p V₁).map Prod.snd = some l₁)
    (h₂ : (NFProg.leakRun M fuel p V₂).map Prod.snd = some l₂) :
    ∃ m₁ m₂, (NFProg.leakRun M fuel (aegraphOptNF R p) V₁).map Prod.snd = some m₁ ∧
      (NFProg.leakRun M fuel (aegraphOptNF R p) V₂).map Prod.snd = some m₂ ∧
      (l₁ = l₂ → m₁ = m₂) := by
  obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
  obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
  obtain ⟨s₁, -, hs₁, -⟩ := aegraphOptNF_ctRel R hI fuel p V₁ V₁ r₁ r₁ hr₁ hr₁ rfl
  obtain ⟨s₂, -, hs₂, -⟩ := aegraphOptNF_ctRel R hI fuel p V₂ V₂ r₂ r₂ hr₂ hr₂ rfl
  refine ⟨s₁.2, s₂.2, by rw [hs₁]; rfl, by rw [hs₂]; rfl, fun he => ?_⟩
  obtain ⟨t₁, t₂, ht₁, ht₂, -, -, het⟩ := aegraphOptNF_ctRel R hI fuel p V₁ V₂ r₁ r₂ hr₁ hr₂ he
  rw [hs₁, Option.some.injEq] at ht₁
  rw [hs₂, Option.some.injEq] at ht₂
  rw [ht₁, ht₂, het]

/-- The step certificate of the e-graph pass at the unrestricted leakage semantics. -/
def aegraphCTStep {M : LeakModel d} (R : RuleSet d) (hI : RulesIndep M R) (fuel : Nat)
    (Γ : Ctxt d) (ts : List d.Ty) :
    StepCert (aegraphStep R Γ ts).run (leakSemNF M fuel Γ ts).twoRun
      (leakSemNF M fuel Γ ts).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q _ _ _ _ _ _} hf hV₁ hV₂ h₁ h₂ => by
    cases hf
    subst hV₁ hV₂
    exact aegraphOptNF_leak2 R hI fuel p _ _ h₁ h₂

/-- The step certificate of the e-graph pass at the branch-free leakage semantics. -/
def aegraphCTStepIfFree {M : LeakModel d} (R : RuleSet d) (hI : RulesIndep M R)
    (fuel : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    StepCert (aegraphStep R Γ ts).run (leakSemIfFree M fuel Γ ts).twoRun
      (leakSemIfFree M fuel Γ ts).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q _ _ _ _ _ _} hf hV₁ hV₂ h₁ h₂ => by
    cases hf
    subst hV₁ hV₂
    obtain ⟨hif, h₁⟩ := leakSemIfFree_leak_eq_some h₁
    obtain ⟨-, h₂⟩ := leakSemIfFree_leak_eq_some h₂
    have hif' := ifFree_aegraphOptNF R p hif
    obtain ⟨m₁, m₂, hm₁, hm₂, he⟩ := aegraphOptNF_leak2 R hI fuel p _ _ h₁ h₂
    exact ⟨m₁, m₂, by simp only [leakSemIfFree, hif', ite_true, hm₁],
      by simp only [leakSemIfFree, hif', ite_true, hm₂], he⟩

end Sems

/-- The leakage semantics of programs of `nfDialect` over the leaf table of the builtin
    table `bi` at the leakage model `M`: the events of `NFProg.leakRunM`; at the default
    `nfLeakModel`, the events of `nfLeakRun`. -/
def srcLeakSem (bi : _root_.Hax.Builtins) (fuel : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy)
    (M : LeakModel nfDialect := nfLeakModel) : LeakSem (NFProg nfDialect Γ ts) where
  In := Valuation Γ
  Ev := CTLeak
  leak p V :=
    (@NFProg.leakRunM nfDialect _ _ _ _ (nfDenote (tableOf bi)) M fuel _ _ p V).map Prod.snd

/-- The leakage semantics of `RouteProgJ` programs: the events `RouteProgJ.ctLeak` at the
    leakage parameters `Pj` and the fuel `fuel`. -/
def routeLeakSem (Pj : JLeakParams) (fuel : Nat) (Γ : Ctxt jasminDialect) (t : JasminTy) :
    LeakSem (RouteProgJ Γ t) where
  In := Valuation Γ
  Ev := CTLeak
  leak rp W := RouteProgJ.ctLeak Pj fuel rp W

/-! ## The leaves of the steps -/

/-- The constant-time step certificate of the check of the result type: the identity. -/
def outTyCTStep (bi : _root_.Hax.Builtins) (fuel : Nat) (Γ : Ctxt nfDialect) (t : NfTy)
    (M : LeakModel nfDialect := nfLeakModel) :
    StepCert (outTyStep Γ t).run (srcLeakSem bi fuel Γ [t] M).twoRun
      (srcLeakSem bi fuel Γ [t] M).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q _ _ _ _ l₁ l₂} hf hV₁ hV₂ h₁ h₂ => by
    subst hV₁ hV₂
    simp only [outTyStep] at hf
    split at hf
    · cases hf
      exact ⟨l₁, l₂, h₁, h₂, _root_.id⟩
    · cases hf

/-- The constant-time step certificate of `dce` at the leakage model `M`, from
    `NFProg.dce_ctRel`. -/
def dceCTStep (bi : _root_.Hax.Builtins) (fuel : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy)
    (M : LeakModel nfDialect := nfLeakModel) :
    StepCert (dceStep Γ ts).run (srcLeakSem bi fuel Γ ts M).twoRun
      (srcLeakSem bi fuel Γ ts M).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q V₁ V₂ _ _ _ _} hf hV₁ hV₂ h₁ h₂ => by
    let _ := nfDenote (tableOf bi)
    cases hf
    subst hV₁ hV₂
    obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
    obtain ⟨s₁, -, hs₁, -⟩ := NFProg.dce_ctRel M fuel p V₁ V₁ r₁ r₁ hr₁ hr₁ rfl
    obtain ⟨s₂, -, hs₂, -⟩ := NFProg.dce_ctRel M fuel p V₂ V₂ r₂ r₂ hr₂ hr₂ rfl
    refine ⟨s₁.2, s₂.2, ?_, ?_, fun he => ?_⟩
    · exact congrArg (Option.map Prod.snd) hs₁
    · exact congrArg (Option.map Prod.snd) hs₂
    · obtain ⟨t₁, t₂, ht₁, ht₂, -, -, het⟩ :=
        NFProg.dce_ctRel M fuel p V₁ V₂ r₁ r₂ hr₁ hr₂ he
      rw [hs₁, Option.some.injEq] at ht₁
      rw [hs₂, Option.some.injEq] at ht₂
      rw [ht₁, ht₂, het]

/-- The constant-time step certificate of `nfToCat`, from `nfToCat_leak_id`: the input
    relation relates a valuation in range to its mapped valuation `mapVal`, and the events are
    those of the source without those of division (`stripDiv`), a function of the source
    events. -/
def nfToCatCTStep {P : CatLeakParams} (hP : NoVT P) {bi : _root_.Hax.Builtins}
    (hbi : SubTable bi) (fuel : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    StepCert (nfToCatStep Γ ts).run (srcLeakSem bi fuel Γ ts).twoRun
      (leakSemNF (catLeakModel P) fuel (Γ.map catTy) (ts.map catTy)).twoRun :=
  stepCertOfLeak _ _ (fun V W => W = mapVal V ∧ ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V))
    fun {p q V₁ V₂ _ _ _ _} hf hV₁ hV₂ h₁ h₂ => by
      obtain ⟨rfl, hin₁⟩ := hV₁
      obtain ⟨rfl, hin₂⟩ := hV₂
      obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
      obtain ⟨c₁, hc₁, e₁⟩ := nfToCat_leak_id hP hbi fuel hf V₁ hin₁ hr₁
      obtain ⟨c₂, hc₂, e₂⟩ := nfToCat_leak_id hP hbi fuel hf V₂ hin₂ hr₂
      exact ⟨c₁.2, c₂.2, by simp only [leakSemNF, hc₁, Option.map_some],
        by simp only [leakSemNF, hc₂, Option.map_some], fun he => by rw [e₁, e₂, he]⟩

/-- The constant-time step certificate of `map?` along `catToJasmin`, from
    `catToJasmin_map?_ctLeak`: the input relation is the graph of `ctMapValD`, and the
    events are those of the source. -/
def mapCTStep {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj) (fuel : Nat)
    (Γ : Ctxt catCryptDialect) (ts : List _) :
    StepCert (mapStep catToJasmin catToJasmin_regionTypes Γ ts).run
      (leakSemNF (catLeakModel P) fuel Γ ts).twoRun
      (leakSemNF (jLeakModel Pj) fuel (mapCtx Γ) (ts.map mapTy)).twoRun :=
  stepCertOfLeak _ _ (fun V W => W = ctMapValD V) fun {p q V₁ V₂ _ _ l₁ l₂} hf hV₁ hV₂ h₁ h₂ => by
    subst hV₁ hV₂
    exact ⟨l₁, l₂, (catToJasmin_map?_ctLeak hc fuel p q hf V₁).trans h₁,
      (catToJasmin_map?_ctLeak hc fuel p q hf V₂).trans h₂, _root_.id⟩

/-- **The select of `jasminDialect` is quiet** at leakage parameters compatible with
    parameters of `catCryptDialect`. The block of `bitToSword w` is two register constants
    and `select w`, and it emits the events of `bitToSword w`, at most one event, on one
    argument value; a variable-time `select w` would emit an event on three. -/
theorem jKind_select_of_leakCompat {P : CatLeakParams} {Pj : JLeakParams}
    (hc : LeakCompat P Pj) (w : Nat) : (jLeakModel Pj).kind (.select w) = .quiet := by
  have h := hc.2.2
    (Γ := [CatCrypt.Crypto.SecureCompilation.CryptoSSA.CryptoTy.bit]) (t := .sword w)
    ⟨CatCryptOp.bitToSword w, rfl, .cons .here .nil⟩ _ rfl (.cons false .nil)
  change jKind Pj (.select w) = .quiet
  rcases hs : Pj.opVT (.select w) with _ | m
  · simp only [jKind, hs]
  · exfalso
    simp only [Com.ctLeak, Expr.ctLeak, opLeak, jLeakModel, catLeakModel, jKind,
      Dialects.CryptoDialectCTLeak.catKind, hs] at h
    rcases h1 : Pj.opVT (.regConst w (BitVec.allOnes w).toNat) with _ | m1 <;>
      rcases h2 : Pj.opVT (.regConst w 0) with _ | m2 <;>
      rcases h3 : P.opVT (.bitToSword w) with _ | m3 <;>
      simp only [h1, h2, h3, List.nil_append, List.append_nil, List.cons_append,
        List.cons.injEq, CTLeak.vt.injEq, reduceCtorEq, and_false, and_true] at h
    have hl : (3 : Nat) = 1 := congrArg List.length h.2
    exact absurd hl (by decide)

/-- **A register constant below `2 ^ w` is quiet** at leakage parameters compatible with
    parameters of `catCryptDialect` with no variable-time operation: `regConst w n` is the
    lowering of `bvConst w n`. -/
theorem jKind_regConst_of_leakCompat {P : CatLeakParams} {Pj : JLeakParams} (hP : NoVT P)
    (hc : LeakCompat P Pj) (w n : Nat) (hn : n < 2 ^ w) :
    (jLeakModel Pj).kind (.regConst w n) = .quiet := by
  have h := hc.2.1 (Γ := []) (t := .sword w)
    ⟨CatCryptOp.bvConst w (BitVec.ofNat w n), rfl, .nil⟩ _ rfl
  change Pj.opVT (.regConst w (BitVec.ofNat w n).toNat) = P.opVT (.bvConst w _) at h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h
  change jKind Pj (.regConst w n) = .quiet
  simp only [jKind, h, hP (.bvConst w _)]

/-- **The events of the ops `jasminQuiet` lists do not depend on the argument values**, in
    the leakage model of `jasminDialect` at parameters with quiet register arithmetic,
    compatible with parameters of `catCryptDialect`: register arithmetic and the select are
    quiet, and a register constant has no argument. -/
theorem jasminQuiet_opLeak_indep {P : CatLeakParams} {Pj : JLeakParams}
    (hc : LeakCompat P Pj) (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (op : JasminOp) (h : HasSelect.quiet (d := jasminDialect) op = true)
    (a b : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasminDialect) op)) :
    opLeak (jLeakModel Pj) op a = opLeak (jLeakModel Pj) op b := by
  change jasminQuiet op = true at h
  cases op <;> simp only [jasminQuiet, Bool.false_eq_true, decide_eq_true_eq] at h
  all_goals first
    | (simp only [opLeak, hq]; done)
    | (simp only [opLeak, jKind_select_of_leakCompat hc]; done)
    | (cases a; cases b; rfl)

/-- The select ops of `jasminDialect` are quiet under the hypotheses of
    `jKind_select_of_leakCompat`. -/
theorem jasminSel_kind {P : CatLeakParams} {Pj : JLeakParams}
    (hc : LeakCompat P Pj) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (h : HasSelect.selects (d := jasminDialect) t = true)
    (c : Var Γ (HasBitType.bit (d := jasminDialect))) (a b : Var Γ t) :
    (jLeakModel Pj).kind (HasSelect.sel h c a b).op = .quiet := by
  cases t with
  | reg w => exact jKind_select_of_leakCompat hc w
  | _ => exact absurd h Bool.false_ne_true

/-- The constant-time step certificate of `lowerSelects`, from `lowerSelects_ctRel`: the
    events of the arms of a lowered branch do not depend on the valuation
    (`jasminQuiet_opLeak_indep`) and the selects are quiet (`jasminSel_kind`), so two runs
    of the source with equal events are lowered to two runs with equal events. -/
def lowerSelectsQuietCTStep {P : CatLeakParams} {Pj : JLeakParams}
    (hc : LeakCompat P Pj) (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (fuel : Nat) (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    StepCert (lowerSelectsStep Γ ts).run (leakSemNF (jLeakModel Pj) fuel Γ ts).twoRun
      (leakSemNF (jLeakModel Pj) fuel Γ ts).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q V₁ V₂ _ _ l₁ l₂} hf hV₁ hV₂ h₁ h₂ => by
    cases hf
    subst hV₁ hV₂
    obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
    obtain ⟨s₁, s₂, hs₁, hs₂, -, -, he⟩ := NFProg.lowerSelects_ctRel (jLeakModel Pj)
      (jasminQuiet_opLeak_indep hc hq) (jasminSel_kind hc) fuel p V₁ V₂ r₁ r₂ hr₁ hr₂
    exact ⟨s₁.2, s₂.2, by simp only [leakSemNF, hs₁, Option.map_some],
      by simp only [leakSemNF, hs₂, Option.map_some], he⟩

/-- The constant-time step certificate of `lowerSelects` on branch-free programs, from
    `leakRun_lowerSelects`: the events are those of the source. -/
def lowerSelectsCTStep (Pj : JLeakParams) (fuel : Nat) (Γ : Ctxt jasminDialect)
    (ts : List JasminTy) :
    StepCert (lowerSelectsStep Γ ts).run (leakSemIfFree (jLeakModel Pj) fuel Γ ts).twoRun
      (leakSemNF (jLeakModel Pj) fuel Γ ts).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q V₁ V₂ _ _ l₁ l₂} hf hV₁ hV₂ h₁ h₂ => by
    cases hf
    subst hV₁ hV₂
    obtain ⟨hif, h₁⟩ := leakSemIfFree_leak_eq_some h₁
    obtain ⟨-, h₂⟩ := leakSemIfFree_leak_eq_some h₂
    refine ⟨l₁, l₂, ?_, ?_, _root_.id⟩
    · exact (congrArg (Option.map Prod.snd) (NFProg.leakRun_lowerSelects _ fuel p hif V₁)).trans h₁
    · exact (congrArg (Option.map Prod.snd) (NFProg.leakRun_lowerSelects _ fuel p hif V₂)).trans h₂

/-- The constant-time step certificate of the range stage, from `rangeNF_ctRel` under quiet
    register arithmetic: two runs of the source give two runs of `rangeNF` of it, with equal
    events when those of the source are equal. -/
def rangeCTStep {Pj : JLeakParams}
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet) (fuel : Nat)
    (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    StepCert (rangeNFStep Γ ts).run (leakSemNF (jLeakModel Pj) fuel Γ ts).twoRun
      (leakSemNF (jLeakModel Pj) fuel Γ ts).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q V₁ V₂ _ _ l₁ l₂} hf hV₁ hV₂ h₁ h₂ => by
    cases hf
    subst hV₁ hV₂
    obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
    obtain ⟨s₁, -, hs₁, -⟩ := rangeNF_ctRel hq fuel p V₁ V₁ r₁ r₁ hr₁ hr₁ rfl
    obtain ⟨s₂, -, hs₂, -⟩ := rangeNF_ctRel hq fuel p V₂ V₂ r₂ r₂ hr₂ hr₂ rfl
    refine ⟨s₁.2, s₂.2, by simp only [leakSemNF, hs₁, Option.map_some],
      by simp only [leakSemNF, hs₂, Option.map_some], fun he => ?_⟩
    obtain ⟨t₁, t₂, ht₁, ht₂, -, -, het⟩ := rangeNF_ctRel hq fuel p V₁ V₂ r₁ r₂ hr₁ hr₂ he
    rw [hs₁, Option.some.injEq] at ht₁
    rw [hs₂, Option.some.injEq] at ht₂
    rw [ht₁, ht₂, het]

/-- The constant-time step certificate of the export, from `exportNFJ_ctLeak`: the events of
    the exported program at the same fuel are those of the source. -/
def exportCTStep (Pj : JLeakParams) (fuel : Nat) (Γ : Ctxt jasminDialect) (t : JasminTy) :
    StepCert (exportStep Γ t).run (leakSemNF (jLeakModel Pj) fuel Γ [t]).twoRun
      (routeLeakSem Pj fuel Γ t).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q V₁ V₂ _ _ l₁ l₂} hf hV₁ hV₂ h₁ h₂ => by
    subst hV₁ hV₂
    exact ⟨l₁, l₂, (exportNFJ_ctLeak Pj fuel p hf V₁).symm.trans h₁,
      (exportNFJ_ctLeak Pj fuel p hf V₂).symm.trans h₂, _root_.id⟩

/-! ## The constant-time certificate of the chain -/

/-- **The constant-time certificate of the linear route**, at the leakage parameters `P` of
    `catCryptDialect` with no variable-time operation, the parameters `Pj` of `jasminDialect`
    compatible with them and with quiet register arithmetic, the builtin table `bi` and the
    fuel `fuel`: one leaf per step of `nfChain`. -/
def nfChainCTCert {P : CatLeakParams} {Pj : JLeakParams} (hP : NoVT P) (hc : LeakCompat P Pj)
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (fuel : Nat) (Γ : Ctxt nfDialect)
    (t : NfTy) :
    CTCert (nfChain Γ t) (srcLeakSem bi fuel Γ [t])
      (routeLeakSem Pj fuel (mapCtx (Γ.map catTy)) (mapTy (catTy t))) :=
  .cons (outTyCTStep bi fuel Γ t) (fun _ _ h => h) <|
    .cons (dceCTStep bi fuel Γ [t]) (fun _ _ h => h) <|
    .cons (nfToCatCTStep hP hbi fuel Γ [t]) (fun _ _ h => h) <|
    .cons (aegraphCTStep catRules catRules_indep fuel (Γ.map catTy) [catTy t])
      (fun _ _ h => h) <|
    .cons (mapCTStep hc fuel (Γ.map catTy) [catTy t]) (fun _ _ h => h) <|
    .cons (lowerSelectsQuietCTStep hc hq fuel (mapCtx (Γ.map catTy)) [mapTy (catTy t)])
      (fun _ _ h => h) <|
    .cons (rangeCTStep hq fuel (mapCtx (Γ.map catTy)) [mapTy (catTy t)]) (fun _ _ h => h) <|
    .cons (aegraphCTStep jasminRules (jasminRules_indep hq) fuel (mapCtx (Γ.map catTy))
      [mapTy (catTy t)]) (fun _ _ h => h) <|
    .cons (exportCTStep Pj fuel (mapCtx (Γ.map catTy)) (mapTy (catTy t))) (fun _ _ h => h) <|
    .nil _

/-- **Constant time through the linear route.** Two runs of the source `p` at the fuel
    `fuel` from valuations in range with equal events give two runs of the program `nfChain`
    returns at the same fuel, from the transported valuations, with equal events; this is
    `PassChain.CTCert.ct` at `nfChainCTCert`. -/
theorem nfChain_ct {P : CatLeakParams} {Pj : JLeakParams} (hP : NoVT P) (hc : LeakCompat P Pj)
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (fuel : Nat) {Γ : Ctxt nfDialect}
    {t : NfTy} (p : NFProg nfDialect Γ [t])
    {rp : RouteProgJ (mapCtx (Γ.map catTy)) (mapTy (catTy t))}
    (h : (nfChain Γ t).run p = some rp) (V₁ V₂ : Valuation Γ)
    (hin₁ : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V₁))
    (hin₂ : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V₂))
    {r₁ r₂ : Valuation (d := nfDialect) [t] × List CTLeak}
    (h₁ : nfLeakRun bi fuel p V₁ = some r₁) (h₂ : nfLeakRun bi fuel p V₂ = some r₂)
    (he : r₁.2 = r₂.2) :
    ∃ m, RouteProgJ.ctLeak Pj fuel rp (ctMapValD (mapVal V₁)) = some m ∧
      RouteProgJ.ctLeak Pj fuel rp (ctMapValD (mapVal V₂)) = some m := by
  obtain ⟨m₁, m₂, hm₁, hm₂, hm⟩ := (nfChainCTCert hP hc hq hbi fuel Γ t).ct
    (W₁ := ctMapValD (mapVal V₁)) (W₂ := ctMapValD (mapVal V₂)) h
    ⟨(V₁, V₂), ⟨rfl, rfl⟩, (V₁, V₂), ⟨rfl, rfl⟩, (mapVal V₁, mapVal V₂),
      ⟨⟨rfl, hin₁⟩, ⟨rfl, hin₂⟩⟩, (mapVal V₁, mapVal V₂), ⟨rfl, rfl⟩,
      (ctMapValD (mapVal V₁), ctMapValD (mapVal V₂)), ⟨rfl, rfl⟩,
      (ctMapValD (mapVal V₁), ctMapValD (mapVal V₂)), ⟨rfl, rfl⟩,
      (ctMapValD (mapVal V₁), ctMapValD (mapVal V₂)), ⟨rfl, rfl⟩,
      (ctMapValD (mapVal V₁), ctMapValD (mapVal V₂)), ⟨rfl, rfl⟩,
      (ctMapValD (mapVal V₁), ctMapValD (mapVal V₂)), ⟨rfl, rfl⟩, rfl⟩
    (show (nfLeakRun bi fuel p V₁).map Prod.snd = some r₁.2 by rw [h₁]; rfl)
    (show (nfLeakRun bi fuel p V₂).map Prod.snd = some r₂.2 by rw [h₂]; rfl) he
  exact ⟨m₁, hm₁, hm ▸ hm₂⟩

/-! ## The suffix of the chain from the program of `catCryptDialect` -/

/-- **The input of `lowerSelects` along the chain is branch-free when the program of
    `catCryptDialect` is**: the e-graph pass and `map?` keep a program branch-free. -/
theorem nfChain_ifFree_lowerSelects {Γ : Ctxt nfDialect} {t : NfTy}
    {p' : NFProg catCryptDialect (Γ.map catTy) [catTy t]} (hif : NFProg.ifFree p' = true)
    {q : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]}
    (hq : NFProg.map? catToJasmin catToJasmin_regionTypes (aegraphOptNF catRules p')
      (fun v => v) = some q) :
    NFProg.ifFree q = true :=
  NFProg.ifFree_map? catToJasmin catToJasmin_regionTypes _
    (ifFree_aegraphOptNF catRules p' hif) _ q hq

/-- **Constant time through the chain from its program of `catCryptDialect`.** When the chain
    returns `rp` for `p` and the program `p'` that `nfToCat` translates `NFProg.dce p` to is
    constant time for `L`, the route program is constant time for `mapLabels L`: the e-graph
    passes and the range stage keep `NFCT` (`aegraphOptNF_catRules_nfCT`,
    `aegraphOptNF_jasminRules_nfCT`, `rangeNF_nfCT`),
    `map?` transports it (`catToJasmin_map?_ctLeak` with the section `ctBackV`),
    `lowerSelects` keeps it (`NFProg.nfCT_lowerSelects`: a branch it lowers emits the events
    of both arms, which do not depend on the valuation, and a branch it keeps emits the
    events of the source), and the export gives `RouteCTJ` at the same fuel
    (`exportNFJ_routeCT`). The program `p'` may branch; a branch `lowerSelects` keeps is
    refused by the export, so the route program has none. -/
theorem nfChain_routeCT_cat {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet) (fuel : Nat)
    {Γ : Ctxt nfDialect} {t : NfTy} (p : NFProg nfDialect Γ [t])
    {rp : RouteProgJ (mapCtx (Γ.map catTy)) (mapTy (catTy t))}
    (h : (nfChain Γ t).run p = some rp)
    {p' : NFProg catCryptDialect (Γ.map catTy) [catTy t]}
    (hp' : nfToCat (NFProg.dce p) TRd.id = some p')
    (L : Labels (d := catCryptDialect) (Γ.map catTy))
    (hct : NFCT (catLeakModel P) L fuel p') :
    RouteCTJ Pj (mapLabels L) fuel rp := by
  simp only [nfChain, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨q0, h0, q1, h1, q2, h2, q3, h3, q4, h4, q5, h5, q6, h6, q7, h7, q8, h8, h9⟩ := h
  simp only [outTyStep] at h0
  split at h0
  · cases h0
    cases h1
    cases h3
    cases h5
    cases h6
    cases h7
    cases h9
    change nfToCat (NFProg.dce p) TRd.id = some q2 at h2
    rw [hp', Option.some.injEq] at h2
    subst h2
    change NFProg.map? catToJasmin catToJasmin_regionTypes (aegraphOptNF catRules p')
      (fun v => v) = some q4 at h4
    have c3 := aegraphOptNF_catRules_nfCT fuel L p' hct
    have c4 : NFCT (jLeakModel Pj) (mapLabels L) fuel q4 := by
      intro W₁ W₂ hW
      have e₁ := catToJasmin_map?_ctLeak hc fuel _ q4 h4 (ctBackV W₁)
      have e₂ := catToJasmin_map?_ctLeak hc fuel _ q4 h4 (ctBackV W₂)
      rw [ctMapValD_ctBackV] at e₁ e₂
      exact e₁.trans ((c3 _ _ (pubEqV_ctBackV hW)).trans e₂.symm)
    have c5 : NFCT (jLeakModel Pj) (mapLabels L) fuel (NFProg.lowerSelects q4) :=
      NFProg.nfCT_lowerSelects (jLeakModel Pj) (jasminQuiet_opLeak_indep hc hq)
        (jasminSel_kind hc) fuel _ q4 c4
    exact exportNFJ_routeCT Pj fuel _ h8 _
      (aegraphOptNF_jasminRules_nfCT hq fuel _ _ (rangeNF_nfCT hq fuel _ _ c5))
  · cases h0

/-! ## The hax front through the chain -/

/-- **The intermediate program of `catCryptDialect` is a prefix run of the chain**:
    `nfCatProg σ te` is `nfToCat` after `NFProg.dce` on the source `nfSrcProg σ te`. -/
theorem nfCatProg_eq_of_nfSrcProg {σ : AbiLayout} {te : TExpr}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq : nfSrcProg σ te = some q) :
    nfCatProg σ te = (nfToCat (NFProg.dce q.2) TRd.id).map fun p' => ⟨q.1, p'⟩ := by
  unfold nfSrcProg at hq
  unfold nfCatProg
  split at hq
  · rename_i hok
    rw [ite_eq_left hok]
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hq
    rw [ho, Option.bind_some]
    rfl
  · cases hq

theorem nfFront_eq_some {σ : AbiLayout} {te : TExpr}
    {p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))} (hf : nfFront σ te = some p) :
    ∃ q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t],
      ∃ rp : RouteProgJ (nfCtx σ) (mapTy (catTy q.1)),
        nfSrcProg σ te = some q ∧ (nfChain _ q.1).run q.2 = some rp ∧ p = ⟨q.1, rp⟩ := by
  obtain ⟨q, hq, hf⟩ := Option.bind_eq_some_iff.mp hf
  obtain ⟨rp, hrp, rfl⟩ := Option.map_eq_some_iff.mp hf
  exact ⟨q, rp, hq, hrp, rfl⟩

/-- A property of route programs at every result type carries along an equality of route
    programs with their result types. -/
theorem routeProg_transfer {Γ : Ctxt jasminDialect} (Φ : (T : JasminTy) → RouteProg Γ T → Prop)
    {T T' : JasminTy} {r : RouteProg Γ T} {r' : RouteProg Γ T'}
    (h : (⟨Γ, T, r⟩ : AnyRouteProg) = ⟨Γ, T', r'⟩) (hr : Φ T r) : Φ T' r' := by
  cases h
  exact hr

/-- A property of `RouteProgJ` programs at every result type carries along an equality of
    such programs with their result types. -/
theorem routeProgJ_transfer {Γ : Ctxt jasminDialect}
    (Φ : (T : JasminTy) → RouteProgJ Γ T → Prop)
    {T T' : JasminTy} {r : RouteProgJ Γ T} {r' : RouteProgJ Γ T'}
    (h : (⟨Γ, T, r⟩ : AnyRouteProgJ) = ⟨Γ, T', r'⟩) (hr : Φ T r) : Φ T' r' := by
  cases h
  exact hr

theorem nfFrontC_front_eq_some {σ : AbiLayout} {te : TExpr}
    {p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))}
    (hf : nfFrontC.front σ (te : CatCrypt.Crypto.Hax.HaxModule) = some ⟨nfCtx σ, _, p.2⟩) :
    ∃ p' : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t)),
      nfFront σ (bindConsts σ.consts te) = some p' ∧
        (⟨nfCtx σ, _, p'.2⟩ : AnyRouteProgJ) = ⟨nfCtx σ, _, p.2⟩ := by
  rw [nfFrontC_front] at hf
  obtain ⟨p', hp', he⟩ := Option.map_eq_some_iff.mp hf
  exact ⟨p', hp', he⟩

/-! ## The optimisation stage on `RouteProgJ` keeps constant time -/

/-- **The optimisation stage keeps equal events**: two valuations at which a `RouteProgJ`
    program emits the same events give the same events of `p.opt`, under quiet register
    arithmetic of `jLeakModel Pj`. -/
theorem RouteProgJ.opt_ctLeak_eq {Pj : JLeakParams}
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : RouteProgJ Γ t) (V₁ V₂ : Valuation Γ)
    (h : RouteProgJ.ctLeak Pj fuel p V₁ = RouteProgJ.ctLeak Pj fuel p V₂) :
    RouteProgJ.ctLeak Pj fuel p.opt V₁ = RouteProgJ.ctLeak Pj fuel p.opt V₂ := by
  cases p with
  | straightLoop rp =>
      exact congrArg some (RouteProg.opt_ctLeak_eq hq rp V₁ V₂ (Option.some.inj h))
  | regions q => exact h

/-- The optimisation stage keeps two successful runs with equal events. -/
theorem RouteProgJ.opt_ctLeak_some {Pj : JLeakParams}
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : RouteProgJ Γ t) {V₁ V₂ : Valuation Γ}
    (h : ∃ m, RouteProgJ.ctLeak Pj fuel p V₁ = some m ∧ RouteProgJ.ctLeak Pj fuel p V₂ = some m) :
    ∃ m, RouteProgJ.ctLeak Pj fuel p.opt V₁ = some m ∧
      RouteProgJ.ctLeak Pj fuel p.opt V₂ = some m := by
  obtain ⟨m, h₁, h₂⟩ := h
  cases p with
  | straightLoop rp =>
      exact ⟨_, rfl, (RouteProgJ.opt_ctLeak_eq hq fuel (.straightLoop rp) V₁ V₂
        (h₁.trans h₂.symm)).symm⟩
  | regions q => exact ⟨m, h₁, h₂⟩

/-- **The optimisation stage keeps constant time** of a `RouteProgJ` program at a fuel,
    under quiet register arithmetic of `jLeakModel Pj`. -/
theorem RouteCTJ_opt {Pj : JLeakParams}
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (L : Labels Γ) (fuel : Nat) (p : RouteProgJ Γ t)
    (h : RouteCTJ Pj L fuel p) : RouteCTJ Pj L fuel p.opt :=
  fun V₁ V₂ hR => RouteProgJ.opt_ctLeak_eq hq fuel p V₁ V₂ (h V₁ V₂ hR)

/-! ## Constant time of the front through the chain -/

/-- **Constant time of the route program of the front.** When the level check of the
    compiler's intermediate program `nfCatProg σ te` accepts for the labels of the
    parameters in the secrecy record `s`, the route program `nfFront σ te` emits is constant
    time, at the leakage `jLeakModel Pj` with quiet register arithmetic, for the transported
    labels. The hypothesis is a check on the compiler's intermediate program; the conclusion
    concerns the emitted route program, not the hax source. -/
theorem nfFront_routeCT {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (h : nfFrontLeakCT P s σ te = true)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))) (hf : nfFront σ te = some p) :
    ∀ fuel : Nat, RouteCTJ Pj (mapLabels (nfLabels s (abiEntry σ))) fuel p.2 := by
  obtain ⟨q, rp, hq', hrp, rfl⟩ := nfFront_eq_some hf
  unfold nfFrontLeakCT at h
  rw [nfCatProg_eq_of_nfSrcProg hq'] at h
  rcases hp' : nfToCat (NFProg.dce q.2) TRd.id with _ | p'
  · rw [hp'] at h
    cases h
  · rw [hp', Option.map_some] at h
    exact fun fuel =>
      nfChain_routeCT_cat hc hq fuel q.2 hrp hp' _ (NFProg.nfCT_of_levelCheck _ fuel p' _ h)

/-- **Constant time of the route program of the front through the chain on the owned
    route**: the instance of `nfFront_routeCT` at the parameters with no variable-time
    leaf and no variable-time operation. -/
theorem nfFront_routeCT_owned (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (h : nfFrontLeakCT CatLeakParams.owned s σ te = true)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))) (hf : nfFront σ te = some p) :
    ∀ fuel : Nat, RouteCTJ JLeakParams.owned (mapLabels (nfLabels s (abiEntry σ))) fuel p.2 :=
  nfFront_routeCT leakCompat_owned (fun _ _ => rfl) s σ te h p hf

/-- **Constant time of a route program of the front**: the statement of `nfFront_routeCT` on
    `RouteCT` when the front returns a route program `RouteProgJ.straightLoop rp`. -/
theorem nfFront_routeCT_straight {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (h : nfFrontLeakCT P s σ te = true) {t : NfTy} (rp : RouteProg (nfCtx σ) (mapTy (catTy t)))
    (hf : nfFront σ te = some ⟨t, .straightLoop rp⟩) :
    RouteCT Pj (mapLabels (nfLabels s (abiEntry σ))) rp :=
  (routeCTJ_straightLoop_iff Pj _ 0 rp).1 (nfFront_routeCT hc hq s σ te h _ hf 0)

/-- **Constant time from the source to the route program of the front, relative to source
    runs.** Let the source `nfSrcProg σ te` be constant time for the labels of the secrecy
    record `s` relative to its successful runs over the leaf table of `bi`. For two entry
    valuations in range that agree on the public parameters and from which the source runs to
    results, the route program `nfFront σ te` emits equal events from their transported
    valuations, under quiet register arithmetic of `jLeakModel Pj`; it is `nfChain_ct`. -/
theorem nfFront_routeCT_src {P : CatLeakParams} {Pj : JLeakParams} (hP : NoVT P)
    (hc : LeakCompat P Pj) (hqj : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (fuel : Nat)
    (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))) (hf : nfFront σ te = some p)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    (hq : nfSrcProg σ te = some q)
    (hct : @NFCTRel nfDialect _ _ _ _ (nfDenote (tableOf bi)) nfLeakModel _ _
      (nfSrcLabels s (abiEntry σ)) fuel q.2)
    (V₁ V₂ : Valuation (entryCtx (abiEntry σ)))
    (hin₁ : ∀ (t : NfTy) (v : Var (entryCtx (abiEntry σ)) t), InRange t (v.lookup V₁))
    (hin₂ : ∀ (t : NfTy) (v : Var (entryCtx (abiEntry σ)) t), InRange t (v.lookup V₂))
    (hpub : PubEqV (nfSrcLabels s (abiEntry σ)) V₁ V₂)
    {r₁ r₂ : Valuation (d := nfDialect) [q.1] × List CTLeak}
    (h₁ : nfLeakRun bi fuel q.2 V₁ = some r₁) (h₂ : nfLeakRun bi fuel q.2 V₂ = some r₂) :
    ∃ m, RouteProgJ.ctLeak Pj fuel p.2 (ctMapValD (mapVal V₁)) = some m ∧
      RouteProgJ.ctLeak Pj fuel p.2 (ctMapValD (mapVal V₂)) = some m := by
  obtain ⟨q', rp, hq', hrp, rfl⟩ := nfFront_eq_some hf
  rw [hq, Option.some.injEq] at hq'
  subst hq'
  exact nfChain_ct hP hc hqj hbi fuel q.2 hrp V₁ V₂ hin₁ hin₂ h₁ h₂
    (hct V₁ V₂ r₁ r₂ hpub h₁ h₂)

/-- **Constant time from the level check of the source, through the chain**: the instance of
    `nfFront_routeCT_src` whose hypothesis on the source is the acceptance of
    `nfFrontSrcCT s σ te`. -/
theorem nfFront_routeCT_src_check {P : CatLeakParams} {Pj : JLeakParams} (hP : NoVT P)
    (hc : LeakCompat P Pj) (hqj : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (fuel : Nat)
    (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (hchk : nfFrontSrcCT s σ te = true)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))) (hf : nfFront σ te = some p)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    (hq : nfSrcProg σ te = some q)
    (V₁ V₂ : Valuation (entryCtx (abiEntry σ)))
    (hin₁ : ∀ (t : NfTy) (v : Var (entryCtx (abiEntry σ)) t), InRange t (v.lookup V₁))
    (hin₂ : ∀ (t : NfTy) (v : Var (entryCtx (abiEntry σ)) t), InRange t (v.lookup V₂))
    (hpub : PubEqV (nfSrcLabels s (abiEntry σ)) V₁ V₂)
    {r₁ r₂ : Valuation (d := nfDialect) [q.1] × List CTLeak}
    (h₁ : nfLeakRun bi fuel q.2 V₁ = some r₁) (h₂ : nfLeakRun bi fuel q.2 V₂ = some r₂) :
    ∃ m, RouteProgJ.ctLeak Pj fuel p.2 (ctMapValD (mapVal V₁)) = some m ∧
      RouteProgJ.ctLeak Pj fuel p.2 (ctMapValD (mapVal V₂)) = some m := by
  unfold nfFrontSrcCT at hchk
  rw [hq] at hchk
  exact nfFront_routeCT_src hP hc hqj hbi fuel s σ te p hf q hq
    (@NFProg.nfCTRel_of_levelCheck' nfDialect _ _ _ _ (nfDenote (tableOf bi))
      nfLeakModel fuel _ _ q.2 _ hchk) V₁ V₂ hin₁ hin₂ hpub h₁ h₂

/-- **Constant time of the optimised route program of the front**: the statement of
    `nfFront_routeCT` at `p.2.opt`, the program the back half compiles. -/
theorem nfFront_routeCT_opt {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (h : nfFrontLeakCT P s σ te = true)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))) (hf : nfFront σ te = some p) :
    ∀ fuel : Nat, RouteCTJ Pj (mapLabels (nfLabels s (abiEntry σ))) fuel p.2.opt :=
  fun fuel => RouteCTJ_opt hq _ fuel p.2 (nfFront_routeCT hc hq s σ te h p hf fuel)

/-- **Constant time of the optimised route program of the front through the chain on the
    owned route**: the instance of `nfFront_routeCT_opt` at the owned parameters. -/
theorem nfFront_routeCT_opt_owned (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (h : nfFrontLeakCT CatLeakParams.owned s σ te = true)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))) (hf : nfFront σ te = some p) :
    ∀ fuel : Nat, RouteCTJ JLeakParams.owned (mapLabels (nfLabels s (abiEntry σ))) fuel p.2.opt :=
  nfFront_routeCT_opt leakCompat_owned (fun _ _ => rfl) s σ te h p hf

/-- **Constant time from the source to the optimised route program of the front, relative
    to source runs**: the statement of `nfFront_routeCT_src` at `p.2.opt`. -/
theorem nfFront_routeCT_src_opt {P : CatLeakParams} {Pj : JLeakParams} (hP : NoVT P)
    (hc : LeakCompat P Pj) (hqj : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (fuel : Nat)
    (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t))) (hf : nfFront σ te = some p)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    (hq : nfSrcProg σ te = some q)
    (hct : @NFCTRel nfDialect _ _ _ _ (nfDenote (tableOf bi)) nfLeakModel _ _
      (nfSrcLabels s (abiEntry σ)) fuel q.2)
    (V₁ V₂ : Valuation (entryCtx (abiEntry σ)))
    (hin₁ : ∀ (t : NfTy) (v : Var (entryCtx (abiEntry σ)) t), InRange t (v.lookup V₁))
    (hin₂ : ∀ (t : NfTy) (v : Var (entryCtx (abiEntry σ)) t), InRange t (v.lookup V₂))
    (hpub : PubEqV (nfSrcLabels s (abiEntry σ)) V₁ V₂)
    {r₁ r₂ : Valuation (d := nfDialect) [q.1] × List CTLeak}
    (h₁ : nfLeakRun bi fuel q.2 V₁ = some r₁) (h₂ : nfLeakRun bi fuel q.2 V₂ = some r₂) :
    ∃ m, RouteProgJ.ctLeak Pj fuel p.2.opt (ctMapValD (mapVal V₁)) = some m ∧
      RouteProgJ.ctLeak Pj fuel p.2.opt (ctMapValD (mapVal V₂)) = some m :=
  RouteProgJ.opt_ctLeak_some hqj fuel p.2
    (nfFront_routeCT_src hP hc hqj hbi fuel s σ te p hf q hq hct V₁ V₂ hin₁ hin₂ hpub
      h₁ h₂)

/-! ## Constant time of `nfFrontC` -/

/-- **Constant time of the route program of `nfFrontC`**: `nfFront_routeCT` on the
    extraction with the constants of the layout bound. -/
theorem nfFrontC_routeCT {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (h : nfFrontLeakCT P s σ (bindConsts σ.consts te) = true)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t)))
    (hf : nfFrontC.front σ (te : CatCrypt.Crypto.Hax.HaxModule) = some ⟨nfCtx σ, _, p.2⟩) :
    ∀ fuel : Nat, RouteCTJ Pj (mapLabels (nfLabels s (abiEntry σ))) fuel p.2 := by
  obtain ⟨p', hp', he⟩ := nfFrontC_front_eq_some hf
  exact routeProgJ_transfer (fun _ r => ∀ fuel : Nat, RouteCTJ Pj _ fuel r) he
    (nfFront_routeCT hc hq s σ _ h p' hp')

/-- **Constant time of the route program of `nfFrontC` on the owned route.** -/
theorem nfFrontC_routeCT_owned (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (h : nfFrontLeakCT CatLeakParams.owned s σ (bindConsts σ.consts te) = true)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t)))
    (hf : nfFrontC.front σ (te : CatCrypt.Crypto.Hax.HaxModule) = some ⟨nfCtx σ, _, p.2⟩) :
    ∀ fuel : Nat, RouteCTJ JLeakParams.owned (mapLabels (nfLabels s (abiEntry σ))) fuel p.2 :=
  nfFrontC_routeCT leakCompat_owned (fun _ _ => rfl) s σ te h p hf

/-- **Constant time from the source to the route program of `nfFrontC`, relative to source
    runs**: `nfFront_routeCT_src` on the extraction with the constants of the layout
    bound. -/
theorem nfFrontC_routeCT_src {P : CatLeakParams} {Pj : JLeakParams} (hP : NoVT P)
    (hc : LeakCompat P Pj) (hqj : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (fuel : Nat)
    (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t)))
    (hf : nfFrontC.front σ (te : CatCrypt.Crypto.Hax.HaxModule) = some ⟨nfCtx σ, _, p.2⟩)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    (hq : nfSrcProg σ (bindConsts σ.consts te) = some q)
    (hct : @NFCTRel nfDialect _ _ _ _ (nfDenote (tableOf bi)) nfLeakModel _ _
      (nfSrcLabels s (abiEntry σ)) fuel q.2)
    (V₁ V₂ : Valuation (entryCtx (abiEntry σ)))
    (hin₁ : ∀ (t : NfTy) (v : Var (entryCtx (abiEntry σ)) t), InRange t (v.lookup V₁))
    (hin₂ : ∀ (t : NfTy) (v : Var (entryCtx (abiEntry σ)) t), InRange t (v.lookup V₂))
    (hpub : PubEqV (nfSrcLabels s (abiEntry σ)) V₁ V₂)
    {r₁ r₂ : Valuation (d := nfDialect) [q.1] × List CTLeak}
    (h₁ : nfLeakRun bi fuel q.2 V₁ = some r₁) (h₂ : nfLeakRun bi fuel q.2 V₂ = some r₂) :
    ∃ m, RouteProgJ.ctLeak Pj fuel p.2 (ctMapValD (mapVal V₁)) = some m ∧
      RouteProgJ.ctLeak Pj fuel p.2 (ctMapValD (mapVal V₂)) = some m := by
  obtain ⟨p', hp', he⟩ := nfFrontC_front_eq_some hf
  exact routeProgJ_transfer
    (fun _ r => ∃ m, RouteProgJ.ctLeak Pj fuel r (ctMapValD (mapVal V₁)) = some m ∧
      RouteProgJ.ctLeak Pj fuel r (ctMapValD (mapVal V₂)) = some m) he
    (nfFront_routeCT_src hP hc hqj hbi fuel s σ _ p' hp' q hq hct V₁ V₂ hin₁ hin₂ hpub
      h₁ h₂)

/-- **Constant time from the level check of the source, through `nfFrontC`.** -/
theorem nfFrontC_routeCT_src_check {P : CatLeakParams} {Pj : JLeakParams} (hP : NoVT P)
    (hc : LeakCompat P Pj) (hqj : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (fuel : Nat)
    (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (hchk : nfFrontSrcCT s σ (bindConsts σ.consts te) = true)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t)))
    (hf : nfFrontC.front σ (te : CatCrypt.Crypto.Hax.HaxModule) = some ⟨nfCtx σ, _, p.2⟩)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    (hq : nfSrcProg σ (bindConsts σ.consts te) = some q)
    (V₁ V₂ : Valuation (entryCtx (abiEntry σ)))
    (hin₁ : ∀ (t : NfTy) (v : Var (entryCtx (abiEntry σ)) t), InRange t (v.lookup V₁))
    (hin₂ : ∀ (t : NfTy) (v : Var (entryCtx (abiEntry σ)) t), InRange t (v.lookup V₂))
    (hpub : PubEqV (nfSrcLabels s (abiEntry σ)) V₁ V₂)
    {r₁ r₂ : Valuation (d := nfDialect) [q.1] × List CTLeak}
    (h₁ : nfLeakRun bi fuel q.2 V₁ = some r₁) (h₂ : nfLeakRun bi fuel q.2 V₂ = some r₂) :
    ∃ m, RouteProgJ.ctLeak Pj fuel p.2 (ctMapValD (mapVal V₁)) = some m ∧
      RouteProgJ.ctLeak Pj fuel p.2 (ctMapValD (mapVal V₂)) = some m := by
  obtain ⟨p', hp', he⟩ := nfFrontC_front_eq_some hf
  exact routeProgJ_transfer
    (fun _ r => ∃ m, RouteProgJ.ctLeak Pj fuel r (ctMapValD (mapVal V₁)) = some m ∧
      RouteProgJ.ctLeak Pj fuel r (ctMapValD (mapVal V₂)) = some m) he
    (nfFront_routeCT_src_check hP hc hqj hbi fuel s σ _ hchk p' hp' q hq V₁ V₂ hin₁ hin₂
      hpub h₁ h₂)

/-- **Constant time of the optimised route program of `nfFrontC`.** -/
theorem nfFrontC_routeCT_opt {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (h : nfFrontLeakCT P s σ (bindConsts σ.consts te) = true)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t)))
    (hf : nfFrontC.front σ (te : CatCrypt.Crypto.Hax.HaxModule) = some ⟨nfCtx σ, _, p.2⟩) :
    ∀ fuel : Nat, RouteCTJ Pj (mapLabels (nfLabels s (abiEntry σ))) fuel p.2.opt :=
  fun fuel => RouteCTJ_opt hq _ fuel p.2 (nfFrontC_routeCT hc hq s σ te h p hf fuel)

/-- **Constant time of the optimised route program of `nfFrontC` on the owned route.** -/
theorem nfFrontC_routeCT_opt_owned (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (h : nfFrontLeakCT CatLeakParams.owned s σ (bindConsts σ.consts te) = true)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t)))
    (hf : nfFrontC.front σ (te : CatCrypt.Crypto.Hax.HaxModule) = some ⟨nfCtx σ, _, p.2⟩) :
    ∀ fuel : Nat, RouteCTJ JLeakParams.owned (mapLabels (nfLabels s (abiEntry σ))) fuel p.2.opt :=
  nfFrontC_routeCT_opt leakCompat_owned (fun _ _ => rfl) s σ te h p hf

/-- **Constant time from the source to the optimised route program of `nfFrontC`, relative
    to source runs.** -/
theorem nfFrontC_routeCT_src_opt {P : CatLeakParams} {Pj : JLeakParams} (hP : NoVT P)
    (hc : LeakCompat P Pj) (hqj : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (fuel : Nat)
    (s : _root_.Hax.FnSecrecy) (σ : AbiLayout) (te : TExpr)
    (p : Σ t : NfTy, RouteProgJ (nfCtx σ) (mapTy (catTy t)))
    (hf : nfFrontC.front σ (te : CatCrypt.Crypto.Hax.HaxModule) = some ⟨nfCtx σ, _, p.2⟩)
    (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    (hq : nfSrcProg σ (bindConsts σ.consts te) = some q)
    (hct : @NFCTRel nfDialect _ _ _ _ (nfDenote (tableOf bi)) nfLeakModel _ _
      (nfSrcLabels s (abiEntry σ)) fuel q.2)
    (V₁ V₂ : Valuation (entryCtx (abiEntry σ)))
    (hin₁ : ∀ (t : NfTy) (v : Var (entryCtx (abiEntry σ)) t), InRange t (v.lookup V₁))
    (hin₂ : ∀ (t : NfTy) (v : Var (entryCtx (abiEntry σ)) t), InRange t (v.lookup V₂))
    (hpub : PubEqV (nfSrcLabels s (abiEntry σ)) V₁ V₂)
    {r₁ r₂ : Valuation (d := nfDialect) [q.1] × List CTLeak}
    (h₁ : nfLeakRun bi fuel q.2 V₁ = some r₁) (h₂ : nfLeakRun bi fuel q.2 V₂ = some r₂) :
    ∃ m, RouteProgJ.ctLeak Pj fuel p.2.opt (ctMapValD (mapVal V₁)) = some m ∧
      RouteProgJ.ctLeak Pj fuel p.2.opt (ctMapValD (mapVal V₂)) = some m :=
  RouteProgJ.opt_ctLeak_some hqj fuel p.2
    (nfFrontC_routeCT_src hP hc hqj hbi fuel s σ te p hf q hq hct V₁ V₂ hin₁ hin₂ hpub h₁ h₂)

end CatCrypt.Crypto.SecureCompilation.Haxc
