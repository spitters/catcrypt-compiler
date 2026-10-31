/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldLowerChain
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldLowerLeak
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChainCT

/-!
# Constant time through the chain of a function over a prime field

`nfChainFCTCert` is a constant-time certificate (`PassChain.CTCert`) of the chain
`nfChainF`, with one leaf per step:

0. `dce` and 1. `nfToSum`: by the definition of the source leakage semantics;
2. `fieldLower`: `lowerF_leak2`, under the hypothesis `BlocksCT` on the blocks of the
   Montgomery template, with `ifFree_lowerF` for the branch-free target semantics;
3. `lowerSelects`, 4. `aegraph` at `jasminRules`, 5. `exportNFJ`: the leaves
   `lowerSelectsCTStep`, `aegraphCTStep` and `exportCTStep` of `nfChain`.

## The source leakage semantics

The events of a source program are measured on the program of `nfFieldDialect` that
`nfToSum` returns, at the model `nfFieldLeakModel` (`fieldSrcLeakSem`). A call of a field
entry of the name table is a field operation only when `nfToSum` finds its arguments
carried as field elements; a call of the same name on integers stays a leaf call of
`nfDialect`, with the class `nfKind` gives it. The class of a call is therefore fixed by
the carried kinds, which the name of the call does not determine, and `nfKind` is used
unchanged. Constant time of the source in this semantics follows from the level checker on
the program of `nfFieldDialect` (`fieldSrc_ct_of_levelCheck'`).

## The hypothesis on the blocks

`BlocksCT P Pj` (the events of each block of the template do not depend on the words of
its arrays) is a hypothesis of the certificate. It follows from the level check
`blocksCheck P Pj` of the seven blocks (`blocksCT_of_check`); the check is not proved here
for the limb parameters.

## Main definitions

* `sumLeakSem`, `fieldSrcLeakSem`, `fieldSrcLeakSemDce` — the leakage semantics of the
  programs of `nfFieldDialect` and of the source programs after and before `dce`.
* `dceCTStepF`, `sumCTStep`, `fieldLowerCTStep` — the leaves of the first three steps.
* `nfChainFCTCert` — the constant-time certificate of `nfChainF`.

## Main results

* `nfChainF_ct` — equal source events of two runs give two runs of the exported program
  with equal events.
* `fieldSrc_ct_of_levelCheck'` — the level checker on the program of `nfFieldDialect`
  gives equal source events.
* `nfChainF_ct_of_levelCheck'` — the exported program of a source the level checker
  accepts has equal events on valuations that agree on the public positions.
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
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Hax.NFFieldSum (nfFieldDialect nfFieldDenote nfFieldLeakModel
  nfFieldLeakRun nfField_nfCTRel_of_levelCheck' SRen)
open CatCrypt.Hax.PrimeirNames (OpTable)
open CatCrypt.Crypto.Hax.ImpToNF (tableOf)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules jasminRules_indep)
open Ctxt (Var Valuation)
open _root_.Hax (Builtins)

variable {n : Nat} (P : LimbParams n)

/-! ## 1. The leakage semantics -/

/-- The leakage semantics of programs of `nfFieldDialect` over the leaf table of the
    builtin table `bi`: the events of `nfFieldLeakRun`. -/
def sumLeakSem (bi : Builtins) (fuel : Nat) (Δ : Ctxt nfFieldDialect)
    (ts : List nfFieldDialect.Ty) : LeakSem (NFProg nfFieldDialect Δ ts) where
  In := Valuation Δ
  Ev := CTLeak
  leak p X := (nfFieldLeakRun bi fuel p X).map Prod.snd

/-- **The source leakage semantics of a function over the field**: the events of the
    program of `nfFieldDialect` that `sumStep P T σ` returns, from a valuation of its
    context; no run when the step refuses. -/
def fieldSrcLeakSem (T : OpTable) (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect}
    {Δ : Ctxt nfFieldDialect} (σ : SRen P.p Γ Δ) : LeakSem (NFProg nfDialect Γ [.int]) where
  In := Valuation Δ
  Ev := CTLeak
  leak p X := ((sumStep P T σ).run p).bind fun q => (sumLeakSem bi fuel Δ _).leak q X

/-- The source leakage semantics before `dce`: `fieldSrcLeakSem` on the pruned program. -/
def fieldSrcLeakSemDce (T : OpTable) (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect}
    {Δ : Ctxt nfFieldDialect} (σ : SRen P.p Γ Δ) : LeakSem (NFProg nfDialect Γ [.int]) where
  In := Valuation Δ
  Ev := CTLeak
  leak p X := (fieldSrcLeakSem P T bi fuel σ).leak (NFProg.dce p) X

/-! ## 2. The leaves of the first three steps -/

/-- The constant-time step certificate of `dce`: the source semantics before `dce` reads
    the pruned program. -/
def dceCTStepF (T : OpTable) (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect}
    {Δ : Ctxt nfFieldDialect} (σ : SRen P.p Γ Δ) :
    StepCert (dceStep Γ [.int]).run (fieldSrcLeakSemDce P T bi fuel σ).twoRun
      (fieldSrcLeakSem P T bi fuel σ).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q _ _ _ _ l₁ l₂} hf hV₁ hV₂ h₁ h₂ => by
    cases hf
    subst hV₁ hV₂
    exact ⟨l₁, l₂, h₁, h₂, _root_.id⟩

/-- The constant-time step certificate of `nfToSum`: the source semantics reads the
    program the step returns. -/
def sumCTStep (T : OpTable) (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect}
    {Δ : Ctxt nfFieldDialect} (σ : SRen P.p Γ Δ) :
    StepCert (sumStep P T σ).run (fieldSrcLeakSem P T bi fuel σ).twoRun
      (sumLeakSem bi fuel Δ [.inr (.fp P.p)]).twoRun :=
  stepCertOfLeak _ _ Eq fun {p q _ _ _ _ l₁ l₂} hf hV₁ hV₂ h₁ h₂ => by
    subst hV₁ hV₂
    simp only [fieldSrcLeakSem, hf] at h₁ h₂
    exact ⟨l₁, l₂, h₁, h₂, _root_.id⟩

/-- **The constant-time step certificate of the field lowering**, from `lowerF_leak2` under
    `BlocksCT`: the input relation is the agreement along `ρ`, and the target semantics is
    the branch-free one (`ifFree_lowerF`). -/
def fieldLowerCTStep {Pj : JLeakParams} (hn : n < 2 ^ 64) (hB : BlocksCT P Pj) (bi : Builtins)
    (fuel : Nat) {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    (ts : List nfFieldDialect.Ty) :
    StepCert (fieldLowerStep P ρ ts).run (sumLeakSem bi fuel Δ ts).twoRun
      (leakSemIfFree (jLeakModel Pj) fuel Θ (ts.map (jTy n))).twoRun :=
  stepCertOfLeak _ _ (fun X W => JAgree P ρ X W) fun {p q _ _ _ _ _ _} hf hA₁ hA₂ h₁ h₂ => by
    obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
    obtain ⟨s₁, s₂, k₁, k₂, -, -, he⟩ := lowerF_leak2 P Pj (tableOf bi) nfFieldLeakModel hn hB
      fuel fuel p ρ q hf hA₁ hA₂ hr₁ hr₂
    have hif := ifFree_lowerF P p ρ q hf
    exact ⟨s₁.2, s₂.2, by simp only [leakSemIfFree, hif, ite_true, k₁, Option.map_some],
      by simp only [leakSemIfFree, hif, ite_true, k₂, Option.map_some], he⟩

/-! ## 3. The certificate of the chain -/

/-- **The constant-time certificate of `nfChainF`**, at leakage parameters `Pj` of
    `jasminDialect` with quiet register arithmetic and blocks whose events do not depend on
    the valuation (`BlocksCT`), the builtin table `bi` and the fuel `fuel`: one leaf per
    step. -/
def nfChainFCTCert (T : OpTable) {Pj : JLeakParams} (hn : n < 2 ^ 64) (hB : BlocksCT P Pj)
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet) (bi : Builtins)
    (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ) :
    CTCert (nfChainF P T σ ρ) (fieldSrcLeakSemDce P T bi fuel σ)
      (routeLeakSem Pj fuel Θ (arrTy n)) :=
  .cons (dceCTStepF P T bi fuel σ) (fun _ _ h => h) <|
    .cons (sumCTStep P T bi fuel σ) (fun _ _ h => h) <|
    .cons (fieldLowerCTStep P hn hB bi fuel ρ [.inr (.fp P.p)]) (fun _ _ h => h) <|
    .cons (lowerSelectsCTStep Pj fuel Θ [arrTy n]) (fun _ _ h => h) <|
    .cons (aegraphCTStep jasminRules (jasminRules_indep hq) fuel Θ [arrTy n])
      (fun _ _ h => h) <|
    .cons (exportCTStep Pj fuel Θ (arrTy n)) (fun _ _ h => h) <| .nil _

/-- **Constant time through the chain of a function over the field.** Two source runs at
    the fuel `fuel` from valuations `X₁`, `X₂` related along `ρ` to `W₁`, `W₂`, with equal
    events, give two runs of the program `nfChainF` returns from `W₁`, `W₂` at the same
    fuel with equal events; this is `PassChain.CTCert.ct` at `nfChainFCTCert`. -/
theorem nfChainF_ct (T : OpTable) {Pj : JLeakParams} (hn : n < 2 ^ 64) (hB : BlocksCT P Pj)
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet) (bi : Builtins)
    (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ) (prog : NFProg nfDialect Γ [.int])
    {rp : RouteProgJ Θ (arrTy n)} (h : (nfChainF P T σ ρ).run prog = some rp)
    {X₁ X₂ : Valuation Δ} {W₁ W₂ : Valuation Θ} (hA₁ : JAgree P ρ X₁ W₁)
    (hA₂ : JAgree P ρ X₂ W₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce P T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce P T bi fuel σ).leak prog X₂ = some l₂) (he : l₁ = l₂) :
    ∃ m, RouteProgJ.ctLeak Pj fuel rp W₁ = some m ∧ RouteProgJ.ctLeak Pj fuel rp W₂ = some m := by
  obtain ⟨m₁, m₂, hm₁, hm₂, hm⟩ := (nfChainFCTCert P T hn hB hq bi fuel σ ρ).ct
    (W₁ := W₁) (W₂ := W₂) h
    ⟨(X₁, X₂), ⟨rfl, rfl⟩, (X₁, X₂), ⟨rfl, rfl⟩, (W₁, W₂), ⟨hA₁, hA₂⟩, (W₁, W₂), ⟨rfl, rfl⟩,
      (W₁, W₂), ⟨rfl, rfl⟩, (W₁, W₂), ⟨rfl, rfl⟩, rfl⟩ h₁ h₂ he
  exact ⟨m₁, hm₁, hm ▸ hm₂⟩

/-! ## 4. The source hypothesis from the level checker -/

/-- **The level checker gives equal source events.** If the program `q` of `nfFieldDialect`
    that `sumStep` returns on the pruned source passes the level checker at
    `nfFieldLeakModel` for the labels `L`, two source runs from valuations that agree on the
    public positions have equal events. -/
theorem fieldSrc_ct_of_levelCheck' (T : OpTable) (bi : Builtins) (fuel : Nat)
    {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} (σ : SRen P.p Γ Δ)
    (prog : NFProg nfDialect Γ [.int]) {q : NFProg nfFieldDialect Δ [.inr (.fp P.p)]}
    (hq : (sumStep P T σ).run (NFProg.dce prog) = some q) (L : Labels Δ)
    (hL : (NFProg.levelCheck' nfFieldLeakModel q L).isSome) {X₁ X₂ : Valuation Δ}
    (hp : PubEqV L X₁ X₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce P T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce P T bi fuel σ).leak prog X₂ = some l₂) : l₁ = l₂ := by
  simp only [fieldSrcLeakSemDce, fieldSrcLeakSem, hq, Option.bind_some, sumLeakSem] at h₁ h₂
  obtain ⟨r₁, hr₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
  obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
  exact nfField_nfCTRel_of_levelCheck' (tableOf bi) fuel q L hL X₁ X₂ r₁ r₂ hp hr₁ hr₂

/-- **Constant time of the exported program from the level checker.** For a source whose
    program of `nfFieldDialect` passes the level checker for the labels `L`, two source runs
    from valuations that agree on the public positions give two runs of the exported
    program with equal events. -/
theorem nfChainF_ct_of_levelCheck' (T : OpTable) {Pj : JLeakParams} (hn : n < 2 ^ 64)
    (hB : BlocksCT P Pj) (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect}
    {Θ : Ctxt jasminDialect} (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ)
    (prog : NFProg nfDialect Γ [.int]) {rp : RouteProgJ Θ (arrTy n)}
    (h : (nfChainF P T σ ρ).run prog = some rp)
    {q : NFProg nfFieldDialect Δ [.inr (.fp P.p)]}
    (hs : (sumStep P T σ).run (NFProg.dce prog) = some q) (L : Labels Δ)
    (hL : (NFProg.levelCheck' nfFieldLeakModel q L).isSome) {X₁ X₂ : Valuation Δ}
    {W₁ W₂ : Valuation Θ} (hA₁ : JAgree P ρ X₁ W₁) (hA₂ : JAgree P ρ X₂ W₂)
    (hp : PubEqV L X₁ X₂) {l₁ l₂ : List CTLeak}
    (h₁ : (fieldSrcLeakSemDce P T bi fuel σ).leak prog X₁ = some l₁)
    (h₂ : (fieldSrcLeakSemDce P T bi fuel σ).leak prog X₂ = some l₂) :
    ∃ m, RouteProgJ.ctLeak Pj fuel rp W₁ = some m ∧ RouteProgJ.ctLeak Pj fuel rp W₂ = some m :=
  nfChainF_ct P T hn hB hq bi fuel σ ρ prog h hA₁ hA₂ h₁ h₂
    (fieldSrc_ct_of_levelCheck' P T bi fuel σ prog hs L hL hp h₁ h₂)

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower
