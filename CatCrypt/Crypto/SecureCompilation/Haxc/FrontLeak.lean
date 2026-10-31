/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFFront
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower

/-!
# The leakage of the route program and constant time through the direct front

The leakage of a route program `RouteProg` at the leakage model `jLeakModel Pj` of
`jasminDialect`: the events `Com.ctLeak` of a straight-line program and `ComL.ctLeak` of a
looped program. `RouteCT Pj L rp` is constant time of the route program for the entry
labels `L`.

The intermediate program of the direct front is the program of `NFProg catCryptDialect` the
chain `nfChain` reaches after its translation step: the body of `te` translated by
`ImpToNF.impToNF`, pruned by `NFProg.dce` and translated by `NFToCat.nfToCat` (`nfCatProg`).

`nfFrontLeakCT P s σ te` runs the level checker `NFProg.levelCheck` on that intermediate
program from the labels `nfLabels s (abiEntry σ)` of the parameters in the secrecy record `s`.
What an accepted check establishes for the route program `nfFront σ te` is
`NFChainCT.nfFront_routeCT`.

## Main definitions

* `RouteProg.ctLeak`, `RouteCT` — the leakage of a route program and its constant time.
* `RouteProgJ.leakRun`, `RouteProgJ.ctLeak`, `RouteCTJ` — the leakage run of a `RouteProgJ`
  program at a fuel, its events, and its constant time at a fuel; on a structured program
  the events are those of `NFProg.leakRun` and constant time is `NFCT`
  (`routeCTJ_regions_iff`).
* `nfCatProg` — the intermediate program of `NFProg catCryptDialect` of the direct front.
* `nfFrontLeakCT` — the level check of that program from a secrecy record.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (ComL)
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak (CatLeakParams catLeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnv impToNF hax64SigOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open _root_.Hax (TExpr)

/-! ## The leakage of a route program -/

/-- The events of the run of a route program from a valuation: `ComL.ctLeak` of its
    program. -/
def RouteProg.ctLeak (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : RouteProg Γ t) (V : Ctxt.Valuation Γ) : List CTLeak :=
  ComL.ctLeak (jLeakModel Pj) p.com V

/-- The events of a straight-line program are `Com.ctLeak`. -/
theorem RouteProg.ctLeak_straight (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    RouteProg.ctLeak Pj (.straight c) V = Com.ctLeak (jLeakModel Pj) c V :=
  ctLeak_comToComL (jLeakModel Pj) c V

/-- The events of the route program of a `ComL` program are `ComL.ctLeak`. -/
theorem RouteProg.ctLeak_loop (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (V : Ctxt.Valuation Γ) :
    RouteProg.ctLeak Pj (.loop c) V = ComL.ctLeak (jLeakModel Pj) c V := rfl

/-- Constant time of a route program for the entry labels `L`: valuations that agree on the
    positions `L` marks public give equal leakage. -/
def RouteCT (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {t : JasminTy} (L : Labels Γ)
    (rp : RouteProg Γ t) : Prop :=
  ConstantTime (PubEqV L) (RouteProg.ctLeak Pj rp)

section RouteJ

/-- The run of a `RouteProgJ` program from a valuation at the fuel `fuel`, with the list of
    its events: `some` of the denotation and `RouteProg.ctLeak` for a route program, and
    `NFProg.leakRun` with the one result of its valuation for a structured program; `none`
    when a do-while runs out of fuel. -/
def RouteProgJ.leakRun (Pj : JLeakParams) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} : RouteProgJ Γ t → Ctxt.Valuation Γ → Option (⟦t⟧ × List CTLeak)
  | .straightLoop rp, V => some (rp.denote V, RouteProg.ctLeak Pj rp V)
  | .regions p, V => (NFProg.leakRun (jLeakModel Pj) fuel p V).map fun r => (oneResult r.1, r.2)

/-- The events of the run of a `RouteProgJ` program at the fuel `fuel`, or `none` when a
    do-while runs out of fuel. -/
def RouteProgJ.ctLeak (Pj : JLeakParams) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (rp : RouteProgJ Γ t) (V : Ctxt.Valuation Γ) : Option (List CTLeak) :=
  (RouteProgJ.leakRun Pj fuel rp V).map Prod.snd

/-- Constant time of a `RouteProgJ` program at the fuel `fuel` for the entry labels `L`:
    valuations that agree on the positions `L` marks public give the same events. -/
def RouteCTJ (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {t : JasminTy} (L : Labels Γ)
    (fuel : Nat) (rp : RouteProgJ Γ t) : Prop :=
  ∀ W₁ W₂ : Ctxt.Valuation Γ, PubEqV L W₁ W₂ →
    RouteProgJ.ctLeak Pj fuel rp W₁ = RouteProgJ.ctLeak Pj fuel rp W₂

/-- The result of the leakage run of a `RouteProgJ` program is its denotation. -/
theorem RouteProgJ.leakRun_fst (Pj : JLeakParams) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (rp : RouteProgJ Γ t) (V : Ctxt.Valuation Γ) :
    (RouteProgJ.leakRun Pj fuel rp V).map Prod.fst = rp.denoteF fuel V := by
  cases rp with
  | straightLoop rp => rfl
  | regions p =>
      have h : (NFProg.leakRun (jLeakModel Pj) fuel p V).map Prod.fst = p.denote fuel V :=
        NFProg.leakRun_fst (jLeakModel Pj) fuel p V
      simp only [RouteProgJ.leakRun, RouteProgJ.denoteF, ← h, Option.map_map]
      rfl

/-- A structured program emits the events of `NFProg.leakRun`, at every fuel. -/
@[simp] theorem RouteProgJ.ctLeak_regions (Pj : JLeakParams) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t])
    (V : Ctxt.Valuation Γ) :
    RouteProgJ.ctLeak Pj fuel (.regions p) V =
      (NFProg.leakRun (jLeakModel Pj) fuel p V).map Prod.snd := by
  simp only [RouteProgJ.ctLeak, RouteProgJ.leakRun, Option.map_map]
  rfl

/-- On a structured program, `RouteCTJ` at a fuel is constant time `NFCT` of the program at
    that fuel. -/
theorem routeCTJ_regions_iff (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (L : Labels Γ) (fuel : Nat) (p : NFProg jasminDialect Γ [t]) :
    RouteCTJ Pj L fuel (.regions p) ↔ NFCT (jLeakModel Pj) L fuel p := by
  simp only [RouteCTJ, NFCT, RouteProgJ.ctLeak_regions]

/-- A route program emits `RouteProg.ctLeak`, at every fuel. -/
@[simp] theorem RouteProgJ.ctLeak_straightLoop (Pj : JLeakParams) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (rp : RouteProg Γ t) (V : Ctxt.Valuation Γ) :
    RouteProgJ.ctLeak Pj fuel (.straightLoop rp) V = some (RouteProg.ctLeak Pj rp V) := rfl

/-- On a route program, `RouteCTJ` at any fuel is `RouteCT`. -/
theorem routeCTJ_straightLoop_iff (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (L : Labels Γ) (fuel : Nat) (rp : RouteProg Γ t) :
    RouteCTJ Pj L fuel (.straightLoop rp) ↔ RouteCT Pj L rp :=
  ⟨fun h W₁ W₂ hW => Option.some.inj (h W₁ W₂ hW),
    fun h W₁ W₂ hW => congrArg some (h W₁ W₂ hW)⟩

end RouteJ

/-! ## The level check of the direct front -/

/-- The program of `NFProg catCryptDialect` the direct front lowers to a route program: the
    body of `te` translated by `impToNF` from the parameters `abiEntry σ`, pruned by
    `NFProg.dce`, and translated by `nfToCat`. -/
def nfCatProg (σ : AbiLayout) (te : TExpr) :
    Option (Σ t : NfTy,
      NFProg catCryptDialect ((entryCtx (abiEntry σ)).map catTy) [catTy t]) :=
  if CatCrypt.Crypto.Hax.haxFrontShapeOk te = true then
    (impToNF hax64SigOf none (entryEnv (abiEntry σ)) (nfBody te)).bind fun o =>
      (nfToCat (NFProg.dce o.prog) TRd.id).map fun p' => ⟨o.t, p'⟩
  else none

/-- **The level check of the direct front with loops**: the program `nfCatProg σ te`,
    checked by `NFProg.levelCheck` at the leakage of `catCryptDialect` from the labels of the
    parameters in the secrecy record `s`. -/
def nfFrontLeakCT (P : CatLeakParams) (s : _root_.Hax.FnSecrecy) (σ : AbiLayout)
    (te : TExpr) : Bool :=
  match nfCatProg σ te with
  | some p => (NFProg.levelCheck (catLeakModel P) p.2 (nfLabels s (abiEntry σ))).isSome
  | none => false

end CatCrypt.Crypto.SecureCompilation.Haxc
