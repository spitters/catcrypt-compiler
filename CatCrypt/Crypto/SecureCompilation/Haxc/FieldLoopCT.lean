/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTStraight
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTStraight
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldLowerChainCT
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldBlocksCT

@[expose] public section

set_option autoImplicit false

/-!
# Constant time of the route program of a function over a prime field

`regionChain_bytes_ct` derives constant time of the decoded bytes that the region back half
`compileRegion` returns on a structured program from `NFCT` of that program at every fuel, a
statement over every pair of valuations that agree on the public positions. The chain
theorem `nfChainF_ct` relates two source runs to two runs of the compiled program from
valuations whose arrays hold Montgomery encodings (`JAgree`); an array whose limbs are not
below the modulus is the carrier of no field element, so `nfChainF_ct` does not give `NFCT`.

This module derives `NFCT` from the level check of the program of `jasminDialect` that
the field lowering `lowerF` returns inside the chain `nfChainF`: the check gives `NFCT` at
every valuation (`NFProg.nfCT_of_levelCheck`), `lowerSelects` keeps the events of the
branch-free program (`ifFree_lowerF`), and the e-graph pass at `jasminRules` keeps constant
time; the export keeps it on a route program. A counted loop
passes the check when its trip count is public. The check is a Boolean on an intermediate
program of the compiler, generic in the limb parameters.

## Main definitions

* `fieldFrontLeakCT`: the level check of the program `fieldLoweredFront` (in
  `Haxc/FieldLowerChain.lean`) for labels of the carrier context.

## Main results

* `nfChainF_routeCT_of_lowered`: `RouteCTJ` of the result of `nfChainF` from `NFCT` of the
  lowered program.
* `fieldChainFront_routeCT`: `RouteCTJ` of the result of `fieldChainFront` from
  `fieldFrontLeakCT`, at every fuel.
* `fieldRegionFront_nfCT`: `NFCT` of the result of `fieldRegionFront` from
  `fieldFrontLeakCT`, at every fuel.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.Hax.NFFieldSum (nfFieldDialect Kind SRen primeirFieldTable)
open CatCrypt.Hax.PrimeirNames (OpTable)
open CatCrypt.Crypto.Hax.ImpToNF (impToNF entryCtx entryEnv)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (aegraphOptNF aegraphOptNF_jasminRules_nfCT)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldCorrect (fieldSigOf)
open Ctxt (Var Valuation)
open _root_.Hax (ImpExpr)

variable {n : Nat} (P : LimbParams n)

/-- **Constant time through the chain from its lowered program.** When `nfChainF` returns
    `rp` for `prog` and the program `q'` that `lowerF` returns on the program `sumStep`
    returns on the pruned source is constant time for the labels `L` at the fuel `fuel`, the
    program `rp` is constant time for `L` at that fuel, under quiet register arithmetic of
    `jLeakModel Pj`. -/
theorem nfChainF_routeCT_of_lowered (T : OpTable) {Pj : JLeakParams}
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet) (fuel : Nat)
    {Γ : Ctxt nfDialect} {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    (σ : SRen P.p Γ Δ) (ρ : JRen n Δ Θ) (prog : NFProg nfDialect Γ [.int])
    {rp : RouteProgJ Θ (arrTy n)} (h : (nfChainF P T σ ρ).run prog = some rp)
    {q : NFProg nfFieldDialect Δ [.inr (.fp P.p)]}
    (hs : (sumStep P T σ).run (NFProg.dce prog) = some q)
    {q' : NFProg jasminDialect Θ [arrTy n]} (hl : lowerF P q ρ = some q')
    (L : Labels Θ) (hct : NFCT (jLeakModel Pj) L fuel q') : RouteCTJ Pj L fuel rp := by
  simp only [nfChainF, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨q0, h0, q1, h1, q2, h2, q3, h3, q4, h4, q5, h5, h6⟩ := h
  cases h0
  rw [hs, Option.some.injEq] at h1
  subst h1
  change lowerF P q ρ = some q2 at h2
  rw [hl, Option.some.injEq] at h2
  subst h2
  cases h3
  cases h4
  cases h6
  have hif := ifFree_lowerF P q ρ q' hl
  have c : NFCT (jLeakModel Pj) L fuel (NFProg.lowerSelects q') := by
    intro W₁ W₂ hW
    exact (congrArg (Option.map Prod.snd) (NFProg.leakRun_lowerSelects _ fuel q' hif W₁)).trans
      ((hct W₁ W₂ hW).trans
        (congrArg (Option.map Prod.snd) (NFProg.leakRun_lowerSelects _ fuel q' hif W₂)).symm)
  exact exportNFJ_routeCT Pj fuel _ h5 _ (aegraphOptNF_jasminRules_nfCT hq fuel _ _ c)

/-- **The level check of the lowered program of the front**: `fieldLoweredFront` returns a
    program that the level checker accepts at the leakage model `jLeakModel Pj` for the
    labels `L` of the carrier context. -/
def fieldFrontLeakCT (Pj : JLeakParams) (ps : List (String × NfTy))
    (ks : HVector (Kind P.p) (entryCtx ps))
    (L : Labels (d := jasminDialect) ((Hax.NFFieldSum.kTys ks).map (jTy n))) (e : ImpExpr) :
    Bool :=
  (fieldLoweredFront P ps ks e).any fun q => (NFProg.levelCheck (jLeakModel Pj) q L).isSome

/-- **Constant time of the program of the front through the chain.** When the level check
    `fieldFrontLeakCT` of the lowered program accepts for the labels `L`, the program
    `fieldChainFront` returns is constant time for `L` at every fuel, under quiet register
    arithmetic of `jLeakModel Pj`. The hypothesis is a check on an intermediate program of
    the compiler; the conclusion concerns the emitted program at every valuation. -/
theorem fieldChainFront_routeCT {Pj : JLeakParams}
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (ps : List (String × NfTy)) (ks : HVector (Kind P.p) (entryCtx ps))
    (L : Labels (d := jasminDialect) ((Hax.NFFieldSum.kTys ks).map (jTy n))) (e : ImpExpr)
    {rp : RouteProgJ ((Hax.NFFieldSum.kTys ks).map (jTy n)) (arrTy n)}
    (hf : fieldChainFront P ps ks e = some rp)
    (hchk : fieldFrontLeakCT P Pj ps ks L e = true) (fuel : Nat) : RouteCTJ Pj L fuel rp := by
  unfold fieldChainFront at hf
  unfold fieldFrontLeakCT fieldLoweredFront at hchk
  obtain ⟨o, ho, hf⟩ := Option.bind_eq_some_iff.mp hf
  rw [ho, Option.bind_some] at hchk
  split at hf
  · rename_i ht
    rw [dite_eq_left ht] at hchk
    rcases hs : (sumStep P primeirFieldTable (kindRen ks)).run (NFProg.dce (ht ▸ o.prog))
      with _ | q
    · rw [hs] at hchk
      cases hchk
    · rw [hs, Option.bind_some] at hchk
      rcases hl : lowerF P q (idRen n _) with _ | q'
      · rw [hl] at hchk
        cases hchk
      · rw [hl, Option.any_some] at hchk
        exact nfChainF_routeCT_of_lowered P primeirFieldTable hq fuel (kindRen ks) (idRen n _)
          _ hf hs hl L (NFProg.nfCT_of_levelCheck _ fuel q' L hchk)
  · cases hf

/-- **Constant time of the structured program of the chain.** When `fieldRegionFront`
    returns `p` and the level check `fieldFrontLeakCT` of the lowered program accepts for the
    labels `L`, the program `p` is constant time for `L` at every fuel, under quiet register
    arithmetic of `jLeakModel Pj`. -/
theorem fieldRegionFront_nfCT {Pj : JLeakParams}
    (hq : ∀ bop w, (jLeakModel Pj).kind (.regArith bop w) = .quiet)
    (ps : List (String × NfTy)) (ks : HVector (Kind P.p) (entryCtx ps))
    (L : Labels (d := jasminDialect) ((Hax.NFFieldSum.kTys ks).map (jTy n))) (e : ImpExpr)
    {p : NFProg jasminDialect ((Hax.NFFieldSum.kTys ks).map (jTy n)) [arrTy n]}
    (hp : fieldRegionFront P ps ks e = some p)
    (hchk : fieldFrontLeakCT P Pj ps ks L e = true) (fuel : Nat) :
    NFCT (jLeakModel Pj) L fuel p := by
  unfold fieldRegionFront at hp
  split at hp
  case isFalse => cases hp
  obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hp
  unfold fieldFrontLeakCT at hchk
  rw [hq', Option.any_some] at hchk
  unfold fieldLoweredFront at hq'
  obtain ⟨o, -, hq'⟩ := Option.bind_eq_some_iff.mp hq'
  split at hq'
  · obtain ⟨q, -, hl⟩ := Option.bind_eq_some_iff.mp hq'
    have hif := ifFree_lowerF P q _ q' hl
    have hct := NFProg.nfCT_of_levelCheck _ fuel q' L hchk
    have c : NFCT (jLeakModel Pj) L fuel (NFProg.lowerSelects q') := by
      intro W₁ W₂ hW
      exact (congrArg (Option.map Prod.snd)
        (NFProg.leakRun_lowerSelects _ fuel q' hif W₁)).trans
        ((hct W₁ W₂ hW).trans
          (congrArg (Option.map Prod.snd) (NFProg.leakRun_lowerSelects _ fuel q' hif W₂)).symm)
    exact aegraphOptNF_jasminRules_nfCT hq fuel _ _ c
  · cases hq'

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower
