/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ExportNF
public import CatCrypt.Crypto.SecureCompilation.Haxc.FrontLeak
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat
public import CatCrypt.Crypto.Optimizer.Rewrite.Aegraph
public import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.NFIfToSelect

/-!
# The linear route from `NFProg nfDialect` to a route program

`nfToRouteProgVia p` lowers a program `p` of `NFProg nfDialect` with one result to the route
program `RouteProg` through the structured programs of each dialect:

1. `NFToCat.nfToCat` from the readings `TRd.id`, to `NFProg catCryptDialect`;
2. the e-graph pass `aegraphOptNF` at the catCrypt rule set `catRules`;
3. `NFProg.map?` along the partial block lowering `catToJasmin`, to `NFProg jasminDialect`;
4. the lowering of branches to selects `NFProg.lowerSelects`;
5. the e-graph pass `aegraphOptNF` at the jasmin rule set `jasminRules`;
6. the export `exportNF` to `RouteProg`.

Stages 2 to 6 form `catToRouteVia`, a function of the program of `NFProg catCryptDialect`.
The front `nfFront` runs the chain `NFChain.nfChain`: these stages with the step `range`
(`RangeNF.rangeNF`) between stages 4 and 5, and with the last step `exportNFJ` (the export
`exportNF` tried first, then the region export). `nfChain_run` states the chain as
its stages after `NFProg.dce` under the check of the result type, and
`nfChain_run_of_exportNF` relates a result of `exportNF` to a result of the chain.

## Main definitions

* `catToRouteVia` — stages 2 to 6 on a program of `NFProg catCryptDialect`.
* `nfToRouteProgVia` — the linear route.

## Main results

* `catToRouteVia_denote` — stages 2 to 6 preserve the denotation up to `ctTransTy`.
* `nfToRouteProgVia_denote`, `nfToRouteProgVia_entry` — the linear route simulates the
  source program, and gives the input of the back half.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes catToJasmin_map?_denote)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (aegraphOptNF aegraphOptNF_denote)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (enc PDenP entryCtx EntryVals entryEnv impToNF hax64SigOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open Ctxt (Var Valuation)
open _root_.Hax (TExpr)

/-! ## The stages after `nfToCat` -/

/-- **Stages 2 to 6 of the linear route** on a program of `NFProg catCryptDialect` with one
    result: the e-graph pass at `catRules`, `map?` along `catToJasmin` at the identity
    renaming, the select lowering, the e-graph pass at `jasminRules`, and `exportNF`. -/
def catToRouteVia {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (p : NFProg catCryptDialect Γ [t]) : Option (RouteProg (mapCtx Γ) (mapTy t)) :=
  (NFProg.map? catToJasmin catToJasmin_regionTypes (aegraphOptNF catRules p)
      (fun v => v)).bind fun q =>
    exportNF (aegraphOptNF jasminRules (NFProg.lowerSelects q))

/-- **Preservation through stages 2 to 6.** When `catToRouteVia p = some rp`, the source
    program denotes `some` of one value `x` at every fuel, and `rp` on the transported
    valuation denotes `ctTransTy x`. -/
theorem catToRouteVia_denote {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (p : NFProg catCryptDialect Γ [t]) {rp : RouteProg (mapCtx Γ) (mapTy t)}
    (h : catToRouteVia p = some rp) (fuel : Nat) (V : Valuation Γ) :
    ∃ x : CryptoTy.denote t, p.denote fuel V = some (.cons x .nil) ∧
      rp.denote (ctMapValD V) = ctTransTy x := by
  obtain ⟨q, hq, he⟩ := Option.bind_eq_some_iff.mp h
  have h1 := exportNF_denote _ he fuel (ctMapValD V)
  rw [aegraphOptNF_denote jasminRules] at h1
  have h1' := (NFProg.denote_lowerSelects fuel q (ctMapValD V)).symm.trans h1
  have h2 := catToJasmin_map?_denote fuel (aegraphOptNF catRules p) (fun v => v) V
    (ctMapValD V) (FieldDialectBlockDescent.pullV_id _) q hq
  rw [aegraphOptNF_denote catRules] at h2
  have h3 := h1'.symm.trans h2
  rcases hp : p.denote fuel V with _ | r
  · rw [hp] at h3
    cases h3
  · rcases r with _ | ⟨x, _ | _⟩
    rw [hp] at h3
    exact ⟨x, rfl, (HVector.cons.inj (Option.some.inj h3)).1⟩

/-! ## The linear route -/

/-- **The linear route** of a program of `NFProg nfDialect` with one result: its translation
    to `catCryptDialect` by `nfToCat` from the readings `TRd.id`, followed by
    `catToRouteVia`. -/
def nfToRouteProgVia {Γ : Ctxt nfDialect} {t : NfTy} (p : NFProg nfDialect Γ [t]) :
    Option (RouteProg (mapCtx (Γ.map catTy)) (mapTy (catTy t))) :=
  (nfToCat p TRd.id).bind catToRouteVia

/-- **The linear route simulates the source program.** When `nfToRouteProgVia p = some rp`
    under a leaf table agreeing with the `u64` table at the translated calls (`SubTable`), a
    source run of `p` from a valuation `V` in range to the value `y` of a result type is
    matched by the route program on the mapped valuation: its source value is the encoding
    of `y`. -/
theorem nfToRouteProgVia_denote {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (tf : Nat)
    {Γ : Ctxt nfDialect} {t : NfTy} (ht : OutTy t) (p : NFProg nfDialect Γ [t])
    {rp : RouteProg (mapCtx (Γ.map catTy)) (mapTy (catTy t))}
    (h : nfToRouteProgVia p = some rp) (V : Valuation Γ)
    (hin : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V)) {y : t.denote}
    (hp : PDenP bi tf p V = some (HVector.cons y .nil)) :
    denVal (mapTy (catTy t)) (rp.denote (ctMapValD (mapVal V))) = enc t y := by
  obtain ⟨p', hp', hrp⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨out', hden, hrel⟩ := nfToCat_sound hbi tf p TRd.id p' hp' V (mapVal V)
    (.cons y .nil) (TRd.agree_id V hin) hp 0
  rcases out' with _ | ⟨x, _ | _⟩
  have hx : VRel t y x := hrel.1
  obtain ⟨x', hx', hj⟩ := catToRouteVia_denote p' hrp 0 (mapVal V)
  rw [hden, Option.some.injEq] at hx'
  obtain rfl : x = x' := (HVector.cons.inj hx').1
  rw [hj]
  exact denVal_ctTransTy t ht y x hx

/-- **The input of the back half through the linear route.** For a source run of `p` from a
    valuation of the entry parameters whose encodings an environment the layout `σ` reads off
    `sa` holds, the route program on the mapped valuation satisfies two conditions: the
    valuation is the one `σ` reads off `sa` (`AbiValOf`), and the source value of its
    denotation is the encoding of the value of the source run. -/
theorem nfToRouteProgVia_entry {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (tf : Nat)
    {σ : AbiLayout} {sa : Ascent.AddrMem.AState} {env : _root_.Hax.Env}
    (hσ : σ.EnvOf sa env) {t : NfTy} (ht : OutTy t)
    (p : NFProg nfDialect (entryCtx (abiEntry σ)) [t])
    {rp : RouteProg (mapCtx ((entryCtx (abiEntry σ)).map catTy)) (mapTy (catTy t))}
    (h : nfToRouteProgVia p = some rp) (V : Valuation (entryCtx (abiEntry σ)))
    (hV : EntryVals env (abiEntry σ) V) {y : t.denote}
    (hp : PDenP bi tf p V = some (HVector.cons y .nil)) :
    X86Backend.ExportCertEntry.AbiValOf σ sa (ctMapValD (mapVal V)) ∧
      denVal (mapTy (catTy t)) (rp.denote (ctMapValD (mapVal V))) = enc t y :=
  ⟨abiValOf_mapVal hσ V hV,
    nfToRouteProgVia_denote hbi tf ht p h V (inRange_entry hσ V hV) hp⟩

end CatCrypt.Crypto.SecureCompilation.Haxc
