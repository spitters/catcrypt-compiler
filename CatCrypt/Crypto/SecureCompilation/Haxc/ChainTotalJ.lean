/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal
public import CatCrypt.Crypto.SecureCompilation.Haxc.CallsAll
public import CatCrypt.Crypto.Hax.NFToCatComplete
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectRegionCategory

/-!
# Completeness of the steps of `extChain` after the translation

The conversion `mapStep catToJasmin` returns a program on every `Convertible` program of
`catCryptDialect` (`catToJasmin_isSome_of_Dom`). The domain `fieldDomB` defined here is the
domain on which the field step of the chain, `FieldDialectStep.fieldDialectStep`, is complete
(`FieldDialectStep.fieldDialectStep_completeOn`). The inlining step `fieldInlineStep` returns
a program on every program of `jasminDialect` whose `call` nodes have a head that is no field
head (`Hax.FieldTag.fieldHeadB`, a canonical or a Montgomery head) or a head with a template
body `fieldBody` at the signature of the call (`fieldInlineDomB`, `fieldInline_isSome_of_Dom`): the
library `fieldLibJ` has no operation bodies, the splice of a body at the renamings of a call
is defined (`NFProg.seq?_isSome_of_total`), and every template body has no `call`, so the
inlined program calls no field head.

The steps `extChainCore D Γ t` after tuple flattening run to `some` on every program `p` at
a result type that passes `outTyB` whose dead-code-eliminated form satisfies `NB`
(`extChainCore_completeOn_NB`): `nfToCat`
is defined on `NB` (`nfToCat_isSome_of_NB`) and returns a program without `call`, which the
translation with declarations returns as well, and every later step is complete on the
programs without `call`. The chain `extChain D Γ t` runs to `some` on every program whose
flattening `flatSameStep` returns such a program (`extChain_isSome_of_NB`).

The chain runs to `some` as well on every program whose flattening has a dead-code-eliminated
form that satisfies `NBD` at its declarations `fieldDeclsFor D` and has a template for every
tagged call (`extChain_isSome_of_NBD`). The predicate `callsAll C` (every `call` node satisfies `C`
at its symbol and signature) is kept by the e-graph traversal, by inlining at a library
whose bodies pass it, and by the montify pass when `C` holds at the reduce-multiply heads;
the conversion `map?` carries it from the signatures in `catCryptDialect` to their images
in `jasminDialect`. Every call of the translation is a declaration of `fieldDeclsFor D`
(`nfToCatExt_calls`): an untagged declaration of `D`, or a declaration of a field head with a
template body or of a narrow Montgomery head, so the program the montify pass returns is in
the domain `fieldDomB` of the field dialect step.

This module holds the domains and the completeness of the steps; the completeness theorems
of `extChainCore` and `extChain` on these domains are in `Haxc/ExtChain.lean`.

## Main definitions

* `fieldDomB` — every `call` node has a head that is no field head, a head with a template
  body, or a narrow Montgomery head (`fieldCallMontB`).
* `fieldInlineDomB` — every `call` node has a head that is no field head or a head with a
  template body.
* `extDomNB` — the programs at a result type that passes `outTyB` whose `dce` image
  satisfies `NB`.
* `fieldCallB`, `fieldTemplB`, `fieldTemplsB` — a call in the domain of the field dialect
  step; a declaration whose head has a template body, or is a narrow Montgomery head, at the
  image of its signature; every declaration of `fieldDeclsOf` is one.
* `extDomNBD` — the programs at a result type that passes `outTyB` whose `dce` image
  satisfies `NBD` at its declarations and `fieldTemplsB`.

## Main results

* `PRen.total_ofArgs` — the renaming of a call's parameters to its arguments is total.
* `fieldFree_rename?`, `fieldFree_seq?` — renaming keeps `fieldFree`, and the splice of two
  programs that pass `fieldFree` passes it.
* `fieldBody_callFree` — a template body has no `call`.
* `inline?_fieldLibJ_of_Dom` — the inlining at `fieldLibJ` is defined on `fieldInlineDomB`
  and its result passes `fieldFree`.
* `fieldInlineStep_completeOn`, `fieldInline_isSome_of_Dom` — the inlining step is complete
  on `fieldInlineDomB`.
* `catToJasmin_completeOn`, `catToJasmin_isSome_of_Dom` — the conversion is complete on the
  `Convertible` programs and keeps the absence of `call`.
* `extCallStep_completeOn_NB` — the translation with declarations is complete on `NB`.
* `callsAll_inline?`, `callsAll_nfGo`, `callsAll_montifyPass` — the passes
  keep or transport `callsAll`.
* `fieldDomB_eq_callsAll`, `montifyStep_completeOn` — `fieldDomB` is `callsAll fieldCallB`,
  and the montify step keeps it.
* `extCallStep_completeOn_NBD` — the translation with declarations is complete on `NBD`.
* `narrowFoldsOf_isSome` — the fold template exists exactly at the moduli
  `ImpToNF.fieldNarrowOk` accepts.
* `fieldTemplB_of_fieldModOk`, `fieldTemplsB_of_fieldModOk` — a tagged declaration at a
  modulus that passes `ImpToNF.fieldModOk` has a template, so a program whose tagged calls
  are at such moduli passes `fieldTemplsB`.
* `fieldTemplB_mont` — a declaration of a narrow Montgomery head has a template.
-/

@[expose] public section

set_option autoImplicit false

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
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (aegraphOptNF)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.NFToCatImages (Convertible OpsHaveImages
  isSome_map?_catToJasmin_iff aegraphOptNF_catRules_opsHaveImages)
open CatCrypt.Crypto.Hax.NFToCatComplete (NB nfToCat_isSome_of_NB NBD nfToCatExt_isSome_of_NBD)
open _root_.Hax.FieldTag (fieldTag? fieldHeadB)
open Ctxt (Var Valuation)

/-! ## Renaming and the splice keep `fieldFree` -/

section Generic

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

omit [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] in
/-- The renaming of the parameters of a call to its arguments keeps every variable. -/
theorem PRen.total_ofArgs {Γ : Ctxt d} :
    {as : List d.Ty} → (args : HVector (fun t => Var Γ t) as) → PRen.Total (PRen.ofArgs args)
  | [], .nil => fun v => nomatch v
  | _ :: _, .cons _ ws => fun v => by
      cases v with
      | here => rfl
      | there v => exact PRen.total_ofArgs ws v

/-- A renamed program passes `fieldFree` exactly when the source does. -/
theorem fieldFree_rename? {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} {f : PRen Γ Δ} {q : NFProg d Δ ts}, NFProg.rename? f p = some q →
      fieldFree q = fieldFree p := by
  induction p with
  | ret vs =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.map_eq_some_iff] at h
      obtain ⟨_, -, rfl⟩ := h
      rfl
  | var e k ih =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, k', hk, rfl⟩ := h
      simp only [fieldFree, ih hk]
  | forLoop count inits body k ihb ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, _, -, b', hb, k', hk, rfl⟩ := h
      simp only [fieldFree, ihb hb, ihk hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, t', ht, e', he, k', hk, rfl⟩ := h
      simp only [fieldFree, iht ht, ihe he, ihk hk]
  | whileLoop inits body k ihb ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb, k', hk, rfl⟩ := h
      simp only [fieldFree, ihb hb, ihk hk]
  | call g args k ih =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, k', hk, rfl⟩ := h
      simp only [fieldFree, ih hk]

/-- The splice of a body and a continuation that pass `fieldFree` passes `fieldFree`. -/
theorem fieldFree_seq? {Δ : Ctxt d} {rs : List d.Ty} (b : NFProg d Δ rs) :
    ∀ {Γ₀ : Ctxt d} {ts : List d.Ty} (k : NFProg d (rs ++ Γ₀) ts) {Γ : Ctxt d}
      {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ} {q : NFProg d Γ ts}, NFProg.seq? k b ρ θ = some q →
      fieldFree b = true → fieldFree k = true → fieldFree q = true := by
  induction b with
  | ret vs =>
      intro Γ₀ ts k Γ ρ θ q h _ hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff] at h
      obtain ⟨_, -, h⟩ := h
      rw [fieldFree_rename? k h, hk]
  | var e b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb', rfl⟩ := h
      have h' := ih k hb' hb hk
      exact h'
  | forLoop count inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [fieldFree, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, _, -, body', hbody, b', hb', rfl⟩ := h
      simp only [fieldFree, fieldFree_rename? body hbody, hb.1, ih k hb' hb.2 hk,
        Bool.and_self]
  | ifThenElse cond thn els b _ _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [fieldFree, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, t', ht, e', he, b', hb', rfl⟩ := h
      simp only [fieldFree, fieldFree_rename? thn ht, fieldFree_rename? els he, hb.1.1,
        hb.1.2, ih k hb' hb.2 hk, Bool.and_self]
  | whileLoop inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [fieldFree, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, body', hbody, b', hb', rfl⟩ := h
      simp only [fieldFree, fieldFree_rename? body hbody, hb.1, ih k hb' hb.2 hk,
        Bool.and_self]
  | call f args b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [fieldFree, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb', rfl⟩ := h
      simp only [fieldFree, hb.1, ih k hb' hb.2 hk, Bool.and_self]


/-- A program without `call` passes `callsAll C` at every `C`. -/
theorem callsAll_of_callFree (C : String → List d.Ty → List d.Ty → Bool) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.callFree = true) : callsAll C p = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [callsAll, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [callsAll, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [callsAll, ihb hp.1, ihk hp.2, Bool.and_self]
  | call _ _ _ _ => simp [NFProg.callFree] at hp

/-- A program whose every call satisfies `C` passes `callsAll C`. -/
theorem callsAll_of_calls (C : String → List d.Ty → List d.Ty → Bool) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (h : ∀ f as rs, p.Calls f as rs → C f as rs = true) :
    callsAll C p = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih h
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsAll, Bool.and_eq_true]
      exact ⟨ihb fun f as rs hc => h f as rs (Or.inl hc),
        ihk fun f as rs hc => h f as rs (Or.inr hc)⟩
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsAll, Bool.and_eq_true]
      exact ⟨⟨iht fun f as rs hc => h f as rs (Or.inl hc),
        ihe fun f as rs hc => h f as rs (Or.inr (Or.inl hc))⟩,
        ihk fun f as rs hc => h f as rs (Or.inr (Or.inr hc))⟩
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsAll, Bool.and_eq_true]
      exact ⟨ihb fun f as rs hc => h f as rs (Or.inl hc),
        ihk fun f as rs hc => h f as rs (Or.inr hc)⟩
  | call f args k ih =>
      simp only [callsAll, Bool.and_eq_true]
      exact ⟨h _ _ _ (Or.inl ⟨rfl, rfl, rfl⟩), ih fun g as rs hc => h g as rs (Or.inr hc)⟩

/-- A renamed program passes `callsAll C` exactly when the source does. -/
theorem callsAll_rename? (C : String → List d.Ty → List d.Ty → Bool) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} {f : PRen Γ Δ} {q : NFProg d Δ ts}, NFProg.rename? f p = some q →
      callsAll C q = callsAll C p := by
  induction p with
  | ret vs =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.map_eq_some_iff] at h
      obtain ⟨_, -, rfl⟩ := h
      rfl
  | var e k ih =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, k', hk, rfl⟩ := h
      simp only [callsAll, ih hk]
  | forLoop count inits body k ihb ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, _, -, b', hb, k', hk, rfl⟩ := h
      simp only [callsAll, ihb hb, ihk hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, t', ht, e', he, k', hk, rfl⟩ := h
      simp only [callsAll, iht ht, ihe he, ihk hk]
  | whileLoop inits body k ihb ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb, k', hk, rfl⟩ := h
      simp only [callsAll, ihb hb, ihk hk]
  | call g args k ih =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, k', hk, rfl⟩ := h
      simp only [callsAll, ih hk]

/-- The splice of a body and a continuation that pass `callsAll C` passes `callsAll C`. -/
theorem callsAll_seq? (C : String → List d.Ty → List d.Ty → Bool) {Δ : Ctxt d}
    {rs : List d.Ty} (b : NFProg d Δ rs) :
    ∀ {Γ₀ : Ctxt d} {ts : List d.Ty} (k : NFProg d (rs ++ Γ₀) ts) {Γ : Ctxt d}
      {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ} {q : NFProg d Γ ts}, NFProg.seq? k b ρ θ = some q →
      callsAll C b = true → callsAll C k = true → callsAll C q = true := by
  induction b with
  | ret vs =>
      intro Γ₀ ts k Γ ρ θ q h _ hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff] at h
      obtain ⟨_, -, h⟩ := h
      rw [callsAll_rename? C k h, hk]
  | var e b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb', rfl⟩ := h
      have h' := ih k hb' hb hk
      exact h'
  | forLoop count inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [callsAll, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, _, -, body', hbody, b', hb', rfl⟩ := h
      simp only [callsAll, callsAll_rename? C body hbody, hb.1, ih k hb' hb.2 hk,
        Bool.and_self]
  | ifThenElse cond thn els b _ _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [callsAll, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, t', ht, e', he, b', hb', rfl⟩ := h
      simp only [callsAll, callsAll_rename? C thn ht, callsAll_rename? C els he, hb.1.1,
        hb.1.2, ih k hb' hb.2 hk, Bool.and_self]
  | whileLoop inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [callsAll, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, body', hbody, b', hb', rfl⟩ := h
      simp only [callsAll, callsAll_rename? C body hbody, hb.1, ih k hb' hb.2 hk,
        Bool.and_self]
  | call f args b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [callsAll, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb', rfl⟩ := h
      simp only [callsAll, hb.1, ih k hb' hb.2 hk, Bool.and_self]

/-- **Inlining keeps `callsAll C`** at a library without operation bodies whose call bodies
    pass `callsAll C`. -/
theorem callsAll_inline? (C : String → List d.Ty → List d.Ty → Bool) (L : InlineLib d)
    (hL : ∀ o, L.op o = none)
    (hb : ∀ f as rs b, L.call f as rs = some b → callsAll C b = true) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : callsAll C p = true) :
    ∀ {q : NFProg d Γ ts}, NFProg.inline? L p = some q → callsAll C q = true := by
  induction p with
  | ret vs =>
      intro q h
      cases h
      rfl
  | var e k ih =>
      intro q h
      obtain ⟨k', hk, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨o, rfl, args⟩ := e
      simp only [NFProg.inlineVar, hL] at h
      cases h
      exact ih hp hk
  | forLoop count inits body k ihb ihk =>
      intro q h
      simp only [callsAll, Bool.and_eq_true] at hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', k', hk', rfl⟩ := h
      simp only [callsAll, ihb hp.1 hb', ihk hp.2 hk', Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro q h
      simp only [callsAll, Bool.and_eq_true] at hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t', ht', e', he', k', hk', rfl⟩ := h
      simp only [callsAll, iht hp.1.1 ht', ihe hp.1.2 he', ihk hp.2 hk', Bool.and_self]
  | whileLoop inits body k ihb ihk =>
      intro q h
      simp only [callsAll, Bool.and_eq_true] at hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', k', hk', rfl⟩ := h
      simp only [callsAll, ihb hp.1 hb', ihk hp.2 hk', Bool.and_self]
  | call f args k ih =>
      intro q h
      simp only [callsAll, Bool.and_eq_true] at hp
      obtain ⟨k', hk, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i b hbb
        exact callsAll_seq? C b k' h (hb _ _ _ _ hbb) (ih hp.2 hk)
      · cases h
        simp only [callsAll, hp.1, ih hp.2 hk, Bool.and_self]

end Generic

/-- **The traversal of the e-graph pass keeps `callsAll C`.** -/
theorem callsAll_nfGo {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d]
    (C : String → List d.Ty → List d.Ty → Bool)
    (R : CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.RuleSet d) {Γ Δ : Ctxt d}
    {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S) (p : NFProg d Γ ts) :
    callsAll C (CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo R ρ S p) = callsAll C p := by
  induction p generalizing Δ S with
  | ret => rfl
  | var e k ih =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo]
      split <;> simp only [callsAll, ih]
  | forLoop _ _ _ _ ihb ihk =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, callsAll, ihb, ihk]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, callsAll, iht, ihe, ihk]
  | whileLoop _ _ _ ihb ihk =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, callsAll, ihb, ihk]
  | call _ _ _ ih =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, callsAll, ih]


/-! ## The montify pass keeps the calls of a program -/

section Montify

open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (w64)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32 (mont32Cert)

section Rewrite

variable {p : Nat} (h : mont32Cert p = true) (C : String → List JasminTy → List JasminTy → Bool)

/-- A conversion calls the reduce-multiply head at two words before its continuation. -/
theorem callsAll_convProg (hm : C (montHead p) [w64, w64] [w64] = true)
    {Θ : Ctxt jasminDialect} (x : Var Θ w64) (j : ℤ) {us : List JasminTy}
    {k : NFProg jasminDialect (w64 :: w64 :: Θ) us} (hk : callsAll C k = true) :
    callsAll C (convProg h x j k) = true := by
  simp only [convProg, callsAll, hm, hk, Bool.and_self]

theorem callsAll_resConv (hm : C (montHead p) [w64, w64] [w64] = true)
    {Θ : Ctxt jasminDialect} (v : Var Θ w64) (k d : ℤ) {us : List JasminTy}
    {kk : BindK Θ w64 us}
    (hk : ∀ {Θ' : Ctxt jasminDialect} (g : Ctxt.Hom Θ Θ') r (q : NFProg jasminDialect Θ' us),
      kk g r = some q → callsAll C q = true)
    {q : NFProg jasminDialect Θ us} (hq : resConv h v k d kk = some q) :
    callsAll C q = true := by
  unfold resConv at hq
  split at hq
  · exact hk _ _ _ hq
  · obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    exact callsAll_convProg h C hm _ _ (hk _ _ _ hq')

theorem callsAll_fieldRes (hm : C (montHead p) [w64, w64] [w64] = true)
    {Γ Θ : Ctxt jasminDialect} {ρ : MRen Γ Θ} {g : String} {as us : List JasminTy}
    {args : HVector (fun t => Var Θ t) as} {k d : ℤ} {kk : CallK Γ [w64] us}
    (hg : C g as [w64] = true)
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen ([w64] ++ Γ) Θ') (q : NFProg jasminDialect Θ' us),
      kk ρ' = some q → callsAll C q = true)
    {q : NFProg jasminDialect Θ us} (hq : fieldRes h ρ g args k d kk = some q) :
    callsAll C q = true := by
  obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
  simp only [callsAll, hg,
    callsAll_resConv h C hm _ _ _ (fun _ _ q' hq' => hk _ q' hq') hq0, Bool.and_self]

omit h in
theorem callsAll_opaqueArm {Γ Θ : Ctxt jasminDialect} {f : String} {as rs us : List JasminTy}
    {args : HVector (fun t => Var Γ t) as} {ρ : MRen Γ Θ} {kk : CallK Γ rs us}
    (hf : C f as rs = true)
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen (rs ++ Γ) Θ') (q : NFProg jasminDialect Θ' us),
      kk ρ' = some q → callsAll C q = true)
    {q : NFProg jasminDialect Θ us} (hq : opaqueArm f args ρ kk = some q) :
    callsAll C q = true := by
  obtain ⟨_, -, hq⟩ := Option.bind_eq_some_iff.mp hq
  obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
  simp only [callsAll, hf, hk _ _ hk', Bool.and_self]

theorem callsAll_binArm (hm : C (montHead p) [w64, w64] [w64] = true)
    {Γ Θ : Ctxt jasminDialect} {f : String} {a b : Var Γ w64} {ρ : MRen Γ Θ} {d : ℤ}
    {us : List JasminTy} {kk : CallK Γ [w64] us} (hf : C f [w64, w64] [w64] = true)
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen ([w64] ++ Γ) Θ') (q : NFProg jasminDialect Θ' us),
      kk ρ' = some q → callsAll C q = true)
    {q : NFProg jasminDialect Θ us} (hq : binArm h f a b ρ d kk = some q) :
    callsAll C q = true := by
  unfold binArm at hq
  split at hq
  · split at hq
    · split at hq
      · exact callsAll_fieldRes h C hm hm hk hq
      · split at hq
        · exact callsAll_fieldRes h C hm hf hk hq
        · cases hq
    · exact callsAll_opaqueArm C hf hk hq
  · exact callsAll_opaqueArm C hf hk hq

theorem callsAll_unArm (hm : C (montHead p) [w64, w64] [w64] = true)
    {Γ Θ : Ctxt jasminDialect} {f : String} {a : Var Γ w64} {ρ : MRen Γ Θ} {d : ℤ}
    {us : List JasminTy} {kk : CallK Γ [w64] us} (hf : C f [w64] [w64] = true)
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen ([w64] ++ Γ) Θ') (q : NFProg jasminDialect Θ' us),
      kk ρ' = some q → callsAll C q = true)
    {q : NFProg jasminDialect Θ us} (hq : unArm h f a ρ d kk = some q) :
    callsAll C q = true := by
  unfold unArm at hq
  split at hq
  · split at hq
    · split at hq
      · exact callsAll_fieldRes h C hm hm hk hq
      · split at hq
        · exact callsAll_fieldRes h C hm hf hk hq
        · cases hq
    · exact callsAll_opaqueArm C hf hk hq
  · exact callsAll_opaqueArm C hf hk hq

/-- A call the rewriter accepts makes its own symbol at its own signature, the
    reduce-multiply head at two words, and the calls of its continuation. -/
theorem callsAll_callArm (hm : C (montHead p) [w64, w64] [w64] = true)
    {Γ Θ : Ctxt jasminDialect} {f : String} {us as rs : List JasminTy}
    {args : HVector (fun t => Var Γ t) as} {ρ : MRen Γ Θ} {d : ℤ} {kk : CallK Γ rs us}
    (hf : C f as rs = true)
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen (rs ++ Γ) Θ') (q : NFProg jasminDialect Θ' us),
      kk ρ' = some q → callsAll C q = true)
    {q : NFProg jasminDialect Θ us} (hq : callArm h f args ρ d kk = some q) :
    callsAll C q = true := by
  unfold callArm at hq
  split at hq
  · rename_i hs
    obtain ⟨h1, h2⟩ := hs
    subst h1 h2
    exact callsAll_binArm h C hm hf hk hq
  · split at hq
    · rename_i _ hs
      obtain ⟨h1, h2⟩ := hs
      subst h1 h2
      exact callsAll_unArm h C hm hf hk hq
    · exact callsAll_opaqueArm C hf hk hq

theorem callsAll_varConv (hm : C (montHead p) [w64, w64] [w64] = true)
    {Θ : Ctxt jasminDialect} {d : ℤ} {us : List JasminTy} {t : JasminTy}
    {kk : BindK (t :: Θ) t us}
    (hk : ∀ {Θ' : Ctxt jasminDialect} (g : Ctxt.Hom (t :: Θ) Θ') r
      (q : NFProg jasminDialect Θ' us), kk g r = some q → callsAll C q = true)
    {q : NFProg jasminDialect (t :: Θ) us} (hq : varConv h d kk = some q) :
    callsAll C q = true := by
  unfold varConv at hq
  split at hq
  · exact hk _ _ _ hq
  · cases t with
    | reg w =>
      by_cases hw : w = 64
      · subst hw
        obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
        exact callsAll_convProg h C hm _ _ (hk _ _ _ hq')
      · simp [wordConv, hw] at hq
    | _ => simp [wordConv] at hq

/-- **The rewriter keeps `callsAll C`** when `C` holds at the reduce-multiply head at two
    words: every call it returns is a call of the source at its signature or a call of that
    head. -/
theorem callsAll_montifyAux (hm : C (montHead p) [w64, w64] [w64] = true) :
    {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    (prog : NFProg jasminDialect Γ ts) → (H : DegHint) → {Θ : Ctxt jasminDialect} →
    (ρ : MRen Γ Θ) → (q : NFProg jasminDialect Θ ts) → callsAll C prog = true →
      montifyAux h prog H ρ = some q → callsAll C q = true
  | _, _, .ret _, _, _, _, _, _, hq => by
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hq
      rfl
  | _, _, .var e k, H, _, ρ, q, hp, hq => by
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
      have h0 := callsAll_varConv h C hm
        (fun _ _ q' hq' => callsAll_montifyAux hm k _ _ q' hp hq') hq0
      exact h0
  | _, _, .forLoop count inits body k, H, _, ρ, q, hp, hq => by
      simp only [callsAll, Bool.and_eq_true] at hp
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hb', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [callsAll, callsAll_montifyAux hm body _ _ _ hp.1 hb',
        callsAll_montifyAux hm k _ _ _ hp.2 hk', Bool.and_self]
  | _, _, .ifThenElse cond thn els k, H, _, ρ, q, hp, hq => by
      simp only [callsAll, Bool.and_eq_true] at hp
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨t', ht', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨e', he', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [callsAll, callsAll_montifyAux hm thn _ _ _ hp.1.1 ht',
        callsAll_montifyAux hm els _ _ _ hp.1.2 he', callsAll_montifyAux hm k _ _ _ hp.2 hk',
        Bool.and_self]
  | _, _, .whileLoop inits body k, H, _, ρ, q, hp, hq => by
      simp only [callsAll, Bool.and_eq_true] at hp
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hb', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [callsAll, callsAll_montifyAux hm body _ _ _ hp.1 hb',
        callsAll_montifyAux hm k _ _ _ hp.2 hk', Bool.and_self]
  | _, _, .call f args k, H, _, ρ, q, hp, hq => by
      simp only [callsAll, Bool.and_eq_true] at hp
      unfold montifyAux at hq
      split at hq
      · cases hq
      · exact callsAll_callArm h C hm hp.1
          (fun ρ' q' hk => callsAll_montifyAux hm k _ ρ' q' hp.2 hk) hq

theorem callsAll_entryConv (hm : C (montHead p) [w64, w64] [w64] = true)
    {Γ : Ctxt jasminDialect} {us : List JasminTy}
    (kk : ∀ {Θ : Ctxt jasminDialect}, MRen Γ Θ → Option (NFProg jasminDialect Θ us))
    (hk : ∀ {Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ) (q : NFProg jasminDialect Θ us),
      kk ρ = some q → callsAll C q = true) :
    ∀ (vs : List (Var Γ w64 × ℤ)) {Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ)
      (q : NFProg jasminDialect Θ us), entryConv h kk vs ρ = some q → callsAll C q = true
  | [], _, ρ, q, hq => hk ρ q hq
  | (v, d) :: vs, _, ρ, q, hq => by
      obtain ⟨x, -, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨q1, hq1, rfl⟩ := Option.map_eq_some_iff.mp hq
      exact callsAll_convProg h C hm _ _ (callsAll_entryConv hm kk hk vs _ q1 hq1)

theorem callsAll_montify
    (hm : montTag? (montHead p) = some p → C (montHead p) [w64, w64] [w64] = true)
    (pd : List ℤ) (H : DegHint) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (prog : NFProg jasminDialect Γ ts) (hp : callsAll C prog = true)
    {q : NFProg jasminDialect Γ ts} (hq : montify h pd H prog = some q) :
    callsAll C q = true := by
  unfold montify at hq
  split at hq
  · rename_i hmt
    exact callsAll_entryConv h C (hm hmt) _
      (fun ρ q' hq' => callsAll_montifyAux h C (hm hmt) prog H ρ q' hp hq') _ _ q hq
  · cases hq

end Rewrite

/-- The reduce-multiply block as a program has no `call`. -/
theorem redcMulProg_callFree (q : Nat) : (redcMulProg q).callFree = true :=
  callFree_ofCom _

variable (C : String → List JasminTy → List JasminTy → Bool)

/-- A body of a reduce-multiply head has no `call`. -/
theorem callsAll_montBody {f : String} {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (hb : montBody f as rs = some b) : callsAll C b = true := by
  unfold montBody at hb
  split at hb
  · rename_i q _
    split at hb
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      cases hb
      have hr := callsAll_of_callFree (d := jasminDialect) C (redcMulProg q)
        (redcMulProg_callFree q)
      exact hr
    · cases hb
  · cases hb

/-- A montify round keeps `callsAll C`. -/
theorem callsAll_montifyAt {p : Nat} (h : mont32Cert p = true)
    (hm : montTag? (montHead p) = some p → C (montHead p) [w64, w64] [w64] = true)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts)
    (hp : callsAll C prog = true) : callsAll C (montifyAt h prog) = true := by
  unfold montifyAt
  split
  · rename_i q hq
    split
    · rename_i q' hq'
      split
      · exact callsAll_inline? C montLibJ (fun _ => rfl)
          (fun _ _ _ _ hb => callsAll_montBody C hb) q
          (callsAll_montify h C hm _ _ prog hp hq) hq'
      · exact hp
    · exact hp
  · exact hp

/-- The montify rounds at a list of moduli keep `callsAll C`. -/
theorem callsAll_montifyMods
    (hm : ∀ p, montTag? (montHead p) = some p → C (montHead p) [w64, w64] [w64] = true)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} :
    ∀ (ps : List Nat) (prog : NFProg jasminDialect Γ ts), callsAll C prog = true →
      callsAll C (montifyMods ps prog) = true
  | [], _, hp => hp
  | p :: ps, prog, hp => by
      refine callsAll_montifyMods hm ps _ ?_
      split
      · rename_i h
        exact callsAll_montifyAt C h (hm p) prog hp
      · exact hp

/-- **The montify pass keeps `callsAll C`** when `C` holds at every reduce-multiply head at
    two words. -/
theorem callsAll_montifyPass
    (hm : ∀ p, montTag? (montHead p) = some p → C (montHead p) [w64, w64] [w64] = true)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts)
    (hp : callsAll C prog = true) : callsAll C (montifyPass prog) = true :=
  callsAll_montifyMods C hm _ prog hp

end Montify

/-! ## The inlining step on its domain -/

/-- **A template body has no `call`**: every body of `fieldBody` is built by `NFProg.ofCom`. -/
theorem fieldBody_callFree {f : String} {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (h : fieldBody f as rs = some b) : b.callFree = true := by
  unfold fieldBody at h
  split at h
  · rename_i m p _
    split at h
    · split at h
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        cases h
        cases m <;> exact callFree_ofCom _
      · cases h
    · unfold FieldWideDecl.wideBody at h
      split at h
      · rename_i m' p' _
        split at h
        · split at h
          · rename_i hs
            obtain ⟨rfl, rfl⟩ := hs
            cases h
            exact callFree_ofCom _
          · cases h
        · split at h
          · split at h
            · rename_i hs
              obtain ⟨rfl, rfl⟩ := hs
              cases h
              exact callFree_ofCom _
            · cases h
          · cases h
      · cases h
  · cases h

/-- **A call of a narrow Montgomery head**: `fieldTagM?` reads its head as a method `m` at an
    odd modulus `1 < p < 2^64`, and its signature is `fieldJSig m → [.reg 64]`. -/
def fieldCallMontB (f : String) (as rs : List JasminTy) : Bool :=
  match _root_.Hax.FieldTag.fieldTagM? f with
  | some (m, p, _) =>
      decide (1 < p ∧ p % 2 = 1 ∧ p < 2 ^ 64 ∧ as = fieldJSig m ∧ rs = [.reg 64])
  | none => false

/-- **The domain of the field dialect step**: every `call` node of the program has a head
    that is no field head (`fieldHeadB`, a canonical or a Montgomery head), a head with a
    template body `fieldBody` at the signature of the call, or a narrow Montgomery head at its
    signature (`fieldCallMontB`). -/
def fieldDomB : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => fieldDomB k
  | _, _, .forLoop _ _ body k => fieldDomB body && fieldDomB k
  | _, _, .ifThenElse _ thn els k => fieldDomB thn && fieldDomB els && fieldDomB k
  | _, _, .whileLoop _ body k => fieldDomB body && fieldDomB k
  | _, _, .call (as := as) (rs := rs) f _ k =>
      (!fieldHeadB f || (fieldBody f as rs).isSome || fieldCallMontB f as rs) && fieldDomB k

/-- **The domain of the inlining at `fieldLibJ`**: every `call` node of the program has a
    head that is no field head, or a head with a template body `fieldBody` at the signature
    of the call. -/
def fieldInlineDomB : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => fieldInlineDomB k
  | _, _, .forLoop _ _ body k => fieldInlineDomB body && fieldInlineDomB k
  | _, _, .ifThenElse _ thn els k =>
      fieldInlineDomB thn && fieldInlineDomB els && fieldInlineDomB k
  | _, _, .whileLoop _ body k => fieldInlineDomB body && fieldInlineDomB k
  | _, _, .call (as := as) (rs := rs) f _ k =>
      (!fieldHeadB f || (fieldBody f as rs).isSome) && fieldInlineDomB k

/-- A program without `call` is in the domain of the inlining step. -/
theorem fieldDomB_of_callFree {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : p.callFree = true) : fieldDomB p = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [fieldDomB, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [fieldDomB, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [fieldDomB, ihb hp.1, ihk hp.2, Bool.and_self]
  | call _ _ _ _ => simp [NFProg.callFree] at hp

/-- **The inlining at `fieldLibJ` is defined on `fieldInlineDomB`, and its result calls no
    field head.** -/
theorem inline?_fieldLibJ_of_Dom {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : fieldInlineDomB p = true) :
    ∃ q, NFProg.inline? fieldLibJ p = some q ∧ fieldFree q = true := by
  induction p with
  | ret vs => exact ⟨_, rfl, rfl⟩
  | var e k ih =>
      obtain ⟨k', hk, hf⟩ := ih hp
      obtain ⟨o, rfl, args⟩ := e
      refine ⟨.var ⟨o, rfl, args⟩ k', ?_, hf⟩
      simp only [NFProg.inline?, hk, Option.bind_some, NFProg.inlineVar,
        show fieldLibJ.op o = none from rfl]
  | forLoop count inits body k ihb ihk =>
      simp only [fieldInlineDomB, Bool.and_eq_true] at hp
      obtain ⟨b', hb, hfb⟩ := ihb hp.1
      obtain ⟨k', hk, hfk⟩ := ihk hp.2
      exact ⟨.forLoop count inits b' k', by
        simp only [NFProg.inline?, hb, hk, Option.bind_some, Option.map_some],
        by simp only [fieldFree, hfb, hfk, Bool.and_self]⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [fieldInlineDomB, Bool.and_eq_true] at hp
      obtain ⟨t', ht, hft⟩ := iht hp.1.1
      obtain ⟨e', he, hfe⟩ := ihe hp.1.2
      obtain ⟨k', hk, hfk⟩ := ihk hp.2
      exact ⟨.ifThenElse cond t' e' k', by
        simp only [NFProg.inline?, ht, he, hk, Option.bind_some, Option.map_some],
        by simp only [fieldFree, hft, hfe, hfk, Bool.and_self]⟩
  | whileLoop inits body k ihb ihk =>
      simp only [fieldInlineDomB, Bool.and_eq_true] at hp
      obtain ⟨b', hb, hfb⟩ := ihb hp.1
      obtain ⟨k', hk, hfk⟩ := ihk hp.2
      exact ⟨.whileLoop inits b' k', by
        simp only [NFProg.inline?, hb, hk, Option.bind_some, Option.map_some],
        by simp only [fieldFree, hfb, hfk, Bool.and_self]⟩
  | call f args k ih =>
      simp only [fieldInlineDomB, Bool.and_eq_true, Bool.or_eq_true] at hp
      obtain ⟨k', hk, hf⟩ := ih hp.2
      simp only [NFProg.inline?, hk, Option.bind_some]
      split
      · rename_i b hb
        obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
          (NFProg.seq?_isSome_of_total b k' (PRen.total_ofArgs args) PRen.total_id)
        exact ⟨q, hq, fieldFree_seq? b k' hq (fieldFree_of_callFree b (fieldBody_callFree hb))
          hf⟩
      · rename_i hb
        have hn : (!fieldHeadB f) = true := by
          rcases hp.1 with h | h
          · exact h
          · exact absurd h (by simp [show fieldBody f _ _ = none from hb])
        exact ⟨_, rfl, by simp only [fieldFree, hn, hf, Bool.and_self]⟩

/-- **The inlining step is complete on `fieldInlineDomB`**, into the programs that call no
    field head. -/
theorem fieldInlineStep_completeOn (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    (fieldInlineStep Γ ts).CompleteOn (fun p => fieldInlineDomB p = true)
      (fun q => fieldFree q = true) := by
  intro p hp
  obtain ⟨q, hq, hf⟩ := inline?_fieldLibJ_of_Dom p hp
  refine ⟨q, ?_, hf⟩
  change (NFProg.inline? fieldLibJ p).bind (fun q => if fieldFree q then some q else none) = _
  rw [hq, Option.bind_some, ite_eq_left hf]

/-- **The inlining step runs every program of `fieldInlineDomB` to `some`.** -/
theorem fieldInline_isSome_of_Dom {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hp : fieldInlineDomB p = true) :
    ((fieldInlineStep Γ ts).run p).isSome = true :=
  (fieldInlineStep_completeOn Γ ts).run_isSome hp

/-! ## The conversion on its domain -/

/-- **The conversion is complete on the `Convertible` programs without `call`**, into the
    programs without `call`. -/
theorem catToJasmin_completeOn (Γ : Ctxt catCryptDialect) (ts : List CryptoTy) :
    (mapStep catToJasmin catToJasmin_regionTypes Γ ts).CompleteOn
      (fun r => Convertible r ∧ r.callFree = true) (fun q => q.callFree = true) := by
  rintro r ⟨hc, hf⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
    ((isSome_map?_catToJasmin_iff r (fun v => v)).2 hc)
  exact ⟨q, hq, map?_callFree _ _ r hf _ hq⟩

/-- **The conversion runs every `Convertible` program to `some`.** -/
theorem catToJasmin_isSome_of_Dom {Γ : Ctxt catCryptDialect} {ts : List CryptoTy}
    {r : NFProg catCryptDialect Γ ts} (hr : Convertible r) :
    ((mapStep catToJasmin catToJasmin_regionTypes Γ ts).run r).isSome = true :=
  (isSome_map?_catToJasmin_iff r (fun v => v)).2 hr

/-! ## The chain on the programs of `NB` -/

/-- **The domain of `extChainCore` through `NB`**: the result type passes `outTyB` and the
    dead-code-eliminated program satisfies `NB`. -/
def extDomNB {Γ : Ctxt nfDialect} (t : NfTy) (p : NFProg nfDialect Γ [t]) : Bool :=
  outTyB t && NB (NFProg.dce p)

/-- The translation with declarations is complete on `NB`, into the programs without `call`
    whose operations have images in `jasminDialect`. -/
theorem extCallStep_completeOn_NB (D : List ExtDecl) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    (extCallStep D Γ ts).CompleteOn (fun q => NB q = true)
      (fun r => r.callFree = true ∧ OpsHaveImages r) := by
  intro q hq
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (nfToCat_isSome_of_NB q hq TRd.id)
  have hcf := nfToCat_callFree q TRd.id hr
  have hx : nfToCatExt (fieldDeclsFor D q) q TRd.id = some r :=
    nfToCatExt_of_nfToCat _ q TRd.id r (nfToCatExt_nil q TRd.id r hr) hcf
  exact ⟨r, hx, hcf, nfToCatExt_opsHaveImages _ q TRd.id r hx⟩

/-! ## The chain on the programs of `NBD` -/

/-- **A call in the domain of the field dialect step**: its head is no field head, it has a
    template body `fieldBody` at its signature, or it is a narrow Montgomery head at its
    signature (`fieldCallMontB`). -/
def fieldCallB (f : String) (as rs : List JasminTy) : Bool :=
  !fieldHeadB f || (fieldBody f as rs).isSome || fieldCallMontB f as rs

/-- `fieldDomB` is `callsAll fieldCallB`. -/
theorem fieldDomB_eq_callsAll {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) : fieldDomB p = callsAll fieldCallB p := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih
  | forLoop _ _ _ _ ihb ihk => simp only [fieldDomB, callsAll, ihb, ihk]
  | ifThenElse _ _ _ _ iht ihe ihk => simp only [fieldDomB, callsAll, iht, ihe, ihk]
  | whileLoop _ _ _ ihb ihk => simp only [fieldDomB, callsAll, ihb, ihk]
  | call f args k ih => simp only [fieldDomB, callsAll, fieldCallB, ih]

/-- **The montify step keeps `fieldDomB`**: a call of its result is a call of its source at
    the same signature or a call of a reduce-multiply head, which is no field head. -/
theorem montifyStep_completeOn (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    (montifyStep Γ ts).CompleteOn (fun q => fieldDomB q = true)
      (fun q => fieldDomB q = true) := by
  intro q hq
  refine ⟨_, rfl, ?_⟩
  show fieldDomB (NFMontify.montifyPass q) = true
  rw [fieldDomB_eq_callsAll] at hq ⊢
  exact callsAll_montifyPass fieldCallB (fun _ hm => by
    simp only [fieldCallB, NFMontify.fieldHeadB_of_montTag? hm, Bool.not_false,
      Bool.true_or]) q hq

/-- **The template of a declaration**: at the image in `jasminDialect` of its signature, the
    body `fieldBody` of its name exists, or its name is a narrow Montgomery head
    (`fieldCallMontB`). -/
def fieldTemplB (d : ExtDecl) : Bool :=
  (fieldBody d.name ((d.args.map catTy).map mapTy) ([catTy d.ret].map mapTy)).isSome ||
    fieldCallMontB d.name ((d.args.map catTy).map mapTy) ([catTy d.ret].map mapTy)

/-- **Every tagged call of the program has a template**: every declaration of
    `fieldDeclsOf` passes `fieldTemplB`. -/
def fieldTemplsB {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) : Bool :=
  (fieldDeclsOf p).all fieldTemplB

/-- **The translation with declarations is complete on `NBD`**, into the programs whose calls
    are in the domain of the inlining step at the image of their signatures and whose
    operations have images in `jasminDialect`: every call of the translation is a declaration
    of `fieldDeclsFor D q` (`nfToCatExt_calls`), an untagged one of `D` or a tagged one of
    `fieldDeclsOf q`, which has a template. -/
theorem extCallStep_completeOn_NBD (D : List ExtDecl) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    (extCallStep D Γ ts).CompleteOn
      (fun q => NBD (fieldDeclsFor D q) q = true ∧ fieldTemplsB q = true)
      (fun r => callsAll (fun f as rs => fieldCallB f (as.map mapTy) (rs.map mapTy)) r = true ∧
        OpsHaveImages r) := by
  rintro q ⟨hq, hT⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
    (nfToCatExt_isSome_of_NBD (fieldDeclsFor D q) q hq TRd.id)
  refine ⟨r, hr, ?_, nfToCatExt_opsHaveImages _ q TRd.id r hr⟩
  refine callsAll_of_calls _ r fun f as rs hc => ?_
  obtain ⟨d, hd, rfl, rfl, rfl, -⟩ := nfToCatExt_calls _ q TRd.id r hr f as rs hc
  simp only [fieldDeclsFor, List.mem_append, List.mem_filter] at hd
  rcases hd with ⟨-, hn⟩ | hd
  · simp only [fieldCallB, hn, Bool.true_or]
  · have ht := List.all_eq_true.mp hT d hd
    simp only [fieldTemplB, Bool.or_eq_true] at ht
    simp only [fieldCallB, Bool.or_eq_true]
    rcases ht with ht | ht
    · exact Or.inl (Or.inr ht)
    · exact Or.inr ht

/-- **The domain of `extChainCore` through `NBD`**: the result type passes `outTyB`, and the
    dead-code-eliminated program satisfies `NBD` at its declarations `fieldDeclsFor D` and has
    a template for every tagged call. -/
def extDomNBD (D : List ExtDecl) {Γ : Ctxt nfDialect} (t : NfTy)
    (p : NFProg nfDialect Γ [t]) : Bool :=
  outTyB t && NBD (fieldDeclsFor D (NFProg.dce p)) (NFProg.dce p) &&
    fieldTemplsB (NFProg.dce p)

/-! ## The moduli of the front have templates -/

/-- The bound chain of the fold template is the chain `ImpToNF.fieldFoldsOk` of the front. -/
theorem foldsOk_eq_fieldFoldsOk (c P : Nat) :
    ∀ k B, FieldRouteNarrow.foldsOk c P k B = CatCrypt.Crypto.Hax.ImpToNF.fieldFoldsOk c P k B
  | 0, _ => rfl
  | k + 1, B => by
      simp only [FieldRouteNarrow.foldsOk, CatCrypt.Crypto.Hax.ImpToNF.fieldFoldsOk,
        foldsOk_eq_fieldFoldsOk c P k]

/-- **The fold template exists exactly at the moduli `ImpToNF.fieldNarrowOk` accepts.** -/
theorem narrowFoldsOf_isSome (p : Nat) :
    (FieldRouteNarrow.narrowFoldsOf p).isSome = CatCrypt.Crypto.Hax.ImpToNF.fieldNarrowOk p := by
  have hc : FieldRouteNarrow.narrowCert p = fun n =>
      decide (1 < p ∧ p ≤ 2 ^ 31) &&
        CatCrypt.Crypto.Hax.ImpToNF.fieldFoldsOk (2 ^ 31 - p) p n ((p - 1) * (p - 1) + 1) := by
    funext n
    simp only [FieldRouteNarrow.narrowCert, foldsOk_eq_fieldFoldsOk]
  rw [FieldRouteNarrow.narrowFoldsOf, hc, CatCrypt.Crypto.Hax.ImpToNF.fieldNarrowOk]
  exact Bool.eq_iff_iff.mpr (by simp only [List.find?_isSome, List.any_eq_true])

/-- A modulus without a narrow template has none of the fold count `narrowFoldsOf`. -/
theorem fieldNarrowOk_of_narrowFieldOf {p : Nat} (h : narrowFieldOf p = none) :
    CatCrypt.Crypto.Hax.ImpToNF.fieldNarrowOk p = false := by
  rw [← narrowFoldsOf_isSome]
  unfold narrowFieldOf at h
  split at h
  · cases h
  · rename_i hn
    rw [hn]
    rfl

/-- **A tagged declaration at a modulus that passes `ImpToNF.fieldModOk` has a template**:
    `fieldDecl` at a modulus below `2⁶⁴` has the narrow template block or the one-limb
    Montgomery block (`montWordOf_isSome`), and `FieldWideDecl.wideDecl` at a modulus of
    several words has the wide block of its template (`wideTemplateOf_isSome`). -/
theorem fieldTemplB_of_fieldModOk {d : ExtDecl} {m : _root_.Hax.FieldTag.FieldMethod} {p : Nat}
    (hmp : fieldTag? d.name = some (m, p))
    (hd : (p < 2 ^ 64 ∧ d = fieldDecl d.name m) ∨
      (2 ^ 64 ≤ p ∧ d = FieldWideDecl.wideDecl d.name m p))
    (hp : CatCrypt.Crypto.Hax.ImpToNF.fieldModOk p = true) : fieldTemplB d = true := by
  unfold fieldTemplB
  refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
  generalize d.name = f at hmp hd
  rcases hd with ⟨h64, rfl⟩ | ⟨h64, rfl⟩
  · have hs : List.map mapTy (List.map catTy (fieldDecl f m).args) = fieldJSig m := by
      cases m <;> rfl
    have hr : List.map mapTy [catTy (fieldDecl f m).ret] = [.reg 64] := rfl
    rw [hs, hr]
    unfold fieldBody
    simp only [hmp]
    rcases hN : narrowFieldOf p with _ | F
    · have hn := fieldNarrowOk_of_narrowFieldOf hN
      simp only [CatCrypt.Crypto.Hax.ImpToNF.fieldModOk, hn, Bool.or_false, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hp
      have hw : FieldWideInline.wideTemplateOf p = none := FieldWideInline.wideTemplateOf_of_lt h64
      obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp
        (FieldWideInline.montWordOf_isSome hp.1.1 hp.1.2 h64)
      unfold FieldWideDecl.wideBody
      simp only [hmp, hw, hP]
      rw [dite_eq_left ⟨by cases m <;> rfl, trivial⟩]
      rfl
    · simp only
      rw [dite_eq_left ⟨trivial, trivial⟩]
      rfl
  · have hN : narrowFieldOf p = none := by
      rcases hF : narrowFieldOf p with _ | F
      · rfl
      · have := (narrowFieldOf_spec hF).2.1
        omega
    have hn := fieldNarrowOk_of_narrowFieldOf hN
    simp only [CatCrypt.Crypto.Hax.ImpToNF.fieldModOk, hn, Bool.or_false, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨W, hW⟩ := FieldWideInline.wideTemplateOf_isSome h64 hp.1.2 hp.2
    unfold fieldBody FieldWideDecl.wideBody
    simp only [hmp, hN, hW]
    rw [dite_eq_left ⟨by cases m <;> rfl, rfl⟩]
    rfl

/-- **A declaration of a narrow Montgomery head has a template**: `fieldDecl` at a head that
    `fieldTagM?` reads at an odd modulus `1 < p < 2^64` is at the signature
    `fieldJSig m → [.reg 64]` (`fieldCallMontB`). -/
theorem fieldTemplB_mont {d : ExtDecl} {m : _root_.Hax.FieldTag.FieldMethod} {p k : Nat}
    (hmp : _root_.Hax.FieldTag.fieldTagM? d.name = some (m, p, k)) (h1 : 1 < p)
    (hodd : p % 2 = 1) (hp : p < 2 ^ 64) (hd : d = fieldDecl d.name m) :
    fieldTemplB d = true := by
  unfold fieldTemplB
  refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
  generalize d.name = f at hmp hd
  subst hd
  have hs : List.map mapTy (List.map catTy (fieldDecl f m).args) = fieldJSig m := by
    cases m <;> rfl
  have hr : List.map mapTy [catTy (fieldDecl f m).ret] = [.reg 64] := rfl
  rw [hs, hr]
  simp only [fieldCallMontB, hmp]
  exact decide_eq_true ⟨h1, hodd, hp, trivial, trivial⟩

/-- **Every tagged call at a modulus that passes `ImpToNF.fieldModOk` has a template**: when
    the modulus of every declaration of `fieldDeclsOf q` passes `fieldModOk`, `q` passes
    `fieldTemplsB`. -/
theorem fieldTemplsB_of_fieldModOk {Γ : Ctxt nfDialect} {ts : List NfTy}
    (q : NFProg nfDialect Γ ts)
    (h : ∀ d ∈ fieldDeclsOf q, ∀ m p, fieldTag? d.name = some (m, p) →
      CatCrypt.Crypto.Hax.ImpToNF.fieldModOk p = true) :
    fieldTemplsB q = true := by
  refine List.all_eq_true.mpr fun d hd => ?_
  rcases mem_fieldDeclsOf q hd with ⟨m, p, hmp, hdp⟩ | ⟨m, p, k, hmp, h1, hodd, hp, hdm⟩
  · exact fieldTemplB_of_fieldModOk hmp hdp (h d hd m p hmp)
  · exact fieldTemplB_mont hmp h1 hodd hp hdm

end CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal
