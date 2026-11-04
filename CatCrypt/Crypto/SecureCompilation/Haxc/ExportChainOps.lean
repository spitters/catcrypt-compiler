/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ExportComplete
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldInlineOps
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep

/-!
# The calls and the exit-flag loops of the output of the chain

The predicate `callsLoopsAll C W` holds of a program when every `call` node satisfies `C` at
its symbol and signature and every exit-flag loop satisfies `W` at its carried types. Every
step of `extChain` keeps it: tuple flattening and dead-binding elimination, renaming,
splicing and inlining at a library whose bodies pass it, the e-graph traversal, the
conversion `map?` (which carries it along the type map), the select lowering, the range
stage, the montify pass, when `C` holds at the reduce-multiply heads, and the field dialect
step, whose inlined bodies have no exit-flag loop and no call. The translation `nfToCatExt`
maps the carried types of the exit-flag loops along `catTy` and declares its calls at
signatures of words and word arrays (`nfToCatExt_calls`). On an input whose flattened form
has its exit-flag loops at types of `whileCarryOkB`, every program `extChain` returns has its
exit-flag loops at register types of positive width and calls only at signatures of
`wordSig`: it passes `whileRegB` and `wordCalls` (`extChain_whileRegB`,
`extChain_wordCalls`).

Every program `extChain` returns on the unit-free output of the flattening, over a context of
types of positive width, has its operations in `opMemB`, each with a result type of positive
width. The translation gives operations of `catMemB`; the e-graph pass at `catRules` keeps
them, since its rules emit variables and constants at the type of the rewritten binding; the
conversion takes them to `opMemB` at positive width; the montify pass binds `64`-bit
constants and register arithmetic; the select lowering binds selects at the result types of
branches, which are types of variables of the context and so of positive width; the range
stage and the e-graph pass at `jasminRules` fold to register constants and register
arithmetic at the type of the binding they replace.

## Main definitions

* `callsLoopsAll` — every call satisfies `C` and every exit-flag loop satisfies `W`.
* `altOpsB`, `altConstB`, `RulesOps` — the operations of an alternative of an e-graph rule,
  and rule sets whose alternatives keep an operation predicate.

## Main results

* `callsLoopsAll_rename?`, `callsLoopsAll_seq?`, `callsLoopsAll_inline?`, `callsLoopsAll_dce`,
  `callsLoopsAll_flatSame`, `callsLoopsAll_nfGo`, `callsLoopsAll_map?`,
  `callsLoopsAll_lowerSel`, `callsLoopsAll_rangeGo`, `callsLoopsAll_montifyPass`,
  `callsLoopsAll_fieldDialect` — the passes keep or transport `callsLoopsAll`.
* `callsAll_of_callsLoopsAll`, `whileFree_of_callsLoopsAll` — `callsLoopsAll C W` gives
  `callsAll C`, and at `W = fun _ => false` the absence of exit-flag loops.
* `callsLoopsAll_of_opsNB` — a program of `opsNB P` at the loop test `W` passes
  `callsLoopsAll C W`.
* `nfToCatExt_callsLoopsAll` — the translation maps the carried types of the exit-flag loops
  along `catTy`.
* `extChain_callsLoopsAll` — every program `extChain` returns on an input whose flattened
  form has its exit-flag loops at types of `whileCarryOkB` passes `callsLoopsAll` at the
  signatures of `wordSig` and with its exit-flag loops at register types of positive
  width.
* `extChain_whileRegB`, `extChain_wordCalls` — every such program passes `whileRegB` and
  `wordCalls`.
* `allOps_nfGo`, `catRules_ops`, `jasminRules_ops`, `allOps_rangeGo`, `allOps_montifyPass`,
  `allOps_lowerSel` — the passes keep their operation predicates.
* `unitFree_dce`, `unitFree_flatSame` — the input of the translation is unit-free.
* `extChain_allOps` — every program `extChain` returns has its operations in `opMemB` at
  positive width.
* `HaxModule.refusal?_eq_none_imp_export_isSome` — on a module `refusal?` accepts, the
  program `extChain` returns passes `whileRegB`, `wordCalls` and `regionExportableB`, and the
  export returns code on it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep (fieldDialectStep fieldLibD
  fieldBodyD_callsAll fieldBodyD_whileFree calls_of_callsAll)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (opsNB)
open Ctxt (Var Valuation)

/-! ## 1. The calls and the exit-flag loops of a program -/

section Generic

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- **Every `call` node satisfies `C` at its symbol and signature, and every exit-flag loop
    satisfies `W` at its carried types**, in every region and continuation. -/
def callsLoopsAll (C : String → List d.Ty → List d.Ty → Bool) (W : List d.Ty → Bool) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => callsLoopsAll C W k
  | _, _, .forLoop _ _ body k => callsLoopsAll C W body && callsLoopsAll C W k
  | _, _, .ifThenElse _ thn els k =>
      callsLoopsAll C W thn && callsLoopsAll C W els && callsLoopsAll C W k
  | _, _, .whileLoop (cs := cs) _ body k => W cs && callsLoopsAll C W body && callsLoopsAll C W k
  | _, _, .call (as := as) (rs := rs) f _ k => C f as rs && callsLoopsAll C W k

variable (C : String → List d.Ty → List d.Ty → Bool) (W : List d.Ty → Bool)

/-- A program without exit-flag loops whose every call satisfies `C` passes
    `callsLoopsAll C W`. -/
theorem callsLoopsAll_of_calls {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hw : p.whileFree = true) (h : ∀ f as rs, p.Calls f as rs → C f as rs = true) :
    callsLoopsAll C W p = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hw h
  | forLoop _ _ _ _ ihb ihk =>
      simp only [NFProg.whileFree, Bool.and_eq_true] at hw
      simp only [callsLoopsAll, Bool.and_eq_true]
      exact ⟨ihb hw.1 fun f as rs hc => h f as rs (Or.inl hc),
        ihk hw.2 fun f as rs hc => h f as rs (Or.inr hc)⟩
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [NFProg.whileFree, Bool.and_eq_true] at hw
      simp only [callsLoopsAll, Bool.and_eq_true]
      exact ⟨⟨iht hw.1.1 fun f as rs hc => h f as rs (Or.inl hc),
        ihe hw.1.2 fun f as rs hc => h f as rs (Or.inr (Or.inl hc))⟩,
        ihk hw.2 fun f as rs hc => h f as rs (Or.inr (Or.inr hc))⟩
  | whileLoop => simp [NFProg.whileFree] at hw
  | call f args k ih =>
      simp only [callsLoopsAll, Bool.and_eq_true]
      exact ⟨h _ _ _ (Or.inl ⟨rfl, rfl, rfl⟩), ih hw fun g as rs hc => h g as rs (Or.inr hc)⟩

/-- A program whose exit-flag loops pass `W` and whose every call satisfies `C` passes
    `callsLoopsAll C W`. -/
theorem callsLoopsAll_of_loops {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hw : callsLoopsAll (fun _ _ _ => true) W p = true)
    (h : ∀ f as rs, p.Calls f as rs → C f as rs = true) :
    callsLoopsAll C W p = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hw h
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hw ⊢
      exact ⟨ihb hw.1 fun f as rs hc => h f as rs (Or.inl hc),
        ihk hw.2 fun f as rs hc => h f as rs (Or.inr hc)⟩
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hw ⊢
      exact ⟨⟨iht hw.1.1 fun f as rs hc => h f as rs (Or.inl hc),
        ihe hw.1.2 fun f as rs hc => h f as rs (Or.inr (Or.inl hc))⟩,
        ihk hw.2 fun f as rs hc => h f as rs (Or.inr (Or.inr hc))⟩
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hw ⊢
      exact ⟨⟨hw.1.1, ihb hw.1.2 fun f as rs hc => h f as rs (Or.inl hc)⟩,
        ihk hw.2 fun f as rs hc => h f as rs (Or.inr hc)⟩
  | call f args k ih =>
      simp only [callsLoopsAll, Bool.and_eq_true, Bool.true_and] at hw ⊢
      exact ⟨h _ _ _ (Or.inl ⟨rfl, rfl, rfl⟩), ih hw fun g as rs hc => h g as rs (Or.inr hc)⟩

/-- `callsLoopsAll` is monotone in the test on the calls and in the loop test. -/
theorem callsLoopsAll_mono {C' : String → List d.Ty → List d.Ty → Bool}
    {W' : List d.Ty → Bool} (hC : ∀ f as rs, C f as rs = true → C' f as rs = true)
    (hW : ∀ cs, W cs = true → W' cs = true) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : callsLoopsAll C W p = true) : callsLoopsAll C' W' p = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp ⊢
      exact ⟨ihb hp.1, ihk hp.2⟩
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp ⊢
      exact ⟨⟨iht hp.1.1, ihe hp.1.2⟩, ihk hp.2⟩
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp ⊢
      exact ⟨⟨hW _ hp.1.1, ihb hp.1.2⟩, ihk hp.2⟩
  | call _ _ _ ih =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp ⊢
      exact ⟨hC _ _ _ hp.1, ih hp.2⟩

/-- Every program passes `callsLoopsAll` at the tests that accept everything. -/
theorem callsLoopsAll_true {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    callsLoopsAll (fun _ _ _ => true) (fun _ => true) p = true := by
  induction p <;> simp_all [callsLoopsAll]

/-- A program of `opsNB P` at the loop test `W` passes `callsLoopsAll C W`: it has no
    `call`. -/
theorem callsLoopsAll_of_opsNB {P : d.Op → Bool} {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hp : opsNB P p W = true) : callsLoopsAll C W p = true := by
  induction p with
  | ret => rfl
  | var e k ih =>
      simp only [opsNB, Bool.and_eq_true] at hp
      exact ih hp.2
  | forLoop _ _ _ _ ihb ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [callsLoopsAll, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [callsLoopsAll, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [callsLoopsAll, hp.1.1, ihb hp.1.2, ihk hp.2, Bool.and_self]
  | call => simp [opsNB] at hp

/-- A program that passes `callsLoopsAll C W` passes `callsAll C`. -/
theorem callsAll_of_callsLoopsAll {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : callsLoopsAll C W p = true) : ChainTotal.callsAll C p = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [ChainTotal.callsAll, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [ChainTotal.callsAll, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [ChainTotal.callsAll, ihb hp.1.2, ihk hp.2, Bool.and_self]
  | call _ _ _ ih =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [ChainTotal.callsAll, hp.1, ih hp.2, Bool.and_self]

/-- A program that passes `callsLoopsAll C (fun _ => false)` has no exit-flag loop. -/
theorem whileFree_of_callsLoopsAll {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : callsLoopsAll C (fun _ => false) p = true) : p.whileFree = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.whileFree, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.whileFree, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop => simp [callsLoopsAll] at hp
  | call _ _ _ ih =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      exact ih hp.2

/-- An embedded straight-line program passes `callsLoopsAll C W`. -/
theorem callsLoopsAll_ofCom : {Γ : Ctxt d} → {t : d.Ty} → (c : Com d Γ t) →
    callsLoopsAll C W (NFProg.ofCom c) = true
  | _, _, .ret _ => rfl
  | _, _, .var _ c => callsLoopsAll_ofCom c

/-- A renamed program passes `callsLoopsAll C W` exactly when the source does. -/
theorem callsLoopsAll_rename? {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} {f : PRen Γ Δ} {q : NFProg d Δ ts}, NFProg.rename? f p = some q →
      callsLoopsAll C W q = callsLoopsAll C W p := by
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
      simp only [callsLoopsAll, ih hk]
  | forLoop count inits body k ihb ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, _, -, b', hb, k', hk, rfl⟩ := h
      simp only [callsLoopsAll, ihb hb, ihk hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, t', ht, e', he, k', hk, rfl⟩ := h
      simp only [callsLoopsAll, iht ht, ihe he, ihk hk]
  | whileLoop inits body k ihb ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb, k', hk, rfl⟩ := h
      simp only [callsLoopsAll, ihb hb, ihk hk]
  | call g args k ih =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, k', hk, rfl⟩ := h
      simp only [callsLoopsAll, ih hk]

/-- The splice of a body and a continuation that pass `callsLoopsAll C W` passes it. -/
theorem callsLoopsAll_seq? {Δ : Ctxt d} {rs : List d.Ty} (b : NFProg d Δ rs) :
    ∀ {Γ₀ : Ctxt d} {ts : List d.Ty} (k : NFProg d (rs ++ Γ₀) ts) {Γ : Ctxt d}
      {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ} {q : NFProg d Γ ts}, NFProg.seq? k b ρ θ = some q →
      callsLoopsAll C W b = true → callsLoopsAll C W k = true → callsLoopsAll C W q = true := by
  induction b with
  | ret vs =>
      intro Γ₀ ts k Γ ρ θ q h _ hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff] at h
      obtain ⟨_, -, h⟩ := h
      rw [callsLoopsAll_rename? C W k h, hk]
  | var e b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb', rfl⟩ := h
      have h' := ih k hb' hb hk
      exact h'
  | forLoop count inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [callsLoopsAll, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, _, -, body', hbody, b', hb', rfl⟩ := h
      simp only [callsLoopsAll, callsLoopsAll_rename? C W body hbody, hb.1, ih k hb' hb.2 hk,
        Bool.and_self]
  | ifThenElse cond thn els b _ _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [callsLoopsAll, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, t', ht, e', he, b', hb', rfl⟩ := h
      simp only [callsLoopsAll, callsLoopsAll_rename? C W thn ht, callsLoopsAll_rename? C W els he,
        hb.1.1, hb.1.2, ih k hb' hb.2 hk, Bool.and_self]
  | whileLoop inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [callsLoopsAll, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, body', hbody, b', hb', rfl⟩ := h
      simp only [callsLoopsAll, callsLoopsAll_rename? C W body hbody, hb.1.1, hb.1.2,
        ih k hb' hb.2 hk, Bool.and_self]
  | call f args b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [callsLoopsAll, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb', rfl⟩ := h
      simp only [callsLoopsAll, hb.1, ih k hb' hb.2 hk, Bool.and_self]

/-- **Inlining keeps `callsLoopsAll C W`** at a library without operation bodies whose call
    bodies pass it. -/
theorem callsLoopsAll_inline? (L : InlineLib d) (hL : ∀ o, L.op o = none)
    (hb : ∀ f as rs b, L.call f as rs = some b → callsLoopsAll C W b = true) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : callsLoopsAll C W p = true) :
    ∀ {q : NFProg d Γ ts}, NFProg.inline? L p = some q → callsLoopsAll C W q = true := by
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
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', k', hk', rfl⟩ := h
      simp only [callsLoopsAll, ihb hp.1 hb', ihk hp.2 hk', Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro q h
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t', ht', e', he', k', hk', rfl⟩ := h
      simp only [callsLoopsAll, iht hp.1.1 ht', ihe hp.1.2 he', ihk hp.2 hk', Bool.and_self]
  | whileLoop inits body k ihb ihk =>
      intro q h
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', k', hk', rfl⟩ := h
      simp only [callsLoopsAll, hp.1.1, ihb hp.1.2 hb', ihk hp.2 hk', Bool.and_self]
  | call f args k ih =>
      intro q h
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      obtain ⟨k', hk, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i b hbb
        exact callsLoopsAll_seq? C W b k' h (hb _ _ _ _ hbb) (ih hp.2 hk)
      · cases h
        simp only [callsLoopsAll, hp.1, ih hp.2 hk, Bool.and_self]

/-- **Dead-binding elimination keeps `callsLoopsAll C W`.** -/
theorem callsLoopsAll_dce {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : callsLoopsAll C W p = true) : callsLoopsAll C W (NFProg.dce p) = true := by
  induction p with
  | ret => rfl
  | var e k ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hk'
        rw [callsLoopsAll_rename? C W _ hk']
        exact ih hp
      · exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.dce, callsLoopsAll, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.dce, callsLoopsAll, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.dce, callsLoopsAll, hp.1.1, ihb hp.1.2, ihk hp.2, Bool.and_self]
  | call _ _ _ ih =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.dce, callsLoopsAll, hp.1, ih hp.2, Bool.and_self]

end Generic

/-- **The traversal of the e-graph pass keeps `callsLoopsAll C W`.** -/
theorem callsLoopsAll_nfGo {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d]
    (C : String → List d.Ty → List d.Ty → Bool) (W : List d.Ty → Bool)
    (R : CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric.RuleSet d) {Γ Δ : Ctxt d}
    {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S) (p : NFProg d Γ ts) :
    callsLoopsAll C W (CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo R ρ S p) =
      callsLoopsAll C W p := by
  induction p generalizing Δ S with
  | ret => rfl
  | var e k ih =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo]
      split <;> simp only [callsLoopsAll, ih]
  | forLoop _ _ _ _ ihb ihk =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, callsLoopsAll, ihb, ihk]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, callsLoopsAll, iht, ihe, ihk]
  | whileLoop _ _ _ ihb ihk =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, callsLoopsAll, ihb, ihk]
  | call _ _ _ ih =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, callsLoopsAll, ih]

/-! ## 2. The conversion between dialects -/

section MapCalls

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- A block spliced before continuations that return programs of `callsLoopsAll C W` gives a
    program of `callsLoopsAll C W`. -/
theorem callsLoopsAll_spliceNF? (C : String → List d'.Ty → List d'.Ty → Bool)
    (W : List d'.Ty → Bool) {ts : List d'.Ty} :
    {Δ : Ctxt d'} → {a : d'.Ty} → (blk : Com d' Δ a) →
    (k : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d' Δ' ts)) →
    (∀ {Δ' : Ctxt d'} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) (q : NFProg d' Δ' ts),
      k ren res = some q → callsLoopsAll C W q = true) →
    ∀ {q : NFProg d' Δ ts}, NFProg.spliceNF? blk k = some q → callsLoopsAll C W q = true
  | _, _, .ret v, _, hk, _, h => hk _ v _ h
  | _, _, .var _ blk, k, hk, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact callsLoopsAll_spliceNF? C W blk _ (fun ren res q hq => hk _ res q hq) hq'

/-- Carrying the first result type keeps `callsLoopsAll C W`. -/
theorem callsLoopsAll_castRetHead (C : String → List d.Ty → List d.Ty → Bool)
    (W : List d.Ty → Bool) {Δ : Ctxt d} {a b : d.Ty} {ts : List d.Ty} (h : a = b)
    (p : NFProg d Δ (a :: ts)) :
    callsLoopsAll C W (NFProg.castRetHead h p) = callsLoopsAll C W p := by
  subst h
  rfl

/-- **The conversion `map?` transports `callsLoopsAll`**: a call of the result is a call of
    the source with its signature mapped by `P.mapTy`, and an exit-flag loop of the result
    is one of the source with its carried types mapped by `P.mapTy`. -/
theorem callsLoopsAll_map? (P : PartialBlockLowering d d') (hT : P.RegionTypes)
    (C : String → List d'.Ty → List d'.Ty → Bool) (W : List d'.Ty → Bool) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : callsLoopsAll (fun f as rs => C f (as.map P.mapTy) (rs.map P.mapTy))
      (fun cs => W (cs.map P.mapTy)) p = true) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) {q : NFProg d' Δ (ts.map P.mapTy)},
      NFProg.map? P hT p ren = some q → callsLoopsAll C W q = true := by
  induction p with
  | ret vs =>
      intro Δ ren q h
      cases h
      rfl
  | var e k ih =>
      intro Δ ren q h
      obtain ⟨blk, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact callsLoopsAll_spliceNF? C W _ _ (fun ren' res q' hq' => ih hp _ hq') h
  | forLoop count inits body k ihb ihk =>
      intro Δ ren q h
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [callsLoopsAll, ihb hp.1 _ hb, ihk hp.2 _ hk, Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren q h
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [callsLoopsAll, iht hp.1.1 _ ht, ihe hp.1.2 _ he, ihk hp.2 _ hk, Bool.and_self]
  | whileLoop inits body k ihb ihk =>
      intro Δ ren q h
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [callsLoopsAll, callsLoopsAll_castRetHead, hp.1.1, ihb hp.1.2 _ hb, ihk hp.2 _ hk,
        Bool.and_self]
  | call f args k ih =>
      intro Δ ren q h
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [callsLoopsAll, hp.1, ih hp.2 _ hk, Bool.and_self]

end MapCalls

/-! ## 3. The select lowering -/

section Select

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectDenoteM d Option] [HasSelect d]
  (C : String → List d.Ty → List d.Ty → Bool) (W : List d.Ty → Bool)

omit [DialectDenoteM d Option] [HasSelect d] in
/-- A program `emitArm? p ren kont` returns passes `callsLoopsAll C W` when every program the
    continuation returns does: `emitArm?` binds the expressions of a straight-line arm. -/
theorem callsLoopsAll_emitArm? {ts : List d.Ty} {Γ : Ctxt d} {rs : List d.Ty}
    (p : NFProg d Γ rs) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ)
      (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
        Option (NFProg d Δ' ts)),
      (∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs) q,
        kont r res = some q → callsLoopsAll C W q = true) →
      ∀ q, NFProg.emitArm? p ren kont = some q → callsLoopsAll C W q = true := by
  induction p with
  | ret vs => intro Δ ren kont hk q hq; exact hk _ _ q hq
  | var e k ih =>
      intro Δ ren kont hk q hq
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact ih (Ctxt.Hom.lift ren) (fun r res => kont (fun v => r (.there v)) res)
        (fun r res q hq => hk _ res q hq) q' hq'
  | forLoop => intro _ _ _ _ q hq; simp [NFProg.emitArm?] at hq
  | ifThenElse => intro _ _ _ _ q hq; simp [NFProg.emitArm?] at hq
  | whileLoop => intro _ _ _ _ q hq; simp [NFProg.emitArm?] at hq
  | call => intro _ _ _ _ q hq; simp [NFProg.emitArm?] at hq

/-- The selects pass `callsLoopsAll C W` when every program the continuation returns does. -/
theorem callsLoopsAll_emitSels {ts : List d.Ty} : ∀ {Δ : Ctxt d} {rs : List d.Ty}
    (h : rs.all HasSelect.selects = true) (c : Var Δ (HasBitType.bit (d := d)))
    (va vb : HVector (fun t => Var Δ t) rs)
    (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg d Δ' ts),
    (∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs),
      callsLoopsAll C W (kont r res) = true) →
    callsLoopsAll C W (NFProg.emitSels h c va vb kont) = true
  | _, [], _, _, .nil, .nil, _, hk => hk _ _
  | _, _ :: _, h, c, .cons a va, .cons b vb, kont, hk => by
      rw [NFProg.emitSels, callsLoopsAll]
      exact callsLoopsAll_emitSels _ _ _ _ _ (fun r res => hk _ _)

/-- A program `lowerIte?` returns passes `callsLoopsAll C W` when every program the
    continuation returns does. -/
theorem callsLoopsAll_lowerIte? {ts : List d.Ty} {Δ : Ctxt d} {rs : List d.Ty}
    (c : Var Δ (HasBitType.bit (d := d))) (thn els : NFProg d Δ rs)
    (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg d Δ' ts)
    (hk : ∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs),
      callsLoopsAll C W (kont r res) = true)
    (q : NFProg d Δ ts) (hq : NFProg.lowerIte? c thn els kont = some q) :
    callsLoopsAll C W q = true := by
  unfold NFProg.lowerIte? at hq
  split at hq
  next =>
    refine callsLoopsAll_emitArm? C W thn _ _ (fun r1 va q1 hq1 => ?_) q hq
    refine callsLoopsAll_emitArm? C W els _ _ (fun r2 vb q2 hq2 => ?_) q1 hq1
    obtain rfl := Option.some.inj hq2
    exact callsLoopsAll_emitSels C W _ _ _ _ _ (fun r3 res => hk _ res)
  next => cases hq

/-- **The select lowering keeps `callsLoopsAll C W`**, along every renaming. -/
theorem callsLoopsAll_lowerSel {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : callsLoopsAll C W p = true) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ), callsLoopsAll C W (NFProg.lowerSel p ren) = true := by
  induction p with
  | ret => intro Δ ren; rfl
  | var e k ih => intro Δ ren; exact ih hp _
  | forLoop count inits body k ihb ihk =>
      intro Δ ren
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.lowerSel, callsLoopsAll, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.lowerSel]
      split
      · rename_i q hq
        exact callsLoopsAll_lowerIte? C W _ _ _ _ (fun _ _ => ihk hp.2 _) q hq
      · simp only [callsLoopsAll, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop inits body k ihb ihk =>
      intro Δ ren
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.lowerSel, callsLoopsAll, hp.1.1, ihb hp.1.2, ihk hp.2, Bool.and_self]
  | call f args k ih =>
      intro Δ ren
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [NFProg.lowerSel, callsLoopsAll, hp.1, ih hp.2, Bool.and_self]

end Select

/-! ## 4. The exit-flag loops of the translation -/

section Translation

open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

variable (W : List CryptoTy → Bool)

/-- The bindings of a translated operation keep the exit-flag loops of the continuation in
    `W`. -/
theorem emitRes_callsLoopsAll {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    {cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy))}
    (hcont : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (q : NFProg catCryptDialect Δ' (ts.map catTy)), cont σ' = some q →
        callsLoopsAll (fun _ _ _ => true) W q = true) :
    ∀ {Δ : Ctxt catCryptDialect} {t : NfTy} (h : t = s) (res : OpRes Δ t) (σ : TRd Γ Δ)
      (q : NFProg catCryptDialect Δ (ts.map catTy)), emitRes cont h res σ = some q →
      callsLoopsAll (fun _ _ _ => true) W q = true
  | _, _, _, .rd _, _, q, hq => hcont _ q hq
  | _, _, _, .expr _, _, _, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact hcont _ k' hk'
  | _, _, _, .expr1 _ _, _, _, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact hcont _ k' hk'
  | _, _, h, .bind _ _ rest, σ, _, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact emitRes_callsLoopsAll hcont h rest σ.wk k' hk'

/-- The bindings of `pinAll` keep the exit-flag loops of the program `k` gives in `W`. -/
theorem pinAll_callsLoopsAll {Γ : Ctxt nfDialect} {us : List CryptoTy} {ts : List NfTy}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) → Option (NFProg catCryptDialect Δ' us)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy)) (q : NFProg catCryptDialect Δ' us),
      k σ' ws = some q → callsLoopsAll (fun _ _ _ => true) W q = true)
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts)
    (q : NFProg catCryptDialect Δ us) (h : pinAll k σ rs = some q) :
    callsLoopsAll (fun _ _ _ => true) W q = true :=
  pinAll_elim (M := fun {_} _ _ q => callsLoopsAll (fun _ _ _ => true) W q = true)
    (fun σ _ ws q _ hq => hk σ ws q hq) (fun _ _ _ _ _ ih => ih) σ rs q h

/-- **The translation transports the exit-flag loops along `catTy`**: an exit-flag loop of
    a program `nfToCatExt` returns is the translation of one of the source, with its carried
    types mapped by `catTy`. -/
theorem nfToCatExt_callsLoopsAll (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts)
    (hp : callsLoopsAll (fun _ _ _ => true) (fun cs => W (cs.map catTy)) p = true) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (q : NFProg catCryptDialect Δ (ts.map catTy)),
      nfToCatExt D p σ = some q → callsLoopsAll (fun _ _ _ => true) W q = true := by
  induction p with
  | ret vs =>
      intro Δ σ q h
      refine pinAll_callsLoopsAll W ?_ σ _ q h
      intro _ _ _ q' hq'
      cases hq'
      rfl
  | var e k ih =>
      intro Δ σ q h
      have hk : callsLoopsAll (fun _ _ _ => true) (fun cs => W (cs.map catTy)) k = true := hp
      obtain ⟨op, rfl, args⟩ := e
      change emitOp D (fun σ' => nfToCatExt D k σ') σ op rfl args = some q at h
      unfold emitOp at h
      split at h
      · rename_i res hres
        exact emitRes_callsLoopsAll W (fun σ' q' hq' => ih hk σ' q' hq') rfl res σ q h
      · obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨g, bs, rds⟩ := c
        dsimp only at h
        unfold emitCall at h
        refine pinAll_callsLoopsAll W ?_ σ rds q h
        intro _ _ _ q' hq'
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq'
        exact ih hk _ k' hk'
  | @forLoop _ cs _ count inits body k ihb ihk =>
      intro Δ σ q h
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      refine pinAll_callsLoopsAll W (ts := .word 64 :: cs) ?_ σ _ q h
      intro _ _ _ q' hq'
      obtain ⟨b', hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq'
      simp only [callsLoopsAll, ihb hp.1 _ b' hb, ihk hp.2 _ k' hk, Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ σ q h
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [nfToCatExt] at h
      split at h
      · obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [callsLoopsAll, iht hp.1.1 _ t' ht, ihe hp.1.2 _ e' he, ihk hp.2 _ k' hk,
          Bool.and_self]
      · cases h
  | @whileLoop _ cs _ inits body k ihb ihk =>
      intro Δ σ q h
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      refine pinAll_callsLoopsAll W (ts := cs) ?_ σ _ q h
      intro _ _ _ q' hq'
      obtain ⟨b', hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq'
      simp only [callsLoopsAll, hp.1.1, ihb hp.1.2 _ b' hb, ihk hp.2 _ k' hk, Bool.and_self]
  | call f args k _ =>
      intro Δ σ q h
      cases h

/-- A declaration at a signature of words and word arrays has an image in `jasminDialect`
    at a signature of `wordSig`. -/
theorem wordSig_of_extDecl {d : ExtDecl} (h : d.wordSig = true) :
    JasminLprogExport.ExportRegions.wordSig
      ((d.args.map catTy).map CryptoToJasminCom.mapTy)
      ([catTy d.ret].map CryptoToJasminCom.mapTy) = true := by
  have hty : ∀ t : NfTy, wordArrTy t = true →
      JasminLprogExport.ExportRegions.callArgTy (CryptoToJasminCom.mapTy (catTy t)) = true ∧
        JasminLprogExport.ExportRegions.callResTy
          [CryptoToJasminCom.mapTy (catTy t)] = true := by
    intro t ht
    unfold wordArrTy at ht
    split at ht
    · exact ⟨rfl, rfl⟩
    · cases t with
      | int => exact ⟨rfl, rfl⟩
      | word w =>
          by_cases hw : w = 64
          · subst hw
            exact ⟨rfl, rfl⟩
          · simp [ImpToNF.hax64NFWordTy, hw] at ht
      | _ => simp [ImpToNF.hax64NFWordTy] at ht
  simp only [ExtDecl.wordSig, wordArrSig, Bool.and_eq_true, List.all_eq_true] at h
  simp only [JasminLprogExport.ExportRegions.wordSig, Bool.and_eq_true, List.all_eq_true,
    List.map_map, List.mem_map, List.map_cons, List.map_nil]
  refine ⟨?_, (hty _ h.2).2⟩
  rintro _ ⟨t, ht, rfl⟩
  exact (hty t (h.1 t ht)).1

end Translation

/-! ## 5. The range stage, the montify pass, the inlining step and the field dialect step -/

/-- **The traversal of the range stage keeps `callsLoopsAll C W`.** -/
theorem callsLoopsAll_rangeGo (C : String → List JasminTy → List JasminTy → Bool)
    (W : List JasminTy → Bool) : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (A : _)
    (len : Nat) (p : NFProg jasminDialect Γ ts),
    callsLoopsAll C W (CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeGo A len p) =
      callsLoopsAll C W p
  | _, _, _, _, .ret _ => rfl
  | _, _, _, _, .var _ k => by
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeGo, callsLoopsAll,
        callsLoopsAll_rangeGo C W _ _ k]
  | _, _, _, _, .forLoop _ _ body k => by
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeGo, callsLoopsAll,
        callsLoopsAll_rangeGo C W _ _ body, callsLoopsAll_rangeGo C W _ _ k]
  | _, _, _, _, .ifThenElse _ thn els k => by
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeGo, callsLoopsAll,
        callsLoopsAll_rangeGo C W _ _ thn, callsLoopsAll_rangeGo C W _ _ els,
        callsLoopsAll_rangeGo C W _ _ k]
  | _, _, _, _, .whileLoop _ body k => by
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeGo, callsLoopsAll,
        callsLoopsAll_rangeGo C W _ _ body, callsLoopsAll_rangeGo C W _ _ k]
  | _, _, _, _, .call _ _ k => by
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeGo, callsLoopsAll,
        callsLoopsAll_rangeGo C W _ _ k]

section Montify

open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (w64)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32 (mont32Cert)

section Rewrite

variable {p : Nat} (h : mont32Cert p = true) (C : String → List JasminTy → List JasminTy → Bool)
  (W : List JasminTy → Bool)

/-- A conversion calls the reduce-multiply head at two words before its continuation. -/
theorem callsLoopsAll_convProg (hm : C (montHead p) [w64, w64] [w64] = true)
    {Θ : Ctxt jasminDialect} (x : Var Θ w64) (j : ℤ) {us : List JasminTy}
    {k : NFProg jasminDialect (w64 :: w64 :: Θ) us} (hk : callsLoopsAll C W k = true) :
    callsLoopsAll C W (convProg h x j k) = true := by
  simp only [convProg, callsLoopsAll, hm, hk, Bool.and_self]

theorem callsLoopsAll_resConv (hm : C (montHead p) [w64, w64] [w64] = true)
    {Θ : Ctxt jasminDialect} (v : Var Θ w64) (k d : ℤ) {us : List JasminTy}
    {kk : BindK Θ w64 us}
    (hk : ∀ {Θ' : Ctxt jasminDialect} (g : Ctxt.Hom Θ Θ') r (q : NFProg jasminDialect Θ' us),
      kk g r = some q → callsLoopsAll C W q = true)
    {q : NFProg jasminDialect Θ us} (hq : resConv h v k d kk = some q) :
    callsLoopsAll C W q = true := by
  unfold resConv at hq
  split at hq
  · exact hk _ _ _ hq
  · obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    exact callsLoopsAll_convProg h C W hm _ _ (hk _ _ _ hq')

theorem callsLoopsAll_fieldRes (hm : C (montHead p) [w64, w64] [w64] = true)
    {Γ Θ : Ctxt jasminDialect} {ρ : MRen Γ Θ} {g : String} {as us : List JasminTy}
    {args : HVector (fun t => Var Θ t) as} {k d : ℤ} {kk : CallK Γ [w64] us}
    (hg : C g as [w64] = true)
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen ([w64] ++ Γ) Θ')
      (q : NFProg jasminDialect Θ' us), kk ρ' = some q → callsLoopsAll C W q = true)
    {q : NFProg jasminDialect Θ us} (hq : fieldRes h ρ g args k d kk = some q) :
    callsLoopsAll C W q = true := by
  obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
  simp only [callsLoopsAll, hg,
    callsLoopsAll_resConv h C W hm _ _ _ (fun _ _ q' hq' => hk _ q' hq') hq0, Bool.and_self]

omit h in
theorem callsLoopsAll_opaqueArm {Γ Θ : Ctxt jasminDialect} {f : String}
    {as rs us : List JasminTy} {args : HVector (fun t => Var Γ t) as} {ρ : MRen Γ Θ}
    {kk : CallK Γ rs us} (hf : C f as rs = true)
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen (rs ++ Γ) Θ')
      (q : NFProg jasminDialect Θ' us), kk ρ' = some q → callsLoopsAll C W q = true)
    {q : NFProg jasminDialect Θ us} (hq : opaqueArm f args ρ kk = some q) :
    callsLoopsAll C W q = true := by
  obtain ⟨_, -, hq⟩ := Option.bind_eq_some_iff.mp hq
  obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
  simp only [callsLoopsAll, hf, hk _ _ hk', Bool.and_self]

theorem callsLoopsAll_binArm (hm : C (montHead p) [w64, w64] [w64] = true)
    {Γ Θ : Ctxt jasminDialect} {f : String} {a b : Var Γ w64} {ρ : MRen Γ Θ} {d : ℤ}
    {us : List JasminTy} {kk : CallK Γ [w64] us} (hf : C f [w64, w64] [w64] = true)
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen ([w64] ++ Γ) Θ')
      (q : NFProg jasminDialect Θ' us), kk ρ' = some q → callsLoopsAll C W q = true)
    {q : NFProg jasminDialect Θ us} (hq : binArm h f a b ρ d kk = some q) :
    callsLoopsAll C W q = true := by
  unfold binArm at hq
  split at hq
  · split at hq
    · split at hq
      · exact callsLoopsAll_fieldRes h C W hm hm hk hq
      · split at hq
        · exact callsLoopsAll_fieldRes h C W hm hf hk hq
        · cases hq
    · exact callsLoopsAll_opaqueArm C W hf hk hq
  · exact callsLoopsAll_opaqueArm C W hf hk hq

theorem callsLoopsAll_unArm (hm : C (montHead p) [w64, w64] [w64] = true)
    {Γ Θ : Ctxt jasminDialect} {f : String} {a : Var Γ w64} {ρ : MRen Γ Θ} {d : ℤ}
    {us : List JasminTy} {kk : CallK Γ [w64] us} (hf : C f [w64] [w64] = true)
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen ([w64] ++ Γ) Θ')
      (q : NFProg jasminDialect Θ' us), kk ρ' = some q → callsLoopsAll C W q = true)
    {q : NFProg jasminDialect Θ us} (hq : unArm h f a ρ d kk = some q) :
    callsLoopsAll C W q = true := by
  unfold unArm at hq
  split at hq
  · split at hq
    · split at hq
      · exact callsLoopsAll_fieldRes h C W hm hm hk hq
      · split at hq
        · exact callsLoopsAll_fieldRes h C W hm hf hk hq
        · cases hq
    · exact callsLoopsAll_opaqueArm C W hf hk hq
  · exact callsLoopsAll_opaqueArm C W hf hk hq

/-- A call the rewriter accepts makes its own symbol at its own signature, the
    reduce-multiply head at two words, and the calls of its continuation. -/
theorem callsLoopsAll_callArm (hm : C (montHead p) [w64, w64] [w64] = true)
    {Γ Θ : Ctxt jasminDialect} {f : String} {us as rs : List JasminTy}
    {args : HVector (fun t => Var Γ t) as} {ρ : MRen Γ Θ} {d : ℤ} {kk : CallK Γ rs us}
    (hf : C f as rs = true)
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen (rs ++ Γ) Θ')
      (q : NFProg jasminDialect Θ' us), kk ρ' = some q → callsLoopsAll C W q = true)
    {q : NFProg jasminDialect Θ us} (hq : callArm h f args ρ d kk = some q) :
    callsLoopsAll C W q = true := by
  unfold callArm at hq
  split at hq
  · rename_i hs
    obtain ⟨h1, h2⟩ := hs
    subst h1 h2
    exact callsLoopsAll_binArm h C W hm hf hk hq
  · split at hq
    · rename_i _ hs
      obtain ⟨h1, h2⟩ := hs
      subst h1 h2
      exact callsLoopsAll_unArm h C W hm hf hk hq
    · exact callsLoopsAll_opaqueArm C W hf hk hq

theorem callsLoopsAll_varConv (hm : C (montHead p) [w64, w64] [w64] = true)
    {Θ : Ctxt jasminDialect} {d : ℤ} {us : List JasminTy} {t : JasminTy}
    {kk : BindK (t :: Θ) t us}
    (hk : ∀ {Θ' : Ctxt jasminDialect} (g : Ctxt.Hom (t :: Θ) Θ') r
      (q : NFProg jasminDialect Θ' us), kk g r = some q → callsLoopsAll C W q = true)
    {q : NFProg jasminDialect (t :: Θ) us} (hq : varConv h d kk = some q) :
    callsLoopsAll C W q = true := by
  unfold varConv at hq
  split at hq
  · exact hk _ _ _ hq
  · cases t with
    | reg w =>
      by_cases hw : w = 64
      · subst hw
        obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
        exact callsLoopsAll_convProg h C W hm _ _ (hk _ _ _ hq')
      · simp [wordConv, hw] at hq
    | _ => simp [wordConv] at hq

/-- **The rewriter keeps `callsLoopsAll C W`** when `C` holds at the reduce-multiply head at
    two words: every call it returns is a call of the source at its signature or a call of
    that head, and every exit-flag loop is one of the source at its carried types. -/
theorem callsLoopsAll_montifyAux (hm : C (montHead p) [w64, w64] [w64] = true) :
    {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    (prog : NFProg jasminDialect Γ ts) → (H : DegHint) → {Θ : Ctxt jasminDialect} →
    (ρ : MRen Γ Θ) → (q : NFProg jasminDialect Θ ts) → callsLoopsAll C W prog = true →
      montifyAux h prog H ρ = some q → callsLoopsAll C W q = true
  | _, _, .ret _, _, _, _, _, _, hq => by
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hq
      rfl
  | _, _, .var e k, H, _, ρ, q, hp, hq => by
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
      exact callsLoopsAll_varConv h C W hm
        (fun _ _ q' hq' => callsLoopsAll_montifyAux hm k _ _ q' hp hq') hq0
  | _, _, .forLoop count inits body k, H, _, ρ, q, hp, hq => by
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hb', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [callsLoopsAll, callsLoopsAll_montifyAux hm body _ _ _ hp.1 hb',
        callsLoopsAll_montifyAux hm k _ _ _ hp.2 hk', Bool.and_self]
  | _, _, .ifThenElse cond thn els k, H, _, ρ, q, hp, hq => by
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨t', ht', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨e', he', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [callsLoopsAll, callsLoopsAll_montifyAux hm thn _ _ _ hp.1.1 ht',
        callsLoopsAll_montifyAux hm els _ _ _ hp.1.2 he',
        callsLoopsAll_montifyAux hm k _ _ _ hp.2 hk', Bool.and_self]
  | _, _, .whileLoop inits body k, H, _, ρ, q, hp, hq => by
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hb', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [callsLoopsAll, hp.1.1, callsLoopsAll_montifyAux hm body _ _ _ hp.1.2 hb',
        callsLoopsAll_montifyAux hm k _ _ _ hp.2 hk', Bool.and_self]
  | _, _, .call f args k, H, _, ρ, q, hp, hq => by
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      unfold montifyAux at hq
      split at hq
      · cases hq
      · exact callsLoopsAll_callArm h C W hm hp.1
          (fun ρ' q' hk => callsLoopsAll_montifyAux hm k _ ρ' q' hp.2 hk) hq

theorem callsLoopsAll_entryConv (hm : C (montHead p) [w64, w64] [w64] = true)
    {Γ : Ctxt jasminDialect} {us : List JasminTy}
    (kk : ∀ {Θ : Ctxt jasminDialect}, MRen Γ Θ → Option (NFProg jasminDialect Θ us))
    (hk : ∀ {Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ) (q : NFProg jasminDialect Θ us),
      kk ρ = some q → callsLoopsAll C W q = true) :
    ∀ (vs : List (Var Γ w64 × ℤ)) {Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ)
      (q : NFProg jasminDialect Θ us), entryConv h kk vs ρ = some q → callsLoopsAll C W q = true
  | [], _, ρ, q, hq => hk ρ q hq
  | (v, d) :: vs, _, ρ, q, hq => by
      obtain ⟨x, -, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨q1, hq1, rfl⟩ := Option.map_eq_some_iff.mp hq
      exact callsLoopsAll_convProg h C W hm _ _ (callsLoopsAll_entryConv hm kk hk vs _ q1 hq1)

theorem callsLoopsAll_montify
    (hm : montTag? (montHead p) = some p → C (montHead p) [w64, w64] [w64] = true)
    (pd : List ℤ) (H : DegHint) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (prog : NFProg jasminDialect Γ ts) (hp : callsLoopsAll C W prog = true)
    {q : NFProg jasminDialect Γ ts} (hq : montify h pd H prog = some q) :
    callsLoopsAll C W q = true := by
  unfold montify at hq
  split at hq
  · rename_i hmt
    exact callsLoopsAll_entryConv h C W (hm hmt) _
      (fun ρ q' hq' => callsLoopsAll_montifyAux h C W (hm hmt) prog H ρ q' hp hq') _ _ q hq
  · cases hq

end Rewrite

variable (C : String → List JasminTy → List JasminTy → Bool) (W : List JasminTy → Bool)

/-- A body of a reduce-multiply head passes `callsLoopsAll C W`: it is an embedded
    straight-line program. -/
theorem callsLoopsAll_montBody {f : String} {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (hb : montBody f as rs = some b) :
    callsLoopsAll C W b = true := by
  unfold montBody at hb
  split at hb
  · rename_i q _
    split at hb
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      cases hb
      have hr : callsLoopsAll C W (redcMulProg q) = true := by
        unfold redcMulProg
        exact callsLoopsAll_ofCom (d := jasminDialect) C W _
      exact hr
    · cases hb
  · cases hb

/-- A montify round keeps `callsLoopsAll C W`. -/
theorem callsLoopsAll_montifyAt {p : Nat} (h : mont32Cert p = true)
    (hm : montTag? (montHead p) = some p → C (montHead p) [w64, w64] [w64] = true)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts)
    (hp : callsLoopsAll C W prog = true) : callsLoopsAll C W (montifyAt h prog) = true := by
  unfold montifyAt
  split
  · rename_i q hq
    split
    · rename_i q' hq'
      split
      · exact callsLoopsAll_inline? C W montLibJ (fun _ => rfl)
          (fun _ _ _ _ hb => callsLoopsAll_montBody C W hb) q
          (callsLoopsAll_montify h C W hm _ _ prog hp hq) hq'
      · exact hp
    · exact hp
  · exact hp

/-- The montify rounds at a list of moduli keep `callsLoopsAll C W`. -/
theorem callsLoopsAll_montifyMods
    (hm : ∀ p, montTag? (montHead p) = some p → C (montHead p) [w64, w64] [w64] = true)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} :
    ∀ (ps : List Nat) (prog : NFProg jasminDialect Γ ts), callsLoopsAll C W prog = true →
      callsLoopsAll C W (montifyMods ps prog) = true
  | [], _, hp => hp
  | p :: ps, prog, hp => by
      refine callsLoopsAll_montifyMods hm ps _ ?_
      split
      · rename_i h
        exact callsLoopsAll_montifyAt C W h (hm p) prog hp
      · exact hp

/-- **The montify pass keeps `callsLoopsAll C W`** when `C` holds at every reduce-multiply
    head at two words. -/
theorem callsLoopsAll_montifyPass
    (hm : ∀ p, montTag? (montHead p) = some p → C (montHead p) [w64, w64] [w64] = true)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts)
    (hp : callsLoopsAll C W prog = true) : callsLoopsAll C W (montifyPass prog) = true :=
  callsLoopsAll_montifyMods C W hm _ prog hp

end Montify

/-- **A template body passes `callsLoopsAll C W`**: every body of `fieldBody` is built by
    `NFProg.ofCom`. -/
theorem callsLoopsAll_fieldBody (C : String → List JasminTy → List JasminTy → Bool)
    (W : List JasminTy → Bool) {f : String} {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (h : fieldBody f as rs = some b) :
    callsLoopsAll C W b = true := by
  unfold fieldBody at h
  split at h
  · rename_i m p _
    split at h
    · split at h
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        cases h
        cases m <;> exact callsLoopsAll_ofCom (d := jasminDialect) C W _
      · cases h
    · unfold FieldWideDecl.wideBody at h
      split at h
      · rename_i m' p' _
        split at h
        · split at h
          · rename_i hs
            obtain ⟨rfl, rfl⟩ := hs
            cases h
            exact callsLoopsAll_ofCom (d := jasminDialect) C W _
          · cases h
        · split at h
          · split at h
            · rename_i hs
              obtain ⟨rfl, rfl⟩ := hs
              cases h
              exact callsLoopsAll_ofCom (d := jasminDialect) C W _
            · cases h
          · cases h
      · cases h
  · cases h

/-- **The inlining step keeps `callsLoopsAll C W`.** -/
theorem callsLoopsAll_fieldInline (C : String → List JasminTy → List JasminTy → Bool)
    (W : List JasminTy → Bool) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (hp : callsLoopsAll C W p = true)
    (hq : (fieldInlineStep Γ ts).run p = some q) : callsLoopsAll C W q = true := by
  change (NFProg.inline? fieldLibJ p).bind
    (fun q => if fieldFree q then some q else none) = some q at hq
  obtain ⟨q', hq', h⟩ := Option.bind_eq_some_iff.mp hq
  split at h
  · cases h
    exact callsLoopsAll_inline? C W fieldLibJ (fun _ => rfl)
      (fun _ _ _ _ hb => callsLoopsAll_fieldBody C W hb) p hp hq'
  · cases h

/-- **The field dialect step keeps `callsLoopsAll C W`**: it inlines lowered bodies, which
    have no exit-flag loop (`fieldBodyD_whileFree`) and no call (`fieldBodyD_callsAll`). -/
theorem callsLoopsAll_fieldDialect (C : String → List JasminTy → List JasminTy → Bool)
    (W : List JasminTy → Bool) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (hp : callsLoopsAll C W p = true)
    (hq : (fieldDialectStep Γ ts).run p = some q) : callsLoopsAll C W q = true := by
  change (if fieldFree p then some p else
    (NFProg.inline? fieldLibD p).bind fun q => if fieldFree q then some q else none) =
      some q at hq
  split at hq
  · cases hq
    exact hp
  · obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hq
    split at hif
    · cases hif
      exact callsLoopsAll_inline? C W fieldLibD (fun _ => rfl)
        (fun _ _ _ b hb => callsLoopsAll_of_calls C W b (fieldBodyD_whileFree hb)
          fun _ _ _ hc => calls_of_callsAll C b (fieldBodyD_callsAll C hb) hc) p hp hq0
    · cases hif

/-! ## 6. The output of the chain -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (wordSig wordCalls
  isRegTy)
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportComplete (whileRegB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps (widthPos)

/-- A program whose exit-flag loops carry register types passes `whileRegB`. -/
theorem whileRegB_of_callsLoopsAll (C : String → List JasminTy → List JasminTy → Bool)
    {W : List JasminTy → Bool} (hW : ∀ cs, W cs = true → cs.all isRegTy = true)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (hp : callsLoopsAll C W p = true) : whileRegB p = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [whileRegB, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [whileRegB, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [whileRegB, hW _ hp.1.1, ihb hp.1.2, ihk hp.2, Bool.and_self]
  | call _ _ _ ih =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      exact ih hp.2

/-- A program whose calls are at signatures of `wordSig` passes `wordCalls`. -/
theorem wordCalls_of_callsLoopsAll (W : List JasminTy → Bool) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (hp : callsLoopsAll (fun _ as rs => wordSig as rs) W p = true) : wordCalls p = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [wordCalls, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [wordCalls, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [wordCalls, ihb hp.1.2, ihk hp.2, Bool.and_self]
  | call _ _ _ ih =>
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      simp only [wordCalls, hp.1, ih hp.2, Bool.and_self]

open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)

/-- The types of `whileCarryOkB` map along `catTy` and the conversion to register types of
    positive width. -/
theorem regLoop_of_whileCarry {cs : List NfTy}
    (h : cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB = true) :
    ((cs.map catTy).map catToJasmin.mapTy).all (fun s => isRegTy s && widthPos s) = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp_apply] at h ⊢
  intro t ht
  have := h t ht
  cases t with
  | word w =>
      change (isRegTy (.reg w) && widthPos (.reg w)) = true
      simpa [CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB, isRegTy, widthPos] using this
  | int | uint _ | bit => rfl
  | _ => simp [CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB] at this

/-- **Every program `extChain` returns has its exit-flag loops at register types of positive
    width and calls only at signatures of `wordSig`**, at every list of declarations and on
    every input whose flattened form has its exit-flag loops at types of `whileCarryOkB`:
    dead-binding elimination keeps the loops (`callsLoopsAll_dce`), the translation maps
    their carried types along `catTy` (`nfToCatExt_callsLoopsAll`) and declares its calls at
    signatures of words and word arrays (`nfToCatExt_calls`), the reduce-multiply heads of
    the montify pass are at two words, and every later step keeps `callsLoopsAll`. -/
theorem extChain_callsLoopsAll (D : List ExtDecl) {Γ : Ctxt nfDialect} {t : NfTy}
    {p : NFProg nfDialect Γ [t]} {q : NFProg jasminDialect (mapCtx (Γ.map catTy))
      [mapTy (catTy t)]} (h : (extChain D Γ t).run p = some q)
    (hw : ∀ p1, flatSame (NFProg.abortElim NfOp.isAbort p) = some p1 →
      callsLoopsAll (fun _ _ _ => true)
        (fun cs => cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB) p1 = true) :
    callsLoopsAll (fun _ as rs => wordSig as rs)
      (fun cs => cs.all fun s => isRegTy s && widthPos s) q = true := by
  simp only [extChain, extChainCore, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨p0, hp0, p1, hp1, p2, hp2, p3, hp3, r, hr, r1, hr1, j, hj, j1, hj1, j2, hj2, j3, hj3,
    j4, hj4, j5, hj5, hq⟩ := h
  obtain rfl := Option.some.inj hq
  change some (NFProg.abortElim NfOp.isAbort p) = some p0 at hp0
  cases hp0
  change flatSame (NFProg.abortElim NfOp.isAbort p) = some p1 at hp1
  change (if outTyB t then some p1 else none) = some p2 at hp2
  change some (NFProg.dce p2) = some p3 at hp3
  change nfToCatExt (fieldDeclsFor D p3) p3 TRd.id = some r at hr
  have hp2' : p1 = p2 := by split at hp2 <;> cases hp2; rfl
  subst hp2'
  cases hp3; cases hr1; cases hj1; cases hj3; cases hj4; cases hj5
  have hd := callsLoopsAll_mono _ _ (fun _ _ _ h => h) (fun cs h => regLoop_of_whileCarry h)
    _ (callsLoopsAll_dce _ _ p1 (hw p1 hp1))
  have h0 : callsLoopsAll (fun _ as rs => wordSig ((as.map catToJasmin.mapTy))
      (rs.map catToJasmin.mapTy))
      (fun cs => (cs.map catToJasmin.mapTy).all fun s => isRegTy s && widthPos s) r = true := by
    refine callsLoopsAll_of_loops _ _ r
      (nfToCatExt_callsLoopsAll _ _ (NFProg.dce p1) hd TRd.id r hr) ?_
    intro f as rs hc
    obtain ⟨d, -, -, rfl, rfl, hw⟩ := nfToCatExt_calls _ _ TRd.id r hr f as rs hc
    exact wordSig_of_extDecl hw
  have h1 := (callsLoopsAll_nfGo (d := catCryptDialect) _ _ catRules (Ctxt.Hom.id _) (∅, ∅)
    r).trans h0
  have h2 := callsLoopsAll_map? catToJasmin catToJasmin_regionTypes
    (fun _ as rs => wordSig as rs) (fun cs => cs.all fun s => isRegTy s && widthPos s) _ h1 _ hj
  have h3 := callsLoopsAll_montifyPass _ _ (fun _ _ => rfl) _ h2
  have h4 := callsLoopsAll_fieldDialect _ _ h3 hj2
  have h5 := callsLoopsAll_lowerSel _ _ _ h4 (fun v => v)
  unfold CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.aegraphOptNF
    CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeNF
  rw [callsLoopsAll_nfGo (d := jasminDialect), callsLoopsAll_rangeGo]
  exact h5

/-- **Every program `extChain` returns passes `whileRegB`.** -/
theorem extChain_whileRegB (D : List ExtDecl) {Γ : Ctxt nfDialect} {t : NfTy}
    {p : NFProg nfDialect Γ [t]} {q : NFProg jasminDialect (mapCtx (Γ.map catTy))
      [mapTy (catTy t)]} (h : (extChain D Γ t).run p = some q)
    (hw : ∀ p1, flatSame (NFProg.abortElim NfOp.isAbort p) = some p1 →
      callsLoopsAll (fun _ _ _ => true)
        (fun cs => cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB) p1 = true) :
    whileRegB q = true :=
  whileRegB_of_callsLoopsAll _ (fun cs hc => by
      simp only [List.all_eq_true, Bool.and_eq_true] at hc ⊢
      exact fun s hs => (hc s hs).1)
    q (extChain_callsLoopsAll D h hw)

/-- **Every program `extChain` returns passes `wordCalls`.** -/
theorem extChain_wordCalls (D : List ExtDecl) {Γ : Ctxt nfDialect} {t : NfTy}
    {p : NFProg nfDialect Γ [t]} {q : NFProg jasminDialect (mapCtx (Γ.map catTy))
      [mapTy (catTy t)]} (h : (extChain D Γ t).run p = some q)
    (hw : ∀ p1, flatSame (NFProg.abortElim NfOp.isAbort p) = some p1 →
      callsLoopsAll (fun _ _ _ => true)
        (fun cs => cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB) p1 = true) :
    wordCalls q = true :=
  wordCalls_of_callsLoopsAll _ q (extChain_callsLoopsAll D h hw)

/-! ## 7. The operations of the e-graph passes -/

section AegraphOps

open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.TraitRules

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op]

/-- The operations of the bindings an alternative emits satisfy `Q`. -/
def altOpsB (Q : d.Op → Bool) {Δ : Ctxt d} {s : d.Ty} : Alt Δ s → Bool
  | .var _ => true
  | .one e => Q e.op
  | .two e1 e2 => Q e1.op && Q e2.op

/-- An alternative is a variable, or one binding whose operation satisfies `C`. -/
def altConstB (C : d.Op → Bool) {Δ : Ctxt d} {s : d.Ty} : Alt Δ s → Bool
  | .var _ => true
  | .one e => C e.op
  | .two _ _ => false

/-- The alternatives the rules of `R` give an expression whose operation satisfies `Q` emit
    bindings whose operations satisfy `Q`. -/
def RulesOps (R : RuleSet d) (Q : d.Op → Bool) : Prop :=
  ∀ (D : Defs d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s), Q e.op = true →
    ∀ a ∈ R.alts D e, altOpsB Q a = true

omit [TyDenote d.Ty] [DecidableEq d.Ty] [DialectDenote d] [DecidableEq d.Op] in
/-- An alternative of `altConstB C` emits bindings of `Q` when every expression of its type
    whose operation satisfies `C` has an operation of `Q`. -/
theorem altOpsB_of_altConstB {C Q : d.Op → Bool} {Δ : Ctxt d} {s : d.Ty}
    (hC : ∀ e' : Expr d Δ s, C e'.op = true → Q e'.op = true) :
    ∀ a : Alt Δ s, altConstB C a = true → altOpsB Q a = true
  | .var _, _ => rfl
  | .one e', h => hC e' h
  | .two _ _, h => absurd h Bool.false_ne_true

/-- The involution rule emits variables only. -/
theorem involutionRule_altConst (C : d.Op → Bool) (I : Involution d) (D : Defs d)
    {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) :
    ∀ a ∈ (involutionRule I).apply D e, altConstB C a = true := by
  intro alt ha
  change alt ∈ invApply I D e at ha
  unfold invApply at ha
  split at ha
  · split at ha
    · split at ha
      · split at ha
        · obtain ⟨x, -, rfl⟩ := mem_varAlts ha
          rfl
        · simp at ha
      · simp at ha
    · simp at ha
  · simp at ha

omit [DecidableEq d.Op] in
/-- The idempotence rule emits variables only. -/
theorem idempotentRule_altConst (C : d.Op → Bool) (I : Idempotent d) (D : Defs d)
    {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) :
    ∀ a ∈ (idempotentRule I).apply D e, altConstB C a = true := by
  intro alt ha
  change alt ∈ idemApply I e at ha
  unfold idemApply at ha
  split at ha
  · split at ha
    · split at ha
      · obtain ⟨x, -, rfl⟩ := mem_varAlts ha
        rfl
      · simp at ha
    · simp at ha
  · simp at ha

omit [DecidableEq d.Op] in
/-- The copy rule emits variables only. -/
theorem copyRule_altConst (C : d.Op → Bool) (K : CopyOp d) (D : Defs d) {Δ : Ctxt d}
    {s : d.Ty} (e : Expr d Δ s) : ∀ a ∈ (copyRule K).apply D e, altConstB C a = true := by
  intro alt ha
  change alt ∈ copyApply K e at ha
  unfold copyApply at ha
  split at ha
  · split at ha
    · obtain ⟨x, -, rfl⟩ := mem_varAlts ha
      rfl
    · simp at ha
  · simp at ha

omit [DecidableEq d.Op] in
/-- The self-cancellation rule emits the binding of `zero op`. -/
theorem selfCancelRule_altConst (C : d.Op → Bool) (I : SelfCancel d)
    (hz : ∀ op, I.isCancel op = true → C (I.zero op) = true) (D : Defs d) {Δ : Ctxt d}
    {s : d.Ty} (e : Expr d Δ s) :
    ∀ a ∈ (selfCancelRule I).apply D e, altConstB C a = true := by
  intro alt ha
  change alt ∈ cancelApply I e at ha
  unfold cancelApply at ha
  split at ha
  · rename_i hc
    split at ha
    · split at ha
      · simp only [List.mem_singleton] at ha
        subst ha
        exact hz _ hc
      · simp at ha
    · simp at ha
  · simp at ha

omit [DecidableEq d.Op] in
/-- Constant folding emits the binding of a constant-like operation. -/
theorem constFoldRule_altConst {T : OpTraits d} (C : d.Op → Bool) (R : ConstReify d T)
    (sel : d.Op → Bool) (hC : ∀ op, T.constLike op = true → C op = true) (D : Defs d)
    {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) :
    ∀ a ∈ (constFoldRule R sel).apply D e, altConstB C a = true := by
  intro alt ha
  change alt ∈ foldApply R sel D e at ha
  unfold foldApply at ha
  split at ha
  · split at ha
    · split at ha
      · split at ha
        · split at ha
          · rename_i c hc
            simp only [List.mem_singleton] at ha
            subst ha
            exact hC _ (R.const _ _ c hc)
          · simp at ha
        · simp at ha
      · simp at ha
    · simp at ha
  · simp at ha

omit [TyDenote d.Ty] [DialectDenote d] in
theorem altOpsB_reduceOne (Q pure : d.Op → Bool) (M : Tbl d) {Δ : Ctxt d} {s : d.Ty}
    (e : Expr d Δ s) (he : Q e.op = true) : altOpsB Q (reduceOne pure M e) = true := by
  unfold reduceOne
  split
  · rfl
  · exact he

omit [TyDenote d.Ty] [DialectDenote d] in
theorem altOpsB_reduceAlt (Q pure : d.Op → Bool) (M : Tbl d) {Δ : Ctxt d} {s : d.Ty}
    (a : Alt Δ s) (ha : altOpsB Q a = true) : altOpsB Q (reduceAlt pure M a) = true := by
  cases a with
  | var v => rfl
  | one e => exact altOpsB_reduceOne Q pure M e ha
  | two e1 e2 =>
      simp only [altOpsB, Bool.and_eq_true] at ha
      simp only [reduceAlt]
      split
      · exact altOpsB_reduceOne Q pure M _ ha.2
      · simp only [altOpsB, ha.1, ha.2, Bool.and_self]

/-- **Extraction keeps an operation predicate** that the alternatives of the rules keep. -/
theorem altOpsB_choose (R : RuleSet d) (Q : d.Op → Bool) (hR : RulesOps R Q)
    (S : Tbl d × Defs d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) (he : Q e.op = true) :
    altOpsB Q (choose R S e) = true :=
  pick_prop R _ (fun a => altOpsB Q a = true) _ _ (altOpsB_reduceOne Q _ _ e he)
    (fun a ha _ => by
      unfold classAlts at ha
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      exact altOpsB_reduceAlt Q _ _ a' (hR S.2 e he a' ha'))

/-- **The traversal of the e-graph pass keeps an operation predicate** that the alternatives
    of the rules keep. -/
theorem allOps_nfGo [HasWord64 d] [HasBoolBit d] (R : RuleSet d) (Q : d.Op → Bool)
    (hR : RulesOps R Q) {Γ Δ : Ctxt d} {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ)
    (S : Tbl d × Defs d) (p : NFProg d Γ ts) (hp : p.allOps Q = true) :
    (CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo R ρ S p).allOps Q = true := by
  induction p generalizing Δ S with
  | ret => rfl
  | var e k ih =>
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      have hc := altOpsB_choose R Q hR S (e.rename ρ) hp.1
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo]
      split
      · exact ih _ _ hp.2
      · rename_i e2 h2
        rw [h2] at hc
        simp only [NFProg.allOps, Bool.and_eq_true]
        exact ⟨hc, ih _ _ hp.2⟩
      · rename_i e1 e2 h2
        rw [h2] at hc
        simp only [altOpsB, Bool.and_eq_true] at hc
        simp only [NFProg.allOps, Bool.and_eq_true]
        exact ⟨hc.1, hc.2, ih _ _ hp.2⟩
  | forLoop _ _ _ _ ihb ihk =>
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, NFProg.allOps,
        ihb _ _ hp.1, ihk _ _ hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, NFProg.allOps,
        iht _ _ hp.1.1, ihe _ _ hp.1.2, ihk _ _ hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, NFProg.allOps,
        ihb _ _ hp.1, ihk _ _ hp.2, Bool.and_self]
  | call _ _ _ ih =>
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.nfGo, NFProg.allOps, ih _ _ hp]

end AegraphOps

/-! ## 8. The operations of the catCrypt rule set -/

section CatOps

open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.TraitRules
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat
open CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps (catMemB widthPos)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

/-- A constant-like operation at the type of an expression of `catMemB` is in `catMemB`: the
    type maps to a register of positive width, so the constant is not the unit constant and
    a word constant has a positive width. -/
theorem catMemB_of_constLike {Δ : Ctxt catCryptDialect} {s : CryptoTy}
    {e e' : Expr catCryptDialect Δ s} (he : catMemB e.op = true)
    (hc : catConstLike e'.op = true) : catMemB e'.op = true := by
  have hw : widthPos (catToJasmin.mapTy s) = true := by
    simp only [catMemB, Bool.and_eq_true] at he
    rw [← e.retTy_eq]
    exact he.2
  clear he
  revert hc hw
  obtain ⟨op, rfl, -⟩ := e'
  cases op <;> simp [catConstLike, catMemB, widthPos, DialectSignature.ret, catToJasmin,
    CryptoToJasminCom.mapTy]

section Alts

variable {Δ : Ctxt catCryptDialect} {w : Nat} (D : Defs catCryptDialect)

theorem xorAlts_altConst (a b : Var Δ (.sword w)) :
    ∀ alt ∈ xorAlts D a b, altConstB catConstLike alt = true := by
  intro alt h
  simp only [xorAlts, List.mem_append] at h
  rcases h with (h | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> rfl

theorem andAlts_altConst (a b : Var Δ (.sword w)) :
    ∀ alt ∈ andAlts D a b, altConstB catConstLike alt = true := by
  intro alt h
  simp only [andAlts, List.mem_append] at h
  rcases h with (((h | h) | h) | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> rfl

theorem orAlts_altConst (a b : Var Δ (.sword w)) :
    ∀ alt ∈ orAlts D a b, altConstB catConstLike alt = true := by
  intro alt h
  simp only [orAlts, List.mem_append] at h
  rcases h with (((h | h) | h) | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> rfl

theorem addAlts_altConst (a b : Var Δ (.sword w)) :
    ∀ alt ∈ addAlts D a b, altConstB catConstLike alt = true := by
  intro alt h
  simp only [addAlts, List.mem_append] at h
  rcases h with h | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> rfl

theorem subAlts_altConst (a b : Var Δ (.sword w)) :
    ∀ alt ∈ subAlts D a b, altConstB catConstLike alt = true := by
  intro alt h
  simp only [subAlts, List.mem_append] at h
  rcases h with h | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> rfl

theorem mulAlts_altConst (a b : Var Δ (.sword w)) :
    ∀ alt ∈ mulAlts D a b, altConstB catConstLike alt = true := by
  intro alt h
  simp only [mulAlts, List.mem_append] at h
  rcases h with ((h | h) | h) | h <;> split at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;> subst h <;> rfl

omit D in
theorem zeroAmtAlts_altConst (k : Nat) (a : Var Δ (.sword w)) :
    ∀ alt ∈ zeroAmtAlts k a, altConstB catConstLike alt = true := by
  intro alt h
  unfold zeroAmtAlts at h
  split at h
  · simp only [List.mem_singleton] at h
    subst h
    rfl
  · simp at h

end Alts

/-- Every alternative of the catCrypt rule set is a variable or one binding of a
    constant-like operation. -/
theorem catRules_altConst (D : Defs catCryptDialect) {Δ : Ctxt catCryptDialect}
    {s : CryptoTy} (e : Expr catCryptDialect Δ s) :
    ∀ alt ∈ catRules.alts D e, altConstB catConstLike alt = true := by
  intro alt ha
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp ha
  simp only [catRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_left 7
  · exact involutionRule_altConst _ catInvolution D e alt ha
  · exact idempotentRule_altConst _ catIdempotent D e alt ha
  · exact selfCancelRule_altConst _ catSelfCancel
      (fun op _ => by cases op <;> rfl) D e alt ha
  · exact constFoldRule_altConst _ catReify _ (fun _ h => h) D e alt ha
  all_goals rcases e with ⟨op, hop, args⟩
  all_goals cases op <;>
    simp only [xorRule, andRule, orRule, addRule, subRule, mulRule, shiftZeroRule,
      xorApply, andApply, orApply, addApply, subApply, mulApply, shiftZeroApply,
      List.not_mem_nil] at ha <;> subst hop
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact xorAlts_altConst D a b alt ha
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact andAlts_altConst D a b alt ha
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact orAlts_altConst D a b alt ha
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact addAlts_altConst D a b alt ha
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact subAlts_altConst D a b alt ha
  · match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at ha
      exact mulAlts_altConst D a b alt ha
  all_goals
    match args, (rfl : args = args) with
    | .cons a .nil, _ =>
      simp only [HVector.head] at ha
      exact zeroAmtAlts_altConst _ a alt ha

/-- **The catCrypt rule set keeps `catMemB`.** -/
theorem catRules_ops : RulesOps catRules catMemB := by
  intro D Δ s e he a ha
  exact altOpsB_of_altConstB (fun e' hc => catMemB_of_constLike he hc) a
    (catRules_altConst D e a ha)

end CatOps

/-! ## 9. The operations of the jasmin rule set and of the range stage -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)

/-- The Jasmin operations of `opMemB` whose result has positive width. -/
local notation "opMemPos" => fun op =>
  CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment.opMemB op &&
    CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps.bindPosB op

section JasminOps

open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.TraitRules
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph
open CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps (bindPosB widthPos)

/-- An operation at the type of an expression of `opMemB` of positive width is of positive
    width, and is in `opMemB` when its positive width puts it there. -/
theorem opMemPos_of_ty {Γ : Ctxt jasminDialect} {t : JasminTy}
    {e e' : Expr jasminDialect Γ t} (he : (opMemB e.op && bindPosB e.op) = true)
    (h : bindPosB e'.op = true → opMemB e'.op = true) :
    (opMemB e'.op && bindPosB e'.op) = true := by
  have hb : bindPosB e'.op = bindPosB e.op := by
    unfold bindPosB
    rw [e.retTy_eq, e'.retTy_eq]
  simp only [Bool.and_eq_true] at he ⊢
  rw [hb] at h ⊢
  exact ⟨h he.2, he.2⟩

/-- The bindings of a rule term at a positive width are in `opMemB` of positive width. -/
theorem toAlt_ops {Δ : Ctxt jasminDialect} {w : Nat} (hw : 0 < w) (t : Term Δ w) :
    altOpsB (opMemPos) t.toAlt = true := by
  cases t <;>
    simp [Term.toAlt, altOpsB, constE, CatCrypt.Crypto.Optimizer.Rewrite.Egraph.binE, opMemB, bindPosB, widthPos, hw,
      DialectSignature.ret]

theorem ruleAlts_ops (D : Defs) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) (he : (opMemB e.op && bindPosB e.op) = true) :
    ∀ alt ∈ ruleAlts D e, altOpsB (opMemPos) alt = true := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case regArith bop w =>
    subst hop
    have hw : 0 < w := by
      simpa [opMemB, bindPosB, widthPos, DialectSignature.ret] using he
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [ruleAlts, HVector.head, HVector.tail] at halt
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp halt
      exact toAlt_ops hw t
  all_goals intro alt h; simp [ruleAlts] at h

theorem cmpOneAlts_altConst (C : JasminOp → Bool) (D : Defs) {Δ : Ctxt jasminDialect}
    {s : JasminTy} (e : Expr jasminDialect Δ s) :
    ∀ alt ∈ cmpOneAlts D e, altConstB C alt = true := by
  intro alt halt
  unfold cmpOneAlts at halt
  split at halt
  · rename_i hop args
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [HVector.head, HVector.tail] at halt
      split at halt
      · obtain rfl := List.mem_singleton.mp halt
        rfl
      · cases halt
  · cases halt

/-- **The jasmin rule set keeps `opMemB` at positive width**: the terms of `binRule` bind
    register constants and register arithmetic at the width of the node, constant folding
    binds a register constant at the type of the folded binding, and the copy and the
    one-bit equality rules emit variables. -/
theorem jasminRules_ops : RulesOps jasminRules (opMemPos) := by
  intro D Δ s e he alt ha
  have hC : ∀ e' : Expr jasminDialect Δ s, jasminConstLike e'.op = true →
      (opMemB e'.op && bindPosB e'.op) = true := by
    intro e' hc
    refine opMemPos_of_ty he ?_
    obtain ⟨op, _, _⟩ := e'
    cases op <;> first | exact fun h => h | exact absurd hc Bool.false_ne_true
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp ha
  simp only [jasminRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ruleAlts_ops D e he alt ha
  · exact altOpsB_of_altConstB hC alt
      (constFoldRule_altConst _ jasminReify _ (fun _ h => h) D e alt ha)
  · exact altOpsB_of_altConstB hC alt (copyRule_altConst _ jasminCastCopy D e alt ha)
  · exact altOpsB_of_altConstB hC alt (cmpOneAlts_altConst _ D e alt ha)

open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline (rangeExpr rangeRule ruleOp_op)
open CatCrypt.Crypto.Optimizer.ComRangeFold (pointExpr)

/-- A point of the range stage is a register constant. -/
theorem pointExpr_op {Γ : Ctxt jasminDialect} :
    ∀ (t : JasminTy) (i : _) (e' : Expr jasminDialect Γ t), pointExpr t i = some e' →
      ∃ w n, e'.op = .regConst w n
  | .reg w, i, e', h => by
      simp only [pointExpr, Option.map_eq_some_iff] at h
      obtain ⟨n, -, rfl⟩ := h
      exact ⟨w, n, rfl⟩
  | .stackArr _ _, _, _, h => by simp [pointExpr] at h
  | .inlineInt, _, _, h => by simp [pointExpr] at h
  | .bool, _, _, h => by simp [pointExpr] at h

/-- **A binding of the range stage keeps `opMemB` at positive width**: a point folds to a
    register constant at the type of the binding, and a rule rewrites to register
    arithmetic. -/
theorem rangeExpr_ops {Γ : Ctxt jasminDialect} (A : _) (len : Nat) {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : (opMemB e.op && bindPosB e.op) = true) :
    (opMemB (rangeExpr A len e).op && bindPosB (rangeExpr A len e).op) = true := by
  rcases e with ⟨op, rfl, args⟩
  unfold rangeExpr
  split
  · exact he
  split
  · rename_i e' h'
    refine opMemPos_of_ty he ?_
    obtain ⟨w, n, hop⟩ := pointExpr_op _ _ e' h'
    rw [hop]
    exact fun h => h
  · refine opMemPos_of_ty he ?_
    unfold rangeRule
    split
    · rename_i e' h'
      obtain ⟨bop, w, hop, -⟩ := ruleOp_op _ _ _ h'
      intro _
      show opMemB e'.op = true
      rw [hop]
      rfl
    · intro _
      simp only [Bool.and_eq_true] at he
      exact he.1

/-- **The traversal of the range stage keeps `opMemB` at positive width.** -/
theorem allOps_rangeGo : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (A : _)
    (len : Nat) (p : NFProg jasminDialect Γ ts), p.allOps (opMemPos) = true →
    (CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeGo A len p).allOps (opMemPos) = true
  | _, _, _, _, .ret _, _ => rfl
  | _, _, A, len, .var e k, hp => by
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeGo, NFProg.allOps,
        Bool.and_eq_true]
      have h1 := rangeExpr_ops A len e ((Bool.and_eq_true _ _).mpr hp.1)
      simp only [Bool.and_eq_true] at h1
      exact ⟨h1, allOps_rangeGo _ _ k hp.2⟩
  | _, _, _, _, .forLoop _ _ body k, hp => by
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeGo, NFProg.allOps,
        allOps_rangeGo _ _ body hp.1, allOps_rangeGo _ _ k hp.2, Bool.and_self]
  | _, _, _, _, .ifThenElse _ thn els k, hp => by
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeGo, NFProg.allOps,
        allOps_rangeGo _ _ thn hp.1.1, allOps_rangeGo _ _ els hp.1.2,
        allOps_rangeGo _ _ k hp.2, Bool.and_self]
  | _, _, _, _, .whileLoop _ body k, hp => by
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeGo, NFProg.allOps,
        allOps_rangeGo _ _ body hp.1, allOps_rangeGo _ _ k hp.2, Bool.and_self]
  | _, _, _, _, .call _ _ k, hp => by
      simp only [CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeGo, NFProg.allOps]
      exact allOps_rangeGo _ _ k hp

end JasminOps

/-! ## 10. The operations of the montify pass -/

section MontifyOps

open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (w64)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32 (mont32Cert)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps (bindPosB)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom coveredCom_spliceCom)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldInlineOps (binBlk_mem binLitBlk_mem csubBlk_mem allOps_ofCom allOps_inline?)

section Rewrite

variable {p : Nat} (h : mont32Cert p = true)

theorem allOps_convProg {Θ : Ctxt jasminDialect} (x : Var Θ w64) (j : ℤ)
    {us : List JasminTy} {k : NFProg jasminDialect (w64 :: w64 :: Θ) us}
    (hk : k.allOps (opMemPos) = true) : (convProg h x j k).allOps (opMemPos) = true := by
  simp only [convProg, NFProg.allOps, hk, Bool.and_true]
  rfl

theorem allOps_resConv {Θ : Ctxt jasminDialect} (v : Var Θ w64) (k d : ℤ)
    {us : List JasminTy} {kk : BindK Θ w64 us}
    (hk : ∀ {Θ' : Ctxt jasminDialect} (g : Ctxt.Hom Θ Θ') r (q : NFProg jasminDialect Θ' us),
      kk g r = some q → q.allOps (opMemPos) = true)
    {q : NFProg jasminDialect Θ us} (hq : resConv h v k d kk = some q) :
    q.allOps (opMemPos) = true := by
  unfold resConv at hq
  split at hq
  · exact hk _ _ _ hq
  · obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    exact allOps_convProg h _ _ (hk _ _ _ hq')

theorem allOps_fieldRes {Γ Θ : Ctxt jasminDialect} {ρ : MRen Γ Θ} {g : String}
    {as us : List JasminTy} {args : HVector (fun t => Var Θ t) as} {k d : ℤ}
    {kk : CallK Γ [w64] us}
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen ([w64] ++ Γ) Θ')
      (q : NFProg jasminDialect Θ' us), kk ρ' = some q → q.allOps (opMemPos) = true)
    {q : NFProg jasminDialect Θ us} (hq : fieldRes h ρ g args k d kk = some q) :
    q.allOps (opMemPos) = true := by
  obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
  simp only [NFProg.allOps]
  exact allOps_resConv h _ _ _ (fun _ _ q' hq' => hk _ q' hq') hq0

omit h in
theorem allOps_opaqueArm {Γ Θ : Ctxt jasminDialect} {f : String}
    {as rs us : List JasminTy} {args : HVector (fun t => Var Γ t) as} {ρ : MRen Γ Θ}
    {kk : CallK Γ rs us}
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen (rs ++ Γ) Θ')
      (q : NFProg jasminDialect Θ' us), kk ρ' = some q → q.allOps (opMemPos) = true)
    {q : NFProg jasminDialect Θ us} (hq : opaqueArm f args ρ kk = some q) :
    q.allOps (opMemPos) = true := by
  obtain ⟨_, -, hq⟩ := Option.bind_eq_some_iff.mp hq
  obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
  simp only [NFProg.allOps]
  exact hk _ k' hk'

theorem allOps_binArm {Γ Θ : Ctxt jasminDialect} {f : String} {a b : Var Γ w64}
    {ρ : MRen Γ Θ} {d : ℤ} {us : List JasminTy} {kk : CallK Γ [w64] us}
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen ([w64] ++ Γ) Θ')
      (q : NFProg jasminDialect Θ' us), kk ρ' = some q → q.allOps (opMemPos) = true)
    {q : NFProg jasminDialect Θ us} (hq : binArm h f a b ρ d kk = some q) :
    q.allOps (opMemPos) = true := by
  unfold binArm at hq
  split at hq
  · split at hq
    · split at hq
      · exact allOps_fieldRes h hk hq
      · split at hq
        · exact allOps_fieldRes h hk hq
        · cases hq
    · exact allOps_opaqueArm hk hq
  · exact allOps_opaqueArm hk hq

theorem allOps_unArm {Γ Θ : Ctxt jasminDialect} {f : String} {a : Var Γ w64}
    {ρ : MRen Γ Θ} {d : ℤ} {us : List JasminTy} {kk : CallK Γ [w64] us}
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen ([w64] ++ Γ) Θ')
      (q : NFProg jasminDialect Θ' us), kk ρ' = some q → q.allOps (opMemPos) = true)
    {q : NFProg jasminDialect Θ us} (hq : unArm h f a ρ d kk = some q) :
    q.allOps (opMemPos) = true := by
  unfold unArm at hq
  split at hq
  · split at hq
    · split at hq
      · exact allOps_fieldRes h hk hq
      · split at hq
        · exact allOps_fieldRes h hk hq
        · cases hq
    · exact allOps_opaqueArm hk hq
  · exact allOps_opaqueArm hk hq

theorem allOps_callArm {Γ Θ : Ctxt jasminDialect} {f : String} {us as rs : List JasminTy}
    {args : HVector (fun t => Var Γ t) as} {ρ : MRen Γ Θ} {d : ℤ} {kk : CallK Γ rs us}
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen (rs ++ Γ) Θ')
      (q : NFProg jasminDialect Θ' us), kk ρ' = some q → q.allOps (opMemPos) = true)
    {q : NFProg jasminDialect Θ us} (hq : callArm h f args ρ d kk = some q) :
    q.allOps (opMemPos) = true := by
  unfold callArm at hq
  split at hq
  · rename_i hs
    obtain ⟨h1, h2⟩ := hs
    subst h1 h2
    exact allOps_binArm h hk hq
  · split at hq
    · rename_i _ hs
      obtain ⟨h1, h2⟩ := hs
      subst h1 h2
      exact allOps_unArm h hk hq
    · exact allOps_opaqueArm hk hq

theorem allOps_varConv {Θ : Ctxt jasminDialect} {d : ℤ} {us : List JasminTy}
    {t : JasminTy} {kk : BindK (t :: Θ) t us}
    (hk : ∀ {Θ' : Ctxt jasminDialect} (g : Ctxt.Hom (t :: Θ) Θ') r
      (q : NFProg jasminDialect Θ' us), kk g r = some q → q.allOps (opMemPos) = true)
    {q : NFProg jasminDialect (t :: Θ) us} (hq : varConv h d kk = some q) :
    q.allOps (opMemPos) = true := by
  unfold varConv at hq
  split at hq
  · exact hk _ _ _ hq
  · cases t with
    | reg w =>
      by_cases hw : w = 64
      · subst hw
        obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
        exact allOps_convProg h _ _ (hk _ _ _ hq')
      · simp [wordConv, hw] at hq
    | _ => simp [wordConv] at hq

/-- **The rewriter keeps `opMemB` at positive width**: a binding is kept with its
    operation, and a conversion binds a `64`-bit register constant before a call. -/
theorem allOps_montifyAux :
    {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    (prog : NFProg jasminDialect Γ ts) → (H : DegHint) → {Θ : Ctxt jasminDialect} →
    (ρ : MRen Γ Θ) → (q : NFProg jasminDialect Θ ts) → prog.allOps (opMemPos) = true →
      montifyAux h prog H ρ = some q → q.allOps (opMemPos) = true
  | _, _, .ret _, _, _, _, _, _, hq => by
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hq
      rfl
  | _, _, .var e k, H, _, ρ, q, hp, hq => by
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      obtain ⟨e', he', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
      unfold renExpr at he'
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp he'
      simp only [NFProg.allOps, Bool.and_eq_true]
      exact ⟨hp.1, allOps_varConv h
        (fun _ _ q' hq' => allOps_montifyAux k _ _ q' hp.2 hq') hq0⟩
  | _, _, .forLoop count inits body k, H, _, ρ, q, hp, hq => by
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hb', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.allOps, allOps_montifyAux body _ _ _ hp.1 hb',
        allOps_montifyAux k _ _ _ hp.2 hk', Bool.and_self]
  | _, _, .ifThenElse cond thn els k, H, _, ρ, q, hp, hq => by
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨t', ht', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨e', he', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.allOps, allOps_montifyAux thn _ _ _ hp.1.1 ht',
        allOps_montifyAux els _ _ _ hp.1.2 he', allOps_montifyAux k _ _ _ hp.2 hk',
        Bool.and_self]
  | _, _, .whileLoop inits body k, H, _, ρ, q, hp, hq => by
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hb', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.allOps, allOps_montifyAux body _ _ _ hp.1 hb',
        allOps_montifyAux k _ _ _ hp.2 hk', Bool.and_self]
  | _, _, .call f args k, H, _, ρ, q, hp, hq => by
      simp only [NFProg.allOps] at hp
      unfold montifyAux at hq
      split at hq
      · cases hq
      · exact allOps_callArm h (fun ρ' q' hk => allOps_montifyAux k _ ρ' q' hp hk) hq

theorem allOps_entryConv {Γ : Ctxt jasminDialect} {us : List JasminTy}
    (kk : ∀ {Θ : Ctxt jasminDialect}, MRen Γ Θ → Option (NFProg jasminDialect Θ us))
    (hk : ∀ {Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ) (q : NFProg jasminDialect Θ us),
      kk ρ = some q → q.allOps (opMemPos) = true) :
    ∀ (vs : List (Var Γ w64 × ℤ)) {Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ)
      (q : NFProg jasminDialect Θ us), entryConv h kk vs ρ = some q →
        q.allOps (opMemPos) = true
  | [], _, ρ, q, hq => hk ρ q hq
  | (v, d) :: vs, _, ρ, q, hq => by
      obtain ⟨x, -, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨q1, hq1, rfl⟩ := Option.map_eq_some_iff.mp hq
      exact allOps_convProg h _ _ (allOps_entryConv kk hk vs _ q1 hq1)

theorem allOps_montify (pd : List ℤ) (H : DegHint) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts)
    (hp : prog.allOps (opMemPos) = true) {q : NFProg jasminDialect Γ ts}
    (hq : montify h pd H prog = some q) : q.allOps (opMemPos) = true := by
  unfold montify at hq
  split at hq
  · exact allOps_entryConv h _
      (fun ρ q' hq' => allOps_montifyAux h prog H ρ q' hp hq') _ _ q hq
  · cases hq

end Rewrite

/-- The reduction block binds register constants and register arithmetic at width `64`. -/
theorem redcBlk_mem {Γ : Ctxt jasminDialect} (P μ : Nat) (t : Var Γ w64) :
    CoveredCom (fun e => (opMemB e.op && bindPosB e.op) = true)
      (CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32.redcBlk P μ t) := by
  unfold CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32.redcBlk
  exact coveredCom_spliceCom (d := jasminDialect) (opMemPos) _ _ (binLitBlk_mem _ _ _) <|
    coveredCom_spliceCom (d := jasminDialect) (opMemPos) _ _ (binLitBlk_mem _ _ _) <|
    coveredCom_spliceCom (d := jasminDialect) (opMemPos) _ _ (binLitBlk_mem _ _ _) <|
    coveredCom_spliceCom (d := jasminDialect) (opMemPos) _ _ (binLitBlk_mem _ _ _) <|
    coveredCom_spliceCom (d := jasminDialect) (opMemPos) _ _ (binBlk_mem _ _ _)
      (binLitBlk_mem _ _ _)

/-- A body of a reduce-multiply head binds operations of `opMemB` of positive width only. -/
theorem allOps_montBody {f : String} {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (hb : montBody f as rs = some b) :
    b.allOps (opMemPos) = true := by
  unfold montBody at hb
  split at hb
  · rename_i q _
    split at hb
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      cases hb
      unfold redcMulProg
      refine allOps_ofCom (d := jasminDialect) (opMemPos) _ ?_
      unfold CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.MontDeg.redcMulBlk
      exact coveredCom_spliceCom (d := jasminDialect) (opMemPos) _ _ (binBlk_mem _ _ _) <|
        coveredCom_spliceCom (d := jasminDialect) (opMemPos) _ _ (redcBlk_mem _ _ _)
          (csubBlk_mem _ _)
    · cases hb
  · cases hb

/-- A montify round keeps `opMemB` at positive width. -/
theorem allOps_montifyAt {p : Nat} (h : mont32Cert p = true) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts)
    (hp : prog.allOps (opMemPos) = true) : (montifyAt h prog).allOps (opMemPos) = true := by
  unfold montifyAt
  split
  · rename_i q hq
    split
    · rename_i q' hq'
      split
      · exact allOps_inline? montLibJ (opMemPos) (fun _ _ hb => by cases hb)
          (fun _ _ _ _ hb => allOps_montBody hb) q hq' (allOps_montify h _ _ prog hp hq)
      · exact hp
    · exact hp
  · exact hp

/-- The montify rounds at a list of moduli keep `opMemB` at positive width. -/
theorem allOps_montifyMods {Γ : Ctxt jasminDialect} {ts : List JasminTy} :
    ∀ (ps : List Nat) (prog : NFProg jasminDialect Γ ts), prog.allOps (opMemPos) = true →
      (montifyMods ps prog).allOps (opMemPos) = true
  | [], _, hp => hp
  | p :: ps, prog, hp => by
      refine allOps_montifyMods ps _ ?_
      split
      · rename_i h
        exact allOps_montifyAt h prog hp
      · exact hp

/-- **The montify pass keeps `opMemB` at positive width.** -/
theorem allOps_montifyPass {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (prog : NFProg jasminDialect Γ ts) (hp : prog.allOps (opMemPos) = true) :
    (montifyPass prog).allOps (opMemPos) = true :=
  allOps_montifyMods _ prog hp

end MontifyOps

/-! ## 11. The operations of the select lowering -/

section SelectOps

open CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps (bindPosB widthPos)

/-- A variable of a context of types of positive width has a type of positive width. -/
theorem widthPos_var {Γ : Ctxt jasminDialect} (hΓ : ∀ t ∈ Γ, widthPos t = true) :
    ∀ {t : JasminTy}, Var Γ t → widthPos t = true
  | _, .here => hΓ _ List.mem_cons_self
  | _, .there v => widthPos_var (fun s hs => hΓ s (List.mem_cons_of_mem _ hs)) v

/-- The variables of a context of types of positive width have types of positive width. -/
theorem widthPos_vars {Γ : Ctxt jasminDialect} (hΓ : ∀ t ∈ Γ, widthPos t = true) :
    ∀ {ss : List JasminTy}, HVector (fun t => Var Γ t) ss → ∀ t ∈ ss, widthPos t = true
  | [], .nil => fun _ h => absurd h List.not_mem_nil
  | _ :: _, .cons v vs => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · exact widthPos_var hΓ v
      · exact widthPos_vars hΓ vs t ht

/-- A prefix of types of positive width keeps a context of types of positive width. -/
theorem widthPos_append {cs Γ : List JasminTy} (hcs : ∀ t ∈ cs, widthPos t = true)
    (hΓ : ∀ t ∈ Γ, widthPos t = true) : ∀ t ∈ cs ++ Γ, widthPos t = true := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  exacts [hcs t ht, hΓ t ht]

/-- The result types of a call at a signature of `wordSig` are of positive width. -/
theorem widthPos_of_wordSig {as rs : List JasminTy} (h : wordSig as rs = true) :
    ∀ t ∈ rs, widthPos t = true := by
  obtain ⟨-, hrs | ⟨n, hrs⟩⟩ :=
    CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions.wordSig_iff.mp h <;>
    subst hrs <;> simp [widthPos]

/-- The type of a binding of positive width extends a context of types of positive
    width. -/
theorem widthPos_cons {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : (opMemB e.op && bindPosB e.op) = true)
    (hΓ : ∀ t ∈ Γ, widthPos t = true) : ∀ s ∈ t :: Γ, widthPos s = true := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · simp only [Bool.and_eq_true] at he
    have h2 := he.2
    unfold bindPosB at h2
    rwa [e.retTy_eq] at h2
  · exact hΓ s hs

/-- **The result types of a program are of positive width** when its context, its bindings
    and the results of its calls are: each result is a variable of the final context. -/
theorem widthPos_rets (W : List JasminTy → Bool) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    (∀ t ∈ Γ, widthPos t = true) → p.allOps (opMemPos) = true →
      callsLoopsAll (fun _ as rs => wordSig as rs) W p = true →
        ∀ t ∈ ts, widthPos t = true := by
  induction p with
  | ret vs => intro hΓ _ _; exact widthPos_vars hΓ vs
  | var e k ih =>
      intro hΓ hp hc
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      exact ih (widthPos_cons e ((Bool.and_eq_true _ _).mpr hp.1) hΓ) hp.2 hc
  | forLoop count inits body k _ ihk =>
      intro hΓ hp hc
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [callsLoopsAll, Bool.and_eq_true] at hc
      exact ihk (widthPos_append (widthPos_vars hΓ inits) hΓ) hp.2 hc.2
  | ifThenElse cond thn els k iht _ ihk =>
      intro hΓ hp hc
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [callsLoopsAll, Bool.and_eq_true] at hc
      exact ihk (widthPos_append (iht hΓ hp.1.1 hc.1.1) hΓ) hp.2 hc.2
  | whileLoop inits body k _ ihk =>
      intro hΓ hp hc
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [callsLoopsAll, Bool.and_eq_true] at hc
      exact ihk (widthPos_append (widthPos_vars hΓ inits) hΓ) hp.2 hc.2
  | call f args k ih =>
      intro hΓ hp hc
      simp only [NFProg.allOps] at hp
      simp only [callsLoopsAll, Bool.and_eq_true] at hc
      exact ih (widthPos_append (widthPos_of_wordSig hc.1) hΓ) hp hc.2

/-- The select of `jasminDialect` at a type of positive width is in `opMemB` of positive
    width. -/
theorem sel_ops {Γ : Ctxt jasminDialect} {t : JasminTy}
    (h : HasSelect.selects (d := jasminDialect) t = true) (ht : widthPos t = true)
    (c : Var Γ (HasBitType.bit (d := jasminDialect))) (a b : Var Γ t) :
    (opMemB (HasSelect.sel h c a b).op && bindPosB (HasSelect.sel h c a b).op) = true := by
  cases t with
  | reg w =>
      show (opMemB (JasminOp.select w) && bindPosB (JasminOp.select w)) = true
      simpa [opMemB, bindPosB, DialectSignature.ret] using ht
  | _ => exact absurd h Bool.false_ne_true

/-- A program `emitArm? p ren kont` returns has its operations in `Q` when `p` has and every
    program the continuation returns has. -/
theorem allOps_emitArm? {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] (Q : d.Op → Bool) {ts : List d.Ty} {Γ : Ctxt d}
    {rs : List d.Ty} (p : NFProg d Γ rs) (hp : p.allOps Q = true) :
    ∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ)
      (kont : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
        Option (NFProg d Δ' ts)),
      (∀ {Δ' : Ctxt d} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs) q,
        kont r res = some q → q.allOps Q = true) →
      ∀ q, NFProg.emitArm? p ren kont = some q → q.allOps Q = true := by
  induction p with
  | ret vs => intro Δ ren kont hk q hq; exact hk _ _ q hq
  | var e k ih =>
      intro Δ ren kont hk q hq
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.allOps, Bool.and_eq_true]
      exact ⟨hp.1, ih hp.2 (Ctxt.Hom.lift ren) (fun r res => kont (fun v => r (.there v)) res)
        (fun r res q hq => hk _ res q hq) q' hq'⟩
  | forLoop => intro _ _ _ _ q hq; simp [NFProg.emitArm?] at hq
  | ifThenElse => intro _ _ _ _ q hq; simp [NFProg.emitArm?] at hq
  | whileLoop => intro _ _ _ _ q hq; simp [NFProg.emitArm?] at hq
  | call => intro _ _ _ _ q hq; simp [NFProg.emitArm?] at hq

/-- The selects at result types of positive width keep `opMemB` at positive width. -/
theorem allOps_emitSels {ts : List JasminTy} : ∀ {Δ : Ctxt jasminDialect}
    {rs : List JasminTy} (h : rs.all (HasSelect.selects (d := jasminDialect)) = true)
    (_hrs : ∀ t ∈ rs, widthPos t = true) (c : Var Δ (HasBitType.bit (d := jasminDialect)))
    (va vb : HVector (fun t => Var Δ t) rs)
    (kont : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg jasminDialect Δ' ts),
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs),
      (kont r res).allOps (opMemPos) = true) →
    (NFProg.emitSels h c va vb kont).allOps (opMemPos) = true
  | _, [], _, _, _, .nil, .nil, _, hk => hk _ _
  | _, _ :: _, h, hrs, c, .cons a va, .cons b vb, kont, hk => by
      rw [NFProg.emitSels]
      simp only [NFProg.allOps, Bool.and_eq_true]
      exact ⟨by
          have := sel_ops (NFProg.selects_head h) (hrs _ List.mem_cons_self) c a b
          simpa only [Bool.and_eq_true] using this,
        allOps_emitSels _ (fun t ht => hrs t (List.mem_cons_of_mem _ ht)) _ _ _ _
          (fun r res => hk _ _)⟩

/-- A program `lowerIte?` returns keeps `opMemB` at positive width when the arms, the
    continuation and the result types do. -/
theorem allOps_lowerIte? {ts : List JasminTy} {Δ : Ctxt jasminDialect} {rs : List JasminTy}
    (hrs : ∀ t ∈ rs, widthPos t = true) (c : Var Δ (HasBitType.bit (d := jasminDialect)))
    (thn els : NFProg jasminDialect Δ rs) (ht : thn.allOps (opMemPos) = true)
    (he : els.allOps (opMemPos) = true)
    (kont : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → HVector (fun t => Var Δ' t) rs →
      NFProg jasminDialect Δ' ts)
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (res : HVector (fun t => Var Δ' t) rs),
      (kont r res).allOps (opMemPos) = true)
    (q : NFProg jasminDialect Δ ts) (hq : NFProg.lowerIte? c thn els kont = some q) :
    q.allOps (opMemPos) = true := by
  unfold NFProg.lowerIte? at hq
  split at hq
  next =>
    refine allOps_emitArm? (opMemPos) thn ht _ _ (fun r1 va q1 hq1 => ?_) q hq
    refine allOps_emitArm? (opMemPos) els he _ _ (fun r2 vb q2 hq2 => ?_) q1 hq1
    obtain rfl := Option.some.inj hq2
    exact allOps_emitSels _ hrs _ _ _ _ (fun r3 res => hk _ res)
  next => cases hq

/-- **The select lowering keeps `opMemB` at positive width** on a program over a context of
    types of positive width whose calls are at signatures of `wordSig`: the selects are at
    the result types of the branches, which are of positive width (`widthPos_rets`). -/
theorem allOps_lowerSel (W : List JasminTy → Bool) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    (∀ t ∈ Γ, widthPos t = true) → p.allOps (opMemPos) = true →
      callsLoopsAll (fun _ as rs => wordSig as rs) W p = true →
        ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ),
          (NFProg.lowerSel p ren).allOps (opMemPos) = true := by
  induction p with
  | ret => intro _ _ _ Δ ren; rfl
  | var e k ih =>
      intro hΓ hp hc Δ ren
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [NFProg.lowerSel, NFProg.allOps, Bool.and_eq_true]
      exact ⟨hp.1, ih (widthPos_cons e ((Bool.and_eq_true _ _).mpr hp.1) hΓ) hp.2 hc _⟩
  | forLoop count inits body k ihb ihk =>
      intro hΓ hp hc Δ ren
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [callsLoopsAll, Bool.and_eq_true] at hc
      have hcs := widthPos_vars hΓ inits
      have hw := widthPos_append (cs := [HasWord64.word (d := jasminDialect)])
        (fun t ht => by rcases List.mem_singleton.mp ht with rfl; rfl) hΓ
      simp only [NFProg.lowerSel, NFProg.allOps, Bool.and_eq_true]
      exact ⟨ihb (widthPos_append hcs hw) hp.1 hc.1 _, ihk (widthPos_append hcs hΓ) hp.2 hc.2 _⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro hΓ hp hc Δ ren
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [callsLoopsAll, Bool.and_eq_true] at hc
      have hrs := widthPos_rets W thn hΓ hp.1.1 hc.1.1
      have hk := fun {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom (_ ++ _) Δ') =>
        ihk (widthPos_append hrs hΓ) hp.2 hc.2 r
      simp only [NFProg.lowerSel]
      split
      · rename_i q hq
        exact allOps_lowerIte? hrs _ _ _ (iht hΓ hp.1.1 hc.1.1 ren) (ihe hΓ hp.1.2 hc.1.2 ren)
          _ (fun _ _ => hk _) q hq
      · simp only [NFProg.allOps, iht hΓ hp.1.1 hc.1.1, ihe hΓ hp.1.2 hc.1.2, hk,
          Bool.and_self]
  | whileLoop inits body k ihb ihk =>
      intro hΓ hp hc Δ ren
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [callsLoopsAll, Bool.and_eq_true] at hc
      have hcs := widthPos_append (widthPos_vars hΓ inits) hΓ
      simp only [NFProg.lowerSel, NFProg.allOps, ihb hcs hp.1 hc.1.2, ihk hcs hp.2 hc.2,
        Bool.and_self]
  | call f args k ih =>
      intro hΓ hp hc Δ ren
      simp only [NFProg.allOps] at hp
      simp only [callsLoopsAll, Bool.and_eq_true] at hc
      simp only [NFProg.lowerSel, NFProg.allOps]
      exact ih (widthPos_append (widthPos_of_wordSig hc.1) hΓ) hp hc.2 _

end SelectOps

/-! ## 12. The input of the translation is unit-free -/

section UnitFreeInput

open CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples (UnitFree flattenTuples_unitFree)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (op_rename?)

/-- **Renaming keeps `UnitFree`.** -/
theorem unitFree_rename? {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt nfDialect} {f : PRen Γ Δ} {p' : NFProg nfDialect Δ ts},
      NFProg.rename? f p = some p' → UnitFree p → UnitFree p' := by
  induction p with
  | ret vs =>
      intro Δ f p' h _
      simp only [NFProg.rename?, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      trivial
  | var e k ih =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨e', he', k', hk, rfl⟩ := h
      exact ⟨hp.1, by rw [op_rename? he']; exact hp.2.1, ih hk hp.2.2⟩
  | forLoop count inits body k ihb ihk =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, b', hb, k', hk, rfl⟩ := h
      exact ⟨hp.1, ihb hb hp.2.1, ihk hk hp.2.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, t', ht, e', he, k', hk, rfl⟩ := h
      exact ⟨hp.1, iht ht hp.2.1, ihe he hp.2.2.1, ihk hk hp.2.2.2⟩
  | whileLoop inits body k ihb ihk =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, b', hb, k', hk, rfl⟩ := h
      exact ⟨hp.1, ihb hb hp.2.1, ihk hk hp.2.2⟩
  | call fn args k ih =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, k', hk, rfl⟩ := h
      exact ⟨hp.1, hp.2.1, ih hk hp.2.2⟩

/-- **Dead-binding elimination keeps `UnitFree`.** -/
theorem unitFree_dce {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts)
    (hp : UnitFree p) : UnitFree (NFProg.dce p) := by
  induction p with
  | ret => trivial
  | var e k ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hk'
        exact unitFree_rename? _ hk' (ih hp.2.2)
      · exact ⟨hp.1, hp.2.1, ih hp.2.2⟩
  | forLoop _ _ body k ihb ihk =>
      exact ⟨hp.1, ihb hp.2.1, ihk hp.2.2⟩
  | ifThenElse _ thn els k iht ihe ihk =>
      exact ⟨hp.1, iht hp.2.1, ihe hp.2.2.1, ihk hp.2.2.2⟩
  | whileLoop _ body k ihb ihk =>
      exact ⟨hp.1, ihb hp.2.1, ihk hp.2.2⟩
  | call _ _ k ih =>
      exact ⟨hp.1, hp.2.1, ih hp.2.2⟩

/-- A cast along equal contexts and result types keeps `UnitFree`. -/
theorem unitFree_cast {Γ Γ' : Ctxt nfDialect} {ts ts' : List NfTy} (hΓ : Γ = Γ')
    (hts : ts = ts') (q : NFProg nfDialect Γ ts)
    (E : NFProg nfDialect Γ ts = NFProg nfDialect Γ' ts') (hq : UnitFree q) :
    UnitFree (cast E q) := by
  subst hΓ hts
  exact hq

/-- **Tuple flattening at a context and result types without tuple types returns a
    unit-free program.** -/
theorem unitFree_flatSame {Γ : Ctxt nfDialect} {ts : List NfTy} {p q : NFProg nfDialect Γ ts}
    (h : flatSame p = some q) : UnitFree q := by
  unfold flatSame at h
  split at h
  · rename_i hn
    obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp h
    exact unitFree_cast (flatCtx_of_noTuple hn.1) (flatCtx_of_noTuple hn.2) q0 _
      (flattenTuples_unitFree p hq0)
  · cases h

open CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples (flatCtx flatProg tupleHom?)

section FlatLoops

variable {C : String → List NfTy → List NfTy → Bool} {W : List NfTy → Bool}
  (hC : ∀ f as rs, C f as rs = true → C f (flatCtx as) (flatCtx rs) = true)
  (hW : ∀ cs, W cs = true → W (flatCtx cs) = true)

include hC hW in
/-- **Tuple flattening keeps `callsLoopsAll C W`** at tests that accept the flattening of
    every signature and tuple they accept. -/
theorem callsLoopsAll_flatProg {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt nfDialect} (ren : Ctxt.Hom (flatCtx Γ) Δ) (q : NFProg nfDialect Δ (flatCtx ts)),
      flatProg p ren = some q → callsLoopsAll C W p = true → callsLoopsAll C W q = true := by
  induction p with
  | ret vs =>
      intro Δ ren q hq _
      rw [flatProg] at hq
      cases hq
      rfl
  | var e k ih =>
      obtain ⟨op, rfl, args⟩ := e
      intro Δ ren q hq hp
      rw [flatProg] at hq
      cases hT : tupleHom? ren op args with
      | some R =>
          simp only [hT] at hq
          exact ih _ q hq hp
      | none =>
          simp only [hT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
          obtain ⟨args', _, R, _, k', hk, rfl⟩ := hq
          exact ih _ k' hk hp
  | forLoop count inits body k ihb ihk =>
      intro Δ ren q hq hp
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      rw [flatProg] at hq
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨body', hb, k', hk, rfl⟩ := hq
      simp only [callsLoopsAll, ihb _ body' hb hp.1, ihk _ k' hk hp.2, Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren q hq hp
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      rw [flatProg] at hq
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨thn', ht, els', he, k', hk, rfl⟩ := hq
      simp only [callsLoopsAll, iht _ thn' ht hp.1.1, ihe _ els' he hp.1.2, ihk _ k' hk hp.2,
        Bool.and_self]
  | whileLoop inits body k ihb ihk =>
      intro Δ ren q hq hp
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      rw [flatProg] at hq
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨body', hb, k', hk, rfl⟩ := hq
      simp only [callsLoopsAll, Bool.and_eq_true]
      exact ⟨⟨hW _ hp.1.1, ihb _ body' hb hp.1.2⟩, ihk _ k' hk hp.2⟩
  | call f args k ih =>
      intro Δ ren q hq hp
      simp only [callsLoopsAll, Bool.and_eq_true] at hp
      rw [flatProg] at hq
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [callsLoopsAll, hC _ _ _ hp.1, ih _ k' hk hp.2, Bool.and_self]

include hC hW in
/-- **`flatSame` keeps `callsLoopsAll C W`** at tests that accept the flattening of every
    signature and tuple they accept. -/
theorem callsLoopsAll_flatSame {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p q : NFProg nfDialect Γ ts} (hq : flatSame p = some q) (hp : callsLoopsAll C W p = true) :
    callsLoopsAll C W q = true := by
  unfold flatSame at hq
  split at hq
  · rename_i h
    obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
    have hc : ∀ {Γ' : Ctxt nfDialect} {ts' : List NfTy} (hΓ : Γ' = Γ) (hts : ts' = ts)
        (e : NFProg nfDialect Γ' ts' = NFProg nfDialect Γ ts) (r : NFProg nfDialect Γ' ts'),
        callsLoopsAll C W (cast e r) = callsLoopsAll C W r := by
      intro _ _ hΓ hts _ _
      subst hΓ hts
      rfl
    rw [hc (flatCtx_of_noTuple h.1) (flatCtx_of_noTuple h.2)]
    exact callsLoopsAll_flatProg hC hW p _ q0 hq0 hp
  · cases hq

end FlatLoops

end UnitFreeInput

/-! ## 13. The operations of the output of the chain -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps (bindPosB widthPos catMemB
  nfToCatExt_allOps_catMemB catToJasmin_allOps_of_catMemB)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep (fieldDialectStep_allOps)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)

/-- **Every program `extChain` returns has its operations in `opMemB`, each with a result
    type of positive width**, when the context of the output has types of positive width:
    the translation of the unit-free output of the flattening has its operations in
    `catMemB` (`nfToCatExt_allOps_catMemB`), the e-graph pass at `catRules` keeps them
    (`catRules_ops`), the conversion takes them to `opMemB` at positive width
    (`catToJasmin_allOps_of_catMemB`), and the montify pass, the field dialect step, the select
    lowering, the range stage and the e-graph pass at `jasminRules` keep that. -/
theorem extChain_allOps (D : List ExtDecl) {Γ : Ctxt nfDialect} {t : NfTy}
    {p : NFProg nfDialect Γ [t]} {q : NFProg jasminDialect (mapCtx (Γ.map catTy))
      [mapTy (catTy t)]} (h : (extChain D Γ t).run p = some q)
    (hΓ : ∀ s ∈ mapCtx (Γ.map catTy), widthPos s = true) :
    q.allOps (opMemPos) = true := by
  simp only [extChain, extChainCore, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨p0, hp0, p1, hp1, p2, hp2, p3, hp3, r, hr, r1, hr1, j, hj, j1, hj1, j2, hj2, j3, hj3,
    j4, hj4, j5, hj5, hq⟩ := h
  obtain rfl := Option.some.inj hq
  change some (NFProg.abortElim NfOp.isAbort p) = some p0 at hp0
  cases hp0
  change flatSame (NFProg.abortElim NfOp.isAbort p) = some p1 at hp1
  change (if outTyB t then some p1 else none) = some p2 at hp2
  change some (NFProg.dce p2) = some p3 at hp3
  change nfToCatExt (fieldDeclsFor D p3) p3 TRd.id = some r at hr
  have hp2' : p1 = p2 := by split at hp2 <;> cases hp2; rfl
  subst hp2'
  cases hp3; cases hr1; cases hj1; cases hj3; cases hj4; cases hj5
  have hu : CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples.UnitFree (NFProg.dce p1) :=
    unitFree_dce _ (unitFree_flatSame hp1)
  have h0 : r.allOps catMemB = true := nfToCatExt_allOps_catMemB _ _ hu TRd.id r hr
  have h1 : (CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.aegraphOptNF catRules r).allOps
      catMemB = true :=
    allOps_nfGo catRules catMemB catRules_ops _ _ r h0
  have h2 := catToJasmin_allOps_of_catMemB _ h1 _ j hj
  have h3 := allOps_montifyPass _ h2
  have h4 := fieldDialectStep_allOps h3 hj2
  have hc0 : callsLoopsAll (fun _ as rs => wordSig ((as.map catToJasmin.mapTy))
      (rs.map catToJasmin.mapTy)) (fun _ => true) r = true := by
    refine callsLoopsAll_of_loops _ _ r
      (nfToCatExt_callsLoopsAll _ _ (NFProg.dce p1) (callsLoopsAll_true _) TRd.id r hr) ?_
    intro f as rs hc
    obtain ⟨d, -, -, rfl, rfl, hw⟩ := nfToCatExt_calls _ _ TRd.id r hr f as rs hc
    exact wordSig_of_extDecl hw
  have hc1 := (callsLoopsAll_nfGo (d := catCryptDialect) _ _ catRules (Ctxt.Hom.id _) (∅, ∅)
    r).trans hc0
  have hc2 := callsLoopsAll_map? catToJasmin catToJasmin_regionTypes
    (fun _ as rs => wordSig as rs) (fun _ => true) _ hc1 _ hj
  have hc3 := callsLoopsAll_montifyPass _ _ (fun _ _ => rfl) _ hc2
  have hc4 := callsLoopsAll_fieldDialect _ _ hc3 hj2
  have h5 := allOps_lowerSel _ _ hΓ h4 hc4 (fun v => v)
  unfold CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.aegraphOptNF
    CatCrypt.Crypto.Optimizer.Rewrite.RangeNF.rangeNF
  exact allOps_nfGo jasminRules _ jasminRules_ops _ _ _ (allOps_rangeGo _ _ _ h5)

/-- The entry context of an ABI layout maps to Jasmin types of positive width. -/
theorem widthPos_entryCtx (σ : AbiLayout) :
    ∀ s ∈ mapCtx ((CatCrypt.Crypto.Hax.ImpToNF.entryCtx (NFToRoute.abiEntry σ)).map catTy),
      widthPos s = true := by
  intro s hs
  simp only [mapCtx, CatCrypt.Crypto.Hax.ImpToNF.entryCtx, NFToRoute.abiEntry,
    CatCrypt.Crypto.Hax.NFToCat.abiParamsArr, List.map_reverse, List.mem_reverse,
    List.map_map, List.mem_map] at hs
  obtain ⟨a, -, rfl⟩ := hs
  simp only [Function.comp_apply]
  cases a.kind <;> rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps

/-! ## 14. The region export on the output of the chain -/

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportComplete
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps

/-- **The region export on the output of the chain.** On a module `refusal?` accepts, the
    front returns a program `p`, and at every table `bi` the chain `extChain` at the
    declarations `linkedDecls m bi` returns a program `q` on `p`; `q` passes `whileRegB`,
    `wordCalls` and `regionExportableB` (its operations are in `opMemB`), and the export
    `exportR` returns code on it at every number of arguments, name, depth, label and
    instruction set. -/
theorem CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_export_isSome
    {σ : CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule}
    (hr : m.refusal? σ = none) :
    ∃ (t : _) (p : _), CatCrypt.Crypto.SecureCompilation.Haxc.haxToNF σ m = some ⟨t, p⟩ ∧
      ∀ bi, ∃ q, (CatCrypt.Crypto.SecureCompilation.Haxc.extChain
          (CatCrypt.Crypto.SecureCompilation.Haxc.linkedDecls m bi) _ t).run p = some q ∧
        whileRegB q = true ∧ wordCalls q = true ∧ regionExportableB q = true ∧
        ∀ nArgs fn d n I, (exportR nArgs fn q d n I).isSome = true := by
  obtain ⟨t, p, hp, h⟩ := CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_extChain_isSome hr
  refine ⟨t, p, hp, fun bi => ?_⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (h bi)
  have hw : ∀ p1, CatCrypt.Crypto.SecureCompilation.Haxc.flatSame
      (NFProg.abortElim CatCrypt.Crypto.SecureCompilation.VIR.NFDialect.NfOp.isAbort p) =
        some p1 →
      callsLoopsAll (fun _ _ _ => true)
        (fun cs => cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB) p1 = true := by
    rw [NFProg.abortElim_of_abortFree _ p
      (CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete.haxToNF_abortFree hp)]
    exact fun p1 h1 => callsLoopsAll_of_opsNB _ _ p1
      (CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete.haxToNF_flatSame_opsNBLoop hp h1)
  have h3 := extChain_whileRegB _ hq hw
  have h4 := extChain_wordCalls _ hq hw
  have hA := extChain_allOps _ hq (widthPos_entryCtx σ)
  have h1 : q.allOps opMemB = true := (NFProg.allOps_iff _ q).mpr fun o ho => by
    have := (NFProg.allOps_iff _ q).mp hA o ho
    simp only [Bool.and_eq_true] at this
    exact this.1
  have hB : regionExportableB q = true := by
    rw [regionExportableB_eq, h1, h3, h4]; rfl
  exact ⟨q, hq, h3, h4, hB, exportR_isSome_of_regionExportableB hB⟩
