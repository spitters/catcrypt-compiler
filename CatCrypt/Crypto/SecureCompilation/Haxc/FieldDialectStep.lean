/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRaise
public import CatCrypt.Crypto.SecureCompilation.Haxc.ModArithLimbs
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldInlineOps
public import CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotalJ
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithChain
public import CatCrypt.Crypto.SecureCompilation.VIR.NFFwdLoad1
public import CatCrypt.Crypto.SecureCompilation.VIR.NFMapLeakBlockEv
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgDCE

/-!
# The field dialect step

`fieldDialectStep` is a chain step `NFProg jasminDialect Γ ts → NFProg jasminDialect Γ ts`
that replaces the tagged field calls of a program by the limb templates through the field
dialects. A program that calls no field head (`Hax.FieldTag.fieldHeadB`) is returned
unchanged. Otherwise each call of a tagged head is inlined (`NFProg.inline?`) with its lowered
body `fieldBodyD`: the raised body
of the head in `jasField` (`FieldRaise.raiseBody`), lowered to `jasMod`
(`FieldToModArithChain.fieldToModArithStep`) and to `jasminDialect` along the limb templates
(`ModArithLimbs.modArithLimbsStep`), carried back to the signature of the head (`castNF`,
`ctx3_eq`), with its loads from one-word arrays forwarded (`NFFwdLoad1.fwdLoad1`) and its dead
bindings removed (`NFProg.dce`) (`lowerBody`). The stages run on the bodies of the heads, each
a few dozen nodes, and the program is traversed once.

The certificates of the two lowerings need the call environments to agree at every call of
the lowered program. Every call of a raised program is at injected types
(`fieldRaiseStep_callsAll`, `fieldToModArithStep_callsAll`), where `liftEnv E`, `liftEnvM E`
and `E` agree (`liftEnv_transports`, `liftEnvM_transports`), so `NFProg.map?_refinesAtM`
applies at the calls of the program. The transport of a valuation through the two lowerings
is the valuation up to the equality of contexts (`val3_cast`). The library of the lowered
bodies is sound for the denotation (`fieldLibD_sound`) and for the leakage run, with events
that do not depend on the arguments (`fieldLibD_leakSound`).

The operations of the raised program are the operations of `jasminDialect`, the field
operations at a modulus with a template, and the casts the template has a block for, at
`canon` or at a representation `mont k` with a block for Montgomery multiplication (`opOkF`,
`reprOkB`, `fieldRaiseStep_allOps`); the lowering to `jasMod` maps them to the operations of
`opOkM` (`opOkF_block`), each of which has a block in the lowering to `jasminDialect`
(`opOkM_block`): a multiplication at `mont k` becomes `montMul`, lowered by
`ModArithLimbs.montBlock?`. A narrow Montgomery head (an odd modulus `1 < p < 2^64`) is raised
at `mont k` on registers (`raiseBody_isSome_mont`, `castsAt_of_odd`). On `fieldDomB` the
raising is defined (`fieldRaiseStep_isSome_of_dom`), so the whole step is.

## Main definitions

* `castNF`: a program carried along equalities of its context and result types.
* `opOkF`, `opOkM`: the operations the two lowerings accept.
* `lowerBody`, `fieldBodyD`, `fieldLibD`: the lowering of a raised body, the lowered body of
  a tagged head and the inlining library of the lowered bodies.
* `fieldDialectStep`, `fieldDialectCert`: the chain step and its certificate from the
  semantics at `fieldEnv E` to the semantics at `E`, with equal inputs and outputs.

## Main results

* `ctx3_eq`, `val3_cast`: the context and the valuations after the three stages.
* `liftEnv_transports`, `liftEnvM_transports`: the call environments agree at injected calls.
* `fieldRaiseStep_callsAll`, `fieldToModArithStep_callsAll`: the calls of the stages are at
  injected types.
* `fieldRaiseStep_allOps`, `opOkF_block`, `opOkM_block`: the operations of the stages have
  blocks.
* `lowerBody_denoteAt`, `lowerBody_leakRunC`: the lowering of a body keeps its runs.
* `fieldLibD_sound`, `fieldLibD_leakSound`: the library of the lowered bodies is sound.
* `fieldDialectStep_completeOn`: the step is complete on `fieldDomB`.
* `fieldDialectStep_callsAll`, `fieldDialectStep_whileFree`: the step keeps `callsAll C` and
  the absence of exit-flag loops.
* `fieldDialectStep_leakRunC`: two leakage runs before the step at `fieldEnv E'` give two
  runs of its result at `E'` with the same results, with equal events from equal events.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.FieldChainDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom)
open CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal (callsAll callsAll_of_calls
  callsAll_of_callFree callsAll_inline? callsAll_map? callsAll_rename? fieldDomB
  fieldDomB_eq_callsAll fieldCallB fieldFree_seq? PRen.total_ofArgs)
open _root_.Hax.FieldTag (fieldTag? fieldLimbs fieldHeadB)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open Ctxt (Var Valuation)

/-! ## 1. Generic facts -/

section Generic

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- A call of a program that passes `callsAll C` satisfies `C`. -/
theorem calls_of_callsAll (C : String → List d.Ty → List d.Ty → Bool) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : callsAll C p = true) {f : String}
    {as rs : List d.Ty} (hc : p.Calls f as rs) : C f as rs = true := by
  induction p with
  | ret => exact hc.elim
  | var e k ih => exact ih hp hc
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsAll, Bool.and_eq_true] at hp
      rcases hc with h | h
      exacts [ihb hp.1 h, ihk hp.2 h]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsAll, Bool.and_eq_true] at hp
      rcases hc with h | h | h
      exacts [iht hp.1.1 h, ihe hp.1.2 h, ihk hp.2 h]
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsAll, Bool.and_eq_true] at hp
      rcases hc with h | h
      exacts [ihb hp.1 h, ihk hp.2 h]
  | call g _ k ih =>
      simp only [callsAll, Bool.and_eq_true] at hp
      rcases hc with ⟨rfl, rfl, rfl⟩ | h
      exacts [hp.1, ih hp.2 h]

/-- `callsAll` is monotone in the predicate. -/
theorem callsAll_mono {C C' : String → List d.Ty → List d.Ty → Bool}
    (h : ∀ f as rs, C f as rs = true → C' f as rs = true) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hp : callsAll C p = true) : callsAll C' p = true :=
  callsAll_of_calls C' p fun _ _ _ hc => h _ _ _ (calls_of_callsAll C p hp hc)

/-- Dead-binding elimination keeps a run at an explicit call environment. -/
theorem denoteAt_dce [DialectDenoteM d Option] (E : CallEnv d) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) {V : Valuation Γ} {o : Valuation ts}
    (h : p.denoteAt E fuel V = some o) : (NFProg.dce p).denoteAt E fuel V = some o :=
  @NFProg.denote_dce d _ _ _ _ _ ⟨E⟩ Γ ts p fuel V o h

/-- Dead-binding elimination keeps `callsAll C`. -/
theorem callsAll_dce (C : String → List d.Ty → List d.Ty → Bool) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : callsAll C p = true) :
    callsAll C (NFProg.dce p) = true := by
  induction p with
  | ret => rfl
  | var e k ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hk'
        rw [callsAll_rename? C _ hk']
        exact ih hp
      · exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsAll, Bool.and_eq_true] at hp
      simp only [NFProg.dce, callsAll, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsAll, Bool.and_eq_true] at hp
      simp only [NFProg.dce, callsAll, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsAll, Bool.and_eq_true] at hp
      simp only [NFProg.dce, callsAll, ihb hp.1, ihk hp.2, Bool.and_self]
  | call _ _ _ ih =>
      simp only [callsAll, Bool.and_eq_true] at hp
      simp only [NFProg.dce, callsAll, hp.1, ih hp.2, Bool.and_self]

/-- A renamed program has no exit-flag loop exactly when the source has none. -/
theorem whileFree_rename? {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} {f : PRen Γ Δ} {q : NFProg d Δ ts}, NFProg.rename? f p = some q →
      q.whileFree = p.whileFree := by
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
      simp only [NFProg.whileFree, ih hk]
  | forLoop count inits body k ihb ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, _, -, b', hb, k', hk, rfl⟩ := h
      simp only [NFProg.whileFree, ihb hb, ihk hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, t', ht, e', he, k', hk, rfl⟩ := h
      simp only [NFProg.whileFree, iht ht, ihe he, ihk hk]
  | whileLoop inits body k ihb ihk =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb, k', hk, rfl⟩ := h
      rfl
  | call g args k ih =>
      intro Δ f q h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, k', hk, rfl⟩ := h
      simp only [NFProg.whileFree, ih hk]

/-- The splice of a body and a continuation without exit-flag loops has none. -/
theorem whileFree_seq? {Δ : Ctxt d} {rs : List d.Ty} (b : NFProg d Δ rs) :
    ∀ {Γ₀ : Ctxt d} {ts : List d.Ty} (k : NFProg d (rs ++ Γ₀) ts) {Γ : Ctxt d}
      {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ} {q : NFProg d Γ ts}, NFProg.seq? k b ρ θ = some q →
      b.whileFree = true → k.whileFree = true → q.whileFree = true := by
  induction b with
  | ret vs =>
      intro Γ₀ ts k Γ ρ θ q h _ hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff] at h
      obtain ⟨_, -, h⟩ := h
      rw [whileFree_rename? k h, hk]
  | var e b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb', rfl⟩ := h
      exact (ih k hb' hb hk : b'.whileFree = true)
  | forLoop count inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.whileFree, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, _, -, body', hbody, b', hb', rfl⟩ := h
      simp only [NFProg.whileFree, whileFree_rename? body hbody, hb.1, ih k hb' hb.2 hk,
        Bool.and_self]
  | ifThenElse cond thn els b _ _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.whileFree, Bool.and_eq_true] at hb
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, t', ht, e', he, b', hb', rfl⟩ := h
      simp only [NFProg.whileFree, whileFree_rename? thn ht, whileFree_rename? els he, hb.1.1,
        hb.1.2, ih k hb' hb.2 hk, Bool.and_self]
  | whileLoop =>
      intro Γ₀ ts k Γ ρ θ q _ hb _
      simp [NFProg.whileFree] at hb
  | call f args b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb', rfl⟩ := h
      exact (ih k hb' hb hk : b'.whileFree = true)

/-- Inlining keeps the absence of exit-flag loops at a library without operation bodies whose
    call bodies have no exit-flag loop. -/
theorem whileFree_inline? (L : InlineLib d) (hL : ∀ o, L.op o = none)
    (hb : ∀ f as rs b, L.call f as rs = some b → b.whileFree = true) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.whileFree = true) :
    ∀ {q : NFProg d Γ ts}, NFProg.inline? L p = some q → q.whileFree = true := by
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
      simp only [NFProg.whileFree, Bool.and_eq_true] at hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', k', hk', rfl⟩ := h
      simp only [NFProg.whileFree, ihb hp.1 hb', ihk hp.2 hk', Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro q h
      simp only [NFProg.whileFree, Bool.and_eq_true] at hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t', ht', e', he', k', hk', rfl⟩ := h
      simp only [NFProg.whileFree, iht hp.1.1 ht', ihe hp.1.2 he', ihk hp.2 hk', Bool.and_self]
  | whileLoop =>
      intro q _
      simp [NFProg.whileFree] at hp
  | call f args k ih =>
      intro q h
      obtain ⟨k', hk, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i b hbb
        exact whileFree_seq? b k' h (hb _ _ _ _ hbb) (ih hp hk)
      · cases h
        exact ih hp hk

/-- Dead-binding elimination keeps the absence of exit-flag loops. -/
theorem whileFree_dce {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : p.whileFree = true) : (NFProg.dce p).whileFree = true := by
  induction p with
  | ret => rfl
  | var e k ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hk'
        rw [whileFree_rename? _ hk']
        exact ih hp
      · exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [NFProg.whileFree, Bool.and_eq_true] at hp
      simp only [NFProg.dce, NFProg.whileFree, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [NFProg.whileFree, Bool.and_eq_true] at hp
      simp only [NFProg.dce, NFProg.whileFree, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop => simp [NFProg.whileFree] at hp
  | call _ _ _ ih => exact ih hp

end Generic

section MapLoops

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- A block spliced before continuations that return programs without exit-flag loops gives
    a program without exit-flag loops. -/
theorem whileFree_spliceNF? {ts : List d'.Ty} :
    {Δ : Ctxt d'} → {a : d'.Ty} → (blk : Com d' Δ a) →
    (k : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d' Δ' ts)) →
    (∀ {Δ' : Ctxt d'} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) (q : NFProg d' Δ' ts),
      k ren res = some q → q.whileFree = true) →
    ∀ {q : NFProg d' Δ ts}, NFProg.spliceNF? blk k = some q → q.whileFree = true
  | _, _, .ret v, _, hk, _, h => hk _ v _ h
  | _, _, .var _ blk, k, hk, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact whileFree_spliceNF? blk _ (fun ren res q hq => hk _ res q hq) hq'

/-- The conversion `map?` keeps the absence of exit-flag loops. -/
theorem whileFree_map? (P : PartialBlockLowering d d') (hT : P.RegionTypes) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.whileFree = true) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) {q : NFProg d' Δ (ts.map P.mapTy)},
      NFProg.map? P hT p ren = some q → q.whileFree = true := by
  induction p with
  | ret vs =>
      intro Δ ren q h
      cases h
      rfl
  | var e k ih =>
      intro Δ ren q h
      obtain ⟨blk, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact whileFree_spliceNF? _ _ (fun ren' res q' hq' => ih hp _ hq') h
  | forLoop count inits body k ihb ihk =>
      intro Δ ren q h
      simp only [NFProg.whileFree, Bool.and_eq_true] at hp
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [NFProg.whileFree, ihb hp.1 _ hb, ihk hp.2 _ hk, Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren q h
      simp only [NFProg.whileFree, Bool.and_eq_true] at hp
      obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [NFProg.whileFree, iht hp.1.1 _ ht, ihe hp.1.2 _ he, ihk hp.2 _ hk,
        Bool.and_self]
  | whileLoop =>
      intro Δ ren q _
      simp [NFProg.whileFree] at hp
  | call f args k ih =>
      intro Δ ren q h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      exact (ih hp _ hk : k'.whileFree = true)

end MapLoops

/-- The forwarding of loads keeps the absence of exit-flag loops. -/
theorem whileFree_fwdLoad1Go {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (K : NFFwdLoad1.StoreFacts Γ) (ren : Ctxt.Hom Γ Δ),
      (NFFwdLoad1.fwdLoad1Go p K ren).whileFree = p.whileFree := by
  induction p with
  | ret => intro Δ K ren; rfl
  | var e k ih =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go]
      split
      · split
        · exact ih _ _
        · exact ih _ _
      · exact ih _ _
  | forLoop _ _ _ _ ihb ihk =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go, NFProg.whileFree, ihb, ihk]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go, NFProg.whileFree, iht, ihe, ihk]
  | whileLoop => intro Δ K ren; rfl
  | call _ _ _ ih =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go, NFProg.whileFree, ih]

/-- The forwarding of loads keeps `callsAll C`. -/
theorem callsAll_fwdLoad1Go (C : String → List JasminTy → List JasminTy → Bool)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (K : NFFwdLoad1.StoreFacts Γ) (ren : Ctxt.Hom Γ Δ),
      callsAll C (NFFwdLoad1.fwdLoad1Go p K ren) = callsAll C p := by
  induction p with
  | ret => intro Δ K ren; rfl
  | var e k ih =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go]
      split
      · split
        · exact ih _ _
        · exact ih _ _
      · exact ih _ _
  | forLoop _ _ _ _ ihb ihk =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go, callsAll, ihb, ihk]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go, callsAll, iht, ihe, ihk]
  | whileLoop _ _ _ ihb ihk =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go, callsAll, ihb, ihk]
  | call _ _ _ ih =>
      intro Δ K ren
      simp only [NFFwdLoad1.fwdLoad1Go, callsAll, ih]

/-- Two vectors with the same head and heterogeneously equal tails are heterogeneously
    equal. -/
theorem heq_cons {α : Type} {f : α → Type} {a : α} {l l' : List α} (h : l = l') (x : f a)
    {xs : HVector f l} {ys : HVector f l'} (hx : HEq xs ys) :
    HEq (HVector.cons x xs : HVector f (a :: l)) (HVector.cons x ys : HVector f (a :: l')) := by
  subst h
  cases hx
  rfl

/-- Callees at heterogeneously equal arguments and equal signatures are heterogeneously
    equal. -/
theorem heq_call {d : Dialect.{0, 0}} [TyDenote d.Ty] (E : CallEnv d) (f : String)
    {as as' rs rs' : List d.Ty} (ha : as = as') (hr : rs = rs') {x : Valuation as}
    {x' : Valuation as'} (hx : HEq x x') : HEq (E.call f as rs x) (E.call f as' rs' x') := by
  subst ha hr
  cases hx
  rfl

/-- Maps of one option by pointwise heterogeneously equal functions are heterogeneously
    equal. -/
theorem heq_map_option {α β β' : Type} (h : β = β') (o : Option α) (g : α → β) (g' : α → β')
    (hg : ∀ z, HEq (g z) (g' z)) : HEq (o.map g) (o.map g') := by
  subst h
  cases o with
  | none => rfl
  | some z => exact heq_of_eq (congrArg some (eq_of_heq (hg z)))

/-! ## 2. The context and the valuations after the three stages -/

/-- The injected types of `jasField`, lowered to `jasMod`, are the injected types of
    `jasMod`. -/
theorem ctxM_eq : ∀ bs : List JasminTy,
    (bs.map (Sum.inl (β := PfTy))).map FieldToModArithChain.mapTy = bs.map Sum.inl
  | [] => rfl
  | t :: bs => congrArg (Sum.inl t :: ·) (ctxM_eq bs)

/-- The injected types of `jasMod`, lowered to `jasminDialect`, are the types. -/
theorem ctxJ_eq : ∀ bs : List JasminTy,
    (bs.map (Sum.inl (β := ModArithTy))).map ModArithLimbs.mapTy = bs
  | [] => rfl
  | t :: bs => congrArg (t :: ·) (ctxJ_eq bs)

/-- The lowering to `jasMod` of an injected valuation is the injected valuation. -/
theorem liftV_heq_liftVM : ∀ {bs : List JasminTy} (y : HVector (fun t => ⟦t⟧) bs),
    HEq (transArgs FieldToModArithChain.mapTy (fun y => FieldToModArithChain.transTy y)
      (FieldRaise.liftV y)) (FieldToModArithChain.liftVM y)
  | [], .nil => HEq.rfl
  | t :: bs, .cons y ys => by
      exact heq_cons (a := Sum.inl t) (ctxM_eq bs) y (liftV_heq_liftVM ys)

/-- Injecting the stripped valuation of `jasMod` gives the valuation. -/
theorem liftVM_unmapInl : ∀ {as : List JasminTy}
    (x : HVector (fun t => ⟦t⟧) (as.map (Sum.inl (β := ModArithTy)))),
    FieldToModArithChain.liftVM (unmapInl (d := jasminDialect) (e := modArithDialect) x) = x
  | [], .nil => rfl
  | _ :: _, .cons _ xs => congrArg (HVector.cons _) (liftVM_unmapInl xs)

/-- The lowering to `jasminDialect` of an injected valuation is the valuation. -/
theorem liftVM_heq : ∀ {bs : List JasminTy} (y : HVector (fun t => ⟦t⟧) bs),
    HEq (transArgs ModArithLimbs.mapTy (fun y => ModArithLimbs.transTy y)
      (FieldToModArithChain.liftVM y)) y
  | [], .nil => HEq.rfl
  | _ :: bs, .cons y ys => heq_cons (ctxJ_eq bs) y (liftVM_heq ys)

/-- The context after the three stages is the source context. -/
theorem ctx3_eq : ∀ Γ : List JasminTy,
    ((Γ.map Sum.inl).map FieldToModArithChain.mapTy).map ModArithLimbs.mapTy = Γ
  | [] => rfl
  | t :: Γ => congrArg (t :: ·) (ctx3_eq Γ)

/-- The transport of an injected valuation through the two lowerings is the valuation. -/
theorem val3_cast : ∀ {as : List JasminTy} (x : HVector (fun t => ⟦t⟧) as),
    HEq (transArgs ModArithLimbs.mapTy (fun y => ModArithLimbs.transTy y)
      (transArgs FieldToModArithChain.mapTy (fun y => FieldToModArithChain.transTy y)
        (FieldRaise.liftV x))) x
  | [], .nil => HEq.rfl
  | _ :: as, .cons x xs => heq_cons (ctx3_eq as) x (val3_cast xs)

/-- A program of `jasminDialect` carried along equalities of its context and result types. -/
def castNF {Γ Γ' : Ctxt jasminDialect} {ts ts' : List JasminTy} (hΓ : Γ = Γ') (hts : ts = ts')
    (q : NFProg jasminDialect Γ ts) : NFProg jasminDialect Γ' ts' :=
  hΓ ▸ hts ▸ q

/-- A carried program runs from the carried valuation to the carried result. -/
theorem denoteAt_castNF (E : CallEnv jasminDialect) (fuel : Nat) {Γ Γ' : Ctxt jasminDialect}
    {ts ts' : List JasminTy} (hΓ : Γ = Γ') (hts : ts = ts') (q : NFProg jasminDialect Γ ts)
    {W : Valuation Γ} {W' : Valuation Γ'} {o : Valuation (d := jasminDialect) ts}
    {o' : Valuation (d := jasminDialect) ts'}
    (hW : HEq W W') (ho : HEq o o') (h : q.denoteAt E fuel W = some o) :
    (castNF hΓ hts q).denoteAt E fuel W' = some o' := by
  subst hΓ hts
  cases hW
  cases ho
  exact h

/-- A carried program has the leakage runs of the program, from the carried valuation to the
    carried result, with the same events. -/
theorem leakRunMC_castNF (M : LeakModel jasminDialect) (E : CallEnv jasminDialect) (fuel : Nat)
    {Γ Γ' : Ctxt jasminDialect} {ts ts' : List JasminTy} (hΓ : Γ = Γ') (hts : ts = ts')
    (q : NFProg jasminDialect Γ ts) {W : Valuation Γ} {W' : Valuation Γ'}
    {o : Valuation (d := jasminDialect) ts} {o' : Valuation (d := jasminDialect) ts'}
    {l : List CTLeak} (hW : HEq W W') (ho : HEq o o')
    (h : Dialects.NFLeak.NFProg.leakRunMC M E fuel q W = some (o, l)) :
    Dialects.NFLeak.NFProg.leakRunMC M E fuel (castNF hΓ hts q) W' = some (o', l) := by
  subst hΓ hts
  cases hW
  cases ho
  exact h

/-! ## 3. The calls of the stages -/

/-- A call of `jasField` at injected types. -/
def inlCallB (_ : String) (as rs : List (JasminTy ⊕ PfTy)) : Bool :=
  (FieldRaise.ofInl? as).isSome && (FieldRaise.ofInl? rs).isSome

/-- A call of `jasMod` at injected types. -/
def inlCallM (_ : String) (as rs : List (JasminTy ⊕ ModArithTy)) : Bool :=
  (FieldToModArithChain.ofInlM? as).isSome && (FieldToModArithChain.ofInlM? rs).isSome

/-- At injected calls, `liftEnv E` and `liftEnvM E` agree along the lowering to `jasMod`. -/
theorem liftEnv_transports (E : CallEnv jasminDialect) :
    (FieldRaise.liftEnv E).Transports (FieldToModArithChain.liftEnvM E)
      (fun as => as.map FieldToModArithChain.mapTy)
      (fun x => transArgs FieldToModArithChain.mapTy (fun y => FieldToModArithChain.transTy y) x)
      (fun f as rs => inlCallB f as rs = true) := by
  intro f as rs x hc
  simp only [inlCallB, Bool.and_eq_true, Option.isSome_iff_exists] at hc
  obtain ⟨⟨bs, hbs⟩, ⟨cs, hcs⟩⟩ := hc
  obtain rfl := FieldRaise.map_inl_of_ofInl? hbs
  obtain rfl := FieldRaise.map_inl_of_ofInl? hcs
  obtain ⟨y, rfl⟩ : ∃ y, FieldRaise.liftV y = x := ⟨_, FieldRaise.liftV_unmapInl x⟩
  apply eq_of_heq
  refine (heq_call (FieldToModArithChain.liftEnvM E) f (ctxM_eq bs) (ctxM_eq cs)
    (liftV_heq_liftVM y)).trans ?_
  change HEq (FieldToModArithChain.liftCallM E f _ _ (FieldToModArithChain.liftVM y))
    ((FieldRaise.liftCall E f _ _ (FieldRaise.liftV y)).map _)
  rw [FieldToModArithChain.liftCallM_liftVM, FieldRaise.liftCall_liftV, Option.map_map]
  exact heq_map_option (congrArg _ (ctxM_eq cs)).symm _ _ _
    fun z => (liftV_heq_liftVM z).symm

/-- At injected calls, `liftEnvM E` and `E` agree along the lowering to `jasminDialect`. -/
theorem liftEnvM_transports (E : CallEnv jasminDialect) :
    (FieldToModArithChain.liftEnvM E).Transports E
      (fun as => as.map ModArithLimbs.mapTy)
      (fun x => transArgs ModArithLimbs.mapTy (fun y => ModArithLimbs.transTy y) x)
      (fun f as rs => inlCallM f as rs = true) := by
  intro f as rs x hc
  simp only [inlCallM, Bool.and_eq_true, Option.isSome_iff_exists] at hc
  obtain ⟨⟨bs, hbs⟩, ⟨cs, hcs⟩⟩ := hc
  obtain rfl := FieldToModArithChain.map_inl_of_ofInlM? hbs
  obtain rfl := FieldToModArithChain.map_inl_of_ofInlM? hcs
  obtain ⟨y, rfl⟩ : ∃ y, FieldToModArithChain.liftVM y = x :=
    ⟨_, liftVM_unmapInl x⟩
  apply eq_of_heq
  refine (heq_call E f (ctxJ_eq bs) (ctxJ_eq cs) (liftVM_heq y)).trans ?_
  change HEq (E.call f bs cs y)
    ((FieldToModArithChain.liftCallM E f _ _ (FieldToModArithChain.liftVM y)).map _)
  rw [FieldToModArithChain.liftCallM_liftVM, Option.map_map]
  exact (heq_of_eq (Option.map_id' (x := E.call f bs cs y)).symm).trans
    (heq_map_option (congrArg _ (ctxJ_eq cs)).symm _ (fun z => z) _ fun z => (liftVM_heq z).symm)

/-- A raised body has no `call`. -/
theorem raiseBody_callFree {f : String} {as rs : List (JasminTy ⊕ PfTy)}
    {b : NFProg jasField as rs} (h : FieldRaise.raiseBody f as rs = some b) :
    b.callFree = true := by
  have hw : ∀ m p r b', FieldRaise.raiseWord m p as rs r = some b' → b'.callFree = true := by
    intro m p r b' hb
    unfold FieldRaise.raiseWord at hb
    split at hb
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      cases hb
      cases m <;> rfl
    · cases hb
  unfold FieldRaise.raiseBody at h
  split at h
  · rename_i m p _
    have ha : ∀ b', FieldRaise.raiseArr m p as rs = some b' → b'.callFree = true := by
      intro b' hb
      unfold FieldRaise.raiseArr at hb
      split at hb
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        cases hb
        cases m <;> rfl
      · cases hb
    split at h
    · exact hw _ _ _ b h
    · exact ha b h
    · exact hw _ _ _ b h
    · cases h
  · split at h
    · split at h
      · exact hw _ _ _ b h
      · cases h
    · cases h

/-- A raised body has no exit-flag loop. -/
theorem raiseBody_whileFree {f : String} {as rs : List (JasminTy ⊕ PfTy)}
    {b : NFProg jasField as rs} (h : FieldRaise.raiseBody f as rs = some b) :
    b.whileFree = true := by
  have hw : ∀ m p r b', FieldRaise.raiseWord m p as rs r = some b' → b'.whileFree = true := by
    intro m p r b' hb
    unfold FieldRaise.raiseWord at hb
    split at hb
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      cases hb
      cases m <;> rfl
    · cases hb
  unfold FieldRaise.raiseBody at h
  split at h
  · rename_i m p _
    have ha : ∀ b', FieldRaise.raiseArr m p as rs = some b' → b'.whileFree = true := by
      intro b' hb
      unfold FieldRaise.raiseArr at hb
      split at hb
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        cases hb
        cases m <;> rfl
      · cases hb
    split at h
    · exact hw _ _ _ b h
    · exact ha b h
    · exact hw _ _ _ b h
    · cases h
  · split at h
    · split at h
      · exact hw _ _ _ b h
      · cases h
    · cases h

/-- The inclusion into `jasField` keeps the absence of exit-flag loops. -/
theorem whileFree_embed {Γ : Ctxt jasPf} {ts : List jasPf.Ty} (q : NFProg jasPf Γ ts) :
    (FieldRaise.embed q).whileFree = q.whileFree := by
  induction q with
  | ret => rfl
  | var e k ih => exact ih
  | forLoop _ _ _ _ ihb ihk => simp only [FieldRaise.embed, NFProg.whileFree, ihb, ihk]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [FieldRaise.embed, NFProg.whileFree, iht, ihe, ihk]
  | whileLoop => rfl
  | call _ _ _ ih => exact ih

/-- The inclusion into `jasField` keeps the calls. -/
theorem callsAll_embed (C : String → List (JasminTy ⊕ PfTy) → List (JasminTy ⊕ PfTy) → Bool)
    {Γ : Ctxt jasPf} {ts : List jasPf.Ty} (q : NFProg jasPf Γ ts) :
    callsAll C (FieldRaise.embed q) = callsAll C q := by
  induction q with
  | ret => rfl
  | var e k ih => exact ih
  | forLoop _ _ _ _ ihb ihk => simp only [FieldRaise.embed, callsAll, ihb, ihk]
  | ifThenElse _ _ _ _ iht ihe ihk => simp only [FieldRaise.embed, callsAll, iht, ihe, ihk]
  | whileLoop _ _ _ ihb ihk => simp only [FieldRaise.embed, callsAll, ihb, ihk]
  | call _ _ _ ih => simp only [FieldRaise.embed, callsAll, ih]

/-- The inclusion into `jasField` tags every operation `.inl`. -/
theorem allOps_embed (Q : jasField.Op → Bool) {Γ : Ctxt jasPf} {ts : List jasPf.Ty}
    (q : NFProg jasPf Γ ts) :
    (FieldRaise.embed q).allOps Q = q.allOps (fun o => Q (.inl o)) := by
  induction q with
  | ret => rfl
  | var e k ih => simp only [FieldRaise.embed, NFProg.allOps, FieldRaise.embedPfExpr, ih]
  | forLoop _ _ _ _ ihb ihk => simp only [FieldRaise.embed, NFProg.allOps, ihb, ihk]
  | ifThenElse _ _ _ _ iht ihe ihk => simp only [FieldRaise.embed, NFProg.allOps, iht, ihe, ihk]
  | whileLoop _ _ _ ihb ihk => simp only [FieldRaise.embed, NFProg.allOps, ihb, ihk]
  | call _ _ _ ih => simp only [FieldRaise.embed, NFProg.allOps, ih]

/-- **The calls of the raised program are at injected types.** -/
theorem fieldRaiseStep_callsAll {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {r : NFProg jasField (Γ.map Sum.inl) (ts.map Sum.inl)}
    (hr : (FieldRaise.fieldRaiseStep Γ ts).run p = some r) : callsAll inlCallB r = true := by
  obtain ⟨q, hq, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨r0, hr0, hif⟩ := Option.bind_eq_some_iff.mp hr
  split at hif
  · cases hif
    refine callsAll_inline? inlCallB FieldRaise.raiseLib (fun _ => rfl)
      (fun _ _ _ b hb => callsAll_of_callFree _ b (raiseBody_callFree hb)) (FieldRaise.embed q) ?_
      hr0
    rw [callsAll_embed]
    exact callsAll_map? FieldRaise.liftJ FieldRaise.liftJ_regionTypes inlCallB p
      (callsAll_of_calls _ p fun _ as rs _ => by
        simp [inlCallB, FieldRaise.liftJ, FieldRaise.ofInl?_map]) _ hq
  · cases hif

/-- **The lowering to `jasMod` keeps the calls at injected types.** -/
theorem fieldToModArithStep_callsAll {Γ : Ctxt jasField} {ts : List jasField.Ty}
    {r : NFProg jasField Γ ts} (hr : callsAll inlCallB r = true)
    {q : NFProg jasMod (Γ.map FieldToModArithChain.mapTy) (ts.map FieldToModArithChain.mapTy)}
    (hq : (FieldToModArithChain.fieldToModArithStep Γ ts).run r = some q) :
    callsAll inlCallM q = true := by
  refine callsAll_map? FieldToModArithChain.fieldToModArithJ FieldToModArithChain.regionTypes
    inlCallM r (callsAll_mono ?_ r hr) _ hq
  intro f as rs h
  simp only [inlCallB, Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨bs, hbs⟩, ⟨cs, hcs⟩⟩ := h
  obtain rfl := FieldRaise.map_inl_of_ofInl? hbs
  obtain rfl := FieldRaise.map_inl_of_ofInl? hcs
  show ((FieldToModArithChain.ofInlM? ((bs.map Sum.inl).map FieldToModArithChain.mapTy)).isSome &&
    (FieldToModArithChain.ofInlM? ((cs.map Sum.inl).map FieldToModArithChain.mapTy)).isSome) = true
  rw [ctxM_eq, ctxM_eq, FieldToModArithChain.ofInlM?_map, FieldToModArithChain.ofInlM?_map]
  rfl

/-! ## 4. The operations of the stages -/

/-- The modulus `p` has a block for Montgomery multiplication (`ModArithLimbs.montBlock?`):
    its template at `canon` has the cast block from its `64`-bit words, `p ≠ 0` and
    `p ≤ 2 ^ (64 * T.limbs)`. -/
def montOkB (p : Nat) : Bool :=
  (ModArithLimbs.canonTemplateOf p).any fun T =>
    (T.ofWords 64 T.limbs).isSome && decide (p ≠ 0 ∧ p ≤ 2 ^ (64 * T.limbs))

/-- The representations the two lowerings accept at the modulus `p`: `canon`, and `mont k`
    at an odd modulus with a block for Montgomery multiplication (`montOkB`). -/
def reprOkB (p : Nat) : FieldRepr → Bool
  | .canon => true
  | .mont _ => decide (Nat.Coprime 2 p) && montOkB p

/-- The operations of `jasField` the two lowerings accept: the operations of `jasminDialect`,
    the field operations at a modulus with a template at `canon`, and the casts the template
    has a block for, each at a representation of `reprOkB`. -/
def opOkF : jasField.Op → Bool
  | .inl (.inl _) => true
  | .inl (.inr (.add p r)) | .inl (.inr (.sub p r)) | .inl (.inr (.mul p r))
  | .inl (.inr (.neg p r)) | .inl (.inr (.square p r))
  | .inl (.inr (.double p r)) => (ModArithLimbs.canonTemplateOf p).isSome && reprOkB p r
  | .inr (.fromWords p r w n) =>
      reprOkB p r && (ModArithLimbs.canonTemplateOf p).any fun T => (T.ofWords w n).isSome
  | .inr (.toWords p r w n) =>
      reprOkB p r && (ModArithLimbs.canonTemplateOf p).any fun T => (T.toWords w n).isSome
  | _ => false

/-- The operations of `jasMod` the lowering to `jasminDialect` accepts. -/
def opOkM : jasMod.Op → Bool
  | .inl (.inl _) => true
  | .inl (.inr (.modAdd p)) | .inl (.inr (.modSub p)) | .inl (.inr (.modMul p))
  | .inl (.inr (.modNeg p)) => (ModArithLimbs.canonTemplateOf p).isSome
  | .inl (.inr (.modCopy _)) => true
  | .inl (.inr (.montMul p _)) => montOkB p
  | .inr (.fromWordsM p w n) =>
      (ModArithLimbs.canonTemplateOf p).any fun T => (T.ofWords w n).isSome
  | .inr (.toWordsM p w n) =>
      (ModArithLimbs.canonTemplateOf p).any fun T => (T.toWords w n).isSome
  | _ => false

/-- An accepted operation of `jasField` has a block in the lowering to `jasMod`. -/
theorem opOkF_lower_isSome {Γ : Ctxt jasField} {t : jasField.Ty} (e : Expr jasField Γ t)
    (he : opOkF e.op = true) :
    (FieldToModArithChain.fieldToModArithJ.lowerExprBlock? e).isSome = true := by
  obtain ⟨op, rfl, args⟩ := e
  rcases op with (o | o) | o
  · rfl
  · cases o <;> (try cases ‹FieldRepr›) <;> first
      | rfl
      | (simp [opOkF] at he; done)
      | (simp only [opOkF, reprOkB, Bool.and_eq_true, decide_eq_true_eq,
           Nat.coprime_two_left] at he
         simp [FieldToModArithChain.fieldToModArithJ, FieldToModArithChain.lowerBlock?,
           FieldToModArithChain.opBlock?, FieldToModArithChain.pfBlock?, he])
  · cases o <;> (try cases ‹FieldRepr›) <;> first
      | rfl
      | (simp only [opOkF, reprOkB, Bool.and_eq_true, decide_eq_true_eq,
           Nat.coprime_two_left] at he
         simp [FieldToModArithChain.fieldToModArithJ, FieldToModArithChain.lowerBlock?,
           FieldToModArithChain.opBlock?, FieldToModArithChain.castBlock?,
           FieldRepr.Admits, he])

/-- The block of an accepted operation of `jasField` has accepted operations of `jasMod`. -/
theorem opOkF_block {Γ : Ctxt jasField} {t : jasField.Ty} (e : Expr jasField Γ t)
    (he : opOkF e.op = true) (blk : Com jasMod _ _)
    (hb : FieldToModArithChain.fieldToModArithJ.lowerExprBlock? e = some blk) :
    CoveredCom (fun e' => opOkM e'.op = true) blk := by
  obtain ⟨op, rfl, args⟩ := e
  rcases op with (o | o) | o
  · cases hb
    exact ⟨rfl, trivial⟩
  all_goals cases o <;> (try cases ‹FieldRepr›) <;> first
    | (simp [opOkF] at he; done)
    | (simp only [opOkF, reprOkB, Bool.and_eq_true] at he
       simp only [FieldToModArithChain.fieldToModArithJ, FieldToModArithChain.lowerBlock?,
         FieldToModArithChain.opBlock?, FieldToModArithChain.pfBlock?,
         FieldToModArithChain.castBlock?] at hb
       (try split at hb) <;> cases hb
       exact ⟨by simp [opOkM, he], trivial⟩)

/-- The body of a method under a template has a block. -/
theorem bodyBlock?_isSome {Δ : Ctxt jasminDialect} {p : Nat}
    (o : Option (Algebraic.ModArithLimbTemplate p .canon)) (ho : o.isSome = true)
    (m : _root_.Hax.FieldTag.FieldMethod)
    (args : HVector (fun t => Var Δ t) (Algebraic.ModArithLimbTemplate.limbSig
      (ModArithLimbs.optTy o) m)) :
    (ModArithLimbs.bodyBlock? o m args).isSome = true := by
  cases o with
  | none => cases ho
  | some T => rfl

/-- The cast `fromWordsM` has a block under a template with a block at `w` bits and `n`
    words. -/
theorem ofWordsBlock?_isSome {Δ : Ctxt jasminDialect} {p : Nat}
    (o : Option (Algebraic.ModArithLimbTemplate p .canon)) {w n : Nat}
    (ho : (o.any fun T => (T.ofWords w n).isSome) = true) (a : Var Δ (.stackArr w n)) :
    (ModArithLimbs.ofWordsBlock? o w n a).isSome = true := by
  cases o with
  | none => cases ho
  | some T =>
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp ho
      show ((T.ofWords w n).map _).isSome = true
      rw [hc]
      rfl

/-- The cast `toWordsM` has a block under a template with a block at `w` bits and `n`
    words. -/
theorem toWordsBlock?_isSome {Δ : Ctxt jasminDialect} {p : Nat}
    (o : Option (Algebraic.ModArithLimbTemplate p .canon)) {w n : Nat}
    (ho : (o.any fun T => (T.toWords w n).isSome) = true) (a : Var Δ (ModArithLimbs.optTy o)) :
    (ModArithLimbs.toWordsBlock? o w n a).isSome = true := by
  cases o with
  | none => cases ho
  | some T =>
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp ho
      show ((T.toWords w n).map _).isSome = true
      rw [hc]
      rfl

/-- Montgomery multiplication has a block under a template with the cast block from its
    `64`-bit words, at `p ≠ 0` and `p ≤ 2 ^ (64 * T.limbs)`. -/
theorem montBlock?_isSome {Δ : Ctxt jasminDialect} {p : Nat}
    (o : Option (Algebraic.ModArithLimbTemplate p .canon))
    (ho : (o.any fun T => (T.ofWords 64 T.limbs).isSome &&
      decide (p ≠ 0 ∧ p ≤ 2 ^ (64 * T.limbs))) = true) (c : ZMod p)
    (a b : Var Δ (ModArithLimbs.optTy o)) :
    (ModArithLimbs.montBlock? o c a b).isSome = true := by
  cases o with
  | none => cases ho
  | some T =>
      simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at ho
      rw [ModArithLimbs.montBlock?, dite_eq_left ho]
      rfl

/-- An accepted operation of `jasMod` has a block. -/
theorem opOkM_block {Γ : Ctxt jasMod} {t : jasMod.Ty} (e : Expr jasMod Γ t)
    (he : opOkM e.op = true) : (ModArithLimbs.modArithLimbsJ.lowerExprBlock? e).isSome = true := by
  obtain ⟨op, rfl, args⟩ := e
  rcases op with (o | o) | o
  · rfl
  · cases o
    all_goals first
      | exact bodyBlock?_isSome _ he _ _
      | (simp only [ModArithLimbs.modArithLimbsJ, ModArithLimbs.limbLowerBlock?,
          ModArithLimbs.limbOpBlock?, ModArithLimbs.modBlock?]
         split <;> exact bodyBlock?_isSome _ he _ _)
      | exact montBlock?_isSome _ he _ _ _
      | rfl
      | (simp [opOkM] at he)
  · cases o
    · exact ofWordsBlock?_isSome _ he _
    · exact toWordsBlock?_isSome _ he _

/-- A template at `canon` with the cast blocks at `n` words of `64` bits. -/
def CastsAt (p n : Nat) : Prop :=
  ∃ T : Algebraic.ModArithLimbTemplate p .canon, ModArithLimbs.canonTemplateOf p = some T ∧
    (T.ofWords 64 n).isSome = true ∧ (T.toWords 64 n).isSome = true

/-- A modulus with a narrow representation has a template with the one-word cast blocks. -/
theorem castsAt_narrow {p : Nat} {F : Algebraic.FieldWord.SingleWordField p}
    (hn : narrowFieldOf p = some F) : CastsAt p 1 := by
  unfold CastsAt ModArithLimbs.canonTemplateOf
  split
  · exact ⟨_, rfl, rfl, rfl⟩
  · rename_i hn'
    rw [hn'] at hn
    cases hn

/-- A modulus with a wide template and no narrow representation has a template with the
    cast blocks at `fieldLimbs p` words. -/
theorem castsAt_wide {p : Nat} {W : FieldWideInline.WideTemplate p (fieldLimbs p)}
    (hn : narrowFieldOf p = none) (hw : FieldWideInline.wideTemplateOf p = some W) :
    CastsAt p (fieldLimbs p) := by
  unfold CastsAt ModArithLimbs.canonTemplateOf
  split
  · rename_i hn'
    rw [hn'] at hn
    cases hn
  · split
    · refine ⟨_, rfl, ?_, ?_⟩
      · show (ModArithLimbs.arrOfWords (fieldLimbs p) 64 (fieldLimbs p)).isSome = true
        simp [ModArithLimbs.arrOfWords]
      · show (ModArithLimbs.arrToWords (fieldLimbs p) 64 (fieldLimbs p)).isSome = true
        simp [ModArithLimbs.arrToWords]
    · rename_i hw'
      rw [hw'] at hw
      cases hw

/-- A modulus with a one-limb Montgomery record and neither a narrow representation nor a
    wide template has a template with the one-word cast blocks. -/
theorem castsAt_mont {p : Nat} {P : Algebraic.FieldLimbs.Mont.LimbParams 1}
    (hn : narrowFieldOf p = none) (hw : FieldWideInline.wideTemplateOf p = none)
    (hm : FieldWideInline.montWordOf p = some P) : CastsAt p 1 := by
  unfold CastsAt ModArithLimbs.canonTemplateOf
  split
  · rename_i hn'
    rw [hn'] at hn
    cases hn
  · split
    · rename_i hw'
      rw [hw'] at hw
      cases hw
    · split
      · exact ⟨_, rfl, rfl, rfl⟩
      · rename_i hm'
        rw [hm'] at hm
        cases hm

/-- Every odd modulus `1 < p < 2^64` has a template with the one-word cast blocks: the
    narrow template, else the one-limb Montgomery record. -/
theorem castsAt_of_odd {p : Nat} (h1 : 1 < p) (hodd : p % 2 = 1) (hp : p < 2 ^ 64) :
    CastsAt p 1 := by
  rcases hn : narrowFieldOf p with _ | F
  · rcases hw : FieldWideInline.wideTemplateOf p with _ | W
    · rcases hm : FieldWideInline.montWordOf p with _ | P
      · have := FieldWideInline.montWordOf_isSome h1 hodd hp
        rw [hm] at this
        cases this
      · exact castsAt_mont hn hw hm
    · have := ModArithLimbs.le_of_wideTemplateOf hw
      omega
  · exact castsAt_narrow hn

/-- Every representation `mont k` is accepted at an odd modulus `1 < p < 2^64`. -/
theorem reprOkB_mont {p : Nat} (k : Nat) (h1 : 1 < p) (hodd : p % 2 = 1) (hp : p < 2 ^ 64) :
    reprOkB p (.mont k) = true := by
  obtain ⟨T, hT, hw, hpw⟩ := ModArithLimbs.canonTemplateOf_mont h1 hodd hp
  simp only [reprOkB, montOkB, hT, Option.any_some, hw, Bool.true_and, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd), by omega, hpw⟩

/-- The raised body on registers at an accepted representation has accepted operations. -/
theorem raiseWord_allOps {m : _root_.Hax.FieldTag.FieldMethod} {p : Nat} {r : FieldRepr}
    (hc : CastsAt p 1) (hr : reprOkB p r = true)
    {as rs : List (JasminTy ⊕ PfTy)} {b : NFProg jasField as rs}
    (h : FieldRaise.raiseWord m p as rs r = some b) : b.allOps opOkF = true := by
  obtain ⟨T, hT, h1, h2⟩ := hc
  unfold FieldRaise.raiseWord at h
  split at h
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    cases h
    show NFProg.allOps opOkF (FieldRaise.wordBody m p r) = true
    cases m <;> simp only [FieldRaise.wordBody, FieldRaise.wordBody2, FieldRaise.wordBody1,
      FieldRaise.wordTail, NFProg.allOps, FieldRaise.zeroE, FieldRaise.storeE, FieldRaise.fromE,
      FieldRaise.toE, FieldRaise.constE, FieldRaise.loadE, FieldRaise.opE, opOkF, hT, hr,
      Option.any_some, Option.isSome_some, h1, h2, Bool.and_self]
  · cases h

/-- The raised body on arrays has accepted operations. -/
theorem raiseArr_allOps {m : _root_.Hax.FieldTag.FieldMethod} {p : Nat}
    (hc : CastsAt p (fieldLimbs p)) {as rs : List (JasminTy ⊕ PfTy)}
    {b : NFProg jasField as rs} (h : FieldRaise.raiseArr m p as rs = some b) :
    b.allOps opOkF = true := by
  obtain ⟨T, hT, h1, h2⟩ := hc
  unfold FieldRaise.raiseArr at h
  split at h
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    cases h
    show NFProg.allOps opOkF (FieldRaise.arrBody m p (fieldLimbs p)) = true
    cases m <;> simp only [FieldRaise.arrBody, FieldRaise.arrBody2, FieldRaise.arrBody1,
      NFProg.allOps, FieldRaise.fromE, FieldRaise.toE, FieldRaise.opE, opOkF, reprOkB, hT,
      Option.any_some, Option.isSome_some, h1, h2, Bool.and_self]
  · cases h

/-- **The heads the field dialect step lowers**: a head that is no Montgomery head, or a
    Montgomery head at a modulus `1 < p`. -/
def montLowB (f : String) : Bool :=
  (_root_.Hax.FieldTag.fieldTagM? f).all fun mpk => decide (1 < mpk.2.1)

/-- A raised body of a head of `montLowB` has accepted operations. -/
theorem raiseBody_allOps {f : String} {as rs : List (JasminTy ⊕ PfTy)}
    (hM : montLowB f = true)
    {b : NFProg jasField as rs} (h : FieldRaise.raiseBody f as rs = some b) :
    b.allOps opOkF = true := by
  unfold FieldRaise.raiseBody at h
  split at h
  · split at h
    · rename_i hn
      exact raiseWord_allOps (castsAt_narrow hn) rfl h
    · rename_i hn hw
      exact raiseArr_allOps (castsAt_wide hn hw) h
    · rename_i hn hw hm
      exact raiseWord_allOps (castsAt_mont hn hw hm) rfl h
    · cases h
  · split at h
    · rename_i m p k hm
      split at h
      · rename_i hc
        have h1 : 1 < p := by simpa [montLowB, hm] using hM
        exact raiseWord_allOps (castsAt_of_odd h1 hc.1 hc.2) (reprOkB_mont k h1 hc.1 hc.2) h
      · cases h
    · cases h

/-- **Inlining keeps an operation predicate on the programs whose calls pass `C`**, when it
    holds of every body of the library at a call that passes `C`. -/
theorem allOps_inline?_of_callsAll (L : InlineLib jasField) (Q : jasField.Op → Bool)
    (C : String → List jasField.Ty → List jasField.Ty → Bool)
    (hop : ∀ o b, L.op o = some b → b.allOps Q = true)
    (hcall : ∀ f as rs b, C f as rs = true → L.call f as rs = some b → b.allOps Q = true)
    {Γ : Ctxt jasField} {ts : List jasField.Ty} (p : NFProg jasField Γ ts) :
    callsAll C p = true → ∀ {q : NFProg jasField Γ ts}, NFProg.inline? L p = some q →
      p.allOps Q = true → q.allOps Q = true := by
  induction p with
  | ret vs =>
      intro _ q h _
      cases h
      rfl
  | var e k ih =>
      intro hC q h hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff] at h
      obtain ⟨k', hk', h⟩ := h
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      have hk := ih hC hk' hp.2
      obtain ⟨o, rfl, args⟩ := e
      simp only [NFProg.inlineVar] at h
      split at h
      · rename_i b hb
        exact FieldInlineOps.allOps_seq? Q b k' _ _ h (hop o b hb) hk
      · cases h
        simp only [NFProg.allOps, Bool.and_eq_true]
        exact ⟨hp.1, hk⟩
  | forLoop count inits body k ihb ihk =>
      intro hC q h hp
      simp only [callsAll, Bool.and_eq_true] at hC
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', k', hk', rfl⟩ := h
      simp only [NFProg.allOps, Bool.and_eq_true] at hp ⊢
      exact ⟨ihb hC.1 hb' hp.1, ihk hC.2 hk' hp.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro hC q h hp
      simp only [callsAll, Bool.and_eq_true] at hC
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t', ht', e', he', k', hk', rfl⟩ := h
      simp only [NFProg.allOps, Bool.and_eq_true] at hp ⊢
      exact ⟨⟨iht hC.1.1 ht' hp.1.1, ihe hC.1.2 he' hp.1.2⟩, ihk hC.2 hk' hp.2⟩
  | whileLoop inits body k ihb ihk =>
      intro hC q h hp
      simp only [callsAll, Bool.and_eq_true] at hC
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', k', hk', rfl⟩ := h
      simp only [NFProg.allOps, Bool.and_eq_true] at hp ⊢
      exact ⟨ihb hC.1 hb' hp.1, ihk hC.2 hk' hp.2⟩
  | call f args k ih =>
      intro hC q h hp
      simp only [callsAll, Bool.and_eq_true] at hC
      simp only [NFProg.inline?, Option.bind_eq_some_iff] at h
      obtain ⟨k', hk', h⟩ := h
      simp only [NFProg.allOps] at hp
      have hk := ih hC.2 hk' hp
      split at h
      · rename_i b hb
        exact FieldInlineOps.allOps_seq? Q b k' _ _ h (hcall _ _ _ b hC.1 hb) hk
      · cases h
        exact hk

/-- A call in the domain of the field dialect step has a head of `montLowB`. -/
theorem montLowB_of_fieldCallB {f : String} {as rs : List JasminTy}
    (h : fieldCallB f as rs = true) : montLowB f = true := by
  simp only [fieldCallB, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with (h | h) | h
  · simp [montLowB, (_root_.Hax.FieldTag.fieldHeadB_eq_false_iff.mp h).2]
  · have ht := fieldTag?_isSome_of_fieldBody h
    cases hm : _root_.Hax.FieldTag.fieldTagM? f with
    | none => simp [montLowB, hm]
    | some mpk =>
        obtain ⟨m, p, k⟩ := mpk
        rw [_root_.Hax.FieldTag.fieldTag?_of_fieldTagM? hm] at ht
        cases ht
  · unfold ChainTotal.fieldCallMontB at h
    split at h
    · rename_i m p k hm
      simpa [montLowB, hm] using (of_decide_eq_true h).1
    · cases h

/-- The embedding of a program of `fieldDomB` calls heads of `montLowB` only. -/
theorem callsAll_embed_montLowB {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hp : fieldDomB p = true)
    {q : NFProg jasPf (Γ.map Sum.inl) (ts.map Sum.inl)}
    (hq : NFProg.map? FieldRaise.liftJ FieldRaise.liftJ_regionTypes p (fun v => v) = some q) :
    callsAll (fun f _ _ => montLowB f) (FieldRaise.embed q) =
      true := by
  rw [fieldDomB_eq_callsAll] at hp
  rw [callsAll_embed]
  exact callsAll_map? FieldRaise.liftJ FieldRaise.liftJ_regionTypes _ p
    (callsAll_mono (fun f as rs h => montLowB_of_fieldCallB h) p hp) _ hq

/-- **The raised program of a program of `fieldDomB` has accepted operations.** -/
theorem fieldRaiseStep_allOps {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hd : fieldDomB p = true)
    {r : NFProg jasField (Γ.map Sum.inl) (ts.map Sum.inl)}
    (hr : (FieldRaise.fieldRaiseStep Γ ts).run p = some r) : r.allOps opOkF = true := by
  obtain ⟨q, hq, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨r0, hr0, hif⟩ := Option.bind_eq_some_iff.mp hr
  split at hif
  · cases hif
    refine allOps_inline?_of_callsAll FieldRaise.raiseLib opOkF _ (fun _ _ hb => by cases hb)
      (fun _ _ _ b hM hb => raiseBody_allOps hM hb) (FieldRaise.embed q)
      (callsAll_embed_montLowB hd hq) hr0 ?_
    rw [allOps_embed]
    refine JasminImageOps.allOps_map? FieldRaise.liftJ FieldRaise.liftJ_regionTypes _ p
      (NFProg.covered_of_forall _ (fun e blk hb => ?_) p) _ q hq
    cases hb
    exact ⟨rfl, trivial⟩
  · cases hif

/-! ## 5. The raising on the domain of the inlining step -/

/-- Inlining the raised bodies is defined, and calls no field head, on a program each of
    whose calls has a head that is no field head or a head with a raised body. -/
theorem inline?_raiseLib_of_dom {Γ : Ctxt jasField} {ts : List jasField.Ty}
    (s : NFProg jasField Γ ts)
    (hs : callsAll (fun f as rs => !fieldHeadB f || (FieldRaise.raiseBody f as rs).isSome)
      s = true) :
    ∃ r, NFProg.inline? FieldRaise.raiseLib s = some r ∧ fieldFree r = true := by
  induction s with
  | ret vs => exact ⟨_, rfl, rfl⟩
  | var e k ih =>
      obtain ⟨k', hk, hf⟩ := ih hs
      obtain ⟨o, rfl, args⟩ := e
      refine ⟨.var ⟨o, rfl, args⟩ k', ?_, hf⟩
      simp only [NFProg.inline?, hk, Option.bind_some, NFProg.inlineVar,
        show FieldRaise.raiseLib.op o = none from rfl]
  | forLoop count inits body k ihb ihk =>
      simp only [callsAll, Bool.and_eq_true] at hs
      obtain ⟨b', hb, hfb⟩ := ihb hs.1
      obtain ⟨k', hk, hfk⟩ := ihk hs.2
      exact ⟨.forLoop count inits b' k', by
        simp only [NFProg.inline?, hb, hk, Option.bind_some, Option.map_some],
        by simp only [fieldFree, hfb, hfk, Bool.and_self]⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [callsAll, Bool.and_eq_true] at hs
      obtain ⟨t', ht, hft⟩ := iht hs.1.1
      obtain ⟨e', he, hfe⟩ := ihe hs.1.2
      obtain ⟨k', hk, hfk⟩ := ihk hs.2
      exact ⟨.ifThenElse cond t' e' k', by
        simp only [NFProg.inline?, ht, he, hk, Option.bind_some, Option.map_some],
        by simp only [fieldFree, hft, hfe, hfk, Bool.and_self]⟩
  | whileLoop inits body k ihb ihk =>
      simp only [callsAll, Bool.and_eq_true] at hs
      obtain ⟨b', hb, hfb⟩ := ihb hs.1
      obtain ⟨k', hk, hfk⟩ := ihk hs.2
      exact ⟨.whileLoop inits b' k', by
        simp only [NFProg.inline?, hb, hk, Option.bind_some, Option.map_some],
        by simp only [fieldFree, hfb, hfk, Bool.and_self]⟩
  | call f args k ih =>
      simp only [callsAll, Bool.and_eq_true, Bool.or_eq_true] at hs
      obtain ⟨k', hk, hf⟩ := ih hs.2
      simp only [NFProg.inline?, hk, Option.bind_some]
      split
      · rename_i b hb
        obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
          (NFProg.seq?_isSome_of_total b k' (PRen.total_ofArgs args) PRen.total_id)
        exact ⟨q, hq, fieldFree_seq? b k' hq
          (fieldFree_of_callFree b (raiseBody_callFree hb)) hf⟩
      · rename_i hb
        have hn : (!fieldHeadB f) = true := by
          rcases hs.1 with h | h
          · exact h
          · exact absurd h (by simp [show FieldRaise.raiseBody f _ _ = none from hb])
        exact ⟨_, rfl, by simp only [fieldFree, hn, hf, Bool.and_self]⟩

/-- A narrow Montgomery head at its signature has a raised body. -/
theorem raiseBody_isSome_mont {f : String} {as rs : List JasminTy}
    (h : ChainTotal.fieldCallMontB f as rs = true) :
    (FieldRaise.raiseBody f (as.map Sum.inl) (rs.map Sum.inl)).isSome = true := by
  unfold ChainTotal.fieldCallMontB at h
  split at h
  · rename_i m p k hm
    obtain ⟨-, hodd, hp, rfl, rfl⟩ := of_decide_eq_true h
    unfold FieldRaise.raiseBody
    rw [_root_.Hax.FieldTag.fieldTag?_of_fieldTagM? hm, hm]
    simp only [ite_eq_left (And.intro hodd hp), FieldRaise.raiseWord, FieldRaise.fieldJSig_eq_wordSig]
    rw [dite_eq_left ⟨trivial, rfl⟩]
    rfl
  · cases h

/-- **The raising step is defined on `fieldDomB`.** -/
theorem fieldRaiseStep_isSome_of_dom {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : fieldDomB p = true) :
    ∃ r, (FieldRaise.fieldRaiseStep Γ ts).run p = some r := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
    ((NFProg.isSome_map?_iff FieldRaise.liftJ FieldRaise.liftJ_regionTypes p (fun v => v)).2
      (NFProg.covered_of_forall _ (fun _ => rfl) p))
  rw [fieldDomB_eq_callsAll] at hp
  have hs : callsAll (fun f as rs => !fieldHeadB f ||
      (FieldRaise.raiseBody f as rs).isSome) (FieldRaise.embed q) = true := by
    rw [callsAll_embed]
    refine callsAll_map? FieldRaise.liftJ FieldRaise.liftJ_regionTypes _ p
      (callsAll_mono ?_ p hp) _ hq
    intro f as rs h
    show (!fieldHeadB f ||
      (FieldRaise.raiseBody f (as.map Sum.inl) (rs.map Sum.inl)).isSome) = true
    simp only [fieldCallB, Bool.or_eq_true] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl h
    · right
      rw [FieldRaise.raiseBody_isSome f as rs (fieldTag?_isSome_of_fieldBody h)]
      exact h
    · exact Or.inr (raiseBody_isSome_mont h)
  obtain ⟨r, hr, hf⟩ := inline?_raiseLib_of_dom _ hs
  refine ⟨r, ?_⟩
  change ((NFProg.map? FieldRaise.liftJ FieldRaise.liftJ_regionTypes p (fun v => v)).bind
    fun q => (NFProg.inline? FieldRaise.raiseLib (FieldRaise.embed q)).bind
      fun r => if fieldFree r then some r else none) = some r
  rw [hq, Option.bind_some, hr, Option.bind_some, ite_eq_left hf]

/-! ## 6. The lowered bodies -/

/-- The leakage model of `modArithDialect` whose operations are quiet. -/
def quietModLeak : LeakModel modArithDialect := ⟨fun _ => .quiet, fun _ _ => 0⟩

/-- A carried program passes `callsAll C` exactly when the program does. -/
theorem callsAll_castNF (C : String → List JasminTy → List JasminTy → Bool)
    {Γ Γ' : Ctxt jasminDialect} {ts ts' : List JasminTy} (hΓ : Γ = Γ') (hts : ts = ts')
    (q : NFProg jasminDialect Γ ts) : callsAll C (castNF hΓ hts q) = callsAll C q := by
  subst hΓ hts
  rfl

/-- A carried program has an exit-flag loop exactly when the program has one. -/
theorem whileFree_castNF {Γ Γ' : Ctxt jasminDialect} {ts ts' : List JasminTy} (hΓ : Γ = Γ')
    (hts : ts = ts') (q : NFProg jasminDialect Γ ts) :
    (castNF hΓ hts q).whileFree = q.whileFree := by
  subst hΓ hts
  rfl

/-- **The lowering of a raised body** at the signature `as → rs`: the body is lowered to
    `mod_arith` (`fieldToModArithStep`) and to the limb templates in `jasminDialect`
    (`modArithLimbsStep`), carried back to the signature (`castNF`, `ctx3_eq`), its loads from
    one-word arrays are forwarded (`fwdLoad1`) and its dead bindings removed (`dce`). -/
def lowerBody (as rs : List JasminTy) (r₁ : NFProg jasField (as.map Sum.inl) (rs.map Sum.inl)) :
    Option (NFProg jasminDialect as rs) :=
  ((FieldToModArithChain.fieldToModArithStep _ _).run r₁).bind fun r₂ =>
  ((ModArithLimbs.modArithLimbsStep _ _).run r₂).map fun r₃ =>
    NFProg.dce (NFFwdLoad1.fwdLoad1 (castNF (ctx3_eq as) (ctx3_eq rs) r₃))

/-- **The lowered body of a head of `montLowB`** at the signature `as → rs`: the raised body
    (`FieldRaise.raiseBody`) at the injected signature, lowered by `lowerBody`; `none` at a
    Montgomery head at a modulus `p ≤ 1`. At a Montgomery head the multiplications lower to
    Montgomery multiplication on the limb template (`ModArithLimbs.montBlock?`). -/
def fieldBodyD (f : String) (as rs : List JasminTy) : Option (NFProg jasminDialect as rs) :=
  if montLowB f then
    (FieldRaise.raiseBody f (as.map Sum.inl) (rs.map Sum.inl)).bind (lowerBody as rs)
  else none

/-- A lowered body is the lowering of the raised body of a head of `montLowB`. -/
theorem fieldBodyD_some {f : String} {as rs : List JasminTy} {b : NFProg jasminDialect as rs}
    (hb : fieldBodyD f as rs = some b) :
    montLowB f = true ∧
      ∃ r₁, FieldRaise.raiseBody f (as.map Sum.inl) (rs.map Sum.inl) = some r₁ ∧
        lowerBody as rs r₁ = some b := by
  unfold fieldBodyD at hb
  split at hb
  · rename_i hM
    exact ⟨hM, Option.bind_eq_some_iff.mp hb⟩
  · cases hb

/-- **The inlining library of the lowered bodies**: no operation has a body, and a `call` of
    a tagged head has the lowered body `fieldBodyD`. -/
def fieldLibD : InlineLib jasminDialect where
  op _ := none
  call := fieldBodyD

/-- A program each of whose calls fails `fun _ _ _ => false` has no `call`. -/
theorem callFree_of_callsAll_false {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : callsAll (fun _ _ _ => false) p = true) : p.callFree = true := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [callsAll, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [callsAll, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [callsAll, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, ihb hp.1, ihk hp.2, Bool.and_self]
  | call _ _ _ _ => simp [callsAll] at hp

/-- A lowered body keeps `callsAll C` of a body without `call`. -/
theorem lowerBody_callsAll (C : String → List JasminTy → List JasminTy → Bool)
    {as rs : List JasminTy} {r₁ : NFProg jasField (as.map Sum.inl) (rs.map Sum.inl)}
    (hr : r₁.callFree = true) {b : NFProg jasminDialect as rs} (hb : lowerBody as rs r₁ = some b) :
    callsAll C b = true := by
  obtain ⟨s₂, hs₂, hf⟩ := Option.bind_eq_some_iff.mp hb
  obtain ⟨s₃, hs₃, rfl⟩ := Option.map_eq_some_iff.mp hf
  refine callsAll_dce (d := jasminDialect) C _ ?_
  unfold NFFwdLoad1.fwdLoad1
  rw [callsAll_fwdLoad1Go, callsAll_castNF]
  refine callsAll_map? ModArithLimbs.modArithLimbsJ ModArithLimbs.modArithLimbsJ_regionTypes C _
    ?_ _ hs₃
  refine callsAll_map? FieldToModArithChain.fieldToModArithJ FieldToModArithChain.regionTypes
    _ r₁ ?_ _ hs₂
  exact callsAll_of_callFree _ r₁ hr

/-- A lowered body passes `callsAll C` at every `C`. -/
theorem fieldBodyD_callsAll (C : String → List JasminTy → List JasminTy → Bool) {f : String}
    {as rs : List JasminTy} {b : NFProg jasminDialect as rs} (hb : fieldBodyD f as rs = some b) :
    callsAll C b = true := by
  obtain ⟨-, r₁, hr₁, hb⟩ := fieldBodyD_some hb
  exact lowerBody_callsAll C (raiseBody_callFree hr₁) hb

/-- A lowered body has no `call`. -/
theorem fieldBodyD_callFree {f : String} {as rs : List JasminTy} {b : NFProg jasminDialect as rs}
    (hb : fieldBodyD f as rs = some b) : b.callFree = true :=
  callFree_of_callsAll_false b (fieldBodyD_callsAll _ hb)

/-- A lowered body of a body without exit-flag loops has none. -/
theorem lowerBody_whileFree {as rs : List JasminTy}
    {r₁ : NFProg jasField (as.map Sum.inl) (rs.map Sum.inl)} (hr : r₁.whileFree = true)
    {b : NFProg jasminDialect as rs} (hb : lowerBody as rs r₁ = some b) : b.whileFree = true := by
  obtain ⟨s₂, hs₂, hf⟩ := Option.bind_eq_some_iff.mp hb
  obtain ⟨s₃, hs₃, rfl⟩ := Option.map_eq_some_iff.mp hf
  refine whileFree_dce (d := jasminDialect) _ ?_
  unfold NFFwdLoad1.fwdLoad1
  rw [whileFree_fwdLoad1Go, whileFree_castNF]
  refine whileFree_map? ModArithLimbs.modArithLimbsJ ModArithLimbs.modArithLimbsJ_regionTypes
    _ ?_ _ hs₃
  exact whileFree_map? FieldToModArithChain.fieldToModArithJ FieldToModArithChain.regionTypes
    r₁ hr _ hs₂

/-- A lowered body has no exit-flag loop. -/
theorem fieldBodyD_whileFree {f : String} {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (hb : fieldBodyD f as rs = some b) : b.whileFree = true := by
  obtain ⟨-, r₁, hr₁, hb⟩ := fieldBodyD_some hb
  exact lowerBody_whileFree (raiseBody_whileFree hr₁) hb

/-- **The lowering of a body without `call` keeps its runs**: a run of the body at
    `liftEnv E` from an injected valuation to an injected result gives a run of the lowered
    body at `E`. -/
theorem lowerBody_denoteAt (E : CallEnv jasminDialect) (fuel : Nat) {as rs : List JasminTy}
    {r₁ : NFProg jasField (as.map Sum.inl) (rs.map Sum.inl)} (hr : r₁.callFree = true)
    {b : NFProg jasminDialect as rs} (hb : lowerBody as rs r₁ = some b)
    {x : Valuation (d := jasminDialect) as} {y : Valuation (d := jasminDialect) rs}
    (e₁ : r₁.denoteAt (FieldRaise.liftEnv E) fuel (FieldRaise.liftV x) =
      some (FieldRaise.liftV y)) :
    b.denoteAt E fuel x = some y := by
  obtain ⟨r₂, h₂, hf⟩ := Option.bind_eq_some_iff.mp hb
  obtain ⟨r₃, h₃, rfl⟩ := Option.map_eq_some_iff.mp hf
  have c₁ := callsAll_of_callFree inlCallB r₁ hr
  have e₂ := NFProg.map?_refinesAtM FieldToModArithChain.fieldToModArithJ
    (fun x => FieldToModArithChain.transTy x) (fun V => FieldToModArithChain.mapVal V)
    FieldToModArithChain.regionTypes (fun _ => True)
    FieldToModArithChain.fieldToModArith_varTransports
    (fun e _ blk hb V x hx => FieldToModArithChain.block_fwd e blk hb V x hx)
    FieldToModArithChain.fieldToModArith_mapValExtends FieldToModArithChain.regionTransports
    (FieldRaise.liftEnv E) (FieldToModArithChain.liftEnvM E) fuel r₁
    (NFProg.covered_of_forall _ (fun _ => trivial) r₁)
    ((liftEnv_transports E).mono fun _ _ _ hc => calls_of_callsAll _ r₁ c₁ hc)
    _ _ _ (NFProg.renRel_id _) r₂ h₂ _ e₁
  have c₂ := fieldToModArithStep_callsAll c₁ h₂
  have e₃ := NFProg.map?_refinesAtM ModArithLimbs.modArithLimbsJ
    (fun x => ModArithLimbs.transTy x) (fun V => ModArithLimbs.mapVal V)
    ModArithLimbs.modArithLimbsJ_regionTypes (fun _ => True)
    ModArithLimbs.modArithLimbsJ_varTransports
    (fun e _ blk hb V x hx => ModArithLimbs.modArithLimbsJ_block_fwd e blk hb V x hx)
    ModArithLimbs.modArithLimbsJ_mapValExtends ModArithLimbs.modArithLimbsJ_regionTransports
    (FieldToModArithChain.liftEnvM E) E fuel r₂
    (NFProg.covered_of_forall _ (fun _ => trivial) r₂)
    ((liftEnvM_transports E).mono fun _ _ _ hc => calls_of_callsAll _ r₂ c₂ hc)
    _ _ _ (NFProg.renRel_id _) r₃ h₃ _ e₂
  have e₄ := denoteAt_castNF E fuel (ctx3_eq as) (ctx3_eq rs) r₃ (val3_cast x) (val3_cast y) e₃
  rw [← NFFwdLoad1.denoteAt_fwdLoad1 E fuel _ x] at e₄
  exact denoteAt_dce E fuel _ e₄

/-- **The library of the lowered bodies is sound** at `fieldEnv E`, at every fuel: the raised
    body runs as the callee at `liftEnv (fieldEnv E)` (`FieldRaise.raiseLib_sound`), and the
    lowering keeps the run (`lowerBody_denoteAt`). -/
theorem fieldLibD_sound (E : CallEnv jasminDialect) (fuel : Nat) :
    @InlineLib.Sound jasminDialect _ _ _ _ _ ⟨fieldEnv E⟩ fieldLibD fuel := by
  refine @InlineLib.Sound.mk jasminDialect _ _ _ _ _ ⟨fieldEnv E⟩ fieldLibD fuel
    (fun o b hb => by cases hb) ?_
  intro f as rs b hb x y hy
  change fieldBodyD f as rs = some b at hb
  change (fieldEnv E).call f as rs x = some y at hy
  obtain ⟨-, r₁, hr₁, hb⟩ := fieldBodyD_some hb
  have h1 := @InlineLib.Sound.call jasField _ _ _ _ _ ⟨FieldRaise.liftEnv (fieldEnv E)⟩
    FieldRaise.raiseLib fuel (FieldRaise.raiseLib_sound E fuel) f _ _ r₁ hr₁ (FieldRaise.liftV x)
    (FieldRaise.liftV y)
    ((FieldRaise.liftCall_liftV (fieldEnv E) f as rs x).trans (congrArg (Option.map _) hy))
  exact lowerBody_denoteAt (fieldEnv E) fuel (raiseBody_callFree hr₁) hb h1

/-- **The lowering of a body without `call` keeps two leakage runs**, with equal events from
    equal events. -/
theorem lowerBody_leakRunC {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E' : CallEnv jasminDialect) (fuel : Nat) {as rs : List JasminTy}
    {r₁ : NFProg jasField (as.map Sum.inl) (rs.map Sum.inl)} (hr : r₁.callFree = true)
    {b : NFProg jasminDialect as rs} (hb : lowerBody as rs r₁ = some b)
    {x₁ x₂ : Valuation (d := jasminDialect) as}
    {y₁ y₂ : Valuation (d := jasminDialect) rs} {a₁ a₂ : List CTLeak}
    (ea₁ : Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel Pj)) (FieldRaise.liftEnv E')
      fuel r₁ (FieldRaise.liftV x₁) = some (FieldRaise.liftV y₁, a₁))
    (ea₂ : Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel Pj)) (FieldRaise.liftEnv E')
      fuel r₁ (FieldRaise.liftV x₂) = some (FieldRaise.liftV y₂, a₂)) :
    ∃ l₁ l₂, Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) E' fuel b x₁ = some (y₁, l₁) ∧
      Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) E' fuel b x₂ = some (y₂, l₂) ∧
      (a₁ = a₂ → l₁ = l₂) := by
  obtain ⟨s₂, hs₂, hf⟩ := Option.bind_eq_some_iff.mp hb
  obtain ⟨s₃, hs₃, rfl⟩ := Option.map_eq_some_iff.mp hf
  have c₁ := callsAll_of_callFree inlCallB r₁ hr
  obtain ⟨b₁, b₂, eb₁, eb₂, hb⟩ := FieldToModArithChain.fieldToModArithStep_leakRunC
    (jLeakModel Pj) quietModLeak (fun _ => rfl) (FieldRaise.liftEnv E')
    (FieldToModArithChain.liftEnvM E') fuel hs₂
    ((liftEnv_transports E').mono fun _ _ _ hc => calls_of_callsAll _ r₁ c₁ hc) ea₁ ea₂
  have c₂ := fieldToModArithStep_callsAll c₁ hs₂
  obtain ⟨d₁, d₂, ed₁, ed₂, hd⟩ := ModArithLimbs.modArithLimbsStep_leakRunC hV quietModLeak
    (FieldToModArithChain.liftEnvM E') E' fuel
    ((liftEnvM_transports E').mono fun _ _ _ hc => calls_of_callsAll _ s₂ c₂ hc) hs₃ eb₁ eb₂
  have ec₁ := leakRunMC_castNF (jLeakModel Pj) E' fuel (ctx3_eq as) (ctx3_eq rs) s₃
    (val3_cast x₁) (val3_cast y₁) ed₁
  have ec₂ := leakRunMC_castNF (jLeakModel Pj) E' fuel (ctx3_eq as) (ctx3_eq rs) s₃
    (val3_cast x₂) (val3_cast y₂) ed₂
  obtain ⟨f₁, ef₁, kf₁⟩ := NFFwdLoad1.leakRunMC_fwdLoad1 (jLeakModel Pj) E' fuel _ x₁ _ ec₁
  obtain ⟨f₂, ef₂, kf₂⟩ := NFFwdLoad1.leakRunMC_fwdLoad1 (jLeakModel Pj) E' fuel _ x₂ _ ec₂
  obtain ⟨g₁, eg₁, kg₁⟩ := Dialects.NFLeak.NFProg.leakRunMC_dce (jLeakModel Pj) E' E' fuel _
    (fun _ _ _ _ _ => rfl) x₁ _ ef₁
  obtain ⟨g₂, eg₂, kg₂⟩ := Dialects.NFLeak.NFProg.leakRunMC_dce (jLeakModel Pj) E' E' fuel _
    (fun _ _ _ _ _ => rfl) x₂ _ ef₂
  refine ⟨g₁, g₂, eg₁, eg₂, fun he => ?_⟩
  have hd' : d₁ = d₂ := hd (hb he)
  subst hd'
  have hf' : f₁ = f₂ := (Prod.mk.inj ((kf₁ []).symm.trans (kf₂ []))).1
  subst hf'
  exact (Prod.mk.inj ((kg₁ []).symm.trans (kg₂ []))).1

/-- **The library of the lowered bodies is sound for the leakage run** at `fieldEnv E'`: a
    lowered body runs as the callee, and its events do not depend on the arguments, since
    the raised body emits the events `raiseEv` at every argument vector
    (`FieldRaise.raiseLib_leakSound`) and the lowering maps equal events to equal events
    (`lowerBody_leakRunC`). -/
theorem fieldLibD_leakSound {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E' : CallEnv jasminDialect) (fuel : Nat) :
    ∃ ev, fieldLibD.LeakSound (jLeakModel Pj) (fieldEnv E') fuel ev := by
  classical
  have key : ∀ f as rs (b : NFProg jasminDialect as rs), fieldBodyD f as rs = some b →
      ∀ x₁ y₁ x₂ y₂, (fieldEnv E').call f as rs x₁ = some y₁ →
        (fieldEnv E').call f as rs x₂ = some y₂ →
        ∃ l₁ l₂, Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) (fieldEnv E') fuel b x₁ =
            some (y₁, l₁) ∧
          Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) (fieldEnv E') fuel b x₂ =
            some (y₂, l₂) ∧ l₁ = l₂ := by
    intro f as rs b hb x₁ y₁ x₂ y₂ h₁ h₂
    obtain ⟨-, r₁, hr₁, hb⟩ := fieldBodyD_some hb
    have ea := fun (x : Valuation (d := jasminDialect) as) (y : Valuation (d := jasminDialect) rs)
        (hy : (fieldEnv E').call f as rs x = some y) =>
      (FieldRaise.raiseLib_leakSound hV E' fuel).call f _ _ r₁ hr₁ (FieldRaise.liftV x)
        (FieldRaise.liftV y)
        ((FieldRaise.liftCall_liftV (fieldEnv E') f as rs x).trans (congrArg (Option.map _) hy))
    obtain ⟨l₁, l₂, e₁, e₂, hl⟩ := lowerBody_leakRunC hV (fieldEnv E') fuel
      (raiseBody_callFree hr₁) hb (ea x₁ y₁ h₁) (ea x₂ y₂ h₂)
    exact ⟨l₁, l₂, e₁, e₂, hl rfl⟩
  refine ⟨fun f as rs => if h : ∃ l : List CTLeak, ∀ b, fieldBodyD f as rs = some b →
      ∀ x y, (fieldEnv E').call f as rs x = some y →
        Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) (fieldEnv E') fuel b x = some (y, l)
    then h.choose else [], ⟨fun _ _ hb => (by cases hb), ?_⟩⟩
  intro f as rs b hb x y hy
  change fieldBodyD f as rs = some b at hb
  obtain ⟨l, -, e, -, -⟩ := key f as rs b hb x y x y hy hy
  have hex : ∃ l : List CTLeak, ∀ b, fieldBodyD f as rs = some b →
      ∀ x y, (fieldEnv E').call f as rs x = some y →
        Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) (fieldEnv E') fuel b x =
          some (y, l) := by
    refine ⟨l, fun b' hb' x' y' hy' => ?_⟩
    obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
    obtain ⟨l₁, l₂, e₁, e₂, rfl⟩ := key f as rs b' hb x y x' y' hy hy'
    rw [e] at e₁
    cases e₁
    exact e₂
  rw [dite_eq_left hex]
  exact hex.choose_spec b hb x y hy

/-- **The lowering of a raised body is defined** when the body has accepted operations. -/
theorem lowerBody_isSome {as rs : List JasminTy}
    {r₁ : NFProg jasField (as.map Sum.inl) (rs.map Sum.inl)} (a₁ : r₁.allOps opOkF = true) :
    (lowerBody as rs r₁).isSome = true := by
  obtain ⟨r₂, h₂⟩ : ∃ r₂, (FieldToModArithChain.fieldToModArithStep _ _).run r₁ = some r₂ :=
    Option.isSome_iff_exists.mp
    ((NFProg.isSome_map?_iff FieldToModArithChain.fieldToModArithJ
      FieldToModArithChain.regionTypes r₁ (fun v => v)).2
      (NFProg.Covered.mono (fun e he => opOkF_lower_isSome e he)
        (JasminImageOps.covered_of_allOps opOkF r₁ a₁)))
  have a₂ := JasminImageOps.allOps_map? FieldToModArithChain.fieldToModArithJ
    FieldToModArithChain.regionTypes opOkM r₁
    (NFProg.Covered.mono (fun e he blk hb => opOkF_block e he blk hb)
      (JasminImageOps.covered_of_allOps opOkF r₁ a₁)) _ r₂ h₂
  obtain ⟨r₃, h₃⟩ : ∃ r₃, (ModArithLimbs.modArithLimbsStep _ _).run r₂ = some r₃ :=
    Option.isSome_iff_exists.mp
    ((NFProg.isSome_map?_iff ModArithLimbs.modArithLimbsJ
      ModArithLimbs.modArithLimbsJ_regionTypes r₂ (fun v => v)).2
      (NFProg.Covered.mono (fun e he => opOkM_block e he)
        (JasminImageOps.covered_of_allOps opOkM r₂ a₂)))
  rw [lowerBody, h₂, Option.bind_some, h₃]
  rfl

/-- **A tagged head with a template body has a lowered body.** -/
theorem fieldBodyD_isSome {f : String} {as rs : List JasminTy}
    (h : (fieldBody f as rs).isSome = true) : (fieldBodyD f as rs).isSome = true := by
  have ht := fieldTag?_isSome_of_fieldBody h
  have hM : montLowB f = true := montLowB_of_fieldCallB (as := as) (rs := rs)
    (by simp [fieldCallB, h])
  rw [← FieldRaise.raiseBody_isSome f as rs ht] at h
  obtain ⟨r₁, hr₁⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (lowerBody_isSome (raiseBody_allOps hM hr₁))
  rw [fieldBodyD, ite_eq_left hM, hr₁, Option.bind_some, hb]
  rfl

/-- **A narrow Montgomery head at its signature has a lowered body.** -/
theorem fieldBodyD_isSome_mont {f : String} {as rs : List JasminTy}
    (h : ChainTotal.fieldCallMontB f as rs = true) : (fieldBodyD f as rs).isSome = true := by
  have hM : montLowB f = true := montLowB_of_fieldCallB (as := as) (rs := rs)
    (by simp [fieldCallB, h])
  obtain ⟨r₁, hr₁⟩ := Option.isSome_iff_exists.mp (raiseBody_isSome_mont h)
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (lowerBody_isSome (raiseBody_allOps hM hr₁))
  rw [fieldBodyD, ite_eq_left hM, hr₁, Option.bind_some, hb]
  rfl

/-- Inlining the lowered bodies is defined, and calls no field head, on `fieldDomB`. -/
theorem inline?_fieldLibD_of_dom {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (s : NFProg jasminDialect Γ ts) (hs : callsAll fieldCallB s = true) :
    ∃ r, NFProg.inline? fieldLibD s = some r ∧ fieldFree r = true := by
  induction s with
  | ret vs => exact ⟨_, rfl, rfl⟩
  | var e k ih =>
      obtain ⟨k', hk, hf⟩ := ih hs
      obtain ⟨o, rfl, args⟩ := e
      refine ⟨.var ⟨o, rfl, args⟩ k', ?_, hf⟩
      simp only [NFProg.inline?, hk, Option.bind_some, NFProg.inlineVar,
        show fieldLibD.op o = none from rfl]
  | forLoop count inits body k ihb ihk =>
      simp only [callsAll, Bool.and_eq_true] at hs
      obtain ⟨b', hb, hfb⟩ := ihb hs.1
      obtain ⟨k', hk, hfk⟩ := ihk hs.2
      exact ⟨.forLoop count inits b' k', by
        simp only [NFProg.inline?, hb, hk, Option.bind_some, Option.map_some],
        by simp only [fieldFree, hfb, hfk, Bool.and_self]⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [callsAll, Bool.and_eq_true] at hs
      obtain ⟨t', ht, hft⟩ := iht hs.1.1
      obtain ⟨e', he, hfe⟩ := ihe hs.1.2
      obtain ⟨k', hk, hfk⟩ := ihk hs.2
      exact ⟨.ifThenElse cond t' e' k', by
        simp only [NFProg.inline?, ht, he, hk, Option.bind_some, Option.map_some],
        by simp only [fieldFree, hft, hfe, hfk, Bool.and_self]⟩
  | whileLoop inits body k ihb ihk =>
      simp only [callsAll, Bool.and_eq_true] at hs
      obtain ⟨b', hb, hfb⟩ := ihb hs.1
      obtain ⟨k', hk, hfk⟩ := ihk hs.2
      exact ⟨.whileLoop inits b' k', by
        simp only [NFProg.inline?, hb, hk, Option.bind_some, Option.map_some],
        by simp only [fieldFree, hfb, hfk, Bool.and_self]⟩
  | call f args k ih =>
      simp only [callsAll, fieldCallB, Bool.and_eq_true, Bool.or_eq_true] at hs
      obtain ⟨k', hk, hf⟩ := ih hs.2
      simp only [NFProg.inline?, hk, Option.bind_some]
      split
      · rename_i b hb
        obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
          (NFProg.seq?_isSome_of_total b k' (PRen.total_ofArgs args) PRen.total_id)
        exact ⟨q, hq, fieldFree_seq? b k' hq
          (fieldFree_of_callFree b (fieldBodyD_callFree hb)) hf⟩
      · rename_i hb
        have hn : (!fieldHeadB f) = true := by
          rcases hs.1 with (h | h) | h
          · exact h
          · exact absurd (fieldBodyD_isSome h) (by simp [show fieldBodyD f _ _ = none from hb])
          · exact absurd (fieldBodyD_isSome_mont h)
              (by simp [show fieldBodyD f _ _ = none from hb])
        exact ⟨_, rfl, by simp only [fieldFree, hn, hf, Bool.and_self]⟩

/-! ## 7. The step -/

/-- **The field dialect step.** A program that calls no field head is returned unchanged.
    Otherwise each call of a tagged head is replaced by its lowered body (`fieldBodyD`: the
    raised body lowered to `mod_arith` and to the limb templates in `jasminDialect`, with its
    loads from one-word arrays forwarded and its dead bindings removed) in one round of
    `NFProg.inline?` at the library `fieldLibD`, refused when the result keeps a `call` of a
    field head. -/
def fieldDialectStep (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    Step (NFProg jasminDialect Γ ts) (NFProg jasminDialect Γ ts) :=
  ⟨"fieldDialect", fun p => if fieldFree p then some p else
    (NFProg.inline? fieldLibD p).bind fun q => if fieldFree q then some q else none⟩

/-- **The certificate of the field dialect step**, from the semantics at `fieldEnv E` to the
    semantics at `E`, with equal inputs and outputs. -/
def fieldDialectCert (E : CallEnv jasminDialect) (fuel : Nat) (Γ : Ctxt jasminDialect)
    (ts : List JasminTy) :
    StepCert (fieldDialectStep Γ ts).run (nfSemE (fieldEnv E) fuel Γ ts) (nfSemE E fuel Γ ts) where
  relIn V W := W = V
  relOut o o' := o' = o
  sound := by
    rintro p q W V o hf rfl hd
    refine ⟨o, ?_, rfl⟩
    change p.denoteAt (fieldEnv E) fuel V = some o at hd
    change q.denoteAt E fuel V = some o
    change (if fieldFree p then some p else _) = some q at hf
    split at hf
    · rename_i hff
      cases hf
      rw [NFProg.denoteAt_congr p E (fieldEnv E) (fun f as rs x hc =>
        (fieldEnv_of_none E (fieldHeadB_of_fieldFree p hff hc) as rs x).symm) fuel V]
      exact hd
    · obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hf
      split at hif
      · rename_i hff
        cases hif
        rw [NFProg.denoteAt_congr q E (fieldEnv E) (fun f as rs x hc =>
          (fieldEnv_of_none E (fieldHeadB_of_fieldFree q hff hc) as rs x).symm) fuel V]
        exact NFProg.denoteAt_inline? (fieldEnv E) (fieldLibD_sound E fuel) p hq0 hd
      · cases hif

/-- **The field dialect step is complete on `fieldDomB`.** -/
theorem fieldDialectStep_completeOn (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    (fieldDialectStep Γ ts).CompleteOn (fun p => fieldDomB p = true) (fun _ => True) := by
  intro p hp
  by_cases hff : fieldFree p = true
  · refine ⟨p, ?_, trivial⟩
    change (if fieldFree p then some p else _) = some p
    rw [ite_eq_left hff]
  · obtain ⟨q, hq, hf⟩ := inline?_fieldLibD_of_dom p (by rw [← fieldDomB_eq_callsAll]; exact hp)
    refine ⟨q, ?_, trivial⟩
    change (if fieldFree p then some p else _) = _
    rw [ite_eq_right hff, hq, Option.bind_some, ite_eq_left hf]

/-- **The field dialect step returns a program without `call` unchanged.** -/
theorem fieldDialectStep_of_callFree {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : p.callFree = true) :
    (fieldDialectStep Γ ts).run p = some p := by
  change (if fieldFree p then some p else _) = some p
  rw [ite_eq_left (fieldFree_of_callFree p hp)]

/-! ## 8. The calls of the output of the step -/

/-- **The field dialect step keeps `callsAll C`.** Inlining keeps it, since the lowered
    bodies call nothing (`fieldBodyD_callsAll`). -/
theorem fieldDialectStep_callsAll (C : String → List JasminTy → List JasminTy → Bool)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p q : NFProg jasminDialect Γ ts}
    (hp : callsAll C p = true) (hf : (fieldDialectStep Γ ts).run p = some q) :
    callsAll C q = true := by
  change (if fieldFree p then some p else _) = some q at hf
  split at hf
  · cases hf
    exact hp
  · obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hf
    split at hif
    · cases hif
      exact callsAll_inline? C fieldLibD (fun _ => rfl)
        (fun _ _ _ b hb => fieldBodyD_callsAll C hb) p hp hq0
    · cases hif

/-- **The field dialect step keeps the absence of exit-flag loops.** Inlining keeps it, since
    the lowered bodies have none (`fieldBodyD_whileFree`). -/
theorem fieldDialectStep_whileFree {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (hp : p.whileFree = true)
    (hf : (fieldDialectStep Γ ts).run p = some q) : q.whileFree = true := by
  change (if fieldFree p then some p else _) = some q at hf
  split at hf
  · cases hf
    exact hp
  · obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hf
    split at hif
    · cases hif
      exact whileFree_inline? fieldLibD (fun _ => rfl)
        (fun _ _ _ b hb => fieldBodyD_whileFree hb) p hp hq0
    · cases hif

/-! ## 9. The leakage of the step -/

/-- **Two leakage runs before the field dialect step give two runs of its result at the
    remaining calls, with equal events from equal events.** At leakage parameters of
    `jasminDialect` with no variable-time operation, a program that calls no field head runs
    at `E'` as at `fieldEnv E'`. Otherwise the library of the lowered bodies is sound for the
    leakage run at `fieldEnv E'` with a fixed list of events per head (`fieldLibD_leakSound`),
    so the inlined program runs from each valuation to the same results, with equal events
    when the source events are equal (`NFProg.leakRunMC_inline?_prefix`); the result calls no
    field head, at which alone `fieldEnv E'` and `E'` differ. -/
theorem fieldDialectStep_leakRunC {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E' : CallEnv jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (hf : (fieldDialectStep Γ ts).run p = some q)
    {V₁ V₂ : Valuation Γ} {r₁ r₂ : Valuation (d := jasminDialect) ts × List CTLeak}
    (h₁ : Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) (fieldEnv E') fuel p V₁ = some r₁)
    (h₂ : Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) (fieldEnv E') fuel p V₂ = some r₂) :
    ∃ l₁ l₂, Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) E' fuel q V₁ = some (r₁.1, l₁) ∧
      Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) E' fuel q V₂ = some (r₂.1, l₂) ∧
      (r₁.2 = r₂.2 → l₁ = l₂) := by
  change (if fieldFree p then some p else _) = some q at hf
  split at hf
  · rename_i hff
    cases hf
    have hc := fun V => Dialects.NFLeak.NFProg.leakRunMC_congr (jLeakModel Pj) p (fieldEnv E') E'
      (fun f as rs x hc => fieldEnv_of_none E' (fieldHeadB_of_fieldFree p hff hc) as rs x)
      fuel V
    rw [hc] at h₁ h₂
    exact ⟨r₁.2, r₂.2, h₁, h₂, _root_.id⟩
  · obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hf
    split at hif
    · rename_i hff
      cases hif
      obtain ⟨ev, hL⟩ := fieldLibD_leakSound hV E' fuel
      obtain ⟨l₁, l₂, e₁, e₂, hl⟩ := NFProg.leakRunMC_inline?_prefix (jLeakModel Pj)
        (fieldEnv E') hL p hq0 h₁ h₂
      have hc := fun V => Dialects.NFLeak.NFProg.leakRunMC_congr (jLeakModel Pj) q
        (fieldEnv E') E' (fun f as rs x hc =>
          fieldEnv_of_none E' (fieldHeadB_of_fieldFree q hff hc) as rs x) fuel V
      exact ⟨l₁, l₂, (hc _).symm.trans e₁, (hc _).symm.trans e₂,
        fun he => (hl [] [] (by simp only [he])).1⟩
    · cases hif

/-! ## 10. The operations of the output of the step -/

section Ops

open CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps (bindPosB widthPos covered_of_allOps)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (coveredCom_rename
  coveredCom_spliceCom)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)

/-- The Jasmin operations of `opMemB` whose result has positive width. -/
local notation "opMemPos" => fun op => opMemB op && bindPosB op

/-- A block whose embedding has its operations in `Q` has its operations in `Q`. -/
theorem coveredCom_ofCom {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] (Q : d.Op → Bool) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t)
    (hc : (NFProg.ofCom c).allOps Q = true) : CoveredCom (fun e => Q e.op = true) c := by
  induction c with
  | ret v => trivial
  | var e k ih =>
      simp only [NFProg.ofCom, NFProg.allOps, Bool.and_eq_true] at hc
      exact ⟨hc.1, ih hc.2⟩

/-- Dead-binding elimination keeps `allOps Q`. -/
theorem allOps_dce {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
    [HasBoolBit d] (Q : d.Op → Bool) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : p.allOps Q = true) : (NFProg.dce p).allOps Q = true := by
  induction p with
  | ret => rfl
  | var e k ih =>
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [NFProg.dce]
      split
      · rename_i k' hk'
        rw [FieldInlineOps.allOps_rename? Q _ _ hk']
        exact ih hp.2
      · simp only [NFProg.allOps, hp.1, ih hp.2, Bool.and_self]
  | forLoop _ _ _ _ ihb ihk =>
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [NFProg.dce, NFProg.allOps, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [NFProg.dce, NFProg.allOps, iht hp.1.1, ihe hp.1.2, ihk hp.2, Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [NFProg.dce, NFProg.allOps, ihb hp.1, ihk hp.2, Bool.and_self]
  | call _ _ _ ih => exact ih hp

/-- The forwarding of loads keeps `allOps Q`. -/
theorem allOps_fwdLoad1Go (Q : jasminDialect.Op → Bool) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : p.allOps Q = true) :
    ∀ {Δ : Ctxt jasminDialect} (K : NFFwdLoad1.StoreFacts Γ) (ren : Ctxt.Hom Γ Δ),
      (NFFwdLoad1.fwdLoad1Go p K ren).allOps Q = true := by
  induction p with
  | ret => intro Δ K ren; rfl
  | var e k ih =>
      intro Δ K ren
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [NFFwdLoad1.fwdLoad1Go]
      split
      · split
        · exact ih hp.2 _ _
        · simp only [NFProg.allOps, Bool.and_eq_true]
          exact ⟨hp.1, ih hp.2 _ _⟩
      · simp only [NFProg.allOps, Bool.and_eq_true]
        exact ⟨hp.1, ih hp.2 _ _⟩
  | forLoop _ _ _ _ ihb ihk =>
      intro Δ K ren
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [NFFwdLoad1.fwdLoad1Go, NFProg.allOps, ihb hp.1, ihk hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      intro Δ K ren
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [NFFwdLoad1.fwdLoad1Go, NFProg.allOps, iht hp.1.1, ihe hp.1.2, ihk hp.2,
        Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      intro Δ K ren
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [NFFwdLoad1.fwdLoad1Go, NFProg.allOps, ihb hp.1, ihk hp.2, Bool.and_self]
  | call _ _ _ ih =>
      intro Δ K ren
      exact ih hp _ _

/-- A carried program has the operations of the program. -/
theorem allOps_castNF (Q : jasminDialect.Op → Bool) {Γ Γ' : Ctxt jasminDialect}
    {ts ts' : List JasminTy} (hΓ : Γ = Γ') (hts : ts = ts') (q : NFProg jasminDialect Γ ts) :
    (castNF hΓ hts q).allOps Q = q.allOps Q := by
  subst hΓ hts
  rfl

/-- The accepted operations of `jasField` (`opOkF`) whose operations of `jasminDialect` are
    in `opMemB` with a result of positive width. -/
def opPosF (o : jasField.Op) : Bool :=
  opOkF o && match o with
    | .inl (.inl o) => opMemB o && bindPosB o
    | _ => true

/-- The accepted operations of `jasMod` (`opOkM`) whose operations of `jasminDialect` are in
    `opMemB` with a result of positive width. -/
def opPosM (o : jasMod.Op) : Bool :=
  opOkM o && match o with
    | .inl (.inl o) => opMemB o && bindPosB o
    | _ => true

/-- The raised body on registers at an accepted representation has its operations in
    `opPosF`. -/
theorem raiseWord_opPosF {m : _root_.Hax.FieldTag.FieldMethod} {p : Nat} {r : FieldRepr}
    (hc : CastsAt p 1) (hr : reprOkB p r = true)
    {as rs : List (JasminTy ⊕ PfTy)} {b : NFProg jasField as rs}
    (h : FieldRaise.raiseWord m p as rs r = some b) : b.allOps opPosF = true := by
  obtain ⟨T, hT, h1, h2⟩ := hc
  unfold FieldRaise.raiseWord at h
  split at h
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    cases h
    show NFProg.allOps opPosF (FieldRaise.wordBody m p r) = true
    cases m <;> simp only [FieldRaise.wordBody, FieldRaise.wordBody2, FieldRaise.wordBody1,
      FieldRaise.wordTail, NFProg.allOps, FieldRaise.zeroE, FieldRaise.storeE, FieldRaise.fromE,
      FieldRaise.toE, FieldRaise.constE, FieldRaise.loadE, FieldRaise.opE, opPosF, opOkF, hT, hr,
      Option.any_some, Option.isSome_some, h1, h2, Bool.and_self, Bool.true_and,
      Bool.and_true] <;> decide
  · cases h

/-- The raised body on arrays has its operations in `opPosF`. -/
theorem raiseArr_opPosF {m : _root_.Hax.FieldTag.FieldMethod} {p : Nat}
    (hc : CastsAt p (fieldLimbs p)) {as rs : List (JasminTy ⊕ PfTy)}
    {b : NFProg jasField as rs} (h : FieldRaise.raiseArr m p as rs = some b) :
    b.allOps opPosF = true := by
  obtain ⟨T, hT, h1, h2⟩ := hc
  unfold FieldRaise.raiseArr at h
  split at h
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    cases h
    show NFProg.allOps opPosF (FieldRaise.arrBody m p (fieldLimbs p)) = true
    cases m <;> simp only [FieldRaise.arrBody, FieldRaise.arrBody2, FieldRaise.arrBody1,
      NFProg.allOps, FieldRaise.fromE, FieldRaise.toE, FieldRaise.opE, opPosF, opOkF, reprOkB,
      hT, Option.any_some, Option.isSome_some, h1, h2, Bool.and_self]
  · cases h

/-- A raised body of a head of `montLowB` has its operations in `opPosF`. -/
theorem raiseBody_opPosF {f : String} {as rs : List (JasminTy ⊕ PfTy)}
    (hM : montLowB f = true)
    {b : NFProg jasField as rs} (h : FieldRaise.raiseBody f as rs = some b) :
    b.allOps opPosF = true := by
  unfold FieldRaise.raiseBody at h
  split at h
  · split at h
    · rename_i hn
      exact raiseWord_opPosF (castsAt_narrow hn) rfl h
    · rename_i hn hw
      exact raiseArr_opPosF (castsAt_wide hn hw) h
    · rename_i hn hw hm
      exact raiseWord_opPosF (castsAt_mont hn hw hm) rfl h
    · cases h
  · split at h
    · rename_i m p k hm
      split at h
      · rename_i hc
        have h1 : 1 < p := by simpa [montLowB, hm] using hM
        exact raiseWord_opPosF (castsAt_of_odd h1 hc.1 hc.2) (reprOkB_mont k h1 hc.1 hc.2) h
      · cases h
    · cases h

/-- **The raised program of a program of `fieldDomB` with its operations in `opMemB` at
    positive width has its operations in `opPosF`.** -/
theorem fieldRaiseStep_opPosF {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hd : fieldDomB p = true) (hp : p.allOps opMemPos = true)
    {r : NFProg jasField (Γ.map Sum.inl) (ts.map Sum.inl)}
    (hr : (FieldRaise.fieldRaiseStep Γ ts).run p = some r) : r.allOps opPosF = true := by
  obtain ⟨q, hq, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨r0, hr0, hif⟩ := Option.bind_eq_some_iff.mp hr
  split at hif
  · cases hif
    refine allOps_inline?_of_callsAll FieldRaise.raiseLib opPosF _ (fun _ _ hb => by cases hb)
      (fun _ _ _ b hM hb => raiseBody_opPosF hM hb) (FieldRaise.embed q)
      (callsAll_embed_montLowB hd hq) hr0 ?_
    rw [allOps_embed]
    refine JasminImageOps.allOps_map? FieldRaise.liftJ FieldRaise.liftJ_regionTypes _ p
      (NFProg.Covered.mono (fun e he blk hb => ?_) (covered_of_allOps _ p hp)) _ q hq
    cases hb
    exact ⟨he, trivial⟩
  · cases hif

/-- The block of an operation of `opPosF` has its operations in `opPosM`. -/
theorem opPosF_block {Γ : Ctxt jasField} {t : jasField.Ty} (e : Expr jasField Γ t)
    (he : opPosF e.op = true) (blk : Com jasMod _ _)
    (hb : FieldToModArithChain.fieldToModArithJ.lowerExprBlock? e = some blk) :
    CoveredCom (fun e' => opPosM e'.op = true) blk := by
  obtain ⟨op, rfl, args⟩ := e
  rcases op with (o | o) | o
  · cases hb
    exact ⟨he, trivial⟩
  all_goals cases o <;> (try cases ‹FieldRepr›) <;> first
    | (simp [opPosF, opOkF] at he; done)
    | (simp only [opPosF, opOkF, reprOkB, Bool.and_true, Bool.and_eq_true] at he
       simp only [FieldToModArithChain.fieldToModArithJ, FieldToModArithChain.lowerBlock?,
         FieldToModArithChain.opBlock?, FieldToModArithChain.pfBlock?,
         FieldToModArithChain.castBlock?] at hb
       (try split at hb) <;> cases hb
       exact ⟨by simp [opPosM, opOkM, he], trivial⟩)

/-- The operations of the bodies and of the cast blocks of a limb template are in `opMemB`
    with results of positive width. -/
def TemplateOps {p : Nat} (T : Algebraic.ModArithLimbTemplate p .canon) : Prop :=
  (∀ m, CoveredCom (fun e => (opMemB e.op && bindPosB e.op) = true) (T.body m)) ∧
  (∀ w n c, T.ofWords w n = some c →
    CoveredCom (fun e => (opMemB e.op && bindPosB e.op) = true) c) ∧
  (∀ w n c, T.toWords w n = some c →
    CoveredCom (fun e => (opMemB e.op && bindPosB e.op) = true) c)

/-- The bodies of a narrow representation have their operations in `opMemB` at positive
    width. -/
theorem singleBody_covered {p : Nat} {F : Algebraic.FieldWord.SingleWordField p}
    (hn : narrowFieldOf p = some F) (m : _root_.Hax.FieldTag.FieldMethod) :
    CoveredCom (fun e => (opMemB e.op && bindPosB e.op) = true)
      (Algebraic.ModArithLimbTemplate.singleBody F m) := by
  unfold narrowFieldOf at hn
  split at hn
  · rename_i n hk
    cases hn
    have h := FieldInlineOps.fieldBlockOf_allOps (FieldRouteNarrow.narrowCert_of_narrowFoldsOf hk) m
    rw [ModArithLimbs.fieldBlockOf_eq] at h
    exact coveredCom_ofCom _ _ h
  · cases hn

/-- The load block of a single-word representation has its operations in `opMemB` at
    positive width. -/
theorem singleOfWords_covered {w n : Nat} {c : Com jasminDialect [.stackArr w n] (.reg 64)}
    (hc : Algebraic.ModArithLimbTemplate.singleOfWords w n = some c) :
    CoveredCom (fun e => (opMemB e.op && bindPosB e.op) = true) c := by
  unfold Algebraic.ModArithLimbTemplate.singleOfWords at hc
  split at hc
  · cases hc
    exact ⟨rfl, rfl, trivial⟩
  · cases hc

/-- The store block of a single-word representation has its operations in `opMemB` at
    positive width. -/
theorem singleToWords_covered {w n : Nat} {c : Com jasminDialect [.reg 64] (.stackArr w n)}
    (hc : Algebraic.ModArithLimbTemplate.singleToWords w n = some c) :
    CoveredCom (fun e => (opMemB e.op && bindPosB e.op) = true) c := by
  unfold Algebraic.ModArithLimbTemplate.singleToWords at hc
  split at hc
  · cases hc
    exact ⟨rfl, rfl, trivial⟩
  · cases hc

/-- **The chosen template at `canon` has its operations in `opMemB` at positive width.** -/
theorem canonTemplateOf_ops {p : Nat} {T : Algebraic.ModArithLimbTemplate p .canon}
    (hT : ModArithLimbs.canonTemplateOf p = some T) : TemplateOps T := by
  unfold ModArithLimbs.canonTemplateOf at hT
  split at hT
  · rename_i F hn
    cases hT
    exact ⟨fun m => singleBody_covered hn m, fun _ _ _ hc => singleOfWords_covered hc,
      fun _ _ _ hc => singleToWords_covered hc⟩
  · split at hT
    · rename_i W hw
      cases hT
      refine ⟨fun m => ?_, fun w n c hc => ?_, fun w n c hc => ?_⟩
      · have h := FieldInlineOps.wideBlockOf_allOps hw m
        rw [ModArithLimbs.wideBlockOf_eq] at h
        exact coveredCom_ofCom _ _ h
      · change ModArithLimbs.arrOfWords _ w n = some c at hc
        unfold ModArithLimbs.arrOfWords at hc
        split at hc
        · rename_i h
          cases hc
          injection h with h1 h2
          subst h1 h2
          trivial
        · cases hc
      · change ModArithLimbs.arrToWords _ w n = some c at hc
        unfold ModArithLimbs.arrToWords at hc
        split at hc
        · rename_i h
          cases hc
          injection h with h1 h2
          subst h1 h2
          trivial
        · cases hc
    · split at hT
      · rename_i P hm
        cases hT
        refine ⟨fun m => ?_, fun _ _ _ hc => singleOfWords_covered hc,
          fun _ _ _ hc => singleToWords_covered hc⟩
        have h := FieldInlineOps.montWordBlockOf_allOps P m
        rw [ModArithLimbs.montWordBlockOf_eq] at h
        exact coveredCom_ofCom _ _ h
      · cases hT

/-- The body block of a method under a template with `TemplateOps` has its operations in
    `opMemB` at positive width. -/
theorem bodyBlock?_covered {Δ : Ctxt jasminDialect} {p : Nat}
    (o : Option (Algebraic.ModArithLimbTemplate p .canon)) (ho : ∀ T, o = some T → TemplateOps T)
    (m : _root_.Hax.FieldTag.FieldMethod)
    (args : HVector (fun t => Var Δ t) (Algebraic.ModArithLimbTemplate.limbSig
      (ModArithLimbs.optTy o) m)) {blk : Com jasminDialect Δ (ModArithLimbs.optTy o)}
    (hb : ModArithLimbs.bodyBlock? o m args = some blk) :
    CoveredCom (fun e => (opMemB e.op && bindPosB e.op) = true) blk := by
  cases o with
  | none => cases hb
  | some T =>
      cases hb
      exact coveredCom_rename (d := jasminDialect) (fun o => opMemB o && bindPosB o) _ _
        ((ho T rfl).1 m)

/-- The block of `fromWordsM` under a template with `TemplateOps` has its operations in
    `opMemB` at positive width. -/
theorem ofWordsBlock?_covered {Δ : Ctxt jasminDialect} {p : Nat}
    (o : Option (Algebraic.ModArithLimbTemplate p .canon)) (ho : ∀ T, o = some T → TemplateOps T)
    {w n : Nat} (a : Var Δ (.stackArr w n)) {blk : Com jasminDialect Δ (ModArithLimbs.optTy o)}
    (hb : ModArithLimbs.ofWordsBlock? o w n a = some blk) :
    CoveredCom (fun e => (opMemB e.op && bindPosB e.op) = true) blk := by
  cases o with
  | none => cases hb
  | some T =>
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
      exact coveredCom_rename (d := jasminDialect) (fun o => opMemB o && bindPosB o) _ _
        ((ho T rfl).2.1 _ _ _ hc)

/-- The block of `toWordsM` under a template with `TemplateOps` has its operations in
    `opMemB` at positive width. -/
theorem toWordsBlock?_covered {Δ : Ctxt jasminDialect} {p : Nat}
    (o : Option (Algebraic.ModArithLimbTemplate p .canon)) (ho : ∀ T, o = some T → TemplateOps T)
    {w n : Nat} (a : Var Δ (ModArithLimbs.optTy o)) {blk : Com jasminDialect Δ (.stackArr w n)}
    (hb : ModArithLimbs.toWordsBlock? o w n a = some blk) :
    CoveredCom (fun e => (opMemB e.op && bindPosB e.op) = true) blk := by
  cases o with
  | none => cases hb
  | some T =>
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
      exact coveredCom_rename (d := jasminDialect) (fun o => opMemB o && bindPosB o) _ _
        ((ho T rfl).2.2 _ _ _ hc)

/-- The stores of a literal array have their operations in `opMemB` at positive width. -/
theorem fillArr_covered (n N : Nat) : ∀ (m : Nat) {Γ : Ctxt jasminDialect}
    (a : Var Γ (.stackArr 64 n)),
    CoveredCom (fun e => (opMemB e.op && bindPosB e.op) = true)
      (Algebraic.ModArithLimbTemplate.fillArr 64 n N m a)
  | 0, _, _ => trivial
  | m + 1, _, _ => ⟨rfl, rfl, fillArr_covered n N m _⟩

/-- The block of `montMul p c` under a template with `TemplateOps` has its operations in
    `opMemB` at positive width. -/
theorem montBlock?_covered {Δ : Ctxt jasminDialect} {p : Nat}
    (o : Option (Algebraic.ModArithLimbTemplate p .canon)) (ho : ∀ T, o = some T → TemplateOps T)
    (c : ZMod p) (a b : Var Δ (ModArithLimbs.optTy o))
    {blk : Com jasminDialect Δ (ModArithLimbs.optTy o)}
    (hb : ModArithLimbs.montBlock? o c a b = some blk) :
    CoveredCom (fun e => (opMemB e.op && bindPosB e.op) = true) blk := by
  cases o with
  | none => cases hb
  | some T =>
      simp only [ModArithLimbs.montBlock?] at hb
      split at hb
      · rename_i h
        cases hb
        have hT := ho T rfl
        unfold Algebraic.ModArithLimbTemplate.ofCanonMontMul
        refine coveredCom_spliceCom (d := jasminDialect) (fun o => opMemB o && bindPosB o) _ _
          (coveredCom_rename (d := jasminDialect) (fun o => opMemB o && bindPosB o) _ _
            (hT.1 .mul)) ?_
        refine coveredCom_spliceCom (d := jasminDialect) (fun o => opMemB o && bindPosB o) _ _
          ⟨rfl, fillArr_covered _ _ _ _⟩ ?_
        refine coveredCom_spliceCom (d := jasminDialect) (fun o => opMemB o && bindPosB o) _ _
          (coveredCom_rename (d := jasminDialect) (fun o => opMemB o && bindPosB o) _ _
            (hT.2.1 _ _ _ (Option.some_get h.1).symm)) ?_
        exact coveredCom_rename (d := jasminDialect) (fun o => opMemB o && bindPosB o) _ _
          (hT.1 .mul)
      · cases hb

/-- The block of an operation of `opPosM` has its operations in `opMemB` at positive
    width. -/
theorem opPosM_block {Γ : Ctxt jasMod} {t : jasMod.Ty} (e : Expr jasMod Γ t)
    (he : opPosM e.op = true) (blk : Com jasminDialect _ _)
    (hb : ModArithLimbs.modArithLimbsJ.lowerExprBlock? e = some blk) :
    CoveredCom (fun e' => (opMemB e'.op && bindPosB e'.op) = true) blk := by
  obtain ⟨op, rfl, args⟩ := e
  have ho : ∀ q T, ModArithLimbs.canonTemplateOf q = some T → TemplateOps T :=
    fun _ _ h => canonTemplateOf_ops h
  rcases op with (o | o) | o
  · cases hb
    exact ⟨he, trivial⟩
  · cases o
    all_goals first
      | (simp only [ModArithLimbs.modArithLimbsJ, ModArithLimbs.limbLowerBlock?,
          ModArithLimbs.limbOpBlock?, ModArithLimbs.modBlock?] at hb
         split at hb <;> exact bodyBlock?_covered _ (ho _) _ _ hb)
      | exact bodyBlock?_covered _ (ho _) _ _ hb
      | exact montBlock?_covered _ (ho _) _ _ _ hb
      | (cases hb; trivial)
      | cases hb
  · cases o
    · exact ofWordsBlock?_covered _ (ho _) _ hb
    · exact toWordsBlock?_covered _ (ho _) _ hb

/-- **A lowered body has its operations in `opMemB` at positive width.** The raised body has
    its operations in `opPosF` (it binds word operations of `opMemB` and casts with template
    blocks), the lowering to `jasMod` takes them to `opPosM`, the lowering to the limb
    templates takes them to `opMemB` at positive width (`canonTemplateOf_ops`), and the cast,
    `fwdLoad1` and `dce` keep that. -/
theorem fieldBodyD_allOps {f : String} {as rs : List JasminTy}
    {b : NFProg jasminDialect as rs} (hb : fieldBodyD f as rs = some b) :
    b.allOps opMemPos = true := by
  obtain ⟨hM, s₁, hs₁, hb⟩ := fieldBodyD_some hb
  obtain ⟨s₂, hs₂, hf⟩ := Option.bind_eq_some_iff.mp hb
  obtain ⟨s₃, hs₃, rfl⟩ := Option.map_eq_some_iff.mp hf
  have a₁ := raiseBody_opPosF hM hs₁
  have a₂ := JasminImageOps.allOps_map? FieldToModArithChain.fieldToModArithJ
    FieldToModArithChain.regionTypes opPosM s₁
    (NFProg.Covered.mono (fun e he blk hb => opPosF_block e he blk hb)
      (covered_of_allOps opPosF s₁ a₁)) _ s₂ hs₂
  have a₃ := JasminImageOps.allOps_map? ModArithLimbs.modArithLimbsJ
    ModArithLimbs.modArithLimbsJ_regionTypes opMemPos s₂
    (NFProg.Covered.mono (fun e he blk hb => opPosM_block e he blk hb)
      (covered_of_allOps opPosM s₂ a₂)) _ s₃ hs₃
  refine allOps_dce _ _ ?_
  unfold NFFwdLoad1.fwdLoad1
  refine allOps_fwdLoad1Go _ _ ?_ _ _
  rw [allOps_castNF]
  exact a₃

/-- **`fieldDialectStep_allOps`: the field dialect step keeps
    `allOps (fun op => opMemB op && bindPosB op)`.** Inlining keeps it, since every lowered
    body has its operations there (`fieldBodyD_allOps`). -/
theorem fieldDialectStep_allOps {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts} (hp : p.allOps opMemPos = true)
    (hf : (fieldDialectStep Γ ts).run p = some q) : q.allOps opMemPos = true := by
  change (if fieldFree p then some p else _) = some q at hf
  split at hf
  · cases hf
    exact hp
  · obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hf
    split at hif
    · cases hif
      exact FieldInlineOps.allOps_inline? fieldLibD opMemPos (fun _ _ hb => by cases hb)
        (fun _ _ _ b hb => fieldBodyD_allOps hb) p hq0 hp
    · cases hif

end Ops

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDialectStep
