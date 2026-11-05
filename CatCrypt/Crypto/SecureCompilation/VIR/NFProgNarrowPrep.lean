/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgWidenExport
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMaskElimFast
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFDceLeak
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFMapLeak

/-!
# The narrow-word stages of the region back half

`narrowPrep p` is the widening `widenJ` of the narrow words of a structured Jasmin program
`p`, followed by the elimination of redundant masks `maskElim` and dead-binding elimination
`NFProg.dce`. Its result is a program over the context `Γ.map wideTy` with results
`ts.map wideTy`, in which every word is held in a 64-bit register or 64-bit array slot, zero
extended (`transTy`).

The stages keep the meaning of the program along the transport `mapVal`: a run of `p` to `v`
at `V` is a run of the result to the transported `v` at `mapVal V` (`narrowPrep_denote`). They
keep the gate of the region back half: a program that passes `regionExportableB` has a result,
which passes `regionExportableB` (`narrowPrep_of_exportable`). They keep constant time, at
leakage parameters with no variable-time operation: two runs of `p` with equal events give two
runs of the result, at the transported valuations, with equal events (`narrowPrep_ctRel`). The
leakage transformer of `widenJ` is the identity (`widenJ_leakRun`), and so is that of
`maskElim`, which removes only quiet bindings (`leakRun_maskElim`).

The compiled code runs the stages in time linear in the program, up to the sizes of the live
and tainted sets: `NFProg.dce` runs as `NFProg.dceLive` (one liveness pass,
`NFProg.dce_eq_dceLive`), `maskElim` as `maskElimFast` (each mask decided on the uses of its
value, `maskElim_eq_maskElimFast`) and `mapVar` as `mapVarFast` (`mapVar_eq_mapVarFast`), all
by `@[csimp]`; the theorems below are about the stages as defined.

## Main definitions

* `narrowPrep` — `widenJ`, then `maskElim`, then `NFProg.dce`.
* `allSpecTraits` — the operation traits at which every operation is speculatable.
* `castProg` — a program carried along equalities of its context and result types.

## Main results

* `narrowPrep_denote` — the stages preserve the denotation along `mapVal` and `transArgs`.
* `regionExportableB_maskElimGo`, `regionExportableB_rename?`, `regionExportableB_dce` — mask
  elimination and dead-binding elimination keep `regionExportableB`.
* `narrowPrep_of_exportable` — the gate: an exportable program has an exportable result.
* `callFree_map?`, `callFree_dce`, `callFree_maskElimGo`, `callFree_narrowPrep` — the stages
  keep the absence of `call` and its presence.
* `opBlock?_ctLeak`, `widenJ_leakRun` — the blocks of the widening emit the events of their
  operation, and the widened program the events of the source.
* `ctLeak_rename_of_okE`, `leakRun_maskElimGo`, `leakRun_maskElim` — mask elimination keeps
  the leakage run.
* `narrowPrep_ctRel`, `narrowPrep_events` — equal source events give equal events of the
  result.
* `denote_dce_jasmin`, `narrowPrep_denote_eq` — dead-binding elimination, and so the stages,
  keep the denotation of a Jasmin program exactly.
* `narrowPrep_cast_denote`, `narrowPrep_cast_nfct`, `narrowPrep_cast_callFree` — over a
  context and result types that `wideTy` fixes, the result carried back by `castProg` denotes
  what the source denotes, is constant time where it is, and has its calls.
* `wordSig_wide`, `wordSig_of_calls`, `transports_of_wide` — the calls of an exportable program
  are at word signatures, which the widening fixes.
* `narrowPrep_denoteAt_eq`, `narrowPrep_castCtx_denoteAt` — the same at call environments.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportComplete (regionExportableB_eq)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel opLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel jKind)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProg (appLift bindHom varTyCast)

/-! ## 1. The stages -/

/-- **The narrow-word stages**: the widening `widenJ`, then mask elimination `maskElim`, then
    dead-binding elimination `NFProg.dce`; `none` when the widening refuses an operation. -/
def narrowPrep {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    Option (NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)) :=
  (widenJ p).map fun q => NFProg.dce (maskElim q)

/-- A result of `narrowPrep` is `dce (maskElim q₀)` for the widened program `q₀`. -/
theorem narrowPrep_eq_some {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)} :
    narrowPrep p = some q ↔ ∃ q₀, widenJ p = some q₀ ∧ NFProg.dce (maskElim q₀) = q :=
  Option.map_eq_some_iff

/-! ## 2. The denotation -/

/-- **Preservation.** A run of `p` at `V` to `v` is a run of a result of `narrowPrep p` at the
    widened valuation `mapVal V` to the widened `v`, at the same fuel. -/
theorem narrowPrep_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)}
    (hq : narrowPrep p = some q) {fuel : Nat} {V : Valuation Γ}
    {v : Valuation (d := jasminDialect) ts} (hv : p.denote fuel V = some v) :
    q.denote fuel (mapVal V) = some (transArgs wideTy (fun x => transTy x) v) := by
  obtain ⟨q₀, h₀, rfl⟩ := narrowPrep_eq_some.mp hq
  apply NFProg.denote_dce
  have hm := denoteAt_maskElim (CallDenote.env (d := jasminDialect)) fuel q₀ (mapVal V)
  have hw := widenJ_denote_empty fuel p V q₀ h₀
  rw [hv] at hw
  exact hm.trans hw

/-- The operation traits at which every operation of `jasminDialect` is speculatable. -/
def allSpecTraits : OpTraits jasminDialect where
  pure _ := true
  speculatable _ := true
  constLike _ := false
  cost _ := 0

/-- Every binding `dce` removes is speculatable under `allSpecTraits`. -/
theorem dceDrops_allSpec {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) : NFProg.dceDrops allSpecTraits.speculatable p = true := by
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [NFProg.dceDrops, ih, Bool.true_and]
      split <;> rfl
  | forLoop count inits body k ihb ihk => simp only [NFProg.dceDrops, ihb, ihk, Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.dceDrops, iht, ihe, ihk, Bool.and_self]
  | whileLoop inits body k ihb ihk => simp only [NFProg.dceDrops, ihb, ihk, Bool.and_self]
  | call f args k ih => exact ih

/-- **Dead-binding elimination keeps the denotation of a Jasmin program**: every operation of
    `jasminDialect` denotes a value, so a removed binding cannot fail. -/
theorem denote_dce_jasmin [CallDenote jasminDialect] {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (fuel : Nat) (V : Valuation Γ) :
    (NFProg.dce p).denote fuel V = p.denote fuel V :=
  NFProg.denote_dce_eq allSpecTraits (SpecLaw.ofPure allSpecTraits) p (dceDrops_allSpec p) fuel V

/-- **The stages keep the denotation exactly** along `mapVal` and `transArgs`, at every fuel. -/
theorem narrowPrep_denote_eq {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)}
    (hq : narrowPrep p = some q) (fuel : Nat) (V : Valuation Γ) :
    q.denote fuel (mapVal V) =
      (p.denote fuel V).map (transArgs wideTy (fun x => transTy x)) := by
  obtain ⟨q₀, h₀, rfl⟩ := narrowPrep_eq_some.mp hq
  rw [denote_dce_jasmin]
  have hm := denoteAt_maskElim (CallDenote.env (d := jasminDialect)) fuel q₀ (mapVal V)
  exact hm.trans (widenJ_denote_empty fuel p V q₀ h₀)

/-! ## 3. The gate -/

/-- **Mask elimination keeps `regionExportableB`**: it removes bindings and renames the
    arguments of the others. -/
theorem regionExportableB_maskElimGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ),
      regionExportableB p = true → regionExportableB (maskElimGo p A ren) = true := by
  induction p with
  | ret vs => intro Δ A ren _; rfl
  | var e k ih =>
      intro Δ A ren h
      simp only [regionExportableB, Bool.and_eq_true] at h
      have hkeep : ∀ i, regionExportableB (NFProg.var (e.rename ren)
          (maskElimGo k (A.push i) (Ctxt.Hom.lift ren))) = true := fun i => by
        simp only [regionExportableB, Bool.and_eq_true]
        exact ⟨h.1, ih _ _ h.2⟩
      simp only [maskElimGo]
      split
      · split
        · exact ih _ _ h.2
        · exact hkeep _
      · exact hkeep _
  | forLoop count inits body k ihb ihk =>
      intro Δ A ren h
      simp only [maskElimGo, regionExportableB, Bool.and_eq_true] at h ⊢
      exact ⟨ihb _ _ h.1, ihk _ _ h.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ A ren h
      simp only [maskElimGo, regionExportableB, Bool.and_eq_true] at h ⊢
      exact ⟨⟨iht _ _ h.1.1, ihe _ _ h.1.2⟩, ihk _ _ h.2⟩
  | whileLoop inits body k ihb ihk =>
      intro Δ A ren h
      simp only [maskElimGo, regionExportableB, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, ihb _ _ h.1.2⟩, ihk _ _ h.2⟩
  | call f args k ih =>
      intro Δ A ren h
      simp only [maskElimGo, regionExportableB, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih _ _ h.2⟩

/-- `maskElim` keeps `regionExportableB`. -/
theorem regionExportableB_maskElim {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : regionExportableB p = true) :
    regionExportableB (maskElim p) = true :=
  regionExportableB_maskElimGo p _ _ h

/-- **A partial renaming keeps `regionExportableB`**: it keeps every operation and every
    signature. -/
theorem regionExportableB_rename? {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} {f : PRen Γ Δ} {p' : NFProg jasminDialect Δ ts},
      NFProg.rename? f p = some p' → regionExportableB p' = regionExportableB p := by
  induction p with
  | ret vs =>
      intro Δ f p' h
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
  | var e k ih =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨e', he, k', hk, rfl⟩ := h
      simp only [Expr.rename?, Option.map_eq_some_iff] at he
      obtain ⟨_, -, rfl⟩ := he
      simp only [regionExportableB, ih hk]
      rfl
  | forLoop count inits body k ihb ihk =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, _, -, b', hb, k', hk, rfl⟩ := h
      simp only [regionExportableB, ihb hb, ihk hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, t', ht, e', he, k', hk, rfl⟩ := h
      simp only [regionExportableB, iht ht, ihe he, ihk hk]
  | whileLoop inits body k ihb ihk =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb, k', hk, rfl⟩ := h
      simp only [regionExportableB, ihb hb, ihk hk]
  | call fn args k ih =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, k', hk, rfl⟩ := h
      simp only [regionExportableB, ih hk]

/-- **Dead-binding elimination keeps `regionExportableB`.** -/
theorem regionExportableB_dce {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (h : regionExportableB p = true) :
    regionExportableB (NFProg.dce p) = true := by
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [regionExportableB, Bool.and_eq_true] at h
      simp only [NFProg.dce]
      split
      · rename_i k' hk
        rw [regionExportableB_rename? _ hk]
        exact ih h.2
      · simp only [regionExportableB, h.1, ih h.2, Bool.and_self]
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.dce, regionExportableB, Bool.and_eq_true] at h ⊢
      exact ⟨ihb h.1, ihk h.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.dce, regionExportableB, Bool.and_eq_true] at h ⊢
      exact ⟨⟨iht h.1.1, ihe h.1.2⟩, ihk h.2⟩
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.dce, regionExportableB, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, ihb h.1.2⟩, ihk h.2⟩
  | call f args k ih =>
      simp only [NFProg.dce, regionExportableB, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih h.2⟩

/-- **The gate.** A program that passes `regionExportableB` has a result of `narrowPrep`, and
    that result passes `regionExportableB`. -/
theorem narrowPrep_of_exportable {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true) :
    ∃ q, narrowPrep p = some q ∧ regionExportableB q = true := by
  have hops : p.allOps opMemB = true := by
    have h := hp
    rw [regionExportableB_eq] at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  obtain ⟨q₀, h₀⟩ := Option.isSome_iff_exists.mp (widenJ_isSome p hops)
  exact ⟨_, narrowPrep_eq_some.mpr ⟨q₀, h₀, rfl⟩, regionExportableB_dce _
    (regionExportableB_maskElim (widenJ_regionExportable_of_exportable p hp q₀ h₀))⟩

/-! ## 4. The calls -/

section CallFree

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- A block spliced before continuations whose programs have `callFree = b` gives a program
    with `callFree = b`. -/
theorem callFree_spliceNF? {ts : List d'.Ty} (b : Bool) :
    {Δ : Ctxt d'} → {a : d'.Ty} → (blk : Com d' Δ a) →
    (k : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → Var Δ' a → Option (NFProg d' Δ' ts)) →
    (∀ {Δ' : Ctxt d'} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) (q : NFProg d' Δ' ts),
      k ren res = some q → q.callFree = b) →
    ∀ {q : NFProg d' Δ ts}, NFProg.spliceNF? blk k = some q → q.callFree = b
  | _, _, .ret v, _, hk, _, h => hk _ v _ h
  | _, _, .var _ blk, k, hk, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact callFree_spliceNF? b blk _ (fun ren res q hq => hk _ res q hq) hq'

/-- Carrying the first result type keeps `callFree`. -/
theorem callFree_castRetHead {Δ : Ctxt d} {a b : d.Ty} {ts : List d.Ty} (h : a = b)
    (p : NFProg d Δ (a :: ts)) : (NFProg.castRetHead h p).callFree = p.callFree := by
  subst h
  rfl

/-- **The conversion `map?` keeps the absence of `call` and its presence**: it keeps every
    `call` node and lowers bindings into blocks without `call`. -/
theorem callFree_map? (P : PartialBlockLowering d d') (hT : P.RegionTypes) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) {q : NFProg d' Δ (ts.map P.mapTy)},
      NFProg.map? P hT p ren = some q → q.callFree = p.callFree := by
  induction p with
  | ret vs =>
      intro Δ ren q h
      cases h
      rfl
  | var e k ih =>
      intro Δ ren q h
      obtain ⟨blk, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact callFree_spliceNF? _ _ _ (fun ren' res q' hq' => ih _ hq') h
  | forLoop count inits body k ihb ihk =>
      intro Δ ren q h
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [NFProg.callFree, ihb _ hb, ihk _ hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren q h
      obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [NFProg.callFree, iht _ ht, ihe _ he, ihk _ hk]
  | whileLoop inits body k ihb ihk =>
      intro Δ ren q h
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [NFProg.callFree, callFree_castRetHead, ihb _ hb, ihk _ hk]
  | call f args k ih =>
      intro Δ ren q h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl

/-- A partial renaming keeps `callFree`. -/
theorem callFree_rename? {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} {f : PRen Γ Δ} {p' : NFProg d Δ ts},
      NFProg.rename? f p = some p' → p'.callFree = p.callFree := by
  induction p with
  | ret vs =>
      intro Δ f p' h
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
  | var e k ih =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨e', -, k', hk, rfl⟩ := h
      show k'.callFree = k.callFree
      exact ih hk
  | forLoop count inits body k ihb ihk =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, _, -, b', hb, k', hk, rfl⟩ := h
      simp only [NFProg.callFree, ihb hb, ihk hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, t', ht, e', he, k', hk, rfl⟩ := h
      simp only [NFProg.callFree, iht ht, ihe he, ihk hk]
  | whileLoop inits body k ihb ihk =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, b', hb, k', hk, rfl⟩ := h
      simp only [NFProg.callFree, ihb hb, ihk hk]
  | call fn args k ih =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, -, k', -, rfl⟩ := h
      rfl

/-- Dead-binding elimination keeps `callFree`. -/
theorem callFree_dce {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    (NFProg.dce p).callFree = p.callFree := by
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [NFProg.dce]
      split
      · rename_i k' hk
        rw [callFree_rename? _ hk]
        exact ih
      · exact ih
  | forLoop count inits body k ihb ihk => simp only [NFProg.dce, NFProg.callFree, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.dce, NFProg.callFree, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk => simp only [NFProg.dce, NFProg.callFree, ihb, ihk]
  | call f args k ih => rfl

end CallFree

/-- Mask elimination keeps `callFree`. -/
theorem callFree_maskElimGo {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ),
      (maskElimGo p A ren).callFree = p.callFree := by
  induction p with
  | ret vs => intro Δ A ren; rfl
  | var e k ih =>
      intro Δ A ren
      simp only [maskElimGo]
      split
      · split
        · exact ih _ _
        · exact ih _ _
      · exact ih _ _
  | forLoop count inits body k ihb ihk =>
      intro Δ A ren
      simp only [maskElimGo, NFProg.callFree, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ A ren
      simp only [maskElimGo, NFProg.callFree, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk =>
      intro Δ A ren
      simp only [maskElimGo, NFProg.callFree, ihb, ihk]
  | call f args k ih => intro Δ A ren; rfl

/-- **The stages keep the absence of `call` and its presence.** -/
theorem callFree_narrowPrep {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)}
    (hq : narrowPrep p = some q) : q.callFree = p.callFree := by
  obtain ⟨q₀, h₀, rfl⟩ := narrowPrep_eq_some.mp hq
  rw [callFree_dce]
  exact (callFree_maskElimGo q₀ _ _).trans (callFree_map? widenP widenP_regionTypes p _ h₀)

/-! ## 5. The events of the widening -/

section Events

variable {Pj : JLeakParams}

/-- At parameters with no variable-time operation, an operation other than a stack access
    and a leaf call emits no event. -/
theorem jKind_quiet (hV : ∀ op, Pj.opVT op = none) (op : JasminOp)
    (hl : ∀ w n, op ≠ .stackLoad w n) (hs : ∀ w n, op ≠ .stackStore w n)
    (hc : ∀ f as r, op ≠ .extCall f as r) : jKind Pj op = .quiet := by
  cases op <;> simp_all [jKind]

/-- **The block leak leaf.** At parameters with no variable-time operation, the block of an
    operation emits, at the widened valuation, the events of the operation: none, or the index
    of a stack access, which the widening keeps at width `64`. -/
theorem opBlock?_ctLeak (hV : ∀ op, Pj.opVT op = none) {Γ : Ctxt jasminDialect}
    (op : JasminOp)
    (args : HVector (fun t => Var Γ t) (DialectSignature.sig (d := jasminDialect) op))
    (blk : Com jasminDialect (Γ.map wideTy)
      (wideTy (DialectSignature.ret (d := jasminDialect) op)))
    (h : wideOpBlock? op args = some blk) (V : Valuation Γ) :
    ComLevelCheck.Com.ctLeak (jLeakModel Pj) blk (mapVal V) =
      ComLevelCheck.Expr.ctLeak (jLeakModel Pj)
        (⟨op, rfl, args⟩ : Expr jasminDialect Γ _) V := by
  have L := fun {t : JasminTy} (v : Var Γ t) => lookup_mapVar_mapVal_wide v V
  cases op <;> simp only [wideOpBlock?, reduceCtorEq] at h <;> (injection h with h; subst h)
  case stackLoad w n =>
    rcases args with _ | ⟨a, _ | ⟨i, _ | _⟩⟩
    have hi : (mapVar i).lookup (mapVal V) = i.lookup V := (L i).trans (transTy_reg64 _)
    show [CTLeak.addr "" ((Dialects.JasminComLLeak.jValNat (.reg 64)
        ((mapVar i).lookup (mapVal V)) : Nat) : Int)] ++ [] =
      [CTLeak.addr "" ((Dialects.JasminComLLeak.jValNat (.reg 64) (i.lookup V) : Nat) : Int)]
    rw [hi, List.append_nil]
  case stackStore w n =>
    rcases args with _ | ⟨a, _ | ⟨i, _ | ⟨v, _ | _⟩⟩⟩
    have hi : (mapVar i).lookup (mapVal V) = i.lookup V := (L i).trans (transTy_reg64 _)
    show [CTLeak.addr "" ((Dialects.JasminComLLeak.jValNat (.reg 64)
        ((mapVar i).lookup (mapVal V)) : Nat) : Int)] ++ [] =
      [CTLeak.addr "" ((Dialects.JasminComLLeak.jValNat (.reg 64) (i.lookup V) : Nat) : Int)]
    rw [hi, List.append_nil]
  all_goals
    simp only [ComLevelCheck.Expr.ctLeak, opLeak, jLeakModel, jKind, hV]
    simp only [arithBlock, castBlock, mulhiBlock, addLoBlock, addHiBlock, wideRorBlock, sarBlock,
      wideShlBlock, withMask, countThen, one]
    repeat' split
    all_goals simp [ComLevelCheck.Com.ctLeak, ComLevelCheck.Expr.ctLeak, opLeak,
      jKind, hV]

/-- The block leak leaf at an expression. -/
theorem exprBlock?_ctLeak (hV : ∀ op, Pj.opVT op = none) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (e : Expr jasminDialect Γ t)
    (blk : Com jasminDialect (Γ.map wideTy) (wideTy t)) (h : exprBlock? e = some blk)
    (V : Valuation Γ) :
    ComLevelCheck.Com.ctLeak (jLeakModel Pj) blk (mapVal V) =
      ComLevelCheck.Expr.ctLeak (jLeakModel Pj) e V := by
  obtain ⟨op, rfl, args⟩ := e
  exact opBlock?_ctLeak hV op args blk h V

/-- **The leakage transformer of the widening is the identity.** At parameters with no
    variable-time operation, a program `widenJ` returns for `p` runs at `mapVal V`, at every
    fuel, to the widened results and the events of the run of `p` at `V`. -/
theorem widenJ_leakRun (hV : ∀ op, Pj.opVT op = none) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (V : Valuation Γ)
    (q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)) (hq : widenJ p = some q) :
    Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel q (mapVal V) =
      (Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V).map
        fun r => (transArgs wideTy (fun x => transTy x) r.1, r.2) :=
  NFProg.map?_leakRun widenP (fun x => transTy x) (fun V => mapVal V) (jLeakModel Pj)
    (jLeakModel Pj) widenP_regionTypes (fun _ => True) widenP_varTransports
    (fun e _ blk hblk V => exprBlock?_denote e blk hblk V)
    (fun e _ blk hblk V => exprBlock?_ctLeak hV e blk hblk V)
    widenP_mapValExtends widenP_regionTransports fuel p
    (NFProg.covered_of_forall _ (fun _ => trivial) p) (fun v => v) V (mapVal V)
    (FieldDialectBlockDescent.pullV_id _) q hq

/-! ## 6. The events of mask elimination -/

/-- A binding `okE` accepts emits, at related valuations, the events of the source: an
    operation with a relaxed argument is quiet, and every other reads equal arguments. -/
theorem ctLeak_rename_of_okE (hV : ∀ op, Pj.opVT op = none) {Γ Δ : Ctxt jasminDialect}
    {A : Facts Γ} {ren : Ctxt.Hom Γ Δ} {V : Valuation Γ} {W : Valuation Δ}
    (hR : MRel A ren V W) {t : JasminTy} (e : Expr jasminDialect Γ t) {i : Info}
    (hi : okE A e = some i) :
    ComLevelCheck.Expr.ctLeak (jLeakModel Pj) (e.rename ren) W =
      ComLevelCheck.Expr.ctLeak (jLeakModel Pj) e V := by
  obtain ⟨op, hty, args⟩ := e
  by_cases hx : allExactB A args = true
  · show opLeak _ op (Expr.lookupArgs (HVector.renameVars ren args) W) =
      opLeak _ op (Expr.lookupArgs args V)
    rw [hR.lookupArgs_eq args hx]
  · cases op <;> simp_all [okE, okOp, exactOp, ComLevelCheck.Expr.ctLeak, opLeak, jLeakModel,
      jKind]

/-- A mask emits no event. -/
theorem ctLeak_of_maskOf? (hV : ∀ op, Pj.opVT op = none) {Γ : Ctxt jasminDialect}
    {A : Facts Γ} {t : JasminTy} (e : Expr jasminDialect Γ t) {x : Var Γ (.reg 64)} {m : Nat}
    {h : t = .reg 64} (he : maskOf? A e = some ⟨(x, m), h⟩) (V : Valuation Γ) :
    ComLevelCheck.Expr.ctLeak (jLeakModel Pj) e V = [] := by
  obtain ⟨op, hty, args⟩ := e
  cases op <;> simp_all [maskOf?, ComLevelCheck.Expr.ctLeak, opLeak, jLeakModel, jKind]

/-- **Mask elimination keeps the leakage run along a renaming.** At parameters with no
    variable-time operation, when the facts relate `V` to `W` along `ren` and the source
    passes `okP`, the pass runs at `W`, at every fuel, to the results and events of the run of
    the source at `V`. -/
theorem leakRun_maskElimGo (hV : ∀ op, Pj.opVT op = none) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ) (V : Valuation Γ)
      (W : Valuation Δ), MRel A ren V W → okP p A = true →
      Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel (maskElimGo p A ren) W =
        Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V := by
  induction p with
  | ret vs =>
      intro Δ A ren V W hR hok
      simp only [maskElimGo, Dialects.NFLeak.NFProg.leakRun, hR.lookupArgs_eq vs hok]
  | var e k ih =>
      intro Δ A ren V W hR hok
      simp only [okP] at hok
      split at hok
      · rename_i i hi
        have hkeep : Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel
            (NFProg.var (e.rename ren)
              (maskElimGo k (A.push ((okE A e).getD .exact)) (Ctxt.Hom.lift ren))) W =
            Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel (NFProg.var e k) V := by
          have hs := okE_sound hR e hi
          simp only [Dialects.NFLeak.NFProg.leakRun, hi, Option.getD_some,
            ih _ _ _ _ (MRel.push hR hs.1 hs.2) hok, ctLeak_rename_of_okE hV hR e hi]
        simp only [maskElimGo]
        split
        · rename_i x m h he
          split
          · rename_i hk
            subst h
            have hrel := maskOf?_rel hR e he hi
            rw [ih _ _ _ _ (MRel.bind hR (varTyCast rfl (ren x)) hrel trivial) hk]
            simp only [Dialects.NFLeak.NFProg.leakRun, ctLeak_of_maskOf? hV e he V,
              List.nil_append, Option.map_id']
          · exact hkeep
        · exact hkeep
      · cases hok
  | forLoop count inits body k ihb ihk =>
      intro Δ A ren V W hR hok
      simp only [okP, Bool.and_eq_true, Option.isNone_iff_eq_none] at hok
      obtain ⟨⟨⟨hc, hi⟩, hb⟩, hk⟩ := hok
      have hbd : ∀ acc i, Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel
            (maskElimGo body (Facts.appExact _ (A.push .exact))
              (appLift _ (Ctxt.Hom.lift ren)))
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) W)) =
          Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) :=
        fun acc i => ihb _ _ _ _
          (MRel.appExact (MRel.push hR (rel_exact _) (constOK_exact _)) _ acc) hb
      have hkd : ∀ acc, Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel
            (maskElimGo k (Facts.appExact _ A) (appLift _ ren)) (hvAppend acc W) =
          Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel k (hvAppend acc V) :=
        fun acc => ihk _ _ _ _ (MRel.appExact hR _ acc) hk
      simp only [maskElimGo, Dialects.NFLeak.NFProg.leakRun, hR.lookupArgs_eq inits hi,
        hR.lookup_ren_eq count hc, hbd, hkd]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ A ren V W hR hok
      simp only [okP, Bool.and_eq_true, Option.isNone_iff_eq_none] at hok
      obtain ⟨⟨⟨hc, htn⟩, hel⟩, hk⟩ := hok
      have hkd : ∀ r, Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel
            (maskElimGo k (Facts.appExact _ A) (appLift _ ren)) (hvAppend r W) =
          Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel k (hvAppend r V) :=
        fun r => ihk _ _ _ _ (MRel.appExact hR _ r) hk
      simp only [maskElimGo, Dialects.NFLeak.NFProg.leakRun, hR.lookup_ren_eq cond hc,
        iht A ren V W hR htn, ihe A ren V W hR hel, hkd]
  | whileLoop inits body k ihb ihk =>
      intro Δ A ren V W hR hok
      simp only [okP, Bool.and_eq_true] at hok
      obtain ⟨⟨hi, hb⟩, hk⟩ := hok
      have hbd : ∀ acc, Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel
            (maskElimGo body (Facts.appExact _ A) (appLift _ ren)) (hvAppend acc W) =
          Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel body (hvAppend acc V) :=
        fun acc => ihb _ _ _ _ (MRel.appExact hR _ acc) hb
      have hkd : ∀ acc, Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel
            (maskElimGo k (Facts.appExact _ A) (appLift _ ren)) (hvAppend acc W) =
          Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel k (hvAppend acc V) :=
        fun acc => ihk _ _ _ _ (MRel.appExact hR _ acc) hk
      simp only [maskElimGo, Dialects.NFLeak.NFProg.leakRun, hR.lookupArgs_eq inits hi, hbd,
        hkd]
  | call f args k ih =>
      intro Δ A ren V W hR hok
      simp only [maskElimGo, Dialects.NFLeak.NFProg.leakRun]

/-- **Mask elimination keeps the leakage run** at parameters with no variable-time
    operation. -/
theorem leakRun_maskElim (hV : ∀ op, Pj.opVT op = none) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (V : Valuation Γ) :
    Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel (maskElim p) V =
      Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V :=
  leakRun_maskElimGo hV fuel p _ _ V V (fun _ => ⟨rel_exact _, constOK_exact _⟩)
    (okP_of_noRelax p _ (fun _ => rfl))

/-! ## 7. Constant time through the stages -/

/-- **The leakage transformer of the stages.** At parameters with no variable-time operation,
    a successful leakage run of `p` at `V` is matched by a leakage run of a result of
    `narrowPrep p` at `mapVal V` to the widened results, whose events are those
    `NFProg.dceErase` keeps from the trace of `p` at the mask-eliminated widened program. -/
theorem narrowPrep_leakRun (hV : ∀ op, Pj.opVT op = none) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)} (hq : narrowPrep p = some q)
    (V : Valuation Γ) (r : Valuation (d := jasminDialect) ts × List CTLeak)
    (h : Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V = some r) :
    ∃ q₀, widenJ p = some q₀ ∧ q = NFProg.dce (maskElim q₀) ∧ ∃ l,
      Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel q (mapVal V) =
        some (transArgs wideTy (fun x => transTy x) r.1, l) ∧
      ∀ rest, Dialects.NFLeak.NFProg.dceErase (jLeakModel Pj) fuel (maskElim q₀) (r.2 ++ rest)
        = (l, rest) := by
  obtain ⟨q₀, h₀, rfl⟩ := narrowPrep_eq_some.mp hq
  have hm : Dialects.NFLeak.NFProg.leakRunM (jLeakModel Pj) fuel (maskElim q₀) (mapVal V) =
      some (transArgs wideTy (fun x => transTy x) r.1, r.2) := by
    rw [Dialects.NFLeak.NFProg.leakRunM_eq_leakRun, leakRun_maskElim hV,
      widenJ_leakRun hV fuel p V q₀ h₀, h]
    rfl
  obtain ⟨l, hl, el⟩ := Dialects.NFLeak.NFProg.leakRunM_dce _ fuel _ _ _ hm
  rw [Dialects.NFLeak.NFProg.leakRunM_eq_leakRun] at hl
  exact ⟨q₀, h₀, rfl, l, hl, el⟩

/-- **Constant time through the stages, relative to source runs.** At parameters with no
    variable-time operation, two successful leakage runs of `p` with equal events give two
    successful leakage runs of a result of `narrowPrep p` at the widened valuations, to the
    widened results, with equal events. -/
theorem narrowPrep_ctRel (hV : ∀ op, Pj.opVT op = none) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)} (hq : narrowPrep p = some q)
    (V₁ V₂ : Valuation Γ) (r₁ r₂ : Valuation (d := jasminDialect) ts × List CTLeak)
    (h₁ : Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V₁ = some r₁)
    (h₂ : Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V₂ = some r₂)
    (he : r₁.2 = r₂.2) :
    ∃ s₁ s₂, Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel q (mapVal V₁) = some s₁ ∧
      Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel q (mapVal V₂) = some s₂ ∧
      s₁.1 = transArgs wideTy (fun x => transTy x) r₁.1 ∧
      s₂.1 = transArgs wideTy (fun x => transTy x) r₂.1 ∧ s₁.2 = s₂.2 := by
  obtain ⟨q₀, h₀, rfl, l₁, k₁, e₁⟩ := narrowPrep_leakRun hV fuel hq V₁ r₁ h₁
  obtain ⟨q₀', h₀', hq', l₂, k₂, e₂⟩ := narrowPrep_leakRun hV fuel hq V₂ r₂ h₂
  rw [h₀] at h₀'
  obtain rfl := Option.some.inj h₀'
  refine ⟨_, _, k₁, k₂, rfl, rfl, ?_⟩
  have g1 := e₁ []
  have g2 := e₂ []
  rw [he] at g1
  rw [g1] at g2
  exact (Prod.mk.inj g2).1

/-- **The stages keep the source events equal.** At parameters with no variable-time
    operation, when the runs of `p` at `V₁` and `V₂` have equal events (or both fail), so have
    the runs of a result of `narrowPrep p` at `mapVal V₁` and `mapVal V₂`. -/
theorem narrowPrep_events (hV : ∀ op, Pj.opVT op = none) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)} (hq : narrowPrep p = some q)
    (V₁ V₂ : Valuation Γ)
    (h : (Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V₁).map Prod.snd =
      (Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V₂).map Prod.snd) :
    (Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel q (mapVal V₁)).map Prod.snd =
      (Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel q (mapVal V₂)).map Prod.snd := by
  have hnone : ∀ V, Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V = none →
      Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel q (mapVal V) = none := by
    intro V hn
    have h1 := Dialects.NFLeak.NFProg.leakRun_fst (jLeakModel Pj) fuel q (mapVal V)
    have h2 := Dialects.NFLeak.NFProg.leakRun_fst (jLeakModel Pj) fuel p V
    rw [hn] at h2
    have h3 := narrowPrep_denote_eq hq fuel V
    change _ = p.denote fuel V at h2
    change _ = q.denote fuel (mapVal V) at h1
    rw [← h2] at h3
    rw [h3] at h1
    exact Option.map_eq_none_iff.mp h1
  cases h₁ : Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V₁ with
  | none =>
      rw [h₁, Option.map_none] at h
      have h₂ := Option.map_eq_none_iff.mp h.symm
      rw [hnone V₁ h₁, hnone V₂ h₂]
  | some r₁ =>
      rw [h₁, Option.map_some] at h
      obtain ⟨r₂, h₂, he⟩ := Option.map_eq_some_iff.mp h.symm
      obtain ⟨s₁, s₂, k₁, k₂, -, -, hs⟩ := narrowPrep_ctRel hV fuel hq V₁ V₂ r₁ r₂ h₁ h₂ he.symm
      rw [k₁, k₂, Option.map_some, Option.map_some, hs]

end Events

/-! ## 8. Programs over wide contexts -/

/-- A program carried along equalities of its context and of its result types. -/
def castProg {Γ Γ' : Ctxt jasminDialect} {ts ts' : List JasminTy} (hΓ : Γ = Γ')
    (hts : ts = ts') (p : NFProg jasminDialect Γ ts) : NFProg jasminDialect Γ' ts' :=
  hΓ ▸ hts ▸ p

/-- A carried program is the program up to the cast. -/
theorem castProg_heq {Γ Γ' : Ctxt jasminDialect} {ts ts' : List JasminTy} (hΓ : Γ = Γ')
    (hts : ts = ts') (p : NFProg jasminDialect Γ ts) : castProg hΓ hts p ≍ p := by
  subst hΓ hts
  rfl

/-- Heterogeneously equal programs at heterogeneously equal valuations denote heterogeneously
    equal results. -/
theorem denote_heq {Γ Γ' : Ctxt jasminDialect} {ts ts' : List JasminTy} (hΓ : Γ = Γ')
    (hts : ts = ts') {p : NFProg jasminDialect Γ ts} {p' : NFProg jasminDialect Γ' ts'}
    (hp : p ≍ p') {V : Valuation Γ} {V' : Valuation Γ'} (hV : V ≍ V') (fuel : Nat) :
    p.denote fuel V ≍ p'.denote fuel V' := by
  subst hΓ hts
  cases hp
  cases hV
  rfl

/-- Heterogeneously equal programs at heterogeneously equal valuations emit equal events. -/
theorem leakRun_snd_heq (M : LeakModel jasminDialect) {Γ Γ' : Ctxt jasminDialect}
    {ts ts' : List JasminTy} (hΓ : Γ = Γ') (hts : ts = ts') {p : NFProg jasminDialect Γ ts}
    {p' : NFProg jasminDialect Γ' ts'} (hp : p ≍ p') {V : Valuation Γ} {V' : Valuation Γ'}
    (hV : V ≍ V') (fuel : Nat) :
    (Dialects.NFLeak.NFProg.leakRun M fuel p V).map Prod.snd =
      (Dialects.NFLeak.NFProg.leakRun M fuel p' V').map Prod.snd := by
  subst hΓ hts
  cases hp
  cases hV
  rfl

/-- **On a wide context the stages keep the denotation.** When `wideTy` fixes the context and
    the result types, a result of `narrowPrep p` carried back to them denotes, at every fuel
    and valuation, what `p` denotes. -/
theorem narrowPrep_cast_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (hΓ : Γ.map wideTy = Γ) (hts : ts.map wideTy = ts) {p : NFProg jasminDialect Γ ts}
    {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)} (hq : narrowPrep p = some q)
    (fuel : Nat) (V : Valuation Γ) : (castProg hΓ hts q).denote fuel V = p.denote fuel V := by
  have h1 := denote_heq hΓ.symm hts.symm (castProg_heq hΓ hts q)
    (mapVal_heq_of_wide hΓ V).symm fuel
  rw [narrowPrep_denote_eq hq] at h1
  exact eq_of_heq (h1.trans (option_map_hvector_heq hts _ (transArgs_heq_of_wide hts) _))

/-- **On a wide context the stages keep constant time.** At parameters with no variable-time
    operation, a result of `narrowPrep p` carried back to the context and result types of `p`
    is constant time for the labels and the fuel at which `p` is. -/
theorem narrowPrep_cast_nfct {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (hΓ : Γ.map wideTy = Γ)
    (hts : ts.map wideTy = ts) {p : NFProg jasminDialect Γ ts}
    {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)} (hq : narrowPrep p = some q)
    {L : ComLevelCheck.Labels Γ} {fuel : Nat}
    (h : Dialects.NFLeak.NFCT (jLeakModel Pj) L fuel p) :
    Dialects.NFLeak.NFCT (jLeakModel Pj) L fuel (castProg hΓ hts q) := by
  intro V₁ V₂ hpub
  have e : ∀ V : Valuation Γ,
      (Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel (castProg hΓ hts q) V).map
          Prod.snd =
        (Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel q (mapVal V)).map Prod.snd :=
    fun V => leakRun_snd_heq _ hΓ.symm hts.symm (castProg_heq hΓ hts q)
      (mapVal_heq_of_wide hΓ V).symm fuel
  rw [e, e]
  exact narrowPrep_events hV fuel hq V₁ V₂ (h V₁ V₂ hpub)

/-- **On a wide context the stages keep the absence of `call`.** -/
theorem narrowPrep_cast_callFree {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (hΓ : Γ.map wideTy = Γ) (hts : ts.map wideTy = ts) {p : NFProg jasminDialect Γ ts}
    {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)} (hq : narrowPrep p = some q) :
    (castProg hΓ hts q).callFree = p.callFree := by
  have key : ∀ {Γ' : Ctxt jasminDialect} {ts' : List JasminTy} (e₁ : Γ' = Γ) (e₂ : ts' = ts)
      (r : NFProg jasminDialect Γ' ts'), (castProg e₁ e₂ r).callFree = r.callFree := by
    intro Γ' ts' e₁ e₂ r
    subst e₁ e₂
    rfl
  rw [key hΓ hts q, callFree_narrowPrep hq]


/-! ## 9. Call environments -/

/-- A word signature is fixed by the widening. -/
theorem wordSig_wide {as rs : List JasminTy} (h : wordSig as rs = true) :
    as.map wideTy = as ∧ rs.map wideTy = rs := by
  rw [wordSig_iff] at h
  obtain ⟨ha, hr⟩ := h
  refine ⟨?_, ?_⟩
  · conv_rhs => rw [← List.map_id as]
    apply List.map_congr_left
    intro t ht
    have := ha t ht
    cases t <;> simp_all [callArgTy, wideTy, wideW, narrowB]
  · rcases hr with rfl | ⟨n, rfl⟩ <;> rfl

/-- A call of a program whose calls pass `callsAll C` passes `C`. -/
private theorem forall_calls_of_callsAll {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] (C : String → List d.Ty → List d.Ty → Bool) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (h : Haxc.ChainTotal.callsAll C p = true) :
    ∀ f as rs, p.Calls f as rs → C f as rs = true := by
  induction p with
  | ret vs => intro f as rs hc; simp [NFProg.Calls] at hc
  | var e k ih => exact ih h
  | forLoop count inits body k ihb ihk =>
      simp only [Haxc.ChainTotal.callsAll, Bool.and_eq_true] at h
      rintro f as rs (hc | hc)
      exacts [ihb h.1 f as rs hc, ihk h.2 f as rs hc]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [Haxc.ChainTotal.callsAll, Bool.and_eq_true] at h
      rintro f as rs (hc | hc | hc)
      exacts [iht h.1.1 f as rs hc, ihe h.1.2 f as rs hc, ihk h.2 f as rs hc]
  | whileLoop inits body k ihb ihk =>
      simp only [Haxc.ChainTotal.callsAll, Bool.and_eq_true] at h
      rintro f as rs (hc | hc)
      exacts [ihb h.1 f as rs hc, ihk h.2 f as rs hc]
  | call f' args k ih =>
      simp only [Haxc.ChainTotal.callsAll, Bool.and_eq_true] at h
      rintro f as rs (⟨rfl, rfl, rfl⟩ | hc)
      exacts [h.1, ih h.2 f as rs hc]

/-- Every call of a program that passes `regionExportableB` is at a word signature. -/
theorem wordSig_of_calls {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hB : regionExportableB p = true) :
    ∀ f as rs, p.Calls f as rs → wordSig as rs = true := by
  have h := hB
  rw [regionExportableB_eq] at h
  simp only [Bool.and_eq_true] at h
  have hw := h.2
  rw [wordCalls_eq_callsAll] at hw
  exact forall_calls_of_callsAll _ p hw

/-- **A call environment agrees with itself along the widening at word signatures**: the
    widening fixes their types and values. -/
theorem transports_of_wide (E : CallEnv jasminDialect)
    {C : String → List JasminTy → List JasminTy → Prop}
    (hC : ∀ f as rs, C f as rs → as.map wideTy = as ∧ rs.map wideTy = rs) :
    E.Transports E (fun as => as.map wideTy)
      (fun x => transArgs wideTy (fun x => transTy x) x) C := by
  intro f as rs x hc
  obtain ⟨ha, hr⟩ := hC f as rs hc
  have key : ∀ (as' rs' : List JasminTy) (_ : as' = as) (_ : rs' = rs)
      (y : Valuation (d := jasminDialect) as') (_ : y ≍ x)
      (g : Valuation (d := jasminDialect) rs → Valuation (d := jasminDialect) rs'),
      (∀ r, g r ≍ r) → E.call f as' rs' y = (E.call f as rs x).map g := by
    intro as' rs' e₁ e₂ y hy g hg
    subst e₁ e₂
    obtain rfl := eq_of_heq hy
    have hid : g = id := funext fun r => eq_of_heq (hg r)
    subst hid
    simp
  exact key _ _ ha hr _ (transArgs_heq_of_wide ha x) _ (transArgs_heq_of_wide hr)

/-- **The stages keep the denotation at call environments** that agree along the widening at
    every call of the program. -/
theorem narrowPrep_denoteAt_eq (E E' : CallEnv jasminDialect) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts}
    {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)} (hq : narrowPrep p = some q)
    (hCall : E.Transports E' (fun as => as.map wideTy)
      (fun x => transArgs wideTy (fun x => transTy x) x) p.Calls)
    (fuel : Nat) (V : Valuation Γ) :
    q.denoteAt E' fuel (mapVal V) =
      (p.denoteAt E fuel V).map (transArgs wideTy (fun x => transTy x)) := by
  obtain ⟨q₀, h₀, rfl⟩ := narrowPrep_eq_some.mp hq
  have hd := @denote_dce_jasmin ⟨E'⟩ _ _ (maskElim q₀) fuel (mapVal V)
  have hm := denoteAt_maskElim E' fuel q₀ (mapVal V)
  exact (hd.trans hm).trans (widenJ_denote E E' fuel p hCall V q₀ h₀)

/-- Heterogeneously equal programs over equal contexts denote heterogeneously equal results
    at every call environment. -/
theorem denoteAt_heq (E : CallEnv jasminDialect) {Γ Γ' : Ctxt jasminDialect}
    {ts : List JasminTy} (hΓ : Γ = Γ') {p : NFProg jasminDialect Γ ts}
    {p' : NFProg jasminDialect Γ' ts} (hp : p ≍ p') {V : Valuation Γ} {V' : Valuation Γ'}
    (hV : V ≍ V') (fuel : Nat) : p.denoteAt E fuel V = p'.denoteAt E fuel V' := by
  subst hΓ
  cases hp
  cases hV
  rfl

/-- **Over a wide context, the stages keep the denotation at every call environment**, up to
    the widening of the results: a result of `narrowPrep p` carried back to the context of a
    program `p` that passes `regionExportableB`, whose calls are at word signatures, denotes the
    widened denotation of `p`. -/
theorem narrowPrep_castCtx_denoteAt (E : CallEnv jasminDialect) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (hΓ : Γ.map wideTy = Γ) {p : NFProg jasminDialect Γ ts}
    (hB : regionExportableB p = true)
    {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)} (hq : narrowPrep p = some q)
    (fuel : Nat) (V : Valuation Γ) :
    (castProg hΓ rfl q).denoteAt E fuel V =
      (p.denoteAt E fuel V).map (transArgs wideTy (fun x => transTy x)) := by
  rw [denoteAt_heq E hΓ.symm (castProg_heq hΓ rfl q) (mapVal_heq_of_wide hΓ V).symm fuel]
  exact narrowPrep_denoteAt_eq E E hq
    (transports_of_wide E fun f as rs hc => wordSig_wide (wordSig_of_calls hB f as rs hc)) fuel V

end CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords
