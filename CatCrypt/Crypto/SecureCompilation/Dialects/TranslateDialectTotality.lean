/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote

@[expose] public section

set_option autoImplicit false

/-!
# Totality of the scalar front on reads-bound covered bodies

`TranslateDialectDirectControl.translateDialectControl` and the jasmin lowering
`DialectToJasminCom.cryptoDialectToJasminCom` are `Option`-valued, and the
preservation theorem `translateDialectControl_denote_ctl` takes their success as
a hypothesis. This module proves that success, structurally: on a straight-line
body whose commands are covered scalar arms and whose reads are bound in the
`VarMap` at the right types, the front translates, the emitted continuation
accepts every lowerable tail, and the resulting `Com catCryptDialect` lowers to
`Com jasminDialect`. The rolled-loop front gate
`(frontLoopBodyJ … body).isSome` follows for any such body, with no evaluation
of the body's command list.

The reads-bound discipline is a big-step judgment `TransTotal σ c σ'` over
name-to-type maps `σ : String → Option CryptoTy`: each command's reads must be
claimed by `σ` at the type its front arm matches on, and each command updates
`σ` at the name it binds. `VmApprox σ vm` ties the map to a `VarMap` as a lower
bound, so the judgment never mentions De Bruijn contexts and composes along
`RSeq` by function update alone.

## Main results

* `VmApprox` / `NameTys.upd` / `vmApprox_upd` — the name-to-type lower bound on
  a `VarMap` and its stability under a front binding.
* `ContJTotal` and its closure lemmas (`ContJTotal.id` / `.comp` / `.varBind` /
  `.castCtx`) — a `ComCont` prefix that accepts every jasmin-lowerable tail and
  emits a jasmin-lowerable program.
* `lowerSExpr_total` — the `SExpr` chain lowering succeeds when the expression
  is `srcClean` and every variable it reads is bound at `.sword 64`, binds its
  result at `.sword 64`, preserves all non-temporary bindings, and emits a
  `ContJTotal` prefix.
* `TransTotal` — the reads-bound covered judgment (`RSkip` / `RBlock` / `RSeq`
  / `RScalarSet` / `RScalarSetExpr` / `RArrLoad` / `RArrStore`).
* `translateDialectFull_total` / `translateDialectControl_total` — the front
  succeeds on a `TransTotal` body from any `VarMap` the entry map
  lower-bounds, with the exit map lower-bounding the exit `VarMap` and the
  emitted prefix `ContJTotal`.
* `frontLoopBodyCD_total` / `frontLoopBodyJ_total` — the rolled-loop body
  front succeeds on a `TransTotal` body whose exit map binds the accumulator
  name at the accumulator type: the success gate the per-kernel
  `(frontLoopBodyJ …).isSome` hypotheses ask for.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
  (cryptoDialectToJasminCom toJExprD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (IsCoveredS srcClean isTmpName ne_tmpName_of_not_isTmp)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
  (frontLoopBodyCD frontLoopBodyJ frontLoopBodyJ_eq)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located)

/-! ## 1. Name-to-type lower bounds on a `VarMap` -/

/-- A name-to-type map: the string-level shadow of a `VarMap`, free of the
    De Bruijn context, so reads-bound side conditions compose along `RSeq` by
    function update. -/
def NameTys : Type := String → Option CryptoTy

namespace NameTys

/-- Update one name's claimed type. -/
def upd (σ : NameTys) (x : String) (t : CryptoTy) : NameTys :=
  fun y => if y = x then some t else σ y

end NameTys

/-- The name `y` is bound in the `VarMap` at type `t`. -/
def BoundAt {Γ : Ctx} (vm : VarMap Γ) (y : String) (t : CryptoTy) : Prop :=
  ∃ v : CVar Γ t, vm.lookup y = some ⟨t, v⟩

/-- `σ` lower-bounds the `VarMap`: every binding `σ` claims is present at the
    claimed type. Bindings the `VarMap` holds beyond `σ` (the front's fresh
    `__sx` temporaries in particular) are unconstrained. -/
def VmApprox (σ : NameTys) {Γ : Ctx} (vm : VarMap Γ) : Prop :=
  ∀ x t, σ x = some t → BoundAt vm x t

/-- Every name `σ` claims is outside the front's reserved `__sx` fresh-temp
    namespace. -/
def SrcTys (σ : NameTys) : Prop := ∀ x, (σ x).isSome → ¬ isTmpName x

/-- The empty map lower-bounds every `VarMap`. -/
theorem vmApprox_none {Γ : Ctx} (vm : VarMap Γ) :
    VmApprox (fun _ => none) vm := fun _ _ h => by simp at h

/-- The empty map claims no temporary. -/
theorem srcTys_none : SrcTys (fun _ => none) := fun _ h => by simp at h

/-- A binding at the top of the context is looked up at its own name. -/
theorem boundAt_bind_self {Γ : Ctx} (vm : VarMap Γ) (x : String) (t : CryptoTy) :
    BoundAt (vm.bind (t := t) x) x t :=
  ⟨.here, by simp [VarMap.bind]⟩

/-- A binding at the top of the context preserves the lookup of every other
    name, weakened. -/
theorem boundAt_bind_of_ne {Γ : Ctx} {vm : VarMap Γ} {y : String} {t : CryptoTy}
    (x : String) (s : CryptoTy) (hne : y ≠ x) (h : BoundAt vm y t) :
    BoundAt (vm.bind (t := s) x) y t := by
  obtain ⟨v, hv⟩ := h
  exact ⟨.there v, by simp [VarMap.bind, hne, hv]⟩

/-- A `.sword 64` binding preserves `.sword 64`-boundness of every name — the
    rebound name included. -/
theorem boundAt64_bind64 {Γ : Ctx} {vm : VarMap Γ} {y : String} (x : String)
    (h : BoundAt vm y (.sword 64)) :
    BoundAt (vm.bind (t := .sword 64) x) y (.sword 64) := by
  by_cases hyx : y = x
  · subst hyx
    exact boundAt_bind_self vm y _
  · exact boundAt_bind_of_ne x _ hyx h

/-- Lower-bound stability under a front binding: binding `x` at `t` in the
    `VarMap` realises the map update `σ.upd x t`. -/
theorem vmApprox_upd {σ : NameTys} {Γ : Ctx} {vm : VarMap Γ} {t : CryptoTy}
    (h : VmApprox σ vm) (x : String) :
    VmApprox (σ.upd x t) (vm.bind (t := t) x) := by
  intro y s hy
  by_cases hyx : y = x
  · subst hyx
    have hst : t = s := by simpa [NameTys.upd] using hy
    subst hst
    exact boundAt_bind_self vm y t
  · simp only [NameTys.upd, if_neg hyx] at hy
    exact boundAt_bind_of_ne x t hyx (h y s hy)

/-- A map update at a non-temporary name keeps the map temporary-free. -/
theorem srcTys_upd {σ : NameTys} {x : String} {t : CryptoTy}
    (hσ : SrcTys σ) (hx : ¬ isTmpName x) : SrcTys (σ.upd x t) := by
  intro y hy
  by_cases hyx : y = x
  · exact hyx ▸ hx
  · exact hσ y (by simpa [NameTys.upd, if_neg hyx] using hy)

/-- `lookupU64` succeeds on a name bound at `.sword 64`. -/
theorem lookupU64_of_lookup {Γ : Ctx} {vm : VarMap Γ} {y : String}
    {v : CVar Γ (.sword 64)} (h : vm.lookup y = some ⟨.sword 64, v⟩) :
    lookupU64 vm y = some v := by
  simp [lookupU64, h]

/-! ## 2. Jasmin-lowerable continuation prefixes

Every prefix the scalar front emits is a composition of `ComCont.id`,
`ComCont.varBind` on a `toJExprD`-lowerable expression, and `ComCont.castCtx`.
`ContJTotal` packages the two facts the front-success gate needs about such a
prefix: applied to a tail whose jasmin lowering succeeds, the application
succeeds, and the resulting program's jasmin lowering succeeds. -/

/-- A `ComCont` prefix that accepts every jasmin-lowerable tail and emits a
    jasmin-lowerable program. -/
def ContJTotal {Γ Γ' : Ctx} (f : ComCont Γ Γ') : Prop :=
  ∀ {t : CryptoTy} (tail : Com catCryptDialect Γ' t),
    (cryptoDialectToJasminCom tail).isSome →
    ∃ com : Com catCryptDialect Γ t,
      f tail = some com ∧ (cryptoDialectToJasminCom com).isSome

/-- The identity prefix is jasmin-lowerable. -/
theorem ContJTotal.id {Γ : Ctx} : ContJTotal (ComCont.id (Γ := Γ)) :=
  fun tail h => ⟨tail, rfl, h⟩

/-- Composition of jasmin-lowerable prefixes. -/
theorem ContJTotal.comp {Γ Γ' Γ'' : Ctx} {f : ComCont Γ Γ'} {g : ComCont Γ' Γ''}
    (hf : ContJTotal f) (hg : ContJTotal g) : ContJTotal (ComCont.comp f g) := by
  intro t tail htail
  obtain ⟨b, hb, hbl⟩ := hg tail htail
  obtain ⟨c, hc, hcl⟩ := hf b hbl
  refine ⟨c, ?_, hcl⟩
  simp only [ComCont.comp, hb]
  exact hc

/-- A single binding of a `toJExprD`-lowerable expression is a jasmin-lowerable
    prefix. -/
theorem ContJTotal.varBind {Γ : Ctx} {s : CryptoTy} {e : Expr catCryptDialect Γ s}
    (he : (toJExprD e).isSome) : ContJTotal (ComCont.varBind e) := by
  intro t tail htail
  refine ⟨Com.var e tail, rfl, ?_⟩
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp he
  obtain ⟨tl, htl⟩ := Option.isSome_iff_exists.mp htail
  simp [cryptoDialectToJasminCom, he', htl]

/-- A codomain-context transport preserves jasmin-lowerability. -/
theorem ContJTotal.castCtx {Γ Δ Δ' : Ctx} (h : Δ = Δ') {f : ComCont Γ Δ}
    (hf : ContJTotal f) : ContJTotal (ComCont.castCtx h f) := by
  subst h
  exact hf

/-- Both branches of the `RArrLoad` prefix — the `memrefGetDyn` bind and the
    opaque `extCall` fallback — are jasmin-lowerable. -/
theorem contJTotal_arrLoadCont {Γ : Ctx}
    (dty : CatCrypt.Crypto.Jasmin.LowCT.TowerType)
    (resolvedArgs : List ((t : CryptoTy) × CVar Γ t))
    (idxSig : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys) :
    ContJTotal (arrLoadCont dty resolvedArgs idxSig hv) := by
  unfold arrLoadCont
  split
  · exact ContJTotal.varBind rfl
  · exact ContJTotal.varBind rfl

/-- All three branches of the `RArrStore` prefix — the transported
    `memrefSetDyn` bind and the two opaque `extCall` fallbacks — are
    jasmin-lowerable. -/
theorem contJTotal_arrStoreCont {Γ : Ctx}
    (dty : CatCrypt.Crypto.Jasmin.LowCT.TowerType)
    (resolvedArgs : List ((t : CryptoTy) × CVar Γ t))
    (idxSig : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys) :
    ContJTotal (arrStoreCont dty resolvedArgs idxSig hv) := by
  unfold arrStoreCont
  split
  · split
    · exact ContJTotal.castCtx _ (ContJTotal.varBind rfl)
    · exact ContJTotal.varBind rfl
  · exact ContJTotal.varBind rfl

/-! ## 3. Totality of the `SExpr` chain lowering

`lowerSExpr` declines only when a variable it reads is unbound (or bound off
`.sword 64`) or the expression leaves the `srcClean` alphabet. On a `srcClean`
expression with bound reads it succeeds; every binding it pushes is a fresh
`.sword 64` slot, so non-temporary bindings of any type and `.sword 64`
bindings of any name survive, and the emitted prefix is a chain of word-op
`varBind`s, each `toJExprD`-lowerable. -/

/-- **The `SExpr` chain lowering succeeds on bound reads.** For a `srcClean`
    expression whose variables are bound at `.sword 64`, `lowerSExpr` returns a
    result bound at `.sword 64`, preserves every non-temporary binding at its
    type and every `.sword 64` binding, and emits a jasmin-lowerable prefix. -/
theorem lowerSExpr_total :
    ∀ (e : SExpr), srcClean e →
    ∀ {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat),
      (∀ y ∈ sexprVars e, BoundAt vm y (.sword 64)) →
      ∃ (o : DTransOut Γ) (nm : String) (cnt' : Nat),
        lowerSExpr vm cnt e = some (o, nm, cnt') ∧
        BoundAt o.vm nm (.sword 64) ∧
        (∀ y t, ¬ isTmpName y → BoundAt vm y t → BoundAt o.vm y t) ∧
        (∀ y, BoundAt vm y (.sword 64) → BoundAt o.vm y (.sword 64)) ∧
        ContJTotal o.cont := by
  intro e
  induction e with
  | SVar x =>
      intro hcl Γ vm cnt hrd
      obtain ⟨v, hv⟩ := hrd x (by simp [sexprVars])
      refine ⟨⟨Γ, ComCont.id, vm⟩, x, cnt, ?_, ⟨v, hv⟩,
        fun y t _ hb => hb, fun y hb => hb, ContJTotal.id⟩
      simp only [lowerSExpr, lookupU64_of_lookup hv]
  | SLit n =>
      intro hcl Γ vm cnt hrd
      refine ⟨_, tmpName cnt, cnt + 1, rfl, boundAt_bind_self _ _ _,
        fun y t hyt hb =>
          boundAt_bind_of_ne _ _ (ne_tmpName_of_not_isTmp hyt cnt) hb,
        fun y hb => boundAt64_bind64 _ hb,
        ContJTotal.comp ContJTotal.id (ContJTotal.varBind rfl)⟩
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SMulHiU a b iha ihb =>
      intro hcl Γ vm cnt hrd
      obtain ⟨oA, na, cA, hA, hbA, hP1A, hP2A, hcA⟩ :=
        iha hcl.1 vm cnt (fun y hy =>
          hrd y (by simp only [sexprVars, List.mem_append]; exact Or.inl hy))
      obtain ⟨oB, nb, cB, hB, hbB, hP1B, hP2B, hcB⟩ :=
        ihb hcl.2 oA.vm cA (fun y hy => hP2A y
          (hrd y (by simp only [sexprVars, List.mem_append]; exact Or.inr hy)))
      obtain ⟨va, hva⟩ := hP2B na hbA
      obtain ⟨vb, hvb⟩ := hbB
      simp only [lowerSExpr, hA, hB, lookupU64_of_lookup hva,
        lookupU64_of_lookup hvb]
      refine ⟨_, _, _, rfl, boundAt_bind_self _ _ _,
        fun y t hyt hb =>
          boundAt_bind_of_ne _ _ (ne_tmpName_of_not_isTmp hyt cB)
            (hP1B y t hyt (hP1A y t hyt hb)),
        fun y hb => boundAt64_bind64 _ (hP2B y (hP2A y hb)),
        ContJTotal.comp (ContJTotal.comp hcA hcB) (ContJTotal.varBind rfl)⟩
  | SShl a b iha ihb | SShr a b iha ihb =>
      intro hcl Γ vm cnt hrd
      obtain ⟨oA, na, cA, hA, hbA, hP1A, hP2A, hcA⟩ :=
        iha hcl.1 vm cnt (fun y hy =>
          hrd y (by simp only [sexprVars, List.mem_append]; exact Or.inl hy))
      obtain ⟨oB, nb, cB, hB, hbB, hP1B, hP2B, hcB⟩ :=
        ihb hcl.2 oA.vm cA (fun y hy => hP2A y
          (hrd y (by simp only [sexprVars, List.mem_append]; exact Or.inr hy)))
      obtain ⟨va, hva⟩ := hP2B na hbA
      obtain ⟨vb, hvb⟩ := hbB
      simp only [lowerSExpr, hA, hB, lookupU64_of_lookup hva,
        lookupU64_of_lookup hvb]
      refine ⟨_, _, _, rfl, boundAt_bind_self _ _ _,
        fun y t hyt hb =>
          boundAt_bind_of_ne _ _ (ne_tmpName_of_not_isTmp hyt cB)
            (hP1B y t hyt (hP1A y t hyt hb)),
        fun y hb => boundAt64_bind64 _ (hP2B y (hP2A y hb)), ?_⟩
      cases b <;>
        exact ContJTotal.comp (ContJTotal.comp hcA hcB) (ContJTotal.varBind rfl)
  | SLt a b _ _ => intro hcl; exact hcl.elim
  | SAsr a b _ _ => intro hcl; exact hcl.elim
  | SMulS a b _ _ => intro hcl; exact hcl.elim
  | SMulHiS a b _ _ => intro hcl; exact hcl.elim
  | SLimb v i => intro hcl; exact hcl.elim

/-! ## 4. The reads-bound covered judgment -/

/-- **The reads-bound covered judgment.** `TransTotal σ c σ'` holds when every
    command of the straight-line body `c` is a covered scalar arm whose reads
    are claimed by the running name-to-type map at the type its front arm
    matches on; `σ'` is the map after `c`'s bindings. Soundness
    (`translateDialectFull_total`) turns a derivation into front success from
    any `VarMap` that realises `σ`.

    Every bound name is required to be outside the front's `__sx` fresh-temp
    namespace, so the map stays temporary-free (`SrcTys`) along a
    derivation. -/
inductive TransTotal : NameTys → LowCT → NameTys → Prop
  | rSkip {σ : NameTys} : TransTotal σ .RSkip σ
  | rBlock {σ σ' : NameTys} {body : LowCT} :
      TransTotal σ body σ' → TransTotal σ (.RBlock body) σ'
  | rSeq {σ σ₁ σ₂ : NameTys} {c₁ c₂ : LowCT} :
      TransTotal σ c₁ σ₁ → TransTotal σ₁ c₂ σ₂ →
      TransTotal σ (.RSeq c₁ c₂) σ₂
  | rScalarSet {σ : NameTys} (x : String) (n : Nat) (hx : ¬ isTmpName x) :
      TransTotal σ (.RScalarSet x n) (σ.upd x (.sword 64))
  | rScalarSetExpr {σ : NameTys} (x : String) (e : SExpr) (hx : ¬ isTmpName x)
      (hcl : srcClean e) (hrd : ∀ y ∈ sexprVars e, σ y = some (.sword 64)) :
      TransTotal σ (.RScalarSetExpr x e) (σ.upd x (.sword 64))
  | rArrLoad {σ : NameTys} (dst src : Located) (idxVar : String)
      (hd : ¬ isTmpName dst.locVar)
      (hs : (σ src.locVar).isSome) (hi : (σ idxVar).isSome) :
      TransTotal σ (.RArrLoad dst src idxVar)
        (σ.upd dst.locVar (encodeTy dst.locDst))
  | rArrStore {σ : NameTys} (arr : Located) (idxVar : String) (src : Located)
      (ha : ¬ isTmpName arr.locVar) (hb : (σ arr.locVar).isSome)
      (hs : (σ src.locVar).isSome) (hi : (σ idxVar).isSome) :
      TransTotal σ (.RArrStore arr idxVar src)
        (σ.upd arr.locVar (encodeTy arr.locDst))

/-- A derivation keeps the name-to-type map temporary-free. -/
theorem TransTotal.srcTys {σ σ' : NameTys} {c : LowCT}
    (h : TransTotal σ c σ') (hσ : SrcTys σ) : SrcTys σ' := by
  induction h with
  | rSkip => exact hσ
  | rBlock _ ih => exact ih hσ
  | rSeq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | rScalarSet x n hx => exact srcTys_upd hσ hx
  | rScalarSetExpr x e hx _ _ => exact srcTys_upd hσ hx
  | rArrLoad dst src idxVar hd _ _ => exact srcTys_upd hσ hd
  | rArrStore arr idxVar src ha _ _ _ => exact srcTys_upd hσ ha

/-- Every judged body lies in the straight-line scalar covered fragment. -/
theorem TransTotal.toIsCoveredS {σ σ' : NameTys} {c : LowCT}
    (h : TransTotal σ c σ') : IsCoveredS c := by
  induction h with
  | rSkip => exact .rSkip
  | rBlock _ ih => exact .rBlock ih
  | rSeq _ _ ih₁ ih₂ => exact .rSeq ih₁ ih₂
  | rScalarSet x n _ => exact .rScalarSet x n
  | rScalarSetExpr x e _ hcl _ => exact .rScalarSetExpr x e hcl
  | rArrLoad dst src idxVar _ _ _ => exact .rArrLoad dst src idxVar
  | rArrStore arr idxVar src _ _ _ _ => exact .rArrStore arr idxVar src

/-! ## 5. Soundness: front success on a judged body -/

/-- **The straight-line front succeeds on a judged body.** From any `VarMap`
    that realises the entry map, `translateDialectFull` translates a
    `TransTotal` body; the exit map lower-bounds the exit `VarMap` — the frame
    lookup a downstream accumulator selection needs — and the emitted prefix
    accepts every jasmin-lowerable tail into a jasmin-lowerable program. -/
theorem translateDialectFull_total {σ σ' : NameTys} {c : LowCT}
    (h : TransTotal σ c σ') :
    ∀ {Γ : Ctx} (vm : VarMap Γ), SrcTys σ → VmApprox σ vm →
      ∃ o : DTransOut Γ, translateDialectFull vm c = some o ∧
        VmApprox σ' o.vm ∧ ContJTotal o.cont := by
  induction h with
  | rSkip =>
      intro Γ vm hσ ha
      exact ⟨⟨Γ, ComCont.id, vm⟩, rfl, ha, ContJTotal.id⟩
  | rBlock _ ih =>
      intro Γ vm hσ ha
      obtain ⟨o, ho, ha', hc⟩ := ih vm hσ ha
      exact ⟨o, by simpa only [translateDialectFull] using ho, ha', hc⟩
  | rSeq h₁ h₂ ih₁ ih₂ =>
      intro Γ vm hσ ha
      obtain ⟨o₁, ho₁, ha₁, hc₁⟩ := ih₁ vm hσ ha
      obtain ⟨o₂, ho₂, ha₂, hc₂⟩ := ih₂ o₁.vm (h₁.srcTys hσ) ha₁
      refine ⟨⟨o₂.Γ', ComCont.comp o₁.cont o₂.cont, o₂.vm⟩, ?_, ha₂,
        ContJTotal.comp hc₁ hc₂⟩
      simp only [translateDialectFull, ho₁, ho₂]
  | rScalarSet x n hx =>
      intro Γ vm hσ ha
      exact ⟨_, rfl, vmApprox_upd ha x, ContJTotal.varBind rfl⟩
  | rScalarSetExpr x e hx hcl hrd =>
      intro Γ vm hσ ha
      obtain ⟨o, nm, cnt', heq, ⟨v, hv⟩, hP1, hP2, hcont⟩ :=
        lowerSExpr_total e hcl vm 0
          (fun y hy => ha y (.sword 64) (hrd y hy))
      refine ⟨pushVarBind o
        { op := .bvShiftL 64 0, retTy_eq := rfl, args := .cons (toVIRVar v) .nil }
        x, ?_, ?_, ?_⟩
      · simp only [translateDialectFull, heq, lookupU64_of_lookup hv]
      · intro y s hy
        by_cases hyx : y = x
        · subst hyx
          have hst : CryptoTy.sword 64 = s := by simpa [NameTys.upd] using hy
          subst hst
          exact boundAt_bind_self _ _ _
        · simp only [NameTys.upd, if_neg hyx] at hy
          exact boundAt_bind_of_ne _ _ hyx
            (hP1 y s (hσ y (by simp [hy])) (ha y s hy))
      · exact ContJTotal.comp hcont (ContJTotal.varBind rfl)
  | rArrLoad dst src idxVar hd hs hi =>
      intro Γ vm hσ ha
      obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨vs, hvs⟩ := ha _ ts hts
      obtain ⟨ti, hti⟩ := Option.isSome_iff_exists.mp hi
      obtain ⟨vi, hvi⟩ := ha _ ti hti
      have hres : resolveLocatedArgs vm [src] = some [⟨ts, vs⟩] := by
        simp [resolveLocatedArgs, hvs]
      refine ⟨⟨encodeTy dst.locDst :: Γ,
        arrLoadCont dst.locDst [⟨ts, vs⟩] ⟨ti, vi⟩
          (listSigmaToCHVector ([⟨ts, vs⟩] ++ [⟨ti, vi⟩])).2,
        vm.bind (t := encodeTy dst.locDst) dst.locVar⟩, ?_, ?_, ?_⟩
      · simp only [translateDialectFull, hres, hvi]
      · exact vmApprox_upd ha dst.locVar
      · exact contJTotal_arrLoadCont dst.locDst _ _ _
  | rArrStore arr idxVar src ha' hb hs hi =>
      intro Γ vm hσ ha
      obtain ⟨ta, hta⟩ := Option.isSome_iff_exists.mp hb
      obtain ⟨va, hva⟩ := ha _ ta hta
      obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨vs, hvs⟩ := ha _ ts hts
      obtain ⟨ti, hti⟩ := Option.isSome_iff_exists.mp hi
      obtain ⟨vi, hvi⟩ := ha _ ti hti
      have hres : resolveLocatedArgs vm [arr, src] = some [⟨ta, va⟩, ⟨ts, vs⟩] := by
        simp [resolveLocatedArgs, hva, hvs]
      refine ⟨⟨encodeTy arr.locDst :: Γ,
        arrStoreCont arr.locDst [⟨ta, va⟩, ⟨ts, vs⟩] ⟨ti, vi⟩
          (listSigmaToCHVector ([⟨ta, va⟩, ⟨ts, vs⟩] ++ [⟨ti, vi⟩])).2,
        vm.bind (t := encodeTy arr.locDst) arr.locVar⟩, ?_, ?_, ?_⟩
      · simp only [translateDialectFull, hres, hvi]
      · exact vmApprox_upd ha arr.locVar
      · exact contJTotal_arrStoreCont arr.locDst _ _ _

/-- `translateDialectControl` succeeds on a judged body: on the covered
    fragment it coincides with `translateDialectFull`, which
    `translateDialectFull_total` covers. -/
theorem translateDialectControl_total {σ σ' : NameTys} {c : LowCT}
    (h : TransTotal σ c σ') {Γ : Ctx} (vm : VarMap Γ)
    (hσ : SrcTys σ) (ha : VmApprox σ vm) :
    ∃ o : DTransOut Γ, translateDialectControl vm c = some o ∧
      VmApprox σ' o.vm ∧ ContJTotal o.cont := by
  rw [translateDialectControl_eq_full_of_covered vm h.toIsCoveredS.toIsCovered]
  exact translateDialectFull_total h vm hσ ha

/-! ## 6. Success of the rolled-loop body front -/

/-- **The rolled-loop body front's `catCryptDialect` stage succeeds on a judged
    body**, and its output lowers to jasmin. The exit map must claim the
    accumulator name at the accumulator type; the entry map must be realised by
    the body `VarMap` and claim no `__sx` temporary. -/
theorem frontLoopBodyCD_total {Γbody : Ctx} {accCTy : CryptoTy}
    {σ σ' : NameTys} (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    (h : TransTotal σ body σ') (hσ : SrcTys σ) (ha : VmApprox σ vmBody)
    (hacc : σ' accName = some accCTy) :
    ∃ com : Com catCryptDialect Γbody accCTy,
      frontLoopBodyCD (accCTy := accCTy) vmBody accName body = some com ∧
      (cryptoDialectToJasminCom com).isSome := by
  obtain ⟨o, htr, happ, hcont⟩ := translateDialectControl_total h vmBody hσ ha
  obtain ⟨v, hv⟩ := happ accName accCTy hacc
  obtain ⟨com, hcom, hlow⟩ := hcont (Com.ret (toVIRVar v)) (by rfl)
  refine ⟨com, ?_, hlow⟩
  simp only [frontLoopBodyCD, htr, hv, dif_pos]
  exact hcom

/-- **The rolled-loop body front succeeds on a judged body**: the
    `(frontLoopBodyJ …).isSome` gate holds structurally, with no evaluation of
    the body. -/
theorem frontLoopBodyJ_total {Γbody : Ctx} {accCTy : CryptoTy}
    {σ σ' : NameTys} (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    (h : TransTotal σ body σ') (hσ : SrcTys σ) (ha : VmApprox σ vmBody)
    (hacc : σ' accName = some accCTy) :
    (frontLoopBodyJ (accCTy := accCTy) vmBody accName body).isSome := by
  obtain ⟨com, hcd, hlow⟩ :=
    frontLoopBodyCD_total vmBody accName body h hσ ha hacc
  rw [frontLoopBodyJ_eq, hcd]
  exact hlow

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
