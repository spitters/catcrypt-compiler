/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FrontLoopBodyArrMemN

/-!
# The inductive walk that discharges `ContArrMemN o.cont`

`FrontLoopBodyArrMemN` supplies the scaffold — the `ContArrMemN` continuation
invariant, its prefix algebra, and the per-op `ScalarMemN`-head bridges — and
consumes `ContArrMemN o.cont` in `frontLoopBodyJ_arrMem`. This module produces
`ContArrMemN o.cont` by induction over the straight-line scalar front, mirroring
`translateDialectFull_total` / `translateDialectControl_total` but tracking
`ContArrMemN` in place of `ContJTotal`.

The reads-bound covered judgment `TransArrN` refines `TransTotal`: the array-op
arms carry the memref-cell typing that forces `arrLoadCont` / `arrStoreCont`
into their `memrefGetDyn` / `memrefSetDyn` branch rather than the opaque
`extCall` fallback (the `extCall` head is not `ScalarMemN`, so the fallback
carries no `ArrMemN`). The scalar-expression shift bound `k < 2 ^ 64` is already
part of `srcClean`, so the immediate-shift head bridge applies with no extra
hypothesis.

## Main results

* `lowerSExpr_totalArr` — the `SExpr` chain lowering, with `ContArrMemN o.cont`
  added to `lowerSExpr_total`'s conclusion. Covers the arithmetic / bitwise /
  shift / high-multiply alphabet `lowerSExpr` emits.
* `TransArrN` — the memref-typed reads-bound covered judgment, with
  `TransArrN.srcTys` / `TransArrN.toIsCoveredS`.
* `translateDialectFull_totalArr` / `translateDialectControl_totalArr` — the
  straight-line front produces `ContArrMemN o.cont` on a `TransArrN` body.
* `frontLoopBodyJ_arrMemN_of_judged` — the end lemma: for a `TransArrN` body
  whose exit map binds the accumulator at a `memref n` slot, the front-compiled
  update is `ArrMemN`, with no reduction of the body command list.

Coverage: the walk reaches every rolled-loop body whose command list lies in the
`RScalarSet` / `RScalarSetExpr` (over `SAdd` / `SSub` / `SMul` / `SAnd` / `SXor`
/ `SShl` / `SShr` / `SMulHiU`) / `RArrLoad` / `RArrStore` / `RSeq` / `RBlock` /
`RSkip` fragment — the single-loop `mpn_mul_1` / `mpn_addmul_1` / logical / shift
template bodies. It does not reach the carry-select / compare bodies (`cmp`,
`divrem`), whose `bvAddCarryLo` / `select` heads are emitted by the separate
`CarryChainSelect.emitAll` front, not by `translateDialectControl`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.FrontLoopBodyArrMemNWalk

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
  (cryptoDialectToJasminCom toJExprD)
open CatCrypt.Crypto.SecureCompilation.VIR.FrontLoopBodyArrMemN
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
  (translateDialectControl translateDialectControl_eq_full_of_covered)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (IsCoveredS srcClean isTmpName ne_tmpName_of_not_isTmp)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
  (frontLoopBodyCD frontLoopBodyJ frontLoopBodyJ_eq)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located)

/-! ## 1. The `SExpr` chain lowering lands `ContArrMemN` -/

/-- **`lowerSExpr` produces a `ContArrMemN` prefix.** The `ContArrMemN`-tracking
    twin of `lowerSExpr_total`: the same success / boundedness / preservation
    facts, with the emitted prefix additionally carrying `ContArrMemN`. Each
    emitted binding is a register-producing word op whose jasmin lowering has a
    `ScalarMemN` head, so it extends an `ArrMemN` tail by `ArrMemN.reg`. -/
theorem lowerSExpr_totalArr :
    ∀ (e : SExpr), srcClean e →
    ∀ {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat),
      (∀ y ∈ sexprVars e, BoundAt vm y (.sword 64)) →
      ∃ (o : DTransOut Γ) (nm : String) (cnt' : Nat),
        lowerSExpr vm cnt e = some (o, nm, cnt') ∧
        BoundAt o.vm nm (.sword 64) ∧
        (∀ y t, ¬ isTmpName y → BoundAt vm y t → BoundAt o.vm y t) ∧
        (∀ y, BoundAt vm y (.sword 64) → BoundAt o.vm y (.sword 64)) ∧
        ContArrMemN o.cont := by
  intro e
  induction e with
  | SVar x =>
      intro hcl Γ vm cnt hrd
      obtain ⟨v, hv⟩ := hrd x (by simp [sexprVars])
      refine ⟨⟨Γ, ComCont.id, vm⟩, x, cnt, ?_, ⟨v, hv⟩,
        fun y t _ hb => hb, fun y hb => hb, ContArrMemN.id⟩
      simp only [lowerSExpr, lookupU64_of_lookup hv]
  | SLit n =>
      intro hcl Γ vm cnt hrd
      refine ⟨_, tmpName cnt, cnt + 1, rfl, boundAt_bind_self _ _ _,
        fun y t hyt hb =>
          boundAt_bind_of_ne _ _ (ne_tmpName_of_not_isTmp hyt cnt) hb,
        fun y hb => boundAt64_bind64 _ hb,
        ContArrMemN.comp ContArrMemN.id
          (ContArrMemN.ofRegHead (regHeadLowerable_bvConst64 _ _))⟩
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb =>
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
        ContArrMemN.comp (ContArrMemN.comp hcA hcB)
          (ContArrMemN.ofRegHead ⟨_, rfl, ScalarMemN.var _ rfl _ (.ret .here)⟩)⟩
  | SMulHiU a b iha ihb =>
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
        ContArrMemN.comp (ContArrMemN.comp hcA hcB)
          (ContArrMemN.ofRegHead ⟨_, rfl, ScalarMemN.mulhi rfl _ (.ret .here)⟩)⟩
  | SShl a b iha ihb =>
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
      cases b
      case SLit k =>
        exact ContArrMemN.comp (ContArrMemN.comp hcA hcB)
          (ContArrMemN.ofRegHead (regHeadLowerable_bvShiftL hcl.2 _))
      all_goals
        exact ContArrMemN.comp (ContArrMemN.comp hcA hcB)
          (ContArrMemN.ofRegHead (regHeadLowerable_bvShiftLV _))
  | SShr a b iha ihb =>
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
        ?_⟩
      cases b
      case SLit k =>
        exact ContArrMemN.comp (ContArrMemN.comp hcA hcB)
          (ContArrMemN.ofRegHead (regHeadLowerable_bvShiftR hcl.2 _))
      all_goals
        exact ContArrMemN.comp (ContArrMemN.comp hcA hcB)
          (ContArrMemN.ofRegHead (regHeadLowerable_bvShiftRV _))
  | SLt a b _ _ => intro hcl; exact hcl.elim
  | SAsr a b _ _ => intro hcl; exact hcl.elim
  | SMulS a b _ _ => intro hcl; exact hcl.elim
  | SMulHiS a b _ _ => intro hcl; exact hcl.elim
  | SLimb v i => intro hcl; exact hcl.elim

/-! ## 2. The memref-typed reads-bound covered judgment -/

/-- **The memref-typed reads-bound covered judgment.** Refines `TransTotal`: the
    scalar arms are identical, and the array-op arms carry the memref-cell typing
    that pins `arrLoadCont` / `arrStoreCont` to their `memrefGetDyn` /
    `memrefSetDyn` branch. `rArrLoad` requires the destination to be a `u64`
    word, the array slot a `memref n`, and the index a `.sword 64`; `rArrStore`
    additionally requires the destination array's encoding to be exactly
    `.memref n`. -/
inductive TransArrN : NameTys → LowCT → NameTys → Prop
  | rSkip {σ : NameTys} : TransArrN σ .RSkip σ
  | rBlock {σ σ' : NameTys} {body : LowCT} :
      TransArrN σ body σ' → TransArrN σ (.RBlock body) σ'
  | rSeq {σ σ₁ σ₂ : NameTys} {c₁ c₂ : LowCT} :
      TransArrN σ c₁ σ₁ → TransArrN σ₁ c₂ σ₂ →
      TransArrN σ (.RSeq c₁ c₂) σ₂
  | rScalarSet {σ : NameTys} (x : String) (n : Nat) (hx : ¬ isTmpName x) :
      TransArrN σ (.RScalarSet x n) (σ.upd x (.sword 64))
  | rScalarSetExpr {σ : NameTys} (x : String) (e : SExpr) (hx : ¬ isTmpName x)
      (hcl : srcClean e) (hrd : ∀ y ∈ sexprVars e, σ y = some (.sword 64)) :
      TransArrN σ (.RScalarSetExpr x e) (σ.upd x (.sword 64))
  | rArrLoad {σ : NameTys} (dst src : Located) (idxVar : String) (n : Nat)
      (hd : ¬ isTmpName dst.locVar)
      (hdty : dst.locDst = .TU64)
      (hs : σ src.locVar = some (.memref n))
      (hi : σ idxVar = some (.sword 64)) :
      TransArrN σ (.RArrLoad dst src idxVar)
        (σ.upd dst.locVar (encodeTy dst.locDst))
  | rArrStore {σ : NameTys} (arr : Located) (idxVar : String) (src : Located) (n : Nat)
      (ha : ¬ isTmpName arr.locVar)
      (hb : σ arr.locVar = some (.memref n))
      (hda : encodeTy arr.locDst = .memref n)
      (hs : σ src.locVar = some (.sword 64))
      (hi : σ idxVar = some (.sword 64)) :
      TransArrN σ (.RArrStore arr idxVar src)
        (σ.upd arr.locVar (encodeTy arr.locDst))

/-- A derivation keeps the name-to-type map temporary-free. -/
theorem TransArrN.srcTys {σ σ' : NameTys} {c : LowCT}
    (h : TransArrN σ c σ') (hσ : SrcTys σ) : SrcTys σ' := by
  induction h with
  | rSkip => exact hσ
  | rBlock _ ih => exact ih hσ
  | rSeq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | rScalarSet x n hx => exact srcTys_upd hσ hx
  | rScalarSetExpr x e hx _ _ => exact srcTys_upd hσ hx
  | rArrLoad dst src idxVar n hd _ _ _ => exact srcTys_upd hσ hd
  | rArrStore arr idxVar src n ha _ _ _ _ => exact srcTys_upd hσ ha

/-- Every judged body lies in the straight-line scalar covered fragment. -/
theorem TransArrN.toIsCoveredS {σ σ' : NameTys} {c : LowCT}
    (h : TransArrN σ c σ') : IsCoveredS c := by
  induction h with
  | rSkip => exact .rSkip
  | rBlock _ ih => exact .rBlock ih
  | rSeq _ _ ih₁ ih₂ => exact .rSeq ih₁ ih₂
  | rScalarSet x n _ => exact .rScalarSet x n
  | rScalarSetExpr x e _ hcl _ => exact .rScalarSetExpr x e hcl
  | rArrLoad dst src idxVar n _ _ _ _ => exact .rArrLoad dst src idxVar
  | rArrStore arr idxVar src n _ _ _ _ _ => exact .rArrStore arr idxVar src

/-! ## 3. Soundness: the straight-line front produces `ContArrMemN` -/

/-- **The straight-line front produces a `ContArrMemN` prefix on a judged body.**
    The `ContArrMemN`-tracking twin of `translateDialectFull_total`: from any
    `VarMap` realising the entry map, `translateDialectFull` translates a
    `TransArrN` body, the exit map lower-bounds the exit `VarMap`, and the emitted
    prefix preserves `ArrMemN` membership. -/
theorem translateDialectFull_totalArr {σ σ' : NameTys} {c : LowCT}
    (h : TransArrN σ c σ') :
    ∀ {Γ : Ctx} (vm : VarMap Γ), SrcTys σ → VmApprox σ vm →
      ∃ o : DTransOut Γ, translateDialectFull vm c = some o ∧
        VmApprox σ' o.vm ∧ ContArrMemN o.cont := by
  induction h with
  | rSkip =>
      intro Γ vm hσ ha
      exact ⟨⟨Γ, ComCont.id, vm⟩, rfl, ha, ContArrMemN.id⟩
  | rBlock _ ih =>
      intro Γ vm hσ ha
      obtain ⟨o, ho, ha', hc⟩ := ih vm hσ ha
      exact ⟨o, by simpa only [translateDialectFull] using ho, ha', hc⟩
  | rSeq h₁ h₂ ih₁ ih₂ =>
      intro Γ vm hσ ha
      obtain ⟨o₁, ho₁, ha₁, hc₁⟩ := ih₁ vm hσ ha
      obtain ⟨o₂, ho₂, ha₂, hc₂⟩ := ih₂ o₁.vm (h₁.srcTys hσ) ha₁
      refine ⟨⟨o₂.Γ', ComCont.comp o₁.cont o₂.cont, o₂.vm⟩, ?_, ha₂,
        ContArrMemN.comp hc₁ hc₂⟩
      simp only [translateDialectFull, ho₁, ho₂]
  | rScalarSet x n hx =>
      intro Γ vm hσ ha
      exact ⟨_, rfl, vmApprox_upd ha x,
        ContArrMemN.ofRegHead (regHeadLowerable_bvConst64 _ _)⟩
  | rScalarSetExpr x e hx hcl hrd =>
      intro Γ vm hσ ha
      obtain ⟨o, nm, cnt', heq, ⟨v, hv⟩, hP1, hP2, hcont⟩ :=
        lowerSExpr_totalArr e hcl vm 0
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
      · exact ContArrMemN.comp hcont
          (ContArrMemN.ofRegHead (regHeadLowerable_bvShiftL (by positivity) _))
  | rArrLoad dst src idxVar n hd hdty hs hi =>
      intro Γ vm hσ ha
      obtain ⟨vs, hvs⟩ := ha _ (.memref n) hs
      obtain ⟨vi, hvi⟩ := ha _ (.sword 64) hi
      have hres : resolveLocatedArgs vm [src] = some [⟨.memref n, vs⟩] := by
        simp [resolveLocatedArgs, hvs]
      refine ⟨⟨encodeTy dst.locDst :: Γ,
        arrLoadCont dst.locDst [⟨.memref n, vs⟩] ⟨.sword 64, vi⟩
          (listSigmaToCHVector ([⟨.memref n, vs⟩] ++ [⟨.sword 64, vi⟩])).2,
        vm.bind (t := encodeTy dst.locDst) dst.locVar⟩, ?_, ?_, ?_⟩
      · simp only [translateDialectFull, hres, hvi]
      · exact vmApprox_upd ha dst.locVar
      · rw [hdty]
        exact ContArrMemN.ofRegHead (regHeadLowerable_memrefGetDyn _)
  | rArrStore arr idxVar src n ha' hb hda hs hi =>
      intro Γ vm hσ ha
      obtain ⟨va, hva⟩ := ha _ (.memref n) hb
      obtain ⟨vs, hvs⟩ := ha _ (.sword 64) hs
      obtain ⟨vi, hvi⟩ := ha _ (.sword 64) hi
      have hres : resolveLocatedArgs vm [arr, src]
          = some [⟨.memref n, va⟩, ⟨.sword 64, vs⟩] := by
        simp [resolveLocatedArgs, hva, hvs]
      refine ⟨⟨encodeTy arr.locDst :: Γ,
        arrStoreCont arr.locDst [⟨.memref n, va⟩, ⟨.sword 64, vs⟩] ⟨.sword 64, vi⟩
          (listSigmaToCHVector
            ([⟨.memref n, va⟩, ⟨.sword 64, vs⟩] ++ [⟨.sword 64, vi⟩])).2,
        vm.bind (t := encodeTy arr.locDst) arr.locVar⟩, ?_, ?_, ?_⟩
      · simp only [translateDialectFull, hres, hvi]
      · exact vmApprox_upd ha arr.locVar
      · simp only [arrStoreCont, dif_pos hda]
        exact ContArrMemN.castCtx (congrArg (· :: Γ) hda.symm)
          (ContArrMemN.memrefSetDyn _)

/-- `translateDialectControl` produces a `ContArrMemN` prefix on a judged body:
    on the covered fragment it coincides with `translateDialectFull`, which
    `translateDialectFull_totalArr` covers. -/
theorem translateDialectControl_totalArr {σ σ' : NameTys} {c : LowCT}
    (h : TransArrN σ c σ') {Γ : Ctx} (vm : VarMap Γ)
    (hσ : SrcTys σ) (ha : VmApprox σ vm) :
    ∃ o : DTransOut Γ, translateDialectControl vm c = some o ∧
      VmApprox σ' o.vm ∧ ContArrMemN o.cont := by
  rw [translateDialectControl_eq_full_of_covered vm h.toIsCoveredS.toIsCovered]
  exact translateDialectFull_totalArr h vm hσ ha

/-! ## 4. The end lemma: the front-compiled update is `ArrMemN` -/

/-- **The front-compiled rolled-loop update of a judged body is `ArrMemN`.**
    From a `TransArrN` body whose exit map binds the accumulator name at a
    `memref n` slot, `frontLoopBodyJ` produces a jasmin program in the
    array-returning stack-memory fragment, with no reduction of the body command
    list. Composes `translateDialectControl_totalArr` with the scaffold's
    `frontLoopBodyJ_arrMem`. -/
theorem frontLoopBodyJ_arrMemN_of_judged {Γbody : Ctx} {n : Nat}
    {σ σ' : NameTys} (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    (h : TransArrN σ body σ') (hσ : SrcTys σ) (ha : VmApprox σ vmBody)
    (hacc : σ' accName = some (.memref n))
    {update : Com jasminDialect (mapCtx Γbody) (mapTy (.memref n))}
    (hupd : frontLoopBodyJ (accCTy := .memref n) vmBody accName body = some update) :
    ArrMemN update := by
  obtain ⟨o, htr, happ, hcont⟩ := translateDialectControl_totalArr h vmBody hσ ha
  obtain ⟨v, hv⟩ := happ accName (.memref n) hacc
  exact frontLoopBodyJ_arrMem vmBody accName body htr hcont hv hupd

end CatCrypt.Crypto.SecureCompilation.VIR.FrontLoopBodyArrMemNWalk
