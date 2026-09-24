/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

/-!
# Leak-trace factoring for the direct dialect front

The static leak trace `Com.leakTrace` of a `Com catCryptDialect` is the ordered
list of op events (`Com.var e body ↦ leakEvent e :: leakTrace body`). The
direct dialect front (`TranslateDialectDirect`) emits its program prefix as a
`ComCont` built from `id` / `varBind` / `comp`. Each of those prepends a
*fixed-length* event prefix to any tail it accepts, so the leak trace of the
front's output factors as `prefix-events ++ tail-events`.

`ComCont.LeakFactors f k` records that `f` prepends exactly `k` events. It holds
for the three `ComCont` constructors and composes additively, so the front's
prefix leak-factors on the core straight-line fragment
(`translateDialect_cont_leakFactors`). The corollary `dialect_leak_prefix_constant`
is the dialect-leak analogue of `LowCTRHP.RHP_leakage_LowCT_prefix_constant`: the
leak-trace length a prefix contributes is the same for any two tails, so it does
not depend on the tail — the constancy fact behind leakage non-interference at the
front-end boundary, stated over `Com.leakTrace`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap)
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakTrace
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType)

/-- `f` prepends a fixed `k`-event leak prefix to any tail it accepts: whenever
    `f body = some c`, the leak trace of `c` is `k` events longer than that of
    `body`. -/
def ComCont.LeakFactors {Γ Γ' : Ctx} (f : ComCont Γ Γ') (k : Nat) : Prop :=
  ∀ {t : CryptoTy} (body : Com catCryptDialect Γ' t) (c : Com catCryptDialect Γ t),
    f body = some c → (Com.leakTrace c).length = k + (Com.leakTrace body).length

/-- The identity prefix adds no events. -/
theorem ComCont.id_leakFactors {Γ : Ctx} : ComCont.LeakFactors (ComCont.id (Γ := Γ)) 0 := by
  intro t body c h
  simp only [ComCont.id, Option.some.injEq] at h
  subst h; simp

/-- A single `varBind` adds exactly one event. -/
theorem ComCont.varBind_leakFactors {Γ : Ctx} {s : CryptoTy} (e : Expr catCryptDialect Γ s) :
    ComCont.LeakFactors (ComCont.varBind e) 1 := by
  intro t body c h
  simp only [ComCont.varBind, Option.some.injEq] at h
  subst h
  simp only [Com.leakTrace, List.length_cons]; omega

/-- Composition adds the two prefix lengths. -/
theorem ComCont.comp_leakFactors {Γ Γ' Γ'' : Ctx} {f : ComCont Γ Γ'} {g : ComCont Γ' Γ''}
    {kf kg : Nat} (hf : ComCont.LeakFactors f kf) (hg : ComCont.LeakFactors g kg) :
    ComCont.LeakFactors (ComCont.comp f g) (kf + kg) := by
  intro t body c h
  simp only [ComCont.comp] at h
  cases hgb : g body with
  | none => rw [hgb] at h; simp at h
  | some b' => rw [hgb] at h; rw [hf b' c h, hg body b' hgb]; omega

/-- **The direct dialect front's prefix leak-factors.** On the core straight-line
    fragment, `translateDialect` succeeds and its emitted `ComCont` prefix
    prepends a fixed number of leak events `k` to any tail. -/
theorem translateDialect_cont_leakFactors {Γ : Ctx} (vm : VarMap Γ) {c : LowCT} (hc : IsCore c) :
    ∃ o : DTransOut Γ, translateDialect vm c = some o ∧ ∃ k : Nat, ComCont.LeakFactors o.cont k := by
  induction hc generalizing Γ vm with
  | rSkip => exact ⟨_, rfl, 0, ComCont.id_leakFactors⟩
  | rScalarSet name n => exact ⟨_, rfl, 1, ComCont.varBind_leakFactors _⟩
  | @rSeq c₁ c₂ _ _ ih₁ ih₂ =>
      obtain ⟨o₁, h₁, k₁, hf₁⟩ := ih₁ vm
      obtain ⟨o₂, h₂, k₂, hf₂⟩ := ih₂ o₁.vm
      refine ⟨⟨o₂.Γ', ComCont.comp o₁.cont o₂.cont, o₂.vm⟩, ?_, k₁ + k₂,
        ComCont.comp_leakFactors hf₁ hf₂⟩
      simp only [translateDialect, h₁, h₂]
  | @rLetU64Zero name body _ ih =>
      obtain ⟨o, h, k, hf⟩ := ih (vm.bind name)
      refine ⟨⟨o.Γ', ComCont.comp
          (ComCont.varBind ⟨.bvConst 64 (0 : BitVec 64), rfl, .nil⟩) o.cont, o.vm⟩,
        ?_, 1 + k, ComCont.comp_leakFactors (ComCont.varBind_leakFactors _) hf⟩
      simp only [translateDialect, h]
  | @rBlock body _ ih => obtain ⟨o, h, k, hf⟩ := ih vm; exact ⟨_, h, k, hf⟩

/-- **The bounded-loop unroller's prefix leak-factors.** If the per-iteration
    body translator leak-factors at every `VarMap`, then `loopRForD`'s `N`-fold
    unroll leak-factors: each iteration contributes its body's prefix plus one
    `bvConst` counter event. By induction on `N`. -/
theorem loopRForD_leakFactors {Γ : Ctx}
    (translateBody : ∀ {Γ'' : Ctx}, VarMap Γ'' → Option (DTransOut Γ''))
    (hbody : ∀ {Γ'' : Ctx} (vm'' : VarMap Γ''),
      ∃ o : DTransOut Γ'', translateBody vm'' = some o ∧ ∃ k : Nat, ComCont.LeakFactors o.cont k)
    (vm : VarMap Γ) (x : String) (N : Nat) :
    ∃ o : DTransOut Γ, loopRForD translateBody vm x N = some o
      ∧ ∃ k : Nat, ComCont.LeakFactors o.cont k := by
  induction N with
  | zero => exact ⟨_, rfl, 0, ComCont.id_leakFactors⟩
  | succ n ih =>
      obtain ⟨oPre, hPre, kPre, hfPre⟩ := ih
      obtain ⟨oBody, hBody, kBody, hfBody⟩ := hbody (oPre.vm.bind x)
      refine ⟨⟨oBody.Γ',
        ComCont.comp oPre.cont (ComCont.comp
          (ComCont.varBind ⟨.bvConst 64 (BitVec.ofNat 64 n), rfl, .nil⟩) oBody.cont),
        oBody.vm⟩, ?_, kPre + (1 + kBody),
        ComCont.comp_leakFactors hfPre
          (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _) hfBody)⟩
      simp only [loopRForD, hPre, hBody]

/-- **Conditional bounded-loop leak-factoring.** If the body translator
    leak-factors *whenever it succeeds* (not necessarily total), then `loopRForD`,
    *whenever it succeeds*, leak-factors. This is the composable form needed when
    the body translator (e.g. `translateDialectControl`) can decline. By induction
    on `N`. -/
theorem loopRForD_leakFactors_cond {Γ : Ctx}
    (translateBody : ∀ {Γ'' : Ctx}, VarMap Γ'' → Option (DTransOut Γ''))
    (hbody : ∀ {Γ'' : Ctx} (vm'' : VarMap Γ'') {o'' : DTransOut Γ''},
      translateBody vm'' = some o'' → ∃ k : Nat, ComCont.LeakFactors o''.cont k)
    (vm : VarMap Γ) (x : String) (N : Nat) {o : DTransOut Γ}
    (h : loopRForD translateBody vm x N = some o) :
    ∃ k : Nat, ComCont.LeakFactors o.cont k := by
  induction N generalizing o with
  | zero =>
      rw [loopRForD, Option.some.injEq] at h
      subst h; exact ⟨0, ComCont.id_leakFactors⟩
  | succ n ih =>
      rw [loopRForD] at h
      split at h
      · simp at h
      · next oPre hPre =>
          dsimp only at h
          split at h
          · simp at h
          · next oBody hBody =>
              rw [Option.some.injEq] at h; subst h
              obtain ⟨kPre, hkPre⟩ := ih hPre
              obtain ⟨kBody, hkBody⟩ := hbody (oPre.vm.bind x) hBody
              exact ⟨kPre + (1 + kBody), ComCont.comp_leakFactors hkPre
                (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _) hkBody)⟩

/-- **The N-call dest-fold's prefix leak-factors.** `loopCallNDestsD` binds one
    `extCall` per destination; whenever it succeeds, its `ComCont` prefix
    leak-factors (one event per bound destination). By induction on the dest list. -/
theorem loopCallNDestsD_leakFactors {Γ : Ctx} (fname : String) (args : List Located)
    (vm : VarMap Γ) (dests : List Located) {i : Nat} {o : DTransOut Γ}
    (h : loopCallNDestsD fname args vm dests i = some o) :
    ∃ k : Nat, ComCont.LeakFactors o.cont k := by
  induction dests generalizing Γ vm i with
  | nil =>
      rw [loopCallNDestsD, Option.some.injEq] at h
      subst h; exact ⟨0, ComCont.id_leakFactors⟩
  | cons d rest ih =>
      rw [loopCallNDestsD] at h
      split at h
      · simp at h
      · split at h
        dsimp only at h
        split at h
        · simp at h
        · next oRest heq =>
            rw [Option.some.injEq] at h
            subst h
            obtain ⟨k, hk⟩ := ih (vm.bind d.locVar) heq
            exact ⟨1 + k, ComCont.comp_leakFactors (ComCont.varBind_leakFactors _) hk⟩

/-! ### Scalar-`SExpr` chain leak-factoring (`lowerSExpr`)

The `seqOut` / `pushVarBind` combinators leak-factor as `comp` / `comp ∘ varBind`,
so the `lowerSExpr` chain factors by a fixed count (one event per node). -/

/-- `seqOut` leak-factors as the composition of the two sub-prefixes. -/
theorem seqOut_leakFactors {Γ : Ctx} {oa : DTransOut Γ} {ob : DTransOut oa.Γ'}
    {ka kb : Nat} (ha : ComCont.LeakFactors oa.cont ka)
    (hb : ComCont.LeakFactors ob.cont kb) :
    ComCont.LeakFactors (seqOut oa ob).cont (ka + kb) := by
  simp only [seqOut]; exact ComCont.comp_leakFactors ha hb

/-- `pushVarBind` adds one event to its base prefix's factor. -/
theorem pushVarBind_leakFactors {Γ : Ctx} {o : DTransOut Γ}
    (e : Expr catCryptDialect o.Γ' (.sword 64)) (nm : String) {k : Nat}
    (h : ComCont.LeakFactors o.cont k) :
    ComCont.LeakFactors (pushVarBind o e nm).cont (k + 1) := by
  simp only [pushVarBind]; exact ComCont.comp_leakFactors h (ComCont.varBind_leakFactors _)

/-- A `ComCont` transported along a codomain-context equality leak-factors
    identically (the transport is `f` up to `rfl` on the equality). -/
theorem ComCont.castCtx_leakFactors {Γ Δ Δ' : Ctx} (h : Δ = Δ')
    {f : ComCont Γ Δ} {k : Nat} (hf : ComCont.LeakFactors f k) :
    ComCont.LeakFactors (ComCont.castCtx h f) k := by
  subst h; exact hf

set_option backward.isDefEq.respectTransparency.types false in
/-- **The `RArrLoad` prefix leak-factors at 1.** Both `arrLoadCont` branches —
    the real `memrefGetDyn` `varBind` and the opaque `extCall "arrLoadDyn"`
    `varBind` — prepend exactly one leak event. -/
theorem arrLoadCont_leakFactors {Γ : Ctx} (dty : TowerType)
    (resolvedArgs : List ((t : CryptoTy) × CVar Γ t)) (idxSig : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys) :
    ComCont.LeakFactors (arrLoadCont dty resolvedArgs idxSig hv) 1 := by
  unfold arrLoadCont
  split <;> exact ComCont.varBind_leakFactors _

/-- **The `RArrStore` prefix leak-factors at 1.** All `arrStoreCont` branches —
    the transported `memrefSetDyn` `varBind` and the opaque `extCall "arrStoreDyn"`
    `varBind` — prepend exactly one leak event. -/
theorem arrStoreCont_leakFactors {Γ : Ctx} (dty : TowerType)
    (resolvedArgs : List ((t : CryptoTy) × CVar Γ t)) (idxSig : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys) :
    ComCont.LeakFactors (arrStoreCont dty resolvedArgs idxSig hv) 1 := by
  unfold arrStoreCont
  split
  · split
    · exact ComCont.castCtx_leakFactors _ (ComCont.varBind_leakFactors _)
    · exact ComCont.varBind_leakFactors _
  · exact ComCont.varBind_leakFactors _

/-- **The scalar-`SExpr` chain leak-factors.** Whenever `lowerSExpr` succeeds, its
    emitted `ComCont` prefix prepends a fixed number of leak events. By induction
    on the `SExpr`, via the `seqOut` / `pushVarBind` combinator factorings. -/
theorem lowerSExpr_cont_leakFactors {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat)
    (e : CatCrypt.Crypto.Jasmin.LowCT.SExpr) {o : DTransOut Γ} {nm : String} {cnt' : Nat}
    (h : lowerSExpr vm cnt e = some (o, nm, cnt')) :
    ∃ k : Nat, ComCont.LeakFactors o.cont k := by
  induction e generalizing Γ vm cnt o nm cnt' with
  | SVar x =>
      simp only [lowerSExpr] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨ho, _⟩ := h; subst ho; exact ⟨0, ComCont.id_leakFactors⟩
      · exact absurd h (by simp)
  | SLit n =>
      simp only [lowerSExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨ho, _⟩ := h; subst ho
      exact ⟨0 + 1, pushVarBind_leakFactors _ _ ComCont.id_leakFactors⟩
  | SAdd a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨ka, hka⟩ := iha vm cnt heqA
                   obtain ⟨kb, hkb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨ka + kb + 1, pushVarBind_leakFactors _ _ (seqOut_leakFactors hka hkb)⟩)
                | exact absurd h (by simp)
  | SSub a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨ka, hka⟩ := iha vm cnt heqA
                   obtain ⟨kb, hkb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨ka + kb + 1, pushVarBind_leakFactors _ _ (seqOut_leakFactors hka hkb)⟩)
                | exact absurd h (by simp)
  | SMul a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨ka, hka⟩ := iha vm cnt heqA
                   obtain ⟨kb, hkb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨ka + kb + 1, pushVarBind_leakFactors _ _ (seqOut_leakFactors hka hkb)⟩)
                | exact absurd h (by simp)
  | SAnd a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨ka, hka⟩ := iha vm cnt heqA
                   obtain ⟨kb, hkb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨ka + kb + 1, pushVarBind_leakFactors _ _ (seqOut_leakFactors hka hkb)⟩)
                | exact absurd h (by simp)
  | SXor a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨ka, hka⟩ := iha vm cnt heqA
                   obtain ⟨kb, hkb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨ka + kb + 1, pushVarBind_leakFactors _ _ (seqOut_leakFactors hka hkb)⟩)
                | exact absurd h (by simp)
  | SShl a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨ka, hka⟩ := iha vm cnt heqA
                   obtain ⟨kb, hkb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨ka + kb + 1, pushVarBind_leakFactors _ _ (seqOut_leakFactors hka hkb)⟩)
                | exact absurd h (by simp)
  | SShr a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨ka, hka⟩ := iha vm cnt heqA
                   obtain ⟨kb, hkb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨ka + kb + 1, pushVarBind_leakFactors _ _ (seqOut_leakFactors hka hkb)⟩)
                | exact absurd h (by simp)
  | SLt _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SAsr _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SMulS _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SMulHiU a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨ka, hka⟩ := iha vm cnt heqA
                   obtain ⟨kb, hkb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨ka + kb + 1, pushVarBind_leakFactors _ _ (seqOut_leakFactors hka hkb)⟩)
                | exact absurd h (by simp)
  | SMulHiS _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SLimb _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)

/-- **The comparison-select prefix leak-factors.** The three `varBind`s of
    `selectCmpCont` prepend a fixed number of leak events. -/
theorem selectCmpCont_leakFactors {Γ : Ctx} (sV aV cV : CVar Γ (.sword 64)) :
    ∃ k : Nat, ComCont.LeakFactors (selectCmpCont sV aV cV) k := by
  unfold selectCmpCont
  exact ⟨_, ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
    (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
      (ComCont.varBind_leakFactors _))⟩

/-- **The mask-chain prefix leak-factors.** The eight `varBind`s of
    `selectMaskCont` prepend a fixed number of leak events. -/
theorem selectMaskCont_leakFactors {Γ : Ctx} (sV aV cV : CVar Γ (.sword 64)) :
    ∃ k : Nat, ComCont.LeakFactors (selectMaskCont sV aV cV) k := by
  unfold selectMaskCont
  exact ⟨_, ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
    (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
      (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
        (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
          (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
            (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
              (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
                (ComCont.varBind_leakFactors _)))))))⟩

/-- **The leaf-call front's prefix leak-factors (covered fragment).** On every
    `IsCovered` `LowCT`, whenever `translateDialectFull` succeeds its emitted
    `ComCont` prefix leak-factors: the straight-line/leaf-call/fold arms each
    prepend a fixed number of leak events to any tail. By induction on `IsCovered`
    — recursive arms via the IH, the `RCallN` fold via `loopCallNDestsD_leakFactors`,
    and the single/double `extCall` arms via `varBind`/`comp`. -/
theorem translateDialectFull_cont_leakFactors {Γ : Ctx} (vm : VarMap Γ) {c : LowCT}
    (hc : IsCovered c) {o : DTransOut Γ}
    (h : translateDialectFull vm c = some o) : ∃ k : Nat, ComCont.LeakFactors o.cont k := by
  induction hc generalizing Γ vm o with
  | rSkip =>
      simp only [translateDialectFull, translateDialect, Option.some.injEq] at h
      subst h; exact ⟨0, ComCont.id_leakFactors⟩
  | rScalarSet name n =>
      simp only [translateDialectFull, translateDialect, Option.some.injEq] at h
      subst h; exact ⟨1, ComCont.varBind_leakFactors _⟩
  | rSeq _ _ ih₁ ih₂ =>
      rw [translateDialectFull] at h
      split at h
      · next o₁ heq₁ =>
          split at h
          · next o₂ heq₂ =>
              rw [Option.some.injEq] at h; subst h
              obtain ⟨k₁, hk₁⟩ := ih₁ vm heq₁
              obtain ⟨k₂, hk₂⟩ := ih₂ o₁.vm heq₂
              exact ⟨k₁ + k₂, ComCont.comp_leakFactors hk₁ hk₂⟩
          · simp at h
      · simp at h
  | rLetU64Zero _ ih =>
      rw [translateDialectFull] at h
      split at h
      · next o' heq =>
          rw [Option.some.injEq] at h; subst h
          obtain ⟨k, hk⟩ := ih (vm.bind _) heq
          exact ⟨1 + k, ComCont.comp_leakFactors (ComCont.varBind_leakFactors _) hk⟩
      · simp at h
  | rBlock _ ih => rw [translateDialectFull] at h; exact ih vm h
  | rCallN fname dests args =>
      rw [translateDialectFull] at h
      exact loopCallNDestsD_leakFactors fname args vm dests h
  | rLimbStore loc idx v =>
      rw [translateDialectFull] at h
      split at h <;> first
        | (split at h <;> first
            | (split at h <;> first
                | (rw [Option.some.injEq] at h; subst h;
                   exact ⟨2, ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
                     (ComCont.varBind_leakFactors _)⟩)
                | exact absurd h (by simp))
            | (rw [Option.some.injEq] at h; subst h;
               exact ⟨2, ComCont.comp_leakFactors (ComCont.varBind_leakFactors _) (ComCont.varBind_leakFactors _)⟩)
            | exact absurd h (by simp))
        | exact absurd h (by simp)
  | rCallSwap fname dest1 dest2 args =>
      rw [translateDialectFull] at h
      split at h <;> first
        | (split at h; dsimp only at h; split at h <;> first
            | (rw [Option.some.injEq] at h; subst h;
               exact ⟨2, ComCont.comp_leakFactors (ComCont.varBind_leakFactors _) (ComCont.varBind_leakFactors _)⟩)
            | exact absurd h (by simp))
        | exact absurd h (by simp)
  | rCloneCall cv cloneTy oldDest innerF newDest args =>
      rw [translateDialectFull] at h
      split at h <;> first
        | (dsimp only at h; split at h <;> first
            | (rw [Option.some.injEq] at h; subst h;
               exact ⟨2, ComCont.comp_leakFactors (ComCont.varBind_leakFactors _) (ComCont.varBind_leakFactors _)⟩)
            | exact absurd h (by simp))
        | exact absurd h (by simp)
  | rScalarSetExpr x e =>
      rw [translateDialectFull] at h
      split at h
      · exact absurd h (by simp)
      · next r heqL =>
          obtain ⟨oe, ne, c⟩ := r
          obtain ⟨k, hk⟩ := lowerSExpr_cont_leakFactors vm 0 e heqL
          split at h <;> first
            | (simp only [Option.some.injEq] at h; subst h
               exact ⟨k + 1, pushVarBind_leakFactors _ _ hk⟩)
            | exact absurd h (by simp)
  | rSelect dst sel src0 src1 =>
      rw [translateDialectFull] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact selectCmpCont_leakFactors _ _ _
      · split at h <;>
          first
            | (split at h; dsimp only at h; rw [Option.some.injEq] at h; subst h;
               exact ⟨1, ComCont.varBind_leakFactors _⟩)
            | exact absurd h (by simp)
  | rArrLoadLit dst src idx =>
      rw [translateDialectFull] at h
      split at h
      · rw [Option.some.injEq] at h; subst h
        exact ⟨_, ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
          (ComCont.varBind_leakFactors _)⟩
      · split at h <;>
          first
            | (split at h; dsimp only at h; rw [Option.some.injEq] at h; subst h;
               exact ⟨1, ComCont.varBind_leakFactors _⟩)
            | exact absurd h (by simp)
  | rArrStoreLit arr idx src =>
      rw [translateDialectFull] at h
      split at h
      · rw [Option.some.injEq] at h; subst h
        exact ⟨_, ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
          (ComCont.varBind_leakFactors _)⟩
      · split at h <;>
          first
            | (split at h; dsimp only at h; rw [Option.some.injEq] at h; subst h;
               exact ⟨1, ComCont.varBind_leakFactors _⟩)
            | exact absurd h (by simp)
  | rArrLoad dst src idxVar =>
      rw [translateDialectFull] at h
      split at h <;>
        first
          | (split at h; dsimp only at h; rw [Option.some.injEq] at h; subst h;
             exact ⟨1, arrLoadCont_leakFactors _ _ _ _⟩)
          | exact absurd h (by simp)
  | rArrStore arr idxVar src =>
      rw [translateDialectFull] at h
      split at h <;>
        first
          | (split at h; dsimp only at h; rw [Option.some.injEq] at h; subst h;
             exact ⟨1, arrStoreCont_leakFactors _ _ _ _⟩)
          | exact absurd h (by simp)
  | rAssert label =>
      simp only [translateDialectFull, Option.some.injEq] at h
      subst h; exact ⟨0, ComCont.id_leakFactors⟩
  | _ =>
      rw [translateDialectFull] at h
      split at h <;>
        first
          | (split at h; dsimp only at h; rw [Option.some.injEq] at h; subst h;
             exact ⟨1, ComCont.varBind_leakFactors _⟩)
          | exact absurd h (by simp)

/-- **The full control front's prefix leak-factors.** On every `IsCoveredCtl`
    `LowCT`, whenever `translateDialectControl` succeeds its `ComCont` prefix
    leak-factors. The `ofCovered` case discharges via
    `translateDialectFull_cont_leakFactors`, the `RFor` case via
    `loopRForD_leakFactors_cond`, the `RIfNz` φ-merge via the branch IHs
    (pass-through `o₁`/`o₂` cont; the six-binding `ite`-chain at factor 6; the
    re-translation `comp o₁.cont o₂'.cont`), and the `RWhileNz` case by the
    context-invariant `ComCont.id` prefix at factor 0. -/
theorem translateDialectControl_cont_leakFactors {Γ : Ctx} (vm : VarMap Γ) {c : LowCT}
    (hc : IsCoveredCtl c) {o : DTransOut Γ}
    (h : translateDialectControl vm c = some o) : ∃ k : Nat, ComCont.LeakFactors o.cont k := by
  induction hc generalizing Γ vm o with
  | ofCovered hcov =>
      rw [translateDialectControl_eq_full_of_covered vm hcov] at h
      exact translateDialectFull_cont_leakFactors vm hcov h
  | rFor _ ih =>
      rw [translateDialectControl] at h
      refine loopRForD_leakFactors_cond _ ?_ vm _ _ h
      intro Γ'' vm'' o'' hh
      exact ih vm'' hh
  | rIfNz hthen helse ihthen ihelse =>
      rw [translateDialectControl] at h
      split at h
      · next w condVar =>
          split at h
          · next o₁eq o₂eq =>
              obtain ⟨k₁, hf₁⟩ := ihthen vm o₁eq
              obtain ⟨k₂, hf₂⟩ := ihelse vm o₂eq
              split_ifs at h with hg1 hg2 hg2'
              · rw [Option.some.injEq] at h; subst h; exact ⟨k₁, hf₁⟩
              · rw [Option.some.injEq] at h; subst h; exact ⟨k₂, hf₂⟩
              · rw [Option.some.injEq] at h; subst h; exact ⟨k₁, hf₁⟩
              · split at h
                · split at h
                  · rw [Option.some.injEq] at h; subst h
                    exact ⟨_, ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
                      (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
                        (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
                          (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
                            (ComCont.comp_leakFactors (ComCont.varBind_leakFactors _)
                              (ComCont.varBind_leakFactors _)))))⟩
                  · split at h
                    · next o₂' heq₂' =>
                        rw [Option.some.injEq] at h; subst h
                        obtain ⟨k₂', hf₂'⟩ := ihelse _ heq₂'
                        exact ⟨k₁ + k₂', ComCont.comp_leakFactors hf₁ hf₂'⟩
                    · simp at h
                · split at h
                  · next o₂' heq₂' =>
                      rw [Option.some.injEq] at h; subst h
                      obtain ⟨k₂', hf₂'⟩ := ihelse _ heq₂'
                      exact ⟨k₁ + k₂', ComCont.comp_leakFactors hf₁ hf₂'⟩
                  · simp at h
          · simp at h
      · simp at h
  | @rWhileNz name body _hbody _ih =>
      rw [translateDialectControl] at h
      split at h
      · cases hb : translateDialectControl vm body with
        | none => rw [hb] at h; exact absurd h (by simp)
        | some o' =>
            rw [hb] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            exact ⟨0, ComCont.id_leakFactors⟩
      · simp at h

/-- **Prefix leak-length constancy (dialect leak model).** A leak-factoring
    prefix `f` contributes the same number of leak events regardless of the tail:
    the length differential of the front-prefixed program over the tail is the
    same for any two tails. The dialect-leak analogue of
    `LowCTRHP.RHP_leakage_LowCT_prefix_constant`, stated over `Com.leakTrace`. -/
theorem dialect_leak_prefix_constant {Γ Γ' : Ctx} {f : ComCont Γ Γ'} {k : Nat}
    (hf : ComCont.LeakFactors f k) {t : CryptoTy}
    (b₁ b₂ : Com catCryptDialect Γ' t) (c₁ c₂ : Com catCryptDialect Γ t)
    (h₁ : f b₁ = some c₁) (h₂ : f b₂ = some c₂) :
    (Com.leakTrace c₁).length - (Com.leakTrace b₁).length
      = (Com.leakTrace c₂).length - (Com.leakTrace b₂).length := by
  rw [hf b₁ c₁ h₁, hf b₂ c₂ h₂]; omega

/-- **Front-level dialect leak prefix-constancy.** For every `IsCoveredCtl`
    `LowCT` whose front succeeds with output `o`, the emitted prefix `o.cont`
    contributes the same leak-trace length to any two dialect tails `b₁`/`b₂`: the
    length differential is independent of the tail. This is the dialect-leak,
    front-connected analogue of `LowCTRHP.RHP_leakage_LowCT_prefix_constant` —
    leakage non-interference at the front-end boundary, over `Com.leakTrace`.
    Combines `translateDialectControl_cont_leakFactors` (the front
    prefix leak-factors) with `dialect_leak_prefix_constant`. -/
theorem dialect_front_leak_prefix_constant {Γ : Ctx} (vm : VarMap Γ) {c : LowCT}
    (hc : IsCoveredCtl c) {o : DTransOut Γ}
    (h : translateDialectControl vm c = some o)
    {t : CryptoTy} (b₁ b₂ : Com catCryptDialect o.Γ' t)
    {c₁ c₂ : Com catCryptDialect Γ t}
    (h₁ : o.cont b₁ = some c₁) (h₂ : o.cont b₂ = some c₂) :
    (Com.leakTrace c₁).length - (Com.leakTrace b₁).length
      = (Com.leakTrace c₂).length - (Com.leakTrace b₂).length := by
  obtain ⟨k, hf⟩ := translateDialectControl_cont_leakFactors vm hc h
  exact dialect_leak_prefix_constant hf b₁ b₂ c₁ c₂ h₁ h₂

/-! ## Trace-tracking leak-factoring (actual prefix, not just length)

The stronger form: the front prefix prepends a *fixed event list* `pre` (not just
a length) to any tail. This is the dialect analogue of
`LowCTLeakTrace.leakTrace_translate_factors` (the actual-prefix factoring the
RHP-pipeline leakage-NI result, `RHP_pipeline_labeled_leakage_NI`, exposes). The
length-based `ComCont.LeakFactors` above is the `.length` corollary. -/

/-- `f` prepends a fixed event list `pre` to any tail it accepts. -/
def ComCont.LeakFactorsTrace {Γ Γ' : Ctx} (f : ComCont Γ Γ') (pre : LeakTrace) : Prop :=
  ∀ {t : CryptoTy} (body : Com catCryptDialect Γ' t) (c : Com catCryptDialect Γ t),
    f body = some c → Com.leakTrace c = pre ++ Com.leakTrace body

/-- A trace-factoring prefix is in particular length-factoring (`pre.length`). -/
theorem ComCont.leakFactorsTrace_toLength {Γ Γ' : Ctx} {f : ComCont Γ Γ'} {pre : LeakTrace}
    (h : ComCont.LeakFactorsTrace f pre) : ComCont.LeakFactors f pre.length := by
  intro t body c hc; rw [h body c hc, List.length_append]

theorem ComCont.id_leakFactorsTrace {Γ : Ctx} :
    ComCont.LeakFactorsTrace (ComCont.id (Γ := Γ)) [] := by
  intro t body c h; simp only [ComCont.id, Option.some.injEq] at h; subst h; simp

theorem ComCont.varBind_leakFactorsTrace {Γ : Ctx} {s : CryptoTy} (e : Expr catCryptDialect Γ s) :
    ComCont.LeakFactorsTrace (ComCont.varBind e) [Expr.leakEvent e] := by
  intro t body c h; simp only [ComCont.varBind, Option.some.injEq] at h; subst h
  simp [Com.leakTrace]

theorem ComCont.comp_leakFactorsTrace {Γ Γ' Γ'' : Ctx} {f : ComCont Γ Γ'} {g : ComCont Γ' Γ''}
    {pf pg : LeakTrace} (hf : ComCont.LeakFactorsTrace f pf) (hg : ComCont.LeakFactorsTrace g pg) :
    ComCont.LeakFactorsTrace (ComCont.comp f g) (pf ++ pg) := by
  intro t body c h
  simp only [ComCont.comp] at h
  cases hgb : g body with
  | none => rw [hgb] at h; simp at h
  | some b' => rw [hgb] at h; rw [hf b' c h, hg body b' hgb, List.append_assoc]

/-- The N-call dest-fold's trace-factoring. -/
theorem loopCallNDestsD_leakFactorsTrace {Γ : Ctx} (fname : String) (args : List Located)
    (vm : VarMap Γ) (dests : List Located) {i : Nat} {o : DTransOut Γ}
    (h : loopCallNDestsD fname args vm dests i = some o) :
    ∃ pre : LeakTrace, ComCont.LeakFactorsTrace o.cont pre := by
  induction dests generalizing Γ vm i with
  | nil => rw [loopCallNDestsD, Option.some.injEq] at h; subst h; exact ⟨[], ComCont.id_leakFactorsTrace⟩
  | cons d rest ih =>
      rw [loopCallNDestsD] at h
      split at h
      · exact absurd h (by simp)
      · split at h
        dsimp only at h
        split at h
        · exact absurd h (by simp)
        · next oRest heq =>
            rw [Option.some.injEq] at h; subst h
            obtain ⟨p, hp⟩ := ih _ heq
            exact ⟨_, ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _) hp⟩

/-- Conditional bounded-loop trace-factoring. -/
theorem loopRForD_leakFactorsTrace_cond {Γ : Ctx}
    (translateBody : ∀ {Γ'' : Ctx}, VarMap Γ'' → Option (DTransOut Γ''))
    (hbody : ∀ {Γ'' : Ctx} (vm'' : VarMap Γ'') {o'' : DTransOut Γ''},
      translateBody vm'' = some o'' → ∃ pre : LeakTrace, ComCont.LeakFactorsTrace o''.cont pre)
    (vm : VarMap Γ) (x : String) (N : Nat) {o : DTransOut Γ}
    (h : loopRForD translateBody vm x N = some o) :
    ∃ pre : LeakTrace, ComCont.LeakFactorsTrace o.cont pre := by
  induction N generalizing o with
  | zero => rw [loopRForD, Option.some.injEq] at h; subst h; exact ⟨[], ComCont.id_leakFactorsTrace⟩
  | succ n ih =>
      rw [loopRForD] at h
      split at h
      · simp at h
      · next oPre hPre =>
          dsimp only at h
          split at h
          · simp at h
          · next oBody hBody =>
              rw [Option.some.injEq] at h; subst h
              obtain ⟨pPre, hpPre⟩ := ih hPre
              obtain ⟨pBody, hpBody⟩ := hbody (oPre.vm.bind x) hBody
              exact ⟨_, ComCont.comp_leakFactorsTrace hpPre
                (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _) hpBody)⟩

/-- `seqOut` trace-factors as the concatenation of the two sub-prefixes. -/
theorem seqOut_leakFactorsTrace {Γ : Ctx} {oa : DTransOut Γ} {ob : DTransOut oa.Γ'}
    {pa pb : LeakTrace} (ha : ComCont.LeakFactorsTrace oa.cont pa)
    (hb : ComCont.LeakFactorsTrace ob.cont pb) :
    ComCont.LeakFactorsTrace (seqOut oa ob).cont (pa ++ pb) := by
  simp only [seqOut]; exact ComCont.comp_leakFactorsTrace ha hb

/-- Trace version of `ComCont.castCtx_leakFactors`. -/
theorem ComCont.castCtx_leakFactorsTrace {Γ Δ Δ' : Ctx} (h : Δ = Δ')
    {f : ComCont Γ Δ} {pre : LeakTrace} (hf : ComCont.LeakFactorsTrace f pre) :
    ComCont.LeakFactorsTrace (ComCont.castCtx h f) pre := by
  subst h; exact hf

set_option backward.isDefEq.respectTransparency.types false in
/-- **The `RArrLoad` prefix has a fixed leak-event trace.** -/
theorem arrLoadCont_leakFactorsTrace {Γ : Ctx} (dty : TowerType)
    (resolvedArgs : List ((t : CryptoTy) × CVar Γ t)) (idxSig : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys) :
    ∃ pre : LeakTrace, ComCont.LeakFactorsTrace (arrLoadCont dty resolvedArgs idxSig hv) pre := by
  unfold arrLoadCont
  split <;> exact ⟨_, ComCont.varBind_leakFactorsTrace _⟩

/-- **The `RArrStore` prefix has a fixed leak-event trace.** -/
theorem arrStoreCont_leakFactorsTrace {Γ : Ctx} (dty : TowerType)
    (resolvedArgs : List ((t : CryptoTy) × CVar Γ t)) (idxSig : (t : CryptoTy) × CVar Γ t)
    {argTys : List CryptoTy} (hv : CHVector (fun t => CVar Γ t) argTys) :
    ∃ pre : LeakTrace, ComCont.LeakFactorsTrace (arrStoreCont dty resolvedArgs idxSig hv) pre := by
  unfold arrStoreCont
  split
  · split
    · exact ⟨_, ComCont.castCtx_leakFactorsTrace _ (ComCont.varBind_leakFactorsTrace _)⟩
    · exact ⟨_, ComCont.varBind_leakFactorsTrace _⟩
  · exact ⟨_, ComCont.varBind_leakFactorsTrace _⟩

/-- `pushVarBind` appends its node's event to its base prefix's trace. -/
theorem pushVarBind_leakFactorsTrace {Γ : Ctx} {o : DTransOut Γ}
    (e : Expr catCryptDialect o.Γ' (.sword 64)) (nm : String) {p : LeakTrace}
    (h : ComCont.LeakFactorsTrace o.cont p) :
    ComCont.LeakFactorsTrace (pushVarBind o e nm).cont (p ++ [Expr.leakEvent e]) := by
  simp only [pushVarBind]
  exact ComCont.comp_leakFactorsTrace h (ComCont.varBind_leakFactorsTrace _)

/-- **The scalar-`SExpr` chain trace-factors.** Existential trace analogue of
    `lowerSExpr_cont_leakFactors`. -/
theorem lowerSExpr_cont_leakFactorsTrace {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat)
    (e : CatCrypt.Crypto.Jasmin.LowCT.SExpr) {o : DTransOut Γ} {nm : String} {cnt' : Nat}
    (h : lowerSExpr vm cnt e = some (o, nm, cnt')) :
    ∃ pre : LeakTrace, ComCont.LeakFactorsTrace o.cont pre := by
  induction e generalizing Γ vm cnt o nm cnt' with
  | SVar x =>
      simp only [lowerSExpr] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨ho, _⟩ := h; subst ho; exact ⟨[], ComCont.id_leakFactorsTrace⟩
      · exact absurd h (by simp)
  | SLit n =>
      simp only [lowerSExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨ho, _⟩ := h; subst ho
      exact ⟨_, pushVarBind_leakFactorsTrace _ _ ComCont.id_leakFactorsTrace⟩
  | SAdd a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨pa, hpa⟩ := iha vm cnt heqA
                   obtain ⟨pb, hpb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨_, pushVarBind_leakFactorsTrace _ _ (seqOut_leakFactorsTrace hpa hpb)⟩)
                | exact absurd h (by simp)
  | SSub a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨pa, hpa⟩ := iha vm cnt heqA
                   obtain ⟨pb, hpb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨_, pushVarBind_leakFactorsTrace _ _ (seqOut_leakFactorsTrace hpa hpb)⟩)
                | exact absurd h (by simp)
  | SMul a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨pa, hpa⟩ := iha vm cnt heqA
                   obtain ⟨pb, hpb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨_, pushVarBind_leakFactorsTrace _ _ (seqOut_leakFactorsTrace hpa hpb)⟩)
                | exact absurd h (by simp)
  | SAnd a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨pa, hpa⟩ := iha vm cnt heqA
                   obtain ⟨pb, hpb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨_, pushVarBind_leakFactorsTrace _ _ (seqOut_leakFactorsTrace hpa hpb)⟩)
                | exact absurd h (by simp)
  | SXor a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨pa, hpa⟩ := iha vm cnt heqA
                   obtain ⟨pb, hpb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨_, pushVarBind_leakFactorsTrace _ _ (seqOut_leakFactorsTrace hpa hpb)⟩)
                | exact absurd h (by simp)
  | SShl a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨pa, hpa⟩ := iha vm cnt heqA
                   obtain ⟨pb, hpb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨_, pushVarBind_leakFactorsTrace _ _ (seqOut_leakFactorsTrace hpa hpb)⟩)
                | exact absurd h (by simp)
  | SShr a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨pa, hpa⟩ := iha vm cnt heqA
                   obtain ⟨pb, hpb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨_, pushVarBind_leakFactorsTrace _ _ (seqOut_leakFactorsTrace hpa hpb)⟩)
                | exact absurd h (by simp)
  | SLt _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SAsr _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SMulS _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SMulHiU a b iha ihb =>
      simp only [lowerSExpr] at h
      split at h
      · exact absurd h (by simp)
      · next r heqA =>
          obtain ⟨oa, na, cnt1⟩ := r
          split at h
          · exact absurd h (by simp)
          · next s heqB =>
              obtain ⟨ob, nb, cnt2⟩ := s
              split at h <;> first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h
                   obtain ⟨ho, _⟩ := h; subst ho
                   obtain ⟨pa, hpa⟩ := iha vm cnt heqA
                   obtain ⟨pb, hpb⟩ := ihb oa.vm cnt1 heqB
                   exact ⟨_, pushVarBind_leakFactorsTrace _ _ (seqOut_leakFactorsTrace hpa hpb)⟩)
                | exact absurd h (by simp)
  | SMulHiS _ _ _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)
  | SLimb _ _ => simp only [lowerSExpr] at h; exact absurd h (by simp)

/-- **The comparison-select prefix has a fixed leak-event trace.** -/
theorem selectCmpCont_leakFactorsTrace {Γ : Ctx} (sV aV cV : CVar Γ (.sword 64)) :
    ∃ pre : LeakTrace, ComCont.LeakFactorsTrace (selectCmpCont sV aV cV) pre := by
  unfold selectCmpCont
  exact ⟨_, ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
    (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
      (ComCont.varBind_leakFactorsTrace _))⟩

/-- **The mask-chain prefix has a fixed leak-event trace.** -/
theorem selectMaskCont_leakFactorsTrace {Γ : Ctx} (sV aV cV : CVar Γ (.sword 64)) :
    ∃ pre : LeakTrace, ComCont.LeakFactorsTrace (selectMaskCont sV aV cV) pre := by
  unfold selectMaskCont
  exact ⟨_, ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
    (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
      (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
        (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
          (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
            (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
              (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
                (ComCont.varBind_leakFactorsTrace _)))))))⟩

/-- The leaf-call front's trace-factoring (covered fragment). -/
theorem translateDialectFull_cont_leakFactorsTrace {Γ : Ctx} (vm : VarMap Γ) {c : LowCT}
    (hc : IsCovered c) {o : DTransOut Γ}
    (h : translateDialectFull vm c = some o) :
    ∃ pre : LeakTrace, ComCont.LeakFactorsTrace o.cont pre := by
  induction hc generalizing Γ vm o with
  | rSkip =>
      simp only [translateDialectFull, translateDialect, Option.some.injEq] at h
      subst h; exact ⟨[], ComCont.id_leakFactorsTrace⟩
  | rScalarSet name n =>
      simp only [translateDialectFull, translateDialect, Option.some.injEq] at h
      subst h; exact ⟨_, ComCont.varBind_leakFactorsTrace _⟩
  | rSeq _ _ ih₁ ih₂ =>
      rw [translateDialectFull] at h
      split at h
      · next o₁ heq₁ =>
          split at h
          · next o₂ heq₂ =>
              rw [Option.some.injEq] at h; subst h
              obtain ⟨p₁, hp₁⟩ := ih₁ vm heq₁
              obtain ⟨p₂, hp₂⟩ := ih₂ o₁.vm heq₂
              exact ⟨_, ComCont.comp_leakFactorsTrace hp₁ hp₂⟩
          · simp at h
      · simp at h
  | rLetU64Zero _ ih =>
      rw [translateDialectFull] at h
      split at h
      · next o' heq =>
          rw [Option.some.injEq] at h; subst h
          obtain ⟨p, hp⟩ := ih (vm.bind _) heq
          exact ⟨_, ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _) hp⟩
      · simp at h
  | rBlock _ ih => rw [translateDialectFull] at h; exact ih vm h
  | rCallN fname dests args =>
      rw [translateDialectFull] at h; exact loopCallNDestsD_leakFactorsTrace fname args vm dests h
  | rLimbStore loc idx v =>
      rw [translateDialectFull] at h
      split at h <;> first
        | (split at h <;> first
            | (split at h <;> first
                | (rw [Option.some.injEq] at h; subst h;
                   exact ⟨_, ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
                     (ComCont.varBind_leakFactorsTrace _)⟩)
                | exact absurd h (by simp))
            | (rw [Option.some.injEq] at h; subst h;
               exact ⟨_, ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _) (ComCont.varBind_leakFactorsTrace _)⟩)
            | exact absurd h (by simp))
        | exact absurd h (by simp)
  | rCallSwap fname dest1 dest2 args =>
      rw [translateDialectFull] at h
      split at h <;> first
        | (split at h; dsimp only at h; split at h <;> first
            | (rw [Option.some.injEq] at h; subst h;
               exact ⟨_, ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _) (ComCont.varBind_leakFactorsTrace _)⟩)
            | exact absurd h (by simp))
        | exact absurd h (by simp)
  | rCloneCall cv cloneTy oldDest innerF newDest args =>
      rw [translateDialectFull] at h
      split at h <;> first
        | (dsimp only at h; split at h <;> first
            | (rw [Option.some.injEq] at h; subst h;
               exact ⟨_, ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _) (ComCont.varBind_leakFactorsTrace _)⟩)
            | exact absurd h (by simp))
        | exact absurd h (by simp)
  | rScalarSetExpr x e =>
      rw [translateDialectFull] at h
      split at h
      · exact absurd h (by simp)
      · next r heqL =>
          obtain ⟨oe, ne, c⟩ := r
          obtain ⟨p, hp⟩ := lowerSExpr_cont_leakFactorsTrace vm 0 e heqL
          split at h <;> first
            | (simp only [Option.some.injEq] at h; subst h
               exact ⟨_, pushVarBind_leakFactorsTrace _ _ hp⟩)
            | exact absurd h (by simp)
  | rSelect dst sel src0 src1 =>
      rw [translateDialectFull] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact selectCmpCont_leakFactorsTrace _ _ _
      · split at h <;>
          first
            | (split at h; dsimp only at h; rw [Option.some.injEq] at h; subst h;
               exact ⟨_, ComCont.varBind_leakFactorsTrace _⟩)
            | exact absurd h (by simp)
  | rArrLoadLit dst src idx =>
      rw [translateDialectFull] at h
      split at h
      · rw [Option.some.injEq] at h; subst h
        exact ⟨_, ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
          (ComCont.varBind_leakFactorsTrace _)⟩
      · split at h <;>
          first
            | (split at h; dsimp only at h; rw [Option.some.injEq] at h; subst h;
               exact ⟨_, ComCont.varBind_leakFactorsTrace _⟩)
            | exact absurd h (by simp)
  | rArrStoreLit arr idx src =>
      rw [translateDialectFull] at h
      split at h
      · rw [Option.some.injEq] at h; subst h
        exact ⟨_, ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
          (ComCont.varBind_leakFactorsTrace _)⟩
      · split at h <;>
          first
            | (split at h; dsimp only at h; rw [Option.some.injEq] at h; subst h;
               exact ⟨_, ComCont.varBind_leakFactorsTrace _⟩)
            | exact absurd h (by simp)
  | rArrLoad dst src idxVar =>
      rw [translateDialectFull] at h
      split at h <;> first
        | (split at h; dsimp only at h; rw [Option.some.injEq] at h; subst h;
           exact arrLoadCont_leakFactorsTrace _ _ _ _)
        | exact absurd h (by simp)
  | rArrStore arr idxVar src =>
      rw [translateDialectFull] at h
      split at h <;> first
        | (split at h; dsimp only at h; rw [Option.some.injEq] at h; subst h;
           exact arrStoreCont_leakFactorsTrace _ _ _ _)
        | exact absurd h (by simp)
  | rAssert label =>
      simp only [translateDialectFull, Option.some.injEq] at h
      subst h; exact ⟨[], ComCont.id_leakFactorsTrace⟩
  | _ =>
      rw [translateDialectFull] at h
      split at h <;> first
        | (split at h; dsimp only at h; rw [Option.some.injEq] at h; subst h;
           exact ⟨_, ComCont.varBind_leakFactorsTrace _⟩)
        | exact absurd h (by simp)

/-- **The full control front's trace-factoring.** On every `IsCoveredCtl` `LowCT`,
    the front prefix prepends a fixed event list to any tail. The actual-prefix
    (not just length) dialect analogue of `LowCTLeakTrace.leakTrace_translate_factors`,
    the leak-factoring `RHP_pipeline_labeled_leakage_NI` exposes. -/
theorem translateDialectControl_cont_leakFactorsTrace {Γ : Ctx} (vm : VarMap Γ) {c : LowCT}
    (hc : IsCoveredCtl c) {o : DTransOut Γ}
    (h : translateDialectControl vm c = some o) :
    ∃ pre : LeakTrace, ComCont.LeakFactorsTrace o.cont pre := by
  induction hc generalizing Γ vm o with
  | ofCovered hcov =>
      rw [translateDialectControl_eq_full_of_covered vm hcov] at h
      exact translateDialectFull_cont_leakFactorsTrace vm hcov h
  | rFor _ ih =>
      rw [translateDialectControl] at h
      refine loopRForD_leakFactorsTrace_cond _ ?_ vm _ _ h
      intro Γ'' vm'' o'' hh; exact ih vm'' hh
  | rIfNz hthen helse ihthen ihelse =>
      rw [translateDialectControl] at h
      split at h
      · next w condVar =>
          split at h
          · next o₁eq o₂eq =>
              obtain ⟨p₁, hp₁⟩ := ihthen vm o₁eq
              obtain ⟨p₂, hp₂⟩ := ihelse vm o₂eq
              split_ifs at h with hg1 hg2 hg2'
              · rw [Option.some.injEq] at h; subst h; exact ⟨_, hp₁⟩
              · rw [Option.some.injEq] at h; subst h; exact ⟨_, hp₂⟩
              · rw [Option.some.injEq] at h; subst h; exact ⟨_, hp₁⟩
              · split at h
                · split at h
                  · rw [Option.some.injEq] at h; subst h
                    exact ⟨_, ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
                      (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
                        (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
                          (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
                            (ComCont.comp_leakFactorsTrace (ComCont.varBind_leakFactorsTrace _)
                              (ComCont.varBind_leakFactorsTrace _)))))⟩
                  · split at h
                    · next o₂' heq₂' =>
                        rw [Option.some.injEq] at h; subst h
                        obtain ⟨p₂', hp₂'⟩ := ihelse _ heq₂'
                        exact ⟨_, ComCont.comp_leakFactorsTrace hp₁ hp₂'⟩
                    · simp at h
                · split at h
                  · next o₂' heq₂' =>
                      rw [Option.some.injEq] at h; subst h
                      obtain ⟨p₂', hp₂'⟩ := ihelse _ heq₂'
                      exact ⟨_, ComCont.comp_leakFactorsTrace hp₁ hp₂'⟩
                  · simp at h
          · simp at h
      · simp at h
  | @rWhileNz name body _hbody _ih =>
      rw [translateDialectControl] at h
      split at h
      · cases hb : translateDialectControl vm body with
        | none => rw [hb] at h; exact absurd h (by simp)
        | some o' =>
            rw [hb] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            exact ⟨_, ComCont.id_leakFactorsTrace⟩
      · simp at h

/-- **Front-level RHP-pipeline leakage factoring (dialect).** For every
    `IsCoveredCtl` `LowCT` whose front succeeds, there is a fixed leak prefix `pre`
    such that plugging *any* tail `body` yields `Com.leakTrace = pre ++
    body.leakTrace`. This is the dialect, front-connected analogue of the
    leak-factoring half of `LowCTRHPFull.RHP_pipeline_labeled_leakage_NI`
    (`∃ pre, ∀ body, (out.cont body).leakTrace = pre ++ body.leakTrace`).
    (The x86-CT half of that result is machine-level.) -/
theorem dialect_front_leakage_factoring {Γ : Ctx} (vm : VarMap Γ) {c : LowCT}
    (hc : IsCoveredCtl c) {o : DTransOut Γ}
    (h : translateDialectControl vm c = some o) :
    ∃ pre : LeakTrace, ∀ {t : CryptoTy} (body : Com catCryptDialect o.Γ' t)
      (c' : Com catCryptDialect Γ t), o.cont body = some c' →
      Com.leakTrace c' = pre ++ Com.leakTrace body :=
  translateDialectControl_cont_leakFactorsTrace vm hc h

/-- **The vector node `RVsimdSetExpr` leak-factors (data-oblivious pure op).**
    `RVsimdSetExpr x tag args` is definitionally a reserved-tag `RCall`, so on the
    covered control front its emitted prefix prepends a *fixed* leak trace `pre` to
    any tail: the 128-bit SIMD op is data-oblivious (a fixed lane pattern, a single
    constant-cost `varBind`), so its leak contribution is independent of the secret
    operand values — the pure-op case. Direct corollary of
    `dialect_front_leakage_factoring` on the `rCall` arm (the `RVsimdSetExpr`
    desugaring). -/
theorem RVsimdSetExpr_leakage_factoring {Γ : Ctx} (vm : VarMap Γ)
    (x tag : String) (args : List String) {o : DTransOut Γ}
    (h : translateDialectControl vm (LowCT.RVsimdSetExpr x tag args) = some o) :
    ∃ pre : LeakTrace, ∀ {t : CryptoTy} (body : Com catCryptDialect o.Γ' t)
      (c' : Com catCryptDialect Γ t), o.cont body = some c' →
      Com.leakTrace c' = pre ++ Com.leakTrace body :=
  dialect_front_leakage_factoring vm
    (.ofCovered (.rCall tag ⟨x, .TU64⟩ (args.map (fun s => ⟨s, .TU64⟩)))) h

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring
